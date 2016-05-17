#define _XOPEN_SOURCE 800

#include "shared_object.h"
#include "mem/pool.h"
#include "sched/scheduler.h"
#include "actor/actor.h"
#include <assert.h>
#include <stdio.h>
#include <stdint.h>

static inline void gc_sendobject_shallow(pony_ctx_t *ctx, void *p)
{
  gc_sendobject(ctx, p, NULL);
}

static inline void gc_sendobject_shallow_done(pony_ctx_t *ctx)
{
  pony_send_done(ctx);
}

static inline void gc_recvobject_shallow(pony_ctx_t *ctx, void *p)
{
  gc_recvobject(ctx, p, NULL);
}

static inline void gc_recvobject_shallow_done(pony_ctx_t *ctx)
{
  pony_recv_done(ctx);
}

typedef struct queue_node_t
{
  void* data;
  queue_node_t* next;
} queue_node_t;

typedef struct mpscq_t
{
  queue_node_t* head;
  queue_node_t* tail;
} mpscq_t;

// distinguish exit or legacy depending on if closed
typedef struct closed_and_exit_t {
  union {
    struct {
      bool closed;
      uint32_t exit;
    };
    uint64_t dw;
  };
} closed_and_exit_t;

typedef struct duration_t {
  to_trace_t *head;
  uint32_t entry;
  uint32_t legacy;
  closed_and_exit_t closed_and_exit;
  bool collectible;
  struct duration_t *next;
} duration_t;

#define _atomic_sub(PTR, VAL) \
  (__atomic_fetch_sub(PTR, VAL, __ATOMIC_RELEASE))

typedef struct trace_address_list {
  void *address;
  struct trace_address_list *next;
} trace_address_list;

typedef struct to_trace_t {
  duration_t *duration;
  trace_address_list *address;
  int head_candidate;
  bool exited;
} to_trace_t;

static void mpscq_init(mpscq_t* q)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = NULL;
  node->next = NULL;

  q->tail = q->head = node;
}

static void mpscq_destroy(mpscq_t* q)
{
  assert(_atomic_load(&q->head) == _atomic_load(&q->tail));
  POOL_FREE(queue_node_t, q->tail);
}

static queue_node_t* mpscq_push(mpscq_t *q, void *data)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = data;
  node->next = NULL;

  queue_node_t* prev = (queue_node_t*)_atomic_exchange(&q->head, node);
  _atomic_store(&prev->next, node);
  return node;
}

static void mpscq_push_single(mpscq_t *q, void *data)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = data;
  node->next = NULL;

  queue_node_t* prev = q->head;
  q->head = node;
  prev->next = node;
}

static void *mpscq_pop(mpscq_t *q)
{
  queue_node_t *tail = q->tail;
  queue_node_t *next = _atomic_load(&tail->next);

  if (next == NULL) {
    return NULL;
  }
  void *data = next->data;
  q->tail = next;
  POOL_FREE(queue_node_t, tail);
  return data;
}

static void double_head_mpscq_init(double_head_mpscq_t* q)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = NULL;
  node->next = NULL;

  q->tail = q->double_head.head = node;
  q->double_head.node_of_head = NULL;
}

static void double_head_mpscq_destroy(double_head_mpscq_t* q)
{
  assert(_atomic_load(&q->double_head.head) == _atomic_load(&q->tail));
  assert(_atomic_load(&q->double_head.node_of_head) == NULL);
  POOL_FREE(queue_node_t, q->tail);
}

static void* double_mpscq_init_push(double_head_mpscq_t *q, void *data)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = data;
  node->next = NULL;

  double_head_t cmp, xchg;
  cmp = q->double_head;
  cmp.node_of_head = NULL;
  xchg.head = xchg.node_of_head = node;
  while (true) {
    if (_atomic_dwcas(&q->double_head.dw, &cmp.dw, xchg.dw)) {
      _atomic_store(&cmp.head->next, node);
      return data;
    } else {
      if (cmp.node_of_head) {
        POOL_FREE(queue_node_t, node);
        return cmp.node_of_head->data;
      }
    }
  }
}

static void *double_head_mpscq_push(double_head_mpscq_t *q, void *data)
{
  queue_node_t* node = POOL_ALLOC(queue_node_t);
  node->data = data;
  node->next = NULL;

  queue_node_t* prev = _atomic_exchange(&q->double_head.head, node);
  _atomic_store(&prev->next, node);
  return node;
}

static void *double_head_mpscq_pop(double_head_mpscq_t *q)
{
  queue_node_t *tail = q->tail;
  queue_node_t *next = _atomic_load(&tail->next);

  if (next == NULL) {
    return NULL;
  }
  void *data = next->data;
  q->tail = next;
  POOL_FREE(queue_node_t, tail);
  return data;
}

static void *double_head_mpscq_peek(double_head_mpscq_t *q)
{
  queue_node_t *tail = _atomic_load(&q->tail);
  queue_node_t *next = _atomic_load(&tail->next);

  if (next == NULL) {
    return NULL;
  }
  return next->data;
}

static void duration_spscq_init(duration_spscq_t *q)
{
  duration_t *dummy = POOL_ALLOC(duration_t);
  dummy->next = NULL;
  q->head = q->tail = dummy;
}

static void duration_spscq_destroy(duration_spscq_t *q)
{
  assert(_atomic_load(&q->head) == _atomic_load(&q->tail));
  POOL_FREE(duration_t, q->tail);
}

static void duration_spscq_push(duration_spscq_t *q, duration_t *d)
{
  duration_t *prev = q->head;
  q->head = d;
  prev->next = d;
}

static duration_t* duration_spscq_pop(duration_spscq_t *q)
{
  duration_t *tail = q->tail;
  duration_t *next = _atomic_load(&tail->next);

  if (next == NULL) {
    return NULL;
  }

  POOL_FREE(duration_t, tail);
  q->tail = next;
  return next;
}

static duration_t* duration_spscq_peek(duration_spscq_t *q)
{
  return _atomic_load(&q->tail->next);
}

// caller needs to ensure no gc is happening while traversing through node list
static queue_node_t *next_node_of_not_exit_item(queue_node_t *node)
{
  to_trace_t *item;
  while ((node = _atomic_load(&node->next))) {
    item = node->data;
    assert(item);
    if (!_atomic_load(&item->exited)) {
      return node;
    }
  }
  return NULL;
}

static void clean_one(to_trace_t *item)
{
  assert(item);
  pony_ctx_t *ctx = pony_ctx();
  {
    trace_address_list *cur = item->address;
    trace_address_list *pre;
    while (true) {
      if (!cur) {
        break;
      }
      gc_recvobject_shallow(ctx, cur->address);
      pre = cur;
      cur = cur->next;
      POOL_FREE(trace_address_list, pre);
    }
    gc_recvobject_shallow_done(ctx);
  }
  POOL_FREE(to_trace_t, item);
}

static void collect(encore_so_t *this)
{
  // single thread entry
  dwcas_t cmp, xchg;
  so_gc_t *so_gc = &this->so_gc;
  duration_t *d = duration_spscq_pop(&so_gc->duration_q);
  do {
    assert(d->collectible);
    for (size_t i = 0; i < d->closed_and_exit.exit; ++i) {
      clean_one(double_head_mpscq_pop(&so_gc->in_out_q));
    }
    // TODO designate syntax
    cmp.aba = _atomic_load(&so_gc->cas_d.aba);
    cmp.current = d;
    xchg.aba = cmp.aba + 1;
    xchg.current = NULL;
    bool _ret = _atomic_dwcas(&so_gc->cas_d.dw, &cmp.dw, xchg.dw);
    assert(_ret);
    // _atomic_store(&so_gc->cas_d.dw, xchg.dw);
    d = duration_spscq_peek(&so_gc->duration_q);
    if (d == NULL || !_atomic_load(&d->collectible)) {
      return;
    }
    cmp.aba = xchg.aba;
    cmp.current = NULL;
    xchg.aba = cmp.aba + 1;
    xchg.current = d;
    // racing with set_collectible
    if (!_atomic_dwcas(&so_gc->cas_d.dw, &cmp.dw, xchg.dw)) {
      return;
    }
    d = duration_spscq_pop(&so_gc->duration_q);
  } while (true);
}

static void set_collectible(encore_so_t *this, duration_t *d)
{
  // multithread entry
  // called by any thread on exiting so
  if (!_atomic_load(&d->closed_and_exit.closed)) { return; }
  if (_atomic_load(&d->collectible)) { return; }

  if (_atomic_load(&d->closed_and_exit.exit) + d->legacy ==
      _atomic_load(&d->entry)) {
    dwcas_t cmp, xchg;
    bool old_collectible = false;
    to_trace_t *head = d->head;
    so_gc_t *so_gc = &this->so_gc;
    if (_atomic_cas(&d->collectible, &old_collectible, true)) {
      if (double_head_mpscq_peek(&this->so_gc.in_out_q) == head) {
        cmp.aba = _atomic_load(&so_gc->cas_d.aba);
        cmp.current = NULL;
        xchg.aba = cmp.aba + 1;
        xchg.current = d;
        if (_atomic_dwcas(&so_gc->cas_d.dw, &cmp.dw, xchg.dw)) {
          collect(this);
        }
      }
    }
  }
}

static duration_t *duration_new(to_trace_t *head)
{
  duration_t *new = POOL_ALLOC(duration_t);
  new->head = head;
  // entry is initialized on duration closing
  new->legacy = 0;
  new->closed_and_exit.closed = false;
  new->closed_and_exit.exit = 0;
  new->collectible = false;
  new->next = NULL;
  return new;
}

static inline void relax(void)
{
#if defined(PLATFORM_IS_X86) && !defined(PLATFORM_IS_VISUAL_STUDIO)
    asm volatile("pause" ::: "memory");
#endif
}

static queue_node_t *next_node(double_head_mpscq_t *q, queue_node_t *node)
{
  queue_node_t *next = NULL;
  do {
    next = _atomic_load(&node->next);
    if (next && next != _atomic_load(&q->tail)) {
      return next;
    }
    relax();
  } while (true);
}

// currend_d is closing; set new duration by selecting the first non-exited
// item in in_out_q from node_of_head. Need duration entry info so that we know
// how much to advance, and busy wait if the push-to-queue operation has not
// completed
static void set_new_current_duration(so_gc_t *so_gc, duration_t *current_d)
{
  // single thread
  // called by head of duration on exit
  queue_node_t *node = _atomic_load(&so_gc->in_out_q.double_head.node_of_head);
  uint32_t start_index = _atomic_load(&so_gc->start_index);

  assert(current_d);
  assert(current_d->closed_and_exit.closed);
  assert(!current_d->collectible);
  assert(node);
  assert(node->data == current_d->head);

  queue_node_t *next = NULL;
  to_trace_t *item = node->data;
  duration_t *d = NULL;
  duration_t *d_iter = item->duration;
  do {
    uint32_t i;
    assert(d_iter->entry >= 1);
    for (i = start_index+1; i < d_iter->entry; ++i) {
      node = next_node(&so_gc->in_out_q, node);
      item = node->data;
      assert(item);
      if (!_atomic_load(&item->exited)) {
        int old_head_candidate = 0;
        if (_atomic_cas(&item->head_candidate, &old_head_candidate, 1)) {
          d = duration_new(item);
          // head is in the new duration by default
          so_gc->aba_entry.entry = 1;
          break;
        }
      }
    }
    if (d) {
      start_index = i;
      break;
    }
    start_index = 0;
    if (d_iter == current_d) {
      node = NULL;
      break;
    }
    // next duration
    d_iter = _atomic_load(&d_iter->next);
  } while (true);

  assert(d ? true : node == NULL);
  _atomic_store(&so_gc->in_out_q.double_head.node_of_head, node);
  _atomic_store(&so_gc->start_index, start_index);
  assert(_atomic_load(&so_gc->cas.current) == current_d);
  dwcas_t xchg = { .aba = _atomic_load(&so_gc->cas.aba) + 1, .current = d };
  _atomic_store(&so_gc->cas.dw, xchg.dw);
  uint32_t current_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
  assert(current_aba % 2 == 1);
}

// caller would wait until the current duration becomes open, increment the
// entry counter, and push itself into in_out_q
void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item)
{
  dwcas_t cmp, xchg;
  so_gc_t *so_gc = &this->so_gc;
  assert(so_gc->in_out_q.double_head.head);
  aba_entry_t aba_entry, new_aba_entry;
  uint32_t current_aba;
  to_trace_t *head_item = NULL;
  bool entered = false;
  do {
    current_aba = _atomic_load(&so_gc->aba_entry.aba);
    // read duration after entry aba to avoid duration entry mismatch
    cmp.dw = _atomic_load(&so_gc->cas.dw);
    if (current_aba % 2 != 0) {
      relax();
      continue;
    }
    if (cmp.current == NULL) {
      head_item = double_mpscq_init_push(&so_gc->in_out_q, item);
      assert(head_item);
      xchg.aba = cmp.aba + 1;
      xchg.current = duration_new(head_item);
      // using dw to avoid using obsolete head_item
      if (_atomic_dwcas(&so_gc->cas.dw, &cmp.dw, xchg.dw)) {
        cmp.current = xchg.current;
      } else {
        POOL_FREE(duration_t, xchg.current);
        if (!cmp.current) {
          // read after set_new_current_duration
          continue;
        }
      }
    }
    assert(cmp.current);
    new_aba_entry.aba = aba_entry.aba = current_aba;
    aba_entry.entry = _atomic_load(&so_gc->aba_entry.entry);
    do {
      new_aba_entry.entry = aba_entry.entry + 1;
      if (_atomic_cas(&so_gc->aba_entry.dw, &aba_entry.dw, new_aba_entry.dw)) {
        entered = true;
        break;
      }
      if (aba_entry.aba != new_aba_entry.aba) {
        // duration changed
        break;
      }
    } while (true);
  } while (!entered);

  item->duration = cmp.current;
  if (head_item != item) {
    double_head_mpscq_push(&so_gc->in_out_q, item);
  }
}

// head would closes its duration, try to set a new duration and try to set the
// current duration collectible. If head doesn't belong to the current
// duration, it would additionally set its own duration collectible
static void exit_as_head(encore_so_t *this, duration_t *current_d,
    to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  uint32_t current_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
  assert(current_aba % 2 == 0);
  _atomic_store(&current_d->entry,
      _atomic_exchange(&so_gc->aba_entry.entry, 0));
  _atomic_store(&current_d->closed_and_exit.closed, true);
  duration_spscq_push(&so_gc->duration_q, current_d);
  set_new_current_duration(so_gc, current_d);
  if (item->duration == current_d) {
    _atomic_add(&current_d->closed_and_exit.exit, 1);
  } else {
    assert(_atomic_load(&item->duration->closed_and_exit.closed));
    _atomic_add(&item->duration->legacy, 1);
    set_collectible(this, item->duration);
  }
  set_collectible(this, current_d);
}

// increment exit or legacy counter depending on if the duration is closed
// exited items would be collected if the duration becomes collectible, while
// legacy counter merely determines when the duration becomes collectible
static void exit_as_not_head(encore_so_t *this, to_trace_t *item)
{
  closed_and_exit_t old_closed_and_exit;
  old_closed_and_exit.dw = _atomic_load(&item->duration->closed_and_exit.dw);
  do {
    if (old_closed_and_exit.closed) {
      _atomic_add(&item->duration->legacy, 1);
      set_collectible(this, item->duration);
      return;
    }
    assert(!old_closed_and_exit.closed);
    closed_and_exit_t new_closed_and_exit = old_closed_and_exit;
    new_closed_and_exit.exit = old_closed_and_exit.exit + 1;
    if (_atomic_cas(&item->duration->closed_and_exit.dw,
          &old_closed_and_exit.dw,
          new_closed_and_exit.dw)) {
        set_collectible(this, item->duration);
        return;
    }
  } while (true);
}

// delegate to exit_as_head and exit_as_not_head, need to wait for the new
// duration if selected as the head candidate
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  duration_t *current_d = _atomic_load(&so_gc->cas.current);
  assert(current_d);
  _atomic_store(&item->exited, true);
  if (current_d->head == item) {
    if (_atomic_load(&item->head_candidate) == 1) {
      // wait until set_new_current_duration ends
      while (_atomic_load(&so_gc->aba_entry.aba) % 2 != 0) {
        relax();
      }
    }
    exit_as_head(this, current_d, item);
  } else {
    int old_head_candidate = 0;
    if (_atomic_cas(&item->head_candidate, &old_head_candidate, 2)) {
      exit_as_not_head(this, item);
    } else {
      do {
        if (_atomic_load(&so_gc->cas.current)->head == item &&
            _atomic_load(&so_gc->aba_entry.aba) % 2 == 0) {
          break;
        }
        relax();
      } while (true);
      current_d = _atomic_load(&so_gc->cas.current);
      assert(current_d);
      assert(current_d->head == item);
      exit_as_head(this, current_d, item);
    }
  }
}

encore_so_t *encore_create_so(pony_ctx_t *ctx, pony_type_t *type)
{
  encore_so_t *this = (encore_so_t*) encore_create(ctx, type);
  this->so_gc.start_index = 0;
  this->so_gc.aba_entry.dw = 0;
  this->so_gc.cas.dw = 0;
  this->so_gc.cas_d.dw = 0;
  double_head_mpscq_init(&this->so_gc.in_out_q);
  duration_spscq_init(&this->so_gc.duration_q);
  return this;
}

to_trace_t *so_to_trace_new(encore_so_t *this)
{
  to_trace_t *ret = POOL_ALLOC(to_trace_t);
  ret->head_candidate = 0;
  ret->address = NULL;
  ret->exited = false;
  return ret;
}

void so_to_trace(to_trace_t *item, void *p)
{
  trace_address_list *new = POOL_ALLOC(trace_address_list);
  new->address = p;
  new->next = item->address;
  item->address = new;
}

void encore_so_finalinzer(void *p)
{
  return;
  assert(p);
  encore_so_t *this = p;
  assert(double_head_mpscq_pop(&this->so_gc.in_out_q) == NULL);
  assert(duration_spscq_pop(&this->so_gc.duration_q) == NULL);
  double_head_mpscq_destroy(&this->so_gc.in_out_q);
  duration_spscq_destroy(&this->so_gc.duration_q);
}

void so_lockfree_send(pony_ctx_t *ctx)
{
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
    gc_sendobject_shallow(ctx, p);
  }
  gc_sendobject_shallow_done(ctx);
}

void so_lockfree_unsend(pony_ctx_t *ctx)
{
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
  }
}

void so_lockfree_recv(pony_ctx_t *ctx)
{
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
    gc_recvobject_shallow(ctx, p);
  }
  gc_recvobject_shallow_done(ctx);
}

bool so_lockfree_is_reachable(pony_ctx_t *ctx, void *target)
{
  bool ret = false;
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
    ret = ret || p == target;
  }
  return ret;
}

void so_lockfree_delay_recv_using_send(pony_ctx_t *ctx, void *p)
{
  gc_sendobject(ctx, p, NULL);
  pony_send_done(ctx);
  ctx->lf_acc_stack = gcstack_push(ctx->lf_acc_stack, p);
}

void so_lockfree_register_acc_to_recv(pony_ctx_t *ctx, to_trace_t *item)
{
  void *p;
  while(ctx->lf_acc_stack != NULL) {
    ctx->lf_acc_stack = gcstack_pop(ctx->lf_acc_stack, &p);
    so_to_trace(item, p);
  }
}

void so_lockfree_set_trace_boundary(pony_ctx_t *ctx, void *p)
{
  ctx->boundary = p;
}
