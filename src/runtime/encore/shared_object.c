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
  bool collectable;
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

static void *mpscq_peek(mpscq_t *q)
{
  queue_node_t *tail = _atomic_load(&q->tail);

  queue_node_t *next = _atomic_load(&tail->next);
  if (next == NULL) {
    return NULL;
  }
  return next->data;
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
  mpscq_destroy((mpscq_t *)q);
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
  if ( _atomic_dwcas(&q->double_head.dw, &cmp.dw, xchg.dw)) {
    return data;
  } else {
    POOL_FREE(queue_node_t, node);
    assert(cmp.node_of_head);
    return cmp.node_of_head->data;
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
  return mpscq_pop((mpscq_t*) q);
}

static void *double_head_mpscq_peek(double_head_mpscq_t *q)
{
  return mpscq_peek((mpscq_t *) q);
}

static void duration_list_init(duration_list_t *list)
{
  list->head = list->tail = NULL;
}

static void duration_list_push(duration_list_t *list, duration_t *d)
{
  if (_atomic_load(&list->head)) {
    _atomic_store(&list->head->next, d);
    _atomic_store(&list->head, d);
  } else {
    assert(!_atomic_load(&list->tail));
    _atomic_store(&list->head, d);
    _atomic_store(&list->tail, d);
  }
}

static duration_t* duration_list_pop(duration_list_t *list)
{
  if (!_atomic_load(&list->tail)) {
    assert(_atomic_load(&list->head));
    return NULL;
  }
  duration_t *ret = list->tail;
  _atomic_store(&list->tail, _atomic_load(&list->tail->next));
  if (!list->tail) {
    _atomic_store(&list->head, NULL);
  }
  return ret;
}

static duration_t* duration_list_peek(duration_list_t *list)
{
  if (!list->tail) {
    assert(list->head);
    return NULL;
  }
  return list->tail;
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
  duration_t *d = duration_list_pop(&so_gc->duration_list);
  do {
    assert(d->collectable);
    for (size_t i = 0; i < d->closed_and_exit.exit; ++i) {
      clean_one(double_head_mpscq_pop(&so_gc->in_out_q));
    }
    POOL_FREE(duration_t, d);
    cmp.aba = _atomic_load(&so_gc->cas_d.aba);
    cmp.current = d;
    xchg.aba = cmp.aba + 1;
    xchg.current = NULL;
    bool ret = _atomic_dwcas(&so_gc->cas_d.dw, &cmp.dw, xchg.dw);
    assert(ret);
    // _atomic_store(&so_gc->cas_d.dw, xchg.dw);
    d = duration_list_peek(&so_gc->duration_list);
    if (d == NULL || !_atomic_load(&d->collectable)) {
      return;
    }
    cmp.aba = xchg.aba;
    cmp.current = NULL;
    xchg.aba = cmp.aba + 1;
    xchg.current = d;
    // racing with set_collectable
    if (!_atomic_dwcas(&so_gc->cas_d.dw, &cmp.dw, xchg.dw)) {
      return;
    }
  } while (true);
}

static void set_collectable(encore_so_t *this, duration_t *d)
{
  // multithread entry
  // called by any thread on exiting so
  if (!_atomic_load(&d->closed_and_exit.closed)) { return; }
  if (_atomic_load(&d->collectable)) { return; }

  if (_atomic_load(&d->closed_and_exit.exit) + d->legacy ==
      _atomic_load(&d->entry)) {
    dwcas_t cmp, xchg;
    bool old_collectable = false;
    to_trace_t *head = d->head;
    so_gc_t *so_gc = &this->so_gc;
    if (_atomic_cas(&d->collectable, &old_collectable, true)) {
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
  new->collectable = false;
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

static void set_new_current_duration(so_gc_t *so_gc, duration_t *current_d)
{
  // single thread
  // called by head of duration on exit
  queue_node_t *node = _atomic_load(&so_gc->in_out_q.double_head.node_of_head);
  uint32_t start_index = _atomic_load(&so_gc->start_index);

  assert(current_d);
  assert(current_d->closed_and_exit.closed);
  assert(!current_d->collectable);
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
          assert(_atomic_load(&so_gc->aba_entry.entry) == 0);
          _atomic_store(&so_gc->aba_entry.entry, 1);
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
      break;
    }
    // next duration
    d_iter = d_iter->next;
  } while (true);

  _atomic_store(&so_gc->in_out_q.double_head.node_of_head, node);
  _atomic_store(&so_gc->start_index, start_index);
  dwcas_t cmp, xchg;
  xchg.dw = cmp.dw = _atomic_load(&so_gc->cas.dw);
  xchg.current = d;
  xchg.aba++;
  bool ret = _atomic_dwcas(&so_gc->cas.dw, &cmp.dw, xchg.dw);
  assert(ret);
  // _atomic_store(&so_gc->cas.dw, xchg.dw);
  _atomic_store(&so_gc->closed, false);
}

void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item)
{
  dwcas_t cmp, xchg;
  so_gc_t *so_gc = &this->so_gc;
  assert(so_gc->in_out_q.double_head.head);
  aba_entry_t aba_entry, new_aba_entry;
  aba_entry.dw = _atomic_load(&so_gc->aba_entry.dw);
  to_trace_t *head_item = NULL;
  bool entered = false;
  do {
    cmp.current = _atomic_load(&so_gc->cas.current);
    cmp.aba = _atomic_load(&so_gc->cas.aba);
    if (_atomic_load(&so_gc->closed)) {
      relax();
      continue;
    }
    if (cmp.current == NULL) {
      head_item = double_mpscq_init_push(&so_gc->in_out_q, item);
      xchg.current = duration_new(head_item);
      xchg.aba = cmp.aba + 1;
      if (_atomic_cas(&so_gc->cas.dw, &cmp.dw, xchg.dw)) {
        cmp.current = xchg.current;
      } else {
        POOL_FREE(duration_t, xchg.current);
        if (!cmp.current) {
          // aba invalid
          continue;
        }
      }
    }
    assert(cmp.current);
    uint32_t old_aba_entry_aba = new_aba_entry.aba = aba_entry.aba;
    do {
      new_aba_entry.entry = aba_entry.entry + 1;
      if (_atomic_cas(&so_gc->aba_entry.dw, &aba_entry.dw, new_aba_entry.dw)) {
        entered = true;
        break;
      }
      if (old_aba_entry_aba != aba_entry.aba) {
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

static void exit_as_head(encore_so_t *this, duration_t *current_d,
    to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  _atomic_store(&so_gc->closed, true);
  _atomic_add(&so_gc->aba_entry.aba, 1);
  _atomic_store(&current_d->entry,
      _atomic_exchange(&so_gc->aba_entry.entry, 0));
  _atomic_store(&current_d->closed_and_exit.closed, true);
  duration_list_push(&so_gc->duration_list, current_d);
  set_new_current_duration(so_gc, current_d);
  if (item->duration == current_d) {
    _atomic_add(&current_d->closed_and_exit.exit, 1);
  } else {
    assert(_atomic_load(&item->duration->closed_and_exit.closed));
    _atomic_add(&item->duration->legacy, 1);
    set_collectable(this, item->duration);
  }
  set_collectable(this, current_d);
}

static void exit_as_not_head(encore_so_t *this, to_trace_t *item)
{
  closed_and_exit_t old_closed_and_exit;
  old_closed_and_exit.dw = _atomic_load(&item->duration->closed_and_exit.dw);
  do {
    if (old_closed_and_exit.closed) {
      _atomic_add(&item->duration->legacy, 1);
      set_collectable(this, item->duration);
      return;
    }
    assert(!old_closed_and_exit.closed);
    closed_and_exit_t new_closed_and_exit = old_closed_and_exit;
    new_closed_and_exit.exit = old_closed_and_exit.exit + 1;
    if (_atomic_cas(&item->duration->closed_and_exit.dw,
          &old_closed_and_exit.dw,
          new_closed_and_exit.dw)) {
        set_collectable(this, item->duration);
        return;
    }
  } while (true);
}

void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  duration_t *current_d = _atomic_load(&so_gc->cas.current);
  assert(current_d);
  _atomic_store(&item->exited, true);
  if (current_d->head == item) {
    exit_as_head(this, current_d, item);
  } else {
    int old_head_candidate = 0;
    if (_atomic_cas(&item->head_candidate, &old_head_candidate, 1)) {
      exit_as_not_head(this, item);
    } else {
      do {
        if (_atomic_load(&so_gc->cas.current)->head == item &&
            !_atomic_load(&so_gc->closed)) {
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
  this->so_gc.closed = false;
  this->so_gc.aba_entry.dw = 0;
  this->so_gc.cas.dw = 0;
  this->so_gc.cas_d.dw = 0;
  double_head_mpscq_init(&this->so_gc.in_out_q);
  duration_list_init(&this->so_gc.duration_list);
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
  assert(duration_list_pop(&this->so_gc.duration_list) == NULL);
  double_head_mpscq_destroy(&this->so_gc.in_out_q);
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
