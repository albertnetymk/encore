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

typedef struct duration_t {
  to_trace_t *head;
  uint32_t entry;
  uint32_t exit;
  bool collectible;
  bool closed;
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
  duration_t *next = tail->next;

  if (next == NULL) {
    return NULL;
  }

  POOL_FREE(duration_t, tail);
  q->tail = next;
  return next;
}

static duration_t* duration_spscq_peek(duration_spscq_t *q)
{
  duration_t *tail = q->tail;
  assert(tail);
  return tail->next;
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
  // multithread
  so_gc_t *so_gc = &this->so_gc;
  uint32_t pending = 0;
  if (!_atomic_cas(&so_gc->pending_lock.pending, &pending, 1)) {
    return;
  }
  uint32_t lock = 0;
  if (!_atomic_cas(&so_gc->pending_lock.lock, &lock, 1)) {
    return;
  }
  duration_t *d;
  pending_lock_t pending_lock = (pending_lock_t) {.lock = 1};
  pending_lock_t new_pending_lock = (pending_lock_t) {};
  do {
    _atomic_store(&so_gc->pending_lock.pending, 0);
    d = duration_spscq_peek(&so_gc->duration_q);
    if (d && _atomic_load(&d->collectible)) {
      clean_one(d->head);
      duration_t *_d = duration_spscq_pop(&so_gc->duration_q);
      assert(d == _d);
    }
    pending_lock.pending = 0;
    if (_atomic_cas(&so_gc->pending_lock.dw, &pending_lock.dw,
          new_pending_lock.dw)) {
        break;
    }
  } while (true);
}

static void set_collectible(encore_so_t *this, duration_t *d)
{
  // multithread entry
  // called by any thread on exiting so
  if (!_atomic_load(&d->closed)) { return; }
  if (_atomic_load(&d->collectible)) { return; }

  if (_atomic_load(&d->exit) == _atomic_load(&d->entry)) {
    _atomic_store(&d->collectible, true);
        collect(this);
  }
}

static duration_t *new_headless_duration()
{
  duration_t *new = POOL_ALLOC(duration_t);
  new->head = NULL;
  // entry is initialized on duration closing
  new->exit = 0;
  new->collectible = false;
  new->closed = true;
  new->next = NULL;
  return new;
}

static inline void relax(void)
{
#if defined(PLATFORM_IS_X86) && !defined(PLATFORM_IS_VISUAL_STUDIO)
    asm volatile("pause" ::: "memory");
#endif
}

// caller would wait until the current duration becomes open, increment the
// entry counter, and push itself into in_out_q
void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  aba_entry_t aba_entry, new_aba_entry;
  bool entered = false;
  duration_t *current_d;
  do {
    aba_entry.aba = _atomic_load(&so_gc->aba_entry.aba);
    current_d = _atomic_load(&so_gc->current_d);
    if (aba_entry.aba % 2 != 0 || current_d == NULL) {
      relax();
      continue;
    }
    assert(current_d);
    new_aba_entry.aba = aba_entry.aba;
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

  item->duration = current_d;
}

// delegate to exit_as_head and exit_as_not_head, need to wait for the new
// duration if selected as the head candidate
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  duration_t *current_d, *old_current_d;
  old_current_d = current_d = item->duration;
  assert(current_d);
  if (_atomic_cas(&so_gc->current_d, &old_current_d, NULL)) {
    uint32_t current_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
    assert(current_aba % 2 == 0);
    current_d->entry = _atomic_exchange(&so_gc->aba_entry.entry, 0);
    current_d->head = item;
    _atomic_store(&current_d->closed, true);
    _atomic_store(&so_gc->current_d, new_headless_duration());
    current_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
    assert(current_aba % 2 == 1);
    (void) current_aba;
    duration_spscq_push(&so_gc->duration_q, current_d);
  }

  _atomic_add(&current_d->exit, 1);
  set_collectible(this, current_d);
}

encore_so_t *encore_create_so(pony_ctx_t *ctx, pony_type_t *type)
{
  encore_so_t *this = (encore_so_t*) encore_create(ctx, type);
  this->so_gc.aba_entry.dw = 0;
  this->so_gc.current_d = new_headless_duration();
  this->so_gc.pending_lock.dw = 0;
  duration_spscq_init(&this->so_gc.duration_q);
  return this;
}

to_trace_t *so_to_trace_new(encore_so_t *this)
{
  to_trace_t *item = POOL_ALLOC(to_trace_t);
  item->head_candidate = 0;
  item->address = NULL;
  item->exited = false;
  return item;
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
  assert(duration_spscq_pop(&this->so_gc.duration_q) == NULL);
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
