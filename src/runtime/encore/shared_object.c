#define _XOPEN_SOURCE 800

#include "shared_object.h"
#include "mem/pool.h"
#include "sched/scheduler.h"
#include "actor/actor.h"
#include <assert.h>
#include <stdio.h>
#include <stdint.h>

#define _atomic_sub(PTR, VAL) \
  (__atomic_fetch_sub(PTR, VAL, __ATOMIC_RELEASE))

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
  encore_passive_lf_so_t *f;
  pony_ctx_t *ctx = pony_ctx();
  {
    trace_address_list *cur = item->address;
    trace_address_list *pre;
    while (true) {
      if (!cur) {
        break;
      }
      f = cur->address;
      assert(f->published);
      if (_atomic_load(&f->rc) == 0) {
        gc_recvobject_shallow(ctx, cur->address);
      }
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
  if (_atomic_add(&so_gc->pending_lock.pending, 1) != 0) {
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
    _atomic_sub(&so_gc->pending_lock.pending, 1);
    while ((d = duration_spscq_peek(&so_gc->duration_q))) {
      if (!_atomic_load(&d->collectible)) {
        break;
      }
      clean_one(d->head);
      duration_t *_d = duration_spscq_pop(&so_gc->duration_q);
      assert(d == _d);
    }
    if (so_gc->pending_lock.pending > 0) {
      continue;
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
    duration_spscq_push(&so_gc->duration_q, current_d);
    current_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
    assert(current_aba % 2 == 1);
    (void) current_aba;
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

void so_lockfree_register_final_cb(void *p, so_lockfree_final_cb_fn final_cb)
{
  encore_so_t *this = p;
  this->so_gc.final_cb = final_cb;
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
  assert(p);
  encore_so_t *this = p;
  assert(this->so_gc.final_cb);
  this->so_gc.final_cb(pony_ctx(), this);
  assert(duration_spscq_peek(&this->so_gc.duration_q) == NULL);
  duration_spscq_destroy(&this->so_gc.duration_q);
}

static void so_lockfree_publish(void *p)
{
  assert(p);
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  if (!f->published) {
    f->published = true;
  }
}

void so_lockfree_spec_subord_field_apply(pony_ctx_t *ctx, void *p)
{
  if (!p) { return; }
  so_lockfree_publish(p);
  gc_sendobject_shallow(ctx, p);
}

void so_lockfree_non_spec_subord_field_apply(pony_ctx_t *ctx, void *p)
{
  if (!p) { return; }
  so_lockfree_publish(p);
  gc_sendobject_shallow(ctx, p);
  so_lockfree_inc_rc(p);
}

void so_lockfree_subord_fields_apply_done(pony_ctx_t *ctx)
{
  gc_sendobject_shallow_done(ctx);
}

void so_lockfree_subord_field_final_apply(pony_ctx_t *ctx, void *p)
{
  if (!p) { return; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  assert(f->published);
  assert(_atomic_load(&f->rc) != 0);
  if (_atomic_sub(&f->rc, 1) == 1) {
    gc_recvobject_shallow(ctx, f);
  }
}

bool so_lockfree_is_published(void *p)
{
  assert(p);
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  return f->published;
}

void so_lockfree_chain_final(pony_ctx_t *ctx, void *p)
{
  if (!p) { return; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  assert(_atomic_load(&f->rc) != 0);
  if (_atomic_sub(&f->rc, 1) == 1) {
    gc_recvobject_shallow(ctx, f);
  }
}

void so_lockfree_send(pony_ctx_t *ctx)
{
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
    so_lockfree_publish(p);
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

void so_lockfree_delay_recv_using_send(pony_ctx_t *ctx, void *p)
{
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

size_t so_lockfree_get_rc(void *p)
{
  if (!p) { return 0; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  return _atomic_load(&f->rc);
}

size_t so_lockfree_inc_rc(void *p)
{
  if (!p) { return 0; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  return _atomic_add(&f->rc, 1);
}

size_t so_lockfree_dec_rc(void *p)
{
  if (!p) { return 0; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  assert(_atomic_load(&f->rc) != 0);
  return _atomic_sub(&f->rc, 1);
}

bool _so_lockfree_cas_try_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *_Z,
    pony_trace_fn F)
{
  assert(X);
  bool ret;
  void *Z = UNFREEZE(_Z);

  pony_gc_collect_to_send(ctx);
  so_lockfree_set_trace_boundary(ctx, NULL);
  pony_traceobject(ctx, Z, F);
  pony_gc_collect_to_send_done(ctx);

  so_lockfree_inc_rc(Z);

  ret = _atomic_cas((void**)X, &Y, _Z);
  if (ret) {
    assert(Y == NULL);
    so_lockfree_send(ctx);
  } else {
    so_lockfree_dec_rc(Z);
    assert(so_lockfree_is_published(Z) == false);
    so_lockfree_unsend(ctx);
  }

  return ret;
}

void* _so_lockfree_cas_extract_wrapper(void *_address, pony_trace_fn F)
{
  void **address = (void **)_address;
  void *tmp = *(void **)address;
  *address = NULL;
  pony_ctx_t *ctx = pony_ctx();
  pony_gc_recv(ctx);
  pony_traceobject(ctx, tmp, F);
  pony_recv_done(ctx);
  return tmp;
}

bool _so_lockfree_cas_link_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *Z,
    pony_trace_fn F)
{
  assert(X);
  bool ret;

  pony_gc_collect_to_send(ctx);
  so_lockfree_set_trace_boundary(ctx, Y);
  pony_traceobject(ctx, Z, F);
  pony_gc_collect_to_send_done(ctx);

  so_lockfree_inc_rc(Z);

  ret = _atomic_cas((void**)X, &Y, Z);
  if (ret) {
    if (so_lockfree_dec_rc(Y) == 1) {
      so_lockfree_delay_recv_using_send(ctx, Y);
    }
    so_lockfree_send(ctx);
  } else {
    so_lockfree_dec_rc(Z);
    assert(so_lockfree_is_published(Z) == false);
    so_lockfree_unsend(ctx);
  }

  return ret;
}

bool _so_lockfree_cas_unlink_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *Z,
    pony_trace_fn F)
{
  assert(X);
  so_lockfree_inc_rc(Z);
  bool ret = _atomic_cas((void**)X, &Y, Z);
  if (ret) {
    pony_gc_collect_to_recv(ctx);
    so_lockfree_set_trace_boundary(ctx, Z);
    pony_traceobject(ctx, Y, F);
    pony_gc_collect_to_recv_done(ctx);

    so_lockfree_recv(ctx);

    gc_sendobject_shallow(ctx, Y);
    gc_sendobject_shallow_done(ctx);

    if (so_lockfree_dec_rc(Y) == 1) {
      so_lockfree_delay_recv_using_send(ctx, Y);
    }
  } else {
    if (so_lockfree_dec_rc(Z) == 1) {
      so_lockfree_delay_recv_using_send(ctx, Z);
    }
  }
  return ret;
}

// TODO I can probably unite the two
void so_lockfree_assign_spec_wrapper(pony_ctx_t *ctx, void *lhs, void *rhs,
    pony_trace_fn F)
{
  so_lockfree_inc_rc(rhs);
  so_lockfree_dec_rc(lhs);
}

void _so_lockfree_assign_subord_wrapper(void *lhs, void *rhs)
{
  so_lockfree_inc_rc(rhs);
  so_lockfree_dec_rc(lhs);
}
