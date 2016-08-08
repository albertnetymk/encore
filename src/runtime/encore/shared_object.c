#define _XOPEN_SOURCE 800

#include "shared_object.h"
#include "mem/pool.h"
#include "sched/scheduler.h"
#include "actor/actor.h"
#include "ds/hash.h"
#include <assert.h>
#include <stdio.h>
#include <stdint.h>

// #define use_stw_mark_sweep

#define void_assert(e) { (void)(e) ; assert(e); }

#define _atomic_sub(PTR, VAL) \
  (__atomic_fetch_sub(PTR, VAL, __ATOMIC_RELEASE))

#define _atomic_load_relaxed(PTR) \
  __atomic_load_n(PTR, __ATOMIC_RELAXED)

#define _atomic_store_relaxed(PTR, VAL) \
  __atomic_store_n(PTR, VAL, __ATOMIC_RELAXED)

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

static inline void relax(void)
{
#if defined(PLATFORM_IS_X86) && !defined(PLATFORM_IS_VISUAL_STUDIO)
    asm volatile("pause" ::: "memory");
#endif
}

typedef void* trace_address_t;

static size_t address_wrapper_hash(trace_address_t* w)
{
  return hash_ptr(w);
}

static bool address_wrapper_cmp(trace_address_t* a, trace_address_t* b)
{
  return a == b;
}

DECLARE_HASHMAP(address_wrapper_set, trace_address_t);

DEFINE_HASHMAP(address_wrapper_set, trace_address_t, address_wrapper_hash,
    address_wrapper_cmp, pool_alloc_size, pool_free_size,
    NULL);

typedef struct duration_t {
  to_trace_t *head;
  uint32_t entry;
  uint32_t exit;
  bool collectible;
  // may be removed for optimization
  bool closed;
  bool stw;
  struct duration_t *next;
} duration_t;

typedef struct trace_address_list {
  void *address;
  struct trace_address_list *next;
} trace_address_list;

typedef struct to_trace_t {
  duration_t *duration;
  trace_address_list *address;
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

__attribute__((unused))
static void duration_spscq_push_atomic(duration_spscq_t *q, duration_t *d)
{
  duration_t *prev = _atomic_exchange(&q->head, d);
  _atomic_store(&prev->next, d);
}

__attribute__((unused))
static void duration_spscq_push(duration_spscq_t *q, duration_t *d)
{
  duration_t *prev = q->head;
  q->head = d;
  _atomic_store(&prev->next, d);
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

__attribute__((unused))
static duration_t* duration_spscq_peek(duration_spscq_t *q)
{
  duration_t *tail = q->tail;
  assert(tail);
  return tail->next;
}

static void so_subord_mpscq_init(so_subord_mpscq_t *q)
{
  so_lockfree_subord_wrapper_t *d = POOL_ALLOC(so_lockfree_subord_wrapper_t);
  d->p = NULL;
  q->head = q->tail = d;
}

static void so_subord_mpscq_destroy(so_subord_mpscq_t *q)
{
  POOL_FREE(so_lockfree_subord_wrapper_t, q->tail);
}

static so_lockfree_subord_wrapper_t *
so_lockfree_subord_wrapper_new(encore_passive_lf_so_t *p, uint32_t gc_mark)
{
  so_lockfree_subord_wrapper_t *w = POOL_ALLOC(so_lockfree_subord_wrapper_t);
  if (p) {
    w->gc_mark = gc_mark - 1;
    w->p = p;
    w->next = NULL;
    p->wrapper = w;
  } else {
    w->p = NULL;
    w->next = NULL;
  }
  return w;
}

__attribute__ ((unused))
static bool so_subord_mpscq_exist(so_subord_mpscq_t *q,
    so_lockfree_subord_wrapper_t *w)
{
  assert(w);
  if (q->tail == q->head) {
    return false;
  }

  so_lockfree_subord_wrapper_t *cur = q->tail->next;
  while (cur) {
    if (cur == w) {
      return true;
    }
    cur = cur->next;
  }

  return false;
}

static void so_subord_mpscq_push(so_subord_mpscq_t *q,
    encore_passive_lf_so_t *d, uint32_t gc_mark)
{
  so_lockfree_subord_wrapper_t *w = so_lockfree_subord_wrapper_new(d, gc_mark);
  so_lockfree_subord_wrapper_t *prev =
    (so_lockfree_subord_wrapper_t*)_atomic_exchange(&q->head, w);
  w->prev = prev;
  _atomic_store(&prev->next, w);
}

static void so_subord_mpscq_push_delimiter(so_subord_mpscq_t *q)
{
  so_subord_mpscq_push(q, NULL, 1);
}

static void so_subord_remove_tail(so_subord_mpscq_t *q)
{
  so_lockfree_subord_wrapper_t *tail = q->tail;
  so_lockfree_subord_wrapper_t *next = tail->next;
  assert(tail->p == NULL);
  assert(next);
  POOL_FREE(so_lockfree_subord_wrapper_t, tail);
  q->tail = next;
}

static so_lockfree_subord_wrapper_t* so_subord_mpscq_peak(so_subord_mpscq_t *q)
{
  assert(q->tail);
  if (q->tail == q->head) {
    return NULL;
  }
  assert(q->tail->next);
  return q->tail->next;
}

static void sweep_all_delimiters(so_subord_mpscq_t *q)
{
  if (q->tail == q->head) {
    return;
  }
  so_lockfree_subord_wrapper_t *cur = q->tail->next;
  so_lockfree_subord_wrapper_t *tmp;
  while (cur != q->head) {
    if (!cur->p) {
      tmp = cur;
      cur = cur->next;
      POOL_FREE(so_lockfree_subord_wrapper_t, tmp);
    } else {
      cur = cur->next;
    }
  }
}

static void free_prefix_delimiters(so_subord_mpscq_t *q)
{
  so_lockfree_subord_wrapper_t *first = so_subord_mpscq_peak(q);
  assert(first);
  do {
    if (first->p) {
      return;
    }
    so_subord_remove_tail(q);
    first = so_subord_mpscq_peak(q);
  } while (first);
}

static void so_subord_mpscq_remove(so_subord_mpscq_t *q,
    so_lockfree_subord_wrapper_t *w)
{
  assert(so_subord_mpscq_exist(q, w) == true);
  if (!_atomic_load(&w->next)) {
    so_subord_mpscq_push_delimiter(q);
  }
  while(!_atomic_load(&w->next)) { relax(); }
  assert(w->prev);
  assert(w->next);
  w->prev->next = w->next;
  w->next->prev = w->prev;
}

static void so_lockfree_heap_push(encore_so_t *this, encore_passive_lf_so_t *f)
{
  assert(f == UNFREEZE(f));
  assert(f->wrapper == NULL);
  so_subord_mpscq_push(&this->so_gc.so_subord_mpscq, f, this->gc_mark);
  assert(f->wrapper);
}

static void so_lockfree_heap_remove(so_gc_t *so_gc, encore_passive_lf_so_t *f)
{
  assert(f->wrapper);
  so_subord_mpscq_remove(&so_gc->so_subord_mpscq, f->wrapper);
}

extern void pony_so_lockfree_mark(pony_ctx_t* ctx);

void so_lockfree_markobject(pony_ctx_t *ctx, encore_passive_lf_so_t *p,
    pony_trace_fn f)
{
  if (!p) { return; }
  p = UNFREEZE(p);
  assert(p->wrapper);
  if (p->wrapper->gc_mark == ctx->so_lockfree_gc_mark) {
    return;
  }
  p->wrapper->gc_mark = ctx->so_lockfree_gc_mark;
  if (f) {
    ctx->stack = gcstack_push(ctx->stack, p);
    ctx->stack = gcstack_push(ctx->stack, f);
  }
}

__attribute__((unused))
static void mark_sweep(encore_so_t *this)
{
  this->gc_mark++;
  pony_ctx_t *ctx = pony_ctx();
  ctx->so_lockfree_gc_mark = this->gc_mark;
  pony_so_lockfree_mark(ctx);
  this->subord_trace(ctx, this);
  gc_handlestack(ctx);

  so_subord_mpscq_t *q = &this->so_gc.so_subord_mpscq;
  so_lockfree_subord_wrapper_t *prev;
  assert(q->tail);
  so_lockfree_subord_wrapper_t *cur = q->tail->next;
  while (cur) {
    if (cur->p == NULL || cur->gc_mark == this->gc_mark) {
      cur = cur->next;
      continue;
    }
    prev = cur->prev;
    // TODO maybe its safe to delete the wrapper, even though there's a pending
    // cas `bool _r = _atomic_cas(&f->wrapper->p, &f, NULL);`
    so_subord_mpscq_remove(q, cur);
    // TODO need to check if there's pending recv...
    // gc_recvobject_shallow(ctx, cur->p);
    cur = prev->next;
    // TODO I think the elem in tmp has been consumed; need to rethink this on
    // supporting swap
  }
}

static inline bool is_marked(void *p)
{
  return ((uintptr_t)p & 1) == 1;
}

static void clean_one(encore_so_t *this, to_trace_t *item)
{
  assert(item);
  encore_passive_lf_so_t *f;
  pony_ctx_t *ctx = pony_ctx();
  {
    trace_address_list *cur = item->address;
    trace_address_list *pre;
    while (cur) {
      f = cur->address;
      if (!is_marked(f)) {
        assert(f->wrapper);
        if (_atomic_load(&f->rc) == 0) {
          so_subord_mpscq_t *q = &this->so_gc.so_subord_mpscq;
          assert(so_subord_mpscq_exist(q, f->wrapper) == true);
          free_prefix_delimiters(q);
          so_lockfree_heap_remove(&this->so_gc, f);
          gc_recvobject_shallow(ctx, f);
        }
      }
      pre = cur;
      cur = cur->next;
      POOL_FREE(trace_address_list, pre);
    }
    gc_recvobject_shallow_done(ctx);
  }
  POOL_FREE(to_trace_t, item);
}

#ifdef use_stw_mark_sweep
static void collect(encore_so_t *this)
{
  // single thread
  so_gc_t *so_gc = &this->so_gc;
  duration_t *d;
  while ((d = duration_spscq_pop(&so_gc->duration_q))) {
    assert(d->collectible);
    clean_one(this, d->head);
  }
  mark_sweep(this);
  uint32_t current_aba = _atomic_add(&this->so_gc.aba_entry.aba, 1);
  void_assert(current_aba % 2 == 1);
}
#else
static void collect(encore_so_t *this)
{
  // multithread
  so_gc_t *so_gc = &this->so_gc;
  if (_atomic_add(&so_gc->pending_lock.pending, 1) != 0) { return; }
  uint32_t lock = 0;
  if (!_atomic_cas(&so_gc->pending_lock.lock, &lock, 1)) { return; }
  duration_t *d;
  pending_lock_t pending_lock = (pending_lock_t) {.lock = 1};
  pending_lock_t new_pending_lock = (pending_lock_t) {};
  if (_atomic_load(&so_gc->pending_lock.pending) == 0
      && _atomic_cas(&so_gc->pending_lock.dw, &pending_lock.dw,
        new_pending_lock.dw)) {
    return;
  }
  do {
    assert(_atomic_load(&so_gc->pending_lock.pending) > 0);
    _atomic_sub(&so_gc->pending_lock.pending, 1);
    while ((d = duration_spscq_peek(&so_gc->duration_q))) {
      if (!_atomic_load(&d->collectible)) { break; }
      clean_one(this, d->head);
      duration_t *_d = duration_spscq_pop(&so_gc->duration_q);
      void_assert(d == _d);
      if (d->stw) {
        void_assert(mark_sweep);
        mark_sweep(this);
        uint32_t current_aba = _atomic_add(&this->so_gc.aba_entry.aba, 1);
        void_assert(current_aba % 2 == 1);
      }
    }
    if (so_gc->pending_lock.pending > 0) { continue; }
    pending_lock.pending = 0;
    if (_atomic_cas(&so_gc->pending_lock.dw, &pending_lock.dw,
          new_pending_lock.dw)) {
        break;
    }
  } while (true);
}
#endif

static void set_collectible(encore_so_t *this, duration_t *d)
{
  // multithread entry
  // called by any thread on exiting so
  assert(d->closed);
  assert (!_atomic_load(&d->collectible));
  uint32_t entry = d->entry;
  uint32_t old_exit = _atomic_load(&d->exit);
  while (true) {
    uint32_t new_exit = old_exit + 1;
    assert(new_exit <= entry);
    if (_atomic_cas(&d->exit, &old_exit, new_exit)) {
      if (entry == new_exit) {
        _atomic_store(&d->collectible, true);
#ifdef use_stw_mark_sweep
        if (d->stw) {
          collect(this);
        }
#else
        collect(this);
#endif
      }
      break;
    }
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
  new->stw = false;
  new->next = NULL;
  return new;
}

void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  aba_entry_t aba_entry, new_aba_entry;
  bool entered = false;
  duration_t *current_d;
  do {
    aba_entry.aba = _atomic_load(&so_gc->aba_entry.aba);
    current_d = so_gc->current_d;
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

static void subsume_former_alias_address(duration_t *start, duration_t *end)
{
#ifdef use_stw_mark_sweep
  if (!start) { return; }
#endif
  duration_t *d_cur = start;
  to_trace_t *latter = end->head;
  void *former_addr, *latter_addr;
  while (d_cur != end) {
    assert(d_cur->closed == true);
    to_trace_t *former = d_cur->head;
    trace_address_list *former_cur = former->address;
    trace_address_list *latter_cur = latter->address;
    while (latter_cur) {
      while (former_cur) {
        // benign data race on reading and marking address
        former_addr = _atomic_load_relaxed(&former_cur->address);
        latter_addr = _atomic_load_relaxed(&latter_cur->address);
        if (!is_marked(former_addr) && former_addr == latter_addr) {
          _atomic_store_relaxed(&former_cur->address,
              (void*) ((uintptr_t)former_addr | 1));
          break;
        }
        former_cur = former_cur->next;
      }
      latter_cur = latter_cur->next;
    }
    d_cur = d_cur->next;
  }
}

#ifdef use_stw_mark_sweep
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  duration_t *current_d;
  duration_t *my_d = item->duration;
  assert(my_d);
  aba_entry_t aba_entry;

  aba_entry.aba = _atomic_load(&so_gc->aba_entry.aba);
  if (aba_entry.aba % 2 == 0) {
    _atomic_store(&so_gc->aba_entry.aba, aba_entry.aba + 1);
  }
  current_d = _atomic_exchange(&so_gc->current_d, new_headless_duration());
  assert(current_d);
  if (my_d == current_d) {
    current_d->entry = so_gc->aba_entry.entry;
    so_gc->aba_entry.entry = 0;
    _atomic_store(&current_d->stw, true);
  } else {
    current_d->entry = 1;
  }
  assert(current_d->entry > 0);
  current_d->head = item;
  current_d->closed = true;
  duration_spscq_t *d_q = &so_gc->duration_q;
  duration_spscq_push_atomic(d_q, current_d);

  if (current_d != my_d) {
    assert(current_d->stw != true);
    subsume_former_alias_address(duration_spscq_peek(d_q), current_d);
    set_collectible(this, current_d);
  }
  while (!_atomic_load(&my_d->stw)) { relax(); }
  set_collectible(this, my_d);
}
#else
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item)
{
  so_gc_t *so_gc = &this->so_gc;
  duration_t *current_d;
  duration_t *my_d = item->duration;
  assert(my_d);
  aba_entry_t aba_entry;
  do {
    aba_entry.aba = _atomic_load(&so_gc->aba_entry.aba);
    if (aba_entry.aba % 2 != 0) {
      relax();
      continue;
    }
    uint32_t new_aba = aba_entry.aba + 1;
    assert(new_aba % 2 == 1);
    if (_atomic_cas(&so_gc->aba_entry.aba, &aba_entry.aba, new_aba)) {
      current_d = so_gc->current_d;
      assert(current_d);
      current_d->entry = _atomic_exchange(&so_gc->aba_entry.entry, 0);
      if (current_d != my_d) {
        current_d->entry++;
      }
      current_d->head = item;
      current_d->closed = true;
      so_gc->current_d = new_headless_duration();
      duration_spscq_push(&so_gc->duration_q, current_d);
      uint32_t old_aba = _atomic_add(&so_gc->aba_entry.aba, 1);
      void_assert(old_aba % 2 == 1);
      break;
    }
  } while (true);

  if (current_d != my_d) {
    subsume_former_alias_address(my_d, current_d);
    set_collectible(this, current_d);
  }
  set_collectible(this, my_d);
}
#endif

void so_lockfree_address_wrapper_set_init(pony_ctx_t *ctx)
{
  assert(ctx->set == NULL);
  ctx->set = POOL_ALLOC(address_wrapper_set_t);
}

encore_so_t *encore_create_so(pony_ctx_t *ctx, pony_type_t *type)
{
  encore_so_t *this = (encore_so_t*) encore_create(ctx, type);
  this->so_gc.aba_entry.dw = 0;
  this->so_gc.current_d = new_headless_duration();
  this->so_gc.pending_lock.dw = 0;
  duration_spscq_init(&this->so_gc.duration_q);
  so_subord_mpscq_init(&this->so_gc.so_subord_mpscq);
  return this;
}

void so_lockfree_register_final_cb(void *p, so_lockfree_final_cb_fn final_cb)
{
  encore_so_t *this = p;
  this->so_gc.final_cb = final_cb;
}

typedef pony_trace_fn non_subord_trace_fn;
typedef pony_trace_fn subord_trace_fn;

void so_lockfree_register_subord_trace_fn(void *p, subord_trace_fn trace)
{
  encore_so_t *this = p;
  this->subord_trace = trace;
}

to_trace_t *so_to_trace_new(encore_so_t *this)
{
  to_trace_t *item = POOL_ALLOC(to_trace_t);
  item->address = NULL;
  return item;
}

static void so_to_trace(to_trace_t *item, void *p)
{
  trace_address_list *new = POOL_ALLOC(trace_address_list);
  new->address = p;
  new->next = item->address;
  item->address = new;
}

void encore_so_finalizer(void *p)
{
  assert(p);
  encore_so_t *this = p;
  sweep_all_delimiters(&this->so_gc.so_subord_mpscq);
  assert(this->so_gc.final_cb);
  pony_ctx_t *ctx = pony_ctx();
  this->so_gc.final_cb(ctx, this);
  assert(duration_spscq_peek(&this->so_gc.duration_q) == NULL);
  duration_spscq_destroy(&this->so_gc.duration_q);
  so_subord_mpscq_destroy(&this->so_gc.so_subord_mpscq);
}

static void so_lockfree_publish(encore_so_t *this, void *p)
{
  assert(p);
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  if (!f->wrapper) {
    so_lockfree_heap_push(this, f);
  }
}

static void so_lockfree_delay_recv(pony_ctx_t *ctx, void *p)
{
  address_wrapper_set_put(ctx->set, p);
}

void so_lockfree_spec_subord_field_apply(pony_ctx_t *ctx, encore_so_t *this,
    void *p)
{
  if (!p) { return; }
  so_lockfree_publish(this, p);
  gc_sendobject_shallow(ctx, p);
}

void so_lockfree_non_spec_subord_field_apply(pony_ctx_t *ctx, encore_so_t *this,
    void *p)
{
  if (!p) { return; }
  so_lockfree_publish(this, p);
  gc_sendobject_shallow(ctx, p);
  so_lockfree_inc_rc(p);
}

void so_lockfree_subord_fields_apply_done(pony_ctx_t *ctx)
{
  gc_sendobject_shallow_done(ctx);
}

void so_lockfree_subord_field_final_apply(pony_ctx_t *ctx, void *p,
    non_subord_trace_fn fn)
{
  if (!p) { return; }
  assert(p == UNFREEZE(p));
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  assert(f->wrapper);
  size_t rc = _atomic_sub(&f->rc, 1);
  assert(rc > 0);
  if (rc == 1) {
    // TODO need to rethink on supporting mark-sweep
    // can use store for optimization
    bool _r = _atomic_cas(&f->wrapper->p, &f, NULL);
    void_assert(_r);
    pony_gc_recv(ctx);
    pony_traceobject(ctx, f, fn);
    pony_recv_done(ctx);
  }
}

// TODO do we need non_subord_field_final_apply??

static bool so_lockfree_is_published(void *p)
{
  assert(p);
  assert(p == UNFREEZE(p));
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)p;
  return f->wrapper != NULL;
}

void so_lockfree_chain_final(pony_ctx_t *ctx, void *p, non_subord_trace_fn fn)
{
  if (!p) { return; }
  encore_passive_lf_so_t *f = (encore_passive_lf_so_t *)UNFREEZE(p);
  if (!f->wrapper) { return; }
  size_t rc = _atomic_sub(&f->rc, 1);
  assert(rc > 0);
  if (rc == 1) {
    // TODO need to rethink on supporting mark-sweep
    // can use store for optimization
    bool _r = _atomic_cas(&f->wrapper->p, &f, NULL);
    void_assert(_r);
    pony_gc_recv(ctx);
    pony_traceobject(ctx, f, fn);
    pony_recv_done(ctx);
  }
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

static void so_lockfree_recv(pony_ctx_t *ctx)
{
  void *p;
  while(ctx->lf_tmp_stack != NULL) {
    ctx->lf_tmp_stack = gcstack_pop(ctx->lf_tmp_stack, &p);
    gc_recvobject_shallow(ctx, p);
  }
  gc_recvobject_shallow_done(ctx);
}

void so_lockfree_register_acc_to_recv(pony_ctx_t *ctx, to_trace_t *item)
{
  size_t i = HASHMAP_BEGIN;
  address_wrapper_set_t *set = ctx->set;
  trace_address_t* p;

  while ((p = address_wrapper_set_next(set, &i)) != NULL) {
    so_to_trace(item, p);
  }
  // reset
  address_wrapper_set_destroy(set);
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

bool _so_lockfree_cas_try_wrapper(pony_ctx_t *ctx, encore_so_t *this,
    void *X, void *Y, void *_Z, pony_trace_fn F)
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
    so_lockfree_publish(this, Z);
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

bool _so_lockfree_cas_link_wrapper(pony_ctx_t *ctx, encore_so_t *this,
    void *X, void *Y, void *Z, pony_trace_fn F)
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
      so_lockfree_delay_recv(ctx, Y);
    }
    so_lockfree_publish(this, Z);
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
      so_lockfree_delay_recv(ctx, Y);
    }
  } else {
    if (so_lockfree_dec_rc(Z) == 1) {
      so_lockfree_delay_recv(ctx, Z);
    }
  }
  return ret;
}

// TODO I can probably unite the two
void so_lockfree_assign_spec_wrapper(pony_ctx_t *ctx, void *lhs, void *rhs,
    pony_trace_fn F)
{
  so_lockfree_inc_rc(rhs);
  if (so_lockfree_dec_rc(lhs) == 1 && so_lockfree_is_published(lhs)) {
      so_lockfree_delay_recv(ctx, lhs);
  }
}

void _so_lockfree_assign_subord_wrapper(pony_ctx_t *ctx, void *lhs, void *rhs)
{
  so_lockfree_inc_rc(rhs);
  if (so_lockfree_dec_rc(lhs) == 1 && so_lockfree_is_published(lhs)) {
      so_lockfree_delay_recv(ctx, lhs);
  }
}
