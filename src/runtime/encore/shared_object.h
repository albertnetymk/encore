#ifndef SHARED_OBJECT_H_L6JOK8YX
#define SHARED_OBJECT_H_L6JOK8YX

#include "encore.h"

typedef struct duration_t duration_t;

typedef struct duration_spscq_t {
  duration_t *head;
  duration_t *tail;
} duration_spscq_t;

__pony_spec_align__(
  typedef struct dwcas_t {
    union {
      struct {
        uintptr_t aba;
        duration_t *current;
      };
      dw_t dw;
    };
  } dwcas_t, 16
);

typedef struct {
  union {
    struct {
      uint32_t aba;
      uint32_t entry;
    };
    uint64_t dw;
  };
} aba_entry_t;

typedef struct {
  union {
    struct {
      uint32_t pending;
      uint32_t lock;
    };
    uint64_t dw;
  };
} pending_lock_t;

typedef void (*so_lockfree_final_cb_fn) (pony_ctx_t *ctx, void *p);

typedef struct so_gc_t {
  so_lockfree_final_cb_fn final_cb;
  aba_entry_t aba_entry;
  duration_t *current_d;
  duration_spscq_t duration_q;
  pending_lock_t pending_lock;
} so_gc_t;

typedef struct encore_so_t
{
  pony_actor_pad_t pad;
  // Everything else that goes into an encore_actor that's not part of PonyRT
  bool resume;
  int await_counter;
  int suspend_counter;
  pthread_mutex_t *lock;
#ifndef LAZY_IMPL
  ucontext_t uctx;
  ucontext_t home_uctx;
  volatile bool run_to_completion;
  stack_page *page;
#else
  ucontext_t *saved;
#endif
  pony_type_t *_enc__self_type;
  so_gc_t so_gc;
} encore_so_t;

typedef struct encore_passive_lf_so_t {
  pony_type_t *t;
  struct encore_passive_lf_so_t *prev;
  struct encore_passive_lf_so_t *next;
  size_t rc;
  bool published;
} encore_passive_lf_so_t;

typedef struct so_lockfree_padding {
    char data[sizeof(encore_passive_lf_so_t) - sizeof(void*)];
} so_lockfree_padding;

#define FREEZE(field) ((void*)(((uintptr_t)field) | 1UL))
#define UNFREEZE(field) ((void*)(((uintptr_t)field) & ~1UL))

#define _SO_LOCKFREE_CAS_TRY_WRAPPER(X, Y, Z, F) \
  _so_lockfree_cas_try_wrapper(_ctx, X, Y, Z, F)

#define _SO_LOCKFREE_CAS_EXTRACT_WRAPPER(X, F) \
  _so_lockfree_cas_extract_wrapper(&X, F)

#define _SO_LOCKFREE_CAS_LINK_WRAPPER(X, Y, Z, F) \
  _so_lockfree_cas_link_wrapper(_ctx, X, Y, Z, F)

#define _SO_LOCKFREE_CAS_UNLINK_WRAPPER(X, Y, Z, F) \
  _so_lockfree_cas_unlink_wrapper(_ctx, X, Y, Z, F)

#define _SO_LOCKFREE_ASSIGN_SPEC_WRAPPER(LHS, RHS, F) \
  so_lockfree_assign_spec_wrapper(_ctx, LHS, RHS, F)

#define _SO_LOCKFREE_ASSIGN_SUBORD_WRAPPER(LHS, RHS) \
  _so_lockfree_assign_subord_wrapper(LHS, RHS)

typedef struct to_trace_t to_trace_t;

encore_so_t *encore_create_so(pony_ctx_t *ctx, pony_type_t *type);
void so_lockfree_register_final_cb(void *p, so_lockfree_final_cb_fn final_cb);
void so_lockfree_spec_subord_field_apply(pony_ctx_t *ctx, void *p);
void so_lockfree_non_spec_subord_field_apply(pony_ctx_t *ctx, void *p);
void so_lockfree_subord_fields_apply_done(pony_ctx_t *ctx);
void so_lockfree_subord_field_final_apply(pony_ctx_t *ctx, void *p);
to_trace_t *so_to_trace_new(encore_so_t *this);
void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item);
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item);
void encore_so_finalinzer(void *p);
void pony_gc_collect_to_send(pony_ctx_t* ctx);
void pony_gc_collect_to_send_done(pony_ctx_t *ctx);
void pony_gc_collect_to_recv(pony_ctx_t* ctx);
void pony_gc_collect_to_recv_done(pony_ctx_t *ctx);
void so_lockfree_send(pony_ctx_t *ctx);
void so_lockfree_unsend(pony_ctx_t *ctx);
void so_lockfree_recv(pony_ctx_t *ctx);
void so_lockfree_delay_recv_using_send(pony_ctx_t *ctx, void *p);
void so_lockfree_register_acc_to_recv(pony_ctx_t *ctx, to_trace_t *item);
void so_lockfree_set_trace_boundary(pony_ctx_t *ctx, void *p);
void so_lockfree_chain_final(pony_ctx_t *ctx, void *p);
size_t so_lockfree_inc_rc(void *p);
size_t so_lockfree_dec_rc(void *p);
bool so_lockfree_is_published(void *p);
bool _so_lockfree_cas_try_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *Z,
    pony_trace_fn F);
void* _so_lockfree_cas_extract_wrapper(void *_address, pony_trace_fn F);
bool _so_lockfree_cas_link_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *Z,
    pony_trace_fn F);
bool _so_lockfree_cas_unlink_wrapper(pony_ctx_t *ctx, void *X, void *Y, void *Z,
    pony_trace_fn F);
void so_lockfree_assign_spec_wrapper(pony_ctx_t *ctx, void *lhs, void *rhs,
    pony_trace_fn F);
void _so_lockfree_assign_subord_wrapper(void *lhs, void *rhs);
void so_lockfree_non_spec_field_apply(void *p);
#endif /* end of include guard: SHARED_OBJECT_H_L6JOK8YX */
