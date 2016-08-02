#ifndef SHARED_OBJECT_H_L6JOK8YX
#define SHARED_OBJECT_H_L6JOK8YX

#include "encore.h"

typedef struct queue_node_t queue_node_t;

__pony_spec_align__(
  typedef struct {
    union {
      struct {
        queue_node_t* node_of_head;
        queue_node_t* head;
      };
      dw_t dw;
    };
  } double_head_t, 16
);

typedef struct double_head_mpscq_t
{
  double_head_t double_head;
  queue_node_t* tail;
} double_head_mpscq_t;

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

typedef struct so_gc_t {
  uint32_t start_index;
  aba_entry_t aba_entry;
  dwcas_t cas;
  double_head_mpscq_t in_out_q;
  dwcas_t cas_d;
  duration_spscq_t duration_q;
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

#define FREEZE(field) ((void*)(((uintptr_t)field) | 1UL))
#define UNFREEZE(field) ((void*)(((uintptr_t)field) & ~1UL))

#define _CAS_LINK_WRAPPER(X, Y, Z, F)            \
  ({                                             \
    bool ret;                                    \
    pony_gc_try_send(_ctx);                      \
    so_lockfree_set_trace_boundary(_ctx, Y);     \
    pony_traceobject(_ctx, Z, F);                \
    pony_gc_try_send_done(_ctx);                 \
    ret = __sync_bool_compare_and_swap(X, Y, Z); \
    if (ret) {                                   \
      so_lockfree_send(_ctx);                    \
    } else {                                     \
      so_lockfree_unsend(_ctx);                  \
    }                                            \
    ret;                                         \
  })                                             \

#define _CAS_UNLINK_WRAPPER(X, Y, Z, F, IF)             \
  ({                                                    \
    pony_gc_try_recv(_ctx);                             \
    so_lockfree_set_trace_boundary(_ctx, NULL);         \
    pony_traceobject(_ctx, _this, IF);                  \
    pony_gc_try_recv_done(_ctx);                        \
    bool reachable = so_lockfree_is_reachable(_ctx, Y); \
    bool ret = __sync_bool_compare_and_swap(X, Y, Z);   \
    if (ret) {                                          \
      pony_gc_try_recv(_ctx);                           \
      so_lockfree_set_trace_boundary(_ctx, Z);          \
      pony_traceobject(_ctx, Y, F);                     \
      pony_gc_try_recv_done(_ctx);                      \
      so_lockfree_recv(_ctx);                           \
      if (!reachable) {                                 \
        so_lockfree_delay_recv_using_send(_ctx, Y);     \
      }                                                 \
    }                                                   \
    ret;                                                \
  })                                                    \

// #define _UNLINK_LEFTOVER(P)
//   ({
//    // deal with double bar ownership fields
//   })

#define _CAS_TRY_WRAPPER(X, Y, Z, F)             \
  ({                                             \
    bool ret;                                    \
    pony_gc_try_send(_ctx);                      \
    so_lockfree_set_trace_boundary(_ctx, NULL);  \
    pony_traceobject(_ctx, (UNFREEZE(Z)), F);    \
    pony_gc_try_send_done(_ctx);                 \
    ret = __sync_bool_compare_and_swap(X, Y, Z); \
    if (ret) {                                   \
      so_lockfree_send(_ctx);                    \
    } else {                                     \
      so_lockfree_unsend(_ctx);                  \
    }                                            \
    ret;                                         \
  })                                             \

#define _ASSIGN_CONSUME_WRAPPER(X, F)          \
  ({                                           \
   pony_gc_try_send(_ctx);                     \
   so_lockfree_set_trace_boundary(_ctx, NULL); \
   pony_traceobject(_ctx, X, F);               \
   pony_gc_try_send_done(_ctx);                \
   so_lockfree_send(_ctx);                     \
   })                                          \

typedef struct to_trace_t to_trace_t;

encore_so_t *encore_create_so(pony_ctx_t *ctx, pony_type_t *type);
to_trace_t *so_to_trace_new(encore_so_t *this);
void so_lockfree_on_entry(encore_so_t *this, to_trace_t *item);
void so_lockfree_on_exit(encore_so_t *this, to_trace_t *item);
void encore_so_finalinzer(void *p);
void pony_gc_try_send(pony_ctx_t* ctx);
void pony_gc_try_send_done(pony_ctx_t *ctx);
void pony_gc_try_recv(pony_ctx_t* ctx);
void pony_gc_try_recv_done(pony_ctx_t *ctx);
void so_lockfree_send(pony_ctx_t *ctx);
void so_lockfree_unsend(pony_ctx_t *ctx);
void so_lockfree_recv(pony_ctx_t *ctx);
bool so_lockfree_is_reachable(pony_ctx_t *ctx, void *target);
void so_lockfree_delay_recv_using_send(pony_ctx_t *ctx, void *p);
void so_lockfree_register_acc_to_recv(pony_ctx_t *ctx, to_trace_t *item);
void so_lockfree_set_trace_boundary(pony_ctx_t *ctx, void *p);
#endif /* end of include guard: SHARED_OBJECT_H_L6JOK8YX */
