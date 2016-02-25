#include "party.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "closure.h"
#include "list.h"
#include <array.h>

typedef struct fmap_s fmap_s;
typedef par_t* (*fmapfn)(par_t*, fmap_s*);

// TODO: add EMPTY_PAR, JOIN_PAR
enum PTAG { VALUE_PAR, FUTURE_PAR, FUTUREPAR_PAR, PAR_PAR};
enum VAL_OR_PAR {VAL, PAR};

// TODO: uncomment once we handle the empty par case
/* typedef struct EMPTY_PARs {} EMPTY_PARs; */

typedef struct VALUE_PARs { value_t val; enum VAL_OR_PAR tag;} VALUE_PARs;
typedef struct FUTURE_PARs { future_t* fut; } FUTURE_PARs;
typedef struct FUTUREPAR_PARs { future_t* fut; } FUTUREPAR_PARs;
typedef struct PAR_PARs { struct par_t* left; struct par_t* right; } PAR_PARs;
typedef struct JOIN_PARs { struct par_t* join; } JOIN_PARs;

struct par_t {
    enum PTAG tag;
    pony_type_t* rtype;
    union ParU {
      /* EMPTY_PARs s; */
      VALUE_PARs v;
      FUTURE_PARs f;
      PAR_PARs p;
      FUTUREPAR_PARs fp;
      JOIN_PARs j;
      /* struct EMPTY_PARs; */
      struct VALUE_PARs;
      struct FUTURE_PARs;
      struct PAR_PARs;
      struct JOIN_PARs;
    } data;
};

pony_type_t party_type =
  {
    .id=ID_PARTY,
    .size=sizeof(struct par_t),
    .trace=party_trace
  };

#define get_rtype(x) (x)->rtype

// MACRO for setting the parallel collection. Needs gcc-4.9
/* #define set_par(elem1, elem2, par) \ */
/*   _Generic((elem1),                \ */
/*   future_t*: set_par_future,       \ */
/*   par_t*: set_par_par,             \ */
/*   encore_arg_t: set_par_value)(elem1, elem2, par) */

static inline void set_par_value(encore_arg_t val,
                                 void * __attribute__((unused))null,
                                 par_t * const par){
  par->data.val = val;
}

static inline void set_par_future(future_t * const fut,
                                  void * __attribute__((unused)) null,
                                  par_t *par){
  par->data.fut = fut;
}

static inline void set_par_par(par_t * const rpar, par_t * const lpar,
                               par_t * const par){
  switch(par->tag){
  case PAR_PAR: {
      par->data.left = lpar;
      par->data.right = rpar;
      break;
  }
  default: assert(0);
  }
}

void party_trace(pony_ctx_t* ctx, void* p){
  par_t *obj = p;
  if(obj->rtype == ENCORE_ACTIVE){
    pony_traceactor(ctx, (pony_actor_t*) obj->data.v.val.p);
  }else if(obj->rtype != ENCORE_PRIMITIVE){
    switch(obj->tag){
    /* case EMPTY_PAR: break; */
    case VALUE_PAR: {
      pony_traceobject(ctx, obj->data.v.val.p, obj->rtype->trace);
      break;
    }
    case FUTURE_PAR: {
      pony_traceobject(ctx, obj->data.f.fut, obj->rtype->trace);
      break;
    }
    case PAR_PAR: {
      party_trace(ctx, obj->data.p.left);
      party_trace(ctx, obj->data.p.right);
      break;
    }
    case FUTUREPAR_PAR: {
      pony_traceobject(ctx, obj->data.fp.fut, obj->rtype->trace);
      break;
    }
    /* case JOIN_PAR: { */
    /*   party_trace(obj->data.j.join); */
    /*   break; */
    /* } */
    }
  }
}

struct fmap_s{
  closure_t* fn;
  pony_type_t const * rtype;
};

/*
 * Parallel constructors
 */

static par_t* init_par(pony_ctx_t* ctx, enum PTAG tag, pony_type_t const * const rtype){
  par_t* res = encore_alloc(ctx, sizeof* res);
  res->tag = tag;
  res->rtype = rtype;
  return res;
}

// TODO: (kiko) uncomment once we can create empty computations
/* par_t* new_par_empty(pony_type_t const * const rtype){ */
/*   return init_par(EMPTY_PAR, rtype); */
/* } */

par_t* new_par_v(pony_ctx_t* ctx, encore_arg_t val, pony_type_t const * const rtype){
  par_t* p = init_par(ctx, VALUE_PAR, rtype);
  set_par_value(val, NULL, p);
  return p;
}

par_t* new_par_f(pony_ctx_t* ctx, future_t* f, pony_type_t const * const rtype){
  par_t* p = init_par(ctx, FUTURE_PAR, rtype);
  set_par_future(f, NULL, p);
  return p;
}

par_t* new_par_p(pony_ctx_t* ctx, par_t* p1, par_t* p2,
                 pony_type_t const * const rtype){
  par_t* p = init_par(ctx, PAR_PAR, rtype);
  set_par_par(p1, p2, p);
  return p;
}

par_t* new_par_fp(pony_ctx_t* ctx, future_t* f, pony_type_t const * const rtype){
  par_t* p = init_par(ctx, FUTUREPAR_PAR, rtype);
  set_par_future(f, NULL, p);
  return p;
}

// TODO: enable once we can create J
/* par_t* new_par_join(par_t* const p, pony_type_t const * const rtype){ */
/*   par_t* par = init_par(JOIN_PAR, rtype); */
/*   par->data.join = p; */
/*   return par; */
/* } */

//---------------------------------------
// SEQUENCE COMBINATOR
//---------------------------------------

// Forward declaration
static par_t* fmap(pony_ctx_t* ctx, closure_t* const f, par_t* const in,
                   pony_type_t const * const rtype);

static value_t fmap_party_closure(pony_ctx_t* ctx, value_t args[], void* const env){
  par_t* p = (par_t*)args[0].p;
  fmap_s* fm = env;
  return (value_t){.p = fmap(ctx, fm->fn, p, get_rtype(fm))};
}

static inline future_t* chain_party_to_function(pony_ctx_t* ctx,
                                                par_t* const in,
                                                fmap_s* const fm,
                                                closure_fun clos){
  future_t* rf = (future_t*)future_mk(ctx, in->rtype);
  closure_t* cp = closure_mk(ctx, clos, fm, NULL);
  return future_chain_actor(ctx, in->data.fut, (future_t*)rf, cp);
}

static inline par_t* fmap_run_fp(pony_ctx_t* ctx, par_t* const in, fmap_s* const f){
  future_t* fut = chain_party_to_function(ctx, in, f, fmap_party_closure);
  return new_par_fp(ctx, fut, get_rtype(f));
}

static inline par_t* fmap_run_v(pony_ctx_t* ctx, par_t* const in, fmap_s* const f){
  value_t v = closure_call(ctx, f->fn, (value_t[]){in->data.val});
  return new_par_v(ctx, v, get_rtype(f));
}

static inline par_t* fmap_run_f(pony_ctx_t* ctx, par_t* const in, fmap_s* const f){
  future_t* rf = (future_t*)future_mk(ctx, in->rtype);
  future_t* chained_fut = future_chain_actor(ctx, in->data.fut, rf, f->fn);
  return new_par_f(ctx, chained_fut, get_rtype(f));
}

// WARNING:
// this function is only used for fmap J, which guarantees
// that args is of: {.p = par_t* }
/* static encore_arg_t fmap_fmap_closure(value_t args[], void* const env){ */
/*   fmap_s* fm = env; */
/*   encore_arg_t arg = args[0]; */
/*   return (encore_arg_t) {.p = fmap(fm->fn, (par_t*) arg.p, fm->rtype)}; */
/* } */

/* static inline par_t* fmap_run_j(par_t* const in, fmap_s* const f){ */
/*   fmap_s* fm = (fmap_s*)encore_alloc(sizeof* fm); */
/*   *fm = (fmap_s){.fn=f->fn, .rtype = f->rtype}; */
/*   closure_t* clos = closure_mk(fmap_fmap_closure, fm, NULL); */
/*   par_t* p = fmap(clos, in->data.join, get_rtype(fm)); */
/*   return new_par_join(p, get_rtype(f)); */
/* } */

/**
 *  fmap: (a -> b) -> Par a -> Par b
 *
 *  @param f Closure function to be called
 *  @param in Parallel collection data structure to call \p f on
 *  @param rtype The returned runtime type (ENCORE_PRIMITIVE or ENCORE_ACTIVE)
 *  @return a pointer to a new parallel collection of \p rtype runtime type
 */

// TODO: enable EMPTY_PAR and JOIN_PAR once it is added to the language
static par_t* fmap(pony_ctx_t* ctx, closure_t* const f, par_t* const in,
                   pony_type_t const * const rtype){
  fmap_s *fm = (fmap_s*) encore_alloc(ctx, sizeof* fm);
  *fm = (fmap_s){.fn = f, .rtype=rtype};
  switch(in->tag){
  /* case EMPTY_PAR: return new_par_empty(rtype); */
  case VALUE_PAR: return fmap_run_v(ctx, in, fm);
  case FUTURE_PAR: return fmap_run_f(ctx, in, fm);
  case PAR_PAR: {
    par_t* left = fmap(ctx, f, in->data.left, rtype);
    par_t* right = fmap(ctx, f, in->data.right, rtype);
    return new_par_p(ctx, left, right, rtype);
  }
  case FUTUREPAR_PAR: return fmap_run_fp(ctx, in, fm);
  /* case JOIN_PAR: return fmap_run_j(in, fm); */
  }
}

par_t* party_sequence(pony_ctx_t* ctx, par_t* const p, closure_t* const f,
                      pony_type_t const * const rtype){
  return fmap(ctx, f, p, rtype);
}

//---------------------------------------
// JOIN COMBINATOR
//---------------------------------------

static inline par_t* party_join_v(pony_ctx_t* ctx, par_t* const p){
   return ((par_t*)p->data.val.p);
}

// TODO: uncomment when the empty par is added to the language
static inline par_t* party_join_p(pony_ctx_t* ctx, par_t* const p){
  /* if(p->data.left->tag == EMPTY_PAR){ */
  /*   return party_join(p->data.right); */
  /* }else if(p->data.right->tag == EMPTY_PAR){ */
  /*   return party_join(p->data.left); */
  /* }else{ */
  par_t* pleft = party_join(ctx, p->data.left);
  par_t* pright = party_join(ctx,p->data.right);
  assert(get_rtype(pleft) == get_rtype(pright));
  return new_par_p(ctx, pleft, pright, get_rtype(pleft));
  /* } */
}

static value_t party_join_fp_closure(pony_ctx_t* ctx,
                                     value_t args[],
                                     void* __attribute__ ((unused)) env){
  par_t* const p = (par_t*)args[0].p;
  return (value_t){.p = party_join(ctx, p)};
}

static inline par_t* party_join_fp(pony_ctx_t* ctx, par_t* const p){
  future_t* const fut = p->data.fut;
  future_t* const chained_fut = future_mk(ctx, p->rtype);
  closure_t* const clos = closure_mk(ctx, party_join_fp_closure, NULL, NULL);
  future_chain_actor(ctx, fut, chained_fut, clos);
  return new_par_fp(ctx, chained_fut, p->rtype);
}

par_t* party_join(pony_ctx_t* ctx, par_t* const p){
  switch(p->tag){
  /* case EMPTY_PAR: return p; */
  case VALUE_PAR: return party_join_v(ctx, p);
  case FUTURE_PAR: return new_par_fp(ctx, p->data.fut, get_rtype(p));
  case PAR_PAR: return party_join_p(ctx, p);
  case FUTUREPAR_PAR: return party_join_fp(ctx, p);
  /* case JOIN_PAR: return party_join(party_join(p->data.join)); */
  }
}

//----------------------------------------
// EXTRACT COMBINATOR
//----------------------------------------

static inline list_t* extract_helper(list_t * const list, par_t * const p,
                                     pony_type_t const * const type){
  pony_ctx_t* ctx = pony_ctx();
  switch(p->tag){
  /* case EMPTY_PAR: return list; */
  case VALUE_PAR: return list_push(list, p->data.v.val);
  case FUTURE_PAR: {
    future_t *fut = p->data.f.fut;
    value_t val = future_get_actor(ctx, fut);
    return list_push(list, val);
  }
  case PAR_PAR: {
    par_t *left = p->data.left;
    par_t *right = p->data.right;
    list_t* tmp_list = extract_helper(list, left, type);
    return extract_helper(tmp_list, right, type);
  }
  case FUTUREPAR_PAR: {
    future_t *fut = p->data.f.fut;
    par_t* par = future_get_actor(ctx, fut).p;
    return extract_helper(list, par, type);
  }
  }
}

static inline array_t* list_to_array(list_t* const list,
                                     pony_type_t const * const type){
  pony_ctx_t* ctx = pony_ctx();
  size_t size = list_length(list);
  array_t* arr = array_mk(ctx, size, type);
  list_t* temp_list = list_index(list, 0);

  // TODO: If the list is too big, distribute work using tasks
  for(size_t i=0; i<size; i++) {
    array_set(arr, i, list_data(temp_list));
    temp_list = list_index(temp_list, 1);
  }
  return arr;
}

array_t* party_extract(pony_ctx_t* ctx, par_t * const p, pony_type_t const * const type){
  list_t *list = NULL;
  list_t* const tmp_list = extract_helper(list, p, type);

  return list_to_array(tmp_list, type);
}