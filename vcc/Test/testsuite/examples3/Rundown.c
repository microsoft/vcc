#include <vcc.h>
#include <stdlib.h>

_(atomic_inline) unsigned int InterlockedIncrement(volatile unsigned int *p) {
  *p = *p + 1;
  return *p;
}

_(atomic_inline) unsigned int InterlockedDecrement(volatile unsigned int *p) {
  *p = *p - 1;
  return *p;
}


typedef _(claimable) struct _Protector {
  int dummy;
} Protector;

typedef _(claimable) _(volatile_owns) struct _Rundown {
   _(ghost volatile \claim self_claim;)
   _(ghost \object protected_obj;)
  volatile unsigned int count;

   _(ghost volatile \bool alive;)
   _(ghost volatile \bool enabled;)
   _(ghost Protector enabled_protector;)
  _(invariant \old((&enabled_protector)->\closed) ==> \unchanged(enabled) && \unchanged(alive))

  _(invariant !alive ==> !enabled && count == 0)
  // cannot set both count and alive in one step
  _(invariant \old(count) > 0 && \old(alive) ==> alive)
  _(invariant alive ==>
               \mine(protected_obj) &&
               \mine(self_claim) &&
               \claims_object(self_claim, \this) &&
               self_claim->\claim_count == count)
  _(invariant \old(alive) ==> \unchanged(self_claim))

  _(invariant !enabled ==> count <= \old(count))

} Rundown;

void InitializeRundown(Rundown *r _(ghost \object obj) _(out \claim rdi))
  _(writes \extent(r), obj)
  _(requires \wrapped(obj))
  _(ensures \claims_object(rdi, r))
  _(ensures \claims_object(rdi, &r->enabled_protector))
  _(ensures \fresh(rdi) && \wrapped0(rdi) && \claims(rdi, r->enabled && r->protected_obj == obj))
  _(ensures r->\claim_count == 2)
  _(ensures \wrapped(&r->enabled_protector) && (&r->enabled_protector)->\claim_count == 1)
  _(ensures \wrapped(r))
{
  _(ghost \claim s1)

  r->count = 0;
  _(ghost r->\owns =  {});
  _(ghost (&r->enabled_protector)->\owns =  {});
  _(ghost { r->protected_obj = obj; r->alive = \false; r->enabled = \false; })
  _(wrap r)

  _(assert \not_shared(r))

  _(ghost {
    _(atomic r) {
      s1 = \make_claim({r}, \true);
      _(begin_update)
      r->alive = \true;
      r->enabled = \true;
      r->self_claim = s1;
      _(ghost r->\owns += obj);
      _(ghost r->\owns += s1);
    }
    _(wrap &r->enabled_protector)
    // we can still claim r->enabled, as the state is havoced only at the BEGINNING of the atomic,
    // not at the end
    rdi = \make_claim({r, &r->enabled_protector}, r->enabled && r->protected_obj == obj);
  })
}

void ReferenceRundown(Rundown *r _(out \claim res) _(ghost \claim rdi))
  // we want a claim to our enabled rundown
  _(always rdi, r->\closed && r->enabled)
  // we will give out a fresh claim with zero ref_cnt
  _(ensures \wrapped0(res) && \fresh(res))
  // the claim will reference r->self_claim, will guarantee that the protected_obj is closed and the rundown is initialized
  _(ensures \claims(res, \claims_object(res, r->self_claim) && r->\closed && (r->protected_obj)->\closed && r->count > 0))
{
   _(ghost \claim c;)

  _(atomic r, rdi) {
    _(assume r->count < 0xffffffff)
    InterlockedIncrement(&r->count);
     _(ghost res = \make_claim({r->self_claim}, r->alive /* TODO <-- was needed with /2 */ && r->count > 0 && (r->protected_obj)->\closed && \when_claimed(r->self_claim) == r->self_claim);)
  }
}

void DereferenceRundown(Rundown *r _(ghost \claim  h))
  // we write the claim, what will we do with it? we're not telling.
  _(writes h)
  // we want a claim to self_claim with no outstanding references guaranteeing that rundown is fully initialized
  _(requires \wrapped0(h) && \claims(h, \claims_object(h, r->self_claim) && r->\closed && r->count > 0))
{
  _(atomic h, r) {
    _(ghost \destroy_claim(h, {r->self_claim}));
    InterlockedDecrement(&r->count);
  }
}

typedef _(claimable) struct _Resource {
  volatile int x;
  Rundown rd;
} Resource;

typedef struct _RundownContainer {
  Resource *rsc;
  int enabled;
   _(ghost \claim rd_claim;)

  _(invariant \mine(rd_claim, &rsc->rd, &rsc->rd.enabled_protector))

  _(invariant \claims_object(rd_claim, &rsc->rd))
  _(invariant \claims_object(rd_claim, &rsc->rd.enabled_protector))

  _(invariant (&rsc->rd.enabled_protector)->\claim_count == 1)
  _(invariant (&rsc->rd)->\claim_count == 2)
  _(invariant rd_claim->\claim_count == 0)

  _(invariant \claims(rd_claim, \when_claimed(rsc)->rd.enabled == \when_claimed(enabled)))
  _(invariant \claims(rd_claim, \when_claimed(rsc)->rd.alive))
  _(invariant \claims(rd_claim, \when_claimed(rsc)->rd.protected_obj == \when_claimed(rsc)))
} RundownContainer;

void InitializeRundownContainer(Resource *rsc, RundownContainer *cont)
  _(writes \span(cont), rsc, \extent(&rsc->rd))
  _(requires \mutable(&rsc->rd.enabled_protector))
  _(requires \wrapped(rsc))
  _(ensures \wrapped(cont))
{
  cont->rsc = rsc;
  InitializeRundown(&rsc->rd _(ghost rsc) _(out cont->rd_claim));
  cont->enabled = 1;

  _(wrap cont)
}

void FinalizeRundownContainer(RundownContainer *cont)
  _(writes cont)
  _(maintains \wrapped(cont))
  _(requires cont->enabled)
  _(ensures !cont->enabled)
{
  _(ghost \claim tmp)
  _(ghost Rundown *rd)

  _(unwrap cont)
  cont->enabled = 0;
  _(ghost {
    rd = &cont->rsc->rd;
    _(atomic rd) {
      _(assert \active_claim(cont->rd_claim))
      _(ghost \destroy_claim(cont->rd_claim, {rd, &rd->enabled_protector}));
      _(unwrap &rd->enabled_protector)
      _(begin_update)
      rd->enabled = 0;
    }
    _(wrap &rd->enabled_protector)
    tmp = \make_claim({rd, &rd->enabled_protector}, rd->alive && !rd->enabled && rd->protected_obj == \when_claimed(cont->rsc));
    _(ghost cont->\owns -= cont->rd_claim);
    cont->rd_claim = tmp;
    _(ghost cont->\owns += cont->rd_claim);
    _(wrap cont)
  })
}

Resource *KillRundownContainerDead(RundownContainer *cont)
  _(writes cont)
  _(requires \wrapped(cont))
  _(ensures \old(cont->rsc) == \result)
  _(ensures \wrapped(\result))
  _(requires !cont->enabled)
  _(requires \malloc_root(cont))
{
  Resource *rsc;
  unsigned int cur_count;
  Rundown *rd = &cont->rsc->rd;
  _(ghost \claim tmp, is_zero;)

  _(unwrap cont)
    rsc = cont->rsc;

    do
      _(invariant (cont->rd_claim)->\claim_count == 0)
      _(invariant \wrapped(cont->rd_claim))
      _(writes cont->rd_claim)
    {
      _(atomic cont->rd_claim, rd) {
        cur_count = rd->count;

           _(ghost if (cur_count == 0) {
             is_zero = \make_claim({cont->rd_claim}, rd->count == 0);
           })
      }
    } while (cur_count != 0);

    _(ghost {
      _(atomic rd) {
        _(assert \active_claim(is_zero))
        _(assert \active_claim(cont->rd_claim))
        _(ghost \destroy_claim(is_zero, {cont->rd_claim}));
        _(ghost \destroy_claim(cont->rd_claim, {rd, &rd->enabled_protector}));
        _(unwrap &rd->enabled_protector)
        _(begin_update)
        tmp = rd->self_claim;
        _(ghost rd->\owns -= rd->self_claim);
        _(ghost rd->\owns -= rsc); // TODO the /2 version worked without this
        rd->alive = 0;
      }
      _(ghost \destroy_claim(tmp, {rd}));
      _(unwrap rd)
    })
  free(cont);
  return rsc;
}

void UseRundown(Resource *a, Rundown *r _(ghost \claim rdi))
  _(always rdi, r->\closed && r->protected_obj == a && r->enabled)
{
   _(ghost \claim ac;)
  ReferenceRundown(r _(out ac) _(ghost rdi));
  _(atomic rdi, ac, a) {
    a->x = 12;
  }
  DereferenceRundown(r _(ghost ac));
}

/*`
Verification of _Rundown#adm succeeded.
Verification of _RundownContainer#adm succeeded.
Verification of InitializeRundown succeeded.
Verification of ReferenceRundown succeeded.
Verification of DereferenceRundown succeeded.
Verification of InitializeRundownContainer succeeded.
Verification of FinalizeRundownContainer succeeded.
Verification of KillRundownContainerDead succeeded.
Verification of UseRundown succeeded.
`*/
