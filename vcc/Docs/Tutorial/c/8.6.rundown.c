#include <vcc.h>
#include <limits.h>

/*{xchg}*/
_(atomic_inline) unsigned InterlockedCompareExchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}
/*{refcnt}*/
struct RefCnt {
  volatile unsigned cnt;
  _(ghost \object resource;)
  _(invariant \mine(resource))
  _(invariant \claimable(resource))
  _(invariant resource->\claim_count == cnt >> 1)
  _(invariant \old(cnt & 1) ==> \old(cnt) >= cnt)
};
/*{init}*/
void init(struct RefCnt *r _(ghost \object rsc))
  _(writes \span(r), rsc)
  _(requires \wrapped0(rsc) && \claimable(rsc))
  _(ensures \wrapped(r) && r->resource == rsc)
{
  r->cnt = 0;
  _(ghost r->resource = rsc;)
  _(wrap r)
}
/*{incr}*/
int try_incr(struct RefCnt *r _(ghost \claim c)
             _(	out \claim ret))
  _(always c, r->\closed)
  _(ensures \result == 0 ==>
     \claims_object(ret, r->resource) && \wrapped0(ret) && \fresh(ret))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) return -1;

    _(assume v <= UINT_MAX - 2)
    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v + 2, v);
      _(ghost
        if (v == n) ret = \make_claim({r->resource}, \true);)
    }

    if (v == n) return 0;
  }
}
/*{decr}*/
void decr(struct RefCnt *r _(ghost \claim c) _(ghost \claim handle))
  _(always c, r->\closed)
  _(requires \claims_object(handle, r->resource) && \wrapped0(handle))
  _(requires c != handle)
  _(writes handle)
{
  unsigned v, n;

  for (;;)
    _(invariant \wrapped(c) && \wrapped0(handle))
  {
    _(atomic c, r) {
      v = r->cnt;
      _(assert \active_claim(handle))
      _(assert v >= 2)
    }

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v - 2, v);
      _(ghost
        if (v == n) {
          _(ghost \destroy_claim(handle, {r->resource}));
        })
    }

    if (v == n) break;
  }
}
/*{use}*/
_(claimable) struct A {
  volatile int x;
};

struct B {
  struct RefCnt rc;
  struct A a;
  _(invariant \mine(&rc))
  _(invariant rc.resource == &a)
};

void useb(struct B *b _(ghost \claim c))
  _(always c, b->\closed)
{
  _(ghost \claim ac;)
  if (try_incr(&b->rc _(ghost c) _(out ac)) == 0) {
    _(atomic &b->a, ac) {
      b->a.x = 10;
    }
    decr(&b->rc _(ghost c) _(ghost ac));
  }
}

void initb(struct B *b)
  _(writes \extent(b))
  _(ensures \wrapped(b))
{
  b->a.x = 7;
  _(wrap &b->a)
  init(&b->rc _(ghost &b->a));
  _(wrap b)
}
/*{enduse}*/
/*`
Verification of RefCnt#adm succeeded.
Verification of B#adm succeeded.
Verification of init succeeded.
Verification of try_incr succeeded.
Verification of decr succeeded.
Verification of useb succeeded.
Verification of initb succeeded.
`*/
