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
_(ghost struct Token {
  int dummy;
})
_(ghost _(claimable) struct Counter {
  int dummy;
})
/*{refcnt}*/
_(volatile_owns)
struct RwLock {
  volatile unsigned cnt;
  _(ghost \object resource)
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, (&claim_counter)->\claim_count == 0))

  _(ghost struct Token token)
  _(ghost struct Counter claim_counter)
  _(invariant resource != &claim_counter)
  _(invariant resource != &token)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> \mine(resource))
  _(invariant \mine(&token) || \mine(resource))
};
/*{init}*/
void init(struct RwLock *r _(ghost \object rsc))
  _(writes \extent(r), rsc)
  _(requires \wrapped(rsc))
  _(ensures \wrapped(r) && r->resource == rsc)
{
  r->cnt = 0;
  _(ghost r->resource = rsc)
  _(wrap &r->token)
  _(wrap &r->claim_counter)
  _(ghost r->\owns = { &r->token, rsc, &r->claim_counter })
  _(wrap r)
}
/*{incr}*/
void acquire_read(struct RwLock *r _(ghost \claim c)
             _(out \claim ret))
  _(always c, r->\closed)
  _(ensures \claims_object(ret, &r->claim_counter) && \claims(ret, r->resource->\closed) && \wrapped0(ret) && \fresh(ret))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(assume v <= UINT_MAX - 2)
    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v + 2, v);
      _(ghost
        if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0 && r->resource->\closed))
       // if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0))
    }

    if (v == n) return;
  }
}
/*{decr}*/
void release_read(struct RwLock *r _(ghost \claim c) _(ghost \claim handle))
  _(always c, r->\closed)
  _(requires \claims_object(handle, &r->claim_counter) && \wrapped0(handle))
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
          \destroy_claim(handle, {&r->claim_counter});
        })
    }

    if (v == n) break;
  }
}
void acquire_write(struct RwLock *r _(ghost \claim c))
  _(always c, r->\closed)
  _(ensures \wrapped(r->resource) && \fresh(r->resource))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v|1, v);
      _(ghost
        if (v == n) {
          r->\owns -= &r->token;
        })
    }

    if (v == n) break;
  }

  for (;;)
    _(invariant \wrapped(&r->token))
    _(writes &r->token)
  {
    _(atomic c, r) {
      v = r->cnt;
      _(ghost
        if (v == 1) {
          r->\owns += &r->token;
          r->\owns -= r->resource;
        })
    }
    if (v == 1) break;
  }
}
void release_write(struct RwLock *r _(ghost \claim c))
  _(always c, r->\closed)
  _(requires c != r->resource)
  _(requires \wrapped(r->resource))
  _(writes r->resource)
{
  _(atomic c, r) {
    r->cnt = 0;
    _(ghost r->\owns += r->resource)
  }
}

/*{use}*/
struct A {
  volatile int x;
};

struct B {
  struct RwLock rc;
  struct A a;
  _(invariant \mine(&rc))
  _(invariant rc.resource == &a)
};

void useb(struct B *b _(ghost \claim c))
  _(always c, b->\closed)
{
  _(ghost \claim ac)
  acquire_read(&b->rc _(ghost c) _(out ac));
    _(atomic &b->a, ac) {
      b->a.x = 10;
    }
  release_read(&b->rc _(ghost c) _(ghost ac));
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
Verification of RwLock#adm succeeded.
Verification of B#adm succeeded.
Verification of init succeeded.
Verification of acquire_read succeeded.
Verification of release_read succeeded.
Verification of acquire_write succeeded.
Verification of release_write succeeded.
Verification of useb succeeded.
Verification of initb succeeded.
`*/
