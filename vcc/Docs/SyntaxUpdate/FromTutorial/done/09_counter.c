#include <vcc.h>

/*{counter}*/
_(claimable) struct Counter {
  volatile unsigned v;
  _(invariant v > 0)
  _(invariant v == \old(v) || v == \old(v) + 1)
};
/*{reading}*/
struct Reading {
  struct Counter *n;
  volatile unsigned r;
  _(ghost \claim c;)
  _(invariant \mine(c) && \claims_object(c, n))
  _(invariant n->v >= r)
};
/*{endreading}*/
void create_reading(struct Counter *n _(ghost \claim c))
  _(requires \wrapped(c) && \claims_object(c, n))
  _(writes c)
{
  struct Reading k;
  k.r = 0;
  k.n = n;
  _(ghost k.c = c;)
  _(wrap &k)
  _(unwrap &k)
}

/*{readtwice}*/
void readtwice(struct Counter *n)
  _(requires \wrapped(n))
  _(writes n)
{
  unsigned int x, y;
  _(ghost \claim r;)

  _(atomic n) {
    x = n->v;
    _(ghost  r = \make_claim({n}, x <= n->v);)
  }

  _(atomic n) {
    y = n->v;
    _(assert \active_claim(r))
    _(assert x <= y)
  }
}
/*{endreadtwice}*/

/*`

Verification of Counter#adm succeeded.
Verification of Reading#adm succeeded.
Verification of create_reading succeeded.
Verification of readtwice succeeded.
`*/
