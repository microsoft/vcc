#include <vcc.h>

typedef _(claimable) struct _A {
  volatile int f;
  _(invariant f == \old(f) || f == _(unchecked)(\old(f) + 2))
  // unchecked() used as work-around for issue 5883
} A;

int check_parity(A *a _(out \claim p))
  _(requires \wrapped(a))
  _(writes a)
  _(ensures \wrapped(a) && a->\claim_count == \old(a->\claim_count) + 1)
  _(ensures \wrapped(p) && \claims(p, (a->f & 1) == \result))
{
  int tmp;
  _(atomic a) {
    tmp = a->f;
    _(assert {:bv} \forall int x; (x&1) == ((x+2) & 1))
    _(ghost p = \make_claim({a}, (a->f & 1) == (tmp & 1)))
  }
  return (tmp & 1);
}

int check_parity_b(A *a _(ghost \claim c) _(out \claim p))
  _(requires \wrapped(c) && \claims(c, a->\closed))
  _(writes c)
  _(ensures \wrapped(c) && c->\claim_count == \old(c->\claim_count) + 1)
  _(ensures \wrapped(p) && \claims(p, (a->f & 1) == \result))
{
  int tmp;
  _(atomic a, c) {
    tmp = a->f;
    _(assert {:bv} \forall int x; (x&1) == ((x+2) & 1))
    _(ghost p = \make_claim({c}, (a->f & 1) == (tmp & 1)))
  }
  return (tmp & 1);
}

/*`
Verification of _A#adm succeeded.
Verification of check_parity succeeded.
Verification of check_parity_b succeeded.
Verification of check_parity#bv_lemma#0 succeeded.
Verification of check_parity_b#bv_lemma#0 succeeded.
`*/
