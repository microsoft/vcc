#include <vcc.h>
#include <stdlib.h>

_(claimable) struct A {
  volatile int x;
  _(invariant \unchanged(x) || \old(x) + 1 == x)
};

void incr(struct A *a, int *res _(ghost \claim c) _(out \claim cres))
  _(writes c, res)
  _(always c, a->\closed)
  // there will be a single new child to c
  _(ensures c->\claim_count == \old(c->\claim_count) + 1)
  // the claim we return will be child of c
  _(ensures \claims_object(cres, c))
  // it will be wrapped without any references
  _(ensures \wrapped0(cres))
  // and it will guarantee a condition about a->x
  _(ensures \claims(cres, a->x >= \when_claimed(*res)))
  // and it was not allocated before
  _(ensures \fresh(cres))
  // we don't free the result parameter
  _(ensures \mutable(res))
{
  int val;

  _(atomic c,a) {
    val = a->x;
  }
  
  *res = val;
   _(ghost cres = \make_claim({c}, \when_claimed(*res) <= a->x);) 
}

void use_case()
{
  struct A *a;
  int tmp;
   _(ghost \claim c;) 
   _(ghost \claim c2;) 

  a = malloc(sizeof(*a));
  _(assume a != NULL)
  a->x = 0;
  _(wrap a)

   _(ghost c = \make_claim({a}, \true);) 
  incr(a, &tmp _(ghost c) _(out c2) );
  _(assert \wrapped(c))
 
  _(assert \active_claim(c2))
  _(assert tmp <= a->x)

  _(assert \wrapped(c))

  _(ghost \destroy_claim(c2, {c}));
  _(ghost \destroy_claim(c, {a}));
  _(unwrap a)
  free(a);
}

/*`
Verification of A#adm succeeded.
Verification of incr succeeded.
Verification of use_case succeeded.
`*/
