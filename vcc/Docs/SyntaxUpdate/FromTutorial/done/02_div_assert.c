//` /b:/timeLimit:30
#include <vcc.h>
_(axiom \forall unsigned a,b; a > b && b != 0 ==> a % b == (a - b) % b)
_(axiom \forall unsigned a,b; a < b && b != 0 ==> a % b == a)

unsigned anything()
  _(reads \universe()); //--

unsigned mod(unsigned a, unsigned b)
{
  unsigned res = a;

  // check that invariant initially holds
  _(assert a % b == res % b)

  // start an arbitrary loop iteration
  res = anything();
  _(assume a % b == res % b) // assume the invariant
  if (res < b) goto theEnd;
  res -= b;
  _(assert a % b == res % b) // check the invariant
  _(assume \false) // end of an iteration

theEnd:
  ; // so that we no longer attempt to parser loop contracts
  _(assert res == a % b) // translation of ensures
  return res;
}
// TODO: timeout?
/*`
Verification of mod timeout.
`*/
