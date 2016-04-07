#include "vcc.h"
#include <limits.h>

unsigned lsearch(int elt, int *ar, unsigned sz)
  _(requires  \wrapped((int[sz])(ar)))
  _(ensures \result != UINT_MAX ==> ar[\result] == elt)
  _(ensures \result == UINT_MAX ==> 
            \forall unsigned i; i < sz ==> ar[i] != elt)
{
  unsigned i;
  for (i = 0; i < sz; i++)
    _(invariant \forall unsigned j; j < i ==> ar[j] != elt)
  {
    if (ar[i] == elt) return i;
  }

  return UINT_MAX;
}
/*`
Verification of lsearch succeeded.
`*/
