#include "vcc.h"
#include <limits.h>

int lsearch(int elt, int *ar, unsigned sz)
  _(requires 0 <= sz)
  _(requires sz < INT_MAX / sizeof(int))
  _(requires \wrapped((int[sz])(ar)))
  _(ensures \result >= 0 ==> ar[\result] == elt)
  _(ensures \result < 0 ==> \forall int i; 0 <= i && i < (int) sz ==> ar[i] != elt)
{
  int i;
  for (i = 0; i < (int) sz; i++)
    _(invariant 0 <= i && i <= (int) sz)
    _(invariant \forall int j; 0 <= j && j < i ==> ar[j] != elt)
  {
    if (ar[i] == elt) return i;
  }

  return -1;
}

/*`
Verification of lsearch succeeded.
`*/
