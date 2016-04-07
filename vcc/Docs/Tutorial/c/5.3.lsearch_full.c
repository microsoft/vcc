/*{begin}*/
#include <vcc.h>
#include <limits.h>

unsigned lsearch(int elt, int *ar, unsigned sz)
  _(requires \thread_local_array(ar, sz))
  _(ensures \result != UINT_MAX 
     ==> ar[\result] == elt)
  _(ensures \forall unsigned i; 
    i < sz && i < \result ==> ar[i] != elt)
{
  unsigned i;
  for (i = 0; i < sz; i++)
    _(invariant \forall unsigned j; 
        j < i ==> ar[j] != elt)
  {
    if (ar[i] == elt) return i;
  }
  return UINT_MAX;
}
/*{end}*/
/*`
Verification of lsearch succeeded.
`*/
