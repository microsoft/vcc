/*{begin}*/
#include <vcc.h>
#include <limits.h>

unsigned lsearch(int elt, int *ar, unsigned sz)
  _(requires \thread_local_array(ar, sz))
  _(ensures \result != UINT_MAX ==> ar[\result] == elt)
{
  unsigned i;
  for (i = 0; i < sz; i++)
  {
    if (ar[i] == elt) return i;
  }

  return UINT_MAX;
}
/*`
Verification of lsearch succeeded.
`*/
