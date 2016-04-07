#include <limits.h>
#include <vcc.h>

unsigned binary_search(int val, int *buf, unsigned len)
  _(requires \thread_local_array(buf, len))                   // buf[0..len] is valid, locally owned
  _(requires \forall unsigned i, j; i < j && j < len ==> buf[i] <= buf[j])         // buffer sorted
  _(ensures \result != UINT_MAX ==> buf[\result] == val)                           // val found
  _(ensures \result == UINT_MAX ==> \forall unsigned i; i < len ==> buf[i] != val) // val not found
  _(decreases 0)
{
  unsigned low, high, mid;
  low = 0; high = len;
  while (low < high)
    _(invariant high <= len)
    _(invariant \forall unsigned i; i < low              ==> buf[i] <  val) // val isn't to the left of low
    _(invariant \forall unsigned i; high <= i && i < len ==> buf[i] >= val) // val isn't to the right of high
  {
    mid = low + (high - low) / 2;
    if (buf[mid] < val)             low = mid + 1;
    else                            high = mid;
  }

  if (low < len && buf[low] == val) return low;
  else                              return UINT_MAX;
}

/*`
Verification of binary_search succeeded.
`*/
