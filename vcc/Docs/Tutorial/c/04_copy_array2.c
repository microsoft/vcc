#include<vcc.h>
/*{begin}*/
void my_memcpy(unsigned char *dst, unsigned char *src, unsigned len)
  _(writes \array_range(dst, len))
  _(requires \thread_local_array(src, len))
  _(requires \arrays_disjoint(src, len, dst, len))
  _(ensures \forall unsigned i; i < len ==> dst[i] == \old(src[i]))
{
  unsigned k;
  for (k = 0; k < len; ++k)
    _(invariant \mutable_array(\old(dst), \old(len)))
    _(invariant \forall unsigned i; i < k ==> \old(dst)[i] == \old(src[i]))
    _(invariant dst == \old(dst) + k)
    _(invariant src == \old(src) + k)
  {
    *dst++ = *src++;
  }
}
/*{end}*/
/*`
testcase(11,43) : warning VC9106: '\old', '\at', or '\when_claimed' in '\old(len)' has no effect
Verification of my_memcpy succeeded.
`*/
