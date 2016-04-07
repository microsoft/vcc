#include<vcc.h>
/*{begin}*/
void memcpyandclr(unsigned char *dst, 
                  unsigned char *src, 
                  unsigned len)
  _(writes \array_range(src, len))
  _(writes \array_range(dst, len))
  _(requires \arrays_disjoint(src, len, dst, len))
  _(ensures \forall unsigned i; i < len 
      ==> dst[i] == \old(src[i]))
  _(ensures \forall unsigned i; i < len 
      ==> src[i] == 0)
  _(decreases 0)
{
  unsigned k;
  for (k = 0; k < len; ++k)
    _(writes \array_range(dst, len))
    _(invariant \forall unsigned i; i < k 
        ==> dst[i] == \old(src[i]))
  {
    dst[k] = src[k];
  }
  for (k = 0; k < len; ++k)
    _(writes \array_range(src, len))
    _(invariant \forall unsigned i; i < k 
        ==> src[i] == 0)
  {
    src[k] = 0;
  }
}
/*{end}*/
/*`
Verification of memcpyandclr succeeded.
`*/
