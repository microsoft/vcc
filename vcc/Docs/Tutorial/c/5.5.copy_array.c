#include<vcc.h>
/*{begin}*/
void my_memcpy(unsigned char *dst, 
               unsigned char *src, 
               unsigned len)
  _(writes \array_range(dst, len))
  _(requires \thread_local_array(src, len))
  _(requires \arrays_disjoint(src, len, dst, len))
  _(ensures \forall unsigned i; i < len ==> 
       dst[i] == \old(src[i]))
  _(decreases 0)
{
  unsigned k;
  for (k = 0; k < len; ++k)
    _(invariant \forall unsigned i; i < k ==> 
        dst[i] == \old(src[i]))
  {
    dst[k] = src[k];
  }
}
/*{end}*/
/*`
Verification of my_memcpy succeeded.
`*/
