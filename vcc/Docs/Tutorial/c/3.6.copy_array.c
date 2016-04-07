#include<vcc.h>
/*{begin}*/
void my_memcpy(unsigned char *dst, 
               unsigned char *src, 
               unsigned len)
  _(writes \array_range(dst, len))
  _(requires \thread_local_array(src, len))
  _(requires \arrays_disjoint(src, len, dst, len))
  _(ensures \forall unsigned i; i < len 
      ==> dst[i] == \old(src[i]))
{
  if (len > 0) {
    dst[len - 1] = src[len - 1];
    my_memcpy(dst, src, len - 1);
  }
}
/*{end}*/
/*`
Verification of my_memcpy succeeded.
`*/
