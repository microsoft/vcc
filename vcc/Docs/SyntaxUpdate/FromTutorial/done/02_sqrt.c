#include <vcc.h>

unsigned isqrt(unsigned x)
  _(requires  x < 0xfffe0001)
  _(ensures  \result*\result <= x && x < (\result+1)*(\result+1))
{
  unsigned r = 0;
  while ((r+1)*(r+1) <= x)
    _(invariant  r*r <= x)
  {
    r++;
  }
  return r;
}
/*`
Verification of isqrt succeeded.
`*/
