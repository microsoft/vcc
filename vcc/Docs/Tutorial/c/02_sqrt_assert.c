#include <vcc.h>

unsigned anything()
  _(reads \universe());

void isqrt(unsigned x)
  _(requires x < 0xfffe0001)
{
  unsigned r = 0, s;

  _(assert r*r <= x) // invariant initially holds
  r = anything();
  _(assume r*r <= x)
  if ((r+1)*(r+1) <= x) {
    r++;
    _(assert r*r <= x)
    _(assume \false)
  }
  _(assert r*r <= x && x < (r+1)*(r+1))
}
/*`
Verification of isqrt succeeded.
`*/
