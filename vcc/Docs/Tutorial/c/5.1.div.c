/*{begin}*/
#include <vcc.h>

void divide(unsigned x, 
            unsigned d, 
            unsigned *q, 
            unsigned *r)
_(requires d > 0 && q != r)
_(writes q,r)
_(ensures x == d*(*q) + *r && *r < d)
{
  unsigned lq = 0;
  unsigned lr = x;
  while (lr >= d)
  _(invariant x == d*lq + lr)
  {
    lq++;
    lr -= d;
  }
  *q = lq;
  *r = lr;
}
/*{end}*/
/*`
Verification of divide succeeded.
`*/
