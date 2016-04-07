/*{begin}*/
#include <vcc.h>

void divide(unsigned x, 
            unsigned d, 
            unsigned *q, 
            unsigned *r)
  _(writes q,r)
{
  // assume the precondition
  _(assume d > 0 && q != r)
  unsigned lq = 0;
  unsigned lr = x;

  // check that the invariant holds on loop entry
  _(assert x == d*lq + lr)

  // start an arbitrary iteration
  // forget variables modified in the loop
  {
    unsigned _fresh_lq, _fresh_lr;
    lq = _fresh_lq; lr = _fresh_lr;
  }
  // assume that the loop invariant holds
  _(assume x == d*lq + lr)
  // jump out if the loop terminated
  if (!(lr >= d))
    goto loopExit;
  // body of the loop
  {
    lq++;
    lr -= d;
  }
  // check that the loop preserves the invariant
  _(assert x == d*lq + lr)
  // end of the loop
  _(assume \false)

  loopExit:
  *q = lq;
  *r = lr;
  // assert postcondition
  _(assert x == d*(*q) + *r && *r < d)
}
/*{end}*/
/*`
Verification of divide succeeded.
`*/
