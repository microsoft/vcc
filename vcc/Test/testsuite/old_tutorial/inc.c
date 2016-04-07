#include "vcc.h"
#include <limits.h>

void increment(int *x)
  _(requires \mutable(x))
  _(requires *x < INT_MAX)
  _(writes x)
  _(ensures *x == \old(*x) + 1)
{
  *x = *x + 1;
}

/*`
Verification of increment succeeded.
`*/
