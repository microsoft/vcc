#include "vcc.h"
#include <limits.h>

int succ(int i)
  _(ensures \result == i + 1)
{
  return i + 1;
}

int succ_INT_MAX(int i)
  _(requires i < INT_MAX)
  _(ensures \result == i + 1)
{
  return i+1;
}

int succ_unchecked(int i)
  _(ensures \result == _(unchecked) (i + 1))
{
  return _(unchecked) (i + 1);
}

/*`
testcase(20,24) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
Verification of succ failed.
testcase(7,10) : error VC8004: i + 1 might overflow.
Verification of succ_INT_MAX succeeded.
Verification of succ_unchecked succeeded.
`*/
