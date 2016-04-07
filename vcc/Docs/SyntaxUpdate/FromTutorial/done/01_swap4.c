#include "01_swap.c"

/*{foo}*/
int x, y, z;

void foo()
  _(writes &y, &z)
  _(requires x == 1 && y == 2)
{
  z = 3;
  swap(&x, &y);
  _(assert x == 2 && y == 1 && z == 3)
}
/*{out}*/
/*`
Verification of swap succeeded.
Verification of foo failed.
testcase(11,3) : error VC8510: Assertion 'x is writable in call to swap(&x, &y)' did not verify.
`*/
