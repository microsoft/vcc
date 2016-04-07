#include <vcc.h>

void boundedIncr(int *p)
  _(writes p)
  _(ensures \old(*p) < 100 ==> *p == \old(*p) + 1);

int x, y;

/*{foo}*/
int foo()
  _(requires x == 12)
  _(writes &y)
{
  y = 42;
  boundedIncr(&x);
  _(assert x == 13 && y == 42)
}
/*{out}*/
/*`
Verification of foo failed.
testcase(15,3) : error VC8510: Assertion 'x is writable in call to boundedIncr(&x)' did not verify.
`*/
