#include <vcc.h>

/*{swap}*/
void swap(int *p, int *q)
  _(ensures *p == \old(*q) && *q == \old(*p))
{
  int tmp;
  tmp = *p;
  *p = *q;
  *q = tmp;
}
/*{out}*/
/*`
Verification of swap failed.
testcase(8,10) : error VC8512: Assertion 'p is thread local' did not verify.
testcase(9,4) : error VC8507: Assertion 'p is writable' did not verify.
testcase(9,9) : error VC8512: Assertion 'q is thread local' did not verify.
testcase(10,4) : error VC8507: Assertion 'q is writable' did not verify.
`*/
