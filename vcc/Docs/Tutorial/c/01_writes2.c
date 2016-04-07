#include <vcc.h>

void boundedIncr(int *p)
{
  if (*p < 100)
    (*p)++;
}

/*{out}*/
/*`
Verification of boundedIncr failed.
testcase(5,8) : error VC8512: Assertion 'p is thread local' did not verify.
testcase(6,7) : error VC8507: Assertion 'p is writable' did not verify.
`*/
