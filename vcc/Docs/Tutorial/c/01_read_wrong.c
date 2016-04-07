#include <vcc.h>

int read_pointer(int *p)
{
  return *p;
}
/*{begin}*/
/*`
Verification of read_pointer failed.
testcase(5,11) : error VC8512: Assertion 'p is thread local' did not verify.
`*/
