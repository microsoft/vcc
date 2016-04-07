/*{begin}*/
#include <vcc.h>

int min(int a, int b)
{
  if (a <= b)
    return a;
  else return b;
}

int main()
{
  int x, y, z;
  z = min(x, y);
  _(assert z <= x)
  return 0;
}
/*`
Verification of min succeeded.
Verification of main failed.
testcase(15,12) : error VC9500: Assertion 'z <= x' did not verify.
`*/
