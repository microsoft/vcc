#include <vcc.h>

int min(int a, int b)
{
  return a < b ? a : b;
}

#define LIMIT 1000
int main()
{
  int position = 0, newPos;
  // ...
  position = min(newPos, LIMIT);
  _(assert position <= LIMIT)
  // ...
  return 0;
}
/*`
Verification of min succeeded.
Verification of main failed.
testcase(14,12) : error VC9500: Assertion 'position <= 1000' did not verify.
`*/
