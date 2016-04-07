#include <vcc.h>

/*{min}*/
int min(int a, int b)
  _(requires  \true)
  _(ensures  \result <= a && \result <= b)
{
  return a > b ? a : b;
}
/*{endmin}*/
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
/*{out}*/
/*`
Verification of min failed.
testcase(8,3) : error VC9501: Post condition '\result <= a && \result <= b' did not verify.
testcase(6,14) : error VC9599: (related information) Location of post condition.
Verification of main succeeded.
`*/
