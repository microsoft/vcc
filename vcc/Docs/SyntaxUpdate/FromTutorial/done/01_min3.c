/*{min}*/
#include <vcc.h>

int min(int a, int b)
  _(requires  \true)
  _(ensures  \result <= a && \result <= b)
{
  return a < b ? a : b;
}
// ... definition of main() unchanged ...
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
Verification of min succeeded.
Verification of main succeeded.
`*/
