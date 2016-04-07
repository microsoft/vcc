/*{min}*/
#include <vcc.h>

int min(int a, int b)
  _(requires \true)
  _(ensures \result <= a && \result <= b)
{
  if (a <= b)
    return a;
  else return b;
}
// ... definition of main() unchanged ...
/*{endmin}*/
int main()
{
  int x, y, z;
  z = min(x, y);
  _(assert z <= x)
  return 0;
}
/*{out}*/
/*`
Verification of min succeeded.
Verification of main succeeded.
`*/
