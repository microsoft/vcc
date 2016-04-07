#include <vcc.h>
/*{beg}*/
void boundedIncr(int *p)
  _(writes p)
  _(ensures \old(*p) < 100 ==> *p == \old(*p) + 1)
{
  if (*p < 100)
    (*p)++;
}
/*{foo}*/
int x, y;

int foo()
  _(requires x == 12)
  _(writes &x, &y)
{
  y = 42;
  boundedIncr(&x);
  _(assert x == 13 && y == 42)
}
/*`
Verification of boundedIncr succeeded.
Verification of foo succeeded.
`*/
