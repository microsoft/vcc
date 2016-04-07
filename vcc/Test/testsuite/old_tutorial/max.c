#include "vcc.h"

_(pure) int max(int a, int b)
  _(ensures \result == (a > b ? a : b))
{
  if (a > b) return a;
  return b;
}

int max4(int a, int b, int c, int d)
  _(ensures \result == max(max(a,b), max(c,d)))
{
  if (a > b)
    if (a > c)
      if (a > d) return a;
      else return d;
    else
      if (c > d) return c;
      else return d;
  else
    if (b > c)
      if (b > d) return b;
      else return d;
    else
      if (c > d) return c;
      else return d;
}

/*`
Verification of max succeeded.
Verification of max4 succeeded.
`*/
