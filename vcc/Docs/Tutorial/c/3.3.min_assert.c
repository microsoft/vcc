/*{begin}*/
#include <vcc.h>

int min(int a, int b)
{
  int \result;
  // assume precondition of min(a,b)
  _(assume \true)
  if (a <= b)
    \result = a;
  else \result = b;
  // assert postcondition of min(a,b)
  _(assert \result <= a && \result <= b)
}

int main()
{
  int \result;
  // assume precondition of main()
  _(assume \true)
  int x, y, z;
  // z = min(x,y);
  {
    int _res; // placeholder for the result of min()
    // assert precondition of min(x,y)
    _(assert \true)
    // assume postcondition of min(x,y)
    _(assume _res <= x && _res <= y)
    z = _res; // store the result of min()
  }
  _(assert z <= x)
  \result = 0;
  // assert postcondition of main()
  _(assert \true)
}
/*{end}*/
// Note: this above example is just meant to illustrate how VCC works; the
// expected output below does not mean much.
/*`
testcase(6,7) : error VC0000: Invalid expression term '\r'.
testcase(10,5) : error VC0000: Invalid expression term '\r'.
testcase(11,8) : error VC0000: Invalid expression term '\r'.
testcase(13,12) : error VC0000: Cannot use '\result' in this context.
testcase(13,28) : error VC0000: Cannot use '\result' in this context.
testcase(18,7) : error VC0000: Invalid expression term '\r'.
testcase(32,3) : error VC0000: Invalid expression term '\result'.
testcase(32,13) : warning VC9001: The expression '0' has no side effect; expected operation with side effect.
`*/
