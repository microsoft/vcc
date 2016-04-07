
#include <vcc.h>

int foo(int *i)
  _(requires i->\valid)
  _(requires \thread_local(i))
  _(ensures \result == \old(*i))
{
  return *i;
}
/*`
Verification of foo succeeded.
`*/
