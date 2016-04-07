#include <vcc.h>

void foo(_(out int o)) 
  _(ensures o == 5)
{
  _(ghost o = 5;)
}		

void bar() {
  _(ghost int p;)
  foo(_(out p));
  _(assert p == 5)
}
/*`
Verification of foo succeeded.
Verification of bar succeeded.
`*/
