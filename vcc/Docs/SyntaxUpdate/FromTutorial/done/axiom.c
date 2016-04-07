#include <vcc.h>

_(axiom 1 != 1)

void foo()
{
  _(assert \false)
}
/*`
Verification of foo succeeded.
`*/
