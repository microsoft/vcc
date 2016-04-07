#include <vcc.h>

void foo () {
  _(ghost \thread m = \me)
  _(assert m == \me)
  _(assert \ghost(m))
}
/*`
Verification of foo succeeded.
`*/
