#include <vcc.h>

void foo() {
  _(ghost \objset o)
  _(ghost void *p)
  _(ghost void *q)
  _(assume p != q)
  _(ghost o = {p})
  _(assert p \in o)
  _(assert !(q \in o))
}
/*`
Verification of foo succeeded.
`*/
