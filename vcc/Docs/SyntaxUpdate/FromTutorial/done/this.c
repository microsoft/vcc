
#include <vcc.h>

struct S {
  int a;
  int b;
  _(invariant \this->a == \this->b)
};

void foo(struct S *s) { }
/*`
Verification of S#adm succeeded.
Verification of foo succeeded.
`*/
