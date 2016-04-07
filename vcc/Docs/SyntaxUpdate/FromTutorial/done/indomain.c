
#include <vcc.h>

struct S { int a; _(invariant a > 0) };

_(dynamic_owns) struct T {
  int x;
  struct S *s;
  _(invariant x > 0 ==> s \in \this->\owns)
};

void foo(struct T *t)
  _(requires \wrapped(t) && t->x > 0)
  _(writes t)
{
  _(assert t->s \in \domain(t))
  _(unwrap t)
  _(assert t->s->a > 0)
  _(wrap t)
}
/*`
Verification of S#adm succeeded.
Verification of T#adm succeeded.
Verification of foo succeeded.
`*/
