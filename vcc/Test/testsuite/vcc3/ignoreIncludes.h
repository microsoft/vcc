#include <vcc.h>

struct S {
  int a;
  _(invariant a > 0)
};

void bar() { }
