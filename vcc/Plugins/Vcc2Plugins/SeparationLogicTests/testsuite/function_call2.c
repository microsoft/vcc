#include "vcc2.h"

int blob(char*, void*, int);
int value_S(int, int);

struct S {
    int a;
    int b;
};

void foo (struct S* p)
requires (exists (int x; int y; blob("struct S", p, value_S(x,y))))
ensures (blob("struct S", p, value_S(42,28)))
{
  p->a = 42;
  p->b = 28;
  return;
}

void bar (struct S* p, struct S* q)
requires (blob("struct S", p, value_S(1,0)) && blob("struct S", q, value_S(0,1)))
ensures (blob("struct S", p, value_S(42,28)) && blob("struct S", q, value_S(0,1)))
{
  foo(p);
  return;
}

int value_T(int);

struct T {
    int a;
};

void zot (struct T* p)
//requires (exists (int x; blob("struct T", p, value_T(x))))
requires (exists (int x; blob("Int32", p, x)))
// ensures (blob("struct T", p, value_T(42)))
ensures (blob("Int32", p, 42))
{
  p->a = 42;
  return;
}
