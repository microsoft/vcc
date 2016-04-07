#include "vcc2.h"

int blob(char*, void*, int);
int value_S(int, int);

struct S {
    int a;
    int b;
};

void bar (int* p)
requires (exists (int x; blob("Int32", p, x)))
ensures (blob("Int32", p, 42))
{
  *p = 42;
  return;
}

void zot (struct S* p) 
requires (exists(int x; int y; blob("struct S", p, value_S(x,y))))
ensures (exists(int y; blob("struct S", p, value_S(42,y))))
{
  int* x = (int*) p;
  bar(x);
  return;
}
