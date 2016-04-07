#include "vcc2.h"

int blob(char*, void*, int);
int value_A(int);
int value_B(int, int);

struct A {
    int x;
};

struct B {
	struct A* a;
    int y;
};

void zot(int* p)
requires (exists(int x; blob("Int32",p,x)))
ensures (exists(int x; blob("Int32",p,0)))
{
  *p = 0;
  return;
}

void bar(struct A* a)
requires (exists(int x; blob("struct A",a,value_A(x))))
ensures (exists(int x; blob("Int32",a,0)))
{
  int* p;
  p = &a->x;
  zot(p);
  return;
}

void foo(struct B* b)
requires (exists(int y; int x; struct A* a; blob("struct B",b,value_B(a, y)) && blob("struct A",a,value_A(x))))
ensures (exists(int y; int x; struct A* a; blob("struct B",b,value_B(a, y)) && blob("struct A",a,value_A(0))))
{
  struct A* a = b->a;
  bar(a);
  return;
}
