#include "vcc2.h"

int blob(char*, void*, int);
int value_A(int);
int value_B(int, int);

struct A {
    int x;
};

struct B {
	struct A a;
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

void foo1(struct B* b)
requires (exists(int y; int x; blob("struct B",b,value_B(value_A(x), y))))
ensures (exists(int y; int x; blob("struct B",b,value_B(value_A(0), y))))
{
  struct A* a;
  a = &b->a;
  bar(a);
  return;
}

void foo2(struct B* b)
requires (exists(int y; int x; blob("struct B",b,value_B(value_A(x), y))))
ensures (exists(int y; int x; blob("struct B",b,value_B(value_A(0), y))))
{
  struct A* a;
  a = &b->a;
  b->a.x = 0;
  return;
}
