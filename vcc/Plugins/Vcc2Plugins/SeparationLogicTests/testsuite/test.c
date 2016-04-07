#include "vcc2.h"

int blob(char*, void*, int);

int value_S(int, int);

struct S {
    int a;
    int b;
};

void foo (struct S* p)
requires(exists(int x; int y; blob("struct S", p, value_S(x,y))))
ensures (blob("struct S", p, value_S(42,28)))
{
  p->a = 42;
  p->b = 28;
  return;
}

/*
struct A {
int x;
};

struct B {
struct A a;
int y;
};

int f(struct B b) {
  struct B* pb;
  int* t;
  pb = &b;
  pb->a.x = 1;
  *(&(b.a.x)) = 2;
  b.y = pb->a.x;
  return b.y;
}
*/
/*
struct S {
    int a;
    int b;
};

void bar (int* p)
requires (typed(p) && thread_local(p))
writes(p)
ensures (*p == 42)
{
  *p = 42;
  return;
}

void zot (struct S* p) 
requires (typed(p) && thread_local(p))
writes(p)
ensures (p->a == 42)
{
  bar((int*)p);
  return;
}
*/

