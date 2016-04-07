#include "vcc2.h"

int blob(char*, void*, int);
int value_A(int);
int value_S(int, int);
int value_Z(int, char);

struct A {
    int x;
};

int f(struct A* a)
requires (exists(int x; blob("struct A",a,value_A(x))))
ensures (result==0 && blob("struct A",a,value_A(0)))
{
  int v;
  a->x = 0;
  v = a->x;
  return v;
}

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
//  bar(x);
  p->a = 42;
  return;
}

/*
void zot (int* p) 
requires (exists (int x; blob("Int32", p, x)))
ensures (blob("Int32", p, 42))
{ 
  bar(p);
  return;
}
*/

union Z {
  int x;
  char c;
};

void foo_z (union Z* p) 
requires (exists(int x; char c; blob("struct Z", p, value_Z(x,c))))
ensures (exists(int x; blob("struct Z", p, value_Z(x,'a'))))
{
  p->c = 'a';
  return;
}
