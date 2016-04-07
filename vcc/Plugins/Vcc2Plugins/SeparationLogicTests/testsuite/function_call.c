#include "vcc2.h"

int f1() 
ensures (result==1)
{
  int ret = 1;
  return ret;
}

int f2() 
ensures (result==1)
{
  int ret = f1();
  return ret;
}
/*
#ifdef VERIFY
bool g()
ensures (result==true)
{
  int v1 = f1();
  int v2 = f2();
  return v1 == v2;
}

bool h()
ensures (result!=false)
{
  int v1 = f1();
  int v2 = f2();
  return v1 == v2;
}
#endif
*/
int assoc() 
ensures (result==3)
{
  int x = 1;
  int y = 2;
  return x+y;
}

int g()
ensures (exists(int x; result==1+x))
{
  int v1 = f1();
  int v2 = f2();
  int v3 = v1 + v2;
  return v3;
}

int h()
ensures (result!=0)
{
  int v1 = f1();
  int v2 = f2();
  return v1 == v2;
}

/*
  Call to z3 does not type check.
void disjunction(int x)
 ensures ( x == 3 || x == 4)
{
  x=4;
  return;
}
*/