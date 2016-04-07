#include "vcc2.h"

int blob(char*, int*, int);

int f(int * v) 
requires (exists(int x; blob("Int32",v,x)))
ensures (result==0 && exists(int x; blob("Int32",v,0)))
{
  *v = 0;
  return 0;
}
