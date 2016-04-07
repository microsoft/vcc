#include "vcc2.h"

int f() 
ensures (result == 0)
{
  int x;
  x = 0;
  return x;
}
