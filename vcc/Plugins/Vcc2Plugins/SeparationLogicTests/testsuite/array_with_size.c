#include "vcc2.h"

int blob(char*, void*, int);

int value_Int32_2(int,int);
int value_Int32_3(int,int,int);


void f2(int* a) 
requires (exists(int a0; int a1; blob("Int32[2]",a,value_Int32_2(a0,a1))))
ensures (exists(int a0; blob("Int32[2]",a,value_Int32_2(a0,5))))
{
  a[1] = 5;
  return;
}


void f3(int* a) 
requires (exists(int a0; int a1; int a2; blob("Int32[3]",a,value_Int32_3(a0,a1,a2))))
ensures (exists(int a0; int a2; blob("Int32[3]",a,value_Int32_3(a0,5,a2))))
{
  a[1] = 5;
  return;
}
