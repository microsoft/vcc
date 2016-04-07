#include "vcc2.h"

void constants_addition() {
    assert (1+1==2);
}

void variables_addition() {
    int x = 1;
    int y = 1;
    int z = 2;
	int w = x+y;
    assert (w==z);
}

void variables_addition2() {
    int x = 1;
    int y = 1;
    int z = 2;
    assert (x+y==z);
}
/*
void test_exists() 
    ensures(exists(int x; x+2==5))
{
	return;
}
*/
void test_exists2(int x) 
    ensures((x+2==5) || (x+2!=5))
{
	return;
}
