#include <vcc.h>

/*{begin}*/
void write(int *p)
  _(writes p)
{ *p = 42; }

void write_wrong(int *p)
  _(requires \mutable(p))
{ *p = 42; }

int read1(int *p)
  _(requires \thread_local(p))
{ return *p; }

int read2(int *p)
  _(requires \mutable(p))
{ return *p; }

int read_wrong(int *p)
{ return *p; }

void test_them()
{
  int a = 3, b = 7;
  read1(&a);
  _(assert a == 3 && b == 7) // OK
  read2(&a);
  _(assert a == 3 && b == 7) // OK
  write(&a);
  _(assert b == 7) // OK
  _(assert a == 3) // error
}
/*`
Verification of write succeeded.
Verification of write_wrong failed.
testcase(10,4) : error VC8507: Assertion 'p is writable' did not verify.
Verification of read1 succeeded.
Verification of read2 succeeded.
Verification of read_wrong failed.
testcase(21,11) : error VC8512: Assertion 'p is thread local' did not verify.
Verification of test_them failed.
testcase(32,12) : error VC9500: Assertion 'a == 3' did not verify.
`*/
