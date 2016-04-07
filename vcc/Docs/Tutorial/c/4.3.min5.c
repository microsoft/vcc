/*{begin}*/
#include <vcc.h>

int min(int a, int b)
  _(requires \true)
  _(ensures \result <= a && \result <= b)
{
  _(assert {:bv} \forall int x; (x & (-1)) == x)
  _(assert {:bv} \forall int a,b; (a - (a - b)) == b)
  return _(unchecked)(a - ((a - b) & -(a > b)));
}
/*`
testcase(10,23) : warning VC9326: [possible unsoundness]: signed overflow (of '-') has undefined behavior in C
testcase(10,29) : warning VC9326: [possible unsoundness]: signed overflow (of '-') has undefined behavior in C
testcase(10,38) : warning VC9326: [possible unsoundness]: signed overflow (of '-') has undefined behavior in C
Verification of min succeeded.
Verification of min#bv_lemma#0 succeeded.
Verification of min#bv_lemma#1 succeeded.
`*/
