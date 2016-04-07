#include <vcc.h>

int min(int a, int b)
  _(requires \true)
  _(ensures  \result <= a && \result <= b)
{
  _(assert {:bv} \forall int x; (x & (-1)) == x)
  _(assert {:bv} \forall int a,b; (a - (a - b)) == b)
  return _(unchecked)(a - ((a - b) & -(a > b)));
}
/*`
Verification of min succeeded.
Verification of min#bv_lemma#0 succeeded.
Verification of min#bv_lemma#1 succeeded.
`*/
