#include <vcc.h>
#include <limits.h>

#define SET(n, i) (!!(((n) >> (i)) & 1))
#define FB(x) _(unchecked)((x) & (unsigned)-(x))
#define INT int

#define MAX_BIT 32

_(typedef \bool intset[\integer])
_(def \bool validBits(intset s)
{
  return \forall \integer i; s[i] ==> i >= 0 && i < MAX_BIT;
})

_(def intset bits(unsigned n)
   _(ensures validBits(\result))
{
  return \lambda \integer i; i >= 32 || i < 0 ? \false : SET(n, i); 
})

_(def intset singleton(\integer i) { return \lambda \integer j; i == j; })
_(def intset empty() { return \lambda \integer j; \false; })

_(abstract \integer min_elt_rec(intset s, \integer p)
    _(decreases MAX_BIT - p)
    _(requires \forall \integer i; i < p ==> !s[i])
    _(requires p >= 0 && validBits(s))
    _(ensures s != empty() ==> s[\result])
    _(ensures \forall \integer i; s[i] ==> i >= \result)
    _(ensures \result >= 0)
{
  if (s[p]) return p;
  else if (p >= MAX_BIT) return 0;
  else return min_elt_rec(s, p + 1);
})

_(def \integer min_elt(intset s) 
   _(requires validBits(s))
{
  return min_elt_rec(s, 0); 
})

#define ONE_SET(n) \
  SET(n, 0) || SET(n, 1) || SET(n, 2) || SET(n, 3) || SET(n, 4) || SET(n, 5) || SET(n, 6) || SET(n, 7) || \
  SET(n, 8) || SET(n, 9) || SET(n, 10) || SET(n, 11) || SET(n, 12) || SET(n, 13) || SET(n, 14) || SET(n, 15) || \
  SET(n, 16) || SET(n, 17) || SET(n, 18) || SET(n, 19) || SET(n, 20) || SET(n, 21) || SET(n, 22) || SET(n, 23) || \
  SET(n, 24) || SET(n, 25) || SET(n, 26) || SET(n, 27) || SET(n, 28) || SET(n, 29) || SET(n, 30) || SET(n, 31)

_(abstract \bool lemma_first_bit(unsigned x)
   _(ensures x != 0 ==> bits(FB(x)) == singleton(min_elt(bits(x))))
   _(ensures \result)
{
  _(ghost \bool b = bits(FB(x)) == singleton(min_elt(bits(x))))
  _(assert {:bv} \forall unsigned x, i; SET(FB(x), i) ==> SET(x, i))
  _(assert {:bv} \forall unsigned x, i, j; SET(x, i) && SET(FB(x), j) ==> i >= j)
  _(assert {:bv} \forall unsigned x; {bits(x)} x != 0 ==> ONE_SET(x))
  _(assert {:bv} \forall unsigned x; {bits(x)} x != 0 ==> ONE_SET(FB(x)))
  _(assert \forall unsigned i; {x >> i} i < 32 ==> (SET(x,i) <==> bits(x)[i]))
  return \true;
})

_(abstract \bool lemma_sum(unsigned x, unsigned y)
   _(ensures bits(x|y) == \lambda \integer i; bits(x)[i] || bits(y)[i])
   _(ensures \result)
{
  _(assert {:bv} \forall unsigned x, y, i; SET(x|y, i) <==> SET(x, i) || SET(y, i))
  return \true;
})

_(abstract \bool lemma_sub(unsigned x, unsigned y)
   _(ensures bits(x&~y) == \lambda \integer i; bits(x)[i] && !bits(y)[i])
   _(ensures \result)
{
  _(assert {:bv} \forall unsigned x, y, i; SET(x&~y, i) <==> SET(x, i) && !SET(y, i))
  return \true;
})

_(def \bool mark2(unsigned x, \integer y) { return \true; })

_(abstract \bool lemma_succ(unsigned x)
   _(ensures bits(_(unchecked)(x * 2)) == \lambda \integer i; i < 32 && i != 0 && bits(x)[i-1])
   _(ensures \result)
{
  _(assert {:bv} \forall unsigned x, i; {mark2(x, i)} SET(x * 2, i) <==> i < 32 && i != 0 && SET(x, i - 1))
  _(assert \forall \integer i; {:hint mark2(x,i)} bits(_(unchecked)(x * 2))[i] <==> i < 32 && i != 0 && bits(x)[i-1])
  return \true;
})

_(abstract \bool lemma_pred(unsigned x)
   _(ensures bits(_(unchecked)(x / 2)) == \lambda \integer i; i >= 0 && bits(x)[i+1])
   _(ensures \result)
{
  _(assert {:bv} \forall unsigned x, i; {mark2(x, i)} i < 132 ==> (SET(x / 2, i) <==> SET(x, i + 1)))
  _(assert \forall \integer i; {:hint mark2(x,i)} bits(_(unchecked)(x / 2))[i] <==> i >= 0 && bits(x)[i+1])
  return \true;
})

/*`
testcase(54,55) : warning VC9326: [possible unsoundness]: signed overflow (of '-') has undefined behavior in C
Verification of validBits succeeded.
Verification of bits succeeded.
Verification of singleton succeeded.
Verification of empty succeeded.
Verification of min_elt_rec succeeded.
Verification of min_elt succeeded.
Verification of lemma_first_bit succeeded.
Verification of lemma_sum succeeded.
Verification of lemma_sub succeeded.
Verification of mark2 succeeded.
Verification of lemma_succ succeeded.
Verification of lemma_pred succeeded.
Verification of lemma_first_bit#bv_lemma#0 succeeded.
Verification of lemma_first_bit#bv_lemma#1 succeeded.
Verification of lemma_first_bit#bv_lemma#2 succeeded.
Verification of lemma_first_bit#bv_lemma#3 succeeded.
Verification of lemma_pred#bv_lemma#0 succeeded.
Verification of lemma_sub#bv_lemma#0 succeeded.
Verification of lemma_succ#bv_lemma#0 succeeded.
Verification of lemma_sum#bv_lemma#0 succeeded.
`*/
