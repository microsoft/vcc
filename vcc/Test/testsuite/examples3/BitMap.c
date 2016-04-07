#include <vcc.h>

typedef unsigned __int64 UINT64;
typedef unsigned __int32 UINT32;

_(ghost typedef \bool BITMAP[UINT64])


_(ghost _(pure) BITMAP ToBm64(UINT64 n);) 



_(ghost _(pure) BITMAP ToBm32(UINT32 n);) 



_(ghost _(pure) BITMAP Bm64Singleton(UINT64 i) _(ensures \result == \lambda UINT64 j; (j == i));)



_(ghost _(pure) BITMAP Bm32Singleton(UINT64 i) _(ensures \result == \lambda UINT64 j; (j == i));)



_(ghost _(pure) BITMAP Bm64Union(BITMAP bm1, BITMAP bm2)  
  _(ensures \result == \lambda UINT64 i; i < 64 ==> (bm1[i] || bm2[i]));)



_(ghost _(pure) BITMAP Bm32Union(BITMAP bm1, BITMAP bm2)  
  _(ensures \result == \lambda UINT64 i; i < 32 ==> (bm1[i] || bm2[i]));)



_(ghost _(pure) BITMAP Bm64Intersect(BITMAP bm1, BITMAP bm2)
  _(ensures \result == \lambda UINT64 i; i < 64 ==> (bm1[i] && bm2[i]));)



_(ghost _(pure) BITMAP Bm32Intersect(BITMAP bm1, BITMAP bm2)
  _(ensures \result == \lambda UINT64 i; i < 32 ==> (bm1[i] && bm2[i]));)



_(ghost _(pure) BITMAP Bm64SymmetricDiff(BITMAP bm1, BITMAP bm2)
  _(ensures \result == \lambda UINT64 i; i < 64 ==> (!(bm1[i] <==> bm2[i])));)



_(ghost _(pure) BITMAP Bm32SymmetricDiff(BITMAP bm1, BITMAP bm2)
  _(ensures \result == \lambda UINT64 i; i < 32 ==> (!(bm1[i] <==> bm2[i])));)



_(ghost _(pure) \bool Bm64SpecialValue(UINT64 bm)
  _(ensures \result == \true);)



_(ghost _(pure) \bool Bm32SpecialValue(UINT32 bm)
  _(ensures \result == \true);)


_(axiom \forall UINT64 i; i < 64 ==> !ToBm64(0)[i])
_(axiom \forall UINT64 i; i < 64 ==> ToBm64((UINT64)-1)[i])
_(axiom \forall UINT64 i; { ToBm64(1UI64 << i) } i < 64 ==> ToBm64(1UI64 << i) == Bm64Singleton(i))
_(axiom \forall UINT64 x; {Bm64SpecialValue(x)} (\forall UINT64 i; i < 64 ==> !ToBm64(x)[i]) ==> x == 0)
_(axiom \forall UINT64 x; {Bm64SpecialValue(x)} (\forall UINT64 i; i < 64 ==> ToBm64(x)[i]) ==> x == (UINT64)-1)
_(axiom \forall UINT64 x,y; { ToBm64(x & y) } ToBm64(x & y) == Bm64Intersect(ToBm64(x), ToBm64(y)))
_(axiom \forall UINT64 x,y; { ToBm64(x | y) } ToBm64(x | y) == Bm64Union(ToBm64(x), ToBm64(y)))
_(axiom \forall UINT64 x,y; { ToBm64(x ^ y) } ToBm64(x ^ y) == Bm64SymmetricDiff(ToBm64(x), ToBm64(y)))
_(axiom \forall UINT64 x, i; i < 64 ==> ToBm64(x)[i] <==> (x & (1UI64 << i)) != 0)

_(axiom \forall UINT64 i; i < 32 ==> !ToBm32(0)[i])
_(axiom \forall UINT64 i; i < 32 ==> ToBm32((UINT32)-1)[i])
_(axiom \forall UINT64 i; { ToBm32(1UI32 << i) } i < 32 ==> ToBm32(1UI32 << i) == Bm32Singleton(i))
_(axiom \forall UINT32 x; {Bm32SpecialValue(x)} (\forall UINT32 i; i < 32 ==> !ToBm32(x)[i]) ==> x == 0)
_(axiom \forall UINT32 x; {Bm32SpecialValue(x)} (\forall UINT32 i; i < 32 ==> ToBm32(x)[i]) ==> x == (UINT32)-1)
_(axiom \forall UINT32 x,y; { ToBm32(x & y) } ToBm32(x & y) == Bm32Intersect(ToBm32(x), ToBm32(y)))
_(axiom \forall UINT32 x,y; { ToBm32(x | y) } ToBm32(x | y) == Bm32Union(ToBm32(x), ToBm32(y)))
_(axiom \forall UINT32 x,y; { ToBm32(x ^ y) } ToBm32(x ^ y) == Bm32SymmetricDiff(ToBm32(x), ToBm32(y)))
_(axiom \forall UINT32 x; \forall UINT64 i; i < 32 ==> ToBm32(x)[i] <==> (x & (1UI32 << i)) != 0)

UINT64 Add64(UINT64 x, UINT64 n)
  _(requires n < 64)
  _(ensures ToBm64(\result)[n])
{
  return x | (1UI64 << n);
}

int InSet64(UINT64 x, UINT64 n)
  _(requires n < 64)
  _(ensures \result == ToBm64(x)[n])
{
  return (x & (1UI64 << n)) != 0;
}

UINT64 Toggle64(UINT64 x, UINT64 n)
  _(requires n < 64)
  _(ensures !(ToBm64(\result)[n] <==> ToBm64(x)[n]))
{
  return (x ^ (1UI64 << n));
}

UINT32 Add32(UINT32 x, UINT64 n)
  _(requires n < 32)
  _(ensures ToBm32(\result)[n])
{
  return x | (1UI32 << n);
}

int InSet32(UINT32 x, UINT64 n)
  _(requires n < 32)
  _(ensures \result == ToBm32(x)[n])
{
  return (x & (1UI32 << n)) != 0;
}

UINT32 Toggle32(UINT32 x, UINT64 n)
  _(requires n < 32)
  _(ensures !(ToBm32(\result)[n] <==> ToBm32(x)[n]))
{
  return (x ^ (1UI32 << n));
}

void SpecialValues64() {
  UINT64 zero, all;
  _(assume \forall UINT64 i; i < 64 ==> ToBm64(all)[i])
  _(assume \forall UINT64 i; i < 64 ==> !ToBm64(zero)[i])
  _(assert Bm64SpecialValue(all))
  _(assert all == (UINT64)-1)
  _(assert Bm64SpecialValue(zero))
  _(assert zero == 0)
}

void SpecialValues32() {
  UINT32 zero, all;
  _(assume \forall UINT64 i; i < 32 ==> ToBm32(all)[i])
  _(assume \forall UINT64 i; i < 32 ==> !ToBm32(zero)[i])
  _(assert Bm32SpecialValue(all))
  _(assert all == (UINT32)-1)
  _(assert Bm32SpecialValue(zero))
  _(assert zero == 0)
}

void FortyTwo64() {
  UINT64 one = 1;
  UINT64 ft = (one << 5) | (one << 3) | (one << 1);
  _(assert !ToBm64(ft)[0])
  _(assert ToBm64(ft)[1])
  _(assert !ToBm64(ft)[2])
  _(assert ToBm64(ft)[3])
  _(assert !ToBm64(ft)[4])
  _(assert ToBm64(ft)[5])
  _(assert !ToBm64(ft)[6])
}

void FortyTwo32() {
  UINT32 one = 1;
  UINT32 ft = (one << 5) | (one << 3) | (one << 1);
  _(assert !ToBm32(ft)[0])
  _(assert ToBm32(ft)[1])
  _(assert !ToBm32(ft)[2])
  _(assert ToBm32(ft)[3])
  _(assert !ToBm32(ft)[4])
  _(assert ToBm32(ft)[5])
  _(assert !ToBm32(ft)[6])
}

typedef struct _toto {
    UINT64 inti;
    }toto, *ptoto;

int
test(ptoto ob)
_(requires \wrapped(ob))
_(requires ob->inti==0)
_(writes ob)
{
  _(unwrap ob)
  _(assert ob->inti == 0)
  ob->inti=ob->inti | _(unchecked)(_(UINT64)(1<<1));
  _(assert ToBm64(ob->inti)[1])
  _(assert ob->inti != 0)
  _(assert ob->inti == 2)
  _(assert ToBm64(ob->inti)[1])
  _(assert \forall UINT64 i; i < 64 && i != 1 ==> !ToBm64(ob->inti)[i])
  //assert((ob->inti & (1UI64<<1)) == 2);
  return 1;
};
/*`
Verification of Add64 succeeded.
Verification of InSet64 succeeded.
Verification of Toggle64 succeeded.
Verification of Add32 succeeded.
Verification of InSet32 succeeded.
Verification of Toggle32 succeeded.
Verification of SpecialValues64 succeeded.
Verification of SpecialValues32 succeeded.
Verification of FortyTwo64 succeeded.
Verification of FortyTwo32 succeeded.
Verification of test succeeded.
`*/
