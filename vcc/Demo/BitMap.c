#include "BitMap.h"

void InitializeBitMap (BITMAP *BitMap, unsigned *BitMapBuffer, unsigned Size)
{
  BitMap->Size = Size;
  BitMap->Buffer = BitMapBuffer;
  memzero(BitMapBuffer, Size/32);

  _(ghost BitMap->BM = \lambda unsigned i; \false)
  _(wrap BitMap)
}

void SetBit (BITMAP *BitMap, unsigned BitNumber)
{
  _(unwrapping BitMap) {
  _(unwrapping (unsigned[BitMap->Size/32])(BitMap->Buffer)) {

    BitMap->Buffer[BitNumber/32] |= 1 << BitNumber % 32;

    _(assert {:bv} \forall unsigned x, i, j; j < 32 && i != j ==>
      (BIT_SELECT(x, i) <==> BIT_SELECT(x | (1 << j), i)))

    _(ghost BitMap->BM[BitNumber] = \true)
  }}
}

/*`
Verification of _BITMAP#adm succeeded.
Verification of InitializeBitMap succeeded.
Verification of SetBit succeeded.
Verification of SetBit#bv_lemma#0 succeeded.
Verification of TestBit#reads succeeded.
`*/
