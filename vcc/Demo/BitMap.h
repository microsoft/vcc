#pragma once

#include <vcc.h>
#include "spec.h"

#define BIT_SELECT(x, i) ((x) & (1 << (i)))

// |-------------------------------------------------------|
// | 010...                                                |
// |-------------------------------------------------------|
// <--                     Size                          -->

typedef struct _BITMAP {
  unsigned Size;      // Number of bits in bit map
  unsigned *Buffer;   // Memory to store the bit map

  #pragma region invariant

  // private invariants
  _(invariant Size > 0 && Size % 32 == 0)
  _(invariant \mine((unsigned[Size/32])Buffer))

  // public abstraction
  _(ghost \bool BM[unsigned]) // unsigned --> {true, false}
  _(invariant \forall unsigned i; i < Size ==>
        (BM[i] <==> BIT_SELECT(Buffer[i/32], i%32)))

  #pragma endregion
} BITMAP;

void InitializeBitMap (BITMAP *BitMap, unsigned * BitMapBuffer, unsigned Size)
  #pragma region contract
  _(writes \extent(BitMap), (unsigned[Size/32])BitMapBuffer)
  _(requires \wrapped((unsigned[Size/32])BitMapBuffer))
  _(requires Size > 0 && Size % 32 == 0)
  _(ensures \wrapped(BitMap))
  _(ensures BitMap->Size == Size)
  _(ensures \forall unsigned i; i < Size ==> BitMap->BM[i] == \false)
  #pragma endregion
  ;

void SetBit (BITMAP *BitMap, unsigned BitNumber)
  #pragma region contract
  _(writes BitMap)
  _(maintains \wrapped(BitMap))
  _(requires BitNumber < BitMap->Size)
  _(ensures \forall unsigned i;
      BitMap->BM[i] == (i == BitNumber ? \true : \old(BitMap->BM[i])))
  _(ensures \unchanged(BitMap->Size))
  #pragma endregion
  ;

_(pure) unsigned __int8 TestBit (BITMAP *BitMap, unsigned BitNumber)
  #pragma region contract
  _(reads &BitMap->BM)
  _(requires \wrapped(BitMap))
  _(requires 0 < BitNumber && BitNumber < BitMap->Size)
  _(ensures \result == BitMap->BM[BitNumber])
  #pragma endregion
  ;
