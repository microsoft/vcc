#include <vcc.h>
#include "Spinlock.h"
#include "BitMap.h"

_claimable_ struct LockContainer {
  BITMAP bitmap;
  _(as_array) unsigned buffer[10];
  SPIN_LOCK Lock;

  _(invariant \mine(&Lock))
  _(invariant Lock.protected_obj == &bitmap)
};

void InitContainer(struct LockContainer *lc)
  _(writes \extent(lc))
  _(ensures \wrapped(lc))
{
  _(wrap (unsigned[10])(lc->buffer))
  InitializeBitMap(&lc->bitmap, lc->buffer, 320);
  InitializeSpinLock(&lc->Lock _(ghost &lc->bitmap));
  _(wrap lc)
}

#ifdef SIMPLE_SPIN_LOCKS

void UseContainer(struct LockContainer *lc, unsigned bitNumber)
  _(writes lc)
  _(maintains \wrapped(lc))
{
  _(unwrapping lc) {
    Acquire(&lc->Lock);
    _(assert &lc->Lock \in \domain(&lc->Lock))
    if (bitNumber < lc->bitmap.Size) SetBit(&lc->bitmap, bitNumber);
    Release(&lc->Lock);
  }
}

#else

struct ConcurrentUser {
  struct LockContainer *lc;

  _(ghost \claim cont_claim)
  _(invariant \mine(cont_claim))
  _(invariant \claims_object(cont_claim, lc))
};

void UseContainer(struct LockContainer *lc, unsigned bitNumber _(ghost \claim cont_claim))
  _(always cont_claim, lc->\closed)
{
  Acquire(&lc->Lock _(ghost cont_claim));
  _(assert &lc->bitmap \in \domain(&lc->bitmap))
  if (bitNumber < lc->bitmap.Size) SetBit(&lc->bitmap, bitNumber);
  Release(&lc->Lock _(ghost cont_claim));
}

void InitializeConcurrentUser(struct ConcurrentUser *cu, struct LockContainer *lc)
  _(writes lc, \extent(cu))
  _(maintains \wrapped(lc))
  _(ensures \wrapped(cu))
  _(ensures cu->lc == lc)
{
  _(ghost cu->cont_claim = \make_claim({lc}, lc->\closed))
  cu->lc = lc;
  _(wrap cu)
}

void UseConcurrentOwner(struct ConcurrentUser *cu)
  _(writes cu)
  _(maintains \wrapped(cu))
{
  _(unwrapping cu) {
  UseContainer(cu->lc, 10 _(ghost cu->cont_claim));
  }
}

#endif

// Note: expected output only applies if SIMPLE_SPIN_LOCKS is defined
/*`
Verification of _SPIN_LOCK#adm succeeded.
Verification of _BITMAP#adm succeeded.
Verification of LockContainer#adm succeeded.
Verification of InitContainer succeeded.
Verification of UseContainer succeeded.
Verification of TestBit#reads succeeded.
`*/
