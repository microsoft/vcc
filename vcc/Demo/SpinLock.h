#include <vcc.h>
#include <stdlib.h>

#define SIMPLE_SPIN_LOCKS

typedef _(claimable) _(volatile_owns) struct _SPIN_LOCK
{
  volatile int Lock;
  _(ghost \object protected_obj)
  _(invariant !Lock ==> \mine(protected_obj))
} SPIN_LOCK;

void InitializeSpinLock(SPIN_LOCK * SpinLock _(ghost \object obj))
  _(writes \span(SpinLock), obj)
  _(requires \wrapped(obj))
  _(ensures \wrapped(SpinLock))
  _(ensures SpinLock->protected_obj == obj)
  ;

#ifdef SIMPLE_SPIN_LOCKS

#define _claimable_

void Acquire(SPIN_LOCK *SpinLock)
  _(requires \wrapped(SpinLock))
  _(ensures \wrapped(SpinLock->protected_obj))
  _(ensures \fresh(SpinLock->protected_obj))
  ;

void Release(SPIN_LOCK *SpinLock)
  _(writes SpinLock->protected_obj)
  _(requires \wrapped(SpinLock))
  _(requires \wrapped(SpinLock->protected_obj))
  ;

#else

#define _claimable_ _(claimable)

void Acquire(SPIN_LOCK *SpinLock _(ghost \claim access_claim))
  _(always access_claim, SpinLock->\closed)
  _(ensures \wrapped(SpinLock->protected_obj))
  _(ensures \fresh(SpinLock->protected_obj))
  ;

void Release(SPIN_LOCK *SpinLock _(ghost \claim access_claim))
  _(writes SpinLock->protected_obj)
  _(always access_claim, SpinLock->\closed)
  _(requires access_claim != SpinLock->protected_obj)
  _(requires \wrapped(SpinLock->protected_obj))
  ;

#endif
