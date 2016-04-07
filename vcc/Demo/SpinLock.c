#include "SpinLock.h"
#include "Intrinsics.h"

void InitializeSpinLock(SPIN_LOCK *SpinLock _(ghost \object obj))
{
  SpinLock->Lock = 0;
  _(ghost SpinLock->protected_obj = obj;
    ghost SpinLock->\owns = {obj};
    wrap SpinLock)
}

#ifdef SIMPLE_SPIN_LOCKS

void Acquire(SPIN_LOCK *SpinLock)
{
  int stop;
  do  {
    _(atomic SpinLock) {
      stop = (__interlockedcompareexchange(&SpinLock->Lock, 1, 0) == 0);
      _(ghost if (stop) _(ghost SpinLock->\owns -= SpinLock->protected_obj))
    }
  } while (!stop);
}

void Release(SPIN_LOCK *SpinLock)
{
  _(atomic SpinLock) {
    SpinLock->Lock = 0;
    _(ghost SpinLock->\owns += SpinLock->protected_obj);
  }
}

#else

void Acquire(SPIN_LOCK *SpinLock _(ghost \claim access_claim))
{
  int stop;
  do {
    _(atomic access_claim, SpinLock) {
      stop = (__interlockedcompareexchange(&SpinLock->Lock, 1, 0) == 0);
      _(ghost if (stop) SpinLock->\owns -= SpinLock->protected_obj)
    }
  } while (!stop);
}

void Release(SPIN_LOCK *SpinLock _(ghost \claim access_claim))
{
  _(atomic access_claim, SpinLock) {
    SpinLock->Lock = 0;
    _(ghost  SpinLock->\owns += SpinLock->protected_obj);
  }
}

#endif

// Note: expected output only applies if SIMPLE_SPIN_LOCKS is defined
/*`
Verification of _SPIN_LOCK#adm succeeded.
Verification of InitializeSpinLock succeeded.
Verification of Acquire succeeded.
Verification of Release succeeded.
`*/
