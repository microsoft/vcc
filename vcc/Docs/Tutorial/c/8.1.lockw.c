#include <vcc.h>

/*{lock}*/
_(volatile_owns) struct Lock {
  volatile int locked;
  _(ghost \object protected_obj;)
  _(invariant locked == 0 ==> \mine(protected_obj))
};
/*{init}*/
void InitializeLock(struct Lock *l _(ghost \object obj))
  _(writes \span(l), obj)
  _(requires \wrapped(obj))
  _(ensures \wrapped(l) && l->protected_obj == obj)
{
  l->locked = 0;
  _(ghost {
    l->protected_obj = obj;
    l->\owns = {obj};
    _(wrap l)
  })
}
/*{xchg}*/
_(atomic_inline) 
int InterlockedCompareExchange(volatile int *Destination, int Exchange, int Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}
/*{acquire}*/
void Acquire(struct Lock *l)
  _(requires \wrapped(l))
  _(ensures \wrapped(l->protected_obj) && \fresh(l->protected_obj))
{
  int stop = 0;

  do {
    _(atomic l) {
      stop = InterlockedCompareExchange(&l->locked, 1, 0) == 0;
      _(ghost if (stop) l->\owns -= l->protected_obj)
    }
  } while (!stop);
}
/*{release}*/
void Release(struct Lock *l)
  _(requires \wrapped(l))
  _(requires \wrapped(l->protected_obj))
  _(writes l->protected_obj)
{
  _(atomic l) {
    l->locked = 0;
    _(ghost l->\owns += l->protected_obj)
  }
}
/*{out}*/
/*`
Verification of Lock#adm succeeded.
Verification of InitializeLock succeeded.
Verification of Acquire succeeded.
Verification of Release succeeded.
`*/
