#include <vcc.h>

/*{lock}*/
_(claimable, volatile_owns) struct Lock {
  volatile int locked;
  _(ghost  \object protected_obj;)
  _(invariant  locked == 0 ==> \mine(protected_obj))
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
_(atomic_inline) int InterlockedCompareExchange(volatile int *Destination, int Exchange, int Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}
/*{acquire}*/
void Acquire(struct Lock *l _(ghost \claim c))
  _(always c, l->\closed)
  _(ensures  \wrapped(l->protected_obj) && \fresh(l->protected_obj))
{
  int stop = 0;

  do {
    _(atomic c, l) {
      stop = InterlockedCompareExchange(&l->locked, 1, 0) == 0;
      _(ghost if (stop) l->\owns -= l->protected_obj)
    }
  } while (!stop);
}

/*{release}*/
void Release(struct Lock *l _(ghost \claim c))
  _(always c, l->\closed)
  _(requires l->protected_obj != c)
  _(writes  l->protected_obj)
  _(requires  \wrapped(l->protected_obj))
{
  _(atomic c, l) {
    l->locked = 0;
    _(ghost l->\owns += l->protected_obj)
  }
}
/*{usage}*/
typedef struct _DATA {
  int a;
  int b;
  _(invariant a + b > 0)
} DATA;

_(ghost 
_(claimable) struct _DATA_CONTAINER {
  int dummy;
  _(invariant \mine(&DataLock))
  _(invariant DataLock.protected_obj == &Data)
} DataContainer;)

struct Lock DataLock;
DATA Data;

void testit(_(ghost \claim c))
  _(always c, (&DataContainer)->\closed)
{
  Acquire(&DataLock _(ghost c));
    _(unwrapping &Data) {
      Data.a = 5;
      Data.b = 7;
    }
  Release(&DataLock _(ghost c));
}

void boot()
  _(writes \universe())
  _(requires \program_entry_point())
{
  _(ghost \claim c;)

  Data.a = 42;
  Data.b = 17;
  _(wrap &Data)
  InitializeLock(&DataLock _(ghost &Data));
  _(ghost (&DataContainer)->\owns = {&DataLock, &DataContainer})
  _(wrap &DataContainer)

  _(ghost c = \make_claim({&DataContainer}, (&DataContainer)->\closed);)
  testit(_(ghost c));
}

/*{out}*/
/*`
Verification of Lock#adm succeeded.
Verification of _DATA#adm succeeded.
Verification of _DATA_CONTAINER#adm succeeded.
Verification of InitializeLock succeeded.
Verification of Acquire succeeded.
Verification of Release succeeded.
Verification of testit succeeded.
Verification of boot succeeded.
`*/
