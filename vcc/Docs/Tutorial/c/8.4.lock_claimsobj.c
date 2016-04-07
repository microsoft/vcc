#include <vcc.h>

/*{lock}*/
_(claimable, volatile_owns) struct Lock {
  volatile int locked;
  _(ghost \object protected_obj;)
  _(invariant locked == 0 ==> \mine(protected_obj))
};

/*{init}*/
void InitializeLock(struct Lock *l _(ghost \object obj))
  _(writes \span(l), obj)
  _(requires \wrapped(obj))
  _(ensures \wrapped0(l) && l->protected_obj == obj)
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
  _(ensures \wrapped(l->protected_obj) && \fresh(l->protected_obj))
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
  _(requires \wrapped(c) && \claims_object(c, l))
  _(requires l->protected_obj != c)
  _(requires \wrapped(l->protected_obj))
  _(ensures \wrapped(c))
  _(writes l->protected_obj)
{
  _(atomic c, l) {
    _(assert \by_claim(c, l->protected_obj) != c) // why do we need it?
    l->locked = 0;
    _(ghost l->\owns += l->protected_obj)
  }
}

/*{struct_data}*/
struct Data {
  int x;
};
/*{create_claim}*/
void create_claim(struct Data *d)
  _(requires \wrapped(d))
  _(writes d)
{
  _(ghost \claim c;)
  struct Lock l;
  InitializeLock(&l _(ghost d));
  _(ghost c = \make_claim({&l}, \true);)
  Acquire(&l _(ghost c));
  Release(&l _(ghost c));
  _(ghost \destroy_claim(c, {&l}));
  _(unwrap &l)
}
/*{out}*/
/*`
Verification of Lock#adm succeeded.
Verification of InitializeLock succeeded.
Verification of Acquire succeeded.
Verification of Release succeeded.
Verification of create_claim succeeded.
`*/
