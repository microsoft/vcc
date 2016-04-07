#include <vcc.h>


  _(ghost _(claimable) struct Protector {
    int dummy;
  };)



  _(ghost _(claimable) struct AbstractStruct
  {
    volatile int value;
    struct Protector protector;

    // By claiming the protector, a claim that abs->value doesn't change can be
    // established.
    _(invariant (&protector)->\closed ==> \unchanged(value))
    // The other case.
    _(invariant value == 2*\old(value) || \unchanged(value))
  };)


struct ConcreteStruct
{
  int value;
  _(ghost struct AbstractStruct *abs)
  _(invariant \mine(abs, &abs->protector))
  // We need to make sure no one has a claim on the protector, as we will want
  // to crack it open.
  _(invariant (&abs->protector)->\claim_count == 0)
  _(invariant value == abs->value)
};

void writeStruct(struct ConcreteStruct *s, int v)
  _(maintains \wrapped(s))
  _(writes s)
  _(requires v == 2*s->value)
{
  _(ghost \claim c)

  // Need to save s->abs into a local, otherwise when using s->abs in claims,
  // the prover thinks that it might change (which is true).
   _(ghost struct AbstractStruct *abs = s->abs;) 

  // We unwrap s and immediately take a claim on the protector and abs.
  // The claim holds initially, because we're right after unwrap, therefore
  // the invariant of s has to hold.
  // The claim holds after step of the machine, because the abs and its protector
  // stay closed, therefore abs->value cannot change.
  _(unwrap s)
  _(ghost c = \make_claim({&abs->protector, abs}, abs->value == \when_claimed(abs->value)))

  s->value = v;

  _(atomic abs) {
    // Here actions of other thread happen ('atomic havoc')
    //
    // Note the missing c in the atomic clause: if we had listed c above, the
    // compiler generates an assert(valid_claim(c)) here and _after_
    // begin_update().  If you look below, you see that the second one cannot
    // hold.  The first assert we do explicitly, allowing us to still make use
    // of the claim here.
    
    // We use the claim, so we know abs->value didn't change.
    _(assert \active_claim(c))
    // We get rid of the claim...
    _(ghost \destroy_claim(c, {&abs->protector, abs}));
    // ...so that we can crack the protector open.
    _(unwrap &abs->protector)

    // begin_update() gives you write access to s, and also makes
    // the two state invariant of s to be checked between here and
    // the end of the atomic block. Otherwise it does not modify the
    // heap.
    _(begin_update)
    _(ghost s->abs->value = v)
  }
  // We close the protector again.
  _(wrap &abs->protector)
  // Then we can close s. Note that there was no other atomic havoc since the
  // beginning of atomic, which is why the invariant of s holds.
  _(wrap s)
}

/*`
Verification of AbstractStruct#adm succeeded.
Verification of ConcreteStruct#adm succeeded.
Verification of writeStruct succeeded.
`*/
