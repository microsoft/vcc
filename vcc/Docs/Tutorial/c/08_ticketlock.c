// vim:set expandtab tabstop=4 shiftwidth=4:
#include "vcc.h"

struct Data { int data; };

// TODO reference counts
typedef _(volatile_owns) _(claimable) struct Lock {
    volatile int serving;
    volatile int ticket;
    _(ghost volatile \claim tickets[int])
    _(ghost \object protected_object)
    // TODO consider protected_object claimable / not claimable?

    _(invariant serving <= ticket)

    _(invariant ticket==serving || tickets[serving] ==> \mine(protected_object))

    _(invariant \forall int i;
        \unchanged(tickets[i]) ||
        !\old(tickets[i]) ||
        !\old(tickets[i])->\closed)
        // the last one replaced 'inv(old(tickets[i]))' from the board; in the
        // VCC tool, inv() is not defined for claim pointers

    _(invariant \forall int i; ticket <= i ==> !tickets[i])

} Lock;

void Initialize(Lock *lock _(ghost \object protected_object))
    _(requires \wrapped(protected_object))
    _(writes \extent(lock), protected_object)
    _(ensures \wrapped0(lock))
    _(ensures lock->protected_object==protected_object)
{
    lock->serving = lock->ticket = 0;
    _(ghost lock->protected_object = protected_object)
    _(ghost lock->tickets = \lambda int i; (\claim)0)
    _(ghost lock->\owns = {protected_object})
    _(wrap lock)
}

void Acquire(Lock *lock _(ghost \claim lockAccessClaim))
    _(requires \wrapped(lockAccessClaim) && \claims(lockAccessClaim, lock->\closed))
    _(ensures \wrapped(lock->protected_object) && \fresh(lock->protected_object))
    _(writes lock) // TODO we can get rid of the writes() clause setting up a so-called "self claim", which we have avoid here
{
    _(ghost \claim c)
    int ticket;

    _(atomic lockAccessClaim, lock) {
        _(assume lock->ticket < 4711) // TODO assume no overflow
        ticket = lock->ticket++; // TODO use interlocked intrinsics
        _(ghost lock->tickets[ticket] = \make_claim({lock}, c==lock->tickets[ticket]))
        _(ghost c = lock->tickets[ticket])
    }

    _(atomic lockAccessClaim, lock, c) {
        _(assume ticket==lock->serving) // TODO should add loop
        _(ghost \destroy_claim(c, {lock}))
        _(ghost lock->\owns -= lock->protected_object)
        _(ghost lock->tickets[ticket] = (\claim)0)
    }
}

void Release(Lock *lock _(ghost \claim lockAccessClaim))
    _(requires \wrapped(lockAccessClaim) && \claims(lockAccessClaim, lock->\closed))
    _(requires \wrapped(lock->protected_object))
    _(writes lock->protected_object)
{
    _(atomic lockAccessClaim, lock) {
        _(assert \unchanged(lock->protected_object))
        _(assume lock->serving < 4711) // TODO assume no overflow
        lock->serving++; // TODO should split into read and write
        _(ghost lock->\owns += lock->protected_object);
    }
}

/*`
testcase(52,18) : warning VC9302: [possible unsoundness]: more than one access to physical memory in atomic block ('lock->ticket' and 'lock->ticket'); extra accesses might be due to bitfield operations
testcase(73,9) : warning VC9302: [possible unsoundness]: more than one access to physical memory in atomic block ('lock->serving' and 'lock->serving'); extra accesses might be due to bitfield operations
Verification of Lock#adm succeeded.
Verification of Initialize succeeded.
Verification of Acquire succeeded.
Verification of Release succeeded.
`*/
