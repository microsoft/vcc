#include <vcc.h>

/*{lock}*/
_(volatile_owns) struct Lock {
  volatile int locked;
  _(ghost \object protected_obj;)
  _(invariant locked == 0 ==> \mine(protected_obj))
};
/*{release}*/
void Release(struct Lock *l)
  _(requires \wrapped(l))
  _(requires \wrapped(l->protected_obj))
{
  _(atomic l) {
    l->locked = 0;
    _(ghost l->\owns += l->protected_obj)
  }
}
/*{out}*/
/*`
Verification of Lock#adm succeeded.
Verification of Release failed.
testcase(16,13) : error VC8510: Assertion 'l->protected_obj is writable in call to l->\owns += l->protected_obj' did not verify.
`*/
