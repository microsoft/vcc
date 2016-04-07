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
  _(writes l->protected_obj)
{
  _(atomic l) {
    l->locked = 0;
  }
}
/*{out}*/
/*`
Verification of Lock#adm succeeded.
Verification of Release failed.
testcase(15,12) : error VC8524: Assertion 'chunk locked == 0 ==> \mine(protected_obj) of invariant of l holds after atomic' did not verify.
`*/
