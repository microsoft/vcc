//` /smoke

#include <vcc.h>

typedef struct S { int a; } S;
typedef struct T { int b; } T;

void foo(void *p)
  _(requires p \is struct S || p \is T)
  _(requires \thread_local(p))
{
  _(assert p \is S || p \is struct T)
}

// TODO smoke?

/*`
Verification of foo succeeded.
testcase(12,1) : warning : found unreachable code, possible soundness violation, please check the axioms or add an explicit assert(false)
`*/
