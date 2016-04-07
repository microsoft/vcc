#include <vcc.h>

void foo() {
  _(ghost \objset s1;)
  _(ghost \objset s2;)
  _(ghost \objset s3;)
  _(ghost \object o;)
  _(assume o \in s1;)
  _(assume o \in s2;)
  _(assume !(o \in s3);)
  _(assert o \in s1 \inter s2;)
  _(assert !(o \in s1 \inter s3);)
  _(assert o \in s1 \union s3;)
  _(assert !(o \in s1 \diff s2);)
}
/*`
Verification of foo succeeded.
`*/
