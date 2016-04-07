#include <vcc.h>

/*{begin}*/
int read_pointer(int *p)
  _(requires \thread_local(p))
{
  return *p;
}
/*`
Verification of read_pointer succeeded.
`*/
