/*{begin}*/
#include <vcc.h>

unsigned hash(unsigned char *s, unsigned len)
  _(requires \thread_local_array(s, len))
{
  unsigned i, res;
  for (res = 0, i = 0; i < len; ++i)
    res = (res + s[i]) * 13;
  return res;
}
/*`
Verification of hash failed.
testcase(9,11) : error VC8004: (res + s[i]) * 13 might overflow.
`*/
