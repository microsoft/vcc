#include <vcc.h>

unsigned hash(unsigned char *s, unsigned len)
  _(requires \thread_local_array(s, len))
{
  unsigned i, res;
  for (res = 0, i = 0; i < len; ++i)
/*{update}*/
    res = _(unchecked)((res + s[i]) * 13);
/*{endupdate}*/
  return res;
}
/*`
Verification of hash succeeded.
`*/
