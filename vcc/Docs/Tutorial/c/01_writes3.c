#include <vcc.h>

#define writable(p) 1 // TODO

/*{beg}*/
void boundedIncr(int *p)
  _(writes p)
{
  _(assume writable(p)) // from writes clause

  _(assert \thread_local(p))
  if (*p < 100) {
    _(assert writable(p))
    (*p)++;
  }

  _(assert \old(*p) < 100 ==> *p == \old(*p) + 1) // ensures
}
/*`
Verification of boundedIncr succeeded.
`*/
