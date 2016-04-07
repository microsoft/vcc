/*{begin}*/
#include <vcc.h>

unsigned random(unsigned bound)
  _(requires bound > 0)
  _(ensures \result < bound)
  _(decreases 0)
;

/*`
`*/
