#include <vcc.h>
/*{begin}*/
_(void triangle()
	_(decreases 0)
{
  \natural x[\natural];
  \natural n;
  _(assume x[0] == 0 && \forall \natural i; x[i+1] == x[i] + i + 1)
  _(ghost 
      for (\natural i = 0; i < n; i=i+1) 
        _(invariant i <= n && x[i] == i * (i + 1) / 2)
      {})
  _(assert x[n] == n * (n + 1) / 2)
})
/*{end}*/
/*`
Verification of triangle succeeded.
`*/