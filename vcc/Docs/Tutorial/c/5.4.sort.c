#include <vcc.h>

/*{begin}*/
_(def \bool sorted(int *buf, unsigned len) {
  return \forall unsigned i, j; i < j && j < len 
            ==> buf[i] <= buf[j];
})

void sort(int *buf, unsigned len)
  _(writes \array_range(buf, len))
  _(ensures sorted(buf, len))
  _(decreases 0)
{
  if (len < 2) return;
  for (unsigned i = len; i > 0; i--)
    _(invariant i <= len)
    _(invariant \forall unsigned u,v; 
      i <= v && u <= v && v < len 
      ==> buf[u] <= buf[v])
    for (unsigned j = 0; j + 1 < i; j++)
      _(decreases i-j)
      _(invariant j < i)
      _(invariant \forall unsigned u,v; 
          i <= v && u <= v && v < len 
          ==> buf[u] <= buf[v])
      _(invariant \forall unsigned u; u < j 
          ==> buf[u] <= buf[j])
      if (buf[j] > buf[j+1]) {
        int tmp = buf[j];
        buf[j] = buf[j+1];
        buf[j+1] = tmp;
      }
}
/*{out}*/
/*`
Verification of sorted succeeded.
Verification of sort succeeded.
`*/
