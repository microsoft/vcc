#include <vcc.h>

_(logic \bool sorted(int *buf, unsigned len) =
  \forall unsigned i, j; i < j && j < len ==> buf[i] <= buf[j])

void insertion_sort(int *buf, unsigned len)
  _(writes \array_range(buf, len))
  _(ensures sorted(buf, len))
{
  unsigned i, j;
  int v;

  for (i = 1; i < len; ++i)
    _(invariant sorted(buf, i))
    _(invariant \mutable_array(buf, len))
  {
    v = buf[i];
    j = i - 1;
    for (;;)
      _(invariant j <= i - 1)
      _(invariant sorted(buf, i))
      _(invariant (j == i - 1 && buf[i] == v) || sorted(buf, i + 1))
      _(invariant \forall unsigned k; j < k && k <= i ==> buf[k] >= v)
      _(invariant \mutable_array(buf, len))
      _(writes \array_range(buf, i + 1))
    {
      if (buf[j] > v) {
        buf[j + 1] = buf[j];
        if (_(unchecked)(j--) == 0) break;
      } else
        break;
    }
    buf[_(unchecked)(j + 1)] = v;
  }
}

/*`
Verification of insertion_sort succeeded.
`*/
