#include <vcc.h>

_(logic \bool sorted(int *buf, unsigned len) =
  \forall unsigned i, j; i < j && j < len ==> buf[i] <= buf[j])

_(typedef unsigned perm_t[unsigned]; )

_(logic \bool is_permutation(perm_t perm, unsigned len) =
  (\forall unsigned i, j;
    i < j && j < len ==> perm[i] != perm[j]))

_(logic \bool is_permuted(\state s, int *buf, unsigned len, perm_t perm) =
  \forall unsigned i;  i < len ==> perm[i] < len && \at(s, buf[ perm[i] ]) == buf[i])

_(_(pure) perm_t swap(perm_t p, unsigned i, unsigned j)
  _(ensures \result == \lambda unsigned k; k == i ? p[j] : k == j ? p[i] : p[k]); )

void bubble_sort(int *buf, unsigned len _(out perm_t perm))
  _(writes \array_range(buf, len))
  _(ensures sorted(buf, len))
  _(ensures is_permutation(perm, len))
  _(ensures is_permuted(\old(\now()), buf, len, perm))
{
  int swapped;
  _(ghost \state s0 = \now() )

  _(ghost perm = \lambda unsigned i; i)

  if (len == 0) return;

  do
    _(invariant \mutable_array(buf, len))
    _(invariant is_permutation(perm, len))
    _(invariant is_permuted(s0, buf, len, perm))
  {
    int tmp;
    unsigned i;

    swapped = 0;
    for (i = 0; i < len - 1; ++i)
      _(invariant !swapped ==> sorted(buf, i + 1))
      _(invariant \mutable_array(buf, len))
      _(invariant is_permutation(perm, len))
      _(invariant is_permuted(s0, buf, len, perm))
    {
      if (buf[i] > buf[i + 1]) {
        tmp = buf[i + 1];
        buf[i + 1] = buf[i];
        buf[i] = tmp;
        _(ghost perm = swap(perm, i, i + 1) )
        swapped = 1;
      }
    }

  }
  while (swapped);
}

/*`
Verification of bubble_sort succeeded.
`*/
