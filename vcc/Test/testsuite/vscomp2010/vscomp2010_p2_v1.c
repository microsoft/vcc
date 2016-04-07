#include <vcc.h>
#ifndef VERIFY
#include <stdio.h>
#endif

#define is_bounded(A, N) \
  (\forall unsigned _j; _j < (N) ==> (A)[_j] < (N))

#define is_inverse(A, inverse, N) \
  (\forall unsigned _j; _j < (N) ==> (A)[(inverse)[_j]] == _j)

#define is_injective(A, N) \
  (\forall unsigned _j1, _j2; _j1 < (N) && _j2 < (N) && (A)[_j1] == (A)[_j2] ==> _j1 == _j2)

void invert(unsigned *A, unsigned *B, unsigned N _(ghost unsigned inverse[unsigned]))
  _(requires is_bounded(A, N))
  _(requires is_injective(A, N))
  _(requires is_bounded(inverse, N))
  _(requires is_inverse(A, inverse, N))
  _(maintains \wrapped((unsigned[N])A))
  _(maintains \mutable((unsigned[N])B))
  _(writes \array_range(B,(unsigned)N))
  _(ensures is_bounded(B, N))
  _(ensures is_injective(B, N))
  _(ensures is_inverse(B, A, N))
{
  unsigned i;

  for (i = 0; i < N; i++)
    _(invariant \forall unsigned j; j < i ==> B[A[j]] == j)
  {
    B[A[i]] = i;
  }

  _(assert \forall unsigned j; {B[j]} j < N ==> B[j] == B[A[inverse[j]]])
}

#ifndef VERIFY
void main(int argc, char **argv) {
  unsigned A[10] = { 9, 3, 8, 2, 7, 4, 0, 1, 5, 6 };
  unsigned B[10];
  unsigned i;

  invert(A, B, 10);

  for (i = 0; i < sizeof(B)/sizeof(unsigned); i++) {
    printf("B[%d] = %d\n", i, B[i]);
  }
}
#endif

/*`
Verification of invert succeeded.
`*/
