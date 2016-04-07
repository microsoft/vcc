#include <vcc.h>
#include <limits.h>

unsigned sum_max(unsigned *a, unsigned N, unsigned *maxout _(out unsigned S[unsigned]))
  _(requires \wrapped((unsigned[N])a))
  _(writes maxout)
  _(ensures \forall unsigned k; k < N ==> S[k + 1] == S[k] + a[k])
  _(ensures \result == S[N])
  _(ensures \forall unsigned k; k < N ==> a[k] <= *maxout)
  _(ensures \result <= N * *maxout)
{
  unsigned max = 0;
  unsigned sum = 0;
  unsigned i;

  _(ghost S[0] = 0)

  for (i = 0; i < N; i++)
    _(invariant \forall unsigned k; k < i ==> S[k + 1] == S[k] + a[k])
    _(invariant sum == S[i])
    _(invariant \forall unsigned k; k < i ==> a[k] <= max)
    _(invariant sum <= i * max)
    _(invariant i <= N)
  {
    _(assert \forall \integer x; max <= x ==> sum <= i * x) // Helper for (*).  Sometimes still looping, however.
    if (max < a[i]) {
      max = a[i];
    }
    _(assume sum + a[i] < UINT_MAX) // TODO satisfy overflow check
    _(assert sum <= i * max) // (*)

    sum += a[i];
    _(ghost S[i + 1] = S[i] + a[i])
  }

  _(assert sum == S[N])
  *maxout = max;

  return sum;
}

#ifndef VERIFY
int main(int argc, char **argv) {
  unsigned A[10] = { 9, 5, 0, 2, 7, 3, 2, 1, 10, 6 };
  unsigned sum, huh;
  sum = sum_max(A, 10, &huh);

  printf("max = %d\n", huh);
  printf("sum = %d\n", sum);
}
#endif

/*`
Verification of sum_max succeeded.
`*/
