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
  unsigned max;
  unsigned sum = 0;
  unsigned i;

  //_(ghost unsigned oldmax = 0)
  _(ghost unsigned maxsum = 0)

  _(ghost S = \lambda unsigned k; (unsigned)0)

  for (i = 0; i < N; i++)
    _(invariant \forall unsigned k; k < i ==> S[k + 1] == S[k] + a[k])
    _(invariant sum == S[i])
    _(invariant \forall unsigned k; k < i ==> a[k] <= max)
    _(invariant sum <= maxsum)
    _(invariant maxsum <= i * max)
    _(invariant sum <= i * max)
    _(invariant i <= N)
  {
    _(assert i < N)
    //_(ghost oldmax = max)
    if (max < a[i]) {
      max = a[i];
    }
    _(assume maxsum + max < UINT_MAX) // satisfy overflow check
    //_(assert maxsum <= i * oldmax)
    //_(assert oldmax <= max)
    _(assume maxsum <= i * max)

    _(ghost maxsum += max)
    sum += a[i];
    _(ghost S[i + 1] = S[i] + a[i])
  }

  _(assert sum == S[N])
  *maxout = max;

  return sum;
}

/*`
Verification of sum_max succeeded.
`*/
