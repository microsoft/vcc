#include <vcc.h>
#include <limits.h>

_(ghost typedef \integer IntIntMap[\integer])

_(ghost _(pure) bool match_integer(\integer) _(returns \true))

unsigned sum_max(unsigned *a, unsigned N, unsigned *maxout)
  _(requires \wrapped((unsigned[N])a))
  _(requires 0 < N)
  _(writes maxout)
  _(ensures \exists IntIntMap S;
    (\forall unsigned k; {:hint match_integer(S[k + 1])}
      k < N ==> S[k + 1] == S[k] + a[k]) &&
      (S[N] < UINT_MAX ==> \result == S[N]))
  _(ensures \forall unsigned k; k < N ==> a[k] <= *maxout)
  _(ensures \result <= N * *maxout)
  _(ensures \exists unsigned i; i < N && a[i] == *maxout)
{
  unsigned max = a[0];
  unsigned sum = 0;
  unsigned i;
  _(ghost IntIntMap S)
  _(ghost S[0] = 0)

  for (i = 0; i < N; i++)
    _(invariant \forall unsigned k; {match_integer(S[k + 1])} {:hint match_integer(S[k + 1])}
      k < i ==> S[k + 1] == S[k] + a[k])
    _(invariant S[i] < UINT_MAX ==> sum == S[i])
    _(invariant \forall unsigned k; k < i ==> a[k] <= max)
    _(invariant sum <= i * max)
    _(invariant i <= N)
    _(invariant \exists unsigned k; k < N && a[k] == max)
  {
    _(assert \forall \integer x; max <= x ==> sum <= i * x) // Helper for (*).  Could loop sometimes still.
    if (max < a[i]) {
      max = a[i];
    }
    _(assert sum <= i * max) // (*)

    _(unchecked) sum += a[i];
    _(ghost S[i + 1] = S[i] + a[i])
  }

  *maxout = max;

  return sum;
}

/*`
Verification of sum_max succeeded.
`*/
