#include <vcc.h>
#include <limits.h>

_(ghost _(pure) \integer fsum(\integer i, \integer map[\integer])
  _(returns i <= 0 ? (\integer) 0 : map[i - 1] + fsum(i - 1, map))
{
  return i <= 0 ? (\integer) 0 : map[i - 1] + fsum(i - 1, map);
})

_(ghost _(pure) void fsum_lemma(\integer i, \integer j, \integer map[\integer])
 _(requires 0 <= i)
 _(requires i <= j)
 _(requires \forall \integer k; 0 <= k && k < j ==> 0 <= map[k])
 _(ensures fsum(i, map) <= fsum(j, map))
{
  _(ghost \integer k = i)
  for( ; k < j; k += 1)
    _(invariant fsum(i, map) <= fsum(k, map))
    _(invariant i <= k && k <= j)
  {
    //_(assert fsum(k, map) == map[k - 1] + fsum(k - 1, map))
  }

  //_(assert fsum(j, map) <= fsum(i, map))
  _(assert k == j)
})


unsigned sum_max(unsigned *a, unsigned N, unsigned *maxout)
  _(requires \wrapped((unsigned[N])a))
  _(writes maxout)
  //_(returns fsum(N, \lambda \integer x; (x < 0 || x >= N) ? 0 : (\integer) a[x]))
  _(ensures \forall unsigned k; k < N ==> a[k] <= *maxout)
  _(ensures \result <= N * *maxout)
{
  unsigned max = 0;
  unsigned sum = 0;
  unsigned i;

  _(ghost \integer am[\integer] = \lambda \integer x; x < 0 || x >= N ? 0 : (\integer) a[x])
  _(assume fsum(N, am) < UINT_MAX)
  for (i = 0; i < N; i++)
    _(invariant sum == fsum(i, am))
    _(invariant \forall unsigned k; k < i ==> a[k] <= max)
    _(invariant sum <= i * max)
    _(invariant i <= N)
  {
    //_(assert \forall \integer x; max <= x ==> sum <= i * x)
    if (max < a[i]) {
      max = a[i];
    }
    _(assume sum <= i * max)

    _(assert i + 1 <= N)
    _(assert fsum(i + 1, am) == a[i] + fsum(i, am))
    _(ghost fsum_lemma(i + 1, N, am) )
    _(assert fsum(i + 1, am) < UINT_MAX) // TODO satisfy overflow check

    sum += a[i];
  }
  *maxout = max;

  _(assert sum == fsum(N, am))
  _(assert am == \lambda \integer x; x < 0 || x >= N ? 0 : (\integer) a[x])
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
testcase(17,3) : warning VC9323: [possible unsoundness]: ghost loop not checked for termination
testcase(4,11) : warning VC9303: [possible unsoundness]: cycle in pure function calls: fsum -> fsum
Verification of fsum succeeded.
Verification of fsum_lemma succeeded.
Verification of sum_max succeeded.
`*/
