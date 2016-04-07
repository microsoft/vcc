#include <vcc.h>

#define my_mutable_array(arr, len) (\forall unsigned i; {arr + i} i < len ==> \mutable(arr + i))

/*{swap}*/
void swap(int *p, int *q)
  _(writes p, q)
  _(ensures *p == \old(*q) && *q == \old(*p))
{
  int tmp;
  tmp = *p;
  *p = *q;
  *q = tmp;
}

/*{partition}*/
unsigned partition(int *arr, unsigned len, unsigned pivotIdx)
  _(writes \array_range(arr, len))
  _(requires my_mutable_array(arr, len))
  _(requires pivotIdx < len)
  _(requires len > 0)

  _(ensures my_mutable_array(arr, len))
  _(ensures \forall unsigned k; {arr[k]} k < \result ==> arr[k] <= \old(arr[pivotIdx]))
  _(ensures \forall unsigned k; {arr[k]} \result < k && k < len ==> arr[k] >= \old(arr[pivotIdx]))
  _(ensures \result < len)
{
  unsigned i, j;
  int pivot;
  
  pivot = arr[pivotIdx];

  i = 0;
  j = len - 1;
  while (i < j)
    _(writes \array_range(arr, len))
    _(invariant my_mutable_array(arr, len))
    _(invariant \forall unsigned k; {arr[k]} k < i ==> arr[k] <= pivot)
    _(invariant \forall unsigned k; {arr[k]} j < k && k < len ==> arr[k] >= pivot)
    _(invariant j < len)
  {
    if (arr[i] <= pivot) {
      i++;
    } else if (arr[j] >= pivot) {
      j--;
    } else {
      swap(arr + i, arr + j);
      i++;
      j--;
    }
  }

  return j;
}

#if 0
_(ghost ispure bool iszero(int x) returns(x == 0);)
/*{qsort}*/
void qsort(int *arr, unsigned len)
  _(writes array_range(arr, len))
  _(requires my_mutable_array(arr, len))
  _(ensures my_mutable_array(arr, len))
  _(ensures \forall unsigned i; {arr[i]} i < len - 1 ==> arr[i] <= arr[i+1])
  _(ensures \forall unsigned k; {&arr[k]} {hint: iszero(arr[k])} k < len ==> \exists unsigned k0; k0 < len && arr[k] == \old(arr[k0]))
{
  unsigned idx;

  if (len <= 1) return;

  idx = partition(arr, len, len / 2);

  qsort(arr, idx);
  _(assert \forall unsigned k; {&arr[k]} {hint: iszero(arr[k])} k < len ==> \exists unsigned k0; k0 < len && arr[k] == \old(arr[k0]))
  _(assume \false)
  if (idx < len)
    qsort(arr + idx + 1, len - idx - 1);
}
#endif
/*`
Verification of swap succeeded.
Verification of partition succeeded.
`*/
