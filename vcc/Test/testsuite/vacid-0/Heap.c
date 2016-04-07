/*
Copyright (c) 2010, Microsoft Corporation
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

   * Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimer.

   * Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.

   * Neither the name of Microsoft Corporation nor the names of its
     contributors may be used to endorse or promote products derived from this
     software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <vcc.h>
#include <stdio.h> // R

#define MAXLEN 1000 // R

_(ghost typedef \integer intmset[int])
_(ghost _(pure) unsigned mark(unsigned i) _(returns i))

_(ghost _(pure) \bool mark3(unsigned i, int e) _(returns mark(i) >= 0 && mark(2*i+1) >= 0 && mark(2*i+2) >= 0))

#define DEF(F,D) _(logic \bool F = {:split} D)

DEF(isHeapExcept(struct Heap *h, unsigned p),
  (\forall unsigned i; {h->sh[mark(i)]} i >= h->len ==> (h->sh[mark(i)] == \lambda int e; (\integer)0)) &&
  \forall unsigned i; int e; {h->sh[mark(i)][e]} {mark3(i,e)} {:hint mark3(i,e)}
    i < h->len ==> (h->sh[mark(i)][e] >= 0 && (i != p ==> h->sh[i][e] > 0 ==> e >= h->heap[i])))

#define isheap(h) isHeapExcept(h,h->len)
#define tcAt(h,i,e) ((e == h->heap[i] ? 1 : 0) + h->sh[2*i+1][e] + h->sh[2*i+2][e])

DEF(tcExcept(struct Heap *h, unsigned p),
  \forall unsigned i; {h->sh[mark(i)]} i != p && i < h->len ==> (h->sh[mark(i)] == \lambda int e; tcAt(h,i,e)))

struct Heap {              // R
  // public:
  unsigned len;            // R
  _(ghost intmset abs)

  // private:
  int heap[MAXLEN];        // R
  _(ghost intmset sh[unsigned])
  _(invariant sh[0] == abs)
  _(invariant len <= MAXLEN)
  _(invariant tcExcept(\this, len))
  _(invariant isheap(\this))
};                         // R

void init(struct Heap *h) // R
  _(writes \span(h))
  _(ensures \wrapped(h) && h->len == 0 && h->abs == \lambda int e; (\integer)0)
{ // R
  _(ghost {
    h->sh = \lambda unsigned i; int e; (\integer)0;
    h->abs = h->sh[0];
  })
  h->len = 0; // R
  _(wrap h)
} // R

void insert(struct Heap *h, int elt) // R
  _(requires h->len < MAXLEN - 1)
  _(maintains \wrapped(h))
  _(writes h)
  _(ensures h->abs == \lambda int k; k == elt ? \old(h->abs)[k] + 1 : \old(h->abs)[k])
  _(ensures h->len == \old(h->len) + 1)
{ // R
  unsigned p; // R

  _(unwrap h)
  p = h->len; // R
  h->len = h->len + 1; // R
  h->heap[p] = elt; // R

  _(assert mark3(p,0))

  while (p > 0) // R
    _(invariant \unchanged(h->len) && \unchanged(h->sh[0]))
    _(invariant p < h->len)
    _(invariant isheap(h))
    _(writes \span(h))
    _(invariant tcExcept(h, p))
    _(invariant h->sh[p] == \lambda int e; (e == elt ? -1 : 0) + tcAt(h, p, e))
    _(invariant h->heap[p] == elt)
  { // R
    unsigned p2; // R

    p2 = (p - 1) / 2; // R

    _(assert mark3(p2,0))
    //_(assert mark3(p,0))
    _(assert mark3(2*p+1,0))
    _(assert mark3(2*p+2,0))

    _(assert h->sh[p2][h->heap[2*p+2]] >= 0)
    _(assert h->sh[p2][h->heap[2*p+1]] >= 0)

//    _(assert 2*p+2 < h->len && h->heap[2*p+2] != elt ==> h->sh[p2][h->heap[2*p+2]] > 0)
//    _(assert 2*p+1 < h->len && h->heap[2*p+1] != elt ==> h->sh[p2][h->heap[2*p+1]] > 0)

    if (h->heap[p] < h->heap[p2]) { // R
      int tmp; // R
      tmp = h->heap[p]; // R
      h->heap[p] = h->heap[p2]; // R
      h->heap[p2] = tmp; // R
//      _(assert 2*p+2 < h->len ==> h->sh[p2][h->heap[2*p+2]] > 0)
//      _(assert 2*p+1 < h->len ==> h->sh[p2][h->heap[2*p+1]] > 0)
    } else  // R
    {
      _(ghost h->sh[p] = \lambda int e; tcAt(h, p, e))
      p = p2;
      break; // R
    }

    _(ghost h->sh[p] = \lambda int e; tcAt(h, p, e))
    p = p2; // R
  } // R

  while (p > 0)
    _(invariant \unchanged(h->len) && \unchanged(h->sh[0]))
    _(invariant p < h->len)
    _(invariant isheap(h))
    _(writes \span(h))
    _(invariant tcExcept(h, p))
    _(invariant h->sh[p] == \lambda int e; (e == elt ? -1 : 0) + tcAt(h, p, e))
    _(invariant h->heap[p] <= elt)
    _(invariant p == 0 || h->sh[p][h->heap[p]] > 0)
  {
    unsigned p2;

    p2 = (p - 1) / 2;

//    _(assert mark3(p,0))
    _(assert mark3(p2,0))

    _(assert h->sh[p2][h->heap[p]] > 0)

//    _(assert h->heap[p] >= h->heap[p2])

    _(ghost h->sh[p] = \lambda int e; tcAt(h, p, e))
    p = p2;
  }

//  _(assert p == 0)
  _(ghost {
    h->sh[p] = \lambda int e; tcAt(h, p, e);
    h->abs = h->sh[p];
  })
  _(wrap h)
} // R

int extractMin(struct Heap *h) // R
  _(requires h->len > 0)
  _(maintains \wrapped(h))
  _(writes h)
  _(ensures \old(h->abs)[\result] > 0)
  _(ensures \forall int e; \old(h->abs)[e] > 0 ==> \result <= e)
  _(ensures h->abs == \lambda int k; k == \result ? \old(h->abs)[k] - 1 : \old(h->abs)[k])
  _(ensures h->len == \old(h->len) - 1)
{ // R
  int res; // R
  int last;
  unsigned p; // R

  _(unwrap h)
  res = h->heap[0]; // R
  _(assert mark3(0,0))
  _(assert \forall int e; \old(h->abs)[e] > 0 ==> res <= e)
  h->len--; // R

  p = h->len;
  _(assert mark3(p,0))
  last = h->heap[p];
  _(assert h->sh[p][last] == 1)
  _(ghost h->sh[p] = \lambda int e; (\integer)0)

  if (p == 0) goto end;

  p = (p - 1) / 2;
  _(assert mark3(p,0))

  while (p > 0)
    _(invariant \unchanged(h->sh[0]))
    _(invariant p < h->len)
    _(invariant isheap(h))
    _(writes &h->sh)
    _(invariant tcExcept(h, p))
    _(invariant h->sh[p] == \lambda int e; (e == last ? 1 : 0) + tcAt(h, p, e))
  {
    _(assert mark3(p,0))
    _(assert mark3((p-1)/2,0))
    _(ghost h->sh[p] = \lambda int e; tcAt(h, p, e))
    p = (p - 1) / 2;
  }

  h->heap[0] = h->heap[h->len];
  _(ghost h->sh[0] = \lambda int e; tcAt(h, p, e))

  p = 0; // R
  while (p < h->len) // R
    _(invariant \unchanged(h->len))
    _(invariant h->sh[0] == \lambda int k; k == res ? \old(h->abs)[k] - 1 : \old(h->abs)[k])
    _(writes \span(h))
    _(invariant isHeapExcept(h, p))
    _(invariant tcExcept(h, h->len))
  { // R
    unsigned l = 2*p+1, r = 2*p+2;  // R
    unsigned smallest = p; // R
    if (l < h->len && h->heap[l] < h->heap[p]) // R
      smallest = l; // R
    if (r < h->len && h->heap[r] < h->heap[smallest]) // R
      smallest = r; // R
    if (smallest != p) { // R
      int tmp; // R
      tmp = h->heap[p]; // R
      h->heap[p] = h->heap[smallest]; // R
      h->heap[smallest] = tmp; // R
      _(assert mark3(smallest, 0))
      _(assert mark3(p, 0))
      _(ghost h->sh[smallest] = \lambda int e; tcAt(h, smallest, e))
      p = smallest; // R
    } else // R
    {
      _(assert isheap(h))
      break; // R
    } // R
  } // R

end:
  _(ghost h->abs = h->sh[0])
  _(wrap h)

  return res; // R
} // R


_(ghost typedef unsigned idxseq_t[\integer])
_(ghost typedef unsigned perm_t[unsigned])

#define indexesOK() \
  (\forall int e; \integer i; 0 <= i && i < h.abs[e] ==> indexes[e][i] < len && \old(arr[indexes[e][i]]) == e) && \
  (\forall int e1, e2; \integer i1, i2; \
    0 <= i1 && 0 <= i2 && \
    i1 < h.abs[e1] && i2 < h.abs[e2] && (e1 != e2 || i1 != i2) ==> indexes[e1][i1] != indexes[e2][i2])

#define validPerm(N) \
  ((\forall unsigned a, b; a < b && b < N ==> perm[a] != perm[b]) && \
   \forall unsigned a; {arr[a]} {perm[a]} a < N ==> perm[a] < len && \old(arr[perm[a]]) == arr[a])

#define sorted(N) \
  (\forall unsigned a, b; a < b && b < N ==> arr[a] <= arr[b])

void heapSort(int *arr, unsigned len // R
              _(out perm_t perm)
             ) // R
  _(requires len < MAXLEN)
  _(maintains \mutable_array(arr, len))
  _(writes \array_range(arr, len))
  _(ensures validPerm(len) && sorted(len))
{ // R
  struct Heap h; // R
  unsigned i; // R
  _(ghost idxseq_t indexes[int])

#ifndef VERIFY3
  _(assert \forall unsigned i; i < len ==> (\mutable(arr+i)))
#endif

  init(&h); // R

  for (i = 0; i < len; ++i) // R
    _(writes &h)
    _(invariant i <= len)
    _(invariant \wrapped(&h) && h.len == i)
    _(invariant indexesOK())
    _(invariant \forall int e; \integer k; 0 <= k && k < h.abs[e] ==> indexes[e][k] < i)
  {
    insert(&h, arr[i]); // R
    _(ghost indexes[arr[i]][h.abs[arr[i]] - 1] = i)
  }

  for (i = 0; i < len; ++i) // R
    _(writes &h, \array_range(arr, len))
    _(invariant i <= len)
    _(invariant \wrapped(&h) && h.len == len - i)
    _(invariant \mutable_array(arr, len))
    _(invariant indexesOK())
    _(invariant \forall int e; \integer a; unsigned b; 0 <= a && a < h.abs[e] && b < i ==> indexes[e][a] != perm[b])
    _(invariant \forall unsigned a; int e; a < i ==> (h.abs[e] > 0 ==> e >= arr[a]))
    _(invariant validPerm(i) && sorted(i))
  {
    arr[i] = extractMin(&h); // R
    _(ghost perm[i] = indexes[arr[i]][h.abs[arr[i]]])
  }

  _(unwrap &h)
}

#define ASSERT(E) { int tmp = E; _(assert tmp) } // A
void heapSortTestHarness() // R
{
  int arr[] = { 42, 13, 42 }; // R
  _(ghost unsigned perm[unsigned])
  heapSort(arr, 3 // R
           _(out perm)
          );  // R
  ASSERT(arr[0] <= arr[1] && arr[1] <= arr[2]); // R
  ASSERT(arr[0] == 13 && arr[1] == 42 && arr[2] == 42); // R
} // R

#ifndef VERIFY                                // A
int main()                                    // A
{                                             // A
  unsigned i;                                 // A
  int arr[] = { 3, 1, 2, 42, 0, 4 };          // A
  #define LEN (sizeof(arr) / sizeof(arr[0]))  // A
  heapSort(arr, LEN);                         // A
  for (i = 0; i < LEN; ++i)                   // A
    printf("%d ", arr[i]);                    // A
  printf("\n");                               // A
}                                             // A
#endif                                        // A

/*`
Verification of Heap#adm succeeded.
Verification of swprintf succeeded.
Verification of vswprintf succeeded.
Verification of _swprintf_l succeeded.
Verification of _vswprintf_l succeeded.
Verification of init succeeded.
Verification of insert succeeded.
Verification of extractMin succeeded.
Verification of heapSort succeeded.
Verification of heapSortTestHarness succeeded.
`*/
