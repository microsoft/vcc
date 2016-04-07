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

#define MAXLEN 1000 // R

#define ASSERT(E) { int tmp = E; _(assert tmp) } // A

_(ghost typedef \bool uset_t[unsigned])

_(ghost _(pure) \integer card(uset_t s))  // A
_(ghost _(pure) uset_t empty()  // A
 _(returns \lambda unsigned i; \false))  // A
_(ghost _(pure) uset_t addone(uset_t s, unsigned i) // A
  _(returns \lambda unsigned j; i == j ? \true : s[j]))  // A

_(axiom card(empty()) == 0) // A
_(axiom \forall uset_t s; unsigned i; card(s) >= 0 && !s[i] ==> card(addone(s, i)) == card(s) + 1) // A

_(ghost _(pure) \bool upper_card(uset_t s, \integer n) _(returns \forall unsigned i; s[i] ==> i < n))  // A
_(axiom \forall uset_t s; \integer n; upper_card(s, n) ==> card(s) <= n) // A

#define wrappedD(a) (a \in \domain(a) && \wrapped(a))

struct Array {               // R
  _(ghost int ab[unsigned])
  int val[MAXLEN];           // R
  unsigned idx[MAXLEN];      // R
  unsigned back[MAXLEN];     // R
  unsigned sz;               // R

  _(invariant sz <= MAXLEN)

  _(ghost uset_t mapped)
  _(invariant \forall unsigned i; mapped[i] <==> i < MAXLEN && idx[i] < sz && back[idx[i]] == i)
  _(invariant \forall unsigned i; i < MAXLEN ==> (ab[i] == (mapped[i] ? val[i] : 0)))
  _(invariant card(mapped) == (\integer)sz)
};                             // R

void init(struct Array *a)     // R
  _(writes \span(a))
  _(ensures wrappedD(a))
  _(ensures \forall unsigned i; a->ab[i] == 0)
{                              // R
  a->sz = 0;                   // R
  _(ghost {
    a->ab = \lambda unsigned i; 0;
    a->mapped = empty();
  })
  _(wrap a)
}                              // R

void set(struct Array *a, unsigned i, int v) // R
  _(writes a)
  _(requires i < MAXLEN)
  _(maintains wrappedD(a))
  _(ensures a->ab == \lambda unsigned j; i == j ? v : \old(a->ab)[j])
{                                                          // R
  _(unwrapping a) {
    _(ghost a->ab[i] = v)
    a->val[i] = v;                                         // R
    if (!(a->idx[i] < a->sz && a->back[a->idx[i]] == i)) { // R
      _(ghost a->mapped = addone(a->mapped, i))
      _(assert upper_card(a->mapped, MAXLEN))
      a->idx[i] = a->sz;                                   // R
      a->back[a->sz++] = i;                                // R
    }                                                      // R
  }
}                                                          // R

int get(struct Array *a, unsigned i)                       // R
  _(requires i < MAXLEN)
  _(maintains \wrapped(a))
  _(ensures \result == a->ab[i])
{                                                         // R
  if (a->idx[i] < a->sz && a->back[a->idx[i]] == i)       // R
    return a->val[i];                                     // R
  else return 0;                                          // R
}                                                         // R

void sparseArrayTestHarness()                             // R
{                                                         // R
  struct Array a, b;                                      // R

  init(&a);                                               // R
  init(&b);                                               // R
  ASSERT(get(&a, 5) == 0 && get(&b, 7) == 0);             // R
  set(&a, 5, 1); set(&b, 7, 2);                           // R
  ASSERT(get(&a, 5) == 1 && get(&b, 7) == 2);             // R
  ASSERT(get(&a, 0) == 0 && get(&b, 0) == 0);             // R

  _(unwrap &a)
  _(unwrap &b)
}                                                         // R

/*`
Verification of Array#adm succeeded.
Verification of init succeeded.
Verification of set succeeded.
Verification of get succeeded.
Verification of sparseArrayTestHarness succeeded.
`*/
