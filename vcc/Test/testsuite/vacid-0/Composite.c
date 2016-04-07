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
#include <stdlib.h>

#define inv0(p) ((p) == NULL || \inv(p))
#define nextclosed(f) (\forall struct Node *n; {n->f \in \this->\owns} n \in \this->\owns ==> n->f == NULL || n->f \in \this->\owns)

struct Node {
  struct Node *l, *r, *p;
  volatile int val, sum;
  _(ghost struct Mgr ^m)
  _(invariant m->\closed)
  _(invariant l != NULL ==> l != \this && l->p == \this && l->m == m && l->\closed)
  _(invariant r != NULL ==> r != \this && r->p == \this && r->m == m && r->\closed)
  _(invariant \this == m->except || sum == _(unchecked) (val + (l == NULL ? 0 : l->sum) + (r == NULL ? 0 : r->sum)))
  _(invariant \unchanged(sum) || \inv(p) || p == NULL)
  _(invariant \on_unwrap(\this, \false))
};
typedef struct Node *PNode;


_(ghost _(dynamic_owns) struct Mgr {
  volatile PNode except;
  _(invariant \unchanged(except) || inv0(\old(except)))
  _(invariant \approves(\this->\owner, except))
  _(invariant \forall struct Node *n; n \in \this->\owns ==> n->m == \this)
  _(invariant nextclosed(p))
  _(invariant nextclosed(l))
  _(invariant nextclosed(r))
  _(invariant \on_unwrap(\this, \false))
})


void update(struct Node *n, int v _(ghost struct Mgr ^m))
  _(requires n \in m->\owns)
  _(maintains \wrapped(m) && m->except == NULL)
  _(writes m)
{
  _(atomic n, m) {
    n->val = v;
    _(ghost {
      m->except = n;
      _(bump_volatile_version m)
    })
  }

  while (n)
    _(invariant m->except == n)
    _(invariant \wrapped(m))
    _(invariant n == NULL || n \in m->\owns)
    _(writes m)
  {
    int a,b;

    _(assert m \in \domain(m))
    _(assert n \in \domain(m))
    _(atomic n,m) {
      _(assert n->p == NULL || n->p \in \domain(m))
      _(assume a == n->l->sum && b == n->r->sum) // assume that we can read it atomically
      n->sum = _(unchecked) (n->val + (n->l == NULL ? 0 : a) + (n->r == NULL ? 0 : b));
      _(ghost {
       m->except = n->p;
       _(bump_volatile_version m)
      })
    }
    n = n->p;
  }
}

/*`
testcase(89,30) : warning VC9302: [possible unsoundness]: more than one access to physical memory in atomic block ('n->val' and 'n->sum'); extra accesses might be due to bitfield operations
testcase(89,30) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
Verification of Node#adm succeeded.
Verification of Mgr#adm succeeded.
Verification of update succeeded.
`*/
