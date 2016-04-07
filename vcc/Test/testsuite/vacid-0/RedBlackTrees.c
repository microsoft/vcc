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

#define NULL ((void*)0)

typedef struct Node {
  int red;
  int key, value;
  struct Node *left, *right, *parent;

} Node, *PNode;

_(ghost _(pure) \bool intTo\bool(int ) _(returns \true))

_(ghost typedef \bool PNodeSet[PNode])
_(ghost _(pure) PNode mark(PNode p) _(returns p))
_(ghost _(pure) \bool doMark(PNode p) _(returns mark(p) == p))

_(ghost _(pure) \bool mark2(PNode p))

#define DEF(F,...) _(logic \bool F = {:split} __VA_ARGS__)

DEF(rb_lrclosed(struct Tree *t, PNode p, PNode x),
  (\forall PNode n; {mark(n)} t->R[t->root][n] && mark(n)->parent == NULL ==> n == x || n == t->root) &&
  \forall PNode n,m; {t->R[mark(n)][m]} t->R[mark(n)][m] == (t->R[t->root][n] && ((n == p && m == x) || m == n || t->R[n->left][m] || t->R[n->right][m])))

DEF(rb_istree(struct Tree *t),
  !t->R[t->root][NULL] && // just for triggering
  (t->root != NULL ==> t->R[t->root][t->root] && t->root->parent == NULL) &&
  (\forall PNode m; !t->R[NULL][m]) &&
  (\forall PNode n, m; {t->R[mark(n)->left][m]} t->R[t->root][n] ==> t->R[mark(n)->left][m] ==> m->key < n->key) &&
  (\forall PNode n, m; {t->R[mark(n)->right][m]} t->R[t->root][n] ==> t->R[mark(n)->right][m] ==> m->key > n->key) &&

  (\forall PNode m; {t->R[t->root][m]} {mark2(m)} {:hint mark2(m)} t->R[t->root][m] <==> m \in t->\owns) &&
  (\forall PNode n, m; {t->R[n][m]} t->R[n][m] ==> t->R[t->root][m] && t->R[t->root][n]) &&
  (\forall PNode n; {mark(n)} t->R[t->root][n] && mark(n)->left != NULL ==> t->R[n][n->left] && n->left->parent == n) &&
  (\forall PNode n; {mark(n)} t->R[t->root][n] && mark(n)->right != NULL ==> t->R[n][n->right] && n->right->parent == n) &&
  (\forall PNode n; {mark(n)} t->R[t->root][n] && mark(n)->parent != NULL ==> t->R[t->root][n->parent] && (n->parent->left == n || n->parent->right == n)) &&
  (\forall PNode n; {t->R[t->root][n]} t->R[t->root][n] ==> t->R[n][n]) &&
  \true
)

DEF(rb_abs(struct Tree *t),
  (\forall PNode m; {t->abs[m->key]} t->R[t->root][m] ==> t->abs[m->key] == m->value) &&
  \forall int k; {t->abs[k]} (\forall PNode m; t->R[t->root][m] ==> m->key != k) ==> t->abs[k] == 0)

_(dynamic_owns) struct Tree {
  PNode root;
   _(ghost int abs[int])
   _(ghost PNodeSet R[PNode])

  _(invariant rb_istree(\this))
  _(invariant rb_abs(\this))
  _(invariant rb_lrclosed(\this, NULL, NULL))
};

void tree_init(struct Tree *t)
  _(writes \span(t))
  _(ensures \wrapped(t))
{
  t->root = NULL;
  _(ghost {
    t->R = \lambda PNode m; PNode n; \false;
    t->abs = \lambda int k; 0;
    t->\owns = {};
  })
  _(wrap t)
}


PNode tree_find(struct Tree *t, int key)
  _(requires \wrapped(t))
  _(ensures \result != NULL ==> t->R[t->root][\result] && \result->key == key)
  _(ensures \result == NULL ==> \forall PNode n; t->R[t->root][n] ==> n->key != key)
{
  PNode p;
  p = t->root;
  while (p)
    _(invariant p == NULL || t->R[t->root][mark(p)])
    _(invariant \forall PNode n; n->key == key && t->R[t->root][n] ==> t->R[p][n])
  {
    if (key < p->key)
      p = p->left;
    else if (key > p->key)
      p = p->right;
    else
      return p;
  }
  return NULL;
}

int tree_lookup(struct Tree *t, int key)
  _(requires \wrapped(t))
  _(ensures \result == t->abs[key])
{
  PNode r = tree_find(t, key);
  if (r == NULL) {
    _(assert \inv(t))
    return 0;
  } else
    return r->value;
}

void tree_insert(struct Tree *t, PNode x)
  _(maintains \wrapped(t))
  _(writes t, \span(x))
  _(requires !t->R[t->root][x])
  _(requires \forall PNode n; t->R[t->root][n] ==> n->key != x->key)
  _(ensures \forall PNode n; t->R[t->root][n] <==> n == x || \old(t->R[t->root][n]))
  _(ensures \unchanged(x->key) && \unchanged(x->value))
{
  PNode p, n;

  _(unwrap t)

  x->left = x->right = x->parent = NULL;

  p = t->root;

  _(ghost {
    t->abs = \lambda int k; k == x->key ? x->value : t->abs[k];
    t->\owns = t->\owns \union {x};
    t->R[x] = \lambda PNode n; n == x;
  })

  if (p == NULL) {
    t->root = x;
    _(wrap x)
    _(wrap t)
    return;
  }

  _(ghost t->R[t->root] = \lambda PNode n; n == x || \old(t->R[t->root][n]))
  _(assert doMark(t->root))
  _(assert t->R[t->root][x])

  while (1)
    _(writes t->\owns \diff {x}, &t->R)
    _(invariant (\forall \object p; p \in t->\owns ==> p == x || \wrapped(p)) && \mutable(x))
    _(invariant \unchanged(t->R[t->root]) && \unchanged(t->R[NULL]) && \unchanged(t->R[x]))
    _(invariant rb_istree(t))
    _(invariant rb_abs(t))
    _(invariant rb_lrclosed(t, p, x))
    _(invariant t->R[t->root][p])
    _(invariant p != x && !t->R[p->left][x] && !t->R[p->right][x])
    _(invariant \forall PNode n; t->R[t->root][n] ==> n == x || n->key != x->key)
  {
    if (x->key < p->key) {
      n = p->left;
      if (n == NULL) {
        _(unwrapping p) { p->left = x; }
        break;
      }
    } else if (x->key > p->key) {
      n = p->right;
      if (n == NULL) {
        _(unwrapping p) { p->right = x; }
        break;
      }
    } else {
      _(assert \false)
    }
    _(assert doMark(p) && doMark(n))
    _(ghost t->R[n] = \lambda PNode k; k == x || t->R[n][k])
    p = n;
  }

  x->parent = p;
  _(wrap x)
  _(wrap t)
}

void left_rotate(struct Tree *t, PNode x)
  _(requires t->R[t->root][x] && x->right != NULL)
  _(maintains \wrapped(t))
  _(writes t)
  _(ensures \unchanged(t->R[t->root]) && \unchanged(t->abs))
{
  PNode y;

  _(unwrap t)
  _(assert doMark(x)) _(unwrap x)
  y = x->right;
  _(assert doMark(y)) _(unwrap y)

  x->right = y->left;
  if (y->left != NULL)
      _(unwrapping y->left) y->left->parent = x;
  y->parent = x->parent;
  if (x->parent == NULL) {
    t->root = y;
  } else {
    _(assert doMark(x->parent))
    _(unwrapping x->parent)
     if (x->parent->left == x)
        x->parent->left = y;
     else
        x->parent->right = y;
  }

  y->left = x;
  x->parent = y;
  _(wrap x) _(wrap y)

  _(assert doMark(x->right))
  _(assert \forall PNode m; {:hint t->R[y][m]} {t->R[x->right][m]} t->R[x->right][m] ==> m->key > x->key)

  _(ghost {
    t->R[y] = t->R[x];
    t->R[x] = \lambda PNode m; m == x || t->R[x->left][m] || t->R[x->right][m];
  })

  _(wrap t)
}

void right_rotate(struct Tree *t, PNode y)
  _(requires t->R[t->root][y] && y->left != NULL)
  _(maintains \wrapped(t))
  _(writes t)
  _(ensures \unchanged(t->R[t->root]) && \unchanged(t->abs))
{
  PNode x;

  _(unwrap t)
  _(assert doMark(y)) _(unwrap y)
  x = y->left;
  _(assert doMark(x)) _(unwrap x)

  y->left = x->right;
  if (x->right != NULL)
      _(unwrapping x->right) x->right->parent = y;
  x->parent = y->parent;
  if (y->parent == NULL) t->root = x;
  else{
    _(assert doMark(y->parent))
    _(unwrapping y->parent)
     if (y->parent->left == y)
        y->parent->left = x;
     else
        y->parent->right = x;
  }

  x->right = y;
  y->parent = x;

  _(wrap x) _(wrap y)

  _(assert doMark(y->left))
  _(assert \forall PNode m; {:hint t->R[x][m]} {t->R[y->left][m]} t->R[y->left][m] ==> m->key < y->key)

  _(ghost {
    t->R[x] = t->R[y];
    t->R[y] = \lambda PNode m; m == y || t->R[y->left][m] || t->R[y->right][m];
  })

  _(wrap t)
}

#if 0
void rb_rotate(struct Tree *t, PNode x)
{
  PNode y;
  tree_insert(t, x);

  x->red = 1;
  while (x != t->root && x->parent->red) {
    if (x->parent == x->parent->parent->left) {
      y = x->parent->parent->right;
      if (y->red) {
        // case 1 - change the colors
        x->parent->red = 0;
        y->red = 0;
        x->parent->parent->red = 1;
        // Move x up the tree
        x = x->parent->parent;
      } else {
        if (x == x->parent->right) {
          // case 2 - move x up and rotate
          x = x->parent;
          left_rotate(t, x);
        }
        // case 3
        x->parent->red = 0;
        x->parent->parent->red = 1;
        right_rotate(t, x->parent->parent);
      }
    } else {
      y = x->parent->parent->left;
      if (y->red) {
        // case 1 - change the colors
        x->parent->red = 0;
        y->red = 0;
        x->parent->parent->red = 1;
        // Move x up the tree
        x = x->parent->parent;
      } else {
        if (x == x->parent->left) {
          // case 2 - move x up and rotate
          x = x->parent;
          right_rotate(t, x);
        }
        // case 3
        x->parent->red = 0;
        x->parent->parent->red = 1;
        left_rotate(t, x->parent->parent);
      }

    }
  }
  t->root->red = 0;
}
#endif

/*`
Verification of Tree#adm succeeded.
Verification of tree_init succeeded.
Verification of tree_find succeeded.
Verification of tree_lookup succeeded.
Verification of tree_insert succeeded.
Verification of left_rotate succeeded.
Verification of right_rotate succeeded.
`*/
