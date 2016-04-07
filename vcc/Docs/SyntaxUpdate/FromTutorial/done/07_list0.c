#include <vcc.h>
#include <stdlib.h>

/*{types}*/
struct Node {
  struct Node *next;
  int data;
};

_(dynamic_owns) struct List {
  struct Node *head;
  _(ghost  bool val[int];)
  _(invariant head != NULL ==> \mine(head))
  _(invariant \forall struct Node *n;
                {n->next \in \this->\owns}
                \mine(n) ==> n->next == NULL || \mine(n->next))
  _(invariant \forall struct Node *n; 
                {n \in \this->\owns}
                \mine(n) ==> val[n->data])
};
/*{init}*/
struct List *mklist()
  _(ensures \result != NULL ==> \wrapped(\result) && \result->val == \lambda int k; \false)
{
  struct List *l = malloc(sizeof(*l));
  if (l == NULL) return l;
  l->head = NULL;
  _(ghost {
    l->\owns = {};
    l->val = (\lambda int k; \false);
  })
  _(wrap l)
  return l;
}
/*{add}*/
int add(struct List *l, int k)
  _(requires \wrapped(l))
  _(ensures \wrapped(l))
  _(ensures \result != 0 ==> l->val == \old(l->val))
  _(ensures \result == 0 ==>
       \forall int p; l->val[p] == (\old(l->val)[p] || p == k))
  _(writes l)
/*{endspec}*/
{
  struct Node *n = malloc(sizeof(*n));
  if (n == NULL) return -1;
  _(unwrapping l) {
    n->next = l->head;
    n->data = k;
    _(wrap n)
    l->head = n;
    _(ghost {
      l->\owns = l->\owns \union {n};
      l->val = (\lambda int z; z == k || l->val[z]);
    })
  }
  return 0;
}
/*{member}*/
int member(struct List *l, int k)
  _(requires \wrapped(l))
  // partial specification, ==> instead of <==>
  _(ensures \result != 0 ==> l->val[k])
{
  struct Node *n;

  n = l->head;

  if (n == NULL)
    return 0;

  for (;;)
    _(invariant n \in l->\owns)
  {
    if (n->data == k)
      return 1;
    n = n->next;
    if (n == NULL)
      return 0;
  }
}
/*{out}*/
/*`
Verification of List#adm succeeded.
Verification of mklist succeeded.
Verification of add succeeded.
Verification of member succeeded.
`*/
