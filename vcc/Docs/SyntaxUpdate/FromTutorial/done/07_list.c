#include <vcc.h>
#include <stdlib.h>

struct Node {
  struct Node *next;
  int data;
};

/*{type}*/
_(dynamic_owns) struct List {
  _(ghost  bool val[int];)
  struct Node *head;
  _(ghost  bool followers[struct Node *][int];)
  _(invariant val == followers[head])
  _(invariant head != NULL ==> \mine(head))
  _(invariant followers[NULL] == \lambda int k; \false)
  _(invariant \forall struct Node *n;
                {n->next \in \this->\owns}
                \mine(n) ==> n->next == NULL || \mine(n->next))
  _(invariant \forall struct Node *n; 
                {n \in \this->\owns}
                \mine(n) ==> 
                   \forall int e; 
                      followers[n][e] <==> 
                      followers[n->next][e] || e == n->data)
};


/*{init}*/
struct List *mklist()
  _(ensures \result != NULL ==> \wrapped(\result) && \result->val == \lambda int k; \false)
{
  struct List *l = malloc(sizeof(*l));
  if (l == NULL) return NULL;
  l->head = NULL;
  _(ghost {
    l->\owns =  {};
    l->followers = \lambda struct Node *n; int k; \false;
    l->val = l->followers[l->head];
  })
  _(wrap l)
  return l;
}

int add(struct List *l, int k)
  _(requires \wrapped(l))
  _(ensures \wrapped(l))
  _(ensures \result == 0 ==> l->val == \lambda int p; \old(l->val)[p] || p == k)
  _(ensures \result != 0 ==> l->val == \old(l->val))
  _(writes l)
{
  struct Node *n = malloc(sizeof(*n));
  if (n == NULL) return -1;
  _(unwrapping l) {
    n->next = l->head;
    n->data = k;
    l->head = n;
    _(wrap n)
    _(ghost {
      l->\owns = l->\owns \union {n}; /*{specupdate}*/
      l->followers[n] = 
        (\lambda int z; l->followers[n->next][z] || z == k);
      l->val = l->followers[n]; /*{updateend}*/
    })
  }
  return 0;
}

/*{member}*/
int member(struct List *l, int k)
  _(requires \wrapped(l))
  _(ensures \result != 0 <==> l->val[k])/*{endspec}*/
{
  struct Node *n;

  for (n = l->head; n; n = n->next)
    _(invariant n != NULL ==> n \in l->\owns)
    _(invariant l->val[k] <==> l->followers[n][k])
  {
    if (n->data == k)
      return 1;
  }
  return 0;
}


/*{out}*/
/*`
Verification of List#adm succeeded.
Verification of mklist succeeded.
Verification of add succeeded.
Verification of member succeeded.
`*/
