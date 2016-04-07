#include <vcc.h>
#include <stdlib.h>

/*{types}*/
typedef struct Node {
  struct Node *nxt;
  int data;
} Node;

typedef _(dynamic_owns) struct List {
  Node *head;
  _(ghost \bool val[int];)
  _(ghost Node *find[int];)
  _(invariant head != NULL ==> \mine(head))
  _(invariant \forall Node *n; \mine(n) && n->nxt 
     ==> \mine(n->nxt))
  _(invariant \forall Node *n; \mine(n) 
    ==> val[n->data])
  _(invariant \forall int v; val[v] 
    ==> \mine(find[v]) && find[v]->data == v)
} List;
/*{init}*/
List *mklist()
  _(ensures \result != NULL ==> 
      \wrapped(\result) 
      && \result->val == \lambda int k; \false)
{
  List *l = malloc(sizeof(*l));
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
int add(List *l, int k)
  _(requires \wrapped(l))
  _(ensures \wrapped(l))
  _(ensures \result != 0 ==> l->val == \old(l->val))
  _(ensures \result == 0 ==> (\forall int p; l->val[p] 
       <==> (\old(l->val)[p] || p == k)))
  _(writes l)
/*{endspec}*/
{
  Node *n = malloc(sizeof(*n));
  if (n == NULL) return -1;
  _(unwrapping l) {
    n->nxt = l->head;
    n->data = k;
    _(wrap n)
    l->head = n;
    _(ghost {
      l->\owns += n;
	  l->val = (\lambda int z; z == k || l->val[z]);
	  l->find = (\lambda int z; z == k ? n : l->find[z]);
    })
  }
  return 0;
}
/*{out}*/
/*`
Verification of List#adm succeeded.
Verification of mklist succeeded.
Verification of add succeeded.
`*/
