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
  _(invariant \forall Node *n; \mine(n) && n->nxt ==> \mine(n->nxt))
  _(invariant \forall Node *n; \mine(n) ==> val[n->data])
  _(invariant \forall int v; val[v] ==> \mine(find[v]) && find[v]->data == v)
/*{moreList}*/
  _(ghost \natural idx[Node *])
  _(invariant head ==> idx[head] == 0)
  _(invariant \forall Node *n, *m; \mine(n) && \mine(m) ==>
      head  
      && (idx[n] == 0 ==> n==head)
      && (n->nxt ==> idx[n->nxt] == idx[n] + 1)
      && (idx[m] == idx[n] + 1 ==> m == n->nxt)
      && (idx[m] > idx[n] ==> n->nxt)
  )
/*{noMoreList}*/
} List;

void listInit(List *l)
	_(requires \extent_mutable(l))
	_(writes \extent(l))
	_(ensures \wrapped(l) && l->val == \lambda int k; \false)
{
  l->head = NULL;
  _(ghost {
    l->\owns = {};
    l->val = (\lambda int k; \false);
	_(ghost l->find = (\lambda int k; (Node *) NULL))
  })
  _(wrap l)
}
/*{add}*/
int add(List *l, int k)
  _(requires \wrapped(l))
  _(ensures \wrapped(l))
  _(ensures \result != 0 ==> l->val == \old(l->val))
  _(ensures \result == 0 ==>
       (\forall int p; l->val[p] <==> (\old(l->val)[p] || p == k)))
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
      l->val = (\lambda int z; z == k || l->val[z]);
	  l->find = (\lambda int z; z == k ? n : l->find[z]);
	  l->idx = (\lambda Node *m; m == n ? 0 : l->idx[m] + 1);
	  l->\owns += n; 
    })
  }
  return 0;
}
/*{member}*/
int member(List *l, int k)
  _(requires \wrapped(l))
  // partial specification, ==> instead of <==>
  _(ensures \result == l->val[k])
{
  Node *n;
  _(assert \inv(l))
  for (n = l->head; n; n = n->nxt) 
    _(invariant n ==> n \in l->\owns && n \in \domain(l))
    _(invariant  \forall Node *m; m \in l->\owns && m->data == k 
      ==> m==n || (n && l->idx[m] > l->idx[n]))
  {
	if (n->data == k) return 1;
  }
  _(assert l->val[k] ==> l->find[k] \in l->\owns)
  return 0;
}
/*{out}*/
/*`
Verification of List#adm succeeded.
Verification of listInit succeeded.
Verification of add succeeded.
Verification of member succeeded.
`*/
