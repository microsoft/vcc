#include <vcc.h>

struct Node {
  struct Node *next;
  int data;
};

_(dynamic_owns) struct List {
  struct Node *head;
  _(ghost struct Node *seq[unsigned])         // sequence of nodes in the list
  _(ghost unsigned idx[struct Node *])        // indices of the nodes in the list
  _(ghost bool followers[struct Node *][int])
  _(ghost unsigned length_acc[struct Node *])
  _(ghost unsigned length)
  _(invariant head ==> \mine(head))
  _(invariant followers[0] == \lambda int k; \false)
  _(invariant \forall struct Node *n; \mine(n) ==> !n->next || \mine(n->next))
  _(invariant \forall struct Node *n; \mine(n) ==>
    \forall int e; followers[n][e] <==> followers[n->next][e] || e == n->data)
  _(invariant length_acc[0] == 0 && \forall struct Node *n; \mine(n) ==> length_acc[n] == length_acc[n->next] + 1)
  _(invariant \forall struct Node *n; \mine(n) ==> seq[idx[n]] == n)
  _(invariant \forall unsigned i; i < length ==> \mine(seq[i]))
  _(invariant \forall unsigned i; {:hint \mine(seq[i])} i < length ==> seq[i]->next == seq[i + 1])
  _(invariant idx[head] == 0 && (head ==> seq[0] == head))
  _(invariant \forall struct Node *n; \mine(n) && n->next ==> idx[n->next] == idx[n] + 1)
  _(invariant length == length_acc[head])
};

unsigned find(struct List *l)
  _(requires \wrapped(l))
  _(ensures \result <= l->length && \forall unsigned i; i < \result ==> l->seq[i]->data != 0)
  _(ensures \result < l->length ==> l->seq[\result]->data == 0)
{
  struct Node *n;
  unsigned i;

  for (n = l->head, i = 0; n; n = n->next, i++)
    _(invariant n ==> n \in l->\owns)
    _(invariant l->length - i == l->length_acc[n])
    _(invariant n ==> n == l->seq[i])
    _(invariant \forall unsigned j; j < i ==> l->seq[j]->data != 0)
  {
    if (n->data == 0) {
      break;
    }
  }

  return i;
}

/*`
Verification of List#adm succeeded.
Verification of find succeeded.
`*/
