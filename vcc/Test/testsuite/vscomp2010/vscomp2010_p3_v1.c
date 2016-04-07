#include <vcc.h> 

typedef _(dynamic_owns) struct List {
  int head;
  struct List *tail;
  unsigned length;
  _(ghost int vals[unsigned])
  _(invariant vals == \lambda unsigned i; i < length ? (i == 0 ? head : tail->vals[i - 1]) : 0)
  _(invariant length == 0 || (\mine(tail) && length == tail->length + 1))
} List, *PList;

unsigned find(PList l)
  _(requires \wrapped(l))
  _(ensures \result <= l->length)
  _(ensures \result < l->length ==> l->vals[\result] == 0)
  _(ensures \forall unsigned i; i < \result ==> l->vals[i] != 0)
{
  PList p;
  for (p = l; p->length != 0; p = p->tail)
    _(invariant p->length <= l->length)
    _(invariant p \in \domain(l))
    _(invariant p->vals == \lambda unsigned j; j < p->length ? l->vals[l->length - p->length + j] : 0)
    _(invariant \forall unsigned j; j < l->length - p->length ==> l->vals[j] != 0)
  {
    _(assert \forall unsigned j; j < p->tail->length ==> p->tail->vals[j] == p->vals[j + 1])
    _(assert p->head == p->vals[0])
    if (p->head == 0) {
      break;
    }
  }
  return l->length - p->length;
}

/*`
Verification of List#adm succeeded.
Verification of find succeeded.
`*/
