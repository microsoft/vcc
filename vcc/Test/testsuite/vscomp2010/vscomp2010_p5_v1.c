#include <vcc.h>
#include <stdlib.h>

#define wrapped_dom(a) (\wrapped(a) && (a) \in \domain(a))

_(ghost typedef void *intMap[\integer])

typedef struct List {
  void *head;
  struct List *tail;
  unsigned length;
  _(ghost intMap val)
  _(invariant \malloc_root(\this))
  _(invariant val == \lambda \integer i; 0 <= i && i < length ? (i == 0 ? head : tail->val[i - 1]) : 0)
  _(invariant length == 0 || length == tail->length + 1)
  _(invariant length != 0 <==> \mine(tail))
} List, *PList;

PList ListNew()
  _(ensures wrapped_dom(\result) && \fresh(\result))
  _(ensures \result->length == 0)
{
  PList l = malloc(sizeof(List));
  _(assume l)
  l->tail = NULL;
  l->length = 0;
  _(ghost l->val = \lambda \integer i; (void*)0)
  _(wrap l)
  return l;
}

PList Cons(List *l, void *d)
  _(requires \wrapped(l))
  _(requires l->length < UINT_MAX)
  _(writes l)
  _(ensures \wrapped(\result) && \fresh(\result))
  _(ensures \result->length == \old(l->length) + 1)
  _(ensures \result->val == \old(\lambda \integer i; i == 0 ? d : l->val[i - 1]))
{
  PList r = malloc(sizeof(List));
  _(assume r)
  r->head = d;
  r->tail = l;
  r->length =  l->length + 1;
  _(ghost r->val = \lambda \integer i; i == 0 ? d : l->val[i - 1])
  _(wrap r)
  return r;
}

PList Concat(PList l, PList end)
  _(requires \wrapped(l) && \wrapped(end) && l != end)
  _(requires l->length + end->length <= UINT_MAX)
  _(writes l, end)
  _(ensures wrapped_dom(\result) && (\fresh(\result) || (\old(l->length == 0) && \result == end)))
  _(ensures \result->length == \old(l->length + end->length))
  _(ensures \result->val == \old(\lambda \integer i; i < l->length ? l->val[i] : end->val[i - l->length]))
{
  _(unwrap l)
  if (l->length == 0) {
    free(l);
    return end;
  } else {
    PList c = Concat(l->tail, end);
    c = Cons(c, l->head);
    free(l);
    return c;
  }
}

PList Reverse(PList l)
  _(requires \wrapped(l))
  _(writes l)
  _(ensures wrapped_dom(\result) && (\fresh(\result) || (\result == l && \old(\result \in \domain(l)))))
  _(ensures \result->val == \old(\lambda \integer i; l->val[(\integer) l->length - 1 - i]))
  _(ensures \result->length == \old(l->length))
{
  PList r;
  if (l->length == 0) {
    return l;
  } else {
    PList e, f;
    _(unwrap l)
    r = Reverse(l->tail);
    e = ListNew();
    f = Cons(e, l->head);
    r = Concat(r, f);
    return r;
  }
}

PList Tail(PList l)
  _(requires \wrapped(l) && l->length != 0)
  _(writes l)
  _(ensures \wrapped(\result) && \fresh(\result) && \old(\result \in \domain(l)))
  _(ensures \result->length == \old(l->length) - 1)
  _(ensures \result->val == \old(\lambda \integer i; i == -1 ? 0 : l->val[i + 1]))
{
  _(unwrap l)
  PList r = l->tail;
  free(l);
  return r;
}

typedef struct Queue {
  PList front, rear;
  _(invariant \malloc_root(\this))
  _(invariant front != rear && \mine(front) && \mine(rear))
  _(invariant rear->length <= front->length)
  _(invariant front->length + rear->length <= UINT_MAX)
} Queue, *PQueue;

_(logic \integer QLen(Queue *q) = (q->front->length + q->rear->length))
_(ghost _(pure) intMap qv(PList front, PList rear)
  _(reads \universe())
  _(returns \lambda \integer i; i < front->length
    ? front->val[i]
    : rear->val[_(\integer) rear->length + front->length - 1 - i]))
_(logic intMap QVal(Queue *q) = qv(q->front, q->rear))

Queue *QueueNew()
  _(ensures \fresh(\result) && \wrapped(\result))
  _(ensures QVal(\result) == \lambda \integer i; (void*)0)
{
  Queue *r = malloc(sizeof(Queue));
  _(assume r)
  r->front = ListNew();
  r->rear = ListNew();
  _(wrap r)
  return r;
}

Queue *QueueBuild(PList front, PList rear)
  _(requires front->length + rear->length <= UINT_MAX)
  _(requires \wrapped(front) && \wrapped(rear) && front != rear)
  _(writes front, rear)
  _(ensures wrapped_dom(\result) && \fresh(\result))
  _(ensures QLen(\result) == \old(front->length + rear->length))
  _(ensures QVal(\result) == \old(qv(front, rear)))
{
  Queue *r = malloc(sizeof(Queue));
  _(assume r)
  if (rear->length <= front->length) {
    r->front = front;
    r->rear = rear;
  } else {
    PList f;
    f = Reverse(rear);
    r->front = Concat(front, f);
    r->rear = ListNew();
  }
  _(wrap r)
  return r;
}

void *QueueFront(Queue *q)
  _(requires \wrapped(q) && QLen(q) > 0)
  _(ensures \result == QVal(q)[0])
{
  _(assert q->front \in \domain(q))
  return q->front->head;
}

Queue *QueueTail(Queue *q)
  _(requires \wrapped(q) && QLen(q) > 0)
  _(writes q)
  _(ensures \fresh(\result) && \wrapped(\result))
  _(ensures QLen(\result) == \old(QLen(q) - 1))
  _(ensures QVal(\result) == \old(\lambda \integer i; (i == -1 ? 0 : QVal(q)[i + 1])))
{
  _(unwrap q)
  _(assert wrapped_dom(q->front) && wrapped_dom(q->rear))
  PList t = Tail(q->front);
  Queue *r = QueueBuild(t, q->rear);
  free(q);
  return r;
}

Queue *Enqueue(Queue *q, void *item)
  _(requires \wrapped(q))
  _(requires QLen(q) + 1 <= UINT_MAX)
  _(writes q)
  _(ensures \fresh(\result) && \wrapped(\result))
  _(ensures QLen(\result) == \old(QLen(q) + 1))
  _(ensures QVal(\result) == \old(\lambda \integer i; i == QLen(q) ? item : QVal(q)[i]))
{
  Queue *r;
  _(unwrap q)
  _(assert wrapped_dom(q->front) && wrapped_dom(q->rear))
  q->rear = Cons(q->rear, item);
  r = QueueBuild(q->front, q->rear);

  return r;
}

/*`
Verification of List#adm succeeded.
Verification of Queue#adm succeeded.
Verification of ListNew succeeded.
Verification of Cons succeeded.
Verification of Concat succeeded.
Verification of Reverse succeeded.
Verification of Tail succeeded.
Verification of QueueNew succeeded.
Verification of QueueBuild succeeded.
Verification of QueueFront succeeded.
Verification of QueueTail succeeded.
Verification of Enqueue succeeded.
`*/
