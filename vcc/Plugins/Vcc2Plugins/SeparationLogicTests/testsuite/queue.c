#include "vcc2.h"

// --- Sequence ---
typedef struct node {
    struct node *next;
    void *data;
} Node, * PNode;

typedef struct queue {
    struct node *head;
    struct node *tail;
} Queue, * PQueue;

spec (int value_queue(PNode, PNode);)
spec (int value_node(PNode, void*);)

spec (int seq_empty();)
spec (int seq_cons(void*, int);)
spec (int seq_append(int, int);)
//spec int seq_singleton(void*);
//spec int seq_length(int);

int blob(char*, void*, int);
//spec int mblock(void *, int);


spec (int list(PNode a, PNode e, int xs)
  ensures(result == 
   (((a==e) ==> (xs==seq_empty())) && 
   ((a!=e) ==> exists(PNode _d; PQueue _ys; void* _b; xs==seq_cons(_d, _ys) && 
   blob("node", a, value_node(_d, _b)) && list(_b, e, _ys))
   /*&& mblock(a,sizeof(Node))*/ )));)

/*
| | list(a,e,vs) * blob(type,b,v) * S |- | list(a,b,ys)	* S'
if
| | blob(type,b,v) * S |- seq_app(vs,_ws) = ys | list(e,b,_ws) * S'
*/


spec (int ValidQueue(PQueue q, int xs)
  ensures (result == 
  exists(PNode _h, _t, _q; void* _d, _y; int _ys;
    blob("queue", q, value_queue(_h, _t)) &&
    blob("node", _t, value_node(_q, _d)) &&
    ((_h==_t) ==> (xs==seq_empty())) && 
    ((_h!=_t) ==> (list(_h, _t, seq_cons(_y,_ys)) && 
     seq_append(_ys, seq_cons(_d, seq_empty())) == xs))));)
 

// --- struct queue ---

int is_empty(struct queue *q)
  requires (exists(int xs; ValidQueue(q, xs)))
  ensures (exists(int xs; ValidQueue(q, xs) && result == (xs==seq_empty())))
{
  struct node* hd = q->head;
  struct node* tl = q->tail;
  return hd==tl;
}

struct node* dequeue_node(struct queue *q)
  requires (exists(int ys; void* x; ValidQueue(q, seq_cons(x,ys))))
  ensures(exists(int ys; void* x; PNode n; ValidQueue(q, ys) && blob("struct node",result,value_node(n,x)))) 
;
/*{
  struct node *nod;
  struct node* t;
  nod = q->head;
  t = nod->next;
  q->head = t;
  return nod;
}
*/
void free_node(struct node * n) requires(exists(struct node * m; void * x; blob("struct node",n,value_node(m,x))));
/*
void dequeue(struct queue *q)
  requires (exists(int ys; void* x; ValidQueue(q, seq_cons(x,ys))))
  ensures(exists(int ys; ValidQueue(q, ys))) {
  struct node * n;
  n = dequeue_node(q);
  free_node(n);
  return;
}
*/
/*
void *front(struct queue *q)
  requires (exists(int ys; void* x; ValidQueue(q, seq_cons(x,ys))))
  ensures (exists(int ys; void* x; ValidQueue(q, seq_cons(x,ys)) && result == x)) {
  void * v;
  PNode t = q->head;
  t = t->next;
  v = t->data;	  
  return v;
}
*/
struct queue * alloc_queue () ensures (exists(PNode x,z; blob("struct queue",result, value_queue(x,z)))) ;
struct node * alloc_node () ensures (exists(void* x; PNode z; blob("struct node",result, value_node(z,x)))) ;


struct queue *make_queue()
  ensures (ValidQueue(result, seq_empty())) {
  struct node *n;
  struct queue *q;

//  q = alloc(struct queue);
  q = alloc_queue();
  n = alloc_node();

  q->head = n;
  q->tail = n;
  return q;
}



void enqueue_node(struct queue *q, struct node * nod)
  requires (exists(int xs; void* v; struct node * n; ValidQueue(q, xs) && blob("struct node",nod,value_node(n,v))))
  ensures (exists(int xs, ys; void* v; ValidQueue(q, ys) && ys == seq_append(xs, seq_cons(v,seq_empty())))) {
  struct node * t = q->tail;
  t->next = nod;
  q->tail = nod;
} 


void enqueue(struct queue *q, void *t)
  requires (exists(int xs; ValidQueue(q, xs)))
  ensures (exists(int xs, ys; ValidQueue(q, ys) && ys == seq_append(xs, seq_cons(t,seq_empty()))))

{ struct node *n;
  n = alloc_node();
  n->data = t;

  enqueue_node(q, n);
} 

/*
node* list_find_nth(struct node *l, int k)
  requires (exists(int xs; Pnode e; 
					list(l, e, xs) && k >=0 && seq_length(xs) > k))
  ensures (exists(int xs, ys, zs; 
				  Pnode t,e;
				  void * v;
				  list(l, result,ys) && 
                          blob("node", result, value_node(t,v)) &&
                          list(t,e,zs) && 
                          seq_append(ys,seq_cons(v,zs)) == xs &&
                          seq_length(ys) == k+1)) {
  if(k==0) {
    return l;	
  } else {
    list_find_nth(l->next, k-1);
  }
}



void remove_nth(struct queue *q, int k)
  requires (exists(int xs; ValidQueue(q, xs) && k >=0 && seq_length(xs) > k))
  ensures (  exists(int xs, ys; void * v;
						ValidQueue(q, seq_append(ys,zs)) && 
						seq_append(ys,seq_cons(v,zs)) == xs &&
                        seq_length(ys) == k)) )

{
  struct node *p;
  struct node *temp;

  p = list_find_nth(q->head, k)  

  if(p->next == q->tail) {
    q->tail = p;
    free(p->next);
  } else {
    temp = p->next;
    p->next = p->next->next;
    free(temp);
  }
}
*/

/*
void my_transfer(struct queue * from, struct queue *to)
  requires(exists(int xs, ys; void* x; ValidQueue(from, seq_cons(x,xs)) &&
                                       ValidQueue(to, ys)))
  ensures(exists(int xs, ys; void* x; ValidQueue(from, xs) &&
                                      ValidQueue(to, seq_append(ys,seq_cons(x,seq_empty()))))) {

  struct node * t = dequeue_node(from);
  enqueue_node(to, t);
}
*/
/*

//  Could follow the subsequent two with vcc2 annotations, so made up my own.
void freeq(PQueue q)
  requires exists(int xs; ValidQueue(q,xs)) {
  PNode p = q->head;
  while (p!=q->tail) {
	  t = p->next;
	  free(p);
	  p = t;
  }
  free(p);
  free(q);
}
  


void main1(void *t, void *u, void *v)
{
  struct queue *q0;
  struct queue *q1;
  void *w;

  q1 = make_queue();
  q0 = make_queue();

  assert(q0 != q1);

  enqueue(q0, t);
  enqueue(q0, u);
  enqueue(q1, v);

  w = front(q0);
  assert (w == t);

  dequeue(q0);
  
  w = front(q0);
  assert (w == u);

  assert (exists(int xs; ValidQueue(q0,xs) && seq_length(xs) == 1));
  assert (exists(int xs; ValidQueue(q1,xs) && seq_length(xs) == 1));
  freeq(q0);
  freeq(q1);
}
*/
/*
void main2(struct queue* q0, struct queue *q1, void *t, void *u, void *v)
  requires(packed(q0) && seq_length(AbstractValue(q0)) == 0)
  requires(packed(q1) && seq_length(AbstractValue(q1)) < 100)
  requires(q0 != q1)
  ensures (seq_length(AbstractValue(q0)) == 1);
  ensures (seq_length(old(AbstractValue(q1))) + 1 == seq_length(AbstractValue(q1)));
  ensures (seq_length(AbstractValue(q1)) == seq_length(old(AbstractValue(q1))) + 1); }

{
  void *w;

  enqueue(q0, t);
  enqueue(q0, u);

  enqueue(q1, v);
  assert (seq_length(AbstractValue(q0)) == 2);

  w = front(q0);
  assert (w == t);
 

  dequeue(q0);

  w = front(q0);
  assert (w == u);

}
*/
