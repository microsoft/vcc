#include <vcc.h>

#define bool int
#define true 1
#define false 0
#define NULL 0

typedef void *PVOID;


typedef struct Node {
    struct Node *next;

    _(invariant \depends(\this->\owner, \this))
} *PNODE;

_(atomic_inline) PNODE InterlockedCompareExchangePointer(volatile PNODE *Destination, PNODE Exchange, PNODE Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}


typedef struct Node *PNode;
_(volatile_owns) struct Stack {
    volatile PNode hd;

    _(invariant \this->hd == NULL <==> \this->\owns == {})
    _(invariant \this->hd != NULL <==> \this->\owns != {})
    _(invariant \this->hd != NULL <==>\this->hd \in \this->\owns)
    _(invariant \this->hd != NULL ==>
                  (\forall struct Node *x; //{x \in \this->\owns}
                    x \in \this->\owns ==> /* x->\valid && */ x->next != \this->hd)
               && (\forall struct Node *x; //{x->next \in \this->\owns}
                    x \in \this->\owns && x->next != NULL ==> x->next \in \this->\owns)
               && \forall struct Node *x; struct Node *y; {x->next, y->next}
                    x \in \this->\owns && y \in \this->\owns && x->next == y->next ==> x == y)
};

bool push(struct Node *n, struct Stack *s _(ghost \claim c))
    _(always c, s->\closed)
    _(requires n->\owns == {})
    _(writes \extent(n))
{
    while (true)
        _(invariant \mutable(n) && n->\owns == {})
    {
        struct Node *h;
        bool ok;

        _(atomic c, s) {
          h = s->hd;
        }
        n->next = h;

        ok = false;
        _(atomic c, s) {
            _(wrap n)
	    _(begin_update)
        ok = (InterlockedCompareExchangePointer(&s->hd, n, h) == h);
        if (ok) {
                _(assert !(n \in s->\owns))
                _(ghost s->\owns += n);
            }
	}

        if (ok)
            return true;

	_(unwrap n)
    }
}

#ifdef NOTYET
bool pop(struct Node **n, struct Stack *s)
    _(invariant s->\closed && s->\valid)
//    requires (mutable(s->hd))
    _(requires \mutable(*n))
    _(ensures (s->\owns == {}) ==> \result == \false)
    _(ensures s->hd \in s->\owns ==> \result == \true)
    _(writes *n, s->hd)
{
    _(assume s->hd != NULL)
    _(assume s->\owns != {})

    while (true)
    _(invariant /*mutable(s->hd) && */\mutable(*n) && s->\owns != {})
    {
        struct Node *h;
        bool ok;

        h = volatile(s->hd, s->\owns != {});

        assume false;

/*
        if (h == NULL)
        {
            assert (owns(s) == set_empty());
            return false;
        }
        else
*/
//        {

            _(assert s->\owns != {})
            ok = false;
            _(atomic s, s->\owns != {}) {
                // InterlockedCompareExchange(&s->hd, h, h->next)
                if (s->hd == h) {
                    s->hd = h->next;
                    ok = true;
                    _(ghost s->\owns -= h);
                    _(unwrap h)
                    _(assert !(h \in s->\owns))
                    *n = h;
                }
            }

            if (ok)
                return true;

//        }
    }
}
#endif
/*`
Verification of Node#adm succeeded.
Verification of Stack#adm succeeded.
Verification of push succeeded.
`*/
