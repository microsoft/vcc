#include <vcc.h>
#include <limits.h>

#define FALSE 0
#define TRUE !0
typedef unsigned UINT;
typedef int bool;

#define approvesClientFields(a) \approves(a, ticket) && \approves(a, flag) && \approves(a, checked) \
    && \approves(a, max) && \approves(a, waiting)

typedef _(claimable) struct Client {
  volatile UINT ticket;                             // chosen ticket
  volatile bool flag;                               // true when choosing a ticket
  _(ghost volatile UINT checked)                    // minimum index of unchecked clients
  _(ghost volatile UINT max)                        // maximum ticket read from other clients
  _(ghost volatile bool waiting)                    // true when waiting for another client's flag to be lowered
  _(ghost \object bakery)                           // the bakery this client is in
  _(invariant \on_unwrap(\this, \inv(bakery)))      // don't destroy the client while the bakery is running
  _(invariant approvesClientFields(\this->\owner))  // only the owner can "change" the fields
  _(invariant approvesClientFields(bakery))         // changes to the fields require checking the bakery invariants
} Client;

#define thinking(s, i)     (!in_bakery(s, i) && !in_doorway(s, i))
#define in_bakery(s, i)    (s->c[i].ticket > 0 && !s->c[i].flag)
#define in_doorway(s, i)   (s->c[i].flag)
#define serving(s, i)      (in_bakery(s, i) && s->c[i].checked==s->N)
#define ticket_order(ti, i, tj, j) (ti < tj || (ti == tj && i<=j))
#define before(s, i, j)    (in_bakery(s, i) && \
                 (ticket_order(s->c[i].ticket, i, s->c[j].ticket, j) || thinking(s, j) \
                  || (in_doorway(s, j) && (s->c[j].checked <= i || s->c[j].max >= s->c[i].ticket ))))

typedef _(claimable, dynamic_owns) struct Bakery {
  UINT N;               // number of clients
  Client *c;            // pointer to array of clients
  _(invariant \forall UINT i; i < N ==> (&c[i])->\closed && (c[i].bakery==\this) && (c[i].checked<=N))
  // a client in the checking phase has priority over all the clients he's checked
  _(invariant \forall UINT i, j; i < N && j < c[i].checked && in_bakery(\this, i) ==> before(\this, i, j))
  // once i has checked a flag of a client, if the client is choosing again, he comes after i
  _(invariant \forall UINT i; i < N && c[i].checked < N && in_bakery(\this, i) && !c[i].waiting
                  && in_doorway(\this, c[i].checked) ==> before(\this, i, c[i].checked))
} Bakery;

#define cl (&server->c[idx])  // defined rather than declared as a local so we can use it in the contract (replace with let someday)
#define atomicCl(arg) _(atomic sc, server, cl) { arg; _(bump_volatile_version cl) }      // atomic operation on cl
#define atomicCc(arg) _(atomic sc, server, cl, cc) { arg; _(bump_volatile_version cl) }  // atomic operation on cl and cc
#define cl_coupling_invariant \
  _(writes cl) \
  _(invariant \wrapped(cl) && cl->checked == checked &&  cl->ticket == max && !cl->flag && cl->ticket > 0)

void BakeryAcquire(Bakery *server, UINT idx _(ghost \claim sc))
  _(requires \wrapped(sc) && \claims(sc, server->\closed))   // need evidence that nobody will destroy the server
  _(requires idx < server->N && \wrapped(cl))                // must own a client of the server
  _(requires thinking(server, idx))                          // client must be thinking
  _(writes cl)
  _(ensures serving(server, idx))                            // get me some service!
{
  UINT max = 0;
  UINT checked;
  UINT N = server->N;
  bool flag;

  // start choosing
  atomicCl(cl->flag = TRUE;
    _(ghost cl->max = 0)
    _(ghost cl->checked = 0))

  // calculate the maximum of the outstanding tickets (asynchronously)
  for(checked = 0; checked < N; checked++)
    _(invariant \wrapped(cl) && max == cl->max && checked == cl->checked && cl->flag && !cl->ticket)
    _(writes cl)
  {
    UINT t;
    Client *cc = &server->c[checked];
    atomicCc(t = cc->ticket;
      _(ghost if (t >= max) cl->max = t)
      _(ghost cl->checked++))
    if (t > max) max = t;
  }

  _(assume max < UINT_MAX); // unbounded tickets - hope we don't overflow!

  // make my ticket bigger than the biggest ticket I found
  max++;
  atomicCl(cl->ticket = max)

  // announce that I'm done choosing
  atomicCl(cl->flag = FALSE;
    _(ghost cl->waiting = \true)
    _(ghost cl->checked = 0))

  _(requires \wrapped(sc) && \claims(sc, server->\closed))
  _(requires idx < server->N && \wrapped(cl))
  _(requires N == server->N)
  _(requires \wrapped(cl) && cl->checked == 0 &&  cl->ticket == max && !cl->flag && cl->ticket > 0)
  _(writes cl)
  _(ensures serving(server, idx))
  {

    // wait until it's my turn - check that nobody is ahead of me
    for (checked = 0; checked < N; checked++)
      cl_coupling_invariant
      _(invariant checked <= N)
    {
      Client *cc = &server->c[checked];  // next client to check
      UINT other_ticket;          // his ticket
  
      // wait for his flag to be down
      while (1)
          cl_coupling_invariant
      {
        _(atomic sc, server, cl, cc) {
          flag = cc->flag;
          if (!flag) {
            _(ghost cl->waiting = \false)
            _(bump_volatile_version cl)
          }
        }
        if (!flag) break;
      }
  
      // wait until his ticket is 0 or is bigger than mine
      while (1)
        _(invariant !cl->waiting)
        cl_coupling_invariant
      {
        _(atomic sc, server, cl, cc) {
          other_ticket = cc->ticket;
          _(ghost if (other_ticket == 0 || ticket_order(max, idx, other_ticket, checked)) {
              cl->checked++;
              cl->waiting = \true;
              _(bump_volatile_version cl) })
  
        }
        if (other_ticket == 0 || ticket_order(max, idx, other_ticket, checked)) break;
      }
    }
  }
}

void BakeryRelease(Bakery *server, UINT idx _(ghost \claim sc))
  _(requires \wrapped(sc) && \claims(sc, server->\closed))
  _(requires idx < server->N && \wrapped(cl))
  _(requires serving(server, idx))
  _(writes cl)
  _(ensures thinking(server, idx))
{
  atomicCl(cl->ticket = 0)
}

/*`
Verification of Client#adm succeeded.
Verification of Bakery#adm succeeded.
Verification of BakeryAcquire succeeded.
Verification of BakeryRelease succeeded.
Verification of BakeryAcquire#block#0 succeeded.
`*/
