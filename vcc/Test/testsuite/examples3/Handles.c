#include <vcc.h>
#include <stdlib.h>

struct X { int y; };

struct Data {
  int dummy;
   _(ghost volatile \bool handles[struct Handle*];) 
  _(invariant \on_unwrap(\this, \forall struct Handle *h; ! handles[h]))
  _(invariant \approves(\this->\owner, handles))
  //invariant(forall(struct Handle *h; closed(h) && h->data == this ==> handles[h]))
  _(invariant \forall struct Handle *h; \old(handles[h]) && !handles[h] ==> !h->\closed)
};

struct Handle {
  int dummy;
   _(ghost struct Data *data;) 
  _(invariant data->\closed && data->handles[\this])
};

void foo(struct X *x) _(writes \extent(x)) _(maintains \mutable(x) && \object_root(x));

void wrapped_use()
{
  struct Data d;
  struct Handle h;
  struct X x;

  _(ghost {

  d.handles = (\lambda struct Handle *h; (\false));
  _(assert \forall struct Handle *h; h->data == &d ==> !\inv(h))
  _(wrap &d)
  _(assert &d \in \domain(&d))

  _(atomic &d) {
    d.handles = (\lambda struct Handle *hh; (hh == &h));
    _(bump_volatile_version &d)
  }
  _(assert &d \in \domain(&d))
  h.data = &d;
  _(wrap &h)

  })

  foo(&x);

  _(ghost {

  _(atomic &d) {
    _(unwrap &h)
    _(begin_update)
    d.handles = (\lambda struct Handle *hh; (\false));
    _(bump_volatile_version &d)
  }
  _(assert &d \in \domain(&d))

  _(unwrap &d)

  })
}

struct Container {
  struct Data d;
  struct Handle h;
  struct Handle h2;

  _(invariant \mine(&d))
  _(invariant \forall struct Handle *hh; d.handles[hh] ==> hh == &h || hh == &h2)
};

void init()
{
  struct Container *c = (struct Container *)malloc(sizeof(struct Container));
  if (c != NULL) {
     _(ghost c->d.handles = (\lambda struct Handle *h; (\false));) 
    _(assert \forall struct Handle *h; h->data == &c->d ==> !\inv(h))
    _(wrap &c->d)
    _(wrap c)
  }
}

void closed_use(struct Container *c)
  _(writes \extent(&c->h))
  _(requires \wrapped(c))
  _(ensures \wrapped(&c->h) && c->h.data == &c->d)
{
_(ghost {
  _(atomic &c->d) {
    _(assert \inv(c))
    c->d.handles = (\lambda struct Handle *hh; (hh == &c->h || c->d.handles[hh]));
  }
  c->h.data = &c->d;
  _(wrap &c->h)
})
}

/*`
Verification of Data#adm succeeded.
Verification of Handle#adm succeeded.
Verification of Container#adm succeeded.
Verification of wrapped_use succeeded.
Verification of init succeeded.
Verification of closed_use succeeded.
`*/
