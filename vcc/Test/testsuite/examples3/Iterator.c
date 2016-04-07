#include <vcc.h>
#include <stdlib.h>

struct Collection {
  int *arr;
  int ver;

  _(group  _(claimable) Shadow)
  _(ghost _(:Shadow) volatile \state shadow;)
  _(invariant :Shadow \approves(\this->\owner, shadow))
  _(invariant :Shadow \at(\old(shadow), ver) <= \at(shadow, ver))
  _(invariant :Shadow \at(\old(shadow), ver) == \at(shadow, ver) ==>
                      \at(\old(shadow), arr) == \at(shadow, arr))

  _(invariant \mine(\this::Shadow))
  _(invariant \at(shadow, arr) == arr)
  _(invariant \at(shadow, ver) == ver)
};


void init()
{
  struct Collection *coll = (struct Collection *)malloc(sizeof(struct Collection));
  if (coll != NULL) {
    coll->arr = NULL;
    coll->ver = 0;

    _(ghost {
      coll->shadow = \now();
      _(wrap coll::Shadow)
      _(wrap coll)
    })
  }
}


void add(struct Collection *c)
  _(maintains \wrapped(c))
  _(requires c->ver < 100000)
  _(writes c)
{
  int x;

  _(unwrapping c) {
    c->arr = &x;
    c->ver++;

    _(ghost _(atomic c::Shadow) {
      c->shadow = \now();
      _(bump_volatile_version c::Shadow)
    })
  }
}

struct Iterator {
  struct Collection *coll;
  int ver;
   _(ghost \claim cl;)
   _(ghost int *arr;)

#define shadow_copy(o, f) \at((o)->shadow, \at(\now(), o)->f)
  _(invariant \mine(cl) && \claims_object(cl, coll::Shadow))
  _(invariant shadow_copy(coll, ver) >= ver)
  _(invariant shadow_copy(coll, ver) == ver ==> shadow_copy(coll, arr) == arr)
};

void get_iter(struct Collection *c)
  _(requires \wrapped(c))
{
  struct Iterator *iter = (struct Iterator *)malloc(sizeof(struct Iterator));
  if (iter != NULL) {
    iter->coll = c;
    iter->ver = c->ver;
     _(ghost iter->arr = c->arr;)
    _(atomic c) {
       _(ghost iter->cl = \make_claim({c::Shadow}, \true);)
    }

    _(wrap iter)
  }
}

void iterate(struct Iterator *it)
  _(maintains \wrapped(it))
  _(requires \wrapped(it->coll))
  _(requires it->ver == it->coll->ver)
  _(writes it)
{
  _(unwrapping it) {
    _(assert it->arr == it->coll->arr)
  }
}

/*`
Verification of Collection#adm succeeded.
Verification of Collection##Shadow#adm succeeded.
Verification of Iterator#adm succeeded.
Verification of init succeeded.
Verification of add succeeded.
Verification of get_iter succeeded.
Verification of iterate succeeded.
`*/
