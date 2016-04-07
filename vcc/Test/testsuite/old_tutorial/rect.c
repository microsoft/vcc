#include "vcc.h"

struct point {
  int x;
  int y;
};

struct rect {
  struct point ll;
  struct point ur;

  _(invariant inv_rect(\this))
  _(invariant \mine(&ll))
  _(invariant \mine(&ur))
};

_(ghost _(pure) \bool inv_rect(struct rect * r)
  _(reads r)
  _(returns r->ll.x <= r->ur.x && r->ll.y <= r->ur.y);)

_(ghost _(pure) \bool within_bounds(struct rect *r, int dx, int dy)
  _(reads r)
  _(returns 0 <= r->ll.x + dx && r->ll.x + dx < 1024 &&
    0 <= r->ur.x + dx && r->ur.x + dx < 1024 &&
    0 <= r->ll.y + dy && r->ll.y + dy < 1024 &&
    0 <= r->ur.y + dy && r->ur.y + dy < 1024))

void move(struct rect *r, int dx, int dy)
  _(maintains \wrapped(r))
  _(requires within_bounds(r, dx, dy))
  _(writes r)
{
  _(assert r \in \domain(r))
  _(assert &r->ll \in \domain(r))
  _(assert &r->ur \in \domain(r))

  _(unwrap r)
  _(unwrap &r->ll)
  r->ll.x = _(unchecked)(r->ll.x + dx);
  r->ll.y = _(unchecked)(r->ll.y + dy);
  _(wrap &r->ll)
  _(unwrap &r->ur)
  r->ur.x = _(unchecked)(r->ur.x + dx);
  r->ur.y = _(unchecked)(r->ur.y + dy);
  _(wrap &r->ur)
  _(wrap r)
}

/*`
testcase(39,26) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
testcase(40,26) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
testcase(43,26) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
testcase(44,26) : warning VC9326: [possible unsoundness]: signed overflow (of '+') has undefined behavior in C
Verification of rect#adm succeeded.
Verification of move succeeded.
Verification of within_bounds#reads succeeded.
Verification of inv_rect#reads succeeded.
`*/
