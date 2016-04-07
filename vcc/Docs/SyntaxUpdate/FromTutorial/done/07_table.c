#include <vcc.h>
#include <stdlib.h>

struct SafeString {
  unsigned capacity, len;
  char *content;
  _(invariant len < capacity)
  _(invariant content[len] == '\0')
  _(invariant \mine((char[capacity])content))
};

/*{obj}*/
_(dynamic_owns) struct SafeContainer {
  struct SafeString **strings;
  unsigned len;

  _(invariant \mine((struct SafeString *[len])strings))
  _(invariant \forall unsigned i; i < len ==> 
      \mine(strings[i]))
  _(invariant \forall unsigned i, j; i < len && j < len ==>
      i != j ==> strings[i] != strings[j])
};

/*{set}*/
void sc_set(struct SafeContainer *c, 
            struct SafeString *s, unsigned idx)
  _(requires \wrapped(c) && \wrapped(s))
  _(requires idx < c->len)
  _(ensures \wrapped(c))
  _(ensures c->strings[idx] == s)
  _(ensures \wrapped(\old(c->strings[idx])))
  _(ensures c->len == \old(c->len))
  _(writes c, s)
{
  _(unwrapping c) {
    _(unwrapping (struct SafeString *[c->len])(c->strings)) {
      c->strings[idx] = s;
    }
    _(ghost {
      // could be also done with one assignment
      c->\owns =  c->\owns \diff {\old(c->strings[idx])};
      c->\owns =  c->\owns \union {s};
    })
  }
}

/*{use}*/
void use_case(struct SafeContainer *c, struct SafeString *s)
  _(requires \wrapped(c) && \wrapped(s))
  _(requires c->len > 10)
  _(writes c, s)
{
  struct SafeString *o;
  o = c->strings[5];

  _(assert \wrapped(s)) // OK
  sc_set(c, s, 5);
  _(assert \wrapped(o)) // OK
}

/*{out}*/
/*`
Verification of SafeString#adm succeeded.
Verification of SafeContainer#adm succeeded.
Verification of sc_set succeeded.
Verification of use_case succeeded.
`*/
