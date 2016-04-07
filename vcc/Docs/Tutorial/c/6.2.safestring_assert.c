#include <vcc.h>

/*{obj}*/
#define SSTR_MAXLEN 100
struct SafeString {
  unsigned len;
  char content[SSTR_MAXLEN + 1];
  _(invariant len <= SSTR_MAXLEN)
  _(invariant content[len] == '\0')
};

_(\bool \writable(\objset o) _(returns \true))

/*{assert}*/
void sstr_append_char(struct SafeString *s, char c)
  _(requires \wrapped(s))
  _(requires s->len < SSTR_MAXLEN)
  _(ensures \wrapped(s))
{
  // _(unwrap s), steps 1-5
  _(assert \writable(s))
  _(assert \wrapped(s))
  _(assume s->len <= SSTR_MAXLEN &&
           s->content[s->len] == '\0')
  _(ghost s->\closed = \false)
  _(assume \writable(\span(s)))

  s->content[s->len++] = c;
  s->content[s->len] = '\0';

  // _(wrap s), steps 1-3
  _(assert \mutable(s))
  _(assert s->len <= SSTR_MAXLEN &&
           s->content[s->len] == '\0')
  _(ghost s->\closed = \true)
}
/*{out}*/
/*`
testcase(25,11) : warning VC9300: [possible unsoundness]: assignment to physical location from specification code
testcase(35,11) : warning VC9300: [possible unsoundness]: assignment to physical location from specification code
testcase(25,11) : error VC9612: don't know how to write to @_vcc_closed(s)
testcase(35,11) : error VC9612: don't know how to write to @_vcc_closed(s)
`*/
