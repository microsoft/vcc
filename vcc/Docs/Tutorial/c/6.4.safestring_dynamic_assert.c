/*{include}*/
#include <vcc.h>
#include <stdlib.h>
/*{obj}*/

struct SafeString {
  unsigned capacity, len;
  char *content;
  _(invariant len < capacity)
  _(invariant content[len] == '\0')
  _(invariant \mine((char[capacity])content))
  _(ghost \bool consistencyFlag; )
};
/*{append}*/
void sstr_append_char(struct SafeString *s, char c)
  _(requires \wrapped(s))
  _(requires s->len < s->capacity - 1)
  _(ensures \wrapped(s))
  _(writes s)
{
  _(ghost \object cont = (char[s->capacity]) s->content; )
  // _(unwrap s) steps 1-5
  _(assert \writable(s) && \wrapped(s))
  _(assume \writable(\span(s)) && \inv(s))
  _(ghost s->\closed = \false; )
  // and the transfer:
  _(ghost cont->\owner = \me; )
  _(assume \writable(cont))
  // _(unwrap cont) steps 1-5
  _(assert \writable(cont) && \wrapped(cont))
  _(ghost cont->\closed = \false; )
  _(assume \writable(\span(cont)) && \inv(cont))
  // no transfer here

  s->content[s->len++] = c;
  s->content[s->len] = '\0';

  // _(wrap cont) steps 1-3
  _(assert \mutable(cont) && \inv(cont))
  _(ghost cont->\closed = \true; )
  // _(wrap s) steps 1-3, with transfer in the middle
  _(assert \mutable(s))
  _(ghost cont->\owner = s; )
  _(assert \inv(s))
  _(ghost s->\closed = \true; )
}
/*{out}*/
// Not that the output makes no much sense, but at least there are no parse errors.
/*`
testcase(24,12) : error VC0000: The best overloaded method match for '__Globals__.\writable(System.Diagnostics.Contracts.CodeContract.TypedPtr)' has some invalid arguments.
testcase(24,22) : error VC0000: Argument '1': cannot convert from '\objset' to '\object'.
testcase(32,12) : error VC0000: The best overloaded method match for '__Globals__.\writable(System.Diagnostics.Contracts.CodeContract.TypedPtr)' has some invalid arguments.
testcase(32,22) : error VC0000: Argument '1': cannot convert from '\objset' to '\object'.
`*/
