#include <vcc.h>

/*{obj}*/
#define SSTR_MAXLEN 100
typedef struct SafeString {
  unsigned len;
  char content[SSTR_MAXLEN + 1];
  _(invariant \this->len <= SSTR_MAXLEN)
  _(invariant content[len] == '\0')
} SafeString;
/*{init}*/
void sstr_init(struct SafeString *s)
  _(writes \span(s))
  _(ensures \wrapped(s))
  _(decreases 0)
{
  s->len = 0;
  s->content[0] = '\0';
  _(wrap s)
}
/*{append}*/
void sstr_append_char(struct SafeString *s, char c)
  _(requires \wrapped(s))
  _(requires s->len < SSTR_MAXLEN)
  _(ensures \wrapped(s))
  _(writes s)
  _(decreases 0)
{
  _(unwrap s)
  s->content[s->len++] = c;
  s->content[s->len] = '\0';
  _(wrap s)
}
/*{index}*/
int sstr_index_of(struct SafeString *s, char c)
  _(requires \wrapped(s))
  _(ensures \result >= 0 ==> s->content[\result] == c)
  _(decreases 0)
{
  unsigned i;
  for (i = 0; i < s->len; ++i)
	  _(decreases s->len - i)
    if (s->content[i] == c) return (int)i;
  return -1;
}
/*{out}*/
/*`
Verification of SafeString#adm succeeded.
Verification of sstr_init succeeded.
Verification of sstr_append_char succeeded.
Verification of sstr_index_of succeeded.
`*/
