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
};

/*{append}*/
void sstr_append_char(struct SafeString *s, char c)
  _(requires \wrapped(s))
  _(requires s->len < s->capacity - 1)
  _(ensures \wrapped(s))
  _(writes s)
{
  _(unwrapping s) {
    _(unwrapping (char[s->capacity])(s->content)) {
      s->content[s->len++] = c;
      s->content[s->len] = '\0';
    }
  }
}

/*{alloc}*/
struct SafeString *sstr_alloc(unsigned capacity)
  _(requires capacity > 0)
  _(ensures \result != NULL ==> \wrapped(\result))
{
  struct SafeString *s;

  s = malloc(sizeof(*s));
  if (s == NULL) return NULL;

  s->content = malloc(capacity);
  if (s->content == NULL) {
    free(s);
    return NULL;
  }

  s->capacity = capacity;
  s->len = 0;
  s->content[0] = '\0';

  _(wrap (char[capacity])(s->content))
  _(wrap s)

  return s;
}

/*`
Verification of SafeString#adm succeeded.
Verification of sstr_append_char succeeded.
Verification of sstr_alloc succeeded.
`*/
