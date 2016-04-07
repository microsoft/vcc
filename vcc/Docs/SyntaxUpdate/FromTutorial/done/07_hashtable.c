#include <vcc.h>
#include <stdlib.h>

struct SafeString {
  unsigned capacity, len;
  char *content;
  _(invariant len < capacity)
  _(invariant content[len] == '\0')
  _(invariant \mine((char[capacity])content))
};

_(ghost typedef struct SafeString * sstr_map[unsigned];)
_(bool _(pure) match(unsigned i, unsigned j) _(ensures \result == \true);) // should use 'logic'
_(\integer _(pure) do_mod(\integer a, \integer b);)

_(axiom \forall \integer a, b; {do_mod(a,b)} a >= 0 && b > 0 ==> 0 <= do_mod(a, b) && do_mod(a,b) < b)
_(axiom \forall \integer a; {do_mod(a,a)} a > 0 ==> do_mod(a, a) == 0)
_(axiom \forall \integer a, b; {do_mod(a,b)} a >= 0 && b > 0 && do_mod(a, b) < b - 1 ==> 
  do_mod(a + 1, b) == do_mod(a, b) + 1)
_(axiom \forall \integer a, b; {do_mod(a,b)} a >= 0 && b > 0 && do_mod(a, b) == b - 1 ==> 
  do_mod(a + 1, b) == 0)

#define mod(a,b) ((unsigned)(do_mod((\integer)(a), (\integer)(b))))

struct Hashtable {
  unsigned *keys;
  struct SafeString **values;
  unsigned size;
  _(ghost sstr_map elts;)

  _(invariant size > 0)

  _(invariant \mine((unsigned[size])keys, (struct SafeString *[size])values))

  _(invariant \forall unsigned k; {match(k,0)} match(k,0) && elts[k] != NULL ==> 
    \exists unsigned d; {match(d,1)}
      match(d,1) &&
      (\forall unsigned i; {match(i,2)} match(i,2) && i < d ==> values[mod(k + i, size)] != NULL) &&
      keys[mod(k + d, size)] == k &&
      values[mod(k + d, size)] == elts[k])
  _(invariant \forall unsigned k, i; {match(i,3),match(k,4)} match(i,3) && match(k, 4) && i < size ==>
    values[i] != NULL && keys[i] == k ==> elts[k] == values[i])
};

int h_insert(struct Hashtable *h, unsigned k, struct SafeString *s)
  _(writes h)
  _(requires h->elts[k] == NULL)
  _(requires s != NULL)
  _(requires \wrapped(h))
  _(ensures \result == 0 ==> h->elts[k] == s && \forall unsigned i; h->elts[i] == \old(h->elts[i]) || i == k)
  _(ensures \result != 0 ==> h->elts == \old(h->elts))
{
  unsigned i ,d;
  int res = 0;


  _(unwrapping h) {
    _(unwrapping (unsigned[h->size])(h->keys)) {
      _(unwrapping (struct SafeString*[h->size])(h->values)) {

        // i = k % h->size;
	_(assume i == mod(k, h->size))
	d = 0;

        for (;;)
	  _(invariant i < h->size && d < h->size)
	  _(invariant i == mod(k + d, h->size))
	  _(invariant d >= 0)
          _(invariant \forall unsigned j; {match(j,2)} match(j,2) && j < d ==> h->values[mod(k + j, h->size)] != NULL)
	{
	  if (h->values[i] == NULL)
	    break;

	  if (++i >= h->size)
	    i = 0;
	  d++;

	  if (d >= h->size) { 
	    res = -1;
	    break;
	  }
	}

	if (res == 0) {
  	_(assert match(d,1))

          h->values[i] = s;
          h->keys[i] = k;
          _(ghost h->elts[k] = s;)
	}
      }
    }
  }

  return res;
}

struct SafeString *h_find(struct Hashtable *h, unsigned k)
_(requires \wrapped(h))
_(ensures \result == h->elts[k])
{
unsigned i, d;

        // i = k % h->size;
	_(assume i == mod(k, h->size))
	d = 0;

        for (;;)
	  _(invariant i < h->size && d < h->size)
	  _(invariant i == mod(k + d, h->size))
	  _(invariant d >= 0)
          _(invariant \forall unsigned j; {match(j,1)} match(j,1) && j < d ==> h->keys[mod(k + j, h->size)] != k || h->values[mod(k + j, h->size)] == NULL)
	{
	  _(assert \inv(h))
          _(assert match(k,0))
          _(assert match(d,2))

	  if (h->values[i] == NULL) {
            _(assert match(d,1))
            _(assert match(d+1,1))
	    return NULL;
	  }


	  if (h->keys[i] == k) {
	    _(assert match(i,3) && match(k,4))
	    return h->values[i];
	  }

	  if (++i >= h->size)
	    i = 0;
	  d++;

	  if (d >= h->size) { 
	    _(assume \false)
	    return NULL;
	  }
	}
}
/*`
Verification of SafeString#adm succeeded.
Verification of Hashtable#adm succeeded.
Verification of h_insert succeeded.
Verification of h_find succeeded.
`*/
