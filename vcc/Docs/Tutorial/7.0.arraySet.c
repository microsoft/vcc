#include <vcc.h>

#define SIZE 1000
#define TRUE 1
#define FALSE 0
typedef int BOOL;


typedef struct ArraySet {
  _(ghost \bool mem[int])  // abstract value of the set
  int data[SIZE];
  unsigned len;
  _(ghost unsigned idx[int])
  _(invariant len <= SIZE)
  _(invariant \forall unsigned i; i < len ==> mem[data[i]])
  _(invariant \forall int d; mem[d] ==> idx[d] < len && data[idx[d]] == d)
} ArraySet;

void ArraySetInit(ArraySet *s)
	_(requires \extent_mutable(s))
	_(writes \extent(s))
	_(ensures \wrapped(s) && s->mem == \lambda int i; \false)
{
	s->len = 0;
	_(ghost s->mem = \lambda int i; \false)
	_(wrap s)
}

BOOL ArraySetMem(ArraySet *s, int v)
	_(requires \wrapped(s))
	_(ensures \result <==> s->mem[v])
{
	for (unsigned i = 0; i < s->len; i++)
		_(invariant \forall unsigned j; j < i ==> s->data[j] != v)
	{
		if (s->data[i] == v) return TRUE;
	}
	return FALSE;
}
BOOL ArraySetAdd(ArraySet *s, int v)
	_(requires \wrapped(s))
	_(writes s)
	_(ensures \result ==> s->mem == \lambda int i; \old(s->mem[i]) || i == v)
	_(ensures !\result ==> \unchanged(s->mem))
{
	if (s->len == SIZE) return FALSE;
	_(unwrapping s) {
		s->data[s->len] = v;
		_(ghost s->mem[v] = \true)
		_(ghost s->idx[v] = s->len)
		s->len++;
	}
	return TRUE;
}

void ArraySetDel(ArraySet *s, int v)
	_(maintains \wrapped(s))
	_(writes s)
	_(ensures s->mem == \lambda int i; \old(s->mem[i]) && i != v)
{
	_(unwrap s)
	unsigned front, rear;
	for (front = 0, rear = 0; front < s->len; front++) 
		_(writes \array_range(s->data, s->len), &s->idx)
		_(invariant rear <= front && front <= s->len)
		_(invariant \forall unsigned i; i < rear || (front <= i && i < s->len) 
			==> s->mem[s->data[i]])
        _(invariant \forall unsigned i; i < rear ==> s->data[i] != v)
		_(invariant \forall int d; s->mem[d] && d != v ==> 
			(s->idx[d] < rear || (front <= s->idx[d] && s->idx[d] < s->len))  
			&& s->data[s->idx[d]] == d)
		_(invariant \forall int d; d != v ==> \unchanged(s->mem[d])) 
		
	{
		int d = s->data[front];
		if (d != v) {
			s->data[rear] = d;
			_(ghost s->idx[d] = rear)
			rear++;
		} 
	}
	s->len = rear;
	_(ghost s->mem[v] = \false)
	_(wrap s)
}