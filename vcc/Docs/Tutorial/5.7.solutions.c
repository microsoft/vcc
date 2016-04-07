#include <vcc.h>

typedef int BOOL;
#define TRUE 1
#define FALSE 0

_(def BOOL sorted(int *p, unsigned len) {
  return \forall unsigned i,j; i < j && j < len ==> p[i] <= p[j];
})

// a function that takes two arrays and checks 
// whether the arrays are equal 
BOOL arrays_eq(int *p, int *q, unsigned len)
  _(requires \thread_local_array(p, len))
  _(requires \thread_local_array(q,len))
  _(ensures \result <==> (\forall unsigned i; 
      i < len ==> p[i] == q[i]))
  _(decreases 0)
{
  for (unsigned i = 0; i < len; i++)
    _(invariant \forall unsigned j; j < i 
      ==> p[j] == q[j])
    if (p[i] != q[i]) return FALSE;
  return TRUE;
}

// a function that checks whether two sorted arrays 
// contain a common element;
BOOL disjoint(int *p, unsigned lp, int *q, unsigned lq)
  _(requires \thread_local_array(p,lp))
  _(requires \thread_local_array(q,lq))
  _(requires sorted(p,lp) && sorted(q,lq))
  _(ensures \result <==> \forall unsigned i,j; 
      i < lp && j < lq ==> p[i] != q[j])
  _(decreases 0)
{
  unsigned i,j;
  i = 0;
  j = 0;
  while (i < lp && j < lq) 
    _(invariant i <= lp && j <= lq)
    _(invariant \forall unsigned x,y; 
        x < i && y >= j && y < lq ==> p[x] < q[y])
    _(invariant \forall unsigned x,y; 
        y < j && x >= i && x < lp ==> q[y] < p[x])
    _(invariant \forall unsigned x,y; 
        x < i && y < j ==> p[x] != q[y])
	_(decreases lp - i + lq - j)
  {
    if (p[i] < q[j]) i++;
    else if (p[i] > q[j]) j++; 
    else return FALSE;
  }
  return TRUE;
}

// a function that checks whether a sorted array 
// contains a given value;
unsigned binary_search(int *p, unsigned len, int val)
  _(requires \thread_local_array(p,len) && sorted(p,len))
  _(ensures \result <= len)
  _(ensures \result == len ==> \forall unsigned i; 
      i < len ==> p[i] != val)
  _(ensures \result < len ==> p[\result] == val)
  _(decreases 0)
{
  unsigned i = 0;
  unsigned j = len;
  while (i < j) 
    _(invariant i <= j && j <= len)
    _(invariant \forall unsigned u; 
        u < i ==> p[u] < val)
    _(invariant \forall unsigned u; 
        j <= u && u < len ==> p[u] > val)
    _(decreases j - i)
  {
    unsigned k = i + (j-i)/2;
    if (p[k] > val) j = k;
    else if (p[k] < val) i = k+1; 
    else return k;
  }
  return len;
}

// a function that takes an array and checks whether 
// it contains any duplicate elements;
BOOL no_dups(int *p, unsigned len)
  _(requires \thread_local_array(p,len))
  _(ensures \result <==> \forall unsigned i,j; 
      i < len && j < len && p[i] == p[j] ==> i==j)
  _(decreases 0)
{
  unsigned i=0, j=0;
  while (i < len) 
    _(invariant j <= i && i <= len)
    _(invariant \forall unsigned u,v; 
        (u < i && v < i) || (u == i && v < j)
        ==> (p[u] == p[v] ==> u == v))
    _(decreases len-i, len-j)
  {
    if (j==i) {
      j = 0;
      i++;
    } else {
      if (p[i] == p[j]) return FALSE;
      j++;
    }
  }
  return TRUE;
}

// a function that reverses an array
void reverse(int *p, unsigned len)
  _(requires \mutable_array(p,len))
  _(writes \array_range(p,len))
  _(ensures \forall unsigned i; i < len 
      ==> p[i] == \old(p[len-i-1]))
	_(decreases 0)
{
  for (unsigned i = 0; i < len/2; i++)
    _(decreases len/2 - i)
    _(invariant \forall unsigned j; j < i 
      ==> p[j] == \old(p[len-j-1]) 
		  && p[len-j-1] == \old(p[j]))
    _(invariant \forall unsigned j; j >= i && j < len-i 
      ==> p[j] == \old(p[j]))
  {
    int tmp = p[i];
    p[i] = p[len-i-1];
    p[len-i-1] = tmp;
  }
}
