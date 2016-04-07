#include <vcc.h>

_(def \bool sorted(int *buf, unsigned len) {
  return \forall unsigned i, j; i < j && j < len ==> buf[i] <= buf[j];
})

/*{begin}*/
_(typedef _(record) struct  Perm {
	\natural fwd[\natural];
	\natural bwd[\natural];
} Perm;)

_(def \bool isPerm(Perm p, \natural len) {
	return (\forall \natural i; i < len ==> p.fwd[i] < len && p.bwd[i] < len)
	       && (\forall \natural i; i < len ==> p.fwd[p.bwd[i]] == i 
	       && p.bwd[p.fwd[i]] == i);
})

_(def Perm permId() {
	Perm p;
	p.fwd = (\lambda \natural i; i);
	p.bwd = (\lambda \natural i; i);
	return p;
})

_(def Perm permSwap(\natural i, \natural j) {
	Perm p;
	p.fwd = (\lambda \natural k; k == i ? j : (k == j ? i : k));
	p.bwd = p.fwd;
	return p;
})

_(def Perm permCompose(Perm p, Perm q) {
	Perm r;
	r.fwd = (\lambda \natural k; p.fwd[q.fwd[k]]);
	r.bwd = (\lambda \natural k; q.bwd[p.bwd[k]]);
	return r;
})

void sort(int *buf, unsigned len _(out Perm p))
  _(requires \mutable_array(buf,len))
  _(writes \array_range(buf, len))
  _(ensures sorted(buf, len))
  _(ensures isPerm(p,len))
  _(ensures \forall unsigned i; i < len ==> buf[i] == \old(buf[p.fwd[i]]))
  _(decreases 0)
{
  _(ghost int av[\natural] = \lambda \natural i; buf[i])
  _(ghost p = permId())

  if (len < 2) return;

  for (unsigned i = len; i > 0; i--)
    _(invariant i <= len)
    _(invariant \forall unsigned u,v; i <= v && u <= v && v < len ==> buf[u] <= buf[v])
    _(invariant isPerm(p,len))
    _(invariant \forall unsigned i; i < len ==> buf[i] == av[p.fwd[i]]) 
    for (unsigned j = 0; j + 1 < i; j++)
      _(decreases i-j)
      _(invariant j < i)
      _(invariant \forall unsigned u,v; i <= v && u <= v && v < len ==> buf[u] <= buf[v])
      _(invariant \forall unsigned u; u < j ==> buf[u] <= buf[j])
      _(invariant isPerm(p,len))
      _(invariant \forall unsigned i; i < len ==> buf[i] == av[p.fwd[i]]) 
      if (buf[j] > buf[j+1]) {
        int tmp = buf[j];
        buf[j] = buf[j+1];
        buf[j+1] = tmp;
        _(ghost p = permCompose(p,permSwap(j,j+1)))
      }
}

/*`
Verification of sorted succeeded.
Verification of isPerm succeeded.
Verification of permId succeeded.
Verification of permSwap succeeded.
Verification of permCompose succeeded.
Verification of sort succeeded.
`*/
