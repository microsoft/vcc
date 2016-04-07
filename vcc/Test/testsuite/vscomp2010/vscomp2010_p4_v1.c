// Run without /it!
#include <vcc.h>
#ifndef VERIFY
#include <stdio.h>
#endif

_(ghost typedef int IntIntMap[int])

// Triggering function
_(ghost _(pure) bool match_map(IntIntMap board) _(returns \true))

#define boundedBefore(board, i, N) \
  (\forall int _j; 0 <= _j && _j < (i) ==> 0 <= (board)[_j] && (board)[_j] < (N))

#define equalBefore(b1, b2, i) \
  (\forall int _j; 0 <= _j && _j < (i) ==> (b1)[_j] == (b2)[_j])

#define captures(board, i, j) \
  ((board)[i] == (board)[j] || \
    (board)[i] - (board)[j] == (j) - (i) || \
    (board)[j] - (board)[i] == (j) - (i))

#define safeAt(board, j) \
  (\forall int _i; 0 <= _i && _i < (j) ==> !captures(board, _i, j))

#define safeBefore(board, k) \
  (\forall int _j; 0 <= _j && _j < (k) ==> safeAt(board, _j))

int IsConsistent(int *board, int pos, int length)
  _(requires 0 <= pos)
  _(requires \thread_local_array(board,(unsigned)pos+1))
  _(requires boundedBefore(board,pos+1,length))
  _(returns safeAt(board,pos))
{
  int q;
  for (q = 0; q < pos; q++)
    _(invariant \forall int k; 0 <= k && k < q ==> !captures(board,k,pos))
    if (captures(board,q,pos)) return 0;

  return 1;
}

int Search(int *board, int pos, int length)
  _(requires 0 < length)
  _(requires 0 <= pos && pos < length)
  _(requires safeBefore(board,pos))
  _(maintains \mutable_array(board,(unsigned)length))
  _(requires boundedBefore(board,pos,length))
  _(ensures \forall int k; 0 <= k && k < pos ==> \unchanged(board[k]))
  _(ensures \result
    ? safeBefore(board,length)
    : \forall IntIntMap b; {match_map(b)} {:hint match_map(b)}
      boundedBefore(b, length, length) && equalBefore(board, b, pos) ==>
        !safeBefore(b, length))
  _(writes \array_range(board, (unsigned)length))
{
  int i;

  for (i = 0; i < length; i++)
    _(invariant \mutable_array(board, (unsigned)length))
    _(invariant \forall int k; 0 <= k && k < pos ==> \unchanged(board[k]))
    _(invariant \forall IntIntMap b; {match_map(b)} {:hint match_map(b)}
      boundedBefore(b, length, length) && equalBefore(board, b, pos) &&
      b[pos] < i ==>
        !safeBefore(b, length))
  {
    board[pos] = i;

    if (IsConsistent(board, pos, length) &&
      (pos == length - 1 || Search(board, pos + 1, length)))
        return 1;
  }

  return 0;
}

#ifndef VERIFY
void printBoard(int *a, int length) {
  int i;
  for (i = 0; i < length; i++)
    printf("  [%d] = %d\n", i, a[i]);
}

int main(int argc, char **argv) {
  int a[4]; // good enough for both tests
  int r;

  r = Search(a,0,2);
  printf("Search(a,0,2) = %d\n", r);
  if (r) printBoard(a,2);

  r = Search(a,0,4);
  printf("Search(a,0,4) = %d\n", r);
  if (r) printBoard(a,4);

}
#endif

/*`
Verification of IsConsistent succeeded.
Verification of Search succeeded.
`*/
