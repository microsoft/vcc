#include "List.h"
#include "limits.h"

typedef unsigned __int8 uint8_t;

#define CONTAINING_RECORD(_Address_, _Type_, _Field_) \
  ((_Type_ *)( (uint8_t *)(_Address_) - (uint8_t *)(&((_Type_ *)0)->_Field_)))

#define LIST_ENTRY_AT(_Manager_, _Entry_, _Pos_) \
  (((_Manager_)->pointer[_Pos_] == (_Entry_)) && \
  ((_Manager_)->index[_Entry_] == (_Pos_)) && \
  ((_Manager_)->mem[_Entry_]))

typedef struct _NODE {
  LIST_ENTRY List;
  int data;
} NODE, *PNODE;

typedef _(dynamic_owns) struct _LIST {
  LIST_ENTRY Head;
  _(ghost PLIST_MANAGER ListManager)
  _(invariant \mine(ListManager))
  _(invariant LIST_ENTRY_AT(ListManager, &Head, 0))
  _(invariant \forall \integer i; 0 < i && i < ListManager->size ==>
    \mine(CONTAINING_RECORD(ListManager->pointer[i], NODE, List)))
} LIST, *PLIST;

unsigned find(PLIST l)
  _(requires \wrapped(l))
  _(requires l->ListManager->size < UINT_MAX)
  _(ensures \forall \integer j; 0 < j && j < \result ==>
    CONTAINING_RECORD(l->ListManager->pointer[j], NODE, List)->data != 0)
  _(ensures \result < l->ListManager->size ==>
    CONTAINING_RECORD(l->ListManager->pointer[\result], NODE, List)->data == 0)
{
  PNODE n;
  PLIST_ENTRY le;
  unsigned i;

  _(assert l->ListManager \in \domain(l))

  le = l->Head.Flink;
  i = 1;

  while (le != &l->Head)
    _(invariant l->ListManager->mem[le])
    _(invariant i <= l->ListManager->size)
    _(invariant \forall \integer j; 0 < j && j < i ==>
      CONTAINING_RECORD(l->ListManager->pointer[j], NODE, List)->data != 0)
    _(invariant le == l->ListManager->pointer[i == l->ListManager->size ? 0 : i])
  {
    n = CONTAINING_RECORD(le, NODE, List);
    if (n->data == 0) {
      break;
    }
    _(assert \forall \integer j; 0 < j && j <= i ==>
      CONTAINING_RECORD(l->ListManager->pointer[j], NODE, List)->data != 0)
    le = le->Flink;
    i++;
  }

  return i;
}

/*`
Verification of _LIST_MANAGER#adm succeeded.
Verification of _LIST#adm succeeded.
Verification of find succeeded.
`*/
