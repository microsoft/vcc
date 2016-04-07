#include "vcc.h"

#define increments(x) ((x) == \old(x) + 1)
#define decrements(x) ((x) == \old(x) - 1)
#define wrapped_dom(a) (\wrapped(a) && (a) \in \domain(a))

typedef struct _LIST_ENTRY
{
  struct _LIST_ENTRY *Flink;
  _(ghost struct _LIST_ENTRY *Blink)
} LIST_ENTRY, *PLIST_ENTRY;

_(ghost typedef PLIST_ENTRY ListEntryMap[\integer])

_(ghost _(pure) ListEntryMap ListRemoveAt(ListEntryMap m, \integer i)
  _(returns \lambda \integer j; j < i ? m[j] : m[j + 1]))

_(ghost _(pure) ListEntryMap ListInsertAt(ListEntryMap m, \integer i, PLIST_ENTRY e)
  _(returns \lambda \integer j; j == i ? e : j < i ? m[j] : m[j - 1]))

_(ghost typedef _(dynamic_owns) struct _LIST_MANAGER {
  \integer size;
  \integer index[PLIST_ENTRY];
  ListEntryMap pointer;
  bool mem[PLIST_ENTRY];

  _(invariant \forall PLIST_ENTRY e; {mem[e]} mem[e] ==> \mine(e))

  _(invariant \forall PLIST_ENTRY e; {mem[e->Flink]} {:hint mem[e->Flink]}
    mem[e] ==> mem[e->Flink] && e->Flink->Blink == e)

  _(invariant \forall PLIST_ENTRY e; {mem[e->Blink]} {:hint mem[e->Blink]}
    mem[e] ==> mem[e->Blink] && e->Blink->Flink == e)

  _(invariant \forall PLIST_ENTRY e; {mem[e]} {:hint mem[e->Flink]}
    mem[e] && e != pointer[size - 1] ==> index[e] + 1 == index[e->Flink])

  _(invariant \forall PLIST_ENTRY e; {mem[e]} {:hint mem[e->Blink]}
    mem[e] && e != pointer[0] ==> index[e] - 1 == index[e->Blink])

  _(invariant \forall \integer i; 0 <= i && i < size ==>
    index[pointer[i]] == i && mem[pointer[i]])

  _(invariant \forall PLIST_ENTRY e; mem[e] ==>
    0 <= index[e] && index[e] < size && pointer[index[e]] == e)

} LIST_MANAGER, ^PLIST_MANAGER)

void ListInitialize(PLIST_ENTRY Entry _(out PLIST_MANAGER Manager))
  _(writes \extent(Entry))
  _(ensures wrapped_dom(Manager) && \fresh(Manager))
  _(ensures Manager->pointer == \lambda \integer i; i == 0 ? Entry : (PLIST_ENTRY)0)
  _(ensures Manager->size == 1);

int ListIsEmpty(PLIST_ENTRY Entry _(ghost PLIST_MANAGER Manager))
  _(requires wrapped_dom(Manager))
  _(requires Manager->mem[Entry])
  _(returns Manager->size == 1);

PLIST_ENTRY ListRemoveEntryAfter(PLIST_ENTRY Entry _(ghost PLIST_MANAGER Manager))
  _(requires 1 < Manager->size)
  _(maintains Manager->mem[Entry])
  _(maintains wrapped_dom(Manager))
  _(writes Manager)
  _(returns \old(Manager->index[Entry] == Manager->size - 1
    ? Manager->pointer[0]
    : Manager->pointer[Manager->index[Entry] + 1]))
  _(ensures decrements(Manager->size))
  _(ensures Manager->pointer == \old(ListRemoveAt(Manager->pointer, Manager->index[\result])))
  _(ensures \extent_mutable(\result) && \extent_fresh(\result));

void ListInsertEntryAfter(PLIST_ENTRY Entry, PLIST_ENTRY NewEntry _(ghost PLIST_MANAGER Manager))
  _(maintains wrapped_dom(Manager))
  _(requires Manager->mem[Entry])
  _(writes Manager, \extent(NewEntry))
  _(ensures increments(Manager->size))
  _(ensures Manager->pointer ==
    \old(ListInsertAt(Manager->pointer, Manager->index[Entry] + 1, NewEntry)));
