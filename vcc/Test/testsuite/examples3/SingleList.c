/*
 * This file provides a sample implementation of singly-linked lists.
 */
#include "vcc.h"

/*
 * Required forward definitions/declarations.
 */
#define NULL    (void*)0
#define MAXUINT 0x7FFFFFFF

#ifdef VERIFY
/*
 * Forward declaration of ghost type _SINGLE_LIST_MANAGER.
 */
typedef struct _SINGLE_LIST_MANAGER SINGLE_LIST_MANAGER, *PSINGLE_LIST_MANAGER;
#endif

/*
 * Define singly-linked list entry.
 */
typedef struct _SINGLE_LIST_ENTRY
{
    struct _SINGLE_LIST_ENTRY *Next;

    // For proving the structure of the list, we also need a pointer
    // to the previous item in the list.
    _(ghost struct _SINGLE_LIST_ENTRY *Back)
    // Each list entry contains a back link to its corresponding list manager.
    _(ghost SINGLE_LIST_MANAGER ^Manager)
} SINGLE_LIST_ENTRY, *PSINGLE_LIST_ENTRY;

#ifdef VERIFY
/*
 * This ghost type _SINGLE_LIST_MANAGER is used to manage the list entries in an abstract way.
 * The list manager is the owner of all list entries and contains a pointer to that
 * designated SINGLE_LIST_ENTRY, that is considered as the list head.
 * The list structure is modeled by a map of pointers to SINGLE_LIST_ENTRY structs to integer
 * values in the range of 0 to size-1, which represent the position of the pointer in
 * the list.
 */

_(ghost _(dynamic_owns) struct _SINGLE_LIST_MANAGER
{
    // Number of entries in the list
    unsigned int size;
    // Pointer to the designated list head
    _(ghost PSINGLE_LIST_ENTRY ListHead)
    // A map for the housekeeping of the order of referenced pointers in the list.
    _(ghost unsigned int index[PSINGLE_LIST_ENTRY])

    // All objects are of the type SINGLE_LIST_ENTRY
    _(invariant \forall \object p; {p \in \this->\owns}
        p \in \this->\owns ==> p \is SINGLE_LIST_ENTRY)

    // The "Manager" back-pointer of each LIST_ENTRY points back to this list manager.
    _(invariant \forall PSINGLE_LIST_ENTRY p; {p \in \this->\owns}
        p \in \this->\owns ==> p->Manager == \this)

    // The ListHead is owned by the list manager.
    _(invariant ListHead \in \this->\owns)

    // Each list entry, that can be reached via a Next is also in the ownership
    // domain of the list manager. Additionally each Back of an entry p->Next points
    // back to p.
    _(invariant \forall PSINGLE_LIST_ENTRY p; {p->Next \in \this->\owns} {:hint p->Next \in \this->\owns}
        p \in \this->\owns && p->Next != NULL ==> p->Next \in \this->\owns && p->Next->Back == p)
    // Each list entry, that can be reached via a Back is also in the ownership
    // domain of the list manager. Additionally each Next of an entry p->Back points
    // back to p.
    _(invariant \forall PSINGLE_LIST_ENTRY p; {p->Back \in \this->\owns} {:hint p->Back \in \this->\owns}
        p \in \this->\owns && p->Back != NULL ==> p->Back \in \this->\owns && p->Back->Next == p)

    // The index[] map always increases by 1 for each object that can be reached by
    // an Flink pointer. Except if the Flink points to the list head, which implies
    // the end of the list.
    //
    // The {sk_hack(set_in(p->Next,owns(this)))} trigger introduces a witness of
    // an set_in(p->Next,owns(this)) entry, that is required for the prove to succeed.
    _(invariant \forall PSINGLE_LIST_ENTRY p; {p \in \this->\owns} {:hint p->Next \in \this->\owns}
        p \in \this->\owns && p->Next != NULL ==> index[p] + 1 == index[p->Next])

    // Specify index[] for well known objects.
    _(invariant index[ListHead] == 0)

    // Specify range of the index[] map.
    _(invariant \forall PSINGLE_LIST_ENTRY e; {e \in \this->\owns}
        e \in \this->\owns ==> 0 <= index[e] && index[e] < size)

    // Each element in the list is only contained once.
    _(invariant \forall PSINGLE_LIST_ENTRY e1, e2; {e1 \in \this->\owns, e2 \in \this->\owns}
        e1 \in \this->\owns && e2 \in \this->\owns && e1 != e2 ==> index[e1] != index[e2])

};)


typedef struct _SINGLE_LIST_MANAGER SINGLE_LIST_MANAGER, *PSINGLE_LIST_MANAGER;

#endif


/**
 * InitializeSingleListHead
 * ========================
 *
 * The InitializeSingleListHead initalises an entry of type PSINGLE_LIST_ENTRY as
 * list head of a singly-linked list.
 *
 * Parameters:
 *   ListHead : Pointer to the SINGLE_LIST_ENTRY structure that represents the head
 *              of the list. On return, ListHead->Next points to NULL.
 *
 * Return Value:
 *   None
 */
void InitializeSingleListHead( PSINGLE_LIST_ENTRY ListHead )
    _(requires \mutable(ListHead))
    _(writes \extent(ListHead))
    _(ensures (ListHead->Manager)->\owns == {ListHead})
    _(ensures ListHead->Manager->ListHead == ListHead)
    _(ensures ListHead->Manager->size == 1)
    _(ensures \wrapped(ListHead->Manager))
    _(ensures \fresh(ListHead->Manager))
{
    _(ghost SINGLE_LIST_MANAGER ^ListManager)
    ListHead->Next = NULL;
    _(ghost ListHead->Back = NULL)

_(ghost {
    ListManager = \alloc<SINGLE_LIST_MANAGER>();
    ListManager->size = 1;
    ListManager->index[ListHead] = 0;
    ListManager->ListHead = ListHead;

    _(ghost ListHead->\owns = {});
    _(ghost ListManager->\owns = {ListHead});
    ListHead->Manager = ListManager;
    _(wrap ListHead)
    _(wrap ListManager)
    })
}


/**
 * PopEntryList
 * ============
 *
 * The PopEntryList routine removes the first entry from a singly linked list of
 * SINGLE_LIST_ENTRY structures.
 *
 * Parameters:
 *   ListHead : Pointer to the SINGLE_LIST_ENTRY structure that represents the head
 *              of the list. On return, ListHead->Next points to the beginning of
 *              the list with the first entry removed.
 *
 * Return Value:
 *   PopEntryList returns a pointer to the entry removed from the list,
 *   or NULL if the list is currently empty.
 */
PSINGLE_LIST_ENTRY PopEntryList( PSINGLE_LIST_ENTRY ListHead )
    _(requires ListHead \in (ListHead->Manager)->\owns)
    _(requires ListHead == ListHead->Manager->ListHead)
    _(requires ListHead->\closed)
    _(maintains \wrapped(ListHead->Manager))
    _(ensures \old(ListHead->Manager->size) == 1 ==> \result == NULL)
    _(ensures \old(ListHead->Manager->size) > 1 ==> \result == \old(ListHead->Next))
    _(ensures \result == NULL ==> \unchanged(ListHead->Manager->size))
    _(ensures \result == NULL ==> (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns))
    _(ensures \result != NULL ==> ListHead->Manager->size == \old(ListHead->Manager->size) - 1)
    _(ensures \result != NULL ==> (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \diff {\result})
    _(ensures \result != NULL ==> \wrapped(\result))
    _(writes ListHead->Manager)
{
    PSINGLE_LIST_ENTRY FirstEntry;
    _(ghost SINGLE_LIST_MANAGER ^ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Next != NULL ==> ListHead->Next \in \domain(ListManager))

    FirstEntry = ListHead->Next;
    if (FirstEntry != NULL)
    {
        _(assert ListManager->size > 1)
        _(assert FirstEntry->Next != NULL ==> FirstEntry->Next \in \domain(ListManager))
        _(unwrapping ListManager) {
            _(unwrapping ListHead) {
                ListHead->Next = FirstEntry->Next;

                _(ghost if (ListHead->Next != NULL) {
                    _(unwrapping ListHead->Next) {
                        ListHead->Next->Back = ListHead;
                    }
                })
            }
_(ghost {
            ListManager->size = ListManager->size - 1;
            _(ghost ListManager->\owns -= FirstEntry);
            ListManager->index = (\lambda PSINGLE_LIST_ENTRY x; ((x == ListHead) ? 0 : ListManager->index[x]-1));
})
            _(assert \old(ListManager->size) > 0)
            _(assert ListManager->size == \old(ListManager->size) - 1)
        }
    }
    return FirstEntry;
}


/**
 * PushEntryList
 * =============
 *
 * The PushEntryList routine inserts an entry at the beginning of a singly-linked list
 * of SINGLE_LIST_ENTRY structures.
 *
 * Parameters:
 *   ListHead : Pointer to the SINGLE_LIST_ENTRY structure that serves as the list header.
 *   Entry    : Pointer to SINGLE_LIST_ENTRY structure that represents the entry to be
 *              inserted on the list.
 *
 * Return Value:
 *   None
 */
void
PushEntryList( PSINGLE_LIST_ENTRY ListHead, PSINGLE_LIST_ENTRY Entry )
    _(maintains \wrapped(ListHead->Manager))
    _(maintains ListHead \in (ListHead->Manager)->\owns)
    _(requires ListHead == ListHead->Manager->ListHead)
    _(requires \mutable(Entry))
    _(requires ListHead->Manager->size < MAXUINT)
    _(ensures Entry \in (ListHead->Manager)->\owns)
    _(ensures ListHead->Manager->size == \old(ListHead->Manager->size) + 1)
    _(ensures (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \union {Entry})
    _(writes ListHead->Manager, \extent(Entry))
{
    _(ghost SINGLE_LIST_MANAGER ^ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Next != NULL ==> ListHead->Next \in \domain(ListManager))

    // assert(!set_in(Entry, owns(ListManager)));

    _(unwrapping ListManager) {
        Entry->Next = ListHead->Next;

_(ghost {
        _(ghost Entry->\owns =  {});
        Entry->Back = ListHead;
        Entry->Manager = ListManager;
        _(wrap Entry)

        if (Entry->Next != NULL) {
            _(unwrapping Entry->Next) {
                Entry->Next->Back = Entry;
            }
        }
})
        _(unwrapping ListHead) {
            ListHead->Next = Entry;
        }

_(ghost {
        ListManager->size = ListManager->size + 1;
        _(ghost ListManager->\owns += Entry);
        ListManager->index = (\lambda PSINGLE_LIST_ENTRY x; ((x==Entry)?ListManager->index[ListHead] + 1 :
                                        ((ListManager->index[x]<= ListManager->index[ListHead])?ListManager->index[x]:ListManager->index[x] + 1 )));
})
    }
}

/*`
Verification of _SINGLE_LIST_MANAGER#adm succeeded.
Verification of InitializeSingleListHead succeeded.
Verification of PopEntryList succeeded.
Verification of PushEntryList succeeded.
`*/
