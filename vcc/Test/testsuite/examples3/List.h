/*
 * This file provides sample specs of doubly-linked lists.
 */
#include "vcc.h"

/*
 * Required forward definitions/declarations.
 */
#define MAXUINT 0xFFFFFFFF

/*
 * Forward declaration of ghost type _LIST_MANAGER.
 */
_(ghost typedef struct _LIST_MANAGER LIST_MANAGER, ^PLIST_MANAGER)

/*
 * Define the doubly-linked list type.
 */
typedef struct _LIST_ENTRY
{
    struct _LIST_ENTRY *Flink;
    struct _LIST_ENTRY *Blink;

    // Each list entry contains a back link to its corresponding list manager.
    _(ghost PLIST_MANAGER Manager)
} LIST_ENTRY, *PLIST_ENTRY;

/*
 * This ghost type _LIST_MANAGER is used to manage the list entries in an abstract way.
 * The list manager is the owner of all list entries and contains a pointer to that
 * designated LIST_ENTRY, that is considered as the list head.
 * The list structure is modeled by a map of pointers to LIST_ENTRY structs to integer
 * values in the range of 0 to size-1, which represent the position of the pointer in
 * the list.
 */

_(ghost _(dynamic_owns) struct _LIST_MANAGER
{
    // Number of entries in the list
    unsigned size;
    // Pointer to the designated list head
    _(ghost PLIST_ENTRY ListHead)
    // A map for the housekeeping of the order of referenced pointers in the list.
    _(ghost unsigned index[PLIST_ENTRY])

    // The "Manager" back-pointer of each LIST_ENTRY points back to this list manager.
    _(invariant \forall PLIST_ENTRY p; {\mine(p)}
        \mine(p) ==> p->Manager == \this)

    // The ListHead is owned by the list manager.
    _(invariant \mine(ListHead))

    // The invariant explicitly talks about this node, and thus we explicitly state
    // we own it.
    _(invariant \mine(ListHead->Blink)) 

    // Each list entry, that can be reached via a Flink is also in the ownership
    // domain of the list manager. Additionally each Blink of an entry p->Flink points
    // back to p.
    _(invariant \forall PLIST_ENTRY p; {\mine(p->Flink)} {:hint \mine(p->Flink)}
        \mine(p) ==> \mine(p->Flink) && p->Flink->Blink == p)

    // Each list entry, that can be reached via a Blink is also in the ownership
    // domain of the list manager. Additionally each Flink of an entry p->Blink points
    // back to p.
    _(invariant \forall PLIST_ENTRY p; {\mine(p->Blink)} {:hint \mine(p->Blink)}
        \mine(p) ==> \mine(p->Blink) && p->Blink->Flink == p)

    // The index[] map always increases by 1 for each object that can be reached by
    // an Flink pointer. Except if the Flink points to the list head, which implies
    // the end of the list.
    //
    // The {:hint \mine(p->Flink)} trigger introduces a witness of
    // a \mine(p->Flink) entry, that is required for the prove to succeed.
    _(invariant \forall PLIST_ENTRY p; {\mine(p)} {:hint \mine(p->Flink)}
        \mine(p) && p->Flink != ListHead ==> index[p] + 1 == index[p->Flink])

    // Specify index[] for well known objects.
    _(invariant index[ListHead] == 0)
    _(invariant index[ListHead->Blink] == size - 1)

    // Specify range of the index[] map.
    _(invariant \forall PLIST_ENTRY e; {\mine(e)}
        \mine(e) ==> index[e] < size)

    // Each element in the list is only contained once.
    _(invariant \forall PLIST_ENTRY e1, e2; {\mine(e1), \mine(e2)}
        \mine(e1) && \mine(e2) && e1 != e2 ==> index[e1] != index[e2])

})

/**
 * InitializeListHead
 * ==================
 *
 * The InitializeListHead routine initializes a LIST_ENTRY structure that represents
 * the head of a doubly-linked list.
 *
 * Parameters:
 *   ListHead : Pointer to a LIST_ENTRY structure that serves as the list header.
 *
 * Return Value:
 *   None
 */
void InitializeListHead( PLIST_ENTRY ListHead )
    _(writes \span(ListHead))
    _(ensures \wrapped(ListHead->Manager) && \fresh(ListHead->Manager))
    _(ensures (ListHead->Manager)->\owns == {ListHead})
    _(ensures ListHead->Manager->size == 1)
    _(ensures ListHead->Manager->ListHead == ListHead);

/**
 * IsListEmpty
 * ===========
 *
 * The IsListEmpty routine indicates whether a doubly linked list of LIST_ENTRY structures is empty.
 *
 *
 * Parameters:
 *   ListHead : Pointer to a LIST_ENTRY structure that represents the head of the list.
 *
 * Return Value:
 *   IsListEmpty returns TRUE if there are currently no entries in the list and FALSE otherwise.
 */
int IsListEmpty( PLIST_ENTRY ListHead )
    _(requires \wrapped(ListHead->Manager))
    _(requires ListHead \in (ListHead->Manager)->\owns)
    _(returns ListHead->Manager->size == 1);

/**
 * RemoveEntryList
 * ===============
 *
 * The RemoveEntryList routine removes an entry from a doubly linked list of LIST_ENTRY structures.
 * The entry to be removed must not be the list head.
 *
 * Parameters:
 *   Entry : Pointer to the LIST_ENTRY structure that represents the entry to be removed.
 *
 * Return Value:
 *   RemoveEntryList returns TRUE if the list is empty and FALSE otherwise.
 */
int RemoveEntryList( PLIST_ENTRY Entry )
    _(requires Entry \in (Entry->Manager)->\owns)
    _(requires Entry != Entry->Manager->ListHead)
    _(maintains \wrapped(Entry->Manager))
    _(writes Entry->Manager)
    _(returns \old(Entry->Manager)->size==1)
    _(ensures \wrapped(Entry) && \fresh(Entry))
    _(ensures (Entry->Manager)->\owns == \old((Entry->Manager)->\owns) \diff {Entry})
    _(ensures Entry->Manager->size == \old(Entry->Manager->size) - 1)
    _(ensures \old(Entry->Manager->ListHead)==\old(Entry->Manager)->ListHead);

/**
 * RemoveHeadList
 * ==============
 *
 * The RemoveHeadList routine removes an entry from the beginning of a doubly linked
 * list of LIST_ENTRY structures. This function must only be called, if the list
 * is not empty.
 *
 * Parameters:
 *   ListHead : Pointer to the LIST_ENTRY structure that serves as the list header.
 *
 * Return Value:
 *   RemoveHeadList returns a pointer to the entry removed from the list.
 */
PLIST_ENTRY RemoveHeadList( PLIST_ENTRY ListHead )
    _(requires ListHead->Flink != ListHead->Manager->ListHead)
    _(maintains ListHead \in (ListHead->Manager)->\owns)
    _(maintains \wrapped(ListHead->Manager))
    _(writes ListHead->Manager)
    _(returns \old(ListHead->Flink))
    _(ensures \unchanged(ListHead->Manager))
    _(ensures \unchanged(ListHead->Manager->ListHead))
    _(ensures ListHead->Manager->size == \old(ListHead->Manager->size) - 1)
    _(ensures (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \diff {\result})
    _(ensures \result \in \old((ListHead->Manager)->\owns))
    _(ensures \wrapped(\result));

/**
 * RemoveTailList
 * ==============
 *
 * The RemoveTailList routine removes an entry from the end of a doubly linked list of
 * LIST_ENTRY structures. The list must not be empty.
 *
 * Parameters:
 *   ListHead : Pointer to the LIST_ENTRY structure that serves as the list header.
 *
 * Return Value:
 *   RemoveTailList returns a pointer to the entry that was at the tail of the list.
 */
PLIST_ENTRY RemoveTailList( PLIST_ENTRY ListHead )
    _(requires ListHead->Manager->size > 1)
    _(requires ListHead->Blink != ListHead->Manager->ListHead)
    _(maintains ListHead \in (ListHead->Manager)->\owns)
    _(maintains \wrapped(ListHead->Manager))
    _(writes ListHead->Manager)
    _(returns \old(ListHead->Blink))
    _(ensures \unchanged(ListHead->Manager))
    _(ensures \unchanged(ListHead->Manager->ListHead))
    _(ensures ListHead->Manager->size == \old(ListHead->Manager->size) - 1)
    _(ensures (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \diff {\result})
    _(ensures \wrapped(\result));

/**
 * InsertTailList
 * ==============
 *
 * The InsertTailList routine inserts an entry at the tail of a doubly linked list of
 * LIST_ENTRY structures.
 *
 * Parameters:
 *   ListHead : Pointer to the LIST_ENTRY structure that represents the head of
 *              the list.
 *   Entry    : Pointer to a LIST_ENTRY structure that represents the entry to
 *              be inserted in the list.
 *
 * Return Value:
 *   None
 */
void InsertTailList( PLIST_ENTRY ListHead, PLIST_ENTRY Entry )
    _(requires \mutable(Entry))
    _(requires ListHead->Manager->size < MAXUINT)
    _(maintains \wrapped(ListHead->Manager))
    _(maintains ListHead \in (ListHead->Manager)->\owns)
    _(writes ListHead->Manager,\span(Entry))
    _(ensures \unchanged(ListHead->Manager))
    _(ensures \unchanged(ListHead->Manager->ListHead))
    _(ensures Entry \in (ListHead->Manager)->\owns)
    _(ensures ListHead->Manager->size == \old(ListHead->Manager->size) + 1)
    _(ensures (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \union {Entry})
    _(ensures \unchanged(ListHead->Manager->ListHead))
    _(ensures Entry->Manager == ListHead->Manager);

/**
 * InsertHeadList
 * ==============
 *
 * The InsertHeadList routine inserts an entry at the head of a doubly-linked list of
 * LIST_ENTRY structures.
 *
 * Parameters:
 *   ListHead  : Pointer to the LIST_ENTRY structure that represents the head
 *               of the list.
 *   Entry     : Pointer to a LIST_ENTRY structure that represents the entry to
 *               be inserted into the list.
 *
 * Return Value:
 *   None
 */
void InsertHeadList( PLIST_ENTRY ListHead, PLIST_ENTRY Entry )
    _(requires \mutable(Entry))
    _(requires ListHead->Manager->size < MAXUINT)
    _(maintains \wrapped(ListHead->Manager))
    _(maintains ListHead \in (ListHead->Manager)->\owns)
    _(writes ListHead->Manager,\span(Entry))
    _(ensures \unchanged(ListHead->Manager))
    _(ensures \unchanged(ListHead->Manager->ListHead))
    _(ensures Entry \in (ListHead->Manager)->\owns)
    _(ensures ListHead->Manager->size == \old(ListHead->Manager->size) + 1)
    _(ensures (ListHead->Manager)->\owns == \old((ListHead->Manager)->\owns) \union {Entry})
    _(ensures Entry->Manager == ListHead->Manager);
