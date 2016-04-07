/*
 * This file provides a sample implementation of doubly-linked lists.
 */
#include "list.h"

void InitializeListHead( PLIST_ENTRY ListHead )
{
    _(ghost PLIST_MANAGER ListManager)
    ListHead->Flink = ListHead->Blink = ListHead;

_(ghost {
    ListManager = \alloc<LIST_MANAGER>();
    ListManager->size = 1;
    ListManager->index[ListHead] = 0;
    ListManager->ListHead = ListHead;
    ListHead->Manager = ListManager;
    _(ghost ListManager->\owns = {ListHead});
    _(wrap ListHead)
    _(wrap ListManager)
    })
}

int IsListEmpty( PLIST_ENTRY ListHead )
{
    _(assert ListHead->Flink \in (ListHead->Manager)->\owns)
    return ListHead->Flink == ListHead;
}

int RemoveEntryList( PLIST_ENTRY Entry )
{
    PLIST_ENTRY Blink, Flink;
    _(ghost PLIST_MANAGER ListManager = Entry->Manager)

    _(assert Entry \in \domain(ListManager))
    _(assert Entry->Blink \in \domain(ListManager))
    _(assert Entry->Flink \in \domain(ListManager))

    Blink = Entry->Blink;
    Flink = Entry->Flink;
    _(unwrapping ListManager) {
        _(unwrapping Blink) {
            Blink->Flink = Flink;
        }
        _(unwrapping Flink) {
            Flink->Blink = Blink;
        }

_(ghost {
        ListManager->size--;
        _(ghost ListManager->\owns -= Entry);
        ListManager->index = (\lambda PLIST_ENTRY x; (ListManager->index[x] < ListManager->index[Entry]
                ? ListManager->index[x]
                : ListManager->index[x] - 1));
        })
    }

    return Flink == Blink;
}

PLIST_ENTRY RemoveHeadList( PLIST_ENTRY ListHead )
{
    PLIST_ENTRY Flink, Entry;
    _(ghost PLIST_MANAGER ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Flink \in \domain(ListManager))
    _(assert ListHead->Flink->Flink \in \domain(ListManager))

    Entry = ListHead->Flink;
    Flink = ListHead->Flink->Flink;
    _(unwrapping ListManager) {
        _(unwrapping ListHead) {
            ListHead->Flink = Flink;
        }
        _(unwrapping Flink) {
            Flink->Blink = ListHead;
        }

_(ghost {
        ListManager->size--;
        _(ghost ListManager->\owns -= Entry);
        ListManager->index = (\lambda PLIST_ENTRY x; (ListManager->index[x] < ListManager->index[Entry]
                ? ListManager->index[x]
                : ListManager->index[x] - 1));
        })
    }
    return Entry;
}

PLIST_ENTRY RemoveTailList( PLIST_ENTRY ListHead )
{
    PLIST_ENTRY Blink, Entry;
    _(ghost PLIST_MANAGER ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Blink \in \domain(ListManager))
    _(assert ListHead->Blink->Blink \in \domain(ListManager))

    Entry = ListHead->Blink;
    Blink = ListHead->Blink->Blink;
    _(unwrapping ListManager) {
        _(unwrapping ListHead) {
            ListHead->Blink = Blink;
        }
        _(unwrapping Blink) {
            Blink->Flink = ListHead;
        }

_(ghost {
        ListManager->size--;
        _(ghost ListManager->\owns -= Entry);
        ListManager->index = (\lambda PLIST_ENTRY x; (ListManager->index[x] < ListManager->index[Entry]
                ? ListManager->index[x]
                : ListManager->index[x] - 1));
        })
    }
    return Entry;
}

void InsertTailList( PLIST_ENTRY ListHead, PLIST_ENTRY Entry )
{
    _(ghost PLIST_MANAGER ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Blink \in \domain(ListManager))

    Entry->Flink = ListHead;
    Entry->Blink = ListHead->Blink;
    _(ghost Entry->Manager = ListManager)

    _(wrap Entry)
    _(unwrapping ListManager) {
        _(unwrapping ListHead->Blink) {
            ListHead->Blink->Flink = Entry;
        }
        _(unwrapping ListHead) {
            ListHead->Blink = Entry;
        }

_(ghost {
        ListManager->size++;
        _(ghost ListManager->\owns += Entry);

        if (ListHead == ListManager->ListHead) {
            ListManager->index[Entry] = ListManager->size - 1;
        } else {
            ListManager->index = (\lambda PLIST_ENTRY x; (x==Entry
                    ? ListManager->index[ListHead]
                    : (ListManager->index[x] < ListManager->index[ListHead]
                        ? ListManager->index[x]
                        : ListManager->index[x] + 1)));
        }
        })
    }
}

void InsertHeadList( PLIST_ENTRY ListHead, PLIST_ENTRY Entry )
{
    _(ghost PLIST_MANAGER ListManager = ListHead->Manager)

    _(assert ListHead \in \domain(ListManager))
    _(assert ListHead->Flink \in \domain(ListManager))

    Entry->Blink = ListHead;
    Entry->Flink = ListHead->Flink;
    _(ghost Entry->Manager = ListManager)
    _(wrap Entry)
    _(unwrapping ListManager) {
        _(unwrapping ListHead->Flink) {
            ListHead->Flink->Blink = Entry;
        }
        _(unwrapping ListHead) {
            ListHead->Flink = Entry;
        }

_(ghost {
        ListManager->size++;
        _(ghost ListManager->\owns += Entry);
        ListManager->index = (\lambda PLIST_ENTRY x; (x==Entry
                ? ListManager->index[ListHead] + 1
                : (ListManager->index[x] <= ListManager->index[ListHead]
                    ? ListManager->index[x]
                    : ListManager->index[x] + 1)));
        })
    }
}

/*`
Verification of _LIST_MANAGER#adm succeeded.
Verification of InitializeListHead succeeded.
Verification of IsListEmpty succeeded.
Verification of RemoveEntryList succeeded.
Verification of RemoveHeadList succeeded.
Verification of RemoveTailList succeeded.
Verification of InsertTailList succeeded.
Verification of InsertHeadList succeeded.
`*/
