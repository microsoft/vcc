
#include <vcc.h>

typedef unsigned __int32 UINT32;
typedef unsigned __int64 UINT64;
typedef void VOID, *PVOID;

#define NULL ((void*)0)

typedef struct _ENTRY
{
    union
    {
        struct
        {
            UINT64 : 6;
            UINT64 f : 1;
            UINT64 g : 1;
            UINT64 h: 1;
            UINT64 : 1;
            UINT64 : 11;
            UINT64 : 3;
            UINT64 : 40;
        };

        _(backing_member) UINT64 AsUINT64;
    };

    union
    {
        _(backing_member) struct _ENTRY *NextPfn;
        UINT64 Available2;
    };
} ENTRY, *PENTRY;

typedef _(dynamic_owns) struct _RESERVE
{
    void *Compartment;
    void *ListHead;   
    UINT64 ListDepth;

    _(ghost UINT64 ListIndex[struct _ENTRY *])
    _(ghost PENTRY _ListHead)
    
    _(invariant Compartment != NULL)
    _(invariant _ListHead == (PENTRY)ListHead)
    _(invariant _ListHead == NULL <==> ListDepth == 0)
    _(invariant _ListHead == NULL || _ListHead \in0 \this->\owns)
    _(invariant \forall \object p; {p \in0 \this->\owns} p \in0 \this->\owns ==> p \is ENTRY)
    _(invariant \forall PENTRY p; { p->NextPfn \in0 \this->\owns } p \in0 \this->\owns ==> ((p->NextPfn == NULL) || p->NextPfn \in0 \this->\owns))
    _(invariant \forall PENTRY p; { p \in0 \this->\owns } p \in0 \this->\owns ==> (p->NextPfn == NULL) || ListIndex[p] == ListIndex[p->NextPfn] + 1)
    _(invariant \forall PENTRY p; { p \in0 \this->\owns } p \in0 \this->\owns ==> (ListIndex[p] == 0 <==> p->NextPfn == NULL))
    _(invariant _ListHead != NULL ==> ListIndex[_ListHead] + 1 == ListDepth)
    _(invariant \forall PENTRY p; { p \in0 \this->\owns } p \in0 \this->\owns ==> ListDepth > ListIndex[p])
    _(invariant \forall PENTRY p; { p \in0 \this->\owns } p \in0 \this->\owns ==> p->h&& (p->f || p->g))
    
} RESERVE, *PRESERVE;

void
Check(PRESERVE Reserve)
    _(maintains \wrapped(Reserve))
{
    UINT64 pageCount;
    PENTRY pfn;

    _(assert Reserve != NULL)
    _(assert Reserve->Compartment != NULL)
        
    for (pfn = (PENTRY) Reserve->ListHead, pageCount = Reserve->ListDepth;
         pageCount != 0;
         pfn = pfn->NextPfn, pageCount--)
    _(invariant pfn == NULL || pfn \in0 Reserve->\owns)
    _(invariant pfn == NULL <==> pageCount == 0)
    _(invariant pfn == NULL || pageCount == Reserve->ListIndex[pfn] + 1)
    {
      _(assert pfn != NULL)
      _(assert pfn->h)
      _(assert pfn->f || pfn->g)
    }

    _(assert pfn == NULL)
    return;
}

/*`
Verification of _RESERVE#adm succeeded.
Verification of Check succeeded.
`*/
