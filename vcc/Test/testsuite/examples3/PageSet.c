#include <stdlib.h>

#include <vcc.h>

typedef unsigned __int32 UINT32;
typedef unsigned __int64 UINT64, *PUINT64;

typedef struct _PAGE_SET
{
    UINT32 PageCount;          
    UINT32 PagesAllocated;
    PUINT64 Array;

    _(invariant PagesAllocated <= PageCount)
    _(invariant \mine((void[PageCount])Array))

} PAGE_SET, *PPAGE_SET;

void Init(
    PPAGE_SET PageSet,
    UINT32 PageCount,
    UINT64 Array[]
    )
    _(writes \extent(PageSet), (void[PageCount])Array)
    _(requires \wrapped((void[PageCount])Array))
    _(ensures PageSet->PageCount == PageCount)
    _(ensures PageSet->PagesAllocated == 0)
    _(ensures PageSet->Array == Array)
    _(ensures \wrapped(PageSet))
{
    PageSet->Array = Array;
    PageSet->PageCount = PageCount;
    PageSet->PagesAllocated = 0;
    _(wrap PageSet)
}

void CallInit() {
  PAGE_SET *ps = (PAGE_SET *)malloc(sizeof(PAGE_SET));
  PUINT64 arr = malloc(sizeof(UINT64) * 100);
  if (ps != NULL && arr != NULL) {
    _(wrap (void[100])arr)
    Init(ps, 100, arr);
  }
}

/*`
Verification of _PAGE_SET#adm succeeded.
Verification of Init succeeded.
Verification of CallInit succeeded.
`*/
