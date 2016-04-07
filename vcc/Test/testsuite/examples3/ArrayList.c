// ----------------------------------------------------------------------------
// ArrayList.c
//
// The capacity of an ArrayList is the number of elements the ArrayList can
// hold.  As elements are added to an ArrayList, the capacity is automatically
// increased as required through reallocation.  Elements in this collection can
// be accessed using an integer index. Indexes in this collection are
// zero-based.
//
// ----------------------------------------------------------------------------

#include <stdlib.h>
#include "vcc.h"

#ifdef VERIFY
#define speccast(_TYPE_, _EXPR_) ((_TYPE_)(_EXPR_))
#else
#define speccast(_TYPE_, _EXPR_) (_EXPR_)
#endif

struct ArrayList {
    size_t capacity;
    size_t length;
    int *array;

    _(invariant \malloc_root(\this) &&
        length <= capacity &&
        \mine((int[capacity])array) &&
        \malloc_root((int[capacity])array))
};

_(pure)
size_t Length(struct ArrayList *A)
    _(reads \universe())
    _(requires \wrapped(A))
    _(returns A->length)
{
    return A->length;
}

struct ArrayList *CreateArrayList(size_t InitialCapacity)
    _(requires 0 < InitialCapacity)
    _(ensures \wrapped(\result))
    _(ensures \fresh(\result))
    _(ensures Length(\result) == 0)
{
    struct ArrayList *A;

    A = malloc(sizeof(*A));
    _(assume A != NULL)

    A->capacity = InitialCapacity;
    A->length = 0;
    A->array = malloc(sizeof(*A->array) * InitialCapacity);
    _(assume A->array != NULL)

    _(wrap (int[InitialCapacity])A->array)
    _(wrap A)
    return A;
}

void MakeEmpty(struct ArrayList *A)
    _(maintains \wrapped(A))
    _(writes A)
    _(ensures Length(A) == 0)
{
    _(unwrap A)
    A->length = 0;
    _(wrap A)
}

_(pure)
int Select(struct ArrayList *A, size_t i)
    _(reads \universe())
    _(requires i < Length(A))
    _(requires \wrapped(A))
    _(ensures \result == A->array[i])
{
    return A->array[i];
}

void Update(struct ArrayList *A, size_t i, int v)
    _(requires i < Length(A))
    _(requires \wrapped(A))
    _(writes A)
    _(ensures \forall size_t j; j < Length(A) ==>
        Select(A, j) == \old(j == i ? v : A->array[j]))
{
    _(unwrapping A, (int[A->capacity])(A->array))
        A->array[i] = v;
}

void DisposeArrayList(struct ArrayList *A)
    _(requires \wrapped(A))
    _(writes A)
{
    _(unwrap A)
    _(unwrap (int[A->capacity])A->array)
    free(speccast(int[A->capacity], A->array));
    free(A);
}

void Add(struct ArrayList *A, int v)
    _(requires Length(A) < 100000)
    _(maintains \wrapped(A))
    _(writes A)
    _(ensures Length(A) == \old(Length(A)) + 1)
    _(ensures \forall size_t j; j < \old(Length(A)) ==>
        Select(A, j) == \old(Select(A, j)))
    _(ensures Select(A, Length(A) - 1) == v)
{
    _(unwrapping A, (int[A->capacity])A->array) {
        if (A->capacity == A->length) {
            size_t i;
            int *tmp;
            size_t newCapacity;

            newCapacity = A->capacity * 2 + 1;

            tmp = malloc(sizeof(*A->array) * newCapacity);
            _(assume tmp != NULL)

            i = 0;
            while (i < A->length)
                _(invariant \forall size_t j; j < i ==> tmp[j] == \old(A->array[j]))
                _(writes \array_range(tmp, A->length))
            {
                tmp[i] = A->array[i];
                i = i + 1;
            }
            free(speccast(int[A->capacity], A->array));
            A->capacity = newCapacity;
            A->array = tmp;
        }
        A->array[A->length] = v;
        A->length++;
    }
}

int main_test()
{
    size_t N = 42;
    struct ArrayList *A = CreateArrayList(N);
    size_t i = 0;

    while (i < N)
        _(writes A)
        _(invariant \wrapped(A))
        _(invariant Length(A) == i)
        _(invariant \forall size_t j; j < i ==> Select(A, j) == (int) j)
    {
        Add(A, (int)i);
        i++;
    }
    DisposeArrayList(A);
    return 0;
}

/*`
Verification of ArrayList#adm succeeded.
Verification of Length succeeded.
Verification of CreateArrayList succeeded.
Verification of MakeEmpty succeeded.
Verification of Select succeeded.
Verification of Update succeeded.
Verification of DisposeArrayList succeeded.
Verification of Add succeeded.
Verification of main_test succeeded.
`*/
