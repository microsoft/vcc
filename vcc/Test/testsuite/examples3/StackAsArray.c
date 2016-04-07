#include <stdlib.h>
#include <limits.h>

#ifdef VERIFY
#define speccast(_TYPE_, _EXPR_) ((_TYPE_)(_EXPR_))
#else
#define speccast(_TYPE_, _EXPR_) (_EXPR_)
#endif

#include <vcc.h>

_(ghost struct AbsStack {
    size_t high_mark;
    size_t capacity;
    size_t entries[size_t];

    _(invariant high_mark <= capacity)
    _(invariant \malloc_root(\this))
})

struct Stack{
    size_t topOfStack;
    size_t capacity;
    size_t *elements;
    _(ghost struct AbsStack ^abs)
    _(ghost \object elementsAsArray)

    _(invariant elementsAsArray == (void[capacity])elements)
    _(invariant \mine(abs, elementsAsArray))
    _(invariant \malloc_root(\this))
    _(invariant \malloc_root(elementsAsArray))
    _(invariant topOfStack <= capacity)
    _(invariant AbstractionRelation(\this))
};


_(ghost _(pure)
\bool AbstractionRelation(struct Stack *stack)
    _(reads \universe())
    _(returns (stack->capacity == stack->abs->capacity) &&
        stack->topOfStack == stack->abs->high_mark &&
        \forall size_t idx; idx < stack->topOfStack ==> (stack->elements[idx] == stack->abs->entries[idx])))


_(frameaxiom)
int IsEmpty(struct Stack *S)
    _(reads S)
    _(requires \wrapped(S))
    _(returns S->abs->high_mark == 0)
{
    return S->topOfStack == 0;
}

_(pure)
int IsFull(struct Stack *S)
    _(reads S)
    _(requires \wrapped(S))
    _(returns S->abs->high_mark == S->abs->capacity)
{
    return S->topOfStack == S->capacity;
}

size_t Length(struct Stack *S)
    _(requires \wrapped(S))
    _(returns S->abs->high_mark)
{
    return S->topOfStack;
}

struct Stack *CreateStack(unsigned max_capacity)
    _(requires max_capacity > 0)
    _(ensures \result == NULL ||
        \wrapped(\result) &&
        \fresh(\result) &&
        IsEmpty(\result) &&
        \result->abs->capacity == max_capacity)
{
    struct Stack *S;

    S = malloc(sizeof(struct Stack));
    if (S == NULL) return NULL;

    S->topOfStack = 0;
    S->capacity = max_capacity;
    S->elements = malloc(sizeof(size_t) * S->capacity);
    if (S->elements == NULL) {
        free(S);
        return NULL;
    }

    _(ghost {
        S->elementsAsArray = (void[S->capacity])(S->elements);
        S->abs = \alloc<struct AbsStack>();
        S->abs->high_mark = S->topOfStack;
        S->abs->capacity = S->capacity;})
    _(wrap S->elementsAsArray)
    _(wrap S->abs)
    _(wrap S)
    return S;
}

void DisposeStack(struct Stack *S)
    _(requires \wrapped(S))
    _(writes S)
{
    _(assert S->elementsAsArray \in \domain(S))
    _(unwrap S)
    _(unwrap S->elementsAsArray)
    free((void*) speccast(void[S->capacity], S->elements));
    _(unwrap S->abs)
    free(S);
}

void MakeEmpty(struct Stack *S)
    _(maintains \wrapped(S))
    _(ensures IsEmpty(S))
    _(writes S)
{
    _(unwrap S)
    S->topOfStack = 0;
    _(unwrap S->abs)
    _(ghost S->abs->high_mark = S->topOfStack)
    _(wrap S->abs)
    _(wrap S)
}

size_t Top(struct Stack *S)
    _(requires \wrapped(S))
    _(requires !IsEmpty(S))
    _(returns S->abs->entries[S->abs->high_mark - 1])
{
    _(assert S->elementsAsArray \in \domain(S))
    return S->elements[S->topOfStack - 1];
}

void Pop(struct Stack *S)
    _(maintains \wrapped(S))
    _(writes S)
    _(requires !IsEmpty(S))
    _(ensures !IsFull(S))
    _(ensures S->abs->high_mark == \old(S->abs->high_mark) - 1)
    _(ensures \forall size_t idx; idx < S->abs->high_mark ==> (\unchanged(S->abs->entries[idx])))
{
    _(unwrap S)
    S->topOfStack--;
    _(unwrap S->abs)
    _(ghost S->abs->high_mark--)
    _(wrap S->abs)
    _(wrap S)
}

void Push(struct Stack *S, size_t X)
    _(maintains \wrapped(S))
    _(writes S)
    _(requires !IsFull(S))
    _(ensures !IsEmpty(S))
    _(ensures S->abs->high_mark == \old(S->abs->high_mark) + 1)
    _(ensures \forall size_t idx; idx < \old(S->abs->high_mark) ==> (\unchanged(S->abs->entries[idx])))
    _(ensures S->abs->entries[S->abs->high_mark - 1] == X)
{
    _(assert S->elementsAsArray \in \domain(S))
    _(unwrap S)
    _(unwrap S->elementsAsArray)
    S->elements[S->topOfStack] = X;
    _(wrap S->elementsAsArray)
    S->topOfStack++;
    _(unwrap S->abs)
    _(ghost {
        S->abs->entries[S->abs->high_mark] = X;
        S->abs->high_mark++;
    })
    _(wrap S->abs)
    _(wrap S)
}

_(pure)
int IsIn(struct Stack *S, size_t value)
    _(requires \wrapped(S))
    _(reads \universe())
    _(returns \exists size_t v; v < S->abs->high_mark && S->abs->entries[v] == value)
{
    unsigned __int64 index;

    _(assert S->elementsAsArray \in \domain(S))
    _(assert S->abs \in \domain(S))

    for (index = 0; index < S->topOfStack; index++)
        _(invariant \forall size_t v; v < index ==> (S->abs->entries[v] != value))
    {
        if (S->elements[index] == value) {
            _(assert S->abs->entries[index] == value)
            return 1;
        }
    }
    return 0;
}

/*`
Verification of AbsStack#adm succeeded.
Verification of Stack#adm succeeded.
Verification of IsEmpty succeeded.
Verification of IsFull succeeded.
Verification of Length succeeded.
Verification of CreateStack succeeded.
Verification of DisposeStack succeeded.
Verification of MakeEmpty succeeded.
Verification of Top succeeded.
Verification of Pop succeeded.
Verification of Push succeeded.
Verification of IsIn succeeded.
Verification of IsFull#reads succeeded.
Verification of IsEmpty#reads succeeded.
`*/
