#include <stdlib.h>
#include "vcc.h"

#define CAPACITY (100)

struct Stack {
    size_t topOfStack;
    int array[CAPACITY];
    _(invariant \malloc_root(\this) && topOfStack <= CAPACITY)
};

_(frameaxiom)
int IsEmpty(struct Stack *S)
    _(reads S)
    _(requires \wrapped(S))
    _(returns S->topOfStack == 0)
{
    return S->topOfStack == 0;
}

_(pure)
int IsFull(struct Stack *S)
    _(reads S)
    _(requires \wrapped(S))
    _(returns S->topOfStack == CAPACITY)
{
    return S->topOfStack == CAPACITY;
}

_(pure)
size_t Length(struct Stack *S)
    _(reads S)
    _(requires \wrapped(S))
    _(returns S->topOfStack)
{
    return S->topOfStack;
}

struct Stack *CreateStack()
    _(ensures \result == NULL ||
	    \wrapped(\result) && \fresh(\result) && IsEmpty(\result))
{
    struct Stack *S;

    S = malloc(sizeof(*S));
    if (S != NULL) {
        S->topOfStack = 0;
        _(wrap S)
    }
    return S;
}

void DisposeStack(struct Stack *S)
    _(requires \wrapped(S))
    _(writes S)
{
    _(unwrap S)
    free(S);
}

void MakeEmpty(struct Stack *S)
    _(maintains \wrapped(S))
    _(ensures IsEmpty(S))
    _(writes S)
{
    _(unwrap S)
    S->topOfStack = 0;
    _(wrap S)
}

void Push(struct Stack *S, int X)
    _(maintains \wrapped(S))
    _(requires !IsFull(S))
    _(ensures !IsEmpty(S))
    _(ensures S->topOfStack==\old(S->topOfStack) + 1)
    _(writes S)
{
    _(unwrap S)
    S->array[S->topOfStack++] = X;
    _(wrap S)
}

int Top(struct Stack *S)
    _(requires !IsEmpty(S))
    _(requires \wrapped(S))
    _(returns S->array[S->topOfStack-1])
{
    return S->array[S->topOfStack-1];
}

void Pop(struct Stack *S)
    _(maintains \wrapped(S))
    _(requires !IsEmpty(S))
    _(ensures !IsFull(S))
    _(ensures S->topOfStack==\old(S->topOfStack) - 1)
    _(writes S)
{
    _(unwrap S)
    S->topOfStack--;
    _(wrap S)
}

void test_main()
{
    struct Stack *S;
    size_t i;
    int j;

    S = CreateStack();

    if (S!=NULL) {
        _(assert IsEmpty(S))
        i = 0;
        while (i < CAPACITY)
            _(writes S)
            _(invariant \wrapped(S))
            _(invariant i == Length(S))
        {   
            Push(S, _(unchecked)((int)i));
            i++;
        }

        while (i > 0)
            _(writes S)
            _(invariant \wrapped(S))
            _(invariant i == Length(S))
        {   
            j = Top(S);
            Pop(S);
            i--;
        }

        DisposeStack(S);
    }
}

/*`
Verification of Stack#adm succeeded.
Verification of IsEmpty succeeded.
Verification of IsFull succeeded.
Verification of Length succeeded.
Verification of CreateStack succeeded.
Verification of DisposeStack succeeded.
Verification of MakeEmpty succeeded.
Verification of Push succeeded.
Verification of Top succeeded.
Verification of Pop succeeded.
Verification of test_main succeeded.
Verification of Length#reads succeeded.
Verification of IsFull#reads succeeded.
Verification of IsEmpty#reads succeeded.
`*/
