#pragma once

void memzero(unsigned *b, unsigned size)
  _(writes (unsigned[size])b)
  _(maintains \wrapped((unsigned[size])b))
  _(ensures \forall unsigned i; i < size ==> b[i] == 0);

#define _InterlockedCompareExchange(T)                                         \
_(atomic_inline)                                                               \
T InterlockedCompareExchange(volatile T *Destination, T Exchange, T Compare) { \
  if (*Destination == Compare) {                                               \
    *Destination = Exchange;                                                   \
    return Compare;                                                            \
  }                                                                            \
  else {                                                                       \
    return *Destination;                                                       \
  }                                                                            \
}                                                                              \

typedef unsigned __int64 uint64_t;
typedef unsigned __int8  uint8_t;

_(atomic_inline)
int InterlockedBitSet(volatile uint64_t *v, uint64_t pos) {
  int result = (((*v) >> pos) & 1) == 1;
  *v |= (1ULL << pos);
  return result;
}
