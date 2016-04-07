#pragma once

#include <vcc.h>

_(atomic_inline) int __interlockedcompareexchange(volatile int *Destination, int Exchange, int Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}

#ifdef VERIFY
// Hide overloaded version from regular compiler

_(atomic_inline) unsigned __interlockedcompareexchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}
#endif
