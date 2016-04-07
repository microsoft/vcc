//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;

namespace Microsoft.Research.Vcc {
  using va_list = ArgIterator;
  public static unsafe partial class  Stdarg {
    // First attempt
    public static void va_start(va_list argp, object dontcare) {
    }

    public static void va_end(va_list argp) {
    }

    public static object/*?*/ va_arg(va_list argp, Type t) {
      ArgIterator ai = argp; 

      if (ai.GetRemainingCount() > 0) {
        TypedReference tr = ai.GetNextArg();
        // TODO: coerce return value to type t...
        return (object)(__refvalue(tr, object));
      }
      throw new FormatException();
    }
  }
}
