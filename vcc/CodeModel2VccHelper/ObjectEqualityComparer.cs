//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;

namespace Microsoft.Research.Vcc
{
  // work around a problem in the F# implementation for Equals in tuples,
  // which fails for an argument of different type
  public class ObjEqualityComparer : IEqualityComparer<Object> 
  {
    bool IEqualityComparer<object>.Equals(object x, object y) {
      if (x.GetType() == y.GetType()) return x.Equals(y);
      return object.ReferenceEquals(x, y);
    }

    int IEqualityComparer<object>.GetHashCode(object obj) {
      return obj.GetHashCode();
    }
  }
}
