//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Diagnostics;

namespace Microsoft.Research.Vcc {
  public static partial class Runtime {
    public static void __debugbreak() {
      System.Diagnostics.Debugger.Break();
    }

    public static void __int2c() {
      System.Diagnostics.Debug.Assert(false);
    }

    unsafe public static sbyte* __FUNCTION__ { get { return (sbyte*)IntPtr.Zero; } }

    [Conditional("GenerateCodeFor__noopCalls")]
    public static void __noop(params object[] args) {
    }

  }
}
