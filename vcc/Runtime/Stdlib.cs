//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Runtime.InteropServices;

namespace Microsoft.Research.Vcc {
  public static unsafe partial class Runtime {

    public static void free(void* _Memory) {
      Marshal.FreeHGlobal((IntPtr)_Memory);
    }

    public static void* malloc(uint size)
      //^ requires size <= int.MaxValue;
    {
      return Marshal.AllocHGlobal((int)size).ToPointer();
    }
  }
}