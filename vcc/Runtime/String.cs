//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

namespace Microsoft.Research.Vcc {
  public static unsafe partial class Runtime {
    public static void* memcpy(void* _Dst, void* _Src, uint _Size) {
      //TODO: preconditions, post conditions
      if (_Size > 0) {
        byte* tgt = (byte*)_Dst;
        byte* src = (byte*)_Src;
        while (_Size-- > 0)
          *tgt = *src;
      }
      return _Dst;
    }

    public static int memcmp(void* _Dst, void* _Src, uint _Size) {
      if (_Size > 0) {
        byte* tgt = (byte*)_Dst;
        byte* src = (byte*)_Src;
        while (_Size-- > 0) {
          if (*tgt < *src) return 1;
          if (*tgt > *src) return -1;
        }
      }
      return 0;
    }
  }
}