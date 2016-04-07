// Guids.cs
// MUST match guids.h
using System;

namespace Microsoft.Research.Vcc.VSPackage
{
  static class GuidList
  {
    public const string GuidVSPackagePkgString = "eced64f5-d683-451b-8b50-821d19c7eb50";
    public const string GuidVSPackageCmdSetString = "7c3dd686-d502-4019-8b44-67b2efb94304";
    public const string GuidErrorToolWindowPersistanceString = "0f26e8a6-9867-4fd1-846d-d420a0d5ecbf";
    public const string GuidBvdWindowPersistanceString = "7b57ffd0-4205-4ba2-8ef4-a2fd76e0a126";
    
    public static readonly Guid GuidVSPackageCmdSet = new Guid(GuidVSPackageCmdSetString);
  };
}