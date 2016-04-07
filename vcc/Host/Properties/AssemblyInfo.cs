//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Reflection;
using System.Runtime.InteropServices;

[assembly: AssemblyTitle("Vcc")]
[assembly: AssemblyDescription("Command line compiler for the Microsoft Research Vcc language")]
#if DEBUG
[assembly: AssemblyConfiguration("Debug")]
#else
[assembly: AssemblyConfiguration("Release")]
#endif
[assembly: AssemblyTrademark("Microsoft Research Vcc v2")]
[assembly: AssemblyProduct("Vcc Compiler")]
[assembly: AssemblyCulture("")]
[assembly: ComVisible(false)]

