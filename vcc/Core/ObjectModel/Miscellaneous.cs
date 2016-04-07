//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using Microsoft.Cci;
using Microsoft.Cci.Ast;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {
  class ErrorReporter : ISymbolSyntaxErrorsReporter {
    private ErrorReporter() { }
    internal static readonly ErrorReporter Instance = new ErrorReporter();
  }

  public class VccNameDeclaration : NameDeclaration
  {
    private readonly bool isCompilerGenerated;

    public VccNameDeclaration(IName name, bool isCompilerGenerated, ISourceLocation sourceLocation)
      : base(name, sourceLocation) {
        this.isCompilerGenerated = isCompilerGenerated;
    }

    public VccNameDeclaration(IName name, ISourceLocation sourceLocation) 
      : this(name, false, sourceLocation) {
      
    }

    protected VccNameDeclaration(Compilation targetCompilation, VccNameDeclaration template) 
      : base(targetCompilation, template) {
        this.isCompilerGenerated = template.isCompilerGenerated;
    }

    public override NameDeclaration MakeCopyFor(Compilation targetCompilation) {
      return new VccNameDeclaration(targetCompilation, this);
    }

    public bool IsCompilerGenerated {
      get { return this.isCompilerGenerated; }
    }
  }
}