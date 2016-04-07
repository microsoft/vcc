//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using Microsoft.Research.Vcc.Parsing;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  public sealed class VccRootNamespaceDeclaration : RootNamespaceDeclaration {

    internal VccRootNamespaceDeclaration(VccCompilationPart compilationPart, ISourceLocation sourceLocation)
      : base(compilationPart, sourceLocation) 
      //^ requires sourceLocation.SourceDocument is VccCompositeDocument;
    {
    }

    internal VccRootNamespaceDeclaration(ISourceLocation sourceLocation)
      : base(null, sourceLocation)
      //^ requires sourceLocation.SourceDocument is VccCompositeDocument;
    {
    }

    protected override void InitializeIfNecessary()
      //^^ ensures this.members != null;
    {
      if (this.isInitialized) return;
      lock (GlobalLock.LockingObject) {
        if (this.isInitialized) return;
        //^ assume this.CompilationPart is VccCompilationPart; //The constructor ensures this
        VccCompilationPart cp = (VccCompilationPart)this.CompilationPart;
        Parser parser = Parser.Create(cp.Compilation, this.SourceLocation, cp.ScannerAndParserErrors); //TODO: get options from Compilation
        this.Parse(parser);
        this.SetContainingNodes();
        ErrorEventArgs errorEventArguments = new ErrorEventArgs(ErrorReporter.Instance, this.SourceLocation, cp.ScannerAndParserErrors.AsReadOnly());
        this.Compilation.HostEnvironment.ReportErrors(errorEventArguments);
        errorEventArguments = new ErrorEventArgs(ErrorReporter.Instance, cp.UnpreprocessedDocument.SourceLocation, cp.PreprocessorErrors);
        this.Compilation.HostEnvironment.ReportErrors(errorEventArguments);
        this.isInitialized = true;
      }
    }

    public void ReportDuplicateIncompatibleTypedefs() {
      Dictionary<int, TypedefDeclaration> seenTypedefs = new Dictionary<int, TypedefDeclaration>();
      foreach (var typedef in IteratorHelper.GetFilterEnumerable<ITypeDeclarationMember, TypedefDeclaration>(this.CompilationPart.GlobalDeclarationContainer.TypeDeclarationMembers)) {
        TypedefDeclaration seenTypedef;
        if (seenTypedefs.TryGetValue(typedef.Name.UniqueKey , out seenTypedef)) {
          if (!TypeHelper.TypesAreEquivalent(typedef.Type.ResolvedType, seenTypedef.Type.ResolvedType)) {
            this.Helper.ReportError(
              new VccErrorMessage(typedef.SourceLocation, Error.DuplicateTypedef, typedef.Name.Value, 
                this.Helper.GetTypeName(seenTypedef.Type.ResolvedType), this.Helper.GetTypeName(typedef.Type.ResolvedType)));
          }
        } else {
          seenTypedefs.Add(typedef.Name.UniqueKey, typedef);
        }
      }
    }
    bool isInitialized;
    //^ invariant isInitialized ==> this.members != null;

    private void Parse(Parsing.Parser parser)
      //^ ensures this.members != null;
    {
      List<INamespaceDeclarationMember> members = this.members = new List<INamespaceDeclarationMember>();
      parser.ParseCompilationUnit(this.CompilationPart.GlobalDeclarationContainer, members);
      members.TrimExcess();
      //^ assume this.members != null;
    }

    internal void Parse(Parsing.Parser parser, VccCompilationPart compilationPart) {
      this.Parse(parser);
      this.compilationPart = compilationPart;
      this.SetContainingNodes();
      this.isInitialized = true;
    }

    public override NamespaceDeclaration UpdateMembers(List<INamespaceDeclarationMember> members, ISourceDocumentEdit edit)
      //^^ requires edit.SourceDocumentAfterEdit.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
      //^^ ensures result.GetType() == this.GetType();
    {
      VccRootNamespaceDeclaration result = 
        new VccRootNamespaceDeclaration(edit.SourceDocumentAfterEdit.GetCorrespondingSourceLocation(this.SourceLocation)) { members = members, isInitialized = true };
      result.compilationPart = this.CompilationPart.UpdateRootNamespace(result);
      return result;
    }

  }

}
