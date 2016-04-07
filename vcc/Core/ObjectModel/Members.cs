//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using Microsoft.Cci;
using Microsoft.Cci.Ast;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  /// <summary>
  /// Represents a global method in symbol table.
  /// </summary>
  public class VccGlobalMethodDefinition : GlobalMethodDefinition, ISourceItem, ISpecItem {

    /// <summary>
    /// Allocates a global method definition to correspond to a given global method declaration.
    /// </summary>
    /// <param name="functionDefinition">The global method declaration that corresponds to the definition being allocated.</param>
    internal VccGlobalMethodDefinition(FunctionDefinition functionDefinition)
      : base(functionDefinition)
    {
      this.sourceLocation = functionDefinition.SourceLocation;
    }

    /// <summary>
    /// The parameters of this method.
    /// </summary>
    public override IEnumerable<ParameterDefinition> Parameters {
      get {
        //^ assume this.GlobalMethodDeclaration is FunctionDefinition; //the constructor assures this
        var functionDefinition = (FunctionDefinition)this.GlobalMethodDeclaration;
        if (functionDefinition.HasSingleVoidParameter) return Enumerable<ParameterDefinition>.Empty;
        return base.Parameters;
      }
    }

    public static bool ParameterListsMatch(IEnumerator<ParameterDefinition> left, IEnumerator<ParameterDeclaration> right)
    {
      while (left.MoveNext()) {
        if (!right.MoveNext())
          return false;
        if (!TypeHelper.TypesAreEquivalent(left.Current.Type.ResolvedType, right.Current.Type.ResolvedType))
          return false;
      }

      if (right.MoveNext()) return false;

      return true;
    }

    public static bool ParameterListsMatch(IEnumerator<ParameterDeclaration> left, IEnumerator<ParameterDeclaration> right)
    {
      while (left.MoveNext()) {
        if (!right.MoveNext())
          return false;
        if (!TypeHelper.TypesAreEquivalent(left.Current.Type.ResolvedType, right.Current.Type.ResolvedType))
          return false;
      }

      if (right.MoveNext()) return false;

      return true;
    }

    public IEnumerable<FunctionDeclaration> Declarations
    {
      get
      {
        var functionDefinition = (FunctionDefinition) this.GlobalMethodDeclaration;
        // copy global member list because it may change
        var members = new List<ITypeDeclarationMember>(functionDefinition.CompilationPart.GlobalDeclarationContainer.GlobalMembers);
        foreach (ITypeDeclarationMember member in members)
        {
          var decl = member as FunctionDeclaration;
          if (decl != null && decl.Name.Name == this.Name && decl.AcceptsExtraArguments == this.AcceptsExtraArguments)
          {
            if (ParameterListsMatch(this.Parameters.GetEnumerator(), decl.Parameters.GetEnumerator()))
              yield return decl;
          }
        }
      }
    }

    public bool IsSpec {
      get {
        return ((FunctionDefinition)this.GlobalMethodDeclaration).IsSpec;
      }
    }

    #region ISourceItem Members

    private readonly ISourceLocation sourceLocation;

    public ISourceLocation SourceLocation
    {
      get { return this.sourceLocation; }
    }

    #endregion
  }
}