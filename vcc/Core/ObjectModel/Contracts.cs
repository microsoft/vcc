//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using ITypeInvariant = Microsoft.Cci.Contracts.ITypeInvariant;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  /// <summary>
  /// A collection of collections of objects that augment the signature of a type with additional information
  /// that describe invariants, model variables and functions, as well as axioms.
  /// </summary>
  // ^ [Immutable]
  public class VccTypeContract : Contract, Microsoft.Cci.Contracts.ITypeContract, ISpecItem {
    /// <summary>
    /// Allocates a collection of collections of objects that augment the signature of a type with additional information
    /// that describe invariants, model variables and functions, as well as axioms.
    /// </summary>
    /// <param name="contractFields">A possibly empty list of contract fields. Contract fields can only be used inside contracts and are not available at runtime.</param>
    /// <param name="invariants">A possibly empty list of type invariants. Axioms are a special type of invariant.</param>
    /// <param name="isSpec">A flag that indicates if this type is a specification or implementation type</param>
    public VccTypeContract(IEnumerable<FieldDeclaration>/*?*/ contractFields, IEnumerable<TypeInvariant>/*?*/ invariants, bool isSpec) {
      this.contractFields = contractFields ?? EmptyListOfFields;
      this.invariants = invariants ?? EmptyListOfInvariants;
      this.isSpec = isSpec;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound()
    {
      bool result = false;
      foreach (ITypeInvariant inv in this.Invariants)
        result |= ((Expression)inv.Condition).HasErrors;
      return result;
    }

    readonly bool isSpec;

    public bool IsSpec {
      get { return this.isSpec; }
    }

    /// <summary>
    /// The type declaration that contains the type contract.
    /// </summary>
    protected TypeDeclaration/*?*/ containingType;

    /// <summary>
    /// A possibly empty list of contract fields. Contract fields can only be used inside contracts and are not available at runtime.
    /// </summary>
    public IEnumerable<IFieldDefinition> ContractFields {
      get {
        foreach (FieldDeclaration fieldDecl in this.contractFields) yield return fieldDecl.FieldDefinition;
        foreach (FieldDeclaration builtInFieldDecl in this.BuiltInFields) yield return builtInFieldDecl.FieldDefinition;
      }
    }
    readonly IEnumerable<FieldDeclaration> contractFields;

    protected virtual IEnumerable<FieldDeclaration> BuiltInFields {
      get {
        return Enumerable<FieldDeclaration>.Empty;
      }
    }

    /// <summary>
    /// A possibly empty list of contract methods. Contract methods have no bodies and can only be used inside contracts. The meaning of a contract
    /// method is specified by the axioms (assumed invariants) of the associated type. Contract methods are not available at runtime.
    /// </summary>
    public IEnumerable<IMethodDefinition> ContractMethods {
      get { yield break; }
    }

    private static readonly IEnumerable<FieldDeclaration> EmptyListOfFields = Enumerable<FieldDeclaration>.Empty;
    private static readonly IEnumerable<TypeInvariant> EmptyListOfInvariants = Enumerable<TypeInvariant>.Empty;

    private IEnumerable<ITypeInvariant> GetInvariantsAndAxiomsAboutConstantArraysAndStructs() {
      VccGlobalDeclarationContainerClass/*?*/ globals = this.containingType as VccGlobalDeclarationContainerClass;
      if (globals == null)
        return IteratorHelper.GetConversionEnumerable<TypeInvariant, ITypeInvariant>(this.invariants);
      List<ITypeInvariant> result = new List<ITypeInvariant>();
      foreach (TypeInvariant tinv in this.invariants) result.Add(tinv);
      return result.AsReadOnly();
    }

    /// <summary>
    /// A possibly empty list of type invariants. Axioms are a special type of invariant.
    /// </summary>
    public IEnumerable<ITypeInvariant> Invariants {
      get {
        if (this.invariantsAndAxiomsAboutConstantArraysAndStructs == null)
          this.invariantsAndAxiomsAboutConstantArraysAndStructs = this.GetInvariantsAndAxiomsAboutConstantArraysAndStructs();
        return this.invariantsAndAxiomsAboutConstantArraysAndStructs;
      }
    }
    readonly IEnumerable<TypeInvariant> invariants;
    IEnumerable<ITypeInvariant>/*?*/ invariantsAndAxiomsAboutConstantArraysAndStructs;

    /// <summary>
    /// Completes the two stage construction of this object. This allows bottom up parsers to construct an Expression before constructing the containing Expression.
    /// This method should be called once only and must be called before this object is made available to client code. The construction code itself should also take
    /// care not to call any other methods or property/event accessors on the object until after this method has been called.
    /// </summary>
    public void SetContainingType(TypeDeclaration containingType) {
      this.containingType = containingType;
      Expression containingExpression = new DummyExpression(containingType.DummyBlock, SourceDummy.SourceLocation);
      foreach (FieldDeclaration contractField in this.contractFields)
        contractField.SetContainingTypeDeclaration(containingType, true);
      foreach (TypeInvariant typeInvariant in this.invariants)
        typeInvariant.SetContainingExpression(containingExpression);
    }

    #region IObjectWithLocations Members

    IEnumerable<ILocation> IObjectWithLocations.Locations {
      get {
        foreach (var f in this.contractFields)
          foreach (var loc in f.Locations) yield return loc;
        foreach (var i in this.invariants)
          foreach (var loc in i.Locations) yield return loc;
      }
    }

    #endregion
  }
}