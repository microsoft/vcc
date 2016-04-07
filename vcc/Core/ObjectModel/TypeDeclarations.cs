//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using Microsoft.Cci;
using Microsoft.Cci.Ast;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {
  public interface IVccDatatypeDeclaration : IStructDeclaration
  {
    IEnumerable<FunctionDeclaration> Constructors { get; }
  }

  internal sealed class VccGlobalDeclarationContainerClass : GlobalDeclarationContainerClass {

    public VccGlobalDeclarationContainerClass(IMetadataHost compilationHost)
      : base(compilationHost) {
    }

    private VccGlobalDeclarationContainerClass(NamespaceDeclaration containingNamespaceDeclaration, VccGlobalDeclarationContainerClass template)
      : base(containingNamespaceDeclaration, template)
      //^ ensures this.containingNamespaceDeclaration == containingNamespaceDeclaration;
    {
    }

    public override INamespaceDeclarationMember MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.ContainingNamespaceDeclaration) return this;
      return new VccGlobalDeclarationContainerClass(targetNamespaceDeclaration, this);
    }


    public override void SetCompilationPart(CompilationPart compilationPart, bool recurse) {
      base.SetCompilationPart(compilationPart, recurse);
      VccTypeContract/*?*/ typeContract = this.Compilation.ContractProvider.GetTypeContractFor(this) as VccTypeContract;
      if (typeContract != null) typeContract.SetContainingType(this);
    }

    public override void SetMemberContainingTypeDeclaration(ITypeDeclarationMember member) {
      TypedefDeclaration/*?*/ typedef = member as TypedefDeclaration;
      if (typedef != null) {
        typedef.SetContainingTypeDeclaration(this); 
        return;
      }
      FunctionDeclaration/*?*/ functionDeclaration = member as FunctionDeclaration;
      if (functionDeclaration != null) {
        functionDeclaration.SetContainingTypeDeclaration(this); 
        return;
      }
      base.SetMemberContainingTypeDeclaration(member);
    }

  }

  internal class VccArray : NestedStructDeclaration {
    internal VccArray(NameDeclaration name, List<ITypeDeclarationMember> members, uint arraySizeInBytes)
      : base(null, Flags.Sealed|(Flags)TypeMemberVisibility.Public, name, new List<GenericTypeParameterDeclaration>(0), new List<TypeExpression>(0), members, SourceDummy.SourceLocation)
      //^ requires arraySizeInBytes > 0;
    {
      this.arraySizeInBytes = arraySizeInBytes;
    }

    protected VccArray(TypeDeclaration containingTypeDeclaration, VccArray template)
      : base(containingTypeDeclaration, template)
    {
    }

    protected VccArray(TypeDeclaration containingTypeDeclaration, VccArray template, List<ITypeDeclarationMember> members)
      : base(containingTypeDeclaration, template, members)
    {
    }

    //^ [MustOverride]
    protected override NestedTypeDeclaration MakeShallowCopy(List<ITypeDeclarationMember> members)
      //^^ ensures result.GetType() == this.GetType();
    {
      return new VccArray(this.ContainingTypeDeclaration, this, members);
    }

    //^ [MustOverride]
    public override ITypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new VccArray(targetTypeDeclaration, this);
    }

    /// <summary>
    /// Size of an object of this type. In bytes. If zero, the size is unspecified and will be determined at runtime.
    /// </summary>
    public override uint SizeOf {
      get
        //^^ ensures result >= 0;
      {
        return this.arraySizeInBytes;
      }
    }
    readonly uint arraySizeInBytes;
    //^ invariant arraySizeInBytes > 0;

  }

  internal class VccEnumDeclaration : NamespaceEnumDeclaration {
    internal VccEnumDeclaration(NameDeclaration name, TypeExpression underlyingType, List<ITypeDeclarationMember> members, ISourceLocation sourceLocation)
      : base(null, Flags.None, name, underlyingType, members, sourceLocation) 
    {
    }

    protected VccEnumDeclaration(NamespaceDeclaration containingNamespaceDeclaration, VccEnumDeclaration template)
      : base(containingNamespaceDeclaration, template) {
    }

    //^ [MustOverride]
    public override INamespaceDeclarationMember MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.ContainingNamespaceDeclaration) return this;
      return new VccEnumDeclaration(targetNamespaceDeclaration, this);
    }
   }

  internal abstract class VccStructuredTypeDeclaration : NamespaceStructDeclaration
  {
    protected VccStructuredTypeDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(null, Flags.None, name, new List<GenericTypeParameterDeclaration>(0), new List<TypeExpression>(0), members, sourceLocation) {
      this.extendedAttributes = extendedAttributes;
    }

    protected VccStructuredTypeDeclaration(NamespaceDeclaration containingNamespaceDeclaration, VccStructuredTypeDeclaration template)
      : base(containingNamespaceDeclaration, template) {
      this.extendedAttributes = new List<Specifier>(template.extendedAttributes);
    }

    protected override List<ICustomAttribute> GetAttributes() {
      var result = base.GetAttributes();
      IEnumerable<SourceCustomAttribute> attributesFromDeclSpec = FunctionDefinition.ConvertSpecifiersIntoAttributes(
        this.extendedAttributes,
        new DummyExpression(this.DummyBlock, SourceDummy.SourceLocation));
      foreach (SourceCustomAttribute extAttr in attributesFromDeclSpec)
        result.Add(new CustomAttribute(extAttr));
      return result;
    }

    /// <summary>
    /// Layout of the type declaration.
    /// </summary>
    public override LayoutKind Layout {
      get { return LayoutKind.Explicit; }
    }

    public override void SetCompilationPart(CompilationPart compilationPart, bool recurse) {
      base.SetCompilationPart(compilationPart, recurse);
      VccTypeContract/*?*/ typeContract = this.Compilation.ContractProvider.GetTypeContractFor(this) as VccTypeContract;
      if (typeContract != null) typeContract.SetContainingType(this);
    }

    readonly IEnumerable<Specifier> extendedAttributes;

    public override TypeMemberVisibility GetDefaultVisibility() {
      return TypeMemberVisibility.Public;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound()
    {
      return base.CheckForErrorsAndReturnTrueIfAnyAreFound() ||
             VccStructuredTypeDeclaration.HasTypeCycle(this.TypeDefinition, this.Helper) ||
             VccStructuredTypeDeclaration.HasFieldOfUnspecifiedType(this.TypeDefinition, this.TypeDefinition.Members, this.Helper);
    }

    internal static bool HasFieldOfUnspecifiedType(ITypeReference type,  IEnumerable<ITypeDefinitionMember> members, LanguageSpecificCompilationHelper helper)
    {
      bool errorFound = false;
      foreach (var member in members)
      {
        var field = member as IFieldDefinition;
        if (field != null && field.Type == helper.Compilation.PlatformType.SystemVoid.ResolvedType)
        {
          var fieldDecl = ((Cci.Ast.FieldDefinition) field).Declaration as FieldDefinition;
          var location = IteratorHelper.First(helper.Compilation.SourceLocationProvider.GetPrimarySourceLocationsFor(type.Locations));
            helper.ReportError(
              new VccErrorMessage(location,
                                  Error.IllegalUseOfUndefinedType,
                                  field.Name.Value,
                                  fieldDecl != null ? fieldDecl.Type.SourceLocation.Source : helper.GetTypeName(field.Type.ResolvedType)));
          errorFound = true;
        }
      }

      return errorFound;
    }

    internal static bool HasTypeCycle(ITypeReference type, LanguageSpecificCompilationHelper helper) {
      return VccStructuredTypeDeclaration.HasTypeCycle(type, null, new Stack<ITypeReference>(), helper);
    }

    private static readonly Dictionary<ITypeReference, bool> typesWithKnownLoops = new Dictionary<ITypeReference, bool>();

    private static bool HasTypeCycle(ITypeReference type, IFieldDefinition/*?*/ offendingField, Stack<ITypeReference> seenTypes, LanguageSpecificCompilationHelper helper) {

      if (type.TypeCode != PrimitiveTypeCode.NotPrimitive ||
          !type.ResolvedType.IsStruct) return false;

      lock (GlobalLock.LockingObject) {
        if (typesWithKnownLoops.ContainsKey(type)) return true;
      }

      if (seenTypes.Contains(type)) {
        lock (GlobalLock.LockingObject) {
          if (!typesWithKnownLoops.ContainsKey(type)) {
            typesWithKnownLoops.Add(type, true);
            var location = IteratorHelper.First(helper.Compilation.SourceLocationProvider.GetPrimarySourceLocationsFor(type.Locations));
            helper.ReportError(
              new VccErrorMessage(location,
                Error.ValueTypeLayoutCycle, offendingField.Name.Value, helper.GetTypeName(type.ResolvedType)));
          }
        }
        return true;
      }

      seenTypes.Push(type);
      bool hasCycle = false;
      foreach (var field in IteratorHelper.GetFilterEnumerable<ITypeDefinitionMember, IFieldDefinition>(type.ResolvedType.Members)) {
        if (!field.IsStatic) {
          hasCycle |= VccStructuredTypeDeclaration.HasTypeCycle(field.Type, field, seenTypes, helper);
        }
      }

      seenTypes.Pop();
      return hasCycle;
    }

    public override ushort Alignment {
      get {
        if (this.HasErrors) return 1;
        return TypeHelper.TypeAlignment(this.TypeDefinition, false);
      }
    }
  }

  internal abstract class VccNestedStructuredTypeDeclaration : NestedStructDeclaration {
    protected VccNestedStructuredTypeDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(null, Flags.None|(Flags)TypeMemberVisibility.Public, name, new List<GenericTypeParameterDeclaration>(0), new List<TypeExpression>(0), members, sourceLocation)
    {
      this.extendedAttributes = extendedAttributes;
    }

    protected VccNestedStructuredTypeDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedStructuredTypeDeclaration template)
      : base(containingTypeDeclaration, template)
    {
      this.extendedAttributes = new List<Specifier>(template.extendedAttributes);
    }

    protected VccNestedStructuredTypeDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedStructuredTypeDeclaration template, List<ITypeDeclarationMember> members)
      : base(containingTypeDeclaration, template, members)
    {
      this.extendedAttributes = new List<Specifier>(template.ExtendedAttributes);
    }

    public IEnumerable<Specifier> ExtendedAttributes
    {
      get
      {
        return this.extendedAttributes;
      }
    }

    readonly IEnumerable<Specifier> extendedAttributes;

    protected override List<ICustomAttribute> GetAttributes() {
      var result = base.GetAttributes();
      IEnumerable<SourceCustomAttribute> attributesFromDeclSpec = FunctionDefinition.ConvertSpecifiersIntoAttributes(
        this.extendedAttributes,
        new DummyExpression(this.DummyBlock, SourceDummy.SourceLocation));
      foreach (SourceCustomAttribute extAttr in attributesFromDeclSpec)
        result.Add(new CustomAttribute(extAttr));
      return result;
    }

    /// <summary>
    /// Layout of the type declaration.
    /// </summary>
    public override LayoutKind Layout {
      get { return LayoutKind.Explicit; }
    }

    // to prevent warning about unverifiable code

    public override TypeMemberVisibility GetDefaultVisibility()
    {
      return TypeMemberVisibility.Public;
    }

    public override ushort Alignment {
      get {
        if (this.HasErrors) return 1;
        return TypeHelper.TypeAlignment(this.NestedTypeDefinition, false); 
      }
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound()
    {
      return base.CheckForErrorsAndReturnTrueIfAnyAreFound() ||
             VccStructuredTypeDeclaration.HasTypeCycle(this.TypeDefinition, this.Helper) ||
             VccStructuredTypeDeclaration.HasFieldOfUnspecifiedType(this.TypeDefinition, this.TypeDefinition.Members, this.Helper);

    }
  }

  internal class VccStructDeclaration : VccStructuredTypeDeclaration {

    internal VccStructDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(name, members, extendedAttributes, sourceLocation) {
    }

    internal bool IsAbstractType;

    protected VccStructDeclaration(NamespaceDeclaration containingNamespaceDeclaration, VccStructDeclaration template)
      : base(containingNamespaceDeclaration, template) {
    }

    /// <summary>
    /// Use compute field offset to get the offset. 
    /// </summary>
    /// <param name="item"> Field whose offset is of concern. </param>
    /// <returns></returns>
    public override uint GetFieldOffset(object item) {
      FieldDeclaration field = item as FieldDeclaration;
      if (field != null)
        return MemberHelper.ComputeFieldOffset(field.FieldDefinition, field.FieldDefinition.ContainingTypeDefinition);
      else
        return MemberHelper.ComputeFieldOffset((INestedTypeDefinition)item, this.TypeDefinition);
    }

    public override uint SizeOf {
      get {
        if (this.HasErrors) return 1;
        return TypeHelper.SizeOfType(this.TypeDefinition, false);
      }
    }


    //^ [MustOverride]
    public override INamespaceDeclarationMember MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.ContainingNamespaceDeclaration) return this;
      return new VccStructDeclaration(targetNamespaceDeclaration, this);
    }
  }

  internal class VccDatatypeDeclaration : VccStructuredTypeDeclaration, IVccDatatypeDeclaration {

    internal VccDatatypeDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, IEnumerable<FunctionDeclaration> ctors, ISourceLocation sourceLocation)
      : base(name, members, extendedAttributes, sourceLocation) {
        this.Constructors = ctors;
    }

    protected VccDatatypeDeclaration(NamespaceDeclaration containingNamespaceDeclaration, VccDatatypeDeclaration template)
      : base(containingNamespaceDeclaration, template) {
        this.Constructors = template.Constructors;
    }

    public override uint SizeOf {
      get {
        return 1;
      }
    }

    public IEnumerable<FunctionDeclaration> Constructors { get; private set; }

    //^ [MustOverride]
    public override INamespaceDeclarationMember MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.ContainingNamespaceDeclaration) return this;
      return new VccDatatypeDeclaration(targetNamespaceDeclaration, this);
    }
  }

  internal class VccNestedStructDeclaration : VccNestedStructuredTypeDeclaration {

    internal VccNestedStructDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(name, members, extendedAttributes, sourceLocation)
    {
    }

    protected VccNestedStructDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedStructDeclaration template)
      : base(containingTypeDeclaration, template)
    {
    }

    protected VccNestedStructDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedStructDeclaration template, List<ITypeDeclarationMember> members)
      : base(containingTypeDeclaration, template, members)
    {
    }

    public override uint SizeOf {
      get {
        if (this.HasErrors) return 1;
        return TypeHelper.SizeOfType(this.NestedTypeDefinition, false);
      }
    }

    public override uint GetFieldOffset(object item)
    {
      FieldDeclaration field = item as FieldDeclaration;
      INestedTypeDefinition nestedTypeDef = item as INestedTypeDefinition;
      uint result = field != null ? MemberHelper.ComputeFieldOffset(field.FieldDefinition, field.FieldDefinition.ContainingTypeDefinition) : MemberHelper.ComputeFieldOffset(nestedTypeDef, this.TypeDefinition);

      // This distinguishes between anonymous nested types, where we need to walk upwards to the surrounding type,
      // and nested types that have their own field name, where we must not do this
      // the current AST representation requires such a complicated approach
      bool nestedTypeHasFieldName = false;
      ITypeDefinition containingDef = this.ContainingTypeDeclaration.TypeDefinition;
      foreach (ITypeDefinitionMember member in containingDef.Members) {
        IFieldDefinition fieldMember = member as IFieldDefinition;
        if (fieldMember != null && fieldMember.Type.ResolvedType == this.TypeDefinition && !String.IsNullOrEmpty(fieldMember.Name.Value)) {
          nestedTypeHasFieldName = true;
          break;
        }
      }
      if (!nestedTypeHasFieldName)
        result += this.ContainingTypeDeclaration.GetFieldOffset(this.TypeDefinition);
      return result;
    }

    //^ [MustOverride]
    protected override NestedTypeDeclaration MakeShallowCopy(List<ITypeDeclarationMember> members)
    //^^ ensures result.GetType() == this.GetType();
    {
      return new VccNestedStructDeclaration(this.ContainingTypeDeclaration, this, members);
    }

    //^ [MustOverride]
    public override ITypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration)
    {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new VccNestedStructDeclaration(targetTypeDeclaration, this);
    }

    public override void SetCompilationPart(CompilationPart compilationPart, bool recurse)
    {
      base.SetCompilationPart(compilationPart, recurse);
      VccTypeContract/*?*/ typeContract = this.Compilation.ContractProvider.GetTypeContractFor(this) as VccTypeContract;
      if (typeContract != null) typeContract.SetContainingType(this);
    }
  }

  internal class VccUnionDeclaration : VccStructuredTypeDeclaration {
    internal VccUnionDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(name, members, extendedAttributes, sourceLocation) 
    {
    }

    protected VccUnionDeclaration(NamespaceDeclaration containingNamespaceDeclaration, VccUnionDeclaration template)
      : base(containingNamespaceDeclaration, template) {
    }


    //^ [MustOverride]
    public override INamespaceDeclarationMember MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.ContainingNamespaceDeclaration) return this;
      return new VccUnionDeclaration(targetNamespaceDeclaration, this);
    }

    public override uint SizeOf {
      get { 
        if (this.HasErrors) return 1;
        return ComputeSizeOf(this.TypeDeclarationMembers); 
      }
    }

    internal static uint ComputeSizeOf(IEnumerable<ITypeDeclarationMember> members)
    {
      uint size = 0;
      foreach (ITypeDeclarationMember member in members) {
        AnonymousFieldDefinition anonFieldDef = member as AnonymousFieldDefinition;
        if (anonFieldDef != null) {
          uint memberSize = TypeHelper.SizeOfType(anonFieldDef.Type.ResolvedType);
          size = Math.Max(size, memberSize);
          continue;
        }
        FieldDefinition/*?*/ fieldDef = member as FieldDefinition;
        if (fieldDef != null && !fieldDef.IsStatic && !fieldDef.IsCompileTimeConstant) {
          uint memberSize;
          VccArrayTypeExpression/*?*/ arrayType = fieldDef.Type as VccArrayTypeExpression;
          if (arrayType != null && arrayType.Size != null) {
            uint numElements = (uint)arrayType.SizeAsInt32;
            memberSize = numElements * TypeHelper.SizeOfType(arrayType.ElementType.ResolvedType);
          } else {
            memberSize = TypeHelper.SizeOfType(fieldDef.Type.ResolvedType);
          }
          size = Math.Max(size, memberSize);
          continue;
        }
        BitFieldDefinition bfieldDef = member as BitFieldDefinition;
        if (bfieldDef != null && !bfieldDef.IsStatic && !bfieldDef.IsCompileTimeConstant) {
          uint memberSize = TypeHelper.SizeOfType(bfieldDef.Type.ResolvedType);
          size = Math.Max(size, memberSize);
          continue;
        }
      }
      return size;
    }
  }

  internal class VccNestedUnionDeclaration : VccNestedStructuredTypeDeclaration {

    internal VccNestedUnionDeclaration(NameDeclaration name, List<ITypeDeclarationMember> members, IEnumerable<Specifier> extendedAttributes, ISourceLocation sourceLocation)
      : base(name, members, extendedAttributes, sourceLocation)
    {
    }

    protected VccNestedUnionDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedUnionDeclaration template)
      : base(containingTypeDeclaration, template)
    {
    }

    protected VccNestedUnionDeclaration(TypeDeclaration containingTypeDeclaration, VccNestedUnionDeclaration template, List<ITypeDeclarationMember> members)
      : base(containingTypeDeclaration, template, members)
    {
    }

    public override uint SizeOf {
      get { return VccUnionDeclaration.ComputeSizeOf(this.TypeDeclarationMembers); }
    }

    public override uint GetFieldOffset(object item)
    {
      return this.ContainingTypeDeclaration.GetFieldOffset(this.TypeDefinition);
    }

    //^ [MustOverride]
    protected override NestedTypeDeclaration MakeShallowCopy(List<ITypeDeclarationMember> members)
    //^^ ensures result.GetType() == this.GetType();
    {
      return new VccNestedUnionDeclaration(this.ContainingTypeDeclaration, this, members);
    }

    //^ [MustOverride]
    public override ITypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration)
    {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new VccNestedUnionDeclaration(targetTypeDeclaration, this);
    }

    public override void SetCompilationPart(CompilationPart compilationPart, bool recurse)
    {
      base.SetCompilationPart(compilationPart, recurse);
      VccTypeContract/*?*/ typeContract = this.Compilation.ContractProvider.GetTypeContractFor(this) as VccTypeContract;
      if (typeContract != null) typeContract.SetContainingType(this);
    }
  }

  public class VccFunctionPointerType : Microsoft.Cci.Immutable.FunctionPointerType
  {
    private readonly NameDeclaration name;

    public VccFunctionPointerType(NameDeclaration name, ISignature signature, IInternFactory internFactory)
      : base(signature, internFactory)
    {
      this.name = name;
    }

    public VccFunctionPointerType(NameDeclaration name, CallingConvention callingConvention, bool returnValueIsByRef, ITypeReference type, IEnumerable<ICustomModifier> returnValueCustomModifiers, IEnumerable<IParameterTypeInformation> parameters, IEnumerable<IParameterTypeInformation> extraArgumentTypes, IInternFactory internFactory)
      : base(callingConvention, returnValueIsByRef, type, returnValueCustomModifiers, parameters, extraArgumentTypes, internFactory)
    {
      this.name = name;
    }

    public NameDeclaration Name
    {
      get { return this.name; }
    }
  }
}