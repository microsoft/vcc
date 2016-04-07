//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using Microsoft.Cci.Immutable;
using Microsoft.Research.Vcc.Parsing;
using IMethodContract = Microsoft.Cci.Contracts.IMethodContract;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  public interface ISpecItem
  {
    bool IsSpec { get; }
  }

  public sealed class AnonymousFieldDefinition : FieldDeclaration {

    internal AnonymousFieldDefinition(FieldDeclaration.Flags flags, TypeExpression type, AnonymousFieldDeclarator fieldDeclarator) :
      base(null, flags | FieldDeclaration.Flags.Unsafe, TypeMemberVisibility.Public, type, fieldDeclarator.Identifier, null, type.SourceLocation) {
        this.specMemberName = fieldDeclarator.SpecMemberName;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    //^ [NotDelayed]
    private AnonymousFieldDefinition(TypeDeclaration containingTypeDeclaration, AnonymousFieldDefinition template)
      : base(containingTypeDeclaration, template)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
      this.specMemberName = template.SpecMemberName;
    }

    private readonly NameDeclaration specMemberName;

    public NameDeclaration SpecMemberName {
      get {
        return specMemberName;
      }
    }

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target type declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target type declaration it
    /// returns itself.
    /// </summary>
    //^ [Pure]
    public override TypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new AnonymousFieldDefinition(targetTypeDeclaration, this);
    }
  }

  public sealed class BitFieldDefinition : BitFieldDeclaration {

    public BitFieldDefinition(List<Specifier> extendedAttributes, Expression bitLength, FieldDeclaration.Flags flags, TypeExpression type, NameDeclaration name, Expression/*?*/ initializer, ISourceLocation sourceLocation)
      : base(null, bitLength, flags|FieldDeclaration.Flags.Unsafe, TypeMemberVisibility.Public, type, name, initializer, sourceLocation) {
      this.extendedAttributes = extendedAttributes;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    //^ [NotDelayed]
    private BitFieldDefinition(TypeDeclaration containingTypeDeclaration, BitFieldDefinition template)
      : base(containingTypeDeclaration, template)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
      this.extendedAttributes = template.extendedAttributes;
    }

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target type declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target type declaration it
    /// returns itself.
    /// </summary>
    //^ [Pure]
    public override TypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new BitFieldDefinition(targetTypeDeclaration, this);
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
    private readonly IList<Specifier> extendedAttributes;

    private BlockStatement DummyBlock {
      get {
        if (this.dummyBlock == null) {
          BlockStatement dummyBlock = BlockStatement.CreateDummyFor(this.SourceLocation);
          dummyBlock.SetContainers(this.ContainingTypeDeclaration.DummyBlock, this.ContainingTypeDeclaration);
          lock (this) {
            if (this.dummyBlock == null) {
              this.dummyBlock = dummyBlock;
            }
          }
        }
        return this.dummyBlock;
      }
    }
    //^ [Once]
    private BlockStatement/*?*/ dummyBlock;
  }

  public sealed class FieldDefinition : FieldDeclaration, ISpecItem {

    public FieldDefinition(List<Specifier> extendedAttributes, FieldDeclaration.Flags flags, TypeExpression type, NameDeclaration name, Expression/*?*/ initializer, bool isSpec, ISourceLocation sourceLocation)
      : base(null, flags|FieldDeclaration.Flags.Unsafe, TypeMemberVisibility.Public, type, name, initializer, sourceLocation) {
      this.extendedAttributes = extendedAttributes;
      this.isSpec = isSpec;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    //^ [NotDelayed]
    private FieldDefinition(TypeDeclaration containingTypeDeclaration, FieldDefinition template)
      : base(containingTypeDeclaration, template)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
      this.extendedAttributes = template.extendedAttributes;
      this.isSpec = template.isSpec;
    }

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target type declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target type declaration it
    /// returns itself.
    /// </summary>
    //^ [Pure]
    public override TypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new FieldDefinition(targetTypeDeclaration, this);
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

    public bool IsSpec {
      get { return this.isSpec; }
    }
    private readonly bool isSpec;
    private readonly IList<Specifier> extendedAttributes;

    private BlockStatement DummyBlock
    {
      get
      {
        if (this.dummyBlock == null) {
          BlockStatement dummyBlock = BlockStatement.CreateDummyFor(this.SourceLocation);
          dummyBlock.SetContainers(this.ContainingTypeDeclaration.DummyBlock, this.ContainingTypeDeclaration);
          lock (this) {
            if (this.dummyBlock == null) {
              this.dummyBlock = dummyBlock;
            }
          }
        }
        return this.dummyBlock;
      }
    }
    //^ [Once]
    private BlockStatement/*?*/ dummyBlock;


  }

  public sealed class FunctionDefinition : GlobalMethodDeclaration, ISpecItem {

    public FunctionDefinition(MethodDeclaration.Flags flags, IEnumerable<Specifier>/*?*/ specifiers,
      CallingConvention callingConvention, TypeMemberVisibility visibility, TypeExpression type, NameDeclaration name,
      List<GenericMethodParameterDeclaration>/*?*/ genericParameters, List<ParameterDeclaration>/*?*/ parameters, BlockStatement/*?*/ body, bool isSpec, Expression /*?*/ expansion, ISourceLocation sourceLocation)
      : base(null, flags|MethodDeclaration.Flags.Unsafe, visibility, type, name, genericParameters, parameters, body, sourceLocation)
    {
      this.specifiers = specifiers;
      this.callingConvention = callingConvention;
      this.parameters = parameters;
      this.isSpec = isSpec;
      this.expansion = expansion;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    //^ [NotDelayed]
    private FunctionDefinition(TypeDeclaration containingTypeDeclaration, FunctionDefinition template)
      : base(containingTypeDeclaration, template)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
      this.specifiers = template.specifiers;
      this.callingConvention = template.CallingConvention;
      this.parameters = template.parameters;
      this.isSpec = template.isSpec;
      //^ base;
    }

    public override CallingConvention CallingConvention {
      get { return this.callingConvention; }
    }

    readonly CallingConvention callingConvention;

    protected override GlobalMethodDefinition CreateGlobalMethodDefinition() {
      VccGlobalMethodDefinition globalMethodDefinition = new VccGlobalMethodDefinition(this);
      MethodContract/*?*/ contract = this.Compilation.ContractProvider.GetMethodContractFor(this) as MethodContract;
      if (contract != null)
        this.Compilation.ContractProvider.AssociateMethodWithContract(globalMethodDefinition, contract);
      return globalMethodDefinition;
    }

    //^ [Pure]
    public override TypeMemberVisibility GetDefaultVisibility() {
      return TypeMemberVisibility.Public;
    }
    protected override List<SourceCustomAttribute>/*?*/ GetSourceAttributes() {
      if (this.specifiers == null) return null;
      return FunctionDefinition.ConvertSpecifiersIntoAttributes(this.specifiers, new DummyExpression(this.ContainingTypeDeclaration.DummyBlock, SourceDummy.SourceLocation));
    }

    internal static List<SourceCustomAttribute> ConvertSpecifiersIntoAttributes(IEnumerable<Specifier> specifiers, Expression/*!*/ containingExpression)
    {
      List<SourceCustomAttribute> result = new List<SourceCustomAttribute>(1);
      foreach (Specifier specifier in specifiers) {
        DeclspecSpecifier/*?*/ declSpec = specifier as DeclspecSpecifier;
        if (declSpec != null) {
          List<Expression> arguments = new List<Expression>(declSpec.Modifiers);
          if (arguments.Count < 1) continue;
          Expression attributeTypeName = arguments[0];
          SimpleName/*?*/ simpleName = attributeTypeName as SimpleName;
          if (!(simpleName != null || attributeTypeName is QualifiedName || attributeTypeName is AliasQualifiedName)) continue;
          if (simpleName != null && IsUnsupportedDeclspec(simpleName.Name.Value)) continue;
          AttributeTypeExpression attributeType = new AttributeTypeExpression(attributeTypeName);
          arguments.RemoveAt(0);
          SourceCustomAttribute custAttr = new SourceCustomAttribute(AttributeTargets.All, attributeType, arguments, declSpec.SourceLocation);
          custAttr.SetContainingExpression(containingExpression);
          result.Add(custAttr);
        } else {
          SpecDeclspecSpecifier specTokenSpec = specifier as SpecDeclspecSpecifier;
          if (specTokenSpec != null) {
            var attrTypeName = NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(containingExpression.ContainingBlock.Compilation.NameTable, "StringVccAttr");
            AttributeTypeExpression attrType = new AttributeTypeExpression(attrTypeName);
            var argument = new CompileTimeConstant(specTokenSpec.Argument, specTokenSpec.SourceLocation);
            List<Expression> args = new List<Expression> { new CompileTimeConstant(specTokenSpec.Token, specTokenSpec.SourceLocation), argument };
            SourceCustomAttribute custAttr = new SourceCustomAttribute(AttributeTargets.All, attrType, args, specTokenSpec.SourceLocation);
            custAttr.SetContainingExpression(containingExpression);
            result.Add(custAttr);
          }
        }
      }
      result.TrimExcess();
      return result;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      bool result = false;
      var parameters = IteratorHelper.GetFilterEnumerable<ParameterDeclaration, VccParameterDeclaration>(this.Parameters);
      int physParCount = 0;

      foreach (var p in parameters) {
        if (!p.IsSpec) ++physParCount;
      }

      // check for duplicate parameter names or parameters of type void
      Dictionary<int, bool> seenParameters = new Dictionary<int, bool>();
      foreach (var p in parameters) {
        if (seenParameters.ContainsKey(p.Name.Name.UniqueKey)) {
          this.Helper.ReportError(new VccErrorMessage(p.SourceLocation, Error.DuplicateParameterName, p.Name.Value));
          result = true;
        } else
          seenParameters.Add(p.Name.UniqueKey, true);

        if (p.Type.HasErrors)
          result = true;
        else if (p.Type.ResolvedType.TypeCode == PrimitiveTypeCode.Void) {
          VccNameDeclaration vccParName = p.Name as VccNameDeclaration;
          if (physParCount != 1 || vccParName == null || !vccParName.IsCompilerGenerated || p.IsSpec) {
            string parNameToReport = p.Name.Value;
            if (vccParName != null && vccParName.IsCompilerGenerated) parNameToReport = String.Empty;
            VccNamedTypeExpression namedType = p.Type as VccNamedTypeExpression;
            if (namedType != null && (namedType.HasErrors || namedType.DidSilentlyResolveToVoid))
              this.Helper.ReportError(new VccErrorMessage(p.SourceLocation, Error.IllegalUseOfUndefinedType, parNameToReport, namedType.Expression.SourceLocation.Source));
            else
              this.Helper.ReportError(new AstErrorMessage(p, Microsoft.Cci.Ast.Error.IllegalUseOfType, parNameToReport, this.Helper.GetTypeName(this.PlatformType.SystemVoid.ResolvedType)));
            result = true;
          }
        }
      }
      result |= (this.expansion != null && (this.Expansion is DummyExpression || this.Expansion.HasErrors));

      return result;
      // do not recurse to the body because we trigger that check separately and checking it here would interfere with pruning
    }

    internal bool HasSingleVoidParameter {
      get {
        if (this.parameters != null && this.parameters.Count == 1)
          return this.parameters[0].Type.ResolvedType.TypeCode == PrimitiveTypeCode.Void;
        return false;
      }
    }

    public override bool IsHiddenBySignature {
      get { return false; }
    }

    public bool IsSpec {
      get { return this.isSpec; }
    }

    private readonly bool isSpec;

    public Expression /*?*/ Expansion {
      get {
        if (this.expansion == null) return null;
        if (this.convertedExpansion == null)
          this.convertedExpansion = GetConvertedExpansion();
        return convertedExpansion;
      }
    }

    private Expression GetConvertedExpansion() {
      if (this.expansion == null) return new DummyExpression(this.SourceLocation);
      var result = this.Helper.ImplicitConversionInAssignmentContext(this.expansion, this.Type.ResolvedType);
      if (result is DummyExpression && !this.expansion.HasErrors)
        this.Helper.ReportFailedImplicitConversion(this.expansion, this.Type.ResolvedType);
      return result;
    }

    private readonly Expression/*?*/ expansion;
    private Expression/*?*/ convertedExpansion;

    static private bool IsUnsupportedDeclspec(string spec) {
      if (spec[0] == 'n') {
        return (spec == "naked" || spec == "noalias" || spec == "noinline" || spec == "noreturn" ||
          spec == "nothrow" || spec == "novtable");
      }
      if (spec[0] == 'a') {
        return (spec == "allocate" || spec == "appdomain" || spec == "align");
      }

      if (spec[0] == 'd') {
        return (spec == "depreciated" || spec == "dllimport" || spec =="dllexport");
      }

      return (spec == "jitintrinsic" || spec =="process" || spec == "restrict" ||
        spec =="selectany" || spec == "thread" || spec == "uuid");
    }

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target type declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target type declaration it
    /// returns itself.
    /// </summary>
    //^ [MustOverride, Pure]
    public override TypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new FunctionDefinition(targetTypeDeclaration, this);
    }

    public override void SetContainingTypeDeclaration(TypeDeclaration containingTypeDeclaration, bool recurse) {
      base.SetContainingTypeDeclaration(containingTypeDeclaration, recurse);
      if (this.expansion != null) {
        var dummyExpression = new DummyExpression(this.DummyBlock, SourceDummy.SourceLocation);
        this.expansion.SetContainingExpression(dummyExpression);
      }
    }

    private readonly List<ParameterDeclaration>/*?*/ parameters;

    public override bool ReturnValueIsModified {
      get { return false; }
    }

    readonly IEnumerable<Specifier>/*?*/ specifiers;

    public override IEnumerable<ICustomModifier> ReturnValueCustomModifiers {
      get {
        return IteratorHelper.GetSingletonEnumerable<ICustomModifier>(new CustomModifier(true, this.PlatformType.SystemRuntimeCompilerServicesCallConvCdecl));
        //TODO: what about this.CallingConvention?
      }
    }

  }

  public sealed class FunctionDeclaration : CheckableSourceItem, ISignatureDeclaration, ITypeDeclarationMember, IAggregatableNamespaceDeclarationMember, ISpecItem  {
    public FunctionDeclaration(bool acceptsExtraArguments, IEnumerable<Specifier>/*?*/ specifiers, bool isExternal, CallingConvention callingConvention, TypeMemberVisibility visibility, TypeExpression type, NameDeclaration name,
      List<GenericMethodParameterDeclaration>/*?*/ templateParameters, List<ParameterDeclaration>/*?*/ parameters, bool isSpec, Expression /*?*/ expansion, ISourceLocation sourceLocation)
      : base(sourceLocation){
      this.acceptsExtraArguments = acceptsExtraArguments;
      this.callingConvention = callingConvention;
      this.isExternal = isExternal;
      this.name = name;
      this.parameters = parameters;
      this.specifiers = specifiers;
      this.templateParameters = templateParameters;
      this.type = type;
      this.visibility = visibility;
      this.isSpec = isSpec;
      this.expansion = expansion;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    //^ [NotDelayed]
    private FunctionDeclaration(TypeDeclaration containingTypeDeclaration, FunctionDeclaration template)
      : base(template.SourceLocation)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
      this.containingTypeDeclaration = containingTypeDeclaration;
      this.acceptsExtraArguments = template.AcceptsExtraArguments;
      this.callingConvention = template.callingConvention;
      this.isExternal = template.isExternal;
      this.name = template.Name;
      this.parameters = template.parameters;
      this.specifiers = template.specifiers;
      this.templateParameters = template.templateParameters;
      this.type = (TypeExpression)template.Type.MakeCopyFor(containingTypeDeclaration.DummyBlock);
      this.visibility = template.Visibility;
      //^ base;
      MethodContract/*?*/ contract = template.CompilationPart.Compilation.ContractProvider.GetMethodContractFor(template) as MethodContract;
      if (contract != null)
        this.CompilationPart.Compilation.ContractProvider.AssociateMethodWithContract(this, contract.MakeCopyFor(this.DummyBlock));
    }

    /// <summary>
    /// True if the method is a "vararg" method. That is, if it has a calling convention that allows extra arguments to be passed on the stack.
    /// In C++ such methods specify ... at the end of their parameter lists. In C#, the __arglist keyword is used.
    /// </summary>
    public bool AcceptsExtraArguments {
      get { return this.acceptsExtraArguments; }
    }

    readonly bool acceptsExtraArguments;

    public CallingConvention CallingConvention {
      get { return this.callingConvention; }
    }

    readonly CallingConvention callingConvention;

    public CompilationPart CompilationPart {
      get { return this.ContainingTypeDeclaration.CompilationPart; }
    }

    public TypeDeclaration ContainingTypeDeclaration {
      get {
        //^ assume this.containingTypeDeclaration != null;
        return this.containingTypeDeclaration;
      }
    }
    TypeDeclaration/*?*/ containingTypeDeclaration;

    private IMethodDefinition CreateForwardReferenceToMethodDefinition() {
      //TODO: if not compiling an object file give an error
      MethodDeclaration.Flags flags = MethodDeclaration.Flags.External;
      if (this.AcceptsExtraArguments) flags |= MethodDeclaration.Flags.AcceptsExtraArguments;
      FunctionDefinition externFunc = new FunctionDefinition(flags, this.specifiers, this.CallingConvention, TypeMemberVisibility.Public, this.Type, this.Name, this.templateParameters, this.parameters, null, this.isSpec, this.expansion, this.SourceLocation);
      externFunc.SetContainingTypeDeclaration(this.CompilationPart.GlobalDeclarationContainer, false);
      if (this.templateParameters != null) {
        foreach (GenericMethodParameterDeclaration templatePar in this.templateParameters) templatePar.SetDeclaringMethod(externFunc);
      }
      IMethodDefinition result = externFunc.MethodDefinition;
      this.TransferContract(result);
      return result;
    }


    /// <summary>
    /// Custom attributes that are to be persisted in the metadata.
    /// </summary>
    public IEnumerable<ICustomAttribute> Attributes
    {
      get
      {
        if (this.attributes == null) {
          List<ICustomAttribute> attrs = this.GetAttributes();
          attrs.TrimExcess();
          this.attributes = attrs.AsReadOnly();
        }
        return this.attributes;
      }
    }
    //^ [Once]
    IEnumerable<ICustomAttribute>/*?*/ attributes;

    /// <summary>
    /// Returns a list of custom attributes that describes this type declaration member.
    /// Typically, these will be derived from this.SourceAttributes. However, some source attributes
    /// might instead be persisted as metadata bits and other custom attributes may be synthesized
    /// from information not provided in the form of source custom attributes.
    /// </summary>
    private List<ICustomAttribute> GetAttributes()
    {
      List<ICustomAttribute> result = new List<ICustomAttribute>();
      foreach (SourceCustomAttribute sourceAttribute in this.SourceAttributes) {
        result.Add(new CustomAttribute(sourceAttribute));
      }
      return result;
    }

    /// <summary>
    /// Custom attributes that are explicitly specified in source. Some of these may not end up in persisted metadata.
    /// For example in C# a custom attribute is used to specify IFieldDefinition.IsNotSerialized. This custom attribute is deleted by the compiler.
    /// </summary>
    public IEnumerable<SourceCustomAttribute> SourceAttributes
    {
      [DebuggerNonUserCode]
      get
      {
        if (this.sourceAttributes == null)
          this.sourceAttributes = this.GetSourceAttributes();
        if (this.sourceAttributes != null) {
          for (int i = 0, n = this.sourceAttributes.Count; i < n; i++) {
            //^ assume this.sourceAttributes != null;
            yield return this.sourceAttributes[i] = this.sourceAttributes[i].MakeShallowCopyFor(this.ContainingTypeDeclaration.DummyBlock);
          }
        }
      }
    }
    List<SourceCustomAttribute>/*?*/ sourceAttributes;

    private List<SourceCustomAttribute>/*?*/ GetSourceAttributes()
    {
      if (this.specifiers == null) return null;
      return FunctionDefinition.ConvertSpecifiersIntoAttributes(this.specifiers, new DummyExpression(this.ContainingTypeDeclaration.DummyBlock, SourceDummy.SourceLocation));
    }

    public BlockStatement DummyBlock {
      get {
        if (this.dummyBlock == null) {
          BlockStatement dummyBlock = BlockStatement.CreateDummyFor(this.SourceLocation);
          dummyBlock.SetContainers(this.ContainingTypeDeclaration.DummyBlock, this);
          lock (this) {
            if (this.dummyBlock == null) {
              this.dummyBlock = dummyBlock;
            }
          }
        }
        return this.dummyBlock;
      }
    }
    //^ [Once]
    private BlockStatement/*?*/ dummyBlock;

    public TypeMemberVisibility GetDefaultVisibility() {
      return TypeMemberVisibility.Public;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      bool result = this.Type.HasErrors;
      return result;
    }  

    public bool IsExternal {
      get { return this.isExternal; }
    }
    readonly bool isExternal;

    public bool IsSpec {
      get { return this.isSpec; }
    }
    readonly bool isSpec;

    public bool IsNew {
      get { return false; }
    }

    public bool IsUnsafe {
      get { return true; }
    }

    public NameDeclaration Name {
      get { return this.name; }
    }
    readonly NameDeclaration name;

    public ITypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new FunctionDeclaration(targetTypeDeclaration, this);
    }

    /// <summary>
    /// The parameters of the referenced method.
    /// </summary>
    public IEnumerable<ParameterDeclaration> Parameters {
      get {
        List<ParameterDeclaration> parameters;
        if (this.parameters == null)
          yield break;
        else
          parameters = this.parameters;
        for (int i = 0, n = parameters.Count; i < n; i++)
          yield return parameters[i] = parameters[i].MakeShallowCopyFor(this, this.DummyBlock);
      }
    }
    readonly List<ParameterDeclaration>/*?*/ parameters;

    public IMethodDefinition ResolvedMethod {
      get {
        if (this.resolvedMethod == null)
          this.resolvedMethod = this.ResolveMethod();
        return this.resolvedMethod;
      }
    }
    //^ [Once]
    IMethodDefinition/*?*/ resolvedMethod;

    private IMethodDefinition ResolveMethod() {
      if (!this.ResolvedMember.IsForwardReference) return this.ResolvedMember;
      if (this.ResolvedMember.IsGeneric) return this.ResolvedMember;
      List<ITypeReference> parameterTypes = new List<ITypeReference>(this.parameters == null ? 0 : this.parameters.Count);
      foreach (ParameterDeclaration parDec in this.Parameters) parameterTypes.Add(parDec.Type.ResolvedType);
      if (parameterTypes.Count == 1 && parameterTypes[0].TypeCode == PrimitiveTypeCode.Void)
        parameterTypes.Clear();
      IMethodDefinition result = TypeHelper.GetMethod(this.VccCompilationHelper.Runtime, this.Name, parameterTypes.ToArray());
      if (result == Dummy.Method) {
        //TODO: run through referenced assemblies
        return this.ResolvedMember;
      }
      SourceContractProvider provider = this.CompilationPart.Compilation.ContractProvider;
      if (provider.GetMethodContractFor(result) == null) {
        IMethodContract/*?*/ contract = provider.GetMethodContractFor(this);
        if (contract != null)
          provider.AssociateMethodWithContract(result, contract);
      }
      return result;
    }

    private IMethodDefinition ResolvedMember {
      get {
        if (this.resolvedMember == null)
          this.resolvedMember = this.ResolveMember();
        return this.resolvedMember;
      }
    }
    //^ [Once]
    IMethodDefinition/*?*/ resolvedMember;

    private IMethodDefinition ResolveMember() {
      //This method is called while initializing this.CompilationPart.GlobalDeclarationContainer.TypeDefinition
      //and thus cannot depend on it being initialized. Instead, it searches the members of each compilation part separately.

      //Check if the compilation part containing this declaration has a matching definition
      foreach (ITypeDeclarationMember tdmem in this.CompilationPart.GlobalDeclarationContainer.GetTypeDeclarationMembersNamed(this.Name.UniqueKey)) {

        FunctionDefinition/*?*/ fdef = tdmem as FunctionDefinition;
        if (fdef != null && VccGlobalMethodDefinition.ParameterListsMatch(fdef.Parameters.GetEnumerator(), this.Parameters.GetEnumerator())) 
        {
          this.TransferContract(fdef.GlobalMethodDefinition);
          return fdef.GlobalMethodDefinition;
        }
      }

      if (this.templateParameters == null) {
        List<ITypeReference> parameterTypes = new List<ITypeReference>(this.parameters == null ? 0 : this.parameters.Count);
        foreach (ParameterDeclaration parDec in this.Parameters) parameterTypes.Add(parDec.Type.ResolvedType);
        if (parameterTypes.Count == 1 && parameterTypes[0].TypeCode == PrimitiveTypeCode.Void) {
          parameterTypes.Clear();
          //^ assert this.parameters != null;
          this.parameters.Clear();
        }
        IMethodDefinition result = TypeHelper.GetMethod(this.CompilationPart.GlobalDeclarationContainer.TypeDefinition, this.Name, parameterTypes.ToArray());
        if (result != Dummy.Method) {
          this.TransferContract(result);
          return result;
        }
      }

      return this.CreateForwardReferenceToMethodDefinition();
    }

    public void SetContainingTypeDeclaration(TypeDeclaration containingTypeDeclaration) {
      this.containingTypeDeclaration = containingTypeDeclaration;
      DummyExpression dummyExpression = new DummyExpression(this.DummyBlock, SourceDummy.SourceLocation);
      this.Type.SetContainingExpression(dummyExpression);
      if (this.parameters != null)
        foreach (ParameterDeclaration parameter in this.parameters) {
          parameter.SetContainingSignatureAndExpression(this, dummyExpression);
          parameter.Type.SetContainingExpression(dummyExpression);
        }
      if (this.templateParameters != null) {
        foreach (var tpar in this.templateParameters)
          tpar.SetContainingExpression(dummyExpression);
      }
      MethodContract/*?*/ contract = this.CompilationPart.Compilation.ContractProvider.GetMethodContractFor(this) as MethodContract;
      if (contract != null)
        contract.SetContainingBlock(this.DummyBlock);
    }

    readonly IEnumerable<Specifier>/*?*/ specifiers;

    internal List<GenericMethodParameterDeclaration>/*?*/ templateParameters;

    private void TransferContract(IMethodDefinition result)
    {
      SourceContractProvider provider = this.CompilationPart.Compilation.ContractProvider;
      IMethodContract/*?*/ contract = provider.GetMethodContractFor(this);
      if (contract != null) {
        if (provider.GetMethodContractFor(result) != null) {
          this.VccCompilationHelper.ReportError(new VccErrorMessage((result as ISourceItem).SourceLocation, Error.DiscardedContractAtDefinition, this.Name.Value));
        }
        provider.AssociateMethodWithContract(result, contract); //TODO: if result has a contract, make sure it is the same. If parameter names differ, do renames.
      }
    }
    

    /// <summary>
    /// An expression that denotes the return type of the referenced method.
    /// </summary>
    public TypeExpression Type {
      get { return this.type; }
    }
    readonly TypeExpression type;

    public ITypeDefinitionMember/*?*/ TypeDefinitionMember {
      get 
        //^ ensures result != null;
      {
        return this.ResolvedMethod; 
      }
    }

    private VccCompilationHelper VccCompilationHelper {
      get {
        return (VccCompilationHelper)this.CompilationPart.Helper;
      }
    }

    public TypeMemberVisibility Visibility {
      get { return this.visibility; }
    }
    readonly TypeMemberVisibility visibility;

    /// <summary>
    /// The expansion of a logic function, or null for normal functions
    /// </summary>
    public Expression/*?*/ Expansion {
      get { return this.expansion; }
    }
    readonly Expression/*?*/ expansion;

    #region IContainerMember<ITypeDeclaration> Members

    TypeDeclaration IContainerMember<TypeDeclaration>.Container {
      get { return this.ContainingTypeDeclaration; }
    }

    IName IContainerMember<TypeDeclaration>.Name {
      get { return this.Name; }
    }

    #endregion

    #region INamedEntity Members

    IName INamedEntity.Name {
      get { return this.Name; }
    }

    #endregion

    #region IDeclaration Members

    IEnumerable<ICustomAttribute> IDeclaration.Attributes {
      get { return Enumerable<ICustomAttribute>.Empty; }
    }

    IEnumerable<SourceCustomAttribute> IDeclaration.SourceAttributes {
      get { return Enumerable<SourceCustomAttribute>.Empty; }
    }

    #endregion

    #region ISignatureDeclaration Members

    ISignature ISignatureDeclaration.SignatureDefinition {
      get { return this.ResolvedMethod; }
    }

    #endregion

    #region IAggregatableNamespaceDeclarationMember Members

    INamespaceMember IAggregatableNamespaceDeclarationMember.AggregatedMember {
      [DebuggerNonUserCode]
      get { return (INamespaceMember)this.ResolvedMember; }
    }

    #endregion


    #region INamespaceDeclarationMember Members

    NamespaceDeclaration INamespaceDeclarationMember.ContainingNamespaceDeclaration {
      get { return this.CompilationPart.RootNamespace; }
    }

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target namespace declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target namespace declaration it
    /// returns itself. 
    /// </summary>
    INamespaceDeclarationMember INamespaceDeclarationMember.MakeShallowCopyFor(NamespaceDeclaration targetNamespaceDeclaration)
      //^^ requires targetNamespaceDeclaration.GetType() == this.ContainingNamespaceDeclaration.GetType();
      //^^ ensures result.GetType() == this.GetType();
      //^^ ensures result.ContainingNamespaceDeclaration == targetNamespaceDeclaration;
    {
      if (targetNamespaceDeclaration == this.CompilationPart.RootNamespace) return this;
      return (INamespaceDeclarationMember)this.MakeShallowCopyFor(targetNamespaceDeclaration.CompilationPart.GlobalDeclarationContainer);
    }

    #endregion

    #region IContainerMember<NamespaceDeclaration> Members

    NamespaceDeclaration IContainerMember<NamespaceDeclaration>.Container {
      get { return this.CompilationPart.RootNamespace; }
    }

    IName IContainerMember<NamespaceDeclaration>.Name {
      get { return this.Name; }
    }

    #endregion
  }

  /// <summary>
  /// Represents a global variable.
  /// </summary>
  public sealed class GlobalVariableDeclaration : GlobalFieldDeclaration {
    /// <summary>
    /// Allocates a global variable.
    /// </summary>
    /// <param name="flags">A set of flags that specify the value of boolean properties of the field, such as IsStatic.</param>
    /// <param name="visibility">Indicates if the member is public or confined to its containing type, derived types and/or declaring assembly.</param>
    /// <param name="type">An expression that denote the type of value that is stored in this field.</param>
    /// <param name="name">The name of the member. </param>
    /// <param name="initializer">An expression that evaluates to the initial value of this field. May be null.</param>
    /// <param name="sourceLocation">The source location corresponding to the newly allocated expression.</param>
    public GlobalVariableDeclaration(FieldDeclaration.Flags flags, TypeMemberVisibility visibility, TypeExpression type, NameDeclaration name, Expression/*?*/ initializer, ISourceLocation sourceLocation)
      : base(null, flags|FieldDeclaration.Flags.Static|FieldDeclaration.Flags.Unsafe, visibility, type, name, initializer, sourceLocation) {
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing type.
    /// </summary>
    /// <param name="containingTypeDeclaration">The containing type of the copied member. This should be different from the containing type of the template member.</param>
    /// <param name="template">The type member to copy.</param>
    private GlobalVariableDeclaration(TypeDeclaration containingTypeDeclaration, GlobalVariableDeclaration template)
      : base(containingTypeDeclaration, template)
      //^ ensures this.containingTypeDeclaration == containingTypeDeclaration;
    {
    }

    /// <summary>
    /// Adds zero or more assignments statements to the giving collection. Executing these statements will initialize the field.
    /// </summary>
    protected override void AddInitializingAssignmentsTo(ICollection<Statement> statements) {
      VccInitializer/*?*/ vcInit = this.Initializer as VccInitializer;
      if (vcInit != null) {
        VccArrayTypeExpression/*?*/ vcArrTypeExpr = this.Type as VccArrayTypeExpression;
        if (vcArrTypeExpr != null) {
          SimpleName fieldName = new SimpleName(this.Name, this.Name.SourceLocation, false);
          Expression pointerToField = fieldName;
          vcInit.AddInitializingElementAssignmentsTo(statements, pointerToField, vcArrTypeExpr);
          return;
        }

        VccNamedTypeExpression/*?*/ vcStructTypeExpr = this.Type as VccNamedTypeExpression;
        if (vcStructTypeExpr != null)
        {
          SimpleName varName = new SimpleName(this.Name, this.Name.SourceLocation, false);
          /* Because this is global variable, its type must be in the global scope, for which we can find the names of the fields. 
           * A mini-resolve to find the list of field names. The standard resolve will not work
           * because we are in the process of resolving when this method is called. 
           */
          SimpleName/*?*/ typeName = vcStructTypeExpr.Expression as SimpleName;
          if (typeName == null) return;
          int typeNameUniqueKey = typeName.Name.UniqueKey;
          VccStructuredTypeDeclaration/*?*/ typeDecl = null;
          foreach (VccStructuredTypeDeclaration td in 
            IteratorHelper.GetFilterEnumerable<INamespaceDeclarationMember, VccStructuredTypeDeclaration>(this.ContainingNamespaceDeclaration.Members)) {
            if (td.Name.UniqueKey == typeNameUniqueKey) {
              typeDecl = td;
              break;
            }
          }
          /* Now we send this field name list to generate assignment statements that initialize the fields of the current variable. */
          if (typeDecl != null) 
            vcInit.AddInitializingFieldAssignmentsTo(statements, varName, typeDecl);
          // TODO: name resolution error. 
          return;
        }
      }

      // if the initializer is a string, and the type is a char array, convert the string into an 
      // array initializer and continue
      VccByteStringLiteral stringLiteral = this.initializer as VccByteStringLiteral;
      VccArrayTypeExpression arrayType = this.Type as VccArrayTypeExpression;
      if (stringLiteral != null && arrayType != null) {
        string val = stringLiteral.Value as string;
        if (val != null) {
          // If the char array to be initialized doesnt have a size, set its size to hold the 
          // initial string literal plus 1 (for the terminating zero). 
          if (arrayType.Size == null) {
            CompileTimeConstant ctc = new CompileTimeConstant(val.Length + 1, stringLiteral.SourceLocation);
            ctc.SetContainingExpression(stringLiteral);
            arrayType.ResetSizeWhenProvidedByInitializer(ctc);
          }
          int size = arrayType.SizeAsInt32;
          Expression newInitializer = VccInitializer.fromStringWithPatchedZeros(val, size, stringLiteral);
          if (newInitializer != null) {
            this.initializer = newInitializer;
            this.AddInitializingAssignmentsTo(statements);
          }
        } 
      }
      base.AddInitializingAssignmentsTo(statements);
    }

    /// <summary>
    /// Returns a byte array representing the part of the process image to which this field will be mapped. Can be null.
    /// </summary>
    protected override byte[]/*?*/ GetMappedData() {
      VccInitializer/*?*/ vcInit = this.Initializer as VccInitializer;
      if (vcInit != null) return vcInit.GetMappedData();
      VccByteStringLiteral/*?*/ vcByteString = this.Initializer as VccByteStringLiteral;
      if (vcByteString != null) return vcByteString.GetMappedData();
      return null;
    }

    /// <summary>
    /// This field is mapped to an explicitly initialized (static) memory location.
    /// </summary>
    public override bool IsMapped {
      get {
        return this.IsReadOnly && this.Initializer != null && (this.Initializer is VccInitializer || this.Initializer is VccByteStringLiteral);
      }
    } 

    /// <summary>
    /// Makes a shallow copy of this member that can be added to the member list of the given target type declaration.
    /// The shallow copy may share child objects with this instance, but should never expose such child objects except through
    /// wrappers (or shallow copies made on demand). If this instance is already a member of the target type declaration it
    /// returns itself.
    /// </summary>
    //^ [MustOverride, Pure]
    public override TypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (targetTypeDeclaration == this.ContainingTypeDeclaration) return this;
      return new GlobalVariableDeclaration(targetTypeDeclaration, this);
    }
  }

  internal sealed class TemplateParameterDeclarator : Declarator {

    internal TemplateParameterDeclarator(NameDeclaration identifier, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.identifier = identifier;
    }

    internal override NameDeclaration Identifier {
      get { return this.identifier; }
    }
    readonly NameDeclaration identifier;

  }

  public sealed class TypedefDeclaration : CheckableSourceItem, ITypeDeclarationMember {

    public TypedefDeclaration(TypeExpression type, NameDeclaration name, IEnumerable<Specifier> specifiers, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.name = name;
      this.type = type;
      this.specifiers = specifiers;
    }

    public TypedefDeclaration(TypeExpression type, NameDeclaration name, ISourceLocation sourceLocation)
      : this(type, name, Enumerable<Specifier>.Empty, sourceLocation) {
    }

    private TypedefDeclaration(TypeDeclaration containingTypeDeclaration, TypedefDeclaration template)
      : base(template.SourceLocation) {
      this.containingTypeDeclaration = containingTypeDeclaration;
      this.name = template.name;
      this.type = template.type;
    }

    public CompilationPart CompilationPart {
      get { return this.ContainingTypeDeclaration.CompilationPart; }
    }

    public TypeDeclaration ContainingTypeDeclaration {
      get {
        //^ assume this.containingTypeDeclaration != null;
        return this.containingTypeDeclaration;
      }
    }
    TypeDeclaration/*?*/ containingTypeDeclaration;

    public bool IsVolatile {
      get { return VccCompilationHelper.ContainsTypeQualifier(specifiers, Token.Volatile); }
    }

    public bool IsConst {
      get { return VccCompilationHelper.ContainsTypeQualifier(specifiers, Token.Const); }
    }

    public bool IsNew {
      get { return false; }
    }

    public bool IsUnsafe {
      get { return true; }
    }

    public TypeMemberVisibility GetDefaultVisibility() {
      return TypeMemberVisibility.Public;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      bool result = this.Type.HasErrors;
      //TODO: check that typedef name is unique 
      return result;
    }

    public NameDeclaration Name {
      get { return this.name; }
    }
    readonly NameDeclaration name;

    public IEnumerable<Specifier> Specifiers {
      get { return this.specifiers; }
    }
    readonly IEnumerable<Specifier> specifiers;

    //^ [Pure]
    public ITypeDeclarationMember MakeShallowCopyFor(TypeDeclaration targetTypeDeclaration) {
      if (this.ContainingTypeDeclaration == targetTypeDeclaration) return this;
      return new TypedefDeclaration(targetTypeDeclaration, this);
    }

    public void SetContainingTypeDeclaration(TypeDeclaration containingTypeDeclaration) {
      this.containingTypeDeclaration = containingTypeDeclaration;
      BlockStatement containingBlock = containingTypeDeclaration.DummyBlock;
      DummyExpression containingExpression = new DummyExpression(containingBlock, SourceDummy.SourceLocation);
      this.Type.SetContainingExpression(containingExpression);
    }

    public TypeExpression Type {
      get { return this.type; }
    }

    readonly TypeExpression type;

    public ITypeDefinitionMember/*?*/ TypeDefinitionMember {
      get { return null; }
    }

    public TypeMemberVisibility Visibility {
      get { return this.GetDefaultVisibility(); }
    }

    #region IContainerMember<TypeDeclaration> Members

    TypeDeclaration IContainerMember<TypeDeclaration>.Container {
      get { return this.ContainingTypeDeclaration; }
    }

    IName IContainerMember<TypeDeclaration>.Name {
      get { return this.Name; }
    }

    #endregion

    #region INamedEntity Members

    IName INamedEntity.Name {
      get { return this.Name; }
    }

    #endregion

    #region IDeclaration Members

    IEnumerable<ICustomAttribute> IDeclaration.Attributes {
      get { return Enumerable<ICustomAttribute>.Empty; }
    }

    IEnumerable<SourceCustomAttribute> IDeclaration.SourceAttributes {
      get { return Enumerable<SourceCustomAttribute>.Empty; }
    }

    #endregion
  }

  internal abstract class Declarator : SourceItem {

    protected Declarator(ISourceLocation sourceLocation)
      : base(sourceLocation) {
    }

    internal abstract NameDeclaration Identifier {
      get;
    }

  }

  internal sealed class AnonymousFieldDeclarator : Declarator {

    internal AnonymousFieldDeclarator(NameDeclaration specMemberName)
      : base(specMemberName.SourceLocation) {
        this.specMemberName = specMemberName;
        this.identifier = new NameDeclaration(Dummy.Name, specMemberName.SourceLocation);
    }

    internal AnonymousFieldDeclarator()
      : base(SourceDummy.SourceLocation)
    {
      this.identifier = new NameDeclaration(Dummy.Name, SourceDummy.SourceLocation);
    }

    private readonly NameDeclaration specMemberName;

    public NameDeclaration SpecMemberName {
      get { return specMemberName; }
    }
    internal override NameDeclaration Identifier {
      get { return this.identifier; }
    }

    readonly NameDeclaration identifier;
  }

  internal sealed class ArrayDeclarator : Declarator {
    internal ArrayDeclarator(Declarator elementType, Expression/*?*/ arraySize, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.ElementType = elementType;
      this.ArraySize = arraySize;
    }

    internal readonly Expression/*?*/ ArraySize;
    internal Declarator ElementType;
    internal override NameDeclaration Identifier {
      get { return this.ElementType.Identifier; }
    }
  }

  internal sealed class BitfieldDeclarator : Declarator {
    internal BitfieldDeclarator(Declarator fieldDeclarator, Expression fieldSize, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.FieldDeclarator = fieldDeclarator;
      this.FieldSize = fieldSize;
    }

    internal readonly Declarator FieldDeclarator;
    internal readonly Expression FieldSize;
    internal override NameDeclaration Identifier {
      get { return this.FieldDeclarator.Identifier; }
    }
  }

  internal sealed class FunctionOrBlockContract
  {
    internal FunctionOrBlockContract() {
    }

    /// <summary>
    /// Create a shallow copy of the template
    /// </summary>
    internal FunctionOrBlockContract(FunctionOrBlockContract template) {
      this.HasContract = template.HasContract;
      this.Postconditions = template.Postconditions;
      this.Preconditions = template.Preconditions;
      this.Reads = template.Reads;
      this.Writes = template.Writes;
      this.IsPure = template.IsPure;
      this.Variants = template.Variants;
    }

    internal MethodContract ToMethodContract() {
      // TODO: leverage the IsPure flag
      return new MethodContract(null, null, null, this.Postconditions, this.Preconditions, this.Reads, null, this.Writes, this.IsPure, this.Variants);
    }

    internal void AddPostcondition(Postcondition postcondition) {
      if (this.Postconditions == null) {
        this.Postconditions = new List<Postcondition>();
        this.HasContract = true;
      }
      this.Postconditions.Add(postcondition);
    }

    internal void AddPrecondition(Precondition precondition) {
      if (this.Preconditions == null) {
        this.Preconditions = new List<Precondition>();
        this.HasContract = true;
      }
      this.Preconditions.Add(precondition);
    }

    internal void AddReads(Expression reads) {
      if (this.Reads == null) {
        this.Reads = new List<Expression>();
        this.HasContract = true;
      }
      this.Reads.Add(reads);
    }

    internal void AddReads(IEnumerable<Expression> reads) {
      if (this.Reads == null) {
        this.Reads = new List<Expression>();
        this.HasContract = true;
      }
      this.Reads.AddRange(reads);
    }

    internal void AddWrites(Expression writes) {
      if (this.Writes == null) {
        this.Writes = new List<Expression>();
        this.HasContract = true;
      }
      this.Writes.Add(writes);
    }

    internal void AddWrites(IEnumerable<Expression> writes) {
      if (this.Writes == null) {
        this.Writes = new List<Expression>();
        this.HasContract = true;
      }
      this.Writes.AddRange(writes);
    }

    internal void AddMethodVariant(Expression variant)
    {
      if (this.Variants == null)  {
        this.Variants = new List<Expression>();
        this.HasContract = true;
      }
      this.Variants.Add(variant);
    }

    internal void AddMethodVariants(IEnumerable<Expression> variants)
    {
      if (this.Variants == null) {
        this.Variants = new List<Expression>();
        this.HasContract = true;
      }
      this.Variants.AddRange(variants);
    }

    internal bool HasContract;
    internal bool IsPure;
    internal List<Postcondition>/*?*/ Postconditions;
    internal List<Precondition>/*?*/ Preconditions;
    internal List<Expression>/*?*/ Reads;
    internal List<Expression>/*?*/ Writes;
    internal List<Expression>/*?*/ Variants;
  }

  internal class FunctionDeclarator : Declarator {

    internal FunctionDeclarator(Declarator functionName, List<Parameter> parameters, List<TemplateParameterDeclarator> templateParameters, ISourceLocation sourceLocation)
      : base(sourceLocation)
    {
      this.Contract = new FunctionOrBlockContract();
      this.FunctionName = functionName;
      this.parameters = parameters;
      this.templateParameters = templateParameters;
    }

    internal FunctionDeclarator(Declarator functionName, FunctionDeclarator template)
      : base(functionName.SourceLocation)
    {
      this.FunctionName = functionName;
      this.parameters = template.Parameters;
      this.templateParameters = template.TemplateParameters;
      this.Specifiers = template.Specifiers;
      this.Contract = new FunctionOrBlockContract(template.Contract);
    }

    internal readonly Declarator FunctionName;
    internal List<Specifier>/*?*/ Specifiers;
    internal readonly FunctionOrBlockContract Contract;

    internal bool HasContract {
      get { return this.Contract.HasContract; }
    }

    private readonly List<TemplateParameterDeclarator> templateParameters;
    internal List<TemplateParameterDeclarator> TemplateParameters {
      get { return this.templateParameters; }
    }

    private List<Parameter> parameters;
    internal List<Parameter> Parameters  {
      get { return parameters; }
    }
    /* only used when we need to adjust the parameters in parsing complicated function 
     * declarations. */
    internal void ResetParameters(List<Parameter> newParameters)
    {
      this.parameters = newParameters;
    }

    internal override NameDeclaration Identifier
    {
      get { return this.FunctionName.Identifier; }
    }
  }

  internal sealed class Parameter : SourceItem, ISpecItem {

    internal Parameter(IEnumerable<Specifier> typeSpecifiers, Declarator name, bool isSpec, bool isOut, ISourceLocation sourceLocation)
      : this(typeSpecifiers, name, isSpec, isOut, sourceLocation, false) {
    }

    internal Parameter(IEnumerable<Specifier> typeSpecifiers, Declarator name, bool isSpec, bool isOut, ISourceLocation sourceLocation, bool isVarArgs)
      : base(sourceLocation) {
      this.typeSpecifiers = typeSpecifiers;
      this.Name = name;
      this.isSpec = isSpec;
      this.isOut = isOut;
      IsVarArgs = isVarArgs;
    }

    internal bool IsOut {
      get {
        if (this.isOut) return true;
        foreach (var spec in this.typeSpecifiers)
          if (spec is OutSpecifier) return true;
        return false;
      }
    }
    private readonly bool isOut;


    public bool IsSpec {
      get { return this.isSpec; }
    }

    private readonly bool isSpec;

    internal IEnumerable<Specifier> TypeSpecifiers {
      get {
        foreach (var spec in this.typeSpecifiers) {
          if (spec is OutSpecifier) continue;
          yield return spec;
        }
      }
    }

    internal readonly bool IsVarArgs;
    internal readonly Declarator Name;
    private readonly IEnumerable<Specifier> typeSpecifiers;
  }

  public class VccParameterDeclaration : ParameterDeclaration, ISpecItem
  {
    public VccParameterDeclaration(TypeExpression type, NameDeclaration name, IEnumerable<Specifier> specifiers, ushort index, bool isOut, bool isSpec, ISourceLocation sourceLocation)
      : base(null, type, name, null, index, false, isOut, false, false, sourceLocation) 
      //^ requires isParameterArray ==> type is ArrayTypeExpression;
    {
      this.specifiers = specifiers;
      this.isSpec = isSpec;
    }

    protected VccParameterDeclaration(ISignatureDeclaration containingSignature, BlockStatement containingBlock, VccParameterDeclaration template)
      : base(containingSignature, containingBlock, template) {
      this.specifiers = new List<Specifier>(template.specifiers);
      this.isSpec = template.isSpec;
    }

    public override ParameterDeclaration MakeShallowCopyFor(ISignatureDeclaration containingSignature, BlockStatement containingBlock)
    //^ ensures result.GetType() == this.GetType();
    {
      if (this.ContainingSignature == containingSignature) return this;
      return new VccParameterDeclaration(containingSignature, containingBlock, this);
    }

    protected override ParameterDefinition CreateParameterDefinition()
    {
      return new VccParameterDefinition(this, this.isSpec);
    }

    public bool IsSpec {
      get { return this.isSpec; }
    }

    private readonly bool isSpec;

    readonly IEnumerable<Specifier> specifiers;

  }

  public class VccParameterDefinition : ParameterDefinition, ISpecItem
  {
    protected internal VccParameterDefinition(VccParameterDeclaration declaration, bool isSpec)
      : base(declaration)
    {
      this.isSpec = isSpec;
    }

    public bool IsSpec {
      get { return this.isSpec; }
    }

    private readonly bool isSpec;
  }

  internal sealed class IdentifierDeclarator : Declarator {

    internal IdentifierDeclarator(NameDeclaration identifier)
      : base(identifier.SourceLocation) {
      this.identifier = identifier;
    }

    internal override NameDeclaration Identifier {
      get { return this.identifier; }
    }
    readonly NameDeclaration identifier;

    public override string ToString() {
      return identifier.ToString();
    }
  }

  internal sealed class InitializedDeclarator : Declarator {
    internal InitializedDeclarator(Declarator declarator, Expression initialValue, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.Declarator = declarator;
      this.InitialValue = initialValue;
    }

    internal readonly Declarator Declarator;
    internal override NameDeclaration Identifier {
      get { return this.Declarator.Identifier; }
    }
    internal readonly Expression InitialValue;
  }

  internal sealed class PointerDeclarator : Declarator {

    internal PointerDeclarator(List<Pointer> pointers, Declarator declarator, List<TypeQualifier> qualifiers, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.Pointers = pointers;
      this.Declarator = declarator;
      this.Qualifiers = qualifiers;
      }

    internal readonly List<TypeQualifier> /*?*/ Qualifiers;
    internal readonly List<Pointer> Pointers;
    internal Declarator Declarator;
    internal override NameDeclaration Identifier {
      get { return this.Declarator.Identifier; }
    }
  }

  internal sealed class Pointer : SourceItem {
    internal Pointer(List<TypeQualifier>/*?*/ qualifiers, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.Qualifiers = qualifiers;
    }

    internal readonly List<TypeQualifier>/*?*/ Qualifiers;
  }
}