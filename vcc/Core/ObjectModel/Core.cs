//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.SymbolStore;
using System.Resources;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using Microsoft.Cci.Immutable;
using Microsoft.Research.Vcc.Parsing;
using Microsoft.Research.Vcc.Preprocessing;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  /// <summary>
  /// An object that represents a source document, such as file, which is parsed by a Spec# compiler to produce the Spec# specific object model
  /// from which the language agnostic object model can be obtained.
  /// </summary>
  public interface IVccSourceDocument : ISourceDocument {
    /// <summary>
    /// The Vcc compilation part that corresponds to this Vcc source document.
    /// </summary>
    VccCompilationPart VccCompilationPart {
      get;
      // ^ ensures result.SourceLocation.SourceDocument == this;
    }
  }

  public class IsSpecVisitor : BaseCodeVisitor
  {
    private bool result;

    public override void Visit(IExpression expr) {
      expr.Dispatch(this);
    }

    public override void Visit(IAddressOf addressOf) {
      this.Visit(addressOf.Expression);
    }

    private void VisitDefinitionThenInstance(object definition, IExpression instance) {
      var localDef = definition as VccLocalDefinition;
      if (localDef != null) {
        if (localDef.IsSpec) result = true;
        var containingMethod = localDef.ContainingBlock.ContainingMethodDefinition as Microsoft.Research.Vcc.VccGlobalMethodDefinition;
        if (containingMethod != null && containingMethod.IsSpec) result = true;
      } else {
        var field = definition as Cci.Ast.FieldDefinition;
        if (field != null) {
          var fieldDef = field.Declaration as Vcc.FieldDefinition;
          if (fieldDef != null && fieldDef.IsSpec) result = true;
          else {
            var gVar = field.Declaration as GlobalVariableDeclaration;
            if (gVar != null) {
              var typeContract = gVar.Compilation.ContractProvider.GetTypeContractFor(gVar.ContainingTypeDeclaration);
              foreach (var cField in typeContract.ContractFields) {
                if (cField == field) {
                  result = true;
                  break;
                }
              }
            }
          }
        }
      }

      if (!result && instance != null) this.Visit(instance);
    }

    public override void Visit(IBoundExpression boundExpression) {
      var typeAsPtr = boundExpression.Type.ResolvedType as IPointerType;
      if (typeAsPtr != null) {
        if (VccCompilationHelper.IsSpecPointer(typeAsPtr)) result = true;
      } else this.VisitDefinitionThenInstance(boundExpression.Definition, boundExpression.Instance);
    }


    public override void Visit(IAddressableExpression addressableExpression) {
      this.VisitDefinitionThenInstance(addressableExpression.Definition, addressableExpression.Instance);
    }

    public static bool Check(IExpression expr) {
      var visitor = new IsSpecVisitor();
      visitor.Visit(expr);
      return visitor.result;
    }
  }


  public sealed class VccCompilation : Compilation {

    /// <summary>
    /// Do not use this constructor unless you are implementing the Compilation property of the Module class.
    /// I.e. to construct a Compilation instance, construct a Module instance and use its Compilation property. 
    /// </summary>
    internal VccCompilation(ISourceEditHost hostEnvironment, Unit result, VccOptions options, IEnumerable<CompilationPart> parts)
      : base(hostEnvironment, result, options)
      //^ requires result is VccModule || result is VccAssembly;
    {
      this.parts = parts;
    }

    public IMethodDefinition VoidSpecPtrOpVoidSpecPtr {
      [DebuggerNonUserCode]
      get {
        if (this.voidSpecPtrOpVoidSpecPtr == null) {
          lock (GlobalLock.LockingObject) {
            if (this.voidSpecPtrOpVoidSpecPtr == null) {
              var modifiers = new ICustomModifier[] { new CustomModifier(false, this.PlatformType.SystemDiagnosticsContractsContract) };
              ITypeDefinition voidSpecPtr = ModifiedPointerType.GetModifiedPointerType(this.PlatformType.SystemVoid.ResolvedType, modifiers, this.HostEnvironment.InternFactory).ResolvedType;
              this.voidSpecPtrOpVoidSpecPtr = BuiltinMethods.GetDummyOp(voidSpecPtr, voidSpecPtr, voidSpecPtr);
            }
          }
        }
        return this.voidSpecPtrOpVoidSpecPtr;
      }
    }
    IMethodDefinition/*?*/ voidSpecPtrOpVoidSpecPtr;

    internal VccStructDeclaration TypeStateFields {
      get { return this.typeStateFields; }
      set {
        if (this.typeStateFields != null) throw new InvalidOperationException();
        this.typeStateFields = value;
      }
    }

    VccStructDeclaration typeStateFields;

    protected override List<CompilationPart> GetPartList() {
      return new List<CompilationPart>(this.parts);
    }
    readonly IEnumerable<CompilationPart> parts;

    internal readonly VccOptions options = new VccOptions();

    public override Compilation UpdateCompilationParts(IEnumerable<CompilationPart> parts) {
      VccAssembly/*?*/ oldAssembly = this.Result as VccAssembly;
      if (oldAssembly != null) {
        VccAssembly newAssembly = new VccAssembly(oldAssembly.Name, oldAssembly.Location, this.HostEnvironment, this.options, oldAssembly.AssemblyReferences, oldAssembly.ModuleReferences, parts);
        return newAssembly.Compilation;
      }
      //^ assume this.Result is VccModule; //follows from constructor precondition and immutability.
      VccModule oldModule = (VccModule)this.Result;
      VccModule newModule = new VccModule(oldModule.Name, oldModule.Location, this.HostEnvironment, this.options, Dummy.Assembly, oldModule.AssemblyReferences, oldModule.ModuleReferences, parts);
      return newModule.Compilation;
    }
  }

  public sealed class VccCompilationPart : CompilationPart {

    public VccCompilationPart(VccCompilationHelper helper, ISourceLocation sourceLocation)
      : base(helper, sourceLocation, new VccGlobalDeclarationContainerClass(helper.Compilation.HostEnvironment))
      //^ requires sourceLocation.SourceDocument is VccCompositeDocument;
    {
    }

    internal VccArray GetFixedSizeArrayType(ITypeDefinition elementType, uint numberOfElements) {
      uint arraySizeInBytes = numberOfElements * TypeHelper.SizeOfType(elementType);
      VccArray/*?*/ result;
      lock (this) {
        Dictionary<ITypeDefinition, VccArray>/*?*/ arrayTypeTable2;
        if (this.arrayTypeTable.TryGetValue(arraySizeInBytes, out arrayTypeTable2)) {
          //^ assume arrayTypeTable2 != null;
          if (arrayTypeTable2.TryGetValue(elementType, out result)) {
            //^ assume result != null;
            return result;
          }
        } else {
          arrayTypeTable2 = new Dictionary<ITypeDefinition, VccArray>();
          this.arrayTypeTable.Add(arraySizeInBytes, arrayTypeTable2);
        }
        NameDeclaration fieldName = new NameDeclaration(this.Helper.NameTable.GetNameFor("_ElementType"), SourceDummy.SourceLocation);
        // Mangle the new type's name. Add an underscore to avoid name clash. 
        FieldDeclaration dummyField = 
          new FieldDeclaration(null, FieldDeclaration.Flags.Unsafe | FieldDeclaration.Flags.Static, TypeMemberVisibility.Private, TypeExpression.For(elementType), fieldName, null, SourceDummy.SourceLocation);
        List<ITypeDeclarationMember> members = new List<ITypeDeclarationMember>(1) {dummyField};
        NameDeclaration typeName = new NameDeclaration(this.Helper.NameTable.GetNameFor("_FixedArrayOfSize" + arraySizeInBytes + "_" + elementType), SourceDummy.SourceLocation);
        result = new VccArray(typeName, members, arraySizeInBytes);
        result.SetContainingTypeDeclaration(this.GlobalDeclarationContainer, true);
        arrayTypeTable2.Add(elementType, result);
      }
      this.GlobalDeclarationContainer.AddHelperMember(result);
      return result;
    }
    readonly Dictionary<uint, Dictionary<ITypeDefinition, VccArray>> arrayTypeTable = new Dictionary<uint, Dictionary<ITypeDefinition, VccArray>>();

    //^ [MustOverride]
    public override CompilationPart MakeShallowCopyFor(Compilation targetCompilation)
      //^^ ensures result.GetType() == this.GetType();
    {
      if (this.Compilation == targetCompilation) return this;
      ISourceLocation sloc = this.SourceLocation;
      VccCompositeDocument/*?*/ oldDocument = sloc.SourceDocument as VccCompositeDocument;
      //^ assume oldDocument != null; //follows from constructor precondition and immutability of sloc
      CompilationPart result = oldDocument.MakeShallowCopyFor(targetCompilation).VccCompilationPart;
      //^ assume result.GetType() == this.GetType();
      return result;
    }

    public override INamespaceDeclarationMember/*?*/ ParseAsNamespaceDeclarationMember(ISourceLocation sourceLocationBeforeEdit, ISourceDocumentEdit edit)
    {
      return null;
    }

    public override RootNamespaceDeclaration ParseAsRootNamespace() {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume sloc.SourceDocument is VccCompositeDocument;  //follows from constructor precondition and immutability of sloc
      VccRootNamespaceDeclaration result = new VccRootNamespaceDeclaration(this, sloc);
      this.rootNamespace = result;
      List<IErrorMessage> scannerAndParserErrors = ((VccCompositeDocument)this.SourceLocation.SourceDocument).ScannerAndParserErrors;
      scannerAndParserErrors.Clear();
      Parser parser = Parser.Create(this.Compilation, this.SourceLocation, scannerAndParserErrors); //TODO: get options from Compilation
      result.Parse(parser, this);
      ErrorEventArgs errorEventArguments = new ErrorEventArgs(ErrorReporter.Instance, this.SourceLocation, scannerAndParserErrors.AsReadOnly());
      this.Compilation.HostEnvironment.ReportErrors(errorEventArguments);
      errorEventArguments = new ErrorEventArgs(ErrorReporter.Instance, this.UnpreprocessedDocument.SourceLocation, this.PreprocessorErrors);
      this.Compilation.HostEnvironment.ReportErrors(errorEventArguments);
      return result;
    }

    public override ITypeDeclarationMember/*?*/ ParseAsTypeDeclarationMember(ISourceLocation sourceLocationBeforeEdit, ISourceDocumentEdit edit, IName typeName)
    {
      return null;
    }

    internal List<IErrorMessage> PreprocessorErrors {
      get {
        ISourceLocation sloc = this.SourceLocation;
        VccCompositeDocument/*?*/ sdoc = sloc.SourceDocument as VccCompositeDocument;
        //^ assume sdoc != null; //follows from constructor precondition and immutability of sloc
        return sdoc.PreprocessorErrors;
      }
    }

    public override RootNamespaceDeclaration RootNamespace {
      get
        //^ ensures result is VccRootNamespaceDeclaration;
      {
        if (this.rootNamespace == null) {
          lock (GlobalLock.LockingObject) {
            if (this.rootNamespace == null) {
              ISourceLocation sloc = this.SourceLocation;
              //^ assume sloc.SourceDocument is VccCompositeDocument;  //follows from constructor precondition and immutability of sloc
              this.rootNamespace = new VccRootNamespaceDeclaration(this, sloc);
            }
          }
        }
        //^ assume this.rootNamespace is VccRootNamespaceDeclaration; //The above assignment is the sole initialization of this.rootNamespace
        return this.rootNamespace;
      }
    }

    internal List<IErrorMessage> ScannerAndParserErrors {
      get {
        ISourceLocation sloc = this.SourceLocation;
        VccCompositeDocument/*?*/ sdoc = sloc.SourceDocument as VccCompositeDocument;
        //^ assume sdoc != null; //follows from constructor precondition and immutability of sloc
        return sdoc.ScannerAndParserErrors; 
      }
    }

    public override void SetContainingTypeDeclaration(ITypeDeclarationMember newMember, TypeDeclaration newNsType, bool recurse) {
      TypedefDeclaration/*?*/ typedefDeclaration = newMember as TypedefDeclaration;
      if (typedefDeclaration != null)
        typedefDeclaration.SetContainingTypeDeclaration(newNsType);
      else
        base.SetContainingTypeDeclaration(newMember, newNsType, recurse);
    }

    public override CompilationPart UpdateRootNamespace(RootNamespaceDeclaration rootNamespace)
      //^^ requires this.RootNamespace.GetType() == rootNamespace().GetType();
    {
      List<CompilationPart> newParts = new List<CompilationPart>(this.Compilation.Parts);
      Compilation newCompilation = this.Compilation.UpdateCompilationParts(newParts);
      //^ assume this.Helper is VccCompilationHelper; //The constructor's type signature ensures this.
      VccCompilationHelper helper = (VccCompilationHelper)this.Helper.MakeShallowCopyFor(newCompilation);
      //^ assume rootNamespace is VccRootNamespaceDeclaration; //follows from the precondition and the post condition of this.RootNamespace.
      ISourceLocation sloc = rootNamespace.SourceLocation;
      //^ assume sloc.SourceDocument is VccCompositeDocument; //follows from the precondition of the constructors of VccRootNamespaceDeclaration.
      VccCompilationPart result = new VccCompilationPart(helper, sloc) {rootNamespace = rootNamespace};
      for (int i = 0, n = newParts.Count; i < n; i++) {
        if (newParts[i] == this) { newParts[i] = result; break; }
      }
      return result;
    }

    internal ISourceDocument UnpreprocessedDocument {
      get {
        ISourceLocation sloc = this.SourceLocation;
        VccCompositeDocument/*?*/ sdoc = sloc.SourceDocument as VccCompositeDocument;
        //^ assume sdoc != null; //follows from constructor precondition and immutability of sloc
        return sdoc.UnpreprocessedDocument;
      }
    }

    internal VccCompilationHelper VccHelper {
      get {
        return (VccCompilationHelper)this.Helper;
      }
    }

  }

  public sealed class VccCompilationHelper : LanguageSpecificCompilationHelper {

    public VccCompilationHelper(Compilation compilation)
      : base(compilation, "Vcc") {
    }

    private VccCompilationHelper(Compilation targetCompilation, VccCompilationHelper template) 
      : base(targetCompilation, template) {
    }

    public static readonly string SystemDiagnosticsContractsCodeContractTypedPtrString = Microsoft.Cci.Ast.NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".TypedPtr";
    public static readonly string SystemDiagnosticsContractsCodeContractMapString = Microsoft.Cci.Ast.NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".Map";
    public static readonly string SystemDiagnosticsContractsCodeContractBigIntString = Microsoft.Cci.Ast.NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".BigInt";
    public static readonly string SystemDiagnosticsContractsCodeContractBigNatString = Microsoft.Cci.Ast.NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".BigNat";
    public static readonly string SystemDiagnosticsContractsCodeContractObjsetString = Microsoft.Cci.Ast.NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".Objset";

    static internal VccNamedTypeExpression GetBigIntType(INameTable nameTable) {
      var bigIntRef = NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(nameTable, "BigInt");
      return new VccNamedTypeExpression(bigIntRef);
    }

    static internal VccNamedTypeExpression GetBigIntType(INameTable nameTable, Expression containingExpression) {
      var result = GetBigIntType(nameTable);
      result.SetContainingExpression(containingExpression);
      return result;
    }

    static internal VccNamedTypeExpression GetBigNatType(INameTable nameTable) {
      var bigNatRef = NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(nameTable, "BigNat");
      return new VccNamedTypeExpression(bigNatRef);
    }

    static internal VccNamedTypeExpression GetBigNatType(INameTable nameTable, Expression containingExpression) {
      var result = GetBigNatType(nameTable);
      result.SetContainingExpression(containingExpression);
      return result;
    }


    internal ITypeDefinition/*?*/ GetFixedArrayElementType(ITypeDefinition fixedSizeArray) {
      if (fixedSizeArray.IsStruct) {
        IFieldDefinition field = TypeHelper.GetField(fixedSizeArray, this.NameTable.GetNameFor("_ElementType"));
        if (field != Dummy.Field) return field.Type.ResolvedType;
      }
      return null;
    }

    internal IPointerType/*?*/ GetPointerForFixedSizeArray(ITypeDefinition fixedSizeArray, bool isSpec) {
      ITypeDefinition/*?*/ elementType = this.GetFixedArrayElementType(fixedSizeArray);
      if (elementType == null) return null;
      if (isSpec)
        return this.MakeSpecPointer(elementType);
      else
        return PointerType.GetPointerType(elementType, this.Compilation.HostEnvironment.InternFactory);
    }

    private enum PtrConvKind
    { 
      None,
      VoidP,
      VoidSpecP,
      Ptr,
      SpecPtr,
      FuncP,
      ObjT,
      Int,
      Array
    }

    private enum ConvMethod
    {
      Implicit,
      Explicit,
      ExplicitAndImplicitIfZero,
      IncompatibleAndImplicitIfZero,
      Identity,
      Incompatible,
      Base
    }

    private static ConvMethod KindsToConvMethod(PtrConvKind src, PtrConvKind tgt) {

      if (src == PtrConvKind.None || tgt == PtrConvKind.None) return ConvMethod.Base;
      
      switch (src) {
        case PtrConvKind.VoidP:
          switch (tgt) {
            case PtrConvKind.Int:
              return ConvMethod.Explicit;
            case PtrConvKind.VoidSpecP:
            case PtrConvKind.SpecPtr:
              return ConvMethod.IncompatibleAndImplicitIfZero;
            default:
              return ConvMethod.Implicit;
          }

        case PtrConvKind.VoidSpecP:
          switch (tgt) {
            case PtrConvKind.ObjT:
            case PtrConvKind.SpecPtr:
            case PtrConvKind.VoidSpecP:
              return ConvMethod.Implicit;
            default:
              return ConvMethod.Incompatible;
          }

        case PtrConvKind.Ptr:
          switch (tgt) {
            case PtrConvKind.ObjT:
            case PtrConvKind.VoidP:
              return ConvMethod.Implicit;
            case PtrConvKind.SpecPtr:
            case PtrConvKind.VoidSpecP:
              return ConvMethod.Incompatible;
            default:
              return ConvMethod.Explicit;
          }

        case PtrConvKind.SpecPtr:
          switch (tgt) {
            case PtrConvKind.VoidSpecP:
            case PtrConvKind.ObjT:
              return ConvMethod.Implicit;
            case PtrConvKind.SpecPtr:
            case PtrConvKind.Array:
              return ConvMethod.Explicit;
            default:
              return ConvMethod.Incompatible;
          }

        case PtrConvKind.FuncP:
          switch (tgt) {
            case PtrConvKind.ObjT:
            case PtrConvKind.VoidP:
              return ConvMethod.Implicit;
            case PtrConvKind.SpecPtr:
            case PtrConvKind.VoidSpecP:
              return ConvMethod.Incompatible;
            default:
              return ConvMethod.Explicit;
          }

        case PtrConvKind.ObjT:
         switch (tgt) {
           case PtrConvKind.Int:
           case PtrConvKind.FuncP:
             return ConvMethod.Explicit;
           case PtrConvKind.VoidP:
           case PtrConvKind.ObjT:
           case PtrConvKind.VoidSpecP:
             return ConvMethod.Identity;
           default:
             return ConvMethod.Implicit;
         }

        case PtrConvKind.Int:
         switch (tgt) {
           case PtrConvKind.Int:
             return ConvMethod.Base;
           default:
             return ConvMethod.ExplicitAndImplicitIfZero;
         }
         
        default:
         System.Diagnostics.Debug.Assert(false);
         return ConvMethod.Incompatible;
      }
    }

    private PtrConvKind ToPtrConvKind(ITypeDefinition type, out IPointerType ptrTypeForArray) {
      ptrTypeForArray = null;
      if (TypeHelper.IsPrimitiveInteger(type))
        return PtrConvKind.Int;
      if (TypeHelper.GetTypeName(type) == SystemDiagnosticsContractsCodeContractTypedPtrString)
        return PtrConvKind.ObjT;
      //System.Diagnostics.Debug.Assert(!(type is IPointerType && !(type is IPointerType)));
      IPointerType typeAsPtrType = type as IPointerType;
      if (typeAsPtrType != null) {
        var isSpec = VccCompilationHelper.IsSpecPointer(typeAsPtrType);
        if (typeAsPtrType.TargetType.ResolvedType.TypeCode == PrimitiveTypeCode.Void)
          return isSpec ? PtrConvKind.VoidSpecP : PtrConvKind.VoidP;
        else {
          return isSpec ? PtrConvKind.SpecPtr : PtrConvKind.Ptr;
        }
      } else {
        if (type is IFunctionPointer)
          return PtrConvKind.FuncP;
        IPointerType arrayPtr = this.GetPointerForFixedSizeArray(type, false);
        if (arrayPtr != null) {
          ptrTypeForArray = arrayPtr;
          return PtrConvKind.Array;
        }
      }

      return PtrConvKind.None;
    }

    private static bool IsIntegralZero(Expression expression) {
      CompileTimeConstant cc = expression as CompileTimeConstant;
      return (cc != null && ExpressionHelper.IsIntegralZero(cc));
    }

    private class IsZeroVisitor : BaseCodeVisitor
    {
      private bool result;

      public override void Visit(ICompileTimeConstant constant) {
        result = ExpressionHelper.IsIntegralZero(constant);
      }

      public override void Visit(IConversion conversion) {
        this.Visit(conversion.ValueToConvert);
      }

      public override void Visit(IExpression expression) {
        expression.Dispatch(this);
      }

      public static bool IsZero(IExpression expression) {
        var visitor = new IsZeroVisitor();
        visitor.Visit(expression);
        return visitor.result;
      }
    }

    public static bool HasModifier(IPointerType type, INamespaceTypeReference modifier) {
      var modifiedPtr = type as IModifiedTypeReference;
      if (modifiedPtr != null) {
        foreach (var tmodifier in modifiedPtr.CustomModifiers) {
          if (tmodifier.Modifier.InternedKey == modifier.InternedKey)
            return true;
        }
      }
      return false;
    }

    public IPointerType MakeSpecPointer(ITypeReference targetType) {
      var modifier = new ICustomModifier[] { new CustomModifier(false, this.PlatformType.SystemDiagnosticsContractsContract) };
      return ModifiedPointerType.GetModifiedPointerType(targetType, modifier, this.Compilation.HostEnvironment.InternFactory);
    }

    public static bool IsSpecPointer(IPointerType type) {
      return HasModifier(type, type.PlatformType.SystemDiagnosticsContractsContract);
    }

    public static bool IsVolatilePointer(IPointerType type) {
      return HasModifier(type, type.PlatformType.SystemRuntimeCompilerServicesIsVolatile);
    }

    public static bool IsConstPointer(IPointerType type) {
      return HasModifier(type, type.PlatformType.SystemRuntimeCompilerServicesIsConst);
    }


    //^ [Pure]
    protected override Expression Conversion(Expression expression, ITypeDefinition targetType, bool isExplicitConversion, ISourceLocation sourceLocation) {

      // bool -> bool
      if (TypeHelper.TypesAreEquivalent(targetType, this.PlatformType.SystemBoolean) &&
          TypeHelper.TypesAreEquivalent(expression.Type, this.PlatformType.SystemBoolean))
        return expression;

      // * -> bool
      if (TypeHelper.TypesAreEquivalent(targetType, this.PlatformType.SystemBoolean))
        return this.ConversionExpression(expression, this.PlatformType.SystemBoolean.ResolvedType, sourceLocation);
      
      // bool -> int
      if (TypeHelper.TypesAreEquivalent(expression.Type, this.PlatformType.SystemBoolean) &&
          TypeHelper.IsPrimitiveInteger(targetType))
        return this.ConversionExpression(expression, targetType, sourceLocation);

      // int -> enum
      if (targetType.IsEnum && TypeHelper.IsPrimitiveInteger(expression.Type))
        return base.Conversion(expression, targetType, true, sourceLocation);

      // int -> mathint
      if (TypeHelper.GetTypeName(targetType) == SystemDiagnosticsContractsCodeContractBigIntString && TypeHelper.IsPrimitiveInteger(expression.Type))
        return this.ConversionExpression(expression, targetType, sourceLocation);

      if (TypeHelper.GetTypeName(targetType) == SystemDiagnosticsContractsCodeContractBigNatString && 
        (TypeHelper.IsUnsignedPrimitiveInteger(expression.Type) || (expression is CompileTimeConstant && expression.ValueIsPolymorphicCompileTimeConstant)))
        return this.ConversionExpression(expression, targetType, sourceLocation);

      IPointerType/*?*/ srcPointerType;
      IPointerType/*?*/ tgtPointerType;

      PtrConvKind srcKind = this.ToPtrConvKind(expression.Type, out srcPointerType);
      PtrConvKind tgtKind = this.ToPtrConvKind(targetType, out tgtPointerType);

      if (srcKind != PtrConvKind.None && tgtKind != PtrConvKind.None) {
        if (srcKind == PtrConvKind.Array) {
          AddressOf addressOf = new VccAddressOf(new AddressableExpression(expression), expression.SourceLocation);
          addressOf.SetContainingExpression(expression);
          return this.Conversion(addressOf, targetType, isExplicitConversion, sourceLocation);
        }

        var convKind = KindsToConvMethod(srcKind, tgtKind);
        if (convKind == ConvMethod.Identity) return expression;
        if (convKind == ConvMethod.Implicit ||
            convKind == ConvMethod.Explicit && isExplicitConversion ||
            convKind == ConvMethod.ExplicitAndImplicitIfZero && (isExplicitConversion || IsIntegralZero(expression)) ||
            convKind == ConvMethod.IncompatibleAndImplicitIfZero && IsZeroVisitor.IsZero(expression.ProjectAsIExpression()))
          return this.ConversionExpression(expression, targetType, sourceLocation);

        if (convKind == ConvMethod.Incompatible ||
            convKind == ConvMethod.IncompatibleAndImplicitIfZero) 
          return new DummyExpression(expression.ContainingBlock, expression.SourceLocation);
      }

      if (expression.Type == Dummy.Type) {
        IFunctionPointer/*?*/ functionPointer = targetType as IFunctionPointer;
        if (functionPointer != null) return this.ConversionFromMethodGroupToFunctionPointer(expression, functionPointer);
        IMethodDefinition/*?*/ method = this.ResolveToMethod(expression);
        if (method != null) {
          IPointerType/*?*/ pointer = targetType as IPointerType;
          bool intConversion = isExplicitConversion && TypeHelper.IsPrimitiveInteger(targetType);
          if (intConversion) pointer = this.PlatformType.SystemVoidPtr.ResolvedType as IPointerType;
          if (pointer != null && pointer.TargetType.ResolvedType.TypeCode == PrimitiveTypeCode.Void) {
            expression = this.AddAddressOfIfExpressionIsFunctionName(expression);
            Expression result = new Conversion(expression, pointer, expression.SourceLocation);
            if (intConversion) result = this.ConversionExpression(result, targetType);
            return result;
          }
        }
      }

      return base.Conversion(expression, targetType, isExplicitConversion, sourceLocation);
    }

    private IMethodDefinition/*?*/ ResolveToMethod(Expression expression) {
      VccSimpleName/*?*/ simpleName = expression as VccSimpleName;
      if (simpleName != null)
        return simpleName.Resolve() as IMethodDefinition;
      else {
        AddressOf/*?*/ addressOfExpression = expression as AddressOf;
        if (addressOfExpression != null)
          return addressOfExpression.Address.Definition as IMethodDefinition;
        Parenthesis/*?*/ parenthesis = expression as Parenthesis;
        if (parenthesis != null)
          return this.ResolveToMethod(parenthesis.ParenthesizedExpression);
        return null;
      }
    }

    public override string GetTypeName(ITypeDefinition typeDefinition)
    {
      switch (typeDefinition.TypeCode)
      {
        case PrimitiveTypeCode.Boolean:
          return "\\bool";
        case PrimitiveTypeCode.Char:
          return "wchar";
        case PrimitiveTypeCode.Int8:
          return "__int8";
        case PrimitiveTypeCode.Int16:
          return "__int16";
        case PrimitiveTypeCode.Int32:
          return "__int32";
        case PrimitiveTypeCode.Int64:
          return "__int64";
        case PrimitiveTypeCode.UInt8:
          return "unsigned __int8";
        case PrimitiveTypeCode.UInt16:
          return "unsigned __int16";
        case PrimitiveTypeCode.UInt32:
          return "unsigned __int32";
        case PrimitiveTypeCode.UInt64:
          return "unsigned __int64";
        default:
          // TODO SystemDiagnosticsContractsCodeContractMapString
          if (TypeHelper.GetTypeName(typeDefinition) == SystemDiagnosticsContractsCodeContractTypedPtrString)
            return "\\object";
          else if (TypeHelper.GetTypeName(typeDefinition) == SystemDiagnosticsContractsCodeContractBigIntString)
            return "\\integer";
          else if (TypeHelper.GetTypeName(typeDefinition) == SystemDiagnosticsContractsCodeContractBigNatString)
            return "\\natural";
          else if (TypeHelper.GetTypeName(typeDefinition) == SystemDiagnosticsContractsCodeContractObjsetString)
            return "\\objset";
          else
            return base.GetTypeName(typeDefinition);
      }
    }

    protected override bool ReportAreYouMissingACast
    {
      get { return false; }
    }

    protected override Expression ConversionFromMethodGroupToFunctionPointer(Expression expression, IFunctionPointerTypeReference functionPointer) { //TODO: pass in the source context of the conversion
      expression = this.AddAddressOfIfExpressionIsFunctionName(expression);
      return base.ConversionFromMethodGroupToFunctionPointer(expression, functionPointer);
    }

    private Expression AddAddressOfIfExpressionIsFunctionName(Expression expression) {
      IMethodDefinition/*?*/ method = this.ResolveToMethod(expression);
      if (method != null && !(expression is AddressOf)) {
        Expression addressOf = new VccAddressOf(new AddressableExpression(expression), expression.SourceLocation);
        addressOf.SetContainingExpression(expression);
        return addressOf;
      }
      return expression;
    }

    protected override TypeNameFormatter CreateTypeNameFormatter() {
      return new VccTypeNameFormatter();
    }

    public override AddressOf GetAddressOf(Expression expr, ISourceLocation sourceLocation) {
      return new VccAddressOf(new VccAddressableExpression(expr), sourceLocation);
    }

    public override IEnumerable<ITypeDefinitionMember> GetExtensionMembers(ITypeDefinition type, IName memberName, bool ignoreCase) {
      foreach (ITypeDefinitionMember anonMember in type.GetMembersNamed(Dummy.Name, false)) {
        IFieldDefinition/*?*/ anonField = anonMember as IFieldDefinition;
        if (anonField != null){
          var fieldDef = anonField as Microsoft.Cci.Ast.FieldDefinition;
          if (fieldDef != null) {
            var anonFieldDecl = fieldDef.FieldDeclaration as AnonymousFieldDefinition;
            if (anonFieldDecl != null && anonFieldDecl.SpecMemberName != null && anonFieldDecl.SpecMemberName.Name.UniqueKey == memberName.UniqueKey)
              yield return anonField;
          }
          foreach (ITypeDefinitionMember member in anonField.Type.ResolvedType.GetMembersNamed(memberName, ignoreCase))
            yield return member;
          foreach (ITypeDefinitionMember member in this.GetExtensionMembers(anonField.Type.ResolvedType, memberName, ignoreCase))
            yield return member;
        }
      }
      Microsoft.Cci.Contracts.ITypeContract tc = this.Compilation.ContractProvider.GetTypeContractFor(type);
      if (tc != null) {
        foreach (IFieldDefinition contractField in tc.ContractFields) {
          if (ignoreCase) {
            if (contractField.Name.UniqueKeyIgnoringCase == memberName.UniqueKeyIgnoringCase) yield return contractField;
          } else {
            if (contractField.Name.UniqueKey == memberName.UniqueKey) yield return contractField;
          }
          if (contractField.Name.UniqueKey == Dummy.Name.UniqueKey) {
            foreach (ITypeDefinitionMember member in contractField.Type.ResolvedType.GetMembersNamed(memberName, ignoreCase))
              yield return member;
            foreach (ITypeDefinitionMember member in this.GetExtensionMembers(contractField.Type.ResolvedType, memberName, ignoreCase))
              yield return member;
          }
        }
      }

      //var typeStateFields = ((VccCompilation)this.Compilation).TypeStateFields;
      //if (typeStateFields != null) {
      //  var typeContract = this.Compilation.ContractProvider.GetTypeContractFor(typeStateFields);
      //  if (typeContract != null) {
      //    foreach (var typeStateField in typeContract.ContractFields) {
      //      if (ignoreCase) {
      //        if (typeStateField.Name.UniqueKeyIgnoringCase == memberName.UniqueKeyIgnoringCase) yield return typeStateField;
      //      } else {
      //        if (typeStateField.Name.UniqueKey == memberName.UniqueKey) yield return typeStateField;
      //      }
      //    }
      //  }
      //}
    }

    /// <summary>
    /// Returns the collection of methods with the same name as the given method and declared by the same type as the given method (or by a base type)
    /// and that might be called with the given number of arguments.
    /// </summary>
    //^ [Pure]
    public override IEnumerable<IMethodDefinition> GetMethodGroupMethods(IMethodDefinition methodGroupRepresentative, uint argumentCount, bool argumentListIsIncomplete) {
      if (methodGroupRepresentative.IsForwardReference) return GetMatchingForwardDeclarations(methodGroupRepresentative, argumentCount);
      return base.GetMethodGroupMethods(methodGroupRepresentative, argumentCount, argumentListIsIncomplete);
    }

    private static IEnumerable<IMethodDefinition> GetMatchingForwardDeclarations(IMethodDefinition methodGroupRepresentative, uint argumentCount) {
      // forward declarations cannot be found with 'GetMembersNamed'; thus we have to go looking for them the long way
      IName methodName = methodGroupRepresentative.Name;
      foreach (var member in methodGroupRepresentative.ContainingTypeDefinition.Members) {
        if (member.Name == methodName) {
          var memberAsMethod = member as IMethodDefinition;
          if (memberAsMethod != null) {
            if (memberAsMethod.ParameterCount == argumentCount || 
                memberAsMethod.ParameterCount < argumentCount && memberAsMethod.AcceptsExtraArguments) yield return memberAsMethod;
          }
        }
      }
    }

    /// <summary>
    /// Returns a language specific string that corresponds to a source expression that would evaluate to the given type definition when appearing in an appropriate context.
    /// </summary>
    //^ [Pure]
    public override string GetTypeName(ITypeDefinition typeDefinition, NameFormattingOptions formattingOptions) {
      var/*?*/ tdef = typeDefinition as NamedTypeDefinition;
      if (tdef != null) {
        foreach (TypeDeclaration typeDeclaration in tdef.TypeDeclarations) {
          VccArray/*?*/ vcArr = typeDeclaration as VccArray;
          if (vcArr != null) {
            foreach (ITypeDeclarationMember member in vcArr.TypeDeclarationMembers) {
              IFieldDefinition/*?*/ field = member.TypeDefinitionMember as IFieldDefinition;
              if (field != null) {
                uint elementTypeSize = TypeHelper.SizeOfType(field.Type.ResolvedType);
                if (elementTypeSize <= 0) elementTypeSize = 1;
                return this.GetTypeName(field.Type.ResolvedType, formattingOptions) + "[" + vcArr.SizeOf/elementTypeSize +"]";
              }
            }
          }
        }
      }
      return base.GetTypeName(typeDefinition, formattingOptions);
    }

    //^ [Pure]
    public override Expression ImplicitConversion(Expression expression, ITypeDefinition targetType) {

      Expression result = base.ImplicitConversion(expression, targetType);

      if (TypeHelper.TypesAreEquivalent(targetType, this.PlatformType.SystemBoolean)) {
        if (TypeHelper.IsPrimitiveInteger(expression.Type) || this.IsFloatType(expression.Type)) {
          // The converted result may not be in {0,1} in the framework. While in C, the
          // value "true" has to be 1. 
          Expression t = new CompileTimeConstant(true, SourceDummy.SourceLocation);
          Expression f = new CompileTimeConstant(false, SourceDummy.SourceLocation);
          result = new Conditional(result, t, f, result.SourceLocation);
          result.SetContainingExpression(expression);
          t.SetContainingExpression(result);
          f.SetContainingExpression(result);
        }
      }

      return result;
    }

    private static bool IsGenericTypeOrPointerToOne(ITypeDefinition type) {
      while (true) {
        if (type is IGenericMethodParameter) return true;
        IPointerType ptr = type as IPointerType;
        if (ptr == null) return false;
        type = ptr.TargetType.ResolvedType;
      }
    }

    private bool StripPointersThenInferTypesAndReturnTrueIfInferenceFails(Dictionary<IGenericMethodParameter, ITypeDefinition> inferredTypeArgumentFor, ITypeDefinition argumentType, ITypeDefinition parameterType) {
      IPointerType/*?*/ pType = parameterType as IPointerType;
      if (pType != null) {
        if (this.IsPointerType(argumentType)) {
          return this.StripPointersThenInferTypesAndReturnTrueIfInferenceFails(inferredTypeArgumentFor, 
                    this.GetPointerTargetType(argumentType).ResolvedType, pType.TargetType.ResolvedType);
        }
      }
      return base.InferTypesAndReturnTrueIfInferenceFails(inferredTypeArgumentFor, argumentType, parameterType);
    }

    /// <summary>
    /// Try to unify the given argument type with the given parameter type by replacing any occurrences of type parameters in parameterType with corresponding type
    /// arguments obtained from inferredTypeArgumentsFor. Returns true if unification fails. Updates inferredTypeArgumentsFor with any new inferences made during
    /// a successful unification.
    /// </summary>
    //^ [Pure]
    public override bool InferTypesAndReturnTrueIfInferenceFails(Dictionary<IGenericMethodParameter, ITypeDefinition> inferredTypeArgumentFor, ITypeDefinition argumentType, ITypeDefinition parameterType) {
      if (!IsGenericTypeOrPointerToOne(parameterType)) return false;
      return this.StripPointersThenInferTypesAndReturnTrueIfInferenceFails(inferredTypeArgumentFor, argumentType, parameterType);
    }

    public override ITypeReference GetPointerTargetType(ITypeDefinition type) {
      if (this.IsFixedSizeArrayType(type))
        return this.GetFixedArrayElementType(type);
      return base.GetPointerTargetType(type);
    }

    public override bool IsPointerType(ITypeDefinition type) {
      return this.IsFixedSizeArrayType(type) || base.IsPointerType(type);
    }

    public bool IsFixedSizeArrayType(ITypeDefinition type) {
      NestedTypeDefinition/*?*/ nestedType = type as NestedTypeDefinition;
      return nestedType != null && nestedType.Name.Value.StartsWith("_FixedArrayOfSize", StringComparison.Ordinal);
    }

    private bool IsIntOrBooleanType(ITypeDefinition type) {
      return TypeHelper.TypesAreEquivalent(type, this.PlatformType.SystemBoolean) || TypeHelper.IsPrimitiveInteger(type);
    }

    private bool IsFloatType(ITypeDefinition type) {
      return (TypeHelper.TypesAreEquivalent(type, this.PlatformType.SystemFloat32) ||
        TypeHelper.TypesAreEquivalent(type, this.PlatformType.SystemFloat64));
    }

    private static bool TypesAreEquivalent(ITypeDefinition t1, ITypeDefinition t2) {
      IPointerType/*?*/ p1 = t1 as IPointerType;
      IPointerType/*?*/ p2 = t2 as IPointerType;
      if (p1 != null && p2 != null && VccCompilationHelper.IsSpecPointer(p1) != VccCompilationHelper.IsSpecPointer(p2)) return false;
      return TypeHelper.TypesAreEquivalent(t1, t2);
    }

    public override Expression ImplicitConversionInAssignmentContext(Expression expression, ITypeDefinition targetType) {
      return this.ImplicitConversionInAssignmentContext(expression, targetType, false);
    }

    public Expression ImplicitConversionInAssignmentContext(Expression expression, ITypeDefinition targetType, bool allowUnsafeNumericConversions) {
      if (VccCompilationHelper.TypesAreEquivalent(expression.Type, targetType)) 
        return expression;

      if (VccCompilationHelper.TypesAreEquivalent(TypeWithoutIgnorableModifiers(expression.Type), TypeWithoutIgnorableModifiers(targetType)))
        return expression;

      if (targetType.IsEnum && TypeHelper.IsPrimitiveInteger(expression.Type))
        return this.ExplicitConversion(expression, targetType);
      if (expression.Type.IsEnum && TypeHelper.IsPrimitiveInteger(targetType))
        return this.ExplicitConversion(expression, targetType);

      if (TypeHelper.IsPrimitiveInteger(expression.Type) &&  TypeHelper.IsPrimitiveInteger(targetType)
          && (allowUnsafeNumericConversions || expression.IntegerConversionIsLossless(targetType)))
      {
        return this.ExplicitConversion(expression, targetType);
      }

      if (allowUnsafeNumericConversions) {
        if (this.IsIntOrBooleanType(expression.Type) && this.IsFloatType(targetType))
          return this.ExplicitConversion(expression, targetType);
        if (this.IsFloatType(expression.Type) && TypeHelper.IsPrimitiveInteger(targetType))
          return this.ExplicitConversion(expression, targetType);

        CompileTimeConstant/*?*/ cst = expression as CompileTimeConstant;
        if (cst != null && targetType.TypeCode == PrimitiveTypeCode.Pointer && ExpressionHelper.IsIntegralZero(cst)) {
          return cst;
        }
      }

      return base.ImplicitConversionInAssignmentContext(expression, targetType);
    }

    private static bool ImplicitConversionToBooleanExists(ITypeDefinition sourceType) {
      if (sourceType.TypeCode == PrimitiveTypeCode.Boolean) return true; // bools are trivially compatible
      string typeName = TypeHelper.GetTypeName(sourceType);
      if (typeName.StartsWith(SystemDiagnosticsContractsCodeContractTypedPtrString, StringComparison.Ordinal)) return true;
      if (sourceType.TypeCode == PrimitiveTypeCode.NotPrimitive && sourceType.IsStruct) return false; // structs are not
      if (sourceType.TypeCode == PrimitiveTypeCode.Void) return false;
      if (typeName.StartsWith(SystemDiagnosticsContractsCodeContractMapString, StringComparison.Ordinal)) return false;
      return true;
    }

    /// <summary>
    /// Returns true if an implicit conversion is available to convert the value of the given expression to a corresponding value of the given target type.
    /// </summary>
    //^ [Pure]
    public override bool ImplicitConversionExists(Microsoft.Cci.Ast.Expression expression, ITypeDefinition targetType) {
      if (TypeHelper.TypesAreEquivalent(targetType, this.PlatformType.SystemBoolean))
        return ImplicitConversionToBooleanExists(expression.Type);

      IPointerType targetTypeAsPtr = targetType as IPointerType;

      // CCI now treats false as zero, and thus allows its usage as a pointer
      if (targetTypeAsPtr != null && TypeHelper.TypesAreEquivalent(expression.Type, this.PlatformType.SystemBoolean))
        return false;

      if (targetTypeAsPtr != null && VccCompilationHelper.IsSpecPointer(targetTypeAsPtr) && IsZeroVisitor.IsZero(expression.ProjectAsIExpression())) return true;

      CompileTimeConstant/*?*/ cconst = expression as CompileTimeConstant;
      if (cconst != null) {

        if (TypeHelper.GetTypeName(targetType) == SystemDiagnosticsContractsCodeContractBigNatString && expression.ValueIsPolymorphicCompileTimeConstant)
          return true;

        if (targetTypeAsPtr != null && ExpressionHelper.IsIntegralZero(cconst)) return true;
        // Disable int -> enum so that any enum operation becomes int operation
        if (targetType.IsEnum && cconst.ValueIsPolymorphicCompileTimeConstant) return ImplicitConversionExists(cconst, targetType.UnderlyingType.ResolvedType);
        if (TypeHelper.IsUnsignedPrimitiveInteger(cconst.Type) && !TypeHelper.IsUnsignedPrimitiveInteger(targetType) && 
          cconst is VccCompileTimeConstantWhoseSignDependsOnAnotherExpression)
          return false;
      }

      // allow implicit conversion of bitfields if their effective value range can be safely converted to the target type
      VccQualifiedName/*?*/ qName = expression as VccQualifiedName;
      if (qName != null && qName.IntegerConversionIsLossless(targetType))
        return true;

      VccPointerQualifiedName/*?*/ pqName = expression as VccPointerQualifiedName;
      if (pqName != null && pqName.IntegerConversionIsLossless(targetType))
        return true;

      if (expression.Type == Dummy.Type) {
        IFunctionPointer/*?*/ functionPointer = targetType as IFunctionPointer;
        if (functionPointer != null) return (this.ConversionFromMethodGroupToFunctionPointer(expression, functionPointer).Type != Dummy.Type);
        if (targetTypeAsPtr != null && targetTypeAsPtr.TargetType.ResolvedType.TypeCode == PrimitiveTypeCode.Void) {
          if (this.ResolveToMethod(expression) != null) return true;
        }
      }

      if (IsFixedSizeArrayType(expression.Type) && IsSpecVisitor.Check(expression.ProjectAsIExpression()))
        return this.ImplicitConversionExists(this.GetPointerForFixedSizeArray(expression.Type, true), targetType);

      var result = base.ImplicitConversionExists(expression, targetType);
      return result;
    }


    /// <summary>
    /// True if the last call to 'MethodIsEligible' has been for an operator method
    /// This is a hack that is being used to allow implicit conversion from a bitfield 
    /// to any type that can accomodate the bit field's value range. This behavior
    /// is undesirable when resolving operators. See the implementation of
    /// IntegerConversionIsLossless of types VccQualifiedName and VccPointerQualifiedName.
    /// </summary>
    internal bool CurrentlyResolvingOperator { get; private set; }

    public override bool MethodIsEligible(IMethodDefinition method, IEnumerable<Expression> arguments) {
      bool savedCurrentlyResolvingOperator = this.CurrentlyResolvingOperator;
      this.CurrentlyResolvingOperator = method.Name.Value.Contains(" op ");
      bool result = base.MethodIsEligible(method, arguments);
      this.CurrentlyResolvingOperator = savedCurrentlyResolvingOperator;
      return result;
    }

    private ITypeDefinition TypeWithoutIgnorableModifiers(ITypeDefinition type)
    {
      ModifiedPointerType typeAsModifiedPtrType = type as ModifiedPointerType;
      if (typeAsModifiedPtrType == null) return type;

      List<ICustomModifier> nonIgnorableModifiers = new List<ICustomModifier>();

      int modifierCount = 0;
      foreach (var modifier in typeAsModifiedPtrType.CustomModifiers)
      {
        modifierCount++;
        if (modifier.Modifier.InternedKey == type.PlatformType.SystemRuntimeCompilerServicesIsVolatile.InternedKey)
          continue;
        if (modifier.Modifier.InternedKey == type.PlatformType.SystemRuntimeCompilerServicesIsConst.InternedKey)
          continue;
       
        nonIgnorableModifiers.Add(modifier);
      }

      if (nonIgnorableModifiers.Count == 0)
        return PointerType.GetPointerType(typeAsModifiedPtrType.TargetType,
                                          this.Compilation.HostEnvironment.InternFactory);

      if (nonIgnorableModifiers.Count != modifierCount)
        return ModifiedPointerType.GetModifiedPointerType(typeAsModifiedPtrType.TargetType,
                                                          nonIgnorableModifiers,
                                                          this.Compilation.HostEnvironment.InternFactory);
      return type;
    }

    //^ [Pure]
    public override bool ImplicitConversionExists(ITypeDefinition sourceType, ITypeDefinition targetType) {

      if (TypeHelper.TypesAreEquivalent(sourceType, targetType)) return true;

      // * -> bool
      if (TypeHelper.TypesAreEquivalent(targetType, this.PlatformType.SystemBoolean))
        return ImplicitConversionToBooleanExists(sourceType);

      // bool -> int
      if (TypeHelper.TypesAreEquivalent(sourceType, this.PlatformType.SystemBoolean))
        return TypeHelper.IsPrimitiveInteger(targetType);

      // enum -> int
      if (sourceType.IsEnum && TypeHelper.IsPrimitiveInteger(targetType))
        return this.ImplicitConversionExists(sourceType.UnderlyingType.ResolvedType, targetType);
     
      // int -> enum
      if (targetType.IsEnum && TypeHelper.IsPrimitiveInteger(sourceType))
        return this.ImplicitConversionExists(sourceType, targetType.UnderlyingType.ResolvedType);

      var sourceUnmod = TypeWithoutIgnorableModifiers(sourceType);
      var targetUnmod = TypeWithoutIgnorableModifiers(targetType);

      if (sourceUnmod != sourceType || targetUnmod != targetType) {
        return this.ImplicitConversionExists(sourceUnmod, targetUnmod);
      }

      // special pointer conversion rules
      IPointerType/*?*/ srcPointerType;
      IPointerType/*?*/ tgtPointerType;
      PtrConvKind srcKind = this.ToPtrConvKind(sourceType, out srcPointerType);
      PtrConvKind tgtKind = this.ToPtrConvKind(targetType, out tgtPointerType);

      if (srcKind == PtrConvKind.Array) return this.ImplicitConversionExists(srcPointerType, targetType);

      if (srcKind != PtrConvKind.None && tgtKind != PtrConvKind.None) {
        ConvMethod convMethod = VccCompilationHelper.KindsToConvMethod(srcKind, tgtKind);
        if (convMethod == ConvMethod.Implicit || convMethod == ConvMethod.Identity) 
          return true;
        if (srcKind == PtrConvKind.SpecPtr || srcKind == PtrConvKind.VoidSpecP || tgtKind == PtrConvKind.SpecPtr || tgtKind == PtrConvKind.VoidSpecP)
          return false;
      }


      return base.ImplicitConversionExists(sourceType, targetType);

      //if (srcKind != PtrConvKind.None && tgtKind != PtrConvKind.None) {
      //  ConvMethod convKind = VccCompilationHelper.KindsToConvMethod(srcKind, tgtKind);
      //  if (convKind == ConvMethod.Identity || convKind == ConvMethod.Implicit) return true;
      //  if (convKind == ConvMethod.Explicit || convKind == ConvMethod.ExplicitAndImplicitIfZero || convKind == ConvMethod.Incompatible) return false;
      //}
      //return base.ImplicitConversionExists(sourceType, targetType);
    }

    /// <summary>
    /// Returns true if argument has a better implicit conversion to par1type than it has to par2Type.
    /// </summary>
    //^ [Pure]
    protected override bool ImplicitConversionFromArgumentToType1isBetterThanImplicitConversionToType2(Microsoft.Cci.Ast.Expression argument, ITypeDefinition par1Type, ITypeDefinition par2Type) {
      if (par1Type.TypeCode != par2Type.TypeCode){
        if (TypeHelper.IsPrimitiveInteger(par1Type)) {
          if (par2Type.TypeCode == PrimitiveTypeCode.Boolean && TypeHelper.IsPrimitiveInteger(argument.Type) && argument.Type.TypeCode != PrimitiveTypeCode.Boolean)
            return true;
          if (par2Type is IPointerType && argument is CompileTimeConstant && TypeHelper.IsPrimitiveInteger(argument.Type))
            return true;
        } else if (par1Type.IsEnum && TypeHelper.IsPrimitiveInteger(par2Type)) {
          return true;
        }
      }
      return base.ImplicitConversionFromArgumentToType1isBetterThanImplicitConversionToType2(argument, par1Type, par2Type);
    }

    /// <summary>
    /// Returns true if a value of an enumeration type can be implicitly converted to an integer type.
    /// </summary>
    protected override bool ImplicitEnumToIntegerConversionIsAllowed {
      get { return true; }
    }

    //^ [Pure]
    public override LanguageSpecificCompilationHelper MakeShallowCopyFor(Compilation targetCompilation)
      //^^ ensures result.GetType() == this.GetType();
    {
      if (this.Compilation == targetCompilation) return this;
      return new VccCompilationHelper(targetCompilation, this);
    }

    public ITypeDefinition Runtime {
      get {
        if (this.runtime == null)
          this.runtime = this.GetRuntime();
        return this.runtime;
      }
    }
    //^ [Once]
    ITypeDefinition/*?*/ runtime;

    //^ [Confined]
    private ITypeDefinition GetRuntime() {
      IName microsoft  = this.NameTable.GetNameFor("Microsoft");
      IName research = this.NameTable.GetNameFor("Research");
      IName vcc = this.NameTable.GetNameFor("Vcc");
      IName runtime = this.NameTable.GetNameFor("Runtime");

      INamespaceDefinition/*?*/ ns = this.Compilation.UnitSet.UnitSetNamespaceRoot;
      foreach (INamespaceMember member in ns.GetMembersNamed(microsoft, false)) {
        ns = member as INamespaceDefinition;
        if (ns == null) continue;
        foreach (INamespaceMember member2 in ns.GetMembersNamed(research, false)) {
          ns = member2 as INamespaceDefinition;
          if (ns == null) continue;
          foreach (INamespaceMember member3 in ns.GetMembersNamed(vcc, false)) {
            ns = member3 as INamespaceDefinition;
            if (ns == null) continue;
            foreach (INamespaceMember mem in ns.GetMembersNamed(runtime, false)) {
              ITypeDefinition/*?*/ type = mem as ITypeDefinition;
              if (type != null) return type;
            }
          }
        }
      }
      return Dummy.Type;
      //TODO: error if type cannot be found
    }

    internal Dictionary<string, GlobalVariableDeclaration> StringTable = new Dictionary<string, GlobalVariableDeclaration>();

    /// <summary>
    /// Checks if selecting this overload would cause something undesirable to happen. For example "int op uint" may become "long op long" which
    /// is desirable for C# but undesirable for C.
    /// </summary>
    public override bool StandardBinaryOperatorOverloadIsUndesirable(IMethodDefinition standardBinaryOperatorMethod, Expression leftOperand, Expression rightOperand) {
      if (TypeHelper.SizeOfType(leftOperand.Type) == 4 && TypeHelper.SizeOfType(rightOperand.Type) == 4) {
        return standardBinaryOperatorMethod == this.Compilation.BuiltinMethods.Int64opInt64;
      }
      return false;
    }

    /// <summary>
    /// Returns true if the field has (or should have) a compile time value that should be used in expressions whenever the field is referenced.
    /// For example, if field.IsCompileTimeConstant is true then the CLR mandates that the value should be used since the field will have no runtime memory associated with it.
    /// </summary>
    public override bool UseCompileTimeValueOfField(IFieldDefinition field) {
      return field.IsCompileTimeConstant || (field.IsReadOnly && TypeHelper.IsCompileTimeConstantType(field.Type.ResolvedType) && field.CompileTimeValue != Dummy.Constant);
    }

    internal static bool ContainsTypeQualifier(IEnumerable<Specifier> specifiers, Token token) {
      foreach (var specifier in specifiers) {
        TypeQualifier tq = specifier as TypeQualifier;
        if (tq != null && tq.Token == token)
          return true;
      }
      return false;
    }

    internal static bool ContainsStorageClassSpecifier(IEnumerable<Specifier> specifiers, Token token) {
      foreach (var specifier in specifiers) {
        StorageClassSpecifier scs = specifier as StorageClassSpecifier;
        if (scs != null && scs.Token == token)
          return true;
      }
      return false;
    }

  }

  public sealed class VccTypeNameFormatter : TypeNameFormatter {

    protected override string GetFunctionPointerTypeName(IFunctionPointerTypeReference functionPointerType, NameFormattingOptions formattingOptions) {
      StringBuilder sb = new StringBuilder();
      sb.Append(this.GetTypeName(functionPointerType.Type, formattingOptions));
      bool first = true;
      sb.Append(" (*)(");
      foreach (IParameterTypeInformation par in functionPointerType.Parameters) {
        if (first) first = false; else sb.Append(", ");
        sb.Append(this.GetTypeName(par.Type, formattingOptions));
      }
      sb.Append(')');
      return sb.ToString();
    }

    //^ [Pure]
    protected override string GetNestedTypeName(INestedTypeReference nestedType, NameFormattingOptions formattingOptions) {
      NestedTypeDefinition/*?*/ ntDef = nestedType as NestedTypeDefinition;
      if (ntDef != null) {
        foreach (NestedTypeDeclaration ntDecl in ntDef.TypeDeclarations){
          VccArray/*?*/ vcArray = ntDecl as VccArray;
          if (vcArray != null) {
            foreach (ITypeDeclarationMember member in vcArray.TypeDeclarationMembers) {
              IFieldDefinition/*?*/ field = member.TypeDefinitionMember as IFieldDefinition;
              if (field != null) {
                uint elementTypeSize = TypeHelper.SizeOfType(field.Type.ResolvedType);
                if (elementTypeSize <= 0) elementTypeSize = 1;
                return this.GetTypeName(field.Type.ResolvedType, formattingOptions) + "[" + vcArray.SizeOf/elementTypeSize +"]";
              }
            }
          }
        }
      }
      return base.GetNestedTypeName(nestedType, formattingOptions);
    }

    protected override string GetPointerTypeName(IPointerTypeReference pointerType, NameFormattingOptions formattingOptions) {
      IPointerType pt = pointerType as IPointerType;
      if (pt != null) {
        var ptrSym = VccCompilationHelper.IsSpecPointer(pt) ? "^" : "*";
        var vol = VccCompilationHelper.IsVolatilePointer(pt) ? "volatile " : "";
        var _const = VccCompilationHelper.IsConstPointer(pt) ? "const " : "";
        return vol + _const + this.GetTypeName(pt.TargetType, formattingOptions) + ptrSym;
      }
      return base.GetPointerTypeName(pointerType, formattingOptions);
    }

  }

  public sealed class VccUnpreprocessedSourceDocument : PrimarySourceDocument, IVccUnpreprocessedSourceDocument {

    public VccUnpreprocessedSourceDocument(VccCompilationHelper helper, IName name, string location, System.IO.StreamReader streamReader)
      : base(name, location, streamReader) {
      this.helper = helper;
    }

    public VccUnpreprocessedSourceDocument(VccCompilationHelper helper, IName name, string location, string text)
      : base(name, location, text) {
      this.helper = helper;
    }

    public VccUnpreprocessedSourceDocument(VccCompilationHelper helper, string text, SourceDocument previousVersion, int position, int oldLength, int newLength)
      : base(text, previousVersion, position, oldLength, newLength) {
      this.helper = helper;
    }

    readonly VccCompilationHelper helper;

    //public override CompilationPart CompilationPart {
    //  get
    //    //^^ ensures result.SourceLocation.SourceDocument == this;
    //  {
    //    //^ assume false; //unpreprocessed source documents should be fed to the preprocessor only and should never be asked to parse themselves.
    //    throw new System.InvalidOperationException();
    //  }
    //}

    public Preprocessor GetPreprocessorFor(string location, IDictionary<string, string> preprocessorSymbols)
      // ^ requires System.IO.File.Exists(location);
    {
      IName name = this.helper.NameTable.GetNameFor(System.IO.Path.GetFileNameWithoutExtension(location));
      System.IO.StreamReader reader = System.IO.File.OpenText(location);
      VccUnpreprocessedSourceDocument doc = new VccUnpreprocessedSourceDocument(this.helper, name, location, reader);
      VccSourceDocument sdoc = new VccSourceDocument(this.helper, doc, preprocessorSymbols);
      return sdoc.GetAndCacheNewPreprocessor();
    }

    //^ [Pure]
    public override ISourceLocation GetSourceLocation(int position, int length)
      //^^ requires 0 <= position && (position < this.Length || position == 0);
      //^^ requires 0 <= length;
      //^^ requires length <= this.Length;
      //^^ requires position+length <= this.Length;
      //^^ ensures result.SourceDocument == this;
      //^^ ensures result.StartIndex == position;
      //^^ ensures result.Length == length;
    {
      return new PrimarySourceLocation(this, position, length);
    }

    public VccUnpreprocessedSourceDocument GetUpdatedDocument(int position, int length, string updatedText)
      //^ requires 0 <= position && position < this.Length;
      //^ requires 0 <= length && length <= this.Length;
      //^ requires 0 <= position+length && position+length <= this.Length;
    {
      string oldText = this.GetText();
      if (position > oldText.Length) 
        position = oldText.Length; //This should only happen if the source document got clobbered after the precondition was established.
      //^ assume 0 <= position; //Follows from the precondition and the previous statement
      if (position+length > oldText.Length)
        length = oldText.Length-position;
      //^ assume 0 <= position+length; //established by the precondition and not changed by the previous two statements.
      string newText = oldText.Substring(0, position)+updatedText+oldText.Substring(position+length);
      return new VccUnpreprocessedSourceDocument(this.helper, newText, this, position, length, updatedText.Length);
    }

    public override string SourceLanguage {
      get { return "Vcc"; }
    }

    public override Guid DocumentType {
      get { return SymDocumentType.Text; }
    }

    public override Guid Language {
      get { return SymLanguageType.C; }
    }

    public override Guid LanguageVendor {
      get { return SymLanguageVendor.Microsoft; }
    }
  }

  public abstract class VccCompositeDocument : CompositeSourceDocument {

    protected VccCompositeDocument(IName name)
      : base(name) {
    }

    protected VccCompositeDocument(SourceDocument previousVersion, int position, int oldLength, int newLength)
      : base(previousVersion, position, oldLength, newLength) {
    }

    /// <summary>
    /// Makes a shallow copy of this source document (creating a new
    /// </summary>
    //^^ [MustOverride]
    public abstract VccCompositeDocument MakeShallowCopyFor(Compilation targetCompilation);

    internal abstract List<IErrorMessage> PreprocessorErrors { get; }

    internal abstract List<IErrorMessage> ScannerAndParserErrors { get; }

    internal abstract ISourceDocument UnpreprocessedDocument { get; }

    public abstract VccCompilationPart VccCompilationPart {
      get;
      //^ ensures result.SourceLocation.SourceDocument == this;
    }
    
  }

  public abstract class VccCompositeDocument<TPrimaryDocument, TVersion> : VccCompositeDocument, IVccSourceDocument
    where TPrimaryDocument : class, IVccUnpreprocessedSourceDocument
  {

    protected VccCompositeDocument(VccCompilationHelper helper, TPrimaryDocument/*!*/ documentToPreprocess, IDictionary<string, string>/*?*/ preprocessorDefinedSymbols)
      : base(documentToPreprocess.Name)
    {
      this.helper = helper;
      this.documentToPreprocess = documentToPreprocess;
      this.preprocessorDefinedSymbols = preprocessorDefinedSymbols;
    }

    protected VccCompositeDocument(VccCompilationHelper helper, TPrimaryDocument/*!*/ documentToPreprocess, PreprocessorInformation/*?*/ preprocessorInformation, 
      VccCompositeDocument<TPrimaryDocument, TVersion> previousVersion, int position, int oldLength, int newLength)
      : base(previousVersion, position, oldLength, newLength)
    {
      this.helper = helper;
      this.documentToPreprocess = documentToPreprocess;
      this.preprocessorInformation = preprocessorInformation;
    }

    //public override CompilationPart CompilationPart {
    //  get { return this.VccCompilationPart; }
    //}

    public override VccCompilationPart VccCompilationPart {
      get
        //^ ensures result.SourceLocation.SourceDocument == this;
      {
        if (this.compilationPart == null) {
          lock (GlobalLock.LockingObject) {
            if (this.compilationPart == null) {
              ISourceLocation sloc = this.SourceLocation;
              //^ assume sloc.SourceDocument is VccCompositeDocument;
              this.compilationPart = new VccCompilationPart(this.helper, sloc);
            }
          }
        }
        return this.compilationPart;
      }
    }
    private VccCompilationPart/*?*/ compilationPart;

    public TPrimaryDocument/*!*/ DocumentToPreprocess {
      //^ [Pure]
      get { return this.documentToPreprocess; }
      protected set { this.documentToPreprocess = value; }
    }
    private TPrimaryDocument/*!*/ documentToPreprocess;

    /// <summary>
    /// Returns a source document that represents the replacement of the text of this.DocumentToPreprocess from position to position+length with updatedText.
    /// I.e. the given position and length corresponds to the text of the document before preprocessing, but the resulting
    /// edit is an edit to the document after preprocessing (i.e. this document, not the one that preprocessor consumes).
    /// The compilation containing the compilation part that corresponds to the result of this call is registered with the
    /// host environment as being the latest version of the compilation.
    /// </summary>
    /// <param name="position">The position in this.DocumentToPreprocess, of the first character to be replaced by this edit.</param>
    /// <param name="length">The number of characters in this.DocumentToPreprocess that will be replaced by this edit.</param>
    /// <param name="updatedText">The replacement string.</param>
    /// <param name="version">The document's version</param>
    protected IVccSourceDocument GetUpdatedDocument(int position, int length, string updatedText, TVersion version)
      //^ requires 0 <= position && position < this.DocumentToPreprocess.Length;
      //^ requires 0 <= length && length <= this.DocumentToPreprocess.Length;
      //^ requires 0 <= position+length && position+length <= this.DocumentToPreprocess.Length;
      //^ ensures result.IsUpdatedVersionOf(this);
      //^ ensures result.GetType() == this.GetType();
    {
      VccCompositeDocument<TPrimaryDocument, TVersion> result;
      List<CompilationPart> nextParts = new List<CompilationPart>(this.VccCompilationPart.Compilation.Parts);
      Compilation nextCompilation = this.VccCompilationPart.Compilation.UpdateCompilationParts(nextParts);
      VccCompilationHelper nextHelper = (VccCompilationHelper)this.Helper.MakeShallowCopyFor(nextCompilation);
      PreprocessorInformation ppInfo = this.PreprocessorInformation;
      foreach (ISourceLocation includedLocation in ppInfo.IncludedLocations) {
        if (includedLocation.StartIndex <= position && position+length <= includedLocation.StartIndex+includedLocation.Length) {
          //Included section spans the edit.
          TPrimaryDocument nextVersionOfDocumentToPreprocess = this.GetNextVersionOfDocumentToPreprocess(position, length, updatedText, version);
          PreprocessorInformation nextVersionOfPreprocessorInformation = new PreprocessorInformation(nextVersionOfDocumentToPreprocess, ppInfo);
          result = this.GetNextVersion(nextHelper, nextVersionOfDocumentToPreprocess, nextVersionOfPreprocessorInformation, position, length, updatedText.Length);
          goto updateCompilationPart;
        }
      }
      foreach (ISourceLocation excludedLocation in ppInfo.excludedLocations) {
        if (excludedLocation.StartIndex <= position && position+length <= excludedLocation.StartIndex+excludedLocation.Length) {
          //Excluded section spans the edit.
          TPrimaryDocument nextVersionOfDocumentToPreprocess = this.GetNextVersionOfDocumentToPreprocess(position, length, updatedText, version);
          PreprocessorInformation nextVersionOfPreprocessorInformation = new PreprocessorInformation(nextVersionOfDocumentToPreprocess, ppInfo);
          result = this.GetNextVersion(nextHelper, nextVersionOfDocumentToPreprocess, nextVersionOfPreprocessorInformation, 0, 0, 0);
          goto updateCompilationPart;
        }
      }
      {
        //Not a common case and could be an edit that results in a different list of included locations.
        //Re-preprocess and produce an edit that replaces the entire resulting document (and thus forces the entire CompilationUnit to be rebuilt).
        TPrimaryDocument nextVersionOfDocumentToPreprocess = this.GetNextVersionOfDocumentToPreprocess(position, length, updatedText, version);
        result = this.GetNewVersion(nextHelper, nextVersionOfDocumentToPreprocess);
        result = this.GetNextVersion(nextHelper, nextVersionOfDocumentToPreprocess, result.PreprocessorInformation, 0, this.Length, result.Length);
        goto updateCompilationPart;
      }
    updateCompilationPart:
      EditEventArgs editEventArgs;
      EditEventArgs/*?*/ symbolTableEditEventArgs;
      ISourceLocation oldLocationBeforePreprocessing = this.DocumentToPreprocess.GetSourceLocation(position, length);
      ISourceLocation oldLocationAfterPreprocessing = this.GetLocationAfterPreprocessing(oldLocationBeforePreprocessing);
      VccSourceDocumentEdit edit = new VccSourceDocumentEdit(oldLocationAfterPreprocessing, result);
      edit.compilationPartAfterEdit = result.compilationPart = (VccCompilationPart)this.VccCompilationPart.UpdateWith(edit, nextParts, out editEventArgs, out symbolTableEditEventArgs);
      this.Helper.Compilation.HostEnvironment.RegisterAsLatest(result.VccCompilationPart.Compilation);
      this.Helper.Compilation.HostEnvironment.ReportEdits(editEventArgs);
      if (symbolTableEditEventArgs != null)
        this.Helper.Compilation.HostEnvironment.ReportSymbolTableEdits(symbolTableEditEventArgs);
      return result;
    }

    internal sealed class VccSourceDocumentEdit : AstSourceDocumentEdit {
      /// <summary>
      /// Allocates an object that describes an edit to a source file.
      /// </summary>
      internal VccSourceDocumentEdit(ISourceLocation sourceLocationBeforeEdit, ISourceDocument sourceDocumentAfterEdit)
        : base(sourceLocationBeforeEdit, sourceDocumentAfterEdit)
        //^ requires sourceDocumentAfterEdit.IsUpdatedVersionOf(sourceLocationBeforeEdit.SourceDocument);
      {
      }

      /// <summary>
      /// The compilation part that is the result of applying this edit.
      /// </summary>
      public override CompilationPart CompilationPartAfterEdit {
        get {
          //^ assume this.compilationPartAfterEdit != null;
          return this.compilationPartAfterEdit;
        }
      }
      internal CompilationPart/*?*/ compilationPartAfterEdit;
    }

    /// <summary>
    /// Returns a location in the preprocessed document that corresponds to the given location from the unpreprocessed document.
    /// </summary>
    /// <param name="sourceLocation">A locotion in a source document that forms part of this composite document.</param>
    public ISourceLocation GetLocationAfterPreprocessing(ISourceLocation sourceLocation)
      //^ requires sourceLocation.SourceDocument == this.DocumentToPreprocess;
    {
      int start = 0;
      int length = 0;
      PreprocessorInformation ppInfo = this.PreprocessorInformation;
      foreach (ISourceLocation includedLocation in ppInfo.IncludedLocations) {
        if (includedLocation.StartIndex+includedLocation.Length <= sourceLocation.StartIndex) {
          //The included location is before the source location. Just add its length to start.
          start += includedLocation.Length;
        } else if (includedLocation.StartIndex <= sourceLocation.StartIndex) {
          if (includedLocation.StartIndex+includedLocation.Length >= sourceLocation.StartIndex+sourceLocation.Length) {
            //The included location overlaps the entire source location
            start += sourceLocation.StartIndex-includedLocation.StartIndex;
            length = sourceLocation.Length;
            break;
          } else {
            //The included location overlaps a prefix of the source location
            start += sourceLocation.StartIndex-includedLocation.StartIndex;
            length += includedLocation.Length-(sourceLocation.StartIndex-includedLocation.StartIndex);
          }
        } else if (includedLocation.StartIndex >= sourceLocation.StartIndex+sourceLocation.Length) {
          //The included location occurs after the end of the source location.
          break;
        } else {
          if (includedLocation.StartIndex+includedLocation.Length < sourceLocation.StartIndex+sourceLocation.Length) {
            //The included location is contained within the source location.
            length += includedLocation.Length;
          } else {
            //The included location overlaps a suffix of the source location
            length += includedLocation.StartIndex-sourceLocation.StartIndex;
            break;
          }
        }
      }
      return this.GetSourceLocation(start, length);
    }

    /// <summary>
    /// Returns a new preprocessed document of the same type as this document, but using the given helper and underlying document to preprocess.
    /// </summary>
    /// <param name="helper">A Vcc specific helper object that is used to provide the value of the CompilationPart property.</param>
    /// <param name="documentToPreprocess">The unpreprocessed document on which the newly allocated document should be based.</param>
    protected abstract VccCompositeDocument<TPrimaryDocument, TVersion> GetNewVersion(VccCompilationHelper helper, TPrimaryDocument documentToPreprocess);
    // ^ ensures result.GetType() == this.GetType(); //TODO: this crashes the non null analyzer

    /// <summary>
    /// Returns a new version of this.DocumentToPreprocess where the substring designated by position and length has been replaced by the given replacement text.
    /// </summary>
    /// <param name="position">The index of the first character to replace.</param>
    /// <param name="length">The number of characters to replace.</param>
    /// <param name="updatedText">The replacement string.</param>
    /// <param name="version">A version object (may be null) to associate with the result.</param>
    protected abstract TPrimaryDocument/*!*/ GetNextVersionOfDocumentToPreprocess(int position, int length, string updatedText, TVersion version);
    // ^ requires 0 <= position && position < this.DocumentToPreprocess.Length; //Spec# bug: this contract is not fully analyzed by the time it is inherited by the override
    // ^ requires 0 <= length && length <= this.DocumentToPreprocess.Length;
    // ^ requires 0 <= position+length && position+length <= this.DocumentToPreprocess.Length;

    /// <summary>
    /// Returns a new version of this document where the substring designated by position and length has been replaced by the given replacement text.
    /// </summary>
    /// <param name="helper">A Vcc specific helper object that is used to provide the value of the CompilationPart property.</param>
    /// <param name="nextVersionOfDocumentToPreprocess">The unpreprocessed document on which the newly allocated document should be based.</param>
    /// <param name="nextVersionOfPreprocessorInformation">A preprocessing information object that was incrementally derived from it previous version.</param>
    /// <param name="position">The first character in the previous version of the new document that will be changed in the new document.</param>
    /// <param name="oldLength">The number of characters in the previous verion of the new document that will be changed in the new document.</param>
    /// <param name="newLength">The number of replacement characters in the new document. 
    /// (The length of the string that replaces the substring from position to position+length in the previous version of the new document.)</param>
    protected abstract VccCompositeDocument<TPrimaryDocument, TVersion> GetNextVersion(VccCompilationHelper helper,
      TPrimaryDocument nextVersionOfDocumentToPreprocess, PreprocessorInformation/*?*/ nextVersionOfPreprocessorInformation, int position, int oldLength, int newLength);
    // ^ ensures result.GetType() == this.GetType(); //TODO: this crashes the non null analyzer

    protected override IEnumerable<ISourceLocation> GetFragments()  {
      if (this.preprocessorInformation != null)
        return this.preprocessorInformation.IncludedLocations; //should get here when constructing a PDB
      if (this.preprocessor == null) {
        //Fast case for constructing symbol table in VS
        Preprocessor preprocessor = this.GetAndCacheNewPreprocessor(); //avoid calling this.PreprocessorInformation as it will process the entire document before returning.
        return preprocessor.GetIncludedSections();
      }
      //Should only get here when getting source location information about an error.
      return this.PreprocessorInformation.IncludedLocations;
    }

    internal Preprocessor GetAndCacheNewPreprocessor()
      //^ ensures this.preprocessor == result;
    {
      if (this.preprocessorDefinedSymbols == null)
        return this.preprocessor = new Preprocessor(this.DocumentToPreprocess, (VccOptions)this.VccCompilationPart.Compilation.Options);
      else
        return this.preprocessor = new Preprocessor(this.DocumentToPreprocess, this.preprocessorDefinedSymbols, new List<IErrorMessage>());
    }

    protected VccCompilationHelper Helper {
      get { return this.helper; }
    }
    readonly VccCompilationHelper helper;

    private Preprocessor Preprocessor {
      get
        //^ ensures result.PreprocessingIsComplete;
      {
        if (this.preprocessor == null || !this.preprocessor.PreprocessingIsComplete) {
          lock (GlobalLock.LockingObject) {
            if (this.preprocessor == null || !this.preprocessor.PreprocessingIsComplete) {
              Preprocessor preprocessor = this.GetAndCacheNewPreprocessor();
              //^ assert this.preprocessor != null;
#pragma warning disable 642
              for (IEnumerator<ISourceLocation> includedSectionEnumerator = preprocessor.GetIncludedSections().GetEnumerator(); includedSectionEnumerator.MoveNext(); ) ;
#pragma warning restore 642
              //^ assume this.preprocessor.PreprocessingIsComplete;
            }
          }
        }
        return this.preprocessor; 
      }
    }
    private Preprocessor/*?*/ preprocessor;

    readonly IDictionary<string, string>/*?*/ preprocessorDefinedSymbols;

    internal override List<IErrorMessage> PreprocessorErrors {
      get {
        if (this.preprocessor == null) {
          lock (GlobalLock.LockingObject) {
            if (this.preprocessor == null) {
              if (this.preprocessorInformation == null)
                return new List<IErrorMessage>(0);
              return this.preprocessorInformation.errors;
            }
          }
        }
        return this.preprocessor.errors;
      }
    }

    public PreprocessorInformation PreprocessorInformation {
      get {
        if (this.preprocessorInformation == null) {
          lock (GlobalLock.LockingObject) {
            if (this.preprocessorInformation == null)
              this.preprocessorInformation = this.Preprocessor.PreprocessorInformation;
          }
        }
        return this.preprocessorInformation;
      }
    }
    private PreprocessorInformation/*?*/ preprocessorInformation;

    internal override List<IErrorMessage> ScannerAndParserErrors {
      get { return this.scannerAndParserErrors; }
    }
    private readonly List<IErrorMessage> scannerAndParserErrors = new List<IErrorMessage>();

    public override string SourceLanguage {
      get { return "Vcc"; }
    }

    internal override ISourceDocument UnpreprocessedDocument {
      get { return this.documentToPreprocess; }
    }

  }

  public interface IVccUnpreprocessedSourceDocument : IPrimarySourceDocument {
    Preprocessor GetPreprocessorFor(string location, IDictionary<string, string> preprocessorSymbols);
    // ^ requires System.IO.File.Exists(location);
  }

  public sealed class VccSourceDocument : VccCompositeDocument<VccUnpreprocessedSourceDocument, object> {

    public VccSourceDocument(VccCompilationHelper helper, IName name, string location, System.IO.StreamReader streamReader)
      : base(helper, new VccUnpreprocessedSourceDocument(helper, name, location, streamReader), null) {
    }

    public VccSourceDocument(VccCompilationHelper helper, IName name, string location, string text)
      : base(helper, new VccUnpreprocessedSourceDocument(helper, name, location, text), null) {
    }

    public VccSourceDocument(VccCompilationHelper helper, VccUnpreprocessedSourceDocument documentToPreprocess, IDictionary<string, string> preprocessorDefinedSymbols)
      : base(helper, documentToPreprocess, preprocessorDefinedSymbols) {
    }

    private VccSourceDocument(VccCompilationHelper helper, VccUnpreprocessedSourceDocument documentToPreprocess)
      : base(helper, documentToPreprocess, null) {
    }

    private VccSourceDocument(VccCompilationHelper helper, VccUnpreprocessedSourceDocument nextVersionOfDocumentToPreprocess, PreprocessorInformation/*?*/ nextVersionOfPreprocessorInformation,
      VccSourceDocument previousVersion, int position, int oldLength, int newLength)
      : base(helper, nextVersionOfDocumentToPreprocess, nextVersionOfPreprocessorInformation, previousVersion, position, oldLength, newLength) {
    }

    /// <summary>
    /// Returns a source document edit that represents the replacement of the text of this.DocumentToPreprocess from position to position+length with updatedText.
    /// I.e. the given position and length corresponds to the text of the document before preprocessing, but the resulting
    /// edit is an edit to the document after preprocessing (i.e. this document, not the one that preprocessor consumes).
    /// </summary>
    /// <param name="position">The position in this.DocumentToPreprocess, of the first character to be replaced by this edit.</param>
    /// <param name="length">The number of characters in this.DocumentToPreprocess that will be replaced by this edit.</param>
    /// <param name="updatedText">The replacement string.</param>
    public IVccSourceDocument GetUpdatedDocument(int position, int length, string updatedText)
      //^ requires 0 <= position && position < this.DocumentToPreprocess.Length;
      //^ requires 0 <= length && length <= this.DocumentToPreprocess.Length;
      //^ requires 0 <= position+length && position+length <= this.DocumentToPreprocess.Length;
      //^ ensures result.IsUpdatedVersionOf(this);
    {
      return base.GetUpdatedDocument(position, length, updatedText, this);
    }

    /// <summary>
    /// Returns a new preprocessed document of the same type as this document, but using the given helper and underlying document to preprocess.
    /// </summary>
    /// <param name="helper">A Vcc specific helper object that is used to provide the value of the CompilationPart property.</param>
    /// <param name="documentToPreprocess">The unpreprocessed document on which the newly allocated document should be based.</param>
    protected override VccCompositeDocument<VccUnpreprocessedSourceDocument, object> GetNewVersion(VccCompilationHelper helper, VccUnpreprocessedSourceDocument documentToPreprocess) {
      return new VccSourceDocument(helper, documentToPreprocess);
    }

    protected override VccUnpreprocessedSourceDocument GetNextVersionOfDocumentToPreprocess(int position, int length, string updatedText, object version) 
      //^^ requires 0 <= position && position < this.DocumentToPreprocess.Length;
      //^^ requires 0 <= length && length <= this.DocumentToPreprocess.Length;
      //^^ requires 0 <= position+length && position+length <= this.DocumentToPreprocess.Length;
    {
      VccUnpreprocessedSourceDocument documentToPreprocess = this.DocumentToPreprocess;
      //^ assume 0 <= position && position < documentToPreprocess.Length; //follows from precondition
      //^ assume 0 <= length && length <= this.DocumentToPreprocess.Length; //follows from precondition
      //^ assume 0 <= position+length && position+length <= this.DocumentToPreprocess.Length;
      return documentToPreprocess.GetUpdatedDocument(position, length, updatedText);
    }

    protected override VccCompositeDocument<VccUnpreprocessedSourceDocument, object> GetNextVersion(VccCompilationHelper helper,
      VccUnpreprocessedSourceDocument nextVersionOfDocumentToPreprocess, PreprocessorInformation/*?*/ nextVersionOfPreprocessorInformation, int position, int oldLength, int newLength)
      //^^ ensures result.GetType() == this.GetType();
    {
      return new VccSourceDocument(helper, nextVersionOfDocumentToPreprocess, nextVersionOfPreprocessorInformation, this, position, oldLength, newLength); 
    }

    /// <summary>
    /// Makes a shallow copy of this source document (creating a new
    /// </summary>
    public override VccCompositeDocument MakeShallowCopyFor(Compilation targetCompilation) {
      VccCompilationHelper helperCopy = (VccCompilationHelper)this.Helper.MakeShallowCopyFor(targetCompilation);
      PreprocessorInformation/*?*/ nextVersionOfPreprocessorInformation = new PreprocessorInformation(this.DocumentToPreprocess, this.PreprocessorInformation);
      return new VccSourceDocument(helperCopy, this.DocumentToPreprocess, nextVersionOfPreprocessorInformation, this, 0, 0, 0);
    }

    internal override ISourceDocument UnpreprocessedDocument {
      get { return this.DocumentToPreprocess; }
    }
  }

  internal sealed class VccErrorMessage : ErrorMessage {

    private VccErrorMessage(ISourceLocation sourceLocation, long code, string messageKey, params string[] messageArguments)
      : base(sourceLocation, code, messageKey, messageArguments) {
    }

    public VccErrorMessage(ISourceLocation sourceLocation, Error error, params string[] messageArguments)
      : this(sourceLocation, (long)error, error.ToString(), messageArguments) {
    }

    public override object ErrorReporter {
      get { return Microsoft.Research.Vcc.ErrorReporter.Instance; }
    }

    public override string ErrorReporterIdentifier {
      get { return "Vcc"; }
    }

    public override bool IsWarning {
      get {
        return this.Severity != 0; //TODO: check options
      }
    }

    public override ISourceErrorMessage MakeShallowCopy(ISourceDocument targetDocument)
      //^^ requires targetDocument == this.SourceLocation.SourceDocument || targetDocument.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
      //^^ ensures targetDocument == this.SourceLocation.SourceDocument ==> result == this;
    {
      if (this.SourceLocation.SourceDocument == targetDocument) return this;
      ISourceLocation sloc = this.SourceLocation;
      //^ assume targetDocument.IsUpdatedVersionOf(sloc.SourceDocument); //follows from precondition
      return new VccErrorMessage(targetDocument.GetCorrespondingSourceLocation(sloc), this.Code, this.MessageKey, this.MessageArguments());
    }

    public override string Message {
      get {
        ResourceManager resourceManager = new ResourceManager("Microsoft.Research.Vcc.ErrorMessages", this.GetType().Assembly);
        return base.GetMessage(resourceManager);
      }
    }

    public int Severity {
      get {
        switch ((Error)this.Code) {
          case Error.PossibleMistakenNullStatement:
          case Error.SizeOfUnknown:
          case Error.DiscardedContractAtDefinition:
          case Error.PotentialPrecedenceErrorInLogicalExpression:
          case Error.LoopWithOnlySpecStatements:
            return 1;
          default:
            return 0;
        }
      }
    }
  }
}
