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

  internal sealed class EntryPointFinder : BaseMetadataTraverser {

    internal EntryPointFinder(ICompilation compilation) {
      this.compilation = compilation;
      this.entryPoints = new List<IMethodDefinition>();
    }

    readonly ICompilation compilation;
    internal readonly List<IMethodDefinition> entryPoints;

    public override void Visit(IGlobalMethodDefinition method) {
      if (method.Name.Value == "main" && method.IsStatic &&
        (TypeHelper.TypesAreEquivalent(method.Type.ResolvedType, this.compilation.PlatformType.SystemInt32) || 
        TypeHelper.TypesAreEquivalent(method.Type.ResolvedType, this.compilation.PlatformType.SystemVoid)) &&
        ParametersAreOkForMainMethod(method.Parameters)) {
        this.entryPoints.Add(method);
      }
    }

    private static bool ParametersAreOkForMainMethod(IEnumerable<IParameterDefinition> parameters) {
      bool ok = true;
      int count = 0;
      foreach (IParameterDefinition parameter in parameters) {
        if (count++ > 0) { ok = false; break; }
        IArrayType/*?*/ ptype = parameter.Type.ResolvedType as IArrayType;
        ok = ptype != null && ptype.IsVector && TypeHelper.TypesAreEquivalent(ptype.ElementType, ptype.PlatformType.SystemString);
      }
      return ok;
    }

  }

  public sealed class VccAssembly : Assembly {

    public VccAssembly(IName name, string location, ISourceEditHost hostEnvironment, VccOptions options,
      IEnumerable<IAssemblyReference> assemblyReferences, IEnumerable<IModuleReference> moduleReferences, IEnumerable<VccSourceDocument> programSources)
      : base(name, location, name, assemblyReferences, moduleReferences, new List<IResourceReference>(0).AsReadOnly(), new List<IFileReference>(0).AsReadOnly()) {
      this.options = options;
      this.hostEnvironment = hostEnvironment;
      this.programSources = programSources;
    }

    internal VccAssembly(IName name, string location, ISourceEditHost hostEnvironment, VccOptions options,
      IEnumerable<IAssemblyReference> assemblyReferences, IEnumerable<IModuleReference> moduleReferences, IEnumerable<CompilationPart> compilationParts)
      : base(name, location, name, assemblyReferences, moduleReferences, new List<IResourceReference>(0).AsReadOnly(), new List<IFileReference>(0).AsReadOnly()) {
      this.options = options;
      this.hostEnvironment = hostEnvironment;
      this.compilationParts = compilationParts;
    }

    public override Compilation Compilation {
      get
        //^ ensures result is Compilation;
      {
        if (this.compilation == null) {
          lock (GlobalLock.LockingObject) {
            if (this.compilation == null) {
              this.compilation = new VccCompilation(this.hostEnvironment, this, this.options, this.compilationParts ?? this.ProvideCompilationParts());
              //TODO: construct unit sets from references. Associate these with the compilation.
            }
          }
        }
        return this.compilation;
      }
    }
    VccCompilation/*?*/ compilation;

    readonly IEnumerable<CompilationPart>/*?*/ compilationParts;

    protected override RootUnitNamespace CreateRootNamespace()
      //^^ ensures result.RootOwner == this;
    {
      //^ assume false; //constructor can't provide the necessary post condition until Spec# non delayed constructors get fixed
      return new RootUnitNamespace(this.Compilation.NameTable.EmptyName, this);
    }

    public override void Dispatch(IMetadataVisitor visitor) {
      visitor.Visit(this);
    }

    public override IMethodReference EntryPoint {
      get {
        if (this.entryPoint == null) {
          lock (GlobalLock.LockingObject) {
            if (this.entryPoint == null) {
              //TODO: move this to static helper so that Module can share
              EntryPointFinder entryPointFinder = new EntryPointFinder(this.Compilation);
              entryPointFinder.Visit(this);
              IMethodDefinition entryPoint = Dummy.Method;
              foreach (IMethodDefinition ep in entryPointFinder.entryPoints) {
                entryPoint = ep; //TODO: check for dups, invalid args, generics etc. 
              }
              this.entryPoint = entryPoint;
            }
          }
          //report any errors found above
        }
        return this.entryPoint;
      }
    }
    IMethodReference/*?*/ entryPoint;

    readonly ISourceEditHost hostEnvironment;

    public override bool ILOnly {
      get { return true; }
    }

    readonly VccOptions options;

    readonly IEnumerable<VccSourceDocument>/*?*/ programSources;

    IEnumerable<CompilationPart> ProvideCompilationParts() {
      IEnumerable<VccSourceDocument> programSources;
      if (this.programSources == null)
        yield break;
      else
        programSources = this.programSources;
      foreach (VccSourceDocument programSource in programSources)
        yield return programSource.VccCompilationPart;
    }

    public override bool RequiresAmdInstructionSet {
      get { return false; }
    }

    public override bool Requires32bits {
      get { return false; }
    }

    public override bool Requires64bits {
      get { return false; }
    }

    public override bool TrackDebugData {
      get { return false; } //TODO: get this value from the compilation options
    }

    public override bool UsePublicKeyTokensForAssemblyReferences {
      get { return false; }
    }

    public override string Culture {
      get { return string.Empty; } //TODO: obtain from custom attribute
    }

    public override IEnumerable<IAliasForType> ExportedTypes {
      get { return Enumerable<IAliasForType>.Empty; } //TODO: compute this
    }

    public override IEnumerable<ISecurityAttribute> SecurityAttributes {
      get { return Enumerable<ISecurityAttribute>.Empty; } //TODO: compute this
    }

    public override uint Flags {
      get { return 0; } //TODO: compute this
    }

    public override ModuleKind Kind {
      get {
        if (this.EntryPoint.ResolvedMethod == Dummy.Method)
          return ModuleKind.DynamicallyLinkedLibrary;
        return ModuleKind.ConsoleApplication; 
      } //TODO: obtain it from the compiler options
    }

    public override IEnumerable<byte> PublicKey {
      get { return Enumerable<byte>.Empty; } //TODO: obtain it from the compiler options or a custom attribute
    }

    public override Version Version {
      get { return new Version(); } //TODO: obtain from compiler options or custom attributes
    }
  }

  public sealed class VccModule : Module {

    public VccModule(IName name, string location, ISourceEditHost hostEnvironment, VccOptions options, IAssembly containingAssembly,
      IEnumerable<IAssemblyReference> assemblyReferences, IEnumerable<IModuleReference> moduleReferences, IEnumerable<VccSourceDocument> programSources)
      //TODO: pass in information about which assemblies belong to which named unit sets
      : base(name, location, containingAssembly, assemblyReferences, moduleReferences)
    {
      this.options = options;
      this.hostEnvironment = hostEnvironment;
      this.programSources = programSources;
    }

    internal VccModule(IName name, string location, ISourceEditHost hostEnvironment, VccOptions options, IAssembly containingAssembly,
      IEnumerable<IAssemblyReference> assemblyReferences, IEnumerable<IModuleReference> moduleReferences, IEnumerable<CompilationPart> compilationParts)
      //TODO: pass in information about which assemblies belong to which named unit sets
      : base(name, location, containingAssembly, assemblyReferences, moduleReferences) {
      this.options = options;
      this.hostEnvironment = hostEnvironment;
      this.compilationParts = compilationParts;
    }

    public override Compilation Compilation {
      get 
        //^ ensures result is Compilation;
      {
        if (this.compilation == null) {
          this.compilation = new VccCompilation(this.hostEnvironment, this, this.options, this.compilationParts ?? this.ProvideCompilationParts());
          //TODO: construct unit sets from references. Associate these with the compilation.
        }
        return this.compilation;
      }
    }
    VccCompilation/*?*/ compilation;

    readonly IEnumerable<CompilationPart>/*?*/ compilationParts;

    protected override RootUnitNamespace CreateRootNamespace()
      //^^ ensures result.RootOwner == this;
    {
      //^ assume false; //constructor can't provide the necessary post condition until Spec# non delayed constructors get fixed
      return new RootUnitNamespace(this.Compilation.NameTable.EmptyName, this);
    }

    public override void Dispatch(IMetadataVisitor visitor) {
      visitor.Visit(this);
    }

    public override IMethodReference EntryPoint {
      get {
        throw new NotImplementedException(); 
      } //TODO: get from compiler option via the symbol table, using Main as the default
    }

    readonly ISourceEditHost hostEnvironment;

    readonly VccOptions options;

    readonly IEnumerable<VccSourceDocument>/*?*/ programSources;

    IEnumerable<CompilationPart> ProvideCompilationParts() {
      IEnumerable<VccSourceDocument> programSources;
      if (this.programSources == null)
        yield break;
      else
        programSources = this.programSources;
      foreach (VccSourceDocument programSource in programSources)
        yield return programSource.VccCompilationPart;
    }

    public override bool ILOnly {
      get { return true; }
    }

    public override ModuleKind Kind {
      get { return ModuleKind.ConsoleApplication; } //TODO: obtain it from the compiler options
    }

    public override bool RequiresAmdInstructionSet {
      get { return false; } 
    }

    public override bool Requires32bits {
      get { return false; } 
    }

    public override bool Requires64bits {
      get { return false; }
    }
    
    public override bool TrackDebugData {
      get { return true; } //TODO: get these from compiler options

    }

    public override bool UsePublicKeyTokensForAssemblyReferences {
      get { return true; }
    }

    public override ModuleIdentity ModuleIdentity {
      get {
        if (this.moduleIdentity == null) {
          moduleIdentity = UnitHelper.GetModuleIdentity(this);
        }
        return moduleIdentity;
      }
    }
    ModuleIdentity/*?*/ moduleIdentity;
  }
}