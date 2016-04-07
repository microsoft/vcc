//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using Microsoft.Cci.Immutable;
using Microsoft.Research.Vcc.Parsing;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc {

  public interface IVccStatement : IStatement
  {
    void Dispatch(IVccCodeVisitor visitor);
  }

  public interface IVccSpecStatement : IVccStatement
  {
    IStatement WrappedStatement { get; }
  }

  public interface IVccUnwrappingStatement : IVccStatement
  {
    IEnumerable<IExpression> Objects { get; }
    IStatement Body { get; }
  }

  public interface IVccAtomicStatement : IVccStatement
  {
    IEnumerable<IExpression> Objects { get; }
    IStatement Body { get; }
    bool IsGhostAtomic { get; }
  }

  public interface IVccMatchCase : IObjectWithLocations
  {
    IBlockStatement Body { get; }
    bool IsDefault { get; }
  }

  public interface IVccMatchStatement : IVccStatement
  {
    IEnumerable<IVccMatchCase> Cases { get; }
    IExpression Expression { get; }
  }

  public interface IVccCodeVisitor : ICodeVisitor
  {
    void Visit(IVccSpecStatement specStatement);
    void Visit(IVccUnwrappingStatement unwrappingStatment);
    void Visit(IVccAtomicStatement atomicStatement);
    void Visit(IVccMatchStatement matchStatement);
  }

  internal class StatementGroup : Statement {

    internal StatementGroup(List<Statement> statements)
      : base(SourceDummy.SourceLocation)
    {
      this.Statements = statements;
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      return false;
    }

    internal List<Statement> Statements;

    internal static void AddStatementOrGroupToList(Statement s, List<Statement> statements) {
      StatementGroup sg = s as StatementGroup;
      if (sg != null)
        statements.AddRange(sg.Statements);
      else
        statements.Add(s);
    }

    internal static Statement Create(List<Statement> stmts) {
      if (stmts.Count == 1) return stmts[0];
      return new StatementGroup(stmts);
    }
  }

  public class VccLocalDefinition : LocalDefinition, ISpecItem
  {
    internal VccLocalDefinition(VccLocalDeclaration localDeclaration, List<Specifier> specifiers, bool isSpec)
      : base(localDeclaration) {
      this.specifiers = specifiers;
      this.isSpec = isSpec;
    }

    private readonly List<Specifier> specifiers;
    private readonly bool isSpec;

    public bool IsSpec {
      get { return this.isSpec; }
    }

    public bool IsVolatile {
      get { return VccCompilationHelper.ContainsTypeQualifier(this.specifiers, Token.Volatile); }
    }

    private List<ICustomAttribute> GetAttributes() {
      var attributesFromDeclSpec = FunctionDefinition.ConvertSpecifiersIntoAttributes(this.specifiers, new DummyExpression(this.ContainingBlock, SourceDummy.SourceLocation));
      var result = new List<ICustomAttribute>();
      foreach (SourceCustomAttribute extAttr in attributesFromDeclSpec)
        result.Add(new CustomAttribute(extAttr));
      return result;
    }

    public IEnumerable<ICustomAttribute> Attributes {
      get {
        if (this.attributes == null) {
          List<ICustomAttribute> attrs = this.GetAttributes();
          attrs.TrimExcess();
          this.attributes = attrs.AsReadOnly();
        }
        return this.attributes;
      }
    }
    IEnumerable<ICustomAttribute>/*?*/ attributes;
  }

  /// <summary>
  /// A local declaration that appears as part of a statement containing a collection of local declarations, all with the same type.
  /// </summary>
  internal class VccLocalDeclaration : LocalDeclaration, ILocalDeclarationStatement, ISpecItem {
    /// <summary>
    /// Allocates local declaration that appears as part of a statement containing a collection of local declarations, all with the same type.
    /// </summary>
    /// <param name="name">The name of the local.</param>
    /// <param name="initialValue">The value, if any, to assign to the local as its initial value. May be null.</param>
    /// <param name="isSpec">A flag that indicates if this declaration is spec code</param>
    /// <param name="sourceLocation">The source location corresponding to the newly allocated expression.</param>
    /// <param name="specifiers">The specifiers of this declaration</param>
    public VccLocalDeclaration(NameDeclaration name, Expression/*?*/ initialValue, List<Specifier> specifiers, bool isSpec, ISourceLocation sourceLocation)
      : base(false, false, name, initialValue, sourceLocation)
    {
      this.specifiers = specifiers;
      this.isSpec = isSpec;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing block.
    /// </summary>
    /// <param name="containingLocalDeclarationsStatement">The containing statement. This should be different from the containing statement of the template declaration.</param>
    /// <param name="template">The statement to copy.</param>
    protected VccLocalDeclaration(LocalDeclarationsStatement containingLocalDeclarationsStatement, VccLocalDeclaration template)
      : base(containingLocalDeclarationsStatement, template) {
      this.specifiers = new List<Specifier>(template.specifiers);
      this.isSpec = template.isSpec;
    }

    private LanguageSpecificCompilationHelper Helper {
      get { return this.ContainingLocalDeclarationsStatement.CompilationPart.Helper; }
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      var containingSignature = this.ContainingLocalDeclarationsStatement.ContainingBlock.ContainingSignatureDeclaration;
      if (containingSignature != null) {
        foreach (var par in containingSignature.Parameters) {
          if (par.Name.UniqueKey == this.Name.UniqueKey) {
            this.Helper.ReportError(new VccErrorMessage(this.SourceLocation, Error.RedefinitionOfFormalParameter, this.Name.Value));
            return true;
          }
        }
      }
      return false;
    }

    private Expression initialValue;

    private Expression GetInitialValue() {
      VccArrayTypeExpression /*?*/
        arrayTypeExpression = this.ContainingLocalDeclarationsStatement.TypeExpression as VccArrayTypeExpression;
      var baseInit = base.InitialValue;
      if (baseInit == null && arrayTypeExpression != null && arrayTypeExpression.Size != null) {
        VccLocalDefinition loc = this.LocalVariable as VccLocalDefinition;
        var isSpec = loc != null ? loc.IsSpec : false;
        var result = new VccCreateStackArray(arrayTypeExpression.ElementType, arrayTypeExpression.Size, isSpec,
                                       SourceDummy.SourceLocation);
        var containingExpression = new DummyExpression(this.ContainingLocalDeclarationsStatement.ContainingBlock, SourceDummy.SourceLocation);
        result.SetContainingExpression(containingExpression);
        return result;
      }
      else if (baseInit == null) {
        return new DummyExpression(this.Name.SourceLocation);
      }
      else return baseInit;
    }

    public override Expression InitialValue {
      get {
        if (this.initialValue == null) {
          this.initialValue = this.GetInitialValue();
        }

        return this.initialValue is DummyExpression ? null : this.initialValue;
      }
    }

    public override void Dispatch(ICodeVisitor visitor) {
      visitor.Visit(this); // do not go to base.Dispatch because it will not do anything for const decls
    }

    /// <summary>
    /// Makes a copy of this local declaration, changing the ContainingBlock to the given block.
    /// </summary>
    //^ [MustOverride]
    public override LocalDeclaration MakeCopyFor(LocalDeclarationsStatement containingLocalDeclarationsStatement)
      //^^ ensures result.GetType() == this.GetType();
    {
      if (this.ContainingLocalDeclarationsStatement == containingLocalDeclarationsStatement) return this;
      return new VccLocalDeclaration(containingLocalDeclarationsStatement, this);
    }

    protected override LocalDefinition CreateLocalDefinition() {
      return new VccLocalDefinition(this, this.specifiers, this.isSpec);
    }

    private readonly bool isSpec;

    public bool IsSpec {
      get { return this.isSpec; }
    }

    /// <summary>
    /// The type of the local.
    /// </summary>
    public override ITypeDefinition Type {
      [DebuggerNonUserCode]
      get {
        if (this.type == null) {
          ITypeDefinition result;
          VccArrayTypeExpression/*?*/ arrayTypeExpression = this.ContainingLocalDeclarationsStatement.TypeExpression as VccArrayTypeExpression;
          if (arrayTypeExpression != null && arrayTypeExpression.Size != null) {
            result = this.IsSpec ? ((VccCompilationHelper)this.Helper).MakeSpecPointer(arrayTypeExpression.ElementType.ResolvedType) : PointerType.GetPointerType(arrayTypeExpression.ElementType.ResolvedType, this.Helper.Compilation.HostEnvironment.InternFactory);
          } else
            result = this.ContainingLocalDeclarationsStatement.Type;
          this.type = result;
        }
        return this.type;
      }
    }
    //^ [Once]
    ITypeDefinition/*?*/ type;

    private readonly List<Specifier> specifiers;

    #region ILocalDeclarationStatement Members

    IExpression/*?*/ ILocalDeclarationStatement.InitialValue {
      get {
        if (this.InitialValue == null) return null;
        return this.ConvertedInitialValue.ProjectAsIExpression();
      }
    }

    ILocalDefinition ILocalDeclarationStatement.LocalVariable {
      get { return this.LocalVariable; }
    }

    #endregion

  }

  // A local declaration of a function. It is the same as a VccLocalDeclaration except that
  // it contains a pointer to a toplevel mangled function declaration, which is a hack to help resolve
  // this function. 
  // The mangled function declaration should be created during parsing, when a local declaration turns out
  // to be a function type. 
  internal class VccLocalFunctionDeclaration : VccLocalDeclaration {

    internal VccLocalFunctionDeclaration(NameDeclaration name, Expression/*?*/ initialValue, List<Specifier> specifiers, bool isSpec, ISourceLocation sourceLocation, FunctionDeclaration mangledFunctionDeclaration)
      : base (name, initialValue, specifiers, isSpec, sourceLocation) {
      this.mangledFunctionDeclaration = mangledFunctionDeclaration;
    }

    /// <summary>
    /// A copy constructor that allocates an instance that is the same as the given template, except for its containing block.
    /// </summary>
    /// <param name="containingLocalDeclarationsStatement">The containing statement. This should be different from the containing statement of the template declaration.</param>
    /// <param name="template">The statement to copy.</param>
    protected VccLocalFunctionDeclaration(LocalDeclarationsStatement containingLocalDeclarationsStatement, VccLocalFunctionDeclaration template)
      : base(containingLocalDeclarationsStatement, template) {
      this.mangledFunctionDeclaration = template.mangledFunctionDeclaration;
    }

    /// <summary>
    /// Calls the visitor.Visit(IExpressionStatement) method on an assignment statement that initializes the local. 
    /// </summary>
    public override void Dispatch(ICodeVisitor visitor) {
    }

    //^ [MustOverride]
    public override LocalDeclaration MakeCopyFor(LocalDeclarationsStatement containingLocalDeclarationsStatement) {
      if (this.ContainingLocalDeclarationsStatement == containingLocalDeclarationsStatement) return this;
      else return new VccLocalFunctionDeclaration(containingLocalDeclarationsStatement, this);
    }

    public FunctionDeclaration MangledFunctionDeclaration {
      get { return this.mangledFunctionDeclaration; }
    }
    readonly FunctionDeclaration mangledFunctionDeclaration;

  }

  /// <summary>
  /// A special kind of block introduced by the parser for atomic_op. It is used when infering the type
  /// of the VccReturnValue expression.
  /// </summary>
  public class VccAtomicOpBlock : BlockStatement
  {
    public VccAtomicOpBlock(List<Statement> statements, VccAtomicOp atomicOp, ISourceLocation sourceLocation)
      : base(statements, sourceLocation) {
      this.atomicOp = atomicOp;
    }

    protected VccAtomicOpBlock(BlockStatement containingBlock, VccAtomicOpBlock template)
      : base(containingBlock, template) {
      this.atomicOp = template.atomicOp;
    }

    private readonly VccAtomicOp atomicOp;

    public VccAtomicOp AtomicOp {
      get { return this.atomicOp; }
    }

    /// <summary>
    /// Makes a copy of this statement, changing the ContainingBlock to the given block.
    /// </summary>
    //^ [MustOverride]
    public override Statement MakeCopyFor(BlockStatement containingBlock)
      //^^ ensures result.GetType() == this.GetType();
    {
      if (this.ContainingBlock == containingBlock) return this;
      return new VccAtomicOpBlock(containingBlock, this);
    }
  }

  /// <summary>
  /// A special kind of block introduced by the parser for blocks with associated contracts.
  /// It is aware of these contracts and includes these contracts into the SetContainingBlock
  /// operation.
  /// </summary>
  public sealed class VccBlockWithContracts : BlockStatement
  {
    public VccBlockWithContracts(List<Statement> statements, ISourceLocation sourceLocation)
      : base(statements, sourceLocation) {
    }

    private VccBlockWithContracts(BlockStatement containingBlock, VccBlockWithContracts template)
      : base(containingBlock, template) {
    }

    private void SetContainingBlockForContracts() {
      MethodContract mc = this.Compilation.ContractProvider.GetMethodContractFor(this) as MethodContract;
      if (mc != null) mc.SetContainingBlock(this);
    }

    public override void SetContainers(BlockStatement containingBlock, ISignatureDeclaration containingSignatureDeclaration) {
      base.SetContainers(containingBlock, containingSignatureDeclaration);
      this.SetContainingBlockForContracts();
    }

    public override void SetContainers(BlockStatement containingBlock, NamespaceDeclaration containingNamespaceDeclaration) {
      base.SetContainers(containingBlock, containingNamespaceDeclaration);
      this.SetContainingBlockForContracts();
    }

    public override void SetContainers(BlockStatement containingBlock, TypeDeclaration containingTypeDeclaration) {
      base.SetContainers(containingBlock, containingTypeDeclaration);
      this.SetContainingBlockForContracts();
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      this.SetContainingBlockForContracts();
    }

    /// <summary>
    /// Makes a copy of this statement, changing the ContainingBlock to the given block.
    /// </summary>
    //^ [MustOverride]
    public override Statement MakeCopyFor(BlockStatement containingBlock)
      //^^ ensures result.GetType() == this.GetType();
    {
      if (this.ContainingBlock == containingBlock) return this;
      return new VccBlockWithContracts(containingBlock, this);
    }
  }

  public class VccAssertStatement : AssertStatement
  {
    public VccAssertStatement(Expression condition, ISourceLocation sourceLocation)
      : base(condition, sourceLocation) {
    }

    public VccAssertStatement(BlockStatement containingBlock, VccAssertStatement template) 
      : base(containingBlock, template) {
    }

    private void CopyTriggersFromTemplate(VccAssertStatement template) {
      IEnumerable<IEnumerable<Expression>>/*?*/ triggers = template.Compilation.ContractProvider.GetTriggersFor(template);
      if (triggers != null) {
        IEnumerable<IEnumerable<Expression>> copiedTriggers = CopyTriggers(triggers, this.ContainingBlock);
        this.Compilation.ContractProvider.AssociateTriggersWithQuantifier(this, copiedTriggers);
      }
    }

    private static IEnumerable<IEnumerable<Expression>> CopyTriggers(IEnumerable<IEnumerable<Expression>> triggers, BlockStatement containingBlock) {
      List<IEnumerable<Expression>> copiedTriggers = new List<IEnumerable<Expression>>();
      foreach (IEnumerable<Expression> trigger in triggers) {
        List<Expression> copiedTrigger = new List<Expression>();
        foreach (Expression e in trigger) {
          copiedTrigger.Add(e.MakeCopyFor(containingBlock));
        }
        copiedTriggers.Add(copiedTrigger.AsReadOnly());
      }
      return copiedTriggers.AsReadOnly();
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      IEnumerable<IEnumerable<Expression>>/*?*/ triggers = this.Compilation.ContractProvider.GetTriggersFor(this);
      if (triggers != null) {
        Expression dummyExpression = new DummyExpression(containingBlock, this.SourceLocation);
        foreach (IEnumerable<Expression> trigger in triggers)
          foreach (Expression e in trigger)
            e.SetContainingExpression(dummyExpression);
      }
    }

    public override Statement MakeCopyFor(BlockStatement containingBlock) {
      if (this.ContainingBlock == containingBlock) return this;
      var result = new VccAssertStatement(containingBlock, this);
      result.CopyTriggersFromTemplate(this);
      return result;
    }
  }

  public sealed class VccSpecStatement : Statement, IVccSpecStatement
  {
    private readonly Statement wrappedStatement;

    public VccSpecStatement(Statement statement, ISourceLocation sourceLocation)
      : base(sourceLocation) { 
      this.wrappedStatement = statement;
    }

    private VccSpecStatement(BlockStatement containingBlock, VccSpecStatement template)
      : base(containingBlock, template) {
      this.wrappedStatement = template.wrappedStatement.MakeCopyFor(containingBlock);
    }

    public Statement WrappedStatement {
      get { return this.wrappedStatement; }
    }

    IStatement IVccSpecStatement.WrappedStatement {
      get { return this.wrappedStatement; }
    }

    public override void Dispatch(ICodeVisitor visitor) {
      this.WrappedStatement.Dispatch(visitor);
    }

    public  void Dispatch(IVccCodeVisitor visitor) {
      visitor.Visit(this);
    }

    public override void Dispatch(SourceVisitor visitor) {
      this.WrappedStatement.Dispatch(visitor);
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      this.WrappedStatement.SetContainingBlock(containingBlock);
    }

    public override Statement MakeCopyFor(BlockStatement containingBlock) {
      if (containingBlock == this.ContainingBlock) return this;
      return new VccSpecStatement(containingBlock, this);
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      return this.WrappedStatement.HasErrors;
    }
  }

  public sealed class VccUnwrappingStatement : Statement, IVccUnwrappingStatement
  {

    public VccUnwrappingStatement(Statement body, IEnumerable<Expression> exprs, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.expressions = exprs;
      this.body = body;
    }

    private VccUnwrappingStatement(BlockStatement containingBlock, VccUnwrappingStatement template)
      : base(containingBlock, template) {
      this.expressions = template.expressions.Select(e => e.MakeCopyFor(containingBlock)).ToArray();
      this.body = template.body.MakeCopyFor(containingBlock);
    }

    public IEnumerable<Expression> Expressions {
      get { return this.expressions; }
    }
    private readonly IEnumerable<Expression> expressions;

    public Statement Body {
      get { return this.body; }
    }
    private readonly Statement body;

    public void Dispatch(IVccCodeVisitor visitor) {
      visitor.Visit(this);
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      return this.Expressions.Any(e => e.HasErrors) || 
             this.Expressions.Any(e => e.HasSideEffect(true)) || 
             this.Body.HasErrors;
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      this.body.SetContainingBlock(containingBlock);
      DummyExpression containingExpression = new DummyExpression(containingBlock, SourceDummy.SourceLocation);
      foreach (var e in this.expressions)
        e.SetContainingExpression(containingExpression);
    }

    public override Statement MakeCopyFor(BlockStatement containingBlock) {
      if (this.ContainingBlock == containingBlock) return this;
      return new VccUnwrappingStatement(containingBlock, this);
    }

    IEnumerable<IExpression> IVccUnwrappingStatement.Objects {
      get { return this.expressions.Select(e => e.ProjectAsIExpression()).ToArray(); }
    }

    IStatement IVccUnwrappingStatement.Body {
      get { return this.body; }
    }
  }

  public sealed class VccAtomicStatement : Statement, IVccAtomicStatement
  {

    public VccAtomicStatement(Statement body, IEnumerable<Expression> exprs, ISourceLocation sourceLocation, bool isGhostAtomic)
      : base(sourceLocation) {
      this.expressions = exprs;
      this.body = body;
      this.isGhostAtomic = isGhostAtomic;
    }

    private VccAtomicStatement(BlockStatement containingBlock, VccAtomicStatement template)
      : base(containingBlock, template) {
      var exprs = new List<Expression>();
      foreach (var expr in template.expressions)
        exprs.Add(expr.MakeCopyFor(containingBlock));
      exprs.TrimExcess();
      this.expressions = exprs;
      this.body = template.body.MakeCopyFor(containingBlock);
      this.isGhostAtomic = template.isGhostAtomic;
    }

    public IEnumerable<Expression> Expressions {
      get { return this.expressions; }
    }
    private readonly IEnumerable<Expression> expressions;

    public Statement Body {
      get { return this.body; }
    }
    private readonly Statement body;

    public bool IsGhostAtomic {
      get { return this.isGhostAtomic; }
    }
    private bool isGhostAtomic;

    public void Dispatch(IVccCodeVisitor visitor) {
      visitor.Visit(this);
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      bool result = false;
      foreach (var expr in this.Expressions)
        result |= expr.HasErrors || expr.HasSideEffect(true);
      return result || this.Body.HasErrors;
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      this.body.SetContainingBlock(containingBlock);
      DummyExpression containingExpression = new DummyExpression(containingBlock, SourceDummy.SourceLocation);
      foreach (var expr in this.Expressions)
        expr.SetContainingExpression(containingExpression);
    }

    public override Statement MakeCopyFor(BlockStatement containingBlock) {
      if (this.ContainingBlock == containingBlock) return this;
      return new VccAtomicStatement(containingBlock, this);
    }

    IEnumerable<IExpression> IVccAtomicStatement.Objects {
      get {
        foreach (var expr in this.Expressions)
          yield return expr.ProjectAsIExpression();
      }
    }

    IStatement IVccAtomicStatement.Body {
      get { return this.body; }
    }
  }

  public sealed class VccMatchCase : CheckableSourceItem, IVccMatchCase
  {
    public VccMatchCase(Expression pattern, IEnumerable<Statement> body, ISourceLocation sourceLocation)
      : base(sourceLocation)
    {
      this.pattern = pattern;
      this.statements = body;
    }

    internal SwitchCase ToSwitchCase()
    {
      return new SwitchCase(this.pattern, this.statements, this.sourceLocation);
    }

    internal void AddEmptyStatement()
    {
      var stmts = this.statements.ToList();
      if (stmts.Count == 0) {
        stmts.Add(new EmptyStatement(true, this.SourceLocation));
        this.statements = stmts;
      }
    }

    private VccMatchCase(VccMatchStatement stmt, VccMatchCase template)
      : base(template.sourceLocation)
    {
      this.containingMatchStatement = stmt;
      this._body = (BlockStatement)template.Body.MakeCopyFor(stmt.Block);
      if (template.pattern != null)
        this.pattern = template.pattern.MakeCopyFor(stmt.Block);
    }

    internal VccMatchCase MakeCopyFor(VccMatchStatement stmt)
    {
      if (stmt == this.containingMatchStatement)
        return this;
      return new VccMatchCase(stmt, this);
    }

    private LanguageSpecificCompilationHelper Helper {
      get { return this.ContainingMatchStatement.Block.CompilationPart.Helper; }
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound()
    {
      if (pattern == null)
        return Body.HasErrors;

      var hasError = false;
      var newStmts = new List<Statement>();
      var newBlock = new BlockStatement(newStmts, this.SourceLocation);
      var call = pattern as VccMethodCall;
      if (call == null) {
        this.Helper.ReportError(new VccErrorMessage(pattern.SourceLocation, Error.ExpectedIdentifier));
        return true;
      }

      var args = call.OriginalArguments.ToArray();
      var calledMethod = call.MethodExpression as VccSimpleName;
      if (calledMethod == null) {
        this.Helper.ReportError(new VccErrorMessage(call.MethodExpression.SourceLocation, Error.ExpectedIdentifier));
        return true;
      }

      var methods = call.GetCandidateMethods(true).Where(m => m.ParameterCount == args.Length).ToArray();
      if (methods.Length == 0) {
        if (!call.MethodExpression.HasErrors)
          this.Helper.ReportError(new AstErrorMessage(call, Cci.Ast.Error.BadNumberOfArguments, calledMethod.Name.Value, args.Length.ToString()));
        return true;
      }

      var meth = (MethodDefinition)methods.First();
      var decl = (FunctionDefinition)meth.Declaration;
      var parms = decl.Parameters.ToArray();
      List<Statement> stmts = new List<Statement>();
      for (int i = 0; i < args.Length; ++i) {
        var name = args[i] as VccSimpleName;
        if (name == null) {
          this.Helper.ReportError(new VccErrorMessage(args[i].SourceLocation, Error.ExpectedIdentifier));
          hasError = true;
        } else {
          var local = new VccLocalDeclaration(new NameDeclaration(name.Name, name.SourceLocation), null, new List<Specifier>(), true, name.SourceLocation);
          var tp = (TypeExpression)parms[i].Type;
          //tp = (TypeExpression)tp.MakeCopyFor(newBlock);
          var stmt = new LocalDeclarationsStatement(false, true, false, tp, new LocalDeclaration[] { local }.ToList(), name.SourceLocation);
          newStmts.Add(stmt);
        }
      }

      newStmts.Add(new ExpressionStatement(call));

      if (_body != null)
        newStmts.AddRange(_body.Statements);
      else
        newStmts.AddRange(statements);

      _body = newBlock;
      newBlock.SetContainingBlock(containingMatchStatement.ContainingBlock);
      hasError |= newBlock.HasErrors;

      return hasError;
    }

    private readonly Expression pattern;

    public BlockStatement Body
    {
      get {
        if (_body == null) {
          _body = new BlockStatement(statements.ToList(), this.sourceLocation);
          _body.SetContainingBlock(containingMatchStatement.ContainingBlock);
        }
        return _body; 
      }
    }
    private BlockStatement _body;
    private IEnumerable<Statement> statements;

    IBlockStatement IVccMatchCase.Body
    {
      get { return Body; }
    }

    public bool IsDefault
    {
      get { return pattern == null; }
    }

    public VccMatchStatement ContainingMatchStatement
    {
      get { return this.containingMatchStatement; }
    }
    VccMatchStatement containingMatchStatement;

    public void SetContainingMatchStatement(VccMatchStatement stmt)
    {
      this.containingMatchStatement = stmt;
      if (this.pattern != null) {
        this.pattern.SetContainingExpression(new DummyExpression(stmt.Block, SourceDummy.SourceLocation));
      }
      Body.SetContainingBlock(stmt.Block);
    }
  }


  public sealed class VccMatchStatement : Statement, IVccMatchStatement
  {
    public VccMatchStatement(Expression expr, IEnumerable<VccMatchCase> cases, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.expression = expr;
      this.cases = cases;
    }

    private VccMatchStatement(BlockStatement containingBlock, VccMatchStatement template)
      : base(containingBlock, template) {
      var cases = new List<VccMatchCase>();
      foreach (var cs in template.cases)
        cases.Add(cs.MakeCopyFor(this));
      cases.TrimExcess();
      this.cases = cases;
      this.expression = template.expression.MakeCopyFor(containingBlock);
    }

    public IExpression Expression {
      get { return this.expression.ProjectAsIExpression(); }
    }
    private readonly Expression expression;

    public IEnumerable<IVccMatchCase> Cases {
      get { return this.cases; }
    }
    private readonly IEnumerable<VccMatchCase> cases;

    public void Dispatch(IVccCodeVisitor visitor) {
      visitor.Visit(this);
    }

    protected override bool CheckForErrorsAndReturnTrueIfAnyAreFound() {
      bool result = false;
      foreach (var expr in this.cases)
        result |= expr.HasErrors;
      return result || this.expression.HasErrors;
    }

    public override void SetContainingBlock(BlockStatement containingBlock) {
      base.SetContainingBlock(containingBlock);
      foreach (var cs in this.cases)
        cs.SetContainingMatchStatement(this);
      DummyExpression containingExpression = new DummyExpression(containingBlock, SourceDummy.SourceLocation);
      this.expression.SetContainingExpression(containingExpression);
    }

    public override Statement MakeCopyFor(BlockStatement containingBlock) {
      if (this.ContainingBlock == containingBlock) return this;
      return new VccMatchStatement(containingBlock, this);
    }

    public BlockStatement Block
    {
      get
      {
        if (this.block == null) {
          List<Statement> statements = new List<Statement>(1);
          BlockStatement block = new BlockStatement(statements, this.SourceLocation);
          block.SetContainingBlock(this.ContainingBlock);
          statements.Add(this);
          this.block = block;
        }
        return this.block;
      }
    }
    //^ [Once]
    private BlockStatement/*?*/ block;
  }


}