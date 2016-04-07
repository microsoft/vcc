//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using System.Linq;

//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc.Parsing {

  [System.Diagnostics.DebuggerDisplay("CurrentToken = {this.currentToken}, {this.scanner.GetIdentifierString()}")]
  internal abstract class Parser {

    protected delegate TResult Func<in T, out TResult>(T arg);
    protected delegate TResult Func<in T1, in T2, out TResult>(T1 arg1, T2 arg2);

    protected readonly Compilation compilation;
    protected readonly Dictionary<string, TypedefDeclaration> typedefs = new Dictionary<string, TypedefDeclaration>();
    protected readonly Dictionary<string, bool> locallyDefinedNames = new Dictionary<string, bool>();
    protected readonly Dictionary<string, string> functionContractExtensions = new Dictionary<string, string>();
    protected readonly Dictionary<string, string> castlikeFunctions = new Dictionary<string, string>();
    protected readonly Dictionary<string, string> declspecExtensions = new Dictionary<string, string>();
    protected readonly Dictionary<string, string> statementLikeFunctions = new Dictionary<string, string>();
    protected readonly Dictionary<Expression, bool> emptyStructuredTypes = new Dictionary<Expression, bool>();
    protected readonly Scanner scanner;
    protected readonly List<IErrorMessage> scannerAndParserErrors;
    protected readonly RootNamespaceExpression rootNs;
    protected readonly AliasQualifiedName systemNs;
    protected readonly INameTable nameTable;

    protected List<FieldDeclaration>/*?*/ currentSpecificationFields;
    protected List<TypeInvariant>/*?*/ currentTypeInvariants;
    protected List<ITypeDeclarationMember>/*?*/ currentTypeMembers;
    protected LexicalScope/*?*/ currentLexicalScope;
    protected Token currentToken;
    protected Expression/*?*/ currentTypeName;
    protected bool resultIsAKeyword;
    protected bool outIsAKeyword;
    protected bool inSpecCode;

    protected enum FixedSizeArrayContext
    {
      AsField,
      AsParameter,
      AsLocal
    }

    internal static Parser Create(Compilation compilation, ISourceLocation sourceLocation, List<IErrorMessage> scannerAndParserErrors) {
      return new ParserV2(compilation, sourceLocation, scannerAndParserErrors);
    }

    // the following virtual functions used to make the difference between the V1 and V2 syntax
    // now that the V1 syntax is no-longer supported, they remain abstract

    protected abstract void ParseGlobalSpecDeclarationList(List<INamespaceDeclarationMember> members, List<ITypeDeclarationMember> globalMembers, TokenSet followers);
    protected abstract void ParseNonLocalDeclarationInSpecBlock(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal, List<TemplateParameterDeclarator> templateParameters, List<Specifier> specifiers);
    protected abstract LoopContract/*?*/ ParseLoopContract(TokenSet followers);
    protected abstract bool TryToGetBuiltInSpecTypeName(TypedefNameSpecifier typedefName, out TypeExpression result);
    protected abstract Expression ParseBraceLabeledExpression(SourceLocationBuilder slb, TokenSet followers);
    protected abstract List<Parameter> ParseParameterList(TokenSet followers);
    protected abstract void ParseFunctionOrBlockContract(FunctionOrBlockContract contract, TokenSet followers);
    protected abstract bool ParseSpecTypeModifiers(List<Specifier> specifiers, TokenSet followers);
    protected abstract void ParseTypeMemberDeclarationList(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers);
    protected abstract Statement ParseSpecStatements(TokenSet followers);
    protected abstract Expression ParseSpecCastExpression(TokenSet followers);
    protected abstract Expression ParseQuantifier(TokenSet followers);
    protected abstract Expression ParseLabeledExpression(TokenSet followers, bool inInvariant);
    protected abstract List<Expression> ParseArgumentList(SourceLocationBuilder slb, TokenSet followers);
    protected abstract void SkipSemiColonAfterDeclarationOrStatement(TokenSet followers);

    protected Parser(Compilation compilation, ISourceLocation sourceLocation, List<IErrorMessage> scannerAndParserErrors, bool isV2 = false)
    {
      this.compilation = compilation;
      this.nameTable = compilation.NameTable;
      this.scannerAndParserErrors = scannerAndParserErrors;
      this.scanner = new Scanner(scannerAndParserErrors, sourceLocation, ignoreComments: true, underscoreIsKeyword: isV2);
      this.rootNs = new RootNamespaceExpression(SourceDummy.SourceLocation);
      this.systemNs = new AliasQualifiedName(rootNs, this.GetSimpleNameFor("System"), SourceDummy.SourceLocation);
    }

    protected bool EnterSpecBlock() {
      bool old = this.inSpecCode;
      this.inSpecCode = true;
      return old;
    }

    protected void LeaveSpecBlock(bool previousState) {
      this.inSpecCode = previousState;
    }

    protected bool InSpecCode {
      get { return this.inSpecCode; }
    }

    protected IName GetNameFor(string name)
      //^ ensures result.Value == name;
    {
      return this.nameTable.GetNameFor(name);
    }

    protected void GetNextToken()
      //^ requires this.currentToken != Token.EndOfFile;
    {
      this.currentToken = this.scanner.GetNextToken(this.inSpecCode, false);
      if (this.currentToken == Token.Pragma) {
        this.ParsePragma();
      }
    }

    protected void GetNextToken(bool specKeywordExpected)
      //^ requires this.currentToken != Token.EndOfFile;
{
      this.currentToken = this.scanner.GetNextToken(this.inSpecCode, specKeywordExpected);
      if (this.currentToken == Token.Pragma) {
        this.ParsePragma();
      }
    }

    protected void HandleError(Error error, params string[] messageParameters) 
      // ^ modifies this.scannerAndParserErrors;
      //^ ensures this.currentToken == old(this.currentToken);
    {
      this.HandleError(this.scanner.SourceLocationOfLastScannedToken, error, messageParameters);
    }

    protected void HandleError(ISourceLocation errorLocation, Error error, params string[] messageParameters)
      // ^ modifies this.scannerAndParserErrors;
      //^ ensures this.currentToken == old(this.currentToken);
    {
      //^ Token oldToken = this.currentToken;
      this.scannerAndParserErrors.Add(new VccErrorMessage(errorLocation, error, messageParameters));
      //^ assume this.currentToken == oldToken;
    }

    protected void WarnIfLoopWithContractAndEmptyBody(LoopContract contract, Statement body)
    {
      if (contract != null && body is EmptyStatement)
        this.HandleError(body.SourceLocation, Error.PossibleMistakenNullStatement);

      if (body is VccAssertStatement || body is AssumeStatement || body is VccSpecStatement)
        this.HandleError(body.SourceLocation, Error.LoopWithOnlySpecStatements);
    }

    /// <summary>
    /// Call this method only on a freshly allocated Parser instance and call it only once.
    /// </summary>
    internal virtual void ParseCompilationUnit(GlobalDeclarationContainerClass globalContainer, List<INamespaceDeclarationMember> members) {
      //^ assume this.currentToken != Token.EndOfFile; //assume this method is called directly after construction and then never again.
      this.GetNextToken(); //Get first token from scanner
      this.ParseGlobalDeclarations(globalContainer, members, TS.EndOfFile);
      VccTypeContract tc = new VccTypeContract(this.currentSpecificationFields, this.currentTypeInvariants, false);
      this.compilation.ContractProvider.AssociateTypeWithContract(globalContainer, tc);
    }

    protected NameDeclaration ParseNameDeclaration(bool requireIdentifier) {
      IName name;
      ISourceLocation sourceLocation = this.scanner.SourceLocationOfLastScannedToken;
      bool compilerGenerated = false;
      if (this.currentToken == Token.Identifier) {
        name = this.GetNameFor(this.scanner.GetIdentifierString());
        this.GetNextToken();
      } else {
        if (requireIdentifier) this.HandleError(Error.ExpectedIdentifier);
        name = this.GetNameFor(SanitizeString(sourceLocation.SourceDocument.Name.Value)+".."+sourceLocation.StartIndex);
        compilerGenerated = true;
      }
      return new VccNameDeclaration(name, compilerGenerated, sourceLocation);
    }

    protected static string SanitizeString(string str) {
      StringBuilder result = new StringBuilder(str.Length);
      foreach (var c in str) {
        switch (c) {
          case '$':
          case '%':
          case '\'':
          case '-':
          case '@':
          case '~':
          case '`':
          case '!':
          case '(':
          case ')':
          case '&':
          case '+':
          case ',':
          case ';':
          case '=':
          case '[':
          case ']':
          case ' ':
            result.Append('_');
            break;
          default: 
            result.Append(c);
            break;
        }
      }
      return result.ToString();
    }

    protected Expression ParseScopedName(Expression qualifier, TokenSet followers)
    {
      Expression result = qualifier;
      while (this.currentToken == Token.ScopeResolution) {
        SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
        this.GetNextToken();
        SimpleName name = this.ParseSimpleName(followers);
        slb.UpdateToSpan(name.SourceLocation);
        result = new VccScopedName(result, name, slb.GetSourceLocation());
      }
      return result;
    }

    protected Expression ParseSimpleOrScopedName(TokenSet followers)
    {
      followers |= Token.ScopeResolution;
      SimpleName qualifier = this.ParseSimpleName(followers);
      return ParseScopedName(qualifier, followers);
    }

    protected VccSimpleName ParseSimpleName(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      IName name;
      ISourceLocation sourceLocation = this.scanner.SourceLocationOfLastScannedToken;
      if (this.currentToken == Token.Identifier) {
        name = this.GetNameFor(this.scanner.GetIdentifierString());
        //^ assume this.currentToken != Token.EndOfFile;
        this.GetNextToken();
      } else {
        name = Dummy.Name;
        this.HandleError(Error.ExpectedIdentifier);
      }
      VccSimpleName result = new VccSimpleName(name, sourceLocation);
      this.SkipTo(followers);
      return result;
    }

    List<INamespaceDeclarationMember>/*?*/ namespaceDeclarationMembers;

    protected void ParseGlobalDeclarations(GlobalDeclarationContainerClass globalContainer, List<INamespaceDeclarationMember> members, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      List<ITypeDeclarationMember> globalMembers = (List<ITypeDeclarationMember>)globalContainer.GlobalMembers;

      this.currentTypeMembers = globalMembers;
      this.namespaceDeclarationMembers = members;
      this.ParseGlobalDeclarationList(members, globalMembers, followers);
      this.SkipTo(followers);
    }

    protected void ParseGlobalDeclarationList(List<INamespaceDeclarationMember> members, List<ITypeDeclarationMember> globalMembers, TokenSet followers) {
      TokenSet followersOrDeclarationStart = followers | TS.DeclarationStart;
      while (TS.DeclarationStart[this.currentToken] && this.currentToken != Token.EndOfFile) {
        if (this.currentToken == Token.Specification)
          this.ParseGlobalSpecDeclarationList(members, globalMembers, followersOrDeclarationStart);
        else
          this.ParseNonLocalDeclaration(members, globalMembers, followersOrDeclarationStart, true);
      }
    }

    protected void ParseNonLocalDeclaration(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal) {
      this.ParseNonLocalDeclaration(namespaceMembers, typeMembers, followers, isGlobal, null);
    }

    protected void ParseNonLocalDeclaration(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal, List<Specifier> specSpecifiers)
      //^ requires this.currentToken != Token.EndOfFile;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      List<TemplateParameterDeclarator>/*?*/ templateParameters = this.ParseTemplateParameters(followers|TS.DeclaratorStartOrRightParenOrSemicolon);
      this.InitializeLocallyDefinedNamesFromParameters(templateParameters);
      List<Specifier> specifiers = this.ParseSpecifiers(namespaceMembers, typeMembers, specSpecifiers, followers | TS.DeclaratorStart | Token.Semicolon);

      if (this.currentToken == Token.Specification) 
        ParseNonLocalDeclarationInSpecBlock(namespaceMembers, typeMembers, followers, isGlobal, templateParameters, specifiers);
      else 
        ParseNonLocalDeclaration(typeMembers, followers, isGlobal, templateParameters, specifiers);
    }

    private void ParseNonLocalDeclaration(List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal, List<TemplateParameterDeclarator> templateParameters, List<Specifier> specifiers) {
      VccFunctionTypeExpression/*?*/ functionTypeExpression = null;
      TypedefNameSpecifier/*?*/ typeDefName = GetTypedefNameSpecifier(specifiers);
      if (typeDefName != null) {
        TypedefDeclaration/*?*/ typeDefDecl;
        if (this.typedefs.TryGetValue(typeDefName.TypedefName.Name.Value, out typeDefDecl))
          functionTypeExpression = typeDefDecl.Type as VccFunctionTypeExpression;
      }
      bool foundNoDeclaration = true;
      TokenSet followersOrCommaOrLeftBraceOrSemicolon = followers | Token.Comma | Token.LeftBrace | Token.Semicolon;
      while (TS.DeclaratorStart[this.currentToken]) {
        foundNoDeclaration = false;
        Declarator declarator = this.ParseDeclarator(templateParameters, followersOrCommaOrLeftBraceOrSemicolon, false);
        if (functionTypeExpression != null && functionTypeExpression.declarator != null && declarator is IdentifierDeclarator)
          declarator = new FunctionDeclarator(declarator, functionTypeExpression.declarator);
        else {
          // List<Specifier> innerSpecifiers = this.ParseSpecifiers(namespaceMembers, followers | Parser.DeclarationStart | Token.Semicolon | Token.Colon);
          declarator = this.UseDeclaratorAsTypeDefNameIfThisSeemsIntended(specifiers, declarator, followersOrCommaOrLeftBraceOrSemicolon);
        }
        PointerDeclarator/*?*/ pointerDeclarator = declarator as PointerDeclarator;
        FunctionDeclarator/*?*/ funcDeclarator = declarator as FunctionDeclarator;
        ArrayDeclarator/*?*/ arrayDeclarator = declarator as ArrayDeclarator;
        while (funcDeclarator == null && (pointerDeclarator != null || arrayDeclarator != null)) {
          if (pointerDeclarator != null) {
            funcDeclarator = pointerDeclarator.Declarator as FunctionDeclarator;
            arrayDeclarator = pointerDeclarator.Declarator as ArrayDeclarator;
            pointerDeclarator = null;
          } else if (arrayDeclarator != null) {
            funcDeclarator = arrayDeclarator.ElementType as FunctionDeclarator;
            pointerDeclarator = arrayDeclarator.ElementType as PointerDeclarator;
            arrayDeclarator = null;
          }
        }

        if (funcDeclarator != null) {
          //TODO: complain if not first declarator
          if (this.currentToken == Token.LeftBrace) {
            this.ParseFunctionDefinition(specifiers, typeMembers, declarator, funcDeclarator, followers | Token.Semicolon);
            if (this.currentToken == Token.Semicolon) 
              this.SkipSemiColon(followers);
            return;
          } else
            this.ParseFunctionDeclaration(specifiers, typeMembers, declarator, funcDeclarator, followers | Token.Semicolon, isGlobal);
        } else {
          InitializedDeclarator iDecl = declarator as InitializedDeclarator;
          if (iDecl != null) {
            FunctionDeclarator fDecl = iDecl.Declarator as FunctionDeclarator;
          }
          //TODO: complain if templateParameters are not null
          this.AddTypeDeclarationMember(specifiers, declarator, typeMembers, isGlobal);
        }
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      if (specifiers.Count > 0 && specifiers[specifiers.Count - 1] is CompositeTypeSpecifier) {
        if (this.currentTypeName != null && foundNoDeclaration) {
          StructSpecifier structSpecifier = specifiers[specifiers.Count - 1] as StructSpecifier;
          UnionSpecifier unionSpecifier = specifiers[specifiers.Count - 1] as UnionSpecifier;
          if (structSpecifier != null || unionSpecifier != null) {
            if (structSpecifier == null || !this.emptyStructuredTypes.ContainsKey(structSpecifier.TypeExpression)) {
              Declarator declarator = new AnonymousFieldDeclarator();
              this.AddTypeDeclarationMember(specifiers, declarator, typeMembers);
            }
          }
        }
      }

      this.SkipSemiColonAfterDeclarationOrStatement(followers);
    }

    protected List<Statement> ParseLocalDeclaration(TokenSet followers) {
      return this.ParseLocalDeclaration(new Specifier[] { }, followers);
    }

    protected List<Statement> ParseLocalDeclaration(IEnumerable<Specifier> previousSpecifiers, TokenSet followers) {  
      // Because, in C, a local declaration may introduce a type definition to the global scope
      // pass in the namespace declaration members so that these definitions can be found later. 
      var specifiers = new List<Specifier>(previousSpecifiers);
      var additionalSpecifiers = this.ParseSpecifiers(this.namespaceDeclarationMembers, null, null, followers|Token.Semicolon|Token.BitwiseXor);
      specifiers.AddRange(additionalSpecifiers);
      bool isLocalTypeDef = VccCompilationHelper.ContainsStorageClassSpecifier(specifiers, Token.Typedef);
      List<Statement> result = new List<Statement>();
      while (TS.DeclaratorStart[this.currentToken]) {
        Declarator declarator = this.ParseDeclarator(followers|Token.Comma|Token.LeftBrace|Token.Semicolon);
        declarator = this.UseDeclaratorAsTypeDefNameIfThisSeemsIntended(specifiers, declarator, followers);
        if (isLocalTypeDef) {
          this.AddTypeDeclarationMember(specifiers, declarator, this.currentTypeMembers);
          break;
        }
        this.AddDeclarationStatement(specifiers, declarator, result);
        this.locallyDefinedNames[declarator.Identifier.Name.Value] = true;
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      this.SkipSemiColonAfterDeclarationOrStatement(followers);
      return result;
    }

    protected LoopInvariant ParseLoopInvariant(TokenSet followers)
    //^ requires this.currentToken == Token.Invariant;
    //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      return this.ParseExpressionWithParens(followers, (expr, slb) => new LoopInvariant(expr, slb));
    }

    protected Expression ParseLoopVariant(TokenSet followers)
    //^ requires this.currentToken == Token.Variants;
    //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      return this.ParseExpressionWithParens(followers, (expr, slb) => expr);
    }

    protected void ParseTypeInvariant(TokenSet followers)
      //^ requires this.currentToken == Token.Invariant;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      NameDeclaration nameDecl = null;
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      if (this.currentToken == Token.Identifier) {
        string id = this.scanner.GetIdentifierString();
        Scanner.Snapshot snap = this.scanner.MakeSnapshot();
        Token tok = scanner.GetNextToken(false, false);
        if (tok == Token.Colon) {
          slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
          nameDecl = new VccNameDeclaration(this.GetNameFor(id), slb);
          this.GetNextToken();
        } else {
          this.scanner.RevertToSnapshot(snap);
        }
      }
      Expression condition = this.ParseExpression(followers|Token.RightParenthesis);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      this.Skip(Token.RightParenthesis);
      TypeInvariant typeInvariant = new TypeInvariant(nameDecl, new CheckedExpression(condition, condition.SourceLocation), false, slb);
      this.AddTypeInvariantToCurrent(typeInvariant);
      if (this.currentToken == Token.Semicolon)
        this.SkipOverTo(Token.Semicolon, followers);
    }

    protected void AddTypeInvariantToCurrent(TypeInvariant typeInvariant) {
      if (this.currentTypeInvariants == null)
        this.currentTypeInvariants = new List<TypeInvariant>();
      this.currentTypeInvariants.Add(typeInvariant);
    }

    protected void ParseFunctionDeclaration(List<Specifier> specifiers, List<ITypeDeclarationMember> typeMembers,
      Declarator declarator, FunctionDeclarator funcDeclarator, TokenSet followers, bool isGlobal)
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(funcDeclarator.SourceLocation);
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[0].SourceLocation);
      Token storageClass = GetStorageClassToken(specifiers);
      if (funcDeclarator.Specifiers != null) {
        foreach (Specifier sp in funcDeclarator.Specifiers) {
          specifiers.Add(sp);
        }
        // specifiers = funcDeclarator.Specifiers; //TODO: combine the specifiers?
      }
      TypeMemberVisibility visibility = storageClass == Token.Static ? TypeMemberVisibility.Assembly : TypeMemberVisibility.Public;
      PointerDeclarator/*?*/ pointerToFunc = funcDeclarator.FunctionName as PointerDeclarator;
      TypeExpression returnType;
      if (pointerToFunc != null)
        returnType = this.GetTypeExpressionFor(specifiers, pointerToFunc.Declarator);
      else
        returnType = this.GetTypeExpressionFor(specifiers, funcDeclarator.FunctionName);
      if (declarator != funcDeclarator)
        returnType = this.ApplyDeclarator(declarator, returnType);
      if (pointerToFunc != null || storageClass == Token.Typedef) {
        TypeExpression functionType = this.GetTypeExpressionFor(returnType, funcDeclarator);
        if (storageClass == Token.Typedef) {
          if (pointerToFunc == null) funcDeclarator.Specifiers = specifiers;
          var typedefDecl = new TypedefDeclaration(functionType, funcDeclarator.Identifier, slb);
          this.InitializeLocallyDefinedNamesFromParameters(funcDeclarator.Parameters);
          this.ParseFunctionOrBlockContract(funcDeclarator.Contract, followers);
          RegisterTypedef(funcDeclarator.Identifier.Name.Value, typedefDecl); //TODO: const and volatile;
          this.AssociateContracts(functionType, funcDeclarator);
          typeMembers.Add(typedefDecl);
        } else {
          //^ assert pointerToFunc != null;
          // Distinguish between whether this function pointer is inside a type definition
          if (isGlobal) {
            GlobalVariableDeclaration globalVarDecl =
               new GlobalVariableDeclaration(0, visibility, functionType, pointerToFunc.Identifier, null, slb);
            typeMembers.Add(globalVarDecl);
          } else {
            FieldDeclaration field = new FieldDeclaration(null, FieldDeclaration.Flags.Unsafe, visibility, functionType, pointerToFunc.Identifier, null, slb);
            typeMembers.Add(field);
          }
        }
        this.locallyDefinedNames.Clear();
        return;
      }
      bool acceptsExtraArguments;
      List<ParameterDeclaration> parameters = this.ConvertToParameterDeclarations(funcDeclarator.Parameters, out acceptsExtraArguments);
      List<GenericMethodParameterDeclaration>/*?*/ templateParameters = Parser.ConvertToGenericMethodParameterDeclarations(funcDeclarator.TemplateParameters);
      CallingConvention callingConvention = GetCallingConvention(specifiers, acceptsExtraArguments);

      FunctionDeclaration fdecl = new FunctionDeclaration(acceptsExtraArguments,
          specifiers,
          storageClass == Token.Extern,
          callingConvention,
          visibility,
          returnType,
          funcDeclarator.Identifier,
          templateParameters,
          parameters,
          this.InSpecCode,
          null,
          slb);
      this.AssociateContracts(fdecl, funcDeclarator);
      typeMembers.Add(fdecl);
      this.locallyDefinedNames.Clear();

      var prefixMacro = "\\macro_";
      var prefixResMacro = "\\result_macro_";
      var prefixCastLike = "\\castlike_";
      var prefixCastLikeVa = "\\castlike_va_";
      var nameString = funcDeclarator.FunctionName.Identifier.Name.Value;
      if (nameString.StartsWith(prefixMacro)) {
        this.functionContractExtensions[nameString.Substring(prefixMacro.Length)] = nameString;
      } else if (nameString.StartsWith(prefixResMacro)) {
        this.functionContractExtensions[nameString.Substring(prefixResMacro.Length)] = nameString;
      } else if (nameString.StartsWith(prefixCastLikeVa)) {
        this.castlikeFunctions[nameString.Substring(prefixCastLikeVa.Length)] = nameString;
      } else if (nameString.StartsWith(prefixCastLike)) {
        this.castlikeFunctions[nameString.Substring(prefixCastLike.Length)] = nameString;
      } else if (nameString.StartsWith("\\") && IsVoid(returnType)) {
        this.statementLikeFunctions[nameString.Substring(1)] = nameString;
      }
    }

    protected void RegisterTypedef(string typedefName, TypedefDeclaration typedefDecl) {
      // this potentiall overwrites previous typedefs - we will check later if these were compatile
      this.typedefs[typedefName] = typedefDecl;
    }  

    protected List<ParameterDeclaration> ConvertToParameterDeclarations(List<Parameter> parameters, out bool acceptsExtraArguments) {
      acceptsExtraArguments = false;
      List<ParameterDeclaration> result = new List<ParameterDeclaration>(parameters.Count);
      ushort i = 0;
      for (int j = 0, n = parameters.Count; j < n; j++) {
        Parameter p = parameters[j];
        if (p.IsVarArgs) {
          if (j != n - 1) {
            // TODO: issue an error, varargs must be the last parameter; should already be caught during parsing
          }
          acceptsExtraArguments = true;
          break; 
        }
        Declarator name = p.Name;
        ArrayDeclarator/*?*/ array = name as ArrayDeclarator;
        if (array != null && array.ArraySize != null && !(array.ArraySize is TypeExpression)) {
          name = new ArrayDeclarator(array.ElementType, null, array.SourceLocation);
          //TODO: add a precondition requiring the array to be of at least array.ArraySize in length
        }
        TypeExpression type = this.GetTypeExpressionFor(p.TypeSpecifiers, name, FixedSizeArrayContext.AsParameter);
        ParameterDeclaration pdecl = new VccParameterDeclaration(type, name.Identifier, p.TypeSpecifiers, i++, p.IsOut, p.IsSpec, p.SourceLocation);
        result.Add(pdecl);
      }
      return result;
    }

    protected static List<GenericMethodParameterDeclaration>/*?*/ ConvertToGenericMethodParameterDeclarations(List<TemplateParameterDeclarator>/*?*/ parameters) {
      if (parameters == null || parameters.Count == 0) return null;
      List<GenericMethodParameterDeclaration> result = new List<GenericMethodParameterDeclaration>(parameters.Count);
      List<TypeExpression> contraints = new List<TypeExpression>(0);
      ushort index = 0;
      foreach (TemplateParameterDeclarator tp in parameters) {
        GenericMethodParameterDeclaration gmpd = new GenericMethodParameterDeclaration(null, tp.Identifier, index++, contraints, TypeParameterVariance.NonVariant, false, false, false, tp.SourceLocation);
        result.Add(gmpd);
      }
      return result;
    }

    protected void ParseFunctionDefinition(List<Specifier> specifiers, List<ITypeDeclarationMember> typeMembers,
      Declarator declarator, FunctionDeclarator funcDeclarator, TokenSet followers)
      //^ requires this.currentToken == Token.LeftBrace;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(funcDeclarator.SourceLocation);
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[0].SourceLocation);
      //InitializeLocallyDefinedNamesFromParameters(funcDeclarator.Parameters);

      this.currentLexicalScope = new LexicalScope(this.currentLexicalScope, slb);
      BlockStatement body = this.ParseBody(followers | Token.Semicolon);
      this.currentLexicalScope = this.currentLexicalScope.ParentScope;

      slb.UpdateToSpan(body.SourceLocation);
      Token storageClass = GetStorageClassToken(specifiers);
      TypeMemberVisibility visibility = storageClass == Token.Static ? TypeMemberVisibility.Assembly : TypeMemberVisibility.Public;
      TypeExpression returnType;
      returnType = this.GetTypeExpressionFor(specifiers, funcDeclarator.FunctionName); //TODO: complain if function pointer type has a body
      if (declarator != funcDeclarator)
        returnType = this.ApplyDeclarator(declarator, returnType);
      bool acceptsExtraArguments;
      List<ParameterDeclaration> parameters = this.ConvertToParameterDeclarations(funcDeclarator.Parameters, out acceptsExtraArguments);
      List<GenericMethodParameterDeclaration>/*?*/ templateParameters = Parser.ConvertToGenericMethodParameterDeclarations(funcDeclarator.TemplateParameters);
      CallingConvention callingConvention = GetCallingConvention(specifiers, acceptsExtraArguments);
      if (returnType is VccFunctionTypeExpression)
        returnType = new VccPointerTypeExpression(returnType, null, returnType.SourceLocation);
      MethodDeclaration.Flags flags = 0;
      if (acceptsExtraArguments) flags |= MethodDeclaration.Flags.AcceptsExtraArguments;
      FunctionDefinition func = new FunctionDefinition(flags, specifiers, callingConvention, visibility, returnType, funcDeclarator.Identifier, templateParameters, parameters, body, this.InSpecCode, null, slb);
      typeMembers.Add(func);
      this.AssociateContracts(func, funcDeclarator);
      //TODO: complain if statements != null;
      if (this.currentToken == Token.Semicolon) this.GetNextToken();
      this.locallyDefinedNames.Clear();
      this.SkipTo(followers);
    }

    protected void InitializeLocallyDefinedNamesFromParameters(IEnumerable<Parameter> parameters) {
      if (parameters != null)
        foreach (var p in parameters)
          this.locallyDefinedNames[p.Name.Identifier.Name.Value] = true;
    }

    protected void InitializeLocallyDefinedNamesFromParameters(IEnumerable<TemplateParameterDeclarator> parameters) {
      if (parameters != null)
        foreach (var p in parameters)
          this.locallyDefinedNames[p.Identifier.Name.Value] = false;
    }
    protected TypeExpression ApplyDeclarator(Declarator declarator, TypeExpression returnType) {
      PointerDeclarator/*?*/ pointerDeclarator = declarator as PointerDeclarator;
      FunctionDeclarator/*?*/ funcDeclarator = declarator as FunctionDeclarator;
      ArrayDeclarator/*?*/ arrayDeclarator = declarator as ArrayDeclarator;
      while (funcDeclarator == null && (pointerDeclarator != null || arrayDeclarator != null)) {
        if (pointerDeclarator != null) {
          funcDeclarator = pointerDeclarator.Declarator as FunctionDeclarator;
          arrayDeclarator = pointerDeclarator.Declarator as ArrayDeclarator;
          if (funcDeclarator != null)
            pointerDeclarator.Declarator = new IdentifierDeclarator(funcDeclarator.FunctionName.Identifier);
          pointerDeclarator = null;
        } else if (arrayDeclarator != null) {
          funcDeclarator = arrayDeclarator.ElementType as FunctionDeclarator;
          pointerDeclarator = arrayDeclarator.ElementType as PointerDeclarator;
          if (funcDeclarator != null)
            arrayDeclarator.ElementType = new IdentifierDeclarator(funcDeclarator.FunctionName.Identifier);
          arrayDeclarator = null;
        }
      }
      return this.GetTypeExpressionFor(returnType, declarator);
    }

    protected void AssociateContracts(object func, FunctionDeclarator funcDeclarator) {
      if (!funcDeclarator.HasContract) return;
      this.compilation.ContractProvider.AssociateMethodWithContract(func, funcDeclarator.Contract.ToMethodContract());
    }

    private bool IsArrayDeclarator(Declarator declarator)
    {
      if (declarator is ArrayDeclarator) return true;
      var id = declarator as InitializedDeclarator;
      if (id != null) return IsArrayDeclarator(id.Declarator);
      return false;
    }

    protected bool IsPointerDeclarator(Declarator declarator, out List<TypeQualifier> qualifiers) {
      var pd = declarator as PointerDeclarator;
      if (pd != null) {
        qualifiers = pd.Qualifiers;
        return true;
      }
      var id = declarator as InitializedDeclarator;
      if (id != null) return this.IsPointerDeclarator(id.Declarator, out qualifiers);
      qualifiers = null;
      var ad = declarator as ArrayDeclarator;
      if (ad != null) return ad.ArraySize == null;
      return false;
    }

    protected void AddDeclarationStatement(List<Specifier> specifiers, Declarator declarator, List<Statement> statements) {
      SourceLocationBuilder slb = new SourceLocationBuilder(declarator.SourceLocation);
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[0].SourceLocation);
      TypeExpression localType = this.GetTypeExpressionFor(specifiers, declarator, FixedSizeArrayContext.AsLocal);
      List<TypeQualifier> pointerDeclaratorQualifiers;
      FieldDeclaration.Flags constOrVolatile = 
        this.IsPointerDeclarator(declarator, out pointerDeclaratorQualifiers) 
        ? LookForConstAndVolatile(pointerDeclaratorQualifiers) 
        : LookForConstAndVolatile(specifiers);
      //Token sct = GetStorageClassToken(specifiers); //TODO: use a LocalDeclaration subclass that can record and interpret the storage class
      Expression/*?*/ initializer = null;
      InitializedDeclarator/*?*/ initializedDeclarator = declarator as InitializedDeclarator;
      if (initializedDeclarator != null) {
        initializer = initializedDeclarator.InitialValue;
        var arrayOrStructureInitializer = initializer as VccInitializerBase;
        if (arrayOrStructureInitializer != null) {
          arrayOrStructureInitializer.arrayTypeExpression = localType as VccArrayTypeExpression;
          arrayOrStructureInitializer.structureTypeExpression = localType as VccNamedTypeExpression;
        }
      }
      List<LocalDeclaration> declarations = new List<LocalDeclaration>(1);
      // if we have local function declaration, we create a global mangled function declaration
      VccFunctionTypeExpression/*?*/ cFuncTypeExp = localType as VccFunctionTypeExpression;
      if (cFuncTypeExp != null) {
        Token storageClass = GetStorageClassToken(specifiers); 
        TypeMemberVisibility visibility = storageClass == Token.Static ? TypeMemberVisibility.Assembly : TypeMemberVisibility.Public;
               
        bool isExternal = storageClass == Token.Extern;
        List<ParameterDeclaration> parameters = new List<ParameterDeclaration>();
        foreach (ParameterDeclaration pd in cFuncTypeExp.parameters) {
          parameters.Add(pd);
        }
        // create a unique mangled function declaration at the top level
        FunctionDeclaration mangledFunc = 
          new FunctionDeclaration(cFuncTypeExp.AcceptsExtraArguments, specifiers, isExternal, 
            cFuncTypeExp.CallingConvention, visibility, cFuncTypeExp.ReturnType, 
            new VccNameDeclaration(this.GetNameFor(cFuncTypeExp.Name.Value + ".." + cFuncTypeExp.GetHashCode()), true, cFuncTypeExp.SourceLocation),
            null, parameters, this.InSpecCode, null, slb);
        
        this.currentTypeMembers.Add(mangledFunc);
        declarations.Add(new VccLocalFunctionDeclaration(declarator.Identifier, initializer, specifiers, this.InSpecCode, slb, mangledFunc));
      } else {
        declarations.Add(new VccLocalDeclaration(declarator.Identifier, initializer, specifiers, this.InSpecCode, slb));
      }

      //TODO: There may also be constant pointers - this would need to be dealt with differently
      if (TypeExpressionHasPointerType(localType) != null)
        constOrVolatile &= ~FieldDeclaration.Flags.ReadOnly;

      // stack allocated arrays are readonly, so that they cannot be used as lvalues
      if (localType is VccArrayTypeExpression)
        constOrVolatile |= FieldDeclaration.Flags.ReadOnly;

      statements.Add(new LocalDeclarationsStatement((constOrVolatile & FieldDeclaration.Flags.ReadOnly) != 0, false, false, localType, declarations, slb));
    }

    protected void AddTypeDeclarationMember(List<Specifier> specifiers, Declarator declarator, List<ITypeDeclarationMember> typeMembers, bool isGlobal = false) {
      SourceLocationBuilder slb = new SourceLocationBuilder(declarator.SourceLocation);
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[0].SourceLocation);
      TypeExpression memberType = this.GetTypeExpressionFor(specifiers, declarator, FixedSizeArrayContext.AsField);
      List<TypeQualifier> pointerDeclaratorQualifiers;
      FieldDeclaration.Flags flags = 
        this.IsPointerDeclarator(declarator, out pointerDeclaratorQualifiers) 
        ? LookForConstAndVolatile(pointerDeclaratorQualifiers)
        : LookForConstAndVolatile(specifiers);

      if (isGlobal 
        && IsArrayDeclarator(declarator) 
        && specifiers.Exists(s => s is TypeQualifier && ((TypeQualifier)s).Token == Token.Const)) flags |= FieldDeclaration.Flags.ReadOnly;

      // C's const will be treated as readonly. When we are inside a type, isConst is never true because you 
      // cannot initialize it.
      Token sct = GetStorageClassToken(specifiers);
      if (sct == Token.Typedef) {
        var typedefDecl = new TypedefDeclaration(memberType, declarator.Identifier, specifiers, slb);
        this.RegisterTypedef(declarator.Identifier.Value, typedefDecl);
        typeMembers.Add(typedefDecl);
      } else if (this.InSpecCode || IsAxiom(specifiers)) {
        Expression/*?*/ initializer = null;
        InitializedDeclarator/*?*/ initializedDeclarator = declarator as InitializedDeclarator;
        if (initializedDeclarator != null) initializer = initializedDeclarator.InitialValue;
        if (this.currentTypeName != null) {
          FieldDefinition specField = new FieldDefinition(specifiers, flags, memberType, declarator.Identifier, initializer, this.InSpecCode, slb);
          if (this.currentSpecificationFields == null) this.currentSpecificationFields = new List<FieldDeclaration>();
          this.currentSpecificationFields.Add(specField);
        } else {
          if (initializer != null && IsAxiom(specifiers)) {
            this.AddTypeInvariantToCurrent(new TypeInvariant(declarator.Identifier, new CheckedExpression(initializer, initializer.SourceLocation), true, slb));
          } else if (initializer != null && IsLogic(specifiers) && initializedDeclarator.Declarator is FunctionDeclarator) {
            FunctionDeclarator funcDeclarator = initializedDeclarator.Declarator as FunctionDeclarator;
            bool acceptsExtraArguments;
            List<ParameterDeclaration> parameters = this.ConvertToParameterDeclarations(funcDeclarator.Parameters, out acceptsExtraArguments);
            List<GenericMethodParameterDeclaration>/*?*/ templateParameters = Parser.ConvertToGenericMethodParameterDeclarations(funcDeclarator.TemplateParameters);
            TypeExpression returnType = this.GetTypeExpressionFor(specifiers, funcDeclarator.FunctionName);
            FunctionDeclaration fdecl = new FunctionDeclaration(false, specifiers, false, CallingConvention.C, TypeMemberVisibility.Public, 
              returnType, funcDeclarator.Identifier, templateParameters, parameters, true, initializer, slb);
            typeMembers.Add(fdecl);
          } else {
            if (this.currentSpecificationFields == null) this.currentSpecificationFields = new List<FieldDeclaration>();
            FieldDeclaration glob = new GlobalVariableDeclaration(flags, TypeMemberVisibility.Public, memberType, declarator.Identifier, initializer, slb);
            this.currentSpecificationFields.Add(glob);
            if (declarator.Identifier.Name.Value.StartsWith("\\declspec_")) {
              this.declspecExtensions.Add(declarator.Identifier.Name.Value.Substring(10), 
                initializer == null ? String.Empty : (string)initializer.Value);
            }

          }
        }
      } else {
        //TODO: complain if sct is Auto or Register.
        //TODO: complain if memberType is function
        Expression/*?*/ initializer = null;
        InitializedDeclarator/*?*/ initializedDeclarator = declarator as InitializedDeclarator;
        if (initializedDeclarator != null)
          initializer = initializedDeclarator.InitialValue;
        else if (sct == Token.Extern || sct == Token.Static) {
          TypeMemberVisibility visibility = sct == Token.Static ? TypeMemberVisibility.Assembly : TypeMemberVisibility.Public;
          typeMembers.Add(new GlobalVariableDeclaration(flags, visibility, memberType, declarator.Identifier, null, slb));
          return;
        }
        if (this.currentTypeName != null) {
          if (sct == Token.Static) flags |= FieldDeclaration.Flags.Static;
          AnonymousFieldDeclarator/*?*/ anonymousFieldDeclarator = declarator as AnonymousFieldDeclarator;
          if (anonymousFieldDeclarator != null) {
            typeMembers.Add(new AnonymousFieldDefinition(flags, memberType, anonymousFieldDeclarator));
          } else {
            BitfieldDeclarator/*?*/ bitFieldDeclarator = declarator as BitfieldDeclarator;
            if (bitFieldDeclarator != null)
              typeMembers.Add(new BitFieldDefinition(specifiers, bitFieldDeclarator.FieldSize, flags, memberType, declarator.Identifier, initializer, slb));
            else
              typeMembers.Add(new FieldDefinition(specifiers, flags, memberType, declarator.Identifier, initializer, this.InSpecCode, slb));
          }
        } else {
          flags |= FieldDeclaration.Flags.Static; //global fields are always static
          //at the global level, the static modifier means visible only inside the current compilation unit (file)
          TypeMemberVisibility visibility = sct == Token.Static ? TypeMemberVisibility.Assembly : TypeMemberVisibility.Public;
          typeMembers.Add(new GlobalVariableDeclaration(flags, visibility, memberType, declarator.Identifier, initializer, slb));
        }
      }
    }

    protected static CallingConvention GetCallingConvention(List<Specifier>/*?*/ specifiers, bool acceptsExtraArguments) {
      if (acceptsExtraArguments) return CallingConvention.ExtraArguments;
      if (specifiers != null) {
        foreach (Specifier specifier in specifiers) {
          FunctionSpecifier/*?*/ fs = specifier as FunctionSpecifier;
          if (fs != null) {
            switch (fs.Token) {
              case Token.Cdecl: return CallingConvention.C;
              case Token.Stdcall: return CallingConvention.Standard;
              case Token.Fastcall: return CallingConvention.FastCall;
            }
          }
        }
      }
      return CallingConvention.Default;
    }

    protected static Token GetStorageClassToken(List<Specifier> specifiers) {
      Token result = Token.None;
      foreach (Specifier specifier in specifiers) {
        StorageClassSpecifier/*?*/ scs = specifier as StorageClassSpecifier;
        if (scs != null) {
          //TODO: give error if result != Token.None;
          result = scs.Token;
        }
      }
      return result;
    }

    protected static TypedefNameSpecifier/*?*/ GetTypedefNameSpecifier(List<Specifier> specifiers) {
      TypedefNameSpecifier/*?*/ result = null;
      foreach (Specifier specifier in specifiers) {
        result = specifier as TypedefNameSpecifier;
        if (result != null) return result;
      }
      return result;
    }

    protected static bool IsAxiom(List<Specifier> specifiers) {
      foreach (Specifier specifier in specifiers) {
        PrimitiveTypeSpecifier/*?*/ pts = specifier as PrimitiveTypeSpecifier;
        if (pts != null && pts.Token == Token.Axiom) return true;
      }
      return false;
    }

    protected static bool IsLogic(List<Specifier> specifiers) {
      foreach (Specifier specifier in specifiers) {
        SpecDeclspecSpecifier/*?*/ sts = specifier as SpecDeclspecSpecifier;
        if (sts != null && sts.Token == "spec_macro") return true;
      }
      return false;
    }

    protected static bool IsInline(List<Specifier> specifiers) {
      foreach (Specifier specifier in specifiers) {
        FunctionSpecifier/*?*/ fs = specifier as FunctionSpecifier;
        if (fs != null && fs.Token == Token.Inline) return true;
      }
      return false;
    }

    private TypeExpression HandleTypeQualifiersForPointer(IEnumerable<Specifier> specifiers, TypeExpression type, Declarator declarator)
    {
      List<TypeQualifier> fldQualifiers;
      if (this.IsPointerDeclarator(declarator, out fldQualifiers)) {
        var ptrQualifiers =
          new List<TypeQualifier>(specifiers.Where(s => s is TypeQualifier).Select(s => s as TypeQualifier));
        if (ptrQualifiers.Count > 0) {
          type = new VccQualifiedTypeExpression(type, ptrQualifiers, type.SourceLocation);
        }
      }

      return type;
    }

    /// <summary>
    /// For a local variable of pointer type, see if it is const or volatile. 
    /// If volatile appears in the specifiers, then it is volatile;
    /// If const appears after the last type specifier (primitive, structured, or typedef), 
    /// then the local pointer is "constant".
    /// TODO: to fully support the const specifier, we need a more expressive type system in the framework. 
    /// </summary>
    /// <param name="specifiers"></param>
    protected FieldDeclaration.Flags LookForConstAndVolatileForLocalPointer(List<Specifier> specifiers) {
      FieldDeclaration.Flags result = 0;
      foreach (Specifier specifier in specifiers) {
        if (specifier is CompositeTypeSpecifier || specifier is PrimitiveTypeSpecifier ||
          specifier is FunctionSpecifier || specifier is TypedefNameSpecifier) {
          result &= ~FieldDeclaration.Flags.ReadOnly;
          continue;
        }
        TypeQualifier/*?*/ tqual = specifier as TypeQualifier;
        if (tqual == null) continue;
        if (tqual.Token == Token.Const) result |= FieldDeclaration.Flags.ReadOnly;
        else if (tqual.Token == Token.Volatile) result |= FieldDeclaration.Flags.Volatile;
      }
      return result;
    }

    protected FieldDeclaration.Flags LookForConstAndVolatile(IEnumerable<Specifier> specifiers) {
      FieldDeclaration.Flags result = 0;
      if (specifiers == null) return result;
      foreach (Specifier specifier in specifiers) {
        TypeQualifier/*?*/ tqual = specifier as TypeQualifier;
        if (tqual != null) {
          if (tqual.Token == Token.Const) result |= FieldDeclaration.Flags.ReadOnly;
          else if (tqual.Token == Token.Volatile) result |= FieldDeclaration.Flags.Volatile;
          continue;
        }
        TypedefNameSpecifier tdn = specifier as TypedefNameSpecifier;
        if (tdn != null) {
          TypedefDeclaration  typedefDecl;
          if (this.typedefs.TryGetValue(tdn.TypedefName.Name.Value, out typedefDecl)) {
            if (typedefDecl.IsConst) result |= FieldDeclaration.Flags.ReadOnly;
            if (typedefDecl.IsVolatile) result |= FieldDeclaration.Flags.Volatile;
          }
        }
      }
      return result;
    }

    protected TypeExpression GetTypeExpressionFor(IEnumerable<Specifier> specifiers, Declarator declarator, FixedSizeArrayContext fsaCtx = FixedSizeArrayContext.AsField, Expression/*?*/ initializer = null)
    {
      InitializedDeclarator /*?*/ initialized = declarator as InitializedDeclarator;
      if (initialized != null)
        return this.GetTypeExpressionFor(specifiers, initialized.Declarator, fsaCtx, initialized.InitialValue);
      else
      {
        var elementType = this.GetTypeExpressionFor(specifiers, declarator is IdentifierDeclarator ? (declarator as IdentifierDeclarator).SourceLocation : null);
        elementType = HandleTypeQualifiersForPointer(specifiers, elementType, declarator);
        return this.GetTypeExpressionFor(elementType, declarator, fsaCtx, initializer);
      }
    }

    protected TypeExpression GetTypeExpressionFor(TypeExpression elementType, Declarator declarator, FixedSizeArrayContext fsaCtx = FixedSizeArrayContext.AsField, Expression/*?*/ initializer = null)
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(elementType.SourceLocation);
      ArrayDeclarator/*?*/ array = declarator as ArrayDeclarator;
      if (array != null) {
        slb.UpdateToSpan(array.SourceLocation);
        Declarator nestedDeclarator = array.ElementType;
        PointerDeclarator/*?*/ pointerDeclarator = nestedDeclarator as PointerDeclarator;
        if (pointerDeclarator != null) nestedDeclarator = pointerDeclarator.Declarator;
        Expression/*?*/ arraySize = array.ArraySize;
        if (arraySize == null) {
          var vcInitializer = initializer as VccInitializerBase;
          if (vcInitializer != null) {
            arraySize = new CompileTimeConstant(vcInitializer.ExpressionCount, array.SourceLocation);
          }
        }
        if (arraySize is TypeExpression) {
          elementType = new VccMapTypeExpressions((TypeExpression)arraySize, elementType, this.nameTable, slb);
        } else if (fsaCtx == FixedSizeArrayContext.AsParameter || (fsaCtx == FixedSizeArrayContext.AsLocal && arraySize == null)) {
          // for parameters, arrays are simply treated as pointers
          elementType = new VccPointerTypeExpression(elementType, null, slb);
        } else {
          elementType = new VccArrayTypeExpression(elementType, arraySize, slb);
        }
        TypeExpression result = this.GetTypeExpressionFor(elementType, nestedDeclarator);
        result = AddIndirectionsToType(result, pointerDeclarator, slb);
        return result;
      }
      FunctionDeclarator/*?*/ function = declarator as FunctionDeclarator;
      if (function != null) {
        slb.UpdateToSpan(declarator.SourceLocation);
        Declarator nestedDeclarator = function.FunctionName;
        PointerDeclarator/*?*/ pointerDeclarator = nestedDeclarator as PointerDeclarator;
        if (pointerDeclarator != null) nestedDeclarator = pointerDeclarator.Declarator;
        ArrayDeclarator/*?*/ arrayDeclarator = nestedDeclarator as ArrayDeclarator;
        if (arrayDeclarator != null) nestedDeclarator = arrayDeclarator.ElementType;
        TypeExpression returnType = this.GetTypeExpressionFor(elementType, nestedDeclarator);
        bool acceptsExtraArguments;
        List<ParameterDeclaration> parameters = this.ConvertToParameterDeclarations(function.Parameters, out acceptsExtraArguments);
        CallingConvention callingConvention = GetCallingConvention(function.Specifiers, acceptsExtraArguments);
        TypeExpression result = new VccFunctionTypeExpression(acceptsExtraArguments, callingConvention, returnType, 
          function.FunctionName.Identifier, parameters, function, slb);
        result = AddIndirectionsToType(result, pointerDeclarator, slb);
        if (arrayDeclarator != null) {
          SourceLocationBuilder aslb = new SourceLocationBuilder(arrayDeclarator.SourceLocation);
          aslb.UpdateToSpan(slb);
          result = new VccArrayTypeExpression(result, arrayDeclarator.ArraySize, aslb);
        }
        return result;
      }

      PointerDeclarator/*?*/ pointer = declarator as PointerDeclarator;
      if (pointer != null)
      {
        elementType = AddIndirectionsToType(elementType, pointer, slb);
        return this.GetTypeExpressionFor(elementType, pointer.Declarator, fsaCtx, initializer);        
      }

      return elementType;
    }

    protected static TypeExpression AddIndirectionsToType(TypeExpression type, PointerDeclarator pointerDeclarator, SourceLocationBuilder slb) {
      TypeExpression result = type;
      if (pointerDeclarator != null) {
        foreach (Pointer p in pointerDeclarator.Pointers) {
          SourceLocationBuilder pslb = new SourceLocationBuilder(p.SourceLocation);
          pslb.UpdateToSpan(slb);
          if (result is VccQualifiedTypeExpression) {
            var qte = result as VccQualifiedTypeExpression;
            var qualifiers = new List<TypeQualifier>();
            if (p.Qualifiers != null) qualifiers.AddRange(p.Qualifiers);
            if (qte.Qualifiers != null) qualifiers.AddRange(qte.Qualifiers);
            result = new VccPointerTypeExpression(result, qualifiers, pslb);
          } else {
            result = new VccPointerTypeExpression(result, p.Qualifiers, pslb);
          }
        }
      }
      return result;
    }

    protected TypeExpression GetTypeExpressionFor(IEnumerable<Specifier> specifiers, ISourceLocation declaratorLocationForErrorReporting) {
      TypeExpression/*?*/ result = this.TryToGetTypeExpressionFor(specifiers);
      if (result != null) return result;

      ISourceLocation /*?*/ errorLocation = declaratorLocationForErrorReporting;
      if (errorLocation == null) {
        foreach (Specifier specifier in specifiers)
        {
          errorLocation = specifier.SourceLocation;
          if (errorLocation != null) break;
        }
      }

      if (errorLocation != null)
        this.HandleError(errorLocation, Error.UnexpectedToken, errorLocation.Source);
      return TypeExpression.For(Dummy.Type);
    }

    protected TypeExpression/*?*/ TryToGetTypeExpressionFor(IEnumerable<Specifier> specifiers) {
      TypeExpression/*?*/ result = null;
      PrimitiveTypeSpecifier/*?*/ sign = null;
      PrimitiveTypeSpecifier/*?*/ length = null;
      PrimitiveTypeSpecifier/*?*/ primitiveType = null;
      List<TypeQualifier> typeQualifiers = null;
      foreach (Specifier specifier in specifiers) {
        CompositeTypeSpecifier/*?*/ cts = specifier as CompositeTypeSpecifier;
        if (cts != null) {
          //TODO: if (result != null || sign != null || length != null || primitiveType != null) Error;
          result = cts.TypeExpression;
          continue;
        }
        TypeQualifier/*?*/ tq = specifier as TypeQualifier;
        if (tq != null) {
          if (result != null) {
            TypeExpression /*?*/ elementType = this.TypeExpressionHasPointerType(result);
            if (elementType != null) {
              if (typeQualifiers == null) {
                typeQualifiers = new List<TypeQualifier>(2);
                result = new VccPointerTypeExpression(elementType, typeQualifiers, result.SourceLocation);
              }
              typeQualifiers.Add(tq);
            }
          } 
          continue;
        }
        TypedefNameSpecifier/*?*/ tdns = specifier as TypedefNameSpecifier;
        if (tdns != null) {
          if (this.TryToGetBuiltInSpecTypeName(tdns, out result)) {
            // found - result is set as a side effect of the function call
          } else {
            TypedefDeclaration typedefDecl;
            if (this.typedefs.TryGetValue(tdns.TypedefName.ToString(), out typedefDecl)) {
              if (IsVoid(typedefDecl.Type)) {
                primitiveType = new PrimitiveTypeSpecifier(Token.Void, tdns.SourceLocation);
                continue;
              }
            }
            result = new VccNamedTypeExpression(tdns.TypedefName, false);
            break; // further specifiers belong to the field, not the type
          }
          continue;
        }
        ScopedTypeNameSpecifier/*?*/ stns = specifier as ScopedTypeNameSpecifier;
        if (stns != null) {
          result = new VccScopedTypeExpression(stns.ScopedName);
          continue;
        }
        PrimitiveTypeSpecifier/*?*/ pts = specifier as PrimitiveTypeSpecifier;
        if (pts != null) {
          switch (pts.Token) {
            case Token.Signed:
            case Token.Unsigned:
              //TODO: error if sign != null || result != null;
              sign = pts;
              break;
            case Token.W64:
              length = pts;
              break;
            case Token.Short:
              //TODO: error if length != null || result != null;;
              length = pts;
              break;
            case Token.Long:
              //TODO: error if result != null;
              if (length == null)
                length = pts;
              else {
                if (length.Token == Token.Long) {
                  SourceLocationBuilder slb = new SourceLocationBuilder(length.SourceLocation);
                  slb.UpdateToSpan(pts.SourceLocation);
                  length = new PrimitiveTypeSpecifier(Token.Int64, slb);
                } else {
                  //TODO: error
                }
              }
              break;
            case Token.Axiom:
            case Token.Char:
            case Token.Int:
            case Token.Float:
            case Token.Double:
            case Token.Void:
            case Token.Bool:
            case Token.Int8:
            case Token.Int16:
            case Token.Int32:
            case Token.Int64:
              //TODO: error is primitiveType != null || result != null;
              primitiveType = pts;
              break;
            default:
              //^ assert false;
              break;
          }
        }
      }
      if (result != null) return result;
      if (primitiveType != null) {
        SourceLocationBuilder slb = new SourceLocationBuilder(primitiveType.SourceLocation);
        if (length != null) {
          slb.UpdateToSpan(length.SourceLocation);

          if (length.Token == Token.Short) {
            //TODO: error if primitive type != int
          } else {
            //TODO: error if primitive type != int and != double and != float;
            //only warn if primitive type is float
          }
        }
        if (sign != null) slb.UpdateToSpan(sign.SourceLocation);
        if (sign == null || sign.Token == Token.Signed) {
          switch (primitiveType.Token) {
            case Token.Char:
              return this.GetTypeExpressionFor(TypeCode.SByte, slb);
            case Token.Float:
              //TODO: error if signed != null;
              if (length != null && length.Token == Token.Long) {
                //TODO: warning
                return this.GetTypeExpressionFor(TypeCode.Double, slb);
              } else
                return this.GetTypeExpressionFor(TypeCode.Single, slb);
            case Token.Double:
              //TODO: error if signed != null;
              return this.GetTypeExpressionFor(TypeCode.Double, slb);
            case Token.Void:
              //TODO: error if signed != null;
              return this.GetTypeExpressionFor(TypeCode.Empty, slb);
            case Token.Bool:
              //TODO: error if signed != null;
              return this.GetTypeExpressionFor(TypeCode.Boolean, slb);
            case Token.Int8:
              return this.GetTypeExpressionFor(TypeCode.SByte, slb);
            case Token.Int16:
              return this.GetTypeExpressionFor(TypeCode.Int16, slb);
            case Token.Int32:
              return this.GetTypeExpressionFor(TypeCode.Int32, slb);
            case Token.Int64:
              return this.GetTypeExpressionFor(TypeCode.Int64, slb);
          }
        } else {
          //unsigned
          switch (primitiveType.Token) {
            case Token.Char:
              return this.GetTypeExpressionFor(TypeCode.Byte, slb);
            case Token.Float:
              //TODO: error
              if (length != null && length.Token == Token.Long) {
                //TODO: warning
                return this.GetTypeExpressionFor(TypeCode.Double, slb);
              } else
                return this.GetTypeExpressionFor(TypeCode.Single, slb);
            case Token.Double:
              //TODO: error
              return this.GetTypeExpressionFor(TypeCode.Double, slb);
            case Token.Void:
              //TODO: error
              return this.GetTypeExpressionFor(TypeCode.Empty, slb);
            case Token.Bool:
              //TODO: error
              return this.GetTypeExpressionFor(TypeCode.Boolean, slb);
            case Token.Int8:
              return this.GetTypeExpressionFor(TypeCode.Byte, slb);
            case Token.Int16:
              return this.GetTypeExpressionFor(TypeCode.UInt16, slb);
            case Token.Int32:
              return this.GetTypeExpressionFor(TypeCode.UInt32, slb);
            case Token.Int64:
              return this.GetTypeExpressionFor(TypeCode.UInt64, slb);
          }
        }
      }
      //get here if primitive type is int or has not been specified

      Token effectiveLengthToken = Token.None;

      if (length != null) {
        effectiveLengthToken = length.Token;
        if (effectiveLengthToken == Token.W64) {
          effectiveLengthToken = this.compilation.HostEnvironment.PointerSize == 4 ? Token.Long : Token.Int64;
        }
      }

      if (sign != null) {
        if (sign.Token == Token.Unsigned) {
          if (length == null) return this.GetTypeExpressionFor(TypeCode.UInt32, sign.SourceLocation);
          SourceLocationBuilder slb = new SourceLocationBuilder(sign.SourceLocation);
          slb.UpdateToSpan(length.SourceLocation);
          if (primitiveType != null) slb.UpdateToSpan(primitiveType.SourceLocation);
          switch (effectiveLengthToken) {
            case Token.Short: return this.GetTypeExpressionFor(TypeCode.UInt16, slb);
            case Token.Long: return this.GetTypeExpressionFor(TypeCode.UInt32, slb);
            case Token.Int64: return this.GetTypeExpressionFor(TypeCode.UInt64, slb);
          }
        }else if (sign.Token == Token.Signed) {
          if (length == null) return this.GetTypeExpressionFor(TypeCode.Int32, sign.SourceLocation);
          SourceLocationBuilder slb = new SourceLocationBuilder(sign.SourceLocation);
          slb.UpdateToSpan(length.SourceLocation);
          if (primitiveType != null) slb.UpdateToSpan(primitiveType.SourceLocation);
          switch (effectiveLengthToken) {
            case Token.Short: return this.GetTypeExpressionFor(TypeCode.Int16, slb);
            case Token.Long: return this.GetTypeExpressionFor(TypeCode.Int32, slb);
            case Token.Int64: return this.GetTypeExpressionFor(TypeCode.Int64, slb);
          }
        }
      }
      if (length != null) {
        SourceLocationBuilder slb = new SourceLocationBuilder(length.SourceLocation);
        if (primitiveType != null) slb.UpdateToSpan(primitiveType.SourceLocation);
        switch (effectiveLengthToken) {
          case Token.Short: return this.GetTypeExpressionFor(TypeCode.Int16, slb);
          case Token.Long: return this.GetTypeExpressionFor(TypeCode.Int32, slb);
          case Token.Int64: return this.GetTypeExpressionFor(TypeCode.Int64, slb);
        }
      }
      if (primitiveType != null) {
        //^ assume primitiveType.Token == Token.Int;
        return this.GetTypeExpressionFor(TypeCode.Int32, primitiveType.SourceLocation);
      }
      return null;
    }

    private bool IsVoid(TypeExpression typeExpr) {
      NamedTypeExpression ntExpr = typeExpr as NamedTypeExpression;
      if (ntExpr == null) return false;
      QualifiedName qName = ntExpr.Expression as QualifiedName;
      return qName != null && qName.Qualifier is AliasQualifiedName && qName.SimpleName.Name == this.nameTable.Void;
    }

    protected Declarator ParseDeclarator(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      //^ ensures result is IdentifierDeclarator || result is BitfieldDeclarator || result is ArrayDeclarator || result is FunctionDeclarator ||
      //^   result is PointerDeclarator || result is AbstractMapDeclarator || result is InitializedDeclarator;
    {
      return this.ParseDeclarator(null, followers, false);
    }


    protected Declarator ParseDeclarator(List<TemplateParameterDeclarator> templateParameters, TokenSet followers, bool requireIdentifier)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      //^ ensures result is IdentifierDeclarator || result is BitfieldDeclarator || result is ArrayDeclarator || result is FunctionDeclarator ||
      //^   result is PointerDeclarator || result is AbstractMapDeclarator || result is InitializedDeclarator;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      List<TypeQualifier> fieldQualifiers;
      List<Pointer> pointers = this.ParsePointers(out fieldQualifiers);
      Declarator result;
      List<Specifier>/*?*/ specifiers = null;
      if (this.currentToken == Token.LeftParenthesis){
        this.GetNextToken();
        if (!TS.DeclarationStart[this.currentToken])
          specifiers = this.ParseSpecifiers(new List<INamespaceDeclarationMember>(), null, null, followers|TS.DeclaratorStartOrRightParenOrSemicolon);
        result = this.ParseDeclarator(templateParameters, followers | Token.RightParenthesis, requireIdentifier);
        this.Skip(Token.RightParenthesis);
      } else if (this.currentToken == Token.Colon) {
        result = this.ParseBitfieldDeclarator(null, followers|Token.LeftBracket|Token.LeftParenthesis);
      } else {
        result = new IdentifierDeclarator(this.ParseNameDeclaration(requireIdentifier));
        if (this.currentToken == Token.Colon)
          result = this.ParseBitfieldDeclarator(result, followers|Token.LeftBracket|Token.LeftParenthesis);
      }
      while (this.currentToken == Token.LeftBracket || this.currentToken == Token.LeftParenthesis) {
        if (this.currentToken == Token.LeftBracket)
          result = this.ParseArrayDeclarator(result, followers|Token.LeftBracket|Token.LeftParenthesis|Token.Assign);
        else
          result = this.ParseFunctionDeclarator(result, templateParameters, followers|Token.LeftParenthesis|Token.Assign);
      }
      if (pointers.Count > 0) {
        slb.UpdateToSpan(result.SourceLocation);
        result = new PointerDeclarator(pointers, result, fieldQualifiers, slb);
      }
      if (this.currentToken == Token.Assign)
        result = this.ParseInitializedDeclarator(result, followers);
      else if (specifiers != null && specifiers.Count > 0 && result is FunctionDeclarator)
        ((FunctionDeclarator)result).Specifiers = specifiers;
      else
        this.SkipTo(followers);
      return result;
    }

    protected Declarator ParseDeclaratorInQuantifier(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      //^ ensures result is IdentifierDeclarator || result is PointerDeclarator;
{
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      List<TypeQualifier> fieldQualifiers;
      List<Pointer> pointers = this.ParsePointers(out fieldQualifiers);
      Declarator result = new IdentifierDeclarator(this.ParseNameDeclaration(true));
      if (pointers.Count > 0) {
        slb.UpdateToSpan(result.SourceLocation);
        result = new PointerDeclarator(pointers, result, fieldQualifiers, slb);
      }
      this.SkipTo(followers);
      return result;
    }

    protected List<TemplateParameterDeclarator>/*?*/ ParseTemplateParameters(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (this.currentToken != Token.Template) return null;
      this.GetNextToken();
      this.Skip(Token.LessThan);
      List<TemplateParameterDeclarator> result = new List<TemplateParameterDeclarator>();
      while (true) {
        SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
        this.Skip(Token.Typename);
        NameDeclaration parName = this.ParseNameDeclaration(false);
        slb.UpdateToSpan(parName.SourceLocation);
        result.Add(new TemplateParameterDeclarator(parName, slb));
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      result.TrimExcess();
      this.SkipOverTo(Token.GreaterThan, followers);
      return result;
    }

    protected Declarator ParseInitializedDeclarator(Declarator declarator, TokenSet followers)       
      //^ requires this.currentToken == Token.Assign;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(declarator.SourceLocation);
      this.GetNextToken();
      Expression initialValue = this.ParseInitializer(followers);
      Declarator result;
      result = new InitializedDeclarator(declarator, initialValue, slb);
      slb.UpdateToSpan(initialValue.SourceLocation);
      this.SkipTo(followers);
      return result;
    }

    protected VccDesignatorExpressionPair ParseDesignatorExpressionPair(TokenSet followers) {
      TokenSet followersOrAssignOrDot = followers | Token.Assign | Token.Dot;
      List<SimpleName> designators = new List<SimpleName>();
      while (this.currentToken == Token.Dot) {
        this.Skip(Token.Dot);
        designators.Add(this.ParseSimpleName(followersOrAssignOrDot));
      }
      designators.TrimExcess();
      this.Skip(Token.Assign);
      Expression expr = this.ParseExpression(false, true, followers);
      return new VccDesignatorExpressionPair(designators, expr);
    }

    protected Expression ParseInitializerWithDesignators(TokenSet followers, SourceLocationBuilder slb)
      //^ requires this.currentToken == Token.Dot
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {

      List<VccDesignatorExpressionPair> pairs = new List<VccDesignatorExpressionPair>();
      TokenSet followersOrCommaOrRightBrace = followers|Token.Comma|Token.RightBrace;
      pairs.Add(this.ParseDesignatorExpressionPair(followersOrCommaOrRightBrace));
      while (this.currentToken == Token.Comma) {
        this.GetNextToken();
        pairs.Add(this.ParseDesignatorExpressionPair(followersOrCommaOrRightBrace));
      }
      
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      var result = new VccInitializerWithDesignators(pairs, slb);
      this.SkipOverTo(Token.RightBrace, followers);
      return result;
    }

    protected Expression ParseInitializer(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (this.currentToken != Token.LeftBrace) return this.ParseExpression(followers);
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      if (this.currentToken == Token.Dot) return ParseInitializerWithDesignators(followers, slb);

      if (this.currentToken == Token.Colon) {
        var res = this.ParseBraceLabeledExpression(slb, followers);
        if (res != null)
          return res;
      }

      TokenSet followersOrCommaOrRightBrace = followers | Token.Comma | Token.RightBrace;
      List<Expression> expressions = new List<Expression>();
      if (this.currentToken != Token.RightBrace) {
        Expression expression = this.ParseInitializer(followersOrCommaOrRightBrace);
        expressions.Add(expression);
        while (this.currentToken == Token.Comma) {
          this.GetNextToken();
          if (this.currentToken != Token.RightBrace) {
            expression = this.ParseInitializer(followersOrCommaOrRightBrace);
            expressions.Add(expression);
          }
        }
      }
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      VccInitializer result = new VccInitializer(expressions, this.InSpecCode, slb);
      this.SkipOverTo(Token.RightBrace, followers);
      return result;
    }

    protected BitfieldDeclarator ParseBitfieldDeclarator(Declarator/*?*/ fieldDeclarator, TokenSet followers) 
      //^ requires this.currentToken == Token.Colon;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (fieldDeclarator == null)
        fieldDeclarator = new IdentifierDeclarator(new VccNameDeclaration(this.ParseNameDeclaration(false), this.scanner.SourceLocationOfLastScannedToken));
      SourceLocationBuilder slb = new SourceLocationBuilder(fieldDeclarator.SourceLocation);
      this.GetNextToken();
      BitfieldDeclarator result = new BitfieldDeclarator(fieldDeclarator, this.ParseExpression(followers), slb);
      slb.UpdateToSpan(result.FieldSize.SourceLocation);
      this.SkipTo(followers);
      return result;
    }

    protected List<Pointer> ParsePointers(out List<TypeQualifier> fieldQualifiers) {
      var result = new List<Pointer>(2);
      while (true)
      {
        List<TypeQualifier>/*?*/ qualifiers = this.ParseTypeQualifiers();
        if (this.currentToken != Token.Multiply && this.currentToken != Token.BitwiseXor)
        {
          fieldQualifiers = qualifiers;
          break;
        }
        result.Add(this.ParsePointer(qualifiers));      
      }
      result.TrimExcess();
      return result;
    }

    protected Pointer ParsePointer(List<TypeQualifier>/*?*/ qualifiers)
      //^ requires this.currentToken == Token.Multiply || this.currentToken == Token.BitwiseXor;
    {
      SourceLocationBuilder sloc = this.GetSourceLocationBuilderForLastScannedToken();
      bool isSpec = this.currentToken == Token.BitwiseXor;
      this.GetNextToken();
      if (isSpec) {
        if (qualifiers == null) qualifiers = new List<TypeQualifier>(1);
        qualifiers.Add(new TypeQualifier(Token.Specification, sloc));
      }
      return new Pointer(qualifiers, sloc);
    }

    protected ArrayDeclarator ParseArrayDeclarator(Declarator elementTypeAndName, TokenSet followers)
      //^ requires this.currentToken == Token.LeftBracket;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(elementTypeAndName.SourceLocation);
      this.Skip(Token.LeftBracket);
      Expression/*?*/ arraySize = null;
      if (this.currentToken != Token.RightBracket)
        if (this.CurrentTokenStartsTypeExpression())
          arraySize = this.ParseTypeExpression(followers|Token.RightBracket);
        else
          arraySize = this.ParseExpression(followers|Token.RightBracket);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      this.SkipOverTo(Token.RightBracket, followers);
      ArrayDeclarator result = new ArrayDeclarator(elementTypeAndName, arraySize, slb);
      return result;
    }

    protected FunctionDeclarator ParseFunctionDeclarator(Declarator functionName, List<TemplateParameterDeclarator> templateParameters, TokenSet followers)
      //^ requires this.currentToken == Token.LeftParenthesis;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(functionName.SourceLocation);
      List<Parameter> parameters = this.ParseParameterList(followers);
      
      // If the declarator is a pointer to a function declarator, exchange the
      // parameters:
      // int (*func(void))(int) is a function that takes void and return an int->int. 
      parameters = this.OutermostFuncDeclaratorAdjustIfNecessary(functionName, parameters);

      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      FunctionDeclarator result = new FunctionDeclarator(functionName, parameters, templateParameters, slb);
      this.Skip(Token.RightParenthesis);
      this.InitializeLocallyDefinedNamesFromParameters(parameters);
      this.ParseFunctionOrBlockContract(result.Contract, followers);
      return result;
    }

    /// <summary>
    /// When a function that may return a function type, the order of the parameters needs to
    /// be reversed. Given a possible chain of declarators, in which the chain of parameter lists
    /// is in the right order, put the new outer parameter list into the inner most, and shift the
    /// chain of parameter lists outside.
    /// For example:
    /// inner (1) outer (2) -> inner (2) outer (1)
    /// innermost (1) inner (2) outer (3) 0> innermost (3) inner (1) outer (2)
    /// </summary>
    /// <param name="functionName">the function name declarator of the function declarator of concern; the function
    /// name declarator could represent a chain of function types; each link of the chain may be a pointer, or an array.</param>
    /// <param name="currentParameters">the outermost parameter list from parsing</param>
    /// <returns>the new outermost parameter list</returns>
    protected List<Parameter> OutermostFuncDeclaratorAdjustIfNecessary(Declarator functionName, List<Parameter> currentParameters) {
      PointerDeclarator/*?*/ pointerDeclarator = functionName as PointerDeclarator;
      ArrayDeclarator/*?*/ arrayDeclarator = functionName as ArrayDeclarator;
      FunctionDeclarator/*?*/ functionDeclarator = functionName as FunctionDeclarator; 
      if (pointerDeclarator != null)
        functionDeclarator = pointerDeclarator.Declarator as FunctionDeclarator;
      if (arrayDeclarator != null)
        functionDeclarator = arrayDeclarator.ElementType as FunctionDeclarator;
      if (functionDeclarator != null) {
        List<Parameter> temp = functionDeclarator.Parameters;
        List<Parameter> nextToOuttermost = OutermostFuncDeclaratorAdjustIfNecessary(functionDeclarator.FunctionName, currentParameters);
        functionDeclarator.ResetParameters(nextToOuttermost);
        return temp;
      } else {
        return currentParameters;
      }
    }

    protected Expression CheckedExpressionIfRequested(Expression expr) {
      if (this.compilation.Options.CheckedArithmetic)
        return new CheckedExpression(expr, expr.SourceLocation);
      else
        return expr;
    }

    protected TypeExpression/*?*/ TypeExpressionHasPointerType(TypeExpression typeExpr)
    {
      return TypeExpressionHasPointerType(typeExpr, new List<TypeExpression>());
    }

    protected TypeExpression/*?*/ TypeExpressionHasPointerType(TypeExpression typeExpr, List<TypeExpression> visitedTypes)
    {
      PointerTypeExpression pte = typeExpr as PointerTypeExpression;
      if (pte != null) return pte.ElementType;

      ArrayTypeExpression ate = typeExpr as ArrayTypeExpression;
      if (ate != null) return ate.ElementType;

      if (typeExpr is VccTemplateTypeParameterExpression)
        return null;

      if (visitedTypes.Contains(typeExpr)) // cycle in type definitions (or "typedef struct S { ... } S;")
        return null;

      NamedTypeExpression namedTypeExpr = typeExpr as NamedTypeExpression;
      if (namedTypeExpr != null) {
        SimpleName simpleName = namedTypeExpr.Expression as SimpleName;
        if (simpleName != null) {
          TypedefDeclaration typedefDecl;
          if (this.typedefs.TryGetValue(simpleName.ToString(), out typedefDecl)) {
            visitedTypes.Add(typeExpr);
            return TypeExpressionHasPointerType(typedefDecl.Type, visitedTypes);
          }
        }
        return null;
      }
      GenericTypeInstanceExpression genericTypeInstance = typeExpr as GenericTypeInstanceExpression;
      if (genericTypeInstance != null)
        return TypeExpressionHasPointerType(genericTypeInstance.GenericType);
      NonNullTypeExpression nonNullType = typeExpr as NonNullTypeExpression;
      if (nonNullType != null)
        return TypeExpressionHasPointerType(nonNullType);
      return null;
    }

    protected Parameter ParseVarArgsParameter(TokenSet followers) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      IName name = this.GetNameFor("__arglist");
      Declarator dec = new IdentifierDeclarator(new VccNameDeclaration(name, true, slb));
      slb.UpdateToSpan(dec.SourceLocation);
      Parameter result = new Parameter(new List<Specifier>(0), dec, this.InSpecCode, false, slb, true);
      this.SkipTo(followers);
      return result;
    }


    protected void ParseList<T>(List<T> result, Func<TokenSet, T> parseElement, TokenSet followers) {
      TokenSet followersOrCommaOrRightParentesisOrSpecification = followers | Token.Comma | Token.RightParenthesis | Token.Specification;
      while (this.currentToken != Token.RightParenthesis) {
        if (this.currentToken == Token.Specification) {
          this.ParseSpecList(result, parseElement, followersOrCommaOrRightParentesisOrSpecification);
          continue;
        }
        result.Add(parseElement(followersOrCommaOrRightParentesisOrSpecification));
        if (this.currentToken == Token.Comma) {
          this.GetNextToken();
          continue;
        }
        if (this.currentToken == Token.Specification)
          continue;
        break;
      }
    }

    protected void ParseSpecList<T>(List<T> list, Func<TokenSet, T> parseElement, TokenSet followers) {
      bool savedInSpecCode = this.EnterSpecBlock();
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      this.ParseList(list, parseElement, followers | Token.RightParenthesis);
      this.SkipOverTo(Token.RightParenthesis, followers);
      this.LeaveSpecBlock(savedInSpecCode);
    }

    protected Parameter ParseParameter(TokenSet followers) {
      if (this.currentToken == Token.Range) 
        return ParseVarArgsParameter(followers);

      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      if (this.InSpecCode) this.outIsAKeyword = true;
      List<Specifier> specifiers = this.ParseSpecifiers(null, null, null, followers | TS.DeclaratorStart);
      if (this.InSpecCode) this.outIsAKeyword = false;
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[specifiers.Count-1].SourceLocation);
      Declarator declarator;
      if (this.currentToken != Token.Identifier && specifiers.Count > 0 && specifiers[specifiers.Count - 1] is OutSpecifier) {
        // turn out specifier back into identifier
        Specifier o = specifiers[specifiers.Count - 1];
        specifiers.RemoveAt(specifiers.Count - 1);
        declarator = new IdentifierDeclarator(new NameDeclaration(this.GetNameFor("out"), o.SourceLocation));

      } else 
        declarator = this.ParseDeclarator(followers);
      declarator = this.UseDeclaratorAsTypeDefNameIfThisSeemsIntended(specifiers, declarator, followers);
      slb.UpdateToSpan(declarator.SourceLocation);
      var result = new Parameter(specifiers, declarator, this.InSpecCode, false, slb);
      this.SkipTo(followers);
      return result;
    }

    protected Declarator UseDeclaratorAsTypeDefNameIfThisSeemsIntended(List<Specifier> specifiers, Declarator declarator, TokenSet followers) {
      if (this.currentToken == Token.Identifier && declarator is IdentifierDeclarator && (specifiers.Count == 0 || this.TryToGetTypeExpressionFor(specifiers) == null)) {
        specifiers.Add(new TypedefNameSpecifier(new SimpleName(declarator.Identifier.Name, declarator.Identifier.SourceLocation, false)));
        declarator = this.ParseDeclarator(followers);
      }
      return declarator;
    }

    protected List<Specifier> ParseSpecifiers(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, List<ITypeDeclarationMember>/*?*/ typeMembers, List<Specifier> initialSpecifiers, TokenSet followers) {
      List<Specifier> result = new List<Specifier>();
      if (initialSpecifiers != null) result.AddRange(initialSpecifiers);
      bool typeDefNameIsAllowed = true;
      bool typeDefNameMustReferencePrimitive = false;
      TokenSet followersOrSpecifierStart = followers | TS.SpecifierStart;
      IList<Specifier> misplacedSpecifiers;
      for (; ; ) {
        switch (this.currentToken) {
          case Token.Auto:
          case Token.Register:
          case Token.Static:
          case Token.Extern:
          case Token.Typedef:
            result.Add(new StorageClassSpecifier(this.currentToken, this.scanner.SourceLocationOfLastScannedToken));
            this.GetNextToken();
            break;
          case Token.Declspec:
            result.Add(this.ParseDeclspec(followersOrSpecifierStart));
            break;
          case Token.Void:
          case Token.Char:
          case Token.Int:
          case Token.Int8:
          case Token.Int16:
          case Token.Int32:
          case Token.Int64:
          case Token.Float:
          case Token.Bool:
          //case Token.Complex:
          case Token.W64:
          case Token.Axiom:
            typeDefNameIsAllowed = false;
            goto case Token.Double
              ;
          case Token.Double:
          case Token.Long:
          case Token.Short:
          case Token.Signed:
          case Token.Unsigned:
            typeDefNameMustReferencePrimitive = true;
            result.Add(new PrimitiveTypeSpecifier(this.currentToken, this.scanner.SourceLocationOfLastScannedToken));
            this.GetNextToken();
            break;
          case Token.Struct:
            typeDefNameIsAllowed = false;
            misplacedSpecifiers = MoveMisplacedSpecifiers(result);
            result.Add(new StructSpecifier(this.ParseStructuredDeclarationOrDefinition(namespaceMembers, typeMembers, followersOrSpecifierStart, misplacedSpecifiers, true)));
            goto default;
          case Token.Union:
            typeDefNameIsAllowed = false;
            misplacedSpecifiers = MoveMisplacedSpecifiers(result);
            result.Add(new UnionSpecifier(this.ParseStructuredDeclarationOrDefinition(namespaceMembers, typeMembers, followersOrSpecifierStart, misplacedSpecifiers, false)));
            goto default;
          case Token.Enum:
            typeDefNameIsAllowed = false;
            misplacedSpecifiers = MoveMisplacedSpecifiers(result);
            result.Add(new EnumSpecifier(this.ParseEnumDeclarationOrDefinition(namespaceMembers, followersOrSpecifierStart)));
            goto default;
          case Token.Const:
          case Token.Volatile:
          case Token.Unaligned:
            result.Add(new TypeQualifier(this.currentToken, this.scanner.SourceLocationOfLastScannedToken));
            this.GetNextToken();
            break;
          //case Token.Asm:
          case Token.Cdecl:
          case Token.Fastcall:
          case Token.Inline:
          case Token.Stdcall:
            result.Add(new FunctionSpecifier(this.currentToken, this.scanner.SourceLocationOfLastScannedToken));
            this.GetNextToken();
            break;
          case Token.Identifier:
            if (this.InSpecCode && this.outIsAKeyword && this.scanner.GetIdentifierString() == "out") {
              result.Add(new OutSpecifier(this.scanner.SourceLocationOfLastScannedToken));
              this.GetNextToken();
              break;
            }
            if (!typeDefNameIsAllowed) goto default;
            TypeExpression/*?*/ referencedType;
            if (!IdIsTypeDefNameOrTemplateParameter(this.scanner.GetIdentifierString(), out referencedType)) goto default;
            if (typeDefNameMustReferencePrimitive) {
              NamedTypeExpression/*?*/ nte = referencedType as NamedTypeExpression;
              if (nte == null) goto default;
              if (!(nte.Expression is AliasQualifiedName)) goto default;
            }
            typeDefNameIsAllowed = false;
            result.Add(ScopedTypeNameSpecifier.CreateForExpression(this.ParseSimpleOrScopedName(followers | TS.SpecifierThatCombinesWithTypedefName)));
            break;
          case Token.Specification:
            if (!this.ParseSpecTypeModifiers(result, followers))
              goto default;
            else 
              break;
          default:
            this.SkipTo(followers);
            return result;
        }
      }
    }

    protected IList<Specifier> MoveMisplacedSpecifiers(IList<Specifier> specifiers) {

      List<Specifier> result = null;

      foreach (var specifier in specifiers) {
        DeclspecSpecifier declspec = specifier as DeclspecSpecifier;
        if (declspec != null) {
          var modEnum = declspec.Modifiers.GetEnumerator();
          if (modEnum.MoveNext()) {
            if (modEnum.Current.ToString() == NamespaceHelper.SystemDiagnosticsContractsCodeContractString + ".StringVccAttr" && modEnum.MoveNext()) {
              VccByteStringLiteral str = modEnum.Current as VccByteStringLiteral;
              var val = str != null ? str.Value.ToString() : null;
              if (val == "dynamic_owns" || val == "volatile_owns" || val == "claimable") {
                if (result == null) result = new List<Specifier>();
                result.Add(declspec);
              }
            }
          }
        } else if (specifier is SpecDeclspecSpecifier) {
          if (result == null) result = new List<Specifier>();
          result.Add(specifier);
        }
      }
      return result;
    }

    protected DeclspecSpecifier ParseDeclspec(TokenSet followers)
      //^ requires this.currentToken == Token.Declspec;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();
      TokenSet followersOrCommaOrRightParenthesis = followers|Token.Comma|Token.RightParenthesis;
      this.GetNextToken();
      List<Expression> modifiers = new List<Expression>();
      this.Skip(Token.LeftParenthesis);
      if (this.currentToken != Token.RightParenthesis) {
        Expression modifier = this.ParseExpression(followersOrCommaOrRightParenthesis);
        modifiers.Add(modifier);
        while (this.currentToken == Token.Comma) {
          this.GetNextToken();
          modifier = this.ParseExpression(followersOrCommaOrRightParenthesis);
          modifiers.Add(modifier);
        }
      }
      sctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      DeclspecSpecifier result = new DeclspecSpecifier(modifiers, sctx);
      this.SkipOverTo(Token.RightParenthesis, followers);
      return result;
    }

    /// <summary>
    /// In C, there could be structured type declaration inside a method, a scope or another structured declaration,
    /// while in CCI, these have to live in the top level namespace. To avoid name clash, we have to mangle
    /// the names. A mangled name is the original name + a hash that represents the scope 
    /// 
    /// </summary>
    /// <param name="unmangeledName">the unmangled name from the source</param>
    /// <returns>The mangeled name if we are inside a scope, or unmangledName if not.</returns>
    protected NameDeclaration MangledStructuredName(NameDeclaration unmangeledName) {
      string seg1 = unmangeledName.Name.Value;
      string seg2 = this.currentLexicalScope == null ? "" : this.currentLexicalScope.FullMangledName;
      string newname;
      if (String.IsNullOrEmpty(seg2)) newname = seg1;
      else newname = seg1 + "^" + seg2;
      return new VccNameDeclaration(this.nameTable.GetNameFor(newname), true, unmangeledName.SourceLocation);
    }

    protected TypeExpression ParseStructuredDeclarationOrDefinition(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, IList<Specifier> specifiers, bool isStruct) 
      //^ requires this.currentToken == Token.Struct || this.currentToken == Token.Union;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      List<FieldDeclaration>/*?*/ savedSpecificationFields = this.currentSpecificationFields;
      List<TypeInvariant>/*?*/ savedTypeInvariants = this.currentTypeInvariants;
      List<Specifier> extendedAttributes = new List<Specifier>();
      if (specifiers != null) extendedAttributes.AddRange(specifiers);
      this.currentSpecificationFields = null;
      this.currentTypeInvariants = null;
      SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      while (this.currentToken == Token.Declspec) {
        extendedAttributes.Add(this.ParseDeclspec(followers | Token.LeftBrace));
      }
      bool noName = this.currentToken != Token.Identifier;
      NameDeclaration name = this.ParseNameDeclaration(false);
      if (name.Name == this.nameTable.System) {
        this.HandleError(name.SourceLocation, Error.ReservedName, name.Name.Value, "type name");
        name = new VccNameDeclaration(this.GetNameFor(SanitizeString(name.SourceLocation.SourceDocument.Name.Value) + ".." + name.SourceLocation.StartIndex), true, name.SourceLocation);
      }
      NameDeclaration mangledName = this.MangledStructuredName(name);
      NamedTypeExpression/*?*/ texpr = null;
      List<ITypeDeclarationMember> newTypeMembers = new List<ITypeDeclarationMember>();
      object type = null;

      if (this.currentToken == Token.LeftBrace) {
        if (this.currentTypeName != null) {
          SimpleName nestedName = new VccSimpleName(name, name.SourceLocation);
          texpr = new VccNamedTypeExpression(new QualifiedName(this.currentTypeName, nestedName, name.SourceLocation));
          ITypeDeclarationMember nestedType;
          if (isStruct)
            nestedType = new VccNestedStructDeclaration(name, newTypeMembers, extendedAttributes, sctx);
          else
            nestedType = new VccNestedUnionDeclaration(name, newTypeMembers, extendedAttributes, sctx);
          if (typeMembers != null)
            typeMembers.Add(nestedType);
          type = nestedType;
          if (namespaceMembers != null)
            namespaceMembers.Insert(0, new AliasDeclaration(mangledName, texpr.Expression, name.SourceLocation));
        } else {
          texpr = new VccNamedTypeExpression(new VccSimpleName(mangledName, name.SourceLocation));
          INamespaceDeclarationMember namespaceType;
          if (isStruct)
            namespaceType = new VccStructDeclaration(mangledName, newTypeMembers, extendedAttributes, sctx);
          else
            namespaceType = new VccUnionDeclaration(mangledName, newTypeMembers, extendedAttributes, sctx);
          if (namespaceMembers != null)
            namespaceMembers.Add(namespaceType);
          type = namespaceType;
        }

        //TODO: else give error
        this.ParseRestOfTypeDeclaration(sctx, namespaceMembers, texpr.Expression, newTypeMembers, followers);
        if (this.currentToken == Token.EndOfFile) {
          ISourceLocation errorLocation = this.scanner.SourceLocationOfLastScannedToken;
          this.HandleError(errorLocation, Error.MissingSemicolonAfterStruct, "end-of-file");
        }   
        this.SkipTo(followers);
        // filter out unexpected constructs that cannot have they CompilationPart setup properly, they may
        // have been generated as artifacts of recovery from parse errors
        // see Microsoft.Cci.Ast.TypeDeclaration.SetMemberContainingTypeDeclaration for the supported classes
        newTypeMembers.RemoveAll(delegate(ITypeDeclarationMember member) { return !(member is TypeDeclarationMember || member is NestedTypeDeclaration); });
        this.AssociateTypeWithTypeContract(type, this.currentSpecificationFields, this.currentTypeInvariants, this.InSpecCode);
      } else if (noName) {
        texpr = new VccNamedTypeExpression(new VccSimpleName(name, name.SourceLocation));
        this.HandleError(name.SourceLocation, Error.ExpectedIdentifier);
        this.SkipTo(followers);
      }
      if (texpr == null) {
        VccSimpleName simpleName = new VccSimpleName(mangledName, name.SourceLocation);
        if (this.currentToken == Token.ScopeResolution)
          texpr = new VccScopedTypeExpression((VccScopedName)this.ParseScopedName(simpleName, followers | Token.ScopeResolution));
        else 
          texpr = new VccNamedTypeExpression(simpleName);
      }

      if (newTypeMembers.Count == 0 && currentSpecificationFields == null)
        this.emptyStructuredTypes[texpr] = true;

      this.currentSpecificationFields = savedSpecificationFields;
      this.currentTypeInvariants = savedTypeInvariants;
      return texpr;
    }

    protected void AssociateTypeWithTypeContract(object type, List<FieldDeclaration> specFields, List<TypeInvariant> invariants, bool isSpecType) {
      if (specFields != null || invariants != null || isSpecType) {
        VccTypeContract tc = new VccTypeContract(specFields, invariants, isSpecType);
        this.compilation.ContractProvider.AssociateTypeWithContract(type, tc);
      }
    }

    protected void ParseRestOfTypeDeclaration(SourceLocationBuilder sctx, List<INamespaceDeclarationMember>/*?*/ namespaceMembers, Expression typeName, List<ITypeDeclarationMember> typeMembers, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      TokenSet fieldFollowers = followers | Token.RightBrace | Token.Specification | Token.Invariant;
      Expression/*?*/ savedCurrentTypeName = this.currentTypeName;
      this.currentTypeName = typeName;
      List<ITypeDeclarationMember>/*?*/ savedCurrentTypeMembers = this.currentTypeMembers;
      this.currentTypeMembers = typeMembers;
      this.Skip(Token.LeftBrace);
      this.ParseTypeMemberDeclarationList(namespaceMembers, typeMembers, fieldFollowers);
      ISourceLocation tokLoc = this.scanner.SourceLocationOfLastScannedToken;
      //^ assume tokLoc.SourceDocument == sctx.SourceDocument;
      sctx.UpdateToSpan(tokLoc);
      typeMembers.TrimExcess();
      this.Skip(Token.RightBrace); //, followers);
      this.currentTypeName = savedCurrentTypeName;
      this.currentTypeMembers = savedCurrentTypeMembers;
    }

    protected void ParseTypeSpecMemberDeclarationList(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers) {
      bool savedInSpecCode = this.EnterSpecBlock();
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      this.ParseTypeMemberDeclarationList(namespaceMembers, typeMembers, followers | Token.RightParenthesis);
      this.SkipOverTo(Token.RightParenthesis, followers);
      this.LeaveSpecBlock(savedInSpecCode);
    }


    protected List<TypeQualifier>/*?*/ ParseTypeQualifiers() {
      List<TypeQualifier>/*?*/ result = null;
      for (; ; ) {
        switch (this.currentToken) {
          case Token.Const:
          case Token.Volatile:
          case Token.Cdecl:
          case Token.Unaligned:
            if (result == null) result = new List<TypeQualifier>(1);
            result.Add(new TypeQualifier(this.currentToken, this.scanner.SourceLocationOfLastScannedToken));
            this.GetNextToken();
            break;
          default:
            return result;
        }
      }
    }

    protected TypeExpression ParseEnumDeclarationOrDefinition(List<INamespaceDeclarationMember>/*?*/ namespaceMembers, TokenSet followers)
      //^ requires this.currentToken == Token.Enum;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      NameDeclaration name = this.ParseNameDeclaration(false);
      NameDeclaration newname = this.MangledStructuredName(name);
      VccNamedTypeExpression texpr = new VccNamedTypeExpression(new VccSimpleName(newname, name.SourceLocation));
      if (this.currentToken == Token.LeftBrace) {
        List<ITypeDeclarationMember> members = new List<ITypeDeclarationMember>();
        NamespaceEnumDeclaration enumDeclaration = new VccEnumDeclaration(newname, this.GetTypeExpressionFor(TypeCode.UInt32, name.SourceLocation), members, sctx);
        if (namespaceMembers != null)
          namespaceMembers.Add(enumDeclaration);
        //TODO: else give error
        this.Skip(Token.LeftBrace);
        while (this.currentToken == Token.Identifier) {
          FieldDeclaration enumField = this.ParseEnumMember(texpr, members, followers|Token.Comma|Token.RightBrace);
          //TODO: deal with enums declared inside a method body.
          this.currentTypeMembers.Add(enumField); //promote the enumeration member to a constant in the current namespace.
          if (this.currentToken == Token.RightBrace) break;
          this.Skip(Token.Comma);
          if (this.currentToken == Token.RightBrace) break;
        }
        sctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        this.Skip(Token.RightBrace);
      }
      this.SkipTo(followers);
      return texpr;
    }

    protected FieldDeclaration ParseEnumMember(VccNamedTypeExpression typeExpression, List<ITypeDeclarationMember>/*?*/ members, TokenSet followers)
      //^ requires this.currentToken == Token.Identifier;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();
      List<SourceCustomAttribute>/*?*/ attributes = null;
      NameDeclaration name = this.ParseNameDeclaration(true);
      Expression/*?*/ initializer = null;
      if (this.currentToken == Token.Assign) {
        this.GetNextToken();
        initializer = this.ParseExpression(followers);
      }
      EnumMember member = new EnumMember(attributes, typeExpression, name, initializer, sctx);
      if (members != null) members.Add(member);
      var globalInitializer = new QualifiedName(typeExpression.Expression, new VccSimpleName(name, name.SourceLocation), name.SourceLocation);
      FieldDeclaration.Flags flags = FieldDeclaration.Flags.Constant|FieldDeclaration.Flags.Static|FieldDeclaration.Flags.Unsafe; //TODO: why unsafe?
      FieldDeclaration result = new FieldDeclaration(null, flags, TypeMemberVisibility.Assembly, typeExpression, name, globalInitializer, sctx);
      this.SkipTo(followers);
      return result;
    }

    protected TypeExpression GetTypeExpressionFor(TypeCode typeCode, ISourceLocation sourceLocation)
      //^ requires typeCode == TypeCode.Boolean || typeCode == TypeCode.Byte || typeCode == TypeCode.Double || typeCode == TypeCode.Int16 ||
      //^   typeCode == TypeCode.Int32 || typeCode == TypeCode.Int64 || typeCode == TypeCode.SByte || typeCode == TypeCode.Single ||
      //^   typeCode == TypeCode.UInt16 || typeCode == TypeCode.UInt32 || typeCode == TypeCode.UInt64 || typeCode == TypeCode.Empty; 
    {
      return new NamedTypeExpression(this.RootQualifiedNameFor(typeCode, sourceLocation));
    }


    protected BlockStatement ParseBody(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder bodyCtx = this.GetSourceLocationBuilderForLastScannedToken();
      List<Statement> statements = new List<Statement>();
      BlockStatement block = new BlockStatement(statements, 
        this.compilation.Options.CheckedArithmetic ? BlockStatement.Options.UseCheckedArithmetic : BlockStatement.Options.UseUncheckedArithmetic, bodyCtx);
      this.ParseBody(statements, bodyCtx, followers);
      //TODO: throw the body away and replace it with a stub that will reparse when needed.
      return block;
    }

    protected void ParseBody(List<Statement> statements, SourceLocationBuilder bodyCtx, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      bodyCtx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      if (this.currentToken == Token.LeftBrace){
        this.GetNextToken();
        this.ParseStatementList(statements, followers|Token.RightBrace);
        statements.Add(new EmptyStatement(true, this.scanner.SourceLocationOfLastScannedToken));
        bodyCtx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        this.Skip(Token.RightBrace);
      }
      this.SkipTo(followers);
    }

    protected BlockStatement ParseBlock(TokenSet followers)
      //^ requires options == BlockStatement.Options.Default || options == BlockStatement.Options.AllowUnsafeCode || 
      //^  options == BlockStatement.Options.UseCheckedArithmetic || options == BlockStatement.Options.UseUncheckedArithmetic;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      FunctionOrBlockContract contract = new FunctionOrBlockContract();
      if (this.currentToken == Token.Block) {
        this.Skip(Token.Block);
        this.ParseFunctionOrBlockContract(contract, followers);
      }
      this.Skip(Token.LeftBrace);
      List<Statement> statements = new List<Statement>();
      this.ParseStatementList(statements, followers|Token.RightBrace);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      BlockStatement result = contract.HasContract ? new VccBlockWithContracts(statements, slb) : new BlockStatement(statements, slb);
      if (contract.HasContract) {
        this.compilation.ContractProvider.AssociateMethodWithContract(result, contract.ToMethodContract());
      }
      this.SkipOverTo(Token.RightBrace, followers);
      return result;
    }

    protected void ParseStatementList(List<Statement> statements, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      TokenSet statementFollowers = followers | TS.StatementStart;
      if (!statementFollowers[this.currentToken])
        this.SkipTo(statementFollowers, Error.InvalidExprTerm, this.scanner.GetTokenSource());
      while (TS.StatementStart[this.currentToken]) {
        Statement s = this.ParseStatement(statementFollowers);
        StatementGroup.AddStatementOrGroupToList(s, statements);
      }
      this.SkipTo(followers);
    }

    protected Statement ParseStatement(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      Statement result;

      switch (this.currentToken) {
        case Token.LeftBrace:
        case Token.Block:
          //this.lexicalScopeSuffix = this.PushScopeString(this.lexicalScopeSuffix, this.GetNewScopeId());
          SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
          this.currentLexicalScope = new LexicalScope(this.currentLexicalScope, slb);
          result = this.ParseBlock(followers);
          this.currentLexicalScope = this.currentLexicalScope.ParentScope;
          return result;
        case Token.Semicolon: return this.ParseEmptyStatement(followers);
        case Token.If: return this.ParseIf(followers);
        case Token.Switch: return this.ParseSwitch(followers);
        case Token.While: return this.ParseWhile(followers);
        case Token.Do: return this.ParseDoWhile(followers);
        case Token.For: return this.ParseFor(followers);
        case Token.Assert: return this.ParseSingleArgStatement(followers, (expr, sl) => new AssertStatement(expr, sl));
        case Token.Assume: return this.ParseSingleArgStatement(followers, (expr, sl) => new AssumeStatement(expr, sl));
        case Token.Break: return this.ParseSimpleStatement(followers, sl => new BreakStatement(sl));
        case Token.Continue: return this.ParseSimpleStatement(followers, sl => new ContinueStatement(sl));
        case Token.Goto: return this.ParseGoto(followers);
        case Token.Return: return this.ParseReturn(followers);
        case Token.Specification: return this.ParseSpecStatements(followers);
        default:
          return this.ParseExpressionStatementOrDeclaration(false, followers);
      }
    }

    protected Statement ParseExpressionStatementOrDeclaration(bool inForInitializer, TokenSet followers)
      //^ requires acceptComma ==> followers[Token.Comma];
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      //^ ensures result is ExpressionStatement || result is LocalDeclarationsStatement || (acceptLabel && result is LabeledStatement);
    {
      if (this.CurrentTokenStartsDeclaration()) {
        List<Statement> statements = this.ParseLocalDeclaration(followers);
        return StatementGroup.Create(statements);
      }
      TokenSet followersOrCommaOrColonOrSemicolon = followers|Token.Comma|Token.Colon|Token.Semicolon;
      Expression e = this.ParseExpression(!inForInitializer, false, followersOrCommaOrColonOrSemicolon);
      SourceLocationBuilder slb = new SourceLocationBuilder(e.SourceLocation);
      ExpressionStatement eStat = new ExpressionStatement(e, slb);
      VccSimpleName/*?*/ id;
      if (this.currentToken == Token.Colon && !inForInitializer && (id = e as VccSimpleName) != null)
        return this.ParseLabeledStatement(id, followers);
      if (!inForInitializer) {
          this.SkipSemiColonAfterDeclarationOrStatement(followers);
      } else {
          if (this.currentToken != Token.Comma) {
              this.SkipOverTo(Token.Semicolon, followers);
          }
      }
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return eStat;
    }

    protected LabeledStatement ParseLabeledStatement(VccSimpleName label, TokenSet followers) 
      //^ requires this.currentToken == Token.Colon;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(label.SourceLocation);
      this.GetNextToken();
      LoopContract/*?*/ contract = this.ParseLoopContract(followers);
      Statement statement;
      if (TS.StatementStart[this.currentToken]) {
        statement = this.ParseStatement(followers);
      } else {
        statement = new EmptyStatement(false, this.scanner.SourceLocationOfLastScannedToken);
        this.SkipTo(followers, Error.ExpectedSemicolon);
      }
      //^ assert followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      slb.UpdateToSpan(statement.SourceLocation);
      LabeledStatement result = new LabeledStatement(new VccNameDeclaration(label.Name, label.SourceLocation), statement, slb);
      if (contract != null)
        this.compilation.ContractProvider.AssociateLoopWithContract(result, contract);
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return result;
    }

    protected Statement ParseReturn(TokenSet followers)       
      //^ requires this.currentToken == Token.Return;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Expression/*?*/ expr = null;
      if (this.currentToken != Token.Semicolon) {
        expr = this.ParseExpression(true, false, followers|Token.Semicolon);
        slb.UpdateToSpan(expr.SourceLocation);
      }
      Statement result = new ReturnStatement(expr, slb);
      this.SkipSemiColon(followers);
      return result;
    }

    protected Statement ParseSingleArgStatement(TokenSet followers, Func<Expression, ISourceLocation, Statement> func)  {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      Expression/*?*/ expr = this.ParseExpression(true, false, followers|Token.RightParenthesis|Token.Semicolon);
      slb.UpdateToSpan(expr.SourceLocation);
      Statement result = func(expr, slb);
      this.SkipOverTo(Token.RightParenthesis, followers|Token.Semicolon);
      this.SkipSemiColon(followers);
      return result;
    }

    protected Statement ParseGoto(TokenSet followers)
      //^ requires this.currentToken == Token.Goto;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Statement result = new GotoStatement(this.ParseSimpleName(followers), slb);
      this.SkipSemiColon(followers);
      return result;
    }

    protected Statement ParseSimpleStatement(TokenSet followers, Func<ISourceLocation, Statement> func)       
    {
      ISourceLocation sourceLocation = this.scanner.SourceLocationOfLastScannedToken;
      this.GetNextToken();
      Statement result = func(sourceLocation);
      this.SkipSemiColon(followers);
      return result;
    }

    protected Statement ParseFor(TokenSet followers)
      //^ requires this.currentToken == Token.For;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      TokenSet followersOrRightParenthesisOrSemicolon = followers | TS.RightParenthesisOrSemicolon | Token.Invariant | Token.Writes;
      List<Statement> initStatements = this.ParseForInitializer(followersOrRightParenthesisOrSemicolon);
      Expression condition = this.ParseForCondition(followersOrRightParenthesisOrSemicolon);
      List<Statement> incrementStatements = this.ParseForIncrementer(followers | Token.RightParenthesis | Token.Invariant | Token.Writes);
      this.Skip(Token.RightParenthesis);
      LoopContract/*?*/ contract = this.ParseLoopContract(followers);
      Statement body = this.ParseStatement(followers);
      slb.UpdateToSpan(body.SourceLocation);
      this.WarnIfLoopWithContractAndEmptyBody(contract, body);
      ForStatement result = new ForStatement(initStatements, condition, incrementStatements, body, slb);
      if (contract != null)
        this.compilation.ContractProvider.AssociateLoopWithContract(result, contract);
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return result;
    }

    protected List<Statement> ParseForInitializer(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.Semicolon || this.currentToken == Token.RightParenthesis || this.currentToken == Token.EndOfFile;
    {
      List<Statement> statements = new List<Statement>(1);
      if (this.currentToken == Token.Semicolon) {
        this.GetNextToken();
        statements.TrimExcess();
        //^ assume this.currentToken == Token.Semicolon;
        return statements;
      }
      if (this.currentToken == Token.RightParenthesis) {
        this.Skip(Token.Semicolon);
        statements.TrimExcess();
        //^ assume this.currentToken == Token.RightParenthesis;
        return statements;
      }
      TokenSet followerOrComma = followers|Token.Comma;
      for (; ; ) {
        //^ assume followerOrComma[Token.Comma];
        var exprOrDecl = this.ParseExpressionStatementOrDeclaration(true, followerOrComma);        
        var grp = exprOrDecl as StatementGroup;
        var stmts = grp == null ? IteratorHelper.GetSingletonEnumerable(exprOrDecl) : grp.Statements;
        foreach (var s in stmts) {
          statements.Add(s);
          if (s is LocalDeclarationsStatement) {
            if (statements.Count > 1)
              this.HandleError(s.SourceLocation, Error.ExpectedExpression);
          } else {
            ExpressionStatement es = (ExpressionStatement)s;
            Expression e = es.Expression;
            if (!(e is Assignment || e is BinaryOperationAssignment || e is MethodCall || e is UnaryOperationAssignment || e is CreateObjectInstance))
              this.HandleError(e.SourceLocation, Error.IllegalStatement);
          }
        }
        //^ assume followers[this.currentToken] || this.currentToken == Token.Comma || this.currentToken == Token.EndOfFile;
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      //^ assert followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      statements.TrimExcess();
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return statements;
    }

    protected List<Statement> ParseForIncrementer(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.RightParenthesis || this.currentToken == Token.EndOfFile;
    {
      List<Statement> statements = new List<Statement>(1);
      if (this.currentToken == Token.RightParenthesis) {
        statements.TrimExcess();
        //^ assume this.currentToken == Token.RightParenthesis;
        return statements;
      }
      TokenSet followerOrComma = followers|Token.Comma;
      for (; ; ) {
        Expression e = this.ParseExpression(followerOrComma);
        if (!(e is Assignment || e is BinaryOperationAssignment || e is MethodCall || e is UnaryOperationAssignment || e is CreateObjectInstance))
          this.HandleError(e.SourceLocation, Error.IllegalStatement);
        statements.Add(new ExpressionStatement(e));
        //^ assume followers[this.currentToken] || this.currentToken == Token.Comma || this.currentToken == Token.EndOfFile;
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      //^ assert followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      statements.TrimExcess();
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return statements;
    }

    protected Expression ParseForCondition(TokenSet follower)
    {
      Expression result;
      if (this.currentToken != Token.Semicolon)
        result = this.ParseExpression(follower);
      else {
        SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
        result = new CompileTimeConstant(true, slb.GetSourceLocation());
      }
      this.Skip(Token.Semicolon);
      return result;
    }

    protected Statement ParseDoWhile(TokenSet followers)
      //^ requires this.currentToken == Token.Do;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      LoopContract/*?*/ contract = this.ParseLoopContract(followers);
      Statement body = this.ParseStatement(followers|Token.While);
      if (body is EmptyStatement)
        this.HandleError(body.SourceLocation, Error.PossibleMistakenNullStatement);
      this.Skip(Token.While);
      Expression condition = this.ParseParenthesizedExpression(followers|Token.Semicolon);
      DoWhileStatement result = new DoWhileStatement(body, condition, slb);
      if (contract != null)
        this.compilation.ContractProvider.AssociateLoopWithContract(result, contract);

      this.SkipSemiColon(followers);
      return result;
    }

    protected Statement ParseWhile(TokenSet followers) 
      //^ requires this.currentToken == Token.While;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Expression condition = this.ParseParenthesizedExpression(followers | Token.Invariant | Token.Semicolon | Token.Writes);
      LoopContract/*?*/ contract = this.ParseLoopContract(followers);
      Statement body = this.ParseStatement(followers);
      slb.UpdateToSpan(body.SourceLocation);
      WarnIfLoopWithContractAndEmptyBody(contract, body);
      WhileDoStatement result = new WhileDoStatement(condition, body, slb);
      if (contract != null)
        this.compilation.ContractProvider.AssociateLoopWithContract(result, contract);
      this.SkipTo(followers);
      return result;
    }

    protected Statement ParseSwitch(TokenSet followers)
      //^ requires this.currentToken == Token.Switch;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      var expression = this.ParseParenthesizedExpression(followers|Token.LeftBrace);
      var cases = new List<VccMatchCase>();
      var isMatch = false;
      this.Skip(Token.LeftBrace);
      TokenSet followersOrCaseOrColonOrDefaultOrRightBrace = followers | TS.CaseOrColonOrDefaultOrRightBrace;
      TokenSet followersOrCaseOrDefaultOrRightBrace = followers | TS.CaseOrDefaultOrRightBrace;
      for (; ; ) {
        SourceLocationBuilder scCtx = this.GetSourceLocationBuilderForLastScannedToken();
        Expression/*?*/ scExpression = null;
        switch (this.currentToken) {
          case Token.Case:
            this.GetNextToken();
            if (this.currentToken == Token.Colon)
              this.HandleError(Error.ConstantExpected);
            else {
              scExpression = this.ParseExpression(followersOrCaseOrColonOrDefaultOrRightBrace);
              isMatch |= scExpression is VccMethodCall;
              scCtx.UpdateToSpan(scExpression.SourceLocation);
            }
            break;
          case Token.Default: //Parse these as many times as they occur. Checker will report the error.
            this.GetNextToken();
            break;
          default:
            if (TS.StatementStart[this.currentToken]) {
              this.HandleError(Error.StmtNotInCase);
              this.ParseStatement(followersOrCaseOrColonOrDefaultOrRightBrace);
              continue;
            }
            goto done;
        }
        this.Skip(Token.Colon);
        IEnumerable<Statement> scBody;
        if (TS.StatementStart[this.currentToken])
          scBody = this.ParseSwitchCaseStatementBlock(scCtx, followersOrCaseOrDefaultOrRightBrace);
        else
          scBody = Enumerable<Statement>.Empty;
        cases.Add(new VccMatchCase(scExpression, scBody, scCtx));
      }
    done:
      if (cases.Count == 0) {
        this.HandleError(Error.EmptySwitch);
      } else {
        // add SwitchCaseBottom to last case if it happened to have no statements.
        cases[cases.Count - 1].AddEmptyStatement();
      }

      Statement result;
      if (isMatch) {
        cases.TrimExcess();
        result = new VccMatchStatement(expression, cases, slb);
      } else {
        var switchCases = cases.Select(c => c.ToSwitchCase()).ToList();
        switchCases.TrimExcess();
        result = new SwitchStatement(expression, switchCases, slb);
      }
      this.SkipOverTo(Token.RightBrace, followers);
      return result;
    }

    protected IEnumerable<Statement> ParseSwitchCaseStatementBlock(SourceLocationBuilder switchCaseContext, TokenSet followers)
      //^ requires Parser.StatementStart[this.currentToken];
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      List<Statement> statements = new List<Statement>();
      while (TS.StatementStart[this.currentToken]) {
        Statement s = this.ParseStatement(followers);
        StatementGroup.AddStatementOrGroupToList(s, statements);
      }
      if (statements.Count > 0) {
        ISourceLocation sctx = statements[statements.Count-1].SourceLocation;
        switchCaseContext.UpdateToSpan(sctx);
        statements.Add(new EmptyStatement(true, sctx));
      }
      statements.TrimExcess();
      IEnumerable<Statement> result = statements.AsReadOnly();
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return result;
    }

    protected Statement ParseIf(TokenSet followers)       
      //^ requires this.currentToken == Token.If;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Expression ifCondition = this.ParseParenthesizedExpression(followers | TS.StatementStart);
      Statement ifTrue = this.ParseStatement(followers|Token.Else);
      if (ifTrue is EmptyStatement)
        this.HandleError(ifTrue.SourceLocation, Error.PossibleMistakenNullStatement);
      Statement ifFalse;
      if (this.currentToken == Token.Else) {
        this.GetNextToken();
        ifFalse = this.ParseStatement(followers);
        if (ifFalse is EmptyStatement)
          this.HandleError(ifFalse.SourceLocation, Error.PossibleMistakenNullStatement);
      } else {
        ifFalse = new EmptyStatement(false, ifTrue.SourceLocation);
      }
      slb.UpdateToSpan(ifFalse.SourceLocation);
      Statement result = new ConditionalStatement(ifCondition, ifTrue, ifFalse, slb);
      this.SkipTo(followers);
      return result;
    }

    protected Statement ParseEmptyStatement(TokenSet followers)
      //^ requires this.currentToken == Token.Semicolon;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      EmptyStatement result = new EmptyStatement(false, this.scanner.SourceLocationOfLastScannedToken);
      this.GetNextToken();
      this.SkipTo(followers);
      return result;
    }

    protected Expression ParseExpression(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      return this.ParseExpression(false, false, followers);
    }

    protected Expression ParseExpression(bool allowCommaExpressions, bool allowInitializer, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      TokenSet followersOrInfixOperators = followers | TS.InfixOperators;
      Expression operand1 = this.ParseUnaryExpression(allowInitializer, followersOrInfixOperators);
      for (; ; ) {
        if (!TS.InfixOperators[this.currentToken] || (this.currentToken == Token.Comma && !allowCommaExpressions)) {
          this.SkipTo(followers);
          return operand1;
        }
        if (this.currentToken == Token.Conditional)
          operand1 = this.ParseConditional(operand1, followers|Token.Comma);
        else if (this.currentToken == Token.Comma) {
          this.GetNextToken();
          Expression operand2 = this.ParseUnaryExpression(followers | TS.InfixOperators);
          if (TS.InfixOperators[this.currentToken])
            operand2 = this.ParseAssignmentExpression(operand2, followers);
          operand1 = this.AllocateBinaryExpression(operand1, operand2, Token.Comma);
        } else {
          Expression assignmentExpr = this.ParseAssignmentExpression(operand1, followers|Token.Comma);
          if (assignmentExpr == operand1) return assignmentExpr; //no progress made, exit.
          operand1 = assignmentExpr;
        }
      }
    }

    protected List<Expression> ParseExpressionList(Token separator, TokenSet followers) {
      return this.ParseExpressionList(new List<Expression>(), separator, true, followers);
    }

    protected List<Expression> ParseExpressionList(List<Expression> listToAddTo, Token separator, bool checkedExpressions, TokenSet followers) {
      while (true) {
        Expression e = this.ParseExpression(followers | separator);
        if (checkedExpressions) { e = this.CheckedExpressionIfRequested(e); }
        listToAddTo.Add(e);
        if (this.currentToken != separator) break;
        this.GetNextToken();
      }
      return listToAddTo;
    }

    protected List<Expression> ParseExpressionListWithParens(Token leftParen, Token separator, Token rightParen, TokenSet followers) {
      return ParseExpressionListWithParens(new List<Expression>(), leftParen, separator, rightParen, followers);
    }

    protected List<Expression> ParseExpressionListWithParens(List<Expression> listToAddTo, Token leftParen, Token separator, Token rightParen, TokenSet followers) {
      this.GetNextToken();
      this.Skip(leftParen);
      this.ParseExpressionList(listToAddTo, separator, true, followers | rightParen);
      this.SkipOverTo(rightParen, followers);
      return listToAddTo;
    }

    protected TResult ParseExpressionWithParens<TResult>(TokenSet followers, Func<Expression, ISourceLocation, TResult> func) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      this.Skip(Token.LeftParenthesis);
      Expression expr = this.ParseExpression(followers | Token.RightParenthesis);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      TResult result = func(expr, slb);
      this.SkipOverTo(Token.RightParenthesis, followers);
      return result;
    }

    protected Expression ParseAssignmentExpression(Expression operand1, TokenSet followers) 
      //^ requires Parser.InfixOperators[this.currentToken];
      //^ requires this.currentToken != Token.Conditional && this.currentToken != Token.Comma;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      switch (this.currentToken) {
        case Token.AddAssign:
        case Token.Assign:
        case Token.BitwiseAndAssign:
        case Token.BitwiseOrAssign:
        case Token.BitwiseXorAssign:
        case Token.DivideAssign:
        case Token.LeftShiftAssign:
        case Token.MultiplyAssign:
        case Token.RemainderAssign:
        case Token.RightShiftAssign:
        case Token.SubtractAssign:
          SourceLocationBuilder slb = new SourceLocationBuilder(operand1.SourceLocation);
          Token operatorToken = this.currentToken;
          this.GetNextToken();
          TargetExpression target = new TargetExpression(operand1);
          Expression operand2 = this.ParseExpression(false, operatorToken == Token.DivideAssign, followers);
          slb.UpdateToSpan(operand2.SourceLocation);
          //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
          switch (operatorToken) {
            case Token.AddAssign: return new VccAdditionAssignment(target, operand2, slb);
            case Token.BitwiseAndAssign: return new BitwiseAndAssignment(target, operand2, slb);
            case Token.BitwiseOrAssign: return new BitwiseOrAssignment(target, operand2, slb);
            case Token.BitwiseXorAssign: return new ExclusiveOrAssignment(target, operand2, slb);
            case Token.DivideAssign:
              VccInitializerWithDesignators initializer = operand2 as VccInitializerWithDesignators;
              if (initializer != null)
                return new VccInitializerAssignment(target, initializer, slb);
              else 
                return new DivisionAssignment(target, operand2, slb);
            case Token.LeftShiftAssign: return new LeftShiftAssignment(target, this.ConvertToInt32(operand2), slb);
            case Token.MultiplyAssign: return new MultiplicationAssignment(target, operand2, slb);
            case Token.RemainderAssign: return new VccModulusAssignment(target, operand2, slb);
            case Token.RightShiftAssign: return new RightShiftAssignment(target, this.ConvertToInt32(operand2), slb);
            case Token.SubtractAssign: return new SubtractionAssignment(target, operand2, slb);
            default: return new VccAssignment(target, operand2, slb);
          }
        default:
          operand1 = this.ParseBinaryExpression(operand1, followers|Token.Conditional);
          if (this.currentToken == Token.Conditional)
            return this.ParseConditional(operand1, followers);
          //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
          return operand1;
      }
    }

    protected Expression ParseBinaryExpression(Expression operand1, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      TokenSet unaryFollowers = followers | TS.InfixOperators;
      Expression expression;
      if (TS.BinaryOperators[this.currentToken]) {
        Token operator1 = this.currentToken;
        this.GetNextToken();
        if (operator1 == Token.SpecIs) {
          SourceLocationBuilder slb = new SourceLocationBuilder(operand1.SourceLocation);
          var type = this.ParseTypeExpression(unaryFollowers);
          slb.UpdateToSpan(type.SourceLocation);
          expression = new CheckIfInstance(operand1, type, slb);
          if (TS.BinaryOperators[this.currentToken])
            expression = this.ParseBinaryExpression(expression, unaryFollowers);
        } else {
          Expression operand2 = this.ParseUnaryExpression(operator1 == Token.Divide, unaryFollowers);
          if (TS.BinaryOperators[this.currentToken])
            expression = this.ParseComplexExpression(Token.None, operand1, operator1, operand2, unaryFollowers);
          else
            expression = this.AllocateBinaryExpression(operand1, operand2, operator1);
        }
      } else expression = operand1;
      this.SkipTo(followers);
      return expression;
    }

    protected Expression AllocateBinaryExpression(Expression operand1, Expression operand2, Token operatorToken) {
      SourceLocationBuilder slb = new SourceLocationBuilder(operand1.SourceLocation);
      slb.UpdateToSpan(operand2.SourceLocation);
      switch (operatorToken) {
        case Token.Plus: return new VccAddition(operand1, operand2, slb);
        case Token.BitwiseAnd: return new VccBitwiseAnd(operand1, operand2, slb);
        case Token.BitwiseOr: return new VccBitwiseOr(operand1, operand2, slb);
        case Token.BitwiseXor: return new VccExclusiveOr(operand1, operand2, slb);
        case Token.Comma: return new Comma(operand1, operand2, slb);
        case Token.Explies: return new VccExplies(operand1, operand2, slb);
        case Token.IfAndOnlyIf: return new VccIfAndOnlyIf(operand1, operand2, slb);
        case Token.Equal: return new VccEquality(operand1, operand2, slb);
        case Token.GreaterThan: return new GreaterThan(operand1, operand2, slb);
        case Token.GreaterThanOrEqual: return new GreaterThanOrEqual(operand1, operand2, slb);
        case Token.Implies: return new Implies(operand1, operand2, slb);
        case Token.LeftShift: return new VccLeftShift(this.ProvideSignBiasIfNeeded(operand1, operand2), this.ConvertToInt32(operand2), slb);
        case Token.LessThan: return new LessThan(operand1, operand2, slb);
        case Token.LessThanOrEqual: return new LessThanOrEqual(operand1, operand2, slb);
        case Token.LogicalAnd: return new VccLogicalAnd(operand1, operand2, slb);
        case Token.LogicalOr: return new VccLogicalOr(operand1, operand2, slb);
        case Token.Multiply: return new VccMultiplication(operand1, operand2, slb);
        case Token.NotEqual: return new VccNotEquality(operand1, operand2, slb);
        case Token.Remainder: return new VccModulus(operand1, operand2, slb);
        case Token.RightShift: return new VccRightShift(this.ProvideSignBiasIfNeeded(operand1, operand2), this.ConvertToInt32(operand2), slb);
        case Token.Subtract: return new VccSubtraction(operand1, operand2, slb);
        case Token.Divide:
          VccInitializerWithDesignators initializer = operand2 as VccInitializerWithDesignators;
          if (initializer != null)
            return new VccInitializerWithDefault(operand1, initializer, slb);
          return new VccDivision(operand1, operand2, slb);
        case Token.SetIn: return new VccSetMember(operand1, operand2, false, slb);
        case Token.SetIn0: return new VccSetMember(operand1, operand2, true, slb);
        case Token.SetIntersection: return new VccSetIntersection(operand1, operand2, slb);
        case Token.SetUnion: return new VccSetUnion(operand1, operand2, slb);
        case Token.SetDifference: return new VccSetDifference(operand1, operand2, slb);
        default:
          //^ assume false;
          goto case Token.Plus;
      }
    }

    protected Expression ProvideSignBiasIfNeeded(Expression operand1, Expression operand2) {
      CompileTimeConstant/*?*/ cc = operand1 as CompileTimeConstant;
      if (cc != null && cc.ValueIsPolymorphicCompileTimeConstant) {
        //If operand2 is unsigned, we want cc to prefer binding to unsigned types during overload resolution.
        //For example, 1 << 2u, whould result in (unsigned)4, not (signed)4.
        return new VccCompileTimeConstantWhoseSignDependsOnAnotherExpression(cc, operand2);
      }
      Parenthesis/*?*/ paren = operand1 as Parenthesis;
      if (paren != null)
        operand1 = new Parenthesis(this.ProvideSignBiasIfNeeded(paren.ParenthesizedExpression, operand2), paren.SourceLocation);
      return operand1;
    }

    protected Expression ConvertToInt32(Expression expression) {
      return new VccCast(expression, this.GetTypeExpressionFor(TypeCode.Int32, expression.SourceLocation), expression.SourceLocation);
    }

    protected Expression ParseComplexExpression(Token operator0, Expression operand1, Token operator1, Expression operand2, TokenSet followers)
      //^ requires this.currentToken != Token.EndOfFile;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
    restart:
      //^ assume this.currentToken != Token.EndOfFile; //OK because of precondition and state at point where control comes back here
      Token operator2 = this.currentToken;
      this.GetNextToken();
      if (operator2 == Token.SpecIs) {
        SourceLocationBuilder slb = new SourceLocationBuilder(operand2.SourceLocation);
        var type = this.ParseTypeExpression(followers);
        slb.UpdateToSpan(type.SourceLocation);
        operand2 = new CheckIfInstance(operand2, type, slb);
      } else {
        Expression operand3 = this.ParseUnaryExpression(operator2 == Token.Divide, followers);
        if (Parser.LowerPriority(operator1, operator2)) {
          if (TS.BinaryOperators[this.currentToken] && Parser.LowerPriority(operator2, this.currentToken)) {
            //Can't reduce just operand2 op2 operand3 because there is an op3 with priority over op2
            //^ assume this.currentToken != Token.EndOfFile; //follows from the switch logic
            operand2 = this.ParseComplexExpression(operator1, operand2, operator2, operand3, followers); //reduce complex expression
            //Now either at the end of the entire expression, or at an operator that is at the same or lower priority than op1
            //Either way, operand2 op2 operand3 op3 ... has been reduced to just operand2 and the code below will
            //either restart this procedure to parse the remaining expression or reduce operand1 op1 operand2 and return to the caller
          } else {
            //Reduce operand2 op2 operand3. There either is no further binary operator, or it does not take priority over op2.
            operand2 = this.AllocateBinaryExpression(operand2, operand3, operator2);
            //The code following this will reduce operand1 op1 operand2 and return to the caller
          }
        } else {
          operand1 = this.AllocateBinaryExpression(operand1, operand2, operator1);
          operand2 = operand3;
          operator1 = operator2;
        }
      }
      //At this point either operand1 op1 operand2 has been reduced, or operand2 op2 operand3 .... has been reduced, so back to just two operands
      if (TS.BinaryOperators[this.currentToken] &&
          (operator0 == Token.None || Parser.LowerPriority(operator0, this.currentToken))) {
            //The caller is not prepared to deal with the current token, go back to the start of this routine and consume some more tokens
            goto restart;
      } else {
          return this.AllocateBinaryExpression(operand1, operand2, operator1);
      }
    }

    /// <summary>
    /// returns true if opnd1 operator1 opnd2 operator2 opnd3 implicitly brackets as opnd1 operator1 (opnd2 operator2 opnd3)
    /// TODO: turn this mess into a table-driven function!!!
    /// </summary>

    private class OperatorPrecedence
    {
      public readonly int Precendence;
      public readonly bool IsLeftAssociative;

      public OperatorPrecedence(int precedence, bool isLeftAssociative) {
        this.Precendence = precedence;
        this.IsLeftAssociative = isLeftAssociative;
      }

      public OperatorPrecedence(int precedence) 
        :this(precedence, true) {
      }
    }

    private static Dictionary<Token, OperatorPrecedence> operatorPrecedences;

    private static void InitOperatorPrecedences() {
      Dictionary<Token, OperatorPrecedence> precedences = new Dictionary<Token, OperatorPrecedence>();
      precedences[Token.Divide] = precedences[Token.Multiply] = precedences[Token.Remainder] = new OperatorPrecedence(10);
      precedences[Token.Plus] = precedences[Token.Subtract] = new OperatorPrecedence(20);
      precedences[Token.LeftShift] = precedences[Token.RightShift] = new OperatorPrecedence(30);
      precedences[Token.GreaterThan] = precedences[Token.GreaterThanOrEqual] = precedences[Token.LessThan] = precedences[Token.LessThanOrEqual] = new OperatorPrecedence(40);
      precedences[Token.SpecIs] = new OperatorPrecedence(40);
      precedences[Token.SetIntersection] = new OperatorPrecedence(40);
      precedences[Token.SetDifference] = new OperatorPrecedence(41);
      precedences[Token.SetUnion] = new OperatorPrecedence(42);
      precedences[Token.SetIn] = precedences[Token.SetIn0] = new OperatorPrecedence(43);
      precedences[Token.Equal] = precedences[Token.NotEqual] = new OperatorPrecedence(50);
      precedences[Token.BitwiseAnd] = new OperatorPrecedence(60);
      precedences[Token.BitwiseXor] = new OperatorPrecedence(61);
      precedences[Token.BitwiseOr] = new OperatorPrecedence(62);
      precedences[Token.LogicalAnd] = new OperatorPrecedence(70);
      precedences[Token.LogicalOr] = new OperatorPrecedence(71);
      precedences[Token.Explies] = new OperatorPrecedence(72);
      precedences[Token.Implies] = new OperatorPrecedence(73, false);
      precedences[Token.IfAndOnlyIf] = new OperatorPrecedence(74);
      operatorPrecedences = precedences;
    }

    protected static bool LowerPriority(Token operator1, Token operator2) {
      if (operatorPrecedences == null) InitOperatorPrecedences();
      OperatorPrecedence prec1, prec2;
      if (operatorPrecedences.TryGetValue(operator1, out prec1)) {
        if (operatorPrecedences.TryGetValue(operator2, out prec2)) {
          if (prec1.Precendence < prec2.Precendence) return false;
          else if (prec1.Precendence > prec2.Precendence) return true;
          else if (operator1 == operator2 && !prec1.IsLeftAssociative) return true;
          else return false;
        } else return false; ; // should never happen!
      } else return false; // should never happen!
    }

    protected Expression ParseConditional(Expression condition, TokenSet followers) 
      //^ requires this.currentToken == Token.Conditional;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      this.GetNextToken();
      SourceLocationBuilder slb = new SourceLocationBuilder(condition.SourceLocation);
      Expression resultIfTrue = this.ParseExpression(true, false, followers|Token.Colon);
      Expression resultIfFalse;
      if (this.currentToken == Token.Colon) {
        this.GetNextToken();
        resultIfFalse = this.ParseExpression(followers);
      } else {
        this.Skip(Token.Colon); //gives appropriate error message
        if (!followers[this.currentToken])
          //Assume that only the : is missing. Go ahead as if it were specified.
          resultIfFalse = this.ParseExpression(followers);
        else
          resultIfFalse = this.ParseDummyExpression();
      }
      slb.UpdateToSpan(resultIfFalse.SourceLocation);
      Expression result = new VccConditional(condition, resultIfTrue, resultIfFalse, slb);
      this.SkipTo(followers);
      return result;
    }

    protected Expression ParseDummyExpression() {
      ISourceLocation currentLocation = this.scanner.SourceLocationOfLastScannedToken;
      return new CompileTimeConstant(null, currentLocation.SourceDocument.GetSourceLocation(currentLocation.StartIndex, 0));
    }

    protected Expression ParseUnaryExpression(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      return this.ParseUnaryExpression(false, followers);
    }

    protected Expression ParseUnaryExpression(bool allowInitializer, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      switch (this.currentToken) {
        case Token.AddOne:
        case Token.SubtractOne: 
        case Token.BitwiseAnd:
        case Token.Multiply:
        case Token.Plus:
        case Token.Subtract:
        case Token.BitwiseNot:
        case Token.LogicalNot: 
          SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
          Token operatorToken = this.currentToken;
          this.GetNextToken();
          Expression operand;
          if (this.currentToken == Token.LeftParenthesis)
            operand = this.ParseCastExpression(followers);
          else
            operand = this.ParseUnaryExpression(followers);
          slb.UpdateToSpan(operand.SourceLocation);
          Expression result = AllocateUnaryExpression(operatorToken, operand, slb);
          //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
          return result;

        case Token.Exists:
        case Token.Forall:
          return this.ParseQuantifier(followers);

        case Token.Lambda:
          Expression lambda = this.ParseQuantifier(followers|Token.LeftBracket);
          return ParsePostFix(lambda, followers);

        case Token.LeftParenthesis:
          return this.ParseCastExpression(followers);

        case Token.Specification:
          return this.ParseSpecCastExpression(followers);

        case Token.AlignOf:
          return this.ParseAlignOf(followers);

        case Token.Sizeof: 
          return this.ParseSizeof(followers);

        case Token.LeftBrace:
          if (allowInitializer || this.InSpecCode) return this.ParseInitializer(followers);
          else goto default;

        default:
          return this.ParsePostfixExpression(followers);
      }
    }

    protected static Expression AllocateUnaryExpression(Token operatorToken, Expression operand, SourceLocationBuilder slb)
      //^ requires operatorToken == Token.AddOne || operatorToken == Token.BitwiseAnd || operatorToken == Token.BitwiseNot || operatorToken == Token.LogicalNot || 
      //^ operatorToken == Token.Multiply || operatorToken == Token.Plus || operatorToken == Token.Subtract || operatorToken == Token.SubtractOne;
    {
      switch (operatorToken) {
        case Token.AddOne: return new VccPrefixIncrement(new TargetExpression(operand), slb);
        case Token.BitwiseNot: return new OnesComplement(operand, slb);
        case Token.LogicalNot: return new LogicalNot(operand, slb);
        case Token.Multiply: return new VccAddressDereference(operand, slb);
        case Token.Plus: return new UnaryPlus(operand, slb);
        case Token.Subtract: return new UnaryNegation(operand, slb);
        case Token.SubtractOne: return new VccPrefixDecrement(new TargetExpression(operand), slb);
        case Token.BitwiseAnd: 
          VccPointerScopedName pointerScopedName = operand as VccPointerScopedName;
          if (pointerScopedName != null)
            return new VccPointerScopedName(new VccAddressOf(new AddressableExpression(pointerScopedName.Qualifier), slb), pointerScopedName.SimpleName, pointerScopedName.SourceLocation);
          else 
            return new VccAddressOf(new AddressableExpression(operand), slb);
        default:
          //^ assume false;
          goto case Token.AddOne;
      }
    }

    protected Expression ParseTypeArgumentList(Expression expression, TokenSet followers) {
      Scanner.Snapshot snapshot = scanner.MakeSnapshot();
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      slb.UpdateToSpan(expression.SourceLocation);
      this.GetNextToken();
      if (this.CurrentTokenStartsTypeExpression()) {
        TokenSet followersOrCommaOrGreaterThan = followers|Token.Comma|Token.GreaterThan;
        List<TypeExpression> arguments = new List<TypeExpression>();
        if (this.currentToken != Token.GreaterThan) {
          TypeExpression argument = this.ParseTypeExpression(followersOrCommaOrGreaterThan);
          arguments.Add(argument);
          while (this.currentToken == Token.Comma) {
            this.GetNextToken();
            argument = this.ParseTypeExpression(followersOrCommaOrGreaterThan);
            arguments.Add(argument);
          }
        }
        arguments.TrimExcess();
        this.SkipOverTo(Token.GreaterThan, followers);
        slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        return new GenericInstanceExpression(expression, arguments, slb);
      }
      scanner.RevertToSnapshot(snapshot);
      this.currentToken = Token.LessThan;
      return expression;
      
    }

    protected Expression ParsePostfixExpression(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      //TODO: first try to parse an initializer
      Expression expression = this.ParsePrimaryExpression(followers|Token.LeftBracket|Token.LeftParenthesis|Token.Dot|Token.Arrow|Token.ScopeResolution|Token.AddOne|Token.SubtractOne);
      return this.ParsePostFix(expression, followers);
    }

    protected Expression ParsePostFix(Expression expression, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      for (; ; ) {
        switch (this.currentToken) {
          case Token.AddOne:
            SourceLocationBuilder slb = new SourceLocationBuilder(expression.SourceLocation);
            slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
            this.GetNextToken();
            expression = new VccPostfixIncrement(new TargetExpression(expression), slb);
            break;
          case Token.SubtractOne:
            slb = new SourceLocationBuilder(expression.SourceLocation);
            slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
            this.GetNextToken();
            expression = new VccPostfixDecrement(new TargetExpression(expression), slb);
            break;
          case Token.LessThan:
            Expression exp = this.ParseTypeArgumentList(expression, followers);
            if (exp == expression) goto default;
            expression = exp;
            break;
          case Token.Arrow:
          case Token.ScopeResolution:
          case Token.Dot:
          case Token.LeftBracket:
            expression = this.ParseIndexerCallOrSelector(expression, followers|Token.AddOne|Token.SubtractOne);
            break;
          case Token.LeftParenthesis:
            //TODO: try to parse an initializer
            goto case Token.Arrow;
          default:
            return expression;
        }
      }
    }

    protected Expression ParsePrimaryExpression(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      ISourceLocation sctx = this.scanner.SourceLocationOfLastScannedToken;
      Expression expression = new DummyExpression(sctx);

      switch (this.currentToken) {
        case Token.Identifier:
          SimpleName name = this.ParseSimpleName(followers|Token.Dot);
          if (name.Name.Value == "__this")
            expression = new VccThisReference(name.SourceLocation);
          else if (this.resultIsAKeyword && name.Name.Value == "\\result")
            expression = new VccReturnValue(name.SourceLocation);
          else
            expression = name;
          break;
        case Token.IntegerLiteral:
          expression = this.ParseIntegerLiteral();
          break;
        case Token.OctalLiteral:
          expression = this.ParseOctalLiteral();
          break;
        case Token.HexLiteral:
          expression = this.ParseHexLiteral();
          break;
        case Token.RealLiteral:
          expression = this.ParseRealLiteral();
          break;
        case Token.HexFloatLiteral:
          expression = this.ParseHexFloatLiteral();
          break;
        case Token.SByteLiteral:
          expression = new CompileTimeConstant((sbyte)this.scanner.charLiteralValue, false, sctx);
          this.GetNextToken();
          break;
        case Token.CharLiteral:
          expression = new CompileTimeConstant((char)this.scanner.charLiteralValue, false, sctx);
          this.GetNextToken();
          break;
        case Token.MultiCharLiteral:
          expression = new CompileTimeConstant(this.scanner.charLiteralValue, false, sctx);
          this.GetNextToken();
          break;
        case Token.SByteStringLiteral:
          expression = this.ParseSbyteStringLiteral();
          break;
        case Token.StringLiteral:
          expression = new CompileTimeConstant(this.scanner.GetString(), false, sctx);
          this.GetNextToken();
          break;
        case Token.LeftParenthesis:
          expression = this.ParseParenthesizedExpression(followers);
          break;
        case Token.Old:
          expression = this.ParseExpressionWithParens(followers, (expr, sl) => new OldValue(expr, sl));
          break;
        case Token.Unchecked:
          expression = this.ParseExpressionWithParens(followers, (expr, sl) => new UncheckedExpression(expr, sl));
          break;
          // the following ones will only occur in the next syntax
        case Token.Result:
          if (this.resultIsAKeyword) {
            expression = new VccReturnValue(this.GetSourceLocationBuilderForLastScannedToken());
          } else {
            expression = new DummyExpression(this.GetSourceLocationBuilderForLastScannedToken());
            this.HandleError(Error.ResultNotAllowedHere);
          }
          this.GetNextToken();
          break;
        case Token.This:
          expression = new VccThisReference(this.GetSourceLocationBuilderForLastScannedToken());
          this.GetNextToken();
          break;
        default:
          if (TS.InfixOperators[this.currentToken]) {
            this.HandleError(Error.InvalidExprTerm, this.scanner.GetTokenSource());
            //^ assume this.currentToken != Token.EndOfFile; //should not be a member of InfixOperators
            this.GetNextToken();
          } else
            this.SkipTo(followers | TS.PrimaryStart, Error.InvalidExprTerm, this.scanner.GetTokenSource());
          if (TS.PrimaryStart[this.currentToken]) return this.ParsePrimaryExpression(followers);
          break;
      }
      this.SkipTo(followers);
      return expression;
    }

    protected Expression ParseSbyteStringLiteral()
      //^ requires this.currentToken == Token.SByteStringLiteral;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      StringBuilder sb = new StringBuilder();
      string/*?*/ str = this.scanner.GetString();
      if (str != null) sb.Append(str);
      this.GetNextToken();
      while (this.currentToken == Token.SByteStringLiteral) {
        slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        str = this.scanner.GetString();
        if (str != null) sb.Append(str);
        this.GetNextToken();
      }
      return new VccByteStringLiteral(sb.ToString(), slb);
    }

    protected Expression ParseCastExpression(TokenSet followers)
      //^ requires this.currentToken == Token.LeftParenthesis;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      if (this.CurrentTokenStartsTypeExpression()) {
        TypeExpression targetType = this.ParseTypeExpression(followers|Token.RightParenthesis);
        this.Skip(Token.RightParenthesis);
        Expression valueToCast = this.ParseUnaryExpression(true, followers);
        VccInitializerBase initializer = valueToCast as VccInitializerBase;
        if (initializer != null)
          initializer.structureTypeExpression = targetType as VccNamedTypeExpression; // null does not hurt here
        slb.UpdateToSpan(valueToCast.SourceLocation);
        Expression expression = new VccCast(valueToCast, targetType, slb);
        return expression;
      }else{
        Expression expression = this.ParseExpression(true, false, followers|Token.RightParenthesis|Token.LeftBracket|Token.LeftParenthesis|Token.Dot|Token.Arrow|Token.ScopeResolution|Token.AddOne|Token.SubtractOne);
        slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        expression = new Parenthesis(expression, slb);
        this.SkipOverTo(Token.RightParenthesis, followers|Token.LeftBracket|Token.LeftParenthesis|Token.Dot|Token.Arrow|Token.ScopeResolution|Token.AddOne|Token.SubtractOne);
        return this.ParsePostFix(expression, followers);
      }
    }

    protected bool CurrentTokenStartsDeclaration() {
      return CurrentTokenStartsXHelper(TS.DeclarationStart);
    }

    protected bool CurrentTokenStartsTypeExpression() {
      return CurrentTokenStartsXHelper(TS.TypeStart);
    }

    private bool CurrentTokenStartsXHelper(TokenSet ts) {
      if (!ts[this.currentToken]) return false;               // not even a superficial match
      if (this.currentToken != Token.Identifier) return true; // non-identifier must start type    
      TypeExpression teDummy;
      return IdIsTypeDefNameOrTemplateParameter(this.scanner.GetIdentifierString(), out teDummy);    // identifiers need closer inspection
    }

    private bool IdIsTypeDefNameOrTemplateParameter(string id, out TypeExpression typeDefExpression) {
      bool localNameIsParOrDecl;
      typeDefExpression = null;
      if (this.locallyDefinedNames.TryGetValue(id, out localNameIsParOrDecl))
        return !localNameIsParOrDecl;                                                // when locally defined, then only type parameters match
      TypedefDeclaration typedefDecl;
      // non-local - see if it is a known typedef'ed name
      if (this.typedefs.TryGetValue(id, out typedefDecl)) {
        typeDefExpression = typedefDecl.Type;
        return true;
      }
      return false;
    }

    protected Expression ParseQualifiedName(Expression qualifier, TokenSet followers)
      //^ requires this.currentToken == Token.Arrow || this.currentToken == Token.Dot || this.currentToken == Token.ScopeResolution;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      Token tok = this.currentToken;
      SourceLocationBuilder slb = new SourceLocationBuilder(qualifier.SourceLocation);
      this.GetNextToken();
      VccSimpleName name = this.ParseSimpleName(followers);
      slb.UpdateToSpan(name.SourceLocation);
      Expression result;
      if (tok == Token.Arrow)
        result = new VccPointerQualifiedName(qualifier, name, slb);
      else if (tok == Token.ScopeResolution)
        result = new VccPointerScopedName(qualifier, name, slb);
      else {
        //^ assert tok == Token.Dot 
        result = new VccQualifiedName(qualifier, name, slb);
      }
      //^ assume followers[this.currentToken] || this.currentToken == Token.EndOfFile;
      return result;
    }

    protected IEnumerable<IEnumerable<Expression>> ParseQuantifierTriggers(TokenSet followers) {
      List<IEnumerable<Expression>> result = new List<IEnumerable<Expression>>();
      while (this.currentToken == Token.LeftBrace) {
        IEnumerable<Expression>/*?*/ trigger = this.ParseQuantifierTrigger(followers);
        if (trigger != null) result.Add(trigger);
      }
      result.TrimExcess();
      return result.AsReadOnly();
    }

    protected IEnumerable<Expression>/*?*/ ParseQuantifierTrigger(TokenSet followers) 
      //^ requires this.currentToken == Token.LeftBrace;
    {
      this.GetNextToken();
      if (this.currentToken == Token.RightBrace) return null;
      List<Expression> result = new List<Expression>();
      TokenSet followersOrCommaOrRightBrace = followers | TS.CommaOrRightBrace;
      while (this.currentToken != Token.RightBrace) {
        Expression e = this.ParseLabeledExpression(followersOrCommaOrRightBrace, false);
        result.Add(e);
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken();
      }
      this.SkipOverTo(Token.RightBrace, followers | Token.LeftBrace);
      result.TrimExcess();
      return result.AsReadOnly();
    }

    protected List<LocalDeclarationsStatement> ParseQuantifierBoundVariables(TokenSet followers) {
      List<LocalDeclarationsStatement> result = new List<LocalDeclarationsStatement>();
      TokenSet followersOrTypeStart = followers | TS.TypeStart;
      while (this.CurrentTokenStartsTypeExpression()) {
        List<Specifier> specifiers = this.ParseSpecifiers(null, null, null, followers|Token.Semicolon);
        List<LocalDeclaration> declarations = new List<LocalDeclaration>(1);
        Declarator declarator = this.ParseDeclaratorInQuantifier(followers | Token.Comma | Token.Semicolon);
        TypeExpression type = this.GetTypeExpressionFor(specifiers, declarator, FixedSizeArrayContext.AsLocal);
        SourceLocationBuilder slb = new SourceLocationBuilder(type.SourceLocation);
        slb.UpdateToSpan(declarator.SourceLocation);
        declarations.Add(new LocalDeclaration(false, false, declarator.Identifier, null, slb));
        while (this.currentToken == Token.Comma) {
          this.GetNextToken();
          declarator = this.ParseDeclarator(null, followers|Token.Comma, true);
          slb.UpdateToSpan(declarator.SourceLocation);
          declarations.Add(new LocalDeclaration(false, false, declarator.Identifier, null, slb));
        }
        LocalDeclarationsStatement locDecls = new LocalDeclarationsStatement(false, false, false, type, declarations, slb);
        result.Add(locDecls);
        this.SkipSemiColon(followersOrTypeStart);
      }
      return result;
    }

    protected Expression ParseAlignOf(TokenSet followers)
    //^ requires this.currentToken == Token.AlignOf;
    //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Expression result;
      bool skipRightParenthesis = false;
      if (this.currentToken == Token.LeftParenthesis) {
        this.GetNextToken();
        skipRightParenthesis = true;
      }
      TypeExpression typeExpression = this.ParseTypeExpression(followers | Token.RightParenthesis);
      slb.UpdateToSpan(typeExpression.SourceLocation);
      result = new VccAlignOf(typeExpression, slb);
      if (skipRightParenthesis) {
        slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        this.Skip(Token.RightParenthesis);
      }
      this.SkipTo(followers);
      return result;
    }

    protected Expression ParseSizeof(TokenSet followers)
      //^ requires this.currentToken == Token.Sizeof;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      Expression result;
      bool seenLeftParenthesis = false;
      if (this.currentToken == Token.LeftParenthesis) {
        this.GetNextToken();
        seenLeftParenthesis = true;
      }
      Expression expression;
      if (this.CurrentTokenStartsTypeExpression()) {
        // C standard 6.5.3.4 - '... parenthesize name of a type ...'
        if (!seenLeftParenthesis) this.HandleError(Error.UnexpectedToken, this.scanner.GetTokenSource()); 
        expression = this.ParseTypeExpression(followers | Token.RightParenthesis);
      } else
        expression = this.ParseExpression(followers | Token.RightParenthesis);
      slb.UpdateToSpan(expression.SourceLocation);
      result = new VccSizeOf(expression, slb);
      if (seenLeftParenthesis) {
        slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
        this.Skip(Token.RightParenthesis);
      }
      this.SkipTo(followers);
      return result;
    }

    protected TypeExpression ParseTypeExpression(TokenSet followers)
      //^ requires this.currentToken == Token.LeftParenthesis;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      List<INamespaceDeclarationMember> members = new List<INamespaceDeclarationMember>();
      List<Specifier> specifiers = this.ParseSpecifiers(members, null, null, followers|Token.Multiply|Token.RightParenthesis|Token.LeftBracket);
      Declarator declarator = this.ParseDeclarator(followers);
      slb.UpdateToSpan(declarator.SourceLocation);
      TypeExpression type = this.GetTypeExpressionFor(specifiers, null);
      type = HandleTypeQualifiersForPointer(specifiers, type, declarator);
      type = this.GetTypeExpressionFor(type, declarator);
      this.SkipTo(followers);
      return type;
    }

    protected Expression ParseIndexerCallOrSelector(Expression expression, TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      while (true) {
        switch (this.currentToken) {
          case Token.Arrow:
          case Token.ScopeResolution:
          case Token.Dot:
            expression = this.ParseQualifiedName(expression, followers|Token.Arrow|Token.ScopeResolution|Token.Dot|Token.LeftBracket|Token.LeftParenthesis|Token.LessThan);
            break;
          case Token.LeftBracket:
            expression = this.ParseIndexer(expression, followers|Token.Arrow|Token.ScopeResolution|Token.Dot|Token.LeftBracket|Token.LeftParenthesis|Token.LessThan);
            break;
          case Token.LeftParenthesis:
            expression = this.ParseMethodCall(expression, followers|Token.Arrow|Token.ScopeResolution|Token.Dot|Token.LeftBracket|Token.LeftParenthesis|Token.LessThan);
            break;
          default: 
            this.SkipTo(followers);
            return expression;
        }
      }
    }

    protected Expression ParseMethodCall(Expression method, TokenSet followers)
      //^ requires this.currentToken == Token.LeftParenthesis;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SimpleName methodName = method as SimpleName;
      if (methodName != null && methodName.Name.Value == "_vcc_atomic_op")
        return ParseAtomicOp(method, followers);
      SourceLocationBuilder slb = new SourceLocationBuilder(method.SourceLocation);
      return new VccMethodCall(method, this.ParseArgumentList(slb, followers).AsReadOnly(), slb);
    }

    protected Expression ParseAtomicOp(Expression method, TokenSet followers) {
      SourceLocationBuilder slb = new SourceLocationBuilder(method.SourceLocation);
      bool saveResultIsAKeyWord = this.resultIsAKeyword;
      this.resultIsAKeyword = true;
      var args = this.ParseArgumentList(slb, followers);
      this.resultIsAKeyword = saveResultIsAKeyWord;
      var atomicOp = new VccAtomicOp(method, args.AsReadOnly(), slb);
      var atomicOpBlock = new VccAtomicOpBlock(new List<Statement>(0), atomicOp, method.SourceLocation);
      return new BlockExpression(atomicOpBlock, atomicOp, method.SourceLocation);
    }

    protected void ParsePragma() 
      //^ requires this.currentToken == Token.Pragma;
    {
      //Just ignore the pragma for the time being.
      Token tok = this.scanner.GetNextToken(false, false);
      if (tok == Token.LeftParenthesis) {
        int count = 1;
        do {
          tok = this.scanner.GetNextToken(false, false);
          if (tok == Token.LeftParenthesis)
            count++;
          else if (tok == Token.RightParenthesis)
            count--;
        } while (count > 0);
        this.GetNextToken();
      }
    }


    protected Expression ParseArgumentExpression(TokenSet followers)
    {
      if (this.InSpecCode && this.currentToken == Token.Identifier && this.scanner.GetIdentifierString() == "out") {
        this.GetNextToken();
        var argExpr = this.ParseExpression(followers);
        var slb = new SourceLocationBuilder(argExpr.SourceLocation);
        return new VccOutArgument(new TargetExpression(argExpr), slb);
      } else 
        return this.ParseExpression(followers);
    }

    protected Indexer ParseIndexer(Expression indexedObject, TokenSet followers)
      //^ requires this.currentToken == Token.LeftBracket;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(indexedObject.SourceLocation);
      this.GetNextToken();
      List<Expression> indices = new List<Expression>();
      while (this.currentToken != Token.RightBracket) {
        Expression index = this.ParseExpression(followers|Token.Comma|Token.RightBracket);
        indices.Add(index);
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken(); // TODO: unreachable
      }
      indices.TrimExcess();
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      Indexer result = new VccIndexer(indexedObject, indices.AsReadOnly(), slb);
      this.SkipOverTo(Token.RightBracket, followers);
      return result;
    }

    protected Expression ParseParenthesizedExpression(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();
      if (this.currentToken == Token.LeftBrace) {
        Expression dummy = new DummyExpression(sctx);
        this.SkipTo(followers, Error.SyntaxError, "(");
        return dummy;
      }
      this.Skip(Token.LeftParenthesis);
      Expression result = this.ParseExpression(true, false, followers|Token.RightParenthesis|Token.Colon);
      this.SkipOverTo(Token.RightParenthesis, followers);
      return result;
    }

    protected Expression ParseOctalLiteral()
      //^ requires this.currentToken == Token.OctalLiteral;
    {
      string tokStr = this.scanner.GetTokenSource();
      SourceLocationBuilder ctx = this.GetSourceLocationBuilderForLastScannedToken();
      TypeCode tc = this.scanner.ScanNumberSuffix();
      ctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      CompileTimeConstant result;
      switch (tc) {
        case TypeCode.Single:
        case TypeCode.Double:
        case TypeCode.Decimal:
          this.HandleError(Error.ExpectedSemicolon);
          goto default;
        default:
          ulong ul = 0;
          foreach (char ch in tokStr){
            //^ assume '0' <= ch && ch <= '7'; //The scanner should not return a Token.OctalLiteral when this is not the case.
            ulong digit = (ulong)(ch - '0');
            //^ assume 0 <= digit && digit <= 7;
            ul = (ul << 3) + digit;
            if (ul > ulong.MaxValue-7) {
              this.HandleError(ctx, Error.IntOverflow);
              break;
            }
          }
          result = GetConstantOfSmallestIntegerTypeThatIncludes(ul, tc, ctx, true);
          break;
      }
      //^ assume this.currentToken == Token.OctalLiteral; //follows from the precondition
      this.GetNextToken();
      return result;
    }

    protected Expression ParseHexFloatLiteral() {
      throw new NotImplementedException("The method or operation is not implemented.");
    }

    protected CompileTimeConstant ParseHexLiteral()
      //^ requires this.currentToken == Token.HexLiteral;
    {
      string tokStr = this.scanner.GetTokenSource();
      //^ assume tokStr.StartsWith("0x") || tokStr.StartsWith("0X"); //The scanner should not return a Token.HexLiteral when this is not the case.
      SourceLocationBuilder ctx = this.GetSourceLocationBuilderForLastScannedToken();
      TypeCode tc = this.scanner.ScanNumberSuffix();
      ctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      CompileTimeConstant result;
      switch (tc) {
        case TypeCode.Single:
        case TypeCode.Double:
        case TypeCode.Decimal:
          this.HandleError(Error.ExpectedSemicolon);
          goto default;
        case TypeCode.Int64:
          long l;
          if (!Int64.TryParse(tokStr.Substring(2), System.Globalization.NumberStyles.HexNumber, System.Globalization.CultureInfo.InvariantCulture, out l)) {
            this.HandleError(ctx, Error.IntOverflow);
            l = 0;
          }
          result = new CompileTimeConstant(l, false, true, ctx);
          break;
          
        default:
          ulong ul;
          //^ assume tokStr.Length >= 2;
          if (!UInt64.TryParse(tokStr.Substring(2), System.Globalization.NumberStyles.HexNumber, System.Globalization.CultureInfo.InvariantCulture, out ul)) {
            this.HandleError(ctx, Error.IntOverflow);
            ul = 0;
          }
          result = GetConstantOfSmallestIntegerTypeThatIncludes(ul, tc, ctx, true);
          break;
      }
      //^ assume this.currentToken == Token.HexLiteral; //follows from the precondition
      this.GetNextToken();
      return result;
    }

    protected CompileTimeConstant ParseIntegerLiteral() 
      //^ requires this.currentToken == Token.IntegerLiteral;
    {
      string tokStr = this.scanner.GetTokenSource();
      SourceLocationBuilder ctx = this.GetSourceLocationBuilderForLastScannedToken();
      TypeCode tc = this.scanner.ScanNumberSuffix();
      ctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      CompileTimeConstant result;
      switch (tc) {
        case TypeCode.Single:
          float f;
          if (!Single.TryParse(tokStr, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out f)) {
            this.HandleError(ctx, Error.FloatOverflow);
            f = float.NaN;
          }
          result = new CompileTimeConstant(f, false, ctx);
          break;
        case TypeCode.Double:
          double d;
          if (!Double.TryParse(tokStr, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out d)) {
            this.HandleError(ctx, Error.FloatOverflow);
            d = double.NaN;
          }
          result = new CompileTimeConstant(d, false, ctx);
          break;
        case TypeCode.Decimal:
          decimal m;
          if (!decimal.TryParse(tokStr, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out m)) {
            this.HandleError(ctx, Error.IntOverflow);
            m = decimal.Zero;
          }
          result = new CompileTimeConstant(m, false, ctx);
          break;
        default:
          ulong ul;
          if (!UInt64.TryParse(tokStr, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out ul)) {
            this.HandleError(ctx, Error.IntOverflow);
            ul = 0;
          }
          result = GetConstantOfSmallestIntegerTypeThatIncludes(ul, tc, ctx, false);
          break;
      }
      //^ assume this.currentToken == Token.IntegerLiteral; //follows from the precondition
      this.GetNextToken();
      return result;
    }

    protected static CompileTimeConstant GetConstantOfSmallestIntegerTypeThatIncludes(ulong ul, TypeCode tc, SourceLocationBuilder ctx, bool hexOrOctal) {
      //TODO: there are more types than int and uint
      CompileTimeConstant result;
      if (ul <= int.MaxValue && tc == TypeCode.Empty)
        result = new CompileTimeConstant((int)ul, true, ctx);
      else if (ul <= uint.MaxValue && tc == TypeCode.Empty)
        result = new CompileTimeConstant((uint)ul, true, hexOrOctal, ctx);
      else if (ul <= byte.MaxValue && tc == TypeCode.Byte)
        result = new CompileTimeConstant((byte)ul, true, ctx);
      else if (ul <= byte.MaxValue && tc == TypeCode.SByte)
        result = new CompileTimeConstant((sbyte)ul, true, ctx);
      else if (ul <= uint.MaxValue && tc == TypeCode.UInt32)
        result = new CompileTimeConstant((uint)ul, true, ctx);
      else if (ul <= uint.MaxValue && tc == TypeCode.Int16)
        result = new CompileTimeConstant((short)ul, true, ctx);
      else if (ul <= uint.MaxValue && tc == TypeCode.UInt16)
        result = new CompileTimeConstant((ushort)ul, true, ctx);
      else if (ul <= uint.MaxValue && tc == TypeCode.Int32)
        result = new CompileTimeConstant((int)ul, true, ctx);
      else if (ul <= long.MaxValue && (tc == TypeCode.Empty || tc == TypeCode.Int64))
        result = new CompileTimeConstant((long)ul, tc == TypeCode.Empty, ctx);
      else
        result = new CompileTimeConstant(ul, tc == TypeCode.Empty, tc == TypeCode.Empty && hexOrOctal, ctx);
      return result;
    }

    protected static char[] nonZeroDigits = { '1', '2', '3', '4', '5', '6', '7', '8', '9' };

    protected CompileTimeConstant ParseRealLiteral()
      //^ requires this.currentToken == Token.RealLiteral;
    {
      string tokStr = this.scanner.GetTokenSource();
      SourceLocationBuilder ctx = this.GetSourceLocationBuilderForLastScannedToken();
      TypeCode tc = this.scanner.ScanNumberSuffix(false);
      ctx.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      CompileTimeConstant result;
      string/*?*/ typeName;
      switch (tc) {
        case TypeCode.Single:
          typeName = "float";
          float fVal;
          if (!Single.TryParse(tokStr, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out fVal))
            this.HandleError(ctx, Error.FloatOverflow, typeName);
          else if (fVal == 0f && tokStr.IndexOfAny(nonZeroDigits) >= 0)
            this.HandleError(ctx, Error.FloatOverflow, typeName);
          result = new CompileTimeConstant(fVal, false, ctx);
          break;
        case TypeCode.Empty:
        case TypeCode.Double:
          typeName = "double";
          double dVal;
          if (!Double.TryParse(tokStr, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out dVal))
            this.HandleError(ctx, Error.FloatOverflow, typeName);
          else if (dVal == 0d && tokStr.IndexOfAny(nonZeroDigits) >= 0)
            this.HandleError(ctx, Error.FloatOverflow, typeName);
          result = new CompileTimeConstant(dVal, tc == TypeCode.Empty, ctx);
          break;
        case TypeCode.Decimal:
          typeName = "decimal";
          decimal decVal;
          if (!Decimal.TryParse(tokStr, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out decVal))
            this.HandleError(ctx, Error.FloatOverflow, typeName);
          result = new CompileTimeConstant(decVal, false, ctx);
          break;
        default:
          this.HandleError(Error.ExpectedSemicolon);
          goto case TypeCode.Empty;
      }
      //^ assume this.currentToken == Token.RealLiteral; //follows from the precondition
      this.GetNextToken();
      return result;
    }

    protected SourceLocationBuilder GetSourceLocationBuilderForLastScannedToken() {
      return new SourceLocationBuilder(this.scanner.SourceLocationOfLastScannedToken);
    }

    protected void SkipOverTo(Token token, TokenSet followers)
      //^ requires token != Token.EndOfFile;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      this.Skip(token);
      this.SkipTo(followers);
    }

    protected void SkipOverTo(Token token, TokenSet followers, bool specKeywordExpected)
      //^ requires token != Token.EndOfFile;
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      this.Skip(token, specKeywordExpected);
      this.SkipTo(followers, Error.None);
    }

    protected void Skip(Token token) {
      this.Skip(token, false);
    }

    protected void Skip(Token token, bool specKeywordExpected)
      //^ requires token != Token.EndOfFile;
    {
      if (this.currentToken == token)
        this.GetNextToken(specKeywordExpected);
      else {
        switch (token) {
          case Token.Colon: this.HandleError(Error.SyntaxError, ":"); break;
          case Token.Identifier: this.HandleError(Error.ExpectedIdentifier); break;
          case Token.LeftBrace: this.HandleError(Error.ExpectedLeftBrace); break;
          case Token.LeftParenthesis: this.HandleError(Error.SyntaxError, "("); break;
          case Token.RightBrace: this.HandleError(Error.ExpectedRightBrace); break;
          case Token.RightBracket: this.HandleError(Error.ExpectedRightBracket); break;
          case Token.RightParenthesis: this.HandleError(Error.ExpectedRightParenthesis); break;
          case Token.Semicolon: this.HandleError(Error.ExpectedSemicolon); break;
          default: this.HandleError(Error.UnexpectedToken, this.scanner.GetTokenSource()); break;
        }
      }
    }


    protected void SkipSemiColon(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (this.currentToken == Token.Semicolon) {
        while (this.currentToken == Token.Semicolon) {
          this.GetNextToken();
        }
        this.SkipTo(followers|Token.EndOfFile);
      } else if (this.currentToken == Token.EndOfFile) {
        return;
      } else {
        this.Skip(Token.Semicolon);
        while (!this.scanner.TokenIsFirstAfterLineBreak && this.currentToken != Token.Semicolon && this.currentToken != Token.RightBrace && this.currentToken != Token.EndOfFile
          && (this.currentToken != Token.LeftBrace || !followers[Token.LeftBrace]))
          this.GetNextToken();
        if (this.currentToken == Token.Semicolon) 
          this.GetNextToken();
        this.SkipTo(followers|Token.EndOfFile);
      }
    }

    protected void SkipTo(TokenSet followers)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (followers[this.currentToken]) return;
      Error error = Error.InvalidExprTerm;
      this.HandleError(error, this.scanner.GetTokenSource());
      while (!followers[this.currentToken] && this.currentToken != Token.EndOfFile)
        this.GetNextToken();
    }

    protected void SkipTo(TokenSet followers, Error error, params string[] messages)
      //^ ensures followers[this.currentToken] || this.currentToken == Token.EndOfFile;
    {
      if (error != Error.None)
        this.HandleError(error, messages);
      while (!followers[this.currentToken] && this.currentToken != Token.EndOfFile)
        this.GetNextToken();
    }

    protected QualifiedName RootQualifiedNameFor(TypeCode typeCode, ISourceLocation sctx)
      //^ requires typeCode == TypeCode.Boolean || typeCode == TypeCode.Byte || typeCode == TypeCode.Double || typeCode == TypeCode.Int16 ||
      //^   typeCode == TypeCode.Int32 || typeCode == TypeCode.Int64 || typeCode == TypeCode.SByte || typeCode == TypeCode.Single ||
      //^   typeCode == TypeCode.UInt16 || typeCode == TypeCode.UInt32 || typeCode == TypeCode.UInt64 || typeCode == TypeCode.Empty; 
    {
      switch (typeCode) {
        case TypeCode.Boolean: return new QualifiedName(systemNs, this.GetSimpleNameFor("Boolean"), sctx);
        case TypeCode.Byte: return new QualifiedName(systemNs, this.GetSimpleNameFor("Byte"), sctx);
        case TypeCode.Double: return new QualifiedName(systemNs, this.GetSimpleNameFor("Double"), sctx);
        case TypeCode.Int16: return new QualifiedName(systemNs, this.GetSimpleNameFor("Int16"), sctx);
        case TypeCode.Int32: return new QualifiedName(systemNs, this.GetSimpleNameFor("Int32"), sctx);
        case TypeCode.Int64: return new QualifiedName(systemNs, this.GetSimpleNameFor("Int64"), sctx);
        case TypeCode.SByte: return new QualifiedName(systemNs, this.GetSimpleNameFor("SByte"), sctx);
        case TypeCode.Single: return new QualifiedName(systemNs, this.GetSimpleNameFor("Single"), sctx);
        case TypeCode.UInt16: return new QualifiedName(systemNs, this.GetSimpleNameFor("UInt16"), sctx);
        case TypeCode.UInt32: return new QualifiedName(systemNs, this.GetSimpleNameFor("UInt32"), sctx);
        case TypeCode.UInt64: return new QualifiedName(systemNs, this.GetSimpleNameFor("UInt64"), sctx);
        default:
          //^ assert typeCode == TypeCode.Empty;
          return new QualifiedName(systemNs, this.GetSimpleNameFor("Void"), sctx);
      }
    }

    protected VccSimpleName GetSimpleNameFor(string nameString) {
      IName name = this.GetNameFor(nameString);
      return new VccSimpleName(name, this.scanner.SourceLocationOfLastScannedToken);
    }

    protected static class TS
    {

      public static readonly TokenSet AddOneOrSubtractOne;
      public static readonly TokenSet AssignmentOperators;
      public static readonly TokenSet BinaryOperators;
      public static readonly TokenSet CaseOrDefaultOrRightBrace;
      public static readonly TokenSet CaseOrColonOrDefaultOrRightBrace;
      public static readonly TokenSet CastFollower;
      public static readonly TokenSet CommaOrRightBrace;
      public static readonly TokenSet ContractStart;
      public static readonly TokenSet DeclarationStart;
      public static readonly TokenSet DeclaratorStart;
      public static readonly TokenSet DeclaratorStartOrRightParenOrSemicolon;
      public static readonly TokenSet EndOfFile;
      public static readonly TokenSet InfixOperators;
      public static readonly TokenSet LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart;
      public static readonly TokenSet LoopContractStart;
      public static readonly TokenSet PrimaryStart;
      public static readonly TokenSet RightParenthesisOrSemicolon;
      public static readonly TokenSet SpecifierStart;
      public static readonly TokenSet SpecifierThatCombinesWithTypedefName;
      public static readonly TokenSet StatementStart;
      public static readonly TokenSet TypeStart;
      public static readonly TokenSet TypeOperator;
      public static readonly TokenSet UnaryStart;
      public static readonly TokenSet Term; //  Token belongs to first set for term-or-unary-operator (follows casts), but is not a predefined type.
      public static readonly TokenSet Predefined; // Token is a predefined type
      public static readonly TokenSet UnaryOperator; //  Token belongs to unary operator
      public static readonly TokenSet StructFollowers;

      static TS() {
        AddOneOrSubtractOne = new TokenSet();
        AddOneOrSubtractOne |= Token.AddOne;
        AddOneOrSubtractOne |= Token.SubtractOne;

        AssignmentOperators = new TokenSet();
        AssignmentOperators |= Token.AddAssign;
        AssignmentOperators |= Token.Assign;
        AssignmentOperators |= Token.BitwiseAndAssign;
        AssignmentOperators |= Token.BitwiseOrAssign;
        AssignmentOperators |= Token.BitwiseXorAssign;
        AssignmentOperators |= Token.DivideAssign;
        AssignmentOperators |= Token.LeftShiftAssign;
        AssignmentOperators |= Token.MultiplyAssign;
        AssignmentOperators |= Token.RemainderAssign;
        AssignmentOperators |= Token.RightShiftAssign;
        AssignmentOperators |= Token.SubtractAssign;

        BinaryOperators = new TokenSet();
        BinaryOperators |= Token.Plus;
        BinaryOperators |= Token.BitwiseAnd;
        BinaryOperators |= Token.BitwiseOr;
        BinaryOperators |= Token.BitwiseXor;
        BinaryOperators |= Token.Divide;
        BinaryOperators |= Token.Equal;
        BinaryOperators |= Token.Explies;
        BinaryOperators |= Token.GreaterThan;
        BinaryOperators |= Token.GreaterThanOrEqual;
        BinaryOperators |= Token.Implies;
        BinaryOperators |= Token.IfAndOnlyIf;
        BinaryOperators |= Token.LeftShift;
        BinaryOperators |= Token.LessThan;
        BinaryOperators |= Token.LessThanOrEqual;
        BinaryOperators |= Token.LogicalAnd;
        BinaryOperators |= Token.LogicalOr;
        BinaryOperators |= Token.Multiply;
        BinaryOperators |= Token.NotEqual;
        BinaryOperators |= Token.Remainder;
        BinaryOperators |= Token.RightShift;
        BinaryOperators |= Token.Subtract;
        BinaryOperators |= Token.SetDifference;
        BinaryOperators |= Token.SetIn;
        BinaryOperators |= Token.SetIn0;
        BinaryOperators |= Token.SpecIs;
        BinaryOperators |= Token.SetIntersection;
        BinaryOperators |= Token.SetUnion;

        CaseOrDefaultOrRightBrace = new TokenSet();
        CaseOrDefaultOrRightBrace |= Token.Case;
        CaseOrDefaultOrRightBrace |= Token.Default;
        CaseOrDefaultOrRightBrace |= Token.RightBrace;

        CaseOrColonOrDefaultOrRightBrace = CaseOrDefaultOrRightBrace;
        CaseOrColonOrDefaultOrRightBrace |= Token.Colon;

        CommaOrRightBrace = new TokenSet();
        CommaOrRightBrace |= Token.Comma;
        CommaOrRightBrace |= Token.RightBrace;

        ContractStart = new TokenSet();
        ContractStart |= Token.Decreases;
        ContractStart |= Token.Ensures;
        ContractStart |= Token.Reads;
        ContractStart |= Token.Requires;
        ContractStart |= Token.Writes;

        DeclarationStart = new TokenSet();
        DeclarationStart |= Token.Declspec;
        DeclarationStart |= Token.Axiom;
        DeclarationStart |= Token.Typedef;
        DeclarationStart |= Token.Extern;
        DeclarationStart |= Token.Static;
        DeclarationStart |= Token.Auto;
        DeclarationStart |= Token.Register;
        DeclarationStart |= Token.Const;
        DeclarationStart |= Token.Volatile;
        DeclarationStart |= Token.Inline;
        DeclarationStart |= Token.Void;
        DeclarationStart |= Token.Char;
        DeclarationStart |= Token.Short;
        DeclarationStart |= Token.Int;
        DeclarationStart |= Token.Int8;
        DeclarationStart |= Token.Int16;
        DeclarationStart |= Token.Int32;
        DeclarationStart |= Token.Int64;
        DeclarationStart |= Token.Long;
        DeclarationStart |= Token.Float;
        DeclarationStart |= Token.Double;
        DeclarationStart |= Token.Signed;
        DeclarationStart |= Token.Unsigned;
        DeclarationStart |= Token.Bool;
        //DeclarationStart |= Token.Complex;
        DeclarationStart |= Token.Struct;
        DeclarationStart |= Token.Template;
        DeclarationStart |= Token.Union;
        DeclarationStart |= Token.Enum;
        DeclarationStart |= Token.Identifier;
        DeclarationStart |= Token.Specification;

        DeclaratorStart = new TokenSet();
        DeclaratorStart |= Token.Multiply;
        DeclaratorStart |= Token.BitwiseXor;
        DeclaratorStart |= Token.Identifier;
        DeclaratorStart |= Token.LeftParenthesis;
        DeclaratorStart |= Token.Colon; // occurs in anonymous bitfields

        DeclaratorStartOrRightParenOrSemicolon = new TokenSet();
        DeclaratorStartOrRightParenOrSemicolon |= Token.RightParenthesis;
        DeclaratorStartOrRightParenOrSemicolon |= Token.Semicolon;
        DeclaratorStartOrRightParenOrSemicolon |= TS.DeclaratorStart;

        EndOfFile = new TokenSet();
        EndOfFile |= Token.EndOfFile;

        InfixOperators = new TokenSet();
        InfixOperators |= AssignmentOperators;
        InfixOperators |= BinaryOperators;
        InfixOperators |= Token.Conditional;
        InfixOperators |= Token.Comma;
        InfixOperators |= Token.Equal;
        InfixOperators |= Token.Arrow;
        InfixOperators |= Token.ScopeResolution;

        LoopContractStart = new TokenSet();
        LoopContractStart |= Token.Invariant;
        LoopContractStart |= Token.Writes;
        LoopContractStart |= Token.Decreases;

        PrimaryStart = new TokenSet();
        PrimaryStart |= Token.Identifier;
        PrimaryStart |= Token.IntegerLiteral;
        PrimaryStart |= Token.OctalLiteral;
        PrimaryStart |= Token.HexLiteral;
        PrimaryStart |= Token.RealLiteral;
        PrimaryStart |= Token.HexFloatLiteral;
        PrimaryStart |= Token.CharLiteral;
        PrimaryStart |= Token.StringLiteral;
        PrimaryStart |= Token.LeftParenthesis;
        PrimaryStart |= Token.Unchecked;
        PrimaryStart |= Token.This;
        PrimaryStart |= Token.Result;

        RightParenthesisOrSemicolon = new TokenSet();
        RightParenthesisOrSemicolon |= Token.RightParenthesis;
        RightParenthesisOrSemicolon |= Token.Semicolon;

        SpecifierThatCombinesWithTypedefName = new TokenSet();
        SpecifierThatCombinesWithTypedefName |= Token.Auto;
        SpecifierThatCombinesWithTypedefName |= Token.Register;
        SpecifierThatCombinesWithTypedefName |= Token.Static;
        SpecifierThatCombinesWithTypedefName |= Token.Extern;
        SpecifierThatCombinesWithTypedefName |= Token.Typedef;
        SpecifierThatCombinesWithTypedefName |= Token.Declspec;
        SpecifierThatCombinesWithTypedefName |= Token.Short;
        SpecifierThatCombinesWithTypedefName |= Token.Long;
        SpecifierThatCombinesWithTypedefName |= Token.Signed;
        SpecifierThatCombinesWithTypedefName |= Token.Unsigned;
        SpecifierThatCombinesWithTypedefName |= Token.Const;
        SpecifierThatCombinesWithTypedefName |= Token.Volatile;
        //SpecifierThatCombinesWithTypedefName |= Token.Asm;
        SpecifierThatCombinesWithTypedefName |= Token.Cdecl;
        SpecifierThatCombinesWithTypedefName |= Token.Fastcall;
        SpecifierThatCombinesWithTypedefName |= Token.Inline;
        SpecifierThatCombinesWithTypedefName |= Token.Stdcall;
        SpecifierThatCombinesWithTypedefName |= Token.Identifier;
        //SpecifierThatCombinesWithTypedefName |= Token.LeftBracket;
        SpecifierThatCombinesWithTypedefName |= Token.Multiply;
        SpecifierThatCombinesWithTypedefName |= Token.Unaligned;
        SpecifierThatCombinesWithTypedefName |= Token.ScopeResolution;

        StructFollowers = new TokenSet();
        StructFollowers |= Token.Identifier;
        StructFollowers |= Token.Semicolon;
        StructFollowers |= Token.Multiply;
        StructFollowers |= Token.BitwiseXor;

        TypeStart = new TokenSet();
        TypeStart |= Token.Identifier;
        TypeStart |= Token.Bool;
        TypeStart |= Token.Short;
        TypeStart |= Token.Int;
        TypeStart |= Token.Long;
        TypeStart |= Token.Char;
        TypeStart |= Token.Float;
        TypeStart |= Token.Double;
        TypeStart |= Token.LeftBracket;
        TypeStart |= Token.Void;
        TypeStart |= Token.Int8;
        TypeStart |= Token.Int16;
        TypeStart |= Token.Int32;
        TypeStart |= Token.Int64;
        TypeStart |= Token.Signed;
        TypeStart |= Token.Unsigned;
        TypeStart |= Token.W64;
        TypeStart |= Token.Struct;
        TypeStart |= Token.Union;
        TypeStart |= Token.Enum;
        TypeStart |= Token.Const;
        TypeStart |= Token.Volatile;
        TypeStart |= Token.Axiom;
        TypeStart |= Token.Unaligned;

        SpecifierStart = SpecifierThatCombinesWithTypedefName | TypeStart;
        //SpecifierStart |= Token.Asm;
        SpecifierStart |= Token.Cdecl;
        SpecifierStart |= Token.Fastcall;
        SpecifierStart |= Token.Inline;
        SpecifierStart |= Token.Stdcall;

        TypeOperator = new TokenSet();
        TypeOperator |= Token.LeftBracket;
        TypeOperator |= Token.Multiply;
        TypeOperator |= Token.Plus;
        TypeOperator |= Token.Conditional;
        TypeOperator |= Token.LogicalNot;
        TypeOperator |= Token.BitwiseAnd;

        UnaryStart = new TokenSet();
        UnaryStart |= Token.Identifier;
        UnaryStart |= Token.LeftParenthesis;
        UnaryStart |= Token.LeftBracket;
        UnaryStart |= Token.Lambda;
        UnaryStart |= Token.AddOne;
        UnaryStart |= Token.SubtractOne;
        UnaryStart |= Token.AlignOf;
        UnaryStart |= Token.Sizeof;
        UnaryStart |= Token.Forall;
        UnaryStart |= Token.Exists;
        UnaryStart |= Token.Old;
        UnaryStart |= Token.HexLiteral;
        UnaryStart |= Token.IntegerLiteral;
        UnaryStart |= Token.OctalLiteral;
        UnaryStart |= Token.StringLiteral;
        UnaryStart |= Token.CharLiteral;
        UnaryStart |= Token.RealLiteral;
        UnaryStart |= Token.Unchecked;
        UnaryStart |= Token.Bool;
        UnaryStart |= Token.Short;
        UnaryStart |= Token.Int;
        UnaryStart |= Token.Long;
        UnaryStart |= Token.Char;
        UnaryStart |= Token.Float;
        UnaryStart |= Token.Double;
        UnaryStart |= Token.Plus;
        UnaryStart |= Token.BitwiseNot;
        UnaryStart |= Token.LogicalNot;
        UnaryStart |= Token.Multiply;
        UnaryStart |= Token.Subtract;
        UnaryStart |= Token.AddOne;
        UnaryStart |= Token.SubtractOne;
        UnaryStart |= Token.BitwiseAnd;

        LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart = new TokenSet();
        LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart |= Token.LeftBrace;
        LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart |= Token.RightParenthesis;
        LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart |= Token.Semicolon;
        LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart |= TS.UnaryStart;

        StatementStart = new TokenSet();
        StatementStart |= TS.UnaryStart;
        StatementStart |= TS.DeclarationStart;
        StatementStart |= Token.LeftBrace;
        StatementStart |= Token.Semicolon;
        StatementStart |= Token.If;
        StatementStart |= Token.Switch;
        StatementStart |= Token.While;
        StatementStart |= Token.Do;
        StatementStart |= Token.For;
        StatementStart |= Token.While;
        StatementStart |= Token.Assert;
        StatementStart |= Token.Assume;
        StatementStart |= Token.Break;
        StatementStart |= Token.Continue;
        StatementStart |= Token.Goto;
        StatementStart |= Token.Return;
        StatementStart |= Token.Const;
        StatementStart |= Token.Void;
        StatementStart |= Token.Unaligned;
        StatementStart |= Token.Block;

        Term = new TokenSet();
        Term |= Token.AlignOf;
        Term |= Token.Sizeof;
        Term |= Token.Old;
        Term |= Token.Identifier;
        Term |= Token.IntegerLiteral;
        Term |= Token.RealLiteral;
        Term |= Token.StringLiteral;
        Term |= Token.CharLiteral;
        Term |= Token.LeftParenthesis;
        Term |= Token.Unchecked;

        Predefined = new TokenSet();
        Predefined |= Token.Bool;
        Predefined |= Token.Short;
        Predefined |= Token.Int;
        Predefined |= Token.Long;
        Predefined |= Token.Char;
        Predefined |= Token.Float;
        Predefined |= Token.Double;
        Predefined |= Token.Void;

        UnaryOperator = new TokenSet();
        UnaryOperator |= Token.AlignOf;
        UnaryOperator |= Token.Sizeof;
        UnaryOperator |= Token.BitwiseAnd;
        UnaryOperator |= Token.Plus;
        UnaryOperator |= Token.Subtract;
        UnaryOperator |= Token.Multiply;
        UnaryOperator |= Token.BitwiseNot;
        UnaryOperator |= Token.LogicalNot;
        UnaryOperator |= Token.AddOne;
        UnaryOperator |= Token.SubtractOne;

        CastFollower = new TokenSet();
        CastFollower |= Token.Identifier;
        CastFollower |= Token.LeftParenthesis;
        CastFollower |= Token.AddOne;
        CastFollower |= Token.SubtractOne;
        CastFollower |= Token.AlignOf;
        CastFollower |= Token.Sizeof;
        CastFollower |= Token.Old;
        CastFollower |= Token.HexLiteral;
        CastFollower |= Token.IntegerLiteral;
        CastFollower |= Token.StringLiteral;
        CastFollower |= Token.CharLiteral;
        CastFollower |= Token.RealLiteral;
        CastFollower |= Token.Bool;
        CastFollower |= Token.Short;
        CastFollower |= Token.Int;
        CastFollower |= Token.Long;
        CastFollower |= Token.Char;
        CastFollower |= Token.Float;
        CastFollower |= Token.Double;
        CastFollower |= Token.BitwiseNot;
        CastFollower |= Token.LogicalNot;
        CastFollower |= Token.Unchecked;
      }
    }



    protected struct TokenSet { 
      private ulong bits0, bits1, bits2;

      //^ [Pure]
      [System.Diagnostics.DebuggerNonUserCode]
      public static TokenSet operator |(TokenSet ts, Token t){
        TokenSet result = new TokenSet();
        int i = (int)t;
        if (i < 64){
          result.bits0 = ts.bits0 | (1ul << i);
          result.bits1 = ts.bits1;
          result.bits2 = ts.bits2;
        }else if (i < 128){
          result.bits0 = ts.bits0;
          result.bits1 = ts.bits1 | (1ul << (i-64));
          result.bits2 = ts.bits2;
        }else {
          result.bits0 = ts.bits0;
          result.bits1 = ts.bits1;
          result.bits2 = ts.bits2 | (1ul << (i-128));
        }
        return result;
      }

      //^ [Pure]
      [System.Diagnostics.DebuggerNonUserCode]
      public static TokenSet operator|(TokenSet ts1, TokenSet ts2) {
        TokenSet result = new TokenSet();
        result.bits0 = ts1.bits0 | ts2.bits0;
        result.bits1 = ts1.bits1 | ts2.bits1;
        result.bits2 = ts1.bits2 | ts2.bits2;
        return result;
      }

      internal bool this[Token t] {
        get {
          int i = (int)t;
          if (i < 64)
            return (this.bits0 & (1ul << i)) != 0;
          else if (i < 128)
            return (this.bits1 & (1ul << (i-64))) != 0;
          else
            return (this.bits2 & (1ul << (i-128))) != 0;
        }
      }

      //^ static TokenSet(){
        //^ int i = (int)Token.EndOfFile;
        //^ assert 0 <= i && i <= 191;
      //^ }
    }

  }

  internal class LexicalScope {
    public LexicalScope(LexicalScope/*?*/ parentScope, ISourceLocation sourceLocation) {
      this.parentScope = parentScope;
      this.sourceLocation = sourceLocation;
    }
    ISourceLocation sourceLocation;
    LexicalScope/*?*/ parentScope;

    public LexicalScope/*?*/ ParentScope {
      get {
        return parentScope;
      }
    }

    public string MangledName {
      get {
        return "sc" + this.GetHashCode();
      }
    }

    public string FullMangledName {
      get {
        if (parentScope == null) return "#" + this.MangledName;
        return parentScope.FullMangledName + "#" + this.MangledName;
      }
    }

    /// <summary>
    /// Accessor of a mangled name
    /// </summary>
    /// <param name="mangledName"></param>
    /// <returns></returns>
    public static string LexicalScopeOf(string mangledName) {
      int firstpos = mangledName.IndexOf('^');
      //^ assert firstpos >=0 ;
      try {
        return mangledName.Substring(firstpos + 1, mangledName.Length - firstpos - 1);
      } catch (ArgumentOutOfRangeException) {
        return "";
      }
    }

    /// <summary>
    /// When leaving an inner scope, pop the last segment that represents the inner scope
    /// out of the string encoding. 
    /// </summary>
    /// <param name="scopeString">String that represents the scope from which we are leaving, a "#" separated
    /// string where each segment represents a scope.</param>
    /// <returns>The string that encodes the parent scope. </returns>
    public static string/*!*/ PopScopeString(string/*!*/ scopeString) {
      int positionOfExpletive = scopeString.LastIndexOf('#');
      //^ assert positionOfExpletive >=0;
      if (positionOfExpletive > 0) {
        return scopeString.Substring(0, positionOfExpletive);
      } else {
        // TODO: report an error.
        return "";
      }
    }

    public static string MangledNameWithOuterLexcialScope(string mangledName) {
      string scope = LexicalScopeOf(mangledName);
      string outerscope = PopScopeString(scope);
      if (outerscope == "") {
        // assert mangledName.IndexOf('^') >=0;
        return mangledName.Substring(0, mangledName.IndexOf('^'));
      }
      string result = new string(mangledName.ToCharArray());
      result = result.Replace(scope, outerscope);
      return result;
    }

    public static string UnmangledName(string mangledName) {
      int pos = mangledName.IndexOf('^');
      if (pos < 0) return mangledName;

      return mangledName.Substring(0, pos);
    }
  }
}
