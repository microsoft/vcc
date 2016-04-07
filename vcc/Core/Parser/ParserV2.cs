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

namespace Microsoft.Research.Vcc.Parsing
{

  internal class ParserV2 : Parser
  {
     internal ParserV2(Compilation compilation, ISourceLocation sourceLocation, List<IErrorMessage> scannerAndParserErrors) 
    : base(compilation, sourceLocation, scannerAndParserErrors, isV2: true) {
    }

    override protected bool TryToGetBuiltInSpecTypeName(TypedefNameSpecifier typedefName, out TypeExpression result) {
      switch (typedefName.TypedefName.ToString()) {
        case "\\object":
          Expression typePtrRef = NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(this.nameTable, "TypedPtr");
          result = new VccNamedTypeExpression(typePtrRef);
          return true;
        case "\\integer":
          result = VccCompilationHelper.GetBigIntType(this.nameTable);
          return true;
        case "\\natural":
          result = VccCompilationHelper.GetBigNatType(this.nameTable);
          return true;
        case "\\objset":
          Expression objsetRef = NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(this.nameTable, "Objset");
          result = new VccNamedTypeExpression(objsetRef);
          return true;
        default:
          result = null;
          return false;
      }
    }

    override protected void ParseGlobalSpecDeclarationList(List<INamespaceDeclarationMember> members, List<ITypeDeclarationMember> globalMembers, TokenSet followers) {
      bool savedInSpecCode = this.SkipIntoSpecBlock();

      var id = "";
      if (this.currentToken == Token.Identifier)
        id = this.scanner.GetIdentifierString();

      if (id == "record") {
        // don't treat _(record identifier ...) as a specifier, it will be handled as type definition
        var snap = this.scanner.MakeSnapshot();
        this.GetNextToken();
        if (this.currentToken == Token.Identifier) {
          id = "";
        }
        this.scanner.RevertToSnapshot(snap);
        this.currentToken = Token.Identifier;
      }

      if (this.declspecExtensions.ContainsKey(id)) {
        this.ParseDeclarationWithSpecModifiers(members, globalMembers, followers, true, savedInSpecCode);
        return;
      }
      TokenSet followersOrDeclarationStart = followers | TS.DeclarationStart | Token.Semicolon | Token.RightParenthesis;
      while (TS.DeclarationStart[this.currentToken] || STS.Global[this.currentToken]) {
        switch (this.currentToken) {
          case Token.SpecAxiom:
            SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
            this.GetNextToken();
            var axiom = this.ParseExpression(followersOrDeclarationStart);
            slb.UpdateToSpan(axiom.SourceLocation);
            this.AddTypeInvariantToCurrent(new TypeInvariant(null, axiom, true, slb));
            break;
          case Token.SpecGhost:
            this.GetNextToken();
            this.ParseNonLocalDeclaration(members, globalMembers, followersOrDeclarationStart, true);
            break;
          case Token.SpecLogic:
            var specifier = new List<Specifier>(1) { new SpecDeclspecSpecifier("spec_macro", "", this.scanner.SourceLocationOfLastScannedToken) };
            this.GetNextToken();
            this.ParseNonLocalDeclaration(members, globalMembers, followersOrDeclarationStart, true, specifier);
            break;
          case Token.Identifier:
            switch (this.scanner.GetIdentifierString()) {
              case "datatype":
                this.GetNextToken();
                this.ParseDataTypeDefinition(members, globalMembers, followersOrDeclarationStart);
                break;
              case "type":
                this.GetNextToken();
                this.ParseTypeDefinition(members, globalMembers, followersOrDeclarationStart, isRecord: false);
                break;
              case "record":
                this.GetNextToken();
                this.ParseTypeDefinition(members, globalMembers, followersOrDeclarationStart, isRecord: true);
                break;
              default:
                this.ParseNonLocalDeclaration(members, globalMembers, followersOrDeclarationStart, true);
                break;
            }
            break;
          default:
            this.ParseNonLocalDeclaration(members, globalMembers, followersOrDeclarationStart, true);
            break;
        }
        this.SkipSemicolonsInSpecBlock(TS.DeclarationStart | STS.Global | Token.RightParenthesis);
      }

      this.SkipOutOfSpecBlock(savedInSpecCode, followers, true);
    }

    void UpdateForwardDeclaration(List<INamespaceDeclarationMember> members, VccStructuredTypeDeclaration tp)
    {
      var name = tp.Name.Name;
      for (var i = 0; i < members.Count; ++i) {
        var strct = members[i] as VccStructDeclaration;
        if (strct != null && strct.IsAbstractType && strct.Name.Name.Equals(name)) {
          members[i] = tp;
          return;
        }
      }
      members.Add(tp);
    }

    void ParseTypeDefinition(List<INamespaceDeclarationMember> members, List<ITypeDeclarationMember> globalMembers, TokenSet followers, bool isRecord)
    {
      var noSpecifiers = new Specifier[0];
      var name = this.ParseNameDeclaration(true);
      var loc = name.SourceLocation;
      var name0 = name.Name.Value;
      var mangledName = new VccNameDeclaration(this.GetNameFor("_vcc_math_type_" + name0), loc);

      var tpMembers = new List<ITypeDeclarationMember>();
      var strct = new VccStructDeclaration(mangledName, tpMembers, noSpecifiers, loc);
      var tp = new VccNamedTypeExpression(new VccSimpleName(mangledName, mangledName.SourceLocation));

      UpdateForwardDeclaration(members, strct);

      if (isRecord) {
        List<FieldDeclaration>/*?*/ savedSpecificationFields = this.currentSpecificationFields;
        List<TypeInvariant>/*?*/ savedTypeInvariants = this.currentTypeInvariants;
        this.currentSpecificationFields = null;
        this.currentTypeInvariants = null;
        SourceLocationBuilder sctx = this.GetSourceLocationBuilderForLastScannedToken();

        this.ParseRestOfTypeDeclaration(sctx, members, tp.Expression, tpMembers, followers);
        if (this.currentToken == Token.EndOfFile) {
          ISourceLocation errorLocation = this.scanner.SourceLocationOfLastScannedToken;
          this.HandleError(errorLocation, Error.MissingSemicolonAfterStruct, "end-of-file");
        }
        this.SkipTo(followers);
        this.AssociateTypeWithTypeContract(strct, this.currentSpecificationFields, this.currentTypeInvariants, this.InSpecCode);

        this.currentSpecificationFields = savedSpecificationFields;
        this.currentTypeInvariants = savedTypeInvariants;
      } else {
        strct.IsAbstractType = true;
        /*
        var fld = new FieldDefinition(new List<Specifier>(), 0, VccCompilationHelper.GetBigIntType(nameTable),
                                      new VccNameDeclaration(this.GetNameFor("_vcc_dummy"), loc), null, true, loc);
        tpMembers.Add(fld);
        */
      }

      var typedefDecl = new TypedefDeclaration(tp, name, loc);
      this.RegisterTypedef(name.Value, typedefDecl);
      globalMembers.Add(typedefDecl);
    }

    void ParseDataTypeDefinition(List<INamespaceDeclarationMember> members, List<ITypeDeclarationMember> globalMembers, TokenSet followers)
    {
      var noSpecifiers = new Specifier[0];
      var name = this.ParseNameDeclaration(true);
      var loc = name.SourceLocation;
      var mangledName = new VccNameDeclaration(this.GetNameFor("_vcc_math_type_" + name.Name.Value), loc);
      var ctornames = new List<FunctionDeclaration>();
      var strct = new VccDatatypeDeclaration(mangledName, new List<ITypeDeclarationMember>(), noSpecifiers, ctornames, loc);
      UpdateForwardDeclaration(members, strct);

      var tp = new VccNamedTypeExpression(new VccSimpleName(mangledName, mangledName.SourceLocation));

      var typedefDecl = new TypedefDeclaration(tp, name, loc);
      this.RegisterTypedef(name.Value, typedefDecl);
      globalMembers.Add(typedefDecl);

      this.Skip(Token.LeftBrace);

      for (; ; ) {
        SourceLocationBuilder scCtx = this.GetSourceLocationBuilderForLastScannedToken();
        if (this.currentToken != Token.Case)
        {
          this.Skip(this.currentToken == Token.RightBrace ? Token.RightBrace : Token.Case);
          break;
        }
        this.Skip(Token.Case);
        var fname = this.ParseNameDeclaration(true);
        var parmFollowers = followers | Token.RightBrace | Token.Case | Token.Semicolon;
        var parms0 = this.ParseParameterList(parmFollowers);
        this.Skip(Token.RightParenthesis);
        if (this.currentToken == Token.Semicolon)
          this.Skip(Token.Semicolon);
        bool acceptsExtraArguments;
        var parms1 = this.ConvertToParameterDeclarations(parms0, out acceptsExtraArguments);
        var specifiers = new[] { this.CreateAttribute("_vcc_internal__is_datatype_option", "", scCtx) };
        var fdecl = new FunctionDeclaration(acceptsExtraArguments,
                        specifiers, false, CallingConvention.C, TypeMemberVisibility.Public,
                        tp, fname, null, parms1, true, null, scCtx
                    );
        globalMembers.Add(fdecl);
        ctornames.Add(fdecl);
      }

      if (ctornames.Count == 0)
        this.HandleError(Error.EmptySwitch); //TODO use proper error
    }

    protected override void SkipSemiColonAfterDeclarationOrStatement(TokenSet followers) {
      if (this.InSpecCode && this.currentToken == Token.RightParenthesis) {
        // do nothing
      } else {
        if (this.currentToken == Token.Semicolon) {
          while (this.currentToken == Token.Semicolon) {
            this.GetNextToken(this.InSpecCode);
          }
          this.SkipTo(followers);
        } else {
          this.Skip(Token.Semicolon);
          while (!this.scanner.TokenIsFirstAfterLineBreak 
            && this.currentToken != Token.Semicolon 
            && this.currentToken != Token.RightBrace 
            && this.currentToken != Token.RightParenthesis 
            && this.currentToken != Token.EndOfFile 
            && (this.currentToken != Token.LeftBrace || !followers[Token.LeftBrace]))
            this.GetNextToken(this.InSpecCode);
          if (this.currentToken == Token.Semicolon)
            this.GetNextToken(this.InSpecCode);
          this.SkipTo(followers);
        }
      }
    }

    internal override void ParseCompilationUnit(GlobalDeclarationContainerClass globalContainer, List<INamespaceDeclarationMember> members) {
      base.ParseCompilationUnit(globalContainer, members);
      bool found = false;
      int typeStateFieldsKey = this.GetNameFor("\\TypeState").UniqueKey;
      foreach (var member in members) {
        if (member.Name.UniqueKey == typeStateFieldsKey) {
          var typeStateFieldsStruct = member as VccStructDeclaration;
          if (typeStateFieldsStruct != null) {
            ((VccCompilation)this.compilation).TypeStateFields = typeStateFieldsStruct;
            found = true;
            break;
          }
        }
      }
      if (!found) this.HandleError(Error.MissingIncludeOfVccH);
    }

    protected override bool ParseSpecTypeModifiers(List<Specifier> specifiers, TokenSet followers) {
      var snap = scanner.MakeSnapshot();
      bool savedInSpecCode = this.SkipIntoSpecBlock();

      if (IsSpecParameterStart(this.currentToken)) {
        this.LeaveSpecBlock(savedInSpecCode);
        scanner.RevertToSnapshot(snap);
        this.currentToken = Token.Specification;
        return false;
      }

      this.ParseSpecTypeModifierList(specifiers, followers);
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      return true;
    }

    private void ParseSpecTypeModifier(List<Specifier> specifiers, TokenSet followers) {
      if (this.currentToken == Token.Identifier) {
        string id = this.scanner.GetIdentifierString();
        string declspec;
        if (this.declspecExtensions.TryGetValue(id, out declspec)) {
          if (String.IsNullOrEmpty(declspec)) declspec = id;
          var loc = this.scanner.SourceLocationOfLastScannedToken;
          var argument = "";
          this.GetNextToken();
          if (this.currentToken == Token.StringLiteral || this.currentToken == Token.SByteStringLiteral) {
            argument = this.scanner.GetString();
            this.GetNextToken();
          }
          var specifier = new SpecDeclspecSpecifier(declspec, argument, loc);
          specifiers.Add(specifier);
        }
      } else if (this.currentToken == Token.Inline) {       
        specifiers.Add(new SpecDeclspecSpecifier("inline", "", this.scanner.SourceLocationOfLastScannedToken));
        this.GetNextToken();
      } else if (this.currentToken == Token.Colon) {
        var groupLabel = (VccLabeledExpression)this.ParseLabeledExpression(followers);
        specifiers.Add(this.CreateAttribute("in_group", groupLabel.Label.Name.Value, groupLabel.SourceLocation));
      }
      this.SkipTo(followers);
    }

    private void ParseSpecTypeModifierList(List<Specifier> specifiers, TokenSet followers) {
      while (this.currentToken != Token.RightParenthesis) {
        this.ParseSpecTypeModifier(specifiers, followers | Token.Comma | Token.RightParenthesis);
        if (this.currentToken != Token.Comma) break;
        this.GetNextToken(true);
      }
    }

    private void ParseDeclarationWithSpecModifiers(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal, bool savedInSpecCode)
    {
      var specifiers = new List<Specifier>();
      this.ParseSpecTypeModifierList(specifiers, followers);
      if (specifiers.Count == 1 && this.currentToken != Token.RightParenthesis) {
        this.ParseNonLocalDeclaration(namespaceMembers, typeMembers, followers | Token.RightParenthesis, isGlobal, specifiers);
        this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      } else {
        this.SkipOutOfSpecBlock(savedInSpecCode, followers);
        this.ParseNonLocalDeclaration(namespaceMembers, typeMembers, followers, isGlobal, specifiers);
      }
    }

    protected override void ParseNonLocalDeclarationInSpecBlock(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers, bool isGlobal, List<TemplateParameterDeclarator> templateParameters, List<Specifier> specifiers) {
      bool savedInSpecCode = this.SkipIntoSpecBlock();
      var name = this.ParseNameDeclaration(true);
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      this.AddTypeDeclarationMember(specifiers, new AnonymousFieldDeclarator(name), typeMembers);
      this.SkipSemiColonAfterDeclarationOrStatement(followers);
    }

    override protected void ParseTypeMemberDeclarationList(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers) {
      TokenSet expectedTokens = TS.DeclarationStart | Token.Colon;
      while (expectedTokens[this.currentToken]) {
        if (this.currentToken == Token.Specification) {
          this.ParseTypeSpecMemberDeclarationList(namespaceMembers, typeMembers, followers);
        } else {
          this.ParseNonLocalDeclaration(namespaceMembers, typeMembers, followers, false);
        }
      }
    }

    new protected void ParseTypeSpecMemberDeclarationList(List<INamespaceDeclarationMember> namespaceMembers, List<ITypeDeclarationMember> typeMembers, TokenSet followers) {
      bool savedInSpecCode = this.SkipIntoSpecBlock();
      if (this.currentToken == Token.Colon || this.currentToken == Token.Inline ||
        (this.currentToken == Token.Identifier && this.declspecExtensions.ContainsKey(this.scanner.GetIdentifierString()))) {
        this.ParseDeclarationWithSpecModifiers(namespaceMembers, typeMembers, followers, false, savedInSpecCode);
        return;
      }

      while (STS.TypeMember[this.currentToken]) {
        switch (this.currentToken) {
          case Token.SpecInvariant:
            this.ParseTypeInvariant(followers | Token.RightParenthesis);
            break;
          case Token.SpecGhost:
            this.GetNextToken();
            this.ParseNonLocalDeclaration(namespaceMembers, typeMembers, followers | Token.RightParenthesis, false);
            break;
          case Token.SpecGroup:
            ParseGroupDeclaration(typeMembers, followers);
            break;
        }
        this.SkipSemicolonsInSpecBlock(STS.TypeMember | Token.RightParenthesis);
      }
      this.SkipOutOfSpecBlock(savedInSpecCode, followers | Token.Specification);
    }

    private void ParseGroupDeclaration(List<ITypeDeclarationMember> typeMembers, TokenSet followers) {
      var slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      List<Specifier> specifiers = this.ParseSpecifiers(null, null, null, followers | Token.Identifier);
      var groupName = this.ParseNameDeclaration(true);
      slb.UpdateToSpan(groupName.SourceLocation);
      var dummyName = this.GetNameFor(SanitizeString(slb.SourceDocument.Name.Value) + ".." + ((ISourceLocation)slb).StartIndex);
      specifiers.Add(this.CreateAttribute("group_decl", groupName.Name.Value, groupName.SourceLocation));
      var groupDecl = new VccNestedStructDeclaration(new VccNameDeclaration(dummyName, true, groupName.SourceLocation), new List<ITypeDeclarationMember>(0), specifiers, slb);
      typeMembers.Add(groupDecl);
    }

    private Specifier CreateAttribute(string attrName, string attrVal, ISourceLocation sourceLocation) {
      var groupDeclSpecifiers = new List<Expression>(3)
                                               {
                                                 NamespaceHelper.CreateInSystemDiagnosticsContractsCodeContractExpr(
                                                   this.compilation.NameTable, "StringVccAttr"),
                                                 new CompileTimeConstant(attrName, sourceLocation),
                                                 new CompileTimeConstant(attrVal, sourceLocation)
                                               };
      return new DeclspecSpecifier(groupDeclSpecifiers, sourceLocation);
    }

    new protected void ParseTypeInvariant(TokenSet followers) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      NameDeclaration nameDecl = null;
      this.GetNextToken();
      Expression condition = this.ParseLabeledExpression(followers, true);
      var labeledInvariant = condition as VccLabeledExpression;
      if (labeledInvariant != null) {
        nameDecl = labeledInvariant.Label;
        condition = labeledInvariant.Expression;
      }
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      var typeInvariant = new TypeInvariant(nameDecl, new CheckedExpression(condition, condition.SourceLocation), false, slb);
      this.AddTypeInvariantToCurrent(typeInvariant);
    }

    protected override LoopContract ParseLoopContract(TokenSet followers) {
      var invariants = new List<LoopInvariant>();
      var writes = new List<Expression>();
      var variants = new List<Expression>();
      while (this.currentToken == Token.Specification) {
        var snap = this.scanner.MakeSnapshot();
        bool savedInSpecCode = this.SkipIntoSpecBlock();

        if (!STS.LoopContract[this.currentToken]) {
          this.LeaveSpecBlock(savedInSpecCode);
          scanner.RevertToSnapshot(snap);
          this.currentToken = Token.Specification;
          break;
        }

        while (STS.LoopContract[this.currentToken]) {
          switch (this.currentToken) {
            case Token.SpecInvariant:
              SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
              this.GetNextToken();
              var inv = this.ParseExpression(followers | Token.RightParenthesis);
              slb.UpdateToSpan(inv.SourceLocation);
              invariants.Add(new LoopInvariant(inv, slb));
              break;
            case Token.SpecWrites:
              this.GetNextToken();
              this.ParseExpressionList(writes, Token.Comma, true, followers | Token.RightParenthesis);
              break;
            case Token.SpecDecreases:              
              this.GetNextToken();
              this.ParseExpressionList(variants, Token.Comma, true, followers | Token.RightParenthesis);
              break;
          }
          this.SkipSemicolonsInSpecBlock(STS.LoopContract | Token.RightParenthesis);
        }
        this.SkipOutOfSpecBlock(savedInSpecCode, followers | Token.Specification);
      }
      if (invariants.Count == 0 && writes.Count == 0 && variants.Count == 0) return null;
      return new LoopContract(invariants, writes, variants);
    }

    override protected void ParseFunctionOrBlockContract(FunctionOrBlockContract contract, TokenSet followers) {
      this.ParseFunctionOrBlockContract(contract, followers, false, false);
    }

    private void ParseFunctionOrBlockContract(FunctionOrBlockContract contract, TokenSet followers, bool alreadyInContract, bool savedInSpecCode) {
      while (this.currentToken == Token.Specification || alreadyInContract) {
        if (alreadyInContract) {
          alreadyInContract = false;
        } else{
          savedInSpecCode = SkipIntoSpecBlock();
        }
        while (STS.FunctionOrBlockContract[this.currentToken] || 
               (this.currentToken == Token.Identifier && this.functionContractExtensions.ContainsKey(this.scanner.GetIdentifierString()))) {
          switch (this.currentToken) {
            case Token.SpecRequires:
              this.GetNextToken();
              var precond = this.ParseExpression(followers | Token.RightParenthesis);
              precond = this.CheckedExpressionIfRequested(precond);
              contract.AddPrecondition(new Precondition(precond, null, precond.SourceLocation));
              break;
            case Token.SpecEnsures:
              this.GetNextToken();
              this.resultIsAKeyword = true;
              var postcond = this.ParseExpression(followers | Token.RightParenthesis);
              this.resultIsAKeyword = false;
              postcond = this.CheckedExpressionIfRequested(postcond);
              contract.AddPostcondition(new Postcondition(postcond, postcond.SourceLocation));
              break;
            case Token.SpecWrites:
              this.GetNextToken();
              var writes = this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
              contract.AddWrites(writes);
              break;
            case Token.SpecDecreases:
              this.GetNextToken();
              var variants = this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
              contract.AddMethodVariants(variants);
              break;
            case Token.SpecReads:
              this.GetNextToken();
              var reads = this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
              contract.AddReads(reads);
              break;
            case Token.Identifier:
              this.ParseContractMacro(contract, followers);
              break;
          }
          this.SkipSemicolonsInSpecBlock(STS.FunctionOrBlockContract | Token.RightParenthesis);
        }
        this.SkipOutOfSpecBlock(savedInSpecCode, followers | Token.Specification);
      }
    }

    private void ParseContractMacro(FunctionOrBlockContract contract, TokenSet followers)
    {
      var keyword = this.scanner.GetIdentifierString();
      var fnName = this.functionContractExtensions[keyword];
      var loc = this.GetSourceLocationBuilderForLastScannedToken();
      Expression name = this.GetSimpleNameFor(fnName);
      this.GetNextToken();
      var slb = new SourceLocationBuilder(name.SourceLocation);
      List<Expression> parameters = new List<Expression>();
      if (this.currentToken != Token.RightParenthesis) {
        this.ParseExpressionList(parameters, Token.Comma, false, followers | Token.RightParenthesis);
      } 
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      if (fnName.StartsWith("\\result_macro_")) {
        var res = new VccReturnValue(loc);
        parameters.Insert(0, res);
        var tp = new VccTypeExpressionOf(res);
        name = new GenericInstanceExpression(name, new TypeExpression[] { tp }, loc);
      }
      var call = this.CheckedExpressionIfRequested(new VccMethodCall(name, parameters.AsReadOnly(), slb));
      contract.AddPostcondition(new Postcondition(call, call.SourceLocation));
    }

    protected override List<Parameter> ParseParameterList(TokenSet followers) {
      var result = new List<Parameter>();
      this.Skip(Token.LeftParenthesis);
      if (this.currentToken != Token.RightParenthesis) {
        TokenSet followersOrCommaOrRightParenthesisOrSpecification = followers | Token.Comma | Token.RightParenthesis | Token.Specification;
        while (this.currentToken != Token.RightParenthesis) {
          if (this.currentToken == Token.Specification) {
            result.Add(this.ParseSpecParameter(followers | Token.RightParenthesis));
            continue;
          }
          result.Add(this.ParseParameter(followersOrCommaOrRightParenthesisOrSpecification));
          if (this.currentToken == Token.Comma) {
            this.GetNextToken();
            continue;
          }
          if (this.currentToken == Token.Specification)
            continue;
          break;
        }
      }
      return result;
    }

    private Parameter ParseParameter(TokenSet followers, bool isOut, SourceLocationBuilder slb) {
      if (this.currentToken == Token.Range)
        return ParseVarArgsParameter(followers);

      List<Specifier> specifiers = this.ParseSpecifiers(null, null, null, followers | TS.DeclaratorStart);
      if (specifiers.Count > 0) slb.UpdateToSpan(specifiers[specifiers.Count - 1].SourceLocation);
      Declarator declarator = this.ParseDeclarator(followers);
      declarator = this.UseDeclaratorAsTypeDefNameIfThisSeemsIntended(specifiers, declarator, followers);
      slb.UpdateToSpan(declarator.SourceLocation);
      var result = new Parameter(specifiers, declarator, this.InSpecCode, isOut, slb);
      this.SkipTo(followers);
      return result;
    }

    private bool IsSpecParameterStart(Token t)
    {
      return t == Token.SpecGhost || t == Token.SpecOut;
    }

    private Parameter ParseSpecParameter(TokenSet followers) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      Parameter result;
      bool savedInSpecCode = this.SkipIntoSpecBlock();

      // sync with IsSpecParameterStart
      switch (this.currentToken) {
        case Token.SpecGhost:
          this.GetNextToken();
          result = this.ParseParameter(followers|Token.RightParenthesis, false, slb);
          break;
        case Token.SpecOut:
          this.GetNextToken();
          result = this.ParseParameter(followers|Token.RightParenthesis, true, slb);
          break;
        default:
          this.HandleError(Error.SyntaxError, "ghost or out");
          result = this.ParseParameter(followers | Token.RightParenthesis);
          break;
      }
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      return result;
    }

    protected override List<Expression> ParseArgumentList(SourceLocationBuilder slb, TokenSet followers) {
      var result = new List<Expression>();
      this.Skip(Token.LeftParenthesis);
      while (this.currentToken != Token.RightParenthesis) {
        if (this.currentToken == Token.Specification) {
          result.Add(this.ParseSpecArgument(followers | Token.Comma | Token.Specification | Token.RightParenthesis));
          continue;
        }
        result.Add(this.ParseArgumentExpression(followers | Token.Comma | Token.Specification | Token.RightParenthesis));
        if (this.currentToken == Token.Comma) {
          this.GetNextToken();
          continue;
        }
        if (this.currentToken == Token.Specification)
          continue;
        break;
      }
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      this.SkipOverTo(Token.RightParenthesis, followers);
      return result;
    }

    private Expression ParseSpecArgument(TokenSet followers) {
      Expression result;
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      bool savedInSpecCode = this.SkipIntoSpecBlock();
      switch (this.currentToken) {
        case Token.SpecGhost:
          this.GetNextToken();
          result = this.ParseExpression(followers | Token.RightParenthesis);
          break;
        case Token.SpecOut:
          this.GetNextToken();
          var outArg = this.ParseExpression(followers | Token.RightParenthesis);
          slb.UpdateToSpan(outArg.SourceLocation);
          result = new VccOutArgument(new TargetExpression(outArg), slb);
          break;
        default:
          result = this.ParseSpecCastExpression(followers, savedInSpecCode, slb);
          // we need to add the comma here because our caller is not prepared to deal with it
          if (this.currentToken == Token.Comma) this.GetNextToken(); 
          return result;
      }
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      return result;
    }

    override protected Statement ParseSpecStatements(TokenSet followers) {
      var scannerState = scanner.MakeSnapshot();

      bool savedInSpecCode = this.SkipIntoSpecBlock();

      switch (this.currentToken) {
        case Token.SpecUnwrapping:
          return this.ParseUnwrappingStatement(followers, savedInSpecCode);
        case Token.SpecAtomic:
          return this.ParseAtomic(followers, savedInSpecCode);
        case Token.Unchecked:
          return this.ParseUncheckedExpressionStatement(followers, savedInSpecCode);
        case Token.SpecEnsures:
        case Token.SpecReads:
        case Token.SpecRequires:
        case Token.SpecDecreases:
        case Token.SpecWrites:
          return this.ParseBlockWithContracts(followers, savedInSpecCode);
        case Token.Identifier:
          var id = this.scanner.GetIdentifierString();
          if (this.functionContractExtensions.ContainsKey(id)) {
              return this.ParseBlockWithContracts(followers, savedInSpecCode);
          }
          if (id == "ghost_atomic")
            return this.ParseGhostAtomic(followers, savedInSpecCode);
          if (id == "pure") 
            return this.ParseBlockWithPureModifier(followers, savedInSpecCode);
          if (this.declspecExtensions.ContainsKey(id)) {
            var specifiers = new List<Specifier>();
            this.ParseSpecTypeModifierList(specifiers, followers | Token.RightParenthesis);
            this.SkipOutOfSpecBlock(savedInSpecCode, followers | TS.DeclaratorStart);
            return StatementGroup.Create(this.ParseLocalDeclaration(specifiers, followers));
          }
          if (id == "atomic_op" || this.castlikeFunctions.ContainsKey(id)) {
            this.LeaveSpecBlock(savedInSpecCode);
            scanner.RevertToSnapshot(scannerState);
            this.currentToken = Token.Specification;

            if (id == "atomic_op") this.resultIsAKeyword = true;
            Expression expr = this.ParseExpression(true, false, followers | Token.Semicolon);
            this.resultIsAKeyword = false;
            var eStat = new ExpressionStatement(expr, new SourceLocationBuilder(expr.SourceLocation));
            this.SkipSemiColonAfterDeclarationOrStatement(followers);
            return eStat;
          }
          break;
      }

      var statements = new List<Statement>();
      TokenSet followersOrRightParenOrSpecStmt = followers | Token.RightParenthesis | STS.SimpleSpecStatment;

      while (STS.SimpleSpecStatment[this.currentToken] || 
        (this.currentToken == Token.Identifier &&  this.statementLikeFunctions.ContainsKey(this.scanner.GetIdentifierString()))) {
          SourceLocationBuilder slb;
          switch (this.currentToken) {
          case Token.SpecGhost:
            slb = this.GetSourceLocationBuilderForLastScannedToken();
            this.GetNextToken();
            var stmt = this.ParseStatement(followersOrRightParenOrSpecStmt);
            slb.UpdateToSpan(stmt.SourceLocation);
            StatementGroup.AddStatementOrGroupToList(DeepWrapInSpecStmt(stmt, slb), statements);
            break;
          case Token.SpecAssert:
            statements.Add(this.ParseAssert(followersOrRightParenOrSpecStmt));
            break;
          case Token.SpecAssume:
            statements.Add(this.ParseSingleArgSpecStatement(followersOrRightParenOrSpecStmt, (expr, sl) => new AssumeStatement(expr, sl)));
            break;
          case Token.Identifier:
            var keyword = this.scanner.GetIdentifierString();
            var name = this.GetSimpleNameFor(this.statementLikeFunctions[keyword]);
            this.GetNextToken();
            slb = new SourceLocationBuilder(name.SourceLocation);
            var parameters = new List<Expression>();
            if (this.currentToken != Token.RightParenthesis) {
              this.ParseExpressionList(parameters, Token.Comma, true, followers | Token.RightParenthesis);
              slb.UpdateToSpan(parameters[parameters.Count - 1].SourceLocation);
            }
            var call = new VccMethodCall(name, parameters.AsReadOnly(), slb);
            var exprStmt = new ExpressionStatement(call);
            statements.Add(DeepWrapInSpecStmt(exprStmt, slb));
            break;
        }
        this.SkipSemicolonsInSpecBlock(STS.SimpleSpecStatment | Token.Identifier | Token.RightParenthesis);
      }
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      return StatementGroup.Create(statements);
    }

    private Statement ParseBlockWithPureModifier(TokenSet followers, bool savedInSpecCode)
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      this.SkipOutOfSpecBlock(savedInSpecCode, TS.StatementStart | followers);
      var contract = new FunctionOrBlockContract { IsPure = true };
      this.ParseFunctionOrBlockContract(contract, followers, false, savedInSpecCode);
      Statement stmt = this.ParseStatement(followers);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      var blockWithContracts = new VccBlockWithContracts(new List<Statement>(1) { stmt }, slb);
      this.compilation.ContractProvider.AssociateMethodWithContract(blockWithContracts, contract.ToMethodContract());
      return blockWithContracts;      
    }

    private Statement ParseBlockWithContracts(TokenSet followers, bool savedInSpecCode)
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      var contract = new FunctionOrBlockContract();
      this.ParseFunctionOrBlockContract(contract, followers, true, savedInSpecCode);
      Statement stmt = this.ParseStatement(followers);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      var blockWithContracts = new VccBlockWithContracts(new List<Statement>(1){stmt}, slb);
      this.compilation.ContractProvider.AssociateMethodWithContract(blockWithContracts, contract.ToMethodContract());
      return blockWithContracts;
    }

    private Statement ParseUncheckedExpressionStatement(TokenSet followers, bool savedInSpecCode) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      this.SkipOutOfSpecBlock(savedInSpecCode, TS.StatementStart | followers);
      var expr = this.ParseExpression(true, false, followers);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      return new ExpressionStatement(new UncheckedExpression(expr, slb), slb);
    }

    private Statement ParseAtomic(TokenSet followers, bool savedInSpecCode) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      var exprs = this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
      this.SkipOutOfSpecBlock(savedInSpecCode, TS.StatementStart | followers);
      var body = this.ParseStatement(followers);
      slb.UpdateToSpan(body.SourceLocation);
      return new VccAtomicStatement(body, exprs, slb, isGhostAtomic: false);
    }

    private Statement ParseGhostAtomic(TokenSet followers, bool savedInSpecCode) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      var exprs = this.ParseExpressionList(Token.Comma, followers | Token.RightBrace);
      var body = this.ParseStatement(followers | Token.RightParenthesis);
      this.SkipOutOfSpecBlock(savedInSpecCode, TS.StatementStart | followers);
      slb.UpdateToSpan(body.SourceLocation);
      var wrapped = DeepWrapInSpecStmt(body, slb);
      return new VccAtomicStatement(wrapped, exprs, slb, isGhostAtomic: true);
    }

    private Statement ParseUnwrappingStatement(TokenSet followers, bool savedInSpecCode) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      var exprs = this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
      this.SkipOutOfSpecBlock(savedInSpecCode, TS.StatementStart | followers);
      var body = this.ParseStatement(followers);
      slb.UpdateToSpan(body.SourceLocation);
      return new VccUnwrappingStatement(body, exprs, slb);
    }

    private AssertStatement ParseAssert(TokenSet followers) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      //IEnumerable<IEnumerable<Expression>> triggers = null;
      //if (this.currentToken == Token.LeftBrace)
      //  triggers = this.ParseQuantifierTriggers(followers | TS.UnaryStart);
      var condition = this.ParseExpression(followers | Token.RightParenthesis);
      slb.UpdateToSpan(condition.SourceLocation);
      var result = new VccAssertStatement(condition, slb);
      //if (triggers != null) this.compilation.ContractProvider.AssociateTriggersWithQuantifier(result, triggers);
      return result;
    }

    protected override Expression ParseBraceLabeledExpression(SourceLocationBuilder slb, TokenSet followers)
    {
      var lab = (VccLabeledExpression)this.ParseLabeledExpression(followers | Token.RightBrace);      
      this.Skip(Token.RightBrace);
      var body = this.ParseExpression(followers);
      var labString = lab.Label.Name.Value;
      var labName = new VccByteStringLiteral(labString, lab.Label.SourceLocation);
      var labArg = lab.Expression;
      if (labArg is DummyExpression)
        labArg = new CompileTimeConstant(1, false, lab.Label.SourceLocation);
      if (labString == "use") { // this condition is sort of a hack, it should likely look at some function \lbl_use(...) or something
        labArg = new VccByteStringLiteral(labArg.SourceLocation.Source, labArg.SourceLocation);        
      }
      var args = new[] { labName, labArg, body };
      slb.UpdateToSpan(body.SourceLocation);
      return new VccMethodCall(this.GetSimpleNameFor("\\labeled_expression"), args, slb.GetSourceLocation());
    }

    protected override Expression ParseLabeledExpression(TokenSet followers, bool isInvariant = false)
    {
      if (this.currentToken == Token.Colon) {
        SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
        this.GetNextToken();
        NameDeclaration label;
        if (isInvariant && this.currentToken == Token.Volatile) {
          label = new VccNameDeclaration(this.GetNameFor("volatile"), false, slb);
          this.GetNextToken();
        } else {
          label = this.ParseNameDeclaration(true);
        }
        Expression expr;
        if (TS.UnaryStart[this.currentToken] || TS.PrimaryStart[this.currentToken]) {
          expr = this.ParseExpression(followers);
          slb.UpdateToSpan(expr.SourceLocation);
        } else {
          slb.UpdateToSpan(label.SourceLocation);
          expr = new DummyExpression(slb);
          this.SkipTo(followers);
        }
        return new VccLabeledExpression(expr, label, slb);
      }
      return this.ParseExpression(followers);
    }

    private Expression ParseSpecCastExpression(TokenSet followers, bool savedInSpecCode, SourceLocationBuilder slb)
    {
      if (this.CurrentTokenStartsTypeExpression()) {
        TypeExpression targetType = this.ParseTypeExpression(followers | Token.RightParenthesis);
        this.SkipOutOfSpecBlock(savedInSpecCode, TS.UnaryStart | followers);
        var valueToCast = this.ParseUnaryExpression(followers);
        slb.UpdateToSpan(valueToCast.SourceLocation);
        return new VccCast(valueToCast, targetType, slb);
      }
      if (this.currentToken == Token.Unchecked) {
        this.GetNextToken();
        this.SkipOutOfSpecBlock(savedInSpecCode, TS.UnaryStart | followers);
        var uncheckedExpr = this.ParseUnaryExpression(followers);
        slb.UpdateToSpan(uncheckedExpr.SourceLocation);
        return new UncheckedExpression(uncheckedExpr, slb);
      }
      if (this.currentToken == Token.Identifier) {
        var id = this.scanner.GetIdentifierString();
        //if (id.StartsWith("\\") && this.castlikeFunctions.ContainsKey(id.Substring(1)))
        //  id = id.Substring(1);
        if (id == "atomic_op" || this.castlikeFunctions.ContainsKey(id)) {
          var methodName = id == "atomic_op" ? "" : this.castlikeFunctions[id];
          var savedResultIsKeyword = this.resultIsAKeyword;
          this.resultIsAKeyword = (id == "atomic_op");
          var isVarArgs = methodName.StartsWith("\\castlike_va_");
          this.GetNextToken();
          List<Expression> exprs = this.currentToken == Token.RightParenthesis ? new List<Expression>() : this.ParseExpressionList(Token.Comma, followers | Token.RightParenthesis);
          this.resultIsAKeyword = savedResultIsKeyword;
          this.SkipOutOfSpecBlock(savedInSpecCode, TS.UnaryStart | followers);
          if (isVarArgs) {
            slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
            var argList = new VccMethodCall(this.GetSimpleNameFor("\\argument_tuple"), exprs.ToArray(), slb.GetSourceLocation());
            exprs.Clear();
            exprs.Add(argList);
          }
          var expr = this.ParseUnaryExpression(followers);
          slb.UpdateToSpan(expr.SourceLocation);
          if (id == "atomic_op") {
            exprs.Add(expr);
            var atomicOp = new VccAtomicOp(this.GetSimpleNameFor("_vcc_atomic_op"), exprs.AsReadOnly(), slb);
            var atomicOpBlock = new VccAtomicOpBlock(new List<Statement>(0), atomicOp, slb);
            return new BlockExpression(atomicOpBlock, atomicOp, slb);
          }
          exprs.Insert(0, expr);
          return new VccMethodCall(this.GetSimpleNameFor(methodName), exprs, slb);
        }
        this.HandleError(Error.SyntaxError, this.scanner.GetTokenSource());
        this.SkipOutOfSpecBlock(savedInSpecCode, followers);
        return new DummyExpression(slb);
      }
      this.HandleError(Error.SyntaxError, this.scanner.GetTokenSource());
      this.SkipOutOfSpecBlock(savedInSpecCode, followers);
      return new DummyExpression(slb);
    }

    protected override Expression ParseSpecCastExpression(TokenSet followers)
    {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      bool savedInSpecCode = this.SkipIntoSpecBlock();
      return this.ParseSpecCastExpression(followers, savedInSpecCode, slb);
    }

    protected override Expression ParseQuantifier(TokenSet followers) {
      Token kind = this.currentToken;
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      TokenSet followersOrLeftBraceOrSemicolonOrUnaryStart = followers | TS.LeftBraceOrRightParenthesisOrSemicolonOrUnaryStart | TS.PrimaryStart;
      List<LocalDeclarationsStatement> boundVariables = this.ParseQuantifierBoundVariables(followersOrLeftBraceOrSemicolonOrUnaryStart);
      IEnumerable<IEnumerable<Expression>> triggers = this.ParseQuantifierTriggers(followers | TS.UnaryStart | TS.PrimaryStart);
      Expression condition = this.ParseExpression(followers);
      slb.UpdateToSpan(this.scanner.SourceLocationOfLastScannedToken);
      Expression result;
      if (kind == Token.Exists)
        result = new Exists(boundVariables, condition, slb);
      else if (kind == Token.Forall)
        result = new Forall(boundVariables, condition, slb);
      else if (kind == Token.Lambda)
        result = new VccLambda(boundVariables, new CompileTimeConstant(true, SourceDummy.SourceLocation), condition, slb);
      else
        throw new InvalidOperationException();
      this.compilation.ContractProvider.AssociateTriggersWithQuantifier(result, triggers);
      return result;
    }

    private bool SkipIntoSpecBlock() {
      this.GetNextToken();
      bool savedInSpecCode = this.EnterSpecBlock();
      this.Skip(Token.LeftParenthesis, true);
      return savedInSpecCode;
    }

    private void SkipOutOfSpecBlock(bool savedInSpecBlock, TokenSet followers, bool skipSemicolons = false) {
      this.Skip(Token.RightParenthesis);
      this.LeaveSpecBlock(savedInSpecBlock);
      if (skipSemicolons)
        while (this.currentToken == Token.Semicolon)
          this.Skip(Token.Semicolon, true);
      this.SkipTo(followers);
    }

    private void SkipSemicolonsInSpecBlock(TokenSet followers) {
      if (this.currentToken == Token.RightParenthesis) return;
      while (this.currentToken == Token.Semicolon)
        this.Skip(Token.Semicolon, true);
      this.SkipTo(followers);
    }

    private Statement ParseSingleArgSpecStatement(TokenSet followers, Func<Expression, ISourceLocation, Statement> createStmt) {
      SourceLocationBuilder slb = this.GetSourceLocationBuilderForLastScannedToken();
      this.GetNextToken();
      var expr = this.ParseExpression(followers);
      slb.UpdateToSpan(expr.SourceLocation);
      return createStmt(expr, slb);
    }

    private static Statement DeepWrapInSpecStmt(Statement stmt, ISourceLocation slb) {
      var sg = stmt as StatementGroup;
      if (sg != null) return new StatementGroup(sg.Statements.ConvertAll(s => DeepWrapInSpecStmt(s, s.SourceLocation)));
      var localDecl = stmt as LocalDeclarationsStatement;
      if (localDecl != null) return localDecl;
      return new VccSpecStatement(stmt, slb);
    }

    private static class STS {
      public static TokenSet SimpleSpecStatment = new TokenSet() | Token.SpecGhost | Token.SpecAssume | Token.SpecAssert;
      public static TokenSet FunctionOrBlockContract = new TokenSet() | Token.SpecEnsures | Token.SpecReads | Token.SpecRequires | Token.SpecDecreases | Token.SpecWrites;
      public static TokenSet LoopContract = new TokenSet() | Token.SpecInvariant | Token.SpecWrites | Token.SpecDecreases;
      public static TokenSet TypeMember = new TokenSet() | Token.SpecGhost | Token.SpecInvariant | Token.SpecGroup;
      public static TokenSet Global = new TokenSet() | Token.SpecAxiom | Token.SpecGhost | Token.SpecLogic;
    }
  }
}
