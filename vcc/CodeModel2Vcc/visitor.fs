//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open Microsoft.FSharp.Math
  open Microsoft.Cci
  open Microsoft.Cci.Contracts
  open Microsoft.Cci.Ast
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.Util
  module C = Microsoft.Research.Vcc.CAST

  module StringLiterals =
    [<Literal>]
    let SystemDiagnosticsContractsCodeContract = "System.Diagnostics.Contracts.CodeContract"

    [<Literal>]
    let SystemDiagnosticsContractsCodeContractTypedPtr = "System.Diagnostics.Contracts.CodeContract.TypedPtr"

    [<Literal>]
    let SystemIntPtr = "System.IntPtr"

    [<Literal>]
    let SystemDiagnosticsContractsCodeContractMap = "System.Diagnostics.Contracts.CodeContract.Map"

    [<Literal>]
    let SystemDiagnosticsContractsCodeContractBigInt = "System.Diagnostics.Contracts.CodeContract.BigInt"

    [<Literal>]
    let SystemDiagnosticsContractsCodeContractBigNat = "System.Diagnostics.Contracts.CodeContract.BigNat"

    [<Literal>]
    let SystemDiagnosticsContractsCodeContractObjset = "System.Diagnostics.Contracts.CodeContract.Objset"

    [<Literal>]
    let SystemDouble = "System.Double"

    [<Literal>]
    let SystemFloat = "System.Float"

  open StringLiterals

  type Dict<'a, 'b> = System.Collections.Generic.Dictionary<'a, 'b>

  type HashSet<'a> = System.Collections.Generic.HashSet<'a>
  
  and Visitor(contractProvider:Microsoft.Cci.Ast.SourceContractProvider, helper:Helper.Env) =

    inherit Microsoft.Cci.Ast.SourceVisitor()

    do C.PointerSizeInBytes := helper.PointerSizeInBytes

    let mutable topDecls : list<C.Top> = []
    let mutable stmtRes : C.Expr = C.Expr.Bogus
    let mutable exprRes : C.Expr = C.Expr.Bogus
    let mutable typeRes : C.Type = C.Type.Bogus
    let mutable globalsType = null
    let mutable fnPtrCount = 0;
    let finalActions = System.Collections.Generic.Queue<(unit -> unit)>()
    
    let mutable localsMap = new Dict<obj, C.Variable>(new ObjEqualityComparer());
    let mutable localVars = []
    let mutable unfoldingConstant = false
    let globalsMap = new Dict<IGlobalFieldDefinition, C.Variable>()
    let specGlobalsMap = new Dict<string, C.Variable>()
    let methodsMap = new Dict<ISignature, C.Function>()
    let functionPointerMap = new Dict<ISignature, C.TypeDecl>()
    let methodNameMap = new Dict<string, C.Function>()
    let typesMap = new Dict<ITypeDefinition, C.TypeDecl>()
    let typeNameMap = new Dict<string, C.TypeDecl>()
    let fieldsMap = new Dict<IFieldDefinition, C.Field>()
    let mutable doingEarlyPruning = false
    let mutable requestedFunctions = []
    let mutable currentFunctionName = ""

    let typestateFieldsMap = Map.ofList [ 
                                          "\\claim_count",  "_vcc_ref_cnt"
                                          "\\closed",       "_vcc_closed"
                                          "\\owns",         "_vcc_owns"
                                          "\\owner",        "_vcc_owner"
                                          "\\valid",        "_vcc_typed2"
                                        ]
       
    let cTrue = C.Expr.BoolLiteral ( { Type = C.Type.Bool; Token = C.bogusToken }, true )
    let cFalse = C.Expr.BoolLiteral ( { Type = C.Type.Bool; Token = C.bogusToken }, false )

    let token (o : Microsoft.Cci.IObjectWithLocations) = VisitorHelper.GetTokenFor (o.Locations)
    let oops msg =
      helper.Oops (C.bogusToken, msg)
    let oopsLoc (o : Microsoft.Cci.IObjectWithLocations) msg =
      helper.Oops (token o, msg)
    let emacro name args = C.Expr.Macro (C.ExprCommon.Bogus, name, args)
    let die () = helper.Die ()
    let dieTok tok = helper.Die(tok)
    let xassert cond =
      if cond then ()
      else oops "assertion failed"; die ()

    let findFunctionOrDie name objWithLoc =
      match methodNameMap.TryGetValue(name) with
        | true, f -> f
        | _ -> oopsLoc objWithLoc ("cannot find internal function " + name + ". Forgotten #include <vcc.h>?"); die()


    let checkedStatus ch = if ch then C.CheckedStatus.Checked else C.CheckedStatus.Unchecked
  
    let stmtToken (msg:string) (e:C.Expr) =
      let forwardingToken tok (getmsg : unit -> string) =
        { Token = (new ForwardingToken (tok, getmsg) :> Token);
          Type = C.Type.Void } : C.ExprCommon
      forwardingToken e.Token (fun () -> msg.Replace ("@@", e.Token.Value))

    let removeDuplicates l =
      let elements = new HashSet<_>()
      let rec loop = function
        | [] -> []
        | x::xs -> if elements.Add x then x :: loop xs else loop xs
      loop l

    let hasCustomAttr n = List.exists (function C.VccAttr (n', _) -> n = n' | _ -> false)

    let convCustomAttributes tok (attrs : ICustomAttribute seq) = 
      let getAttrTypeName (attr:ICustomAttribute) = TypeHelper.GetTypeName(attr.Type.ResolvedType)
      let getAttrArgs (attr:ICustomAttribute) =
        let args = new System.Collections.Generic.List<IMetadataExpression>(attr.Arguments)
        let name = ((args.Item(0) :?> IMetadataConstant).Value :?> string)
        let value = if args.Count > 1 then (args.Item(1) :?> IMetadataConstant).Value else null
        (name, value)      
      [ for attr in attrs do
        let attrName = getAttrTypeName attr
        match attrName with
        | "Microsoft.Cci.DummyType" -> yield! []   
        | "System.Diagnostics.Contracts.CodeContract.BoolBoogieAttr" -> 
          let (name, value) = getAttrArgs attr
          yield C.BoolBoogieAttr (name, (value :?> int) <> 0)
        | "System.Diagnostics.Contracts.CodeContract.StringVccAttr" ->
          let (name, value) = getAttrArgs attr
          yield C.VccAttr (name, (value :?> string))
        | "System.Diagnostics.Contracts.CodeContract.IntBoogieAttr" ->
          let (name, value) = getAttrArgs attr
          yield C.IntBoogieAttr (name, (value :?> int))
        | other when other.StartsWith("Microsoft.Contracts") ->
            do helper.Oops (tok, "unsupported custom attribute: " + other); die (); 
            yield! []
        | _ -> yield! []
      ]

    let isTypeWhereVolatileMatters = function
      | C.Type.Ref(_) -> true
      | _ -> false
        
    static member private CheckHasError(e : IExpression) =
     match e with
       | :? IErrorCheckable as ec -> ec.HasErrors
       | _ -> false
    
    static member private CheckHasError(c : ITypeContract) =
     match c with
       | :? IErrorCheckable as ec -> ec.HasErrors
       | _ -> false
    
    static member private CheckHasError(s : IStatement) =
     match s with
       | :? IErrorCheckable as ec -> ec.HasErrors
       | _ -> false
    
    static member private CheckHasError(c : IMethodContract) =
     match c with
       | :? IErrorCheckable as ec -> ec.HasErrors
       | _ -> false
    
    static member private CheckHasError(c : ILoopContract) =
     match c with
       | :? IErrorCheckable as ec -> ec.HasErrors
       | _ -> false
    
    member private this.DoPrecond (p:IPrecondition) =
      if Visitor.CheckHasError(p.Condition) then oopsLoc p "precondition has errors"; cTrue
      else this.DoIExpression (p.Condition)
    member private this.DoPostcond (p:IPostcondition) =
      if Visitor.CheckHasError(p.Condition) then oopsLoc p "postcondition has errors"; cFalse
      else this.DoIExpression (p.Condition)
        
    member this.GetResult () =
      while finalActions.Count > 0 do      
        finalActions.Dequeue () ()
      topDecls

    member this.EnsureMethodIsVisited (m : IMethodDefinition) =
      if doingEarlyPruning then 
        match m with 
          | :? IGlobalMethodDefinition -> this.DoMethod(m, true, false) 
          | :? IGenericMethodInstance as gmi -> this.EnsureMethodIsVisited(gmi.GenericMethod.ResolvedMethod)
          | _ -> ()
    
    member this.DoType (typ:ITypeReference) =
      typeRes <- C.Type.Bogus
      typ.Dispatch (this)
      let res = typeRes
      typeRes <- C.Type.Bogus
      if typ.TypeCode <> PrimitiveTypeCode.Invalid && res = C.Type.Bogus then
        die ()
      match res with
        | C.Type.Ref ({ Name = "\\type"; Kind = C.MathType }) -> C.Type.TypeIdT
        | _ -> res
    
    member this.ExprCommon (expr:IExpression) = { Token = token expr; Type = this.DoType (expr.Type) } : C.ExprCommon
      
    member this.ExprCommon (expr:Expression)  = 
      let iexpr = expr.ProjectAsIExpression()
      { Token = token iexpr; Type = this.DoType (iexpr.Type) } : C.ExprCommon
      
    member this.StmtCommon (expr:IStatement) = { Token = token expr; Type = C.Void } : C.ExprCommon
      
    member this.LookupMethod (meth:ISignature) : C.Function =
      if methodsMap.ContainsKey meth then
        methodsMap.[meth]
      else
        let (name, tok) = 
          match meth with
            | :? IMethodDefinition as def -> (def.Name.Value, token def)
            | :? VccFunctionPointerType as fptr -> 
              fnPtrCount <- fnPtrCount + 1
              (fptr.Name.Value + "#" + fnPtrCount.ToString(), token fptr)
            | _ -> die()
        // there is an additional malloc in Vcc.Runtime, we want only one
        // same goes for other ones
        // TODO check if the thing is from Vcc.Runtime and if so, ignore it -- don't list all the names
        match name with
          | "malloc" 
          | "free"
          | "get___FUNCTION__"
          | "memcmp"
          | "__int2c"
          | "__debugbreak"
          | "memcpy" 
              when methodNameMap.ContainsKey name ->
            let decl = methodNameMap.[name]
            methodsMap.Add (meth, decl)
            decl
          | _ when methodsMap.ContainsKey meth -> methodsMap.[meth]
          | _ ->
            let isSpec =
              if name.StartsWith("_vcc") || name.StartsWith("\\") then true 
              else match meth with
                    | :? Microsoft.Research.Vcc.VccGlobalMethodDefinition as def -> def.IsSpec 
                    | _ -> false 
            let acceptsExtraArguments =
              match meth with
                | :? IMethodDefinition as methodDef -> methodDef.AcceptsExtraArguments
                | _ -> false
            let decl =
              { C.Function.Empty() with
                  Token           = tok
                  IsSpec          = isSpec
                  RetType         = this.DoType(meth.Type)
                  Name            = name
                  AcceptsExtraArguments = acceptsExtraArguments
                  }
            if decl.Name = "" then
              printf "null name\n"
            else
              methodNameMap.[decl.Name] <- decl
            methodsMap.Add(meth, decl)
            decl
    
    member this.DoMethod (meth:ISignature, contractsOnly:bool, deferContracts:bool) =
      
      let (name, genericPars) =
        match meth with
          | :? IMethodDefinition as def -> def.Name.Value, def.GenericParameters
          | _ -> "", Seq.empty

      if name = "_vcc_atomic_op_result" then ()
      else       
        let decl = this.LookupMethod (meth)
        if decl.IsProcessed then ()
        else
          let expansion, hasErrors =
            match meth with
              | :? VccGlobalMethodDefinition as vccMeth -> 
                match vccMeth.GlobalMethodDeclaration with 
                  | :? Microsoft.Research.Vcc.FunctionDefinition as fDef -> fDef.Expansion, fDef.HasErrors
                  | _ -> null, false
              | _ -> null, false
          let body = 
            match meth with
              | :? IMethodDefinition as def ->
                (def.Body :?> ISourceMethodBody).Block
              | _ -> null
          decl.IsProcessed <- true       
          let parm (p:IParameterTypeInformation) =
            let name =
              match p with
                | :? IParameterDefinition as def -> def.Name.Value
                | _ -> "#p" + p.GetHashCode().ToString()
            let isSpec, isOut =
              match p with
                | :? Microsoft.Research.Vcc.VccParameterDefinition as vcp -> vcp.IsSpec, vcp.IsOut
                | _ -> false, false
            let varKind =
              match isSpec, isOut with
                | true, true -> C.VarKind.OutParameter
                | true, false -> C.VarKind.SpecParameter
                | false, false -> C.VarKind.Parameter
                | _ -> die() // out param must always also be a spec parameter
            let v = C.Variable.CreateUnique name (this.DoType (p.Type)) varKind
            if not (localsMap.ContainsKey p) && not (localsMap.ContainsKey ((p.ContainingSignature, v.Name))) then
              localsMap.Add (p, v)
              // this is SO WRONG, however it seems that sometimes different instances
              // of IParameterDefinition are referenced from code (does it have to do with
              // contract variable renaming?)
              localsMap.Add ((p.ContainingSignature, v.Name), v)
            v
                                    
          // needs to be done first so they get into localsMap
          decl.TypeParameters <- [ for tp in genericPars -> { Name = tp.Name.Value } : C.TypeVariable ]
          decl.Parameters <- meth.Parameters |> Seq.toList |> List.filter (fun p -> p.Type.TypeCode <> PrimitiveTypeCode.Void) |> List.map parm

          // extract custom attributes
          match meth with
            | :? IMethodDefinition as def ->
              let attrsFromDecls = 
                match meth with
                | :? VccGlobalMethodDefinition as fd ->
                  List.concat [ for d in fd.Declarations -> convCustomAttributes (token d) d.Attributes ]
                | _ -> []
              let attrsFromDef = convCustomAttributes (token def) def.Attributes
              decl.CustomAttr <- removeDuplicates (attrsFromDef @ attrsFromDecls)
            | _ -> ()

          let contractsOnly = contractsOnly && 
                              not (hasCustomAttr CAST.AttrAtomicInline decl.CustomAttr) && 
                              not (List.exists (fun n -> n = decl.Name) requestedFunctions) &&
                              not (hasCustomAttr CAST.AttrDefinition decl.CustomAttr)
          // make sure that if the current function is explicitly requested or atomic_inline or def, then process its body
          // coming here again to process the body in a second round does not work.
          
          if body = null || contractsOnly then
            topDecls <- C.Top.FunctionDecl decl :: topDecls
          else
            let savedLocalVars = localVars
            localVars <- []
            currentFunctionName <- decl.Name
            let body = this.DoStatement body
            let body' = if decl.IsSpec then C.Expr.SpecCode(body) else body
            let locals = (List.map (fun v -> C.Expr.VarDecl (C.voidBogusEC(), v, [])) decl.InParameters) @ List.rev localVars
            decl.Body <- Some (C.Expr.MkBlock (locals @ [body']))
            localVars <- savedLocalVars
            topDecls <- C.Top.FunctionDecl decl :: topDecls

          let contract = contractProvider.GetMethodContractFor(meth)     
          if contract <> null then
            Visitor.CheckHasError(contract) |> ignore
            // reset localsMap to deal with renaming of contracts between definition and declaration          
            let doContracts() = 
              let savedLocalsMap = localsMap
              match contract with
              | :? MethodContract as methodContract ->
                let isNotVoidPar (p : ParameterDeclaration) = p.Type.ResolvedType.TypeCode <> PrimitiveTypeCode.Void
                if (methodContract.ContainingSignatureDeclaration.Parameters |> Seq.filter isNotVoidPar |> Seq.length) <> (Seq.length decl.Parameters) then
                  helper.Error(decl.Token, 9658, "declared formal parameter list different from definition", Some(VisitorHelper.GetTokenFor [(methodContract.ContainingSignatureDeclaration.SourceLocation :> ILocation)]))
                localsMap <- new Dict<obj,_>(new ObjEqualityComparer())
                let addParmRenaming (fromParm:ParameterDeclaration) (toVar:C.Variable) =
                  localsMap.Add(((fromParm.ContainingSignature.SignatureDefinition), fromParm.Name.Value), toVar)
                let contractPars = seq { for p in methodContract.ContainingSignatureDeclaration.Parameters do if p.Type.ResolvedType.TypeCode <> PrimitiveTypeCode.Void then yield p }
                Seq.iter2 addParmRenaming contractPars decl.Parameters
              | _ -> ()
              decl.Requires   <- [ for p in contract.Preconditions -> this.DoPrecond p ]
              decl.Ensures    <- [ for r in contract.Postconditions -> this.DoPostcond r ]
              decl.Writes     <- [ for e in contract.Writes -> this.DoIExpression e ]
              decl.Reads      <- [ for e in contract.Reads -> this.DoIExpression e ]
              decl.Variants   <- [ for e in contract.Variants -> this.DoIExpression e ]
              localsMap <- savedLocalsMap

            if deferContracts then finalActions.Enqueue doContracts else doContracts()

          else if expansion <> null then
            let ex = this.DoIExpression (expansion.ProjectAsIExpression())
            decl.Ensures <- [ C.Expr.Prim({ex.Common with Type = C.Type.Bool}, C.Op("==", C.CheckedStatus.Unchecked), [C.Expr.Result(ex.Common); ex]) ]
        
    member this.DoStatement (stmt:IStatement) : C.Expr =
      if Visitor.CheckHasError(stmt) then
        oopsLoc stmt  "errors in stmt"
        C.Comment (this.StmtCommon stmt, sprintf "statement %s had errors" (stmt.ToString()))
      else
        stmtRes <- C.Expr.Bogus
        match stmt with
          | :? LocalDeclarationsStatement as stmt ->
            oopsLoc stmt "unexpected LocalDeclarationsStatement"
            stmtRes <- C.Comment (this.StmtCommon stmt, sprintf "unexpected statement %s" (stmt.ToString()))
          | :? IVccStatement as stmt -> stmt.Dispatch(this)
          | stmt -> stmt.Dispatch(this)
        let res = stmtRes
        stmtRes <- C.Expr.Bogus
        xassert (res <> C.Expr.Bogus)
        res
     
    member this.DoInvariant (inv:ITypeInvariant) : C.Expr =
      let cond = this.DoIExpression inv.Condition
      let name = if inv.Name <> null then inv.Name.Value else "public"
      C.Expr.Macro(cond.Common, "labeled_invariant", [C.Expr.Macro(C.bogusEC, name, []); cond])
     
    member this.DoIExpression(expr:IExpression) : C.Expr =
      if Visitor.CheckHasError(expr) then
        oopsLoc expr "error in expr"
        C.Expr.Bogus
      else
        exprRes <- C.Expr.Bogus
        expr.Dispatch(this)
        let res = exprRes
        exprRes <- C.Expr.Bogus
        xassert (res <> C.Expr.Bogus)
        res

    member this.DoExpression(expr:Expression) : C.Expr =
      exprRes <- C.Expr.Bogus
      match expr with 
        | :? VccSizeOf as sizeOf -> exprRes <- this.DoSizeOf(sizeOf)
        | _ -> expr.Dispatch(this :> SourceVisitor)
      let res = exprRes
      exprRes <- C.Expr.Bogus
      assert (res <> C.Expr.Bogus)
      res

    member this.DoSizeOf(sizeOf : SizeOf) = 
      C.Expr.SizeOf(this.ExprCommon (sizeOf :> Expression), this.DoType(sizeOf.Expression.ResolvedType))

    member this.DoSizeOf(sizeOf : VccSizeOf) = 
      let tp = this.DoType(sizeOf.TypeToSize.ResolvedType)
      let v = sizeOf.CompileTimeValue()
      if v > 0 && v <> tp.SizeOf then
        C.Expr.IntLiteral (this.ExprCommon (sizeOf :> Expression), new bigint(v))
      else
        C.Expr.SizeOf(this.ExprCommon (sizeOf :> Expression), tp)


    member this.DoCompileTimeConstant(constant : ICompileTimeConstant) =

      let ec, value =
        match constant with
          | :? CompileTimeConstant as cconst ->
            let unfolded = cconst.UnfoldedExpression

            // this is an ungly workaround for the situation where CCI converts constants, which could be
            // either signed or unsigned to their unsigned form, which looses the sign extension
            // should they really be meant as signed the are then being cast to a larger signed type
            // the example from the test suite, where this happens is this:
            //
            // address = (__int32 *) (((__int64) Target) & (~0x3));
            //
            // Here, the ~0x3 is the negative number -4, which should then be cast to __int64, without this
            // fix, it is treated as (__int64)(unsigned __int32)(~0x3), which is wrong

            if constant.Type.ResolvedType <> unfolded.Type.ResolvedType 
              && TypeHelper.IsSignedPrimitiveInteger(constant.Type.ResolvedType)
              && TypeHelper.IsSignedPrimitiveInteger(unfolded.Type.ResolvedType)
              && constant.Value <> unfolded.Value 
            then
              this.ExprCommon (cconst.ProjectAsIExpression()), unfolded.Value
            else
              this.ExprCommon constant, constant.Value
          | _ -> this.ExprCommon constant, constant.Value

      match ec.Type with
        | C.Type.Integer _ ->
          match value with
            | :? char as c -> C.Expr.IntLiteral(ec, new bigint((int)c))
            | _ -> C.Expr.IntLiteral (ec, bigint.Parse(value.ToString ()))
        | C.Type.Bool -> C.Expr.BoolLiteral (ec, unbox value)
        | C.Type.Primitive _ -> C.Expr.Macro(ec, "float_literal", [C.Expr.UserData(ec, value)])
        | C.Ptr (C.Type.Integer C.IntKind.UInt8) -> C.Expr.Macro (ec, "string", [C.Expr.ToUserData(value)])
        | C.Ptr (C.Type.Void) -> 
          let ptrVal = 
            let ecInt = {ec with Type = C.Type.Integer C.IntKind.Int64}
            match value with
              | :? System.IntPtr as ptr ->  C.Expr.IntLiteral(ecInt, new bigint(ptr.ToInt64()))
              | _ -> C.Expr.IntLiteral(ecInt, bigint.Parse(value.ToString()))
          C.Expr.Cast(ec, C.CheckedStatus.Unchecked, ptrVal)
        | _ -> die()

    member this.DoBlock(block : IBlockStatement) =
     let savedLocalVars = localVars
     localVars <- []
     let stmts = [for s in block.Statements -> this.DoStatement (s)]
     let block' = C.Expr.Block(this.StmtCommon block, (localVars @ stmts), None)
     localVars <- savedLocalVars
     let contract = contractProvider.GetMethodContractFor(block)
     let result = 
       if (contract = null) then
         block'
       else 
        let cs = {Requires  = [ for req in contract.Preconditions -> this.DoPrecond req ];
                  Ensures   = [ for ens in contract.Postconditions -> this.DoPostcond ens ];
                  Reads     = [ for rd in contract.Reads -> this.DoIExpression rd ];
                  Writes    = [ for wr in contract.Writes -> this.DoIExpression wr ];
                  Decreases = [ for vr in contract.Variants -> this.DoIExpression vr ];
                  IsPureBlock = contract.IsPure } : CAST.BlockContract
        match block' with
          | C.Expr.Block (ec,ss,_) -> C.Expr.Block (ec,ss, Some cs)
          | _ -> C.Expr.Block ({ Type = block'.Type; Token = block'.Token }, [block'], Some cs)
     match block with
       //| :? VccSpecBlock -> C.Macro(result.Common, "spec", [result])
       | _ -> result

    member this.DoIUnary (op:string, un:IUnaryOperation, ch) =
      exprRes <- C.Expr.Prim (this.ExprCommon un, C.Op(op, checkedStatus ch), [this.DoIExpression (un.Operand)])

    member this.DoUnary (op:string, un:UnaryOperation) =
      C.Expr.Prim (this.ExprCommon (un :> Expression), C.Op(op, C.Unchecked), [this.DoExpression (un.ConvertedOperand)])

    member this.DoIBinary (op:string, bin:IBinaryOperation) =
      this.DoIBinary(op, bin, false)

    member this.DoIBinary (op:string, bin:IBinaryOperation, ch:bool) =
      exprRes <- C.Expr.Prim (this.ExprCommon bin, C.Op(op, checkedStatus ch), [this.DoIExpression (bin.LeftOperand); this.DoIExpression (bin.RightOperand)])

    member this.DoBinary (op:string, bin:BinaryOperation) =
      C.Expr.Prim (this.ExprCommon (bin :> Expression), C.Op(op, C.Unchecked), [this.DoExpression (bin.ConvertedLeftOperand); this.DoExpression (bin.ConvertedRightOperand)])

    member this.DoGlobal (g:IGlobalFieldDefinition) =
      // TODO initializer?
      match globalsMap.TryGetValue g with
        | (true, v) -> v
        | _ -> 
          match g with
            | :? GlobalFieldDefinition as decl ->
              let rec doInitializer t (expr : Expression) = 
                match expr with
                  | :? VccInitializer as initializer ->
                    let ec = { Token = token expr; Type = t } : C.ExprCommon
                    C.Macro(ec, "init", [ for e in initializer.Expressions -> doInitializer (this.DoType (e.Type)) e])
                  | _ when expr.Type.ResolvedType = Microsoft.Cci.Dummy.Type ->
                    this.DoIExpression (expr.ContainingBlock.Helper.ImplicitConversionInAssignmentContext(expr, decl.Type.ResolvedType).ProjectAsIExpression())
                  | _ -> this.DoIExpression (expr.ProjectAsIExpression())
              let t = this.DoType g.Type
              let t' = if decl.GlobalFieldDeclaration.IsVolatile then C.Type.Volatile(t) else t
              let var = C.Variable.CreateUnique g.Name.Value t' (if decl.IsReadOnly then C.VarKind.ConstGlobal else C.VarKind.Global)
              globalsMap.Add (g, var)
              let initializer = if decl.GlobalFieldDeclaration.Initializer = null then None else Some(doInitializer (var.Type) (decl.GlobalFieldDeclaration.Initializer))
              topDecls <- C.Top.Global(var, initializer) :: topDecls
              var
            | _ -> die()
    
    member this.DoSpecGlobal (g:Microsoft.Cci.Ast.FieldDefinition) =
      // TODO initializer?
      match specGlobalsMap.TryGetValue (g.Name.Value) with
        | (true, v) -> v
        | _ -> 
          let var = C.Variable.CreateUnique g.Name.Value (this.DoType g.Type) C.VarKind.SpecGlobal
          specGlobalsMap.Add (var.Name, var)
          topDecls <- C.Top.Global(var, None) :: topDecls
          var
    
    member this.DoField (expr:IExpression) (instance:IExpression) (definition:obj) =
      let ec = this.ExprCommon expr
      if instance = null then
        exprRes <-
          match definition with
            | :? IExpression as e -> this.DoIExpression e
            | _ when localsMap.ContainsKey definition ->
              C.Expr.Ref (ec, localsMap.[definition]) 
            | :? IParameterDefinition as p ->
              let key = (p.ContainingSignature, p.Name.Value)
              let name = p.Name.Value
              if localsMap.ContainsKey name then
                C.Expr.Ref (ec, localsMap.[name])
              else
                if not (localsMap.ContainsKey (key :> obj)) then
                  oopsLoc p ("cannot find parameter " + name); die ()
                C.Expr.Ref (ec, localsMap.[key])
            | :? IGlobalFieldDefinition as g ->
              C.Expr.Ref (ec, this.DoGlobal g)
            | :? Microsoft.Cci.Ast.FieldDefinition as def ->
              if def.FieldDeclaration.Name.Value.StartsWith ("?mappedLiteral") then
                C.Expr.Macro (ec, "string", [C.Expr.ToUserData(def.FieldDeclaration.Initializer.Value)])
              else
                C.Expr.Ref (ec, this.DoSpecGlobal def)
            | :? IMethodDefinition as def ->
              this.EnsureMethodIsVisited(def)
              let fn = this.LookupMethod def
              C.Expr.Macro (ec, "get_fnptr", [C.Expr.Call ({ ec with Type = fn.RetType }, fn, [], [])])
            | _ -> oopsLoc expr ("cannot find " + definition.ToString()); die ()
      else
        match definition with
          | :? IAddressDereference as deref -> (this :> ICodeVisitor).Visit deref
          | :? IFieldDefinition as def ->
            let instance = this.DoIExpression instance

            match typestateFieldsMap.TryFind def.Name.Value with
              | Some v1Fn ->
                // We seem to generate _vcc_typed(*f) when f is a function
                let instance = 
                  match instance with
                    | C.Deref (_, inner) when instance.Type = inner.Type -> inner
                    | _ -> instance
                let instance =
                  match instance.Type with
                   | C.Type.ObjectT
                   | C.Ptr _ -> instance
                   | t -> C.Expr.Macro ({ instance.Common with Type = C.PhysPtr t }, // TODO: Ptr kind
                                        "&", [instance])

                exprRes <- C.Expr.Macro({ec with Type = this.DoType def.Type}, v1Fn, [instance])           
              | None ->

                if not (fieldsMap.ContainsKey def) then
                  oopsLoc def ("field " + def.Name.Value + " not found")
            
                let field = fieldsMap.[def]
                let instance =
                  match instance.Type with
                   | C.Ptr _ -> instance
                   | t -> C.Expr.Macro ({ instance.Common with Type = C.PhysPtr t }, // TODO: Ptr kind
                                        "&", [instance])
                let dot =  C.Expr.MkDot(ec, instance, field)
                exprRes <- C.Expr.Deref (ec, dot)
          | _ -> assert false
   
    member this.TryGetDatatypeDefinition (typeDef:ITypeDefinition) =
      match typeDef with
        | :? NamedTypeDefinition as ntd ->
          let dts =
             ntd.TypeDeclarations |> 
             Seq.map (fun o -> o :> obj) |>
             Seq.collect 
               (function
                  | (:? IVccDatatypeDeclaration as dt) -> [dt]
                  | _ -> []) |>
             Seq.toList
          match dts with
            | dt :: _ -> dt
            | _ -> null
        | _ -> null

    member this.DoTypeDefinition (typeDef:ITypeDefinition) =
      typeRes <-
          match typeDef.TypeCode with
            | PrimitiveTypeCode.Char -> C.Type.Integer (C.IntKind.UInt8)
            | PrimitiveTypeCode.String -> C.Type.PhysPtr (C.Type.Integer C.IntKind.UInt8)
            | PrimitiveTypeCode.UInt8  -> C.Type.Integer (C.IntKind.UInt8)
            | PrimitiveTypeCode.UInt16 -> C.Type.Integer (C.IntKind.UInt16)
            | PrimitiveTypeCode.UInt32 -> C.Type.Integer (C.IntKind.UInt32)
            | PrimitiveTypeCode.UInt64 -> C.Type.Integer (C.IntKind.UInt64)
            | PrimitiveTypeCode.Int8   -> C.Type.Integer (C.IntKind.Int8)
            | PrimitiveTypeCode.Int16  -> C.Type.Integer (C.IntKind.Int16)
            | PrimitiveTypeCode.Int32  -> C.Type.Integer (C.IntKind.Int32)
            | PrimitiveTypeCode.Int64  -> C.Type.Integer (C.IntKind.Int64)
            | PrimitiveTypeCode.Boolean -> C.Type.Bool
            | PrimitiveTypeCode.Void -> C.Type.Void
            | PrimitiveTypeCode.Invalid -> C.Type.Bogus
            | PrimitiveTypeCode.Float32 -> C.Type.Primitive C.PrimKind.Float32
            | PrimitiveTypeCode.Float64 -> C.Type.Primitive C.PrimKind.Float64
            | PrimitiveTypeCode.UIntPtr
            | PrimitiveTypeCode.IntPtr -> C.Type.PhysPtr(C.Type.Void)
            | PrimitiveTypeCode.NotPrimitive ->
              let (hasit, ret) = typesMap.TryGetValue(typeDef)
              if hasit then C.Type.Ref (ret)
              elif typeDef.IsEnum then this.DoType typeDef.UnderlyingType
              else 
                let fields = [ for f in typeDef.Fields -> f ]
                let members = [ for m in typeDef.Members -> m ] // contains fields as well as nested types
                // TODO check embedded structs in unions
                let name =
                  match typeDef with
                    | :? INamespaceTypeDefinition as n -> n.Name.Value
                    | :? INestedTypeDefinition as n -> n.ContainingTypeDefinition.ToString() + "." + n.Name.Value
                    | _ -> die()
                let mathPref = "_vcc_math_type_"
                let datatypeDefinition = this.TryGetDatatypeDefinition typeDef
                let contract = contractProvider.GetTypeContractFor(typeDef)
                let isMathRecord = contract <> null && Seq.length contract.ContractFields > 0 && name.StartsWith mathPref
                     
                if name.StartsWith mathPref && datatypeDefinition = null && not isMathRecord then
                  if name.Substring(mathPref.Length) = "\\label"
                    then C.Type.SecLabel None
                    else
                      let typeName = name.Substring (mathPref.Length)
                      let td = C.Type.MathTd typeName
                      typesMap.Add(typeDef, td)
                      typeNameMap.Add(td.Name, td)
                      topDecls <- C.Top.TypeDecl (td) :: topDecls
                      C.Type.Ref td
                else if name = "_vcc_claim_struct" || name = "\\claim_struct" then
                  C.Type.Claim
                else if name.Contains ("._FixedArrayOfSize") then
                  match fields with
                    | f :: _ ->
                      let eltype = this.DoType f.Type
                      C.Type.Array (eltype, int typeDef.SizeOf / eltype.SizeOf)
                    | _ -> die()
                else if name = SystemDiagnosticsContractsCodeContractTypedPtr then
                  C.Type.ObjectT
                else if name = SystemDiagnosticsContractsCodeContractBigInt then
                  C.Type.MathInteger C.Signed
                else if name = SystemDiagnosticsContractsCodeContractBigNat then
                  C.Type.MathInteger C.Unsigned
                else if name = SystemDiagnosticsContractsCodeContractObjset then
                  C.Type.Math "\\objset"
                else              
                  let tok = token typeDef
                  let totalOffset f = MemberHelper.GetFieldBitOffset f + f.Offset
                  let notAllEqual = function
                    | x :: xs -> List.exists (fun y -> y <> x) xs
                    | _ -> die()                        
                  let customAttr = convCustomAttributes tok typeDef.Attributes
                  let customAttr =
                    if isMathRecord then
                      C.VccAttr (C.AttrRecord, "") :: customAttr
                    else customAttr
                  let specFromContract = 
                    match contract with
                      | :? VccTypeContract as vccTypeContract -> vccTypeContract.IsSpec
                      | _ -> false
                  let td = 
                    { Token = tok
                      Name = name
                      Fields = []
                      Invariants = []
                      CustomAttr = customAttr
                      SizeOf = int typeDef.SizeOf
                      IsNestedAnon = false
                      GenerateEquality = CAST.StructEqualityKind.NoEq
                      Kind = 
                        // Cci does not know about unions, so a union for us is a struct with more than one member whose all offsets are equal
                        if List.length fields <= 1 || notAllEqual (List.map totalOffset fields) then
                          C.TypeKind.Struct
                        else
                          C.TypeKind.Union
                      Parent =
                        match typeDef with
                        | :? NestedTypeDefinition as nestedType ->
                          match typesMap.TryGetValue(nestedType.ContainingTypeDefinition) with
                          | (true, parent) -> Some parent
                          | _ -> None
                        | _ -> None
                      IsSpec = specFromContract || hasCustomAttr C.AttrRecord customAttr
                      IsVolatile = false
                      UniqueId = C.unique()
                      DataTypeOptions = []
                    } : C.TypeDecl
                                      
                  // TODO?
                  let td =
                    if td.Name = "Object" && td.SizeOf = 0 then
                      { td with Name = "#Object"; SizeOf = C.Type.ObjectT.SizeOf }
                    else td
                  
                  let minOffset = 
                    match fields with
                      | f :: _ -> int f.Offset
                      | _ -> 0
                  let minOffset = List.fold (fun off (f:IFieldDefinition) -> 
                                                    if int f.Offset < off then int f.Offset else off) minOffset fields
                  typesMap.Add(typeDef, td)
                  typeNameMap.Add(td.Name, td)
                  topDecls <- C.Top.TypeDecl (td) :: topDecls
                  
                  let trField isSpec (f:IFieldDefinition) =
                    let fldVolatile = 
                      match f with
                        | :? Microsoft.Cci.Ast.FieldDefinition as fd -> fd.FieldDeclaration.IsVolatile
                        | _ -> false
                      
                    let name =
                      match f with
                        | :? Microsoft.Cci.Ast.FieldDefinition as fd ->
                          match fd.FieldDeclaration with
                            | :? Microsoft.Research.Vcc.AnonymousFieldDefinition as anonFd when anonFd.SpecMemberName <> null -> "#" + anonFd.SpecMemberName.Name.Value
                            | _ -> f.Name.Value
                        | _ -> f.Name.Value

                    let t = this.DoType (f.Type)
                    let tok = token f
                    let isSpec = isSpec || td.IsSpec
                    let isSpec =
                      match t with
                        | C.Type.Map(_,_) when not isSpec ->
                          helper.Error(tok, 9632, "fields of map type must be declared as specification fields", None)
                          true
                        | _ -> isSpec

                    if f.IsBitField then
                      match t with 
                        | C.Type.Integer _ -> ()
                        | _ -> helper.Error(tok, 9739, "bit field of unsupported type '" + t.ToString() + "'", None)
                    let res =
                      { Name = name
                        Token = tok
                        Type = t
                        Parent = td
                        IsSpec = isSpec
                        IsVolatile = fldVolatile
                        Offset =
                          if f.IsBitField then                               
                            C.FieldOffset.BitField (int f.Offset - minOffset, int (MemberHelper.GetFieldBitOffset f), int f.BitLength)
                          else match t with
                                | C.Type.Array(elType, 0) ->
                                  // zero-size arrays start after the current type with the proper alignment
                                  let alignment = elType.SizeOf // TODO: this should really be computed via TypeHelper.GetAlignment
                                  let offset = ((td.SizeOf + alignment - 1) / alignment) * alignment
                                  C.FieldOffset.Normal (offset - minOffset)
                                | _ -> C.FieldOffset.Normal (int f.Offset - minOffset)
                        CustomAttr = convCustomAttributes (token f) f.Attributes
                        UniqueId = C.unique()
                      } : C.Field               
                    fieldsMap.Add(f, res)
                    res
                        
                  let trMember isSpec (m:ITypeDefinitionMember) =
                    match m with
                    | :? IFieldDefinition as f -> Some(trField isSpec f)
                    | :? NestedTypeDefinition as t -> 
                      this.DoTypeDefinition t
                      None
                    | _ -> None
                    
                  let rec trMembers isSpec = function
                  | [] -> []
                  | m :: ms ->
                    match trMember isSpec m with
                    | None -> trMembers isSpec ms
                    | Some(f) -> f :: trMembers isSpec ms
                  
                  //if (contract <> null) then contract.HasErrors |> ignore

                  if datatypeDefinition <> null then
                    td.DataTypeOptions <- 
                      datatypeDefinition.Constructors |> Seq.map (fun fd -> this.LookupMethod fd.ResolvedMethod) |> Seq.toList
                    td.Kind <- C.TypeKind.MathType
                    let pref = "_vcc_math_type_"
                    td.Name <- td.Name.Substring pref.Length

                  match fields with
                    | [] when not (VccScopedName.IsGroupType(typeDef)) && not td.IsSpec ->
                      if contract <> null && Seq.length contract.ContractFields > 0 then
                        helper.Error (tok, 9620, "need at least one physical field in structure, got only ghost fields", None)
                      // forward declaration
                      C.Type.Ref td
                    | _ ->
                      td.Fields <- trMembers false members

                      if td.SizeOf < 1  && not td.IsSpec then
                        helper.Oops(td.Token, "type " + td.Name + " smaller than 1 byte!")
                        die()
                                            
                      if contract <> null then
                        td.Fields <- td.Fields @ [ for f in contract.ContractFields -> trField true f ]
                        if not (Visitor.CheckHasError(contract)) then
                          finalActions.Enqueue (fun () ->
                            td.Invariants <- [ for inv in contract.Invariants -> this.DoInvariant inv])
                       
                      let reportErrorForDuplicateFields fields =
                        let seenFields = new Dict<string,C.Field>()
                        let addFieldOrReportError (f:C.Field) =
                          if f.Name = "" then ()
                          else 
                            match seenFields.TryGetValue f.Name with
                              | true, f' -> 
                                let msg = "'" + f.Name + "' : '" + (if td.Kind = C.TypeKind.Struct then "struct" else "union") + "' member redefinition"
                                helper.Error(f.Token, 9677, msg, Some(f'.Token))
                              | _ -> seenFields.Add(f.Name, f)
                        List.iter addFieldOrReportError fields
                        
                      reportErrorForDuplicateFields td.Fields
                      C.Type.Ref (td)
                
            | v ->
              oopsLoc typeDef ("bad value of typecode: " + v.ToString())
              die()

    // Range checks are added later, in transformers
    member this.GetExpressionAndBindings (arguments:System.Collections.Generic.IEnumerable<IExpression>, kind:C.QuantKind, methodCall:IMethodCall) =
      let getReturnStmt (blockStmt:IBlockStatement) : IExpression =
        let mutable found = false
        let mutable retval = CodeDummy.Expression
        for stmt in blockStmt.Statements do
          if (found = false) then
            let retStmt = stmt :?> IReturnStatement
            if (retStmt <> null) then
              if (retStmt.Expression <> null) then 
                found <- true
                retval <- retStmt.Expression
        retval
        
      let mutable (bindings:list<C.Variable>) = []
      let argEnumerator = arguments.GetEnumerator()
      if (argEnumerator.MoveNext() <> true) then
        (cTrue, bindings, [])
      else 
        let anonymousDelegate = (argEnumerator.Current :?> IAnonymousDelegate)
        if (anonymousDelegate = null) then
          oopsLoc methodCall "found errors in quantifier body, faking it to be 'true'"
          (cTrue, bindings, [])
        else
          let parEnumerator = anonymousDelegate.Parameters.GetEnumerator()
          if (parEnumerator.MoveNext() <> true) then
            oopsLoc anonymousDelegate ("found errors in quantifier body, faking it to be 'true'")
            (cTrue, bindings, [])
          else
            let par = parEnumerator.Current
            let parType = par.Type.ResolvedType
            let var = C.Variable.CreateUnique par.Name.Value (this.DoType (parType)) C.VarKind.QuantBound
            localsMap.Add (par, var)
            
            let name = par.Name.Value
            match localsMap.TryGetValue name with
              | true, prev ->
                helper.Error(token par, 9675, "Quantified variable '" + name + "' clashes with earlier declaration", None)
              | false, _ ->
                localsMap.Add (name, var)
            
            bindings <- var :: bindings
            let body = getReturnStmt(anonymousDelegate.Body)
            if Visitor.CheckHasError(body) then
              oopsLoc body "found errors in quantifier body, faking it to be 'true'"
              (cTrue, bindings, [])
            else
              let resultExpr = this.DoIExpression (body)
              let rec collect addVars = function
                | C.Quant (_, { Variables = vars; Body = b }) ->
                  collect (vars @ addVars) b
                | _ -> addVars
              let addVars = collect [] resultExpr
              for v in addVars do
                localsMap.Add (v.Name, v)
              let triggers = this.GetTriggers(methodCall)
              for v in var :: addVars do
                localsMap.Remove v.Name |> ignore
              (resultExpr, bindings, triggers)

    member this.GetTriggers (o:obj) =
      let doTrigger (expr:Expression) = 
        let ec = { Token = token expr; Type = this.DoType (expr.Type) } : C.ExprCommon
        match expr with
        | :? VccLabeledExpression as lblExpr ->
          let lbl = C.Expr.Label(ec, {Name = lblExpr.Label.Name.Value})
          match lblExpr.Expression with
            | :? DummyExpression -> C.Expr.Macro(ec, "labeled_expr", [lbl])
            | e -> 
              let e' = this.DoIExpression(e.ProjectAsIExpression())
              C.Expr.Macro(ec, "labeled_expr", [lbl; e'])
        | _ -> this.DoIExpression(expr.ProjectAsIExpression())
      let triggers = contractProvider.GetTriggersFor(o)
      match triggers with
        | null -> []
        | _ -> 
          [ for triggerExprs in triggers -> 
            [ for triggerExpr in triggerExprs -> doTrigger triggerExpr] ]
    
    member this.DoQuant (methodCall:IMethodCall) = 
      let methodToCall = methodCall.MethodToCall.ResolvedMethod
      let methodName = methodToCall.Name.Value
      let kind = match methodName with 
                   | "Exists" -> C.Exists
                   | "ForAll" -> C.Forall
                   | "Lambda" -> C.Lambda
                   | _ -> die()
      let (body, bindings, triggers) = this.GetExpressionAndBindings(methodCall.Arguments, kind, methodCall)
      { 
        Variables = bindings
        Triggers = triggers
        Condition = None // TODO: figure out where condition is in code model
        Body = body
        Kind = kind
        Weight = ""
      } : C.QuantData 
    
    member this.DoLoopContract (loop:IStatement) =
      let contract = contractProvider.GetLoopContractFor loop
      if (contract <> null) then Visitor.CheckHasError(contract) |> ignore
      let conds =
        if contract = null then []
        else [ for i in contract.Invariants -> C.Expr.MkAssert (this.DoIExpression i.Condition) ] @
             [ for v in contract.Variants ->
                  let expr = this.DoIExpression v                 
                  C.Expr.MkAssert (C.Expr.Macro ({ expr.Common with Type = C.Type.Bool }, "loop_variant", [expr]))] @
             [ for w in contract.Writes -> 
                  let set = this.DoIExpression w                    
                  C.Expr.MkAssert (C.Expr.Macro ({ set.Common with Type = C.Type.Bool }, "loop_writes", [set]))]
      C.Expr.Macro (C.bogusEC, "loop_contract", conds)

    member this.DoneVisitingAssembly(assembly:IAssembly) : unit = 
      if globalsType <> null then
        let contract = contractProvider.GetTypeContractFor globalsType
        if contract <> null then
          Visitor.CheckHasError(contract) |> ignore
          for inv in contract.Invariants do
            if inv.IsAxiom then
              topDecls <- C.Top.Axiom (this.DoIExpression inv.Condition) :: topDecls
              
      let typedefs = glist []
      (assembly :?> VccAssembly).Compilation.Parts |> 
          Seq.iter (fun m -> m.GlobalDeclarationContainer.GlobalMembers |> 
                                Seq.iter (function
                                            | :? TypedefDeclaration as decl -> typedefs.Add decl
                                            | _ -> ()))
      let rec doTd stripPtr = function
        | (name, C.Ptr tp) when stripPtr -> doTd false (name, tp)
        | (name, C.Type.Ref td) ->
          let cdot = td.Name.LastIndexOf ".."
          if cdot > 0 && td.Name.Substring (cdot + 2) |> Seq.forall System.Char.IsDigit then
            td.Name <- name
        | _ -> ()
      
      let typedefs = typedefs |> Seq.map (fun decl -> (decl.Name.Value, decl.Type.ResolvedType |> this.DoType)) |> Seq.toList
      typedefs |> Seq.iter (doTd false)
      typedefs |> Seq.iter (doTd true)
      topDecls <- List.rev topDecls        

    member this.VisitOnly (assembly:IAssembly, fnNames) : unit =
      let isRequired sym =
        let syms = [ "malloc" ]
        List.exists (fun elem -> elem = sym) syms
      let ns = assembly.NamespaceRoot
      doingEarlyPruning <- true
      requestedFunctions <- Seq.toList fnNames
      for n in ns.Members do 
        let ncmp s = s = n.Name.Value
        if n.Name.Value.StartsWith("_vcc") || n.Name.Value.StartsWith("\\") || List.exists ncmp requestedFunctions || isRequired n.Name.Value then
          n.Dispatch(this)
      this.DoneVisitingAssembly assembly

    //
    // Source Visitor Implementation, use to recover unfolded version of folded constant expressions
    //

    override this.Visit(conversion: Conversion) = 
      exprRes <- C.Expr.Cast (this.ExprCommon (conversion :> Expression), C.Unchecked, this.DoExpression (conversion.ValueToConvert))

    override this.Visit(cast: Cast) = 
      exprRes <- C.Expr.Cast (this.ExprCommon (cast :> Expression), C.Unchecked, this.DoExpression (cast.ValueToCast))

    override this.Visit(constant: CompileTimeConstant) =
      exprRes <- this.DoCompileTimeConstant(constant)

    override this.Visit(simpleName : SimpleName) = 
      exprRes <- this.DoIExpression(simpleName.ProjectAsIExpression())

    override this.Visit(parenthesis : Parenthesis) = 
      exprRes <- this.DoExpression(parenthesis.ParenthesizedExpression)

    override this.Visit(addition : Addition) =
      exprRes <- this.DoBinary("+", addition)

    override this.Visit(bitwiseAnd: BitwiseAnd) = 
      exprRes <- this.DoBinary("&", bitwiseAnd)

    override this.Visit(bitwiseOr: BitwiseOr) = 
      exprRes <- this.DoBinary("|", bitwiseOr)

    override this.Visit(checkedExpression: CheckedExpression) = 
      exprRes <- this.DoExpression(checkedExpression.Operand)

    override this.Visit(conditional: Conditional) = 
      exprRes <- C.Expr.Macro (this.ExprCommon (conditional :> Expression), "ite",
                               [this.DoIExpression (conditional :> IConditional).Condition
                                this.DoExpression conditional.ConvertedResultIfTrue;
                                this.DoExpression conditional.ConvertedResultIfFalse])

    override this.Visit(defaultValue: DefaultValue) = 
      exprRes <- this.DoIExpression(defaultValue.ProjectAsIExpression())

    override this.Visit(division: Division) =
      exprRes <- this.DoBinary("/", division)

    override this.Visit(exclusiveOr: ExclusiveOr) =
      exprRes <- this.DoBinary("^", exclusiveOr)

    override this.Visit(equality: Equality) = 
      exprRes <- this.DoIExpression(equality.ProjectAsIExpression())

    override this.Visit(greaterThan: GreaterThan) = 
      exprRes <- this.DoIExpression(greaterThan.ProjectAsIExpression())

    override this.Visit(greaterThanOrEqual: GreaterThanOrEqual) = 
      exprRes <- this.DoIExpression(greaterThanOrEqual.ProjectAsIExpression())

    override this.Visit(lessThan: LessThan) = 
      exprRes <- this.DoIExpression(lessThan.ProjectAsIExpression())

    override this.Visit(lessThanOrEqual: LessThanOrEqual) = 
      exprRes <- this.DoIExpression(lessThanOrEqual.ProjectAsIExpression())

    override this.Visit(logicalOr : LogicalOr) = 
      exprRes <- this.DoIExpression(logicalOr.ProjectAsIExpression())

    override this.Visit(logicalAnd: LogicalAnd) = 
      exprRes <- this.DoIExpression(logicalAnd.ProjectAsIExpression())

    override this.Visit(logicalNot: LogicalNot) = 
      exprRes <- this.DoUnary("!", logicalNot)

    override this.Visit(implies: Implies) = 
      exprRes <- this.DoBinary("==>", implies)

    override this.Visit(isTrue: IsTrue) = 
      exprRes <- C.Expr.Cast (this.ExprCommon (isTrue :> Expression), C.Unchecked, this.DoExpression (isTrue.ConvertedOperand))

    override this.Visit(isFalse: IsFalse) = 
      exprRes <- C.Expr.Cast (this.ExprCommon (isFalse :> Expression), C.Unchecked, this.DoExpression (isFalse.ConvertedOperand))

    override this.Visit(leftShift: LeftShift) =
      exprRes <- this.DoBinary("<<", leftShift)

    override this.Visit(modulus : Modulus) = 
      exprRes <- this.DoBinary("%", modulus)

    override this.Visit(multiplication : Multiplication) = 
      exprRes <- this.DoBinary("*", multiplication)

    override this.Visit(notEquality : NotEquality) = 
      exprRes <- this.DoBinary("!=", notEquality)

    override this.Visit(onesComplement : OnesComplement) = 
      exprRes <- this.DoUnary("~", onesComplement)

    override this.Visit(qualifiedName : QualifiedName) = 
      exprRes <- this.DoIExpression(qualifiedName.ProjectAsIExpression())

    override this.Visit(rightShift : RightShift) = 
      exprRes <- this.DoBinary(">>", rightShift)

    override this.Visit(sizeOf : SizeOf) = 
      exprRes <- this.DoSizeOf(sizeOf)

    override this.Visit(subtraction : Subtraction) = 
      exprRes <- this.DoBinary("-", subtraction)

    override this.Visit(unaryNegation : UnaryNegation) = 
      exprRes <- this.DoUnary("-", unaryNegation)
    
    override this.Visit(unaryPlus : UnaryPlus) = 
      exprRes <- this.DoUnary("+", unaryPlus)

    override this.Visit(uncheckedExpression : UncheckedExpression) = 
      exprRes <- this.DoExpression(uncheckedExpression.Operand)

    override this.Visit(additionAssignment : AdditionAssignment) = assert false
    override this.Visit(addressableExpression : AddressableExpression) = assert false
    override this.Visit(addressDereference : AddressDereference) = assert false
    override this.Visit(addressOf : AddressOf) = assert false
    override this.Visit(aliasDeclaraion : AliasDeclaration) = assert false
    override this.Visit(aliasQualifiedName : AliasQualifiedName) = assert false
    override this.Visit(anonymousMethod : AnonymousMethod) = assert false
    override this.Visit(attributeTypeExpression: AttributeTypeExpression) = assert false
    override this.Visit(arrayTypeExpression: ArrayTypeExpression) = assert false
    override this.Visit(assertStatement: AssertStatement) = assert false
    override this.Visit(assignment: Assignment) = assert false
    override this.Visit(assumeStatement: AssumeStatement) = assert false
    override this.Visit(baseClassReference: BaseClassReference) = assert false
    override this.Visit(bitwiseAndAssignment: BitwiseAndAssignment) = assert false
    override this.Visit(bitwiseOrAssignment: BitwiseOrAssignment) = assert false
    override this.Visit(blockExpression: BlockExpression) = assert false
    override this.Visit(block: BlockStatement) = assert false
    override this.Visit(castIfPossible: CastIfPossible) = assert false
    override this.Visit(catchClause: CatchClause) = assert false
    override this.Visit(checkIfInstance: CheckIfInstance) = assert false
    override this.Visit(clearLastErrorStatement: ClearLastErrorStatement) = assert false
    override this.Visit(comma: Comma) = assert false
    override this.Visit(compilation: Compilation) = assert false
    override this.Visit(compilationPart: CompilationPart) = assert false
    override this.Visit(conditionalStatement: ConditionalStatement) = assert false
    override this.Visit(continueStatement: ContinueStatement) = assert false
    override this.Visit(createAnonymousObject: CreateAnonymousObject) = assert false
    override this.Visit(createArray: CreateArray) = assert false
    override this.Visit(createDelegateInstance: CreateDelegateInstance) = assert false
    override this.Visit(implicitlyTypedArrayCreate: CreateImplicitlyTypedArray) = assert false
    override this.Visit(createObjectInstance: CreateObjectInstance) = assert false
    override this.Visit(stackArrayCreate: CreateStackArray) = assert false
    override this.Visit(indexer: Indexer) = assert false
    override this.Visit(disableOnErrorHandler: DisableOnErrorHandler) = assert false
    override this.Visit(divisionAssignment: DivisionAssignment) = assert false
    override this.Visit(doWhileStatement: DoWhileStatement) = assert false
    override this.Visit(documentation: Documentation) = assert false
    override this.Visit(documentationAttribute: DocumentationAttribute) = assert false
    override this.Visit(documentationElement: DocumentationElement) = assert false
    override this.Visit(doUntilStatement: DoUntilStatement) = assert false
    override this.Visit(emptyStatement: EmptyStatement) = assert false
    override this.Visit(emptyTypeExpression: EmptyTypeExpression) = assert false
    override this.Visit(endStatement: EndStatement) = assert false
    override this.Visit(eraseStatement: EraseStatement) = assert false
    override this.Visit(errorStatement: ErrorStatement) = assert false
    override this.Visit(eventDeclaration: EventDeclaration) = assert false
    override this.Visit(exclusiveOrAssignment: ExclusiveOrAssignment) = assert false
    override this.Visit(breakStatement: BreakStatement) = assert false
    override this.Visit(exists: Exists) = assert false
    override this.Visit(exponentiation: Exponentiation) = assert false
    override this.Visit(expressionStatement: ExpressionStatement) = assert false
    override this.Visit(fieldDeclaration: FieldDeclaration) = assert false
    override this.Visit(fixedStatement: FixedStatement) = assert false
    override this.Visit(forall: Forall) = assert false
    override this.Visit(forEachStatement: ForEachStatement) = assert false
    override this.Visit(forRangeStatement: ForRangeStatement) = assert false
    override this.Visit(forStatement: ForStatement) = assert false
    override this.Visit(genericInstanceExpression: GenericInstanceExpression) = assert false
    override this.Visit(genericMethodParameterDeclaration: GenericMethodParameterDeclaration) = assert false
    override this.Visit(genericTypeInstanceExpression: GenericTypeInstanceExpression) = assert false
    override this.Visit(gotoStatement: GotoStatement) = assert false
    override this.Visit(gotoSwitchCaseStatement: GotoSwitchCaseStatement) = assert false
    override this.Visit(genericTypeInstance: Immutable.GenericTypeInstance) = assert false
    override this.Visit(genericTypeParameterDeclaration: GenericTypeParameterDeclaration) = assert false
    override this.Visit(getTypeOfTypedReference: GetTypeOfTypedReference) = assert false
    override this.Visit(getValueOfTypedReference: GetValueOfTypedReference) = assert false
    override this.Visit(implicitQualifier: ImplicitQualifier) = assert false
    override this.Visit(initializeObject: InitializeObject) = assert false
    override this.Visit(integerDivision: IntegerDivision) = assert false
    override this.Visit(labeledStatement: LabeledStatement) = assert false
    override this.Visit(lambda: Lambda) = assert false
    override this.Visit(lambdaParameter: LambdaParameter) = assert false
    override this.Visit(leftShiftAssignment: LeftShiftAssignment) = assert false
    override this.Visit(liftedConversion: LiftedConversion) = assert false
    override this.Visit(like: Like) = assert false
    override this.Visit(localDeclaration: LocalDeclaration) = assert false
    override this.Visit(localDeclarationsStatement: LocalDeclarationsStatement) = assert false
    override this.Visit(lockStatement: LockStatement) = assert false
    override this.Visit(_ : AttachEventHandlerStatement) = assert false
    override this.Visit(_ : LoopInvariant) = assert false
    override this.Visit(_ : MakeTypedReference) = assert false
    override this.Visit(_ : Immutable.ManagedPointerType) = assert false
    override this.Visit(_ : ManagedPointerTypeExpression) = assert false
    override this.Visit(_ : MethodBody) = assert false
    override this.Visit(_ : MethodCall) = assert false
    override this.Visit(_ : MethodDeclaration) = assert false
    override this.Visit(_ : MethodGroup) = assert false
    override this.Visit(_ : ModulusAssignment) = assert false
    override this.Visit(_ : MultiplicationAssignment) = assert false
    override this.Visit(_ : NamedArgument) = assert false
    override this.Visit(_ : NameDeclaration) = assert false
    override this.Visit(_ : NamedTypeExpression) = assert false
    override this.Visit(_ : NamespaceClassDeclaration) = assert false
    override this.Visit(_ : NamespaceDeclaration) = assert false
    override this.Visit(_ : NamespaceDelegateDeclaration) = assert false
    override this.Visit(_ : NamespaceEnumDeclaration) = assert false
    override this.Visit(_ : NamespaceImportDeclaration) = assert false
    override this.Visit(_ : NamespaceInterfaceDeclaration) = assert false
    override this.Visit(_ : NamespaceReferenceExpression) = assert false
    override this.Visit(_ : NamespaceStructDeclaration) = assert false
    override this.Visit(_ : NestedClassDeclaration) = assert false
    override this.Visit(_ : NestedNamespaceDeclaration) = assert false
    override this.Visit(_ : NestedDelegateDeclaration) = assert false
    override this.Visit(_ : NestedEnumDeclaration) = assert false
    override this.Visit(_ : NestedInterfaceDeclaration) = assert false
    override this.Visit(_ : NestedStructDeclaration) = assert false
    override this.Visit(_ : NonNullTypeExpression) = assert false
    override this.Visit(_ : NullableTypeExpression) = assert false
    override this.Visit(_ : NullCoalescing) = assert false
    override this.Visit(_ : OnErrorGotoStatement) = assert false
    override this.Visit(_ : OnErrorResumeNextStatement) = assert false
    override this.Visit(_ : OptionDeclaration) = assert false
    override this.Visit(_ : OutArgument) = assert false
    override this.Visit(_ : ParameterDeclaration) = assert false
    override this.Visit(_ : PointerTypeExpression) = assert false
    override this.Visit(_ : PopulateCollection) = assert false
    override this.Visit(_ : Postcondition) = assert false
    override this.Visit(_ : PostfixDecrement) = assert false
    override this.Visit(_ : PostfixIncrement) = assert false
    override this.Visit(_ : Precondition) = assert false
    override this.Visit(_ : PrefixDecrement) = assert false
    override this.Visit(_ : PrefixIncrement) = assert false
    override this.Visit(_ : PropertyDeclaration) = assert false
    override this.Visit(_ : PropertySetterValue) = assert false
    override this.Visit(_ : RaiseEventStatement) = assert false
    override this.Visit(_ : Range) = assert false
    override this.Visit(_ : RedimensionClause) = assert false
    override this.Visit(_ : RedimensionStatement) = assert false
    override this.Visit(_ : RefArgument) = assert false
    override this.Visit(_ : ReferenceEquality) = assert false
    override this.Visit(_ : ReferenceInequality) = assert false
    override this.Visit(_ : RemoveEventHandlerStatement) = assert false
    override this.Visit(_ : ResumeLabeledStatement) = assert false
    override this.Visit(_ : ResumeNextStatement) = assert false
    override this.Visit(_ : ResumeStatement) = assert false
    override this.Visit(_ : ResourceUseStatement) = assert false
    override this.Visit(_ : RethrowStatement) = assert false
    override this.Visit(_ : ReturnStatement) = assert false
    override this.Visit(_ : ReturnValue) = assert false
    override this.Visit(_ : RightShiftAssignment) = assert false
    override this.Visit(_ : UnsignedRightShift) = assert false
    override this.Visit(_ : RootNamespaceExpression) = assert false
    override this.Visit(_ : RuntimeArgumentHandleExpression) = assert false
    override this.Visit(_ : SignatureDeclaration) = assert false
    override this.Visit(_ : Slice) = assert false
    override this.Visit(_ : SourceCustomAttribute) = assert false
    override this.Visit(_ : StopStatement) = assert false
    override this.Visit(_ : StringConcatenation) = assert false
    override this.Visit(_ : SubtractionAssignment) = assert false
    override this.Visit(_ : SwitchCase) = assert false
    override this.Visit(_ : SwitchStatement) = assert false
    override this.Visit(_ : TargetExpression) = assert false
    override this.Visit(_ : ThisReference) = assert false
    override this.Visit(_ : ThrownException) = assert false
    override this.Visit(_ : ThrowStatement) = assert false
    override this.Visit(_ : TryCatchFinallyStatement) = assert false
    override this.Visit(_ : TypeDeclaration) = assert false
    override this.Visit(_ : TypeInvariant) = assert false
    override this.Visit(_ : TypeOf) = assert false
    override this.Visit(_ : UnitSetAliasDeclaration) = assert false
    override this.Visit(_ : UntilDoStatement) = assert false
    override this.Visit(_ : WhileDoStatement) = assert false
    override this.Visit(_ : WithStatement) = assert false
    override this.Visit(_ : YieldBreakStatement) = assert false
    override this.Visit(_ : YieldReturnStatement) = assert false

    // The idea is to only do dispatch into children, and not put any complicated
    // logic inside Visit(***) methods. The logic should be up, in the Do*** methods.
    // This is however not yet the case.
    interface IVccCodeVisitor with    

      member this.Visit (arrayTypeReference:IArrayTypeReference) : unit = assert false

      member this.Visit (assembly:IAssembly) : unit =
        let ns = assembly.NamespaceRoot
        ns.Dispatch(this)
        this.DoneVisitingAssembly assembly
             
      member this.Visit (copyMemoryStmt : ICopyMemoryStatement) : unit = assert false

      member this.Visit (fillMemoryStmt : IFillMemoryStatement) : unit = assert false

      member this.Visit (peSection:IPESection) : unit = assert false
                          
      member this.Visit (assemblyReference:IAssemblyReference) : unit = assert false

      member this.Visit (customAttribute:ICustomAttribute) : unit = assert false

      member this.Visit (customModifier:ICustomModifier) : unit = assert false

      member this.Visit (eventDefinition:IEventDefinition) : unit = assert false

      member this.Visit (fieldDefinition:IFieldDefinition) : unit = assert false

      member this.Visit (fieldReference:IFieldReference) : unit = assert false

      member this.Visit (fileReference:IFileReference) : unit = assert false
      
      member this.Visit (platformInvokeInformation:IPlatformInvokeInformation) : unit = assert false

      member this.Visit (specializedEventDefinition:ISpecializedEventDefinition) : unit = assert false

      member this.Visit (specializedFieldDefinition:ISpecializedFieldDefinition) : unit = assert false

      member this.Visit (specializedFieldReference:ISpecializedFieldReference) : unit = assert false

      member this.Visit (specializedMethodDefinition:ISpecializedMethodDefinition) : unit = assert false

      member this.Visit (specializedMethodReference:ISpecializedMethodReference) : unit = assert false

      member this.Visit (specializedPropertyDefinition:ISpecializedPropertyDefinition) : unit = assert false

      member this.Visit (specializedNestedTypeDefinition:ISpecializedNestedTypeDefinition) : unit = assert false

      member this.Visit (specializedNestedTypeReference:ISpecializedNestedTypeReference) : unit = assert false

      member this.Visit (localDefinition:ILocalDefinition) : unit = assert false

      member this.Visit (operation:IOperation) : unit = assert false

      member this.Visit (operationExceptionInformation:IOperationExceptionInformation) : unit = assert false

      member this.VisitReference (localDefinition:ILocalDefinition) : unit = assert false

      member this.VisitReference (parameterDefinition:IParameterDefinition) : unit = assert false

      member this.Visit (functionPointerTypeReference:IFunctionPointerTypeReference) : unit =
        let meth = functionPointerTypeReference :> ISignature
        let cont =
          match Seq.toList meth.Parameters with
            | x :: _ -> x.ContainingSignature
            | _ -> meth
        let td =
          match functionPointerMap.TryGetValue cont with
            | true, td -> td
            | _ ->
              this.DoMethod(meth, true, true)
              let fndecl = this.LookupMethod meth
              let td = 
                { 
                  Token = C.bogusToken
                  Kind = C.FunctDecl fndecl
                  Name = fndecl.Name
                  Fields = []
                  Invariants = []
                  CustomAttr = []
                  SizeOf = C.Type.ObjectT.SizeOf
                  IsNestedAnon = false
                  GenerateEquality = CAST.StructEqualityKind.NoEq
                  Parent = None
                  IsVolatile = false
                  IsSpec = false
                  DataTypeOptions = []
                  UniqueId = C.unique()
                 } : C.TypeDecl
              topDecls <- C.Top.TypeDecl td :: topDecls
              functionPointerMap.Add (cont, td)
              td
        typeRes <- C.Type.PhysPtr (C.Type.Ref td)

      member this.Visit (genericMethodInstanceReference:IGenericMethodInstanceReference) : unit = assert false

      member this.Visit (genericMethodParameter:IGenericMethodParameter) : unit = 
        typeRes <- C.Type.TypeVar({ Name = genericMethodParameter.Name.Value })

      member this.Visit (genericMethodParameterReference:IGenericMethodParameterReference) : unit = assert false

      member this.Visit (globalFieldDefinition:IGlobalFieldDefinition) : unit =
        this.DoGlobal globalFieldDefinition |> ignore
                                  
      member this.Visit (globalMethodDefinition:IGlobalMethodDefinition) : unit =
        globalsType <- globalMethodDefinition.ContainingTypeDefinition
        match globalMethodDefinition.Name.Value with
          | "_vcc_in_state" | "\\at"
          | "_vcc_approves" | "\\approves"
          | "_vcc_deep_struct_eq" | "_vcc_shallow_struct_eq" | "_vcc_known" | "\\deep_eq" | "\\shallow_eq" | "\\size"
          | "\\test_classifier" | "\\downgrade_to" | "\\current_context" | "\\label_of" | "\\lblset_leq"
          | "\\labeled_expression"
          | "\\new_club" | "\\add_member" | "\\is_member" -> ()
          | x when x.StartsWith "\\castlike_" -> ()
          | _ -> this.DoMethod (globalMethodDefinition, false, false)

      member this.Visit (genericTypeInstanceReference:IGenericTypeInstanceReference) : unit =
        let rec isAdmissibleMapDomainType = function
          | C.Volatile t -> isAdmissibleMapDomainType t
          | C.Type.Ref td -> td.IsMathValue // TODO exclude big types
          | C.TypeVar _
          | C.Array _
          | C.Void -> false
          | _ -> true
        let rec isAdmissibleMapRangeType = function
          | C.Volatile t -> isAdmissibleMapRangeType t
          | C.Void -> false
          | _ -> true

        if genericTypeInstanceReference.GenericType.ToString () = SystemDiagnosticsContractsCodeContractMap then
          match [ for t in genericTypeInstanceReference.GenericArguments -> this.DoType t ] with
            | [t1; t2] ->
              let mapTypes = [ for t in genericTypeInstanceReference.GenericArguments -> t ]

              let t1 = if isAdmissibleMapDomainType t1 then t1
                       else 
                         helper.Error(token (mapTypes.Item(0)), 9702, "Illegal type '" + t1.ToString() + "' in map domain.", None)
                         C.Type.Bogus
              let t2 = if isAdmissibleMapRangeType t2 then t2
                       else 
                         helper.Error(token (mapTypes.Item(1)), 9721, "Illegal type '" + t2.ToString() + "' in map range.", None)
                         C.Type.Bogus
              typeRes <- C.Type.Map (t1, t2)
            | _ -> assert false
        else
          assert false
        
      member this.Visit (genericTypeParameter:IGenericTypeParameter) : unit = assert false

      member this.Visit (genericTypeParameterReference:IGenericTypeParameterReference) : unit = assert false

      member this.Visit (managedPointerTypeReference:IManagedPointerTypeReference) : unit =
        typeRes <- C.Type.PhysPtr (this.DoType (managedPointerTypeReference.TargetType)) //TODO: Ptr kind

      member this.Visit (marshallingInformation:IMarshallingInformation) : unit = assert false
      
      member this.Visit (constant:IMetadataConstant) : unit = assert false

      member this.Visit (createArray:IMetadataCreateArray) : unit = assert false

      member this.Visit (expression:IMetadataExpression) : unit = assert false

      member this.Visit (namedArgument:IMetadataNamedArgument) : unit = assert false

      member this.Visit (typeOf:IMetadataTypeOf) : unit = assert false

      member this.Visit (methodBody:IMethodBody) : unit = assert false

      member this.Visit (method_:IMethodDefinition) : unit = assert false

      member this.Visit (methodImplementation:IMethodImplementation) : unit = assert false

      member this.Visit (methodReference:IMethodReference) : unit = assert false

      member this.Visit (modifiedTypeReference:IModifiedTypeReference) : unit = 
        modifiedTypeReference.UnmodifiedType.Dispatch(this)
        //TODO: this may loose modifiers that we need

      member this.Visit (module_:IModule) : unit = assert false

      member this.Visit (moduleReference:IModuleReference) : unit = assert false

      member this.Visit (namespaceAliasForType:INamespaceAliasForType) : unit = assert false

      member this.Visit (namespaceTypeDefinition:INamespaceTypeDefinition) : unit =
        this.DoTypeDefinition namespaceTypeDefinition
            
      member this.Visit (namespaceTypeReference:INamespaceTypeReference) : unit =
        this.DoTypeDefinition namespaceTypeReference.ResolvedType

      member this.Visit (nestedAliasForType:INestedAliasForType) : unit = assert false

      member this.Visit (nestedTypeDefinition:INestedTypeDefinition) : unit =
        if not (nestedTypeDefinition.ContainingTypeDefinition.ToString().StartsWith(SystemDiagnosticsContractsCodeContract))
           && (nestedTypeDefinition.ContainingTypeDefinition.ToString()) <> "__Globals__" then
          nestedTypeDefinition.ContainingTypeDefinition.Dispatch(this)
        this.DoTypeDefinition nestedTypeDefinition

      member this.Visit (nestedTypeReference:INestedTypeReference) : unit = assert false

      member this.Visit (nestedUnitNamespace:INestedUnitNamespace) : unit = assert false

      member this.Visit (nestedUnitNamespaceReference:INestedUnitNamespaceReference) : unit = assert false

      member this.Visit (nestedUnitSetNamespace:INestedUnitSetNamespace) : unit = assert false

      member this.Visit (parameterDefinition:IParameterDefinition) : unit = assert false

      member this.Visit (parameterTypeInformation:IParameterTypeInformation) : unit = assert false

      member this.Visit (pointerTypeReference:IPointerTypeReference) : unit =
        let targetType = this.DoType (pointerTypeReference.TargetType)
        let isSpec, targetType' = 
          match pointerTypeReference with
            | :? IPointerType as pt -> 
              VccCompilationHelper.IsSpecPointer(pt),
              if VccCompilationHelper.IsVolatilePointer(pt) && isTypeWhereVolatileMatters targetType 
              then C.Type.Volatile(targetType) else targetType
            | _ -> false, targetType

        typeRes <- C.Type.MkPtr (targetType', isSpec)

      member this.Visit (propertyDefinition:IPropertyDefinition) : unit = assert false

      member this.Visit (resourceReference:IResourceReference) : unit = assert false

      member this.Visit (rootUnitNamespace:IRootUnitNamespace) : unit =
        match rootUnitNamespace with
          | :? UnitNamespace as unitNs ->
            for nsDecl in unitNs.NamespaceDeclarations do
              match nsDecl with
                | :? Microsoft.Research.Vcc.VccRootNamespaceDeclaration as rootNsDecl -> rootNsDecl.ReportDuplicateIncompatibleTypedefs()
                | _ -> ()
          | _ -> ()
        Seq.iter (fun (m : INamespaceMember) -> m.Dispatch(this)) rootUnitNamespace.Members

      member this.Visit (rootUnitNamespaceReference:IRootUnitNamespaceReference) : unit = assert false

      member this.Visit (rootUnitSetNamespace:IRootUnitSetNamespace) : unit = assert false

      member this.Visit (securityAttribute:ISecurityAttribute) : unit = assert false

      member this.Visit (unitSet:IUnitSet) : unit = assert false

      member this.Visit (win32Resource:IWin32Resource) : unit = assert false
    
      member this.Visit (addition:IAddition) : unit =
        if (addition.LeftOperand.Type :? IPointerType) || (addition.RightOperand.Type :? IPointerType) then
          exprRes <- C.Expr.Macro (this.ExprCommon addition, "ptr_addition", 
                                   [this.DoIExpression addition.LeftOperand; this.DoIExpression addition.RightOperand])
        else
          this.DoIBinary ("+", addition, addition.CheckOverflow)

      member this.Visit (addressableExpression:IAddressableExpression) : unit =
        this.DoField addressableExpression addressableExpression.Instance addressableExpression.Definition

      member this.Visit (addressDereference:IAddressDereference) : unit =
        exprRes <- C.Expr.Deref (this.ExprCommon addressDereference, this.DoIExpression (addressDereference.Address))

      member this.Visit (addressOf:IAddressOf) : unit =
        exprRes <- C.Expr.Macro (this.ExprCommon addressOf, "&", [this.DoIExpression (addressOf.Expression)])

      member this.Visit (anonymousMethod:IAnonymousDelegate) : unit = assert false

      member this.Visit (arrayIndexer:IArrayIndexer) : unit = assert false

      member this.Visit (assertStatement:IAssertStatement) : unit =
        let cond = this.DoIExpression (assertStatement.Condition)
        stmtRes <- C.Expr.Assert({ cond.Common with Type = C.Type.Void }, cond, this.GetTriggers assertStatement)

      member this.Visit (assignment:IAssignment) : unit =
        let target = this.DoIExpression (assignment.Target)
        let source = this.DoIExpression (assignment.Source)
        exprRes <- C.Expr.Macro (this.ExprCommon assignment, "=", [target; source])

      member this.Visit (assumeStatement:IAssumeStatement) : unit =
        stmtRes <- C.Expr.MkAssume (this.DoIExpression (assumeStatement.Condition))

      member this.Visit (bitwiseAnd:IBitwiseAnd) : unit =
        this.DoIBinary ("&", bitwiseAnd)

      member this.Visit (bitwiseOr:IBitwiseOr) : unit =
        this.DoIBinary ("|", bitwiseOr)

      member this.Visit (blockExpression:IBlockExpression) : unit =
        let savedLocalVars = localVars
        localVars <- []
        let stmts = [for s in blockExpression.BlockStatement.Statements -> this.DoStatement s]
        let expr = this.DoIExpression blockExpression.Expression
        exprRes <- C.Expr.Block (this.ExprCommon blockExpression, localVars @ stmts @ [expr], None)
        localVars <- savedLocalVars
        
      member this.Visit (block:IBlockStatement) : unit =
        stmtRes <- this.DoBlock(block) 
        
      member this.Visit (breakStatement:IBreakStatement) : unit = 
        stmtRes <- C.Expr.Macro(this.StmtCommon breakStatement, "break", [])

      member this.Visit (boundExpression:IBoundExpression) : unit =
        this.DoField boundExpression boundExpression.Instance boundExpression.Definition 
          
      member this.Visit (castIfPossible:ICastIfPossible) : unit = assert false

      member this.Visit (catchClause:ICatchClause) : unit = assert false

      member this.Visit (checkIfInstance:ICheckIfInstance) : unit = 
        let typeToCheck = this.DoType checkIfInstance.TypeToCheck
        let ec = this.ExprCommon checkIfInstance
        match typeToCheck with
          | C.Ptr(_) -> helper.Warning(ec.Token, 9107, "'\\is' applied to a pointer type; this is probably not what you intended", None) // TODO update to new syntax, \is
          | _ -> ()
        let operand = this.DoIExpression checkIfInstance.Operand
        match operand.Type with 
          | C.Ptr _ 
          | C.Type.ObjectT
          | C.Type.Claim -> ()
          | t -> helper.Error (operand.Token, 9748, "Cannot apply '\\is' to argument of type '" + operand.Type.ToString() + "'")
        // set also the type in ExprCommon so we prevent pruning of the type
        let typeExpr = C.Expr.UserData({C.ExprCommon.Bogus with Type = typeToCheck}, typeToCheck ) 
        exprRes <- C.Expr.Macro(ec, "\\is", [operand; typeExpr ])

      member this.Visit (constant:ICompileTimeConstant) : unit =

        let unfolded = 
          if unfoldingConstant then None
          else
            match constant with
              | :? CompileTimeConstant as cconst -> 
                if cconst :> Expression <> cconst.UnfoldedExpression 
                   && not (cconst.UnfoldedExpression :? CompileTimeConstant) 
                   && (cconst.Value = null || cconst.Value.GetType() <> typeof<string>)
                then
                  unfoldingConstant <- true
                  let res = Some(this.DoExpression(cconst.UnfoldedExpression))
                  unfoldingConstant <- false
                  res
                else None
              | _ -> None

        let cconst = this.DoCompileTimeConstant(constant)

        exprRes <-
          match unfolded with
            | None -> cconst
            | Some uconst -> 
              let uconst' = if uconst.Type <> cconst.Type then C.Expr.Cast({uconst.Common with Type = cconst.Type}, C.CheckedStatus.Unchecked, uconst) else uconst
              if cconst.ExprEquals(uconst') then cconst 
              else C.Macro(cconst.Common, "const", [cconst; uconst'])

      member this.Visit (conversion:IConversion) : unit =
        match conversion with
          | :? Microsoft.Research.Vcc.VccCast.VccCastArrayConversion as arrConv -> 
            let cmn = this.ExprCommon conversion
            exprRes <- C.Expr.Macro({cmn with Type = C.Type.ObjectT}, "_vcc_as_array",
                                   [this.DoIExpression(arrConv.ValueToConvert); this.DoIExpression(arrConv.Size)]) 
          | _ -> 
            exprRes <- C.Expr.Cast (this.ExprCommon conversion, 
                                    checkedStatus conversion.CheckNumericRange, 
                                    this.DoIExpression (conversion.ValueToConvert))

      member this.Visit (conditional:IConditional) : unit =
        exprRes <- C.Expr.Macro (this.ExprCommon conditional, "ite",
                                 [this.DoIExpression conditional.Condition;
                                  this.DoIExpression conditional.ResultIfTrue;
                                  this.DoIExpression conditional.ResultIfFalse])

      member this.Visit (conditionalStatement:IConditionalStatement) : unit =
        stmtRes <- C.Expr.If (this.StmtCommon conditionalStatement,
                              None,
                              this.DoIExpression conditionalStatement.Condition,
                              this.DoStatement conditionalStatement.TrueBranch,
                              this.DoStatement conditionalStatement.FalseBranch)

      member this.Visit (continueStatement:IContinueStatement) : unit = 
        stmtRes <- C.Expr.Macro(this.StmtCommon continueStatement, "continue", [])

      member this.Visit (createArray:ICreateArray) : unit = 
        // this is how we project finite set expressions
        let elems = [ for e in createArray.Initializers -> this.DoIExpression e]
        let ec = {Token = token createArray; Type = C.Type.Math "\\objset"} : C.ExprCommon
        exprRes <- C.Expr.Macro(ec, "set", elems)

      member this.Visit (createDelegateInstance:ICreateDelegateInstance) : unit = assert false

      member this.Visit (createObjectInstance:ICreateObjectInstance) : unit = assert false

      member this.Visit (debuggerBreakStatement:IDebuggerBreakStatement) : unit = assert false

      member this.Visit (defaultValue:IDefaultValue) : unit = assert false

      member this.Visit (division:IDivision) : unit =
        match division with 
          | :? VccDivision as vccDiv -> this.DoIBinary ("/", division, vccDiv.CheckOverflow)
          | _ -> this.DoIBinary ("/", division, true)
      
      member this.Visit (doUntilStatement:IDoUntilStatement) : unit =
        stmtRes <- C.Expr.Macro (this.StmtCommon doUntilStatement,
                                 "doUntil", 
                                 [this.DoLoopContract doUntilStatement;
                                  this.DoStatement doUntilStatement.Body; 
                                  this.DoIExpression doUntilStatement.Condition])

      member this.Visit (emptyStatement:IEmptyStatement) : unit =
        stmtRes <- C.Expr.Skip(this.StmtCommon emptyStatement)

      member this.Visit (equality:IEquality) : unit =
        this.DoIBinary ("==", equality)

      member this.Visit (exclusiveOr:IExclusiveOr) : unit =
        this.DoIBinary ("^", exclusiveOr)

      member this.Visit (expressionStatement:IExpressionStatement) : unit =
        let expr = this.DoIExpression (expressionStatement.Expression)
        let expr =
          match expr with
            | C.Macro (c, "=", args) -> C.Macro ({ c with Type = C.Void }, "=", args) 
            | expr -> expr
        stmtRes <- expr

      member this.Visit (forEachStatement:IForEachStatement) : unit = assert false

      member this.Visit (forStatement:IForStatement) : unit =
        let doStmts l =
          C.Expr.MkBlock [for s in l -> this.DoStatement s]
        let inits = doStmts forStatement.InitStatements // there can be declarations there, so do it first
        stmtRes <- C.Expr.Macro (this.StmtCommon forStatement,
                                 "for", 
                                 [this.DoLoopContract forStatement;
                                  inits;
                                  this.DoIExpression forStatement.Condition;
                                  doStmts forStatement.IncrementStatements;
                                  this.DoStatement forStatement.Body
                                  ])

      member this.Visit (gotoStatement:IGotoStatement) : unit = 
        stmtRes <- C.Goto(this.StmtCommon gotoStatement, { Name = gotoStatement.TargetStatement.Label.Value })

      member this.Visit (gotoSwitchCaseStatement:IGotoSwitchCaseStatement) : unit = assert false

      member this.Visit (getTypeOfTypedReference:IGetTypeOfTypedReference) : unit = assert false

      member this.Visit (getValueOfTypedReference:IGetValueOfTypedReference) : unit = assert false

      member this.Visit (greaterThan:IGreaterThan) : unit =
        this.DoIBinary (">", greaterThan)

      member this.Visit (greaterThanOrEqual:IGreaterThanOrEqual) : unit =
        this.DoIBinary (">=", greaterThanOrEqual)

      member this.Visit (labeledStatement:ILabeledStatement) : unit = 
        let lblStmt = C.Label(this.StmtCommon labeledStatement, { Name = labeledStatement.Label.Value })
        stmtRes <- C.Expr.MkBlock([lblStmt; this.DoStatement(labeledStatement.Statement)])

      member this.Visit (leftShift:ILeftShift) : unit =
        this.DoIBinary ("<<", leftShift)

      member this.Visit (lessThan:ILessThan) : unit =
        this.DoIBinary ("<", lessThan)

      member this.Visit (lessThanOrEqual:ILessThanOrEqual) : unit =
        this.DoIBinary ("<=", lessThanOrEqual)

      member this.Visit (localDeclarationStatement:ILocalDeclarationStatement) : unit =
        let loc = localDeclarationStatement.LocalVariable
        let sc = this.StmtCommon localDeclarationStatement
        let varkind, attrs = 
          match loc with 
            | :? Microsoft.Research.Vcc.VccLocalDefinition as vcLoc -> 
                (if vcLoc.IsSpec then C.VarKind.SpecLocal else C.VarKind.Local),
                convCustomAttributes sc.Token vcLoc.Attributes
            | _ -> C.VarKind.Local, []
        let var = C.Variable.CreateUnique loc.Name.Value (this.DoType (loc.Type)) varkind
        localsMap.Add(loc, var)
        let decl = C.Expr.VarDecl (sc, var, attrs) 
        localVars <- decl :: localVars
        // it seems that if there is an initalizer, it sometimes
        // gets called separatly and the node returned from here is gone.
        // so we return a comment instead of the decl, for if it is lost there is no big deal
        let decl = C.Expr.Comment (sc, "var " + var.ToString())
        let init = localDeclarationStatement.InitialValue
        if init = null then
          stmtRes <- decl
        else
          let assign = C.Expr.Macro (sc, "=", [C.Expr.Ref({ sc with Type = var.Type }, var); 
                                                            this.DoIExpression init])
          let assign = if var.Kind = C.VarKind.SpecLocal then C.Expr.SpecCode(assign) else assign
          stmtRes <- assign

      member this.Visit (lockStatement:ILockStatement) : unit = assert false

      member this.Visit (logicalNot:ILogicalNot) : unit =
        this.DoIUnary ("!", logicalNot, false)

      member this.Visit (makeTypedReference:IMakeTypedReference) : unit = assert false

      member this.Visit (methodCall:IMethodCall) : unit =
        let ec = this.ExprCommon methodCall
        let methodToCall = 
          match methodCall with
            // the two don't agree if there is an elipsis in function prototype (i.e. there are additional parameters)
            | :? VccMethodCall as meth -> meth.ResolvedMethod
            | _ -> methodCall.MethodToCall.ResolvedMethod            
        let methodName = methodToCall.Name.Value
        let containingTypeDefinitionName = TypeHelper.GetTypeName(methodToCall.ContainingTypeDefinition)        

        let bigIntOpMap = Map.ofList [ "op_Equality", ("==", false) ; "op_Inequality", ("!=", false); "op_Addition", ("+", false);
                                       "op_Subtraction", ("-", true); "op_Division", ("/", true); "op_Modulus", ("%", true);
                                       "op_Multiply", ("*", false); "op_LessThan", ("<", false); "op_LessThanOrEqual", ("<=", false);
                                       "op_GreaterThan", (">", false); "op_GreaterThanOrEqual", (">=", false);
                                       "op_UnaryNegation", ("-", false);
                                       "op_LeftShift", ("<<", false); "op_RightShift", (">>", false); "op_BitwiseAnd", ("&", false);
                                       "op_BitwiseOr", ("|", false); "op_BitwiseNot", ("~", false); "op_ExclusiveOr", ("^", false);
                                    ]

        let floatOpMap = Map.ofList [ "op_Equality", ("==", false) ; "op_Inequality", ("!=", false); "op_Addition", ("+", false);
                                      "op_Subtraction", ("-", true); "op_Division", ("/", true); 
                                       "op_Multiply", ("*", false); "op_LessThan", ("<", false); "op_LessThanOrEqual", ("<=", false);
                                       "op_GreaterThan", (">", false); "op_GreaterThanOrEqual", (">=", false);
                                       "op_UnaryNegation", ("-", false);                                       
                                    ]


        this.EnsureMethodIsVisited(methodToCall)

        let (|MapTypeString|_|) = function
          | (s:string) when s.StartsWith(SystemDiagnosticsContractsCodeContractMap) -> Some ()
          | _ -> None

        let (|BigIntOp|_|) = fun s ->
          if Map.containsKey s bigIntOpMap then
            Some ()
          else None

        let (|FloatOp|_|) = fun s ->
          if Map.containsKey s floatOpMap then
            Some ()
          else None

        let (|ObjsetOp|_|) = function
          | "op_Addition"
          | "op_Subtraction"
          | "op_BitwiseAnd"
          | "op_BitwiseOr"
          | "op_ExclusiveOr"
          | "op_LessThan"
          | "op_LessThanOrEqual" -> Some ()
          | _ -> None

        let oopsNumArgs() = oopsLoc methodCall ("unexpected number of arguments for "+ methodName); die ()

        let args() = [for e in methodCall.Arguments -> this.DoIExpression e]

        let trOp opMap methodName = 
          let mcIsChecked = 
            match methodCall with
              | :? Expression as expr -> expr.ContainingBlock.UseCheckedArithmetic
              | _ -> true
          match args() with
            | [e1] when methodName = "op_UnaryNegation" ->
              let op, isChecked = Map.find methodName opMap
              exprRes <- C.Expr.Prim (ec, C.Op(op, checkedStatus (isChecked && mcIsChecked)), [e1])
            | [e1; e2] -> 
              let op, isChecked = Map.find methodName opMap
              exprRes <- C.Expr.Prim (ec, C.Op(op, checkedStatus (isChecked && mcIsChecked)), [e1; e2])
            | _ -> oopsNumArgs()
            
        let trBigIntOp = trOp bigIntOpMap
        let trFloatOp = trOp floatOpMap

        let trSetOp methodName =
          match args() with
           | [e1; e2] ->
             match methodName with
               | "op_LessThanOrEqual" -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_in" methodCall, [], [e1; e2])
               | "op_LessThan"        -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_in0" methodCall, [], [e1; e2])
               | "op_BitwiseAnd"      -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_intersection" methodCall, [], [e1; e2])
               | "op_BitwiseOr"       -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_union" methodCall, [], [e1; e2])
               | "op_ExclusiveOr"     -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_difference" methodCall, [], [e1; e2])
               | "op_Addition"        -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_add_element" methodCall, [], [e1; e2])
               | "op_Subtraction"     -> exprRes <- C.Call(ec, findFunctionOrDie "\\set_remove_element" methodCall, [], [e1; e2])
               | _ -> die()
           | _ -> oopsNumArgs()

        let trTrivialCast() =             
          match args() with
            | [e] -> exprRes <- e
            | _ -> oopsNumArgs()

        let trCast() =             
          match args() with
            | [e] -> exprRes <- C.Expr.Cast(ec, C.CheckedStatus.Checked, e)
            | _ -> oopsNumArgs()

        let (|BigIntTypeName|_|) = function
          | SystemDiagnosticsContractsCodeContractBigInt
          | SystemDiagnosticsContractsCodeContractBigNat -> Some ()
          | _ -> None


        match containingTypeDefinitionName, methodName with
          | SystemDiagnosticsContractsCodeContract, ("Exists" | "ForAll" | "Lambda") ->
            exprRes <- C.Expr.Quant (ec, this.DoQuant (methodCall))
          | SystemDiagnosticsContractsCodeContract, "InLambda" -> exprRes <- C.Expr.Macro (ec, "in_lambda", args())
          | SystemIntPtr, ("op_Implicit" | "op_Explicit") 
          | SystemDiagnosticsContractsCodeContractTypedPtr, ("op_Implicit" | "op_Explicit") -> trTrivialCast()
          | SystemDiagnosticsContractsCodeContractTypedPtr, ("op_Equality" | "op_Inequality") -> trBigIntOp methodName
          | BigIntTypeName, "op_Implicit" -> trTrivialCast()
          | BigIntTypeName, "op_Explicit" -> trCast()
          | BigIntTypeName, BigIntOp -> trBigIntOp methodName
          | (SystemDouble | SystemFloat), FloatOp -> trFloatOp methodName
          | SystemDiagnosticsContractsCodeContractObjset, ObjsetOp -> trSetOp methodName
          | "Microsoft.Research.Vcc.Runtime", "__noop" -> exprRes <- C.Expr.Skip ({ec with Type = C.Type.Void})
          | MapTypeString, "get_Item" ->
            let th = this.DoIExpression methodCall.ThisArgument
            match args() with
              | [x] -> exprRes <- C.Expr.Macro (ec, "map_get", [th; x])
              | _ -> oopsNumArgs()
          | MapTypeString, "set_Item" ->
            let th = this.DoIExpression methodCall.ThisArgument
            match args() with
              | [x; y] -> exprRes <- C.Expr.Macro (ec, "map_set", [th; x; y])
              | _ -> oopsNumArgs()
          | ( SystemDiagnosticsContractsCodeContract | SystemDiagnosticsContractsCodeContractTypedPtr | MapTypeString), _ ->
            oopsLoc methodCall ("unexpected method \'" + containingTypeDefinitionName + "." + methodName + "\'"); die()
          | _, ("_vcc_in_state"|"\\at") ->
            match args() with
              | [e1; e2] -> exprRes <- C.Expr.Old ({ec with Type = e2.Type}, e1, e2)
              | _ -> oopsNumArgs()
          | _, ("_vcc_approves" | "\\approves") ->
            match args() with
              | [e1; e2] -> exprRes <- C.Expr.Macro (ec, "approves", [e1; e2])
              | _ -> oopsNumArgs() 
          | _, ("_vcc_deep_struct_eq" | "_vcc_shallow_struct_eq" | "_vcc_known" | "\\deep_eq" | "\\shallow_eq") ->
            match args() with
              | [e1; e2] as args -> exprRes <- C.Expr.Macro(ec, methodName, args)
              | _ -> oopsNumArgs()
          | _, ("\\size") ->
            match args() with
              | [e1] as args -> exprRes <- C.Expr.Macro(ec, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\argument_tuple" ->
            exprRes <- C.Expr.Macro(ec, "argument_tuple",  args())
          | _, _ when methodName.StartsWith "\\castlike_" ->
            exprRes <- C.Expr.Macro(ec, methodName, args())
          | _, "\\labeled_expression" ->
            match args() with
              | [labName; arg; body] ->
                let rec aux = function
                  | C.Macro (_, "&", [e])
                  | C.Cast (_, _, e) -> aux e
                  | C.Macro (_, "string", [C.UserData (_, (:? string as r))]) -> r
                  | e -> oops ("expecting label name as string, got " + e.ToString()); ""
                exprRes <- C.Expr.Macro(ec, "lbl_" + aux labName, [arg; body])
              | _ -> oopsNumArgs()
          | _, "_vcc_atomic_op" ->
            exprRes <- C.Expr.Macro(ec, "atomic_op",  args())
          | _, "_vcc_atomic_op_result" ->
            exprRes <- C.Expr.Macro(ec, "atomic_op_result", [])
          | _, "\\test_classifier" ->
            match args() with
              | [classif;cond] as args -> exprRes <- C.Expr.Macro ({ ec with Type = cond.Type }, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\downgrade_to" ->
            match args() with
              | [var;expr] as args -> exprRes <- C.Expr.Macro ({ ec with Type = CAST.Type.Void }, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\current_context" ->
            match args() with
              | [] -> exprRes <- C.Expr.Macro ({ ec with Type = CAST.Type.SecLabel None }, methodName, [])
              | _ -> oopsNumArgs()
          | _, "\\label_of" ->
            match args() with
              | [expr] as args -> exprRes <- C.Expr.Macro ({ec with Type = C.Type.SecLabel(Some expr) }, methodName, args)
              | _ -> oopsNumArgs()
          | _, ("\\seclabel_bot"|"\\seclabel_top") ->
            match args() with
              | [] -> exprRes <- C.Expr.Macro ({ec with Type = C.Type.SecLabel(None) }, methodName, [])
              | _ -> oopsNumArgs()
          | _, "\\lblset_leq" ->
            match args() with
              | [l1;l2] as args -> exprRes <- C.Expr.Macro ({ec with Type = C.Type.Bool }, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\new_club" ->
            match args() with
              | [l] as args -> exprRes <- C.Expr.Macro({ec with Type = C.Type.Math "club_t"}, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\add_member" ->
            match args() with
              | [p; c] as args -> exprRes <- C.Expr.Macro({ec with Type = C.Type.Void}, methodName, args)
              | _ -> oopsNumArgs()
          | _, "\\is_member" ->
            match args() with
              | [p; c] as args -> exprRes <- C.Expr.Macro({ec with Type = C.Type.Bool}, methodName, args)
              | _ -> oopsNumArgs()
//          | _, "\\static_cast" ->
//            let tgtType = 
//              match methodToCall with
//                | :? IGenericMethodInstance as gmi -> 
//                  match [ for t in gmi.GenericArguments -> this.DoType t ] with
//                    | [ t0; _ ] -> t0
//                    | _ -> oopsLoc methodToCall "\\static_cast has wrong number of type arguments"; C.Type.Bogus
//                | _ -> oopsLoc methodToCall "\\static_cast must be generic"; C.Type.Bogus
//            match args() with
//              | [o] -> exprRes <- o.WithCommon { o.Common with Type = tgtType }
//              | _ -> oopsNumArgs()
          | _ ->
            let args = args()
            let nonVoidParCount = [for p in methodToCall.Parameters do if p.Type.ResolvedType.TypeCode <> PrimitiveTypeCode.Void then yield p].Length;
            if args.Length <> nonVoidParCount && not methodToCall.AcceptsExtraArguments then
              helper.Error(token methodCall, 9636, 
                           "wrong number of arguments in call to function '" + (methodToCall.Name.ToString()) + "'; was " 
                           + (args.Length.ToString()) + ", should be " + (methodToCall.ParameterCount.ToString()), Some(token methodToCall))
            if methodName = "_vcc_is" then
              match args with
                | [_; C.Expr.Call(_, _, _, [C.Expr.Cast(_,_,e)])] ->
                  match e.Type with
                    | C.Ptr(C.Ptr(_)) -> helper.Warning(e.Common.Token, 9107, "'is' applied to a pointer type; this is probably not what you intended", None) // TODO update to new syntax, \is
                    | _ -> ()
                | _ -> ()
            let mtc, tArgs =
              match methodToCall with
                | :? IGenericMethodInstance as gmi -> gmi.GenericMethod.ResolvedMethod, [ for t in gmi.GenericArguments -> this.DoType t ]
                | _ -> methodToCall, []
            exprRes <- C.Expr.Call (ec, this.LookupMethod mtc, tArgs, args)

      member this.Visit (modulus:IModulus) : unit =
        this.DoIBinary ("%", modulus, false)

      member this.Visit (multiplication:IMultiplication) : unit =
        this.DoIBinary ("*", multiplication, multiplication.CheckOverflow)

      member this.Visit (namedArgument:INamedArgument) : unit = assert false

      member this.Visit (notEquality:INotEquality) : unit =
        this.DoIBinary ("!=", notEquality)        

      member this.Visit (oldValue:IOldValue) : unit =
        let ec = this.ExprCommon oldValue
        let findTypeOrDie name =
          match typeNameMap.TryGetValue(name) with
            | (true, f) -> f
            | _ -> oopsLoc oldValue ("cannot find internal type " + name + ". Forgotten #include <vcc.h>?"); die()
        let ts = findTypeOrDie "\\state"
        let expr = this.DoIExpression oldValue.Expression
        // the type of expr and old(expr) may disagree in CCI, so we fix it up here
        exprRes <- C.Expr.Old ({ec with Type = expr.Type}, C.Expr.Macro ({ec with Type = C.Type.Ref(ts) }, "prestate", []), expr)

      member this.Visit (onesComplement:IOnesComplement) : unit =
        this.DoIUnary ("~", onesComplement, false)

      member this.Visit (outArgument:IOutArgument) : unit = 
        exprRes <- C.Expr.Macro(this.ExprCommon outArgument, "out", [this.DoIExpression outArgument.Expression])

      member this.Visit (pointerCall:IPointerCall) : unit = 
        exprRes <- C.Expr.Macro (this.ExprCommon pointerCall, "fnptr_call", 
                                 this.DoIExpression pointerCall.Pointer :: 
                                   [for e in pointerCall.Arguments -> this.DoIExpression e])

      member this.Visit (refArgument:IRefArgument) : unit = die()

      member this.Visit (resourceUseStatement:IResourceUseStatement) : unit = die()

      member this.Visit (returnValue:IReturnValue) : unit =
        let ec = this.ExprCommon returnValue
        exprRes <- C.Expr.Result ec
        
      member this.Visit (rethrowStatement:IRethrowStatement) : unit = die()

      member this.Visit (returnStatement:IReturnStatement) : unit =
        let expr = returnStatement.Expression
        stmtRes <- C.Return (this.StmtCommon returnStatement, if expr = null then None else Some (this.DoIExpression expr))

      member this.Visit (rightShift:IRightShift) : unit =
        this.DoIBinary (">>", rightShift)

      member this.Visit (runtimeArgumentHandleExpression:IRuntimeArgumentHandleExpression) : unit = die()

      member this.Visit (sizeOf:ISizeOf) : unit =
       match sizeOf.TypeToSize.ResolvedType with
         | :? IGenericMethodParameter as tVar ->
          let ec = this.ExprCommon sizeOf
          exprRes <- C.Expr.SizeOf(ec, C.Type.TypeVar({ Name = tVar.Name.Value }))
         | _ ->  exprRes <- C.Expr.IntLiteral (this.ExprCommon sizeOf, 
                                               new bigint(int64 (TypeHelper.SizeOfType (sizeOf.TypeToSize.ResolvedType))))

      member this.Visit (specStmt:IVccSpecStatement) : unit =
        let stmt = this.DoStatement specStmt.WrappedStatement
        stmtRes <- C.Expr.SpecCode(stmt)

      member this.Visit (unwrappingStmt:IVccUnwrappingStatement) : unit =
        let cmn = this.StmtCommon unwrappingStmt
        let exprs = unwrappingStmt.Objects |> Seq.map this.DoIExpression |> Seq.toList
        let body = this.DoStatement(unwrappingStmt.Body)
        stmtRes <- C.Expr.Macro (cmn, "unwrapping", body :: exprs)

      member this.Visit (atomicStmt : IVccAtomicStatement) : unit =
        let args = [ for arg in atomicStmt.Objects -> this.DoIExpression arg ]
        let body = this.DoStatement atomicStmt.Body
        let args = 
          if atomicStmt.IsGhostAtomic then 
            C.Expr.Macro ({ C.bogusEC with Type =  C.Type.ObjectT }, "ghost_atomic", []) :: args
          else args
        stmtRes <- C.Expr.Atomic (this.StmtCommon atomicStmt, args, body)

      member this.Visit (stackArrayCreate:IStackArrayCreate) : unit = 
        match stackArrayCreate with
        | :? CreateStackArray as createStackArray -> 
          let numberOfElements = this.DoIExpression(createStackArray.Size.ProjectAsIExpression())
          let elementType = this.DoType(createStackArray.ElementType.ResolvedType)
          let isSpec = 
            match createStackArray with 
              | :? VccCreateStackArray as vccCreateStackArray -> if vccCreateStackArray.IsSpec then cTrue else cFalse
              | _ -> cFalse
          exprRes <- C.Macro({numberOfElements.Common with Type = C.PhysPtr elementType}, "stack_allocate_array", [numberOfElements; isSpec]) 
        | _ -> assert false

      member this.Visit (subtraction:ISubtraction) : unit =
        this.DoIBinary ("-", subtraction, subtraction.CheckOverflow)

      member this.Visit (switchCase:ISwitchCase) : unit = assert false // never encountered during traversal

      member this.Visit (switchStatement:IVccMatchStatement) : unit = 
        let doCase (sc : IVccMatchCase) =
          C.Expr.Macro({ C.voidBogusEC () with Token = token sc }, "case", [this.DoStatement sc.Body])
        let condExprStmt = this.DoIExpression switchStatement.Expression
        let cases = [for sc in switchStatement.Cases -> doCase sc]
        stmtRes <- C.Expr.Macro(this.StmtCommon switchStatement, "match", condExprStmt :: cases)

      member this.Visit (switchStatement:ISwitchStatement) : unit = 
        let doCase (sc : ISwitchCase) =
          let (caseLabel,castExprStmt) =
            if sc.Expression = CodeDummy.Constant then ("default", [])
            else ("case", [this.DoIExpression sc.Expression])
          let body = castExprStmt @ [ for stmt in sc.Body -> this.DoStatement stmt]       
          C.Expr.Macro({ C.voidBogusEC () with Token = token sc }, caseLabel, body)
        let condExprStmt = this.DoIExpression switchStatement.Expression
        let cases = [for sc in switchStatement.Cases -> doCase sc]
        stmtRes <- C.Expr.Macro(this.StmtCommon switchStatement, "switch", condExprStmt :: cases)

      member this.Visit (targetExpression:ITargetExpression) : unit =
        this.DoField targetExpression targetExpression.Instance targetExpression.Definition

      member this.Visit (thisReference:IThisReference) : unit =
        exprRes <- C.Expr.This (this.ExprCommon thisReference)

      member this.Visit (throwStatement:IThrowStatement) : unit = assert false

      member this.Visit (tryCatchFilterFinallyStatement:ITryCatchFinallyStatement) : unit = assert false

      member this.Visit (tokenOf:ITokenOf) : unit = assert false

      member this.Visit (typeOf:ITypeOf) : unit = assert false

      member this.Visit (unaryNegation:IUnaryNegation) : unit =
        this.DoIUnary ("-", unaryNegation, unaryNegation.CheckOverflow)

      member this.Visit (unaryPlus:IUnaryPlus) : unit =
        this.DoIUnary ("+", unaryPlus, false)

      member this.Visit (vectorLength:IVectorLength) : unit = assert false

      member this.Visit (whileDoStatement:IWhileDoStatement) : unit =
        let cond = this.DoIExpression (whileDoStatement.Condition)
        let body = this.DoStatement (whileDoStatement.Body)
        let cmn = this.StmtCommon whileDoStatement

        match cond with
          | C.Call (_, { Name = "_vcc_atomic" }, _, args) ->
            stmtRes <- C.Expr.Atomic (cmn, args, body)
          | C.Call (_, { Name = "_vcc_expose" }, _, [arg]) ->
            let wrap = findFunctionOrDie "_vcc_wrap" whileDoStatement
            let unwrap = findFunctionOrDie "_vcc_unwrap" whileDoStatement
            stmtRes <- C.Expr.Block(cmn, [ C.Expr.Call((stmtToken "unwrap(@@)" arg), unwrap, [], [arg]);  body; C.Expr.Call((stmtToken "wrap(@@)" arg), wrap, [], [arg]) ], None )
          | _ ->
            let contract = this.DoLoopContract whileDoStatement
            stmtRes <- C.Expr.Macro (cmn, "while", [contract; cond; body])

      member this.Visit (yieldBreakStatement:IYieldBreakStatement) : unit = assert false

      member this.Visit (yieldReturnStatement:IYieldReturnStatement) : unit = assert false       

      member this.Visit (dupValue:IDupValue) : unit = assert false

      member this.Visit (popValue:IPopValue) : unit = assert false

      member this.Visit (pushStmt:IPushStatement) : unit = assert false
