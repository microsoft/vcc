//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open Microsoft.FSharp.Math
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.TranslatorUtils
  open Microsoft.Research.Vcc.Util
  open System
  
  module C = Microsoft.Research.Vcc.CAST
  module B = Microsoft.Research.Vcc.BoogieAST
  module IF = Microsoft.Research.Vcc.InformationFlow
  
  type MyFunc<'a> = delegate of unit -> 'a

  module Translator =
    type ClaimContext =
      {
        mutable ClaimChecks : list<B.Stmt>;
        mutable ClaimInits : list<B.Stmt>;
      }
      
    let globalHasIF = ref false

    type Env =
      {
        OldState : B.Expr
        WritesState : B.Expr
        Writes : list<C.Expr>
        WritesTime : B.Expr
        AtomicObjects : list<B.Expr>
        AtomicReads : list<B.Expr>
        ClaimContext : option<ClaimContext>
        InverseTranslation : Dict<B.Expr, list<C.Expr>>

        hasIF : bool
        IFPCNum : ref<int>
        IFBlockNum : ref<int>
        IFContexts : list<list<C.LabelId>*string>
        IFGrpID : ref<bigint>
      }

    let nestingExtents = false
    
    let initialEnv = { OldState = bOld bState
                       Writes = []
                       AtomicObjects = []
                       AtomicReads = []
                       WritesState = bOld bState
                       WritesTime = er "$bogus"
                       ClaimContext = None
                       InverseTranslation = null

                       hasIF = false
                       IFPCNum = ref 0
                       IFBlockNum = ref 0
                       IFContexts = []
                       IFGrpID = ref (bigint.Zero)
                     }
    
    let fieldName (f:C.Field) = f.Parent.Name + "." + f.Name

    let genPureFunctionDef (f:C.Function) = 
      f.IsPure && f.RetType <> C.Void && not (f.Name.Contains("#block#"))

    let currentPC (env:Env) =
      match env.IFContexts with
        | [] -> die()
        | (_,pc) :: _ -> pc

    let parentPC (env:Env) =
      match env.IFContexts with
        | []
        | [_] -> die()
        | _::(_,pc)::_ -> pc

    let getLocalLabels (expr:C.Expr) =
      let labels = ref []
      let rec visitor self = function
        | C.Expr.Label(_,lbl) -> labels := lbl::!labels; false
        | C.Expr.If _
        | C.Expr.Loop _ -> false
        | _ -> true
      expr.SelfVisit(visitor)
      !labels

    let newIFContext (env:Env) expr =
      let jmpContext =
        match expr with
          | C.Expr.If(_,_,_,t,e) -> getLocalLabels t @ getLocalLabels e
          | C.Expr.Loop(_,_,_,_,e) -> getLocalLabels e
          | _ -> die()
      let newPCNum = incr env.IFPCNum; !(env.IFPCNum)
      let newPC = "FlowData#PC#"+(newPCNum.ToString())
      {env with IFContexts = (jmpContext,newPC)::env.IFContexts}

    let freshGrpID (env:Env) = env.IFGrpID := (!env.IFGrpID) + bigint.One; !env.IFGrpID

    let rec noUnions = function
      | C.Type.Ref td ->
        match td.Kind with           
          | C.TypeKind.Struct -> 
            // empty field list denote a forward declaration, in which case we do not know
            td.Fields <> [] && List.forall (fun (f:C.Field) -> noUnions f.Type) td.Fields
          | C.TypeKind.Union -> false
          | _ -> true
      | C.Array (t, _) -> noUnions t
      | _ -> true
    
    let mutable stateId = 0
    let saveState pref =      
      let oldState = pref + "State#" + stateId.ToString()
      stateId <- stateId + 1
      ([B.Stmt.VarDecl ((oldState, tpState), None);
        B.Stmt.Assign (er oldState, bState)], er oldState)

    let translate functionToVerify (helper:Helper.Env) (getPrelude:MyFunc<Microsoft.Boogie.Program>) decls =
      let ctx = TranslationState(helper)
      let helper = ctx.Helper
      let bv = BvTranslator(ctx)
      let preludeBodies = lazy (ToBoogieAST.getFunctionExpansions (getPrelude.Invoke()))
      
      let toTypeId = ctx.ToTypeId
      let castFromInt = ctx.CastFromInt
      let castToInt = ctx.CastToInt
      let trType = ctx.TrType
      let weight = ctx.Weight
      
      let captureStateAttrs suff (tok:Token) =
        if helper.Options.PrintCEVModel && suff <> "<skip>" then             
          let suff = if suff = "" then "" else " : " + suff
          [B.StringAttr ("captureState", String.Format ("{0}({1},{2}){3}", tok.Filename, tok.Line, tok.Column, suff))]
        else []

      let assumeSyncCS suff (env:Env) tok =
        let name = ctx.GetTokenConst tok
        let pred =
          match env.AtomicObjects with
            | [] -> "$full_stop_ext"
            | _ -> "$good_state_ext"
        let attrs = captureStateAttrs suff tok
        B.Stmt.Assume (attrs, bCall pred [er name; bState])

      let assumeSync = assumeSyncCS "<skip>"

      let captureState suff tok =
        B.Stmt.Assume (captureStateAttrs suff tok, bTrue)

      let rec addType t e =
        match t with
          | C.PtrSoP (C.Type.Ref td, gh) when td.IsGroup -> 
            let p = addType (C.Type.MkPtr (C.Type.Ref td.Parent.Value, gh)) e
            let f = td.Parent.Value.Fields |> List.find (fun f -> f.Type = C.Type.Ref td)
            bCall "$dot" [p; er (fieldName f)]
          | C.Type.SpecPtr t -> bCall "$spec_ptr_cast" [e; toTypeId t]
          | C.Type.PhysPtr t -> bCall "$phys_ptr_cast" [e; toTypeId t]
          | _ -> e
     
      let intToTyped t fetch =
        match t with
          | C.Type.MathInteger C.MathIntKind.Unsigned
          | C.Type.Integer _ ->
            bCall "$unchecked" [toTypeId t; fetch]
          | C.Ptr t -> addType t (castFromInt (trType t) fetch)
          | C.Bool ->
            bNeq fetch (bInt 0)
          | t ->
            castFromInt (trType t) fetch
         
      let typedEq tp e1 e2 =
        match tp with
          | C.Type.Ref td when td.IsRecord ->
            bCall ("REQ#" + td.Name) [e1; e2]
          | C.Type.Ref td when td.IsDataType ->
            bCall ("DEQ#" + td.Name) [e1; e2]
          | C.Type.Map _ ->
            bCall ("$eq." + (ctx.TypeIdToName (toTypeId tp))) [e1; e2]
          | _ ->
            bEq e1 e2
       
      let defaultValueOf = function
        | C.Ptr _ as t -> addType t (er "$null")
        | C.Type.Claim
        | C.Type.MathInteger _
        | C.Type.Integer _ -> bInt 0
        | C.Type.ObjectT _ -> er "$null"
        | C.Type.Ref({Kind = C.TypeKind.Record} as td) -> er ("RZ#" + td.Name)
        | C.Type.Ref(td) when td.IsDataType ->
          er ("DZ#" + td.Name)
        | C.Type.Ref({Name = n; Kind = C.TypeKind.MathType}) -> 
          match n with 
            | "\\objset" -> bCall "$set_empty" []
            | "\\state" -> er "$state_zero"
            | _ -> er "$struct_zero"
        | C.Type.Bool -> bFalse
        | C.Type.Map _ as t -> er ("$zero." + ctx.TypeIdToName(toTypeId t))
        | t -> helper.Panic ("don't know default value for type " + t.ToString())
      
      let mapEqAxioms t =
        let t1, t2 =
          match t with
            | C.Type.Map (t1, t2) -> t1, t2            
            | _ -> die()
        let bt1 = trType t1
        let bt2 = trType t2
        let mapName = ctx.TypeIdToName (toTypeId t)
        let mt = B.Type.Ref mapName      
      
        let tp = B.Type.Ref mapName
        let mapTypeName = (mapName.Replace ("$#", "")).Replace ("$", "")
        let mapType = B.Type.Ref (mapName)
        let sel = "$select." + mapName
        let selMP = bCall sel [er "M"; er "p"]
        let stor  = "$store." + mapName
        let zero = "$zero." + mapName
        let eq = "$eq." + mapName
        let v = er "v"
        let inRange =
          let rangeAxiom rangeFn args = [B.Decl.Axiom (B.Expr.Forall (Token.NoToken, ["M", tp; "p", bt1], [], weight "select-map-eq", bCall rangeFn args))]
          match t2 with
            | C.Type.MathInteger C.MathIntKind.Unsigned  
            | C.Type.Integer _ -> rangeAxiom "$in_range_t" [toTypeId t2; selMP]
            | C.Type.Claim
            | C.Type.SpecPtr _ -> rangeAxiom "$in_range_spec_ptr" [selMP]
            | C.Type.PhysPtr _ -> rangeAxiom "$in_range_phys_ptr" [selMP]
            | _ -> []
        let unchk t e =
          match t with
            | C.Type.MathInteger C.MathIntKind.Unsigned
            | C.Type.Integer _ ->
              bCall "$unchecked" [toTypeId t; e]
            | C.Ptr _ -> addType t e
            | _ -> e
        let v = unchk t2 v
        let tpEq t p q = typedEq t (unchk t p) (unchk t q)
        let argRange = 
          match t1 with
            | C.Type.MathInteger C.MathIntKind.Unsigned 
            | _ -> bTrue
        
        let selStorPQ =
          bEq (bCall sel [bCall stor [er "M"; er "q"; er "v"]; er "p"])
              (B.Expr.Ite (tpEq t1 (er "p") (er "q"), v, selMP))
        let selZero =
          let zeroVal = defaultValueOf t2
          bEq (bCall sel [er zero; er "p"]) zeroVal
        let eqM1M2 = bCall eq [er "M1"; er "M2"]
        let unchkp = unchk t1 (er "p")
        let eqM1M2Ax1 = bImpl (B.Expr.Forall(Token.NoToken, ["p", bt1], [], weight "select-map-eq", 
                                             bImpl argRange (tpEq t2 (bCall sel [er "M1"; unchkp]) (bCall sel [er "M2"; unchkp]))))
                             eqM1M2
        let eqM1M2Ax2 = bImpl eqM1M2 (bEq (er "M1") (er "M2"))
        
        let mpv = ["M", tp; "p", bt1; "v", bt2]
        let m1m2 = ["M1", tp; "M2", tp]
        [B.Decl.TypeDef mapName;
         B.Decl.Function (bt2, [], sel, ["M", tp; "p", bt1], None);
         B.Decl.Function (tp, [], stor, mpv, None);
         B.Decl.Function (B.Type.Bool, [], eq, m1m2, None);
         B.Decl.Const({Unique = false; Name = "MT#" + sel; Type = tpCtype});
         B.Decl.Axiom(bEq (er ("MT#" + sel)) (toTypeId t));
         B.Decl.Const({Unique = false; Name = zero; Type = mapType});
         B.Decl.Axiom (B.Expr.Forall (Token.NoToken, mpv, [], weight "select-map-eq", bTrue));
         B.Decl.Axiom (B.Expr.Forall (Token.NoToken, mpv @ ["q", bt1], [], weight "select-map-neq", selStorPQ));
         B.Decl.Axiom (B.Expr.Forall (Token.NoToken, m1m2, [[eqM1M2]], weight "select-map-eq", eqM1M2Ax1));
         B.Decl.Axiom (B.Expr.Forall (Token.NoToken, m1m2, [[eqM1M2]], weight "select-map-eq", eqM1M2Ax2));
         B.Decl.Axiom (bEq (castFromInt mt (bInt 0)) (er zero));
         B.Decl.Axiom (B.Expr.Forall (Token.NoToken, ["p", bt1], [], weight "select-map-eq", selZero));
        ] @ inRange
      
      let recTypeName (td:C.TypeDecl) = "RT#" + td.Name
      let dataTypeName (td:C.TypeDecl) = "DT#" + td.Name

      let recType = function
        | C.Ptr (C.Type.Ref td) // we get this for nested records
        | C.Type.Ref td when td.IsRecord -> td
        | t -> helper.Panic ("record type expected, got " + t.ToString())

      let dtType = function
        | C.Type.Ref td when td.IsDataType -> td
        | t -> helper.Panic ("data type expected, got " + t.ToString())

      let trRecordFetch3 (td:C.TypeDecl) (r:B.Expr) (f:C.Field) =
        match r with
          | B.FunctionCall (n, args) when n.StartsWith "RC#" ->
            try
              List.nth args (List.findIndex (fun x -> x = f) td.Fields)
            with e ->
              helper.Panic ("cannot find field " + f.Name + " in " + td.Name)
          | _ ->
            bCall ("RF#" + fieldName f) [r]

      let trRecordUpdate3 (td:C.TypeDecl) (r:B.Expr) (f:C.Field) (v:B.Expr) =
        let args = td.Fields |> List.map (fun g -> if g = f then v else trRecordFetch3 td r g)
        bCall ("RC#" + td.Name) args
      
      let tryDecomposeDot = function
        | B.Expr.FunctionCall ("$dot", [p; f]) -> Some [p; f]
        | _ -> None

      let decomposeDot e = 
        match tryDecomposeDot e with
          | Some r -> r
          | None -> [bCall "$prim_emb" [e]; bCall "$field" [e]]

      let typedRead s p t =
        let decomp p = List.rev (decomposeDot p)
        match t with
          | C.SpecPtr t ->
            bCall "$rd_spec_ptr" (s :: decomp p @ [toTypeId t])
          | C.PhysPtr t ->
            bCall "$rd_phys_ptr" (s :: decomp p @ [toTypeId t])
          | _ ->
            castFromInt (trType t) (bCall "$rd_inv" (s :: decomp p))

      let varRef v = er (ctx.VarName v)

      let trVar (v:C.Variable) : B.Var =
        (ctx.VarName v, trType (v.Type))

      let typeVarName (tv : C.TypeVariable) = "^^TV#" + tv.Name
      let typeVarRef (tv : C.TypeVariable) = er (typeVarName tv)
      let trTypeVar (tv : C.TypeVariable) : B.Var = (typeVarName tv, trType C.Type.TypeIdT)
                  
      
      let trInRange t e =
        match t with
          | C.Type.MathInteger C.MathIntKind.Unsigned -> bCall "$in_range_nat" [e]
          | C.Type.Integer k -> bCall ("$in_range_" + C.Type.IntSuffix k) [e]
          | C.Type.PhysPtr t 
          | C.Type.SpecPtr t -> bTrue // bCall "$is_spac_ptr" [varRef v; toTypeId t]
          | _ -> bTrue
        
      let trWhereVar (v:C.Variable) =
        let v' = trVar v
        let wh = trInRange v.Type (varRef v)
        if wh = bTrue then (v', None)
        else (v', Some wh)
    
      let ptrType (expr:C.Expr) =
        match expr.Type with
          | C.Ptr C.Void -> failwith ("void* not supported " + expr.ToString())
          | C.Ptr t -> toTypeId t
          | _ -> failwith ("pointer type expected " + expr.ToString())        
      
      let convertArgs (fn:C.Function) args =
        let rec loop = function
          | ((f: C.Variable) :: ff, a :: aa) ->
            a :: loop (ff, aa)
          | ([], a) -> a // varargs functions
          | _ -> helper.Die()
        loop (fn.InParameters, args)

      let stripFreeFromEnsures = function
        | C.Macro(_, "_vcc_assume", [e]) -> e
        | e -> e

      let stripFreeFromRequires = function
        | C.Macro(_, "_vcc_assume", [e]) -> e
        | e -> e

      let isSetEmpty = function
        | C.Macro (_, "_vcc_set_empty", []) -> true
        | _ -> false
        
      let warnForIneffectiveOld token expr =
        if not (bContains "$s" expr) then
          helper.Warning (token, 9106, "'\\old', '\\at', or '\\when_claimed' in '" + token.Value + "' has no effect")

      let claimStateId = ref 0

      let abstractSizeUndef = bInt 0 
      let abstractSize t expr =
        match t with
          | C.MathInteger _ 
          | C.Type.Integer _ ->
            bCall "$abs" [expr]
          | C.Type.Ref td when td.IsDataType ->
            bCall ("DSZ#" + td.Name) [expr]
          | C.Type.Ref td when td.IsRecord ->
            bCall ("RSZ#" + td.Name) [expr]
          | _ -> 
            abstractSizeUndef

      let mkIdx ptr idx getTypeWhichIsIgnoredForVcc3 =
        bCall "$idx" [ptr; idx]

      let rec trExpr (env:Env) expr =
        let self = trExpr env
        let selfs = List.map self
        let isFloatingPoint = function | C.Type.Primitive _ -> true | _ -> false
        try
          let res =
            match expr with
              | C.Expr.Skip _ -> die()
              | C.Expr.Cast ({ Type = C.Type.Integer k }, _, e') ->
                match e'.Type with
                  | C.Type.Bool ->
                    bCall "$bool_to_int" [self e']
                  | C.Type.Integer _
                  | C.Type.MathInteger _ -> self e'
                  | C.Type.ObjectT
                  | C.Ptr _ -> // TODO insert checks for casts here
                    bCall ("$ptr_to_" + C.Type.IntSuffix k) [self e']
                  | _ -> die()
              | C.Expr.Cast ({ Type = C.Type.Bool }, _, e') ->
                match e'.Type with
                  | C.Type.Integer _ ->
                    match e' with
                      | C.IntLiteral (_, ZeroBigInt) -> bFalse
                      | C.IntLiteral (_, OneBigInt) -> bTrue
                      | _ -> bCall "$int_to_bool" [self e']
                  | C.ObjectT
                  | C.Ptr _ ->
                    bCall "$ptr_neq" [self e'; er "$null"]
                  | C.Type.MathInteger _ ->
                    bCall "$int_to_bool" [self e']
                  | C.Type.SecLabel _ ->
                    self e'
                  | _ -> die()
              | C.Cast ({ Type = C.Type.MathInteger _}, _, e') when e'.Type._IsPtr -> bCall "$addr" [self e']
              | C.Expr.Cast (_, _, e') when expr.Type._IsPtr && e'.Type._IsPtr ->
                match expr.Type with
                  | C.SpecPtr _ -> bCall "$spec_ptr_cast" [self e'; ptrType expr]
                  | C.PhysPtr _ -> bCall "$phys_ptr_cast" [self e'; ptrType expr]
                  | _ -> die()
              | C.Expr.Cast ({ Type = C.Type.ObjectT }, _, C.Expr.IntLiteral(_, z)) when z = bigint.Zero -> er "$null"
              | C.Expr.Cast ({ Type = C.Type.MathInteger _}, _, e') -> self e'
              | C.Expr.Pure (_, e') -> self e'
              | C.Expr.Macro (c1, name, [C.Expr.Prim (c2, C.Op(_, C.Unchecked), _) as inner]) 
                  when name.StartsWith "unchecked" && c1.Type = c2.Type -> trExpr env inner
              | C.Expr.Prim (c, C.Op(opName, _), args) when isFloatingPoint c.Type ->
                let suffix = match c.Type with | C.Type.Primitive k -> C.Type.PrimSuffix k | _ -> die()
                let opName' = if args.Length = 1 then "u" + opName else opName
                let funcNameTbl = Map.ofList [ "+", "$add"; "-", "$sub"; "*", "$mul"; "/", "$div"; "u-", "$neg";
                                             "<", "$lt"; "<=", "$leq"; ">", "$gt"; ">=", "$geq" ]
                match funcNameTbl.TryFind opName' with
                  | Some(fName) -> bCall (fName + "_" + suffix)(selfs args)
                  | None -> 
                    helper.Error(expr.Token, 9701, "Operator '" + opName + "' not supported for floating point values")
                    bTrue
              | C.Expr.Prim (c, C.Op(opName, ch), args) ->
                let args = selfs args
                let targs = toTypeId c.Type :: args
                match opName with
                  | "&" -> bCall "$_and" targs
                  | "|" -> bCall "$_or" targs
                  | ">>" -> bCall "$_shr" args
                  | "<<" -> bCall "$_shl" targs
                  | "~" -> bCall "$_not" targs
                  | "^" -> bCall "$_xor" targs 
                  | "*" when ch <> C.Unchecked -> bCall "$op_mul" args
                  | _ -> 
                    if ch = C.Unchecked then
                      match opName with
                        | "+" -> bCall "$unchk_add" targs
                        | "-" -> bCall "$unchk_sub" targs
                        | "*" -> bCall "$unchk_mul" targs
                        | "/" -> bCall "$unchk_div" targs
                        | "%" -> bCall "$unchk_mod" targs
                        | _ -> B.Expr.Primitive (opName, args)
                    else if helper.Options.OpsAsFunctions then
                      match opName with
                        | "+" -> bCall "$op_add" targs
                        | "-" -> bCall "$op_sub" targs
                        // * is always translated like this
                        | "/" -> bCall "$op_div" targs
                        | "<" -> bCall "$op_lt" targs
                        | "<=" -> bCall "$op_le" targs
                        | ">" -> bCall "$op_gt" targs
                        | ">=" -> bCall "$op_ge" targs
                        | _ -> B.Expr.Primitive (opName, args)
                    else B.Expr.Primitive (opName, args)
              | C.Expr.Ref (_, v) -> 
                addType v.Type (varRef v)
              | C.Expr.IntLiteral (_, v) ->
                B.Expr.IntLiteral v
              | C.Expr.BoolLiteral (_, v) ->
                B.Expr.BoolLiteral v
              | C.Macro(ec, n, args) -> trMacro env ec n args    
              | C.Expr.Dot (c, o, f) ->
                if f.Parent.Kind = C.Record then
                  helper.Oops (c.Token, "record dot found " + expr.ToString())
                bCall "$dot" [self o; er (fieldName f)]
              | C.Expr.Index (_, arr, idx) ->
                mkIdx (self arr) (self idx) (fun () -> ptrType arr)
              | C.Expr.Deref (_, p) -> typedRead bState (self p) expr.Type
              | C.Expr.Call (_, fn, targs, args) ->
                if fn.IsDatatypeOption then
                  bCall ("DF#" + fn.Name) (selfs args)
                else
                  let args = List.map ctx.ToTypeIdArraysAsPtrs targs @ convertArgs fn (selfs args)
                  let args =
                    if fn.IsStateless then args
                    else bState :: args
                  addType fn.RetType (bCall ("F#" + fn.Name) args)
              // TODO this is wrong for loop invariants and stuff (but the legacy vcc doesn't handle that correctly as well)
              | C.Expr.Old (ec, C.Macro (_, "_vcc_when_claimed", []), e) ->
                warnForIneffectiveOld ec.Token (self e)
                bSubst [("$s", er "$when_claimed_state")] (self e)
              | C.Expr.Old (ec, state, e) ->
                let be = self e
                warnForIneffectiveOld ec.Token be
                match state with 
                  | C.Macro (_, "prestate", []) -> bSubst [("$s", env.OldState)] be
                  | _ -> 
                    let state = state |> self |> bSubst [("$s", er "$$s")]
                    bSubst [("$s", state)] be
              | C.Expr.Result c ->
                addType c.Type (er "$result")
              | C.Expr.Quant (c, q) ->
                for v in q.Variables do
                  ctx.QuantVarTokens.[v] <- c.Token
                let invMapping = gdict()
                let body = trExpr { env with InverseTranslation = invMapping } q.Body
                let body =
                  match q.Condition, q.Kind with
                    | Some e, C.Forall -> bImpl (self e) body
                    | Some e, C.Exists -> bAnd (self e) body
                    | _, C.Lambda -> die()
                    | None, _ -> body                
                let supportedTypeForQuantification (v : C.Variable) =
                  match v.Type with
                    | C.Type.Ref({Kind = C.TypeKind.Struct|C.TypeKind.Union})
                    | C.Array _ ->
                      helper.Error(c.Token, 9696, "Cannot quantify over type '" + v.Type.ToString() + "' (bound variable is '" + v.Name + "').")
                      false
                    | _ -> true
                let vars = q.Variables |> List.filter supportedTypeForQuantification |> List.map trVar 
                if body = bTrue then
                  bTrue
                else
                  let (body, triggers) = TriggerInference(helper, preludeBodies, c.Token, invMapping, vars).Run (body, List.map selfs q.Triggers)
                  let weight n = if System.String.IsNullOrEmpty(q.Weight) then weight n else weight q.Weight
                  match q.Kind with
                    | C.Forall -> B.Forall (c.Token, vars, triggers, weight "user-forall", body)
                    | C.Exists -> B.Exists (c.Token, vars, triggers, weight "user-exists", body)
                    | C.Lambda -> die()
            
              | C.Expr.SizeOf(_, C.Type.TypeVar(tv)) ->bCall "$sizeof" [typeVarRef tv]
              | C.Expr.SizeOf(_, t) -> bInt t.SizeOf
              | C.Expr.This _ -> er "$_this"
              | _ ->         
                helper.Oops (expr.Token, "unhandled expr " + expr.ToString())
                er "$bogus"

          if env.InverseTranslation <> null then
            let cur = lookupWithDefault env.InverseTranslation [] res
            env.InverseTranslation.[res] <- expr :: cur
          res
        with 
          | Failure _ -> 
            helper.Error(expr.Token, 9600, "OOPS for expression " + expr.ToString())
            reraise()

      and trMacro env (ec : C.ExprCommon) n args = 
        let self = trExpr env
        let selfs = List.map self
        let trInvLabel = ctx.TrInvLabel
        match n, args with
          | "writes_check", [a] -> writesCheck env ec.Token false a
          | "prim_writes_check", [a] -> writesCheck env ec.Token true a
          | ("in_range_phys_ptr"|"in_range_spec_ptr") as in_range, [p] ->
            bCall ("$" + in_range) [self p]
          | "in_int_range", [a] ->
            trInRange a.Type (self a)
          | in_range, args when in_range.StartsWith ("in_range") -> bCall ("$" + in_range) (selfs args)
          | ("unchecked_sbits"|"unchecked_ubits"), args ->
            bCall ("$" + n) (selfs args)
          | "_vcc_typed2", [_; a] when a.Type.IsFunctionPtr ->
            bCall "$valid_fnptr" [self a]
          | unchecked, args when unchecked.StartsWith ("unchecked_") -> bCall "$unchecked" (er ("^^" + unchecked.Substring (unchecked.IndexOf '_' + 1)) :: selfs args)
          | ("map_get"|"map_get_trig"), [a; b] ->
            match a.Type with
              | C.Type.Map (f, t) ->
                let fn = "$select." + (trType a.Type).ToString()
                let select = bCall fn [self a; self b]
                if n = "map_get" then addType t select else select
              | _ -> die()          
          | "map_zero", _ -> er ("$zero." + ctx.TypeIdToName(toTypeId ec.Type))
          | "map_updated", [a; b; c] ->
            match a.Type with
              | C.Type.Map (f, t) ->
                let fn = "$store." + (trType a.Type).ToString()
                bCall fn [self a; (self b); (self c)]
              | _ -> die()
          | "field", [C.Expr.UserData (_, ( :? C.Field as f))] ->
            er (fieldName f)
          | "owns_field", [e] ->
            bCall "$f_owns" [toTypeId e.Type.Deref]

          | "_vcc_rec_eq", [r1; r2] ->
            bCall ("REQ#" + (recType r1.Type).Name) [self r1; self r2]

          | "_vcc_simple_emb", [C.Dot (_, p, _)] ->
            self p
             
          | "rec_zero", [] -> 
            er ("RZ#" + (recType ec.Type).Name)
          
          | "rec_fetch", [r; C.UserData(_, (:? C.Field as f))] ->
            trRecordFetch3 (recType r.Type) (self r) f
            
          | "rec_update", [r; C.UserData(_, ( :? C.Field as f) ); v] ->
            trRecordUpdate3 (recType r.Type) (self r) f (self v)
          
          | "rec_update_bv", [r; C.UserData(_, (:? C.Field as f)); bvSize; bvStart; bvEnd; v] ->
            bCall "$rec_update_bv" [self r; er (fieldName f); self bvSize; self bvStart; self bvEnd; trForWrite env f.Type v]
          
          | "vs_placeholder", [] -> er "$vs_placeholder"
          | "vs_placeholder2", [] -> er "$vs_placeholder2"
          | "vs_zero", [] -> er "$struct_zero"
          | "vs_fetch", [p] ->
            match p with
              | C.Expr.Ref _ ->
                self p
              | _ ->
                let (ptr, state, _) = vsTrans env p
                match ec.Type with
                  | C.Type.Ref ({ Kind = (C.Struct|C.Union) }) ->
                    bCall "$vs_ctor" [state;  ptr]
                  | _ ->
                    self (C.Deref (ec, C.Macro (p.Common, "vs_placeholder2", []))) 
                             |> bSubst [("$s", state); ("$vs_placeholder2", ptr)]        
                          
          | "vs_updated", [p; src] ->
            let (ptr, state, (bbase, tp)) = vsTrans env p
            match p.Type with
              | C.Ptr t ->
                let wr = trForWrite env t src
                bCall "$vs_ctor" [bCall "$update_int" [state; ptr; wr]; bCall "$vs_base" [bbase; tp]]
              | _ -> helper.Panic("non ptr type in vs_updated")
          
          | "vs_can_update", [up] ->
            match self up with
              | B.FunctionCall ("$vs_ctor", [arr; _]) ->
                bCall "$good_state" [arr]
              | _ -> helper.Panic("wrong thing in vs_can_update")
            
          | "yarra_nondet", [p] ->
            typedRead (bCall "$yarra_heap" [bState]) (self p) ec.Type
          | "by_claim", args ->
            self (C.Expr.Deref (ec, C.Expr.Macro (ec, "by_claim_ptr", args)))
          | "by_claim_ptr", [c; obj; ptr] ->
            bCall "$by_claim" [bState; self c; self obj; self ptr]
          | "current_claim", [] -> er "$claim"
          | "null", [] -> er "$null"
          | "dont_instantiate", [e] ->
            let arg = self e
            match e.Type with
              | C.Type.Integer _ -> bCall "$dont_instantiate_int" [arg]
              | C.Type.SpecPtr _
              | C.Type.PhysPtr _
              | C.Type.ObjectT  -> bCall "$dont_instantiate" [arg]
              | _ -> bCall "$dont_instantiate_int" [castToInt (trType e.Type) arg]
          | "_vcc_claims", [cl; cond] ->
            claims env (self cl) cond
          | "_vcc_in_domain", [s; C.Macro(_, "_vcc_use", [C.UserData(_, lbl); e1]); e2] ->
            bCall "$in_domain_lab" ((selfs [s;e1;e2]) @ [er (trInvLabel ((string)lbl))])
          | "_vcc_in_domain", args ->
              bCall "$in_domain_lab" ((selfs args) @ [er (trInvLabel "public")])
          | "_vcc_in_vdomain", [s; C.Macro(_, "_vcc_use", [C.UserData(_, lbl); e1]); e2] ->
            bCall "$in_vdomain_lab" ((selfs [s;e1;e2]) @ [er (trInvLabel ((string)lbl))])
          | "_vcc_in_vdomain", args ->
              bCall "$in_vdomain_lab" ((selfs args) @ [er (trInvLabel "public")])
          | "_vcc_sk_hack", [e] ->
            bCall "sk_hack" [self e]
          | "_vcc_ptr_eq_pure", [e1; e2] ->
            bEq (self e1) (self e2)
          | "_vcc_ptr_neq_pure", [e1; e2] ->
            bNeq (self e1) (self e2)
          | "_vcc_ptr_eq_null", [e1] ->
            bCall "$is_null" [self e1]
          | "_vcc_ptr_neq_null", [e1] ->
            bCall "$non_null" [self e1]
          | "trigger_hint", [e] ->
            if e.Type = C.Type.Bool then
              bCall "sk_hack" [self e]
            else
              bCall "sk_hack" [bCall "$instantiate_int" [ctx.CastToInt (ctx.TrType e.Type) (self e)]]

          // trigger inference will delete this guy
          | "trigger_level", [e] ->
            bCall "trigger_level" [self e]
            
          | ("_vcc_set_in"|"_vcc_set_in0"), [p; C.Macro (_, "_vcc_owns", _)] ->
            match p.Type with
              | C.Ptr t when not t.IsComposite ->
                helper.Warning (p.Token, 9104, "primitive pointers are unlikely to be in the owns set")
              | _ -> ()
            bCall ("$" + n.Substring 5) (selfs args)
                              
          | "reads_same", [ptr] ->
            let sptr = self ptr
            match ptr.Type with
              | C.Ptr t when t.IsComposite ->
                let expr = bCall "$read_version" [bState; sptr]
                B.Primitive ("==", [expr; B.Old expr])                
              | _ ->
                let expr = bCall "$mem" [bState; sptr]
                B.Primitive ("==", [expr; B.Old expr])
          
          | "reads_same_arr", [_; ptr; sz] ->
            bCall "$same_array" [B.Old bState; bState; self ptr; self sz]
          
          | "keeps", [p1; p2] ->
            match p2.Type with
              | C.Ptr t when not t.IsComposite ->
                helper.Warning (p2.Token, 9104, "primitive pointers are unlikely to be in the owns set")
              | _ -> ()
            bCall "$keeps" [bState; self p1; self p2]         
          | ("inv_check" | "token_holder" | "_vcc_bv_lemma"), [e] ->
            self e
          | "ite", ([cond; th; el] as args) ->
            // TODO: check if this is still needed
            let cond' =
              match cond with
                | C.Expr.Ref (_, { Kind = C.QuantBound }) ->
                  bCall "$bool_id" [self cond]
                | _ -> self cond
            B.Ite (cond', self th, self el)
          | "can_use_frame_axiom_of", [C.Call (_, f, _, _)] ->
            bCall "$can_use_frame_axiom_of" [er ("cf#" + f.Name)]
          | "decreases_level_is", [n] ->
            bEq (self n) (er "$decreases_level")
          | "_vcc_typeof", [e] ->
            typeOf env e                
          | "_vcc_obj_eq", [e1; e2] ->
            bEq (self e1) (self e2)
          | "_vcc_obj_neq", [e1; e2] ->
            bNeq (self e1) (self e2)
          | ("bv_extract_signed" | "bv_extract_unsigned" | "bv_update" as name), args ->
            bCall ("$" + name) (selfs args)
          | "_vcc_extent", [arg] when (match arg.Type with C.Ptr t -> noUnions t | _ -> false) ->
            bCall "$struct_extent" [self arg]              
          | "_vcc_thread_local", [C.Dot (_, p, f)] when not f.IsVolatile && not f.Type.IsComposite && f.Parent.Kind = C.Struct ->
            self (C.Macro (ec, n, [p]))
          | "_vcc_union_active", [C.Dot (_, p, f)] ->
            bCall "$union_active" [bState; self p; er (fieldName f)]
          // avoid warning 9106
          | "keeps_stable", [C.Old (_, _, e1); e2] when not (bContains "$s" (self e1)) ->
             bEq (self e1) (self e2)
          | "keeps_stable", [e1; e2] ->
             bEq (self e1) (self e2)
          | "_vcc_gemb", [e] ->
            let rec strip_dots = function
              | C.Index (_, e, _)
              | C.Dot (_, e, _) -> strip_dots e
              | e -> e
            match strip_dots e with
              | C.Expr.Ref (_, v) as e when v.Kind = C.VarKind.ConstGlobal ->
                self e
              | x -> 
                helper.Error(e.Token, 9651, "gemb(...) applied to non-global", None)
                self x                
          | "instantiate_ptr", [e] ->
            bCall "$instantiate_ptr" [self e]
          | "state", [] -> bState
          | "is_atomic_obj", [e] ->
            let e = self e
            bMultiOr (List.map (bEq e) env.AtomicObjects)
          | "pure_outpar", [ C.Expr.Call(_, fn, targs, args); C.Expr.Ref(_, v); arg] ->
            let args =  List.map ctx.ToTypeIdArraysAsPtrs targs @ convertArgs fn (selfs args)
            let args =
              if fn.IsStateless then args
              else bState :: args
            bEq (addType v.Type (bCall ("F#" + fn.Name + "#OP#" + v.Name) args)) (self arg)
          | "stackframe", [] -> er "#stackframe"
          | "map_eq", [e1; e2] -> bCall ("$eq." + (ctx.TypeIdToName (toTypeId e1.Type))) [self e1; self e2]
          | "default", [] ->
            defaultValueOf ec.Type
          | "float_literal", [C.Expr.UserData(_, f)] ->
            match f with
              | :? float as f -> ctx.GetFloatConst f
              | :? single as s -> ctx.GetFloatConst ((float)s)
              | _ -> die()
          | "dt_testhd", [e; C.UserData (_, (:? C.Function as fn))] ->
            let td = dtType e.Type
            bEq (bCall ("DGH#" + td.Name) [self e]) (er ("DH#" + fn.Name))
          | "size", [e] ->
            let res = abstractSize e.Type (self e)
            if res = abstractSizeUndef then
              helper.Error (ec.Token, 9737, "\\size() can only be called on data types, records and integers")
            res
          | "skip_termination_check", [e] ->
            self e
          | "check_termination", [e] ->
            bCall "$check_termination" [self e]
          | "isolate", [e] -> self e
          | "*", [] ->
            er "*"
          | n, [e] when n.StartsWith "limited#" ->
            let n = if n = "limited#0" then "" else "#" + n
            let repl = function
              | B.FunctionCall (nn, args) when nn.StartsWith "F#" ->
                bCall (nn + n) args
              | ee -> die()
            match self e with
              | B.FunctionCall (name, [e; t]) when name.StartsWith "$" ->
                bCall name [repl e; t]
              | e -> repl e
          | name, [e] when name.StartsWith "DP#" ->
            bCall name [self e]
          | name, [e1; e2] when name.StartsWith("_vcc_deep_struct_eq.") || name.StartsWith("_vcc_shallow_struct_eq.") ->
            B.FunctionCall(name, [self e1; self e2])
          | name, args when name.StartsWith "prelude_" ->
            B.FunctionCall (name.Replace ("prelude_", "$"), selfs args)
          | n, _ when (helper.PureCallSignature n).IsSome ->
            let signature = (helper.PureCallSignature n).Value
            let rec aux acc idx (args:list<C.Expr>) =
              if idx >= signature.Length then
                xassert (args = [])
                let n =
                  if n.StartsWith "_vcc_" then  "$" + n.Substring 5
                  elif n.StartsWith "\\" then "$" + n.Substring 1
                  else "$" + n
                bCall n (List.rev acc)
              else
                let assertFirstIsState() = 
                  match args with
                    | arg :: _ ->
                      match arg.Type with
                        | C.MathTypeRef "\\state" -> ()
                        | _ -> die()
                    | _ -> die()
                          
                match signature.[idx] with
                  | 't' -> 
                    match args with
                      | arg :: rest ->
                        aux (typeOf env arg :: self arg :: acc) (idx + 1) rest
                      | [] -> 
                        helper.Error (ec.Token, 9615, "expecting more arguments in call to " + n, None)
                        aux acc signature.Length []
                  | 'S'
                  | 's' 
                  | 'a'
                  | 'p'
                  | 'i'
                  | '.' ->
                    if (signature.[idx] = 's' || signature.[idx] = 'S') then assertFirstIsState()
                    match args with
                      | arg :: rest ->
                        aux (self arg :: acc) (idx + 1) rest
                      | [] -> 
                        helper.Error (ec.Token, 9615, "expecting more arguments in call to " + n, None)
                        aux acc signature.Length []
                  | _ -> die()
            aux [] 0 args
          | "_vcc_current_context", [] -> IF.getPC
          | "_vcc_expect_unreachable_child", [e] -> B.Expr.FunctionCall("$expect_unreachable_child",[trExpr env e])
          | "_vcc_label_of", [e] -> IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) (IF.exprLevel false e)
          | "_vcc_seclabel_bot", [] -> B.Expr.Ref "$lblset.bot"
          | "_vcc_seclabel_top", [] -> B.Expr.Ref "$lblset.top"
          | "_vcc_lblset_leq", [l1;l2] -> B.Expr.FunctionCall ("$lblset.leq", [trExpr env l1; trExpr env l2])
          | "_vcc_is_member", [p; c] -> B.Expr.FunctionCall("$ptrclub.isMember", [trExpr env p; trExpr env c])
          | _ ->
            if n.StartsWith "lbl_" then
              helper.Error (ec.Token, 9724, sprintf "expression label {:%s ...} unsupported (here)" (n.Substring 4))
            else
              helper.Oops (ec.Token, sprintf "unhandled macro %s" n)
            er "$bogus"                

      and typeOf env (e:C.Expr) =
        match e.Type with
          | C.ObjectT ->
            match e with
              | C.Expr.Macro (_, "_vcc_as_array", [arr; sz]) ->
                bCall "$array" [typeOf env arr; trExpr env sz]
              | _ ->
                bCall "$typ" [trExpr env e]
          | C.Ptr t -> toTypeId t 
          | C.FunctionPtr decl -> er "$fnptr_type"
          | t ->
            helper.Error (e.Token, 9616, t.ToString() + " is not a pointer", None)
            er "$bogus"


      and writesCheck env tok prim (e:C.Expr) =
        match e.Type with
          | C.ObjectT
          | C.Ptr _ ->
            inWritesOrIrrelevant false env (trExpr env e) (if prim then Some e else None)
          | C.MathTypeRef "\\objset" ->
            xassert (not prim)
            writesMultiCheck false env tok (fun p -> bCall "$set_in" [p; trExpr env e])
          | _ -> 
            helper.Error (e.Token, 9617, "unsupported thing passed to writes check (" + e.ToString() + ")", None)
            er "$bogus"

      and writesInclusion env env'  = ()

      and readsCheck env isWf (p:C.Expr) =
        let cond id msg name (args : C.Expr list) = 
          (afmte id msg args.Tail, trExpr env (C.Macro ({p.Common with Type = C.Bool }, name, args)))
        let (codeTp, codeTh, suff) =
          if isWf then (8501, 8502, " (in well-formedness check)")
          else         (8511, 8512, "")
        let th =
          match p with
            | C.Dot (_, p', f) when not f.Parent.IsUnion ->
              let msg, isAtomic =
                match env.AtomicReads with
                  | [] -> "", []
                  | _ ->
                    "or atomically updated ", List.map (bEq (trExpr env p')) env.AtomicReads
              let tok, prop = 
                if f.IsVolatile then
                  cond codeTh ("{0} is mutable " + msg + "(accessing volatile field " + f.Name + ")" + suff) "_vcc_mutable" [cState; p']
                else
                  if not f.Type.IsComposite then
                    cond codeTh ("{0} is thread local " + msg + "(accessing field " + f.Name + ")" + suff) "_vcc_thread_local" [cState; p']
                  else
                    cond codeTh ("{0} is thread local" + suff) "_vcc_thread_local2" [cState; p]
              tok, bMultiOr (prop :: isAtomic)
            | _ -> 
              let msg, isAtomic =
                match env.AtomicReads with
                  | [] -> "", []
                  | _ ->
                      // TODO: shouldn't that be $volatile_span()?
                    " or atomically updated", List.map (fun o -> bCall "$set_in" [trExpr env p; bCall "$span" [o]]) env.AtomicReads
              let tok, prop =
                cond codeTh ("{0} is thread local" + msg + suff) "_vcc_thread_local" [cState; p]
              tok, bMultiOr (prop :: isAtomic)
        [B.Stmt.MkAssert th]
      
      and writesMultiCheck use_wr env tok f =
        let name = "#writes" + ctx.TokSuffix tok
        let p = er name
        let precond = 
          if nestingExtents then 
            bAnd (f p) (bOr (bCall "$is_primitive" [bCall "$typ" [p]]) (bCall "$is_non_primitive" [bCall "$typ" [p]]))
          else f p
        B.Expr.Forall (Token.NoToken, [(name, tpPtr)], dont_inst p, weight "dont-inst", bImpl precond (inWritesOrIrrelevant use_wr env p None))
         
      and inWritesOrIrrelevant use_wr env (e:B.Expr) (origPrim:option<C.Expr>) =
        let prim = origPrim.IsSome
        let atomicWr =
          if prim then
            env.AtomicObjects |>
              List.map (fun o -> bCall "$set_in" [e; bCall "$volatile_span" [bState; o]]) |>
              bMultiOr
          else bFalse
        let pred = if prim || use_wr then "$writable" else "$top_writable"
        let ch = 
          if prim then
            bCall "$writable_prim" [bState; env.WritesTime; e]
          else
            bCall pred (bState :: env.WritesTime :: [e])
        bOr atomicWr ch
        (*
        match origPrim with
          | Some (C.Dot (_, p, f)) when f.Parent.Kind = C.Struct ->
          | _ -> *)
        
      and isInWrites (env:Env) (p:B.Expr) =
        let trWrites acc (e:C.Expr) =
          let test =
            match e.Type with
              | C.ObjectT
              | C.Ptr _ -> bEq p (trExpr env e)
              | C.MathTypeRef "\\objset" -> 
                if isSetEmpty e then bFalse
                else bCall "$set_in" [p; trExpr env e]
              | _ -> helper.Error (e.Token, 9618, "unsupported writes clause " + e.ToString(), None); er "$bogus"
          bOr acc test
        List.fold trWrites bFalse env.Writes

      and claimIn env claim s expr =
        let repl = [("$claim", claim); ("$s", s); ("$when_claimed_state", bState)]
        let doClosed = function
          | B.Expr.FunctionCall ("$closed", args) -> Some (B.Expr.FunctionCall ("$claimed_closed", args))
          | _ -> None
        (bSubst repl (trExpr env expr)).Map doClosed
        
      and claims env claim expr =
        let cs = "#cs" + (!claimStateId).ToString()
        incr claimStateId
        let ms = [er cs]
        let use_claim = bCall "$valid_claim" (ms @ [claim])
        B.Expr.Forall (Token.NoToken, [(cs, tpState)], [[use_claim]], weight "claims",
             bImpl use_claim (claimIn env claim (er cs) expr))      
      
      and vsTrans env p =
        let theBase = ref p
        let lastType = ref None
        let rec findPath = function
          | C.Dot (c, e, f) -> 
            lastType := Some f.Parent
            C.Dot (c, findPath e, f)
          | C.Index (c, e, i) ->
            C.Index (c, findPath e, i)
          | e ->
            theBase := e
            C.Macro (e.Common, "vs_placeholder", [])                    
        let path = findPath p
        match (!theBase).Type with
          | C.MathTypeRef "struct" -> ()
          | _ ->
            helper.Oops (p.Token, "expected $struct type, got " + (!theBase).Type.ToString() + " for " + p.ToString())
        let bbase = trExpr env !theBase
        if (!lastType).IsNone then
          helper.Oops (p.Token, "vsTrans on " + p.ToString())
        let tp = toTypeId (C.Type.Ref ((!lastType).Value))
        let (state, bbase, vsBase) = 
          match bbase with 
            | B.FunctionCall("$vs_ctor", [state; (B.FunctionCall("$vs_base", [bbase; _]) as vsBase)]) -> (state, bbase, vsBase)
            | _ -> bCall "$vs_state" [bbase], bbase, bCall "$vs_base" [bbase; tp]
        let ptr = trExpr env path |> bSubst [("$vs_placeholder", vsBase)]
        (ptr, state, (bbase, tp))      
      
      and trForWrite env t (e2:C.Expr) =
        match e2.Type with
          | C.MathTypeRef "struct" -> die()
          | _ -> ()
        let e2' = trExpr env e2
        match e2.Type with
          | C.Ptr _ -> bCall "$ptr_to_int" [e2']
          | C.Type.Integer _ -> e2'
          | _ ->
            castToInt (trType t) e2'

      let repl e = bSubst [("$$s", er "$s")] e
      
      let trExpr env expr = repl (trExpr env expr)
      let isInWrites e p = repl (isInWrites e p)
      let typeOf env e = repl (typeOf env e)
      let readsCheck env isWf p = 
        List.map (function B.Stmt.Assert (_, t, e) -> B.Stmt.MkAssert (t, repl e) | _ -> die()) (readsCheck env isWf p)
      let objectWritesCheck env expr = repl (inWritesOrIrrelevant false env expr None)
      let claimIn env claim s expr = repl (claimIn env claim s expr)
      let claims env claim expr = repl (claims env claim expr)
      let trForWrite env t e2 = repl (trForWrite env t e2)
      
      let trMacro = ()
      let writesCheck env tok prim (e:C.Expr) = ()
      let writesMultiCheck env tok f = ()
      let vsTrans env p = ()
      let inWritesOrIrrelevant = ()
      
      let trLabel (label:C.LabelId) = label.Name

      let stateChanges (env:Env) =
        if env.Writes = [] then
          bCall "$writes_nothing" [env.WritesState; bState]
        else 
          let inWr = isInWrites env (er "#p") |> bSubst [("$s", env.WritesState)]
          let wrSet = B.Lambda (Token.NoToken, [("#p", tpPtr)], [], inWr)
          bCall "$modifies" [env.WritesState; bState; wrSet]
              
      let rec hasSideEffect = function
        | C.Expr.Ref _
        | C.Expr.IntLiteral _
        | C.Expr.BoolLiteral _ -> false
        | C.Expr.Cast (_, _, e) -> hasSideEffect e
        | C.Expr.Prim (_, _, args) -> List.exists hasSideEffect args      
        | _ -> true
        
      let claimedObjCheck env tok doClaim obj =
        let bobj = trExpr env obj
        let wr = objectWritesCheck env bobj
        let own = List.map (bEq (bCall "$owner" [bState; bobj])) env.AtomicObjects
        let ref_cnt = bCall "$ref_cnt" [bState; bobj]
        let ref_cnt_plus_one =
          B.Expr.Primitive ((if doClaim then "+" else "-"), [ref_cnt; B.Expr.IntLiteral (bigint.One)])
        let tok = 
          let cl_or_uncl = if doClaim then "claim" else "unclaim"
          afmtet tok 8008 ("{0} is non-writable and its owner is not listed in atomic(...) (and thus is impossible to " + cl_or_uncl + ")") [obj]
        let tok2 = 
          afmtet tok 8009 "type of object {0} was not marked with vcc(claimable)" [obj]
        [B.Stmt.MkAssert (tok, bMultiOr (wr :: own));
         B.Stmt.MkAssert (tok2, bCall "$is_claimable" [typeOf env obj]);
         B.Stmt.Call (C.bogusToken, [], "$write_ref_cnt", [bobj; ref_cnt_plus_one]);
         B.Stmt.MkAssume (B.Expr.Primitive (">=", [ref_cnt; B.Expr.IntLiteral (bigint.Zero)]))]
               
      let claimId = ref 0            
      
      let trClaim (env:Env) upgrade tok (local:C.Variable) args =
        match args with
          | C.Pure (_, expr) :: objects ->
            let objects =
              match objects with
                | [C.Macro(_, "_vcc_set_empty", [])] -> []
                | _ -> objects
            let claim = "claim#" + (!claimId).ToString()
            incr claimId
            let conditions = CAST.splitConjunction expr
            let inState = claimIn env (er claim)
            
            let didAlloc = bImpl (bNeq (er claim) (er "$no_claim"))
            let mkInitAssert s (expr:C.Expr) =
              let tok = afmtet tok 8520 "chunk {0} of the claim initially holds" [expr]
              B.Stmt.MkAssert (tok, didAlloc (inState s expr))
              
            let mkAdmAssert s (expr:C.Expr) =
              let tok = afmtet tok 8521 "chunk {0} of the claim holds after a step of the machine" [expr]
              B.Stmt.MkAssert (tok, inState s expr)
            
            let rf n = er (claim + n)
            
            let doObj obj =
              let obj' = trExpr env obj
              let tok' = afmtet tok 8528 "object {0} is closed before claiming it" [obj]
              B.Stmt.MkAssert (tok', bCall "$closed" [bState; obj']) :: claimedObjCheck env tok true obj
            
            let doClaim (obj:C.Expr) =
              let obj' = trExpr env obj
              let tokWrite = afmtet tok 8023 ("{0} is non-writable and (and thus is impossible to upgrade)") [obj]
              let tokWrap = afmtet tok 8024 "the claim {0} is not wrapped before upgrade" [obj]
              let tokRef = afmtet tok 8025 "the claim {0} has outstanding claims" [obj]
              [B.Stmt.MkAssert (tokWrap, bCall "$wrapped" [bState; obj'; er "^^claim"]);
               B.Stmt.MkAssert (tokRef, bEq (bCall "$ref_cnt" [bState; obj']) (bInt 0));
               B.Stmt.MkAssert (tokWrite, objectWritesCheck env obj')]
            
            let killClaim obj =
              B.Call (C.bogusToken, [], "$kill_claim", [trExpr env obj])
                        
            let wrChecks = 
              if upgrade then
                // first checking for conditions and then killing all at once
                // allows for aliasing between claims
                (List.map doClaim objects |> List.concat) @
                  List.map killClaim objects
              else
                List.map doObj objects |> List.concat
            
            let claimAdm =
              [B.Stmt.MkAssume (inState (rf "s1") expr);
               B.Stmt.MkAssume (bCall "$valid_claim_impl" [rf "s0"; rf "s2"]);
               B.Stmt.MkAssume (bCall "$claim_transitivity_assumptions" ([rf "s1"; rf "s2"; er claim; er (ctx.GetTokenConst tok)]));
               ] @
               List.map (mkAdmAssert (rf "s2")) conditions @
               [B.Stmt.MkAssume bFalse]
            let rand = claim + "doAdm"
            let claimAdm cond =
              [B.Stmt.If  (C.bogusToken, bAnd cond (er rand), B.Stmt.Block (B.Stmt.VarDecl ((rand, B.Type.Bool), None) :: claimAdm), B.Stmt.Block [])]
               
            let initial cond = 
              [B.Stmt.MkAssume (didAlloc (bCall "$claim_initial_assumptions" [bState; er claim; er (ctx.GetTokenConst tok)]))] @
              List.map (mkInitAssert bState) conditions @
              claimAdm cond @
              [B.Stmt.MkAssume (didAlloc (claims env (er claim) expr))]
            
            let claims_obj = List.map (fun e -> B.Stmt.MkAssume (bCall (if upgrade then "$claims_upgrade" else "$claims_obj") [er claim; trExpr env e])) objects 
            
            let assign = 
              [B.Stmt.Assign (varRef local, er claim);
               assumeSyncCS "claim constructed" env tok]
                                      
            let initial =
              match env.AtomicObjects with
                | [] -> initial bTrue
                | _ ->
                  let ctx = env.ClaimContext.Value
                  let cond = bNeq (er claim) (er "$no_claim")
                  ctx.ClaimChecks <- initial cond @ ctx.ClaimChecks
                  ctx.ClaimInits <- B.Stmt.MkAssume (bEq (er claim) (er "$no_claim")) :: ctx.ClaimInits 
                  []
                  
            [B.Stmt.VarDecl ((claim, tpPtr), None);
             B.Stmt.VarDecl ((claim + "s0", tpState), None);
             B.Stmt.VarDecl ((claim + "s1", tpState), None);
             B.Stmt.VarDecl ((claim + "s2", tpState), None);
            ] @
            wrChecks @
            [B.Stmt.Assign ((rf "s0"), bState)] @
            [B.Stmt.Call (tok, [claim], "$alloc_claim", [])] @
            claims_obj @
            assign @
            initial
            
          | _ ->           
            helper.Oops (tok, "wrong format of a claim")
            []

      let setWritesTime tok env wr =
        let name = "#wrTime" + ctx.TokSuffix tok
        let p = er "#p"
        let inWritesAt = bCall "$in_writes_at" [er name; p]
        let env = { env with Writes = wr; WritesTime = er name }
        let defWrites =
          B.Stmt.MkAssume (bCall "$def_writes" [bState; er name; B.Expr.Lambda (Token.NoToken, [("#p", tpPtr)], [],  (isInWrites env p))])
        let init =
          [B.Stmt.VarDecl ((name, B.Type.Int), None);
           B.Stmt.MkAssume (bEq (er name) (bCall "$current_timestamp" [bState]));
           defWrites]
        (init, env)
                  
      let trUnclaim env tok = function
        | claim :: objects ->
          let claim' = trExpr env claim
          let doObj obj =
            let obj' = trExpr env obj
            let tok = afmtet tok 8522 "object {0} was claimed by {1}" [obj; claim]
            B.Stmt.MkAssert (tok, bCall "$claims_obj" [claim'; obj']) :: claimedObjCheck env tok false obj
          let tr = trExpr env
          let rec different acc = function
            | x :: xs ->
              let mkDiff y =
                let tok = afmtet tok 8010 "object {0} might equal {1}" [x; y]
                B.Stmt.MkAssert (tok, bNeq (tr x) (tr y))
              different (List.map mkDiff xs @ acc) xs
            | [] -> acc
          let allowWrite = 
            B.Stmt.MkAssert (afmtet tok 8523 "the disposed claim {0} is writable" [claim], objectWritesCheck env claim')
          let different = different [] objects
          let decrements = List.map doObj objects |> List.concat
          let call = B.Stmt.Call (tok, [], "$unclaim", [claim'])
          allowWrite :: different @ [call] @ decrements @ [assumeSyncCS "claim disposed" env tok]
        | _ -> die()
      
      let trAtomic trStmt env (ec:C.ExprCommon) objs body =
        let rec split acc = function
          | C.Stmt (_, C.Macro (_, "begin_update", [])) :: xs -> List.rev acc, xs
          | C.Block (_, xs, _) :: xs' -> split acc (xs @ xs')
          | x :: xs -> split (x :: acc) xs
          | [] -> [], List.rev acc
        
        let getType (obj : C.Expr) (bobj : B.Expr)=
          match obj.Type with
            | C.Ptr(_) -> ptrType obj
            | C.Type.ObjectT -> bCall "$typ" [bobj]
            | _ -> die()
        
        let isGhostAtomic, objs =
          match objs with
            | C.Pure (_, C.Macro (_, "ghost_atomic", [])) :: rest -> true, rest
            | _ -> false, objs

        let isClaim (e:C.Expr) = e.Type = C.Type.SpecPtr C.Claim
        let rec normObj = function
          | C.Pure (_, e) -> normObj e
          | C.Macro (_, "read_only", [e]) when isClaim e -> e
          | e -> e

        let (claims, objs) = objs |> List.map normObj |> List.partition isClaim

        let (before, after) =
          match body with
            | C.Block (_, lst, _) -> split [] lst
            | _ -> [], [body]
        let (save, oldState) = saveState "beforeAtomic"
        let ctx = { ClaimChecks = []; ClaimInits = [] }
        let (atomicInits, atomicObjs, rwObjs) =
          let init = ref []
          let stripRo = function
            | C.Macro (_, "read_only", [a]) -> C.Pure (ec, a)
            | a -> a
          let saveRef e =
            let e' = trExpr env (stripRo e)
            let tmp = "atomicObj#" + (helper.UniqueId()).ToString()
            init := B.Stmt.VarDecl ((tmp, tpPtr), None) :: B.Stmt.Assign (er tmp, e') :: !init
            (er tmp, e)
          let res_rw = objs |> List.filter (fun e -> stripRo e = e) |> List.map saveRef
          let res_ro = objs |> List.filter (fun e -> stripRo e <> e) |> List.map saveRef
          (!init, res_ro @ res_rw, res_rw)
          
        let preEnv = { env with AtomicReads = List.map fst atomicObjs }
        let env' = { preEnv with AtomicObjects = List.map fst rwObjs
                                 OldState = oldState;
                                 ClaimContext = Some ctx }
        let flmap f l = List.map f l |> List.concat
        let checkInv (bobj, (obj:C.Expr)) =
          match obj.Type with
            | C.Ptr (C.Type.Ref td) -> 
              let mkAssert (e:C.Expr) =
                let tok = afmtet obj.Token 8524 "chunk {0} of invariant of {1} holds after atomic" [e; obj]
                B.Stmt.MkAssert (tok, trExpr env' e |> bSubst [("$_this", bobj)])
              td.Invariants 
              |> List.filter (fun i -> not (CAST.isLemmaInv i)) 
              |> List.map CAST.splitConjunction 
              |> List.concat 
              |> List.map mkAssert
            | _ ->
              [B.Stmt.MkAssert (afmte 8525 "invariant of {0} holds after atomic" [obj],
                              bCall "$inv2_without_lemmas" [oldState; bState; bobj; getType obj bobj])]
        
        let valid_claims =
          [for c in claims ->
            B.Stmt.MkAssert (afmte 8526 "claim {0} is valid" [c],
                             bCall "$valid_claim" [bState; trExpr env c])]
                           
        let before =
          if before = [] then []
          else valid_claims @ flmap (trStmt preEnv) before
        
        // this sets env'.ClaimContext things
        let atomicAction = flmap (trStmt env') after

        let atomic_havoc =
          if isGhostAtomic then []
          else [B.Stmt.Call (ec.Token, [], "$atomic_havoc", [])]
          
        atomic_havoc @
        [assumeSyncCS "inside atomic" env ec.Token] @
        atomicInits @
        before @
        valid_claims @
        [for (bobj, obj) in atomicObjs do
             yield B.Stmt.MkAssert (afmte 8527 "{0} is closed (for atomic(...))" [obj], bCall "$closed" [bState; bobj])
             yield B.Stmt.MkAssume (bCall "$inv" [bState; bobj; getType obj bobj])
             ] @
        save @
        ctx.ClaimInits @
        atomicAction @ 
        ctx.ClaimChecks @
        flmap checkInv rwObjs @
        [assumeSync env ec.Token]
        
      
      let isPure bpl =
        let vars = B.writtenVars bpl
        if _list_mem "$s" vars then false
        else
          let isPure = ref true
          let tst = function
            | B.Stmt.Call (_, _, _, _) ->
              isPure := false
              None
            | _ -> None
          B.mapStmt tst bpl |> ignore
          !isPure

      let callConvCnt = ref 0
      let rec trStmt (env:Env) (stmt:C.Expr) =
        let self = trStmt env
        let cmt () = 
          let c = B.Stmt.Comment (((stmt.ToString ()).Replace ("\n", " ")).Replace ("\r", ""))
          if helper.Options.PrintCEVModel then
            B.Stmt.Block [c; captureState "" stmt.Token]
          else
            c
        let doCall (c:C.ExprCommon) (res : C.Variable list) fn (name:string) targs args =
          let name' = 
            if name.StartsWith "_vcc_" then "$" + name.Substring 5 
            else name
          if env.AtomicObjects <> [] then
            match fn with
              | Some (f : C.Function) when f.IsPure && (f.IsSpec || f.Reads.IsEmpty) -> ()
              | _ ->
                match name' with
                  | "$wrap"
                  | "$unwrap"
                  | "$deep_unwrap" 
                  | "$static_wrap"
                  | "$static_unwrap"
                  | "$wrap_set"
                  | "$unwrap_set"
                  | "$alloc" ->
                    helper.Error (c.Token, 9626, name.Substring 5 + "(...) cannot be used inside atomic update/read", None)
                  | "$bump_volatile_version"
                  | "$unclaim"
                  | "$set_closed_owner"
                  | "$giveup_closed_owner"
                  | "$set_closed_owns" -> ()
                  | name when name.StartsWith("lambda#") -> ()
                  | name ->
                    helper.Error (c.Token, 9627, "ordinary functions like " + name + "(...) cannot be used inside atomic update/read", None)
          let args =  List.map (trExpr env) args
          let args, resultIsObjT =
            match fn with
              | Some (f:C.Function) ->
                let resObj =
                  match f.RetType with
                    | C.Ptr _ when f.Name.StartsWith "_vcc_" -> true // not quite sure, maybe not needed
                    | C.ObjectT -> true
                    | _ -> false
                if f.Parameters.Length + (if f.RetType = C.Type.Void then 0 else 1) <> args.Length + res.Length ||
                   f.InParameters.Length <> args.Length
                then
                  helper.Oops (c.Token, "wrong number of parms")
                convertArgs f args, resObj
              | None -> args, false
          let varIsObjT =
            match res with
              | [(v:C.Variable)] when v.Type = C.ObjectT -> true
              | _ -> false
          let args =
            match args, name' with
              | [B.Expr.FunctionCall ("$dot", [p; f])], "$union_reinterpret" -> [p; f]
              | _ -> args
          let resBuf, tail = 
            let setSecLabel = if (env.hasIF) then
                                  match name' with
                                    | ("$stack_alloc"|"$alloc"|"$spec_alloc"|"$spec_alloc_array"|"$alloc_claim") ->
                                     [IF.setPLabel stmt.Token (er (fst (trVar res.Head))) (B.Expr.Ref "$lblset.top")   // Uninitialised memory is high
                                      assumeSync env stmt.Token
                                      IF.setPMeta stmt.Token (er (fst (trVar res.Head))) IF.getPC
                                      assumeSync env stmt.Token
                                      IF.setLLabel ("FlowData#"+(fst (trVar res.Head))) (B.Expr.Ref "$lblset.bot")   // This is the label of the pointer, not the raw data
                                      IF.setLMeta ("FlowData#"+(fst (trVar res.Head))) IF.getPC]
                                    | _ -> []
                                else []
            List.map ctx.VarName res, setSecLabel
          let syncEnv =
            match name' with
              | "$wrap"
              | "$unwrap" 
              | "$static_wrap"
              | "$static_unwrap"
              | "$static_wrap_non_owns"
              | "$wrap_set"
              | "$unwrap_set" 
              | "$atomic_havoc"
              | "$havoc_others"
              | "$unwrap_check" -> { env with AtomicObjects = [er "$no_such_thing"] }
              | _ -> env
          let targs = List.map toTypeId targs
          [cmt (); B.Stmt.Call (c.Token, resBuf, name',  targs @ args); assumeSync syncEnv c.Token] @ tail

        try         
          match stmt with
            | C.Expr.Skip _ -> [B.Stmt.Comment("skip")]
            | C.Expr.Block (_, stmts, None) -> 
              List.concat (List.map self stmts)
            | C.Expr.Comment (_, s) -> 
              [B.Stmt.Comment s]
            | C.Expr.Assert (_, C.Expr.Macro (_, "_vcc_bv_lemma", [e]), []) -> 
              [cmt (); B.Stmt.MkAssert (stmt.Token, bv.TrBvExpr env e)]
            | C.Expr.Assert (_, C.Expr.Macro (_, "reads_check_normal", [e]), []) ->
              cmt () :: readsCheck env false e            
            | C.Expr.Assert (_, e, []) -> 
              [cmt (); B.Stmt.MkAssert (stmt.Token, trExpr env e)]
            | C.Expr.Assert(ec, e, trigs) -> helper.Oops(ec.Token, "non-empty triggers on assert"); trStmt env (C.Expr.Assert(ec, e, []))
            | C.Expr.Assume (_, e) -> 
              [cmt (); B.Stmt.MkAssume (trExpr env e)]
            | C.Expr.Return (c, s) ->
              match s with
              | None -> 
                [cmt ()
                 captureState "function exit" c.Token
                 B.Stmt.MkAssert (c.Token, bCall "$position_marker" [])
                 B.Stmt.Goto (c.Token, ["#exit"])
                 ]
              | (Some e) -> 
                [cmt ()
                 B.Stmt.Assign (B.Expr.Ref "$result", trExpr env e)
                 captureState "function exit" c.Token
                 B.Stmt.MkAssert (c.Token, bCall "$position_marker" [])
                 B.Stmt.Goto (c.Token, ["#exit"])]
            | C.Expr.Macro (_, "havoc", [e ;t]) ->
              [cmt (); B.Stmt.Call (e.Token, [], "$havoc", [trExpr env e; trExpr env t]); assumeSync env e.Token]
            | C.Expr.Macro (_, "_vcc_add_member", [p; c]) ->
              let bClub = trExpr env c
              [B.Stmt.Assign(bClub, B.Expr.FunctionCall("$ptrclub.addMember", [trExpr env p; bClub]))
               B.Stmt.MkAssume(B.Expr.FunctionCall("is_active_ptrclub", [bClub]))]
            | C.Expr.Macro (_, "_vcc_downgrade_to", [C.Expr.Ref _ as v; e]) ->
              let setLabels = [IF.setLLabel ("FlowData#"+(trExpr env v).ToString()) (IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) (IF.exprLevel false e))
                               IF.setLMeta ("FlowData#"+(trExpr env v).ToString()) (B.Expr.Ref "$lblset.bot")]
              let tokNotEqual = afmte 9717 "{0} == {1}" [v; e]
              let tokHighCtxt = afmte 9718 "context is low" [stmt]
              [cmt(); B.Stmt.MkAssert (tokNotEqual, B.Expr.Primitive("==", [trExpr env v; trExpr env e])); B.Stmt.MkAssert (tokHighCtxt, B.Expr.FunctionCall("$lblset.leq",  [IF.getPC; B.Expr.Ref "$lblset.bot"]))] @ setLabels
            | C.Expr.Macro (_, "_vcc_downgrade_to", [C.Expr.Deref (_, var) as v; e]) ->
              let setLabels =
                [IF.setPLabel stmt.Token (trExpr env var) (IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) (IF.exprLevel false e))
                 assumeSync env stmt.Token
                 IF.setPMeta stmt.Token (trExpr env var) (B.Expr.Ref "$lblset.bot")
                 assumeSync env stmt.Token]
              let tokNotEqual = afmte 9717 "{0} = {1}" [v; e]
              let tokHighCtxt = afmte 9718 "context is low" [stmt]
              [cmt(); B.Stmt.MkAssert (tokNotEqual, B.Expr.Primitive("==", [trExpr env v; trExpr env e])); B.Stmt.MkAssert (tokHighCtxt, B.Expr.FunctionCall("$lblset.leq",  [IF.getPC; B.Expr.Ref "$lblset.bot"]))] @ setLabels
            | C.Macro(_, "test_classifier_validity_check", [C.Expr.Quant(ec, {Kind = C.QuantKind.Forall; Variables = [p]; Triggers = trigs; Condition = cond; Body = body})]) ->
              let tokClass = afmte 0000 "the provided test classifier is valid" [stmt]
              let bodyLabel = IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) (IF.exprLevel false body)
              ctx.QuantVarTokens.[p] <- ec.Token
              let p,pt = trVar p
              let bodyCheck = B.Expr.FunctionCall("$seclbl.leq", [B.Expr.ArrayIndex(bodyLabel, [B.Expr.Ref p]); B.Expr.Ref "$seclbl.bot"])
              let conditioned =
                match cond with
                  | None -> bodyCheck
                  | Some c -> B.Primitive("==>", [trExpr env c; bodyCheck])
              [B.Stmt.MkAssert (tokClass,
                                B.Expr.Forall(Token.NoToken,
                                              [p,pt],
                                              [], [],
                                              conditioned))]
            | C.Expr.MemoryWrite (_, e1, e2) when (not env.hasIF) ->
              let e2' =
                match e1.Type with
                  | C.Ptr t -> trForWrite env t e2
                  | _ -> die()
              let e1' = trExpr env e1
              let write_call_args =
                (List.rev (decomposeDot e1')) @ [e2']
              [cmt (); 
               B.Stmt.Call (C.bogusToken, [], "$write_int", write_call_args); 
               assumeSync env e1.Token]
            | C.Expr.MemoryWrite (_, e1, e2) when env.hasIF ->
              let e2' =
                match e1.Type with
                  | C.Ptr t -> trForWrite env t e2
                  | _ -> die()
              let memLoc = trExpr env e1
              let asPointer =
                match e1.Type with
                  | C.Type.PhysPtr (C.Type.PhysPtr _ | C.Type.SpecPtr _) -> true
                  | _ -> false
              let secLabel = IF.contextify (IF.exprLevel asPointer e2)
              let secLabelExpr = IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) secLabel
              [cmt ();
               B.Stmt.Call (C.bogusToken, [], "$write_int", [memLoc; e2']); 
               assumeSync env e1.Token
               IF.setPLabel C.bogusToken (memLoc) (secLabelExpr);
               assumeSync env e1.Token
               IF.setPMeta C.bogusToken (memLoc) (IF.getPC);
               assumeSync env e1.Token]
            | C.Expr.VarWrite (_, [v], C.Expr.Macro (c, "claim", args)) ->
              cmt() :: trClaim env false c.Token v args
              
            | C.Expr.VarWrite (_, [v], C.Expr.Macro (c, "upgrade_claim", args)) ->
              cmt() :: trClaim env true c.Token v args
              
            | C.Expr.Stmt (_, C.Expr.Macro (c, "unclaim", args)) ->
              cmt() :: trUnclaim env c.Token args
            
            | C.Expr.Atomic (ec, objs, body) ->
              captureState "" ec.Token :: trAtomic trStmt env ec objs body
              
            | C.Expr.VarWrite (_, vs, C.Expr.Call (c, fn, targs, args)) -> 
              doCall c vs (Some fn) fn.Name targs args
              
            | C.Expr.VarWrite (_, vs, C.Expr.Macro (c, ("_vcc_blobify"|"_vcc_unblobify" as name), args)) -> 
              doCall c vs None name [] args
              
            | C.Expr.Stmt (_, C.Expr.Call (c, fn, targs, args))        -> 
              doCall c [] (Some fn) fn.Name targs args
            | C.Expr.Macro (c, (("_vcc_reads_havoc"|"_vcc_havoc_others"|"_vcc_unwrap_check"|"_vcc_set_owns"|
                                  "_vcc_giveup_closed_owner"|"_vcc_set_closed_owner"| 
                                  "_vcc_static_wrap"|"_vcc_static_wrap_non_owns"|"_vcc_static_unwrap"|
                                  "_vcc_wrap_set"|"_vcc_unwrap_set"|
                                  "_vcc_unblobify_into") as name), args) -> 
              doCall c [] None name [] args
            | C.Expr.Stmt (_, C.Expr.Macro (c, (("_vcc_unwrap"|"_vcc_wrap"|"_vcc_deep_unwrap") as name), args)) ->
              doCall c [] None name [] args         
              
            | C.Expr.VarWrite (c, [v], C.Expr.Macro(c', "_vcc_new_club", [l])) ->
              [cmt ()
               B.Stmt.Assign (varRef v, B.Expr.FunctionCall("$ptrclub.construct", [B.Expr.Ref "$ptrclub.empty"; trExpr env l]))]
            | C.Expr.VarWrite (c, [v], e) when (not env.hasIF) ->
              [cmt ();
               B.Stmt.Assign (varRef v, trExpr env e)]
            | C.Expr.VarWrite (c, [v], e) when env.hasIF ->
              match v.Type with
                | C.Type.Ref s when s.Name.StartsWith("$map_t.") ->
                  cmt () ::
                  B.Stmt.Assign (varRef v, trExpr env e) :: []
                | C.Type.Map _ ->
                  cmt () ::
                  B.Stmt.Assign (varRef v, trExpr env e) :: []
                | _ ->
                  let (vname,_) = trVar v
                  let asPointer =
                    match v.Type with
                      | C.Type.PhysPtr _ | C.Type.SpecPtr _ -> true
                      | _ -> false
                  let secLabel = IF.contextify (IF.exprLevel asPointer e)
                  cmt () ::
                  B.Stmt.Assign (varRef v, trExpr env e) ::
                  IF.setLLabel ("FlowData#"+vname) (IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) secLabel) ::
                  IF.setLMeta ("FlowData#"+vname) IF.getPC :: []
            | C.Expr.If (ec, cl, c, s1, s2) ->
              let prefix,suffix,innerEnv = 
                if (env.hasIF)              
                 then let explicitClassif = ref false;
                      let classifier = match cl with
                                            | None -> B.Expr.FunctionCall("#classifier#default", [])
                                            | Some cl -> explicitClassif := true; trExpr env cl
                      let cl =
                        match cl with
                          | None -> C.Expr.BoolLiteral(ec, false)
                          | Some cl -> cl
                      let tokHighClassif = afmte 9720 "test classifier is low" [cl]
                      let tokHighCondition = afmte 9719 "test condition is as low as specified by the test classifier" [c; cl]
                      let condLevel = IF.secLabelToBoogie (trExpr env) (fun v -> fst(trVar v)) (IF.exprLevel false c)
                      let classifier = if (!explicitClassif) then B.Expr.Lambda(Token.NoToken, ["CLS#ptr",B.Type.Ref "$ptr"], [], B.Expr.FunctionCall("$select.$map_t..$ptr_to..^^void.^^bool", [classifier; B.Expr.Ref "CLS#ptr"]))
                                                             else IF.makePermissiveUpgrade (trExpr env) (fun v -> fst(trVar v)) trType c classifier
                      let getMapElement map index =
                        B.Expr.ArrayIndex(map, [index])
                      let condLevelCheck = B.Stmt.MkAssert(tokHighCondition,
                                                         B.Expr.Forall(Token.NoToken,
                                                                       ["ptr#CLC",B.Type.Ref "$ptr"],
                                                                       [],
                                                                       [],
                                                                       B.Expr.Primitive("==>",
                                                                                        [B.Expr.Primitive("!", [getMapElement classifier (B.Expr.Ref "ptr#CLC")])
                                                                                         B.Expr.Primitive("==", [B.Expr.ArrayIndex(condLevel, [B.Expr.Ref "ptr#CLC"])
                                                                                                                 B.Expr.Ref "$seclbl.bot"])
                                                                                        ])
                                                                      )
                                                        )
                      let env' = newIFContext env stmt
                      let setPC = [B.Stmt.VarDecl((currentPC env', B.Type.Ref "$labelset"), None)
                                   B.Stmt.Assign(B.Expr.Ref (currentPC env'), IF.getPC)
                                   IF.setPC (stmt.Token)
                                            (B.Expr.Lambda(Token.NoToken,
                                                           ["ptr#setPC", B.Type.Ref "$ptr"],
                                                           [],
                                                           B.Expr.Ite(getMapElement classifier (B.Expr.Ref "ptr#setPC"),
                                                                      B.Expr.Ref "$seclbl.top",
                                                                      B.Expr.Ref "$seclbl.bot")))
                                   assumeSync env stmt.Token]
                      let resetPC = [IF.setPC (stmt.Token) (B.Expr.Ref (currentPC env'))
                                     assumeSync env stmt.Token]
                      condLevelCheck :: setPC, resetPC, env'
                else [],[],env
              let s2 =
                match s2 with                   
                  | C.Expr.Skip(_) -> CAST.possiblyUnreachable
                  | _ -> s2
              captureState "" ec.Token ::
              B.Stmt.Comment ("if (" + c.ToString() + ") ...") ::
              prefix @
              [B.Stmt.If (ec.Token, trExpr env c, B.Stmt.Block (trStmt innerEnv s1), B.Stmt.Block (trStmt innerEnv s2))] @
              suffix
            | C.Expr.Block (comm, stmts, Some bc) ->
              let (save, oldState) = saveState "loop"
              let nonDetVar = "nondet#" + stateId.ToString()
              let varDecl = B.Stmt.VarDecl ((nonDetVar, B.Type.Bool), None)
              let origEnv = env
              let env = { env with OldState = oldState }
              let wrTok =
                if bc.Writes.IsEmpty then comm.Token
                else bc.Writes.Head.Token              
              let (bump, wrCheck, env) =
                    let env' = { env with WritesState = oldState }
                    let (init, env') = setWritesTime wrTok env' bc.Writes
                    let name = "#loopWrites^" + (ctx.TokSuffix wrTok)
                    let p = er name
                    let impl = 
                      let repl = function
                        | B.FunctionCall ("$top_writable", args) -> Some (bCall "$listed_in_writes" args)
                        | _ -> None
                      bImpl ((objectWritesCheck env' p).Map repl) (objectWritesCheck env p)
                    let tok = afmtet wrTok 8027 "writes clause of the block might not be included writes clause of the function" []
                    let bump =  [B.Stmt.Call (tok, [], "$bump_timestamp", []); assumeSync env tok]
                    let check = [B.Stmt.MkAssert (tok, B.Forall (Token.NoToken, [name, tpPtr], [[bCall "$dont_instantiate" [p]]], weight "dont-inst", impl))]
                    (bump, init @ check, env')

              let mkAssert (e:C.Expr) = 
                B.Stmt.Assert ([], afmtet e.Token 8028 "postcondition '{0}' of the block might not hold" [e], trExpr env e)

              let mkAssume (e) = 
                B.Stmt.Assume ([], trExpr origEnv e)
                
              let innerBodyLst =
                  captureState "block start" comm.Token ::                  
                  List.collect (trStmt env) stmts @
                  [captureState "end if the block" comm.Token] @
                  List.map mkAssert bc.Ensures
              let innerBody = B.Stmt.Block innerBodyLst
              let innerVars = B.writtenVars innerBody
              let (check, havoc) =
                if isPure innerBody then
                  [B.Stmt.Assert ([], afmtet comm.Token 0 "OOPS: state changed" [], bEq bState oldState)],
                   [B.Stmt.Havoc innerVars]
                else
                  [],
                   [B.Stmt.Havoc ("$s" :: innerVars);
                    B.Stmt.MkAssume (stateChanges env);
                    B.Stmt.MkAssume (bCall "$timestamp_post" [env.OldState; bState]);
                    assumeSync env comm.Token]
                  
              let callBody = havoc @ List.map mkAssume bc.Ensures
              let innerBodyLst = innerBodyLst @ check @ [B.Stmt.Assume ([], bFalse)]

              let body =
                B.Stmt.If (C.bogusToken, er nonDetVar, B.Stmt.Block innerBodyLst, B.Stmt.Block callBody)
              bump @ save @ wrCheck @ [varDecl; body]

            | C.Expr.Loop (comm, invs, writes, variants, s) ->
              let (save, oldState) = saveState "loop"
              let env = { env with OldState = oldState }
              let writes =
                match writes, env.Writes with
                  | [], fst :: rest ->
                    fst.WithCommon ({ comm with Type = fst.Type }) :: rest
                  | x, _ -> x
              let (bump, wrCheck, env) =
                match writes with
                  | [] -> ([], [], env)
                  | fst :: _ ->
                    let env' = { env with WritesState = oldState }
                    let (init, env') = setWritesTime fst.Token env' writes
                    let name = "#loopWrites^" + (ctx.TokSuffix fst.Token)
                    let p = er name
                    let impl = 
                      let repl = function
                        | B.FunctionCall ("$top_writable", args) -> Some (bCall "$listed_in_writes" args)
                        | _ -> None
                      bImpl ((objectWritesCheck env' p).Map repl) (objectWritesCheck env p)
                    let tok = afmtet fst.Common.Token 8011 "writes clause of the loop might not be included writes clause of the function" []
                    let bump =  [B.Stmt.Call (tok, [], "$bump_timestamp", []); assumeSync env tok]
                    let check = [B.Stmt.MkAssert (tok, B.Forall (Token.NoToken, [name, tpPtr], [[bCall "$dont_instantiate" [p]]], weight "dont-inst", impl))]
                    (bump, init @ check, env')
              let body =
                B.Stmt.While (bTrue, 
                  List.map (fun (e:C.Expr) -> (e.Token, trExpr env e)) invs,
                  B.Stmt.Block ([B.Stmt.MkAssume (stateChanges env);
                                 B.Stmt.MkAssume (bCall "$timestamp_post" [env.OldState; bState]);
                                 assumeSync env comm.Token] @
                                 trStmt env s @
                                 [captureState "after loop iter" comm.Token] ))
              let capture = captureState "before loop" comm.Token
              bump @ save @ wrCheck @ [capture; body; assumeSync env comm.Token]
                
            | C.Expr.VarDecl (b, v, _) when env.hasIF ->
              if v.Kind = C.Parameter || v.Kind = C.SpecParameter || v.Kind = C.OutParameter then []
              else
                let (v', w) = trWhereVar v
                let vname,_ = v'
                cmt() ::
                B.Stmt.VarDecl (v', w) ::
                B.Stmt.VarDecl (("FlowData#"+vname,B.Type.Ref "$flowdata"),None) ::
                IF.setLLabel ("FlowData#"+vname) (B.Expr.Ref "$lblset.top") ::
                IF.setLMeta ("FlowData#"+vname) (B.Expr.Ref "$lblset.bot") :: []
            | C.Expr.VarDecl (b, v, _) when (not env.hasIF) ->
              if v.Kind = C.Parameter || v.Kind = C.SpecParameter || v.Kind = C.OutParameter then []
              else
                let (v', w) = trWhereVar v
                cmt() ::
                B.Stmt.VarDecl (v', w) :: []
            | C.Expr.Goto (c, l) when (not env.hasIF) -> [cmt (); B.Stmt.Goto (c.Token, [trLabel l])]
            | C.Expr.Goto (c,l) when (env.hasIF) ->
              let curPC = currentPC env
              let targetPC = snd(List.find (fun (lbls,_) -> List.exists (fun lbl -> lbl = l) lbls) env.IFContexts)
              if curPC = targetPC then [cmt (); B.Stmt.Goto (c.Token, [trLabel l])]
                                  else [cmt()
                                        B.Stmt.Block [B.Stmt.MkAssert (afmte 9716 "the target label's context is at least as high as the jump's" [stmt],
                                                                     B.Expr.FunctionCall("$lblset.leq",
                                                                                         [IF.getPC
                                                                                          IF.getLabel (B.Expr.Ref(targetPC))]))
                                                      B.Stmt.Goto (c.Token, [trLabel l])]]
            | C.Expr.Label (c, l) -> [B.Stmt.Label (c.Token, trLabel l)]

            | C.Expr.Macro (_, "havoc_locals", []) -> []

            | C.Expr.Macro (_, "havoc_locals", args) ->
              let aux = function
                | C.Expr.Ref (_, v) -> v
                | _ -> die()
              let vars = args |> List.map aux
              let mkAssump v =
                match trWhereVar v with
                  | (_, Some e) -> [e]
                  | _ -> []
              [B.Stmt.Havoc (vars |> List.map ctx.VarName)
               B.Stmt.Assume ([], vars |> List.map mkAssump |> List.concat |> bMultiAnd)]
            
            | C.Expr.Macro (_, "ignore_me", []) -> []
            | C.Expr.Macro (_, "inlined_atomic", [C.Expr.Macro (_, "ignore_me", [])]) -> []
            | C.Expr.Macro (_, "inlined_atomic", [C.Expr.Skip(_)]) -> []

            | e when not (hasSideEffect e) -> []
            
            | _ -> 
              helper.Oops (stmt.Token, "unhandled stmt " + stmt.ToString())
              []
          with
            | Failure _ ->
              helper.Error(stmt.Token, 9600, "OOPS for statement " + stmt.ToString())
              reraise()

      let trHeader (header:C.Function) =
        let env = { initialEnv with Writes = header.Writes }
        let te e = trExpr env e
        let pureEq =
          if genPureFunctionDef header then 
            let parms = 
              (if header.IsStateless then [] else [bState]) @ [for tv in header.TypeParameters -> typeVarRef tv] 
                                                            @ [for v in header.InParameters -> varRef v]
            let tok = CAST.afmtt header.Token 8022 "the pure function '{0}' is underspecified; please supply ensures(result == ...) contract matching the implementation" [header.Name]
            [B.FreeEnsures (bEq (er "$result") (bCall ("F#" + header.Name) parms))]
          else []
        let (writes, ensures) =
          let check (writes, ensures) = function
            | C.Call (_, { Name = "_vcc_public_writes" }, _, [s]) ->
              (s :: writes, ensures)
            | e -> (writes, e :: ensures)
          match List.fold check ([], []) header.Ensures with
            | ([], e) -> (header.Writes, e)
            | acc -> acc
        let ensures = List.rev ensures
        let stateCondition =
          if header.IsPure then
            if writes <> [] then die() // should have been caught earlier!
            []
          else
            [B.FreeEnsures (stateChanges { env with Writes = writes });                    
             B.Modifies "$s";
             B.Modifies "$cev_pc";
             ]
        let tEnsures = function
          | C.Macro(_, "_vcc_assume", [e]) -> B.FreeEnsures(te e)
          | e -> B.Ensures(e.Token, te e)
        let tRequires = function
          | C.Macro(_, "_vcc_assume", [e]) -> B.FreeRequires(te e)
          | e -> B.Requires(e.Token, te e)
        let rec splitConjuncts = function
          | C.Prim(_, C.Op("&&", _), [e1;e2]) -> splitConjuncts e1 @ splitConjuncts e2
          | e -> [e]
        let proc =
          let outPars, inPars = List.map trVar (header.OutParameters), List.map trTypeVar header.TypeParameters @ List.map trVar (header.InParameters)
          let outPars = if header.RetType = C.Type.Void then outPars else ("$result", trType header.RetType) :: outPars
          { Name      = header.Name
            Token     = header.Token
            InParms   = inPars
            OutParms  = outPars
            Locals    = []
            Body      = None
            Contracts = 
              [for e in header.Requires |> List.map splitConjuncts |> List.concat -> tRequires e] @
              [for e in ensures -> tEnsures e] @
              pureEq @ stateCondition @
              [B.FreeEnsures (bCall "$call_transition" [bOld bState; bState])]
            Attributes = 
              [ for attr in header.CustomAttr do
                  match attr with
                    | C.IntBoogieAttr (key, value) -> yield (B.ExprAttr (key, bInt value))
                    | C.BoolBoogieAttr (key, value) -> yield (B.ExprAttr (key, B.Expr.BoolLiteral value))
                    | C.VccAttr(C.AttrSkipVerification, _) when not helper.Options.ExplicitTargetsGiven -> yield (B.ExprAttr ("verify", bFalse))
                    | C.VccAttr ("extra_options", o) -> yield (B.StringAttr ("vcc_extra_options", o))
                    | C.VccAttr (C.AttrBvLemmaCheck, o) -> yield (B.StringAttr ("vcc_bv_lemma_check", o))
                    | C.VccAttr (C.AttrSkipSmoke, o) -> yield (B.StringAttr("vcc_skip_smoke", o))
                    | C.VccAttr _ -> yield! []
                    | C.ReadsCheck _ -> yield! []
                     
              ] } : B.ProcData
        (proc, env)

      let toFieldRef (f:C.Field) =
        er (fieldName f)
        
      let toBaseType (f:C.Field) =
        match f.Type with
          | C.Array (t, _) -> t
          | t -> t
          
      let trField3 (td:C.TypeDecl) (f:C.Field) =
        let isAsArray = CAST.hasCustomAttr C.AttrAsArray f.CustomAttr
        let tdname = er ("^" + td.Name)
        let def =
          [B.Decl.Const ({ Name = fieldName f
                           Type = B.Type.Ref "$field"
                           Unique = true } : B.ConstData)]
        let args = [tdname; toFieldRef f; toTypeId (toBaseType f); bBool f.IsVolatile]
        let args = if f.IsSpec then args else args @ [bInt f.ByteOffset]
        let axs =
          match f.Type with
            | C.Array (_, sz) when isAsArray ->              
              [B.Decl.Axiom (bCall (if f.IsSpec then "$def_ghost_as_array_field" else "$def_phys_as_array_field") (args @ [bInt sz]))]
            | C.Array (_, sz) ->
              if td.IsUnion then
                helper.Error (f.Token, 0, "array fields directly in unions are not supported; surround the array with 'struct { ... } _(myArrayField);' or add _(as_array) attribute")
              [B.Decl.Axiom (bCall (if f.IsSpec then "$def_ghost_arr_field" else "$def_phys_arr_field") (args @ [bInt sz]))]
            | C.Type.Ref (td) when td.Name.Contains "##" && f.ByteOffset = 0 ->
              xassert (not td.IsUnion)
              let args = args |> Seq.take 3 |> Seq.toList
              [B.Decl.Axiom (bCall "$def_group" args)]
            | _ ->
              let defAx = B.Decl.Axiom (bCall (if f.IsSpec then "$def_ghost_field" else "$def_phys_field") args)
              if td.IsUnion && not f.IsSpec then
                let unionAx =
                  B.Decl.Axiom (bCall (if (td.Fields |> List.filter (fun f -> not f.IsSpec)).Head = f then "$is_first_union_field" else "$is_union_field") [toFieldRef f])
                [defAx; unionAx]
              else
                [defAx]
        def @ axs
      
      let rec compositeFields = function
        | C.Type.Ref td -> td.Fields
        | C.Volatile(t)
        | C.Array (t, _) -> compositeFields t
        | _ -> []

      // vcc3-only
      let trCompositeExtent (td:C.TypeDecl) =
        let we = er ("^" + td.Name)
        let s = er "s"
        let forallRM id trig body = B.Expr.Forall (Token.NoToken, [("p", tpPtr); ("q", tpPtr); ("s", tpState)], trig, weight id, body)
        let eq = bEq (er "q")
        let union_active f =
          bCall "$union_active" [er "s"; er "p"; er (fieldName f)]
        let allActive = ref [] 
        let oneField (f:C.Field) =
          let isUnion = td.IsUnion && not f.IsSpec
          let unionThing eq = 
            if isUnion then 
              allActive := union_active f :: !allActive
              bAnd (union_active f) eq
            else eq
          let isAsArray = CAST.hasCustomAttr C.AttrAsArray f.CustomAttr
          if f.Type.IsComposite || isAsArray then
            let dot = bCall "$dot" [er "p"; er (fieldName f)]
            if isAsArray || compositeFields f.Type |> List.exists (fun f -> f.Type.IsComposite) then
              match f.Type with
                | C.Type.Array (_, sz) when not isAsArray ->
                  xassert (helper.ErrorReported || not isUnion)
                  bCall "$in_composite_array_lev2" [er "s"; er "q"; dot; bInt sz]
                | _ -> 
                  let eq = bCall "$in" [er "q"; bCall "$composite_extent" [er "s"; dot; toTypeId f.Type]]
                  unionThing eq
            else
              match f.Type with
                | C.Type.Array (_, sz)  when not isAsArray ->                  
                  xassert (helper.ErrorReported || not isUnion)
                  bCall "$in_composite_array" [er "q"; dot; bInt sz]
                | _ ->
                  unionThing (eq dot)
          else
            if isUnion then
              helper.Error (f.Token, 0, "unions with primitive fields are not supported; either use _(backing_member) attribute or surround the offending field with 'struct { ... } _(myPrimitiveField);'")
            bFalse
        let eqs = td.Fields |> List.map oneField
        let eqs = (eq (er "p")) :: eqs
        let inExt = bCall "$in" [er "q"; bCall "$composite_extent" [er "s"; er "p"; er ("^" + td.Name)]]
        let body = bEq inExt (bMultiOr eqs)          
        let body =
          if td.IsUnion then
            bAnd body (bImpl (bCall "$good_state" [er "s"]) (bMultiOr !allActive))
          else body
        forallRM "composite-extent-def" [[inExt]] body        

      // vcc2-only
      let trField (td:C.TypeDecl) (f:C.Field) =
        let tok = td.Token
        let we = er ("^" + td.Name)
        let isUnion = td.Kind = C.Union
        let isComp (f:C.Field) = f.Type.IsComposite
        let s = er "#s"
        let useIs = true
        let (p, pv) =
          if useIs then er "#p", ("#p", tpPtr)
          else bCall "$ptr" [we; er "#r"], ("#r", B.Type.Int)
        let weTyped = bCall "$typed2" [s; p; we] 
        
        let forallRM id trig body = B.Expr.Forall (Token.NoToken, [pv; ("#s", tpState)], trig, weight id, body)              
        let fieldRef = toFieldRef f
        let baset = toBaseType f
        let dot = bCall "$dot" [p; fieldRef]
        let dott = toTypeId baset
        let ptrref = 
          if f.IsSpec then bCall "$ghost_ref" [p; fieldRef]            
          else B.Primitive ("+", [bCall "$ref" [p]; bInt f.ByteOffset])
        let dotdef = bAnd (bEq dot (bCall "$ptr" [dott; ptrref])) (bCall "$extent_hint" [dot; p])
        let dotdef = if useIs then bInvImpl (bCall "$is" [p; we]) dotdef else dotdef
        let dotdef = B.Forall (Token.NoToken, [pv], [[dot]], weight "def-field-dot", dotdef)
        // ghost fields we treat alike regardless if in union or struct
        let isUnion = if f.IsSpec then false else isUnion          
        
        let fieldoff = bEq (bCall "$field_offset" [fieldRef]) (bInt f.ByteOffset)
        
        let isActive = bEq (bCall "$active_option" [s; p]) fieldRef
        let noInline = if CAST.hasCustomAttr C.AttrAsArray f.CustomAttr then "no_inline_" else ""
        let emb =
          match f.Type with
            | C.Array (_, sz) -> 
              bCall ("$" + noInline + "array_field_properties") [fieldRef; dott; bInt sz; bBool isUnion; bBool f.IsVolatile]
            | _ ->
              let tsOfDot = bCall "$ts" [s; dot]
              let statusOfDot = bCall "$st" [s; dot]
              let emb = bCall "$field_properties" [s; p; fieldRef; dott; bBool f.IsVolatile]
              let triggers = [ (* [dot; bCall "$typed" [s; p]]; *) [tsOfDot]; [statusOfDot]]
              let emb =
                if isUnion then bInvImpl (bAnd weTyped isActive) emb
                else            bInvImpl weTyped emb
              forallRM "def-field-typed" triggers emb
        
        (*        
        let maybeArrayProp name =
          let whostyped = if isUnion then (bAnd weTyped isActive) else weTyped
          let dname = "$" + name
          let res =
            match f.Type with
              | C.Array (_, sz) -> bCall ("$is_" + name + "_array") [s; dot; dott; bInt sz]
              | _ -> bCall dname [s; dot]
          bImpl (bAnd whostyped (bCall dname [s; p])) res
            
        let mutableTrans =
          forallRM "def-field-trans" [if f.Type = baset then [bCall "$st" [s; dot]]
                                      else bCall "$typed" [s; p] :: (if useIs then [bCall "$is" [p; we]] else [])]
                                     (if f.IsVolatile then maybeArrayProp "mutable"
                                      else bAnd (maybeArrayProp "mutable") (maybeArrayProp "thread_local"))
        *)
        
        let unionAxioms () =
          [B.Decl.Axiom (bCall "$is_union_field" [we; fieldRef])]
        
        let primVolatile() =
          B.Decl.Axiom (bCall "$static_field_properties" [fieldRef; we]) ::
            match f.Type with
              | C.Array (t, sz) when not t.IsComposite ->
                if CAST.hasCustomAttr C.AttrAsArray f.CustomAttr then
                  []
                elif f.IsVolatile then
                  [B.Decl.Axiom (bCall "$is_primitive_embedded_volatile_array" [fieldRef; bInt sz; dott])]
                else
                  [B.Decl.Axiom (bCall "$is_primitive_embedded_array" [fieldRef; bInt sz])]
              | t when t.IsComposite -> [] 
              | _ when f.IsVolatile ->
                [B.Decl.Axiom (bCall "$is_primitive_volatile_field" [fieldRef])]
              | _ ->
                [B.Decl.Axiom (bCall "$is_primitive_non_volatile_field" [fieldRef])]
           
        let arraySize() =
            match f.Type with
              | C.Array (t, sz) ->
                [B.Decl.Axiom (bEq (bCall "$embedded_array_size" [fieldRef; toTypeId t]) (bInt sz))]
              | _ -> []
          
        let fldOffsetAxioms =
          //if td.GenerateFieldOffsetAxioms || helper.Options.GenerateFieldOffsetAxioms then
            (if f.IsSpec then [] else [B.Decl.Axiom fieldoff]) @ [B.Decl.Axiom dotdef]
          //else []

        [B.Decl.Const ({ Name = fieldName f
                         Type = B.Type.Ref "$field"
                         Unique = true } : B.ConstData)] @
        primVolatile() @
        arraySize() @
        fldOffsetAxioms @
        [B.Decl.Axiom emb] @ 
        //(if f.Type.IsComposite then [] else [B.Decl.Axiom mutableTrans]) @
        (if isUnion then unionAxioms () else []) @
        (if f.Name = "$owns" then [B.Decl.Axiom (bEq (bCall "$owns_set_field" [we]) fieldRef)] else [])
        
        
        
      let trStructEq deep (td:C.TypeDecl) =
        let deepStr = if deep then "deep" else "shallow"
        let vars = [("#p1", tpStruct); ("#p2", tpStruct)]
        let s1 = er "#p1"
        let s2 = er "#p2"
        let idx = er "#i"
        let eqFunName typeName deep = "_vcc_" + deep + "_struct_eq." + typeName
        let eqFun = B.Function(B.Type.Bool, [], eqFunName td.Name deepStr, vars, None)
        let typeRef = toTypeId (C.Type.Ref td)
        let fldEqual inUnion (f : C.Field) =
          let rec read arrayElementType v = 
            let state = bCall "$vs_state" [v]
            let fldAccess = 
              match arrayElementType with
                | None -> fun v f -> bCall "$dot" [bCall "$vs_base" [v; typeRef]; er (fieldName f)]
                | Some t -> fun v f -> mkIdx (bCall "$dot" [bCall "$vs_base" [v; typeRef]; er (fieldName f)]) idx (fun () -> toTypeId t)
            function
              | C.Array(t, n) -> 
                match arrayElementType with
                  | Some _ ->
                    helper.Error(f.Token, 9656, "equality for structures with nested arrays not supported", Some(td.Token))
                    die()
                  | None -> read (Some t) v t 
              | C.Ref(td) when not td.IsMathValue ->
                  bCall "$vs_ctor" [ state; bCall "$dot" [bCall "$vs_base" [v; typeRef]; er (fieldName f)]]
              | t ->
                typedRead state (fldAccess v f) t
//              | C.Bool -> bCall "$read_bool" [state; fldAccess v f]
//              | C.Integer _
//              | C.Ptr _ // using $read_ptr() would add type information, but this isn't needed
//              | C.Map(_,_) -> bCall "$mem" [state; fldAccess v f]
//              | t ->
//                die()
          let read = read None

          match f.Type with // _vcc_deep_struct_eq.S($vs_ctor(#s2, $dot(#p, T.s1)),
            | C.Ref _ when not deep && not inUnion -> None
            | C.Ref td' when not td'.IsMathValue ->
                let funName = eqFunName td'.Name (if deep then "deep" else "shallow")
                Some(bCall funName [read s1 f.Type; read s2 f.Type]) 
            | C.Array(t,n) -> 
              let cond = B.Expr.Primitive ("==>", [ bAnd (B.Expr.Primitive("<=", [bInt 0; idx])) (B.Expr.Primitive("<", [idx; bInt n]));
                                                      bEq (read s1 f.Type) (read s2 f.Type) ])
              Some(B.Forall(Token.NoToken, [("#i", B.Int)], [], weight "array-structeq", cond))

            | _ -> 
              Some (typedEq f.Type (read s1 f.Type) (read s2 f.Type))
        let andOpt e = function 
          | None -> e
          | Some e' -> bAnd e e'

        let eqCall = bCall (eqFunName td.Name deepStr) [s1; s2]
        let eqExpr = 
          match td.Kind with
          | C.TypeKind.Struct -> td.Fields |> List.map (fldEqual false) |> List.fold andOpt bTrue
          | C.TypeKind.Union ->
            let getAO v = bCall "$active_option" [bCall "$vs_state" [v]; bCall "$vs_base" [v; typeRef] ]
            let aoEq = bEq (getAO s1) (getAO s2)
            let fldEqualCond (f : C.Field) =
              match fldEqual true f with
                | Some expr -> B.Primitive("==>", [bEq (getAO s1) (er (fieldName f)); expr])
                | None -> die()
            td.Fields |> List.map fldEqualCond |> List.fold bAnd aoEq
            //activeOptionEq = 
            //bEq (bCall "$active_option" [s; p]) fieldRef
          | _ -> die()
        let eqForall = B.Forall(Token.NoToken, vars, [[eqCall]], weight "eqdef-structeq", bEq eqCall eqExpr)
        [eqFun; B.Axiom eqForall]


      let imax x y = if x < y then y else x
      let imin x y = if x < y then x else y
      
      let typeNesting types =
        let withNest = List.map (fun td -> (td, ctx.TypeDepth (C.Type.Ref td))) types  
        let withNest = List.sortWith (fun (_, x) -> fun (_, y) -> x - y) withNest
        let nestings = gdict()
        let isNested = gdict()
        for (td, n) in withNest do
          if n = 1 then
            isNested.Add((td, td), (0, 0))
            nestings.Add(td, [0, td])
          else
            let lst = ref [0, td]
            for f in td.Fields do
              match f.Type with
                | C.Type.Ref ({Kind = C.Union|C.Struct} as td') ->
                  lst := List.map (fun (l, t) -> (l + 1, t)) nestings.[td'] @ !lst
                | _ -> ()
            nestings.Add(td, !lst)
            for (l, td') in !lst do
              match isNested.TryGetValue ((td', td)) with
                | true, (x, y) ->
                  isNested.[(td', td)] <- (imin l x, imax l y)
                | _ -> isNested.[(td', td)] <- (l, l)
        
        let aux res (td, n) =
          let name td = toTypeId (C.Type.Ref td)
          let aux' res (td', n') =
            let expr =
              match isNested.TryGetValue ((td', td)) with
                | true, (x, y) when td' <> td -> bCall "$is_nested_range" [name td'; name td; bInt x; bInt y]
                | _ -> bNot (bCall "$is_nested" [name td'; name td])
            B.Decl.Axiom expr :: res
          let selfLev = B.Decl.Axiom (bEq (bCall "$nesting_level" [name td]) (bInt n))
          selfLev :: List.fold aux' res withNest
        List.fold aux [] withNest
        
        // The code below tries to optimize the size of the encoding of the tree.
        // For a sample HV source (ca 300 types, 150 second or higher level, 150 types with single or
        // no nesting), it reduces from 90K axioms to 30K (just levels) down to 15k (taking single
        // or no nesting into account). There is however no evidence that it would help, those is_nested(...)
        // terms shouldn't polute the search space in any way.
        (*
        let parents = gdict()
        for td in types do
          for td' in nestings.[td] do
            if td <> td' then
              match parents.TryGetValue td' with
                | true, Some x when x = td -> ()
                | false, _ -> parents.[td'] <- Some td
                | true, Some _ -> parents.[td'] <- None
                | _ -> ()
        
        
        let aux res (td, n) =
          let name td = toTypeId (C.Type.Ref td)
          let aux' res (td', n') =
            if n' >= n then res
            else
              match parents.TryGetValue td' with
                | false, _
                | true, Some _ -> res
                | true, None ->                
                  let expr = bEq (bCall "$is_nested" [name td'; name td]) (bBool (isNested.ContainsKey (td', td)))
                  B.Decl.Axiom expr :: res
          let selfLev = B.Decl.Axiom (bEq (bCall "$nesting_level" [name td]) (bInt n))
          let selfDesc =
            match parents.TryGetValue td with
              | false, _ -> bCall "$no_known_nesting" [name td]
              | true, Some td' -> bCall "$single_known_nesting" [name td; name td']
              | true, None -> bCall "$is_known_type" [name td]
          selfLev :: B.Decl.Axiom selfDesc :: List.fold aux' res withNest
        List.fold aux [] withNest
        *)
        
        

      let trCompositeType (td:C.TypeDecl) =
        let tok = td.Token
        let we = er ("^" + td.Name)
        let isUnion = td.Kind = C.Union
        let isComp (f:C.Field) =
          match f.Type with
            | C.Array _ when CAST.hasCustomAttr C.AttrAsArray f.CustomAttr -> true
            | _ -> f.Type.IsComposite

        let p = er "#p"
        let q = er "#q"
        let r = er "#r"
        let s = er "#s"
        
        let substOld l (e:B.Expr) =
          let rec outsideOld = function
            | B.Expr.Old e -> Some (e.Map insideOld)
            | _ -> None
          and insideOld = function
            | B.Expr.Ref n -> _try_assoc n l
            | _ -> None          
          e.Map outsideOld

        let s1 = er "#s1"
        let s2 = er "#s2"
        let s1s2p = [("#s1", tpState); ("#s2", tpState); ("#p", tpPtr)]
        let s2r = [("#s2", tpState); ("#r", B.Type.Int)]
        let s1s2pwe = [s1; s2; p; we];
        
        let is_claimable = ref false
        let owns_set_is_volatile = ref false
          
        List.iter (function C.VccAttr ("claimable", _) -> is_claimable := true
                          | C.VccAttr ("volatile_owns", _) -> owns_set_is_volatile := true
                          | _ -> ()) td.CustomAttr
            
        let isNoLemmaInvariant = function
          | C.Macro(_, "labeled_invariant", [C.Macro(_, "lemma", []); _]) -> false
          | _ -> true
        let stripLabel = function
          | C.Macro(_, "labeled_invariant", [_; i]) -> i                  
          | i -> i
        let gatherByLabel invs = 
          let dict = new Dict<_,_>()
          let add = 
            let add' lbl i =
              match dict.TryGetValue(lbl) with
                | true, invs -> dict.[lbl] <- i::invs
                | false, _ -> dict.[lbl] <- [i]
            function
              | C.Macro(_, "labeled_invariant", [C.Macro(_, lbl, []); i]) -> add' lbl i
              | i -> add' "public" i
          List.iter add invs
          [ for kv in dict -> (kv.Key, List.rev kv.Value) ] |> List.sortBy fst
          
        let removeTrivialEqualities (bExpr : B.Expr) =
          let rec rte = function
            | B.Primitive("==", [be1; be2]) when be1 = be2 -> Some(bTrue)
            | B.Primitive("!=", [be1; be2]) when be1 = be2 -> Some(bFalse)
            | B.Primitive("||", [be1; be2]) -> Some(bOr (be1.Map(rte)) (be2.Map(rte)))
            | B.Primitive("&&", [be1; be2]) -> Some(bAnd (be1.Map(rte)) (be2.Map(rte)))
            | B.Primitive("==>", [be1; be2]) -> Some(bImpl (be1.Map(rte)) (be2.Map(rte)))
            | _ -> None
          bExpr.Map(rte)
            
        let doInv e = 
          e |> 
            trExpr initialEnv |>
            substOld [("$s", s1)] |>
            bSubst [("$_this", p); ("$s", s2)]
        let toInv exprs = bMultiAnd (exprs |> List.map doInv) 
        let invcall = bCall "$inv2" s1s2pwe
        let invWithoutLemmasCall = bCall "$inv2_without_lemmas" s1s2pwe
        let typedPtr = bCall "$ptr" [we; r]
        let invlabcall lbl = bCall "$inv_lab" [s2; typedPtr; er (ctx.TrInvLabel lbl)]
        let normalizeLabeledInvariant = bSubst [("#s1", er "#s2"); ("#p", typedPtr)] >> removeTrivialEqualities
        let invlab (lbl,exprs) = 
          let invcall = invlabcall lbl
          B.Forall(Token.NoToken, s2r, [[invcall]], weight "eqdef-inv", (bEq (invcall) (toInv exprs |> normalizeLabeledInvariant)))
        let inv = B.Forall (Token.NoToken, s1s2p, [[invcall]], weight "eqdef-inv", (bEq invcall (toInv (td.Invariants |> List.map stripLabel))))
        let invWithoutLemmas = B.Forall (Token.NoToken, s1s2p, [[invWithoutLemmasCall]], weight "eqdef-inv", (bEq invWithoutLemmasCall (toInv (td.Invariants |> List.filter isNoLemmaInvariant |> List.map stripLabel))))
        let labeledInvs = td.Invariants |> gatherByLabel |> List.map invlab |> List.map (fun e -> B.Axiom(e))
        
        let extentCall extentName meta union1 (fields:list<C.Field>) =
          let auxPtr r =
            bCall "$ptr" [we; r]
          let auxDot r f =
            bCall "$dot" [auxPtr r; toFieldRef f] 
          let auxTyped r f =
            bCall "$typed" [s; auxDot r f]
          let typedCond r (f:C.Field) = 
            if meta && union1 && not f.IsSpec then
              bEq (bCall "$active_option" [s; auxPtr r]) (toFieldRef f)
            else bTrue
          let qvars = (if meta then [("#s", tpState)] else []) @ [("#q", tpPtr); ("#r", B.Type.Int)]
          let args = (if meta then [s] else []) @ [q; auxPtr r]
          let bExtentCall = bCall extentName args
          let inExtent (fld:C.Field) dot =
            let common = (if meta then [s] else []) @ [q; dot]
            match fld.Type with
              | C.Array (t, sz) -> 
                let add = [toTypeId t; bInt sz]
                if CAST.hasCustomAttr C.AttrAsArray fld.CustomAttr then
                  let args = (if meta then [s] else []) @ [q; bCall "$as_array" (dot :: add)]
                  bCall extentName args
                else
                  if t.IsComposite then bCall (extentName.Replace ("$in_", "$in_array_")) (common @ add)
                  else bCall "$in_array" ([q; dot] @ add)
              | t ->            
                if t.IsComposite then bCall extentName common
                else bEq q dot
          let isAField = bMultiOr (List.map (function fld -> bAnd (inExtent fld (auxDot r fld)) (typedCond r fld)) fields)
          let body = bOr (bEq q (auxPtr r)) isAField
          B.Forall (Token.NoToken, qvars, [[bExtentCall]], weight ("eqdef-extent-" + extentName.Replace ("$", "")), bEq bExtentCall body)
        
        let spansCalls (fields:list<C.Field>) =          
          let maybeArrayLift r f prop =
            let dot = bCall "$dot" [r; toFieldRef f]
            match f.Type with
              | C.Type.Array (t, sz) ->
                let idx = bCall "$idx" [dot; er "#i"; toTypeId t]
                B.Forall (Token.NoToken, [("#i", B.Type.Int)], [[idx]], weight "array-span",
                       bInvImpl (bCall "$in_range" [bInt 0; er "#i"; bInt (sz - 1)]) (prop idx))
              | _ -> prop dot

          let auxDot r f =
            bCall "$dot" [r; toFieldRef f] 
          let qvars = [("#p", tpPtr); ("#s1", tpState); ("#s2", tpState)]
          let args = [s1; s2; p; we]
          let bSpansCall = bCall "$state_spans_the_same" args
          let bNonVolatileSpansCall = bCall "$state_nonvolatile_spans_the_same" args
          let mkForall call fields =
            B.Forall (Token.NoToken, qvars, [[call]], weight "eqdef-span", bEq call 
              (bMultiAnd (List.map (function fld -> maybeArrayLift p fld (fun idx -> bCall "$mem_eq" [s1; s2; idx])) fields)))
          (mkForall bSpansCall fields, mkForall bNonVolatileSpansCall (List.filter (fun fld -> not fld.IsVolatile) fields))
        
        let extentProp propName twostate union1 includeSelf primFieldProp (fields:list<C.Field>) =
          let auxPtr r =
            bCall "$ptr" [we; r]
          let auxDot r f =
            bCall "$dot" [auxPtr r; toFieldRef f] 
          let typedCond r (f:C.Field) = 
            if union1 && not f.IsSpec then
              bEq (bCall "$active_option" [(if twostate then (er "#s2") else er "#s1"); auxPtr r]) (toFieldRef f)
            else bTrue
          let qvars = ("#s1", tpState) :: (if twostate then [("#s2", tpState)] else []) @ [("#r", B.Type.Int)]
          let states = er "#s1" :: (if twostate then [er "#s2"] else []) 
          let prop p = bCall ("$extent_" + propName) (states @ [p])
          let hasProp (fld:C.Field) dot =
            match fld.Type with
              | C.Array (t, sz) ->
                if CAST.hasCustomAttr C.AttrAsArray fld.CustomAttr then
                  prop (bCall "$as_array" [dot; toTypeId t; bInt sz])
                else 
                  let idx = bCall "$idx" [dot; er "#i"; toTypeId t]
                  let fieldProp = if t.IsComposite then prop else primFieldProp
                  B.Forall (Token.NoToken, [("#i", B.Type.Int)], 
                         //[[bCall ("$" + propName) (states @ [idx])]],
                         [[idx]], weight "array-extentprop",
                         bInvImpl (bCall "$in_range" [bInt 0; er "#i"; bInt (sz - 1)]) (fieldProp idx))
              | t -> if t.IsComposite then prop dot else primFieldProp dot
              
          let allHaveProp = bMultiAnd (List.map (function fld -> bInvImpl (typedCond r fld) (hasProp fld (auxDot r fld))) fields)
          let body = if includeSelf then bAnd (bCall ("$" + propName) (states @ [auxPtr r])) allHaveProp else allHaveProp
          let bExtentCall = prop (auxPtr r)
          B.Forall (Token.NoToken, qvars, [[bExtentCall]], weight "eqdef-extentprop", bEq bExtentCall body)
        
        let allFields = td.Fields
        let primFields = List.filter (function fld -> not (isComp (fld))) allFields
        let in_full_extent_of = extentCall "$in_full_extent_of" false false allFields
        
        let in_extent_of = 
          if nestingExtents then
            let q = bCall "$ptr" [we; er "#r"]
            let in_ext = bCall "$in_extent_of" [er "#s"; er "#p"; q] 
            let depth = ctx.TypeDepth (C.Type.Ref td)
            let rec is_emb acc lev emb in_range =
              if lev >= depth then acc
              else
                let emb = bCall "$emb" [er "#s"; emb]
                let here =
                  if in_range then bCall "$is_emb_at_lev" [er "#p"; emb; q; bInt lev]
                  else bEq q emb
                is_emb (bOr acc here) (lev + 1) emb in_range
            let is_emb = is_emb (bEq (er "#p") q) 1 (er "#p")
            let quant in_range = 
              B.Forall (Token.NoToken, ["#s", tpState; "#p", tpPtr; "#r", B.Int], 
                        [[in_ext]], weight "eqdef-extent",
                        if in_range then bImpl in_ext (is_emb true)
                        else bImpl (is_emb false) in_ext)
            bAnd (quant true) (quant false)
          else
            if isUnion then
              extentCall "$in_extent_of" true true allFields
            else
              let def = extentCall "$in_extent_of" true false allFields
              if noUnions (C.Type.Ref td) then
                match def with
                  | B.Forall (tok, vars, [[extent]], attrs, body) ->
                    let us = bCall "$ptr" [we; er "#r"]
                    let d1 = B.Forall (tok, vars, [[extent]], attrs, bEq extent (bCall "$in_struct_extent_of" [er "#q"; us]))
                    if ctx.TypeDepth (C.Type.Ref td) = 2 then
                      let consq = bOr (bEq (er "#q") us) (bEq (bCall "$emb" [er "#s"; er "#q"]) us)
                      bAnd d1 (B.Forall (tok, vars, [[extent]], attrs, bInvImpl (bCall "$typed" [er "#s"; us]) (bEq extent consq)))
                    else d1
                  | _ -> die()
              else def        
        
        let in_span_of = extentCall "$in_span_of" false false primFields   
        let ignorePrimField _ = bTrue     
        let readAnyIsZero field = bEq (bCall "$mem" [ er "#s1"; field ]) (bInt 0)
        let extentProps = List.map B.Decl.Axiom
                              [extentProp "mutable" false isUnion true ignorePrimField allFields;
                               extentProp "is_fresh" true isUnion true ignorePrimField allFields;
                               extentProp "zero" false isUnion false readAnyIsZero td.Fields ]
        
        let (state_spans_the_same, state_nonvolatile_spans_the_same) = spansCalls primFields
                
        let forward = [bDeclUnique tpCtype ("^" + td.Name)]
                          
        let forward =
          let defName = if isUnion then "$def_union_type" else "$def_struct_type"
          let defAx = bCall defName [we; bInt td.SizeOf; B.Expr.BoolLiteral !is_claimable; B.Expr.BoolLiteral !owns_set_is_volatile]
          let seq =
            if !owns_set_is_volatile || td.Fields |> List.exists (fun f -> f.IsVolatile) then []
            else [B.Decl.Axiom (bCall "$is_span_sequential" [we])]
          forward @ seq @ [B.Decl.Axiom defAx]
           
        let volatile_owns = B.Decl.Axiom (bEq (bCall "$has_volatile_owns_set" [we]) (B.Expr.BoolLiteral !owns_set_is_volatile))
        let claimable = B.Decl.Axiom (bEq (bCall "$is_claimable" [we]) (B.Expr.BoolLiteral !is_claimable))
           
        let forward = 
          match td.GenerateEquality with
          | C.StructEqualityKind.NoEq -> forward
          | C.StructEqualityKind.ShallowEq -> (trStructEq false td) @ forward
          | C.StructEqualityKind.DeepEq -> (trStructEq true td) @ (trStructEq false td) @ forward

        forward @ 
            [ B.Decl.Axiom inv; B.Decl.Axiom invWithoutLemmas; B.Decl.Axiom (trCompositeExtent td) ] 
              @ List.concat (List.map (trField3 td) allFields)

      let trRecord2 (td:C.TypeDecl) =
        let intKind = function
          | C.Type.Integer _ as t -> toTypeId t
          | C.Type.MathInteger C.MathIntKind.Unsigned -> er "^^nat"
          | C.Type.MathInteger C.MathIntKind.Signed -> er "^^mathint"
          | _ -> er "^^mathint"
        let trRecField (f:C.Field) =
          [B.Decl.Const { Unique = true; Name = fieldName f; Type = B.Type.Ref "$field" };
           B.Decl.Axiom (bCall "$is_record_field" [toTypeId (C.Type.Ref td); er (fieldName f); toTypeId f.Type]);
           B.Decl.Axiom (bEq (bCall "$record_field_int_kind" [er (fieldName f)]) (intKind f.Type))]
        List.map trRecField td.Fields |> List.concat
      
      let mkSelector rt tp name ff =
        let constrained =
          match tp with
            | C.Type.MathInteger C.MathIntKind.Unsigned 
            | C.Type.Integer _ -> bCall "$unchecked" [toTypeId tp; ff]
            | C.Type.SpecPtr t -> bCall "$spec_ptr_cast" [ff; toTypeId t]
            | C.Type.PhysPtr t -> bCall "$phys_ptr_cast" [ff; toTypeId t]
            | _ -> ff
        (B.Decl.Function (trType tp, [], name, [("r", rt)], None), constrained)
     
      let plusOne sz = B.Primitive ("+", [sz; bInt 1])
       
      let trRecord3 (td:C.TypeDecl) =
        let name = td.Name
        let rt = trType (C.Type.Ref td)
        let loc f = fieldName f
        let ctorArgs = td.Fields |> List.map (fun f -> (loc f, trType f.Type)) 
        let ctorCall = bCall ("RC#" + name) (ctorArgs |> List.map (fun (n, _) -> er n))
        let rf f e = bCall ("RF#" + fieldName f) [e]
        let sum = ref (bInt 0)
        let trRecField (f:C.Field) =
          let sel = rf f ctorCall
          let ff = er (loc f)
          let fndef, constrained = mkSelector rt f.Type ("RF#" + fieldName f) ff
          sum := bPlus !sum (abstractSize f.Type constrained)
          fndef, bEq (rf f ctorCall) constrained
        let injArgs = td.Fields |> List.map (fun f -> rf f (er "r"))
        let eqArgs = td.Fields |> List.map (fun f -> typedEq f.Type (rf f (er "a")) (rf f (er "b")))
        let eqAB = bCall ("REQ#" + name) [er "a"; er "b"]
        let prjFuns, eqs = List.map trRecField td.Fields |> List.unzip
        let szEq =  bEq (abstractSize (C.Type.Ref td) ctorCall) (plusOne !sum)
        let tdef = [
          B.Decl.TypeDef (recTypeName td)
          B.Decl.Function (rt, [], "RC#" + name, ctorArgs, None)
          B.Decl.Function (B.Type.Int, [], "RSZ#" + name, ["a",rt], None)
          B.Decl.Function (B.Type.Bool, [], "REQ#" + name, ["a",rt; "b",rt], None)
          B.Decl.Const { Unique = false; Name = "RZ#" + name; Type = rt }
          B.Decl.Axiom (B.Forall (Token.NoToken, ctorArgs, [[ctorCall]], [], bMultiAnd (szEq :: eqs)))
          B.Decl.Axiom (B.Forall (Token.NoToken, [("r", rt)], [], [], bEq (er "r") (bCall ("RC#" + name) injArgs)))
          B.Decl.Axiom (B.Forall (Token.NoToken, [("r", rt)], [], [], B.Expr.Primitive ("<", [bInt 0; abstractSize (C.Type.Ref td) (er "r")])))
          B.Decl.Axiom (B.Forall (Token.NoToken, ["a",rt; "b",rt], [[eqAB]], [],  bImpl (bMultiAnd (eqArgs)) eqAB))
          B.Decl.Axiom (B.Forall (Token.NoToken, ["a",rt; "b",rt], [[eqAB]], [],  bEq (eqAB) (bEq (er "a") (er "b"))))
        ] 
        tdef @ prjFuns
      
      let trDataType (td:C.TypeDecl) =
        let rt = trType (C.Type.Ref td)
        let name = td.Name
        let hd e = bCall ("DGH#" + name) [e]
        let dtsz e = bCall ("DSZ#" + td.Name) [e]
        let trCtor (h:C.Function) =
          let fnconst = "DH#" + h.Name
          let defconst = B.Decl.Const { Unique = true; Name = fnconst; Type = B.Type.Ref "$dt_tag" }
          let defax = B.Decl.Axiom (bCall "$def_datatype_option" [h.RetType |> toTypeId; er fnconst; bInt (h.Parameters |> List.length)]) 
          let args = h.Parameters |> List.mapi (fun n p -> ("p" + n.ToString(), p.Type))
          let ctorArgs = args |> List.map (fun (n, t) -> (n, trType t))
          let ctordef = B.Decl.Function (rt, [], "DF#" + h.Name, ctorArgs, None)
          let ctorCall = bCall ("DF#" + h.Name) (args |> List.map (fun (n, _) -> er n))

          let prjFuns = glist[]
          let eqs = glist[]
          let injPrjCalls = glist[]
          let subEqs = glist[]
          let sum = ref (bInt 0)
           
          let getProjection (n, t) =
            let name = "DP#" + n + "#" + h.Name 
            let fndef, constrained = mkSelector rt t name (er n)
            prjFuns.Add fndef
            eqs.Add (bEq (bCall name [ctorCall]) constrained)
            sum := bPlus !sum (abstractSize t constrained)
            injPrjCalls.Add (bCall name [er "a"])
            subEqs.Add (typedEq t (bCall name [er "a"]) (bCall name [er "b"]))
          List.iter getProjection args

          let eqSz = bEq (dtsz ctorCall) (plusOne !sum)
          eqs.Add eqSz

          let hdIs = bEq (hd ctorCall) (er fnconst)
          let prjAxiom = B.Decl.Axiom (B.Forall (Token.NoToken, ctorArgs, [[ctorCall]], [], bMultiAnd (hdIs :: Seq.toList eqs)))
          let injDisj = bEq (bCall ("DF#" + h.Name) (injPrjCalls |> Seq.toList)) (er "a")
          let eqDisj = bMultiAnd (bEq (hd (er "a")) (er fnconst) :: Seq.toList subEqs)
          [defconst; defax; ctordef; prjAxiom] @ (prjFuns |> Seq.toList), injDisj, eqDisj
        let eqAB = bCall ("DEQ#" + name) [er "a"; er "b"]
        let ctorDefs, injDisjs, eqArgs = td.DataTypeOptions |> List.map trCtor |> List.unzip3
        let tdef = [
          B.Decl.TypeDef (dataTypeName td)
          B.Decl.Function (B.Type.Bool, [], "DEQ#" + name, ["a",rt; "b",rt], None)
          B.Decl.Const { Unique = false; Name = "DZ#" + name; Type = rt }
          B.Decl.Function (B.Type.Ref "$dt_tag", [], "DGH#" + name, ["",rt], None)
          B.Decl.Function (B.Type.Int, [], "DSZ#" + name, ["",rt], None)

          B.Decl.Axiom (B.Forall (Token.NoToken, [("a", rt)], [[bCall ("DGH#" + name) [er "a"]]], [], bMultiOr injDisjs))
          B.Decl.Axiom (B.Forall (Token.NoToken, ["a",rt; "b",rt], [[eqAB]], [], bImpl (bEq (hd (er "a")) (hd (er "b"))) (bImpl (bMultiOr eqArgs) eqAB)))
          B.Decl.Axiom (B.Forall (Token.NoToken, ["a",rt; "b",rt], [[eqAB]], [],  bEq (eqAB) (bEq (er "a") (er "b"))))
          B.Decl.Axiom (B.Forall (Token.NoToken, ["a",rt], [[dtsz (er "a")]], [], B.Primitive ("<", [bInt 0; dtsz (er "a")])))
        ]
        tdef :: ctorDefs |> List.concat

      let trMathType (td:C.TypeDecl) =
        match td.Name with
          | "\\state"
          | "\\thread_id_t"
          | "tptr"
          | "\\type"
          | "\\objset" -> []
          | origname ->
            let name = "$#" + origname
            let t = B.Type.Ref name
            let typeDef = [B.Decl.TypeDef name]
            let (additions, kind) = 
              match td.Kind with
                | C.FunctDecl _ -> (typeDef, "fnptr")
                | C.Record -> (trRecord3 td, "record")
                | _ when td.IsDataType -> (trDataType td, "datatype")
                | _ -> (typeDef, "math")
            let def = "$def_" 
                        
            [B.Decl.Const { Unique = true
                            Name = "^" + name
                            Type = tpCtype };           
             B.Decl.Axiom (bCall (def + kind + "_type") [er ("^" + name)])
             ] @ additions

      let equalityInstantiation (h:C.Function) fappl parameters =
        if not h.IsStateless then
          let f0 = bSubst ["#s", er "#s0"] fappl
          let f1 = bSubst ["#s", er "#s1"] fappl
          match typedEq h.RetType f0 f1 with
            | B.Primitive ("==", _) -> []
            // we only do it for maps, others are usually automatically extensional; to be revisited
            | eq when h.RetType._IsMap ->
              // the exact body is not very relevant, it's only so that definition axiom for "eq" will get instantiated
              let body = bImpl eq (bEq f0 f1)
              let qargs = ["#s0", tpState; "#s1", tpState] @ parameters
              let trans = bCall "$trans_call_transition" [er "#s0"; er "#s1"]
              [B.Decl.Axiom (B.Forall (Token.NoToken, qargs, [[trans; f0; f1]], weight "eqprop", body))]
            | _ -> []
        else []

      let trPureFunction (h:C.Function) =
        if not (genPureFunctionDef h) then  []
        else
          let parameters =  List.map trTypeVar h.TypeParameters @ List.map trVar h.InParameters
          let qargs = (if h.IsStateless then [] else [("#s", tpState)]) @ parameters
          let fForPureContext (t, suffix) =
            let suffix = if suffix = "" then "" else "#" + suffix
            let fname = "F#" + h.Name + suffix
            let retType = trType t
            let fappl = bCall fname (List.map (fun ((vi,vt):B.Var) -> er vi) qargs)
            let fdecl = B.Decl.Function (retType, [], fname, qargs, None)
            (fappl, fdecl)
          let env = { initialEnv with Writes = h.Writes }
          let te e = trExpr env e
          // it is unsound to include these in the axiom
          let tens = function
            | C.Macro (_, ("in_range_phys_ptr"|"in_range_spec_ptr"), [_]) -> bTrue
            | e -> trExpr env e
          let ensures = bMultiAnd (List.map (stripFreeFromEnsures >> tens) h.Ensures)
          let requires = bMultiAnd (List.map (stripFreeFromRequires >> te) h.Requires)
          let range = h.InParameters |> List.fold (fun acc parm -> bAnd acc (trInRange parm.Type (er (ctx.VarName parm)))) bTrue
          let requires = bAnd range requires
          let fname = "F#" + h.Name
          let retType = trType h.RetType
          (*
          match h.Ensures with
            // note that it is in general unsafe to strip casts from "result", e.g. this:
            //   ispure bool bar() ensures(result == 7);
            // which generates (int)result == 7, might lead to inconsistency (because we assume result
            // of type bool to be 0 or 1)
            | [C.Prim (_, C.Op ("==", _), [C.Result (_); _])] -> ()
            | lst ->
              helper.Warning (h.Token, 0, "wrong " + String.concat "; " (lst |> List.map (fun e -> e.ToString())))
            *)  
          let (fappls, fdecls) = (h.RetType, "") :: List.map (fun (v:C.Variable) -> (v.Type, "OP#" + v.Name)) h.OutParameters |> List.map fForPureContext |> List.unzip
          
          // this is just saying f#limited#0 = f#limited#1 with the appropriate triggering
          let rec limitedFun decls prevName n =
            if n > h.DefExpansionLevel then decls
            else
              let (limappl, limdecl) = fForPureContext (h.RetType, "limited#" + n.ToString())
              let curName, fappl = 
                match limappl with
                  | B.FunctionCall (n, args) -> n, B.FunctionCall (prevName, args)
                  | _ -> die()
              let axBody = bEq fappl limappl
              let ax = B.Decl.Axiom (B.Expr.Forall(Token.NoToken, qargs, [[fappl]], weight "eqdef-userfun", axBody))
              limitedFun (ax :: limdecl :: decls) curName (n + 1)

          let fappl  = fappls.Head
          let subst = bSubst (("$s", er "#s") :: List.zip ("$result" :: List.map (fun (v:C.Variable) -> "OP#" + v.Name) h.OutParameters)  fappls )
          let defBody = subst (bImpl requires ensures)
          let defBody =
            if h.IsWellFounded then
              bImpl (B.Expr.Primitive ("<", [bInt h.DecreasesLevel; er "$decreases_level"])) defBody
            else defBody
          if h.IsStateless && bContains "#s" defBody then
            helper.Error (h.Token, 9650, "the specification refers to memory, but function is missing a reads clause", None)
          let defAxiom =
            if (defBody = bTrue) then [] 
            else if qargs = [] then [B.Decl.Axiom defBody]
            else [B.Decl.Axiom (B.Expr.Forall(Token.NoToken, qargs, List.map (fun x -> [x]) fappls, weight "eqdef-userfun", defBody))]
          let defAxiom = limitedFun defAxiom fname 1
          let defAxiom = defAxiom @ equalityInstantiation h fappl parameters
          let fnconst = "cf#" + h.Name
          let defconst = B.Decl.Const { Unique = true; Name = fnconst; Type = B.Type.Ref "$pure_function" }
          let frameAxiom =
            let containsGenerateFrameAxiom = CAST.hasCustomAttr C.AttrFrameaxiom h.CustomAttr
            if (not containsGenerateFrameAxiom) || h.IsStateless then 
              []
            else
              let readsRef (e:C.Expr) =
                match e.Type with
                  | C.Ptr t -> 
                    if not t.IsComposite then
                      (bTrue, te (C.Deref ({ e.Common with Type = t }, e)), trType t)
                    else
                      (bCall "$closed" [er "#s"; te e], bCall "$read_version" [er "#s"; te e], tpVersion)
                  | C.MathTypeRef "\\objset" ->
                    match e with 
                      | C.Macro(_, "_vcc_array_range", [_; ptr; length]) -> 
                        (bTrue, bCall "$mem_range" [er "#s"; te ptr; te length], B.Type.Int)
                      | _ -> helper.Error(e.Token, 9619, "ptrset in reads clause must be an array_range")
                             (bTrue, er "$bogus", tpVersion)
                  | _ ->
                    helper.Error (e.Token, 9619, "non-pointer reads clauses are not supported", None)
                    (bTrue, er "$bogus", tpVersion)
              let (conds, refs, types) = List.unzip3 (List.map readsRef h.Reads)
              let pTypes = List.map snd parameters
              let pRefs = List.map (fun ((vi,vt):B.Var) -> er vi) parameters
              let framename = fname + "#frame"
              let framedecl = B.Decl.Function (retType, [], framename, List.map (fun t -> ("", t)) (pTypes @ types), None)
              
              let pre = bMultiAnd (bCall "$full_stop" [er "#s"] :: bCall "$can_use_frame_axiom_of" [er fnconst] :: conds)
              let post = bEq fappl (bCall framename (pRefs @ refs))
              [framedecl; B.Decl.Axiom (B.Expr.Forall(Token.NoToken, qargs, [[fappl]], weight "frameaxiom", subst (bImpl pre post)))]
          let typeInfo =
            let arg i t = B.Decl.Axiom (bCall "$function_arg_type" [er fnconst; bInt i; toTypeId t])
            arg 0 h.RetType :: (h.Parameters |> List.mapi (fun i v -> arg (i + 1) v.Type))
          fdecls @ [defconst] @ defAxiom @ frameAxiom @ typeInfo

      let sanityChecks env (h:C.Function) =
        // we disable that by default for now, it seems to be too much of a hassle
        if not (CAST.hasCustomAttr "postcondition_sanity" h.CustomAttr) then []
        else
          let checks = List.map stripFreeFromEnsures h.Ensures
          match checks with
            | [] -> []
            | lst ->
              let var = "#postcondition_sanity"
              let repl = function
                | B.Expr.Ref "$s" -> Some (er "#sanityState")
                | B.Old _ as expr -> Some expr
                | _ -> None
              let subst (expr:B.Expr) = expr.Map repl
              let mkAssert (e:C.Expr) =
                match e with
                  | C.Macro (_, "reads_check_wf", [a]) -> 
                    match readsCheck env true a |> List.rev with
                      | B.Stmt.Assert (_, t, e) :: _ -> B.Stmt.MkAssert (t, e |> subst)
                      | _ -> die()
                  | _ -> B.Stmt.MkAssert (e.Token, trExpr env e |> subst)
              let assumes = h.Ensures |> List.map (stripFreeFromEnsures>> trExpr env >> subst >> B.Stmt.MkAssume)
              let state = B.Stmt.MkAssume (stateChanges env |> subst)
              let goodstuff = B.Stmt.MkAssume (bCall "$full_stop" [bState] |> subst)
              [B.Stmt.VarDecl ((var, B.Type.Bool), None);
               B.Stmt.VarDecl (("#sanityState", tpState), None);
               B.Stmt.If (C.bogusToken, er var, B.Stmt.Block (assumes @ state :: goodstuff :: List.map mkAssert lst), B.Stmt.Block []);
               B.Stmt.MkAssume (bNot (er var))]
        
      let hasStartHere (stmt:B.Stmt) =
        let found = ref false
        let repl = function
          | B.Stmt.Assume (_, (B.FunctionCall ("$start_here", []) as call)) ->
            found := true
            Some (B.Stmt.Assume ([B.ExprAttr ("start_checking_here", bTrue)], call))
          | _ -> None
        let newBody = B.mapStmt repl stmt
        if !found then Some newBody
        else None        
      
      let trTop decl =
        try 
          match decl with
            | C.Top.FunctionDecl h when h.IsDatatypeOption -> []
            | C.Top.FunctionDecl h when h.Name.StartsWith "_vcc_" && not (h.Name.StartsWith "_vcc_match") -> []
            | C.Top.FunctionDecl h ->
                ctx.NewFunction()
                let (proc, env) = trHeader h
                let (init, env) = setWritesTime h.Token env h.Writes
                let hasIF = IF.scanForIFAnnotations decl
                let env = {env with hasIF = hasIF}
                if hasIF then globalHasIF := true
                let assumeMutability e =
                  let te = trExpr env
                  let e' = te e 
                  let assump =
                    match e.Type with
                      | C.Ptr t ->                      
                        bCall (if t.IsComposite then "$thread_owned" else "$mutable") [bState; e']
                      | C.ObjectT ->
                        bCall "$thread_owned_or_even_mutable" [bState; e']
                      | C.MathTypeRef "\\objset" ->
                        let mut extOf name =
                          let p = er "#p"
                          let triggers =
                            match extOf with
                              | Some q ->
                                [[bCall "$extent_hint" [p; q]]]
                              | _ ->
                                List.map (fun n -> [bCall n [bState; p]]) ["$st"; "$ts"]
                          B.Expr.Forall (Token.NoToken, [("#p", tpPtr)], triggers,
                                         weight "begin-writes2",
                                         bInvImpl (bCall "$set_in" [p; e']) (bCall name [bState; p]))

                        match e' with
                          | B.Expr.FunctionCall (("$set_universe" | "$set_empty"), []) ->
                            // writes(set_universe()) is for debugging, so disable the immediate false that we could conclude
                            // writes(set_empty()) doesn't mean anything, so also ignore it
                            bTrue
                          | B.Expr.FunctionCall (("$struct_extent" | "$extent" | "$full_extent"), args) ->
                            let args = if args.Length = 1 then bState :: args else args
                            bCall "$extent_mutable" args
                          | B.Expr.FunctionCall ("$span", [o]) ->
                            bCall "$mutable" [bState; o]
                          | B.Expr.FunctionCall ("$array_range", args) ->
                            bCall "$initially_mutable_array" args
                          | B.Expr.FunctionCall (("$struct_extent" | "$extent" | "$full_extent" | "$span"), args) ->
                            bCall "$initially_mutable" [bState; e']
                          | _ -> 
                            bCall "$initially_thread_owned_or_mutable" [bState; e']
                      | _ -> bTrue
                  B.Stmt.MkAssume assump
                  
                let inParams = h.Parameters |> List.filter (fun v -> v.Kind <> C.VarKind.OutParameter)
                let inParamLabels = if env.hasIF then List.collect (fun (v:CAST.Variable) -> [B.Stmt.VarDecl (("FlowData#P#"+(v.Name),B.Type.Ref "$flowdata"), None)]) inParams
                                                 else []
                let init = inParamLabels @ init                    
                
                let can_frame =
                  if List.exists (function C.ReadsCheck _ -> true | _ -> false) h.CustomAttr then []
                  else
                    [B.Stmt.MkAssume (bCall "$can_use_all_frame_axioms" [bState])]
                
                let doBody (s:CAST.Expr) =
                  let secDecls =
                    if (env.hasIF) then [B.Stmt.VarDecl(("FlowData#initPC", B.Type.Ref "$flowdata"), None)
                                         IF.setLLabel "FlowData#initPC" (B.Expr.Ref "$lblset.bot")
                                         IF.setPC (s.Token) (IF.getLabel (IF.getLData "FlowData#initPC"))
                                         assumeSync env s.Token]
                                   else []
                  B.Stmt.Block (B.Stmt.MkAssume (bCall "$function_entry" [bState]) ::
                                B.Stmt.VarDecl(("#stackframe", B.Type.Int), None) ::
                                secDecls @
                                (assumeSyncCS "function entry" env h.Token ::
                                 can_frame @
                                 init @
                                 List.map assumeMutability h.Writes @
                                 trStmt {env with IFContexts = (getLocalLabels s,"FlowData#initPC")::(env.IFContexts)} s @ 
                                 [B.Stmt.Label (Token.NoToken, "#exit")] @
                                 sanityChecks env h))
                let theBody =
                  if functionToVerify = null || functionToVerify = h.Name then h.Body
                  else None
                let replPossiblyUnreachable = function
                  | B.Stmt.Assert ([], t, (B.FunctionCall ("$possibly_unreachable", []) as call)) ->
                    Some (B.Stmt.Assert ([B.ExprAttr ("PossiblyUnreachable", bTrue)], t, bTrue))
                  | _ -> None
                let proc = { proc with Body = Option.map doBody theBody }
                let proc = { proc with Body = Option.map (B.mapStmt replPossiblyUnreachable) proc.Body }
                let proc =
                  match proc.Body with
                    | Some b ->
                      match hasStartHere b with
                        | Some newBody ->
                          { proc with Body = Some newBody; Attributes = B.Attribute.ExprAttr ("selective_checking", bTrue) :: proc.Attributes }
                        | None -> proc
                    | _ -> proc
                trPureFunction h @ [B.Decl.Proc proc]

            | C.Top.TypeDecl td ->
              match td.Kind with
                | C.TypeKind.Union
                | C.TypeKind.Struct -> trCompositeType td
                | C.TypeKind.Record
                | C.TypeKind.FunctDecl _
                | C.TypeKind.MathType -> trMathType td

            | C.Top.GeneratedAxiom(e, _)
            | C.Top.Axiom e ->

              let seenState = ref false
              let replMS = function
                | B.Expr.Ref "$s" -> seenState := true; Some (er "#s")
                | B.Expr.Old _ ->
                  failwith "axiom mentions old"
                | _ -> None
              let res = trExpr initialEnv e
              let res = res.Map replMS

              let e =
                if not !seenState then e
                else
                  let stateVar = C.Variable.CreateUnique "__vcc_state" C.Type.MathState C.VarKind.QuantBound
                  let stateRef = C.Expr.Ref ({ C.bogusEC with Type = stateVar.Type }, stateVar)
                  let inState (e:C.Expr) =
                    let ec = { e.Common with Token = WarningSuppressingToken (e.Token, 9106) }
                    C.Old (ec, stateRef, e)
                  let goodState = C.Expr.Macro (C.boolBogusEC(), "prelude_good_state", [stateRef])
                  match e with
                    | C.Quant (ec, ({ Kind = C.Forall } as qd)) ->
                      let qd =
                        { qd with 
                            Variables = stateVar :: qd.Variables
                            Body = inState qd.Body
                            Condition =
                              match qd.Condition with
                                | Some c -> Some (CAST.mkAnd goodState (inState c))
                                | None -> Some goodState
                            Triggers = List.map (List.map inState) qd.Triggers }
                      C.Quant (ec, qd)
                    | _ ->
                      let qd = 
                          {
                            Kind = C.QuantKind.Forall
                            Variables = [stateVar]
                            Triggers = []
                            Condition = Some goodState
                            Body = inState e
                            Weight = null
                          } : C.QuantData
                      C.Expr.Quant (e.Common, qd)
              // run trExpr again, so it will infer triggers 
              [B.Decl.Axiom (trExpr initialEnv e)]

            | C.Top.Global ({ Kind = C.ConstGlobal ; Type = C.Ptr t } as v, _) ->
              [bDeclUnique tpPtr (ctx.VarName v);
                B.Decl.Axiom (bCall "$def_global" [varRef v; toTypeId t])]

            | C.Top.Global _ -> die()
          with
            | Failure _ ->
              helper.Error(decl.Token, 9600, "OOPS for declaration " + decl.ToString())
              reraise()

      let archSpecific() = 
        let ptrSizeInBytes = !C.PointerSizeInBytes
        //let archComment = B.Comment ("Configuration for sizeof(void *) == " + ptrSizeInBytes.ToString())
        let sizeOfPtrAxiom = B.Axiom(bEq (er "$arch_ptr_size") (bInt ptrSizeInBytes))
        let startOfSpecPtrRange = B.Axiom(bEq (er "$arch_spec_ptr_start") (er ("$max.u" + (ptrSizeInBytes.ToString()))))
        [[sizeOfPtrAxiom; startOfSpecPtrRange]]

      let main () =
        let res = List.map trTop decls
        
        let types = List.fold (fun acc -> function
                                     | C.Top.TypeDecl ({ Kind = (C.Union|C.Struct)} as td) -> td :: acc
                                     | _ -> acc) [] decls
        let tn = if nestingExtents then typeNesting types else []

        List.concat (archSpecific() @ res @ [tn; ctx.FlushDecls mapEqAxioms])
        
      main()
