//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
 open Microsoft.FSharp.Math
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.CAST
 
 module Simplifier =
    
  let inRangeBvExtract (expr:Expr) numOfBits =
    let ec = expr.Common
    let (lower, upper) =
      let mkBigInt (n:int32) = new bigint(n)
      let two = mkBigInt 2
      let sub bi1 bi2 = bi1 - bi2
      if ec.Type.IsSignedInteger then
        let x = bigint.Pow(two, numOfBits - 1)
        (sub zero x, sub x one)
      else
        (zero, sub (bigint.Pow(two, numOfBits)) one)
    let mkCheck args = Expr.Prim({ec with Type = Type.Bool }, Op("<=", Processed), args )
    let lowerCheck = mkCheck [IntLiteral(ec, lower); expr]
    let upperCheck = mkCheck [expr; IntLiteral(ec, upper)]
    let assertEc = {(afmte 8503 (lower.ToString() + " <= {0} && {0} <= " + upper.ToString() + " in bitfield assignment") [expr]) with Type = Type.Bool; }
    Expr.Prim(assertEc, Op("&&", Processed), [lowerCheck; upperCheck])

  let init (helper:TransHelper.TransEnv) =
  
    // ============================================================================================================
    
    let classifierValidityChecks decls =
      let rec addCheck self = function
        | If(ec, None, (Macro(_, "_vcc_test_classifier", [Quant(ec', ({Kind = Lambda} as qd)); cond]) as c), iB, tB) as e ->
          let cond,body =
            match qd.Body with
              | Macro(_, "in_lambda", [c;b]) -> c,b
              | _ -> die()
          let iB' = iB.SelfMap(addCheck)
          let tB' = tB.SelfMap(addCheck)
          Some(Macro(ec, "fake_block", [Macro({ec' with Type = Void}, "test_classifier_validity_check", [Quant({ec' with Type = Bool}, {qd with Kind = Forall; Condition = Some cond; Body = body})]); If(ec, None, c, iB', tB')]))
        | _ -> None
      let doFunction = function
        | FunctionDecl ({Body = Some b} as fn) ->
          fn.Body <- Some(b.SelfMap(addCheck))
          FunctionDecl fn
        | _ as d -> d
      List.map (doFunction) decls
    
    let desugarLambdas decls =
      let defs = ref []
      
      // n-ary lambdas are represented as nested quantifiers. We need to make sure that we place an in_lambda for every quantifier
      // also, we need to adjust the types. Originally, all nested quantifiers have the same type, which is the type of the
      // entire lambda. We need to shave of map-type for map-type as we walk down the nested quantifiers
      // for this, we pass in the extra optional type argument. Initially, the argument in None, which corresponds to the
      // fact that we have found the outermost quantifier
      let rec addNestedInLambdas mapType self = function
        | Quant (_, ({ Kind = Lambda; Condition = None; Body = Cast({Type = Type.Bool}, _, Quant(qc, ({Kind = Lambda})))})) as outer when Option.isNone mapType ->
          Some(outer.SelfMap(addNestedInLambdas (Some(qc.Type))))
        | Quant (c, ({ Kind = Lambda; Condition = None; Body = Cast(({Type = Type.Bool} as bc), _, Quant(qc, ({Kind = Lambda} as nestedQData)))} as q)) -> 
          let nestedType = match mapType with | Some(Type.Map(_, t)) -> t | _ -> die()
          let nestedQ = Quant({qc with Type = nestedType }, nestedQData)
          let nestedQ = nestedQ.SelfMap(addNestedInLambdas (Some(nestedType)))
          Some ((Quant (c, { q with Body = Macro(bc, "in_lambda", [Expr.True; nestedQ]) })))
        | _ -> None

      let expand self = function
        | Quant (c, ({ Kind = Lambda; Condition = None; Body = Macro (_, "in_lambda", [cond; expr]) } as q)) ->
          Some (self (Quant (c, { q with Condition = Some cond; Body = (self expr) })))
          
        | Quant (c, ({ Kind = Lambda } as q)) ->
          let (domain, range) =
            match c.Type with
              | Type.Map (d, r) -> (d, r)
              | _ -> helper.Die()
         
          
          let rec hasQVar vars expr =
            let hasIt = ref false
            let check self = function
              | Expr.Ref (_, v) when _list_mem v vars ->
                hasIt := true
                false
              | _ -> true
            (expr:Expr).SelfVisit check
            !hasIt
            
          let parms = ref []
          
          let repl = 
          
            let rec repl' vars prestate self = 
              let turnExpressionIntoParameter (expr : Expr) = 
                let pname = "#l" + (List.length !parms).ToString()
                let var = Variable.CreateUnique pname expr.Type QuantBound
                let expr = 
                  match prestate with
                    | None -> expr
                    | Some prestate -> Old(expr.Common, prestate, expr)
                parms := (expr, var) :: !parms
                Some (Expr.Ref (expr.Common, var))

              function
                | Old(ec, prestate, expr) -> Some(expr.SelfMap (repl' vars (Some(prestate))))
                | Quant(ec, qd) as quant when hasQVar vars quant ->
                  let self = fun (e : Expr) -> e.SelfMap(repl' (qd.Variables @ vars) prestate)
                  Some(Quant(ec, {qd with Body = self qd.Body}))
                | Macro(ec, "vs_updated", [Dot(dc, e1, f); e2]) when hasQVar vars e1 || hasQVar vars e2 ->
                  let e1' = self e1
                  let e2' = self e2
                  Some(Macro(ec, "vs_updated", [Dot(dc, e1', f); e2']))
                  // special handling because the field and assignment are split into two separate arguments but must be handled
                  // together
                | expr when hasQVar vars expr -> None
                | IntLiteral _
                | BoolLiteral _
                | Macro (_, "null", [])
                | CallMacro(_, "_vcc_typeof", _, _)
                | CallMacro(_, "vs_zero", _, [])
                | Cast (_, _, Macro (_, "null", [])) -> None
                | expr -> turnExpressionIntoParameter expr
            repl' q.Variables None
          
          let cond = 
            match q.Condition with
              | Some c -> c.SelfMap repl
              | None -> Expr.True
          let body = q.Body.SelfMap repl
          
          let fn =
            { Function.Empty() with
                Token           = c.Token
                IsSpec          = true
                RetType         = c.Type
                Name            = "lambda#" + (helper.UniqueId()).ToString()
                Parameters      = [for (_, var) in !parms -> { var with Kind = Parameter }]
                Reads           = computeReads body
                CustomAttr      = [VccAttr (AttrIsPure, "")]
                IsProcessed     = true
              }
                
          let axcall = Call ({ bogusEC with Type = fn.RetType }, fn, [], List.map (snd >> mkRef) !parms)
          let idxvar = match q.Variables with [x] -> x | _ -> die()
          let mkIdx mgf = Macro ({ bogusEC with Type = range }, mgf, [axcall; mkRef idxvar])
          let idx = mkIdx "map_get"
          let trigIdx = mkIdx "map_get_trig"
          let axiom = Quant ({ c with Type = Bool }, 
                             { Kind = Forall
                               Variables = idxvar :: List.map snd !parms
                               Triggers = [[trigIdx]]
                               Condition = Some cond
                               Body = Prim ({ c with Type = Bool }, Op ("==", Processed), [idx; body])
                               Weight = "c-lambda-def"
                             })
          
          defs := Top.FunctionDecl fn :: Top.GeneratedAxiom(axiom, Top.FunctionDecl(fn)) :: !defs
          Some (Call (c, fn, [], List.map (fst >> self) !parms))
          
        | _ -> None   
                   
      let decls = decls |> classifierValidityChecks |> deepMapExpressions (addNestedInLambdas None) |> deepMapExpressions expand 
      decls @ !defs    
    
    // ============================================================================================================
    
    /// Get rid of &&, || -- operators that alter control flow.
    /// Actually FELT translates them all to "ite" (IConditional) nodes.
    let removeLazyOps = 

      let splitKnown = function
        | Expr.Macro(_, "_vcc_known'", expr :: stmts) -> expr, stmts
        | Expr.Cast(c, cs, Expr.Macro(_, "_vcc_known'", expr :: stmts)) -> expr, stmts
        | expr -> expr, []

      let rec doRemoveLazyOps inSpecBlock keepKnown ctx self = 
        let selfs = List.map self
        function
        | Macro (c, "ite", [cond; th; el]) when not ctx.IsPure ->
          let varKind =
            match exprDependsOnSpecExpr th, exprDependsOnSpecExpr el with
              | None, None when not inSpecBlock  -> VarKind.Local
              | _,_ -> VarKind.SpecLocal
        
          let c' = { c with Type = Void }
          let tmp = getTmp helper "ite" c.Type varKind
          let tmpRef = Expr.Ref (c, tmp)
          let thAssign = Macro (c', "=", [tmpRef; th])
          let elAssign = Macro (c', "=", [tmpRef; el])          
          let write = Expr.If (c', None, cond, Expr.MkBlock([CAST.possiblyUnreachable; thAssign]), Expr.MkBlock([CAST.possiblyUnreachable; elAssign]))
          addStmtsOpt [VarDecl (c', tmp, []); self write] tmpRef
        | If(c, cl, cond, th, el) ->
          match splitKnown cond with
            | (Cast(_, _, BoolLiteral(_, true))  | BoolLiteral(_, true)),  asserts -> Some(Expr.MkBlock(asserts @  [self th]))
            | (Cast(_, _, BoolLiteral(_, false)) | BoolLiteral(_, false)), asserts -> Some(Expr.MkBlock(asserts @  [self el]))
            | _ -> None     
        | Macro (wtok, "doUntil", [Macro (lc, "loop_contract", conds); body; cond]) ->
          // special treatment for the condition of doUntil so that we re-visit the 'known' annotation once we have desugared the loop 
          Some(Macro(wtok, "doUntil", [Macro(lc, "loop_contract", selfs conds); self body; cond.SelfCtxMap(false, doRemoveLazyOps false true)]))
        | Macro(ec, "spec", args) -> Some(Macro(ec, "spec", List.map (fun (e:Expr) -> e.SelfCtxMap(ctx.IsPure, doRemoveLazyOps true false)) args))
        | _ -> None
    
      let propagateKnownValue ctx self = 
        let assertEq cond expectedValue = Expr.MkAssert (Expr.Prim (afmte 8533 "{0} has the value {1} specified by _(known ...)" [cond; expectedValue], Op("==", CheckedStatus.Unchecked), [cond; expectedValue]))
        function
        | Expr.Macro(c, "_vcc_known", [expr; knownValue]) when not ctx.IsPure ->
          let e, ea = splitKnown (self expr)
          let k, ka = splitKnown (self knownValue)
          let tmp = getTmp helper "known" expr.Type VarKind.Local
          let tmpRef = Expr.Ref(expr.Common, tmp)
          let tmpDecl = VarDecl({expr.Common with Type = Type.Void}, tmp, [])
          let tmpAssign = Macro({expr.Common with Type = Type.Void}, "=", [tmpRef; e])
          let e' = if e.Type = Type.Bool then tmpRef else Expr.Cast({e.Common with Type = Type.Bool}, CheckedStatus.Unchecked, tmpRef)
          let k' = if k.Type = c.Type then k else Expr.Cast(c, CheckedStatus.Unchecked, k)
          Some(Expr.Macro(c, "_vcc_known'", k' :: tmpDecl :: tmpAssign :: assertEq e' k :: (ea @ ka)))
        | Expr.Prim(c, (Op("!", _) as op), [arg]) when not ctx.IsPure ->
          let arg' = self arg
          match splitKnown arg' with
            | (Cast(_, _, BoolLiteral(ec, b)) | BoolLiteral(ec, b)), stmts -> Some(Expr.Macro(c, "_vcc_known'", BoolLiteral(ec, not b) :: stmts))
            | _ -> Some(Expr.Prim(c, op, [arg']))
        | Expr.Macro(c, "ite", [cond; th; el]) when not ctx.IsPure ->
          let cond' = self cond
          let pick e stmts =
            let e', eStmts = splitKnown (self e)
            Some(Expr.Macro(c, "_vcc_known'", Expr.Cast(c, CheckedStatus.Unchecked, e') :: (stmts @ eStmts)))
          match splitKnown cond' with
            | (Cast(_,_, BoolLiteral(_, b)) | BoolLiteral(_, b)), stmts -> if b then pick th stmts else pick el stmts
            | _ -> Some(Expr.Macro(c, "ite", [cond'; self th; self el]))
        | _ -> None
                  
      let eliminateKnown self = function
        | Expr.Macro(c, "_vcc_known'", e :: stmts) -> Some(self (Expr.MkBlock (stmts @ [e])))
        | _ -> None

      deepMapExpressionsCtx propagateKnownValue >> 
      deepMapExpressionsCtx (doRemoveLazyOps false false) >> 
      deepMapExpressions eliminateKnown 
    
    // ============================================================================================================

    /// Rename locals if their names clashes with parameters or locals from other scopes   
    let doRemoveNestedLocals (f:Function)=
      let subst = new Dict<Variable, Variable>()
      let seenNames = new HashSet<string>()    
      let addVarToSeen (v : Variable) = seenNames.Add (v.Name)

      let renameVar (v : Variable) =
        if addVarToSeen v
          then v
          else
            let renamedVar = { v.UniqueCopy() with Name = v.Name + "#" + subst.Count.ToString()}
            if v.Kind <> Local && v.Kind <> SpecLocal then die()
            subst.[v] <- renamedVar
            renamedVar

      let rnExpr self = function
        | Expr.VarDecl (ce, var, attr) -> Some(Expr.VarDecl (ce, renameVar var, attr))
        | Expr.Ref(ce, var) ->
          match subst.TryGetValue(var) with
            | true, substName -> Some(Expr.Ref(ce, substName)) 
            | false, _ -> None
        | VarWrite _ -> die()
        | _ -> None
        
      f.Body <- Option.map (fun (body : Expr) -> body.SelfMap(rnExpr)) f.Body
      f
       
    let removeNestedLocals = mapFunctions doRemoveNestedLocals    
    
    // ============================================================================================================
    
    let singleFieldStruct tok tp_name field_name isSpec (t:Type) =
      let td =
          { Token = tok
            Name = tp_name
            Fields = []
            Invariants = []
            CustomAttr = []
            SizeOf = t.SizeOf
            Kind = Struct
            IsNestedAnon = false
            GenerateEquality = NoEq
            Parent = None
            IsVolatile = false 
            IsSpec = isSpec
            DataTypeOptions = []
            UniqueId = CAST.unique() }
      let (t, vol) = match t with | Volatile(t) -> (t, true) | t -> (t, false)
      let singleField =
        { Name = field_name
          Token = tok
          Type = t
          Parent = td
          IsSpec = false
          Offset = Normal 0
          IsVolatile = vol
          CustomAttr = []
          UniqueId = CAST.unique() }
      td.Fields <- [singleField]
      (td, singleField)
          
    (*
       Turn a global:
       
         int x;
         
       into:
       
         struct {
           int data;
         } x;
         
       and then all "x" into "x.data". This allows to own globals (with emb(&x) at the C level).
     *)
    let wrapPrimitiveGlobals decls =
      // TODO: Ptr kind - deal also with spec globals, where all ptrs are spec ptrs
      let globalSubst = new Dict<_,_>()
      let varSubst = new Dict<_,_>()
      let rec isPrimitive = function
        | Type.Volatile(t) -> isPrimitive(t)
        | t -> not t.IsComposite
      let handle = function
        | Top.Global (v, init) when isPrimitive v.Type ->
          let isSpec = v.Kind = VarKind.SpecGlobal
          let (td, fld) = singleFieldStruct bogusToken ("swrap#" + v.Name) "data"  isSpec v.Type 
          let approvesInv =
            match v.Type with 
              | Type.Volatile _ -> 
                let ecObjT = { bogusEC with Type = Type.ObjectT }
                let this = This( { bogusEC with Type = Type.MkPtrToStruct td })
                [Macro (boolBogusEC(), "approves", 
                  [ Macro( ecObjT, "_vcc_owner", [ this ]); 
                    Deref ({bogusEC with Type = v.Type}, 
                           Expr.MkDot (this, fld))])]
              | _ -> []
          td.Invariants <- approvesInv
          let v' = Variable.CreateUnique ("wrap#" + v.Name) (Type.Ref td) v.Kind
          let repl ec =
            let inner = Macro ({ ec with Type = Type.MkPtrToStruct(td) }, "&", [Expr.Ref ({ ec with Type = Type.Ref td }, v')])
            match v.Type with
              | Array (t, _) ->
                Deref ({ ec with Type = t }, Dot ({ ec with Type = Type.MkPtr(t, isSpec)}, inner, fld))
              | _ ->
                Deref (ec, Dot ({ ec with Type = Type.MkPtr(ec.Type, isSpec) }, inner, fld))
          globalSubst.Add (v, repl)
          varSubst.Add(v, v')
          [Top.TypeDecl td; Top.Global (v', init)]
        | d -> [d]
        
      let repl self = function
        | Expr.Ref (ec, v) ->
          match globalSubst.TryGetValue v with
            | true, f -> Some (f ec)
            | _ -> None
        | _ -> None
        
      let replaceVarsInGeneratedAxioms = function
        | Top.GeneratedAxiom(ax, Top.Global(v, _)) as ga ->
          match varSubst.TryGetValue(v) with
            | true, v' -> Top.GeneratedAxiom(ax, Top.Global(v', None))
            | _ -> ga
        | t -> t
  
      decls |> List.map handle |> List.concat |> List.map replaceVarsInGeneratedAxioms |> deepMapExpressions repl 
    
    // ============================================================================================================

    let cleanupAddrDeref =
      let cleanupAddDeref' self = function
        | Macro (ec, "&", [expr]) -> 
          match self expr with 
            | Deref (_, e) -> Some (e)
            | expr' -> Some(Macro(ec, "&", [expr']))
        | Cast (ec, _, e) when ec.Type = e.Type -> Some (self e)
        | _ -> None
      deepMapExpressions cleanupAddDeref'

    
    let expandByClaim =
      let pushOldIn self = function
        | Deref (_, Macro (_, "&", [e])) -> Some (self e)
        | Old (ec, state, expr) ->
          match self expr with
            | Macro (_, ("bv_extract_signed" | "bv_extract_unsigned" as name), [e; i; j; k]) ->
              Some (Macro (ec, name, [self (Old (ec, state, e)); i; j; k]))
            | _ -> None
        | _ -> None    
            
      let doByClaim self = function
        | Expr.Old (ec, CallMacro (_, "_vcc_by_claim", _, [c]), e) ->
          match e with
            | Expr.Deref (_, (Dot (_, obj, f) as ptr))
            | Expr.Deref (_, (Index (_, Dot (_, obj, f), _) as ptr)) ->
              if f.IsVolatile then
                helper.Error (ec.Token, 9629, "by_claim(...) can only refer to a non-volatile field", Some(f.Token))
              Some (Expr.Macro (ec, "by_claim", [self c; self obj; self ptr]))
            | Expr.Deref (ec', (Index (_, obj, _) as ptr)) ->
              if not ec'.Type._IsInteger && not ec'.Type._IsPtr then
                helper.Error (ec.Token, 9629, "by_claim(...) can only refer to arrays of primitive types")
              Some (Expr.Macro (ec, "by_claim", [self c; self obj; self ptr]))
            | _ ->
              helper.Error (ec.Token, 9628, "by_claim(...) expects field or embedded array reference as a second parameter", None)
              None            
        | _ -> None
      deepMapExpressions pushOldIn >> deepMapExpressions doByClaim
    
    
    // ============================================================================================================
    
    let handleApprovers decls =
      let generated = gdict()
      let res expr =
        generated.[expr] <- true
        Some expr
      let approvers = gdict()
      let selfApproved = gdict()
      let (|AnyField|_|) = function
        | Deref (_, Dot (_, (This _ as th), subject)) -> Some (th, mkFieldRef subject, Some subject)
        | CallMacro (ec, "_vcc_owns", _, [th]) -> 
          let fld = Macro ({ bogusEC with Type = Type.FieldT }, "owns_field", [th])
          Some (th, fld, None)
        | _ -> None
      let doApproves self = function
        | Macro (ec, "approves", [approver; AnyField (th, subject, subjOpt)]) ->
          match approver with
            | CallMacro (_, "_vcc_owner", _, [This(_)]) ->
              res (Macro (ec, "_vcc_inv_is_owner_approved", [th; subject]))
            | Deref (_, Dot (_, This(_), approver)) ->
              if Some approver = subjOpt then
                selfApproved.[approver] <- true
              approvers.[approver] <- ec.Token
              res (Macro (ec, "_vcc_inv_is_approved_by", [th; mkFieldRef approver; subject]))
            | expr ->
              helper.Error (ec.Token, 9670, "approves(...) needs owner(this) or this->field as the first parameter", None)
              None
        | Macro (ec, "approves", _) as expr ->
          helper.Error (ec.Token, 9669, "approves(...) needs this->field as the second parameter", None)
          None
        | expr ->
          None
    
      let checkForAxiom axioms = function
        | Macro (ec, "_vcc_inv_is_owner_approved", [th; subject]) as expr ->
          generated.Remove expr |> ignore
          Macro (ec, "_vcc_is_owner_approved", [typeExpr th.Type.Deref; subject]) :: axioms
        | Macro (ec, "_vcc_inv_is_approved_by", [th; approver; subject]) as expr ->
          generated.Remove expr |> ignore
          Macro (ec, "_vcc_is_approved_by", [typeExpr th.Type.Deref; approver; subject]) :: axioms
        | _ -> axioms
        
      let doDecl = function
        | Top.TypeDecl (td) as d ->
          generated.Clear()
          approvers.Clear()
          selfApproved.Clear()
          td.Invariants <- td.Invariants |> List.map (fun e -> e.SelfMap doApproves)
          let axioms = 
            List.map splitConjunction td.Invariants |> 
              List.concat |> 
              List.fold checkForAxiom [] |>
              List.map Top.Axiom
          for e in generated.Keys do
            helper.Error (e.Token, 9671, "approves(...) can only be used as a top-level invariant")
          for f in approvers.Keys do
            match f.Type with
              | ObjectT -> ()
              | _ ->
                helper.Error (approvers.[f], 9673, "approver field '" + f.Name + "' should have \\object type, it has '" + f.Type.ToString() + "'")
            if not (selfApproved.ContainsKey f) && f.IsVolatile then
              helper.Error (approvers.[f], 9672, "volatile field '" + f.Name + "' is an approver, but not a self-approver")
          d :: axioms
        | d -> [d]
        
      List.map doDecl decls |> List.concat
        
    // ============================================================================================================    
    
    /// Remove operators like +=, -=, pre++ ...
    /// Also handle assignments to bitfields (as they also require precomputation).
      (* Require precomputation for example:
           ... *(f()) += 3 ...
         should go into:
           tmp = f();
           ... *tmp = *tmp + 3 ... 
         
         TODO: FELT does the desugaring itself, but does it wrongly. Investigate.
       *)        

    let cacheAssignTarget self = function
      | Expr.Deref (_, Dot(_, _, f)) as e when f.Parent.IsRecord -> (self, e)

      | Expr.Deref (c, ptr) ->
        let cacheVarKind =
          match exprDependsOnSpecExpr ptr with
            | Some _ -> VarKind.SpecLocal
            | None -> VarKind.Local
        let (inits, tmp) = cache helper "assignOp" ptr cacheVarKind
        let addInits e = Expr.MkBlock (List.map self (inits @ [e]))
        addInits, Expr.Deref (c, tmp)
      | _ as e -> (self, e)


    let removeAssignOps self = function
    
        | Expr.Macro (c, "map_set", [map; idx; value]) ->
          let (inits, map) = cacheAssignTarget self map
          Some (inits (Expr.Macro (c, "=", [map; Expr.Macro (map.Common, "map_updated", [map; idx; value])])))
        | Expr.Macro (c, "=", [Expr.Macro(c1, "map_get", [map; idx]); expr]) ->
          Some(self(Expr.Macro(c, "map_set", [map; idx; expr])))
        // here we assume that bit extraction is always padded; when we write, we just ignore the padding
        | Expr.Macro (c, "=", [ Expr.Macro (c', ("bv_extract_signed" | "bv_extract_unsigned"), 
                                            [e1; 
                                             Expr.IntLiteral (_, total);
                                             Expr.IntLiteral (_, beg); 
                                             Expr.IntLiteral (_, end_)]); e2]) ->
                                             
          let beg = int32 beg
          let end_ = int32 end_
          let total = int32 total          
          let rec stripUnchecked = function
            | Expr.Macro(_, name, [e]) when name.StartsWith("unchecked_") -> stripUnchecked e
            | e -> e
          let (inits1, bv1) = cacheAssignTarget self (self (stripUnchecked e1)) // the unchecked ops were only meaningful for reading
          let (inits2, e2) = cache helper "assignSrc" (self e2) (VarKind.Local)
          let concat = Macro ({c' with Type = c'.Type.Deref}, "bv_update", [bv1; mkInt total; mkInt beg; mkInt end_; e2])
          let rangeAssertForRhs = Expr.MkAssert(inRangeBvExtract (ignoreEffects e2) (end_ - beg) )
          Some (inits1 (Expr.MkBlock (inits2 @ [rangeAssertForRhs; Expr.Macro (c, "=", [bv1; concat])])))
          
        | Expr.Macro (c, "=", [ Expr.Macro (_, ("_vcc_ptr_to_i4" | "_vcc_ptr_to_i8" | "_vcc_ptr_to_u4" | "_vcc_ptr_to_u8"), [e1]); e2 ]) -> 
          let (inits, target) = cacheAssignTarget self (self e1)
          Some (inits (Expr.Macro(c, "=", [target; Expr.Macro({c with Type = e1.Type}, intToPtrFunction e2.Type, [e2])])))
        | Expr.Macro (c, "=", [ Expr.Macro (_, ("_vcc_i4_to_ptr" | "_vcc_i8_to_ptr" | "_vcc_u4_to_ptr" | "_vcc_u8_to_ptr"), [e1]); e2 ]) -> 
          let (inits, target) = cacheAssignTarget self (self e1)
          Some (inits (Expr.Macro(c, "=", [target; Expr.Macro({c with Type = e1.Type}, ptrToIntFunction e1.Type, [e2])])))
        | Expr.Macro (c, "=", [ Expr.Macro (_, name, [e1]); e2 ]) when name.StartsWith("unchecked_") ->
          let (inits, target) = cacheAssignTarget self (self e1)
          Some (inits (Expr.Macro(c, "=", [target; uncheckedSignConversion e2]))) 
        | Expr.Macro (c, "=", [ Expr.Cast(_,_, e1); e2]) ->
          Some(self(Expr.Macro(c, "=", [e1; e2])))
        // fix type of remaining occurrences of the transformer functions         
        | Expr.Macro(c, name, args) when name.StartsWith("bv_extract_") && c.Type._IsPtr -> 
          Some(Expr.Macro({c with Type = c.Type.Deref}, name, List.map self args))
        | Expr.Macro(c, name, args) when name.StartsWith("unchecked_") ->
          match c.Type with
            | Ptr (Integer _ as i) -> Some(Expr.Macro({c with Type = i}, name, List.map self args)) 
            | _ -> None       
        | _ -> None
        
    // ============================================================================================================
    
    
    /// Remember which locals have the address of them taken, and then for each of them
    /// turn them into heap-allocated pointers. Same goes for local structs.
    /// TODO: add free(...) somewhere
    (* void f()
       {
          int x, y;
          struct S s;
          
          x = 7;
          g(&x);
          s.y = 12;          
       }
       
       void f()
       {
         int *x_;
         int y;
         struct S *s_;
         
         x_ = alloc(int);
         s_ = alloc(struct S);
         
         *x_ = 7;
         g(&( *x_));
         ( *s_).y = 12;
       }
     *)
    let rec replaceWithPointers (subst:Dict<_,_>) inClaim _ = function
      | Expr.Macro (c, "&", [Expr.Ref (_, v)]) ->
        match subst.TryGetValue v with
          | true, (v', _) -> Some (Expr.Ref (c, v'))
          | _ -> None
      | Expr.Ref (c, v) ->
        match subst.TryGetValue v with
          | true, (v', _) -> 
            let result = Expr.Deref (c, Expr.Ref ({ c with Type = v'.Type }, v'))
            let result = if inClaim then Old(c,  Macro(bogusEC, "_vcc_when_claimed", []), result) else result
            Some (result)
          | _ -> None
      | Expr.VarDecl (_, v, _) ->
        match subst.TryGetValue v with
          | true, (_, decl) -> Some(decl)
          | false, _ -> None
      | Expr.Macro(ec, "claim", args) ->
        Some(Expr.Macro(ec, "claim", List.map (fun (expr:Expr) -> expr.SelfMap(replaceWithPointers subst true)) args))
      | _ -> None

    let heapifyAddressedLocals decls =
      let addressableLocals = new Dict<_,_>()
      let addressableLocalsList = ref []
      let fnTok = ref bogusEC
      let fakeEC t = { !fnTok with Type = t }
      let pointernize comm v =
        let mkEc t = { comm with Type = t } : ExprCommon
        if not (addressableLocals.ContainsKey (v:Variable)) then
          let v' = { v.UniqueCopy() with Type = Type.MkPtr(v.Type, v.IsSpec); Name = "addr." + v.Name; Kind = VarKind.Local }
          let vRef = Expr.Ref({forwardingToken (comm.Token) None (fun () -> "&" + v.Name) with Type = v'.Type} , v')
          let alloc = Expr.Call (fakeEC v'.Type, internalFunction helper "stack_alloc", [v.Type], [Macro(bogusEC, "stackframe", []); BoolLiteral(boolBogusEC(), v.IsSpec)])
          let assign = Expr.Macro (fakeEC Void, "=", [vRef; alloc])
          let init =
            if v.Kind = VarKind.Parameter || v.Kind = VarKind.SpecParameter || v.Kind = VarKind.OutParameter then
              [Expr.Macro (fakeEC Void, "=", [Expr.Deref (fakeEC v.Type, Expr.Ref ({ comm with Type = v'.Type }, v')); mkRef v])]
            else []
          let def = VarDecl (fakeEC Void, v', []) :: assign :: init
          addressableLocals.[v] <- (v', Macro(fakeEC Void, "fake_block", def))
          addressableLocalsList := (v, (v', Macro(fakeEC Void, "fake_block", def))) :: !addressableLocalsList
          
      let pointsToStruct = function
        | Ptr(Type.Ref({Kind = (TypeKind.Struct|TypeKind.Union)} as td)) when not td.IsMathValue ->  true
        | _ -> false
          
      let rec findThem inBody self = function
         | Expr.Deref (_, dot) as expr ->
           let rec aux = function
             | Expr.Index (_, e, idx) -> 
               self idx
               aux e
             | Expr.Dot (_, e, _) -> aux e
             | Expr.Macro (_, "&", [Expr.Ref _]) -> ()
             | e -> self e
           aux dot
           false // don't recurse
         | Expr.Macro (_, "=", [Expr.Deref(_, e1); Expr.Deref(_, e2)]) when pointsToStruct e2.Type -> self e1; self e2; false            
         | Expr.Macro (_, "&", [Expr.Ref (c, ({ Kind = (VarKind.Local|VarKind.Parameter|VarKind.SpecLocal|VarKind.SpecParameter|VarKind.OutParameter) } as v))]) when inBody ->
           pointernize c v
           true
         | Expr.Macro (cmn, "&", [Expr.Ref (c, ({ Kind = (VarKind.Parameter|VarKind.SpecParameter|VarKind.OutParameter) } as v))]) when not inBody ->
           helper.Error(cmn.Token, 9666, "Cannot take an parameter's address inside of function contracts")
           true
         | Expr.VarDecl (c, ({ Type = Type.Ref td } as v), _) when td.IsUnion ->
           pointernize c v 
           true
         | _ -> true
            
      let doFunction (d:Function) =
        match d.Body with
          | Some b ->
            fnTok := { !fnTok with Token = d.Token }
            List.iter (fun (e:Expr) -> e.SelfVisit (findThem false)) (d.Reads @ d.Writes @ d.Requires @ d.Ensures)
            b.SelfVisit (findThem true)
            let b = b.SelfMap (replaceWithPointers addressableLocals false)
            let outParDecls = [ for (v, (_, expr)) in !addressableLocalsList do if v.Kind = VarKind.OutParameter then yield expr ]
            let b = Expr.MkBlock(outParDecls @ [b])
            d.Body <- Some b
          | None -> ()
        d
        
      decls |> mapFunctions doFunction
    
    // ============================================================================================================
    
    let handleGlobals decls =
      let globalSubst = new Dict<_,_>()
      let handle = function
        | Top.Global ({ Kind = VarKind.Global|VarKind.ConstGlobal; Type = Array (t, sz) } as v, init) ->
          let v' = { v.UniqueCopy() with Type = PhysPtr t; Kind = VarKind.ConstGlobal }
          globalSubst.[v] <- (v', Skip(bogusEC))
          let is_global = Expr.Macro (boolBogusEC (), "_vcc_is_global_array", 
                                      [mkRef v'; mkInt sz])
          [Top.Global (v', init); Top.GeneratedAxiom(is_global, Top.Global(v', None))]
        | Top.Global ({ Kind = VarKind.Global|VarKind.ConstGlobal|VarKind.SpecGlobal } as v, init) ->
          let v' = { v.UniqueCopy() with Type = Type.MkPtr(v.Type, v.Kind = VarKind.SpecGlobal); Kind = VarKind.ConstGlobal }
          globalSubst.[v] <- (v', Skip(bogusEC))
          let is_global = Expr.Macro (boolBogusEC (), "_vcc_is_global", 
                                      [mkRef v'])
          [Top.Global (v', init); Top.GeneratedAxiom(is_global, Top.Global(v',None))]
        | d -> [d]
        
      let replaceVarsInGeneratedAxioms = function
        | Top.GeneratedAxiom(ax, Top.Global(v, _)) as ga ->
          match globalSubst.TryGetValue(v) with
            | true, (v', _) -> Top.GeneratedAxiom(ax, Top.Global(v', None))
            | _ -> ga
        | t -> t
        
      decls |> List.map handle |> List.concat |> List.map replaceVarsInGeneratedAxioms |> deepMapExpressions (replaceWithPointers globalSubst false)  

   
    // ============================================================================================================
    
    /// Get rid of while(){}, do{}while(), for(;;){}, break and continue
    let rec loopAndSwitchDesugaring labels self s =
      let generateUnique = helper.UniqueId
      let selfWith labels (body:Expr) =
        body.SelfMap (loopAndSwitchDesugaring labels)
      let doLoop (loopEc:ExprCommon) contract =
        let unique = generateUnique().ToString()
        let break_lbl = { Name = "#break_" + unique } : LabelId
        let continue_lbl = { Name = "#continue_" + unique } : LabelId
        let rec aux invs writes variants = function
          | Block (_, exprs, _) :: rest -> aux invs writes variants (exprs @ rest)
          | Assert (_, Expr.Macro (_, "loop_writes", [e]), _) :: rest -> aux invs (e :: writes) variants rest
          | Assert (_, Expr.Macro (_, "loop_variant", [e]), _) :: rest -> aux invs writes (e :: variants) rest
          | Assert (_, e, _) :: rest -> aux (e :: invs) writes variants rest
          | [] -> (List.rev invs, List.rev writes, List.rev variants)
          | _ -> die()
        let (invs, writes, variants) = aux [] [] [] contract
        let mkLoop stmts =
          let loop = Loop ({ voidBogusEC() with Token = loopEc.Token }, invs, writes, variants, Expr.MkBlock stmts)
          Some (Expr.MkBlock [loop; Label (loopEc, break_lbl)])
        let inBody = selfWith (Some (break_lbl, continue_lbl))
        (mkLoop, inBody, break_lbl, continue_lbl)
      
      let doSwitch ctx stmts =
        let (expr, cases) = 
          match stmts with
          | expr :: cases -> (expr, cases)
          | _ -> die()
        let condCopy, condExpr = cache helper "switch" expr VarKind.Local
        let end_switch_lbl = { Name = "#end_of_switch_" + generateUnique().ToString() } : LabelId
        let updatedCtx =
          match ctx with
          | Some(_, continue_lbl) -> Some(end_switch_lbl, continue_lbl)
          | None -> Some(end_switch_lbl, ({ Name = "dummy_label"} : LabelId))
        let doCaseBody (stmts : Expr list) = [ for s in stmts -> s.SelfMap (loopAndSwitchDesugaring updatedCtx) ]
        let doCase case =
          let case_lbl = { Name = "#switch_case_" + generateUnique().ToString() } : LabelId
          let (token, caseExpr, caseBody) =
            match case with
            | Expr.Macro(token, "case", caseExpr :: caseBody) -> (token, Some(caseExpr), caseBody)
            | Expr.Macro(token, "default", caseBody) -> (token, None, caseBody)
            | _ -> die()
          let caseDispatch = 
            let gotoCase = Goto(token, case_lbl)
            match caseExpr with
            | None -> gotoCase
            | Some(caseExpr) -> If(voidBogusEC(), None, Prim({condExpr.Common with Type = Bool}, Op("==", Processed), [condExpr; caseExpr]), gotoCase, Expr.MkBlock([]))
          let doneCaseBody = [Label(token, case_lbl)] @ (doCaseBody caseBody)
          (caseDispatch, doneCaseBody)
          
        let (dispatch, bodies) = cases |> List.map doCase |> List.unzip
        let ec' = {expr.Common with Type = Void}
        Expr.MkBlock
         (condCopy @ dispatch @ [Goto(ec', end_switch_lbl)] @ (List.concat bodies) @ [Label(ec', end_switch_lbl)])
                  
      match s with
        | Macro (wtok, "while", [Macro (_, "loop_contract", conds); cond; body]) ->
          let (mkLoop, inBody, break_lbl, continue_lbl) = doLoop wtok conds
          mkLoop [ If (wtok, None, cond, 
                          inBody body, 
                          Expr.MkBlock([CAST.possiblyUnreachable; Goto (wtok, break_lbl)]));
                   Label (wtok, continue_lbl)]
     
        | Macro (wtok, "doUntil", [Macro (_, "loop_contract", conds); body; cond]) ->
          let (mkLoop, inBody, break_lbl, continue_lbl) = doLoop wtok conds
          let usedBreak = ref false
          let check _ = function
            | Expr.Label (_, l) ->
              if l.Name = break_lbl.Name || l.Name = continue_lbl.Name then
                usedBreak := true
              false
            | _ -> not !usedBreak // keep looking
          let body = inBody body
          let branch = If (wtok, None, cond, Goto (wtok, break_lbl), Expr.Skip({wtok with Type = Void}))
          //let branch = branch.SelfCtxMap(false, doRemoveLazyOps false false)
          let res () = mkLoop [ body; Label (wtok, continue_lbl); branch ]
          match cond with
            | Expr.BoolLiteral (_, true) ->
              body.SelfVisit check
              if !usedBreak then res ()
              else Some body
            | _ -> res ()
        
        | Macro (wtok, "for", [Macro (_, "loop_contract", conds); init; cond; incr; body]) ->
          let (mkLoop, inBody, break_lbl, continue_lbl) = doLoop wtok conds
          let loop =
            mkLoop [If (wtok, None, cond,
                         inBody body,
                         Expr.MkBlock([CAST.possiblyUnreachable; Goto (wtok, break_lbl)]));
                    Label (wtok, continue_lbl);
                    inBody incr ]
          Some (Expr.MkBlock [init; loop.Value])
        
        | Macro (token, "switch", condAndBody) -> Some (doSwitch labels condAndBody)
        | Macro (token, "match", _) as expr ->
          DataTypes.handleMatchStatement helper selfWith labels expr
        | Macro (token, "break", []) ->
          match labels with
            | Some (l, _) -> Some (Goto (token, l))
            | None -> None
        | Macro (token, "continue", []) ->
          match labels with
            | Some (_, l) -> Some (Goto (token, l))
            | None -> die()
        | _ -> None
        
    // ============================================================================================================\


    let checkSpecCode decls =

      let isPhysicalLocation triggerOnlyOnVolatileFields = 
        let rec isPhysicalLocation' = function 
          | Dot(_, _, f) when f.IsSpec -> false
          | Dot(_, _, f) when triggerOnlyOnVolatileFields && not f.IsVolatile -> false
          | Dot(_, ptr, _) -> isPhysicalLocation' ptr
          | Index(_, ptr, _) -> isPhysicalLocation' ptr
          | Ref(_, {Kind = SpecLocal|SpecParameter|OutParameter|QuantBound}) -> false        
          | Ref(_, {Type = Type.Ref td }) when td.IsRecord -> false
          | Ref(_, {Name = name}) when name.StartsWith("__temp") -> false // introduced during IExpression projection; unclear status
          | Deref(_, expr) -> 
            match expr.Type with 
              | SpecPtr _ -> false 
              | _ when triggerOnlyOnVolatileFields -> isPhysicalLocation' expr 
              | _  -> true
          | _ -> true
        isPhysicalLocation'

      let rec checkNoWritesToPhysicalFromSpec withinSpec self = function
       | Macro(cmn, "=", [location ; expr]) when isPhysicalLocation false location ->
         match exprDependsOnSpecExpr expr with
           | None when withinSpec ->
             helper.GraveWarning(cmn.Token, 9300, "assignment to physical location from specification code")
             false
           | None -> false
           | Some specField -> 
             helper.GraveWarning(cmn.Token, 9300, "assignment to physical location from specification " + specField)
             false
       | Macro(cmn, "out", [outPar]) when isPhysicalLocation false outPar ->
         helper.GraveWarning(cmn.Token, 9304, "physical location passed as out parameter")
         false
       | CallMacro(_, "spec", _, args) -> List.iter (fun (e:Expr) -> e.SelfVisit(checkNoWritesToPhysicalFromSpec true)) args; false
       | Call(ec, fn, _, _) when withinSpec && not fn.IsSpec && not fn.IsPure ->
         helper.GraveWarning(ec.Token, 9313, "call to impure implementation function '" + fn.Name + "' from specification code")
         false
       | _ -> true

      let rec isSpecType = function
        | Type.Array(t, _) 
        | Type.PhysPtr(t)
        | Type.Volatile(t) -> isSpecType t
        | Type.SpecPtr _
        | Type.Map _
        | Type.MathInteger _
        | Type.TypeIdT -> true
        | Type.Ref(td) -> td.IsSpec
        | _ -> false


      let checkFieldType (f:Field) =
        if not f.IsSpec && isSpecType f.Type then helper.GraveWarning(f.Token, 9301, "non-specification field '" + f.Name + "' has specification type '" + f.Type.ToString() + "'"); 

      let rec checkAccessToSpecFields ctx self = function
        | _ when ctx.IsPure -> 
          false
        | CallMacro(_, "spec", _, _) 
        | CallMacro(_, ("_vcc_unwrap"|"_vcc_wrap"|"_vcc_wrap_non_owns"|"_vcc_wrap_set"|"_vcc_unwrap_set"|"_vcc_alloc"|"_vcc_free"|"_vcc_stack_alloc"), _, _)
        | CallMacro(_, ("_vcc_havoc_others"), _, _)
        | CallMacro(_, ("_vcc_bump_volatile_version"|"_vcc_deep_unwrap"|"_vcc_union_reinterpret"|"_vcc_reads_havoc"),_ , _)
        | CallMacro(_, ("_vcc_set_owns"|"_vcc_set_closed_owner"|"_vcc_set_closed_owns"),_ , _)
        | CallMacro(_, ("_vcc_giveup_closed_owner"), _, _)
        | CallMacro(_, "unclaim", _, _) 
        | CallMacro(_, "by_claim", _, [_; _; _]) ->
          false
        | CallMacro(_, "_vcc_test_classifier", _, [_; cond]) ->
          cond.SelfVisit(checkAccessToSpecFields ctx);
          false
        | Macro(_, "=", [tgt; src]) as assign ->
          let tgt =
            match tgt with
              | Deref (c, CallMacro (_, "_vcc_retype", _, [p])) -> Deref(c, p)
              | e -> e
          match exprDependsOnSpecExpr tgt with
            | Some specThing ->
              helper.GraveWarning(tgt.Token, 9301, "write to specification " + specThing + " from non-specification code")
              false
            | _ -> true
        | Call(cmn, ({IsSpec = true} as fn), _, args) when fn.Name <> "_vcc_retype" ->
          helper.GraveWarning(cmn.Token, 9301, "access to specification function '" + fn.Name + "' within non-specification code")
          false
        | Call(_, f, _, args) ->
          let checkIfNotSpecPar (v : Variable) (expr : Expr) =
            if v.Kind <> VarKind.SpecParameter && v.Kind <> VarKind.OutParameter then expr.SelfCtxVisit(ctx.IsPure, checkAccessToSpecFields)
          List.iter2 checkIfNotSpecPar f.Parameters args
          false
        | Dot(cmn, _, f) when f.IsSpec ->
          helper.GraveWarning(cmn.Token, 9301, "access to specification field '" + f.Name + "' within non-specification code")
          true
        | Ref(cmn, ({Kind = SpecLocal} as v)) ->
          helper.GraveWarning(cmn.Token, 9301, "access to specification variable '" + v.Name + "' within non-specification code")
          false
        | Ref(cmn, ({Kind = SpecParameter|OutParameter} as v)) ->
          helper.GraveWarning(cmn.Token, 9301, "access to specification parameter '" + v.Name + "' within non-specification code")
          false
        | VarDecl(cmn, ({Kind = VarKind.Local} as v), _) when isSpecType v.Type ->
          helper.GraveWarning(cmn.Token, 9301, "non-specification object '" + v.Name + "' has specification type")
          false
        | _ -> true
        
      let errorForSecondPhysicalAccess (expr : Expr) =
        let foundInstances = ref None
        let rec isHeapAllocatedParOrLocal = function
          | Macro(_, "&", [Ref(_, {Kind = VarKind.Local|VarKind.Parameter|VarKind.SpecLocal|VarKind.SpecParameter|VarKind.OutParameter})]) -> true
          | Dot(_, ptr, _) -> isHeapAllocatedParOrLocal ptr
          | _ -> false
        
        let registerAndReportError (t:option<Type>) token =
          if t.IsSome && t.Value.SizeOf > !PointerSizeInBytes then
            helper.GraveWarning(token, 9320, "accessing " + (t.Value.SizeOf * 8).ToString() + " bits of memory may not be not atomic on this architecture")
          match !foundInstances with
            | None -> foundInstances := Some token
            | Some otherToken -> 
              helper.GraveWarning(token, 9302, "more than one access to physical memory in atomic block ('" + 
                                               token.Value + "' and '" + otherToken.Value + "'); extra accesses might be due to bitfield operations", Some(otherToken))
       
        let countPhysicalAccesses' ctx self = function
          | Deref(_, ptr) when not ctx.IsPure && isHeapAllocatedParOrLocal ptr -> true
          | Deref(cmn, ptr) when not ctx.IsPure && isPhysicalLocation true ptr -> registerAndReportError (Some cmn.Type) cmn.Token; true
          | CallMacro(cmn, "inlined_atomic", _, _) -> registerAndReportError None cmn.Token; false
          | CallMacro(_, "spec", _, _) -> false
          | _ -> true
        expr.SelfCtxVisit(false, countPhysicalAccesses')
        
      let checkAtMostOnePhysicalAccessInAtomic self = function
        | Atomic(_, _, body) as _atomic ->
          errorForSecondPhysicalAccess body
          false
        | _ -> true
      
      let checkParameterTypes (fn:Function) =
        let checkPar (v:Variable) =
          if v.Kind = VarKind.Parameter && isSpecType v.Type then
            helper.GraveWarning(fn.Token, 9301, "non-specification parameter '" + v.Name + "' of function '" + fn.Name + "' has specification type")
        List.iter checkPar fn.Parameters

      for d in decls do
        match d with 
          | Top.FunctionDecl({IsSpec = true}) -> ()
          | Top.FunctionDecl(fn) -> 
            if isSpecType fn.RetType then
              helper.GraveWarning(fn.Token, 9301, "non-specification function '" + fn.Name + "' returns value of specification type")
            checkParameterTypes fn
          | Top.TypeDecl(td) when not td.IsSpec ->
            List.iter checkFieldType td.Fields
          | _ -> ()
        
      for d in decls do
        match d with 
          | Top.FunctionDecl({IsSpec = true}) as d -> deepVisitExpressions (checkNoWritesToPhysicalFromSpec true) [d]
          | _ -> [d] |> deepVisitExpressionsCtx checkAccessToSpecFields 
                 [d] |> deepVisitExpressions (checkNoWritesToPhysicalFromSpec false)
                 [d] |> deepVisitExpressions checkAtMostOnePhysicalAccessInAtomic
        
      decls

    // ============================================================================================================\
  
    let pushDeclsIntoBlocks decls =
      
      // we use reference equality to speed this up as in most cases we will compare objects with themselves
      let commonPrefix l1 l2 = 
        let rec commonPrefix' acc l1 l2 =
          match l1, l2 with
            | [], _ 
            | _, [] -> List.rev acc
            | x::xs, y::ys when obj.ReferenceEquals(x,y) -> commonPrefix' (x::acc) xs ys
            | _ -> List.rev acc
        if obj.ReferenceEquals(l1, l2) then l1 else commonPrefix' [] l1 l2
              
      let findInnermostBlockForVariables (block:Expr) =
        let innermostSoFar = new Dict<_,_>()
        let rec findInnermostBlock blocks self =
          let insertOrJoin (v:Variable) =
            match innermostSoFar.TryGetValue v with
              | true, soFar -> innermostSoFar.[v] <- commonPrefix blocks soFar
              | _ -> innermostSoFar.Add(v, blocks)
          function 
            | Ref(_, v) -> insertOrJoin v; false
            | VarWrite(_, vs, _) -> List.iter insertOrJoin vs; true
            | Block(ec,ss,Some cs) ->
              List.iter self cs.Requires
              List.iter self cs.Ensures
              List.iter self cs.Reads
              List.iter self cs.Writes
              List.iter self cs.Decreases
              Block(ec,ss,None).SelfVisit(findInnermostBlock (blocks @ [block])); false
            | _ -> true
        block.SelfVisit(findInnermostBlock [block])
        
        let result = new Dict<_,_>()
        
        for kvp in innermostSoFar do 
          let last = List.rev >> List.head
          match last kvp.Value with
            // keep only those where the target is a block with contracts
            | Block(_,_,Some _) as block -> result.Add(kvp.Key, block)
            | _ -> ()
        result
        
      let moveDeclsIntoTargetBlocks (targetMap : Dict<Variable,Expr>) (block:Expr)= 
        let declsToReinsert = new Dict<_,_>()
        let markForReInsertion block decl =
          match declsToReinsert.TryGetValue block with
            | true, others -> declsToReinsert.[block] <- decl::others
            | _ -> declsToReinsert.Add(block, [decl])
        let rec moveDecls (currentBlock : Expr) _ = function
          | VarDecl(ec, v, []) as decl ->
            match targetMap.TryGetValue v with
              | true, tgt -> 
                targetMap.Remove(v) |> ignore
                if tgt = currentBlock then None 
                else 
                   markForReInsertion tgt decl
                   Some(Comment(ec, "__vcc__ pushed decl into block"))
              | _ -> None
          | Block (ec, ss, Some cs) as block ->
            let declsToMoveHere = 
              match declsToReinsert.TryGetValue block with
                | true, decls -> decls
                | _ -> []
            match Expr.MkBlock(declsToMoveHere @ [block.SelfMap (moveDecls block)]) with
                | Block (ec,ss',None) -> Some (Block(ec,ss',Some cs))
                | _ -> die()
          | _ -> None
        block.SelfMap(moveDecls Expr.Bogus)
            
      let doFunction (f:Function) =
        let doBody body =
          let targetBlocks = findInnermostBlockForVariables body
          if targetBlocks.Count = 0 then body else moveDeclsIntoTargetBlocks targetBlocks body
        f.Body <- Option.map doBody f.Body
        f
        
      mapFunctions doFunction decls        

    // ============================================================================================================\
    
    let fixGroupCasts self = 
      function
        | Expr.Cast ({ Type = PtrSoP (Type.Ref td, spec)} as c1, ch, e) when td.IsGroup ->
          let par = td.Parent.Value
          let isUs (f:Field) = f.Type = Type.Ref td
          let f = List.find isUs par.Fields
          let res e = Some (Expr.Dot (c1, e, f))
          match e.Type with
            | Ptr (Type.Ref sub) ->
              if sub = par then res e
              else if sub.IsGroup && sub.Parent.Value = par then
                res (Expr.Cast ({ c1 with Type = Type.MkPtr (Type.Ref par, spec) }, ch, e))
              else None
            | _ -> None
        | _ -> None
    
    // ============================================================================================================\
    
    helper.AddTransformer ("desugar-begin", TransHelper.DoNothing)
    
    helper.AddTransformer ("desugar-ite", TransHelper.Decl removeLazyOps)
    helper.AddTransformer ("norm-nested-locals", TransHelper.Decl removeNestedLocals)
    helper.AddTransformer ("norm-primitive-globals", TransHelper.Decl wrapPrimitiveGlobals)
    helper.AddTransformer ("desugar-addr-deref", TransHelper.Decl cleanupAddrDeref)
    helper.AddTransformer ("desugar-by-claim", TransHelper.Decl expandByClaim)
    helper.AddTransformer ("desugar-approvers", TransHelper.Decl handleApprovers)
    helper.AddTransformer ("desugar-assign-ops", TransHelper.Expr removeAssignOps)
    helper.AddTransformer ("desugar-lambdas", TransHelper.Decl desugarLambdas)
    helper.AddTransformer ("check-spec-code", TransHelper.Decl checkSpecCode)
    helper.AddTransformer ("desugar-push-decls-into-blocks", TransHelper.Decl pushDeclsIntoBlocks)
    helper.AddTransformer ("desugar-addressable-locals", TransHelper.Decl heapifyAddressedLocals)
    helper.AddTransformer ("desugar-globals", TransHelper.Decl handleGlobals)
    helper.AddTransformer ("desugar-loops", TransHelper.Expr (loopAndSwitchDesugaring None))
    helper.AddTransformer ("fix-group-casts", TransHelper.Expr fixGroupCasts)
    helper.AddTransformer ("datatype-wrap-ctors", TransHelper.Expr (DataTypes.handleSize helper))
     
    helper.AddTransformer ("desugar-end", TransHelper.DoNothing)
