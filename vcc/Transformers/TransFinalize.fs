//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light


namespace Microsoft.Research.Vcc
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.CAST
 
 module TransFinalize =

  let init (helper:TransHelper.TransEnv) =
    // ============================================================================================================

    let addRangeAssumptions =
      let rangeAssumptions (parm : Variable) =
        match parm.Type with
          | Ptr _
          | Integer _ 
          | MathInteger _ ->
            [inRange helper (boolBogusEC ()) (mkRef parm)]
          | _ ->
            []                    

      let mkFreeEnsures (expr:Expr) = Expr.Macro(expr.Common, "_vcc_assume", [expr])

      let quantRange self = function
        | Quant (c, q) ->
          let lst = List.concat (List.map rangeAssumptions q.Variables)
          let condition = Some (multiAnd (Option.toList q.Condition @ lst))
          Some (Quant (c, { q with Condition = condition; Body = self q.Body }))
        | _ -> None        

      let rangeAssume (parm:Variable) =
        List.map Expr.MkAssume (rangeAssumptions parm)
      let aux (h:Function) =
        if not (hasCustomAttr AttrIsAdmissibility h.CustomAttr) then
          h.Body <- Option.map (addStmts (List.concat (List.map rangeAssume (h.InParameters @ h.OutParameters)))) h.Body
          h.Ensures <- List.map mkFreeEnsures (List.concat (List.map rangeAssumptions h.OutParameters)) @ h.Ensures
        if h.RetType._IsInteger || h.RetType._IsPtr || h.RetType._IsMathInteger then
          let ec = { boolBogusEC() with Token = h.Token }
          h.Ensures <- (mkFreeEnsures (inRange helper ec (Expr.Result({bogusEC with Type = h.RetType})))) :: h.Ensures
        h
      mapFunctions aux >> deepMapExpressions quantRange
      
    // ============================================================================================================
    
    let addReturnConversions decls =
      for d in decls do
        match d with
          // we need the precise type information so the type can be added or stripped in the translator
          | Top.FunctionDecl ({ Body = Some b; RetType = (Ptr _|ObjectT) } as f) ->
            let repl _ = function
              | Return (c, Some e) ->
                Some (Return (c, Some (Cast ({ e.Common with Type = f.RetType }, Processed, e))))
              | _ -> None            
            f.Body <- Some (b.SelfMap repl)
          | _ -> ()
      decls
    
    
    // ============================================================================================================
     
    /// Change if (cond) tmp = e1; else tmp = e2; into tmp = cond?e1:e2; (as there are no
    /// assertions associated with e1 and e2).
    let foldIteBack self = function
      | If (c, None, cond, Block(_, [Assert(_, Macro(_, "_vcc_possibly_unreachable", []), []); VarWrite (_, tmp, e1)], None),
                           Block(_, [Assert(_, Macro(_, "_vcc_possibly_unreachable", []), []); VarWrite (_, tmp', e2)], None))
      | If (c, None, cond, VarWrite (_, tmp, e1), VarWrite (_, tmp', e2)) when tmp = tmp' ->
        Some (VarWrite (c, tmp, self (Expr.Macro (e1.Common, "ite", [cond; e1; e2]))))
      | _ -> None
      
    // ============================================================================================================
    
    let introduceAndOrs self = function
      | Expr.Macro (c, "ite", [e1; e2; EFalse]) -> Some (self (Expr.Prim (c, Op("&&", Processed), [e1; e2])))
      | Expr.Macro (c, "ite", [e1; ETrue; e2]) -> Some (self (Expr.Prim (c, Op("||", Processed), [e1; e2])))
      | Expr.Macro (c, "ite", [e1; e2; ETrue]) -> Some (self (Expr.Prim (c, Op("==>", Processed), [e1; e2])))
      
      | Expr.Prim (_, Op("||", _), [e1; EFalse])
      | Expr.Prim (_, Op("||", _), [EFalse; e1])
      | Expr.Prim (_, Op("&&", _), [e1; ETrue])
      | Expr.Prim (_, Op("&&", _), [ETrue; e1]) -> Some (self e1)
      
      | x -> None
      
    // ============================================================================================================
    

    let addBoolConversions decls =
      let rec f (x:Expr) =
        let self (e:Expr) = e.SelfMap doExpr
        convertToBool self x
        
      and fs = List.map f
      
      and doExpr self = function
        | Skip _
        | Expr.Ref _
        | Prim _
        | Expr.Call _
        | IntLiteral _
        | BoolLiteral _
        | Deref _
        | Dot _
        | Index _
        | Cast _
        | Result _
        | Old _
        | Macro _
        | VarWrite _
        | MemoryWrite _
        | Goto _
        | Label _
        | Block _
        | Return _
        | VarDecl _
        | Stmt _
        | Pure _
        | UserData _
        | SizeOf _
        | This _
        | Comment _ -> None
        
        | Quant (c, q) -> Some (Quant (c, { q with Body = f q.Body; Condition = Option.map f q.Condition }))
        | If (c, None, cond, e1, e2) -> Some (If (c, None, f cond, self e1, self e2))
        | If (c, cl, cond, e1, e2) -> Some (If (c, cl, f cond, self e1, self e2))
        | Loop (c, invs, writes, variants, body) -> Some (Loop (c, fs invs, List.map self writes, fs variants, self body)) //TODO check the treatment of the variants
        | Assert (c, cond, trigs) -> Some (Assert (c, f cond, trigs))
        | Assume (c, cond) -> Some (Assume (c, f cond))
        | Atomic (c, objs, body) -> Some (Atomic (c, List.map self objs, self body))

      let aux d =
        match d with
          | Top.Axiom e -> Top.Axiom (f e)
          | Top.GeneratedAxiom(e, origin) -> Top.GeneratedAxiom(f e, origin)
          | Top.FunctionDecl x ->
            x.Requires <- fs x.Requires
            x.Ensures <- fs x.Ensures
            x.Body <- Option.map (fun (e:Expr) -> e.SelfMap doExpr) x.Body
            d          
          | Top.TypeDecl td ->
            td.Invariants <- fs td.Invariants; d
          | Top.Global _ -> d
          
      // run handleConversions again to get rid of the junk we have generated
      decls |> List.map aux |> Normalizer.handleConversions helper            
    
    // ============================================================================================================
  
    let removeTrivialBitvectorOperations self = function
      | Expr.Macro (_, ("bv_extract_signed" | "bv_extract_unsigned"), 
                    [e; IntLiteral(_, sz); IntLiteral(_, z); IntLiteral(_, sz') ]) when z = zero && sz = sz' -> Some(self e)
      | Expr.Macro (_, "bv_update",
                    [_; IntLiteral(_, sz); IntLiteral(_, z); IntLiteral(_, sz'); e ]) when z = zero && sz = sz' -> Some(self e)
      | _ -> None
    
    let theKeepsWarning = function
      | TypeDecl td as decl when staticOwns td ->
        let rec check top self = function
          | Macro(_, "labeled_invariant", [_; i]) when top ->
            i.SelfVisit (check true)
            false
          | Prim (_, Op (("<==>"|"=="), _), [cond; keeps]) as e when top ->
            cond.SelfVisit (check false) 
            cond.SelfVisit (check true)
            false
          | BoolOp (_, "&&", e1, e2) as e when top -> self e1; self e2; false
          | Macro (_, "keeps", _) as e ->
            if not top then 
              helper.Warning (e.Token, 9110, "\\mine(...) (or ... \\in \\owns(\\this)) is not allowed here; " +
                                             "annotate the type '" + td.Name + "' with _(dynamic_owns)")
            true
          // 9111 for | Macro (_, "_vcc_set_in", _) as e ?
          | e when top ->
            e.SelfVisit (check false)
            false
          | _ -> true
        deepVisitExpressions (check true) [decl]
        decl
            
      | decl -> decl

    // ============================================================================================================
   
    let errorForMissingDynamicOwns decls =

      let checkAndWarn self = function
        | CallMacro(_, "_vcc_owns", _, [_; Cast(_,_,expr)]) 
        | CallMacro(_, "_vcc_owns", _, [_; expr]) as owns -> 
          match expr.Type with
            | Ptr(Type.Ref(td)) when staticOwns td ->
              helper.Error(owns.Token, 9662, "Explicit reference to owns-set of type '" + td.Name + "', which is static. Use \\mine(...) or mark '" + td.Name + "' with _(dynamic_owns).")
              true
            | _ -> true
        | _ -> true
        
      forEachInvariant checkAndWarn decls
      decls

    // ============================================================================================================          

    let assignExpressionStmts self = 
      let dummyId = ref 0
      let ignoreType = function
        | Type.Void
        | Type.Ref({Kind = TypeKind.MathType; Name = "$$bogus$$" }) -> true
        | _ -> false
      let rec stmtalize = function
        | Block(ec, [], cso) -> [Block(ec, [], cso)]
        | Block(ec, stmts, cso) ->
          let last, stmts' = TransUtil.splitLast stmts
          [Block({ec with Type = Type.Void}, stmts' @ stmtalize last, cso)]
        | expr when ignoreType expr.Type -> [expr]
        | expr ->
          let ecVoid = {expr.Common with Type = Type.Void}
          let dummy = getTmp helper ("stmtexpr" + ((!dummyId).ToString())) expr.Type VarKind.Local
          let decl = VarDecl(ecVoid, dummy, [])
          let assign = VarWrite(ecVoid, [dummy], expr)
          incr dummyId
          [decl; assign]
      function
        | If(ec, cl, cond, e1, e2) -> Some(If(ec, cl, self cond, Expr.MkBlock(stmtalize (self e1)), Expr.MkBlock(stmtalize (self e2))))
        | Loop(ec, inv, writes, variants, stmts) -> Some(Loop(ec, List.map self inv, List.map self writes, List.map self variants, Expr.MkBlock(stmtalize (self stmts))))
        | Stmt(ec, expr) when not (ignoreType expr.Type) -> Some(Expr.MkBlock(stmtalize (self expr)))
        | Atomic(ec, args, expr) -> Some(Atomic(ec, List.map self args, Expr.MkBlock(stmtalize (self expr))))
        | Block(ec, [], _) -> None
        | Block(ec, stmts, cso) ->
          let last, stmts' = splitLast stmts
          Some(Block(ec, (stmts' |> List.map self |> List.map stmtalize |> List.concat) @ [ self last ], cso))
          
        | _ -> None
        

    // ============================================================================================================

    let flattenBlocks self = function
      | Expr.Block(ec, stmts, cso) ->
        let rec loop acc = function
          | [] -> List.rev acc
          | Expr.Macro(_,"fake_block",nested)::stmts
          | Expr.Block(_, nested, None) :: stmts -> loop acc (nested @ stmts)
          | Expr.Comment(_, comment) :: stmts when comment.StartsWith("__vcc__") -> loop acc stmts
          | stmt :: stmts -> loop (self stmt :: acc) stmts
        Some(Expr.Block(ec, loop [] stmts, cso))
      | _ -> None
        
    // ============================================================================================================

    let handleStackAllocations =
      
      let rec findRealLocalLabels acc = function
        | [] -> acc
        | (Label (_,lbl)) :: es -> findRealLocalLabels (lbl::acc) es
        | _ :: es -> findRealLocalLabels acc es
      let rec findLocalLabels acc = function
        | [] -> acc
        | (Label (_,lbl)) :: es -> findLocalLabels (lbl::acc) es
        | e :: es ->
          let subLocalLabels =
            match e with
              | Prim (_,_,es')
              | Call (_,_,_,es')
              | Macro (_,_,es')
              | Block (_,es',_) -> findLocalLabels acc es'
              | Dot (_,e,_)
              | Cast (_,_,e)
              | VarWrite (_,_,e)
              | Assume (_,e)
              | Pure (_,e)
              | Return (_,Some e)
              | Stmt (_,e)
              | Deref (_,e) -> findLocalLabels acc [e]
              | Old (_,e1,e2)
              | MemoryWrite(_,e1,e2)
              | Index (_,e1,e2) -> findLocalLabels acc [e1;e2]
              | If (_,_,cond,thenB,elseB) -> findLocalLabels acc [cond;thenB;elseB]
              | Atomic (_,es',e) -> findLocalLabels acc (e::es')
              | Assert (_,e,es') -> findLocalLabels acc (e::(List.concat es'))
              | Label _ -> die()
              | Loop _ // We know that we won't jump into loops, for now
              | _ -> []
          subLocalLabels@(findLocalLabels acc es)
      let rec findLocalStackDeallocs acc = function
        | [] -> acc
        | (VarWrite(ec, [v], CallMacro(_,"_vcc_stack_alloc",_,_))) :: es ->
          let vName = if v.Name.StartsWith "addr." then v.Name.Substring(5) else v.Name
          let ec' = {forwardingToken (ec.Token) None (fun () -> "stack_free(&" + vName + ")") with Type = Void }
          let vRef = Expr.Ref({forwardingToken (ec.Token) None (fun () -> "&" + vName) with Type = v.Type}, v)
          let free = Expr.Call(ec',internalFunction helper "stack_free", [], [Expr.Macro(ec', "stackframe", []); vRef])
          findLocalStackDeallocs (free::acc) es
        | Macro (_,"fake_block",ss) :: es -> findLocalStackDeallocs acc (ss@es)
        | _ :: es -> findLocalStackDeallocs acc es
      let deallocStmtFromEcAndCall ec call = Expr.Stmt(ec,call)
      let rec deallocsFromLbl acc lbl = function
        | [] -> die()
        | (lbls,deallocs)::scs ->
          if (List.exists (fun x -> lbl = x) lbls) then acc
                                                   else deallocsFromLbl (deallocs@acc) lbl scs
      let rec pushFreesIn frees = function
        | [] -> die()
        | [x] -> frees@[x]
        | x::xs -> x::(pushFreesIn frees xs)
      let scopes = ref []

      let rec handleBlocks self = function
        | Block (ec, es, None) as b ->
          let localLabels = findRealLocalLabels [] es
          let subLocalLabels = findLocalLabels [] es
          let localDeallocs = findLocalStackDeallocs [] es
          let childrenChanges = ref false
          let oldScopes = !scopes
          scopes := (subLocalLabels,localDeallocs)::(!scopes)
          let handleChildren self e =
            match handleBlocks self e with
              | None -> None
              | Some e' -> childrenChanges := true; Some e'
          let es' = List.map (fun (e : Expr) -> e.SelfMap(handleChildren)) es
          let lds = List.map (deallocStmtFromEcAndCall ec) localDeallocs
          scopes := oldScopes
          match !childrenChanges,localDeallocs,!scopes with
            | false,[],_
            | false,_,[] -> Some b
            | false,_,_ -> Some(Block(ec,es@(Comment(ec,"Block cleanup")::lds),None))
            | true,[],_
            | true,_,[] -> Some(Block(ec,es',None))
            | true,_,_ -> Some(Block(ec,es'@(Comment(ec,"Block cleanup")::lds),None))
        | Goto (ec, lbl) as g ->
          match deallocsFromLbl [] lbl (!scopes) with
            | [] -> None
            | ds -> 
              let ds' = List.map (deallocStmtFromEcAndCall ec) ds
              Some(Block(ec,ds'@[g],None))
        | Return(ec,Some(Block(ec',es,None))) as r ->
          match List.concat (List.map snd (!scopes)) with
            | [] -> None
            | ds -> 
              let ds' = List.map (deallocStmtFromEcAndCall ec) ds
              Some(Return(ec,Some(Block(ec',pushFreesIn ds' es,None))))
        | Return (ec,_) as r ->
          match List.concat (List.map snd (!scopes)) with
            | [] -> None
            | ds -> 
              let ds' = List.map (deallocStmtFromEcAndCall ec) ds
              Some(Block(ec,ds'@[r],None))
        | _ -> None
            
      let handleFunction (f : Function) =
        match f.Body with
          | None -> f
          | Some body ->
            scopes := []
            let body' = (body.SelfMap(handleBlocks))
            f.Body <- Some(body')
            f

      mapFunctions handleFunction
            
    // ============================================================================================================
    
    let errorForOldInOneStateContext decls =
    
      let reportErrorForOld self = function
        | Expr.Old(ec, Expr.Macro(_, "prestate", []), expr) ->
          helper.Error(ec.Token, 9697, "\\old(...) is allowed only in two-state contexts")
          false
        | CallMacro(ec, n, _, args) ->
          match helper.PureCallSignature n with
            | Some signature when signature.Contains("s") -> 
              helper.Error(ec.Token, 9697, "calling '" + n + "' is allowed only in two-state contexts")
              false
            | _ -> true
        | _ -> true
            
      let checkFunction (fn:Function) =
        List.iter (fun (e : Expr) -> e.SelfVisit(reportErrorForOld)) 
                  (fn.Requires @ (if fn.IsPure then fn.Ensures else []) @ fn.Reads @ fn.Writes) 
        
      for d in decls do
        match d with
          | Top.FunctionDecl(fn) -> checkFunction fn
          | _ -> ()
            
      decls
    
    // ============================================================================================================

    let errorForStateWriteInPureContext decls = 
    
      let reportErrorForStateWriteInPureContext ctx self = function
        | CallMacro(ec, ("_vcc_alloc"|"_vcc_spec_alloc"|"_vcc_spec_alloc_array"),_ ,_) when ctx.IsPure -> 
          helper.Error(ec.Token, 9703, "Memory allocation in pure context is not allowed."); false
        | MemoryWrite(ec, loc, _) when ctx.IsPure -> 
          helper.Error(ec.Token, 9703, "Writing memory location '" + loc.Token.Value + "' in pure context is not allowed."); false
        | Call(ec, fn, _, _) when ctx.IsPure && fn.Writes.Length > 0 -> 
          helper.Error(ec.Token, 9703, "Calling function '" + fn.Name + "' with non-empty writes clause in pure context is not allowed."); false
        | Atomic(ec, _, _) when ctx.IsPure ->
          helper.Error(ec.Token, 9703, "Atomic block in pure context is not allowed."); false
        | _ -> true
    
      let checkFunction (fn:Function) = 
        List.iter (fun (e:Expr) -> e.SelfCtxVisit(true, reportErrorForStateWriteInPureContext)) (fn.Requires @ fn.Ensures @ fn.Reads @ fn.Writes @ fn.Variants)
        Option.iter (fun (e:Expr) -> e.SelfCtxVisit(fn.IsPure, reportErrorForStateWriteInPureContext)) fn.Body

      for d in decls do
        match d with 
          | Top.FunctionDecl(fn) -> checkFunction fn
          | _ -> ()
    
      decls

    // ============================================================================================================

    let rec flattenOld _ = function
      | Old(ec, (Expr.Macro(_, "prestate", []) as ps), expr) ->
        let removeOldForPrestate self = function
          | Old(_, Expr.Macro(_, "prestate", []), expr)  -> Some(self expr)
          | Old(_, _, _) as o -> Some(o.SelfMap(flattenOld))
          | _ -> None
        Some(Old(ec, ps, expr.SelfMap(removeOldForPrestate)))
      | _ -> None
    
    // ============================================================================================================

    let insertTypeArgumentForWrapUnwrap _ = 
      let typeOf (expr:Expr) = Expr.Macro({expr.Common with Type = Type.TypeIdT}, "_vcc_typeof", [expr])
      function
        | CallMacro(ec, ("_vcc_wrap"|"_vcc_unwrap"|"_vcc_deep_unwrap" as name), _, [e]) -> Some(Macro(ec, name, [e; typeOf e]))
        | _ -> None
    
    // ============================================================================================================
    
    let errorForWhenClaimedOutsideOfClaim decls =

      let errorForWhenClaimedOutsideOfClaim' _ = function
        | Macro(_, ("claim" | "_vcc_claims" | "upgrade_claim"), body) -> false
        | CallMacro(ec, "_vcc_when_claimed", _, _) ->
          helper.Error(ec.Token, 9708, "'\\when_claimed' cannot be used outside of a claim.")
          false
        | _ -> true

      deepVisitExpressions errorForWhenClaimedOutsideOfClaim' decls
      decls

    // ============================================================================================================

    let errorForInvWithNegativPolarity decls =
    
      let polarityStatus polarity = if polarity = 0 then "unknown" else "negative"

      // polarity: -1, 1, and 0 for unknown 
      // once we are 'unknown', only search for invariants and report errors
 
      let rec checkPolarity seenFunctions polarity  _ = function
        | CallMacro(ec, ("_vcc_inv"|"_vcc_inv2"), _, _) ->
          if (polarity <= 0) then
            helper.Error(ec.Token, 9712, "Use of '\\inv(...)' or '\\inv2(...)' with " + polarityStatus polarity + " polarity.")
          true
        | Call(ec, fn, _, args) -> 
          checkPolarities seenFunctions 0 args
          if Set.contains fn.UniqueId seenFunctions then
            helper.Error(ec.Token, 9712, "Encountered cyclic dependency for function '" + fn.Name + "' when checking for legal use of \\inv(...) or \\inv2(...)")
          else checkPolarities (Set.add fn.UniqueId seenFunctions) polarity fn.Ensures
          false
        | _ when polarity = 0 -> true // stick on unknown
        | Prim(_, Op(("=="|"<==>"), _), [Expr.Result _; e]) -> true
        | Macro(_, "labeled_invariant", _)
        | Prim(_, Op(("||"|"&&"), _), _)
        | Quant _
        | Old _ -> true // these do not change polarity
        | Prim(_, Op("!", _), [e]) -> e.SelfVisit (checkPolarity seenFunctions (-polarity)); false
        | Prim(_, Op("<==", _), [e2; e1])
        | Prim(_, Op("==>", _), [e1; e2]) -> e1.SelfVisit (checkPolarity seenFunctions (-polarity)); e2.SelfVisit (checkPolarity seenFunctions polarity); false
        | Macro(_, "ite", [cond; e1; e2]) -> // (cond ==> e1) && (!cond ==> e2)
          cond.SelfVisit (checkPolarity seenFunctions 0); e1.SelfVisit (checkPolarity seenFunctions polarity); e2.SelfVisit (checkPolarity seenFunctions polarity); false
        | e -> e.SelfVisit (checkPolarity seenFunctions 0); false // AST node with unknown effect on polarity, switch to unknown polarity
      and checkPolarities seenFunctions polarity = List.iter (fun (e:Expr) -> e.SelfVisit(checkPolarity seenFunctions polarity))
        
      for d in decls do
        match d with 
          | Top.TypeDecl(td) -> checkPolarities Set.empty 1 td.Invariants
          | Top.Axiom(e)
          | Top.GeneratedAxiom(e,_) -> e.SelfVisit(checkPolarity Set.empty 1)
          | _ -> ()
          
      decls
    
    // ============================================================================================================
    
    let flattenTestClassifiers decls =
      let rec moveTestClassifiers _ = function
        | If(ec, None, Macro(_, "_vcc_test_classifier", [c;test]), t, e) -> Some (If(ec,Some(c.SelfMap(moveTestClassifiers)),test.SelfMap(moveTestClassifiers),t.SelfMap(moveTestClassifiers),e.SelfMap(moveTestClassifiers)))
        | _ -> None
      for d in decls do
        match d with
          | Top.FunctionDecl fn ->
            match fn.Body with
              | Some body -> fn.Body <- Some (body.SelfMap(moveTestClassifiers))
              | None -> ()
          | _ -> ()
      decls

    // ============================================================================================================

    let checkTriggerOps _ = function
      | Expr.Quant(_, ({Kind = (QuantKind.Forall|QuantKind.Exists)} as qd)) ->
        let reportErrorForUnallowedOperations _ = function
          | Expr.Prim(ec, Op(("=="|"!"|"&&"|"||" as op), _), _) ->
            helper.Error(ec.Token, 9718, "operator \'" + op + "\' not allowed in triggers")
            false
          | Expr.Prim(ec, Op(("<"|"<="|">"|">=" as op), _), _) when not helper.Options.OpsAsFunctions ->
            helper.Error(ec.Token, 9718, "operator \'" + op + "\' not allowed in triggers when /opsasfuncs is not set")
            false
          | _ -> true
        List.iter (List.iter (fun (e:Expr) -> e.SelfVisit(reportErrorForUnallowedOperations))) qd.Triggers
        None          
      | _ -> None

    // ============================================================================================================

    let removeTrivial decls =

      let replaceTrivialEqualities _ = function
        | Expr.Prim(ec, Op("==", _), [e0; e1]) when e0.ExprEquals(e1) ->
          Some(BoolLiteral(ec, true))
        | _ -> None

      let removeTrivialAsserts _ = function
        | Assert(ec, BoolLiteral(_, true), _) -> Some(Expr.Comment(ec, "assert true"))
        | Assume(ec, BoolLiteral(_, true)) -> Some(Expr.Comment(ec, "assume true"))
        | Macro(ec, "_vcc_assume", [BoolLiteral(_, true)]) -> Some(BoolLiteral(ec, true))
        | _ -> None
        
      let decls' = decls |> deepMapExpressions replaceTrivialEqualities |> deepMapExpressions removeTrivialAsserts

      for d in decls' do
        match d with
          | Top.FunctionDecl(fn) -> 
            fn.Ensures <- fn.Ensures |> List.filter (function | BoolLiteral(_, true) -> false | _ -> true)
            fn.Requires <- fn.Requires |> List.filter (function | BoolLiteral(_, true) -> false | _ -> true)
          | _ -> ()
      
      decls'

    // ============================================================================================================

    let rec errorWhenJumpingFromAtomic inAtomic _= function
      | Atomic(_, _, body) -> body.SelfMap(errorWhenJumpingFromAtomic true) |> ignore; None
      | Return(ec, _) when inAtomic ->
        helper.Error(ec.Token, 9742, "returning from within _(atomic ...) is not allowed")
        None
      | Goto(ec, _) when inAtomic ->
        helper.Error(ec.Token, 9742, "goto from within _(atomic ...) is not allowed")
        None
      | Label(ec, _) when inAtomic ->
        helper.Error(ec.Token, 9742, "label withing _(atomic ...) is not allowed")
        None
      | _ -> None

    // ============================================================================================================

    let sortDecls decls = 
      if not helper.Options.DeterminizeOutput then decls
      else
        let rec declCompare d0 d1 = 
          match d0, d1 with
            | Top.Global (g0, _), Top.Global (g1, _) -> g0.Name.CompareTo(g1.Name)
            | Top.Global _, _ -> -1

            | Top.TypeDecl t0, Top.TypeDecl t1 -> t0.Name.CompareTo(t1.Name)
            | Top.TypeDecl _, Top.Global _ -> 1
            | Top.TypeDecl _, _ -> -1

            | Top.FunctionDecl f0, Top.FunctionDecl f1 -> f0.Name.CompareTo(f1.Name)
            | Top.FunctionDecl _, Top.Global _-> 1
            | Top.FunctionDecl _, Top.TypeDecl _-> 1
            | Top.FunctionDecl _, _ -> -1

            | Top.Axiom a0, Top.Axiom a1 -> a0.Token.Byte.CompareTo(a1.Token.Byte)
            | Top.Axiom _, Top.GeneratedAxiom _ -> -1
            | Top.Axiom _, _ -> 1

            | Top.GeneratedAxiom(a0, t0), Top.GeneratedAxiom(a1, t1) ->
              let ct = declCompare t0 t1
              if ct <> 0 then ct else a0.Token.Byte.CompareTo(a1.Token.Byte)
            | Top.GeneratedAxiom _, _ -> 1
        List.sortWith declCompare decls

    // ============================================================================================================

    let errorForResultWhenThereIsNone decls = 

      let reportErrorForResult = 
        let reportErrorForResult' _ = function
          | Result(ec) -> helper.Error(ec.Token, 9746, "Cannot use '\\result' in this context."); false
          | _ -> true

        List.iter (fun (expr:Expr) -> expr.SelfVisit(reportErrorForResult')) 

      for d in decls do
        match d with
          | Top.FunctionDecl(fn) -> 
            reportErrorForResult fn.Requires            
            reportErrorForResult fn.Reads
            reportErrorForResult fn.Writes
            reportErrorForResult fn.Variants
            if fn.RetType = Type.Void then reportErrorForResult fn.Ensures            
          | _ -> ()
      decls
                  
    // ============================================================================================================

    let errorForMe decls =

      let errorForMeInInvariant _ = function
        | Macro(ec, "_vcc_me", []) ->
          helper.Error(ec.Token, 9749, "Cannot refer to '\me' in invariant", None)
          false
        | _ -> true

      let errorForAddressOfMe _ = function
        | Macro(ec, "&", [Macro(_, "_vcc_me", [])]) ->
          helper.Error(ec.Token, 9750, "Cannot take address of '\me'", None)
          false
        | _ -> true

      decls |> deepVisitExpressions errorForAddressOfMe

      for d in decls do
        match d with
          | Top.TypeDecl(td) ->
            td.Invariants |> List.iter (fun (e:Expr) -> e.SelfVisit(errorForMeInInvariant))
          | _ -> ()

      decls

    // ============================================================================================================

    helper.AddTransformer ("final-begin", TransHelper.DoNothing)
    
    helper.AddTransformer ("final-range-assumptions", TransHelper.Decl addRangeAssumptions)
    helper.AddTransformer ("final-return-conversions", TransHelper.Decl addReturnConversions)
    helper.AddTransformer ("final-free-stack", TransHelper.Decl handleStackAllocations)
    helper.AddTransformer ("final-flatten-blocks", TransHelper.Expr flattenBlocks)
    helper.AddTransformer ("final-stmt-expressions", TransHelper.Expr assignExpressionStmts)
    helper.AddTransformer ("final-linearize", TransHelper.Decl (ToCoreC.linearizeDecls helper))
    helper.AddTransformer ("final-keeps-warning", TransHelper.Decl (List.map theKeepsWarning))
    helper.AddTransformer ("final-dynamic-owns", TransHelper.Decl errorForMissingDynamicOwns)
    helper.AddTransformer ("final-error-result", TransHelper.Decl errorForResultWhenThereIsNone)
    helper.AddTransformer ("final-error-old", TransHelper.Decl errorForOldInOneStateContext)
    helper.AddTransformer ("final-error-pure", TransHelper.Decl errorForStateWriteInPureContext)
    helper.AddTransformer ("final-error-me", TransHelper.Decl errorForMe)
    helper.AddTransformer ("final-error-when-claimed", TransHelper.Decl errorForWhenClaimedOutsideOfClaim)
    helper.AddTransformer ("final-error-arithmetic-in-trigger", TransHelper.Expr checkTriggerOps)
    helper.AddTransformer ("final-error-jump-from-atomic", TransHelper.Expr (errorWhenJumpingFromAtomic false))
    helper.AddTransformer ("final-move-test-classifiers", TransHelper.Decl flattenTestClassifiers)
    helper.AddTransformer ("final-before-cleanup", TransHelper.DoNothing)
    // reads check goes here

    helper.AddTransformer ("datatype-wrap-ctors", TransHelper.ExprCtx (DataTypes.wrapDatatypeCtors helper))
    
    helper.AddTransformer ("final-fold-ITE", TransHelper.Expr foldIteBack)
    helper.AddTransformer ("final-ITE-to-logical", TransHelper.Expr introduceAndOrs)
    helper.AddTransformer ("final-bool-conversions", TransHelper.Decl addBoolConversions)
    helper.AddTransformer ("final-bv-cleanup", TransHelper.Expr removeTrivialBitvectorOperations)
    helper.AddTransformer ("final-error-inv-polarity", TransHelper.Decl errorForInvWithNegativPolarity)
    helper.AddTransformer ("final-flatten-old", TransHelper.Expr flattenOld)
    helper.AddTransformer ("final-insert-type-arguments", TransHelper.Expr insertTypeArgumentForWrapUnwrap)
    helper.AddTransformer ("final-insert-state-arguments", TransHelper.Expr (ToCoreC.handlePureCalls helper))
    helper.AddTransformer ("final-remove-trivial", TransHelper.Decl removeTrivial)
    helper.AddTransformer ("final-sort-decls", TransHelper.Decl sortDecls)
    
    helper.AddTransformer ("final-end", TransHelper.DoNothing)
