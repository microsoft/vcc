//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.CAST
 
 module ExtraWarnings =

  // ============================================================================================================          

  type VarMap = Map<Variable, Token>

  type private SideEffects =
    {
      VarWrites : VarMap
      VarReads : VarMap
      PureFunctionCall : Option<Function * Token>
      ImpureFunctionCall : Option<Function * Token>
      MemRead : Option<Token>
      MemWrite : Option<Token>
    }

  let private seNone = { VarWrites = Map.empty; VarReads = Map.empty; PureFunctionCall = None; ImpureFunctionCall = None; MemRead = None; MemWrite = None }

  let private seUnion se0 se1 = 

    let opUnion op0 op1 = 
      match op0 with
        | None -> op1
        | Some _ -> op0 

    let varWrites = Map.foldBack (Map.add) se0.VarWrites se1.VarWrites
    let varReads = Map.foldBack (Map.add) se0.VarReads se1.VarReads
    let pureFn = opUnion se0.PureFunctionCall se1.PureFunctionCall
    let impureFn = opUnion se0.ImpureFunctionCall se1.ImpureFunctionCall
    let memRead = opUnion se0.MemRead se1.MemRead
    let memWrite = opUnion se0.MemWrite se1.MemWrite

    { VarWrites = varWrites; VarReads = varReads; PureFunctionCall = pureFn; ImpureFunctionCall = impureFn; MemRead = memRead; MemWrite = memWrite }

  let private seWarnForConflicts (helper : TransHelper.TransEnv) se0 se1 =

    let warnVarConflict kind1 (map0 : VarMap) (map1 : VarMap) = 
      let noWarning = ref true
      let warnVarConflict' v tok =
        match Map.tryFind v map1 with
          | Some tok' -> 
            helper.GraveWarning(tok, 9325, "Writing '" + v.Name + "' may have sequence conflict with " + kind1, Some(tok'))
            noWarning := false
          | _ -> ()
      Map.iter warnVarConflict' map0
      !noWarning

    let warnFunctionConflict = function
      | Some((fn0 : Function), tok0), Some((fn1 : Function), tok1) -> 
        helper.GraveWarning(tok0, 9325, "Call to '" + fn0.Name + "' may have sequence conflict with call to '" + fn1.Name + "'", Some(tok1))
        false
      | _ -> true

    let warnMemoryConflict kind1 = function
      | Some(tok0), Some(tok1:Token) ->
        helper.GraveWarning(tok0, 9325, "Writing memory '" + tok0.Value + "' may have sequence conflict with " + kind1 + " '" + tok1.Value + "'", Some(tok1))
        false
      | _ -> true

    let warnFuncMemConflict kind0 = function
      | Some(tok0), Some((fn1 : Function), tok1) ->
        helper.GraveWarning(tok0, 9325, "Memory " + kind0 + " '" + tok0.Value + "' may have sequence conflict with call to '" + fn1.Name + "'", Some(tok1))
        false
      | _ -> true

    warnVarConflict "other write" se0.VarWrites se1.VarWrites 
    && warnVarConflict "read" se0.VarWrites se1.VarReads
    && warnVarConflict "read" se1.VarWrites se0.VarReads
    && warnMemoryConflict "write" (se0.MemWrite, se1.MemWrite)
    && warnMemoryConflict "read" (se0.MemWrite, se1.MemRead)
    && warnMemoryConflict "read" (se1.MemWrite, se0.MemRead)
    && warnFunctionConflict (se0.ImpureFunctionCall, se1.ImpureFunctionCall)
    && warnFunctionConflict (se0.PureFunctionCall, se1.ImpureFunctionCall)
    && warnFunctionConflict (se0.ImpureFunctionCall, se1.PureFunctionCall)
    && warnFuncMemConflict "write" (se0.MemWrite, se1.PureFunctionCall)
    && warnFuncMemConflict "write" (se0.MemWrite, se1.ImpureFunctionCall)
    && warnFuncMemConflict "write" (se1.MemWrite, se0.PureFunctionCall)
    && warnFuncMemConflict "write" (se1.MemWrite, se0.ImpureFunctionCall)
    && warnFuncMemConflict "read" (se0.MemRead, se1.ImpureFunctionCall)
    && warnFuncMemConflict "read" (se1.MemRead, se0.ImpureFunctionCall)    
   
  let warnForSequenceProblems (helper:TransHelper.TransEnv) decls =

    let rec checkSequences warn = function
      | [] -> seNone
      | e0 :: es ->
        let se0 = checkSequence e0
        checkSequences' warn se0 es

    and checkSequences' warn se0 = function
      | [] -> se0
      | e1 :: es ->
        let se1 = checkSequence e1
        if warn then seWarnForConflicts helper se0 se1 |> ignore
        checkSequences' warn (seUnion se0 se1) es

    and checkSequence = function
      | Skip _ 
      | IntLiteral _
      | BoolLiteral _
      | This _
      | VarDecl _
      | Goto _
      | Label _
      | Return(_, None) 
      | Result _
      | SizeOf _
      | Assert _
      | Assume _
      | Pure _
      | UserData _
      | Comment _        -> seNone

      | Prim(_, _, args) -> checkSequences true args

      | Call(ec, fn, _, args) ->
        let seArgs = checkSequences true args
        let pureCall, impureCall = if fn.IsPure then Some(fn, ec.Token), seArgs.ImpureFunctionCall else seArgs.PureFunctionCall, Some(fn, ec.Token)
        {seArgs with PureFunctionCall = pureCall; ImpureFunctionCall = impureCall }

      | Deref(_, Dot(_, Macro(_, "&", [expr]), _)) -> checkSequence expr

      | Deref(ec, expr) ->
        {checkSequence expr with MemRead = Some(ec.Token) }

      | Index(ec, expr, idx) ->
        checkSequences true [expr; idx]

      | Dot(_, expr, _) 
      | Return(_, Some(expr))
      | Cast(_,_, expr) 
      | Quant(_, {Body = expr}) -> checkSequence expr

      | Old(_, e0, e1) -> checkSequences true [e0; e1]

      | Ref(ec, v) -> {seNone with VarReads = Map.add v ec.Token Map.empty}

      | VarWrite(ec, vs, expr) ->
        let se = checkSequence expr
        let varWrites  = List.fold (fun m v -> Map.add v ec.Token m) Map.empty vs
        let combinedWrites = List.fold (fun m v -> Map.add v ec.Token m) se.VarWrites vs
        seWarnForConflicts helper { seNone with VarWrites = varWrites } { se with VarReads = Map.empty } |> ignore
        { se with VarWrites = combinedWrites }

      | MemoryWrite(ec, e0, e1) ->
        let se = checkSequences true [e0; e1]
        { se with MemWrite = Some(ec.Token) }

      | If(_, _, cond, _then, _else) ->
        checkSequence cond |> ignore
        checkSequence _then |> ignore
        checkSequence _else |> ignore
        seNone

      | Loop(_, _, _, _, body) -> 
        checkSequence body |> ignore
        seNone

      | Block(_, stmts, _) ->
        checkSequences false stmts
                
      | Atomic(_, exprs, body) ->
        checkSequences true exprs |> ignore
        checkSequence body |> ignore
        seNone

      | Stmt(_, expr) ->
        checkSequence expr |> ignore
        seNone

      | Macro(_, "fake_block", stmts) -> checkSequences false stmts
      | Macro(_, _, args) -> checkSequences true args

    for d in decls do
      match d with 
        | Top.FunctionDecl({Body = Some body}) -> checkSequence body |> ignore
        | _ -> ()

    decls

  let init (helper:TransHelper.TransEnv) =

    let warnForUncheckedGhostLoops decls = 

      let rec warnForUncheckedGhostLoops fn withinSpec self = function
        | Loop(ec, _, _, _, _) 
        | Macro(ec, ("while"|"doUntil"|"for"), _) when withinSpec -> helper.GraveWarning (ec.Token, 9323, "ghost loop not checked for termination"); true
        | CallMacro(_, "spec", _, args) -> List.iter (fun (e:Expr) -> e.SelfVisit(warnForUncheckedGhostLoops fn true)) args; false
        | _ -> true    

      for d in decls do
        match d with
          | Top.FunctionDecl({Body = Some body} as fn) when not (checkTermination helper fn) ->
            body.SelfVisit(warnForUncheckedGhostLoops fn fn.IsSpec)
            ()
          | _ -> ()

      decls

    // ============================================================================================================          

    let warnForOldWithoutVolatiles decls =
      
      let rec isVolatileType = function
        | Type.Ref({IsVolatile = true}) | Volatile(_) -> true
        | Ptr(t) | Array(t, _) -> isVolatileType t
        | _ -> false
      
      let mentionsVolatile (expr:Expr) =
        let foundVolatile = ref false     
        let continueIfNotFound() = not !foundVolatile
        let found() = foundVolatile := true; false
        let findVolatile _ = function
          | Expr.Dot(_,_,f) when f.IsVolatile || isVolatileType f.Type -> found()
          | CallMacro(_, "_vcc_current_state", _, _) -> found()
          | CallMacro(_, "_vcc_closed", _, _) -> found()
          | CallMacro(_, "_vcc_owns", _, [Cast(_,_, expr)|expr]) ->
            match expr.Type with 
              | Ptr(Type.Ref(td)) ->
                if hasCustomAttr AttrVolatileOwns td.CustomAttr then found() else continueIfNotFound()
              | _ -> continueIfNotFound()
          | _ -> continueIfNotFound()
        expr.SelfVisit findVolatile 
        !foundVolatile

      let doWarn self = function
        | Expr.Old(_, Macro (_, "prestate", []), e) as expr when not (mentionsVolatile e) ->
          helper.Warning(expr.Token, 9115, "'\\old' in invariant does not refer to volatile state")
          true
        | _ -> true
      
      forEachInvariant doWarn decls
          
      decls

    // ============================================================================================================          

    let warnForWritesOnPureFunctions =
      let doDecl = function
        | Top.FunctionDecl(fn) as decl when fn.IsPure && fn.Writes <> [] ->
          helper.Error (fn.Token, 9623, "writes specified on a pure function", None)
          decl
        | decl -> decl
      List.map doDecl

    // ============================================================================================================
    
    let pointerCmpWarning self = function
      | Expr.Macro (c, ("_vcc_ptr_eq_pure"|"_vcc_ptr_neq_pure"), [p1; p2]) ->
          match p1.Type, p2.Type with
            | Ptr(t1), Ptr(t2) ->
              if t1 <> t2 then
                helper.Warning (c.Token, 9124, "pointers of different types (" + t1.ToString() + " and " + t2.ToString() + ") are never equal in pure context")
              None
            | _ -> None
      | _ -> None
    
    // ============================================================================================================

    helper.AddTransformer ("warn-begin", TransHelper.DoNothing)
    helper.AddTransformer ("warn-two-state-inv-without-volatile", TransHelper.Decl warnForOldWithoutVolatiles)
    helper.AddTransformer ("warn-unchecked-ghost-loops", TransHelper.Decl warnForUncheckedGhostLoops)
    helper.AddTransformer ("warn-writes-on-pure-functions", TransHelper.Decl warnForWritesOnPureFunctions)
    helper.AddTransformer ("warn-pointer-cmp", TransHelper.Expr pointerCmpWarning)
    helper.AddTransformer ("warn-end", TransHelper.DoNothing)

