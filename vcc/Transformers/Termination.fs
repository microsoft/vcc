//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

namespace Microsoft.Research.Vcc

open Microsoft.Research.Vcc
open Microsoft.Research.Vcc.Util
open Microsoft.Research.Vcc.TransUtil
open Microsoft.Research.Vcc.CAST

module Termination = 

  type CallGraphEntry =
    {
      Functions : GList<Function>
      mutable Level : int
      mutable Visited : bool
      mutable Visiting : bool
      mutable LocVisited : bool
    }

  let checkCallCycles (helper:TransHelper.TransEnv, decls) = 
    let recurses = gdict()
    let rec recRoot (f:Function) =
      match recurses.TryGetValue f.UniqueId with
        | true, v -> recRoot v
        | _ -> f
    let calls = gdict()
    let funs = glist[]
    let specMacros = glist[]
    let buildCallGraph = function
      | Top.FunctionDecl tfn when tfn.DecreasesLevel = 0 && (Normalizer.isSpecMacro tfn || checkTermination helper tfn) ->
        if Normalizer.isSpecMacro tfn then
          specMacros.Add tfn
        else
          funs.Add tfn
        let recur = ref None
        let keepIt = function
          | CallMacro (ec, "\\macro_recursive_with", _, [expr]) ->
            let aux _ = function
              | Macro (_, "get_fnptr", [Call (_, f, _, _)]) ->
                if recurses.ContainsKey tfn.UniqueId then
                  // maybe we should take the union?
                  helper.Error (ec.Token, 9744, "_(recurses_with ...) specified more than once; you can pick any function as representiative of a call group")
                if recRoot f <> tfn then // prevent infinit recursion on cycles
                  recurses.[tfn.UniqueId] <- f 
                true
              | _ -> true
            expr.SelfVisit aux
            false
          | _ -> true
        tfn.Ensures <- tfn.Ensures |> List.filter keepIt

        let body =
          if Normalizer.isSpecMacro tfn then
            Normalizer.specMacroBody tfn
          else tfn.Body

        match body with
          | Some b ->
            let called = ulist()
            let aux _ = function
              | Call (ec, fn, _, _) when not (called.Contains fn) ->
                if checkTermination helper fn || Normalizer.isSpecMacro fn then
                  called.Add fn
                elif fn.IsWellFounded then
                  ()
                else
                  // for expanded spec-macros we should get an error later
                  if not (Normalizer.isSpecMacro tfn) && 
                     not (fn.Name = "malloc" || fn.Name = "free") &&
                     not (fn.Name.StartsWith("\\") && fn.Token.Filename.EndsWith("vccp.h", System.StringComparison.OrdinalIgnoreCase)) then
                    helper.GraveWarning (ec.Token, 9315, "termination checking not enabled for function '" + fn.Name + "'; consider supplying _(decreases ...) clause")
                true
                (*
              | Assert _
              | Assume _
              | Macro (_, "loop_contract", _) -> false 
              *)
              | _ -> true
            b.SelfVisit aux
            calls.[tfn.UniqueId] <- called
          | _ -> ()
      | _ -> ()
    List.iter buildCallGraph decls

    let expandSpec (fn:Function) =
      let visited = gdict()
      let normCalled = ulist()
      let rec visit (f:Function) =
        if visited.ContainsKey f then ()
        else
          visited.[f] <- true
          lookupWithDefault calls (ulist()) fn.UniqueId
            |> Seq.iter (fun g -> 
                 if Normalizer.isSpecMacro g then
                   visit g
                 elif checkTermination helper g then
                   normCalled.Add g)
      visit fn
      calls.[fn.UniqueId] <- normCalled
    specMacros |> Seq.iter expandSpec
    let calls0 = gdict()
    let expandNorm (fn:Function) = 
      let newCalled = ulist()
      lookupWithDefault calls (ulist()) fn.UniqueId
        |> Seq.iter (fun f ->
             if Normalizer.isSpecMacro f then
               newCalled.AddRange calls.[f.UniqueId]
             else
               newCalled.Add f) 
      calls0.[fn.UniqueId] <- newCalled |> Seq.toList
    funs |> Seq.iter expandNorm
    let calls = calls0

    let entries = gdict()
    let entryList = glist[]
    funs |> Seq.iter (fun f ->
      let r = recRoot f
      match entries.TryGetValue r.UniqueId with
        | true, (e:CallGraphEntry) ->
          e.Functions.Add f
          entries.[f.UniqueId] <- e
        | false, _ ->
          let e = 
            {
              Functions = glist [f]
              Level = 1
              Visited = false 
              LocVisited = false 
              Visiting = false
            }
          entries.[r.UniqueId] <- e
          entries.[f.UniqueId] <- e
          entryList.Add e)
    let rec dfs (e:CallGraphEntry) =
      let children = glist[]
      let addCall (f:Function) =
        let entry = entries.[f.UniqueId]
        if not entry.LocVisited then
          entry.LocVisited <- true
          children.Add (entry, f)
      e.Functions |> Seq.iter (fun f -> lookupWithDefault calls [] f.UniqueId |> List.iter addCall)
      children |> Seq.iter (fun (e, _) -> e.LocVisited <- false)
      e.Visited <- true
      let check (ch:CallGraphEntry, f:Function) =
        if ch.Visited then
          if ch.Visiting && ch <> e then
            helper.Error (f.Token, 9743, "function '" + f.Name + "' calls '" + e.Functions.[0].Name + "' recursively, but they are not part of the same call group; please use _(recurses_with ...)")
        else
          dfs ch
      e.Visiting <- true 
      children |> Seq.iter check 
      e.Visiting <- false
      let levels = children |> Seq.map (fun (e, _) -> e.Level)
      if levels |> Seq.isEmpty then ()
      else e.Level <- Seq.max levels + 1
    let processEntry (e:CallGraphEntry) =
      if not e.Visited then dfs e
      e.Functions |> Seq.iter (fun f -> f.DecreasesLevel <- e.Level)
    entryList |> Seq.iter processEntry



  let setDecreasesLevel (helper:TransHelper.TransEnv) decls =
    let aux = function
      | Top.FunctionDecl fn ->
        let checkDecr = function
          | CallMacro (ec, "_vcc_decreases_level", _, [arg]) ->
            helper.Warning (ec.Token, 9126, "_(level ...) annotations have no effect now; use _(recursive_with ...) if required")
            Expr.True
          | e -> e
        fn.Requires <- List.map checkDecr fn.Requires
        let lev =
          if fn.DecreasesLevel <> 0 || checkTermination helper fn then
            fn.DecreasesLevel
          else
            System.Int32.MaxValue
        let assump = Expr.MkAssume (Macro (boolBogusEC(), "decreases_level_is", [mkInt lev]))
        fn.Body <- Option.map (addStmts [assump]) fn.Body
      | _ -> ()
    List.iter aux decls
    decls

  type PureTrCtx =
    {
      InStmt : bool
      SeenAssertFalse : bool
    }

  let turnIntoPureExpression (helper:TransHelper.TransEnv) topType (expr:Expr) =
    let rec aux (ctx:PureTrCtx) bindings (exprs:list<Expr>) =
      let expr, cont = exprs.Head, exprs.Tail
      //System.Console.WriteLine ("doing (cont={0}) e: {1}/{2}", cont.Length, expr, expr.GetType())

      let recExpr e = aux { ctx with InStmt = false } bindings [e]
      let self = aux ctx bindings

      let notsupp kind = 
        helper.Error (expr.Token, 9735, kind + " are not supported when turning statements into expressions")
        Macro ({ bogusEC with Type = topType }, "default", [])

      let valueShouldFollow (ctx:PureTrCtx) f =
        if cont.IsEmpty then
          if not ctx.SeenAssertFalse then
            helper.Error (expr.Token, 9736, "expecting value here")
          Macro ({ bogusEC with Type = topType }, "default", [])
        else
          f cont

      let returnValue () =
        if cont.IsEmpty then
          expr.ApplyToChildren recExpr
        else
          // warn about ignored expression?
          self cont

      match expr with
        // pure expressions
        | Prim _
        | IntLiteral _
        | BoolLiteral _
        | Deref _
        | Dot _
        | Index _
        | Cast _
        | Quant _
        | Result _
        | This _
        | Old _
        | SizeOf _ 
        | UserData _ ->
          returnValue()

        | Ref (_, v) ->
          if Map.containsKey v.UniqueId bindings && cont.IsEmpty then
            Map.find v.UniqueId bindings
          else
            returnValue()

        | Call (ec, fn, _, _) ->
          // TODO check if fn is OK
          returnValue()

        | Pure (_, e)
        | Stmt (_, e) ->
          self (e :: cont)

        | Assert (_, Expr.BoolLiteral (_, false), _) ->
          let ctx = { ctx with SeenAssertFalse = true }
          valueShouldFollow ctx (aux ctx bindings)

        // ignored statements
        | Skip _
        | Label _
        | Assert _
        | Assume _ 
        | Comment _
        | VarDecl _ ->
          valueShouldFollow ctx self

        // errors
        | MemoryWrite _ -> notsupp "state updates"
        | Atomic _ -> notsupp "atomic blocks"
        | Loop _ -> notsupp "loops"
        | Goto _ -> notsupp "gotos"

        | VarWrite (ec, [v], e) ->
          let bindings = Map.add v.UniqueId (recExpr e) bindings
          valueShouldFollow ctx (aux ctx bindings)

        | If (c, None, cond, Block(_, [Assert(_, Macro(_, "_vcc_possibly_unreachable", []), []); VarWrite (_, [tmp], e1)], None),
                               Block(_, [Assert(_, Macro(_, "_vcc_possibly_unreachable", []), []); VarWrite (_, [tmp'], e2)], None))
        | If (c, None, cond, VarWrite (_, [tmp], e1), VarWrite (_, [tmp'], e2)) when tmp = tmp' ->
          let e = Expr.Macro (e1.Common, "ite", [cond; e1; e2])
          let bindings = Map.add tmp.UniqueId (recExpr e) bindings
          valueShouldFollow ctx (aux ctx bindings)

        | If (ec, _, cond, thn, els) ->
          let rec noEffect = function
            | If (_, _, Macro (_, "check_termination", _), _, _) -> true
            | If (_, _, _, thn, els) -> noEffect thn && noEffect els
            | Assert _
            | Assume _ 
            | Comment _
            | Label _ 
            | VarDecl _ -> true
            | Block (_, lst, _) -> List.forall noEffect lst
            | _ -> false
          if noEffect expr then
            self cont
          else
            let thn' = self (thn :: cont)
            let els' = self (els :: cont)
            Macro ({ec with Type = thn'.Type}, "ite", [recExpr cond; thn'; els']) 
 
        | Block (ec, exprs, None) ->
          self (exprs @ cont)

        | Return (ec, Some e) ->
          if not ctx.InStmt then
            helper.Die()
          recExpr e

        | Macro _ ->
          // TODO?
          returnValue()

        | VarWrite _
        | Block _
        | Return _ -> helper.Die()

    let ctx =
      {
        InStmt = true
        SeenAssertFalse = false
      } 
    aux ctx Map.empty [expr]

  let insertTerminationChecks (helper:TransHelper.TransEnv) decls =
    let check (currFn:Function) decrRefs (labels:Dict<_,_>) self e =
      let rec computeCheck tok = function
        | ((s:Expr) :: ss, (c:Expr) :: cc) ->
          match s.Type, c.Type with
            | (MathInteger _ | Integer _), (MathInteger _ | Integer _) ->
              Expr.Macro (boolBogusEC(), "prelude_int_lt_or", [c; s; computeCheck tok (ss, cc)])
            | _ ->
              helper.GraveWarning (tok, 9314, "only integer arguments are currently accepted in _(decreases ...) clauses; consider using \\size(...)")
              Expr.False
        // missing elements are treated as Top, e.g. consider:
        // f(a) = ... f(a-1) ... g(a-1,b) ...
        // g(a,b) = ... g(a,b-1) ... f(a-1) ...
        | (_, []) -> Expr.False
        | ([], _) -> Expr.True 

      let rec justChecks = function
        | Pure (_, e) -> justChecks e

        | Call (ec, fn, tps, args) as e ->
          if fn.IsDatatypeOption then
            []
          elif fn.Name.StartsWith "lambda#" then
            []
          elif fn.DecreasesLevel < currFn.DecreasesLevel then
            []
          elif fn.DecreasesLevel > currFn.DecreasesLevel then
            helper.GraveWarning (e.Token, 9319, 
                                 System.String.Format ("calling function '{0}' (level {1}) from lower-level function ('{2}' at level {3})", 
                                                       fn.Name, fn.DecreasesLevel, currFn.Name, currFn.DecreasesLevel))
            []
          elif checkTermination helper fn then
            let subst = fn.CallSubst args
            let assigns, callVariants = 
              fn.Variants 
                |> List.map (fun e -> e.Subst subst)
                |> cacheMultiple helper lateCache "callDecr" VarKind.SpecLocal
            let check = computeCheck e.Token (decrRefs, callVariants)
            if check = Expr.False then
              helper.GraveWarning (e.Token, 9321, "no measure to decrease when calling '" + e.ToString() + "'; consider using _(level ...)")
              assigns
            else
              let check = check.WithCommon (afmte 8029 "the call '{0}' might not terminate" [e])
              let check = Expr.MkAssert check
              assigns @ [check]
          else
            helper.GraveWarning (e.Token, 9315, "termination checking not enabled for function '" + fn.Name + "'; consider supplying _(decreases ...) clause")
            []
        | _ -> helper.Die()

      let inferDecr (body:Expr) =
        let rec hasBreak = function
          | Block (_, lst, _) -> List.exists hasBreak lst
          | Goto (_, id) when id.Name.StartsWith "#break" -> true
          | _ -> false
        let res = ref None 
        let rec lookForCondition = function
          | e when (!res).IsSome -> e
          | If (_, _, Prim (ec, Op (("<"|">"|"<="|">="|"!="), _), [a; b]), th, el) as e 
            when (hasBreak th || hasBreak el) && a.Type.IsNumber && b.Type.IsNumber ->
            let a = turnIntoPureExpression helper a.Type a
            let b = turnIntoPureExpression helper b.Type b
            res := Some (Macro ({ ec with Type = Type.MathInteger MathIntKind.Signed }, "prelude_int_distance", [a; b]))
            e
          | e ->
            e.ApplyToChildren lookForCondition
        body.ApplyToChildren lookForCondition |> ignore
        match !res with
          | Some expr -> [expr]
          | _ -> []
     
      match e with
      | Call (_, { Name = "_vcc_stack_alloc" }, _, _) ->
        None

      | CallMacro (_, name, _, _) when helper.PureCallSignature name |> Option.isSome ->
        None

      | Call (ec, fn, tps, args) as e ->
        match justChecks e with
          | [] -> None
          | lst ->
            Some (Expr.MkBlock (lst @ [Call (ec, fn, tps, List.map self args)]))

      | Loop (ec, inv, wr, decr, body) ->
        let decr = 
          if decr <> [] then decr
          else inferDecr body
        if decr = [] then 
          helper.GraveWarning (ec.Token, 9323, "failed to infer _(decreases ...) clause for the loop; please supply one")
          Some (Loop (ec, inv, wr, decr, self body))
        else
          let body = self body
          let assigns0, refs0 = cacheMultiple helper lateCacheRef "loopDecrBeg" VarKind.SpecLocal decr
          let assigns1, refs1 = cacheMultiple helper lateCacheRef "loopDecrEnd" VarKind.SpecLocal decr
          let check = computeCheck ec.Token (refs0, refs1)
          let check = check.WithCommon (afmte 8033 "the loop fails to decrease termination measure" [e])
          let body = Expr.MkBlock (assigns0 @ [body] @ assigns1 @ [Expr.MkAssert check])
          Some (Loop (ec, inv, wr, decr, body))

      | Label (_, { Name = n }) ->
        labels.[n] <- true
        None

      | Goto (ec, { Name = n }) ->
        if labels.ContainsKey n then
          helper.GraveWarning (e.Token, 9316, "backward gotos are currently not supported in termination checking")
        Some e

      | Assert _
      | Assume _ -> 
        // skip checking inside
        Some e 

      | Macro (_, "skip_termination_check", [e]) ->
        Some e

      | Block (_, _, Some _) ->
        helper.Die() // these should be gone, right?
        None

      | Macro (_, "dt_testhd", _) ->
        None

      | Macro (_, name, _) when name.StartsWith "DP#" ->
        None

      | Macro (_, ("rec_update"|"rec_fetch"|"map_zero"|"rec_zero"|"havoc_locals"|"_vcc_rec_eq"|"map_get"
                    |"vs_fetch"|"ite"|"size"|"check_termination"|"map_updated"|"stackframe"|"map_eq"
                    |"ignore_me"|"null"|"by_claim"|"vs_updated"|"state"|"ghost_atomic"
                    |"bv_update"|"bv_extract_unsigned"|"float_literal"|"_vcc_by_claim"
                    |"rec_update_bv"|"prestate"|"_vcc_ptr_eq_pure"|"bogus"
                    |"_vcc_ptr_eq_null"|"_vcc_ptr_neq_null"), _) ->
        None

      | Macro (_, ("_vcc_static_wrap"|"_vcc_static_unwrap"|"havoc"|"_vcc_unblobify"|"_vcc_blobify"
                    |"_vcc_wrap"|"_vcc_unwrap"|"_vcc_static_wrap_non_owns"
                    |"_vcc_wrap_set"|"_vcc_unwrap_set"
                    |"_vcc_havoc_others"|"_vcc_unwrap_check"|"inlined_atomic"
                    |"unclaim"|"claim"|"begin_update"|"upgrade_claim"), _) ->
        None

      | Macro (_, s, _) when s.StartsWith "prelude_" || s.StartsWith "unchecked_" -> 
        None

      | Macro (ec, s, args) as e ->
        helper.GraveWarning (e.Token, 9317, "macro '" + s + "' is not supported in termination checking")
        Some e

      | _ -> None

    let computeAllDefReads decls =
      let didSomething = ref true
      let computeDefReads = function
        | Top.FunctionDecl fn as decl when fn.CustomAttr |> hasCustomAttr AttrDefinition ->
          match fn.Reads, fn.Body with
            | [], Some b ->
              fn.Reads <- computeReads b
              if fn.Reads <> [] then
                didSomething := true
            | _ -> ()
        | _ -> ()
      while !didSomething do
        didSomething := false
        List.iter computeDefReads decls
   
    let setDefaultVariants = function
      | Top.FunctionDecl fn as decl when checkTermination helper fn ->
          if fn.Variants = [] then
            let aux acc (v:Variable) =
              let rf = Ref ({ bogusEC with Type = v.Type }, v)
              let sz = Macro ({ bogusEC with Type = Type.MathInteger Signed }, "size", [rf])
              match v.Type with
                | Type.MathInteger _
                | Type.Integer _ ->
                  rf :: acc
                | Type.Ref td when td.IsDataType || td.IsRecord ->
                  sz :: acc
                | _ -> acc
            fn.Variants <- fn.Parameters |> List.fold aux [] |> List.rev
      | _ -> ()
   
    let genDefAxiom = function
      | Top.FunctionDecl fn as decl when fn.CustomAttr |> hasCustomAttr AttrDefinition ->
        match fn.Body with
          | None ->
            helper.GraveWarning (fn.Token, 9318, "definition functions need to have body")
            [decl]
          | _ when fn.RetType = Void -> [decl]
          | Some body ->
            fn.DefExpansionLevel <- helper.Options.DefExpansionLevel
            let expr = turnIntoPureExpression helper fn.RetType body
            let axiomFor k u =
              let addLimits self = function
                | Call (ec, f, targs, args) as e when f.DecreasesLevel = fn.DecreasesLevel ->
                  Some (Macro (ec, "limited#" + k.ToString(), [Call (ec, f, targs, List.map self args)]))
                | _ -> None
              let expr = expr.SelfMap addLimits
              if fn.Reads = [] then
                fn.Reads <- computeReads expr
              let suff = "#" + helper.UniqueId().ToString() 
              let vars, repl = Variable.UniqueCopies (fun v -> { v with Name = v.Name + suff ; Kind = QuantBound }) fn.Parameters
              let ec t = { body.Common with Type = t }
              let app = Call (ec fn.RetType, fn, [], vars |> List.map (fun v -> Expr.Ref (ec v.Type, v)))
              let app = Macro (app.Common, "limited#" + u.ToString(), [app])
              let eq = Prim (ec Type.Bool, Op ("==", Processed), [app; repl expr])
              let preconds = fn.Requires |> multiAnd |> repl
              let impl = Prim (ec Type.Bool, Op ("==>", Processed), [preconds; eq])
              let qd = 
                {
                  Body = eq
                  Variables = vars
                  Kind = Forall
                  Condition = None
                  Triggers = [[app]]
                  Weight = "c-def-function"
                }
              Top.Axiom (if vars = [] then eq else Quant (ec Type.Bool, qd))
            let rec genAxiom k =
              if k <= 0 then []
              else axiomFor k (k-1) :: genAxiom (k - 1)
            let axioms = 
              if fn.DefExpansionLevel = 0 then [axiomFor 0 0]
              else genAxiom fn.DefExpansionLevel
            decl :: axioms
      | decl -> [decl]
   
    let warnForIgnoredDecreases (fn : Function) self = function
      | Loop(_, _, _, decreases :: _, _) -> helper.GraveWarning(decreases.Token, 9324, "_(decreases ...) is ignored because function '" + fn.Name + "' is not checked for termination"); true
      | _ -> true

    let genChecks = function
      | Top.FunctionDecl ({ Body = Some body } as fn) when checkTermination helper fn ->
        let assigns, refs = cacheMultiple helper lateCacheRef "thisDecr" VarKind.SpecLocal fn.Variants 
        let body = Expr.MkBlock (assigns @ [body])
        let body = body.SelfMap (check fn refs (gdict()))
        fn.Body <- Some body
      | Top.FunctionDecl ({ Body = Some body } as fn) ->
        body.SelfVisit(warnForIgnoredDecreases fn)
        ()
      | decl -> ()

    computeAllDefReads decls
    List.iter setDefaultVariants decls
    let decls = List.collect genDefAxiom decls
    List.iter genChecks decls
    decls

  let terminationCheckingPlaceholder (helper:TransHelper.TransEnv) decls =
    let rec skipChecks = function
      | Expr.Call _ as e ->
        Expr.Macro (e.Common, "skip_termination_check", [Expr.Pure (e.Common, e.ApplyToChildren skipChecks)])
      | e ->
        e.ApplyToChildren skipChecks
       
    let rec checks = function
      | Expr.Quant (ec, qd) as res ->
        let suff = "#" + helper.UniqueId().ToString() 
        let vars, repl = Variable.UniqueCopies (fun v -> { v with Name = v.Name + suff ; Kind = SpecLocal }) qd.Variables
        let decls = vars |> List.map (fun v -> Expr.VarDecl (bogusEC, v, []))
        match qd.Condition with
          | Some e ->
            let e = repl e
            let pref0 = checks e
            let pref1 = checks (repl qd.Body)
            decls @ pref0 @ [Expr.If (bogusEC, None, e, Expr.MkBlock pref1, Skip(bogusEC))]
          | None ->
            let pref1 = checks (repl qd.Body)
            decls @ pref1 
      | Expr.Macro (ec, "ite", [cond; a; b]) ->
        checks cond @ [Expr.If (bogusEC, None, skipChecks cond, Expr.MkBlock (checks a), Expr.MkBlock (checks b))]
      | Expr.Call (ec, fn, targs, args) as e ->
        (args |> List.map checks |> List.concat) @ [e]

      // just the common stuff, so we know when we run into it
      | Expr.Assert _
      | Expr.Assume _
      | Expr.VarWrite _
      | Expr.Block _ 
      | Expr.Return _
      | Expr.MemoryWrite _
      | Expr.Goto _
      | Expr.Loop _ 
      | Expr.Stmt _ as e ->
        helper.Oops (e.Token, "expression not supported when checking termination of a binder: " + e.ToString())
        []

      | e ->
        let acc = glist[]
        let f e =
          acc.AddRange (checks e)
          e
        e.ApplyToChildren f |> ignore
        acc |> Seq.toList
      
    let termWrapper checks =
      Expr.If (voidBogusEC(), None, Expr.Macro (boolBogusEC(), "check_termination", [mkInt (helper.UniqueId())]), Expr.MkBlock(checks @ [Expr.MkAssume (Expr.False)]), Skip(bogusEC))
     
    let rec addChecks = function
      | Quant _ as q ->
        Expr.MkBlock [termWrapper (checks q); skipChecks q]
      | Macro (_, "loop_contract", _) 
      | Assert _
      | Assume _ as e -> e
      | e ->
        e.ApplyToChildren addChecks
       
    let aux = function
      | Top.FunctionDecl fn as decl when checkTermination helper fn ->
        fn.Body <- fn.Body |> Option.map addChecks
      | _ -> ()

    List.iter aux decls
    decls

  let init (helper:TransHelper.TransEnv) =

    helper.AddTransformerAfter ("termination-compute-cycles", TransHelper.Decl (fun decls -> checkCallCycles (helper, decls); decls), "begin")
    helper.AddTransformer ("termination-set-level", TransHelper.Decl (setDecreasesLevel helper))
    helper.AddTransformer ("termination-add-checks", TransHelper.Decl (insertTerminationChecks helper))
    helper.AddTransformerBefore ("termination-insert-placeholders", TransHelper.Decl (terminationCheckingPlaceholder helper), "desugar-lambdas")
