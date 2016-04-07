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
 
 module TransSideChecks =
  
 
  // ============================================================================================================
  
  let prestate = Macro ({ bogusEC with Type = Type.MathState }, "prestate", [])
  
  let admChecks helper p =
    AddChecks.invariantCheck helper (fun e -> not (CAST.isLemmaInv e)) (fun _ -> true) 8012 "is not admissible" prestate (mkRef p)

  let lemmaChecks helper p =
    AddChecks.invariantCheck helper CAST.isLemmaInv (fun _ -> true) 8033 "is not a lemma" prestate (mkRef p)
  
  let unwrapChecks helper p =
    AddChecks.invariantCheck helper (fun _ -> true) (fun e -> not (AddChecks.isOnUnwrap e)) 8018 "forbids unwrapping" prestate (mkRef p)

  let stuttChecks helper p =    
    let stutteringCheck (inv:Expr) =
      let seenOld = ref false
      let replaceThisOld self = function 
        | Expr.This _ -> Some (mkRef p)
        | Expr.Old (_, Macro (_, "prestate", []), e) -> 
          seenOld := true
          Some (self e)
        | _ -> None
      let inv = inv.SelfMap replaceThisOld
      if !seenOld then
        [Expr.Macro(afmte 8013 "invariant({0}) is not admissible (stuttering)" [inv], "token_holder", [inv])]
            else []
    let td = match p.Type with Ptr (Type.Ref td) -> td | _ -> die()
    List.map stutteringCheck (AddChecks.invariantsOf td (fun _ -> true)) |> List.concat

  let addDefaultAdmissibilityChecks (explicitAdm:Dict<_,_>) (helper:TransHelper.TransEnv) =
    let handleDecl = function
      | Top.TypeDecl td as decl when not (hasCustomAttr AttrNoAdmissibility td.CustomAttr) ->
        let rec isTrivialInvariant = function
          | CallMacro(_, "_vcc_typed2", _, [_;  This(_)]) -> true
          | CallMacro(_, "_vcc_set_eq", _, [CallMacro(_, "_vcc_owns", _, [_; This(_)]); CallMacro(_, "_vcc_set_empty", _, [])]) -> true
          | CallMacro(_, "_vcc_inv_is_owner_approved", _, _) -> true
          | CallMacro(_, "labeled_invariant", _, [_; inv]) -> isTrivialInvariant inv
          | _ -> false
        
        if List.forall isTrivialInvariant (td.Invariants) then [decl]
        else              
          let parm = Variable.CreateUnique "_this_"  (Type.MkPtrToStruct td) Parameter
          let (explicitAdm, explicitUnwrap, explicitStutt) =
            match explicitAdm.TryGetValue td with
              | true, r -> r
              | _ -> (false, false, false)
          let ec = { bogusEC with Token = td.Token; Type = Type.Void }
          let isStutt = Macro (boolBogusEC(), "_vcc_is_stuttering_check", [])
          let isUnwrap = Macro (boolBogusEC(), "_vcc_is_unwrap_check", [])
          let isAdm = Macro (boolBogusEC(), "_vcc_is_admissibility_check", [])
          let assume name = Expr.MkAssume (Macro (boolBogusEC(), name, [mkRef parm]))
          // insert after havoc to make sure there is :captureState generated there
          let assertTrue = Expr.MkAssert (Expr.BoolLiteral ({ ec with Type = Type.Bool }, true)) 
          let unwrapBody = Expr.MkBlock [Expr.MkAssume (mkNot isStutt);
                                         assume "_vcc_unwrap_check_pre";
                                         Macro (ec, "_vcc_unwrap_check", [mkRef parm]);
                                         assertTrue]
          let admBody    = Expr.MkBlock ( if explicitAdm then 
                                            [ assume "_vcc_stuttering_pre" ]
                                          else 
                                            [ If (ec, None, isAdm, assume "_vcc_admissibility_pre", assume "_vcc_stuttering_pre");
                                            Macro (ec, "_vcc_havoc_others", [mkRef parm; typeExpr (Type.Ref td)]);
                                            assertTrue;
                                            Expr.MkAssume (mkImpl isStutt (Macro (boolBogusEC(), "_vcc_inv2", [mkRef parm]))) ])
          let assumeNot cond name body =
            if cond then Expr.MkBlock [Expr.MkAssume (mkNot name); body]
            else body
            
          let body = 
            if explicitUnwrap then admBody
            else If (ec, None, isUnwrap, unwrapBody, admBody)
          let body = 
              body |>
                assumeNot explicitAdm isAdm |>
                assumeNot explicitStutt isStutt |>
                assumeNot explicitUnwrap isUnwrap
          let body = Expr.MkBlock [assume "_vcc_admissibility_start"; body]
          let post = 
            List.map (mkImpl isAdm) (admChecks helper parm) @
            List.map (mkImpl isStutt) (stuttChecks helper parm) @
            List.map (mkImpl isUnwrap) (unwrapChecks helper parm) @
            List.map (mkImpl isAdm) (lemmaChecks helper parm)
          
              //Expr.Assert( { afmte 8514 "invariant({0}) holds (in admissibility check)" [expr] with Type = Type.Void }, expr )
          let check = 
            { Function.Empty() with
                Token = td.Token
                IsSpec = true  
                Name = td.Name + "#adm"
                Parameters = [parm]
                Ensures = post
                Variants = [ mkInt 0 ]
                CustomAttr = VccAttr(AttrIsAdmissibility, "") :: (inheritedAttrs td.CustomAttr)
                Body = Some body
                IsProcessed = true }
          [decl; Top.FunctionDecl check]
      | decl -> [decl]
    List.map handleDecl >> List.concat
 
  let handleCustomAdmissibilityChecks (explicitAdm:Dict<_,_>) (helper:TransHelper.TransEnv) decls =
    let errCheck (f:Function) cb =
      match f.Parameters with
        | [{ Type = Ptr (Type.Ref td) } as p] ->
          if f.Requires <> [] || f.Ensures <> [] || f.Writes <> [] || f.Variants <> [] then
            helper.Error (f.Token, 9624, "custom admissibility checks are not allowed to have explicit requires/ensures/writes", None)
          if f.Body.IsNone then
            helper.Error (f.Token, 9644, "the admissibility check is required to have a body", None)
          
          cb td p
              
        | _ -> helper.Error (f.Token, 9622, "the admissibility check function expects a single pointer parameter", None)
    
    for d in decls do    
      match d with
        | Top.FunctionDecl f when hasCustomAttr AttrIsAdmissibility f.CustomAttr ->
          errCheck f (fun td p ->
            match explicitAdm.TryGetValue td with
              | true, (_, u, s) -> explicitAdm.[td] <- (true, u, s)
              | _ -> explicitAdm.[td] <- (true, false, false)
            let pre  = Expr.Macro (afmtt f.Token 8001 "custom admissibility was called" [], 
                                 "_vcc_admissibility_pre", [mkRef p])
            let pre2 = Expr.Macro (afmtt f.Token 8001 "custom admissibility was called" [], 
                                 "_vcc_is_admissibility_check", [])
            let good = Expr.Macro (afmtt f.Token 8002 "state was altered after havoc_others()" [], 
                                 "_vcc_good_for_post_admissibility", [])
            f.Requires <- pre2 :: pre :: f.Requires
            f.Ensures <- [good] @ admChecks helper p @ f.Ensures
            f.Variants <- [ mkInt 0 ])
            
        | Top.FunctionDecl f when hasCustomAttr "is_unwrap_check" f.CustomAttr ->
          errCheck f (fun td p ->
            match explicitAdm.TryGetValue td with
              | true, (a, _, s) -> explicitAdm.[td] <- (a, true, s)
              | _ -> explicitAdm.[td] <- (false, true, false)
            let pre  = Expr.Macro (afmtt f.Token 8001 "custom unwrap check was called" [], 
                                 "_vcc_unwrap_check_pre", [mkRef p])
            let good = Expr.Macro (afmtt f.Token 8002 "state was altered after unwrap_check()" [], 
                                 "_vcc_good_for_post_can_unwrap", [])
            f.Requires <- pre :: f.Requires
            f.Ensures <- good :: unwrapChecks helper p @ f.Ensures)
            
        | _ -> ()
    decls
  
  let handleAdmissibilityChecks helper decls =
    let expl = gdict()
    decls |>
      handleCustomAdmissibilityChecks expl helper |>
      addDefaultAdmissibilityChecks expl helper
    
  // ============================================================================================================

  type PathElt =
    | Field of Field
    | Bit of int
    
  let (|QuantLet|_|) = function
    | Quant (c, ({ Kind = Exists; Variables = [v] } as qd)) ->
      let isV = function
        | Expr.Ref (_, v') when v = v' -> true
        | _ -> false
      let qd = 
        match qd.Condition with
          | Some (Expr.BoolLiteral _)
          | None ->
            match qd.Body with
              | Macro (_, "ite", [a; b; EFalse])
              | Prim (_, Op ("&&", _), [a; b]) -> 
                {qd with Condition = Some a; Body = b}
              | _ -> qd
          | Some _ -> qd
      match qd.Condition with
        | Some (CallMacro (_, "_vcc_rec_eq", _, [e1; e2]))
        | Some (Prim (_, Op ("==", _), [e1; e2])) ->
          if isV e1 && not (e2.HasSubexpr isV) then
            Some (c, qd)
          else None
        | _ -> None
    | _ ->
      None
    
  let usesRes (expr:Expr) =
    expr.HasSubexpr (function Result (_) -> true | _ -> false)          
      
  let checkPurePostconditionForm (helper:TransHelper.TransEnv) = function
    | Top.FunctionDecl f when f.IsPure && f.Body.IsNone && not f.IsWellFounded ->
      let paths = gdict()
      
      let rec checkOne = function
        | QuantLet (c, ({ Condition = Some cond } as qd)) as expr ->
          if usesRes cond then
            helper.GraveWarning (f.Token, 9312, "'\\result' cannot be used in let binding in a pure function definition")
            expr
          else
            Quant (c, { qd with Body = checkOne qd.Body })
          
        | Macro (c0, ("_vcc_ptr_eq"|"_vcc_ptr_eq_pure" as name), [Cast ({ Type = Ptr _ } as c1, _, (Result ({ Type = Ptr _ }) as res)); e2]) ->
          checkOne (Macro (c0, name, [res; e2]))
          
        // push the cast to Bool around
        | Prim (c0, (Op ("==", _) as op), [Cast ({ Type = Integer _ } as c1, _, (Result ({ Type = Bool }) as res)); e2]) ->
          checkOne (Prim (c0, op, [res; Cast ({ e2.Common with Type = Bool }, Unchecked, e2)]))
          
        | CallMacro (c, ("_vcc_ptr_eq"|"_vcc_rec_eq"|"_vcc_ptr_eq_pure"|"map_eq"), _, [e1; e2])
        | Prim (c, Op ("==", _), [e1; e2]) as post ->
          let res, def = 
            if usesRes e2 then e2, e1
            else e1, e2
          let round = ref None
          if not (usesRes res) then
            helper.GraveWarning (post.Token, 9305, "'\\result' does not occur in one of a pure function postconditions")
          elif usesRes def then
            helper.GraveWarning (f.Token, 9306, "'\\result' cannot be used recursively in a pure function definition")
          else
            let gave = ref false
            let rec collect aux = function
              | CallMacro (_, ("bv_extract_signed"|"bv_extract_unsigned" as name), _, [e; _; Expr.IntLiteral (_, from); Expr.IntLiteral (_, to_)]) ->
                if aux <> [] then die()
                let width = (int)(to_ - from)
                let round_name = if name.Contains "unsigned" then "unchecked_ubits" else "unchecked_sbits"
                round := Some (fun (e:Expr) -> Macro (e.Common, round_name, [mkInt width; e]))
                match collect aux e with
                  | [lst] -> [for x in (int)from .. (int)to_ - 1 -> Bit x :: lst]
                  | _ -> die()
              | CallMacro (_, "vs_fetch", _, [e]) -> collect aux e
              | CallMacro (_, "rec_fetch", _, [e; Expr.UserData (_, (:? Field as f)) ]) -> collect (Field f :: aux) e
              | Result (_) -> [List.rev aux]
              | Dot (_, e, f) -> collect (Field f :: aux) e
              | e ->
                gave := true
                helper.GraveWarning (post.Token, 9307, "form of a pure function postcondition is neither '\\result == ...' nor '\\result.x.y.z == ...' (it is: " + e.ToString() + ")")
                [List.rev aux]
            let handlePath path =
              if not (paths.ContainsKey path) || !gave then
                paths.[path] <- res
              else
                gave := true
                helper.GraveWarning (post.Token, 9309, "value of '" + res.Token.Value + "' was already defined in this pure function contract (as '" + paths.[path].Token.Value + "')")
            collect [] res |> List.iter handlePath
          let post =
            match res.Type with
              | Type.MathInteger MathIntKind.Unsigned
              | Type.Integer _ -> 
                let f = 
                  match !round with
                    | Some f -> f
                    | None -> fun (def:Expr) -> Macro ({ def.Common with Type = res.Type }, "unchecked_" + intSuffix res.Type, [def])
                Prim (c, Op ("==", Processed), [res; f def])
              | _ -> post
          post
        | expr ->
          helper.GraveWarning (f.Token, 9310, "a non-equality postcondition in a pure function (not _(ensures \\result == ...))")
          expr
          
      let freebies, normals = f.Ensures |> List.partition (function CallMacro (_, "_vcc_assume", _, _) -> true | _ -> false)
      f.Ensures <- freebies @ (normals |> List.map splitConjunction |> List.concat |> List.map checkOne)
      
      let gave = ref false
      let rec checkSub tok l =
        if not !gave && paths.ContainsKey l then
          gave := true
          helper.GraveWarning (tok, 9311, "value of '" + tok.Value + "' was already defined in this pure function contract (as '" + paths.[l].Token.Value + "')")
        else
          match l with
            | _ :: xs -> checkSub tok xs
            | [] -> ()
                          
      for p in paths.Keys do
        if p <> [] then          
          checkSub paths.[p].Token p.Tail
          
    | _ -> ()
  
    
  let addReadsChecks (helper:TransHelper.TransEnv) decls =
    let calls = new Dict<_,_>()
    
    let readChecks = new Dict<_,_>()
    let revReadChecks = new Dict<_,_>()
    
    let doDecl = function
      | Top.FunctionDecl f as decl ->
        for a in f.CustomAttr do
          match a with
            | ReadsCheck (name) ->
              let add_rev () =
                if revReadChecks.ContainsKey f then
                  helper.Error (f.Token, 9639, "function '" + f.Name + "' pretends to be several read checks at once", None)
                else
                  revReadChecks.[f] <- name
              match readChecks.TryGetValue name with
                | true, f' when f = f' -> ()
                | true, _ -> 
                  helper.Warning (f.Token, 9105, "reads check for '" + name.Name + "' specified multiple times")
                  helper.Warning ((readChecks.[name]:Function).Token, 9105, "(this is the first one)")
                  add_rev ()
                | _ ->
                  readChecks.[name] <- f
                  add_rev ()
            | _ -> ()
        let fns = new HashSet<_>()
        let mycalls = ref []
        let check self = function
          | Call (_, fn, _, _) ->
            if fns.Add fn then mycalls := fn :: !mycalls
            true
          | _ -> true
        [decl] |> deepVisitExpressions check
        calls.[f] <- !mycalls
      | _ -> ()        
    
    let transCalls = new Dict<_,_>()
    let synteticReadChecks = ref []
    
    // Given a pointer to a struct/union expression, construct
    // expressions that are certainly in the owns set (this is a heuristics of course)
    let owns (expr:Expr) =
      match expr.Type with
        | Ptr (Type.Ref { Kind = Struct|Union; Invariants = invs }) ->
          let possibly = function
            | Macro (_, "keeps", [This _; p])
            | Macro (_, ("_vcc_set_in"|"_vcc_set_in0"), [p; Macro (_, "_vcc_owns", [This _])]) ->
              let repl self = function
                | This _ -> Some expr
                | _ -> None
              Some (p.SelfMap repl)
            | _ -> None
          invs |> List.map splitConjunction |> List.concat |> revMapSome possibly
        | _ -> []
    
    let addReadCheck (f:Function) =
      if readChecks.ContainsKey f then ()
      // if it's stateless then we have a separate check
      else if f.IsStateless then ()
      else if f.RetType = Type.Void then ()
      else if hasCustomAttr "no_reads_check" f.CustomAttr then ()
      // no point in checking
      else if List.exists (function Macro (_, "_vcc_set_universe", []) -> true | _ -> false) f.Reads then ()
      else
        let body =
          let tok = { bogusEC with Token = f.Token }
          Expr.MkBlock [Stmt (tok, Macro (tok, "_vcc_reads_havoc", []));
                        Return (tok, None)]
        let rc =
          { Function.Empty() with
              Token = f.Token
              IsSpec = true  
              Name = f.Name + "#reads"
              CustomAttr = ReadsCheck f :: inheritedAttrs f.CustomAttr
              Body = Some body
              IsProcessed = true }
        let decl = Top.FunctionDecl rc
        revReadChecks.[rc] <- f
        synteticReadChecks := decl :: !synteticReadChecks
                
    let checkForCycles = function
      | Top.FunctionDecl f when f.IsPure ->
        addReadCheck f
        let trans = new HashSet<_>()
        let allCalled = ref []
        let error = ref []
        let rec add path g =
          if f = g then error := g :: path
          elif trans.Add g then
            allCalled := g :: !allCalled
            List.iter (add (g::path)) calls.[g]
            
        for g in calls.[f] do
          if g.IsPure then
            if g.IsWellFounded then
              // these are checked for termination, and cannot call ordinary pure functions
              ()
            else
              add [f] g
          else
            helper.Error (f.Token, 9637, "the pure function '" + f.Name + "' calls '" + g.Name + "' which is not pure", Some(g.Token))
        if !error <> [] then
          helper.GraveWarning (f.Token, 9303, "cycle in pure function calls: " + (String.concat " -> " (_list_rev_map (fun (f:Function) -> f.Name) !error)))            
        transCalls.Add (f, !allCalled)
      | _ -> ()


    let handleReadsCheck = function
      | Top.FunctionDecl rd_f when revReadChecks.ContainsKey rd_f ->
        let f = revReadChecks.[rd_f]
        if rd_f.Requires <> [] || rd_f.Writes <> [] || rd_f.Ensures <> [] then
          helper.Error (rd_f.Token, 9640, "the reads check cannot specify additional contract", None)
        if rd_f.Parameters.Length <> f.Parameters.Length then
          if rd_f.Parameters <> [] then
            helper.Error (rd_f.Token, 9641, "the reads check and the function checked have different number of parameters", Some(f.Token))
          rd_f.Parameters <- f.Parameters |> List.map (fun p -> { p with Name = p.Name })
        let subst = new Dict<_,_>()
        let addSubst (orig:Variable) (rdchk:Variable) =
          if orig.Type <> rdchk.Type then
            helper.Error (rd_f.Token, 9642, "the reads check and function checked differ on type of parameter '" + rdchk.Name + "'", Some(f.Token))
          subst.Add (orig, rdchk)
        List.iter2 addSubst f.Parameters rd_f.Parameters
        rd_f.Requires <- [Macro (afmtt rd_f.Token 8005 "intercepted call to reads check" [], "_vcc_reads_check_pre", [])]
        let good = Expr.Macro (afmtt rd_f.Token 8006 "state was altered after reads_havoc()" [], 
                               "_vcc_reads_check_post", [])
        rd_f.Ensures <- [good]
        let mkTok name = afmtt rd_f.Token 8007 "the value of '{0}' changed (in reads check of '{1}')" [name; f.Name]
        let ftok = { bogusEC with Type = f.RetType }
        let fcall = Call (ftok, f, [], List.map mkRef rd_f.Parameters)
        let rec cmp name tp (expr:Expr) =
          match tp with
            | Type.Ref ({ Name = "struct"; Parent = Some td})
            | Type.Ref ({ Kind = Struct | Union } as td) ->
              for fld in td.Fields do
                let dot = Dot(ftok, expr, fld)
                let deref =
                  if fld.Type.IsComposite then dot
                  else Macro ({ ftok with Type = fld.Type }, "vs_fetch", [dot])
                cmp (name + "." + fld.Name) fld.Type deref
            | _ -> 
              rd_f.Ensures <- Prim (mkTok name, Op ("==",Processed), [mkOld ftok "prestate" expr; expr]) :: rd_f.Ensures
        cmp "result" f.RetType fcall
        
        let subst self = function
          | Expr.Ref (c, v) when subst.ContainsKey v ->
            Some (Expr.Ref (c, subst.[v]))
          | _ -> None
        let subst (e:Expr) = e.SelfMap subst

        let ranges = f.InParameters |> List.map (fun p -> Expr.Macro (boolBogusEC(), "in_int_range", [Expr.Ref ({ bogusEC with Type = p.Type }, p)]))
        let preconds = (f.Requires @ ranges) |> List.map( function | Macro(_, "_vcc_assume", [e]) -> e | e -> e)  |> List.map (fun e -> Expr.MkAssume (subst e)) 
        let fixupHavocOthers self = function
          | Stmt (_, CallMacro (ec, "_vcc_reads_havoc", _, [])) as call ->
            let isSame (expr:Expr) =
              match expr.Type with
                | Ptr Void
                | ObjectT ->
                  helper.Error (expr.Token, 9647, "void* and \\object are not supported in reads clauses", None)
                  Skip({expr.Common with Type = Type.Void})
                | Ptr _ ->
                  Expr.MkAssume (Macro (boolBogusEC(), "reads_same", [subst expr]))
                | t when t.IsPtrSet ->
                  match expr with
                    | Macro(_, "_vcc_set_empty", _) -> Skip({expr.Common with Type = Type.Void})
                    | Macro(_, "_vcc_array_range", args) ->
                      let setIn = Expr.Macro(boolBogusEC(), "reads_same_arr", args)
                      Expr.MkAssume setIn
                    | _ -> helper.Error (expr.Token, 9648, "unsupported pointer set in reads clauses", None)
                           Skip({expr.Common with Type = Type.Void})
                | _ ->
                  helper.Error (expr.Token, 9648, "non-pointers are not supported in reads clauses", None)
                  Skip({expr.Common with Type = Type.Void})
            Some (Expr.MkBlock ([Macro (ec, "_vcc_reads_havoc", [])] @ List.map isSame f.Reads @ preconds))
          | _ -> None
        let can_frame f =
          Expr.MkAssume (Expr.Macro (boolBogusEC(), "can_use_frame_axiom_of", [Expr.Call (bogusEC, f, [], [])]))
        let ptrReads = f.Reads |> List.filter (fun e -> match e.Type with Ptr (Type.Ref { Kind = (Struct|Union) }) -> true | _ -> false)
        let inDomain (expr:Expr) =
          let ownsPtrs = ptrReads |> List.filter (fun e -> e <> expr) |> List.map owns |> List.concat
          let inDom e = 
            let eq (x:Expr) =
              if expr.Type = x.Type then mkEq expr x
              else Expr.False
            let final = Macro (boolBogusEC(), "_vcc_in_domain", [e; subst expr])
            ownsPtrs |> List.map eq |> List.fold mkOr final |> Expr.MkAssume
          (subst expr :: owns expr) |> List.map inDom
        match rd_f.Body with
          | Some b -> 
            let can_frame = List.map can_frame (List.filter (fun fn -> fn.RetType <> Type.Void) transCalls.[f]) @ (List.map inDomain ptrReads |> List.concat)
            rd_f.Body <- Some (Expr.MkBlock (preconds @ can_frame @ b.SelfMap fixupHavocOthers :: []))
          | None -> helper.Error (rd_f.Token, 9646, "the reads check is required to have a body", None)
          
      | _ -> ()
        
    List.iter doDecl decls
    List.iter checkForCycles decls
    List.iter (checkPurePostconditionForm helper) decls
    let decls = decls @ !synteticReadChecks
    List.iter handleReadsCheck decls
    decls

  // ============================================================================================================
