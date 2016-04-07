//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

module Microsoft.Research.Vcc.NewSyntax

open Microsoft.Research.Vcc
open Microsoft.Research.Vcc.TransUtil
open Microsoft.Research.Vcc.Util
open Microsoft.Research.Vcc.CAST

let init (helper:TransHelper.TransEnv) =

  let normalizeNewSyntax =  

    let newToOldFn = Map.ofList [ 
                                  "\\at",                  "_vcc_in_state"
                                  "\\now",                 "_vcc_current_state"
                                  "\\mine",                "_vcc_keeps"
                                  "\\embedding",           "_vcc_emb"
                                  "\\simple_embedding",    "_vcc_simple_emb"
                                  "\\ghost",               "_vcc_is_ghost_ptr"
                                  "\\fresh",               "_vcc_is_fresh"
                                  "\\thread_local",        "_vcc_thread_local2"
                                  "\\thread_local_array",  "_vcc_is_thread_local_array"
                                  "\\mutable_array",       "_vcc_is_mutable_array"
                                  "\\claims_object",       "_vcc_claims_obj"
                                  "\\claimable",           "_vcc_is_claimable"
                                  "\\make_claim",          "_vcc_claim"
                                  "\\destroy_claim",       "_vcc_unclaim"
                                  "\\active_claim",        "_vcc_valid_claim"
                                  "\\atomic_object",       "_vcc_is_atomic_obj"
                                  "\\universe",            "_vcc_set_universe" 
                                  "\\disjoint",            "_vcc_set_disjoint" 
                                  "\\subset",              "_vcc_set_subset" 
                                  "\\by_claim_wrapper",    "_vcc_by_claim"
                                  "\\alloc",               "_vcc_spec_alloc"
                                  "\\alloc_array",         "_vcc_spec_alloc_array"
                                  "\\heap_alloc",          "_vcc_alloc"
                                  "\\when_claimed_marker", "_vcc_when_claimed"
                                  "\\extent_fresh",        "_vcc_extent_is_fresh"
                                  "\\malloc_root",         "_vcc_is_malloc_root"
                                  "\\object_root",         "_vcc_is_object_root"
                                  "\\deep_eq",             "_vcc_deep_struct_eq"
                                  "\\shallow_eq",          "_vcc_shallow_struct_eq"
                                  "\\non_primitive_ptr",   "_vcc_is_non_primitive_ptr"
                                  "\\castlike_known",      "_vcc_known"
                                ]

    let fnMap = new Dict<_,_>()

    let normalizeCallsAndFindKeyFunctions = function
      | Top.TypeDecl(td) as decl ->
        let normalizeMine self = function
          | Call(ec, ({Name = "\\mine"} as fn), [], args) -> Some(Call(ec, fn, [], Expr.This({ec with Type = Type.MkPtrToStruct(td)}) :: List.map self args))
          | _ -> None
        deepMapExpressions normalizeMine [decl] |> List.head
      | Top.FunctionDecl({Name = ("\\set_closed_owner"|"\\giveup_closed_owner"|"\\set_owns")} as fn) as decl -> 
        fnMap.Add(fn.Name, fn)
        decl
      | decl -> decl

    let removeMagicEntities = 
      let isNotMagic = function 
        | Top.Global({Name = "\\me"}, _) 
        | Top.TypeDecl({Name = "\\TypeState"}) -> false
        | _ -> true
      List.filter isNotMagic

    let normalizeInDomain self = function
      | Call(ec, {Name = "\\set_in"}, [], [e1; Call(_, {Name = "\\domain"}, [], [e2])]) ->          
        let uncasted =
          match e2 with
            | Cast ({ Type = Type.ObjectT }, _, e) -> e
            | e2 -> e2
        let name =
          match uncasted.Type with
            | Ptr Claim -> "_vcc_in_claim_domain"
            | _ -> "_vcc_in_domain"
        Some(Macro(ec, name, [self e1; self e2]))
      | Call(ec, {Name = "\\set_in"}, [], [e1; Call(_, {Name = "\\vdomain"}, [], [e2])]) -> 
        Some(Macro(ec, "_vcc_in_vdomain", [self e1; self e2]))
      | _ -> None

    let normalizeSignatures self =
      let selfs = List.map self
      function
        | Call(ec, ({Name = "\\make_claim"} as fn), [], [Macro(es, "set", []); prop]) -> Some(Call(ec, fn, [],  [Macro(es, "_vcc_set_empty", []); self prop]))
        | Call(ec, ({Name = "\\make_claim"} as fn), [], [Macro(_, "set", elems); prop]) -> Some(Call(ec, fn, [], selfs elems @ [prop]))
        | Call(ec, ({Name = "\\destroy_claim"} as fn), [], [cl; Macro(_, "set", elems)]) -> Some(Call(ec, fn, [], selfs (cl :: elems)))
        | Call(ec, ({Name = "\\upgrade_claim"} as fn), [], [Macro(es, "set", []); prop]) -> Some(Call(ec, fn, [], [Macro(es, "_vcc_set_empty", []); self prop]))
        | Call(ec, ({Name = "\\upgrade_claim"} as fn), [], [Macro(_, "set", claimsSet); prop]) -> Some(Call(ec, fn, [], selfs (claimsSet @ [prop])))
        | Call(ec, ({Name = "\\claimable"} as fn), [], [e]) -> Some(Call(ec, fn, [], [Macro({e.Common with Type = Type.TypeIdT}, "_vcc_typeof", [self e])]))
        | Call(ec, ({Name = "\\havoc_others"} as fn), [], [e]) -> 
          let e' = self e
          Some(Macro(ec, "_vcc_havoc_others", [e'; Macro({e'.Common with Type = Type.TypeIdT}, "_vcc_typeof", [e'])]))
        | _ -> None

    let normalizeOwnershipManipulation =
      let checkOwnsObjectT self = function
        | Macro (ec, "_vcc_owns", [Macro (_, "&", [e])]) when e.Type = Type.ObjectT ->
          Some (Macro (ec, "_vcc_owns", [self e]))
        | _ -> None

      let rec aux inAtomic self = 
        let selfs = List.map self
        function
          | Atomic(ec, objs, body) -> Some(Atomic(ec, selfs objs, body.SelfMap(aux true)))
          | Macro(ec, "atomic_op", args) ->
            let self' (e:Expr) = e.SelfMap(aux true)
            Some (Macro (ec, "atomic_op", List.map self' args))
          | Macro(ec, "=", [Macro(_, "_vcc_owns", [e1]); 
                            CallMacro(_, ("\\set_add_element"|"\\set_remove_element" as setOp), [], 
                                  [Macro(_, "_vcc_owns", [e1']); e2] )]) when inAtomic  -> 
              let fn = if setOp = "\\set_add_element" then fnMap.["\\set_closed_owner"] else fnMap.["\\giveup_closed_owner"]
              Some(Call({ec with Type = Type.Void}, fn, [], [self e2; self e1]))
          | Macro(ec, "=", [Macro(_, "_vcc_owns", [e1]) as ownsSet; 
                            CallMacro (_, "\\set_remove_element", [], [Macro(_, "_vcc_owns", [e1']); e2]) as newOwns]) ->
            let e1 = self e1
            let e2 = self e2
            let tok = afmte 8026 "{0} is not in {1}->\\owns before trying to remove it" [e2; e1]            
            let check = Expr.MkAssert (Expr.Macro (tok, "_vcc_set_in", [e2; ownsSet]))
            let update = Call({ec with Type = Type.Void}, fnMap.["\\set_owns"], [], [e1; self newOwns])
            Some (Expr.MkBlock [check; update])
          | Macro(ec, "=", [Macro(_, "_vcc_owns", [e1]); e2]) -> 
            Some(Call({ec with Type = Type.Void}, fnMap.["\\set_owns"], [], [self e1; self e2]))
          | _ -> None
      let doDecl = function
        | Top.FunctionDecl f when f.Body.IsSome ->
          let isAtomic = hasCustomAttr AttrAtomicInline f.CustomAttr
          f.Body <- Some (f.Body.Value.SelfMap checkOwnsObjectT)
          f.Body <- Some (f.Body.Value.SelfMap (aux isAtomic))
          Top.FunctionDecl f
        | d -> d
      List.map doDecl

    let normalizeMisc self = 
      let selfs = List.map self
      function
        | Macro(ec, "set", elems) -> Some(Macro(ec, "_vcc_create_set", Expr.Bogus :: selfs elems))
        | Macro(ec, "\\is", [arg;UserData(_, (:? Type as t))]) -> Some(Macro(ec, "_vcc_is", [self arg; typeExpr t]))
        | Ref(ec, {Name = "\\me"}) -> Some(Macro(ec, "_vcc_me", []))
        | Prim (ec, Op ("==" as name, _), [e1; e2]) when e1.Type.IsPtrSet ->
          Some (Macro (ec, "_vcc_set_eq", [self e1; self e2]))
        | Prim (ec, Op ("!=" as name, _), [e1; e2]) when e1.Type.IsPtrSet ->
          Some (mkNot (Macro (ec, "_vcc_set_eq", [self e1; self e2])))
        | _ -> None

    let normalizeMacros self = function
      | Macro(ec, m, args) -> 
        match Map.tryFind m newToOldFn with
          | Some m' -> Some(Macro(ec, m', List.map self args))
          | None -> None
      | _ -> None

    let mapFromNewSyntax = function        
      | Top.FunctionDecl(fn) when fn.Name.StartsWith("\\macro") -> ()
      | Top.FunctionDecl(fn) when fn.Name.StartsWith("\\result_macro") -> ()
      | Top.FunctionDecl(fn) when fn.Name.StartsWith "\\" ->
        match newToOldFn.TryFind fn.Name with
          | Some oldName -> fn.Name <- oldName
          | None when fn.Token.Filename.EndsWith("vccp.h", System.StringComparison.OrdinalIgnoreCase) -> fn.Name <- "_vcc_" + fn.Name.Substring(1)
          | _ -> ()
      | _ -> ()
      
    let rec normalizeCastLike withinSpec self = function
      | Macro (ec, "spec", [body]) ->
        Some(Macro(ec, "spec", [body.SelfMap(normalizeCastLike true)]))
      | Macro (ec, n, [primary; Macro (_, "argument_tuple", secondary)]) when n.StartsWith "\\castlike_va_" ->
        match n.Substring 13 with
          | "atomic_read" ->
            let secondary = secondary |> List.map (fun e -> Pure (e.Common, Macro (e.Common, "read_only", [e])))
            Some (Macro (ec, "atomic_op", secondary @ [Expr.False; primary]))
          | n ->              
            helper.Oops (ec.Token, "unknown \\castlike_va_ function " + n)
            None
      | Macro (ec, "\\castlike_retype", args) ->
        Some (Macro (ec, "_vcc_retype", List.map self args))
      | Macro (ec, "\\castlike_by_claim", [expr; cl]) ->
        Some (Old (ec, Macro ({ expr.Common with Type = Type.MathState }, "_vcc_by_claim", [cl]), expr))
      | Macro (ec, ("\\castlike_blob" | "\\castlike_blob_of" | "\\castlike_root_array" | "\\castlike_root_index" as name), args) ->
        Some (Macro (ec, name.Replace ("\\castlike", "prelude"), List.map self args))
      | Macro (ec, "\\castlike_root_array", args) ->
        Some (Macro (ec, "prelude_blob", List.map self args))
      | Macro (ec, "\\castlike_unblobify", args) ->
        let expr' = Macro (ec, "_vcc_unblobify", List.map self args)
        let kind =
          if (withinSpec || exprDependsOnSpecExpr expr' |> Option.isSome) then VarKind.SpecLocal
          else VarKind.Local
        let decls1, rf = cache helper "blob" expr' kind
        Some (Expr.MkBlock (decls1 @ [rf]))
      | Macro (ec, "\\castlike_read_only", [arg]) ->
        Some (Expr.Macro (ec, "read_only", [self arg]))
      | _ -> None
      
    let rewriteBvAssertAsBvLemma self = function
      | Assert(ec, Macro (_, "lbl_bv", [_; expr]), []) -> 
        let makeUnchecked self = function
          | Prim(ec, Op(_, CheckedStatus.Unchecked), _) -> None
          | Prim(ec, Op(op, _), args) -> Some(Prim(ec, Op(op, CheckedStatus.Unchecked), List.map self args))
          | Cast(ec, CheckedStatus.Unchecked, _) -> None
          | Cast(ec, _, expr) -> Some(Cast(ec, CheckedStatus.Unchecked, self expr))
          | _ -> None
        Some(Assert(ec, Expr.Macro(expr.Common, "_vcc_bv_lemma", [expr.SelfMap(makeUnchecked)]), []))
      | Assert(ec, expr, []) -> None
      | Assert(ec, expr, trigs) -> 
        helper.Error(ec.Token, 9713, "unhandled triggers on assert")
        Some(Assert(ec, expr, []))
      | _ -> None

    let handleExpressionLabels self = function
      | Macro (ec, "lbl_split", [_; expr]) ->
        Some (Macro (ec, "_vcc_split_conjunctions", [self expr]))
      | Macro (ec1, "lbl_use", [lbl; CallMacro(ec2, ("_vcc_in_domain"|"_vcc_in_vdomain" as fn), [], [e1; e2])]) ->
        Some (self (Macro (ec2, fn, [Macro (ec1, "_vcc_use", [lbl; e1]); e2])))
      | _ -> None
    
    let normalizeUnwrapping self = function
      | Macro (ec, "unwrapping", Block (bec, stmts, Some bc) :: objects) ->
        let nonWrites = bc.Decreases @ bc.Reads @ bc.Ensures @ bc.Requires
        match nonWrites with
          | e :: _ ->  
            helper.Error (e.Token, 9674, "_(unwrapping ...) does not allow contracts other than _(writes ...)")
          | [] -> ()
        let wr = Macro (ec, "se_writes", bc.Writes)
        Some (Macro (ec, "skinny_expose", wr :: (self (Block (bec, stmts, None))) :: objects))
      | Macro (ec, "unwrapping", body :: objects) ->
        let stmtToken (msg:string) ec =
          let ee = forwardingToken ec None (fun () -> msg.Replace ("@@", ec.Value))
          { ee with Type = Type.Void }
        let rec build = function
          | (o:Expr) :: os ->
            let wrapLike n = 
              let t = stmtToken ("_(" + n + " @@)") o.Token 
              let fn = TransUtil.internalFunction helper n
              Stmt (t, Call (t, fn, [], [o]))
            Expr.MkBlock [wrapLike "unwrap"; build os; wrapLike "wrap"] 
          | [] -> self body
        Some (build objects)
      | _ -> None

    let normalizeGroupInvariants decls = 

      let addGroupToMap (map : Map<_,_>) = 
        let rec getGroupNameFromAttrs = function
        | [] -> None
        | VccAttr(AttrGroupDecl, name) :: _ -> 
          Some name
        | _ :: attrs -> getGroupNameFromAttrs attrs

        function
        | Top.TypeDecl(td) ->
          match getGroupNameFromAttrs td.CustomAttr with
            | Some name -> 
              let parent = td.Parent.Value.UniqueId
              match map.TryFind parent with
                | None -> map.Add(parent, Set.singleton name)
                | Some groups -> map.Add(parent, Set.add name groups)
            | None -> map
        | _ -> map
                
      let groups = List.fold addGroupToMap Map.empty decls
      
      let doIt = function
        | Top.TypeDecl(td) as top -> 
          let groupsOfTd = match groups.TryFind td.UniqueId with | Some groupsOfTd -> groupsOfTd | None -> Set.empty
          let ngi (groupsOfTd : Set<_>) self = function
            | Macro(ec, "labeled_invariant", ([Macro(_, lbl, _); i] as args)) when groupsOfTd.Contains lbl -> Some(Macro(ec, "group_invariant", args))
            | _ -> None
          td.Invariants <- List.map (fun (expr:Expr) -> expr.SelfMap (ngi groupsOfTd)) td.Invariants
        | top -> ()

      List.iter doIt decls
      decls

    deepMapExpressions normalizeInDomain >> 
    List.map normalizeCallsAndFindKeyFunctions >> 
    normalizeGroupInvariants >>
    normalizeOwnershipManipulation >>
    deepMapExpressions normalizeSignatures >> 
    (fun decls -> List.iter mapFromNewSyntax decls; decls)>> 
    deepMapExpressions normalizeMacros >>
    removeMagicEntities >>
    deepMapExpressions normalizeMisc >> 
    deepMapExpressions rewriteBvAssertAsBvLemma >>
    deepMapExpressions handleExpressionLabels >>
    deepMapExpressions (normalizeCastLike false) >>
    deepMapExpressions normalizeUnwrapping



  // ============================================================================================================  
  helper.AddTransformer ("norm-new-syntax", TransHelper.Decl normalizeNewSyntax)