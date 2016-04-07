namespace Microsoft.Research.Vcc.SyntaxConverter
open Microsoft.FSharp.Text
open Microsoft.Research.Vcc.SyntaxConverter.Ast

module Rules =
  let gdict() = new System.Collections.Generic.Dictionary<_,_>()
  
  type ctx = 
    {
      in_ensures : bool
      outer_braces : int
    }

  type rule =
    {
      keyword : string
      replFn : ctx -> list<Tok> -> ctx * list<Tok> * list<Tok>
    }

  let ctxFreeRule rule ctx toks = let (l1, l2) = rule toks in ctx, l1, l2
    
  let rules = gdict()
  
  let rev_append a b =
    let rec aux acc = function
      | x :: xs -> aux (x :: acc) xs
      | [] -> acc
    aux b a
    
  let rec apply' ctx acc = function
    | Tok.Id (_, s) as t :: rest ->
      match rules.TryGetValue s with
        | true, r ->
          let ctx', res, rest = (r:rule).replFn ctx (t :: rest)
          apply' ctx' (rev_append res acc) rest
        | _ -> apply' ctx (t :: acc) rest
    | Tok.Group (p, s, toks) :: rest ->
      let ctx = if s = "{" then { ctx with outer_braces = ctx.outer_braces + 1 } else ctx
      apply' ctx (Tok.Group (p, s, apply' ctx [] toks) :: acc) rest    
    | t :: rest -> apply' ctx (t :: acc) rest
    | [] -> List.rev acc


  let replRule kw fn =
    let repl = function
      | id :: toks ->
        fn (), toks
      | _ -> failwith ""
    { keyword = kw
      replFn = ctxFreeRule repl }
    
  let parenRuleExt kw fn =
    let repl ctx = function
      | id :: toks ->
        match eatWs toks with
          | Tok.Group (_, "(", toks) :: rest ->
            let toks = apply' ctx [] toks
            let l1, l2 = fn (toks, rest) in ctx, l1, l2
          | _ -> ctx, [id], toks
      | _ -> failwith ""
    { keyword = kw
      replFn = repl }

  let parenRuleExtCtx kw fn fnCtx =
    let repl ctx = function
      | id :: toks ->
        match eatWs toks with
          | Tok.Group (_, "(", toks) :: rest ->
            let toks' = apply' (fnCtx ctx) [] toks
            let l1, l2 = fn (ctx, toks, toks', rest) in ctx, l1, l2
          | _ -> ctx, [id], toks
      | _ -> failwith ""
    { keyword = kw
      replFn = repl }
  
  let parenRuleCtx eatSemi kw fn =
    let repl (_, _, toks, rest) =
      match eatWs rest with
        | Tok.Op (_, ";") :: rest when eatSemi -> fn toks, rest
        | _ -> fn toks, rest            
    parenRuleExtCtx kw repl
  
  let parenRule eatSemi kw fn = parenRuleCtx eatSemi kw fn (fun x -> x)

  let splitAt op toks =
    let rec aux acc locAcc = function
      | Tok.Op (_, n) :: rest when n = op ->
        aux (List.rev locAcc :: acc) [] rest
      | x :: rest ->
        aux acc (x :: locAcc) rest
      | [] ->
        if locAcc.IsEmpty then List.rev acc
        else List.rev (List.rev locAcc :: acc)
    aux [] [] toks
  
  let parenRuleN kw n fn =
    let repl ctx = function
      | id :: toks ->
        match eatWs toks with
          | Tok.Group (_, "(", toks) :: rest when (splitAt "," (eatWs toks)).Length = n ->
            let args = splitAt "," (apply' ctx [] toks)
            ctx, fn args, rest
          | _ -> ctx, [id], toks
      | _ -> failwith ""
    { keyword = kw
      replFn = repl }
    
  let addRule (r:rule) = rules.Add (r.keyword, r)
  let addStmtKwRule kw newKw =    
    addRule (parenRule true kw (fun toks -> spec newKw toks))
    
  let addKwRule kw newKw =    
    addRule (parenRule false kw (fun toks -> spec newKw toks))
  
  let addFnRule fnName newFnName =
    addRule (parenRule false fnName (fun toks -> fnApp newFnName toks))
  
  let addKwRepl oldKw newKw =
    addRule (replRule oldKw (fun () -> [Tok.Id (fakePos, newKw)]))
    
  let countSemicolons toks =
    let isSemi = function
      | Tok.Op (_, ";") -> true
      | _ -> false
    List.length (List.filter isSemi toks)
  
  let joinWith op defs =
    let rec aux acc = function
      | [x] -> List.rev (rev_append x acc)
      | x :: rest -> aux (Tok.Op (fakePos, op) :: rev_append x acc) rest
      | [] -> List.rev acc
    aux [] defs
      
  let looksLikeDecl toks =
    let isDeclTok = function
      | Tok.Id _
      | Tok.Whitespace _
      | Tok.Comment _ -> true
      | Tok.Op (_, ("*"|"^")) -> true
      | _ -> false
    List.forall isDeclTok toks
  
  let rec getTriggers acc = function
    | Tok.Op (_, ";") as h :: rest ->
      match eatWs rest with
        | (Tok.Group (_, "{", _) :: _) as lst ->
          let rec aux acc l = 
            match eatWsEx l with
              | ws, (Tok.Group (_, "{", _) as t) :: rest ->
                aux (acc @ ws @ [t]) rest
              | _ -> (acc, l)
          let (trig, lst) = aux [] lst
          Some (List.rev acc, trig, lst)
        | _ -> getTriggers (h :: acc) rest
    | h :: rest -> getTriggers (h :: acc) rest
    | [] -> None

  let quantRule name guardOp =
    let repl (toks, rest) =
      let p = poss toks
      let body =
        match getTriggers [] toks with
          | Some (bindings, triggers, body) ->
            let body' =
              if countSemicolons body > 0 then
                match List.rev (splitAt ";" body) with
                  | [body; guard] -> guard @ [Tok.Whitespace (p, " "); Tok.Op (p, guardOp)] @ [space; Tok.Group(fakePos, "(", eatWs body)]
                  | _ -> failwith ""
              else body
            bindings @ [Tok.Op (p, ";")] @ [Tok.Whitespace (p, " ")] @ triggers @ body'
          | None ->
            if countSemicolons toks > 1 then
              let body, defs =
                match List.rev (splitAt ";" toks) with
                  | body :: guard :: defs ->
                    match trim guard with
                      | [Tok.Id (_, "\\true")] ->
                        [space; Tok.Group(fakePos, "(", eatWs body)], List.rev defs
                      | _ ->
                        if looksLikeDecl guard then
                          body, List.rev (guard :: defs)
                        else
                          let guardOp =
                            if guardOp = "###" then
                              System.Console.WriteLine ("{0}: Making lambda total with: {1} ==> ...", p, Tok.Sequence guard)
                              "==>"
                            else guardOp
                          guard @ [Tok.Whitespace (p, " "); Tok.Op (p, guardOp)] @ [space; Tok.Group(fakePos, "(", eatWs body)], List.rev defs
                  | _ -> failwith ""
              joinWith ";" defs @ [Tok.Op (p, ";")] @ body
            else
              toks
      let body = Tok.Id (p, "\\" + name) :: Tok.Whitespace (p, " ") :: body
      // stylistic: always place () around \forall ..., or only when neccessary?
      if (eatWs rest).IsEmpty then
        [paren "" body], rest
      else
        [paren "(" body], rest
    parenRuleExt name repl    
    
  let addInfixRule name tok =
    let repl = function 
      | [e1;e2] -> e1 @ (space :: tok :: space :: eatWs e2)
      | _ -> failwith ""
    addRule (parenRuleN name 2 repl)

  let init() =
    let canonicalKw = [
                        "atomic"
                        "decreases"
                        "requires"
                        "reads"
                        "writes"
                        "always"
                        "maintains"
                        "returns"
                      ]

    let canonicalFn = [
                        "wrapped"
                        "wrapped0"
                        "nested"
                        "thread_local"
                        "span"
                        "extent"
                        "inv"
                        "inv2"
                        "old"
                        "gemb"
                        "match_long"
                        "match_ulong"
                        "array_range"
                        "array_members"
                        "is_array"
                        "start_here"
                        "depends"
                        "not_shared"
                        "claims"
                        "unchanged"
                        "claims_claim"
                        "when_claimed"
                        "account_claim"
                        "always_by_claim"
                        "extent_zero"
                        "full_extent"
                        "mutable"
                        "extent_mutable"
                        "approves"
                        "program_entry_point"
                        "in_array"
                        "domain_updated_at"
                      ]

    let canonicalSm = [
                        "assert"
                        "assume"
                        "wrap"
                        "unwrap"
                        "deep_unwrap"
                        "axiom"
                        "reads_havoc"
                        "set_closed_owns"
                        "bump_volatile_version"
                        "begin_update"
                        "join_arrays"
                        "split_array"
                        "from_bytes"
                        "to_bytes"
                        "havoc_others"
                      ]

    for cw in canonicalKw do addKwRule cw cw
    for cf in canonicalFn do addFnRule cf ("\\" + cf)
    for cs in canonicalSm do addStmtKwRule cs cs

    addStmtKwRule "bv_lemma" "assert {:bv}" // this is stretching it
    
    // mostly for the testsuite
    addStmtKwRule "__assert" "assert"
    
    addKwRepl "mathint" "\\integer"
    addKwRepl "state_t" "\\state"
    addKwRepl "obj_t" "\\object"
    addKwRepl "ptrset" "\\objset"
    addKwRepl "claim_t" "\\claim"
    addKwRepl "thread_id" "\\thread"
    addKwRepl "this" "\\this"
    addKwRepl "ispure" "_(pure)"
    addKwRepl "no_reads_check" "_(no_reads_check)"
    addKwRepl "frameaxiom" "_(frameaxiom)"
    addKwRepl "isadmissibilitycheck" "_(admissibility)"
    addKwRepl "skipverification" "_(assume_correct)"
    addKwRepl "backing_member" "_(backing_member)"
    addKwRepl "true" "\\true"
    addKwRepl "false" "\\false"
    addKwRepl "spec_malloc" "\\alloc"             // cannot use fnRule because of template paramters
    addKwRepl "spec_malloc_array" "\\alloc_array"  // cannot use fnRule because of template paramters
    addKwRepl "block" ""                          // has become superfluous in the new syntax
    
    addRule (parenRule false "sk_hack" (fun toks -> [id ":hint"; space; paren "" toks]))
    addRule (quantRule "forall" "==>")
    addRule (quantRule "exists" "&&")
    addRule (quantRule "lambda" "###")

    addKwRule "expose" "unwrapping"
    addKwRule "skinny_expose" "unwrapping"
    addKwRule "out_param" "writes"
    addKwRule "weak_out_param" "writes"

    addFnRule "emb" ("\\embedding")
    addFnRule "valid_claim" "\\active_claim"
    addFnRule "is_claimable" "\\claimable"
    addFnRule "is_fresh" "\\fresh"
    addFnRule "is_thread_local_array" "\\thread_local_array"
    addFnRule "is_mutable_array" "\\mutable_array"
    addFnRule "unchecked" "_(unchecked)"
    addFnRule "keeps" "\\mine"
    addFnRule "set_universe" "\\universe"
    addFnRule "claims_obj" "\\claims_object"
    addFnRule "extent_is_fresh" "\\extent_fresh"
    addFnRule "is_malloc_root" "\\malloc_root"
    addFnRule "is_object_root" "\\object_root"
    addFnRule "in_state" "\\at"
    addFnRule "current_state" "\\now"
    addFnRule "deep_eq"  "\\deep_eq"
    addFnRule "shallow_eq" "\\shallow_eq"
    addFnRule "set_disjoint" "\\disjoint"
    addFnRule "set_subset" "\\subset"
    addFnRule "is_non_primitive_ptr" "\\non_primitive_ptr"
    addFnRule "generic_instance" "vcc_generic_instance"
    addFnRule "nospeccast" "vcc_nospeccast"
    addFnRule "vcs_force_splits" "vcc_force_splits"
    addFnRule "vcs_keep_going" "vcc_keep_going"

    addRule (parenRule false "SET" (fun toks -> [paren "{" toks]))
    addRule (parenRule false "set_singleton" (fun toks -> [paren "{" toks]))
    addRule (parenRule false "set_empty" (fun toks -> [paren "{" []]))
    
    let claimp toks =
      match eatWs toks with
        | Tok.Id (_, "out") :: rest ->
          spec "out" (Tok.Id (fakePos, "\\claim") :: rest)
        | _ -> spec "ghost" (Tok.Id (fakePos, "\\claim") :: space :: toks)
    addRule (parenRule false "claimp" claimp)
    
    addRule (parenRuleN "me" 0 (fun _ -> [Tok.Id (fakePos, "\\me")]))
    addRule (parenRuleN "reads_check" 1 (fun n -> id "vcc_attr (\"is_reads_check\", \"" :: n.Head @ [id "\")"]))

    let speccast = function
      | [tp; expr] ->
        fnApp "_" tp @ [paren "(" expr]
      | _ -> failwith ""
    addRule (parenRuleN "speccast" 2 speccast)

    let speccast_uc = function
      | [tp; expr] ->
        fnApp "_(unchecked)" (fnApp "_" tp @ [paren "(" expr])
      | _ -> failwith ""
    addRule (parenRuleN "speccast_uc" 2 speccast_uc)

    let typed_phys_or_spec isSpec toks = 
      let optNot = if isSpec then [] else [Tok.Op(fakePos, "!")]
      [paren "(" ([parenOpt toks; Tok.Op(fakePos, "->"); id "\\valid"; space; Tok.Op(fakePos, "&&"); space] @ optNot @ (fnApp "\\ghost" toks))]

    addRule (parenRule false "typed_phys" (typed_phys_or_spec false))
    addRule (parenRule false "typed_spec" (typed_phys_or_spec true))

    addRule (parenRule false "vcc" (fnApp "_"))

    addInfixRule "set_union" (Tok.Op(fakePos, "\\union"))
    addInfixRule "set_difference" (Tok.Op(fakePos, "\\diff"))
    addInfixRule "set_intersection" (Tok.Op(fakePos, "\\inter"))
    addInfixRule "set_eq" (Tok.Op(fakePos, "=="))
    addInfixRule "set_equal" (Tok.Op(fakePos, "=="))
    addInfixRule "set_in" (Tok.Op(fakePos, "\\in"))
    addInfixRule "set_in0" (Tok.Op(fakePos, "\\in0"))
    addInfixRule "is" (Tok.Op(fakePos, "\\is"))

    let addGhostFieldRule fn fld = 
      let ghostFieldRule fieldName = function
        | [e] -> parenOpt e :: [Tok.Op(fakePos, "->"); Tok.Id(fakePos, fieldName)]
        | _ -> failwith ""
      addRule (parenRuleN fn 1 (ghostFieldRule fld))

    addGhostFieldRule "owns"    "\\owns"
    addGhostFieldRule "owner"   "\\owner"
    addGhostFieldRule "typed"   "\\valid"
    addGhostFieldRule "closed"  "\\closed"
    addGhostFieldRule "ref_cnt" "\\claim_count"

    let result_rule ctx = function
      | (id:Tok) :: rest when ctx.in_ensures -> ctx, [Tok.Id(id.Pos, "\\result")], rest
      | id :: rest -> ctx, [id], rest
      | _ -> failwith ""

    addRule { keyword = "result"; replFn = result_rule }
    addRule (parenRuleCtx false "ensures" (fun toks -> spec "ensures" toks) (fun (c:ctx) -> { c with in_ensures = true}) )

    
    let as_array = function
      | [arr; sz] ->
        let arr =
          match arr with
            | [Tok.Id _] -> arr
            | _ -> [paren "(" arr]
        [paren "(" [Tok.Id (fakePos, "void"); paren "[" sz]] @ arr
      | _ -> failwith ""
    addRule (parenRuleN "as_array" 2 as_array)
        
    let union_active = function
      | [u; fld] -> fnApp "\\union_active" (Tok.Op(fakePos, "&") :: parenOpt u :: Tok.Op(fakePos, "->") :: eatWs fld)
      | _ -> failwith ""
    addRule (parenRuleN "union_active" 2 union_active)
    addRule (parenRuleN "union_active_anon" 2 union_active)
        
    let union_reinterpret = function
      | [u; fld] ->  spec "union_reinterpret" (Tok.Op(fakePos, "&") :: parenOpt u :: Tok.Op(fakePos, "->") :: eatWs fld)
      | _ -> failwith ""
    addRule (parenRuleN "union_reinterpret" 2 union_reinterpret)

    let on_unwrap = function
      | [ cond ] -> spec "invariant" (fnApp "\\on_unwrap" (Tok.Id(fakePos, "\\this") :: Tok.Op(fakePos, ",") :: space :: cond))
      | _ -> failwith ""
    addRule (parenRuleN "on_unwrap" 1 on_unwrap)

    let set_owns = function
      | [e; s] ->
        spec "ghost" ([parenOpt e; Tok.Op(fakePos, "->"); Tok.Id(fakePos, "\\owns"); Tok.Op(fakePos, " = ")] @ s)
      | _ -> failwith ""
    addRule (parenRuleN "set_owns" 2 set_owns)
    
    let closed_owner_rule op = function
      | [ob; owner] ->
        spec "ghost" ([parenOpt owner; Tok.Op(fakePos, "->"); Tok.Id(fakePos, "\\owns"); Tok.Op(fakePos, " " + op + " ") ] @ (eatWs ob))
      | _ -> failwith ""

    addRule (parenRuleN "set_closed_owner" 2 (closed_owner_rule "+="))
    addRule (parenRuleN "giveup_closed_owner" 2 (closed_owner_rule "-="))

    addRule (parenRuleN "set_owner" 2 (closed_owner_rule "+="))
    addRule (parenRuleN "giveup_owner" 2 (closed_owner_rule "-="))

    let doUse = function
      | [lab; expr] -> paren "{" (Tok.Id (fakePos, ":use ") :: lab) :: expr
      | _ -> failwith ""
    addRule (parenRuleN "use" 2 doUse)

    let simpleLabel labName = function
      | [expr] -> paren "{" [Tok.Id (fakePos, (":" + labName))] :: space :: expr
      | _ -> failwith ""
    addRule (parenRuleN "split_conjunctions" 1 (simpleLabel "split"))

    let in_domain dom = function
     | [e1; e2] ->
       e1 @ [ Tok.Op(fakePos, " \\in ") ] @ fnApp dom (eatWs e2)
     | _ -> failwith ""
    addRule (parenRuleN "in_domain" 2 (in_domain "\\domain"))
    addRule (parenRuleN "in_claim_domain" 2 (in_domain "\\domain"))
    addRule (parenRuleN "in_vdomain" 2 (in_domain "\\vdomain"))
        
    let reify fn toks = 
      match List.rev (splitAt "," toks) with 
        | prop :: objs ->
          fnApp fn (paren "{" (joinWith "," (List.rev objs)) :: Tok.Op (fakePos, ",") :: prop)
        | _ -> failwith ""

    let by_claim = function
      | [claim; expr] -> [paren "(" (spec "by_claim" claim @ [paren "(" expr])]
      | _ -> failwith ""
    addRule (parenRuleN "by_claim" 2 by_claim)

    addRule (parenRule false "claim" (reify "\\make_claim"))
    addRule (parenRule false "upgrade_claim" (reify "\\upgrade_claim"))
            
    let castLike useResult oldName newName =
      let fn toks =
        match splitAt "," toks with
          | hd :: tl ->
            spec newName (joinWith "," tl) @ [parenOpt hd]
          | _ -> failwith ""      
      parenRuleCtx false oldName fn (fun ctx -> if useResult then { ctx with in_ensures = true } else ctx)

    addRule (castLike false "known" "known")
    addRule (castLike true "atomic_op" "atomic_op")
    addRule (castLike true "atomic_read" "atomic_read")

    let unclaim toks = 
      match splitAt "," toks with 
        | cl :: objs ->
          spec "ghost" (fnApp "\\destroy_claim" (cl @ [Tok.Op (fakePos, ", "); paren "{" (joinWith "," objs)]))
        | _ -> failwith ""
    addRule (parenRule false "unclaim" unclaim)
            
    let def_group toks = 
      match splitAt "," toks with
        | [groupName] -> spec "group" groupName
        | groupName :: groupSpecs -> spec "group" ((joinWith " " groupSpecs) @ (space ::  groupName))
        | _ -> failwith ""
    addRule (parenRule false "def_group" def_group)

    let in_group = function
      | [toks] -> fnApp "_" (Tok.Op(fakePos, ":") :: toks)
      | _ -> failwith ""    
    addRule (parenRuleN "in_group" 1 in_group)

    let inv_group = function
      | [groupName; invariant] -> spec "invariant" (Tok.Op(fakePos, ":") :: groupName @ (space :: eatWs invariant))
      | _ -> failwith ""
    addRule (parenRuleN "inv_group" 2 inv_group)

    let invariant toks = 
      match eatWs toks with
        | (Tok.Id(_, lbl) as id) :: Tok.Op(_, ":") :: invariant ->  spec "invariant" (Tok.Op(fakePos, ":") :: id :: (space :: eatWs invariant))
        | invariant -> spec "invariant" (eatWs invariant)
    addRule (parenRule true "invariant" invariant)

    let member_name = function
      | hd :: rest ->
        match eatWs rest with
          | Tok.Group(_, "(", memName) :: rest ->
            match eatWs rest with 
              | (Tok.Id _ as tName) :: rest ->
                match eatWs rest with
                  | (Tok.Group(_, "{", _) as tp) :: rest -> [], (tName :: space :: tp :: space :: fnApp "_" memName) @ rest
                  | _ -> [], tName :: space :: rest
              | (Tok.Group(_, "{", _) as tp) :: rest -> [], (tp :: space :: fnApp "_" memName) @ rest
              | _ -> [], rest
          | _ -> failwith ""
      | _ -> failwith ""
    addRule { keyword = "member_name"; replFn = ctxFreeRule member_name }

    let spec_code toks =
      if List.exists (function Tok.Op (_, ";") -> true | _ -> false) toks then
        spec "ghost" [Tok.Group (fakePos, "{", toks)]
      else
        spec "ghost" toks

    let specOnlyBlock (ctx, oldToks, toks, rest) =
      if countSemicolons oldToks > 1 then
        spec "ghost" [Tok.Group (fakePos, "{", toks)], rest
      else
        spec "ghost" toks, rest

    addRule (parenRuleExtCtx "speconly" specOnlyBlock (fun x -> x))

    let specBlock (ctx:ctx, oldToks, toks, rest) =
      if countSemicolons oldToks > 1 && ctx.outer_braces > 0 then
        spec "ghost" [Tok.Group (fakePos, "{", toks)], rest
      else
        match toks with
          | FnApp ("_", AfterWs ([Tok.Id (_, "specmacro")]), AfterWs (fnDef)) ->
            let rec repl = function
              | FnApp ("_", AfterWs (Tok.Id (p, "returns") :: inner), remaining) -> space :: Tok.Op (p, "=") :: space :: paren "(" inner :: remaining
              | x :: xs -> x :: repl xs
              | [] -> []
            spec "logic" (repl fnDef), rest
          | _ ->
            let rec map_with_last f = function
              | [] -> []
              | [x] -> [f true x]
              | x :: xs -> f false x :: map_with_last f xs
            let  doStmt isLast stmt =
              let semi = if isLast then [] else [Tok.Op(fakePos, ";")]
              match eatWsEx stmt with
                | ws, [] -> ws
                | ws, stmt' ->  ws @ spec "ghost" (stmt' @ semi)
            toks |> splitAt ";" |> map_with_last doStmt |> List.concat, rest

    addRule (parenRuleExtCtx "spec" specBlock (fun x -> x))

    let struct_rule = function
      | hd :: rest ->
        match eatWs rest with
          | Tok.Id (_, "vcc") :: args ->
            match eatWs args with
              | Tok.Group (_, "(", toks) :: rest ->
                fnApp "_" toks @ [space], hd :: rest
              | _ -> [hd], rest
          | _ -> [hd], rest
      | _ -> failwith ""
    
    addRule { keyword = "struct"; replFn = ctxFreeRule struct_rule }
    addRule { keyword = "union"; replFn = ctxFreeRule struct_rule }

  let apply = apply' { in_ensures = false; outer_braces = 0 }  []
