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

type TriggerInference(helper:Helper.Env, bodies:Lazy<list<ToBoogieAST.Function>>, quantTok:Token, invMapping:Dict<B.Expr,list<C.Expr>>, quantVars:list<B.Var>) =
  let dbg = helper.Options.DumpTriggers >= 5
  let maxQuality = 4
  let quantVars = List.map fst quantVars // we don't care about the type
  let quantVarSet = gdict()
  do for v in quantVars do quantVarSet.[v] <- true

  // TODO: It would be good to make this match the {:level ...} directive.

  // -1 : never use it
  //  0 : uses arithmetic (see below)
  //  1 : only as last resort
  //  2 : everything else
  //  3 : maps, sets, user functions
  //  4 : ownership
  //
  // Currently the polarity is ignored, in future we might do something about it.
  let topTriggerQuality pol = function
    // level 4
    | B.Expr.FunctionCall (("$keeps"|"$set_in0"), _)
    | B.Expr.FunctionCall ("$set_in", [_; B.Expr.FunctionCall ("$owns", _)])
    | B.Expr.ArrayIndex (B.Expr.FunctionCall ("$owns", _), _) as expr ->
      4

    // level 3
    | B.Expr.FunctionCall ("$set_in", _)
    | B.Expr.ArrayIndex (_, _) ->
      3
    | B.Expr.FunctionCall (name, _) when name.StartsWith "$select.$map" ->
      3

    // list of bad patterns: 
    | B.Expr.FunctionCall (("$good_state"), _) -> 1 
    | B.Expr.FunctionCall (("$ptr"|"$phys_ptr_cast"|"$spec_ptr_cast"), [_; B.Expr.Ref _]) -> 1 
    | B.Expr.FunctionCall (("$field_parent_type"|"$field_type"|"$base"|"$is_primitive"|"$is"|"$addr"|"$field"
                           |"$is_null"), _) -> -1 
    | B.Expr.FunctionCall (("$ref"|"$base"|"$addr"), [B.Expr.FunctionCall ("$ptr", [_; B.Expr.Ref _])]) -> -1

    // all the rest:
    | expr ->
      let isUserFun = function
        | C.Expr.Call _ -> true
        | _ -> false
      let orig = lookupWithDefault invMapping [] expr
      if List.exists isUserFun orig then 3
      else 2

  // this is very arbitrary; keep in mind that sk_hack has type bool->bool, so don't use it on terms of non-bool type
  let shouldAddSkHack = function
    | B.Expr.FunctionCall (("$keeps"|"$set_in"|"$set_in0"), _) as expr -> topTriggerQuality 0 expr = 4
    | _ -> false

  let isForbiddenInTrigger = function
    | B.Expr.Exists _
    | B.Expr.Forall _
    | B.Expr.Lambda _
    | B.Expr.Ite _
    | B.Expr.Primitive (("&&"|"||"|"=="|"!="|"==>"|"<==>"|"!"|"anyEqual"), _) -> true

    // Boogie doesn't allow comparisons
    | B.Expr.Primitive (("<"|">"|"<="|">="), _) -> true
    // We don't want these.
    | B.Expr.FunctionCall (name, _) when name.StartsWith "$in_range" -> true
    | B.Expr.FunctionCall (("$ptr_eq"|"$ptr_neq"), _) -> true

    | B.Expr.Primitive _ 
    | B.Expr.ArrayIndex _
    | B.Expr.ArrayUpdate _
    | B.Expr.BoolLiteral _
    | B.Expr.BvConcat _
    | B.Expr.BvExtract _ 
    | B.Expr.FunctionCall _ 
    | B.Expr.Ref _ 
    | B.Expr.Old _
    | B.Expr.BvLiteral _
    | B.Expr.SecLabelLiteral _
    | B.Expr.IntLiteral _ -> false

  let isArithmetic = function
    | B.Expr.Primitive (("<"|">"|"<="|">="|"+"|"-"|"*"), _) -> true
    | _ -> false

  let getTriggerScore pol = function
    | B.Expr.Ref _ -> None
    | expr when isForbiddenInTrigger expr -> None
    | expr ->
      let allowed = ref true
      let hasArithmetic = ref false
      let res = gdict()
      let aux expr =
        if not !allowed then Some expr
        elif isForbiddenInTrigger expr then
          allowed := false
          Some expr
        else
          if isArithmetic expr then
            hasArithmetic := true
          match expr with
            | B.Expr.Ref s when quantVarSet.ContainsKey s ->
              res.[s] <- true
            | _ -> ()
          None
      expr.Map aux |> ignore
      if !allowed then        
        if !hasArithmetic then Some (res, 0)
        else           
          Some (res, topTriggerQuality pol expr)
      else None
  
  let removeSubsumed resTrig =
    let trigs = gdict()
    let shouldKeep = function
      | [(t:B.Expr)] ->
        let res = ref true
        let checkSubterm expr =
          if expr <> t && trigs.ContainsKey expr then
            res := false
            Some expr
          else None
        t.Map checkSubterm |> ignore
        !res
      | _ -> true

    Seq.iter (function [t] -> trigs.Add (t, true) | _ -> ()) resTrig
    Seq.filter shouldKeep resTrig

  let addSkHack resTrig =
    let checkOne = function
      | [t] when shouldAddSkHack t -> [[t]; [B.Expr.FunctionCall ("sk_hack", [t])]]
      | e -> [e]
    Seq.collect checkOne resTrig

  let substToString = function
    | Some m -> Map.fold (fun acc k v -> String.Format ("{0} -> {1}", k, v) :: acc) [] m |> listToString
    | None -> "None"

  let rec matchExpr (sub : Map<_,_>) (a, b) = 
    if helper.Options.DumpTriggers >= 10 then
      Console.WriteLine ("  (((")
    let res =
      match a, b with
        | B.Expr.FunctionCall ("$mem", [s1; p1]), B.Expr.FunctionCall ("$mem", [s2; p2]) when matchExpr sub (s1, s2) = None -> 
          matchExpr sub (p1, p2) // ignore failure in state
        | B.Expr.FunctionCall (id1, e1), B.Expr.FunctionCall (id2, e2) when id1 = id2 -> matchExprs sub e1 e2
        | B.Expr.FunctionCall ("$ptr", [_; p]), e2 ->
          matchExpr sub (p, e2)
        | B.Expr.FunctionCall (("$phys_ptr_cast"|"$spec_ptr_cast"), [p; _]), e2 ->
          matchExpr sub (p, e2)
        | B.Expr.Primitive (id1, e1), B.Expr.Primitive (id2, e2) when id1 = id2 -> matchExprs sub e1 e2
        | B.Expr.ArrayIndex (e1, es1), B.Expr.ArrayIndex (e2, es2) -> matchExprs sub (e1 :: es1) (e2 :: es2)
        | B.Expr.ArrayUpdate (e1, es1, ee1), B.Expr.ArrayUpdate (e2, es2, ee2) -> matchExprs sub (ee1 :: e1 :: es1) (ee2 :: e2 :: es2)
        | B.Expr.BvConcat (e1, ee1), B.Expr.BvConcat (e2, ee2) -> matchExprs sub [e1; ee1] [e2; ee2]
        | B.Expr.BvExtract (e1, x1, y1), B.Expr.BvExtract (e2, x2, y2) when x1 = x2 && y1 = y2 -> matchExpr sub (e1, e2)
        | B.Expr.Old e1, e2 -> matchExpr sub (e1, e2)
        | e1, B.Expr.Old e2 -> matchExpr sub (e1, e2)
        | B.Expr.Ref i1, e2 when sub.ContainsKey i1 ->
          if sub.[i1] = e2 then Some sub else None
        | B.Expr.Ref i1, e2 when quantVarSet.ContainsKey i1 ->
          Some (sub.Add (i1, e2))
        | e1, e2 -> if e1 = e2 then Some sub else None
    if helper.Options.DumpTriggers >= 10 then
      Console.WriteLine ("  unify: {0} / {1} ?= {2} -> {3} )))", a, substToString (Some sub), b, substToString res)
    res
  and matchExprs sub e1 e2 = 
    let rec aux s = function
      | e1 :: ee1, e2 :: ee2 ->
        match matchExpr s (e1, e2) with
          | Some s -> aux s (ee1, ee2)
          | None -> None
      | [], [] -> Some s
      | _ -> die()
    if List.length e1 <> List.length e2 then None
    else aux sub (e1, e2)
  
  let transformGList f (l:GList<_>) =
    let tmp = f l |> Seq.toList
    l.Clear()
    l.AddRange tmp

  let expandBody (expr:B.Expr) =
    let functions = gdict()
    for f in bodies.Value do
      functions.[f.Name] <- f

    let visited = gdict()

    let rec booleanTrigger expr =
      isForbiddenInTrigger expr ||
        match expr with
          | B.Expr.FunctionCall (name, _) ->
            match functions.TryGetValue name with
              | true, f -> booleanTrigger f.Body
              | _ -> false
          | _ -> false

    let rec visit expr =
      let rec self (expr:B.Expr) = expr.Map visit
      if visited.ContainsKey expr then
        if not (booleanTrigger expr) then None
        else
          match expr with
            | B.Expr.FunctionCall (name, args) ->
              match functions.TryGetValue name with
                | true, f -> Some (self (f.Expand args))
                | _ -> None
            | _ -> None
      else
        visited.Add (expr, true)
        let res = self expr
        invMapping.[res] <- (lookupWithDefault invMapping [] res) @ (lookupWithDefault invMapping [] expr)
        Some res

    expr.Map visit
       
  let doInfer (body:B.Expr) =
    let body = expandBody body
    let resTrig = glist[]

    let candidates = glist[]
    let candidatesSet = gdict()
    let rec getSubterms pol expr =
      if candidatesSet.ContainsKey expr then
        None
      else
        match expr with
        | B.Primitive (("||"|"&&"), args) ->
          None
        | B.Primitive ("!", [arg]) ->
          arg.Map (getSubterms (-pol)) |> ignore
          Some expr
        | B.Primitive ("==>", [a; b]) ->
          a.Map (getSubterms (-pol)) |> ignore
          b.Map (getSubterms pol) |> ignore
          Some expr
        | B.Forall _
        | B.Exists _ -> 
          Some expr
        | _ ->
          candidatesSet.[expr] <- true
          // subterms need to be added first to the candidate list
          expr.Map (getSubterms 0) |> ignore
          // then we can add the current term
          match getTriggerScore pol expr with
            | Some (vs, q) -> candidates.Add ((expr, vs, q))
            | None -> ()          
          Some expr

    let hasFreeVars (e:B.Expr) =
      let res = ref false
      e.Map (function 
               | B.Expr.Ref v when quantVarSet.ContainsKey v ->
                 res := true
                 None
               | _ -> None) |> ignore
      !res

    let willLoop tr =
      let isHigh = function
        | Some m ->
          if helper.Options.DumpTriggers >= 10 then Console.WriteLine ("check subst: " + substToString (Some m))
          Map.exists (fun _ -> function B.Expr.Ref _ -> false | e -> hasFreeVars e) m
        | None -> false
      Seq.exists (fun (t, _, _) -> isHigh (matchExpr Map.empty (tr, t))) candidates
      
    body.Map (getSubterms 1) |> ignore
    if dbg then
      Console.WriteLine ("infer: {0}", quantTok.Value)
      Console.WriteLine ("  BPL: {0}", body.ToString())
    for (tr, vs, q) in candidates do
      if List.forall vs.ContainsKey quantVars then
        if dbg then Console.WriteLine ("  cand: {0} q:{1}", tr, q)
        if willLoop tr then ()
        elif q >= 0 then
          resTrig.Add (q, [tr])

    let strigQual = 
      if resTrig.Count = 0 then -1
      else fst (Seq.maxBy fst resTrig)

    if strigQual <= 0 then
      let coveredVars = gdict()

      let rec loop mtrig =
        if coveredVars.Count = quantVarSet.Count then
          resTrig.Add (1, List.rev mtrig)
        else
          let checkCandidate cur (tr, (vs:Dict<_,_>), q) =
            let addedVars = Seq.filter (fun v -> not (coveredVars.ContainsKey v)) vs.Keys |> Seq.length
            if dbg then Console.WriteLine ("  check multi: {0} q:{1} v:{2}", tr, q, addedVars)
            if addedVars > 0 then
              match cur with
                | None -> Some (tr, q, addedVars, vs)
                | Some (_, q', av', _) when q' < q || (q' = q && av' < addedVars) -> Some (tr, q, addedVars, vs)
                | _ -> cur
            else cur
          match Seq.fold checkCandidate None candidates with
            | Some (tr, q, av, vs) ->
              if q <= strigQual then ()
              else
                if dbg then Console.WriteLine ("add multi: {0} q:{1} v:{2}", tr, q, av)
                for k in vs.Keys do coveredVars.[k] <- true
                loop (tr :: mtrig)
            | None -> ()
      loop []

    resTrig |> 
      Seq.groupBy fst |> 
      Seq.map (fun (q, l) -> (q, l |> Seq.map snd |> removeSubsumed |> addSkHack |> Seq.toList)) |> 
      Seq.sortBy fst |>       
      Seq.toList |>
      List.rev

  // the nested ptr_cast(ptr(...)) gets into triggers and causes trouble later
  let rec stripPtrCast (expr:B.Expr) = 
    let aux = function
      | B.FunctionCall (("$ptr_cast"|"$spec_ptr_cast"|"$phys_ptr_cast"), [B.FunctionCall ("$ptr", [_; r]); t]) ->
        Some (stripPtrCast (bCall "$ptr" [t; r]))
      | _ -> None
    expr.Map aux

  let fixupTrigger trigger =
    List.map stripPtrCast trigger
   
  let dumpTriggers  = function
    | ((_, []), _) ->
      helper.Warning (quantTok, 9121, "failed to infer triggers for '" + quantTok.Value + "'")
    | ((qual, chosen), rest) when helper.Options.DumpTriggers >= 1 ->
      let trToRawString tr = "{" + (List.map (fun t -> t.ToString ()) (fixupTrigger tr) |> String.concat ", ") + "}"
      let trToString tr = 
        let rec exprToStr = function
          | B.Expr.FunctionCall ("sk_hack", [e]) ->
            ":hint " + exprToStr e
          | e ->
            match invMapping.TryGetValue e with
              | true, x :: _ ->
                match e with 
                  | B.Expr.FunctionCall (("$idx"|"$dot"), _) ->
                    // this is going to be wrong when user writes *(a+i) instead of a[i]
                    "(&)" + x.Token.Value
                  | _ -> 
                    let v = x.Token.Value
                    if v = "" then "<<" + e.ToString() + ">>" else v
              | _ -> "<<" + (fixupTrigger [e]).Head.ToString() + ">>" // this shouldn't happen
        "{" + (List.map exprToStr tr |> String.concat ", ") + "}"
      let lev n = " at {:level " + (maxQuality - n).ToString() + "}"
      // this isn't really a warning, but this way it will automatically show up in VS and friends
      let spConcat f l = String.concat " " (Seq.map f l)
      helper.Warning (quantTok, 9122, "inferred triggers" + lev qual + ": " + spConcat trToString chosen + " for '" + quantTok.Value + "'")
      if helper.Options.DumpTriggers >= 2 && rest <> [] then
        let possibly = List.map (fun (q, trigs) -> lev q + ": " + spConcat trToString trigs) rest
        helper.Warning (quantTok, 9122, "could have inferred" + String.concat ", " possibly)
      if helper.Options.DumpTriggers >= 4 then
        helper.Warning (quantTok, 9123, "raw inferred triggers: " + spConcat trToRawString chosen)
    | _ -> ()
  
  let isRealTrigger = function
    | [B.Expr.FunctionCall ("sk_hack", _)] -> false
    | _ -> true

  member this.Run (body, triggers) = 
    let level = ref 0
    let shouldKeep = function
      | [B.Expr.FunctionCall ("trigger_level", [B.Expr.IntLiteral n])] ->
        level := (int) n
        false
      | _ -> true
    let triggers = List.filter shouldKeep triggers
    let selected = 
      let minQuality = maxQuality - !level
      function
        | [] -> (-1, []), []
        // these don't meet the criteria, but we have to select something
        | (n, lst) :: rest when n <= minQuality ->
          (n, lst), rest
        | lst ->
          let rec aux n acc = function
            | (n, lst) :: rest when n >= minQuality ->
              aux n (acc @ lst) rest
            | rest -> (n, acc), rest
          aux 0 [] lst

    let newBody = stripPtrCast body
    let triggers =
      if (List.filter isRealTrigger triggers).IsEmpty then
        let ((_, newTrig), _) as toDump = selected (doInfer body)
        dumpTriggers toDump
        triggers @ List.map fixupTrigger newTrig
      else
        if helper.Options.DumpTriggers >= 3 then
          // still infer and ignore the results
          dumpTriggers (selected (doInfer body))
        triggers
    newBody, triggers
          
