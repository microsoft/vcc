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
 
 module Normalizer =

  type private StackArrayDetails = SAR of Variable * Type * int * bool

  type private Contract = {
    Requires : list<Expr>;
    Ensures : list<Expr>;
    Reads : list<Expr>;
    Writes : list<Expr>;
    Decreases : list<Expr>;
  }

  let isSpecMacro (fn:Function) = hasCustomAttr AttrSpecMacro fn.CustomAttr

  let specMacroBody fn =
    if not (isSpecMacro fn) then None
    else
      match fn.Ensures with
        | [Expr.Prim (_, Op ("==", _), ([Result _; e]|[e; Result _]))]
        | [Expr.Macro (_, "_vcc_set_eq", ([Result _; e]|[e; Result _]))] ->
          Some e
        | _ -> None
 

  // ============================================================================================================          

  let rec doHandleComparison helper self = function
    | Expr.Prim (c, op, [Expr.Cast ({ Type = Integer _ }, _, a1); Expr.Cast ({ Type = Integer _ }, _, a2)]) 
      when op.IsEqOrIneq && a1.Type = Type.Bool && a2.Type = Type.Bool -> 
      Some (self (Expr.Prim (c, op, [a1; a2])))
    | Expr.Prim ({ Type = Type.Integer _ } as c, op, args) when op.IsEqOrIneq ->
      Some (self (Expr.Cast (c, Processed, Expr.Prim ({ c with Type = Type.Bool }, op, args))))
    | Expr.Prim (c, op, [a1; a2]) when op.IsEqOrIneq ->
      match a1.Type, a2.Type with
        | PtrSoP(t, _), PtrSoP(t', _) ->
          let macro = if op.IsEq then "_vcc_ptr_eq" else "_vcc_ptr_neq"
          Some (self (Expr.Macro (c, macro, [self a1; self a2])))
        | _ -> None
    | Expr.Dot (c, e, ({ Type = Array (t, _) } as f)) when c.Type <> SpecPtr t && c.Type <> PhysPtr t ->
      Some (self (Expr.MkDot (c, e, f)))
    | _ -> None
  

  // ============================================================================================================          

  let doHandleConversions = 
    let rec doHandleConversions' inGroupInvariant self = function
      | Expr.Cast ({ Type = ObjectT}, _, e) -> 
        match e.Type with
          | Ptr _ | ObjectT | Claim -> Some (self e)
          | _ -> None
      | Expr.Cast ({Type = Ptr(t1) } as ec, cs, Expr.Cast ({ Type = (ObjectT | Ptr(Type.Ref(_) | Void)) }, _, e')) when t1 <> Void -> Some (self (Cast(ec, cs, e')))
      | Expr.Cast ({ Type = t1 }, (Processed|Unchecked), Expr.Cast ({ Type = t2 }, (Processed|Unchecked), e')) when t1.IsPtr && t2.IsPtr && e'.Type = t1 -> Some (self e')
      | Expr.Cast ({ Type = Bool }, _, Expr.Cast (_, _, e')) when e'.Type = Bool -> Some (self e')
      | Expr.Cast ({ Type = PtrSoP(_, isSpec) } as c, _, Expr.IntLiteral (_, ZeroBigInt)) -> 
        Some (self (Expr.Cast (c, Processed, Expr.Macro ({c with Type = Type.MkPtr(Void, isSpec)}, "null", []))))
      | Expr.Cast ({ Type = PtrSoP(_, isSpec) } as c, _, e) when e.Type._IsInteger ->
        match e.Type with
          | Integer k ->
            Some (self (Expr.Cast (c, Processed, Expr.Macro ({c with Type = Type.MkPtr(Void, isSpec)}, "_vcc_" + (Type.IntSuffix k) + "_to_ptr" , [e]))))
          | _ -> None
      | Expr.Cast ({ Type = Integer k }, _, Expr.IntLiteral (c, n)) ->
        let (min, max) = Type.IntRange k
        if min <= n && n <= max then
          Some (Expr.IntLiteral ({ c with Type = Integer k }, n))
        else
          None 
      | Expr.Cast ({ Type = MathInteger Signed}, _, expr) when expr.Type._IsInteger -> Some(self(expr))
      | Expr.Cast ({ Type = MathInteger Unsigned}, _, Expr.IntLiteral (c, n)) when n >= bigint.Zero -> Some(Expr.IntLiteral(c,n))
      | Expr.Cast(ec, _, This(tc)) when inGroupInvariant && ec.Type = tc.Type -> 
        None // Do not remove this cast because the type of 'this' will change later on
      | Expr.Cast (_, _, e') as e ->
        match e'.Type, e.Type with
          | (Ptr _|ObjectT), Ptr Void -> Some (self e')
          | _, Type.Ref { Name = "#Object" } -> Some (self e')
          | t, t' when t = t' -> Some (self e')
          | _ -> None
      | Expr.Macro(c, "group_invariant", args) -> Some(Expr.Macro(c, "group_invariant", List.map (fun (e:Expr) -> e.SelfMap(doHandleConversions' true)) args))
      | Expr.Call(c, ({Name = "_vcc_inv_group"} as fn), targs, args) -> Some(Expr.Call(c, fn, targs, List.map (fun (e:Expr) -> e.SelfMap(doHandleConversions' true)) args))
      | _ -> None
    doHandleConversions' false
    
  let handlePurePtrEq (helper:TransHelper.TransEnv) decls =
    let rec isNull = function
      | Expr.Cast (_, _, e) -> isNull e
      | Expr.Macro (_, "null", []) -> true
      | _ -> false

    let aux (ctx:ExprCtx) self = function
      | Expr.Cast (c, _, p) when c.Type = Type.Bool && p.Type.IsPtr ->
        Some (Expr.Macro (c, "_vcc_ptr_neq_null", [self p]))
      | Expr.Macro (c, ("_vcc_ptr_eq"|"_vcc_ptr_neq" as name), [p1; p2]) ->
        if isNull p1 then
          Some (Expr.Macro (c, name + "_null", [self p2]))
        else if isNull p2 then
          Some (Expr.Macro (c, name + "_null", [self p1]))
        else if ctx.IsPure then
          match p1.Type, p2.Type with
            | Ptr(t1), Ptr(t2) ->
              Some (Expr.Macro (c, name + "_pure", [self p1; self p2]))
            | ObjectT, Ptr(_)
            | Ptr(_), ObjectT
            | ObjectT, ObjectT ->
              Some (Expr.Macro (c, name + "_pure", [self p1; self p2]))
            | _ ->
              helper.Oops (p1.Token, "cannot compare non-pointers as pointers: " + p1.Type.ToString() + " == " + p2.Type.ToString())
              None
        else None
      | _ -> None

    deepMapExpressionsCtx aux decls

  let handleConversions helper = 
    deepMapExpressions (doHandleComparison helper) >> 
    deepMapExpressions doHandleConversions >>
    handlePurePtrEq helper

  // ============================================================================================================      
  
  let init (helper:TransHelper.TransEnv) =
    let internalFunction = TransUtil.internalFunction helper
 
    // ============================================================================================================
    
    let removeFixedSizeArraysAsParameters decls =
      let map = new Dict<_,_>()
      let replParm (p : Variable) =
        match map.TryGetValue p with
          | true, p -> p
          | _ ->
            match p.Type with
              | Array (t, _) ->
                let p' = { p with Type = Type.MkPtr(t, p.IsSpec) }
                map.Add (p, p')
                p'          
              | _ -> p       
              
      let replRef self = function
        | VarDecl (c, v, attr) when replParm v <> v -> Some (VarDecl (c, replParm v, attr))
        | Macro (c, "=", [Expr.Ref (c', v); Expr.Deref (_, e)]) when map.ContainsKey v ->
          Some (Macro (c, "=", [Expr.Ref ({c' with Type = map.[v].Type }, map.[v]); self e]))
        | Macro (c, "&", [Expr.Ref (_, v)]) when map.ContainsKey v -> Some (Expr.Ref ({ c with Type = map.[v].Type }, map.[v]))
        | Expr.Ref (c, v) when map.ContainsKey v ->
          helper.Oops (c.Token, "fixed size array used as value")
          None
        | _ -> None        
      for d in decls do
        match d with          
          | Top.FunctionDecl h ->
            h.Parameters <- List.map replParm h.Parameters          
          | _ -> ()
      deepMapExpressions replRef decls
      
    // ============================================================================================================
   
    let makeQuantifiedVarsUnique (expr:Expr) =
      let aux self = function
        | Quant(ec, qd) ->
          let vs', replace = Variable.UniqueCopies (fun x -> x) qd.Variables
          let qd' = { qd with Variables = vs';
                              Triggers = List.map (List.map(replace)) qd.Triggers;
                              Condition = Option.map replace qd.Condition;
                              Body = replace qd.Body }
          Some(Quant(ec, qd'))
        | _ -> None
      expr.SelfMap aux

    let handleLemmas self = 
      function 
        | Assert (c, e, trigs) -> 
          let e = self e 
          Some (Expr.MkBlock [Assert (c, e, trigs); Assume (c, makeQuantifiedVarsUnique e)])
        | Macro (_, "loop_contract", _) as expr -> Some expr
        | _ -> None      
         
    // ============================================================================================================
    
    let inlineCall pref self call =
      match call with
        | Call (ec, fn, _, args) ->
          let callTok = ec.Token
          let inExpansion = fun () -> "from expansion of '" + pref + callTok.Value + "'"
          
          let overrideMacroLocation (expr:Expr) =
            let orig = expr.Token
            let related = new ForwardingToken (orig, orig.Related, inExpansion) :> Token
            let primary = new ForwardingToken (callTok, Some related, fun () -> orig.Value)
            expr.WithCommon { expr.Common with Token = primary }

          let updateArgLocation (expr:Expr) =
            let orig = expr.Token
            let related = new ForwardingToken (fn.Token, orig.Related, inExpansion) :> Token
            let primary = new ForwardingToken (orig, Some related, fun () -> orig.Value)
            expr.WithCommon { expr.Common with Token = primary }
          let args = List.map (fun expr -> ((self expr) : Expr).DeepMap updateArgLocation) args

          let subst = gdict()
          List.iter2 (fun f a -> subst.Add (f, a)) fn.Parameters args 

          (fun (expr:Expr) ->
            (expr.DeepMap overrideMacroLocation).Subst subst |> makeQuantifiedVarsUnique)
        | _ -> die()

    let inlineSpecMacros decls =
      
      let rec doInline expandedFns self =
        function 
          | Call (ec, fn, targs, args) when isSpecMacro fn ->
            if Set.contains fn.UniqueId expandedFns then
              helper.Error (fn.Token, 9740, "recursive spec macro '" + fn.Name + "'", Some ec.Token)
              None
            else
              let fn' = fn.Specialize(targs, false)
              match specMacroBody fn' with
                | Some e ->
                  if e.HasSubexpr (function Result _ -> true | _ -> false) then
                    helper.Error (fn.Token, 9714, "'result' cannot be used recursively in a spec macro definition", Some ec.Token)
                    None
                  else      
                    Some ((inlineCall "" self (Call({ec with Type = fn'.RetType}, fn', [], args)) e).SelfMap((doInline (Set.add fn.UniqueId expandedFns))))
                | _ ->
                  helper.Error (fn.Token, 9715, "spec macros should have one ensures clause of the form 'result == expr'", Some ec.Token)
                  None
          | _ -> None
      deepMapExpressions (doInline Set.empty) decls |>
        List.filter (function Top.FunctionDecl f when isSpecMacro f -> false | _ -> true)    

    // ============================================================================================================

    let deepSplitConjunctions self = 
      let aux self = function
        | Quant (ec, q) ->
          let q = { q with Body = self q.Body }
          let mkQ (e:Expr) = 
            let related = 
              match ec.Token with
                | :? ForwardingToken as t -> t.Related
                | _ -> None
            let t = forwardingToken ec.Token related (fun () -> e.Token.Value + " in " + ec.Token.Value)
            let vars = gdict()
            for v in q.Variables do
              vars.Add (v.UniqueId, true)
            let aux _ = function
              | Expr.Ref (_, v) ->
                vars.Remove v.UniqueId |> ignore
                true
              | _ -> true
            e.SelfVisit aux
            q.Triggers |> List.iter (fun l -> l |> List.iter (fun e -> e.SelfVisit aux))
            let newVars = q.Variables |> List.filter (fun v -> not (vars.ContainsKey v.UniqueId))
            makeQuantifiedVarsUnique (Quant ({ ec with Token = t.Token }, { q with Body = e ; Variables = newVars }))
          match splitConjunctionEx true q.Body with
            | [] -> die()
            | [_] -> Some (Quant (ec, q))
            | x :: xs -> 
              Some (List.fold mkAnd (mkQ x) (List.map mkQ xs))
        | CallMacro (_, "_vcc_split_conjunctions", [], [e]) -> Some(self e) // strip nested occurrences of split_conjunctions
        | CallMacro(ec, ("_vcc_inv2"), [], [e]) ->
          let stripLabelsAndSubstituteThis subst (expr : Expr) = 
            let stripLabelsAndSubstituteThis' self = function
              | Macro(_, "labeled_invariant", [_; inv]) -> Some(self inv)
              | This(_) -> Some(subst)
              | _ -> None
            expr.SelfMap(stripLabelsAndSubstituteThis')
          match e.Type with 
            | Ptr(Type.Ref(td)) ->  Some(td.Invariants |> List.map (stripLabelsAndSubstituteThis e) |> List.fold mkAnd Expr.True)
            | _ -> None
        | _ -> None
      function 
        | CallMacro (_, "_vcc_split_conjunctions", [], [e]) ->
          Some (e.SelfMap aux)
        | _ -> None      
         
    // ============================================================================================================
    
    let splitConjunctionsInAssertions self = 
      function 
        | Assert (c, e, trigs) -> 
          let exprs = splitConjunctionEx true (self e)
          if exprs.IsEmpty then die()          
          Some (Expr.MkBlock (exprs |> List.map (fun e -> Assert ({ e.Common with Type = Type.Void }, e, trigs))))
        | _ -> None      
         
    // ============================================================================================================
    
    let handleClaims self = function
      | Call (c, ({ Name = ("_vcc_claim"|"_vcc_upgrade_claim" as name) } as fn), _, args) ->
        match List.rev args with
          | [_] ->
            helper.Error(c.Token, 9710, "claim(...) requires at least one object and a claimed property")
            None
          | x :: xs ->
            if (x.Type._IsPtr) then
              helper.Error(x.Token, 9711, "claimed property must not be of pointer type")
            Some (self (Macro (c, name.Replace("_vcc_", ""), Expr.Pure (x.Common, convertToBool (fun x -> x) x) :: (List.rev xs))))
          | _ -> 
            helper.Oops (c.Token, "no arguments to claim")
            None
            
      | Call (c, { Name = "_vcc_unclaim" }, _, args) ->
        Some (Stmt (c, Macro (c, "unclaim", List.map self args)))

      | Call (c, { Name = "_vcc_begin_update" }, _, args) ->
        Some (Stmt (c, Macro (c, "begin_update", List.map self args)))
        
      | Atomic (c, objs, body) -> 
        let errorIfNotPtrToStruct (expr : Expr) =
          match expr.Type with
            | Ptr(Volatile(Type.Ref(_))) 
            | Ptr(Type.Ref(_)| Claim) 
            | Type.ObjectT -> ()
            | t -> helper.Error(expr.Token, 9668, "'" + expr.Token.Value + "' has non-admissible type '" + t.ToString() + "' for atomic")
        List.iter errorIfNotPtrToStruct objs
        Some (Atomic (c, List.map (fun (e:Expr) -> Pure (e.Common, self e)) objs, self body))
        
      | _ -> None
    
    // ============================================================================================================
    
    let fixupOld (ctx:ExprCtx) self = function
      | Old(_, (CallMacro(_, "_vcc_by_claim", _, _)), _) -> None
      | Old (c, _, _) as o when not ctx.IsPure -> Some (Expr.Pure (c, o))
      | _ -> None
    
    // ============================================================================================================

    let addExplicitReturn =
      let doDecl = function
        | Top.FunctionDecl ({ RetType = Void; Body = Some b } as f) ->
          let rec addIt = function
            | Block (c, lst, cs) as e ->
              let rec repl acc = function
                | [x] -> Block (c, List.rev (addIt x :: acc), cs)
                | x :: xs -> repl (x :: acc) xs
                | [] -> Block (c, [], cs)
              repl [] lst
            | Skip(c) -> Return (c, None)
            | x -> x
          f.Body <- Some (addIt b)
          Top.FunctionDecl f        
        | x -> x
      List.map doDecl

    // ============================================================================================================

    let miscNorm =
      let stringLiterals = new Dict<_,_>()
                
      // TODO rename this
      let doFixQuantifiers self = function
        | Expr.Quant (ec, { Kind = k1;
                            Variables = vars1;
                            Triggers = triggers1;      
                            Condition = None;
                            Body = Expr.Quant (_, ({ Kind = k2;                                                   
                                                     Triggers = triggers2; 
                                                     Variables = vars2 } as q)) } ) when k1 = k2 ->          
          match triggers1, triggers2 with
            | [], t
            | t, [] -> Some (self (Expr.Quant (ec, { q with Variables = vars1 @ vars2; Triggers = t })))
            | _ -> None

        | Expr.SizeOf(ec, Type.TypeVar(_)) -> None
        | Expr.SizeOf(ec, t) -> Some(IntLiteral(ec, new bigint(t.SizeOf)))
        | Expr.Call (c, { Name = "_vcc_inv_group"}, _, [Expr.Cast (_, _, EString (c', v)); groupInv]) ->
          Some (Expr.Macro (c, "group_invariant", [Expr.Macro (c', v, []); self groupInv]))
        | Macro (ec, "\\castlike_precise", [EString (_, v)]) ->
          Some (Expr.Macro (ec, "precise_string", [UserData (ec, v)]))
        | EString (c, v) ->
          let id =
            match stringLiterals.TryGetValue v with
              | (true, id) -> id
              | _ -> 
                let id = stringLiterals.Count
                stringLiterals.Add (v, id)
                id
          Some (Expr.Macro (c, "_vcc_get_string_literal", [mkInt id; mkInt v.Length]))
        | Expr.Macro (c, "ptr_addition", [e1; e2]) as expr ->
          let ptr, off =
            if e1.Type._IsPtr then (e1, e2)
            else (e2, e1)
          let elType = elementTypeForArithmetic ptr.Type
          let off =
            match extractArraySize helper expr elType off with
              | Some e -> e
              | None -> Expr.IntLiteral (off.Common, one)
          Some (self (Expr.Index (c, ptr, off)))
        | Expr.Prim (c, Op ("-", _), [e1; e2]) when e1.Type._IsPtr && e2.Type._IsPtr ->      
          match e1.Type, e2.Type with
            | Ptr t1, Ptr t2 when t1 = t2 ->
                let expr = Expr.Macro (c, "_vcc_byte_ptr_subtraction", [e1; e2])
                let expr =
                  if t1.SizeOf = 1 then
                    expr
                  else
                    Expr.Prim (c, Op ("/", Processed), [expr; mkInt t1.SizeOf])
                Some (self expr)
            | _ -> 
              helper.Error (c.Token, 9601, "pointer types in subtraction differ", None)
              None
        
        | Expr.Prim (c, (Op (("<"|">"|"<="|">="), _) as op), [e1; e2]) when e1.Type._IsPtr && e2.Type._IsPtr ->
          let ec = { c with Type = Type.Integer IntKind.Int64 }
          Some (self (Expr.Prim (c, op, [Expr.Macro (ec, "_vcc_byte_ptr_subtraction", [e1; e2]);
                                         Expr.IntLiteral (ec, zero)])))
        
        | Expr.Prim (c, (Op ("-", _) as op), [e1; e2]) when e1.Type._IsPtr && not e2.Type._IsPtr ->  
          let tok = if e2.Token <> Token.NoToken then e2.Token else e1.Token    
          Some (self (Expr.Macro (c, "ptr_addition", [e1; Expr.Prim ({ e2.Common with Token = tok }, Op("-", CheckedStatus.Processed), [e2])])))
          
        | Expr.Prim (c, Op ("-", ch), [e]) ->
          Some (self (Expr.Prim (c, Op ("-", ch), [Expr.IntLiteral (c, zero); e])))
        
        | Expr.Prim (c, (Op(("<<"|">>"), _) as op), [e1; Cast(_,_, e2)]) ->
          Some(self (Expr.Prim(c, op, [e1; e2])))
        
        | Expr.Prim (c, (Op (("&"|"|"|"^"), _) as op), [e1; e2]) when e1.Type = Bool || e2.Type = Bool ->
          let toInt (e:Expr) = 
            if e.Type = Bool then
              Cast ({ e.Common with Type = Integer IntKind.Int32 }, Processed, e)
            else e
          let c = if c.Type = Bool then { c with Type = Integer IntKind.Int32 } else c
          Some (self (Expr.Prim (c, op, [toInt e1; toInt e2])))
        
        // this is an easy one ;-)
        | Expr.Prim (_, Op ("+", _), [e]) -> Some (self e)
        | Expr.Macro (c, "stack_allocate_array", [s; isSpec]) -> 
          match c.Type, s with 
          | Ptr elemType, Expr.IntLiteral(_, sz) ->
            Some (Expr.Cast(c, Processed, 
                            Expr.Call({ c with Type = PhysPtr Void }, internalFunction "stack_alloc", [Type.Array(elemType, (int)sz)], [Expr.Macro(bogusEC, "stackframe", []); isSpec]))) 
          | _ -> die()        
        | Expr.Cast ({ Type = Ptr t } as c, _, Expr.Call (_, { Name = "malloc" }, _, [sz])) as expr ->
          match extractArraySize helper expr t sz with
            | None ->
              Some (Expr.Call (c, internalFunction "alloc", [], [typeExpr t]))
            | Some elts ->
              // TODO overflow! we get rid of multiplication here
              let t' = typeExpr t
              let arrTy = Expr.Macro (t'.Common, "_vcc_array", [t'; self elts])
              Some (Expr.Cast (c, Processed, 
                               Expr.Call ({ c with Type = PhysPtr Void }, internalFunction "alloc", [], [arrTy])))
        | Expr.Call (c, { Name = "free" }, _, [p]) ->
          Some (Expr.Call (c, internalFunction "free", [], [self p]))
        | Expr.Macro (c, "&", [This(c')]) when not c'.Type._IsPtr ->
          Some (self (This(c)))
        | CallMacro (c, "_vcc_create_set", _, pars) ->
          match pars with
            | [] 
            | [_] -> Some(Expr.Macro(c, "_vcc_set_empty", []))
            | _ :: rest ->
              let mkSingleton (e:Expr) = 
                match e.Type with 
                  | Type.ObjectT 
                  | Type.PhysPtr _
                  | Type.SpecPtr _
                  | Type.Claim -> ()
                  | _ -> helper.Error(e.Token, 9706, "Invalid type '" + e.Type.ToString() + "' in SET expression.")
                Expr.Macro({e.Common with Type = c.Type}, "_vcc_set_singleton", [e])
              let mkUnion (e1:Expr) (e2:Expr) = Expr.Macro(e1.Common, "_vcc_set_union", [e1;e2])
              let rec createUnion exprs =
                let rec splitAt n acc (l : 'a list) =
                  if (n = 0 || l.IsEmpty) then (List.rev acc, l)
                  else match l with
                       | x :: xs -> splitAt (n-1) (x::acc) xs
                       | _ -> die()
                match exprs with
                | [] -> die()
                | [expr] -> mkSingleton expr
                | _ -> 
                  let (a,b) = splitAt (exprs.Length / 2) [] exprs
                  mkUnion (createUnion a) (createUnion b)
              Some(rest |> List.map self |> createUnion)
   
        | Expr.Return (ec, Some e) when e.Type = Type.Void ->
          helper.Error (ec.Token, 9738, "expressions of type void cannot be used as an argument to a return statement")
          None
           
        | _ -> None
    
      deepMapExpressions doFixQuantifiers
        
    // ============================================================================================================

    let handleTriggerHints self = 
      let getLabel = function
        | Macro (_, "labeled_expr", [Label (_, n); e]) -> Some (n.Name, e)
        | _ -> None
      let isLabeled = getLabel >> Option.isSome
      let fixOneTrigger = function
        | x :: xs ->
          if List.exists isLabeled xs then
            helper.Error (x.Token, 0, "only the first expression in trigger is allowed to have label")
          match getLabel x with
            | Some ("hint", x) ->
              (x :: xs) |> List.map (fun e -> [Expr.Macro (e.Common, "trigger_hint", [e])])
            | Some ("level", (IntLiteral (_, n) as e)) when xs.IsEmpty ->
              [[Expr.Macro (x.Common, "trigger_level", [e])]]
            | Some (name, e) ->
              helper.Error (x.Token, 0, "unrecongized quantifier trigger hint")
              []
            | None ->
              [x :: xs]
        | [] -> die()
              
      function
        | Expr.Quant (ec, q) ->
          Some (Expr.Quant (ec, { q with Triggers = List.collect fixOneTrigger q.Triggers; Body = self q.Body}))
        | _ -> None

    // ============================================================================================================
    
    let normalizeWrites decls =
      let fixOne (e:Expr) =
        match e.Type with
          | MathTypeRef "\\objset"
          | ObjectT
          | Array _
          | Ptr _ -> e         
          | _ ->
            match e with
              | CallMacro (c, "_vcc_ref_cnt", _, [p]) ->
                //helper.Error (c.Token, 9999, "the ref_cnt(...) no longer resides in memory and cannot be written to", None)
                p
              | _ -> e // we will catch this error later
                
      let fixWrites = function
        | Top.FunctionDecl f ->
          f.Writes <- List.map fixOne f.Writes
          f.Reads <- List.map fixOne f.Reads
        | _ -> ()
      List.iter fixWrites decls
      decls       
   
    // ============================================================================================================
    
    let inlineAtomics decls =
      let inlines = gdict()
      let isntInline = function
        | Top.FunctionDecl fd ->
          if hasCustomAttr AttrAtomicInline fd.CustomAttr then
            if fd.IsPure then
              helper.Error(fd.Token, 9667, "Pure function '" + fd.Name + "' cannot be inlined.")
              true
            else 
              if fd.Requires.Length > 0 || fd.Ensures.Length > 0 || fd.Reads.Length > 0 || fd.Writes.Length > 0 then
                helper.Warning(fd.Token, 9117, "Contracts of inlined function '" + fd.Name + "' are ignored.")
              inlines.Add (fd, true)
              false
          else true
        | _ -> true
        
      let rec _inline inSpec self = function
        | Macro(ec, "spec", [body]) -> Some(Macro(ec, "spec", [body.SelfMap(_inline true)]))
        | Call (c, f, targs, args) when inlines.ContainsKey f ->
          let f = f.Specialize(targs, true)
          let map = gdict()
          let bindIn (formal:Variable) = function
            | Expr.Ref _ as r -> 
              map.Add (formal, r)
              []
            | actual ->
              let c = actual.Common
              let cvoid = { c with Type = Void }
              let tmp = getTmp helper formal.Name formal.Type VarKind.Local
              map.Add (formal, Ref (c, tmp))
              [VarDecl (cvoid, tmp, []);
               Macro (cvoid, "=", [ Ref ({ c with Type = tmp.Type }, tmp); actual ])]
          let bindOut (formal:Variable) = function
            | Macro(_, "out", [actual]) ->
              let c = actual.Common
              let cvoid = { c with Type = Void }
              let tmp = getTmp helper formal.Name formal.Type VarKind.SpecLocal
              map.Add (formal, Ref (c, tmp))
              VarDecl (cvoid, tmp, []), Expr.SpecCode(Macro (cvoid, "=", [ actual; Ref ({ c with Type = tmp.Type }, tmp)]))
            | _ -> die()
          let inPars, inActuals, outPars, outActuals = 
            let rec loop (formals:Variable list) actuals fiAcc aiAcc foAcc aoAcc = 
              match formals, actuals with
                | [], [] -> List.rev fiAcc, List.rev aiAcc, List.rev foAcc, List.rev aoAcc
                | ({Kind = VarKind.OutParameter} as formal)::formals', actual::actuals' -> 
                  loop formals' actuals' fiAcc aiAcc (formal::foAcc) (actual::aoAcc)
                | formal::formals', actual::actuals' -> loop formals' actuals' (formal::fiAcc) (actual::aiAcc) foAcc aoAcc
                | _ -> die()
            loop f.Parameters args [] [] [] []

          let inits = List.map2 bindIn inPars inActuals |> List.concat
          let declsForOutPars, outParAssignmentOnExit = List.map2 bindOut outPars outActuals |> List.unzip
          let resVar = getTmp helper "res" f.RetType (if f.IsSpec || inSpec then VarKind.SpecLocal else VarKind.Local)
          let subst self = function
            | Ref (_, v)  ->
              match map.TryGetValue(v) with
                | true, v' -> Some (map.[v])
                | false, _ -> None
            | VarDecl (_, v, _) when map.ContainsKey v ->
              Some(Skip({c with Type = Type.Void}))
            | Return (c, Some e) ->              
              Some (Macro (c, "=", [Ref (c, resVar); self e]))
              // TODO check if it the return doesn't disturn control flow
              // TODO look for gotos and such
            | Return (c, None) ->
              Some(Skip({c with Type = Type.Void}))
            | _ -> None            
          let body = 
            match f.Body with
              | Some stmt -> Macro ({c with Type = Type.Void}, "inlined_atomic", [stmt.SelfMap subst])
              | None -> Comment(bogusEC, "inlined function without body")
          let body =
            if f.RetType = Void then
              body :: outParAssignmentOnExit
            else
              [VarDecl ({c with Type = Void}, resVar, []); body] @ outParAssignmentOnExit @ [Ref (c, resVar)]
          Some (Expr.MkBlock (inits @ declsForOutPars @ body))
        | d -> None
              
      let decls = List.filter isntInline decls      
      decls |> deepMapExpressions (_inline false)
   
    // ============================================================================================================
   
    let normalizeAtomicOperations self = function
      | Macro(ec, "atomic_op", args) -> 
        let splitLastTwo = 
          let rec splitLastTwo acc = function
          | [x;y] -> x, y, List.rev acc
          | x :: xs -> splitLastTwo (x :: acc) xs
          | [_]
          | [] -> die()
          splitLastTwo []
        let cvoid = {ec with Type = Void}
        let ghostUpdate, op, atomicParameters = splitLastTwo args
        let tmp = getTmp helper "atomic_op" op.Type VarKind.Local
        let res = Expr.Ref({bogusEC with Type = op.Type}, tmp)
        let op' = Macro(op.Common, "=", [res; op])
        let ghostUpdate' = 
          match ghostUpdate with
            | Macro(_, "null", []) -> []
            | _ ->
              let fixupResult self = function
                | Result _ -> Some(res)
                | _ -> None
              [Expr.SpecCode(ghostUpdate.SelfMap fixupResult)]
        let stmts = VarDecl(cvoid, tmp, []) :: Atomic(cvoid, atomicParameters, Expr.MkBlock (op':: ghostUpdate')) :: [res]
        Some(Block(ec, stmts, None))
      | _ -> None
    
    // ============================================================================================================

    let buildSkinnyExpose ec writes objects sbody =
      let ptrsetEC = { bogusEC with Type = Type.PtrSet }
      let empty = Macro (ptrsetEC, "_vcc_set_empty", [])
      let single e = Macro (ptrsetEC, "_vcc_set_singleton", [e])
      let union a b = Macro (ptrsetEC, "_vcc_set_union", [a; b])
      let setify acc (e:Expr) =
        let e = 
          match e.Type with 
            | MathTypeRef "\\objset" -> e
            | _ -> single e
        if acc = empty then e
        else union acc e
        
      let setify = List.fold setify empty
      let isNonStruct (e:Expr) = 
        match e.Type with
          | Ptr (Type.Ref { Kind = Struct|Union }) -> false
          | _ -> true
        
      let fnToken (obj:Expr) name =
        { forwardingToken obj.Token None (fun () -> name + "(" + obj.Token.Value + ")") with Type = Void }
    
      let prestateVar = getTmp helper "prestate" Type.MathState VarKind.SpecLocal
      let nowstate = Expr.Macro ({ bogusEC with Type = Type.MathState }, "_vcc_current_state", [])        
      let prestate = mkRef prestateVar
      let saveState = [VarDecl (bogusEC, prestateVar, []); Expr.SpecCode(Macro (bogusEC, "=", [prestate; nowstate]))]
      let postUnwrapVar = getTmp helper "postUnwrap" Type.MathState VarKind.SpecLocal
      let postUnwrap = mkRef postUnwrapVar
      let savePostUnwrapState = [VarDecl (bogusEC, postUnwrapVar, []); Expr.SpecCode(Macro (bogusEC, "=", [postUnwrap; nowstate]))]
      let old (e:Expr) = Old ({ e.Common with Token = new WarningSuppressingToken (e.Token, 9106) }, prestate, e)
        
      let writeSet = old (setify writes)
      let primWriteSet = old (setify (List.filter isNonStruct writes))
        
      let writesCheck =
        let assrt id msg name =
          let tok = afmte id msg objects
          Expr.MkAssert (Macro (tok, "_vcc_updated_only_" + name, [postUnwrap; nowstate; writeSet]))
        [assrt 8530 "skinny_expose({0}, ...) body has written at an unlisted location" "values";
          assrt 8530 "skinny_expose({0}, ...) body has written at an unlisted location in a domain" "domains"]
        
      let introduceWrapUnwrap acc obj =
        let obj' = old obj
        let wrapLike name vcc_name =
          let tok = fnToken obj name
          Stmt (tok, Macro (tok, vcc_name, [obj']))
            
        let owns st = Macro ({ bogusEC with Type = Type.PtrSet }, "_vcc_owns", [st; obj])
        let checkOwns = 
          let tok = afmte 8531 "owns({0}) was updated inside skinny_expose(...)" [obj]
          Expr.MkAssert (Prim (tok, Op ("==", Processed), [owns nowstate; owns prestate]))
            
        [wrapLike "unwrap" "_vcc_unwrap"] @ acc @ 
        [checkOwns;
          wrapLike "wrap" "_vcc_wrap_non_owns"]
        
      let finalAssume =
        Expr.MkAssume (Macro (boolBogusEC(), "_vcc_domain_updated_at", [prestate; nowstate; old objects.Head; primWriteSet ]))
          
      let totalBody = 
        saveState @
        (List.rev objects |> List.fold introduceWrapUnwrap (savePostUnwrapState @ [sbody] @ writesCheck)) @
        [finalAssume]
          
      Expr.MkBlock totalBody

    let normalizeSkinnyExpose self = function
      | Macro (ec, "while", [Macro (_, "loop_contract", contract); CallMacro (_, "_vcc_skinny_expose", _, objects); body]) ->
        let extractWrites acc = function
          | Assert (_, Macro (_, "loop_writes", [e]), []) -> e :: acc
          | e ->
            helper.Error (e.Token, 9674, "skinny_expose(...) does not allow invariants, only writes(...)")
            acc
        let writes = List.rev (List.fold extractWrites [] contract)
        Some (buildSkinnyExpose ec writes objects (self body))   
      | Macro (ec, "skinny_expose", Macro (_, "se_writes", writes) :: body :: objects) ->
        Some (buildSkinnyExpose ec writes objects (self body))   
      | _ -> None
    
    // ============================================================================================================

    let removeDerefFromOutParams self = function
      | Deref(ec, Ref(_, ({Kind = VarKind.OutParameter} as v))) -> Some(Ref(ec, v))
      | _ -> None
    
    // ============================================================================================================

    let normalizeInitializers self = 
    
      let splitOfLast l = 
        let rl = List.rev l
        rl.Head, List.rev (rl.Tail)
    
      let subst v expr (e:Expr) = 
        let doSubst _ = function
          | Expr.Ref(_,v) -> Some(expr)
          | _ -> None
        e.SelfMap(doSubst)
        
      let shouldHandle = function
        | Type.Ref td -> td.IsRecord
        | _ -> false
        
      let foldBackFieldAssignments ec tmp =
        let rec buildDotExpr tgt = function
          | Ref(_,v) when v = tmp -> tgt
          | Deref(_, Dot(_, Macro(_, "&", [e]), f)) ->
            Expr.MkDot(buildDotExpr tgt e, f)
          | _ -> die()
        let rec foldBackFieldAssignments' (tgt : Expr) = function
          | Macro(_, "=", [Ref(_,v); e]) when v = tmp -> e
          | Macro(_, "=", [fieldExpr; e]) -> 
            Macro({tgt.Common with Type = tgt.Type}, "vs_updated", [buildDotExpr tgt fieldExpr; self e])
          | Block(_, stmts, _) -> recurse tgt stmts
          | _ -> tgt
        and recurse = List.fold foldBackFieldAssignments' 
        recurse (Macro(ec, "vs_zero",  []))
        
      function
        | Block(ec, stmts, _) when shouldHandle (ec.Type) ->
            match splitOfLast stmts with 
              | Ref(ec, v), stmts' -> Some(foldBackFieldAssignments ec v stmts')
              | _ -> None        
        | _ -> None
    
    // ============================================================================================================
    
    let reportGenericsErrors decls = 
    
      let reportGenericsErrors' self =
        let errorForVarType = function
          | Expr.Ref _ -> None // these are caught for the declaration
          | e ->
            match e.Type with
              | TypeVar({Name = name}) -> 
                helper.Error(e.Token, 9691, "Expression '" + e.Token.Value + "' is of generic type '" + name + "'; only pointers to generic types are supported.")
                Some(bogusExpr)
              | _ -> None
        function
          | Expr.VarDecl(ec, {Name = name; Type = TypeVar({Name = tvName}); Kind = (Local|SpecLocal) }, _) ->
            helper.Error(ec.Token, 9693, "Cannot declare local '" + name + "' of generic type '" + tvName + "'")
            Some(bogusExpr)
          | Expr.Call(ec,{TypeParameters = tpars}, targs, _) as e -> 
            errorForVarType e
          | e -> errorForVarType e

      for d in decls do
        match d with 
          | Top.FunctionDecl(fn) ->
            let reportErrorIfGeneric prefix t =
              match t with 
                | TypeVar({Name = tvName}) ->
                  helper.Error(fn.Token, 9693, "Cannot " + prefix + " of generic type '" + tvName + "'")
                | _ -> ()
          
            List.iter (fun (v : Variable) -> reportErrorIfGeneric ("declare parameter '" + v.Name + "'") v.Type) (fn.Parameters)
            reportErrorIfGeneric "return value" (fn.RetType)
          | _ -> ()
          
      decls |> deepMapExpressions reportGenericsErrors' 
    // ============================================================================================================

    let normalizeUse self = function
      | CallMacro(ec, "_vcc_use", _, [lbl; e]) ->
        let rec normalizeLabel = function
          | Cast(_, _, Macro(_, "&", [Macro(_, "string", [lbl])])) -> lbl
          | _ -> die()
        Some(Macro(ec, "_vcc_use", [normalizeLabel lbl; self e]))
      | CallMacro(ec, ("_vcc_in_domain"|"_vcc_in_vdomain" as fn), [], [e1; e2]) ->
        let e2' = self e2
        match self e1 with
          | Macro(uc, "_vcc_use", [UserData(_, (:? string as lbl)); e1']) ->
            let lbls = [for s in lbl.Split('|') -> s]
            let mkInDomain l = Macro(ec, fn, [Macro(uc, "_vcc_use", [Expr.ToUserData(l); e1']); e2'])
            let mkAnd c1 c2 = Expr.Prim(ec, Op("&&", Unchecked), [c1; c2])
            Some(List.fold (fun expr l -> mkAnd expr (mkInDomain l)) (mkInDomain lbls.Head) lbls.Tail)
          | e1' -> Some(Macro(ec, fn, [e1'; e2']))
      | _ -> None
 
    // ============================================================================================================

    let normalizeInlineArrayAccesses self = function
      | Macro(ec, "&", [e]) ->
        match e with 
          | Dot(_,_,f) when f.Type._IsArray -> Some(e)
          | e' -> Some(Macro(ec, "&", [e']))
      | Deref(_, (Dot(_,_,f) as dot)) when f.Type._IsArray -> Some(self dot)
      | _ -> None
 
    // ============================================================================================================

    let normalizeOnUnwrap = 
      let expandOne = function
         | BoolOp (c1, "||", Prim(_, Op("==", _), [ COld (_, CallMacro (_, "_vcc_closed", _, [This(_)])) as theOld;
                                               CallMacro (_, "_vcc_closed", _, [This(_)]) as theNew]), body) ->
           mkAnd (Prim (c1, Op("==>",Unchecked), [mkAnd theOld (mkNot theNew); body]))
                 (Prim (c1, Op("==>",Unchecked), [mkAnd (mkNot theOld) theNew; body]))
         | expr -> 
           expr
         
      mapInvariants expandOne
                                           
    // ============================================================================================================

    let handleBoogieInlineDeclarations decls =
      let maybeAdd = function
        | Top.FunctionDecl f ->
          let pref =
            if hasCustomAttr AttrBoogie0 f.CustomAttr then ""
            elif hasCustomAttr AttrBoogie1 f.CustomAttr then "S"
            elif hasCustomAttr AttrBoogie2 f.CustomAttr then "sS"
            else null
          if pref <> null then
            let sign = pref + (f.InParameters |> List.map (fun _ -> ".") |> String.concat "")
            helper.AddPureCall (f.Name, sign)
        | _ -> ()
      List.iter maybeAdd decls
      decls
            
    // ============================================================================================================
 
    let expandContractMacros decls =
      let isMacro (f:Function) = f.Name.StartsWith "\\macro_" || f.Name.StartsWith ("\\result_macro_")
      let isMacroCall = function
        | Call (_, f, _, _) -> isMacro f
        | Macro(_, "ite", [Cast(_, _, Call(_, f, _, _)); BoolLiteral(_, true); BoolLiteral(_, false)]) -> isMacro f
          // this is how non-bool macros are projected
        | _ -> false


      let collectExpansions = 
        let addExpansion (c : Contract) = function
          | Call (ec, m, targs, args) as call
          | Macro(_, "ite", [Cast(_, _, (Call(ec, m, targs, args) as call)); BoolLiteral(_, true); BoolLiteral(_, false)]) ->
            let m' = m.Specialize(targs, false)
            let subst = inlineCall "_(" (fun x -> x) (Call({ec with Type=m'.RetType}, m', [], args))
            let substs = List.map subst
            { c with Requires = c.Requires @ substs m'.Requires; 
                     Ensures = c.Ensures @ substs m'.Ensures;
                     Writes = c.Writes @ substs m'.Writes;
                     Reads = c.Reads @ substs m'.Reads;
                     Decreases = c.Decreases @ substs m'.Variants }
          | _ -> die()
        List.fold addExpansion { Requires = []; Ensures = []; Writes = []; Reads = []; Decreases = [] }

      let expand = function
        | Top.FunctionDecl f ->
          let (macros, ens) = List.partition isMacroCall f.Ensures
          let contr = collectExpansions macros
          f.Requires <- f.Requires @ contr.Requires
          f.Ensures <- ens @ contr.Ensures
          f.Writes <- f.Writes @ contr.Writes
          f.Reads <- f.Reads @ contr.Reads
          f.Variants <- f.Variants @ contr.Decreases
        | _ -> ()

      let expandBlockContracts self = function
        | Block(ec, stmts, Some(contract)) ->
          let (macros, ens) = List.partition isMacroCall contract.Ensures
          let contr = collectExpansions macros
          let contract' = { contract with Requires = contract.Requires @ contr.Requires;
                                          Ensures = ens @ contr.Ensures;
                                          Writes = contract.Writes @ contr.Writes;
                                          Reads = contract.Reads @ contr.Reads;
                                          Decreases = contract.Decreases @ contr.Decreases }
          Some(Block(ec, List.map self stmts, Some(contract')))
        | _ -> None

      let isMacro = function
        | Top.FunctionDecl f -> isMacro f
        | _ -> false

      let macros, decls = List.partition isMacro decls
      List.iter expand macros
      List.iter expand decls
      deepMapExpressions expandBlockContracts decls
    
    // ============================================================================================================

    let normalizeBvLemma decls =

      let lemmaCheckFunctionDecls = ref []

      let extractBvLemmas (fn : Function) = 
        let idCount = ref -1
        let checkFunctionFor (lemma:Expr) = 
          { Function.Empty() with
              Token = lemma.Token
              IsSpec = true
              Name = fn.Name + "#bv_lemma#" + (incr idCount; (!idCount).ToString())
              CustomAttr = VccAttr (AttrIsPure, "") :: VccAttr(AttrBvLemmaCheck, "true") :: inheritedAttrs fn.CustomAttr
              Body = Some (Expr.Block(lemma.Common, [lemma], None))
              IsProcessed = true }
        let findAndExtractThem _ = function
          | Expr.Assert(ec, CallMacro(_, "_vcc_bv_lemma", _, _), _) as _assert ->
            let checkFn = checkFunctionFor _assert
            lemmaCheckFunctionDecls := Top.FunctionDecl(checkFn) :: !lemmaCheckFunctionDecls
            Some(Expr.Comment(ec, "bv_lemma extracted into " + checkFn.Name))
          | _ -> None
        fn.Body <- Option.map (fun (e : Expr) -> e.SelfMap(findAndExtractThem)) fn.Body

      for d in decls do
        match d with
          | Top.FunctionDecl f -> extractBvLemmas f
          | _ -> ()

      decls @ List.sortBy (fun top -> match top with | Top.FunctionDecl(fn) -> fn.Name | _ -> die()) !lemmaCheckFunctionDecls

    // ============================================================================================================

    let embedStackArrays decls =

      let embeddingStructs = ref []     

      let findStackArrays stmts =
        let stackArrays = ref []
        let findStackArraysInBlock' self = function
          | Expr.Macro(_, "=", [Expr.Ref(_,var); Macro(_, "stack_allocate_array", [IntLiteral(_, size); BoolLiteral(_, isSpec)])]) -> 
            match var.Type with
              | Ptr t -> stackArrays := SAR(var, t, (int)size, isSpec) :: !stackArrays; true
              | _ -> false
          | Expr.Block _ -> false
          | _ -> true
        List.iter (fun (e:Expr) -> e.SelfVisit(findStackArraysInBlock')) stmts
        !stackArrays

      let doFunction (fn:Function) =
        let embCount = ref 0
        let asArrayDecls = new HashSet<_>()

        let findAsArray self = function
          // find the stack allocated arrays that are marked as_array
          // also include those that are generated as part of the projection of arrays with
          // initializer
          | VarDecl(_,v,attr) as decl when hasCustomAttr AttrAsArray attr -> asArrayDecls.Add v |> ignore; false
          | Macro(_, "=", [Ref(_, v); Block(_, VarDecl(_,vTemp,_) :: stmts, _)]) when asArrayDecls.Contains v ->
            match TransUtil.last stmts with
              | Ref(_, v') when v = v' -> asArrayDecls.Add vTemp |> ignore
              | _ -> ()
            true
          | _ -> true
             
        let findAndEmbedStackArrays self = function
          | Expr.Block(ec, stmts, bc) ->
            let stackArrays = findStackArrays stmts
            if stackArrays.Length = 0 then None
            else
              let fieldMap = new Dict<_,_>()
              let createField (td:TypeDecl) offset = function
                | SAR(var, t, size, isSpec) ->
                  let asArray = asArrayDecls.Contains var
                  let f = { Token = td.Token
                            Name = var.Name
                            Type = Type.Array(t, size)
                            Parent = td
                            IsSpec = isSpec
                            IsVolatile = false
                            Offset = FieldOffset.Normal(offset)
                            CustomAttr = [VccAttr("as_array", "true")]
                            UniqueId = CAST.unique() } : Field
                  fieldMap.Add(var, f)
                  f

              let rec createFields td offset acc = function
                | [] -> List.rev acc
                | sad :: sads ->
                  let f = createField td offset sad
                  createFields td (offset + f.Type.SizeOf) (f::acc) sads 

              let embTd = { 
                Token = fn.Token
                Kind = TypeKind.Struct
                Name = fn.Name + "stackframe#" + (!embCount).ToString()
                Fields = []
                Invariants = []
                CustomAttr = []
                SizeOf = 0
                IsNestedAnon = false
                GenerateEquality = StructEqualityKind.NoEq
                IsSpec = false
                Parent = None
                IsVolatile = false
                DataTypeOptions = []
                UniqueId = CAST.unique() } : TypeDecl

              let fields = createFields embTd 0 [] (List.rev stackArrays)
              let sizeof = List.fold (fun size (f:Field) -> size + f.Type.SizeOf) 0 fields
              embTd.Fields <- fields
              embTd.SizeOf <- sizeof
              embeddingStructs := Top.TypeDecl(embTd) :: !embeddingStructs

              let embVar = { Name = "#stackframe#" + (!embCount).ToString()
                             Type = Type.Ref(embTd)
                             Kind = VarKind.Local
                             UniqueId = CAST.unique() } : Variable
              let embVarDecl = Expr.VarDecl(bogusEC, embVar, [])
              let embVarPtr = Expr.Macro({bogusEC with Type = Type.PhysPtr (embVar.Type)}, "&", [Expr.Ref({bogusEC with Type = embVar.Type}, embVar)])
              incr embCount

              let addAssignments self =  function
                | Expr.Macro(ec, "=", [Expr.Ref(_,var) as vr; Macro(_, "stack_allocate_array", _)]) ->
                  match fieldMap.TryGetValue var with
                    | true, f -> Some(Expr.Macro(ec, "=", [vr; Expr.MkDot(vr.Common, embVarPtr, f)]))
                    | _ -> None
                | _ -> None

              let stmts' = stmts |> List.map self |> List.map (fun (e:Expr) -> e.SelfMap(addAssignments))

              Some(Expr.Block(ec, embVarDecl :: stmts', bc))

          | _ -> None

        match fn.Body with
          | Some body -> 
            body.SelfVisit(findAsArray)
            fn.Body <- Some(body.SelfMap(findAndEmbedStackArrays))
          | None -> ()
          

      for d in decls do
        match d with
          | Top.FunctionDecl fn -> doFunction fn
          | _ -> ()

      decls @ !embeddingStructs

    // ============================================================================================================
   
    let fixAsArrayRefs self = function
      | Dot (ec, p, f) when hasCustomAttr AttrAsArray f.CustomAttr ->
        Some (Macro (ec, "prelude_as_array_first_index", [Dot (ec, self p, f)]))
      | _ -> None

    // ============================================================================================================

    let normalizeVarArgs self = 
      let ignoredVarArgsFunctions = Map.ofList [ "_vcc_claim", true;
                                                 "_vcc_unclaim", true;
                                                 "_vcc_upgrade_claim", true;
                                                 "_vcc_skinny_expose", true;
                                                 "_vcc_create_set", true ] 
      function
      | Call(ec, { Name = "_vcc_keeps" }, _, args) ->
        Some(Macro(ec, "_vcc_keeps", List.map self args))
      | Call(ec, ({ Name = ("_vcc_unwrap"|"_vcc_wrap") as name } as id), _, args) as expr ->
        if List.length args = 1 then Some expr
        else
          let ptrsetEC = { bogusEC with Type = Type.PtrSet }
          let empty = Expr.Macro (ptrsetEC, "_vcc_set_empty", [])
          let set = Expr.Macro (ptrsetEC, "_vcc_create_set", empty :: args)
          Some(Macro(ec, id.Name + "_set", [self set]))
      | Call(ec, { Name = fnName }, _, args) when Map.containsKey fnName ignoredVarArgsFunctions ->
        None
      | Call(ec, { Name = "__annotation"}, _, args) ->
        let reportErrorForSideEffect _ = function
          | VarWrite(ec, _, _)
          | MemoryWrite(ec, _,_)
          | Call(ec, { Writes = _ :: _ }, _, _) -> 
              helper.Error(ec.Token, 9732, "Side effect in argument to '__annotation' intrinsic")
              false
          | _ -> true
        List.iter (fun (e:Expr) -> e.SelfVisit(reportErrorForSideEffect)) args
        Some(Macro(ec, "ignore_me", []))
      | Call(ec, fn, _, _) when fn.AcceptsExtraArguments ->
        helper.Error(ec.Token, 9731, "Call to function '" + fn.Name + "', which has variable arguments, is not supported.")
        None
      | _ -> None

    // ============================================================================================================

    let desugarStringLiterals decls =
      let stringLiterals = gdict()
      let addDecls = glist[]
      let generateGlobal (v:string) =
        let vn = "string_literal#" + stringLiterals.Count.ToString()
        let vr = Variable.CreateUnique vn (Array (Integer IntKind.Int8, v.Length + 1)) VarKind.ConstGlobal
        let initExprs = ((v |> Seq.map (fun c -> (int)c) |> Seq.toList) @ [0]) |> List.map mkInt
        addDecls.Add (Top.Global (vr, Some (Macro ({ bogusEC with Type = vr.Type }, "init", initExprs))))
        vr
      let aux self = function
        | Macro (c, "precise_string", [UserData (_, (:? string as v))]) ->
          if not (stringLiterals.ContainsKey v) then
            stringLiterals.Add (v, generateGlobal v)
          Some (Expr.Macro (c, "&", [Expr.Ref (c, stringLiterals.[v])]))
        | _ -> None
      let decls = deepMapExpressions aux decls 
      decls @ (addDecls |> Seq.toList)

    // ============================================================================================================

    let normalizeMultiAssignments self = function

      // turns a nested assignment of the form lhs_1 = lhs_2 = ... = lhs_n = rhs 
      // into the sequence tmp = rhs; lhs_n = tmp; ...l lhs_1 = tmp;

      | Macro(ec, "=", _) as assignment ->
        let rec collectLhss acc = function
          | Macro(_, "=", [lhs; rhs]) -> collectLhss (lhs :: acc) rhs
          | rhs -> (acc, rhs)
        
        let (lhss, rhs) = collectLhss [] assignment 
        if lhss.Length = 1 then None
        else 
          let varKind = if Option.isSome (exprDependsOnSpecExpr rhs) then VarKind.SpecLocal else VarKind.Local
          let tmp = getTmp helper "nested" rhs.Type varKind
          let tmpRef = mkRef tmp
          let varDecl = VarDecl({ec with Type = Void}, tmp, [])
          let rhsassign = Macro(ec, "=", [tmpRef; self rhs])
          let lhssassigns = List.map (fun (expr : Expr) -> Macro(expr.Common, "=", [self expr; tmpRef])) lhss
          Some(Expr.MkBlock(varDecl :: rhsassign :: lhssassigns))
      | _ -> None

    // ============================================================================================================

    let unfoldConstants decls = 

      let eqs = ref []
      let extraAxioms = ref []

      let findAndReplaceThem _ = function
        | Macro(_, "const", [c; uc]) ->
          let newEq = Expr.Prim({c.Common with Type = Type.Bool}, Op("==", Unchecked), [c; uc])
          if List.forall (fun (e : Expr) -> not (newEq.ExprEquals(e))) (!eqs) then eqs := newEq :: !eqs
          Some c
        | _ -> None
          
      let doExpr (expr : Expr) = expr.SelfMap(findAndReplaceThem)
      let doExprs = List.map doExpr
        
      let addExtraAxioms eqs origin = 
        extraAxioms := !extraAxioms @ List.map (fun (e : Expr) -> Top.GeneratedAxiom(e, origin)) eqs 

      let doDecl decl = 
        eqs := []
        match decl with
          | Top.Axiom(expr)  -> 
            let result = Top.Axiom(expr.SelfMap(findAndReplaceThem))
            addExtraAxioms !eqs decl
            result
          | Top.GeneratedAxiom(expr, origin) ->
            let result = Top.GeneratedAxiom(expr.SelfMap(findAndReplaceThem), origin)
            addExtraAxioms !eqs origin
            result
          | Top.Global _ -> decl
          | Top.TypeDecl(td) ->
            td.Invariants <- doExprs td.Invariants
            addExtraAxioms !eqs decl
            decl
          | Top.FunctionDecl(fn) ->
            fn.Reads <- doExprs fn.Reads
            fn.Writes <- doExprs fn.Writes
            fn.Variants <- doExprs fn.Variants
            fn.Requires <- doExprs fn.Requires
            fn.Ensures <- doExprs fn.Ensures
            if isSpecMacro fn then
              addExtraAxioms !eqs decl
            else
              fn.Ensures <- fn.Ensures @ (List.map (fun (eq:Expr) -> Expr.Macro(eq.Common, "_vcc_assume", [eq])) !eqs)
              fn.Requires <- fn.Requires @ (List.map (fun (eq:Expr) -> Expr.Macro(eq.Common, "_vcc_assume", [eq])) !eqs)
            eqs := []
            match fn.Body with
              | None -> ()
              | Some body ->
                let body' = doExpr body
                fn.Body <- Some(Expr.MkBlock(List.map Expr.MkAssume !eqs @ [body']))
            decl
      List.map doDecl decls @ !extraAxioms
                
    // ============================================================================================================

    let renameOverloads decls =
      
      let findOverloads (seen, clashes) = function
        | Top.FunctionDecl({Name = ("_vcc_when_claimed"|"_vcc_by_claim")}) -> (seen, clashes) // we introduce our own name clash during NewSyntax
        | Top.FunctionDecl({Name = name}) ->
          if Set.contains name seen then (seen, Set.add name clashes) else (Set.add name seen, clashes)
        | _ -> (seen, clashes)

      let (_, overloadedNames) = List.fold findOverloads (Set.empty, Set.empty) decls

      let overloads = new Dict<_,_>()

      for d in decls do
        match d with 
          | Top.FunctionDecl({Name = name} as fn) when Set.contains name overloadedNames -> 

            let sanitizedTypeName (t : Type) = t.ToString().Replace(' ', '_').Replace('*', '.')

            let parKindStr =  function
              | VarKind.Parameter -> ""
              | VarKind.SpecParameter -> "spec_"
              | VarKind.OutParameter -> "out_"
              | _ -> die()

            let parTypes = [| for p in fn.Parameters -> parKindStr p.Kind + sanitizedTypeName p.Type |]
            let parTypeString = if parTypes.Length = 0 then "" else "#" + System.String.Join("#", parTypes)
            let overloadName = fn.Name + "#overload#" + (sanitizedTypeName fn.RetType) + parTypeString

            match overloads.TryGetValue(overloadName) with
              | true, clashingDecl ->
                helper.Error(fn.Token, 9717, "function '" + fn.Name + "' already has a body", Some clashingDecl.Token)
              | _ -> overloads.Add(overloadName, fn)

            fn.Name <- overloadName

          | _ -> ()

      decls

    // ============================================================================================================

    let addInternalFunctions decls =

      // template<typename T> \object \stack_alloc(\integer, bool);
      let stackAlloc = 
        Top.FunctionDecl ( 
          { Function.Empty() with 
              IsSpec = true
              Name = "_vcc_stack_alloc"
              RetType = Type.ObjectT
              Parameters = [ Variable.CreateUnique "stack_frame" (Type.MathInteger(MathIntKind.Signed)) VarKind.Parameter
                             Variable.CreateUnique "is_spec" Type.Bool VarKind.Parameter ]
              TypeParameters = [ { Name = "T" } ]
        })

      // void \stack_free(\integer, \object);
      let stackFree = 
        Top.FunctionDecl ( 
          { Function.Empty() with 
              IsSpec = true
              Name = "_vcc_stack_free"
              Parameters = [ Variable.CreateUnique "stack_frame" (Type.MathInteger(MathIntKind.Signed)) VarKind.Parameter
                             Variable.CreateUnique "obj" Type.ObjectT VarKind.Parameter ]
        })

      [stackAlloc; stackFree] @ decls

    // ============================================================================================================

    helper.AddTransformer ("norm-begin", TransHelper.DoNothing)
    helper.AddTransformer ("norm-internals", TransHelper.Decl addInternalFunctions)
    helper.AddTransformer ("norm-unfold-constants", TransHelper.Decl unfoldConstants)
    helper.AddTransformer ("norm-overloads", TransHelper.Decl renameOverloads)
    helper.AddTransformer ("norm-varargs", TransHelper.Expr normalizeVarArgs)
    helper.AddTransformer ("norm-multi-assignments", TransHelper.Expr normalizeMultiAssignments)
    helper.AddTransformer ("norm-inline-boogie", TransHelper.Decl handleBoogieInlineDeclarations)
    helper.AddTransformer ("norm-expand-contract-macros", TransHelper.Decl expandContractMacros)
    helper.AddTransformer ("norm-initializers", TransHelper.Expr normalizeInitializers)
    helper.AddTransformer ("norm-use", TransHelper.Expr normalizeUse)
    helper.AddTransformer ("norm-fixed-array-parms", TransHelper.Decl removeFixedSizeArraysAsParameters)
    helper.AddTransformer ("norm-inline-array-accesses", TransHelper.Expr normalizeInlineArrayAccesses)
    helper.AddTransformer ("norm-out-params", TransHelper.Expr removeDerefFromOutParams)
    helper.AddTransformer ("norm-comparison", TransHelper.Expr (doHandleComparison helper))
    helper.AddTransformer ("norm-conversions", TransHelper.Expr doHandleConversions)   
    helper.AddTransformer ("norm-ptr-comparison", TransHelper.Decl (handlePurePtrEq helper))
    helper.AddTransformer ("inline-spec-macros", TransHelper.Decl inlineSpecMacros)
    helper.AddTransformer ("norm-generic-errors", TransHelper.Decl reportGenericsErrors) 
    helper.AddTransformer ("add-assume-to-assert", TransHelper.Expr handleLemmas)    
    helper.AddTransformer ("fixup-old", TransHelper.ExprCtx fixupOld)    
    helper.AddTransformer ("fixup-claims", TransHelper.Expr handleClaims)    
    helper.AddTransformer ("add-explicit-return", TransHelper.Decl addExplicitReturn)
    helper.AddTransformer ("norm-embed-stack-arrays", TransHelper.Decl embedStackArrays)
    helper.AddTransformer ("norm-fix-as_array-refs", TransHelper.Expr fixAsArrayRefs)
    helper.AddTransformer ("norm-atomic-ops", TransHelper.Expr normalizeAtomicOperations)
    helper.AddTransformer ("norm-skinny-expose", TransHelper.Expr normalizeSkinnyExpose)
    helper.AddTransformer ("norm-bv_lemma", TransHelper.Decl normalizeBvLemma)
    helper.AddTransformer ("norm-misc", TransHelper.Decl miscNorm)
    helper.AddTransformer ("norm-quant-triggers", TransHelper.Expr handleTriggerHints)
    helper.AddTransformer ("deep-split-conjunctions", TransHelper.Expr deepSplitConjunctions)
    helper.AddTransformer ("split-assertions", TransHelper.Expr splitConjunctionsInAssertions)
    helper.AddTransformer ("norm-writes", TransHelper.Decl normalizeWrites)
    helper.AddTransformer ("norm-atomic-inline", TransHelper.Decl inlineAtomics)
    helper.AddTransformer ("norm-on-unwrap", TransHelper.Decl normalizeOnUnwrap)
    helper.AddTransformer ("norm-strings", TransHelper.Decl desugarStringLiterals)
    helper.AddTransformer ("norm-end", TransHelper.DoNothing)
