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
 
 module Inference =
  let init (helper:TransHelper.TransEnv) =

    let inferLoopInvariants self = function
      | Loop (comm, invs, writes, variants, body) ->
        let has_free = ref false
        let has_meta_write = ref false
        let checkFree _ = function
          | Call (_, fn, _, _) ->            
            if fn.Writes <> [] then
              has_free := true
            if not fn.IsPure then
              has_meta_write := true
            true
          | Atomic _ -> has_meta_write := true; true
          | Macro (_, "unclaim", _) -> has_free := true; true
          | _ -> true
        body.SelfVisit checkFree
        if !has_free then None
        else 
          let incr = Expr.MkAssume (Macro (boolBogusEC(), (if not !has_meta_write then "_vcc_meta_eq" else "_vcc_mutable_increases"), []))
          let body = Expr.MkBlock [incr; self body]
          Some (Loop (comm, invs, writes, variants, body))
      | _ -> None
    
    let conjuncts = List.map splitConjunction >> List.concat

    let preconditions (f:Function) = conjuncts f.Requires
    
    let allOnWhichCalled name f lst =
      let add acc = function
        | CallMacro (_, name', _, [p]) when name = name' -> f p :: acc
        | _ -> acc      
      List.fold add [] lst
    
    let inferAssert tok (e:Expr) =
      Expr.Assert({forwardingToken tok None (fun () -> afmt 8505 "inferred assertion: {0}" [e.ToString()]) with Type = Type.Void }, e, [])
     
    let inferMacro name (args: list<Expr>) =
      inferAssert args.Head.Token (Macro (boolBogusEC(), name, args))
    
    let inferInDomain f (b:Expr) =
      let addWrapped = allOnWhichCalled "_vcc_wrapped" (fun p -> inferMacro "_vcc_in_domain" [p; p])
      let handleBlocks self = function
        | Block(ec, stmts, Some bc) -> 
          Some(Block(ec, (addWrapped (conjuncts bc.Requires)) @ (List.map self stmts), Some bc))
        | _ -> None

      Expr.MkBlock (addWrapped (preconditions f) @ [b.SelfMap(handleBlocks)])
    
    let concatSome =
      let add acc = function Some e -> e :: acc | None -> acc
      List.fold add []
      
    let inferValidClaim (f:Function) (b:Expr) =
      let mkAssert (p:Expr) =
        match p.Type with
          | Ptr Claim ->
            Some (inferMacro "_vcc_valid_claim" [p])
          | _ -> None
      let addWrapped = allOnWhichCalled "_vcc_wrapped" mkAssert >> concatSome
      let handleBlocks self = function
        | Block(ec, stmts, Some bc) -> 
          Some(Block(ec, (addWrapped (conjuncts bc.Requires)) @ (List.map self stmts), Some bc))
        | _ -> None

      Expr.MkBlock (addWrapped (preconditions f) @ [b.SelfMap(handleBlocks)])
      
    let doInferAlwaysByClaim conds =
      let add acc = function
        | Call (_, { Name = "_vcc_claims" }, _, [c; cond]) ->          
          let mkAssert p =
            Macro (boolBogusEC(), "_vcc_always_by_claim", [c; p])
          (splitConjunction cond |> allOnWhichCalled "_vcc_closed" mkAssert) @ acc
        | _ -> 
          acc
      List.fold add conds (List.concat (List.map splitConjunction conds))

    let inferAlwaysByClaim = function
      | Top.FunctionDecl f as decl ->
        f.Requires <- doInferAlwaysByClaim f.Requires
        decl
      | Top.TypeDecl td as decl ->      
        td.Invariants <- doInferAlwaysByClaim td.Invariants
        decl
      | decl -> decl

    let shouldInfer attrs attr =
      let check = function
        | CustomAttr.VccAttr ("no_infer", "all") -> true
        | CustomAttr.VccAttr ("no_infer", attr') -> attr = attr'
        | _ -> false
      not (List.exists check attrs)
    
    (*
      applyMagicAssertion "bar" "foo" [] updateEnv applyEnv decls      
      will look for mentions of Macro("foo", args) in contracts, call (updateEnv curEnv args)
      and then call applyEnv with the finally obtained environment on contracts and the body.
      Also when Assert(Macro("foo", ...)) is found inside of a block, the env will be updated
      accordingly for the rest of the block. The macro itself is replaced by 'true'.
      The applyEnv function is getting the usual SelfMap interface. The applyEnv is called only
      if "bar" should be applied on respective type/function.
    *)      
    let applyMagicAssertion id name init updateEnv applyEnv decls =
      let scan env (expr:Expr) =
        let env = ref env
        let check self = function
          | CallMacro (_, name', _, args) when name' = name ->
            env := updateEnv !env args
            Some (Expr.True)
          | _ -> None
        let res = expr.SelfMap check
        (res, !env)
      
      let rec apply doIt env (expr:Expr) : Expr =
        let is_assert_assume = function
          | Assert _
          | Assume _ -> true
          | _ -> false
        let repl self = function
          | Block (ec, stmts, cs) ->
            let rec aux env acc = function
              | AssertAssume (_, CallMacro (_, name', _, args)) as x :: xs when name' = name ->
                aux (updateEnv env args) acc xs
              | Block (_, stmts, _) :: xs when List.forall is_assert_assume stmts ->
                aux env acc (stmts @ xs)                
              | x :: xs ->
                aux env (apply doIt env x :: acc) xs
              | [] ->
                Block (ec, List.rev acc, cs)
            Some (aux env [] stmts)
          | expr -> 
            if doIt then applyEnv env self expr
            else None
        expr.SelfMap repl
      
      let doDecl decl = 
        let env = ref init
        let repl _ expr =
          let (res, tmp) = scan !env expr
          env := tmp
          Some res
        let myapply attrs _ expr =
          let doIt = shouldInfer attrs id
          Some (apply doIt !env expr)
          
        match decl with
          | Top.FunctionDecl f ->
            let tmp = f.Body
            f.Body <- None
            deepMapExpressions repl [decl] |> ignore
            f.Body <- tmp
            deepMapExpressions (myapply f.CustomAttr) [decl] |> ignore
            decl
          | (Top.TypeDecl td) as decl ->
            match deepMapExpressions (myapply td.CustomAttr) (deepMapExpressions repl [decl]) with
              | [decl] -> decl
              | _ -> die()
          | decl -> decl      
      
      List.map doDecl decls
      
    let findRepl env ex = 
      let rec aux = function
        | (Old (_, _, x), c) :: _ when simpleCmp helper false (x, ex) -> Some c
        | (x, c) :: _ when simpleCmp helper false (x, ex) -> Some c
        | (_x, _) :: xs -> 
          aux xs
        | [] -> None
      aux env
      
    let addByClaim decls =
      let updateEnv env = function 
        | [c; o] -> (o, c) :: env
        | _ -> die()
      let applyEnv env self expr =
        match expr with
          | Deref (ec, (Index (_, Dot (_, p, f), _) as ptr))
          | Deref (ec, (Dot (_, p, f) as ptr)) when not f.IsVolatile ->
            match findRepl env p with
              | Some c -> Some ((Macro (ec, "by_claim", [c; self p; self ptr])))
              | None -> None
          | Atomic _ as expr -> Some expr
          | Macro(ec, "=", [Deref(ec1, e1); e2]) -> Some(Macro(ec, "=", [Deref(ec1, self e1); self e2]))
          | _ -> None      
      applyMagicAssertion "by_claim" "_vcc_always_by_claim" [] updateEnv applyEnv decls                
      
    let inferEmptyOwns = 
    
      let hasKeeps exprs =
        let keepsFound = ref false
        let hasKeeps' self = function
          | CallMacro(_, "_vcc_keeps", _, This _ :: _) -> 
            keepsFound := true
            false
          | _ -> not !keepsFound
        List.iter (fun (e : Expr) -> e.SelfVisit(hasKeeps')) exprs
        !keepsFound
      
      function 
        | Top.TypeDecl({Kind = Struct|Union} as td) as top when staticOwns td && not td.IsRecord ->
          if not (hasKeeps td.Invariants) then
            let ownsThis = Macro({ bogusEC with Type = Type.PtrSet }, "_vcc_owns", [This({bogusEC with Type = Type.MkPtr(Type.Void, td.IsSpec)})]) // todo: change type to *S instead of void *
            let emptySet = Macro({ bogusEC with Type = Type.PtrSet }, "_vcc_set_empty", [])
            let ownsIsEmpty = Macro({ bogusEC with Type = Type.Bool}, "_vcc_set_eq", [ownsThis; emptySet])
            td.Invariants <- ownsIsEmpty :: td.Invariants
          top
        | top -> top
      
    let inferSetIn decl =   
      let isSetType = function
        | Type.Ref { Name = "\\objset"; Kind = TypeKind.MathType } -> true
        | _ -> false
      let doInferSetIn self = function
        | CallMacro(c, "_vcc_set_eq", _, [e1; e2]) as expr when (isSetType e1.Type) && (isSetType e2.Type) -> 
          let rec collectSingletons = function
            | CallMacro(_, "_vcc_set_singleton", _, [e]) -> [e]
            | CallMacro(_, "_vcc_set_union", _, [e1; e2]) -> (collectSingletons e1) @ (collectSingletons e2)
            | _ -> []
          let singletons1 = collectSingletons (self e1)
          let singletons2 = collectSingletons (self e2)
          let mkSetIn e1 e2 = Expr.Macro(c, "_vcc_set_in", [e1; e2])
          Some(
            List.fold (fun a b -> boolOp "&&" a (mkSetIn b e2))
              (List.fold (fun a b -> boolOp "&&" a (mkSetIn b e1)) expr singletons2)
              singletons1
              )
        | _ -> None 
      deepMapDecl doInferSetIn decl
         
    let inferFn name proc =
      let one (f:Function) =
        if shouldInfer f.CustomAttr name then
          match f.Body with
            | Some b -> f.Body <- Some (proc f b)
            | None -> ()
        f          
      mapFunctions one

    let inferAny name proc =
      let doDecl = function
        | Top.FunctionDecl f as decl when shouldInfer f.CustomAttr name -> proc decl
        | Top.TypeDecl td as decl when shouldInfer td.CustomAttr name -> proc decl
        | decl -> decl
      List.map doDecl                
  
    
    helper.AddTransformer ("infer-begin", TransHelper.DoNothing)
    
    helper.AddTransformer ("infer-in_domain", TransHelper.Decl (inferFn "in_domain" inferInDomain))
    helper.AddTransformer ("infer-valid_claim", TransHelper.Decl (inferFn "valid_claim" inferValidClaim))
    helper.AddTransformer ("infer-always_by_claim", TransHelper.Decl (inferAny "always_by_claim" inferAlwaysByClaim))
    helper.AddTransformer ("infer-by_claim", TransHelper.Decl addByClaim)
    helper.AddTransformer ("infer-loop_invariants", TransHelper.Expr inferLoopInvariants)
    helper.AddTransformer ("infer-set_in", TransHelper.Decl (inferAny "set_in" inferSetIn))
    helper.AddTransformer ("infer-empty-owns", TransHelper.Decl (inferAny "empty_owns" inferEmptyOwns))
   
    helper.AddTransformer ("infer-end", TransHelper.DoNothing)
