//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc

  open System.Diagnostics
  open Microsoft
  open Microsoft.Research.Vcc.Util
  open Microsoft.Research.Vcc.BoogieAST
  open Microsoft.Research.Vcc.ToBoogieAST

  module VcOpt =
  
    let (|App|_|) = function
      | Primitive (name, args) -> Some (name, args)
      | FunctionCall (name, args) -> Some (name, args)
      | _ -> None
      
    let (|BTrue|_|) = function
      | BoolLiteral true -> Some (BTrue)
      | _ -> None
    
    let (|BFalse|_|) = function
      | BoolLiteral false -> Some (BFalse)
      | _ -> None
    
    let BTrue = BoolLiteral true
    let BFalse = BoolLiteral false
    
    let warn (msg:string) =
      System.Console.WriteLine ("VC Optimizer Warning: {0}", msg)
    
    let info (msg:string) =
      System.Console.WriteLine ("VC Optimizer Info: {0}", msg)
    
    // -----------------------------------------------------------------------------------
    // simple types 
    // -----------------------------------------------------------------------------------
    
    type Var = Id * Type   
    
    type ExprId = int
    type State = ExprId
    
    type CType =
      | PtrTo of Type
      | Map of Type * Type
      | Base of string
    type Ptr = ExprId
    
    type B3 = 
      | Yes 
      | No 
      | Maybe
      
      override this.ToString() =
        match this with
          | Yes -> "1"
          | No -> "0"
          | Maybe -> "?"
    
    type Value =
      {
        IsTyped : B3;
        IsThreadLocal : B3;
        IsClosed : B3;
        IsThreadOwned : B3;
      }
      
      override this.ToString() =
        sprintf "typed=%O closed=%O mine=%O trans-mine=%O" this.IsTyped this.IsClosed this.IsThreadOwned this.IsThreadLocal
      
      static member Default =
        { IsTyped = Maybe;
          IsThreadLocal = Maybe;
          IsClosed = Maybe;
          IsThreadOwned = Maybe; }
        
      
    type Object =
      {
        Name : Expr;
        InState : Map<State, Value>;
      }
      
      override this.ToString() =
        let sb = System.Text.StringBuilder()
        (sb.Append this.Name).Append (":\r\n") |> ignore
        this.InState |> Map.iter (fun s v -> ((((sb.Append "   ").Append s).Append ": ").Append v).Append "\r\n" |> ignore)
        sb.ToString()
      
      static member Build n =
        { Name = n; InState = new Map<_,_> ([]) }

      
    // -----------------------------------------------------------------------------------
    // FunctionDef
    // -----------------------------------------------------------------------------------
    
    type FunctionDef =
      {
        Name    : Id;
        Formals : list<Id>;
        Equiv   : list<Expr>;
        Implies : list<Expr>;
      }
      
      override this.ToString() =
        let sb = System.Text.StringBuilder()
        let wr = wrb sb
        wr this.Name
        wr (listToString this.Formals)
        wr ":\r\n"
        for e in this.Equiv do
          wr "  <==> "
          e.WriteTo sb
          wr "\r\n"
        for e in this.Implies do
          wr "   ==> "
          e.WriteTo sb
          wr "\r\n"          
        sb.ToString()
      
      member this.Subst actuals =
        let map = new Map<_,_> (List.zip this.Formals actuals)
        let repl = function
          | Ref n -> map.TryFind n
          | _ -> None
        fun (e:Expr) -> e.Map repl
      
      member this.Implications actuals =
        List.map (this.Subst actuals) (this.Equiv @ this.Implies)
        
      
    // -----------------------------------------------------------------------------------
    // Context
    // -----------------------------------------------------------------------------------
    
    type Context =
      {
        mutable Version : int;
        mutable Objects : Map<Ptr, Object>;
        mutable HeapSuccession : Map<State * State, FunctionDef>;
        mutable ActivePtrs : Set<Ptr>;
      }
      
      override this.ToString() =
        let sb = System.Text.StringBuilder()
        this.Objects |> Map.iter (fun _ v -> (sb.Append "\r\n").Append v |> ignore)
        this.HeapSuccession |> Map.iter (fun _ v -> (sb.Append "\r\n").Append v |> ignore)
        sb.ToString()
      
      static member Empty =
        { Objects = empty (); HeapSuccession = empty (); ActivePtrs = Set.empty; Version = 0 }
        
      member this.Get (state, ptr) =
        match this.Objects.TryFind ptr with
          | Some obj ->
            match obj.InState.TryFind state with
              | Some v -> v
              | None -> Value.Default
          | None -> Value.Default
      
      member this.Set (state, ptr, ptrn, v) =
        let obj =
          match this.Objects.TryFind ptr with
            | Some obj -> obj
            | None -> Object.Build ptrn
        let repl = { obj with InState = obj.InState.Add (state, v) }
        this.Objects <- this.Objects.Add (ptr, repl)
        this.BumpVer ()
      
      member this.Copy () = { this with ActivePtrs = Set.empty }
      
      member this.BumpVer () =
        this.Version <- this.Version + 1
        
      
    // -----------------------------------------------------------------------------------
    // AxiomContext
    // -----------------------------------------------------------------------------------
    
    type AxiomContext =
      {
        Axioms : list<Expr>;
        Functions : Map<Id, FunctionDef>;
      }
      
      override this.ToString () =
        let sb = System.Text.StringBuilder()
        this.Functions |> Map.iter (fun _ f -> sb.Append (f.ToString()) |> ignore) 
        sb.ToString()
      
      static member Build axs =
        let stripGoodState = function
          | App ("==>", [App ("$good_state", [_]); e]) -> e
          | e -> e
          
        let rec findFunctions (fns:Map<_,FunctionDef>) = function
          | Forall (_, vars, _, _, body) ->
            //info ("do forall " + body.ToString())
            match stripGoodState body with
              | App (("==>"|"<==>"|"==") as op, [App (name, args); body]) ->
                let rec collectArgs acc = function
                  | Ref name :: xs when List.exists (fun (n, _) -> n = name) vars && not (_list_mem name acc) ->
                    collectArgs (name :: acc) xs
                  | [] -> List.rev acc
                  | lst -> 
                    //info ("fail on arg " + listToString lst + " / " + listToString acc)
                    []
                match collectArgs [] args with
                  | [] -> fns
                  | formals ->
                    let theNew = { Name = name; Formals = formals; Equiv = []; Implies = [] }
                    let body, f =
                      match fns.TryFind name with
                        | Some f -> theNew.Subst (List.map Ref f.Formals) body, f
                        | None -> body, theNew
                    let f =
                      match op with
                        | "==>" -> { f with Implies = body :: f.Implies }
                        | _     -> { f with Equiv = body :: f.Equiv }
                    fns.Add (name, f)
              | expr -> 
                //info ("skip forall " + expr.ToString())
                fns
          | _ -> fns
        
        { Axioms = axs; Functions = List.fold findFunctions (empty ()) axs }
    
    
    
    // -----------------------------------------------------------------------------------
    // the main optmization function
    // -----------------------------------------------------------------------------------
    
    let optimize (ax:AxiomContext) root =    
      let curId = ref 1
      
      let cache (back:Dict<_,_>) (dict:Dict<_,_>) x =
        match dict.TryGetValue x with
          | true, n -> n
          | _ ->
            incr curId
            dict.[x] <- !curId
            back.[!curId] <- x
            !curId
      
      let exprIds = new Dict<_,_>()
      let revExprIds = new Dict<_,_>()
      let exprId expr = cache revExprIds exprIds expr
      let idToExpr id = revExprIds.[id]
      
      let updateCtx (ctx:Context) state ptrn upf =
        let s = exprId state
        let ptr = exprId ptrn
        let v = ctx.Get (s, ptr)
        let v' = upf v
        if v <> v' then
          ctx.Set (s, ptr, ptrn, v')
      
      let syncValues (ctx:Context) s1 s2 p fetch set =
        let s1 = exprId s1
        let s2 = exprId s2
        let p' = exprId p
        let v1 = ctx.Get (s1, p')
        let v2 = ctx.Get (s2, p')
        match fetch v1, fetch v2 with
          | x1, x2 when x1 = x2 -> ()
          | Maybe, x
          | x, Maybe ->
            ctx.Set (s1, p', p, set x v1)
            ctx.Set (s2, p', p, set x v2)
          | x1, x2 ->
            warn ("found inconsistency on " + p.ToString())
      
      let conditions =
        new Map<_,_> 
         ([
           "$thread_local", fun v -> v.IsThreadOwned = Yes || v.IsThreadLocal = Yes;
           "$wrapped", fun v -> v.IsThreadOwned = Yes && v.IsClosed = Yes;
           "$closed", fun v -> v.IsClosed = Yes;
         ])
                  
      let rec simplify fns (ctx:Context) expr =
        let expand = function
          | App (name, args) as expr ->
            if _list_mem name fns then
              warn ("expansion loop on " + expr.ToString())
              expr
            else
              match ax.Functions.TryFind name with
                | Some ({ Equiv = (_ :: _) as eq } as f) ->
                  let eq = eq |> List.map (f.Subst args) |> List.map (simplify (name :: fns) ctx)
                  if _list_mem BTrue eq then BTrue
                  elif _list_mem BFalse eq then BFalse
                  else expr
                | _ -> expr
           | expr -> expr
           
        match expr with
          | App (("&&"|"||"|"==>") as op, [e1; e2]) ->
            let e1 = simplify fns ctx e1
            let e2 = simplify fns ctx e2
            
            match e1, op, e2 with
              | BFalse, "==>", _
              | _, "==>", BTrue
              | BTrue, "||", _
              | _, "||", BTrue -> BTrue
              | BFalse, "&&", _
              | _, "&&", BFalse -> BFalse
              | BTrue, "==>", e
              | BFalse, "||", e
              | e, "||", BFalse
              | BTrue, "&&", e
              | e, "&&", BTrue -> e
              | _ -> Primitive (op, [e1; e2])
          
          | (App (name, ([s;ptr] | [s;ptr;_])) as expr) when conditions.ContainsKey name ->
            let ptr = exprId ptr
            if not (ctx.ActivePtrs.Contains ptr) then
              ctx.ActivePtrs <- ctx.ActivePtrs.Add ptr
              ctx.BumpVer()
            if conditions.[name] (ctx.Get (exprId s, ptr)) then BTrue
            else expand expr          
          
          | _ -> expand expr
            
      let rec update fns (ctx:Context) expr = 
        let self = update fns
        match expr with
          | App ("&&", [e1; e2]) ->
            self ctx e1
            self ctx e2
          | App (name, args) ->
            info ("update with " + expr.ToString())
            let u = updateCtx ctx
            match name, args with
              | "$ts_typed", [App ("$ts", [s; ptr])] -> u s ptr (fun v -> { v with IsTyped = Yes })
              | "==", [App ("$owner", [s;ptr]); App ("$me", [])] -> u s ptr (fun v -> { v with IsThreadOwned = Yes })
              | "$closed", [s;ptr] -> u s ptr (fun v -> { v with IsClosed = Yes })
              | "$st_eq", [s1;s2;ptr] ->
                syncValues ctx s1 s2 ptr (fun x -> x.IsClosed) (fun x v -> { v with IsClosed = x })
                syncValues ctx s1 s2 ptr (fun x -> x.IsThreadOwned) (fun x v -> { v with IsThreadOwned = x })
              | "$ts_eq", [s1;s2;ptr] ->
                syncValues ctx s1 s2 ptr (fun x -> x.IsTyped) (fun x v -> { v with IsTyped = x })
              | _ -> ()
            if _list_mem name fns then
              warn ("expansion loop on " + name)
            else
              match ax.Functions.TryFind name with
                | Some f -> 
                  List.iter (update (name :: fns) ctx) (f.Implications args)
                | None -> ()
          | Forall (_, [(ptr, Type.Ref "$ptr")], _, _, body) ->
            let heapPair = ref None
            let find = function
              | App (("$st_eq"|"$ts_eq"|"$mem_eq"), [s1; s2; Ref ptr']) when ptr = ptr' ->
                heapPair := Some (s1, s2)
                None
              | _ -> None
            body.Map find |> ignore
            match !heapPair with
              | Some (s1, s2) ->
                let theNew = { Name = "$heap_succ[" + s1.ToString() + "->" +  s2.ToString() + "]" ; 
                               Formals = [ptr]; Equiv = []; Implies = [] }
                let key = (exprId s1, exprId s2)
                let body, f =
                  match ctx.HeapSuccession.TryFind key with
                    | Some f -> theNew.Subst (List.map Ref f.Formals) body, f
                    | None -> body, theNew
                let f = { f with Implies = body :: f.Implies }
                ctx.HeapSuccession <- ctx.HeapSuccession.Add (key, f)
                ctx.BumpVer()
              | None -> ()
          | _ -> ()
      
      let propagate (ctx:Context) =
        let makeUse e = update [] ctx (simplify [] ctx e)
        let applyHS p _ (f:FunctionDef) = List.iter makeUse (f.Implications [idToExpr p])
        Set.iter (fun p -> Map.iter (applyHS p) ctx.HeapSuccession) ctx.ActivePtrs
      
      let rec recSimplify ctx e =
        let oldVer = ctx.Version
        propagate ctx
        let res = simplify [] ctx e
        info (ctx.ToString())
        info ("simplify: " + e.ToString() + " ----> " + res.ToString())
        if oldVer = ctx.Version then res
        else recSimplify ctx e
      
      let rec main ctx (block:Block) =
        info ("optimizing " + block.Label)
        let optcmd (ctx, acc) cmd =
          let cmd =
            if cmd.IsAssert then
              { cmd with Condition = recSimplify ctx cmd.Condition }
            else
              cmd
          let ctx' = ctx.Copy()
          update [] ctx' cmd.Condition
          (ctx', cmd :: acc)
        let (ctx, cmds) = List.fold optcmd (ctx, []) block.Cmds
        info "done, output context:"
        info (ctx.ToString())
        block.Cmds <- List.rev cmds
        List.iter (main ctx) block.Exits
      
      main Context.Empty root
             
             
    // -----------------------------------------------------------------------------------
    // Callback
    // -----------------------------------------------------------------------------------
    
    type DummyOpt (prog:Boogie.Program, helper:Helper.Env, options) =
      inherit Passyficator(prog, helper, options)      
      override this.Optimize (proc:BlockProc) = ()
      
    type Optimizer (prog:Boogie.Program, helper:Helper.Env, options) =
      inherit Passyficator(prog, helper, options)
      
      override this.Optimize (proc:BlockProc) =
        let axioms = this.GetAxioms()
        let axioms = this.GetExpansionAxioms() @ axioms
        let ax = AxiomContext.Build axioms
        info (ax.ToString())
        let root = proc.Blocks.Head
        optimize ax root
        proc.Blocks <- ToBoogieAST.blocksFromRoot root
        
