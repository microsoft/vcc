//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc

  open System.Diagnostics
  open Microsoft
  open Util

  module BoogieAST =

    let die() = failwith "confused, will now die"

    let sanitize (id:string) = id.Replace('\\', '#')

    type Id = string

    type Type =
      | Bool
      | Int
      | Map of list<Type> * Type
      | Ref of Id
      | Bv of int
      
      override this.ToString() =
        match this with
          | Bool -> "bool"
          | Int -> "int"
          | Map (f, t) ->
            "[" + String.concat ", " [for t in f -> t.ToString()] + "]" + t.ToString()
          | Ref n -> n
          | Bv n -> "bv" + n.ToString()

    type Var = Id * Type
    
    [<StructuralEquality;NoComparison>] 
    type Expr =
      | Ref of Id // Bid Id from Microsoft.Boogie.hs
      | BoolLiteral of bool
      | IntLiteral of bigint
      | SecLabelLiteral of string
      | BvLiteral of bigint * int
      | BvConcat of Expr * Expr
      | BvExtract of Expr * int * int
      | Primitive of Id * list<Expr>
      | FunctionCall of Id * list<Expr>
      | ArrayIndex of Expr * list<Expr>
      | ArrayUpdate of Expr * list<Expr> * Expr
      | Old of Expr
      | Ite of Expr * Expr * Expr
      | Exists of Token * list<Var> * list<list<Expr>> * list<Attribute> * Expr // may generate warnings
      | Forall of Token * list<Var> * list<list<Expr>> * list<Attribute> * Expr // may generate warnings
      | Lambda of Token * list<Var> * list<Attribute> * Expr
      
      override this.ToString () = toString this.WriteTo
      
      member this.WriteTo sb =
        let wr = wrb sb
        let self (p:Expr) = p.WriteTo sb
        let doVar (n, (t:Type)) =
          wr n
          wr ":"
          wr (t.ToString())          
        let quant (vars, triggers, attrs, expr) =
          commas sb doVar vars
          wr " :: "
          // TODO triggers
          // TODO attrs
          self expr
          wr ")"
        match this with
          | Ref n -> wr n
          | BoolLiteral true -> wr "true"
          | BoolLiteral false -> wr "false"          
          | IntLiteral n -> wr (n.ToString())
          | SecLabelLiteral l -> wr l
          | BvLiteral (k, sz) -> wr (k.ToString()); wr "bv"; wr (sz.ToString())
          | BvConcat (e1, e2) -> 
            wr "("
            self e1
            wr " ++ "
            self e2
            wr ")"
          | BvExtract (e1, t, f) ->
            wr "("
            self e1
            wr "["
            wr (t.ToString())
            wr ":"
            wr (f.ToString())
            wr "])"
          | Primitive (n, [e1; e2]) ->
            wr "("
            self e1
            wr (" " + n + " ")
            self e2
            wr ")"
          | Primitive (n, [e1]) ->
            wr ("(" + n + " ")
            self e1
            wr ")"
          | Primitive (n, args)
          | FunctionCall (n, args) ->
            doArgsb sb self n args
          | ArrayIndex (expr, args) ->
            self expr
            wr "["
            commas sb self args
            wr "]"
          | ArrayUpdate (expr, args, v) ->
            self expr
            wr "["
            commas sb self args
            wr " := "
            self v
            wr "]"
          | Old (e) ->
            wr "old("
            self e
            wr ")"
          | Ite (c, t, e) ->
            wr "if "; self c; wr " then "; self t; wr " else "; self e
          | Exists (_, vars, triggers, attrs, expr) ->
            wr "(exists "
            quant (vars, triggers, attrs, expr)
          | Forall (_, vars, triggers, attrs, expr) ->
            wr "(forall "
            quant (vars, triggers, attrs, expr)
          | Lambda (_, vars, attrs, expr) ->
            wr "(lambda "
            quant (vars, [], attrs, expr)

    and Attribute =
      | ExprAttr of string * Expr
      | StringAttr of string * string
      
    let unaryOps = 
      [
         ("!", Microsoft.Boogie.UnaryOperator.Opcode.Not);
      ]
        
    let binaryOps = 
      [
         ("+", Microsoft.Boogie.BinaryOperator.Opcode.Add);
         ("-", Microsoft.Boogie.BinaryOperator.Opcode.Sub);
         ("*", Microsoft.Boogie.BinaryOperator.Opcode.Mul);
         ("/", Microsoft.Boogie.BinaryOperator.Opcode.Div);
         ("%", Microsoft.Boogie.BinaryOperator.Opcode.Mod);
         ("==", Microsoft.Boogie.BinaryOperator.Opcode.Eq);
         ("!=", Microsoft.Boogie.BinaryOperator.Opcode.Neq);
         (">", Microsoft.Boogie.BinaryOperator.Opcode.Gt);
         (">=", Microsoft.Boogie.BinaryOperator.Opcode.Ge);
         ("<", Microsoft.Boogie.BinaryOperator.Opcode.Lt);
         ("<=", Microsoft.Boogie.BinaryOperator.Opcode.Le);
         ("&&", Microsoft.Boogie.BinaryOperator.Opcode.And);
         ("||", Microsoft.Boogie.BinaryOperator.Opcode.Or);
         ("==>", Microsoft.Boogie.BinaryOperator.Opcode.Imp);
         ("<==>", Microsoft.Boogie.BinaryOperator.Opcode.Iff);
         ("<:", Microsoft.Boogie.BinaryOperator.Opcode.Subtype)
      ]

    type AddCmdInfo =
      | AddEnsures of Boogie.Ensures
      | AddRequires of Boogie.CallCmd * Boogie.Requires
      | AddNothing

    type TokenWithAddCmdInfo (t:Token, ai:AddCmdInfo) =
      inherit ForwardingToken(t, fun () -> t.Value)
      member this.GetAddInfo () = ai           
      
    let noToken = Microsoft.Boogie.Token.NoToken
    let tok t = new BoogieToken.Token (t)
      
    let trIdent id =    
      let res = Microsoft.Boogie.Expr.Ident(sanitize id, Microsoft.Boogie.Type.Int)
      res.Type <- null
      res
       
    let rec trType t =
      match t with
        | Bool -> Microsoft.Boogie.Type.Bool
        | Int -> Microsoft.Boogie.Type.Int
        | Map (it, et) ->
          let args = Boogie.TypeSeq [| for t in it -> trType t |]
          let tyargs = Boogie.TypeVariableSeq [| |] 
          Microsoft.Boogie.MapType (noToken, tyargs, args, trType et) :> Microsoft.Boogie.Type
        | Type.Ref id -> Microsoft.Boogie.UnresolvedTypeIdentifier (noToken, sanitize id) :> Microsoft.Boogie.Type
        | Type.Bv n -> Microsoft.Boogie.BvType n :> Microsoft.Boogie.Type


    let trBound tok (n, t) = 
      (Microsoft.Boogie.BoundVariable (tok, Microsoft.Boogie.TypedIdent (tok, sanitize n, trType t)) :> Microsoft.Boogie.Variable)

    let trConstant (n, t) unique = 
      (Microsoft.Boogie.Constant (noToken, Microsoft.Boogie.TypedIdent (noToken, sanitize n, trType t), unique) :> Microsoft.Boogie.Variable)

    let trFormal (n, t) incoming = 
      (Microsoft.Boogie.Formal (noToken, Microsoft.Boogie.TypedIdent (noToken, sanitize n, trType t), incoming) :> Microsoft.Boogie.Variable)

    let rec trLocalVariable ((n, t), where) = 
      let where =
        match where with
          | Some e -> trExpr e
          | None -> null
      let var = Microsoft.Boogie.LocalVariable (noToken, Microsoft.Boogie.TypedIdent (noToken, sanitize n, trType t, where))
      (var :> Microsoft.Boogie.Variable)

    and trExpr e =
      match e with
        | Ref "*" ->
          null :> Microsoft.Boogie.Expr
        | Ref id -> 
          (trIdent id) :> Microsoft.Boogie.Expr
        | Primitive (op, args) ->
          match args with
            | [a; b] ->
              match _try_assoc op binaryOps with
                | Some o -> Microsoft.Boogie.Expr.Binary (o, trExpr a, trExpr b) :> Microsoft.Boogie.Expr
                | None -> printf "unknown boogie binary op: %s" op; die()
            | [a] ->
              match _try_assoc op unaryOps with
                | Some o -> Microsoft.Boogie.Expr.Unary (noToken, o, trExpr a) :> Microsoft.Boogie.Expr
                | None -> printf "unknown boogie unary op: %s" op; die()
            | _ -> die()
        | BoolLiteral b ->
          Microsoft.Boogie.LiteralExpr (noToken, b) :> Microsoft.Boogie.Expr
        | IntLiteral v ->
          Microsoft.Boogie.LiteralExpr (noToken, Microsoft.Basetypes.BigNum.FromBigInt v) :> Microsoft.Boogie.Expr
        | SecLabelLiteral s ->
          match s with
            | "top" -> Microsoft.Boogie.LiteralExpr (noToken, false) :> Microsoft.Boogie.Expr
            | "bot" -> Microsoft.Boogie.LiteralExpr (noToken, true) :> Microsoft.Boogie.Expr
            | _ -> printf "unknown security label: %s" s; die()
        | BvLiteral (v, sz) ->
          Microsoft.Boogie.LiteralExpr (noToken, Microsoft.Basetypes.BigNum.FromBigInt v, sz) :> Microsoft.Boogie.Expr
        | BvConcat(BvLiteral (_, 0), e)
        | BvConcat(e, BvLiteral (_, 0)) -> trExpr e
        | BvConcat(e1, e2) ->
          Microsoft.Boogie.BvConcatExpr(noToken, trExpr e1, trExpr e2) :> Microsoft.Boogie.Expr
        | BvExtract(e, t, f) -> 
          Microsoft.Boogie.BvExtractExpr(noToken, trExpr e, t, f) :> Microsoft.Boogie.Expr
        | FunctionCall (id, args) ->
          Microsoft.Boogie.NAryExpr (noToken, Microsoft.Boogie.FunctionCall(trIdent id), toExprSeq args) :> Microsoft.Boogie.Expr
        | ArrayIndex (a, ie) ->
          Microsoft.Boogie.NAryExpr (noToken, Boogie.MapSelect (noToken, ie.Length), toExprSeq (a :: ie)) :> Microsoft.Boogie.Expr
        | ArrayUpdate (a, ie, v) ->
          Microsoft.Boogie.NAryExpr (noToken, Boogie.MapStore (noToken, ie.Length), toExprSeq (a :: ie @ [v])) :> Microsoft.Boogie.Expr
        | Old e ->
          Microsoft.Boogie.OldExpr (noToken, trExpr e) :> Microsoft.Boogie.Expr // TODO: in AbsyExpr.scc we have OldExpr : Expr, AI.IFunApp // HACK ???
        | Ite (c, t, e) ->
          Microsoft.Boogie.NAryExpr (noToken, Boogie.IfThenElse (noToken), toExprSeq ([c; t; e])) :> Microsoft.Boogie.Expr
        | Exists (_, [], _, _, e)
        | Forall (_, [], _, _, e) ->
          trExpr e
        | Exists (token, vl, tl, attrs, e) ->
          let vars = Boogie.VariableSeq(List.toArray (List.map (trBound (tok token)) vl))          
          let attrs = toAttributesList attrs
          Boogie.ExistsExpr (tok token, Boogie.TypeVariableSeq [| |], vars, attrs, toTriggersList tl, trExpr e) :> Microsoft.Boogie.Expr
        | Forall (token, vl, tl, attrs, e) -> 
          let vars = Boogie.VariableSeq(List.toArray (List.map (trBound (tok token)) vl))          
          let attrs = toAttributesList attrs
          Boogie.ForallExpr (tok token, Boogie.TypeVariableSeq [| |], vars, attrs, toTriggersList tl, trExpr e) :> Microsoft.Boogie.Expr
        | Lambda (token, vl, attrs, e) -> 
          let vars = Boogie.VariableSeq(List.toArray (List.map (trBound (tok token)) vl))          
          let attrs = toAttributesList attrs
          Boogie.LambdaExpr (tok token, Boogie.TypeVariableSeq [| |], vars, attrs, trExpr e) :> Microsoft.Boogie.Expr

    // TODO: In case the trigger is {foo(x,y) != const}, should we make it {foo(x,y)}? Does != work in triggers?
    and toTriggersList (l:list<list<Expr>>) =
      match l with
        | [] -> null
        | [[]] -> null      
        | l ->
          List.foldBack (
            fun (p:Microsoft.Boogie.Trigger) (n:Microsoft.Boogie.Trigger) -> p.Next <- n; p) 
            (List.map (fun el -> Microsoft.Boogie.Trigger (noToken, true, (toExprSeq el))) l) null

    and toAttributesList (attr:list<Attribute>) =
      let rec convert = function
        | ExprAttr (key, value) :: rest -> Microsoft.Boogie.QKeyValue (noToken, key, glist [(trExpr value :> obj)], convert rest)
        | StringAttr (key, value) :: rest -> Microsoft.Boogie.QKeyValue (noToken, key, glist [(value :> obj)], convert rest)
        | [] -> null
      convert attr

    and toExprSeq l =
      Microsoft.Boogie.ExprSeq (List.toArray (List.map trExpr l))

    let toIdentifierExprSeq l =
      Microsoft.Boogie.IdentifierExprSeq (List.toArray (List.map trIdent l))


    type Stmt =
      | Assert of list<Attribute> * Token * Expr // can generate errors
      | Assume of list<Attribute> * Expr
      | Havoc of list<Id>
      | Assign of Expr * Expr
      | Call of Token * list<Id> * Id * list<Expr> // can generate errors
      | If of Token * Expr * Stmt * Stmt
      | While of Expr * list<Token * Expr> * Stmt // invariants can generate errors
      | Label of Token * Id // appear in the error trace
      | Goto of Token * list<Id>
      | Block of list<Stmt>
      | VarDecl of Var * option<Expr>
      | Comment of string    
      | Return of Token
      | Empty

      static member MkAssume e = Assume ([], e)
      static member MkAssert (t, e) = Assert ([], t, e)
      
    let rec mapStmt f s =
      match f s with
        | Some s -> s
        | None ->
          let self = mapStmt f
          match s with
            | Return _
            | Goto _
            | Comment _
            | VarDecl _
            | Assert _
            | Assume _
            | Havoc _
            | Stmt.Label _
            | Assign _
            | Empty
            | Call _ -> s
            | If (c, tok, t, e) -> If (c, tok, self t, self e)
            | While (a, b, s) -> While (a, b, self s)
            | Block stmts -> Block (List.map self stmts)
    
    let writtenVars stmt =
      let vars = gdict()
      let varList = ref []
      let useV v =
        if not (vars.ContainsKey v) then
          varList := v :: !varList
          vars.Add (v, true)
      let aux = function
        | Havoc ids
        | Call (_, ids, _, _) ->
          List.iter useV ids
          None
        | Assign (e, _) ->
          let rec f = function
            | Expr.ArrayIndex (e, _) -> f e
            | Expr.Ref v -> useV v
            | e -> failwith ("wrong thing assigned to " + e.ToString())
          f e
          None
        | _ -> None
      mapStmt aux stmt |> ignore
      !varList

    type AbstrCmd =
       | Label of string
       | StructuredCmd of Microsoft.Boogie.StructuredCmd
       | TransferCmd of Microsoft.Boogie.TransferCmd
       | Cmd of Microsoft.Boogie.Cmd
    

    let mutable id = 0
    let anonName () = id <- id + 1; "anon" + id.ToString()
   
    let toStmtList cmds =
      let rec getSimple acc lst =
        match lst with
          | Cmd c :: rest -> getSimple (c :: acc) rest
          | rest -> (List.rev acc, rest)

      let rec loop blocks cmds =
        match cmds with
          | Label label :: rest ->
            match getSimple [] rest with
              | (simple, StructuredCmd cmd :: rest) ->
                loop (Microsoft.Boogie.BigBlock (noToken, label, Microsoft.Boogie.CmdSeq (List.toArray simple), cmd, null) :: blocks) rest
              | (simple, TransferCmd cmd :: rest) ->
                loop (Microsoft.Boogie.BigBlock (noToken, label, Microsoft.Boogie.CmdSeq (List.toArray simple), null, cmd) :: blocks) rest
              | (simple, rest) ->
                loop (Microsoft.Boogie.BigBlock (noToken, label, Microsoft.Boogie.CmdSeq (List.toArray simple), null, null) :: blocks) rest
          | [] -> List.rev blocks
          | x -> loop blocks (Label (anonName ()) :: x)
      
      let blocks =
        match loop [] cmds with
          | [] -> [Microsoft.Boogie.BigBlock (noToken, anonName(), Microsoft.Boogie.CmdSeq([| |]), null, null)]
          | x -> x
       
      Microsoft.Boogie.StmtList (System.Collections.Generic.List blocks, noToken)


    let rec trStmt s =
      match s with
        | Assert (attrs, token, e) ->
          let cmd =
            match token with
              | :? TokenWithAddCmdInfo as twaci ->
                match twaci.GetAddInfo() with
                  | AddNothing -> Boogie.AssertCmd (tok token, trExpr e)
                  | AddEnsures ens -> 
                    let res = Boogie.AssertEnsuresCmd ens
                    res.Expr <- trExpr e
                    res :> Boogie.AssertCmd
                  | AddRequires (c, r) ->
                    let res = Boogie.AssertRequiresCmd (c, r)
                    res.Expr <- trExpr e
                    res :> Boogie.AssertCmd
              | _ -> Boogie.AssertCmd (tok token, trExpr e)          
          cmd.Attributes <- toAttributesList attrs
          [Cmd cmd]
        | Assume (attrs, e) -> 
          let assump = Boogie.AssumeCmd (noToken, trExpr e)
          assump.Attributes <- toAttributesList attrs
          [Cmd assump]
        | Havoc il ->
          [Cmd (Microsoft.Boogie.HavocCmd (noToken, toIdentifierExprSeq il) :> Microsoft.Boogie.Cmd)]
        | Assign (lhs, rhs) ->
          let lhs =
            match lhs with
              | Ref id -> (Boogie.SimpleAssignLhs (noToken, trIdent id) :> Boogie.AssignLhs)
              | ArrayIndex (Ref a, ie) -> 
                (Boogie.MapAssignLhs (noToken, Boogie.SimpleAssignLhs (noToken, trIdent a), 
                                      glist (List.map trExpr ie)) :> Boogie.AssignLhs)
              | _ -> die()
          [Cmd (Microsoft.Boogie.AssignCmd (noToken, glist [lhs], glist [trExpr rhs]) :> Microsoft.Boogie.Cmd)]
        | Call (token, il, f, args) ->
          [Cmd (Microsoft.Boogie.CallCmd (tok token, sanitize f, toExprSeq args, toIdentifierExprSeq il) :> Microsoft.Boogie.Cmd)]
        | If (token, c, t, Block []) -> 
          [StructuredCmd 
            (Microsoft.Boogie.IfCmd (tok token, trExpr c, toStmtList (trStmt t), null, null) :> Microsoft.Boogie.StructuredCmd)]
        | If (token, c, t, e) -> 
          [StructuredCmd 
            (Microsoft.Boogie.IfCmd (tok token, trExpr c, toStmtList (trStmt t), null, toStmtList (trStmt e)) :> Microsoft.Boogie.StructuredCmd)]
        | While (e, tinvl, b) ->
          [StructuredCmd (Microsoft.Boogie.WhileCmd (noToken, trExpr e, 
                            System.Collections.Generic.List [ 
                              for (token, inv) in tinvl -> 
                                Microsoft.Boogie.AssertCmd(tok token, trExpr inv) :> Microsoft.Boogie.PredicateCmd ], // TODO: is this ok? can invariant be free?
                            toStmtList (trStmt b)) :> Microsoft.Boogie.StructuredCmd)]
        | Stmt.Label (token, s) -> 
          [Label s] // TODO: how to translate token for label?
        | Goto (token, ls) ->
          [TransferCmd (Microsoft.Boogie.GotoCmd (tok token, Microsoft.Boogie.StringSeq (List.toArray ls)) :> Microsoft.Boogie.TransferCmd)]
        | Block stmts -> 
          List.concat (List.map trStmt stmts)
        | Comment s ->
          [Cmd (Microsoft.Boogie.CommentCmd (s) :> Microsoft.Boogie.Cmd)]
        | Empty -> []
        | Return t ->
          [TransferCmd (Microsoft.Boogie.ReturnCmd (tok t))]
        | VarDecl _ -> die()


    type Contract =
      | Requires of Token * Expr // can generate errors
      | Ensures of Token * Expr // can generate errors        
      | FreeRequires of Expr
      | FreeEnsures of Expr
      | Modifies of Id

    type ConstData = 
      { 
        Unique: bool; 
        Name: Id; 
        Type: Type; 
      }

    type ProcData = 
      {     
        Name: string;
        Token : Token;
        InParms: list<Var>;
        OutParms: list<Var>;
        Contracts: list<Contract>;
        Locals: list<Var * option<Expr>>;
        Body: option<Stmt>;
        Attributes: list<Attribute>
      }

    type Decl =
      | Const of ConstData
      | Function of Type * list<Attribute> * Id * list<Var> * option<Expr>
      | Axiom of Expr
      | Proc of ProcData
      | TypeDef of Id
  //    | Comment of string // TODO: what to do with Comment Decl ?

    let trDecl d =
      match d with
        | Const c -> 
          [(trConstant (c.Name, c.Type) c.Unique :> Microsoft.Boogie.Declaration)]
        | Function (t, attrs, f, vars, body) ->
          let fdecl =
            Microsoft.Boogie.Function (noToken, sanitize f, 
              Boogie.TypeVariableSeq [| |],
              Microsoft.Boogie.VariableSeq ([| for (n, t) in vars -> trFormal (n, t) false |]),
              trFormal (Microsoft.Boogie.TypedIdent.NoName, t) false, null, toAttributesList attrs)
          if body.IsSome then fdecl.Body <- trExpr body.Value
          [fdecl :> Microsoft.Boogie.Declaration]
        | Axiom e ->
          [(Microsoft.Boogie.Axiom(noToken, trExpr e) :> Microsoft.Boogie.Declaration)]
        | Proc p -> 
          let inparms = Microsoft.Boogie.VariableSeq ([| for x in p.InParms -> trFormal x true |])
          let outparms = Microsoft.Boogie.VariableSeq ([| for x in p.OutParms -> trFormal x false |])
          let addVars = ref []
          let aux = function
            | VarDecl (v, where) -> addVars := (v, where) :: !addVars; Some (Block [])
            | _ -> None
          let body =
            match p.Body with
              | None -> None
              | Some b -> Some (mapStmt aux b)
          let proc =      
            Microsoft.Boogie.Procedure (tok p.Token, sanitize p.Name, Boogie.TypeVariableSeq [| |], inparms, outparms,
              Microsoft.Boogie.RequiresSeq [| for e in p.Contracts do 
                                                match e with
                                                  | Requires (token, e) -> yield Microsoft.Boogie.Requires (tok token, false, trExpr e, null)
                                                  | FreeRequires (e) -> yield Microsoft.Boogie.Requires (noToken, true, trExpr e, null)
                                                  | _ -> yield! []
                                           |],
              Microsoft.Boogie.IdentifierExprSeq [| for n in p.Contracts do
                                                      match n with
                                                        | Modifies n -> yield trIdent n
                                                        | _ -> yield! []
                                                 |],
              Microsoft.Boogie.EnsuresSeq [| for e in p.Contracts do
                                               match e with
                                                 | Ensures (token, e) -> yield Microsoft.Boogie.Ensures (tok token, false, trExpr e, null)
                                                 | FreeEnsures (e) -> yield Microsoft.Boogie.Ensures (noToken, true, trExpr e, null)
                                                 | _ -> yield! []
                                          |],
              toAttributesList p.Attributes)
          [(proc :> Microsoft.Boogie.Declaration)] @ 
            match body with
              | Some (b) ->                       
                let impl = 
                  Microsoft.Boogie.Implementation (noToken, sanitize p.Name, Boogie.TypeVariableSeq [| |], inparms, outparms, 
                    Microsoft.Boogie.VariableSeq ([| for v in p.Locals @ !addVars -> trLocalVariable v |]), toStmtList (trStmt b))
                [(impl :> Microsoft.Boogie.Declaration)]
              | _ -> []
        | TypeDef tid ->
          [(Microsoft.Boogie.TypeCtorDecl (noToken, sanitize tid, 0) :> Microsoft.Boogie.Declaration)]
    

    let trProgram decls =
      let prog = new Microsoft.Boogie.Program()
      prog.TopLevelDeclarations.AddRange (List.concat (List.map trDecl decls))
      prog
      

    let printExpr outWriter expr =
      let stream = new Microsoft.Boogie.TokenTextWriter("<debug>", outWriter, false);
      (trExpr expr).Emit(stream)

    let printStmt outWriter stmt =
      let stream = new Microsoft.Boogie.TokenTextWriter("<debug>", outWriter, false);
      (toStmtList (trStmt stmt)).Emit(stream, 0)

    let printDecl outWriter decl =
      let stream = new Microsoft.Boogie.TokenTextWriter("<debug>", outWriter, false);
      for d in trDecl decl do
        d.Emit(stream, 0)
        
    type Expr with
      member this.Map (f : Expr -> option<Expr>) : Expr =
        let self (e:Expr) = e.Map f
        let selfs = List.map self
        match f this with
          | Some e -> e
          | None ->
            match this with
              | Ref _
              | BoolLiteral _
              | BvLiteral _
              | IntLiteral _
              | SecLabelLiteral _ -> this
              | BvConcat(e1, e2) -> BvConcat(self e1, self e2)
              | BvExtract(e, t, f) -> BvExtract(self e, t, f)
              | Primitive (n, args) -> Primitive (n, selfs args)
              | FunctionCall (n, args) -> FunctionCall (n, selfs args)
              | ArrayIndex (e1, args) -> ArrayIndex (self e1, selfs args)
              | ArrayUpdate (e1, args, e2) -> ArrayUpdate (self e1, selfs args, self e2)
              | Old e -> Old (self e)
              | Ite (c, t, e) -> Ite (self c, self t, self e)
              // Note that the map function is not applied to the attributes.
              // These are usually used for weights and similar stuff anyhow.
              | Exists (token, vars, triggers, attrs, body) ->
                Exists (token, vars, List.map selfs triggers, attrs, self body)
              | Forall (token, vars, triggers, attrs, body) ->
                Forall (token, vars, List.map selfs triggers, attrs, self body)
              | Lambda (token, vars, attrs, body) ->
                Lambda (token, vars, attrs, self body)
                
