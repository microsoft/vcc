//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module Microsoft.Research.Vcc2.CoreCAST

  module C = Microsoft.Research.Vcc2.CAST
  
  let wrb = Microsoft.Research.Vcc2.Util.wrb
  let toString = Microsoft.Research.Vcc2.Util.toString
  let doArgsb = Microsoft.Research.Vcc2.Util.doArgsb

  type
    [<StructuralEquality(false); StructuralComparison(false)>]
    Function = 
    {
      Token: Microsoft.Research.Vcc2.Token;
      IsSpec: bool;
      IsSpecInline: bool;
      RetType: C.Type;
      Name: C.Id;
      Parameters: list<C.Variable>;
      mutable Requires: list<Expr>;
      mutable Ensures: list<Expr>;
      mutable Body: option<Stmt>;
    }
    
    override this.ToString () : string = 
      let b = System.Text.StringBuilder()
      let wr (s:string) = b.Append s |> ignore
      if this.IsSpec then wr "spec " else ()
      if this.IsSpecInline then wr "specinline " else ()
      this.RetType.WriteTo b; wr " "
      doArgsb b (fun (p:C.Variable) -> p.WriteTo b) (this.Name) this.Parameters
      wr "\n"
      let doList pref lst =
        for (e:Expr) in lst do
          wr "  "; wr pref; wr " ";
          e.WriteTo b
          wr ";\n";
      doList "requires" (this.Requires)
      doList "ensures" (this.Ensures)
      b.ToString()    

  and QuantData = 
    {
      Kind: C.QuantKind;
      Variables: list<C.Variable>;
      Triggers: list<list<Expr>>;
      Condition: option<Expr>;
      Body: Expr;
    }

  and Expr =
    | Ref of C.ExprCommon * C.Variable    
    | Prim of C.ExprCommon * C.Op * list<Expr>
    | IntLiteral of C.ExprCommon * bigint
    | BoolLiteral of C.ExprCommon * bool
    | StringLiteral of C.ExprCommon * string
    | Cast of C.ExprCommon * C.CheckedStatus * Expr
    | Result of C.ExprCommon
    | FieldRead of C.ExprCommon * C.Variable * list<C.Field>
    | AddressOfField of C.ExprCommon * C.Variable * list<C.Field>
    | Quant of C.ExprCommon * QuantData
    | Call of C.ExprCommon * Function * list<Expr>
    | ArrElemRead of C.ExprCommon * Expr * Expr
    | AddressOfArrElem of C.ExprCommon * Expr * Expr
    
    override this.ToString () = toString (this.WriteTo)
    
    member x.Common =
      match x with
        | Ref (e, _)
        | Prim (e, _, _)
        | IntLiteral (e, _)
        | BoolLiteral (e, _) 
        | StringLiteral (e, _)         
        | Cast (e, _, _)
        | Result (e)
        | FieldRead (e, _, _)
        | AddressOfField (e, _, _)
        | Quant (e, _)
        | Call (e, _, _)
        | ArrElemRead (e, _, _)
        | AddressOfArrElem (e, _, _)
          -> e
          
    member this.Map (f : Expr -> option<Expr>) : Expr =        
      let rec aux e =
        match f e with
          | Some e -> e
          | None ->
            match e with
              | Ref _
              | IntLiteral _
              | BoolLiteral _
              | StringLiteral _
              | Result _
              | FieldRead _ -> e 
              | AddressOfField _ -> e 
              | Prim (ec, op, es) -> Prim (ec, op, auxs es)
              | Cast (ec, ch, e) -> Cast (ec, ch, aux e)
              | Quant (ec, q) -> Quant (ec, { q with Triggers = List.map auxs q.Triggers; 
                                                     Condition = Option.map aux q.Condition;
                                                     Body = aux q.Body })
              | Call (c, fn, es) -> Call (c, fn, auxs es)
              | ArrElemRead (c, e1, e2) -> ArrElemRead (c, aux e1, aux e2)         
              | AddressOfArrElem (c, e1, e2) -> AddressOfArrElem (c, aux e1, aux e2)
      and auxs = List.map aux
      aux this

    member this.SelfMap (f : (Expr -> Expr) -> Expr -> option<Expr>) : Expr =
      let rec aux (e:Expr) = e.Map f'
      and f' e = f aux e
      this.Map f'
      
    member this.Subst (subst : System.Collections.Generic.Dictionary<C.Variable, Expr>) =
      let repl self e =
        match e with
          | Ref (_, v) when subst.ContainsKey v -> Some (subst.[v])
          | _ -> None
      this.SelfMap repl

    member x.Type = x.Common.Type
    member x.Token = x.Common.Token

    member x.WriteTo (b:System.Text.StringBuilder) : unit =
      let f e = (e:Expr).WriteTo b
      let wr = wrb b
      let wrFields fs = List.iter (fun (f:C.Field) -> wr ("." + f.Name)) fs      
      let doArgs = doArgsb b f
      match x with
        | Ref (_, v) -> wr (v.Name)
        | Prim (_, op, args) -> doArgs (op.ToString()) args
        | BoolLiteral (_, v) -> wr (if v then "true" else "false")
        | IntLiteral (_, l) -> wr (l.ToString())
        | StringLiteral (_, s) -> wr "\""; wr (s.ToString()); wr "\""
        | Cast (_, ch, e) -> wr "("; wr (ch.ToString()); wr " "; wr (x.Type.ToString()); wr ")"; f e
        | Result (_) -> wr "result"
        | FieldRead (_, v, fs) -> wr v.Name; wrFields fs;
        | AddressOfField (_, v, fs) -> wr "&("; wr v.Name; wrFields fs; wr ")";
        | Quant (_, q) ->
          match q.Kind with
            | C.Exists -> wr "exists("
            | C.Forall -> wr "forall("
            | C.Lambda -> wr "lambda("            
          for v in q.Variables do
            wr (v.Type.ToString())
            wr " "
            wr v.Name
            wr "; "
          match q.Condition with
            | Some e -> f e; wr "; "
            | None -> ()
          f q.Body
          wr ")"
        | Call (_, fn, args) -> doArgs fn.Name args
        | ArrElemRead (_, e, off) -> f e; wr "["; f off; wr "]"
        | AddressOfArrElem (_, e, off) -> wr "&"; f e; wr "["; f off; wr "]"

  and Stmt = 
    | VarDecl of C.ExprCommon * C.Variable
    | VarWrite of C.ExprCommon * C.Variable * Expr
    | FieldWrite of C.ExprCommon * C.Variable * list<C.Field> * Expr
    | ArrElemWrite of C.ExprCommon * Expr * Expr * Expr
//    | If of C.ExprCommon * Expr * C.LabelId * C.LabelId
    | If of C.ExprCommon * Expr * Stmt * Stmt // if c then goto l1 else goto l2
    | Goto of C.ExprCommon * C.LabelId
    | Label of C.ExprCommon * C.LabelId
    | Assert of C.ExprCommon * Expr
    | Assume of C.ExprCommon * Expr
    | Return of C.ExprCommon * option<Expr>
    | FunCall of C.ExprCommon * C.Variable * Function * list<Expr>
    | ProcCall of C.ExprCommon * Function * list<Expr>
    | VarKill of C.ExprCommon * C.Variable
//    | Block of C.ExprCommon * list<Stmt> * list<Stmt> // { VarDecl*; Stmt* }
    | Block of C.ExprCommon * list<Stmt> // { Stmt* }

    override this.ToString () = toString (this.WriteTo 0)
  
    member x.Common =
      match x with
        | VarDecl (e, _)
        | VarWrite (e, _, _)
        | FieldWrite (e, _, _, _)
        | ArrElemWrite (e, _, _, _)
        | If (e, _, _, _)
        | Goto (e, _)
        | Label (e, _)
        | Assert (e, _)
        | Assume (e, _)
        | Return (e, _)
        | FunCall (e, _, _, _)
        | ProcCall (e, _, _)
        | VarKill (e, _)
        | Block (e, _)
          -> e

    member this.Map (f : Stmt -> option<Stmt>, g : Expr -> Expr) : Stmt =
      let rec aux s =
        match f s with
          | Some ss -> ss
          | None ->
            match s with
              | Return (_, None)
              | Goto _
              | Label _ 
              | VarKill _
              | VarDecl _ -> s
              | VarWrite (ec, v, e) -> VarWrite (ec, v, g e)
              | FieldWrite (ec, v, fs, e) -> FieldWrite (ec, v, fs, g e)
              | ArrElemWrite (ec, e1, e2, e3) -> ArrElemWrite (ec, g e1, g e2, g e3)
              | If (ec, c, s1, s2) -> If (ec, g c, aux s1, aux s2)
              | Assert (ec, e) -> Assert (ec, g e)
              | Assume (ec, e) -> Assume (ec, g e)
              | Return (ec, Some e) -> Return (ec, Some (g e))
              | FunCall (ec, v, f, es) -> FunCall (ec, v, f, List.map g es)
              | ProcCall (ec, f, es) -> ProcCall (ec, f, es)
              | Block (ec, ss) -> Block (ec, List.map aux ss)
      aux this

    member this.Map (f : Stmt -> option<Stmt>) : Stmt =
      this.Map (f, fun x -> x)

    member x.WriteTo (ind:int) b : unit =
      let f s = (s:Stmt).WriteTo (ind + 2) b
      let fe s = (s:Stmt).WriteTo System.Int32.MinValue b
      let fe e = (e:Expr).WriteTo b
      let wr = wrb b
      let wrFields fs = List.iter (fun (f:C.Field) -> wr ("." + f.Name)) fs
      let doArgs = doArgsb b fe
      let doInd ind = 
        if ind > 0 then wr (System.String(' ', ind))
      doInd ind    
      match x with
        | VarDecl (_, v) ->
          wr (v.Type.ToString()); wr " "; wr v.Name; wr ";\n"
        | VarWrite (_, v, e) ->
          wr v.Name; wr " = "; fe e; wr ";\n"
        | FieldWrite (_, v, fs, e) -> 
          wr v.Name; wrFields fs; wr " = "; fe e; wr ";\n"
        | ArrElemWrite (_, e1, e2, e3) -> 
          fe e1; wr "["; fe e2; wr "] = "; fe e3; wr ";\n"
        | If (_, cond, th, el) ->
          wr "if ("; fe cond; wr ")\n"; f th; doInd ind; wr "else\n"; f el; wr ";\n"
        | Goto (_, l) -> wr "goto "; wr l.Name; wr ";\n"
        | Label (_, l) -> wr l.Name; wr ":\n"
        | Assert (_, e) -> wr "assert "; fe e; wr ";\n"
        | Assume (_, e) -> wr "assume "; fe e; wr ";\n"
        | Return (_, Some (e)) -> wr "return "; fe e; wr ";\n"
        | Return (_, None) -> wr "return;\n"
        | FunCall (_, v, fn, args) -> 
          wr v.Name; wr " = "; doArgs fn.Name args; wr ";\n"
        | ProcCall (_, fn, args) -> doArgs fn.Name args; wr ";\n"
        | VarKill (_, v) -> wr "varkill"; wr v.Name; wr ";\n"
        | Block (_, ss) ->
          wr "{\n";
          for s in ss do f s
          doInd ind;
          wr "}\n"

  type [<StructuralEquality(false); StructuralComparison(false)>] Top =
//    | Global of C.Variable // TODO
    | TypeDecl of C.TypeDecl
    | FunctionDecl of Function

    override this.ToString () = toString (this.WriteTo)
    
    member this.WriteTo b =
      let wr = wrb b
      match this with
//        | Global v -> wr (v.ToString() + ";\n")
        | TypeDecl d -> wr (d.Declaration())
        | FunctionDecl d -> 
          wr (d.ToString())
          match d.Body with
            | Some e ->
              e.WriteTo 0 b
            | None -> ()
