//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
 
  module C = Microsoft.Research.Vcc2.CAST
  module Transformers = Microsoft.Research.Vcc2.Transformers
  module CoreC = Microsoft.Research.Vcc2.CoreCAST
   
  module CAST2CoreCAST =
    
    let ignoreFunction (name : string) =
      name.StartsWith "_vcc_" //or name.StartsWith "$" or name.StartsWith "@"

    type AuxField =
      | Field of C.Field
      | Var of C.Variable
        
    let rec trDot (expr : C.Expr) =
      let rec auxDot (expr : C.Expr) =
        match expr with
          | C.Expr.Dot (ec, e, f) -> (auxDot e) @ [Field f]
          | C.Expr.Ref (ec, v) -> [Var v]
          | _ -> failwith "auxDot match expr"
      let vfs = auxDot expr
      let v = match vfs.Head with
                | Var x -> x
                | _ -> failwith "trDot match vfs.Head"
      let fs = List.map (function
                | Field f -> f
                | _ -> failwith "trDot match List.map") vfs.Tail
      (v, fs)
    
    let findValue (v:'b) (dict:Util.Dict<'a,'b>) : option<'a> =
      let mutable found = None
      for item in dict do
        if item.Value = v then
          found <- Some (item.Key)
      found


    type Dict<'a, 'b> = System.Collections.Generic.Dictionary<'a, 'b>

    let functions = new Dict<C.Function, CoreC.Function>()
   
    let lookupFunction cF =
      match functions.TryGetValue cF with
        | (true, corecF) -> corecF
        | _ -> 
          let corecF = { new  CoreC.Function 
                         with Token = cF.Token
                         and  IsSpec = cF.IsSpec
                         and  IsSpecInline = cF.IsSpecInline
                         and  RetType = cF.RetType
                         and  Name = cF.Name
                         and  Parameters = cF.Parameters
                         and  Requires = []
                         and  Ensures = []
                         and  Body = None }        
          functions.Add(cF, corecF)
          corecF
              
              
    let rec trExpr (expr : C.Expr) =
      let trExprs es = List.choose (fun x -> x) (List.map trExpr es)
      let trExprO = Option.get << trExpr
      match expr with
        | C.Expr.Ref (ec, v) -> Some (CoreC.Ref (ec, v))
        | C.Expr.Prim (ec, op, es) ->
          Some (CoreC.Prim (ec, op, trExprs es))
        | C.Expr.IntLiteral (ec, i) -> Some (CoreC.IntLiteral (ec, i))
        | C.Expr.BoolLiteral (ec, b) -> Some (CoreC.BoolLiteral (ec, b))
        | C.Expr.Deref (_, C.Expr.Dot(ec, e, f))  -> 
          let (v, fs) = trDot (C.Expr.Dot(ec, e, f))
          Some (CoreC.FieldRead (ec, v, fs))
        | C.Expr.Dot (ec, e, f) ->
          let (v, fs) = trDot expr
          Some (CoreC.AddressOfField (ec, v, fs))
        | C.Expr.Deref (_, C.Expr.Ref(ec, v)) ->
          Some (CoreC.FieldRead (ec, v, []))
        | C.Expr.Deref (_, C.Index (ec, e1, e2))  -> 
          Some (CoreC.ArrElemRead (ec, trExprO e1, trExprO e2))
        | C.Expr.Index (ec, a, b) -> 
          Some (CoreC.AddressOfArrElem (ec, trExprO a, trExprO b))
        | C.Expr.Cast (_, _, C.Expr.Macro (ec, "_vcc_get_string_literal", [id; len])) ->
          let id = match id with
                     | C.Expr.IntLiteral (_, id) -> Math.BigInt.ToInt32 id
                     | _ -> failwith "trExpr match id"
          None
          //match findValue id Normalizer.miscNorm.stringLiterals with
          //  | Some s -> Some (CoreC.StringLiteral (ec, s))
          //  | None -> None
        | C.Expr.Cast (ec, s, e) -> 
          Some (CoreC.Cast (ec, s, trExprO e))
        | C.Expr.Quant (ec, q) ->
          Some (CoreC.Quant (ec, { 
            Kind = q.Kind;
            Variables = q.Variables;
            Triggers = List.map (fun (l:list<C.Expr>) -> trExprs l) q.Triggers;
            Condition = Option.bind (fun (e:C.Expr) -> trExpr e) q.Condition;
            Body = Option.get (trExpr q.Body) }))
        | C.Expr.Result ec -> Some (CoreC.Result ec)
        | C.Expr.Call (ec, f, es) ->
          if ignoreFunction f.Name then None
          else Some (CoreC.Call (ec, lookupFunction f, List.map trExprO es))
        | C.Expr.Macro (ec, "null", []) when ec.Type = C.Ptr C.Void -> 
          Some (CoreC.IntLiteral (ec, Math.BigInt 0))
        | C.Expr.Macro (ec, "_vcc_ptr_eq", [ptr1; ptr2]) -> 
          Some (CoreC.Expr.Prim(ec, C.Op("==", C.CheckedStatus.Processed), [trExprO ptr1; trExprO ptr2]))
        | C.Expr.Macro (ec, "_vcc_ptr_neq", [ptr1; ptr2]) -> 
          Some (CoreC.Expr.Prim(ec, C.Op("!=", C.CheckedStatus.Processed), [trExprO ptr1; trExprO ptr2]))
        | C.Expr.Macro (ec, "_vcc_typeof", [ptr]) -> 
          Some (trExprO ptr)
        | C.Expr.Macro (ec, "_vcc_vs_ctor", [ptr]) -> 
          Some (trExprO ptr)
        | C.Expr.Macro (ec, "havoc", [ptr]) -> 
          Some (trExprO ptr)
        | C.Expr.Macro (_, _, _) -> None
        | C.Expr.Old (_, _, _) -> None
        | _ -> failwith "trExpr match fail"


    let mutable labelId = 0
    let generateLabel () =
      labelId <- labelId + 1
      { new C.LabelId with Name = "CoreClabel" + labelId.ToString() }
    
    let rec trStmt (expr : C.Expr) =
      let trExprO = Option.get << trExpr
      match expr with
        | C.VarDecl (ec, v) -> [ CoreC.VarDecl (ec, v) ]
        | C.VarWrite (ec, v, e) -> 
          match e with
            | C.Call (_, f, es) -> 
              [ CoreC.FunCall (ec, v, lookupFunction f, List.map trExprO es) ]
            | _ -> 
              [ CoreC.VarWrite (ec, v, trExprO e) ]
        | C.MemoryWrite (ec, e1, e2) ->
          match e1 with
            | C.Dot (_, _, _) ->
              let (v, fs) = trDot e1
              [ CoreC.FieldWrite (ec, v, fs, trExprO e2) ]
            | C.Expr.Ref (_, v) ->
              [ CoreC.FieldWrite (ec, v, [], trExprO e2) ]
            | C.Index (_, ex, ey) ->
              [ CoreC.ArrElemWrite (ec, trExprO ex, trExprO ey, trExprO e2) ]
            | _ -> failwith "trStmt MemoryWrite match"
        | C.If (ec, cond, s1, s2) ->
          let l1 = generateLabel ()
          let l2 = generateLabel ()
          let exit = generateLabel()
          [ CoreC.If (ec, trExprO cond, CoreC.Goto (ec, l1), CoreC.Goto (ec, l2));
            CoreC.Label (ec, l1) ] @ 
          trStmt s1 @
          [ CoreC.Goto (ec, exit); CoreC.Label (ec, l2) ] @
          trStmt s2 @
          [ CoreC.Goto (ec, exit); CoreC.Label (ec, exit) ]
        | C.Loop (ec, invs, writes, s) -> 
          // TODO: deal with invariants, writes ?
          let begin_loop = generateLabel()
          [ CoreC.Label (ec, begin_loop) ] @
          trStmt s @
          [ CoreC.Goto (ec, begin_loop) ]
        | C.Goto (ec, l) -> [ CoreC.Goto (ec, l) ]
        | C.Label (ec, l) -> [ CoreC.Label (ec, l) ]
        | C.Assert (ec, e) -> 
          let eo = trExpr e
          match eo with
            | Some e -> [ CoreC.Assert (ec, e) ]
            | None -> []
        | C.Assume (ec, e) -> 
          let eo = trExpr e
          match eo with
            | Some e -> [ CoreC.Assume (ec, e) ]
            | None -> []
        | C.Block (ec, ss) -> [ CoreC.Block (ec, List.concat (List.map trStmt ss)) ]
        | C.Return (ec, r) -> 
          [ CoreC.Return (ec, Option.bind (fun (e:C.Expr) -> Some (trExprO e)) r) ]
        | C.Stmt (_, (C.Call (ec, f, es))) ->
          if ignoreFunction f.Name then []
          else [ CoreC.ProcCall (ec, lookupFunction f, List.map trExprO es) ]
        | C.Atomic (_, _, _) -> []
        | C.Comment _ -> []
        | _ -> failwith "trStmt match fail"


    let trDecl (decl : C.Top) =
      match decl with
        | C.Axiom _ -> failwith "trDecl Axiom fail"
        | C.GeneratedAxiom _ -> failwith "trDecl GeneratedAxiom fail"
        | C.Top.Global _ -> failwith "trDecl Global fail"
        | C.TypeDecl t -> CoreC.TypeDecl t
        | C.FunctionDecl f ->
          let trExprsO (es:list<C.Expr>) = List.choose (fun x -> x) (List.map trExpr es)
          let fn = lookupFunction f
          let body = 
            match Option.bind (fun (e:C.Expr) -> Some (trStmt e)) f.Body with
              | Some [e] -> Some e
              | Some [] -> Some (CoreC.Block (C.bogusEC, []))
              | Some stmts -> Some (CoreC.Block (C.bogusEC, stmts))
              | None -> None
          fn.Body <- body
          fn.Requires <- trExprsO f.Requires
          fn.Ensures <- trExprsO f.Ensures
          CoreC.FunctionDecl fn

    let printDecls decls =
      for (d:CoreC.Top) in decls do
        printf "%s" (d.ToString())
      printf "\n"

    let apply (helper:Microsoft.Research.Vcc2.Helper.Env) (decls:list<C.Top>) : list<CoreC.Top> =
      let decls = List.map trDecl decls
//      if helper.Options.DumpSource1 then printDecls decls
      decls
      
    let toStmtsArray (stmts:list<CoreC.Stmt>) =
      let rec aux s = 
        match s with
          | CoreC.Block (cc, ss) -> List.concat (List.map aux ss)
          | _ -> [s]
      List.to_array (List.concat (List.map aux stmts))
      
    let printStmts (stmts: array<CoreC.Stmt>) =
      for s in stmts do
        printf "%s" (s.ToString())
      printf "\n"
