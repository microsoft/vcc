//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
 open System.IO
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.CAST
 
 module Isabelle =

  exception BadType of Token * Type
  exception BadExpression of Expr

  let rename (name : string) = name

  let par withPar s = if withPar then "(" + s + ")" else s

  let rec typeString tok withPar = function
    | Type.Bool -> "bool"
    | Type.MathInteger _ -> "int"
    | Type.Map (dom, rng) ->
      par withPar (typeString tok true dom + " => " + typeString tok false rng)
    | Type.Ref td -> rename td.Name
    | ty -> raise (BadType (tok, ty))

  let argsString tok (args : list<Variable>) (retType : Type) =
    [retType]
    |> List.append (List.map (function (v : Variable) -> v.Type) args)
    |> List.map (typeString tok true)
    |> String.concat " => "

  let exprString (fprefix : string) =
    let rec expr = function
      | Ref (_, v) -> rename v.Name
      | Prim (_, Op (op, _), es) -> app (op, es)
      | Call (_, f, _, es) -> app (f.Name, es)
      | IntLiteral (_, i) -> i.ToString ()
      | BoolLiteral (_, b) -> if b then "True" else "False"
      | Dot (_, e, f) ->
        par true (rename (fprefix + rename f.Name) + " " + expr e)
      | Quant (_, q) -> quant q
      | Macro (_, "ite", [e1; e2; BoolLiteral (_, false)]) ->
        app ("&&", [e1; e2])
      | Macro (_, "ite", [e1; BoolLiteral (_, true); e2]) ->
        app ("||", [e1; e2])
      | Macro (_, "ite", [e1; e2; BoolLiteral (_, true)]) ->
        app ("==>", [e1; e2])
      | Macro (_, "ite", [e1; e2; e3]) ->
        "(if " + expr e1 + " then " + expr e2 + " else " + expr e3 + ")"
      | Macro (_, "map_get", [e1; e2]) ->
        par true (expr e1 + " " + expr e2)
      | Deref (_, Dot (c, Macro (_, "&", [e]), f)) -> expr (Dot (c, e, f))
      | Cast (_, _, e) -> expr e
      | e -> raise (BadExpression e)

    and app = function
      | ("!", [e]) -> par true ("~ " + expr e)
      | ("&&", [e1; e2]) -> par true (expr e1 + " & " + expr e2)
      | ("||", [e1; e2]) -> par true (expr e1 + " | " + expr e2)
      | ("==>", [e1; e2]) -> par true (expr e1 + " --> " + expr e2)
      | ("<==>", [e1; e2]) -> par true (expr e1 + " = " + expr e2)
      | ("==", [e1; e2]) -> par true (expr e1 + " = " + expr e2)
      | ("!=", [e1; e2]) -> par true (expr e1 + " ~= " + expr e2)
      | ("<", [e1; e2]) -> par true (expr e1 + " < " + expr e2)
      | ("<=", [e1; e2]) -> par true (expr e1 + " <= " + expr e2)
      | (">", [e1; e2]) -> par true (expr e2 + " < " + expr e1)
      | (">=", [e1; e2]) -> par true (expr e2 + " <= " + expr e1)
      | ("+", [e1; e2]) -> par true (expr e1 + " + " + expr e2)
      | ("-", [e1; e2]) -> par true (expr e1 + " - " + expr e2)
      | ("*", [e1; e2]) -> par true (expr e1 + " * " + expr e2)
      | ("/", [e1; e2]) -> par true (expr e1 + " div " + expr e2)
      | (n, es) -> par true (String.concat " " (rename n :: List.map expr es))

    and quant (q : QuantData) =
      let kind =
        match q.Kind with
          | Forall -> "ALL"
          | Exists -> "EX"
          | Lambda -> "%"
      let vars =
        List.map (function (v : Variable) -> rename v.Name) q.Variables
      let body =
        match q.Condition with
          | Some e -> app ("==>", [e; q.Body])
          | None -> expr q.Body
      par true (String.concat " " (List.append (kind :: vars) ["."; body]))

    expr


  let dumpTypeDecl (w : StreamWriter) (fprefix : string) (td : TypeDecl) =
    w.WriteLine ("record " + rename td.Name + " =")
    for f in td.Fields do
      w.WriteLine ("  " + fprefix + rename f.Name + " :: \"" +
        (typeString f.Token false f.Type) + "\"")
    w.WriteLine ""

  let dumpFunction (w : StreamWriter) (fprefix : string) (f : Function) =
    let lhs =
      List.map (function (v : Variable) -> rename v.Name) f.Parameters
      |> List.append [rename f.Name]
      |> String.concat " "

    let rhs (e : Expr) =
      match e with
        | Prim (_, Op ("==", _), [_; e']) -> exprString fprefix e'
        | _ -> raise (BadExpression e)

    let vs = f.Parameters
    w.WriteLine ("fun " + rename f.Name + " :: \"" + argsString f.Token vs f.RetType +
      "\" where")
    w.WriteLine ("\"" + lhs + " = " + rhs f.Ensures.[0] + "\"")
    w.WriteLine ""


  let dumpTheory (thyname : string) (fprefix : string) (tds : list<TypeDecl>)
      (funs : list<Function>) (w : StreamWriter) =
    w.WriteLine ("theory " + rename thyname)
    w.WriteLine "imports Main"
    w.WriteLine "begin"
    w.WriteLine ""

    for td in tds do dumpTypeDecl w fprefix td
    for f in funs do dumpFunction w fprefix f

    w.WriteLine "end"


  let dump (helper : TransHelper.TransEnv) (thyname : string) (fprefix : string)
      (decls : list<Top>) =
    let isIsabelleFunction (f : Function) = 
      hasCustomAttr "isabelle" f.CustomAttr
    let isabelleFunction = function
      | Top.FunctionDecl f ->
        if isIsabelleFunction f then Option.Some f
        else Option.None
      | _ -> Option.None
    
    let insert x xs = x :: List.filter (function y -> not (y.Equals x)) xs

    let rec addTypeDecls (tds : list<TypeDecl>) = function
      | Type.Map (dom, rng) -> addTypeDecls (addTypeDecls tds dom) rng
      | Type.Ref td -> List.fold addTypeDeclsFields (insert td tds) td.Fields
      | _ -> tds
    and addTypeDeclsFields (tds : list<TypeDecl>) f =
      addTypeDecls tds f.Type
    let addTypeDecls' (tds : list<TypeDecl>) (v : Variable) =
      addTypeDecls tds v.Type
    let addRequiredTypeDecls (tds : list<TypeDecl>) (f : Function) =
      addTypeDecls (List.fold addTypeDecls' tds f.Parameters) f.RetType

    let funs = List.choose isabelleFunction decls
    let tds = List.fold addRequiredTypeDecls [] funs

    helper.Warning (Token.NoToken, 9125, "The export to Isabelle may " +
      "produce incorrect theories. Check that names of function arguments " +
      "do not collide with constant names defined in Isabelle.")
    try
      using (File.CreateText(thyname + ".thy"))
        (dumpTheory thyname fprefix tds funs)
    with
      | BadType (tok, ty) -> helper.Error (tok, 9722, "Unsupported type.")
      | BadExpression e -> helper.Error (e.Token, 9723, "Unsupported expression.")
    decls
