//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

module Microsoft.Research.Vcc.DataTypes

open Microsoft.Research.Vcc
open Microsoft.Research.Vcc.Util
open Microsoft.Research.Vcc.TransUtil
open Microsoft.Research.Vcc.CAST

// for datatype definition check that
// - the induction is grounded (there is a non-recursive option)
let checkDatatypeDefinitions (helper:TransHelper.TransEnv) decls =
  let cache = gdict()
  let rec grounded (td:TypeDecl) =
    match cache.TryGetValue td with
      | true, res -> res
      | _ ->
        cache.Add (td, false)
        let res = td.DataTypeOptions |> List.exists (fun fd -> fd.Parameters |> List.forall (fun p -> groundedType p.Type))
        cache.[td] <- res
        res
  and groundedType = function
    | Type.Ref td ->
      not td.IsDataType || grounded td
    | _ -> true

  let aux = function 
    | Top.TypeDecl td when td.IsDataType ->
      if not (grounded td) then
        helper.Error (td.Token, 9725, "a finite instance of datatype '" + td.Name + "' could never be constructed", None)
    | _ -> ()
  List.iter aux decls
  decls

let handleSize (helper:TransHelper.TransEnv) self = function
  | Macro (ec, "\\size", [e]) ->
    Some (Macro (ec, "size", [self e]))
  | _ -> None

let wrapDatatypeCtors (helper:TransHelper.TransEnv) (ctx:ExprCtx) self = function
  | Call (ec, fn, tps, args) as e when not ctx.IsPure && fn.IsDatatypeOption ->
    Some (Pure (ec, Call (ec, fn, tps, List.map self args)))
  | _ -> None

// for match stmt check that
// - each branch uses the same type
// - each branch ends with break or return
// - add assert(false) for unused options
// - each datatype option is used at most once

let handleMatchStatement (helper:TransHelper.TransEnv) desugarSwitch labels expr =
  let usedCases = gdict() 
  let testHd expr fn =
    Expr.Macro (boolBogusEC(), "dt_testhd", [expr; Expr.UserData (boolBogusEC(), fn)])
 
  let rec fallOff nm expr = 
    let self = fallOff nm 
    match expr with
    | Expr.Block (_, stmts, _) -> List.forall self stmts
    | Expr.If (_, _, _, th, el) -> self th || self el
    | Expr.Assert (_, EFalse, _)
    | Expr.Assume (_, EFalse)
    | Expr.Return _ -> false
    | Expr.Goto (_, nm') -> nm <> nm'
    | _ -> true

  let (|Case|_|) = function
    | Macro (_, "case", [Block (blockEc, stmts, None)]) ->
      Some (blockEc, stmts)
    | Macro (_, "case", [Call _ as call]) ->
      Some (call.Common, [call])
    | _ -> None

  let compileCases expr (dtTd:TypeDecl) cases =
    let rec aux = function
      | Case (blockEc, stmts) :: rest ->
        let unique = helper.UniqueId()
        let case_end = { Name = "match_end_" + unique.ToString() } : LabelId
        let labels = 
          match labels with
            | Some(_, continue_lbl) -> Some(case_end, continue_lbl)
            | None -> Some(case_end, ({ Name = "dummy_label"} : LabelId))
        let rec findPattern acc = function
          | Call (ec, fn, _, args) :: rest when fn.IsDatatypeOption ->
            Some (ec, fn, args, List.rev acc, rest)
          | (Expr.Skip _ | Expr.VarDecl _ | Expr.Comment _ as x) :: rest ->
            findPattern (x :: acc) rest
          | _ -> 
            None
        let buildBody stmts =
          let body = desugarSwitch labels (Expr.MkBlock stmts)
          if fallOff case_end body then
            helper.Error (blockEc.Token, 9728, "possible fall-off from a match case")
          body

        match findPattern [] stmts with
          | Some (ec, fn, args, pref, suff) ->
            match usedCases.TryGetValue fn.UniqueId with
              | true, loc ->
                helper.Error (ec.Token, 9726, "the datatype case '" + fn.Name + "' is used more than once", Some loc)
              | false, _ ->
                if dtTd.DataTypeOptions |> _list_mem fn then
                  usedCases.Add (fn.UniqueId, ec.Token)
                else
                  helper.Error (ec.Token, 9727, "case '" + fn.Name + "' is not a member of " + dtTd.Name)
            let mkAssign (n:int) (e:Expr) =
              let fetch = Macro ({ bogusEC with Type = e.Type }, ("DP#p" + n.ToString() + "#" + fn.Name), [expr])
              Macro (voidBogusEC(), "=", [e; fetch])
            let assignments = args |> List.mapi mkAssign
            let body = pref @ assignments @ suff @ [Expr.Label (bogusEC, case_end)]
            let body = buildBody body
            Expr.If ({ ec with Type = Void }, None, testHd expr fn, body, (aux rest))
          | None ->
            if rest <> [] then
              helper.Error (rest.Head.Token, 9726, "case is unreachable (after the default: label)") 
            buildBody stmts
      | [] ->
        let asserts = 
          dtTd.DataTypeOptions 
            |> List.filter (fun f -> not (usedCases.ContainsKey f.UniqueId))
            |> List.map (fun f -> 
                  let err = afmte 8030 ("case " + f.Name + " is unhandled when matching {0}") [expr]
                  Expr.MkAssert ((mkNot (testHd expr f)).WithCommon err))
        let finalErr = afmte 8030 "some case is unhandled when matching {0}" [expr] // this shouldn't really happen
        Expr.MkBlock (asserts @ [Expr.MkAssert (Expr.False.WithCommon finalErr)])
      | _ -> die()
    aux cases

  match expr with
    | Macro (ec, "match", expr :: cases) ->
      match expr.Type with
        | Type.Ref dtTd when dtTd.IsDataType ->
          let (save, expr) = cache helper "matched" expr VarKind.SpecLocal
          Some (Expr.MkBlock (save @ [compileCases expr dtTd cases]))
        | tp ->
          helper.Error (ec.Token, 9729, "cannot match on non-datatype " + tp.ToString())
          Some (Expr.MkBlock [])
    | _ -> None

let init (helper:TransHelper.TransEnv) =
  helper.AddTransformer ("datatype-check-defs", TransHelper.Decl (checkDatatypeDefinitions helper))