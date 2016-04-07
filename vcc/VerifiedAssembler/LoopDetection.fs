//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module LoopDetection

open Ast
open PrettyPrinter

let boolFilter b = b
let StringContains s1 (s2: string) =
    (s2.Contains s1)
let ListContains (sl: string list) s2 =
    match (List.filter boolFilter (List.map (StringContains s2) sl)) with
    | [] -> false
    | _  -> true
let label_list = ref []
let label_add s = 
    label_list := !label_list@[s]
    !label_list
let goto_list = ref []
let goto_add s = 
    goto_list := !goto_list@[s]
    !goto_list
let rec loopStmt stmt =
    match stmt with
    | Inst (s,[],w) -> Inst(s,[],w)
    | Inst (s,p,w)  -> Inst(s,p,w)
    | Jmp (c, Def(l,w)) ->
                    let k = if (ListContains (!label_list) l) then while_add l else goto_add l
                    Jmp (c, Def(l,w))
    | Jmp (a,b)     -> Jmp (a,b)
    | Break (c)     -> Break (c)
    | Label (s)     -> 
                    let k = label_add s;
                    Label(s)
    | Spec (s)      -> Spec(s)
    | Assert (s)    -> Assert(s)
    | Assume (s)    -> Assume(s)
    | While         -> While
    | Invariant (s) -> Invariant(s)
    | SpecEnds      -> SpecEnds
    | Comment       -> Comment
/// Evaluate an equation
and loopEquation eq =
    match eq with
    | Function (name, spec, body) -> 
                                  //printfn (new Printf.TextWriterFormat<_> (name)); 
                                  Function(name, spec, (List.map loopStmt body))
    | SpecFunc (s)            -> SpecFunc (s)
    | ConstDef (id, value) -> ConstDef(id, value)
    | FwdDecl (id)            -> FwdDecl (id)
    | VarDecl (id,typ)        -> VarDecl (id,typ)
    | StructDecl (id,entries) -> StructDecl(id,entries)
 
and loopProg p =
    match p with
    | Entry(entries) -> Entry(List.map loopEquation entries)
