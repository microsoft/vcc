//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module RenameFields

open Ast

let keyWords = [ ("auto", "asm_auto");  ("break", "asm_break");  ("case", "asm_case");  ("char", "asm_char");  ("const", "asm_const"); ("continue", "asm_continue"); ("default", "asm_default");  ("do", "asm_do"); 
                 ("double", "asm_double"); ("else", "asm_else"); ("enum", "asm_enum"); ("extern", "asm_extern"); ("float", "asm_float"); ("for", "asm_for"); ("goto", "asm_goto"); ("if", "asm_if"); 
                 ("int", "asm_int"); ("long", "asm_long"); ("register", "asm_register"); ("return", "asm_return"); ("short", "asm_short"); ("signed", "asm_signed"); ("sizeof", "asm_sizeof"); ("static", "asm_static");
                 ("struct", "asm_struct"); ("switch", "asm_switch"); ("typedef", "asm_typedef"); ("union", "asm_union"); ("unsigned", "asm_unsigned"); ("void", "asm_void"); ("volatile", "asm_volatile"); ("while", "asm_while"); ]
let keyMap = Map.ofList keyWords
let renameField id = match keyMap.TryFind id with | Some id' -> id' | None -> id
    

/// Evaluate an equation
let rec renameEquation eq =
    match eq with
    | Function (name, spec, body) -> Function (name, spec, List.map renameStmt body)
    | SpecFunc (s)                -> SpecFunc (s)
    | ConstDef (id, value)        -> ConstDef (id,value)
    | FwdDecl (id)                -> FwdDecl (id)
    | VarDecl (id,typ)            -> VarDecl (id,typ)
    | StructDecl (id, entries)    -> StructDecl (id, List.map renameStructEntry entries)
    
and renameStmt stmt =
    match stmt with
    | Inst (s,[],w)    -> Inst (s, [], w)
    | Inst (s,[a],w)   -> Inst (s, [renameParam a], w)
    | Inst (s,[a;b],w) -> Inst (s, [renameParam a; renameParam b], w)
    | Inst (s,_,w)     -> Inst (s,[],w)
    | Label (s)        -> Label(s)
    | Spec (s)         -> Spec(s)
    | While            -> While
    | Assert (s)       -> Assert(s)
    | Assume (s)       -> Assume(s)
    | Invariant (s)    -> Invariant(s)
    | SpecEnds         -> SpecEnds
    | Comment          -> Comment
    | Jmp (c, g)       -> Jmp (c, g)
    | Break (c)        -> Break(c)

and renameParam param =
    match param with
    | Reg(r,w)         -> Reg(r,w)
    | Def(d,w)         -> Def(d,w)
    | StructAcc(s,d,w) -> StructAcc(s,renameField d,w)
    | SizeOf(s,w)      -> SizeOf(s,w)
    | Const(i,w)       -> Const(i,w)
    | Add(p1,p2,w)     -> Add(renameParam p1,renameParam p2,w)
    | Sub(p1,p2,w)     -> Sub(renameParam p1,renameParam p2,w)
    | Div(p1,p2,w)     -> Div(renameParam p1,renameParam p2,w)
    | Mul(p1,p2,w)     -> Mul(renameParam p1,renameParam p2,w)
    | Mem(p,w)         -> Mem(renameParam p,w)
    | Not(p,w)         -> Not(renameParam p,w)

and renameStructEntry (id,typ) = (renameField id,typ)

let renameProg p =
    match p with
    | Entry(entries) -> Entry (List.map renameEquation entries)
