//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module Ast

open System


type Prog =
    | Entry of OutStmt list
    
and Cond =
    | Z
    | NZ
    | EMPTY
    | E
    | NE
    | NC
    
and Stmt =
    | Inst of String * Param list * Int32
    | Jmp of Cond * Param
    | Break of Cond
    | Label of String
    | While //of Stmt list
    | Spec of String
    | Assume of String
    | Assert of String
    | Invariant of String
    | SpecEnds
    | Comment
    
and OutStmt =
    //| Equation of Expr
    | SpecFunc of String
    | ConstDef of String * Param 
    | Function of String * Spec list * Stmt list
    | FwdDecl of String
    | VarDecl of String * String
    | StructDecl of String * (String * Int32) list
    
and Spec =
    | Writes of String
    | Ensures of String
    | Requires of String
    | Maintains of String
    
and Param =
    | Def of String * Int32
    | StructAcc of String * String * Int32
    | SizeOf of String * Int32
    | Const of Int64 * Int32
    | Add of Param * Param * Int32
    | Sub of Param * Param * Int32
    | Div of Param * Param * Int32
    | Mul of Param * Param * Int32
    | Mem of Param * Int32
    | Not of Param * Int32
    | Reg of RegDef * Int32
    
and RegDef =
    | RAX
    | RBX
    | RCX
    | RDX
    | RDI
    | RSI
    | RBP
    | RSP
    | R8
    | R9
    | R10
    | R11
    | R12
    | R13
    | R14
    | R15
    | CR0
    | CR1
    | CR2
    | CR3
    | CR4
    | CR5
    | CR6
    | CR7
    | CR8
    
    | XMM0
    | XMM1
    | XMM2
    | XMM3
    | XMM4
    | XMM5
    | XMM6
    | XMM7
    | XMM8
    | XMM9
    | XMM10
    | XMM11
    | XMM12
    | XMM13
    | XMM14
    | XMM15
    
    | CS
    | DS
    | ES
    | FS
    | GS
    | SS
    
    | DR0
    | DR1
    | DR2
    | DR3
    | DR4
    | DR5
    | DR6
    | DR7
