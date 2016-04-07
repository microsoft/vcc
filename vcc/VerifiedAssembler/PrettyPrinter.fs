//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module PrettyPrinter

open Ast


let boolFilter b = b
let StringContains s1 (s2: string) =
    (s2.Contains s1)
let ListContains (sl: string list) s2 =
    match (List.filter boolFilter (List.map (StringContains s2) sl)) with
    | [] -> false
    | _  -> true


let while_list = ref []
let while_add s = 
    while_list := !while_list@[s]
    !while_list

let max i1 i2 = 
    if i1 >= i2 then i1 else i2

//type functions compute the width of expressions and instructions and add it to the AST
let rec typeStmt stmt =
    match stmt with
    | Inst (s,[],w) -> Inst(s,[],w)
    | Inst (s,p,w)  ->
                    let temp = List.map typeParam p;
                    let (l_param, l_width) = List.unzip temp;
                    let width = List.max l_width
                    Inst(s,l_param,width)
    | Label (s)     -> if (ListContains (!while_list) s) then While else Label (s) 
    | Jmp (c, Def(l,w))-> if (ListContains (!while_list) l) then Break(c) else Jmp (c, Def(l,w))
    | Jmp (c,l)     -> Jmp (c,l)
    | Break (c)     -> Break (c)
    | Spec (s)      -> Spec(s)
    | Assert (s)    -> Assert(s)
    | Assume (s)    -> Assume(s)
    | While         -> While
    | Invariant (s) -> Invariant(s)
    | SpecEnds      -> SpecEnds
    | Comment       -> Comment
    
and typeParam param =
    match param with
    | Reg(r,i)         -> (Reg(r,i) , i)
    | Def(d,w)         -> (Def(d,w) , w)
    | StructAcc(s,d,w) -> (StructAcc(s,d,w),w)
    | SizeOf(s,w)      -> (SizeOf(s,w),w)
    | Const(i,w)       -> (Const(i,w), w)
    | Add(p1,p2,w) -> 
                    let (param1,w1) = typeParam p1;
                    let (param2,w2) = typeParam p2;
                    let width = max w1 w2
                    (Add(param1, param2, width) , width)
    | Sub(p1,p2,w) ->
                    let (param1,w1) = typeParam p1;
                    let (param2,w2) = typeParam p2;
                    let width = max w1 w2
                    (Sub(param1, param2, width) , width)
    | Div(p1,p2,w) -> 
                    let (param1,w1) = typeParam p1;
                    let (param2,w2) = typeParam p2;
                    let width = max w1 w2
                    (Div(param1, param2, width) , width)
    | Mul(p1,p2,w) -> 
                    let (param1,w1) = typeParam p1;
                    let (param2,w2) = typeParam p2;
                    let width = max w1 w2
                    (Mul(param1, param2, width) , width)
    | Mem(p,w) -> 
        (match w with
        | 0 -> 
            let (param,width) = typeParam p;
            (Mem(param, width) , width)
        | _ -> (Mem(p,w),w))
    | Not(p,w) ->
                    let (param,width) = typeParam p;
                    (Not(param, width), width)

and typeSpec spec =
    match spec with
    | []                -> []
    | Writes(w)::rest   -> Writes(w)::typeSpec rest
    | Ensures(e)::rest  -> Ensures(e)::typeSpec rest
    | Requires(r)::rest -> Requires(r)::typeSpec rest
    | Maintains(r)::rest-> Maintains(r)::typeSpec rest

/// Evaluate an equation
and typeEquation eq =
    match eq with
    | Function (name, spec, body) -> Function(name, typeSpec spec, (List.map typeStmt body))
    | SpecFunc (s)                -> SpecFunc (s)
    | ConstDef (id, value) -> 
                            let (param, width) = typeParam value;
                            ConstDef(id, param)
    | FwdDecl (id)            -> FwdDecl (id)
    | VarDecl (id,typ)        -> VarDecl (id,typ)
    | StructDecl (id,entries) -> StructDecl(id,entries)
 
and typeProg p =
    match p with
    | Entry(entries) -> Entry(List.map typeEquation entries)

let convertCast w =
    match w with
    | 128 -> "uint128"
    | 64  -> "uint64"
    | 32  -> "uint32"
    | 16  -> "uint16"
    | 8   -> "uint08"
    | _   -> "uint64"
let convertMemCast w =
    match w with
    | 128 -> "uint128*"
    | 64  -> "uint64*"
    | 32  -> "uint32*"
    | 16  -> "uint16*"
    | 8   -> "uint08*"
    | _   -> "uint64*"
let convertMachCast w =
    match w with
    | "byte"  -> "uint08"
    | "word"  -> "uint16"
    | "dword" -> "uint32"
    | "qword" -> "uint64"
    | "near"  -> "uint64" // what width is a near pointer in 64-bit mode???
    | "BYTE"  -> "uint08"
    | "WORD"  -> "uint16"
    | "DWORD" -> "uint32"
    | "QWORD" -> "uint64"
    | "NEAR"  -> "uint64" // what width is a near pointer in 64-bit mode???
    | _       -> "uint64"
let convertCastInst w =
    match w with
    | 64  -> "q"
    | 32  -> "d"
    | 16  -> "w"
    | 8   -> "b"
    | _   -> "u"


//eval functions compute a string representing the AST in C language
let rec evalStmt stmt =
    match stmt with
    | Inst ("ret",[],_)-> "return;"
    | Inst (s,[],w)    -> s+"();"
    | Inst ("lea",[Reg(r,_);Mem(p,w1)],w) -> "lea_reg_"+convertCastInst w+" ("+evalReg r+" ,("+convertMemCast w1+")"+evalParam p+");"
    | Inst ("mov",[Reg(DR0,_);b],_) -> "mov_dr0_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR1,_);b],_) -> "mov_dr1_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR2,_);b],_) -> "mov_dr2_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR3,_);b],_) -> "mov_dr3_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR4,_);b],_) -> "mov_dr4_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR5,_);b],_) -> "mov_dr5_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR6,_);b],_) -> "mov_dr6_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(DR7,_);b],_) -> "mov_dr7_q (" + evalParam b + ");"
    | Inst ("mov",[Reg(CR0,_);b],_) -> "mov_to_CR0 (" + evalParam b + ");"
    | Inst ("mov",[Reg(CR2,_);b],_) -> "mov_to_CR2 (" + evalParam b + ");"
    | Inst ("mov",[Reg(CR3,_);b],_) -> "mov_to_CR3 (" + evalParam b + ");"
    | Inst ("mov",[Reg(CR4,_);b],_) -> "mov_to_CR4 (" + evalParam b + ");"
    | Inst ("mov",[Reg(CR8,_);b],_) -> "mov_to_CR8 (" + evalParam b + ");"
    | Inst ("mov",[b;Reg(CR0,_)],_) -> "mov_from_CR0 (" + evalParam b + ");"
    | Inst ("mov",[b;Reg(CR2,_)],_) -> "mov_from_CR2 (" + evalParam b + ");"
    | Inst ("mov",[b;Reg(CR3,_)],_) -> "mov_from_CR3 (" + evalParam b + ");"
    | Inst ("mov",[b;Reg(CR4,_)],_) -> "mov_from_CR4 (" + evalParam b + ");"
    | Inst ("mov",[b;Reg(CR8,_)],_) -> "mov_from_CR8 (" + evalParam b + ");"
    | Inst (s,[Reg(r,_)],w)    -> s+"_reg_"+convertCastInst w+" ("+evalReg(r)+");"
    | Inst (s,[Reg(r,_);b],w)  -> s+"_reg_"+convertCastInst w+" ("+evalReg(r)+","+evalParam b+");"
    | Inst (s,[Def(r,_)],w)    -> s+"_var_"+convertCastInst w+" (&"+r+");"
    | Inst (s,[Def(r,_);b],w)  -> s+"_var_"+convertCastInst w+" (&" + r + ","+evalParam b+");"
    | Inst (s,[Mem(p,w1)],w)   -> s+"_mem_"+convertCastInst w+" (SS,("+convertMemCast w1+")" + evalMemParam p + ");"
    | Inst (s,[Mem(p,w1);b],w) -> s+"_mem_"+convertCastInst w+" (SS,("+convertMemCast w1+")" + evalMemParam p + ","+evalParam b+");"
    | Inst (s,[a],w)   -> s + "_mem_" + convertCastInst w + " (" + evalParam a + ");"
    | Inst (s,[a;b],w) -> s + "_mem_" + convertCastInst w + " (" + evalParam a + "," + evalParam b + ");"
    | Inst (s,_,w)     -> s + " + Parameters"
    | Label (s)        -> s+":"
    | Jmp (Z, l)       -> "if (core.RFLAGS.ZF != 0) goto "+evalParam l+";\n"
    | Jmp (NZ, l)      -> "if (core.RFLAGS.ZF == 0) goto "+evalParam l+";\n"
    | Jmp (E, l)       -> "if (core.RFLAGS.ZF != 0) goto "+evalParam l+";\n"
    | Jmp (NE, l)      -> "if (core.RFLAGS.ZF == 0) goto "+evalParam l+";\n"
    | Jmp (NC, l)      -> "if (core.RFLAGS.CF == 0) goto "+evalParam l+";\n"
    | Jmp (EMPTY, l)   -> "goto "+evalParam l+";\n"
    | Break (Z)        -> "if (core.RFLAGS.ZF == 0) break;\n}\n"
    | Break (NZ)       -> "if (core.RFLAGS.ZF != 0) break;\n}\n"
    | Break (E)        -> "if (core.RFLAGS.EF == 0) break;\n}\n"
    | Break (NE)       -> "if (core.RFLAGS.EF != 0) break;\n}\n"
    | Break (NC)       -> "if (core.RFLAGS.CF != 0) break;\n}\n"
    | Break (EMPTY)    -> "\n}\n"
    | While            -> "while(1)\n"
    | Spec (s)         -> "spec "+s
    | Assert (s)       -> "assert "+s
    | Assume (s)       -> "assume "+s
    | Invariant (s)    -> "invariant "+s
    | SpecEnds         -> "{\n"
    | Comment          -> ""
    
and evalReg(r) = 
    match r with
    | RAX -> "RAX"
    | RBX -> "RBX"
    | RCX -> "RCX"
    | RDX -> "RDX"
    | RDI -> "RDI"
    | RSI -> "RSI"
    | RBP -> "RBP"
    | RSP -> "RSP"
    | R8  -> "R8"
    | R9  -> "R9"
    | R10 -> "R10"
    | R11 -> "R11"
    | R12 -> "R12"
    | R13 -> "R13"
    | R14 -> "R14"
    | R15 -> "R15"
    | CR0 -> "CR0"
    | CR1 -> "CR1"
    | CR2 -> "CR2"
    | CR3 -> "CR3"
    | CR4 -> "CR4"
    | CR5 -> "CR5"
    | CR6 -> "CR6"
    | CR7 -> "CR7"
    | CR8 -> "CR8"
    
    | XMM0  -> "XMM0"
    | XMM1  -> "XMM1"
    | XMM2  -> "XMM2"
    | XMM3  -> "XMM3"
    | XMM4  -> "XMM4"
    | XMM5  -> "XMM5"
    | XMM6  -> "XMM6"
    | XMM7  -> "XMM7"
    | XMM8  -> "XMM8"
    | XMM9  -> "XMM9"
    | XMM10 -> "XMM10"
    | XMM11 -> "XMM11"
    | XMM12 -> "XMM12"
    | XMM13 -> "XMM13"
    | XMM14 -> "XMM14"
    | XMM15 -> "XMM15"
    
    | CS -> "CS"
    | DS -> "DS"
    | ES -> "ES"
    | FS -> "FS"
    | GS -> "GS"
    | SS -> "SS"
    
    | DR0 -> "DR0"
    | DR1 -> "DR1"
    | DR2 -> "DR2"
    | DR3 -> "DR3"
    | DR4 -> "DR4"
    | DR5 -> "DR5"
    | DR6 -> "DR6"
    | DR7 -> "DR7"
and evalRegCore r =
                        match r with
                        | RAX -> "core.R[RAX]"
                        | RBX -> "core.R[RBX]"
                        | RCX -> "core.R[RCX]"
                        | RDX -> "core.R[RDX]"
                        | RDI -> "core.R[RDI]"
                        | RSI -> "core.R[RSI]"
                        | RBP -> "core.R[RBP]"
                        | RSP -> "core.R[RSP]"
                        | R8  -> "core.R[R8]"
                        | R9  -> "core.R[R9]"
                        | R10 -> "core.R[R10]"
                        | R11 -> "core.R[R11]"
                        | R12 -> "core.R[R12]"
                        | R13 -> "core.R[R13]"
                        | R14 -> "core.R[R14]"
                        | R15 -> "core.R[R15]"
                        
                        | CR0 -> "core.CR0"
                        | CR1 -> "core.CR1"
                        | CR2 -> "core.CR2"
                        | CR3 -> "core.CR3"
                        | CR4 -> "core.CR4"
                        | CR5 -> "core.CR5"
                        | CR6 -> "core.CR6"
                        | CR7 -> "core.CR7"
                        | CR8 -> "core.CR8"
    
                        | XMM0  -> "core.XMM[0]"
                        | XMM1  -> "core.XMM[1]"
                        | XMM2  -> "core.XMM[2]"
                        | XMM3  -> "core.XMM[3]"
                        | XMM4  -> "core.XMM[4]"
                        | XMM5  -> "core.XMM[5]"
                        | XMM6  -> "core.XMM[6]"
                        | XMM7  -> "core.XMM[7]"
                        | XMM8  -> "core.XMM[8]"
                        | XMM9  -> "core.XMM[9]"
                        | XMM10 -> "core.XMM[10]"
                        | XMM11 -> "core.XMM[11]"
                        | XMM12 -> "core.XMM[12]"
                        | XMM13 -> "core.XMM[13]"
                        | XMM14 -> "core.XMM[14]"
                        | XMM15 -> "core.XMM[15]"
    
                        | CS -> "core.SR[CS]"
                        | DS -> "core.SR[DS]"
                        | ES -> "core.SR[ES]"
                        | FS -> "core.SR[FS]"
                        | GS -> "core.SR[GS]"
                        | SS -> "core.SR[SS]"
    
                        | DR0 -> "core.DR0"
                        | DR1 -> "core.DR1"
                        | DR2 -> "core.DR2"
                        | DR3 -> "core.DR3"
                        | DR4 -> "core.DR4"
                        | DR5 -> "core.DR5"
                        | DR6 -> "core.DR6"
                        | DR7 -> "core.DR7"

and evalParam param =
    match param with
    | Reg(r,_)         -> evalRegCore r
    | Def(d,_)         -> d
    | StructAcc(s,d,_) -> "(offsetof(struct " + s + ", " + d + "))"
    | SizeOf(s,_)      -> "sizeof(struct "+s+")"
    | Const(i,_)       -> i.ToString()
    | Add(p1,p2,_)     -> evalParam p1 + " + " + evalParam p2
    | Sub(p1,p2,_)     -> evalParam p1 + " - " + evalParam p2
    | Div(p1,p2,_)     -> evalParam p1 + " / " + evalParam p2
    | Mul(p1,p2,_)     -> evalParam p1 + " * " + evalParam p2
    | Mem(p,w)         -> "*(" + convertMemCast w + ")(" + evalMemParam p + ")"
    | Not(p,w)         -> "~(" + evalParam p + ")" 
and evalMemParam param =
    match param with
    | Reg(r,i) -> match i with
                  | 64 -> evalRegCore r //ToDo: Pointer casts
                  | _  -> "unknownSize" + evalRegCore r
    | Def(d,_)         -> d
    | StructAcc(s,d,_) -> "(offsetof(struct " + s + ", " + d + "))"
    | SizeOf(s,_)      -> "sizeof(struct "+s+")"
    | Const(i,_)       -> (i / 8L).ToString()
    | Add(p1,p2,_)     -> evalMemParam p1 + " + " + evalMemParam p2
    | Sub(p1,p2,_)     -> evalMemParam p1 + " - " + evalMemParam p2
    | Div(p1,p2,_)     -> evalMemParam p1 + " / " + evalMemParam p2
    | Mul(p1,p2,_)     -> evalMemParam p1 + " * " + evalMemParam p2
    | Mem(p,_)         -> "Memory Access in Memory Access *(U8*)(" + evalParam p + ")"
    | Not(p,w)         -> "~(" + evalMemParam p + ")"

and evalSpec spec =
    match spec with
    | []                 -> ""
    | Writes(w)::rest    -> "writes " + w + "\n" + evalSpec rest
    | Ensures(e)::rest   -> "ensures " + e + "\n" + evalSpec rest
    | Requires(r)::rest  -> "requires " + r + "\n" + evalSpec rest
    | Maintains(m)::rest -> "maintains " + m + "\n" + evalSpec rest

/// Evaluate an equation
and evalEquation eq =
    match eq with
    | Function (name, spec, body) -> "void " + name + " ()\n" + evalSpec spec + " {\n" + String.concat "\n" (List.map evalStmt body) + "\n}\n"
    | SpecFunc (s)                -> "spec " + s + "\n"
    | ConstDef (id, value)        -> "#define " + id + " " + evalParam value
    | FwdDecl (id)                -> "void " + id + " ();\n"
    | VarDecl (id,typ)            -> convertMachCast typ + " " + id + ";\n"
    | StructDecl (id, entries)    -> "struct "+id+"{\n" + String.concat "\n" (List.map evalStructEntry entries) + "\n};\n"
    
and evalStructEntry (id,typ) = convertCast typ + " " + id + ";\n"
    
and evalProg p =
    match p with
    | Entry(entries) -> String.concat "\n" (List.map evalEquation entries)
