//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
  module Background =

    open Microsoft.Z3

    let prove (z3:TypeSafeContext) p = 
      z3.Push()
      printf "to PROVE: %s\n" (z3.ToString(z3.MkNot(p))) 
      z3.AssertCnstr (z3.MkNot(p))
      z3.Display(System.Console.Out)
      let model = ref null in
      let res = 
       match z3.CheckAndGetModel(model) with
        | LBool.True ->  Printf.printf "Z3 says false.\n"; ((!model).Display(System.Console.Out)); (!model).Dispose(); false
        | LBool.False -> Printf.printf "Z3 says true.\n"; true
        | LBool.Undef -> Printf.printf "Unknown result from z3."; false
        | _ -> failwith "prove z3.CheckAndGetModel"
      z3.Pop()
      res
    
    let mk_bool (z3:TypeSafeContext) (b:bool) = 
      match b with
        | true -> z3.MkTrue()
        | false -> z3.MkFalse()
        
    let mk_bv (z3:TypeSafeContext) (b:System.UInt32) (num_bytes:System.UInt32) = 
      z3.MkNumeral(System.String.Format("{0}", b), z3.MkBvType(num_bytes))
    
    let addTestBackground(z3:TypeSafeContext) = 
      let int_type = z3.MkIntType()
      let bool_type = z3.MkBoolType()
      let seq_type = z3.MkIntType() 
        //z3.MkType("seq")
      
      let equals t1 t2 = z3.MkEq(t1, t2)
      let add t1 t2 = z3.MkAdd(t1, t2)
      let sub t1 t2 = z3.MkSub(t1, t2)
      let implies t1 t2 = z3.MkImplies(t1, t2)
      let zand t1 t2 = z3.MkAnd(t1, t2)
      let lt t1 t2 = z3.MkLt(t1, t2)
      let le t1 t2 = z3.MkLe(t1, t2)
      let zz (i:int) = z3.MkNumeral(i, z3.MkIntType())
      
      let seq_emptyD = z3.MkFuncDecl("nil",[||],seq_type)
      let seq_singletonD = z3.MkFuncDecl("seq_singleton",[| int_type |],seq_type)
      let seq_appendD = z3.MkFuncDecl("app",[|seq_type;seq_type|],seq_type)
      let seq_lengthD = z3.MkFuncDecl("seq_length",[| seq_type |], int_type)
      let seq_indexD = z3.MkFuncDecl("seq_index",[| seq_type; int_type|], int_type)
      let seq_takeD = z3.MkFuncDecl("seq_take",[| seq_type; int_type|], seq_type)
      let seq_dropD = z3.MkFuncDecl("seq_drop",[| seq_type; int_type|], seq_type)
      let seq_consD = z3.MkFuncDecl("cons",[| int_type; seq_type|], seq_type)
      let seq_eqD = z3.MkFuncDecl("seq_eq", [| seq_type; seq_type |], bool_type)
      let p2i4D = z3.MkFuncDecl("$ptr_to_i4",[| int_type|], int_type)
     
      let seq_empty = z3.MkApp(seq_emptyD,[||])
      let seq_singleton (t:TermAst) = z3.MkApp (seq_singletonD, t)
      let seq_append t1 t2 = z3.MkApp (seq_appendD, t1, t2)
      let seq_cons t1 t2 = z3.MkApp (seq_consD, t1, t2)
      let seq_length (t:TermAst)= z3.MkApp (seq_lengthD, t)
      let seq_index t1 t2 = z3.MkApp (seq_indexD, t1, t2)
      let seq_take t1 t2 = z3.MkApp (seq_takeD, t1, t2)
      let seq_drop t1 t2 = z3.MkApp (seq_dropD, t1, t2)
      let seq_eq t1 t2 = z3.MkApp (seq_eqD, t1, t2)
      let p2i4 (t1 :TermAst) = z3.MkApp (p2i4D, t1)
      
      let s0 = z3.MkBound(0ul, seq_type)
      let s1 = z3.MkBound(1ul, seq_type)
      let s2 = z3.MkBound(2ul, seq_type)
      let i0 = z3.MkBound(0ul, int_type)
      let i1 = z3.MkBound(1ul, int_type)
      let i2 = z3.MkBound(2ul, int_type)
      
      let axiom_p2i4 =
        z3.MkForall(0ul,[||],[|int_type|],[|z3.MkSymbol("i0")|],equals (p2i4 i0) i0)
      z3.AssertCnstr axiom_p2i4
      
      let axiom_length_of_empty = 
        equals (seq_length seq_empty) (zz 0)
      z3.AssertCnstr (axiom_length_of_empty)
     
      let length_always_positive = 
        le (zz 0) (seq_length s0)
      z3.AssertCnstr (z3.MkForall(0ul,[||],[|seq_type|],[|z3.MkSymbol("s0")|],length_always_positive))
      
      let length_of_singleton = 
        equals (seq_length (seq_singleton i0)) (zz 1)   
      let axiom_length_of_singleton = 
        z3.MkForall(0ul,[||],[|int_type|],[|z3.MkSymbol("i0")|],length_of_singleton)
      z3.AssertCnstr (axiom_length_of_singleton)
      
      let length_of_append = 
        equals (seq_length (seq_append s0 s1)) (add (seq_length s0) (seq_length s1))
      let axiom_length_of_append = 
        z3.MkForall(0ul,[||],[|seq_type;seq_type|],[|z3.MkSymbol("s1"); z3.MkSymbol("s0")|],length_of_append)
      z3.AssertCnstr (axiom_length_of_append)
      
      let index_of_singleton =
        equals (seq_index (seq_singleton i0) (zz 0)) i0      
      let axiom_index_of_singleton = 
        z3.MkForall(0ul,[||], [|int_type|],[|z3.MkSymbol("i0")|],index_of_singleton)
      z3.AssertCnstr (axiom_index_of_singleton)

      let index_of_append_left =
        implies (lt i0 (seq_length s1))
                (equals (seq_index (seq_append s1 s2) i0) (seq_index s1 i0))
      let axiom_index_of_append_left = 
        z3.MkForall(0ul,[||],[|seq_type;seq_type;int_type|],
         [|z3.MkSymbol("s2");z3.MkSymbol("s1");z3.MkSymbol("i0")|],index_of_append_left)
      z3.AssertCnstr (axiom_index_of_append_left)
      
      let index_of_append_right =
        implies (le (seq_length s1) i0)
                (equals (seq_index (seq_append s1 s2) i0) (seq_index s1 (sub i0 (seq_length s1))))          
      let axiom_index_of_append_right = 
        z3.MkForall(0ul,[||],[|seq_type;seq_type;int_type|],
                     [|z3.MkSymbol("s2");z3.MkSymbol("s1");z3.MkSymbol("i0")|],index_of_append_right)
      z3.AssertCnstr (axiom_index_of_append_right)
      
      let seq_length_of_seq_take_within =
        implies (le (zz 0) i0) (implies (le i0 (seq_length s1)) (equals (seq_length (seq_take s1 i0)) i0))
      z3.AssertCnstr(z3.MkForall(0ul,[||], [|seq_type;int_type|],[|z3.MkSymbol("s1"); z3.MkSymbol("i0")|],seq_length_of_seq_take_within))
      
      let seq_length_of_seq_take_out_of_bounds =
        implies (le (zz 0) i0) (implies (lt (seq_length s1) i0) (equals (seq_length (seq_take s1 i0)) (seq_length s1)))
      z3.AssertCnstr(z3.MkForall(0ul,[||], [|seq_type;int_type|],[|z3.MkSymbol("s1"); z3.MkSymbol("i0")|],seq_length_of_seq_take_out_of_bounds))
        
      let seq_index_of_seq_take_within =
        implies (zand (zand (le (zz 0) i2) (lt i2 i1))(lt i2 (seq_length s0))) 
          (equals (seq_index (seq_take s0 i1) i2) (seq_index s0 i2))
      z3.AssertCnstr(
        z3.MkForall(0ul,[||],[|int_type;int_type;seq_type|],
                     [|z3.MkSymbol("i2");z3.MkSymbol("i1");z3.MkSymbol("s0")|],seq_index_of_seq_take_within))

      let seq_eq_equals = 
        implies (seq_eq s0 s1) (equals s0 s1)
      let axiom_seq_eq_equals = 
        z3.MkForall(0ul,[||],[|seq_type;seq_type|],[|z3.MkSymbol("s0"); z3.MkSymbol("s1")|],seq_eq_equals)
      z3.AssertCnstr (axiom_seq_eq_equals)

      let f = implies (zand (le (zz 0) i0) (lt i0 (seq_length s1)))
                      (equals (seq_index s1 i0) (seq_index s2 i0))
      let seq_index_equal =
        implies (zand (equals (seq_length s0) (seq_length s1))
                      (z3.MkForall 
                        (0ul,[||],[|int_type|],[|z3.MkSymbol("i0")|],f)))
                (equals s0 s1)
      let axiom_seq_index_equal =           
        z3.MkForall(0ul,[||],[|seq_type;seq_type|],
                     [|z3.MkSymbol("s0"); z3.MkSymbol("s1")|],                    
                      seq_index_equal)
      z3.AssertCnstr(axiom_seq_index_equal)
(*      
      let a7 = z3.MkBound(7ul, int_type)
      let a4 = z3.MkBound(4ul, int_type)
      let b6 = z3.MkBound(6ul, seq_type)
      let b3 = z3.MkBound(3ul, seq_type)
      let c5 = z3.MkBound(5ul, int_type)
      let c2 = z3.MkBound(2ul, int_type)
      let d4 = z3.MkBound(4ul, seq_type)
      let d1 = z3.MkBound(1ul, seq_type)
      let e3 = z3.MkBound(3ul, seq_type)
      let e0 = z3.MkBound(0ul, seq_type)
      let X = z3.MkBound(2ul, int_type)
      let Y = z3.MkBound(1ul, seq_type)
      let Z = z3.MkBound(0ul, seq_type)

      let ant = 
        (zand (seq_eq (seq_append e0 (seq_cons a4 seq_empty)) d1) 
              (seq_eq (seq_append b3 seq_empty) (seq_cons c2 e0)))
      let con = 
        (zand (seq_eq (seq_append b6 seq_empty) (seq_cons X Y)) 
              (seq_eq (seq_append Y (seq_cons a7 seq_empty)) Z))
      let impl = 
        implies ant 
                (z3.MkExists (0ul, [||], [|int_type;seq_type;seq_type|], 
                    [|z3.MkSymbol("X");z3.MkSymbol("Y");z3.MkSymbol("Z")|], con))
      let to_prove =           
        z3.MkForall(0ul,[||],[|int_type;seq_type;int_type;seq_type;seq_type|],
           [|z3.MkSymbol("a");z3.MkSymbol("b");z3.MkSymbol("c");z3.MkSymbol("d");z3.MkSymbol("e")|], impl)

      printf "ant: %s\n" (z3.ToString(ant))
      printf "con: %s\n" (z3.ToString(con))
      printf "toProve: %s\n" (z3.ToString(impl))
      printf "theorem_test: %s\n" (z3.ToString(to_prove))
      let b = prove z3 to_prove
      printf("prove: is %s\n") (b.ToString())
*)     
(*
axiom (forall (seq s0; seq s1; { seq_equal(s0,s1) }
    seq_length(s0) == seq_length(s1) &&
     forall (int j; { dont_instantiate_int(j) }
        0 <= j && j < seq_length(s0) ==> seq_index(s0,j) == seq_index(s1,j))
  ==> seq_equal(s0,s1)
*)

     
      let derived_cons =
        (equals (seq_cons i1 s0) (seq_append (seq_singleton i1) s0))
      let axiom_derived_cons = 
        z3.MkForall(0ul,[||], [|int_type;seq_type|],[|z3.MkSymbol("i1"); z3.MkSymbol("s0")|],derived_cons)
      z3.AssertCnstr (axiom_derived_cons)
      
      //let b = prove z3 (equals (seq_length (seq_cons (zz 99) seq_empty)) (zz 1))
      //printf("prove: is %s\n") (b.ToString())
      
      (*let b = 
        prove z3 
         (equals (seq_singleton (z3.MkConst("a",(z3.MkIntType())))) 
                          (seq_cons (z3.MkConst("a",(z3.MkIntType()))) seq_empty))
      printf("Result %s\n\n") (b.ToString())
      
      let b = 
        prove z3 
         (implies (equals (seq_cons (z3.MkConst("a",(z3.MkIntType()))) seq_empty) 
                          (seq_cons (z3.MkConst("b",(z3.MkIntType()))) seq_empty)) 
                  (equals (z3.MkConst ("b",(z3.MkIntType()))) 
                          (z3.MkConst("a",(z3.MkIntType())))))
      printf("Result %s\n\n") (b.ToString())
      
      let b = 
        prove z3 
         (implies (equals (seq_singleton (z3.MkConst("a",(z3.MkIntType())))) 
                          (seq_singleton (z3.MkConst("b",(z3.MkIntType()))))) 
                  (equals (z3.MkConst ("b",(z3.MkIntType()))) 
                          (z3.MkConst("a",(z3.MkIntType())))))
      printf("Result %s\n\n") (b.ToString())
      *)
      (*
      let b = prove z3 (equals (seq_length (seq_cons (zz 99) seq_empty)) (zz 1))
      printf("prove: seq_length(seq_cons(1,seq_empty)) = 1 %s\n") (b.ToString())
      
       
      let b = prove z3 (equals (seq_length seq_empty) (zz 0))
      printf("prove: seq_length(seq_empty) = 0 is %s\n") (b.ToString())
      
      let b = prove z3 (equals (seq_length (seq_singleton (zz 99))) (zz 1))
      printf("prove: seq_length(seq_singleton(99))=1  is %s\n") (b.ToString())

      let b = prove z3 (equals (seq_length (seq_append (seq_singleton (zz 99)) (seq_singleton (zz 99)))) (zz 2))
      printf("prove: (seq_length (seq_append (seq_singleton (zz 99) (seq_singleton (zz 99))) =2  is %s\n") (b.ToString())

      let b = prove z3 (z3.MkNot(equals (seq_length (seq_singleton (zz 99))) (zz 2)))
      printf("prove: seq_length(seq_singleton(99))!=2  is %s\n") (b.ToString())
   
      let b = prove z3 (equals (seq_length (seq_singleton (zz 99))) (zz 2))
      printf("prove: seq_length(seq_singleton(99))==2  is %s\n") (b.ToString())

      let b = prove z3 (equals (seq_singleton (zz 99)) seq_empty)
      printf("prove: seq_singleton(99)!=seq_empty  is %s\n") (b.ToString())
      *)
      
  module PureProver =
    
    let mutable debug = false
    
    open Microsoft.Z3
    
    module CAST = Microsoft.Research.Vcc2.CAST
    module TypeCoding = Microsoft.Research.Vcc2.TypeCoding
    module L = Microsoft.Research.Vcc2.Logic
    module S = Microsoft.Research.Vcc2.SepProver
    
    //module B = Microsoft.Research.Vcc2.Background 

    // types from external interface
    type out_term = S.out_term
    type out_form = S.out_form

    // Z3 types
(*    
    type TypeAst = System.IntPtr
    type TermAst = System.IntPtr
    type ConstDeclAst = System.IntPtr
    type ConstAst = System.IntPtr
    type Value = System.IntPtr
    type PatternAst = System.IntPtr    
*)

    // Z3 helpers
    //let mutable z3:Context = null;
    let mutable (z3:TypeSafeContext) = null;
   
    let mk_context() =
      if z3 <> null then
        z3.Dispose()
      let p = new Config ()
      p.SetParamValue("MODEL", "true")
      p.SetParamValue("PARTIAL_MODELS", "true");
      // Required to make arithmetic existentials match 
      //p.SetParamValue("FOURIER_MOTZKIN_ELIM", "true");
      //z3 <- new Context(p)
      z3 <- new TypeSafeContext(p)
      //Is this needed?
      z3.EnableArithmetic()
      let success = z3.Log("sep.z3")
      p.Dispose()

    let mk_bound_var (i:int) (t:TypeAst) = 
      z3.MkBound (uint32 i, t)
  
    let mk_var (name:string) (t:TypeAst) = 
      z3.MkConst(name, t)

    let mk_int_var (name:string) = 
      mk_var name (z3.MkIntType())

    let mk_bool_var (name:string) = 
      mk_var name (z3.MkBoolType())

    let mk_bv_var (name:string) (num_bytes:System.UInt32) = 
      mk_var name (z3.MkBvType(num_bytes))

    let mk_int (v:int) = 
      z3.MkNumeral(v, z3.MkIntType())

    let mk_bool (b:bool) = 
      match b with
        | true -> z3.MkTrue()
        | false -> z3.MkFalse()
    
    let mk_bv (b:System.UInt32) (num_bytes:System.UInt32) = 
      z3.MkNumeral(System.String.Format("{0}", b), z3.MkBvType(num_bytes))
    
    let mk_neq (x, y) = z3.MkNot (z3.MkEq (x,y))
    
    //let mk_all (args,types,pred) = z3.MkForall(UInt32.of_int 0,[| |], args,types ,pred)

    //let mk_seq = z3.MkType("seq")
    
    let mk_binary_app (f:ConstDeclAst,x:TermAst,y:TermAst) =
      z3.MkApp(f, x, y)
    let mk_unary_app (f:ConstDeclAst,x:TermAst) =
      z3.MkApp(f, x)

  (*  let addTestBackground() = 
      let int_type = z3.MkIntType()
      let rec seq_type = z3.MkType("seq")
      let seq_empty = z3.MkFreshConst("seq_empty",seq_type)
      let seq_singleton = z3.MkFuncDecl("seq_singleton",[| int_type |],seq_type)
      let seq_append = z3.MkFuncDecl("seq_append",[|seq_type;seq_type|],seq_type)
      let seq_length = z3.MkFuncDecl("seq_length",[| seq_type |], int_type)
      let seq_index = z3.MkFuncDecl("seq_index",[| seq_type; int_type|], int_type)
      
      let s0 = z3.MkBound(0ul, seq_type)
      let s1 = z3.MkBound(1ul, seq_type)
      let i0 = z3.MkBound(0ul, int_type)
      let i1 = z3.MkBound(1ul, int_type)
      
      let length_of_empty = 
        z3.MkEq( mk_unary_app(seq_length, seq_empty), mk_int(0))
      let length_of_singleton = 
        z3.MkEq(mk_unary_app(seq_length, mk_unary_app(seq_singleton, i0)),
                mk_int(1))
      let length_of_append = 
        z3.MkEq(mk_unary_app(seq_length, mk_binary_app(seq_append, s0, s1)), 
                z3.MkAdd(mk_unary_app(seq_length,s0),mk_unary_app(seq_length,s1)))
   *) 
    
    //let assert_inj_axiom 
    
   
      
      
//      (* assert f(x, y) = f(w, v) *)
//      let q          = z3.MkForall(UInt32.of_int 0,[||],[|int_type|],[|"x"|],p)
//      printf("z3:: =  %s") (z3.ToString(q))
//      z3.AssertCnstr(q)
//   
//      let e          = z3.MkApp(f, mk_int(3))
//      let b         = z3.MkEq(e,mk_int(2))
//   
//      printf("prove: f(3) = 2 is %s") (prove(b).ToString())
//      let b         = z3.MkEq(e,mk_int(1))
//      printf("prove: f(3) = 1 is %s") (prove(b).ToString())
//      
      //

    // translation of out terms and out forms
    type Dict<'a, 'b> = System.Collections.Generic.Dictionary<'a, 'b>

    let types = new Dict<CAST.Type, TypeAst>()
    let functions = new Dict<string, ConstDeclAst>()
    let mutable progVarsIndex = -1
    let progVars = new Dict<string, TermAst*TypeAst>()
    let mutable existVarsIndex = -1
    let existVars = new Dict<string, TermAst*TypeAst>()
    // in implies, variables are bound (stored in progVars and existVars)
    // in congruence_closure, variables are free (stored as constants in constVars)
    let constVars = new Dict<string, TermAst*TypeAst>()
    let mutable makeConstVars = false

    let countVariablesTerm (f:out_term) doExistVars doProgVars =
      let existVars = new Dict<string, bool>()
      let progVars = new Dict<string, bool>()
      let rec doTerm (t:out_term) =
        match t with 
          | out_term.Fun(name, ts) -> for t in ts do doTerm t;
          | out_term.PVar s ->
            if doProgVars then
              match progVars.TryGetValue s with
                | (true, _) -> ()
                | _ -> progVars.Add (s, true)
            else ()
          | out_term.EVar s ->
            if doExistVars then
              match existVars.TryGetValue s with
                | (true, _) -> ()
                | _ -> existVars.Add (s, true)
            else ()
          | out_term.String s -> ()
      doTerm f;
      match doExistVars, doProgVars with
        | true, false -> existVars.Count
        | false, true -> progVars.Count
        | true, true -> existVars.Count + progVars.Count
        | false, false -> 0

    let rec countVariablesForm (f:out_form) e p =
      match f with
        | out_form.EQ (t1, t2) -> 
          countVariablesTerm t1 e p + countVariablesTerm t2 e p
        | out_form.NEQ (t1, t2) -> 
          countVariablesTerm t1 e p + countVariablesTerm t2 e p
        | out_form.Pred (name, ts) -> 
          List.fold_left (fun x y -> x + y) 0 
            (List.map (fun t -> countVariablesTerm t e p) ts)
        | out_form.Or (f1, f2) -> 
          countVariablesForm f1 e p + countVariablesForm f2 e p
        | out_form.And (f1, f2) -> 
          countVariablesForm f1 e p + countVariablesForm f2 e p
        | out_form.TT -> 0
        | out_form.FF -> 0

    let countExistVarsTerm (f:out_term) = countVariablesTerm f true false
    let countExistVarsForm (f:out_form) = countVariablesForm f true false
    let countProgVarsTerm (f:out_term) = countVariablesTerm f false true
    let countProgVarsForm (f:out_form) = countVariablesForm f false true

    let initTranslation() =
      types.Clear()
      functions.Clear()
      progVars.Clear()
      progVarsIndex <- 0
      existVars.Clear()
      existVarsIndex <- 0
      constVars.Clear()
      makeConstVars <- false

    let toZ3Type t =
      match t with
        | CAST.Type.Bool -> z3.MkBoolType()
//        | CAST.Type.Bool -> z3.MkIntType()
        | CAST.Type.Integer kind -> z3.MkIntType()
        | CAST.Type.Primitive kind -> z3.MkIntType() // z3.MkRealType() 
        | CAST.Type.Ref s when s.Name = "^seq" -> z3.MkIntType() // z3.MkType("seq")
        | CAST.Type.Void
        | CAST.Type.Ptr _
        | CAST.Type.Ref _
        | CAST.Type.TypeIdT 
        | _ -> z3.MkIntType() // z3.MkType("void")
//        | CAST.Type.Array (tp, sz) -> 
//        | CAST.Type.Map (range, dom) -> 

    let lookupType (t:CAST.Type) =
      match types.TryGetValue t with
        | (true, z3Type) -> z3Type
        | _ -> let z3type = toZ3Type t
               types.Add (t, z3type)
               z3type

    let lookupFunction typeEnc name =
      match functions.TryGetValue name with
        | (true, funDecl) -> funDecl
        | _ -> let (rt, ats) = Option.get (TypeCoding.decodeFunctionType typeEnc)
               let rt = toZ3Type rt
               let ats = List.map toZ3Type ats
               let funDecl = z3.MkFuncDecl(name, List.to_array ats, rt)
               functions.Add (name, funDecl)
               funDecl

    let lookupProgramVar typeEnc name =
      match progVars.TryGetValue name with
        | (true, (varDecl, typ)) -> varDecl
        | _ -> let typ = toZ3Type (Option.get (TypeCoding.decodeVarType typeEnc))
               let varDecl = mk_bound_var progVarsIndex typ
               progVarsIndex <- progVarsIndex + 1
               progVars.Add (name, (varDecl, typ))
               varDecl
    
    let lookupExistentialVar typeEnc name =
      match existVars.TryGetValue name with
        | (true, (varDecl, typ)) -> varDecl
        | _ -> let typ = toZ3Type (Option.get (TypeCoding.decodeVarType typeEnc))
               let varDecl = mk_bound_var existVarsIndex typ
               existVarsIndex <- existVarsIndex + 1
               existVars.Add (name, (varDecl, typ))
               varDecl

    let lookupConstVar typeEnc name =
      match constVars.TryGetValue name with
        | (true, (varDecl, typ)) -> varDecl
        | _ -> let typ = toZ3Type (Option.get (TypeCoding.decodeVarType typeEnc))
               let varDecl = mk_var name typ
               constVars.Add (name, (varDecl, typ))
               varDecl


    // helper functions for dealing with type coding
    let extractVariableTypeAndName (s:string) =
      match TypeCoding.isTypeEncoded s with
        | true ->
          TypeCoding.splitEncodedString s
        | false ->
          ("i4", s) // TODO: what type to assume here?    
    
    let extractFunctionTypeArgs (ts:list<out_term>) =
      match ts with
        | typeEncTerm::argTerms ->
          match typeEncTerm with
            | out_term.String s -> (s, argTerms)
            | _ -> failwith "extractFunctionTypeArgs"
        | _ -> failwith "extractFunctionTypeArgs"

    let extractString (t:out_term) =
      match t with
        | out_term.String s -> s
        | _ -> failwith "extractString"

    let extractVarString (t:out_term) =
      match t with
        | out_term.PVar s 
        | out_term.EVar s -> s
        | _ -> failwith "extractVarString"

    let isFunctionTypeEncoded (t:out_term) =
      match t with
        | out_term.String s -> TypeCoding.isTypeEncoded s
        | _ -> false
    
    let unaryOps = 
      [
         ("!", z3.MkNot); 
      ]

    let binaryOps = 
      [
         ("+", (fun x y -> z3.MkAdd (x,y)));
         ("-", (fun x y -> z3.MkSub (x,y)));
         ("*", (fun x y -> z3.MkMul (x,y)));
         ("/", (fun x y -> z3.MkDiv (x,y)));
         ("%", (fun x y -> z3.MkMod (x,y)));
         ("==", (fun x y -> z3.MkEq (x,y)));
         ("!=", (fun x y -> mk_neq (x,y)));
         (">", (fun x y -> z3.MkGt (x,y)));
         (">=", (fun x y -> z3.MkGe (x,y)));
         ("<", (fun x y -> z3.MkLt (x,y)));
         ("<=", (fun x y -> z3.MkLe (x,y)));
         ("&&", (fun x y -> z3.MkAnd (x,y)));
         ("||", (fun x y -> z3.MkOr (x,y)));
         ("==>", (fun x y -> z3.MkImplies (x,y)));
         ("<==>", (fun x y -> z3.MkIff (x,y)))
      ]

    let lookupSeq_eqD name =
      assert (name = "seq_eq")
      match functions.TryGetValue name with
        | (true, funDecl) -> funDecl
        | _ -> let seq_type = z3.MkIntType() 
               let seq_eqD = z3.MkFuncDecl(name, [| seq_type; seq_type |], z3.MkBoolType())
               functions.Add (name, seq_eqD)
               seq_eqD
    let seq_eq (t1:TermAst) (t2:TermAst) = z3.MkApp (lookupSeq_eqD "seq_eq", t1, t2)
    // some way do decide when to use seq_eq instead of z3.MkEq; might be erroneous
    let eq_fun f1 f2 =
      let match_name s =
        s = "app" || s = "cons" || s = "nil"
      if (match_name f1 && match_name f2) then //seq_eq
        fun x y -> z3.MkEq (x, y)
      else fun x y -> z3.MkEq (x, y)


    // conversion of out terms and out forms
    let rec handle_special_function (name:string) (ts:list<out_term>) = 
      match name with
        | "int" ->
          Some (mk_int(System.Int32.Parse (extractString ts.Head)))
        | "bool" ->
          match extractString ts.Head with
            | "true" -> Some (mk_bool(true))
//            | "true" -> Some (mk_int(1))
            | "false" -> Some (mk_bool(false))
//            | "false" -> Some (mk_int(0))
            | _ -> failwith "handle_special_function"
        | "nil" ->
          let funDecl = lookupFunction "()i4" name
          //let funDecl = lookupFunction "()^seq" name
          Some (z3.MkApp (funDecl, [| |]))
        | "cons"
        | "app" ->
          let funDecl = lookupFunction "(i4,i4)i4" name
          //let funDecl = lookupFunction "(^seq,^seq)^seq" name
          Some (z3.MkApp (funDecl, List.to_array (List.map convert_out_term ts)))
        | "Add"
        | "Loc" ->
          (*let (typeEnc, name) = extractVariableTypeAndName (extractVarString ts.Head)*)
          let funDecl = lookupFunction ("(i4,i4)i4") name
          Some (z3.MkApp (funDecl, List.to_array (List.map convert_out_term ts)))
        | "$is" ->
          Some (mk_bool(true))
        | "$ptr_cast" ->
          Some (convert_out_term ts.Tail.Head)
        | "$bool_to_int" ->
          Some (z3.MkIte(z3.MkEq(convert_out_term ts.Head, mk_bool(true)), mk_int(1), mk_int(0)))
        | "$int_to_bool" | "lift" ->
          Some (z3.MkIte(mk_neq(convert_out_term ts.Head, mk_int(0)), mk_bool(true), mk_bool(false)))
        | "!" ->
          match Util._try_assoc name unaryOps with
              | Some op ->
                let (typeEnc, argTerms) = extractFunctionTypeArgs ts
                Some (op (convert_out_term (argTerms.Head)))
              | None -> printf "unknown unary operation: %s" name;
                        failwith "handle_special_function";    
        | "+"
        | "/"
        | "*"
        | "/"
        | "%"
        | "=="
        | "!="
        | ">"
        | ">="
        | "<"
        | "<="
        | "&&"
        | "||"
        | "==>"
        | "<==>" ->
          match Util._try_assoc name binaryOps with
              | Some op ->
                if isFunctionTypeEncoded ts.Head then
                  let (typeEnc, argTerms) = extractFunctionTypeArgs ts
                  Some (op (convert_out_term (argTerms.Head)) (convert_out_term (argTerms.Tail.Head)))
                else 
                  Some (op (convert_out_term (ts.Head)) (convert_out_term (ts.Tail.Head)))
              | None -> printf "unknown binary operation: %s" name;
                        failwith "handle_special_function"
        | s when s.StartsWith "value_" ->
          let funDecl = lookupFunction "(i4,i4)i4" s
          Some (z3.MkApp (funDecl, List.to_array (List.map convert_out_term ts)))
        | _ -> None
    
    and convert_out_term (term:out_term) =
      match term with 
        | out_term.Fun(name, ts) ->
          match handle_special_function name ts with
            | Some z3Term ->
              match ts with
//                | [out_term.Fun (name1, ts1); out_term.Fun (name2, ts2)] ->
//                  eq_fun name1 name2 (convert_out_term (out_term.Fun (name1, ts1))) (convert_out_term (out_term.Fun (name2, ts2)))
                | _ -> z3Term
            | None ->
              let (typeEnc, argTerms) = extractFunctionTypeArgs ts
              let funDecl = lookupFunction typeEnc name
              let args = List.map convert_out_term argTerms
              z3.MkApp (funDecl, List.to_array args)
        | out_term.PVar s ->
          let (typeEnc, name) = extractVariableTypeAndName s
          if makeConstVars then
            lookupConstVar typeEnc name
          else
            lookupProgramVar typeEnc name 
        | out_term.EVar s ->
          let (typeEnc, name) = extractVariableTypeAndName s
          if makeConstVars then
            lookupConstVar typeEnc name
          else
            lookupExistentialVar typeEnc name 
        | out_term.String s -> z3.MkConst(s,z3.MkIntType())
//          mk_int(Int32.of_string s)
//          match s with 
//            | "0" -> mk_int(0)
//            | "1" -> mk_int(1)
//            | _ -> assert false // TODO
     
    let rec convert_out_form (form:out_form) =
      match form with
        | out_form.EQ (out_term.Fun (name1, ts1), out_term.Fun (name2, ts2)) ->
          eq_fun name1 name2 (convert_out_term (out_term.Fun (name1, ts1))) (convert_out_term (out_term.Fun (name2, ts2)))
        | out_form.NEQ (out_term.Fun (name1, ts1), out_term.Fun (name2, ts2)) ->
          z3.MkNot (eq_fun name1 name2 (convert_out_term (out_term.Fun (name1, ts1))) (convert_out_term (out_term.Fun (name2, ts2))))
        | out_form.EQ (t1, t2) ->
          let a = convert_out_term t1
          let b = convert_out_term t2
          z3.MkEq (a, b)
//          z3.MkEq (convert_out_term t1, convert_out_term t2)
//          seq_eq (convert_out_term t1) (convert_out_term t2)
        | out_form.NEQ (t1, t2) ->
          z3.MkNot (z3.MkEq (convert_out_term t1, convert_out_term t2))
//          z3.MkNot (seq_eq (convert_out_term t1) (convert_out_term t2))
        | out_form.Pred (name, ts) ->
          match handle_special_function name ts with
            | Some z3Term -> 
              match ts with
//                | [out_term.Fun (name1, ts1); out_term.Fun (name2, ts2)] ->
//                  eq_fun name1 name2 (convert_out_term (out_term.Fun (name1, ts1))) (convert_out_term (out_term.Fun (name2, ts2)))
                | _ -> z3Term
            | None ->
              let (typeEnc, argTerms) = extractFunctionTypeArgs ts
              let funDecl = lookupFunction typeEnc name
              let args = List.map convert_out_term argTerms
              z3.MkApp (funDecl, List.to_array args)
        | out_form.Or (f1, f2) ->
          z3.MkOr (convert_out_form f1, convert_out_form f2)
        | out_form.And (f1, f2) ->
          z3.MkAnd (convert_out_form f1, convert_out_form f2)
        | out_form.TT -> mk_bool(true)
//        | out_form.TT -> mk_int(1)
        | out_form.FF -> mk_bool(false)
//        | out_form.FF -> mk_int(0)


    // pretty printer for out terms and out forms
    let rec print_special_function (name:string) (ts:list<out_term>) = 
      match name with
        | "int" ->
          Some (extractString ts.Head)
        | "bool" ->
          Some (extractString ts.Head)
        | "nil" ->
          Some ("nil()")
        | "cons" ->
          Some ("cons(" + print_out_term ts.Head + ", " + (print_out_term ts.Tail.Head) + ")")
        | "app" ->
          Some ("app(" + print_out_term ts.Head + ", " + (print_out_term ts.Tail.Head) + ")")
        | "Add" ->
          Some ("Add(" + print_out_term ts.Head + ", " + (print_out_term ts.Tail.Head) + ")")
        | "Loc" ->
          Some ("Loc(" + print_out_term ts.Head + ", " + (print_out_term ts.Tail.Head) + ")")
        | "$is" ->
          Some ("is(" + print_out_term ts.Head + ", " + (print_out_term ts.Tail.Head) + ")")
        | "$bool_to_int" ->
          Some ("$bool_to_int(" + print_out_term ts.Head + ")")
        | "$int_to_bool" | "lift" ->
          Some ("$int_to_bool(" + print_out_term ts.Head + ")")
        | "!" ->
          let (typeEnc, argTerms) = extractFunctionTypeArgs ts
          Some ("(!" + print_out_term argTerms.Head + ")")
        | "+"
        | "/"
        | "*"
        | "/"
        | "%"
        | "=="
        | "!="
        | ">"
        | ">="
        | "<"
        | "<="
        | "&&"
        | "||"
        | "==>"
        | "<==>" ->
          if isFunctionTypeEncoded ts.Head then
            let (typeEnc, argTerms) = extractFunctionTypeArgs ts
            Some ("(" + print_out_term argTerms.Head + " " + name + " " + print_out_term argTerms.Tail.Head + ")")
          else 
            Some ("(" + print_out_term ts.Head + " " + name + " " + print_out_term ts.Tail.Head + ")")
        | s when s.StartsWith "value_" ->
          Some (s + "(" + (String.concat ", " (List.map print_out_term ts)) + ")")
        | _ -> None

    and print_out_term (term:out_term) =
      match term with 
        | out_term.Fun(name, ts) ->
          match print_special_function name ts with
            | Some s -> s
            | None ->
              let (typeEnc, argTerms) = extractFunctionTypeArgs ts
              let args =
                match List.map print_out_term argTerms with
                  | [] -> ""
                  | [at] ->  at
                  | hd::tl -> hd + (List.fold_left (fun (acc:string) (s:string) -> acc + "," + s) "" tl)
              typeEnc + ":" + name + "(" + args + ")"
        | out_term.PVar s ->
          let (typeEnc, name) = extractVariableTypeAndName s
          "PVar " + typeEnc + ":" + name
        | out_term.EVar s ->
          let (typeEnc, name) = extractVariableTypeAndName s
          "EVar " + typeEnc + ":" + name
        | out_term.String s ->
          s

    let rec print_out_form (form:out_form) n =
      match form with
        | out_form.EQ (t1, t2) ->
          "(" + (print_out_term t1) + " == " + (print_out_term t2) + ")"
        | out_form.NEQ (t1, t2) ->
          "(" + (print_out_term t1) + " != " + (print_out_term t2) + ")"
        | out_form.Pred (name, ts) ->
          match print_special_function name ts with
            | Some s -> s
            | None ->
              let (typeEnc, argTerms) = extractFunctionTypeArgs ts
              let args =
                match List.map print_out_term argTerms with
                  | [] -> ""
                  | [at] ->  at
                  | hd::tl -> hd + (List.fold_left (fun (acc:string) (s:string) -> acc + "," + s) "" tl)
              typeEnc + ":" + name + "(" + args + ")"
        | out_form.Or (f1, f2) ->
          "\n" + System.String(' ', n+1) + "(" +  (print_out_form f1 (n+2)) 
           + "\n" + System.String(' ', n+1) + "||" + (print_out_form f2 (n+2)) + ")\n"
        | out_form.And (f1, f2) ->
           System.String(' ', n) + (print_out_form f1 n) + "\n" +  System.String(' ', n) + "&&" + (print_out_form f2 n)
        | out_form.TT -> "TT"
        | out_form.FF -> "FF"
   
    let pretty_print (x:out_form) (y:out_form) =
      let toPrint = (print_out_form x 0) + "\n==>\n" + (print_out_form y 0)
      printf "%s\n" toPrint


    // function encapsulating external prover calls to Z3
    let implies (x:out_form) (y:out_form) =
      if debug then
        printf "%s" "Running Z3...\n"
        pretty_print x y
      mk_context()
      Background.addTestBackground(z3)
      
      initTranslation()
      progVarsIndex <- countExistVarsForm x + countExistVarsForm y
      let ant = convert_out_form x
      let con = convert_out_form y
(*
      let toProve = 
        z3.MkForall(UInt32.of_int 0, Array.of_seq(progVars.Values), [| |],
          z3.MkExists(UInt32.of_int 0, Array.of_seq(existVars.Values), [| |],
            z3.MkImplies (ant, con)))
*)
      let pVarNames = Array.of_seq (progVars.Keys)
      let pVarTypes =
        let (pVarTermAst, pVarTypes) = List.unzip (List.of_seq (progVars.Values))
        Array.of_list pVarTypes
      let eVarNames = Array.of_seq (existVars.Keys)
      let eVarTypes =
        let (eVarTermAst, eVarTypes) = List.unzip (List.of_seq (existVars.Values))
        Array.of_list eVarTypes

      let toProve = 
        z3.MkNot
         (z3.MkForall(uint32 0, [| |], pVarTypes, pVarNames,
            z3.MkImplies (z3.MkExists(uint32 0, [| |], eVarTypes, eVarNames, ant), 
              z3.MkExists(uint32 0, [| |], eVarTypes, eVarNames, con))))
 
      if debug then
        printf "Prove: %s\n" (z3.ToString toProve)
 
      z3.AssertCnstr (toProve)
      let model = ref null in
      match z3.CheckAndGetModel(model) with
        | LBool.True ->  
          if debug then
            Printf.printf "Z3 says false.\n"; 
          ((!model).Display(System.Console.Out)); (!model).Dispose(); false
        | LBool.False -> 
          if debug then
            Printf.printf "Z3 says true.\n"; 
          true
        | LBool.Undef -> 
          if debug then
            Printf.printf "Unknown result from Z3."; 
          false
        | _ -> failwith "implies"

(*
    // external congruence closure computation using Z3
    let mutable cc_count = 0
    
    let congruence_closure (f:out_form) (ts:list<out_term>) = 
      if debug then
        printf "%s" "Running congruence closure computation...\n"
        printf "Assumptions: %s\n" (print_out_form f 0)
        let terms = 
          match ts with
            | [] -> ""
            | [t] -> print_out_term t
            | hd::tl -> (print_out_term hd) +
                        (List.fold_left
                        (fun acc t -> acc + ", " + (print_out_term t)) "" tl)
        printf "Terms: { %s }\n" terms 
      if cc_count > 0 then 
        List.map (fun t -> [t]) ts
      else 
        cc_count <- cc_count + 1
        let arr = List.to_array ts
        [[arr.[0]]; [arr.[1]]; [arr.[2];arr.[6]]; [arr.[3]]; [arr.[4]]; [arr.[5]]; [arr.[7]]]
*)
(*
      let x = z3.MkBound(0ul, z3.MkIntType())
      let y = z3.MkBound(2ul, z3.MkIntType())
      let toProve = 
        z3.MkIff(
          z3.MkForall(UInt32.of_int 0, [| |], [| z3.MkIntType(); z3.MkIntType() |], 
            [| z3.MkSymbol("x"); z3.MkSymbol("y") |], 
              z3.MkForall(UInt32.of_int 0, [| |], [| z3.MkIntType(); z3.MkIntType() |], 
                [| z3.MkSymbol("a"); z3.MkSymbol("b") |], z3.MkEq(x, y))),
          z3.MkConst("bul", z3.MkBoolType()))
      if debug then
        printf "Prove: %s\n" (z3.ToString toProve)
      z3.AssertCnstr (toProve)
*)
(*
    let congruence_closure (f:out_form) (ts:list<out_term>) = 
      let ts_old = ts
      let ts = List.rev ((out_term.PVar "*i4:temp") :: (List.rev ts).Tail)
    
      if debug then
        printf "%s" "Running congruence closure computation...\n"
        printf "Assumptions: %s\n" (print_out_form f 0)
        let terms = 
          match ts with
            | [] -> ""
            | [t] -> print_out_term t
            | hd::tl -> (print_out_term hd) +
                        (List.fold_left
                        (fun acc t -> acc + ", " + (print_out_term t)) "" tl)
        printf "Terms: { %s }\n" terms

      mk_context()
      initTranslation()
      makeConstVars <- true

      let distinct = ref [| |]

      existVarsIndex <- 0
      progVarsIndex <- countExistVarsForm f
      let assumption = convert_out_form f
      if countExistVarsForm f = 0 && countProgVarsForm f = 0 then
        distinct := Array.append !distinct [|assumption|]

      let terms = 
        List.map (fun t -> existVarsIndex <- 0;
                           progVarsIndex <- countExistVarsTerm t;
                           let tt = convert_out_term t;
                           if countExistVarsTerm t = 0 && countProgVarsTerm t = 0 then
                             distinct := Array.append !distinct [|tt|];
                           tt) ts
      let t =  List.to_array terms

      let pVarNames = Array.of_seq (progVars.Keys) |> Array.rev
      let pVarTypes =
        let (pVarTermAst, pVarTypes) = List.unzip (List.of_seq (progVars.Values))
        Array.of_list pVarTypes |> Array.rev
      let eVarNames = Array.of_seq (existVars.Keys) |> Array.rev
      let eVarTypes =
        let (eVarTermAst, eVarTypes) = List.unzip (List.of_seq (existVars.Values))
        Array.of_list eVarTypes |> Array.rev

      z3.AssertCnstr(z3.MkDistinct(!distinct))
      
      if debug then
        printf "pVarNames: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" pVarNames)
      if debug then
        printf "eVarNames: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" eVarNames)
      if debug then
        printf "assumptions: %s\n" (z3.ToString assumption)
        printf "terms: %s\n" (List.fold_left (fun x y -> x + " " + y) "" (List.map z3.ToString terms))
        printf "t: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" (Array.map z3.ToString t))
        printf "distinct: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" (Array.map z3.ToString !distinct))

      let assumption_a =
        z3.MkForall(UInt32.of_int 0, [| |], pVarTypes, pVarNames,
          z3.MkForall(UInt32.of_int 0, [| |], eVarTypes, eVarNames, assumption))
      if debug then
        printf "Assumptions in prover: %s\n" (z3.ToString assumption_a)
      z3.AssertCnstr(assumption_a)
      
      let bool_type = z3.MkBoolType()
      let bool_true = z3.MkTrue()
      let r = 
        [| for i in 0 .. ts.Length-1 do
             yield [| for j in 0 .. ts.Length-1 do 
                        yield z3.MkConst (("r_" + i.ToString() + "_" + j.ToString()), bool_type) |] |]

      // Initial congruence
      if debug then
        printf "Congruences in prover:\n"       
      for i in 0 .. t.Length-1 do
        for j in 0 .. t.Length-1 do 
          let congruence_a = 
            z3.MkIff(
              z3.MkForall(UInt32.of_int 0, [| |], pVarTypes, pVarNames,
                z3.MkForall(UInt32.of_int 0, [| |], eVarTypes, eVarNames,
                  z3.MkEq(t.[i], t.[j]))),
              z3.MkEq(r.[i].[j], bool_true))
          if debug then
            printf "%s\n" (z3.ToString congruence_a)
          z3.AssertCnstr(congruence_a)              

      // Equivalence relation - reflexivity
      for i in 0 .. ts.Length-1 do
        z3.AssertCnstr(z3.MkEq(r.[i].[i], bool_true))
      // Equivalence relation - symmetry
      for i in 0 .. ts.Length-1 do
        for j in 0 .. ts.Length-1 do 
          z3.AssertCnstr(
            z3.MkImplies(z3.MkEq(r.[i].[j], bool_true),
              z3.MkEq(r.[j].[i], bool_true)))
      // Equivalence relation - transitivity
      for i in 0 .. ts.Length-1 do
        for j in 0 .. ts.Length-1 do 
          for k in 0 .. ts.Length-1 do
            z3.AssertCnstr(
              z3.MkImplies(
                z3.MkAnd(
                  z3.MkEq(r.[i].[j], bool_true), 
                  z3.MkEq(r.[j].[k], bool_true)),
                z3.MkEq(r.[i].[k], bool_true)))

      let model = ref null in
      match z3.CheckAndGetModel(model) with
        | LBool.True ->  
          if debug then
            Printf.printf "Z3 says true.\n"; 
          ((!model).Display(System.Console.Out)); (!model).Dispose()
        | LBool.False -> 
          if debug then
            Printf.printf "Z3 says false.\n"; 
          ((!model).Display(System.Console.Out)); (!model).Dispose()
        | LBool.Undef -> 
          if debug then
            Printf.printf "Unknown result from Z3."; 
        | _ -> assert false
      List.map (fun t -> [t]) ts_old
*)

    let congruence_closure (f:out_form) (ts:list<out_term>) = 
      
      let rec find_consts (fs:array<TermAst>) =
(*
        let equalityComparer =
          { new System.Collections.Generic.IEqualityComparer<TermAst> with
            member x.Equals (x, y) = z3.IsEq (x, y)
            member x.GetHashCode obj = 1
          }
        let consts = new Dict<TermAst, bool>(equalityComparer)
*)
        let consts = new Dict<string, TermAst>()
        let rec do_consts (f:TermAst) =
          match z3.GetAstKind f with
            | AstKind.Const ->
              match z3.GetConstAstArgs f with
                | [| |] ->
                  let name = (z3.GetSymbolString (z3.GetDeclName (z3.GetConstAstDecl f))) 
                  match consts.TryGetValue name with
                    | (true, _) -> ()
                    | _ -> consts.Add (name, f)                
                | fs ->
                  for f in fs do
                    do_consts f 
            | _ -> ()
        for f in fs do
          do_consts f
        List.of_seq (consts.Values)

      let rec find_equal_terms (f:TermAst) =
        match z3.GetAstKind f with
          | AstKind.Const ->
            match z3.GetConstAstArgs f with
              | [| |] -> []
              | a ->
                if (z3.GetSymbolString (z3.GetDeclName (z3.GetConstAstDecl f))) = "=" then
                  [(a.[0], a.[1])]
                else
                  (find_equal_terms (a.[0])) @ (find_equal_terms (a.[1]))
          | _ -> []
      
      let is_member (f:TermAst) (ts:list<TermAst>) =
        match List.tryfind (fun t -> z3.IsEq(f, t)) ts with
          | Some _ -> true
          | None -> false 

      let list_diff (fs:list<TermAst>) (ts:list<TermAst>) =
        List.filter (fun f -> if is_member f ts then false else true) fs

      if debug then
        printf "%s" "Running congruence closure computation...\n"
        printf "Assumptions: %s\n" (print_out_form f 0)
        let terms = 
          match ts with
            | [] -> ""
            | [t] -> print_out_term t
            | hd::tl -> (print_out_term hd) +
                        (List.fold_left
                        (fun acc t -> acc + ", " + (print_out_term t)) "" tl)
        printf "Terms: { %s }\n" terms

      mk_context()
      initTranslation()
      makeConstVars <- true

//      let assumption = convert_out_form f

(*      
      let terms = List.map convert_out_term ts
      let t =  List.to_array terms

      let assumed_equal = find_equal_terms assumption
//      let consts = fst (List.unzip (List.of_seq (constVars.Values)))
      let consts = find_consts t
      let distinct_consts =
        List.to_array (list_diff consts 
          (List.choose (fun (x,y) -> if is_member x consts then Some y else None) assumed_equal))

      if debug then
        printf "assumptions: %s\n" (z3.ToString assumption)
        printf "terms: %s\n" (List.fold_left (fun x y -> x + " " + y) "" (List.map z3.ToString terms))
        printf "t: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" (Array.map z3.ToString t))
        printf "assumed_equal: %s\n" (List.fold_left (fun x y -> x + " " + y) "" (List.map z3.ToString (fst (List.unzip assumed_equal))))
        printf "consts: %s\n" (List.fold_left (fun x y -> x + " " + y) "" (List.map z3.ToString consts))
        printf "distinct_consts: %s\n" (Array.fold_left (fun x y -> x + " " + y) "" (Array.map z3.ToString distinct_consts))
       
//      z3.AssertCnstr(z3.MkDistinct(distinct_consts))

// distinct_consts seems to still allow that function app terms are equal to some of consts

      let distinct_terms =
        List.to_array (list_diff terms 
          (List.choose (fun (x,y) -> if is_member x terms then Some y else None) assumed_equal))
//      z3.AssertCnstr(z3.MkDistinct(distinct_terms))

*)     
//      z3.AssertCnstr(assumption)
//      z3.AssertCnstr(z3.MkNot(z3.MkEq(t.[0],t.[1])))

(*
      let a = mk_int_var "a"
      let b = mk_int_var "b"
      let c = mk_int_var "c"
//      z3.AssertCnstr(z3.MkEq(z3.MkAdd([|a;b|]),mk_int 5))
//      z3.AssertCnstr(z3.MkEq(z3.MkAdd([|c;b|]),mk_int 5))
      z3.AssertCnstr(z3.MkEq(z3.MkAdd([|a;b|]),z3.MkAdd([|c;b|])))
 *)
(*
      let a = mk_int_var "a"
      let b = mk_int_var "b"
      let c = mk_int_var "c"
      let d = mk_int_var "d"
      let f = z3.MkFuncDecl("f", [|z3.MkIntType();z3.MkIntType()|], z3.MkIntType())
      z3.AssertCnstr(z3.MkEq(z3.MkApp(f,a,b),d))
      z3.AssertCnstr(z3.MkEq(z3.MkApp(f,c,b),d))
 *)
(*
      let a = mk_int_var "a"
      let b = mk_int_var "b"
      let c = mk_int_var "c"
      let d = mk_int_var "d"
      let f = z3.MkFuncDecl("f", [|z3.MkIntType()|], z3.MkIntType())
      let g = z3.MkFuncDecl("g", [|z3.MkIntType()|], z3.MkIntType())
 
      z3.AssertCnstr(z3.MkEq(z3.MkApp(f,a),c))
      z3.AssertCnstr(z3.MkEq(z3.MkApp(g,a),d))
      z3.AssertCnstr(z3.MkNot(z3.MkEq(c,d)))
 *)
 (*
      let a = mk_int_var "a"
      let b = mk_int_var "b"
      let d = mk_int_var "d"
      let f = z3.MkFuncDecl("f", [|z3.MkIntType()|], z3.MkIntType())
 
      z3.AssertCnstr(z3.MkEq(b,d))
      z3.AssertCnstr(z3.MkEq(z3.MkApp(f,b),d))
      z3.AssertCnstr(z3.MkEq(z3.MkApp(f,d),a))
 *)
      let a = mk_int_var "a"
      let l = z3.MkAdd([|a;z3.MkMul([|mk_int 2;mk_int 4|])|])
      let r = z3.MkAdd([|mk_int 8;a|])
      
      let t = [|a;l;r|]
      
      let bool_type = z3.MkBoolType()
      let bool_true = z3.MkTrue()
      let r = 
        [| for i in 0 .. ts.Length-1 do
             yield [| for j in 0 .. ts.Length-1 do 
                        yield z3.MkConst (("r_" + i.ToString() + "_" + j.ToString()), bool_type) |] |]

      for i in 0 .. t.Length-1 do
        for j in 0 .. t.Length-1 do 
          let congruence_a = 
            z3.MkIff(z3.MkEq(t.[i], t.[j]),z3.MkEq(r.[i].[j], bool_true))
          z3.AssertCnstr(congruence_a)   

      let model = ref null in
      match z3.CheckAndGetModel(model) with
        | LBool.True ->  
          if debug then
            Printf.printf "Z3 says true.\n"
          ((!model).Display(System.Console.Out))
(*          
          for i in 0 .. t.Length-1 do
            for j in 0 .. t.Length-1 do 
              printf "%b " ((!model).IsEq((!model).Eval(t.[i]),(!model).Eval(t.[j])))
            printf "\n"
          for i in 0 .. t.Length-1 do
            printf "%s \n" ((!model).ToString((!model).Eval(t.[i])))
*)          
          let model_constants = (!model).GetModelConstants()
          for i in 0 .. model_constants.Length-1 do
            printf "%s \n" (model_constants.[i].ToString())

//          let evala = (!model).Eval(a)
//          if not (evala.IsNull()) then printf "%s \n" ((!model).ToString(evala))
 
          (!model).Dispose()
        | LBool.False -> 
          if debug then
            Printf.printf "Z3 says false.\n"; 
        | LBool.Undef -> 
          if debug then
            Printf.printf "Unknown result from Z3."; 
        | _ -> assert false
      
      List.map (fun t -> [t]) ts
