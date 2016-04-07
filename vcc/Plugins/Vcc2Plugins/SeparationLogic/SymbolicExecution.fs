//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
  //open Microsoft.Research.Vcc2
 
  module CAST = Microsoft.Research.Vcc2.CAST
  module Transformers = Microsoft.Research.Vcc2.Transformers
  module CoreC = Microsoft.Research.Vcc2.CoreCAST  
  module CAST2CoreCAST = Microsoft.Research.Vcc2.CAST2CoreCAST
  module TypeCoding = Microsoft.Research.Vcc2.TypeCoding
  module PureProver = Microsoft.Research.Vcc2.PureProver
  module L = Microsoft.Research.Vcc2.Logic
  module S = Microsoft.Research.Vcc2.SepProver
  
  module SymbolicExecution =
   
    let encodeTypes = TypeCoding.encodeTypes
    let encodeVarType = TypeCoding.encodeVarType
    let encodeFunctionType = TypeCoding.encodeFunctionType
    
    type Env =
      {
        Pre : S.form;
        Post: S.form;
      }
    
    let spAssert cond =
      if cond then ()
      else assert false
    
    let oops msg =
      printf "%s\n" msg
      assert false

    // variables
    let spProgVar (t:CAST.Type) (name:string) = S.prog_var (encodeVarType t + name)
    let spCProgVar (v:CAST.Variable) = spProgVar v.Type v.Name
    let spExistsVar (t:CAST.Type) (name:string) = S.exists_var (encodeVarType t + name)
    let spFreshExistsVar (t:CAST.Type) = S.fresh_exists_var_str (encodeVarType t)
    let spFreshProgVar (t:CAST.Type) = S.fresh_prog_var_str (encodeVarType t) 
    let spResult t = spProgVar t "result"
    
    // var to term
    let spMkVar = S.mkVar
     
    // terms
    let spFun (rt:CAST.Type) (fname:string) (ats:list<CAST.Type>) (args:list<S.term>) =
      S.mkFun fname ((S.mkString (encodeFunctionType (rt, ats))) :: args)
    let spFunNoEncoding (fname:string) (args:list<S.term>) =
      S.mkFun fname args
    let spTrue_t = spFunNoEncoding "bool" [S.mkString "true"]
    let spFalse_t = spFunNoEncoding "bool" [S.mkString "false"]
    let spBool (v:bool) =
      match v with
        | true -> spTrue_t
        | false -> spFalse_t
    let spNot a = spFun CAST.Type.Bool "!" [CAST.Type.Bool] [a]
    let spInt (n:bigint) = spFunNoEncoding "int" [S.mkString (n.ToString())]
    let spString s = S.mkString s
    //let spIndex a b = ??
    
    let getType (v:CAST.Variable) (fs:CAST.Field list) =
      match fs with
        | [] -> 
          match v.Type with
            | CAST.Type.Ptr t -> t
            | _ -> failwith "getType"
        | _ -> (List.rev fs).Head.Type
    
    let spFieldLoc (v:CAST.Variable) (fs:CAST.Field list) = 
      L.spLoc2 ((spMkVar << spCProgVar) v) (L.spList (List.map L.field_name fs))

    let spField (v:CAST.Variable) (fs:CAST.Field list) =
      L.spType (getType v fs) (spFieldLoc v fs)

    let spBlobT kind loc value = 
      S.mkFun "blob" [kind; loc; value]

    // lift term to form
    let spLiftTerm = L.spLift
    
    // forms
    let spTrue_f = S.mkEmpty //??
    let spFalse_f = S.mkFalse
    let spEmpty = S.mkEmpty    
    let spEq a b = S.mkEQ (a,b)
    let spNeq a b = S.mkNEQ (a,b)    
    let spPPred s l = S.mkPPred (s, l)
    let spSPred s l = S.mkSPred (s, l)
    
    let mutable currentLogic = L.default_logic()
    let mutable spFrame = S.frame (currentLogic)
    let mutable spImplies = S.implies (currentLogic)


    let rec toTypeTerm t =
      match t with
        | CAST.Type.Void -> S.mkString "^^void"
        | CAST.Type.Integer kind -> S.mkString ("^^" + CAST.Type.IntSuffix kind)
        | CAST.Type.Primitive kind -> S.mkString ("^^" + CAST.Type.PrimSuffix kind) 
        | CAST.Type.Bool -> S.mkString "^^bool"
        | CAST.Type.Ptr tp -> S.mkFun "$ptr_to" [toTypeTerm tp] 
        | CAST.Type.Ref { Name = n; Kind = (CAST.MathType|CAST.FunctDecl _) } -> S.mkString ("^$#" + n)
        | CAST.Type.Ref td -> S.mkString ("^" + td.Name)
        | CAST.Type.Array (tp, sz) -> S.mkFun "$ptr_to" [toTypeTerm tp]
        | CAST.Type.TypeIdT -> S.mkString "^$#typeid_t"
        | CAST.Type.Claim -> S.mkString "^$#claim_t"
        | CAST.Type.Map (range, dom) -> S.mkFun "$map_t" [toTypeTerm range; toTypeTerm dom]
        | CAST.Type.ObjectT -> S.mkString "^$#object_t"

    let toPtrTypeTerm (expr:CoreC.Expr) =
      match expr.Type with
        | CAST.Ptr CAST.Void -> failwith ("void* not supported " + expr.ToString())
        | CAST.Ptr t -> toTypeTerm t
        | _ -> failwith ("pointer type expected " + expr.ToString())

    
    // get rid of existential quantifiers in expr
    let stripExistentials (e:CoreC.Expr) = 
      let aux self e =
        match e with
          | CoreC.Quant (ec, q) ->
            match q.Kind with
              | CAST.Exists ->
                match q.Condition with
                  | Some cond ->
                    (* Not Sure what this was meant to do, but it seems to cause problems *)
                    (*Some (CoreC.Expr.Prim(ec, CAST.Op("&&", CAST.CheckedStatus.Processed), 
                           [self cond; self q.Body])) *)
                        Some (self q.Body)     
                  | None ->
                    Some (self q.Body)
              | _ -> None
          | _ -> None
      e.SelfMap aux

    // find expression that result should be equal to
    let rec findResultExpr (e:CoreC.Expr) =
      match e with
        | CoreC.Expr.Prim (_, CAST.Op("==", _), [lhs; rhs]) ->
          match lhs with
            | CoreC.Expr.Result _ -> Some rhs
            | _ -> None
        | CoreC.Expr.Prim (_, CAST.Op("&&", _), [lhs; rhs]) ->
          match findResultExpr lhs, findResultExpr rhs with
            | Some l, None -> Some l
            | None, Some r -> Some r
            | Some _, Some _
            | None, None -> None
        | _ -> None
    
    // remove existential quantifiers in expr
    let removeResultExpr (e:CoreC.Expr) = 
      let aux self e =
        match e with
          | CoreC.Expr.Prim (ec, CAST.Op("==", _), [CoreC.Expr.Result _; _]) ->
            Some (CoreC.Expr.BoolLiteral (ec, true))
          | CoreC.Expr.Prim (ec, CAST.Op("==", _), [_; CoreC.Expr.Result _]) ->
            Some (CoreC.Expr.BoolLiteral (ec, true))
          | _ -> None
      e.SelfMap aux


    let rec evalExpr (env:Env) expr : S.term =
      let self = evalExpr env
      let selfs = List.map self
      let toTypes = List.map (fun (e:CoreC.Expr) -> e.Common.Type)
      let genericPtrType = CAST.Type.Ptr (CAST.Type.Integer CAST.IntKind.UInt8)
      
      match expr with
        | CoreC.Expr.Ref (_, v) ->
          match v.Kind with
            | CAST.VarKind.ConstGlobal -> (spMkVar (spProgVar v.Type ("g." + v.Name)))
            | CAST.VarKind.Global -> (spMkVar (spProgVar v.Type ("g." + v.Name)))
            | CAST.VarKind.QuantBound -> (spMkVar (spExistsVar v.Type v.Name))
            | _ -> (spMkVar << spCProgVar) v

        | CoreC.Expr.Prim (_, CAST.Op(opName, _), args) ->
          let ats = toTypes args
          let args = selfs args
          //spFunNoEncoding opName args
          spFun expr.Common.Type opName ats args

        | CoreC.Expr.IntLiteral (_, n) -> spInt n
        | CoreC.Expr.BoolLiteral (_, b) -> spBool b
        | CoreC.StringLiteral (_, s) -> spString s

        | CoreC.Expr.Cast ({ Type = CAST.Type.Integer k }, _, e') ->
          match e' with
            | CoreC.Expr.Result _ ->  
              //self e'
              L.sp_b2i (self e')
            | _ ->
              match e'.Type with
                | CAST.Type.Bool ->
                  L.sp_b2i (self e')
                | CAST.Type.Integer _ -> self e'
                | CAST.Type.Ptr _ ->
                  spFun (CAST.Type.Integer k) ("$ptr_to_" + CAST.Type.IntSuffix k) 
                    [e'.Common.Type] [self e']
                | _ -> failwith "evalExpr CoreC.Expr.Cast ({ Type = CAST.Type.Integer k }, _, e') match"
        
        | CoreC.Expr.Cast ({ Type = CAST.Type.Bool }, _, e') ->
          match e'.Type with
            | CAST.Type.Integer _ ->
              match e' with
                | CoreC.IntLiteral (_, Util.ZeroBigInt) -> spFalse_t
                | CoreC.IntLiteral (_, Util.OneBigInt) -> spTrue_t
                | _ -> L.sp_i2b (self e')
            | CAST.Type.Ptr _ ->
              spFun CAST.Type.Bool "$ptr_neq" 
                [e'.Common.Type; e'.Common.Type] [self e'; spInt (Math.BigInt 0)]
            | _ -> failwith "evalExpr CoreC.Expr.Cast ({ Type = CAST.Type.Bool }, _, e') match"
        
        | CoreC.Expr.Cast (_, _, e') when expr.Type.IsPtr && e'.Type.IsPtr ->
          spFun expr.Common.Type "$ptr_cast" 
            [e'.Common.Type; expr.Common.Type] [self e'; toPtrTypeTerm expr]
        
        | CoreC.Expr.Result _ -> spMkVar (spResult expr.Common.Type)

        | CoreC.AddressOfField (_, v, fs) -> spFieldLoc v fs

        | CoreC.Call (_, fn, args) when fn.IsSpec ->
          spFunNoEncoding fn.Name (selfs args)

        | CoreC.Call (_, fn, args) when fn.Name.StartsWith "value" ->
          spFunNoEncoding fn.Name (selfs args)

        | CoreC.Call (_, fn, args) when fn.Name = "blob" ->
          match args with
            | [kind; loc; value] -> spBlobT (self kind) (self loc) (self value)
            | _ -> printf "%s" "blob has three parameters (kind, loc, value)"; 
                   failwith "evalExpr CoreC.Call (_, fn, args) when fn.Name = \"blob\" match"

        | CoreC.Call (_, fn, args) when fn.Name = "seq_cons" ->
          match args with
            | [elem; rest] -> L.spCons (self elem) (self rest)
            | _ -> printf "%s" "seq_cons has two parameters (elem, rest)";
                   failwith "evalExpr CoreC.Call (_, fn, args) when fn.Name = \"seq_cons\" match"

        | CoreC.Call (_, fn, args) when fn.Name = "seq_append" ->
          match args with
            | [l1; l2] -> L.spApp (self l1) (self l2)
            | _ -> printf "%s" "seq_append has two parameters (l1, l2)"; 
                   failwith "evalExpr CoreC.Call (_, fn, args) when fn.Name = \"seq_append\" match"

        | CoreC.Call (_, fn, args) when fn.Name = "seq_empty" ->
          match args with
            | [] -> L.spNil
            | _ -> printf "%s" "seq_empty has no parameters";
                   failwith "evalExpr CoreC.Call (_, fn, args) when fn.Name = \"seq_empty\" match"

        | CoreC.Call (_, fn, args) -> //assert false // other calls should be handled as stmts
          spFunNoEncoding fn.Name (selfs args) // !!!
        
        | CoreC.FieldRead (_, v, fs) -> failwith "evalExpr CoreC.FieldRead" // should already be handled before
        | CoreC.Quant (_, q) -> failwith "evalExpr Quant" // we strip existentials; TODO universals
//        | CoreC.Index (_, arr, idx) -> assert false // TODO

        | _ ->         
          printf "unhandled expr %s\n" (expr.ToString())
          failwith "evalExpr match"


    type Heap = S.rform
    type PC = int

    let contractsToForm env es = 
      List.fold_left S.mkStar spEmpty (List.map (spLiftTerm << (evalExpr env) << stripExistentials) es)

    let rec evalStmt (env : Env) (Hs : (Heap * PC) list) (stmts : array<CoreC.Stmt>) =
      let findGotoPC label =
        let isLabel s =
          match s with
            | CoreC.Goto (_, label) -> true
            | _ -> false
        Array.find_index isLabel stmts
      
      let hs = ref Hs
      while (!hs <> []) do
        //let ((h,pc)::rs) = !hs
        let (h,pc) = (!hs).Head
        let rs = (!hs).Tail
        
        // quick fix; normalize end statements later
        if pc >= stmts.Length then
          hs := rs
        else 
          match stmts.[pc] with
            | CoreC.Stmt.Assert (_, e) -> 
              let f = S.form_clone h
              let fs = spFrame h (spLiftTerm (evalExpr env e))
              spAssert (fs <> [])
              hs := (f,pc+1):: rs

            | CoreC.Stmt.Assume (_, e) -> 
              hs := (S.conjoin (spLiftTerm (evalExpr env e)) h, pc+1) :: rs

            | CoreC.Stmt.Return (c, s) ->
              match s with
              | (Some e) -> S.update_var_to (spResult e.Type) (evalExpr env e) h
              | None -> ()
              spAssert (spImplies h (S.convert env.Post))
              hs := rs
                
            // v := &((*w).f1.f2);
            | CoreC.Stmt.VarWrite (_, v, CoreC.Expr.AddressOfField (_, w, fs)) ->
              S.update_var_to (spCProgVar v) (spFieldLoc w fs) h
              hs := (h,pc+1)::rs
   
            // v := ((*w).f1.f2);
            | CoreC.Stmt.VarWrite (_, v, CoreC.Expr.FieldRead (_, w, fs)) ->
              let newVar = spFreshExistsVar (getType v fs)
              let newVarT = spMkVar newVar
              let thatField = spField w fs
              let fs = spFrame h (thatField newVarT)
              spAssert (fs <> [])
              hs := rs
              for f in fs do
                let f1 = S.conjoin (thatField newVarT) f //fs.Head ??
                S.update_var_to (spCProgVar v) newVarT f1
                S.kill_var newVar f1
                hs := (f1,pc+1) :: !hs
            
            // v := &(e1[e2]);
            | CoreC.Stmt.VarWrite (_, v, CoreC.Expr.AddressOfArrElem (_, e1, e2)) ->
              let elemType =
                match e1.Type with
                  | CAST.Type.Ptr t -> t
                  | _ -> failwith "evalStmt CoreC.Stmt.VarWrite (_, v, CoreC.Expr.AddressOfArrElem (_, e1, e2)) match e1.Type"
              let index =
                match e2 with
                  | CoreC.Expr.IntLiteral (_, i) -> bigint.ToInt32 i
                  | _ -> failwith "evalStmt CoreC.Stmt.VarWrite (_, v, CoreC.Expr.AddressOfArrElem (_, e1, e2)) match e2"
              S.update_var_to (spCProgVar v) (L.spArrElemLoc (evalExpr env e1) elemType index) h
              hs := (h,pc+1)::rs
            
            // v := e;
            | CoreC.Stmt.VarWrite (_, v, e) ->
              S.update_var_to (spCProgVar v) (evalExpr env e) h
              hs := (h,pc+1)::rs
           
            // kill v;
            | CoreC.Stmt.VarKill (_, v) ->
              S.kill_var (spCProgVar v) h
              hs := (h,pc+1)::rs

            // ((*w).f1.f2) := e;
            | CoreC.Stmt.FieldWrite (_, v, fs, e) ->
              let newVar = spFreshExistsVar (getType v fs)
              let newVarT = spMkVar newVar
              let thatField = spField v fs
              let fs = spFrame h (thatField newVarT)
              spAssert (fs <> [])
              hs := rs
              for f in fs do
                let f1 = S.conjoin (thatField (evalExpr env e)) f
                S.kill_var newVar f1
                hs := (f1,pc+1) :: !hs              

            // e1[e2] := e;
            | CoreC.Stmt.ArrElemWrite (_, e1, e2, e) ->
              let elemType =
                match e1.Type with
                  | CAST.Type.Ptr t -> t
                  | _ -> failwith "evalStmt CoreC.Stmt.ArrElemWrite match e1.Type"
              let index =
                match e2 with
                  | CoreC.Expr.IntLiteral (_, i) -> bigint.ToInt32 i
                  | _ -> failwith "evalStmt CoreC.Stmt.ArrElemWrite match e2"
              let newVar = spFreshExistsVar elemType
              let newVarT = spMkVar newVar
              let thatElem = L.spBlob (S.mkString (elemType.ToString())) (L.spArrElemLoc (evalExpr env e1) elemType index)
              let fs = spFrame h (thatElem newVarT)
              spAssert (fs <> [])
              hs := rs
              for f in fs do
                let f1 = S.conjoin (thatElem (evalExpr env e)) f
                S.kill_var newVar f1
                hs := (f1,pc+1) :: !hs   

            | CoreC.Stmt.FunCall(_, v, fn, args) ->
              let pre = contractsToForm env fn.Requires
              let formals = fn.Parameters
              let formals = fn.Parameters
              let fvars = List.fold_right (spCProgVar >> S.vs_add) fn.Parameters (S.vs_add (spResult fn.RetType) S.vs_empty) in
              let lvars = (S.vs_diff (S.fv_form pre) fvars)
              let mutable subst = S.empty_subst
              for (v,e) in (List.zip formals args) do
                subst <- S.add_subst (spCProgVar v) (evalExpr env e) subst                
              subst <- S.add_subst (spResult fn.RetType) (S.mkVar (spResult fn.RetType)) subst 
              // Make logical variables fresh to avoid capture
              let subst2 = S.subst_kill_vars_to_fresh_exist lvars
              let pre = S.subst_form subst2 (S.subst_form subst pre)
              let fs = spFrame h pre
              spAssert (fs <> [])
              hs := rs
              let post = contractsToForm env fn.Ensures in
              //substitution makes exists in post, that aren't already handled into prog variables.
              let evars = S.vs_diff (S.vs_diff (S.fv_form post) fvars) lvars in 
              let subst3 = S.subst_kill_vars_to_fresh_prog evars
              let post = S.subst_form subst3 (S.subst_form subst2 (S.subst_form subst post)) in 
              for f in fs do
                let f = S.conjoin post f in  
                S.update_var_to (spCProgVar v) (S.mkVar (spResult fn.RetType)) f
                S.kill_var (spResult fn.RetType) f
                hs := (f, pc+1) :: !hs

            | CoreC.Stmt.ProcCall(c, fn, args) ->
              let pre = contractsToForm env fn.Requires
              let formals = fn.Parameters
              let fvars = List.fold_right (spCProgVar >> S.vs_add) fn.Parameters S.vs_empty in
              let lvars = (S.vs_diff (S.fv_form pre) fvars)
              let mutable subst = S.empty_subst
              for (v,e) in (List.zip formals args) do
                subst <- S.add_subst (spCProgVar v) (evalExpr env e) subst
              subst <- S.add_subst (spResult fn.RetType) (S.mkVar (spResult fn.RetType)) subst 
              let subst2 = S.subst_kill_vars_to_fresh_exist lvars
              let pre = S.subst_form subst2 (S.subst_form subst pre)
              printf "%s\n" "---"
              printf "%s\n" (S.string_form pre)
              printf "%s\n" "---"
              let fs = spFrame h pre
              spAssert (fs <> [])
              hs := rs
              let post = contractsToForm env fn.Ensures in
              //substitution makes exists in post, that aren't already handled into prog variables.
              let evars = S.vs_diff (S.vs_diff (S.fv_form post) fvars) lvars in 
              let subst3 = S.subst_kill_vars_to_fresh_prog evars
              let post = S.subst_form subst3 (S.subst_form subst2 (S.subst_form subst post)) in 
              for f in fs do
                hs := (S.conjoin post f, pc+1) :: !hs

            | CoreC.Stmt.If (_, c, CoreC.Stmt.Goto(_, l1), CoreC.Stmt.Goto(_, l2)) ->
              let f = S.form_clone h
              let h1 = S.conjoin (spLiftTerm(evalExpr env c)) h
              let h2 = S.conjoin (spLiftTerm(spNot (evalExpr env c))) f
              hs := (h1, findGotoPC l1) :: (h2, findGotoPC l2) :: rs

            | CoreC.Stmt.VarDecl (_, v) ->
              match v.Type with
                | CAST.Type.Integer k -> 
                  hs := (S.conjoin (spPPred ("$in_range_" + (CAST.Type.IntSuffix k))
                          ((S.mkString "(i4)bool") :: [((spMkVar << spCProgVar) v)])) h, pc+1) :: rs
                | CAST.Type.Ptr t ->
                  hs := (S.conjoin (spPPred "$is" 
                          [((spMkVar << spCProgVar) v); toTypeTerm t]) h, pc+1) :: rs
                | _ ->
                  hs := (h, pc+1) :: rs
                    
            | CoreC.Stmt.Goto (c, l) -> 
                hs := (h, findGotoPC l) :: rs
            
            // Incorrect, just for testing, but should not be present here anyway
  //          | CoreC.Block (c, ss) -> 
  //              hs := (h, pc + 1) :: rs

            | _ -> 
              printf "unhandled stmt %s\n" (stmts.[pc].ToString())
              assert false 

    let verifyFunction (func : CoreCAST.Function) (messageSender : string->unit) =
      match func.Body with
        | Some (CoreC.Block (_, stmts)) ->
          messageSender ("Verifying: " + (func.Name) + "\n")
          let env = { Pre = spEmpty; Post = spEmpty}
          let pre = contractsToForm env func.Requires
          let post = contractsToForm env  func.Ensures
          // get parameter set
          let varset = List.fold_left (fun vs v -> S.vs_add (spCProgVar v) vs) S.vs_empty  func.Parameters
          let varset = S.vs_add (spResult func.RetType) varset
          //get variables in precondition
          let fv_pre = S.fv_form pre
          //replace all free parameters with fresh program variables  (Logical variables are forall quantified)
          let subst = S.subst_kill_vars_to_fresh_prog (S.vs_diff fv_pre varset)
          let pre = S.subst_form subst pre
          //Apply subst to post as well.  Free variables, not mentioned in pre will remain as exists. 
          let post = S.subst_form subst post
          let heap_list = [(S.convert pre, 0)]
          let stmts = CAST2CoreCAST.toStmtsArray stmts
          evalStmt { Pre = pre; Post = post} heap_list stmts
          messageSender ("Verification of " + func.Name + " succeeded.\n")
          true
        | None -> true
        | _ -> failwith (func.Name + " body does not start with a block.")
