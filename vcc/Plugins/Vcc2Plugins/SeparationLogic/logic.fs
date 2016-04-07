//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
  open Microsoft.Research.Vcc2
 
  module C = Microsoft.Research.Vcc2.CAST
  module S = Microsoft.Research.Vcc2.SepProver
  
  module Logic =

    (* Encodings into prover *)
    (* Encodings of list *)
    let spCons x t = S.mkFun "cons" [x;t]
    let spApp x t = S.mkFun "app" [x;t]
    let spNil = S.mkFun "nil" []
    let spList = fun x -> List.fold_right spCons x spNil   

    (* Avoiding types *)
    let sp_match_Int n = S.mkFun "int" [n]


    (* Addition *)
    let spNumber (n : int) = S.mkFun "int" [S.mkString (n.ToString())]
    let spAdd x y = S.mkFun "Add" [x;y]

    (* Location function *)
    let spLocationFunction = "Loc"

    (* Unique name for each field *)
    let field_name (field : C.Field) =  S.mkString (field.Parent.Name ^ "_$_" ^ field.Name) 
    
    (*  Creates a location formula *)
    let spLoc loc fields = S.mkFun spLocationFunction [loc; spList (List.map field_name fields)]
    let spLoc2 loc tls = S.mkFun spLocationFunction [loc; tls]
  
    let offset_term loc (offset : C.FieldOffset) = 
      match offset with 
        C.Normal 0 -> loc
      | C.Normal n -> spAdd loc (spNumber n)
      | _ -> failwith "offset_term"
  
    let spBlob kind loc value = 
      S.mkSPred("blob", [kind; loc; value])
  
    let spTypeDecl (typedecl : C.TypeDecl) (loc : S.term) (value : S.term) =
      match typedecl.Kind with C.Struct -> () | _ -> assert false;
      spBlob (S.mkString ("struct " ^ typedecl.Name))  loc  value
    
    let spType (typ : C.Type) (loc : S.term) (value : S.term) =
      let blob_type = 
        match typ with 
          C.Type.Ref typedecl -> "struct " ^ typedecl.Name 
        | _ -> typ.ToString()
      in
      S.mkSPred("blob", [S.mkString blob_type; loc; value])

    let lr_expand_rule pred body name logic = 
      let body' = S.subst_form (S.subst_kill_vars_to_fresh_prog (S.ev_form body)) body in 
      (* right rule*) 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, S.mkEmpty, pred);
          premises=[[(S.mkEmpty, S.mkEmpty, body)]];
          name = name^"_right";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in
      (* Left rule *)
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, pred, S.mkEmpty);
          premises=[[(S.mkEmpty, body', S.mkEmpty)]];
          name = name ^"_left";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in
      logic


    let add_struct_to_rules (defn : C.TypeDecl) (logic : S.logic) : S.logic = 
      match defn.Kind with 
        | C.Struct -> 
          let var = S.mkVar (S.unify_var "x") in
          let vartl = S.mkVar (S.unify_var "tl") in
          (* First build rewrite rules for field names *)
          let logic = 
            List.fold_left 
              (fun logic field ->  
                let match_args = [var; spCons (field_name field) vartl] in 
                let match_name = spLocationFunction in 
                let match_result = spLoc2 (offset_term var field.Offset) vartl in 
                let rr : S.rewrite_rule =
                  {op=match_name; arguments=match_args; new_term=match_result; rule_name="foo"}
                S.add_rewrite_rule rr logic  
              ) logic defn.Fields 
          (* Predicate definition for struct *)
          let valvar = S.mkVar (S.unify_var "val") in
          let evs = List.map (fun (field : C.Field) -> S.mkVar (S.exists_var field.Name)) defn.Fields in 
          let avs = List.map (fun (field : C.Field) -> S.mkVar (S.unify_var (field.Name))) defn.Fields in 
          let avs2 = List.map (fun (field : C.Field) -> S.mkVar (S.unify_var (field.Name ^ "2"))) defn.Fields in 
          let sub_structs = 
            List.map2 
              (fun (field : C.Field) ev ->   
                spType field.Type (spLoc var [field]) ev     
              ) 
              defn.Fields evs in 
          let body = List.fold_left S.mkStar S.mkEmpty sub_structs in 
          let value_eq = S.mkEQ(valvar, S.mkFun ("value_" ^ defn.Name) evs) in
          let body = S.mkStar body value_eq in 
          let pred = spTypeDecl defn var valvar in 
          (* predicate used to trigger rule *)
          let guard_pred = 
            spBlob 
              (S.mkVar (S.unify_var "__type")) 
              (spLoc2 var (S.mkVar (S.unify_var "__fields")))
              (S.mkVar (S.unify_var "__value")) in 
          (* Add unfold rule for struct *)
          let rule : S.sequent_rule = 
            { conclusion = (S.mkEmpty,pred,guard_pred);
              premises = [[(S.mkEmpty,body,guard_pred)]];
              name = "unfold_" ^ defn.Name;
              without = S.mkEmpty} in
          let logic = S.add_sequent_rule rule logic in 
          (* Add fold rule for struct *)
          let rule : S.sequent_rule = 
            { conclusion = (S.mkEmpty,guard_pred,pred);
              premises = [[(S.mkEmpty,guard_pred,body)]];
              name = "fold_" ^ defn.Name;
              without = S.mkEmpty} in
          let logic = S.add_sequent_rule rule logic in       
          (* Add value eq *)
          let pred = S.mkEQ(S.mkFun ("value_" ^ defn.Name) avs, S.mkFun ("value_" ^ defn.Name) avs2) in 
          let body = List.fold_left2 (fun form a1 a2 -> S.mkStar (S.mkEQ(a1,a2)) form) S.mkEmpty avs avs2 in 
          let logic = lr_expand_rule pred body ("value_eq_" ^ defn.Name) logic in  
          logic
        | _ -> logic


    let spIndexFunction = "Ind"
    let spArrElemLoc loc (elemType : C.Type) (index : int)  = 
      S.mkFun spIndexFunction [loc; S.mkString (elemType.ToString()); spNumber index]
    let arrElem_offset_term loc (elemType:C.Type) i =
      if (i = 0) then loc
      else spAdd loc (spNumber (i * elemType.SizeOf))

    let add_array_to_rules (elemType : C.Type) (size : int) (logic : S.logic) : S.logic = 
      let varName = "x"
      let var = S.mkVar (S.unify_var varName) in
      let typeStr = elemType.ToString()
      let arrayTypeStr = typeStr ^ "[]"
//      let arrayTypeStr = typeStr ^ "[" ^ size.ToString() ^ "]"
      let arrayTypeSzStr = typeStr ^ "[" ^ size.ToString() ^ "]"

      (* Build rewrite rules for Ind(p, t, i) = p + i*sizeof(t) *)
      let logic =
        List.fold_left 
          (fun logic i ->  
            let match_name = spIndexFunction
            let match_args = [var; S.mkString typeStr; spNumber i]
            let match_result = arrElem_offset_term var elemType i
            let rr : S.rewrite_rule =
              {op=match_name; arguments=match_args; new_term=match_result; rule_name="array_ind"}
            S.add_rewrite_rule rr logic  
          ) logic [0..size-1]

      (* Build sequent rules for folding and unfolding *)
      let valueName = ("value_" ^ elemType.ToString() ^ "_" ^ size.ToString())
//      let valueName = ("value_" ^ elemType.ToString())
      let valvar = S.mkVar (S.unify_var "val")
      let elemNames = List.map (fun i -> varName ^ "[" ^ i.ToString() ^ "]") [0..size-1] 
      let evs = List.map (fun s -> S.mkVar (S.exists_var s)) elemNames
      let avs = List.map (fun s -> S.mkVar (S.unify_var s)) elemNames
      let avs2 = List.map (fun s -> S.mkVar (S.unify_var (s ^ "2"))) elemNames
      let elems = 
        List.map2 
          (fun i ev -> spBlob (S.mkString typeStr) (spArrElemLoc var elemType i) ev)
          [0..size-1] evs
      let body = List.fold_left S.mkStar S.mkEmpty elems
      let value_eq = S.mkEQ(valvar, S.mkFun valueName evs)
      let body = S.mkStar body value_eq
      let pred = spBlob (S.mkString arrayTypeStr) var valvar
(*
      let guard_pred = 
        spBlob 
          (S.mkVar (S.unify_var "__type"))
          (var)
          (S.mkFun valueName 
            (List.map (fun s -> S.mkVar (S.unify_var s)) 
               (List.map (fun i -> "__value") [0..size-1])))
      let guard_pred = 
        spBlob 
          (S.mkVar (S.unify_var "__type")) 
          (S.mkFun "Add" [var;S.mkVar (S.unify_var "__value")])
          (S.mkVar (S.unify_var "__value"))
*)
//      printf "guard_pred: %s\n" (S.string_form guard_pred)
      let guard_pred = S.mkEmpty
      (* Add unfold rule for array *)
      let rule : S.sequent_rule = 
        { conclusion = (S.mkEmpty,pred,guard_pred);
          premises = [[(S.mkEmpty,body,guard_pred)]];
          name = "unfold_" ^ arrayTypeSzStr;
          without = S.mkEmpty}
      let logic = S.add_sequent_rule rule logic 
      (* Add fold rule for array *)
      let rule : S.sequent_rule = 
        { conclusion = (S.mkEmpty,guard_pred,pred);
          premises = [[(S.mkEmpty,guard_pred,body)]];
          name = "fold_" ^ arrayTypeSzStr;
          without = S.mkEmpty}
      let logic = S.add_sequent_rule rule logic
      (* Add value eq *)
      let pred = S.mkEQ(S.mkFun valueName avs, S.mkFun valueName avs2) in 
      let body = List.fold_left2 (fun form a1 a2 -> S.mkStar (S.mkEQ(a1,a2)) form) S.mkEmpty avs avs2 in 
      let logic = lr_expand_rule pred body ("value_eq_" ^ valueName) logic in  
      logic

    let i2b = "$int_to_bool"
    let b2i = "$bool_to_int"
    let sp_i2b t = S.mkFun i2b [t]
    let sp_b2i t = S.mkFun b2i [t]
    
    let spLift t = S.mkSPred ("lift", [t])  

    let list_pred  t x y vs = S.mkSPred ("listseg", [S.mkString t;x;y;vs])
    let node_pred  t y n v = spBlob (S.mkString ("struct " ^ t)) y (S.mkFun ("value_" ^ t) [n;v])  
    let spNull = S.mkFun "null" []

    let add_list_logic logic = 
      let t = "node" in 
      let x = S.mkVar (S.unify_var "x") in
      let y = S.mkVar (S.unify_var "y") in
      let z = S.mkVar (S.unify_var "w") in
      let w = S.mkVar (S.unify_var "z") in
      let n = S.mkVar (S.unify_var "n") in
      let v = S.mkVar (S.unify_var "v") in
      let vs1 = S.mkVar (S.unify_var "vs1") in
      let vs2 = S.mkVar (S.unify_var "vs2") in
      (* empty rules *)
      let pred = list_pred t x y spNil in
      let body = S.mkEQ(x, y) in 
      let logic = lr_expand_rule pred body "emp_list_1" logic in  
      (* second rule *)
      let pred = list_pred t x x w in
      let body = S.mkEQ(w, spNil) in 
      let logic = lr_expand_rule pred body "emp_list_2" logic in  
      (* contradiction rules  list * list *)
      let pred = S.mkStar (list_pred t x y vs1) (list_pred t x z vs2) in 
      let rule : S.sequent_rule = 
        { conclusion=(pred, S.mkEmpty, S.mkEmpty);
          premises=[[(S.mkEmpty, S.mkEQ(x,y), S.mkEmpty );
                     (S.mkEmpty, S.mkEQ(x,z), S.mkEmpty )
                   ]];
          name = "list_list_emp";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in
      (* list * blob *) 
      let pred = S.mkStar (list_pred t x y vs1) (spBlob y x vs2) in 
      let rule : S.sequent_rule = 
        { conclusion=(pred, S.mkEmpty, S.mkEmpty);
          premises=[[(S.mkEmpty, S.mkEQ(x,y), S.mkEmpty )]];
          name = "list_blob_emp";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in 
      (* unfold rule *)
      let px = S.mkVar (S.prog_var "px") in
      let pn = S.mkVar (S.prog_var "pn") in
      let pvs = S.mkVar (S.prog_var "pvs") in
      let left = list_pred t x y vs1 in 
      let right = spBlob w x z in
      let unfold1 = S.mkStar (S.mkEQ(spNil,vs1)) (S.mkEQ(x,y)) in
      let unfold2 = 
        S.mkStar (S.mkEQ(spCons px pvs,vs1))
         (S.mkStar (node_pred t x pn px) (list_pred t pn y pvs)) in 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, left, right);
          premises=[[(S.mkEmpty, unfold1, right);(S.mkEmpty, unfold2, right)]];
          name = "unfold_list";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in  
      (* fold rule *)
      let vse = S.mkVar (S.exists_var "vse") in
      let node = node_pred t x n v in 
      let list = list_pred t x y vs1 in 
      let fold = S.mkStar (list_pred t n y pvs) (S.mkEQ(spCons v vse, vs1)) in 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, node, list);
          premises=[[(node, S.mkEmpty, fold)]];
          name = "fold_list";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in 
      (* sublist rule *)
      let list = list_pred t x y vs1 in 
      let list2 = list_pred t x z vs2 in
      let list3 = list_pred t y z vse in 
      let blob = spBlob v z w in  
      let rule : S.sequent_rule = 
        { conclusion=(blob, list, list2);
          premises=[[(list, list3, S.mkEQ(vs2,spApp vs1 vse))]];
          name = "list_append";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in 
      let list2 = list_pred t x (spNull) vs2 in
      let list3 = list_pred t y (spNull) vse in 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, list, list2);
          premises=[[(list, list3, S.mkEQ(vs2,spApp vs1 vse))]];
          name = "list_append2";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in 
      (* Simple stuff for cons, app and nil *)
      let pred = S.mkEQ(spCons x y, spCons w z) in 
      let body = S.mkStar (S.mkEQ(x,w)) (S.mkEQ(y,z)) in 
      let logic = lr_expand_rule pred body "cons_inj" logic in  
      let pred = S.mkEQ(spCons x y, spNil) in 
      let body = S.mkFalse in 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, S.mkEmpty, pred);
          premises=[[(S.mkEmpty, S.mkEmpty, body)]];
          name = "cons_nil_contra_right";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, pred, S.mkEmpty);
          premises=[[(S.mkEmpty, body, S.mkEmpty)]];
          name = "cons_nil_contra_left";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in
      let pred = S.mkNEQ(spCons x y, spNil) in 
      let body = S.mkEmpty in 
      let logic = lr_expand_rule pred body "cons_nil_NEQ" logic in  
      let pred = S.mkEQ(spNil, spApp w z) in 
      let body = S.mkStar (S.mkEQ(spNil,w)) (S.mkEQ(spNil,z)) in 
      let logic = lr_expand_rule pred body "app_eq_nil" logic in         
      let pred = S.mkNEQ(spNil, spApp w z) in 
      let body = S.mkOr ((S.mkNEQ(spNil,w)),(S.mkNEQ(spNil,z))) in 
      let logic = lr_expand_rule pred body "app_neq_nil" logic in         
      let rr : S.rewrite_rule =
       {op="app"; arguments=[spNil;x]; new_term=x; rule_name="app_nil_1"} in 
      let logic = S.add_rewrite_rule rr logic in 
      let rr : S.rewrite_rule =
       {op="app"; arguments=[x;spNil]; new_term=x; rule_name="app_nil_2"} in 
      let logic = S.add_rewrite_rule rr logic in 
      logic 
          
(*
 spec (int ValidQueue(PQueue q, int xs)
  ensures (result == 
  exists(PNode _h, _t, _q; void* _d, _y; int _ys;
    blob("queue", q, value_queue(_h, _t)) &&
    blob("node", _t, value_node(_q, _d)) &&
    ((_h==_t) ==> (xs==seq_empty())) && 
    ((_h!=_t) ==> (list(_h, _t, seq_cons(_y,_ys)) && 
     seq_append(_ys, seq_cons(_d, seq_empty())) == xs))));)
*)          
    let add_valid_queue logic =
      let q = S.mkVar (S.unify_var "q") in
      let vs = S.mkVar (S.unify_var "vs") in
      let h = S.mkVar (S.fresh_exists_var_str "h") in
      let t = S.mkVar (S.fresh_exists_var_str "t") in
      let n = S.mkVar (S.fresh_exists_var_str "n") in
      let v = S.mkVar (S.fresh_exists_var_str "v") in
      let y = S.mkVar (S.fresh_exists_var_str "y") in
      let ys = S.mkVar (S.fresh_exists_var_str "ys") in
      let vs2 = S.mkVar (S.fresh_exists_var_str "vs2") in
      (* Expand definition *)
      let pred = S.mkSPred("ValidQueue",[q;vs]) in 
      let body = spBlob (S.mkString "struct queue")  q (S.mkFun "value_queue" [h;t]) in
      let body = S.mkStar body (spBlob (S.mkString "struct node") t (S.mkFun "value_node" [n;v])) in
      let body = S.mkStar body (list_pred "node" h t vs2) in
      let case1 = S.mkStar (S.mkEQ(h,t)) (S.mkEQ(vs,spNil)) in
      let case2 = S.mkStar (S.mkNEQ(h,t)) (S.mkEQ(vs2, spCons y ys )) in
      let case2 = S.mkStar case2 (S.mkEQ(spApp ys (spCons v spNil ), vs)) in 
      let body = S.mkStar body (S.mkOr(case1,case2)) in  
      let logic = lr_expand_rule pred body "valid_queue" logic in  
      (* Lifting of fun to logic *)
      let pred = spLift (sp_i2b (S.mkFun "ValidQueue" [q;vs])) in
      let body = S.mkSPred("ValidQueue",[q;vs]) in
      let logic = lr_expand_rule pred body "lift_neq" logic in  
      logic
          
    let default_logic () = 
      let logic = S.empty_logic in
      let x = S.mkVar (S.unify_var "x") in
      let y = S.mkVar (S.unify_var "y") in
      let z = S.mkVar (S.unify_var "w") in
      let w = S.mkVar (S.unify_var "z") in
      let ignore = S.mkVar (S.unify_var "ignore") in
      let ignore2 = S.mkVar (S.unify_var "ignore2") in
      (* basic blob match rule *)
      let left = spBlob x y w in 
      let right = spBlob x y z in
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, left, right);
          premises=[[(left, S.mkEmpty, S.mkEQ(w,z) )]];
          name = "blob_match";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in 
      (* rules for lifting equality *)
      let pred = spLift (S.mkFun "==" [ignore;x;y]) in
      let body= S.mkEQ(x,y) in 
      let logic = lr_expand_rule pred body "lift_eq" logic in  
      (* rules for lifting inequality *)
      let pred = spLift (S.mkFun "!=" [ignore;x;y]) in
      let body= S.mkNEQ(x,y) in 
      let logic = lr_expand_rule pred body "lift_neq" logic in  
      (* rules for lifting true *)
      let pred = spLift (S.mkFun "bool" [S.mkString "true"]) in
      let body= S.mkEmpty in 
      let logic = lr_expand_rule pred body "lift_true" logic in  
      (* rules for lifting or to proposition level *)
      let pred = spLift (S.mkFun "||" [ignore;x;y]) in
      let body = S.mkOr (spLift x, spLift y) in 
      let logic = lr_expand_rule pred body "lift_or" logic in       
      (* rules for lifting and to proposition level *)
      let pred = spLift (S.mkFun "&&" [ignore;x;y]) in
      let body = S.mkStar (spLift x) (spLift y) in 
      let logic = lr_expand_rule pred body "lift_star" logic in 
      (* HAcKS for bad translation *)
      let pred = spLift (S.mkFun "&&" [ignore;x]) in
      let body = (spLift x) in 
      let logic = lr_expand_rule pred body "lift_star" logic in   
      let pred = spLift (S.mkFun "&&" [ignore]) in
      let body = S.mkEmpty in 
      let logic = lr_expand_rule pred body "lift_star" logic in  
      (* rules for lifting blobs to proposition level *)
      let t = S.mkVar (S.unify_var "t") in 
      let pred = spLift (sp_i2b (S.mkFun "blob" [t;x;y])) in
      let body = spBlob t x y in 
      let logic = lr_expand_rule pred body "lift_blob" logic in  
      (* rules for collapsing some coercions. *)
      let rr : S.rewrite_rule =
        {op=b2i; arguments=[sp_i2b x]; new_term=x; rule_name="b2i_i2b_collapse"} in
      let logic = S.add_rewrite_rule rr logic in 
      let rr : S.rewrite_rule =
        {op=i2b; arguments=[sp_b2i x]; new_term=x; rule_name="i2b_b2i_collapse"} in
      let logic = S.add_rewrite_rule rr logic in 
      (* b2i and equality *)
      let pred = S.mkEQ(sp_match_Int (S.mkString "1"), sp_b2i x) in
      let body = spLift(x) in 
      let logic = lr_expand_rule pred body "eq_true_lift" logic in
      (* b2i and inequality *)  
      let pred = S.mkEQ(sp_match_Int (S.mkString "0"), sp_b2i x) in
      let body = spLift(S.mkFun "!" [ignore;x]) in 
      let logic = lr_expand_rule pred body "eq_false_lift" logic in
      (* b2i and inequality *)
      let pred = S.mkNEQ(sp_match_Int (S.mkString "1"), sp_b2i x) in
      let body = spLift(S.mkFun "!" [ignore;x]) in 
      let logic = lr_expand_rule pred body "neq_true_lift" logic in
      (* b2i and inequality *)  
      let pred = S.mkNEQ(sp_match_Int (S.mkString "0"), sp_b2i x) in
      let body = spLift(x) in 
      let logic = lr_expand_rule pred body "neq_false_lift" logic in
      (* Remove not eq to neq *)
      let rr : S.rewrite_rule =
       {op="!"; arguments=[S.mkFun "==" [ignore;x;y]]; new_term=S.mkFun "!=" [ignore;x;y]; rule_name="not_eq_neq"} in 
      let logic = S.add_rewrite_rule rr logic in 
      (* Remove eq when same args *)
      let rr : S.rewrite_rule =
       {op="=="; arguments=[ignore;x;x]; new_term=S.mkFun "bool" [S.mkString "true"]; rule_name="ceq_equal"} in  
      let logic = S.add_rewrite_rule rr logic in 
      (* Remove not eq to neq *)
      let rr : S.rewrite_rule =
       {op="!"; arguments=[S.mkFun "!=" [ignore;x;y]]; new_term=S.mkFun "==" [ignore;x;y]; rule_name="not_neq_eq"} in 
      let logic = S.add_rewrite_rule rr logic in 
      (* Remove empty field list *)
      let rr : S.rewrite_rule =
       {op=spLocationFunction; arguments=[x; spNil]; new_term=x; rule_name="remove_empty_field_list"} in 
      let logic = S.add_rewrite_rule rr logic in 
      (* REmove identity coercions *)
      let rr : S.rewrite_rule =
       {op="$ptr_to_i4"; arguments=[ignore;x]; new_term=x; rule_name="remove_id_coercion"} in 
      let logic = S.add_rewrite_rule rr logic in 
      let rr : S.rewrite_rule =
       {op="$ptr_cast"; arguments=[ignore;x;z]; new_term=x; rule_name="remove_id_coercion"} in 
//      let logic = S.add_rewrite_rule rr logic in 
//      let rr : S.rewrite_rule =
//       {op="int"; arguments=[x]; new_term=x; rule_name="remove_int_wrapper"} in 
      let logic = S.add_rewrite_rule rr logic in 
      (* If two equalities are equal, then lift them *)
      let pred = S.mkEQ (sp_b2i(S.mkFun "==" [ignore;x;y]), sp_b2i(S.mkFun "==" [ignore2;w;z])) in
      let case1= S.mkStar (S.mkEQ(x,y)) (S.mkEQ(w,z)) in 
      let case2= S.mkStar (S.mkNEQ(x,y)) (S.mkNEQ(w,z)) in
      let body = S.mkOr(case1,case2) in 
      let rule : S.sequent_rule = 
        { conclusion=(S.mkEmpty, S.mkEmpty, pred);
          premises=[[(S.mkEmpty, S.mkEmpty, body)]];
          name = "eq_ceq_ceq_right";
          without = S.mkEmpty;
        }
      let logic = S.add_sequent_rule rule logic in

      let logic = add_list_logic logic in 
      let logic = add_valid_queue logic in
      logic
