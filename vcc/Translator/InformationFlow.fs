//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open System.Text
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.Util
  
  module C = Microsoft.Research.Vcc.CAST
  module B = Microsoft.Research.Vcc.BoogieAST
  module TU = Microsoft.Research.Vcc.TranslatorUtils

  module InformationFlow =
    let freshPG = ref (bigint.Zero)
    let freshPtrGrp () = freshPG := bigint.op_Subtraction(!freshPG,bigint.One); !freshPG

    type SecLabel =
      | Bottom
      | Top
      | ProgramContext
      | VarLabel of C.Expr  // Label of a variable
      | VarMeta of C.Expr
      | MemLabel of C.Expr  // Label of a memory location
      | MemMeta of C.Expr
      | StructLabel of C.Expr*C.Expr // Label of a by-value structure
      | StructMeta of C.Expr*C.Expr
      | PtrCompare of C.Expr*C.Expr // Level of a pointer comparison
      | Join of SecLabel*SecLabel
      | Meet of SecLabel*SecLabel

// Gets
    let getLData name = B.Expr.Ref name
    let getPData bExpr = B.Expr.FunctionCall ("$select.flow.data", [B.Expr.FunctionCall("$memory",[B.Expr.Ref "$s"]); bExpr])

    let getLabel bExpr = B.Expr.FunctionCall ("$select.flow.label", [bExpr])
    let getMeta  bExpr = B.Expr.FunctionCall ("$select.flow.meta", [bExpr])

    let getPC = B.Expr.FunctionCall ("$select.sec.pc", [B.Expr.Ref "$s"])

// Sets
    let setLData name value = B.Stmt.Assign (getLData name, value)
    let setPData tok loc value = B.Stmt.Call (tok, [], "$store_flow_data", [loc; value])

    let setPLabel tok loc value = setPData tok loc (B.Expr.FunctionCall("$store.flow.label", [getPData loc; value]))
    let setPMeta tok loc value = setPData tok loc (B.Expr.FunctionCall("$store.flow.meta", [getPData loc; value]))

    let setLLabel name value = setLData name (B.Expr.FunctionCall("$store.flow.label", [getLData name; value]))
    let setLMeta name value = setLData name (B.Expr.FunctionCall("$store.flow.meta", [getLData name; value]))

    let setPC tok value = B.Stmt.Call (tok, [], "$store_sec_pc", [value])

// Generic Functions on SecLabels
    let rec normaliseSecLabel = function
      | Bottom
      | Top
      | ProgramContext
      | VarLabel _ | VarMeta _
      | MemLabel _ | MemMeta _
      | StructLabel _ | StructMeta _
      | PtrCompare _ as l -> l

      | Join(Bottom,l)
      | Join(l,Bottom)
      | Meet(Top,l)
      | Meet(l,Top) -> normaliseSecLabel l

      | Join(l1,l2) ->
        let l1' = normaliseSecLabel l1
        let l2' = normaliseSecLabel l2
        match l1',l2' with
          | Bottom,l
          | l,Bottom -> l
          | Top,l
          | l,Top -> Top
          | _,_ -> Join(l1',l2')
      | Meet(l1,l2) ->
        let l1' = normaliseSecLabel l1
        let l2' = normaliseSecLabel l2
        match l1',l2' with
          | Bottom,l
          | l,Bottom -> Bottom
          | Top,l
          | l,Top -> l
          | _,_ -> Meet(l1',l2')


// Level of a C expression
    let rec exprLevel asPointer (e:C.Expr) = 
      match e with
        // Constants
        | C.Expr.Macro(_, "null", _)
        | C.Expr.Macro(_, "_vcc_set_empty", _)
        | C.Expr.IntLiteral _
        | C.Expr.BoolLiteral _
        | C.Expr.SizeOf _ -> Bottom
        // Casts (care is needed when casting a pointer value to raw data)
        | C.Expr.Cast ({ Type = (C.Type.PhysPtr _ | C.Type.SpecPtr _)},_,e') -> exprLevel true e'
        | C.Expr.Cast (_,_,e') -> exprLevel false e'
        // Base Cases
        | C.Expr.Ref _ as e' ->
          match e'.Type with
            | C.Type.PhysPtr _ | C.Type.SpecPtr _ when not asPointer -> Top // We need to be much more conservative here... which types could actually be pointers?
            | _ -> VarLabel e'
        | C.Expr.Deref(_,e') -> Join(exprLevel true e', MemLabel e')
        | C.Expr.Macro (_, "_vcc_as_array", _) as e' -> MemLabel e'
        | C.Expr.Macro (_, "_vcc_current_context", []) ->  ProgramContext
        | C.Expr.Macro (_, ("_vcc_ptr_eq" | "_vcc_ptr_neq"), [p1; p2]) -> PtrCompare(p1, p2)
        | C.Expr.Macro (_, "_vcc_label_of", [expr]) ->
          let lblExpr = exprLevel asPointer expr
          let rec getMeta lbl =
            match lbl with
              | Bottom | Top | ProgramContext -> Bottom
              | VarMeta _ | MemMeta _ | StructMeta _ -> lbl
              | VarLabel e' -> VarMeta e'
              | MemLabel e' -> MemMeta e'
              | StructLabel(s,h) -> StructMeta(s,h)
              | PtrCompare _ -> Top // We probably want to figure something out here...
              | Meet (l1, l2) -> Meet (getMeta l1, getMeta l2)
              | Join (l1, l2) -> Join (getMeta l1, getMeta l2)
          getMeta lblExpr
        | C.Expr.Macro (_, "_vcc_vs_ctor", [s;h]) -> StructLabel(s,h)
        | C.Expr.Macro (_, "_vcc_current_state", _) -> Top
        | _ when e.Type = C.Type.Math "club_t" -> Top
        // Recursive Cases
        | C.Expr.Prim(_,_,es) ->
          let ugly = List.foldBack (fun e lbl -> Join (lbl,(exprLevel asPointer e))) es Bottom    // The arguments' labels are joined
          normaliseSecLabel ugly
        | C.Expr.Index (_, arr, idx) -> Join(exprLevel asPointer arr, exprLevel false idx)
        | C.Expr.Dot (_, s, _) -> exprLevel asPointer s
        // The rest
        | C.Expr.Call _    // First step: no function calls
        | C.Expr.Old _     // Contracts are not supposed to cause
        | C.Expr.Quant _  -> die() //  information-flow problems
        | _ -> failwith (sprintf "Incomplete implementation: Encountered an error while trying to take the expression level of %s." (e.ToString()))
    
    let contextify = function
      | Bottom
      | ProgramContext -> ProgramContext
      | Top -> Top
      | l -> normaliseSecLabel(Join(l,ProgramContext))

    let physicalFullExtent trExpr (ptr: C.Expr) =
      let rec removeFromExtent (ptr: option<B.Expr> -> B.Expr) ({Name = n; Fields = fs}: C.TypeDecl) =
        let newPtr fName = function
          | None -> ptr (Some(B.Expr.Ref (n+"."+fName)))
          | Some v -> B.Expr.FunctionCall("$dot", [ptr (Some(B.Expr.Ref (n+"."+fName))); v])
        let recCall = List.map (fun (f: C.Field) -> match f.Type with | C.Type.Ref td -> Some(removeFromExtent (newPtr f.Name) td) | _ -> None) fs
        let flat =
          List.fold (fun l eop ->
                       match l,eop with
                         | None, None -> None
                         | None, Some _ -> eop
                         | Some _, None -> l
                         | Some l, Some l' -> Some (l@l')) None recCall
        let nested =
          match flat with
            | None -> []
            | Some es -> es
        ptr None ::
        B.Expr.FunctionCall ("$dot", [ptr None; B.Expr.Ref (n+".$owns")]) ::
        nested
      match ptr.Type with
        | C.Type.PhysPtr(C.Type.Ref td) ->
          let bPtr = trExpr ptr
          let stripPtr = function
            | None -> bPtr
            | Some f -> B.Expr.FunctionCall ("$dot", [bPtr; f])
          let minusList = removeFromExtent stripPtr td
          let minus = List.fold (fun setExpr bExpr ->
                                   match setExpr with
                                     | B.Expr.FunctionCall("$set_empty", []) -> B.Expr.FunctionCall("$set_singleton", [bExpr])
                                     | s -> B.Expr.FunctionCall("$set_union", [setExpr; B.Expr.FunctionCall("$set_singleton", [bExpr])]))
                                (B.Expr.FunctionCall("$set_empty", []))
                                minusList
          B.Expr.FunctionCall("$set_difference", [B.Expr.FunctionCall("$full_extent", [bPtr]); minus])
        | _ -> System.Console.WriteLine("Type: {0}", ptr.Type); die()

// Translating a label expression into a Boogie expression
    let rec secLabelToBoogie trExpr trVar = function
      | ProgramContext -> getPC

      | PtrCompare (p1, p2) ->
        B.Expr.FunctionCall("$ptrclub.compare", [trExpr p1; trExpr p2])
      
      | Meet (Bottom, _)
      | Meet (_, Bottom)
      | Bottom -> B.Expr.Ref "$lblset.bot"
      
      | Join (Top, _)
      | Join (_, Top)
      | Top -> B.Expr.Ref "$lblset.top"
      
      | VarLabel e -> 
        match e with
          | C.Expr.Ref(_,v) -> getLabel (getLData ("FlowData#"+(trVar v)))
          | C.Expr.Result _ -> getLabel (getLData "FlowData#special#result")
          | _ -> die()
      | VarMeta e ->
        match e with
          | C.Expr.Ref(_,v) -> getMeta (getLData ("FlowData#"+(trVar v)))
          | C.Expr.Result _ -> getMeta (getLData "FlowData#special#result")
          | _ -> die()

      | MemLabel e ->
        match e with
          | C.Expr.Ref(_, v) -> getLabel (getPData (trExpr e))
          | C.Expr.Dot _
          | C.Expr.Index _
          | C.Expr.Macro (_, "_vcc_as_array", _) -> getLabel (getPData (trExpr e))
          | C.Expr.Deref(_, e') -> getLabel (getPData (trExpr e'))
          | _ -> failwith (sprintf "Incomplete implementation: Encountered a MemLabel with argument %s\n." (e.ToString()))
      | MemMeta e ->
        match e with
          | C.Expr.Ref(_,v) -> getMeta (getPData (trExpr e))
          | C.Expr.Dot _
          | C.Expr.Index _
          | C.Expr.Macro (_, "_vcc_as_array", _) -> getMeta (getPData (trExpr e))
          | C.Expr.Deref(_, e') -> getMeta (getPData (trExpr e'))
          | _ -> failwith (sprintf "Incomplete implementation: Encountered a MemMeta with argument %s\n." (e.ToString()))

      | StructLabel(s,h) -> B.Expr.FunctionCall ("$get.seclabel.lub", [B.Expr.FunctionCall("$memory", [trExpr s]); physicalFullExtent trExpr h])
      | StructMeta(s,h) -> B.Expr.FunctionCall ("$get.metalabel.lub", [B.Expr.FunctionCall("$memory", [trExpr s]); physicalFullExtent trExpr h])

      | Meet (Top, l)
      | Meet (l, Top)
      | Join (Bottom, l)
      | Join (l, Bottom) -> secLabelToBoogie trExpr trVar l

      | Join (l1, l2) -> B.Expr.FunctionCall ("$lblset.join", [secLabelToBoogie trExpr trVar l1;secLabelToBoogie trExpr trVar l2])
      | Meet (l1, l2) -> B.Expr.FunctionCall ("$lblset.meet", [secLabelToBoogie trExpr trVar l1;secLabelToBoogie trExpr trVar l2])

    let scanForIFAnnotations (decl:C.Top) =
      let res = ref false
      let bodyHasIFAnnotations _ = function
        | C.Expr.If(_, Some _, _, _, _)
        | C.Expr.Macro(_, "_vcc_lblset_leq", _)
        | C.Expr.Macro(_, "_vcc_downgrade_to", _)
        | C.Expr.Macro(_, "_vcc_current_context", _)
        | C.Expr.Macro(_,"_vcc_label_of",_) -> res := true; false
        | _ -> true
      match decl with
        | C.Top.FunctionDecl fn ->
          match fn.Body with
            | None -> false
            | Some body -> body.SelfVisit(bodyHasIFAnnotations); !res
        | _ -> false

// Transformations for if statements
    let rec insert acc e = function
      | [] -> e :: acc
      | e'::_ as es when e' = e -> es @ acc
      | e'::es -> insert (e'::acc) e es
    let union es es' = List.foldBack (insert []) es es'
    
    let makePermissiveUpgrade trExpr trVar trType cExpr testClassif =
      let cLevel = secLabelToBoogie trExpr trVar (exprLevel false cExpr)
      let cMeta  = secLabelToBoogie trExpr trVar (exprLevel false (C.Expr.Macro({cExpr.Common with Type = C.Type.SecLabel(Some cExpr)}, "_vcc_label_of", [cExpr])))
      B.Expr.Lambda (Token.NoToken,
                     ["PU#CLS#ptr",B.Type.Ref "$ptr"],
                     [],
                     B.Expr.Primitive("||",
                                      [B.Expr.FunctionCall("$select.$map_t..$ptr_to..^^void.^^bool", [testClassif; B.Expr.Ref "PU#CLS#ptr"])
                                       B.Expr.Primitive("||",
                                                        [B.Expr.ArrayIndex(getPC, [B.Expr.Ref "PU#CLS#ptr"])
                                                         B.Expr.Primitive("&&",
                                                                          [B.Expr.ArrayIndex(cLevel, [B.Expr.Ref "PU#CLS#ptr"])
                                                                           B.Expr.Primitive("!", [B.Expr.ArrayIndex(cMeta, [B.Expr.Ref "PU#CLS#ptr"])])])])]))

    let bExprLevel bExpr =
      let rec getVarLevels = function
        | B.Expr.Ref (vname) as v -> [v]
        | B.Expr.FunctionCall ("$select.sec.pc", _) -> []
        | B.Expr.FunctionCall ("$select.flow.label", [fd]) -> [getMeta fd]
        | B.Expr.FunctionCall ("$select.flow.meta", _) as l -> [l]
        | B.Expr.BoolLiteral _
        | B.Expr.IntLiteral _
        | B.Expr.BvLiteral _ -> []
        | B.Expr.BvConcat (e1,e2) ->
          let v1 = getVarLevels e1
          let v2 = getVarLevels e2
          union v1 v2
        | B.Expr.BvExtract (e,_,_) -> getVarLevels e
        | B.Expr.Primitive (_,es) -> List.fold (fun vs e -> let v = getVarLevels e in union vs v) [] es
        | _ as e -> failwith (sprintf "Incomplete implementation: Failed on making hazardous check for expression %s\n." (e.ToString()))
      let varLevels = getVarLevels bExpr
      let construct bExpr expr =
        B.Expr.Primitive ("&&", [expr; B.Expr.FunctionCall("$lblset.leq",  [bExpr; B.Expr.Ref "$lblset.bot"])])
      List.foldBack construct varLevels (B.Expr.BoolLiteral true)
