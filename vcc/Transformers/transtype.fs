//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
 open Microsoft.FSharp.Math
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.CAST
 
 module TransType =
 
  let setEqualityKind (td : TypeDecl) eqKind =
    let rec markTypeDecl eqKind (td : TypeDecl) =
      match td.GenerateEquality, eqKind with
        | (NoEq | ShallowEq), DeepEq  -> 
          td.GenerateEquality <- eqKind
          List.iter (markField eqKind) td.Fields
        | (NoEq | ShallowEq), ShallowEq when td.Kind = TypeKind.Union  -> 
          td.GenerateEquality <- eqKind
          List.iter (markField eqKind) td.Fields
        | DeepEq , ShallowEq -> ()
        | _ -> 
          assert (eqKind <> NoEq)
          td.GenerateEquality <- eqKind
    and markField eqKind (f : Field) =
      match f.Type with
      | Type.Ref td -> markTypeDecl eqKind td
      | _ -> ()
    markTypeDecl eqKind td

  // ============================================================================================================
  
  
  let init (helper:TransHelper.TransEnv) =
    
    // ============================================================================================================
    
    let handleFunctionPointers decls =
      let parentDecl = ref (Axiom(bogusExpr))
      let addDecls = ref []
      let checks = new Dict<_,_>()
      let fnids = new Dict<_,_>()
      let addThis (fnptr:Function) =
        match fnptr.Parameters with
          | { Name = "$this" } :: _ -> ()
          | parms ->
            let th = Variable.CreateUnique "$this" (PhysPtr Void) VarKind.Parameter
            fnptr.Parameters <- th :: parms
                    
      let repl ctx self = function
        | Expr.Macro (comm, "&", [Expr.Macro (_, "get_fnptr", [Expr.Call (_, called, _, [])])]) ->
          if not (fnids.ContainsKey called.Name) then
            fnids.[called.Name] <- fnids.Count
          Some (Expr.Macro ({ comm with Type = PhysPtr Void }, "_vcc_get_fnptr", [mkInt fnids.[called.Name]; typeExpr Void]))
          
        | Expr.Cast ({ Token = tok; Type = (Ptr (Type.Ref { Kind = FunctDecl fnptr } as fnptrref)) } as comm, CheckedStatus.Checked, 
                     Expr.Macro (_, "&", [Expr.Macro (_, "get_fnptr", [Expr.Call (_, called, [], [])])])) ->
          if not (fnids.ContainsKey called.Name) then
            fnids.[called.Name] <- fnids.Count
          let neqPar (a:Variable) (b:Variable) = a.Type <> b.Type
          addThis fnptr
          let fnptrparms = fnptr.Parameters.Tail
          if ctx.IsPure then
            helper.Error (tok, 9602, "checked function pointer casts are only allowed in non-pure context", None)
            None
          elif List.length fnptrparms <> List.length called.Parameters then
            helper.Error (tok, 9603, "checked function pointer cast: different number of parameters", Some(called.Token))
            None
          elif List.exists2 neqPar fnptrparms called.Parameters then
            helper.Error (tok, 9604, "checked function pointer cast: different types of parameters", Some(called.Token))
            None
          elif fnptr.RetType <> called.RetType then
            helper.Error (tok, 9605, "checked function pointer cast: different return types", Some(called.Token))
            None
          else
            let (checkPrefix, inheritedAttrs) =
              match !parentDecl with
                | Top.FunctionDecl fn -> (fn.Name + "#fnptr#", inheritedAttrs fn.CustomAttr)
                | _ -> ("$fnptr#", [])
            let header = { fnptr with Name = checkPrefix + called.Name + "_to_" + fnptr.Name; Token = tok; 
                                      Parameters = List.map (fun (v:Variable) -> v.UniqueCopy()) fnptr.Parameters;
                                      CustomAttr = fnptr.CustomAttr @ inheritedAttrs }
            if not (checks.ContainsKey header.Name) then
              checks.Add (header.Name, checks.Count)
              let call = Expr.Call ({ comm with Type = called.RetType },
                                    called, 
                                    [], 
                                    List.map mkRef fnptrparms)
              let body = 
                if called.RetType = Void then call 
                else Expr.Return ({ call.Common with Type = Void }, Some call)
              let def = FunctionDecl { header with Body = Some body }
              addDecls := def :: !addDecls
            Some (Expr.Macro (comm, "_vcc_get_fnptr", [mkInt fnids.[called.Name]; typeExpr fnptrref]))
        | Expr.Macro (c, "fnptr_call", fn :: args) ->
          match fn.Type with
            | FunctionPtr decl ->
              addThis decl
              if ctx.IsPure then
                Some (Expr.Call (c, decl, [], fn :: args))
              else
                let (init, tmp) = cache helper "ptrcall" fn VarKind.Local
                let assertions = init @ [
                                   propAssert 8504 "{0} is valid function pointer" "_vcc_typed2" tmp;
                                   Expr.Call (c, decl, [], tmp :: args)]
                Some (self (Expr.MkBlock assertions))
            | _ -> die()
        | _ -> None
      
      let doDecl decl =
        parentDecl := decl
        let replExpr isPure (e:Expr) = e.SelfCtxMap(isPure, repl)
        decl.MapExpressions replExpr

      (List.map doDecl decls) @ !addDecls
      
    // ============================================================================================================
    
    let liftGroups decls =   
    
      let groupTypes = new Dict<TypeDecl * string, TypeDecl>()
      let fieldTransform = new Dict<Field, TypeDecl * Field * Field>()
      let groupParent = new Dict<TypeDecl, TypeDecl * Field>()
      let groupAxioms = ref []
           
      let rec getGroupNameFromAttrs = function
        | [] -> None
        | VccAttr(AttrInGroup, name) :: _ -> 
          Some name
        | VccAttr(AttrGroupDecl, name) :: _ -> 
          Some name
        | _ :: attrs -> getGroupNameFromAttrs attrs
        
      let removeGroupDeclAttrs =
        let isNotGroupDeclAttr = function | VccAttr((AttrInGroup|AttrGroupDecl), _) -> false | _ -> true
        List.filter isNotGroupDeclAttr

      let makeTypeNameForGroup parentName groupName = parentName + "##" + groupName

      let findGroupTypes decls =
        let addToDictIfGroupType = function
          | Top.TypeDecl td ->
            match getGroupNameFromAttrs td.CustomAttr with
            | Some groupName ->
              match td.Parent with
              | Some parent -> 
                td.Name <- makeTypeNameForGroup parent.Name groupName
                td.SizeOf <- parent.SizeOf
                td.CustomAttr <- VccAttr("__vcc_group", "") :: td.CustomAttr
                match groupTypes.TryGetValue ((parent, groupName)) with
                  | true, td' ->
                    let msg = "'" + groupName + "' : group name redefinition"
                    helper.Error(td.Token, 9678, msg, Some(td'.Token))
                  | _ -> groupTypes.[(parent, groupName)] <- td
              | None -> 
                helper.Oops(td.Token, "Encountered group type without parent.")
                helper.Die()
            | None -> ()
          | _ -> ()
          
        List.iter addToDictIfGroupType decls
           
      let genGroupAxiom (group:TypeDecl) (parent:TypeDecl) (groupField : Field) =
        let t = Type.MkPtrToStruct(group)
        let pt = Type.MkPtrToStruct(parent)
        let v = Variable.CreateUnique "ptr" t VarKind.QuantBound
        let ptr = Expr.Ref({bogusEC with Type = t}, v)
        let rhs = Expr.Dot({bogusEC with Type = t}, Expr.Cast({bogusEC with Type = pt}, CheckedStatus.Unchecked, ptr), groupField)
        let eq = Expr.Prim(boolBogusEC(), Op.Op("==", CheckedStatus.Unchecked), [ptr; rhs])
        let forall = Expr.Quant(boolBogusEC(), { Kind = QuantKind.Forall
                                                 Variables = [v]
                                                 Triggers = [[ptr]]
                                                 Condition = None
                                                 Body = eq 
                                                 Weight = "c-group-axiom"
                                                 })
        Top.GeneratedAxiom(forall, Top.TypeDecl(parent))                                                             
        
           
      let makeTypeDeclsForGroups (parent:TypeDecl) =
        let typeDecls = new Dict<string, TypeDecl * Field>()
        let findOrCreateTypeForGroup groupName =
          match typeDecls.TryGetValue groupName with
          | (true, (td, field)) -> (false, td, field) // type exists, no new field
          | (false, _) ->
            // create type for the previously unencountered group and create a field for it in the parent
            match groupTypes.TryGetValue((parent, groupName)) with
            | (true, td) ->
              let newField = { Name = groupName
                               Token = parent.Token
                               Type = Type.Ref td
                               Parent = parent
                               IsSpec = false
                               IsVolatile = false 
                               Offset = Normal 0
                               CustomAttr = []
                               UniqueId = CAST.unique() }
              typeDecls.[groupName] <- (td, newField)
              groupParent.[td] <- (parent, newField)
              (true, td, newField)
            | _ -> 
              helper.Oops(parent.Token, "Unknown group \"" + groupName + "\" in field declaration.")
              helper.Die()

        let rec processFields = function
          | [] -> []
          | (field : Field) :: fields' ->
            match getGroupNameFromAttrs field.CustomAttr with
            | None -> field :: processFields fields'
            | Some groupName ->
              let (isNewField, groupTd, groupField) = findOrCreateTypeForGroup groupName 
              let nestedField = { field with Parent = groupTd; CustomAttr = removeGroupDeclAttrs field.CustomAttr }
              groupTd.Fields <- groupTd.Fields @ [ nestedField ]
              fieldTransform.[field] <- (groupTd, groupField, nestedField)
              if (isNewField) then
                groupField :: processFields fields'
              else
                processFields fields'
        
        let rec processInvariants invs =
          let retypeThis td self = function
            // the 'this' will have type of the group in the invariant defintion
            // however field accesses are done with the type of parent in mind
            // therefore for field accesses we cast back
            | Expr.Dot (c1, (Expr.This(c2) as th), f) ->
              Some (Expr.Dot (c1, Expr.Cast (c2, Processed, self th), f))
            | Expr.This(c) ->
              Some (Expr.This({ c with Type = Type.MkPtrToStruct(td) }))
            | _ -> None
           
     
          match invs with 
          | [] -> []
          | Expr.Macro(_, "labeled_invariant", [_; Expr.Macro(_, "group_invariant", [Expr.Macro(_, groupName,_); groupInvariant])]) :: invs'
          | Expr.Macro(_, "group_invariant", [Expr.Macro(_, groupName,_); groupInvariant]) :: invs' ->
            match typeDecls.TryGetValue(groupName) with
            | (true, (td, _)) -> 
              td.Invariants <-  groupInvariant.SelfMap (retypeThis td) :: td.Invariants
              processInvariants invs'
            | (false, _) ->
              helper.Oops(groupInvariant.Common.Token, "Unknown group \"" + groupName + "\" in invariant declaration.")
              helper.Die()
              
          | inv :: invs' -> inv :: processInvariants invs'
        
        parent.Fields <- processFields parent.Fields
        parent.Invariants <- processInvariants parent.Invariants
              
      let transformFields self = function
        | Dot (c, e, f) ->
          match fieldTransform.TryGetValue f with
          | (false, _) -> None
          | (true, (groupTd, groupField, fieldField)) ->
            if e.Type.IsPtrTo(Type.Ref groupTd) then
              Some (Dot (c, self e, fieldField))
            else
              match self e with
                // Simplify group field access in invariants, makes matching in @approves(...) work.
                | Cast (_, _, (This _ as th)) when th.Type.IsPtrTo (Type.Ref groupTd) ->
                  Some (Dot (c, th, fieldField))
                | se ->
                  Some (Dot (c, Expr.MkDot(c, se, groupField), fieldField))
        // rewrite (user supplied) casts to group types into field accesses
        | Cast (c, _, e) ->
          match c.Type, e.Type with
            | Ptr (Type.Ref gr), Ptr (Type.Ref par)
            | Ptr (Type.Ref gr), Ptr (Volatile(Type.Ref par)) ->
              match groupParent.TryGetValue gr with
                | true, (tp, fld) when tp = par ->
                  Some (self (Dot (c, e, fld)))
                | _ -> None
            | _ -> None
        | _ -> None 
                 
      let processDecls decls =
        let processDecl = function
          | Top.TypeDecl td -> makeTypeDeclsForGroups td
          | _ -> ()
        List.iter processDecl decls

      findGroupTypes decls
      processDecls decls
      deepMapExpressions transformFields (decls @ !groupAxioms)
    
    
    
    // ============================================================================================================
    
         
    (*
        mark those types that have been introduced as as nested anonymous types, e.g., as in
        
        struct S {
          int a;
          int b;
          struct {  <- this is the type that is marked as such
            int c;
            int d;
          };
        };
        
        and introduce extra Dot expressions that normalize the access to the type's members
        
    *)     
    let markNestedAnonymousTypes decls =
      for d in decls do
        match d with
          | Top.TypeDecl td ->
            for f in td.Fields do
              if f.Name = "" || f.Name.StartsWith "#" then
                match f.Type with
                  | Type.Ref td' ->
                    td'.IsNestedAnon <- true
                  | _ -> ()
          | _ -> ()

      let findFieldForType (td:TypeDecl) =
        match td.Parent with
          | Some parent -> List.find (fun (fld:Field) -> fld.Type = Type.Ref(td)) parent.Fields
          | None -> die()

      let rec addDotForAnonField  = function
        | Dot (c, e, f) when f.Parent.IsNestedAnon -> 
          let fld = findFieldForType f.Parent
          Dot(c, addDotForAnonField(Expr.MkDot(c, e, fld)), f)
        | expr -> expr
     
      let normalizeDots self = function
        | Dot (c, Macro (_, "&", [Deref (_, e)]), f) -> Some (self (Dot (c, e, f)))
        | Dot (c, e, f) when f.Parent.IsNestedAnon -> Some (addDotForAnonField (Dot(c, self e, f)))
        | _ -> None
          
      deepMapExpressions normalizeDots decls
       
    // ============================================================================================================
    
    let rec bv_extrAndPad (c:ExprCommon) (e:Expr) fromBit toBit =

      let sz =
        match e.Type.Deref with
          | Integer IntKind.UInt64
          | Integer IntKind.Int64 -> 64
          | Integer IntKind.UInt32
          | Integer IntKind.Int32 -> 32
          | Integer IntKind.Int16
          | Integer IntKind.UInt16 -> 16
          | Integer IntKind.Int8 
          | Integer IntKind.UInt8 -> 8
          | _ -> die() // we explicitly don't want anything else here

      Expr.Macro (c, "pullout_bv_extract_" + (if c.Type.Deref.IsSignedInteger then "signed" else "unsigned"), 
                  [e; mkInt sz; mkInt fromBit; mkInt toBit])

    let flattenUnions decls =

      let fieldsToReplace = new Dict<Field, Field>()
      let processedTypes = new HashSet<TypeDecl>()
  
      let tryFindBackingMember (td:TypeDecl) = 
        let tdIsRecord = td.IsRecord
        let isValidField (fld : Field) =
          let isValidType = 
            let rec isValidType' allowArray = function
            | Integer _ | Ptr _ -> true
            | Array(t, _) when allowArray -> isValidType' false t
            | Type.Ref(td) -> td.Fields.Length = 1 && isValidType' false  td.Fields.Head.Type
            | _ -> false
            isValidType' true
          (tdIsRecord || not fld.IsSpec) && fld.Type.SizeOf = td.SizeOf && isValidType fld.Type
        match List.filter (fun (fld:Field) -> hasCustomAttr AttrBackingMember fld.CustomAttr) (td.Fields) with
          | [] -> None
          | [fld] ->
             if isValidField fld then 
               Some fld 
             else 
               helper.Error (fld.Token, 9633, "'" + fld.Name + "' cannot be used as a backing member for type '" + td.Name + "'", Some(td.Token))
               None
          | fld0 :: fld1 :: _ ->
            helper.Error (fld0.Token, 9747, "More than one field marked as backing_member", Some(fld1.Token))
            None
    
      let backingField (fld : Field) =
        let rec getPrimitiveType = function
          | Integer _ | Ptr _ as t -> t
          | Type.Ref(td) -> getPrimitiveType td.Fields.Head.Type
          | _ -> die()
        match fld.Type with
          | Integer _ | Ptr _ | Array(Integer _, _) | Array(Ptr _, _) -> fld
          | Type.Ref(_) -> { fld with Name = fld.Name + "#bm"; Type = getPrimitiveType fld.Type }
          | Array(Type.Ref(_) as t, n) -> { fld with Name = fld.Name + "#bm"; Type = Array(getPrimitiveType(t), n) }
          | _ -> die()
                     
      let rec hasVolatileInExtent (fld : Field) =
        if fld.IsSpec then false 
        else if fld.IsVolatile then true else hasVolatileExtentForType fld.Type
      and hasVolatileExtentForType = function
          | Type.Ref(td) -> List.exists hasVolatileInExtent td.Fields
          | Array(t,_) -> hasVolatileExtentForType t
          | _ -> false
    
      let rec processTypeDecl = function
        | TypeDecl(td) when td.Kind = TypeKind.Union ->
          if processedTypes.Add td then
            let rec processType = function
              | Type.Ref(td) -> processTypeDecl (TypeDecl(td))
              | Type.Array(t, _) -> processType t
              | _ -> ()
            List.iter (fun (fld : Field) -> processType (fld.Type)) td.Fields
            match tryFindBackingMember td with
              | Some fld -> 
                let bf = { backingField fld with IsVolatile = List.exists hasVolatileInExtent td.Fields }        
                let tdIsRecord = td.IsRecord
                let addOtherFlds (f : Field) =
                  if f = bf || (f.IsSpec && not tdIsRecord) then () else fieldsToReplace.Add(f, bf)
                List.iter addOtherFlds (td.Fields)
                td.Fields <- bf :: if tdIsRecord then [] else List.filter (fun (f : Field) -> f.IsSpec) td.Fields
              | None ->()
        | _ -> ()
    
      let rec genDotPrime t1 t2 expr =
        match t1, t2 with
          | (Integer _ | Type.Ref _ | Ptr _), (Integer _ | Ptr _) -> Macro({bogusEC with Type = PhysPtr(t1)}, "Dot'", [expr; mkInt 0])
          | t1', Array(t2', _) -> genDotPrime t1' t2' expr
          | Array(t1',_), t2' -> genDotPrime t1' t2' expr
          | _, _ -> die()
    
      let replExpr self = function
        | Dot (c, Macro (_, "&", [Deref (_, e)]), f) -> Some (self (Dot (c, e, f)))
        | Index(c, Macro (_, "&", [Deref (_, e)]), i) -> Some(self (Index(c, e, i)))
        | Dot (c, e, f) as expr ->
          match fieldsToReplace.TryGetValue(f) with
            | true, newFld -> 
              let isSpec = match e.Type with | SpecPtr _ -> true | _ -> newFld.IsSpec
              Some(self (genDotPrime (f.Type) (newFld.Type) (Dot({c with Type = Type.MkPtr(newFld.Type, isSpec)}, (self e), newFld)))) 
              // do NOT call MkDot here because we need to preserve the information that the new field is of array type
              // during the bm substitution process
            | false, _ -> None          
        | _ -> None

      let rippleOutDotPrime self = function
        | Dot(c, e, f) ->
          match self e with
            | Macro(_, "Dot'", [expr; IntLiteral(_, offset)]) ->
              Some(Macro({bogusEC with Type = PhysPtr(f.Type)}, "Dot'", [expr; mkInt ((int)offset + f.ByteOffset)]))
            | se -> Some(Dot(c, se, f))
        | Index(c, e, idx) ->
          match self e with
            | Macro(_, "Dot'", [expr; IntLiteral(_, offset)]) ->
              let reportError() = helper.Error(c.Token, 9654, "Expression is invalid due to union flattening. Flattening of arrays requires the backing member to be of array type with same element size and alignment.", None)
              if not expr.Type.Deref._IsArray then 
                reportError()
                Some(bogusExpr)
              else
                let elemSize = c.Type.Deref.SizeOf
                let bmElemType = match expr.Type.Deref with Array(t, _) -> t | _ -> die()
                if ((int)offset % elemSize <> 0) || (elemSize  <> bmElemType.SizeOf) then
                  reportError()
                  Some(bogusExpr)
                else
                  let idx' = if offset = bigint.Zero then idx else Prim(idx.Common, Op("+", Checked), [mkInt((int)offset); idx])
                  Some(self(Macro({bogusEC with Type = c.Type}, "Dot'", [Index({c with Type = PhysPtr(bmElemType)}, expr, idx'); mkInt 0])))
            | e' -> Some(Index(c, e', self idx))
        | _ -> None

      let removeDotPrime self = function
        | Macro(c, "Dot'", [expr; IntLiteral(_, offset)]) ->
          match c.Type.Deref, expr.Type.Deref with
            | ct, _ when ct.IsComposite ->
              Some(expr)
            | _, Array(elemType, _) ->  
              Some(self(Macro(c, "Dot'", [Index({expr.Common with Type = PhysPtr(elemType)}, expr, mkInt ((int)offset / elemType.SizeOf)); mkInt ((int)offset % elemType.SizeOf)])))
            | (Ptr(_) as ct), Ptr(_) -> Some(Macro({c with Type = ct}, "pullout_cast", [self expr]))
            | Integer(_) as ct, Ptr(_) ->
              let targetTypeCode, conversionFunction = if ct.IsSignedInteger then IntKind.Int64, "pullout__vcc_ptr_to_i8" else IntKind.UInt64, "pullout__vcc_ptr_to_u8"
              Some(self(Macro(c, "Dot'", [Macro({bogusEC with Type = PhysPtr(Integer(targetTypeCode))}, conversionFunction, [expr]); mkInt((int)offset)])))
            | Ptr(_) as ct, (Integer(_) as et) ->
              let conversionFunction = if et.IsSignedInteger then "pullout__vcc_i8_to_ptr" else "pullout__vcc_u8_to_ptr"
              Some(Macro({c with Type = ct}, "pullout_cast", [Macro({bogusEC with Type = PhysPtr(Void)}, conversionFunction, [self expr])]))
            | Integer(_) as ct, Integer(_) as et ->
              Some(bv_extrAndPad {expr.Common with Type = ct} (self expr) ((int)offset * 8) (((int)offset + ct.SizeOf) * 8))
            | _ -> die()
        | Deref(c,e) ->
          match (self e) with
            | Macro(bvec, name, e'::args) when name.StartsWith("pullout_") ->
              Some(self (Macro(bvec, name, Deref({c with Type = e'.Type.Deref}, e')::args)))
            | e' -> Some(Deref(c, e'))
        | _ -> None

      let removePullOut self = function
        | Macro(bvec, "pullout_cast", [e']) -> Some(Cast(bvec, Unchecked, self e'))
        | Macro(c, name, args) when name.StartsWith("pullout_") -> Some(Macro(c, name.Substring(8), List.map self args))
        | _ -> None
              
      let coalesceBvExtractsAndUncheckedCoversions self = 
        let getSuffix = function 
          | Integer k -> Type.IntSuffix(k)
          | _ -> die()
        function
          | Expr.Macro (c, ("bv_extract_signed" | "bv_extract_unsigned"), 
                        [e; IntLiteral(_, sz); IntLiteral(_, z); IntLiteral(_, sz') ]) when z = zero && sz = sz' -> 
              let unchecked (expr :Expr) =
                match expr.Type.DerefSoP with 
                  | Integer k, isSpec -> Macro({expr.Common with Type = Type.MkPtr(Integer(Type.SwitchSignedness k), isSpec)}, "unchecked_" + Type.IntSuffix(Type.SwitchSignedness k), [expr])
                  | _ -> die()                      
              let e' = if c.Type.Deref.IsSignedInteger = e.Type.Deref.IsSignedInteger then e else unchecked e             
              Some(self e')
          | Macro(c, outer, [Macro(_, inner, [expr])]) when outer.StartsWith("unchecked_") && inner.StartsWith("unchecked_") ->
            Some(self(Macro(c, outer, [expr])))
          | Macro(c, outer, [expr]) when outer.StartsWith("unchecked_") && outer.Substring(10) = getSuffix (expr.Type) ->
            Some(self expr)
          | Macro(c, outer, [Macro(_, inner, [expr; innerSize; innerStart; _]); _; outerStart; outerEnd]) when outer.StartsWith("bv_extract_") && inner.StartsWith("bv_extract_") ->
            let toInt = function
              | IntLiteral(_, i) -> (int)i
              | _ -> die()
            Some(self(Macro(c, outer, [self expr; innerSize; mkInt ((toInt innerStart) + (toInt outerStart)); mkInt ((toInt innerStart) + (toInt outerEnd))])))
          | Expr.Macro (c, (("bv_extract_signed" | "bv_extract_unsigned") as extractName), e :: args)  -> 
            match self e with
              | Expr.Macro(c, name, [e']) when name.StartsWith("unchecked_") ->
                Some(self (Expr.Macro(c, extractName, e' :: args)))
              | e' -> Some(Expr.Macro(c, extractName, e' :: args))
                
          
          | _ -> None
      
      decls |> List.iter processTypeDecl
      decls |> deepMapExpressions replExpr 
            |> deepMapExpressions rippleOutDotPrime 
            |> deepMapExpressions removeDotPrime 
            |> deepMapExpressions removePullOut
            //|> deepMapExpressions removeTrivialBvOps
            |> deepMapExpressions coalesceBvExtractsAndUncheckedCoversions
    
    // ============================================================================================================
    
    let removeBitfields decls =
    
      let fieldsToReplace = new Dict<Field, Field>()
    
      let hasBitFields (td : TypeDecl) =
        let isBitField = function
          | BitField(_,_,_) -> true
          | _ -> false
        List.exists ((fun f -> f.Offset) >> isBitField) (td.Fields)

      let fieldsForBitfields td = 
        let addFieldSubst oldFld = function
          | None -> die()
          | Some newFld -> fieldsToReplace.Add(oldFld, newFld)
        let rec fieldsForBitfields' currentOffset lastNewField = function
          | [] -> []
          | ({ Offset = Normal(n) } as fld) :: flds -> fld :: (fieldsForBitfields' (n+fld.Type.SizeOf) None flds)
          | ({ Offset = BitField(byteOffset, bitOffset, bitSize) } as fld) :: flds ->
              if (currentOffset * 8 >= (byteOffset * 8 + bitOffset + bitSize)) then
                addFieldSubst fld lastNewField
                fieldsForBitfields' currentOffset lastNewField flds
              else
                let newFldType = match fld.Type with | Integer k -> Integer (Type.ToUnsigned k) | _ -> die()
                let newFld = { fld with Name = "bitfield#" + byteOffset.ToString(); Offset = Normal(byteOffset); Type = newFldType }
                addFieldSubst fld (Some newFld)
                newFld :: (fieldsForBitfields' (byteOffset + newFld.Type.SizeOf) (Some newFld) flds)
        fieldsForBitfields' 0 None td.Fields

      let fieldsForBitfieldsInUnion td =
        let f = function
          | ({ Offset = BitField(byteOffset, bitOffset, _) } as fld) ->
            if byteOffset <> 0 || bitOffset <> 0 then helper.Oops(fld.Token, "bitfield with non-zero byte- or bit-offset in union")
            let newFld = { fld with Offset = Normal(0) }
            fieldsToReplace.Add(fld, newFld)
            newFld
          | fld -> fld
        List.map f (td.Fields)
          

      let processTypes = function
         | TypeDecl td when td.Kind = TypeKind.Struct && hasBitFields td -> td.Fields <- fieldsForBitfields td
         | TypeDecl td when td.Kind = TypeKind.Union && hasBitFields td -> td.Fields <- fieldsForBitfieldsInUnion td
         | _ -> ()

      let toBitFieldOffset size = function
        | Normal n -> BitField(n, 0, size*8)
        | bf -> bf

      let replExpr self = function
        | Dot (c, Macro (_, "&", [Deref (_, e)]), f) -> Some (self (Dot (c, e, f)))
        | Index(c, Macro (_, "&", [Deref (_, e)]), i) -> Some(self (Index(c, e, i)))
        | Macro(c, "vs_updated", [Dot(_, e, f); expr]) ->
          match fieldsToReplace.TryGetValue(f) with
            | true, newFld -> 
              let ec = {c with Type = PhysPtr(f.Type)} // TODO Ptr kind
              match subtractOffsets (f.Offset) (newFld.Offset) |> (toBitFieldOffset newFld.Type.SizeOf) with
                | BitField(0, start, size) -> 
                  match bv_extrAndPad ec (Expr.MkDot(c, (self e), newFld)) start (start+size) with
                    | Macro(_, name, [e; bvSize; bvStart; bvEnd]) when name.StartsWith("pullout_bv_extract") ->
                      Some(Macro(c, "vs_updated_bv", [e; bvSize; bvStart; bvEnd; self expr]))
                    | _ -> die()
                | _ -> die()
            | false, _ -> None
        | Dot (c, e, f) as expr ->
          match fieldsToReplace.TryGetValue(f) with
            | true, newFld -> 
              let ec = {c with Type = PhysPtr(f.Type)} // TODO Ptr kind
              match subtractOffsets (f.Offset) (newFld.Offset) |> (toBitFieldOffset newFld.Type.SizeOf) with
                // this will create 'pullout' expressions, which will be normalized in the subsequent union flattening step
                | BitField(0, start, size) -> Some(bv_extrAndPad ec (Expr.MkDot(c, (self e), newFld)) start (start+size))
                | _ -> die()
            | false, _ -> None
        | _ -> None

      decls |> List.iter processTypes
      decls |> deepMapExpressions replExpr
    
    // ============================================================================================================
    
    (*
        struct X {
          int a;
          struct {
            int b;
            int c;
          };
          int d;
        }
        
        The inner struct is unfolded into X.
        
        TODO: make the dummy struct declaration created for inner struct go away.
     *)

    let removedNestedAnonymousTypes decls = 

      let fields = new Dict<Field,Field>()
      let fieldsToRemove = new HashSet<Field>()
      let processedTypeDecls = new HashSet<TypeDecl>()
      let id = ref 0
      let unnamedFieldId = ref 0
    
      let rec processTypeDecl = function
        | td -> 
          if processedTypeDecls.Add td then
            let rec processType = function
              | Type.Ref(td) -> processTypeDecl td
              | Array (t, _) -> processType t
              | _ -> ()
            let trField (f:Field) =
              processType f.Type
              match f.Type with 
                | Type.Ref td' when f.Name = "" && td'.IsNestedAnon && ((td.Kind = Struct && td'.Kind = Struct) || td'.Fields.Length <= 1) ->
                  fieldsToRemove.Add f |> ignore
                  [for f' in td'.Fields -> 
                     let newf' =
                       { f' with Offset = addOffsets (f'.Offset) (f.Offset);
                                 Parent = td; 
                                 Name = f'.Name + "#nest" + (!id).ToString () }
                     incr id
                     fields.Add (f', newf')
                     newf'
                  ]
                | _ -> [f]
            let nameNonameFields (fld:Field) =
              if fld.Name = "" then                    
                fld.Name <- "unnamed#" + (!unnamedFieldId).ToString() 
                incr unnamedFieldId
              fld

            let newFields = td.Fields |> List.map trField |> List.concat |> List.map nameNonameFields
            td.Fields <- newFields
      
      let nameFieldsByMemberName td =
        let nameFieldByMemberName (f:Field) =
          match f.Name, f.Type with
            | "", Type.Ref(td') ->
              let rec findMemberNames acc = function
                | [] -> List.rev acc
                | CustomAttr.VccAttr(AttrMemberName, name) :: attrs -> findMemberNames (name :: acc) attrs
                | _ :: attrs -> findMemberNames acc attrs
              match findMemberNames [] td'.CustomAttr with
                | [] -> ()
                | [name] -> f.Name <- name; td'.IsNestedAnon <- false
                | _ -> helper.Error(f.Token, 9695, "More than one member_name for field")
            | _ -> ()
        List.iter nameFieldByMemberName td.Fields

      for d in decls do
        match d with
          | Top.TypeDecl td -> nameFieldsByMemberName td
          | _ -> ()
       
      for d in decls do
        match d with
          | Top.TypeDecl td -> processTypeDecl td
          | _ -> ()
      
      let replFields self = function
        | Dot (c, Macro (_, "&", [Deref (_, e)]), f) -> Some (self (Dot (c, e, f)))
        | Dot (c, Dot (_, e, f'), f) when fields.ContainsKey f && fieldsToRemove.Contains f' ->
          Some (self (Dot (c, e, f)))
        | Dot (c, e, f) ->
          if fieldsToRemove.Contains f then die()
          match fields.TryGetValue f with
            | (true, sField) -> Some (self (Dot (c, e, sField)))
            | (false, _) -> None
        | _ -> None
 
      decls |> deepMapExpressions replFields 

    // ============================================================================================================

    let inlineFieldsByRequest decls =
      let processedTypeDecls = new HashSet<TypeDecl>()
      let inlinedFields = new Dict<Field, (Field * Field) list>()
      let inlinedArrays = new Dict<Field, Field>()
      let (dotAxioms : Top list ref) = ref []

      let mkBogusEC t = { bogusEC with Type = t }
      
      let genDotAxioms (td : TypeDecl) (oldField: Field) (newFields : Field list) =
        let genDotAxiom (oldSubField : Field) (newField : Field) =
          let varType = PhysPtr(Type.Ref(td)) // TODO Ptr kind - we need these axioms to hold for both physical and spec 
          let var = Variable.CreateUnique "p" varType QuantBound
          let varref = Ref(mkBogusEC varType, var)
            
          let left = Expr.MkDot(Cast(mkBogusEC (PhysPtr(oldField.Type)), Unchecked, Expr.MkDot(varref, newFields.Head)), oldSubField) // TODO Ptr kind
          let right = Expr.MkDot(varref, newField)
          GeneratedAxiom(Quant(mkBogusEC Bool, { Kind = Forall 
                                                 Variables = [var] 
                                                 Triggers = [[left]] 
                                                 Condition = None 
                                                 Body = Prim(mkBogusEC Bool, Op("==", Unchecked), [left; right]) 
                                                 Weight = "c-dot-inline-axiom"
                                                 }), Top.TypeDecl(td))
        let oldFieldTypeDecl = 
          match oldField.Type with
            | Type.Ref(td) -> td
            | _ -> die()
        List.map2 genDotAxiom (oldFieldTypeDecl.Fields) newFields
        
      let genInlinedArrayAxiom td elemType (newFields : Field list) =
        let var = Variable.CreateUnique "p" ObjectT QuantBound
        let varref = Ref(mkBogusEC ObjectT, var)
        let mkInstantiatePtr (f : Field) = Macro(mkBogusEC Bool, "instantiate_ptr", [Expr.MkDot(varref, f)])
        let mkAnd e1 e2 = Expr.Prim(mkBogusEC Bool, Op("&&", Unchecked), [e1; e2])
        let instExpr = List.fold mkAnd (mkInstantiatePtr newFields.Head) (List.map mkInstantiatePtr (newFields.Tail))
        let ec = mkBogusEC elemType
        let trigger = Macro(ec, "_vcc_inlined_array", [Dot(ec, varref, newFields.Head)])
        GeneratedAxiom(Quant(mkBogusEC Bool, { Kind = Forall 
                                               Variables = [var] 
                                               Triggers = [[trigger]] 
                                               Condition = None 
                                               Body = instExpr 
                                               Weight = "c-array-inline-axiom"
                                               }), Top.TypeDecl(td))
          
      let rec processTypeDecl = function
        | td ->
          if processedTypeDecls.Add td then
            let rec processType = function
                | Type.Ref(td) -> processTypeDecl td
                | Array (t, _) -> processType t
                | _ -> ()
            let trField (f:Field) =
              processType f.Type
              if (not (hasCustomAttr "inline" f.CustomAttr)) then [f] else
                match f.Type with 
                  | Type.Ref td' when ((td.Kind = Struct && td'.Kind = Struct) || td'.Fields.Length <= 1) ->
                    let newFields = 
                      [for f' in td'.Fields -> 
                         let newf' =
                           { f' with Offset = 
                                        match f'.Offset with
                                          | Normal n -> Normal (n + f.ByteOffset)
                                          | BitField (n, b, s) -> BitField (n + f.ByteOffset, b, s)
                                        ;
                                     Parent = td; 
                                     Name = "inline#" + f.Name + "#" + f'.Name }
                         newf'
                      ]
                    inlinedFields.Add(f, List.zip td'.Fields newFields)
                    dotAxioms := !dotAxioms @ (genDotAxioms td f newFields)
                    newFields
                  | Type.Array(Type.Ref td', n) when td.Kind = Struct ->
                    let mkFieldForIndex i =
                      [ for f' in td'.Fields ->
                        { f' with Offset = 
                                     match f'.Offset with
                                       | Normal n -> Normal (n + f.ByteOffset + i * td'.SizeOf)
                                       | BitField (n,b,s) -> BitField (n + f.ByteOffset + i * td'.SizeOf, b, s)
                                     ;
                                  Parent = td;
                                  Name = f.Name + "#" + f'.Name + "#" + i.ToString() }
                      ]
                    let newFields = [ for i in seq { 0 .. n-1 } -> mkFieldForIndex i ] |> List.concat
                    inlinedArrays.Add(f, newFields.Head)
                    dotAxioms := (genInlinedArrayAxiom td (Type.MkPtrToStruct(td')) newFields) :: !dotAxioms
                    newFields
                  | _ -> 
                    helper.Warning(f.Token, 9109, "field '" + f.Name + "' could not be inlined")
                    [f] 
            td.Fields <- td.Fields |> List.map trField |> List.concat 

      for d in decls do
        match d with 
          | Top.TypeDecl td -> processTypeDecl td
          | _ -> ()
      
      let replFields self = function
        | Dot (c, Macro (_, "&", [Deref (_, e)]), f) -> Some (self (Dot (c, e, f)))
        | Dot (c, (Dot(c', e, f') as dot'), f) ->
          let fAfterInlining = 
            match self (Dot(c, Macro(c', "bogus_for_inlining", []), f)) with
              | Dot(_,_, fAfterInlining) -> fAfterInlining
              | _ -> f
          match inlinedFields.TryGetValue(f') with
            | false, _ -> None
            | true, fields -> 
              match _try_assoc fAfterInlining fields with
                | Some field -> Some(self (Dot(c, e, field)))
                | None -> die()
        | Dot (c, e, f) as expr ->
          match inlinedFields.TryGetValue(f) with
            //| true, [(_, f')] -> Some (self (Dot({c with Type = Ptr(f'.Type) }, e, f')))
            | true, _ -> helper.Error(expr.Token, 9679, "Field '" + f.Name + "' has been inlined and cannot be referred to as such; refer to its nested fields instead"); None
            | false, _ -> 
              match inlinedArrays.TryGetValue(f) with
                | true, f' -> Some (self (Macro(c, "_vcc_inlined_array", [Dot(c, e, f')])))
                | _ -> None
         | _ -> None

      (decls |> deepMapExpressions replFields) @ !dotAxioms
  
    // ============================================================================================================
         
    let turnSingleMemberUnionsIntoStructs decls =
    
      let atMostOneNonspecField =
        let rec atMostOneNonspecField' found = function
          | [] -> true
          | (fld : Field) :: flds when fld.IsSpec -> atMostOneNonspecField' found flds
          | _ :: flds when not found -> atMostOneNonspecField' true flds // first found
          | _ -> false // second found
        atMostOneNonspecField' false
    
      for d in decls do
        match d with 
          | TypeDecl td when td.Kind = TypeKind.Union && atMostOneNonspecField td.Fields -> td.Kind <- Struct
          | _ -> ()
      decls
      
    // ============================================================================================================
    
    // TODO
    // remark: not quite sure we need that                
    /// Replace structs/unions smaller than 64-bit with integers (or longs).
    (* E.g.    
         union U {
           struct {
             INT32 i1;
             INT32 i2;
           }
           UINT64 AsUINT64;
         }
       
       Then U should be replaced with UINT64 and field accesses on U should be
       replaced with bit operators.
       
       union U *u;
       
       u->i2 ====> Macro("bv_extract", [*u; 32; 64])
       
       
       Later:       
       
         Macro("bv_extract", [p->f; x; y]) = e'  ====>
           tmp = p
           tmp->f = Macro("bv_concat", [Macro("bv_extract", [tmp->f; 0; x]);
                                        Macro("bv_extract", [e'; 0; y-x]);
                                        Macro("bv_extract", [tmp->f; y; 8*sizeof(p->f)])])
    
      The other (simpler) option, just translate:
      
        union U {
          T f1;
          T f2;
          ...
          T fN;
        }
        
      into T (this includes the case when N==1).
    *)
    let removeSmallStructs (decls:list<Top>) = decls
    
    // ============================================================================================================
    
    let handleStructAndRecordEquality self expr =
      let rec markTypeDecl eqKind (td : TypeDecl) =
        match td.GenerateEquality, eqKind with
          | (NoEq | ShallowEq), DeepEq  -> 
            td.GenerateEquality <- eqKind
            List.iter (markField eqKind) td.Fields
          | (NoEq | ShallowEq), ShallowEq when td.Kind = TypeKind.Union  -> 
            td.GenerateEquality <- eqKind
            List.iter (markField eqKind) td.Fields
          | DeepEq , ShallowEq -> ()
          | _ -> 
            assert (eqKind <> NoEq)
            td.GenerateEquality <- eqKind
      and markField eqKind (f : Field) =
        match f.Type with
        | Type.Ref td -> markTypeDecl eqKind td
        | _ -> ()
      
      match expr with
        | Expr.Macro(c, (("_vcc_deep_struct_eq" | "_vcc_shallow_struct_eq") as name), ([e1;e2] as args)) ->
          let eqKind = if name = "_vcc_deep_struct_eq" then DeepEq else ShallowEq
          match e1.Type with
          | Type.Ref(td) as t ->
            setEqualityKind td eqKind
            Some(Expr.Macro(c, name + "." + td.Name, [self e1; self e2]))
          | _ -> 
            helper.Error(c.Token, 9655, "structured equality applied to non-structured type " + e1.Type.ToString(), None)
            None
        | Expr.Prim(ec, Op("==",_), [e1; e2]) ->
          match e1.Type with
            | Type.Ref(td) when td.IsRecord -> Some(self (Expr.Macro(ec, "_vcc_rec_eq", [e1; e2])))
            | _ -> None
        | _ -> None

    // ============================================================================================================

    let removeVolatileInvariants decls = 
      for d in decls do
        match d with  
          | Top.TypeDecl(td) ->
            td.Invariants <- 
              td.Invariants |> 
              List.choose (function | Macro(_, "labeled_invariant", [Macro(_, "volatile", []); inv]) -> None | inv -> Some inv)
          | _ -> ()

      decls
    
    // ============================================================================================================

    
    let handleVolatileModifiers decls =
    
      let fldToVolatileFld = new Dict<_,_>()
      let initialFldToVolatileFld = new Dict<_,_>()
      let volatileVars = new Dict<Variable,Variable>()
      let volatileTds = ref []
      let typeToVolatileType = new Dict<_,_>()
    
      let rec mkVolFld td (f : Field) = 
        let f' = 
          match f.Type with
            | Array(Type.Ref({Kind = Struct|Union} as tdRef), size) when not tdRef.IsRecord->
              { f with Type = Array(Type.Ref(mkVolTd tdRef), size); Parent = td }
            | Type.Ref({Kind = Struct|Union} as tdRef) when not tdRef.IsRecord ->
              { f with Type = Type.Ref(mkVolTd tdRef);  Parent = td }
            | _ -> { f with IsVolatile = true; Parent = td}
        fldToVolatileFld.Add(f,f')
        f'

      and mkVolTd (td : TypeDecl) =
      
        let fixFields oldFields newFields =
          let fieldSubst = new Dict<Field,Field>()
          List.iter2 (fun oldF newF -> fieldSubst.Add(oldF, newF)) oldFields newFields
          
          let subsFields self = function
            | Dot(ec, expr, f) ->
              match fieldSubst.TryGetValue(f) with
                | (true, f') -> Some(Expr.MkDot(ec, self expr, f'))
                | _ -> None
            | _ -> None
          subsFields      
          
        let retypeThis oldTd newTd self = function
          | Expr.This({Type = PtrSoP(Type.Ref(oldType), isSpec)} as c) ->
              Some (Expr.This( { c with Type = Type.MkPtr(Type.Ref(newTd), isSpec) }))
          | _ -> None
      
        match typeToVolatileType.TryGetValue(td) with
          | true, td' -> td'
          | false, _ ->
            let td' = { td with Name = "volatile#" + td.Name; 
                                IsVolatile = true; 
                                CustomAttr = CustomAttr.VccAttr(AttrVolatileOwns, "") :: td.CustomAttr }
            typeToVolatileType.Add(td, td')
            typeToVolatileType.Add(td', td')
            let vFields = List.map (mkVolFld td') td'.Fields
            td'.Invariants <- 
              td'.Invariants |>
              List.choose (function | Macro(_, "labeled_invariant", [Macro(_, "volatile", []); inv]) -> Some inv | _ -> None) |>
              List.map (fun (expr:Expr) -> expr.SelfMap(retypeThis td td').SelfMap (fixFields td'.Fields vFields)) 
            td'.Fields <- vFields
            volatileTds := td' :: !volatileTds
            pushDownOne false td'  
            td'
        
      and pushDownOne initial (td : TypeDecl) =
        let pdo (f:Field) =
          match f.Type with
            | Type.Ref({Kind = Struct|Union} as td) when f.IsVolatile && not td.IsRecord ->
              let td' = mkVolTd td
              let f' = {f with IsVolatile = false; Type = Type.Ref(td')}
              if initial then initialFldToVolatileFld.Add(f, f')
              f'
            | PtrSoP(Type.Volatile((Type.Ref({Kind = Struct|Union} as td))), isSpec) ->
              let td' = mkVolTd td
              let f' = {f with Type = Type.MkPtr(Type.Ref(td'), isSpec)}
              initialFldToVolatileFld.Add(f, f')
              f'
            | Type.Array(Type.Volatile((Type.Ref({Kind = Struct|Union} as td))), size) ->
              let td' = mkVolTd td
              let f' = {f with Type = Type.Array(Type.Ref(td'), size)}
              initialFldToVolatileFld.Add(f, f')
              f'
            | Type.Array(Type.Ref({Kind = Struct|Union} as td), size) when f.IsVolatile ->
              let td' = mkVolTd td
              let f' = {f with Type = Type.Array(Type.Ref(td'), size); IsVolatile=false}
              initialFldToVolatileFld.Add(f, f')
              f'
            | Type.Array(Type.Volatile(t), size) ->
              let f' = {f with Type = Type.Array(t, size); IsVolatile=true}
              initialFldToVolatileFld.Add(f, f')
              f'
            | PtrSoP(Type.Volatile(t), isSpec) ->
              if initial then
                helper.Warning(f.Token, 9114, "volatile specifier for pointers to primitive types are currently ignored")
              let f' = {f with Type = Type.MkPtr(t, isSpec) }
              initialFldToVolatileFld.Add(f, f')
              f'
            | _ -> f
        // if typeToVolatileType.ContainsKey(td)  then () 
        td.Fields <- List.map pdo td.Fields
        
      let rec typeShouldBePropagated = function
        | Type.Ref(td) when td.IsVolatile -> true
        | Ptr(t) -> typeShouldBePropagated t
        | Type.Array(t, _) -> typeShouldBePropagated t
        | _ -> false
        
      let subsFields self = function
        | VarDecl(ec, v, _) ->
          match volatileVars.TryGetValue(v) with
            | true, v' -> Some(VarDecl(ec, v', []))
            | _ -> None
        | Expr.Ref(ec, v) ->
          match volatileVars.TryGetValue(v) with
            | true, v' -> Some(Expr.Ref({ec with Type = v'.Type}, v'))
            | _ -> None
        | Dot(ec, expr, f) ->
          match initialFldToVolatileFld.TryGetValue(f) with
            | true, f' -> Some(Expr.MkDot(ec, self expr, f'))
            | false, _ ->
              let (expr' : Expr) = self expr
              match expr'.Type with
                | Ptr(Type.Ref({IsVolatile = true})) ->
                  match fldToVolatileFld.TryGetValue(f) with
                    | true, f' -> Some(Expr.MkDot(ec, expr', f'))
                    | false, _ -> Some(Dot(ec, expr', f))
                | _ -> Some(Dot(ec, expr', f))

        // for the above to work as expected, we need to propagate volatile type information outward
  
        | Index(ec, expr, idx) -> 
          let se = self expr
          let si = self idx
          if typeShouldBePropagated se.Type then
            let t = match se.Type with | Ptr(Array(t, _)) -> PhysPtr(t) | t -> t
            Some(Index({ec with Type = t}, se, si))
          else
            Some(Index(ec, se, si))
        | Deref(ec, expr) ->
          let se = self expr
          if typeShouldBePropagated se.Type then
            match se.Type with
              | Ptr(t) -> Some(Deref({ec with Type = t}, se))
              | _      -> Some(Deref(ec, se))
          else 
            Some(Deref(ec, se))
        | Macro(ec, "&", [expr]) ->
          let se = self expr
          if typeShouldBePropagated se.Type then
            let isSpec = match ec.Type with | SpecPtr _ -> true | _ -> false
            Some(Macro({ec with Type = Type.MkPtr(se.Type, isSpec)}, "&", [se]))
          else
            Some(Macro(ec, "&", [se]))
        | Pure(ec, expr) ->
          let se = self expr
          if typeShouldBePropagated se.Type then
            Some(Pure({ec with Type = se.Type}, se))
          else
            Some(Pure(ec, se))
        | _ -> None
      
      let typeSubst = new Dict<Type, Type>()

      let findVolatileTypes self (expr : Expr) =
        match expr.Common.Type with
          | PtrSoP(Volatile(Type.Ref(td)), isSpec) -> 
            typeSubst.[expr.Common.Type] <- Type.MkPtr(Type.Ref(mkVolTd td), isSpec); true
          | _ -> true
       
      do deepVisitExpressions findVolatileTypes decls

      let typeMap t = 
        match typeSubst.TryGetValue t with
          | true, t' -> Some t'
          | false, _ -> None
        
      let decls = deepMapExpressions (fun _ (expr : Expr) -> Some(expr.SubstType(typeMap, new Dict<Variable, Variable>()))) decls

      for d in decls do
        match d with
          | Top.TypeDecl(td) -> pushDownOne true td
          | Top.FunctionDecl({Body = Some(body)} as fn) ->

            let mkVolatileType = function
              | PtrSoP(Volatile(Type.Ref(td)), isSpec) -> 
                let td' = mkVolTd td
                Some(Type.MkPtr(Type.Ref(td'), isSpec || td'.IsSpec))
              | PtrSoP(Volatile(t), isSpec) ->
                Some(Type.MkPtr(t, isSpec))
              | _ -> None
            let mkVolatileVar (v:Variable) =
              match mkVolatileType v.Type with
                | Some t' ->
                  let v' = { v with Type = t' }
                  volatileVars.Add(v, v')
                  v'
                | _ -> v
            let pdLocalDecls self = function
              | VarDecl(_, v, _) when v.Kind <> VarKind.Parameter && v.Kind <> VarKind.SpecParameter && v.Kind <> VarKind.OutParameter -> 
                mkVolatileVar v |> ignore; false
              | _ -> true
            fn.Parameters <- List.map mkVolatileVar fn.Parameters
            do match mkVolatileType fn.RetType with
                | None -> ()
                | Some t' -> fn.RetType <- t' // TODO: might require retyping of 'result' in contracts            
            body.SelfVisit pdLocalDecls
          | Top.Global({Type = Type.Volatile(Type.Ref(td))} as v, _) ->
            let td' = mkVolTd td
            volatileVars.Add(v, {v with Type = Type.Ref(td')})
          | _ -> ()
          
      decls @ (List.map (fun td -> Top.TypeDecl(td)) !volatileTds) |> deepMapExpressions subsFields
    
    // ============================================================================================================

    let assignSingleFieldStructsByField self = function
      | Macro(ec, "=", [dst; src])  ->
        match dst.Type with
          | Type.Ref({Fields = [fld]} as td) when not td.IsRecord &&  not (hasCustomAttr "inline" fld.CustomAttr) ->
            let addDot (e:Expr) = 
              let isSpecRef = function | Ref(_, {Kind = SpecLocal|SpecParameter|OutParameter}) -> true | _ -> false
              Deref({e.Common with Type = fld.Type}, Expr.MkDot(Macro({e.Common with Type = Type.MkPtr(e.Type, isSpecRef e)}, "&", [e]), fld))
            Some(Macro(ec, "=", [addDot dst; addDot src]))
          | _ -> None
      | _ -> None
            
    // ============================================================================================================

    let addAxiomsForGlobals decls = 
      let addAxiomsForGlobals' = function
        | Global({Type = Array(t, n); Kind = ConstGlobal} as v, Some(init)) -> 
          let ec_b = {bogusEC with Type = Bool }
          let ec_t = {bogusEC with Type = t }
          let ec_ptr = {bogusEC with Type = PhysPtr(t)}
          let readAxioms =
            let rec readAxiom n = function
              | [] -> []
              | expr :: exprs ->
                let ax = Top.GeneratedAxiom(Expr.Prim(ec_b, 
                                             Op("==", Unchecked), 
                                             [
                                               Expr.Deref(ec_t, Expr.Index(ec_ptr, Expr.Macro(ec_ptr, "&", [Expr.Ref(ec_t, v)]), mkInt n));
                                               expr
                                             ]), Top.Global(v, None)) 
                ax :: (readAxiom (n+1) exprs)
            function 
              | Expr.Macro(_, "init", initializers) -> readAxiom 0 initializers
              | _ -> die()

          let axBody pref = Expr.Macro(ec_b, "_vcc_is_thread_local_array", pref @ [Expr.Macro(ec_ptr, "&", [Expr.Ref(ec_t, v)]); mkInt n])

          let threadLocalAxiom =
            let stateVar = Variable.CreateUnique "__vcc_state" Type.MathState VarKind.QuantBound
            let stateRef = Expr.Ref ({ bogusEC with Type = stateVar.Type }, stateVar)
            let goodState = Expr.Macro (boolBogusEC(), "prelude_good_state", [stateRef])
            let qd =
              {
                Kind = QuantKind.Forall
                Variables = [stateVar]
                Triggers = [[goodState]]
                Condition = Some goodState
                Body = axBody [stateRef]
                Weight = "c-global-always-good"
              } : QuantData
            Top.GeneratedAxiom(Expr.Quant (boolBogusEC(), qd), Top.Global(v,None))
          Global (v, None) :: threadLocalAxiom :: (readAxioms init) 
        | Global ({Kind = VarKind.ConstGlobal} as v, Some init) when not init.Type.IsComposite -> [Global (v, None)] // the initial value is handled by FELT in the AST
        | Global (v, Some(init)) when v.Type._IsInteger || v.Type._IsPtr ->
          let state = Variable.CreateUnique "#s" Type.MathState VarKind.QuantBound
          let stateRef = Expr.Ref({bogusEC with Type = Type.MathState}, state)
          let ec_t = {bogusEC with Type = v.Type}
          let programEntryState = Macro(boolBogusEC(), "_vcc_program_entry_point", [stateRef])
          let readAtEntry = Expr.Old(ec_t, stateRef, Expr.Ref(ec_t, v))
          let readCondition = Expr.Quant(boolBogusEC(), { Kind = QuantKind.Forall                                                 
                                                          Variables = [state]
                                                          Triggers = [[readAtEntry; programEntryState]]
                                                          Condition = Some(programEntryState)
                                                          Body = Expr.Prim(boolBogusEC(), Op("==", Unchecked), [readAtEntry; init])
                                                          Weight = "c-global-initial-value"
                                                          })
          Global (v, None) :: Top.GeneratedAxiom(readCondition, Top.Global(v, None)) :: []         
        | Global (v, Some(init)) -> 
          helper.Warning(init.Token, 9112, "unhandled initializer")
          [Global(v, None)]
        | other -> [other]
        
        
      decls |> List.map addAxiomsForGlobals' |> List.concat

    // ============================================================================================================

    let checkRecordValidity decls =
      
      let checkDecl (td : TypeDecl) =
      
        if (td.Invariants.Length > 0) then
          helper.Error(td.Token, 9698, "type '" + td.Name + "' is marked as a record type and thus must not declare invariants", Some(td.Invariants.Head.Token))
        
        if (td.Kind = TypeKind.Union) then
          helper.Error(td.Token, 9682, "union '" + td.Name + "' cannot be flattened into a struct and thus cannot be marked as record type")
        else 
          let checkType tok loc tp =
            let rec checkType = function
              | Type.Ref(td') when not td'.IsMathValue ->
                helper.Error(tok, 9680, loc() + " cannot be of non-record structured type '" + td'.Name + "'", Some(td'.Token))
              | Type.Volatile _ -> helper.Error(tok, 9683, "volatile modifier on " + loc() + " is currently not supported")
              | Type.Array _ -> helper.Error(tok, 9688, "inline array in " + loc() + " is currently not supported")
              | _ -> ()
            checkType tp

          let checkField (f:Field) =
            checkType f.Token (fun () -> "field '" + f.Name + "' of record type '" + td.Name + "'") f.Type
            // we now automatically mark them all as spec
            //if (f.IsSpec) then helper.Warning(f.Token, 9118, "field '" + f.Name + "' in record type does not need to marked as spec field")
          
          let checkCtor (f:Function) =
            f.Parameters |> List.iter (fun v -> checkType f.Token (fun () -> "parameter of constructor '" + f.Name + "'") v.Type)

          List.iter checkField td.Fields
          List.iter checkCtor td.DataTypeOptions
      
      for d in decls do
        match d with
          | Top.TypeDecl td when td.IsRecord -> checkDecl td
          | _ -> ()

      decls

    // ============================================================================================================

    let flattenNestedArrays decls = 
    
      // compile nested, fixed-size arrays into flat arrays and re-write arrays accesses accordingly
      // e.g.: int a[5][7] -> int a[35]; and
      //           a[i][j] -> a[7*i + j]
    
      let varSubst = new Dict<Variable, Variable>()
      let fieldSubst = new Dict<Field, (Field * Type)>()
      let rec flatten = function
        | Array(t, sz) -> 
          let (t', sz') = flatten t
          (t', sz * sz')
        | t -> (t,1)
      let flattenNestedArrays' self = function
      | VarDecl(ec, v, attr) ->
        // re-type local variable
        match v.Type with
          | PtrSoP(Array _ as arr, isSpec) -> 
            let (elType, _) = flatten arr
            let v' = Variable.CreateUnique v.Name (Type.MkPtr(elType, isSpec)) v.Kind
            varSubst.Add(v, v')
            Some(VarDecl(ec, v', attr))
          | _ -> None
      | Ref(ec, v) ->
        // fix-up references to locals
        match varSubst.TryGetValue v with
          | true, v' -> Some(Ref({ec with Type = v'.Type}, v'))
          | _ -> None
      | Index(ec, Macro(_, "&", [Deref(_, e)]), idx) ->
        // fold nested Index operations
        match e.Type with 
          | PtrSoP(Array(t,sz), isSpec) ->
            let sidx = self idx
            match self e with
              | Index(ec', e', idx') as e-> 
                // found nested index operation; replace with single one
                Some(Index({ec with Type = Type.MkPtr(t, isSpec)}, e', 
                           Prim(sidx.Common, Op("+", Processed), [Prim(sidx.Common, Op("*", Processed), [idx'; mkInt sz]); sidx])))
              | e -> Some(Index(ec, e, sidx))
          | _ -> None
      | Cast(ec, cs, Call(aec, ({Name = "_vcc_stack_alloc"} as fn), [arr], args)) ->
        // fix the stack_alloc call for stack-allocated arrays
        let (elType, sz) = flatten arr
        Some(Cast({ec with Type = Type.RetypePtr(ec.Type, elType)}, cs, Call(aec, fn, [Array(elType, sz)], args)))
      | Dot(ec, e, f) ->
        // fix-up accesses to fields of nested-array types; the map has been populated for all types by calling 'flattenField' below
        match fieldSubst.TryGetValue f with
          | true, (f', elType) -> 
            let res = Some(Expr.MkDot(self e, f'))
            res
          | _ -> None
      | _ -> None
      
      let flattenFields (f:Field) =
        match f.Type with 
          | Array(Array(_, _), _) as arr -> 
            let (elType, sz) = flatten arr
            let f' = { f with Type = Array(elType, sz) }
            fieldSubst.Add(f, (f', elType))
            f'
          | _ -> f
      
      for d in decls do
        match d with 
          | Top.TypeDecl(td) -> td.Fields <- List.map flattenFields td.Fields
          | _ -> ()
      
      deepMapExpressions flattenNestedArrays' decls
      
    // ============================================================================================================

    let handlePrimitiveStructs decls =

      let primMap = Dict<TypeDecl,Type>()
      let fieldsToRemove = HashSet<Field>()

      // find types marked _(primitive), report errors for those that are invalidly maked so
      // an prepare to replace the legally marked ones

      for d in decls do
        match d with
          | Top.TypeDecl(td) when hasCustomAttr AttrPrimitive td.CustomAttr ->

            let reportError reason = helper.Error(td.Token, 9741, "type '" + td.Name + "' " + reason + " and thus cannot be marked 'primitive'", None)

            match td.Fields with
              | [fld] ->
                if fld.Type.IsComposite then
                  reportError ("has field of non-primitive type '" + fld.Type.ToString() + "'")
                elif td.Invariants.Length > 0 then
                  reportError "has invariants"
                else
                  primMap.Add(td, fld.Type)
                  fieldsToRemove.Add fld |> ignore
              | _ -> reportError "has more than one field"
            ()
          | _ -> ()

      let typeMap = function
        | Type.Ref(td) ->
          match primMap.TryGetValue td with 
            | true, t' -> Some t'
            | false, _ -> None
        | _ -> None

      // fixup function signatures and fields and collect the substitutions

      let paramSubst = new Dict<Variable, Variable>()
      let fieldSubst = new Dict<Field, Field>()

      for d in decls do
        match d with
          | Top.FunctionDecl(fn) -> 
            let retypeParameter (p : Variable) =
              match p.Type.Subst(typeMap) with
                | None -> p
                | Some t' -> 
                  let p' = { p.UniqueCopy() with Type = t'}
                  paramSubst.Add(p, p')
                  p'
            fn.Parameters <- List.map retypeParameter fn.Parameters
            fn.RetType <- match fn.RetType.Subst(typeMap) with
                           | None -> fn.RetType
                           | Some t' -> t'
          | Top.TypeDecl(td) ->
            let retypeField (fld:Field) =
              match fld.Type.Subst(typeMap) with
                | None -> fld
                | Some t' ->
                  let fld' = { fld with Type = t' }
                  fieldSubst.Add(fld, fld')
                  fld'
            td.Fields <- List.map retypeField td.Fields
          | _ -> ()

            
      // remove the extra dots and substitute the types

      let removeAndReplaceFields self = function
        | Dot(_, expr, fld) when fieldsToRemove.Contains fld -> Some(self expr)
        | Dot(_, expr, fld) ->
          match fieldSubst.TryGetValue fld with
            | true, fld' -> Some(Expr.MkDot(self expr, fld'))
            | false, _ -> None
        | _ -> None

      let substTypes _ (expr :Expr) = Some(expr.SubstType(typeMap, paramSubst))

      decls |> deepMapExpressions removeAndReplaceFields |> deepMapExpressions substTypes

    // ============================================================================================================

    helper.AddTransformer ("type-begin", TransHelper.DoNothing)
    helper.AddTransformer ("type-function-pointer", TransHelper.Decl handleFunctionPointers)
    helper.AddTransformer ("type-flatten-arrays", TransHelper.Decl flattenNestedArrays)
    helper.AddTransformer ("type-groups", TransHelper.Decl liftGroups)
    helper.AddTransformer ("type-mark-nested", TransHelper.Decl markNestedAnonymousTypes)
    helper.AddTransformer ("type-remove-bitfields", TransHelper.Decl removeBitfields)
    helper.AddTransformer ("type-flatten-unions", TransHelper.Decl flattenUnions)
    helper.AddTransformer ("type-remove-nested", TransHelper.Decl removedNestedAnonymousTypes)
    helper.AddTransformer ("type-fixup-single-member-unions", TransHelper.Decl turnSingleMemberUnionsIntoStructs)
    helper.AddTransformer ("type-assign-by-single-field", TransHelper.Expr assignSingleFieldStructsByField)
    helper.AddTransformer ("type-inline-fields", TransHelper.Decl inlineFieldsByRequest)
    helper.AddTransformer ("type-fixup-single-member-unions", TransHelper.Decl turnSingleMemberUnionsIntoStructs)
    helper.AddTransformer ("type-primitive-structs", TransHelper.Decl handlePrimitiveStructs)
    helper.AddTransformer ("type-check-records", TransHelper.Decl checkRecordValidity)
    helper.AddTransformer ("type-volatile-modifiers", TransHelper.Decl handleVolatileModifiers)
    helper.AddTransformer ("type-remove-volatile-invariants", TransHelper.Decl removeVolatileInvariants)
    helper.AddTransformer ("type-struct-equality", TransHelper.Expr handleStructAndRecordEquality)
    helper.AddTransformer ("type-globals", TransHelper.Decl addAxiomsForGlobals)
    helper.AddTransformer ("type-end", TransHelper.DoNothing)
