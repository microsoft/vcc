//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.CAST
 open Microsoft.Research.Vcc.Util

 module TransUtil =

  let rec last = function
    | [x] -> x
    | _ :: xs -> last xs
    | [] -> die()

  let splitLast l = 
    let rec loop acc = function
      | [] -> die()
      | [x] -> x, List.rev acc
      | x::xs -> loop (x::acc) xs
    loop [] l
 
  let removeDuplicates l =
    let elements = new HashSet<_>()
    let rec loop = function
      | [] -> []
      | x::xs -> if elements.Add x then x :: loop xs else loop xs
    loop l

  let ignoreEffects e =
    let aux self = function 
      | Block (_, stmts, _) ->
        Some (self (last stmts))
      | _ -> None
    (e:Expr).SelfMap aux 
    
  let propAssert id msg name p =
    let p = ignoreEffects p
    Expr.MkAssert (Expr.Macro (afmte id msg [p], name, [p]))

  let addSuffix tok getsuff =
    forwardingToken tok None (fun () -> tok.Value + " " + getsuff())
    
  // -----------------------------------------------------------------------------
  // Expression patterns (move to CAST.fs?)
  // ----------------------------------------------------------------------------- 

  let (|EString|_|) = function
    | Expr.Macro (c, "string", [UserData(_, o)])
    | Expr.Macro (c, "&", [Expr.Macro (_, "string", [UserData(_, o)])]) -> Some (c, (string)o)
    | _ -> None
                 
  let (|CallMacro|_|) = function
    | Call (ec, { Name = name }, targs, args) -> Some (ec, name, targs, args)
    | Macro (ec, name, args) -> Some (ec, name, [], args)
    | _ -> None
  
  let (|AssertAssume|_|) = function
    | Assume (ec, e) -> Some (ec, e)
    | Assert (ec, e, _) -> Some (ec, e)
    | _ -> None

  let (|BoolOp|_|) = function
    | Expr.Macro (c, "ite", [e1; e2; EFalse]) -> Some (BoolOp (c, "&&", e1, e2))
    | Expr.Macro (c, "ite", [e1; ETrue; e2]) -> Some (BoolOp (c, "||", e1, e2))
    | Expr.Macro (c, "ite", [e1; e2; ETrue]) -> Some (BoolOp (c, "==>", e1, e2))
    | Expr.Prim (c, Op (op, _), [e1; e2]) -> Some (BoolOp (c, op, e1, e2))
    | _ -> None
      
  let (|COld|_|) = function
    | Expr.Old (c, Macro (_, "prestate", []), e) -> Some (COld (c, e))
    | _ -> None
      
  let rec simpleCmp (helper:TransHelper.TransEnv) failOnError = function
    | Expr.Ref (_, v), Expr.Ref (_, v') -> v = v'
    | Dot (_, e, f), Dot (_, e', f') -> f = f' && simpleCmp helper failOnError (e, e')
    | Expr.Macro (_, "&", [e]), Expr.Macro (_, "&", [e'])
    | Deref (_, e), Deref (_, e') -> simpleCmp helper failOnError (e, e')
    | This _, This _ -> true
    | e, e' -> 
      if failOnError then
        helper.Error (e'.Token, 9608, sprintf "expressions are not the same: %s  !==  %s" (e.ToString()) (e'.ToString()), None)
      false

  // -----------------------------------------------------------------------------
  // Expression construction/manipulation utilities
  // ----------------------------------------------------------------------------- 

  let zero = bigint.Zero
  let one = bigint.One
  let sizeT = Type.Integer IntKind.UInt64

  let mkRef (v:Variable) = Expr.Ref ({ bogusEC with Type = v.Type }, v)
  
  let mkOld ec name (expr:Expr) = Old (ec, Macro (voidBogusEC(), name, []), expr)
    
  let mkInt (x : int32) = 
    let intec = { Token = bogusToken; Type = Integer (IntKind.Int32) } : ExprCommon
    IntLiteral (intec, new bigint(x))

  let mkFieldRef (f:Field) = Macro ({ bogusEC with Type = Type.FieldT }, "field",  [Expr.UserData(bogusEC, f)]) 
  
  let typeExpr t =
    let c = { ExprCommon.Bogus with Type = PhysPtr t } // ptr kind does not matter here because it will be stripped of again later
    Expr.Macro ({ ExprCommon.Bogus with Type = Type.Math "\\type" }, "_vcc_typeof", [Expr.Cast (c, Processed, mkInt 0)])
      
  let boolOp op (a:Expr) b =
    Prim (a.Common, Op (op, Processed), [a; b])
  
  let multiAnd = function
    | [] -> Expr.True
    | [x] -> x
    | x :: xs -> List.fold (boolOp "&&") x xs
      
  let mapInvariants f decls =
    let fLab = function
      | Macro (c, "labeled_invariant", [lab; i]) -> 
        Macro (c, "labeled_invariant", [lab; f i])
      | i -> f i
      
    let aux = function
      | Top.TypeDecl td -> 
        td.Invariants <- td.Invariants |> List.map (splitConjunctionEx true) |> List.concat |> List.map fLab
      | _ -> ()
    List.iter aux decls
    decls

  let convertToBool self (x:Expr) =
    if x.Type = Bool then self x
    else Cast ({ x.Common with Type = Bool }, Processed, self x)

  let ptrToIntFunction = function 
    | Integer IntKind.UInt8 -> "_vcc_ptr_to_u1"
    | Integer IntKind.UInt16 -> "_vcc_ptr_to_u2"
    | Integer IntKind.UInt32 -> "_vcc_ptr_to_u4"
    | Integer IntKind.UInt64 -> "_vcc_ptr_to_u8"
    | Integer IntKind.Int8 ->  "_vcc_ptr_to_i1"
    | Integer IntKind.Int16 ->  "_vcc_ptr_to_i2"
    | Integer IntKind.Int32 ->  "_vcc_ptr_to_i4"
    | Integer IntKind.Int64 ->  "_vcc_ptr_to_i8"
    | _ -> die()
  let intToPtrFunction = function 
    | Integer IntKind.UInt8 -> "_vcc_u1_to_ptr"
    | Integer IntKind.UInt16 -> "_vcc_u2_to_ptr"
    | Integer IntKind.UInt32 -> "_vcc_u4_to_ptr"
    | Integer IntKind.UInt64 -> "_vcc_u8_to_ptr"
    | Integer IntKind.Int8 ->  "_vcc_i1_to_ptr"
    | Integer IntKind.Int16 ->  "_vcc_i2_to_ptr"
    | Integer IntKind.Int32 ->  "_vcc_i4_to_ptr"
    | Integer IntKind.Int64 ->  "_vcc_i8_to_ptr"
    | _ -> die()
    
  let elementTypeForArithmetic = function
    | Ptr Void -> Type.Integer IntKind.UInt8
    | Ptr t -> t
    | _ -> failwith "non-ptr type used in pointer arithmetic"

  let mapFunctions f decls =
    let aux decl =
      match decl with
        | Axiom _
        | GeneratedAxiom _
        | Top.Global _ 
        | TypeDecl _ -> decl
        | FunctionDecl d -> FunctionDecl (f d)
    List.map aux decls
    
  let addStmts stmts expr = Expr.MkBlock (stmts @ [expr])
  let addStmtsOpt stmts expr = Some (addStmts stmts expr)
      
  let intSuffix t = 
      match t with
      | Integer k -> Type.IntSuffix k
      | MathInteger Unsigned -> "nat"
      | _ -> failwith "integer type expected"
  
  let inRange (helper:TransHelper.TransEnv) ec (expr:Expr) =
    let castToInt expr = expr
    match expr.Type with
      | Integer k -> Expr.Macro (ec, "in_range_" + Type.IntSuffix k, [expr])
      | MathInteger Unsigned -> Expr.Macro(ec, "in_range_nat", [expr])
      | MathInteger Signed -> Expr.True
      | PhysPtr _ 
      | SpecPtr _ 
      | ObjectT
      | Primitive _ -> Expr.True
      | _ -> failwith "integer or float type expected"

  let uncheckedSignConversion (expr :Expr) =
    match expr.Type.DerefSoP with 
      | Integer k, isSpec -> Macro({expr.Common with Type = Type.MkPtr(Integer(Type.SwitchSignedness k), isSpec)}, "unchecked_" + Type.IntSuffix(Type.SwitchSignedness k), [expr])
      | _ -> die()

  let subtractOffsets fo1 fo2  =
    match fo1, fo2 with
    | Normal n1,              Normal n2 -> assert (n1 >= n2); Normal (n1 - n2)
    | BitField(n1, bo1, bs1), Normal n2 -> assert (n1 >= n2); BitField(n1 - n2, bo1, bs1)
    | _-> die()                  
    
  let addOffsets fo1 fo2 =
    match fo1, fo2 with
    | Normal n1,              Normal n2 -> Normal (n1 + n2)
    | BitField(n1, bo1, bs1), Normal n2 -> BitField(n1 + n2, bo1, bs1)
    | _ -> die()
  
  // -----------------------------------------------------------------------------
  // Caching
  // ----------------------------------------------------------------------------- 

  let getTmp (helper:TransHelper.TransEnv) name = Variable.CreateUnique (name + "#" + (helper.UniqueId()).ToString())
     
  let cacheEx saveRefs helper assign name expr varKind = 
    let rec isSimple = function
      | Expr.Ref _ -> not saveRefs
      | IntLiteral _
      | BoolLiteral _ -> true
      | Dot (_, e, _) -> isSimple e
      | _ -> false  
    if isSimple expr then ([], expr) // no need to cache
    else
      let tmp = getTmp helper name expr.Type varKind
      ([ Expr.VarDecl (voidBogusEC(), tmp, []);
         assign tmp expr ],
       Expr.Ref (expr.Common, tmp))

  let cache helper = cacheEx false helper (fun tmp expr -> Macro (voidBogusEC(), "=", [mkRef tmp; expr]))
  let cacheMany helper name exprs varKind = 
    let decls, refs = 
      exprs 
        |> List.map (fun e -> cache helper name e varKind)
        |> List.unzip
    List.concat decls, refs
  let lateCache helper = cacheEx false helper (fun tmp expr -> VarWrite (voidBogusEC(), [tmp], expr))
  let lateCacheRef helper = cacheEx true helper (fun tmp expr -> VarWrite (voidBogusEC(), [tmp], expr))

  let cacheMultiple helper fn name varKind exprs =
     let aux (assigns, refs) e =
        let assignsE, refE = fn helper name e varKind
        (List.rev assignsE @ assigns, refE :: refs)
     exprs |> List.fold aux ([], []) |> fun (a, b) -> (List.rev a, List.rev b)
  
  (*
  let applyFieldSubst (subst : Dict<Field, Field>) decls =
    let repl self = function
      | Dot (c, e, f) -> 
        match subst.TryGetValue f with
        | (true, sField) -> Some (Dot (c, self e, sField))
        | (false, _) -> None
      | _ -> None 
    deepMapExpressions repl decls
    *)
        
  // -----------------------------------------------------------------------------
  // VCC specific
  // ----------------------------------------------------------------------------- 

  let staticOwns (td:TypeDecl) = 
    List.forall (function VccAttr (AttrDynamicOwns, _) | VccAttr (AttrVolatileOwns, _) -> false | _ -> true) td.CustomAttr
  
  let inheritedAttrs attrs = 
    let isInherited = function
      | VccAttr(AttrSkipVerification, _)
      | VccAttr(AttrIsolateProof, _) 
      | VccAttr(AttrSkipSmoke, _) -> true
      | _ -> false
    attrs |> List.filter isInherited
  
  // Warning: this function gets rid of multiplication so possible overflow check is gone
  // This usually is OK in spec context.
  let extractArraySize (helper:TransHelper.TransEnv) (expr:Expr) (elementType:Type) (byteCount:Expr) =
    let typeSz = new bigint(elementType.SizeOf)
    let byteCount =
      match byteCount with
        | Cast (_, _, e) -> e
        | e -> e
    let (neg, byteCount) =
      match byteCount with
        | Prim (c, (Op("-", _) as op), [e]) -> (fun e -> Prim (c, op, [e])), e
        | e -> (fun x -> x), e
    let elts =
      match byteCount with
        | IntLiteral (c, allocSz) when (allocSz % typeSz) = zero ->
          IntLiteral (c, allocSz / typeSz)
        | Prim (_, Op("*", _), [e1; e2]) ->
          let rec stripCasts = function | Cast(_,_, e) -> stripCasts e | e -> e
          match stripCasts e1, stripCasts e2 with
            | Expr.IntLiteral (_, allocSz), _ when allocSz = typeSz -> e2
            | _, Expr.IntLiteral (_, allocSz) when allocSz = typeSz -> e1
            | Expr.SizeOf(_, t), _ when t = elementType -> e2
            | _, Expr.SizeOf(_, t) when t = elementType -> e1
            | _ -> helper.Warning (byteCount.Common.Token, 9102, "don't know how to determine number of elements in array: " + expr.ToString(), None)
                   Prim (byteCount.Common, Op("/", Processed), [byteCount; mkInt elementType.SizeOf])
        | _ when typeSz = one -> byteCount
        | _ ->
          helper.Warning (byteCount.Common.Token, 9102, "don't know how to determine number of elements in array: " + expr.ToString(), None)
          Prim (byteCount.Common, Op("/", Processed), [byteCount; mkInt elementType.SizeOf])
          
    match neg elts with
      | IntLiteral (_, OneBigInt) -> None
      | sz -> Some sz
        
        
  // when calling that function make sure that the internal function is not pruned away
  let internalFunction (helper: TransHelper.TransEnv) name =
    let name = "_vcc_" + name
    let rec find = function 
      | Top.FunctionDecl hd :: xs -> 
        if hd.Name = name then hd
        else find xs
      | _ :: xs -> find xs
      | [] -> helper.Panic ("cannot find internal function " + name + ". Forgotten #include <vcc.h>?")
    find helper.TopDecls
           
    
  let computeReads (expr:Expr) = 
    let isPure = ref true         
    let rec checkForSideEffect _ = function
      | Deref(_, Dot(_,e,f)) when f.Parent.IsRecord -> true
      | Macro (_, "_vcc_vs_ctor", _)
      | Deref _ ->
        isPure := false
        false
      | Call(_, fn, _, _) ->
          if not fn.IsStateless then isPure := false; false
          else true
      | _ -> true
    expr.SelfVisit checkForSideEffect
    if !isPure then [] else [Expr.Macro ({ bogusEC with Type = Type.PtrSet }, "_vcc_set_universe", [])]

  let exprDependsOnSpecExpr (expr : Expr) = 
    let (specFound : string option ref) = ref None
    let continueIfNotFound() = Option.isNone !specFound
    let hasSpec' self = function
      | Dot(_, _, f) when f.IsSpec -> specFound := Some("field '" + f.Name + "'"); false
      | Ref(_, ({Kind = SpecLocal} as v)) -> specFound := Some("variable '" + v.Name + "'"); false
      | Ref(_, ({Kind = SpecParameter|OutParameter} as v)) -> specFound := Some("parameter '" + v.Name + "'"); false
      | CallMacro(_, ("_vcc_alloc" | "_vcc_stack_alloc"), _, _) -> false
      | Macro(_, "by_claim", [_; obj; ptr]) -> self obj; self ptr; false
      | Call(_, ({IsSpec = true} as f), _, _) -> specFound := Some("function '" + f.Name + "'"); false
      | Call(_, fn, _, args) ->
        let checkNonSpecPar (p : Variable) (e : Expr) =
          if p.Kind <> VarKind.SpecParameter && p.Kind <> VarKind.OutParameter then self e
        List.iter2 checkNonSpecPar fn.Parameters args
        false
      | Old(_, (CallMacro(_, "_vcc_by_claim", _, _)), expr) -> self expr; false
      | Atomic(_, _, expr) -> self expr; false
      | Block(_, exprs, _) ->
        let rec checkLastExpr = function
          | [] -> ()
          | [x] -> self x
          | _ :: xs -> checkLastExpr xs
        checkLastExpr exprs; false
      | _ -> continueIfNotFound()
    expr.SelfVisit hasSpec'
    !specFound
    
  // -----------------------------------------------------------------------------
  // Pruning
  // ----------------------------------------------------------------------------- 

  type PruneCallback =
    abstract UseTypeDecl : TypeDecl -> unit
    abstract UseFunction : Function -> unit
    abstract UseGlobal : Variable -> unit
    
  let rec walkType (cb:PruneCallback) t = 
    let checkType = walkType cb
    match t with
      | PhysPtr t
      | SpecPtr t
      | Type.Volatile t
      | Type.Array (t, _) -> checkType t
      | Type.Map (t1, t2) ->
        checkType t1
        checkType t2
      | Type.Ref td -> 
        match td.Name with
          | "$$bogus$$"
          | "#Object" -> ()
          | _ ->
            cb.UseTypeDecl td
            for f in td.DataTypeOptions do
              cb.UseFunction f
            match td.Kind with
              | FunctDecl d -> cb.UseFunction d
              | _ -> ()
      | Type.Claim
      | Type.SecLabel _
      | Type.TypeIdT
      | Type.Void
      | Type.Bool
      | Type.Integer _
      | Type.MathInteger _
      | Type.ObjectT
      | Type.TypeVar _
      | Type.Primitive _ -> ()     
  
  let walkExpr (cb:PruneCallback) self (e:Expr) =
    walkType cb e.Type
    match e with
      | Expr.Call (_, fn, targs, _) -> 
        cb.UseFunction fn
        for t in targs do walkType cb t
      | Expr.Ref (_, v) ->
        match v.Kind with
          | VarKind.SpecGlobal
          | VarKind.ConstGlobal
          | VarKind.Global -> cb.UseGlobal v
          | VarKind.Local
          | VarKind.SpecLocal
          | VarKind.QuantBound
          | VarKind.SpecParameter
          | VarKind.OutParameter
          | VarKind.Parameter -> () 
      | Expr.Quant (_, qd) ->
        for v in qd.Variables do
          walkType cb v.Type
      | Expr.VarDecl (_, v, _) -> walkType cb v.Type
      | Expr.Dot (_, _, f) ->
        cb.UseTypeDecl f.Parent
      | _ -> ()
    true
  
  let rec walkTop cb t =
    let doVar (v:Variable) = walkType cb v.Type
    match t with
      | Top.FunctionDecl h ->
        List.iter doVar h.Parameters
        walkType cb h.RetType
      | Top.Global (v, _) -> doVar v
      | Top.TypeDecl td ->
        for f in td.Fields do
          walkType cb f.Type
        for o in td.DataTypeOptions do
          cb.UseFunction o
      | Top.Axiom ax -> ax.SelfVisit (walkExpr cb)
      | Top.GeneratedAxiom _ -> ()

      
  let doPruneBy funcName decls =
    let used = new HashSet<obj>()
    let generatedAxioms = objDict()
    let todo = ref []
    let axioms = ref []
    let shouldDo (o:obj) = used.Add(o)
    
    let rec add top = 
      walkTop cb top
      todo := top :: !todo
      addDependentAxioms top
      
    and topToObj = function
      | Top.TypeDecl td -> td :> obj
      | Top.Global(v, _) -> v :> obj
      | Top.FunctionDecl f -> f :>obj
      | Top.Axiom ax -> ax :> obj
      | _ -> null
      
    and addDependentAxioms top = 
      let topAsObj = topToObj top
      if topAsObj <> null then
        match generatedAxioms.TryGetValue(topAsObj) with
          | true, axioms -> List.iter add axioms
          | _ -> ()
    and cb = 
      { new PruneCallback with
          member self.UseTypeDecl td = if shouldDo td then add (Top.TypeDecl td)
          member self.UseGlobal v =    if shouldDo v then add (Top.Global (v, None))
          member self.UseFunction f =  if shouldDo f then add (Top.FunctionDecl f) 
      }
    
    let pickOutAxioms = function
      | GeneratedAxiom(_, origin) as axiom ->
        let originAsObj = topToObj origin
        match generatedAxioms.TryGetValue(originAsObj) with
          | false, _ -> generatedAxioms.Add(originAsObj, [axiom])
          | true, axioms -> generatedAxioms.[originAsObj] <- axiom :: axioms
      | Axiom _ as axiom -> axioms := axiom :: !axioms
      | _ -> ()
      
    List.iter pickOutAxioms decls
    
    let doDecl d = deepVisitExpressions (walkExpr cb) [d]


    let findTheOne = function 
      | FunctionDecl f as d when f.Name = funcName ->
        shouldDo f |> ignore
        add d 
        doDecl d
      | _ -> ()
    List.iter findTheOne decls
    
    let drainTodo() =
      while not (!todo).IsEmpty do
        let lst = !todo
        todo := []

        for d in lst do
          match d with
            | Top.FunctionDecl fn -> 
              let savedBody = fn.Body
              fn.Body <- None
              doDecl d
              fn.Body <- savedBody
            | _ -> doDecl d

    drainTodo()

    let axiomWouldTriggerOnUsed axiom = 
      let usedReferenced = ref false
      let anyReferenced = ref false
      let cb = { new PruneCallback with 
                   member self.UseTypeDecl td = anyReferenced := true;  if used.Contains td then usedReferenced := true
                   member self.UseGlobal v = anyReferenced := true;  if used.Contains v then usedReferenced := true
                   member self.UseFunction f = anyReferenced := true;  if used.Contains f then usedReferenced := true }
                   
      match axiom with
        | Top.Axiom(Quant(_, {Triggers =  tr})) when List.concat tr = [] -> walkTop cb axiom // no, or only empty, triggers, walk all
        | Top.Axiom(Quant(_, qd)) -> List.iter (List.iter (fun (e : Expr) -> e |> (walkExpr cb) |> ignore)) qd.Triggers
        | _ -> walkTop cb axiom
                   
      (not !anyReferenced) || !usedReferenced // if we do not mention anything, that we also need to be included
    
    while not (!axioms).IsEmpty do
      let axs1, axs2 = List.partition axiomWouldTriggerOnUsed !axioms
      List.iter (shouldDo >> ignore) axs1
      todo := axs1
      drainTodo()
      axioms := if axs1.IsEmpty then [] else axs2
    
    let rec needed = function
      | FunctionDecl f -> used.Contains f
      | TypeDecl t -> used.Contains t
      | Global (v, _) -> used.Contains v
      | GeneratedAxiom (_, origin) -> needed origin
      | Axiom _ as ax -> used.Contains ax
    
    let discardFunctionBodysExceptFor fname = function
      | FunctionDecl({Name = name}) as fdecl when name = fname -> fdecl
      | FunctionDecl f -> FunctionDecl({f with Body = None})
      | other -> other

    decls |> List.filter needed |> List.map (discardFunctionBodysExceptFor funcName)
      
  let pruneBy (env:TransHelper.TransEnv) funcName decls = env.SwPruning.Run doPruneBy funcName decls
  
  let dumpDecls msg showTypes decls = 
    printf ">>> %s\r\n" msg
    for (d:Top) in decls do printf "%s" (d.ToStringWT(showTypes))
    decls

  let forEachInvariant f decls =
    for d in decls do
      match d with
        | Top.TypeDecl(td) -> List.iter (fun (i:Expr) -> (i.SelfVisit f)) td.Invariants
        | _ -> ()

  let checkTermination (helper:TransHelper.TransEnv) (fn:Function) =
    if fn.CustomAttr |> hasCustomAttr AttrDefinition || fn.CustomAttr |> hasCustomAttr AttrAbstract then
      helper.Options.TerminationForPure
    // if explicit measure is given, and termination is not disabled, then check it 
    elif helper.Options.TerminationForPure && fn.Variants <> [] then
      true
    elif fn.IsSpec then
      helper.Options.TerminationForGhost
    else
      helper.Options.TerminationForAll

