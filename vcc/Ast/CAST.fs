//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

module Microsoft.Research.Vcc.CAST
  open System.Text
  open Microsoft.FSharp.Math
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.Util
  
  type Id = string
  type Unique = uint64

  [<Literal>]
  let AttrAtomicInline = "atomic_inline"

  [<Literal>]
  let AttrIsAdmissibility = "is_admissibilitycheck"

  [<Literal>]
  let AttrSkipVerification = "skip_verification"

  [<Literal>]
  let AttrIsolateProof = "isolate_proof"

  [<Literal>]
  let AttrSkipSmoke = "skip_smoke"

  [<Literal>]
  let AttrNoAdmissibility = "no_admissibility"

  [<Literal>]
  let AttrInGroup = "in_group"

  [<Literal>]
  let AttrGroupDecl = "group_decl"

  [<Literal>]
  let AttrBackingMember = "backing_member"

  [<Literal>]
  let AttrMemberName = "member_name"

  [<Literal>]
  let AttrFrameaxiom = "frameaxiom"

  [<Literal>]
  let AttrBoogie0 = "_boogie0"

  [<Literal>]
  let AttrBoogie1 = "_boogie1"

  [<Literal>]
  let AttrBoogie2 = "_boogie2"

  [<Literal>]
  let AttrIsPure = "is_pure"

  [<Literal>]
  let AttrDefinition = "definition"

  [<Literal>]
  let AttrAbstract = "abstract"

  [<Literal>]
  let AttrBvLemmaCheck = "bv_lemma_check"

  [<Literal>]
  let AttrNoReadsCheck = "no_reads_check"

  [<Literal>]
  let AttrSpecMacro = "spec_macro"

  [<Literal>]
  let AttrAsArray = "as_array"

  [<Literal>]
  let AttrRecord = "record"

  [<Literal>]
  let AttrIsDatatypeOption = "_vcc_internal__is_datatype_option"

  [<Literal>]
  let AttrYarra = "yarra"

  [<Literal>]
  let AttrDynamicOwns = "dynamic_owns"

  [<Literal>]
  let AttrVolatileOwns = "volatile_owns"

  [<Literal>]
  let AttrPrimitive = "primitive"

  type VarKind =    
    | Parameter
    | SpecParameter
    | OutParameter
    | Local
    | SpecLocal
    | Global
    | ConstGlobal
    | SpecGlobal
    | QuantBound
    
  type QuantKind =
    | Forall
    | Exists
    | Lambda
    // sum and stuff here

  let PointerSizeInBytes = ref 8

  let uniqueCounter = ref 0UL
  let unique() : Unique = 
    uniqueCounter := !uniqueCounter + 1UL
    !uniqueCounter
  
  let bogusToken = Token.NoToken
  
  let mathTypeCache = new Dict<string, obj>()
  
  type FieldOffset =
    | Normal of int
    | BitField of int * int * int // byte-offset, bit-offset, bit-size
  
  type MathIntKind =
    | Signed
    | Unsigned

  type IntKind =
    | UInt8
    | Int8
    | UInt16
    | Int16
    | UInt32
    | Int32
    | UInt64
    | Int64
    
    member this.SizeSign =
      match this with
        | IntKind.UInt8  -> (8, false)
        | IntKind.UInt16 -> (16, false)
        | IntKind.UInt32 -> (32, false)
        | IntKind.UInt64 -> (64, false)
        | IntKind.Int8   -> (8, true)
        | IntKind.Int16  -> (16, true)
        | IntKind.Int32  -> (32, true)
        | IntKind.Int64  -> (64, true)
    
    override this.ToString () =
      let (sz, sign) = this.SizeSign
      (if sign then "int" else "uint") + sz.ToString() + "_t"

  type PrimKind =
    | Float32
    | Float64

  type StructEqualityKind =
    | NoEq
    | ShallowEq
    | DeepEq

  type LabelId = 
    {
      Name:string;
    }
  
  type [<StructuralEquality; NoComparison>] CustomAttr =
    | IntBoogieAttr of string * int
    | BoolBoogieAttr of string * bool
    | VccAttr of string * string
    | ReadsCheck of Function

    override this.ToString () =
      match this with
        | IntBoogieAttr (s, i) -> sprintf "_(%s %d)" s i
        | BoolBoogieAttr (s, b) -> sprintf "_(%s %s)" s (if b then "true" else "false")
        | VccAttr (s, v) -> sprintf "_(%s \"%s\")" s v
        | ReadsCheck f -> sprintf "_(reads_check %s)" f.Name

    static member AsString (lst:list<CustomAttr>) = lst |> List.map (fun a -> a.ToString() + " ") |> String.concat ""

  and [<StructuralEquality; NoComparison>] TypeKind =
    | Struct
    | Union
    | MathType
    | FunctDecl of Function
    | Record
    
  and [<CustomEquality; NoComparison>]
    Field =    
    {
      Token:Token;
      mutable Name:string;
      Type:Type;
      Parent:TypeDecl;
      IsSpec:bool;    
      mutable IsVolatile:bool;
      Offset:FieldOffset;
      CustomAttr:list<CustomAttr>;
      UniqueId:Unique;
    }
    
    override this.GetHashCode () = int this.UniqueId
    override this.Equals (that:obj) = LanguagePrimitives.PhysicalEquality that (this :> obj)
    
    override this.ToString () =
      let postfix =
        match this.Offset with
          | BitField (off, bo, bs) -> sprintf " /* @%d.%d, sz:%d */" off bo bs
          | Normal off -> sprintf " /* @%d */" off
      (if this.IsSpec then "__spec " else "") + 
      (if this.IsVolatile then "volatile " else "") +
      CustomAttr.AsString this.CustomAttr +
      this.Type.ToString() + " " + this.Name + postfix
    
    member this.ByteOffset =
      match this.Offset with
        | FieldOffset.Normal n -> n
        | _ -> die()
  
  
  and [<CustomEquality; NoComparison>]
    TypeDecl =
    {
      Token:Token;    
      mutable Kind: TypeKind;
      mutable Name: string;
      mutable Fields: list<Field>;
      mutable DataTypeOptions: list<Function>;
      mutable Invariants: list<Expr>;
      mutable CustomAttr:list<CustomAttr>;
      mutable SizeOf: int;
      mutable IsNestedAnon: bool;
      mutable GenerateEquality: StructEqualityKind;
      mutable IsSpec: bool;
      Parent : TypeDecl option;
      IsVolatile : bool
      UniqueId:Unique;
    }
    
    override this.GetHashCode () = int this.UniqueId
    override this.Equals (that:obj) = LanguagePrimitives.PhysicalEquality that (this :> obj)

    member this.IsDataType = this.DataTypeOptions <> []

    member this.IsRecord =
      this.Kind = Record ||
      List.exists (function VccAttr(AttrRecord, "") -> true | _ -> false) this.CustomAttr 

    member this.IsMathValue = this.IsRecord || this.IsDataType || this.Kind = MathType

    override this.ToString () =
      (match this.Kind with
        | Struct -> "struct "
        | Record -> "record "
        | Union -> "union "
        | MathType when this.IsDataType -> "datatype "
        | MathType -> "_math "
        | FunctDecl d -> "_fnptr ") + this.Name
    
    member this.IsGroup = List.exists (function VccAttr ("__vcc_group", "") -> true | _ -> false) this.CustomAttr
    member this.IsUnion = this.Kind = Union
    
    member this.Declaration () =
      let prInv = function
        | Macro(_, "labeled_invariant", [Macro(_, "", _); i]) -> "invariant " + i.ToString()
        | Macro(_, "labeled_invariant", [Macro(_, lbl, _); i]) -> "invariant " + lbl + ": " + i.ToString()
        | e -> "invariant " + e.ToString()
      CustomAttr.AsString this.CustomAttr +
      this.ToString () + " {\r\n  " + String.concat ";\r\n  " [for f in this.Fields -> f.ToString ()] + ";\r\n" +
        String.concat "" [for f in this.DataTypeOptions -> f.ToString() ] +
        String.concat "" [for i in this.Invariants -> prInv i + ";\r\n" ] + "}\r\n"
  
  // TODO: this attribute shouldn't be needed here, but is      
  and [<StructuralEquality; NoComparison>] Type =
    | Void
    | Integer of IntKind
    | Primitive of PrimKind
    | Bool
    | Volatile of Type
    | PhysPtr of Type
    | SpecPtr of Type
    | Ref of TypeDecl
    | Array of Type * int
    | TypeIdT
    | SecLabel of Expr option
    | Claim                // the \claim in C is actually Claim*
    | Map of Type * Type   // t1 -> t2
    | ObjectT
    | MathInteger of MathIntKind
    | TypeVar of TypeVariable
    
    member this.WriteTo b =
      let wr = wrb b
      match this with
        | Void -> wr "void"
        | Integer x -> wr (x.ToString())
        | Primitive x -> wr (x.ToString())
        | Bool -> wr "_Bool"
        | TypeIdT -> wr "_TypeId"
        | PhysPtr t -> t.WriteTo b; wr "*"
        | SpecPtr t -> t.WriteTo b; wr "^"
        | Volatile t -> wr "volatile "; t.WriteTo b
        | Type.Ref d -> wr (d.ToString ())
        | Array (t, sz) -> t.WriteTo b; wr ("[" + sz.ToString() + "]")
        | Map (t1, t2) -> wr "("; t1.WriteTo b; wr " -> "; t2.WriteTo b; wr ")"
        | SecLabel _ -> wr "label_t"
        | Claim -> wr "\\claim"
        | ObjectT -> wr "\\object"
        | MathInteger MathIntKind.Signed -> wr "\\integer"
        | MathInteger MathIntKind.Unsigned -> wr "\\natural"
        | TypeVar({Name = id}) -> wr id
    
    override this.ToString () = toString (this.WriteTo)
    
    static member MkPtr(t,isSpec) = if isSpec then Type.SpecPtr(t) else Type.PhysPtr(t)
    
    static member MkPtrToStruct (td:TypeDecl) = Type.MkPtr(Type.Ref(td), td.IsSpec)
    
    static member RetypePtr(ptrType, newTgt) =
      match ptrType with
        | PhysPtr _ -> PhysPtr newTgt
        | SpecPtr _ -> SpecPtr newTgt
        | _ -> die()
    
    member this._IsArray =
      match this with
        | Array _ -> true
        | _ -> false
    
    member this._IsPtr =
      match this with
        | ObjectT
        | SpecPtr _
        | PhysPtr _ -> true
        | _ -> false
        
    member this.IsPtrTo td =
      match this with 
        | SpecPtr td'
        | PhysPtr td' when td = td' -> true
        | _ -> false
    
    member this._IsMap = match this with | Map _ -> true | _ -> false
    
    member this.IsComposite =
      match this with
        | Void
        | Integer _
        | MathInteger _
        | Primitive _
        | Bool
        | PhysPtr _
        | SpecPtr _
        | TypeIdT
        | ObjectT
        | Type.Ref { Kind = (FunctDecl _|MathType|Record) }
        | SecLabel _
        | Map _ -> false
        | TypeVar _
        | Claim
        | Type.Ref { Kind = (Struct|Union) } -> true
        | Volatile(t)
        | Array (t, _) -> t.IsComposite
    
    member this._IsInteger =
      match this with 
      | Integer _ -> true
      | _         -> false

    member this._IsMathInteger =
      match this with
      | MathInteger _ -> true
      | _             -> false

    member this.IsSignedInteger =
      match this with 
      | Integer sz -> sz |> Type.sizeSign |> snd
      | _          -> false
    
    member this.IsNumber =
      this._IsInteger || this._IsMathInteger

    member this.Deref =
      match this with
      | SpecPtr t 
      | PhysPtr t -> t
      | t -> t
     
    member this.IsPtr =
      match this with
      | SpecPtr _
      | PhysPtr _ -> true
      | _ -> false

    member this.DerefSoP =
      match this with
      | SpecPtr t -> t, true
      | PhysPtr t -> t, false  
      | t -> t, false
    
    member private this.IsMathType name =
      match this with
      | Type.Ref({Kind = MathType; Name = name'}) when name = name' -> true
      | _ -> false

    member this.IsPtrSet = this.IsMathType "\\objset"
    member this.IsMathStruct = this.IsMathType "struct"
    member this.IsMathState = this.IsMathType "\\state"

    // those should be treated as immutable
    static member MathTd name = 
      match mathTypeCache.TryGetValue name with
        // if we get the type of the cache right, F# complains about invalid forward type references
        | true, td when name = (td :?> TypeDecl).Name -> (td :?> TypeDecl)
        | _ ->
          let td =
            { 
              Token = bogusToken
              Name = name
              Kind = MathType
              Fields = []
              SizeOf = 1
              Invariants = []
              CustomAttr = []
              DataTypeOptions = []
              IsNestedAnon = false
              GenerateEquality = NoEq
              Parent = None
              IsVolatile = false
              IsSpec = true
              UniqueId = unique()
            }
          mathTypeCache.[name] <- td
          td
 
    static member Math name = Type.Ref (Type.MathTd name)    
    static member Bogus = Type.Math "$$bogus$$"
    static member PtrSet = Type.Math "\\objset"
    static member MathStruct = Type.Math "struct"
    static member MathState = Type.Math "\\state"
    static member FieldT = Type.Math "field_t"
    static member Byte = Type.Integer IntKind.UInt8
    static member MathStructFor td = 
      Type.Ref(
        { 
          Token = bogusToken
          Name = "struct"
          Kind = MathType
          Fields = []
          SizeOf = 1
          Invariants = []
          CustomAttr = []
          DataTypeOptions = []
          IsNestedAnon = false
          GenerateEquality = NoEq
          Parent = Some(td)
          IsVolatile = false
          IsSpec = true
          UniqueId = unique()
        }
      )


    static member private sizeSign t = t.SizeSign
    static member private primSize = function
      | PrimKind.Float32 -> 4
      | PrimKind.Float64 -> 8

    static member ConversionIsLossless = function
      | Integer from, Integer to_ ->
        let (sz1, signed1) = Type.sizeSign from
        let (sz2, signed2) = Type.sizeSign to_
        (signed1 = signed2 && sz1 <= sz2) || (not signed1 && signed2 && sz1 < sz2)
      | MathInteger _ , Integer _ -> false
      | MathInteger Signed, MathInteger Unsigned -> false
      | Integer from, MathInteger Unsigned ->
        let (_, signed) = Type.sizeSign from 
        not signed
      | _ -> true
              
    member this.SizeOf =
      match this with
        | Integer k -> fst (Type.sizeSign k) / 8
        | Primitive k -> Type.primSize k
        | SpecPtr _
        | PhysPtr _
        | ObjectT -> !PointerSizeInBytes
        | Volatile t -> t.SizeOf
        | Type.Ref td -> td.SizeOf
        | Array (t, sz) -> t.SizeOf * sz
        | MathInteger _ -> 8
        | Bool
        | Void
        | SecLabel _
        | Claim
        | SecLabel _
        | TypeIdT
        | Map _
        | TypeVar _ -> 1

      
    static member IntSuffix k =
      match Type.sizeSign k with
        | (sz, true) -> System.String.Format ("i{0}", sz / 8)
        | (sz, false) -> System.String.Format ("u{0}", sz / 8)

    static member SwitchSignedness = function
      | IntKind.UInt8  -> IntKind.Int8
      | IntKind.UInt16 -> IntKind.Int16
      | IntKind.UInt32 -> IntKind.Int32
      | IntKind.UInt64 -> IntKind.Int64
      | IntKind.Int8   -> IntKind.UInt8
      | IntKind.Int16  -> IntKind.UInt16
      | IntKind.Int32  -> IntKind.UInt32
      | IntKind.Int64  -> IntKind.UInt64

    static member ToUnsigned = function
      | IntKind.UInt8
      | IntKind.Int8   -> IntKind.UInt8
      | IntKind.UInt16 
      | IntKind.Int16  -> IntKind.UInt16
      | IntKind.UInt32
      | IntKind.Int32  -> IntKind.UInt32
      | IntKind.UInt64
      | IntKind.Int64  -> IntKind.UInt64

    static member PrimSuffix = function
      | PrimKind.Float32 -> "f4"
      | PrimKind.Float64 -> "f8"
                
    static member IntRange : IntKind -> bigint * bigint =
      memoize (fun k ->
                  let mkBigInt (n : int32) = new bigint(n)
                  let sub bi1 bi2 = bi1 - bi2
                  let zero = bigint.Zero
                  let one = bigint.One
                  let two = mkBigInt 2
                  let (sz, signed) = Type.sizeSign k
                  if signed then
                    let x = bigint.Pow (two, sz - 1)
                    (sub zero x, sub x one)
                  else
                    (zero, sub (bigint.Pow(two, sz)) one))
                    
    member this.Subst(typeMap : Type -> Type option) =
      let rec subst _type =
        match typeMap _type with
          | Some t' -> Some t'
          | None ->
            match _type with
              | SpecPtr(t) -> 
                match subst t with
                  | Some t' -> Some(SpecPtr t')
                  | _ -> None
              | PhysPtr(t) -> 
                match subst t with
                  | Some t' -> Some(PhysPtr t')
                  | _ -> None
              | Volatile(t) -> 
                match subst t with
                  | Some t' -> Some(Volatile t')
                  | _ -> None
              | Array(t, n) -> 
                match subst t with
                  | Some t' -> Some(Array(t', n))
                  | _ -> None
              | Map(t1, t2) -> 
                match subst t1, subst t2 with
                  | None, None -> None
                  | Some t1', None -> Some(Map(t1', t2))
                  | None, Some t2' -> Some(Map(t1, t2'))
                  | Some t1', Some t2' -> Some(Map(t1', t2'))
              | t -> None
      subst this

    member this.ApplySubst(typeMap) = 
      match this.Subst(typeMap) with
        | Some t' -> t'
        | None -> this
        
  and [<CustomEquality; CustomComparison>]
    Variable = 
      { 
        Name:Id; 
        Type:Type; 
        Kind:VarKind; 
        UniqueId:Unique;
      }
    
      interface System.IComparable with
        member this.CompareTo(other : obj) = 
          match other with
            | :? Variable as var1 -> this.UniqueId.CompareTo(var1.UniqueId)
            | _ -> -1
          

      override this.GetHashCode () = int this.UniqueId
      override this.Equals (that:obj) = LanguagePrimitives.PhysicalEquality that (this :> obj)
    
      static member CreateUnique name _type kind  = 
        { Name = name 
          Type = _type
          Kind = kind
          UniqueId = unique()
        } : Variable
    
      member this.UniqueCopy() = Variable.CreateUnique this.Name this.Type this.Kind

      static member UniqueCopies f vars =
        let subst = new Dict<_,_>()
        let doSubst (v:Variable) =
          let v' = f (v.UniqueCopy())
          subst.Add(v,v')
          v'
        let replace (e:Expr) = 
          let replace' _ = function
            | Expr.Ref(ec, v) -> 
              match subst.TryGetValue v with
                | true, v' -> Some(Expr.Ref(ec, v'))
                | false, _ -> None
            | _ -> None
          e.SelfMap(replace')
        let vars' = List.map doSubst vars
        vars', replace
    
      member this.WriteTo b =
        match this.Kind with
          | SpecGlobal
          | SpecLocal 
          | SpecParameter -> wrb b "spec "
          | ConstGlobal -> wrb b "const "
          | OutParameter -> wrb b "out "
          | _ -> ()
        this.Type.WriteTo b
        wrb b (" " + this.Name)      
      
      member this.IsSpec = 
        match this.Kind with 
          | SpecParameter
          | OutParameter
          | SpecLocal
          | SpecGlobal
          | QuantBound -> true
          | _ -> false

      override this.ToString () = toString (this.WriteTo)
 
  and [<StructuralEquality; NoComparison>]
    TypeVariable = 
      {
        Name:Id;
      }
      
      member this.WriteTo b = wrb b (this.Name)
 
  and ExprCommon = 
    {
      Token:Token;
      Type:Type;
    }

  and [<CustomEquality; NoComparison>]
    Function = 
    {
      Token:Token;
      IsSpec:bool;
      AcceptsExtraArguments:bool;
      mutable RetType:Type;
      mutable Name:Id;
      mutable Parameters:list<Variable>;
      mutable TypeParameters:list<TypeVariable>
      mutable Requires:list<Expr>;
      mutable Ensures:list<Expr>;
      mutable Writes:list<Expr>;
      mutable Reads:list<Expr>;
      mutable Variants:list<Expr>;
      mutable CustomAttr:list<CustomAttr>;
      mutable Body:option<Expr>;
      mutable IsProcessed:bool;
      mutable DecreasesLevel:int;
      mutable DefExpansionLevel:int;
      UniqueId:Unique;
    }

    static member Empty() =
      { Token = bogusToken
        IsSpec = false
        RetType = Type.Void
        Parameters = []
        TypeParameters = []
        Name = "<none>"
        Requires = []
        Ensures = []
        Writes = []
        Variants = []
        Reads = []
        CustomAttr = []
        DecreasesLevel = 0
        Body = None
        IsProcessed = false
        AcceptsExtraArguments = false
        DefExpansionLevel = 0
        UniqueId = unique() } : Function
    
    override this.GetHashCode () = int this.UniqueId
    override this.Equals (that:obj) = LanguagePrimitives.PhysicalEquality that (this :> obj)
    
    member this.InParameters = [ for p in this.Parameters do if p.Kind <> VarKind.OutParameter then yield p ]
    
    member this.OutParameters = [ for p in this.Parameters do if p.Kind = VarKind.OutParameter then yield p ]
    
    member this.IsWellFounded =
      List.exists (function VccAttr((AttrDefinition|AttrAbstract|AttrIsDatatypeOption), "") -> true | _ -> false) this.CustomAttr 

    member this.IsPure =
      let isReadsCheck = List.exists (function ReadsCheck _ -> true | _ -> false) this.CustomAttr 
      if (this.Name.StartsWith "_vcc_"  || (this.Name.StartsWith "\\" && not isReadsCheck)) && this.Writes = [] then
        true
      //else if this.Name.StartsWith "fnptr#" && this.Writes = [] then
      //  true // HACK
      else
        List.exists (function VccAttr((AttrFrameaxiom|AttrIsPure|AttrSpecMacro|AttrDefinition|AttrAbstract|AttrIsDatatypeOption), "") -> true | _ -> false) this.CustomAttr 
      
    member this.IsDatatypeOption =
      List.exists (function VccAttr(AttrIsDatatypeOption, "") -> true | _ -> false) this.CustomAttr 
       
    member this.IsStateless =
      this.IsPure && this.Reads = []

    member this.Specialize(targs : list<Type>, includeBody : bool) =
      if targs.Length = 0 then this else       
        let typeVarSubst = new Dict<_,_>()
        let varSubst = new Dict<_,_>()

        let toTypeMap (tvs : Dict<TypeVariable, Type>) = function
          | TypeVar tv -> 
            match tvs.TryGetValue tv with
              | true, t -> Some t
              | false, _ -> None
          | _ -> None

        List.iter2 (fun tv t -> typeVarSubst.Add(tv, t)) this.TypeParameters targs 
        let typeMap = toTypeMap typeVarSubst
        let sv (v : Variable) = 
          match v.Type.Subst(typeMap) with
            | None -> v
            | Some t' ->
              let v' = { v with Type = t' } : Variable
              varSubst.Add(v,v')
              v'
        let pars = List.map sv this.Parameters // do this first to populate varSubst
        let se (e : Expr) = e.SubstType(typeMap, varSubst)
        let ses = List.map se
        { this with RetType = this.RetType.ApplySubst(typeMap);
                    Parameters = pars;
                    Requires = ses this.Requires;
                    Ensures = ses this.Ensures;
                    Writes = ses this.Writes;
                    Variants = ses this.Variants;
                    Reads = ses this.Reads;
                    TypeParameters = [];
                    Body = if includeBody then Option.map se this.Body else None }

    member this.CallSubst args =
      let subst = new Dict<_,_>()
      let rec loop = function
        | (p :: pp, v :: vv) ->
          subst.Add (p, v)
          loop (pp, vv)
        | ([], _) -> () // for varargs functions
        | _ -> failwith "wrong number of arguments"
      loop (this.InParameters, args)
      subst

    member this.ToStringWT (showTypes) = 
      let b = StringBuilder()
      let wr (s:string) = b.Append s |> ignore
      if this.IsSpec then wr "spec " else ()
      wr (CustomAttr.AsString this.CustomAttr)
      this.RetType.WriteTo b; wr " "
      doArgsAndTArgsb b (fun (p:Variable) -> p.WriteTo b) (fun (tp:TypeVariable) -> tp.WriteTo b) (this.Name) this.Parameters this.TypeParameters 
      wr "\r\n"
      
      let doList pref lst =
        for (e:Expr) in lst do
          wr "  "; wr pref; wr " ";
          e.WriteTo System.Int32.MinValue showTypes b
          wr ";\r\n";
      doList "requires" (this.Requires)
      doList "ensures" (this.Ensures)
      doList "reads" (this.Reads)
      doList "decreases" (this.Variants)
      doList "writes" (this.Writes)        
        
      b.ToString()              

    override this.ToString () : string = this.ToStringWT(false)
      
  
  and QuantData = 
    {
      Kind:QuantKind;
      Variables:list<Variable>;
      Triggers:list<list<Expr>>;
      Condition:option<Expr>;
      Body:Expr;
      Weight:string;
    }


  and CheckedStatus =
  | Processed
  | Checked
  | Unchecked
    override this.ToString() : string =
      match this with
      | Processed -> ""
      | Checked -> "checked"
      | Unchecked -> "unchecked"

  and Op =
  | Op of string * CheckedStatus
    override this.ToString() : string =
      match this with
      | Op(name, _checked) -> _checked.ToString() + name
    member this.IsEqOrIneq =
      match this with
      | Op("==", _) -> true
      | Op("!=", _) -> true
      | _ -> false
    member this.IsEq =
      match this with
      | Op("==", _) -> true
      | _ -> false
    member this.IsIneq =
      match this with
      | Op("!=", _) -> true
      | _ -> false
    member this.IsChecked =
      match this with
      | Op(_, Checked) -> true
      | _              -> false
    member this.IsUnchecked =
      match this with
      | Op(_, Unchecked) -> true
      | _                -> false
    member this.IsProcessed =
      match this with
      | Op(_, Processed) -> true
      | _                -> false
    member this.OpName =
      match this with
      | Op(opName, _) -> opName

  and ExprCtx =
    {
      IsPure : bool;
    }
    static member PureCtx = { IsPure = true }

  and BlockContract =
    {
      Requires : list<Expr>;
      Ensures : list<Expr>;
      Reads : list<Expr>;
      Writes : list<Expr>;
      Decreases : list<Expr>;
      IsPureBlock : bool
    }

  and TestClassifier = Expr
  
  and Expr =
    | Skip of ExprCommon
    | Ref of ExprCommon * Variable    
    | Prim of ExprCommon * Op * list<Expr>
    | Call of ExprCommon * Function * list<Type> * list<Expr>
    | IntLiteral of ExprCommon * bigint
    | BoolLiteral of ExprCommon * bool
    | Deref of ExprCommon * Expr
    | Dot of ExprCommon * Expr * Field   // computes address of the field
    | Index of ExprCommon * Expr * Expr  // computes address of an array element
    | Cast of ExprCommon * CheckedStatus * Expr   // take the type from ExprCommon
    | Quant of ExprCommon * QuantData
    | Result of ExprCommon
    | This of ExprCommon
    | Old of ExprCommon * Expr * Expr           // the first expression refers to ``when''
    | SizeOf of ExprCommon * Type
    
    // stmt-like expressions
    | VarDecl of ExprCommon * Variable * list<CustomAttr>
    | VarWrite of ExprCommon * list<Variable> * Expr
    | MemoryWrite of ExprCommon * Expr * Expr
    | If of ExprCommon * TestClassifier option * Expr * Expr * Expr
    // invariants * writes * variants * body
    | Loop of ExprCommon * list<Expr> * list<Expr> * list<Expr> * Expr // TODO use record
    | Goto of ExprCommon * LabelId
    | Label of ExprCommon * LabelId
    // token is taken from expr
    | Assert of ExprCommon * Expr * list<list<Expr>>
    | Assume of ExprCommon * Expr
    | Pure of ExprCommon * Expr
    | Block of ExprCommon * list<Expr> * option<BlockContract>
    | Return of ExprCommon * option<Expr>
    | Atomic of ExprCommon * list<Expr> * Expr
    | Comment of ExprCommon * string
    // for now used to mark calls to be interpreted as statements
    | Stmt of ExprCommon * Expr
    
    // This is for expressions with side effects, or expression that get compiled away
    // later. This include:
    //   assignment     =
    //   assignment-op  +=, -=, >>=, ...
    //   address of     &
    //   incr/decr      pre++, pre--, post++, post--
    //   loops
    | Macro of ExprCommon * string * list<Expr>
    | UserData of ExprCommon * obj
    
    member this.ExprEquals (that:Expr) =
      let eq (e0 : Expr) (e1 : Expr) = e0.ExprEquals e1
      let allEq  = List.forall2 (fun (e0 : Expr) (e1 : Expr) -> e0.ExprEquals(e1))
      let allTypeEq = List.forall2 (fun (t0 : Type) (t1 : Type) -> t0 = t1)
      let allVarsEq = List.forall2 (fun (v0 : Variable) (v1 : Variable) -> v0.UniqueId = v1.UniqueId)
      match this, that with
        | Ref(_, v0), Ref(_, v1) -> v0.UniqueId = v1.UniqueId
        | Prim(_, op0, args0), Prim(_, op1, args1) -> op0 = op1 && allEq args0 args1
        | Call(_, fn0, targs0, args0), Call(_, fn1, targs1, args1) -> fn0 = fn1 && allEq args0 args1  && allTypeEq targs0 targs1
        | IntLiteral(_, i0), IntLiteral(_, i1) -> i0 = i1
        | BoolLiteral(_, b0), BoolLiteral(_, b1) -> b0 = b1
        | Deref(_, e0), Deref(_, e1) -> eq e0 e1
        | Dot(_, e0, f0), Dot(_, e1, f1) -> f0.UniqueId = f1.UniqueId && eq e0 e1
        | Index(_, e0, i0), Index(_, e1, i1) -> eq e0 e1 && eq i0 i1
        | Cast(ec0, cs0, e0), Cast(ec1, cs1, e1) -> ec0.Type = ec1.Type && cs0 = cs1 && eq e0 e1
        | Result _, Result _ -> true
        | This _, This _ -> true
        | Old(_, ps0, e0), Old(_, ps1, e1) -> eq ps0 ps1 && eq e0 e1
        | SizeOf(_, t0), SizeOf(_, t1) -> t0 = t1
        | VarDecl(_, v0, _), VarDecl(_, v1, _) -> v0.UniqueId = v1.UniqueId
        | VarWrite(_, vs0, e0), VarWrite(_, vs1, e1) -> allVarsEq vs0 vs1 && eq e0 e1
        | MemoryWrite(_, m0, e0), MemoryWrite(_, m1, e1) -> eq m0 m1 && eq e0 e1
        | If(_, None, c0, t0, e0), If(_, None, c1, t1, e1) -> eq c0 c1 && eq t0 t1 && eq e0 e1
        | Loop(_, e00, e10, e20, e0), Loop(_, e01, e11, e21, e1) ->
          allEq e00 e01 && allEq e10 e11 && allEq e20 e21 && eq e0 e1
        | Goto(_, l0), Goto(_, l1) -> l0.Name = l1.Name
        | Label(_, l0), Label(_, l1) -> l0.Name = l1.Name
        | Assert(_, e0, l0), Assert(_, e1, l1) -> eq e0 e1 && List.forall2 allEq l0 l1
        | Assume(_, e0), Assume(_, e1) -> eq e0 e1
        | Pure(_, e0), Pure(_, e1) -> eq e0 e1
        | Block(_, b0, None), Block(_, b1, None) -> allEq b0 b1
        | Return(_, None), Return(_, None) -> true
        | Return(_, Some(e0)), Return(_, Some(e1)) -> eq e0 e1
        | Atomic(_, l0, e0), Atomic(_, l1, e1) -> allEq l0 l1 && eq e0 e1
        | Comment(_, c0), Comment(_, c1) -> c0 = c1
        | Stmt(_, s0), Stmt(_, s1) -> eq s0 s1
        | Macro(_, m0, args0), Macro(_, m1, args1) -> m0 = m1 && allEq args0 args1
        | UserData(_, o0), UserData(_, o1) -> o0 = o1
        | _,_ -> false

    override this.ToString () = toString (this.WriteTo 0 false)
    
    member this.ToStringWT (showTypes) = toString (this.WriteTo 0 showTypes)
  
    static member MkDot(ec, expr:Expr, field:Field) = 
      let t = match field.Type with | Array(t, _) -> t | t -> t
      let isSpec = match expr.Type with
                    | _ when field.IsSpec -> true
                    | SpecPtr _ -> true
                    | _ -> false
      Expr.Dot({ec with Type = Type.MkPtr(t, isSpec)}, expr, field)
  
    static member MkDot(expr:Expr, field:Field) = Expr.MkDot(expr.Common, expr, field)

    static member SpecCode(stmt:Expr) = Expr.Macro(stmt.Common, "spec", [stmt])
  
    member x.Common =
      match x with
        | Skip(e)
        | Ref (e, _)
        | Prim (e, _, _)
        | Expr.Call (e, _, _, _)
        | IntLiteral (e, _)
        | BoolLiteral (e, _) 
        | Deref (e, _)
        | Dot (e, _, _)
        | Index (e, _, _)
        | Cast (e, _, _)
        | Quant (e, _)
        | Result (e)
        | This(e)
        | Old (e, _, _)        
        | Macro (e, _, _)
        | VarWrite (e, _, _)
        | MemoryWrite (e, _, _)
        | If (e, _, _, _, _)
        | Loop (e, _, _, _, _)
        | Goto (e, _)
        | Label (e, _)
        | Assert (e, _, _)
        | Assume (e, _)
        | Block (e, _, _)
        | Return (e, _)
        | Atomic (e, _, _)
        | Comment (e, _)
        | VarDecl (e, _, _)
        | Stmt (e, _)
        | Pure (e, _)
        | UserData(e, _)
        | SizeOf(e, _)
          -> e

    member x.WithCommon ec =
      match x with
        | Skip(_) -> Skip(ec)
        | Ref (_, r) -> Ref (ec, r)
        | Prim (_, a, b) -> Prim (ec, a, b)
        | Expr.Call (_, a, b, c) -> Expr.Call (ec, a, b, c)
        | IntLiteral (_, a) -> IntLiteral (ec, a)
        | BoolLiteral (_, a)  -> BoolLiteral (ec, a) 
        | Deref (_, a) -> Deref (ec, a)
        | Dot (_, a, b) -> Dot (ec, a, b)
        | Index (_, a, b) -> Index (ec, a, b)
        | Cast (_, a, b) -> Cast (ec, a, b)
        | Quant (_, a) -> Quant (ec, a)
        | Result (_) -> Result (ec)
        | This (_) -> This (ec)
        | Old (_, a, b) -> Old (ec, a, b)        
        | Macro (_, a, b) -> Macro (ec, a, b)
        | VarWrite (_, a, b) -> VarWrite (ec, a, b)
        | MemoryWrite (_, a, b) -> MemoryWrite (ec, a, b)
        | If (_, a, b, c, d) -> If (ec, a, b, c, d)
        | Loop (_, a, b, c, d) -> Loop (ec, a, b, c, d)
        | Goto (_, a) -> Goto (ec, a)
        | Label (_, a) -> Label (ec, a)
        | Assert (_, a, b) -> Assert (ec, a, b)
        | Assume (_, a) -> Assume (ec, a)
        | Block (_, a, b) -> Block (ec, a, b)
        | Return (_, a) -> Return (ec, a)
        | Atomic (_, a, b) -> Atomic (ec, a, b)
        | Comment (_, a) -> Comment (ec, a)
        | VarDecl (_, a, attr) -> VarDecl (ec, a, attr)
        | Stmt (_, a) -> Stmt (ec, a)
        | Pure (_, a) -> Pure (ec, a)
        | UserData(_, a) -> UserData(ec, a)
        | SizeOf(_, a) -> SizeOf (ec, a)

    member this.Visit (ispure : bool, f: ExprCtx -> Expr -> bool) : unit =
      let rec visit ctx e =
        if f ctx e then
          match e with
            | Skip _
            | Return (_, None)
            | Goto _
            | Label _
            | Comment _ 
            | Ref _
            | IntLiteral _
            | BoolLiteral _
            | VarDecl _
            | Macro(_, _, [])
            | Call(_, _, _, [])
            | UserData _
            | SizeOf _
            | This _
            | Result _ -> ()
            | Prim (_, _, es)
            | Block (_, es, None)
            | Call (_, _, _, es)
            | Macro (_, _, es) -> List.iter (visit ctx) es
            | Deref (_, e)
            | Dot (_, e, _)
            | VarWrite (_, _, e)
            | Stmt (_, e)
            | Return (_, Some e)
            | Cast (_, _, e) -> visit ctx e
            | Pure (_, e) 
            | Assume (_, e) -> paux e
            | Assert (_, e, trigs) -> List.iter pauxs trigs; paux e
            | MemoryWrite (_, e1, e2) 
            | Index (_, e1, e2) -> visit ctx e1; visit ctx e2
            | Old (_, e1, e2) -> paux e1; visit ctx e2
            | Quant (_, q) -> List.iter pauxs q.Triggers; Option.iter paux q.Condition; paux q.Body
            | If (_, None, cond, s1, s2) -> visit ctx cond; visit ctx s1; visit ctx s2
            | If (_, Some classif, cond, s1, s2) -> paux classif; visit ctx cond; visit ctx s1; visit ctx s2
            | Loop (_, invs, writes, variants, s) -> pauxs invs; pauxs writes; pauxs variants; visit ctx s
            | Atomic (c, exprs, s) -> pauxs exprs; visit ctx s
            | Block (ec, es, Some cs) -> pauxs cs.Requires; pauxs cs.Ensures; pauxs cs.Reads; pauxs cs.Writes; pauxs cs.Decreases; List.iter (visit ctx) es


      and paux = visit ExprCtx.PureCtx
      and pauxs = List.iter (visit ExprCtx.PureCtx)
        
      visit { IsPure = ispure } this  

    member this.SelfCtxVisit (ispure : bool, f : ExprCtx -> (Expr -> unit) -> Expr -> bool) : unit =        
      let rec aux ctx (e:Expr) = e.Visit (ispure, f')
      and f' ctx e = f ctx (aux ctx) e
      this.Visit (ispure, f')

    member this.SelfVisit (f : (Expr -> unit) -> Expr -> bool) : unit =        
      let rec aux ctx (e:Expr) = e.Visit (false, f')
      and f' ctx e = f (aux ctx) e
      this.Visit (false, f')
    
    member this.HasSubexpr (f : Expr -> bool) : bool =
      let found = ref false
      let check _ expr =
        if !found then false
        elif f expr then
          found := true
          false
        else true
      this.SelfVisit check
      !found
          
       

    /// When f returns Some(x), this is replaced by x, otherwise Map is applied
    /// recursively to children, including application of g to children expressions.
    member this.Map (ispure : bool, f : ExprCtx -> Expr -> option<Expr>) : Expr =        
      let rec map ctx e =
        let apply f args =        
          let foundSome = ref false
          let supplyDefault arg =
            match f arg with
              | None -> arg
              | Some arg' -> foundSome := true; arg'
          let args' = List.map supplyDefault args 
          !foundSome, args'

        let applyList f argsLists =
          let foundSome = ref false
          let apply' args =
            match apply f args with
              | true, args' -> foundSome := true; args'
              | false, args' -> args'
          let argsLists' = List.map apply' argsLists
          !foundSome, argsLists'

        let supplyDefault arg defArg = 
          match arg with 
            | Some arg' -> arg'
            | None -> defArg

        let construct1 ctor arg =
          match arg with
            | None -> None
            | Some arg' -> Some (ctor arg')
        let construct2 ctor arg1 arg2 defArg1 defArg2 =
          match arg1, arg2 with
            | None, None -> None
            | _ -> Some (ctor (supplyDefault arg1 defArg1) (supplyDefault arg2 defArg2) )
        let construct3 ctor arg1 arg2 arg3 defArg1 defArg2 defArg3=
          match arg1, arg2, arg3 with
            | None, None, None -> None
            | _ -> Some (ctor (supplyDefault arg1 defArg1) (supplyDefault arg2 defArg2) (supplyDefault arg3 defArg3))
        let constructList ctor f args =
          match apply f args with
            | false, _ -> None
            | true, args' -> Some(ctor args')
        match f ctx e with
          | Some e as se -> se
          | None ->
            match e with
              | Skip _
              | Return (_, None)
              | Goto _
              | Label _
              | Comment _ 
              | Ref _
              | IntLiteral _
              | BoolLiteral _
              | VarDecl _
              | Macro(_, _, [])
              | Call(_, _, _, [])
              | UserData _
              | SizeOf _
              | This _
              | Result _ -> None
              | Prim (c, op, es) ->  constructList (fun args ->  Prim (c, op, args)) (map ctx) es
              | Call (c, fn, tas, es) -> constructList  (fun args -> Call (c, fn, tas, args)) (map ctx) es
              | Macro (c, op, es) -> constructList (fun args -> Macro (c, op, args)) (map ctx) es
              | Deref (c, e) -> construct1 (fun arg ->  Deref (c, arg)) (map ctx e)
              | Dot (c, e, f) -> construct1 (fun arg -> Dot (c, arg, f)) (map ctx e)
              | Index (c, e1, e2) -> construct2 (fun arg1 arg2 -> Index (c, arg1, arg2)) (map ctx e1) (map ctx e2) e1 e2
              | Cast (c, ch, e) -> construct1 (fun arg -> Cast (c, ch, arg)) (map ctx e)
              | Old (c, e1, e2) -> construct2 (fun arg1 arg2 -> Old (c, arg1, arg2)) (paux e1) (map ctx e2) e1 e2
              | Quant (c, q) ->
                let rTriggers, triggers = applyList paux q.Triggers
                let rCond, cond = 
                  match q.Condition with
                    | None -> false, None
                    | Some cond -> 
                      match paux cond with
                        | None -> false, Some cond
                        | Some cond' -> true, Some cond'
                let rBody, body = 
                  match paux q.Body with
                    | None -> false, q.Body
                    | Some body' -> true, body'
                if not rTriggers && not rCond && not rBody then None 
                else Some(Quant (c, { q with Triggers = triggers; Condition = cond; Body = body }))
              | VarWrite (c, v, e) -> construct1 (fun arg -> VarWrite (c, v, arg)) (map ctx e)
              | MemoryWrite (c, e1, e2) -> construct2 (fun arg1 arg2 -> MemoryWrite (c, arg1, arg2)) (map ctx e1) (map ctx e2) e1 e2
              | Assert (c, e, trigs) -> 
                let rTriggers, triggers = applyList paux trigs
                let rCond, cond = match paux e with | None -> false, e | Some e' -> true, e'
                if not rTriggers && not rCond then None
                else Some(Assert(c, cond, triggers))
              | Assume (c, e) -> construct1 (fun arg -> Assume (c, arg)) (paux e)
              | Return (c, Some e) -> construct1 (fun arg -> Return (c, Some arg)) (map ctx e)
              | If (c, cl, cond, s1, s2) -> construct3 (fun a1 a2 a3 -> If (c, cl, a1, a2, a3)) (map ctx cond) (map ctx s1) (map ctx s2) cond s1 s2
              | Loop (c, invs, writes, variants, s) -> 
                let rInvs, invs' = apply paux invs
                let rWrites, writes' = apply paux writes
                let rVariants,variants' = apply paux variants
                let rS, s' = match map ctx s with | None -> false, s | Some s' -> true, s'
                if not rInvs && not rWrites && not rVariants && not rS then None else Some(Loop(c, invs', writes', variants', s'))
              | Atomic (c, exprs, s) -> 
                let rExprs, exprs' = apply paux exprs
                let rS, s' = match map ctx s with | None -> false, s | Some s' -> true, s'
                if not rExprs && not rS then None else Some(Atomic(c, exprs', s'))
              | Block (c, ss, None) as b -> constructList (fun args-> Block (c, args, None)) (map ctx) ss
              | Block (c, ss, Some cs) as b ->
                let rPres, pres' = apply paux cs.Requires
                let rPosts, posts' = apply paux cs.Ensures
                let rReads, reads' = apply paux cs.Reads
                let rWrites, writes' = apply paux cs.Writes
                let rDecreases, decreases' = apply paux cs.Decreases
                let cs' = {Requires=pres'; Ensures=posts'; Reads=reads'; Writes=writes'; Decreases=decreases'; IsPureBlock = cs.IsPureBlock }
                let rSS, block'' =
                    match  constructList (fun args -> Block (c, args, Some cs')) (map ctx) ss with
                      | None -> false, Block (c,ss,Some cs')
                      | Some x -> true, x
                if not (rPres || rPosts || rReads || rWrites|| rDecreases || rSS) then None else Some block''
              | Stmt (c, e) -> construct1 (fun arg -> Stmt (c, arg)) (map ctx e)
              | Pure (c, e) -> construct1 (fun arg -> Pure (c, arg)) (paux e)
      and paux = map ExprCtx.PureCtx
      
      match map { IsPure = ispure } this with
        | None -> this
        | Some this' -> this'
    
    // TODO: implement with DeepMap?
    member this.SubstType(typeMap, varSubst : Dict<Variable, Variable>) =
      let sc c = { c with Type = c.Type.ApplySubst(typeMap) } : ExprCommon
      let varSubst = new Dict<_,_>(varSubst) // we add to it, so make a copy first
      let sv v = 
        match varSubst.TryGetValue(v) with
          | true, v' -> v'
          | false, _ ->
            match v.Type.Subst(typeMap) with
              | Some t' ->
                let v' = { v with Type = t' }
                varSubst.Add(v,v')
                v'
              | None -> v
      let repl self = 
        let selfs = List.map self
        function
          | Skip _
          | Return (_, None) 
          | Goto _
          | Label _
          | Comment _
          | IntLiteral _
          | BoolLiteral _
          | UserData _
          | MemoryWrite _
          | Assert _
          | Assume _
          | Pure _
          | Block _ 
          | Stmt _
          | If _
          | Atomic _
          | Loop _  -> None
          | Ref(c, v) -> Some(Ref(sc c, sv v))
          | VarDecl(c, v, attr) -> Some(VarDecl(c, sv v, attr))
          | Result c -> Some(Result(sc c))
          | This c -> Some(This(sc c))
          | Prim (c, op, es) ->  Some(Prim(sc c, op, selfs es))
          | Call (c, fn, tas, es) -> Some(Call(sc c, fn, List.map (fun (t : Type) -> t.ApplySubst(typeMap)) tas, selfs es))
          | Macro (c, op, es) -> Some(Macro(sc c, op, selfs es))
          | Deref (c, e) -> Some(Deref(sc c, self e))
          | Dot (c, e, f) -> Some(Dot(sc c, self e, f))
          | Index (c, e1, e2) -> Some(Index(sc c, self e1, self e2))
          | Cast (c, ch, e) -> Some(Cast(sc c, ch, self e))
          | Old (c, e1, e2) -> Some(Old(sc c, self e1, self e2))
          | Quant (c, q) -> Some(Quant(sc c, {q with Triggers = List.map selfs q.Triggers; Condition = Option.map self (q.Condition); Body = self (q.Body)}))
          | VarWrite (c, vs, e) -> Some(VarWrite(sc c, List.map sv vs, self e))
          | Return (c, Some e) -> Some(Return(sc c, Some(self e)))
          | SizeOf(c, t) -> Some(SizeOf(c, t.ApplySubst(typeMap)))
      this.SelfMap(repl)

    member this.SelfCtxMap (ispure : bool, f : ExprCtx -> (Expr -> Expr) -> Expr -> option<Expr>) : Expr =        
      let rec aux ctx (e:Expr) = e.Map (ispure, f')
      and f' ctx e = f ctx (aux ctx) e
      this.Map (ispure, f')

    member this.SelfMap (f : (Expr -> Expr) -> Expr -> option<Expr>) : Expr =        
      let rec aux ctx (e:Expr) = e.Map (false, f')
      and f' ctx e = f (aux ctx) e
      this.Map (false, f')

    member this.Subst (subst : System.Collections.Generic.Dictionary<Variable, Expr>) =
      let repl self =
        let substVar v = 
          match subst.TryGetValue(v) with
            | true, Ref(_, v') -> v'
            | true, _ -> die()
            | _ -> v
        function
          | Ref (_, v) -> 
            match subst.TryGetValue v with
              | true, e -> Some (e)
              | _ -> None
          | VarDecl (c, v, _) when subst.ContainsKey v -> Some (Block (c, [], None))
          | VarWrite (c, v, e) -> Some (VarWrite (c, List.map substVar v, self e))
          | _ -> None
      this.SelfMap repl
                
    member this.Type = this.Common.Type
    member this.Token = this.Common.Token
    
    member this.ApplyToChildren f =
      let fs = List.map f
      match this with
        | Skip _
        | Return (_, None)
        | Goto _
        | Label _
        | Comment _ 
        | Ref _
        | IntLiteral _
        | BoolLiteral _
        | VarDecl _
        | Macro(_, _, [])
        | Call(_, _, _, [])
        | UserData _
        | SizeOf _
        | This _
        | Result _ -> this
        | Prim (c, op, es) ->  Prim (c, op, fs es)
        | Call (c, fn, tas, es) -> Call (c, fn, tas, fs es)
        | Macro (c, op, es) -> Macro (c, op, fs es)
        | Deref (c, e) -> Deref (c, f e)
        | Dot (c, e, fld) -> Dot (c, f e, fld)
        | Index (c, e1, e2) -> Index (c, f e1, f e2)
        | Cast (c, ch, e) -> Cast (c, ch, f e)
        | Old (c, e1, e2) -> Old (c, f e1, f e2)
        | Quant (c, q) ->
          Quant (c, 
            {q with 
              Condition = Option.map f q.Condition
              Body = f q.Body
              Triggers = List.map fs q.Triggers
            })
        | VarWrite (c, v, e) -> VarWrite (c, v, f e)
        | MemoryWrite (c, e1, e2) -> MemoryWrite (c, f e1, f e2)
        | Assert (c, e, trigs) -> Assert (c, f e, List.map fs trigs)
        | Assume (c, e) -> Assume (c, f e)
        | Return (c, Some e) -> Return (c, Some (f e))
        | If (c, cl, cond, s1, s2) -> If (c, Option.map f cl, f cond, f s1, f s2)
        | Loop (c, invs, writes, variants, s) -> 
          Loop (c, fs invs, fs writes, fs variants, f s)
        | Atomic (c, exprs, s) -> Atomic (c, fs exprs, f s)
        | Block (c, ss, None) -> Block (c, fs ss, None)
        | Block (c, ss, Some cs) as b ->
          let cs = 
            { cs with 
                Requires = fs cs.Requires 
                Ensures = fs cs.Ensures 
                Reads = fs cs.Reads
                Writes = fs cs.Writes
                Decreases = fs cs.Decreases
                }
          Block (c, fs ss, Some cs)
        | Stmt (c, e) -> Stmt (c, f e)
        | Pure (c, e) -> Pure (c, f e)

    member this.WriteTo (ind:int) (showTypes:bool) (b:StringBuilder) : unit =
      
      let rec wt (ind:int) (outerType:Type) (e:Expr) = 
      
        let f = wt (ind + 2) e.Type
        let fe = wt System.Int32.MinValue e.Type
        let wr = wrb b
        let doArgs = doArgsb b fe
        let doInd ind = 
          if ind > 0 then wr (System.String(' ', ind))
        let wrTriggers = List.iter (fun trigs -> wr "{ "; commas b fe trigs;  wr " } ")
        let showType = showTypes && e.Type <> Type.Bogus && e.Type <> Type.Void && e.Type <> outerType
        doInd ind
        if showType then wr "("
        match e with
          | Skip _ -> wr "skip;\r\n"
          | Ref (_, v) -> wr (v.Name)
          | Prim (_, op, args) -> doArgs (op.ToString()) args
          | Expr.Call (_, fn, tArgs, args) -> doArgsAndTArgsb b  fe (fun (t:Type) -> t.WriteTo b) fn.Name args tArgs
          | BoolLiteral (_, v) -> wr (if v then "true" else "false")
          | IntLiteral (_, l) -> wr (l.ToString())
          | Deref (_, e) -> wr "*("; fe e; wr ")"
          | Dot (_, e, fld) -> 
            let fieldName = if fld.Name <> "" then fld.Name else "'" + (fld.ToString()) + "'"
            wr "("; fe e; wr "->"; wr fieldName; wr ")"
          | Index (_, e, off) -> fe e; wr "["; fe off; wr "]"
          | Cast (ec, ch, e) -> 
            let cs = ch.ToString()
            let cs = if cs <> "" then cs + " " else cs
            wr "("; wr cs; wr (ec.Type.ToString()); wr ")"; fe e;
          | Quant (_, q) ->
            match q.Kind with
              | Exists -> wr "exists("
              | Forall -> wr "forall("
              | Lambda -> wr "lambda("
            for v in q.Variables do
              wr (v.Type.ToString())
              wr " "
              wr v.Name
              wr "; "
            wrTriggers q.Triggers
            match q.Condition with
              | Some e -> fe e; wr "; "
              | None -> ()
            fe q.Body
            wr ")"
          | Result _ -> wr "result"
          | This _ -> wr "this"
          | Old (_, w, e) -> doArgs "old" [w; e]
          | Pure (_, e) -> doArgs "pure" [e]
          | Expr.Macro (_, op, args) -> 
              match args with 
                  | [] -> wr "@"; wr op
                  | _ -> doArgs ("@" + op) args
          | VarDecl (_, v, _) ->
            wr (v.Type.ToString()); wr " "; wr v.Name; wr ";\r\n"
          | VarWrite (_, [v], e) ->
            wr v.Name; wr " := "; fe e; wr ";\r\n"
          | VarWrite (_, vs, e) -> 
            let bogus = { Type = Type.Void; Token = Token.NoToken } : ExprCommon
            doArgs "" (List.map (fun v -> Ref(bogus, v)) vs); wr " = "; fe e; wr ";\r\n"
          | MemoryWrite (_, d, s) ->
            wr "*"; fe d; wr " := "; fe s; wr ";\r\n"
          | Goto (_, l) -> wr "goto "; wr l.Name; wr ";\r\n"
          | Label (_, l) -> wr l.Name; wr ":\r\n"
          | Assert (_, e, trigs) -> wr "assert "; fe e; wr ";\r\n"
          | Assume (_, e) -> wr "assume "; fe e; wr ";\r\n"
          | Return (_, Some (e)) -> wr "return "; fe e; wr ";\r\n"
          | Return (_, None) -> wr "return;\r\n"
          | If (_, None, cond, th, el) ->
            wr "if ("; fe cond; wr ")\r\n"; f th; doInd ind; wr "else\r\n"; f el
          | If (_, Some cl, cond, th, el) ->
            wr "if as_high("; fe cl; wr ", "; fe cond;  wr ")\r\n"; f th; doInd ind; wr "else\r\n"; f el
          | Loop (_, invs, writes, variants, body) ->
            wr "loop\r\n";
            for i in invs do
              doInd (ind + 4)
              wr "invariant ";
              fe i;
              wr ";\r\n"
            for w in writes do
              doInd (ind + 4)
              wr "writes ";
              fe w;
              wr ";\r\n"
            for r in variants do
              doInd (ind + 4)
              wr "decreases ";
              fe r;
              wr ";\r\n"
            f body        
          | Atomic (c, args, body) ->
            doArgs "atomic" args
            f (Block (c, [body], None))
          | Block (_, stmts, None) ->
            wr "{\r\n";
            for s in stmts do 
              match s with
                | Macro (_, _, _) -> 
                  f s
                  wr "\r\n"
                | _ -> f s
            doInd ind
            wr "}\r\n"
          | Block (_, stmts, Some cs) ->
            wr "block // with contracts, not correct \r\n";
            let macroPrint prep s app =
              match s with
                | Macro(_, _, _) ->
                  wr prep; f s; wr app
                | _ -> wr prep; f s; wr app // Should do something else, too many line breaks.
            for s in cs.Requires do
              macroPrint "requires(" s ")\r\n"
            for s in cs.Ensures do
              macroPrint "ensures(" s ")\r\n"
            for s in cs.Reads do
              macroPrint "reads(" s ")\r\n"
            for s in cs.Writes do
              macroPrint "writes(" s ")\r\n"
            for s in cs.Decreases do
              macroPrint "variant(" s ")\r\n" // Is this right?
            wr "{\r\n"
            for s in stmts do
              macroPrint "" s "\r\n"
            doInd ind
            wr "}\r\n"
          | Stmt (_, e) ->
            wr "stmt "
            fe e
            wr ";\r\n"
          | Comment (_, s) ->
            wr "// "; wr s; wr "\r\n"
          | UserData (_, o) ->
            wr "userdata("; wr (o.ToString()); wr ") : "; wr (o.GetType().Name)
          | SizeOf(_, t) ->
            wr "sizeof("; wr (t.ToString()); wr ")"
        if showType then wr " : "; wr (e.Type.ToString()); wr ")"
      wt ind Type.Bogus this
          
  let (|ETrue|_|) = function
      | BoolLiteral (_, true) -> Some (ETrue)
      | _ -> None
    
  let (|EFalse|_|) = function
      | BoolLiteral (_, false) -> Some (EFalse)
      | _ -> None
    
  let (|Ptr|_|) = function
      | PhysPtr t  
      | SpecPtr t -> Some(t)
      | _ -> None
      
  let (|PtrSoP|_|) = function
    | PhysPtr t -> Some(t,false)
    | SpecPtr t -> Some(t,true)
    | _ -> None
    
  let (|MathTypeRef|_|) = function
    | Type.Ref ({ Name = n; Kind = MathType }) -> Some (MathTypeRef n)
    | _ -> None
    
  let bogusEC = { Token = bogusToken; Type = Type.Bogus } : ExprCommon
  // there is an initialization bug in the F# compiler, it seems
  // that this code is executed before the Type class if fully constructed
  // and thus we get null as Type instead of Bool/Void (they are unitary)
  let voidBogusEC () = { bogusEC with Type = Void }
  let boolBogusEC () = { bogusEC with Type = Bool }
  let intBogusEC () = { bogusEC with Type = MathInteger Signed }
  type ExprCommon with
    static member Bogus = bogusEC
  
  let bogusExpr = Expr.Macro (ExprCommon.Bogus, "bogus", [])
  type Expr with    
    static member Bogus = bogusExpr
    
    static member True = BoolLiteral(boolBogusEC(), true)
    static member False = BoolLiteral(boolBogusEC(), false)
    
    static member MkBlock exprs =
      let rec last = function
        | [x] -> x
        | _ :: xs -> last xs
        | [] -> die()
      match exprs with
        | [e] -> e
        | [] -> Skip(bogusEC)
        | stmts -> 
          let lstmt = last stmts 
          Block ({ bogusEC with Type = lstmt.Type; Token = lstmt.Token }, stmts, None)
  
    static member MkAssert (expr:Expr) =
      Assert ({ expr.Common with Type = Void }, expr, [])
    
    static member MkAssume (expr:Expr) =
      Assume ({ expr.Common with Type = Void }, expr)
      
    static member ToUserData (o:obj) =
      assert (o <> null)
      UserData(ExprCommon.Bogus, o)

    // First computes "f this", and then applies itself recursively to all subexpressions of "f this".
    member this.DeepMap (f : Expr -> Expr) : Expr =
      let rec aux (prev:obj) (ctx:ExprCtx) (e:Expr) = 
        if obj.ReferenceEquals (prev, e) then None
        else 
          let e = f e
          Some (e.Map (ctx.IsPure, aux e))
      this.Map (false, aux null)
     
  let (|FunctionPtr|_|) = function
    | Ptr (Type.Ref { Kind = FunctDecl f }) -> Some f
    | _ -> None
  
  type Type with
    member this.IsFunctionPtr =
      match this with
        | FunctionPtr _ -> true
        | _ -> false

  type [<ReferenceEquality>] Top =
    | Global of Variable * Expr option
    | TypeDecl of TypeDecl
    | FunctionDecl of Function
    | Axiom of Expr
    | GeneratedAxiom of Expr * Top
    
    // override this.Equals (o:obj) = LanguagePrimitives.PhysicalEquality (this :> obj) o
    // override this.GetHashCode () = LanguagePrimitives.PhysicalHash this
    
    member this.Token =
      match this with
        | Global(v, Some e) -> e.Token
        | Global(v, None) -> Token.NoToken
        | TypeDecl d -> d.Token
        | FunctionDecl d -> d.Token
        | Axiom e -> e.Token
        | GeneratedAxiom(e, _) -> e.Token
    
    override this.ToString () = toString (this.WriteTo false)
    member this.ToStringWT (showTypes : bool) = toString (this.WriteTo showTypes)
    
    member this.WriteTo showTypes b =
      let wr = wrb b
      match this with
        | Global (v, None) -> wr (v.ToString() + ";\r\n")
        | Global (v, Some e) -> wr (v.ToString()); wr " = "; e.WriteTo System.Int32.MinValue false b; wr ";\r\n"
        | TypeDecl d -> wr (d.Declaration())
        | FunctionDecl d -> 
          wr (d.ToStringWT(showTypes))
          match d.Body with
            | Some e ->
              e.WriteTo 0 showTypes b
              wr "\r\n"
            | None -> ()
        | Axiom e -> wr "axiom "; e.WriteTo System.Int32.MinValue showTypes b; wr ";\r\n"
        | GeneratedAxiom(e, origin) ->
          wr "axiom (from "; wr (origin.ToString()); wr ") "; e.WriteTo System.Int32.MinValue showTypes b; wr ";\r\n"
    
    member this.MapExpressions f =
      let pf = f true
      let pfs = List.map pf      
      match this with
        | Top.Axiom e -> Top.Axiom (pf e)
        | Top.GeneratedAxiom(e, origin) -> Top.GeneratedAxiom(pf e, origin)
        | Top.FunctionDecl x ->
          // do the body first, so the function can see VarDecls for parameters
          // before they are actually used in contracts
          x.Body <- Option.map (f false) x.Body
          x.Requires <- pfs x.Requires
          x.Ensures <- pfs x.Ensures
          x.Reads <- pfs x.Reads
          x.Writes <- pfs x.Writes
          x.Variants <- pfs x.Variants
          this
        | Top.TypeDecl td ->
          td.Invariants <- pfs td.Invariants; this
        | Top.Global(v, Some e) -> Top.Global(v, Some(pf e))
        | Top.Global(_, None) -> this

    member this.VisitExpressions f =
      let pf = f true
      let pfs = List.iter pf      
      match this with
        | Top.Axiom e -> pf e
        | Top.GeneratedAxiom(e, origin) -> pf e
        | Top.FunctionDecl x ->
          Option.iter (f false) x.Body
          pfs x.Requires
          pfs x.Ensures
          pfs x.Reads
          pfs x.Writes
          pfs x.Variants
        | Top.TypeDecl td -> pfs td.Invariants
        | Top.Global(v, Some e) -> pf e
        | Top.Global(_, None) -> ()

  let mapExpressions f decls =
    List.map (fun (d:Top) -> d.MapExpressions f) decls
  
  let optExprMap f = Option.map (fun (e:Expr) -> e.SelfMap f)
  
  let deepMapExpressionsCtx f decls =
    let aux ispure (e:Expr) =
      e.SelfCtxMap (ispure, f)
    mapExpressions aux decls
  
  let deepMapExpressions f decls =
    let aux _ (e:Expr) =
      e.SelfMap f
    mapExpressions aux decls
  
  let visitExpressions f decls = 
    List.iter (fun (d:Top) -> d.VisitExpressions f) decls
  
  let deepVisitExpressionsCtx f decls =
    let aux ispure (e:Expr) =
      e.SelfCtxVisit (ispure, f)
    visitExpressions aux decls
  
  let deepVisitExpressions f decls =
    let aux _ (e:Expr) =
      e.SelfVisit f
    visitExpressions aux decls

  let deepMapDecl f decl =
    match [decl] |> deepMapExpressions f with
      | [decl'] -> decl'
      | _ -> die()

  // -----------------------------------------------------------------------------
  // Message/token formatting
  // -----------------------------------------------------------------------------
 
  let forwardingToken tok related (getmsg : unit -> string) =
    { Token = (new ForwardingToken (tok, related, getmsg) :> Token)
      Type = Type.Bool } : ExprCommon
  
  //
  // "id" numbers
  //      
  // Verification errors:  between 8001 and 8499: First available: 8034
  // Assertions:           between 8501 and 8999: First available: 8540
  //

  let afmt (id:int) fmt (args : list<string>) =
    System.String.Format ("#VCCERR:{0:0000}#", id) +
      System.String.Format (fmt, [| for a in args -> (a :> obj) |])

  let afmtt tok id fmt args = forwardingToken tok None (fun () -> afmt id fmt args)
  
  let afmte id fmt (args : list<Expr>) =
    forwardingToken args.Head.Token None (fun () -> afmt id fmt [ for a in args -> a.Token.Value ])
  
  let afmter id fmt primary related (args : list<Expr>) =
    forwardingToken primary related (fun () -> afmt id fmt [ for a in args -> a.Token.Value ])

  let rec splitConjunctionEx keepLabels expr = 
    let splitConjunction = splitConjunctionEx keepLabels
    match expr with
      | Macro (c, "labeled_invariant", [lab; i]) -> 
        if keepLabels then
          splitConjunction i |> List.map (fun i -> Macro (c, "labeled_invariant", [lab; i]))
        else
          splitConjunction i
      | Macro (_, "ite", [a; b; EFalse])
      | Prim (_, Op ("&&", _), [a; b]) -> (splitConjunction a) @ (splitConjunction b)
      | Macro (_, "ite", [a; b; ETrue])
      | Prim (_, Op ("==>", _), [a; b]) as expr ->
        match splitConjunction b with
          | [_] -> [expr]
          | lst ->
            let mkOne (e:Expr) =
              let t = forwardingToken e.Token None (fun () -> a.Token.Value + " ==> " + e.Token.Value)
              Prim ({ e.Common with Token = t.Token }, Op ("==>", Processed), [a; e])
            List.map mkOne lst
      | x -> [x]
  
  let splitConjunction = splitConjunctionEx false
  
  let hasCustomAttr n = List.exists (function VccAttr (n', _) -> n = n' | _ -> false)

  let mkBoolOp str (args:list<Expr>) =
    Prim ((List.head (List.rev args)).Common, Op(str, Processed), args)

  let mkAnd a b = mkBoolOp "&&" [a; b]
  let mkOr a b = mkBoolOp "||" [a; b]
  let mkImpl a b = mkBoolOp "==>" [a; b]
  let mkNot a = mkBoolOp "!" [a]
  let mkEq a b = Expr.Prim(boolBogusEC(), Op.Op("==", CheckedStatus.Unchecked), [a; b])
  
  let isLemmaInv = function
    | Macro(_, "labeled_invariant", [Macro(_, "lemma", []); i]) -> true
    | _ -> false

  let possiblyUnreachable = Expr.MkAssert (Macro (boolBogusEC(), "_vcc_possibly_unreachable", []))
  
