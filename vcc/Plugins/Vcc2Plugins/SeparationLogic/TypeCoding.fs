//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
  module CAST = Microsoft.Research.Vcc2.CAST
  module CoreC = Microsoft.Research.Vcc2.CoreCAST
  
  module TypeCoding =
  
    // encode type information in names sent to prover
    let mutable encodeTypes = true;
    
    let rec toTypeString t =
      match t with
        | CAST.Type.Void -> "void"
        | CAST.Type.Integer kind -> (CAST.Type.IntSuffix kind)
        | CAST.Type.Primitive kind -> (CAST.Type.PrimSuffix kind) 
        | CAST.Type.Bool -> "bool"
        | CAST.Type.Ptr tp -> "*" + (toTypeString tp)
//        | CAST.Type.Ref { Name = n; Kind = (CAST.MathType|CAST.FunctDecl _) } -> "$^" + n
        | CAST.Type.Ref td -> "^" + td.Name
        | CAST.Type.Array (tp, sz) -> "[" + sz.ToString() + "]" + (toTypeString tp)
        | CAST.Type.TypeIdT -> "$typeid_t"
        | CAST.Type.Claim -> "$claim_t"
        | CAST.Type.Map (range, dom) -> "$map_t[" + (toTypeString dom) + "]" + (toTypeString range)
        | CAST.Type.ObjectT -> "$object_t"

    let rec fromTypeString (t:string) =
      match t.Trim([|'_';' '|]) with
        | "bool" -> CAST.Type.Bool
        | "i1" -> CAST.Type.Integer CAST.IntKind.Int8
        | "i2" -> CAST.Type.Integer CAST.IntKind.Int16
        | "i4" -> CAST.Type.Integer CAST.IntKind.Int32
        | "i8" -> CAST.Type.Integer CAST.IntKind.Int64
        | "u1" -> CAST.Type.Integer CAST.IntKind.UInt8
        | "u2" -> CAST.Type.Integer CAST.IntKind.UInt16
        | "u4" -> CAST.Type.Integer CAST.IntKind.UInt32
        | "u8" -> CAST.Type.Integer CAST.IntKind.UInt64
        | "f4" -> CAST.Type.Primitive CAST.PrimKind.Float32
        | "f8" -> CAST.Type.Primitive CAST.PrimKind.Float64
        | "void" -> CAST.Type.Void
        | "$typeid_t" -> CAST.Type.TypeIdT
        | "$claim_t" -> CAST.Type.Claim
        | "$object_t" -> CAST.Type.ObjectT
        | t when t.StartsWith "*" -> CAST.Type.Ptr (fromTypeString (t.Substring 1))
        | t when t.StartsWith "[" -> 
          let sizePos = t.IndexOf "]"
          CAST.Type.Array (fromTypeString (t.Substring (sizePos + 1)), 
                           System.Int32.Parse (t.Substring (1, sizePos - 1)))
        | t when t.StartsWith "$map_t[" -> 
          let domPos = t.IndexOf "]"
          CAST.Type.Map (fromTypeString (t.Substring (domPos + 1)),
                         fromTypeString (t.Substring (7, domPos - 7)))
        | t when t.StartsWith "^" -> 
          CAST.Type.Ref { new  CAST.TypeDecl // Name is the only field we are interested here in
                          with Token = CAST.bogusToken 
                          and  Kind = CAST.Struct
                          and  Name =  t.Substring 1
                          and  Fields = []
                          and  Invariants = []
                          and  CustomAttr = []
                          and  SizeOf = 1
                          and  IsNestedAnon = false
                          and  GenerateEquality = CAST.StructEqualityKind.NoEq
                          and  GenerateFieldOffsetAxioms = false
                          and  Parent = None
                        }
        | _ -> failwith "fromTypeString match"


    let encodeVarType (t:CAST.Type) =
      if encodeTypes then
        toTypeString t + ":"
      else
        ""

    let encodeFunctionType (rt:CAST.Type, ats:list<CAST.Type>) =
      if encodeTypes then
        let atsEncoded =
          match ats with
            | [] -> ""
            | [at] -> toTypeString at
            | hd::tl -> (toTypeString hd) +
                        (List.fold_left 
                        (fun (acc:string) (t:CAST.Type) -> acc + "," + (toTypeString t)) 
                         "" tl)
        "(" + atsEncoded + ")" + (toTypeString rt)
      else
        ""

    let isTypeEncoded (s:string) =
      (s <> "") && (s.Contains ":" || (s.Contains "(" && s.Contains ")"))
    
    let splitEncodedString (s:string) =
      if isTypeEncoded s then
        let splitArr = (s.Trim()).Split([|':'|])
        assert (splitArr.Length = 2)
        let splitList = List.of_array splitArr
        (splitList.Head, (splitList.Tail).Head)
      else
        ("", s)

    let decodeVarType (typeEnc:string) =
      if encodeTypes && typeEnc <> "" then
        Some (fromTypeString typeEnc)
      else
        None

    let decodeFunctionType (typeEnc:string) =
      if encodeTypes && isTypeEncoded typeEnc then
        let retPos = typeEnc.IndexOf ")"
        let ats =
          match retPos with
            | 1 -> []
            | _ -> let atsEncoded = (typeEnc.Substring(1, retPos - 1)).Split([|','|])
                   List.map fromTypeString (List.of_array atsEncoded)
        let rt = fromTypeString (typeEnc.Substring(retPos + 1))
        Some (rt, ats)
      else
        None
