//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open Microsoft.FSharp.Math
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.TranslatorUtils
  open Microsoft.Research.Vcc.Util
  open System
  
  module C = Microsoft.Research.Vcc.CAST
  module B = Microsoft.Research.Vcc.BoogieAST
  
  type BvOp =
    | BinSame of string
    | BinDifferent of string * string
    | BinPredDifferent of string * string
    | UnarySame of string
          
    
  type BvTranslator(ctx:TranslationState) =
    let generatedBvOps = new HashSet<_>()
    let helper = ctx.Helper
    
    let bvSignExtensionOp fromBits toBits =
      let boogieName = "$bv_sign_ext_" + fromBits.ToString() + "_" + toBits.ToString()
      if generatedBvOps.Add boogieName then 
        let retTp = B.Type.Bv toBits
        let fromTp = B.Type.Bv fromBits
        let fn = B.Decl.Function (retTp, [B.Attribute.StringAttr("bvbuiltin", "sign_extend " + (toBits - fromBits).ToString())], boogieName, [("p", fromTp)], None)
        ctx.AddDecls [fn]
      boogieName
    
    let bvZeroExtend fromBits toBits e = B.BvConcat(B.Expr.BvLiteral (new bigint(0), toBits - fromBits), e)
    let bvSignExtend fromBits toBits e = bCall (bvSignExtensionOp fromBits toBits) [e]
    
    let bvExtend (fromType : C.Type) (toType : C.Type) e =
      let fromBits = 8 * fromType.SizeOf
      let toBits = 8 * toType.SizeOf
      if fromBits >= toBits then e 
      elif fromType.IsSignedInteger then bvSignExtend fromBits toBits e
      else bvZeroExtend fromBits toBits e 
    
          
    member this.BvType (expr:C.Expr) = function
        | C.Integer k ->
          let (sz, _) = k.SizeSign
          B.Type.Bv sz
        | C.Bool as t -> ctx.TrType t
        | tp ->
          helper.Error (expr.Token, 9689, "type '" + tp.ToString() + "' is not supported for bitvector translation (in " + expr.Token.Value + ")")            
          B.Type.Int
          
    member this.BvOpFor expr tp name =
      let bvOps =
        [ "+", BinSame "add";
          "-", BinSame "sub"; 
          "*", BinSame "mul"; 
          "/", BinDifferent ("sdiv", "udiv"); 
          "%", BinDifferent ("srem", "urem"); 
          "&", BinSame "and"; 
          "|", BinSame "or"; 
          "^", BinSame "xor"; 
          "<<", BinSame "shl"; 
          ">>", BinDifferent ("ashr", "lshr"); 
          "<", BinPredDifferent ("slt", "ult");
          ">", BinPredDifferent ("sgt", "ugt");
          "<=", BinPredDifferent ("sle", "ule");
          ">=", BinPredDifferent ("sge", "uge");
          "u~", UnarySame "not";
          ]
      let bvt = this.BvType expr tp
      let (signedName, unsignedName, nargs, boolRes) =
        match _try_assoc name bvOps with
          | Some (UnarySame name) -> (name, name, 1, false)
          | Some (BinSame name)   -> (name, name, 2, false)
          | Some (BinDifferent (n1, n2)) -> (n1, n2, 2, false)
          | Some (BinPredDifferent (n1, n2)) -> (n1, n2, 2, true)
          | None -> 
            helper.Oops (expr.Token, "unknown operator '" + name + "' _(assert {:bv} ..." + expr.Token.Value + "...)")
            die()
      let (sz, sign) = 
        match tp with
          | C.Integer k -> k.SizeSign
          | _ -> die()
      let bvname = "bv" + (if sign then signedName else unsignedName)
      let boogieName = "$bv_" + bvname + sz.ToString()
      if generatedBvOps.Add boogieName then
        let bvt = B.Type.Bv sz
        let parms = [for i = 1 to nargs do yield ("p" + i.ToString(), bvt)]
        let retTp = if boolRes then B.Type.Bool else bvt
        let fn = B.Decl.Function (retTp, [B.Attribute.StringAttr ("bvbuiltin", bvname)], boogieName, parms, None)
        ctx.AddDecls [fn]
      boogieName

    member this.TrBvExpr env expr =
      let bvOpFor = this.BvOpFor
      let self = this.TrBvExpr env
      let selfs = List.map self
      let selfExtend toType (expr : C.Expr) = bvExtend expr.Type  toType (self expr)
      let selfsExtend toType = List.map (selfExtend toType)
      match expr with
        | C.Expr.Prim (_, C.Op (("!="|"==") as opName, _), [e1; e2]) ->
          let args = 
            if e1.Type.SizeOf = e2.Type.SizeOf then [self e1; self e2]
            elif e1.Type.SizeOf < e2.Type.SizeOf then [selfExtend e2.Type e1; self e2]
            else [self e1; selfExtend e1.Type e2]
          B.Expr.Primitive (opName, args)

        | C.Expr.Prim (_, C.Op (("&&"|"||"|"==>"|"<==>"|"!") as opName, _), args) ->
          B.Expr.Primitive (opName, selfs args)
          
        | C.Expr.Prim (_, C.Op (("+"|"-"|"*"|"/"|"%"), C.Checked), _) ->
          helper.Error (expr.Token, 9659, "operators in _(assert {:bv} ...) need to be unchecked (expression: " + expr.Token.Value + ")")
          er "$err"
          
        | C.Expr.Prim (c, (C.Op((">>"|"<<") as op, _)), [arg1; arg2]) when c.Type.SizeOf = 8 ->
         let bArg1 = self arg1
         let bArg2 = bvZeroExtend (arg2.Type.SizeOf * 8) 64 (self arg2)
         bCall (bvOpFor expr arg1.Type op) [bArg1; bArg2]
        
        | C.Expr.Prim (c, C.Op ("-", _), [arg]) ->
          self (C.Expr.Prim(c, C.Op("-", C.CheckedStatus.Processed), [C.Expr.IntLiteral(c, new bigint(0)); arg]))
          
        | C.Expr.Prim (_, C.Op (("<"|">"|"<="|">=") as opName, _), [e1; e2]) ->
          let args, opType = 
            if e1.Type.SizeOf = e2.Type.SizeOf then [self e1; self e2], e1.Type
            elif e1.Type.SizeOf < e2.Type.SizeOf then [selfExtend e2.Type e1; self e2], e2.Type
            else [self e1; selfExtend e1.Type e2], e1.Type
          bCall (bvOpFor expr opType opName) args
          
        | C.Expr.Prim (_, C.Op (op, _), args) ->
          let op =
            if args.Length = 1 then "u" + op else op
          bCall (bvOpFor expr expr.Type op) (selfsExtend expr.Type args)
          
        | C.Expr.Quant (c, ({ Kind = C.Forall } as q)) ->
          for v in q.Variables do
            ctx.QuantVarTokens.[v] <- c.Token
          let body = self q.Body
          let body =
            match q.Condition, q.Kind with
              | Some e, C.Forall -> bImpl (self e) body
              | None, _ -> body                
              | _ -> die()
          let trVar v =
            (ctx.VarName v, this.BvType expr v.Type)
          let vars = List.map trVar q.Variables
          B.Forall (c.Token, vars, [], ctx.Weight "user-bv", body)
        
        | C.Expr.Ref (_, ({ Kind = C.QuantBound } as v)) ->
          ctx.VarRef v
        
        | C.Expr.IntLiteral (c, v) when v >= bigint.Zero ->          
          B.Expr.BvLiteral (v, c.Type.SizeOf * 8)
          
        | C.Expr.IntLiteral (c, v) when v < bigint.Zero ->
          self (C.Expr.Prim(c, C.Op("-", C.CheckedStatus.Processed), [C.Expr.IntLiteral(c, -v)]))
        
        | C.Expr.Macro (_, "ite", [c; e1; e2]) -> B.Expr.Ite(self c, self e1, self e2)

        | C.Expr.Macro (_, "in_range_u1", [e])
        | C.Expr.Macro (_, "in_range_i1", [e]) when e.Type.SizeOf <= 1 ->
          bTrue

        | C.Expr.Macro (_, "in_range_u2", [e])
        | C.Expr.Macro (_, "in_range_i2", [e]) when e.Type.SizeOf <= 2 ->
          bTrue

        | C.Expr.Macro (_, "in_range_u4", [e])
        | C.Expr.Macro (_, "in_range_i4", [e]) when e.Type.SizeOf <= 4 ->
          bTrue
          
        | C.Expr.Macro (_, "in_range_u8", [e])
        | C.Expr.Macro (_, "in_range_i8", [e]) when e.Type.SizeOf <= 8 ->
          bTrue
        
        | C.Expr.Macro (_, "unchecked_u2", [e])
        | C.Expr.Macro (_, "unchecked_i2", [e]) when e.Type.SizeOf <= 2 -> self e

        | C.Expr.Macro (_, "unchecked_u4", [e])
        | C.Expr.Macro (_, "unchecked_i4", [e]) when e.Type.SizeOf <= 4 -> self e
        
        | C.Expr.Macro (_, "unchecked_u8", [e])
        | C.Expr.Macro (_, "unchecked_i8", [e]) when e.Type.SizeOf <= 8 -> self e
        
        | C.Expr.Macro (_, "in_range_phys_ptr", [e]) -> self e
        
        | C.Expr.BoolLiteral (_, v) -> B.BoolLiteral v
        
        | C.Expr.Macro(_, (("bv_extract_unsigned"|"bv_extract_signed") as name), [e; C.IntLiteral(_,bs); C.IntLiteral(_, fromBit); C.IntLiteral(_, toBit)]) ->
          let bs = int32 bs
          let fromBit = int32 fromBit
          let toBit = int32 toBit
          let extend = if name = "bv_extract_unsigned" then bvZeroExtend else bvSignExtend
          extend (toBit - fromBit) bs (B.BvExtract(self e, toBit, fromBit))
        
        | C.Expr.Cast (c, ch, e) ->
          match e.Type, c.Type with
            | src, dst when src = dst -> self e
            | C.Integer k, C.Bool ->
              B.Expr.Primitive ("!=", [self e; B.Expr.BvLiteral (bigint.Zero, fst k.SizeSign)])
            | C.Integer _ as src, (C.Integer _ as dst) when ch <> C.CheckedStatus.Checked ->
              if src.SizeOf = dst.SizeOf then self e
              elif src.SizeOf < dst.SizeOf then selfExtend dst e
              else B.BvExtract(self e, dst.SizeOf * 8, 0)
            | C.Ptr _, C.MathInteger _ -> self e
            | src, dst -> 
              helper.Error (expr.Token, 9690, "cast from " + src.ToString() + " to " + dst.ToString() + " is not supported in _(assert {:bv} ...)")
              er "$err"
        
        | _ ->
          helper.Error (expr.Token, 9660, "unsupported expression in _(assert {:bv} ...): " + expr.Token.Value + " (" + expr.ToString() + ")")
          er "$err"
    
