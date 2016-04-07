//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

// Boogie AST instances to be used in unit tests
namespace Microsoft.Research.Vcc2.BoogieASTTest

  module BoogieAST = Microsoft.Research.Vcc2.BoogieAST

  type Expr =
    static member Ref = 
      [|
        BoogieAST.Ref "x";
        BoogieAST.Ref "y"
      |]
    static member BoolLiteral = 
      [|
        BoogieAST.BoolLiteral true;
        BoogieAST.BoolLiteral false
      |]
    static member IntLiteral = 
      [|
        BoogieAST.IntLiteral (Math.BigInt.FromInt32 1);
        BoogieAST.IntLiteral (Math.BigInt.FromInt32 0);
        BoogieAST.IntLiteral (Math.BigInt.FromInt32 (-1))
      |]
    static member Primitive = 
      [|
        BoogieAST.Primitive ("<", [BoogieAST.Ref "x"; BoogieAST.Ref "y"]);
        BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)])
      |]
    static member FunctionCall = 
      [|
        BoogieAST.FunctionCall ("f", []);
        BoogieAST.FunctionCall ("g", [BoogieAST.Ref "x"]);
        BoogieAST.FunctionCall ("h", [BoogieAST.Ref "x"; BoogieAST.Ref "y"])
      |]
    static member ArrayIndex = 
      [|
        BoogieAST.ArrayIndex (BoogieAST.Ref "a", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]);
        BoogieAST.ArrayIndex (BoogieAST.Ref "b", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)])
      |]
    static member Cast = 
      [|
        BoogieAST.Cast (BoogieAST.Ref "x", BoogieAST.Int);
        BoogieAST.Cast (BoogieAST.Ref "y", BoogieAST.Any)
      |]
    static member Old = 
      [|
        BoogieAST.Old (BoogieAST.Ref "x");
        BoogieAST.Old (BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]))
      |]
    static member Exists = 
      [|
        BoogieAST.Exists ([("x", BoogieAST.Bool)],
          [[BoogieAST.FunctionCall ("f", [BoogieAST.Ref "x"])]],
          BoogieAST.Primitive ("==", [BoogieAST.FunctionCall ("f", [BoogieAST.Ref "x"]); BoogieAST.BoolLiteral true]));
        BoogieAST.Exists ([("y", BoogieAST.Int)], 
          [[BoogieAST.FunctionCall ("f", [BoogieAST.Ref "y"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]);
            BoogieAST.FunctionCall ("g", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0); BoogieAST.Ref "y"])]],
          BoogieAST.Primitive ("!=", [BoogieAST.FunctionCall ("f", [BoogieAST.Ref "y"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]); 
                                      BoogieAST.FunctionCall ("g", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0); BoogieAST.Ref "y"])]));
        BoogieAST.Exists ([("x", BoogieAST.Bool)],
          [[]],
          BoogieAST.BoolLiteral true);
      |]
    static member Forall = 
      [|
        BoogieAST.Forall ([("y", BoogieAST.Bool)],
          [[BoogieAST.FunctionCall ("f", [BoogieAST.Ref "y"])]],
          BoogieAST.Primitive ("==", [BoogieAST.FunctionCall ("f", [BoogieAST.Ref "y"]); BoogieAST.BoolLiteral true]));
        BoogieAST.Forall ([("x", BoogieAST.Int)], 
          [[BoogieAST.FunctionCall ("f", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]);
            BoogieAST.FunctionCall ("g", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0); BoogieAST.Ref "x"])]],
          BoogieAST.Primitive ("!=", [BoogieAST.FunctionCall ("f", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]); 
                                      BoogieAST.FunctionCall ("g", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0); BoogieAST.Ref "x"])]))
        BoogieAST.Exists ([("x", BoogieAST.Bool)],
          [],
          BoogieAST.BoolLiteral false);
      |]


  type Stmt =
    static member Assert = 
      [|
        BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive (">=", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]));
        BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive ("==", [BoogieAST.Ref "y"; BoogieAST.BoolLiteral true]))
      |]
    static member Assume = 
      [|
        BoogieAST.Assume (BoogieAST.Primitive ("!=", [BoogieAST.Ref "x"; BoogieAST.BoolLiteral false]));
        BoogieAST.Assume (BoogieAST.Primitive ("<=", [BoogieAST.Ref "y"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]))
      |]
    static member Havoc = 
      [|
        BoogieAST.Havoc [];
        BoogieAST.Havoc ["x"];
        BoogieAST.Havoc ["x"; "y"]
      |]
    static member Assign = 
      [|
        BoogieAST.Assign (BoogieAST.Ref "x", BoogieAST.IntLiteral (Math.BigInt.FromInt32 0));
        BoogieAST.Assign (BoogieAST.ArrayIndex (BoogieAST.Ref "a", [BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]),
          BoogieAST.Ref "y");
        BoogieAST.Assign (BoogieAST.ArrayIndex (BoogieAST.Ref "b", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]), 
          BoogieAST.BoolLiteral true) 
      |]
    static member Call = 
      [|
        BoogieAST.Call (BoogieAST.noToken, [], "f", []);
        BoogieAST.Call (BoogieAST.noToken, [], "f", [BoogieAST.Ref "x"]);
        BoogieAST.Call (BoogieAST.noToken, [], "f", [BoogieAST.Ref "x"; BoogieAST.Ref "y"]);
        BoogieAST.Call (BoogieAST.noToken, ["out1"], "g", [BoogieAST.Ref "x"]);
        BoogieAST.Call (BoogieAST.noToken, ["out2"], "g", [BoogieAST.Ref "x"])        
      |]
    static member If = 
      [|
        BoogieAST.If (BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]),
          BoogieAST.Block [
            BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]));
            BoogieAST.Assign (BoogieAST.Ref "x", BoogieAST.IntLiteral (Math.BigInt.FromInt32 0))],
          BoogieAST.Block [
            BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive ("<=", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]));
            BoogieAST.Assign (BoogieAST.Ref "x", BoogieAST.IntLiteral (Math.BigInt.FromInt32 0))]);
        BoogieAST.If (BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]),
          BoogieAST.Block [
            BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]));
            BoogieAST.Assign (BoogieAST.Ref "x", BoogieAST.IntLiteral (Math.BigInt.FromInt32 0))],
          BoogieAST.Block [])
      |]
    static member While = 
      [|
        BoogieAST.While (
          BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]),
          [(BoogieAST.noToken, BoogieAST.Primitive ("==>", [BoogieAST.Primitive ("==", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]);
                                                            BoogieAST.Primitive ("!=", [BoogieAST.Ref "y"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)])]));
            (BoogieAST.noToken, BoogieAST.Primitive ("==", [BoogieAST.Ref "y"; BoogieAST.BoolLiteral true]))],
          BoogieAST.Block [BoogieAST.Assign (BoogieAST.Ref "x", 
                             BoogieAST.Primitive ("+", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]))]);
        BoogieAST.While (
          BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]),
          [],
          BoogieAST.Block [BoogieAST.Assign (BoogieAST.Ref "x", 
                             BoogieAST.Primitive ("+", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]))]);
        BoogieAST.While (
          BoogieAST.BoolLiteral true,
          [],
          BoogieAST.Block [])
      |]
    static member Label = 
      [|
        (BoogieAST.noToken, "label1");
        (BoogieAST.noToken, "label2")
      |]
    static member Goto = 
      [|
        BoogieAST.Goto (BoogieAST.noToken, "label1");
        BoogieAST.Goto (BoogieAST.noToken, "label2");
      |]
    static member Block = 
      [|
        BoogieAST.Block [
         BoogieAST.Assert (BoogieAST.noToken, BoogieAST.Primitive (">", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 0)]));
         BoogieAST.Assign (BoogieAST.Ref "x", BoogieAST.IntLiteral (Math.BigInt.FromInt32 0))];
        BoogieAST.Block [BoogieAST.Assign (BoogieAST.Ref "x", 
                           BoogieAST.Primitive ("+", [BoogieAST.Ref "x"; BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]))];
        BoogieAST.Block []                           
      |]
    static member Comment = 
      [|
        BoogieAST.Stmt.Comment "This is a single-line comment Stmt";
        BoogieAST.Stmt.Comment "This is \n supposed to be \n a multi-line comment Stmt"
      |]


  type Decl =
    static member Const = 
      [|
        BoogieAST.Const {
          Unique = true;
          Name = "n";
          Type = BoogieAST.Int
        };
        BoogieAST.Const {
          Unique = false;
          Name = "b";
          Type = BoogieAST.Bool
        }        
      |]
    static member Function = 
      [|
        BoogieAST.Function (BoogieAST.Bool, [], "f", [("x", BoogieAST.Int)]);
        BoogieAST.Function (BoogieAST.Int, [], "g", [("x", BoogieAST.Int); ("y", BoogieAST.Bool)]);
        BoogieAST.Function (BoogieAST.Any, [], "h", []);
      |]
    static member Axiom = 
      [|
        BoogieAST.Axiom (BoogieAST.Forall ([("x", BoogieAST.Int)], [], BoogieAST.Primitive ("==", [BoogieAST.Ref "x"; BoogieAST.Ref "x"])));
        BoogieAST.Axiom (BoogieAST.Exists ([("y", BoogieAST.Int)], [[]], BoogieAST.Primitive ("!=", [BoogieAST.Ref "y"; BoogieAST.Ref "y"])));
      |]
    static member Proc = 
      let noWhere = List.map (fun v -> (v, None))
      [|
        BoogieAST.Proc {
          Name = "proc1"; 
          InParms = []; 
          OutParms = []; 
          Contracts = []; 
          Locals = noWhere [("x", BoogieAST.Bool)]; 
          Body = Some(BoogieAST.Block []);
          Attributes = []
        };
        BoogieAST.Proc {
          Name = "proc2";
          InParms = [("in1", BoogieAST.Int)];
          OutParms = [("out1", BoogieAST.Any)];
          Contracts = [];
          Locals = noWhere [("x", BoogieAST.Bool);("y", BoogieAST.Int)];
          Body = Some(BoogieAST.Block [ BoogieAST.Stmt.Label(BoogieAST.noToken, "label1") ]);
          Attributes = []
        }
        BoogieAST.Proc {
          Name = "proc3"; 
          InParms = []; 
          OutParms = []; 
          Contracts = [BoogieAST.Requires (BoogieAST.noToken, BoogieAST.Primitive(">=", [BoogieAST.Ref("x"); BoogieAST.IntLiteral (Math.BigInt.FromInt32 1)]))]; 
          Locals = noWhere [("x", BoogieAST.Int)]; 
          Body = Some(BoogieAST.Block []);
          Attributes = []
        };
      |]
    static member TypeDef = 
      [|
        BoogieAST.TypeDef "Type1";
        BoogieAST.TypeDef "Type2";
      |]
