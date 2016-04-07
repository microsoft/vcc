//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc

  // TODO: expansion axiom has been changed in boogie, this file needs to be updated
  
  open System.Diagnostics
  open Microsoft
  open Microsoft.Research.Vcc.Util
  open Microsoft.Research.Vcc.BoogieAST

  module ToBoogieAST =
    let notok = Boogie.Token.NoToken
    
    type Command =
      {
        Token : Token;
        IsAssert : bool;
        Condition : Expr;
      }
      
      member this.ToStmt () =
        if this.IsAssert then
          Assert ([], this.Token, this.Condition) 
        else 
          Assume ([], this.Condition)
      
    type 
      [<NoComparison>] [<ReferenceEquality>] 
      Block =
      {
        mutable Label : string;
        mutable Cmds : list<Command>;
        mutable Exits : list<Block>;
      }
      
      member this.TransferStmt () =
        match this.Exits with
          | [] -> Return Token.NoToken
          | lst -> Goto (Token.NoToken, lst |> List.map (fun b -> b.Label))
      
      member this.ToStmts () =
        Stmt.Label (Token.NoToken, this.Label) :: (this.Cmds |> List.map (fun c -> c.ToStmt())) @ [this.TransferStmt()]
    
    type BlockProc =
      {
        Name : string;
        mutable Locals : list<Var>;
        mutable Blocks : list<Block>;
      }
      
      member this.ToDecl () =
        let body = Block (this.Blocks |> List.map (fun b -> b.ToStmts()) |> List.concat)
        let procData =
          { Name = "$pass_" + this.Name 
            Token = Token.NoToken
            InParms = []
            OutParms = []
            Contracts = []
            Locals = this.Locals |> List.map (fun v -> (v, None))
            Body = Some body
            Attributes = [] }
        Proc procData
    
    let blocksFromRoot root =
      let visited = new HashSet<_>()
      let res = ref []
      let rec visit (b:Block) =
        if visited.Add b then
          res := b :: !res
          List.iter visit b.Exits
      visit root
      List.rev !res
    
    let toTree root =
      let visited = new Dict<_,_>()
      let rec visit (b:Block) =
        let label =
          match visited.TryGetValue b with
            | true, n ->
              visited.[b] <- n + 1
              System.String.Format ("{0}#branch_{1}", b.Label, n)
            | _ -> 
              visited.[b] <- 1
              b.Label
        { b with Label = label; Exits = List.map visit b.Exits }
      visit root      
      
    let rec unType (t:Boogie.Type) = 
      if t.IsBool then Type.Bool
      elif t.IsInt then Type.Int
      elif t.IsBv then Type.Bv(t.BvBits)
      else
        match t with
          | :? Boogie.CtorType as u ->
            Type.Ref u.Decl.Name
          | :? Boogie.UnresolvedTypeIdentifier as u ->
            Type.Ref u.Name
          | :? Boogie.MapType as a ->
            Type.Map ([for a in a.Arguments -> unType a], unType a.Result)
          | :? Boogie.TypeSynonymAnnotation as u ->
            Type.Ref u.Decl.Name
          | _ ->
            failwith ("cannot handle boogie type " + t.ToString() + " : " + t.GetType().ToString())
     
    let unVar (v:obj) =
      let v = (v :?> Boogie.Variable)
      v.Name, unType v.TypedIdent.Type  
    
    let unVars (vs:Boogie.VariableSeq) =
      [for v in vs -> unVar v]
    
    let rec unparse (expr:Microsoft.Boogie.Expr) =
      match expr with
        | :? Microsoft.Boogie.IdentifierExpr as id -> Expr.Ref id.Name
        | :? Microsoft.Boogie.LiteralExpr as lit ->
          if lit.isBigNum then
            Expr.IntLiteral (bigint.Parse (lit.asBigNum.ToString()))
          elif lit.IsFalse then
            Expr.BoolLiteral false
          elif lit.IsTrue then
            Expr.BoolLiteral true
          else match lit.Val with
                 | :? Microsoft.Boogie.BvConst as bvConst ->
                   Expr.BvLiteral(bigint.Parse(bvConst.Value.ToString()), bvConst.Bits)
                 | _ -> failwith ("cannot unparse lit " + lit.ToString())
        | :? Boogie.NAryExpr as nary ->
          let args = [for e in nary.Args -> unparse e]
          match nary.Fun with
            | :? Boogie.TypeCoercion ->
              if args.Length <> 1 then failwith "wrong coercion"
              args.Head
            | :? Boogie.FunctionCall as fcall -> FunctionCall (fcall.FunctionName, args)
            | :? Boogie.BinaryOperator as binop -> Primitive (binop.FunctionName, args)
            | :? Boogie.UnaryOperator as unop -> Primitive (unop.FunctionName, args)
            | :? Boogie.MapSelect -> ArrayIndex (args.Head, args.Tail)
            | :? Boogie.MapStore -> 
              let ri = List.rev args.Tail
              ArrayUpdate (args.Head, List.rev ri.Tail, ri.Head)
            | :? Boogie.IfThenElse ->
              Ite (args.[0], args.[1], args.[2])
            | _ -> failwith ("wrong nary " + nary.ToString() + " / " + nary.Fun.GetType().ToString())
        | :? Boogie.BvConcatExpr as bvConcat ->
          match [for e in bvConcat.Arguments -> unparse(e :?> Microsoft.Boogie.Expr)] with
            | [arg1; arg2] -> BvConcat(arg1, arg2)
            | _ -> failwith ("unexpected argument list of BvConcatExpr")
        | :? Boogie.QuantifierExpr as quant ->
          let dummies = unVars quant.Dummies
          let rec doTrig (t:Boogie.Trigger) =
            if t = null then []
            elif not t.Pos then
              failwith "negative triggers unsupported at this time"
            else [for e in t.Tr -> unparse e] :: doTrig t.Next
          let triggers = doTrig quant.Triggers
          let body = unparse quant.Body
          let attrs = unparseAttr quant.Attributes
          let tok = BoogieToken.Strip quant.tok
          if (quant :? Boogie.ExistsExpr) then
            Exists (tok, dummies, triggers, attrs, body)
          else
            Forall (tok, dummies, triggers, attrs, body)
        | :? Boogie.LambdaExpr as lambda ->
          Lambda(BoogieToken.Strip lambda.tok, unVars lambda.Dummies, unparseAttr lambda.Attributes, unparse lambda.Body)
        | s -> 
          failwith ("cannot unparse " + s.ToString())
          Expr.Ref "###"      
    
    and unparseAttr (q:Boogie.QKeyValue) =
      if q = null then []
      else
        let cur =
          match q.Params.[0] with
            | :? string as s -> Attribute.StringAttr (q.Key, s)
            | :? Boogie.Expr as e -> Attribute.ExprAttr (q.Key, unparse e)
            | x -> failwith ("wrong attribute value " + x.ToString())
        cur :: unparseAttr q.Next
            
    let doCommand (cmd:obj) =
      match cmd with
        | :? Boogie.PredicateCmd as asrt ->
          let tok =
            match asrt with
              | :? Boogie.AssertEnsuresCmd as a -> new TokenWithAddCmdInfo (BoogieToken.Strip asrt.tok, AddEnsures a.Ensures) :> Token
              | :? Boogie.AssertRequiresCmd as a -> new TokenWithAddCmdInfo (BoogieToken.Strip asrt.tok, AddRequires (a.Call, a.Requires)) :> Token
              | _ -> BoogieToken.Strip asrt.tok
          { Token = tok
            IsAssert = (asrt :? Boogie.AssertCmd)
            Condition = unparse asrt.Expr }
        | _ -> failwith ("unexpected boogie command in passified program " + cmd.ToString())
              
    let doBlock (b:Boogie.Block) =
      { Label = b.Label 
        Exits = [] 
        Cmds = [ for c in b.Cmds -> doCommand c ] }
     
    let resolveExits (names:Dict<_,_>) (b:Boogie.Block) =
      match b.TransferCmd with
        | :? Boogie.ReturnCmd -> []
        | :? Boogie.GotoCmd as goto ->
          [ for t in goto.labelTargets -> names.[t.Label] ]
        | _ -> failwith ("unexpected transfer cmd " + if b.TransferCmd = null then "(null)" else b.TransferCmd.ToString())
      
    let rename proc =
      let ren = new Dict<_,_>()
      let repl (n:string) = 
        let n' = n.Replace ("@", "#")
        match ren.TryGetValue n' with
          | true, o when o = n -> ()
          | false, _ -> ren.[n'] <- n
          | _ -> failwith ("failed renaming of " + n)
        n'
      let doRepl = function
        | Ref n -> Some (Ref (repl n))
        | _ -> None
      for b in proc.Blocks do
        b.Cmds <- b.Cmds |> List.map (fun c -> { c with Condition = c.Condition.Map doRepl })
        b.Label <- b.Label.Replace ("@", "#")
      proc.Locals <- proc.Locals |> List.map (fun (n, t) -> (repl n, t))
    
    let createBody block =
      Block (Stmt.Label (Token.NoToken, block.Label) :: (block.Cmds |> List.map (fun c -> c.ToStmt())) @ [block.TransferStmt()])
    
    let dumpBPL filename (prog:Boogie.Program) add =
      let writer = new Boogie.TokenTextWriter(filename, new System.IO.StreamWriter (filename), false)
      writer.SetToken prog
      for d in prog.TopLevelDeclarations do
        match d with
          | :? Boogie.Procedure 
          | :? Boogie.Implementation -> ()
          | _ -> 
            d.Emit (writer, 0)
            writer.WriteLine()
      for (d:Boogie.Declaration) in add do
        d.Emit (writer, 0)
        writer.WriteLine()
      writer.Close()
    
    type [<AbstractClass>] Passyficator (prog:Boogie.Program, helper:Helper.Env, options:list<string>) =
      inherit VC.VCGen(prog, null, false)
      
      let expansionAxioms = ref []
      
      member this.GetAxioms () =
        [ for d in prog.TopLevelDeclarations do
            match d with
              | :? Boogie.Axiom as ax -> yield (unparse ax.Expr)
              | _ -> yield! []
        ]
      
      member this.RemoveExpansionAxioms () =
        let out = new GList<_>()
        
        for d in prog.TopLevelDeclarations do
            match d with
              | :? Boogie.Axiom as ax ->
                let exp = ref false
                ax.CheckBooleanAttribute ("expand", exp) |> ignore
                if !exp then expansionAxioms := d :: !expansionAxioms
                else out.Add d
              | _ -> out.Add d
        
        prog.TopLevelDeclarations <- out
                   
      member this.Passify (impl:Boogie.Implementation) =
        this.ConvertCFG2DAG (impl, prog)
        this.PassifyImpl (impl, prog) |> ignore
        let blocks = [ for b in impl.Blocks -> doBlock b ]
        let names = new Dict<_,_>()
        for b in blocks do names.Add (b.Label, b)
        for b in impl.Blocks do
          names.[b.Label].Exits <- resolveExits names b
        let vars = unVars impl.InParams @ unVars impl.OutParams @ unVars impl.LocVars
        let res = ref false        
        
        let proc =
          { Name = impl.Name
            Blocks = blocks
            Locals = vars }
        rename proc
        proc
     
      member this.Dump filename decls =
        dumpBPL filename prog (!expansionAxioms @ decls)
      
      abstract Optimize : BlockProc -> unit
      
      member this.GetExpansionAxioms () = 
        [ for d in !expansionAxioms do
            match d with
              | :? Boogie.Axiom as ax -> yield (unparse ax.Expr)
              | _ -> yield! []
        ]
      
      member this.RoundTrip impl =
        let proc = this.Passify impl
        let name = impl.Name
        if _list_mem "pre-dump" options then
          this.Dump "vcopt-pre.bpl" (proc.ToDecl () |> trDecl)
        let root = proc.Blocks.Head
        let tree = toTree root
        proc.Blocks <- blocksFromRoot tree
        this.Optimize (proc)
        let decls = proc.ToDecl () |> trDecl
        prog.TopLevelDeclarations.AddRange (decls)
        let errs = prog.Resolve()
        let errs =
          if errs = 0 then
            prog.Typecheck()
          else errs
        match decls with
          | [_; impl] when errs = 0 ->
            if _list_mem "post-dump" options then
              this.Dump "vcopt-post.bpl" decls
            (impl :?> Boogie.Implementation)
          | _ ->
            System.Console.WriteLine("attempting to dump BPL to vcopt-bug.bpl")
            this.Dump "vcopt-bug.bpl" decls
            failwith "something went wrong"
          


    type Function =
      {
        Name : string
        Parameters : list<Var>
        Body : Expr
      }

      member this.Expand actuals =
        let subst = gdict()
        List.iter2 (fun f a -> subst.Add (fst f, a)) this.Parameters actuals
        this.Body.Map
          (function
            | Expr.Ref v when subst.ContainsKey v -> Some subst.[v]
            | _ -> None)
              
    let getFunctionExpansions (prog:Boogie.Program) =
      let getBody : Boogie.Declaration -> _ = function
        | :? Boogie.Function as fn ->
          if fn.Body <> null then
            [{ Name = fn.Name
               Parameters = unVars fn.InParams
               Body = unparse fn.Body }]
          else
            []
        | _ -> []
      Seq.collect getBody prog.TopLevelDeclarations |> Seq.toList
