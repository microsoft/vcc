
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light


namespace Microsoft.Research.Vcc
 open Microsoft.Research.Vcc
 open Microsoft.Research.Vcc.Util
 open Microsoft.Research.Vcc.TransUtil
 open Microsoft.Research.Vcc.CAST
 
 module Transformers =
 
  let processPipeOptions (helper:TransHelper.TransEnv) =
    let pipeErr msg =
      failwith ("/pipe: error: " + msg)
    let showTypes = ref false
    for origw in helper.Options.PipeOperations do
      let w = origw.Replace('.', ' ').Replace('+', ' ')
      let w = w.Split ([| ' ' |])
      if w.Length > 0 then
        match w.[0] with
          | "show-types" ->
            if w.Length <> 1 then pipeErr "show-types expects no parameters"
            showTypes := true
          | "dump" ->
            if w.Length <> 3 then pipeErr "dump expects two parameters"
            let off =
              match w.[1] with
                | "before" -> 0
                | "after" -> 1
                | "around" -> 2
                | _ -> pipeErr "dump expects 'before', 'after', or 'around'"
            let add off = helper.AddTransformerAt ("dump", TransHelper.Decl (TransUtil.dumpDecls origw !showTypes), w.[2], off)
            if off = 2 then add 0; add 1
            else add off
          | "dump-all" ->
            if w.Length <> 1 then pipeErr "dump-all expects no parameters"
            let mk (t:TransHelper.TransDesc) =
              let name = "after " + t.Name
              let dump = TransHelper.TransDesc.Mk ("dump-all " + name, TransHelper.Decl (TransUtil.dumpDecls name !showTypes))
              [t; dump]
            helper.InterleaveTransformers mk
          | "active" ->
            if w.Length <> 1 then pipeErr "active expects no parameters"
            helper.DumpTransformers()
          | "time" ->
            if w.Length <> 1 then pipeErr "time expects no parameters"
            helper.ShouldDumpTime()
          | "disable" ->
            if w.Length <> 2 then pipeErr "disable expects 1 parameter"
            helper.DisableTransformers w.[1]
          | "move" ->
            if w.Length <> 4 then pipeErr "move expects three parameters"
            let off =
              match w.[2] with
                | "before" -> 0
                | "after" -> 1
                | _ -> pipeErr "move expects 'before' or 'after'"
            let t = helper.RemoveTransformer w.[1]
            helper.AddTransformerAt (t.Name, t.Func, w.[3], off)       
          | "isabelle" ->
            if w.Length < 2 || w.Length > 3 then pipeErr "isabelle expects one or two parameters"
            let prefix = if w.Length = 3 then w.[2] else ""
            helper.AddTransformerAfter ("isabelle", TransHelper.Decl (Isabelle.dump helper (w.[1]) prefix), "begin")       
          | _ ->
            pipeErr ("unknown command " + w.[0])
            
            
  
  let pruneDecls (helper:TransHelper.TransEnv) (decls : list<Top>) : list<Top> =
    let objToTop = objDict()
    let used = new HashSet<Top>()
    
    let populateObjToTop = function
      | Top.Global (v, _) as d ->
        objToTop.Add (v, d)
      | Top.TypeDecl td as d ->
        objToTop.Add (td, d)
      | Top.FunctionDecl h as d ->
        objToTop.Add(h, d)
      | _ -> ()
          
    List.iter populateObjToTop decls

    let rec cb = { new PruneCallback with
                     member self.UseFunction f = useIt f
                     member self.UseGlobal v = doVar v; useIt v
                     member self.UseTypeDecl td = useIt td }      
    and checkType t = walkType cb t
    and doVar (v:Variable) = checkType v.Type
    and useIt (o:obj) =
      match objToTop.TryGetValue o with
      | (true, top) ->
        match top with
          | Top.FunctionDecl { Name = ( "malloc" | "free" ) } -> ()
          | t -> if used.Add t then walkTop cb t
      | (false, _) ->
        helper.Panic (System.String.Format ("pruning: cannot find {0} : {1}", o, o.GetType()))

    let fnByName = new Dict<_,_>()
    for d in decls do
      match d with
        | Top.FunctionDecl h ->
          fnByName.[h.Name] <- h
        | _ -> ()
            
    for d in decls do
      match d with
        | Top.Axiom _ -> used.Add d |> ignore
        | Top.GeneratedAxiom _ -> used.Add d |> ignore
        | Top.FunctionDecl h ->
          let doAttr = function
            | VccAttr ("is_reads_check", name) as attr ->
              match fnByName.TryGetValue name with
                | true, f ->
                  useIt (f :> obj)
                  ReadsCheck f
                | _ -> 
                  helper.Error (h.Token, 9643, "function '" + name + "' is nowhere to be found (for reads check)", None)
                  attr
            | attr -> attr
          h.CustomAttr <- List.map doAttr h.CustomAttr
                  
          match h.Name with
            | "\\free" | "\\stack_free" | "\\heap_alloc" | "\\stack_alloc"
            | "\\set_owns" | "\\set_closed_owner" | "\\giveup_closed_owner"
            | "\\wrap" | "\\unwrap" 
            | "_vcc_free" | "_vcc_stack_free"
            | "_vcc_alloc" | "_vcc_stack_alloc" -> useIt (h :> obj)
            | "__FallThrough" -> ()
            | _ ->
             match h.Body, h.Reads with
               | None, [] -> ()
               | _ -> useIt (h :> obj)
        | _ -> ()
          
    let rec fixpoint decls =
      let prevCount = used.Count
      for d in decls do
        match d with
          | Top.TypeDecl td when td.Fields.IsEmpty && td.DataTypeOptions.IsEmpty -> used.Add d |> ignore // include empty structs, which are really groups
          | _ -> ()
      deepVisitExpressions (walkExpr cb) decls
      if prevCount = used.Count then decls
      else fixpoint decls
    let decls = fixpoint decls
    
    List.filter used.Contains decls


  let init (helper:TransHelper.TransEnv) =
    helper.AddTransformer ("begin", TransHelper.DoNothing)
    helper.AddTransformer ("prune", TransHelper.Decl (pruneDecls helper))

    NewSyntax.init helper
    Normalizer.init helper
    DataTypes.init helper
    TransType.init helper
    ExtraWarnings.init helper
    Simplifier.init helper
    Inference.init helper
    ToCoreC.init helper
    AddChecks.init helper
    Termination.init helper
    TransFinalize.init helper
    
    helper.AddTransformer ("end", TransHelper.DoNothing)
    
    helper.AddTransformerAfter ("add-admissibility-checks", 
      TransHelper.Decl (TransSideChecks.handleAdmissibilityChecks helper), "post-assignments")
    helper.AddTransformerAfter ("add-reads-checks", 
      TransHelper.Decl (TransSideChecks.addReadsChecks helper), "final-before-cleanup")    
    helper.AddTransformerAfter ("warn-sequence",
     TransHelper.Decl (ExtraWarnings.warnForSequenceProblems helper), "core-assignments")
      
