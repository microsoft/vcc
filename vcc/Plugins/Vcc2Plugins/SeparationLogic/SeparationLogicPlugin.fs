//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc2
  module PureProver = Microsoft.Research.Vcc2.PureProver
  module Logic = Microsoft.Research.Vcc2.Logic
  module SepProver = Microsoft.Research.Vcc2.SepProver
  module CAST = Microsoft.Research.Vcc2.CAST
  module CoreC = Microsoft.Research.Vcc2.CoreCAST
  module SymbolicExecution = Microsoft.Research.Vcc2.SymbolicExecution
  
  type SeparationLogicFunctionVerifier(env:Helper.Env, initialDecls:list<CAST.Top>, messageHandler:DelegateEvent<MessageHandler>) =
    inherit FunctionVerifier(env, initialDecls)

    let mutable funcDecls = new Util.Dict<string, CoreC.Function>()    
    let declsCoreC = CAST2CoreCAST.apply env initialDecls
    let updateLogic logicTransformer  =
      SymbolicExecution.currentLogic <- logicTransformer SymbolicExecution.currentLogic

    do
//      updateLogic(SepProver.add_external_prover currentLogic PureProver.implies) // add Z3 as an external prover
//      updateLogic(SepProver.add_external_congruence currentLogic PureProver.congruence_closure) // add external congruence closure
//      updateLogic(Logic.add_array_to_rules (CAST.Integer Microsoft.Cci.PrimitiveTypeCode.Int32) 1 currentLogic) // add array rules
//      updateLogic(Logic.add_array_to_rules (CAST.Integer Microsoft.Cci.PrimitiveTypeCode.Int32) 2 currentLogic) // add array rules
//      updateLogic(Logic.add_array_to_rules (CAST.Integer Microsoft.Cci.PrimitiveTypeCode.Int32) 3 currentLogic) // add array rules
      for d in declsCoreC do
        match d with
        | CoreC.TypeDecl t ->
          updateLogic ((fun l -> Logic.add_struct_to_rules t l))
        | CoreC.FunctionDecl f -> 
          funcDecls.Add (f.Name, f)
     
    override this.FunctionsToVerify () =
      if env.ShouldContinue then
        [ for d in declsCoreC do
            match d with
              | CoreC.FunctionDecl f when f.Body.IsSome -> yield f.Name
              | _ -> yield! [] ]
      else []
      
    override this.Verify funcName = 
      let func = 
        match funcDecls.TryGetValue funcName with
          | (true, f) -> f
          | _ -> failwith (funcName + " is not present in the input file.")
      match SymbolicExecution.verifyFunction func 
        (fun (s:string) -> messageHandler.Trigger([| (s :> obj) |])) with
          | true -> VerificationResult.Succeeded
          | false -> VerificationResult.Failed
    
    override this.DumpInternalsToFile (fn, generate) = ()

  
  [<System.ComponentModel.Composition.Export("Microsoft.Research.Vcc2.Plugin")>]
  type SeparationLogicPlugin() =
    inherit Plugin()
    
    let dumpSepProver = "sp"
    let dumpPureProver = "pp"
    
    member private this.init (env:Helper.Env) =
      Transformers.init(env)
      Transformers.processPipeOptions(env)
    
    member this.IsModular = true
    
    override this.Help () =
      "Options:\n" +
      dumpSepProver + " ... print output from separation logic prover\n" +
      dumpPureProver + " ... print output from pure prover\n"
    
    override this.Name () =
      "SeparationLogic"
    
    override this.UseCommandLineOptions opts =
      // default options
      PureProver.debug <- false
      SepProver.debug false
      // custom options
      for opt in opts do
        if opt.Equals dumpSepProver then
          SepProver.debug true
        if opt.Equals dumpPureProver then
          PureProver.debug <- true
   
    override this.WritePreProcessed (sw, s) =
//      printf "%s\n" s
      sw.WriteLine s
    
    override this.GetFunctionVerifier (fileName, env, decls) =
      this.init env
      let decls = env.ApplyTransformers decls
      SeparationLogicFunctionVerifier(env, decls, this.MessageHandler) :> FunctionVerifier
   
    override this.Verify (fileName, env, decls) =
      this.init env
      let decls = env.ApplyTransformers decls
      if env.ShouldContinue then
        let verifier = this.GetFunctionVerifier (fileName, env, decls)
        for f in verifier.FunctionsToVerify() do
          let result = verifier.Verify f
          ()
