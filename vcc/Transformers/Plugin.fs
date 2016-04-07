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
 
 type VerificationResult =
   | Succeeded
   | Failed
   | Inconclusive
   | Crashed
   | UserError
   | Skipped

 type MessageHandler = delegate of string -> unit
 
 type [<AbstractClass>] FunctionVerifier(env:TransHelper.TransEnv, initialDecls:list<Top>) =
   
   abstract FunctionsToVerify : unit -> list<string * string>
   abstract Verify : string -> VerificationResult
   abstract DumpInternalsToFile : string * bool -> unit
   abstract Close : unit -> unit
   
   default this.Close () = ()
   
   member this.FindAllFunctions decls =
    if env.ShouldContinue then
      [ for d in decls do
          match d with
            | CAST.FunctionDecl f when f.Body.IsSome -> yield (f.Token.Filename, f.Name)
            | _ -> yield! [] ]
    else []
 
 type [<AbstractClass>] Plugin() =
   let messageHandlerEvent = new Event<string>()
   let messageHandler = new DelegateEvent<MessageHandler>()
   let stopWatches = glist []
   
   abstract Name : unit -> string
   abstract Help : unit -> string
   abstract IsModular : unit -> bool
   abstract UseCommandLineOptions : GList<string> -> unit
   abstract UseOptions : Helper.Options -> unit
   // depending on IsModular one uses FunctionVerifier or method Verify
   abstract GetFunctionVerifier : string * TransHelper.TransEnv * list<Top> -> FunctionVerifier
   abstract Verify : string * TransHelper.TransEnv * list<Top> -> unit
   
   
   default this.IsModular () = true
   default this.GetFunctionVerifier (_, _, _) = raise (System.NotImplementedException())
   default this.Verify (_, _, _) = raise (System.NotImplementedException())
   default this.UseOptions _ = ()


   member this.MessageHandler = messageHandlerEvent.Publish
   member this.RegisterStopwatch (s:Stopwatch) = 
     let rec repl i =
       if i >= stopWatches.Count then
         stopWatches.Add s
       else
         if s.ShouldReplace stopWatches.[i] then
           stopWatches.[i] <- s
         else repl (i + 1)
     repl 0
   member this.Stopwatches = (stopWatches :> seq<Stopwatch>)
