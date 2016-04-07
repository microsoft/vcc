//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.Util

  module Helper =

    [<AbstractClass>]
    type public Options() =
      abstract TerminationForPure : bool with get
      abstract TerminationForGhost : bool with get
      abstract TerminationForAll : bool with get
      abstract DefExpansionLevel : int with get
      abstract YarraMode : bool with get
      abstract DeterminizeOutput : bool with get
      abstract OpsAsFunctions : bool with get
      abstract PipeOperations : string seq with get
      abstract DumpTriggers : int with get
      abstract PrintCEVModel : bool with get
      abstract ExplicitTargetsGiven : bool with get
      abstract AggressivePruning : bool with get
      abstract Functions : string seq with get
      abstract WeightOptions : string seq with get

    [<AbstractClass>]
    type public Env(options:Options) =

      let currentId = ref 0
      let pureCalls = new Dict<string,string>()

      abstract PointerSizeInBytes : int with get

      abstract member Oops : Token * string -> unit

      abstract member Die : unit -> 'a

      abstract member Die : Token -> 'a

      abstract ErrorReported : bool with get

      abstract member Error : Token * int * string * Token option -> unit

      // 9100 <= code <= 9199; First available: 9127
      abstract member Warning : Token * int * string * Token option -> unit

      // 9601 <= code <= 9799; First available: 9751
      member this.Error(token, code, msg) = this.Error(token, code, msg, None)

      // 9300 <= code <= 9399; First available: 9327
      member this.GraveWarning(token, code, msg) = this.GraveWarning(token, code, msg, None)

      member this.GraveWarning(token, code, msg, related) = this.Warning(token, code, "[possible unsoundness]: " + msg, related)

      member this.Warning(token, code, msg) = this.Warning(token, code, msg, None)

      member this.Panic (msg:string) =
        this.Oops (Token.NoToken, msg)
        this.Die ()

      member this.Options = options
   
      member this.UniqueId () =
        incr currentId
        !currentId

      member this.PureCallSignature name =
        match pureCalls.TryGetValue name with
          | true, s -> Some s
          | _ -> None
      
      member this.AddPureCall (name, signature) =
        pureCalls.[name] <- signature
