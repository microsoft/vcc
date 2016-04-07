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
  open Microsoft.Boogie

  module BoogieToken =

    type public Token(tok : Microsoft.Research.Vcc.Token) =

      member this.Related = 
        match tok.Related with 
          | None -> None
          | Some related -> Some(Token(related))

      interface Microsoft.Boogie.IToken with 
        
        member this.IsValid 
          with get() = true

        member this.kind
          with get() = 0
          and set _ = failwith "readonly"

        member this.filename
          with get() = tok.Filename
          and set _ = failwith "readonly"

        member this.pos
          with get() = tok.Byte
          and set _ = failwith "readonly"

        member this.col
          with get() = tok.Column
          and set _ = failwith "readonly"

        member this.line
          with get() = tok.Line
          and set _ = failwith "readonly"

        member this.``val``
          with get() = tok.Value
          and set _ = failwith "readonly"

      member this.tok = tok

    let Strip(t : IToken) =
      match t with
        | :? Token as b -> b.tok
        | _ -> Microsoft.Research.Vcc.Token.NoToken
