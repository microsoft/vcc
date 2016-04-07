namespace Microsoft.Research.Vcc.SyntaxConverter
open Microsoft.FSharp.Text

module Ast =
  type P = PreToken.PreTok
  
  type Pos = 
    { 
      line : int; 
      column : int 
    }
    
    override this.ToString() =
      (this.line+1).ToString() + ":" + (this.column+1).ToString()
  
  let fakePos = { line = 0; column = 0 }
  
  exception SyntaxError of Pos * string
  
  let closing = function
    | "(" -> ")"
    | "[" -> "]"
    | "{" -> "}"
    | "" -> ""
    | _ -> failwith ""

  type Tok =
    | Id of Pos * string
    | Literal of Pos * string
    | Op of Pos * string
    | Comment of Pos * string
    | Whitespace of Pos * string
    | Group of Pos * string * list<Tok>
    
    override this.ToString() =
      let sb = System.Text.StringBuilder()
      let wr (s:string) = sb.Append s |> ignore
      let rec pr = function
        | Id (_, s)
        | Literal (_, s)
        | Op (_, s)
        | Comment (_, s)
        | Whitespace (_, s) -> wr s
        | Group (_, c, toks) ->
          wr c
          List.iter pr toks
          wr (closing c)
      pr this
      sb.ToString()

    static member Sequence lst = Group (fakePos, "", lst)
    
    member this.Pos =
      match this with
        | Id (p, _)
        | Literal (p, _)
        | Op (p, _)
        | Comment (p, _)
        | Whitespace (p, _)
        | Group (p, _, _) -> p

  let space = Tok.Whitespace(fakePos, " ")

  let id n = Tok.Id (fakePos, n)
  
  let rec eatWs = function
    | Tok.Whitespace (_, _) :: rest -> eatWs rest
    | x -> x

  let (|AfterWs|) toks = eatWs toks
  let (|FnApp|_|) = function
    | AfterWs (Tok.Id (_, n) :: AfterWs (Tok.Group (_, "(", args) :: rest)) ->
      Some (n, args, rest)
    | _ -> None

  let eatWsEx l = 
    let rec aux acc = function
      | Tok.Whitespace (_, _) as w :: rest -> aux (w :: acc) rest
      | x -> (List.rev acc, x)
    aux [] l
  
  let poss = function
    | [] -> fakePos
    | (x:Tok) :: _ -> x.Pos
  
  let trim toks =
    toks |> List.rev |> eatWs |> List.rev |> eatWs
    
  let paren p toks =
    Tok.Group (fakePos, p, trim toks)
    
  let parenOpt toks =
    match trim toks with
      | [] -> Tok.Whitespace(fakePos, "")
      | [tok] -> tok
      | toks -> paren "(" toks

  let fnApp fnName toks = 
    let p = poss toks 
    [Tok.Id (p, fnName); paren "(" toks]
    
  let spec kw toks = 
    let p = poss toks 
    fnApp "_" (Tok.Id (p, kw) :: Tok.Whitespace (p, " ") :: toks)
    
