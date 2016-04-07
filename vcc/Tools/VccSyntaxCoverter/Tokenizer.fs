namespace Microsoft.Research.Vcc.SyntaxConverter
open Microsoft.FSharp.Text
open Microsoft.Research.Vcc.SyntaxConverter.Ast

module Tokenizer =
  type Tok0 = PreToken.PreTok
  
  let rec tokenize depth path lexbuf : list<Tok> =
    let err pos s = raise (SyntaxError (pos, s))
    
    let rec getToks acc = 
      let tok0 = Lexer.token lexbuf
      let pos = { line = lexbuf.StartPos.Line; column = lexbuf.StartPos.Column }
      match tok0 with
        | Tok0.Invalid s ->
          err pos ("invalid character in input '" + s + "'")
        | Tok0.Eof -> List.rev acc
        | _ -> getToks ((pos, tok0) :: acc)
    
    let rec group acc = function
      | [] -> List.rev acc, []
      | (pos, tok) :: rest ->
        match tok with
          | Tok0.Op (")"|"]"|"}") ->
            List.rev acc, (pos, tok) :: rest
          | Tok0.Op ("("|"["|"{" as c) ->
            match group [] rest with
              | subGroup, ((_, Tok0.Op c') :: rest) when (closing c) = c' ->
                group (Tok.Group (pos, c, subGroup) :: acc) rest
              | _, [] -> err pos ("did not find " + c.ToString() + " before end of the file")
              | _, ((pos', Tok0.Op c') :: _) -> err pos' ("expecting " + (closing c).ToString() + "; got " + c'.ToString())
              | _, (_ :: _) -> failwith "can't happen"
            
          | _ ->
            let add =
              match tok with
                | Tok0.Id n -> Tok.Id (pos, n)
                | Tok0.Comment s -> Tok.Comment (pos, s)
                | Tok0.Op n -> Tok.Op (pos, n)
                | Tok0.Literal n -> Tok.Literal (pos, n)
                | Tok0.Whitespace n -> Tok.Whitespace (pos, n)
                | Tok0.Eof
                | Tok0.Invalid _ -> failwith ""
            group (add :: acc) rest
                
    let topGroup line =
      match group [] line with
        | res, [] -> res
        | res, (pos, Tok0.Op c) :: _ ->
          err pos ("unmatched " + c.ToString())
        | _ -> failwith "can't happen"
            
    topGroup (getToks [])
   
  let fromFile filename = 
    let path = System.IO.Path.GetDirectoryName filename
    tokenize 0 path (Lexing.LexBuffer<char>.FromTextReader (System.IO.File.OpenText filename))    