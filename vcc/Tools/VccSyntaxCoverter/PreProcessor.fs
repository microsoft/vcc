module Microsoft.Research.Vcc.SyntaxConverter.PreProcessor

open Microsoft.FSharp.Text
open Microsoft.Research.Vcc.SyntaxConverter.Ast

let apply toks =
  let rec aux = function
    | Tok.Op (p, "!") :: AfterWs (FnApp ("set_in"|"set_in0" as name, args, rest)) ->
      Tok.Op (p, "!") :: paren "(" [Tok.Id (p, name); paren "(" args] :: aux rest
    | Tok.Group (p, s, toks) :: rest ->
      Tok.Group (p, s, aux toks) :: aux rest
    | t :: rest -> t :: aux rest
    | [] -> []
  aux toks

