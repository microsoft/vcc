namespace Microsoft.Research.Vcc.SyntaxConverter

module PreToken =
  type PreTok =
    | Id of string
    | Literal of string
    | Op of string
    | Comment of string
    | Whitespace of string
    | Eof
    | Invalid of string
    