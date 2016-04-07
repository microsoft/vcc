module Microsoft.Research.Vcc.TokenCounter.Token

type Pos = 
  { 
    line : int; 
    column : int 
  }
  
  override this.ToString() =
    (this.line+1).ToString() + ":" + (this.column+1).ToString()

let fakePos = { line = 0; column = 0 }

exception SyntaxError of Pos * string

type Tok =
  | Id of string
  | Literal of string
  | Op of string
  | Comment of string
  | Whitespace of string
  | Eof
  | Invalid of string
  