namespace SyntaxHighlighting

open Microsoft.FSharp.Text.Lexing

module Parser =

  let Parse text = 
    SyntaxHighlighting.FsParser.reset()
    let lexbuf = LexBuffer<char>.FromString(text)
    try
      SyntaxHighlighting.FsParser.start Lexer.tokenize lexbuf
    with ex -> ()

    SyntaxHighlighting.FsParser.result()



  

