open Microsoft.Research.Vcc.SyntaxConverter
open Microsoft.Research.Vcc.SyntaxConverter.Ast

let go filename = 
  try
    if not (System.IO.File.Exists filename) then
      raise (SyntaxError (fakePos, "file does not exists"))
    let toks = 
      Tokenizer.fromFile filename |> PreProcessor.apply |> Rules.apply
    let isTestSuiteSource = 
      let extension = System.IO.Path.GetExtension(filename)
      extension <> ".c" && extension <> ".h"
    let hasInclude =
      let text = System.IO.File.ReadAllText filename
      text.Contains "#include"
    let toks = PostProcessor.apply isTestSuiteSource (not hasInclude) toks
    let outf = System.IO.File.CreateText (filename + ".out")
    let outs = (Tok.Group (fakePos, "", toks)).ToString()
    let outs = outs.Replace ("\n", "\r\n")
    outf.Write (outs)
    outf.Close()
  with SyntaxError (p, s) ->
    System.Console.WriteLine ("{0}:{1}: {2}", filename, p, s)
    
let main() =
  Rules.init()
  let args = System.Environment.GetCommandLineArgs()
  for i = 1 to args.Length - 1 do
    go args.[i]
      

main()
