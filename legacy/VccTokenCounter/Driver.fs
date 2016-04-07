module Microsoft.Research.Vcc.TokenCounter.Driver

open Microsoft.Research.Vcc.TokenCounter.Token
open Microsoft.Research.Vcc.TokenCounter.Counter

type Tok0 = Token.Tok

let err pos s = raise (SyntaxError (pos, s))

let dbg = ref false
let needHeader = ref true
let total = ref (Count.Zero())
let toks = ref false
let latex = ref false
let maxOverhead = ref 2000


let tokenize lexbuf =
  let rec getToks acc = 
    let tok0 = Lexer.token lexbuf
    let pos = { line = lexbuf.StartPos.Line; column = lexbuf.StartPos.Column }
    match tok0 with
      | Tok0.Invalid s ->
        err pos ("invalid character in input '" + s + "'")
      | Tok0.Eof -> List.rev acc, pos.line
      | _ -> getToks (tok0 :: acc)
  getToks []
   
let lexFile filename = 
  let path = System.IO.Path.GetDirectoryName filename
  tokenize (Lexing.LexBuffer<char>.FromTextReader (System.IO.File.OpenText filename))    

let dump fn (c:Count) =
  let perc a b =
    if b = 0 then sprintf "%9s" ""
    else sprintf "%8d%%" (a * 100 / b)
  if !toks then
    if !needHeader then
      printf "  SPEC /   PHYS =  OVERHEAD   FILENAME\n"
      needHeader := false
    printf "%6d / %6d = %s   %s\r\n" c.spec.tokens c.phys.tokens (perc c.spec.tokens c.phys.tokens) fn
  elif !latex then
    if !needHeader then
      printf "\\begin{array}{|l|r|r|r|}\n"
      printf "\\hline\n"
      printf "\\mbox{File} & \\mbox{Specs} & \\mbox{Code} & \\mbox{Ratio} \\\\\n"
      printf "\\hline\n"
      needHeader := false
    if c.phys.lines * !maxOverhead / 100 < c.spec.lines then
      c.spec.lines <- c.spec.lines + c.phys.lines
      c.phys.lines <- 0
    let p = perc c.spec.lines c.phys.lines
    let p = p.Replace ("%", "\\%")
    let fn = fn.Replace ("_", "\\_")
    if c.phys.lines = 0 then
      printf "\\mbox{%-30s} & %6d & %6s & \\\\\n" fn c.spec.lines ""
    else 
      printf "\\mbox{%-30s} & %6d & %6d & %s \\\\\n" fn c.spec.lines c.phys.lines p
  else
    if !needHeader then
      printf "  SPEC /   PHYS =  OVERHEAD  +BLANK  FILENAME\n"
      needHeader := false
    let blanks = c.real_lines - c.spec.lines - c.phys.lines
    printf "%6d / %6d = %s  +%-6d %s\r\n" c.spec.lines c.phys.lines (perc c.spec.lines c.phys.lines) blanks fn

let go filename = 
  try
    if not (System.IO.File.Exists filename) then
      raise (SyntaxError (fakePos, "file does not exists"))
    let toks, lines = lexFile filename
    let count, specStr, physStr = Counter.compute toks
    let count = { count with real_lines = lines }
    if !dbg then
      System.IO.File.WriteAllText (filename + "-spec", specStr)
      System.IO.File.WriteAllText (filename + "-phys", physStr)
    dump filename count
    total := (!total).Add count
  with SyntaxError (p, s) ->
    System.Console.WriteLine ("{0}:{1}: {2}", filename, p, s)
    
let main() =
  let args = System.Environment.GetCommandLineArgs()
  let mutable fileCount = 0
  for i = 1 to args.Length - 1 do
    match args.[i] with
      | "-d" -> dbg := true
      | "-t" -> toks := true
      | "-l" -> latex := true
      | x when x.StartsWith "-m" ->
        maxOverhead := System.Int32.Parse (x.Substring 2)
      | x -> 
        fileCount <- fileCount + 1
        go x

  if fileCount = 0 then
    printf "Usage: %s [-d(ebug)] [-t(okens)] [-l(atex)] [-m<max overhead in %%>] files.c....\r\n" args.[0]
    printf "The -m option defaults to -m2000. It currently only works for LaTeX mode. It means\r\n"
    printf "that if annotation overhead in file is over 2000%%, then all lines should be counted\r\n"
    printf "as spec. This is useful to discard things like #include, which always count as physical.\r\n"
  elif fileCount > 1 then
    if !latex then
      printf "\\hline\n"
    dump "TOTAL" !total
    if !latex then
      printf "\\hline\n\end{array}\n"

main()