module Microsoft.Research.Vcc.TokenCounter.Counter

type Tok = Token.Tok

type SubCount =
  {
    mutable lines : int
    mutable tokens : int
  }

  static member Zero() = { lines = 0; tokens = 0 }

  member this.Add (other:SubCount) =
    { lines = this.lines + other.lines
      tokens = this.tokens + other.tokens }

type Count =
  {
    spec : SubCount
    phys : SubCount
    real_lines : int
  }

  static member Zero() = { spec = SubCount.Zero(); phys = SubCount.Zero(); real_lines = 0 }

  member this.Curr inSpec =
    if inSpec then this.spec else this.phys 

  member this.Add (other:Count) =
    { spec = this.spec.Add other.spec
      phys = this.phys.Add other.phys
      real_lines = this.real_lines + other.real_lines }

let rec skipWs = function
  | Tok.Whitespace _ :: xs
  | Tok.Comment _ :: xs -> skipWs xs
  | xs -> xs

let (|AfterWs|) toks = skipWs toks
    
let compute toks =
  let total = ref (Count.Zero())
  let curline = ref (Count.Zero())
  let inSpec = ref false
  let specLevel = ref 0

  let specSb = new System.Text.StringBuilder()
  let physSb = new System.Text.StringBuilder()

  let rec work xs =
    let mutable nextInSpec = !inSpec
    let mutable dontCount = false
    match xs with
      | Tok.Id "_" :: AfterWs (Tok.Op "(" :: _) when not !inSpec ->
        dontCount <- true
        inSpec := true
        nextInSpec <- true
        specLevel := 0
      | Tok.Op "(" :: _ when !inSpec ->
        dontCount <- !specLevel = 0
        incr specLevel
      | Tok.Op ")" :: _ when !inSpec ->
        decr specLevel
        if !specLevel = 0 then
          dontCount <- true
          nextInSpec <- false
      | _ -> ()

    let wr (s:string) = 
      let sb = if !inSpec then specSb else physSb
      sb.Append s |> ignore

    let eol () =
      let cl = !curline
      if cl.phys.tokens = 0 && cl.spec.tokens = 0 then ()
      elif cl.phys.tokens > cl.spec.tokens then
        wr "\n"
        cl.phys.lines <- 1
      else
        wr "\n"
        cl.spec.lines <- 1
      total := (!total).Add cl
      curline := Count.Zero()

    if xs = [] then 
      eol()
    else
      match xs.Head with
        | Tok.Literal s
        | Tok.Op s 
        | Tok.Id s ->
          wr s; wr " "
          let c = (!curline).Curr !inSpec
          if not dontCount then
            c.tokens <- c.tokens + 1
  
        | Tok.Whitespace ws ->
          if ws.Contains "\n" then eol()

        | Tok.Eof -> eol()
            
        | Tok.Comment _ -> ()

        | Tok.Invalid c -> failwith ("invalid " + c)

      inSpec := nextInSpec
      work xs.Tail

  work toks
  !total, specSb.ToString(), physSb.ToString()