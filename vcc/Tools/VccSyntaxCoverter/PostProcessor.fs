namespace Microsoft.Research.Vcc.SyntaxConverter
open Microsoft.FSharp.Text
open Microsoft.Research.Vcc.SyntaxConverter.Ast

module PostProcessor =

  let apply addCompilerOptionForTestSuite addInclude toks = 
    let nl = Tok.Whitespace(fakePos, "\n") 
    let rec coalesceWhitespace acc = function
      | [] -> List.rev acc
      | Tok.Whitespace(p0, ws0) :: Tok.Whitespace(p1, ws1) :: rest -> coalesceWhitespace acc (Tok.Whitespace(p0, ws0 + ws1) :: rest)
      | Tok.Group (p, s, toks) :: rest -> coalesceWhitespace (Tok.Group(p, s, coalesceWhitespace [] toks) :: acc) rest
      | tok :: rest -> coalesceWhitespace (tok :: acc) rest
    let inc = if addInclude then [Comment (fakePos, "#include <vcc.h>"); nl] else []
    let rec addNewSyntaxOption atStartOfFile = function
      | Whitespace _ :: rest -> addNewSyntaxOption atStartOfFile rest
      | Comment(p, s) :: rest when addCompilerOptionForTestSuite && s.StartsWith("`/") 
        -> Comment(p, s + " /newsyntax") :: nl :: inc @ rest
      | toks -> 
        let toks = Comment(fakePos, "`/newsyntax") :: nl :: inc @ toks
        if not atStartOfFile then nl :: toks else toks
    let rec apply' acc = function
      // _(ghost out ...) ==> _(out ...)
      | Tok.Id(p0, "_") :: Tok.Group(p1, "(", Tok.Id(p2, "ghost") :: Tok.Whitespace _ :: Tok.Id(p3, "out") :: gRest) :: rest ->
        apply' acc (Tok.Id(p0, "_") :: Tok.Group(p1, "(", Tok.Id(p3, "out") :: gRest) :: rest)
      // _(:G) _(ghost ...) ==> _(ghost _(:G) ...)
      |  Tok.Id(_, "_") :: (Tok.Group(_, "(", Tok.Op(_, ":") :: Tok.Id(_, _) :: _) as groupName) :: Tok.Whitespace _ :: 
         Tok.Id(p0, "_") :: Tok.Group(p1, "(", Tok.Id(p2, "ghost") :: gRest) :: rest ->
         apply' acc (Tok.Id(p0, "_") :: Tok.Group(p1, "(", Tok.Id(p2, "ghost") :: Tok.Whitespace(fakePos, " ")  :: Tok.Id(fakePos, "_") :: groupName :: gRest) :: rest)
      | Tok.Comment(p, s) as tok :: rest when s.StartsWith("`") && s.[s.Length - 1] = '`' ->
        match eatWs rest with
         | [] -> apply' (tok :: acc) []
         | _ -> apply' (tok :: acc) (addNewSyntaxOption false rest)
      | Tok.Group (p, s, toks) :: rest -> apply' (Tok.Group (p, s, apply' [] toks) :: acc) rest  
      | t :: rest -> apply' (t::acc) rest
      | [] -> List.rev acc

    let rec fixupTrueFalse acc = function
      | (Tok.Id (_, "_") as i) :: (Tok.Group (_, _, _) as g) :: rest ->
        fixupTrueFalse (g :: i :: acc) rest
      | Tok.Id (p0, "\\true") :: rest ->
        fixupTrueFalse (Tok.Id (p0, "true") :: acc) rest
      | Tok.Id (p0, "\\false") :: rest ->
        fixupTrueFalse (Tok.Id (p0, "false") :: acc) rest
      | Tok.Id (p0, "\\objset") :: rest ->
        fixupTrueFalse (Tok.Id (p0, "ptrset") :: acc) rest
      | Tok.Group (p, o, toks) :: rest ->
        fixupTrueFalse (Tok.Group (p, o, fixupTrueFalse [] toks) :: acc) rest
      | t :: rest ->
        fixupTrueFalse (t :: acc) rest
      | [] -> List.rev acc

    let toks = toks |> coalesceWhitespace [] |> apply' [] |> fixupTrueFalse []
    if addCompilerOptionForTestSuite then addNewSyntaxOption true toks else toks
      