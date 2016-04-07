//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

open System
open System.IO
open Microsoft.FSharp.Text.Lexing

open Ast
open PrettyPrinter
open RenameFields
open LoopDetection
open Lexer
open Parser

exception QuitException

[<EntryPoint>]
let main (args : string array) = 
    
    let return_value = ref (-1)
    printfn "Assembler Translator"

    match args with
    |[| "/?" |] -> printfn "Vx86 <filename>\n\nCalled without a filename, the tool asks for a filename on the console.\nWith a filename the given file will be loaded and a new file named 'filename'.asm will be created"
    |[| |] ->
      let mutable input = ""
      while input <> "quit" do
       
        try
            printf "Filename or 'quit' to exit: "
            input <- Console.ReadLine()
            
            match input with
            | "quit" -> raise QuitException
            | s ->
            printfn "Lexing [%s]" input

            let lexbuff = Lexing.LexBuffer<_>.FromTextReader (File.OpenText(input))
            lexbuff.EndPos <-{ pos_bol = 0;
                         pos_fname=input; 
                         pos_cnum=0;
                         pos_lnum=1 }
            
            printfn "Parsing..."
            let temp_program = Parser.start Lexer.tokenize lexbuff

            printfn "Infering Types..." // annotate types of expressions onto expressions
            let program = typeProg temp_program
            
            printfn "Renaming Struct Fields..." // renaming struct fields consisting of C keywords
            let _program = renameProg program;
            
            printfn "Pretty Printing..." // produce the C string from the syntax tree
            let result = evalProg _program
            
            printfn "Result:\n\n%s" (result)
            File.WriteAllText( input + ".c", "#include\"D:\\stmaus\\FELT\\Vcc2\\Headers\\Asm.h\"\n#include <stddef.h>\n\nCore core;\n\n" + result)
            
            return_value := 0
            
        with 
            | Failure(blah) as ex -> printf "Parse Exception found: %s\n" blah
            | Microsoft.FSharp.Text.Parsing.RecoverableParseError as ex -> printf "Unhandled RecoverableParseError Exception %s\n" ex.Message
            | Microsoft.FSharp.Text.Parsing.Accept(blah) as ex -> printf "Unhandled Accept Exception %s\n" ex.Message
            | QuitException -> printf "\nExit\n"
            | ex -> printfn "Unhandled Exception %s\n" (ex.Message)
        
        printfn ""
    | [| file_name |] ->
        try
            
            //printfn "Lexing [%s]" file_name

            let lexbuff = Lexing.LexBuffer<_>.FromTextReader (File.OpenText(file_name))
            lexbuff.EndPos <-{ pos_bol = 0;
                         pos_fname=file_name; 
                         pos_cnum=0;
                         pos_lnum=1 }
            
            //printfn "Parsing..."
            let temp_program = Parser.start Lexer.tokenize lexbuff
            
            //printfn "Loop Detection..."
            let t = loopProg temp_program
            
            //printfn "Infering Types..." // annotate types of expressions onto expressions
            let program = typeProg temp_program
            
            //printfn "Renaming Struct Fields..." // renaming struct fields consisting of C keywords
            let _program = renameProg program;
            
            //printfn "Pretty Printing..." // produce the C string from the syntax tree
            let result = evalProg _program
            
            File.WriteAllText( file_name + ".c", "#include\"D:\\stmaus\\FELT\\Vcc2\\Headers\\Asm.h\"\n#include <stddef.h>\n\nCore core;\n\n" + result)
            
            return_value := 0
            
        with 
            | Failure(blah) as ex -> printf "Parse Exception found: %s\n" blah
            | Microsoft.FSharp.Text.Parsing.RecoverableParseError as ex -> printf "Unhandled RecoverableParseError Exception %s\n" ex.Message
            | Microsoft.FSharp.Text.Parsing.Accept(blah) as ex -> printf "Unhandled Accept Exception %s\n" ex.Message
            | ex -> printfn "Unhandled Exception %s\n" (ex.Message)
        
    | _ ->
      printf "Too many arguments, try /? for help!"

    //Exit Code
    !return_value

