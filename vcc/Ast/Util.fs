//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------


(*
  Utilities that are general to the framework/F#, not specific to VCC.
*)

#light

namespace Microsoft.Research.Vcc
  module Util = 
    open System.Text
    open Microsoft.FSharp.Math
  
    type GList<'a> = System.Collections.Generic.List<'a>
    type Dict<'a, 'b> = System.Collections.Generic.Dictionary<'a, 'b>  
    type bigint = System.Numerics.BigInteger
    type HashSet<'a> = System.Collections.Generic.HashSet<'a>
    
    
    let glist (l:list<_>) = new GList<_> (l)
    let gdict () = new Dict<_,_>()
    let objDict() = new Dict<obj, _>() // new ObjEqualityComparer())
     
    let die() = failwith "confused, will now die"

    let rec _try_assoc elem = function
      | [] -> None
      | (a,b) :: _ when elem = a -> Some b
      | _ :: tail -> _try_assoc elem tail

    let _list_mem elem = List.exists (fun e -> e = elem)
    
    let revMapSome f =
      List.fold (fun acc e -> match f e with Some x -> x :: acc | None -> acc) []
      
    let _list_rev_map f =
      let rec _list_rev_map_acc acc f = function
        | [] -> acc
        | h :: t -> _list_rev_map_acc (f h :: acc) f t
      _list_rev_map_acc [] f    
        
    let lookupWithDefault (dict:Dict<_,_>) defl key =
      match dict.TryGetValue key with
        | true, v -> v
        | _ -> defl
    
    let withDefault defl = function
      | Some x -> x
      | None -> defl

    let (|ZeroBigInt|_|) (x:bigint) =
      if x = bigint.Zero then Some (ZeroBigInt)
      else None      
    
    let (|OneBigInt|_|) (x:bigint) =
      if x = bigint.One then Some (OneBigInt)
      else None   
      
      
    let wrb (b:StringBuilder) s : unit = b.Append (s:string) |> ignore
    
    let memoize f =
      let cache = new System.Collections.Generic.Dictionary<_,_> ()
      fun x ->
        let (found, res) = cache.TryGetValue x
        if found then res
        else
          let res = f x
          cache.Add (x, res)
          res
          
    let memoize0 f =
      let cache = ref None
      fun () ->
        match !cache with
          | Some x -> x
          | None ->
            let x = f()
            cache := Some x
            x
            
    let toString f =
      let b = StringBuilder ()
      f b
      b.ToString ()
    
    let rec commas b f args =
      match args with
        | [] -> ()
        | [a] -> f a
        | a :: rest ->
          f a
          wrb b ", "
          commas b f rest
      
    let doArgsAndTArgsb b f tf op args targs : unit =
      let wr = wrb b
      wr op
      match targs with
        | [] -> ()
        | _ -> wr "<"; commas b tf targs; wr ">"
      wr "("
      commas b f args
      wr ")"
    
    let doArgsb b f op args : unit =
      let wr = wrb b
      wr op
      wr "("
      commas b f args
      wr ")"

    let empty () = new Map<_,_> ([])
    
    let listToString (lst:list<'a>) =
      "[" + (lst |> List.map (fun (x:'a) -> (x:>obj).ToString()) |> String.concat "; ") + "]"      
      
    let dbgBreak() = System.Diagnostics.Debugger.Break()
    
    type UniqueList<'a when 'a : equality>() =
      let l = glist[]
      let d = gdict()
    
      member this.Add (e:'a) =
        if d.ContainsKey e then ()
        else
          d.Add (e, l.Count)
          l.Add e
      member this.AddRange (elts:seq<'a>) =
        Seq.iter this.Add elts 
      member this.Remove e =
        let idx = d.[e]
        if idx <> l.Count - 1 then
          let e' = l.[l.Count - 1]
          l.[idx] <- e'
          d.[e'] <- idx
        d.Remove e |> ignore
        l.RemoveAt (l.Count - 1)
      member this.Elements = l :> seq<'a>
      member this.Contains e = d.ContainsKey e 
      member this.Count = l.Count

      interface System.Collections.Generic.IEnumerable<'a> with
        member this.GetEnumerator() = l.GetEnumerator() :> System.Collections.Generic.IEnumerator<'a>

      interface System.Collections.IEnumerable with
        member this.GetEnumerator() = l.GetEnumerator() :> System.Collections.IEnumerator

    let ulist() = UniqueList<_>()    