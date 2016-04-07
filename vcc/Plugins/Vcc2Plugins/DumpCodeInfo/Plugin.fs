//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

namespace Microsoft.Research.Vcc

  module DumpCodeInfo =
    open Microsoft.Research.Vcc
    open Microsoft.FSharp.Math
    open CAST

    [<System.ComponentModel.Composition.Export("Microsoft.Research.Vcc.Plugin")>]
    type ContractGeneratorPlugin() =
      inherit Microsoft.Research.Vcc.Plugin()

      let dbg() = System.Diagnostics.Debugger.Break()
      let wr (s:string) = System.Console.Write(s)

      let pluginOptions = ref []
      let verifiedCOptions = ref null

      let die() = failwith "confused, will now die"

      let hasCustomAttr n = List.exists (function VccAttr (n', _) -> n = n' | _ -> false)

      let commas (separator:string) p elems =
        let rec loop first = function
          | [] -> ()
          | e::es ->
            if not first then wr separator
            p e
            loop false es
        loop true elems

      override this.IsModular() = false
      override this.Help() = "Don't panic!"
      override this.Name() = "codeinfo"
      override this.UseCommandLineOptions options = pluginOptions := [ for o in options -> o ]
      override this.UseVccOptions options = verifiedCOptions := options

      override this.Verify(filename, env, decls) =
        let functionDependencies (fn:Function) =
          let pureImplDeps = new HashSet<_>()
          let physImplDeps = new HashSet<_>()
          let pureContractDeps = new HashSet<_>()
          let physContractDeps = new HashSet<_>()

          let visit (pureDeps:HashSet<_>) (physDeps:HashSet<_>) ctx self = function
            | CAST.Call(_, fn, _, _) ->
              if ctx.IsPure then pureDeps.Add fn |>ignore  else physDeps.Add fn |> ignore
              true
            | _ -> true

          match fn.Body with
            | None -> ()
            | Some e -> e.SelfCtxVisit(false, (visit pureImplDeps physImplDeps))

          List.iter (fun (e:Expr) -> e.SelfCtxVisit(true, (visit pureContractDeps physContractDeps)))
            (fn.Reads @ fn.Writes @ fn.Requires @ fn.Ensures)

          ( [ for k in pureImplDeps -> k ], [ for k in physImplDeps -> k],
            [ for k in pureContractDeps -> k ], [ for k in physContractDeps -> k])

        let doFunction (fn:Function) =
          let (pureImplDeps, physImplDeps, pureContractDeps, physContractDeps) = functionDependencies fn

          assert (physContractDeps = [])

          let wrFn (fn:Function) =
            wr (fn.Name + "(")
            commas ", " (fun t -> wr (t.ToString())) fn.Parameters
            wr (") : " + fn.RetType.ToString())

          let wrFnName (fn:Function) = wr (fn.Name)

          let wrAttr =
            let wr' s = wr ("\t\t" + s + "\n")
            let wrVcc s (o:obj) = wr' ("vcc(" + s + "," + o.ToString() + ")")
            function
              | IntBoogieAttr(s,n) -> wrVcc s n
              | BoolBoogieAttr(s,b) -> wrVcc s b
              | VccAttr(s,s1) -> wrVcc s s1
              | _ -> ()

          let wrDeps = function
            | [] -> wr "\t\t<none>\n"
            | fns -> for fn in fns do wr "\t\t"; wrFnName fn; wr "\n"

          let wrAttrs = function
            | [] -> wr "\t\t<none>\n"
            | attrs -> List.iter wrAttr attrs

          let wrFlags (fn:Function) =
            if fn.IsPure || fn.IsSpec then
              if fn.IsPure then wr "\t\tispure\n"
              if fn.IsSpec then wr "\t\tspec\n"
              if fn.IsStateless then wr "\t\tstateless\n"
            else
              wr "\t\t<none>\n"

          let tokenLocation (t:Token) =
            sprintf "%s(%d,%d)" t.Filename t.Line t.Column

          wr "function: "; wrFn fn; wr "\n"
          wr "\tfilename:\n\t\t";
          wr (tokenLocation fn.Token);
          wr "\n"
          wr "\tflags:\n"
          wrFlags fn
          wr "\tcontract dependencies:\n"
          wrDeps pureContractDeps
          match fn.Body with
            | None -> ()
            | Some e ->
                wr "\tpure implementation dependencies:\n"
                wrDeps pureImplDeps
                wr "\tphysical implementation dependencies:\n"
                wrDeps physImplDeps
          wr "\tattributes:\n"
          wrAttrs fn.CustomAttr
          wr "\n"
          let hasRequiresFalse = List.exists (function BoolLiteral(_,false) -> true | _ -> false) (fn.Requires)
          wr "\tinfo:\n"
          if hasRequiresFalse then wr "\t\trequires false\n"

        for d in decls do
          match d with
            | Top.FunctionDecl(fn) -> doFunction fn
            | _ -> ()
