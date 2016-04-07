//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

#light

namespace Microsoft.Research.Vcc
  open Microsoft.Research.Vcc
  open Microsoft.Research.Vcc.Util

  type Stopwatch(name:string) =
     let stopwatch = new System.Diagnostics.Stopwatch()
     let mutable startCount = 0
     let mutable running = false
     let mutable handicap = int64 0
     member this.Running = running
     member this.Start() = 
       if running then
         failwith "stopwatch already running"
       startCount <- startCount + 1
       running <- true
       stopwatch.Start()
     member this.Stop() =
       if not running then
         failwith "stopwatch already running"
       running <- false
       stopwatch.Stop()
     member this.Elapsed = handicap + stopwatch.ElapsedMilliseconds
     member this.Name = name
     member this.Display() =
       System.String.Format("{0,30} {1:0.000}", name, float this.Elapsed / 1000.0)
     member this.ShouldReplace (that:Stopwatch) =
       if this = that then true
       else
         if name = that.Name then
           if that.Running then
             failwith "replaced stopwatch is running"
           handicap <- handicap + that.Elapsed
           true
         else false
     member this.Run f a =
       try
         this.Start()
         f a
       finally this.Stop()
       
    
  module public TransHelper =
   
    let alwaysPureCallList =
                [ 
                  // signature letter:
                  //   t - typed pointer (will add encoding of type)
                  //   p - typed pointer (nothing gets added)
                  //   S - $s
                  //   s - old($s)
                  //   a - ptrset
                  //   i - _vcc_size_t
                  //   . - just pass whatever was there
                  "admissibility_pre",      "Sp";
                  "good_for_post_admissibility", "S";
                  "array_members",          "ti";
                  "array_range",            "Sti";
                  "array",                  ".i";
                  "as_array",               "ti";
                  "byte_ptr_subtraction",   "pp";
                  "change_owner",           "..p";
                  "closed",                 "Sp";
                  "nested",                 "Sp";
                  "claims_obj",             "pp";
                  "claims",                 "p.";
                  "current_state",          "S";
                  "is_claimable",           ".";
                  "union_active",           "pp";
                  "not_shared",             "Sp";
                  "ref_cnt",                "Sp";
                  "valid_claim",            "Sp";
                  "depends",                "sSpp";
                  "dont_instantiate",       "p";
                  "dont_instantiate_int",   "i";
                  "emb",                    "Sp";
                  "simple_emb",             "p";
                  "extent",                 "Sp";
                  "full_extent",            "p";
                  "get_fnptr",              "i.";
                  "get_memory_allocator",   "";
                  "get_string_literal",     "ii";
                  "in_array",               "pti";
                  "in_domain",              "Spp";
                  "in_vdomain",             "Spp";
                  "in_claim_domain",        "pp";
                  "domain",                 "Sp";
                  "imply_inv",              "St";
                  "inlined_array",          "t";
                  "inv",                    "St";
                  "inv2",                   "sSt";
                  "inv2_when_closed",       "sSt";
                  "i1_to_ptr",              ".";
                  "i2_to_ptr",              ".";
                  "i4_to_ptr",              ".";
                  "i8_to_ptr",              ".";
                  "is",                     "p.";
                  "is_array",               "Sti";
                  "is_array_stateless",     "ti";
                  "is_array_emb",           "Stip";
                  "is_fresh",               "sSp";
                  "is_global",              "t";
                  "is_global_array",        "ti";
                  "is_malloc_root",         "Sp";
                  "is_mutable_array",       "Sti";
                  "is_object",              "p";
                  "is_object_root",         "Sp";
                  "is_thread_local_array",  "Sti";
                  "is_thread_local_array_inline",  "Sti";
                  "is_thread",              "p";
                  "me",                     "";
                  "mutable",                "Sp";
                  "thread_owned",           "Sp";
                  "non_null_array_range",   "ti";
                  "non_null_extent",        "Sp";
                  "non_null_set_singleton", "p";
                  "owner",                  "Sp";
                  "owns",                   "Sp";
                  "obj_eq",                 "pp";
                  "obj_neq",                "pp";
                  "wrapped",                "St";
                  "ptr_eq",                 "pp";
                  "ptr_neq",                "pp";
                  "ptr_to_i1",              "p";
                  "ptr_to_i2",              "p";
                  "ptr_to_i4",              "p";
                  "ptr_to_i8",              "p";
                  "ptr_to_u1",              "p";
                  "ptr_to_u2",              "p";
                  "ptr_to_u4",              "p";
                  "ptr_to_u8",              "p";
                  "thread_local",           "Sp";
                  "thread_local2",          "St";
                  "set_cardinality",        "a";
                  "set_disjoint",           "aa";
                  "set_difference",         "aa";
                  "set_empty",              "";
                  "set_eq",                 "aa";
                  "set_subset",             "aa";
                  "set_in",                 "pa";
                  "set_in0",                "pa";
                  "set_in2",                "pa";
                  "set_intersection",       "aa";
                  "set_singleton",          "p";
                  "set_union",              "aa";
                  "set_universe",           "";
                  "set_add_element",        "..";
                  "set_remove_element",     "..";
                  "sk_hack",                ".";
                  "span",                   "p";
                  "volatile_span",          "Sp";
                  "typed",                  "Sp";
                  "typed2",                 "St";
                  "typed2_phys",            "St";
                  "typed2_spec",            "St";
                  "typeof",                 "p";
                  "u1_to_ptr",              ".";
                  "u2_to_ptr",              ".";
                  "u4_to_ptr",              ".";
                  "u8_to_ptr",              ".";   
                  "update_heap_owns",       ".pa";               
                  "vs_ctor",                "Sp";
                  "when_claimed",           "";
                  "mutable_increases",      "sS";
                  "meta_eq",                "sS";
                  "program_entry_point",    "S";
                  "always_by_claim",        "pp";
                  "reads_check_pre",        "S";
                  "reads_check_post",       "S";
                  "gemb",                   "p";
                  "start_here",             "";
                  "full_stop",              "S";
                  "pre_wrap",               "S";
                  "pre_unwrap",             "S";
                  "pre_static_wrap",        "S";
                  "pre_static_unwrap",      "S";
                  "pre_wrap_set",           "S";
                  "pre_unwrap_set",         "S";
                  "unwrap_check_pre",       "Sp";
                  "good_for_post_can_unwrap","S";
                  "unwrap_post",            "..pp";
                  "unwrap_post_claimable",  "..pp";
                  "wrap_post",              "..pp";
                  "take_over",              ".pp";
                  "start_release",          "..";
                  "release",                "..pp";
                  "expect_unreachable",     "";
                  "possibly_unreachable",   "";
                  "bv_lemma",               ".";
                  "is_non_primitive_ptr",   "p";
                  "extent_mutable",         "Sp";
                  "extent_thread_local",    "Sp";
                  "extent_zero",            "Sp";
                  "extent_is_fresh",        "sSp";
                  "inv_is_approved_by",     "sSp..";
                  "inv_is_owner_approved",  "sSp.";
                  "is_approved_by",         "...";
                  "is_owner_approved",      "..";
                  "updated_only_values",    "sS.";
                  "updated_only_domains",   "sS.";
                  "domain_updated_at",      "sS..";
                  "claims_claim",           "..";
                  "stuttering_pre","S.";
                  "is_admissibility_check", "";
                  "is_unwrap_check", "";
                  "is_stuttering_check", "";
                  "new_ownees", "S..";
                  "rec_eq", "..";
                  "account_claim", "Spp";
                  "is_ghost_ptr", "p";
                  "admissibility_start", "t";
                  "addr", "p";
                  "addr_eq", "pp";
                  "retype", "Sp";
                  "composite_extent", "St";
                  "assume", ".";
                ]
  
    type Transformer =
      | Expr of ((CAST.Expr -> CAST.Expr) -> CAST.Expr -> option<CAST.Expr>)
      | ExprCtx of (CAST.ExprCtx -> (CAST.Expr -> CAST.Expr) -> CAST.Expr -> option<CAST.Expr>)
      | Decl of (list<CAST.Top> -> list<CAST.Top>)
      | DoNothing
    
    type TransDesc =
      {
        Name : string;
        Func : Transformer;
        mutable Enabled : bool;
      }

      static member Mk (name : string, f : Transformer) =
        { Name = name; Func = f; Enabled = true }
      

    [<AbstractClass>]
    type public TransEnv (opts : Helper.Options) as this =
      inherit Helper.Env(opts)
      let stopwatches = ref []
      let sw name = 
        let s = new Stopwatch (name)
        stopwatches := s :: !stopwatches
        s

      let swTransformers = sw "AST transformers"
      let swPruning = sw "Pruning"
      
      let errorReported = ref false
      let transformers = new GList<_>()
      let topDecls = ref []
      let times = new Dict<_,_>()
      let dumpTime = ref false
             
      do
        List.iter (fun (n, s) ->  this.AddPureCall("_vcc_" + n, s)) alwaysPureCallList
     
      member this.Stopwatches = !stopwatches
      
      member this.SwPruning = swPruning

      override this.Die () : 'a =
        failwith "confused, will now die"

      override this.Die(tok : Token) : 'a =
        this.Oops(tok, "internal compiler error")
        this.Die()
                
      abstract ShouldDumpStack : bool with get
      
      member this.ShouldContinue = not this.ErrorReported
      
      member this.TopDecls = !topDecls
      
      member this.AddTransformer (name : string, func : Transformer) =
        let td = { Name = name; Func = func; Enabled = true } : TransDesc
        transformers.Add td
      
      member this.ApplyTransformers (decls : list<CAST.Top>) =
        let apply = function
          | Expr f -> CAST.deepMapExpressions f
          | ExprCtx f -> CAST.deepMapExpressionsCtx f
          | Decl f -> f
          | DoNothing -> (fun x -> x)
        let rec aux i decls =
          if i >= transformers.Count then 
            decls
          else 
            let t = transformers.[i]
            if not t.Enabled then
              aux (i + 1) decls
            else 
              topDecls := decls
              let start = System.DateTime.UtcNow
              let decls' = apply t.Func decls
              let tm = System.DateTime.UtcNow - start            
              times.[t.Name] <- tm.Ticks
              aux (i + 1) decls'
        try
          swTransformers.Start()
          try
            let res = aux 0 decls
            if !dumpTime then this.DumpTransformers()
            res
          with
            e -> 
              if this.ShouldContinue then reraise ()
              else []
        finally
          swTransformers.Stop()

      // the extension interface
      member this.AddTransformerAt (name : string, func : Transformer, after : string, off : int) =
        let td = TransDesc.Mk (name, func)
        let rec add i =
          if i >= transformers.Count then
            failwith ("transformer not found " + after)
          else if transformers.[i].Name = after then
            transformers.Insert (i + off, td)
          else add (i + 1)
        add 0

      member this.InterleaveTransformers f =
        let newTrans = transformers |> Seq.map f |> List.concat
        transformers.Clear ()
        transformers.AddRange newTrans
        
      member this.AddTransformerAfter (name : string, func : Transformer, after : string) =
        this.AddTransformerAt (name, func, after, 1)
      
      member this.AddTransformerBefore (name : string, func : Transformer, after : string) =
        this.AddTransformerAt (name, func, after, 0)
      
      member this.DisableTransformers (prefix : string) =
        for t in transformers do
          if t.Name.StartsWith prefix then t.Enabled <- false
          
      member this.RemoveTransformer (name : string) =
        let rec aux i =
          if i >= transformers.Count then
            failwith "no such transformer"
          else if transformers.[i].Name = name then
            let t = transformers.[i]
            transformers.RemoveAt i
            t
          else aux (i + 1)
        aux 0
      
      member this.ShouldDumpTime () =
        dumpTime := true
          
      member this.DumpTransformers () =
        for t in transformers do
          let kind =
            match t.Func with
              | Expr _ -> "expr"
              | ExprCtx _ -> "Expr"
              | Decl _ -> "decl"
              | DoNothing -> "mark"
          System.Console.WriteLine ("{3:000.000}s {0} {1} {2}", kind, (if t.Enabled then "          " else "(disabled)"), t.Name, 
                                    double (lookupWithDefault times 0L t.Name) / 10000000.0)
                                    
