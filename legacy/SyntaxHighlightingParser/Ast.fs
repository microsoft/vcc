namespace SyntaxHighlighting

open Microsoft.FSharp.Text.Lexing

module Ast =

  type Span = 
    | Spec of int * int
    | Keyword of int * int

  let private toKeywordSet =  
    List.map (fun (str:string) -> str.ToCharArray()) >> Set.ofList

  let private keywords =
    toKeywordSet [
                  "atomic" ; 
                  "assume" ; 
                  "assert" ; 
                  "axiom" ; 
                  "decreases" ; 
                  "ensures" ; 
                  "group" ;
                  "invariant" ;
                  "logic" ;
                  "out" ;
                  "requires" ;
                  "reads" ;
                  "unwrap" ;
                  "unwrapping" ;
                  "unchecked" ;
                  "wrap" ;
                  "writes" ;
                  "maintains" ;
                  "always" ;
                  "updates" ;
                  "out_param" ;
                  "returns" ;
                  "level";
                  "recursive_with";
                  "read_only" ;
                  "by_claim" ;
                  "retype" ;
    ]

  let private guardedKeywords =
    toKeywordSet [
                  "\\bool";
                  "\\result";
                  "\\lambda";
                  "\\forall" ;
                  "\\exists" ;
                  "\\union" ;
                  "\\inter" ;
                  "\\this" ;
                  "\\diff" ;
                  "\\old" ;
                  "\\in0" ;
                  "\\is" ;
                  "\\in" ;
                  "\\objset" ;
                  "\\state" ;
                  "\\type" ;
                  "\\true" ;
                  "\\false" ;
                  "\\integer" ;
                  "\\object" ;
                  "\\claim" ;
                  "\\size_t" ;
                  "\\thread" ;
                  "\\at" ;
                  "\\now" ;
                  "\\claim_count" ;
                  "\\closed" ;
                  "\\owns" ;
                  "\\owner" ;
                  "\\valid" ;
                  "\\by_claim" ;
                  "\\when_claimed"; 
                  "\\on_unwrap" ;
                  "\\mine";
                  "\\wrapped" ;
                  "\\fresh" ;
                  "\\nested" ;
                  "\\non_primitive_ptr" ;
                  "\\extent" ;
                  "\\full_extent" ;
                  "\\extent_mutable" ;
                  "\\extent_zero" ;
                  "\\extent_fresh" ;
                  "\\universe" ;
                  "\\disjoint" ;
                  "\\subset" ;
                  "\\thread_local" ;
                  "\\thread_local_array" ;
                  "\\mutable" ;
                  "\\mutable_array" ;
                  "\\in_array";
                  "\\array_range" ;
                  "\\array_members" ;
                  "\\is_array" ;
                  "\\span" ;
                  "\\domain" ;
                  "\\vdomain" ;
                  "\\domain_updated_at" ;
                  "\\typeof" ;
                  "\\claims"; 
                  "\\claims_object" ;
                  "\\claims_claim" ;
                  "\\claimable" ;
                  "\\make_claim" ;
                  "\\upgrade_claim" ;
                  "\\active_claim" ;
                  "\\account_claim" ;
                  "\\always_by_claim" ;
                  "\\inv" ;
                  "\\inv2" ;
                  "\\approves"; 
                  "\\embedding" ;
                  "\\gemb" ;
                  "\\simple_embedding" ;
                  "\\ghost" ;
                  "\\program_entry_point" ;
                  "\\alloc" ;
                  "\\alloc_array" ;
                  "\\depends" ;
                  "\\not_shared" ;
                  "\\malloc_root" ;
                  "\\object_root" ;
                  "\\union_active" ;
                  "\\addr" ;
                  "\\addr_eq" ;
                  "\\arrays_disjoint" ;
                  "\\full_context" ;
                  "\\wrapped_with_deep_domain" ;
                  "\\composite_extent" ;
                  "\\domain_root" ;
                  "\\size" ;
                  "\\shallow_eq" ;
                  "\\deep_eq" ;
                  "\\wrap" ;
                  "\\unwrap" ;
                  "\\destroy_claim" ;
                  "\\reads_havoc" ;
                  "\\havoc_others" ;
                  "\\set_closed_owns" ;
                  "\\union_reinterpret" ;
                  "\\deep_unwrap" ;
                  "\\bump_volatile_version" ;
                  "\\begin_update" ;
                  "\\match_long" ;
                  "\\match_ulong" ;
                  "\\writable" ;
                  "\\inv2s" ;
                  "\\may_diverge" ;
                  "\\in_range_phys_ptr";
                  "\\in_range_spec_ptr";
                  "\\index_within";
                  "\\wrapped0";
                  "\\unchanged";
                  "\\same";
                  "\\recursive_with";
                  "\\natural" ;
    ]

  let isGuardedKeyword chars = Set.contains chars guardedKeywords

  let isKeyword chars = Set.contains chars keywords
