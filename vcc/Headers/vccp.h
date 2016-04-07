
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
#ifndef _VCCP_H
#define _VCCP_H

/*** 
 *** Types
 ***/

#define _concat_identifiers2(a, b) a ## b
#define _concat_identifiers(a, b) _concat_identifiers2(a, b)

/***
 *** Types
 ***/

#define SPEC_TYPE(name) type _concat_identifiers(\, name)

_(typedef void *\object)
_(typedef __int64 \integer)
_(typedef unsigned __int64 \natural)
_(typedef struct \claim_struct { } ^\claim)
_(typedef unsigned __int64 \size_t)
_(typedef _Bool \bool)

_(type \objset)
_(type \state)
_(type \type)
_(type \thread_id)

_(typedef \thread_id ^\thread)

_(const \bool \true = 1)
_(const \bool \false = 0)

// '__declspec's
_(const char * const \declspec_atomic_inline)
_(const char * const \declspec_backing_member)
_(const char * const \declspec_claimable)
_(const char * const \declspec_dynamic_owns)
_(const char * const \declspec_frameaxiom)
_(const char * const \declspec_no_admissibility)
_(const char * const \declspec_volatile_owns)
_(const char * const \declspec_pure = "is_pure")
_(const char * const \declspec_def = "definition")
_(const char * const \declspec_abstract)
_(const char * const \declspec_as_array)
_(const char * const \declspec_admissibility = "is_admissibilitycheck")
_(const char * const \declspec_no_reads_check)
_(const char * const \declspec_record)
_(const char * const \declspec_yarra)
_(const char * const \declspec_assume_correct = "skip_verification")
_(const char * const \declspec_isolate_proof)
_(const char * const \declspec_skip_smoke)
_(const char * const \declspec__boogie0)
_(const char * const \declspec__boogie1)
_(const char * const \declspec__boogie2)
_(const char * const \declspec_primitive)
// _(inline) is also supported, but becaue 'inline' is a keyword, we special-case _(inline) in the parser

#define vcc_attr(k, v) __declspec(System.Diagnostics.Contracts.CodeContract.StringVccAttr, k, v)
#define vcc_nospeccast(_TYPE_, _EXPR_) (_EXPR_)
#define vcc_generic_instance(_F_, ...) _F_ __VA_ARGS__

#ifdef VCC_NO_SPLITS
#define vcc_force_splits(n)
#define vcc_keep_going(n)
#else
#define vcc_force_splits(n) \
  __declspec(System.Diagnostics.Contracts.CodeContract.IntBoogieAttr, "vcs_max_splits", n) \
  __declspec(System.Diagnostics.Contracts.CodeContract.IntBoogieAttr, "vcs_max_cost", 1)
#define vcc_keep_going(n) \
  __declspec(System.Diagnostics.Contracts.CodeContract.IntBoogieAttr, "vcs_max_keep_going_splits", n)
#endif


_(\bool \mine(\object, ...))
_(\bool \wrapped(\object))
_(\bool \fresh(\object))
_(\bool \nested(\object))
_(\bool \non_primitive_ptr(\object))
_(\objset \extent(\object))
_(\objset \full_extent(\object))
_(\bool \extent_mutable(\object))
_(\bool \extent_zero(\object))
_(\bool \extent_fresh(\object))
_(\objset \universe())
_(\bool \disjoint(\objset, \objset))
_(\bool \subset(\objset, \objset))
_(\bool \thread_local(\object))
_(\bool \thread_local_array(\object, \size_t))
_(\bool \mutable(\object))
_(\bool \mutable_array(\object, \size_t))
_(\bool \in_array(\object, \object, \size_t))
_(\objset \array_range(\object, \size_t))
_(\objset \array_members(\object, \size_t))
_(\bool \is_array(\object, \size_t))
_(\objset \span(\object))
_(\objset \domain(\object))
_(\objset \vdomain(\object))
_(\bool \domain_updated_at(\object p, \objset wr))
_(\type \typeof(\object))
_(\bool \claims(\claim, \bool))
_(\bool \claims_object(\claim, \object))
_(\bool \claims_claim(\claim, \claim))
_(\bool \claimable(\object))
_(\claim \make_claim(\objset, \bool))
_(\claim \upgrade_claim(\objset, \bool))
_(\bool \active_claim(\claim))
_(\bool \account_claim(\claim, \object))
_(\bool \always_by_claim(\claim, \object))
_(\bool \inv(\object))
_(\bool \inv2(\object))
_(\bool _(_boogie0) \inv2s(\state, \state, \object))
_(template<typename T> \bool \approves(\object approver, T expr))
_(\object \embedding(\object))
_(\object \gemb(\object))
_(\object \simple_embedding(\object))
_(\bool \ghost(\object))
_(\bool \program_entry_point())
_(template<typename T> T ^\alloc())
_(template<typename T> T ^\alloc_array(\size_t))
_(\bool \depends(\object, \object))
_(\bool \not_shared(\object))
_(\bool \malloc_root(\object))
_(\bool \object_root(\object))
_(\bool \union_active(\object))
_(\object _(_boogie1) \active_member(\object))
_(\integer \addr(\object))
_(\bool \addr_eq(\object, \object))
_(\bool _(_boogie0) \arrays_disjoint(\object, \size_t, \object, \size_t))
_(\bool _(_boogie0) \full_context())
_(\bool _(_boogie1) \wrapped_with_deep_domain(\object))
_(\objset \composite_extent(\object))
_(\object _(_boogie1) \domain_root(\object))
_(\integer _(_boogie0) \index_within(\object, \object))
_(\integer _(_boogie0) \sizeof_object(\object))
_(\bool _(_boogie0) \in_range_phys_ptr(\object))
_(\bool _(_boogie0) \in_range_spec_ptr(\object))
_(\bool _(_boogie0) \may_diverge())
_(\bool \normal_exit())
_(\bool \writable(\object))
_(\bool \assume(\bool))

_(template<typename T> \integer \size(T dt))

_(template<typename T> \bool \shallow_eq(T s, T t))
_(template<typename T> \bool \deep_eq(T s, T t))

_(template<typename T> T \at(\state, T expr))
_(\state \now())
_(logic template<typename T> T \by_claim(\claim c, T expr) = \at(\by_claim_wrapper(c), expr))
_(logic template<typename T> T \when_claimed(T expr) = \at(\when_claimed_marker(), expr))
_(logic \bool \on_unwrap(\object o, \bool expr) = \old(o->\closed) && !o->\closed ==> expr)
_(logic \objset \everything() = \universe())

// built-in fields

_(struct \TypeState {
  _(ghost \integer \claim_count)
  _(ghost \bool \closed)
  _(ghost \objset \owns)
  _(ghost \object \owner)
  _(ghost \bool \valid)
})

// Statement-like functions

_(void \wrap(\object o, ...) _(writes o, o->\owns))
_(void \unwrap(\object o, ...) _(writes o))
_(void \destroy_claim(\claim, \objset))
_(void \reads_havoc())
_(void \havoc_others(\object p))
_(void \set_closed_owns(\object owner, \objset owns) 
  _(writes \new_ownees(owner, owns))
  _(requires \atomic_object(0)))
_(void \union_reinterpret(\object fld) _(writes \extent(\simple_embedding(fld))))
_(void \deep_unwrap(\object o) _(writes o))
_(void \bump_volatile_version(\object o) _(writes o))
_(void \begin_update())
_(void \blobify(\object))
_(void \unblobify_into(\object))
_(void \join_blobs(\object a, \object b)
  _(writes a, b))
_(void \split_blob(\object a, \integer offset)
  _(writes a))

// matching helper functions

_(pure \bool \match_long(__int64 ) _(ensures \result == \true))
_(pure \bool \match_ulong(unsigned __int64) _(ensures \result == \true))

// global variables

_(ghost extern const \thread \me)

// Function that can be used in cast-like syntax: 
//     _(foobar x, y)(z) -> \castlike_va_foobar(z, \argument_tuple(x, y))
//     _(foobaz x, y)(z) -> \castlike_foobaz(z, x, y)
_(\integer \argument_tuple(\object, ...)) 
_(template<typename T> T \castlike_va_atomic_read(T op, \integer))
_(template<typename T> T \castlike_known(T v, \bool expected))
_(template<typename T> T \castlike_retype(T))
_(template<typename T> T \castlike_by_claim(T v, \claim c))
_(template<typename T> T \castlike_precise(T v))

_(\object \castlike_read_only(\object ptr))
_(\object \castlike_blob(\object ptr, \integer sz))
_(\object \castlike_blob_of(\object ptr))
_(template<typename T> T* \castlike_unblobify(T*))
//_(void* \castlike_blobify(void*))

_(template<typename T> T* \castlike_root_array(T*, \integer))
_(template<typename T> T* \castlike_root_index(T*, \integer))

// the VccAtomicOp AST class uses this
_(void _vcc_atomic_op(\object, ...))

// This one is built-in
// _(template<typename T> T \castlike_unchecked(T v))

// 'Built-in' spec macros and logic definitions

_(\bool \macro_maintains(\bool cond)
  _(requires cond)
  _(ensures cond))

_(\bool \macro_always(\claim c, \bool cond)
  _(requires \wrapped(c) && \claims(c, cond))
  _(requires \assume(\active_claim(c)))
  _(ensures \wrapped(c))
  _(ensures \assume(\active_claim(c))))

_(\bool \macro_updates(\object o)
  _(requires \wrapped(o))
  _(ensures \wrapped(o))
  _(writes o))

_(\bool \macro_out_param(\object p)
  _(writes p)
  _(requires \mutable(p))
  _(ensures \mutable(p)))

_(template<typename T> \bool \result_macro_returns(T res, T expr)
  _(ensures res == expr))

_(\bool \macro_level(\integer l)
  _(requires \decreases_level(l)))

_(\bool \recursive_with(void *))
_(\bool \macro_recursive_with(void *p)
  _(requires \recursive_with(p)))

_(logic \bool \wrapped0(\object o) = \wrapped(o) && o->\claim_count == 0)
_(logic template<typename T> \bool \unchanged(T expr) = \old(expr) == expr)
_(logic template<typename T> \bool \same(T expr) = \old(expr) == expr)

// Internal functions - not meant to be called directly, unless you know what you are doing

_(void \free(\object p) _(writes p, \extent(p)))
_(\bool \set_in(\object, \objset))
_(\bool \set_in0(\object, \objset))
_(\objset \set_union(\objset, \objset))
_(\objset \set_intersection(\objset, \objset))
_(\objset \set_difference(\objset, \objset))
_(\objset \set_add_element(\objset, \object))
_(\objset \set_remove_element(\objset, \object))
_(\bool \atomic_object(unsigned __int64))
_(void \set_closed_owner(\object obj, \object owner)  _(writes obj) _(requires \atomic_object(1)))
_(void \giveup_closed_owner(\object obj, \object owner)  _(requires \atomic_object(1)))
_(void \set_owns(\object obj, \objset owns)  _(writes \span(obj)))
_(\state \by_claim_wrapper(\claim))
_(\state \when_claimed_marker())
_(\object \heap_alloc(\type))
_(\bool \start_here())
_(\objset \new_ownees(\object, \objset))
_(\bool \decreases_level(\integer))

_(template<typename T, typename S> T \labeled_expression(char *label_name, S label_argument, T expr))

#ifdef VCC_DEFINE_ASSERT
#ifdef assert
#undef assert
#endif
_(pure)
void assert(\bool assertedCondition)
  _(requires assertedCondition);
#endif

// Information Flow

#define classifier_t(_VARNAME)	\bool _VARNAME[obj_t]

_(\bool \test_classifier(classifier_t(cl), \bool test))
_(template<typename T> void \downgrade_to(T v, T expr))

_(type \label)

_(pure \label \seclabel_bot())
_(pure \label \seclabel_top())
_(\label \current_context())
_(template<typename T> \label \label_of(T e))
_(logic template<typename T> \label \meta_of(T e) =	\label_of(\label_of(e)))
_(\bool \lblset_leq(\label, \label))
_(logic template<typename T> \bool \is_lower(T e, \label l) = \lblset_leq(\label_of(e), l))
_(logic template<typename T> \bool \is_low(T e) = \is_lower(e, \seclabel_bot()))

_(type \club)

_(\club \new_club(\label))
_(void \add_member(\object, \club))
_(\bool \is_member(\object, \club))

// Misc
char *get___FUNCTION__();
void __annotation(...);
void __debugbreak();

#endif // _VCCP_H
