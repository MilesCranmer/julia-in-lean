import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ExprReflect.Model
import JuliaLean.ExprReflect.Props
import JuliaLean.ExprReflect.Proofs
import JuliaLean.ExprReflect.Refutations
import JuliaLean.ExprReflect.Coverage
import JuliaLean.ExprReflect.EnumsRowEntries
import JuliaLean.ExprReflect.CartesianRowEntries
import JuliaLean.ExprReflect.MetaRowEntries
import JuliaLean.ExprReflect.ReflectionRowEntries
import JuliaLean.ExprReflect.ExprRowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "exprreflect-copy-equal", juliaFile := "base/expr.jl"
    juliaFns := ["copy(::Expr)", "copy_exprargs", "copy_exprs"]
    statement := "copy(::Expr) preserves the complete structural value of every expression in the modelled fragment."
    source := "base/expr.jl:45,67-81; copy invariant", status := .proven
    prop := ``CopyEqual, thm := some ``copyEqual_proven },
  { id := "exprreflect-copy-quotenode-alias", juliaFile := "base/expr.jl"
    juliaFns := ["copy(::Expr)", "copy_exprargs", "copy_exprs"]
    statement := "copy(::Expr) shares no mutable Expr identity with the original when all fresh identities are new."
    source := "requested tree-independence invariant; base/expr.jl:45,67-81", status := .refuted
    prop := ``CopyIndependent, thm := some ``copyIndependent_refuted
    issue := "none found (queries: copy Expr QuoteNode alias OR shared; QuoteNode copy)"
    notes := "An Expr stored as QuoteNode.value is returned unchanged; mutating it through the copy changes the original. The generic copy doc promises a shallow copy, so this is P2 and may be intended." },
  { id := "exprreflect-isexpr", juliaFile := "base/expr.jl"
    juliaFns := ["isexpr", "Meta.isexpr"]
    statement := "isexpr on an Expr is exactly head membership plus the optional argument-count test."
    source := "base/expr.jl:3-4,42-43; base/meta.jl:160-189", status := .proven
    prop := ``IsExprContract, thm := some ``isExprContract_proven },
  { id := "exprreflect-quot", juliaFile := "base/meta.jl"
    juliaFns := ["Meta.quot"]
    statement := "Meta.quot(ex) constructs Expr(:quote, ex) for every expression value."
    source := "base/meta.jl:136-158", status := .proven
    prop := ``QuotContract, thm := some ``quotContract_proven },
  { id := "exprreflect-show-sexpr", juliaFile := "base/meta.jl"
    juliaFns := ["Meta.show_sexpr"]
    statement := "show_sexpr emits the expression head followed by recursively converted arguments in their original order."
    source := "base/meta.jl:220-256", status := .proven
    prop := ``ShowSexprContract, thm := some ``showSexprContract_proven },
  { id := "exprreflect-inline-block", juliaFile := "base/expr.jl"
    juliaFns := ["@inline", "annotate_meta_def_or_block"]
    statement := "@inline on a non-definition brackets the escaped value with inline(true) and inline(false) metadata and returns the value."
    source := "base/expr.jl:307-390,1227-1239", status := .proven
    prop := ``InlineContract, thm := some ``inlineContract_proven },
  { id := "exprreflect-generated-annotation", juliaFile := "base/expr.jl"
    juliaFns := ["@generated"]
    statement := "@generated wraps every accepted function body in the generated/generated_only conditional documented by the macro."
    source := "base/expr.jl:1326-1374", status := .proven
    prop := ``GeneratedContract, thm := some ``generatedContract_proven },
  { id := "exprreflect-fieldnames-count", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldnames", "fieldcount"]
    statement := "Whenever fieldnames and fieldcount return normally for a layout, the number of names equals the field count."
    source := "base/runtime_internals.jl:413-442,1456-1487", status := .proven
    prop := ``FieldNamesCount, thm := some ``fieldNamesCount_proven },
  { id := "exprreflect-fieldoffset-bounds", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldoffset"]
    statement := "Every successful one-based fieldoffset lookup uses an index within fieldnames(type)."
    source := "base/runtime_internals.jl:1228-1275; field-layout invariant", status := .proven
    prop := ``FieldOffsetInBounds, thm := some ``fieldOffsetInBounds_proven },
  { id := "exprreflect-methods-filter", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["methods", "matches_to_methods"]
    statement := "Every method returned by methods matches the requested signature and, when supplied, the module filter."
    source := "base/runtime_internals.jl:1706-1758", status := .proven
    prop := ``MethodFiltering, thm := some ``methodFiltering_proven },
  { id := "exprreflect-which-hasmethod", juliaFile := "base/reflection.jl"
    juliaFns := ["which", "hasmethod"]
    statement := "If which finds a matching method in the ordered method model, hasmethod is true for the same query."
    source := "base/reflection.jl:968-1013,1077-1139", status := .proven
    prop := ``WhichHasMethod, thm := some ``whichHasMethod_proven },
  { id := "exprreflect-nameof", juliaFile := "base/reflection.jl"
    juliaFns := ["nameof(::Function)"]
    statement := "nameof returns the function type's recorded singleton name."
    source := "base/reflection.jl:1029-1043", status := .proven
    prop := ``NameofContract, thm := some ``nameofContract_proven },
  { id := "exprreflect-enum-assignment", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "instances"]
    statement := "For every in-range Int8 starting value below typemax, an explicit member followed by an implicit member receives values x and x+1 in declaration order."
    source := "base/Enums.jl:95-135,144-217,235-237", status := .proven
    prop := ``EnumAssignsDocumentedValues, thm := some ``enumAssignsDocumentedValues_proven },
  { id := "exprreflect-enum-duplicate-values", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every pair of distinct member names assigned the same in-range Int8 value."
    source := "base/Enums.jl:199-200", status := .proven
    prop := ``EnumRejectsDuplicateValues, thm := some ``enumRejectsDuplicateValues_proven },
  { id := "exprreflect-enum-duplicate-names", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every repeated member name even when its two assigned Int8 values differ."
    source := "base/Enums.jl:204-207", status := .proven
    prop := ``EnumRejectsDuplicateNames, thm := some ``enumRejectsDuplicateNames_proven },
  { id := "exprreflect-enum-out-of-range", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every explicit value outside the chosen Int8 base type's range."
    source := "base/Enums.jl:185-190", status := .proven
    prop := ``EnumRejectsOutOfRange, thm := some ``enumRejectsOutOfRange_proven },
  { id := "exprreflect-enum-overflow", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "After an Int8 member assigned typemax, @enum rejects every following implicit member instead of wrapping to typemin."
    source := "base/Enums.jl:178-181,216", status := .proven
    prop := ``EnumRejectsOverflow, thm := some ``enumRejectsOverflow_proven },
  { id := "exprreflect-enum-instances-order", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "instances"]
    statement := "For every three distinct in-range explicit Int8 values, instances lists each value once in declaration order."
    source := "base/Enums.jl:199-207,235-237", status := .proven
    prop := ``EnumInstancesOrder, thm := some ``enumInstancesOrder_proven },
  { id := "exprreflect-enum-typemin-order", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "typemin(::Type{<:Enum})", "typemax(::Type{<:Enum})"]
    statement := "For every successfully constructed enum, typemin and typemax are the minimum and maximum represented instance values."
    source := "base/int.jl:827-831; base/Enums.jl:208-227", status := .refuted
    prop := ``EnumExtremaCorrect, thm := some ``enumExtremaCorrect_refuted
    issue := "none found (queries: enum typemin order OR out of order OR minimum)"
    notes := "@enum E::Int8 high=5 low=-2 top=9 makes Int(typemin(E)) == 5 instead of -2 because lo is never updated after the first member." },
  { id := "exprreflect-nref", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nref"]
    statement := "For every natural dimension count N, @nref produces A[i_1,...,i_N] in increasing dimension order."
    source := "base/cartesian.jl:73-88", status := .proven
    prop := ``NrefExact, thm := some ``nrefExact_proven },
  { id := "exprreflect-ntuple", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@ntuple"]
    statement := "For every natural dimension count N, @ntuple produces (i_1,...,i_N) in increasing dimension order."
    source := "base/cartesian.jl:222-231", status := .proven
    prop := ``NtupleExact, thm := some ``ntupleExact_proven },
  { id := "exprreflect-nloops-atomic-body", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nloops", "Base.Cartesian._nloops"]
    statement := "For every natural dimension count and every body expression, @nloops expands to the documented normalized loop nest."
    source := "base/cartesian.jl:9-38", status := .refuted
    prop := ``CartesianLoopsTotal, thm := some ``cartesianLoopsTotal_refuted
    issue := "none found (queries: Cartesian @nloops body MethodError)"
    notes := "An atomic body such as the symbol body dispatches to no _nloops method because args is restricted to Expr..., although symbols and literals are valid macro body expressions." },
  { id := "exprreflect-nloops-compound", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nloops", "Base.Cartesian._nloops"]
    statement := "For every natural dimension count and compound body, @nloops expands to the documented normalized loop nest with dimension N outermost."
    source := "base/cartesian.jl:25-33,38-70", status := .proven
    prop := ``CartesianLoopsCompoundExact, thm := some ``cartesianLoopsCompoundExact_proven },

  -- Whole-Base source-body coverage families.
  { id := "exprreflect-expr-symbol-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["gensym()", "gensym(::String)", "gensym(::String...)", "gensym(::Symbol)", "@gensym"]
    statement := "The gensym wrappers preserve optional tags, map varargs in order, and @gensym emits one same-named assignment per input."
    source := "base/expr.jl:9-38", status := .proven
    prop := ``ExprSymbolBodies, thm := some ``exprSymbolBodies_proven },
  { id := "exprreflect-expr-ir-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["copy(::Expr)", "copy(::PhiNode)", "copy(::PhiCNode)", "copy_exprs", "copy_exprargs", "exprarray", "copy(::CodeInfo)", "isequal_exprarg", "isequal_exprargs", "==(::Expr,::Expr)", "==(::QuoteNode,::QuoteNode)", "==(::PhiNode,::PhiNode)", "==(::PhiCNode,::PhiCNode)", "==(::CodeInfo,::CodeInfo)", "==(::DebugInfo,::DebugInfo)"]
    statement := "The IR copy family preserves immutable fields, refreshes exactly the mutable subobjects selected by the source branches, and structural equality is reflexive."
    source := "base/expr.jl:40-178", status := .proven
    prop := ``ExprIRBodies, thm := some ``exprIRBodies_proven },
  { id := "exprreflect-expr-macroexpand-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand", "macroexpand!", "@macroexpand", "@macroexpand1"]
    statement := "Every macroexpand wrapper passes the documented recursive, in-place, and legacy-scope flags to jl_macroexpand."
    source := "base/expr.jl:181-296", status := .proven
    prop := ``ExprMacroexpandBodies, thm := some ``exprMacroexpandBodies_proven },
  { id := "exprreflect-expr-effect-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["@inline", "@noinline", "@constprop", "constprop_setting", "@assume_effects", "compute_assumed_settings", "EffectsOverride", "compute_assumed_setting", "encode_effects_override", "decode_effects_override", "form_purity_expr", "@nospecializeinfer", "@propagate_inbounds", "@polly"]
    statement := "Annotation wrappers select the source tags and shapes, effect settings update the stated fields, and the eleven effect bits preserve field order."
    source := "base/expr.jl:307-1163", status := .proven
    prop := ``ExprEffectBodies, thm := some ``exprEffectBodies_proven },
  { id := "exprreflect-expr-meta-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["unwrap_macrocalls", "pushmeta!", "popmeta!", "peekmeta", "_getmeta", "findmetaarg", "annotate_meta_def_or_block", "is_short_function_def", "is_function_def", "findmeta", "findmeta_block", "remove_linenums!", "replace_linenums!", "@generated"]
    statement := "Metadata helpers traverse macro wrappers, locate or delete tags, classify function forms, update line nodes, and construct both generated annotations."
    source := "base/expr.jl:1165-1375", status := .proven
    prop := ``ExprMetaBodies, thm := some ``exprMetaBodies_proven },
  { id := "exprreflect-expr-atomic-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["@atomic", "make_atomic", "@atomicswap", "make_atomicswap", "@atomicreplace", "make_atomicreplace", "@atomiconce", "make_atomiconce"]
    statement := "Atomic macro forms map field and indexed fetch, store, modify, swap, replace, and once operations to their exact Base primitives and order counts."
    source := "base/expr.jl:1378-1837", status := .proven
    prop := ``ExprAtomicBodies, thm := some ``exprAtomicBodies_proven },
  { id := "exprreflect-expr-generated-bodies", juliaFile := "base/expr.jl"
    juliaFns := ["is_meta_expr_head", "is_meta_expr", "isa_ast_node", "is_self_quoting", "quoted", "generated_body_to_codeinfo", "(::Core.GeneratedFunctionStub)(...)"]
    statement := "AST classification, safe IR quoting, generated-body lowering errors, mutable CodeInfo fields, binding edges, and generated-stub wrapper construction follow the source cases."
    source := "base/expr.jl:1839-1933", status := .proven
    prop := ``ExprGeneratedBodies, thm := some ``exprGeneratedBodies_proven },

  { id := "exprreflect-meta-identifier-bodies", juliaFile := "base/meta.jl"
    juliaFns := ["is_id_start_char", "is_id_char", "isidentifier", "is_op_suffix_char", "_isoperator", "isoperator", "isunaryoperator", "is_unary_and_binary_operator", "is_syntactic_operator", "isbinaryoperator", "ispostfixoperator", "is_valid_identifier"]
    statement := "Identifier and operator predicates apply their runtime character oracles and Julia's empty, reserved-word, quote, suffix, unary, binary, and syntactic exclusions in source order."
    source := "base/meta.jl:23-134", status := .proven
    prop := ``MetaIdentifierBodies, thm := some ``metaIdentifierBodies_proven },
  { id := "exprreflect-meta-ast-bodies", juliaFile := "base/meta.jl"
    juliaFns := ["quot", "replace_sourceloc!", "show_sexpr", "@dump", "lower", "@lower"]
    statement := "The AST convenience wrappers construct quote, source-location, S-expression, dump, and lowering calls with the source argument order."
    source := "base/meta.jl:136-289", status := .proven
    prop := ``MetaAstBodies, thm := some ``metaAstBodies_proven },
  { id := "exprreflect-meta-parser-bodies", juliaFile := "base/meta.jl"
    juliaFns := ["ParseError", "parser_for_module", "_parse_string", "_is_parse_error", "parse", "parseatom", "parseall"]
    statement := "Parser wrappers enforce one-based positions, translate parser offsets, choose statement, atom, or all modes, implement raise, and reject trailing tokens."
    source := "base/meta.jl:292-434", status := .proven
    prop := ``MetaParserBodies, thm := some ``metaParserBodies_proven },
  { id := "exprreflect-meta-inline-bodies", juliaFile := "base/meta.jl"
    juliaFns := ["partially_inline!", "_partially_inline!", "_instantiate_type_in_env"]
    statement := "Partial inlining maps assigned statements and mirrors the ordered SSA, goto, slot, node, static-parameter, foreign-call, boundscheck, isdefined, and recursive Expr cases."
    source := "base/meta.jl:436-623", status := .proven
    prop := ``MetaInlineBodies, thm := some ``metaInlineBodies_proven },
  { id := "exprreflect-meta-hygiene-bodies", juliaFile := "base/meta.jl"
    juliaFns := ["unblock", "unescape", "reescape", "uncurly"]
    statement := "Hygiene helpers remove redundant line-only blocks and escape frames, restore the original escape-frame order, and peel curly type applications."
    source := "base/meta.jl:625-682", status := .proven
    prop := ``MetaHygieneBodies, thm := some ``metaHygieneBodies_proven },

  { id := "exprreflect-reflection-lowered-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["code_lowered", "method_instances", "method_instance"]
    statement := "Lowered-code and method-instance wrappers normalize signatures, reject generator-world queries, select staged versus fallback IR, and preserve match order."
    source := "base/reflection.jl:3-88", status := .proven
    prop := ``ReflectionLoweredBodies, thm := some ``reflectionLoweredBodies_proven },
  { id := "exprreflect-reflection-param-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["CodegenParams", "EmissionParams"]
    statement := "CodegenParams and EmissionParams convert every Boolean keyword to its corresponding Cint field in declaration order."
    source := "base/reflection.jl:92-227", status := .proven
    prop := ``ReflectionParamBodies, thm := some ``reflectionParamBodies_proven },
  { id := "exprreflect-reflection-compiler-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["default_tt", "raise_match_failure", "invoke_in_typeinf_world", "invoke_default_compiler", "invoke_interp_compiler", "invoke_mt_compiler"]
    statement := "Compiler dispatch selects type-inference world, configured reflection module, interpreter module, or method-table module using the source precedence."
    source := "base/reflection.jl:304-365", status := .proven
    prop := ``ReflectionCompilerBodies, thm := some ``reflectionCompilerBodies_proven },
  { id := "exprreflect-reflection-query-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["code_typed", "code_typed_by_type", "get_oc_code_rt", "code_typed_opaque_closure", "code_ircode", "code_ircode_by_type", "_builtin_return_type", "_builtin_effects", "_builtin_exception_type", "check_generated_context", "return_types", "infer_return_type", "infer_exception_types", "infer_exception_type", "infer_effects", "print_statement_costs"]
    statement := "Reflection queries preserve method-match order, emit Method=>Any on failed inference, implement opaque and builtin branches, merge collective results, and reject generated contexts."
    source := "base/reflection.jl:229-966", status := .proven
    prop := ``ReflectionQueryBodies, thm := some ``reflectionQueryBodies_proven },
  { id := "exprreflect-reflection-api-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["_which", "which", "nameof", "parentmodule", "hasmethod", "Core.kwcall(::typeof(hasmethod),...)", "bodyfunction"]
    statement := "Public reflection wrappers implement unique method lookup, function naming, first-method modules, positional and keyword method tests, and keyword-body extraction branches."
    source := "base/reflection.jl:968-1193", status := .proven
    prop := ``ReflectionApiBodies, thm := some ``reflectionApiBodies_proven },
  { id := "exprreflect-reflection-ambiguity-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["isambiguous", "inner", "involves_both"]
    statement := "Ambiguity testing rejects identical methods and bottom intersections before bottom-parameter, generator-world, runtime-match, involvement, and reverse-intersection checks."
    source := "base/reflection.jl:1195-1297", status := .proven
    prop := ``ReflectionAmbiguityBodies, thm := some ``reflectionAmbiguityBodies_proven },
  { id := "exprreflect-reflection-invoke-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["@invoke", "getglobalref", "invokelatest_gr", "@invokelatest", "destructure_callex", "flatten"]
    statement := "Invoke macros destructure call, property, index, and assignment forms, preserve keyword order, choose annotations versus Core.Typeof, and select global-reference latest-world calls."
    source := "base/reflection.jl:1299-1497", status := .proven
    prop := ``ReflectionInvokeBodies, thm := some ``reflectionInvokeBodies_proven },
  { id := "exprreflect-reflection-cache-bodies", juliaFile := "base/reflection.jl"
    juliaFns := ["drop_all_caches"]
    statement := "drop_all_caches invokes the runtime cache drop, resets the loading world to typemax, and activates compiler coverage."
    source := "base/reflection.jl:1499-1514", status := .proven
    prop := ``ReflectionCacheBodies, thm := some ``reflectionCacheBodies_proven },

  { id := "exprreflect-enum-runtime-bodies", juliaFile := "base/Enums.jl"
    juliaFns := ["basetype", "convert enum to integer", "cconvert", "write", "read", "_enum_hash", "hash", "isless", "Symbol", "_symbol", "print", "show", "membershiptest", "broadcastable", "enum_argument_error"]
    statement := "Enum runtime methods bitcast through the base type, delegate IO and hashing, order by integer value, map values to names or invalid fallbacks, choose membership strategy, and broadcast as scalars."
    source := "base/Enums.jl:10-93", status := .proven
    prop := ``EnumRuntimeBodies, thm := some ``enumRuntimeBodies_proven },
  { id := "exprreflect-enum-macro-bodies", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "generated enum constructor", "Enums.namemap", "typemin", "typemax", "generated _enum_hash", "instances"]
    statement := "@enum validates base types and members in source order, assigns and increments base values, rejects duplicate or invalid declarations, and generates constructor, name, extrema, hash, instances, and constants."
    source := "base/Enums.jl:95-252", status := .proven
    prop := ``EnumMacroBodies, thm := some ``enumMacroBodies_proven },

  { id := "exprreflect-cartesian-macro-bodies", juliaFile := "base/cartesian.jl"
    juliaFns := ["@nloops", "_nloops", "@nref", "@ncall", "@ncallkw", "@nexprs", "@nextract", "@nall", "@nany", "@ntuple", "@nif"]
    statement := "Cartesian macros generate exactly one ordered dimension contribution per requested dimension, with the documented loop nesting, calls, tuple, extraction, Boolean, and conditional shapes."
    source := "base/cartesian.jl:9-259", status := .proven
    prop := ``CartesianMacroBodies, thm := some ``cartesianMacroBodies_proven },
  { id := "exprreflect-cartesian-substitution-bodies", juliaFile := "base/cartesian.jl"
    juliaFns := ["inlineanonymous", "LReplace", "lreplace", "lreplace!", "lreplace_string!", "poplinenum", "exprresolve_arith", "exprresolve_conditional", "exprresolve"]
    statement := "Cartesian substitution replaces free dimension variables and indexed symbol suffixes across quote/escape boundaries, removes singleton line blocks, and resolves supported arithmetic and conditionals."
    source := "base/cartesian.jl:261-473", status := .proven
    prop := ``CartesianSubstitutionBodies, thm := some ``cartesianSubstitutionBodies_proven }
] ++ enumRowEntries ++ cartesianRowEntries ++ metaRowEntries ++ reflectionRowEntries ++ exprRowEntries

end JuliaLean.ExprReflect
