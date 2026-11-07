import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.expr.LegacyProofs
import JuliaLean.Proofs.base.expr.Refutations
import JuliaLean.Proofs.base.expr.RowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesExpr : List Entry := [
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
] ++ exprRowEntries

end JuliaLean.ExprReflect
