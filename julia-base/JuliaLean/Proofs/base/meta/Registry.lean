import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.meta.LegacyProofs
import JuliaLean.Proofs.base.meta.RowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesMeta : List Entry := [
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
] ++ metaRowEntries

end JuliaLean.ExprReflect
