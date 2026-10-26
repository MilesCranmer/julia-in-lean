import JuliaLean.ExprReflect.MetaRows
import JuliaLean.Registry.Types

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def metaRowEntries : List Entry := [
  { id := "exprreflect-meta-row-25", juliaFile := "base/meta.jl"
    juliaFns := ["is_id_start_char(c::AbstractChar)"]
    statement := "For every allowed input, `is_id_start_char(c::AbstractChar)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:25-25", status := .proven
    prop := ``MetaRow25Property, thm := some ``metaRow25_proven },
  { id := "exprreflect-meta-row-26", juliaFile := "base/meta.jl"
    juliaFns := ["is_id_char(c::AbstractChar)"]
    statement := "For every allowed input, `is_id_char(c::AbstractChar)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:26-26", status := .proven
    prop := ``MetaRow26Property, thm := some ``metaRow26_proven },
  { id := "exprreflect-meta-row-48", juliaFile := "base/meta.jl"
    juliaFns := ["isidentifier(s::AbstractString)"]
    statement := "For every allowed input, `isidentifier(s::AbstractString)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:48-55", status := .proven
    prop := ``MetaRow48Property, thm := some ``metaRow48_proven },
  { id := "exprreflect-meta-row-56", juliaFile := "base/meta.jl"
    juliaFns := ["isidentifier(s::Symbol)"]
    statement := "For every allowed input, `isidentifier(s::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:56-56", status := .proven
    prop := ``MetaRow56Property, thm := some ``metaRow56_proven },
  { id := "exprreflect-meta-row-58", juliaFile := "base/meta.jl"
    juliaFns := ["is_op_suffix_char(c::AbstractChar)"]
    statement := "For every allowed input, `is_op_suffix_char(c::AbstractChar)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:58-58", status := .proven
    prop := ``MetaRow58Property, thm := some ``metaRow58_proven },
  { id := "exprreflect-meta-row-60", juliaFile := "base/meta.jl"
    juliaFns := ["_isoperator(s)"]
    statement := "For every allowed input, `_isoperator(s)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:60-60", status := .proven
    prop := ``MetaRow60Property, thm := some ``metaRow60_proven },
  { id := "exprreflect-meta-row-73", juliaFile := "base/meta.jl"
    juliaFns := ["isoperator(s::Union{Symbol,AbstractString})"]
    statement := "For every allowed input, `isoperator(s::Union{Symbol,AbstractString})` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:73-73", status := .proven
    prop := ``MetaRow73Property, thm := some ``metaRow73_proven },
  { id := "exprreflect-meta-row-86", juliaFile := "base/meta.jl"
    juliaFns := ["isunaryoperator(s::Symbol)"]
    statement := "For every allowed input, `isunaryoperator(s::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:86-86", status := .proven
    prop := ``MetaRow86Property, thm := some ``metaRow86_proven },
  { id := "exprreflect-meta-row-87", juliaFile := "base/meta.jl"
    juliaFns := ["is_unary_and_binary_operator(s::Symbol)"]
    statement := "For every allowed input, `is_unary_and_binary_operator(s::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:87-87", status := .proven
    prop := ``MetaRow87Property, thm := some ``metaRow87_proven },
  { id := "exprreflect-meta-row-88", juliaFile := "base/meta.jl"
    juliaFns := ["is_syntactic_operator(s::Symbol)"]
    statement := "For every allowed input, `is_syntactic_operator(s::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:88-88", status := .proven
    prop := ``MetaRow88Property, thm := some ``metaRow88_proven },
  { id := "exprreflect-meta-row-101", juliaFile := "base/meta.jl"
    juliaFns := ["isbinaryoperator(s::Symbol)"]
    statement := "For every allowed input, `isbinaryoperator(s::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:101-104", status := .proven
    prop := ``MetaRow101Property, thm := some ``metaRow101_proven },
  { id := "exprreflect-meta-row-117", juliaFile := "base/meta.jl"
    juliaFns := ["ispostfixoperator(s::Union{Symbol,AbstractString})"]
    statement := "For every allowed input, `ispostfixoperator(s::Union{Symbol,AbstractString})` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:117-120", status := .proven
    prop := ``MetaRow117Property, thm := some ``metaRow117_proven },
  { id := "exprreflect-meta-row-128", juliaFile := "base/meta.jl"
    juliaFns := ["is_valid_identifier(sym)"]
    statement := "For every allowed input, `is_valid_identifier(sym)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:128-134", status := .proven
    prop := ``MetaRow128Property, thm := some ``metaRow128_proven },
  { id := "exprreflect-meta-row-158", juliaFile := "base/meta.jl"
    juliaFns := ["quot(ex)"]
    statement := "For every allowed input, `quot(ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:158-158", status := .proven
    prop := ``MetaRow158Property, thm := some ``metaRow158_proven },
  { id := "exprreflect-meta-row-209", juliaFile := "base/meta.jl"
    juliaFns := ["replace_sourceloc!(sourceloc, @nospecialize(ex))"]
    statement := "For every allowed input, `replace_sourceloc!(sourceloc, @nospecialize(ex))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:209-217", status := .proven
    prop := ``MetaRow209Property, thm := some ``metaRow209_proven },
  { id := "exprreflect-meta-row-231", juliaFile := "base/meta.jl"
    juliaFns := ["show_sexpr(ex)"]
    statement := "For every allowed input, `show_sexpr(ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:231-231", status := .proven
    prop := ``MetaRow231Property, thm := some ``metaRow231_proven },
  { id := "exprreflect-meta-row-232", juliaFile := "base/meta.jl"
    juliaFns := ["show_sexpr(io::IO, ex)"]
    statement := "For every allowed input, `show_sexpr(io::IO, ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:232-232", status := .proven
    prop := ``MetaRow232Property, thm := some ``metaRow232_proven },
  { id := "exprreflect-meta-row-233", juliaFile := "base/meta.jl"
    juliaFns := ["show_sexpr(io::IO, ex, indent::Int)"]
    statement := "For every allowed input, `show_sexpr(io::IO, ex, indent::Int)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:233-233", status := .proven
    prop := ``MetaRow233Property, thm := some ``metaRow233_proven },
  { id := "exprreflect-meta-row-237", juliaFile := "base/meta.jl"
    juliaFns := ["show_sexpr(io::IO, ex::QuoteNode, indent::Int)"]
    statement := "For every allowed input, `show_sexpr(io::IO, ex::QuoteNode, indent::Int)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:237-242", status := .proven
    prop := ``MetaRow237Property, thm := some ``metaRow237_proven },
  { id := "exprreflect-meta-row-243", juliaFile := "base/meta.jl"
    juliaFns := ["show_sexpr(io::IO, ex::Expr, indent::Int)"]
    statement := "For every allowed input, `show_sexpr(io::IO, ex::Expr, indent::Int)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:243-256", status := .proven
    prop := ``MetaRow243Property, thm := some ``metaRow243_proven },
  { id := "exprreflect-meta-row-264", juliaFile := "base/meta.jl"
    juliaFns := ["dump(expr)"]
    statement := "For every allowed input, `dump(expr)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:264-266", status := .proven
    prop := ``MetaRow264Property, thm := some ``metaRow264_proven },
  { id := "exprreflect-meta-row-275", juliaFile := "base/meta.jl"
    juliaFns := ["lower(m::Module, @nospecialize(x))"]
    statement := "For every allowed input, `lower(m::Module, @nospecialize(x))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:275-275", status := .proven
    prop := ``MetaRow275Property, thm := some ``metaRow275_proven },
  { id := "exprreflect-meta-row-284", juliaFile := "base/meta.jl"
    juliaFns := ["lower(code)"]
    statement := "For every allowed input, `lower(code)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:284-286", status := .proven
    prop := ``MetaRow284Property, thm := some ``metaRow284_proven },
  { id := "exprreflect-meta-row-287", juliaFile := "base/meta.jl"
    juliaFns := ["lower(mod, code)"]
    statement := "For every allowed input, `lower(mod, code)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:287-289", status := .proven
    prop := ``MetaRow287Property, thm := some ``metaRow287_proven },
  { id := "exprreflect-meta-row-305", juliaFile := "base/meta.jl"
    juliaFns := ["ParseError(msg::AbstractString)"]
    statement := "For every allowed input, `ParseError(msg::AbstractString)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:305-305", status := .proven
    prop := ``MetaRow305Property, thm := some ``metaRow305_proven },
  { id := "exprreflect-meta-row-307", juliaFile := "base/meta.jl"
    juliaFns := ["parser_for_module(mod::Union{Module, Nothing})"]
    statement := "For every allowed input, `parser_for_module(mod::Union{Module, Nothing})` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:307-313", status := .proven
    prop := ``MetaRow307Property, thm := some ``metaRow307_proven },
  { id := "exprreflect-meta-row-315", juliaFile := "base/meta.jl"
    juliaFns := ["_parse_string(text::AbstractString, filename::AbstractString, lineno::Integer, index::Integer, options, type, _parse=parser_for_module(nothing))"]
    statement := "For every allowed input, `_parse_string(text::AbstractString, filename::AbstractString, lineno::Integer, index::Integer, options, type, _parse=parser_for_module(nothing))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:315-326", status := .proven
    prop := ``MetaRow315Property, thm := some ``metaRow315_proven },
  { id := "exprreflect-meta-row-328", juliaFile := "base/meta.jl"
    juliaFns := ["_is_parse_error(@nospecialize(ex))"]
    statement := "For every allowed input, `_is_parse_error(@nospecialize(ex))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:328-329", status := .proven
    prop := ``MetaRow328Property, thm := some ``metaRow328_proven },
  { id := "exprreflect-meta-row-363", juliaFile := "base/meta.jl"
    juliaFns := ["parse(str::AbstractString, pos::Integer; filename=\"none\", greedy::Bool=true, raise::Bool=true, depwarn::Bool=true, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))"]
    statement := "For every allowed input, `parse(str::AbstractString, pos::Integer; filename=\"none\", greedy::Bool=true, raise::Bool=true, depwarn::Bool=true, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:363-377", status := .proven
    prop := ``MetaRow363Property, thm := some ``metaRow363_proven },
  { id := "exprreflect-meta-row-406", juliaFile := "base/meta.jl"
    juliaFns := ["parse(str::AbstractString; filename=\"none\", raise::Bool=true, depwarn::Bool=true, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))"]
    statement := "For every allowed input, `parse(str::AbstractString; filename=\"none\", raise::Bool=true, depwarn::Bool=true, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:406-421", status := .proven
    prop := ``MetaRow406Property, thm := some ``metaRow406_proven },
  { id := "exprreflect-meta-row-423", juliaFile := "base/meta.jl"
    juliaFns := ["parseatom(text::AbstractString, pos::Integer; filename=\"none\", lineno=1, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))"]
    statement := "For every allowed input, `parseatom(text::AbstractString, pos::Integer; filename=\"none\", lineno=1, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:423-427", status := .proven
    prop := ``MetaRow423Property, thm := some ``metaRow423_proven },
  { id := "exprreflect-meta-row-429", juliaFile := "base/meta.jl"
    juliaFns := ["parseall(text::AbstractString; filename=\"none\", lineno=1, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))"]
    statement := "For every allowed input, `parseall(text::AbstractString; filename=\"none\", lineno=1, mod::Union{Nothing, Module}=nothing, type=Expr, _parse = parser_for_module(mod))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:429-434", status := .proven
    prop := ``MetaRow429Property, thm := some ``metaRow429_proven },
  { id := "exprreflect-meta-row-463", juliaFile := "base/meta.jl"
    juliaFns := ["partially_inline!(code::Vector{Any}, slot_replacements::Vector{Any}, @nospecialize(type_signature)#=::Type{<:Tuple}=#, static_param_values::Vector{Any}, slot_offset::Int, statement_offset::Int, boundscheck::Symbol)"]
    statement := "For every allowed input, `partially_inline!(code::Vector{Any}, slot_replacements::Vector{Any}, @nospecialize(type_signature)#=::Type{<:Tuple}=#, static_param_values::Vector{Any}, slot_offset::Int, statement_offset::Int, boundscheck::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:463-475", status := .proven
    prop := ``MetaRow463Property, thm := some ``metaRow463_proven },
  { id := "exprreflect-meta-row-477", juliaFile := "base/meta.jl"
    juliaFns := ["_partially_inline!(@nospecialize(x), slot_replacements::Vector{Any}, @nospecialize(type_signature), static_param_values::Vector{Any}, slot_offset::Int, statement_offset::Int, boundscheck::Symbol)"]
    statement := "For every allowed input, `_partially_inline!(@nospecialize(x), slot_replacements::Vector{Any}, @nospecialize(type_signature), static_param_values::Vector{Any}, slot_offset::Int, statement_offset::Int, boundscheck::Symbol)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:477-621", status := .proven
    prop := ``MetaRow477Property, thm := some ``metaRow477_proven },
  { id := "exprreflect-meta-row-623", juliaFile := "base/meta.jl"
    juliaFns := ["_instantiate_type_in_env(x, spsig, spvals)"]
    statement := "For every allowed input, `_instantiate_type_in_env(x, spsig, spvals)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:623-623", status := .proven
    prop := ``MetaRow623Property, thm := some ``metaRow623_proven },
  { id := "exprreflect-meta-row-634", juliaFile := "base/meta.jl"
    juliaFns := ["unblock(@nospecialize ex)"]
    statement := "For every allowed input, `unblock(@nospecialize ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:634-643", status := .proven
    prop := ``MetaRow634Property, thm := some ``metaRow634_proven },
  { id := "exprreflect-meta-row-651", juliaFile := "base/meta.jl"
    juliaFns := ["unescape(@nospecialize ex)"]
    statement := "For every allowed input, `unescape(@nospecialize ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:651-657", status := .proven
    prop := ``MetaRow651Property, thm := some ``metaRow651_proven },
  { id := "exprreflect-meta-row-666", juliaFile := "base/meta.jl"
    juliaFns := ["reescape(@nospecialize(unescaped_expr), @nospecialize(original_expr))"]
    statement := "For every allowed input, `reescape(@nospecialize(unescaped_expr), @nospecialize(original_expr))` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:666-675", status := .proven
    prop := ``MetaRow666Property, thm := some ``metaRow666_proven },
  { id := "exprreflect-meta-row-682", juliaFile := "base/meta.jl"
    juliaFns := ["uncurly(@nospecialize ex)"]
    statement := "For every allowed input, `uncurly(@nospecialize ex)` follows its own predicate, AST, parser, inlining, or hygiene body."
    source := "source-body invariant; base/meta.jl:682-682", status := .proven
    prop := ``MetaRow682Property, thm := some ``metaRow682_proven }
]

end JuliaLean.ExprReflect
