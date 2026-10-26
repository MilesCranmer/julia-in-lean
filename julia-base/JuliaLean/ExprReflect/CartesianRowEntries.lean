import JuliaLean.ExprReflect.CartesianRows
import JuliaLean.Registry.Types

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def cartesianRowEntries : List Entry := [
  { id := "exprreflect-cartesian-row-38", juliaFile := "base/cartesian.jl"
    juliaFns := ["nloops(N, itersym, rangeexpr, args...)"]
    statement := "For every allowed input, `nloops(N, itersym, rangeexpr, args...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:38-40", status := .proven
    prop := ``CartRow38Property, thm := some ``cartRow38_proven },
  { id := "exprreflect-cartesian-row-42", juliaFile := "base/cartesian.jl"
    juliaFns := ["_nloops(N::Int, itersym::Symbol, esc_rng::Bool, arraysym::Symbol, args::Expr...)"]
    statement := "For every allowed input, `_nloops(N::Int, itersym::Symbol, esc_rng::Bool, arraysym::Symbol, args::Expr...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:42-44", status := .proven
    prop := ``CartRow42Property, thm := some ``cartRow42_proven },
  { id := "exprreflect-cartesian-row-46", juliaFile := "base/cartesian.jl"
    juliaFns := ["_nloops(N::Int, itersym::Symbol, esc_rng::Bool, rangeexpr::Expr, args::Expr...)"]
    statement := "For every allowed input, `_nloops(N::Int, itersym::Symbol, esc_rng::Bool, rangeexpr::Expr, args::Expr...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:46-71", status := .proven
    prop := ``CartRow46Property, thm := some ``cartRow46_proven },
  { id := "exprreflect-cartesian-row-85", juliaFile := "base/cartesian.jl"
    juliaFns := ["nref(N::Int, A::Symbol, ex)"]
    statement := "For every allowed input, `nref(N::Int, A::Symbol, ex)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:85-88", status := .proven
    prop := ``CartRow85Property, thm := some ``cartRow85_proven },
  { id := "exprreflect-cartesian-row-105", juliaFile := "base/cartesian.jl"
    juliaFns := ["ncall(N::Int, f, args...)"]
    statement := "For every allowed input, `ncall(N::Int, f, args...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:105-110", status := .proven
    prop := ``CartRow105Property, thm := some ``cartRow105_proven },
  { id := "exprreflect-cartesian-row-132", juliaFile := "base/cartesian.jl"
    juliaFns := ["ncallkw(N::Int, f, kw, args...)"]
    statement := "For every allowed input, `ncallkw(N::Int, f, kw, args...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:132-138", status := .proven
    prop := ``CartRow132Property, thm := some ``cartRow132_proven },
  { id := "exprreflect-cartesian-row-156", juliaFile := "base/cartesian.jl"
    juliaFns := ["nexprs(N::Int, ex::Expr)"]
    statement := "For every allowed input, `nexprs(N::Int, ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:156-159", status := .proven
    prop := ``CartRow156Property, thm := some ``cartRow156_proven },
  { id := "exprreflect-cartesian-row-179", juliaFile := "base/cartesian.jl"
    juliaFns := ["nextract(N::Int, esym::Symbol, isym::Symbol)"]
    statement := "For every allowed input, `nextract(N::Int, esym::Symbol, isym::Symbol)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:179-182", status := .proven
    prop := ``CartRow179Property, thm := some ``cartRow179_proven },
  { id := "exprreflect-cartesian-row-184", juliaFile := "base/cartesian.jl"
    juliaFns := ["nextract(N::Int, esym::Symbol, ex::Expr)"]
    statement := "For every allowed input, `nextract(N::Int, esym::Symbol, ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:184-187", status := .proven
    prop := ``CartRow184Property, thm := some ``cartRow184_proven },
  { id := "exprreflect-cartesian-row-198", juliaFile := "base/cartesian.jl"
    juliaFns := ["nall(N::Int, criterion::Expr)"]
    statement := "For every allowed input, `nall(N::Int, criterion::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:198-204", status := .proven
    prop := ``CartRow198All, thm := some ``cartRow198_all },
  { id := "exprreflect-cartesian-row-214", juliaFile := "base/cartesian.jl"
    juliaFns := ["nany(N::Int, criterion::Expr)"]
    statement := "For every allowed input, `nany(N::Int, criterion::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:214-220", status := .proven
    prop := ``CartRow214All, thm := some ``cartRow214_all },
  { id := "exprreflect-cartesian-row-228", juliaFile := "base/cartesian.jl"
    juliaFns := ["ntuple(N::Int, ex)"]
    statement := "For every allowed input, `ntuple(N::Int, ex)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:228-231", status := .proven
    prop := ``CartRow228Property, thm := some ``cartRow228_proven },
  { id := "exprreflect-cartesian-row-251", juliaFile := "base/cartesian.jl"
    juliaFns := ["nif(N, condition, operation...)"]
    statement := "For every allowed input, `nif(N, condition, operation...)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:251-259", status := .proven
    prop := ``CartRow251Property, thm := some ``cartRow251_proven },
  { id := "exprreflect-cartesian-row-264", juliaFile := "base/cartesian.jl"
    juliaFns := ["inlineanonymous(ex::Expr, val)"]
    statement := "For every allowed input, `inlineanonymous(ex::Expr, val)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:264-276", status := .proven
    prop := ``CartRow264Property, thm := some ``cartRow264_proven },
  { id := "exprreflect-cartesian-row-279", juliaFile := "base/cartesian.jl"
    juliaFns := ["inlineanonymous(base::Symbol, ext)"]
    statement := "For every allowed input, `inlineanonymous(base::Symbol, ext)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:279-279", status := .proven
    prop := ``CartRow279Property, thm := some ``cartRow279_proven },
  { id := "exprreflect-cartesian-row-292", juliaFile := "base/cartesian.jl"
    juliaFns := ["LReplace(sym::Symbol, val::Integer)"]
    statement := "For every allowed input, `LReplace(sym::Symbol, val::Integer)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:292-292", status := .proven
    prop := ``CartRow292Property, thm := some ``cartRow292_proven },
  { id := "exprreflect-cartesian-row-294", juliaFile := "base/cartesian.jl"
    juliaFns := ["lreplace(ex::Expr, sym::Symbol, val)"]
    statement := "For every allowed input, `lreplace(ex::Expr, sym::Symbol, val)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:294-294", status := .proven
    prop := ``CartRow294Property, thm := some ``cartRow294_proven },
  { id := "exprreflect-cartesian-row-296", juliaFile := "base/cartesian.jl"
    juliaFns := ["lreplace!(sym::Symbol, r::LReplace, in_quote_context::Bool, escs::Int)"]
    statement := "For every allowed input, `lreplace!(sym::Symbol, r::LReplace, in_quote_context::Bool, escs::Int)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:296-300", status := .proven
    prop := ``CartRow296Property, thm := some ``cartRow296_proven },
  { id := "exprreflect-cartesian-row-302", juliaFile := "base/cartesian.jl"
    juliaFns := ["lreplace_string!(str::String, r::LReplace)"]
    statement := "For every allowed input, `lreplace_string!(str::String, r::LReplace)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:302-342", status := .proven
    prop := ``CartRow302Property, thm := some ``cartRow302_proven },
  { id := "exprreflect-cartesian-row-344", juliaFile := "base/cartesian.jl"
    juliaFns := ["lreplace!(ex::Expr, r::LReplace, in_quote_context::Bool, escs::Int)"]
    statement := "For every allowed input, `lreplace!(ex::Expr, r::LReplace, in_quote_context::Bool, escs::Int)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:344-377", status := .proven
    prop := ``CartRow344Property, thm := some ``cartRow344_proven },
  { id := "exprreflect-cartesian-row-379", juliaFile := "base/cartesian.jl"
    juliaFns := ["lreplace!(@nospecialize(arg), r::LReplace, in_quote_context::Bool, escs::Int)"]
    statement := "For every allowed input, `lreplace!(@nospecialize(arg), r::LReplace, in_quote_context::Bool, escs::Int)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:379-379", status := .proven
    prop := ``CartRow379Property, thm := some ``cartRow379_proven },
  { id := "exprreflect-cartesian-row-383", juliaFile := "base/cartesian.jl"
    juliaFns := ["poplinenum(arg)"]
    statement := "For every allowed input, `poplinenum(arg)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:383-383", status := .proven
    prop := ``CartRow383Property, thm := some ``cartRow383_proven },
  { id := "exprreflect-cartesian-row-384", juliaFile := "base/cartesian.jl"
    juliaFns := ["poplinenum(ex::Expr)"]
    statement := "For every allowed input, `poplinenum(ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:384-399", status := .proven
    prop := ``CartRow384Property, thm := some ``cartRow384_proven },
  { id := "exprreflect-cartesian-row-408", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve_arith(ex::Expr)"]
    statement := "For every allowed input, `exprresolve_arith(ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:408-418", status := .proven
    prop := ``CartRow408All, thm := some ``cartRow408_all },
  { id := "exprreflect-cartesian-row-419", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve_arith(arg)"]
    statement := "For every allowed input, `exprresolve_arith(arg)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:419-419", status := .proven
    prop := ``CartRow419Property, thm := some ``cartRow419_proven },
  { id := "exprreflect-cartesian-row-421", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve_conditional(b::Bool)"]
    statement := "For every allowed input, `exprresolve_conditional(b::Bool)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:421-421", status := .proven
    prop := ``CartRow421Property, thm := some ``cartRow421_proven },
  { id := "exprreflect-cartesian-row-422", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve_conditional(ex::Expr)"]
    statement := "For every allowed input, `exprresolve_conditional(ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:422-434", status := .proven
    prop := ``CartRow422All, thm := some ``cartRow422_all },
  { id := "exprreflect-cartesian-row-435", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve_conditional(arg)"]
    statement := "For every allowed input, `exprresolve_conditional(arg)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:435-435", status := .proven
    prop := ``CartRow435Property, thm := some ``cartRow435_proven },
  { id := "exprreflect-cartesian-row-437", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve(arg)"]
    statement := "For every allowed input, `exprresolve(arg)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:437-437", status := .proven
    prop := ``CartRow437Property, thm := some ``cartRow437_proven },
  { id := "exprreflect-cartesian-row-438", juliaFile := "base/cartesian.jl"
    juliaFns := ["exprresolve(ex::Expr)"]
    statement := "For every allowed input, `exprresolve(ex::Expr)` follows its own AST construction, validation, substitution, or evaluation body."
    source := "source-body invariant; base/cartesian.jl:438-473", status := .proven
    prop := ``CartRow438Property, thm := some ``cartRow438_proven }
]

end JuliaLean.ExprReflect
