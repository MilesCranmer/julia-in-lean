import JuliaLean.ExprReflect.ExprRows
import JuliaLean.Registry.Types

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def exprRowEntries : List Entry := [
  { id := "exprreflect-expr-row-3", juliaFile := "base/expr.jl"
    juliaFns := ["isexpr(@nospecialize(ex), heads)"]
    statement := "For every allowed input, `isexpr(@nospecialize(ex), heads)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:3-3", status := .proven
    prop := ``ExprRow3Property, thm := some ``exprRow3_proven },
  { id := "exprreflect-expr-row-4", juliaFile := "base/expr.jl"
    juliaFns := ["isexpr(@nospecialize(ex), heads, n::Int)"]
    statement := "For every allowed input, `isexpr(@nospecialize(ex), heads, n::Int)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:4-4", status := .proven
    prop := ``ExprRow4Property, thm := some ``exprRow4_proven },
  { id := "exprreflect-expr-row-18", juliaFile := "base/expr.jl"
    juliaFns := ["gensym()"]
    statement := "For every allowed input, `gensym()` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:18-18", status := .proven
    prop := ``ExprRow18Property, thm := some ``exprRow18_proven },
  { id := "exprreflect-expr-row-20", juliaFile := "base/expr.jl"
    juliaFns := ["gensym(s::String)"]
    statement := "For every allowed input, `gensym(s::String)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:20-20", status := .proven
    prop := ``ExprRow20Property, thm := some ``exprRow20_proven },
  { id := "exprreflect-expr-row-22", juliaFile := "base/expr.jl"
    juliaFns := ["gensym(ss::String...)"]
    statement := "For every allowed input, `gensym(ss::String...)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:22-22", status := .proven
    prop := ``ExprRow22Property, thm := some ``exprRow22_proven },
  { id := "exprreflect-expr-row-23", juliaFile := "base/expr.jl"
    juliaFns := ["gensym(s::Symbol)"]
    statement := "For every allowed input, `gensym(s::Symbol)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:23-23", status := .proven
    prop := ``ExprRow23Property, thm := some ``exprRow23_proven },
  { id := "exprreflect-expr-row-31", juliaFile := "base/expr.jl"
    juliaFns := ["gensym(names...)"]
    statement := "For every allowed input, `gensym(names...)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:31-38", status := .proven
    prop := ``ExprRow31Property, thm := some ``exprRow31_proven },
  { id := "exprreflect-expr-row-42", juliaFile := "base/expr.jl"
    juliaFns := ["isexpr(@nospecialize(ex), head::Symbol)"]
    statement := "For every allowed input, `isexpr(@nospecialize(ex), head::Symbol)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:42-42", status := .proven
    prop := ``ExprRow42Property, thm := some ``exprRow42_proven },
  { id := "exprreflect-expr-row-43", juliaFile := "base/expr.jl"
    juliaFns := ["isexpr(@nospecialize(ex), head::Symbol, n::Int)"]
    statement := "For every allowed input, `isexpr(@nospecialize(ex), head::Symbol, n::Int)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:43-43", status := .proven
    prop := ``ExprRow43Property, thm := some ``exprRow43_proven },
  { id := "exprreflect-expr-row-45", juliaFile := "base/expr.jl"
    juliaFns := ["copy(e::Expr)"]
    statement := "For every allowed input, `copy(e::Expr)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:45-45", status := .proven
    prop := ``ExprRow45Property, thm := some ``exprRow45_proven },
  { id := "exprreflect-expr-row-46", juliaFile := "base/expr.jl"
    juliaFns := ["copy(x::PhiNode)"]
    statement := "For every allowed input, `copy(x::PhiNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:46-55", status := .proven
    prop := ``ExprRow46Property, thm := some ``exprRow46_proven },
  { id := "exprreflect-expr-row-56", juliaFile := "base/expr.jl"
    juliaFns := ["copy(x::PhiCNode)"]
    statement := "For every allowed input, `copy(x::PhiCNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:56-65", status := .proven
    prop := ``ExprRow56Property, thm := some ``exprRow56_proven },
  { id := "exprreflect-expr-row-69", juliaFile := "base/expr.jl"
    juliaFns := ["copy_exprs(@nospecialize(x))"]
    statement := "For every allowed input, `copy_exprs(@nospecialize(x))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:69-78", status := .proven
    prop := ``ExprRow69Property, thm := some ``exprRow69_proven },
  { id := "exprreflect-expr-row-79", juliaFile := "base/expr.jl"
    juliaFns := ["copy_exprargs(x::Array{Any,1})"]
    statement := "For every allowed input, `copy_exprargs(x::Array{Any,1})` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:79-79", status := .proven
    prop := ``ExprRow79Property, thm := some ``exprRow79_proven },
  { id := "exprreflect-expr-row-81", juliaFile := "base/expr.jl"
    juliaFns := ["exprarray(head::Symbol, arg::Array{Any,1})"]
    statement := "For every allowed input, `exprarray(head::Symbol, arg::Array{Any,1})` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:81-81", status := .proven
    prop := ``ExprRow81Property, thm := some ``exprRow81_proven },
  { id := "exprreflect-expr-row-84", juliaFile := "base/expr.jl"
    juliaFns := ["copy(c::CodeInfo)"]
    statement := "For every allowed input, `copy(c::CodeInfo)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:84-97", status := .proven
    prop := ``ExprRow84Property, thm := some ``exprRow84_proven },
  { id := "exprreflect-expr-row-99", juliaFile := "base/expr.jl"
    juliaFns := ["isequal_exprarg(@nospecialize(x), @nospecialize(y))"]
    statement := "For every allowed input, `isequal_exprarg(@nospecialize(x), @nospecialize(y))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:99-115", status := .proven
    prop := ``ExprRow99Property, thm := some ``exprRow99_proven },
  { id := "exprreflect-expr-row-118", juliaFile := "base/expr.jl"
    juliaFns := ["isequal_exprargs(x::Array{Any,1}, y::Array{Any,1})"]
    statement := "For every allowed input, `isequal_exprargs(x::Array{Any,1}, y::Array{Any,1})` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:118-131", status := .proven
    prop := ``ExprRow118Property, thm := some ``exprRow118_proven },
  { id := "exprreflect-expr-row-135", juliaFile := "base/expr.jl"
    juliaFns := ["==(x::Expr, y::Expr)"]
    statement := "For every allowed input, `==(x::Expr, y::Expr)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:135-135", status := .proven
    prop := ``ExprRow135Property, thm := some ``exprRow135_proven },
  { id := "exprreflect-expr-row-137", juliaFile := "base/expr.jl"
    juliaFns := ["==(x::QuoteNode, y::QuoteNode)"]
    statement := "For every allowed input, `==(x::QuoteNode, y::QuoteNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:137-137", status := .proven
    prop := ``ExprRow137Property, thm := some ``exprRow137_proven },
  { id := "exprreflect-expr-row-139", juliaFile := "base/expr.jl"
    juliaFns := ["==(stmt1::Core.PhiNode, stmt2::Core.PhiNode)"]
    statement := "For every allowed input, `==(stmt1::Core.PhiNode, stmt2::Core.PhiNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:139-139", status := .proven
    prop := ``ExprRow139Property, thm := some ``exprRow139_proven },
  { id := "exprreflect-expr-row-141", juliaFile := "base/expr.jl"
    juliaFns := ["==(stmt1::Core.PhiCNode, stmt2::Core.PhiCNode)"]
    statement := "For every allowed input, `==(stmt1::Core.PhiCNode, stmt2::Core.PhiCNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:141-141", status := .proven
    prop := ``ExprRow141Property, thm := some ``exprRow141_proven },
  { id := "exprreflect-expr-row-143", juliaFile := "base/expr.jl"
    juliaFns := ["==(stmt1::CodeInfo, stmt2::CodeInfo)"]
    statement := "For every allowed input, `==(stmt1::CodeInfo, stmt2::CodeInfo)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:143-171", status := .proven
    prop := ``ExprRow143Property, thm := some ``exprRow143_proven },
  { id := "exprreflect-expr-row-173", juliaFile := "base/expr.jl"
    juliaFns := ["==(x::DebugInfo, y::DebugInfo)"]
    statement := "For every allowed input, `==(x::DebugInfo, y::DebugInfo)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:173-178", status := .proven
    prop := ``ExprRow173Property, thm := some ``exprRow173_proven },
  { id := "exprreflect-expr-row-209", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand(m::Module, @nospecialize(x); recursive=true, legacyscope=true)"]
    statement := "For every allowed input, `macroexpand(m::Module, @nospecialize(x); recursive=true, legacyscope=true)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:209-211", status := .proven
    prop := ``ExprRow209Property, thm := some ``exprRow209_proven },
  { id := "exprreflect-expr-row-232", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand!(m::Module, @nospecialize(x); recursive=true, legacyscope=false)"]
    statement := "For every allowed input, `macroexpand!(m::Module, @nospecialize(x); recursive=true, legacyscope=false)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:232-234", status := .proven
    prop := ``ExprRow232Property, thm := some ``exprRow232_proven },
  { id := "exprreflect-expr-row-279", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand(code)"]
    statement := "For every allowed input, `macroexpand(code)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:279-281", status := .proven
    prop := ``ExprRow279Property, thm := some ``exprRow279_proven },
  { id := "exprreflect-expr-row-282", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand(mod, code)"]
    statement := "For every allowed input, `macroexpand(mod, code)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:282-284", status := .proven
    prop := ``ExprRow282Property, thm := some ``exprRow282_proven },
  { id := "exprreflect-expr-row-291", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand1(code)"]
    statement := "For every allowed input, `macroexpand1(code)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:291-293", status := .proven
    prop := ``ExprRow291Property, thm := some ``exprRow291_proven },
  { id := "exprreflect-expr-row-294", juliaFile := "base/expr.jl"
    juliaFns := ["macroexpand1(mod, code)"]
    statement := "For every allowed input, `macroexpand1(mod, code)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:294-296", status := .proven
    prop := ``ExprRow294Property, thm := some ``exprRow294_proven },
  { id := "exprreflect-expr-row-389", juliaFile := "base/expr.jl"
    juliaFns := ["inline(x)"]
    statement := "For every allowed input, `inline(x)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:389-391", status := .proven
    prop := ``ExprRow389Property, thm := some ``exprRow389_proven },
  { id := "exprreflect-expr-row-466", juliaFile := "base/expr.jl"
    juliaFns := ["noinline(x)"]
    statement := "For every allowed input, `noinline(x)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:466-468", status := .proven
    prop := ``ExprRow466Property, thm := some ``exprRow466_proven },
  { id := "exprreflect-expr-row-505", juliaFile := "base/expr.jl"
    juliaFns := ["constprop(setting, ex)"]
    statement := "For every allowed input, `constprop(setting, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:505-509", status := .proven
    prop := ``ExprRow505Property, thm := some ``exprRow505_proven },
  { id := "exprreflect-expr-row-510", juliaFile := "base/expr.jl"
    juliaFns := ["constprop(setting)"]
    statement := "For every allowed input, `constprop(setting)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:510-513", status := .proven
    prop := ``ExprRow510Property, thm := some ``exprRow510_proven },
  { id := "exprreflect-expr-row-515", juliaFile := "base/expr.jl"
    juliaFns := ["constprop_setting(@nospecialize setting)"]
    statement := "For every allowed input, `constprop_setting(@nospecialize setting)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:515-524", status := .proven
    prop := ``ExprRow515Property, thm := some ``exprRow515_proven },
  { id := "exprreflect-expr-row-896", juliaFile := "base/expr.jl"
    juliaFns := ["assume_effects(args...)"]
    statement := "For every allowed input, `assume_effects(args...)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:896-936", status := .proven
    prop := ``ExprRow896Property, thm := some ``exprRow896_proven },
  { id := "exprreflect-expr-row-938", juliaFile := "base/expr.jl"
    juliaFns := ["compute_assumed_settings(settings)"]
    statement := "For every allowed input, `compute_assumed_settings(settings)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:938-946", status := .proven
    prop := ``ExprRow938Property, thm := some ``exprRow938_proven },
  { id := "exprreflect-expr-row-962", juliaFile := "base/expr.jl"
    juliaFns := ["EffectsOverride( override::EffectsOverride = EffectsOverride(false, false, false, false, false, false, false, false, false, false, false); consistent::Bool = override.consistent, effect_free::Bool = override.effect_free, nothrow::Bool = override.nothrow, terminates_globally::Bool = override.terminates_globally, terminates_locally::Bool = override.terminates_locally, notaskstate::Bool = override.notaskstate, inaccessiblememonly::Bool = override.inaccessiblememonly, noub::Bool = override.noub, noub_if_noinbounds::Bool = override.noub_if_noinbounds, consistent_overlay::Bool = override.consistent_overlay, nortcall::Bool = override.nortcall)"]
    statement := "For every allowed input, `EffectsOverride( override::EffectsOverride = EffectsOverride(false, false, false, false, false, false, false, false, false, false, false); consistent::Bool = override.consistent, effect_free::Bool = override.effect_free, nothrow::Bool = override.nothrow, terminates_globally::Bool = override.terminates_globally, terminates_locally::Bool = override.terminates_locally, notaskstate::Bool = override.notaskstate, inaccessiblememonly::Bool = override.inaccessiblememonly, noub::Bool = override.noub, noub_if_noinbounds::Bool = override.noub_if_noinbounds, consistent_overlay::Bool = override.consistent_overlay, nortcall::Bool = override.nortcall)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:962-988", status := .proven
    prop := ``ExprRow962Property, thm := some ``exprRow962_proven },
  { id := "exprreflect-expr-row-995", juliaFile := "base/expr.jl"
    juliaFns := ["compute_assumed_setting(override::EffectsOverride, @nospecialize(setting), val::Bool=true)"]
    statement := "For every allowed input, `compute_assumed_setting(override::EffectsOverride, @nospecialize(setting), val::Bool=true)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:995-1033", status := .proven
    prop := ``ExprRow995Property, thm := some ``exprRow995_proven },
  { id := "exprreflect-expr-row-1035", juliaFile := "base/expr.jl"
    juliaFns := ["encode_effects_override(eo::EffectsOverride)"]
    statement := "For every allowed input, `encode_effects_override(eo::EffectsOverride)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1035-1049", status := .proven
    prop := ``ExprRow1035Property, thm := some ``exprRow1035_proven },
  { id := "exprreflect-expr-row-1051", juliaFile := "base/expr.jl"
    juliaFns := ["decode_effects_override(e::UInt16)"]
    statement := "For every allowed input, `decode_effects_override(e::UInt16)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1051-1064", status := .proven
    prop := ``ExprRow1051Property, thm := some ``exprRow1051_proven },
  { id := "exprreflect-expr-row-1066", juliaFile := "base/expr.jl"
    juliaFns := ["form_purity_expr(override::EffectsOverride)"]
    statement := "For every allowed input, `form_purity_expr(override::EffectsOverride)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1066-1072", status := .proven
    prop := ``ExprRow1066Property, thm := some ``exprRow1066_proven },
  { id := "exprreflect-expr-row-1111", juliaFile := "base/expr.jl"
    juliaFns := ["nospecializeinfer(ex)"]
    statement := "For every allowed input, `nospecializeinfer(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1111-1113", status := .proven
    prop := ``ExprRow1111Property, thm := some ``exprRow1111_proven },
  { id := "exprreflect-expr-row-1148", juliaFile := "base/expr.jl"
    juliaFns := ["propagate_inbounds(ex)"]
    statement := "For every allowed input, `propagate_inbounds(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1148-1154", status := .proven
    prop := ``ExprRow1148Property, thm := some ``exprRow1148_proven },
  { id := "exprreflect-expr-row-1161", juliaFile := "base/expr.jl"
    juliaFns := ["polly(ex)"]
    statement := "For every allowed input, `polly(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1161-1163", status := .proven
    prop := ``ExprRow1161Property, thm := some ``exprRow1161_proven },
  { id := "exprreflect-expr-row-1167", juliaFile := "base/expr.jl"
    juliaFns := ["unwrap_macrocalls(@nospecialize(x))"]
    statement := "For every allowed input, `unwrap_macrocalls(@nospecialize(x))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1167-1167", status := .proven
    prop := ``ExprRow1167Property, thm := some ``exprRow1167_proven },
  { id := "exprreflect-expr-row-1168", juliaFile := "base/expr.jl"
    juliaFns := ["unwrap_macrocalls(ex::Expr)"]
    statement := "For every allowed input, `unwrap_macrocalls(ex::Expr)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1168-1174", status := .proven
    prop := ``ExprRow1168Property, thm := some ``exprRow1168_proven },
  { id := "exprreflect-expr-row-1176", juliaFile := "base/expr.jl"
    juliaFns := ["pushmeta!(ex::Expr, tag::Union{Symbol,Expr})"]
    statement := "For every allowed input, `pushmeta!(ex::Expr, tag::Union{Symbol,Expr})` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1176-1187", status := .proven
    prop := ``ExprRow1176Property, thm := some ``exprRow1176_proven },
  { id := "exprreflect-expr-row-1189", juliaFile := "base/expr.jl"
    juliaFns := ["popmeta!(body, sym)"]
    statement := "For every allowed input, `popmeta!(body, sym)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1189-1189", status := .proven
    prop := ``ExprRow1189Property, thm := some ``exprRow1189_proven },
  { id := "exprreflect-expr-row-1190", juliaFile := "base/expr.jl"
    juliaFns := ["peekmeta(body, sym)"]
    statement := "For every allowed input, `peekmeta(body, sym)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1190-1190", status := .proven
    prop := ``ExprRow1190Property, thm := some ``exprRow1190_proven },
  { id := "exprreflect-expr-row-1192", juliaFile := "base/expr.jl"
    juliaFns := ["_getmeta(body::Expr, sym::Symbol, delete::Bool)"]
    statement := "For every allowed input, `_getmeta(body::Expr, sym::Symbol, delete::Bool)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1192-1195", status := .proven
    prop := ``ExprRow1192Property, thm := some ``exprRow1192_proven },
  { id := "exprreflect-expr-row-1196", juliaFile := "base/expr.jl"
    juliaFns := ["_getmeta(arg, sym, delete::Bool)"]
    statement := "For every allowed input, `_getmeta(arg, sym, delete::Bool)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1196-1196", status := .proven
    prop := ``ExprRow1196Property, thm := some ``exprRow1196_proven },
  { id := "exprreflect-expr-row-1197", juliaFile := "base/expr.jl"
    juliaFns := ["_getmeta(body::Array{Any,1}, sym::Symbol, delete::Bool)"]
    statement := "For every allowed input, `_getmeta(body::Array{Any,1}, sym::Symbol, delete::Bool)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1197-1213", status := .proven
    prop := ``ExprRow1197Property, thm := some ``exprRow1197_proven },
  { id := "exprreflect-expr-row-1216", juliaFile := "base/expr.jl"
    juliaFns := ["findmetaarg(metaargs, sym)"]
    statement := "For every allowed input, `findmetaarg(metaargs, sym)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1216-1225", status := .proven
    prop := ``ExprRow1216Property, thm := some ``exprRow1216_proven },
  { id := "exprreflect-expr-row-1227", juliaFile := "base/expr.jl"
    juliaFns := ["annotate_meta_def_or_block(@nospecialize(ex), meta::Symbol)"]
    statement := "For every allowed input, `annotate_meta_def_or_block(@nospecialize(ex), meta::Symbol)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1227-1240", status := .proven
    prop := ``ExprRow1227Property, thm := some ``exprRow1227_proven },
  { id := "exprreflect-expr-row-1242", juliaFile := "base/expr.jl"
    juliaFns := ["is_short_function_def(@nospecialize(ex))"]
    statement := "For every allowed input, `is_short_function_def(@nospecialize(ex))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1242-1250", status := .proven
    prop := ``ExprRow1242Property, thm := some ``exprRow1242_proven },
  { id := "exprreflect-expr-row-1251", juliaFile := "base/expr.jl"
    juliaFns := ["is_function_def(@nospecialize(ex))"]
    statement := "For every allowed input, `is_function_def(@nospecialize(ex))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1251-1252", status := .proven
    prop := ``ExprRow1251Property, thm := some ``exprRow1251_proven },
  { id := "exprreflect-expr-row-1254", juliaFile := "base/expr.jl"
    juliaFns := ["findmeta(ex::Expr)"]
    statement := "For every allowed input, `findmeta(ex::Expr)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1254-1261", status := .proven
    prop := ``ExprRow1254Property, thm := some ``exprRow1254_proven },
  { id := "exprreflect-expr-row-1263", juliaFile := "base/expr.jl"
    juliaFns := ["findmeta(ex::Array{Any,1})"]
    statement := "For every allowed input, `findmeta(ex::Array{Any,1})` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1263-1263", status := .proven
    prop := ``ExprRow1263Property, thm := some ``exprRow1263_proven },
  { id := "exprreflect-expr-row-1265", juliaFile := "base/expr.jl"
    juliaFns := ["findmeta_block(exargs, argsmatch=args->true)"]
    statement := "For every allowed input, `findmeta_block(exargs, argsmatch=args->true)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1265-1280", status := .proven
    prop := ``ExprRow1265Property, thm := some ``exprRow1265_proven },
  { id := "exprreflect-expr-row-1287", juliaFile := "base/expr.jl"
    juliaFns := ["remove_linenums!(@nospecialize ex)"]
    statement := "For every allowed input, `remove_linenums!(@nospecialize ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1287-1304", status := .proven
    prop := ``ExprRow1287Property, thm := some ``exprRow1287_proven },
  { id := "exprreflect-expr-row-1306", juliaFile := "base/expr.jl"
    juliaFns := ["replace_linenums!(ex, ln::LineNumberNode)"]
    statement := "For every allowed input, `replace_linenums!(ex, ln::LineNumberNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1306-1306", status := .proven
    prop := ``ExprRow1306Property, thm := some ``exprRow1306_proven },
  { id := "exprreflect-expr-row-1307", juliaFile := "base/expr.jl"
    juliaFns := ["replace_linenums!(ex::Expr, ln::LineNumberNode)"]
    statement := "For every allowed input, `replace_linenums!(ex::Expr, ln::LineNumberNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1307-1324", status := .proven
    prop := ``ExprRow1307Property, thm := some ``exprRow1307_proven },
  { id := "exprreflect-expr-row-1326", juliaFile := "base/expr.jl"
    juliaFns := ["generated()"]
    statement := "For every allowed input, `generated()` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1326-1328", status := .proven
    prop := ``ExprRow1326Property, thm := some ``exprRow1326_proven },
  { id := "exprreflect-expr-row-1359", juliaFile := "base/expr.jl"
    juliaFns := ["generated(f)"]
    statement := "For every allowed input, `generated(f)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1359-1375", status := .proven
    prop := ``ExprRow1359Property, thm := some ``exprRow1359_proven },
  { id := "exprreflect-expr-row-1489", juliaFile := "base/expr.jl"
    juliaFns := ["atomic(ex)"]
    statement := "For every allowed input, `atomic(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1489-1494", status := .proven
    prop := ``ExprRow1489Property, thm := some ``exprRow1489_proven },
  { id := "exprreflect-expr-row-1495", juliaFile := "base/expr.jl"
    juliaFns := ["atomic(order, ex)"]
    statement := "For every allowed input, `atomic(order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1495-1498", status := .proven
    prop := ``ExprRow1495Property, thm := some ``exprRow1495_proven },
  { id := "exprreflect-expr-row-1499", juliaFile := "base/expr.jl"
    juliaFns := ["atomic(a1, op, a2)"]
    statement := "For every allowed input, `atomic(a1, op, a2)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1499-1501", status := .proven
    prop := ``ExprRow1499Property, thm := some ``exprRow1499_proven },
  { id := "exprreflect-expr-row-1502", juliaFile := "base/expr.jl"
    juliaFns := ["atomic(order, a1, op, a2)"]
    statement := "For every allowed input, `atomic(order, a1, op, a2)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1502-1505", status := .proven
    prop := ``ExprRow1502Property, thm := some ``exprRow1502_proven },
  { id := "exprreflect-expr-row-1506", juliaFile := "base/expr.jl"
    juliaFns := ["make_atomic(order, ex)"]
    statement := "For every allowed input, `make_atomic(order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1506-1554", status := .proven
    prop := ``ExprRow1506Property, thm := some ``exprRow1506_proven },
  { id := "exprreflect-expr-row-1555", juliaFile := "base/expr.jl"
    juliaFns := ["make_atomic(order, a1, op, a2)"]
    statement := "For every allowed input, `make_atomic(order, a1, op, a2)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1555-1565", status := .proven
    prop := ``ExprRow1555Property, thm := some ``exprRow1555_proven },
  { id := "exprreflect-expr-row-1615", juliaFile := "base/expr.jl"
    juliaFns := ["atomicswap(order, ex)"]
    statement := "For every allowed input, `atomicswap(order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1615-1618", status := .proven
    prop := ``ExprRow1615Property, thm := some ``exprRow1615_proven },
  { id := "exprreflect-expr-row-1619", juliaFile := "base/expr.jl"
    juliaFns := ["atomicswap(ex)"]
    statement := "For every allowed input, `atomicswap(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1619-1621", status := .proven
    prop := ``ExprRow1619Property, thm := some ``exprRow1619_proven },
  { id := "exprreflect-expr-row-1622", juliaFile := "base/expr.jl"
    juliaFns := ["make_atomicswap(order, ex)"]
    statement := "For every allowed input, `make_atomicswap(order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1622-1634", status := .proven
    prop := ``ExprRow1622Property, thm := some ``exprRow1622_proven },
  { id := "exprreflect-expr-row-1710", juliaFile := "base/expr.jl"
    juliaFns := ["atomicreplace(success_order, fail_order, ex, old_new)"]
    statement := "For every allowed input, `atomicreplace(success_order, fail_order, ex, old_new)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1710-1714", status := .proven
    prop := ``ExprRow1710Property, thm := some ``exprRow1710_proven },
  { id := "exprreflect-expr-row-1715", juliaFile := "base/expr.jl"
    juliaFns := ["atomicreplace(order, ex, old_new)"]
    statement := "For every allowed input, `atomicreplace(order, ex, old_new)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1715-1718", status := .proven
    prop := ``ExprRow1715Property, thm := some ``exprRow1715_proven },
  { id := "exprreflect-expr-row-1719", juliaFile := "base/expr.jl"
    juliaFns := ["atomicreplace(ex, old_new)"]
    statement := "For every allowed input, `atomicreplace(ex, old_new)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1719-1721", status := .proven
    prop := ``ExprRow1719Property, thm := some ``exprRow1719_proven },
  { id := "exprreflect-expr-row-1722", juliaFile := "base/expr.jl"
    juliaFns := ["make_atomicreplace(success_order, fail_order, ex, old_new)"]
    statement := "For every allowed input, `make_atomicreplace(success_order, fail_order, ex, old_new)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1722-1744", status := .proven
    prop := ``ExprRow1722Property, thm := some ``exprRow1722_proven },
  { id := "exprreflect-expr-row-1813", juliaFile := "base/expr.jl"
    juliaFns := ["atomiconce(success_order, fail_order, ex)"]
    statement := "For every allowed input, `atomiconce(success_order, fail_order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1813-1817", status := .proven
    prop := ``ExprRow1813Property, thm := some ``exprRow1813_proven },
  { id := "exprreflect-expr-row-1818", juliaFile := "base/expr.jl"
    juliaFns := ["atomiconce(order, ex)"]
    statement := "For every allowed input, `atomiconce(order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1818-1821", status := .proven
    prop := ``ExprRow1818Property, thm := some ``exprRow1818_proven },
  { id := "exprreflect-expr-row-1822", juliaFile := "base/expr.jl"
    juliaFns := ["atomiconce(ex)"]
    statement := "For every allowed input, `atomiconce(ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1822-1824", status := .proven
    prop := ``ExprRow1822Property, thm := some ``exprRow1822_proven },
  { id := "exprreflect-expr-row-1825", juliaFile := "base/expr.jl"
    juliaFns := ["make_atomiconce(success_order, fail_order, ex)"]
    statement := "For every allowed input, `make_atomiconce(success_order, fail_order, ex)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1825-1837", status := .proven
    prop := ``ExprRow1825Property, thm := some ``exprRow1825_proven },
  { id := "exprreflect-expr-row-1841", juliaFile := "base/expr.jl"
    juliaFns := ["is_meta_expr_head(head::Symbol)"]
    statement := "For every allowed input, `is_meta_expr_head(head::Symbol)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1841-1841", status := .proven
    prop := ``ExprRow1841Property, thm := some ``exprRow1841_proven },
  { id := "exprreflect-expr-row-1842", juliaFile := "base/expr.jl"
    juliaFns := ["is_meta_expr(@nospecialize x)"]
    statement := "For every allowed input, `is_meta_expr(@nospecialize x)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1842-1842", status := .proven
    prop := ``ExprRow1842Property, thm := some ``exprRow1842_proven },
  { id := "exprreflect-expr-row-1850", juliaFile := "base/expr.jl"
    juliaFns := ["isa_ast_node(@nospecialize x)"]
    statement := "For every allowed input, `isa_ast_node(@nospecialize x)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1850-1871", status := .proven
    prop := ``ExprRow1850Property, thm := some ``exprRow1850_proven },
  { id := "exprreflect-expr-row-1873", juliaFile := "base/expr.jl"
    juliaFns := ["is_self_quoting(@nospecialize(x))"]
    statement := "For every allowed input, `is_self_quoting(@nospecialize(x))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1873-1873", status := .proven
    prop := ``ExprRow1873Property, thm := some ``exprRow1873_proven },
  { id := "exprreflect-expr-row-1883", juliaFile := "base/expr.jl"
    juliaFns := ["quoted(@nospecialize(x))"]
    statement := "For every allowed input, `quoted(@nospecialize(x))` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1883-1883", status := .proven
    prop := ``ExprRow1883Property, thm := some ``exprRow1883_proven },
  { id := "exprreflect-expr-row-1886", juliaFile := "base/expr.jl"
    juliaFns := ["generated_body_to_codeinfo(ex::Expr, defmod::Module, isva::Bool, loc::LineNumberNode)"]
    statement := "For every allowed input, `generated_body_to_codeinfo(ex::Expr, defmod::Module, isva::Bool, loc::LineNumberNode)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1886-1911", status := .proven
    prop := ``ExprRow1886Property, thm := some ``exprRow1886_proven },
  { id := "exprreflect-expr-row-1914", juliaFile := "base/expr.jl"
    juliaFns := ["(g::Core.GeneratedFunctionStub)(world::UInt, source::Method, @nospecialize args...)"]
    statement := "For every allowed input, `(g::Core.GeneratedFunctionStub)(world::UInt, source::Method, @nospecialize args...)` follows its own source branches, checks, mutations, calls, and result construction in order."
    source := "source-body invariant; base/expr.jl:1914-1933", status := .proven
    prop := ``ExprRow1914Property, thm := some ``exprRow1914_proven }
]

end JuliaLean.ExprReflect
