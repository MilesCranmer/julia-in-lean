import JuliaLean.ExprReflect.ReflectionRows
import JuliaLean.Registry.Types

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def reflectionRowEntries : List Entry := [
  { id := "exprreflect-reflection-row-19", juliaFile := "base/reflection.jl"
    juliaFns := ["code_lowered(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); generated::Bool=true, debuginfo::Symbol=:default)"]
    statement := "For every allowed input, `code_lowered(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); generated::Bool=true, debuginfo::Symbol=:default)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:19-47", status := .proven
    prop := ``ReflectionRow19Property, thm := some ``reflectionRow19_proven },
  { id := "exprreflect-reflection-row-49", juliaFile := "base/reflection.jl"
    juliaFns := ["code_lowered(@nospecialize(f), @nospecialize(t=Tuple); generated::Bool=true, debuginfo::Symbol=:default)"]
    statement := "For every allowed input, `code_lowered(@nospecialize(f), @nospecialize(t=Tuple); generated::Bool=true, debuginfo::Symbol=:default)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:49-52", status := .proven
    prop := ``ReflectionRow49Property, thm := some ``reflectionRow49_proven },
  { id := "exprreflect-reflection-row-58", juliaFile := "base/reflection.jl"
    juliaFns := ["method_instances(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}), world::UInt)"]
    statement := "For every allowed input, `method_instances(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}), world::UInt)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:58-68", status := .proven
    prop := ``ReflectionRow58Property, thm := some ``reflectionRow58_proven },
  { id := "exprreflect-reflection-row-70", juliaFile := "base/reflection.jl"
    juliaFns := ["method_instances(@nospecialize(f), @nospecialize(t), world::UInt)"]
    statement := "For every allowed input, `method_instances(@nospecialize(f), @nospecialize(t), world::UInt)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:70-73", status := .proven
    prop := ``ReflectionRow70Property, thm := some ``reflectionRow70_proven },
  { id := "exprreflect-reflection-row-75", juliaFile := "base/reflection.jl"
    juliaFns := ["method_instance(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); world=Base.get_world_counter(), method_table=nothing)"]
    statement := "For every allowed input, `method_instance(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); world=Base.get_world_counter(), method_table=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:75-82", status := .proven
    prop := ``ReflectionRow75Property, thm := some ``reflectionRow75_proven },
  { id := "exprreflect-reflection-row-84", juliaFile := "base/reflection.jl"
    juliaFns := ["method_instance(@nospecialize(f), @nospecialize(t); world=Base.get_world_counter(), method_table=nothing)"]
    statement := "For every allowed input, `method_instance(@nospecialize(f), @nospecialize(t); world=Base.get_world_counter(), method_table=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:84-88", status := .proven
    prop := ``ReflectionRow84Property, thm := some ``reflectionRow84_proven },
  { id := "exprreflect-reflection-row-90", juliaFile := "base/reflection.jl"
    juliaFns := ["default_debug_info_kind()"]
    statement := "For every allowed input, `default_debug_info_kind()` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:90-90", status := .proven
    prop := ``ReflectionRow90Property, thm := some ``reflectionRow90_proven },
  { id := "exprreflect-reflection-row-201", juliaFile := "base/reflection.jl"
    juliaFns := ["CodegenParams(; track_allocations::Bool=true, code_coverage::Bool=true, prefer_specsig::Bool=false, gnu_pubnames::Bool=true, debug_info_kind::Cint = default_debug_info_kind(), debug_info_level::Cint = Cint(JLOptions().debug_level), safepoint_on_entry::Bool=true, gcstack_arg::Bool=true, use_jlplt::Bool=true, force_emit_all::Bool=false, sanitize_memory::Bool=false, sanitize_thread::Bool=false, sanitize_address::Bool=false, unique_names::Bool=false, debug_info_inline_scopes::Bool=true)"]
    statement := "For every allowed input, `CodegenParams(; track_allocations::Bool=true, code_coverage::Bool=true, prefer_specsig::Bool=false, gnu_pubnames::Bool=true, debug_info_kind::Cint = default_debug_info_kind(), debug_info_level::Cint = Cint(JLOptions().debug_level), safepoint_on_entry::Bool=true, gcstack_arg::Bool=true, use_jlplt::Bool=true, force_emit_all::Bool=false, sanitize_memory::Bool=false, sanitize_thread::Bool=false, sanitize_address::Bool=false, unique_names::Bool=false, debug_info_inline_scopes::Bool=true)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:201-217", status := .proven
    prop := ``ReflectionRow201Property, thm := some ``reflectionRow201_proven },
  { id := "exprreflect-reflection-row-224", juliaFile := "base/reflection.jl"
    juliaFns := ["EmissionParams(; emit_metadata::Bool=true)"]
    statement := "For every allowed input, `EmissionParams(; emit_metadata::Bool=true)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:224-226", status := .proven
    prop := ``ReflectionRow224Property, thm := some ``reflectionRow224_proven },
  { id := "exprreflect-reflection-row-288", juliaFile := "base/reflection.jl"
    juliaFns := ["code_typed(@nospecialize(f), @nospecialize(types=default_tt(f)); kwargs...)"]
    statement := "For every allowed input, `code_typed(@nospecialize(f), @nospecialize(types=default_tt(f)); kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:288-294", status := .proven
    prop := ``ReflectionRow288Property, thm := some ``reflectionRow288_proven },
  { id := "exprreflect-reflection-row-299", juliaFile := "base/reflection.jl"
    juliaFns := ["code_typed(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)"]
    statement := "For every allowed input, `code_typed(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:299-302", status := .proven
    prop := ``ReflectionRow299Property, thm := some ``reflectionRow299_proven },
  { id := "exprreflect-reflection-row-307", juliaFile := "base/reflection.jl"
    juliaFns := ["default_tt(@nospecialize(f))"]
    statement := "For every allowed input, `default_tt(@nospecialize(f))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:307-314", status := .proven
    prop := ``ReflectionRow307Property, thm := some ``reflectionRow307_proven },
  { id := "exprreflect-reflection-row-316", juliaFile := "base/reflection.jl"
    juliaFns := ["raise_match_failure(name::Symbol, @nospecialize(tt))"]
    statement := "For every allowed input, `raise_match_failure(name::Symbol, @nospecialize(tt))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:316-320", status := .proven
    prop := ``ReflectionRow316Property, thm := some ``reflectionRow316_proven },
  { id := "exprreflect-reflection-row-324", juliaFile := "base/reflection.jl"
    juliaFns := ["invoke_in_typeinf_world(args...)"]
    statement := "For every allowed input, `invoke_in_typeinf_world(args...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:324-327", status := .proven
    prop := ``ReflectionRow324Property, thm := some ``reflectionRow324_proven },
  { id := "exprreflect-reflection-row-329", juliaFile := "base/reflection.jl"
    juliaFns := ["invoke_default_compiler(fname::Symbol, args...)"]
    statement := "For every allowed input, `invoke_default_compiler(fname::Symbol, args...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:329-335", status := .proven
    prop := ``ReflectionRow329Property, thm := some ``reflectionRow329_proven },
  { id := "exprreflect-reflection-row-337", juliaFile := "base/reflection.jl"
    juliaFns := ["invoke_interp_compiler(interp, fname::Symbol, args...)"]
    statement := "For every allowed input, `invoke_interp_compiler(interp, fname::Symbol, args...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:337-350", status := .proven
    prop := ``ReflectionRow337Property, thm := some ``reflectionRow337_proven },
  { id := "exprreflect-reflection-row-352", juliaFile := "base/reflection.jl"
    juliaFns := ["invoke_mt_compiler(mt, fname::Symbol, args...)"]
    statement := "For every allowed input, `invoke_mt_compiler(mt, fname::Symbol, args...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:352-365", status := .proven
    prop := ``ReflectionRow352Property, thm := some ``reflectionRow352_proven },
  { id := "exprreflect-reflection-row-373", juliaFile := "base/reflection.jl"
    juliaFns := ["code_typed_by_type(@nospecialize(tt::Type); optimize::Bool=true, debuginfo::Symbol=:default, world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `code_typed_by_type(@nospecialize(tt::Type); optimize::Bool=true, debuginfo::Symbol=:default, world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:373-405", status := .proven
    prop := ``ReflectionRow373Property, thm := some ``reflectionRow373_proven },
  { id := "exprreflect-reflection-row-407", juliaFile := "base/reflection.jl"
    juliaFns := ["get_oc_code_rt(passed_interp, oc::Core.OpaqueClosure, types, optimize::Bool)"]
    statement := "For every allowed input, `get_oc_code_rt(passed_interp, oc::Core.OpaqueClosure, types, optimize::Bool)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:407-436", status := .proven
    prop := ``ReflectionRow407Property, thm := some ``reflectionRow407_proven },
  { id := "exprreflect-reflection-row-438", juliaFile := "base/reflection.jl"
    juliaFns := ["code_typed_opaque_closure(oc::Core.OpaqueClosure, types; debuginfo::Symbol=:default, optimize::Bool=true, interp=nothing, _...)"]
    statement := "For every allowed input, `code_typed_opaque_closure(oc::Core.OpaqueClosure, types; debuginfo::Symbol=:default, optimize::Bool=true, interp=nothing, _...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:438-447", status := .proven
    prop := ``ReflectionRow438Property, thm := some ``reflectionRow438_proven },
  { id := "exprreflect-reflection-row-492", juliaFile := "base/reflection.jl"
    juliaFns := ["code_ircode(@nospecialize(f), @nospecialize(types = default_tt(f)); kwargs...)"]
    statement := "For every allowed input, `code_ircode(@nospecialize(f), @nospecialize(types = default_tt(f)); kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:492-498", status := .proven
    prop := ``ReflectionRow492Property, thm := some ``reflectionRow492_proven },
  { id := "exprreflect-reflection-row-500", juliaFile := "base/reflection.jl"
    juliaFns := ["code_ircode(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)"]
    statement := "For every allowed input, `code_ircode(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:500-503", status := .proven
    prop := ``ReflectionRow500Property, thm := some ``reflectionRow500_proven },
  { id := "exprreflect-reflection-row-511", juliaFile := "base/reflection.jl"
    juliaFns := ["code_ircode_by_type( @nospecialize(tt::Type); world::UInt=get_world_counter(), interp=nothing, optimize_until::Union{Int,String,Nothing}=nothing, )"]
    statement := "For every allowed input, `code_ircode_by_type( @nospecialize(tt::Type); world::UInt=get_world_counter(), interp=nothing, optimize_until::Union{Int,String,Nothing}=nothing, )` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:511-535", status := .proven
    prop := ``ReflectionRow511Property, thm := some ``reflectionRow511_proven },
  { id := "exprreflect-reflection-row-537", juliaFile := "base/reflection.jl"
    juliaFns := ["_builtin_return_type(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))"]
    statement := "For every allowed input, `_builtin_return_type(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:537-542", status := .proven
    prop := ``ReflectionRow537Property, thm := some ``reflectionRow537_proven },
  { id := "exprreflect-reflection-row-544", juliaFile := "base/reflection.jl"
    juliaFns := ["_builtin_effects(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))"]
    statement := "For every allowed input, `_builtin_effects(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:544-551", status := .proven
    prop := ``ReflectionRow544Property, thm := some ``reflectionRow544_proven },
  { id := "exprreflect-reflection-row-553", juliaFile := "base/reflection.jl"
    juliaFns := ["_builtin_exception_type(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))"]
    statement := "For every allowed input, `_builtin_exception_type(passed_interp, interp, @nospecialize(f::Core.Builtin), @nospecialize(types))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:553-557", status := .proven
    prop := ``ReflectionRow553Property, thm := some ``reflectionRow553_proven },
  { id := "exprreflect-reflection-row-559", juliaFile := "base/reflection.jl"
    juliaFns := ["check_generated_context(world::UInt)"]
    statement := "For every allowed input, `check_generated_context(world::UInt)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:559-561", status := .proven
    prop := ``ReflectionRow559Property, thm := some ``reflectionRow559_proven },
  { id := "exprreflect-reflection-row-610", juliaFile := "base/reflection.jl"
    juliaFns := ["return_types(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `return_types(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:610-631", status := .proven
    prop := ``ReflectionRow610Property, thm := some ``reflectionRow610_proven },
  { id := "exprreflect-reflection-row-680", juliaFile := "base/reflection.jl"
    juliaFns := ["infer_return_type(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `infer_return_type(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:680-700", status := .proven
    prop := ``ReflectionRow680Property, thm := some ``reflectionRow680_proven },
  { id := "exprreflect-reflection-row-752", juliaFile := "base/reflection.jl"
    juliaFns := ["infer_exception_types(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `infer_exception_types(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:752-777", status := .proven
    prop := ``ReflectionRow752Property, thm := some ``reflectionRow752_proven },
  { id := "exprreflect-reflection-row-830", juliaFile := "base/reflection.jl"
    juliaFns := ["infer_exception_type(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `infer_exception_type(@nospecialize(f), @nospecialize(types=default_tt(f)); world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:830-845", status := .proven
    prop := ``ReflectionRow830Property, thm := some ``reflectionRow830_proven },
  { id := "exprreflect-reflection-row-908", juliaFile := "base/reflection.jl"
    juliaFns := ["infer_effects(@nospecialize(f), @nospecialize(types=default_tt(f)); optimize::Bool=true, world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `infer_effects(@nospecialize(f), @nospecialize(types=default_tt(f)); optimize::Bool=true, world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:908-922", status := .proven
    prop := ``ReflectionRow908Property, thm := some ``reflectionRow908_proven },
  { id := "exprreflect-reflection-row-930", juliaFile := "base/reflection.jl"
    juliaFns := ["print_statement_costs(io::IO, @nospecialize(f), @nospecialize(t); kwargs...)"]
    statement := "For every allowed input, `print_statement_costs(io::IO, @nospecialize(f), @nospecialize(t); kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:930-933", status := .proven
    prop := ``ReflectionRow930Property, thm := some ``reflectionRow930_proven },
  { id := "exprreflect-reflection-row-935", juliaFile := "base/reflection.jl"
    juliaFns := ["print_statement_costs(io::IO, @nospecialize(tt::Type); world::UInt=get_world_counter(), interp=nothing)"]
    statement := "For every allowed input, `print_statement_costs(io::IO, @nospecialize(tt::Type); world::UInt=get_world_counter(), interp=nothing)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:935-964", status := .proven
    prop := ``ReflectionRow935Property, thm := some ``reflectionRow935_proven },
  { id := "exprreflect-reflection-row-966", juliaFile := "base/reflection.jl"
    juliaFns := ["print_statement_costs(args...; kwargs...)"]
    statement := "For every allowed input, `print_statement_costs(args...; kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:966-966", status := .proven
    prop := ``ReflectionRow966Property, thm := some ``reflectionRow966_proven },
  { id := "exprreflect-reflection-row-968", juliaFile := "base/reflection.jl"
    juliaFns := ["_which(@nospecialize(tt::Type); method_table #=::Union{Nothing,Core.MethodTable,Compiler.MethodTableView}=# =nothing, world::UInt=get_world_counter(), raise::Bool=true)"]
    statement := "Generated-function reflection fails; a missing lookup reports failure or nothing, a MethodMatch is returned, and a wrongly typed compiler result raises TypeError."
    source := "source-body invariant; base/reflection.jl:968-979", status := .proven
    prop := ``ReflectionRow968Property, thm := some ``reflectionRow968_proven },
  { id := "exprreflect-reflection-row-990", juliaFile := "base/reflection.jl"
    juliaFns := ["which(@nospecialize(f), @nospecialize(t))"]
    statement := "For every allowed input, `which(@nospecialize(f), @nospecialize(t))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:990-1003", status := .proven
    prop := ``ReflectionRow990Property, thm := some ``reflectionRow990_proven },
  { id := "exprreflect-reflection-row-1010", juliaFile := "base/reflection.jl"
    juliaFns := ["which(@nospecialize(tt#=::Type=#))"]
    statement := "For every allowed input, `which(@nospecialize(tt#=::Type=#))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1010-1012", status := .proven
    prop := ``ReflectionRow1010Property, thm := some ``reflectionRow1010_proven },
  { id := "exprreflect-reflection-row-1013", juliaFile := "base/reflection.jl"
    juliaFns := ["which(@nospecialize(argtypes::Tuple))"]
    statement := "For every allowed input, `which(@nospecialize(argtypes::Tuple))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1013-1013", status := .proven
    prop := ``ReflectionRow1013Property, thm := some ``reflectionRow1013_proven },
  { id := "exprreflect-reflection-row-1020", juliaFile := "base/reflection.jl"
    juliaFns := ["which(mdl::Module, symbol::Symbol)"]
    statement := "A defined global binding returns its owner; an undefined global binding raises an error."
    source := "source-body invariant; base/reflection.jl:1020-1025", status := .proven
    prop := ``ReflectionRow1020Property, thm := some ``reflectionRow1020_proven },
  { id := "exprreflect-reflection-row-1036", juliaFile := "base/reflection.jl"
    juliaFns := ["nameof(f::Function)"]
    statement := "For every allowed input, `nameof(f::Function)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1036-1038", status := .proven
    prop := ``ReflectionRow1036Property, thm := some ``reflectionRow1036_proven },
  { id := "exprreflect-reflection-row-1040", juliaFile := "base/reflection.jl"
    juliaFns := ["nameof(f::Core.IntrinsicFunction)"]
    statement := "For every allowed input, `nameof(f::Core.IntrinsicFunction)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1040-1043", status := .proven
    prop := ``ReflectionRow1040Property, thm := some ``reflectionRow1040_proven },
  { id := "exprreflect-reflection-row-1051", juliaFile := "base/reflection.jl"
    juliaFns := ["parentmodule(f::Function)"]
    statement := "For every allowed input, `parentmodule(f::Function)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1051-1051", status := .proven
    prop := ``ReflectionRow1051Property, thm := some ``reflectionRow1051_proven },
  { id := "exprreflect-reflection-row-1059", juliaFile := "base/reflection.jl"
    juliaFns := ["parentmodule(@nospecialize(f), @nospecialize(types))"]
    statement := "For every allowed input, `parentmodule(@nospecialize(f), @nospecialize(types))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1059-1065", status := .proven
    prop := ``ReflectionRow1059Property, thm := some ``reflectionRow1059_proven },
  { id := "exprreflect-reflection-row-1075", juliaFile := "base/reflection.jl"
    juliaFns := ["parentmodule(m::Method)"]
    statement := "For every allowed input, `parentmodule(m::Method)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1075-1075", status := .proven
    prop := ``ReflectionRow1075Property, thm := some ``reflectionRow1075_proven },
  { id := "exprreflect-reflection-row-1113", juliaFile := "base/reflection.jl"
    juliaFns := ["hasmethod(@nospecialize(f), @nospecialize(t))"]
    statement := "For every allowed input, `hasmethod(@nospecialize(f), @nospecialize(t))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1113-1115", status := .proven
    prop := ``ReflectionRow1113Property, thm := some ``reflectionRow1113_proven },
  { id := "exprreflect-reflection-row-1117", juliaFile := "base/reflection.jl"
    juliaFns := ["Core.kwcall(kwargs::NamedTuple, ::typeof(hasmethod), @nospecialize(f), @nospecialize(t))"]
    statement := "For every allowed input, `Core.kwcall(kwargs::NamedTuple, ::typeof(hasmethod), @nospecialize(f), @nospecialize(t))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1117-1120", status := .proven
    prop := ``ReflectionRow1117Property, thm := some ``reflectionRow1117_proven },
  { id := "exprreflect-reflection-row-1122", juliaFile := "base/reflection.jl"
    juliaFns := ["hasmethod(f, t, kwnames::Tuple{Vararg{Symbol}}; world::UInt=get_world_counter())"]
    statement := "For every allowed input, `hasmethod(f, t, kwnames::Tuple{Vararg{Symbol}}; world::UInt=get_world_counter())` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1122-1139", status := .proven
    prop := ``ReflectionRow1122Property, thm := some ``reflectionRow1122_proven },
  { id := "exprreflect-reflection-row-1155", juliaFile := "base/reflection.jl"
    juliaFns := ["bodyfunction(basemethod::Method; world::UInt=get_world_counter())"]
    statement := "For every allowed input, `bodyfunction(basemethod::Method; world::UInt=get_world_counter())` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1155-1193", status := .proven
    prop := ``ReflectionRow1155Property, thm := some ``reflectionRow1155_proven },
  { id := "exprreflect-reflection-row-1229", juliaFile := "base/reflection.jl"
    juliaFns := ["isambiguous(m1::Method, m2::Method; ambiguous_bottom::Bool=false)"]
    statement := "For every allowed input, `isambiguous(m1::Method, m2::Method; ambiguous_bottom::Bool=false)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1229-1297", status := .proven
    prop := ``ReflectionRow1229Property, thm := some ``reflectionRow1229_proven },
  { id := "exprreflect-reflection-row-1233", juliaFile := "base/reflection.jl"
    juliaFns := ["inner(ti)"]
    statement := "For every allowed input, `inner(ti)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1233-1277", status := .proven
    prop := ``ReflectionRow1233Property, thm := some ``reflectionRow1233_proven },
  { id := "exprreflect-reflection-row-1249", juliaFile := "base/reflection.jl"
    juliaFns := ["involves_both(ms)"]
    statement := "For every allowed input, `involves_both(ms)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1249-1257", status := .proven
    prop := ``ReflectionRow1249Property, thm := some ``reflectionRow1249_proven },
  { id := "exprreflect-reflection-row-1345", juliaFile := "base/reflection.jl"
    juliaFns := ["invoke(ex)"]
    statement := "For every allowed input, `invoke(ex)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1345-1363", status := .proven
    prop := ``ReflectionRow1345Property, thm := some ``reflectionRow1345_proven },
  { id := "exprreflect-reflection-row-1365", juliaFile := "base/reflection.jl"
    juliaFns := ["getglobalref(gr::GlobalRef, world::UInt)"]
    statement := "For every allowed input, `getglobalref(gr::GlobalRef, world::UInt)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1365-1365", status := .proven
    prop := ``ReflectionRow1365Property, thm := some ``reflectionRow1365_proven },
  { id := "exprreflect-reflection-row-1367", juliaFile := "base/reflection.jl"
    juliaFns := ["invokelatest_gr(gr::GlobalRef, args...; kwargs...)"]
    statement := "For every allowed input, `invokelatest_gr(gr::GlobalRef, args...; kwargs...)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1367-1376", status := .proven
    prop := ``ReflectionRow1367Property, thm := some ``reflectionRow1367_proven },
  { id := "exprreflect-reflection-row-1406", juliaFile := "base/reflection.jl"
    juliaFns := ["invokelatest(ex)"]
    statement := "For every allowed input, `invokelatest(ex)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1406-1448", status := .proven
    prop := ``ReflectionRow1406Property, thm := some ``reflectionRow1406_proven },
  { id := "exprreflect-reflection-row-1450", juliaFile := "base/reflection.jl"
    juliaFns := ["destructure_callex(topmod::Module, @nospecialize(ex))"]
    statement := "For every allowed input, `destructure_callex(topmod::Module, @nospecialize(ex))` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1450-1497", status := .proven
    prop := ``ReflectionRow1450Property, thm := some ``reflectionRow1450_proven },
  { id := "exprreflect-reflection-row-1451", juliaFile := "base/reflection.jl"
    juliaFns := ["flatten(xs)"]
    statement := "For every allowed input, `flatten(xs)` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1451-1461", status := .proven
    prop := ``ReflectionRow1451Property, thm := some ``reflectionRow1451_proven },
  { id := "exprreflect-reflection-row-1506", juliaFile := "base/reflection.jl"
    juliaFns := ["drop_all_caches()"]
    statement := "For every allowed input, `drop_all_caches()` follows its own lookup, validation, compiler-dispatch, result-shaping, or macro body."
    source := "source-body invariant; base/reflection.jl:1506-1514", status := .proven
    prop := ``ReflectionRow1506Property, thm := some ``reflectionRow1506_proven }
]

end JuliaLean.ExprReflect
