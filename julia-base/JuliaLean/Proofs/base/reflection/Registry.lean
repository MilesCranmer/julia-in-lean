import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.reflection.LegacyProofs
import JuliaLean.Proofs.base.reflection.RowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesReflection : List Entry := [
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
] ++ reflectionRowEntries

end JuliaLean.ExprReflect
