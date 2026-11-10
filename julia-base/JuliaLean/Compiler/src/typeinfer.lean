import JuliaLean.Compiler.src.utilities
import JuliaLean.Compiler.src.effects

/-!
The result-caching decisions of `Compiler/src/typeinfer.jl`: whether a result gets the
constant-return ABI (`is_result_constabi_eligible`, `result_is_constabi`), and whether the
optimized or inferred source is kept, dropped or compressed for the global cache
(`discard_optimized_result`, `maybe_compress_codeinfo`). Only these pure decisions are modelled,
not the rest of the file.

The interpreter hooks they call (`may_discard_trees`, `precompile_keep_ir`, `may_compress`) and the
runtime queries (`jl_generating_output`, `isa_compileable_sig(mi)`, `is_inlineable(ci)`) are
inputs.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- `InlineCostType` is `UInt16`; `MAX_INLINE_COST = typemax(InlineCostType)`
(`Compiler/src/types.jl:11-13`). -/
def MAX_INLINE_COST : Nat := 65535

/-- `is_result_constabi_eligible(result)`, on the fields it reads: `result.result` and
`result.ipo_effects`.

Julia source: Compiler/src/typeinfer.jl:483-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_result_constabi_eligible(result::InferenceResult)
    result_type = result.result
    return isa(result_type, Const) && is_foldable_nothrow(result.ipo_effects) && is_inlineable_constant(result_type.val)
end
```
-/
def isResultConstabiEligible (n : Nat) (E : CEnv) (C : ConstLayout) (resultType : LElt)
    (ipoEffects : Effects) : CM Bool := do
  let .const val := resultType | return false
  if !isFoldableNothrow ipoEffects then return false
  isInlineableConstant n E C val

/-- `result_is_constabi(interp, result)`, with `mayDiscardTrees = may_discard_trees(interp)`.

Julia source: Compiler/src/typeinfer.jl:1537-1538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_is_constabi(interp::AbstractInterpreter, result::InferenceResult) =
    may_discard_trees(interp) && is_result_constabi_eligible(result)
```
-/
def resultIsConstabi (n : Nat) (E : CEnv) (C : ConstLayout) (mayDiscardTrees : Bool)
    (resultType : LElt) (ipoEffects : Effects) : CM Bool := do
  if !mayDiscardTrees then return false
  isResultConstabiEligible n E C resultType ipoEffects

/-- `keep_source_for_output(mi)`, with `generatingOutput = jl_generating_output() != 0` and
`compileableSig = isa_compileable_sig(mi)` (only read when generating output).

Julia source: Compiler/src/typeinfer.jl:590-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A cache without native code needs the source of every compileable signature, or
# loading it means inferring them all again. Caches with native code drop it on save.
keep_source_for_output(mi::MethodInstance) =
    ccall(:jl_generating_output, Cint, ()) != 0 && isa_compileable_sig(mi)
```
-/
def keepSourceForOutput (generatingOutput : Bool) (compileableSig : Unit → Bool) : Bool :=
  generatingOutput && compileableSig ()

/-- `discard_optimized_result(interp, mi, inlining_cost)`

Julia source: Compiler/src/typeinfer.jl:582-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function discard_optimized_result(interp::AbstractInterpreter, mi::MethodInstance, inlining_cost::InlineCostType)
    may_discard_trees(interp) || return false
    inlining_cost == MAX_INLINE_COST || return false
    precompile_keep_ir(interp) && return false
    keep_source_for_output(mi) && return false
    return true
end
```
-/
def discardOptimizedResult (mayDiscardTrees precompileKeepIr generatingOutput : Bool)
    (compileableSig : Unit → Bool) (inliningCost : Nat) : Bool :=
  if !mayDiscardTrees then false
  else if inliningCost != MAX_INLINE_COST then false
  else if precompileKeepIr then false
  else if keepSourceForOutput generatingOutput compileableSig then false
  else true

/-- What `maybe_compress_codeinfo` returns: the `CodeInfo` itself, `nothing`, or the compressed
`String` (`jl_compress_ir`). -/
inductive CompressResult where
  | codeinfo
  | nothing_
  | compressed
  deriving Repr, BEq, Inhabited

/-- `maybe_compress_codeinfo(interp, mi, ci)`, with `isMethod = isa(mi.def, Method)`,
`inlineable = is_inlineable(ci)` and the interpreter hooks as inputs.

Julia source: Compiler/src/typeinfer.jl:595-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function maybe_compress_codeinfo(interp::AbstractInterpreter, mi::MethodInstance, ci::CodeInfo)
    def = mi.def
    isa(def, Method) || return ci # don't compress toplevel code
    can_discard_trees = may_discard_trees(interp)
    inlineable = is_inlineable(ci)
    if can_discard_trees && !inlineable
        # Precompile-keep-ir mode: retain non-inlineable IR as raw CodeInfo so
        # irgen's typeinf_ext can reuse it instead of re-inferring.
        # jl_finalize_precompile_inferred nulls it before save.
        precompile_keep_ir(interp) && return ci
        keep_source_for_output(mi) || return nothing
    end
    # TODO: do we want to augment edges here with any :invoke targets that we got from inlining (such that we didn't have a direct edge to it already)?
    may_compress(interp) && return ccall(:jl_compress_ir, String, (Any, Any), def, ci)
    return ci
end
```
-/
def maybeCompressCodeinfo (isMethod mayDiscardTrees inlineable precompileKeepIr generatingOutput
    mayCompress : Bool) (compileableSig : Unit → Bool) : CompressResult := Id.run do
  if !isMethod then return .codeinfo
  let canDiscardTrees := mayDiscardTrees
  if canDiscardTrees && !inlineable then
    if precompileKeepIr then return .codeinfo
    if !keepSourceForOutput generatingOutput compileableSig then return .nothing_
  if mayCompress then return .compressed
  return .codeinfo

end JuliaLean.Compiler
