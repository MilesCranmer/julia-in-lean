import JuliaLean.Proofs.base.array.getindex
import JuliaLean.Proofs.base.array.deleteat_splice
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.array.LegacyRefutations
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- The get(A, I, default) index-tuple signature accepts integer index vectors as
well as ranges, so each accepted tuple should produce retained index positions. -/
def TupleVectorsReturnValues : Prop :=
  ∀ (dims : List I) (indices : List (round4.IndcopyTupleIndex (JuliaLean.base.range.UnitRange I))),
    0 < indices.length → indices.length ≤ dims.length →
    (∀ n ∈ dims, 0 ≤ n.val) → (dims.map Subtype.val).prod < 2 ^ 63 →
    ∃ result, round4.tupleIndcopy round4.unitRangeValues round4.unitRangeFindin round4.unitRangeSlice dims indices = .ok result

theorem tupleVectorsReturnValues_refuted : ¬ TupleVectorsReturnValues := by
  intro promised
  obtain ⟨result, run⟩ := promised [one] [.vector [one]] (by decide) (by decide)
    (by simp [one, JInt.wrap, wrapInt, IntTy.bits, IntTy.signed]) (by decide)
  change Except.error (JlError.methodError "indcopy") = Except.ok result at run
  cases run

/-- Keeping a valid unassigned reference slot should retain its assignment state. -/
theorem keepatAssignedState_refuted : ¬ KeepatAssignedStateSpec := by
  intro promised
  let layout := MemoryLayoutMetadata.ofRuntime JuliaLean.src.genericmemory_c.boxedDictLayout
  let initial := MutableMemory.initial ([none] : List (Option Unit))
  obtain ⟨next, run, rest⟩ :=
    (promised Unit layout initial [none] (by decide) rfl (by decide)).1
      [one] (by simp) (by simp [one, JInt.wrap, wrapInt, IntTy.bits, IntTy.signed])
  have failure : (((nativeKeepatIndices (layout := layout) 0 [one]).run).run initial).1 =
      Except.error Error.undefinedReference := rfl
  have success := congrArg Prod.fst run
  rw [failure] at success
  cases success

open JuliaLean.Registry in
def entries : List Entry := [
  { id := "multidimcov-get-tuple-vectors", juliaFile := "base/array.jl"
    juliaFns := ["indcopy(sz::Dims, I::Tuple{Vararg{RangeIndex}})",
      "get!(X::AbstractArray, A::AbstractArray, I::RangeVecIntList, default)"]
    statement := "Every nonempty tuple of integer index vectors and ranges accepted by get(A, I, default), with no more indices than dimensions, produces its source and destination index positions."
    source := "base/array.jl:2976; base/abstractarray.jl get! index-tuple signature"
    status := .refuted, prop := ``TupleVectorsReturnValues, thm := some ``tupleVectorsReturnValues_refuted
    issue := "none found (queries: indcopy; get default tuple of vectors MethodError; RangeVecIntList)"
    notes := "The native indcopy dispatcher rejects the valid tuple ([1],) with MethodError; the range-valued branch is bound to the installed range.jl methods." },
  { id := "multidimcov-keepat-undef", juliaFile := "base/array.jl"
    juliaFns := ["keepat!(a::Vector, inds)", "keepat!(a::Vector, m::AbstractVector{Bool})"]
    statement := "keepat!(a, inds) and keepat!(a, mask) retain the selected slots in order, including unassigned reference slots, and return the modified vector."
    source := "base/array.jl:3104-3154; base/abstractarray.jl _keepat!"
    status := .refuted, prop := ``JuliaLean.Proofs.base.array.KeepatAssignedStateSpec
    thm := some ``keepatAssignedState_refuted
    issue := "#54401 and #42065 related (queries: keepat! undef; keepat! UndefRefError; deleteat! keepat! undef)"
    notes := "The native source composition raises UndefRefError for a valid one-slot boxed vector whose kept slot is unassigned." }
]

end JuliaLean.Proofs.base.array.LegacyRefutations
