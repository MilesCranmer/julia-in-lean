import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/expr.jl:45-79`: expression copies -/

def exprCopyAccesses (values : List Bool) : List Access :=
  let nvalues := values.length
  let newValuesLength := nvalues
  (oneBased nvalues).flatMap fun i =>
    ⟨nvalues, i⟩ :: if values.getD (i.toNat - 1) false then
      [⟨nvalues, i⟩, ⟨newValuesLength, i⟩]
    else []

def exprArgsAccesses (values : List Bool) : List Access :=
  (oneBased values.length).map fun i => ⟨values.length, i⟩

def ExprCopyInBounds : Prop := ∀ values,
  AllInBounds (exprCopyAccesses values) ∧ AllInBounds (exprArgsAccesses values)





theorem exprCopyInBounds : ExprCopyInBounds := by
  intro values
  constructor
  · intro access ha
    simp only [exprCopyAccesses, List.mem_flatMap] at ha
    obtain ⟨i, hi, ha⟩ := ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact oneBased_mem hi
    · split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact oneBased_mem hi
      · simp at ha
  · simpa [exprArgsAccesses] using mappedOneBased values.length

end JuliaLean.MemSafety.G2
