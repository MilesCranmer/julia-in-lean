import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Indices read by the `n == 1` and `n < 16` branches of `_mapreduce`; the
other branches access no element at the listed sites,
`base/reduce.jl:436-455`. -/
def linearMapreduceAccesses (a : LinearArray α) : List Int :=
  match linearArrayIndices a with
  | [] => []
  | [i] => [i]
  | i :: j :: rest => if rest.length + 2 < 16 then i :: j :: rest else []

/-- Word indices computed by `_simple_count(identity, ::Array{Bool})` from
`chunks = length(x) ÷ sizeof(UInt)`, `base/reduce.jl:1097-1112`. -/
def boolWordAccesses (width : SupportedPointerWidth) (length : Nat) : List Nat :=
  oneBasedLoop (length / pointerBytes width)

/-- The short reduction reads only its computed `LinearIndices`. Every word
load covers `sizeof(UInt)` Bool bytes within the complete-word prefix. -/
def ReduceSafe : Prop :=
  (∀ (α : Type) (a : LinearArray α) i, i ∈ linearMapreduceAccesses a →
    inAxis a.first a.values.length i) ∧
  (∀ (width : SupportedPointerWidth) length i,
    i ∈ boolWordAccesses width length → i * pointerBytes width ≤ length)

private theorem linearArrayIndices_safe (a : LinearArray α) :
    ∀ i ∈ linearArrayIndices a, inAxis a.first a.values.length i := by
  intro i hi
  simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  unfold inAxis
  omega

private theorem linearMapreduceAccesses_subset (a : LinearArray α) :
    ∀ i ∈ linearMapreduceAccesses a, i ∈ linearArrayIndices a := by
  intro i hi
  unfold linearMapreduceAccesses at hi
  cases hinds : linearArrayIndices a with
  | nil => simp [hinds] at hi
  | cons first rest =>
      cases rest with
      | nil => simpa [hinds] using hi
      | cons second tail =>
          by_cases hshort : tail.length + 2 < 16
          · simpa [hinds, hshort] using hi
          · simp [hinds, hshort] at hi

theorem reduceSafe_proven : ReduceSafe := by
  constructor
  · intro α a i hi
    exact linearArrayIndices_safe a i (linearMapreduceAccesses_subset a i hi)
  · intro width length i hi
    simp only [boolWordAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨word, hword, rfl⟩ := hi
    have hdiv := Nat.mul_div_le length (pointerBytes width)
    have hmul := Nat.mul_le_mul_right (pointerBytes width) (Nat.succ_le_iff.mpr hword)
    calc
      (word + 1) * pointerBytes width ≤ (length / pointerBytes width) * pointerBytes width := hmul
      _ = pointerBytes width * (length / pointerBytes width) := Nat.mul_comm _ _
      _ ≤ length := hdiv

end JuliaLean.MemSafety.G3
