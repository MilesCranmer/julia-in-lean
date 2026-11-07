import JuliaLean.base.permuteddimsarray

/-!
`PermutedDimsArray(data, perm)` for a permutation whose entries have any `BitInteger` type.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean


/-- `PermutedDimsArray(A, perm)` accepts every permutation of `1:ndims(A)`, whatever integer type its
entries have (as `permutedims(A, perm)` does). -/
def PermutedAnyIntType : Prop :=
  ∀ (t : IntTy) (perm : List (JInt t)) (N : Nat), perm.length = N → isperm (perm.map (·.val)) = true →
    ∃ iperm, pdaNewTyped t perm N = .ok iperm

/-- `PermutedDimsArray(A, Int32[2, 1])` throws `ErrorException`. -/
theorem permutedAnyIntType_refuted : ¬ PermutedAnyIntType := by
  intro h
  obtain ⟨iperm, e⟩ := h .i32 [JInt.lit .i32 2, JInt.lit .i32 1] 2 rfl rfl
  have e2 : pdaNewTyped .i32 [JInt.lit .i32 2, JInt.lit .i32 1] 2 =
      .error (errorException "perm and iperm must both be NTuple{N,Int}") := rfl
  rw [e2] at e
  cases e

end JuliaLean.ReinterpretArrays
