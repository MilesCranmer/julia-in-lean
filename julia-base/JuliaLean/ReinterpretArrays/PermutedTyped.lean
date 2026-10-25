import JuliaLean.ReinterpretArrays.Views

/-!
`PermutedDimsArray(data, perm)` for a permutation whose entries have any `BitInteger` type.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Julia's `ErrorException` (thrown by `error(msg)`), recorded as a distinct exception message. -/
def errorException (msg : String) : JlError := .argumentError ("ErrorException: " ++ msg)

/-- `PermutedDimsArray(data, perm)`, `base/permuteddimsarray.jl:42-46`, for `perm` with entries of
integer type `t`: `(perm...,)` keeps the element type, and the inner constructor
(`base/permuteddimsarray.jl:12-17`) first requires `perm` and `iperm` to be `NTuple{N,Int}` (line 13,
`error(...)`); the remaining checks are those of `pdaNew`. -/
def pdaNewTyped (t : IntTy) (perm : List (JInt t)) (N : Nat) : Jl (List Int) := do
  if perm.length ≠ N then throw (.argumentError "not a valid permutation")
  let _ ← invperm (perm.map (·.val))
  if t ≠ .i64 then throw (errorException "perm and iperm must both be NTuple{N,Int}")
  pdaNew (perm.map (·.val)) N

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
