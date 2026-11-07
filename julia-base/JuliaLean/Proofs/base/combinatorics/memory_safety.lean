import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

private theorem matrixIndexSafe (rows cols row col : Nat) (hr : row < rows) (hc : col < cols) :
    (at0 (rows * cols) (row + rows * col)).safe := by
  simp only [Access.safe, at0]
  have h := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hc)
  rw [Nat.mul_succ] at h
  omega

/-! ## Swaps, inverse permutations, sets, and replacement -/

/-- `swapcols!`/`swaprows!`, `base/combinatorics.jl:103-123`.  The early
equal-index branch performs no access; otherwise both scalar indices are
checked before the opposite axis is traversed. -/
def swapMatrixAccesses (rows cols : Nat) (i j : Int) (columns : Bool) : List Access :=
  if i = j then []
  else
    let checkedLength := if columns then cols else rows
    let loopLength := if columns then rows else cols
    if 1 ≤ i ∧ i ≤ checkedLength ∧ 1 ≤ j ∧ j ≤ checkedLength then
      (List.range loopLength).flatMap fun k =>
        if columns then
          [at0 (rows * cols) (k + rows * (i - 1).toNat),
           at0 (rows * cols) (k + rows * (j - 1).toNat)]
        else
          [at0 (rows * cols) ((i - 1).toNat + rows * k),
           at0 (rows * cols) ((j - 1).toNat + rows * k)]
    else []

def SwapMatrixInBounds : Prop :=
  ∀ rows cols i j columns, accessesSafe (swapMatrixAccesses rows cols i j columns)

theorem swapMatrixInBounds_proven : SwapMatrixInBounds := by
  intro rows cols i j columns
  by_cases heq : i = j
  · simp [swapMatrixAccesses, heq, accessesSafe]
  · cases columns with
    | false =>
      simp only [swapMatrixAccesses, heq, Bool.false_eq_true, ↓reduceIte]
      by_cases hb : 1 ≤ i ∧ i ≤ (rows : Int) ∧ 1 ≤ j ∧ j ≤ (rows : Int)
      · rw [if_pos hb]
        intro a ha
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨k, hk, rfl | rfl⟩ := ha
        · apply matrixIndexSafe <;> omega
        · apply matrixIndexSafe <;> omega
      · rw [if_neg hb]
        simp [accessesSafe]
    | true =>
      simp only [swapMatrixAccesses, heq, ↓reduceIte]
      by_cases hb : 1 ≤ i ∧ i ≤ (cols : Int) ∧ 1 ≤ j ∧ j ≤ (cols : Int)
      · rw [if_pos hb]
        intro a ha
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨k, hk, rfl | rfl⟩ := ha
        · apply matrixIndexSafe <;> omega
        · apply matrixIndexSafe <;> omega
      · rw [if_neg hb]
        simp [accessesSafe]

private def invpermLoop (capacity : Nat) : List Int → List Nat → List Access
  | [], _ => []
  | j :: rest, seen =>
      if 1 ≤ j ∧ j ≤ capacity then
        let k := (j - 1).toNat
        at0 capacity k :: if k ∈ seen then [] else invpermLoop capacity rest (k :: seen)
      else []

/-- `invperm`, `base/combinatorics.jl:286-296`: enumeration reads each input
position, then the value is range-checked before indexing the length-sized
inverse vector. -/
def invpermAccesses (values : List Int) : List Access :=
  axisAccesses values.length ++ invpermLoop values.length values []

def InvpermInBounds : Prop := ∀ values, accessesSafe (invpermAccesses values)

private theorem invpermLoop_safe (capacity : Nat) (values : List Int) (seen : List Nat) :
    accessesSafe (invpermLoop capacity values seen) := by
  induction values generalizing seen with
  | nil => simp [invpermLoop, accessesSafe]
  | cons j rest ih =>
      simp only [invpermLoop]
      split
      · simp only [accessesSafe, List.mem_cons, forall_eq_or_imp]
        constructor
        · simp [Access.safe, at0]
          omega
        · split
          · simp [accessesSafe]
          · exact ih _
      · simp [accessesSafe]

theorem invpermInBounds_proven : InvpermInBounds := by
  intro values a ha
  simp only [invpermAccesses, List.mem_append] at ha
  rcases ha with ha | ha
  · exact axisLoopInBounds_proven values.length a ha
  · exact invpermLoop_safe values.length values [] a ha

def CombinatoricsAccessesInBounds : Prop := SwapMatrixInBounds ∧ InvpermInBounds

theorem combinatoricsAccessesInBounds_proven : CombinatoricsAccessesInBounds :=
  ⟨swapMatrixInBounds_proven, invpermInBounds_proven⟩

end JuliaLean.MemSafety.G1
