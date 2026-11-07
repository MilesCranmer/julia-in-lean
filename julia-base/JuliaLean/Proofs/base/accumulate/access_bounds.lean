import JuliaLean.Core

namespace JuliaLean.MemSafety.G5

/-- Julia's `start:start+count-1` loop, represented as zero-based offsets. -/
def offsetLoop (start count : Nat) : List Nat :=
  (List.range count).map (start + ·)

/-! ## `base/accumulate.jl` -/

/-- `_accumulate_pairwise!`, `base/accumulate.jl:7-23`. `start` is the
zero-based offset of `i1` in the checked `LinearIndices`; the recursive calls
use the source's `n >> 1`, `start+n2`, and `n-n2`. -/
def pairwiseOffsets (start n : Nat) : List Nat :=
  if n < 128 then offsetLoop start n
  else
    let n2 := n / 2
    pairwiseOffsets start n2 ++ pairwiseOffsets (start + n2) (n - n2)
termination_by n
decreasing_by all_goals omega

/-- Zero-based positions reached after the empty and singleton branches in
`accumulate_pairwise!`, lines 25-35. -/
def accumulatePairwisePositions (length : Nat) : List Nat :=
  match length with
  | 0 => []
  | 1 => [0]
  | n + 2 => 0 :: pairwiseOffsets 1 (n + 1)

/-- Actual Julia indices obtained from the checked common `LinearIndices` after
the equality check at line 27. -/
def accumulatePairwiseAccesses (input output : List Int) : List Int :=
  if input = output then
    (accumulatePairwisePositions input.length).map (input.getD · 0)
  else []

/-- `_accumulate1!`, lines 436-451: after the `LinearIndices` equality check,
the first store and the iterator visit the common index list. -/
def accumulateLinearAccesses (input output : List Int) : List Int :=
  if input = output then input else []

/-- Every unchecked offset produced by the pairwise and iterator paths belongs to
both arrays after the source equality checks. -/
def AccumulateAccessesInBounds : Prop :=
  (∀ input output index, index ∈ accumulatePairwiseAccesses input output →
    index ∈ input ∧ index ∈ output) ∧
  (∀ input output index, index ∈ accumulateLinearAccesses input output →
    index ∈ input ∧ index ∈ output)

private theorem pairwiseOffsets_safe : ∀ start n total k,
    start + n ≤ total → k ∈ pairwiseOffsets start n → k < total := by
  intro start n
  induction n using Nat.strongRecOn generalizing start with
  | ind n ih =>
    intro total k hspan hk
    rw [pairwiseOffsets] at hk
    split at hk
    · simp only [offsetLoop, List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      omega
    · simp only [List.mem_append] at hk
      rcases hk with hk | hk
      · exact ih (n / 2) (by omega) start total k (by omega) hk
      · exact ih (n - n / 2) (by omega) (start + n / 2) total k (by omega) hk

private theorem accumulatePairwisePositions_safe (length position : Nat) :
    position ∈ accumulatePairwisePositions length → position < length := by
  intro h
  cases length with
  | zero => simp [accumulatePairwisePositions] at h
  | succ n =>
    cases n with
    | zero => simp [accumulatePairwisePositions] at h; omega
    | succ n =>
      simp only [accumulatePairwisePositions, List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · exact pairwiseOffsets_safe 1 (n + 1) (n + 2) position (by omega) h

theorem accumulateAccessesInBounds : AccumulateAccessesInBounds := by
  constructor
  · intro input output index hindex
    unfold accumulatePairwiseAccesses at hindex
    split at hindex
    · rename_i heq
      subst output
      simp only [List.mem_map] at hindex
      obtain ⟨position, hp, rfl⟩ := hindex
      have hposition := accumulatePairwisePositions_safe input.length position hp
      have hmem : input.getD position 0 ∈ input := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hposition]
        exact List.getElem_mem hposition
      exact ⟨hmem, hmem⟩
    · contradiction
  · intro input output index hindex
    unfold accumulateLinearAccesses at hindex
    split at hindex
    · rename_i heq
      subst output
      exact ⟨hindex, hindex⟩
    · contradiction

/-- The selected dimension axis after `_accumulate!` has checked that input
and output axes match and that the axis is nonempty. -/
structure AccumulateDimAxis where
  indices : List (JInt .i64)

/-- The initialization access after the matching-axis and nonempty checks. -/
def accumulateDimsInitialRead (input output : AccumulateDimAxis) : Option (JInt .i64) :=
  if input.indices = output.indices then input.indices.head? else none

/-- The initial dimensional read and write use the first index of the common axis. -/
def AccumulateDimsInitialAccessesInBounds : Prop :=
  ∀ input output,
    match accumulateDimsInitialRead input output with
    | none => True
    | some index => index.val ∈ input.indices.map (·.val) ∧
      index.val ∈ output.indices.map (·.val)

theorem accumulateDimsInitialAccessesInBounds : AccumulateDimsInitialAccessesInBounds := by
  intro ⟨input⟩ ⟨output⟩
  by_cases heq : input = output
  · subst output
    cases input <;> simp [accumulateDimsInitialRead]
  · simp [accumulateDimsInitialRead, heq]

/-- The first access in the follow-up loop shared by the `dims == 1` branch
at lines 391-393 and `_accumulaten!` at lines 412-415 and 428-431. -/
def accumulateDimsNextRead (input output : AccumulateDimAxis) : Option (JInt .i64) :=
  if input.indices = output.indices then
    match input.indices with
    | [] => none
    | first :: rest =>
      let last := rest.getLastD first
      let next := first + JInt.lit .i64 1
      if next.val ≤ last.val then some next else none
  else none

/-- Every access produced after the dimensional checks is on the common axis. -/
def AccumulateDimsAccessesInBounds : Prop :=
  ∀ input output,
    match accumulateDimsNextRead input output with
    | none => True
    | some index => index.val ∈ input.indices.map (·.val) ∧
      index.val ∈ output.indices.map (·.val)

theorem accumulateDimsAccessesInBounds_refuted : ¬ AccumulateDimsAccessesInBounds := by
  intro h
  have hwrap : (JInt.typemax .i64 + JInt.lit .i64 1).val = IntTy.i64.min := by decide
  have hmax : (JInt.typemax .i64).val = IntTy.i64.max := by decide
  have bad := h ⟨[JInt.typemax .i64]⟩ ⟨[JInt.typemax .i64]⟩
  simp [accumulateDimsNextRead, hwrap, hmax, IntTy.min, IntTy.max,
    IntTy.signed, IntTy.bits] at bad


end JuliaLean.MemSafety.G5
