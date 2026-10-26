import JuliaLean.BitArrays
import JuliaLean.Channels.ThreadsFor
import JuliaLean.Reduce
import JuliaLean.Toml

/-!
# Bounds models for memory-safety group 5

The models normalize Julia's one-based array axes to a length and an index.
Arithmetic on BitSet chunk offsets remains `Int`, matching `base/bitset.jl`;
the existing `JuliaLean.BitArrays.BitSetS` model establishes why its offset
arithmetic does not wrap. Array lengths and loop offsets are `Nat` after the
enclosing Julia code has checked the axes or successfully allocated the result.
-/

namespace JuliaLean.MemSafety.G5

def OneBasedInBounds (len index : Nat) : Prop := 1 ≤ index ∧ index ≤ len
def IntInBounds (len index : Int) : Prop := 1 ≤ index ∧ index ≤ len

/-- Julia's `1:n` loop, represented as one-based indices. -/
def oneBasedLoop (n : Nat) : List Nat := (List.range n).map Nat.succ

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

/-! ## `base/bitset.jl` -/

/-- Mathematical observation of a Julia `UnitRange{Int}`. It is empty when
`last < first`, as in every BitSet loop below. -/
def intLoop (first last : Int) : List Int :=
  (List.range (last - first + 1).toNat).map (fun k : Nat => first + (k : Int))

private theorem intLoop_bounds (first last index : Int) :
    index ∈ intLoop first last → first ≤ index ∧ index ≤ last := by
  intro h
  simp only [intLoop, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  omega

structure BoundedChunkAccess where
  length : Int
  index : Int

def chunkAccessSafe (access : BoundedChunkAccess) : Prop :=
  IntInBounds access.length access.index

private def chunkLoop (length first last : Int) : List BoundedChunkAccess :=
  (intLoop first last).map (⟨length, ·⟩)

private def chunkSpan (length first count : Int) : List BoundedChunkAccess :=
  chunkLoop length first (first + count - 1)

/-- `_bits_getindex`, lines 63-68, including its computed chunk index and
guard. -/
def bitsGetindexAccesses (length : Nat) (n offset : Int) : List BoundedChunkAccess :=
  let ci := n / 64 - offset + 1
  if 1 ≤ ci ∧ ci ≤ length then [⟨length, ci⟩] else []

/-- `_growend0!` and `_growbeg0!`, lines 114-129, after the exact resize. -/
def bitsetGrowthAccesses (oldLength add : Nat) : List BoundedChunkAccess :=
  chunkLoop (oldLength + add) (oldLength + 1) (oldLength + add) ++
  chunkLoop (oldLength + add) 1 add

/-- A nonempty unit range after conversion of its endpoints to `Int`. The
ordering is the representation invariant established by `isempty(r)` at line 132. -/
structure BitSetChunkRange where
  firstElement : Int
  lastElement : Int
  ordered : firstElement ≤ lastElement

/-- The growth and writes in `union!(::BitSet, ::AbstractUnitRange)`, lines
131-165. `noOffset` identifies the empty sentinel state from lines 5-10. -/
def bitsetUnionAccesses (oldLength : Nat) (offset : Int) (range : BitSetChunkRange) :
    List BoundedChunkAccess :=
  let firstChunk := range.firstElement / 64
  let lastChunk := range.lastElement / 64
  let actualOffset := if offset = JuliaLean.BitArrays.noOffset then firstChunk else offset
  let diffFirst := firstChunk - actualOffset
  let diffLast := lastChunk - actualOffset
  let endLength : Int := if diffLast ≥ oldLength then diffLast + 1 else oldLength
  let finalLength : Int := if diffFirst < 0 then endLength - diffFirst else endLength
  let first := if diffFirst < 0 then 1 else diffFirst + 1
  let last := if diffFirst < 0 then diffLast - diffFirst + 1 else diffLast + 1
  chunkLoop finalLength first last

/-- Common overlap plus the trailing and leading growth/copy branches of the
low-level `_matched_map!`, lines 186-253. Lengths after each resize are attached
to each access; source and destination copies are both expanded. -/
def matchedMapAccesses (len1 len2 : Nat) (offset1 offset2 : Int)
    (leftFalse rightFalse : Bool) : List BoundedChunkAccess :=
  let l1 : Int := len1
  let l2 : Int := len2
  let diff := offset2 - offset1
  let end1 := l1 + offset1
  let end2 := l2 + offset2
  let endDiff := end2 - end1
  let common := (intLoop (max 1 (1 + diff)) (min l1 (l2 + diff))).flatMap fun i =>
    [⟨l1, i⟩, ⟨l2, i - diff⟩]
  let trailing := if 0 < endDiff && !leftFalse then
    let newLength := l1 + endDiff
  let updatedL1 := max l1 diff
    let count := end2 - updatedL1 - offset1
    chunkLoop newLength (l1 + 1) diff ++
      chunkSpan newLength (updatedL1 + 1) count ++
      chunkSpan l2 (l2 + 1 - count) count
    else []
  let leading := if diff < 0 && !leftFalse then
    let newLength := l1 - diff
    let count := min (-diff) l2
    chunkLoop newLength (l2 + 1) (-diff) ++
      chunkSpan newLength 1 count ++ chunkSpan l2 1 count
    else []
  let _ := rightFalse
  common ++ trailing ++ leading

/-- A reachable state supplied back to `iterate(::BitSet, state)`. Julia's
iteration protocol requires the opaque state returned by the prior call. -/
structure BitSetIteration where
  bits : List Bool
  priorIndex : Nat
  reachable : priorIndex ≤ bits.length

/-- The exact `while word == 0` loop at lines 333-338. -/
def bitsetIterationScan (bits : List Bool) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, index =>
    if index = bits.length then []
    else
      let next := index + 1
      next :: if bits.getD index false then [] else bitsetIterationScan bits fuel next

/-- The `while word == 0` reads at line 337. -/
def bitsetIterationAccesses (state : BitSetIteration) : List BoundedChunkAccess :=
  (bitsetIterationScan state.bits (state.bits.length - state.priorIndex + 1)
    state.priorIndex).map (fun i : Nat => ⟨state.bits.length, (i : Int)⟩)

private theorem bitsetIterationScan_safe (bits : List Bool) :
    ∀ fuel prior index, prior ≤ bits.length →
      index ∈ bitsetIterationScan bits fuel prior → prior < index ∧ index ≤ bits.length := by
  intro fuel
  induction fuel with
  | zero => intro; simp [bitsetIterationScan]
  | succ fuel ih =>
    intro prior index hp h
    simp only [bitsetIterationScan] at h
    split at h
    · contradiction
    · rename_i hne
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · split at h
        · contradiction
        · have hs := ih (prior + 1) index (by omega) h
          omega

/-- Equality's `_check0` calls after the source swap has established
`offset1 ≤ offset2`, lines 375-405. -/
def bitsetEqualityCheck0Accesses (len1 len2 : Nat) (offset1 offset2 : Int) :
    List BoundedChunkAccess :=
  let l1 : Int := len1
  let l2 : Int := len2
  let shift := offset2 - offset1
  let overlap0 := max 0 (l1 - shift)
  let included := l2 ≤ overlap0
  chunkLoop l1 1 (l1 - overlap0) ++
    if included then chunkLoop l1 (shift + l2 + 1) l1
    else chunkLoop l2 (1 + overlap0) l2

/-- `_check0` callers in `isempty` and equality, including equality's operand
swap. The first span is `isempty(s)` at line 291. -/
def bitsetCheck0Accesses (len1 len2 : Nat) (offset1 offset2 : Int) :
    List BoundedChunkAccess :=
  chunkLoop len1 1 len1 ++
    if offset1 ≤ offset2 then bitsetEqualityCheck0Accesses len1 len2 offset1 offset2
    else bitsetEqualityCheck0Accesses len2 len1 offset2 offset1

/-- The three generator ranges in `issubset`, lines 409-418. -/
def bitsetIssubsetAccesses (len1 len2 : Nat) (offset1 offset2 : Int) :
    List BoundedChunkAccess :=
  let n : Int := len1
  let other : Int := len2
  let shift := offset2 - offset1
  let j := shift + other
  let leading := chunkLoop n 1 (min n shift)
  let common := (intLoop (max 1 (shift + 1)) (min n j)).flatMap fun i =>
    [⟨n, i⟩, ⟨other, i - shift⟩]
  let trailing := chunkLoop n (max 1 (j + 1)) n
  leading ++ common ++ trailing

/-- Every unchecked chunk index computed by the BitSet functions in this group
is within the vector length in force at that statement. -/
def BitSetAccessesInBounds : Prop :=
  (∀ length n offset access, access ∈ bitsGetindexAccesses length n offset →
    chunkAccessSafe access) ∧
  (∀ oldLength add access, access ∈ bitsetGrowthAccesses oldLength add →
    chunkAccessSafe access) ∧
  (∀ oldLength offset range access, access ∈ bitsetUnionAccesses oldLength offset range →
    chunkAccessSafe access) ∧
  (∀ len1 len2 offset1 offset2 leftFalse rightFalse access,
    access ∈ matchedMapAccesses len1 len2 offset1 offset2 leftFalse rightFalse →
    chunkAccessSafe access) ∧
  (∀ state access, access ∈ bitsetIterationAccesses state → chunkAccessSafe access) ∧
  (∀ len1 len2 offset1 offset2 access,
    access ∈ bitsetCheck0Accesses len1 len2 offset1 offset2 →
    chunkAccessSafe access) ∧
  (∀ len1 len2 offset1 offset2 access,
    access ∈ bitsetIssubsetAccesses len1 len2 offset1 offset2 → chunkAccessSafe access)

private theorem chunkLoop_safe (length first last : Int) (access : BoundedChunkAccess) :
    access ∈ chunkLoop length first last → 1 ≤ first → last ≤ length →
      chunkAccessSafe access := by
  intro h hfirst hlast
  simp only [chunkLoop, List.mem_map] at h
  obtain ⟨index, hi, rfl⟩ := h
  have hb := intLoop_bounds first last index hi
  simp only [chunkAccessSafe, IntInBounds]
  exact ⟨by omega, by omega⟩

private theorem chunkSpan_safe (length first count : Int) (access : BoundedChunkAccess) :
    access ∈ chunkSpan length first count → 1 ≤ first → 0 ≤ count →
      first + count - 1 ≤ length → chunkAccessSafe access := by
  intro h hfirst hcount hlast
  exact chunkLoop_safe length first (first + count - 1) access h hfirst hlast

private theorem bitsetEqualityCheck0Accesses_safe (len1 len2 : Nat)
    (offset1 offset2 : Int) (horder : offset1 ≤ offset2) (access : BoundedChunkAccess) :
    access ∈ bitsetEqualityCheck0Accesses len1 len2 offset1 offset2 →
      chunkAccessSafe access := by
  intro h
  unfold bitsetEqualityCheck0Accesses at h
  simp only [List.mem_append] at h
  have hover0 : 0 ≤ max 0 ((len1 : Int) - (offset2 - offset1)) := by
    simp only [Int.max_def]
    split <;> omega
  have hover1 : max 0 ((len1 : Int) - (offset2 - offset1)) ≤ (len1 : Int) := by
    simp only [Int.max_def]
    split <;> omega
  rcases h with h | h
  · apply chunkLoop_safe _ _ _ access h <;> omega
  · split at h
    · apply chunkLoop_safe _ _ _ access h <;> omega
    · apply chunkLoop_safe _ _ _ access h <;> omega

theorem bitSetAccessesInBounds : BitSetAccessesInBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro length n offset access h
    simp only [bitsGetindexAccesses] at h
    split at h
    · rename_i bounds
      simp at h
      subst access
      exact bounds
    · contradiction
  · intro oldLength add access h
    simp only [bitsetGrowthAccesses, List.mem_append] at h
    rcases h with h | h
    · exact chunkLoop_safe _ _ _ access h (by omega) (by omega)
    · exact chunkLoop_safe _ _ _ access h (by omega) (by omega)
  · intro oldLength offset range access h
    simp only [bitsetUnionAccesses] at h
    repeat' first | split at h
    all_goals
      apply chunkLoop_safe _ _ _ access h <;>
      have ho := Int.ediv_le_ediv (by omega : (0 : Int) < 64) range.ordered <;> omega
  · intro len1 len2 offset1 offset2 leftFalse rightFalse access h
    unfold matchedMapAccesses at h
    simp only [List.mem_append] at h
    rcases h with h | h
    · rcases h with h | h
      · simp only [List.mem_flatMap] at h
        obtain ⟨i, hi, h⟩ := h
        have hb := intLoop_bounds _ _ i hi
        simp only [List.mem_cons] at h
        rcases h with rfl | rfl | h
        · simp only [chunkAccessSafe, IntInBounds]
          exact ⟨by omega, by omega⟩
        · simp only [chunkAccessSafe, IntInBounds]
          exact ⟨by omega, by omega⟩
        · contradiction
      · split at h
        · rename_i htrail
          simp at htrail
          have hmax1 : (len1 : Int) ≤ max (len1 : Int) (offset2 - offset1) := by
            simp only [Int.max_def]
            split <;> omega
          have hmax2 : offset2 - offset1 ≤ max (len1 : Int) (offset2 - offset1) := by
            simp only [Int.max_def]
            split <;> omega
          simp only [List.mem_append] at h
          rcases h with h | h
          · rcases h with h | h
            · apply chunkLoop_safe _ _ _ access h <;> omega
            · apply chunkSpan_safe _ _ _ access h <;> omega
          · apply chunkSpan_safe _ _ _ access h <;> omega
        · contradiction
    · split at h
      · rename_i hleading
        simp at hleading
        have hmin1 : min (-(offset2 - offset1)) (len2 : Int) ≤ -(offset2 - offset1) := by
          simp only [Int.min_def]
          split <;> omega
        have hmin2 : min (-(offset2 - offset1)) (len2 : Int) ≤ (len2 : Int) := by
          simp only [Int.min_def]
          split <;> omega
        have hmin0 : 0 ≤ min (-(offset2 - offset1)) (len2 : Int) := by
          simp only [Int.min_def]
          split <;> omega
        simp only [List.mem_append] at h
        rcases h with h | h
        · rcases h with h | h
          · apply chunkLoop_safe _ _ _ access h <;> omega
          · apply chunkSpan_safe _ _ _ access h <;> omega
        · apply chunkSpan_safe _ _ _ access h <;> omega
      · contradiction
  · intro state access h
    simp only [bitsetIterationAccesses, List.mem_map] at h
    obtain ⟨index, hi, rfl⟩ := h
    have hb := bitsetIterationScan_safe state.bits
      (state.bits.length - state.priorIndex + 1) state.priorIndex index state.reachable hi
    simp only [chunkAccessSafe, IntInBounds]
    omega
  · intro len1 len2 offset1 offset2 access h
    unfold bitsetCheck0Accesses at h
    simp only [List.mem_append] at h
    rcases h with h | h
    · apply chunkLoop_safe _ _ _ access h <;> omega
    · split at h
      · rename_i horder
        exact bitsetEqualityCheck0Accesses_safe len1 len2 offset1 offset2 horder access h
      · rename_i horder
        exact bitsetEqualityCheck0Accesses_safe len2 len1 offset2 offset1 (by omega) access h
  · intro len1 len2 offset1 offset2 access h
    unfold bitsetIssubsetAccesses at h
    simp only [List.mem_append] at h
    rcases h with h | h
    · rcases h with h | h
      · apply chunkLoop_safe _ _ _ access h <;> omega
      · simp only [List.mem_flatMap] at h
        obtain ⟨i, hi, h⟩ := h
        have hb := intLoop_bounds _ _ i hi
        simp only [List.mem_cons] at h
        rcases h with rfl | rfl | h
        · simp only [chunkAccessSafe, IntInBounds]
          exact ⟨by omega, by omega⟩
        · simp only [chunkAccessSafe, IntInBounds]
          exact ⟨by omega, by omega⟩
        · contradiction
    · apply chunkLoop_safe _ _ _ access h <;> omega

/-! ## generated default constructors in `base/essentials.jl` -/

/-- Inputs that affect control flow in `_fieldtypes_constrain_typevars` and
`_defaultctors`. `isAny` also represents the DataType invariant that `names`
and `fts` have the same field count. -/
structure DefaultCtorInput where
  typevars : List Nat
  isAny : List Bool
  hasFieldTypevar : Nat → Nat → Bool
  hasUpperTypevar : Nat → Nat → Bool
  sameTypevar : Nat → Nat → Bool

/-- A checked while scan with a break. `step j = some result` stops at `j`;
`none` advances exactly as the source loops do. -/
def scanUntilResult (start : Nat) : Nat → (Nat → Option Bool) → List Nat × Bool
  | 0, _ => ([], false)
  | count + 1, step =>
    match step start with
    | some result => ([start], result)
    | none =>
      let rest := scanUntilResult (start + 1) count step
      (start :: rest.1, rest.2)

inductive CtorSourceAccess where
  | typevar (index : Nat)
  | fieldtype (index : Nat)

/-- The outer reverse loop and its two inner scans at essentials.jl:1292-1327.
The returned Boolean is the source function's return value. -/
def fieldtypesConstrainLoop (input : DefaultCtorInput) : Nat → Nat →
    List CtorSourceAccess × Bool
  | 0, _ => ([], true)
  | _ + 1, 0 => ([], true)
  | fuel + 1, i + 1 =>
    let fieldScan := scanUntilResult 1 input.isAny.length fun j =>
      if input.hasFieldTypevar (i + 1) j then some true else none
    let current := .typevar (i + 1) :: fieldScan.1.map .fieldtype
    if fieldScan.2 then
      let rest := fieldtypesConstrainLoop input fuel i
      (current ++ rest.1, rest.2)
    else
      let upperScan := scanUntilResult (i + 2) (input.typevars.length - (i + 1)) fun j =>
        if input.hasUpperTypevar (i + 1) j then some true
        else if input.sameTypevar (i + 1) j then some false
        else none
      if upperScan.2 then
        let rest := fieldtypesConstrainLoop input fuel i
        (current ++ upperScan.1.map .typevar ++ rest.1, rest.2)
      else (current ++ upperScan.1.map .typevar, false)

def fieldtypesConstrain (input : DefaultCtorInput) : List CtorSourceAccess × Bool :=
  fieldtypesConstrainLoop input input.typevars.length input.typevars.length

private theorem scanUntilResult_safe : ∀ start count step index,
    index ∈ (scanUntilResult start count step).1 → start ≤ index ∧ index < start + count := by
  intro start count
  induction count generalizing start with
  | zero => intro; simp [scanUntilResult]
  | succ count ih =>
    intro step index h
    simp only [scanUntilResult] at h
    split at h
    · simp at h
      omega
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · have hs := ih (start + 1) step index h
        omega

private theorem fieldtypesConstrainLoop_safe (input : DefaultCtorInput) :
    ∀ fuel i access, i ≤ input.typevars.length →
      access ∈ (fieldtypesConstrainLoop input fuel i).1 →
      match access with
      | .typevar j => OneBasedInBounds input.typevars.length j
      | .fieldtype j => OneBasedInBounds input.isAny.length j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [fieldtypesConstrainLoop]
  | succ fuel ih =>
    intro i access hi hmem
    cases i with
    | zero => simp [fieldtypesConstrainLoop] at hmem
    | succ i =>
      simp only [fieldtypesConstrainLoop] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
        rcases hmem with (rfl | ⟨j, hj, rfl⟩) | hmem
        · exact ⟨by omega, hi⟩
        · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
          exact ⟨by omega, by omega⟩
        · exact ih i access (by omega) hmem
      · split at hmem
        · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
          rcases hmem with ((rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | hmem
          · exact ⟨by omega, hi⟩
          · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
            exact ⟨by omega, by omega⟩
          · have hs := scanUntilResult_safe (i + 2)
                (input.typevars.length - (i + 1)) _ j hj
            exact ⟨by omega, by omega⟩
          · exact ih i access (by omega) hmem
        · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
          rcases hmem with (rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
          · exact ⟨by omega, hi⟩
          · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
            exact ⟨by omega, by omega⟩
          · have hs := scanUntilResult_safe (i + 2)
                (input.typevars.length - (i + 1)) _ j hj
            exact ⟨by omega, by omega⟩

/-- Accesses emitted by one pass over the fields for the inner constructor.
`bodyIndex` is the source's `bidx`; it advances by two only for non-`Any` fields. -/
def innerBodyIndices : List Bool → Nat → List Nat
  | [], _ => []
  | isAny :: rest, bodyIndex =>
    if isAny then innerBodyIndices rest bodyIndex
    else bodyIndex :: (bodyIndex + 1) :: innerBodyIndices rest (bodyIndex + 2)

private theorem innerBodyIndices_safe : ∀ fields bodyIndex index,
    index ∈ innerBodyIndices fields bodyIndex →
      bodyIndex ≤ index ∧ index < bodyIndex + 2 * fields.count false := by
  intro fields
  induction fields with
  | nil => intro; simp [innerBodyIndices]
  | cons isAny rest ih =>
    intro bodyIndex index h
    cases isAny
    · simp only [innerBodyIndices, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · simp <;> omega
      · simp <;> omega
      · have hs := ih (bodyIndex + 2) index h
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
        omega
    · simp only [innerBodyIndices, ↓reduceIte] at h
      have hs := ih bodyIndex index h
      simpa using hs

inductive CtorBuffer where
  | tvars | names | fields | argnames | curlyArgs | outerNewArgs | innerNewArgs
  | atypes | bodyArgs | innerAtypes
  deriving DecidableEq

structure CtorAccess where
  buffer : CtorBuffer
  index : Nat

def ctorBufferLength (input : DefaultCtorInput) : CtorBuffer → Nat
  | .tvars => input.typevars.length
  | .names | .fields | .innerNewArgs => input.isAny.length
  | .argnames | .outerNewArgs | .atypes | .innerAtypes => input.isAny.length + 1
  | .curlyArgs => input.typevars.length + 1
  | .bodyArgs => 2 * input.isAny.count false + 1

private def tagged (buffer : CtorBuffer) (indices : List Nat) : List CtorAccess :=
  indices.map (⟨buffer, ·⟩)

/-- All unchecked accesses in `_defaultctor_typeinfo` and `_defaultctors`,
including the constraint-result branch, parametric branch, all-Any early return,
field loop, `bidx` updates, reverse typevar loop, and exact allocation sizes. -/
def defaultCtorAccesses (input : DefaultCtorInput) : List CtorAccess :=
  let nparams := input.typevars.length
  let n := input.isAny.length
  let constrain := fieldtypesConstrain input
  let sourceReads := constrain.1.map fun access => match access with
    | .typevar i => ⟨.tvars, i⟩
    | .fieldtype i => ⟨.fields, i⟩
  let typeInfo := tagged .tvars (oneBasedLoop nparams)
  let fieldLoop := tagged .names (oneBasedLoop n) ++ tagged .fields (oneBasedLoop n) ++
    tagged .argnames (1 :: (oneBasedLoop n).map (· + 1))
  let outer := if constrain.2 then
      (if nparams = 0 then [] else tagged .curlyArgs (1 :: (oneBasedLoop nparams).map (· + 1))) ++
      tagged .outerNewArgs (1 :: (oneBasedLoop n).map (· + 1)) ++
      tagged .atypes (1 :: (oneBasedLoop n).map (· + 1))
    else []
  let earlyReturn := constrain.2 && nparams = 0 && input.isAny.all id
  let inner := if earlyReturn then [] else
    tagged .innerNewArgs (oneBasedLoop n) ++
    tagged .bodyArgs (innerBodyIndices input.isAny 1) ++
    tagged .tvars (oneBasedLoop nparams).reverse ++
    tagged .innerAtypes (1 :: (oneBasedLoop n).map (· + 1))
  sourceReads ++ typeInfo ++ fieldLoop ++ outer ++ inner

def DefaultCtorAccessesInBounds : Prop :=
  ∀ input access, access ∈ defaultCtorAccesses input →
    OneBasedInBounds (ctorBufferLength input access.buffer) access.index

private theorem oneBasedLoop_safe (n index : Nat) :
    index ∈ oneBasedLoop n → OneBasedInBounds n index := by
  intro h
  simp only [oneBasedLoop, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨by omega, by omega⟩

private theorem shiftedLoop_safe (n index : Nat) :
    index ∈ 1 :: (oneBasedLoop n).map (· + 1) → OneBasedInBounds (n + 1) index := by
  intro h
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨i, hi, rfl⟩
  · simp [OneBasedInBounds]
  · have hs := oneBasedLoop_safe n i hi
    simp only [OneBasedInBounds] at hs ⊢
    omega

/-- A branch-free superset of `defaultCtorAccesses`; it keeps every possible
constructor-generation branch while preserving each source-computed index. -/
private def defaultCtorAllAccesses (input : DefaultCtorInput) : List CtorAccess :=
  let nparams := input.typevars.length
  let n := input.isAny.length
  let sourceReads := (fieldtypesConstrain input).1.map fun access => match access with
    | .typevar i => ⟨.tvars, i⟩
    | .fieldtype i => ⟨.fields, i⟩
  sourceReads ++
    (tagged .tvars (oneBasedLoop nparams) ++
    (tagged .names (oneBasedLoop n) ++
    (tagged .fields (oneBasedLoop n) ++
    (tagged .argnames (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .curlyArgs (1 :: (oneBasedLoop nparams).map (· + 1)) ++
    (tagged .outerNewArgs (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .atypes (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .innerNewArgs (oneBasedLoop n) ++
    (tagged .bodyArgs (innerBodyIndices input.isAny 1) ++
    (tagged .tvars (oneBasedLoop nparams).reverse ++
      tagged .innerAtypes (1 :: (oneBasedLoop n).map (· + 1))))))))))))

private theorem defaultCtorAccesses_subset (input : DefaultCtorInput) (access : CtorAccess) :
    access ∈ defaultCtorAccesses input → access ∈ defaultCtorAllAccesses input := by
  intro h
  by_cases hc : (fieldtypesConstrain input).2
  · by_cases hp : input.typevars.length = 0
    · by_cases ha : input.isAny.all id
      · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp, ha,
          List.mem_append] at h ⊢
        grind
      · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp, ha,
          List.mem_append] at h ⊢
        grind
    · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp,
        List.mem_append] at h ⊢
      grind
  · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc,
      List.mem_append] at h ⊢
    grind

theorem defaultCtorAccessesInBounds : DefaultCtorAccessesInBounds := by
  intro input access h0
  have hall := defaultCtorAccesses_subset input access h0
  clear h0
  unfold defaultCtorAllAccesses at hall
  simp only [List.mem_append] at hall
  rcases hall with h | hall
  · simp only [List.mem_map] at h
    obtain ⟨source, hs, rfl⟩ := h
    have hb := fieldtypesConstrainLoop_safe input input.typevars.length
      input.typevars.length source (by omega) hs
    cases source <;> exact hb
  · rcases hall with h | hall
    · simp only [tagged, List.mem_map] at h
      obtain ⟨i, hi, rfl⟩ := h
      exact oneBasedLoop_safe _ _ hi
    · rcases hall with h | hall
      · simp only [tagged, List.mem_map] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact oneBasedLoop_safe _ _ hi
      · rcases hall with h | hall
        · simp only [tagged, List.mem_map] at h
          obtain ⟨i, hi, rfl⟩ := h
          exact oneBasedLoop_safe _ _ hi
        · rcases hall with h | hall
          · simp only [tagged, List.mem_map] at h
            obtain ⟨i, hi, rfl⟩ := h
            exact shiftedLoop_safe _ _ hi
          · rcases hall with h | hall
            · simp only [tagged, List.mem_map] at h
              obtain ⟨i, hi, rfl⟩ := h
              exact shiftedLoop_safe _ _ hi
            · rcases hall with h | hall
              · simp only [tagged, List.mem_map] at h
                obtain ⟨i, hi, rfl⟩ := h
                exact shiftedLoop_safe _ _ hi
              · rcases hall with h | hall
                · simp only [tagged, List.mem_map] at h
                  obtain ⟨i, hi, rfl⟩ := h
                  exact shiftedLoop_safe _ _ hi
                · rcases hall with h | hall
                  · simp only [tagged, List.mem_map] at h
                    obtain ⟨i, hi, rfl⟩ := h
                    exact oneBasedLoop_safe _ _ hi
                  · rcases hall with h | hall
                    · simp only [tagged, List.mem_map] at h
                      obtain ⟨i, hi, rfl⟩ := h
                      have hs := innerBodyIndices_safe input.isAny 1 i hi
                      simp only [ctorBufferLength, OneBasedInBounds] at hs ⊢
                      omega
                    · rcases hall with h | h
                      · simp only [tagged, List.mem_map, List.mem_reverse] at h
                        obtain ⟨i, hi, rfl⟩ := h
                        exact oneBasedLoop_safe _ _ hi
                      · simp only [tagged, List.mem_map] at h
                        obtain ⟨i, hi, rfl⟩ := h
                        exact shiftedLoop_safe _ _ hi

/-! ## runtime-owned pointer tables -/

/-- One command string in the runtime-owned `JLOptions.commands` table. Its
head is the byte read at options.jl:128; `tail` includes the remaining C string. -/
structure RuntimeCommand where
  head : Nat
  tail : List Nat

/-- The runtime table is the listed command pointers followed by a null
sentinel, exactly the layout scanned at options.jl:121-131. -/
structure RuntimeOptions where
  commands : List RuntimeCommand

/-- Pointer-table indices loaded by the sentinel loop, including the final
null pointer. -/
def optionsPointerLoads (options : RuntimeOptions) : List Nat :=
  oneBasedLoop (options.commands.length + 1)

/-- The first-byte load for each non-null command pointer. -/
def optionsCommandByteLoads (options : RuntimeOptions) : List Nat :=
  options.commands.map (fun _ => 1)

/-- `JLOptions()` loads one runtime object; all show and `exec_options` callers
scan the null-terminated command table and one byte of each command string. -/
def OptionsCommandsAccessesInBounds : Prop :=
  OneBasedInBounds 1 1 ∧
  (∀ options i, i ∈ optionsPointerLoads options →
    OneBasedInBounds (options.commands.length + 1) i) ∧
  (∀ options i, i ∈ optionsCommandByteLoads options → OneBasedInBounds 1 i)

theorem optionsCommandsAccessesInBounds : OptionsCommandsAccessesInBounds := by
  refine ⟨by simp [OneBasedInBounds], ?_, ?_⟩
  · intro options i hi
    simp only [optionsPointerLoads, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [OneBasedInBounds]
    omega
  · intro options i hi
    simp only [optionsCommandByteLoads, List.mem_map] at hi
    obtain ⟨command, _, rfl⟩ := hi
    simp [OneBasedInBounds]

/-- Results of the symbol and task-pool branches that can reach
`_nthreads_in_pool`; foreign and invalid requests return before the table load. -/
inductive RuntimePoolRequest where
  | interactive
  | default
  | foreign
  | invalid
  deriving DecidableEq

/-- `_sym_to_tpid`, `threadpoolsize`, `threadpooltids`, `multiq_size`, and the
`@spawn` branch, followed by the one-based `tpid + 1` at line 64. -/
def runtimePoolIndex : RuntimePoolRequest → Option Nat
  | .interactive => some 1
  | .default => some 2
  | .foreign | .invalid => none

/-- Scalar `cglobal` loads at lines 47, 63, 124, and 169 have one cell. The
pool-count pointer loaded at line 63 names the runtime's two-entry table. -/
def ThreadRuntimeAccessesInBounds : Prop :=
  OneBasedInBounds 1 1 ∧
  ∀ request index, runtimePoolIndex request = some index → OneBasedInBounds 2 index

theorem threadRuntimeAccessesInBounds : ThreadRuntimeAccessesInBounds := by
  constructor
  · simp [OneBasedInBounds]
  · intro request index h
    cases request <;> simp [runtimePoolIndex] at h
    all_goals subst index <;> simp [OneBasedInBounds]

/-! ## `base/rawbigfloats.jl` and `base/show.jl` -/

/-- Descending word requests made by `truncated`, including the partial word.
Each request is kept only after the source's `w < lenx` check. -/
def truncatedWordRequests (wordCount bitCount : Nat) : List Nat :=
  let whole := (List.range (bitCount / 64)).filter (· < wordCount)
  let lastPart := if bitCount % 64 ≠ 0 ∧ bitCount / 64 < wordCount
    then [bitCount / 64] else []
  whole ++ lastPart

/-- A checked zero-based bit request becomes a descending zero-based word
request, matching rawbigfloats.jl:73-80. -/
def bitWordRequest (wordCount bitIndex : Nat) : List Nat :=
  if bitIndex < 64 * wordCount then [bitIndex / 64] else []

/-- The final-bit and round-bit requests at lines 123-127. A zero `len` makes
`len-1` negative in Julia and therefore produces no final-bit word access. -/
def roundingWordRequests (wordCount len : Nat) : List Nat :=
  (if 0 < len then bitWordRequest wordCount (len - 1) else []) ++
    bitWordRequest wordCount len

/-- Descending zero-based word indices become the one-based `i+1` access after
`reversed_index`, lines 9-23. -/
def descendingWordLoads (wordCount : Nat) (requests : List Nat) : List Nat :=
  requests.map (wordCount - ·)

/-- Sticky-bit accesses at lines 53-57 and 139-142. `tailBits` is positive
exactly when the public Float conversion asks for bits below the round bit. -/
def stickyWordLoads (wordCount len : Nat) : List Nat :=
  let tailBits := 64 * wordCount - len - 1
  if tailBits = 0 then [] else
    let whole := tailBits / 64
    (if tailBits % 64 = 0 then [] else [whole + 1]) ++ oneBasedLoop whole

/-- All word-array accesses reached from public BigFloat-to-Float conversion:
`truncated`, final/round bit construction, and the sticky-bit callback. -/
def rawBigFloatWordLoads (wordCount len : Nat) : List Nat :=
  descendingWordLoads wordCount (truncatedWordRequests wordCount len) ++
  descendingWordLoads wordCount (roundingWordRequests wordCount len) ++
  stickyWordLoads wordCount len

def RawBigFloatAccessesInBounds : Prop :=
  ∀ wordCount len index, index ∈ rawBigFloatWordLoads wordCount len →
    OneBasedInBounds wordCount index

private theorem truncatedWordRequests_safe (wordCount bitCount request : Nat) :
    request ∈ truncatedWordRequests wordCount bitCount → request < wordCount := by
  intro h
  simp only [truncatedWordRequests, List.mem_append, List.mem_filter,
    List.mem_range] at h
  rcases h with ⟨_, hr⟩ | h
  · exact of_decide_eq_true hr
  · split at h
    · rename_i hc
      simp at h
      subst request
      exact hc.2
    · contradiction

private theorem bitWordRequest_safe (wordCount bitIndex request : Nat) :
    request ∈ bitWordRequest wordCount bitIndex → request < wordCount := by
  intro h
  unfold bitWordRequest at h
  split at h
  · rename_i hb
    simp at h
    subst request
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 64)).2 (by simpa [Nat.mul_comm] using hb)
  · contradiction

private theorem roundingWordRequests_safe (wordCount len request : Nat) :
    request ∈ roundingWordRequests wordCount len → request < wordCount := by
  intro h
  simp only [roundingWordRequests, List.mem_append] at h
  rcases h with h | h
  · split at h
    · exact bitWordRequest_safe wordCount (len - 1) request h
    · contradiction
  · exact bitWordRequest_safe wordCount len request h

private theorem descendingWordLoads_safe (wordCount : Nat) (requests : List Nat)
    (hrequests : ∀ request ∈ requests, request < wordCount) (index : Nat) :
    index ∈ descendingWordLoads wordCount requests → OneBasedInBounds wordCount index := by
  intro h
  simp only [descendingWordLoads, List.mem_map] at h
  obtain ⟨request, hr, rfl⟩ := h
  have hs := hrequests request hr
  simp only [OneBasedInBounds]
  omega

private theorem stickyWordLoads_safe (wordCount len index : Nat) :
    index ∈ stickyWordLoads wordCount len → OneBasedInBounds wordCount index := by
  intro h
  let tailBits := 64 * wordCount - len - 1
  change index ∈ (if tailBits = 0 then [] else
    (if tailBits % 64 = 0 then [] else [tailBits / 64 + 1]) ++
      oneBasedLoop (tailBits / 64)) at h
  by_cases hz : tailBits = 0
  · simp [hz] at h
  · rw [if_neg hz] at h
    have htail : tailBits < 64 * wordCount := by
      dsimp [tailBits]
      omega
    have hwhole : tailBits / 64 < wordCount :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 64)).2 (by simpa [Nat.mul_comm] using htail)
    by_cases hr : tailBits % 64 = 0
    · simp only [hr, ↓reduceIte, List.nil_append] at h
      have hs := oneBasedLoop_safe _ _ h
      simp only [OneBasedInBounds] at hs ⊢
      omega
    · simp only [hr, ↓reduceIte, List.mem_append, List.mem_singleton] at h
      rcases h with rfl | h
      · simp only [OneBasedInBounds]
        omega
      · have hs := oneBasedLoop_safe _ _ h
        simp only [OneBasedInBounds] at hs ⊢
        omega

theorem rawBigFloatAccessesInBounds : RawBigFloatAccessesInBounds := by
  intro wordCount len index h
  simp only [rawBigFloatWordLoads, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · exact descendingWordLoads_safe wordCount _
        (truncatedWordRequests_safe wordCount len) index h
    · exact descendingWordLoads_safe wordCount _
        (roundingWordRequests_safe wordCount len) index h
  · exact stickyWordLoads_safe wordCount len index h

/-- Inputs affecting the branch in show.jl:530-557. Structured values take the
field loop; only the raw-bits branch reaches the pointer conversion and load. -/
structure ShowBitsInput where
  bitSize : Nat
  rawBitsBranch : Bool

/-- Raw byte offsets computed from `bitsizeof(t)`, `cld`, pointer conversion,
and the descending `(nbytes-1):-1:0` loop. -/
def showBitsAccesses (input : ShowBitsInput) : List Nat :=
  if input.rawBitsBranch then (List.range ((input.bitSize + 7) / 8)).reverse else []

/-- Every raw display load is within the `cld(bitsizeof(t), 8)` bytes occupied
by the bits object. -/
def ShowBitsAccessesInBounds : Prop :=
  ∀ input offset, offset ∈ showBitsAccesses input → offset < (input.bitSize + 7) / 8

theorem showBitsAccessesInBounds : ShowBitsAccessesInBounds := by
  intro input offset h
  unfold showBitsAccesses at h
  split at h
  · simpa only [List.mem_reverse, List.mem_range] using h
  · contradiction

/-! ## `base/slicearray.jl` -/

structure Slice1 where
  parentLen : Nat
  outerLen : Nat

/-- The public `Slices(A, slicemap, ax)` constructor should ensure that every
index accepted by the supplied outer axis maps inside the parent axis. -/
def SlicesAccessesInBounds : Prop :=
  ∀ s : Slice1, ∀ i, OneBasedInBounds s.outerLen i → OneBasedInBounds s.parentLen i

theorem slicesAccessesInBounds_refuted : ¬ SlicesAccessesInBounds := by
  intro h
  have bad := h ⟨2, 3⟩ 3 (by simp [OneBasedInBounds])
  simp [OneBasedInBounds] at bad

/-! ## `base/stream.jl` -/

inductive RedirectGlobal where
  | stdin
  | stdout
  | stderr
  deriving DecidableEq

/-- The nested conditional at stream.jl:1949-1954, including the null branch. -/
def redirectTarget (fd : Int) : Option RedirectGlobal :=
  if fd = 0 then some .stdin
  else if fd = 1 then some .stdout
  else if fd = 2 then some .stderr
  else none

/-- `unsafe_store!(c_sym, value)` uses the implicit pointer offset one. -/
def redirectStoreOffset (fd : Int) : Option Nat := (redirectTarget fd).map (fun _ => 1)

/-- Every non-null target selected by `_redirect_io_cglobal` is a scalar C
global, and the actual implicit store offset is one. -/
def StreamRedirectAccessesInBounds : Prop :=
  ∀ fd offset, redirectStoreOffset fd = some offset → OneBasedInBounds 1 offset

theorem streamRedirectAccessesInBounds : StreamRedirectAccessesInBounds := by
  intro fd offset h
  unfold redirectStoreOffset redirectTarget at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  · simp at h

/-! ## `base/threadingconstructs.jl` -/

/-- The valid linear indices of the result passed from a threaded comprehension
to `_comprehension_result`, `base/threadingconstructs.jl:356-370`. -/
structure ComprehensionResult where
  indices : List (JInt .i64)

/-- The first unchecked read reached by the widening path. This includes the
empty-result and concrete-eltype branches at lines 357-362, the wrapping
`firstindex(result) + 1`, and the `for j in i:lastindex(result)` emptiness test
at lines 368-370. -/
def comprehensionWidenFirstRead (result : ComprehensionResult) (concreteEltype : Bool) :
    Option (JInt .i64) :=
  match result.indices with
  | [] => none
  | first :: rest =>
    if concreteEltype then none
    else
      let last := rest.getLastD first
      let i := first + JInt.lit .i64 1
      if i.val ≤ last.val then some i else none

/-- Every read selected by the public threaded-comprehension widening path is
an index of the result array. -/
def ComprehensionWidenAccessesInBounds : Prop :=
  ∀ result concreteEltype,
    match comprehensionWidenFirstRead result concreteEltype with
    | none => True
    | some i => i.val ∈ result.indices.map (·.val)

theorem comprehensionWidenAccessesInBounds_refuted : ¬ ComprehensionWidenAccessesInBounds := by
  intro h
  have hwrap : (JInt.typemax .i64 + JInt.lit .i64 1).val = IntTy.i64.min := by decide
  have hmax : (JInt.typemax .i64).val = IntTy.i64.max := by decide
  have bad := h ⟨[JInt.typemax .i64]⟩ false
  simp [comprehensionWidenFirstRead, hwrap, hmax, IntTy.min, IntTy.max,
    IntTy.signed, IntTy.bits] at bad

/-! ## `base/toml/parser.jl` -/

/-- A byte range recorded by `parse_string_continue` at parser.jl:1383-1413.
The scanner cursor ensures that every chunk lies in `l.str`. -/
structure TomlChunk (sourceLength : Nat) where
  start : Nat
  length : Nat
  sourceFits : start + length ≤ sourceLength

/-- The relevant Parser fields passed from public `parse` and `tryparse` paths
to `take_chunks`. -/
structure TomlChunkState where
  sourceLength : Nat
  chunks : List (TomlChunk sourceLength)

structure CopySpan where
  sourceStart : Nat
  destStart : Nat
  count : Nat

/-- The copy loop at parser.jl:1447-1459. `destStart` is the source's
one-based `offset` normalized to a zero-based byte offset. -/
def takeChunkCopiesFrom {sourceLength : Nat} :
    Nat → List (TomlChunk sourceLength) → List CopySpan
  | _, [] => []
  | dest, chunk :: rest =>
    ⟨chunk.start, dest, chunk.length⟩ ::
      takeChunkCopiesFrom (dest + chunk.length) rest

def takeChunkCopies (state : TomlChunkState) : List CopySpan :=
  takeChunkCopiesFrom 0 state.chunks

def takeChunkDestinationLength (state : TomlChunkState) : Nat :=
  (state.chunks.map (·.length)).sum

/-- Each source span is within `l.str`; each destination span is within the
string allocated from `sum(length, l.chunks)`. -/
def TomlTakeChunksAccessesInBounds : Prop :=
  ∀ state span, span ∈ takeChunkCopies state →
    span.sourceStart + span.count ≤ state.sourceLength ∧
    span.destStart + span.count ≤ takeChunkDestinationLength state

private theorem takeChunkCopiesFrom_safe {sourceLength : Nat} :
    ∀ (chunks : List (TomlChunk sourceLength)) dest span,
      span ∈ takeChunkCopiesFrom dest chunks →
      span.sourceStart + span.count ≤ sourceLength ∧
      span.destStart + span.count ≤
        dest + (chunks.map (fun chunk : TomlChunk sourceLength => chunk.length)).sum
  | [], _, _, h => by simp [takeChunkCopiesFrom] at h
  | chunk :: rest, dest, span, h => by
      simp only [takeChunkCopiesFrom, List.mem_cons] at h
      rcases h with rfl | h
      · constructor
        · exact chunk.sourceFits
        · simp
      · have ih := takeChunkCopiesFrom_safe rest (dest + chunk.length) span h
        constructor
        · exact ih.1
        · simp only [List.map_cons, List.sum_cons]
          omega

theorem tomlTakeChunksAccessesInBounds : TomlTakeChunksAccessesInBounds := by
  intro state span h
  have hs := takeChunkCopiesFrom_safe state.chunks 0 span h
  simpa [takeChunkCopies, takeChunkDestinationLength] using hs

/-! ## `base/version.jl` -/

/-- Comparison outcomes for one `VersionRange`. The functions stand for the
two source comparisons at version.jl:548 and 553 on the actual versions. -/
structure VersionRangeComparisons where
  lowerAccepts : Nat → Bool
  upperAccepts : Nat → Bool

inductive VersionMatchAccess where
  | version (index : Nat)
  | dest (index : Nat)

mutual
  /-- The first `while` at version.jl:547-550. The `i ≤ n` check occurs before
  each recorded access. -/
  def versionLowerScan (range : VersionRangeComparisons) :
      Nat → Nat → Nat → List VersionMatchAccess
    | 0, _, _ => []
    | fuel + 1, n, i =>
      if i ≤ n then
        .version i :: if range.lowerAccepts i then versionUpperScan range (fuel + 1) n i
          else versionLowerScan range fuel n (i + 1)
      else []

  /-- The marking `while` at lines 552-556, including its read and write. -/
  def versionUpperScan (range : VersionRangeComparisons) :
      Nat → Nat → Nat → List VersionMatchAccess
    | 0, _, _ => []
    | fuel + 1, n, i =>
      if i ≤ n then
        .version i :: if range.upperAccepts i then
          .dest i :: versionUpperScan range fuel n (i + 1)
        else []
      else []
end

/-- All accesses beneath the line-545 `@inbounds` loop after both assertions.
The outer list traversal is `for range in spec.ranges`; every inner scan starts at one. -/
def versionMatchesAccesses (versionsLength destLength n : Nat)
    (ranges : List VersionRangeComparisons) : List VersionMatchAccess :=
  if versionsLength = n ∧ n ≤ destLength then
    ranges.flatMap (fun range => versionLowerScan range (n + 1) n 1)
  else []

def VersionMatchesAccessesInBounds : Prop :=
  ∀ versionsLength destLength n ranges access,
    access ∈ versionMatchesAccesses versionsLength destLength n ranges →
    match access with
    | .version i => OneBasedInBounds versionsLength i
    | .dest i => OneBasedInBounds destLength i

private theorem versionUpperScan_safe (range : VersionRangeComparisons) :
    ∀ fuel n i access, 1 ≤ i → access ∈ versionUpperScan range fuel n i →
      match access with
      | .version j => OneBasedInBounds n j
      | .dest j => OneBasedInBounds n j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [versionUpperScan]
  | succ fuel ih =>
    intro n i access hi hmem
    simp only [versionUpperScan] at hmem
    split at hmem
    · rename_i hin
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨hi, hin⟩
      · split at hmem
        · simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨hi, hin⟩
          · exact ih n (i + 1) access (by omega) hmem
        · contradiction
    · contradiction

private theorem versionLowerScan_safe (range : VersionRangeComparisons) :
    ∀ fuel n i access, 1 ≤ i → access ∈ versionLowerScan range fuel n i →
      match access with
      | .version j => OneBasedInBounds n j
      | .dest j => OneBasedInBounds n j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [versionLowerScan]
  | succ fuel ih =>
    intro n i access hi hmem
    simp only [versionLowerScan] at hmem
    split at hmem
    · rename_i hin
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨hi, hin⟩
      · split at hmem
        · exact versionUpperScan_safe range (fuel + 1) n i access hi hmem
        · exact ih n (i + 1) access (by omega) hmem
    · contradiction

theorem versionMatchesAccessesInBounds : VersionMatchesAccessesInBounds := by
  intro versionsLength destLength n ranges access hmem
  unfold versionMatchesAccesses at hmem
  split at hmem
  · rename_i checks
    simp only [List.mem_flatMap] at hmem
    obtain ⟨range, _, hmem⟩ := hmem
    have hs := versionLowerScan_safe range (n + 1) n 1 access (by omega) hmem
    cases access with
    | version i => simpa [checks.1] using hs
    | dest i =>
      simp only [OneBasedInBounds] at hs ⊢
      omega
  · contradiction

/-- The one-based counter values produced by the nested loops at
version.jl:570-578. There is one write for each pair and the allocation has the
same product length. -/
def versionIntersectAccesses (aRanges bRanges : List Nat) : List Nat :=
  oneBasedLoop (aRanges.length * bRanges.length)

def VersionIntersectAccessesInBounds : Prop :=
  ∀ aRanges bRanges i, i ∈ versionIntersectAccesses aRanges bRanges →
    OneBasedInBounds (aRanges.length * bRanges.length) i

theorem versionIntersectAccessesInBounds : VersionIntersectAccessesInBounds := by
  intro aRanges bRanges i hi
  simp only [versionIntersectAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [OneBasedInBounds]
  omega

end JuliaLean.MemSafety.G5
