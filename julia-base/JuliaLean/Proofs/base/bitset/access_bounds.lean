import JuliaLean.base.bitset

namespace JuliaLean.MemSafety.G5

/-!
# Access bounds for `base/bitset.jl`

The models normalize Julia's one-based array axes to a length and an index.
Arithmetic on BitSet chunk offsets remains `Int`, matching `base/bitset.jl`;
the existing `JuliaLean.BitArrays.BitSetS` model establishes why its offset
arithmetic does not wrap. Array lengths and loop offsets are `Nat` after the
enclosing Julia code has checked the axes or successfully allocated the result.
-/

def IntInBounds (len index : Int) : Prop := 1 ≤ index ∧ index ≤ len

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


end JuliaLean.MemSafety.G5
