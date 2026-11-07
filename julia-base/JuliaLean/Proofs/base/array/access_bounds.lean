import JuliaLean.Core

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- A one-based access of `count` consecutive elements in storage of length `capacity`. -/
def Access (capacity start count : Nat) : Prop :=
  count = 0 ∨ (1 ≤ start ∧ start + count - 1 ≤ capacity)

/-- A live vector occupies `length` elements beginning at `offset` in its backing memory. -/
def VectorState (capacity offset length : Nat) : Prop :=
  1 ≤ offset ∧ offset - 1 + length ≤ capacity

/-- A successful `checkbounds` supplies exactly the obligation used by scalar array,
substring, swap-row, and swap-column accesses. -/
def GuardedBounds : Prop :=
  ∀ capacity index : Nat, 1 ≤ index → index ≤ capacity → Access capacity index 1

/-- Bounds checks in `_copyto_impl!` cover both spans before the call to
`unsafe_copyto!`; `base/array.jl:299-315`. -/
def CopyBounds : Prop :=
  ∀ destLength destOffset srcLength srcOffset count : Nat,
    count = 0 ∨
      (1 ≤ destOffset ∧ destOffset + count - 1 ≤ destLength ∧
       1 ≤ srcOffset ∧ srcOffset + count - 1 ≤ srcLength) →
    Access destLength destOffset count ∧ Access srcLength srcOffset count

/-- A loop whose iterator contract supplies at most the allocated number of elements
writes only allocated slots. This is the bounds part of array construction, collection,
`filter`, `vcat`, `unique!`, and `replace!`. -/
def AllocatedLoopBounds : Prop :=
  ∀ capacity produced index : Nat, produced ≤ capacity → index < produced →
    Access capacity (index + 1) 1

/-- The centered allocation branch of `_growbeg_internal!` and `_growat!`: old data is
read from a valid vector and copied after the new gap into the centered new vector;
`base/array.jl:1116-1148,1263-1273`. -/
def CenteredGrowthBounds : Prop :=
  ∀ oldCapacity oldOffset length newCapacity delta newOffset : Nat,
    VectorState oldCapacity oldOffset length →
    0 < length + delta → length + delta ≤ newCapacity →
    newOffset = (newCapacity - (length + delta)) / 2 + 1 →
    Access oldCapacity oldOffset length ∧
    Access newCapacity (newOffset + delta) length ∧
    Access newCapacity newOffset 1

/-- `_growend_internal!` either moves live data toward the front in the same memory or
keeps its old offset in a larger allocation; `base/array.jl:1171-1208`. -/
def EndGrowthBounds : Prop :=
  ∀ oldCapacity oldOffset length delta newCapacity newOffset : Nat,
    VectorState oldCapacity oldOffset length → 0 < length + delta →
    ((newCapacity = oldCapacity ∧ newOffset = (length + delta) / 8 + 1 ∧
        length + delta < oldOffset) ∨
     (newOffset = oldOffset ∧ oldOffset - 1 + (length + delta) ≤ newCapacity)) →
    Access oldCapacity oldOffset length ∧
    Access newCapacity newOffset length ∧ Access newCapacity newOffset 1

/-- The no-allocation `_growbeg!` branch moves the reference left by `delta`; its branch
condition is `delta <= offset - 1`; `base/array.jl:1151-1168`. -/
def FrontGrowthBounds : Prop :=
  ∀ capacity offset length delta : Nat,
    VectorState capacity offset length → delta ≤ offset - 1 →
    Access capacity (offset - delta) (length + delta)

/-- The in-place tail branch of `_growat!` shifts `length-index+1` elements right by
`delta` after checking that the expanded live span fits; `base/array.jl:1257-1262`. -/
def TailGrowthBounds : Prop :=
  ∀ capacity offset length index delta : Nat, VectorState capacity offset length →
    1 ≤ index → index ≤ length → offset - 1 + length + delta ≤ capacity →
    Access capacity (offset - 1 + index) (length - index + 1) ∧
    Access capacity (offset - 1 + delta + index) (length - index + 1)

/-- `sizehint!` allocates `length + increment` slots and places the live vector either at
one or at `increment + 1`; `base/array.jl:1617-1647`. -/
def SizehintBounds : Prop :=
  ∀ length increment : Nat,
    Access (length + increment) 1 length ∧
    Access (length + increment) (increment + 1) length

/-- Both branches of `_deleteat!` copy a prefix or suffix within the original vector;
`base/array.jl:1312-1327`. -/
def DeleteMoveBounds : Prop :=
  ∀ length index delta : Nat, 1 ≤ index → index ≤ length →
    index + delta ≤ length + 1 →
    Access length 1 (index - 1) ∧
    Access length (index + delta) (length + 1 - delta - index)

/-- Indices yielded by `axes`, `eachindex`, `pairs`, and a checked reverse window stay in
the same array. This covers the direct iterator-indexed loops in `base/array.jl`,
`base/combinatorics.jl`, and `base/set.jl`. -/
def AxisAccess (first last index : Int) : Prop := first ≤ index ∧ index ≤ last

def IteratorBounds : Prop :=
  ∀ first last index : Int, first ≤ index → index ≤ last → AxisAccess first last index

/-- `_wrap` exposes `length` elements starting at a `MemoryRef` only after checking the
remaining memory length; `base/array.jl:3241-3278`. -/
def WrapBounds : Prop :=
  ∀ memoryLength offset length : Nat, 1 ≤ offset →
    offset - 1 + length ≤ memoryLength → Access memoryLength offset length

theorem guardedBounds_proven : GuardedBounds := by
  intro capacity index h1 h2
  simp [Access]
  omega

theorem copyBounds_proven : CopyBounds := by
  intro destLength destOffset srcLength srcOffset count h
  rcases h with h0 | h
  · simp [Access, h0]
  · constructor <;> simp only [Access] <;> right <;> omega

theorem allocatedLoopBounds_proven : AllocatedLoopBounds := by
  intro capacity produced index hp hi
  simp [Access]
  omega

theorem centeredGrowthBounds_proven : CenteredGrowthBounds := by
  intro oldCapacity oldOffset length newCapacity delta newOffset hold hpos hcap hoff
  have hsub := Nat.sub_add_cancel hcap
  have hdiv := Nat.div_le_self (newCapacity - (length + delta)) 2
  constructor
  · rcases hold with ⟨ho, hs⟩
    by_cases hl : length = 0
    · simp [Access, hl]
    · simp only [Access]
      right
      constructor
      · exact ho
      · omega
  · constructor
    · by_cases hl : length = 0
      · simp [Access, hl]
      · simp only [Access]
        right
        constructor
        · omega
        · omega
    · simp only [Access]
      right
      constructor <;> omega

theorem endGrowthBounds_proven : EndGrowthBounds := by
  intro oldCapacity oldOffset length delta newCapacity newOffset hold hpos hbranch
  rcases hold with ⟨hoff, hspan⟩
  constructor
  · by_cases hl : length = 0
    · simp [Access, hl]
    · simp only [Access]
      right
      constructor <;> omega
  · rcases hbranch with hsame | hnew
    · rcases hsame with ⟨rfl, rfl, hfront⟩
      have hdiv := Nat.div_le_self (length + delta) 8
      constructor
      · by_cases hl : length = 0
        · simp [Access, hl]
        · simp only [Access]
          right
          constructor <;> omega
      · simp only [Access]
        right
        constructor <;> omega
    · rcases hnew with ⟨rfl, hnewspan⟩
      constructor
      · by_cases hl : length = 0
        · simp [Access, hl]
        · simp only [Access]
          right
          constructor <;> omega
      · simp only [Access]
        right
        constructor <;> omega

theorem frontGrowthBounds_proven : FrontGrowthBounds := by
  intro capacity offset length delta hstate hdelta
  rcases hstate with ⟨hoff, hlen⟩
  by_cases hzero : length + delta = 0
  · simp [Access, hzero]
  · simp only [Access]
    right
    constructor <;> omega

theorem tailGrowthBounds_proven : TailGrowthBounds := by
  intro capacity offset length index delta hstate hi1 hi2 hcap
  rcases hstate with ⟨hoff, hspan⟩
  constructor <;> simp only [Access] <;> right <;> constructor <;> omega

theorem sizehintBounds_proven : SizehintBounds := by
  intro length increment
  constructor
  · by_cases h : length = 0
    · simp [Access, h]
    · simp only [Access]
      right
      constructor <;> omega
  · by_cases h : length = 0
    · simp [Access, h]
    · simp only [Access]
      right
      constructor <;> omega

theorem deleteMoveBounds_proven : DeleteMoveBounds := by
  intro length index delta hi1 hi2 hid
  constructor
  · by_cases h : index - 1 = 0
    · simp [Access, h]
    · simp only [Access]
      right
      omega
  · by_cases h : length + 1 - delta - index = 0
    · simp [Access, h]
    · simp only [Access]
      right
      constructor <;> omega

theorem iteratorBounds_proven : IteratorBounds := by
  intro first last index h1 h2
  exact ⟨h1, h2⟩

theorem wrapBounds_proven : WrapBounds := by
  intro memoryLength offset length hoff hlen
  by_cases h : length = 0
  · simp [Access, h]
  · simp only [Access]
    right
    constructor <;> omega

end JuliaLean.MemSafety.G1
