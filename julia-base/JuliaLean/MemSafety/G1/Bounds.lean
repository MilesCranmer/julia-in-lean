import JuliaLean.Core

/-!
Bounds models for the unchecked accesses in `memsafety/sites-1.tsv`.

The models retain only the state that decides whether an access is in bounds. Julia
indices are one-based. A zero-length copy performs no access, so its pointer may be the
one-past-the-end pointer. Arithmetic here describes successful paths after Julia's
`checked_add`, `checked_mul`, `Int` conversion, and argument checks have returned.
-/

namespace JuliaLean.MemSafety.G1

/-- A one-based access of `count` consecutive elements in storage of length `capacity`. -/
def Access (capacity start count : Nat) : Prop :=
  count = 0 ∨ (1 ≤ start ∧ start + count - 1 ≤ capacity)

/-- A live vector occupies `length` elements beginning at `offset` in its backing memory. -/
def VectorState (capacity offset length : Nat) : Prop :=
  1 ≤ offset ∧ offset - 1 + length ≤ capacity

/-- `Base.include` grows `_included_files` when its next index reaches capacity, and
`strcat` allocates exactly the sum of its input byte lengths; `base/Base_compiler.jl:16-25,
194-205`. -/
def BootstrapBounds : Prop :=
  (∀ length capacity : Nat, length ≤ capacity → 0 < capacity →
    let grown := if length = capacity then capacity + 1 else capacity
    Access grown (length + 1) 1) ∧
  (∀ nx ny : Nat,
    Access (nx + ny) 1 nx ∧ Access (nx + ny) (nx + 1) ny)

/-- Componentwise bounds used by `repeat_outer` and `repeat_inner`; these are the two
index formulas at `base/abstractarraymath.jl:559-611`. -/
def RepeatBounds : Prop :=
  (∀ size count j : Nat, j < count → Access (size * count) (j * size + 1) size) ∧
  (∀ size count i j : Nat, i < size → j < count →
    Access (size * count) (i * count + j + 1) 1)

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

/-- Set operations combine a checked Dict-table index with indices yielded by an array
axis; `base/set.jl:139-157,373-405,579-592,947-1005`. -/
def SetBounds : Prop := GuardedBounds ∧ IteratorBounds

/-- Swap operations combine checked row or column indices with traversal of the other
axis; `base/combinatorics.jl:103-123,286-296`. -/
def CombinatoricsBounds : Prop := GuardedBounds ∧ IteratorBounds

/-- `_wrap` exposes `length` elements starting at a `MemoryRef` only after checking the
remaining memory length; `base/array.jl:3241-3278`. -/
def WrapBounds : Prop :=
  ∀ memoryLength offset length : Nat, 1 ≤ offset →
    offset - 1 + length ≤ memoryLength → Access memoryLength offset length

/-- Column-major matrix indexing used by `_mapreducedim!` and `findminmax!`;
`base/reducedim.jl:256-293,1032-1080`. -/
def MatrixBounds : Prop :=
  ∀ rows columns row column : Nat, row < rows → column < columns →
    Access (rows * columns) (row + rows * column + 1) 1

/-- The fast reduction path partitions the input into one block for every result slot. -/
def ReductionBlockBounds : Prop :=
  ∀ inputLength resultLength block index : Nat,
    resultLength * block = inputLength → index < resultLength →
    Access inputLength (index * block + 1) block

/-- A valid `SubString` view and every checked code-unit index remain inside the parent;
the second conjunct is the nested `raw_substring` offset calculation;
`base/strings/substring.jl:71-171`. -/
def SubstringBounds : Prop :=
  (∀ parent offset length index : Nat, offset + length ≤ parent →
    1 ≤ index → index ≤ length → Access parent (offset + index) 1) ∧
  (∀ parent offset length first count : Nat, offset + length ≤ parent →
    1 ≤ first → first - 1 + count ≤ length →
    Access parent (offset + first) count)

/-- String-backed IOBuffer construction combines the SubString view invariant with the
checked remaining-span rule used by `wrap`; `base/strings/io.jl:288-307`. -/
def StringIOBounds : Prop := SubstringBounds ∧ WrapBounds

/-- `_string` writes each value into its allocated prefix and string repetition writes
copy `i` into the `i`th block; `base/strings/substring.jl:215-303`. -/
def StringWriteBounds : Prop :=
  (∀ total prefixLength width : Nat, prefixLength + width ≤ total →
    Access total (prefixLength + 1) width) ∧
  (∀ width count index : Nat, index < count →
    Access (width * count) (index * width + 1) width)

/-- C and runtime buffer accesses are in bounds under the size/null-termination contract
of the function that returned the pointer. This covers `FormatMessageW`,
`uv_os_get_group`, and the two `cglobal` cells in this group. -/
def RuntimeBufferBounds : Prop :=
  ∀ available offset count : Nat, 1 ≤ offset → offset + count - 1 ≤ available →
    Access available offset count

theorem bootstrapBounds_proven : BootstrapBounds := by
  constructor
  · intro length capacity hlen hcap
    dsimp
    split
    · simp only [Access]
      right
      omega
    · simp only [Access]
      right
      omega
  · intro nx ny
    constructor
    · by_cases h : nx = 0
      · simp [Access, h]
      · simp only [Access]
        right
        omega
    · by_cases h : ny = 0
      · simp [Access, h]
      · simp only [Access]
        right
        omega

theorem repeatBounds_proven : RepeatBounds := by
  constructor
  · intro size count j hj
    by_cases hs : size = 0
    · simp [Access, hs]
    · simp only [Access]
      right
      have hmul : j * size + size ≤ size * count := by
        simpa [Nat.succ_mul, Nat.mul_comm] using
          (Nat.mul_le_mul_right size (Nat.succ_le_iff.mpr hj))
      constructor
      · omega
      · omega
  · intro size count i j hi hj
    simp only [Access]
    right
    have hmul : i * count + count ≤ size * count := by
      simpa [Nat.succ_mul] using (Nat.mul_le_mul_right count (Nat.succ_le_iff.mpr hi))
    constructor
    · omega
    · omega

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

theorem setBounds_proven : SetBounds := ⟨guardedBounds_proven, iteratorBounds_proven⟩

theorem combinatoricsBounds_proven : CombinatoricsBounds :=
  ⟨guardedBounds_proven, iteratorBounds_proven⟩

theorem wrapBounds_proven : WrapBounds := by
  intro memoryLength offset length hoff hlen
  by_cases h : length = 0
  · simp [Access, h]
  · simp only [Access]
    right
    constructor <;> omega

theorem matrixBounds_proven : MatrixBounds := by
  intro rows columns row column hr hc
  simp only [Access]
  right
  have hmul := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hc)
  rw [Nat.mul_succ] at hmul
  constructor
  · omega
  · omega

theorem reductionBlockBounds_proven : ReductionBlockBounds := by
  intro inputLength resultLength block index heq hi
  by_cases hb : block = 0
  · simp [Access, hb]
  · simp only [Access]
    right
    have hmul := Nat.mul_le_mul_right block (Nat.succ_le_iff.mpr hi)
    rw [Nat.succ_mul] at hmul
    constructor
    · omega
    · omega

theorem substringBounds_proven : SubstringBounds := by
  constructor
  · intro parent offset length index hview hi1 hi2
    simp only [Access]
    right
    constructor <;> omega
  · intro parent offset length first count hview hf hc
    by_cases h : count = 0
    · simp [Access, h]
    · simp only [Access]
      right
      constructor <;> omega

theorem stringIOBounds_proven : StringIOBounds := ⟨substringBounds_proven, wrapBounds_proven⟩

theorem stringWriteBounds_proven : StringWriteBounds := by
  constructor
  · intro total prefixLength width h
    by_cases hw : width = 0
    · simp [Access, hw]
    · simp only [Access]
      right
      constructor <;> omega
  · intro width count index hi
    by_cases hw : width = 0
    · simp [Access, hw]
    · simp only [Access]
      right
      have hmul : index * width + width ≤ width * count := by
        simpa [Nat.succ_mul, Nat.mul_comm] using
          (Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr hi))
      constructor
      · omega
      · omega

theorem runtimeBufferBounds_proven : RuntimeBufferBounds := by
  intro available offset count hoff hlen
  by_cases h : count = 0
  · simp [Access, h]
  · simp only [Access]
    right
    exact ⟨hoff, hlen⟩

end JuliaLean.MemSafety.G1
