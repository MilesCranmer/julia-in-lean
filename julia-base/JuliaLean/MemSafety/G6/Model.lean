import JuliaLean.Core
import JuliaLean.Strings
import JuliaLean.ReinterpretArrays

/-!
Bounds obligations for unchecked accesses in `memsafety/sites-6.tsv`.

The detailed UTF-8 and `SubArray` computations are imported from `JuliaLean.Strings` and
`JuliaLean.ReinterpretArrays`. This file models the remaining index calculations. Pointer
validity supplied by C APIs and explicitly unsafe public functions stays a caller contract in
the site table.
-/

namespace JuliaLean.MemSafety.G6

/-- One-based array bounds used by Julia's checked array interfaces. -/
def inBounds (len i : Int) : Prop := 1 ≤ i ∧ i ≤ len

/-- A contiguous span used by `unsafe_copyto!`, range assignment, and pointer-buffer loops.
The public checked callers establish `first:first+count-1 ⊆ 1:len` before suppressing checks.
This mirrors `base/genericmemory.jl:198-262,308-363` and `base/mpfr.jl:1221-1236`. -/
def GenericMemorySpansInBounds : Prop :=
  ∀ (len first count k : Int), 0 ≤ len → 1 ≤ first → 0 ≤ count →
    first + count ≤ len + 1 → 0 ≤ k → k < count → inBounds len (first + k)

theorem genericMemorySpansInBounds_proven : GenericMemorySpansInBounds := by
  intro len first count k hlen hfirst hcount hspan hk0 hk
  constructor <;> omega

/-- A successful `uv_fs_statfs` request owns one `uv_statfs_t` result object, which Julia mirrors
as one `DiskStat`, `base/file.jl:1660-1713`. -/
def DiskstatPointerLoadInBounds : Prop :=
  ∀ resultObjects : Int, 1 ≤ resultObjects → inBounds resultObjects 1

theorem diskstatPointerLoadInBounds_proven : DiskstatPointerLoadInBounds := by
  intro resultObjects h
  exact ⟨by decide, h⟩

/-- `jl_default_debug_info_kind` is one runtime-owned `Cint` global,
`base/reflection.jl:90`. -/
def ReflectionGlobalLoadInBounds : Prop :=
  ∀ globalObjects : Int, 1 ≤ globalObjects → inBounds globalObjects 1

theorem reflectionGlobalLoadInBounds_proven : ReflectionGlobalLoadInBounds := by
  intro globalObjects h
  exact ⟨by decide, h⟩

/-- The two 64-bit ABIs used by Julia's `BigFloatLayout`. LP64 uses 8-byte `Clong` and limbs;
Win64 uses 4-byte `Clong` and limbs with an 8-byte pointer. -/
inductive BigFloatAbi where
  | lp64
  | win64

def BigFloatAbi.limbBytes : BigFloatAbi → Nat
  | .lp64 => 8
  | .win64 => 4

def BigFloatAbi.headerLimbs : BigFloatAbi → Nat
  | .lp64 => 4
  | .win64 => 6

/-- Byte ends of the precision, sign, exponent, and payload-pointer fields. -/
def BigFloatAbi.fieldEnds : BigFloatAbi → Nat × Nat × Nat × Nat
  | .lp64 => (8, 12, 24, 32)
  | .win64 => (4, 8, 12, 24)

/-- `BigFloatData[i]` adds `offset_p_limbs`, four limbs on LP64 and six on Win64. Header loads
and stores use the ABI field offsets computed by Julia. This mirrors `base/mpfr.jl:128-239`. -/
def BigFloatLayoutAccessesInBounds : Prop :=
  ∀ (abi : BigFloatAbi) (payloadLimbs i : Nat),
    (1 ≤ i → i ≤ payloadLimbs →
      1 ≤ abi.headerLimbs + i ∧ abi.headerLimbs + i ≤ abi.headerLimbs + payloadLimbs) ∧
    let totalBytes := abi.limbBytes * (abi.headerLimbs + payloadLimbs)
    let ends := abi.fieldEnds
    ends.1 ≤ totalBytes ∧ ends.2.1 ≤ totalBytes ∧
      ends.2.2.1 ≤ totalBytes ∧ ends.2.2.2 ≤ totalBytes

theorem bigFloatLayoutAccessesInBounds_proven : BigFloatLayoutAccessesInBounds := by
  intro abi payloadLimbs i
  cases abi <;> simp [BigFloatAbi.headerLimbs, BigFloatAbi.limbBytes, BigFloatAbi.fieldEnds] <;>
    constructor
  · intro hi1 hi2
    constructor <;> omega
  · omega
  · intro hi1 hi2
    constructor <;> omega
  · omega

/-- `parseint` is reached from `parsevalue` with `1 ≤ i ≤ j ≤ length(buf)`.
The eight-byte fast path runs only when `i+7 ≤ j`; scalar and overflow scans use indices in
`i:j`. This mirrors `base/parsers/ints.jl:8-21,71-189`. -/
def ParserAccessesInBounds : Prop :=
  ∀ (len i j k : Int), 1 ≤ i → i ≤ j → j ≤ len →
    ((0 ≤ k ∧ k ≤ 7 ∧ i + 7 ≤ j) → inBounds len (i + k)) ∧
    ((i ≤ k ∧ k ≤ j) → inBounds len k)

theorem parserAccessesInBounds_proven : ParserAccessesInBounds := by
  intro len i j k hi hij hj
  constructor <;> intro h <;> constructor <;> omega

/-- An ovector for `n` capture groups has `2(n+1)` slots. `match` reads slots 1 and 2 for the
whole match, then `2i+1` and `2i+2` for `i = 1:n`; `_findnext_re` reads only 1 and 2.
This mirrors `base/regex.jl:430-451,491-511`. -/
def RegexOvectorAccessesInBounds : Prop :=
  ∀ (captures i : Nat), 1 ≤ i → i ≤ captures →
    1 ≤ 2 * (captures + 1) ∧ 2 ≤ 2 * (captures + 1) ∧
    2 * i + 1 ≤ 2 * (captures + 1) ∧ 2 * i + 2 ≤ 2 * (captures + 1)

theorem regexOvectorAccessesInBounds_proven : RegexOvectorAccessesInBounds := by
  intro captures i hi1 hi2
  omega

/-- The rounded normalized mantissa bucket for `log_proc1` is 128:256, hence the table index
`bucket-127` is 1:129. `_log_ext` masks to seven bits, equivalent to `% 128`, before adding one.
This mirrors `base/special/log.jl:151-156,209-214,555-565`. -/
def LogTableAccessesInBounds : Prop :=
  ∀ (bucket : Int) (bits : Nat), 128 ≤ bucket → bucket ≤ 256 →
    (1 ≤ bucket - 127 ∧ bucket - 127 ≤ 129) ∧
    (1 ≤ bits % 128 + 1 ∧ bits % 128 + 1 ≤ 128)

theorem logTableAccessesInBounds_proven : LogTableAccessesInBounds := by
  intro bucket bits hlo hhi
  constructor
  · constructor <;> omega
  · have hmod := Nat.mod_lt bits (by decide : 0 < 128)
    omega

/-- A valid `SubString` region is a one-based span of its parent; `unannotate` forwards that
span to `raw_substring`. `RegionIterator` uses identical-length region and annotation arrays.
This mirrors `base/strings/annotated.jl:184-199,504-515`. -/
def AnnotatedStringAccessesInBounds : Prop :=
  ∀ (parentLen start count regions annotations i : Int),
    0 ≤ parentLen → 1 ≤ start → 0 ≤ count → start + count ≤ parentLen + 1 →
    regions = annotations → 1 ≤ i → i ≤ regions →
    (count = 0 ∨ inBounds parentLen start) ∧ inBounds annotations i

theorem annotatedStringAccessesInBounds_proven : AnnotatedStringAccessesInBounds := by
  intro parentLen start count regions annotations i hp hs hc hspan hsame hi1 hi2
  constructor
  · by_cases hzero : count = 0
    · exact Or.inl hzero
    · right
      constructor <;> omega
  · constructor <;> omega

/-- Bounds arithmetic for `_thisind_str`, `_nextind_str`, generic `thisind`/`prevind`/`nextind`,
and the UTF-8 continuation readers. The exact byte-level functions are in
`JuliaLean.Strings.Basic`; this property states every guarded `codeunit` obligation appearing at
`base/strings/basic.jl:185-199,396-625` and `base/strings/string.jl:212-623`. -/
def StringIndexAccessesInBounds : Prop :=
  ∀ (len i : Int), 0 ≤ len → inBounds len i →
    inBounds len i ∧
    (1 < i → inBounds len (i - 1)) ∧
    (2 < i → inBounds len (i - 2)) ∧
    (3 < i → inBounds len (i - 3)) ∧
    (i + 1 ≤ len → inBounds len (i + 1)) ∧
    (i + 2 ≤ len → inBounds len (i + 2)) ∧
    (i + 3 ≤ len → inBounds len (i + 3))

theorem stringIndexAccessesInBounds_proven : StringIndexAccessesInBounds := by
  intro len i hlen hi
  rcases hi with ⟨hi1, hi2⟩
  constructor
  · exact ⟨hi1, hi2⟩
  constructor
  · intro h; constructor <;> omega
  constructor
  · intro h; constructor <;> omega
  constructor
  · intro h; constructor <;> omega
  constructor
  · intro h; constructor <;> omega
  constructor <;> intro h <;> constructor <;> omega

/-- `getindex(s, i:j)` allocates `nextind(s,j)-i` bytes and copies exactly that source span.
The premises are the bounds and validity checks at `base/strings/string.jl:580-593`. -/
def StringRangeCopyInBounds : Prop :=
  ∀ (len i next : Int), 0 ≤ len → 1 ≤ i → i < next → next ≤ len + 1 →
    inBounds len i ∧ i + (next - i) ≤ len + 1

theorem stringRangeCopyInBounds_proven : StringRangeCopyInBounds := by
  intro len i next hlen hi hnext hn
  constructor
  · constructor <;> omega
  · omega

/-- `first(s,n)` uses `1:min(lastindex(s), nextind(...))`; if overflow makes the upper endpoint
less than one, the range is empty. `last(s,n)` similarly uses `max(1, prevind(...)):lastindex(s)`.
Thus every element of either nonempty slice is in bounds even when multi-step index arithmetic
wraps, `base/strings/basic.jl:681-719`. -/
def StringFirstLastSlicesInBounds : Prop :=
  ∀ (len computed k : Int), 0 ≤ len →
    ((1 ≤ k ∧ k ≤ min len computed) → inBounds len k) ∧
    ((max 1 computed ≤ k ∧ k ≤ len) → inBounds len k)

theorem stringFirstLastSlicesInBounds_proven : StringFirstLastSlicesInBounds := by
  intro len computed k hlen
  constructor <;> intro h <;> constructor <;> omega

/-- `String(s)` owns `ncodeunits(s)` bytes, and the safe `Vector{UInt8}(s::AbstractString)` and
`Array{UInt8}(s)` wrappers expose exactly those bytes, `base/strings/basic.jl:215-222` and
`base/strings/string.jl:187-200`. -/
def StringStorageWrapInBounds : Prop :=
  ∀ (len i : Int), 0 ≤ len → 1 ≤ i → i ≤ len → inBounds len i

theorem stringStorageWrapInBounds_proven : StringStorageWrapInBounds := by
  intro len i hlen hi1 hi2
  exact ⟨hi1, hi2⟩

/-- `_utf_dfa_step` indexes its 256-entry table by `UInt8(byte)+1`,
`base/strings/string.jl:308-437`. -/
def Utf8DfaTableAccessInBounds : Prop :=
  ∀ byte : Nat, byte ≤ 255 → 1 ≤ byte + 1 ∧ byte + 1 ≤ 256

theorem utf8DfaTableAccessInBounds_proven : Utf8DfaTableAccessInBounds := by
  intro byte h
  omega

/-- Slow SubArray reindexing selects from the stored index map. View construction checks every
stored parent index, and the view docstring requires the parent shape and mutable index arrays to
remain unchanged. This is the bounds obligation at `base/subarray.jl:282-319,385-429`. -/
def SubarrayIndexMapAccessesInBounds : Prop :=
  ∀ (parentLen viewLen i : Nat) (indexAt : Nat → Int),
    (∀ k, k < viewLen → inBounds parentLen (indexAt k)) → i < viewLen →
    inBounds parentLen (indexAt i)

theorem subarrayIndexMapAccessesInBounds_proven : SubarrayIndexMapAccessesInBounds := by
  intro parentLen viewLen i indexAt hmap hi
  exact hmap i hi

/-- The `repeat(c, r)` write loops use widths 1 through 4. For zero-based repetition index `i`,
the last two-, three-, and four-byte stores remain within their exact allocation.
This mirrors `base/strings/string.jl:682-714`. -/
def RepeatCharWritesInBounds : Prop :=
  ∀ (copies i : Nat), i < copies →
    2 * i + 2 ≤ 2 * copies ∧ 3 * i + 3 ≤ 3 * copies ∧ 4 * i + 4 ≤ 4 * copies

theorem repeatCharWritesInBounds_proven : RepeatCharWritesInBounds := by
  intro copies i hi
  omega

/-- The 32 hexadecimal UUID positions and four fixed hyphen positions all lie in the allocated
36-byte string, `base/uuid.jl:98-115`. -/
def uuidWritePositions : List Int :=
  [36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25,
   23, 22, 21, 20, 18, 17, 16, 15, 13, 12, 11, 10,
   8, 7, 6, 5, 4, 3, 2, 1, 9, 14, 19, 24]

def UuidWritesInBounds : Prop :=
  ∀ i : Int, i ∈ uuidWritePositions → inBounds 36 i

theorem uuidWritesInBounds_proven : UuidWritesInBounds := by
  intro i hi
  simp [uuidWritePositions] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [inBounds]

end JuliaLean.MemSafety.G6
