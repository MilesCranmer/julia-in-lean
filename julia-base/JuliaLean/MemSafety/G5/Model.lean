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

/-! ## `base/accumulate.jl` -/

/-- The scalar and dimensional accumulation loops enumerate the axes of `A`;
`B` has the same axes by the checks at lines 27 and 377. The second clause is
the `i-1`/`i` pair in `_accumulaten!`, lines 412-415 and 428-431. -/
def AccumulateAccessesInBounds : Prop :=
  (∀ aLen bLen i, aLen = bLen → OneBasedInBounds aLen i →
    OneBasedInBounds aLen i ∧ OneBasedInBounds bLen i) ∧
  (∀ len i, 1 < i → i ≤ len →
    OneBasedInBounds len (i - 1) ∧ OneBasedInBounds len i)

theorem accumulateAccessesInBounds : AccumulateAccessesInBounds := by
  constructor <;> intro <;> simp only [OneBasedInBounds] at * <;> omega

/-! ## `base/bitset.jl` -/

/-- Bounds obligations used by `_bits_getindex`, the growth loops,
`_matched_map!`, iteration, `_check0`, and `issubset`. `d` is `bdiff`; lengths
are represented as nonnegative `Int`s to keep the source formulas unchanged. -/
def BitSetAccessesInBounds : Prop :=
  (∀ len ci, 0 ≤ len → 1 ≤ ci → ci ≤ len → IntInBounds len ci) ∧
  (∀ oldLen added i, 0 ≤ oldLen → 0 ≤ added → oldLen + 1 ≤ i →
    i ≤ oldLen + added → IntInBounds (oldLen + added) i) ∧
  (∀ l1 l2 d i, 0 ≤ l1 → 0 ≤ l2 →
    max 1 (1 + d) ≤ i → i ≤ min l1 (l2 + d) →
    IntInBounds l1 i ∧ IntInBounds l2 (i - d)) ∧
  (∀ l1 l2 d l1' count, 0 ≤ l1 → 0 ≤ l2 → l1 ≤ l1' → d ≤ l1' →
    count = l2 + d - l1' → 0 ≤ count →
    (count = 0 ∨ (IntInBounds (l2 + d) (l1' + 1) ∧
      IntInBounds (l2 + d) (l1' + count) ∧
      IntInBounds l2 (l1' - d + 1) ∧ IntInBounds l2 (l1' - d + count)))) ∧
  (∀ l1 l2 d count, 0 ≤ l1 → 0 ≤ l2 → d < 0 → 0 ≤ count →
    count ≤ -d → count ≤ l2 →
    (count = 0 ∨ (IntInBounds (l1 - d) 1 ∧ IntInBounds (l1 - d) count ∧
      IntInBounds l2 1 ∧ IntInBounds l2 count))) ∧
  (∀ len idx, 0 ≤ len → 1 ≤ idx → idx ≤ len → IntInBounds len idx) ∧
  (∀ n shift otherLen i, 0 ≤ n → 0 ≤ otherLen →
    max 1 (shift + 1) ≤ i → i ≤ min n (shift + otherLen) →
    IntInBounds n i ∧ IntInBounds otherLen (i - shift))

theorem bitSetAccessesInBounds : BitSetAccessesInBounds := by
  repeat' apply And.intro
  · intro len ci hlen hlo hhi
    exact ⟨hlo, hhi⟩
  · intro oldLen added i hold hadd hlo hhi
    exact ⟨by omega, hhi⟩
  · intro l1 l2 d i hl1 hl2 hlo hhi
    simp only [IntInBounds]
    omega
  · intro l1 l2 d l1' count hl1 hl2 hll hdl hc hcount
    by_cases hz : count = 0
    · exact Or.inl hz
    · right
      simp only [IntInBounds]
      omega
  · intro l1 l2 d count hl1 hl2 hd hc hcd hcl2
    by_cases hz : count = 0
    · exact Or.inl hz
    · right
      simp only [IntInBounds]
      omega
  · intro len idx hlen hlo hhi
    exact ⟨hlo, hhi⟩
  · intro n shift otherLen i hn ho hlo hhi
    simp only [IntInBounds]
    omega

/-! ## generated default constructors in `base/essentials.jl` -/

/-- Bounds for the reverse type-variable loops, arrays allocated with `n+1`
slots, and the two statements emitted for each non-`Any` field. -/
def DefaultCtorAccessesInBounds : Prop :=
  (∀ n i, OneBasedInBounds n i → OneBasedInBounds n i) ∧
  (∀ n i, OneBasedInBounds n i → OneBasedInBounds (n + 1) (i + 1)) ∧
  (∀ nonAny k, k < nonAny →
    OneBasedInBounds (2 * nonAny + 1) (2 * k + 1) ∧
    OneBasedInBounds (2 * nonAny + 1) (2 * k + 2))

theorem defaultCtorAccessesInBounds : DefaultCtorAccessesInBounds := by
  constructor
  · intro n i hi
    exact hi
  constructor
  · intro n i hi
    simp only [OneBasedInBounds] at hi ⊢
    omega
  · intro nonAny k hk
    simp only [OneBasedInBounds]
    omega

/-! ## runtime-owned pointer tables -/

/-- `unsafe_load_commands` scans a runtime-owned null-terminated pointer table.
Before the null sentinel, each pointer designates a command byte followed by a
null-terminated string. The list model stores only entries before the sentinel. -/
def OptionsCommandsAccessesInBounds : Prop :=
  ∀ (commands : List (List Nat)) i command,
    (∀ c ∈ commands, c ≠ []) → i < commands.length → command ∈ commands →
    OneBasedInBounds commands.length (i + 1) ∧ OneBasedInBounds command.length 1

theorem optionsCommandsAccessesInBounds : OptionsCommandsAccessesInBounds := by
  intro commands i command hnonempty hi hmem
  constructor
  · simp only [OneBasedInBounds]
    omega
  · have hne := hnonempty command hmem
    cases command with
    | nil => contradiction
    | cons _ _ => simp [OneBasedInBounds]

/-- The C runtime provides five scalar globals and two thread-pool counts.
`_nthreads_in_pool` is reached only with pool ids 0 and 1. -/
def ThreadRuntimeAccessesInBounds : Prop :=
  OneBasedInBounds 1 1 ∧
  ∀ tpid : Int, (tpid = 0 ∨ tpid = 1) → IntInBounds 2 (tpid + 1)

theorem threadRuntimeAccessesInBounds : ThreadRuntimeAccessesInBounds := by
  constructor
  · simp [OneBasedInBounds]
  · intro tpid ht
    rcases ht with rfl | rfl <;> simp [IntInBounds]

/-! ## `base/rawbigfloats.jl` and `base/show.jl` -/

/-- `get_elem(x, i, :words, :ascending)` changes a valid zero-based word index
to Julia's one-based `i+1`. -/
def RawBigFloatAccessesInBounds : Prop :=
  ∀ len i : Int, 0 ≤ i → i < len → IntInBounds len (i + 1)

theorem rawBigFloatAccessesInBounds : RawBigFloatAccessesInBounds := by
  intro len i hlo hhi
  simp only [IntInBounds]
  omega

/-- The raw-bit display loop reads byte offsets `nbytes-1` through zero from an
object whose byte storage is `cld(bitsizeof(T), 8)` bytes. -/
def ShowBitsAccessesInBounds : Prop :=
  ∀ nbytes offset : Nat, offset < nbytes → offset < nbytes

theorem showBitsAccessesInBounds : ShowBitsAccessesInBounds := by
  intro nbytes offset h
  exact h

/-! ## `base/stream.jl` -/

def redirectSlot (fd : Int) : Option Nat :=
  if fd = 0 then some 1 else if fd = 1 then some 2 else if fd = 2 then some 3 else none

/-- `_redirect_io_cglobal` stores only through one of the three scalar runtime
globals selected by file descriptors 0, 1, and 2. -/
def StreamRedirectAccessesInBounds : Prop :=
  ∀ fd slot, redirectSlot fd = some slot → OneBasedInBounds 3 slot

theorem streamRedirectAccessesInBounds : StreamRedirectAccessesInBounds := by
  intro fd slot h
  simp only [redirectSlot] at h
  split at h <;> rename_i h0
  · simp only [Option.some.injEq] at h
    simp only [OneBasedInBounds]
    omega
  split at h <;> rename_i h1
  · simp only [Option.some.injEq] at h
    simp only [OneBasedInBounds]
    omega
  split at h <;> rename_i h2
  · simp only [Option.some.injEq] at h
    simp only [OneBasedInBounds]
    omega
  · contradiction

/-! ## `base/threadingconstructs.jl` -/

/-- `_comprehension_widened_eltype` scans from `firstindex(result)+1` through
`lastindex(result)`. -/
def ComprehensionWidenAccessesInBounds : Prop :=
  ∀ first last index, first + 1 ≤ index → index ≤ last → first ≤ index ∧ index ≤ last

theorem comprehensionWidenAccessesInBounds : ComprehensionWidenAccessesInBounds := by
  intro first last index hlo hhi
  omega

/-! ## `base/toml/parser.jl` -/

/-- `take_chunks` allocates the sum of the chunk lengths and copies a chunk
after all preceding chunks. Empty copies have no accessed byte. -/
def TomlTakeChunksAccessesInBounds : Prop :=
  ∀ before after : List Nat, ∀ n,
    0 < n →
    OneBasedInBounds ((before ++ n :: after).sum) (before.sum + 1) ∧
    OneBasedInBounds ((before ++ n :: after).sum) (before.sum + n)

theorem tomlTakeChunksAccessesInBounds : TomlTakeChunksAccessesInBounds := by
  intro before after n hn
  simp only [List.sum_append, List.sum_cons, OneBasedInBounds]
  omega

/-! ## `base/version.jl` -/

/-- `matches_spec_range!` reads `versions[i]` and writes `dest[i]` only while
`1 <= i <= n`; its assertions establish the two lengths. -/
def VersionMatchesAccessesInBounds : Prop :=
  ∀ versionsLen destLen n i,
    versionsLen = n → n ≤ destLen → OneBasedInBounds n i →
    OneBasedInBounds versionsLen i ∧ OneBasedInBounds destLen i

theorem versionMatchesAccessesInBounds : VersionMatchesAccessesInBounds := by
  intro versionsLen destLen n i hv hd hi
  simp only [OneBasedInBounds] at hi ⊢
  omega

/-- The nested product loop in `intersect(::VersionSpec, ::VersionSpec)` stores
the pair `(i,j)` at zero-based offset `i*b+j` in an allocation of length `a*b`. -/
def VersionIntersectAccessesInBounds : Prop :=
  ∀ a b i j : Nat, i < a → j < b → i * b + j < a * b

theorem versionIntersectAccessesInBounds : VersionIntersectAccessesInBounds := by
  intro a b i j hi hj
  calc
    i * b + j < i * b + b := Nat.add_lt_add_left hj _
    _ = (i + 1) * b := by simp [Nat.add_mul]
    _ ≤ a * b := Nat.mul_le_mul_right b (Nat.succ_le_iff.mpr hi)

end JuliaLean.MemSafety.G5
