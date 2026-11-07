import JuliaLean.Proofs.base.abstractarray.common.input_invariants
import JuliaLean.Proofs.base.strings.util.strip
import JuliaLean.base.strings.util

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Character-start indices computed by String iteration. `chopprefix`,
`chopsuffix`, `lstrip`, `rstrip`, truncation, and split advance only through
these states. -/
def stringCharacterAccesses (s : Strings.JStr) : List Int :=
  (Strings.collectPairs s).map fun pair => pair.2.val

/-- Code-unit reads computed by the String fast path of `chomp`. -/
def chompCodeunitAccesses (s : Strings.JStr) : List Nat :=
  let n := s.bytes.length
  if n = 0 then [] else [n] ++ if 1 < n then [n - 1] else []

/-- All sentinel or character boundaries accepted by unchecked SubString and
raw_substring construction: `0` through `ncodeunits(s)+1`. -/
def stringSubstringBoundaries (s : Strings.JStr) : List Int :=
  (List.range (s.bytes.length + 2)).map fun (i : Nat) => (i : Int)

/-- Bounds union for the control flow of `chopprefix`, `chopsuffix`, `chomp`,
`lstrip`, `rstrip`, `string_truncate_boundaries`, and `SplitIterator.iterate`,
`base/strings/util.jl:268-806`. -/
def StringPositionSafe : Prop :=
  (∀ s i, i ∈ stringCharacterAccesses s → inAxis 1 s.bytes.length i) ∧
  (∀ s i, i ∈ chompCodeunitAccesses s → inOneBased s.bytes.length i) ∧
  (∀ s i, i ∈ stringSubstringBoundaries s → 0 ≤ i ∧ i ≤ s.bytes.length + 1)

/-- Destination indices computed by the `eachindex(dest)` loop of
`hex2bytes!`, `base/strings/util.jl:1260-1274`. -/
def hex2bytesDestIndices (dest : List UInt8) : List Nat :=
  oneBasedLoop dest.length

/-- The two output positions computed by `bytes2hex` for every enumerated
input byte, `base/strings/util.jl:1316-1327`. -/
def bytes2hexOutputIndices (bytes : List UInt8) : List Nat :=
  (oneBasedLoop bytes.length).flatMap fun i => [2 * i - 1, 2 * i]

/-- The two `hex_chars` indices computed from every byte. -/
def bytes2hexDigitIndices (bytes : List UInt8) : List Nat :=
  bytes.flatMap fun x => [x.toNat / 16 + 1, x.toNat % 16 + 1]

/-- Code-unit indices computed by `ascii(s::String)` from `sizeof(s)`,
`base/strings/util.jl:1336-1341`. -/
def asciiCodeunitIndices (s : Strings.JStr) : List Nat :=
  oneBasedLoop s.bytes.length

def StringHexSafe : Prop :=
  (∀ dest i, i ∈ hex2bytesDestIndices dest → inOneBased dest.length i) ∧
  (∀ bytes i, i ∈ bytes2hexOutputIndices bytes → inOneBased (2 * bytes.length) i) ∧
  (∀ bytes i, i ∈ bytes2hexDigitIndices bytes →
    inOneBased StringUtil.hexChars.length i) ∧
  (∀ s i, i ∈ asciiCodeunitIndices s → inOneBased s.bytes.length i)

private theorem iterTrace_indices_safe (s : Strings.JStr) :
    ∀ {start trace}, Strings.IterTrace s start trace → StringUtil.Strip.VE s start →
      ∀ pair ∈ trace, inAxis 1 s.bytes.length pair.2.val
  | _, [], _, _, pair, hp => by simp at hp
  | start, pair :: rest, htrace, hv, p, hp => by
      obtain ⟨hindex, next, hstep, hrest⟩ := StringUtil.Strip.trace_cons_inv htrace
      obtain ⟨hvalid, _, hvnext⟩ := StringUtil.Strip.iter_step hv hstep
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [hindex]
        unfold inAxis
        exact ⟨hvalid.1, by omega⟩
      · exact iterTrace_indices_safe s hrest hvnext p hp

theorem stringPositionSafe_proven : StringPositionSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i hi
    simp only [stringCharacterAccesses, List.mem_map] at hi
    obtain ⟨pair, hp, rfl⟩ := hi
    exact iterTrace_indices_safe s (StringUtil.Strip.collect_trace s)
      (StringUtil.Strip.ve_one s) pair hp
  · intro s i hi
    unfold chompCodeunitAccesses at hi
    dsimp only at hi
    split at hi
    · simp at hi
    · rename_i hn
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with rfl | hi
      · unfold inOneBased
        omega
      · split at hi
        · simp only [List.mem_singleton] at hi
          subst i
          unfold inOneBased
          omega
        · simp at hi
  · intro s i hi
    simp only [stringSubstringBoundaries, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    omega

private theorem hexDigitIndices_safe : ∀ x : UInt8,
    inOneBased StringUtil.hexChars.length (x.toNat / 16 + 1) ∧
    inOneBased StringUtil.hexChars.length (x.toNat % 16 + 1) := by
  intro x
  have hx := UInt8.toNat_lt x
  simp only [StringUtil.hexChars, List.length_cons, List.length_nil, Nat.reduceAdd]
  constructor <;> unfold inOneBased <;> omega

theorem stringHexSafe_proven : StringHexSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dest i hi
    simp only [hex2bytesDestIndices, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega
  · intro bytes i hi
    simp only [bytes2hexOutputIndices, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range, List.mem_cons] at hi
    obtain ⟨entry, ⟨k, hk, rfl⟩, hi⟩ := hi
    rcases hi with rfl | hi
    · unfold inOneBased
      omega
    · rcases hi with rfl | hi
      · unfold inOneBased
        omega
      · contradiction
  · intro bytes i hi
    simp only [bytes2hexDigitIndices, List.mem_flatMap, List.mem_cons] at hi
    obtain ⟨x, _, hi⟩ := hi
    rcases hi with rfl | hi
    · exact (hexDigitIndices_safe x).1
    · rcases hi with rfl | hi
      · exact (hexDigitIndices_safe x).2
      · contradiction
  · intro s i hi
    simp only [asciiCodeunitIndices, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

end JuliaLean.MemSafety.G3
