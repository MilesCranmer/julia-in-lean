import JuliaLean.Proofs.base.array.common
import JuliaLean.base.strings.basic
import JuliaLean.Proofs.base.strings.string.properties


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## String code-unit accesses -/

/-- The byte reads of `_thisind_str` and `_thisind_continued`
(`base/strings/string.jl:252-270`). The byte tests select a prefix of `i, i-1, i-2, i-3`;
each later read is present only after the corresponding source guard. -/
def thisindAccesses (s : JuliaLean.Strings.JStr) (i : Int) : List Int :=
  let n := s.bytes.length
  if i = 0 ∨ i = n + 1 ∨ i < 1 ∨ n < i then []
  else
    let b0 := JuliaLean.Strings.cu s (JInt.wrap .i64 i)
    if !(JuliaLean.Strings.isCont b0 && decide (i - 1 > 0)) then [i]
    else
      let b1 := JuliaLean.Strings.cu s (JInt.wrap .i64 (i - 1))
      if JuliaLean.Strings.between b1 0xc0 0xf7 then [i, i - 1]
      else if !(JuliaLean.Strings.isCont b1 && decide (i - 2 > 0)) then [i, i - 1]
      else
        let b2 := JuliaLean.Strings.cu s (JInt.wrap .i64 (i - 2))
        if JuliaLean.Strings.between b2 0xe0 0xf7 then [i, i - 1, i - 2]
        else if !(JuliaLean.Strings.isCont b2 && decide (i - 3 > 0)) then
          [i, i - 1, i - 2]
        else [i, i - 1, i - 2, i - 3]

theorem thisindAccesses_safe (s : JuliaLean.Strings.JStr) (i j : Int)
    (h : j ∈ thisindAccesses s i) : inBounds s.bytes.length j := by
  simp only [thisindAccesses] at h
  split at h
  · simp_all
  split at h
  · simp_all [inBounds]
  split at h
  · simp_all [inBounds]
    omega
  split at h
  · simp_all [inBounds]
    omega
  split at h
  · simp_all [inBounds]
    omega
  split at h <;> simp_all [inBounds] <;> omega

/-- The guarded continuation reads shared by `_nextind_continued`, `iterate_continued`, and
`getindex_continued`. Every byte branch from the source is represented, including the lead-byte
width exits after the first and second continuation bytes. -/
def forwardContinuationAccesses
    (s : JuliaLean.Strings.JStr) (start : Int) (lead : UInt8) : List Int :=
  let n := s.bytes.length
  let i1 := start + 1
  if n < i1 then []
  else
    let b1 := JuliaLean.Strings.cu s (JInt.wrap .i64 i1)
    if !JuliaLean.Strings.isCont b1 then [i1]
    else
      let i2 := start + 2
      if n < i2 ∨ lead < 0xe0 then [i1]
      else
        let b2 := JuliaLean.Strings.cu s (JInt.wrap .i64 i2)
        if !JuliaLean.Strings.isCont b2 then [i1, i2]
        else
          let i3 := start + 3
          if n < i3 ∨ lead < 0xf0 then [i1, i2]
          else [i1, i2, i3]

theorem forwardContinuationAccesses_safe
    (s : JuliaLean.Strings.JStr) (start : Int) (lead : UInt8)
    (hs1 : 1 ≤ start) (_hsn : start ≤ s.bytes.length) (i : Int)
    (hi : i ∈ forwardContinuationAccesses s start lead) :
    inBounds s.bytes.length i := by
  simp only [forwardContinuationAccesses] at hi
  split at hi
  · simp_all
  split at hi
  · simp_all [inBounds]
    omega
  split at hi
  · simp_all [inBounds]
    omega
  split at hi
  · simp_all [inBounds]
    omega
  split at hi <;> simp_all [inBounds] <;> omega

/-- Exact byte trace of `_nextind_str` and `_nextind_continued`. The continuation-byte branch
uses the exact `thisZ` rewind computed by `thisind`; all source exits are preserved.
`base/strings/string.jl:276-305`. -/
def nextindAccesses (s : JuliaLean.Strings.JStr) (i : Int) : List Int :=
  let n := s.bytes.length
  if i = 0 then []
  else if i < 1 ∨ n < i then []
  else
    let lead := JuliaLean.Strings.cu s (JInt.wrap .i64 i)
    if !JuliaLean.Strings.between lead 0x80 0xf7 then [i]
    else if lead < 0xc0 then
      let rewind := JuliaLean.Strings.thisZ s i
      let rewindReads := thisindAccesses s i
      if i ≤ rewind then [i] ++ rewindReads
      else
        let rewindLead := JuliaLean.Strings.cu s (JInt.wrap .i64 rewind)
        if rewindLead < 0x80 ∨ 0xf8 ≤ rewindLead then [i] ++ rewindReads ++ [rewind]
        else [i] ++ rewindReads ++ [rewind] ++
          forwardContinuationAccesses s rewind rewindLead
    else [i] ++ forwardContinuationAccesses s i lead

theorem nextindAccesses_safe (s : JuliaLean.Strings.JStr) (i j : Int)
    (h : j ∈ nextindAccesses s i) : inBounds s.bytes.length j := by
  simp only [nextindAccesses] at h
  split at h
  · simp_all
  split at h
  · simp_all
  rename_i hi
  split at h
  · simp_all [inBounds]
  split at h
  · rename_i hcont
    have hi1 : 1 ≤ i := by omega
    have hz := JuliaLean.Strings.thisZ_range s i hi1
    split at h
    · rw [List.mem_append] at h
      rcases h with h | h
      · simp_all [inBounds]
      · exact thisindAccesses_safe s i j h
    · split at h
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with hprefix | hrewind
        · rcases hprefix with rfl | hthis
          · simp [inBounds]
            omega
          · exact thisindAccesses_safe s i j hthis
        · rw [hrewind]
          simp [inBounds]
          omega
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with hprefix | hforward
        · rcases hprefix with hbase | hrewind
          · rcases hbase with rfl | hthis
            · simp [inBounds]
              omega
            · exact thisindAccesses_safe s i j hthis
          · rw [hrewind]
            simp [inBounds]
            omega
        · exact forwardContinuationAccesses_safe s (JuliaLean.Strings.thisZ s i) _
            (by omega) (by omega) j hforward
  · rw [List.mem_append] at h
    rcases h with h | h
    · simp_all [inBounds]
    · exact forwardContinuationAccesses_safe s i _ (by omega) (by omega) j h

/-- Exact byte trace of `iterate(::Union{String,StringView}, i)` and its continuation helper.
`base/strings/string.jl:508-538`. -/
def iterateStringAccesses (s : JuliaLean.Strings.JStr) (i : Int) : List Int :=
  match checkedIndex s.bytes.length i with
  | none => []
  | some j =>
      let lead := JuliaLean.Strings.cu s (JInt.wrap .i64 j)
      if !JuliaLean.Strings.between lead 0x80 0xf7 ∨ lead < 0xc0 then [j]
      else [j] ++ forwardContinuationAccesses s j lead

theorem iterateStringAccesses_safe (s : JuliaLean.Strings.JStr) (i j : Int)
    (h : j ∈ iterateStringAccesses s i) : inBounds s.bytes.length j := by
  simp only [iterateStringAccesses] at h
  split at h
  · simp_all
  rename_i index hi
  unfold checkedIndex at hi
  split at hi
  · rename_i hb
    cases hi
    split at h
    · simp_all [inBounds]
    · rw [List.mem_append] at h
      rcases h with h | h
      · simp_all [inBounds]
      · exact forwardContinuationAccesses_safe s i _ (by omega) (by omega) j h
  · simp_all

/-- Exact byte trace of checked String `getindex` and `getindex_continued`, including the
invalid-continuation call to `isvalid`. `base/strings/string.jl:540-573`. -/
def getindexStringAccesses (s : JuliaLean.Strings.JStr) (i : Int) : List Int :=
  match checkedIndex s.bytes.length i with
  | none => []
  | some j =>
      let lead := JuliaLean.Strings.cu s (JInt.wrap .i64 j)
      if !JuliaLean.Strings.between lead 0x80 0xf7 then [j]
      else if lead < 0xc0 then [j] ++ thisindAccesses s j
      else [j] ++ forwardContinuationAccesses s j lead

theorem getindexStringAccesses_safe (s : JuliaLean.Strings.JStr) (i j : Int)
    (h : j ∈ getindexStringAccesses s i) : inBounds s.bytes.length j := by
  simp only [getindexStringAccesses] at h
  split at h
  · simp_all
  rename_i index hi
  unfold checkedIndex at hi
  split at hi
  · rename_i hb
    cases hi
    split at h
    · simp_all [inBounds]
    · split at h
      · rw [List.mem_append] at h
        rcases h with h | h
        · simp_all [inBounds]
        · exact thisindAccesses_safe s i j h
      · rw [List.mem_append] at h
        rcases h with h | h
        · simp_all [inBounds]
        · exact forwardContinuationAccesses_safe s i _ (by omega) (by omega) j h
  · simp_all

/-- Physical StringView access. A view constructed from parent offset `offset` and byte length
`len` first checks `offset+len ≤ parentLen`; a checked local index then maps to
`offset+i`. This is the representation invariant used by the union methods above. -/
def stringViewAccess
    (parentLen offset len : Nat) (i : Int) : Option Int :=
  if offset + len ≤ parentLen then
    match checkedIndex len i with
    | some j => some (offset + j)
    | none => none
  else none

def StringViewAccessesInBounds : Prop :=
  ∀ parentLen offset len i j,
    stringViewAccess parentLen offset len i = some j → inBounds parentLen j

theorem stringViewAccessesInBounds_proven : StringViewAccessesInBounds := by
  intro parentLen offset len i j h
  unfold stringViewAccess checkedIndex at h
  split at h
  · split at h <;> simp_all [inBounds] <;> omega
  · simp_all

/-! ## String ranges, first/last, storage, DFA, and character repetition -/

/-- `getindex(s::String, i:j)` after its nonempty, bounds, and validity checks. The source
end becomes `nextind(s,j)-1`, so the copied byte count is `nextZ(s,j)-i`.
`base/strings/string.jl:580-594`. -/
def stringRangeAccesses (s : JuliaLean.Strings.JStr) (i j : Int) : List Int :=
  let n := s.bytes.length
  if i ≤ j ∧ 1 ≤ i ∧ j ≤ n ∧
      JuliaLean.Strings.thisZ s i = i ∧ JuliaLean.Strings.thisZ s j = j then
    span i.toNat (JuliaLean.Strings.nextZ s j - i).toNat
  else []

def StringRangeAccessesInBounds : Prop :=
  ∀ s i j k, k ∈ stringRangeAccesses s i j → inBounds s.bytes.length k

theorem stringRangeAccessesInBounds_proven : StringRangeAccessesInBounds := by
  intro s i j k hk
  simp only [stringRangeAccesses] at hk
  split at hk
  · rename_i h
    obtain ⟨d, hd, rfl⟩ := mem_span hk
    have hn := JuliaLean.Strings.nextZ_spec s j (by omega) (by omega)
    have hiNat : i.toNat = i := by omega
    rw [hiNat]
    simp [inBounds]
    omega
  · simp_all

/-- Safe `Vector{UInt8}(s::AbstractString)` first constructs an owned String of exactly
`ncodeunits(String(s))` bytes, then exposes precisely those bytes (`basic.jl:220-221`,
`string.jl:187-200`). -/
def stringStorageAccesses (bytes : List UInt8) : Nat × List Int :=
  (bytes.length, span 1 bytes.length)

def StringStorageAccessesInBounds : Prop :=
  ∀ bytes i, i ∈ (stringStorageAccesses bytes).2 →
    inBounds (stringStorageAccesses bytes).1 i

theorem stringStorageAccessesInBounds_proven : StringStorageAccessesInBounds := by
  intro bytes i hi
  obtain ⟨k, hk, rfl⟩ := mem_span hi
  simp [stringStorageAccesses, inBounds]
  omega

/-- `_utf_dfa_step` indexes its 256-entry table by the exact `UInt8` expression `byte+1`.
The vector read in `_isvalid_utf8_dfa` is the caller-computed inclusive chunk. -/
def utfDfaTableIndex (byte : UInt8) : Nat := byte.toNat + 1

def utfDfaChunkAccesses (len first last : Nat) : List Int :=
  if 1 ≤ first ∧ first ≤ last + 1 ∧ last ≤ len then
    if first ≤ last then span first (last + 1 - first) else []
  else []

def Utf8DfaAccessesInBounds : Prop :=
  (∀ byte, 1 ≤ utfDfaTableIndex byte ∧ utfDfaTableIndex byte ≤ 256) ∧
  (∀ len first last i, i ∈ utfDfaChunkAccesses len first last → inBounds len i)

theorem utf8DfaAccessesInBounds_proven : Utf8DfaAccessesInBounds := by
  constructor
  · intro byte
    unfold utfDfaTableIndex
    have hb := byte.toNat_lt
    omega
  · intro len first last i hi
    unfold utfDfaChunkAccesses at hi
    split at hi
    · rename_i hc
      split at hi
      · obtain ⟨k, hk, rfl⟩ := mem_span hi
        simp [inBounds]
        omega
      · simp_all
    · simp_all

def repeatCharWidth (u : Nat) : Nat :=
  if u < 2 ^ 8 then 1 else if u < 2 ^ 16 then 2 else if u < 2 ^ 24 then 3 else 4

/-- The stores at `base/strings/string.jl:682-713`, after the negative, zero, and overflow
branches. Widths two and four use typed pointers, so their element index is `i`; width three
uses byte indices `3i+1:3i+3`. This byte-level trace is equivalent for all four branches. -/
def repeatCharAccesses (encoded : UInt32) (copies : Nat) : Nat × List Int :=
  let width := repeatCharWidth (JuliaLean.Strings.bswap32 encoded).toNat
  let allocated := width * copies
  (allocated, (List.range copies).flatMap fun copy => span (width * copy + 1) width)

def RepeatCharAccessesInBounds : Prop :=
  ∀ encoded copies i, i ∈ (repeatCharAccesses encoded copies).2 →
    inBounds (repeatCharAccesses encoded copies).1 i

theorem repeatCharAccessesInBounds_proven : RepeatCharAccessesInBounds := by
  intro encoded copies i hi
  unfold repeatCharAccesses at hi ⊢
  rw [List.mem_flatMap] at hi
  obtain ⟨copy, hc, hi⟩ := hi
  have hc' := List.mem_range.mp hc
  obtain ⟨lane, hl, rfl⟩ := mem_span hi
  let u := (JuliaLean.Strings.bswap32 encoded).toNat
  by_cases h8 : u < 2 ^ 8
  · simp [repeatCharWidth, u, h8, inBounds] at hl ⊢
    omega
  · by_cases h16 : u < 2 ^ 16
    · simp [repeatCharWidth, u, h8, h16, inBounds] at hl ⊢
      omega
    · by_cases h24 : u < 2 ^ 24
      · simp [repeatCharWidth, u, h8, h16, h24, inBounds] at hl ⊢
        omega
      · simp [repeatCharWidth, u, h8, h16, h24, inBounds] at hl ⊢
        omega
end JuliaLean.MemSafety.G6
end
