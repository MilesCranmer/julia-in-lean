import JuliaLean.Proofs.base.array.common
import JuliaLean.Proofs.base.strings.string.access_bounds


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## Regex and annotated-string spans -/

def pcreOvectorLength (captures : Nat) : Nat := 2 * (captures + 1)

def pcreMatchCaptureCount (captures : Nat) : Nat := pcreOvectorLength captures / 2 - 1

/-- The unsafe slot loads in `match` and `_findnext_re` at
`base/regex.jl:430-451,491-511`. PCRE supplies `2(captures+1)` slots; Julia recomputes
`n = ovec_length/2-1`, reads the whole-match pair, then four occurrences of the capture pair
for each `i=1:n`. -/
def pcreOvectorReads (captures : Nat) : List Nat :=
  [1, 2] ++ (List.range (pcreMatchCaptureCount captures)).flatMap fun k =>
    let i := k + 1
    [2 * i + 1, 2 * i + 2, 2 * i + 1, 2 * i + 2, 2 * i + 1]

def RegexOvectorAccessesInBounds : Prop :=
  ∀ captures slot, slot ∈ pcreOvectorReads captures →
    1 ≤ slot ∧ slot ≤ pcreOvectorLength captures

theorem regexOvectorAccessesInBounds_proven : RegexOvectorAccessesInBounds := by
  intro captures slot hs
  unfold pcreOvectorReads at hs
  rw [List.mem_append] at hs
  rcases hs with hs | hs
  · simp at hs
    rcases hs with rfl | rfl <;> simp [pcreOvectorLength] <;> omega
  · rw [List.mem_flatMap] at hs
    obtain ⟨k, hk, hs⟩ := hs
    have hk' := List.mem_range.mp hk
    simp [pcreMatchCaptureCount, pcreOvectorLength] at hk'
    simp at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
      simp [pcreOvectorLength] <;> omega

/-- A successful PCRE span is a zero-based half-open byte interval in its subject. The match,
capture, `_annotatedmatch`, and `_findnext_re` paths convert it to Julia's one-based indices.
`base/regex.jl:441-461,506`. -/
def pcreSpanAccesses (subjectLen start stop : Nat) : List Int :=
  if start ≤ stop ∧ stop ≤ subjectLen then span (start + 1) (stop - start) else []

/-- `count(pattern, s)` calls `nextind(s,j)` only after the returned match endpoint satisfies
`j ≤ lastindex(s)` (`base/regex.jl:573-583`). -/
def regexCountNextindAccesses
    (s : JuliaLean.Strings.JStr) (matchStop : Int) : List Int :=
  if 1 ≤ matchStop ∧ matchStop ≤ JuliaLean.Strings.thisZ s s.bytes.length then
    nextindAccesses s matchStop
  else []

def RegexSpanAccessesInBounds : Prop :=
  (∀ subjectLen start stop i, i ∈ pcreSpanAccesses subjectLen start stop →
    inBounds subjectLen i) ∧
  (∀ s matchStop i, i ∈ regexCountNextindAccesses s matchStop →
    inBounds s.bytes.length i)

theorem regexSpanAccessesInBounds_proven : RegexSpanAccessesInBounds := by
  constructor
  · intro subjectLen start stop i hi
    unfold pcreSpanAccesses at hi
    split at hi
    · rename_i hspan
      obtain ⟨k, hk, rfl⟩ := mem_span hi
      simp [inBounds]
      omega
    · simp_all
  · intro s matchStop i hi
    unfold regexCountNextindAccesses at hi
    split at hi
    · exact nextindAccesses_safe s matchStop i hi
    · simp_all
end JuliaLean.MemSafety.G6
end
