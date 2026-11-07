import JuliaLean.Proofs.base.strings.string.memory_safety

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- The two checked constructor calls at `base/strings/substring.jl:76-84`.
The empty-range branch returns first; the other branch checks the range before
calling `isvalid` at its two computed endpoints. -/
def substringConstructorAccesses (parentLength : Nat) (i j : Int) : List Access :=
  if i ≤ j ∧ 1 ≤ i ∧ j ≤ parentLength then
    stringIsvalidAccesses parentLength i ++ stringIsvalidAccesses parentLength j
  else []

def SubstringConstructorInBounds : Prop :=
  ∀ parentLength i j, accessesSafe (substringConstructorAccesses parentLength i j)

theorem substringConstructorInBounds_proven : SubstringConstructorInBounds := by
  intro parentLength i j a ha
  simp only [substringConstructorAccesses] at ha
  split at ha
  · simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · exact stringIsvalidInBounds_proven parentLength i a ha
    · exact stringIsvalidInBounds_proven parentLength j a ha
  · simp at ha

structure SubView where
  parentLength : Nat
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq

/-- The representation invariant stated at `base/strings/substring.jl:142-143`. -/
def SubView.valid (s : SubView) : Prop := s.offset + s.length ≤ s.parentLength

/-- `SubString(s) = raw_substring(s, 1, ncodeunits(s))`, line 117, computes the
whole parent span. -/
def wholeSubstringAccess (parentLength : Nat) : List Access :=
  [span0 parentLength 0 parentLength]

/-- `codeunit`, `getindex`, and `isvalid` for SubString,
`base/strings/substring.jl:146-171`.  The SubString check is executed before
adding its stored offset to the caller's index. -/
def subViewAccesses (s : SubView) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ s.length then
    let parentIndex : Int := s.offset + i
    at0 s.parentLength (parentIndex - 1).toNat ::
      stringIsvalidAccesses s.parentLength parentIndex
  else []

def SubstringIndexInBounds : Prop :=
  SubstringConstructorInBounds ∧
  (∀ parentLength, accessesSafe (wholeSubstringAccess parentLength)) ∧
  ∀ s, s.valid → ∀ i, accessesSafe (subViewAccesses s i)

theorem substringIndexInBounds_proven : SubstringIndexInBounds := by
  refine ⟨substringConstructorInBounds_proven, ?_, ?_⟩
  · intro parentLength
    simp [wholeSubstringAccess, accessesSafe, Access.safe, span0]
  · intro s hs i
    unfold SubView.valid at hs
    unfold subViewAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [Access.safe, at0]
        have hc : (((s.offset : Int) + i - 1).toNat : Int) = s.offset + i - 1 :=
          Int.toNat_of_nonneg (by omega)
        omega
      · exact stringIsvalidInBounds_proven s.parentLength (s.offset + i) a ha
    · simp

/-- String repetition, `base/strings/substring.jl:289-306`.  The checked
`n*r` allocation is partitioned into `r` blocks; the one-byte branch reads the
only source byte and fills the same allocation. -/
def repeatStringAccesses (width count : Nat) : List Access :=
  if count = 0 ∨ width = 0 then []
  else if width = 1 then [at0 width 0, span0 count 0 count]
  else (List.range count).map fun j => span0 (width * count) (j * width) width

def RepeatStringInBounds : Prop :=
  ∀ width count, accessesSafe (repeatStringAccesses width count)

theorem repeatStringInBounds_proven : RepeatStringInBounds := by
  intro width count
  unfold repeatStringAccesses
  split
  · simp [accessesSafe]
  · split
    · simp [accessesSafe, Access.safe, at0, span0, *]
    · intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      simp only [List.mem_range] at hj
      simp only [Access.safe, span0]
      have hm := Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr hj)
      simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using hm

/-- The two `_string` loops, `base/strings/substring.jl:215-283`.  `widths`
are the `ncodeunits`/`sizeof` values selected by the first type-dispatch loop;
the second loop uses the same dispatch and advances `offs` by each returned
width. -/
def stringBuildTrace (capacity : Nat) : Nat → List Nat → List Access
  | _, [] => []
  | offset, width :: rest =>
      span0 capacity offset width :: stringBuildTrace capacity (offset + width) rest

private theorem stringBuildTrace_safe (capacity offset : Nat) (widths : List Nat)
    (h : offset + widths.sum ≤ capacity) :
    accessesSafe (stringBuildTrace capacity offset widths) := by
  induction widths generalizing offset with
  | nil => simp [stringBuildTrace, accessesSafe]
  | cons width rest ih =>
      simp only [stringBuildTrace, accessesSafe, List.mem_cons, forall_eq_or_imp,
        List.sum_cons] at h ⊢
      constructor
      · simp [Access.safe, span0]
        omega
      · apply ih
        omega

def stringBuildAccesses (widths : List Nat) : List Access :=
  let total := widths.sum
  if total ≤ 2 ^ 63 - 1 then stringBuildTrace total 0 widths else []

def StringBuildInBounds : Prop := ∀ widths,
  accessesSafe (stringBuildAccesses widths)

theorem stringBuildInBounds_proven : StringBuildInBounds := by
  intro widths
  unfold stringBuildAccesses
  dsimp
  split
  · apply stringBuildTrace_safe
    omega
  · simp [accessesSafe]

end JuliaLean.MemSafety.G1
