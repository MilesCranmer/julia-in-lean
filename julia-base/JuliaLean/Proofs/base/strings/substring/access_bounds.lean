import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- A valid `SubString` view and every checked code-unit index remain inside the parent;
the second conjunct is the nested `raw_substring` offset calculation;
`base/strings/substring.jl:71-171`. -/
def SubstringBounds : Prop :=
  (∀ parent offset length index : Nat, offset + length ≤ parent →
    1 ≤ index → index ≤ length → Access parent (offset + index) 1) ∧
  (∀ parent offset length first count : Nat, offset + length ≤ parent →
    1 ≤ first → first - 1 + count ≤ length →
    Access parent (offset + first) count)

/-- `_string` writes each value into its allocated prefix and string repetition writes
copy `i` into the `i`th block; `base/strings/substring.jl:215-303`. -/
def StringWriteBounds : Prop :=
  (∀ total prefixLength width : Nat, prefixLength + width ≤ total →
    Access total (prefixLength + 1) width) ∧
  (∀ width count index : Nat, index < count →
    Access (width * count) (index * width + 1) width)

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

end JuliaLean.MemSafety.G1
