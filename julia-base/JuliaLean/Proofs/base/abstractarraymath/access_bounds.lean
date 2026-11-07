import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- Componentwise bounds used by `repeat_outer` and `repeat_inner`; these are the two
index formulas at `base/abstractarraymath.jl:559-611`. -/
def RepeatBounds : Prop :=
  (∀ size count j : Nat, j < count → Access (size * count) (j * size + 1) size) ∧
  (∀ size count i j : Nat, i < size → j < count →
    Access (size * count) (i * count + j + 1) 1)

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

end JuliaLean.MemSafety.G1
