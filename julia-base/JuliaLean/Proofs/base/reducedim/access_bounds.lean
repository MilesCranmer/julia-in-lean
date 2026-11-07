import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

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

end JuliaLean.MemSafety.G1
