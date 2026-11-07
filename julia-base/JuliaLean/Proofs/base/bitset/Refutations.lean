import JuliaLean.Proofs.base.bitset.Properties

namespace JuliaLean.BitArrays

/-- `symdiff!(BitSet([1]), [2, 2])` toggles `2` twice and returns `BitSet([1])`;
`symdiff!(Set([1]), [2, 2])` returns `Set([1, 2])`. -/
theorem bitsetSymdiffDuplicate :
    ((BitSetS.ofList [JInt.lit .i64 1]).symdiff [JInt.lit .i64 2, JInt.lit .i64 2]).contains (JInt.lit .i64 2) = false := by
  decide

theorem bitSetSymdiffAgrees_refuted : ¬ BitSetSymdiffAgrees := by
  intro h
  have := h [JInt.lit .i64 1] [JInt.lit .i64 2, JInt.lit .i64 2] (JInt.lit .i64 2)
  rw [bitsetSymdiffDuplicate] at this
  exact absurd this (by decide)
end JuliaLean.BitArrays
