import JuliaLean.Proofs.base.accumulate.Contracts

namespace JuliaLean.Reduce

/-- A dimension beyond the vector rank applies the initializer to every element. -/
theorem accumulateDimsInit_proven : AccumulateDimsInit := by
  intro v init d hd
  simp [accumulateVecDims, show ¬ d ≤ 0 by omega, show d > 1 by omega]

/-- `cumsum([1]; dims = 0) == [1]`, `accumulate(+, [1]; dims = 0)` throws. -/
theorem cumsumAccumulate_refuted : ¬ CumsumAccumulate := by
  intro h
  have := h [JInt.lit .i64 1] 0
  revert this
  decide

end JuliaLean.Reduce
