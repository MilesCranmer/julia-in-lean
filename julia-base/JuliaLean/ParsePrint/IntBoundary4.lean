import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_i64_10 : ∀ c ∈ centers .i64, ∀ k : Fin 33, nearOK .i64 10 c k = true := by
  decide +kernel
theorem near_i64_16 : ∀ c ∈ centers .i64, ∀ k : Fin 33, nearOK .i64 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
