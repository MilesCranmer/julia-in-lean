import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_i128_10 : ∀ c ∈ centers .i128, ∀ k : Fin 33, nearOK .i128 10 c k = true := by
  decide +kernel
theorem near_i128_16 : ∀ c ∈ centers .i128, ∀ k : Fin 33, nearOK .i128 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
