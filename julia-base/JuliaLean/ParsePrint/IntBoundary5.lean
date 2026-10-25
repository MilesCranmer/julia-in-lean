import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_u128_10 : ∀ c ∈ centers .u128, ∀ k : Fin 33, nearOK .u128 10 c k = true := by
  decide +kernel
theorem near_u128_16 : ∀ c ∈ centers .u128, ∀ k : Fin 33, nearOK .u128 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
