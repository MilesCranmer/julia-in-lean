import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_i16_10 : ∀ c ∈ centers .i16, ∀ k : Fin 33, nearOK .i16 10 c k = true := by
  decide +kernel
theorem near_i16_16 : ∀ c ∈ centers .i16, ∀ k : Fin 33, nearOK .i16 16 c k = true := by
  decide +kernel
theorem near_u32_10 : ∀ c ∈ centers .u32, ∀ k : Fin 33, nearOK .u32 10 c k = true := by
  decide +kernel
theorem near_u32_16 : ∀ c ∈ centers .u32, ∀ k : Fin 33, nearOK .u32 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
