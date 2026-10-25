import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_u8_10 : ∀ c ∈ centers .u8, ∀ k : Fin 33, nearOK .u8 10 c k = true := by
  decide +kernel
theorem near_u8_16 : ∀ c ∈ centers .u8, ∀ k : Fin 33, nearOK .u8 16 c k = true := by
  decide +kernel
theorem near_i8_10 : ∀ c ∈ centers .i8, ∀ k : Fin 33, nearOK .i8 10 c k = true := by
  decide +kernel
theorem near_i8_16 : ∀ c ∈ centers .i8, ∀ k : Fin 33, nearOK .i8 16 c k = true := by
  decide +kernel
theorem near_u16_10 : ∀ c ∈ centers .u16, ∀ k : Fin 33, nearOK .u16 10 c k = true := by
  decide +kernel
theorem near_u16_16 : ∀ c ∈ centers .u16, ∀ k : Fin 33, nearOK .u16 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
