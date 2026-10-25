import JuliaLean.ParsePrint.IntBoundaryDefs

/-! Near-boundary parse checks; see `IntBoundaryDefs`. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem near_i32_10 : ∀ c ∈ centers .i32, ∀ k : Fin 33, nearOK .i32 10 c k = true := by
  decide +kernel
theorem near_i32_16 : ∀ c ∈ centers .i32, ∀ k : Fin 33, nearOK .i32 16 c k = true := by
  decide +kernel
theorem near_u64_10 : ∀ c ∈ centers .u64, ∀ k : Fin 33, nearOK .u64 10 c k = true := by
  decide +kernel
theorem near_u64_16 : ∀ c ∈ centers .u64, ∀ k : Fin 33, nearOK .u64 16 c k = true := by
  decide +kernel

end JuliaLean.ParsePrint.IntParse
