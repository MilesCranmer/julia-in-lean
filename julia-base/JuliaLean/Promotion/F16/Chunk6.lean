import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk48 : chunkOk 48 = true := by decide +kernel
theorem chunk49 : chunkOk 49 = true := by decide +kernel
theorem chunk50 : chunkOk 50 = true := by decide +kernel
theorem chunk51 : chunkOk 51 = true := by decide +kernel
theorem chunk52 : chunkOk 52 = true := by decide +kernel
theorem chunk53 : chunkOk 53 = true := by decide +kernel
theorem chunk54 : chunkOk 54 = true := by decide +kernel
theorem chunk55 : chunkOk 55 = true := by decide +kernel

end JuliaLean.Promotion.F16
