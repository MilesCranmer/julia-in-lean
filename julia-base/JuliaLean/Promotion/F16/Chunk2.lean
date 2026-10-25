import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk16 : chunkOk 16 = true := by decide +kernel
theorem chunk17 : chunkOk 17 = true := by decide +kernel
theorem chunk18 : chunkOk 18 = true := by decide +kernel
theorem chunk19 : chunkOk 19 = true := by decide +kernel
theorem chunk20 : chunkOk 20 = true := by decide +kernel
theorem chunk21 : chunkOk 21 = true := by decide +kernel
theorem chunk22 : chunkOk 22 = true := by decide +kernel
theorem chunk23 : chunkOk 23 = true := by decide +kernel

end JuliaLean.Promotion.F16
