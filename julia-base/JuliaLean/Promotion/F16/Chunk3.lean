import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk24 : chunkOk 24 = true := by decide +kernel
theorem chunk25 : chunkOk 25 = true := by decide +kernel
theorem chunk26 : chunkOk 26 = true := by decide +kernel
theorem chunk27 : chunkOk 27 = true := by decide +kernel
theorem chunk28 : chunkOk 28 = true := by decide +kernel
theorem chunk29 : chunkOk 29 = true := by decide +kernel
theorem chunk30 : chunkOk 30 = true := by decide +kernel
theorem chunk31 : chunkOk 31 = true := by decide +kernel

end JuliaLean.Promotion.F16
