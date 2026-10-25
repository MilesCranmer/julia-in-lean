import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk64 : chunkOk 64 = true := by decide +kernel
theorem chunk65 : chunkOk 65 = true := by decide +kernel
theorem chunk66 : chunkOk 66 = true := by decide +kernel
theorem chunk67 : chunkOk 67 = true := by decide +kernel
theorem chunk68 : chunkOk 68 = true := by decide +kernel
theorem chunk69 : chunkOk 69 = true := by decide +kernel
theorem chunk70 : chunkOk 70 = true := by decide +kernel
theorem chunk71 : chunkOk 71 = true := by decide +kernel

end JuliaLean.Promotion.F16
