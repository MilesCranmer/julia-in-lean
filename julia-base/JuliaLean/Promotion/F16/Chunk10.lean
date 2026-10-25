import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk80 : chunkOk 80 = true := by decide +kernel
theorem chunk81 : chunkOk 81 = true := by decide +kernel
theorem chunk82 : chunkOk 82 = true := by decide +kernel
theorem chunk83 : chunkOk 83 = true := by decide +kernel
theorem chunk84 : chunkOk 84 = true := by decide +kernel
theorem chunk85 : chunkOk 85 = true := by decide +kernel
theorem chunk86 : chunkOk 86 = true := by decide +kernel
theorem chunk87 : chunkOk 87 = true := by decide +kernel

end JuliaLean.Promotion.F16
