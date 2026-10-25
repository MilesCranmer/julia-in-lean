import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk32 : chunkOk 32 = true := by decide +kernel
theorem chunk33 : chunkOk 33 = true := by decide +kernel
theorem chunk34 : chunkOk 34 = true := by decide +kernel
theorem chunk35 : chunkOk 35 = true := by decide +kernel
theorem chunk36 : chunkOk 36 = true := by decide +kernel
theorem chunk37 : chunkOk 37 = true := by decide +kernel
theorem chunk38 : chunkOk 38 = true := by decide +kernel
theorem chunk39 : chunkOk 39 = true := by decide +kernel

end JuliaLean.Promotion.F16
