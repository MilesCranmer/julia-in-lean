import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk8 : chunkOk 8 = true := by decide +kernel
theorem chunk9 : chunkOk 9 = true := by decide +kernel
theorem chunk10 : chunkOk 10 = true := by decide +kernel
theorem chunk11 : chunkOk 11 = true := by decide +kernel
theorem chunk12 : chunkOk 12 = true := by decide +kernel
theorem chunk13 : chunkOk 13 = true := by decide +kernel
theorem chunk14 : chunkOk 14 = true := by decide +kernel
theorem chunk15 : chunkOk 15 = true := by decide +kernel

end JuliaLean.Promotion.F16
