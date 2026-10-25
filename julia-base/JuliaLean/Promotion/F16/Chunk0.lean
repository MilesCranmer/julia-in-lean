import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk0 : chunkOk 0 = true := by decide +kernel
theorem chunk1 : chunkOk 1 = true := by decide +kernel
theorem chunk2 : chunkOk 2 = true := by decide +kernel
theorem chunk3 : chunkOk 3 = true := by decide +kernel
theorem chunk4 : chunkOk 4 = true := by decide +kernel
theorem chunk5 : chunkOk 5 = true := by decide +kernel
theorem chunk6 : chunkOk 6 = true := by decide +kernel
theorem chunk7 : chunkOk 7 = true := by decide +kernel

end JuliaLean.Promotion.F16
