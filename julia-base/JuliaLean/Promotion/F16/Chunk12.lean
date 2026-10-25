import JuliaLean.Promotion.F16.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.Promotion.F16

theorem chunk96 : chunkOk 96 = true := by decide +kernel
theorem chunk97 : chunkOk 97 = true := by decide +kernel
theorem chunk98 : chunkOk 98 = true := by decide +kernel
theorem chunk99 : chunkOk 99 = true := by decide +kernel
theorem chunk100 : chunkOk 100 = true := by decide +kernel
theorem chunk101 : chunkOk 101 = true := by decide +kernel
theorem chunk102 : chunkOk 102 = true := by decide +kernel
theorem chunk103 : chunkOk 103 = true := by decide +kernel

end JuliaLean.Promotion.F16
