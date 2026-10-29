import JuliaLean.CRuntime.WorldStop.WitnessCachedResumeChunk1

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalCachedResumeProjection16 : WitnessProjection :=
  projectedRun canonicalCachedResumeProjection08 (List.replicate 8 (.source 2 {}))

theorem canonicalCachedResumeProjection16_run :
    projectedRun canonicalCachedResumeProjection08 (List.replicate 8 (.source 2 {})) =
      canonicalCachedResumeProjection16 := rfl

theorem canonicalCachedResumeProjection16_supported :
    witnessRunSupported canonicalCachedResumeProjection08 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
