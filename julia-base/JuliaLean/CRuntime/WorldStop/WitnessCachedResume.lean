import JuliaLean.CRuntime.WorldStop.WitnessCachedResumeChunk2

namespace JuliaLean.CRuntime.WorldStop

def canonicalResumedProjection : WitnessProjection := canonicalCachedResumeProjection16

theorem canonicalResumedProjection_run :
    projectedRun canonicalTargetCachedProjection
      (List.replicate 8 (.source 2 {}) ++ List.replicate 8 (.source 2 {})) =
      canonicalResumedProjection := by
  rw [projectedRun_append]
  rw [canonicalCachedResumeProjection08_run, canonicalCachedResumeProjection16_run]
  rfl

theorem canonicalResumedProjection_supported :
    witnessRunSupported canonicalTargetCachedProjection
      (List.replicate 8 (.source 2 {}) ++ List.replicate 8 (.source 2 {})) = true := by
  apply witnessRunSupported_append
  · exact canonicalCachedResumeProjection08_supported
  · rw [canonicalCachedResumeProjection08_run]
    exact canonicalCachedResumeProjection16_supported

end JuliaLean.CRuntime.WorldStop
