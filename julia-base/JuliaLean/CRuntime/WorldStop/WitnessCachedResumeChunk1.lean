import JuliaLean.CRuntime.WorldStop.WitnessCachedTarget

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalCachedResumeProjection08 : WitnessProjection :=
  projectedRun canonicalTargetCachedProjection (List.replicate 8 (.source 2 {}))

theorem canonicalCachedResumeProjection08_run :
    projectedRun canonicalTargetCachedProjection (List.replicate 8 (.source 2 {})) =
      canonicalCachedResumeProjection08 := rfl

theorem canonicalCachedResumeProjection08_supported :
    witnessRunSupported canonicalTargetCachedProjection (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
