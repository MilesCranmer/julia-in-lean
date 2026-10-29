import JuliaLean.CRuntime.WorldStop.WitnessResume

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalTargetCachedProjection : WitnessProjection :=
  projectedRun canonicalCheckpointProjection (List.replicate 8 (.source 1 {}))

theorem canonicalTargetCachedProjection_run :
    projectedRun canonicalCheckpointProjection (List.replicate 8 (.source 1 {})) =
      canonicalTargetCachedProjection := rfl

theorem canonicalTargetCachedProjection_supported :
    witnessRunSupported canonicalCheckpointProjection (List.replicate 8 (.source 1 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
