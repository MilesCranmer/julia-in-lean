import JuliaLean.CRuntime.WorldStop.WitnessSuspend

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection08 : WitnessProjection :=
  projectedRun canonicalSuspendedProjection (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection08_run :
    projectedRun canonicalSuspendedProjection (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection08 := rfl

theorem canonicalCollectProjection08_supported :
    witnessRunSupported canonicalSuspendedProjection (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
