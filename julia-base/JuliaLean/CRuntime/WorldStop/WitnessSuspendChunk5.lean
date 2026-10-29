import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk4

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection40 : WitnessProjection :=
  projectedRun canonicalSuspendProjection32 (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection40_run :
    projectedRun canonicalSuspendProjection32 (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection40 := rfl

set_option maxRecDepth 50000 in
theorem canonicalSuspendProjection40_supported :
    witnessRunSupported canonicalSuspendProjection32 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
