import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk1

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection16 : WitnessProjection :=
  projectedRun canonicalSuspendProjection08 (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection16_run :
    projectedRun canonicalSuspendProjection08 (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection16 := rfl

theorem canonicalSuspendProjection16_supported :
    witnessRunSupported canonicalSuspendProjection08 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
