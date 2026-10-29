import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk3

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection32 : WitnessProjection :=
  projectedRun canonicalSuspendProjection24 (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection32_run :
    projectedRun canonicalSuspendProjection24 (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection32 := rfl

set_option maxRecDepth 50000 in
theorem canonicalSuspendProjection32_supported :
    witnessRunSupported canonicalSuspendProjection24 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
