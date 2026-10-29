import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk2

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection24 : WitnessProjection :=
  projectedRun canonicalSuspendProjection16 (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection24_run :
    projectedRun canonicalSuspendProjection16 (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection24 := rfl

set_option maxRecDepth 50000 in
theorem canonicalSuspendProjection24_supported :
    witnessRunSupported canonicalSuspendProjection16 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
