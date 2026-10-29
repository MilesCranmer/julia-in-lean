import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk5

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection48 : WitnessProjection :=
  projectedRun canonicalSuspendProjection40 (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection48_run :
    projectedRun canonicalSuspendProjection40 (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection48 := rfl

set_option maxRecDepth 50000 in
theorem canonicalSuspendProjection48_supported :
    witnessRunSupported canonicalSuspendProjection40 (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
