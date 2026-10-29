import JuliaLean.CRuntime.WorldStop.WitnessSetup

namespace JuliaLean.CRuntime.WorldStop

def canonicalSuspendProjection08 : WitnessProjection :=
  projectedRun canonicalInitialProjection (List.replicate 8 (.source 2 {}))

theorem canonicalSuspendProjection08_run :
    projectedRun canonicalInitialProjection (List.replicate 8 (.source 2 {})) =
      canonicalSuspendProjection08 := rfl

theorem canonicalSuspendProjection08_supported :
    witnessRunSupported canonicalInitialProjection (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
