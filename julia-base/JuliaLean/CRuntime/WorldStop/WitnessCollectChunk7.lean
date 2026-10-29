import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk6

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection56 : WitnessProjection :=
  projectedRun canonicalCollectProjection48 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection56_run :
    projectedRun canonicalCollectProjection48 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection56 := rfl

theorem canonicalCollectProjection56_supported :
    witnessRunSupported canonicalCollectProjection48 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
