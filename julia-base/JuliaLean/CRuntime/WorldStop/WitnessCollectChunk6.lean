import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk5

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection48 : WitnessProjection :=
  projectedRun canonicalCollectProjection40 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection48_run :
    projectedRun canonicalCollectProjection40 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection48 := rfl

theorem canonicalCollectProjection48_supported :
    witnessRunSupported canonicalCollectProjection40 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
