import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk4

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection40 : WitnessProjection :=
  projectedRun canonicalCollectProjection32 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection40_run :
    projectedRun canonicalCollectProjection32 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection40 := rfl

theorem canonicalCollectProjection40_supported :
    witnessRunSupported canonicalCollectProjection32 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
