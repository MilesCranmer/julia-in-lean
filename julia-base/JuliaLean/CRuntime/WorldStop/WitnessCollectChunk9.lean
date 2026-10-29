import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk8

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection72 : WitnessProjection :=
  projectedRun canonicalCollectProjection64 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection72_run :
    projectedRun canonicalCollectProjection64 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection72 := rfl

theorem canonicalCollectProjection72_supported :
    witnessRunSupported canonicalCollectProjection64 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
