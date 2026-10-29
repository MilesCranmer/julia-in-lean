import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk2

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection24 : WitnessProjection :=
  projectedRun canonicalCollectProjection16 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection24_run :
    projectedRun canonicalCollectProjection16 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection24 := rfl

theorem canonicalCollectProjection24_supported :
    witnessRunSupported canonicalCollectProjection16 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
