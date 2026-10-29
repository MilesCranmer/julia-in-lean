import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk1

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection16 : WitnessProjection :=
  projectedRun canonicalCollectProjection08 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection16_run :
    projectedRun canonicalCollectProjection08 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection16 := rfl

theorem canonicalCollectProjection16_supported :
    witnessRunSupported canonicalCollectProjection08 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
