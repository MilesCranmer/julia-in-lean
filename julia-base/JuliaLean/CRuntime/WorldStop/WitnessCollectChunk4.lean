import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk3

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection32 : WitnessProjection :=
  projectedRun canonicalCollectProjection24 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection32_run :
    projectedRun canonicalCollectProjection24 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection32 := rfl

theorem canonicalCollectProjection32_supported :
    witnessRunSupported canonicalCollectProjection24 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
