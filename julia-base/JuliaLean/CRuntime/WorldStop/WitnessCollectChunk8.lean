import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk7

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000

def canonicalCollectProjection64 : WitnessProjection :=
  projectedRun canonicalCollectProjection56 (List.replicate 8 (.source 0 {}))

theorem canonicalCollectProjection64_run :
    projectedRun canonicalCollectProjection56 (List.replicate 8 (.source 0 {})) =
      canonicalCollectProjection64 := rfl

theorem canonicalCollectProjection64_supported :
    witnessRunSupported canonicalCollectProjection56 (List.replicate 8 (.source 0 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
