import JuliaLean.CRuntime.WorldStop.WitnessCollect

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalResumeEntryProjection08 : WitnessProjection :=
  projectedRun canonicalStoppedProjection (List.replicate 8 (.source 2 {}))

theorem canonicalResumeEntryProjection08_run :
    projectedRun canonicalStoppedProjection (List.replicate 8 (.source 2 {})) =
      canonicalResumeEntryProjection08 := rfl

theorem canonicalResumeEntryProjection08_supported :
    witnessRunSupported canonicalStoppedProjection (List.replicate 8 (.source 2 {})) =
      true := by decide

end JuliaLean.CRuntime.WorldStop
