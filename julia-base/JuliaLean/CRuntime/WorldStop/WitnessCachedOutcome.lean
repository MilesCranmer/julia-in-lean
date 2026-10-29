import JuliaLean.CRuntime.WorldStop.WitnessCachedResume

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalOutcomeProjection : WitnessProjection :=
  projectedRun canonicalResumedProjection (List.replicate 6 (.source 1 {}))

theorem canonicalOutcomeProjection_run :
    projectedRun canonicalResumedProjection (List.replicate 6 (.source 1 {})) =
      canonicalOutcomeProjection := rfl

theorem canonicalOutcomeProjection_supported :
    witnessRunSupported canonicalResumedProjection (List.replicate 6 (.source 1 {})) =
      true := by decide

theorem canonicalOutcomeProjection_events :
    canonicalOutcomeProjection.candidate.events = canonicalCandidate.events := by decide

theorem canonicalCandidate_eventCount : canonicalCandidate.events.size = 88 := by decide

theorem canonicalOutcomeProjection_violationFacts :
    canonicalOutcomeProjection.criticalDuringGC = true ∧
    canonicalOutcomeProjection.collectionActive = true ∧
    canonicalOutcomeProjection.memory[5] = 0 ∧
    canonicalOutcomeProjection.memory[7] = 2 ∧
    canonicalOutcomeProjection.pageProtected[2] = true ∧
    canonicalOutcomeProjection.pageProtected[3] = false := by decide

theorem canonicalOutcomeProjection_protectionsSucceed :
    canonicalOutcomeProjection.os.all (fun event => match event with
      | .protection _ _ _ ok => ok | _ => true) = true := by decide

theorem canonicalOutcomeProjection_noDelivery :
    canonicalOutcomeProjection.os.all (fun event => match event with
      | .delivery _ _ => false | _ => true) = true := by decide

end JuliaLean.CRuntime.WorldStop
