import JuliaLean.CRuntime.WorldStop.WitnessEvents

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

theorem canonicalOutcome_stepCount :
    canonicalFullSchedule.length = 167 ∧ canonicalOutcome.candidate.events.size = 88 := by
  have count := congrArg Array.size canonicalOutcome_events
  exact ⟨by decide, count.trans canonicalCandidate_eventCount⟩

theorem canonicalOutcome_violation :
    canonicalOutcome.criticalDuringGC = true ∧ canonicalOutcome.collectionActive = true ∧
    canonicalOutcome.memory (.gcState 2) = 0 ∧
    canonicalOutcome.memory (.safepoint 2) = 2 ∧
    canonicalOutcome.pageProtected 2 = true ∧ canonicalOutcome.pageProtected 3 = false := by
  rcases canonicalOutcomeProjection_violationFacts with
    ⟨fCritical, fActive, f5, f7, fPage2, fPage3⟩
  have critical := congrArg WitnessProjection.criticalDuringGC canonicalOutcome_projection
  have critical' : canonicalOutcome.criticalDuringGC =
      canonicalOutcomeProjection.criticalDuringGC := by
    simpa only [project] using critical
  have active := congrArg WitnessProjection.collectionActive canonicalOutcome_projection
  have active' : canonicalOutcome.collectionActive =
      canonicalOutcomeProjection.collectionActive := by
    simpa only [project] using active
  have memory5 := congrArg (fun p : WitnessProjection => p.memory[5])
    canonicalOutcome_projection
  rw [project_memory] at memory5
  have memory7 := congrArg (fun p : WitnessProjection => p.memory[7])
    canonicalOutcome_projection
  rw [project_memory] at memory7
  have page2 := congrArg (fun p : WitnessProjection => p.pageProtected[2])
    canonicalOutcome_projection
  rw [project_page] at page2
  have page3 := congrArg (fun p : WitnessProjection => p.pageProtected[3])
    canonicalOutcome_projection
  rw [project_page] at page3
  have loc5 : witnessLocations[5] = .gcState 2 := rfl
  have loc7 : witnessLocations[7] = .safepoint 2 := rfl
  rw [loc5] at memory5
  rw [loc7] at memory7
  exact ⟨critical'.trans fCritical, active'.trans fActive,
    memory5.trans f5, memory7.trans f7, page2.trans fPage2, page3.trans fPage3⟩

theorem canonicalOutcome_platform : PlatformTraceContract canonicalOutcome := by
  have equal := congrArg WitnessProjection.os canonicalOutcome_projection
  have equal' : canonicalOutcome.os = canonicalOutcomeProjection.os := by
    simpa only [project] using equal
  refine ⟨?_, ?_⟩
  · intro actor page enabled ok member
    rw [equal'] at member
    exact (List.all_eq_true.mp canonicalOutcomeProjection_protectionsSucceed) _ member
  · intro actor page member
    rw [equal'] at member
    have impossible := (List.all_eq_true.mp canonicalOutcomeProjection_noDelivery) _ member
    cases impossible

end JuliaLean.CRuntime.WorldStop
