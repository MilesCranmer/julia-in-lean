import JuliaLean.CRuntime.WorldStop.WitnessCachedOutcome

namespace JuliaLean.CRuntime.WorldStop

open Memory

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- `julia_threads.h:638-665`; `safepoint.c:456-472`. -/
def cachedPointerSchedule : List (Scheduled 3) :=
  List.replicate 8 (.source 1 {}) ++
  List.replicate 8 (.source 2 {}) ++
  List.replicate 8 (.source 2 {}) ++
  List.replicate 6 (.source 1 {})

def canonicalFullSchedule : List (Scheduled 3) := canonicalPrefix ++ cachedPointerSchedule

def canonicalOutcome : Machine 3 := run canonicalCheckpoint cachedPointerSchedule

theorem canonicalOutcome_source :
    canonicalOutcome = run canonicalCheckpoint cachedPointerSchedule := rfl

theorem canonicalOutcome_fullSource :
    canonicalOutcome = run canonicalInitial canonicalFullSchedule := by
  rw [canonicalOutcome_source, canonicalCheckpoint_reachable]
  exact (run_append canonicalInitial canonicalPrefix cachedPointerSchedule).symm

private theorem cachedPointer_supported :
    witnessRunSupported canonicalCheckpointProjection cachedPointerSchedule = true := by
  unfold cachedPointerSchedule
  simp only [List.append_assoc]
  apply witnessRunSupported_append
  · exact canonicalTargetCachedProjection_supported
  · rw [canonicalTargetCachedProjection_run]
    apply witnessRunSupported_append
    · exact canonicalCachedResumeProjection08_supported
    · rw [canonicalCachedResumeProjection08_run]
      apply witnessRunSupported_append
      · exact canonicalCachedResumeProjection16_supported
      · rw [canonicalCachedResumeProjection16_run]
        exact canonicalOutcomeProjection_supported

private theorem cachedPointer_projectedRun :
    projectedRun canonicalCheckpointProjection cachedPointerSchedule = canonicalOutcomeProjection := by
  simp only [cachedPointerSchedule, projectedRun_append]
  rw [canonicalTargetCachedProjection_run, canonicalCachedResumeProjection08_run,
    canonicalCachedResumeProjection16_run]
  exact canonicalOutcomeProjection_run

theorem canonicalOutcome_projection : project canonicalOutcome = canonicalOutcomeProjection :=
  project_stage canonicalCheckpoint _ _ _ canonicalCheckpoint_projection
    cachedPointer_supported cachedPointer_projectedRun

theorem canonicalFullSchedule_supported :
    witnessRunSupported canonicalInitialProjection canonicalFullSchedule = true := by
  simp only [canonicalFullSchedule, canonicalPrefix, List.append_assoc]
  apply witnessRunSupported_append
  · exact canonicalSuspendedProjection_supported
  · rw [canonicalSuspendedProjection_run]
    apply witnessRunSupported_append
    · exact canonicalStoppedProjection_supported
    · rw [canonicalStoppedProjection_run]
      apply witnessRunSupported_append
      · exact canonicalCheckpointProjection_supported
      · rw [canonicalCheckpointProjection_run]
        exact cachedPointer_supported

theorem canonicalOutcome_fullProjection :
    project (run canonicalInitial canonicalFullSchedule) = canonicalOutcomeProjection := by
  rw [project_run canonicalInitial canonicalFullSchedule
    (by rw [canonicalInitial_projection]; exact canonicalFullSchedule_supported)]
  rw [canonicalInitial_projection]
  simp only [canonicalFullSchedule, canonicalPrefix, projectedRun_append]
  rw [canonicalSuspendedProjection_run, canonicalStoppedProjection_run,
    canonicalCheckpointProjection_run, cachedPointer_projectedRun]

theorem canonicalOutcome_events :
    canonicalOutcome.candidate.events = canonicalCandidate.events := by
  have equal := congrArg (fun p : WitnessProjection => p.candidate.events)
    canonicalOutcome_projection
  have equal' : canonicalOutcome.candidate.events =
      canonicalOutcomeProjection.candidate.events := by
    simpa only [project] using equal
  exact equal'.trans canonicalOutcomeProjection_events

/-- Equality of the complete source execution and its global C11 candidate. -/
theorem canonicalCandidate_matchesSource : canonicalOutcome.candidate = canonicalCandidate := by
  cases left : canonicalOutcome.candidate with
  | mk leftEvents =>
      cases right : canonicalCandidate with
      | mk rightEvents =>
          have events : leftEvents = rightEvents := by
            simpa only [left, right] using canonicalOutcome_events
          cases events
          rfl

end JuliaLean.CRuntime.WorldStop
