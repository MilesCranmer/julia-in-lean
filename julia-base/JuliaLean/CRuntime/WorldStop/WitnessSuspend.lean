import JuliaLean.CRuntime.WorldStop.WitnessSuspendChunk6

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- `safepoint.c:398-439`; `julia_threads.h:638-665,679`. -/
def canonicalSuspendSchedule : List (Scheduled 3) :=
  List.replicate 8 (.source 2 {}) ++ List.replicate 8 (.source 2 {}) ++
  List.replicate 8 (.source 2 {}) ++ List.replicate 8 (.source 2 {}) ++
  List.replicate 8 (.source 2 {}) ++ List.replicate 8 (.source 2 {})

def canonicalSuspended : Machine 3 := run canonicalInitial canonicalSuspendSchedule

theorem canonicalSuspended_source :
    canonicalSuspended = run canonicalInitial canonicalSuspendSchedule := rfl

def canonicalSuspendedProjection : WitnessProjection := canonicalSuspendProjection48

theorem canonicalSuspendedProjection_run :
    projectedRun canonicalInitialProjection canonicalSuspendSchedule =
      canonicalSuspendedProjection := by
  simp only [canonicalSuspendSchedule, projectedRun_append]
  rw [canonicalSuspendProjection08_run, canonicalSuspendProjection16_run,
    canonicalSuspendProjection24_run, canonicalSuspendProjection32_run,
    canonicalSuspendProjection40_run, canonicalSuspendProjection48_run]
  rfl

theorem canonicalSuspendedProjection_supported :
    witnessRunSupported canonicalInitialProjection canonicalSuspendSchedule = true := by decide

theorem canonicalSuspended_projection : project canonicalSuspended = canonicalSuspendedProjection :=
  project_stage canonicalInitial _ _ _ canonicalInitial_projection
    canonicalSuspendedProjection_supported canonicalSuspendedProjection_run

theorem canonicalSuspended_facts :
    canonicalSuspendSchedule.length = 48 ∧
    controllerAtResumeCall canonicalSuspended = true ∧
    canonicalSuspended.memory (.suspendCount 2) = 1 ∧
    canonicalSuspended.memory (.safepoint 2) = 3 ∧
    canonicalSuspended.memory (.gcState 3) = 2 ∧
    canonicalSuspended.pageProtected 3 = true ∧
    canonicalSuspended.collectionActive = false := by
  have facts :
      (match canonicalSuspendedProjection.threads[2].todo with
        | .call _ _ .resumeThread :: _ => true | _ => false) = true ∧
      canonicalSuspendedProjection.memory[10] = 1 ∧
      canonicalSuspendedProjection.memory[7] = 3 ∧
      canonicalSuspendedProjection.memory[6] = 2 ∧
      canonicalSuspendedProjection.pageProtected[3] = true ∧
      canonicalSuspendedProjection.collectionActive = false := by decide
  have resumeCall : controllerAtResumeCall canonicalSuspended = true := by
    unfold controllerAtResumeCall
    rw [canonicalSuspended_projection]
    exact facts.1
  have memory10 := congrArg (fun p : WitnessProjection => p.memory[10])
    canonicalSuspended_projection
  rw [project_memory] at memory10
  change canonicalSuspended.memory (.suspendCount 2) =
    canonicalSuspendedProjection.memory[10] at memory10
  have memory7 := congrArg (fun p : WitnessProjection => p.memory[7])
    canonicalSuspended_projection
  rw [project_memory] at memory7
  change canonicalSuspended.memory (.safepoint 2) =
    canonicalSuspendedProjection.memory[7] at memory7
  have memory6 := congrArg (fun p : WitnessProjection => p.memory[6])
    canonicalSuspended_projection
  rw [project_memory] at memory6
  change canonicalSuspended.memory (.gcState 3) =
    canonicalSuspendedProjection.memory[6] at memory6
  have page3 := congrArg (fun p : WitnessProjection => p.pageProtected[3])
    canonicalSuspended_projection
  rw [project_page] at page3
  change canonicalSuspended.pageProtected 3 =
    canonicalSuspendedProjection.pageProtected[3] at page3
  have active := congrArg WitnessProjection.collectionActive canonicalSuspended_projection
  have active' : canonicalSuspended.collectionActive =
      canonicalSuspendedProjection.collectionActive := by
    simpa only [project] using active
  exact ⟨by decide, resumeCall, memory10.trans facts.2.1,
    memory7.trans facts.2.2.1, memory6.trans facts.2.2.2.1,
    page3.trans facts.2.2.2.2.1, active'.trans facts.2.2.2.2.2⟩

theorem canonicalSuspended_targetPC :
    (canonicalSuspended.threads 1).todo = entryCommands .safeTarget := by
  have equal := congrArg (fun p : WitnessProjection => p.threads[1].todo)
    canonicalSuspended_projection
  rw [project_todo] at equal
  exact equal.trans (by rfl)

theorem canonicalSuspended_events :
    canonicalSuspended.candidate.events = canonicalCandidate.events.extract 0 42 := by
  have equal := congrArg (fun p : WitnessProjection => p.candidate.events)
    canonicalSuspended_projection
  exact equal.trans (by decide)

end JuliaLean.CRuntime.WorldStop
