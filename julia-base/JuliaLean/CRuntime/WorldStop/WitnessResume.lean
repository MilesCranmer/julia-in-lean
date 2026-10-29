import JuliaLean.CRuntime.WorldStop.WitnessResumeChunk2

namespace JuliaLean.CRuntime.WorldStop

open Memory

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- `safepoint.c:443-455`. -/
def canonicalResumeEntrySchedule : List (Scheduled 3) :=
  List.replicate 8 (.source 2 {}) ++ List.replicate 3 (.source 2 {})

def canonicalPrefix : List (Scheduled 3) :=
  canonicalSuspendSchedule ++ canonicalCollectSchedule ++ canonicalResumeEntrySchedule

def canonicalCheckpoint : Machine 3 := run canonicalStopped canonicalResumeEntrySchedule

theorem canonicalCheckpoint_source :
    canonicalCheckpoint = run canonicalStopped canonicalResumeEntrySchedule := rfl

theorem canonicalCheckpoint_reachable :
    canonicalCheckpoint = run canonicalInitial canonicalPrefix := by
  rw [canonicalCheckpoint_source, canonicalStopped_source, canonicalSuspended_source]
  simp only [canonicalPrefix, run_append]

theorem canonicalCheckpoint_sourceReachable : SourceReachableCheckpoint canonicalCheckpoint :=
  ⟨canonicalInitial, canonicalRoles, canonicalPrefix, canonicalInitial_publicEntry,
    canonicalCheckpoint_reachable⟩

def canonicalCheckpointProjection : WitnessProjection := canonicalResumeEntryProjection11

theorem canonicalCheckpointProjection_run :
    projectedRun canonicalStoppedProjection canonicalResumeEntrySchedule =
      canonicalCheckpointProjection := by
  simp only [canonicalResumeEntrySchedule, projectedRun_append]
  rw [canonicalResumeEntryProjection08_run, canonicalResumeEntryProjection11_run]
  rfl

theorem canonicalCheckpointProjection_supported :
    witnessRunSupported canonicalStoppedProjection canonicalResumeEntrySchedule = true := by
  unfold canonicalResumeEntrySchedule
  apply witnessRunSupported_append
  · exact canonicalResumeEntryProjection08_supported
  · rw [canonicalResumeEntryProjection08_run]
    exact canonicalResumeEntryProjection11_supported

theorem canonicalCheckpoint_projection : project canonicalCheckpoint = canonicalCheckpointProjection :=
  project_stage canonicalStopped _ _ _ canonicalStopped_projection
    canonicalCheckpointProjection_supported canonicalCheckpointProjection_run

theorem canonicalCheckpoint_facts :
    canonicalPrefix.length = 137 ∧
    canonicalCheckpoint.criticalDuringGC = false ∧
    canonicalCheckpoint.collectionActive = true ∧
    canonicalCheckpoint.memory .gcRunning = 1 ∧
    canonicalCheckpoint.memory .gcNThreads = 3 ∧
    canonicalCheckpoint.memory .gcAllTLS = 1 ∧
    canonicalCheckpoint.memory (.gcState 2) = 2 ∧
    canonicalCheckpoint.memory (.gcState 3) = 2 ∧
    canonicalCheckpoint.pageProtected 2 = true ∧
    canonicalCheckpoint.pageProtected 3 = true ∧
    controllerAtResumeBranch canonicalCheckpoint = true ∧
    (project canonicalCheckpoint).threads[2].regs[witnessRegIndex .target] = 2 ∧
    (project canonicalCheckpoint).threads[2].regs[witnessRegIndex .resumeCount] = 1 ∧
    canonicalCheckpoint.locks 0 = some 2 ∧ canonicalCheckpoint.locks 6 = some 2 := by
  rcases canonicalResumeEntryProjection11_facts with
    ⟨fCritical, fActive, f0, f20, f21, f5, f6, fPage2, fPage3, fResume,
      fTarget, fResumeCount, fLock0, fLock6⟩
  have critical := congrArg WitnessProjection.criticalDuringGC canonicalCheckpoint_projection
  have critical' : canonicalCheckpoint.criticalDuringGC =
      canonicalCheckpointProjection.criticalDuringGC := by
    simpa only [project] using critical
  have active := congrArg WitnessProjection.collectionActive canonicalCheckpoint_projection
  have active' : canonicalCheckpoint.collectionActive =
      canonicalCheckpointProjection.collectionActive := by
    simpa only [project] using active
  have memory0 := congrArg (fun p : WitnessProjection => p.memory[0])
    canonicalCheckpoint_projection
  rw [project_memory] at memory0
  have memory20 := congrArg (fun p : WitnessProjection => p.memory[20])
    canonicalCheckpoint_projection
  rw [project_memory] at memory20
  have memory21 := congrArg (fun p : WitnessProjection => p.memory[21])
    canonicalCheckpoint_projection
  rw [project_memory] at memory21
  have memory5 := congrArg (fun p : WitnessProjection => p.memory[5])
    canonicalCheckpoint_projection
  rw [project_memory] at memory5
  have memory6 := congrArg (fun p : WitnessProjection => p.memory[6])
    canonicalCheckpoint_projection
  rw [project_memory] at memory6
  have page2 := congrArg (fun p : WitnessProjection => p.pageProtected[2])
    canonicalCheckpoint_projection
  rw [project_page] at page2
  have page3 := congrArg (fun p : WitnessProjection => p.pageProtected[3])
    canonicalCheckpoint_projection
  rw [project_page] at page3
  have lock0 := congrArg (fun p : WitnessProjection => p.locks[0])
    canonicalCheckpoint_projection
  rw [project_lock] at lock0
  have lock6 := congrArg (fun p : WitnessProjection => p.locks[6])
    canonicalCheckpoint_projection
  rw [project_lock] at lock6
  have resumeBranch : controllerAtResumeBranch canonicalCheckpoint = true := by
    unfold controllerAtResumeBranch
    rw [canonicalCheckpoint_projection]
    exact fResume
  have target : (project canonicalCheckpoint).threads[2].regs[witnessRegIndex .target] = 2 := by
    rw [canonicalCheckpoint_projection]
    exact fTarget
  have resumeCount :
      (project canonicalCheckpoint).threads[2].regs[witnessRegIndex .resumeCount] = 1 := by
    rw [canonicalCheckpoint_projection]
    exact fResumeCount
  have loc0 : witnessLocations[0] = .gcRunning := rfl
  have loc20 : witnessLocations[20] = .gcNThreads := rfl
  have loc21 : witnessLocations[21] = .gcAllTLS := rfl
  have loc5 : witnessLocations[5] = .gcState 2 := rfl
  have loc6 : witnessLocations[6] = .gcState 3 := rfl
  rw [loc0] at memory0
  rw [loc20] at memory20
  rw [loc21] at memory21
  rw [loc5] at memory5
  rw [loc6] at memory6
  exact ⟨by decide, critical'.trans fCritical, active'.trans fActive,
    memory0.trans f0, memory20.trans f20, memory21.trans f21,
    memory5.trans f5, memory6.trans f6, page2.trans fPage2, page3.trans fPage3,
    resumeBranch, target, resumeCount, lock0.trans fLock0, lock6.trans fLock6⟩

theorem canonicalCheckpoint_targetPC :
    (project canonicalCheckpoint).threads[1].todo = entryCommands .safeTarget := by
  rw [canonicalCheckpoint_projection]
  exact canonicalResumeEntryProjection11_targetTodo

theorem canonicalCheckpoint_events :
    canonicalCheckpoint.candidate.events = canonicalCandidate.events.extract 0 77 := by
  have equal := congrArg (fun p : WitnessProjection => p.candidate.events)
    canonicalCheckpoint_projection
  have equal' : canonicalCheckpoint.candidate.events =
      canonicalCheckpointProjection.candidate.events := by
    simpa only [project] using equal
  exact equal'.trans canonicalResumeEntryProjection11_events

end JuliaLean.CRuntime.WorldStop
