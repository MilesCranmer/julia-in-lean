import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk10

namespace JuliaLean.CRuntime.WorldStop

open Memory

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-- `gc-stock.c:3821-3888`; `safepoint.c:128-189`. -/
def canonicalCollectSchedule : List (Scheduled 3) :=
  List.replicate 8 (.source 0 {}) ++ List.replicate 8 (.source 0 {}) ++
  List.replicate 8 (.source 0 {}) ++ List.replicate 8 (.source 0 {}) ++
  List.replicate 8 (.source 0 {}) ++ List.replicate 8 (.source 0 {}) ++
  List.replicate 8 (.source 0 {}) ++ List.replicate 8 (.source 0 {}) ++
  List.replicate 8 (.source 0 {}) ++ List.replicate 6 (.source 0 {})

def canonicalStopped : Machine 3 := run canonicalSuspended canonicalCollectSchedule

theorem canonicalStopped_source :
    canonicalStopped = run canonicalSuspended canonicalCollectSchedule := rfl

def canonicalStoppedProjection : WitnessProjection := canonicalCollectProjection78

theorem canonicalStoppedProjection_run :
    projectedRun canonicalSuspendedProjection canonicalCollectSchedule =
      canonicalStoppedProjection := by
  unfold canonicalCollectSchedule
  simp only [projectedRun_append]
  rw [canonicalCollectProjection08_run, canonicalCollectProjection16_run,
    canonicalCollectProjection24_run, canonicalCollectProjection32_run,
    canonicalCollectProjection40_run, canonicalCollectProjection48_run,
    canonicalCollectProjection56_run, canonicalCollectProjection64_run,
    canonicalCollectProjection72_run, canonicalCollectProjection78_run]
  rfl

theorem canonicalStoppedProjection_supported :
    witnessRunSupported canonicalSuspendedProjection canonicalCollectSchedule = true := by
  unfold canonicalCollectSchedule
  simp only [List.append_assoc]
  apply witnessRunSupported_append
  · exact canonicalCollectProjection08_supported
  · rw [canonicalCollectProjection08_run]
    apply witnessRunSupported_append
    · exact canonicalCollectProjection16_supported
    · rw [canonicalCollectProjection16_run]
      apply witnessRunSupported_append
      · exact canonicalCollectProjection24_supported
      · rw [canonicalCollectProjection24_run]
        apply witnessRunSupported_append
        · exact canonicalCollectProjection32_supported
        · rw [canonicalCollectProjection32_run]
          apply witnessRunSupported_append
          · exact canonicalCollectProjection40_supported
          · rw [canonicalCollectProjection40_run]
            apply witnessRunSupported_append
            · exact canonicalCollectProjection48_supported
            · rw [canonicalCollectProjection48_run]
              apply witnessRunSupported_append
              · exact canonicalCollectProjection56_supported
              · rw [canonicalCollectProjection56_run]
                apply witnessRunSupported_append
                · exact canonicalCollectProjection64_supported
                · rw [canonicalCollectProjection64_run]
                  apply witnessRunSupported_append
                  · exact canonicalCollectProjection72_supported
                  · rw [canonicalCollectProjection72_run]
                    exact canonicalCollectProjection78_supported

theorem canonicalStopped_projection : project canonicalStopped = canonicalStoppedProjection :=
  project_stage canonicalSuspended _ _ _ canonicalSuspended_projection
    canonicalStoppedProjection_supported canonicalStoppedProjection_run

theorem canonicalStopped_facts :
    canonicalCollectSchedule.length = 78 ∧
    canonicalStopped.criticalDuringGC = false ∧
    canonicalStopped.collectionActive = true ∧
    canonicalStopped.memory .gcRunning = 1 ∧
    canonicalStopped.memory .gcNThreads = 3 ∧
    canonicalStopped.memory .gcAllTLS = 1 ∧
    canonicalStopped.memory (.gcState 1) = 1 ∧
    canonicalStopped.memory (.gcState 2) = 2 ∧
    canonicalStopped.memory (.gcState 3) = 2 ∧
    canonicalStopped.pageProtected 1 = true ∧
    canonicalStopped.pageProtected 2 = true ∧
    canonicalStopped.pageProtected 3 = true ∧
    controllerAtResumeCall canonicalStopped = true := by
  rcases canonicalCollectProjection78_facts with
    ⟨fCritical, fActive, f0, f20, f21, f4, f5, f6, fPage1, fPage2, fPage3, fResume⟩
  have critical := congrArg WitnessProjection.criticalDuringGC canonicalStopped_projection
  have critical' : canonicalStopped.criticalDuringGC =
      canonicalStoppedProjection.criticalDuringGC := by
    simpa only [project] using critical
  have active := congrArg WitnessProjection.collectionActive canonicalStopped_projection
  have active' : canonicalStopped.collectionActive =
      canonicalStoppedProjection.collectionActive := by
    simpa only [project] using active
  have memory0 := congrArg (fun p : WitnessProjection => p.memory[0])
    canonicalStopped_projection
  rw [project_memory] at memory0
  have memory20 := congrArg (fun p : WitnessProjection => p.memory[20])
    canonicalStopped_projection
  rw [project_memory] at memory20
  have memory21 := congrArg (fun p : WitnessProjection => p.memory[21])
    canonicalStopped_projection
  rw [project_memory] at memory21
  have memory4 := congrArg (fun p : WitnessProjection => p.memory[4])
    canonicalStopped_projection
  rw [project_memory] at memory4
  have memory5 := congrArg (fun p : WitnessProjection => p.memory[5])
    canonicalStopped_projection
  rw [project_memory] at memory5
  have memory6 := congrArg (fun p : WitnessProjection => p.memory[6])
    canonicalStopped_projection
  rw [project_memory] at memory6
  have page1 := congrArg (fun p : WitnessProjection => p.pageProtected[1])
    canonicalStopped_projection
  rw [project_page] at page1
  have page2 := congrArg (fun p : WitnessProjection => p.pageProtected[2])
    canonicalStopped_projection
  rw [project_page] at page2
  have page3 := congrArg (fun p : WitnessProjection => p.pageProtected[3])
    canonicalStopped_projection
  rw [project_page] at page3
  have resumeCall : controllerAtResumeCall canonicalStopped = true := by
    unfold controllerAtResumeCall
    rw [canonicalStopped_projection]
    exact fResume
  have loc0 : witnessLocations[0] = .gcRunning := rfl
  have loc20 : witnessLocations[20] = .gcNThreads := rfl
  have loc21 : witnessLocations[21] = .gcAllTLS := rfl
  have loc4 : witnessLocations[4] = .gcState 1 := rfl
  have loc5 : witnessLocations[5] = .gcState 2 := rfl
  have loc6 : witnessLocations[6] = .gcState 3 := rfl
  rw [loc0] at memory0
  rw [loc20] at memory20
  rw [loc21] at memory21
  rw [loc4] at memory4
  rw [loc5] at memory5
  rw [loc6] at memory6
  have m0 := memory0.trans f0
  have m20 := memory20.trans f20
  have m21 := memory21.trans f21
  have m4 := memory4.trans f4
  have m5 := memory5.trans f5
  have m6 := memory6.trans f6
  exact ⟨by decide, critical'.trans fCritical, active'.trans fActive,
    m0, m20, m21, m4, m5, m6,
    page1.trans fPage1, page2.trans fPage2, page3.trans fPage3, resumeCall⟩

theorem canonicalStopped_collectorPC :
    (project canonicalStopped).threads[0].todo =
      .stmt "src/gc-stock.c" 3894 (.external "unlock finalizers_lock") ::
        (program .collect).drop 16 := by
  rw [canonicalStopped_projection]
  exact canonicalCollectProjection78_collectorTodo

theorem canonicalStopped_events :
    canonicalStopped.candidate.events = canonicalCandidate.events.extract 0 70 := by
  have equal := congrArg (fun p : WitnessProjection => p.candidate.events)
    canonicalStopped_projection
  have equal' : canonicalStopped.candidate.events =
      canonicalStoppedProjection.candidate.events := by
    simpa only [project] using equal
  exact equal'.trans canonicalCollectProjection78_events

end JuliaLean.CRuntime.WorldStop
