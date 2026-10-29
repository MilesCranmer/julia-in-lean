import JuliaLean.CRuntime.WorldStop.WitnessResumeChunk1

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalResumeEntryProjection11 : WitnessProjection :=
  projectedRun canonicalResumeEntryProjection08 (List.replicate 3 (.source 2 {}))

theorem canonicalResumeEntryProjection11_run :
    projectedRun canonicalResumeEntryProjection08 (List.replicate 3 (.source 2 {})) =
      canonicalResumeEntryProjection11 := rfl

theorem canonicalResumeEntryProjection11_supported :
    witnessRunSupported canonicalResumeEntryProjection08 (List.replicate 3 (.source 2 {})) =
      true := by decide

theorem canonicalResumeEntryProjection11_facts :
    canonicalResumeEntryProjection11.criticalDuringGC = false ∧
    canonicalResumeEntryProjection11.collectionActive = true ∧
    canonicalResumeEntryProjection11.memory[0] = 1 ∧
    canonicalResumeEntryProjection11.memory[20] = 3 ∧
    canonicalResumeEntryProjection11.memory[21] = 1 ∧
    canonicalResumeEntryProjection11.memory[5] = 2 ∧
    canonicalResumeEntryProjection11.memory[6] = 2 ∧
    canonicalResumeEntryProjection11.pageProtected[2] = true ∧
    canonicalResumeEntryProjection11.pageProtected[3] = true ∧
    (match canonicalResumeEntryProjection11.threads[2].todo with
      | .branch file line _ _ _ :: _ => file == "src/safepoint.c" && line == 456
      | _ => false) = true ∧
    canonicalResumeEntryProjection11.threads[2].regs[witnessRegIndex .target] = 2 ∧
    canonicalResumeEntryProjection11.threads[2].regs[witnessRegIndex .resumeCount] = 1 ∧
    canonicalResumeEntryProjection11.locks[0] = some 2 ∧
    canonicalResumeEntryProjection11.locks[6] = some 2 := by decide

theorem canonicalResumeEntryProjection11_targetTodo :
    canonicalResumeEntryProjection11.threads[1].todo = entryCommands .safeTarget := by rfl

theorem canonicalResumeEntryProjection11_events :
    canonicalResumeEntryProjection11.candidate.events =
      canonicalCandidate.events.extract 0 77 := by decide

end JuliaLean.CRuntime.WorldStop
