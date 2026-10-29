import JuliaLean.CRuntime.WorldStop.WitnessCollectChunk9

namespace JuliaLean.CRuntime.WorldStop

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def canonicalCollectProjection78 : WitnessProjection :=
  projectedRun canonicalCollectProjection72 (List.replicate 6 (.source 0 {}))

theorem canonicalCollectProjection78_run :
    projectedRun canonicalCollectProjection72 (List.replicate 6 (.source 0 {})) =
      canonicalCollectProjection78 := rfl

theorem canonicalCollectProjection78_supported :
    witnessRunSupported canonicalCollectProjection72 (List.replicate 6 (.source 0 {})) =
      true := by decide

theorem canonicalCollectProjection78_facts :
    canonicalCollectProjection78.criticalDuringGC = false ∧
    canonicalCollectProjection78.collectionActive = true ∧
    canonicalCollectProjection78.memory[0] = 1 ∧
    canonicalCollectProjection78.memory[20] = 3 ∧
    canonicalCollectProjection78.memory[21] = 1 ∧
    canonicalCollectProjection78.memory[4] = 1 ∧
    canonicalCollectProjection78.memory[5] = 2 ∧
    canonicalCollectProjection78.memory[6] = 2 ∧
    canonicalCollectProjection78.pageProtected[1] = true ∧
    canonicalCollectProjection78.pageProtected[2] = true ∧
    canonicalCollectProjection78.pageProtected[3] = true ∧
    (match canonicalCollectProjection78.threads[2].todo with
      | .call _ _ .resumeThread :: _ => true | _ => false) = true := by decide

theorem canonicalCollectProjection78_collectorTodo :
    canonicalCollectProjection78.threads[0].todo =
      .stmt "src/gc-stock.c" 3894 (.external "unlock finalizers_lock") ::
        (program .collect).drop 16 := by rfl

theorem canonicalCollectProjection78_events :
    canonicalCollectProjection78.candidate.events =
      canonicalCandidate.events.extract 0 70 := by decide

end JuliaLean.CRuntime.WorldStop
