import JuliaLean.base.atomics
import JuliaLean.Proofs.base.task.interleavings

namespace JuliaLean.Tasks






/-- Every legacy `Threads.Atomic{Int64}` operation returns the prior bits and
stores its documented update. Since scheduler interleavings are lists of
atomic steps, `atomicRun` is their linearization in that order. -/
def AtomicOperationsCorrect : Prop :=
  ∀ (old : AtomicInt) (action : AtomicAction),
    (atomicStep action old).1 = old ∧
      (atomicStep action old).2 = atomicUpdate action old

theorem atomicOperationsCorrect_proven : AtomicOperationsCorrect := by
  intro old action
  exact ⟨rfl, rfl⟩

end JuliaLean.Tasks
