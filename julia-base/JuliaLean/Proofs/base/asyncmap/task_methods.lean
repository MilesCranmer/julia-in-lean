import JuliaLean.base.asyncmap
import JuliaLean.Proofs.base.asyncmap.task_properties
import JuliaLean.Proofs.base.linked_list.wellformed
import JuliaLean.Proofs.base.scopedvalues.task_properties
import JuliaLean.Proofs.base.atomics.task_properties

namespace JuliaLean.Tasks



def AsyncMapPublicBodies : Prop := ∀ (_shape : AsyncShape) (values : List Nat)
    (length : Option Nat) (count : Int),
  (asyncResultShape .tuple values).2 = values ∧
  verifyBatchSizeBody none = .ok none ∧
  (count < 0 → verifyNTasksBody length (.constant count) = .error ()) ∧
  verifyNTasksBody length (.dynamic 0) = .ok 1 ∧
  asyncStringResult values = values

theorem asyncMapPublicBodies_proven : AsyncMapPublicBodies := by
  unfold AsyncMapPublicBodies
  intro shape values length count
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  · intro negative; simp [verifyNTasksBody, negative]

def AsyncCollectorBodies : Prop := ∀ (f : Nat → Nat) (state : CollectorState)
    (index value requested : Nat),
  (collectorComplete f state index value).results index = some (f value) ∧
  (collectorGrow state requested).workers =
    (if state.workers < requested then state.workers + 1 else state.workers)

theorem asyncCollectorBodies_proven : AsyncCollectorBodies := by
  intro f state index value requested
  constructor
  · simp [collectorComplete]
  · simp [collectorGrow]
    split <;> rfl

def AsyncGeneratorBodies : Prop := ∀ (state : GeneratorState) (result : List Nat),
  asyncmapBangBody result = result ∧
  (state.done = true → state.results state.nextIndex = none →
    (generatorStep state).1 = .finished)

theorem asyncGeneratorBodies_proven : AsyncGeneratorBodies := by
  intro state result
  constructor
  · rfl
  · intro done missing
    simp [generatorStep, done, missing]

end JuliaLean.Tasks
