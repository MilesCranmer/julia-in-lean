import JuliaLean.base.threads_overloads
import JuliaLean.Proofs.base.locks_mt.common

/-! Source-body models and properties for `base/threads_overloads.jl`. -/

namespace JuliaLean.ConcurrencyCov.ThreadsOverloads

open JuliaLean.ConcurrencyCov





/-- `Threads.foreach` applies `f` once to every item taken by each worker and
waits for all workers; the two schedule traits select direct versus spawn/wait
application (`base/threads_overloads.jl:41-66`). -/
def ThreadsForeachSpec : Prop :=
  applyForSchedule .static = .direct ∧
  applyForSchedule .fair = .spawnedAndWaited ∧
  (∀ (α : Type) schedule ntasks (assignments : List (List α)) f,
    assignments.length = ntasks →
    threadedForeach schedule ntasks assignments f =
      .ok (assignments.flatMap (List.map f)))

theorem threadsForeachSpec_proven : ThreadsForeachSpec := by
  refine ⟨rfl, rfl, ?_⟩
  intro α schedule ntasks assignments f h
  simp [threadedForeach, h]

end JuliaLean.ConcurrencyCov.ThreadsOverloads
