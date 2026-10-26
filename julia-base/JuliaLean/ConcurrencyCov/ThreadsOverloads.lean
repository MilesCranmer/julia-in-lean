import JuliaLean.ConcurrencyCov.Common

/-! Source-body models and properties for `base/threads_overloads.jl`. -/

namespace JuliaLean.ConcurrencyCov.ThreadsOverloads

open JuliaLean.ConcurrencyCov

inductive Schedule where | static | fair
  deriving DecidableEq, Repr

inductive ApplyMode where | direct | spawnedAndWaited
  deriving DecidableEq, Repr

def applyForSchedule : Schedule → ApplyMode
  | .static => .direct
  | .fair => .spawnedAndWaited

/-- One complete execution in which all `ntasks` workers finish normally. Tasks
share the channel, so the scheduler supplies a partition of its items. -/
def threadedForeach {α : Type} (schedule : Schedule) (ntasks : Nat)
    (assignments : List (List α)) (f : α → Nat) : R (List Nat) :=
  if assignments.length != ntasks then .error (.assertionError "worker count")
  else
    let _apply := applyForSchedule schedule
    .ok (assignments.flatMap (List.map f))

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
