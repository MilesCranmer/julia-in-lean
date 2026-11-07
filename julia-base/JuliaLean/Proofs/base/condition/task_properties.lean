import JuliaLean.base.condition
import JuliaLean.Proofs.base.task.interleavings

namespace JuliaLean.Tasks




/-- `notify(c; all=false)` wakes exactly one live waiter when one exists, and
returns zero only when every physical queue entry is stale. -/
def ConditionNotifyOne : Prop :=
  ∀ (waiters : List Waiter),
    let expected := if waiters.any (·.claimable) then 1 else 0
    (notifyModel false waiters).count = expected ∧
      (notifyModel false waiters).woken.length = expected

theorem conditionNotifyOne_proven : ConditionNotifyOne := by
  intro waiters
  induction waiters with
  | nil => simp [notifyModel]
  | cons waiter waiters ih =>
      cases h : waiter.claimable <;> simp_all [notifyModel]

end JuliaLean.Tasks
