import JuliaLean.Tasks.TaskModel

namespace JuliaLean.Tasks

/-- A queued `WaitEntry` as observed by `notify`, `base/condition.jl:417-433`.
Entries already claimed by cancellation remain physically linked but are
skipped and do not count as waiting tasks. -/
structure Waiter where
  id : Nat
  claimable : Bool
  deriving Repr, DecidableEq

structure NotifyResult where
  count : Nat
  woken : List Nat
  remaining : List Waiter
  deriving Repr, DecidableEq

/-- `notify(c, arg, all, error)`, `base/condition.jl:417-433`: pop from the
front, skip stale registrations, schedule each claimed task, and stop after
the first successful claim when `all == false`. -/
def notifyModel (all : Bool) : List Waiter → NotifyResult
  | [] => ⟨0, [], []⟩
  | waiter :: waiters =>
      if waiter.claimable then
        if all then
          let rest := notifyModel true waiters
          ⟨rest.count + 1, waiter.id :: rest.woken, rest.remaining⟩
        else
          ⟨1, [waiter.id], waiters⟩
      else
        notifyModel all waiters

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
