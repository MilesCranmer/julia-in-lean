import JuliaLean.base.condition
import JuliaLean.Proofs.base.task.interleavings
import JuliaLean.Proofs.base.cancellation.task_properties
import JuliaLean.Proofs.base.condition.task_properties

namespace JuliaLean.Tasks



def ConditionLockBodies : Prop := ∀ (locked : Bool) (owner current identity : Nat),
  hasLock locked owner current = (locked && owner == current) ∧
  alwaysLockedTry owner current = (owner == current) ∧
  conditionWaitQueue identity = identity

theorem conditionLockBodies_proven : ConditionLockBodies := by
  unfold ConditionLockBodies
  intros
  exact ⟨rfl, rfl, rfl⟩

def ConditionRegistrationBodies : Prop := ∀ (queue : List Nat) (waiter : Nat)
    (first cancelled started queued armed : Bool),
  conditionDequeue (conditionEnqueue queue waiter first) waiter =
    (conditionEnqueue queue waiter first).erase waiter ∧
  freshWaiter started queued armed = (!started && !queued && !armed) ∧
  (subscribeBody queue waiter first cancelled).2 = !cancelled

theorem conditionRegistrationBodies_proven : ConditionRegistrationBodies := by
  unfold ConditionRegistrationBodies
  intro queue waiter first cancelled started queued armed
  constructor
  · rfl
  constructor
  · rfl
  · cases cancelled <;> rfl

def ConditionWaitBodies : Prop := ∀ (cancelled cancelAsValue notified : Bool)
    (payload severity : Nat),
  conditionWaitBody cancelled cancelAsValue notified payload severity =
    (if cancelled then
      if cancelAsValue then .value severity else .cancelled severity
     else if notified then .value payload else .blocked)

theorem conditionWaitBodies_proven : ConditionWaitBodies := by
  unfold ConditionWaitBodies
  intros
  rfl

def ConditionNotifyBodies : Prop := ∀ (waiters : List Waiter) (all threadSafe : Bool),
  (notifyModel all waiters).count ≤ waiters.length ∧
  conditionShow threadSafe = (if threadSafe then "GenericCondition(lock)" else "Condition()")

theorem conditionNotifyBodies_proven : ConditionNotifyBodies := by
  intro waiters all threadSafe
  constructor
  · induction waiters with
    | nil => simp [notifyModel]
    | cons waiter waiters ih =>
        cases h : waiter.claimable <;> cases all <;> simp_all [notifyModel] <;> omega
  · rfl

end JuliaLean.Tasks
