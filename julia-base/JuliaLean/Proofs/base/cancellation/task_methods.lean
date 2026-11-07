import JuliaLean.base.cancellation
import JuliaLean.Proofs.base.task.interleavings
import JuliaLean.Proofs.base.cancellation.task_properties
import JuliaLean.Proofs.base.condition.task_properties

namespace JuliaLean.Tasks



def CancellationTokenBodies : Prop := ∀ (state first : Nat) (_rest : List Nat),
  cancellationSeverity 0 = none ∧
  cancellationIsCancelled state = (state != 0) ∧
  uniqueParents first [] = [first] ∧
  (raiseCancellation state first).2 = max state first

theorem cancellationTokenBodies_proven : CancellationTokenBodies := by
  intro state first rest
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · unfold raiseCancellation
    split <;> omega

def CancellationSlotBodies : Prop := ∀ (task : Option Nat) (count owner : Nat),
  (waitEntry task count).slots.length = count ∧
  (findWaitSlot (waitEntry task 1) none = 1) ∧
  (match acquireWaitSlot (waitEntry task 1) owner with
    | some entry => (waitSlot entry 1).owner = some owner
    | none => False)

theorem cancellationSlotBodies_proven : CancellationSlotBodies := by
  intro task count owner
  constructor
  · simp [waitEntry]
  constructor
  · simp [findWaitSlot, findWaitSlotFrom, waitEntry, emptyWaitSlot]
  · simp [acquireWaitSlot, findWaitSlot, findWaitSlotFrom, waitEntry, emptyWaitSlot,
      setWaitSlot, waitSlot]

def CancellationArmBodies : Prop := ∀ (state : WaitArm) (entry : Nat),
  (armWait ⟨none, false⟩ entry = some ⟨some entry, true⟩) ∧
  (claimWait ⟨some entry, true⟩ entry = (true, ⟨none, false⟩)) ∧
  (state.armed → armWait state entry = none)

theorem cancellationArmBodies_proven : CancellationArmBodies := by
  intro state entry
  constructor
  · simp [armWait]
  constructor
  · simp [claimWait]
  · intro armed
    simp [armWait, armed]

def CancellationRegistrationBodies : Prop := ∀ (state : RegistrationState) (waiter : Nat),
  (unregisterBody state waiter).waiters.length ≤ state.waiters.length ∧
  (retireBody state waiter).waiters.length ≤ state.waiters.length ∧
  (noteDeadBody state).deadCount = state.deadCount + 1

theorem cancellationRegistrationBodies_proven : CancellationRegistrationBodies := by
  unfold CancellationRegistrationBodies
  intro state waiter
  exact ⟨List.length_erase_le, List.length_erase_le, rfl⟩

def CancellationDeliveryBodies : Prop := ∀ (state severity current status : Nat)
    (hasSource preempt : Bool),
  (validCancellationSeverity severity = true →
    cancelBody state severity = .ok (raiseCancellation state severity)) ∧
  redeliverBody state = (state != 0) ∧
  walkNodeBody severity current = max severity current ∧
  handleCancellationBody hasSource preempt status current =
    (if preempt && (!hasSource || status % 64 == 0) then .ok ()
     else if hasSource && status % 64 != 0 then .error current else .ok ())

theorem cancellationDeliveryBodies_proven : CancellationDeliveryBodies := by
  unfold CancellationDeliveryBodies
  intros
  constructor
  · intro valid; simp [cancelBody, valid]
  exact ⟨rfl, rfl, rfl⟩

def CancellationDefaultBodies : Prop := ∀ (defaultSource : Option Nat)
    (argument : TokenArgument) (state : Nat),
  resolveToken defaultSource .useDefault = defaultSource ∧
  resolveToken defaultSource .none = none ∧
  checkCancelBody none state = .ok () ∧
  cancelSource argument = (match argument with | .token source => some source | _ => none)

theorem cancellationDefaultBodies_proven : CancellationDefaultBodies := by
  intro defaultSource argument state
  cases argument <;> simp [resolveToken, checkCancelBody, cancelSource]

end JuliaLean.Tasks
