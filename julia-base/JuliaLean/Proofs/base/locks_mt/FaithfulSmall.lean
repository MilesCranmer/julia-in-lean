import JuliaLean.base.locks_mt

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def SpinLockCtorProp : Prop := ∀ _u : Unit, spinLockCtor = ⟨0, fun _ => 0⟩
theorem spinLockCtor_proven : SpinLockCtorProp := by
  unfold SpinLockCtorProp
  intros
  rfl

def PaddedSpinLockCtorProp : Prop := ∀ _u : Unit, paddedSpinLockCtor.owned = 0
theorem paddedSpinLockCtor_proven : PaddedSpinLockCtorProp := by
  unfold PaddedSpinLockCtorProp
  intros
  rfl

def SpinAssertHavelockProp : Prop := ∀ violation l,
  spinAssertHavelock violation l = if Locks.spinIslocked l then .ok () else violation
theorem spinAssertHavelock_proven : SpinAssertHavelockProp := by
  unfold SpinAssertHavelockProp
  intros
  rfl

def SpinLockLoopProp : Prop := ∀ task l rest acquired,
  Locks.spinTrylock task l = (true, acquired) → spinLockLoop task (l :: rest) = some (acquired, [])
theorem spinLockLoop_proven : SpinLockLoopProp := by
  intro task l rest acquired h
  simp [spinLockLoop, h]

def SpinTrylockProp : Prop := ∀ task l, spinTrylock task l = Locks.spinTrylock task l
theorem spinTrylock_proven : SpinTrylockProp := by
  unfold SpinTrylockProp
  intros
  rfl

def SpinUnlockProp : Prop := ∀ task l,
  spinUnlock (fun x => x) task l = Locks.spinUnlock task l
theorem spinUnlock_proven : SpinUnlockProp := by
  unfold SpinUnlockProp
  intros
  rfl

def SpinIslockedProp : Prop := ∀ load l,
  spinIslocked load l = (load l.owned != 0)
theorem spinIslocked_proven : SpinIslockedProp := by
  unfold SpinIslockedProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
