import JuliaLean.base.threadcall
import JuliaLean.Proofs.base.locks_mt.common

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def ThreadcallMacroProp : Prop := ∀ tuple f ret tys vals plan,
  threadcallMacro tuple f ret tys vals = .ok plan →
    tuple = true ∧ tys.length = vals.length ∧ plan.argTypes = tys ∧
    plan.argValues = vals ∧ plan.converted = tys.zip vals ∧
    plan.unsafeConverted = tys.zip (List.range vals.length)

theorem threadcallMacro_proven : ThreadcallMacroProp := by
  intro tuple f ret tys vals plan h
  unfold threadcallMacro at h
  split at h <;> rename_i ht
  · cases h
  · split at h <;> rename_i hl
    · cases h
    · cases h
      simp_all

def ThreadcallRunProp : Prop := ∀ call, threadcallRun call = call

theorem threadcallRun_proven : ThreadcallRunProp := by intro call; cases call <;> simp [threadcallRun]

def ThreadcallNotifyProp : Prop := ∀ _task _ctx : Nat,
  threadcallNotify = ⟨true, true, true⟩

theorem threadcallNotify_proven : ThreadcallNotifyProp := by
  unfold ThreadcallNotifyProp
  intros
  rfl

def DoThreadcallProp : Prop := ∀ result,
  doThreadcall result = (result, [.makeRunCallback, .makeNotifyCallback, .boxContext,
    .acquire, .preserveTask, .preserveContext, .queue, .wait, .release, .readResult])

theorem doThreadcall_proven : DoThreadcallProp := by
  unfold DoThreadcallProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
