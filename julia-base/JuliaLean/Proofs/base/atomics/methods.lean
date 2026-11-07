import JuliaLean.base.atomics
import JuliaLean.Proofs.base.locks_mt.common

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def AtomicCtorContract : Prop :=
  (∀ (α β : Type) (convert : β → R α) value converted,
    convert value = .ok converted → atomicValueCtor convert value = .ok ⟨converted⟩) ∧
  (∀ (α β : Type) (convert : β → R α) value err,
    convert value = .error err → atomicValueCtor convert value = .error err) ∧
  (∀ (α β : Type) (convert : β → R α) err,
    atomicZeroCtor (.error err) convert = .error err) ∧
  (∀ (α β : Type) (convert : β → R α) value converted,
    convert value = .ok converted → atomicZeroCtor (.ok value) convert = .ok ⟨converted⟩)

theorem atomicCtorContract_proven : AtomicCtorContract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β convert value converted h
    simp [atomicValueCtor, h]
  · intro α β convert value err h
    simp [atomicValueCtor, h]
  · intro α β convert err
    rfl
  · intro α β convert value converted h
    simp [atomicZeroCtor, atomicValueCtor, h]

def AtomicDefaultContract : Prop := ∀ _ : Unit, atomicDefaultCtor = .ok ⟨0⟩

theorem atomicDefaultContract_proven : AtomicDefaultContract := by intro _; rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
