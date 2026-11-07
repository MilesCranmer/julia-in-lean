import JuliaLean.base.reshapedarray

namespace JuliaLean.ArrayCov

def ReshapedIteratorProtocol : Prop :=
  ∀ (parentIterate : Nat → Option (Nat × Nat)) (state : Nat),
    parentIterate state = none → reshapedIteratorStep parentIterate state = .ok none

theorem reshapedIteratorProtocol_refuted : ¬ ReshapedIteratorProtocol := by
  intro h
  let exhausted : Nat → Option (Nat × Nat) := fun _ => none
  have bad := h exhausted 0 rfl
  simp [reshapedIteratorStep, exhausted] at bad

end JuliaLean.ArrayCov
