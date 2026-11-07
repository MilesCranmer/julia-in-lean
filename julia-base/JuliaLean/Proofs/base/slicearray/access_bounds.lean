import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-! ## `base/slicearray.jl` -/

structure Slice1 where
  parentLen : Nat
  outerLen : Nat

/-- The public `Slices(A, slicemap, ax)` constructor should ensure that every
index accepted by the supplied outer axis maps inside the parent axis. -/
def SlicesAccessesInBounds : Prop :=
  ∀ s : Slice1, ∀ i, OneBasedInBounds s.outerLen i → OneBasedInBounds s.parentLen i

theorem slicesAccessesInBounds_refuted : ¬ SlicesAccessesInBounds := by
  intro h
  have bad := h ⟨2, 3⟩ 3 (by simp [OneBasedInBounds])
  simp [OneBasedInBounds] at bad


end JuliaLean.MemSafety.G5
