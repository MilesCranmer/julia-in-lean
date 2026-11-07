import JuliaLean.base.multidimensional

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- All three `hash_shaped` branches depend only on axes, canonical element
isequal classes and the seed. -/
def ArrayHashConsistency : Prop :=
  ∀ a b : CanonArray, a.axes = b.axes → a.values = b.values →
    ∀ h, hashArray a h = hashArray b h

theorem arrayHashConsistency_proven : ArrayHashConsistency := by
  rintro ⟨aa, av⟩ ⟨ba, bv⟩ ha hv h
  simp_all

end JuliaLean.HashOps
