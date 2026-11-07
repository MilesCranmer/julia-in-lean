import JuliaLean.base.bitarray

namespace JuliaLean.BitSetsCov

namespace Bugs

def BitSizehintSpec : Prop := ∀ isMachineInt n, bitSizehint isMachineInt n = .ok

theorem bitSizehintSpec_refuted : ¬ BitSizehintSpec := by
  intro h
  have := h false 1
  simp [bitSizehint] at this
end Bugs

abbrev BitSizehintSpec := Bugs.BitSizehintSpec
theorem bitSizehintSpec_refuted : ¬ BitSizehintSpec := Bugs.bitSizehintSpec_refuted
end JuliaLean.BitSetsCov
