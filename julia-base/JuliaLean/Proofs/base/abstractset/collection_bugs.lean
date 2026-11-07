import JuliaLean.base.abstractset

/-!
# Refuted collection properties

Small executable models of the six source paths reproduced in Julia. Each
property quantifies over the source method's inputs and each refutation reduces
a concrete counterexample.
-/

namespace JuliaLean.BitSetsCov

namespace Bugs





def RangeIsdisjointSpec : Prop :=
  ∀ minimumA stepA minimumB stepB,
    ∃ result, overlappingRangeIsdisjoint minimumA stepA minimumB stepB = .value result

theorem rangeIsdisjointSpec_refuted : ¬ RangeIsdisjointSpec := by
  intro h
  obtain ⟨result, hr⟩ := h 1 0 1 0
  simp [overlappingRangeIsdisjoint] at hr


def IsdisjointSizeIndependent : Prop :=
  ∀ n, isdisjointThreshold [.positiveZero] (.negativeZero :: List.replicate n .one) =
    isdisjointThreshold [.positiveZero] (.negativeZero :: List.replicate (n + 1) .one)

theorem isdisjointSizeIndependent_refuted : ¬ IsdisjointSizeIndependent := by
  intro h
  have := h 68
  simp [isdisjointThreshold, anyEqual, valueEq, valueIsequal] at this








end Bugs

abbrev RangeIsdisjointSpec := Bugs.RangeIsdisjointSpec
abbrev IsdisjointSizeIndependent := Bugs.IsdisjointSizeIndependent

theorem rangeIsdisjointSpec_refuted : ¬ RangeIsdisjointSpec := Bugs.rangeIsdisjointSpec_refuted
theorem isdisjointSizeIndependent_refuted : ¬ IsdisjointSizeIndependent := Bugs.isdisjointSizeIndependent_refuted

end JuliaLean.BitSetsCov
