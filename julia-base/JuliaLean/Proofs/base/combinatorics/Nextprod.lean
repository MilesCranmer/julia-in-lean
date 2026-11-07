import JuliaLean.base.combinatorics

/-! `nextprod`, `base/combinatorics.jl:337-373`. The source calls `nextpow`
for each factor and then enumerates exponent counters. The executable loop is
used for differential checks; the empty-input branch is kernel-reducible for
the refutation theorem. -/

namespace JuliaLean.Combinatorics

open JuliaLean


def IsFactorProduct (a : List Nat) (y : Nat) : Prop :=
  ∃ powers : List Nat, powers.length = a.length ∧
    y = ((a.zip powers).map fun q => q.1 ^ q.2).foldl (· * ·) 1

def NextprodLeast : Prop := ∀ (a : List Nat) (x : Nat),
  0 < x → (∀ factor ∈ a, 2 ≤ factor) →
  ∃ y, nextprod a x = .ok y ∧ IsFactorProduct a y ∧ x ≤ y ∧
    ∀ z, IsFactorProduct a z → x ≤ z → y ≤ z

theorem nextprodLeast_refuted : ¬ NextprodLeast := by
  intro h
  obtain ⟨y, hy, _⟩ := h [] 1 (by omega) (by simp)
  simp [nextprod] at hy

end JuliaLean.Combinatorics
