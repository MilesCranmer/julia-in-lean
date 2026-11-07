import JuliaLean.base.mpfr

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- Converting NaN to `Rational{BigInt}` throws `InexactError`, as for every other `Rational{T}`
and every lossy conversion (`convert` docstring, `base/essentials.jl`). -/
def RationalOfNaNInexact : Prop :=
  ∀ x : Fl double, x.isnan = true → ∃ fn, rationalBigOfF64 x = .error (.inexactError fn)

theorem rationalOfNaNInexact_refuted : ¬ RationalOfNaNInexact := by
  intro h
  obtain ⟨fn, hfn⟩ := h Fl.nan (by decide)
  simp [rationalBigOfF64, (by decide : (Fl.nan : Fl double).isnan = true)] at hfn

end JuliaLean.BigNums
