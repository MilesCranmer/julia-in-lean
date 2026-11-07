import JuliaLean.Proofs.base.dict.ImmutableClaims
import JuliaLean.Runtime.Float

/-!
# `allunique`, `allequal` and `unique` of ranges, `base/set.jl`

`allunique(r::AbstractRange) = !iszero(step(r)) || length(r) <= 1`
(`base/set.jl:546`) and `allequal(r::AbstractRange) = iszero(step(r)) ||
length(r) <= 1` (`base/set.jl:660`) decide from the step alone. The elements
are modelled for `StepRangeLen{Float64,Float64,Float64}`, whose elements are
`ref + (i - offset) * step` rounded (`base/range.jl:986-989`).
-/

namespace JuliaLean.Dicts

open JuliaLean.Float


/-- Pairwise distinct under `isequal`. -/
def distinctB {α : Type} (eq : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !eq x y) && distinctB eq xs

/-- All elements `isequal` to the first. -/
def allequalB {α : Type} (eq : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (eq x)

/-- `allunique(itr)`: "Return `true` if all values from `itr` are distinct when
compared with `isequal`" (`base/set.jl:484`); `allequal(itr)`: "Return
`true` if all values from `itr` are equal when compared with `isequal`"
(`base/set.jl:613`). For finite `ref` and `step` and moderate lengths, the
range methods must agree with the elements. -/
def RangeAlluniqueElements : Prop :=
  ∀ r : SRL, F64.isfinite r.ref = true → F64.isfinite r.step = true → r.offset = 1 →
    r.len ≤ 2 ^ 20 →
    r.allunique = distinctB F64.isequal r.collect ∧ r.allequal = allequalB F64.isequal r.collect

/-- `1.0e-17` (the correctly rounded literal). -/
def tenToMinus17 : F64 := F64.roundRat 1 (10 ^ 17) false

/-- `StepRangeLen(1.0, 1e-17, 3)`: every element rounds to `1.0`, yet `step(r) != 0`. -/
def subUlpRange : SRL := ⟨F64.one, tenToMinus17, 3, 1⟩

theorem rangeAlluniqueElements_refuted : ¬ RangeAlluniqueElements := by
  intro h
  have hp := h subUlpRange (by decide +kernel) (by decide +kernel) rfl (by decide)
  revert hp
  decide +kernel

end JuliaLean.Dicts
