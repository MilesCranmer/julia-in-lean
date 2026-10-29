import JuliaLean.Ranges.Counted

/-!
Consequences of `length` wrapping for ranges with 2^64 (or 2^128) elements.
-/

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- `length(r)` of a constructed integer UnitRange is its element count whenever
it returns. -/
def LengthIsCount : Prop :=
  ∀ (a b n : Num) (r : Rng), colon2 a b = .ok r → length r = .ok n → n.val = trueCount r

/-- `base/range.jl:1424-1431`: `Array{T,1}(r)` (and so `collect(r)`) allocates
`length(r)` slots and stores every iterated element with `@inbounds`. The stores
stay in bounds only if iteration ends after `length(r)` elements. -/
def CollectStoresInBounds : Prop :=
  ∀ (a b n : Num) (r : Rng), colon2 a b = .ok r → length r = .ok n → 0 ≤ n.val →
    iterateAt r n.val.toNat = .ok none

/-- `r == s` (any integer-range dispatch between a UnitRange and a StepRangeLen)
implies the two ranges agree on emptiness. -/
def RangeEqRespectsEmptiness : Prop :=
  ∀ (a b : Num) (s : Rng) (r : RngLen) (countedLeft : Bool),
    colon2 a b = .ok s → countedOrdinalEq r s (.ok true) countedLeft →
      countedIsEmpty r = isEmpty s

private def i64 (x : Int) : Num := Num.lit (.bit .i64) x
private def u64 (x : Int) : Num := Num.lit (.bit .u64) x

/-- `typemin(Int):typemax(Int)`. -/
private def fullInt : Rng := ⟨.unit, i64 IntTy.i64.min, i64 1, i64 IntTy.i64.max⟩

/-- `UInt64(0):typemax(UInt64)`. -/
private def fullUInt : Rng := ⟨.unit, u64 0, u64 1, u64 IntTy.u64.max⟩

/-- `range(UInt64(7); length=0)`. -/
private def emptyCounted : RngLen := ⟨u64 7, u64 1, i64 0, i64 1, .bit .u64⟩

theorem lengthIsCount_refuted : ¬ LengthIsCount := by
  intro h
  have bad := h (i64 IntTy.i64.min) (i64 IntTy.i64.max) (i64 0) fullInt rfl rfl
  change (0 : Int) = trueCount fullInt at bad
  have : trueCount fullInt = 2 ^ 64 := by decide
  omega

theorem collectStoresInBounds_refuted : ¬ CollectStoresInBounds := by
  intro h
  have bad := h (i64 IntTy.i64.min) (i64 IntTy.i64.max) (i64 0) fullInt rfl rfl (by decide)
  have actual : iterateAt fullInt 0 = .ok (some (i64 IntTy.i64.min)) := rfl
  change iterateAt fullInt 0 = .ok none at bad
  rw [actual] at bad
  cases bad

theorem rangeEqRespectsEmptiness_refuted : ¬ RangeEqRespectsEmptiness := by
  intro h
  have eq : countedOrdinalEq emptyCounted fullUInt (.ok true) false := by
    have hl : length fullUInt = .ok (u64 0) := rfl
    have hk : fullUInt.kind = .unit := rfl
    simp [countedOrdinalEq, countedGenericEq, resultLength, hl, hk, emptyCounted]
    all_goals first
      | decide
      | exact ⟨by decide, fun h => absurd (by decide) h⟩
      | (intro h; exact absurd (by decide) h)
  have bad := h (u64 0) (u64 IntTy.u64.max) fullUInt emptyCounted false rfl eq
  change true = false at bad
  cases bad

def fullWidthEntries : List Entry := []

end JuliaLean.Ranges
