import JuliaLean.base.range
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges

open JuliaLean.Registry


set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- `base/range.jl:935-942`: the element reached by repeated Julia iteration (zero-based position). -/
def iterateAt (r : Rng) : Nat → Jl (Option Num)
  | 0 => iterate r
  | n + 1 => do
      let previous ← iterateAt r n
      match previous with
      | none => pure none
      | some v => iterate r (some v)

/-- Every valid non-Bool scalar position in a UnitRange agrees with its first element and unit step. -/
def UnsignedIndexAgreement : Prop :=
  ∀ a b i r, unit a b = .ok r → i.ty ≠ .bool →
    1 ≤ i.val → i.val ≤ trueCount r →
    ∃ v, getindex r i = .ok v ∧ iterateAt r (i.val - 1).toNat = .ok (some v) ∧
      v.val = (first r).val + i.val - 1

/-- Concrete normalized range constructed by `Int8(-1):Int8(1)`. -/
def negativeUnit : Rng :=
  ⟨.unit, Num.lit (.bit .i8) (-1), Num.one (.bit .i8), Num.lit (.bit .i8) 1⟩

theorem unsignedIndexAgreement_refuted : ¬ UnsignedIndexAgreement := by
  intro h
  obtain ⟨v, hv, _⟩ := h (Num.lit (.bit .i8) (-1)) (Num.lit (.bit .i8) 1)
    (Num.lit (.bit .u8) 1) negativeUnit (by decide) (by decide) (by decide) (by decide)
  have failure : getindex negativeUnit (Num.lit (.bit .u8) 1) = .error .boundsError := by decide
  rw [failure] at hv
  cases hv

/-- A representable mathematical cardinality is returned by checked_length, including extreme negative steps. -/
def CheckedLengthCapacity : Prop :=
  ∀ a s b r, colon3 a s b = .ok r →
    0 ≤ trueCount r → trueCount r ≤ IntTy.i64.max →
    ∃ n, checkedLength r = .ok n ∧ n.val = trueCount r

/-- Concrete two-element range with the most negative Int64 step. -/
def typeminStep : Rng :=
  ⟨.step, Num.zero (.bit .i64), Num.lit (.bit .i64) IntTy.i64.min,
    Num.lit (.bit .i64) IntTy.i64.min⟩

theorem checkedLengthCapacity_refuted : ¬ CheckedLengthCapacity := by
  intro h
  obtain ⟨n, hn, _⟩ := h (Num.zero (.bit .i64)) (Num.lit (.bit .i64) IntTy.i64.min)
    (Num.lit (.bit .i64) IntTy.i64.min) typeminStep (by decide) (by decide) (by decide)
  have failure : checkedLength typeminStep = .error (.inexactError "Int64") := by decide
  rw [failure] at hn
  cases hn

/-- `base/range.jl:428-441`: full-width UnitRange constructor inputs, for each of the ten BitIntegers. -/
def fullWidthUnit (t : IntTy) : Rng :=
  ⟨.unit, Num.lit (.bit t) t.min, Num.one (.bit t), Num.lit (.bit t) t.max⟩

/-- Small element types use Int64 length; large full-width ranges wrap, while checked_length reports overflow. -/
def FullWidthCountBehavior : Prop :=
  ∀ t : IntTy,
    trueCount (fullWidthUnit t) = 2 ^ t.bits ∧
    length (fullWidthUnit t) =
      .ok (Num.lit (if t.bits < 64 then .bit .i64 else .bit t) (2 ^ t.bits)) ∧
    checkedLength (fullWidthUnit t) =
      (if t.bits < 64 then length (fullWidthUnit t)
       else .error (.overflowError "checked arithmetic")) ∧
    isEmpty (fullWidthUnit t) = false

theorem fullWidthCountBehavior_proven : FullWidthCountBehavior := by
  intro t
  cases t <;> decide

/-- Ordinal iteration starts at the same element returned by first. -/
def IterationFirstAgreement : Prop :=
  ∀ r : Rng, isEmpty r = false → iterate r = .ok (some (first r))

theorem iterationFirstAgreement_proven : IterationFirstAgreement := by
  intro r h
  simp [iterate, h]
  rfl

/-- Ordinal iteration stops exactly when its current state equals last. -/
def IterationLastAgreement : Prop :=
  ∀ r i, Num.eq i (last r) = true → iterate r (some i) = .ok none

theorem iterationLastAgreement_proven : IterationLastAgreement := by
  intro r i h
  simp [iterate, h]
  rfl

/-- `base/range.jl:339-350`: a signed endpoint range with a positive unsigned step. -/
def unsignedStepNegative : Rng :=
  ⟨.step, Num.lit (.bit .i64) (-2), Num.one (.bit .u64), Num.lit (.bit .i64) (-1)⟩

/-- A nonempty constructed range reaches last through both scalar indexing and iteration. -/
def OrdinalLastAgreement : Prop :=
  ∀ a s b r n, stepRange a s b = .ok r → length r = .ok n → 0 < n.val →
    getindex r n = .ok (last r) ∧
    iterateAt r (n.val - 1).toNat = .ok (some (last r)) ∧
    iterateAt r n.val.toNat = .ok none

theorem ordinalLastAgreement_refuted : ¬ OrdinalLastAgreement := by
  intro h
  have agreement := h (Num.lit (.bit .i64) (-2)) (Num.one (.bit .u64))
    (Num.lit (.bit .i64) (-1)) unsignedStepNegative (Num.lit (.bit .i64) 2)
    (by decide) (by decide) (by decide)
  have failure : getindex unsignedStepNegative (Num.lit (.bit .i64) 2) =
      .error (.inexactError "Int64") := by decide
  rw [failure] at agreement
  cases agreement.1

/-- `base/range.jl:339-350`: two-element ranges immediately adjacent to each integer extremum. -/
def extremalPair (t : IntTy) (descending : Bool) : Rng :=
  let a := Num.lit (.bit t) (if descending then t.max else t.min)
  let s := Num.lit (.bit .i64) (if descending then -1 else 1)
  let b := Num.lit (.bit t) (if descending then t.max - 1 else t.min + 1)
  ⟨.step, a, s, b⟩

/-- For each width and signedness, ±1 two-element edge ranges agree on first, step, count, indexing and iteration. -/
def ExtremalPairAgreement : Prop :=
  ∀ t : IntTy, ∀ descending : Bool,
    let r := extremalPair t descending
    stepRange (first r) (step r) (last r) = .ok r ∧
    trueCount r = 2 ∧
    length r = .ok (Num.lit (if t.bits < 64 then .bit .i64 else .bit t) 2) ∧
    checkedLength r = length r ∧
    getindex r (Num.lit (.bit .i64) 2) = .ok (last r) ∧
    iterateAt r 1 = .ok (some (last r)) ∧ iterateAt r 2 = .ok none

theorem extremalPairAgreement_proven : ExtremalPairAgreement := by
  intro t descending
  cases t <;> cases descending <;> decide

/-- `base/range.jl:428-441`: large unsigned ranges whose nonzero length exceeds typemax(Int). -/
def unsignedLargeUnit (t : IntTy) : Rng :=
  ⟨.unit, Num.one (.bit t), Num.one (.bit t), Num.lit (.bit t) t.max⟩

/-- UInt64/UInt128 counts need not fit Int64, and their unsigned length still indexes last correctly. -/
def UnsignedLargeCountAgreement : Prop :=
  ∀ t : IntTy, t = .u64 ∨ t = .u128 →
    let r := unsignedLargeUnit t
    let n := Num.lit (.bit t) t.max
    trueCount r = t.max ∧ IntTy.i64.max < trueCount r ∧
    length r = .ok n ∧ checkedLength r = .ok n ∧
    getindex r n = .ok (last r) ∧ isEmpty r = false

theorem unsignedLargeCountAgreement_proven : UnsignedLargeCountAgreement := by
  intro t h
  rcases h with rfl | rfl <;> decide

/-- `base/range.jl:968-971`: a nonpositive scalar UnitRange index is out of bounds. -/
def UnitInvalidLowerIndex : Prop :=
  ∀ r i, r.kind = .unit → i.ty ≠ .bool → i.val ≤ 0 →
    getindex r i = .error .boundsError

theorem unitInvalidLowerIndex_proven : UnitInvalidLowerIndex := by
  intro r i hr hi hn
  have hpos : ¬ i.val > 0 := by omega
  simp [getindex, hr, hi, hpos]

/-- Bool UnitRanges retain Bool steps, reject Bool scalar indices, and agree on emptiness and count. -/
def BoolUnitAgreement : Prop :=
  ∀ a b : Bool,
    let n : Int := if a && !b then 0 else (if b then 1 else 0) - (if a then 1 else 0) + 1
    let r : Rng := ⟨.unit, ⟨.bool, a⟩, Num.one .bool, ⟨.bool, b⟩⟩
    unit ⟨.bool, a⟩ ⟨.bool, b⟩ = .ok r ∧
    step r = Num.one .bool ∧
    length r = .ok (Num.lit (.bit .i64) n) ∧
    checkedLength r = length r ∧
    isEmpty r = decide (n = 0) ∧
    iterateAt r n.toNat = .ok none ∧
    getindex r ⟨.bool, true⟩ = .error (.argumentError "invalid index of type Bool")

theorem boolUnitAgreement_proven : BoolUnitAgreement := by
  intro a b
  cases a <;> cases b <;> decide

def ordinalEntries : List Entry := []

end JuliaLean.Ranges
