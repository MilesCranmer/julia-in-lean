import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.bool
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.base.promotion
import JuliaLean.src.runtime_intrinsics_c
import JuliaLean.Proofs.base.float
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

/-!
# Specifications of `base/operators.jl`

The function-valued arguments model the operators and type operations supplied by other Base files
or user-defined methods. The properties below state documented comparison, membership, and widening
contracts independently of the source equations.
-/

namespace JuliaLean.Proofs.base.operators

open JuliaLean JuliaLean.Registry JuliaLean.base.float

/-- For every IEEEFloat `x` and every `Real` `y` (including arbitrary-precision `BigInt` integers
`y : Int`, all fixed-width integers `y : JInt t` of at most 32 bits, and any general `Real` type
whose `<` and `==` agree with exact real ordering on non-NaN inputs), `isless` and `isequal`
between `AbstractFloat` and `Real` in both argument orders form a strict total order, including
`NaN` and signed zero `-0.0` vs `+0`, and `isequal` is symmetric. -/
def MixedIntegerOrder : Prop :=
  (∀ (T : FTy) (t : IntTy) (x : FV T) (y : JInt t), t.bits ≤ 32 →
    let isnanFloat : FV T → Bool := JuliaLean.base.float.isnan_callee (T := T)
    let isnanInteger : JInt t → Bool := JuliaLean.base.float.isnan_Number
    let signFloat : FV T → Bool := JuliaLean.base.float.signbit_float (T := T)
    let signInteger : JInt t → Bool := JuliaLean.base.int.signbit
    let lessFloatReal :=
      JuliaLean.base.operators.islessFloatReal isnanFloat isnanInteger
        signFloat signInteger JuliaLean.base.float.lt_FI x y
    let lessRealFloat :=
      JuliaLean.base.operators.islessRealFloat isnanInteger isnanFloat
        signInteger signFloat JuliaLean.base.float.lt_IF y x
    let equalFloatReal :=
      JuliaLean.base.operators.isequalFloatReal isnanFloat isnanInteger
        signFloat signInteger JuliaLean.base.float.eq_FI x y
    let equalRealFloat :=
      JuliaLean.base.operators.isequalRealFloat isnanInteger isnanFloat
        signInteger signFloat JuliaLean.base.float.eq_IF y x
    (((lessFloatReal && !lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && !lessRealFloat && equalFloatReal)) = true) ∧
      equalFloatReal = equalRealFloat) ∧
  (∀ (T : FTy) (R : Type) (x : FV T) (y : R) (valR : R → Int)
      (isnanR signR : R → Bool) (ltFR eqFR : FV T → R → Bool) (ltRF eqRF : R → FV T → Bool),
    let isnanFloat : FV T → Bool := JuliaLean.base.float.isnan_callee (T := T)
    let signFloat : FV T → Bool := JuliaLean.base.float.signbit_float (T := T)
    isnanR y = false →
    signR y = decide (valR y < 0) →
    ltFR x y = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some (-1)) →
    ltRF y x = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 1) →
    eqFR x y = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0) →
    eqRF y x = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0) →
    let lessFloatReal :=
      JuliaLean.base.operators.islessFloatReal isnanFloat isnanR signFloat signR ltFR x y
    let lessRealFloat :=
      JuliaLean.base.operators.islessRealFloat isnanR isnanFloat signR signFloat ltRF y x
    let equalFloatReal :=
      JuliaLean.base.operators.isequalFloatReal isnanFloat isnanR signFloat signR eqFR x y
    let equalRealFloat :=
      JuliaLean.base.operators.isequalRealFloat isnanR isnanFloat signR signFloat eqRF y x
    (((lessFloatReal && !lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && !lessRealFloat && equalFloatReal)) = true) ∧
      equalFloatReal = equalRealFloat)

theorem mixedIslessTotalGeneral_proven :
    ∀ (T : FTy) (R : Type) (x : FV T) (y : R) (valR : R → Int)
      (isnanR signR : R → Bool) (ltFR eqFR : FV T → R → Bool) (ltRF eqRF : R → FV T → Bool),
    let isnanFloat : FV T → Bool := JuliaLean.base.float.isnan_callee (T := T)
    let signFloat : FV T → Bool := JuliaLean.base.float.signbit_float (T := T)
    isnanR y = false →
    signR y = decide (valR y < 0) →
    ltFR x y = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some (-1)) →
    ltRF y x = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 1) →
    eqFR x y = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0) →
    eqRF y x = (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0) →
    let lessFloatReal :=
      JuliaLean.base.operators.islessFloatReal isnanFloat isnanR signFloat signR ltFR x y
    let lessRealFloat :=
      JuliaLean.base.operators.islessRealFloat isnanR isnanFloat signR signFloat ltRF y x
    let equalFloatReal :=
      JuliaLean.base.operators.isequalFloatReal isnanFloat isnanR signFloat signR eqFR x y
    let equalRealFloat :=
      JuliaLean.base.operators.isequalRealFloat isnanR isnanFloat signR signFloat eqRF y x
    (((lessFloatReal && !lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && !lessRealFloat && equalFloatReal)) = true) ∧
      equalFloatReal = equalRealFloat := by
  intro T R x y valR isnanR signR ltFR eqFR ltRF eqRF isnanFloat signFloat
    hnanR hsignR hlt hgt heq heq' lessFloatReal lessRealFloat equalFloatReal equalRealFloat
  have hnanFloat : isnanFloat x = x.isnan :=
    JuliaLean.Proofs.base.float.isnan_callee_eq x
  have hsignFloat : signFloat x = x.signbit :=
    JuliaLean.Proofs.base.float.signbit_float_eq x
  have hlessFloatReal :
      lessFloatReal =
        ((!x.isnan && (x.signbit && !decide (valR y < 0))) ||
          (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some (-1))) := by
    simp [lessFloatReal, JuliaLean.base.operators.islessFloatReal,
      JuliaLean.base.operators.signless,
      hnanFloat, hnanR, hsignFloat, hsignR, hlt]
  have hlessRealFloat :
      lessRealFloat =
        (x.isnan || (decide (valR y < 0) && !x.signbit) ||
          (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 1)) := by
    simp [lessRealFloat, JuliaLean.base.operators.islessRealFloat,
      JuliaLean.base.operators.signless,
      hnanFloat, hnanR, hsignFloat, hsignR, hgt]
  have hequalFloatReal :
      equalFloatReal =
        ((x.signbit == decide (valR y < 0)) &&
          (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0)) := by
    simp [equalFloatReal, JuliaLean.base.operators.isequalFloatReal,
      JuliaLean.base.operators.signequal,
      hnanFloat, hnanR, hsignFloat, hsignR, heq]
  have hequalRealFloat :
      equalRealFloat =
        ((decide (valR y < 0) == x.signbit) &&
          (JuliaLean.Proofs.base.float.exactOrder x (valR y) == some 0)) := by
    simp [equalRealFloat, JuliaLean.base.operators.isequalRealFloat,
      JuliaLean.base.operators.signequal,
      hnanFloat, hnanR, hsignFloat, hsignR, heq']
  change
    (((lessFloatReal && !lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && lessRealFloat && !equalFloatReal) ||
      (!lessFloatReal && !lessRealFloat && equalFloatReal)) = true) ∧
      equalFloatReal = equalRealFloat
  rw [hlessFloatReal, hlessRealFloat, hequalFloatReal, hequalRealFloat]
  constructor
  · cases hn : x.isnan
    · have hsign := JuliaLean.Proofs.base.float.exactOrder_sign T x hn (valR y)
      rcases JuliaLean.Proofs.base.float.exactOrder_cases x hn (valR y) with
        h | h | h <;> rw [h] at hsign ⊢ <;>
        cases hsb : x.signbit <;> by_cases hy : valR y < 0 <;> simp_all
    · have hnone : JuliaLean.Proofs.base.float.exactOrder x (valR y) = none := by
        simp [JuliaLean.Proofs.base.float.exactOrder, hn]
      rw [hnone]
      simp
  · cases sx : x.signbit <;>
      cases sy : decide (valR y < 0) <;> simp

theorem mixedIntegerOrder_proven : MixedIntegerOrder := by
  refine ⟨?_, mixedIslessTotalGeneral_proven⟩
  intro T t x y ht
  have hcmp := JuliaLean.Proofs.base.float.mixedCompareSmall_proven T t x y ht
  rcases hcmp with ⟨heq, hlt, _, heq', hgt, _⟩
  have hsignInteger : JuliaLean.base.int.signbit y = decide (y.val < 0) := by
    unfold JuliaLean.base.int.signbit
    cases ht' : t.signed with
    | false =>
      rcases (JuliaLean.Proofs.base.int.signPredicates_proven t y).2 ht' with ⟨h, _⟩
      exact h
    | true =>
      exact (JuliaLean.Proofs.base.int.signPredicates_proven t y).1
  exact mixedIslessTotalGeneral_proven T (JInt t) x y (·.val)
    JuliaLean.base.float.isnan_Number JuliaLean.base.int.signbit
    JuliaLean.base.float.lt_FI JuliaLean.base.float.eq_FI
    JuliaLean.base.float.lt_IF JuliaLean.base.float.eq_IF
    rfl hsignInteger hlt hgt heq heq'

section GenericRealOrder
open JuliaLean.base.operators

/-- Numeric comparisons are trichotomous outside NaNs, symmetric in equality, and
compatible with sign bits. The source total-order methods then include NaNs and signed zero. -/
def MixedRealOrder : Prop :=
  ∀ (A B : Type) (nanA signA : A → Bool) (nanB signB : B → Bool)
    (ltAB eqAB : A → B → Bool) (ltBA eqBA : B → A → Bool) (x : A) (y : B),
  eqAB x y = eqBA y x →
  ((nanA x || nanB y) = true →
    ltAB x y = false ∧ ltBA y x = false ∧ eqAB x y = false) →
  (nanA x = false → nanB y = false →
    ((ltAB x y && !ltBA y x && !eqAB x y) ||
     (!ltAB x y && ltBA y x && !eqAB x y) ||
     (!ltAB x y && !ltBA y x && eqAB x y)) = true) →
  (signA x = true → signB y = false → ltBA y x = false) →
  (signA x = false → signB y = true → ltAB x y = false) →
  let lessAB := islessFloatReal nanA nanB signA signB ltAB x y
  let lessBA := islessRealFloat nanB nanA signB signA ltBA y x
  let equalAB := isequalFloatReal nanA nanB signA signB eqAB x y
  let equalBA := isequalRealFloat nanB nanA signB signA eqBA y x
  (((lessAB && !lessBA && !equalAB) ||
    (!lessAB && lessBA && !equalAB) ||
    (!lessAB && !lessBA && equalAB)) = true) ∧ equalAB = equalBA

theorem mixedRealOrder_proven : MixedRealOrder := by
  intro A B nanA signA nanB signB ltAB eqAB ltBA eqBA x y heq hnan htri hsignAB hsignBA
  dsimp only
  unfold islessFloatReal islessRealFloat isequalFloatReal isequalRealFloat signequal signless
  rw [← heq]
  cases hna : nanA x <;> cases hnb : nanB y <;>
    cases hsa : signA x <;> cases hsb : signB y <;>
    cases hlt : ltAB x y <;> cases hgt : ltBA y x <;> cases he : eqAB x y <;>
    simp_all [bitAnd, bitOr]

end GenericRealOrder

/-- Mixed Float/Real ordering includes the concrete fixed-width integer theorem, arbitrary
integer-valued representations, and all numeric comparison interfaces, including fractional
values and NaNs, satisfying the documented primitive comparison and sign laws. -/
def MixedIslessTotalSmall : Prop := MixedIntegerOrder ∧ MixedRealOrder

theorem mixedIslessTotalSmall_proven : MixedIslessTotalSmall :=
  ⟨mixedIntegerOrder_proven, mixedRealOrder_proven⟩

/- The generic comparison order supplied to the source `min`, `max`, and `minmax` methods. -/
structure IslessTotalOrder {α : Type} (lt eq : α → α → Bool) : Prop where
  irreflexive : ∀ x, lt x x = false
  transitive : ∀ x y z, lt x y = true → lt y z = true → lt x z = true
  partition : ∀ x y,
    (lt x y = true ∧ lt y x = false ∧ eq x y = false) ∨
    (lt x y = false ∧ lt y x = true ∧ eq x y = false) ∨
    (lt x y = false ∧ lt y x = false ∧ eq x y = true)
private theorem islessTotalOrderIsequalIff {α : Type} {lt eq : α → α → Bool}
    (order : IslessTotalOrder lt eq) (x y : α) :
    (eq x y = true) ↔ (lt x y = false ∧ lt y x = false) := by
  rcases order.partition x y with hxy | hyx | heq
  · constructor
    · intro h
      rw [hxy.2.2] at h
      cases h
    · intro h
      rw [hxy.1] at h
      cases h.1
  · constructor
    · intro h
      rw [hyx.2.2] at h
      cases h
    · intro h
      rw [hyx.2.1] at h
      cases h.2
  · constructor
    · intro _
      exact ⟨heq.1, heq.2.1⟩
    · intro _
      exact heq.2.2

private theorem islessAsymm {α : Type} {lt eq : α → α → Bool}
    (order : IslessTotalOrder lt eq) {x y : α}
    (hxy : lt x y = true) : lt y x = false := by
  cases hyx : lt y x with
  | false => rfl
  | true =>
      have hxx := order.transitive x y x hxy hyx
      simp [order.irreflexive x] at hxx

private theorem islessOrEqualOfNotReverse {α : Type} {lt eq : α → α → Bool}
    (order : IslessTotalOrder lt eq) {x y : α}
    (hyx : lt y x = false) : lt x y = true ∨ eq x y = true := by
  rcases order.partition x y with hxy | hyx' | heq
  · exact Or.inl hxy.1
  · simp [hyx] at hyx'
  · exact Or.inr heq.2.2

private theorem islessNotEqualOfReverse {α : Type} {lt eq : α → α → Bool}
    (order : IslessTotalOrder lt eq) {x y : α}
    (hyx : lt y x = true) : eq x y = false := by
  rcases order.partition x y with hxy | hyx' | heq
  · rw [hyx] at hxy
    cases hxy.2.1
  · exact hyx'.2.2
  · rw [hyx] at heq
    cases heq.2.1

/-- The generic `min` and `max` methods return extrema under Julia's documented total-order
contract for `isless` and `isequal`. -/
def MinMaxIsless : Prop :=
  ∀ (α : Type) (lt eq : α → α → Bool) (x y : α),
    IslessTotalOrder lt eq →
    let mn := JuliaLean.base.operators.min lt
      JuliaLean.base.operators.ifelseValue x y
    let mx := JuliaLean.base.operators.max lt
      JuliaLean.base.operators.ifelseValue x y
    (mn = x ∨ mn = y) ∧ lt x mn = false ∧ lt y mn = false ∧
    (mx = x ∨ mx = y) ∧ lt mx x = false ∧ lt mx y = false ∧
    (lt x y = true → mn = x ∧ mx = y) ∧
    (lt y x = true → mn = y ∧ mx = x) ∧
    (eq x y = true → mn = x ∧ mx = y)

theorem minMaxIsless_proven : MinMaxIsless := by
  intro α lt eq x y order mn mx
  have hxx := order.irreflexive x
  have hyy := order.irreflexive y
  have hmn : mn = JuliaLean.base.operators.ifelseValue (lt y x) y x := rfl
  have hmx : mx = JuliaLean.base.operators.ifelseValue (lt y x) x y := rfl
  cases hyx : lt y x with
  | false =>
      have hmnVal : mn = x := by
        simp [hmn, hyx, JuliaLean.base.operators.ifelseValue]
      have hmxVal : mx = y := by
        simp [hmx, hyx, JuliaLean.base.operators.ifelseValue]
      rw [hmnVal, hmxVal]
      refine ⟨Or.inl rfl, hxx, hyx, Or.inr rfl, hyx, hyy, ?_, ?_, ?_⟩
      · intro _
        exact ⟨rfl, rfl⟩
      · intro h
        cases h
      · intro _
        exact ⟨rfl, rfl⟩
  | true =>
      have hmnVal : mn = y := by
        simp [hmn, hyx, JuliaLean.base.operators.ifelseValue]
      have hmxVal : mx = x := by
        simp [hmx, hyx, JuliaLean.base.operators.ifelseValue]
      have hxy := islessAsymm order hyx
      have hne := islessNotEqualOfReverse order hyx
      rw [hmnVal, hmxVal]
      refine ⟨Or.inr rfl, hxy, hyy, Or.inl rfl, hxx, hxy, ?_, ?_, ?_⟩
      · intro h
        rw [hxy] at h
        cases h
      · intro _
        exact ⟨rfl, rfl⟩
      · intro heq
        rw [hne] at heq
        cases heq

/-! ## Widening property stated on the source model -/

/-- After `widen` on same-type fixed-width integers, their sum and difference equal the exact
mathematical results. -/
def WidenNoLoss : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    let wx := JuliaLean.base.operators.widenValue
      (fun input : Σ t : IntTy, JInt t => JuliaLean.base.int.widenType input.1)
      (fun target input =>
        (target, match target with
          | none => input.2.val
          | some wide => (JuliaLean.base.int.widenTo wide input.2).val))
      (fun input => input) ⟨t, x⟩
    let wy := JuliaLean.base.operators.widenValue
      (fun input : Σ t : IntTy, JInt t => JuliaLean.base.int.widenType input.1)
      (fun target input =>
        (target, match target with
          | none => input.2.val
          | some wide => (JuliaLean.base.int.widenTo wide input.2).val))
      (fun input => input) ⟨t, y⟩
    let widenedAdd := match wx.1 with
      | none => wx.2 + wy.2
      | some wide => (JuliaLean.base.int.add (JInt.wrap wide wx.2) (JInt.wrap wide wy.2)).val
    let widenedSub := match wx.1 with
      | none => wx.2 - wy.2
      | some wide => (JuliaLean.base.int.sub (JInt.wrap wide wx.2) (JInt.wrap wide wy.2)).val
    widenedAdd = x.val + y.val ∧ widenedSub = x.val - y.val

theorem widenNoLoss_refuted : ¬ WidenNoLoss := by
  intro h
  have hsub := (h .u8 (JInt.lit .u8 0) (JInt.lit .u8 255)).2
  have hsub' :
      (JuliaLean.base.int.sub
        (JInt.wrap .u16
          (JuliaLean.base.int.widenTo .u16 (JInt.lit .u8 0)).val)
        (JInt.wrap .u16
          (JuliaLean.base.int.widenTo .u16 (JInt.lit .u8 255)).val)).val =
        (JInt.lit .u8 0).val - (JInt.lit .u8 255).val := by
    simpa [WidenNoLoss, JuliaLean.base.operators.widenValue,
      JuliaLean.base.int.widenType, JuliaLean.base.int.widen_UInt8,
      JuliaLean.base.int.widenTo, JInt.wrap] using hsub
  have hvalue :
      (JuliaLean.base.int.sub
        (JInt.wrap .u16
          (JuliaLean.base.int.widenTo .u16 (JInt.lit .u8 0)).val)
        (JInt.wrap .u16
          (JuliaLean.base.int.widenTo .u16 (JInt.lit .u8 255)).val)).val = 65281 := by
    decide
  have hexpected : (JInt.lit .u8 0).val - (JInt.lit .u8 255).val = -255 := by
    decide
  rw [hvalue, hexpected] at hsub'
  omega



open JuliaLean.base.operators


/-- Existential element match over a heterogeneous tuple `HTuple Elem ts`. -/
def htupleAny {τ β : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → β → Truth) (x : β) :
    {ts : List τ} → HTuple Elem ts → Truth → Prop
  | [], .nil, _ => False
  | _ :: _, .cons v rest, target => eq v x = target ∨ htupleAny eq x rest target

/-- Universal false comparison over a heterogeneous tuple `HTuple Elem ts`. -/
def htupleAllFalse {τ β : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → β → Truth) (x : β) :
    {ts : List τ} → HTuple Elem ts → Prop
  | [], .nil => True
  | _ :: _, .cons v rest => eq v x = .false ∧ htupleAllFalse eq x rest

/-- Convert a heterogeneous tuple into a tagged list for `any(==(x), itr)` comparison. -/
def htupleToList {τ : Type} {Elem : τ → Type} :
    {ts : List τ} → HTuple Elem ts → List (Σ t : τ, Elem t)
  | [], .nil => []
  | _ :: _, .cons v rest => ⟨_, v⟩ :: htupleToList rest

theorem tupleMembershipHelper_proven :
    ∀ (τ β : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → β → Truth) (x : β)
      (ts : List τ) (xs : HTuple Elem ts) (initial : Truth),
      htupleAny eq x xs .true →
        inTupleHelper eq x xs initial = .true := by
  intro τ β Elem eq x ts xs initial
  induction xs generalizing initial with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      cases hhead : eq y x with
      | true => simp [inTupleHelper, hhead]
      | false =>
          rcases h with h | h
          · change eq y x = .true at h; rw [hhead] at h; cases h
          · simpa [inTupleHelper, hhead] using ih (Truth.or initial .false) h
      | missing =>
          rcases h with h | h
          · change eq y x = .true at h; rw [hhead] at h; cases h
          · simpa [inTupleHelper, hhead] using ih (Truth.or initial .missing) h

/-- Heterogeneous tuple membership returns `.true` whenever any heterogeneously typed
element compares `.true` to `x`, even after an earlier element comparison returns `.missing`. -/
def TupleMembershipMatch : Prop :=
  ∀ (τ β : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → β → Truth) (x : β)
    (ts : List τ) (xs : HTuple Elem ts) (initial : Truth),
    htupleAny eq x xs .true →
      inTupleHelper eq x xs initial = .true ∧
      inTuple eq x xs = .true

theorem tupleMembershipMatch_proven : TupleMembershipMatch := by
  intro τ β Elem eq x ts xs initial h
  exact ⟨tupleMembershipHelper_proven τ β Elem eq x ts xs initial h,
    tupleMembershipHelper_proven τ β Elem eq x ts xs .false h⟩

/-- Documented primitive comparison laws for a numeric `AbstractFloat` type. -/
structure AbstractFloatPrimitiveLaws {α : Type}
    (nan sign : α → Bool) (lt eq : α → α → Bool)
    (negativeZero positiveZero : α) : Prop where
  nanComparison : ∀ x y, (nan x = true ∨ nan y = true) →
    lt x y = false ∧ lt y x = false ∧ eq x y = false
  finiteComparison : ∀ x y, nan x = false → nan y = false →
    (lt x y = true ∧ lt y x = false ∧ eq x y = false) ∨
    (lt x y = false ∧ lt y x = true ∧ eq x y = false) ∨
    (lt x y = false ∧ lt y x = false ∧ eq x y = true)
  lessTransitive : ∀ x y z, nan x = false → nan y = false → nan z = false →
    lt x y = true → lt y z = true → lt x z = true
  equalReflexive : ∀ x, nan x = false → eq x x = true
  equalSymmetric : ∀ x y, nan x = false → nan y = false →
    eq x y = true → eq y x = true
  equalTransitive : ∀ x y z, nan x = false → nan y = false → nan z = false →
    eq x y = true → eq y z = true → eq x z = true
  signCompatible : ∀ x y, sign x = false → sign y = true → lt x y = false
  negativeZeroFinite : nan negativeZero = false
  positiveZeroFinite : nan positiveZero = false
  zeroesEqual : eq negativeZero positiveZero = true
  negativeZeroSign : sign negativeZero = true
  positiveZeroSign : sign positiveZero = false
private theorem abstractFloatIslessFormula {α : Type}
    (nan sign : α → Bool) (lt : α → α → Bool) (x y : α) :
    JuliaLean.base.operators.islessFloatFloat nan sign lt x y =
      ((!nan x && (nan y || (sign x && !sign y))) || lt x y) := by
  simp only [JuliaLean.base.operators.islessFloatFloat,
    JuliaLean.base.operators.signless, JuliaLean.base.operators.unaryPredPair_same_left,
    JuliaLean.base.operators.unaryPredPair_same_right, JuliaLean.base.operators.bitAnd_eq,
    JuliaLean.base.operators.bitOr_eq]

private theorem abstractFloatIsequalFormula {α : Type}
    (nan sign : α → Bool) (eq : α → α → Bool) (x y : α) :
    JuliaLean.base.operators.isequalFloatFloat nan sign eq x y =
      ((nan x && nan y) || ((sign x == sign y) && eq x y)) := by
  simp only [JuliaLean.base.operators.isequalFloatFloat,
    JuliaLean.base.operators.signequal, JuliaLean.base.operators.unaryPredPair_same_left,
    JuliaLean.base.operators.unaryPredPair_same_right, JuliaLean.base.operators.bitAnd_eq,
    JuliaLean.base.operators.bitOr_eq]

private theorem abstractFloatIsequalSpec {α : Type} {negativeZero positiveZero : α}
    (nan sign : α → Bool) (lt eq : α → α → Bool)
    (laws : AbstractFloatPrimitiveLaws nan sign lt eq negativeZero positiveZero) (x y : α) :
    JuliaLean.base.operators.isequalFloatFloat nan sign eq x y = true ↔
      ((nan x = true ∧ nan y = true) ∨
        (nan x = false ∧ nan y = false ∧ sign x = sign y ∧ eq x y = true)) := by
  rw [abstractFloatIsequalFormula]
  cases hnX : nan x <;> cases hnY : nan y <;>
    cases hsX : sign x <;> cases hsY : sign y <;> cases heq : eq x y <;>
    simp_all [laws.nanComparison]


private theorem finiteIslessTrue {α : Type} (nan sign : α → Bool)
    (lt : α → α → Bool) (x y : α) (hnX : nan x = false) (hnY : nan y = false)
    (h : JuliaLean.base.operators.islessFloatFloat nan sign lt x y = true) :
    (sign x = true ∧ sign y = false) ∨ lt x y = true := by
  rw [abstractFloatIslessFormula] at h
  simp [hnX, hnY] at h
  cases hsX : sign x <;> cases hsY : sign y <;> simp_all


/-- On typed non-IEEE `AbstractFloat` interfaces obeying those primitive laws, the generic
methods define a strict total order, with `isequal` as its equivalence and signed zeros distinct. -/
def GenericAbstractFloatNaNSemantics : Prop :=
  ∀ (α : Type) (nan sign : α → Bool) (eq lt : α → α → Bool)
    (negativeZero positiveZero : α),
    AbstractFloatPrimitiveLaws nan sign lt eq negativeZero positiveZero →
    let isless := JuliaLean.base.operators.islessFloatFloat nan sign lt
    let isequal := JuliaLean.base.operators.isequalFloatFloat nan sign eq
    IslessTotalOrder isless isequal ∧
    (∀ x, isequal x x = true) ∧
    (∀ x y, isequal x y = true → isequal y x = true) ∧
    (∀ x y z, isequal x y = true → isequal y z = true → isequal x z = true) ∧
    (∀ x y, nan x = true → nan y = true → isequal x y = true) ∧
    (∀ x y, isequal x y = true ↔ (isless x y = false ∧ isless y x = false)) ∧
    isequal negativeZero positiveZero = false ∧
    (∀ x y, nan x = false → nan y = true → isless x y = true) ∧
    (∀ x y, nan x = true → nan y = false → isless x y = false)

theorem genericAbstractFloatNaNSemantics_proven : GenericAbstractFloatNaNSemantics := by
  intro α nan sign eq lt negativeZero positiveZero laws isless isequal
  have hIsequalSpec := abstractFloatIsequalSpec nan sign lt eq laws
  have hOrder : IslessTotalOrder isless isequal := by
    constructor
    · intro x
      cases hn : nan x with
      | true =>
          have hnan := laws.nanComparison x x (Or.inl hn)
          cases hs : sign x <;>
            simp [isless, JuliaLean.base.operators.islessFloatFloat,
              JuliaLean.base.operators.signless, JuliaLean.base.operators.bitAnd,
              JuliaLean.base.operators.bitOr, hn, hnan.1, hs]
      | false =>
          have hfinite := laws.finiteComparison x x hn hn
          have hlt : lt x x = false := by
            rcases hfinite with h | h | h
            · have hbad : true = false := h.1.symm.trans h.2.1
              cases hbad
            · exact h.1
            · exact h.1
          cases hs : sign x <;>
            simp [isless, JuliaLean.base.operators.islessFloatFloat,
              JuliaLean.base.operators.signless, JuliaLean.base.operators.bitAnd,
              JuliaLean.base.operators.bitOr, hn, hlt, hs]
    · intro x y z hxy hyz
      by_cases hnX : nan x = true
      · have hnan := laws.nanComparison x y (Or.inl hnX)
        have hfalse : isless x y = false := by
          change JuliaLean.base.operators.islessFloatFloat nan sign lt x y = false
          rw [abstractFloatIslessFormula nan sign lt x y]
          simp [hnX, hnan.1]
        rw [hfalse] at hxy
        cases hxy
      · have hnX' : nan x = false := by cases h : nan x <;> simp_all
        by_cases hnY : nan y = true
        · have hnan := laws.nanComparison y z (Or.inl hnY)
          have hfalse : isless y z = false := by
            change JuliaLean.base.operators.islessFloatFloat nan sign lt y z = false
            rw [abstractFloatIslessFormula nan sign lt y z]
            simp [hnY, hnan.1]
          rw [hfalse] at hyz
          cases hyz
        · have hnY' : nan y = false := by cases h : nan y <;> simp_all
          by_cases hnZ : nan z = true
          · have htrue : isless x z = true := by
              change JuliaLean.base.operators.islessFloatFloat nan sign lt x z = true
              rw [abstractFloatIslessFormula nan sign lt x z]
              simp [hnX', hnZ]
            exact htrue
          · have hnZ' : nan z = false := by cases h : nan z <;> simp_all
            have hxyCases :
                (sign x = true ∧ sign y = false) ∨ lt x y = true :=
              finiteIslessTrue nan sign lt x y hnX' hnY' hxy
            have hyzCases :
                (sign y = true ∧ sign z = false) ∨ lt y z = true :=
              finiteIslessTrue nan sign lt y z hnY' hnZ' hyz
            rcases hxyCases with ⟨hnegX, hposY⟩ | hltXY
            · rcases hyzCases with ⟨hnegY, hposZ⟩ | hltYZ
              · rw [hposY] at hnegY
                cases hnegY
              · have hnegZ : sign z = false := by
                  cases hz : sign z with
                  | false => rfl
                  | true =>
                    have hbad := laws.signCompatible y z hposY hz
                    rw [hltYZ] at hbad
                    cases hbad
                change JuliaLean.base.operators.islessFloatFloat nan sign lt x z = true
                rw [abstractFloatIslessFormula nan sign lt x z]
                simp [hnX', hnZ', hnegX, hnegZ]
            · rcases hyzCases with ⟨hnegY, hposZ⟩ | hltYZ
              · have hnegX : sign x = true := by
                  cases hx : sign x with
                  | false =>
                    have hbad := laws.signCompatible x y hx hnegY
                    rw [hltXY] at hbad
                    cases hbad
                  | true => rfl
                change JuliaLean.base.operators.islessFloatFloat nan sign lt x z = true
                rw [abstractFloatIslessFormula nan sign lt x z]
                simp [hnX', hnZ', hnegX, hposZ]
              · have hltXZ := laws.lessTransitive x y z hnX' hnY' hnZ' hltXY hltYZ
                change JuliaLean.base.operators.islessFloatFloat nan sign lt x z = true
                rw [abstractFloatIslessFormula nan sign lt x z]
                simp [hnX', hnZ', hltXZ]
    · intro x y
      by_cases hnX : nan x = true
      · by_cases hnY : nan y = true
        · have hxy : isless x y = false := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt x y]
            have hnan := laws.nanComparison x y (Or.inl hnX)
            simp [hnX, hnY, hnan.1]
          have hyx : isless y x = false := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt y x]
            have hnan := laws.nanComparison y x (Or.inl hnY)
            simp [hnY, hnX, hnan.1]
          have heq : isequal x y = true := by
            exact (hIsequalSpec x y).2 (Or.inl ⟨hnX, hnY⟩)
          exact Or.inr (Or.inr ⟨hxy, hyx, heq⟩)
        · have hnY' : nan y = false := by cases h : nan y <;> simp_all
          have hxy : isless x y = false := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt x y]
            have hnan := laws.nanComparison x y (Or.inl hnX)
            simp [hnX, hnY', hnan.1]
          have hyx : isless y x = true := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt y x]
            simp [hnY', hnX]
          have heq : isequal x y = false := by
            cases he : isequal x y with
            | false => rfl
            | true =>
                rcases (hIsequalSpec x y).1 he with hnan | hfinite
                · have hbad : false = true := hnY'.symm.trans hnan.2
                  cases hbad
                · have hbad : false = true := hfinite.1.symm.trans hnX
                  cases hbad
          exact Or.inr (Or.inl ⟨hxy, hyx, heq⟩)
      · have hnX' : nan x = false := by cases h : nan x <;> simp_all
        by_cases hnY : nan y = true
        · have hxy : isless x y = true := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt x y]
            simp [hnX', hnY]
          have hyx : isless y x = false := by
            dsimp only [isless]
            rw [abstractFloatIslessFormula nan sign lt y x]
            have hnan := laws.nanComparison x y (Or.inr hnY)
            simp [hnX', hnY, hnan.2.1]
          have heq : isequal x y = false := by
            cases he : isequal x y with
            | false => rfl
            | true =>
                rcases (hIsequalSpec x y).1 he with hnan | hfinite
                · have hbad : false = true := hnX'.symm.trans hnan.1
                  cases hbad
                · have hbad : false = true := hfinite.2.1.symm.trans hnY
                  cases hbad
          exact Or.inl ⟨hxy, hyx, heq⟩
        · have hnY' : nan y = false := by cases h : nan y <;> simp_all
          rcases laws.finiteComparison x y hnX' hnY' with hxyLess | hyxLess | hxyEq
          · cases hsX : sign x with
            | false =>
                cases hsY : sign y with
                | false =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyLess.1, hxyLess.2.1, hxyLess.2.2]
                | true =>
                    have hbad := laws.signCompatible x y hsX hsY
                    rw [hxyLess.1] at hbad
                    cases hbad
            | true =>
                cases hsY : sign y with
                | false =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyLess.1, hxyLess.2.1, hxyLess.2.2]
                | true =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyLess.1, hxyLess.2.1, hxyLess.2.2]
          · cases hsX : sign x with
            | false =>
                cases hsY : sign y with
                | false =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hyxLess.1, hyxLess.2.1, hyxLess.2.2]
                | true =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hyxLess.1, hyxLess.2.1, hyxLess.2.2]
            | true =>
                cases hsY : sign y with
                | false =>
                    have hbad := laws.signCompatible y x hsY hsX
                    rw [hyxLess.2.1] at hbad
                    cases hbad
                | true =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hyxLess.1, hyxLess.2.1, hyxLess.2.2]
          · cases hsX : sign x with
            | false =>
                cases hsY : sign y with
                | false =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyEq.1, hxyEq.2.1, hxyEq.2.2]
                | true =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyEq.1, hxyEq.2.1, hxyEq.2.2]
            | true =>
                cases hsY : sign y with
                | false =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyEq.1, hxyEq.2.1, hxyEq.2.2]
                | true =>
                    simp [isless, isequal, abstractFloatIslessFormula,
                      abstractFloatIsequalFormula, hnX', hnY', hsX, hsY,
                      hxyEq.1, hxyEq.2.1, hxyEq.2.2]
  have hIsequalReflexive : ∀ x, isequal x x = true := by
    intro x
    cases hn : nan x with
    | true =>
        apply (hIsequalSpec x x).2
        exact Or.inl ⟨hn, hn⟩
    | false =>
        apply (hIsequalSpec x x).2
        exact Or.inr ⟨hn, hn, rfl, laws.equalReflexive x hn⟩
  have hIsequalSymmetric : ∀ x y, isequal x y = true → isequal y x = true := by
    intro x y hxy
    rcases (hIsequalSpec x y).1 hxy with hnan | hfinite
    · apply (hIsequalSpec y x).2
      exact Or.inl ⟨hnan.2, hnan.1⟩
    · rcases hfinite with ⟨hnX, hnY, hsign, heq⟩
      apply (hIsequalSpec y x).2
      exact Or.inr ⟨hnY, hnX, hsign.symm,
        laws.equalSymmetric x y hnX hnY heq⟩
  have hIsequalTransitive :
      ∀ x y z, isequal x y = true → isequal y z = true → isequal x z = true := by
    intro x y z hxy hyz
    rcases (hIsequalSpec x y).1 hxy with hnanXY | hfiniteXY
    · rcases (hIsequalSpec y z).1 hyz with hnanYZ | hfiniteYZ
      · apply (hIsequalSpec x z).2
        exact Or.inl ⟨hnanXY.1, hnanYZ.2⟩
      · rcases hfiniteYZ with ⟨hnY, _, _, _⟩
        have hbad : false = true := hnY.symm.trans hnanXY.2
        cases hbad
    · rcases hfiniteXY with ⟨hnX, hnY, hsignXY, heqXY⟩
      rcases (hIsequalSpec y z).1 hyz with hnanYZ | hfiniteYZ
      · have hbad : false = true := hnY.symm.trans hnanYZ.1
        cases hbad
      · rcases hfiniteYZ with ⟨_, hnZ, hsignYZ, heqYZ⟩
        apply (hIsequalSpec x z).2
        exact Or.inr ⟨hnX, hnZ, hsignXY.trans hsignYZ,
          laws.equalTransitive x y z hnX hnY hnZ heqXY heqYZ⟩
  have hNaNsEqual : ∀ x y, nan x = true → nan y = true → isequal x y = true := by
    intro x y hx hy
    apply (hIsequalSpec x y).2
    exact Or.inl ⟨hx, hy⟩
  have hIsequalIffIncomparable : ∀ x y,
      isequal x y = true ↔ (isless x y = false ∧ isless y x = false) := by
    intro x y
    exact islessTotalOrderIsequalIff hOrder x y
  have hZeroSeparate : isequal negativeZero positiveZero = false := by
    cases h : isequal negativeZero positiveZero with
    | false => rfl
    | true =>
        rcases (hIsequalSpec negativeZero positiveZero).1 h with hnan | hfinite
        · have hbad : false = true :=
            laws.negativeZeroFinite.symm.trans hnan.1
          cases hbad
        · rcases hfinite with ⟨_, _, hsign, _⟩
          rw [laws.negativeZeroSign, laws.positiveZeroSign] at hsign
          cases hsign
  have hFiniteLessNaN :
      ∀ x y, nan x = false → nan y = true → isless x y = true := by
    intro x y hx hy
    simp [isless, JuliaLean.base.operators.islessFloatFloat,
      JuliaLean.base.operators.signless, hx, hy]
  have hNaNNotLessFinite :
      ∀ x y, nan x = true → nan y = false → isless x y = false := by
    intro x y hx hy
    have hlt := (laws.nanComparison x y (Or.inl hx)).1
    simp [isless, JuliaLean.base.operators.islessFloatFloat,
      JuliaLean.base.operators.signless, hx, hy, hlt]
  exact ⟨hOrder, hIsequalReflexive, hIsequalSymmetric, hIsequalTransitive,
    hNaNsEqual, hIsequalIffIncomparable, hZeroSeparate, hFiniteLessNaN,
    hNaNNotLessFinite⟩

/-- Left division solves `x * (x \ y) = y` for arbitrary operand and result types under an
involutive antiautomorphism `adjoint`, and reverses scalar division under `conj`. -/
def LeftDivisionScalarCase : Prop :=
  (∀ (α β α' β' γ δ : Type) (adjX : α → α') (adjY : β → β')
      (divide : β' → α' → γ) (adjOut : γ → δ) (adjIn : δ → γ)
      (mul : α → δ → β) (mul' : γ → α' → β') (x : α) (y : β),
    (∀ w, adjIn (adjOut w) = w) →
    (∀ u, adjY (mul x u) = mul' (adjIn u) (adjX x)) →
    mul' (divide (adjY y) (adjX x)) (adjX x) = adjY y →
    adjY (mul x (leftDiv (μ := Id) adjX adjY divide adjOut x y)) = adjY y) ∧
  (∀ (α β γ : Type) (divide : β → α → γ) (x : α) (y : β),
    leftDiv (μ := Id) id id divide id x y = divide y x) ∧
  (∀ (T : FTy) (x y : FV T),
    leftDiv (μ := Id) JuliaLean.base.number.conj JuliaLean.base.number.conj
      JuliaLean.base.float.div_IEEEFloat JuliaLean.base.number.conj x y =
        JuliaLean.base.float.div_IEEEFloat y x)

theorem leftDivisionScalarCase_proven : LeftDivisionScalarCase := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β α' β' γ δ adjX adjY divide adjOut adjIn mul mul' x y hadj hanti hdiv
    change adjY (mul x (adjOut (divide (adjY y) (adjX x)))) = adjY y
    rw [hanti, hadj, hdiv]
  · intros; rfl
  · intros; rfl

@[simp] theorem orBool_eq (a b : Bool) :
    JuliaLean.base.bool.orBool a b = (a || b) := by
  cases a <;> cases b <;> decide

@[simp] theorem result_pure {E A : Type} (a : A) :
    (pure a : Except E A) = .ok a := rfl

theorem except_ok_bind {E A B : Type} (a : A) (f : A → Except E B) :
    (Except.ok a >>= f) = f a := rfl

/-- The three comparison methods return a comparison sign across arbitrary distinct operand
types `α` and `β`, and on mixed-width `BitInteger` pairs, `BigInt` (`Int`), and arbitrary
`Integer` types `(I₁ I₂ : Type)` the sign equals the sign of the exact mathematical integer
comparison. -/
def CmpResultRange : Prop :=
  (∀ (α β : Type) (ltXY : α → β → Bool) (ltYX : β → α → Bool) (x : α) (y : β),
    (cmp ltXY ltYX x y ∈ [-1, 0, 1]) ∧
    (cmpBy ltXY ltYX x y ∈ [-1, 0, 1]) ∧
    (cmpInteger (islessReal ltXY) (islessReal ltYX) x y ∈ [-1, 0, 1]) ∧
    cmpBy ltXY ltYX x y = cmp ltXY ltYX x y ∧
    cmpInteger (islessReal ltXY) (islessReal ltYX) x y = cmp ltXY ltYX x y ∧
    (cmp ltXY ltYX x y = -1 ↔ ltXY x y = true) ∧
    (cmp ltXY ltYX x y = 1 ↔ ltXY x y = false ∧ ltYX y x = true) ∧
    (cmp ltXY ltYX x y = 0 ↔ ltXY x y = false ∧ ltYX y x = false)) ∧
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    let ltXY := islessReal (JuliaLean.base.int.lt (s := s) (t := t))
    let ltYX := islessReal (JuliaLean.base.int.lt (s := t) (t := s))
    (cmpInteger ltXY ltYX x y = -1 ↔ x.val < y.val) ∧
    (cmpInteger ltXY ltYX x y = 0 ↔ x.val = y.val) ∧
    (cmpInteger ltXY ltYX x y = 1 ↔ y.val < x.val) ∧
    cmpInteger ltYX ltXY y x = - cmpInteger ltXY ltYX x y) ∧
  (∀ (I₁ I₂ : Type) (val₁ : I₁ → Int) (val₂ : I₂ → Int)
      (ltXY : I₁ → I₂ → Bool) (ltYX : I₂ → I₁ → Bool) (x : I₁) (y : I₂),
    (∀ a b, ltXY a b = decide (val₁ a < val₂ b)) →
    (∀ b a, ltYX b a = decide (val₂ b < val₁ a)) →
    (cmpInteger (islessReal ltXY) (islessReal ltYX) x y = -1 ↔ val₁ x < val₂ y) ∧
    (cmpInteger (islessReal ltXY) (islessReal ltYX) x y = 0 ↔ val₁ x = val₂ y) ∧
    (cmpInteger (islessReal ltXY) (islessReal ltYX) x y = 1 ↔ val₂ y < val₁ x) ∧
    cmp (islessReal ltXY) (islessReal ltYX) x y =
      cmpInteger (islessReal ltXY) (islessReal ltYX) x y ∧
    cmpBy ltXY ltYX x y =
      cmpInteger (islessReal ltXY) (islessReal ltYX) x y)

theorem cmpResultRange_proven : CmpResultRange := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β ltXY ltYX x y
    cases h : ltXY x y <;> cases h' : ltYX y x <;>
      simp [cmp, cmpBy, cmpInteger, islessReal, h, h']
  · intro s t x y
    simp only [cmpInteger, islessReal, JuliaLean.Proofs.base.int.lt_eq]
    by_cases h : x.val < y.val <;> by_cases h' : y.val < x.val <;>
      simp [h, h'] <;> omega
  · intro I₁ I₂ val₁ val₂ ltXY ltYX x y hXY hYX
    simp only [cmp, cmpBy, cmpInteger, islessReal, hXY, hYX]
    by_cases h : val₁ x < val₂ y <;> by_cases h' : val₂ y < val₁ x <;>
      simp [h, h'] <;> omega

/-- Integer fallback comparisons denote value order across different widths and signedness;
the induced strict order is transitive and equality is an equivalence relation across
distinct operand types. -/
def ComparisonLaws : Prop :=
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    (lessThan (islessReal JuliaLean.base.int.lt) x y = true ↔ x.val < y.val) ∧
    (greaterThan JuliaLean.base.int.lt x y = true ↔ y.val < x.val) ∧
    (lessEqual JuliaLean.base.int.lt JuliaLean.base.int.eq JuliaLean.base.bool.orBool x y = true ↔ x.val ≤ y.val) ∧
    (greaterEqual (lessEqual JuliaLean.base.int.lt JuliaLean.base.int.eq JuliaLean.base.bool.orBool) x y = true ↔ y.val ≤ x.val) ∧
    (notEqual JuliaLean.base.int.eq JuliaLean.base.bool.notBool x y = true ↔ x.val ≠ y.val) ∧
    (isequalDefault JuliaLean.base.int.eq x y = true ↔ x.val = y.val)) ∧
  (∀ (r s t : IntTy) (x : JInt r) (y : JInt s) (z : JInt t),
    (islessReal JuliaLean.base.int.lt x y = true →
      islessReal JuliaLean.base.int.lt y z = true →
      islessReal JuliaLean.base.int.lt x z = true) ∧
    (isequalDefault JuliaLean.base.int.eq x y = isequalDefault JuliaLean.base.int.eq y x) ∧
    (isequalDefault JuliaLean.base.int.eq x y = true →
      isequalDefault JuliaLean.base.int.eq y z = true →
      isequalDefault JuliaLean.base.int.eq x z = true)) ∧
  (∀ (α β : Type) (ltXY : α → β → Bool) (ltYX : β → α → Bool) (eqXY : α → β → Bool),
    (∀ x y, eqXY x y = true ↔ ltXY x y = false ∧ ltYX y x = false) →
    (∀ x y, ltXY x y = true → ltYX y x = false) →
    ∀ x y,
    (lessEqual (lessThan ltXY) eqXY JuliaLean.base.bool.orBool x y = true ↔
      greaterThan (lessThan ltYX) x y = false) ∧
    (notEqual eqXY JuliaLean.base.bool.notBool x y = true ↔
      lessThan ltXY x y = true ∨ greaterThan (lessThan ltYX) x y = true))

theorem comparisonLaws_proven : ComparisonLaws := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t x y
    simp [lessThan, islessReal, greaterThan, lessEqual, greaterEqual, notEqual,
      isequalDefault, orBool_eq, JuliaLean.base.bool.notBool,
      JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.eq_eq]
    omega
  · intro r s t x y z
    simp [islessReal, isequalDefault, JuliaLean.Proofs.base.int.lt_eq,
      JuliaLean.Proofs.base.int.eq_eq]
    omega
  · intro α β ltXY ltYX eqXY h asymm x y
    have heq := h x y
    have hasym := asymm x y
    cases hxy : ltXY x y <;> cases hyx : ltYX y x <;> cases he : eqXY x y <;>
      simp_all [lessEqual, lessThan, greaterThan, notEqual,
        orBool_eq, JuliaLean.base.bool.notBool]

/-- Across arbitrary distinct operand types `A, B, C` sharing an abstract value space `V`,
`isequalDefault` compares abstract values, is symmetric between `A` and `B`, and is
transitive across `A → B → C`. -/
def GenericEqualityFallback : Prop :=
  ∀ (A B C V : Type) [DecidableEq V]
    (valA : A → V) (valB : B → V) (valC : C → V)
    (eqAB : A → B → Bool) (eqBA : B → A → Bool)
    (eqBC : B → C → Bool) (eqAC : A → C → Bool),
  (∀ x y, eqAB x y = decide (valA x = valB y)) →
  (∀ y x, eqBA y x = decide (valB y = valA x)) →
  (∀ y z, eqBC y z = decide (valB y = valC z)) →
  (∀ x z, eqAC x z = decide (valA x = valC z)) →
  ∀ (x : A) (y : B) (z : C),
    (isequalDefault eqAB x y = true ↔ valA x = valB y) ∧
    isequalDefault eqAB x y = isequalDefault eqBA y x ∧
    (isequalDefault eqAB x y = true → isequalDefault eqBC y z = true →
      isequalDefault eqAC x z = true)

theorem genericEqualityFallback_proven : GenericEqualityFallback := by
  intro A B C V _ valA valB valC eqAB eqBA eqBC eqAC hAB hBA hBC hAC x y z
  simp only [isequalDefault, hAB, hBA, hBC, hAC, decide_eq_true_eq]
  refine ⟨True.intro, ?_, ?_⟩
  · simp [eq_comm]
  · intro hxy hyz
    exact hxy.trans hyz

def ComparisonContract : Prop := ComparisonLaws ∧ GenericEqualityFallback

theorem comparisonContract_proven : ComparisonContract :=
  ⟨comparisonLaws_proven, genericEqualityFallback_proven⟩

/-- The `isless` contract (docstring of `isless`: exactly one of `isless(x, y)`,
`isless(y, x)` and `isequal(x, y)` holds, and `isless` is transitive) for
`isless(x::Real, y::Real) = x < y` with the fallback `isequal(x, y) = x == y`, on every triple
of `Real` types whose `<` and `==` compare exact values in a linearly ordered value domain `K`
(the documented meaning of `<` and `==` on Real numbers without special values). -/
def IslessRealGeneric : Prop :=
  ∀ (A B C K : Type) [LT K] [DecidableRel (α := K) (· < ·)] [DecidableEq K]
    (valA : A → K) (valB : B → K) (valC : C → K)
    (ltAB : A → B → Bool) (ltBA : B → A → Bool) (ltBC : B → C → Bool)
    (ltAC : A → C → Bool) (eqAB : A → B → Bool),
    (∀ a : K, ¬ a < a) → (∀ a b c : K, a < b → b < c → a < c) →
    (∀ a b : K, a < b ∨ a = b ∨ b < a) →
    (∀ x y, ltAB x y = decide (valA x < valB y)) →
    (∀ y x, ltBA y x = decide (valB y < valA x)) →
    (∀ y z, ltBC y z = decide (valB y < valC z)) →
    (∀ x z, ltAC x z = decide (valA x < valC z)) →
    (∀ x y, eqAB x y = decide (valA x = valB y)) →
    ∀ (x : A) (y : B) (z : C),
      ((islessReal ltAB x y && !islessReal ltBA y x && !isequalDefault eqAB x y) ||
        (!islessReal ltAB x y && islessReal ltBA y x && !isequalDefault eqAB x y) ||
        (!islessReal ltAB x y && !islessReal ltBA y x && isequalDefault eqAB x y)) = true ∧
      (islessReal ltAB x y = true → islessReal ltBC y z = true →
        islessReal ltAC x z = true)

theorem islessRealGeneric_proven : IslessRealGeneric := by
  intro A B C K _ _ _ valA valB valC ltAB ltBA ltBC ltAC eqAB hirr htrans htri
    hAB hBA hBC hAC hEq x y z
  simp only [islessReal, isequalDefault, hAB, hBA, hBC, hAC, hEq]
  refine ⟨?_, ?_⟩
  · rcases htri (valA x) (valB y) with h | h | h
    · have h1 : ¬ valB y < valA x := fun h' => hirr _ (htrans _ _ _ h h')
      have h2 : ¬ valA x = valB y := fun e => hirr (valB y) (e ▸ h)
      simp [h, h1, h2]
    · have h1 : decide (valA x < valB y) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h' => hirr (valB y) (h ▸ h')
      have h2 : decide (valB y < valA x) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h' => hirr (valB y) (h ▸ h')
      have h3 : decide (valA x = valB y) = true := by
        simp only [decide_eq_true_eq]; exact h
      rw [h1, h2, h3]; rfl
    · have h1 : ¬ valA x < valB y := fun h' => hirr _ (htrans _ _ _ h h')
      have h2 : ¬ valA x = valB y := fun e => hirr (valB y) (e ▸ h)
      simp [h, h1, h2]
  · intro h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    exact htrans _ _ _ h1 h2

/-- `isless(x::Real, y::Real) = x < y` meets the `isless` contract for every lawful Real type
(`IslessRealGeneric`) and, through the source `int.jl` `<` and `==`, on every fixed-width integer
width and signedness, including mixed-type triples. -/
def IslessRealContract : Prop :=
  IslessRealGeneric ∧
  ∀ (r s t : IntTy) (x : JInt r) (y : JInt s) (z : JInt t),
    ((islessReal JuliaLean.base.int.lt x y && !islessReal JuliaLean.base.int.lt y x &&
        !isequalDefault JuliaLean.base.int.eq x y) ||
      (!islessReal JuliaLean.base.int.lt x y && islessReal JuliaLean.base.int.lt y x &&
        !isequalDefault JuliaLean.base.int.eq x y) ||
      (!islessReal JuliaLean.base.int.lt x y && !islessReal JuliaLean.base.int.lt y x &&
        isequalDefault JuliaLean.base.int.eq x y)) = true ∧
    (islessReal JuliaLean.base.int.lt x y = true → islessReal JuliaLean.base.int.lt y z = true →
      islessReal JuliaLean.base.int.lt x z = true)

theorem islessRealContract_proven : IslessRealContract := by
  refine ⟨islessRealGeneric_proven, ?_⟩
  intro r s t x y z
  exact islessRealGeneric_proven (JInt r) (JInt s) (JInt t) Int (·.val) (·.val) (·.val)
    JuliaLean.base.int.lt JuliaLean.base.int.lt JuliaLean.base.int.lt JuliaLean.base.int.lt
    JuliaLean.base.int.eq Int.lt_irrefl (fun _ _ _ => Int.lt_trans) Int.lt_trichotomy
    JuliaLean.Proofs.base.int.lt_eq JuliaLean.Proofs.base.int.lt_eq
    JuliaLean.Proofs.base.int.lt_eq JuliaLean.Proofs.base.int.lt_eq
    JuliaLean.Proofs.base.int.eq_eq x y z

/-- The optimized pair comparison is a strict lexicographic order, with no assumed
laws for BitInteger comparisons, across every combination of component widths. -/
def PairIslessTransitive : Prop :=
  ∀ (r₁ r₂ s₁ s₂ t₁ t₂ : IntTy) (a : JInt r₁ × JInt r₂)
    (b : JInt s₁ × JInt s₂) (c : JInt t₁ × JInt t₂),
  (islessPair (islessReal JuliaLean.base.int.lt)
    (isequalDefault JuliaLean.base.int.eq) (islessReal JuliaLean.base.int.lt) a b = true ↔
    a.1.val < b.1.val ∨ a.1.val = b.1.val ∧ a.2.val < b.2.val) ∧
  (islessPair (islessReal JuliaLean.base.int.lt)
      (isequalDefault JuliaLean.base.int.eq) (islessReal JuliaLean.base.int.lt) a b = true →
   islessPair (islessReal JuliaLean.base.int.lt)
      (isequalDefault JuliaLean.base.int.eq) (islessReal JuliaLean.base.int.lt) b c = true →
   islessPair (islessReal JuliaLean.base.int.lt)
      (isequalDefault JuliaLean.base.int.eq) (islessReal JuliaLean.base.int.lt) a c = true)

theorem pairIslessTransitive_proven : PairIslessTransitive := by
  intro r₁ r₂ s₁ s₂ t₁ t₂ a b c
  simp [islessPair, islessReal, isequalDefault,
    JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.eq_eq]
  omega

/-- `minmax`'s values are the generic `min` and `max` results, and are ordered under Julia's
documented `isless`/`isequal` total-order contract. -/
def MinmaxCoherent : Prop :=
  ∀ (α : Type) (lt eq : α → α → Bool) (x y : α),
    IslessTotalOrder lt eq →
    let values := JuliaLean.base.operators.minmax lt x y
    let lo := Sum.elim (fun a : α => a) (fun b : α => b) values.1
    let hi := Sum.elim (fun a : α => a) (fun b : α => b) values.2
    let mn := JuliaLean.base.operators.min lt
      JuliaLean.base.operators.ifelseValue x y
    let mx := JuliaLean.base.operators.max lt
      JuliaLean.base.operators.ifelseValue x y
    lo = mn ∧ hi = mx ∧
    (lo = x ∨ lo = y) ∧ (hi = x ∨ hi = y) ∧
    (lt lo hi = true ∨ eq lo hi = true)

theorem minmaxCoherent_proven : MinmaxCoherent := by
  intro α lt eq x y order values lo hi mn mx
  cases hyx : lt y x with
  | false =>
      have hordered := islessOrEqualOfNotReverse order hyx
      simp [values, lo, hi, mn, mx, JuliaLean.base.operators.minmax,
        JuliaLean.base.operators.min, JuliaLean.base.operators.max,
        JuliaLean.base.operators.ifelseValue, hyx]
      exact hordered
  | true =>
      simp [values, lo, hi, mn, mx, JuliaLean.base.operators.minmax,
        JuliaLean.base.operators.min, JuliaLean.base.operators.max,
        JuliaLean.base.operators.ifelseValue, hyx]

/-- Reversing a total order only on ordered values preserves its comparison partition.
The unordered predicate uses its actual default, float, and Missing overloads. -/
def UnorderedOrder : Prop :=
  (∀ (α : Type) (lt : α → α → Bool) (x y : α),
    ((isgreater isunordered isunordered lt lt x y = false ∧
      isgreater isunordered isunordered lt lt y x = false) ↔
      (lt x y = false ∧ lt y x = false))) ∧
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    isgreater isunordered isunordered (islessReal JuliaLean.base.int.lt)
      (islessReal JuliaLean.base.int.lt) x y = decide (y.val < x.val)) ∧
  (∀ (T : FTy) (x : FV T),
    isunorderedFloat JuliaLean.base.float.isnan_callee x = x.isnan) ∧
  (∀ (α : Type) (x : α), isunordered x = false) ∧
  (∀ x : Unit, isunorderedMissing x = true)

theorem unorderedOrder_proven : UnorderedOrder := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α lt x y
    simp [isgreater, isunordered, And.comm]
  · intro s t x y
    simp [isgreater, isunordered, islessReal, JuliaLean.Proofs.base.int.lt_eq]
  · intro T x
    exact JuliaLean.Proofs.base.float.isnan_callee_eq x
  · intros; rfl
  · intros; rfl

/-- The mixed Float/Real descending order places NaN below an ordered value for
arbitrary numeric types. -/
def MixedUnorderedLaw : Prop := ∀ (A B : Type)
    (nanF signF : A → Bool) (nanR signR : B → Bool)
    (ltFR : A → B → Bool) (ltRF : B → A → Bool) (x : A) (y : B),
  nanF x = true → nanR y = false → ltFR x y = false →
  isgreater (isunorderedFloat nanF) isunordered
    (islessFloatReal nanF nanR signF signR ltFR)
    (islessRealFloat nanR nanF signR signF ltRF) x y = false ∧
  isgreater isunordered (isunorderedFloat nanF)
    (islessRealFloat nanR nanF signR signF ltRF)
    (islessFloatReal nanF nanR signF signR ltFR) y x = true

theorem mixedUnorderedLaw_proven : MixedUnorderedLaw := by
  intro A B nanF signF nanR signR ltFR ltRF x y hx hy hlt
  simp [isgreater, isunorderedFloat, isunordered, islessFloatReal, islessRealFloat,
    hx, hy, hlt]

def UnorderedContract : Prop := UnorderedOrder ∧ MixedUnorderedLaw

theorem unorderedContract_proven : UnorderedContract :=
  ⟨unorderedOrder_proven, mixedUnorderedLaw_proven⟩

/-- Documented type-equality contract (`base/operators.jl:313-315`, `src/subtype.c:4110-4190`):
for any type representation `α` and subtype check `subtype : α → α → Bool` (`<:`) satisfying
reflexivity and transitivity (together with sound fast-path helpers `structEquiv`,
`obviouslyUnequal`, and `obviousSubtype`), `==(T::Type, S::Type)` holds if and only if
`T <: S` and `S <: T` (`subtype t s = true ∧ subtype s t = true`), forms an equivalence
relation (reflexive, symmetric, transitive), and `==(T::TypeVar, S::Type)` and
`==(T::Type, S::TypeVar)` always return `false` (`!=` returns `true`). -/
def TypeEqualitySemantics : Prop :=
  ∀ (α β : Type) [DecidableEq α]
    (subtype structEquiv obviouslyUnequal : α → α → Bool)
    (obviousSubtype : α → α → Option Bool),
  (∀ x, subtype x x = true) →
  (∀ x y z, subtype x y = true → subtype y z = true → subtype x z = true) →
  (∀ x y, structEquiv x y = true → subtype x y = true ∧ subtype y x = true) →
  (∀ x y, obviouslyUnequal x y = true → subtype x y = false ∨ subtype y x = false) →
  (∀ x y res, obviousSubtype x y = some res → res = subtype x y) →
  let eqType := typeEqual (jlTypesEqual structEquiv obviouslyUnequal obviousSubtype subtype)
  let eqDirect := typeEqual (jlTypesEqual (fun _ _ => false) (fun _ _ => false) (fun _ _ => none) subtype)
  (∀ t s : α, eqType t s = true ↔ (subtype t s = true ∧ subtype s t = true)) ∧
  (∀ t s : α, eqDirect t s = true ↔ (subtype t s = true ∧ subtype s t = true)) ∧
  (∀ t s : α, eqType t s = eqDirect t s) ∧
  (∀ t : α, eqType t t = true) ∧
  (∀ t s : α, eqType t s = eqType s t) ∧
  (∀ t s u : α, eqType t s = true → eqType s u = true → eqType t u = true) ∧
  (∀ (v : β) (t : α),
    typeVarEqual v t = false ∧
    typeEqualVar t v = false ∧
    notEqual typeVarEqual JuliaLean.base.bool.notBool v t = true ∧
    notEqual typeEqualVar JuliaLean.base.bool.notBool t v = true)

theorem typeEqualitySemantics_proven : TypeEqualitySemantics := by
  intro α β _ subtype structEquiv obviouslyUnequal obviousSubtype
    hrefl htrans hstruct hobvUneq hobvSub eqType eqDirect
  have h10 : (JInt.lit .i32 1 != JInt.lit .i32 0) = true := by decide
  have heqType : ∀ t s : α, eqType t s = true ↔ (subtype t s = true ∧ subtype s t = true) := by
    intro t s
    dsimp [eqType, typeEqual, jlTypesEqual]
    by_cases hts : t = s
    · subst hts
      simp [h10, hrefl t]
    · simp only [hts, ↓reduceIte]
      by_cases hse : structEquiv t s = true
      · simp [hse, h10, hstruct t s hse]
      · have hseF : structEquiv t s = false := Bool.eq_false_iff.mpr hse
        simp only [hseF, Bool.false_eq_true, ↓reduceIte]
        by_cases hou : obviouslyUnequal t s = true
        · rcases hobvUneq t s hou with h1 | h2
          · simp [hou, h1]
          · simp [hou, h2]
        · have houF : obviouslyUnequal t s = false := Bool.eq_false_iff.mpr hou
          simp only [houF, Bool.false_eq_true, ↓reduceIte]
          cases hos1 : obviousSubtype t s with
          | none =>
            cases hos2 : obviousSubtype s t with
            | none =>
              cases h1 : subtype t s <;> cases h2 : subtype s t <;> simp [h10]
            | some r2 =>
              have hr2 := hobvSub s t r2 hos2
              subst hr2
              cases h1 : subtype t s <;> cases h2 : subtype s t <;> simp [h10]
          | some r1 =>
            have hr1 := hobvSub t s r1 hos1
            subst hr1
            cases hos2 : obviousSubtype s t with
            | none =>
              cases h1 : subtype t s <;> cases h2 : subtype s t <;> simp [h10]
            | some r2 =>
              have hr2 := hobvSub s t r2 hos2
              subst hr2
              cases h1 : subtype t s <;> cases h2 : subtype s t <;> simp [h10]
  have heqDirect : ∀ t s : α, eqDirect t s = true ↔ (subtype t s = true ∧ subtype s t = true) := by
    intro t s
    dsimp [eqDirect, typeEqual, jlTypesEqual]
    by_cases hts : t = s
    · subst hts
      simp [h10, hrefl t]
    · simp only [hts, ↓reduceIte]
      cases h1 : subtype t s <;> cases h2 : subtype s t <;> simp [h10]
  refine ⟨heqType, heqDirect, ?_, ?_, ?_, ?_, ?_⟩
  · intro t s
    exact Bool.eq_iff_iff.mpr ((heqType t s).trans (heqDirect t s).symm)
  · intro t
    exact (heqType t t).mpr ⟨hrefl t, hrefl t⟩
  · intro t s
    apply Bool.eq_iff_iff.mpr
    rw [heqType, heqType]
    exact And.comm
  · intro t s u hts hsu
    rcases (heqType t s).mp hts with ⟨hts1, hst1⟩
    rcases (heqType s u).mp hsu with ⟨hsu1, hus1⟩
    exact (heqType t u).mpr ⟨htrans t s u hts1 hsu1, htrans u s t hus1 hst1⟩
  · intro v t
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- On the modeled lazy-supertype `DataTypeDesc`, `jlDatatypeComputeSuper` is idempotent,
populates an unmaterialized `:super` cache from `declaredSuper`, makes `supertypeData`
and `getpropertyData ... .super` return `some d.declaredSuper` even when raw `getDataTypeField`
on `.super` is `none`, and leaves non-`:super` property reads (`s ≠ .super`) untouched. -/
def SupertypeAccessAgreement : Prop :=
  ∀ (T : Type) (d : DataTypeDesc T) (s : DataTypeSymbol),
    let superOf := supertypeData jlDatatypeComputeSuper (fun x => getDataTypeField x .super)
    let propOf := getpropertyData (· == .super) superOf getDataTypeField
    jlDatatypeComputeSuper (jlDatatypeComputeSuper d) = jlDatatypeComputeSuper d ∧
    superOf (jlDatatypeComputeSuper d) = superOf d ∧
    propOf d .super = superOf d ∧
    (d.cachedSuper = none →
      getDataTypeField d .super = none ∧
      superOf d = some d.declaredSuper ∧
      propOf d .super = some d.declaredSuper) ∧
    (s ≠ .super → propOf d s = d.otherField s)

theorem supertypeAccessAgreement_proven : SupertypeAccessAgreement := by
  intro T d s
  rcases d with ⟨declared, cached, other⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases cached <;> rfl
  · cases cached <;> rfl
  · rfl
  · intro hnone
    subst hnone
    exact ⟨rfl, rfl, rfl⟩
  · intro hs
    cases s with
    | super => contradiction
    | name => rfl
    | parameters => rfl

/-- `TypeEgal{T}` sits directly below `Type{T}` (= `TypeEq{T}`), which sits directly below
`AnyType` (the comment above `supertype(::TypeEq)`): the parent of `TypeEgal{T}` is `Type{T}`,
distinct for distinct `T`, and the parent of every `Type{T}` is Core's single abstract kind
`AnyType`, which is neither `Any` nor any `Type{S}`. -/
def SupertypeSpecialCases : Prop :=
  (∀ x y : JuliaLean.C.Val,
    supertypeTypeEgal JuliaLean.C.Val.typeeq x = supertypeTypeEgal JuliaLean.C.Val.typeeq y ↔
      x = y) ∧
  (∀ x : JuliaLean.C.Val, supertypeTypeEgal JuliaLean.C.Val.typeeq x = .typeeq x) ∧
  (∀ p q : JuliaLean.C.Val, supertypeTypeEq p = supertypeTypeEq q) ∧
  (∀ p : JuliaLean.C.Val, supertypeTypeEq p = JuliaLean.C.anytypeType ∧
    supertypeTypeEq p ≠ JuliaLean.C.anyType ∧ ∀ s, supertypeTypeEq p ≠ .typeeq s)

theorem supertypeSpecialCases_proven : SupertypeSpecialCases := by
  refine ⟨?_, fun _ => rfl, fun _ _ => rfl, ?_⟩
  · intro x y
    simp [supertypeTypeEgal]
  · intro p
    refine ⟨rfl, ?_, ?_⟩
    · simp [supertypeTypeEq, JuliaLean.C.anytypeType, JuliaLean.C.anyType]
    · intro s
      simp [supertypeTypeEq, JuliaLean.C.anytypeType]

/-- Wrap a list of `UnionAll` type-variable binders around an inner `DataType`. -/
def wrapUnionAllVars {V D : Type} (vars : List V) (d : D) : UnionAllType V D :=
  vars.foldr UnionAllType.unionAll (.data d)

/-- Extract the outer-to-inner list of `UnionAll` binders. -/
def unionAllBinders {V D : Type} : UnionAllType V D → List V
  | .data _ => []
  | .unionAll var body => var :: unionAllBinders body

/-- Extract the innermost `DataType` body inside a `UnionAll` chain. -/
def unionAllBody {V D : Type} : UnionAllType V D → D
  | .data d => d
  | .unionAll _ body => unionAllBody body

/-- Across arbitrarily nested `UnionAll` binder chains around unmaterialized `DataTypeDesc`
nodes, `supertypeUnionAll` and `supertypeUnionAllChain` (instantiated with the source-mirrored
`DataType` `supertype` components `jlDatatypeComputeSuper` and `getDataTypeField · .super` with
no assumed laws or proof-local parent helpers) agree on single-binder steps, preserve all outer
`UnionAll` binders in order, commute with splitting a binder prefix `vars₁ ++ vars₂`, and
materialize the deferred `:super` cache across successive `DataType` levels even when raw
`getDataTypeField · .super` is `none`. -/
def UnionAllSupertypePreservesVariable : Prop :=
  ∀ (V T : Type) (var : V) (vars₁ vars₂ : List V)
    (parent₂ : T) (other₂ : DataTypeSymbol → Option T)
    (other₁ : DataTypeSymbol → Option (DataTypeDesc T))
    (u : UnionAllType V (DataTypeDesc T)),
  let d₂ : DataTypeDesc T := ⟨parent₂, none, other₂⟩
  let d₁ : DataTypeDesc (DataTypeDesc T) := ⟨d₂, none, other₁⟩
  let step₁ := supertypeUnionAllChain jlDatatypeComputeSuper
    (fun x : DataTypeDesc (DataTypeDesc T) => getDataTypeField x .super)
  let step₂ := supertypeUnionAllChain jlDatatypeComputeSuper
    (fun x : DataTypeDesc T => getDataTypeField x .super)
  supertypeUnionAll UnionAllType.unionAll step₂ var u = step₂ (.unionAll var u) ∧
  unionAllBinders (step₂ u) = unionAllBinders u ∧
  step₂ (wrapUnionAllVars (vars₁ ++ vars₂) d₂) =
    vars₁.foldr UnionAllType.unionAll (step₂ (wrapUnionAllVars vars₂ d₂)) ∧
  getDataTypeField d₁ .super = none ∧
  getDataTypeField d₂ .super = none ∧
  step₁ (wrapUnionAllVars vars₁ d₁) = wrapUnionAllVars vars₁ (some d₂) ∧
  unionAllBody (step₁ (wrapUnionAllVars vars₁ d₁)) = some d₂ ∧
  step₂ (wrapUnionAllVars vars₁ d₂) = wrapUnionAllVars vars₁ (some parent₂) ∧
  unionAllBody (step₂ (wrapUnionAllVars vars₁ d₂)) = some parent₂

theorem unionAllSupertypePreservesVariable_proven : UnionAllSupertypePreservesVariable := by
  intro V T var vars₁ vars₂ parent₂ other₂ other₁ u d₂ d₁ step₁ step₂
  have hwrap : ∀ {D₁ D₂ : Type} (cs : D₁ → D₁) (gs : D₁ → D₂) (vs : List V) (x : D₁),
      supertypeUnionAllChain cs gs (wrapUnionAllVars vs x) =
        wrapUnionAllVars vs (supertypeData cs gs x) := by
    intro D₁ D₂ cs gs vs x
    induction vs with
    | nil => rfl
    | cons v vs ih =>
        change UnionAllType.unionAll v (supertypeUnionAllChain cs gs (wrapUnionAllVars vs x)) =
          UnionAllType.unionAll v (wrapUnionAllVars vs (supertypeData cs gs x))
        rw [ih]
  have hbody : ∀ {D : Type} (vs : List V) (x : D),
      unionAllBody (wrapUnionAllVars vs x) = x := by
    intro D vs x
    induction vs with
    | nil => rfl
    | cons v vs ih => exact ih
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · induction u with
    | data t => rfl
    | unionAll v b ih =>
        simp [step₂, supertypeUnionAllChain, supertypeUnionAll, unionAllBinders, ih]
  · induction vars₁ with
    | nil => rfl
    | cons v vs ih =>
        change UnionAllType.unionAll v (step₂ (wrapUnionAllVars (vs ++ vars₂) d₂)) =
          UnionAllType.unionAll v (vs.foldr UnionAllType.unionAll (step₂ (wrapUnionAllVars vars₂ d₂)))
        rw [ih]
  · exact hwrap jlDatatypeComputeSuper (fun x => getDataTypeField x .super) vars₁ d₁
  · unfold step₁
    rw [hwrap jlDatatypeComputeSuper (fun x => getDataTypeField x .super) vars₁ d₁, hbody]
    rfl
  · exact hwrap jlDatatypeComputeSuper (fun x => getDataTypeField x .super) vars₁ d₂
  · unfold step₂
    rw [hwrap jlDatatypeComputeSuper (fun x => getDataTypeField x .super) vars₁ d₂, hbody]
    rfl

/-- The fallback loop consumes its remaining heterogeneous suffix in argument order,
changing the accumulator type tag and value at each step. -/
theorem afoldlFrom_append {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (pre suffix : List (Σ s : σ, Elem s)) (y : Σ t : τ, Acc t) :
    afoldlFrom op (pre ++ suffix) (pre.length + 1) suffix.length y =
      suffix.foldl op y := by
  induction suffix generalizing pre y with
  | nil => rfl
  | cons b bs ih =>
    have hstep : afoldlAt op y (pre ++ b :: bs) (pre.length + 1) = op y b := by
      simp [afoldlAt]
    simp only [List.length_cons, afoldlFrom, hstep, List.foldl_cons]
    have h := ih (pre ++ [b]) (op y b)
    simpa [List.append_assoc, List.length_append, Nat.add_assoc] using h

/-- All 32 early-return cases and the tail loop agree with heterogeneous left folding. -/
theorem afoldlMany_eq_foldl {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : Σ t : τ, Acc t) (bs : List (Σ s : σ, Elem s)) :
    afoldlMany op a bs = bs.foldl op a := by
  cases bs with
  | nil => rfl
  | cons b1 bs =>
    cases bs with
    | nil => rfl
    | cons b2 bs =>
      cases bs with
      | nil => rfl
      | cons b3 bs =>
        cases bs with
        | nil => rfl
        | cons b4 bs =>
          cases bs with
          | nil => rfl
          | cons b5 bs =>
            cases bs with
            | nil => rfl
            | cons b6 bs =>
              cases bs with
              | nil => rfl
              | cons b7 bs =>
                cases bs with
                | nil => rfl
                | cons b8 bs =>
                  cases bs with
                  | nil => rfl
                  | cons b9 bs =>
                    cases bs with
                    | nil => rfl
                    | cons b10 bs =>
                      cases bs with
                      | nil => rfl
                      | cons b11 bs =>
                        cases bs with
                        | nil => rfl
                        | cons b12 bs =>
                          cases bs with
                          | nil => rfl
                          | cons b13 bs =>
                            cases bs with
                            | nil => rfl
                            | cons b14 bs =>
                              cases bs with
                              | nil => rfl
                              | cons b15 bs =>
                                cases bs with
                                | nil => rfl
                                | cons b16 bs =>
                                  cases bs with
                                  | nil => rfl
                                  | cons b17 bs =>
                                    cases bs with
                                    | nil => rfl
                                    | cons b18 bs =>
                                      cases bs with
                                      | nil => rfl
                                      | cons b19 bs =>
                                        cases bs with
                                        | nil => rfl
                                        | cons b20 bs =>
                                          cases bs with
                                          | nil => rfl
                                          | cons b21 bs =>
                                            cases bs with
                                            | nil => rfl
                                            | cons b22 bs =>
                                              cases bs with
                                              | nil => rfl
                                              | cons b23 bs =>
                                                cases bs with
                                                | nil => rfl
                                                | cons b24 bs =>
                                                  cases bs with
                                                  | nil => rfl
                                                  | cons b25 bs =>
                                                    cases bs with
                                                    | nil => rfl
                                                    | cons b26 bs =>
                                                      cases bs with
                                                      | nil => rfl
                                                      | cons b27 bs =>
                                                        cases bs with
                                                        | nil => rfl
                                                        | cons b28 bs =>
                                                          cases bs with
                                                          | nil => rfl
                                                          | cons b29 bs =>
                                                            cases bs with
                                                            | nil => rfl
                                                            | cons b30 bs =>
                                                              cases bs with
                                                              | nil => rfl
                                                              | cons b31 bs =>
                                                                cases bs with
                                                                | nil => rfl
                                                                | cons b32 bs =>
                                                                  exact afoldlFrom_append op [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] (b32 :: bs) (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op a b1) b2) b3) b4) b5) b6) b7) b8) b9) b10) b11) b12) b13) b14) b15) b16) b17) b18) b19) b20) b21) b22) b23) b24) b25) b26) b27) b28) b29) b30) b31)

/-- Splitting a heterogeneous argument list never changes left-to-right evaluation,
including beyond the 31-element unrolled prefix and when both element types and
accumulator types change at every step. -/
def NaryFoldLaw : Prop :=
  (∀ (τ σ φ : Type) (Acc : τ → Type) (Elem : σ → Type) (unusedOp : φ)
      (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
      (a : Σ t : τ, Acc t) (xs ys : List (Σ s : σ, Elem s)),
    afoldlMany op a (xs ++ ys) = afoldlMany op (afoldlMany op a xs) ys ∧
    afoldlMany op a xs = xs.foldl op a ∧
    afoldlOne unusedOp a = afoldlMany op a []) ∧
  (∀ (τ σ α β γ δ : Type) (Acc : τ → Type) (Elem : σ → Type)
      (opAB : α → β → δ) (opABC : δ → γ → Σ t₀ : τ, Acc t₀)
      (opRest : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
      (a : α) (b : β) (c : γ) (xs ys : List (Σ s : σ, Elem s)),
    naryOperator opAB opABC opRest a b c (xs ++ ys) =
      afoldlMany opRest (naryOperator opAB opABC opRest a b c xs) ys)

theorem naryFoldLaw_proven : NaryFoldLaw := by
  constructor
  · intro τ σ φ Acc Elem unusedOp op a xs ys
    simp [afoldlMany_eq_foldl, List.foldl_append, afoldlOne]
  · intro τ σ α β γ δ Acc Elem opAB opABC opRest a b c xs ys
    simp [naryOperator, afoldlMany_eq_foldl, List.foldl_append]

/-- Generated n-ary `min` and `max` folds use the heterogeneous source `min` and `max`
methods across changing accumulator and element types. -/
def NaryMinmaxFold : Prop :=
  ∀ (τ : Type) (Val : τ → Type)
    (lt : {t s : τ} → Val s → Val t → Bool)
    (chooseMin : {t s : τ} → Bool → Val s → Val t → Σ r : τ, Val r)
    (chooseMax : {t s : τ} → Bool → Val t → Val s → Σ r : τ, Val r)
    (t₁ t₂ t₃ : τ) (a : Val t₁) (b : Val t₂) (c : Val t₃)
    (xs ys : List (Σ s : τ, Val s)),
  let minPair : (Σ t : τ, Val t) → (Σ s : τ, Val s) → Σ r : τ, Val r :=
    fun x y => JuliaLean.base.operators.min lt chooseMin x.2 y.2
  let maxPair : (Σ t : τ, Val t) → (Σ s : τ, Val s) → Σ r : τ, Val r :=
    fun x y => JuliaLean.base.operators.max lt chooseMax x.2 y.2
  naryOperator (fun x y => minPair ⟨t₁, x⟩ ⟨t₂, y⟩) (fun ab z => minPair ab ⟨t₃, z⟩)
      minPair a b c (xs ++ ys) =
    afoldlMany minPair
      (naryOperator (fun x y => minPair ⟨t₁, x⟩ ⟨t₂, y⟩) (fun ab z => minPair ab ⟨t₃, z⟩)
        minPair a b c xs) ys ∧
  naryOperator (fun x y => maxPair ⟨t₁, x⟩ ⟨t₂, y⟩) (fun ab z => maxPair ab ⟨t₃, z⟩)
      maxPair a b c (xs ++ ys) =
    afoldlMany maxPair
      (naryOperator (fun x y => maxPair ⟨t₁, x⟩ ⟨t₂, y⟩) (fun ab z => maxPair ab ⟨t₃, z⟩)
        maxPair a b c xs) ys

theorem naryMinmaxFold_proven : NaryMinmaxFold := by
  intro τ Val lt chooseMin chooseMax t₁ t₂ t₃ a b c xs ys minPair maxPair
  simp [naryOperator, afoldlMany_eq_foldl, List.foldl_append]

def NaryOperatorsContract : Prop := NaryFoldLaw ∧ NaryMinmaxFold

theorem naryOperatorsContract_proven : NaryOperatorsContract :=
  ⟨naryFoldLaw_proven, naryMinmaxFold_proven⟩

/-- Repeating `identity` across arbitrarily long folds (past the 31-element unrolling
threshold) leaves the value unchanged, and pipelines that change types at every step
obey left-to-right composition and pipeline splitting laws. -/
def IdentityPipeLaws : Prop :=
  (∀ (α : Type) (x : α) (n : Nat),
    let step : (Σ _ : Unit, α) → (Σ _ : Unit, α → α) → Σ _ : Unit, α :=
      fun acc f => ⟨(), pipe acc.2 f.2⟩
    (afoldlMany (Acc := fun _ : Unit => α) (Elem := fun _ : Unit => α → α)
      step ⟨(), x⟩
      (List.replicate n ⟨(), (JuliaLean.base.operators.identity : α → α)⟩)).2 = x) ∧
  (∀ (α β γ δ : Type) (x : α) (f : α → β) (g : β → γ) (h : γ → δ),
    pipe (pipe (pipe x f) g) h = h (g (f x)) ∧
    pipe (pipe x (JuliaLean.base.operators.identity : α → α)) f = pipe x f ∧
    pipe (pipe x f) (JuliaLean.base.operators.identity : β → β) = pipe x f) ∧
  (∀ (τ σ : Type) (Stage : τ → Type) (StepFn : σ → Type)
      (applyStep : {t : τ} → {s : σ} → Stage t → StepFn s → Σ t' : τ, Stage t')
      (x : Σ t : τ, Stage t) (fs gs : List (Σ s : σ, StepFn s)),
    let pipeStep : (Σ t : τ, Stage t) → (Σ s : σ, StepFn s) → Σ t' : τ, Stage t' :=
      fun v fn => pipe v.2 (fun val => applyStep val fn.2)
    afoldlMany pipeStep x (fs ++ gs) =
      afoldlMany pipeStep (afoldlMany pipeStep x fs) gs)

theorem identityPipeLaws_proven : IdentityPipeLaws := by
  refine ⟨?_, ?_, ?_⟩
  · intro α x n step
    rw [afoldlMany_eq_foldl]
    induction n with
    | zero => rfl
    | succ n ih =>
        simpa [List.replicate_succ, step, pipe, JuliaLean.base.operators.identity] using ih
  · intros; exact ⟨rfl, rfl, rfl⟩
  · intro τ σ Stage StepFn applyStep x fs gs pipeStep
    simp [afoldlMany_eq_foldl, List.foldl_append]

/-! ## Composition: `ComposedFunction`, `unwrap_composed`, `call_composed`, `∘`, `Returns`, `!` -/

/-- The source `call_composed` on a nonempty tuple calls the last callable with every positional
and keyword argument, then each preceding callable from right to left on the previous result. -/
theorem callComposedAny_snoc {F T V σ : Type} (m : CallMethods F T V σ)
    (pre : List (PlainCallable F T)) (last : PlainCallable F T) (x : List V) (kw : List (σ × V)) :
    callComposedAny m (pre ++ [last]) x kw =
      (do let v ← callComposedOne m last x kw
          pre.foldrM (fun f v => callPlain m f [v] []) v) := by
  induction pre with
  | nil => simp [callComposedAny, -result_pure]
  | cons f fs ih =>
      cases fs with
      | nil =>
          simp [callComposedAny, callComposed, -result_pure]
      | cons g gs =>
          have h : callComposedAny m (f :: g :: (gs ++ [last])) x kw =
              (do let v ← callComposedAny m (g :: (gs ++ [last])) x kw
                  callPlain m f [v] []) := by
            rw [callComposedAny.eq_def]
            simp only
            rw [callComposed.eq_def]
          simp only [List.cons_append] at ih ⊢
          rw [h, ih]
          simp [List.foldrM_cons]

/-- The source `unwrap_composed` returns a nonempty tuple for every callable. -/
theorem unwrapComposedAny_snoc {F T : Type} : (c : Callee F T) →
    ∃ pre last, unwrapComposedAny c = pre ++ [last]
  | .plain p => ⟨[], maybeconstructor p, by simp [unwrapComposedAny, unwrapCallable]⟩
  | .composed ⟨o, i⟩ => by
      obtain ⟨pre, last, h⟩ := unwrapComposedAny_snoc i
      exact ⟨unwrapComposedAny o ++ pre, last, by
        simp [unwrapComposedAny, unwrapComposed, h]⟩

theorem unwrapComposedAny_ne_nil {F T : Type} (c : Callee F T) : unwrapComposedAny c ≠ [] := by
  obtain ⟨pre, last, h⟩ := unwrapComposedAny_snoc c
  simp [h]

/-- `maybeconstructor` never leaves a type object in a flattened composition. -/
theorem unwrapComposedAny_no_type {F T : Type} : (c : Callee F T) →
    ∀ p ∈ unwrapComposedAny c, ∀ t : T, p ≠ .type t
  | .plain p, q, hq, t => by
      simp only [unwrapComposedAny, unwrapCallable, List.mem_singleton] at hq
      subst hq
      cases p <;> simp [maybeconstructor, maybeConstructorValue, maybeConstructorType]
  | .composed ⟨o, i⟩, q, hq, t => by
      simp only [unwrapComposedAny, unwrapComposed, List.mem_append] at hq
      rcases hq with hq | hq
      · exact unwrapComposedAny_no_type o q hq t
      · exact unwrapComposedAny_no_type i q hq t

/-- Calling the `Constructor` that `maybeconstructor` makes for a type calls the type. -/
theorem callPlain_maybeconstructor {F T V σ : Type} (m : CallMethods F T V σ)
    (p : PlainCallable F T) (x : List V) (kw : List (σ × V)) :
    callPlain m (maybeconstructor p) x kw = callPlain m p x kw := by
  cases p <;> rfl

/-- Calling any callable equals running the source `call_composed` on its flattening. -/
theorem callCallee_eq_unwrap {F T V σ : Type} (m : CallMethods F T V σ) :
    (c : Callee F T) → (x : List V) → (kw : List (σ × V)) →
    callCallee m c x kw = callComposedAny m (unwrapComposedAny c) x kw
  | .plain p, x, kw => by
      simp [callCallee, unwrapComposedAny, unwrapCallable, callComposedAny, callComposedOne,
        callPlain_maybeconstructor]
  | .composed _, _, _ => rfl

theorem callComposedAny_value {F T V σ : Type} (m : CallMethods F T V σ)
    (fs : List (PlainCallable F T)) (hfs : fs ≠ []) (v : V) :
    callComposedAny m fs [v] ([] : List (σ × V)) =
      fs.foldrM (fun f v => callPlain m f [v] []) v := by
  obtain ⟨pre, last, rfl⟩ : ∃ pre last, fs = pre ++ [last] :=
    ⟨fs.dropLast, fs.getLast hfs, (List.dropLast_concat_getLast hfs).symm⟩
  rw [callComposedAny_snoc]
  simp [List.foldrM_append, callComposedOne, except_ok_bind]

theorem callCallee_value {F T V σ : Type} (m : CallMethods F T V σ) (c : Callee F T) (v : V) :
    callCallee m c [v] ([] : List (σ × V)) =
      (unwrapComposedAny c).foldrM (fun f v => callPlain m f [v] []) v := by
  rw [callCallee_eq_unwrap, callComposedAny_value m _ (unwrapComposedAny_ne_nil c)]

/-- Calling `composeTwo f g` is `f(g(x...; kw...))` for arbitrary callables. -/
theorem callCallee_composeTwo {F T V σ : Type} (m : CallMethods F T V σ) (f g : Callee F T)
    (x : List V) (kw : List (σ × V)) :
    callCallee m (.composed (composeTwo f g)) x kw =
      (do let v ← callCallee m g x kw; callCallee m f [v] []) := by
  obtain ⟨pre, last, hg⟩ := unwrapComposedAny_snoc g
  have h1 : callCallee m (.composed (composeTwo f g)) x kw =
      callComposedAny m ((unwrapComposedAny f ++ pre) ++ [last]) x kw := by
    simp [callCallee, composedCall, unwrapComposed, composeTwo, composed, hg]
  rw [h1, callComposedAny_snoc, callCallee_eq_unwrap m g, hg, callComposedAny_snoc]
  simp only [List.foldrM_append, bind_assoc, callCallee_value]

theorem flatMap_foldrM {F T V σ : Type} (m : CallMethods F T V σ) (L : List (Callee F T))
    (v : V) :
    (L.flatMap unwrapComposedAny).foldrM (fun f v => callPlain m f [v] ([] : List (σ × V))) v =
      L.foldrM (fun f v => callCallee m f [v] []) v := by
  induction L generalizing v with
  | nil => simp
  | cons f L ih =>
      simp only [List.flatMap_cons, List.foldrM_append, List.foldrM_cons, ih, callCallee_value]

/-- The source `∘` on `acc` and a nonempty tail builds a `ComposedFunction` whose flattening is
the concatenation of the flattenings of its arguments. -/
theorem composeAny_chain {F T : Type} : (rest : List (Callee F T)) → (acc : Callee F T) →
    rest ≠ [] → ∃ c, composeAny (acc :: rest) = .ok (.composed c) ∧
      unwrapComposed c = unwrapComposedAny acc ++ rest.flatMap unwrapComposedAny
  | [], _, h => absurd rfl h
  | [h], acc, _ => ⟨composeTwo acc h, by simp [composeAny],
      by simp [unwrapComposed, composeTwo, composed]⟩
  | h :: h2 :: hs, acc, _ => by
      obtain ⟨c, hc, hu⟩ :=
        composeAny_chain (h2 :: hs) (.composed (composeTwo acc h)) (by simp)
      refine ⟨c, ?_, ?_⟩
      · rw [composeAny.eq_def]
        simp only
        rw [composeMany.eq_def]
        exact hc
      · rw [hu]
        simp [unwrapComposedAny, unwrapComposed, composeTwo, composed, List.append_assoc]

/-- `(f ∘ g)(args...; kw...)` is `f(g(args...; kw...))` (`∘` and `ComposedFunction`
docstrings) for all callables `f` and `g`: callable objects, type objects (called through the
`Constructor` that `maybeconstructor` makes), and nested compositions. `g` receives every
positional and keyword argument, `f` only `g`'s result and no keywords, and an error of `g`
propagates before `f` runs. `ComposedFunction{O,I}(outer, inner)` converts arbitrary arguments
to the declared field types `O` and `I` in outer-then-inner order (propagating outer conversion
errors before inner conversion and inner conversion errors before construction), behaves as
`ComposedFunction(o, i)` when both conversions succeed, and `f ∘ g === ComposedFunction(f, g)`. -/
def CompositionApplication : Prop :=
  ∀ (F T V σ O I α β : Type) (m : CallMethods F T V σ) (f g : Callee F T)
    (convertO : α → Jl O) (convertI : β → Jl I)
    (convertOuter : α → Jl (Callee F T)) (convertInner : β → Jl (Callee F T))
    (rawOuter : α) (rawInner : β)
    (x : List V) (kw : List (σ × V)),
    callCallee m (.composed (composeTwo f g)) x kw =
      (do let v ← callCallee m g x kw; callCallee m f [v] []) ∧
    composeTwo f g = composed f g ∧
    (composed f g).outer = f ∧ (composed f g).inner = g ∧
    composedTyped pure pure f g = .ok (composed f g) ∧
    ((∃ c, composedTyped convertO convertI rawOuter rawInner = .ok c) ↔
      (∃ o, convertO rawOuter = .ok o) ∧ (∃ i, convertI rawInner = .ok i)) ∧
    (∀ (o : O) (i : I),
      convertO rawOuter = .ok o → convertI rawInner = .ok i →
      composedTyped convertO convertI rawOuter rawInner = .ok ⟨o, i⟩ ∧
      (composed o i).outer = o ∧ (composed o i).inner = i) ∧
    (∀ e : JlError,
      convertO rawOuter = .error e →
      composedTyped convertO convertI rawOuter rawInner = .error e) ∧
    (∀ (o : O) (e : JlError),
      convertO rawOuter = .ok o → convertI rawInner = .error e →
      composedTyped convertO convertI rawOuter rawInner = .error e) ∧
    (do
      let c ← composedTyped convertOuter convertInner rawOuter rawInner
      callCallee m (.composed c) x kw) =
      (do
        let f' ← convertOuter rawOuter
        let g' ← convertInner rawInner
        let v ← callCallee m g' x kw
        callCallee m f' [v] []) ∧
    (∀ t : T, callCallee m (.composed (composeTwo (.plain (.type t)) g)) x kw =
      (do let v ← callCallee m g x kw; m.callType t [v] []))

theorem compositionApplication_proven : CompositionApplication := by
  intro F T V σ O I α β m f g convertO convertI convertOuter convertInner rawOuter rawInner x kw
  refine ⟨callCallee_composeTwo m f g x kw, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases ho : convertO rawOuter <;> cases hi : convertI rawInner <;>
      simp [composedTyped, ho, hi, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro o i ho hi
    exact ⟨by simp [composedTyped, ho, hi, Bind.bind, Except.bind, Pure.pure, Except.pure], rfl, rfl⟩
  · intro e ho
    simp [composedTyped, ho, Bind.bind, Except.bind]
  · intro o e ho hi
    simp [composedTyped, ho, hi, Bind.bind, Except.bind]
  · cases ho : convertOuter rawOuter with
    | error e =>
        simp [composedTyped, ho, Bind.bind, Except.bind]
    | ok f' =>
        cases hi : convertInner rawInner with
        | error e =>
            simp [composedTyped, ho, hi, Bind.bind, Except.bind]
        | ok g' =>
            simpa [composedTyped, composeTwo, composed, ho, hi,
              Bind.bind, Except.bind, Pure.pure, Except.pure] using
              callCallee_composeTwo m f' g' x kw
  · intro t
    rw [callCallee_composeTwo]
    rfl
/-- Calling a `ComposedFunction` (`(c::ComposedFunction)(x...; kw...)`) is the right fold of
`call_composed` over its flattened callables: the innermost callable
(`call_composed(fs::Tuple{Any}, x, kw)`) receives every positional and keyword argument, each
outer callable (`call_composed(fs, x, kw)`) the previous result as its only argument and no
keywords, and for every nesting this equals `c.outer(c.inner(x...; kw...))`. -/
def ComposedCallFold : Prop :=
  ∀ (F T V σ : Type) (m : CallMethods F T V σ),
    (∀ (pre : List (PlainCallable F T)) (last : PlainCallable F T)
        (x : List V) (kw : List (σ × V)),
      callComposedAny m (pre ++ [last]) x kw =
        (do let v ← callComposedOne m last x kw
            pre.foldrM (fun f v => callPlain m f [v] []) v)) ∧
    (∀ (f : PlainCallable F T) (pre : List (PlainCallable F T)) (last : PlainCallable F T)
        (x : List V) (kw : List (σ × V)),
      callComposed m (f :: pre ++ [last]) x kw =
        (do let v ← callPlain m last x kw
            (f :: pre).foldrM (fun f v => callPlain m f [v] []) v)) ∧
    (∀ (c : ComposedFunction (Callee F T) (Callee F T)) (x : List V) (kw : List (σ × V)),
      composedCall m c x kw =
        (do let v ← callCallee m c.inner x kw; callCallee m c.outer [v] []))

theorem composedCallFold_proven : ComposedCallFold := by
  intro F T V σ m
  refine ⟨callComposedAny_snoc m, ?_, ?_⟩
  · intro f pre last x kw
    have h : callComposed m (f :: (pre ++ [last])) x kw =
        (do let v ← callComposedAny m (pre ++ [last]) x kw; callPlain m f [v] []) := by
      rw [callComposed.eq_def]
    rw [List.cons_append, h, callComposedAny_snoc]
    simp [List.foldrM_cons, callComposedOne, -result_pure]
  · intro c x kw
    exact callCallee_composeTwo m c.outer c.inner x kw

/-- `unwrap_composed` flattens a composition into its callables in outer-to-inner order with
every type object replaced by its `Constructor`: `(f ∘ g) ∘ h` and `f ∘ (g ∘ h)` flatten
identically, a flattening is never empty and never contains a type object, and a callable
object is kept unchanged. -/
def CompositionUnwrapOrder : Prop :=
  ∀ (F T : Type) (f g h : Callee F T) (fn : F) (t : T),
    unwrapComposed (composeTwo (.composed (composeTwo f g)) h) =
      unwrapComposed (composeTwo f (.composed (composeTwo g h))) ∧
    unwrapComposed (composeTwo f g) ≠ [] ∧
    (∀ p ∈ unwrapComposed (composeTwo f g), ∀ t' : T, p ≠ .type t') ∧
    unwrapComposed (composeTwo (.plain (.fn fn) : Callee F T) (.plain (.type t))) =
      [.fn fn, .ctor ⟨t⟩]

theorem compositionUnwrapOrder_proven : CompositionUnwrapOrder := by
  intro F T f g h fn t
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [unwrapComposed, unwrapComposedAny, composeTwo, composed, List.append_assoc]
  · exact unwrapComposedAny_ne_nil (.composed (composeTwo f g))
  · exact unwrapComposedAny_no_type (.composed (composeTwo f g))
  · rfl

/-- `∘(f)` is `f`, and `∘(f₁, …, fₙ)` for `n ≥ 2` is a `ComposedFunction` that flattens to the
concatenation of the flattenings of `f₁, …, fₙ` in argument order; calling it runs `fₙ` first
with every argument and then `fₙ₋₁, …, f₁` on the previous result ("the last argument to `∘`
executes first"). -/
def NaryComposition : Prop :=
  ∀ (F T V σ : Type) (m : CallMethods F T V σ),
    (∀ f : Callee F T, composeAny [f] = .ok f) ∧
    (∀ (pre : List (Callee F T)) (last : Callee F T) (x : List V) (kw : List (σ × V)),
      pre ≠ [] → ∃ c, composeAny (pre ++ [last]) = .ok (.composed c) ∧
        unwrapComposed c = (pre ++ [last]).flatMap unwrapComposedAny ∧
        composedCall m c x kw =
          (do let v ← callCallee m last x kw
              pre.foldrM (fun f v => callCallee m f [v] []) v))

theorem naryComposition_proven : NaryComposition := by
  intro F T V σ m
  refine ⟨fun f => by simp [composeAny, composeOne], ?_⟩
  intro pre last x kw hpre
  obtain ⟨acc, rest, rfl⟩ : ∃ acc rest, pre = acc :: rest := by
    cases pre with
    | nil => exact absurd rfl hpre
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨c, hc, hu⟩ := composeAny_chain (rest ++ [last]) acc (by simp)
  refine ⟨c, by simpa using hc, by simpa [List.flatMap_cons] using hu, ?_⟩
  obtain ⟨p', l', hl⟩ := unwrapComposedAny_snoc last
  change callComposedAny m (unwrapComposed c) x kw = _
  rw [hu]
  have hsplit : unwrapComposedAny acc ++ (rest ++ [last]).flatMap unwrapComposedAny =
      (((acc :: rest).flatMap unwrapComposedAny) ++ p') ++ [l'] := by
    simp [List.flatMap_append, hl, List.append_assoc]
  rw [hsplit, callComposedAny_snoc, callCallee_eq_unwrap m last, hl, callComposedAny_snoc]
  simp only [List.foldrM_append, bind_assoc, flatMap_foldrM]

/-- `Returns(x)` returns `x` for every positional and keyword argument list (`Returns`
docstring), its `value` field is `x`, and `Returns(x)` stores `_stable_typeof(x)` as its type
parameter; `Returns{V}(raw)` converts arbitrary constructor arguments to field type `V`,
storing the converted value and returning it on every call when conversion succeeds and
propagating the conversion error when it fails (including concrete `JInt.convert` across
fixed-width integer types); equal results identify the stored value, and composing `Returns`
with any callable `g` (including types and nested compositions) returns the stored value once
`g` succeeds and propagates `g`'s error. -/
def ReturnsCallContract : Prop :=
  (∀ (τ V α σ T : Type) (callType : T → List V → List (σ × V) → Jl V)
      (convert : τ → α → Jl V) (tag : τ) (raw : α)
      (typeOf : V → τ) (x y : V) (args : List V) (kw : List (σ × V))
      (g : Callee (Returns τ V) T),
    let m : CallMethods (Returns τ V) T V σ := ⟨returnsCall, callType⟩
    ((∃ r, returnsTyped convert tag raw = .ok r) ↔ ∃ v, convert tag raw = .ok v) ∧
    (∀ v : V, convert tag raw = .ok v →
      returnsTyped convert tag raw = .ok ⟨tag, v⟩ ∧
      returnsCall ⟨tag, v⟩ args kw = .ok v ∧
      callCallee m (.composed (composeTwo (.plain (.fn ⟨tag, v⟩)) g)) args kw =
        (do let _ ← callCallee m g args kw; pure v)) ∧
    (∀ e : JlError, convert tag raw = .error e →
      returnsTyped convert tag raw = .error e) ∧
    (do let r ← returnsTyped convert tag raw; returnsCall r args kw) = convert tag raw ∧
    returnsTyped (fun _ v => pure v) tag x = .ok ⟨tag, x⟩ ∧
    returnsCall (returnsStable (stableTypeof typeOf) x) args kw = .ok x ∧
    (returnsStable (stableTypeof typeOf) x).value = x ∧
    (returnsStable (stableTypeof typeOf) x).typeParam = typeOf x ∧
    (returnsCall (returnsStable (stableTypeof typeOf) x) args kw =
      returnsCall (returnsStable (stableTypeof typeOf) y) args kw ↔ x = y) ∧
    callCallee m (.composed (composeTwo (.plain (.fn (returnsStable (stableTypeof typeOf) x))) g)) args kw =
      (do let _ ← callCallee m g args kw; pure x)) ∧
  (∀ (t s : IntTy) (x : JInt s) (args : List (JInt t)) (kw : List (String × JInt t)),
    let conv : IntTy → JInt s → Jl (JInt t) := fun _ a => JInt.convert (t.name) t a.val
    (∀ h : t.min ≤ x.val ∧ x.val ≤ t.max,
      returnsTyped conv t x = .ok ⟨t, ⟨x.val, h⟩⟩ ∧
      (do let r ← returnsTyped conv t x; returnsCall r args kw) = .ok ⟨x.val, h⟩) ∧
    (¬ (t.min ≤ x.val ∧ x.val ≤ t.max) →
      returnsTyped conv t x = .error (.inexactError t.name)))

theorem returnsCallContract_proven : ReturnsCallContract := by
  constructor
  · intro τ V α σ T callType convert tag raw typeOf x y args kw g m
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · cases hc : convert tag raw <;>
        simp [returnsTyped, hc, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro v hc
      refine ⟨by simp [returnsTyped, hc, Bind.bind, Except.bind, Pure.pure, Except.pure], rfl, ?_⟩
      rw [callCallee_composeTwo]
      rfl
    · intro e hc
      simp [returnsTyped, hc, Bind.bind, Except.bind]
    · cases hc : convert tag raw <;>
        simp [returnsTyped, returnsCall, hc, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · constructor
      · intro h
        simpa [returnsCall, returnsStable] using h
      · intro h; subst h; rfl
    · rw [callCallee_composeTwo]
      rfl
  · intro t s x args kw conv
    refine ⟨?_, ?_⟩
    · intro h
      simp [returnsTyped, returnsCall, conv, JInt.convert, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro h
      simp [returnsTyped, conv, JInt.convert, h, Bind.bind, Except.bind]

/-- `!f` (`(!) ∘ f`) computes the boolean negation of the predicate `f` (`!f::Function`
docstring): for every callable predicate `p` and a `!` whose Bool method is `notBool`
(`base/bool.jl`), calling `!p` returns the negation of `p`'s Bool result and propagates `p`'s
errors, and `!(!p)` (the `ComposedFunction{typeof(!)}` method) is `p` itself, so calling it
returns `p`'s results. -/
def NegationComposition : Prop :=
  ∀ (F T V σ : Type) (m : CallMethods F T V σ) (notF : F) (ofBool : Bool → V)
    (p : Callee F T) (x : List V) (kw : List (σ × V)),
    (∀ c, m.callFn notF [ofBool c] [] = .ok (ofBool (JuliaLean.base.bool.notBool c))) →
    let negated := negateFunction (.plain (.fn notF) : Callee F T) p
    (∀ b, callCallee m p x kw = .ok (ofBool b) →
      callCallee m (.composed negated) x kw = .ok (ofBool (!b))) ∧
    (∀ e, callCallee m p x kw = .error e → callCallee m (.composed negated) x kw = .error e) ∧
    doubleNegatedComposition negated = p ∧
    callCallee m (doubleNegatedComposition negated) x kw = callCallee m p x kw

theorem negationComposition_proven : NegationComposition := by
  intro F T V σ m notF ofBool p x kw hnot negated
  have hcall : callCallee m (.composed negated) x kw =
      (do let v ← callCallee m p x kw; callCallee m (.plain (.fn notF)) [v] []) :=
    callCallee_composeTwo m _ p x kw
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro b hb
    rw [hcall, hb]
    cases b
    · simpa [callCallee, callPlain, JuliaLean.base.bool.notBool, except_ok_bind] using hnot false
    · simpa [callCallee, callPlain, JuliaLean.base.bool.notBool, except_ok_bind] using hnot true
  · intro e he
    rw [hcall, he]
    rfl

/-- The `IO`-writing composition, `Fix{N}`, and `Splat` display methods (`show@1140`,
`show@1147`, `_showcomposed@1152/1154/1156/1158`, `Base.show@1226`, `show@1387`) write
through an arbitrary `IO` stream in source order, parenthesizing operator callables and
right-associated nested compositions while omitting outer parentheses on left-associated
and negated compositions, and reproduce the documented `sin ∘ cos`, `splat(+)`, and
`Fix{2}(+, 1)` renderings. -/
def DisplayContract : Prop :=
  (∀ (IO α β γ F T : Type) (contents : IO → String)
      (print : IO → String → Jl IO) (printChar : IO → Char → Jl IO)
      (showA : IO → α → Jl IO) (showB : IO → β → Jl IO) (showC : IO → γ → Jl IO)
      (showConstr : IO → Nat → Jl IO) (showF : IO → F → Jl IO) (showX : IO → T → Jl IO)
      (reprA : α → String) (reprB : β → String) (reprC : γ → String)
      (reprF : F → String) (reprX : T → String)
      (symbolA : α → String) (symbolB : β → String) (symbolC : γ → String)
      (isOp : String → Bool)
      (io : IO) (a : α) (b : β) (c : γ) (n : Nat) (f : F) (x : T),
    (∀ s str, ∃ s', print s str = .ok s' ∧ contents s' = contents s ++ str) →
    (∀ s ch, ∃ s', printChar s ch = .ok s' ∧ contents s' = contents s ++ String.singleton ch) →
    (∀ s u, ∃ s', showA s u = .ok s' ∧ contents s' = contents s ++ reprA u) →
    (∀ s v, ∃ s', showB s v = .ok s' ∧ contents s' = contents s ++ reprB v) →
    (∀ s w, ∃ s', showC s w = .ok s' ∧ contents s' = contents s ++ reprC w) →
    (∀ s k, ∃ s', showConstr s k = .ok s' ∧ contents s' = contents s ++ ("Fix{" ++ toString k ++ "}")) →
    (∀ s fn, ∃ s', showF s fn = .ok s' ∧ contents s' = contents s ++ reprF fn) →
    (∀ s vx, ∃ s', showX s vx = .ok s' ∧ contents s' = contents s ++ reprX vx) →
    let fmtOp (isO : Bool) (r : String) : String := if isO then "(" ++ r ++ ")" else r
    let showPartA := showComposedFunction symbolA isOp printChar showA
    let showPartB := showComposedFunction symbolB isOp printChar showB
    let showPartC := showComposedFunction symbolC isOp printChar showC
    let showCompAB := showComposed (fun _ : α => false) (showComposedDefault showA)
      showPartA print showPartB
    let showCompBC := showComposed (fun _ : β => false) (showComposedDefault showB)
      showPartB print showPartC
    (∃ io', showComposedDefault showA io a = .ok io' ∧
      contents io' = contents io ++ reprA a) ∧
    (∃ io', showPartA io a = .ok io' ∧
      contents io' = contents io ++ fmtOp (isOp (symbolA a)) (reprA a)) ∧
    (∃ io', showCompAB io (composeTwo a b) = .ok io' ∧
      contents io' = contents io ++ fmtOp (isOp (symbolA a)) (reprA a) ++ " ∘ " ++
        fmtOp (isOp (symbolB b)) (reprB b)) ∧
    (∃ io', showComposed (fun _ : ComposedFunction α β => true) showCompAB showCompAB
      print showPartC io (composeTwo (composeTwo a b) c) = .ok io' ∧
      contents io' = contents io ++ fmtOp (isOp (symbolA a)) (reprA a) ++ " ∘ " ++
        fmtOp (isOp (symbolB b)) (reprB b) ++ " ∘ " ++ fmtOp (isOp (symbolC c)) (reprC c)) ∧
    (∃ io', showNestedComposed printChar showCompBC io (composeTwo b c) = .ok io' ∧
      contents io' = contents io ++ "(" ++ fmtOp (isOp (symbolB b)) (reprB b) ++ " ∘ " ++
        fmtOp (isOp (symbolC c)) (reprC c) ++ ")") ∧
    (∃ io', showComposed (fun _ : α => false) (showComposedDefault showA) showPartA print
      (showNestedComposed printChar showCompBC) io
      (composeTwo a (composeTwo b c)) = .ok io' ∧
      contents io' = contents io ++ fmtOp (isOp (symbolA a)) (reprA a) ++ " ∘ (" ++
        fmtOp (isOp (symbolB b)) (reprB b) ++ " ∘ " ++ fmtOp (isOp (symbolC c)) (reprC c) ++ ")") ∧
    (∃ io', showNegatedComposed printChar showPartB io (negateFunction "!" b) = .ok io' ∧
      contents io' = contents io ++ "!" ++ fmtOp (isOp (symbolB b)) (reprB b)) ∧
    (∃ io', showNestedNegatedComposed (showNegatedComposed printChar showPartB) io
      (negateFunction "!" b) = .ok io' ∧
      contents io' = contents io ++ "!" ++ fmtOp (isOp (symbolB b)) (reprB b)) ∧
    (∃ io', showFix showConstr printChar showF showX io (⟨f, x⟩ : Fix n F T () ()) = .ok io' ∧
      contents io' = contents io ++ "Fix{" ++ toString n ++ "}(" ++ reprF f ++ ", " ++ reprX x ++ ")") ∧
    (∃ io', showSplat print showF io (splat makeSplat f) = .ok io' ∧
      contents io' = contents io ++ "splat(" ++ reprF f ++ ")")) ∧
  (let printS : String → String → Jl String := fun s str => .ok (s ++ str)
   let printC : String → Char → Jl String := fun s ch => .ok (s ++ String.singleton ch)
   let showPart := showComposedFunction id (fun s => s == "+") printC printS
   showComposed (fun _ : String => false) (showComposedDefault printS) showPart printS showPart
     "" (composeTwo "sin" "cos") = .ok "sin ∘ cos" ∧
   showNegatedComposed printC showPart "" (negateFunction "!" "isempty") =
     .ok "!isempty" ∧
   showNegatedComposed printC showPart "" (negateFunction "!" "+") =
     .ok "!(+)" ∧
   showFix (fun s k => .ok (s ++ "Fix{" ++ toString k ++ "}")) printC printS printS
     "" (⟨"+", "1"⟩ : Fix 2 String String () ()) = .ok "Fix{2}(+, 1)" ∧
   showSplat printS printS "" (splat makeSplat "+") = .ok "splat(+)")

theorem displayContract_proven : DisplayContract := by
  constructor
  · intro IO α β γ F T contents print printChar showA showB showC showConstr showF showX
      reprA reprB reprC reprF reprX symbolA symbolB symbolC isOp io a b c n f x
      hPrint hPrintChar hShowA hShowB hShowC hShowConstr hShowF hShowX
      fmtOp showPartA showPartB showPartC showCompAB showCompBC
    have hPartA : ∀ s u, ∃ s', showPartA s u = .ok s' ∧
        contents s' = contents s ++ fmtOp (isOp (symbolA u)) (reprA u) := by
      intro s u
      dsimp [showPartA, showComposedFunction, fmtOp]
      by_cases hop : isOp (symbolA u) = true
      · rcases hPrintChar s '(' with ⟨s1, hs1, hc1⟩
        rcases hShowA s1 u with ⟨s2, hs2, hc2⟩
        rcases hPrintChar s2 ')' with ⟨s3, hs3, hc3⟩
        refine ⟨s3, ?_, ?_⟩
        · simp [hop, hs1, hs2, hs3, Bind.bind, Except.bind]
        · rw [hc3, hc2, hc1]; simp [hop, String.append_assoc]
      · have hopF : isOp (symbolA u) = false := Bool.eq_false_iff.mpr hop
        rcases hShowA s u with ⟨s1, hs1, hc1⟩
        exact ⟨s1, by simp [hopF, hs1], by simp [hopF, hc1]⟩
    have hPartB : ∀ s v, ∃ s', showPartB s v = .ok s' ∧
        contents s' = contents s ++ fmtOp (isOp (symbolB v)) (reprB v) := by
      intro s v
      dsimp [showPartB, showComposedFunction, fmtOp]
      by_cases hop : isOp (symbolB v) = true
      · rcases hPrintChar s '(' with ⟨s1, hs1, hc1⟩
        rcases hShowB s1 v with ⟨s2, hs2, hc2⟩
        rcases hPrintChar s2 ')' with ⟨s3, hs3, hc3⟩
        refine ⟨s3, ?_, ?_⟩
        · simp [hop, hs1, hs2, hs3, Bind.bind, Except.bind]
        · rw [hc3, hc2, hc1]; simp [hop, String.append_assoc]
      · have hopF : isOp (symbolB v) = false := Bool.eq_false_iff.mpr hop
        rcases hShowB s v with ⟨s1, hs1, hc1⟩
        exact ⟨s1, by simp [hopF, hs1], by simp [hopF, hc1]⟩
    have hPartC : ∀ s w, ∃ s', showPartC s w = .ok s' ∧
        contents s' = contents s ++ fmtOp (isOp (symbolC w)) (reprC w) := by
      intro s w
      dsimp [showPartC, showComposedFunction, fmtOp]
      by_cases hop : isOp (symbolC w) = true
      · rcases hPrintChar s '(' with ⟨s1, hs1, hc1⟩
        rcases hShowC s1 w with ⟨s2, hs2, hc2⟩
        rcases hPrintChar s2 ')' with ⟨s3, hs3, hc3⟩
        refine ⟨s3, ?_, ?_⟩
        · simp [hop, hs1, hs2, hs3, Bind.bind, Except.bind]
        · rw [hc3, hc2, hc1]; simp [hop, String.append_assoc]
      · have hopF : isOp (symbolC w) = false := Bool.eq_false_iff.mpr hop
        rcases hShowC s w with ⟨s1, hs1, hc1⟩
        exact ⟨s1, by simp [hopF, hs1], by simp [hopF, hc1]⟩
    have hCompAB : ∀ s, ∃ s', showCompAB s (composeTwo a b) = .ok s' ∧
        contents s' = contents s ++ fmtOp (isOp (symbolA a)) (reprA a) ++ " ∘ " ++
          fmtOp (isOp (symbolB b)) (reprB b) := by
      intro s
      rcases hPartA s a with ⟨s1, hs1, hc1⟩
      rcases hPrint s1 " ∘ " with ⟨s2, hs2, hc2⟩
      rcases hPartB s2 b with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · simp [showCompAB, showComposed, composeTwo, composed, hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]
    have hCompBC : ∀ s, ∃ s', showCompBC s (composeTwo b c) = .ok s' ∧
        contents s' = contents s ++ fmtOp (isOp (symbolB b)) (reprB b) ++ " ∘ " ++
          fmtOp (isOp (symbolC c)) (reprC c) := by
      intro s
      rcases hPartB s b with ⟨s1, hs1, hc1⟩
      rcases hPrint s1 " ∘ " with ⟨s2, hs2, hc2⟩
      rcases hPartC s2 c with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · simp [showCompBC, showComposed, composeTwo, composed, hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]
    have hNestedBC : ∀ s, ∃ s', showNestedComposed printChar showCompBC s (composeTwo b c) = .ok s' ∧
        contents s' = contents s ++ "(" ++ fmtOp (isOp (symbolB b)) (reprB b) ++ " ∘ " ++
          fmtOp (isOp (symbolC c)) (reprC c) ++ ")" := by
      intro s
      rcases hPrintChar s '(' with ⟨s1, hs1, hc1⟩
      rcases hCompBC s1 with ⟨s2, hs2, hc2⟩
      rcases hPrintChar s2 ')' with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · simp [showNestedComposed, hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]; simp [String.append_assoc]
    refine ⟨hShowA io a, hPartA io a, hCompAB io, ?_, hNestedBC io, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hCompAB io with ⟨s1, hs1, hc1⟩
      rcases hPrint s1 " ∘ " with ⟨s2, hs2, hc2⟩
      rcases hPartC s2 c with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · change (do
          let io ← showCompAB io (composeTwo a b)
          let io ← print io " ∘ "
          showPartC io c) = .ok s3
        simp [hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]
    · rcases hPartA io a with ⟨s1, hs1, hc1⟩
      rcases hPrint s1 " ∘ " with ⟨s2, hs2, hc2⟩
      rcases hNestedBC s2 with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · change (do
          let io ← showPartA io a
          let io ← print io " ∘ "
          showNestedComposed printChar showCompBC io (composeTwo b c)) = .ok s3
        simp [hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]; simp [String.append_assoc]
    · rcases hPrintChar io '!' with ⟨s1, hs1, hc1⟩
      rcases hPartB s1 b with ⟨s2, hs2, hc2⟩
      refine ⟨s2, ?_, ?_⟩
      · simp [showNegatedComposed, negateFunction, composeTwo, composed, hs1, hs2, Bind.bind, Except.bind]
      · rw [hc2, hc1]; simp [String.append_assoc]
    · rcases hPrintChar io '!' with ⟨s1, hs1, hc1⟩
      rcases hPartB s1 b with ⟨s2, hs2, hc2⟩
      refine ⟨s2, ?_, ?_⟩
      · simp [showNestedNegatedComposed, showNegatedComposed, negateFunction, composeTwo, composed,
          hs1, hs2, Bind.bind, Except.bind]
      · rw [hc2, hc1]; simp [String.append_assoc]
    · rcases hShowConstr io n with ⟨s1, hs1, hc1⟩
      rcases hPrintChar s1 '(' with ⟨s2, hs2, hc2⟩
      rcases hShowF s2 f with ⟨s3, hs3, hc3⟩
      rcases hPrintChar s3 ',' with ⟨s4, hs4, hc4⟩
      rcases hPrintChar s4 ' ' with ⟨s5, hs5, hc5⟩
      rcases hShowX s5 x with ⟨s6, hs6, hc6⟩
      rcases hPrintChar s6 ')' with ⟨s7, hs7, hc7⟩
      refine ⟨s7, ?_, ?_⟩
      · simp [showFix, hs1, hs2, hs3, hs4, hs5, hs6, hs7, Bind.bind, Except.bind]
      · rw [hc7, hc6, hc5, hc4, hc3, hc2, hc1]; simp [String.append_assoc]
    · rcases hPrint io "splat(" with ⟨s1, hs1, hc1⟩
      rcases hShowF s1 f with ⟨s2, hs2, hc2⟩
      rcases hPrint s2 ")" with ⟨s3, hs3, hc3⟩
      refine ⟨s3, ?_, ?_⟩
      · simp [showSplat, splat, makeSplat, hs1, hs2, hs3, Bind.bind, Except.bind]
      · rw [hc3, hc2, hc1]
  · refine ⟨rfl, rfl, rfl, rfl, rfl⟩

section TupleSplit
open JuliaLean.base.tuple

private theorem i64_min_nonpos : IntTy.i64.min ≤ 0 := by
  simp [IntTy.min, IntTy.signed, IntTy.bits]

private theorem mapM_map' {γ β : Type} (g : Nat → γ) (f : γ → R β) (l : List Nat) :
    (l.map g).mapM f = l.mapM (f ∘ g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

private theorem mapM_range_ok {β : Type} (n : Nat) (f : Nat → R β) (L : List β)
    (hl : L.length = n) (h : ∀ k (hk : k < L.length), f k = .ok L[k]) :
    (List.range n).mapM f = .ok L := by
  induction n generalizing f L with
  | zero =>
    cases L with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ n ih =>
    cases L with
    | nil => simp at hl
    | cons b L =>
      rw [List.range_succ_eq_map, List.mapM_cons, mapM_map']
      have h0 : f 0 = .ok b := h 0 (by simp)
      have hr := ih (f ∘ Nat.succ) L (by simpa using hl)
        (fun k hk => h (k + 1) (by simp; omega))
      rw [h0, hr]
      rfl

private theorem getfieldInBounds {α : Type} (t : List α) (i : Nat) (h : i < t.length) :
    getfield t ((i : Int) + 1) = .ok t[i] := by
  unfold getfield
  have hpos : (1 : Int) ≤ (i : Int) + 1 := by omega
  have hindex : ((i : Int) + 1 - 1).toNat = i := by omega
  rw [if_pos hpos, hindex, List.getElem?_eq_getElem h]

private theorem getindexInteger_litI64 {α : Type} (args : List α) (x : Int) (i : Nat) (v : α)
    (convert : α → R α) (hconvert : ∀ a, convert a = .ok a)
    (hval : (JInt.lit .i64 x).val = (i : Int) + 1) (hi : i < args.length)
    (hv : args[i] = v) :
    (do
      let value ← getindexInteger args (Index.integer .i64 (JInt.lit .i64 x))
      convert value) = .ok v := by
  change (do
    let value ← getfield args (JInt.lit .i64 x).val
    convert value) = .ok v
  rw [hval, getfieldInBounds args i hi, hv]
  exact hconvert v

private theorem getindexVector_integerRange {α : Type} (args : List α)
    (typing : TupleConversion α)
    (hconvert : ∀ a, typing.convert (tupleEltype typing.eltypes (typing.typeof args)) a = .ok a)
    (first last : Int) (L : List α)
    (hL : L.length = (last - first + 1).toNat)
    (hstep : ∀ k (hk : k < L.length),
      ∃ (i : Nat) (hi : i < args.length),
        (JInt.lit .i64 (first + (k : Int))).val = (i : Int) + 1 ∧
        args[i] = L[k]) :
    getindexVector noCustomIndex typing args ((integerRange first last).map .integer) =
      .ok L := by
  unfold getindexVector integerRange
  rw [List.map_map, mapM_map']
  apply mapM_range_ok _ _ L hL
  intro k hk
  rcases hstep k hk with ⟨i, hi, hval, hv⟩
  exact getindexInteger_litI64 args (first + (k : Int)) i L[k]
    _ hconvert hval hi hv

theorem splitTuple_take_drop {α : Type} (args : List α) (n : Nat)
    (typing : TupleConversion α)
    (hconvert : ∀ a, typing.convert (tupleEltype typing.eltypes (typing.typeof args)) a = .ok a)
    (hn : n ≤ args.length) (hlen : (args.length : Int) ≤ IntTy.i64.max) :
    splitTupleSlice typing args n 1 =
      .ok (args.take n, args.drop n) := by
  have hval_bound : ∀ (x : Int), 0 ≤ x → x ≤ (args.length : Int) → (JInt.lit .i64 x).val = x :=
    fun x hx0 hx => wrapInt_of_inRange .i64 x
      ⟨Int.le_trans i64_min_nonpos hx0, Int.le_trans hx hlen⟩
  clear hlen
  unfold splitTupleSlice
  have hfirst :
      getindexVector noCustomIndex typing args ((integerRange 1 n).map .integer) =
        .ok (args.take n) := by
    apply getindexVector_integerRange args typing hconvert 1 n (args.take n)
    · rw [List.length_take_of_le hn]
      omega
    · intro k hk
      have hk' : k < n := by rw [List.length_take_of_le hn] at hk; exact hk
      have hk_lt : k < args.length := Nat.lt_of_lt_of_le hk' hn
      refine ⟨k, hk_lt, ?_, (List.getElem_take).symm⟩
      rw [hval_bound (1 + (k : Int)) (by omega) (by omega)]
      omega
  have hlast :
      getindexVector noCustomIndex typing args ((integerRange ((n : Int) + 1) args.length).map .integer) =
        .ok (args.drop n) := by
    apply getindexVector_integerRange args typing hconvert ((n : Int) + 1) args.length (args.drop n)
    · rw [List.length_drop]
      omega
    · intro k hk
      have hk' : k < args.length - n := by rw [List.length_drop] at hk; exact hk
      have hnk_lt : n + k < args.length := by omega
      refine ⟨n + k, hnk_lt, ?_, (List.getElem_drop).symm⟩
      rw [hval_bound (((n : Int) + 1) + (k : Int)) (by omega) (by omega)]
      omega
  rw [hfirst, hlast]
  rfl

end TupleSplit

/-- For tuple lengths representable by `Int64` and value-preserving tuple element conversion,
the end-to-end `Fix{N}` construction, invocation, and type-tag contract chains
`makeFix` into `fixCall` succeeds if and only if `isInt = true ∧ 1 ≤ n ∧ n.toNat - 1 ≤ args.length`,
splicing `⟨tx, fixed⟩` at 1-based position `n.toNat` into the heterogeneous argument list `args`
and recording `n.toNat`, `stableTypeof typeOfF f`, and `stableTypeof typeOfX fixed` in the
`Fix` type parameters (and failing with `ArgumentError` iff `isInt = false ∨ n < 1 ∨ args.length < n.toNat - 1`). -/
def FixCallPosition : Prop :=
  ∀ (τ β K σ₁ σ₂ : Type) (Elem : τ → Type) (tx : τ)
    (f : List (Σ t : τ, Elem t) → K → β) (fixed : Elem tx)
    (isInt : Bool) (n : Int) (args : List (Σ t : τ, Elem t)) (kw : K)
    (showInt typeName : Int → String)
    (typeOfF : (List (Σ t : τ, Elem t) → K → β) → σ₁)
    (typeOfX : Elem tx → σ₂)
    (typing : JuliaLean.base.tuple.TupleConversion (Σ t : τ, Elem t)),
  (∀ xs a, typing.convert (JuliaLean.base.tuple.tupleEltype typing.eltypes (typing.typeof xs)) a = .ok a) →
  (args.length : Int) ≤ IntTy.i64.max →
  let fixedElem : Σ t : τ, Elem t := ⟨tx, fixed⟩
  let split := fun (xs : List (Σ t : τ, Elem t)) (k : Nat) =>
    JuliaLean.base.tuple.splitTupleSlice typing xs (k : Int) 1
  let runFix : JuliaLean.base.tuple.R β := do
    let fix ← (makeFix isInt n showInt typeName Int.toNat
      (stableTypeof typeOfF) (stableTypeof typeOfX) f fixed).mapError .julia
    fixCall split fix args kw
  (isInt = true ∧ 1 ≤ n →
    ∃ fixVal,
      makeFix isInt n showInt typeName Int.toNat
          (stableTypeof typeOfF) (stableTypeof typeOfX) f fixed = .ok fixVal ∧
      fixPosition fixVal = n.toNat ∧
      fixFunctionTag fixVal = stableTypeof typeOfF f ∧
      fixValueTag fixVal = stableTypeof typeOfX fixed) ∧
  ((∃ res, runFix = .ok res) ↔
    (isInt = true ∧ 1 ≤ n ∧ n.toNat - 1 ≤ args.length)) ∧
  ((∃ msg, runFix = .error (.julia (.argumentError msg))) ↔
    (isInt = false ∨ n < 1 ∨ args.length < n.toNat - 1)) ∧
  (isInt = true → 1 ≤ n → n.toNat - 1 ≤ args.length →
    runFix = .ok (f (args.take (n.toNat - 1) ++ [fixedElem] ++ args.drop (n.toNat - 1)) kw) ∧
    (args.take (n.toNat - 1) ++ [fixedElem] ++ args.drop (n.toNat - 1)).length = args.length + 1 ∧
    (args.take (n.toNat - 1) ++ [fixedElem] ++ args.drop (n.toNat - 1))[n.toNat - 1]? = some fixedElem)

theorem fixCallPosition_proven : FixCallPosition := by
  intro τ β K σ₁ σ₂ Elem tx f fixed isInt n args kw showInt typeName typeOfF typeOfX typing hconvert
    hlenArg fixedElem split runFix
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, hn⟩
    refine ⟨⟨f, fixed⟩, ?_, rfl, rfl, rfl⟩
    have hnot : ¬n < 1 := by omega
    simp [makeFix, hnot]
  · cases isInt with
    | false =>
        simp [runFix, makeFix, Except.mapError, Bind.bind, Except.bind]
    | true =>
        by_cases hn : n < 1
        · have hnotge : ¬(1 ≤ n) := by omega
          simp [runFix, makeFix, hn, hnotge, Except.mapError, Bind.bind, Except.bind]
        · have hge : 1 ≤ n := by omega
          by_cases hargs : n.toNat - 1 ≤ args.length
          · have hnotlt : ¬args.length < n.toNat - 1 := by omega
            simp [runFix, makeFix, hn, hge, hargs, fixCall, split, hnotlt,
              splitTuple_take_drop args (n.toNat - 1) typing (hconvert args) hargs hlenArg,
              Except.mapError, Bind.bind, Except.bind]
          · have hlt : args.length < n.toNat - 1 := by omega
            simp [runFix, makeFix, hn, hge, hargs, fixCall, hlt,
              Except.mapError, Bind.bind, Except.bind]
  · cases isInt with
    | false =>
        simp [runFix, makeFix, Except.mapError, Bind.bind, Except.bind]
    | true =>
        by_cases hn : n < 1
        · simp [runFix, makeFix, hn, Except.mapError, Bind.bind, Except.bind]
        · by_cases hlt : args.length < n.toNat - 1
          · simp [runFix, makeFix, hn, fixCall, hlt,
              Except.mapError, Bind.bind, Except.bind]
          · have hargs : n.toNat - 1 ≤ args.length := by omega
            simp [runFix, makeFix, hn, fixCall, split, hlt,
              splitTuple_take_drop args (n.toNat - 1) typing (hconvert args) hargs hlenArg,
              Except.mapError, Bind.bind, Except.bind]
  · intro hInt hn hargs
    subst hInt
    have hnot : ¬n < 1 := by omega
    have hnotlt : ¬args.length < n.toNat - 1 := by omega
    have hpos : 1 ≤ n.toNat := by omega
    have hlen : (args.take (n.toNat - 1)).length = n.toNat - 1 :=
      List.length_take_of_le hargs
    refine ⟨?_, ?_, ?_⟩
    · simp [runFix, makeFix, hnot, fixCall, split, hnotlt,
        splitTuple_take_drop args (n.toNat - 1) typing (hconvert args) hargs hlenArg,
        Except.mapError, Bind.bind, Except.bind, fixedElem]
    · simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
      omega
    · rw [List.append_assoc, List.getElem?_append_right (by omega)]
      simp [hlen]

/-- The specialized one- and two-position calls agree with the general insertion
algorithm; their callable may accept heterogeneous first and second argument types. -/
def FixOneTwoCallPlacement : Prop :=
  (∀ (τ β K : Type) (Elem : τ → Type) (tx ty : τ)
      (f : List (Σ t : τ, Elem t) → K → β) (fixed : Elem tx) (arg : Elem ty) (kw : K)
      (typing : JuliaLean.base.tuple.TupleConversion (Σ t : τ, Elem t)),
    (∀ xs a, typing.convert (JuliaLean.base.tuple.tupleEltype typing.eltypes (typing.typeof xs)) a = .ok a) →
    let split := fun (xs : List (Σ t : τ, Elem t)) (n : Nat) =>
      JuliaLean.base.tuple.splitTupleSlice typing xs n 1
    fixCall split (⟨f, fixed⟩ : Fix 1 _ (Elem tx) () ()) [⟨ty, arg⟩] kw =
      .ok (fixOneCall (⟨fun a b k => f [⟨tx, a⟩, ⟨ty, b⟩] k, fixed⟩ : Fix 1 _ (Elem tx) () ()) arg kw) ∧
    fixCall split (⟨f, fixed⟩ : Fix 2 _ (Elem tx) () ()) [⟨ty, arg⟩] kw =
      .ok (fixTwoCall (⟨fun a b k => f [⟨ty, a⟩, ⟨tx, b⟩] k, fixed⟩ : Fix 2 _ (Elem tx) () ()) arg kw)) ∧
  (∀ (A B R K : Type) (f : A → B → K → R) (a : A) (b : B) (kw : K),
    fixOneCall (⟨f, a⟩ : Fix 1 (A → B → K → R) A () ()) b kw =
      fixTwoCall (⟨f, b⟩ : Fix 2 (A → B → K → R) B () ()) a kw)

theorem fixOneTwoCallPlacement_proven : FixOneTwoCallPlacement := by
  constructor
  · intro τ β K Elem tx ty f fixed arg kw typing hconvert split
    have h0 := splitTuple_take_drop [ (⟨ty, arg⟩ : Σ t : τ, Elem t) ] 0 typing (hconvert _) (by simp) (by simp [IntTy.max, IntTy.signed, IntTy.bits])
    have h1 := splitTuple_take_drop [ (⟨ty, arg⟩ : Σ t : τ, Elem t) ] 1 typing (hconvert _) (by simp) (by simp [IntTy.max, IntTy.signed, IntTy.bits])
    constructor
    · simp [split, fixCall, h0, fixOneCall, Bind.bind, Except.bind]
    · simp [split, fixCall, h1, fixTwoCall, Bind.bind, Except.bind]
  · intros; rfl

/-- Documented `Fix{N}` nesting and `ArgumentError` contract (`base/operators.jl:1185-1220`):
when chaining an outer `Fix{n₂}(..., x₂)` around an inner `Fix{n₁}(f, x₁)`,
(1) the nested invocation throws `ArgumentError` if and only if a type parameter is not `Int`
(`isInt₁ = false ∨ isInt₂ = false`), a position is below `1` (`n₁ < 1 ∨ n₂ < 1`), the outer
call receives fewer than `n₂ - 1` arguments (`args.length < n₂.toNat - 1`), or the inner call
receives fewer than `n₁ - 1` arguments after the outer `Fix` splices `x₂`
(`args.length + 1 < n₁.toNat - 1`);
(2) `Fix{1}(Fix{2}(f, x₁), x₂)` succeeds even on an empty argument tuple `[]` and fixes the
first and second arguments (`f(x₂, x₁, args...)`);
(3) `Fix{2}(Fix{1}(f, x₁), x₂)` rejects `[]` with `ArgumentError` and on `y₁ :: ys` fixes the
first and third arguments (`f(x₁, y₁, x₂, ys...)`). -/
def FixNestingAndErrorContract : Prop :=
  ∀ (τ β K σ₁ σ₂ σ₃ : Type) (Elem : τ → Type) (tx₁ tx₂ : τ)
    (f : List (Σ t : τ, Elem t) → K → β) (x₁ : Elem tx₁) (x₂ : Elem tx₂)
    (isInt₁ isInt₂ : Bool) (n₁ n₂ : Int)
    (args : List (Σ t : τ, Elem t)) (y₁ : Σ t : τ, Elem t) (ys : List (Σ t : τ, Elem t)) (kw : K)
    (showInt typeName : Int → String)
    (typeOfF : (List (Σ t : τ, Elem t) → K → β) → σ₁)
    (typeOfInner : (List (Σ t : τ, Elem t) → K → JuliaLean.base.tuple.R β) → σ₂)
    (typeOfX₁ : Elem tx₁ → σ₃) (typeOfX₂ : Elem tx₂ → σ₃)
    (typing : JuliaLean.base.tuple.TupleConversion (Σ t : τ, Elem t)),
  (∀ xs a, typing.convert (JuliaLean.base.tuple.tupleEltype typing.eltypes (typing.typeof xs)) a = .ok a) →
  (args.length + 1 : Int) ≤ IntTy.i64.max →
  (ys.length + 2 : Int) ≤ IntTy.i64.max →
  let split := fun (xs : List (Σ t : τ, Elem t)) (k : Nat) =>
    JuliaLean.base.tuple.splitTupleSlice typing xs (k : Int) 1
  let runNested (b₁ b₂ : Bool) (m₁ m₂ : Int) (xs : List (Σ t : τ, Elem t)) :
      JuliaLean.base.tuple.R β := do
    let innerFix ← (makeFix b₁ m₁ showInt typeName Int.toNat
      (stableTypeof typeOfF) (stableTypeof typeOfX₁) f x₁).mapError .julia
    let innerCall : List (Σ t : τ, Elem t) → K → JuliaLean.base.tuple.R β :=
      fun zs k => fixCall split innerFix zs k
    let outerFix ← (makeFix b₂ m₂ showInt typeName Int.toNat
      (stableTypeof typeOfInner) (stableTypeof typeOfX₂) innerCall x₂).mapError .julia
    let nestedRes ← fixCall split outerFix xs kw
    nestedRes
  ((∃ msg, runNested isInt₁ isInt₂ n₁ n₂ args = .error (.julia (.argumentError msg))) ↔
    (isInt₁ = false ∨ isInt₂ = false ∨ n₁ < 1 ∨ n₂ < 1 ∨
      args.length < n₂.toNat - 1 ∨ args.length + 1 < n₁.toNat - 1)) ∧
  ((∃ res, runNested isInt₁ isInt₂ n₁ n₂ args = .ok res) ↔
    (isInt₁ = true ∧ isInt₂ = true ∧ 1 ≤ n₁ ∧ 1 ≤ n₂ ∧
      n₂.toNat - 1 ≤ args.length ∧ n₁.toNat - 1 ≤ args.length + 1)) ∧
  runNested true true 2 1 args = .ok (f (⟨tx₂, x₂⟩ :: ⟨tx₁, x₁⟩ :: args) kw) ∧
  (∃ msg, runNested true true 1 2 [] = .error (.julia (.argumentError msg))) ∧
  runNested true true 1 2 (y₁ :: ys) = .ok (f (⟨tx₁, x₁⟩ :: y₁ :: ⟨tx₂, x₂⟩ :: ys) kw)

theorem fixNestingAndErrorContract_proven : FixNestingAndErrorContract := by
  intro τ β K σ₁ σ₂ σ₃ Elem tx₁ tx₂ f x₁ x₂ isInt₁ isInt₂ n₁ n₂ args y₁ ys kw
    showInt typeName typeOfF typeOfInner typeOfX₁ typeOfX₂ typing hconvert hlenArgs hlenYs
    split runNested
  have hlenArgs0 : (args.length : Int) ≤ IntTy.i64.max := by omega
  have hSpliceLen : ∀ (k : Nat), k ≤ args.length →
      (args.take k ++ [ (⟨tx₂, x₂⟩ : Σ t : τ, Elem t) ] ++ args.drop k).length = args.length + 1 := by
    intro k hk
    simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
    omega
  have hNestedTrue : ∀ (m₁ m₂ : Int) (xs : List (Σ t : τ, Elem t)),
      1 ≤ m₁ → 1 ≤ m₂ → m₂.toNat - 1 ≤ xs.length → (xs.length : Int) ≤ IntTy.i64.max →
      runNested true true m₁ m₂ xs =
        fixCall split (⟨f, x₁⟩ : Fix m₁.toNat _ _ (stableTypeof typeOfF f) (stableTypeof typeOfX₁ x₁))
          (xs.take (m₂.toNat - 1) ++ [⟨tx₂, x₂⟩] ++ xs.drop (m₂.toNat - 1)) kw := by
    intro m₁ m₂ xs hm₁ hm₂ hxs hlenXs
    have hnot₁ : ¬m₁ < 1 := by omega
    have hnot₂ : ¬m₂ < 1 := by omega
    have hnotlt : ¬xs.length < m₂.toNat - 1 := by omega
    have hsp := splitTuple_take_drop xs (m₂.toNat - 1) typing (hconvert xs) hxs hlenXs
    simp [runNested, makeFix, hnot₁, hnot₂, fixCall, split, hnotlt, hsp,
      Except.mapError, Bind.bind, Except.bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases isInt₁ with
    | false =>
        simp [runNested, makeFix, Except.mapError, Bind.bind, Except.bind]
    | true =>
        by_cases hn₁ : n₁ < 1
        · simp [runNested, makeFix, hn₁, Except.mapError, Bind.bind, Except.bind]
        · have hge₁ : 1 ≤ n₁ := by omega
          cases isInt₂ with
          | false =>
              simp [runNested, makeFix, hn₁, Except.mapError, Bind.bind, Except.bind]
          | true =>
              by_cases hn₂ : n₂ < 1
              · simp [runNested, makeFix, hn₁, hn₂, Except.mapError, Bind.bind, Except.bind]
              · have hge₂ : 1 ≤ n₂ := by omega
                by_cases houter : args.length < n₂.toNat - 1
                · simp [runNested, makeFix, hn₁, hn₂, fixCall, houter,
                    Except.mapError, Bind.bind, Except.bind]
                · have houter_le : n₂.toNat - 1 ≤ args.length := by omega
                  rw [hNestedTrue n₁ n₂ args hge₁ hge₂ houter_le hlenArgs0]
                  let mid := args.take (n₂.toNat - 1) ++ [ (⟨tx₂, x₂⟩ : Σ t : τ, Elem t) ] ++ args.drop (n₂.toNat - 1)
                  change (∃ msg, fixCall split (⟨f, x₁⟩ : Fix n₁.toNat _ _ (stableTypeof typeOfF f) (stableTypeof typeOfX₁ x₁)) mid kw =
                    .error (.julia (.argumentError msg))) ↔ _
                  have hmid_len : mid.length = args.length + 1 := hSpliceLen (n₂.toNat - 1) houter_le
                  have hmid_max : (mid.length : Int) ≤ IntTy.i64.max := by omega
                  by_cases hinner : args.length + 1 < n₁.toNat - 1
                  · have hinner' : mid.length < n₁.toNat - 1 := by omega
                    simp [fixCall, hinner', hn₁, hn₂, houter, hinner]
                  · have hinner_le : n₁.toNat - 1 ≤ mid.length := by omega
                    have hnot_inner : ¬mid.length < n₁.toNat - 1 := by omega
                    have hsp_in := splitTuple_take_drop mid (n₁.toNat - 1) typing (hconvert mid) hinner_le hmid_max
                    simp [fixCall, split, hnot_inner, hsp_in, hn₁, hn₂, houter, hinner,
                      Bind.bind, Except.bind]
  · cases isInt₁ with
    | false =>
        simp [runNested, makeFix, Except.mapError, Bind.bind, Except.bind]
    | true =>
        by_cases hn₁ : n₁ < 1
        · have hnotge₁ : ¬(1 ≤ n₁) := by omega
          simp [runNested, makeFix, hn₁, hnotge₁, Except.mapError, Bind.bind, Except.bind]
        · have hge₁ : 1 ≤ n₁ := by omega
          cases isInt₂ with
          | false =>
              simp [runNested, makeFix, hn₁, Except.mapError, Bind.bind, Except.bind]
          | true =>
              by_cases hn₂ : n₂ < 1
              · have hnotge₂ : ¬(1 ≤ n₂) := by omega
                simp [runNested, makeFix, hn₁, hn₂, hnotge₂, Except.mapError, Bind.bind, Except.bind]
              · have hge₂ : 1 ≤ n₂ := by omega
                by_cases houter : n₂.toNat - 1 ≤ args.length
                · rw [hNestedTrue n₁ n₂ args hge₁ hge₂ houter hlenArgs0]
                  let mid := args.take (n₂.toNat - 1) ++ [ (⟨tx₂, x₂⟩ : Σ t : τ, Elem t) ] ++ args.drop (n₂.toNat - 1)
                  change (∃ res, fixCall split (⟨f, x₁⟩ : Fix n₁.toNat _ _ (stableTypeof typeOfF f) (stableTypeof typeOfX₁ x₁)) mid kw = .ok res) ↔ _
                  have hmid_len : mid.length = args.length + 1 := hSpliceLen (n₂.toNat - 1) houter
                  have hmid_max : (mid.length : Int) ≤ IntTy.i64.max := by omega
                  by_cases hinner : n₁.toNat - 1 ≤ args.length + 1
                  · have hinner_le : n₁.toNat - 1 ≤ mid.length := by omega
                    have hnot_inner : ¬mid.length < n₁.toNat - 1 := by omega
                    have hsp_in := splitTuple_take_drop mid (n₁.toNat - 1) typing (hconvert mid) hinner_le hmid_max
                    simp [fixCall, split, hnot_inner, hsp_in, hge₁, hge₂, houter, hinner,
                      Bind.bind, Except.bind]
                  · have hinner_lt : mid.length < n₁.toNat - 1 := by omega
                    simp [fixCall, hinner_lt, hge₁, hge₂, houter, hinner]
                · have houter_lt : args.length < n₂.toNat - 1 := by omega
                  simp [runNested, makeFix, hn₁, hn₂, hge₁, hge₂, fixCall,
                    houter, houter_lt, Except.mapError, Bind.bind, Except.bind]
  · rw [hNestedTrue 2 1 args (by omega) (by omega) (by omega) hlenArgs0]
    let mid : List (Σ t : τ, Elem t) := ⟨tx₂, x₂⟩ :: args
    change fixCall split (⟨f, x₁⟩ : Fix 2 _ _ (stableTypeof typeOfF f) (stableTypeof typeOfX₁ x₁)) mid kw = _
    have hmid_max : (mid.length : Int) ≤ IntTy.i64.max := by
      simp only [mid, List.length_cons]; omega
    have hsp := splitTuple_take_drop mid 1 typing (hconvert mid) (by simp [mid]) hmid_max
    simp [fixCall, split, mid, hsp, Bind.bind, Except.bind]
  · simp [runNested, makeFix, fixCall, Except.mapError, Bind.bind, Except.bind]
  · have hlenFull : ((y₁ :: ys).length : Int) ≤ IntTy.i64.max := by
      simp only [List.length_cons]; omega
    rw [hNestedTrue 1 2 (y₁ :: ys) (by omega) (by omega) (by simp) hlenFull]
    let mid : List (Σ t : τ, Elem t) := y₁ :: ⟨tx₂, x₂⟩ :: ys
    change fixCall split (⟨f, x₁⟩ : Fix 1 _ _ (stableTypeof typeOfF f) (stableTypeof typeOfX₁ x₁)) mid kw = _
    have hmid_max : (mid.length : Int) ≤ IntTy.i64.max := by
      simp only [mid, List.length_cons]; omega
    have hsp := splitTuple_take_drop mid 0 typing (hconvert mid) (by omega) hmid_max
    simp [fixCall, split, mid, hsp, Bind.bind, Except.bind]

/-- Every comparison partial application carries position `2`, its distinct operator
type tag (`typeof(op)`), and its fixed-value tag (`typeof(x)`), and denotes the
corresponding mathematical comparison of represented values for mixed-width and
mixed-signedness inputs. -/
def Fix2ArgumentOrder : Prop := ∀ (s t : IntTy) (a : JInt s) (b : JInt t),
  let fIseq := fixIsequal (isequalDefault JuliaLean.base.int.eq) b
  let fEq := fixEqual JuliaLean.base.int.eq b
  let fNe := fixNotEqual (notEqual JuliaLean.base.int.eq JuliaLean.base.bool.notBool) b
  let fGe := fixGreaterEqual (greaterEqual JuliaLean.base.int.le) b
  let fLe := fixLessEqual JuliaLean.base.int.le b
  let fGt := fixGreater (greaterThan JuliaLean.base.int.lt) b
  let fLt := fixLess JuliaLean.base.int.lt b
  fixPosition fIseq = 2 ∧ fixFunctionTag fIseq = .isequal ∧ fixValueTag fIseq = b ∧
  fixPosition fEq = 2 ∧ fixFunctionTag fEq = .eq ∧ fixValueTag fEq = b ∧
  fixPosition fNe = 2 ∧ fixFunctionTag fNe = .ne ∧ fixValueTag fNe = b ∧
  fixPosition fGe = 2 ∧ fixFunctionTag fGe = .ge ∧ fixValueTag fGe = b ∧
  fixPosition fLe = 2 ∧ fixFunctionTag fLe = .le ∧ fixValueTag fLe = b ∧
  fixPosition fGt = 2 ∧ fixFunctionTag fGt = .gt ∧ fixValueTag fGt = b ∧
  fixPosition fLt = 2 ∧ fixFunctionTag fLt = .lt ∧ fixValueTag fLt = b ∧
  (fixTwoCall fIseq a () = true ↔ a.val = b.val) ∧
  (fixTwoCall fEq a () = true ↔ a.val = b.val) ∧
  (fixTwoCall fNe a () = true ↔ a.val ≠ b.val) ∧
  (fixTwoCall fGe a () = true ↔ b.val ≤ a.val) ∧
  (fixTwoCall fLe a () = true ↔ a.val ≤ b.val) ∧
  (fixTwoCall fGt a () = true ↔ b.val < a.val) ∧
  (fixTwoCall fLt a () = true ↔ a.val < b.val)

theorem fix2ArgumentOrder_proven : Fix2ArgumentOrder := by
  intro s t a b
  simp [fixPosition, fixFunctionTag, fixValueTag,
    fixTwoCall, fixIsequal, fixEqual, fixNotEqual, fixGreaterEqual, fixLessEqual,
    fixGreater, fixLess, isequalDefault, notEqual, greaterEqual, greaterThan,
    JuliaLean.base.bool.notBool, JuliaLean.Proofs.base.int.eq_eq,
    JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.le_eq]

/-- All unary comparison constructors retain their `Fix2` operator and value type
parameters and the documented relation between abstract values across heterogeneous
item and fixed-argument types. -/
def GenericUnaryComparisons : Prop :=
  ∀ (A B V : Type) [DecidableEq V] (r : V → V → Prop) [DecidableRel r]
    (aValue : A → V) (bValue : B → V) (equal less le : A → B → Bool)
    (lessBack leBack : B → A → Bool),
  (∀ a b, equal a b = decide (aValue a = bValue b)) →
  (∀ a b, less a b = decide (r (aValue a) (bValue b))) →
  (∀ a b, le a b = decide (r (aValue a) (bValue b) ∨ aValue a = bValue b)) →
  (∀ b a, lessBack b a = decide (r (bValue b) (aValue a))) →
  (∀ b a, leBack b a = decide (r (bValue b) (aValue a) ∨ bValue b = aValue a)) →
  ∀ a b,
    fixFunctionTag (fixIsequal (isequalDefault equal) b) = .isequal ∧
    fixValueTag (fixIsequal (isequalDefault equal) b) = b ∧
    fixFunctionTag (fixEqual equal b) = .eq ∧
    fixValueTag (fixEqual equal b) = b ∧
    fixFunctionTag (fixNotEqual (notEqual equal JuliaLean.base.bool.notBool) b) = .ne ∧
    fixValueTag (fixNotEqual (notEqual equal JuliaLean.base.bool.notBool) b) = b ∧
    fixFunctionTag (fixLess less b) = .lt ∧
    fixValueTag (fixLess less b) = b ∧
    fixFunctionTag (fixLessEqual le b) = .le ∧
    fixValueTag (fixLessEqual le b) = b ∧
    fixFunctionTag (fixGreater (greaterThan lessBack) b) = .gt ∧
    fixValueTag (fixGreater (greaterThan lessBack) b) = b ∧
    fixFunctionTag (fixGreaterEqual (greaterEqual leBack) b) = .ge ∧
    fixValueTag (fixGreaterEqual (greaterEqual leBack) b) = b ∧
    (fixTwoCall (fixIsequal (isequalDefault equal) b) a () = true ↔ aValue a = bValue b) ∧
    (fixTwoCall (fixEqual equal b) a () = true ↔ aValue a = bValue b) ∧
    (fixTwoCall (fixNotEqual (notEqual equal JuliaLean.base.bool.notBool) b) a () = true ↔
      aValue a ≠ bValue b) ∧
    (fixTwoCall (fixLess less b) a () = true ↔ r (aValue a) (bValue b)) ∧
    (fixTwoCall (fixLessEqual le b) a () = true ↔ r (aValue a) (bValue b) ∨ aValue a = bValue b) ∧
    (fixTwoCall (fixGreater (greaterThan lessBack) b) a () = true ↔ r (bValue b) (aValue a)) ∧
    (fixTwoCall (fixGreaterEqual (greaterEqual leBack) b) a () = true ↔
      r (bValue b) (aValue a) ∨ bValue b = aValue a)

theorem genericUnaryComparisons_proven : GenericUnaryComparisons := by
  intro A B V _ r _ aValue bValue equal less le lessBack leBack heq hlt hle hgt hge a b
  simp [fixFunctionTag, fixValueTag,
    fixTwoCall, fixIsequal, fixEqual, fixNotEqual, fixLess, fixLessEqual,
    fixGreater, fixGreaterEqual, isequalDefault, notEqual, greaterThan, greaterEqual,
    JuliaLean.base.bool.notBool, heq, hlt, hle, hgt, hge]

def UnaryComparisonContract : Prop := Fix2ArgumentOrder ∧ GenericUnaryComparisons

theorem unaryComparisonContract_proven : UnaryComparisonContract :=
  ⟨fix2ArgumentOrder_proven, genericUnaryComparisons_proven⟩

/-- Splat and unsplat are inverse adapters (`unsplat(splat(f)) === f`, `splat(unsplat(f)) === f`),
`Splat(f)(args)` calls `f(args...)`, and `unsplat(f)(args...)` (the composition `f ∘ tuple`,
called through the source `ComposedFunction` call method) calls `f` on the tuple of its
arguments for every callable `f`, given only `tuple`'s law of packing its arguments. -/
def SplatRoundTrip : Prop :=
  (∀ (F : Type) (f : F), unsplatSplat (splat makeSplat f) = f ∧
    splatComposed (unsplatGeneric TupleFunction.tuple f) = f) ∧
  (∀ (A B R : Type) (f : A → B → R) (a : A) (b : B),
    splatCall (fun g (args : A × B) => g args.1 args.2) (splat makeSplat f) (a,b) =
      f a b) ∧
  (∀ (F T V σ : Type) (m : CallMethods F T V σ) (tupleF : F) (pack : List V → V)
      (f : Callee F T) (args : List V),
    (∀ xs, m.callFn tupleF xs [] = .ok (pack xs)) →
    composedCall m (unsplatGeneric (.plain (.fn tupleF)) f) args [] =
      callCallee m f [pack args] [])

theorem splatRoundTrip_proven : SplatRoundTrip := by
  refine ⟨?_, ?_, ?_⟩
  · intros; constructor <;> rfl
  · intros; rfl
  · intro F T V σ m tupleF pack f args htuple
    have h := callCallee_composeTwo m f (.plain (.fn tupleF)) args []
    change callCallee m (.composed (composeTwo f (.plain (.fn tupleF)))) args [] = _
    rw [h]
    simp [callCallee, callPlain, htuple, except_ok_bind]

/-- Splatting the heterogeneous left-fold callable preserves the concatenation law for
arbitrary argument-list lengths and changing accumulator/element types. -/
def SplatFoldContract : Prop := SplatRoundTrip ∧
  ∀ (τ σ : Type) (Acc : τ → Type) (Elem : σ → Type)
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : Σ t : τ, Acc t) (xs ys : List (Σ s : σ, Elem s)),
    splatCall (fun f args => f args) (splat makeSplat (afoldlMany op a)) (xs ++ ys) =
      afoldlMany op (afoldlMany op a xs) ys

theorem splatFoldContract_proven : SplatFoldContract := by
  refine ⟨splatRoundTrip_proven, ?_⟩
  intro τ σ Acc Elem op a xs ys
  exact (naryFoldLaw_proven.1 τ σ Unit Acc Elem () op a xs ys).1

/-- A stateful tap performs exactly the callback transition and preserves its input;
a failed callback propagates its exception rather than returning the input. -/
def TapReturnsInput : Prop :=
  (∀ (A B S : Type) (f : A → StateM S B) (a : A) (s : S),
    (tap f a).run s = (a, (f a).run s |>.2)) ∧
  (∀ (A B : Type) (f : A → Jl B) (a : A) (e : JlError),
    f a = .error e → tap f a = .error e)

theorem tapReturnsInput_proven : TapReturnsInput := by
  constructor
  · intros; rfl
  · intro A B f a e h
    simp [tap, h, Bind.bind, Except.bind]

/-- For every Real implementation, a successful one-based modulus lies in the
promised half-open interval, under the usual modulus and zero-test interface laws. -/
def Mod1ZeroRemainder : Prop :=
  ∀ (A : Type) (mod : A → A → Jl A) (iszero : A → Jl Bool)
    (zero : A) (lt le : A → A → Prop) (x y r : A),
  mod x y = .ok r →
  (iszero r = .ok true ↔ r = zero) →
  (iszero r = .ok false ↔ r ≠ zero) →
  (lt zero y → le y y ∧ (r = zero ∨ lt zero r ∧ le r y)) →
  (lt y zero → le y y ∧ (r = zero ∨ le y r ∧ lt r zero)) →
  (r = zero → (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok y) ∧
  (∀ result, (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok result →
    (lt zero y → lt zero result ∧ le result y) ∧
    (lt y zero → le y result ∧ lt result zero))

theorem mod1ZeroRemainder_proven : Mod1ZeroRemainder := by
  intro A mod iszero zero lt le x y r hm hz hn hp hneg
  by_cases hr : r = zero
  · have hi := hz.mpr hr
    have hout : (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok y := by
      simp [mod1, hm, hi, Bind.bind, Except.bind, Except.map, Sum.elim]
    refine ⟨fun _ => hout, ?_⟩
    intro result hresult
    have : result = y := by simpa [hout] using hresult.symm
    subst result
    exact ⟨fun h => ⟨h, (hp h).1⟩, fun h => ⟨(hneg h).1,h⟩⟩
  · have hi := hn.mpr hr
    have hout : (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok r := by
      simp [mod1, hm, hi, Bind.bind, Except.bind, Except.map, Sum.elim]
    refine ⟨fun h => False.elim (hr h), ?_⟩
    intro result hresult
    have : result = r := by simpa [hout] using hresult.symm
    subst result
    constructor
    · intro h
      exact (hp h).2.resolve_left hr
    · intro h
      exact (hneg h).2.resolve_left hr

/-- Quotient/remainder pairs calling the source `mod1` definition retain the integer
reconstruction invariant `x == (q - 1) * y + mod1(x, y)` and one-based bounds
`0 < mod1(x, y) ≤ y`, and `fldmod1` agrees with `cldmod1` whenever `fld1` and `cld` agree. -/
def DivisionPairProjection : Prop := ∀ (A : Type)
    (cld fld1 : A → A → Jl Int) (mod : A → A → Jl A) (iszero : A → Jl Bool)
    (val : A → Int) (x y m : A) (qf : Int),
  0 < val y →
  mod x y = .ok m →
  0 ≤ val m ∧ val m < val y →
  val x = qf * val y + val m →
  (iszero m = .ok true ↔ val m = 0) →
  (iszero m = .ok false ↔ val m ≠ 0) →
  cld x y = .ok (if val m = 0 then qf else qf + 1) →
  fld1 x y = .ok (if val m = 0 then qf else qf + 1) →
  cldmod1 cld (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = fldmod1 fld1 (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y ∧
  (∀ pair,
    (cldmod1 cld (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok pair ∨
      fldmod1 fld1 (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok pair) →
    val x = (pair.1 - 1) * val y + val pair.2 ∧
    0 < val pair.2 ∧ val pair.2 ≤ val y ∧
    val pair.2 = (if val m = 0 then val y else val m))

theorem divisionPairProjection_proven : DivisionPairProjection := by
  intro A cld fld1 mod iszero val x y m qf hy hm hmb hrecon hz hn hcld hfld
  by_cases hm0 : val m = 0
  · have hi : iszero m = .ok true := hz.mpr hm0
    have hmod1 : (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok y := by
      simp [mod1, hm, hi, Bind.bind, Except.bind, Except.map, Sum.elim]
    have hc : cldmod1 cld (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok (qf, y) := by
      simp [cldmod1, hcld, hm0, hmod1, Bind.bind, Except.bind]
    have hf : fldmod1 fld1 (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok (qf, y) := by
      simp [fldmod1, hfld, hm0, hmod1, Bind.bind, Except.bind]
    refine ⟨hc.trans hf.symm, ?_⟩
    intro pair hp
    have hpair : pair = (qf, y) := by
      rcases hp with h | h <;> simpa [hc, hf] using h.symm
    subst hpair
    dsimp only
    refine ⟨?_, hy, by omega, by simp [hm0]⟩
    calc
      val x = qf * val y + 0 := by omega
      _ = (qf - 1) * val y + val y := by rw [Int.sub_mul, Int.one_mul]; omega
  · have hi : iszero m = .ok false := hn.mpr hm0
    have hmod1 : (mod1 mod iszero pure x y).map (Sum.elim id id) = .ok m := by
      simp [mod1, hm, hi, Bind.bind, Except.bind, Except.map, Sum.elim]
    have hc : cldmod1 cld (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok (qf + 1, m) := by
      simp [cldmod1, hcld, hm0, hmod1, Bind.bind, Except.bind]
    have hf : fldmod1 fld1 (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok (qf + 1, m) := by
      simp [fldmod1, hfld, hm0, hmod1, Bind.bind, Except.bind]
    refine ⟨hc.trans hf.symm, ?_⟩
    intro pair hp
    have hpair : pair = (qf + 1, m) := by
      rcases hp with h | h <;> simpa [hc, hf] using h.symm
    subst hpair
    dsimp only
    have hq1 : qf + 1 - 1 = qf := by omega
    refine ⟨by rw [hq1, hrecon], by omega, by omega, by simp [hm0]⟩

/-- Both quotient/remainder APIs preserve `mod1`'s interval contract for arbitrary `Real`
and quotient types. -/
def GenericDivisionPairRange : Prop := ∀ (A Q : Type)
    (quotient : A → A → Jl Q) (mod : A → A → Jl A)
    (iszero : A → Jl Bool) (zero : A) (lt le : A → A → Prop)
    (x y r : A) (q : Q),
  quotient x y = .ok q → mod x y = .ok r →
  (iszero r = .ok true ↔ r = zero) →
  (iszero r = .ok false ↔ r ≠ zero) →
  (lt zero y → le y y ∧ (r = zero ∨ lt zero r ∧ le r y)) →
  (lt y zero → le y y ∧ (r = zero ∨ le y r ∧ lt r zero)) →
  ∀ pair,
    (cldmod1 quotient (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok pair ∨
      fldmod1 quotient (fun x y => (mod1 mod iszero pure x y).map (Sum.elim id id)) x y = .ok pair) →
    pair.1 = q ∧
      (lt zero y → lt zero pair.2 ∧ le pair.2 y) ∧
      (lt y zero → le y pair.2 ∧ lt pair.2 zero)

theorem genericDivisionPairRange_proven : GenericDivisionPairRange := by
  intro A Q quotient mod iszero zero lt le x y r q hq hm hz hn hp hneg pair hpair
  have hrange := (mod1ZeroRemainder_proven A mod iszero zero lt le x y r hm hz hn hp hneg).2
  have hpair' : (do
      let rem ← (mod1 mod iszero pure x y).map (Sum.elim id id)
      pure (q, rem)) = .ok pair := by
    rcases hpair with h | h <;>
      simpa [cldmod1, fldmod1, hq, Bind.bind, Except.bind] using h
  cases hrem : (mod1 mod iszero pure x y).map (Sum.elim id id) with
  | error e => simp [hrem, Bind.bind, Except.bind] at hpair'
  | ok result =>
    have heq : (q, result) = pair := by
      simpa [hrem, Bind.bind, Except.bind] using hpair'
    subst pair
    exact ⟨rfl, hrange result hrem⟩

def DivisionPairContract : Prop := DivisionPairProjection ∧ GenericDivisionPairRange

theorem divisionPairContract_proven : DivisionPairContract :=
  ⟨divisionPairProjection_proven, genericDivisionPairRange_proven⟩

theorem shl_zero_u64 (s : IntTy) (x : JInt s) :
    JuliaLean.base.int.shl_BitInteger_BitUnsigned (JuliaLean.base.int.zero x)
      (JuliaLean.base.int.unsigned (JInt.wrap .i64 0)) = JInt.lit s 0 := by
  unfold JuliaLean.base.int.zero
  cases s <;> decide

theorem shr_zero_u64 (s : IntTy) (x : JInt s) :
    JuliaLean.base.int.shrU (JuliaLean.base.int.zero x)
      (JuliaLean.base.int.unsigned (JInt.wrap .i64 0)) = JInt.lit s 0 := by
  unfold JuliaLean.base.int.zero
  cases s <;> decide

theorem lshr_zero_u64 (s : IntTy) (x : JInt s) :
    JuliaLean.base.int.lshr_BitInteger_BitUnsigned (JuliaLean.base.int.zero x)
      (JuliaLean.base.int.unsigned (JInt.wrap .i64 0)) = JInt.lit s 0 := by
  unfold JuliaLean.base.int.zero
  cases s <;> decide

/-- Across both arbitrary-precision `BigInt` values (`x : Int`) and every fixed-width
`BitInteger` width (`s : IntTy`, `x : JInt s`), and across every `BitInteger` shift-count
width (`t : IntTy`, including 128-bit counts) and `BigInt` shift counts (`c : Int`),
the eight shift methods reverse direction on negative counts, equate `>>>` and `>>` on
`BigInt`, delegate in-range counts to the machine `Int` methods, return `0` or `-1` on
out-of-range counts according to the value and count signs, and raise `MethodError` on
raw `UInt` counts. -/
def ShiftDirectionLaw : Prop :=
  (∀ (x c : Int) (u : Nat),
    let shlBig := fun (v : Int) (k : Nat) => v * (2 ^ k : Nat)
    let shrBig := fun (v : Int) (k : Nat) => v / (2 ^ k : Nat)
    let shlInt := shiftLeftInt Int.toNat shlBig shrBig
    let shrInt := shiftRightInt Int.toNat shrBig shlBig
    let lshrInt := shiftLogicalInt Int.toNat shrBig shlBig
    let inRangeI (n : Int) : Bool := decide (IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64)
    let nonnegBig (v : Int) : Bool := decide (0 ≤ v)
    let negBig (v : Int) : Bool := decide (v < 0)
    let maxU := (IntTy.max .u64).toNat
    shlInt x (-c) = shrInt x c ∧
    lshrInt x c = shrInt x c ∧
    shlInt x (Int.ofNat u) = x * (2 ^ u : Nat) ∧
    shrInt x (Int.ofNat u) = x / (2 ^ u : Nat) ∧
    shiftRightInteger true inRangeI id shrInt (fun _ => 0) 0
      (fun _ n => n) nonnegBig negBig x c = .error (.methodError ">>") ∧
    shiftLeftUnsigned true maxU id shlBig (fun _ => 0) x u = .error (.methodError "<<") ∧
    shiftLogicalUnsigned true maxU id shrBig (fun _ => 0) x u = .error (.methodError ">>>") ∧
    (inRangeI c = true →
      shiftLeftInteger inRangeI id shlInt (fun _ => 0) 0
        (fun _ n => n) nonnegBig nonnegBig x c = shlInt x c ∧
      shiftRightInteger false inRangeI id shrInt (fun _ => 0) 0
        (fun _ n => n) nonnegBig negBig x c = .ok (shrInt x c) ∧
      shiftLogicalInteger inRangeI id lshrInt (fun _ => 0) 0 x c = lshrInt x c) ∧
    (inRangeI c = false →
      shiftLeftInteger inRangeI id shlInt (fun _ => 0) 0
        (fun _ n => n) nonnegBig nonnegBig x c =
          (if 0 ≤ x ∨ 0 ≤ c then 0 else -1) ∧
      shiftRightInteger false inRangeI id shrInt (fun _ => 0) 0
        (fun _ n => n) nonnegBig negBig x c =
          .ok (if 0 ≤ x ∨ c < 0 then 0 else -1) ∧
      shiftLogicalInteger inRangeI id lshrInt (fun _ => 0) 0 x c = 0) ∧
    (maxU < u →
      shiftLeftUnsigned false maxU id shlBig (fun _ => 0) x u = .ok 0 ∧
      shiftLogicalUnsigned false maxU id shrBig (fun _ => 0) x u = .ok 0)) ∧
  (∀ (s : IntTy) (x : JInt s) (c : Int),
    let toU := fun n : Int => JuliaLean.base.int.unsigned (JInt.wrap .i64 n)
    let shl := JuliaLean.base.int.shl_BitInteger_BitUnsigned (t := s) (u := .u64)
    let shr := JuliaLean.base.int.shrU (t := s) (u := .u64)
    let lshr := JuliaLean.base.int.lshr_BitInteger_BitUnsigned (t := s) (u := .u64)
    (c ≠ 0 → shiftLeftInt toU shl shr x (-c) = shiftRightInt toU shr shl x c) ∧
    (c < 0 →
      shiftLeftInt toU shl shr x c = shr x (toU (-c)) ∧
      shiftRightInt toU shr shl x c = shl x (toU (-c)) ∧
      shiftLogicalInt toU lshr shl x c = shl x (toU (-c)))) ∧
  (∀ (s t : IntTy) (x : JInt s) (c : JInt t) (b : Int),
    let toU := fun n : Int => JuliaLean.base.int.unsigned (JInt.wrap .i64 n)
    let shl := JuliaLean.base.int.shl_BitInteger_BitUnsigned (t := s) (u := .u64)
    let shr := JuliaLean.base.int.shrU (t := s) (u := .u64)
    let lshr := JuliaLean.base.int.lshr_BitInteger_BitUnsigned (t := s) (u := .u64)
    let shlInt := shiftLeftInt toU shl shr
    let shrInt := shiftRightInt toU shr shl
    let lshrInt := shiftLogicalInt toU lshr shl
    let inRangeI (n : Int) : Bool := decide (IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64)
    let inRangeT (v : JInt t) : Bool := inRangeI v.val
    let remT (v : JInt t) : Int := (JInt.rem .i64 v).val
    let nonnegX (v : JInt s) : Bool := decide (0 ≤ v.val)
    let nonnegT (v : JInt t) : Bool := decide (0 ≤ v.val)
    let negT (v : JInt t) : Bool := decide (v.val < 0)
    shiftRightInteger true inRangeT remT shrInt JuliaLean.base.int.zero 0
      (fun _ n => JInt.lit s n) nonnegX negT x c = .error (.methodError ">>") ∧
    (inRangeT c = true →
      shiftLeftInteger inRangeT remT shlInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX nonnegT x c = shlInt x (remT c) ∧
      shiftRightInteger false inRangeT remT shrInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX negT x c = .ok (shrInt x (remT c)) ∧
      shiftLogicalInteger inRangeT remT lshrInt JuliaLean.base.int.zero 0 x c =
        lshrInt x (remT c)) ∧
    (inRangeT c = false →
      shiftLeftInteger inRangeT remT shlInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX nonnegT x c =
          (if 0 ≤ x.val ∨ 0 ≤ c.val then JInt.lit s 0 else JInt.lit s (-1)) ∧
      shiftRightInteger false inRangeT remT shrInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX negT x c =
          .ok (if 0 ≤ x.val ∨ c.val < 0 then JInt.lit s 0 else JInt.lit s (-1)) ∧
      shiftLogicalInteger inRangeT remT lshrInt JuliaLean.base.int.zero 0 x c =
        JInt.lit s 0) ∧
    (inRangeI b = false →
      shiftLeftInteger inRangeI id shlInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX (fun n => decide (0 ≤ n)) x b =
          (if 0 ≤ x.val ∨ 0 ≤ b then JInt.lit s 0 else JInt.lit s (-1)) ∧
      shiftRightInteger false inRangeI id shrInt JuliaLean.base.int.zero 0
        (fun _ n => JInt.lit s n) nonnegX (fun n => decide (n < 0)) x b =
          .ok (if 0 ≤ x.val ∨ b < 0 then JInt.lit s 0 else JInt.lit s (-1)) ∧
      shiftLogicalInteger inRangeI id lshrInt JuliaLean.base.int.zero 0 x b =
        JInt.lit s 0)) ∧
  (∀ (s : IntTy) (x : JInt s) (c : Nat),
    let maxU := (IntTy.max .u64).toNat
    let shlU := fun (v : JInt s) (n : Nat) =>
      JuliaLean.base.int.shl_BitInteger_BitUnsigned v (JInt.wrap .u64 (Int.ofNat n))
    let lshrU := fun (v : JInt s) (n : Nat) =>
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned v (JInt.wrap .u64 (Int.ofNat n))
    shiftLeftUnsigned true maxU id shlU JuliaLean.base.int.zero x c =
      .error (.methodError "<<") ∧
    shiftLogicalUnsigned true maxU id lshrU JuliaLean.base.int.zero x c =
      .error (.methodError ">>>") ∧
    (maxU < c →
      shiftLeftUnsigned false maxU id shlU JuliaLean.base.int.zero x c =
        .ok (JInt.lit s 0) ∧
      shiftLogicalUnsigned false maxU id lshrU JuliaLean.base.int.zero x c =
        .ok (JInt.lit s 0)) ∧
    (c ≤ maxU →
      shiftLeftUnsigned false maxU id shlU JuliaLean.base.int.zero x c =
        .ok (shlU x c) ∧
      shiftLogicalUnsigned false maxU id lshrU JuliaLean.base.int.zero x c =
        .ok (lshrU x c)))

theorem shiftDirectionLaw_proven : ShiftDirectionLaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x c u shlBig shrBig shlInt shrInt lshrInt inRangeI nonnegBig negBig maxU
    refine ⟨?_, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · by_cases h : c < 0
      · have h1 : -c ≥ 0 := by omega
        have h2 : ¬(c ≥ 0) := by omega
        unfold shlInt shrInt shiftLeftInt shiftRightInt
        rw [if_pos h1, if_neg h2]
      · by_cases hz : c = 0
        · subst c
          simp [shlInt, shrInt, shiftLeftInt, shiftRightInt, shlBig, shrBig]
        · have h1 : c ≥ 0 := by omega
          have h2 : ¬(-c ≥ 0) := by omega
          unfold shlInt shrInt shiftLeftInt shiftRightInt
          rw [if_neg h2, if_pos h1]
          simp
    · rfl
    · rfl
    · intro hc
      simp [shiftLeftInteger, shiftRightInteger, shiftLogicalInteger, hc]
    · intro hc
      have hshl0 : shlInt 0 0 = 0 := by rfl
      have hshr0 : shrInt 0 0 = 0 := by rfl
      have hlshr0 : lshrInt 0 0 = 0 := by rfl
      refine ⟨?_, ?_, ?_⟩
      · by_cases hx : 0 ≤ x <;> by_cases hcv : 0 ≤ c <;>
          simp [shiftLeftInteger, hc, nonnegBig, hx, hcv, hshl0]
      · by_cases hx : 0 ≤ x <;> by_cases hcv : c < 0 <;>
          simp [shiftRightInteger, hc, nonnegBig, negBig, hx, hcv, hshr0]
      · simp [shiftLogicalInteger, hc, hlshr0]
    · intro hu
      simp [shiftLeftUnsigned, shiftLogicalUnsigned, show ¬u ≤ maxU by omega, shlBig, shrBig]
  · intro s x c toU shl shr lshr
    constructor
    · intro hne
      by_cases h : c < 0
      · have h1 : -c ≥ 0 := by omega
        have h2 : ¬(c ≥ 0) := by omega
        unfold shiftLeftInt shiftRightInt
        rw [if_pos h1, if_neg h2]
      · have h1 : c ≥ 0 := by omega
        have h2 : ¬(-c ≥ 0) := by omega
        unfold shiftLeftInt shiftRightInt
        rw [if_neg h2, if_pos h1]
        simp
    · intro hc
      have hnot : ¬(c ≥ 0) := by omega
      unfold shiftLeftInt shiftRightInt shiftLogicalInt
      rw [if_neg hnot, if_neg hnot, if_neg hnot]
      exact ⟨rfl, rfl, rfl⟩
  · intro s t x c b toU shl shr lshr shlInt shrInt lshrInt inRangeI inRangeT remT nonnegX nonnegT negT
    have hshl0 : shlInt (JuliaLean.base.int.zero x) 0 = JInt.lit s 0 := shl_zero_u64 s x
    have hshr0 : shrInt (JuliaLean.base.int.zero x) 0 = JInt.lit s 0 := shr_zero_u64 s x
    have hlshr0 : lshrInt (JuliaLean.base.int.zero x) 0 = JInt.lit s 0 := lshr_zero_u64 s x
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro hc
      simp [shiftLeftInteger, shiftRightInteger, shiftLogicalInteger, hc]
    · intro hc
      refine ⟨?_, ?_, ?_⟩
      · by_cases hx : 0 ≤ x.val <;> by_cases hcv : 0 ≤ c.val <;>
          simp [shiftLeftInteger, hc, nonnegX, nonnegT, hx, hcv, hshl0]
      · by_cases hx : 0 ≤ x.val <;> by_cases hcv : c.val < 0 <;>
          simp [shiftRightInteger, hc, nonnegX, negT, hx, hcv, hshr0]
      · simp [shiftLogicalInteger, hc, hlshr0]
    · intro hb
      refine ⟨?_, ?_, ?_⟩
      · by_cases hx : 0 ≤ x.val <;> by_cases hbv : 0 ≤ b <;>
          simp [shiftLeftInteger, hb, nonnegX, hx, hbv, hshl0]
      · by_cases hx : 0 ≤ x.val <;> by_cases hbv : b < 0 <;>
          simp [shiftRightInteger, hb, nonnegX, hx, hbv, hshr0]
      · simp [shiftLogicalInteger, hb, hlshr0]
  · intro s x c maxU shlU lshrU
    have hshlU0 : shlU (JuliaLean.base.int.zero x) 0 = JInt.lit s 0 := by
      unfold shlU JuliaLean.base.int.zero
      cases s <;> decide
    have hlshrU0 : lshrU (JuliaLean.base.int.zero x) 0 = JInt.lit s 0 := by
      unfold lshrU JuliaLean.base.int.zero
      cases s <;> decide
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hc
      simp [shiftLeftUnsigned, shiftLogicalUnsigned, show ¬c ≤ maxU by omega, hshlU0, hlshrU0]
    · intro hc
      simp [shiftLeftUnsigned, shiftLogicalUnsigned, hc]

theorem htupleAny_iff_exists_htupleToList {τ B : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → B → Truth) (x : B)
    {ts : List τ} (xs : HTuple Elem ts) (target : Truth) :
    htupleAny eq x xs target ↔ ∃ y ∈ htupleToList xs, eq y.2 x = target := by
  induction xs with
  | nil => simp [htupleAny, htupleToList]
  | cons v rest ih => simp [htupleAny, htupleToList, ih]

theorem htupleAllFalse_iff_forall_htupleToList {τ B : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → B → Truth) (x : B)
    {ts : List τ} (xs : HTuple Elem ts) :
    htupleAllFalse eq x xs ↔ ∀ y ∈ htupleToList xs, eq y.2 x = .false := by
  induction xs with
  | nil => simp [htupleAllFalse, htupleToList]
  | cons v rest ih => simp [htupleAllFalse, htupleToList, ih]

/-- The recursive membership accumulator over a heterogeneous tuple `HTuple Elem ts`
remembers `Missing` without losing a later `.true` match. -/
theorem tupleTruthCharacterization {τ B : Type} {Elem : τ → Type}
    (eq : {t : τ} → Elem t → B → Truth) (x : B)
    {ts : List τ} (xs : HTuple Elem ts) (initial : Truth) :
    (inTupleHelper eq x xs initial = .true ↔ initial = .true ∨ htupleAny eq x xs .true) ∧
    (inTupleHelper eq x xs initial = .false ↔ initial = .false ∧ htupleAllFalse eq x xs) := by
  induction xs generalizing initial with
  | nil => cases initial <;> simp [inTupleHelper, htupleAny, htupleAllFalse]
  | cons y ys ih =>
    cases hy : eq y x <;> cases initial <;>
      simp [inTupleHelper, htupleAny, htupleAllFalse, hy, Truth.or, ih]

private theorem truth_eq_of_true_false_iff {a b : Truth}
    (ht : a = .true ↔ b = .true) (hf : a = .false ↔ b = .false) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Generic iterable membership (`in(x, itr::Any) = any(==(x), itr)`), `Any32` invocation
(`in(x, itr::Any32) = invoke(in, Tuple{Any,Any}, x, itr)`), and heterogeneous tuple membership
(`in(x, itr::Tuple) = _in_tuple(x, itr)`) implement the documented three-valued `any` contract
across `.true`, `.false`, and `.missing`, passing the prebuilt `Fix2` predicate `==(x)` to `any`. -/
def MembershipDispatchSemantics : Prop :=
  (∀ (A B I : Type) (elements : I → List A)
      (any : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
        Fix 2 (A → B → Unit → Truth) B fTag xTag → I → Truth)
      (eq : A → B → Truth) (x : B) (itr : I),
    (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
        (p : Fix 2 (A → B → Unit → Truth) B fTag xTag),
      (any p itr = .true ↔ ∃ y ∈ elements itr, fixTwoCall p y () = .true) ∧
      (any p itr = .false ↔ ∀ y ∈ elements itr, fixTwoCall p y () = .false)) →
    (inAny any eq x itr = .true ↔ ∃ y ∈ elements itr, eq y x = .true) ∧
    (inAny any eq x itr = .false ↔ ∀ y ∈ elements itr, eq y x = .false) ∧
    (inAny any eq x itr = .missing ↔
      (¬∃ y ∈ elements itr, eq y x = .true) ∧ (¬∀ y ∈ elements itr, eq y x = .false)) ∧
    inAny32 (inAny any eq) x itr = inAny any eq x itr ∧
    (inAny32 (inAny any eq) x itr = .true ↔ ∃ y ∈ elements itr, eq y x = .true) ∧
    (inAny32 (inAny any eq) x itr = .false ↔ ∀ y ∈ elements itr, eq y x = .false) ∧
    (inAny32 (inAny any eq) x itr = .missing ↔
      (¬∃ y ∈ elements itr, eq y x = .true) ∧ (¬∀ y ∈ elements itr, eq y x = .false))) ∧
  (∀ (τ B : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → B → Truth)
      (x : B) (ts : List τ) (xs : HTuple Elem ts),
    (inTuple eq x xs = .true ↔ htupleAny eq x xs .true) ∧
    (inTuple eq x xs = .false ↔ htupleAllFalse eq x xs) ∧
    (inTuple eq x xs = .missing ↔
      ¬htupleAny eq x xs .true ∧ ¬htupleAllFalse eq x xs) ∧
    (∀ (anyT : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
          Fix 2 ((Σ t : τ, Elem t) → B → Unit → Truth) B fTag xTag → HTuple Elem ts → Truth)
        (eqSigma : (Σ t : τ, Elem t) → B → Truth),
      (∀ y b, eqSigma y b = eq y.2 b) →
      (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
          (p : Fix 2 ((Σ t : τ, Elem t) → B → Unit → Truth) B fTag xTag),
        (anyT p xs = .true ↔ ∃ y ∈ htupleToList xs, fixTwoCall p y () = .true) ∧
        (anyT p xs = .false ↔ ∀ y ∈ htupleToList xs, fixTwoCall p y () = .false)) →
      inAny anyT eqSigma x xs = inTuple eq x xs ∧
      inAny32 (inAny anyT eqSigma) x xs = inTuple eq x xs))

theorem membershipDispatchSemantics_proven : MembershipDispatchSemantics := by
  have htuple : ∀ (τ B : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → B → Truth)
      (x : B) (ts : List τ) (xs : HTuple Elem ts),
      (inTuple eq x xs = .true ↔ htupleAny eq x xs .true) ∧
      (inTuple eq x xs = .false ↔ htupleAllFalse eq x xs) := by
    intro τ B Elem eq x ts xs
    simpa [inTuple] using tupleTruthCharacterization eq x xs .false
  constructor
  · intro A B I elements any eq x itr hAny
    have h := hAny (fixEqual eq x)
    have htrue : inAny any eq x itr = .true ↔ ∃ y ∈ elements itr, eq y x = .true := by
      simpa [inAny, fixTwoCall, fixEqual] using h.1
    have hfalse : inAny any eq x itr = .false ↔ ∀ y ∈ elements itr, eq y x = .false := by
      simpa [inAny, fixTwoCall, fixEqual] using h.2
    have hmissing : inAny any eq x itr = .missing ↔
        (¬∃ y ∈ elements itr, eq y x = .true) ∧ (¬∀ y ∈ elements itr, eq y x = .false) := by
      cases hm : inAny any eq x itr <;> simp_all
    exact ⟨htrue, hfalse, hmissing, rfl, htrue, hfalse, hmissing⟩
  · intro τ B Elem eq x ts xs
    have ht := htuple τ B Elem eq x ts xs
    have hmiss : inTuple eq x xs = .missing ↔
        ¬htupleAny eq x xs .true ∧ ¬htupleAllFalse eq x xs := by
      cases h : inTuple eq x xs <;> simp_all
    refine ⟨ht.1, ht.2, hmiss, ?_⟩
    intro anyT eqSigma heqSigma hAnyT
    have h := hAnyT (fixEqual eqSigma x)
    have htrueA : inAny anyT eqSigma x xs = .true ↔ htupleAny eq x xs .true := by
      rw [htupleAny_iff_exists_htupleToList]
      simpa [inAny, fixTwoCall, fixEqual, heqSigma] using h.1
    have hfalseA : inAny anyT eqSigma x xs = .false ↔ htupleAllFalse eq x xs := by
      rw [htupleAllFalse_iff_forall_htupleToList]
      simpa [inAny, fixTwoCall, fixEqual, heqSigma] using h.2
    have heq : inAny anyT eqSigma x xs = inTuple eq x xs :=
      truth_eq_of_true_false_iff (htrueA.trans ht.1.symm) (hfalseA.trans ht.2.symm)
    exact ⟨heq, heq⟩

/-- Across arbitrary collections `I` satisfying the typed `any` iteration interface (including
`in(x, itr::Any32)` delegation) as well as heterogeneous tuples `HTuple Elem ts`, `∉`, `∋`, and `∌`
preserve or negate membership (`x ∉ c` iff `!(x in c)`, `c ∋ x` iff `x in c`, `c ∌ x` iff `!(x in c)`),
`notContains = notIn`, and double negation recovers `in`. -/
def MembershipWrapperSemantics : Prop :=
  (∀ (A B I : Type) (elements : I → List A)
      (any : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
        Fix 2 (A → B → Unit → Truth) B fTag xTag → I → Truth)
      (eq : A → B → Truth) (item : B) (collection : I),
    (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
        (p : Fix 2 (A → B → Unit → Truth) B fTag xTag),
      (any p collection = .true ↔ ∃ y ∈ elements collection, fixTwoCall p y () = .true) ∧
      (any p collection = .false ↔ ∀ y ∈ elements collection, fixTwoCall p y () = .false)) →
    let mem : B → I → Truth := inAny any eq
    let mem32 : B → I → Truth := inAny32 mem
    notIn Truth.not mem item collection = Truth.not (mem item collection) ∧
    notIn Truth.not mem32 item collection = Truth.not (mem32 item collection) ∧
    notIn Truth.not mem32 item collection = notIn Truth.not mem item collection ∧
    contains mem collection item = mem item collection ∧
    contains mem32 collection item = mem32 item collection ∧
    contains mem32 collection item = contains mem collection item ∧
    notContains Truth.not (contains mem) collection item = Truth.not (mem item collection) ∧
    notContains Truth.not (contains mem32) collection item = Truth.not (mem32 item collection) ∧
    notContains Truth.not (contains mem32) collection item =
      notContains Truth.not (contains mem) collection item ∧
    notContains Truth.not (contains mem) collection item =
      notIn Truth.not mem item collection ∧
    (notIn Truth.not mem item collection = .true ↔ mem item collection = .false) ∧
    (notIn Truth.not mem item collection = .false ↔ mem item collection = .true) ∧
    (contains mem collection item = .true ↔ mem item collection = .true) ∧
    (contains mem collection item = .false ↔ mem item collection = .false) ∧
    (notContains Truth.not (contains mem) collection item = .true ↔ mem item collection = .false) ∧
    (notContains Truth.not (contains mem) collection item = .false ↔ mem item collection = .true) ∧
    (notIn Truth.not mem item collection = .true ↔
      ∀ y ∈ elements collection, eq y item = .false) ∧
    (notIn Truth.not mem item collection = .false ↔
      ∃ y ∈ elements collection, eq y item = .true) ∧
    (notIn Truth.not mem item collection = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    (contains mem collection item = .true ↔
      ∃ y ∈ elements collection, eq y item = .true) ∧
    (contains mem collection item = .false ↔
      ∀ y ∈ elements collection, eq y item = .false) ∧
    (contains mem collection item = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    (notContains Truth.not (contains mem) collection item = .true ↔
      ∀ y ∈ elements collection, eq y item = .false) ∧
    (notContains Truth.not (contains mem) collection item = .false ↔
      ∃ y ∈ elements collection, eq y item = .true) ∧
    (notContains Truth.not (contains mem) collection item = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    notIn Truth.not (notIn Truth.not mem) item collection =
      mem item collection ∧
    notContains Truth.not (notContains Truth.not (contains mem)) collection item =
      mem item collection) ∧
  (∀ (A B I : Type) (elements : I → List A)
      (anyB : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
        Fix 2 (A → B → Unit → Bool) B fTag xTag → I → Bool)
      (eqB : A → B → Bool) (item : B) (collection : I),
    (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
        (p : Fix 2 (A → B → Unit → Bool) B fTag xTag),
      anyB p collection = true ↔ ∃ y ∈ elements collection, fixTwoCall p y () = true) →
    let memB : B → I → Bool := inAny anyB eqB
    let memB32 : B → I → Bool := inAny32 memB
    notIn JuliaLean.base.bool.notBool memB item collection = !(memB item collection) ∧
    notIn JuliaLean.base.bool.notBool memB32 item collection = !(memB32 item collection) ∧
    contains memB collection item = memB item collection ∧
    contains memB32 collection item = memB32 item collection ∧
    notContains JuliaLean.base.bool.notBool (contains memB) collection item = !(memB item collection) ∧
    notContains JuliaLean.base.bool.notBool (contains memB32) collection item = !(memB32 item collection) ∧
    (notIn JuliaLean.base.bool.notBool memB item collection = true ↔
      ∀ y ∈ elements collection, eqB y item = false) ∧
    (contains memB collection item = true ↔
      ∃ y ∈ elements collection, eqB y item = true) ∧
    (notContains JuliaLean.base.bool.notBool (contains memB) collection item = true ↔
      ∀ y ∈ elements collection, eqB y item = false)) ∧
  (∀ (τ B : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → B → Truth)
      (item : B) (ts : List τ) (collection : HTuple Elem ts),
    let mem : B → HTuple Elem ts → Truth := inTuple eq
    (notIn Truth.not mem item collection = .true ↔
      htupleAllFalse eq item collection) ∧
    (notIn Truth.not mem item collection = .false ↔
      htupleAny eq item collection .true) ∧
    (notIn Truth.not mem item collection = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    (contains mem collection item = .true ↔
      htupleAny eq item collection .true) ∧
    (contains mem collection item = .false ↔
      htupleAllFalse eq item collection) ∧
    (contains mem collection item = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    (notContains Truth.not (contains mem) collection item = .true ↔
      htupleAllFalse eq item collection) ∧
    (notContains Truth.not (contains mem) collection item = .false ↔
      htupleAny eq item collection .true) ∧
    (notContains Truth.not (contains mem) collection item = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    notContains Truth.not (contains mem) collection item =
      notIn Truth.not mem item collection ∧
    notIn Truth.not (notIn Truth.not mem) item collection =
      mem item collection)

theorem membershipWrapperSemantics_proven : MembershipWrapperSemantics := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B I elements any eq item collection hAny mem mem32
    have hd := membershipDispatchSemantics_proven.1 A B I elements any eq item collection hAny
    change (mem item collection = .true ↔ _) ∧
      (mem item collection = .false ↔ _) ∧
      (mem item collection = .missing ↔ _) ∧ _ at hd
    rcases hd with ⟨htrue, hfalse, hmissing, _⟩
    dsimp [notContains, contains, mem32, inAny32]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ?_, ?_, Iff.rfl, Iff.rfl, ?_, ?_,
      ?_, ?_, ?_, htrue, hfalse, hmissing, ?_, ?_, ?_, ?_, ?_⟩
    · cases hm : mem item collection <;> simp [notIn, Truth.not, hm]
    · cases hm : mem item collection <;> simp [notIn, Truth.not, hm]
    · cases hm : mem item collection <;> simp [Truth.not]
    · cases hm : mem item collection <;> simp [Truth.not]
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp [notIn, Truth.not, hm]
    · cases hm : mem item collection <;> simp [Truth.not]
  · intro A B I elements anyB eqB item collection hAnyB memB memB32
    have h := hAnyB (fixEqual eqB item)
    have htrueB : memB item collection = true ↔ ∃ y ∈ elements collection, eqB y item = true := by
      simpa [memB, inAny, fixTwoCall, fixEqual] using h
    have hfalseB : (!memB item collection = true) ↔ ∀ y ∈ elements collection, eqB y item = false := by
      cases hb : memB item collection <;> simp_all
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, htrueB, ?_⟩
    · simpa [notIn, JuliaLean.base.bool.notBool] using hfalseB
    · simpa [notContains, contains, JuliaLean.base.bool.notBool] using hfalseB
  · intro τ B Elem eq item ts collection mem
    have ht := membershipDispatchSemantics_proven.2 τ B Elem eq item ts collection
    change (mem item collection = .true ↔ _) ∧
      (mem item collection = .false ↔ _) ∧
      (mem item collection = .missing ↔ _) ∧ _ at ht
    rcases ht with ⟨htrue, hfalse, hmissing, _⟩
    dsimp [notContains, contains]
    refine ⟨?_, ?_, ?_, htrue, hfalse, hmissing, ?_, ?_, ?_, rfl, ?_⟩
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [notIn, Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp_all [Truth.not]
    · cases hm : mem item collection <;> simp [notIn, Truth.not, hm]

/-- All four unary membership helpers (`in(x)`, `∉(itr)`, `∋(x)`, `∌(x)`) record position
`2`, their distinct operator tag (`typeof(in)`, `typeof(∉)`, `typeof(∋)`, `typeof(∌)`),
and their fixed collection/item value tag, and agree with their binary counterparts across
arbitrary collections `I` satisfying the typed `any` iteration interface (including `in@1474`
`Any32` delegation) as well as heterogeneous tuples `HTuple Elem ts`. -/
def MembershipPartialSemantics : Prop :=
  (∀ (A B I : Type) (elements : I → List A)
      (any : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
        Fix 2 (A → B → Unit → Truth) B fTag xTag → I → Truth)
      (eq : A → B → Truth) (item : B) (collection : I),
    (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
        (p : Fix 2 (A → B → Unit → Truth) B fTag xTag),
      (any p collection = .true ↔ ∃ y ∈ elements collection, fixTwoCall p y () = .true) ∧
      (any p collection = .false ↔ ∀ y ∈ elements collection, fixTwoCall p y () = .false)) →
    let mem : B → I → Truth := inAny any eq
    let mem32 : B → I → Truth := inAny32 mem
    let uIn := inUnary mem collection
    let uIn32 := inUnary mem32 collection
    let uNotIn := notInUnary (notIn Truth.not mem) collection
    let uNotIn32 := notInUnary (notIn Truth.not mem32) collection
    let uContains := containsUnary (contains mem) item
    let uContains32 := containsUnary (contains mem32) item
    let uNotContains := notContainsUnary (notContains Truth.not (contains mem)) item
    let uNotContains32 := notContainsUnary (notContains Truth.not (contains mem32)) item
    let inPart := fixTwoCall uIn item ()
    let in32Part := fixTwoCall uIn32 item ()
    let notInPart := fixTwoCall uNotIn item ()
    let notIn32Part := fixTwoCall uNotIn32 item ()
    let containsPart := fixTwoCall uContains collection ()
    let contains32Part := fixTwoCall uContains32 collection ()
    let notContainsPart := fixTwoCall uNotContains collection ()
    let notContains32Part := fixTwoCall uNotContains32 collection ()
    fixPosition uIn = 2 ∧ fixFunctionTag uIn = .inOp ∧ fixValueTag uIn = collection ∧
    fixPosition uNotIn = 2 ∧ fixFunctionTag uNotIn = .notIn ∧ fixValueTag uNotIn = collection ∧
    fixPosition uContains = 2 ∧ fixFunctionTag uContains = .contains ∧ fixValueTag uContains = item ∧
    fixPosition uNotContains = 2 ∧ fixFunctionTag uNotContains = .notContains ∧
    fixValueTag uNotContains = item ∧
    inPart = mem item collection ∧
    in32Part = mem32 item collection ∧
    in32Part = inPart ∧
    containsPart = contains mem collection item ∧
    containsPart = mem item collection ∧
    contains32Part = contains mem32 collection item ∧
    contains32Part = containsPart ∧
    notInPart = notIn Truth.not mem item collection ∧
    notInPart = Truth.not (mem item collection) ∧
    notIn32Part = notIn Truth.not mem32 item collection ∧
    notIn32Part = notInPart ∧
    notContainsPart = notContains Truth.not (contains mem) collection item ∧
    notContainsPart = notIn Truth.not mem item collection ∧
    notContainsPart = Truth.not (mem item collection) ∧
    notContains32Part = notContains Truth.not (contains mem32) collection item ∧
    notContains32Part = notContainsPart ∧
    (inPart = .true ↔ ∃ y ∈ elements collection, eq y item = .true) ∧
    (inPart = .false ↔ ∀ y ∈ elements collection, eq y item = .false) ∧
    (inPart = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    (containsPart = .true ↔ ∃ y ∈ elements collection, eq y item = .true) ∧
    (containsPart = .false ↔ ∀ y ∈ elements collection, eq y item = .false) ∧
    (containsPart = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    (notInPart = .true ↔ ∀ y ∈ elements collection, eq y item = .false) ∧
    (notInPart = .false ↔ ∃ y ∈ elements collection, eq y item = .true) ∧
    (notInPart = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false)) ∧
    (notContainsPart = .true ↔ ∀ y ∈ elements collection, eq y item = .false) ∧
    (notContainsPart = .false ↔ ∃ y ∈ elements collection, eq y item = .true) ∧
    (notContainsPart = .missing ↔
      (¬∃ y ∈ elements collection, eq y item = .true) ∧
      (¬∀ y ∈ elements collection, eq y item = .false))) ∧
  (∀ (A B I : Type) (elements : I → List A)
      (anyB : {FT XT : Type} → {fTag : FT} → {xTag : XT} →
        Fix 2 (A → B → Unit → Bool) B fTag xTag → I → Bool)
      (eqB : A → B → Bool) (item : B) (collection : I),
    (∀ {FT XT : Type} {fTag : FT} {xTag : XT}
        (p : Fix 2 (A → B → Unit → Bool) B fTag xTag),
      anyB p collection = true ↔ ∃ y ∈ elements collection, fixTwoCall p y () = true) →
    let memB : B → I → Bool := inAny anyB eqB
    let memB32 : B → I → Bool := inAny32 memB
    fixTwoCall (inUnary memB collection) item () = memB item collection ∧
    fixTwoCall (inUnary memB32 collection) item () = memB32 item collection ∧
    fixTwoCall (notInUnary (notIn JuliaLean.base.bool.notBool memB) collection) item () =
      !(memB item collection) ∧
    fixTwoCall (notInUnary (notIn JuliaLean.base.bool.notBool memB32) collection) item () =
      !(memB32 item collection) ∧
    fixTwoCall (containsUnary (contains memB) item) collection () = memB item collection ∧
    fixTwoCall (containsUnary (contains memB32) item) collection () = memB32 item collection ∧
    fixTwoCall (notContainsUnary (notContains JuliaLean.base.bool.notBool (contains memB)) item) collection () =
      !(memB item collection) ∧
    fixTwoCall (notContainsUnary (notContains JuliaLean.base.bool.notBool (contains memB32)) item) collection () =
      !(memB32 item collection) ∧
    (fixTwoCall (inUnary memB collection) item () = true ↔
      ∃ y ∈ elements collection, eqB y item = true) ∧
    (fixTwoCall (notInUnary (notIn JuliaLean.base.bool.notBool memB) collection) item () = true ↔
      ∀ y ∈ elements collection, eqB y item = false) ∧
    (fixTwoCall (containsUnary (contains memB) item) collection () = true ↔
      ∃ y ∈ elements collection, eqB y item = true) ∧
    (fixTwoCall (notContainsUnary (notContains JuliaLean.base.bool.notBool (contains memB)) item) collection () = true ↔
      ∀ y ∈ elements collection, eqB y item = false)) ∧
  (∀ (τ B : Type) (Elem : τ → Type) (eq : {t : τ} → Elem t → B → Truth)
      (item : B) (ts : List τ) (collection : HTuple Elem ts),
    let mem : B → HTuple Elem ts → Truth := inTuple eq
    let uIn := inUnary mem collection
    let uNotIn := notInUnary (notIn Truth.not mem) collection
    let uContains := containsUnary (contains mem) item
    let uNotContains := notContainsUnary (notContains Truth.not (contains mem)) item
    let inPart := fixTwoCall uIn item ()
    let notInPart := fixTwoCall uNotIn item ()
    let containsPart := fixTwoCall uContains collection ()
    let notContainsPart := fixTwoCall uNotContains collection ()
    fixPosition uIn = 2 ∧ fixFunctionTag uIn = .inOp ∧ fixValueTag uIn = collection ∧
    fixPosition uNotIn = 2 ∧ fixFunctionTag uNotIn = .notIn ∧ fixValueTag uNotIn = collection ∧
    fixPosition uContains = 2 ∧ fixFunctionTag uContains = .contains ∧ fixValueTag uContains = item ∧
    fixPosition uNotContains = 2 ∧ fixFunctionTag uNotContains = .notContains ∧
    fixValueTag uNotContains = item ∧
    inPart = mem item collection ∧
    containsPart = mem item collection ∧
    notInPart = notIn Truth.not mem item collection ∧
    notContainsPart = notIn Truth.not mem item collection ∧
    (inPart = .true ↔ htupleAny eq item collection .true) ∧
    (inPart = .false ↔ htupleAllFalse eq item collection) ∧
    (inPart = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    (containsPart = .true ↔ htupleAny eq item collection .true) ∧
    (containsPart = .false ↔ htupleAllFalse eq item collection) ∧
    (containsPart = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    (notInPart = .true ↔ htupleAllFalse eq item collection) ∧
    (notInPart = .false ↔ htupleAny eq item collection .true) ∧
    (notInPart = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)) ∧
    (notContainsPart = .true ↔ htupleAllFalse eq item collection) ∧
    (notContainsPart = .false ↔ htupleAny eq item collection .true) ∧
    (notContainsPart = .missing ↔
      (¬htupleAny eq item collection .true ∧ ¬htupleAllFalse eq item collection)))

theorem membershipPartialSemantics_proven : MembershipPartialSemantics := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B I elements any eq item collection hAny
      mem mem32 uIn uIn32 uNotIn uNotIn32 uContains uContains32 uNotContains uNotContains32
      inPart in32Part notInPart notIn32Part containsPart contains32Part
      notContainsPart notContains32Part
    have hw := membershipWrapperSemantics_proven.1 A B I elements any eq item collection hAny
    rcases hw with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hnT, hnF, hnM, hcT, hcF, hcM, hncT, hncF, hncM, _, _⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hcT, hcF, hcM, hcT, hcF, hcM, hnT, hnF, hnM, hncT, hncF, hncM⟩
  · intro A B I elements anyB eqB item collection hAnyB memB memB32
    have hw := membershipWrapperSemantics_proven.2.1 A B I elements anyB eqB item collection hAnyB
    rcases hw with ⟨_, _, _, _, _, _, hnB, hcB, hncB⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcB, hnB, hcB, hncB⟩
  · intro τ B Elem eq item ts collection mem uIn uNotIn uContains uNotContains
      inPart notInPart containsPart notContainsPart
    have hw := membershipWrapperSemantics_proven.2.2 τ B Elem eq item ts collection
    rcases hw with ⟨hnT, hnF, hnM, hcT, hcF, hcM, hncT, hncF, hncM, _, _⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, hcT, hcF, hcM, hcT, hcF, hcM, hnT, hnF, hnM, hncT, hncF, hncM⟩

/-! ## Method -> property table

method@Julia-line | registry id
supertype@86 | operators-supertype-access
getproperty@95 | operators-supertype-access
supertype@102 | operators-unionall-supertype-variable
supertype@104 | operators-supertype-special-cases
supertype@105 | operators-supertype-special-cases
isequal@196 | operators-isequal-fallback-symmetry
signequal@198 | Nothing to promise (below)
signless@199 | Nothing to promise (below)
isequal@201 | operators-float-nan-order
isequal@202 | promotion-mixed-isless-total-small
isequal@203 | promotion-mixed-isless-total-small
isless@240 | operators-float-nan-order
isless@241 | promotion-mixed-isless-total-small
isless@242 | promotion-mixed-isless-total-small
isless@248 | operators-pair-isless-transitive
isgreater@295 | operators-unordered-order
isunordered@309 | operators-unordered-order
isunordered@310 | operators-unordered-order
isunordered@311 | operators-unordered-order
==@313 | operators-type-equality
==@314 | operators-type-equality
==@315 | operators-type-equality
!=@338 | operators-comparison-fallbacks
<@417 | operators-comparison-fallbacks
>@443 | operators-comparison-fallbacks
<=@467 | operators-comparison-fallbacks
>=@499 | operators-comparison-fallbacks
isless@505 | operators-isless-real-transitive
cmp@526 | operators-cmp-result-range
cmp@534 | operators-cmp-result-range
cmp@537 | operators-cmp-result-range
max@555 | operators-min-max-isless, operators-minmax-coherent
min@573 | operators-min-max-isless, operators-minmax-coherent
minmax@588 | operators-minmax-coherent
identity@605 | operators-identity-extensional
+@607 | Nothing to promise (below)
*@608 | Nothing to promise (below)
&@609 | Nothing to promise (below)
|@610 | Nothing to promise (below)
xor@611 | Nothing to promise (below)
afoldl@622 | operators-nary-fold-law
afoldl@623 | operators-nary-fold-law
+@671 | operators-nary-fold-law
+%@671 | operators-nary-fold-law
*@671 | operators-nary-fold-law
*%@671 | operators-nary-fold-law
&@671 | operators-nary-fold-law
|@671 | operators-nary-fold-law
xor@671 | operators-nary-fold-law
min@671 | operators-nary-fold-law
max@671 | operators-nary-fold-law
kron@671 | operators-nary-fold-law
\@709 | operators-left-division-scalar
<<@735 | operators-shift-direction
<<@741 | operators-shift-direction
<<@748 | operators-shift-direction
>>@780 | operators-shift-direction
>>@789 | operators-shift-direction
>>>@818 | operators-shift-direction
>>>@822 | operators-shift-direction
>>>@829 | operators-shift-direction
mod1@914 | operators-mod1-zero-remainder
cldmod1@943 | operators-division-pair-components
fldmod1@952 | operators-division-pair-components
widen@975 | hashops-widen-unsigned-sub
widen@976 | Nothing to promise (below)
widen@977 | Nothing to promise (below)
|>@1001 | operators-pipe-composition
_stable_typeof@1003 | Nothing to promise (below)
_stable_typeof@1004 | Nothing to promise (below)
Returns{V}@1031 | operators-returns-call
Returns@1032 | operators-returns-call
(obj::Returns)@1035 | operators-returns-call
ComposedFunction{O,I}@1121 | operators-composition-application
ComposedFunction@1122 | operators-composition-application
(c::ComposedFunction)@1125 | operators-composed-call, operators-composition-application
unwrap_composed@1126 | operators-composition-unwrapping
unwrap_composed@1127 | operators-composition-unwrapping
call_composed@1128 | operators-composed-call
call_composed@1129 | operators-composed-call
(::Constructor{F})@1132 | operators-composition-application
maybeconstructor@1133 | operators-composition-unwrapping, operators-composition-application
maybeconstructor@1134 | operators-composition-unwrapping
∘@1136 | operators-nary-composition-tail
∘@1137 | operators-composition-application
∘@1138 | operators-nary-composition-tail
show@1140 | operators-adapter-display
show@1147 | operators-adapter-display
_showcomposed@1152 | operators-adapter-display
_showcomposed@1154 | operators-adapter-display
_showcomposed@1156 | operators-adapter-display
_showcomposed@1158 | operators-adapter-display
!@1182 | operators-negation-composition
!@1183 | operators-double-negation-composition
Fix{N}@1206 | operators-fix-call-position, operators-fix-constructor-errors
(f::Fix{N})@1216 | operators-fix-call-position, operators-fix-constructor-errors
(f::Fix{1})@1223 | operators-fix-special-calls
(f::Fix{2})@1224 | operators-fix-special-calls
Base.show@1226 | operators-adapter-display
isequal@1259 | operators-fix2-argument-order
==@1270 | operators-fix2-argument-order
!=@1283 | operators-fix2-argument-order
>=@1296 | operators-fix2-argument-order
<=@1309 | operators-fix2-argument-order
>@1322 | operators-fix2-argument-order
<@1335 | operators-fix2-argument-order
splat@1366 | operators-splat-roundtrip
Splat@1384 | operators-splat-roundtrip
(s::Splat)@1386 | operators-splat-roundtrip
show@1387 | operators-adapter-display
unsplat@1415 | operators-unsplat-call
unsplat@1416 | operators-splat-roundtrip
splat@1417 | operators-splat-composed-tuple
tap@1438 | operators-tap-returns-input
in@1453 | operators-membership-partials
in@1455 | operators-membership-dispatch, operators-membership-wrappers, operators-membership-partials
in@1459 | operators-tuple-membership-match, operators-membership-dispatch
_in_tuple@1463 | operators-tuple-membership-match, operators-membership-dispatch
in@1474 | operators-membership-dispatch, operators-membership-wrappers, operators-membership-partials
∉@1477 | operators-membership-wrappers, operators-membership-partials
∉@1478 | operators-membership-partials
∋@1486 | operators-membership-wrappers, operators-membership-partials
∋@1497 | operators-membership-partials
∌@1499 | operators-membership-wrappers, operators-membership-partials
∌@1500 | operators-membership-partials

Nothing to promise:
signequal@198: Internal sign-bit comparison helper; its consumers specify the observable equality behavior.
signless@199: Internal sign-bit ordering helper; its consumers specify the observable total order.
+@607: Unary arithmetic forwarding returns the argument without performing a binary operation.
*@608: Unary arithmetic forwarding returns the argument without performing a binary operation.
&@609: Unary bitwise forwarding returns the argument without performing a binary operation.
|@610: Unary bitwise forwarding returns the argument without performing a binary operation.
xor@611: Unary bitwise forwarding returns the argument without performing a binary operation.
widen@976: Unsupported type fallback only delegates MethodError construction.
widen@977: Uninhabited Union{} type fallback, with any trailing arguments, only delegates MethodError construction.
_stable_typeof@1003: Internal typeof forwarding used to select wrapper type parameters.
_stable_typeof@1004: Internal type-tag selection for defined versus free type variables.
-/

end JuliaLean.Proofs.base.operators

namespace JuliaLean.Proofs.base.operators.Archive20261101

open JuliaLean JuliaLean.base.operators JuliaLean.Proofs.base.operators

/-- Parenthesizing a composition either way gives the same observable result or error for every callable and argument list.
Julia source: base/operators.jl:1125-1129,1137-1138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:1039-1057; doc/src/manual/functions.md:1000-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
The subject is the public composition call; no property is registered solely for the internal unwrap_composed helper.
-/
def CompositionAssociativePublic : Prop :=
  ∀ (F T V σ : Type) (m : CallMethods F T V σ) (f g h : Callee F T)
    (args : List V) (kw : List (σ × V)),
    args.length < (2 : Nat) ^ 62 → kw.length < (2 : Nat) ^ 62 →
    composedCall m (composeTwo (.composed (composeTwo f g)) h) args kw =
      composedCall m (composeTwo f (.composed (composeTwo g h))) args kw

end JuliaLean.Proofs.base.operators.Archive20261101

namespace JuliaLean.ChatGPT.Batch6.Group2

/-- Parenthesizing a composition either way has the same public call behavior. -/
theorem OperatorsCompositionUnwrapping_proven :
    JuliaLean.Proofs.base.operators.Archive20261101.CompositionAssociativePublic := by
  intro F T V σ m f g h args kw _ _
  simp [JuliaLean.base.operators.composedCall, JuliaLean.base.operators.composeTwo,
    JuliaLean.base.operators.composed, JuliaLean.base.operators.unwrapComposed,
    JuliaLean.base.operators.unwrapComposedAny, List.append_assoc]

end JuliaLean.ChatGPT.Batch6.Group2

namespace JuliaLean.Proofs.base.operators

open JuliaLean.Registry

def entries : List Entry := [
  { id := "operators-min-max-isless", juliaFile := "base/operators.jl",
    juliaFns := ["min(x, y)", "max(x, y)"],
    statement := "For any type with typed isless and isequal methods satisfying Julia's documented total-order law, generic min and max return an input; no input is less than the minimum, and the maximum is not less than either input. When isequal(x, y) is true, min returns x and max returns y.",
    source := "isless docstring base/operators.jl:208-214; min/max docstrings:539-573", status := .proven,
    prop := ``MinMaxIsless, thm := some ``minMaxIsless_proven },
  { id := "promotion-mixed-isless-total-small", juliaFile := "base/operators.jl",
    juliaFns := ["isless(::AbstractFloat,::Real)", "isless(::Real,::AbstractFloat)", "isequal(::AbstractFloat,::Real)", "isequal(::Real,::AbstractFloat)"],
    statement := "Mixed Float/Real comparisons form a strict total order including NaNs and signed zero under the primitive numeric comparison and sign laws; concrete IEEE float and at-most-32-bit integer comparisons satisfy these laws.",
    source := "isless and isequal docstrings, base/operators.jl:196-214", status := .proven,
    prop := ``MixedIslessTotalSmall, thm := some ``mixedIslessTotalSmall_proven },
  { id := "hashops-widen-unsigned-sub", juliaFile := "base/operators.jl",
    juliaFns := ["widen(x::T) where {T}"],
    statement := "After widening any two fixed-width integers of one type, their sum and difference equal the mathematical results without overflow or precision loss.",
    source := "widen docstring base/operators.jl:955-964", status := .refuted,
    prop := ``WidenNoLoss, thm := some ``widenNoLoss_refuted,
    issue := "none found (queries: widen UInt; widen unsigned; widen subtraction; guaranteed not to overflow widen)",
    notes := "widen(UInt8(0)) - widen(typemax(UInt8)) is UInt16(65281), not -255, on both versions. The implementation may be intended; then the docstring overpromises." },
  { id := "operators-cmp-result-range", juliaFile := "base/operators.jl",
    juliaFns := ["cmp(x, y)", "cmp(<, x, y)", "cmp(x::Integer, y::Integer)"],
    statement := "All three cmp methods return a comparison sign on every input domain; on mixed-width integers the signs denote exact mathematical less-than, equality, and greater-than.",
    source := "cmp docstring, base/operators.jl:507-511", status := .proven,
    prop := ``CmpResultRange, thm := some ``cmpResultRange_proven },
  { id := "operators-tuple-membership-match", juliaFile := "base/operators.jl",
    juliaFns := ["in(x, itr::Tuple)", "_in_tuple"],
    statement := "Tuple membership returns true when any element compares equal, even after an earlier comparison returns missing.",
    source := "in docstring, base/operators.jl:1503-1516", status := .proven,
    prop := ``TupleMembershipMatch, thm := some ``tupleMembershipMatch_proven },
  { id := "operators-float-nan-order", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x::AbstractFloat, y::AbstractFloat)", "isless(x::AbstractFloat, y::AbstractFloat)"],
    statement := "On non-IEEE AbstractFloat types with typed <, ==, isnan, and signbit methods satisfying their documented primitive order and sign laws, generic isless is a strict total order with NaNs last; generic isequal is an equivalence relation, identifies all NaNs, separates negative and positive zero, and holds exactly when neither value is less than the other.",
    source := "base/operators.jl:201,208-218,240", status := .proven,
    prop := ``GenericAbstractFloatNaNSemantics, thm := some ``genericAbstractFloatNaNSemantics_proven },
  { id := "operators-unordered-order", juliaFile := "base/operators.jl",
    juliaFns := ["isgreater(x, y)", "isunordered(_)", "isunordered(x::AbstractFloat)", "isunordered(::Missing)"],
    statement := "Descending comparison preserves the generic comparison partition, uses exact mixed-width integer ordering, and invokes actual default, Float, and Missing unordered methods.",
    source := "base/operators.jl:251-311", status := .proven,
    prop := ``UnorderedContract, thm := some ``unorderedContract_proven },
  { id := "operators-minmax-coherent", juliaFile := "base/operators.jl",
    juliaFns := ["minmax(x, y)", "min(x, y)", "max(x, y)"],
    statement := "For any type with typed isless and isequal methods satisfying Julia's documented total-order law, generic minmax returns the generic min and max values, each selected value is an input, and the pair is in isless or isequal order.",
    source := "isless docstring base/operators.jl:208-214; min/max/minmax:539-588", status := .proven,
    prop := ``MinmaxCoherent, thm := some ``minmaxCoherent_proven },
  { id := "operators-comparison-fallbacks", juliaFile := "base/operators.jl",
    juliaFns := ["isless(x::Real, y::Real)", "!=(x, y)", "<(x, y)", ">(x, y)", "<=(x, y)", ">=(x, y)"],
    statement := "Comparison fallbacks denote exact mixed-width integer value order, give an equivalence relation for equality, preserve transitivity, and satisfy the total-order complement laws for generic lawful comparisons.",
    source := "base/operators.jl:317-499", status := .proven,
    prop := ``ComparisonContract, thm := some ``comparisonContract_proven },
  { id := "operators-isequal-fallback-symmetry", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x, y)"],
    statement := "Comparison fallbacks denote exact mixed-width integer value order, give an equivalence relation for equality, preserve transitivity, and satisfy the total-order complement laws for generic lawful comparisons.",
    source := "isequal docstring and fallback, base/operators.jl:144-196", status := .proven,
    prop := ``ComparisonContract, thm := some ``comparisonContract_proven },
  { id := "operators-isless-real-transitive", juliaFile := "base/operators.jl",
    juliaFns := ["isless(x::Real, y::Real)"],
    statement := "For every triple of Real types whose < and == compare exact values in a linear order, and for the source int.jl comparisons on every fixed-width integer width, exactly one of isless(x, y), isless(y, x) and isequal(x, y) holds and isless is transitive.",
    source := "isless docstring and fallback, base/operators.jl:206-225,505", status := .proven,
    prop := ``IslessRealContract, thm := some ``islessRealContract_proven },
  { id := "operators-type-equality", juliaFile := "base/operators.jl",
    juliaFns := ["==(T::Type, S::Type)", "==(T::TypeVar, S::Type)", "==(T::Type, S::TypeVar)"],
    statement := "For any subtype relation satisfying reflexivity and transitivity, T == S holds if and only if T <: S and S <: T, forms an equivalence relation, and returns false between Type and TypeVar.",
    source := "base/operators.jl:109-142,313-315; src/subtype.c:4110-4190", status := .proven,
    prop := ``TypeEqualitySemantics, thm := some ``typeEqualitySemantics_proven },
  { id := "operators-supertype-access", juliaFile := "base/operators.jl",
    juliaFns := ["supertype(T::DataType)", "getproperty(T::DataType, s::Symbol)"],
    statement := "Direct-supertype reads materialize the runtime cache first, agree with super-field property access, and are unchanged by repeated idempotent materialization.",
    source := "base/operators.jl:67-101", status := .proven,
    prop := ``SupertypeAccessAgreement, thm := some ``supertypeAccessAgreement_proven },
  { id := "operators-supertype-special-cases", juliaFile := "base/operators.jl",
    juliaFns := ["supertype(::TypeEq)", "supertype(T::Core.TypeEgal)"],
    statement := "The parent of TypeEgal{T} is Type{T}, distinct for distinct T, and the parent of every Type{T} is Core's fixed AnyType kind, which is neither Any nor a Type{S}.",
    source := "base/operators.jl:103-105", status := .proven,
    prop := ``SupertypeSpecialCases, thm := some ``supertypeSpecialCases_proven },
  { id := "operators-unionall-supertype-variable", juliaFile := "base/operators.jl",
    juliaFns := ["supertype(T::UnionAll)"],
    statement := "The UnionAll parent retains its binder and computes the direct parent of its body through the actual cache-materializing DataType method.",
    source := "base/operators.jl:102", status := .proven,
    prop := ``UnionAllSupertypePreservesVariable, thm := some ``unionAllSupertypePreservesVariable_proven },
  { id := "operators-pair-isless-transitive", juliaFile := "base/operators.jl",
    juliaFns := ["isless(a::Tuple{BitInteger,BitInteger}, b::Tuple{BitInteger,BitInteger})"],
    statement := "Optimized pairs implement mathematical lexicographic order and are transitive across all combinations of integer widths, without assumed element comparison laws.",
    source := "base/operators.jl:206-214,248-249", status := .proven,
    prop := ``PairIslessTransitive, thm := some ``pairIslessTransitive_proven },
  { id := "operators-nary-fold-law", juliaFile := "base/operators.jl",
    juliaFns := ["afoldl(op, a)", "afoldl(op, a, bs...)", "+(a,b,c,xs...)", "+%(a,b,c,xs...)", "*(a,b,c,xs...)", "*%(a,b,c,xs...)", "&(a,b,c,xs...)", "|(a,b,c,xs...)", "xor(a,b,c,xs...)", "min(a,b,c,xs...)", "max(a,b,c,xs...)", "kron(a,b,c,xs...)"],
    statement := "The n-ary operator fold preserves left-to-right order when its argument list is split into two parts.",
    source := "base/operators.jl:617-671", status := .proven,
    prop := ``NaryOperatorsContract, thm := some ``naryOperatorsContract_proven },
  { id := "operators-identity-extensional", juliaFile := "base/operators.jl",
    juliaFns := ["identity(x)"],
    statement := "Repeating identity in pipelines leaves the value unchanged, including past the unrolled fold prefix, and splitting a pipeline preserves left-to-right evaluation.",
    source := "base/operators.jl:592-605", status := .proven,
    prop := ``IdentityPipeLaws, thm := some ``identityPipeLaws_proven },
  { id := "operators-pipe-composition", juliaFile := "base/operators.jl",
    juliaFns := ["|>(x, f)"],
    statement := "Repeating identity in pipelines leaves the value unchanged, including past the unrolled fold prefix, and splitting a pipeline preserves left-to-right evaluation.",
    source := "base/operators.jl:979-1001", status := .proven,
    prop := ``IdentityPipeLaws, thm := some ``identityPipeLaws_proven },
  { id := "operators-returns-call", juliaFile := "base/operators.jl",
    juliaFns := ["Returns{V}(value)", "Returns(value)", "(obj::Returns)(args...; kw...)"],
    statement := "Returns(x) returns x for every positional and keyword argument list, stores x and _stable_typeof(x), identifies equal stored values, Returns{V}(raw) converts arbitrary arguments to field type V (storing the converted value and returning it on every call or propagating the conversion error, including concrete JInt.convert), and Returns ∘ g returns the stored value after any callable g succeeds while propagating g's error.",
    source := "base/operators.jl:1006-1035", status := .proven,
    prop := ``ReturnsCallContract, thm := some ``returnsCallContract_proven },
  { id := "operators-fix2-argument-order", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x)", "==(x)", "!=(x)", ">=(x)", "<=(x)", ">(x)", "<(x)"],
    statement := "All seven unary comparison constructors, invoked through the source Fix{2} call method, denote mathematical comparisons across different integer widths and signedness.",
    source := "base/operators.jl:1250-1335", status := .proven,
    prop := ``UnaryComparisonContract, thm := some ``unaryComparisonContract_proven },
  { id := "operators-fix-call-position", juliaFile := "base/operators.jl",
    juliaFns := ["Fix{N}(f, x)", "(f::Fix{N})(args...; kws...)"],
    statement := "For Int64-representable tuple lengths and value-preserving element conversion, successful Fix construction stores its position and inserts the argument at exactly that position, with source tuple slicing and arbitrary keywords.",
    source := "base/operators.jl:1185-1220", status := .proven,
    prop := ``FixCallPosition, thm := some ``fixCallPosition_proven },
  { id := "operators-fix-special-calls", juliaFile := "base/operators.jl",
    juliaFns := ["(f::Fix{1})(arg; kws...)", "(f::Fix{2})(arg; kws...)"],
    statement := "The specialized Fix{1} and Fix{2} methods agree with general tuple insertion and support heterogeneous first and second argument types.",
    source := "base/operators.jl:1223-1224", status := .proven,
    prop := ``FixOneTwoCallPlacement, thm := some ``fixOneTwoCallPlacement_proven },
  { id := "operators-fix-constructor-errors", juliaFile := "base/operators.jl",
    juliaFns := ["Fix{N}(f, x)", "(f::Fix{N})(args...; kws...)"],
    statement := "Nested Fix construction and invocation throw ArgumentError if and only if a type parameter is not Int, a position is below 1, or the outer or post-insertion inner argument count is less than N-1; Fix{1}(Fix{2}(f, x1), x2) fixes arguments 1 and 2 even on empty args, while Fix{2}(Fix{1}(f, x1), x2) rejects empty args and fixes arguments 1 and 3.",
    source := "base/operators.jl:1185-1220", status := .proven,
    prop := ``FixNestingAndErrorContract, thm := some ``fixNestingAndErrorContract_proven },
  { id := "operators-splat-roundtrip", juliaFile := "base/operators.jl",
    juliaFns := ["splat(f)", "Splat(f)", "(s::Splat)(args)", "unsplat(s::Splat)"],
    statement := "Splat and unsplat are inverse adapters, Splat(f)(args) calls f(args...), and unsplat(f)(args...) called through the source ComposedFunction call method passes the tuple of its arguments to f.",
    source := "base/operators.jl:1337-1386,1390-1416", status := .proven,
    prop := ``SplatFoldContract, thm := some ``splatFoldContract_proven },
  { id := "operators-unsplat-call", juliaFile := "base/operators.jl",
    juliaFns := ["unsplat(f)"],
    statement := "Splat and unsplat are inverse adapters, Splat(f)(args) calls f(args...), and unsplat(f)(args...) called through the source ComposedFunction call method passes the tuple of its arguments to f.",
    source := "base/operators.jl:1390-1415", status := .proven,
    prop := ``SplatFoldContract, thm := some ``splatFoldContract_proven },
  { id := "operators-splat-composed-tuple", juliaFile := "base/operators.jl",
    juliaFns := ["splat(f::ComposedFunction{<:Any,typeof(tuple)})"],
    statement := "Splat and unsplat are inverse adapters, Splat(f)(args) calls f(args...), and unsplat(f)(args...) called through the source ComposedFunction call method passes the tuple of its arguments to f.",
    source := "base/operators.jl:1417", status := .proven,
    prop := ``SplatFoldContract, thm := some ``splatFoldContract_proven },
  { id := "operators-tap-returns-input", juliaFile := "base/operators.jl",
    juliaFns := ["tap(f)"],
    statement := "Tap performs exactly the callback state transition, returns its original input, and propagates callback failures.",
    source := "base/operators.jl:1419-1438", status := .proven,
    prop := ``TapReturnsInput, thm := some ``tapReturnsInput_proven },
  { id := "operators-mod1-zero-remainder", juliaFile := "base/operators.jl",
    juliaFns := ["mod1(x::T, y::T) where {T<:Real}"],
    statement := "For every Real implementation satisfying the modulus and zero-test interface, mod1 replaces a zero remainder by the divisor and lies in the promised half-open interval.",
    source := "base/operators.jl:888-914", status := .proven,
    prop := ``Mod1ZeroRemainder, thm := some ``mod1ZeroRemainder_proven },
  { id := "operators-division-pair-components", juliaFile := "base/operators.jl",
    juliaFns := ["cldmod1(x, y)", "fldmod1(x, y)", "mod1(x::T, y::T) where {T<:Real}"],
    statement := "Calling the source mod1 method, cldmod1 and fldmod1 preserve the integer reconstruction x == (q - 1) * y + mod1(x, y) and half-open remainder bounds, and agree whenever fld1 and cld agree.",
    source := "base/operators.jl:914-952", status := .proven,
    prop := ``DivisionPairContract, thm := some ``divisionPairContract_proven },
  { id := "operators-shift-direction", juliaFile := "base/operators.jl",
    juliaFns := ["<<(x::Integer,c::Integer)", "<<(x::Integer,c::Unsigned)", "<<(x::Integer,c::Int)",
      ">>(x::Integer,c::Integer)", ">>(x::Integer,c::Int)", ">>>(x::Integer,c::Integer)",
      ">>>(x::Integer,c::Unsigned)", ">>>(x::Integer,c::Int)"],
    statement := "Signed shifts reverse direction on arbitrary Integer values; unsigned boundary cases, unsupported UInt counts, and extreme generic logical shifts preserve their specified outcomes.",
    source := "base/operators.jl:715-829", status := .proven,
    prop := ``ShiftDirectionLaw, thm := some ``shiftDirectionLaw_proven },
  { id := "operators-left-division-scalar", juliaFile := "base/operators.jl",
    juliaFns := ["\\(x, y)"],
    statement := "With identity adjoint, left division reverses the operands of the supplied division.",
    source := "base/operators.jl:682-709", status := .proven,
    prop := ``LeftDivisionScalarCase, thm := some ``leftDivisionScalarCase_proven },
  { id := "operators-composition-application", juliaFile := "base/operators.jl",
    juliaFns := ["∘(f, g)", "ComposedFunction{O,I}(outer, inner)", "ComposedFunction(outer, inner)",
      "(c::ComposedFunction)(x...; kw...)", "(::Constructor{F})(args...; kw...)",
      "maybeconstructor(::Type{F})"],
    statement := "For all callables f and g, including type objects and nested compositions, calling f ∘ g through the source call method equals f(g(args...; kw...)): g gets every argument, f only g's result, and g's error propagates first; a type outer is called through its Constructor, and ComposedFunction{O,I}(outer, inner) converts arbitrary arguments to O and I in outer-then-inner order, propagating conversion errors or behaving as f ∘ g when both succeed.",
    source := "base/operators.jl:1039-1138", status := .proven,
    prop := ``CompositionApplication, thm := some ``compositionApplication_proven },
  { id := "operators-composed-call", juliaFile := "base/operators.jl",
    juliaFns := ["(c::ComposedFunction)(x...; kw...)", "call_composed(fs, x, kw)",
      "call_composed(fs::Tuple{Any}, x, kw)"],
    statement := "The source call_composed is the right fold over the flattened callables: the innermost gets every positional and keyword argument, each outer one only the previous result and no keywords, so calling any ComposedFunction c equals c.outer(c.inner(x...; kw...)).",
    source := "base/operators.jl:1125-1129", status := .proven,
    prop := ``ComposedCallFold, thm := some ``composedCallFold_proven },
  { id := "operators-nary-composition-tail", juliaFile := "base/operators.jl",
    juliaFns := ["∘(f, g, h...)", "∘(f)"],
    statement := "∘(f) is f, and ∘(f₁, …, fₙ) for n ≥ 2 is a ComposedFunction that flattens to the concatenated flattenings of its arguments and, when called, runs fₙ on every argument and then fₙ₋₁, …, f₁ on the previous result.",
    source := "base/operators.jl:1039-1085,1136-1138", status := .proven,
    prop := ``NaryComposition, thm := some ``naryComposition_proven },
  { id := "operators-negation-composition", juliaFile := "base/operators.jl",
    juliaFns := ["!(f::Function)"],
    statement := "For every callable predicate p and a ! whose Bool method is notBool, calling !p through the source ComposedFunction call method returns the negation of p's result and propagates p's errors; !(!p) is p and returns p's results.",
    source := "base/operators.jl:1160-1182", status := .proven,
    prop := ``NegationComposition, thm := some ``negationComposition_proven },
  { id := "operators-double-negation-composition", juliaFile := "base/operators.jl",
    juliaFns := ["!(f::ComposedFunction{typeof(!)})"],
    statement := "For every callable predicate p and a ! whose Bool method is notBool, calling !p through the source ComposedFunction call method returns the negation of p's result and propagates p's errors; !(!p) is p and returns p's results.",
    source := "base/operators.jl:1182-1183", status := .proven,
    prop := ``NegationComposition, thm := some ``negationComposition_proven },
  { id := "operators-membership-dispatch", juliaFile := "base/operators.jl",
    juliaFns := ["in(x, itr::Any)", "in(x, itr::Any32)", "in(x, itr::Tuple)", "_in_tuple"],
    statement := "Generic membership builds the Fix2 equality predicate ==(x) once and passes it to any, delegates Any32 inputs through invoke, and agrees with heterogeneous tuple membership across true, false, and missing.",
    source := "base/operators.jl:1455-1474", status := .proven,
    prop := ``MembershipDispatchSemantics, thm := some ``membershipDispatchSemantics_proven },
  { id := "operators-membership-wrappers", juliaFile := "base/operators.jl",
    juliaFns := ["∉(x, itr)", "∋(itr, x)", "∌(itr, x)", "in(x, itr::Any)", "in(x, itr::Any32)"],
    statement := "Across arbitrary collections satisfying the any iteration interface (including Any32 delegation) and heterogeneous tuples, ∋ reverses arguments and ∉ and ∌ compute the complement of in.",
    source := "base/operators.jl:1455-1486,1499-1500", status := .proven,
    prop := ``MembershipWrapperSemantics, thm := some ``membershipWrapperSemantics_proven },
  { id := "operators-membership-partials", juliaFile := "base/operators.jl",
    juliaFns := ["in(x)", "∉(itr)", "∋(x)", "∌(x)", "in(x, itr::Any)", "in(x, itr::Any32)"],
    statement := "Across arbitrary collections satisfying the any iteration interface (including Any32 delegation) and heterogeneous tuples, the unary membership helpers fix the documented item or collection and agree with their binary counterparts.",
    source := "base/operators.jl:1442-1500", status := .proven,
    prop := ``MembershipPartialSemantics, thm := some ``membershipPartialSemantics_proven },
  { id := "operators-adapter-display", juliaFile := "base/operators.jl",
    juliaFns := ["show(io::IO, c::ComposedFunction)", "show(io::IO, c::ComposedFunction{typeof(!)})",
      "_showcomposed(io::IO, x)", "_showcomposed(io::IO, f::Function)",
      "_showcomposed(io::IO, f::ComposedFunction)", "_showcomposed(io::IO, f::ComposedFunction{typeof(!)})",
      "Base.show(io::IO, fix::Fix{N})", "show(io::IO, s::Splat)"],
    statement := "Writing through an arbitrary IO stream, the composition, Fix{N}, and Splat show methods preserve callable names, operator and nesting parentheses, and reproduce sin ∘ cos, Fix{2}(+, 1), and splat(+).",
    source := "base/operators.jl:1103-1105,1140-1158,1226-1237,1359-1360,1387", status := .proven,
    prop := ``DisplayContract, thm := some ``displayContract_proven },
  { id := "operators-composition-unwrapping", juliaFile := "base/operators.jl",
    juliaFns := ["∘", "(c::ComposedFunction)(x...; kw...)"],
    statement := "Parenthesizing a composition either way gives the same observable result or error for every callable and argument list.",
    source := "base/operators.jl:1125-1129,1137-1138", status := .proven,
    prop := ``JuliaLean.Proofs.base.operators.Archive20261101.CompositionAssociativePublic,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group2.OperatorsCompositionUnwrapping_proven }
]

end JuliaLean.Proofs.base.operators


namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple

/- Proof-side observation infrastructure only. These are not Julia method models.
Every selected dispatch target is an arbitrary state-and-exception action on S;
its exception domain includes an unrestricted, universally quantified UserError;
the observer's trace is private and cannot be forged by that action. -/

/-- The model's existing errors and an unrestricted user-exception payload
are disjoint. Quantifying UserError retains custom exception classes and values;
no selected-dispatch exception has to be collapsed to TupleError. -/
abbrev Error (UserError : Type) := TupleError ⊕ UserError

/-- Inject the concrete Bool-assertion error while retaining arbitrary user
exceptions. A handler for TupleError catches only that summand; user errors
propagate with the state at the throw point unchanged. -/
instance {UserError S : Type} :
    MonadExceptOf TupleError (EStateM (Error UserError) S) where
  throw error := fun state => .error (.inl error) state
  tryCatch action handler := fun state =>
    match action state with
    | .ok value state' => .ok value state'
    | .error (.inl error) state' => handler error state'
    | .error (.inr error) state' => .error (.inr error) state'

structure CallObservation (Event R S UserError : Type) where
  event : Event
  outcome : Except (Error UserError) R
  before : S
  after : S

abbrev Observed (Event R S UserError : Type) :=
  EStateM (Error UserError) (S × List (CallObservation Event R S UserError))

/-- Observe an arbitrary selected call while preserving its exact result, error,
and world transition. Recording the outcome also distinguishes a call that was
attempted and threw from a call that was skipped. -/
def observeCall {Event R S UserError : Type} (event : Event)
    (action : EStateM (Error UserError) S R) : Observed Event R S UserError R :=
  fun (world, trace) =>
    match action world with
    | .ok value world' =>
        .ok value (world', trace ++ [⟨event, .ok value, world, world'⟩])
    | .error error world' =>
        .error error (world', trace ++ [⟨event, .error error, world, world'⟩])

/-- The result's state is observable even when the computation throws. -/
def resultState {E S R : Type} : EStateM.Result E S R → S
  | .ok _ state => state
  | .error _ state => state

def resultError {E S R : Type} : EStateM.Result E S R → Option E
  | .ok _ _ => none
  | .error error _ => some error

def resultSucceeded {E S R : Type} : EStateM.Result E S R → Prop
  | .ok _ _ => True
  | .error _ _ => False

def traceOf {Event R S A UserError : Type}
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) :
    List (CallObservation Event R S UserError) := (resultState result).2

/-- The first observed call starts in the initial world, and each subsequent
call starts in its predecessor's final world. Together with WorldConservation,
this excludes method-owned writes before, between, and after selected calls. -/
def WorldChain {Event R S UserError : Type} (initial : S) :
    List (CallObservation Event R S UserError) → Prop
  | [] => True
  | call :: rest => call.before = initial ∧ WorldChain call.after rest

/-- The final world is the last observed call's final world, or the initial
world when no call was observed. This checks only the final boundary;
WorldChain separately checks the first and intermediate boundaries. -/
def WorldConservation {Event R S A UserError : Type} (initial : S)
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) : Prop :=
  (resultState result).1 =
    ((traceOf result).getLast?.map (fun call => call.after)).getD initial

/-- A selected method's exception must terminate evaluation and remain the
exception returned by the surrounding Julia method. This is a trace invariant,
not a second implementation of that method's result expression. -/
def FailureIsTerminal {Event R S A UserError : Type}
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) : Prop :=
  ∀ (before after : List (CallObservation Event R S UserError))
      (call : CallObservation Event R S UserError) (error : Error UserError),
    traceOf result = before ++ call :: after →
    call.outcome = .error error →
    after = [] ∧ resultError result = some error

/-- A failed concrete type assertion is terminal. The predicate identifies
assertion slots and invalid values; it places no condition on the selected
callbacks, and is evaluated only on their recorded outcomes. -/
def AssertionIsTerminal {Event R S A UserError : Type}
    (badAssertion : Event → R → Prop)
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) : Prop :=
  ∀ (before after : List (CallObservation Event R S UserError))
      (call : CallObservation Event R S UserError) (value : R),
    traceOf result = before ++ call :: after →
    call.outcome = .ok value → badAssertion call.event value →
    after = [] ∧ resultError result = some (.inl .typeError)

/-- These comparison wrappers introduce no exception of their own except a
failed concrete Bool assertion. Every other exception has an observed dispatch
origin. This catches spurious errors as well as changed exception classes. -/
def ErrorsHaveSource {Event R S A UserError : Type}
    (badAssertion : Event → R → Prop)
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) : Prop :=
  ∀ error, resultError result = some error →
    (∃ call ∈ traceOf result, call.outcome = .error error) ∨
    (error = .inl .typeError ∧
      ∃ call ∈ traceOf result, ∃ value,
        call.outcome = .ok value ∧ badAssertion call.event value)

/-- Project only the specified source-level interface calls to their argument
word. Intermediary concrete Bool operations need no dispatch event. -/
def callWord {Event R S Leaf UserError : Type} (project : Event → Option Leaf)
    (trace : List (CallObservation Event R S UserError)) : List Leaf :=
  trace.filterMap (fun call => project call.event)

/-- The projected interface calls form a prefix of the specified argument word;
a normal result requires the whole word. This detects missing, duplicate,
reordered, or wrong-argument calls within that projection. Other event kinds
are not constrained by the word, but all observed calls share world continuity
and terminal-error checks. This is an independent observation invariant. -/
def OrderedProtocol {Event R S A Leaf UserError : Type} (initial : S)
    (project : Event → Option Leaf) (word : List Leaf)
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) A) : Prop :=
  let observed := callWord project (traceOf result)
  (∃ suffix, observed ++ suffix = word) ∧
  (resultSucceeded result → observed = word) ∧
  WorldChain initial (traceOf result) ∧
  WorldConservation initial result ∧ FailureIsTerminal result

/-- Two computations have identical observable effects, including the exception
class and the state visible at failure. Their successful values may differ. -/
def SameEffects {E S A B : Type}
    (a : EStateM.Result E S A) (b : EStateM.Result E S B) : Prop :=
  resultState a = resultState b ∧ resultError a = resultError b

/-- Equality, less-than, and greater-than comparisons of sampled sign bits
partition the two-sign state into exactly one case. No assumption is made about
the signbit methods, their values, their exceptions, or their state changes. -/
def SignTrichotomy {S UserError : Type}
    (eq less greater : EStateM.Result (Error UserError) S Bool) : Prop :=
  SameEffects eq less ∧ SameEffects eq greater ∧
  ∀ (e l g : Bool) (se sl sg : S),
    eq = .ok e se → less = .ok l sl → greater = .ok g sg →
    (e = true ∧ l = false ∧ g = false) ∨
    (e = false ∧ l = true ∧ g = false) ∨
    (e = false ∧ l = false ∧ g = true)


open JuliaLean.base.operators.Models2Group15

/-- Inputs of selected operations, retaining actual operand values. The
observer distinguishes interface calls from the concrete Bool branches. -/
inductive CallEvent (A B Other : Type) where
  | equality (x : A) (y : B)
  | signLeft (x : A)
  | signRight (y : B)
  | nanLeft (x : A)
  | nanRight (y : B)
  | signEqual (x : A) (y : B)
  | signLess (x : A) (y : B)
  | less (x : A) (y : B)
  | negate (value : Other)
  | conjunction (x y : Value Other)
  | disjunction (x y : Value Other)

/-- The ordered named operand queries. Overloaded Boolean operations are
also recorded, but the operand projection does not constrain their number or
order. Their helper implementations have independent invariants below. -/
inductive OperandCall (A B : Type) where
  | equality (x : A) (y : B)
  | signLeft (x : A)
  | signRight (y : B)
  | nanLeft (x : A)
  | nanRight (y : B)
  | signEqual (x : A) (y : B)
  | signLess (x : A) (y : B)
  | less (x : A) (y : B)

def operandCall {A B Other : Type} : CallEvent A B Other → Option (OperandCall A B)
  | .equality x y => some (.equality x y)
  | .signLeft x => some (.signLeft x)
  | .signRight y => some (.signRight y)
  | .nanLeft x => some (.nanLeft x)
  | .nanRight y => some (.nanRight y)
  | .signEqual x y => some (.signEqual x y)
  | .signLess x y => some (.signLess x y)
  | .less x y => some (.less x y)
  | .negate _ | .conjunction _ _ | .disjunction _ _ => none

abbrev ComparisonObserved (S A B Other UserError : Type) :=
  Observed (CallEvent A B Other) (Value Other) S UserError

abbrev ComparisonObservation (S A B Other R UserError : Type) :=
  EStateM.Result (Error UserError)
    (S × List (CallObservation (CallEvent A B Other) (Value Other) S UserError)) R

def observedEqualityOps {S A B Other UserError : Type}
    (ops : EqualityOps (EStateM (Error UserError) S) A B Other) :
    EqualityOps (ComparisonObserved S A B Other UserError) A B Other where
  equal x y := observeCall (CallEvent.equality (Other := Other) x y) (ops.equal x y)

def observedSignOps {S A B Other UserError : Type}
    (ops : SignOps (EStateM (Error UserError) S) A B Other) :
    SignOps (ComparisonObserved S A B Other UserError) A B Other where
  signLeft x := observeCall (CallEvent.signLeft (B := B) (Other := Other) x) (ops.signLeft x)
  signRight y := observeCall (CallEvent.signRight (A := A) (Other := Other) y) (ops.signRight y)

def observedBoolOps {S A B Other UserError : Type}
    (ops : BoolOps (EStateM (Error UserError) S) Other) :
    BoolOps (ComparisonObserved S A B Other UserError) Other where
  notOther value :=
    observeCall (CallEvent.negate (A := A) (B := B) value) (ops.notOther value)
  andOther x y :=
    observeCall (CallEvent.conjunction (A := A) (B := B) x y) (ops.andOther x y)
  orOther x y :=
    observeCall (CallEvent.disjunction (A := A) (B := B) x y) (ops.orOther x y)

def observedFloatEqualOps {S A B Other UserError : Type}
    (ops : FloatEqualOps (EStateM (Error UserError) S) A B Other) :
    FloatEqualOps (ComparisonObserved S A B Other UserError) A B Other where
  nanLeft x := observeCall (CallEvent.nanLeft (B := B) (Other := Other) x) (ops.nanLeft x)
  nanRight y := observeCall (CallEvent.nanRight (A := A) (Other := Other) y) (ops.nanRight y)
  signEqual x y := observeCall (CallEvent.signEqual (Other := Other) x y) (ops.signEqual x y)
  equal x y := observeCall (CallEvent.equality (Other := Other) x y) (ops.equal x y)
  boolOps := observedBoolOps ops.boolOps

def observedFloatLessOps {S A B Other UserError : Type}
    (ops : FloatLessOps (EStateM (Error UserError) S) A B Other) :
    FloatLessOps (ComparisonObserved S A B Other UserError) A B Other where
  nanLeft x := observeCall (CallEvent.nanLeft (B := B) (Other := Other) x) (ops.nanLeft x)
  nanRight y := observeCall (CallEvent.nanRight (A := A) (Other := Other) y) (ops.nanRight y)
  signLess x y := observeCall (CallEvent.signLess (Other := Other) x y) (ops.signLess x y)
  less x y := observeCall (CallEvent.less (Other := Other) x y) (ops.less x y)
  boolOps := observedBoolOps ops.boolOps

/-- Equality results at explicit ::Bool slots must have the concrete Bool
tag. No such condition is imposed on isnan, signequal, signless, or <. -/
def equalityAssertionBad {A B Other : Type} : CallEvent A B Other → Value Other → Prop
  | .equality _ _, .other _ => True
  | _, _ => False

def signAssertionBad {A B Other : Type} : CallEvent A B Other → Value Other → Prop
  | .signLeft _, .other _ => True
  | .signRight _, .other _ => True
  | _, _ => False

def ComparisonProtocol {S A B Other R UserError : Type} (initial : S)
    (badAssertion : CallEvent A B Other → Value Other → Prop)
    (word : List (OperandCall A B))
    (result : ComparisonObservation S A B Other R UserError) : Prop :=
  OrderedProtocol initial operandCall word result ∧
  AssertionIsTerminal badAssertion result ∧ ErrorsHaveSource badAssertion result

/-- A returned value has an actual dispatch-result witness. This relation
checks value/identity preservation without reconstructing an expected method
body or requiring a law of the selected callback. -/
def ReturnedValueObserved {Event R S UserError : Type}
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) R) : Prop :=
  ∀ (value : R) (final : S × List (CallObservation Event R S UserError)),
    result = .ok value final →
    ∃ call ∈ final.2, call.outcome = .ok value

/-- Generic isequal preserves one observed Boolean equality answer, including
its state changes, and rejects other dynamic results with TypeError. It always
attempts exactly one equality call with the original operand identities.

Julia source: base/operators.jl:196. Documentation: base/operators.jl:145-177;
doc/src/manual/types.md:67-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
All callbacks, all operand values, all non-Bool values, and arbitrary mutable
worlds and user-exception types/payloads are quantified. Observation implications constrain outcomes of
this execution; they assume no correctness law for equality. -/
def GenericIsequalProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : EqualityOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := isequal (observedEqualityOps ops) x y (world, [])
    ComparisonProtocol world equalityAssertionBad [.equality x y] result ∧
    callWord operandCall (traceOf result) = [.equality x y] ∧
    ∀ (value : Bool)
        (final : S × List (CallObservation (CallEvent A B Other) (Value Other) S UserError)),
      result = .ok value final →
      ∃ call ∈ final.2, call.outcome = .ok (.bool value)

/-- Proof-side perturbation of sampled sign bits. Non-Bool values and errors
are unchanged, so this neither assumes nor repairs a user signbit method. -/
def complementBoolResult {Other : Type} : Value Other → Value Other
  | .bool value => .bool (!value)
  | .other value => .other value

def complementedSigns {m : Type → Type} [Monad m] {A B Other : Type}
    (ops : SignOps m A B Other) : SignOps m A B Other where
  signLeft x := do pure (complementBoolResult (← ops.signLeft x))
  signRight y := do pure (complementBoolResult (← ops.signRight y))

/-- Sign equality and the two possible sign directions form a partition;
complementing both sampled Bool values reverses the direction while retaining
every dispatch effect and error. This is an algebraic invariant of sign
comparison, rather than an equality to either implementation's body. -/
def SignPartition {S A B Other UserError : Type}
    (ops : SignOps (EStateM (Error UserError) S) A B Other) (x : A) (y : B) (world : S) : Prop :=
  SignTrichotomy (signequal ops x y world) (signless ops x y world)
    (signless (complementedSigns ops) x y world)

/-- Both sign queries are eager, in argument order, subject to the first
exception or failed Bool assertion. Sign equality participates in the complete
three-way partition of sampled sign bits, with identical effects in all cases.
This is a narrow invariant of this internal helper.
Julia source: base/operators.jl:198-199; assertion semantics in
 doc/src/manual/types.md:67-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def SignEqualProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : SignOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := signequal (observedSignOps ops) x y (world, [])
    ComparisonProtocol world signAssertionBad [.signLeft x, .signRight y] result ∧
    traceOf result ≠ [] ∧ SignPartition ops x y world

/-- Sign order is eager even for a nonnegative left sign. The two signs and
their failures obey the same partition/effect invariant as sign equality;
a true result witnesses a negative first sign and a nonnegative second sign.
This is a narrow invariant of the internal helper, not an assumed contract of
arbitrary signbit implementations.
Julia source: base/operators.jl:198-199; operator precedence in
 doc/src/manual/mathematical-operations.md:472-480
 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def SignLessProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : SignOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := signless (observedSignOps ops) x y (world, [])
    ComparisonProtocol world signAssertionBad [.signLeft x, .signRight y] result ∧
    traceOf result ≠ [] ∧ SignPartition ops x y world ∧
    ∀ (final : S × List (CallObservation (CallEvent A B Other) (Value Other) S UserError)),
      result = .ok true final →
      (∃ call ∈ final.2, call.event = .signLeft x ∧ call.outcome = .ok (.bool true)) ∧
      (∃ call ∈ final.2, call.event = .signRight y ∧ call.outcome = .ok (.bool false))

/-- An independent invariant for float equality's four operand queries: their
projection is an ordered prefix of the NaN-left, NaN-right, sign, and equality
queries and is complete on success. Observed exceptions terminate unchanged,
worlds form a continuous chain, and only equality has the specified Bool
assertion. Boolean-operation events contribute to error and world checks but
are projected out of the ordering condition. This is not an exhaustive
semantic specification of Boolean dispatch or of the returned expression.
Julia source: base/operators.jl:201; doc/src/manual/control-flow.md:
264-268,361-376 and doc/src/manual/types.md:67-83
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FloatFloatIsequalProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : FloatEqualOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := isequalFloatFloat (observedFloatEqualOps ops) x y (world, [])
    ComparisonProtocol world equalityAssertionBad
      [.nanLeft x, .nanRight y, .signEqual x y, .equality x y] result ∧
    traceOf result ≠ []

/-- The mixed Real/AbstractFloat method has the same independent operand-query
prefix/completion invariant, retaining independently typed operand identities,
terminal observed errors, world continuity, and the equality Bool assertion.
All stateful/throwing callbacks and intermediate values are quantified.
Boolean-operation events are projected out of the ordering condition; this
invariant is not an exhaustive semantic specification of their calls or of
the returned expression.
Julia source: base/operators.jl:202; doc/src/manual/control-flow.md:
264-268,361-376 and doc/src/manual/types.md:67-83
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def RealFloatIsequalProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : FloatEqualOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := isequalRealFloat (observedFloatEqualOps ops) x y (world, [])
    ComparisonProtocol world equalityAssertionBad
      [.nanLeft x, .nanRight y, .signEqual x y, .equality x y] result ∧
    traceOf result ≠ []

/-- An independent invariant for float comparison's operand-query projection:
NaN-left, NaN-right, sign-order, and less-than occur as an ordered prefix that
is complete on success. Every returned error has an observed selected-call
origin and every observed failure terminates unchanged; worlds are continuous.
Boolean-operation events are projected out of the ordering condition. This
does not exhaustively specify their calls or the final returned expression,
and it introduces no Bool assertion for intermediate predicate results.
Julia source: base/operators.jl:240; doc/src/manual/control-flow.md:
264-268,361-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FloatFloatIslessProtocol : Prop :=
  ∀ (A B Other S UserError : Type) (ops : FloatLessOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (world : S),
    let result := islessFloatFloat (observedFloatLessOps ops) x y (world, [])
    ComparisonProtocol world (fun _ _ => False)
      [.nanLeft x, .nanRight y, .signLess x y, .less x y] result ∧
    traceOf result ≠ []

/-- An open dispatch helper forwards one call without swallowing its exception,
changing its returned object, altering its arguments, or introducing effects. -/
def SingleForwarded {Event R S UserError : Type} (initial : S) (event : Event)
    (result : EStateM.Result (Error UserError) (S × List (CallObservation Event R S UserError)) R) : Prop :=
  (traceOf result).map (fun call => call.event) = [event] ∧
  WorldChain initial (traceOf result) ∧
  WorldConservation initial result ∧ FailureIsTerminal result ∧
  ErrorsHaveSource (fun _ _ => False) result ∧ ReturnedValueObserved result

/-- A closed primitive Boolean branch calls no user method, cannot throw,
and changes no user-visible state. -/
def ClosedBoolBranch {Other S UserError : Type}
    (world : S) (result : ComparisonObservation S Unit Unit Other (Value Other) UserError) : Prop :=
  traceOf result = [] ∧ resultError result = none ∧ (resultState result).1 = world

/-- The three necessary dispatch helpers distinguish concrete Bool from every
other runtime value. On non-Bool inputs they preserve one arbitrary selected
operation's input identities, returned object, state changes, and exception.
On Bool inputs they never invoke the open callback and are effect-free.
Julia source: base/operators.jl:201-202,240; concrete callees
base/essentials.jl:1294, base/bool.jl:14-15
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolDispatchProtocol : Prop :=
  ∀ (Other S UserError : Type) (ops : BoolOps (EStateM (Error UserError) S) Other)
      (x y : Value Other) (world : S),
    let observed := observedBoolOps (A := Unit) (B := Unit) ops
    let negated := notValue observed x (world, [])
    let conjunction := andValue observed x y (world, [])
    let disjunction := orValue observed x y (world, [])
    (match x with
     | .bool _ => ClosedBoolBranch world negated
     | .other value => SingleForwarded world (.negate value) negated) ∧
    (match x, y with
     | .bool _, .bool _ =>
         ClosedBoolBranch world conjunction ∧ ClosedBoolBranch world disjunction
     | _, _ =>
         SingleForwarded world (.conjunction x y) conjunction ∧
         SingleForwarded world (.disjunction x y) disjunction)

/-- Concrete Bool negation is an involution, Boolean conjunction/disjunction
are idempotent, and a value together with its complement has contradictory
conjunction and tautological disjunction. The complete concrete Bool input
domain is covered, and arbitrary other-type callbacks cannot affect it.
These algebraic laws constrain actual results independently of the dispatch
helpers' pattern-match bodies.
Julia source: base/essentials.jl:1294, base/bool.jl:14-15;
doc/src/manual/mathematical-operations.md:52-60,88-95
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolPrimitiveAlgebra : Prop :=
  ∀ (Other S UserError : Type) (ops : BoolOps (EStateM (Error UserError) S) Other)
      (value : Bool) (world : S),
    (do
      let once ← notValue ops (.bool value)
      notValue ops once) world = .ok (.bool value) world ∧
    andValue ops (.bool value) (.bool value) world = .ok (.bool value) world ∧
    orValue ops (.bool value) (.bool value) world = .ok (.bool value) world ∧
    (do
      let complement ← notValue ops (.bool value)
      let both ← andValue ops (.bool value) complement
      let either ← orValue ops (.bool value) complement
      pure (both, either)) world = .ok (.bool false, .bool true) world

theorem boolPrimitiveAlgebra_proven : BoolPrimitiveAlgebra := by
  intro Other S UserError ops value world
  cases value <;> exact ⟨rfl, rfl, rfl, rfl⟩

end JuliaLean.Proofs.base.operators.Models2Group15

namespace JuliaLean.Proofs.base.operators

open JuliaLean.Registry

def Models2Group15.entriesInitial15 : List Entry := [
  { id := "operators-isequal-observation", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x, y)"],
    statement := "Generic isequal makes exactly one equality call with the original operands, preserves its Boolean answer and visible state, propagates selected errors, and rejects non-Bool results with TypeError.",
    source := "base/operators.jl:196; doc/src/manual/types.md:67-83; invariant of observed dispatch and Bool assertion",
    status := .todo, prop := ``Models2Group15.GenericIsequalProtocol, thm := none },
  { id := "operators-signequal-partition", juliaFile := "base/operators.jl",
    juliaFns := ["signequal(x, y)"],
    statement := "The internal sign-equality helper checks signs left to right with exact assertion/error effects and participates in a three-way partition of the two sampled sign bits without assumptions on signbit methods.",
    source := "base/operators.jl:198-199; doc/src/manual/types.md:67-83; internal sign partition invariant",
    status := .todo, prop := ``Models2Group15.SignEqualProtocol, thm := none },
  { id := "operators-signless-partition", juliaFile := "base/operators.jl",
    juliaFns := ["signless(x, y)"],
    statement := "The internal sign-order helper eagerly checks both signs unless an error or assertion stops it, shares the sign partition and effects, and can return true only for a negative first sign and nonnegative second sign.",
    source := "base/operators.jl:198-199; doc/src/manual/mathematical-operations.md:472-480; internal sign order invariant",
    status := .todo, prop := ``Models2Group15.SignLessProtocol, thm := none },
  { id := "operators-isequal-floatfloat-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x::AbstractFloat, y::AbstractFloat)"],
    statement := "Float equality's operand-query projection is an ordered prefix of NaN-left, NaN-right, sign-equality, and equality and is complete on success; observed failures terminate unchanged, worlds form a continuous chain, and equality has the specified Bool assertion.",
    source := "base/operators.jl:201; eager evaluation and explicit Bool assertion invariant",
    status := .todo, prop := ``Models2Group15.FloatFloatIsequalProtocol, thm := none,
    notes := "Independent invariant, not an exhaustive semantic specification: Boolean-operation events are projected out of the call-order condition." },
  { id := "operators-isequal-realfloat-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x::Real, y::AbstractFloat)"],
    statement := "Mixed Real/AbstractFloat equality preserves separately typed operand identities in its ordered operand-query prefix, completes that projection on success, propagates observed failures unchanged, keeps worlds continuous, and checks the equality Bool assertion.",
    source := "base/operators.jl:202; eager evaluation and explicit Bool assertion invariant",
    status := .todo, prop := ``Models2Group15.RealFloatIsequalProtocol, thm := none,
    notes := "Independent invariant, not an exhaustive semantic specification: Boolean-operation events are projected out of the call-order condition." },
  { id := "operators-isless-floatfloat-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isless(x::AbstractFloat, y::AbstractFloat)"],
    statement := "Float isless preserves the ordered NaN-left, NaN-right, sign-order, and less-than operand-query prefix and completes it on success; worlds are continuous, every returned error has an observed call origin, and every observed failure terminates unchanged.",
    source := "base/operators.jl:240; eager evaluation and exception-origin invariant",
    status := .todo, prop := ``Models2Group15.FloatFloatIslessProtocol, thm := none,
    notes := "Independent invariant, not an exhaustive semantic specification: Boolean-operation events are projected out of the call-order condition, and no predicate Bool assertion is assumed." },
  { id := "operators-boolean-dispatch-boundary", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x::AbstractFloat, y::AbstractFloat)", "isequal(x::Real, y::AbstractFloat)", "isless(x::AbstractFloat, y::AbstractFloat)"],
    statement := "The required Boolean-dispatch helpers invoke no user code for concrete Bool arguments; every non-Bool selected operation forwards one call with unchanged operands, returned object, visible state, and exception.",
    source := "base/operators.jl:201-202,240; necessary concrete callees base/essentials.jl:1294 and base/bool.jl:14-15",
    status := .todo, prop := ``Models2Group15.BoolDispatchProtocol, thm := none },
  { id := "operators-boolean-primitive-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["isequal(x::AbstractFloat, y::AbstractFloat)", "isequal(x::Real, y::AbstractFloat)", "isless(x::AbstractFloat, y::AbstractFloat)"],
    statement := "The necessary concrete Bool helpers satisfy double-negation, conjunction/disjunction idempotence, contradiction with the complement, and excluded middle, for both Bool values and arbitrary surrounding state/other-type dispatch.",
    source := "base/essentials.jl:1294; base/bool.jl:14-15; doc/src/manual/mathematical-operations.md:52-60,88-95; dependencies of base/operators.jl:201-202,240",
    status := .proven, prop := ``Models2Group15.BoolPrimitiveAlgebra,
    thm := ``Models2Group15.boolPrimitiveAlgebra_proven }
]

end JuliaLean.Proofs.base.operators


/- Proof-side fragment following PropertyDraft15.lean's observation infrastructure.
This file introduces no Julia implementation or proof. -/
namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple
open JuliaLean.base.operators.Models2Group15
  (Value GreaterOps UnorderedFloatOps NotEqualOps LessEqualOps RealLessOps BoolOps)

/-- Record differently typed results in a common outcome without changing the
value returned to the caller. The action cannot access the private trace.
Proof instrumentation for base/operators.jl:295. -/
def comparisonObserveCall {Event R Recorded S UserError : Type} (event : Event)
    (encode : R → Recorded) (action : EStateM (Error UserError) S R) :
    Observed Event Recorded S UserError R :=
  fun (world, trace) =>
    match action world with
    | .ok value world' =>
        .ok value (world', trace ++ [⟨event, .ok (encode value), world, world'⟩])
    | .error error world' =>
        .error error (world', trace ++ [⟨event, .error error, world, world'⟩])

/-- The first call starts in the initial world and every later call starts in
its predecessor's final world. With WorldConservation this excludes writes
before, between, and after selected calls. Proof-side invariant for
base/operators.jl:295,310,338,467,505. -/
def ComparisonWorldChain {Event R S UserError : Type} (initial : S) :
    List (CallObservation Event R S UserError) → Prop
  | [] => True
  | call :: rest => call.before = initial ∧ ComparisonWorldChain call.after rest

/-- The final selected call supplies the complete returned outcome. Other
clauses separately check call identity, arguments, and reachability.
Proof-side invariant for base/operators.jl:310,338,467,505. -/
def ComparisonLastOutcome {Event R S UserError : Type}
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation Event R S UserError)) R) : Prop :=
  match result with
  | .ok value _ =>
      ∃ call, (traceOf result).getLast? = some call ∧ call.outcome = .ok value
  | .error error _ =>
      ∃ call, (traceOf result).getLast? = some call ∧ call.outcome = .error error

/-- One call on the correct argument, preserving result, exception, and all
state changes on both successful and failed runs. No callee laws are premises.
Proof-side invariant for base/operators.jl:310,505. -/
def ComparisonForwardProtocol {Event R S UserError : Type}
    (argument : Event) (initial : S)
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation Event R S UserError)) R) : Prop :=
  (traceOf result).map (fun call => call.event) = [argument] ∧
  ComparisonWorldChain initial (traceOf result) ∧
  WorldConservation initial result ∧
  FailureIsTerminal result ∧
  ErrorsHaveSource (fun _ _ => False) result ∧
  ComparisonLastOutcome result

/-- Ordered-argument events for generic descending comparison.
Proof instrumentation for base/operators.jl:295. -/
inductive GreaterObservedEvent (A B : Type) where
  | unorderedLeft (value : A)
  | unorderedRight (value : B)
  | lessForward (left : A) (right : B)
  | lessBackward (right : B) (left : A)

/-- Observe arbitrary descending-order calls, retaining the distinct predicate
and result types. Proof instrumentation for base/operators.jl:295. -/
def comparisonObserveGreater {A B Other R S UserError : Type}
    (ops : GreaterOps (EStateM (Error UserError) S) A B Other R) :
    GreaterOps
      (Observed (GreaterObservedEvent A B) (Sum (Value Other) R) S UserError)
      A B Other R where
  unorderedLeft x :=
    comparisonObserveCall (.unorderedLeft x) Sum.inl (ops.unorderedLeft x)
  unorderedRight y :=
    comparisonObserveCall (.unorderedRight y) Sum.inl (ops.unorderedRight y)
  lessForward x y :=
    comparisonObserveCall (.lessForward x y) Sum.inr (ops.lessForward x y)
  lessBackward y x :=
    comparisonObserveCall (.lessBackward y x) Sum.inr (ops.lessBackward y x)

/-- Only reached unordered predicates are Bool assertion sites; the ordering
result is unrestricted. Proof instrumentation for base/operators.jl:295. -/
def comparisonGreaterBadAssertion {A B Other R : Type} :
    GreaterObservedEvent A B → Sum (Value Other) R → Prop
  | .unorderedLeft _, .inl (.other _) => True
  | .unorderedRight _, .inl (.other _) => True
  | _, _ => False

/-- Generic isgreater visits a permitted argument-bearing path. Reaching the
right predicate requires an observed false left predicate, the forward order
requires an observed true predicate, and the backward order requires two false
predicates. A successful result is an observed ordering result of arbitrary
type R. Every error has a dispatch or failed-assertion origin and terminates
evaluation. All states, result types, and user exception types are included;
no callee correctness laws are assumed.
Julia source: base/operators.jl:295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/operators.jl:252-294; doc/src/manual/control-flow.md
(short-circuit evaluation); doc/src/manual/types.md:67-83. -/
-- Source: base/operators.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isgreater(x, y) = isunordered(x) || isunordered(y) ? isless(x, y) : isless(y, x)
-- /Source
def GreaterObservationProtocol : Prop :=
  ∀ (A B Other R S UserError : Type)
      (ops : GreaterOps (EStateM (Error UserError) S) A B Other R)
      (x : A) (y : B) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.isgreater
      (comparisonObserveGreater ops) x y (initial, [])
    let trace := traceOf result
    let word := trace.map (fun call => call.event)
    word ∈
      [[.unorderedLeft x],
       [.unorderedLeft x, .unorderedRight y],
       [.unorderedLeft x, .lessForward x y],
       [.unorderedLeft x, .unorderedRight y, .lessForward x y],
       [.unorderedLeft x, .unorderedRight y, .lessBackward y x]] ∧
    ComparisonWorldChain initial trace ∧
    WorldConservation initial result ∧
    FailureIsTerminal result ∧
    AssertionIsTerminal comparisonGreaterBadAssertion result ∧
    ErrorsHaveSource comparisonGreaterBadAssertion result ∧
    (.unorderedRight y ∈ word →
      ∃ call ∈ trace, call.event = .unorderedLeft x ∧
        call.outcome = .ok (.inl (.bool false))) ∧
    (.lessForward x y ∈ word →
      ∃ call ∈ trace,
        (call.event = .unorderedLeft x ∨ call.event = .unorderedRight y) ∧
        call.outcome = .ok (.inl (.bool true))) ∧
    (.lessBackward y x ∈ word →
      (∃ call ∈ trace, call.event = .unorderedLeft x ∧
        call.outcome = .ok (.inl (.bool false))) ∧
      (∃ call ∈ trace, call.event = .unorderedRight y ∧
        call.outcome = .ok (.inl (.bool false)))) ∧
    (∀ value final, result = .ok value final →
      ∃ call ∈ trace,
        (call.event = .lessForward x y ∨ call.event = .lessBackward y x) ∧
        call.outcome = .ok (.inr value))

/-- AbstractFloat isunordered is transparent around one isnan call: the input
is passed exactly once and its result, exception, and world transition are
preserved. Result types and user exception types are unrestricted, so no
unmentioned Bool assertion can be introduced.
Julia source: base/operators.jl:310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/operators.jl:297-308. -/
-- Source: base/operators.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isunordered(x::AbstractFloat) = isnan(x)
-- /Source
def UnorderedFloatObservationProtocol : Prop :=
  ∀ (A R S UserError : Type)
      (ops : UnorderedFloatOps (EStateM (Error UserError) S) A R)
      (x : A) (initial : S),
    let observed : UnorderedFloatOps (Observed A R S UserError) A R :=
      { isnan := fun value => observeCall value (ops.isnan value) }
    let result := JuliaLean.base.operators.Models2Group15.isunorderedFloat
      observed x (initial, [])
    ComparisonForwardProtocol x initial result

/-- The event vocabulary includes unused Boolean operations so an accidental
extra dispatch is observable. Only non-Bool values select custom negation.
Proof instrumentation for base/operators.jl:338,467. -/
inductive ComparisonObservedEvent (A B Other : Type) where
  | less (left : A) (right : B)
  | equal (left : A) (right : B)
  | negate (value : Other)
  | conjunction (left right : Value Other)
  | disjunction (left right : Value Other)

/-- Instrument result-level custom dispatch without constraining its effects
or outcomes. Concrete Boolean operations remain in the model.
Proof instrumentation for base/operators.jl:338,467. -/
def comparisonObserveBool {A B Other S UserError : Type}
    (ops : BoolOps (EStateM (Error UserError) S) Other) :
    BoolOps
      (Observed (ComparisonObservedEvent A B Other) (Value Other) S UserError) Other where
  notOther value := observeCall (.negate value) (ops.notOther value)
  andOther left right := observeCall (.conjunction left right) (ops.andOther left right)
  orOther left right := observeCall (.disjunction left right) (ops.orOther left right)

/-- Observe inequality's selected calls with a private trace.
Proof instrumentation for base/operators.jl:338. -/
def comparisonObserveNotEqual {A B Other S UserError : Type}
    (ops : NotEqualOps (EStateM (Error UserError) S) A B Other) :
    NotEqualOps
      (Observed (ComparisonObservedEvent A B Other) (Value Other) S UserError)
      A B Other where
  equal x y := observeCall (.equal x y) (ops.equal x y)
  boolOps := comparisonObserveBool ops.boolOps

/-- Generic inequality attempts equality exactly once before any selected
negation. A Bool equality result produces a successful Bool distinct from it,
with no custom negation. A non-Bool equality result is passed unchanged to one
custom negation, whose whole outcome is preserved. Arguments, ordering, error
provenance, and all world transitions are checked for arbitrary effectful
implementations and user exception types, without callee correctness laws.
Julia source: base/operators.jl:338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/operators.jl:319-337; base/essentials.jl:1294. -/
-- Source: base/operators.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !=(x, y) = !(x == y)
-- /Source
def NotEqualObservationProtocol : Prop :=
  ∀ (A B Other S UserError : Type)
      (ops : NotEqualOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.notEqual
      (comparisonObserveNotEqual ops) x y (initial, [])
    let trace := traceOf result
    let word := trace.map (fun call => call.event)
    (word = [.equal x y] ∨ ∃ other, word = [.equal x y, .negate other]) ∧
    ComparisonWorldChain initial trace ∧
    WorldConservation initial result ∧
    FailureIsTerminal result ∧
    ErrorsHaveSource (fun _ _ => False) result ∧
    (∀ call ∈ trace, ∀ bit,
      call.event = .equal x y → call.outcome = .ok (.bool bit) →
      word = [.equal x y] ∧ resultSucceeded result ∧
      ∀ value final, result = .ok value final →
        (∃ otherBit, value = .bool otherBit) ∧ value ≠ .bool bit) ∧
    (∀ call ∈ trace, ∀ other,
      call.event = .equal x y → call.outcome = .ok (.other other) →
      word = [.equal x y, .negate other] ∧ ComparisonLastOutcome result)

/-- Observe the two comparisons and possible result-level disjunction.
Proof instrumentation for base/operators.jl:467. -/
def comparisonObserveLessEqual {A B Other S UserError : Type}
    (ops : LessEqualOps (EStateM (Error UserError) S) A B Other) :
    LessEqualOps
      (Observed (ComparisonObservedEvent A B Other) (Value Other) S UserError)
      A B Other where
  less x y := observeCall (.less x y) (ops.less x y)
  equal x y := observeCall (.equal x y) (ops.equal x y)
  boolOps := comparisonObserveBool ops.boolOps

/-- Generic <= is eager: every successful < call is followed by == on the same
arguments, even when < returned true. Two Bool outcomes produce a successful
Bool that is false exactly when both were false; otherwise one selected
disjunction receives the actual comparison results in order, and its complete
outcome is preserved. Arbitrary effects and user exceptions are included,
without comparison correctness premises. The private log detects omitted,
duplicated, reordered, or spurious calls, errors, and world changes.
Julia source: base/operators.jl:467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/operators.jl:446-466; base/bool.jl:15. -/
-- Source: base/operators.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x, y) = (x < y) | (x == y)
-- /Source
def LessEqualObservationProtocol : Prop :=
  ∀ (A B Other S UserError : Type)
      (ops : LessEqualOps (EStateM (Error UserError) S) A B Other)
      (x : A) (y : B) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.lessEqual
      (comparisonObserveLessEqual ops) x y (initial, [])
    let trace := traceOf result
    let word := trace.map (fun call => call.event)
    (word = [.less x y] ∨ word = [.less x y, .equal x y] ∨
      ∃ left right, word = [.less x y, .equal x y, .disjunction left right]) ∧
    ComparisonWorldChain initial trace ∧
    WorldConservation initial result ∧
    FailureIsTerminal result ∧
    ErrorsHaveSource (fun _ _ => False) result ∧
    (∀ call ∈ trace, ∀ value,
      call.event = .less x y → call.outcome = .ok value →
      ∃ following ∈ trace, following.event = .equal x y) ∧
    (∀ lessCall ∈ trace, ∀ equalCall ∈ trace, ∀ lessValue equalValue,
      lessCall.event = .less x y → lessCall.outcome = .ok lessValue →
      equalCall.event = .equal x y → equalCall.outcome = .ok equalValue →
      match lessValue, equalValue with
      | .bool lessBit, .bool equalBit =>
          word = [.less x y, .equal x y] ∧
          ∃ resultBit final,
            result = .ok (.bool resultBit) final ∧
            (resultBit = false ↔ lessBit = false ∧ equalBit = false)
      | _, _ =>
          word = [.less x y, .equal x y, .disjunction lessValue equalValue] ∧
          ComparisonLastOutcome result)

/-- Real/Real isless forwards one < call on the original ordered pair and
preserves its successful value of any type R, exception on failure, and exact
world transition. Neither a Bool result nor an ordering law is assumed, and
every user exception type is included.
Julia source: base/operators.jl:505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/operators.jl:206-237,503-505. -/
-- Source: base/operators.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isless(x::Real, y::Real) = x<y
-- /Source
def IslessRealObservationProtocol : Prop :=
  ∀ (A B R S UserError : Type)
      (ops : RealLessOps (EStateM (Error UserError) S) A B R)
      (x : A) (y : B) (initial : S),
    let observed : RealLessOps (Observed (A × B) R S UserError) A B R :=
      { less := fun left right => observeCall (left, right) (ops.less left right) }
    let result := JuliaLean.base.operators.Models2Group15.islessReal
      observed x y (initial, [])
    ComparisonForwardProtocol (x, y) initial result

theorem singleton_decomposition {A : Type} (before after : List A) (call only : A)
    (h : [only] = before ++ call :: after) : before = [] ∧ call = only ∧ after = [] := by
  cases before with
  | nil => simpa [List.cons.injEq, Eq.comm] using h
  | cons first rest =>
    have hl := congrArg List.length h
    simp at hl

theorem observeCall_forward {Event R S U : Type} (event : Event)
    (action : EStateM (Error U) S R) (initial : S) :
    ComparisonForwardProtocol event initial (observeCall event action (initial, [])) := by
  cases ha : action initial with
  | ok value after =>
    simp only [observeCall, ha, List.nil_append]
    refine ⟨rfl, ⟨rfl, True.intro⟩, rfl, ?_, ?_, ?_⟩
    · intro before later call error h he
      obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition before later call _ h
      contradiction
    · intro error h
      contradiction
    · exact ⟨⟨event, .ok value, initial, after⟩, rfl, rfl⟩
  | error error after =>
    simp only [observeCall, ha, List.nil_append]
    refine ⟨rfl, ⟨rfl, True.intro⟩, rfl, ?_, ?_, ?_⟩
    · intro before later call e h he
      obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition before later call _ h
      exact ⟨rfl, congrArg some (Except.error.inj he)⟩
    · intro e h
      exact Or.inl ⟨⟨event, .error error, initial, after⟩, List.mem_singleton_self _,
        congrArg Except.error (Option.some.inj h)⟩
    · exact ⟨⟨event, .error error, initial, after⟩, rfl, rfl⟩

theorem unorderedFloatObservationProtocol_proven : UnorderedFloatObservationProtocol := by
  intro A R S U ops x initial
  exact observeCall_forward _ _ _

theorem islessRealObservationProtocol_proven : IslessRealObservationProtocol := by
  intro A B R S U ops x y initial
  exact observeCall_forward _ _ _

/-- Registry additions for the five completed comparison models. -/
def entriesComparison15 : List JuliaLean.Registry.Entry := [
  { id := "operators-isgreater-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isgreater(x, y)"],
    statement := "For arbitrary stateful and throwing dispatch methods, isgreater checks only reached unordered predicates, chooses one justified ordering direction with the original arguments, preserves its unrestricted result, and introduces no unrecorded state changes or errors except terminal TypeError for a non-Bool condition.",
    source := "base/operators.jl:252-295; doc/src/manual/control-flow.md (short-circuit evaluation); doc/src/manual/types.md:67-83",
    status := .todo, prop := ``GreaterObservationProtocol, thm := none },
  { id := "operators-isunordered-float-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isunordered(x::AbstractFloat)"],
    statement := "AbstractFloat isunordered calls the selected isnan exactly once on its operand and preserves its arbitrary result, exception, and world transition without adding a Bool assertion.",
    source := "base/operators.jl:297-310", status := .proven,
    prop := ``UnorderedFloatObservationProtocol, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unorderedFloatObservationProtocol_proven },
  { id := "operators-not-equal-effects", juliaFile := "base/operators.jl",
    juliaFns := ["!=(x, y)"],
    statement := "Generic != calls equality once, complements a Bool result without custom dispatch, or passes a non-Bool result unchanged to one selected negation and preserves its outcome; all call arguments, effects, and errors are retained without assumed callee laws.",
    source := "base/operators.jl:319-338; base/essentials.jl:1294", status := .todo,
    prop := ``NotEqualObservationProtocol, thm := none },
  { id := "operators-less-equal-effects", juliaFile := "base/operators.jl",
    juliaFns := ["<=(x, y)"],
    statement := "Generic <= evaluates < and then == eagerly on the original arguments, returns false for two Bool outcomes exactly when both are false, otherwise calls the selected disjunction once with those outcomes in order, and preserves all effects and exceptions.",
    source := "base/operators.jl:446-467; base/bool.jl:15", status := .todo,
    prop := ``LessEqualObservationProtocol, thm := none },
  { id := "operators-isless-real-effects", juliaFile := "base/operators.jl",
    juliaFns := ["isless(x::Real, y::Real)"],
    statement := "Real/Real isless forwards one < call on the original ordered pair and preserves its unrestricted result, exception, and world transition, with no Bool assertion or callee correctness assumption.",
    source := "base/operators.jl:206-237,503-505", status := .proven,
    prop := ``IslessRealObservationProtocol, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.islessRealObservationProtocol_proven }
]

end JuliaLean.Proofs.base.operators.Models2Group15


/- Reconstructed independent properties for reused pure methods.
   This recovery fragment contains only new Prop declarations and .todo
   registry additions. No existing model, statement, proof, or registry
   entry is changed. Julia commit:
   f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/

namespace JuliaLean.Proofs.base.operators.Models2Group15

/-- Two independent algebraic invariants jointly force identity: no inputs
are merged, and applying the operation again cannot change its first result.
The carrier is unrestricted, so equality can include actual reference identity
rather than a lossy numeric or structural projection. -/
def PureIdentityInvariant {A : Type} (operation : A → A) : Prop :=
  (∀ x y, operation x = operation y → x = y) ∧
  (∀ x, operation (operation x) = operation x)

/-- The parent of TypeEq is independent of its parameter and belongs to the
proper runtime type category. It is a type object whose runtime type is
DataType, differs from Any, and is not a concrete some-type object. This avoids
mistaking the abstract AnyType parent for a member of the closed kind union.
Julia source: base/operators.jl:103-104 at the pinned commit. -/
-- Source: base/operators.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- supertype(::TypeEq) = Core.AnyType
-- /Source
def TypeEqParentCategory : Prop :=
  ∀ (left right : JuliaLean.C.Val),
    let parent := JuliaLean.base.operators.supertypeTypeEq left
    parent = JuliaLean.base.operators.supertypeTypeEq right ∧
    parent.isType = true ∧
    JuliaLean.C.typeOf parent = JuliaLean.C.datatypeType ∧
    parent ≠ JuliaLean.C.anyType ∧
    parent.isSomeType = false

/-- The generic classification ignores its input, and the Missing singleton
has the complementary classification. Both source domains are retained:
arbitrary values for the generic fallback and the unique Missing inhabitant.
This is a narrow independent distinction/input-invariance property.
Documentation: base/operators.jl:297-308 at the pinned commit. -/
-- Source: base/operators.jl:309-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isunordered(_) = false
-- /Source
-- Source: base/operators.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isunordered(::Missing) = true
-- /Source
def UnorderedClassificationSeparation : Prop :=
  ∀ (A B : Type) (left : A) (right : B) (missing : Unit),
    JuliaLean.base.operators.isunordered left =
      JuliaLean.base.operators.isunordered right ∧
    JuliaLean.base.operators.isunorderedMissing missing ≠
      JuliaLean.base.operators.isunordered left ∧
    JuliaLean.base.operators.isunorderedMissing missing =
      !(JuliaLean.base.operators.isunordered left)

/-- Cross-kind equality agrees in both argument directions and can never
classify a TypeVar as equal to a Type. The distinct arbitrary carriers preserve
all actual type/type-variable values rather than selecting numeric samples.
Julia source: base/operators.jl:314-315 at the pinned commit. -/
-- Source: base/operators.jl:314-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(T::TypeVar, S::Type) = false
-- ==(T::Type, S::TypeVar) = false
-- /Source
def TypeVarTypeSeparation : Prop :=
  ∀ (TypeVariable TypeObject : Type)
      (typeVariable : TypeVariable) (typeObject : TypeObject),
    JuliaLean.base.operators.typeVarEqual typeVariable typeObject =
      JuliaLean.base.operators.typeEqualVar typeObject typeVariable ∧
    JuliaLean.base.operators.typeVarEqual typeVariable typeObject ≠ true ∧
    JuliaLean.base.operators.typeEqualVar typeObject typeVariable ≠ true

/-- Identity is injective and idempotent on every carrier, jointly excluding
a replacement, copy with changed identity, or nonidentity permutation.
Documentation: base/operators.jl:592-604 at the pinned commit. -/
-- Source: base/operators.jl:605-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- identity(@nospecialize x) = x
-- /Source
def IdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.identity value)

/-- Unary + retains injectivity and idempotence for arbitrary Number-domain
carriers, including abstract and custom numeric values. No arithmetic law of
the inputs is assumed, and no callee callback is needed by this source body.
Julia source: base/operators.jl:607 at the pinned commit. -/
-- Source: base/operators.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Number) = x
-- /Source
def UnaryPlusIdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.unaryPlusNumber value)

/-- Unary * has the same lossless idempotence invariant over the complete
arbitrary Number carrier, preserving custom and reference-bearing objects.
Julia source: base/operators.jl:608 at the pinned commit. -/
-- Source: base/operators.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Number) = x
-- /Source
def UnaryMulIdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.unaryMulNumber value)

/-- Unary & is lossless and idempotent for every Integer-domain carrier;
the property does not reduce the domain to machine integers or Bool.
Julia source: base/operators.jl:609 at the pinned commit. -/
-- Source: base/operators.jl:609-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (&)(x::Integer) = x
-- /Source
def UnaryAndIdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.unaryAndInteger value)

/-- Unary | is lossless and idempotent for arbitrary Integer-domain values,
including custom subtypes and values represented by reference identity.
Julia source: base/operators.jl:610 at the pinned commit. -/
-- Source: base/operators.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (|)(x::Integer) = x
-- /Source
def UnaryOrIdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.unaryOrInteger value)

/-- Unary xor preserves the same injective/idempotent invariant across every
Integer-domain carrier, with no binary-xor assumptions about those values.
Julia source: base/operators.jl:611 at the pinned commit. -/
-- Source: base/operators.jl:611-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- xor(x::Integer) = x
-- /Source
def UnaryXorIdentityAlgebraic : Prop :=
  ∀ (A : Type),
    PureIdentityInvariant (fun value : A => JuliaLean.base.operators.unaryXorInteger value)

/-- A one-value fold is lossless and idempotent in its accumulator. Replacing
its ignored operator by an arbitrary object of an unrelated type cannot
affect the result. In particular, operator callability is not a premise.
All accumulators, operators, abstract/custom domains, and reference identities
are retained. This is an independent algebraic and parameter-erasure contract.
Julia source and internal design comment: base/operators.jl:617-622. -/
-- Source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- afoldl(op, a) = a
-- /Source
def AfoldlOneIdentityAlgebraic : Prop :=
  ∀ (A Operator OtherOperator : Type)
      (operator : Operator) (otherOperator : OtherOperator),
    PureIdentityInvariant
      (fun value : A => JuliaLean.base.operators.afoldlOne operator value) ∧
    ∀ (value : A),
      JuliaLean.base.operators.afoldlOne operator value =
        JuliaLean.base.operators.afoldlOne otherOperator value

theorem typeEqParentCategory_proven : TypeEqParentCategory := by
  intro left right
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  intro h
  have hn := JuliaLean.C.Val.datatype.inj h
  exact (by decide : ("Core.AnyType" : String) ≠ "Core.Any") hn.1

theorem unorderedClassificationSeparation_proven : UnorderedClassificationSeparation := by
  intro A B left right missing
  exact ⟨rfl, by change true ≠ false; decide, rfl⟩

theorem typeVarTypeSeparation_proven : TypeVarTypeSeparation := by
  intro A B tv object
  exact ⟨rfl, by change false ≠ true; decide, by change false ≠ true; decide⟩

theorem identityAlgebraic_proven : IdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem unaryPlusIdentityAlgebraic_proven : UnaryPlusIdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem unaryMulIdentityAlgebraic_proven : UnaryMulIdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem unaryAndIdentityAlgebraic_proven : UnaryAndIdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem unaryOrIdentityAlgebraic_proven : UnaryOrIdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem unaryXorIdentityAlgebraic_proven : UnaryXorIdentityAlgebraic := by
  intro A
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

theorem afoldlOneIdentityAlgebraic_proven : AfoldlOneIdentityAlgebraic := by
  intro A O O' op op'
  exact ⟨⟨fun _ _ h => h, fun _ => rfl⟩, fun _ => rfl⟩

/-- Additive declarations only; these properties remain unproved. -/
def entriesPure15 : List JuliaLean.Registry.Entry := [
  { id := "operators-typeeq-parent-category", juliaFile := "base/operators.jl",
    juliaFns := ["supertype(::TypeEq)"],
    statement := "The TypeEq parent erases its parameter, is a type object with runtime type DataType, differs from Any, and is not a some-type object.",
    source := "base/operators.jl:103-104; existing Core runtime type predicates",
    status := .proven, prop := ``TypeEqParentCategory, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.typeEqParentCategory_proven },
  { id := "operators-unordered-classification-separation", juliaFile := "base/operators.jl",
    juliaFns := ["isunordered(_)", "isunordered(::Missing)"],
    statement := "Generic unordered classification is input-independent across arbitrary carriers, and Missing has the distinct complementary Bool classification.",
    source := "base/operators.jl:297-311",
    status := .proven, prop := ``UnorderedClassificationSeparation, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unorderedClassificationSeparation_proven },
  { id := "operators-typevar-type-separation", juliaFile := "base/operators.jl",
    juliaFns := ["==(T::TypeVar, S::Type)", "==(T::Type, S::TypeVar)"],
    statement := "Cross-kind TypeVar/Type equality agrees under argument reversal and cannot return true for either direction.",
    source := "base/operators.jl:314-315",
    status := .proven, prop := ``TypeVarTypeSeparation, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.typeVarTypeSeparation_proven },
  { id := "operators-identity-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["identity(@nospecialize x)"],
    statement := "Identity is injective and idempotent for every value carrier, jointly preserving the original value and reference identity.",
    source := "base/operators.jl:592-605",
    status := .proven, prop := ``IdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.identityAlgebraic_proven },
  { id := "operators-unary-plus-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["+(x::Number)"],
    statement := "Unary + is injective and idempotent over arbitrary numeric value carriers, including abstract/custom values and reference identity.",
    source := "base/operators.jl:607",
    status := .proven, prop := ``UnaryPlusIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unaryPlusIdentityAlgebraic_proven },
  { id := "operators-unary-mul-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["*(x::Number)"],
    statement := "Unary * is injective and idempotent over arbitrary numeric value carriers, jointly preserving each original object.",
    source := "base/operators.jl:608",
    status := .proven, prop := ``UnaryMulIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unaryMulIdentityAlgebraic_proven },
  { id := "operators-unary-and-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["(&)(x::Integer)"],
    statement := "Unary & is injective and idempotent for every Integer-domain carrier, including custom values rather than only fixed machine integers.",
    source := "base/operators.jl:609",
    status := .proven, prop := ``UnaryAndIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unaryAndIdentityAlgebraic_proven },
  { id := "operators-unary-or-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["(|)(x::Integer)"],
    statement := "Unary | is injective and idempotent for every Integer-domain carrier, preserving original object identity.",
    source := "base/operators.jl:610",
    status := .proven, prop := ``UnaryOrIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unaryOrIdentityAlgebraic_proven },
  { id := "operators-unary-xor-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["xor(x::Integer)"],
    statement := "Unary xor is injective and idempotent for arbitrary Integer-domain values without assuming any binary-operation law.",
    source := "base/operators.jl:611",
    status := .proven, prop := ``UnaryXorIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.unaryXorIdentityAlgebraic_proven },
  { id := "operators-afoldl-one-algebra", juliaFile := "base/operators.jl",
    juliaFns := ["afoldl(op, a)"],
    statement := "One-value afoldl is injective and idempotent in the accumulator and independent of the ignored operator across unrelated operator types, including noncallable objects.",
    source := "base/operators.jl:617-622",
    status := .proven, prop := ``AfoldlOneIdentityAlgebraic, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.afoldlOneIdentityAlgebraic_proven }
]

end JuliaLean.Proofs.base.operators.Models2Group15


namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple JuliaLean.base.operators.Models2Group15

/-- Argument-bearing comparison and open ifelse calls. The observation layer
does not restrict dispatch returns, mutation, or user exceptions. -/
inductive CmpCall15 (F A B Cond Other : Type) where
  | forward (function : F) (left : A) (right : B)
  | backward (function : F) (left : B) (right : A)
  | select (condition : Value Cond) (yes no : CmpValue Other)

def observeIfelse15 {F A B Cond Other S UserError : Type}
    (ops : IfelseOps (EStateM (Error UserError) S) Cond Other) :
    IfelseOps
      (Observed (CmpCall15 F A B Cond Other)
        (Value Cond ⊕ CmpValue Other) S UserError) Cond Other where
  other condition yes no :=
    comparisonObserveCall (.select (.other condition) yes no) Sum.inr
      (ops.other condition yes no)
  boolOther condition yes no :=
    comparisonObserveCall (.select (.bool condition) yes no) Sum.inr
      (ops.boolOther condition yes no)

def observeCmp15 {A B Cond Other S UserError : Type}
    (ops : CmpOps (EStateM (Error UserError) S) A B Cond Other) :
    CmpOps
      (Observed (CmpCall15 Unit A B Cond Other)
        (Value Cond ⊕ CmpValue Other) S UserError) A B Cond Other where
  lessForward left right :=
    comparisonObserveCall (.forward () left right) Sum.inl
      (ops.lessForward left right)
  lessBackward left right :=
    comparisonObserveCall (.backward () left right) Sum.inl
      (ops.lessBackward left right)
  ifelseOps := observeIfelse15 ops.ifelseOps

def observeCmpBy15 {F A B Cond Other S UserError : Type}
    (ops : CmpByOps (EStateM (Error UserError) S) F A B Cond Other) :
    CmpByOps
      (Observed (CmpCall15 F A B Cond Other)
        (Value Cond ⊕ CmpValue Other) S UserError) F A B Cond Other where
  callForward function left right :=
    comparisonObserveCall (.forward function left right) Sum.inl
      (ops.callForward function left right)
  callBackward function left right :=
    comparisonObserveCall (.backward function left right) Sum.inl
      (ops.callBackward function left right)
  ifelseOps := observeIfelse15 ops.ifelseOps

abbrev CmpResult15 (F A B Cond Other S UserError : Type) :=
  EStateM.Result (Error UserError)
    (S × List (CallObservation (CmpCall15 F A B Cond Other)
      (Value Cond ⊕ CmpValue Other) S UserError)) (CmpValue Other)

def cmpPhases15 {F A B Cond Other S UserError : Type}
    (result : CmpResult15 F A B Cond Other S UserError) : List Nat :=
  (traceOf result).map fun call => match call.event with
    | .forward _ _ _ => 0
    | .backward _ _ _ => 1
    | .select _ _ _ => 2

def cmpBad15 {F A B Cond Other : Type} :
    CmpCall15 F A B Cond Other → Value Cond ⊕ CmpValue Other → Prop
  | .forward _ _ _, .inl (.other _) => True
  | _, _ => False

/-- Generic conservation checks: complete state continuity; every selected
condition has an earlier comparison-result origin; branch payloads are native
sign constants or an earlier actual selection result; output is a native sign
or an actual open-dispatch result. These are trace/data-origin invariants. -/
def CmpConservation15 {F A B Cond Other S UserError : Type}
    (initial : S) (function : F) (x : A) (y : B)
    (result : CmpResult15 F A B Cond Other S UserError) : Prop :=
  WorldChain initial (traceOf result) ∧ WorldConservation initial result ∧
  FailureIsTerminal result ∧
  (∃ first rest, traceOf result = first :: rest ∧
    first.event = .forward function x y) ∧
  (∀ call ∈ traceOf result, match call.event with
    | .forward f a b => f = function ∧ a = x ∧ b = y
    | .backward f b a => f = function ∧ b = y ∧ a = x
    | .select _ _ _ => True) ∧
  (∀ before call after condition yes no,
    traceOf result = before ++ call :: after →
    call.event = .select condition yes no →
    (∃ origin ∈ before, origin.outcome = .ok (.inl condition)) ∧
    (yes = .integer cmpOne ∨ yes = .integer cmpMinusOne) ∧
    (no = .integer cmpZero ∨ no = .integer cmpOne ∨
      ∃ origin ∈ before, origin.outcome = .ok (.inr no))) ∧
  (∀ value final, result = .ok value final →
    (value = .integer cmpMinusOne ∨ value = .integer cmpZero ∨
      value = .integer cmpOne) ∨
    ∃ origin ∈ traceOf result, origin.outcome = .ok (.inr value))

/-- Short comparison is bounded by one forward query, one reverse query and
one selection. A true forward result suppresses all later calls; a false one
reaches the reverse query. The only assertion is the first query. -/
def CmpShortControl15 {F A B Cond Other S UserError : Type}
    (initial : S) (function : F) (x : A) (y : B)
    (result : CmpResult15 F A B Cond Other S UserError) : Prop :=
  CmpConservation15 initial function x y result ∧
  (∃ suffix, cmpPhases15 result ++ suffix = [0, 1, 2]) ∧
  AssertionIsTerminal cmpBad15 result ∧ ErrorsHaveSource cmpBad15 result ∧
  (∀ call ∈ traceOf result, call.event = .forward function x y →
    (call.outcome = .ok (.inl (.bool true)) →
      cmpPhases15 result = [0] ∧
      ∃ final, result = .ok (.integer cmpMinusOne) final) ∧
    (call.outcome = .ok (.inl (.bool false)) →
      ∃ reverse ∈ traceOf result, reverse.event = .backward function y x)) ∧
  (∀ call ∈ traceOf result, call.event = .backward function y x →
    ∀ condition, call.outcome = .ok (.inl condition) →
      match condition with
      | .bool b =>
          cmpPhases15 result = [0, 1] ∧
          ∃ value final, result = .ok value final ∧
            (b = true → value = .integer cmpOne) ∧
            (b = false → value = .integer cmpZero)
      | .other c =>
          ∃ selected ∈ traceOf result,
            selected.event = .select (.other c)
              (.integer cmpOne) (.integer cmpZero)) ∧
  (∀ value final, result = .ok value final →
    2 ∈ cmpPhases15 result →
    ∃ selected ∈ traceOf result, selected.outcome = .ok (.inr value))

/-- Source: base/operators.jl:526, generic cmp. No ordering or Bool-return law
is imposed on either comparison callback. -/
def CmpProtocol : Prop :=
  ∀ (A B Cond Other S UserError : Type)
    (ops : CmpOps (EStateM (Error UserError) S) A B Cond Other)
    (x : A) (y : B) (initial : S),
    CmpShortControl15 initial () x y
      (JuliaLean.base.operators.Models2Group15.cmp
        (observeCmp15 ops) x y (initial, []))

/-- Source: base/operators.jl:534. Function-object identity is included in
every query observation, including the reversed argument order. -/
def CmpByProtocol : Prop :=
  ∀ (F A B Cond Other S UserError : Type)
    (ops : CmpByOps (EStateM (Error UserError) S) F A B Cond Other)
    (function : F) (x : A) (y : B) (initial : S),
    CmpShortControl15 initial function x y
      (JuliaLean.base.operators.Models2Group15.cmpBy
        (observeCmpBy15 ops) function x y (initial, []))

/-- Source: base/operators.jl:537. Both query results are evaluated before
selection, even for a true or non-Bool first result. Selection conditions and
branch values retain observed provenance; arbitrary ifelse results are not
restricted to signs. A Bool with a noninteger branch remains open dispatch. -/
def CmpIntegerProtocol : Prop :=
  ∀ (A B Cond Other S UserError : Type)
    (ops : CmpOps (EStateM (Error UserError) S) A B Cond Other)
    (x : A) (y : B) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.cmpInteger
      (observeCmp15 ops) x y (initial, [])
    CmpConservation15 initial () x y result ∧
    (∃ suffix, cmpPhases15 result ++ suffix = [0, 1, 2, 2]) ∧
    ErrorsHaveSource (fun _ _ => False) result ∧
    (∀ first ∈ traceOf result, first.event = .forward () x y →
      ∀ condition, first.outcome = .ok (.inl condition) →
        ∃ reverse ∈ traceOf result, reverse.event = .backward () y x) ∧
    (∀ value final, result = .ok value final →
      0 ∈ cmpPhases15 result ∧ 1 ∈ cmpPhases15 result) ∧
    (∀ (before : List (CallObservation (CmpCall15 Unit A B Cond Other) (Value Cond ⊕ CmpValue Other) S UserError))
      (call : CallObservation (CmpCall15 Unit A B Cond Other) (Value Cond ⊕ CmpValue Other) S UserError)
      (after : List (CallObservation (CmpCall15 Unit A B Cond Other) (Value Cond ⊕ CmpValue Other) S UserError))
      (condition : Value Cond) (yes no : CmpValue Other),
      traceOf result = before ++ call :: after →
      call.event = .select condition yes no →
      (∃ reverse ∈ before, reverse.event = .backward () y x) ∧
      (condition = .bool true ∨ condition = .bool false →
        (∃ other, yes = .other other) ∨ (∃ other, no = .other other))) ∧
    (∀ value final, result = .ok value final →
      (2 ∉ cmpPhases15 result) →
      value = .integer cmpMinusOne ∨ value = .integer cmpZero ∨
        value = .integer cmpOne)

/-- Narrow registered helper contract. Closed Bool/integer selection retains
one supplied branch and makes no effects; every open dispatch gets the actual
condition and both original branches, with one-call result/error forwarding. -/
def ChooseDispatchConservation : Prop :=
  ∀ (Cond Other S UserError : Type)
    (ops : IfelseOps (EStateM (Error UserError) S) Cond Other)
    (condition : Value Cond) (yes no : CmpValue Other) (initial : S),
    let observed := observeIfelse15 (F := Unit) (A := Unit) (B := Unit) ops
    let result := choose observed condition yes no (initial, [])
    match condition, yes, no with
    | .bool b, .integer a, .integer d =>
        traceOf result = [] ∧
        ∃ value, result = .ok value (initial, []) ∧
          (b = true → value = .integer a) ∧
          (b = false → value = .integer d)
    | _, _, _ =>
        OrderedProtocol initial some [.select condition yes no] result ∧
        ErrorsHaveSource (fun _ _ => False) result ∧
        (∀ value final, result = .ok value final →
          ∃ call ∈ traceOf result, call.outcome = .ok (.inr value))

/-- Source: base/operators.jl:588. minmax conserves both operand identities,
makes exactly one reversed comparison, and accepts only Bool at its branch.
Neither a total-order law nor comparison correctness is assumed. -/
def MinmaxConservation : Prop :=
  ∀ (A B Other S UserError : Type)
    (ops : MinmaxOps (EStateM (Error UserError) S) A B Other)
    (x : A) (y : B) (initial : S),
    let observed : MinmaxOps (Observed (B × A) (Value Other) S UserError)
      A B Other :=
      { lessBackward := fun b a => observeCall (b, a) (ops.lessBackward b a) }
    let result := JuliaLean.base.operators.Models2Group15.minmax
      observed x y (initial, [])
    let bad := fun (_ : B × A) (value : Value Other) =>
      match value with | .other _ => True | .bool _ => False
    OrderedProtocol initial some [(y, x)] result ∧
    AssertionIsTerminal bad result ∧ ErrorsHaveSource bad result ∧
    (∀ value final, result = .ok value final →
      (value = (Sum.inl x, Sum.inr y) ∨ value = (Sum.inr y, Sum.inl x)) ∧
      ∀ call ∈ traceOf result,
        (call.outcome = .ok (.bool false) →
          value = (Sum.inl x, Sum.inr y)) ∧
        (call.outcome = .ok (.bool true) →
          value = (Sum.inr y, Sum.inl x)))

end JuliaLean.Proofs.base.operators.Models2Group15

namespace JuliaLean.Proofs.base.operators

open JuliaLean.Registry

def Models2Group15.entriesCmp15 : List Entry := [
  { id := "operators-cmp-control-effects", juliaFile := "base/operators.jl",
    juliaFns := ["cmp(x, y)"], source := "base/operators.jl:526",
    statement := "Short cmp preserves operand identity, observable call order and state/error effects; its first Bool controls reverse-query reachability, and native signs or actual selection results are conserved.",
    status := .todo, prop := ``Models2Group15.CmpProtocol, thm := none },
  { id := "operators-cmpby-control-effects", juliaFile := "base/operators.jl",
    juliaFns := ["cmp(lt, x, y)"], source := "base/operators.jl:534",
    statement := "Comparator cmp additionally preserves the supplied comparator identity in both argument orders, with complete short-circuit, state, exception and result-origin observations.",
    status := .todo, prop := ``Models2Group15.CmpByProtocol, thm := none },
  { id := "operators-cmpinteger-eager-effects", juliaFile := "base/operators.jl",
    juliaFns := ["cmp(x::Integer, y::Integer)"], source := "base/operators.jl:537",
    statement := "Integer cmp evaluates both comparisons eagerly, preserves observed condition and branch provenance, retains arbitrary open-ifelse results/errors, and restricts signs only when no open selection was observed.",
    status := .todo, prop := ``Models2Group15.CmpIntegerProtocol, thm := none },
  { id := "operators-ifelse-dispatch-conservation", juliaFile := "base/operators.jl",
    juliaFns := ["ifelse dependency of cmp"], source := "base/operators.jl:526-537",
    statement := "Bool selection closes only for two native integer branches; all other condition/branch cases make one argument-preserving open dispatch and conserve its full state, error and result.",
    status := .todo, prop := ``Models2Group15.ChooseDispatchConservation, thm := none },
  { id := "operators-minmax-pair-conservation", juliaFile := "base/operators.jl",
    juliaFns := ["minmax(x, y)"], source := "base/operators.jl:588",
    statement := "minmax returns an identity-preserving permutation of its operands selected by one observed reversed Bool query, with exact failure origin and complete state continuity.",
    status := .todo, prop := ``Models2Group15.MinmaxConservation, thm := none }
]

end JuliaLean.Proofs.base.operators


/- Reconstructed independent fold properties after transient workspace loss.
   These declarations introduce no Julia implementation and no proofs.
   Append after PropertyDraft15's observation infrastructure. -/

namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple
open JuliaLean.base.operators.Models2Group15 (Arguments FoldOps NaryOperator)

/-- A binary call records actual operator, accumulator, and argument identities. -/
structure FoldCall (F V : Type) where
  function : F
  accumulator : V
  argument : V

abbrev FoldLog (F V S UserError : Type) :=
  CallObservation (FoldCall F V) V S UserError

abbrev FoldObserved (F V S UserError : Type) :=
  Observed (FoldCall F V) V S UserError

abbrev FoldRun (F V S UserError : Type) :=
  EStateM.Result (Error UserError) (S × List (FoldLog F V S UserError)) V

/-- The arbitrary action cannot access or forge the observer's private log.
Its exact returned value, error payload, and world transition are preserved. -/
def observedFoldOps {F V S UserError : Type}
    (ops : FoldOps (EStateM (Error UserError) S) F V) :
    FoldOps (FoldObserved F V S UserError) F V where
  apply function accumulator argument :=
    observeCall (FoldCall.mk function accumulator argument)
      (ops.apply function accumulator argument)

/-- Adjacent calls form an accumulator chain, starting at the original
accumulator. On success the last call supplies the returned object, or an
empty call sequence preserves the initial object. These are relations on
actual observations, not a second fold implementation or callee assumptions. -/
def FoldAccumulatorChain {F V S UserError : Type} (initial : V)
    (result : FoldRun F V S UserError) : Prop :=
  let trace := traceOf result
  (match trace with
   | [] => True
   | first :: _ => first.event.accumulator = initial) ∧
  (∀ (before after : List (FoldLog F V S UserError))
      (first second : FoldLog F V S UserError),
    trace = before ++ (first :: second :: after) →
    first.outcome = .ok second.event.accumulator) ∧
  (match result with
   | .error _ _ => True
   | .ok value _ =>
       match trace.getLast? with
       | none => value = initial
       | some last => last.outcome = .ok value)

/-- Calls form the ordered operator/argument word, completed on success.
WorldChain inside OrderedProtocol checks every state boundary; final world,
terminal failures, error provenance, and accumulator identity are independent
observations. No algebraic or correctness law of the binary method is assumed. -/
def FoldExecutionProtocol {F V S UserError : Type}
    (function : F) (initial : V) (arguments : List V) (world : S)
    (result : FoldRun F V S UserError) : Prop :=
  OrderedProtocol world
    (fun call : FoldCall F V => some (call.function, call.argument))
    (arguments.map (fun argument => (function, argument))) result ∧
  ErrorsHaveSource (fun _ _ => False) result ∧
  FoldAccumulatorChain initial result

/-- The complete unrolled-and-loop fold visits every supplied argument once
in order on success, threads each actual result as the next accumulator, and
preserves the last result's identity. The first selected-call error terminates
unchanged, including its world and arbitrary user exception payload. All
runtime-bounded argument packs, operators (including noncallable objects),
values, mutable worlds, and selected binary actions are quantified.
Julia source and internal design documentation: base/operators.jl:617-663
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:623-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function afoldl(op, a, bs...)
--     @_terminates_locally_meta
--     l = length(bs)
--     i =  0; y = a;            l == i && return y
--     #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
--     i =  1; y = op(y, bs[i]); l == i && return y
--     i =  2; y = op(y, bs[i]); l == i && return y
--     i =  3; y = op(y, bs[i]); l == i && return y
--     i =  4; y = op(y, bs[i]); l == i && return y
--     i =  5; y = op(y, bs[i]); l == i && return y
--     i =  6; y = op(y, bs[i]); l == i && return y
--     i =  7; y = op(y, bs[i]); l == i && return y
--     i =  8; y = op(y, bs[i]); l == i && return y
--     i =  9; y = op(y, bs[i]); l == i && return y
--     i = 10; y = op(y, bs[i]); l == i && return y
--     i = 11; y = op(y, bs[i]); l == i && return y
--     i = 12; y = op(y, bs[i]); l == i && return y
--     i = 13; y = op(y, bs[i]); l == i && return y
--     i = 14; y = op(y, bs[i]); l == i && return y
--     i = 15; y = op(y, bs[i]); l == i && return y
--     i = 16; y = op(y, bs[i]); l == i && return y
--     i = 17; y = op(y, bs[i]); l == i && return y
--     i = 18; y = op(y, bs[i]); l == i && return y
--     i = 19; y = op(y, bs[i]); l == i && return y
--     i = 20; y = op(y, bs[i]); l == i && return y
--     i = 21; y = op(y, bs[i]); l == i && return y
--     i = 22; y = op(y, bs[i]); l == i && return y
--     i = 23; y = op(y, bs[i]); l == i && return y
--     i = 24; y = op(y, bs[i]); l == i && return y
--     i = 25; y = op(y, bs[i]); l == i && return y
--     i = 26; y = op(y, bs[i]); l == i && return y
--     i = 27; y = op(y, bs[i]); l == i && return y
--     i = 28; y = op(y, bs[i]); l == i && return y
--     i = 29; y = op(y, bs[i]); l == i && return y
--     i = 30; y = op(y, bs[i]); l == i && return y
--     i = 31; y = op(y, bs[i]); l == i && return y
--     for i in (i + 1):l
--         y = op(y, bs[i])
--     end
--     return y
-- end
-- /Source
def AfoldlProtocol : Prop :=
  ∀ (F V S UserError : Type)
      (ops : FoldOps (EStateM (Error UserError) S) F V)
      (function : F) (initial : V) (arguments : Arguments V) (world : S),
    FoldExecutionProtocol function initial arguments.values world
      (JuliaLean.base.operators.Models2Group15.afoldlMany
        (observedFoldOps ops) function initial arguments (world, []))

/-- Every generated operator uses only ordered binary calls: b then c then
the remaining arguments, with a as the initial accumulator. Actual operation
results form the same identity-preserving chain. No associativity, commutativity,
purity, successful return, or callee correctness assumption is imposed.
All ten source operators, arbitrary heterogeneous runtime carriers and values,
bounded argument packs, states, and user exceptions are included.
Julia source and generator design documentation: base/operators.jl:666-676
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:666-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:+, :(+%), :*, :(*%), :&, :|, :xor, :min, :max, :kron)
--     @eval begin
--         # note: these definitions must not cause a dispatch loop when +(a,b) is
--         # not defined, and must only try to call 2-argument definitions, so
--         # that defining +(a,b) is sufficient for full functionality.
--         ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
--         # a further concern is that it's easy for a type like (Int,Int...)
--         # to match many definitions, so we need to keep the number of
--         # definitions down to avoid losing type information.
--     end
-- end
-- /Source
def GeneratedNaryProtocol : Prop :=
  ∀ (V S UserError : Type)
      (ops : FoldOps (EStateM (Error UserError) S) NaryOperator V)
      (operator : NaryOperator) (a b c : V) (arguments : Arguments V) (world : S),
    FoldExecutionProtocol operator a (b :: c :: arguments.values) world
      (JuliaLean.base.operators.Models2Group15.naryOperator
        (observedFoldOps ops) operator a b c arguments (world, []))

/-- Additive registry entries; the independent properties remain unproved. -/
def entriesFold15 : List JuliaLean.Registry.Entry := [
  { id := "operators-afoldl-ordered-accumulation", juliaFile := "base/operators.jl",
    juliaFns := ["afoldl(op, a, bs...)"],
    statement := "For every bounded argument pack and arbitrary effectful binary method, afoldl visits the original arguments once in order on success, threads actual accumulator identities, preserves every world transition and terminal error, and returns the last actual result or the initial accumulator for an empty pack.",
    source := "base/operators.jl:617-663; unrolled and loop branches share the ordered accumulation invariant",
    status := .todo, prop := ``AfoldlProtocol, thm := none },
  { id := "operators-generated-operators-binary-fold", juliaFile := "base/operators.jl",
    juliaFns := ["+(a, b, c, xs...)", "+%(a, b, c, xs...)",
      "*(a, b, c, xs...)", "*%(a, b, c, xs...)", "&(a, b, c, xs...)",
      "|(a, b, c, xs...)", "xor(a, b, c, xs...)", "min(a, b, c, xs...)",
      "max(a, b, c, xs...)", "kron(a, b, c, xs...)"],
    statement := "Each generated n-ary operator makes only ordered binary calls on b, c, and the remaining arguments; actual results form an accumulator chain beginning at a, with exact state/error propagation and returned-object conservation, without algebraic assumptions on the selected binary method.",
    source := "base/operators.jl:666-676; generator comment requires only two-argument calls",
    status := .todo, prop := ``GeneratedNaryProtocol, thm := none }
]

end JuliaLean.Proofs.base.operators.Models2Group15


namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple JuliaLean.base.operators.Models2Group15

/-- Argument-bearing observations of the two selected calls in mod1.
The remainder is deliberately independent of the original Real value type. -/
inductive Mod1Event (A Rem : Type) where
  | modulus (left right : A)
  | iszero (remainder : Rem)

inductive Mod1Phase where
  | modulus | iszero
  deriving DecidableEq

def mod1Phase {A Rem : Type} : Mod1Event A Rem → Option Mod1Phase
  | .modulus _ _ => some .modulus
  | .iszero _ => some .iszero

def observeMod1 {A Rem Other S UserError : Type}
    (ops : Mod1Ops (EStateM (Error UserError) S) A Rem Other) :
    Mod1Ops (Observed (Mod1Event A Rem) (Rem ⊕ Value Other) S UserError)
      A Rem Other where
  modulus left right :=
    comparisonObserveCall (.modulus left right) Sum.inl (ops.modulus left right)
  iszero remainder :=
    comparisonObserveCall (.iszero remainder) Sum.inr (ops.iszero remainder)

def mod1BadAssertion {A Rem Other : Type} :
    Mod1Event A Rem → Rem ⊕ Value Other → Prop
  | .iszero _, .inr (.other _) => True
  | _, _ => False

/-- mod1 conserves value identity: its output comes from the original divisor
or the actually observed remainder, and the observed Bool selects that origin.
The iszero argument must be a preceding modulus result. Both selected calls,
all result types, all state changes, and arbitrary exceptions are unrestricted;
the sole additional error is the reached non-Bool condition. No arithmetic law
of a custom mod/iszero implementation is assumed.
Julia source: base/operators.jl:914; documentation: base/operators.jl:890-913;
doc/src/manual/control-flow.md:181-190. -/
-- Source: base/operators.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mod1(x::T, y::T) where {T<:Real} = (m = mod(x, y); iszero(m) ? y : m)
-- /Source
def Mod1Conservation : Prop :=
  ∀ (A Rem Other S UserError : Type)
      (ops : Mod1Ops (EStateM (Error UserError) S) A Rem Other)
      (x y : A) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.mod1
      (observeMod1 ops) x y (initial, [])
    let trace := traceOf result
    OrderedProtocol initial mod1Phase [.modulus, .iszero] result ∧
    AssertionIsTerminal mod1BadAssertion result ∧
    ErrorsHaveSource mod1BadAssertion result ∧
    (∀ call ∈ trace, match call.event with
      | .modulus left right => left = x ∧ right = y
      | .iszero _ => True) ∧
    (∀ before call after remainder,
      trace = before ++ call :: after → call.event = .iszero remainder →
      ∃ origin ∈ before, origin.event = .modulus x y ∧
        origin.outcome = .ok (.inl remainder)) ∧
    (∀ value final, result = .ok value final →
      match value with
      | .inl divisor =>
          divisor = y ∧ ∃ test ∈ trace,
            test.outcome = .ok (.inr (.bool true))
      | .inr remainder =>
          (∃ origin ∈ trace, origin.event = .modulus x y ∧
            origin.outcome = .ok (.inl remainder)) ∧
          ∃ test ∈ trace, test.event = .iszero remainder ∧
            test.outcome = .ok (.inr (.bool false)))

/-- Distinguish the two quotient functions rather than treating the legacy
fldmod1 spelling as permission to substitute cld for fld1. -/
inductive QuotientPairEvent (A B : Type) where
  | cld (left : A) (right : B)
  | fld1 (left : A) (right : B)
  | mod1 (left : A) (right : B)

def observeCldmod {A B Quot Rem S UserError : Type}
    (ops : CldmodOps (EStateM (Error UserError) S) A B Quot Rem) :
    CldmodOps
      (Observed (QuotientPairEvent A B) (Quot ⊕ Rem) S UserError)
      A B Quot Rem where
  cld left right :=
    comparisonObserveCall (.cld left right) Sum.inl (ops.cld left right)
  mod1 left right :=
    comparisonObserveCall (.mod1 left right) Sum.inr (ops.mod1 left right)

def observeFldmod {A B Quot Rem S UserError : Type}
    (ops : FldmodOps (EStateM (Error UserError) S) A B Quot Rem) :
    FldmodOps
      (Observed (QuotientPairEvent A B) (Quot ⊕ Rem) S UserError)
      A B Quot Rem where
  fld1 left right :=
    comparisonObserveCall (.fld1 left right) Sum.inl (ops.fld1 left right)
  mod1 left right :=
    comparisonObserveCall (.mod1 left right) Sum.inr (ops.mod1 left right)

/-- Successful pair components conserve the two observed result identities.
An exceptional execution has a prefix of the argument word, stops at its
first observed exception, and retains every world transition. -/
def QuotientPairConservation {A B Quot Rem S UserError : Type}
    (initial : S) (quotientCall remainderCall : QuotientPairEvent A B)
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation (QuotientPairEvent A B) (Quot ⊕ Rem) S UserError))
      (Quot × Rem)) : Prop :=
  OrderedProtocol initial some [quotientCall, remainderCall] result ∧
  ErrorsHaveSource (fun _ _ => False) result ∧
  ∀ pair final, result = .ok pair final →
    ∃ first second, traceOf result = [first, second] ∧
      first.outcome = .ok (.inl pair.1) ∧
      second.outcome = .ok (.inr pair.2)

/-- cldmod1 preserves its quotient/remainder components, their original
arguments, and left-to-right effects. A first-call error prevents the second
call. The statement does not assume a numerical law for either callback.
Julia source/documentation: base/operators.jl:918-943. -/
-- Source: base/operators.jl:943-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cldmod1(x, y) = (cld(x, y), mod1(x, y))
-- /Source
def CldmodPairConservation : Prop :=
  ∀ (A B Quot Rem S UserError : Type)
      (ops : CldmodOps (EStateM (Error UserError) S) A B Quot Rem)
      (x : A) (y : B) (initial : S),
    QuotientPairConservation initial (.cld x y) (.mod1 x y)
      (JuliaLean.base.operators.Models2Group15.cldmod1
        (observeCldmod ops) x y (initial, []))

/-- fldmod1 conserves the observed fld1 and mod1 results in their original
positions, with the same exception/world invariant as cldmod1. The quotient
event is specifically fld1, regardless of docstring equivalence on integers.
Julia source/documentation: base/operators.jl:945-952. -/
-- Source: base/operators.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fldmod1(x, y) = (fld1(x, y), mod1(x, y))
-- /Source
def FldmodPairConservation : Prop :=
  ∀ (A B Quot Rem S UserError : Type)
      (ops : FldmodOps (EStateM (Error UserError) S) A B Quot Rem)
      (x : A) (y : B) (initial : S),
    QuotientPairConservation initial (.fld1 x y) (.mod1 x y)
      (JuliaLean.base.operators.Models2Group15.fldmod1
        (observeFldmod ops) x y (initial, []))

/-- A conversion event includes the original type-indexed input. The widened
target has no Type assertion because the Julia expression has none. -/
inductive WidenEvent (Ty : Type) (Values : Ty → Type) (Widened : Type) where
  | widen (type : Ty)
  | convert (type : Ty) (target : Widened) (value : Values type)

inductive WidenPhase where
  | widen | convert
  deriving DecidableEq

def widenPhase {Ty Widened : Type} {Values : Ty → Type} :
    WidenEvent Ty Values Widened → Option WidenPhase
  | .widen _ => some .widen
  | .convert _ _ _ => some .convert

def observeWiden {Ty Widened R S UserError : Type} {Values : Ty → Type}
    (ops : WidenOps (EStateM (Error UserError) S) Ty Values Widened R) :
    WidenOps
      (Observed (WidenEvent Ty Values Widened) (Widened ⊕ R) S UserError)
      Ty Values Widened R where
  widenType type :=
    comparisonObserveCall (.widen type) Sum.inl (ops.widenType type)
  convert := fun {T} target value =>
    comparisonObserveCall (.convert T target value) Sum.inr
      (ops.convert (T := T) target value)

/-- The conversion target has a preceding widen(T) result as provenance,
while its value argument is the unchanged original input. The final value is
the observed conversion result. This checks data flow, exact dispatch
arguments, state continuity, and error transparency without requiring widen
to return a type or convert to satisfy a correctness law.
Julia source: base/operators.jl:975; documentation: base/operators.jl:954-974;
doc/src/manual/conversion-and-promotion.md:52-53. -/
-- Source: base/operators.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::T) where {T} = convert(widen(T), x)
-- /Source
def WidenValueProvenance : Prop :=
  ∀ (Ty Widened R S UserError : Type) (Values : Ty → Type)
      (ops : WidenOps (EStateM (Error UserError) S) Ty Values Widened R)
      (T : Ty) (x : Values T) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.widenValue
      (observeWiden ops) T x (initial, [])
    let trace := traceOf result
    OrderedProtocol initial widenPhase [.widen, .convert] result ∧
    ErrorsHaveSource (fun _ _ => False) result ∧
    (∀ call ∈ trace, match call.event with
      | .widen type => type = T
      | .convert _ _ _ => True) ∧
    (∀ (before : List (CallObservation (WidenEvent Ty Values Widened) (Widened ⊕ R) S UserError))
      (call : CallObservation (WidenEvent Ty Values Widened) (Widened ⊕ R) S UserError)
      (after : List (CallObservation (WidenEvent Ty Values Widened) (Widened ⊕ R) S UserError)),
      trace = before ++ call :: after →
      widenPhase call.event = some .convert →
      ∃ target, call.event = .convert T target x ∧
        ∃ origin ∈ before, origin.event = .widen T ∧
          origin.outcome = .ok (.inl target)) ∧
    (∀ value final, result = .ok value final →
      ∃ call, trace.getLast? = some call ∧ call.outcome = .ok (.inr value))

/-- A rejected widening cannot run an arbitrary effectful continuation.
This frame and reachability invariant additionally checks the fixed exception
class/function without equating the model to a duplicate throw expression. -/
def WidenRejectionFrame {R Out S UserError : Type} (initial : S)
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation R Out S UserError)) Out) : Prop :=
  traceOf result = [] ∧
  (resultState result).1 = initial ∧
  ¬ resultSucceeded result ∧
  resultError result = some (.inl (.julia (.methodError "widen")))

/-- Every selected Type fallback rejects before any continuation or world
effect, retaining MethodError(widen) in the arbitrary user exception domain.
The attempted continuation is unrestricted, so an accidental return is
observable even when its value would otherwise go unused.
Julia source: base/operators.jl:976. -/
-- Source: base/operators.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::Type{T}) where {T} = throw(MethodError(widen, (T,)))
-- /Source
def WidenTypeRejectionFrame : Prop :=
  ∀ (Ty R Out S UserError : Type) (T : Ty)
      (continuation : R → EStateM (Error UserError) S Out) (initial : S),
    let action : Observed R Out S UserError Out := do
      let value ← JuliaLean.base.operators.Models2Group15.widenTypeError T
      comparisonObserveCall value id (continuation value)
    WidenRejectionFrame initial (action (initial, []))

/-- The bottom fallback is a state-preserving rejection for every
constructible trailing tuple. No continuation can observe a value or run
effects, irrespective of the ignored trailing values and their types.
Julia source: base/operators.jl:977. -/
-- Source: base/operators.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::Type{Union{}}, slurp...) = throw(MethodError(widen, (Union{},)))
-- /Source
def WidenBottomRejectionFrame : Prop :=
  ∀ (Arg R Out S UserError : Type) (bottom : Unit) (slurp : Arguments Arg)
      (continuation : R → EStateM (Error UserError) S Out) (initial : S),
    let action : Observed R Out S UserError Out := do
      let value ← JuliaLean.base.operators.Models2Group15.widenBottomError bottom slurp
      comparisonObserveCall value id (continuation value)
    WidenRejectionFrame initial (action (initial, []))

/-- The installed pipe is polymorphic enough to retain arbitrary effectful
application. It makes one call on the original argument and preserves that
call's entire value/error/world outcome. This independently checks the public
piping promise without imposing a law on the supplied callable.
Julia source: base/operators.jl:1001; documentation:
doc/src/manual/functions.md:1031-1043. -/
-- Source: base/operators.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- |>(x, f) = f(x)
-- /Source
def PipeEffectForwarding : Prop :=
  ∀ (A R S UserError : Type) (f : A → EStateM (Error UserError) S R)
      (x : A) (initial : S),
    let result := JuliaLean.base.operators.pipe x
      (fun argument => comparisonObserveCall argument id (f argument)) (initial, [])
    ComparisonForwardProtocol x initial result

/-- Erase object contents while retaining the outer runtime constructor and
every explicit runtime tag. This is a perturbation of input data, not a second
implementation of typeof; no expected type is computed here. -/
def eraseStablePayload : JuliaLean.C.Val → JuliaLean.C.Val
  | .datatype _ _ => .datatype "" []
  | .union _ _ => .union .bottom .bottom
  | .intersect _ _ => .intersect .bottom .bottom
  | .typeeq _ => .typeeq .bottom
  | .typeegal _ => .typeegal .bottom
  | .unionall _ _ _ _ _ => .unionall 0 "" .bottom .bottom .bottom
  | .typevar _ _ _ _ => .typevar 0 "" .bottom .bottom
  | .vararg _ _ => .vararg none none
  | .bottom => .bottom
  | .typeapp _ _ => .typeapp .bottom .bottom
  | .long _ => .long 0
  | .symbol _ => .symbol ""
  | .bits tag _ => .bits tag 0
  | .imm tag _ => .imm tag []
  | .mutableRef tag _ => .mutableRef tag 0
  | .module _ => .module ""

/-- Changing data, addresses, type parameters, or type-variable identities
without changing a runtime constructor/tag cannot change generic stable
typeof. Explicitly tagged primitive, immutable, and mutable values agree on
their retained tag, so a constant or payload-dependent answer is falsifiable.
The property quantifies over the complete installed runtime value domain.
Julia source: base/operators.jl:1003; documentation:
doc/src/manual/types.md:40-47; installed primitive src/julia_h.lean typeOf. -/
-- Source: base/operators.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _stable_typeof(x) = typeof(x)
-- /Source
def StableTypePayloadErasure : Prop :=
  (∀ x : JuliaLean.C.Val,
    JuliaLean.base.operators.Models2Group15.stableTypeof (eraseStablePayload x) =
      JuliaLean.base.operators.Models2Group15.stableTypeof x) ∧
  (∀ (tag : JuliaLean.C.Val) (bits : Int)
      (fields : Arguments JuliaLean.C.Val) (address : UInt64),
    JuliaLean.base.operators.Models2Group15.stableTypeof (.bits tag bits) = tag ∧
    JuliaLean.base.operators.Models2Group15.stableTypeof (.imm tag fields.values) = tag ∧
    JuliaLean.base.operators.Models2Group15.stableTypeof (.mutableRef tag address) = tag)

/-- Dependent conversion arguments and outcomes keep their actual field type.
This allows fields with abstract or union admission as well as concrete ones. -/
abbrev ConstructorArgument (Ty : Type) (Invalid : Ty → Type) :=
  Σ T : Ty, Invalid T

abbrev ConstructorDatum (Ty : Type) (Values Invalid : Ty → Type) :=
  Σ T : Ty, FieldValue (Values T) (Invalid T)

def observeReturnsConstructor {Ty S UserError : Type} {Values Invalid : Ty → Type}
    (ops : ReturnsConstructorOps (EStateM (Error UserError) S) Ty Values Invalid) :
    ReturnsConstructorOps
      (Observed (ConstructorArgument Ty Invalid) (ConstructorDatum Ty Values Invalid)
        S UserError) Ty Values Invalid where
  convert T value :=
    comparisonObserveCall ⟨T, value⟩ (fun returned => ⟨T, returned⟩)
      (ops.convert T value)

def constructorRejected {Ty : Type} {Values Invalid : Ty → Type}
    (_event : ConstructorArgument Ty Invalid)
    (value : ConstructorDatum Ty Values Invalid) : Prop :=
  match value.2 with
  | .accepted _ => False
  | .rejected _ => True

/-- Accepted constructor input bypasses every conversion and retains its
identity. Otherwise exactly one selected conversion is observed, with the
actual requested field type and original rejected input. A successful stored
value has that conversion's accepted result as its origin. The concrete new
check rejects every other result only after its conversion effects occur.
Julia source: base/operators.jl:1031; field conversion evidence:
base/essentials.jl:1468-1488; doc/src/manual/conversion-and-promotion.md:101-110. -/
-- Source: base/operators.jl:1031-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Returns{V}(value) where {V} = new{V}(value)
-- /Source
def ReturnsTypedAdmission : Prop :=
  ∀ (Ty S UserError : Type) (Values Invalid : Ty → Type)
      (ops : ReturnsConstructorOps (EStateM (Error UserError) S) Ty Values Invalid)
      (T : Ty) (input : FieldValue (Values T) (Invalid T)) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.returnsTyped
      (observeReturnsConstructor ops) T input (initial, [])
    let trace := traceOf result
    ComparisonWorldChain initial trace ∧
    WorldConservation initial result ∧ FailureIsTerminal result ∧
    AssertionIsTerminal constructorRejected result ∧
    ErrorsHaveSource constructorRejected result ∧
    (∀ returned final, result = .ok returned final → returned.typeParam = T) ∧
    (match input with
      | .accepted original =>
          trace = [] ∧ resultSucceeded result ∧
          ∀ returned final, result = .ok returned final → returned.value = original
      | .rejected original =>
          trace.map (fun call => call.event) = [⟨T, original⟩] ∧
          ∀ returned final, result = .ok returned final →
            ∃ call ∈ trace, call.outcome = .ok ⟨T, .accepted returned.value⟩)

/-- Returns calls are total and observationally insensitive to every argument,
keyword container, and stored type tag. Comparing calls distinguishes exactly
their stored values, even across different argument/keyword representations.
This is an extensionality and erasure law, rather than the accessor body
restated as an expected answer. Tuple sizes are constructible native values.
Julia source: base/operators.jl:1035; documentation: base/operators.jl:1006-1028. -/
-- Source: base/operators.jl:1035-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (obj::Returns)(@nospecialize(args...); @nospecialize(kw...)) = obj.value
-- /Source
def ReturnsCallExtensionality : Prop :=
  ∀ (Tag₁ Tag₂ V Arg₁ Arg₂ Kw₁ Kw₂ : Type)
      (left : JuliaLean.base.operators.Returns Tag₁ V)
      (right : JuliaLean.base.operators.Returns Tag₂ V)
      (args₁ : Arguments Arg₁) (args₂ : Arguments Arg₂) (kw₁ : Kw₁) (kw₂ : Kw₂),
    (∃ value, JuliaLean.base.operators.returnsCall left args₁.values kw₁ = .ok value) ∧
    (JuliaLean.base.operators.returnsCall left args₁.values kw₁ =
      JuliaLean.base.operators.returnsCall left args₂.values kw₂) ∧
    (JuliaLean.base.operators.returnsCall left args₁.values kw₁ =
      JuliaLean.base.operators.returnsCall right args₂.values kw₂ ↔
      left.value = right.value)

/-- Only originally non-admitted fields require a selected conversion.
This argument word specifies observable calls, not constructed output values. -/
def fieldConversionWord {Ty : Type} {Values Invalid : Ty → Type} (T : Ty) :
    FieldValue (Values T) (Invalid T) → List (ConstructorArgument Ty Invalid)
  | .accepted _ => []
  | .rejected original => [⟨T, original⟩]

def observeComposedConstructor {Ty S UserError : Type} {Values Invalid : Ty → Type}
    (ops : ComposedConstructorOps (EStateM (Error UserError) S) Ty Values Invalid) :
    ComposedConstructorOps
      (Observed (ConstructorArgument Ty Invalid) (ConstructorDatum Ty Values Invalid)
        S UserError) Ty Values Invalid where
  convert T value :=
    comparisonObserveCall ⟨T, value⟩ (fun returned => ⟨T, returned⟩)
      (ops.convert T value)

/-- A stored field retains either its admitted original or the accepted value
from its own conversion position. A conversion of the other field cannot
supply its value, even when both field types and input values coincide. -/
def StoredFieldOrigin {Ty S UserError : Type} {Values Invalid : Ty → Type}
    (T : Ty) (input : FieldValue (Values T) (Invalid T))
    (call : Option (CallObservation (ConstructorArgument Ty Invalid)
      (ConstructorDatum Ty Values Invalid) S UserError)) (stored : Values T) : Prop :=
  match input with
  | .accepted original => stored = original
  | .rejected _ =>
      ∃ observed, call = some observed ∧ observed.outcome = .ok ⟨T, .accepted stored⟩

/-- Both field expressions are prepared before the concrete new checks.
Consequently an ordinary but inadmissible outer conversion result cannot
suppress inner conversion; only an actual selected-call exception may stop
the conversion word early. Each successful field retains its own original
or observed converted identity. Conversion exceptions take precedence over
later field checks and preserve all mutation, including on failing runs.
Julia source: base/operators.jl:1121; field conversion evidence:
base/essentials.jl:1468-1488; doc/src/manual/conversion-and-promotion.md:101-110. -/
-- Source: base/operators.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ComposedFunction{O, I}(outer, inner) where {O, I} = new{O, I}(outer, inner)
-- /Source
def ComposedTypedPreparation : Prop :=
  ∀ (Ty S UserError : Type) (Values Invalid : Ty → Type)
      (ops : ComposedConstructorOps (EStateM (Error UserError) S) Ty Values Invalid)
      (O I : Ty) (outer : FieldValue (Values O) (Invalid O))
      (inner : FieldValue (Values I) (Invalid I)) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.composedTyped
      (observeComposedConstructor ops) O I outer inner (initial, [])
    let trace := traceOf result
    let required := fieldConversionWord O outer ++ fieldConversionWord I inner
    let noDispatchFailure :=
      ¬ ∃ call ∈ trace, ∃ error, call.outcome = .error error
    OrderedProtocol initial some required result ∧
    ErrorsHaveSource constructorRejected result ∧
    (noDispatchFailure → trace.map (fun call => call.event) = required) ∧
    (noDispatchFailure →
      (∃ call ∈ trace, ∃ returned,
        call.outcome = .ok returned ∧ constructorRejected call.event returned) →
      resultError result = some (.inl .typeError)) ∧
    (∀ returned final, result = .ok returned final →
      StoredFieldOrigin O outer ((trace)[0]?) returned.outer ∧
      StoredFieldOrigin I inner ((trace)[(fieldConversionWord O outer).length]?) returned.inner)

private theorem pairTraceDecomposition {A : Type} (first second : A)
    (before after : List A) (call : A) (trace : [first, second] = before ++ call :: after) :
    (before = [] ∧ call = first ∧ after = [second]) ∨
    (before = [first] ∧ call = second ∧ after = []) := by
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at trace
    exact Or.inl ⟨rfl, trace.1.symm, trace.2.symm⟩
  | cons head rest =>
    simp only [List.cons_append, List.cons.injEq] at trace
    obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition rest after call second trace.2
    exact Or.inr ⟨by rw [trace.1], rfl, rfl⟩

private theorem quotientPairSequence {A B Quot Rem S U : Type}
    (firstEvent secondEvent : QuotientPairEvent A B)
    (first : EStateM (Error U) S Quot) (second : EStateM (Error U) S Rem) (initial : S) :
    let action : Observed (QuotientPairEvent A B) (Quot ⊕ Rem) S U (Quot × Rem) := do
      let q ← comparisonObserveCall firstEvent Sum.inl first
      let r ← comparisonObserveCall secondEvent Sum.inr second
      pure (q, r)
    QuotientPairConservation initial firstEvent secondEvent (action (initial, [])) := by
  cases firstRun : first initial with
  | error error after =>
    simp only [comparisonObserveCall, firstRun, List.nil_append, bind, EStateM.bind]
    refine ⟨⟨⟨[secondEvent], rfl⟩, ?_, ⟨rfl, True.intro⟩, rfl, ?_⟩, ?_, ?_⟩
    · intro impossible
      cases impossible
    · intro before later call error' trace outcome
      obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition before later call _ trace
      exact ⟨rfl, congrArg some (Except.error.inj outcome)⟩
    · intro error' outcome
      exact Or.inl ⟨_, List.mem_singleton_self _,
        congrArg Except.error (Option.some.inj outcome)⟩
    · intro pair final impossible
      cases impossible
  | ok q middle =>
    cases secondRun : second middle with
    | error error after =>
      simp only [comparisonObserveCall, firstRun, secondRun, List.nil_append,
        bind, EStateM.bind]
      refine ⟨⟨⟨[], rfl⟩, ?_, ⟨rfl, rfl, True.intro⟩, rfl, ?_⟩, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro before later call error' trace outcome
        rcases pairTraceDecomposition _ _ before later call trace with h | h
        · rcases h with ⟨rfl, rfl, rfl⟩
          cases outcome
        · rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, congrArg some (Except.error.inj outcome)⟩
      · intro error' outcome
        exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
          congrArg Except.error (Option.some.inj outcome)⟩
      · intro pair final impossible
        cases impossible
    | ok r after =>
      simp only [comparisonObserveCall, firstRun, secondRun, List.nil_append,
        bind, EStateM.bind, pure, EStateM.pure]
      refine ⟨⟨⟨[], rfl⟩, (fun _ => rfl), ⟨rfl, rfl, True.intro⟩, rfl, ?_⟩, ?_, ?_⟩
      · intro before later call error trace outcome
        rcases pairTraceDecomposition _ _ before later call trace with h | h <;>
          rcases h with ⟨rfl, rfl, rfl⟩ <;> cases outcome
      · intro error outcome
        cases outcome
      · intro pair final outcome
        cases outcome
        exact ⟨_, _, rfl, rfl, rfl⟩

theorem cldmodPairConservation_proven : CldmodPairConservation := by
  intro A B Quot Rem S U ops x y initial
  exact quotientPairSequence (.cld x y) (.mod1 x y) (ops.cld x y) (ops.mod1 x y) initial

theorem fldmodPairConservation_proven : FldmodPairConservation := by
  intro A B Quot Rem S U ops x y initial
  exact quotientPairSequence (.fld1 x y) (.mod1 x y) (ops.fld1 x y) (ops.mod1 x y) initial

theorem stableTypePayloadErasure_proven : StableTypePayloadErasure := by
  constructor
  · intro x; cases x <;> rfl
  · intros; exact ⟨rfl, rfl, rfl⟩

theorem returnsCallExtensionality_proven : ReturnsCallExtensionality := by
  intro Tag₁ Tag₂ V Arg₁ Arg₂ Kw₁ Kw₂ left right args₁ args₂ kw₁ kw₂
  refine ⟨⟨left.value, rfl⟩, rfl, ?_⟩
  exact ⟨Except.ok.inj, congrArg Except.ok⟩

theorem pipeEffectForwarding_proven : PipeEffectForwarding := by
  intro A R S U f x initial
  exact observeCall_forward x (f x) initial

theorem widenTypeRejectionFrame_proven : WidenTypeRejectionFrame := by
  intro Ty R Out S U T continuation initial
  exact ⟨rfl, rfl, fun h => h, rfl⟩

theorem widenBottomRejectionFrame_proven : WidenBottomRejectionFrame := by
  intro Arg R Out S U bottom slurp continuation initial
  exact ⟨rfl, rfl, fun h => h, rfl⟩

end JuliaLean.Proofs.base.operators.Models2Group15

namespace JuliaLean.Proofs.base.operators

open JuliaLean.Registry

def Models2Group15.entriesPostShift15 : List Entry := [
  { id := "operators-mod1-value-conservation", juliaFile := "base/operators.jl",
    juliaFns := ["mod1(x::T, y::T) where {T<:Real}"],
    statement := "mod1 sends the actual modulus result to iszero and conserves either the original divisor or that remainder according to the observed Bool, with exact call arguments/order, no intermediate world writes, terminal arbitrary dispatch errors, and TypeError only for a reached non-Bool condition.",
    source := "base/operators.jl:890-914; doc/src/manual/control-flow.md:181-190",
    status := .todo, prop := ``Models2Group15.Mod1Conservation, thm := none,
    notes := "No modulus or iszero correctness laws; the remainder type is unrestricted. Depends on the installed mod1 composition and the registered assertBool behavior." },
  { id := "operators-cldmod1-pair-conservation", juliaFile := "base/operators.jl",
    juliaFns := ["cldmod1(x, y)"],
    statement := "cldmod1 makes the ordered cld/mod1 calls on the original arguments, preserves their result identities as the two tuple components, and stops at the first selected exception while retaining all state changes.",
    source := "base/operators.jl:918-943",
    status := .proven, prop := ``Models2Group15.CldmodPairConservation, thm := some ``JuliaLean.Proofs.base.operators.Models2Group15.cldmodPairConservation_proven },
  { id := "operators-fldmod1-pair-conservation", juliaFile := "base/operators.jl",
    juliaFns := ["fldmod1(x, y)"],
    statement := "fldmod1 specifically selects fld1 followed by mod1 with unchanged operands; successful tuple components preserve those observed results, and every exception and world transition is transparent.",
    source := "base/operators.jl:945-952",
    status := .proven, prop := ``Models2Group15.FldmodPairConservation, thm := some ``JuliaLean.Proofs.base.operators.Models2Group15.fldmodPairConservation_proven,
    notes := "The invariant preserves the actual fld1 dispatch rather than assuming docstring equivalence to cld." },
  { id := "operators-widen-value-provenance", juliaFile := "base/operators.jl",
    juliaFns := ["widen(x::T) where {T}"],
    statement := "Value widening queries its static parameter T, passes the observed unrestricted target and unchanged input to convert, and forwards the actual conversion result with all state/error effects; every conversion target has a preceding widen result as provenance.",
    source := "base/operators.jl:954-975; doc/src/manual/conversion-and-promotion.md:52-53",
    status := .todo, prop := ``Models2Group15.WidenValueProvenance, thm := none },
  { id := "operators-widen-type-rejection-frame", juliaFile := "base/operators.jl",
    juliaFns := ["widen(x::Type{T}) where {T}"],
    statement := "The selected Type fallback raises MethodError(widen) for every type parameter without changing the world or reaching any arbitrary effectful continuation.",
    source := "base/operators.jl:976",
    status := .proven, prop := ``Models2Group15.WidenTypeRejectionFrame, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.widenTypeRejectionFrame_proven },
  { id := "operators-widen-bottom-rejection-frame", juliaFile := "base/operators.jl",
    juliaFns := ["widen(x::Type{Union{}}, slurp...)"],
    statement := "The bottom-type fallback rejects with MethodError(widen), preserving the world and preventing every continuation for all constructible trailing tuples and all trailing value types.",
    source := "base/operators.jl:977",
    status := .proven, prop := ``Models2Group15.WidenBottomRejectionFrame, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.widenBottomRejectionFrame_proven },
  { id := "operators-pipe-effect-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["|>(x, f)"],
    statement := "The reused pipe makes exactly one application to the original argument and preserves the selected callable's complete result, arbitrary exception, and state transitions.",
    source := "base/operators.jl:1001; doc/src/manual/functions.md:1031-1043",
    status := .proven, prop := ``Models2Group15.PipeEffectForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.pipeEffectForwarding_proven,
    notes := "Reuses JuliaLean.base.operators.pipe; instantiating its polymorphic result with an effectful computation retains the complete selected-call domain." },
  { id := "operators-stable-type-payload-erasure", juliaFile := "base/operators.jl",
    juliaFns := ["_stable_typeof(x)"],
    statement := "Generic stable typeof is invariant under erasing payloads and object addresses while retaining runtime constructor/tag, and it preserves the explicit type tag of primitive, immutable, and mutable values.",
    source := "base/operators.jl:1003; doc/src/manual/types.md:40-47; installed src/julia_h.lean typeOf",
    status := .proven, prop := ``Models2Group15.StableTypePayloadErasure, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.stableTypePayloadErasure_proven,
    notes := "All installed C.Val constructors are quantified, including type-object kinds. Uses the installed concrete runtime typeof, without a typeOf callback." },
  { id := "operators-returns-typed-admission", juliaFile := "base/operators.jl",
    juliaFns := ["Returns{V}(value) where {V}"],
    statement := "Typed Returns construction retains an admitted original without conversion, otherwise makes one conversion with unchanged type/input, stores only its admitted observed value, and preserves effects/errors before a concrete field TypeError when admission fails.",
    source := "base/operators.jl:1031; base/essentials.jl:1468-1488; doc/src/manual/conversion-and-promotion.md:101-110",
    status := .todo, prop := ``Models2Group15.ReturnsTypedAdmission, thm := none,
    notes := "Admission includes abstract, union, and Any field types; no law constrains custom conversion results or exceptions." },
  { id := "operators-returns-call-extensionality", juliaFile := "base/operators.jl",
    juliaFns := ["(obj::Returns)(@nospecialize(args...); @nospecialize(kw...))"],
    statement := "Returns calls always succeed, ignore all positional arguments, keyword containers, and type tags, and give equal results exactly when the stored values agree, across arbitrary argument representations and constructible tuple lengths.",
    source := "base/operators.jl:1006-1028,1035",
    status := .proven, prop := ``Models2Group15.ReturnsCallExtensionality, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.returnsCallExtensionality_proven,
    notes := "Reuses JuliaLean.base.operators.returnsCall; the property is an extensionality/erasure law rather than the getter expression repeated as its result." },
  { id := "operators-composed-typed-preparation", juliaFile := "base/operators.jl",
    juliaFns := ["ComposedFunction{O, I}(outer, inner) where {O, I}"],
    statement := "Typed ComposedFunction prepares needed outer and inner conversions in order before field checks, keeps admitted originals and each field's own observed conversion value, and lets only an actual conversion exception truncate preparation; a wrong-type outer result still permits inner conversion and its effects/errors.",
    source := "base/operators.jl:1121; base/essentials.jl:1468-1488; doc/src/manual/conversion-and-promotion.md:101-110",
    status := .todo, prop := ``Models2Group15.ComposedTypedPreparation, thm := none,
    notes := "No conversion correctness laws. Arbitrary world and user exceptions remain observable; assertion checks are deliberately deferred until both field expressions have been prepared." }
]

end JuliaLean.Proofs.base.operators


namespace JuliaLean.Proofs.base.operators.Models2Group15

open JuliaLean JuliaLean.base.tuple JuliaLean.base.operators.Models2Group15

/-- Observe the fallback's selected maybeconstructor call without restricting
its return type, values, mutation, or exceptions. -/
def observeUnwrapFallback {C R S UserError : Type}
    (ops : UnwrapFallbackOps (EStateM (Error UserError) S) C R) :
    UnwrapFallbackOps (Observed C R S UserError) C R where
  maybeconstructor value := observeCall value (ops.maybeconstructor value)

/-- Fallback unwrapping makes a singleton whose element is an observed
maybeconstructor result. The sole selected call receives the unchanged input;
its exception terminates evaluation and its world transition is preserved.
No correctness law is assumed for custom maybeconstructor dispatch.
Julia source: base/operators.jl:1127. -/
-- Source: base/operators.jl:1127-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unwrap_composed(c) = (maybeconstructor(c),)
-- /Source
def UnwrapFallbackSingleton : Prop :=
  ∀ (C R S UserError : Type)
      (ops : UnwrapFallbackOps (EStateM (Error UserError) S) C R)
      (input : C) (initial : S),
    let result := JuliaLean.base.operators.Models2Group15.unwrapFallback
      (observeUnwrapFallback ops) input (initial, [])
    OrderedProtocol initial some [input] result ∧
    ErrorsHaveSource (fun _ _ => False) result ∧
    (∀ values final, result = .ok values final →
      values.length = 1 ∧
      ∀ value ∈ values, ∃ call ∈ traceOf result, call.outcome = .ok value)

/-- Abstract package representations retain heterogeneous positional tuples
and keyword containers, with their original identity. -/
structure ConstructorCallEvent (T Args Kw : Type) where
  type : T
  args : Args
  kw : Kw

/-- The adapter makes one call on its stored type parameter and unchanged
positional/keyword packages, forwarding the full result/error/world outcome.
Julia source: base/operators.jl:1132; documentation:
doc/src/manual/functions.md (varargs and keyword arguments). -/
-- Source: base/operators.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Constructor{F})(args...; kw...) where {F} = (@inline; F(args...; kw...))
-- /Source
def ConstructorCallForwarding : Prop :=
  ∀ (T Args Kw R S UserError : Type)
      (construct : T → Args → Kw → EStateM (Error UserError) S R)
      (adapter : JuliaLean.base.operators.Constructor T)
      (args : Args) (kw : Kw) (initial : S),
    let observed := fun type arguments keywords =>
      observeCall (ConstructorCallEvent.mk type arguments keywords)
        (construct type arguments keywords)
    let result := JuliaLean.base.operators.constructorCall observed adapter args kw
      (initial, [])
    ComparisonForwardProtocol (ConstructorCallEvent.mk adapter.type args kw) initial result

/-- Type adaptation preserves the original type as the target of every later
constructor invocation, checked through arbitrary effectful calls. The model
is not equated to a repeated structure-construction expression.
Julia source: base/operators.jl:1133, with its call method at 1132. -/
-- Source: base/operators.jl:1133-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- maybeconstructor(::Type{F}) where {F} = Constructor{F}()
-- /Source
def ConstructorTypeAdaptation : Prop :=
  ∀ (T Args Kw R S UserError : Type)
      (construct : T → Args → Kw → EStateM (Error UserError) S R)
      (type : T) (args : Args) (kw : Kw) (initial : S),
    let observed := fun selected arguments keywords =>
      observeCall (ConstructorCallEvent.mk selected arguments keywords)
        (construct selected arguments keywords)
    let adapter := JuliaLean.base.operators.maybeConstructorType type
    let result := JuliaLean.base.operators.constructorCall observed adapter args kw
      (initial, [])
    ComparisonForwardProtocol (ConstructorCallEvent.mk type args kw) initial result

/-- Losslessness and stability jointly exclude every nonidentity permutation
or constant replacement, without restating a normalization's body. -/
def LosslessIdempotent {A : Type} (normalize : A → A) : Prop :=
  (∀ left right, normalize left = normalize right ↔ left = right) ∧
  (∀ value, normalize (normalize value) = normalize value)

/-- Generic maybeconstructor is stable under reapplication and never
identifies different original values, over its entire unrestricted domain.
Julia source: base/operators.jl:1134. -/
-- Source: base/operators.jl:1134-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- maybeconstructor(f) = f
-- /Source
def MaybeConstructorValueIdentityLaws : Prop :=
  ∀ A : Type,
    LosslessIdempotent (JuliaLean.base.operators.maybeConstructorValue (α := A))

/-- Unary composition loses no distinctions and is stable on reapplication.
No callability restriction is imposed on its operand type.
Julia source: base/operators.jl:1136; documentation:
doc/src/manual/functions.md:1000-1043. -/
-- Source: base/operators.jl:1136-1136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ∘(f) = f
-- /Source
def ComposeOneIdentityLaws : Prop :=
  ∀ A : Type, LosslessIdempotent (JuliaLean.base.operators.composeOne (α := A))

def observeComposeTwo {F G R S UserError : Type}
    (ops : ComposeTwoOps (EStateM (Error UserError) S) F G R) :
    ComposeTwoOps (Observed (F × G) R S UserError) F G R where
  construct outer inner := observeCall (outer, inner) (ops.construct outer inner)

/-- Binary composition preserves the ordered original operands in its sole
constructor call, retaining arbitrary results, errors, and state changes.
No assumption forces that result to be a ComposedFunction.
Julia source: base/operators.jl:1137; documentation:
doc/src/manual/functions.md:1000-1043. -/
-- Source: base/operators.jl:1137-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ∘(f, g) = ComposedFunction(f, g)
-- /Source
def ComposeTwoForwarding : Prop :=
  ∀ (F G R S UserError : Type)
      (ops : ComposeTwoOps (EStateM (Error UserError) S) F G R)
      (outer : F) (inner : G) (initial : S),
    ComparisonForwardProtocol (outer, inner) initial
      (JuliaLean.base.operators.Models2Group15.composeTwo
        (observeComposeTwo ops) outer inner (initial, []))

/-- Distinct selected display operations retain the original IO reference
and value arguments independently of their arbitrary results. -/
inductive CompositionDisplayEvent (IO V : Type) where
  | print (io : IO) (character : Char)
  | showValue (io : IO) (value : V)
  | showPart (io : IO) (value : V)

/-- The final outcome comes from the last selected call even when its
successful value is recorded in a heterogeneous observation sum. -/
def EncodedLastOutcome {Event Recorded R S UserError : Type}
    (encode : R → Recorded)
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation Event Recorded S UserError)) R) : Prop :=
  match result with
  | .ok value _ =>
      ∃ call, (traceOf result).getLast? = some call ∧ call.outcome = .ok (encode value)
  | .error error _ =>
      ∃ call, (traceOf result).getLast? = some call ∧ call.outcome = .error error

/-- Fixed display sequences conserve their call arguments, all state
transitions, and the final outcome; only selected calls may raise an error. -/
def DisplaySequenceProtocol {Event Recorded R S UserError : Type}
    (initial : S) (word : List Event) (encode : R → Recorded)
    (result : EStateM.Result (Error UserError)
      (S × List (CallObservation Event Recorded S UserError)) R) : Prop :=
  OrderedProtocol initial some word result ∧
  ErrorsHaveSource (fun _ _ => False) result ∧
  EncodedLastOutcome encode result

def observeShowNegated {IO Inner Printed R S UserError : Type}
    (ops : ShowNegatedOps (EStateM (Error UserError) S) IO Inner Printed R) :
    ShowNegatedOps
      (Observed (CompositionDisplayEvent IO Inner) (Printed ⊕ R) S UserError)
      IO Inner Printed R where
  printChar io character :=
    comparisonObserveCall (.print io character) Sum.inl (ops.printChar io character)
  showPart io value :=
    comparisonObserveCall (.showPart io value) Sum.inr (ops.showPart io value)

/-- Negated composition prints ! before showing its inner field, retaining
one IO identity despite arbitrary print results. The final show-part result
and every exception/world transition are preserved. Unit represents the
fixed canonical ! singleton, not an arbitrary outer function.
Julia source: base/operators.jl:1147-1150. -/
-- Source: base/operators.jl:1147-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, c::ComposedFunction{typeof(!)})
--     print(io, '!')
--     _showcomposed(io, c.inner)
-- end
-- /Source
def ShowNegatedIOProtocol : Prop :=
  ∀ (IO Inner Printed R S UserError : Type)
      (ops : ShowNegatedOps (EStateM (Error UserError) S) IO Inner Printed R)
      (io : IO) (value : JuliaLean.base.operators.ComposedFunction Unit Inner)
      (initial : S),
    DisplaySequenceProtocol initial
      [CompositionDisplayEvent.print io '!', CompositionDisplayEvent.showPart io value.inner] Sum.inr
      (JuliaLean.base.operators.Models2Group15.showNegatedComposed
        (observeShowNegated ops) io value (initial, []))

def observeShowValue {IO V R S UserError : Type}
    (ops : ShowValueOps (EStateM (Error UserError) S) IO V R) :
    ShowValueOps (Observed (CompositionDisplayEvent IO V) R S UserError) IO V R where
  «show» io value := observeCall (.showValue io value) (ops.«show» io value)

/-- Fallback _showcomposed forwards its original IO/value pair to one show
call and preserves the entire selected result/error/world outcome.
Julia source: base/operators.jl:1152. -/
-- Source: base/operators.jl:1152-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, x) = show(io, x)
-- /Source
def ShowComposedFallbackForwarding : Prop :=
  ∀ (IO V R S UserError : Type)
      (ops : ShowValueOps (EStateM (Error UserError) S) IO V R)
      (io : IO) (value : V) (initial : S),
    ComparisonForwardProtocol (CompositionDisplayEvent.showValue io value) initial
      (JuliaLean.base.operators.Models2Group15.showComposedDefault
        (observeShowValue ops) io value (initial, []))

def observeShowNested {IO Outer Inner Shown Printed S UserError : Type}
    (ops : ShowNestedOps (EStateM (Error UserError) S) IO Outer Inner Shown Printed) :
    ShowNestedOps
      (Observed
        (CompositionDisplayEvent IO (JuliaLean.base.operators.ComposedFunction Outer Inner))
        (Printed ⊕ Shown) S UserError) IO Outer Inner Shown Printed where
  printChar io character :=
    comparisonObserveCall (.print io character) Sum.inl (ops.printChar io character)
  «show» io value :=
    comparisonObserveCall (.showValue io value) Sum.inr (ops.«show» io value)

/-- Parenthesized display uses the same IO for opening print, selected show,
and closing print, ignoring intermediate return values and preserving the
closing print's actual result. Each exception stops the sequence and retains
its originating state, including mutation performed before throwing.
Julia source: base/operators.jl:1156. -/
-- Source: base/operators.jl:1156-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, f::ComposedFunction) = (print(io, '('); show(io, f); print(io, ')'))
-- /Source
def ShowNestedIOProtocol : Prop :=
  ∀ (IO Outer Inner Shown Printed S UserError : Type)
      (ops : ShowNestedOps (EStateM (Error UserError) S) IO Outer Inner Shown Printed)
      (io : IO) (value : JuliaLean.base.operators.ComposedFunction Outer Inner)
      (initial : S),
    DisplaySequenceProtocol initial
      [CompositionDisplayEvent.print io '(', CompositionDisplayEvent.showValue io value,
        CompositionDisplayEvent.print io ')'] Sum.inl
      (JuliaLean.base.operators.Models2Group15.showNestedComposed
        (observeShowNested ops) io value (initial, []))

/-- Nested negated display makes one selected show call with the original IO
and composed value, preserving its full outcome without parenthesis calls.
The fixed outer ! singleton is Unit; all inner types remain unrestricted.
Julia source: base/operators.jl:1158. -/
-- Source: base/operators.jl:1158-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _showcomposed(io::IO, f::ComposedFunction{typeof(!)}) = show(io, f)
-- /Source
def ShowNestedNegatedForwarding : Prop :=
  ∀ (IO Inner R S UserError : Type)
      (ops : ShowValueOps (EStateM (Error UserError) S) IO
        (JuliaLean.base.operators.ComposedFunction Unit Inner) R)
      (io : IO) (value : JuliaLean.base.operators.ComposedFunction Unit Inner)
      (initial : S),
    ComparisonForwardProtocol (CompositionDisplayEvent.showValue io value) initial
      (JuliaLean.base.operators.Models2Group15.showNestedNegatedComposed
        (observeShowValue ops) io value (initial, []))

def observeNegateFunction {F R S UserError : Type}
    (ops : NegateFunctionOps (EStateM (Error UserError) S) F R) :
    NegateFunctionOps (Observed (Unit × F) R S UserError) F R where
  compose canonicalNot function :=
    observeCall (canonicalNot, function) (ops.compose canonicalNot function)

/-- Function negation makes one selected composition call on canonical ! and
the unchanged function, preserving arbitrary results, errors, and state. No
boolean-correctness or constructor-result law is assumed for custom dispatch.
Julia source: base/operators.jl:1182; documentation: base/operators.jl:1160-1181. -/
-- Source: base/operators.jl:1182-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !(f::Function) = (!) ∘ f
-- /Source
def NegateFunctionForwarding : Prop :=
  ∀ (F R S UserError : Type)
      (ops : NegateFunctionOps (EStateM (Error UserError) S) F R)
      (function : F) (initial : S),
    ComparisonForwardProtocol ((), function) initial
      (JuliaLean.base.operators.Models2Group15.negateFunction
        (observeNegateFunction ops) function (initial, []))

/-- Removing canonical negation is lossless on its inner values, and
re-embedding/removing again is stable. These algebraic laws characterize
identity recovery without repeating the getter expression. Unit is precisely
the singleton carrier for canonical !; every inner value type is quantified.
Julia source: base/operators.jl:1183, explicitly promising !!f === f. -/
-- Source: base/operators.jl:1183-1183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- !(f::ComposedFunction{typeof(!)}) = f.inner #allows !!f === f
-- /Source
def DoubleNegationIdentityLaws : Prop :=
  ∀ Inner : Type,
    LosslessIdempotent (fun inner : Inner =>
      JuliaLean.base.operators.doubleNegatedComposition
        (⟨(), inner⟩ : JuliaLean.base.operators.ComposedFunction Unit Inner))

theorem maybeConstructorValueIdentityLaws_proven : MaybeConstructorValueIdentityLaws := by
  intro A
  exact ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

theorem composeOneIdentityLaws_proven : ComposeOneIdentityLaws := by
  intro A
  exact ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

theorem doubleNegationIdentityLaws_proven : DoubleNegationIdentityLaws := by
  intro A
  exact ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

theorem constructorCallForwarding_proven : ConstructorCallForwarding := by
  intro T Args Kw R S U construct adapter args kw initial
  exact observeCall_forward _ _ _

theorem constructorTypeAdaptation_proven : ConstructorTypeAdaptation := by
  intro T Args Kw R S U construct type args kw initial
  exact observeCall_forward _ _ _

theorem composeTwoForwarding_proven : ComposeTwoForwarding := by
  intro F G R S U ops outer inner initial
  exact observeCall_forward _ _ _

theorem negateFunctionForwarding_proven : NegateFunctionForwarding := by
  intro F R S U ops f initial
  exact observeCall_forward _ _ _

theorem showComposedFallbackForwarding_proven : ShowComposedFallbackForwarding := by
  intro IO V R S U ops io value initial
  exact observeCall_forward _ _ _

theorem showNestedNegatedForwarding_proven : ShowNestedNegatedForwarding := by
  intro IO Inner R S U ops io value initial
  exact observeCall_forward _ _ _

theorem unwrapFallbackSingleton_proven : UnwrapFallbackSingleton := by
  intro C R S U ops input initial
  cases ha : ops.maybeconstructor input initial with
  | ok value after =>
    simp only [JuliaLean.base.operators.Models2Group15.unwrapFallback,
      observeUnwrapFallback, observeCall, bind, pure, EStateM.bind, EStateM.pure, ha,
      List.nil_append]
    refine ⟨⟨⟨[], rfl⟩, fun _ => rfl, ⟨rfl, True.intro⟩, rfl, ?_⟩, ?_, ?_⟩
    · intro before later call error h he
      obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition before later call _ h
      contradiction
    · intro error h; contradiction
    · intro values final h
      cases h
      refine ⟨rfl, ?_⟩
      intro v hv
      simp only [List.mem_singleton] at hv
      subst v
      exact ⟨⟨input, .ok value, initial, after⟩, List.mem_singleton_self _, rfl⟩
  | error error after =>
    simp only [JuliaLean.base.operators.Models2Group15.unwrapFallback,
      observeUnwrapFallback, observeCall, bind, pure, EStateM.bind, EStateM.pure, ha,
      List.nil_append]
    refine ⟨⟨⟨[], rfl⟩, ?_, ⟨rfl, True.intro⟩, rfl, ?_⟩, ?_, ?_⟩
    · intro h; contradiction
    · intro before later call e h he
      obtain ⟨rfl, rfl, rfl⟩ := singleton_decomposition before later call _ h
      exact ⟨rfl, congrArg some (Except.error.inj he)⟩
    · intro e h
      exact Or.inl ⟨⟨input, .error error, initial, after⟩, List.mem_singleton_self _,
        congrArg Except.error (Option.some.inj h)⟩
    · intro values final h; contradiction

end JuliaLean.Proofs.base.operators.Models2Group15

namespace JuliaLean.Proofs.base.operators

open JuliaLean.Registry

def Models2Group15.entriesCallable15 : List Entry := [
  { id := "operators-unwrap-fallback-singleton", juliaFile := "base/operators.jl",
    juliaFns := ["unwrap_composed(c)"],
    statement := "Fallback unwrapping makes one maybeconstructor call on the original input, returns a singleton containing its observed result, and preserves terminal arbitrary exceptions and every state transition.",
    source := "base/operators.jl:1127",
    status := .proven, prop := ``Models2Group15.UnwrapFallbackSingleton,
    thm := ``Models2Group15.unwrapFallbackSingleton_proven },
  { id := "operators-constructor-call-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["(::Constructor{F})(args...; kw...) where {F}"],
    statement := "Constructor invocation forwards its stored type and original positional/keyword packages to one selected call, preserving its complete result, arbitrary exception, and state transition.",
    source := "base/operators.jl:1132; doc/src/manual/functions.md (varargs and keyword arguments)",
    status := .proven, prop := ``Models2Group15.ConstructorCallForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.constructorCallForwarding_proven,
    notes := "Reuses constructorCall with an effectful result and abstract tuple/keyword representations." },
  { id := "operators-constructor-type-adaptation", juliaFile := "base/operators.jl",
    juliaFns := ["maybeconstructor(::Type{F}) where {F}"],
    statement := "Type adaptation preserves that exact type as the target of subsequent effectful invocation, with unchanged arguments, arbitrary return values, exceptions, and state changes.",
    source := "base/operators.jl:1132-1133",
    status := .proven, prop := ``Models2Group15.ConstructorTypeAdaptation, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.constructorTypeAdaptation_proven,
    notes := "Reuses maybeConstructorType and constructorCall without constructor correctness laws." },
  { id := "operators-maybeconstructor-value-identity", juliaFile := "base/operators.jl",
    juliaFns := ["maybeconstructor(f)"],
    statement := "Generic maybeconstructor is stable on reapplication and preserves all distinctions between original inputs, excluding lossy replacements and nonidentity permutations.",
    source := "base/operators.jl:1134",
    status := .proven, prop := ``Models2Group15.MaybeConstructorValueIdentityLaws, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.maybeConstructorValueIdentityLaws_proven,
    notes := "Reuses maybeConstructorValue over its complete polymorphic domain." },
  { id := "operators-compose-one-identity", juliaFile := "base/operators.jl",
    juliaFns := ["∘(f)"],
    statement := "Unary composition loses no operand distinctions and is stable on reapplication, over every operand type without a callability precondition.",
    source := "base/operators.jl:1136; doc/src/manual/functions.md:1000-1043",
    status := .proven, prop := ``Models2Group15.ComposeOneIdentityLaws, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.composeOneIdentityLaws_proven,
    notes := "Reuses composeOne; independent losslessness and idempotence jointly characterize identity." },
  { id := "operators-compose-two-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["∘(f, g)"],
    statement := "Binary composition makes one selected constructor call on the original ordered operands and preserves its unrestricted value, arbitrary exception, and world transition.",
    source := "base/operators.jl:1137; doc/src/manual/functions.md:1000-1043",
    status := .proven, prop := ``Models2Group15.ComposeTwoForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.composeTwoForwarding_proven },
  { id := "operators-show-negated-io", juliaFile := "base/operators.jl",
    juliaFns := ["show(io::IO, c::ComposedFunction{typeof(!)})"],
    statement := "Negated composition prints ! then shows the original inner field through _showcomposed, retaining the same IO despite arbitrary print results and forwarding the final outcome with all errors and state changes.",
    source := "base/operators.jl:1147-1150",
    status := .todo, prop := ``Models2Group15.ShowNegatedIOProtocol, thm := none,
    notes := "Unit fixes canonical !; IO, inner field, print result, and final result remain unrestricted." },
  { id := "operators-showcomposed-fallback-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["_showcomposed(io::IO, x)"],
    statement := "Fallback _showcomposed forwards the original IO/value pair to one show call and preserves its entire outcome without requiring an IO-valued return.",
    source := "base/operators.jl:1152",
    status := .proven, prop := ``Models2Group15.ShowComposedFallbackForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.showComposedFallbackForwarding_proven },
  { id := "operators-show-nested-io", juliaFile := "base/operators.jl",
    juliaFns := ["_showcomposed(io::IO, f::ComposedFunction)"],
    statement := "Nested composition brackets selected show with opening/closing prints on the same IO, ignores arbitrary intermediate return values, and returns the closing print's observed outcome while preserving early errors and mutation.",
    source := "base/operators.jl:1156",
    status := .todo, prop := ``Models2Group15.ShowNestedIOProtocol, thm := none },
  { id := "operators-show-nested-negated-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["_showcomposed(io::IO, f::ComposedFunction{typeof(!)})"],
    statement := "Nested negated display forwards its exact IO and composed value to one show call, preserving its unrestricted outcome and all state changes without extra print calls.",
    source := "base/operators.jl:1158",
    status := .proven, prop := ``Models2Group15.ShowNestedNegatedForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.showNestedNegatedForwarding_proven },
  { id := "operators-negate-function-forwarding", juliaFile := "base/operators.jl",
    juliaFns := ["!(f::Function)"],
    statement := "Function negation forwards canonical ! and the original function in order to one selected composition call, preserving arbitrary results, exceptions, and state changes.",
    source := "base/operators.jl:1160-1182",
    status := .proven, prop := ``Models2Group15.NegateFunctionForwarding, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.negateFunctionForwarding_proven,
    notes := "No correctness or ComposedFunction-result law is assumed for custom composition." },
  { id := "operators-double-negation-identity", juliaFile := "base/operators.jl",
    juliaFns := ["!(f::ComposedFunction{typeof(!)})"],
    statement := "Removing canonical negation is lossless on all inner values and stable under re-embedding/removing again, independently characterizing recovery of the original inner value.",
    source := "base/operators.jl:1183 (explicit !!f === f promise)",
    status := .proven, prop := ``Models2Group15.DoubleNegationIdentityLaws, thm := ``JuliaLean.Proofs.base.operators.Models2Group15.doubleNegationIdentityLaws_proven,
    notes := "Reuses doubleNegatedComposition with the source method's canonical ! singleton; all inner value types remain quantified." }
]

end JuliaLean.Proofs.base.operators

namespace JuliaLean.Proofs.base.operators

def entriesModels2Group15 : List JuliaLean.Registry.Entry :=
  Models2Group15.entriesInitial15 ++
  Models2Group15.entriesComparison15 ++
  Models2Group15.entriesPure15 ++
  Models2Group15.entriesCmp15 ++
  Models2Group15.entriesFold15 ++
  Models2Group15.entriesPostShift15 ++
  Models2Group15.entriesCallable15

end JuliaLean.Proofs.base.operators
