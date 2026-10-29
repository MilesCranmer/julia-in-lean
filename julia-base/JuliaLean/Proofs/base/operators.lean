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

/-- The source `isless(x::AbstractFloat, y::AbstractFloat)` on IEEE floats is the sign-magnitude
total order with NaNs last (`Fl.isless`). -/
theorem islessFloatFloat_eq_isless {T : FTy} (x y : FV T) :
    JuliaLean.base.operators.islessFloatFloat (JuliaLean.base.float.isnan_callee (T := T))
      (JuliaLean.base.float.signbit_float (T := T))
      (JuliaLean.base.float.lt_IEEEFloat (T := T)) x y =
    JuliaLean.Promotion.Fl.isless x y := by
  simp only [JuliaLean.base.operators.islessFloatFloat, JuliaLean.base.operators.signless,
    JuliaLean.base.operators.UnaryPredPair.onLeft, JuliaLean.base.operators.UnaryPredPair.onRight,
    JuliaLean.Proofs.base.float.isnan_callee_eq, JuliaLean.Proofs.base.float.signbit_float_eq,
    JuliaLean.Proofs.base.float.lt_IEEEFloat_eq]
  obtain ⟨hx, hmx⟩ := JuliaLean.Promotion.Fl.bits_split x
  obtain ⟨hy, hmy⟩ := JuliaLean.Promotion.Fl.bits_split y
  unfold JuliaLean.Promotion.Fl.lt JuliaLean.Promotion.Fl.isless JuliaLean.Promotion.Fl.iszero
  cases hnx : x.isnan <;> cases hny : y.isnan <;> cases sx : x.signbit <;>
    cases sy : y.signbit <;>
    simp only [JuliaLean.base.operators.bitAnd, JuliaLean.base.operators.bitOr,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or,
      Bool.false_eq_true, ite_true, ite_false] <;>
    rw [hx, hy] <;> simp [sx, sy] <;> split <;> simp_all <;> omega

/-- `min` and `max` return the minimum and maximum with respect to `isless` (docstrings of
`min(x, y, ...)` and `max(x, y, ...)`). With the source `isless(x::AbstractFloat,
y::AbstractFloat)` on every IEEE format, including NaN payloads and signed zeros, `min(x, y)` is
one of its arguments that neither argument is `isless`-below, `max(x, y)` one that neither
argument is `isless`-above, and since NaN sorts last, `min(NaN, y) = y` and `max(NaN, y) = NaN`
for every non-NaN `y`. -/
def MinMaxIsless : Prop :=
  ∀ (T : FTy) (x y : FV T),
    let lt := JuliaLean.base.operators.islessFloatFloat
      (JuliaLean.base.float.isnan_callee (T := T))
      (JuliaLean.base.float.signbit_float (T := T))
      (JuliaLean.base.float.lt_IEEEFloat (T := T))
    let mn := JuliaLean.base.operators.min lt JuliaLean.base.operators.ifelseValue x y
    let mx := JuliaLean.base.operators.max lt JuliaLean.base.operators.ifelseValue x y
    (mn = x ∨ mn = y) ∧ lt x mn = false ∧ lt y mn = false ∧
    (mx = x ∨ mx = y) ∧ lt mx x = false ∧ lt mx y = false ∧
    (x.isnan = true → y.isnan = false → mn = y ∧ mx = x)

theorem minMaxIsless_proven : MinMaxIsless := by
  intro T x y lt mn mx
  have hlt : ∀ a b : FV T, lt a b = JuliaLean.Promotion.Fl.isless a b :=
    fun a b => islessFloatFloat_eq_isless a b
  have hirr : ∀ a : FV T, lt a a = false := by
    intro a
    rw [hlt]
    unfold JuliaLean.Promotion.Fl.isless
    cases a.isnan <;> simp
  have hasym : ∀ a b : FV T, lt a b = true → lt b a = false := by
    intro a b hab
    cases hba : lt b a
    · rfl
    · have h := JuliaLean.Proofs.base.float.islessTransitive_proven T a b a
      rw [JuliaLean.Proofs.base.float.isless_IEEEFloat_eq,
        JuliaLean.Proofs.base.float.isless_IEEEFloat_eq,
        JuliaLean.Proofs.base.float.isless_IEEEFloat_eq, ← hlt, ← hlt, ← hlt, hirr] at h
      exact absurd (h hab hba) (by simp)
  have hmn : mn = JuliaLean.base.operators.ifelseValue (lt y x) y x := rfl
  have hmx : mx = JuliaLean.base.operators.ifelseValue (lt y x) x y := rfl
  cases hyx : lt y x
  · have e1 : mn = x := by simp [hmn, hyx, JuliaLean.base.operators.ifelseValue]
    have e2 : mx = y := by simp [hmx, hyx, JuliaLean.base.operators.ifelseValue]
    rw [e1, e2]
    refine ⟨Or.inl rfl, hirr x, hyx, Or.inr rfl, hyx, hirr y, ?_⟩
    intro hx hy
    have : JuliaLean.Promotion.Fl.isless y x = true := by
      unfold JuliaLean.Promotion.Fl.isless; simp [hx, hy]
    rw [← hlt, hyx] at this
    exact absurd this (by simp)
  · have e1 : mn = y := by simp [hmn, hyx, JuliaLean.base.operators.ifelseValue]
    have e2 : mx = x := by simp [hmx, hyx, JuliaLean.base.operators.ifelseValue]
    rw [e1, e2]
    exact ⟨Or.inr rfl, hasym y x hyx, hirr y, Or.inl rfl, hirr x, hasym y x hyx,
      fun _ _ => ⟨rfl, rfl⟩⟩

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

/-- Across both same-format and mixed-format `AbstractFloat` pairs (`Float16`, `Float32`,
`Float64`), with IEEE `<` returning `false` on `NaN`, `isless` orders `NaN` above finite
values and `isequal` treats any two `NaN`s as equal. -/
def FloatNaNSemantics : Prop :=
  (∀ (T : FTy) (x y : FV T),
    (x.isnan = false → y.isnan = true →
      islessFloatFloat
        (JuliaLean.base.float.isnan_callee (T := T))
        (JuliaLean.base.float.signbit_float (T := T))
        (JuliaLean.base.float.lt_IEEEFloat (T := T)) x y = true) ∧
    (x.isnan = true → y.isnan = true →
      isequalFloatFloat
        (JuliaLean.base.float.isnan_callee (T := T))
        (JuliaLean.base.float.signbit_float (T := T))
        (JuliaLean.base.float.eq_IEEEFloat (T := T)) x y = true) ∧
    (x.isnan = true → y.isnan = false →
      JuliaLean.base.float.lt_IEEEFloat (T := T) x y = false →
      islessFloatFloat
        (JuliaLean.base.float.isnan_callee (T := T))
        (JuliaLean.base.float.signbit_float (T := T))
        (JuliaLean.base.float.lt_IEEEFloat (T := T)) x y = false)) ∧
  (∀ (S T : FTy) (x : FV S) (y : FV T)
      (eqMixed ltMixed : FV S → FV T → Bool),
    let nanPair := (JuliaLean.base.float.isnan_callee (T := S), JuliaLean.base.float.isnan_callee (T := T))
    let signPair := (JuliaLean.base.float.signbit_float (T := S), JuliaLean.base.float.signbit_float (T := T))
    (x.isnan = false → y.isnan = true →
      islessFloatFloat nanPair signPair ltMixed x y = true) ∧
    (x.isnan = true → y.isnan = true →
      isequalFloatFloat nanPair signPair eqMixed x y = true) ∧
    (x.isnan = true → y.isnan = false → ltMixed x y = false →
      islessFloatFloat nanPair signPair ltMixed x y = false))

theorem floatNaNSemantics_proven : FloatNaNSemantics := by
  constructor
  · intro T x y
    refine ⟨?_, ?_, ?_⟩
    · intro hx hy
      simp [islessFloatFloat, signless, JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy]
    · intro hx hy
      simp [isequalFloatFloat, signequal, JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy]
    · intro hx hy hlt
      simp [islessFloatFloat, signless, JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy, hlt]
  · intro S T x y eqMixed ltMixed nanPair signPair
    refine ⟨?_, ?_, ?_⟩
    · intro hx hy
      simp [islessFloatFloat, signless, nanPair, signPair,
        JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy]
    · intro hx hy
      simp [isequalFloatFloat, signequal, nanPair, signPair,
        JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy]
    · intro hx hy hlt
      simp [islessFloatFloat, signless, nanPair, signPair,
        JuliaLean.Proofs.base.float.isnan_callee_eq, hx, hy, hlt]

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

/-- `minmax` agrees with separately computed `min` and `max` across arbitrary distinct
operand types `α` and `β`, and on mixed-width `BitInteger`s orders the two values while
preserving their mathematical sum. -/
def MinmaxCoherent : Prop :=
  (∀ (α β : Type) (lt : β → α → Bool)
      (chooseMin : Bool → β → α → α ⊕ β)
      (chooseMax : Bool → α → β → α ⊕ β) (x : α) (y : β),
    (∀ c b a, chooseMin c b a = if c then .inr b else .inl a) →
    (∀ c a b, chooseMax c a b = if c then .inl a else .inr b) →
    minmax lt x y = (JuliaLean.base.operators.min lt chooseMin x y,
      JuliaLean.base.operators.max lt chooseMax x y) ∧
    (minmax lt x y = (.inl x, .inr y) ∨ minmax lt x y = (.inr y, .inl x))) ∧
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    let pair := minmax (islessReal JuliaLean.base.int.lt) x y
    let val : JInt s ⊕ JInt t → Int := Sum.elim (·.val) (·.val)
    val pair.1 ≤ val pair.2 ∧ val pair.1 + val pair.2 = x.val + y.val) ∧
  (∀ (t : IntTy) (x y : JInt t),
    let lt := islessReal (JuliaLean.base.int.lt (s := t) (t := t))
    let mn := JuliaLean.base.operators.min lt JuliaLean.base.operators.ifelseValue x y
    let mx := JuliaLean.base.operators.max lt JuliaLean.base.operators.ifelseValue x y
    mn.val ≤ x.val ∧ mn.val ≤ y.val ∧ (mn = x ∨ mn = y) ∧
    x.val ≤ mx.val ∧ y.val ≤ mx.val ∧ (mx = x ∨ mx = y) ∧
    mn.val ≤ mx.val ∧ mn.val + mx.val = x.val + y.val)

theorem minmaxCoherent_proven : MinmaxCoherent := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β lt chooseMin chooseMax x y hMin hMax
    cases hlt : lt y x <;>
      simp [minmax, JuliaLean.base.operators.min, JuliaLean.base.operators.max, hMin, hMax, hlt]
  · intro s t x y
    simp only [minmax, islessReal, JuliaLean.Proofs.base.int.lt_eq]
    by_cases h : y.val < x.val <;> simp [h] <;> omega
  · intro t x y
    simp only [JuliaLean.base.operators.min, JuliaLean.base.operators.max,
      ifelseValue_eq, islessReal, JuliaLean.Proofs.base.int.lt_eq]
    by_cases h : y.val < x.val <;> simp [h] <;> omega

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
propagates before `f` runs. `ComposedFunction{O,I}(f, g)` behaves as `ComposedFunction(f, g)`,
`f ∘ g === ComposedFunction(f, g)`, and both store `f` and `g` as `outer` and `inner`. -/
def CompositionApplication : Prop :=
  ∀ (F T V σ : Type) (m : CallMethods F T V σ) (f g : Callee F T)
    (x : List V) (kw : List (σ × V)),
    callCallee m (.composed (composeTwo f g)) x kw =
      (do let v ← callCallee m g x kw; callCallee m f [v] []) ∧
    callCallee m (.composed (composedTyped f g)) x kw =
      callCallee m (.composed (composeTwo f g)) x kw ∧
    composeTwo f g = composed f g ∧
    (composed f g).outer = f ∧ (composed f g).inner = g ∧
    (composedTyped f g).outer = f ∧ (composedTyped f g).inner = g ∧
    (∀ t : T, callCallee m (.composed (composeTwo (.plain (.type t)) g)) x kw =
      (do let v ← callCallee m g x kw; m.callType t [v] []))

theorem compositionApplication_proven : CompositionApplication := by
  intro F T V σ m f g x kw
  refine ⟨callCallee_composeTwo m f g x kw, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro t
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
docstring), its `value` field is `x`, `Returns(x)` stores `_stable_typeof(x)` as its type
parameter, equal results identify the stored value, and `Returns(x) ∘ g` returns `x` once any
callable `g` (including types and nested compositions) succeeds and propagates `g`'s error. -/
def ReturnsCallContract : Prop :=
  ∀ (τ V σ T : Type) (callType : T → List V → List (σ × V) → Jl V) (tag : τ)
    (typeOf : V → τ) (x y : V) (args : List V) (kw : List (σ × V))
    (g : Callee (Returns τ V) T),
    let m : CallMethods (Returns τ V) T V σ := ⟨returnsCall, callType⟩
    returnsCall (returnsTyped tag x) args kw = .ok x ∧
    returnsCall (returnsStable (stableTypeof typeOf) x) args kw = .ok x ∧
    (returnsStable (stableTypeof typeOf) x).value = x ∧
    (returnsStable (stableTypeof typeOf) x).typeParam = typeOf x ∧
    (returnsCall (returnsTyped tag x) args kw = returnsCall (returnsTyped tag y) args kw ↔
      x = y) ∧
    callCallee m (.composed (composeTwo (.plain (.fn (returnsTyped tag x))) g)) args kw =
      (do let _ ← callCallee m g args kw; pure x)

theorem returnsCallContract_proven : ReturnsCallContract := by
  intro τ V σ T callType tag typeOf x y args kw g m
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · constructor
    · intro h
      simpa [returnsCall, returnsTyped] using h
    · intro h; subst h; rfl
  · rw [callCallee_composeTwo]
    rfl

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
      let value ← getindexInteger args (.integer .i64 (JInt.lit .i64 x))
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
  (r = zero → mod1 mod iszero x y = .ok y) ∧
  (∀ result, mod1 mod iszero x y = .ok result →
    (lt zero y → lt zero result ∧ le result y) ∧
    (lt y zero → le y result ∧ lt result zero))

theorem mod1ZeroRemainder_proven : Mod1ZeroRemainder := by
  intro A mod iszero zero lt le x y r hm hz hn hp hneg
  by_cases hr : r = zero
  · have hi := hz.mpr hr
    have hout : mod1 mod iszero x y = .ok y := by
      simp [mod1, hm, hi, Bind.bind, Except.bind]
    refine ⟨fun _ => hout, ?_⟩
    intro result hresult
    have : result = y := by simpa [hout] using hresult.symm
    subst result
    exact ⟨fun h => ⟨h, (hp h).1⟩, fun h => ⟨(hneg h).1,h⟩⟩
  · have hi := hn.mpr hr
    have hout : mod1 mod iszero x y = .ok r := by
      simp [mod1, hm, hi, Bind.bind, Except.bind]
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
  cldmod1 cld (mod1 mod iszero) x y = fldmod1 fld1 (mod1 mod iszero) x y ∧
  (∀ pair,
    (cldmod1 cld (mod1 mod iszero) x y = .ok pair ∨
      fldmod1 fld1 (mod1 mod iszero) x y = .ok pair) →
    val x = (pair.1 - 1) * val y + val pair.2 ∧
    0 < val pair.2 ∧ val pair.2 ≤ val y ∧
    val pair.2 = (if val m = 0 then val y else val m))

theorem divisionPairProjection_proven : DivisionPairProjection := by
  intro A cld fld1 mod iszero val x y m qf hy hm hmb hrecon hz hn hcld hfld
  by_cases hm0 : val m = 0
  · have hi : iszero m = .ok true := hz.mpr hm0
    have hmod1 : mod1 mod iszero x y = .ok y := by
      simp [mod1, hm, hi, Bind.bind, Except.bind]
    have hc : cldmod1 cld (mod1 mod iszero) x y = .ok (qf, y) := by
      simp [cldmod1, hcld, hm0, hmod1, Bind.bind, Except.bind]
    have hf : fldmod1 fld1 (mod1 mod iszero) x y = .ok (qf, y) := by
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
    have hmod1 : mod1 mod iszero x y = .ok m := by
      simp [mod1, hm, hi, Bind.bind, Except.bind]
    have hc : cldmod1 cld (mod1 mod iszero) x y = .ok (qf + 1, m) := by
      simp [cldmod1, hcld, hm0, hmod1, Bind.bind, Except.bind]
    have hf : fldmod1 fld1 (mod1 mod iszero) x y = .ok (qf + 1, m) := by
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
    (cldmod1 quotient (mod1 mod iszero) x y = .ok pair ∨
      fldmod1 quotient (mod1 mod iszero) x y = .ok pair) →
    pair.1 = q ∧
      (lt zero y → lt zero pair.2 ∧ le pair.2 y) ∧
      (lt y zero → le y pair.2 ∧ lt pair.2 zero)

theorem genericDivisionPairRange_proven : GenericDivisionPairRange := by
  intro A Q quotient mod iszero zero lt le x y r q hq hm hz hn hp hneg pair hpair
  have hrange := (mod1ZeroRemainder_proven A mod iszero zero lt le x y r hm hz hn hp hneg).2
  have hpair' : (do
      let rem ← mod1 mod iszero x y
      pure (q, rem)) = .ok pair := by
    rcases hpair with h | h <;>
      simpa [cldmod1, fldmod1, hq, Bind.bind, Except.bind] using h
  cases hrem : mod1 mod iszero x y with
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

def entries : List Entry := [
  { id := "operators-min-max-isless", juliaFile := "base/operators.jl",
    juliaFns := ["min(x, y)", "max(x, y)"],
    statement := "On every IEEE float format, including NaN payloads and signed zeros, the source min and max with the source AbstractFloat isless return one of their arguments that neither argument is isless-below (min) or isless-above (max), so min(NaN, y) == y and max(NaN, y) is NaN for non-NaN y.",
    source := "base/operators.jl:539-573 (max/min docstrings), 240", status := .proven,
    prop := ``MinMaxIsless, thm := some ``minMaxIsless_proven,
    notes := "Julia's Float64 min/max dispatch to the NaN-propagating math.jl:838-839 methods instead; that bug (mathfuncs-min-isless-nan) is registered on base/math.jl." },
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
    statement := "With IEEE < returning false on NaN, isless orders NaN above finite values and isequal treats two NaNs as equal.",
    source := "base/operators.jl:201-242; base/float.jl:619-634", status := .proven,
    prop := ``FloatNaNSemantics, thm := some ``floatNaNSemantics_proven },
  { id := "operators-unordered-order", juliaFile := "base/operators.jl",
    juliaFns := ["isgreater(x, y)", "isunordered(_)", "isunordered(x::AbstractFloat)", "isunordered(::Missing)"],
    statement := "Descending comparison preserves the generic comparison partition, uses exact mixed-width integer ordering, and invokes actual default, Float, and Missing unordered methods.",
    source := "base/operators.jl:251-311", status := .proven,
    prop := ``UnorderedContract, thm := some ``unorderedContract_proven },
  { id := "operators-minmax-coherent", juliaFile := "base/operators.jl",
    juliaFns := ["minmax(x, y)", "min(x, y)", "max(x, y)"],
    statement := "For every pair and comparator, minmax returns the same two values as the corresponding min and max calls, and on fixed-width integers min and max select the ordered extremum and preserve the sum.",
    source := "base/operators.jl:539-588", status := .proven,
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
    statement := "Returns(x) returns x for every positional and keyword argument list, stores x and _stable_typeof(x), identifies equal stored values, and Returns(x) ∘ g returns x after any callable g succeeds while propagating g's error.",
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
    statement := "For all callables f and g, including type objects and nested compositions, calling f ∘ g (or ComposedFunction{O,I}(f, g)) through the source call method equals f(g(args...; kw...)): g gets every argument, f only g's result, and g's error propagates first; a type outer is called through its Constructor.",
    source := "base/operators.jl:1039-1138", status := .proven,
    prop := ``CompositionApplication, thm := some ``compositionApplication_proven },
  { id := "operators-composition-unwrapping", juliaFile := "base/operators.jl",
    juliaFns := ["unwrap_composed(c::ComposedFunction)", "unwrap_composed(c)",
      "maybeconstructor(::Type{F})", "maybeconstructor(f)"],
    statement := "The source unwrap_composed flattens (f ∘ g) ∘ h and f ∘ (g ∘ h) identically, never returns an empty tuple or a type object, and keeps callable objects while turning types into Constructors.",
    source := "base/operators.jl:1126-1134", status := .proven,
    prop := ``CompositionUnwrapOrder, thm := some ``compositionUnwrapOrder_proven },
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
    prop := ``DisplayContract, thm := some ``displayContract_proven }
]

end JuliaLean.Proofs.base.operators
