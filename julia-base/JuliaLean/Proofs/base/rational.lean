import JuliaLean.Core
import JuliaLean.Proofs.base.checked
import JuliaLean.base.operators
import JuliaLean.Registry.Types
import JuliaLean.base.rational

/-!
# Properties of `base/rational.jl`

Each property states a documented rational-number contract or a previously
classified real Base behavior. Counterexamples use the source-mirrored models
in `JuliaLean.base.rational`.
-/

namespace JuliaLean.Proofs.base.rational

open JuliaLean JuliaLean.Promotion
open JuliaLean.base.rational

@[simp] private theorem unsafeRationalTypeSource_id (T : Type) (n d : T) :
    unsafeRationalTypeSource (m := Id) T id id n d = (⟨n,d⟩ : Rational T) := rfl

@[simp] private theorem unsafeRationalSameSource_pair {T : Type} (n d : T) :
    unsafeRationalSameSource n d = (⟨n,d⟩ : Rational T) := rfl

/-- Positive infinity minus a finite unsigned rational should stay positive
infinity. -/
def InfinitySub : Prop := ∀ (x y : Rat .u8),
  Normalized x → Normalized y → x.num.val > 0 → x.den.val = 0 →
  y.den.val > 0 →
  subRatSource (samePromoteOps (jintOps .u8)) (fun a b => .ok (a, b))
    (fun q => decide (q.den.val = 0))
    (negUnsignedSource (JInt.lit .u8 0) (fun a b => decide (a.val ≠ b.val)))
    (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok x

theorem infinitySub_refuted : ¬ InfinitySub := by
  intro h
  have bad := h unsignedInf unsignedOne
    (by unfold Normalized unsignedInf; decide)
    (by unfold Normalized unsignedOne; decide)
    (by decide) (by decide) (by decide)
  have actual : subRatSource (samePromoteOps (jintOps .u8)) (fun a b => .ok (a, b))
      (fun q => decide (q.den.val = 0))
      (negUnsignedSource (JInt.lit .u8 0) (fun a b => decide (a.val ≠ b.val)))
      (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource unsignedInf unsignedOne =
      .error (.overflowError "cannot negate unsigned number") := by decide
  rw [actual] at bad
  cases bad

/-- A reduced rational whose positive-denominator representation fits the
component type should be constructible from equivalent wider components. -/
def NormalizeBeforeConvert : Prop :=
  ∀ (t s : IntTy) (n d : JInt s) (x : Rat t),
    Normalized x → x.den.val > 0 → d.val ≠ 0 →
    n.val * x.den.val = x.num.val * d.val →
    constructSource (JInt t) (jintOps t)
      (fun a => decide (a.val = 0)) (fun b => decide (b.val = 0))
      (fun a => decide (a.val < 0)) (fun b => decide (b.val < 0))
      JuliaLean.base.float.uabs JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
      (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      Prod.mk n d (inexactErrorCore "Rational") = .ok x

theorem normalizeBeforeConvert_refuted : ¬ NormalizeBeforeConvert := by
  intro h
  let x : Rat .i8 := ⟨JInt.lit .i8 (-128), JInt.lit .i8 1⟩
  have bad := h .i8 .i16 (JInt.lit .i16 128) (JInt.lit .i16 (-1)) x
    (by unfold Normalized x; decide) (by decide) (by decide) (by decide)
  have actual : constructSource (JInt .i8) (jintOps .i8)
      (fun a => decide (a.val = 0)) (fun b => decide (b.val = 0))
      (fun a => decide (a.val < 0)) (fun b => decide (b.val < 0))
      JuliaLean.base.float.uabs JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
      (fun a => JInt.convert .i8 a.val) (fun b => JInt.convert .i8 b.val)
      (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (fun a => JInt.convert .i8 a.val) (fun b => JInt.convert .i8 b.val)
      Prod.mk (JInt.lit .i16 128) (JInt.lit .i16 (-1)) (inexactErrorCore "Rational") =
      .error (.inexactError "Int8") := by decide
  rw [actual] at bad
  cases bad

private theorem wrappedDivExact {t : IntTy} (x : JInt t) (g : Nat) (hg : 0 < g) :
    (JInt.wrap t (if x.val < 0 then -((x.val.natAbs / g : Nat) : Int)
      else ((x.val.natAbs / g : Nat) : Int))).val =
      if x.val < 0 then -((x.val.natAbs / g : Nat) : Int) else ((x.val.natAbs / g : Nat) : Int) := by
  let q : Int := ((x.val.natAbs / g : Nat) : Int)
  have hqNat : x.val.natAbs / g ≤ x.val.natAbs := Nat.div_le_self _ _
  have hqInt : q ≤ (x.val.natAbs : Int) := by
    dsimp [← Int.natCast_ediv, q]
    omega
  have hqNonneg : 0 ≤ q := by
    exact Int.natCast_nonneg _
  change wrapInt t (if x.val < 0 then -q else q) = if x.val < 0 then -q else q
  by_cases hx : x.val < 0
  · simp only [if_pos hx]
    have habs : (x.val.natAbs : Int) = -x.val :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hbound : q ≤ -x.val := by rw [← habs]; exact hqInt
    have hmin : t.min ≤ -q := by omega
    have hmax : -q ≤ t.max := by
      have hmax : 0 ≤ t.max := by cases t <;> decide
      omega
    exact wrapInt_of_inRange t (-q) ⟨hmin, hmax⟩
  · simp only [if_neg hx]
    have habs : (x.val.natAbs : Int) = x.val :=
      Int.natAbs_of_nonneg (by omega)
    have hbound : q ≤ x.val := by rw [← habs]; exact hqInt
    have hmin : t.min ≤ q := by
      have hmin : t.min ≤ 0 := by cases t <;> decide
      omega
    have hmax : q ≤ t.max := by omega
    exact wrapInt_of_inRange t q ⟨hmin, hmax⟩
private theorem intOfNatNatAbs (n : Nat) : ((n : Int).natAbs) = n := by
  have h : ((n : Int).natAbs : Int) = n := Int.natAbs_of_nonneg (by omega)
  omega

private theorem wrappedDivNatAbs {t : IntTy} (x : JInt t) (g : Nat) (hg : 0 < g) :
    (JInt.wrap t (if x.val < 0 then -((x.val.natAbs / g : Nat) : Int)
      else ((x.val.natAbs / g : Nat) : Int))).val.natAbs = x.val.natAbs / g := by
  rw [wrappedDivExact x g hg]
  by_cases hx : x.val < 0
  · simp only [if_pos hx, Int.natAbs_neg]
    exact intOfNatNatAbs _
  · simp only [if_neg hx]
    exact intOfNatNatAbs _

private theorem divgcdCoprime {t s : IntTy} (x : JInt t) (y : JInt s)
    (a : JInt t) (b : JInt s) (h : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok (a, b)) :
    Nat.gcd a.val.natAbs b.val.natAbs = 1 := by
  have hg : Nat.gcd x.val.natAbs y.val.natAbs ≠ 0 := by
    intro hz
    have hbad := h
    simp [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, hz] at hbad
  have hpos : 0 < Nat.gcd x.val.natAbs y.val.natAbs := Nat.pos_of_ne_zero hg
  have hpair : (JInt.wrap t
      (if x.val < 0 then -((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)),
      JInt.wrap s
      (if y.val < 0 then -((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int))) = (a, b) := by
    have h' := h
    simp only [divgcdSource, hg, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
    exact Except.ok.inj h'
  have ha := congrArg Prod.fst hpair
  have hb := congrArg Prod.snd hpair
  have haVal := congrArg Subtype.val ha
  have hbVal := congrArg Subtype.val hb
  rw [← haVal, ← hbVal,
    wrappedDivNatAbs x (Nat.gcd x.val.natAbs y.val.natAbs) hpos,
    wrappedDivNatAbs y (Nat.gcd x.val.natAbs y.val.natAbs) hpos]
  by_cases hx : 0 < x.val.natAbs
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_left hx
  · have hx0 : x.val.natAbs = 0 := by omega
    have hy : 0 < y.val.natAbs := by
      by_cases hy0 : y.val.natAbs = 0
      · simp [← Int.natCast_ediv, hx0, hy0] at hg
      · omega
    exact Nat.gcd_div_gcd_div_gcd_of_pos_right hy

private theorem divgcdPositiveDen {t s : IntTy} (x : JInt t) (y : JInt s)
    (a : JInt t) (b : JInt s) (hy : 0 < y.val)
    (h : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok (a, b)) : 0 < b.val := by
  have hg : Nat.gcd x.val.natAbs y.val.natAbs ≠ 0 := by
    intro hz
    have hbad := h
    simp [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, hz] at hbad
  have hpos : 0 < Nat.gcd x.val.natAbs y.val.natAbs := Nat.pos_of_ne_zero hg
  have hpair : (JInt.wrap t
      (if x.val < 0 then -((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)),
      JInt.wrap s
      (if y.val < 0 then -((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int))) = (a, b) := by
    have h' := h
    simp only [divgcdSource, hg, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
    exact Except.ok.inj h'
  have hb := congrArg Prod.snd hpair
  have hyAbs : (y.val.natAbs : Int) = y.val := Int.natAbs_of_nonneg (by omega)
  have hyAbsPos : 0 < y.val.natAbs := by omega
  have hq : 0 < y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs :=
    Nat.div_gcd_pos_of_pos_right x.val.natAbs hyAbsPos
  have hbVal := congrArg Subtype.val hb
  rw [← hbVal, wrappedDivExact y (Nat.gcd x.val.natAbs y.val.natAbs) hpos]
  simp only [show ¬ y.val < 0 by omega, if_false]
  omega


/-- Dividing both components by their gcd always gives a coprime pair. -/
def DivGcdReturnsCoprime : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (y : JInt s) (a : JInt t) (b : JInt s),
    divgcdSource (fun u : JInt t => u.val.natAbs) (fun v : JInt s => v.val.natAbs) Nat.gcd
      (fun u g => if g = 0 then .error .divideError else
        .ok (JInt.wrap t (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int)
          else ((u.val.natAbs / g : Nat) : Int))))
      (fun v g => if g = 0 then .error .divideError else
        .ok (JInt.wrap s (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int)
          else ((v.val.natAbs / g : Nat) : Int))))
      x y = .ok (a, b) →
    Nat.gcd a.val.natAbs b.val.natAbs = 1 ∧ (0 < y.val → 0 < b.val)

theorem divGcdReturnsCoprime_proven : DivGcdReturnsCoprime := by
  intro t s x y a b h
  have h' : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok (a, b) := by
    unfold divgcdSource at h
    by_cases hg : Nat.gcd x.val.natAbs y.val.natAbs = 0
    · simp [← Int.natCast_ediv, hg, Bind.bind, Except.bind] at h
    · simpa [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, hg, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
  exact ⟨divgcdCoprime x y a b h', fun hy => divgcdPositiveDen x y a b hy h'⟩


/- A positive-denominator construction returns a reduced rational;
`base/rational.jl:31-46`. -/
def ConstructPositiveDenominatorNormalizes : Prop :=
  ∀ (t : IntTy) (n d : JInt t) (r : Rat t), 0 < d.val →
    constructSource (JInt t) (jintOps t)
      (fun a => decide (a.val = 0)) (fun b => decide (b.val = 0))
      (fun a => decide (a.val < 0)) (fun b => decide (b.val < 0))
      JuliaLean.base.float.uabs JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
      (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      Prod.mk n d (inexactErrorCore "Rational") = .ok r → Normalized r ∧ 0 < r.den.val

private theorem positiveGcdRight (a b : Nat) (hb : 0 < b) :
    0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb

private theorem unsignedBoundsSame {t : IntTy} (ht : t.signed = false) :
    t.toUnsigned.min = t.min ∧ t.toUnsigned.max = t.max := by
  cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.bits]

private theorem unsignedNonneg {t : IntTy} (ht : t.signed = false) (x : JInt t) :
    0 ≤ x.val := by
  have hmin : t.min = 0 := by
    cases t <;> simp_all [IntTy.signed, IntTy.min]
  omega

private theorem uabsUnsignedValue {t : IntTy} (ht : t.signed = false) (x : JInt t) :
    (JuliaLean.base.float.uabs x).val = x.val := by
  cases t <;> simp_all [JuliaLean.base.float.uabs, JuliaLean.base.float.uabs_Integer,
    JuliaLean.base.int.abs, JuliaLean.base.int.abs_Unsigned,
    JuliaLean.base.int.Generic.abs_Unsigned, JuliaLean.base.int.remT,
    JuliaLean.base.int.rem_same, IntTy.signed, IntTy.toUnsigned]

theorem constructPositiveDenominatorNormalizes_proven :
    ConstructPositiveDenominatorNormalizes := by
  intro t n d r hd hc
  have hden : d.val ≠ 0 := by omega
  have hdAbsInt : (d.val.natAbs : Int) = d.val := Int.natAbs_of_nonneg (by omega)
  have hdAbs : 0 < d.val.natAbs := by omega
  by_cases hs : t.signed = true
  · have hgpos := positiveGcdRight n.val.natAbs d.val.natAbs hdAbs
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) n d with
    | error e =>
        have hbad := hdiv
        simp [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.ne_of_gt hgpos] at hbad
    | ok pair =>
        rcases pair with ⟨rn, rd⟩
        have hrd := divgcdPositiveDen n d rn rd hd hdiv
        have hcop := divgcdCoprime n d rn rd hdiv
        have hconvN : JInt.convert t rn.val = .ok rn := by
          simp [← Int.natCast_ediv, JInt.convert, rn.property]
        have hconvD : JInt.convert t rd.val = .ok rd := by
          simp [← Int.natCast_ediv, JInt.convert, rd.property]
        have hresult : unsafeRationalSameSource rn rd = r := by
          have hc' : (Except.ok (unsafeRationalSameSource rn rd) : Jl (Rat t)) = .ok r := by
            simpa [← Int.natCast_ediv, constructSource, checkedDenSameSource, checkedDenTypeSource, jintOps,
              hs, hden, hdiv, hconvN, hconvD, show ¬ rd.val < 0 by omega,
              Bind.bind, Except.bind, Pure.pure, Except.pure] using hc
          exact Except.ok.inj hc'
        have hnorm : Normalized (unsafeRationalSameSource rn rd) := by
          simpa [← Int.natCast_ediv, Normalized, unsafeRationalSameSource] using
            (show 0 ≤ rd.val ∧ Nat.gcd rn.val.natAbs rd.val.natAbs = 1 from
              ⟨by omega, hcop⟩)
        have hpositive : 0 < (unsafeRationalSameSource rn rd).den.val := by
          simpa [← Int.natCast_ediv, unsafeRationalSameSource] using hrd
        rw [← hresult]
        exact ⟨hnorm, hpositive⟩
  · have hu : t.signed = false := by
      cases t <;> simp_all [IntTy.signed]
    have hn : 0 ≤ n.val := unsignedNonneg hu n
    have huN := uabsUnsignedValue hu n
    have huD := uabsUnsignedValue hu d
    have hdU : 0 < (JuliaLean.base.float.uabs d).val := by
      rw [huD]
      exact hd
    have hdUAbs : 0 < (JuliaLean.base.float.uabs d).val.natAbs := by
      have ha : ((JuliaLean.base.float.uabs d).val.natAbs : Int) =
          (JuliaLean.base.float.uabs d).val :=
        Int.natAbs_of_nonneg (by omega)
      omega
    have hgpos := positiveGcdRight
      (JuliaLean.base.float.uabs n).val.natAbs
      (JuliaLean.base.float.uabs d).val.natAbs hdUAbs
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (JuliaLean.base.float.uabs n)
        (JuliaLean.base.float.uabs d) with
    | error e =>
        have hbad := hdiv
        simp [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.ne_of_gt hgpos] at hbad
    | ok pair =>
        rcases pair with ⟨rn, rd⟩
        have hrd := divgcdPositiveDen
          (JuliaLean.base.float.uabs n)
          (JuliaLean.base.float.uabs d) rn rd hdU hdiv
        have hcop := divgcdCoprime
          (JuliaLean.base.float.uabs n)
          (JuliaLean.base.float.uabs d) rn rd hdiv
        have hbounds := unsignedBoundsSame hu
        have hrangeN : t.min ≤ rn.val ∧ rn.val ≤ t.max := by
          rw [← hbounds.1, ← hbounds.2]
          exact rn.property
        have hrangeD : t.min ≤ rd.val ∧ rd.val ≤ t.max := by
          rw [← hbounds.1, ← hbounds.2]
          exact rd.property
        let rnT : JInt t := ⟨rn.val, hrangeN⟩
        let rdT : JInt t := ⟨rd.val, hrangeD⟩
        have hconvN : JInt.convert t rn.val = .ok rnT := by
          simp [← Int.natCast_ediv, JInt.convert, hrangeN, rnT]
        have hconvD : JInt.convert t rd.val = .ok rdT := by
          simp [← Int.natCast_ediv, JInt.convert, hrangeD, rdT]
        have hcopT : Nat.gcd rnT.val.natAbs rdT.val.natAbs = 1 := by
          simpa [← Int.natCast_ediv, rnT, rdT] using hcop
        have hrdT : 0 < rdT.val := by simpa [← Int.natCast_ediv, rdT] using hrd
        have hresult : unsafeRationalSameSource rnT rdT = r := by
          have hnn : ¬ n.val < 0 := by omega
          have hdn : ¬ d.val < 0 := by omega
          have hc' : (Except.ok (unsafeRationalSameSource rnT rdT) : Jl (Rat t)) = .ok r := by
            simpa [← Int.natCast_ediv, constructSource, jintOps, hs, hu, hn, hnn, hd, hdn, hden, hdiv, huN, huD,
              hconvN, hconvD, Bind.bind, Except.bind, Pure.pure, Except.pure] using hc
          exact Except.ok.inj hc'
        have hnorm : Normalized (unsafeRationalSameSource rnT rdT) := by
          simpa [← Int.natCast_ediv, Normalized, unsafeRationalSameSource] using
            (show 0 ≤ rdT.val ∧ Nat.gcd rnT.val.natAbs rdT.val.natAbs = 1 from
              ⟨by omega, hcopT⟩)
        have hpositive : 0 < (unsafeRationalSameSource rnT rdT).den.val := by
          simpa [← Int.natCast_ediv, unsafeRationalSameSource] using hrdT
        rw [← hresult]
        exact ⟨hnorm, hpositive⟩

private theorem exactOrOverflow_ok_val {t : IntTy} {z : JInt t} {n : Int}
    (h : JuliaLean.Proofs.base.checked.ExactOrOverflow (.ok z) n) : z.val = n := by
  unfold JuliaLean.Proofs.base.checked.ExactOrOverflow at h
  by_cases hr : t.min ≤ n ∧ n ≤ t.max
  · simp [← Int.natCast_ediv, hr] at h; exact h
  · simp [← Int.natCast_ediv, hr, JuliaLean.Proofs.base.checked.Overflowed] at h

private theorem checkedAdd_ok_val {t : IntTy} {x y z : JInt t} (h : checkedAdd x y = .ok z) :
    z.val = x.val + y.val := by
  have heq : checkedAdd x y = JuliaLean.base.checked.checkedAddBits x y := rfl
  have hex := JuliaLean.Proofs.base.checked.addExact t x y
  rw [← heq, h] at hex
  exact exactOrOverflow_ok_val hex

private theorem checkedSub_ok_val {t : IntTy} {x y z : JInt t} (h : checkedSub x y = .ok z) :
    z.val = x.val - y.val := by
  have heq : checkedSub x y = JuliaLean.base.checked.checkedSubBits x y := rfl
  have hex := JuliaLean.Proofs.base.checked.subExact t x y
  rw [← heq, h] at hex
  exact exactOrOverflow_ok_val hex

private theorem checkedMul_ok_val {t : IntTy} {x y z : JInt t} (h : checkedMul x y = .ok z) :
    z.val = x.val * y.val := by
  have heq : checkedMul x y = JuliaLean.base.checked.checkedMulBits x y := by cases t <;> rfl
  have hex := JuliaLean.Proofs.base.checked.mulExact t x y
  rw [← heq, h] at hex
  exact exactOrOverflow_ok_val hex

private theorem checkedNeg_ok_val {t : IntTy} {x z : JInt t} (h : checkedNeg x = .ok z) :
    z.val = -x.val := by
  have heq : checkedNeg x = JuliaLean.base.checked.checkedNegBits x := rfl
  have hex := JuliaLean.Proofs.base.checked.negExact t x
  rw [← heq, h] at hex
  exact exactOrOverflow_ok_val hex

private theorem checkedAbs_ok_val {t : IntTy} {x z : JInt t} (h : checkedAbs x = .ok z) :
    z.val = (if x.val < 0 then -x.val else x.val) := by
  have heq : checkedAbs x = JuliaLean.base.checked.checkedAbsBits x := rfl
  have hex := JuliaLean.Proofs.base.checked.absExact t x
  rw [← heq, h] at hex
  exact exactOrOverflow_ok_val hex

private theorem wrappedDivMulCancel {t : IntTy} (x : JInt t) (g : Nat)
    (hg : 0 < g) (hdvd : g ∣ x.val.natAbs) :
    (JInt.wrap t (if x.val < 0 then -((x.val.natAbs / g : Nat) : Int)
      else ((x.val.natAbs / g : Nat) : Int))).val * (g : Int) = x.val := by
  rw [wrappedDivExact x g hg]
  have hmul : ((x.val.natAbs / g : Nat) : Int) * (g : Int) = (x.val.natAbs : Int) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  by_cases hx : x.val < 0
  · have habs : (x.val.natAbs : Int) = -x.val := Int.ofNat_natAbs_of_nonpos (by omega)
    have hneg : (-((x.val.natAbs / g : Nat) : Int)) * (g : Int) =
        -(((x.val.natAbs / g : Nat) : Int) * (g : Int)) := Int.neg_mul _ _
    simp only [hx, ↓reduceIte]
    rw [hneg, hmul, habs]
    omega
  · have habs : (x.val.natAbs : Int) = x.val := Int.natAbs_of_nonneg (by omega)
    simp only [hx, ↓reduceIte]
    rw [hmul, habs]

private theorem divgcdFactors {t s : IntTy} (x : JInt t) (y : JInt s)
    (a : JInt t) (b : JInt s) (h : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok (a, b)) :
    let g : Int := Nat.gcd x.val.natAbs y.val.natAbs
    0 < g ∧ a.val * g = x.val ∧ b.val * g = y.val ∧ a.val * y.val = x.val * b.val := by
  dsimp only
  have hg : Nat.gcd x.val.natAbs y.val.natAbs ≠ 0 := by
    intro hz
    have hbad := h
    simp [← Int.natCast_ediv, divgcdSource, Bind.bind, Except.bind, Pure.pure, Except.pure, hz] at hbad
  have hpos : 0 < Nat.gcd x.val.natAbs y.val.natAbs := Nat.pos_of_ne_zero hg
  have hpair : (JInt.wrap t
      (if x.val < 0 then -((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((x.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)),
      JInt.wrap s
      (if y.val < 0 then -((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int)
       else ((y.val.natAbs / Nat.gcd x.val.natAbs y.val.natAbs : Nat) : Int))) = (a, b) := by
    have h' := h
    simp only [divgcdSource, hg, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
    exact Except.ok.inj h'
  have haVal := congrArg Subtype.val (congrArg Prod.fst hpair)
  have hbVal := congrArg Subtype.val (congrArg Prod.snd hpair)
  have haMul : a.val * (Nat.gcd x.val.natAbs y.val.natAbs : Int) = x.val := by
    rw [← haVal]
    exact wrappedDivMulCancel x _ hpos (Nat.gcd_dvd_left _ _)
  have hbMul : b.val * (Nat.gcd x.val.natAbs y.val.natAbs : Int) = y.val := by
    rw [← hbVal]
    exact wrappedDivMulCancel y _ hpos (Nat.gcd_dvd_right _ _)
  refine ⟨by omega, haMul, hbMul, ?_⟩
  calc a.val * y.val
    _ = a.val * (b.val * (Nat.gcd x.val.natAbs y.val.natAbs : Int)) := by rw [hbMul]
    _ = (a.val * (Nat.gcd x.val.natAbs y.val.natAbs : Int)) * b.val := by
        rw [← Int.mul_assoc, Int.mul_right_comm]
    _ = x.val * b.val := by rw [haMul]

private theorem checkedDen_spec {t : IntTy} (n d : JInt t) (r : Rat t)
    (h : checkedDenTypeSource (JInt t) (jintOps t) n d = .ok r) :
    0 ≤ r.den.val ∧ (d.val ≠ 0 → 0 < r.den.val) ∧
    r.den.val = (d.val.natAbs : Int) ∧ r.num.val.natAbs = n.val.natAbs ∧
    r.num.val * d.val = n.val * r.den.val := by
  unfold checkedDenTypeSource jintOps at h
  by_cases hd : d.val < 0
  · simp only [hd, decide_true, ↓reduceIte] at h
    cases hdn : checkedNeg d with
    | error e => simp [← Int.natCast_ediv, hdn, Bind.bind, Except.bind] at h
    | ok d' =>
      cases hnn : checkedNeg n with
      | error e => simp [← Int.natCast_ediv, hdn, hnn, Bind.bind, Except.bind] at h
      | ok n' =>
        have hr : unsafeRationalSameSource n' d' = r := by
          simpa [← Int.natCast_ediv, hdn, hnn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hdVal := checkedNeg_ok_val hdn
        have hnVal := checkedNeg_ok_val hnn
        have hdAbs : (d.val.natAbs : Int) = -d.val := Int.ofNat_natAbs_of_nonpos (by omega)
        subst hr
        simp only [unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]
        refine ⟨by omega, fun _ => by omega, by omega, ?_, ?_⟩
        · rw [hnVal, Int.natAbs_neg]
        · rw [hnVal, hdVal, Int.neg_mul, Int.mul_neg]
  · have hr : unsafeRationalSameSource n d = r := by
      simpa [← Int.natCast_ediv, hd, Pure.pure, Except.pure] using h
    have hdAbs : (d.val.natAbs : Int) = d.val := Int.natAbs_of_nonneg (by omega)
    subst hr
    exact ⟨by simp [← Int.natCast_ediv, unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]; omega, fun hne => by simp [← Int.natCast_ediv, unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]; omega,
      by simp [← Int.natCast_ediv, unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]; omega, rfl, rfl⟩

private theorem sourceConstructor_reduction {t : IntTy} (num den : JInt t) (r : Rat t)
    (h : rationalBitsSource num den = .ok r) :
    (do let (n,d) ← (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) num den; checkedDenTypeSource (JInt t) (jintOps t) n d) = .ok r := by
  by_cases hs : t.signed = true
  · unfold rationalBitsSource rationalSameSource constructSource at h
    by_cases hz : den.val = 0 ∧ num.val = 0
    · simp [jintOps, hz.1, hz.2, throwRationalZeroSource,         LazyString.render, LazyString.build] at h
    · simpa [jintOps, hs, hz, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
  · have hu : t.signed = false := by cases t <;> simp_all [IntTy.signed]
    cases t <;> simp only [IntTy.signed] at hu <;> try { contradiction }
    all_goals
      have hn0 : 0 ≤ num.val := num.property.1
      have hd0 : 0 ≤ den.val := den.property.1
      have hun : JuliaLean.base.float.uabs num = num := by
        apply Subtype.ext; exact uabsUnsignedValue rfl num
      have hud : JuliaLean.base.float.uabs den = den := by
        apply Subtype.ext; exact uabsUnsignedValue rfl den
      unfold rationalBitsSource rationalSameSource constructSource at h
      by_cases hz : den.val = 0 ∧ num.val = 0
      · simp [jintOps, hz.1, hz.2, throwRationalZeroSource,           LazyString.render, LazyString.build] at h
      · simp only [jintOps, hun, hud, IntTy.signed, Bool.not_false, Bool.true_eq,
          beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [IntTy.toUnsigned] at h
        simp [← Int.natCast_ediv, hz, show ¬ num.val < 0 by omega, show ¬ den.val < 0 by omega] at h
        cases hg : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) num den with
        | error e => simpa [← Int.natCast_ediv, hg, Bind.bind, Except.bind] using h
        | ok pair =>
          rcases pair with ⟨n,d⟩
          have hn : JInt.convert _ n.val = .ok n := by simp [JInt.convert, n.property]
          have hd : JInt.convert _ d.val = .ok d := by simp [JInt.convert, d.property]
          have hdnonneg : 0 ≤ d.val := d.property.1
          simpa [← Int.natCast_ediv, hg, hn, hd, checkedDenTypeSource, jintOps,
            show ¬ d.val < 0 by omega, Functor.map, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure] using h

private theorem rationalBitsSource_spec {t : IntTy} (num den : JInt t) (r : Rat t)
    (h : rationalBitsSource num den = .ok r) :
    Normalized r ∧ (den.val ≠ 0 → 0 < r.den.val) ∧
    r.num.val * den.val = num.val * r.den.val := by
  have h := sourceConstructor_reduction num den r h
  cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) num den with
  | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨n, d⟩
    simp only [hdiv, Bind.bind, Except.bind] at h
    have hcop := divgcdCoprime num den n d hdiv
    obtain ⟨_, hnMul, hdMul, _⟩ := divgcdFactors num den n d hdiv
    obtain ⟨hrd0, hrdPos, hrdAbs, hrnAbs, hrCross⟩ := checkedDen_spec n d r h
    have hrdNatAbs : r.den.val.natAbs = d.val.natAbs := by
      rw [hrdAbs, intOfNatNatAbs]
    have hnorm : Normalized r := by
      refine ⟨hrd0, ?_⟩
      rw [hrnAbs, hrdNatAbs]
      exact hcop
    have hpos : den.val ≠ 0 → 0 < r.den.val := by
      intro hden0
      apply hrdPos
      intro hd0
      rw [hd0, Int.zero_mul] at hdMul
      exact hden0 hdMul.symm
    have hcross : r.num.val * den.val = num.val * r.den.val := by
      calc r.num.val * den.val
        _ = r.num.val * (d.val * (Nat.gcd num.val.natAbs den.val.natAbs : Int)) := by rw [hdMul]
        _ = (r.num.val * d.val) * (Nat.gcd num.val.natAbs den.val.natAbs : Int) := by
            rw [← Int.mul_assoc]
        _ = (n.val * r.den.val) * (Nat.gcd num.val.natAbs den.val.natAbs : Int) := by
            rw [hrCross]
        _ = (n.val * (Nat.gcd num.val.natAbs den.val.natAbs : Int)) * r.den.val := by
            rw [Int.mul_right_comm]
        _ = num.val * r.den.val := by rw [hnMul]
    exact ⟨hnorm, hpos, hcross⟩


/-- `round(::Type{T}, x::Rational{Tr}, r)` converts signed infinities on
non-integer targets, throws `DivideError` on infinite integer rounding, and on
finite inputs returns the rounded quotient when it fits in `T` or throws
`InexactError(nameof(T))` when it overflows `T`. -/
def InfiniteRoundingRejected : Prop :=
  ∀ (t target : IntTy) (x : Rat t) (mode : JuliaLean.base.rational.Rounding)
    (copysign : Rat t → JInt t → Rat t)
    (convertInf : Rat t → Jl (JuliaLean.base.float.FV .f64))
    (divF : JInt t → JInt t → Rounding → Jl (JuliaLean.base.float.FV .f64))
    (convertQuotF : JuliaLean.base.float.FV .f64 → Jl (JuliaLean.base.float.FV .f64)),
    (x.den.val = 0 →
      roundRatTypedSource (JInt target) (jintOps t).iszero true
        (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
        roundValue (fun v => JInt.convert target v.val) x mode = .error .divideError) ∧
    (x.den.val = 0 →
      roundRatTypedSource (JuliaLean.base.float.FV .f64) (jintOps t).iszero false
        (jintOps t).one (jintOps t).zero copysign convertInf divF convertQuotF x mode =
      convertInf (copysign (unsafeRationalSameSource (jintOps t).one (jintOps t).zero) (numeratorRationalSource x))) ∧
    (x.den.val ≠ 0 → ∀ q, roundValue x.num x.den mode = .ok q →
      ((target.min ≤ q.val ∧ q.val ≤ target.max →
        ∃ z, roundRatTypedSource (JInt target) (jintOps t).iszero true
          (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
          roundValue (fun v => JInt.convert target v.val) x mode = .ok z ∧ z.val = q.val) ∧
       (¬(target.min ≤ q.val ∧ q.val ≤ target.max) →
        roundRatTypedSource (JInt target) (jintOps t).iszero true
          (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
          roundValue (fun v => JInt.convert target v.val) x mode = .error (.inexactError target.name))))

theorem infiniteRoundingRejected_proven : InfiniteRoundingRejected := by
  intro t target x mode copysign convertInf divF convertQuotF
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    simp [roundRatTypedSource, numeratorRationalSource, denominatorRationalSource, jintOps, roundValue, JInt.div, h0, Bind.bind, Except.bind]
  · intro h0
    simp [← Int.natCast_ediv, roundRatTypedSource, jintOps, denominatorRationalSource, h0]
  · intro _hne q hq
    refine ⟨?_, ?_⟩
    · intro hfit
      refine ⟨⟨q.val, hfit⟩, ?_, rfl⟩
      simp [← Int.natCast_ediv, roundRatTypedSource, numeratorRationalSource, denominatorRationalSource, hq, JInt.convert, hfit, Bind.bind, Except.bind]
    · intro hout
      simp [← Int.natCast_ediv, roundRatTypedSource, numeratorRationalSource, denominatorRationalSource, hq, JInt.convert, hout, Bind.bind, Except.bind]

/-- Rounding toward zero (`RoundToZero`) via `round(::Type{T}, x::Rational{Tr}, RoundToZero)`
and `round(x::Rational, RoundToZero)` returns the exact mathematical quotient for every
positive-denominator rational in its component type. -/
def TruncExact : Prop := ∀ (t : IntTy) (x : Rat t) (copysign : Rat t → JInt t → Rat t),
  0 < x.den.val →
  ∃ z,
    roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .toZero = .ok z ∧
    roundRatDefaultSource (fun _ => ())
      (fun _ q r => roundBitsSource t q r) x .toZero = .ok z ∧
    z.val = x.num.val.tdiv x.den.val

theorem truncExact_proven : TruncExact := by
  intro t x copysign hd
  have hn := x.num.property
  have hz : t.min ≤ 0 ∧ 0 ≤ t.max := by cases t <;> decide
  have hb : t.min ≤ x.num.val.tdiv x.den.val ∧ x.num.val.tdiv x.den.val ≤ t.max := by
    by_cases hs : 0 ≤ x.num.val
    · have hlo := Int.tdiv_le_tdiv hd hs
      have hhi := Int.tdiv_le_self x.den.val hs
      simp only [Int.zero_tdiv] at hlo
      omega
    · have hlo := Int.tdiv_le_self x.den.val (by omega : 0 ≤ -x.num.val)
      rw [Int.neg_tdiv] at hlo
      have hhi := Int.tdiv_le_tdiv hd (by omega : x.num.val ≤ 0)
      simp only [Int.zero_tdiv] at hhi
      omega
  let z : JInt t := ⟨x.num.val.tdiv x.den.val, hb⟩
  have hw : JInt.wrap t (x.num.val.tdiv x.den.val) = z := by
    apply Subtype.ext
    exact wrapInt_of_inRange t _ hb
  have he : ¬ (t.signed = true ∧ x.num.val = t.min ∧ x.den.val = -1) := by omega
  have hdiv : JInt.div x.num x.den = .ok z := by
    unfold JInt.div
    simp [← Int.natCast_ediv, Int.ne_of_gt hd, he, hw]
  have hround : roundValue x.num x.den .toZero = .ok z := by
    simp [← Int.natCast_ediv, roundValue, hdiv]
  have htyped : roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .toZero = .ok z := by
    simp [← Int.natCast_ediv, roundRatTypedSource, numeratorRationalSource, denominatorRationalSource, hround, JInt.convert, hb, z, Bind.bind, Except.bind]
  have hdef : roundRatDefaultSource (fun _ => ()) (fun _ q r => roundBitsSource t q r) x .toZero = .ok z := by
    simp [← Int.natCast_ediv, roundRatDefaultSource, roundBitsSource, roundRatTypedSource, jintOps, numeratorRationalSource, denominatorRationalSource, hround, JInt.convert, hb, z, Bind.bind, Except.bind]
  exact ⟨z, htyped, hdef, rfl⟩

/-- Rational/Float64 `cmp` uses numeric equality, while `isless` orders
negative zero before positive zero. -/
def CmpRationalFloatIsless : Prop :=
  ∀ (t : IntTy) (x : JuliaLean.base.float.FV .f64) (y : Rat t), Normalized y →
    cmpFloatRatSource x y =
      (if JuliaLean.base.operators.islessFloatReal
          JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
          JuliaLean.base.float.signbit_float (signbitRatSource (jintOps t).signbit)
          ltFloatRatSource x y then -1
       else if JuliaLean.base.operators.islessRealFloat
          (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
          (signbitRatSource (jintOps t).signbit) JuliaLean.base.float.signbit_float
          ltRatFloatSource y x then 1
       else 0)

def negativeZeroFloat : JuliaLean.base.float.FV .f64 :=
  JuliaLean.base.float.bitcast_to_float .f64 (JInt.lit .u64 0x8000000000000000)

theorem cmpRationalFloatIsless_refuted : ¬ CmpRationalFloatIsless := by
  intro h
  have bad := h .i64 negativeZeroFloat zeroRat64
    (by unfold Normalized zeroRat64; decide)
  have actual : cmpFloatRatSource negativeZeroFloat zeroRat64 = 0 := by decide +kernel
  have ordered : JuliaLean.base.operators.islessFloatReal
      JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
      JuliaLean.base.float.signbit_float (signbitRatSource (jintOps .i64).signbit)
      ltFloatRatSource negativeZeroFloat zeroRat64 = true := by decide +kernel
  rw [actual, ordered] at bad
  simp at bad

local instance {α : Type} [DecidableEq α] : DecidableEq (ExceptT JlError Option α) :=
  inferInstanceAs (DecidableEq (Option (Except JlError α)))

private theorem genericRationalizeSteps_sound {T F : Type} (ops : RatIntOps T)
    (gtF : F → F → Bool) (subF addF mulF cldF : F → F → F)
    (divremF : F → F → F × F) (convertTF : F → Jl T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T)) (fuel : Nat)
    (s : GenericRatState T F) (result : Jl (Rational T))
    (h : genericRationalizeSteps ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide fuel s = some result) :
    genericRationalizeWhile ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide s = some result := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    rw [genericRationalizeWhile.eq_1]
    cases hgt : gtF s.r s.nt <;>
      simp only [genericRationalizeSteps, hgt, Bool.false_eq_true, if_false, if_true] at h ⊢
    · exact h
    · cases hc : genericConvergentStep ops convertTF s.a s.p s.q s.pp s.qq with
      | error e => simpa only [hc] using h
      | ok pair =>
        rcases pair with ⟨np, nq⟩
        simp only [hc] at h ⊢
        exact ih _ h

/-- A finite Float64 converted to a rational must be exactly equal to that
rational. -/
def RationalOfFloatExact : Prop :=
  ∀ (t : IntTy) (x : JuliaLean.base.float.FV .f64) (r : Rat t) (showTol : JuliaLean.base.float.FV .f64 → String),
    rationalOfFloatSource (JInt t)
      (fun f => rationalizeF64 t f (JuliaLean.base.float.zero_float .f64) showTol)
      (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat) JuliaLean.base.float.eq_IEEEFloat x inexactErrorCore = some (.ok r) →
    JuliaLean.base.float.isfinite_IEEEFloat x = true →
    r.num.val * Int.ofNat (Fl.toRat x).2 = (Fl.toRat x).1 * r.den.val

def pointOne : JuliaLean.base.float.FV .f64 := Fl.ofBits 0x3fb999999999999a
def oneTenth8 : Rat .i8 := ⟨JInt.lit .i8 1, JInt.lit .i8 10⟩

private theorem pointOne_rationalize (showTol : JuliaLean.base.float.FV .f64 → String) : rationalizeF64 .i8 pointOne (JuliaLean.base.float.zero_float .f64) showTol = some (.ok oneTenth8) := by
  dsimp [rationalizeF64, rationalizeAbstractFloatSource, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure]
  apply genericRationalizeSteps_sound (fuel := 100)
  decide +kernel

theorem rationalOfFloatExact_refuted : ¬ RationalOfFloatExact := by
  intro h
  let showTol : JuliaLean.base.float.FV .f64 → String := reprStr
  have bad := h .i8 pointOne oneTenth8 showTol (by
    simp only [rationalOfFloatSource, pointOne_rationalize, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Option.bind]
    decide +kernel) (by decide)
  have actual : (Fl.toRat pointOne).1 * oneTenth8.den.val ≠
      oneTenth8.num.val * Int.ofNat (Fl.toRat pointOne).2 := by decide +kernel
  omega

/-- Exact Float64 values with a representable normalized rational should
convert to that rational. -/
def RationalOfFloatRepresentable : Prop :=
  ∀ (t : IntTy) (x : JuliaLean.base.float.FV .f64) (r : Rat t) (showTol : JuliaLean.base.float.FV .f64 → String),
    Normalized r → 0 < r.den.val → JuliaLean.base.float.isfinite_IEEEFloat x = true →
    r.num.val * Int.ofNat (Fl.toRat x).2 = (Fl.toRat x).1 * r.den.val →
    rationalOfFloatSource (JInt t)
      (fun f => rationalizeF64 t f (JuliaLean.base.float.zero_float .f64) showTol)
      (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat) JuliaLean.base.float.eq_IEEEFloat x inexactErrorCore = some (.ok r)

def minus128 : JuliaLean.base.float.FV .f64 := Fl.ofInt (-128)
def minus128Rat : Rat .i8 := ⟨JInt.lit .i8 (-128), JInt.lit .i8 1⟩

private theorem minus128_rationalize (showTol : JuliaLean.base.float.FV .f64 → String) : rationalizeF64 .i8 minus128 (JuliaLean.base.float.zero_float .f64) showTol = some (.ok (⟨JInt.lit .i8 (-127), JInt.lit .i8 1⟩ : Rat .i8)) := by
  dsimp [rationalizeF64, rationalizeAbstractFloatSource, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure]
  apply genericRationalizeSteps_sound (fuel := 100)
  decide +kernel

theorem rationalOfFloatRepresentable_refuted : ¬ RationalOfFloatRepresentable := by
  intro h
  let showTol : JuliaLean.base.float.FV .f64 → String := reprStr
  have bad := h .i8 minus128 minus128Rat showTol
    (by unfold Normalized minus128Rat; decide) (by decide) (by decide) (by decide)
  have actual : rationalOfFloatSource (JInt .i8)
      (fun f => rationalizeF64 .i8 f (JuliaLean.base.float.zero_float .f64) showTol)
      (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat) JuliaLean.base.float.eq_IEEEFloat minus128 inexactErrorCore ≠ some (.ok minus128Rat) := by
    simp only [rationalOfFloatSource, minus128_rationalize, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Option.bind]
    decide +kernel
  exact actual bad

/-- Conversion of a normalized finite rational to Float64 should round the
mathematical quotient to nearest, ties to even. -/
def RationalToFloatNearest : Prop :=
  ∀ (f : JuliaLean.base.float.FTy) (t : IntTy) (q : Rat t), Normalized q → 0 < q.den.val →
    floatConvertRatSource (JuliaLean.base.float.FV f)
      (JuliaLean.base.float.floatOfInt f)
      JuliaLean.base.float.div_IEEEFloat
      (JuliaLean.base.float.convertFloat f) q =
      Fl.roundRat (f := f.fmt) q.num.val q.den.val.toNat false ∧
    abstractFloatRatSource JuliaLean.base.float.float_BitInteger
      JuliaLean.base.float.div_IEEEFloat q =
      Fl.roundRat q.num.val q.den.val.toNat false

def ratNearestCex : Rat .i64 :=
  ⟨JInt.lit .i64 9007199254740995, JInt.lit .i64 3⟩

theorem rationalToFloatNearest_refuted : ¬ RationalToFloatNearest := by
  intro h
  have bad := (h .f64 .i64 ratNearestCex (by unfold Normalized ratNearestCex; decide) (by decide)).1
  have hne : floatConvertRatSource (JuliaLean.base.float.FV .f64)
      (JuliaLean.base.float.floatOfInt .f64)
      JuliaLean.base.float.div_IEEEFloat
      (JuliaLean.base.float.convertFloat .f64) ratNearestCex ≠
      Fl.roundRat ratNearestCex.num.val ratNearestCex.den.val.toNat false := by
    decide +kernel
  exact hne bad

/-- Truncating either infinite rational to an integer throws InexactError,
according to the historical contract. -/
def TruncInfiniteInexact : Prop :=
  ∀ (target t : IntTy) (x : Rat t) (copysign : Rat t → JInt t → Rat t),
    Normalized x → x.den.val = 0 →
    ∃ message,
      roundRatTypedSource (JInt target) (jintOps t).iszero true
        (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
        roundValue (fun v => JInt.convert target v.val) x .toZero =
      .error (.inexactError message)

def posInf64 : Rat .i64 := ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩

theorem truncInfiniteInexact_refuted : ¬ TruncInfiniteInexact := by
  intro h
  obtain ⟨message, hs⟩ := h .i64 .i64 posInf64 (fun a _ => a)
    (by unfold Normalized posInf64; decide) (by decide)
  have actual : roundRatTypedSource (JInt .i64) (jintOps .i64).iszero true
      (jintOps .i64).one (jintOps .i64).zero (fun a _ => a) (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert .i64 v.val) posInf64 .toZero =
      .error .divideError := by decide
  rw [actual] at hs
  cases hs

/-- The integer `rationalize` overload should honor its tolerance and return
a finite rational within `tol` whenever a representable approximation exists
within that tolerance. -/
def IntegerToleranceExtension : Prop :=
  (∀ (α β : Type) (one : α → α) (unsafeCtor : α → α → β) (x : α),
    rationalizeIntegerGeneric (rationalFromIntegerGeneric unsafeCtor one) x () = unsafeCtor x (one x)) ∧
  ∀ (t : IntTy) (x tolerance : Int), 0 ≤ tolerance →
    (∃ q, t.min ≤ q ∧ q ≤ t.max ∧ (x - q).natAbs ≤ tolerance.toNat) →
    ∃ r,
      rationalizeIntegerTypedSource (JInt t) (jintOps t)
        (fun m => decide (m < 0)) (fun m => decide (m < t.min))
        (fun m => decide (t.max < m)) (fun m => JInt.convert t m) (fun _ => 1)
        x tolerance = .ok r ∧
      0 < r.den.val ∧
      (x * r.den.val - r.num.val).natAbs ≤ tolerance.toNat * r.den.val.natAbs

theorem integerToleranceExtension_refuted : ¬ IntegerToleranceExtension := by
  intro h
  obtain ⟨r, hr, hdPos, _⟩ := h.2 .i8 128 1 (by decide) ⟨127, by decide, by decide, by decide⟩
  have actual : rationalizeIntegerTypedSource (JInt .i8) (jintOps .i8)
      (fun m => decide (m < 0)) (fun m => decide (m < IntTy.i8.min))
      (fun m => decide (IntTy.i8.max < m)) (fun m => JInt.convert .i8 m) (fun _ => 1)
      (128 : Int) (1 : Int) = .ok ⟨JInt.lit .i8 1, JInt.lit .i8 0⟩ := by decide
  rw [actual] at hr
  cases hr
  exact absurd hdPos (by decide)

/-- The documented floating-input tolerance bounds the exact rational error. -/
def RationalFloatingTolerance : Prop :=
  ∀ (t : IntTy) (x tol : JuliaLean.base.float.FV .f64) (r : Rat t) (showTol : JuliaLean.base.float.FV .f64 → String),
    JuliaLean.base.float.isfinite_IEEEFloat x = true →
    JuliaLean.base.float.isfinite_IEEEFloat tol = true →
    0 ≤ (Fl.toRat tol).1 →
    rationalizeF64 t x tol showTol = some (.ok r) →
    0 < r.den.val ∧
      ((Fl.toRat x).1 * r.den.val - r.num.val * (Fl.toRat x).2).natAbs * (Fl.toRat tol).2 ≤
        (Fl.toRat tol).1.natAbs * (Fl.toRat x).2 * r.den.val.natAbs

private theorem float128_rationalize (showTol : JuliaLean.base.float.FV .f64 → String) : rationalizeF64 .i8 (Fl.ofInt 128) (JuliaLean.base.float.zero_float .f64) showTol = some (.ok (⟨JInt.lit .i8 127, JInt.lit .i8 1⟩ : Rat .i8)) := by
  dsimp [rationalizeF64, rationalizeAbstractFloatSource, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure]
  apply genericRationalizeSteps_sound (fuel := 100)
  decide +kernel

set_option maxRecDepth 10000 in
theorem rationalFloatingTolerance_refuted : ¬ RationalFloatingTolerance := by
  intro h
  let showTol : JuliaLean.base.float.FV .f64 → String := reprStr
  let x : JuliaLean.base.float.FV .f64 := Fl.ofInt 128
  let tol := JuliaLean.base.float.zero_float .f64
  let r : Rat .i8 := ⟨JInt.lit .i8 127, JInt.lit .i8 1⟩
  have actual : rationalizeF64 .i8 x tol showTol = some (.ok r) := float128_rationalize showTol
  have bad := h .i8 x tol r showTol (by decide) (by decide) (by decide) actual
  have impossible : ¬ (0 < r.den.val ∧
      ((Fl.toRat x).1 * r.den.val - r.num.val * (Fl.toRat x).2).natAbs * (Fl.toRat tol).2 ≤
        (Fl.toRat tol).1.natAbs * (Fl.toRat x).2 * r.den.val.natAbs) := by decide +kernel
  exact impossible bad

/-- Zero over zero throws `ArgumentError`, while any nonzero numeratorRationalSource over zero
normalizes to `±1 // 0` via `(divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))`. -/
def ZeroOverZeroRejected : Prop :=
  (∀ t : IntTy,
    exactDivideIntsSource (rationalSameSource (jintOps t) JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
      (fun a => JInt.convert t a.val) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) Prod.mk)
      (JInt.lit t 0) (JInt.lit t 0) =
      .error (.argumentError ("invalid rational: zero(" ++ t.name ++ ")//zero(" ++ t.name ++ ")"))) ∧
  (∀ (t : IntTy) (n d : JInt t),
    n.val ≠ 0 → d.val = 0 →
    ∃ a b : JInt t,
      divgcdSource (fun u : JInt t => u.val.natAbs) (fun v : JInt t => v.val.natAbs) Nat.gcd
        (fun u g => if g = 0 then .error .divideError else
          .ok (JInt.wrap t (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int)
            else ((u.val.natAbs / g : Nat) : Int))))
        (fun v g => if g = 0 then .error .divideError else
          .ok (JInt.wrap t (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int)
            else ((v.val.natAbs / g : Nat) : Int))))
        n d = .ok (a, b) ∧
      b.val = 0 ∧ a.val.natAbs = 1 ∧
      a.val = (if n.val < 0 then -1 else 1))

theorem zeroOverZeroRejected_proven : ZeroOverZeroRejected := by
  refine ⟨fun t => by cases t <;> rfl, ?_⟩
  intro t n d hn hd
  have hdAbs : d.val.natAbs = 0 := by omega
  have hg : Nat.gcd n.val.natAbs d.val.natAbs = n.val.natAbs := by
    rw [hdAbs, Nat.gcd_zero_right]
  have hpos : 0 < Nat.gcd n.val.natAbs d.val.natAbs := by
    rw [hg]; exact Int.natAbs_pos.mpr hn
  have hgne : Nat.gcd n.val.natAbs d.val.natAbs ≠ 0 := Nat.ne_of_gt hpos
  have hdivN : n.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs = 1 := by
    rw [hg]; exact Nat.div_self (Int.natAbs_pos.mpr hn)
  have hdivD : d.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs = 0 := by
    rw [hdAbs, Nat.zero_div]
  let a := JInt.wrap t (if n.val < 0 then -((n.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs : Nat) : Int)
    else ((n.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs : Nat) : Int))
  let b := JInt.wrap t (if d.val < 0 then -((d.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs : Nat) : Int)
    else ((d.val.natAbs / Nat.gcd n.val.natAbs d.val.natAbs : Nat) : Int))
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · simp [← Int.natCast_ediv, divgcdSource, hgne, a, b, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have hb := wrappedDivExact d (Nat.gcd n.val.natAbs d.val.natAbs) hpos
    simpa [← Int.natCast_ediv, b, hd, hdivD] using hb
  · have ha := wrappedDivNatAbs n (Nat.gcd n.val.natAbs d.val.natAbs) hpos
    simpa [← Int.natCast_ediv, a, hdivN] using ha
  · have ha := wrappedDivExact n (Nat.gcd n.val.natAbs d.val.natAbs) hpos
    simpa [← Int.natCast_ediv, a, hdivN] using ha

/-- Reading both rational components and rebuilding the pair preserves the
stored representation, `decompose(x)` returns `(numeratorRationalSource(x), 0, denominatorRationalSource(x))`,
and reconstructing any normalized positive-denominator rational through `//`
(`exactDivideIntsSource rationalBitsSource`) recovers `x`. -/
def RationalComponentsRoundTrip : Prop :=
  ∀ (t : IntTy) (x : Rat t) (n d : JInt t),
    unsafeRationalTypeSource (JInt t) (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      (numeratorRationalSource x) (denominatorRationalSource x) = .ok x ∧
    unsafeRationalSameSource (numeratorRationalSource x) (denominatorRationalSource x) = x ∧
    numeratorRationalSource (unsafeRationalSameSource n d) = n ∧
    denominatorRationalSource (unsafeRationalSameSource n d) = d ∧
    decomposeSource x = (numeratorRationalSource x, JInt.lit .i64 0, denominatorRationalSource x) ∧
    (Normalized x → 0 < (denominatorRationalSource x).val →
      exactDivideIntsSource rationalBitsSource (numeratorRationalSource x) (denominatorRationalSource x) = .ok x)

theorem rationalComponentsRoundTrip_proven : RationalComponentsRoundTrip := by
  intro t x n d
  have htype : unsafeRationalTypeSource (JInt t) (fun a => JInt.convert t a.val) (fun b => JInt.convert t b.val)
      (numeratorRationalSource x) (denominatorRationalSource x) = .ok x := by
    cases x with
    | mk num den =>
      simp [← Int.natCast_ediv, unsafeRationalTypeSource, numeratorRationalSource, denominatorRationalSource,
        JInt.convert, num.property, den.property, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, id]
  refine ⟨htype, by cases x; rfl, rfl, rfl, rfl, ?_⟩
  intro hnorm hdPos
  unfold denominatorRationalSource at hdPos
  have hgcd : Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1 := hnorm.2
  have hpos : 0 < Nat.gcd x.num.val.natAbs x.den.val.natAbs := by omega
  have hgne : Nat.gcd x.num.val.natAbs x.den.val.natAbs ≠ 0 := by omega
  have hnVal : (JInt.wrap t (if x.num.val < 0 then
      -((x.num.val.natAbs / Nat.gcd x.num.val.natAbs x.den.val.natAbs : Nat) : Int)
      else ((x.num.val.natAbs / Nat.gcd x.num.val.natAbs x.den.val.natAbs : Nat) : Int))) = x.num := by
    apply Subtype.ext
    rw [wrappedDivExact x.num _ hpos, hgcd, Nat.div_one]
    by_cases hneg : x.num.val < 0
    · have habs : (x.num.val.natAbs : Int) = -x.num.val := Int.ofNat_natAbs_of_nonpos (by omega)
      simp [← Int.natCast_ediv, hneg, habs]
    · have habs : (x.num.val.natAbs : Int) = x.num.val := Int.natAbs_of_nonneg (by omega)
      simp [← Int.natCast_ediv, hneg, habs]
  have hdVal : (JInt.wrap t (if x.den.val < 0 then
      -((x.den.val.natAbs / Nat.gcd x.num.val.natAbs x.den.val.natAbs : Nat) : Int)
      else ((x.den.val.natAbs / Nat.gcd x.num.val.natAbs x.den.val.natAbs : Nat) : Int))) = x.den := by
    apply Subtype.ext
    rw [wrappedDivExact x.den _ hpos, hgcd, Nat.div_one]
    have habs : (x.den.val.natAbs : Int) = x.den.val := Int.natAbs_of_nonneg (by omega)
    simp [← Int.natCast_ediv, show ¬ x.den.val < 0 by omega, habs]
  have hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num x.den = .ok (x.num, x.den) := by
    unfold divgcdSource
    dsimp only
    simp only [hgne, ↓reduceIte, hnVal, hdVal]
    rfl
  have hnotneg : ¬ x.den.val < 0 := by omega
  have hcd : checkedDenTypeSource (JInt t) (jintOps t) x.num x.den = .ok x := by
    cases x
    simp [← Int.natCast_ediv, checkedDenTypeSource, jintOps, hnotneg, unsafeRationalSameSource, Pure.pure, Except.pure, unsafeRationalTypeSource, Bind.bind, Functor.map, id]
  change rationalBitsSource x.num x.den = .ok x
  by_cases hs : t.signed = true
  · simp [← Int.natCast_ediv, rationalBitsSource, rationalSameSource, constructSource,
      jintOps, hs, show x.den.val ≠ 0 by omega, hdiv, hnotneg, checkedDenTypeSource, Bind.bind, Except.bind]
    cases x; rfl
  · have hu : t.signed = false := by cases t <;> simp_all [IntTy.signed]
    cases t <;> simp only [IntTy.signed] at hu <;> try { contradiction }
    all_goals
      have hn0 : 0 ≤ x.num.val := x.num.property.1
      have hun : JuliaLean.base.float.uabs x.num = x.num := by
        apply Subtype.ext; exact uabsUnsignedValue rfl x.num
      have hud : JuliaLean.base.float.uabs x.den = x.den := by
        apply Subtype.ext; exact uabsUnsignedValue rfl x.den
      simp [← Int.natCast_ediv, rationalBitsSource, rationalSameSource, constructSource,
        jintOps, IntTy.signed, IntTy.toUnsigned, hun, hud, show x.den.val ≠ 0 by omega,
        show ¬ x.num.val < 0 by omega, hnotneg, hdiv, JInt.convert, x.num.property,
        x.den.property, Bind.bind, Except.bind]
      cases x; rfl


/-- `inv(x::Rational{T})` turns a zero rational into `x.den // 0`, preserves
normalization and positive denominators on nonzero rationals, and satisfies the
exact multiplicative-inverse cross-product `y.num * x.num = x.den * y.den`. -/
def InverseZeroIsInfinity : Prop :=
  ∀ (t : IntTy) (x y : Rat t),
    (x.num.val = 0 → 0 < x.den.val →
      invRatSource (jintOps t) x = .ok (unsafeRationalSameSource x.den (JInt.lit t 0))) ∧
    (Normalized x → 0 < x.den.val → x.num.val ≠ 0 →
      invRatSource (jintOps t) x = .ok y →
      Normalized y ∧ 0 < y.den.val ∧
      y.num.val * x.num.val = x.den.val * y.den.val ∧
      y.num.val.natAbs = x.den.val.natAbs ∧
      y.den.val.natAbs = x.num.val.natAbs)

theorem inverseZeroIsInfinity_proven : InverseZeroIsInfinity := by
  intro t x y
  refine ⟨?_, ?_⟩
  · intro hn hd
    have hnum : x.num = JInt.lit t 0 := by
      apply Subtype.ext
      rw [hn, JInt.lit, JInt.wrap]
      exact (wrapInt_of_inRange t 0 (by cases t <;> decide)).symm
    have hzero : (JInt.lit t 0).val = 0 := by
      cases t <;> decide
    unfold invRatSource checkedDenSameSource checkedDenTypeSource jintOps
    simp [← Int.natCast_ediv, hnum, hzero, Pure.pure, Except.pure]
  · intro hnorm _hd hne hinv
    obtain ⟨hyd0, hydPos, hydAbs, hynAbs, hcross⟩ := checkedDen_spec x.den x.num y hinv
    have hydNatAbs : y.den.val.natAbs = x.num.val.natAbs := by
      rw [hydAbs, intOfNatNatAbs]
    have hcop : Nat.gcd y.num.val.natAbs y.den.val.natAbs = 1 := by
      rw [hynAbs, hydNatAbs, Nat.gcd_comm]
      exact hnorm.2
    exact ⟨⟨hyd0, hcop⟩, hydPos hne, hcross, hynAbs, hydNatAbs⟩

/-- Integer comparisons against `Rational` match exact cross-multiplication by
the positive denominatorRationalSource, agree with embedding the integer as `y // 1`, and
obey strict/non-strict order duality. -/
def RationalIntegerComparisonsExact : Prop :=
  ∀ (t s : IntTy) (x : Rat t) (y : JInt s), 0 < x.den.val →
    let yRat : Rat s := rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => (jintOps s).one) y
    eqRatIntSource (jintOps t).isone (fun a b => decide (a.val = b.val)) x y =
      decide (x.den.val = 1 ∧ x.num.val = y.val) ∧
    eqIntRatSource (jintOps t).isone (fun a b => decide (a.val = b.val)) y x =
      decide (x.den.val = 1 ∧ x.num.val = y.val) ∧
    ltRatIntSource (fun d m => d.val * m.val) (fun n w => decide (n.val < w)) x y =
      decide (x.num.val < x.den.val * y.val) ∧
    ltIntRatSource (fun m d => m.val * d.val) (fun w n => decide (w < n.val)) y x =
      decide (y.val * x.den.val < x.num.val) ∧
    leRatIntSource (fun d m => d.val * m.val) (fun n w => decide (n.val ≤ w)) x y =
      decide (x.num.val ≤ x.den.val * y.val) ∧
    leIntRatSource (fun m d => m.val * d.val) (fun w n => decide (w ≤ n.val)) y x =
      decide (y.val * x.den.val ≤ x.num.val) ∧
    ltRatIntSource (fun d m => d.val * m.val) (fun n w => decide (n.val < w)) x y =
      !leIntRatSource (fun m d => m.val * d.val) (fun w n => decide (w ≤ n.val)) y x ∧
    ltIntRatSource (fun m d => m.val * d.val) (fun w n => decide (w < n.val)) y x =
      !leRatIntSource (fun d m => d.val * m.val) (fun n w => decide (n.val ≤ w)) x y ∧
    (yRat.den.val = 1 ∧ yRat.num.val = y.val)

theorem rationalIntegerComparisonsExact_proven : RationalIntegerComparisonsExact := by
  intro t s x y _hd
  have hone : (JInt.lit s 1).val = 1 := by cases s <;> decide
  dsimp only
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ⟨hone, rfl⟩⟩
  · by_cases hden : x.den.val = 1 <;> by_cases hnum : x.num.val = y.val <;>
      simp [← Int.natCast_ediv, eqRatIntSource, jintOps, bwand, hden, hnum]
  · by_cases hden : x.den.val = 1 <;> by_cases hnum : x.num.val = y.val <;>
      simp [← Int.natCast_ediv, eqIntRatSource, eqRatIntSource, jintOps, bwand, hden, hnum]
  · simp only [ltRatIntSource, leIntRatSource]
    by_cases h : x.num.val < x.den.val * y.val
    · have h2 : ¬ (y.val * x.den.val ≤ x.num.val) := by
        rw [Int.mul_comm y.val x.den.val]; omega
      simp [← Int.natCast_ediv, h, h2]
    · have h2 : y.val * x.den.val ≤ x.num.val := by
        rw [Int.mul_comm y.val x.den.val]; omega
      simp [← Int.natCast_ediv, h, h2]
  · simp only [ltIntRatSource, leRatIntSource]
    by_cases h : y.val * x.den.val < x.num.val
    · have h2 : ¬ (x.num.val ≤ x.den.val * y.val) := by
        rw [Int.mul_comm x.den.val y.val]; omega
      simp [← Int.natCast_ediv, h, h2]
    · have h2 : x.num.val ≤ x.den.val * y.val := by
        rw [Int.mul_comm x.den.val y.val]; omega
      simp [← Int.natCast_ediv, h, h2]

private theorem log2_shift_lt {A B : Nat} {d : Int} (_hA : 0 < A) (hB : 0 < B)
    (h : (A.log2 : Int) + 1 < (B.log2 : Int) + 1 + d) :
    A * 2 ^ ((-d).toNat) < B * 2 ^ (d.toNat) := by
  have hBne : B ≠ 0 := by omega
  by_cases hd : 0 ≤ d
  · have hneg : (-d).toNat = 0 := by omega
    rw [hneg]
    calc A * 2 ^ 0
      _ = A := by simp
      _ < 2 ^ (A.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ (B.log2 + d.toNat) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ B.log2 * 2 ^ d.toNat := Nat.pow_add 2 B.log2 d.toNat
      _ ≤ B * 2 ^ d.toNat := Nat.mul_le_mul_right _ (Nat.log2_self_le hBne)
  · have hpos : d.toNat = 0 := by omega
    rw [hpos]
    calc A * 2 ^ ((-d).toNat)
      _ < 2 ^ (A.log2 + 1) * 2 ^ ((-d).toNat) :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
      _ = 2 ^ (A.log2 + 1 + (-d).toNat) := (Nat.pow_add 2 (A.log2 + 1) ((-d).toNat)).symm
      _ ≤ 2 ^ B.log2 := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ B := Nat.log2_self_le hBne
      _ = B * 2 ^ 0 := by simp

private theorem shift_branch_eq {γ : Type} (rel : Int → Int → γ) (xc yc xp yp : Int) :
    (if xp > yp then rel (intShiftLeft xc (xp - yp)) yc
     else rel xc (intShiftLeft yc (yp - xp))) =
    rel (xc * ((2 ^ ((xp - yp).toNat) : Nat) : Int))
        (yc * ((2 ^ ((yp - xp).toNat) : Nat) : Int)) := by
  by_cases h : xp > yp
  · have h0 : (yp - xp).toNat = 0 := by omega
    simp [← Int.natCast_ediv, h, intShiftLeft, h0]
  · have h0 : (xp - yp).toNat = 0 := by omega
    simp [← Int.natCast_ediv, h, intShiftLeft, h0]

private theorem rationalFloatPos_spec {γ : Type} (rel : Int → Int → γ)
    (hrel : ∀ a b c d : Int, (a < b ↔ c < d) → (b < a ↔ d < c) → rel a b = rel c d)
    (xn xp xd yn yp yd : Int) (hxd : 0 < xd) (hyd : 0 < yd) :
    let xc := xn * yd
    let yc := yn * xd
    let xs := intSign xc
    let ys := intSign yc
    let lhs := xc * ((2 ^ ((xp - yp).toNat) : Nat) : Int)
    let rhs := yc * ((2 ^ ((yp - xp).toNat) : Nat) : Int)
    (if xs != ys then rel xs ys
     else if xs = 0 then rel xn yn
     else
       let xb := intNdigits0z2 xc 2 + xp
       let yb := intNdigits0z2 yc 2 + yp
       if xb = yb then
         if xp > yp then rel (intShiftLeft xc (xp - yp)) yc
         else rel xc (intShiftLeft yc (yp - xp))
       else if xc > 0 then rel xb yb else rel yb xb) = rel lhs rhs := by
  dsimp only
  let xc := xn * yd
  let yc := yn * xd
  let P : Int := ((2 ^ ((xp - yp).toNat) : Nat) : Int)
  let Q : Int := ((2 ^ ((yp - xp).toNat) : Nat) : Int)
  let lhs := xc * P
  let rhs := yc * Q
  have hP : 0 < P := Int.natCast_pos.mpr (Nat.two_pow_pos (xp - yp).toNat)
  have hQ : 0 < Q := Int.natCast_pos.mpr (Nat.two_pow_pos (yp - xp).toNat)
  have hxc_neg : lhs < 0 ↔ xc < 0 := by
    simpa [← Int.natCast_ediv, lhs, Int.zero_mul] using (Int.mul_lt_mul_right (b := xc) (c := 0) hP)
  have hxc_pos : 0 < lhs ↔ 0 < xc := by
    simpa [← Int.natCast_ediv, lhs, Int.zero_mul] using (Int.mul_lt_mul_right (b := 0) (c := xc) hP)
  have hxc_zero : lhs = 0 ↔ xc = 0 := by
    change xc * P = 0 ↔ xc = 0; rw [Int.mul_eq_zero]; omega
  have hyc_neg : rhs < 0 ↔ yc < 0 := by
    simpa [← Int.natCast_ediv, rhs, Int.zero_mul] using (Int.mul_lt_mul_right (b := yc) (c := 0) hQ)
  have hyc_pos : 0 < rhs ↔ 0 < yc := by
    simpa [← Int.natCast_ediv, rhs, Int.zero_mul] using (Int.mul_lt_mul_right (b := 0) (c := yc) hQ)
  have hyc_zero : rhs = 0 ↔ yc = 0 := by
    change yc * Q = 0 ↔ yc = 0; rw [Int.mul_eq_zero]; omega
  change (if (intSign xc != intSign yc) = true then rel (intSign xc) (intSign yc)
    else if intSign xc = 0 then rel xn yn
    else
      let xb := intNdigits0z2 xc 2 + xp
      let yb := intNdigits0z2 yc 2 + yp
      if xb = yb then
        if xp > yp then rel (intShiftLeft xc (xp - yp)) yc
        else rel xc (intShiftLeft yc (yp - xp))
      else if xc > 0 then rel xb yb else rel yb xb) = rel lhs rhs
  by_cases hs : (intSign xc != intSign yc) = true
  · simp only [hs, ↓reduceIte]
    apply hrel
    · rcases Int.lt_trichotomy xc 0 with h1 | h1 | h1 <;>
      rcases Int.lt_trichotomy yc 0 with h2 | h2 | h2
      all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2] at hs)
      all_goals (simp only [intSign, h1, h2, show ¬ (0 : Int) < 0 by decide, ↓reduceIte]; omega)
    · rcases Int.lt_trichotomy xc 0 with h1 | h1 | h1 <;>
      rcases Int.lt_trichotomy yc 0 with h2 | h2 | h2
      all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2] at hs)
      all_goals (simp only [intSign, h1, h2, show ¬ (0 : Int) < 0 by decide, ↓reduceIte]; omega)
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have hseq : intSign xc = intSign yc := by revert hs; simp
    by_cases hz : intSign xc = 0
    · simp only [hz, ↓reduceIte]
      have hxc0 : xc = 0 := by
        by_cases h1 : xc < 0 <;> by_cases h2 : 0 < xc
        all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2] at hz)
        all_goals omega
      have hyc0 : yc = 0 := by
        have hyz : intSign yc = 0 := by omega
        by_cases h1 : yc < 0 <;> by_cases h2 : 0 < yc
        all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2] at hyz)
        all_goals omega
      have hxn0 : xn = 0 := by
        have hm : xn * yd = 0 := hxc0
        rcases Int.mul_eq_zero.mp hm with h | h <;> omega
      have hyn0 : yn = 0 := by
        have hm : yn * xd = 0 := hyc0
        rcases Int.mul_eq_zero.mp hm with h | h <;> omega
      have hl0 : lhs = 0 := hxc_zero.mpr hxc0
      have hr0 : rhs = 0 := hyc_zero.mpr hyc0
      rw [hxn0, hyn0, hl0, hr0]
    · simp only [hz, ↓reduceIte]
      have hxc0 : xc ≠ 0 := by intro h0; apply hz; simp [← Int.natCast_ediv, intSign, h0]
      have hyc0 : yc ≠ 0 := by intro h0; apply hz; rw [hseq]; simp [← Int.natCast_ediv, intSign, h0]
      let xb := intNdigits0z2 xc 2 + xp
      let yb := intNdigits0z2 yc 2 + yp
      change (if xb = yb then
          if xp > yp then rel (intShiftLeft xc (xp - yp)) yc
          else rel xc (intShiftLeft yc (yp - xp))
        else if xc > 0 then rel xb yb else rel yb xb) = rel lhs rhs
      by_cases hbits : xb = yb
      · simp only [hbits, ↓reduceIte]
        exact shift_branch_eq rel xc yc xp yp
      · simp only [hbits, ↓reduceIte]
        have hlAbs : lhs.natAbs = xc.natAbs * 2 ^ ((xp - yp).toNat) := by
          change (xc * ((2 ^ ((xp - yp).toNat) : Nat) : Int)).natAbs = xc.natAbs * 2 ^ ((xp - yp).toNat)
          rw [Int.natAbs_mul, intOfNatNatAbs]
        have hrAbs : rhs.natAbs = yc.natAbs * 2 ^ ((yp - xp).toNat) := by
          change (yc * ((2 ^ ((yp - xp).toNat) : Nat) : Int)).natAbs = yc.natAbs * 2 ^ ((yp - xp).toNat)
          rw [Int.natAbs_mul, intOfNatNatAbs]
        have hxb_eq : xb = (xc.natAbs.log2 : Int) + 1 + xp := by
          simp [← Int.natCast_ediv, xb, intNdigits0z2, hxc0]
        have hyb_eq : yb = (yc.natAbs.log2 : Int) + 1 + yp := by
          simp [← Int.natCast_ediv, yb, intNdigits0z2, hyc0]
        have hlt1 : xb < yb → lhs.natAbs < rhs.natAbs := by
          intro hlt
          rw [hlAbs, hrAbs]
          have hlog : (xc.natAbs.log2 : Int) + 1 < (yc.natAbs.log2 : Int) + 1 + (yp - xp) := by
            omega
          have hsh := log2_shift_lt (Int.natAbs_pos.mpr hxc0) (Int.natAbs_pos.mpr hyc0) hlog
          rwa [show -(yp - xp) = xp - yp by omega] at hsh
        have hlt2 : yb < xb → rhs.natAbs < lhs.natAbs := by
          intro hlt
          rw [hlAbs, hrAbs]
          have hlog : (yc.natAbs.log2 : Int) + 1 < (xc.natAbs.log2 : Int) + 1 + (xp - yp) := by
            omega
          have hsh := log2_shift_lt (Int.natAbs_pos.mpr hyc0) (Int.natAbs_pos.mpr hxc0) hlog
          rwa [show -(xp - yp) = yp - xp by omega] at hsh
        by_cases hpos : xc > 0
        · simp only [hpos, ↓reduceIte]
          have hypos : 0 < yc := by
            have hxnotneg : ¬ xc < 0 := by omega
            by_cases h1 : yc < 0 <;> by_cases h2 : 0 < yc
            all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2, hxnotneg, hpos] at hseq)
            all_goals omega
          have hlpos : 0 < lhs := hxc_pos.mpr hpos
          have hrpos : 0 < rhs := hyc_pos.mpr hypos
          have hlCast : (lhs.natAbs : Int) = lhs := Int.natAbs_of_nonneg (by omega)
          have hrCast : (rhs.natAbs : Int) = rhs := Int.natAbs_of_nonneg (by omega)
          apply hrel
          · constructor
            · intro h; have := hlt1 h; omega
            · intro h
              exact Decidable.byContradiction fun hge => by
                have hyb : yb < xb := by omega
                have := hlt2 hyb
                omega
          · constructor
            · intro h; have := hlt2 h; omega
            · intro h
              exact Decidable.byContradiction fun hge => by
                have hxb : xb < yb := by omega
                have := hlt1 hxb
                omega
        · simp only [hpos, ↓reduceIte]
          have hxneg : xc < 0 := by omega
          have hyneg : yc < 0 := by
            by_cases h1 : yc < 0 <;> by_cases h2 : 0 < yc
            all_goals (try simp [← Int.natCast_ediv, intSign, h1, h2, hxneg] at hseq)
            all_goals omega
          have hlneg : lhs < 0 := hxc_neg.mpr hxneg
          have hrneg : rhs < 0 := hyc_neg.mpr hyneg
          have hlCast : (lhs.natAbs : Int) = -lhs := Int.ofNat_natAbs_of_nonpos (by omega)
          have hrCast : (rhs.natAbs : Int) = -rhs := Int.ofNat_natAbs_of_nonpos (by omega)
          apply hrel
          · constructor
            · intro h; have := hlt2 h; omega
            · intro h
              exact Decidable.byContradiction fun hge => by
                have hxb : xb < yb := by omega
                have := hlt1 hxb
                omega
          · constructor
            · intro h; have := hlt1 h; omega
            · intro h
              exact Decidable.byContradiction fun hge => by
                have hyb : yb < xb := by omega
                have := hlt2 hyb
                omega

private theorem rationalFloatRelationSource_spec {α β γ : Type}
    (isnanX : α → Bool) (isnanY : β → Bool) (onNanX : β → γ) (onNanY : γ)
    (decomposeX : α → Int × Int × Int) (decomposeY : β → Int × Int × Int)
    (rel : Int → Int → γ)
    (hrel : ∀ a b c d : Int, (a < b ↔ c < d) → (b < a ↔ d < c) → rel a b = rel c d)
    (x : α) (y : β) (hx : isnanX x = false) (hy : isnanY y = false)
    (hxd : (decomposeX x).2.2 ≠ 0) (hyd : (decomposeY y).2.2 ≠ 0) :
    let xn := (decomposeX x).1
    let xp := (decomposeX x).2.1
    let xd := (decomposeX x).2.2
    let yn := (decomposeY y).1
    let yp := (decomposeY y).2.1
    let yd := (decomposeY y).2.2
    let xn' := if xd < 0 then -xn else xn
    let xd' := if xd < 0 then -xd else xd
    let yn' := if yd < 0 then -yn else yn
    let yd' := if yd < 0 then -yd else yd
    rationalFloatRelationSource isnanX isnanY onNanX onNanY decomposeX decomposeY
      (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft rel x y =
    rel ((xn' * yd') * ((2 ^ ((xp - yp).toNat) : Nat) : Int))
        ((yn' * xd') * ((2 ^ ((yp - xp).toNat) : Nat) : Int)) := by
  unfold rationalFloatRelationSource
  simp only [hx, hy, Bool.false_eq_true, ↓reduceIte]
  rcases hdx : decomposeX x with ⟨xn, xp, xd⟩
  rcases hdy : decomposeY y with ⟨yn, yp, yd⟩
  rw [hdx] at hxd
  rw [hdy] at hyd
  dsimp only at hxd hyd ⊢
  by_cases h1 : xd < 0 <;> by_cases h2 : yd < 0 <;>
    simp only [h1, h2, ↓reduceIte] <;>
    exact rationalFloatPos_spec rel hrel _ _ _ _ _ _ (by omega) (by omega)

private theorem decomposeF64Int_den (x : JuliaLean.base.float.FV .f64)
    (hnan : JuliaLean.base.float.isnan_IEEEFloat x = false)
    (hinf : JuliaLean.base.float.isinf_IEEEFloat x = false) :
    (decomposeF64Int x).2.2 ≠ 0 ∧
    (if (decomposeF64Int x).2.2 < 0 then -(decomposeF64Int x).2.2 else (decomposeF64Int x).2.2) = 1 := by
  simp only [decomposeF64Int, JuliaLean.base.float.decompose_Float64,
    hnan, hinf, Bool.false_eq_true, ↓reduceIte, JuliaLean.base.int.ifelse]
  cases JuliaLean.base.float.signbit_float x <;> decide

/-- Rational/Float64 comparisons (`<`, `<=`, `cmp`) via
`rationalFloatRelationSource` (`cmpRatFloatSource`, `cmpFloatRatSource`,
`ltRatFloatSource`, `ltFloatRatSource`, `leRatFloatSource`, `leFloatRatSource`)
return false (or `±1` for `cmp`) on NaN, and on finite floats compare the exact
cross-multiplied dyadic integer values `q.num * 2^((-yp).toNat)` and
`yn' * q.den * 2^(yp.toNat)`. -/
def RationalFloatComparisonsExact : Prop :=
  ∀ (t : IntTy) (q : Rat t) (x : JuliaLean.base.float.FV .f64),
    0 < q.den.val →
    (JuliaLean.base.float.isnan_IEEEFloat x = true →
      ltRatFloatSource q x = false ∧ ltFloatRatSource x q = false ∧
      leRatFloatSource q x = false ∧ leFloatRatSource x q = false ∧
      cmpRatFloatSource q x = -1 ∧ cmpFloatRatSource x q = 1) ∧
    (JuliaLean.base.float.isnan_IEEEFloat x = false →
     JuliaLean.base.float.isinf_IEEEFloat x = false →
      let yn := (decomposeF64Int x).1
      let yp := (decomposeF64Int x).2.1
      let yd := (decomposeF64Int x).2.2
      let yn' := if yd < 0 then -yn else yn
      let lhs := q.num.val * ((2 ^ ((-yp).toNat) : Nat) : Int)
      let rhs := (yn' * q.den.val) * ((2 ^ (yp.toNat) : Nat) : Int)
      cmpRatFloatSource q x = (if lhs < rhs then -1 else if rhs < lhs then 1 else 0) ∧
      cmpFloatRatSource x q = (if rhs < lhs then -1 else if lhs < rhs then 1 else 0) ∧
      ltRatFloatSource q x = decide (lhs < rhs) ∧
      ltFloatRatSource x q = decide (rhs < lhs) ∧
      leRatFloatSource q x = decide (lhs ≤ rhs) ∧
      leFloatRatSource x q = decide (rhs ≤ lhs))

theorem rationalFloatComparisonsExact_proven : RationalFloatComparisonsExact := by
  intro t q x hd
  refine ⟨?_, ?_⟩
  · intro hnan
    simp [← Int.natCast_ediv, ltRatFloatSource, ltFloatRatSource, leRatFloatSource, leFloatRatSource,
      cmpRatFloatSource, cmpFloatRatSource, rationalFloatRelationSource, hnan]
  · intro hnan hinf
    obtain ⟨hydNe, hyd1⟩ := decomposeF64Int_den x hnan hinf
    have hqdNe : (decomposeRatInt q).2.2 ≠ 0 := by
      simp [← Int.natCast_ediv, decomposeRatInt, decomposeSource, denominatorRationalSource]; omega
    have hqdNotNeg : ¬ q.den.val < 0 := by omega
    have hcmpRel : ∀ a b c d : Int, (a < b ↔ c < d) → (b < a ↔ d < c) →
        intCmp a b = intCmp c d := by
      intro a b c d h1 h2
      unfold intCmp
      by_cases hab : a < b
      · have hcd : c < d := h1.mp hab; simp [← Int.natCast_ediv, hab, hcd]
      · have hncd : ¬ c < d := fun h => hab (h1.mpr h)
        by_cases hba : b < a
        · have hdc : d < c := h2.mp hba; simp [← Int.natCast_ediv, hab, hncd, hba, hdc]
        · have hndc : ¬ d < c := fun h => hba (h2.mpr h); simp [← Int.natCast_ediv, hab, hncd, hba, hndc]
    have hltRel : ∀ a b c d : Int, (a < b ↔ c < d) → (b < a ↔ d < c) →
        decide (a < b) = decide (c < d) := fun _ _ _ _ h1 _ => decide_eq_decide.mpr h1
    have hleRel : ∀ a b c d : Int, (a < b ↔ c < d) → (b < a ↔ d < c) →
        decide (a ≤ b) = decide (c ≤ d) := by
      intro a b c d _ h2; apply decide_eq_decide.mpr; omega
    have h1 := rationalFloatRelationSource_spec (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
      (fun y => if JuliaLean.base.float.isnan_IEEEFloat y then 0 else 1) (-1)
      decomposeRatInt decomposeF64Int intCmp hcmpRel q x rfl hnan hqdNe hydNe
    have h2 := rationalFloatRelationSource_spec JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
      (fun _ => 1) (-1)
      decomposeF64Int decomposeRatInt intCmp hcmpRel x q hnan rfl hydNe hqdNe
    have h3 := rationalFloatRelationSource_spec (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
      (fun _ => false) false decomposeRatInt decomposeF64Int (fun a b => decide (a < b)) hltRel
      q x rfl hnan hqdNe hydNe
    have h4 := rationalFloatRelationSource_spec JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
      (fun _ => false) false decomposeF64Int decomposeRatInt (fun a b => decide (a < b)) hltRel
      x q hnan rfl hydNe hqdNe
    have h5 := rationalFloatRelationSource_spec (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
      (fun _ => false) false decomposeRatInt decomposeF64Int (fun a b => decide (a ≤ b)) hleRel
      q x rfl hnan hqdNe hydNe
    have h6 := rationalFloatRelationSource_spec JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
      (fun _ => false) false decomposeF64Int decomposeRatInt (fun a b => decide (a ≤ b)) hleRel
      x q hnan rfl hydNe hqdNe
    have hdq : decomposeRatInt q = (q.num.val, 0, q.den.val) := rfl
    dsimp only at h1 h2 h3 h4 h5 h6 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold cmpRatFloatSource
      rw [h1]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1, intCmp]
    · unfold cmpFloatRatSource
      rw [h2]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1, intCmp]
    · unfold ltRatFloatSource
      rw [h3]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1]
    · unfold ltFloatRatSource
      rw [h4]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1]
    · unfold leRatFloatSource
      rw [h5]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1]
    · unfold leFloatRatSource
      rw [h6]
      simp [← Int.natCast_ediv, hdq, hqdNotNeg, hyd1]

private theorem rationalConvertResult {t : IntTy} (r : Jl (JInt t)) :
    (do
      let z ← r
      JInt.convert t z.val) = r := by
  cases r with
  | error e => rfl
  | ok z =>
      simp [← Int.natCast_ediv, JInt.convert, z.property, Bind.bind, Except.bind]

/-- `round(::Type{T}, x::Rational{Tr}, RoundDown)` and `round(..., RoundUp)`
(and the untyped `round(x, r)`, `fld`, and `cld` entrypoints) compute exact
integer floor and ceiling division for every positive-denominator rational. -/
def RationalFloorCeilDivision : Prop :=
  ∀ (t : IntTy) (x : Rat t) (copysign : Rat t → JInt t → Rat t),
    0 < x.den.val →
    roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .down = JInt.fld x.num x.den ∧
    roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .up = JInt.cld x.num x.den ∧
    fldDefaultSource (fun q _ m => roundBitsSource t q m) x x = JInt.fld x.num x.den ∧
    cldDefaultSource (fun q _ m => roundBitsSource t q m) x x = JInt.cld x.num x.den

theorem rationalFloorCeilDivision_proven : RationalFloorCeilDivision := by
  intro t x copysign hd
  have hno : ¬ (t.signed = true ∧ x.num.val = t.min ∧ x.den.val = -1) := by omega
  have hdiv : JInt.div x.num x.den = .ok (JInt.wrap t (x.num.val.tdiv x.den.val)) := by
    simp [← Int.natCast_ediv, JInt.div, show x.den.val ≠ 0 by omega, hno]
  have hdn : ((jintOps t).iszero (denominatorRationalSource x) && true) = false := by
    simp [← Int.natCast_ediv, jintOps, denominatorRationalSource, show x.den.val ≠ 0 by omega]
  have hdown : roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .down = JInt.fld x.num x.den := by
    simpa [← Int.natCast_ediv, roundRatTypedSource, roundValue, numeratorRationalSource, denominatorRationalSource, hdn, hdiv,
      Bind.bind, Except.bind] using rationalConvertResult (JInt.fld x.num x.den)
  have hup : roundRatTypedSource (JInt t) (jintOps t).iszero true
      (jintOps t).one (jintOps t).zero copysign (fun _ => .error .divideError)
      roundValue (fun v => JInt.convert t v.val) x .up = JInt.cld x.num x.den := by
    simpa [← Int.natCast_ediv, roundRatTypedSource, roundValue, numeratorRationalSource, denominatorRationalSource, hdn, hdiv,
      Bind.bind, Except.bind] using rationalConvertResult (JInt.cld x.num x.den)
  refine ⟨hdown, hup, ?_, ?_⟩
  · simpa [← Int.natCast_ediv, fldDefaultSource, roundBitsSource, roundRatTypedSource, jintOps, numeratorRationalSource, denominatorRationalSource, roundValue, hdiv, Bind.bind, Except.bind] using
      rationalConvertResult (JInt.fld x.num x.den)
  · simpa [← Int.natCast_ediv, cldDefaultSource, roundBitsSource, roundRatTypedSource, jintOps, numeratorRationalSource, denominatorRationalSource, roundValue, hdiv, Bind.bind, Except.bind] using
      rationalConvertResult (JInt.cld x.num x.den)

private theorem genericSemiconvergent_preserves {T F : Type} {P : Rational T → Prop}
    (ops : RatIntOps T) (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (hex : ∀ u v r, exactDivide u v = .ok r → P r)
    (a : F) (p q pp qq : T) (r : Rational T)
    (h : genericSemiconvergent ops leTwo gtHalf exactDivide a p q pp qq = .ok r) : P r := by
  unfold genericSemiconvergent at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · exact hex _ _ _ h
  · split at h
    · split at h
      · split at h <;> (split at h <;> exact hex _ _ _ h)
      · split at h
        · cases h
        · split at h <;> (split at h <;> exact hex _ _ _ h)
    · split at h
      · cases h
      · split at h
        · split at h <;> (split at h <;> exact hex _ _ _ h)
        · split at h
          · cases h
          · split at h <;> (split at h <;> exact hex _ _ _ h)

private theorem genericRationalizeWhile_preserves {T F : Type} {P : Rational T → Prop}
    (ops : RatIntOps T) (gtF : F → F → Bool) (subF addF mulF cldF : F → F → F)
    (divremF : F → F → F × F) (convertTF : F → Jl T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (hex : ∀ u v r, exactDivide u v = .ok r → P r)
    (s : GenericRatState T F) (r : Rational T)
    (h : genericRationalizeWhile ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide s = some (.ok r)) :
    P r := by
  have hp := genericRationalizeWhile.partial_correctness ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide
    (fun _ result => ∀ q, result = .ok q → P q) ?_ s (.ok r) h
  · exact hp r rfl
  · intro recur ih state result hresult q hq
    subst result
    split at hresult
    · split at hresult
      · exact ih _ _ hresult q rfl
      · split at hresult
        · exact genericSemiconvergent_preserves ops leTwo gtHalf exactDivide hex _ _ _ _ _ q (Option.some.inj hresult)
        · cases hresult
    · dsimp only at hresult
      split at hresult
      · exact hex _ _ _ (Option.some.inj hresult)
      · split at hresult
        · exact genericSemiconvergent_preserves ops leTwo gtHalf exactDivide hex _ _ _ _ _ q (Option.some.inj hresult)
        · cases hresult

/-- `rationalize(::Type{T}, x::AbstractFloat, tol::Real)` rejects negative
tolerances and negative inputs on unsigned targets, produces a reduced
(`Normalized`) rational on every successful conversion via `rationalBitsSource`, and
`Rational{T}(x::AbstractFloat)` succeeds only when the reduced rational
round-trips to an IEEE-equal float via `AbstractFloat(r)` / `(::Type{T})(r)`. -/
def RationalFloatRoundTripCore : Prop :=
  ∀ (t : IntTy) (x tol : JuliaLean.base.float.FV .f64) (r : Rat t)
    (z : ComplexValue (JuliaLean.base.float.FV .f64))
    (epsF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64)
    (gtF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 → Bool)
    (subF addF mulF cldF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64)
    (divremF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 →
      JuliaLean.base.float.FV .f64 × JuliaLean.base.float.FV .f64)
    (leTwo : JuliaLean.base.float.FV .f64 → Bool)
    (gtHalf : JInt t → JuliaLean.base.float.FV .f64 → Bool)
    (showTol : JuliaLean.base.float.FV .f64 → String),
    let ratFloat (ty : IntTy) (f tl : JuliaLean.base.float.FV .f64) : ExceptT JlError Option (Rat ty) :=
      rationalizeAbstractFloatSource (JInt ty) (jintOps ty)
        (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
        (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
        JuliaLean.base.float.isnan_IEEEFloat JuliaLean.base.float.isinf_IEEEFloat
        JuliaLean.base.float.abs_IEEEFloat JuliaLean.base.float.round_ToZero_llvm
        (fun _ => JuliaLean.base.float.zero_float .f64)
        (fun _ => JuliaLean.base.float.one_float .f64) (fun _ w => w)
        gtF subF addF mulF cldF divremF (JuliaLean.base.float.intOfFloat ty)
        leTwo (fun _ _ => false) rationalBitsSource f tl showTol
    (JuliaLean.base.float.lt_IEEEFloat tol (JuliaLean.base.float.zero_float .f64) = true →
      ratFloat t x tol = some (.error (.argumentError ("Tolerance can not be negative. tol=" ++ showTol tol)))) ∧
    (JuliaLean.base.float.lt_IEEEFloat tol (JuliaLean.base.float.zero_float .f64) = false →
     t.signed = false →
     JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.zero_float .f64) = true →
      ratFloat t x tol = some (.error (.overflowError "cannot negate unsigned number"))) ∧
    (ratFloat t x tol = some (.ok r) → Normalized r) ∧
    rationalizeFloatDefaultSource epsF (fun (_ : IntTy) f tl => ratFloat t f tl) t x = ratFloat t x (epsF x) ∧
    rationalizeRealSourceMethod (fun (_ : IntTy) f tl => ratFloat .i64 f tl) x tol = ratFloat .i64 x tol ∧
    rationalizeComplexDefaultSource (fun (_ : IntTy) f tl => ratFloat .i64 f tl) ComplexValue.mk z tol =
      rationalizeComplexTypedSource (fun (_ : IntTy) f tl => ratFloat .i64 f tl) ComplexValue.mk IntTy.i64 z tol ∧
    (rationalOfFloatSource (JInt t)
      (fun f => ratFloat t f (JuliaLean.base.float.zero_float .f64))
      (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat)
      JuliaLean.base.float.eq_IEEEFloat x inexactErrorCore = some (.ok r) →
      Normalized r ∧
      JuliaLean.base.float.eq_IEEEFloat x
        (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat r) = true ∧
      JuliaLean.base.float.eq_IEEEFloat x
        (floatConvertRatSource (JuliaLean.base.float.FV .f64)
          (JuliaLean.base.float.floatOfInt .f64)
          JuliaLean.base.float.div_IEEEFloat
          (JuliaLean.base.float.convertFloat .f64) r) = true) ∧
    ∀ (r32 : Rat .i32) (r128 : Rat .i128),
      float16OfRationalSmallSource (t := .i32) rfl r32 =
        JuliaLean.base.float.convertFloat .f16
          (floatConvertRatSource (JuliaLean.base.float.FV .f32)
            (JuliaLean.base.float.floatOfInt .f32)
            JuliaLean.base.float.div_IEEEFloat
            (JuliaLean.base.float.convertFloat .f32) r32) ∧
      float16OfRational128Source (t := .i128) rfl r128 =
        JuliaLean.base.float.convertFloat .f16
          (floatConvertRatSource (JuliaLean.base.float.FV .f64)
            (JuliaLean.base.float.floatOfInt .f64)
            JuliaLean.base.float.div_IEEEFloat
            (JuliaLean.base.float.convertFloat .f64) r128) ∧
      float32OfRational128Source (t := .i128) rfl r128 =
        JuliaLean.base.float.convertFloat .f32
          (floatConvertRatSource (JuliaLean.base.float.FV .f64)
            (JuliaLean.base.float.floatOfInt .f64)
            JuliaLean.base.float.div_IEEEFloat
            (JuliaLean.base.float.convertFloat .f64) r128)

private theorem rationalizeAbstractFloat_normalized
    (t : IntTy) (x tol : JuliaLean.base.float.FV .f64)
    (gtF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 → Bool)
    (subF addF mulF cldF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64)
    (divremF : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64 →
      JuliaLean.base.float.FV .f64 × JuliaLean.base.float.FV .f64)
    (leTwo : JuliaLean.base.float.FV .f64 → Bool)
    {gtHalf : JInt t → JuliaLean.base.float.FV .f64 → Bool}
    {showTol : JuliaLean.base.float.FV .f64 → String}
    (q : Rat t)
    (h : rationalizeAbstractFloatSource (JInt t) (jintOps t)
      (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
      (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
      JuliaLean.base.float.isnan_IEEEFloat JuliaLean.base.float.isinf_IEEEFloat
      JuliaLean.base.float.abs_IEEEFloat JuliaLean.base.float.round_ToZero_llvm
      (fun _ => JuliaLean.base.float.zero_float .f64)
      (fun _ => JuliaLean.base.float.one_float .f64) (fun _ w => w)
      gtF subF addF mulF cldF divremF (JuliaLean.base.float.intOfFloat t)
      leTwo gtHalf rationalBitsSource x tol showTol = some (.ok q)) : Normalized q := by
  unfold rationalizeAbstractFloatSource at h
  by_cases h1 : JuliaLean.base.float.lt_IEEEFloat tol (JuliaLean.base.float.zero_float .f64) = true
  · simp [← Int.natCast_ediv, h1, throw, throwThe, MonadExceptOf.throw, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind] at h
    cases Option.some.inj h
  · by_cases h2 : ((jintOps t).isUnsignedOrBool &&
        JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.zero_float .f64)) = true
    · simp [← Int.natCast_ediv, h1, h2, throwNegateUnsignedSource, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind] at h
      cases Option.some.inj h
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bind.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind, Pure.pure, Except.pure] at h
      split at h
      · cases htx : JuliaLean.base.float.intOfFloat t x with
        | error e => simp only [htx, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Pure.pure, Option.bind, Option.some.injEq] at h; cases h
        | ok tx =>
          simp only [htx, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Pure.pure, Option.bind, Option.some.injEq] at h
          exact (rationalBitsSource_spec tx (jintOps t).one q (Option.some.inj h)).1
      · split at h
        · have hq : unsafeRationalSameSource (if JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.zero_float .f64)
              then (jintOps t).minusOne else (jintOps t).one) (jintOps t).zero = q :=
            Except.ok.inj (Option.some.inj h)
          subst hq
          have hz : ((jintOps t).zero).val = 0 := by cases t <;> decide
          have ho : ((jintOps t).one).val = 1 := by cases t <;> decide
          unfold Normalized unsafeRationalSameSource unsafeRationalTypeSource
          dsimp only [Bind.bind, Pure.pure, Functor.map, id]
          refine ⟨by omega, ?_⟩
          rw [hz]
          split
          · rename_i hnegX
            have hs : t.signed = true := by
              cases ht : t.signed <;> simp_all [jintOps]
            have hm : ((jintOps t).minusOne).val.natAbs = 1 := by
              cases t <;> simp_all [IntTy.signed] <;> decide
            simp [← Int.natCast_ediv, hm]
          · rw [ho]; rfl
        · exact genericRationalizeWhile_preserves (jintOps t) _ _ _ _ _ _ _ _ _ rationalBitsSource
            (fun u v w hw => (rationalBitsSource_spec u v w hw).1) _ q h

private theorem rationalFloatRoundTrip_core : RationalFloatRoundTripCore := by
  intro t x tol r z epsF gtF subF addF mulF cldF divremF leTwo _gtHalf showTol
  dsimp only
  refine ⟨?_, ?_, rationalizeAbstractFloat_normalized t x tol gtF subF addF mulF cldF divremF leTwo r,
    rfl, rfl, rfl, ?_, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  · intro htol
    simp [← Int.natCast_ediv, rationalizeAbstractFloatSource, htol, throw, throwThe, MonadExceptOf.throw, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind]
  · intro htol hu hx
    simp [← Int.natCast_ediv, rationalizeAbstractFloatSource, jintOps, htol, hu, hx, throwNegateUnsignedSource, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind]
  · intro h
    unfold rationalOfFloatSource at h
    cases hr : rationalizeAbstractFloatSource (JInt t) (jintOps t)
        (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
        (fun w => JuliaLean.base.float.lt_IEEEFloat w (JuliaLean.base.float.zero_float .f64))
        JuliaLean.base.float.isnan_IEEEFloat JuliaLean.base.float.isinf_IEEEFloat
        JuliaLean.base.float.abs_IEEEFloat JuliaLean.base.float.round_ToZero_llvm
        (fun _ => JuliaLean.base.float.zero_float .f64)
        (fun _ => JuliaLean.base.float.one_float .f64) (fun _ w => w)
        gtF subF addF mulF cldF divremF (JuliaLean.base.float.intOfFloat t)
        leTwo (fun _ _ => false) rationalBitsSource x (JuliaLean.base.float.zero_float .f64) showTol with
    | none => simp [hr, Bind.bind, ExceptT.bind, ExceptT.mk, Option.bind] at h
    | some result =>
      cases result with
      | error e =>
        simp [← Int.natCast_ediv, hr, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind] at h
        cases Option.some.inj h
      | ok q =>
        have hnorm := rationalizeAbstractFloat_normalized t x (JuliaLean.base.float.zero_float .f64)
          gtF subF addF mulF cldF divremF leTwo q hr
        cases he : JuliaLean.base.float.eq_IEEEFloat x
            (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat q) with
        | false =>
          simp [← Int.natCast_ediv, hr, he, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.mk, ExceptT.bindCont, Option.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
          cases Option.some.inj h
        | true =>
          have hqr : q = r := by
            apply Except.ok.inj
            apply Option.some.inj
            simp only [hr, he, Bind.bind, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Option.bind, ↓reduceIte, Pure.pure] at h
            exact h
          subst hqr
          exact ⟨hnorm, he, he⟩
  

private theorem normalized_extremes {t : IntTy} {r : Rat t} (h : Normalized r) :
    (r.num.val = 0 → r.den.val = 1) ∧ (r.den.val = 0 → r.num.val.natAbs = 1) := by
  rcases h with ⟨hd, hg⟩
  constructor
  · intro hn
    have hdabs : r.den.val.natAbs = 1 := by simpa [hn] using hg
    have heq := Int.ofNat_natAbs_of_nonneg hd
    rw [hdabs] at heq
    omega
  · intro hz
    simpa [hz] using hg

/-- Successful conversion produces canonical zero and infinity representations, in
    addition to coprime components and an IEEE round trip. -/
def RationalFloatRoundTrip : Prop :=
  RationalFloatRoundTripCore ∧
  ∀ (t : IntTy) (x tol : JuliaLean.base.float.FV .f64) (r : Rat t) (showTol : JuliaLean.base.float.FV .f64 → String),
    rationalizeF64 t x tol showTol = some (.ok r) →
    (r.num.val = 0 → r.den.val = 1) ∧ (r.den.val = 0 → r.num.val.natAbs = 1)

theorem rationalFloatRoundTrip_proven : RationalFloatRoundTrip := by
  refine ⟨rationalFloatRoundTrip_core, ?_⟩
  intro t x tol r showTol h
  exact normalized_extremes (rationalizeAbstractFloat_normalized t x tol _ _ _ _ _ _ _ r h)

/-- `checked_den` retains nonnegative denominators, flips both signs via
`checked_neg` when the denominatorRationalSource is negative, and whenever it succeeds it
produces a rational with `0 ≤ r.den`, `r.den = |d|`, `|r.num| = |n|`, and
exact cross-product `r.num * d = n * r.den`. -/
def CheckedDenKeepsPositiveDenominator : Prop :=
  ∀ (t : IntTy) (n d : JInt t) (r : Rat t),
    (0 ≤ d.val →
      checkedDenTypeSource (JInt t) (jintOps t) n d = .ok (unsafeRationalSameSource n d)) ∧
    (d.val < 0 →
      checkedDenTypeSource (JInt t) (jintOps t) n d =
        (do let d' ← checkedNeg d; let n' ← checkedNeg n; pure (unsafeRationalSameSource n' d'))) ∧
    (checkedDenSameSource (jintOps t) n d = .ok r →
      0 ≤ r.den.val ∧ (d.val ≠ 0 → 0 < r.den.val) ∧
      r.den.val = (d.val.natAbs : Int) ∧ r.num.val.natAbs = n.val.natAbs ∧
      r.num.val * d.val = n.val * r.den.val)

theorem checkedDenKeepsPositiveDenominator_proven : CheckedDenKeepsPositiveDenominator := by
  intro t n d r
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    simp [← Int.natCast_ediv, checkedDenTypeSource, jintOps, show ¬ d.val < 0 by omega,
      Pure.pure, Except.pure]
  · intro hd
    simp [← Int.natCast_ediv, checkedDenTypeSource, jintOps, hd]
  · intro h
    exact checkedDen_spec n d r h

/-- Rational equality (`==`) and order (`<`, `<=`) via `eqRatSource`,
`ltRatSource`, and `leRatSource`: for positive denominators, the equal-denominatorRationalSource
fast path in `<` and `<=` is mathematically equivalent to the exact cross-product
order `x.num * y.den < y.num * x.den` (and `≤`), and satisfies reflexivity,
symmetry of `==`, and strict/non-strict order duality (`x < y ↔ ¬(y ≤ x)`). -/
def RationalRationalOrderExact : Prop :=
  ∀ (t s : IntTy) (x : Rat t) (y : Rat s),
    eqRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val = b.val)) x y =
      decide (x.den.val = y.den.val ∧ x.num.val = y.num.val) ∧
    eqRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val = b.val)) x x = true ∧
    eqRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val = b.val)) x y =
      eqRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val = b.val)) y x ∧
    (0 < x.den.val → 0 < y.den.val →
      ltRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val < b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a < b)) x y =
        decide (x.num.val * y.den.val < y.num.val * x.den.val) ∧
      leRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val ≤ b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a ≤ b)) x y =
        decide (x.num.val * y.den.val ≤ y.num.val * x.den.val) ∧
      ltRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val < b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a < b)) x y =
        !leRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val ≤ b.val))
          (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a ≤ b)) y x ∧
      ltRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val < b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a < b)) x x = false ∧
      leRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val ≤ b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a ≤ b)) x x = true)

theorem rationalRationalOrderExact_proven : RationalRationalOrderExact := by
  intro t s x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hden : x.den.val = y.den.val <;>
    by_cases hnum : x.num.val = y.num.val <;>
    simp [← Int.natCast_ediv, eqRatSource, bwand, hden, hnum]
  · simp [← Int.natCast_ediv, eqRatSource, bwand]
  · by_cases hden : x.den.val = y.den.val <;>
    by_cases hnum : x.num.val = y.num.val <;>
    simp [← Int.natCast_ediv, eqRatSource, bwand, hden, hnum, eq_comm]
  · intro hxd hyd
    have hlt_eq : ltRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val < b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a < b)) x y =
        decide (x.num.val * y.den.val < y.num.val * x.den.val) := by
      unfold ltRatSource
      by_cases hden : x.den.val = y.den.val
      · simp only [hden, decide_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        exact (Int.mul_lt_mul_right hyd).symm
      · simp only [hden, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        rw [Int.mul_comm x.den.val y.num.val]
    have hle_eq : leRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val ≤ b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a ≤ b)) x y =
        decide (x.num.val * y.den.val ≤ y.num.val * x.den.val) := by
      unfold leRatSource
      by_cases hden : x.den.val = y.den.val
      · simp only [hden, decide_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        constructor
        · intro h; exact Int.mul_le_mul_of_nonneg_right h (by omega)
        · intro h
          by_cases hlt : y.num.val < x.num.val
          · have := (Int.mul_lt_mul_right hyd).mpr hlt; omega
          · omega
      · simp only [hden, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        rw [Int.mul_comm x.den.val y.num.val]
    have hle_yx : leRatSource (fun a b => decide (a.val = b.val)) (fun a b => decide (a.val ≤ b.val))
        (fun a b => a.val * b.val) (fun a b => a.val * b.val) (fun a b => decide (a ≤ b)) y x =
        decide (y.num.val * x.den.val ≤ x.num.val * y.den.val) := by
      unfold leRatSource
      by_cases hden : y.den.val = x.den.val
      · simp only [hden, decide_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        constructor
        · intro h; exact Int.mul_le_mul_of_nonneg_right h (by omega)
        · intro h
          by_cases hlt : x.num.val < y.num.val
          · have := (Int.mul_lt_mul_right hxd).mpr hlt; omega
          · omega
      · simp only [hden, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply decide_eq_decide.mpr
        rw [Int.mul_comm y.den.val x.num.val]
    refine ⟨hlt_eq, hle_eq, ?_, ?_, ?_⟩
    · rw [hlt_eq, hle_yx]
      by_cases h : x.num.val * y.den.val < y.num.val * x.den.val
      · have h2 : ¬ (y.num.val * x.den.val ≤ x.num.val * y.den.val) := by omega
        simp [← Int.natCast_ediv, h, h2]
      · have h2 : y.num.val * x.den.val ≤ x.num.val * y.den.val := by omega
        simp [← Int.natCast_ediv, h, h2]
    · simp [← Int.natCast_ediv, ltRatSource]
    · simp [← Int.natCast_ediv, leRatSource]

/-- Checked rational arithmetic (`+`, `-`, `*`, `//`, `/`, `fma`, and mixed
Rational/Integer operations) preserves exact mathematical values and positive
reduced denominators whenever no integer overflow occurs. -/
def RationalArithmeticExact : Prop :=
  ∀ (t : IntTy) (x y r : Rat t) (k : JInt t),
    0 < x.den.val → 0 < y.den.val →
    (addRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
      (fun q => decide (q.den.val = 0)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r →
      Normalized r ∧ 0 < r.den.val ∧
      r.num.val * (x.den.val * y.den.val) = (x.num.val * y.den.val + y.num.val * x.den.val) * r.den.val) ∧
    (subRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
      (fun q => decide (q.den.val = 0)) (if h : t.signed = true then negBitSignedSource h else negUnsignedSource (jintOps t).zero (fun a b => decide (a.val ≠ b.val))) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r →
      Normalized r ∧ 0 < r.den.val ∧
      r.num.val * (x.den.val * y.den.val) = (x.num.val * y.den.val - y.num.val * x.den.val) * r.den.val) ∧
    (mulRatRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok r →
      0 < r.den.val ∧
      r.num.val * (x.den.val * y.den.val) = (x.num.val * y.num.val) * r.den.val) ∧
    (y.num.val ≠ 0 → divRatRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x y = .ok r →
      0 < r.den.val ∧
      r.num.val * (x.den.val * y.num.val) = (x.num.val * y.den.val) * r.den.val) ∧
    (k.val ≠ 0 → divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x k = .ok r →
      0 < r.den.val ∧
      r.num.val * (x.den.val * k.val) = x.num.val * r.den.val) ∧
    (x.num.val ≠ 0 → divIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k x = .ok r →
      0 < r.den.val ∧
      r.num.val * x.num.val = (k.val * x.den.val) * r.den.val) ∧
    (mulRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x k = .ok r →
      0 < r.den.val ∧
      r.num.val * x.den.val = (x.num.val * k.val) * r.den.val) ∧
    (mulIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k x = .ok r →
      0 < r.den.val ∧
      r.num.val * x.den.val = (k.val * x.num.val) * r.den.val) ∧
    (rationalIntegerOpSource (samePromoteOps (jintOps t)) checkedAdd x k = .ok r →
      r.den = x.den ∧ r.num.val = x.num.val + x.den.val * k.val) ∧
    (rationalIntegerOpSource (samePromoteOps (jintOps t)) checkedSub x k = .ok r →
      r.den = x.den ∧ r.num.val = x.num.val - x.den.val * k.val) ∧
    (integerRationalOpSource (samePromoteOps (jintOps t)) checkedAdd k x = .ok r →
      r.den = x.den ∧ r.num.val = x.den.val * k.val + x.num.val) ∧
    (integerRationalOpSource (samePromoteOps (jintOps t)) checkedSub k x = .ok r →
      r.den = x.den ∧ r.num.val = x.den.val * k.val - x.num.val)

theorem rationalArithmeticExact_proven : RationalArithmeticExact := by
  intro t x y r k hxdPos hydPos
  have hxdNe : x.den.val ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    unfold addRatSource samePromoteOps jintOps at h
    simp only [hxdNe, decide_false, Bool.false_and, ↓reduceIte] at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      cases ha : checkedMul x.num yd with
      | error e => simp [← Int.natCast_ediv, hdiv, ha, Bind.bind, Except.bind] at h
      | ok a =>
        cases hb : checkedMul y.num xd with
        | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, Bind.bind, Except.bind] at h
        | ok b =>
          cases hn : checkedAdd a b with
          | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, Bind.bind, Except.bind] at h
          | ok n =>
            cases hd : checkedMul x.den yd with
            | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
            | ok d =>
              simp only [hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
              have hydPos' := divgcdPositiveDen x.den y.den xd yd hydPos hdiv
              obtain ⟨_, hxdMul, hydMul, _⟩ := divgcdFactors x.den y.den xd yd hdiv
              have haVal := checkedMul_ok_val ha
              have hbVal := checkedMul_ok_val hb
              have hnVal := checkedAdd_ok_val hn
              have hdVal := checkedMul_ok_val hd
              have hdPos : 0 < d.val := by rw [hdVal]; exact Int.mul_pos hxdPos hydPos'
              obtain ⟨hnorm, hpos, hrCross⟩ := rationalBitsSource_spec n d r h
              refine ⟨hnorm, hpos (by omega), ?_⟩
              let g : Int := Nat.gcd x.den.val.natAbs y.den.val.natAbs
              calc r.num.val * (x.den.val * y.den.val)
                _ = r.num.val * (x.den.val * (yd.val * g)) := by rw [hydMul]
                _ = (r.num.val * (x.den.val * yd.val)) * g := by simp only [Int.mul_assoc]
                _ = (r.num.val * d.val) * g := by rw [← hdVal]
                _ = (n.val * r.den.val) * g := by rw [hrCross]
                _ = (n.val * g) * r.den.val := by rw [Int.mul_right_comm]
                _ = ((x.num.val * yd.val + y.num.val * xd.val) * g) * r.den.val := by
                    rw [hnVal, haVal, hbVal]
                _ = (x.num.val * (yd.val * g) + y.num.val * (xd.val * g)) * r.den.val := by
                    rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
                _ = (x.num.val * y.den.val + y.num.val * x.den.val) * r.den.val := by
                    rw [hydMul, hxdMul]
  · intro h
    unfold subRatSource samePromoteOps jintOps at h
    simp only [hxdNe, decide_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      cases ha : checkedMul x.num yd with
      | error e => simp [← Int.natCast_ediv, hdiv, ha, Bind.bind, Except.bind] at h
      | ok a =>
        cases hb : checkedMul y.num xd with
        | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, Bind.bind, Except.bind] at h
        | ok b =>
          cases hn : checkedSub a b with
          | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, Bind.bind, Except.bind] at h
          | ok n =>
            cases hd : checkedMul x.den yd with
            | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
            | ok d =>
              simp only [hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
              have hydPos' := divgcdPositiveDen x.den y.den xd yd hydPos hdiv
              obtain ⟨_, hxdMul, hydMul, _⟩ := divgcdFactors x.den y.den xd yd hdiv
              have haVal := checkedMul_ok_val ha
              have hbVal := checkedMul_ok_val hb
              have hnVal := checkedSub_ok_val hn
              have hdVal := checkedMul_ok_val hd
              have hdPos : 0 < d.val := by rw [hdVal]; exact Int.mul_pos hxdPos hydPos'
              obtain ⟨hnorm, hpos, hrCross⟩ := rationalBitsSource_spec n d r h
              refine ⟨hnorm, hpos (by omega), ?_⟩
              let g : Int := Nat.gcd x.den.val.natAbs y.den.val.natAbs
              calc r.num.val * (x.den.val * y.den.val)
                _ = r.num.val * (x.den.val * (yd.val * g)) := by rw [hydMul]
                _ = (r.num.val * (x.den.val * yd.val)) * g := by simp only [Int.mul_assoc]
                _ = (r.num.val * d.val) * g := by rw [← hdVal]
                _ = (n.val * r.den.val) * g := by rw [hrCross]
                _ = (n.val * g) * r.den.val := by rw [Int.mul_right_comm]
                _ = ((x.num.val * yd.val - y.num.val * xd.val) * g) * r.den.val := by
                    rw [hnVal, haVal, hbVal]
                _ = (x.num.val * (yd.val * g) - y.num.val * (xd.val * g)) * r.den.val := by
                    rw [Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
                _ = (x.num.val * y.den.val - y.num.val * x.den.val) * r.den.val := by
                    rw [hydMul, hxdMul]
  · intro h
    unfold mulRatRatSource samePromoteOps jintOps at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num y.den with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨xn, yd⟩
      cases h2 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.num with
      | error e => simp [← Int.natCast_ediv, h1, h2, Bind.bind, Except.bind] at h
      | ok p2 =>
        rcases p2 with ⟨xd, yn⟩
        cases hn : checkedMul xn yn with
        | error e => simp [← Int.natCast_ediv, h1, h2, hn, Bind.bind, Except.bind] at h
        | ok n =>
          cases hd : checkedMul xd yd with
          | error e => simp [← Int.natCast_ediv, h1, h2, hn, hd, Bind.bind, Except.bind] at h
          | ok d =>
            have hr : unsafeRationalSameSource n d = r := by
              simpa [← Int.natCast_ediv, h1, h2, hn, hd, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
            have hydPos' := divgcdPositiveDen x.num y.den xn yd hydPos h1
            obtain ⟨_, _, _, hc1⟩ := divgcdFactors x.num y.den xn yd h1
            obtain ⟨hg2, hxdMul, _, hc2⟩ := divgcdFactors x.den y.num xd yn h2
            have hxdPos' : 0 < xd.val :=
              Decidable.byContradiction fun hle => by
                have := Int.mul_nonpos_of_nonpos_of_nonneg (by omega : xd.val ≤ 0) (by omega : 0 ≤ (Nat.gcd x.den.val.natAbs y.num.val.natAbs : Int))
                omega
            have hnVal := checkedMul_ok_val hn
            have hdVal := checkedMul_ok_val hd
            subst hr
            simp only [unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]
            refine ⟨by rw [hdVal]; exact Int.mul_pos hxdPos' hydPos', ?_⟩
            calc n.val * (x.den.val * y.den.val)
              _ = (xn.val * y.den.val) * (x.den.val * yn.val) := by
                  rw [hnVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (x.num.val * yd.val) * (xd.val * y.num.val) := by rw [hc1, ← hc2]
              _ = (x.num.val * y.num.val) * d.val := by
                  rw [hdVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · intro hynNe h
    unfold divRatRatSource at h
    dsimp only [samePromoteOps] at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num y.num with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨xn, yn⟩
      cases h2 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
      | error e => simp [← Int.natCast_ediv, h1, h2, Bind.bind, Except.bind] at h
      | ok p2 =>
        rcases p2 with ⟨xd, yd⟩
        have hydPos' := divgcdPositiveDen x.den y.den xd yd hydPos h2
        obtain ⟨_, hxnMul, hynMul, _⟩ := divgcdFactors x.num y.num xn yn h1
        obtain ⟨_, hxdMul, hydMul, _⟩ := divgcdFactors x.den y.den xd yd h2
        have hxdNe' : xd.val ≠ 0 := by
          intro h0; rw [h0, Int.zero_mul] at hxdMul; exact hxdNe hxdMul.symm
        have hynNe' : yn.val ≠ 0 := by
          intro h0; rw [h0, Int.zero_mul] at hynMul; exact hynNe hynMul.symm
        have hcond : ((jintOps t).iszero xd && (jintOps t).signbit yn) = false := by
          simp [← Int.natCast_ediv, jintOps, hxdNe']
        simp only [h1, h2, hcond, Bool.false_eq_true, ↓reduceIte,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        change (do let a ← checkedMul xn yd; let b ← checkedMul xd yn; checkedDenSameSource (jintOps t) a b) = .ok r at h
        cases hn : checkedMul xn yd with
        | error e => simp [← Int.natCast_ediv, hn, Bind.bind, Except.bind] at h
        | ok n =>
          cases hd : checkedMul xd yn with
          | error e => simp [← Int.natCast_ediv, hn, hd, Bind.bind, Except.bind] at h
          | ok d =>
            simp only [hn, hd, Bind.bind, Except.bind] at h
            have hnVal := checkedMul_ok_val hn
            have hdVal := checkedMul_ok_val hd
            have hdNe : d.val ≠ 0 := by
              rw [hdVal]; exact Int.mul_ne_zero hxdNe' hynNe'
            obtain ⟨_, hrdPos, _, _, hrCross⟩ := checkedDen_spec n d r h
            refine ⟨hrdPos hdNe, ?_⟩
            let g1 : Int := Nat.gcd x.num.val.natAbs y.num.val.natAbs
            let g2 : Int := Nat.gcd x.den.val.natAbs y.den.val.natAbs
            calc r.num.val * (x.den.val * y.num.val)
              _ = r.num.val * ((xd.val * g2) * (yn.val * g1)) := by rw [hxdMul, hynMul]
              _ = (r.num.val * (xd.val * yn.val)) * (g1 * g2) := by
                  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (r.num.val * d.val) * (g1 * g2) := by rw [← hdVal]
              _ = (n.val * r.den.val) * (g1 * g2) := by rw [hrCross]
              _ = ((xn.val * g1) * (yd.val * g2)) * r.den.val := by
                  rw [hnVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (x.num.val * y.den.val) * r.den.val := by rw [hxnMul, hydMul]
  · intro hkNe h
    unfold divRatIntSource at h
    dsimp only [samePromoteOps] at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num k with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨xn, yn⟩
      obtain ⟨_, hxnMul, hynMul, _⟩ := divgcdFactors x.num k xn yn h1
      have hynNe : yn.val ≠ 0 := by
        intro h0; rw [h0, Int.zero_mul] at hynMul; exact hkNe hynMul.symm
      have hcond : ((jintOps t).iszero x.den && (jintOps t).signbit yn) = false := by
        simp [← Int.natCast_ediv, jintOps, hxdNe]
      simp only [h1, hcond, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      change (do let den ← checkedMul x.den yn; checkedDenSameSource (jintOps t) xn den) = .ok r at h
      cases hd : checkedMul x.den yn with
      | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
      | ok d =>
        simp only [hd, Bind.bind, Except.bind] at h
        have hdVal := checkedMul_ok_val hd
        have hdNe : d.val ≠ 0 := by rw [hdVal]; exact Int.mul_ne_zero hxdNe hynNe
        obtain ⟨_, hrdPos, _, _, hrCross⟩ := checkedDen_spec xn d r h
        refine ⟨hrdPos hdNe, ?_⟩
        let g : Int := Nat.gcd x.num.val.natAbs k.val.natAbs
        calc r.num.val * (x.den.val * k.val)
          _ = r.num.val * (x.den.val * (yn.val * g)) := by rw [hynMul]
          _ = (r.num.val * (x.den.val * yn.val)) * g := by simp only [Int.mul_assoc]
          _ = (r.num.val * d.val) * g := by rw [← hdVal]
          _ = (xn.val * r.den.val) * g := by rw [hrCross]
          _ = (xn.val * g) * r.den.val := by rw [Int.mul_right_comm]
          _ = x.num.val * r.den.val := by rw [hxnMul]
  · intro hxnNe h
    unfold divIntRatSource at h
    dsimp only [samePromoteOps] at h
    change (do let (xn, yn) ← (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k x.num; let num ← checkedMul xn x.den; checkedDenSameSource (jintOps t) num yn) = .ok r at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k x.num with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨xn, yn⟩
      obtain ⟨_, hxnMul, hynMul, _⟩ := divgcdFactors k x.num xn yn h1
      have hynNe : yn.val ≠ 0 := by
        intro h0; rw [h0, Int.zero_mul] at hynMul; exact hxnNe hynMul.symm
      simp only [h1, Bind.bind, Except.bind] at h
      cases hn : checkedMul xn x.den with
      | error e => simp [← Int.natCast_ediv, hn] at h
      | ok n =>
        simp only [hn] at h
        have hnVal := checkedMul_ok_val hn
        obtain ⟨_, hrdPos, _, _, hrCross⟩ := checkedDen_spec n yn r h
        refine ⟨hrdPos hynNe, ?_⟩
        let g : Int := Nat.gcd k.val.natAbs x.num.val.natAbs
        calc r.num.val * x.num.val
          _ = r.num.val * (yn.val * g) := by rw [hynMul]
          _ = (r.num.val * yn.val) * g := by rw [← Int.mul_assoc]
          _ = (n.val * r.den.val) * g := by rw [hrCross]
          _ = ((xn.val * g) * x.den.val) * r.den.val := by
              rw [hnVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (k.val * x.den.val) * r.den.val := by rw [hxnMul]
  · intro h
    unfold mulRatIntSource samePromoteOps jintOps at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den k with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨xd, yn⟩
      obtain ⟨hg1, hxdMul, _, hc1⟩ := divgcdFactors x.den k xd yn h1
      have hxdPos' : 0 < xd.val :=
        Decidable.byContradiction fun hle => by
          have := Int.mul_nonpos_of_nonpos_of_nonneg (by omega : xd.val ≤ 0) (by omega : 0 ≤ (Nat.gcd x.den.val.natAbs k.val.natAbs : Int))
          omega
      cases hn : checkedMul x.num yn with
      | error e => simp [← Int.natCast_ediv, h1, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n xd = r := by
          simpa [← Int.natCast_ediv, h1, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hnVal := checkedMul_ok_val hn
        subst hr
        simp only [unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]
        refine ⟨hxdPos', ?_⟩
        calc n.val * x.den.val
          _ = x.num.val * (x.den.val * yn.val) := by
              rw [hnVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = x.num.val * (xd.val * k.val) := by rw [← hc1]
          _ = (x.num.val * k.val) * xd.val := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · intro h
    unfold mulIntRatSource samePromoteOps jintOps at h
    cases h1 : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k x.den with
    | error e => simp [← Int.natCast_ediv, h1, Bind.bind, Except.bind] at h
    | ok p1 =>
      rcases p1 with ⟨yn, xd⟩
      obtain ⟨_, _, _, hc1⟩ := divgcdFactors k x.den yn xd h1
      have hxdPos' := divgcdPositiveDen k x.den yn xd hxdPos h1
      cases hn : checkedMul yn x.num with
      | error e => simp [← Int.natCast_ediv, h1, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n xd = r := by
          simpa [← Int.natCast_ediv, h1, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hnVal := checkedMul_ok_val hn
        subst hr
        simp only [unsafeRationalSameSource, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]
        refine ⟨hxdPos', ?_⟩
        calc n.val * x.den.val
          _ = (yn.val * x.den.val) * x.num.val := by
              rw [hnVal]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = (k.val * xd.val) * x.num.val := by rw [hc1]
          _ = (k.val * x.num.val) * xd.val := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · intro h
    unfold rationalIntegerOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : checkedAdd x.num d with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hdVal := checkedMul_ok_val hd
        have hnVal := checkedAdd_ok_val hn
        subst hr
        exact ⟨rfl, by change n.val = _; rw [hnVal, hdVal]⟩
  · intro h
    unfold rationalIntegerOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : checkedSub x.num d with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hdVal := checkedMul_ok_val hd
        have hnVal := checkedSub_ok_val hn
        subst hr
        exact ⟨rfl, by change n.val = _; rw [hnVal, hdVal]⟩
  · intro h
    unfold integerRationalOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : checkedAdd d x.num with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hdVal := checkedMul_ok_val hd
        have hnVal := checkedAdd_ok_val hn
        subst hr
        exact ⟨rfl, by change n.val = _; rw [hnVal, hdVal]⟩
  · intro h
    unfold integerRationalOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : checkedSub d x.num with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hdVal := checkedMul_ok_val hd
        have hnVal := checkedSub_ok_val hn
        subst hr
        exact ⟨rfl, by change n.val = _; rw [hnVal, hdVal]⟩

/-- Unary rational operations, sign and finiteness predicates, extremal values,
and integer/boolean conversions obey their documented specifications. -/
def RationalUnaryAndPredicatesExact : Prop :=
  ∀ (t target : IntTy) (x r : Rat t) (rc : Rat target) (z : JInt target)
    (ispow2 : JInt t → Bool) (ifelse : Bool → Rat t → Rat t → Rat t)
    (zero : Rat t → Rat t) (copysign : Rat t → Rat t → Rat t),
    (∀ a b, ifelse false a b = b) →
    (∀ a b, ifelse true a b = a) →
    unaryPlusRatSource (jintOps t).uplus x = x ∧
    (∀ hs : t.signed = true, negBitSignedSource hs x = .ok r → r.den = x.den ∧ (t.signed = true → r.num.val = -x.num.val)) ∧
    (∀ hs : t.signed = true, x.num.val = t.min →
      negBitSignedSource hs x = .error (.overflowError ("rational numerator is typemin(" ++ t.name ++ ")"))) ∧
    (x.num.val = 0 → negUnsignedSource (jintOps t).zero (fun a b => decide (a.val ≠ b.val)) x = .ok x) ∧
    (x.num.val ≠ 0 → negUnsignedSource (jintOps t).zero (fun a b => decide (a.val ≠ b.val)) x = .error (.overflowError "cannot negate unsigned number")) ∧
    negWrapRatSource (jintOps t).negWrap x = unsafeRationalSameSource (-x.num) x.den ∧
    (negWrapRatSource (jintOps t).negWrap x).den = x.den ∧
    (negWrapRatSource (jintOps t).negWrap x).num.val = wrapInt t (-x.num.val) ∧
    (absRatSource checkedAbs x = .ok r → r.den = x.den ∧ r.num.val = (x.num.val.natAbs : Int)) ∧
    signbitRatSource (jintOps t).signbit x = decide (x.num.val < 0) ∧
    (signRatSource (fun _ s => unsafeRationalSameSource s (jintOps t).one) (jintOps t).sign x).den.val = 1 ∧
    isIntegerRatSource (jintOps t).isone x = decide (x.den.val = 1) ∧
    isPow2RatSource ispow2 x = (ispow2 x.num && ispow2 x.den) ∧
    isZeroRationalSource (jintOps t).iszero x = decide (x.num.val = 0) ∧
    isOneRationalSource (jintOps t).isone x = decide (x.num.val = 1 ∧ x.den.val = 1) ∧
    (t.signed = true →
      (typeminSignedRatSource (JInt t) (jintOps t).one (jintOps t).zero (jintOps t).negWrap).num.val = -1 ∧
      (typeminSignedRatSource (JInt t) (jintOps t).one (jintOps t).zero (jintOps t).negWrap).den.val = 0) ∧
    ((typeminOtherRatSource (JInt t) (jintOps t).zero (jintOps t).one).num.val = 0 ∧
     (typeminOtherRatSource (JInt t) (jintOps t).zero (jintOps t).one).den.val = 1) ∧
    ((typemaxRatSource (JInt t) (jintOps t).one (jintOps t).zero).num.val = 1 ∧
     (typemaxRatSource (JInt t) (jintOps t).one (jintOps t).zero).den.val = 0) ∧
    (boolOfRatSource (fun q => (eqRatIntSource (fun d : JInt _ => d.val == 1) (fun a b : JInt _ => a.val == b.val)) q (JInt.lit t 0)) (fun q => (eqRatIntSource (fun d : JInt _ => d.val == 1) (fun a b : JInt _ => a.val == b.val)) q (JInt.lit t 1)) x inexactErrorCore = .ok false ↔ x.den.val = 1 ∧ x.num.val = 0) ∧
    (boolOfRatSource (fun q => (eqRatIntSource (fun d : JInt _ => d.val == 1) (fun a b : JInt _ => a.val == b.val)) q (JInt.lit t 0)) (fun q => (eqRatIntSource (fun d : JInt _ => d.val == 1) (fun a b : JInt _ => a.val == b.val)) q (JInt.lit t 1)) x inexactErrorCore = .ok true ↔ x.den.val = 1 ∧ x.num.val = 1) ∧
    (intOfRatSource (JInt target) target.name (isIntegerRatSource (jintOps t).isone) (fun v => JInt.convert target v.val) x inexactErrorCore = .ok z → x.den.val = 1 ∧ z.val = x.num.val) ∧
    (x.den.val ≠ 1 → intOfRatSource (JInt target) target.name (isIntegerRatSource (jintOps t).isone) (fun v => JInt.convert target v.val) x inexactErrorCore = .error (.inexactError target.name)) ∧
    Normalized (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => (jintOps t).one) x.num) ∧
    (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => (jintOps t).one) x.num).num = x.num ∧
    (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => (jintOps t).one) x.num).den.val = 1 ∧
    (convertRatSource (JInt target) (fun v => JInt.convert target v.val) x = .ok rc → rc.num.val = x.num.val ∧ rc.den.val = x.den.val) ∧
    boolMulRatSource ifelse zero copysign false x = copysign (zero x) x ∧
    boolMulRatSource ifelse zero copysign true x = x

theorem rationalUnaryAndPredicatesExact_proven : RationalUnaryAndPredicatesExact := by
  intro t target x r rc z ispow2 ifelse zero copysign hifFalse hifTrue
  have hlit0 : (JInt.lit t 0).val = 0 := by cases t <;> decide
  have hlit1 : (JInt.lit t 1).val = 1 := by cases t <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, hlit1, ?_, by unfold isPow2RatSource bwand; cases ispow2 x.num <;> cases ispow2 x.den <;> rfl, ?_, ?_, ?_,
    ⟨hlit0, hlit1⟩, ⟨hlit1, hlit0⟩, ?_, ?_, ?_, ?_, ?_, rfl, hlit1, ?_, ?_, ?_⟩
  · cases x; rfl
  · intro hs h
    have htv : (JInt.typemin t).val = t.min := by cases t <;> decide
    have hm : x.num.val ≠ t.min := by
      intro hm
      have heq : x.num = JInt.typemin t := Subtype.ext (by simpa [htv] using hm)
      simp [negBitSignedSource, heq, throwNumeratorTypeminSource] at h
    have heq : x.num ≠ JInt.typemin t := by intro heq; exact hm (by simpa [htv] using congrArg Subtype.val heq)
    have hr : unsafeRationalSameSource (-x.num) x.den = r := by
      simpa [negBitSignedSource, show x.num.val ≠ (JInt.typemin t).val by simpa [htv] using hm, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
    subst hr
    refine ⟨rfl, fun _ => ?_⟩
    have hx := x.num.property
    have hsym : t.min + t.max = -1 := by cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits]
    change wrapInt t (-x.num.val) = -x.num.val
    exact wrapInt_of_inRange t (-x.num.val) ⟨by omega, by omega⟩
  · intro hs hm
    have htv : (JInt.typemin t).val = t.min := by cases t <;> decide
    have heq : x.num = JInt.typemin t := Subtype.ext (by simpa [htv] using hm)
    simp [negBitSignedSource, heq, throwNumeratorTypeminSource,       LazyString.render, LazyString.build]
    rfl
  · intro h0; simp [← Int.natCast_ediv, negUnsignedSource, jintOps, h0, hlit0, Pure.pure, Except.pure]
  · intro hne; simp [← Int.natCast_ediv, negUnsignedSource, jintOps, hne, hlit0, throwNegateUnsignedSource, throw, throwThe, MonadExceptOf.throw]
  · intro h
    unfold absRatSource at h
    cases hn : checkedAbs x.num with
    | error e => simp [← Int.natCast_ediv, hn, Bind.bind, Except.bind] at h
    | ok n =>
      have hr : unsafeRationalSameSource n x.den = r := by
        simpa [← Int.natCast_ediv, hn, unsafeRationalSameSource, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
      have hnVal := checkedAbs_ok_val hn
      subst hr
      refine ⟨rfl, ?_⟩
      simp only [unsafeRationalSameSource, hnVal, unsafeRationalTypeSource, Bind.bind, Pure.pure, Functor.map, id]
      by_cases hx : x.num.val < 0
      · have habs : (x.num.val.natAbs : Int) = -x.num.val := Int.ofNat_natAbs_of_nonpos (by omega)
        simp [← Int.natCast_ediv, hx, habs]
      · have habs : (x.num.val.natAbs : Int) = x.num.val := Int.natAbs_of_nonneg (by omega)
        simp [← Int.natCast_ediv, hx, habs]
  · by_cases h1 : x.den.val = 1 <;> simp [← Int.natCast_ediv, isIntegerRatSource, jintOps, h1]
  · by_cases h0 : x.num.val = 0 <;> simp [← Int.natCast_ediv, isZeroRationalSource, jintOps, numeratorRationalSource, h0]
  · by_cases h1 : x.num.val = 1 <;> by_cases h2 : x.den.val = 1 <;> simp [← Int.natCast_ediv, isOneRationalSource, jintOps, numeratorRationalSource, denominatorRationalSource, bwand, h1, h2]
  · intro hs
    have hlitM1 : (-(JInt.lit t 1)).val = -1 := by
      cases t <;> simp_all [IntTy.signed] <;> decide
    exact ⟨hlitM1, hlit0⟩
  · unfold boolOfRatSource eqRatIntSource
    dsimp only
    simp only [hlit0, hlit1]
    by_cases hd : x.den.val = 1 <;> by_cases hn0 : x.num.val = 0 <;>
      by_cases hn1 : x.num.val = 1 <;> simp [← Int.natCast_ediv, bwand, hd, hn0, hn1]
  · unfold boolOfRatSource eqRatIntSource
    dsimp only
    simp only [hlit0, hlit1]
    by_cases hd : x.den.val = 1 <;> by_cases hn0 : x.num.val = 0 <;>
      by_cases hn1 : x.num.val = 1 <;> simp [← Int.natCast_ediv, bwand, hd, hn0, hn1] <;> omega
  · intro h
    unfold intOfRatSource isIntegerRatSource jintOps at h
    by_cases hd : x.den.val = 1
    · simp only [hd, beq_self_eq_true, ↓reduceIte, JInt.convert] at h
      by_cases hr : target.min ≤ x.num.val ∧ x.num.val ≤ target.max
      · simp only [hr, and_self, ↓reduceDIte, Except.ok.injEq] at h
        subst h; exact ⟨hd, rfl⟩
      · simp [← Int.natCast_ediv, hr] at h
    · simp [← Int.natCast_ediv, hd] at h
  · intro hd
    simp [← Int.natCast_ediv, intOfRatSource, isIntegerRatSource, jintOps, hd, throw, throwThe, MonadExceptOf.throw]
  · simp [← Int.natCast_ediv, Normalized, rationalFromIntegerGeneric, jintOps, hlit1]
  · intro h
    unfold convertRatSource at h
    cases hn : JInt.convert target x.num.val with
    | error e => simp [← Int.natCast_ediv, hn, Bind.bind, Except.bind] at h
    | ok n =>
      cases hd : JInt.convert target x.den.val with
      | error e => simp [← Int.natCast_ediv, hn, hd, Bind.bind, Except.bind] at h
      | ok d =>
        have hrc : unsafeRationalSameSource n d = rc := by
          simpa [← Int.natCast_ediv, hn, hd, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        have hnVal : n.val = x.num.val := by
          unfold JInt.convert at hn
          by_cases hrn : target.min ≤ x.num.val ∧ x.num.val ≤ target.max
          · simp [← Int.natCast_ediv, hrn] at hn; exact congrArg Subtype.val hn.symm
          · simp [← Int.natCast_ediv, hrn] at hn
        have hdVal : d.val = x.den.val := by
          unfold JInt.convert at hd
          by_cases hrd : target.min ≤ x.den.val ∧ x.den.val ≤ target.max
          · simp [← Int.natCast_ediv, hrd] at hd; exact congrArg Subtype.val hd.symm
          · simp [← Int.natCast_ediv, hrd] at hd
        subst hrc
        exact ⟨hnVal, hdVal⟩
  · exact hifFalse x (copysign (zero x) x)
  · exact hifTrue x (copysign (zero x) x)

/-- Wrapping rational addition/subtraction, rational remainders, Bool-rational
rounding, and rational unit-range length methods obey their contracts. -/
def RationalWrappingAndRemainderExact : Prop :=
  ∀ (t : IntTy) (x y r : Rat t) (k : JInt t)
    (denomFalse targetIsInt : Bool) (conv : Rat t → Jl (JInt t)),
    (x.den.val = 0 → (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) x y = true →
      addWrapRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
        (fun q => decide (q.den.val = 0)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok x) ∧
    (0 < x.den.val →
      addWrapRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
        (fun q => decide (q.den.val = 0)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r → Normalized r) ∧
    (x.den.val = 0 → (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) x ((negWrapRatSource (jintOps t).negWrap) y) = true →
      subWrapRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
        (fun q => decide (q.den.val = 0)) (fun q => .ok (negWrapRatSource (jintOps t).negWrap q)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok x) ∧
    (0 < x.den.val →
      subWrapRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a, b))
        (fun q => decide (q.den.val = 0)) (fun q => .ok (negWrapRatSource (jintOps t).negWrap q)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r → Normalized r) ∧
    (0 < x.den.val → 0 < y.den.val →
      remRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r → Normalized r ∧ 0 < r.den.val) ∧
    (0 < x.den.val → 0 < y.den.val →
      modRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource x y = .ok r → Normalized r ∧ 0 < r.den.val) ∧
    (rationalIntegerOpSource (samePromoteOps (jintOps t)) JInt.remInt x k = .ok r →
      r.den = x.den) ∧
    (rationalIntegerOpSource (samePromoteOps (jintOps t)) JInt.mod x k = .ok r →
      r.den = x.den) ∧
    (integerRationalRemainderSource (samePromoteOps (jintOps t)) JInt.remInt rationalBitsSource k x = .ok r →
      Normalized r ∧ (x.den.val ≠ 0 → 0 < r.den.val)) ∧
    (integerRationalRemainderSource (samePromoteOps (jintOps t)) JInt.mod rationalBitsSource k x = .ok r →
      Normalized r ∧ (x.den.val ≠ 0 → 0 < r.den.val)) ∧
    (denomFalse = true ∧ targetIsInt = true →
      roundBoolRationalSource (JInt t) targetIsInt (fun _ => conv x) ⟨true, !denomFalse⟩ = .error .divideError) ∧
    (¬(denomFalse = true ∧ targetIsInt = true) →
      roundBoolRationalSource (JInt t) targetIsInt (fun _ => conv x) ⟨true, !denomFalse⟩ = conv x) ∧
    checkedLengthRationalRangeSource Prod.fst Prod.snd (fun _ => true)
      (fun a b => a - b) checkedSub checkedAdd JInt.div (x, y) = .ok (x.num - x.num)

theorem rationalWrappingAndRemainderExact_proven : RationalWrappingAndRemainderExact := by
  intro t x y r k denomFalse targetIsInt conv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro hd0 heq
    simp [← Int.natCast_ediv, addWrapRatSource, hd0, heq, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro hxdPos h
    have hxdNe : x.den.val ≠ 0 := by omega
    unfold addWrapRatSource samePromoteOps jintOps at h
    simp only [hxdNe, decide_false, Bool.false_and, ↓reduceIte] at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      simp only [hdiv, Bind.bind, Except.bind] at h
      exact (rationalBitsSource_spec _ _ r h).1
  · intro hd0 heq
    simp [← Int.natCast_ediv, subWrapRatSource, hd0, heq, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro hxdPos h
    have hxdNe : x.den.val ≠ 0 := by omega
    unfold subWrapRatSource samePromoteOps jintOps at h
    simp only [hxdNe, decide_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      simp only [hdiv, Bind.bind, Except.bind] at h
      exact (rationalBitsSource_spec _ _ r h).1
  · intro hxdPos hydPos h
    unfold remRatSource samePromoteOps jintOps at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      cases ha : checkedMul x.num yd with
      | error e => simp [← Int.natCast_ediv, hdiv, ha, Bind.bind, Except.bind] at h
      | ok a =>
        cases hb : checkedMul y.num xd with
        | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, Bind.bind, Except.bind] at h
        | ok b =>
          cases hn : JInt.remInt a b with
          | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, Bind.bind, Except.bind] at h
          | ok n =>
            cases hd : checkedMul x.den yd with
            | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
            | ok d =>
              simp only [hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
              have hydPos' := divgcdPositiveDen x.den y.den xd yd hydPos hdiv
              have hdVal := checkedMul_ok_val hd
              have hdPos : 0 < d.val := by rw [hdVal]; exact Int.mul_pos hxdPos hydPos'
              obtain ⟨hnorm, hpos, _⟩ := rationalBitsSource_spec n d r h
              exact ⟨hnorm, hpos (by omega)⟩
  · intro hxdPos hydPos h
    unfold modRatSource samePromoteOps jintOps at h
    cases hdiv : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
    | error e => simp [← Int.natCast_ediv, hdiv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨xd, yd⟩
      cases ha : checkedMul x.num yd with
      | error e => simp [← Int.natCast_ediv, hdiv, ha, Bind.bind, Except.bind] at h
      | ok a =>
        cases hb : checkedMul y.num xd with
        | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, Bind.bind, Except.bind] at h
        | ok b =>
          cases hn : JInt.mod a b with
          | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, Bind.bind, Except.bind] at h
          | ok n =>
            cases hd : checkedMul x.den yd with
            | error e => simp [← Int.natCast_ediv, hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
            | ok d =>
              simp only [hdiv, ha, hb, hn, hd, Bind.bind, Except.bind] at h
              have hydPos' := divgcdPositiveDen x.den y.den xd yd hydPos hdiv
              have hdVal := checkedMul_ok_val hd
              have hdPos : 0 < d.val := by rw [hdVal]; exact Int.mul_pos hxdPos hydPos'
              obtain ⟨hnorm, hpos, _⟩ := rationalBitsSource_spec n d r h
              exact ⟨hnorm, hpos (by omega)⟩
  · intro h
    unfold rationalIntegerOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : JInt.remInt x.num d with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst hr; rfl
  · intro h
    unfold rationalIntegerOpSource unsafeRationalPromoteSource samePromoteOps jintOps at h
    cases hd : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
    | ok d =>
      cases hn : JInt.mod x.num d with
      | error e => simp [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind] at h
      | ok n =>
        have hr : unsafeRationalSameSource n x.den = r := by
          simpa [← Int.natCast_ediv, hd, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst hr; rfl
  · intro h
    unfold integerRationalRemainderSource samePromoteOps jintOps at h
    cases ha : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, ha, Bind.bind, Except.bind] at h
    | ok a =>
      cases hn : JInt.remInt a x.num with
      | error e => simp [← Int.natCast_ediv, ha, hn, Bind.bind, Except.bind] at h
      | ok n =>
        simp only [ha, hn, Bind.bind, Except.bind] at h
        obtain ⟨hnorm, hpos, _⟩ := rationalBitsSource_spec n x.den r h
        exact ⟨hnorm, hpos⟩
  · intro h
    unfold integerRationalRemainderSource samePromoteOps jintOps at h
    cases ha : checkedMul x.den k with
    | error e => simp [← Int.natCast_ediv, ha, Bind.bind, Except.bind] at h
    | ok a =>
      cases hn : JInt.mod a x.num with
      | error e => simp [← Int.natCast_ediv, ha, hn, Bind.bind, Except.bind] at h
      | ok n =>
        simp only [ha, hn, Bind.bind, Except.bind] at h
        obtain ⟨hnorm, hpos, _⟩ := rationalBitsSource_spec n x.den r h
        exact ⟨hnorm, hpos⟩
  · intro ⟨h1, h2⟩; simp [← Int.natCast_ediv, roundBoolRationalSource, denominatorRationalSource, h1, h2]
  · intro hnot
    cases denomFalse <;> cases targetIsInt <;> simp_all [roundBoolRationalSource, denominatorRationalSource]

/-- Rational gcd, lcm, gcdx, power, equality with floats/complex, hashing, and
rationalize-from-rational methods obey their structural contracts. -/
def RationalGcdLcmGcdxExact : Prop :=
  ∀ (t s : IntTy) (x : Rat t) (y : Rat s) (qx qy : Rational Int) (n : JInt s)
    (isinfX : Rat t → Bool) (isinfY : Rat s → Bool)
    (gcd : JInt t → JInt s → Jl (JInt (t.promote s)))
    (lcm : JInt t → JInt s → Jl (JInt (t.promote s)))
    (intGcdx : Int → Int → Jl (Int × Int × Int))
    (powerBySquaring : Rat t → JInt s → Jl (Rat t))
    (one : ComplexValue (Rat t) → ComplexValue (Rat t))
    (zc : ComplexValue (Rat t))
    (ldexp : JuliaLean.base.float.FV .f64 → JInt .i64 → JuliaLean.base.float.FV .f64)
    (f : JuliaLean.base.float.FV .f64),
    (∀ u v g a b, intGcdx u v = .ok (g, a, b) → a * u + b * v = g) →
    let isinfI : Rational Int → Bool := fun q => decide (q.den = 0)
    let intGcd : Int → Int → Jl Int := fun a b => .ok (Nat.gcd a.natAbs b.natAbs : Int)
    let intLcm : Int → Int → Jl Int := fun a b => .ok (Nat.lcm a.natAbs b.natAbs : Int)
    (isinfX x != isinfY y →
      gcdRationalSource isinfX isinfY gcd lcm x y =
        .error (.argumentError "gcd is not defined between infinite and finite numbers") ∧
      lcmRationalSource isinfX isinfY lcm gcd x y =
        .error (.argumentError "lcm is not defined between infinite and finite numbers")) ∧
    (isinfX x = isinfY y → ∀ gn ld, gcd x.num y.num = .ok gn → lcm x.den y.den = .ok ld →
      gcdRationalSource isinfX isinfY gcd lcm x y = .ok (unsafeRationalSameSource gn ld)) ∧
    (isinfX x = isinfY y → ∀ ln gd, lcm x.num y.num = .ok ln → gcd x.den y.den = .ok gd →
      lcmRationalSource isinfX isinfY lcm gcd x y = .ok (unsafeRationalSameSource ln gd)) ∧
    ((isinfI qx != isinfI qy) = false →
      gcdRationalSource isinfI isinfI intGcd intLcm qx qy =
        .ok ⟨(Nat.gcd qx.num.natAbs qy.num.natAbs : Int), (Nat.lcm qx.den.natAbs qy.den.natAbs : Int)⟩ ∧
      lcmRationalSource isinfI isinfI intLcm intGcd qx qy =
        .ok ⟨(Nat.lcm qx.num.natAbs qy.num.natAbs : Int), (Nat.gcd qx.den.natAbs qy.den.natAbs : Int)⟩) ∧
    (0 < qx.den → 0 < qy.den → qx.num = 0 → qy.num = 0 →
      gcdxRationalSource isinfI isinfI intGcd intLcm
        (fun m => decide (m = 0)) (fun _ => 0) (fun _ => 1)
        (fun m => decide (m = 0)) (fun m => decide (m = 0))
        (fun c a b => if c then a else b)
        (fun a b => .ok (a.tdiv b)) (fun a b => .ok (a.tdiv b))
        (fun a b => .ok (a.tdiv b)) (fun a b => .ok (a.tdiv b))
        (· * ·) intGcdx qx qy =
        .ok (⟨0, (Nat.lcm qx.den.natAbs qy.den.natAbs : Int)⟩, 0, 0)) ∧
    (0 < qx.den → 0 < qy.den → (qx.num ≠ 0 ∨ qy.num ≠ 0) →
      ∀ g a b,
        intGcdx
          (qx.num.tdiv (Nat.gcd qx.num.natAbs qy.num.natAbs : Int) *
            (Nat.lcm qx.den.natAbs qy.den.natAbs : Int).tdiv qx.den)
          (qy.num.tdiv (Nat.gcd qx.num.natAbs qy.num.natAbs : Int) *
            (Nat.lcm qx.den.natAbs qy.den.natAbs : Int).tdiv qy.den) = .ok (g, a, b) →
        gcdxRationalSource isinfI isinfI intGcd intLcm
          (fun m => decide (m = 0)) (fun _ => 0) (fun _ => 1)
          (fun m => decide (m = 0)) (fun m => decide (m = 0))
          (fun c u v => if c then u else v)
          (fun u v => .ok (u.tdiv v)) (fun u v => .ok (u.tdiv v))
          (fun u v => .ok (u.tdiv v)) (fun u v => .ok (u.tdiv v))
          (· * ·) intGcdx qx qy =
          .ok (⟨(Nat.gcd qx.num.natAbs qy.num.natAbs : Int),
                (Nat.lcm qx.den.natAbs qy.den.natAbs : Int)⟩, a, b) ∧
        a * (qx.num.tdiv (Nat.gcd qx.num.natAbs qy.num.natAbs : Int) *
              (Nat.lcm qx.den.natAbs qy.den.natAbs : Int).tdiv qx.den) +
        b * (qy.num.tdiv (Nat.gcd qx.num.natAbs qy.num.natAbs : Int) *
              (Nat.lcm qx.den.natAbs qy.den.natAbs : Int).tdiv qy.den) = g) ∧
    (0 ≤ n.val → powRationalIntegerSource powerBySquaring x n = powerBySquaring x n) ∧
    (n.val < 0 → ∀ invX, invRatSource (jintOps t) x = .ok invX →
      powRationalIntegerSource powerBySquaring x n = powerBySquaring invX (-n)) ∧
    powComplexRationalBoolSource one zc true = zc ∧
    powComplexRationalBoolSource one zc false = one zc ∧
    lerpiSource (· - ·) (fun c (q : Rational Int) => .ok (c * q.num)) (fun q _ => .ok q)
      (fun c (q : Rational Int) => .ok (c * q.num)) (fun q _ => .ok q) (fun u v => .ok (u + v))
      (0 : Int) (1 : Int) (⟨1, 1⟩ : Rational Int) (⟨2, 1⟩ : Rational Int) = .ok 1 ∧
    eqRatFloatSource JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.int.count_ones
      (fun c => c == JInt.lit .i64 1) (fun d => d - JInt.lit t 1)
      JuliaLean.base.int.top_set_bit ldexp JuliaLean.base.float.eq_FI
      (fun a b => JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.float_BitInteger a) (JuliaLean.base.float.float_BitInteger b))
      JuliaLean.base.float.eq_IEEEFloat x f =
      eqFloatRatSource JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.int.count_ones
        (fun c => c == JInt.lit .i64 1) (fun d => d - JInt.lit t 1)
        JuliaLean.base.int.top_set_bit ldexp JuliaLean.base.float.eq_FI
        (fun a b => JuliaLean.base.float.div_IEEEFloat
          (JuliaLean.base.float.float_BitInteger a) (JuliaLean.base.float.float_BitInteger b))
        JuliaLean.base.float.eq_IEEEFloat f x ∧
    (JuliaLean.base.float.isfinite_IEEEFloat f = false →
      eqFloatRatSource JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.int.count_ones
        (fun c => c == JInt.lit .i64 1) (fun d => d - JInt.lit t 1)
        JuliaLean.base.int.top_set_bit ldexp JuliaLean.base.float.eq_FI
        (fun a b => JuliaLean.base.float.div_IEEEFloat
          (JuliaLean.base.float.float_BitInteger a) (JuliaLean.base.float.float_BitInteger b))
        JuliaLean.base.float.eq_IEEEFloat f x =
        JuliaLean.base.float.eq_IEEEFloat f
          (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat x))

theorem rationalGcdLcmGcdxExact_proven : RationalGcdLcmGcdxExact := by
  intro t s x y qx qy n isinfX isinfY gcd lcm intGcdx powerBySquaring one zc ldexp f hbezout
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro hne
    simp [← Int.natCast_ediv, gcdRationalSource, lcmRationalSource, hne, Bind.bind, Except.bind]; exact ⟨rfl, rfl⟩
  · intro heq gn ld hg hl
    simp [← Int.natCast_ediv, gcdRationalSource, unsafeRationalSameSource, unsafeRationalSameSource, heq, hg, hl, Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
  · intro heq ln gd hl hg
    simp [← Int.natCast_ediv, lcmRationalSource, unsafeRationalSameSource, unsafeRationalSameSource, heq, hl, hg, Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
  · intro heq
    refine ⟨?_, ?_⟩
    · simp [← Int.natCast_ediv, gcdRationalSource, heq, unsafeRationalSameSource, unsafeRationalSameSource, Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
    · simp [← Int.natCast_ediv, lcmRationalSource, heq, unsafeRationalSameSource, unsafeRationalSameSource, Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
  · intro hxd hyd hxn0 hyn0
    have hinf : (decide (qx.den = 0) != decide (qy.den = 0)) = false := by
      simp [← Int.natCast_ediv, show qx.den ≠ 0 by omega, show qy.den ≠ 0 by omega]
    simp [← Int.natCast_ediv, gcdxRationalSource, gcdRationalSource, hinf, hxn0, hyn0,
      unsafeRationalSameSource, unsafeRationalSameSource, Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
  · intro hxd hyd hne g a b hgcdx
    have hinf : (decide (qx.den = 0) != decide (qy.den = 0)) = false := by
      simp [← Int.natCast_ediv, show qx.den ≠ 0 by omega, show qy.den ≠ 0 by omega]
    have hcnum : decide ((Nat.gcd qx.num.natAbs qy.num.natAbs : Int) = 0) = false := by
      rcases hne with h1 | h1
      · have := Nat.gcd_pos_of_pos_left qy.num.natAbs (Int.natAbs_pos.mpr h1)
        exact decide_eq_false (by omega)
      · have := Nat.gcd_pos_of_pos_right qx.num.natAbs (Int.natAbs_pos.mpr h1)
        exact decide_eq_false (by omega)
    have hcden : decide ((Nat.lcm qx.den.natAbs qy.den.natAbs : Int) = 0) = false := by
      simp [← Int.natCast_ediv, Nat.lcm_eq_zero_iff, show qx.den ≠ 0 by omega, show qy.den ≠ 0 by omega]
    refine ⟨?_, hbezout _ _ g a b hgcdx⟩
    simp only [gcdxRationalSource, gcdRationalSource, hinf, hcnum, hcden, Bool.false_eq_true,
      ↓reduceIte, hgcdx, unsafeRationalSameSource, unsafeRationalSameSource,
      Bind.bind, Except.bind, Pure.pure, Except.pure, unsafeRationalTypeSource, Functor.map, id]
  · intro hn
    simp [← Int.natCast_ediv, powRationalIntegerSource, powRationalIntegerGeneric, hn]
  · intro hn invX hinv
    have hnge : ¬ 0 ≤ n.val := by omega
    simp [← Int.natCast_ediv, powRationalIntegerSource, powRationalIntegerGeneric, hnge, hinv, Bind.bind, Except.bind]
  · intro hfin
    simp [← Int.natCast_ediv, eqFloatRatSource, abstractFloatRatSource, hfin]

/-- Fixed-width integer rationalization preserves in-range integers and records overflow signs. -/
def IntegerRationalizeRange : Prop :=
  ∀ (t : IntTy) (x : Int) (kvs : List String),
    let result := rationalizeIntegerTypedSource (JInt t) (jintOps t)
      (fun n => decide (n < 0)) (fun n => decide (n < t.min)) (fun n => decide (t.max < n))
      (JInt.convert t) (fun _ => 1) x kvs
    (t.signed = false → x < 0 → result = .error (.overflowError "cannot negate unsigned number")) ∧
    (t.signed = true ∨ 0 ≤ x →
      (x < t.min → ∃ r, result = .ok r ∧ r.num.val = -1 ∧ r.den.val = 0) ∧
      (t.max < x → ∃ r, result = .ok r ∧ r.num.val = 1 ∧ r.den.val = 0) ∧
      (t.min ≤ x ∧ x ≤ t.max → ∃ r, result = .ok r ∧ r.num.val = x ∧ r.den.val = 1 ∧ Normalized r))

theorem integerRationalizeRange_proven : IntegerRationalizeRange := by
  intro t x kvs
  dsimp only
  have hz : (JInt.lit t 0).val = 0 := by cases t <;> decide
  have ho : (JInt.lit t 1).val = 1 := by cases t <;> decide
  have h1 : t.min ≤ 1 ∧ 1 ≤ t.max := by cases t <;> decide
  refine ⟨?_, ?_⟩
  · intro hu hx
    simp [rationalizeIntegerTypedSource, jintOps, hu, hx, throwNegateUnsignedSource, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind, Bind.bind, Except.bind]
  · intro hx
    have hsign : ((!t.signed && decide (x < 0)) = false) := by
      rcases hx with hs | hx
      · simp [hs]
      · simp [show ¬ x < 0 by omega]
    refine ⟨?_, ?_, ?_⟩
    · intro hlo
      have hs : t.signed = true := by
        cases ht : t.signed
        · have hm : t.min = 0 := by cases t <;> simp_all [IntTy.signed, IntTy.min]
          rcases hx with hx | hx <;> simp_all <;> omega
        · rfl
      have hm : (JInt.lit t (-1)).val = -1 := by cases t <;> simp_all [IntTy.signed] <;> decide
      refine ⟨⟨JInt.lit t (-1), JInt.lit t 0⟩, ?_, hm, hz⟩
      simp [rationalizeIntegerTypedSource, jintOps, hsign, hlo, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro hhi
      have hnlo : ¬ x < t.min := by
        have hb : t.min ≤ t.max := by cases t <;> decide
        omega
      refine ⟨⟨JInt.lit t 1, JInt.lit t 0⟩, ?_, ho, hz⟩
      simp [rationalizeIntegerTypedSource, jintOps, hsign, hnlo, hhi, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro hfit
      refine ⟨⟨⟨x,hfit⟩, JInt.lit t 1⟩, ?_, rfl, ho, ?_⟩
      · simp [rationalizeIntegerTypedSource, jintOps, rationalIntAsSource, hsign,
          show ¬ x < t.min by omega, show ¬ t.max < x by omega,
          JInt.convert, hfit, h1, JInt.lit, JInt.wrap, wrapInt_of_inRange t 1 h1,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp [Normalized, ho]

/-- Numeric conversion preserves both values; generic unary minus changes only the numerator sign. -/
def GenericRationalValueContracts : Prop :=
  ∀ (S T : Type) (valueS : S → Int) (valueT : T → Int)
    (convert : S → Jl T) (neg : T → Jl T),
    (∀ s t, convert s = .ok t → valueT t = valueS s) →
    (∀ s t, neg s = .ok t → valueT t = -valueT s) →
    (∀ (x : Rational S) (r : Rational T), convertRatSource T convert x = .ok r →
      valueT r.num = valueS x.num ∧ valueT r.den = valueS x.den) ∧
    (∀ (x r : Rational T), negRatSource neg x = .ok r →
      valueT r.num = -valueT x.num ∧ r.den = x.den) ∧
    (∀ (n d : S) (r : Rational T), unsafeRationalTypeSource T convert convert n d = .ok r →
      valueT r.num = valueS n ∧ valueT r.den = valueS d)

theorem genericRationalValueContracts_proven : GenericRationalValueContracts := by
  intro S T valueS valueT convert neg hconvert hneg
  refine ⟨?_, ?_, ?_⟩
  · intro x r h
    unfold convertRatSource at h
    cases hn : convert x.num with
    | error e => simp [hn, Bind.bind, Except.bind] at h
    | ok n =>
      cases hd : convert x.den with
      | error e => simp [hn, hd, Bind.bind, Except.bind] at h
      | ok d =>
        have heq : unsafeRationalSameSource n d = r := by
          simpa [hn, hd, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst heq
        exact ⟨hconvert _ _ hn, hconvert _ _ hd⟩
  · intro x r h
    unfold negRatSource at h
    cases hn : neg x.num with
    | error e => simp [hn, Bind.bind, Except.bind] at h
    | ok n =>
      have heq : unsafeRationalSameSource n x.den = r := by
        simpa [hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
      subst heq
      exact ⟨hneg _ _ hn, rfl⟩
  · intro n d r h
    unfold unsafeRationalTypeSource at h
    cases hn : convert n with
    | error e => simp [hn, Bind.bind, Except.bind] at h
    | ok nn =>
      cases hd : convert d with
      | error e => simp [hn, hd, Bind.bind, Except.bind] at h
      | ok dd =>
        have heq : (⟨nn, dd⟩ : Rational T) = r := by
          simpa [hn, hd, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst heq
        exact ⟨hconvert _ _ hn, hconvert _ _ hd⟩

/-- Finite float equality rejects non-dyadic denominators and agrees with integer equality on denominator one. -/
def FiniteFloatEquality : Prop :=
  ∀ (f : JuliaLean.base.float.FTy) (t : IntTy) (x : JuliaLean.base.float.FV f) (q : Rat t)
    (ldexp : JuliaLean.base.float.FV f → JInt .i64 → JuliaLean.base.float.FV f),
    (∀ x, ldexp x (JInt.lit .i64 0) = x) →
    JuliaLean.base.float.isfinite_IEEEFloat x = true →
    (JuliaLean.base.int.count_ones q.den ≠ JInt.lit .i64 1 → eqFloatRatSource JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.int.count_ones
      (fun c => c == JInt.lit .i64 1) (fun d => d - JInt.lit t 1)
      JuliaLean.base.int.top_set_bit ldexp JuliaLean.base.float.eq_FI
      (fun a b => JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.float_BitInteger a) (JuliaLean.base.float.float_BitInteger b))
      (fun a b => JuliaLean.base.float.eq_IEEEFloat (JuliaLean.base.float.convertFloat .f64 a) b) x q = false) ∧
    (q.den = JInt.lit t 1 → eqFloatRatSource JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.int.count_ones
      (fun c => c == JInt.lit .i64 1) (fun d => d - JInt.lit t 1)
      JuliaLean.base.int.top_set_bit ldexp JuliaLean.base.float.eq_FI
      (fun a b => JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.float_BitInteger a) (JuliaLean.base.float.float_BitInteger b))
      (fun a b => JuliaLean.base.float.eq_IEEEFloat (JuliaLean.base.float.convertFloat .f64 a) b) x q = JuliaLean.base.float.eq_FI x q.num)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finiteFloatEquality_proven : FiniteFloatEquality := by
  intro f t x q ldexp hzero hfin
  refine ⟨?_, ?_⟩
  · intro hnot
    have hnotval : (JuliaLean.base.int.count_ones q.den).val ≠ (JInt.lit .i64 1).val := by
      intro h; exact hnot (Subtype.ext h)
    simp [eqFloatRatSource, hfin, hnotval]
  · intro hd
    have hc : JuliaLean.base.int.count_ones (JInt.lit t 1) = JInt.lit .i64 1 := by cases t <;> decide
    have hs : (JInt.lit t 1) - (JInt.lit t 1) = JInt.lit t 0 := by cases t <;> decide
    have ht : JuliaLean.base.int.top_set_bit (JInt.lit t 0) = JInt.lit .i64 0 := by cases t <;> decide
    simp [eqFloatRatSource, hfin, hd, hc, hs, ht, hzero]

/-- Integer powers have the mathematical numerator/denominator power ratio, including negative exponents. -/
def RationalIntegerPowerValue : Prop :=
  ∀ (t : IntTy) (x r : Rat t) (n : Int)
    (powerBySquaring : Rat t → Int → Jl (Rat t)),
    (∀ (q out : Rat t) (k : Int), 0 ≤ k → powerBySquaring q k = .ok out →
      out.num.val * q.den.val ^ k.toNat = q.num.val ^ k.toNat * out.den.val) →
    Normalized x → 0 < x.den.val → x.num.val ≠ 0 →
    powRationalIntegerGeneric (fun k => decide (0 ≤ k)) (- ·)
      (invRatSource (jintOps t)) powerBySquaring x n = .ok r →
    if 0 ≤ n then r.num.val * x.den.val ^ n.toNat = x.num.val ^ n.toNat * r.den.val
    else r.num.val * x.num.val ^ n.natAbs = x.den.val ^ n.natAbs * r.den.val

theorem rationalIntegerPowerValue_proven : RationalIntegerPowerValue := by
  intro t x r n power hpower hnorm hd hn h
  unfold powRationalIntegerGeneric at h
  by_cases hnonneg : 0 ≤ n
  · simp only [hnonneg, decide_true, ↓reduceIte] at h ⊢
    exact hpower x r n hnonneg h
  · simp only [hnonneg, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hi : invRatSource (jintOps t) x with
    | error e => simp [hi, Bind.bind, Except.bind] at h
    | ok inverse =>
      simp only [hi, Bind.bind, Except.bind] at h
      have he := hpower inverse r (-n) (by omega) h
      have hinv := (inverseZeroIsInfinity_proven t x inverse).2 hnorm hd hn hi
      have hnum := hinv.2.2.1
      have hden : 0 < inverse.den.val := hinv.2.1
      have hnat : (-n).toNat = n.natAbs := by
        have := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega)
        omega
      rw [hnat] at he
      have hpow : 0 < inverse.den.val ^ n.natAbs := by
        induction n.natAbs with
        | zero => simp
        | succ k ih => simpa [Int.pow_succ] using Int.mul_pos ih hden
      apply Int.eq_of_mul_eq_mul_right (by omega : inverse.den.val ^ n.natAbs ≠ 0)
      calc
        r.num.val * x.num.val ^ n.natAbs * inverse.den.val ^ n.natAbs =
            (r.num.val * inverse.den.val ^ n.natAbs) * x.num.val ^ n.natAbs := by
              simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ = (inverse.num.val ^ n.natAbs * r.den.val) * x.num.val ^ n.natAbs := by rw [he]
        _ = (inverse.num.val * x.num.val) ^ n.natAbs * r.den.val := by
              rw [Int.mul_pow]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ = (x.den.val * inverse.den.val) ^ n.natAbs * r.den.val := by rw [hnum]
        _ = x.den.val ^ n.natAbs * r.den.val * inverse.den.val ^ n.natAbs := by
              rw [Int.mul_pow]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Complex integer division preserves the exact real and imaginary quotient values. -/
def ComplexIntegerQuotientValues : Prop :=
  ∀ (t : IntTy) (x y : ComplexValue (JInt t)) (q : ComplexValue (Rat t)),
    complexIntegerQuotientSource x y = .ok q →
    Normalized q.re ∧ Normalized q.im ∧
    q.re.num.val * (y.re.val * y.re.val + y.im.val * y.im.val) =
      (x.re.val * y.re.val + x.im.val * y.im.val) * q.re.den.val ∧
    q.im.num.val * (y.re.val * y.re.val + y.im.val * y.im.val) =
      (x.im.val * y.re.val - x.re.val * y.im.val) * q.im.den.val

set_option maxHeartbeats 2000000 in
theorem complexIntegerQuotientValues_proven : ComplexIntegerQuotientValues := by
  intro t x y q h
  unfold complexIntegerQuotientSource divideComplexIntegersSource at h
  dsimp only [Bind.bind, Except.bind] at h
  cases hg : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) y.re y.im with
  | error e => simp [← Int.natCast_ediv, hg, Bind.bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨cr,dr⟩
    simp only [hg, Bind.bind, Except.bind] at h
    cases h_c2 : checkedMul y.re cr with
    | error e => simp [← Int.natCast_ediv, h_c2, Bind.bind, Except.bind] at h
    | ok c2 =>
      simp only [h_c2, Bind.bind, Except.bind] at h
      cases h_d2 : checkedMul y.im dr with
      | error e => simp [← Int.natCast_ediv, h_d2, Bind.bind, Except.bind] at h
      | ok d2 =>
        simp only [h_d2, Bind.bind, Except.bind] at h
        cases h_den : checkedAdd c2 d2 with
        | error e => simp [← Int.natCast_ediv, h_den, Bind.bind, Except.bind] at h
        | ok den =>
          simp only [h_den, Bind.bind, Except.bind] at h
          cases h_ac : checkedMul x.re cr with
          | error e => simp [← Int.natCast_ediv, h_ac, Bind.bind, Except.bind] at h
          | ok ac =>
            simp only [h_ac, Bind.bind, Except.bind] at h
            cases h_bd : checkedMul x.im dr with
            | error e => simp [← Int.natCast_ediv, h_bd, Bind.bind, Except.bind] at h
            | ok bd =>
              simp only [h_bd, Bind.bind, Except.bind] at h
              cases h_re : checkedAdd ac bd with
              | error e => simp [← Int.natCast_ediv, h_re, Bind.bind, Except.bind] at h
              | ok re =>
                simp only [h_re, Bind.bind, Except.bind] at h
                cases h_bc : checkedMul x.im cr with
                | error e => simp [← Int.natCast_ediv, h_bc, Bind.bind, Except.bind] at h
                | ok bc =>
                  simp only [h_bc, Bind.bind, Except.bind] at h
                  cases h_ad : checkedMul x.re dr with
                  | error e => simp [← Int.natCast_ediv, h_ad, Bind.bind, Except.bind] at h
                  | ok ad =>
                    simp only [h_ad, Bind.bind, Except.bind] at h
                    cases h_nad : checkedNeg ad with
                    | error e => simp [← Int.natCast_ediv, h_nad, Bind.bind, Except.bind] at h
                    | ok nad =>
                      simp only [h_nad, Bind.bind, Except.bind] at h
                      cases h_im : checkedAdd bc nad with
                      | error e => simp [← Int.natCast_ediv, h_im, Bind.bind, Except.bind] at h
                      | ok im =>
                        simp only [h_im, Bind.bind, Except.bind] at h
                        unfold exactDivideComplexReal exactDivideIntsSource at h
                        cases h_qr : rationalBitsSource re den with
                        | error e => simp [← Int.natCast_ediv, h_qr, Bind.bind, Except.bind] at h
                        | ok qr =>
                          simp only [h_qr, Bind.bind, Except.bind] at h
                          cases h_qi : rationalBitsSource im den with
                          | error e => simp [← Int.natCast_ediv, h_qi, Bind.bind, Except.bind] at h
                          | ok qi =>
                            simp only [h_qi, Bind.bind, Except.bind] at h
                            have v_c2 := checkedMul_ok_val h_c2
                            have v_d2 := checkedMul_ok_val h_d2
                            have v_den := checkedAdd_ok_val h_den
                            have v_ac := checkedMul_ok_val h_ac
                            have v_bd := checkedMul_ok_val h_bd
                            have v_re := checkedAdd_ok_val h_re
                            have v_bc := checkedMul_ok_val h_bc
                            have v_ad := checkedMul_ok_val h_ad
                            have v_nad := checkedNeg_ok_val h_nad
                            have v_im := checkedAdd_ok_val h_im
                            have hpair : (ComplexValue.mk qr qi) = q := by simpa [← Int.natCast_ediv, Pure.pure, Except.pure] using h
                            subst hpair
                            obtain ⟨hrn, _, hrc⟩ := rationalBitsSource_spec re den qr h_qr
                            obtain ⟨hin, _, hic⟩ := rationalBitsSource_spec im den qi h_qi
                            obtain ⟨_, hcr, hdr, _⟩ := divgcdFactors y.re y.im cr dr hg
                            let g : Int := Nat.gcd y.re.val.natAbs y.im.val.natAbs
                            have hden : den.val * g = y.re.val * y.re.val + y.im.val * y.im.val := by
                              rw [v_den, Int.add_mul, v_c2, v_d2, Int.mul_assoc, Int.mul_assoc, hcr, hdr]
                            have hre : re.val * g = x.re.val * y.re.val + x.im.val * y.im.val := by
                              rw [v_re, Int.add_mul, v_ac, v_bd, Int.mul_assoc, Int.mul_assoc, hcr, hdr]
                            have him : im.val * g = x.im.val * y.re.val - x.re.val * y.im.val := by
                              rw [v_im, Int.add_mul, v_bc, v_nad, v_ad, Int.neg_mul, Int.mul_assoc, Int.mul_assoc, hcr, hdr]
                              rfl
                            refine ⟨hrn, hin, ?_, ?_⟩
                            · calc
                                qr.num.val * (y.re.val * y.re.val + y.im.val * y.im.val) = qr.num.val * (den.val * g) := by rw [hden]
                                _ = (qr.num.val * den.val) * g := by rw [Int.mul_assoc]
                                _ = (re.val * qr.den.val) * g := by rw [hrc]
                                _ = (re.val * g) * qr.den.val := by rw [Int.mul_right_comm]
                                _ = (x.re.val * y.re.val + x.im.val * y.im.val) * qr.den.val := by rw [hre]
                            · calc
                                qi.num.val * (y.re.val * y.re.val + y.im.val * y.im.val) = qi.num.val * (den.val * g) := by rw [hden]
                                _ = (qi.num.val * den.val) * g := by rw [Int.mul_assoc]
                                _ = (im.val * qi.den.val) * g := by rw [hic]
                                _ = (im.val * g) * qi.den.val := by rw [Int.mul_right_comm]
                                _ = (x.im.val * y.re.val - x.re.val * y.im.val) * qi.den.val := by rw [him]

private theorem fraction_scale_divide (mnum mden lnum lden anum aden weight divisor : Int)
    (hden : mden ≠ 0) (hm : mnum * aden = (weight * anum) * mden)
    (hl : lnum * (mden * divisor) = mnum * lden) :
    lnum * (aden * divisor) = (weight * anum) * lden := by
  apply Int.eq_of_mul_eq_mul_right hden
  calc
    lnum * (aden * divisor) * mden = (lnum * (mden * divisor)) * aden := by ac_rfl
    _ = (mnum * lden) * aden := by rw [hl]
    _ = (mnum * aden) * lden := by ac_rfl
    _ = ((weight * anum) * mden) * lden := by rw [hm]
    _ = ((weight * anum) * lden) * mden := by ac_rfl

private theorem fraction_barycentric_add (ln ld rn rd qn qd an ad bn bd j d : Int)
    (hld : ld ≠ 0) (hrd : rd ≠ 0)
    (hl : ln * (ad * d) = ((d-j) * an) * ld)
    (hr : rn * (bd * d) = (j * bn) * rd)
    (hq : qn * (ld * rd) = (ln * rd + rn * ld) * qd) :
    qn * (d * (ad * bd)) = ((d-j)*an*bd + j*bn*ad) * qd := by
  apply Int.eq_of_mul_eq_mul_right (Int.mul_ne_zero hld hrd)
  calc
    qn * (d * (ad * bd)) * (ld * rd) = (qn * (ld * rd)) * (d * (ad * bd)) := by ac_rfl
    _ = ((ln * rd + rn * ld) * qd) * (d * (ad * bd)) := by rw [hq]
    _ = ((ln * (ad*d)) * rd * bd + (rn * (bd*d)) * ld * ad) * qd := by
      simp only [Int.add_mul]; ac_rfl
    _ = ((((d-j)*an)*ld) * rd * bd + ((j*bn)*rd) * ld * ad) * qd := by rw [hl, hr]
    _ = (((d-j)*an*bd + j*bn*ad) * qd) * (ld*rd) := by
      simp only [Int.add_mul]; ac_rfl

/-- Interpolation computes the exact barycentric combination at every in-range integer index. -/
def RationalInterpolationValue : Prop :=
  ∀ (t : IntTy) (j d : JInt t) (a b r : Rat t),
    0 ≤ j.val → j.val ≤ d.val → 0 < d.val → 0 < a.den.val → 0 < b.den.val →
    lerpiBitsSource j d a b = .ok r →
    Normalized r ∧ 0 < r.den.val ∧
    r.num.val * (d.val * (a.den.val * b.den.val)) =
      ((d.val-j.val) * a.num.val * b.den.val + j.val * b.num.val * a.den.val) * r.den.val

theorem rationalInterpolationValue_proven : RationalInterpolationValue := by
  intro t j d a b r hj hjd hd ha hb h
  have hdne : d.val ≠ 0 := by omega
  have hw : (d-j).val = d.val-j.val := by
    change wrapInt t (d.val-j.val) = d.val-j.val
    have hm : t.min ≤ 0 := by cases t <;> decide
    have hx := d.property
    exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  unfold lerpiBitsSource lerpiSource at h
  unfold slashRationalUnionSource at h
  cases h_ml : mulIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (d-j) a with
  | error e => simp [← Int.natCast_ediv, h_ml, Bind.bind, Except.bind] at h
  | ok ml =>
    simp only [h_ml, Bind.bind, Except.bind] at h
    cases h_l : divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) ml d with
    | error e => simp [← Int.natCast_ediv, h_l, Bind.bind, Except.bind] at h
    | ok l =>
      simp only [h_l, Bind.bind, Except.bind] at h
      cases h_mr : mulIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) j b with
      | error e => simp [← Int.natCast_ediv, h_mr, Bind.bind, Except.bind] at h
      | ok mr =>
        simp only [h_mr, Bind.bind, Except.bind] at h
        cases h_right : divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) mr d with
        | error e => simp [← Int.natCast_ediv, h_right, Bind.bind, Except.bind] at h
        | ok right =>
          simp only [h_right, Bind.bind, Except.bind] at h
          have ml_spec := (rationalArithmeticExact_proven t a a ml (d-j) ha ha).2.2.2.2.2.2.2.1 h_ml
          have l_spec := (rationalArithmeticExact_proven t ml ml l d ml_spec.1 ml_spec.1).2.2.2.2.1 hdne h_l
          have mr_spec := (rationalArithmeticExact_proven t b b mr j hb hb).2.2.2.2.2.2.2.1 h_mr
          have right_spec := (rationalArithmeticExact_proven t mr mr right d mr_spec.1 mr_spec.1).2.2.2.2.1 hdne h_right
          have sum_spec := (rationalArithmeticExact_proven t l right r j l_spec.1 right_spec.1).1 h
          refine ⟨sum_spec.1, sum_spec.2.1, ?_⟩
          have hl := fraction_scale_divide ml.num.val ml.den.val l.num.val l.den.val a.num.val a.den.val (d-j).val d.val
            (by omega) ml_spec.2 l_spec.2
          have hr := fraction_scale_divide mr.num.val mr.den.val right.num.val right.den.val b.num.val b.den.val j.val d.val
            (by omega) mr_spec.2 right_spec.2
          rw [hw] at hl
          exact fraction_barycentric_add l.num.val l.den.val right.num.val right.den.val r.num.val r.den.val
            a.num.val a.den.val b.num.val b.den.val j.val d.val (by omega) (by omega) hl hr sum_spec.2.2


/-- Rational display emits its decimal numerator and optional //denominator in order;
    read preserves an underlying read error; fraction parsing preserves the exact ratio. -/
def RationalIoContracts : Prop :=
  (∀ (t : IntTy) (x : Rat t) (io : Unit) (initial : String)
      (display : JInt t → String) (typed : Unit → Bool)
      (showValue : Unit → JInt t → StateT String Jl Unit)
      (print : Unit → String → StateT String Jl Unit),
    (∀ io n out, showValue io n out = .ok ((), out ++ display n)) →
    (∀ io s out, print io s out = .ok ((), out ++ s)) →
    showRationalSource showValue print (fun n => decide (n.val = 1)) typed io x initial =
      .ok ((), initial ++ display x.num ++
        (if x.den.val = 1 ∧ typed io = true then "" else "//" ++ display x.den))) ∧
  (∀ (T τ IO : Type) (read : IO → τ → Jl T)
      (divide : T → T → Jl (Rational T)) (io : IO) (target : τ) (e : JlError),
    read io target = .error e → readRationalSource read divide io target = .error e) ∧
  (∀ (t : IntTy) (text ns ds : String) (n d : JInt t) (r : Rat t)
      (split : String → Char → Nat → List String)
      (get : List String → Nat → Jl String) (starts : String → Char → Bool)
      (chop : String → String) (parse : IntTy → String → Jl (JInt t)),
    split text '/' 2 = [ns, ds] → get [ns, ds] 1 = .ok ns → get [ns, ds] 2 = .ok ds →
    parse t ns = .ok n → parse t (if starts ds '/' then chop ds else ds) = .ok d →
    parseRationalSource split List.length (fun l => decide (l = 1)) get starts chop parse
      (rationalIntAsSource (JInt t) (fun n => JInt.convert t n.val) (fun _ => JInt.lit t 1))
      (exactDivideIntsSource rationalBitsSource) t text = .ok r →
    Normalized r ∧ n.val * r.den.val = r.num.val * d.val)

theorem rationalIoContracts_proven : RationalIoContracts := by
  refine ⟨?_, ?_, ?_⟩
  · intro t x io initial display typed showValue print hs hp
    unfold showRationalSource
    simp only [numeratorRationalSource, denominatorRationalSource]
    by_cases hden : x.den.val = 1 <;> cases ht : typed io <;>
      simp [hden, ht, Bind.bind, StateT.bind, StateT.pure, hs, hp,
        Pure.pure, Except.bind, Except.pure, String.append_assoc]
  · intro T τ IO read divide io target e he
    simp [readRationalSource, he, Bind.bind, Except.bind]
  · intro t text ns ds n d r split get starts chop parse hsplit hg1 hg2 hn hd h
    unfold parseRationalSource at h
    simp only [hsplit, List.length_cons, List.length_nil, Nat.reduceAdd,
      decide_false, Bool.false_eq_true, ↓reduceIte, hg1, hg2, Bind.bind, Except.bind] at h
    cases hslash : starts ds '/' <;> simp only [hslash, Bool.false_eq_true, ↓reduceIte] at hd h
    all_goals
      simp only [hn, hd, Bind.bind, Except.bind, exactDivideIntsSource] at h
      obtain ⟨hnorm, _, hcross⟩ := rationalBitsSource_spec n d r h
      exact ⟨hnorm, hcross.symm⟩


/-- A finite rational unit range has one element per integer step, including both endpoints. -/
def RationalUnitRangeLength : Prop :=
  ∀ (R T Q : Type) (value : T → Int) (resultValue : Q → Int)
    (first last : R → Rational T) (sub add : T → T → T)
    (divide : T → T → Jl Q) (range : R) (q : Q) (k : Int),
    0 < value (first range).den →
    value (last range).num = value (first range).num + k * value (first range).den →
    value (sub (last range).num (first range).num) = value (last range).num - value (first range).num →
    value (add (sub (last range).num (first range).num) (first range).den) =
      value (sub (last range).num (first range).num) + value (first range).den →
    (∀ a b r, divide a b = .ok r → resultValue r = (value a).tdiv (value b)) →
    lengthRationalRangeSource first last sub add divide range = .ok q → resultValue q = k + 1

theorem rationalUnitRangeLength_proven : RationalUnitRangeLength := by
  intro R T Q value resultValue first last sub add divide range q k hd hl hs ha hdiv h
  have hv := hdiv _ _ _ h
  rw [ha, hs, hl] at hv
  have hnum : value (first range).num + k * value (first range).den - value (first range).num +
      value (first range).den = (k + 1) * value (first range).den := by rw [Int.add_mul, Int.one_mul]; omega
  rw [hnum, Int.mul_tdiv_cancel _ (by omega)] at hv
  exact hv

/-- Finite half-integer rationals use the same hash as their exact dyadic float. -/
def RationalHalfIntegerHash : Prop :=
  ∀ (t : IntTy) (h64 : t ≠ .i128 ∧ t ≠ .u128) (n : JInt t) (seed : JInt .u64)
    (hashInt : JInt t → JInt .u64 → JInt .u64)
    (hashFloat : JuliaLean.base.float.FV .f64 → JInt .u64 → JInt .u64)
    (hashInteger : {u : IntTy} → JInt u → JInt .u64 → JInt .u64)
    (ldexp : JuliaLean.base.float.FV .f64 → JInt .i64 → JuliaLean.base.float.FV .f64)
    (maxintfloat : JuliaLean.base.float.FV .f64 → JInt .u64),
    (∀ f, ldexp f (JInt.lit .i64 (-1)) = JuliaLean.base.float.div_IEEEFloat f (Fl.ofInt 2)) →
    JuliaLean.base.int.lt_BitUnsigned (JuliaLean.base.int.widenTo .u64 (JuliaLean.base.float.uabs n))
      (maxintfloat (JuliaLean.base.float.one_float .f64)) = true →
    hashRational64Source h64 hashInt hashFloat hashInteger ldexp maxintfloat (jintOps t).isodd
      JuliaLean.base.int.trailing_zeros JuliaLean.base.int.shr_Int JuliaLean.base.int.shl_Int
      ⟨n, JInt.lit t 2⟩ seed =
      hashFloat (floatConvertRatSource (JuliaLean.base.float.FV .f64)
        (JuliaLean.base.float.floatOfInt .f64) JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.convertFloat .f64) ⟨n, JInt.lit t 2⟩) seed

set_option maxRecDepth 10000 in
theorem rationalHalfIntegerHash_proven : RationalHalfIntegerHash := by
  intro t h64 n seed hashInt hashFloat hashInteger ldexp maxintfloat hldexp hbound
  have htwo : (JInt.lit t 2).val = 2 := by cases t <;> decide
  have hodd : (jintOps t).isodd (JInt.lit t 2) = false := by cases t <;> decide
  have htrail : JuliaLean.base.int.trailing_zeros (JInt.lit t 2) = JInt.lit .i64 1 := by cases t <;> decide
  have hshift : (JuliaLean.base.int.shr_Int (JInt.lit t 2) (JInt.lit .i64 1)).val = 1 := by cases t <;> decide
  have hneg : -(JInt.lit .i64 1) = JInt.lit .i64 (-1) := by decide
  have hfloatTwo : JuliaLean.base.float.floatOfInt .f64 (JInt.lit t 2) = Fl.ofInt 2 := by cases t <;> decide
  simp [floatConvertRatSource, JuliaLean.base.float.convertFloat, hfloatTwo, hldexp, hashRational64Source, numeratorRationalSource, denominatorRationalSource, htwo, hodd, htrail,
    hshift, hneg, hbound]

/-- Value-preserving promotion preserves both stored rational components. -/
def RationalPromotionAndZeroError : Prop :=
  (∀ (A B P : Type) (valueA : A → Int) (valueB : B → Int) (valueP : P → Int)
    (promote : A → B → Jl (P × P)) (a : A) (b : B) (r : Rational P),
    (∀ n d, promote a b = .ok (n,d) → valueP n = valueA a ∧ valueP d = valueB b) →
    unsafeRationalPromoteSource promote a b = .ok r →
    valueP r.num = valueA a ∧ valueP r.den = valueB b) ∧
  (∀ (τ ε α : Type) (argumentError : LazyString τ → ε) (target : τ),
    ∃ payload, throwRationalZeroSource (α := α) argumentError target = .error (argumentError payload) ∧
      payload.parts = [.lit "invalid rational: zero(", .val target, .lit ")//zero(", .val target, .lit ")"])

theorem rationalPromotionAndZeroError_proven : RationalPromotionAndZeroError := by
  refine ⟨?_, ?_⟩
  · intro A B P valueA valueB valueP promote a b r hp h
    unfold unsafeRationalPromoteSource at h
    cases hg : promote a b with
    | error e => simp [hg, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨n,d⟩
      have hr : unsafeRationalSameSource n d = r := by simpa [hg, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
      subst hr
      exact hp n d hg
  · intro τ ε α argumentError target
    exact ⟨_, rfl, rfl⟩


private theorem bwand_true (a b : Bool) : bwand a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem canonical_fraction_components {t s : IntTy} (x : Rat t) (y : Rat s)
    (hx : Normalized x) (hy : Normalized y) (hdx : 0 < x.den.val) (hdy : 0 < y.den.val)
    (h : x.num.val * y.den.val = y.num.val * x.den.val) :
    x.num.val = y.num.val ∧ x.den.val = y.den.val := by
  have habs := congrArg Int.natAbs h
  simp only [Int.natAbs_mul] at habs
  have hxy : x.den.val.natAbs ∣ y.den.val.natAbs := by
    apply Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hx.2)
    rw [habs]
    exact ⟨y.num.val.natAbs, Nat.mul_comm _ _⟩
  have hyx : y.den.val.natAbs ∣ x.den.val.natAbs := by
    apply Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hy.2)
    rw [← habs]
    exact ⟨x.num.val.natAbs, Nat.mul_comm _ _⟩
  have hd : x.den.val = y.den.val := by
    have he := congrArg Int.ofNat (Nat.dvd_antisymm hxy hyx)
    change (x.den.val.natAbs : Int) = (y.den.val.natAbs : Int) at he
    simpa only [Int.natAbs_of_nonneg (Int.le_of_lt hdx), Int.natAbs_of_nonneg (Int.le_of_lt hdy)] using he
  refine ⟨?_, hd⟩
  rw [hd] at h
  exact (Int.mul_eq_mul_right_iff (by omega)).mp h

/-- Complex-rational equality is equality of real values with zero imaginary value. -/
def ComplexRationalEqualityValue : Prop :=
  ∀ (t : IntTy) (z : ComplexValue (Rat t)) (x : Rat t),
    Normalized z.re → Normalized x → 0 < z.re.den.val → 0 < x.den.val →
    let eqR := eqRatSource (fun a b : JInt t => a.val == b.val) (fun a b : JInt t => a.val == b.val)
    (eqComplexRatSource (fun z => decide (z.im.num.val = 0)) ComplexValue.re eqR z x = true ↔
      z.im.num.val = 0 ∧ z.re.num.val * x.den.val = x.num.val * z.re.den.val) ∧
    (eqRatComplexSource (fun z => decide (z.im.num.val = 0)) ComplexValue.re eqR x z = true ↔
      z.im.num.val = 0 ∧ z.re.num.val * x.den.val = x.num.val * z.re.den.val)

theorem complexRationalEqualityValue_proven : ComplexRationalEqualityValue := by
  intro t z x hz hx hdz hdx
  dsimp only
  have eqspec : (eqComplexRatSource (fun z => decide (z.im.num.val = 0)) ComplexValue.re
      (eqRatSource (fun a b : JInt t => a.val == b.val) (fun a b : JInt t => a.val == b.val)) z x = true ↔
      z.im.num.val = 0 ∧ z.re.num.val * x.den.val = x.num.val * z.re.den.val) := by
    simp only [eqComplexRatSource, eqRatSource, bwand_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨hi, hd, hn⟩
      exact ⟨hi, by rw [hd, hn]⟩
    · rintro ⟨hi, hc⟩
      obtain ⟨hn, hd⟩ := canonical_fraction_components z.re x hz hx hdz hdx hc
      exact ⟨hi, hd, hn⟩
  exact ⟨eqspec, eqspec⟩

/-- The conjugate numerator and squared modulus satisfy the complex inverse identity. -/
def ComplexExactInverseValue : Prop :=
  (∀ (T : Type) (value : T → Int) (isinf : T → Bool)
    (zero conj : ComplexValue T → ComplexValue T) (abs2 : ComplexValue T → Int) (y : ComplexValue T),
    isinf y.re = false → isinf y.im = false →
    value (conj y).re = value y.re → value (conj y).im = -value y.im →
    abs2 y = value y.re * value y.re + value y.im * value y.im →
    let result := complexExactInvSource (fun z => (z.re,z.im)) isinf zero conj abs2 y
    value y.re * value result.1.re - value y.im * value result.1.im = result.2 ∧
      value y.re * value result.1.im + value y.im * value result.1.re = 0) ∧
  (∀ (t : IntTy) (y : ComplexValue (JInt t)) (result : ComplexValue (JInt t) × JInt t),
    complexExactInvIntegerSource (fun z => (z.re,z.im)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) checkedMul checkedAdd checkedNeg ComplexValue.mk y = .ok result →
    y.re.val * result.1.re.val - y.im.val * result.1.im.val = result.2.val ∧
      y.re.val * result.1.im.val + y.im.val * result.1.re.val = 0)

theorem complexExactInverseValue_proven : ComplexExactInverseValue := by
  constructor
  · intro T value isinf zero conj abs2 y hcr hci hre him habs
    simp [complexExactInvSource, bwor, hcr, hci, hre, him, habs, Int.mul_comm, Int.mul_neg]
    omega
  · intro t y result h
    unfold complexExactInvIntegerSource at h
    cases hg : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) y.re y.im with
    | error e => simp [← Int.natCast_ediv, hg, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨cr,dr⟩
      simp only [hg, Bind.bind, Except.bind] at h
      cases hc : checkedMul y.re cr with
      | error e => simp [hc, Bind.bind, Except.bind] at h
      | ok c2 =>
        simp only [hc, Bind.bind, Except.bind] at h
        cases hd : checkedMul y.im dr with
        | error e => simp [hd, Bind.bind, Except.bind] at h
        | ok d2 =>
          simp only [hd, Bind.bind, Except.bind] at h
          cases ha : checkedAdd c2 d2 with
          | error e => simp [ha, Bind.bind, Except.bind] at h
          | ok den =>
            simp only [ha, Bind.bind, Except.bind] at h
            cases hn : checkedNeg dr with
            | error e => simp [hn, Bind.bind, Except.bind] at h
            | ok ndr =>
              have hr : (ComplexValue.mk cr ndr, den) = result := by
                simpa [hn, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
              subst hr
              have vc := checkedMul_ok_val hc
              have vd := checkedMul_ok_val hd
              have va := checkedAdd_ok_val ha
              have vn := checkedNeg_ok_val hn
              have cross := (divgcdFactors y.re y.im cr dr hg).2.2.2
              dsimp only
              rw [va, vc, vd, vn]
              constructor
              · simp [Int.mul_comm, Int.mul_neg]
              · rw [Int.mul_neg, Int.mul_comm y.im.val cr.val, cross]
                omega


/-- Rounded rational quotients agree with rounding the unreduced exact cross-products.
    Integer division's external numerical contract is invariant under a positive common scale. -/
def RoundedRationalQuotients : Prop :=
  ∀ (t target : IntTy) (x y : Rat t) (k : JInt t) (q : JInt target) (mode : Rounding)
    (roundInteger : Int → Int → Rounding → Int)
    (divide : JInt t → JInt t → Rounding → Jl (JInt target)),
    (∀ a b m z, divide a b m = .ok z → z.val = roundInteger a.val b.val m) →
    (∀ a b scale m, 0 < scale → roundInteger (a * scale) (b * scale) m = roundInteger a b m) →
    (divRationalIntegerRoundedSource (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) checkedMul divide x k mode = .ok q →
      q.val = roundInteger x.num.val (x.den.val * k.val) mode) ∧
    (divIntegerRationalRoundedSource (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) checkedMul divide k y mode = .ok q →
      q.val = roundInteger (k.val * y.den.val) y.num.val mode) ∧
    (divRationalRationalRoundedSource (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) checkedMul checkedMul divide x y mode = .ok q →
      q.val = roundInteger (x.num.val * y.den.val) (x.den.val * y.num.val) mode)

theorem roundedRationalQuotients_proven : RoundedRationalQuotients := by
  intro t target x y k q mode roundInteger divide hdiv hscale
  refine ⟨?_, ?_, ?_⟩
  · intro h
    unfold divRationalIntegerRoundedSource at h
    cases hg : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num k with
    | error e => simp [← Int.natCast_ediv, hg, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨a,b⟩
      simp only [hg, Bind.bind, Except.bind] at h
      cases hm : checkedMul x.den b with
      | error e => simp [hm, Bind.bind, Except.bind] at h
      | ok den =>
        simp only [hm, Bind.bind, Except.bind] at h
        have vm := checkedMul_ok_val hm
        obtain ⟨hgpos, ha, hb, _⟩ := divgcdFactors x.num k a b hg
        let g : Int := Nat.gcd x.num.val.natAbs k.val.natAbs
        calc
          q.val = roundInteger a.val (x.den.val * b.val) mode := by simpa only [vm] using hdiv _ _ _ _ h
          _ = roundInteger (a.val * g) ((x.den.val * b.val) * g) mode := (hscale _ _ g mode hgpos).symm
          _ = roundInteger x.num.val (x.den.val * k.val) mode := by rw [ha, Int.mul_assoc, hb]
  · intro h
    unfold divIntegerRationalRoundedSource at h
    cases hg : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) k y.num with
    | error e => simp [← Int.natCast_ediv, hg, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨a,b⟩
      simp only [hg, Bind.bind, Except.bind] at h
      cases hm : checkedMul a y.den with
      | error e => simp [hm, Bind.bind, Except.bind] at h
      | ok num =>
        simp only [hm, Bind.bind, Except.bind] at h
        have vm := checkedMul_ok_val hm
        obtain ⟨hgpos, ha, hb, _⟩ := divgcdFactors k y.num a b hg
        let g : Int := Nat.gcd k.val.natAbs y.num.val.natAbs
        calc
          q.val = roundInteger (a.val * y.den.val) b.val mode := by simpa only [vm] using hdiv _ _ _ _ h
          _ = roundInteger ((a.val * y.den.val) * g) (b.val * g) mode := (hscale _ _ g mode hgpos).symm
          _ = roundInteger (k.val * y.den.val) y.num.val mode := by rw [Int.mul_right_comm, ha, hb]
  · intro h
    unfold divRationalRationalRoundedSource at h
    cases hn : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.num y.num with
    | error e => simp [← Int.natCast_ediv, hn, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨a,b⟩
      simp only [hn, Bind.bind, Except.bind] at h
      cases hd : (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) x.den y.den with
      | error e => simp [← Int.natCast_ediv, hd, Bind.bind, Except.bind] at h
      | ok pair =>
        rcases pair with ⟨c,d⟩
        simp only [hd, Bind.bind, Except.bind] at h
        cases hmn : checkedMul a d with
        | error e => simp [hmn, Bind.bind, Except.bind] at h
        | ok num =>
          simp only [hmn, Bind.bind, Except.bind] at h
          cases hmd : checkedMul c b with
          | error e => simp [hmd, Bind.bind, Except.bind] at h
          | ok den =>
            simp only [hmd, Bind.bind, Except.bind] at h
            have vmn := checkedMul_ok_val hmn
            have vmd := checkedMul_ok_val hmd
            obtain ⟨hgn, ha, hb, _⟩ := divgcdFactors x.num y.num a b hn
            obtain ⟨hgd, hc, hdv, _⟩ := divgcdFactors x.den y.den c d hd
            let gn : Int := Nat.gcd x.num.val.natAbs y.num.val.natAbs
            let gd : Int := Nat.gcd x.den.val.natAbs y.den.val.natAbs
            have hnum : (a.val * d.val) * (gn * gd) = x.num.val * y.den.val := by
              calc
                _ = (a.val * gn) * (d.val * gd) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                _ = _ := by rw [ha, hdv]
            have hden : (c.val * b.val) * (gn * gd) = x.den.val * y.num.val := by
              calc
                _ = (c.val * gd) * (b.val * gn) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                _ = _ := by rw [hc, hb]
            calc
              q.val = roundInteger (a.val * d.val) (c.val * b.val) mode := by simpa only [vmn, vmd] using hdiv _ _ _ _ h
              _ = roundInteger ((a.val * d.val) * (gn * gd)) ((c.val * b.val) * (gn * gd)) mode :=
                (hscale _ _ (gn * gd) mode (Int.mul_pos hgn hgd)).symm
              _ = _ := by rw [hnum, hden]


/-- Complex rational numerators use the least common positive denominator. -/
def ComplexRationalNumeratorValue : Prop :=
  ∀ (t : IntTy) (z : ComplexValue (Rat t)) (result : ComplexValue (JInt t))
    (lcm divide : JInt t → JInt t → Jl (JInt t)),
    (∀ a b l, lcm a b = .ok l →
      l.val = (Nat.lcm a.val.natAbs b.val.natAbs : Int) ∧ a.val ∣ l.val ∧ b.val ∣ l.val) →
    (∀ a b q, b.val ∣ a.val → divide a b = .ok q → q.val * b.val = a.val) →
    numeratorComplexSource ComplexValue.re ComplexValue.im lcm divide checkedMul ComplexValue.mk z = .ok result →
    result.re.val * z.re.den.val = z.re.num.val * (Nat.lcm z.re.den.val.natAbs z.im.den.val.natAbs : Int) ∧
    result.im.val * z.im.den.val = z.im.num.val * (Nat.lcm z.re.den.val.natAbs z.im.den.val.natAbs : Int)

theorem complexRationalNumeratorValue_proven : ComplexRationalNumeratorValue := by
  intro t z result lcm divide hlcm hdiv h
  unfold numeratorComplexSource at h
  simp only [denominatorRationalSource, numeratorRationalSource, Bind.bind, Except.bind] at h
  cases hl : lcm z.re.den z.im.den with
  | error e => simp [hl] at h
  | ok den =>
    obtain ⟨hden, hrdiv, hidiv⟩ := hlcm _ _ _ hl
    simp only [hl] at h
    cases hqr : divide den z.re.den with
    | error e => simp [hqr] at h
    | ok qr =>
      simp only [hqr] at h
      cases hnr : checkedMul z.re.num qr with
      | error e => simp [hnr] at h
      | ok nr =>
        simp only [hnr] at h
        cases hqi : divide den z.im.den with
        | error e => simp [hqi] at h
        | ok qi =>
          simp only [hqi] at h
          cases hni : checkedMul z.im.num qi with
          | error e => simp [hni] at h
          | ok ni =>
            have he : ComplexValue.mk nr ni = result := by simpa [hni, Pure.pure, Except.pure] using h
            subst he
            have vr := checkedMul_ok_val hnr
            have vi := checkedMul_ok_val hni
            have vqr := hdiv _ _ _ hrdiv hqr
            have vqi := hdiv _ _ _ hidiv hqi
            dsimp only
            rw [vr, vi, Int.mul_assoc, Int.mul_assoc, vqr, vqi, hden]
            exact ⟨rfl, rfl⟩

/-- Powers in Gaussian homogeneous coordinates, used only as the mathematical specification. -/
def gaussianPower (re im : Int) : Nat → Int × Int
  | 0 => (1,0)
  | n + 1 =>
    let (a,b) := gaussianPower re im n
    (re * a - im * b, re * b + im * a)

def ComplexPowerRatio {t : IntTy} (z : ComplexValue (Rat t)) (n : Nat)
    (q : ComplexValue (Rat t)) : Prop :=
  let re := z.re.num.val * z.im.den.val
  let im := z.im.num.val * z.re.den.val
  let den := z.re.den.val * z.im.den.val
  q.re.num.val * den ^ n = (gaussianPower re im n).1 * q.re.den.val ∧
    q.im.num.val * den ^ n = (gaussianPower re im n).2 * q.im.den.val

/-- Complex integer exponentiation preserves the Gaussian power value, using the
    external power_by_squaring method's numerical contract for nonnegative exponents. -/
def ComplexIntegerPowerValue : Prop :=
  ∀ (t : IntTy) (N : Type) (value : N → Int) (geZero : N → Bool) (neg : N → N)
    (inverse : ComplexValue (Rat t) → Jl (ComplexValue (Rat t)))
    (power : ComplexValue (Rat t) → N → Jl (ComplexValue (Rat t)))
    (z q : ComplexValue (Rat t)) (n : N),
    (∀ m, geZero m = decide (0 ≤ value m)) →
    (value n < 0 → value (neg n) = -value n) →
    (∀ w m r, 0 ≤ value m → power w m = .ok r → ComplexPowerRatio w (value m).toNat r) →
    (0 ≤ value n → powComplexRationalIntegerGeneric geZero neg inverse power z n = .ok q →
      ComplexPowerRatio z (value n).toNat q) ∧
    (value n < 0 → powComplexRationalIntegerGeneric geZero neg inverse power z n = .ok q →
      ∃ inverseZ, inverse z = .ok inverseZ ∧ ComplexPowerRatio inverseZ (value n).natAbs q)

theorem complexIntegerPowerValue_proven : ComplexIntegerPowerValue := by
  intro t N value geZero neg inverse power z q n hge hneg hpower
  constructor
  · intro hn h
    simp [powComplexRationalIntegerGeneric, hge, hn] at h
    exact hpower z n q hn h
  · intro hn h
    simp only [powComplexRationalIntegerGeneric, hge, decide_eq_true_eq] at h
    rw [if_neg (by omega)] at h
    cases hi : inverse z with
    | error e => simp [hi, Bind.bind, Except.bind] at h
    | ok inverseZ =>
      simp only [hi, Bind.bind, Except.bind] at h
      have hnonneg : 0 ≤ value (neg n) := by rw [hneg hn]; omega
      have hval := hpower inverseZ (neg n) q hnonneg h
      have hnabs : (-value n).toNat = (value n).natAbs := by
        have h1 := Int.toNat_of_nonneg (by omega : 0 ≤ -value n)
        have h2 := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hn)
        omega
      rw [hneg hn, hnabs] at hval
      exact ⟨inverseZ, rfl, hval⟩


/-- A successful rational-input approximation must obey its requested tolerance. -/
def RationalInputApproximationTolerance : Prop :=
  ∀ (s target : IntTy) (x : Rat s) (tol : JuliaLean.base.float.FV .f64) (q : Rat target) (showTol : JuliaLean.base.float.FV .f64 → String),
    Normalized x → 0 < x.den.val → JuliaLean.base.float.isfinite_IEEEFloat tol = true →
    0 ≤ (Fl.toRat tol).1 →
    rationalizeRatToleranceSource (fun _ => true) id
      (fun tol threshold => JuliaLean.base.float.le_IEEEFloat threshold tol)
      JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.float.eps_IEEEFloat
      (fun eps => JuliaLean.base.float.div_IEEEFloat eps (Fl.ofInt 2)) target x tol showTol = some (.ok q) →
    0 < q.den.val ∧
      (x.num.val * q.den.val - q.num.val * x.den.val).natAbs * (Fl.toRat tol).2 ≤
        (Fl.toRat tol).1.natAbs * x.den.val.natAbs * q.den.val.natAbs

set_option maxRecDepth 10000 in
theorem rationalInputApproximationTolerance_refuted : ¬ RationalInputApproximationTolerance := by
  intro h
  let showTol : JuliaLean.base.float.FV .f64 → String := reprStr
  let x : Rat .i16 := ⟨JInt.lit .i16 128, JInt.lit .i16 1⟩
  let tol : JuliaLean.base.float.FV .f64 := JuliaLean.base.float.div_IEEEFloat (JuliaLean.base.float.eps_IEEEFloat (Fl.ofInt 128)) (Fl.ofInt 2)
  let q : Rat .i8 := ⟨JInt.lit .i8 127, JInt.lit .i8 1⟩
  have actual : rationalizeRatToleranceSource (fun _ => true) id
      (fun tol threshold => JuliaLean.base.float.le_IEEEFloat threshold tol)
      JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.float.eps_IEEEFloat
      (fun eps => JuliaLean.base.float.div_IEEEFloat eps (Fl.ofInt 2)) .i8 x tol showTol = some (.ok q) := by
    dsimp [x, tol, IntTy.signed, IntTy.min, IntTy.max, rationalizeRatToleranceSource, rationalizeRatToleranceGeneric, rationalizeF64,
      rationalizeAbstractFloatSource, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure]
    apply genericRationalizeSteps_sound (fuel := 100)
    decide +kernel
  have bad := h .i16 .i8 x tol q showTol (by unfold Normalized x; decide) (by decide) (by decide) (by decide) actual
  have impossible : ¬ (0 < q.den.val ∧
      (x.num.val * q.den.val - q.num.val * x.den.val).natAbs * (Fl.toRat tol).2 ≤
        (Fl.toRat tol).1.natAbs * x.den.val.natAbs * q.den.val.natAbs) := by decide +kernel
  exact impossible bad

/-- Complex rational arithmetic, I/O, rounding, hash and range contracts. -/
def RationalComplexAndIoExact : Prop :=
  ComplexExactInverseValue ∧ ComplexIntegerQuotientValues ∧ RationalIoContracts ∧
    ComplexRationalNumeratorValue ∧ ComplexRationalEqualityValue ∧ RoundedRationalQuotients ∧
    ComplexIntegerPowerValue ∧ RationalHalfIntegerHash ∧ RationalUnitRangeLength

theorem rationalComplexAndIoExact_proven : RationalComplexAndIoExact :=
  ⟨complexExactInverseValue_proven, complexIntegerQuotientValues_proven, rationalIoContracts_proven,
    complexRationalNumeratorValue_proven, complexRationalEqualityValue_proven, roundedRationalQuotients_proven,
    complexIntegerPowerValue_proven, rationalHalfIntegerHash_proven, rationalUnitRangeLength_proven⟩

/-! Nothing to promise:
- `unsafe_rational(num::T, den::T) where {T<:Integer}@17`: pure forwarding to `unsafe_rational(T, num, den)`.
- `checked_den(num::T, den::T) where {T<:Integer}@27`: pure forwarding to `checked_den(T, num, den)`.
- `checked_den(num::Integer, den::Integer)@28`: pure forwarding through `promote(num, den)` to `checked_den`.
- `Rational(n::T, d::T) where {T<:Integer}@48`: pure forwarding to `Rational{T}(n, d)`.
- `Rational(n::Integer, d::Integer)@49`: pure forwarding through `promote(n, d)` to `Rational`.
- `//(n::Integer, d::Integer)@91`: pure forwarding to `Rational(n, d)` (also covered by `rational-zero-over-zero-rejected` and `rational-constructor-normalized-positive`).
- `//(x::Complex, y::Real)@116`: pure componentwise forwarding `complex(real(x)//y, imag(x)//y)`.
- `//(x::Number, y::Complex)@137`: pure forwarding through `_complex_exact_inv(y)` to `(x * num) // den`.
- `//(x::Integer, y::Complex{<:Integer})@141`: pure forwarding `complex(x) // y`.
- `//(X::AbstractArray, y::Number)@154`: pure broadcasting forwarding `X .// y`.
- `write(s::IO, z::Rational)@172`: pure forwarding `write(s, numerator(z), denominator(z))`.
- `Rational(x::Rational)@197`: identity constructor returning `x` unchanged.
- `Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}})@211`: pure two-step conversion wrapper `Float16(Float32(x))`.
- `Float16(x::Rational{<:Union{Int128,UInt128}})@213`: pure two-step conversion wrapper `Float16(Float64(x))`.
- `Float32(x::Rational{<:Union{Int128,UInt128}})@215`: pure two-step conversion wrapper `Float32(Float64(x))`.
- `Rational(x::Float64)@223`: pure forwarding to `Rational{Int64}(x)`.
- `Rational(x::Float32)@224`: pure forwarding to `Rational{Int}(x)`.
- `big(q::Rational)@226`: pure componentwise forwarding `unsafe_rational(big(numerator(q)), big(denominator(q)))`.
- `big(z::Complex{<:Rational{<:Integer}})@228`: pure constructor forwarding `Complex{Rational{BigInt}}(z)`.
- `promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer}@230`: type-level promotion plumbing `Rational{promote_type(T,S)}`.
- `promote_rule(::Type{Rational{T}}, ::Type{Rational{S}}) where {T<:Integer,S<:Integer}@231`: type-level promotion plumbing `Rational{promote_type(T,S)}`.
- `promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat}@232`: type-level promotion plumbing `promote_type(T,S)`.
- `widen(::Type{Rational{T}})@234`: type-level widening plumbing `Rational{widen(T)}`.
- `__throw_negate_unsigned()@236`: internal `@noinline` exception constructor; its `OverflowError` contract is stated on its callers by `intarith-rational-infinity-sub`, `rational-unary-predicates-exact`, and `rational-complex-and-io-exact`.
- `rationalize(::Type{T}, x::AbstractFloat; tol::Real = eps(x))@320`: pure default-keyword forwarding to `rationalize(T, x, tol)`.
- `rationalize(x::Real; kvs...)@321`: pure default-type forwarding to `rationalize(Int, x; kvs...)`.
- `rationalize(::Type{T}, x::Complex; kvs...)@322`: pure componentwise forwarding `Complex(rationalize(T, x.re; kvs...), rationalize(T, x.im; kvs...))`.
- `rationalize(x::Complex; kvs...)@323`: pure componentwise forwarding `Complex(rationalize(Int, x.re; kvs...), rationalize(Int, x.im; kvs...))`.
- `rationalize(::Type{T}, x::Rational; tol::Real = eps(float(x)))@324`: pure default-keyword forwarding to `rationalize(T, x, tol)`.
- `rationalize(x::Rational{T}; kvs...)@325`: pure default-type forwarding to `rationalize(T, x; kvs...)`.
- `rationalize(x::Integer; kvs...)@334`: pure forwarding to `Rational(x)` (also covered by `numberscov-rationalize-integer-tolerance`).
- `rationalize(::Type{Union{}}, slurp...; kwargs...)@343`: bottom-type dispatch guard that immediately throws `MethodError`.
- `numerator(x::Union{Integer,Complex{<:Integer}})@360`: identity selector returning `x` unchanged.
- `denominator(x::Union{Integer,Complex{<:Integer}})@383`: pure forwarding to `one(x)`.
- `denominator(z::Complex{<:Rational})@385`: pure forwarding `lcm(denominator(real(z)), denominator(imag(z)))`.
- `__throw_rational_numerator_typemin(T)@406`: internal `@noinline` exception constructor; its `OverflowError` contract is stated on `-(::Rational{<:BitSigned})` by `rational-unary-predicates-exact`.
- `*(y::Rational, x::Bool)@500`: pure commutative forwarding `x * y`.
- `/(x::Rational, y::Union{Rational, Integer})@501`: pure alias forwarding `x // y`.
- `/(x::Integer, y::Rational)@502`: pure alias forwarding `x // y`.
- `fma(x::Rational, y::Rational, z::Rational)@505`: pure forwarding `x * y + z`.
- `==(x::Integer, y::Rational)@515`: pure symmetric forwarding `y == x` (also covered by `rational-integer-comparison-exact`).
- `==(q::Rational, x::AbstractFloat)@529`: pure symmetric forwarding `x == q` (also covered by `rational-gcd-lcm-gcdx-exact`).
- `div(x::T, y::T, r::RoundingMode) where {T<:Rational}@602`: compatibility `invoke` forwarding to `div(::Rational, ::Rational, ::RoundingMode)`.
- `div(x::Rational, y::Integer)@606`: pure default-rounding forwarding to `div(x, y, RoundToZero)`.
- `div(x::Integer, y::Rational)@606`: pure default-rounding forwarding to `div(x, y, RoundToZero)`.
- `div(x::Rational, y::Rational)@606`: pure default-rounding forwarding to `div(x, y, RoundToZero)`.
- `fld(x::Rational, y::Integer)@607`: pure default-rounding forwarding to `div(x, y, RoundDown)`.
- `fld(x::Integer, y::Rational)@607`: pure default-rounding forwarding to `div(x, y, RoundDown)`.
- `fld(x::Rational, y::Rational)@607`: pure default-rounding forwarding to `div(x, y, RoundDown)`.
- `cld(x::Rational, y::Integer)@608`: pure default-rounding forwarding to `div(x, y, RoundUp)`.
- `cld(x::Integer, y::Rational)@608`: pure default-rounding forwarding to `div(x, y, RoundUp)`.
- `cld(x::Rational, y::Rational)@608`: pure default-rounding forwarding to `div(x, y, RoundUp)`.
- `round(x::Rational, r::RoundingMode=RoundNearest)@612`: pure default-type forwarding `round(typeof(x), x, r)`.
- `^(x::Number, y::Rational)@632`: pure forwarding `x ^ (y.num / y.den)`.
- `^(x::T, y::Rational) where {T<:AbstractFloat}@633`: pure forwarding `x ^ convert(T, y)`.
- `^(z::Complex{T}, p::Rational) where {T<:Real}@634`: pure forwarding `z ^ convert(typeof(one(T)^p), p)`.
- `lerpi(j::Integer, d::Integer, a::Rational, b::Rational)@644`: pure linear interpolation formula `((d - j) * a) / d + (j * b) / d`.
- `float(::Type{Rational{T}}) where {T<:Integer}@648`: type-level forwarding `float(T)`.
-/

/-!
## Method-to-property table

| Method (`base/rational.jl`) | Model (`JuliaLean.base.rational`) | Coverage |
| --- | --- | --- |
| `unsafe_rational(::Type{T}, num, den)@14` | `unsafeRationalTypeSource` | `rational-components-roundtrip` |
| `unsafe_rational(num::T, den::T)@17` | `unsafeRationalSameSource` | Nothing to promise (forwards to `unsafe_rational(T, num, den)`) |
| `unsafe_rational(num::Integer, den::Integer)@18` | `unsafeRationalPromoteSource` | `rational-promotion-and-zero-error` |
| `checked_den(::Type{T}, num::T, den::T)@20` | `checkedDenTypeSource` | `rational-checked-den-positive`, `rational-inverse-zero-infinity` |
| `checked_den(num::T, den::T)@27` | `checkedDenSameSource` | Nothing to promise (forwards to `checked_den(T, num, den)`) |
| `checked_den(num::Integer, den::Integer)@28` | `checkedDenPromoteSource` | Nothing to promise (forwards `promote(num, den)` to `checked_den`) |
| `__throw_rational_argerror_zero(T)@30` | `throwRationalZeroSource` | `rational-promotion-and-zero-error` |
| `Rational{T}(num::Integer, den::Integer)@31` | `constructSource` | `intarith-rational-normalize-before-convert`, `rational-zero-over-zero-rejected`, `rational-constructor-normalized-positive` |
| `Rational(n::T, d::T)@48` | `rationalSameSource` | Nothing to promise (forwards to `Rational{T}(n, d)`) |
| `Rational(n::Integer, d::Integer)@49` | `rationalPromoteSource` | Nothing to promise (forwards `promote(n, d)` to `Rational`) |
| `Rational(n::Integer)@50` | `rationalFromIntegerGeneric` | `rational-unary-predicates-exact`, `numberscov-rationalize-integer-tolerance` |
| `divgcd(x::TX, y::TY)@59` | `divgcdSource` | `rational-divgcd-coprime` |
| `//(n::Integer, d::Integer)@91` | `exactDivideIntsSource` | `rational-zero-over-zero-rejected`, `rational-constructor-normalized-positive` |
| `//(x::Rational, y::Integer)@93` | `divRatIntSource` | `rational-arithmetic-exact` |
| `//(x::Integer, y::Rational)@102` | `divIntRatSource` | `rational-arithmetic-exact` |
| `//(x::Rational, y::Rational)@106` | `divRatRatSource` | `rational-arithmetic-exact` |
| `//(x::Complex, y::Real)@116` | `exactDivideComplexReal` | Nothing to promise (forwards real and imaginary parts to `//`) |
| `_complex_exact_inv(y::Complex)@120` | `complexExactInvSource` | `rational-complex-and-io-exact` |
| `_complex_exact_inv(y::Complex{<:Integer})@129` | `complexExactInvIntegerSource` | `rational-complex-and-io-exact` |
| `//(x::Number, y::Complex)@137` | `divideNumberComplexSource` | Nothing to promise (forwards `_complex_exact_inv(y)` to `*` and `//`) |
| `//(x::Integer, y::Complex{<:Integer})@141` | `divideIntegerComplexSource` | Nothing to promise (forwards `complex(x)` to `//`) |
| `//(x::Complex{<:Integer}, y::Complex{<:Integer})@144` | `divideComplexIntegersSource` | `rational-complex-and-io-exact` |
| `//(X::AbstractArray, y::Number)@154` | `divideArraySource` | Nothing to promise (forwards to `.//`) |
| `show(io::IO, x::Rational)@156` | `showRationalSource` | `rational-complex-and-io-exact` |
| `read(s::IO, ::Type{Rational{T}})@167` | `readRationalSource` | `rational-complex-and-io-exact` |
| `write(s::IO, z::Rational)@172` | `writeRationalSource` | Nothing to promise (forwards `numerator(z)` and `denominator(z)` to `write`) |
| `parse(::Type{Rational{T}}, s::AbstractString)@175` | `parseRationalSource` | `rational-complex-and-io-exact` |
| `Rational{T}(x::Rational)@190` | `convertRatSource` | `rational-unary-predicates-exact` |
| `Rational{T}(x::Integer)@193` | `rationalIntAsSource` | `rational-unary-predicates-exact` |
| `Rational(x::Rational)@197` | `rationalIdentitySource` | Nothing to promise (identity constructor) |
| `Bool(x::Rational)@199` | `boolOfRatSource` | `rational-unary-predicates-exact` |
| `(::Type{T})(x::Rational) where {T<:Integer}@201` | `intOfRatSource` | `rational-unary-predicates-exact` |
| `AbstractFloat(x::Rational)@204` | `abstractFloatRatSource` | `promotion-float-from-rational-nearest`, `rational-float-conversion-roundtrip` |
| `(::Type{T})(x::Rational{S}) where T<:AbstractFloat@205` | `floatConvertRatSource` | `promotion-float-from-rational-nearest` |
| `Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}})@211` | `float16OfRationalSmallSource` | Nothing to promise (forwards `Float32(x)` to `Float16`) |
| `Float16(x::Rational{<:Union{Int128,UInt128}})@213` | `float16OfRational128Source` | Nothing to promise (forwards `Float64(x)` to `Float16`) |
| `Float32(x::Rational{<:Union{Int128,UInt128}})@215` | `float32OfRational128Source` | Nothing to promise (forwards `Float64(x)` to `Float32`) |
| `Rational{T}(x::AbstractFloat)@218` | `rationalOfFloatSource` | `promotion-rational-from-float-exact`, `promotion-rational-from-float-representable`, `rational-float-conversion-roundtrip` |
| `Rational(x::Float64)@223` | `rationalFloat64Source` | Nothing to promise (forwards to `Rational{Int64}(x)`) |
| `Rational(x::Float32)@224` | `rationalFloat32Source` | Nothing to promise (forwards to `Rational{Int}(x)`) |
| `big(q::Rational)@226` | `bigRationalSource` | Nothing to promise (forwards `big(numerator(q))` and `big(denominator(q))` to `unsafe_rational`) |
| `big(z::Complex{<:Rational{<:Integer}})@228` | `bigComplexRationalSource` | Nothing to promise (forwards to `Complex{Rational{BigInt}}`) |
| `promote_rule(::Type{Rational{T}}, ::Type{S})@230` | `promoteRuleRatIntSource` | Nothing to promise (type-level promotion rule) |
| `promote_rule(::Type{Rational{T}}, ::Type{Rational{S}})@231` | `promoteRuleRatRatSource` | Nothing to promise (type-level promotion rule) |
| `promote_rule(::Type{Rational{T}}, ::Type{S<:AbstractFloat})@232` | `promoteRuleRatFloatSource` | Nothing to promise (type-level promotion rule) |
| `widen(::Type{Rational{T}})@234` | `widenRatTypeSource` | Nothing to promise (type-level widening rule) |
| `__throw_negate_unsigned()@236` | `throwNegateUnsignedSource` | Nothing to promise (internal exception constructor) |
| `rationalize(::Type{T}, x::AbstractFloat, tol::Real)@256` | `rationalizeAbstractFloatSource` | `promotion-rational-from-float-representable`, `rational-float-conversion-roundtrip` |
| `rationalize(::Type{T}, x::AbstractFloat; tol=eps(x))@320` | `rationalizeFloatDefaultSource` | Nothing to promise (supplies default `tol = eps(x)`) |
| `rationalize(x::Real; kvs...)@321` | `rationalizeRealSourceMethod` | Nothing to promise (forwards `Int` to `rationalize`) |
| `rationalize(::Type{T}, x::Complex; kvs...)@322` | `rationalizeComplexTypedSource` | Nothing to promise (maps `rationalize(T, ...)` over `re` and `im`) |
| `rationalize(x::Complex; kvs...)@323` | `rationalizeComplexDefaultSource` | Nothing to promise (maps `rationalize(Int, ...)` over `re` and `im`) |
| `rationalize(::Type{T}, x::Rational; tol=eps(float(x)))@324` | `rationalizeRatTypedDefaultSource` | Nothing to promise (supplies default `tol = eps(float(x))`) |
| `rationalize(x::Rational{T}; kvs...)@325` | `rationalizeRatSource` | Nothing to promise (forwards `T` to `rationalize`) |
| `rationalize(::Type{T}, x::Rational, tol::Real)@326` | `rationalizeRatToleranceGeneric` | `rational-input-approximation-tolerance` |
| `rationalize(x::Integer; kvs...)@334` | `rationalizeIntegerGeneric` | `rational-integer-rationalize-range` |
| `rationalize(::Type{T}, x::Integer; kvs...)@335` | `rationalizeIntegerTypedSource` | `rational-integer-rationalize-range` |
| `rationalize(::Type{Union{}}, slurp...; kwargs...)@343` | `rationalizeUnionBottomSource` | Nothing to promise (bottom-type `MethodError` guard) |
| `numerator(x::Union{Integer,Complex{<:Integer}})@360` | `numeratorIntegerOrComplex` | Nothing to promise (identity selector) |
| `numerator(x::Rational)@361` | `numeratorRationalSource` | `rational-components-roundtrip` |
| `numerator(z::Complex{<:Rational})@362` | `numeratorComplexSource` | `rational-complex-and-io-exact` |
| `denominator(x::Union{Integer,Complex{<:Integer}})@383` | `denominatorIntegerOrComplex` | Nothing to promise (forwards to `one(x)`) |
| `denominator(x::Rational)@384` | `denominatorRationalSource` | `rational-components-roundtrip` |
| `denominator(z::Complex{<:Rational})@385` | `denominatorComplexSource` | Nothing to promise (forwards to `lcm(denominator(real(z)), denominator(imag(z)))`) |
| `sign(x::Rational)@387` | `signRatSource` | `rational-unary-predicates-exact` |
| `signbit(x::Rational)@388` | `signbitRatSource` | `rational-unary-predicates-exact` |
| `abs(x::Rational)@390` | `absRatSource` | `rational-unary-predicates-exact` |
| `typemin(::Type{Rational{T<:Signed}})@392` | `typeminSignedRatSource` | `rational-unary-predicates-exact` |
| `typemin(::Type{Rational{T<:Integer}})@393` | `typeminOtherRatSource` | `rational-unary-predicates-exact` |
| `typemax(::Type{Rational{T<:Integer}})@394` | `typemaxRatSource` | `rational-unary-predicates-exact` |
| `isinteger(x::Rational)@396` | `isIntegerRatSource` | `rational-unary-predicates-exact` |
| `ispow2(x::Rational)@397` | `isPow2RatSource` | `rational-unary-predicates-exact` |
| `+(x::Rational)@399` | `unaryPlusRatSource` | `rational-unary-predicates-exact` |
| `-(x::Rational)@400` | `negRatSource` | `rational-unary-predicates-exact` |
| `-(x::Rational{T<:BitSigned})@402` | `negBitSignedSource` | `rational-unary-predicates-exact` |
| `__throw_rational_numerator_typemin(T)@406` | `throwNumeratorTypeminSource` | Nothing to promise (internal exception constructor) |
| `-(x::Rational{T<:Unsigned})@408` | `negUnsignedSource` | `intarith-rational-infinity-sub`, `rational-unary-predicates-exact` |
| `-%(x::Rational)@413` | `negWrapRatSource` | `rational-unary-predicates-exact` |
| `+(x::Rational, y::Rational)@415` | `addRatSource` | `rational-arithmetic-exact` |
| `+%(x::Rational, y::Rational)@424` | `addWrapRatSource` | `rational-wrapping-and-remainder-exact` |
| `-(x::Rational, y::Rational)@433` | `subRatSource` | `intarith-rational-infinity-sub`, `rational-arithmetic-exact` |
| `-%(x::Rational, y::Rational)@442` | `subWrapRatSource` | `rational-wrapping-and-remainder-exact` |
| `rem(x::Rational, y::Rational)@453` | `remRatSource`, `modRatSource` | `rational-wrapping-and-remainder-exact` |
| `mod(x::Rational, y::Rational)@453` | `remRatSource`, `modRatSource` | `rational-wrapping-and-remainder-exact` |
| `+(x::Rational, y::Integer)@462` | `rationalIntegerOpSource` | `rational-arithmetic-exact` |
| `-(x::Rational, y::Integer)@462` | `rationalIntegerOpSource` | `rational-arithmetic-exact` |
| `rem(x::Rational, y::Integer)@462` | `rationalIntegerOpSource` | `rational-wrapping-and-remainder-exact` |
| `mod(x::Rational, y::Integer)@462` | `rationalIntegerOpSource` | `rational-wrapping-and-remainder-exact` |
| `+(y::Integer, x::Rational)@469` | `integerRationalOpSource` | `rational-arithmetic-exact` |
| `-(y::Integer, x::Rational)@469` | `integerRationalOpSource` | `rational-arithmetic-exact` |
| `rem(y::Integer, x::Rational)@476` | `integerRationalRemainderSource` | `rational-wrapping-and-remainder-exact` |
| `mod(y::Integer, x::Rational)@476` | `integerRationalRemainderSource` | `rational-wrapping-and-remainder-exact` |
| `*(x::Rational, y::Rational)@482` | `mulRatRatSource` | `rational-arithmetic-exact` |
| `*(x::Rational, y::Integer)@487` | `mulRatIntSource` | `rational-arithmetic-exact` |
| `*(y::Integer, x::Rational)@491` | `mulIntRatSource` | `rational-arithmetic-exact` |
| `*(x::Bool, y::Rational)@497` | `boolMulRatSource` | `rational-unary-predicates-exact` |
| `*(y::Rational, x::Bool)@500` | `mulRatBoolSource` | Nothing to promise (forwards `x * y`) |
| `/(x::Rational, y::Union{Rational, Integer})@501` | `slashRationalUnionSource` | Nothing to promise (forwards `x // y`) |
| `/(x::Integer, y::Rational)@502` | `slashIntegerRationalSource` | Nothing to promise (forwards `x // y`) |
| `inv(x::Rational{T})@503` | `invRatSource` | `rational-inverse-zero-infinity` |
| `fma(x::Rational, y::Rational, z::Rational)@505` | `fmaRatSource` | Nothing to promise (forwards `x * y + z`) |
| `==(x::Rational, y::Rational)@507` | `eqRatSource` | `rational-rational-comparisons` |
| `<(x::Rational, y::Rational)@508` | `ltRatSource` | `rational-rational-comparisons` |
| `<=(x::Rational, y::Rational)@510` | `leRatSource` | `rational-rational-comparisons` |
| `==(x::Rational, y::Integer)@514` | `eqRatIntSource` | `rational-integer-comparison-exact` |
| `==(x::Integer, y::Rational)@515` | `eqIntRatSource` | `rational-integer-comparison-exact` |
| `<(x::Rational, y::Integer)@516` | `ltRatIntSource` | `rational-integer-comparison-exact` |
| `<(x::Integer, y::Rational)@517` | `ltIntRatSource` | `rational-integer-comparison-exact` |
| `<=(x::Rational, y::Integer)@518` | `leRatIntSource` | `rational-integer-comparison-exact` |
| `<=(x::Integer, y::Rational)@519` | `leIntRatSource` | `rational-integer-comparison-exact` |
| `==(x::AbstractFloat, q::Rational)@521` | `eqFloatRatSource` | `rational-gcd-lcm-gcdx-exact` |
| `==(q::Rational, x::AbstractFloat)@529` | `eqRatFloatSource` | `rational-gcd-lcm-gcdx-exact` |
| `<(x::Rational, y::AbstractFloat)@533` | `rationalFloatRelationSource` | `rational-float-comparison-exact` |
| `<(x::AbstractFloat, y::Rational)@533` | `rationalFloatRelationSource` | `rational-float-comparison-exact` |
| `<=(x::Rational, y::AbstractFloat)@533` | `rationalFloatRelationSource` | `rational-float-comparison-exact` |
| `<=(x::AbstractFloat, y::Rational)@533` | `rationalFloatRelationSource` | `rational-float-comparison-exact` |
| `cmp(x::Rational, y::AbstractFloat)@533` | `rationalFloatRelationSource` | `promotion-cmp-rational-signed-zero`, `rational-float-comparison-exact` |
| `cmp(x::AbstractFloat, y::Rational)@533` | `rationalFloatRelationSource` | `promotion-cmp-rational-signed-zero`, `rational-float-comparison-exact` |
| `==(z::Complex, x::Rational)@583` | `eqComplexRatSource` | `rational-complex-and-io-exact` |
| `==(x::Rational, z::Complex)@584` | `eqRatComplexSource` | `rational-complex-and-io-exact` |
| `div(x::Rational, y::Integer, r::RoundingMode)@586` | `divRationalIntegerRoundedSource` | `rational-complex-and-io-exact` |
| `div(x::Integer, y::Rational, r::RoundingMode)@590` | `divIntegerRationalRoundedSource` | `rational-complex-and-io-exact` |
| `div(x::Rational, y::Rational, r::RoundingMode)@594` | `divRationalRationalRoundedSource` | `rational-complex-and-io-exact` |
| `div(x::T, y::T, r::RoundingMode) where {T<:Rational}@602` | `divCompatibilitySource` | Nothing to promise (compatibility `invoke` forwarding) |
| `div(x::Rational, y::Integer)@606` | `divDefaultSource` | Nothing to promise (forwards `RoundToZero` to `div`) |
| `div(x::Integer, y::Rational)@606` | `divDefaultSource` | Nothing to promise (forwards `RoundToZero` to `div`) |
| `div(x::Rational, y::Rational)@606` | `divDefaultSource` | Nothing to promise (forwards `RoundToZero` to `div`) |
| `fld(x::Rational, y::Integer)@607` | `fldDefaultSource` | Nothing to promise (forwards `RoundDown` to `div`) |
| `fld(x::Integer, y::Rational)@607` | `fldDefaultSource` | Nothing to promise (forwards `RoundDown` to `div`) |
| `fld(x::Rational, y::Rational)@607` | `fldDefaultSource` | Nothing to promise (forwards `RoundDown` to `div`) |
| `cld(x::Rational, y::Integer)@608` | `cldDefaultSource` | Nothing to promise (forwards `RoundUp` to `div`) |
| `cld(x::Integer, y::Rational)@608` | `cldDefaultSource` | Nothing to promise (forwards `RoundUp` to `div`) |
| `cld(x::Rational, y::Rational)@608` | `cldDefaultSource` | Nothing to promise (forwards `RoundUp` to `div`) |
| `round(x::Rational, r::RoundingMode)@612` | `roundRatDefaultSource` | Nothing to promise (forwards `typeof(x)` to `round`) |
| `round(x::Rational)@612` | `roundRatDefaultSource` | Nothing to promise (forwards `typeof(x)` to `round`) |
| `round(::Type{T}, x::Rational{Tr}, r::RoundingMode)@614` | `roundRatTypedSource` | `intarith-rational-infinite-rounding`, `intarith-rational-trunc-exact`, `promotion-trunc-rational-infinite-error`, `rational-floor-ceil-division` |
| `round(::Type{T}, x::Rational{Tr})@614` | `roundRatTypedSource` | `intarith-rational-infinite-rounding`, `intarith-rational-trunc-exact`, `promotion-trunc-rational-infinite-error`, `rational-floor-ceil-division` |
| `round(::Type{T}, x::Rational{Bool}, r::RoundingMode)@621` | `roundBoolRationalSource` | `rational-wrapping-and-remainder-exact` |
| `round(::Type{T}, x::Rational{Bool})@621` | `roundBoolRationalSource` | `rational-wrapping-and-remainder-exact` |
| `^(x::Rational, n::Integer)@628` | `powRationalIntegerGeneric` | `rational-gcd-lcm-gcdx-exact` |
| `^(x::Number, y::Rational)@632` | `powNumberRationalSource` | Nothing to promise (forwards `x ^ (y.num / y.den)`) |
| `^(x::T<:AbstractFloat, y::Rational)@633` | `powFloatRationalSource` | Nothing to promise (forwards `x ^ convert(T, y)`) |
| `^(z::Complex{T<:Real}, p::Rational)@634` | `powComplexRationalSource` | Nothing to promise (forwards `z ^ convert(typeof(one(T)^p), p)`) |
| `^(z::Complex{<:Rational}, n::Bool)@636` | `powComplexRationalBoolSource` | `rational-gcd-lcm-gcdx-exact` |
| `^(z::Complex{<:Rational}, n::Integer)@637` | `powComplexRationalIntegerGeneric` | `rational-complex-and-io-exact` |
| `iszero(x::Rational)@641` | `isZeroRationalSource` | `rational-unary-predicates-exact` |
| `isone(x::Rational)@642` | `isOneRationalSource` | `rational-unary-predicates-exact` |
| `lerpi(j::Integer, d::Integer, a::Rational, b::Rational)@644` | `lerpiSource` | Nothing to promise (forwards linear interpolation arithmetic) |
| `float(::Type{Rational{T}})@648` | `floatTypeSource` | Nothing to promise (forwards `float(T)`) |
| `gcd(x::Rational, y::Rational)@650` | `gcdRationalSource` | `rational-gcd-lcm-gcdx-exact` |
| `lcm(x::Rational, y::Rational)@656` | `lcmRationalSource` | `rational-gcd-lcm-gcdx-exact` |
| `gcdx(x::Rational, y::Rational)@662` | `gcdxRationalSource` | `rational-gcd-lcm-gcdx-exact` |
| `decompose(x::Rational)@678` | `decomposeSource` | `rational-components-roundtrip` |
| `hash(x::Rational{<:BitInteger64}, h::UInt)@679` | `hashRational64Source` | `rational-complex-and-io-exact` |
| `length(r::AbstractUnitRange{<:Rational})@707` | `lengthRationalRangeSource` | `rational-complex-and-io-exact` |
| `checked_length(r::AbstractUnitRange{<:Rational})@713` | `checkedLengthRationalRangeSource` | `rational-wrapping-and-remainder-exact` |
-/

def entries : List JuliaLean.Registry.Entry := [
  { id := "rational-input-approximation-tolerance", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T},x::Rational,tol::Real)"]
    statement := "For normalized finite rational inputs and nonnegative finite tolerance, a successful rationalize result is finite and differs from its rational input by no more than tol."
    source := "base/rational.jl:326-333; rational approximation tolerance"
    status := .refuted, prop := ``RationalInputApproximationTolerance, thm := some ``rationalInputApproximationTolerance_refuted
    issue := "none found (queries: rationalize Rational Int8 tolerance semiconvergent overflow)"
    notes := "Target nightly returns127//1 for rationalize(Int8,128//1;tol=eps(128.0)/2), with error1 exceeding tolerance2^-46; release1.13.2 returns1//0." },

  { id := "rational-complex-numerator-value", juliaFile := "base/rational.jl"
    juliaFns := ["numerator(::Complex{<:Rational})"]
    statement := "Complex rational numerator components scale their original numerators to the least common denominator, with no change in either exact rational value."
    source := "base/rational.jl:362-367; common-denominator representation"
    status := .proven, prop := ``ComplexRationalNumeratorValue, thm := some ``complexRationalNumeratorValue_proven },
  { id := "rational-complex-integer-power-value", juliaFile := "base/rational.jl"
    juliaFns := ["^(::Complex{<:Rational},::Integer)"]
    statement := "Nonnegative complex integer powers have the exact Gaussian power ratio; negative powers have the exact corresponding power ratio of the computed inverse, assuming integer negation is representable and the external squaring routine's numerical contract."
    source := "base/rational.jl:637-639; complex exponentiation"
    status := .proven, prop := ``ComplexIntegerPowerValue, thm := some ``complexIntegerPowerValue_proven },

  { id := "rational-rounded-quotient-value", juliaFile := "base/rational.jl"
    juliaFns := ["div(::Rational,::Integer,::RoundingMode)", "div(::Integer,::Rational,::RoundingMode)", "div(::Rational,::Rational,::RoundingMode)"]
    statement := "Every successful rounded quotient equals integer rounding applied to the original exact cross-products, for every rounding mode, assuming the external integer rounding method's positive-scale invariance."
    source := "base/rational.jl:586-598; rounded division"
    status := .proven, prop := ``RoundedRationalQuotients, thm := some ``roundedRationalQuotients_proven },

  { id := "rational-complex-equality-value", juliaFile := "base/rational.jl"
    juliaFns := ["==(::Complex,::Rational)", "==(::Rational,::Complex)"]
    statement := "For normalized finite real components, complex-rational equality holds exactly when the imaginary component is zero and the real cross-products agree."
    source := "base/rational.jl:583-584; complex equality"
    status := .proven, prop := ``ComplexRationalEqualityValue, thm := some ``complexRationalEqualityValue_proven },
  { id := "rational-complex-inverse-value", juliaFile := "base/rational.jl"
    juliaFns := ["_complex_exact_inv(::Complex)", "_complex_exact_inv(::Complex{<:Integer})"]
    statement := "The exact-inverse numerator multiplied by the original finite complex value has real component equal to the returned denominator and zero imaginary component; successful checked integer inverses satisfy the same identity."
    source := "base/rational.jl:120-135; multiplicative inverse identity"
    status := .proven, prop := ``ComplexExactInverseValue, thm := some ``complexExactInverseValue_proven },

  { id := "rational-unit-range-length-value", juliaFile := "base/rational.jl"
    juliaFns := ["length(::AbstractUnitRange{<:Rational})"]
    statement := "For aligned finite endpoints separated by k integer steps, successful length is k+1 whenever the endpoint subtraction and addition preserve their mathematical values."
    source := "base/rational.jl:704-712; inclusive unit-range length"
    status := .proven, prop := ``RationalUnitRangeLength, thm := some ``rationalUnitRangeLength_proven },
  { id := "rational-finite-half-integer-hash", juliaFile := "base/rational.jl"
    juliaFns := ["hash(::Rational{<:BitInteger64},::UInt)"]
    statement := "Every finite half-integer rational whose numerator is exactly representable uses the same hash as the exact dyadic float, at every BitInteger64 component type."
    source := "base/rational.jl:679-702; equal numerical values have equal hashes"
    status := .proven, prop := ``RationalHalfIntegerHash, thm := some ``rationalHalfIntegerHash_proven },
  { id := "rational-promotion-and-zero-error", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(::Integer,::Integer)", "__throw_rational_argerror_zero"]
    statement := "Value-preserving promotion preserves both rational components, and the zero-over-zero exception constructor retains the target twice in its lazy diagnostic payload."
    source := "base/rational.jl:18,30; component-value preservation and invalid-rational diagnostic"
    status := .proven, prop := ``RationalPromotionAndZeroError, thm := some ``rationalPromotionAndZeroError_proven },

  { id := "rational-io-display-parse-errors", juliaFile := "base/rational.jl"
    juliaFns := ["show(::IO,::Rational)", "read(::IO,::Type{Rational{T}})", "parse(::Type{Rational{T}},::AbstractString)"]
    statement := "Display writes numerator and denominator in order, omitting the denominator only in a typed denominator-one context; read propagates read failures; valid fraction parsing returns a reduced rational with the exact parsed ratio, including a leading second slash."
    source := "base/rational.jl:156-187; display, read and parse contracts"
    status := .proven, prop := ``RationalIoContracts, thm := some ``rationalIoContracts_proven },

  { id := "rational-linear-interpolation-value", juliaFile := "base/rational.jl"
    juliaFns := ["lerpi(j::Integer,d::Integer,a::Rational,b::Rational)"]
    statement := "For 0 ≤ j ≤ d and d > 0, successful rational interpolation returns the reduced exact barycentric value ((d-j)a+jb)/d."
    source := "base/rational.jl:644-646; linear interpolation identity"
    status := .proven, prop := ``RationalInterpolationValue, thm := some ``rationalInterpolationValue_proven },

  { id := "rational-complex-integer-quotient", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Complex{<:Integer},y::Complex{<:Integer})"]
    statement := "Every successful complex integer quotient is reduced in each component and has exact real value (ac+bd)/(c²+d²) and imaginary value (bc-ad)/(c²+d²)."
    source := "base/rational.jl:144-152; complex division identity"
    status := .proven, prop := ``ComplexIntegerQuotientValues, thm := some ``complexIntegerQuotientValues_proven },

  { id := "rational-integer-power-value", juliaFile := "base/rational.jl"
    juliaFns := ["^(x::Rational,n::Integer)"]
    statement := "For normalized finite nonzero rationals, integer powers have numerator/denominator ratio x.num^n/x.den^n, reversed for negative n, assuming the external power-by-squaring method's numerical contract."
    source := "base/rational.jl:628-630; integer exponentiation"
    status := .proven, prop := ``RationalIntegerPowerValue, thm := some ``rationalIntegerPowerValue_proven },

  { id := "rational-finite-float-equality", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::AbstractFloat,q::Rational)", "==(q::Rational,x::AbstractFloat)"]
    statement := "For every IEEE format, finite equality rejects rational denominators with more than one set bit and agrees with exact float/integer equality when the denominator is one."
    source := "base/rational.jl:521-529; binary floating-point representation"
    status := .proven, prop := ``FiniteFloatEquality, thm := some ``finiteFloatEquality_proven },

  { id := "rational-generic-numeric-values", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(::Type{T},num,den)", "Rational{T}(x::Rational)", "-(x::Rational)"]
    statement := "Value-preserving integer conversions preserve both rational components, and successful generic unary negation reverses the numerator's value while retaining the denominator."
    source := "base/rational.jl:14,190-192,400"
    status := .proven, prop := ``GenericRationalValueContracts, thm := some ``genericRationalValueContracts_proven },

  { id := "rational-integer-rationalize-range", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T},x::Integer;kvs...)", "Rational{T}(x::Integer)"]
    statement := "Integer rationalization rejects negative unsigned inputs, maps out-of-range signed integers to the corresponding infinity, and preserves in-range integers as normalized denominator-one rationals."
    source := "base/rational.jl:193-195,335-342"
    status := .proven, prop := ``IntegerRationalizeRange, thm := some ``integerRationalizeRange_proven },

  { id := "intarith-rational-infinity-sub", juliaFile := "base/rational.jl"
    juliaFns := ["-(::Rational,::Rational)", "-(::Rational{<:Unsigned})"]
    statement := "Subtracting a finite unsigned rational from positive infinity preserves infinity."
    source := "invariant: +infinity minus a finite value is +infinity"
    status := .refuted, prop := ``InfinitySub, thm := some ``infinitySub_refuted
    issue := "none found (queries: Rational unsigned infinity subtraction; rational infinity; rational unsigned)"
    notes := "The infinity shortcut negates the finite unsigned operand and throws OverflowError." },
  { id := "intarith-rational-normalize-before-convert", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::Integer,::Integer)"]
    statement := "Construction succeeds whenever the normalized reduced rational fits the target component type."
    source := "base/rational.jl:3-7; Rational Numbers manual"
    status := .refuted, prop := ``NormalizeBeforeConvert, thm := some ``normalizeBeforeConvert_refuted
    issue := "none found (queries: Rational typemin constructor InexactError; Rational Int8 constructor; rational normalization)"
    notes := "The typed constructor converts the positive reduced numerator before normalizing the denominator sign." },
  { id := "intarith-rational-infinite-rounding", juliaFile := "base/rational.jl"
    juliaFns := ["round", "floor", "ceil", "trunc"]
    statement := "Rounding infinite rationals to any BitInteger throws DivideError for all rounding modes."
    source := "base/rational.jl:614-619; integer division by zero"
    status := .proven, prop := ``InfiniteRoundingRejected, thm := some ``infiniteRoundingRejected_proven },
  { id := "intarith-rational-trunc-exact", juliaFile := "base/rational.jl"
    juliaFns := ["trunc", "round(::Type{T},::Rational,RoundToZero)"]
    statement := "Every positive-denominator rational truncates exactly to its mathematical quotient in its component type, including typemin numerators."
    source := "base/rational.jl:614-619; base/div.jl:5-13"
    status := .proven, prop := ``TruncExact, thm := some ``truncExact_proven },
  { id := "promotion-cmp-rational-signed-zero", juliaFile := "base/rational.jl"
    juliaFns := ["cmp(::AbstractFloat,::Rational)", "cmp(::Rational,::AbstractFloat)"]
    statement := "cmp between a float and a normalized Rational follows the isless total order."
    source := "cmp docstring, base/operators.jl:508-511"
    status := .refuted, prop := ``CmpRationalFloatIsless, thm := some ``cmpRationalFloatIsless_refuted
    issue := "none found (queries: cmp rational float signed zero; cmp -0 Rational zero)"
    notes := "The generated cmp methods use numerical equality for the two signed zeros." },
  { id := "promotion-rational-from-float-exact", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::AbstractFloat)"]
    statement := "Rational{T}(x) for finite float x returns only a rational exactly equal to x."
    source := "convert docstring, base/essentials.jl:428-430"
    status := .refuted, prop := ``RationalOfFloatExact, thm := some ``rationalOfFloatExact_refuted
    issue := "none found (queries: Rational Float64 exact Int8 0.1)"
    notes := "The constructor accepts the nearest Rational{Int8} approximation to binary64 0.1." },
  { id := "promotion-rational-from-float-representable", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::AbstractFloat)", "rationalize(::Type{T}, ::AbstractFloat)"]
    statement := "Rational{T}(x) succeeds with the exact value whenever finite x equals a normalized Rational{T}."
    source := "invariant; Rational docstring base/rational.jl:3-7"
    status := .refuted, prop := ``RationalOfFloatRepresentable, thm := some ``rationalOfFloatRepresentable_refuted
    issue := "none found (queries: Rational Int8 -128 Float64 representable)"
    notes := "The semiconvergent fallback for -128 selects -127//1 and the exact constructor throws InexactError." },
  { id := "promotion-float-from-rational-nearest", juliaFile := "base/rational.jl"
    juliaFns := ["Float64(::Rational)", "Float32(::Rational)", "Float16(::Rational)"]
    statement := "Float64(q) for a normalized finite Rational q is the nearest binary64 value, ties to even."
    source := "convert docstring, base/essentials.jl:443-445"
    status := .refuted, prop := ``RationalToFloatNearest, thm := some ``rationalToFloatNearest_refuted
    issue := "none found (queries: Float64 Rational nearest rounding)"
    notes := "Float64 converts numerator and denominator separately before dividing." },
  { id := "promotion-trunc-rational-infinite-error", juliaFile := "base/rational.jl"
    juliaFns := ["trunc(::Type{<:Integer}, ::Rational)", "round(::Type{<:Integer}, ::Rational)"]
    statement := "trunc(T, x) throws InexactError for the infinite rationals ±1//0, whose truncation is not representable."
    source := "trunc docstring, base/rounding.jl:423-424"
    status := .refuted, prop := ``TruncInfiniteInexact, thm := some ``truncInfiniteInexact_refuted
    issue := "none found (queries: trunc Rational infinity InexactError)"
    notes := "The rational rounding path delegates to integer division by zero and throws DivideError." },
  { id := "numberscov-rationalize-integer-tolerance", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T}, x::AbstractFloat, tol::Real)"]
    statement := "For finite floating inputs and nonnegative finite tolerance, a successful rationalize result is finite and differs from x by no more than tol."
    source := "base/rational.jl:238-243: result differs from x by no more than tol"
    status := .refuted, prop := ``RationalFloatingTolerance, thm := some ``rationalFloatingTolerance_refuted
    issue := "none found (queries: rationalize Integer tolerance; rationalize Int8 128 tol 1)"
    notes := "rationalize(Int8, 128.0; tol=0.0) returns 127//1, whose error 1 exceeds the requested tolerance." },
  { id := "rational-zero-over-zero-rejected", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::Integer,::Integer)", "//(::Integer,::Integer)"]
    statement := "Every fixed-width Rational constructor rejects the indeterminate 0//0 with ArgumentError."
    source := "base/rational.jl:31-46; Rational Numbers manual"
    status := .proven, prop := ``ZeroOverZeroRejected, thm := some ``zeroOverZeroRejected_proven },
  { id := "rational-components-roundtrip", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(::Type{T}, num, den)", "numerator(::Rational)", "denominator(::Rational)", "decompose(::Rational)"]
    statement := "Rebuilding a Rational from its numerator and denominator preserves its stored pair, and decompose returns (numerator(x), 0, denominator(x))."
    source := "numerator and denominator docstrings, base/rational.jl:9-15,346-384,678"
    status := .proven, prop := ``RationalComponentsRoundTrip, thm := some ``rationalComponentsRoundTrip_proven },
  { id := "rational-inverse-zero-infinity", juliaFile := "base/rational.jl"
    juliaFns := ["inv(::Rational)"]
    statement := "The inverse of a finite zero Rational is an infinite Rational with the original denominator as numerator."
    source := "base/rational.jl:503; Rational extended arithmetic"
    status := .proven, prop := ``InverseZeroIsInfinity, thm := some ``inverseZeroIsInfinity_proven },
  { id := "rational-integer-comparison-exact", juliaFile := "base/rational.jl"
    juliaFns := ["==(::Rational,::Integer)", "==(::Integer,::Rational)", "<(::Rational,::Integer)", "<(::Integer,::Rational)", "<=(::Rational,::Integer)", "<=(::Integer,::Rational)"]
    statement := "Comparisons with an integer use exact denominator-one equality and cross-products for positive-denominator rationals."
    source := "base/rational.jl:514-519"
    status := .proven, prop := ``RationalIntegerComparisonsExact, thm := some ``rationalIntegerComparisonsExact_proven },
  { id := "rational-float-comparison-exact", juliaFile := "base/rational.jl"
    juliaFns := ["cmp(::Rational,::AbstractFloat)", "cmp(::AbstractFloat,::Rational)", "<(::Rational,::AbstractFloat)", "<(::AbstractFloat,::Rational)", "<=(::Rational,::AbstractFloat)", "<=(::AbstractFloat,::Rational)"]
    statement := "For finite Float64 values, rational comparisons use the exact integer ratio of the float."
    source := "base/rational.jl:531-580"
    status := .proven, prop := ``RationalFloatComparisonsExact, thm := some ``rationalFloatComparisonsExact_proven },
  { id := "rational-floor-ceil-division", juliaFile := "base/rational.jl"
    juliaFns := ["floor(::Type{T},::Rational)", "ceil(::Type{T},::Rational)", "round(::Type{T},::Rational,RoundDown)", "round(::Type{T},::Rational,RoundUp)"]
    statement := "With positive denominator, rational floor and ceiling agree with integer floor and ceiling division at every component width."
    source := "base/rational.jl:614-619; base/div.jl"
    status := .proven, prop := ``RationalFloorCeilDivision, thm := some ``rationalFloorCeilDivision_proven },
  { id := "rational-float-conversion-roundtrip", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::AbstractFloat)"]
    statement := "Successful Float64 rationalization produces coprime components with canonical zero n=0,d=1 and infinity |n|=1,d=0; exact conversion also round-trips to an IEEE-equal Float64."
    source := "base/rational.jl:218-222"
    status := .proven, prop := ``RationalFloatRoundTrip, thm := some ``rationalFloatRoundTrip_proven },
  { id := "rational-checked-den-positive", juliaFile := "base/rational.jl"
    juliaFns := ["checked_den(::Type{T},::T,::T)"]
    statement := "When checked_den receives a nonnegative denominator, it preserves the exact pair."
    source := "base/rational.jl:20-26"
    status := .proven, prop := ``CheckedDenKeepsPositiveDenominator, thm := some ``checkedDenKeepsPositiveDenominator_proven },
  { id := "rational-rational-comparisons", juliaFile := "base/rational.jl"
    juliaFns := ["==(::Rational,::Rational)", "<(::Rational,::Rational)", "<=(::Rational,::Rational)"]
    statement := "Rational equality compares stored pairs; order compares numerators directly for equal denominators and exact cross-products otherwise."
    source := "base/rational.jl:507-511"
    status := .proven, prop := ``RationalRationalOrderExact, thm := some ``rationalRationalOrderExact_proven }
  , { id := "rational-divgcd-coprime", juliaFile := "base/rational.jl"
      juliaFns := ["divgcd"]
      statement := "Every successful divgcd result has numerator and denominator with gcd one."
      source := "base/rational.jl:59-62"
      status := .proven, prop := ``DivGcdReturnsCoprime, thm := some ``divGcdReturnsCoprime_proven }
  , { id := "rational-constructor-normalized-positive", juliaFile := "base/rational.jl"
      juliaFns := ["Rational{T}(::Integer,::Integer)", "//(::Integer,::Integer)"]
      statement := "Every successful construction from a positive denominator returns a reduced rational with positive denominator."
      source := "base/rational.jl:30-46,91"
      status := .proven, prop := ``ConstructPositiveDenominatorNormalizes,
        thm := some ``constructPositiveDenominatorNormalizes_proven }
  , { id := "rational-arithmetic-exact", juliaFile := "base/rational.jl"
      juliaFns := ["+(::Rational,::Rational)", "-(::Rational,::Rational)", "*(::Rational,::Rational)", "//(::Rational,::Rational)", "//(::Rational,::Integer)", "//(::Integer,::Rational)", "*(::Rational,::Integer)", "*(::Integer,::Rational)", "+(::Rational,::Integer)", "-(::Rational,::Integer)", "+(::Integer,::Rational)", "-(::Integer,::Rational)", "fma(::Rational,::Rational,::Rational)"]
      statement := "Checked rational arithmetic (+, -, *, //) and mixed Rational/Integer arithmetic preserve exact mathematical ratios and positive reduced denominators whenever no integer overflow occurs."
      source := "base/rational.jl:93-114,415-440,460-494,505"
      status := .proven, prop := ``RationalArithmeticExact,
      thm := some ``rationalArithmeticExact_proven }
  , { id := "rational-unary-predicates-exact", juliaFile := "base/rational.jl"
      juliaFns := ["+(::Rational)", "-(::Rational)", "-(::Rational{<:BitSigned})", "-(::Rational{<:Unsigned})", "-%(::Rational)", "abs(::Rational)", "sign(::Rational)", "signbit(::Rational)", "typemin(::Type{Rational{<:Signed}})", "typemin(::Type{Rational{<:Integer}})", "typemax(::Type{Rational{<:Integer}})", "isinteger(::Rational)", "ispow2(::Rational)", "iszero(::Rational)", "isone(::Rational)", "Bool(::Rational)", "(::Type{T})(::Rational) where T<:Integer", "Rational(::Integer)", "Rational{T}(::Rational)", "Rational{T}(::Integer)", "*(::Bool,::Rational)"]
      statement := "Unary rational operations, sign and finiteness predicates, extremal values, integer/boolean conversions, and Bool strong-zero multiplication obey their documented contracts."
      source := "base/rational.jl:50,190-202,387-413,497-499,641-642"
      status := .proven, prop := ``RationalUnaryAndPredicatesExact,
      thm := some ``rationalUnaryAndPredicatesExact_proven }
  , { id := "rational-wrapping-and-remainder-exact", juliaFile := "base/rational.jl"
      juliaFns := ["+%(::Rational,::Rational)", "-%(::Rational,::Rational)", "rem(::Rational,::Rational)", "mod(::Rational,::Rational)", "rem(::Rational,::Integer)", "mod(::Rational,::Integer)", "rem(::Integer,::Rational)", "mod(::Integer,::Rational)", "round(::Type{T},::Rational{Bool},::RoundingMode)", "checked_length(::AbstractUnitRange{<:Rational})"]
      statement := "Wrapping rational addition and subtraction, rational remainders, Bool-rational rounding, and checked rational unit-range length preserve reduced positive-denominator invariants and exact boundary cases."
      source := "base/rational.jl:424-431,442-458,474-480,621-626,713-720"
      status := .proven, prop := ``RationalWrappingAndRemainderExact,
      thm := some ``rationalWrappingAndRemainderExact_proven }
  , { id := "rational-gcd-lcm-gcdx-exact", juliaFile := "base/rational.jl"
      juliaFns := ["gcd(::Rational,::Rational)", "lcm(::Rational,::Rational)", "gcdx(::Rational,::Rational)", "^(::Rational,::Integer)", "^(::Complex{<:Rational},::Bool)", "==(::AbstractFloat,::Rational)", "==(::Rational,::AbstractFloat)"]
      statement := "Rational gcd, lcm, integer/boolean powers, and float-rational equality methods reject mixed finite/infinite inputs and compute exact componentwise results."
      source := "base/rational.jl:521-529,628-636,650-674"
      status := .proven, prop := ``RationalGcdLcmGcdxExact,
      thm := some ``rationalGcdLcmGcdxExact_proven }
  , { id := "rational-complex-and-io-exact", juliaFile := "base/rational.jl"
      juliaFns := ["_complex_exact_inv(::Complex)", "_complex_exact_inv(::Complex{<:Integer})", "//(::Complex{<:Integer},::Complex{<:Integer})", "show(::IO,::Rational)", "read(::IO,::Type{Rational{T}})", "parse(::Type{Rational{T}},::AbstractString)", "numerator(::Complex{<:Rational})", "==(::Complex,::Rational)", "==(::Rational,::Complex)", "div(::Rational,::Integer,::RoundingMode)", "div(::Integer,::Rational,::RoundingMode)", "div(::Rational,::Rational,::RoundingMode)", "^(::Complex{<:Rational},::Integer)", "hash(::Rational{<:BitInteger64},::UInt)", "length(::AbstractUnitRange{<:Rational})"]
      statement := "Complex inverses and quotients preserve exact values; complex numerators share a common denominator; equality and powers preserve numerical values; display, read and parse obey their I/O contracts; rounded quotients, finite hashes and unit-range lengths preserve their mathematical meanings."
      source := "base/rational.jl:120-187,326-333,362-367,583-598,637-639,679-712"
      status := .proven, prop := ``RationalComplexAndIoExact,
      thm := some ``rationalComplexAndIoExact_proven }
]
end JuliaLean.Proofs.base.rational
