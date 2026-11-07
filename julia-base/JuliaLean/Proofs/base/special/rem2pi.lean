import JuliaLean.Registry.Types
import JuliaLean.base.special.rem2pi
import JuliaLean.Bindings.base.math
import JuliaLean.base.div
import JuliaLean.Spec.Pi

/-!
Only source-bound public rounding methods are used below. The input `x` covers all
Float64 bit patterns, including every NaN encoding and both signs of zero/infinity.
No hypothesis assumes an algorithm outcome or the correctness of its reduction.
The installed Nearest/ToZero callee binding is acknowledged in the inventory.
Its unrestricted MPFR load context and the closed generic rounding-mode tags
are separate model gaps; neither is needed by the Down/Up statements below.
-/

namespace JuliaLean.Proofs.base.special.rem2pi

open JuliaLean JuliaLean.base.float

/-- Project the actual Float32 RoundDown wrapper's definitionally non-error result.
This helper retains the installed all-mode Float64 dispatcher. No success premise,
error default, or alternate remainder implementation is introduced. `mod2pi`
passes only RoundDown, so its pure callee adapter below uses this specialization.
-/
def down32Value (machine : JuliaLean.Bindings.base.math.Machine) (x : FV .f32) : FV .f32 :=
  JuliaLean.base.int.okOf
    (JuliaLean.base.special.rem2pi.rem2piFloat32
      (JuliaLean.Bindings.base.math.rem2pi64 machine) x .Down)
    (by
      intro e h
      simp [JuliaLean.base.special.rem2pi.rem2piFloat32,
        JuliaLean.Bindings.base.math.rem2pi64, bind, Except.bind, pure, Except.pure] at h)

/-- The ordinary binary64 approximation to 2π, also the pinned source's
`pi4o2_h` literal (base/special/rem2pi.jl:11). It is the comparison call's
ordinary divisor; it is not supplied to the rem2pi implementation. -/
def OrdinaryTwoPi64 : FV .f64 :=
  JuliaLean.Promotion.Fl.ofBits 0x401921fb54442d18

/-- Exact specification of 0 ≤ a + bπ through the installed mathematical
Dedekind cuts. For b ≠ 0, irrationality makes equality to the rational -a/b
impossible, so the strict cuts express the non-strict comparison exactly.
This helper is mathematical observation only; no π implementation is replaced. -/
def PiLinearNonnegative (a b : Int) : Prop :=
  if b = 0 then 0 ≤ a
  else if 0 < b then JuliaLean.Spec.Pi.rationalBelowPi (-a) b.natAbs
  else JuliaLean.Spec.Pi.piBelowRational a b.natAbs

/-- q is floor(x/(2π)): 2qπ ≤ x < 2(q+1)π, with x interpreted exactly. -/
def ExactDownPiQuotient (x : FV .f64) (q : Int) : Prop :=
  let (n, d) := x.toRat
  0 < d ∧
    PiLinearNonnegative n (-2 * q * (d : Int)) ∧
    ¬ PiLinearNonnegative n (-2 * (q + 1) * (d : Int))

/-- q is ceil(x/(2π)): 2(q-1)π < x ≤ 2qπ, with x interpreted exactly. -/
def ExactUpPiQuotient (x : FV .f64) (q : Int) : Prop :=
  let (n, d) := x.toRat
  0 < d ∧
    PiLinearNonnegative (-n) (2 * q * (d : Int)) ∧
    ¬ PiLinearNonnegative (-n) (2 * (q - 1) * (d : Int))

/-- For r = x - 2qπ, the finite exact values satisfy |y-r| ≤ |z-r|.
The difference of squared errors is (z-y)(z+y-2x+4qπ). Clearing only positive
rational denominators leaves a linear form in π; no floating arithmetic or
numerical tolerance is used in this independent specification. -/
def NoWorseExactRemainderError (x y z : FV .f64) (q : Int) : Prop :=
  let (xn, xd) := x.toRat
  let (yn, yd) := y.toRat
  let (zn, zd) := z.toRat
  let a := zn * (yd : Int) - yn * (zd : Int)
  let b := (zn * (yd : Int) + yn * (zd : Int)) * (xd : Int) -
    2 * xn * (yd : Int) * (zd : Int)
  let c := 4 * q * (xd : Int) * (yd : Int) * (zd : Int)
  0 < xd ∧ 0 < yd ∧ 0 < zd ∧ PiLinearNonnegative (a * b) (a * c)

end JuliaLean.Proofs.base.special.rem2pi

namespace JuliaLean.Proofs.base.special.rem2piArchive20261101

open JuliaLean.Proofs.base.special.rem2pi
open JuliaLean JuliaLean.base.float

/-- The downward remainder lies in the documented nonnegative interval for every finite Float64, and is NaN exactly on nonfinite inputs.
Julia source: base/special/rem2pi.jl:68-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:1188-1207; doc/src/base/math.md:19-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
The largest Float64 not exceeding mathematical 2π is 0x401921fb54442d18,
the source's pi4o2_h (base/special/rem2pi.jl:11). The same bound stated on a
Float64 result is equivalent to result ≤ 2π, not a replacement modulus.
-/
def DownRangeAndNonfinite : Prop :=
  ∀ x : FV .f64,
    let y := JuliaLean.base.special.rem2pi.rem2piDown x
    if isfinite_IEEEFloat x then
      isfinite_IEEEFloat y = true ∧
      le_IEEEFloat (zero_float .f64) y = true ∧
      le_IEEEFloat y (JuliaLean.Promotion.Fl.ofBits 0x401921fb54442d18) = true
    else isnan_IEEEFloat y = true

/-- The upward remainder lies in the documented nonpositive interval for every finite Float64, and is NaN exactly on nonfinite inputs.
Julia source: base/special/rem2pi.jl:100-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:1188-1207; doc/src/base/math.md:19-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
0xc01921fb54442d18 is the least Float64 not below mathematical -2π. Thus the
machine comparison expresses the documented lower bound without rounding x or
replacing the true modulus by an ordinary Float64 divisor.
-/
def UpRangeAndNonfinite : Prop :=
  ∀ x : FV .f64,
    let y := JuliaLean.base.special.rem2pi.rem2piUp x
    if isfinite_IEEEFloat x then
      isfinite_IEEEFloat y = true ∧
      le_IEEEFloat (JuliaLean.Promotion.Fl.ofBits 0xc01921fb54442d18) y = true ∧
      le_IEEEFloat y (zero_float .f64) = true
    else isnan_IEEEFloat y = true

/-- The public Float32 mod2pi result is in [0,2π) for every finite input, and NaN
for nonfinite inputs; the exclusive upper bound preserves the reported Julia bug.
Julia source: base/math.jl:1241; base/special/rem2pi.jl:68-98,133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:1221-1233; doc/src/base/math.md:23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
0x40c90fda is the largest Float32 strictly below mathematical 2π. This result
comparison does not substitute a rounded divisor in the implementation.
Registry ID: mathfuncs-rem2pi-float32-range
-/
def Mod2piFloat32Range : Prop :=
  ∀ (machine : JuliaLean.Bindings.base.math.Machine) (x : FV .f32),
    let y := JuliaLean.base.math.mod2pi (fun value _ => down32Value machine value) x
    if isfinite_IEEEFloat x then
      isfinite_IEEEFloat y = true ∧
      le_IEEEFloat (zero_float .f32) y = true ∧
      le_IEEEFloat y (JuliaLean.Promotion.Fl.ofBits 0x40c90fda) = true
    else isnan_IEEEFloat y = true

/-- For every finite binary64 input, rem2pi with RoundDown is at least as accurate
in absolute error against the exact-2π remainder as ordinary rem with the binary64
2π approximation; every nonfinite input returns NaN.
The documentation's "more accurate" is interpreted non-strictly because exact
cases, including zero, tie. No correct-rounding or ULP guarantee is asserted.
Julia source: base/special/rem2pi.jl:68-99; base/div.jl:128;
base/float.jl:590-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:1188-1207,1221-1234;
doc/src/base/math.md:20-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DownHighPrecisionAccuracy : Prop :=
  ∀ x : FV .f64,
    let y := JuliaLean.base.special.rem2pi.rem2piDown x
    if JuliaLean.base.float.isfinite_IEEEFloat x then
      ∃ z : FV .f64,
        JuliaLean.base.div.rem_Down
          (fun a b => .ok (JuliaLean.base.float.mod_AbstractFloat a b))
          x OrdinaryTwoPi64 = .ok z ∧
        JuliaLean.base.float.isfinite_IEEEFloat y = true ∧
        JuliaLean.base.float.isfinite_IEEEFloat z = true ∧
        ∃ q : Int, ExactDownPiQuotient x q ∧ NoWorseExactRemainderError x y z q
    else JuliaLean.base.float.isnan_IEEEFloat y = true

/-- For every finite binary64 input, rem2pi with RoundUp is at least as accurate
in absolute error against the exact-2π remainder as ordinary rem with the binary64
2π approximation; every nonfinite input returns NaN.
The documentation's "more accurate" is interpreted non-strictly because exact
cases, including zero, tie. No correct-rounding or ULP guarantee is asserted.
Julia source: base/special/rem2pi.jl:100-132; base/div.jl:129;
base/float.jl:590-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:1188-1207,1221-1234;
doc/src/base/math.md:20-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UpHighPrecisionAccuracy : Prop :=
  ∀ x : FV .f64,
    let y := JuliaLean.base.special.rem2pi.rem2piUp x
    if JuliaLean.base.float.isfinite_IEEEFloat x then
      ∃ z : FV .f64,
        JuliaLean.base.div.rem_Up
          (fun a b => .ok (JuliaLean.base.float.mod_AbstractFloat a b))
          JuliaLean.base.float.neg_IEEEFloat x OrdinaryTwoPi64 = .ok z ∧
        JuliaLean.base.float.isfinite_IEEEFloat y = true ∧
        JuliaLean.base.float.isfinite_IEEEFloat z = true ∧
        ∃ q : Int, ExactUpPiQuotient x q ∧ NoWorseExactRemainderError x y z q
    else JuliaLean.base.float.isnan_IEEEFloat y = true

end JuliaLean.Proofs.base.special.rem2piArchive20261101

namespace JuliaLean.Proofs.base.special.rem2pi

open JuliaLean.Registry

end JuliaLean.Proofs.base.special.rem2pi

/-! Partial proofs over the unchanged rem2pi subjects. -/
namespace JuliaLean.ChatGPT.Batch4.Group18
open JuliaLean JuliaLean.base.float
open JuliaLean.C
open JuliaLean.Promotion (Fl Fmt half)
open JuliaLean.base.special.rem2pi
open JuliaLean.Proofs.base.special.rem2pi
open JuliaLean.Proofs.base.special.rem2piArchive20261101

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

theorem remIEEEWidth (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem remIEEEBitsOfBits {f : Fmt} (v : Nat) :
    (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem remIEEEOfBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem remIEEEExt {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← remIEEEOfBits x, ← remIEEEOfBits y, h]

theorem remIEEESplit {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := remIEEEWidth f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]

theorem remIEEEExponent {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem remIEEEFraction {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem remIEEEFiniteNotNan {f : Fmt} {x : Fl f} (h : x.isfinite = true) :
    x.isnan = false := by
  simp only [Fl.isfinite, bne_iff_ne] at h
  simp only [Fl.isnan, beq_eq_false_iff_ne.mpr h, Bool.false_and]

theorem remIEEEFiniteNotInf {f : Fmt} {x : Fl f} (h : x.isfinite = true) :
    x.isinf = false := by
  simp only [Fl.isfinite, bne_iff_ne] at h
  simp only [Fl.isinf, beq_eq_false_iff_ne.mpr h, Bool.false_and]

theorem remIEEEFinish {T : FTy} (v : FV T) : finishFloat v = v := by
  unfold finishFloat
  have : (T.fmt == bfloat) = false := by cases T <;> decide
  rw [this]
  rfl

theorem remIEEEIsnan {T : FTy} (x : FV T) : isnan_IEEEFloat x = x.isnan := by
  unfold isnan_IEEEFloat isnan_AbstractFloat eq_IEEEFloat eq_float jlEqFloat Fl.eq
  simp only [beq_self_eq_true, Bool.true_or, Bool.and_true, Bool.and_self, Bool.not_not]

theorem remIEEENegParts {T : FTy} (x : FV T) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := remIEEESplit x
  have h2 := remIEEEWidth T.fmt
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hs] at hbx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    unfold Fl.magnitude Fl.signbit
    rw [remIEEEBitsOfBits, Nat.mod_eq_of_lt hlt]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mod_left]
    · rw [decide_eq_true_iff]
      omega
  · simp only [↓reduceIte, Bool.not_true]
    rw [hs] at hbx
    simp only [↓reduceIte] at hbx
    have hlt : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    have hsub : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) = x.magnitude := by omega
    unfold Fl.magnitude Fl.signbit
    rw [remIEEEBitsOfBits, Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]
    omega

theorem remIEEENegRat {T : FTy} (x : FV T) :
    (Fl.neg x).isfinite = x.isfinite ∧
    (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
  obtain ⟨hm, hs⟩ := remIEEENegParts x
  have he : (Fl.neg x).expField = x.expField := by
    rw [remIEEEExponent, hm, ← remIEEEExponent]
  have hfr : (Fl.neg x).frac = x.frac := by
    rw [remIEEEFraction, hm, ← remIEEEFraction]
  have hfn : (Fl.neg x).isfinite = x.isfinite := by
    simp only [Fl.isfinite, he]
  refine ⟨hfn, ?_⟩
  unfold Fl.toRat
  simp only [hfn, he, hfr, hs]
  cases hf : x.isfinite <;> cases hx : x.signbit <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals first | rfl | (split <;> split <;> simp only [Prod.fst, Prod.snd, Int.neg_mul, Int.neg_neg])

theorem remIEEEDenominator {f : Fmt} (x : Fl f) (hf : x.isfinite = true) :
    0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> split
  all_goals first | exact Nat.zero_lt_one | exact Nat.two_pow_pos _

theorem remIEEESubRat {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    sub_IEEEFloat x y = Fl.roundRat
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int))
      (x.toRat.2 * y.toRat.2) (x.signbit && !y.signbit) := by
  have hn := remIEEENegRat y
  have hnf : (Fl.neg y).isfinite = true := hn.1.trans hy
  have hsg := (remIEEENegParts y).2
  unfold sub_IEEEFloat sub_float jlSubFloat floatSub floatAdd
  simp only [remIEEEFinish, remIEEEFiniteNotNan hx, remIEEEFiniteNotNan hy,
    remIEEEFiniteNotNan hnf, remIEEEFiniteNotInf hx, remIEEEFiniteNotInf hy,
    remIEEEFiniteNotInf hnf, Bool.false_eq_true, ↓reduceIte, hn.2, hsg]
  congr 1
  simp only [Int.neg_mul, Int.sub_eq_add_neg]

theorem remIEEENaNMag {T : FTy} (x : FV T) :
    x.isnan = true ↔ T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := by
  have hM := (remIEEESplit x).2
  have hE : T.fmt.emax + 1 = 2 ^ T.fmt.eb := by cases T <;> decide
  have hP := Nat.two_pow_pos T.fmt.sb
  have hdiv : x.expField < 2 ^ T.fmt.eb := by
    rw [remIEEEExponent]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hm : x.magnitude = x.expField * 2 ^ T.fmt.sb + x.frac := by
    rw [remIEEEExponent, remIEEEFraction]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod x.magnitude (2 ^ T.fmt.sb)).symm
  have hf : x.frac < 2 ^ T.fmt.sb := by
    rw [remIEEEFraction]
    exact Nat.mod_lt _ hP
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨he, hfr⟩
    rw [hm, he]
    omega
  · intro hgt
    have he : x.expField = T.fmt.emax := by
      rcases Nat.lt_or_ge x.expField T.fmt.emax with hlt | hge
      · have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.succ_mul] at this
        omega
      · omega
    exact ⟨he, by rw [hm, he] at hgt; omega⟩

theorem remIEEEQuietMag {T : FTy} (x : FV T) :
    (quietFloat x).magnitude = x.magnitude ||| 2 ^ (T.fmt.sb - 1) := by
  have hq : 2 ^ (T.fmt.sb - 1) < 2 ^ (T.fmt.eb + T.fmt.sb) := by
    cases T <;> decide
  have hqw : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width := by
    rw [remIEEEWidth]
    omega
  unfold quietFloat Fl.magnitude
  change ((x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ T.fmt.width) %
    2 ^ (T.fmt.eb + T.fmt.sb) = x.toBits % 2 ^ (T.fmt.eb + T.fmt.sb) ||| 2 ^ (T.fmt.sb - 1)
  have hor : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.width :=
    Nat.or_lt_two_pow x.bits.isLt hqw
  rw [Nat.mod_eq_of_lt hor, Nat.or_mod_two_pow, Nat.mod_eq_of_lt hq]

theorem remIEEEQuietNan {T : FTy} (x : FV T) (hx : x.isnan = true) :
    (quietFloat x).isnan = true := by
  rw [remIEEENaNMag] at hx ⊢
  rw [remIEEEQuietMag]
  exact Nat.lt_of_lt_of_le hx Nat.left_le_or

theorem remIEEEFinite {T : FTy} (x : FV T) : isfinite_IEEEFloat x = x.isfinite := by
  unfold isfinite_IEEEFloat isfinite_AbstractFloat sub_IEEEFloat sub_float jlSubFloat
  rw [remIEEEIsnan, remIEEEFinish]
  unfold floatSub floatAdd
  obtain ⟨hneg_mag, hneg_sign⟩ := remIEEENegParts x
  have hneg_exp : (Fl.neg x).expField = x.expField := by
    rw [remIEEEExponent, remIEEEExponent, hneg_mag]
  have hneg_frac : (Fl.neg x).frac = x.frac := by
    rw [remIEEEFraction, remIEEEFraction, hneg_mag]
  have hneg_nan : (Fl.neg x).isnan = x.isnan := by
    unfold Fl.isnan
    rw [hneg_exp, hneg_frac]
  have hneg_inf : (Fl.neg x).isinf = x.isinf := by
    unfold Fl.isinf
    rw [hneg_exp, hneg_frac]
  rw [hneg_nan, hneg_inf, hneg_sign, (remIEEENegRat x).2]
  have hinv_nan : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
  have hzero_nan : (Fl.zero false : FV T).isnan = false := by cases T <;> decide
  by_cases hfin : x.isfinite = true
  · simp only [hfin, remIEEEFiniteNotNan hfin, remIEEEFiniteNotInf hfin,
      Bool.false_eq_true, ↓reduceIte]
    have hd_pos : 0 < x.toRat.2 := remIEEEDenominator x hfin
    have hd_ne : (x.toRat.2 * x.toRat.2 == 0) = false :=
      beq_eq_false_iff_ne.mpr (by have := Nat.mul_pos hd_pos hd_pos; omega)
    have h0 : x.toRat.1 * (x.toRat.2 : Int) + -x.toRat.1 * (x.toRat.2 : Int) = 0 := by
      rw [Int.neg_mul, Int.add_right_neg]
    have hs : (x.signbit && !x.signbit) = false := by cases x.signbit <;> rfl
    rw [h0, hs]
    simp only [Fl.roundRat, hd_ne, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      hzero_nan, Bool.not_false]
  · have hnf : x.isfinite = false := Bool.eq_false_iff.mpr hfin
    rw [hnf]
    cases hn : x.isnan
    · have hi : x.isinf = true := by
        unfold Fl.isfinite at hnf
        unfold Fl.isnan at hn
        unfold Fl.isinf
        simp only [bne_eq_false_iff_eq] at hnf
        simp only [hnf, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
        simp only [hnf, hn, beq_self_eq_true, Bool.and_self]
      have hne_s : (x.signbit != !x.signbit) = true := by cases x.signbit <;> rfl
      simp only [Bool.false_eq_true, ↓reduceIte, hi, hne_s,
        Bool.and_self, hinv_nan, Bool.not_true]
    · simp only [↓reduceIte, remIEEEQuietNan x hn, Bool.not_true]


/-- The source's NaN branch returns the input unchanged for every NaN encoding. -/
theorem rem2pi_down_nan (x : FV .f64) (h : isnan_IEEEFloat x = true) :
    rem2piDown x = x := by
  simp only [rem2piDown, h, ↓reduceIte, Id.run_pure]

/-- The corresponding NaN branch for upward rounding. -/
theorem rem2pi_up_nan (x : FV .f64) (h : isnan_IEEEFloat x = true) :
    rem2piUp x = x := by
  simp only [rem2piUp, h, ↓reduceIte, Id.run_pure]

/-- Infinite non-NaN inputs are rejected by the source before argument reduction. -/
theorem rem2pi_down_infinite (x : FV .f64)
    (hn : isnan_IEEEFloat x = false) (hi : isinf_IEEEFloat x = true) :
    rem2piDown x = nan_float .f64 := by
  simp only [rem2piDown, hn, hi, Bool.false_eq_true, ↓reduceIte, Id.run_pure]

theorem rem2pi_up_infinite (x : FV .f64)
    (hn : isnan_IEEEFloat x = false) (hi : isinf_IEEEFloat x = true) :
    rem2piUp x = nan_float .f64 := by
  simp only [rem2piUp, hn, hi, Bool.false_eq_true, ↓reduceIte, Id.run_pure]

/-- Positive inputs strictly below the stored 2π high part take the exact identity branch. -/
theorem rem2pi_down_small_nonnegative (x : FV .f64)
    (hn : isnan_IEEEFloat x = false) (hi : isinf_IEEEFloat x = false)
    (hu : lt_float x pi4o2.1 = true)
    (hl : le_float (zero_float .f64) x = true) :
    rem2piDown x = x := by
  simp only [rem2piDown, hn, hi, hu, hl, Bool.false_eq_true, ↓reduceIte, Id.run_pure]

/-- Negative inputs above the negative high part take the exact identity branch. -/
theorem rem2pi_up_small_nonpositive (x : FV .f64)
    (hn : isnan_IEEEFloat x = false) (hi : isinf_IEEEFloat x = false)
    (hl : lt_float (neg_float pi4o2.1) x = true)
    (hu : le_float x (zero_float .f64) = true) :
    rem2piUp x = x := by
  simp only [rem2piUp, hn, hi, hl, hu, Bool.false_eq_true, ↓reduceIte, Id.run_pure]

/-- A constructible Float32 input whose remainder rounds above mathematical 2π. -/
def rem2pi32_counterexample : FV .f32 := Fl.ofBits 0x80000001

/-- The Float32 RoundDown adapter does not inspect any Machine field. -/
theorem rem2pi32_down_machine_independent
    (machine : JuliaLean.Bindings.base.math.Machine) (x : FV .f32) :
    down32Value machine x = convertFloat .f32 (rem2piDown (convertFloat .f64 x)) := by
  rfl

/-- Kernel reduction of the actual installed Float32 public subject. -/
theorem rem2pi32_counterexample_value (machine : JuliaLean.Bindings.base.math.Machine) :
    JuliaLean.base.math.mod2pi (fun value _ => down32Value machine value)
        rem2pi32_counterexample = (Fl.ofBits 0x40c90fdb : FV .f32) := by
  rfl

/-- Any concrete Machine would make the frozen Float32 range property contradictory. -/
theorem rem2pi32_range_counterexample_for_machine
    (machine : JuliaLean.Bindings.base.math.Machine) : ¬ Mod2piFloat32Range := by
  intro claim
  have h := claim machine rem2pi32_counterexample
  change (if isfinite_IEEEFloat rem2pi32_counterexample then _ else _) at h
  have hf : isfinite_IEEEFloat rem2pi32_counterexample = true := by decide
  rw [hf, ite_eq_left rfl, rem2pi32_counterexample_value] at h
  have hupper : le_IEEEFloat (Fl.ofBits 0x40c90fdb : FV .f32)
      (Fl.ofBits 0x40c90fda) = false := by decide
  rw [hupper] at h
  exact Bool.false_ne_true h.2.2

/-- The public reproducer supplies the value; completing the exact refutation additionally
requires an inhabitance proof for the unrelated MPFR-bearing Machine record. -/
theorem rem2pi32_range_refutation_if_machine_exists
    (hm : Nonempty JuliaLean.Bindings.base.math.Machine) : ¬ Mod2piFloat32Range := by
  obtain ⟨machine⟩ := hm
  exact rem2pi32_range_counterexample_for_machine machine


/-- The Float64 public infinity test agrees with the encoding classification. -/
theorem remIEEEInf64 (x : FV .f64) : isinf_IEEEFloat x = x.isinf := by
  unfold isinf_IEEEFloat egal_float abs_IEEEFloat abs_float jlAbsFloat unaryFloat
    oftype_float inf_float
  rw [remIEEEFinish]
  have hhalf : (FTy.f64.fmt == half) = false := by decide
  simp only [hhalf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hbound : x.magnitude < 2 ^ FTy.f64.fmt.width := by
    have hm := (remIEEESplit x).2
    have hw := remIEEEWidth FTy.f64.fmt
    omega
  rw [remIEEEBitsOfBits, Nat.mod_eq_of_lt hbound]
  change (x.magnitude == 0x7ff0000000000000) = x.isinf
  unfold Fl.isinf
  rw [remIEEEExponent, remIEEEFraction]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq]
  change (x.magnitude = 0x7ff0000000000000) ↔
    (x.magnitude / 2^52 = 2047 ∧ x.magnitude % 2^52 = 0)
  omega

/-- Every nonfinite Float64 encoding is classified by the public NaN/infinity tests. -/
theorem remIEEE_nonfinite_cases (x : FV .f64)
    (hf : isfinite_IEEEFloat x = false) :
    isnan_IEEEFloat x = true ∨
      (isnan_IEEEFloat x = false ∧ isinf_IEEEFloat x = true) := by
  rw [remIEEEFinite] at hf
  by_cases hn : isnan_IEEEFloat x = true
  · exact Or.inl hn
  · have hnf : isnan_IEEEFloat x = false := Bool.eq_false_iff.mpr hn
    refine Or.inr ⟨hnf, ?_⟩
    rw [remIEEEInf64]
    have hexp : x.expField = FTy.f64.fmt.emax := by
      simpa only [Fl.isfinite, bne_eq_false_iff_eq] using hf
    have hfrac : x.frac = 0 := by
      rw [remIEEEIsnan] at hnf
      simpa only [Fl.isnan, hexp, beq_self_eq_true, Bool.true_and,
        bne_eq_false_iff_eq] using hnf
    simp only [Fl.isinf, hexp, hfrac, beq_self_eq_true, Bool.true_and]

/-- The complete nonfinite branches of both range and both accuracy targets. -/
theorem rem2pi_nonfinite (x : FV .f64) (hf : isfinite_IEEEFloat x = false) :
    isnan_IEEEFloat (rem2piDown x) = true ∧
      isnan_IEEEFloat (rem2piUp x) = true := by
  rcases remIEEE_nonfinite_cases x hf with hn | ⟨hn, hi⟩
  · rw [rem2pi_down_nan x hn, rem2pi_up_nan x hn]
    exact ⟨hn, hn⟩
  · rw [rem2pi_down_infinite x hn hi, rem2pi_up_infinite x hn hi]
    constructor <;> decide

/-- The full downward interval result for inputs in the source's positive fast interval. -/
theorem rem2pi_down_fast_range (x : FV .f64)
    (hf : isfinite_IEEEFloat x = true)
    (hl : le_float (zero_float .f64) x = true)
    (hu : lt_float x pi4o2.1 = true) :
    isfinite_IEEEFloat (rem2piDown x) = true ∧
      le_IEEEFloat (zero_float .f64) (rem2piDown x) = true ∧
      le_IEEEFloat (rem2piDown x) (Fl.ofBits 0x401921fb54442d18) = true := by
  have hraw : x.isfinite = true := (remIEEEFinite x).symm.trans hf
  have hn : isnan_IEEEFloat x = false := (remIEEEIsnan x).trans (remIEEEFiniteNotNan hraw)
  have hi : isinf_IEEEFloat x = false := (remIEEEInf64 x).trans (remIEEEFiniteNotInf hraw)
  rw [rem2pi_down_small_nonnegative x hn hi hu hl]
  refine ⟨hf, hl, ?_⟩
  change (Fl.lt x pi4o2.1 || Fl.eq x pi4o2.1) = true
  change Fl.lt x pi4o2.1 = true at hu
  rw [hu, Bool.true_or]

/-- The full upward interval result for inputs in the source's negative fast interval. -/
theorem rem2pi_up_fast_range (x : FV .f64)
    (hf : isfinite_IEEEFloat x = true)
    (hl : lt_float (neg_float pi4o2.1) x = true)
    (hu : le_float x (zero_float .f64) = true) :
    isfinite_IEEEFloat (rem2piUp x) = true ∧
      le_IEEEFloat (Fl.ofBits 0xc01921fb54442d18) (rem2piUp x) = true ∧
      le_IEEEFloat (rem2piUp x) (zero_float .f64) = true := by
  have hraw : x.isfinite = true := (remIEEEFinite x).symm.trans hf
  have hn : isnan_IEEEFloat x = false := (remIEEEIsnan x).trans (remIEEEFiniteNotNan hraw)
  have hi : isinf_IEEEFloat x = false := (remIEEEInf64 x).trans (remIEEEFiniteNotInf hraw)
  rw [rem2pi_up_small_nonpositive x hn hi hl hu]
  refine ⟨hf, ?_, hu⟩
  change (Fl.lt (neg_float pi4o2.1) x || Fl.eq (neg_float pi4o2.1) x) = true
  change Fl.lt (neg_float pi4o2.1) x = true at hl
  rw [hl, Bool.true_or]

/-- The frozen universal claim is equivalent to emptiness of its unused machine domain. -/
theorem rem2pi32_range_iff_machine_empty :
    JuliaLean.Proofs.base.special.rem2piArchive20261101.Mod2piFloat32Range ↔
      ¬ Nonempty JuliaLean.Bindings.base.math.Machine := by
  constructor
  · intro claim machineExists
    obtain ⟨machine⟩ := machineExists
    exact rem2pi32_range_counterexample_for_machine machine claim
  · intro empty machine x
    exact False.elim (empty ⟨machine⟩)

theorem rem2pi_error_square (n d m e : Int) :
    (m*d-n*e)*((m*d+n*e)*d-2*n*d*e) =
      d*((m*d-n*e)*(m*d-n*e)) := by
  have htwo : 2*n = n+n := by omega
  have hmd : m*d*d = d*(m*d) := by ac_rfl
  have hned : n*e*d = d*(n*e) := by ac_rfl
  have hnde : n*d*e = d*(n*e) := by ac_rfl
  have hb : (m*d+n*e)*d-2*n*d*e = d*(m*d-n*e) := by
    calc
      _ = m*d*d+n*e*d-(n*d*e+n*d*e) := by
        rw [Int.add_mul, htwo, Int.add_mul, Int.add_mul]
      _ = d*(m*d)-d*(n*e) := by rw [hmd, hned, hnde]; omega
      _ = _ := by rw [Int.mul_sub]
  rw [hb]
  ac_rfl

theorem rem2pi_square_nonnegative (a : Int) : 0 ≤ a*a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- Equal computed answers have equal exact-remainder error for every quotient. -/
theorem rem2pi_error_tie (x y : FV .f64) (q : Int)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    NoWorseExactRemainderError x y y q := by
  change 0 < x.toRat.2 ∧ 0 < y.toRat.2 ∧ 0 < y.toRat.2 ∧ _
  refine ⟨remIEEEDenominator x hx, remIEEEDenominator y hy,
    remIEEEDenominator y hy, ?_⟩
  simp only [Int.sub_self, Int.zero_mul]
  exact Int.le_refl 0

/-- Returning the input is optimal in the zero-quotient exact-remainder comparison. -/
theorem rem2pi_identity_error (x z : FV .f64)
    (hx : x.isfinite = true) (hz : z.isfinite = true) :
    NoWorseExactRemainderError x x z 0 := by
  change 0 < x.toRat.2 ∧ 0 < x.toRat.2 ∧ 0 < z.toRat.2 ∧ _
  refine ⟨remIEEEDenominator x hx, remIEEEDenominator x hx,
    remIEEEDenominator z hz, ?_⟩
  simp only [Int.mul_zero, Int.zero_mul, PiLinearNonnegative, ↓reduceIte]
  rw [rem2pi_error_square]
  exact Int.mul_nonneg (Int.ofNat_nonneg _) (rem2pi_square_nonnegative _)

/-- The downward identity interval satisfies the zero-quotient error comparison. -/
theorem rem2pi_down_fast_zero_quotient_error (x z : FV .f64)
    (hx : isfinite_IEEEFloat x = true) (hz : isfinite_IEEEFloat z = true)
    (hl : le_float (zero_float .f64) x = true) (hu : lt_float x pi4o2.1 = true) :
    NoWorseExactRemainderError x (rem2piDown x) z 0 := by
  have hraw := (remIEEEFinite x).symm.trans hx
  have hn := (remIEEEIsnan x).trans (remIEEEFiniteNotNan hraw)
  have hi := (remIEEEInf64 x).trans (remIEEEFiniteNotInf hraw)
  rw [rem2pi_down_small_nonnegative x hn hi hu hl]
  exact rem2pi_identity_error x z hraw ((remIEEEFinite z).symm.trans hz)

/-- The upward identity interval satisfies the zero-quotient error comparison. -/
theorem rem2pi_up_fast_zero_quotient_error (x z : FV .f64)
    (hx : isfinite_IEEEFloat x = true) (hz : isfinite_IEEEFloat z = true)
    (hl : lt_float (neg_float pi4o2.1) x = true) (hu : le_float x (zero_float .f64) = true) :
    NoWorseExactRemainderError x (rem2piUp x) z 0 := by
  have hraw := (remIEEEFinite x).symm.trans hx
  have hn := (remIEEEIsnan x).trans (remIEEEFiniteNotNan hraw)
  have hi := (remIEEEInf64 x).trans (remIEEEFiniteNotInf hraw)
  rw [rem2pi_up_small_nonpositive x hn hi hl hu]
  exact rem2pi_identity_error x z hraw ((remIEEEFinite z).symm.trans hz)

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.Proofs.base.special.rem2pi

open JuliaLean.Registry
def entries : List Entry := [
  { id := "mathfuncs-rem2pi-float32-range-v2", juliaFile := "base/special/rem2pi.jl",
    juliaFns := ["mod2pi", "rem2pi"],
    statement := "For every Float32 input encoding, mod2pi returns a finite value within [0,2π) on finite inputs and returns NaN on nonfinite inputs.",
    source := "base/math.jl:1221-1241; base/special/rem2pi.jl:68-98,133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.rem2piArchive20261101.Mod2piFloat32Range, thm := none,
    notes := "No complete exact refutation was returned: the conditional obstruction needs a certified PiPrimitive/Machine witness. Existing bugs/mathfuncs-mod2pi-ieee-range.yaml and repro/mathfuncs-mod2pi-ieee-range.jl record the identical 0x80000001 input, 0x40c90fdb result, public exact-range promise, release/nightly evidence, and duplicate review. Reuse that evidence; it does not discharge the formal witness." },
  { id := "mathcov-special-rem2pi-l68-v2", juliaFile := "base/special/rem2pi.jl",
    juliaFns := ["rem2pi"],
    statement := "For every Float64 input, rem2pi with RoundDown returns a finite value within [0,2π] on finite inputs and returns NaN on nonfinite inputs.",
    source := "base/special/rem2pi.jl:68-98; base/math.jl:1188-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.rem2piArchive20261101.DownRangeAndNonfinite, thm := none,
    notes := "Only restricted subnormal inputs and conditional finite-input reductions were proved. The full finite-input normal branches and argument-reduction bounds remain open; no complete exact target proof was returned." },
  { id := "mathcov-special-rem2pi-l100-v2", juliaFile := "base/special/rem2pi.jl",
    juliaFns := ["rem2pi"],
    statement := "For every Float64 input, rem2pi with RoundUp returns a finite value within [-2π,0] on finite inputs and returns NaN on nonfinite inputs.",
    source := "base/special/rem2pi.jl:100-132; base/math.jl:1188-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.rem2piArchive20261101.UpRangeAndNonfinite, thm := none,
    notes := "Only restricted subnormal inputs and conditional finite-input reductions were proved. The full finite-input normal branches and argument-reduction bounds remain open; no complete exact target proof was returned." },
  { id := "rem2pi-down-high-precision-remainder", juliaFile := "base/special/rem2pi.jl",
    juliaFns := ["rem2pi", "rem"],
    statement := "For every finite Float64 input, rem2pi with RoundDown returns a finite result whose absolute error from the exact-2π remainder is no greater than ordinary rem with the Float64 approximation to 2π. Nonfinite inputs return NaN.",
    source := "base/special/rem2pi.jl:68-99; base/div.jl:128; base/math.jl:1188-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.rem2piArchive20261101.DownHighPrecisionAccuracy, thm := none,
    notes := "Only restricted subnormal inputs and conditional finite-input reductions were proved. The full finite-input normal branches and argument-reduction bounds remain open; no complete exact target proof was returned." },
  { id := "rem2pi-up-high-precision-remainder", juliaFile := "base/special/rem2pi.jl",
    juliaFns := ["rem2pi", "rem"],
    statement := "For every finite Float64 input, rem2pi with RoundUp returns a finite result whose absolute error from the exact-2π remainder is no greater than ordinary rem with the Float64 approximation to 2π. Nonfinite inputs return NaN.",
    source := "base/special/rem2pi.jl:100-132; base/div.jl:129; base/math.jl:1188-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.rem2piArchive20261101.UpHighPrecisionAccuracy, thm := none,
    notes := "Only restricted subnormal inputs and conditional finite-input reductions were proved. The full finite-input normal branches and argument-reduction bounds remain open; no complete exact target proof was returned." }
]

end JuliaLean.Proofs.base.special.rem2pi
