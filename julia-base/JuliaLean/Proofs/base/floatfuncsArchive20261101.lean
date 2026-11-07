import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.floatfuncs
import JuliaLean.Bindings.base.floatfuncs
import JuliaLean.Bindings.base.math

namespace JuliaLean.Proofs.base.floatfuncsArchive20261101

open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion (Fl)

/-!
The public subjects below are the installed `base.floatfuncs` definitions.
The existing binding modules supply their concrete callees. No arbitrary
operation record, correctness assumption, or copy of an algorithm is introduced.
IEEE classifications and exact rational observations describe the input/output
bit patterns; `Fl.roundRat` is the independent nearest-even value specification.
The seven approved IDs in history/floatfuncs/floatfuncs.approved are unchanged.
-/

/-- Keep the installed concrete IEEE callees and obtain the promoted operands
from the existing source same-type promotion method. Its two-element list
represents the source tuple, so both projections have statically valid indices.
Julia source: base/promotion.jl:441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def sourceNumberApproxOps (T : FTy) :
    JuliaLean.base.floatfuncs.NumberApproxOps (FV T) (FV T) (FV T) (FV T) :=
  { (JuliaLean.Bindings.base.floatfuncs.numberApproxOps T) with
    promote := fun x y =>
      let promoted := JuliaLean.base.promotion.promoteSameType x y []
      (promoted[0]'(by simp [promoted, JuliaLean.base.promotion.promoteSameType]),
       promoted[1]'(by simp [promoted, JuliaLean.base.promotion.promoteSameType])) }

/-- For every IEEE format and runtime FMA configuration, fma rounds the exact
product-plus-sum once, including signed zero, overflow, underflow, and all
nonfinite input combinations, without constraining NaN payloads.
Julia source: base/floatfuncs.jl:350-361,413-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/floatfuncs.jl:341-348; doc/src/base/math.md:13;
doc/src/manual/integers-and-floating-point-numbers.md:374-435,523-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Registry ID: floatfuncs-fma-exact
-/
def FmaSingleRounding : Prop :=
  ∀ (machine : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y z : FV T),
    let result := JuliaLean.base.floatfuncs.fma_IEEEFloat
      (JuliaLean.Bindings.base.math.floatFmaOps machine) x y z
    let productSign := x.signbit != y.signbit
    if x.isnan || y.isnan || z.isnan then
      result.isnan = true
    else if (x.isinf && y.iszero) || (x.iszero && y.isinf) then
      result.isnan = true
    else if x.isinf || y.isinf then
      if z.isinf && (productSign != z.signbit) then
        result.isnan = true
      else
        result = Fl.inf productSign
    else if z.isinf then
      result = z
    else
      let (xn, xd) := x.toRat
      let (yn, yd) := y.toRat
      let (zn, zd) := z.toRat
      let exactNumerator := xn * yn * (zd : Int) + zn * (xd : Int) * (yd : Int)
      let exactDenominator := xd * yd * zd
      let negativeZero := (x.iszero || y.iszero) && z.iszero && productSign && z.signbit
      result = Fl.roundRat exactNumerator exactDenominator negativeZero

/-- With the documented default absolute-value norm, approximate equality is
symmetric for every IEEE format and all operand/tolerance bit patterns, including
negative or NaN tolerances, signed zeros, infinities, and either NaN policy.
Julia source: base/floatfuncs.jl:230-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/floatfuncs.jl:166-190; doc/src/base/math.md:46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Registry ID: floatfuncs-isapprox-symmetric
-/
def IsapproxIEEESymmetric : Prop :=
  ∀ (T : FTy) (x y atol rtol : FV T) (nans : Bool),
    JuliaLean.base.floatfuncs.isapprox_Number
      (sourceNumberApproxOps T)
      (JuliaLean.base.float.abs_IEEEFloat (T := T))
      (JuliaLean.base.float.abs_IEEEFloat (T := T)) x y atol rtol nans =
    JuliaLean.base.floatfuncs.isapprox_Number
      (sourceNumberApproxOps T)
      (JuliaLean.base.float.abs_IEEEFloat (T := T))
      (JuliaLean.base.float.abs_IEEEFloat (T := T)) y x atol rtol nans

/-!
## Public forwarding methods with no independent registry promise

`isapprox(y; kwargs...)@315` constructs the closure `x -> isapprox(x,y;kwargs...)`.
Its documentation at base/floatfuncs.jl:305-314 describes exactly that forwarding.
Registering closure application equal to the same supplied isapprox callback
would repeat the definition, failing check 3c. The underlying full Number
comparison contract remains separately blocked in floatfuncs.round4.tsv.

`≉(args...; kws...)@323` forwards all arguments and keywords to `≈` and negates
the resulting Boolean. Its documentation at base/floatfuncs.jl:318-322 describes
exactly that forwarding. A registry equality with the negated same callback
would again fail check 3c. This disposition preserves every supported argument
and keyword shape without replacing the underlying comparison contract.

All source/documentation locations above are pinned at
f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/

end JuliaLean.Proofs.base.floatfuncsArchive20261101

namespace JuliaLean.Proofs.base.floatfuncsArchive20261101
open JuliaLean.Registry
end JuliaLean.Proofs.base.floatfuncsArchive20261101

namespace JuliaLean.ChatGPT.Batch4.Group18

open JuliaLean JuliaLean.C JuliaLean.base.float
open JuliaLean.Promotion (Fl Fmt half)

set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

theorem approxWidth (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem approxBitsOfBits {f : Fmt} (v : Nat) :
    (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem approxOfBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem approxExt {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← approxOfBits x, ← approxOfBits y, h]

theorem approxSplit {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := approxWidth f
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

theorem approxExponent {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem approxFraction {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem approxFiniteNotNan {f : Fmt} {x : Fl f} (h : x.isfinite = true) :
    x.isnan = false := by
  simp only [Fl.isfinite, bne_iff_ne] at h
  simp only [Fl.isnan, beq_eq_false_iff_ne.mpr h, Bool.false_and]

theorem approxFiniteNotInf {f : Fmt} {x : Fl f} (h : x.isfinite = true) :
    x.isinf = false := by
  simp only [Fl.isfinite, bne_iff_ne] at h
  simp only [Fl.isinf, beq_eq_false_iff_ne.mpr h, Bool.false_and]

theorem approxFinish {T : FTy} (v : FV T) : finishFloat v = v := by
  unfold finishFloat
  have : (T.fmt == bfloat) = false := by cases T <;> decide
  rw [this]
  rfl

theorem approxIsnan {T : FTy} (x : FV T) : isnan_IEEEFloat x = x.isnan := by
  unfold isnan_IEEEFloat isnan_AbstractFloat eq_IEEEFloat eq_float jlEqFloat Fl.eq
  simp only [beq_self_eq_true, Bool.true_or, Bool.and_true, Bool.and_self, Bool.not_not]

theorem approxNegParts {T : FTy} (x : FV T) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := approxSplit x
  have h2 := approxWidth T.fmt
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hs] at hbx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    unfold Fl.magnitude Fl.signbit
    rw [approxBitsOfBits, Nat.mod_eq_of_lt hlt]
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
    rw [approxBitsOfBits, Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]
    omega

theorem approxNegRat {T : FTy} (x : FV T) :
    (Fl.neg x).isfinite = x.isfinite ∧
    (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
  obtain ⟨hm, hs⟩ := approxNegParts x
  have he : (Fl.neg x).expField = x.expField := by
    rw [approxExponent, hm, ← approxExponent]
  have hfr : (Fl.neg x).frac = x.frac := by
    rw [approxFraction, hm, ← approxFraction]
  have hfn : (Fl.neg x).isfinite = x.isfinite := by
    simp only [Fl.isfinite, he]
  refine ⟨hfn, ?_⟩
  unfold Fl.toRat
  simp only [hfn, he, hfr, hs]
  cases hf : x.isfinite <;> cases hx : x.signbit <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals first | rfl | (split <;> split <;> simp only [Prod.fst, Prod.snd, Int.neg_mul, Int.neg_neg])

theorem approxDenominator {f : Fmt} (x : Fl f) (hf : x.isfinite = true) :
    0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> split
  all_goals first | exact Nat.zero_lt_one | exact Nat.two_pow_pos _

theorem approxSubRat {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    sub_IEEEFloat x y = Fl.roundRat
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int))
      (x.toRat.2 * y.toRat.2) (x.signbit && !y.signbit) := by
  have hn := approxNegRat y
  have hnf : (Fl.neg y).isfinite = true := hn.1.trans hy
  have hsg := (approxNegParts y).2
  unfold sub_IEEEFloat sub_float jlSubFloat floatSub floatAdd
  simp only [approxFinish, approxFiniteNotNan hx, approxFiniteNotNan hy,
    approxFiniteNotNan hnf, approxFiniteNotInf hx, approxFiniteNotInf hy,
    approxFiniteNotInf hnf, Bool.false_eq_true, ↓reduceIte, hn.2, hsg]
  congr 1
  simp only [Int.neg_mul, Int.sub_eq_add_neg]

theorem approxNaNMag {T : FTy} (x : FV T) :
    x.isnan = true ↔ T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := by
  have hM := (approxSplit x).2
  have hE : T.fmt.emax + 1 = 2 ^ T.fmt.eb := by cases T <;> decide
  have hP := Nat.two_pow_pos T.fmt.sb
  have hdiv : x.expField < 2 ^ T.fmt.eb := by
    rw [approxExponent]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hm : x.magnitude = x.expField * 2 ^ T.fmt.sb + x.frac := by
    rw [approxExponent, approxFraction]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod x.magnitude (2 ^ T.fmt.sb)).symm
  have hf : x.frac < 2 ^ T.fmt.sb := by
    rw [approxFraction]
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

theorem approxQuietMag {T : FTy} (x : FV T) :
    (quietFloat x).magnitude = x.magnitude ||| 2 ^ (T.fmt.sb - 1) := by
  have hq : 2 ^ (T.fmt.sb - 1) < 2 ^ (T.fmt.eb + T.fmt.sb) := by
    cases T <;> decide
  have hqw : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width := by
    rw [approxWidth]
    omega
  unfold quietFloat Fl.magnitude
  change ((x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ T.fmt.width) %
    2 ^ (T.fmt.eb + T.fmt.sb) = x.toBits % 2 ^ (T.fmt.eb + T.fmt.sb) ||| 2 ^ (T.fmt.sb - 1)
  have hor : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.width :=
    Nat.or_lt_two_pow x.bits.isLt hqw
  rw [Nat.mod_eq_of_lt hor, Nat.or_mod_two_pow, Nat.mod_eq_of_lt hq]

theorem approxQuietNan {T : FTy} (x : FV T) (hx : x.isnan = true) :
    (quietFloat x).isnan = true := by
  rw [approxNaNMag] at hx ⊢
  rw [approxQuietMag]
  exact Nat.lt_of_lt_of_le hx Nat.left_le_or

theorem approxFinite {T : FTy} (x : FV T) : isfinite_IEEEFloat x = x.isfinite := by
  unfold isfinite_IEEEFloat isfinite_AbstractFloat sub_IEEEFloat sub_float jlSubFloat
  rw [approxIsnan, approxFinish]
  unfold floatSub floatAdd
  obtain ⟨hneg_mag, hneg_sign⟩ := approxNegParts x
  have hneg_exp : (Fl.neg x).expField = x.expField := by
    rw [approxExponent, approxExponent, hneg_mag]
  have hneg_frac : (Fl.neg x).frac = x.frac := by
    rw [approxFraction, approxFraction, hneg_mag]
  have hneg_nan : (Fl.neg x).isnan = x.isnan := by
    unfold Fl.isnan
    rw [hneg_exp, hneg_frac]
  have hneg_inf : (Fl.neg x).isinf = x.isinf := by
    unfold Fl.isinf
    rw [hneg_exp, hneg_frac]
  rw [hneg_nan, hneg_inf, hneg_sign, (approxNegRat x).2]
  have hinv_nan : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
  have hzero_nan : (Fl.zero false : FV T).isnan = false := by cases T <;> decide
  by_cases hfin : x.isfinite = true
  · simp only [hfin, approxFiniteNotNan hfin, approxFiniteNotInf hfin,
      Bool.false_eq_true, ↓reduceIte]
    have hd_pos : 0 < x.toRat.2 := approxDenominator x hfin
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
    · simp only [↓reduceIte, approxQuietNan x hn, Bool.not_true]

theorem approxMagnitudeBits (f : Fmt) (s : Bool) (m : Nat) :
    (Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) + m) : Fl f).magnitude =
      m % 2 ^ (f.eb + f.sb) := by
  unfold Fl.magnitude
  rw [approxBitsOfBits, approxWidth]
  rw [Nat.mod_mod_of_dvd _ (show 2 ^ (f.eb + f.sb) ∣ 2 * 2 ^ (f.eb + f.sb) from
    ⟨2, Nat.mul_comm _ _⟩)]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_mod_left]

theorem approxAbsMagnitude {T : FTy} {x y : FV T} (h : x.magnitude = y.magnitude) :
    abs_IEEEFloat x = abs_IEEEFloat y := by
  have hn : x.isnan = y.isnan := by
    simp only [Fl.isnan, approxExponent, approxFraction, h]
  unfold abs_IEEEFloat abs_float jlAbsFloat unaryFloat
  simp only [approxFinish, hn]
  split <;> simp only [approxQuietMag, h]

theorem approxPackMagnitude {f : Fmt} (s t : Bool) (q : Nat) (k : Int) :
    (Fl.packRounded s q k : Fl f).magnitude =
      (Fl.packRounded t q k : Fl f).magnitude := by
  have hz (u : Bool) : (Fl.zero u : Fl f).magnitude = 0 := by
    simpa only [Fl.zero, Nat.add_zero, Nat.zero_mod] using approxMagnitudeBits f u 0
  have hi (u : Bool) : (Fl.inf u : Fl f).magnitude = (f.emax * 2 ^ f.sb) % 2 ^ (f.eb + f.sb) :=
    approxMagnitudeBits f u _
  unfold Fl.packRounded
  split
  · rw [hz, hz]
  · dsimp only
    split <;> split
    all_goals first | exact (hi _).trans (hi _).symm |
      exact (approxMagnitudeBits f _ _).trans (approxMagnitudeBits f _ _).symm

theorem approxRoundMagnitude {f : Fmt} (n : Int) (d : Nat) (s t : Bool) (hd : d ≠ 0) :
    (Fl.roundRat n d s : Fl f).magnitude = (Fl.roundRat (-n) d t : Fl f).magnitude := by
  have hd' : (d == 0) = false := beq_eq_false_iff_ne.mpr hd
  have hneg : (-n == 0) = (n == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Int.neg_eq_zero]
  unfold Fl.roundRat
  simp only [hd', Bool.false_eq_true, ↓reduceIte, hneg, Int.natAbs_neg]
  split
  · have hz (u : Bool) : (Fl.zero u : Fl f).magnitude = 0 := by
      simpa only [Fl.zero, Nat.add_zero, Nat.zero_mod] using approxMagnitudeBits f u 0
    rw [hz, hz]
  · split
    · exact (approxMagnitudeBits f _ _).trans (approxMagnitudeBits f _ _).symm
    · split
      · have hz (u : Bool) : (Fl.zero u : Fl f).magnitude = 0 := by
          simpa only [Fl.zero, Nat.add_zero, Nat.zero_mod] using approxMagnitudeBits f u 0
        rw [hz, hz]
      · exact approxPackMagnitude _ _ _ _

theorem approxAbsSub {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    abs_IEEEFloat (sub_IEEEFloat x y) = abs_IEEEFloat (sub_IEEEFloat y x) := by
  rw [approxSubRat x y hx hy, approxSubRat y x hy hx,
    Nat.mul_comm y.toRat.2 x.toRat.2]
  rw [show y.toRat.1 * (x.toRat.2 : Int) - x.toRat.1 * (y.toRat.2 : Int) =
      -(x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int)) by omega]
  apply approxAbsMagnitude
  exact approxRoundMagnitude _ _ _ _
    (by have := Nat.mul_pos (approxDenominator x hx) (approxDenominator y hy); omega)

theorem approxSignFlipBits (T : FTy) (s : Bool) (m : Nat) :
    (Fl.ofBits ((if s then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) + m) : FV T).signbit =
      !(Fl.ofBits ((if !s then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) + m) : FV T).signbit := by
  apply Bool.eq_iff_iff.mpr
  cases T <;> cases s <;>
    simp only [Fl.signbit, approxBitsOfBits, FTy.fmt, JuliaLean.Promotion.half,
      JuliaLean.Promotion.single, JuliaLean.Promotion.double, Fmt.width,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.reduceAdd, Nat.reducePow, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals omega

theorem approxPackSignFlip (T : FTy) (s : Bool) (q : Nat) (k : Int) :
    (Fl.packRounded s q k : FV T).signbit =
      !(Fl.packRounded (!s) q k : FV T).signbit := by
  have hz (u : Bool) : (Fl.zero u : FV T).signbit = !(Fl.zero (!u) : FV T).signbit := by
    simpa only [Fl.zero, Nat.add_zero] using approxSignFlipBits T u 0
  unfold Fl.packRounded
  split
  · exact hz s
  · dsimp only
    split <;> split
    all_goals exact approxSignFlipBits T _ _

theorem approxRoundSignFlip (T : FTy) (n : Int) (d : Nat) (s t : Bool)
    (hn : n ≠ 0) (hd : d ≠ 0) :
    (Fl.roundRat n d s : FV T).signbit =
      !(Fl.roundRat (-n) d t : FV T).signbit := by
  have hd' : (d == 0) = false := beq_eq_false_iff_ne.mpr hd
  have hn' : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
  have hneg : (-n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hsign : decide (-n < 0) = !decide (n < 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  unfold Fl.roundRat
  simp only [hd', hn', hneg, Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, hsign]
  split
  · exact approxSignFlipBits T _ _
  · split
    · simpa only [Fl.zero, Nat.add_zero] using approxSignFlipBits T (decide (n < 0)) 0
    · exact approxPackSignFlip T _ _ _

theorem approxAbsParts {T : FTy} (x : FV T) (hx : x.isfinite = true) :
    (abs_IEEEFloat x).magnitude = x.magnitude ∧
    (abs_IEEEFloat x).signbit = false ∧ (abs_IEEEFloat x).isfinite = true := by
  have hn := approxFiniteNotNan hx
  have ha : abs_IEEEFloat x = Fl.ofBits x.magnitude := by
    simp only [abs_IEEEFloat, abs_float, jlAbsFloat, unaryFloat, approxFinish,
      hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hm := (approxSplit x).2
  have hmw : x.magnitude < 2 ^ T.fmt.width := by
    rw [approxWidth]
    omega
  have hmag : (abs_IEEEFloat x).magnitude = x.magnitude := by
    rw [ha]
    change x.magnitude % 2 ^ T.fmt.width % 2 ^ (T.fmt.eb + T.fmt.sb) = _
    rw [Nat.mod_eq_of_lt hmw, Nat.mod_eq_of_lt hm]
  refine ⟨hmag, ?_, ?_⟩
  · rw [ha]
    unfold Fl.signbit
    rw [approxBitsOfBits, Nat.mod_eq_of_lt hmw, decide_eq_false_iff_not]
    omega
  · change ((abs_IEEEFloat x).expField != T.fmt.emax) = true
    rw [approxExponent, hmag, ← approxExponent]
    exact hx

def approxKey (f : Fmt) (m : Nat) : Nat :=
  (m % 2 ^ f.sb + if m / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (m / 2 ^ f.sb - 1)

theorem approxKeyBound (f : Fmt) (m : Nat) :
    approxKey f m < 2 ^ f.sb * 2 ^ (m / 2 ^ f.sb) := by
  have hr := Nat.mod_lt m (Nat.two_pow_pos f.sb)
  unfold approxKey
  generalize m / 2 ^ f.sb = e
  generalize m % 2 ^ f.sb = r at hr
  generalize 2 ^ f.sb = P at *
  cases e with
  | zero => simpa only [Nat.zero_sub, ↓reduceIte, Nat.add_zero, Nat.pow_zero, Nat.mul_one] using hr
  | succ e =>
    have hq := Nat.two_pow_pos e
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.pow_succ]
    have h1 : (r + P) * 2 ^ e < (P + P) * 2 ^ e := (Nat.mul_lt_mul_right hq).2 (by omega)
    have h2 : (P + P) * 2 ^ e = P * (2 ^ e * 2) := by
      rw [← Nat.two_mul, Nat.mul_comm 2 P, Nat.mul_assoc, Nat.mul_comm 2]
    omega

theorem approxKeyLower (f : Fmt) (m : Nat) (h : m / 2 ^ f.sb ≠ 0) :
    2 ^ f.sb * 2 ^ (m / 2 ^ f.sb - 1) ≤ approxKey f m := by
  unfold approxKey
  rw [ite_eq_right h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

theorem approxKeyStrict (f : Fmt) {a b : Nat} (h : a < b) :
    approxKey f a < approxKey f b := by
  have hab : a / 2 ^ f.sb ≤ b / 2 ^ f.sb := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · have h1 := approxKeyBound f a
    have h2 := approxKeyLower f b (Nat.pos_iff_ne_zero.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
    have h3 : 2 ^ (a / 2 ^ f.sb) ≤ 2 ^ (b / 2 ^ f.sb - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_sub_one_of_lt hlt)
    have h4 := Nat.mul_le_mul_left (2 ^ f.sb) h3
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h4 h2)
  · have ha := Nat.div_add_mod a (2 ^ f.sb)
    have hb := Nat.div_add_mod b (2 ^ f.sb)
    rw [heq] at ha
    have hr : a % 2 ^ f.sb < b % 2 ^ f.sb := by omega
    unfold approxKey
    rw [heq]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)

theorem approxKeyInjective (f : Fmt) {a b : Nat} (h : approxKey f a = approxKey f b) : a = b := by
  rcases Nat.lt_trichotomy a b with hl | he | hr
  · have := approxKeyStrict f hl
    omega
  · exact he
  · have := approxKeyStrict f hr
    omega

theorem approxPositiveRatScale {T : FTy} (x : FV T)
    (hx : x.isfinite = true) (hs : x.signbit = false) :
    x.toRat.1 * ((2 ^ (T.fmt.bias + T.fmt.sb - 1) : Nat) : Int) =
      (approxKey T.fmt x.magnitude : Int) * (x.toRat.2 : Int) := by
  have htotal : 1 < T.fmt.bias + T.fmt.sb := by cases T <;> decide
  have hk : approxKey T.fmt x.magnitude =
      (x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb) * 2 ^ (x.expField - 1) := by
    simp only [approxKey, ← approxExponent, ← approxFraction]
  rw [hk]
  unfold Fl.toRat
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hs, beq_iff_eq]
  by_cases he : x.expField = 0
  · have hp : ¬ (1 - (T.fmt.bias : Int) - T.fmt.sb ≥ 0) := by omega
    have hpow : (-(1 - (T.fmt.bias : Int) - T.fmt.sb)).toNat = T.fmt.bias + T.fmt.sb - 1 := by omega
    simp only [he, ↓reduceIte, hp, hpow, Nat.add_zero, Nat.zero_sub, Nat.pow_zero, Nat.mul_one]
  · simp only [he, ↓reduceIte]
    by_cases hp : (x.expField : Int) - T.fmt.bias - T.fmt.sb ≥ 0
    · have hpow : ((x.expField : Int) - T.fmt.bias - T.fmt.sb).toNat +
          (T.fmt.bias + T.fmt.sb - 1) = x.expField - 1 := by omega
      simp only [hp, ↓reduceIte, Int.natCast_one, Int.mul_one]
      have hnat : (x.frac + 2 ^ T.fmt.sb) *
            2 ^ ((x.expField : Int) - T.fmt.bias - T.fmt.sb).toNat *
            2 ^ (T.fmt.bias + T.fmt.sb - 1) =
          (x.frac + 2 ^ T.fmt.sb) * 2 ^ (x.expField - 1) := by
        rw [Nat.mul_assoc, ← Nat.pow_add, hpow]
      simpa only [Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) hnat
    · have hpow : (x.expField - 1) +
          (-((x.expField : Int) - T.fmt.bias - T.fmt.sb)).toNat =
          T.fmt.bias + T.fmt.sb - 1 := by omega
      simp only [hp, ↓reduceIte]
      have hnat : (x.frac + 2 ^ T.fmt.sb) * 2 ^ (T.fmt.bias + T.fmt.sb - 1) =
          ((x.frac + 2 ^ T.fmt.sb) * 2 ^ (x.expField - 1)) *
            2 ^ (-((x.expField : Int) - T.fmt.bias - T.fmt.sb)).toNat := by
        rw [Nat.mul_assoc, ← Nat.pow_add, hpow]
      simpa only [Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) hnat

theorem approxPositiveRatInjective {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true)
    (hsx : x.signbit = false) (hsy : y.signbit = false)
    (hcross : x.toRat.1 * (y.toRat.2 : Int) = y.toRat.1 * (x.toRat.2 : Int)) : x = y := by
  have hxs := approxPositiveRatScale x hx hsx
  have hys := approxPositiveRatScale y hy hsy
  have hk : (approxKey T.fmt x.magnitude : Int) * ((x.toRat.2 : Int) * y.toRat.2) =
      (approxKey T.fmt y.magnitude : Int) * ((x.toRat.2 : Int) * y.toRat.2) := by
    calc
      (approxKey T.fmt x.magnitude : Int) * ((x.toRat.2 : Int) * y.toRat.2) =
          (x.toRat.1 * ((2 ^ (T.fmt.bias + T.fmt.sb - 1) : Nat) : Int)) * y.toRat.2 := by
        rw [← Int.mul_assoc, ← hxs]
      _ = (y.toRat.1 * ((2 ^ (T.fmt.bias + T.fmt.sb - 1) : Nat) : Int)) * x.toRat.2 := by
        rw [Int.mul_right_comm, hcross, Int.mul_right_comm]
      _ = (approxKey T.fmt y.magnitude : Int) * ((x.toRat.2 : Int) * y.toRat.2) := by
        rw [hys]
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hden : ((x.toRat.2 : Int) * y.toRat.2) ≠ 0 := by
    apply Int.ne_of_gt
    exact Int.mul_pos (Int.natCast_pos.mpr (approxDenominator x hx))
      (Int.natCast_pos.mpr (approxDenominator y hy))
  have hk' : approxKey T.fmt x.magnitude = approxKey T.fmt y.magnitude :=
    Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_right hden hk)
  have hm := approxKeyInjective T.fmt hk'
  apply approxExt
  rw [(approxSplit x).1, (approxSplit y).1, hsx, hsy, hm]

theorem approxPositiveMax {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true)
    (hsx : x.signbit = false) (hsy : y.signbit = false) :
    jlMaxFloat x y = jlMaxFloat y x := by
  have hxy : floatSub x y = Fl.roundRat
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int))
      (x.toRat.2 * y.toRat.2) (x.signbit && !y.signbit) := by
    simpa only [sub_IEEEFloat, sub_float, jlSubFloat, approxFinish] using approxSubRat x y hx hy
  have hyx : floatSub y x = Fl.roundRat
      (-(x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int)))
      (x.toRat.2 * y.toRat.2) (y.signbit && !x.signbit) := by
    have h := approxSubRat y x hy hx
    simp only [sub_IEEEFloat, sub_float, jlSubFloat, approxFinish] at h
    rw [Nat.mul_comm y.toRat.2 x.toRat.2] at h
    rw [h]
    congr 1
    omega
  by_cases hn : x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) = 0
  · have heq := approxPositiveRatInjective x y hx hy hsx hsy (by omega)
    rw [heq]
  · have hd : x.toRat.2 * y.toRat.2 ≠ 0 := by
      have := Nat.mul_pos (approxDenominator x hx) (approxDenominator y hy)
      omega
    have hflip : (floatSub y x).signbit = !(floatSub x y).signbit := by
      rw [hxy, hyx]
      have h := congrArg Bool.not (approxRoundSignFlip T _ _
        (x.signbit && !y.signbit) (y.signbit && !x.signbit) hn hd)
      simp only [Bool.not_not] at h
      exact h.symm
    unfold jlMaxFloat
    simp only [approxFinish, approxFiniteNotNan hx, approxFiniteNotNan hy,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte, hflip]
    cases (floatSub x y).signbit <;> rfl

theorem approxMaxAbs {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    jlMaxFloat (abs_IEEEFloat x) (abs_IEEEFloat y) =
      jlMaxFloat (abs_IEEEFloat y) (abs_IEEEFloat x) := by
  exact approxPositiveMax _ _ (approxAbsParts x hx).2.2 (approxAbsParts y hy).2.2
    (approxAbsParts x hx).2.1 (approxAbsParts y hy).2.1

theorem approxEqualSymmetry {T : FTy} (x y : FV T) :
    eq_IEEEFloat x y = eq_IEEEFloat y x := by
  unfold eq_IEEEFloat eq_float jlEqFloat Fl.eq
  rw [Bool.and_comm (!x.isnan) (!y.isnan),
    (show (x.toBits == y.toBits) = (y.toBits == x.toBits) from BEq.comm),
    Bool.and_comm x.iszero y.iszero]

theorem approxExpansion (T : FTy) (x y atol rtol : FV T) (nans : Bool) :
    JuliaLean.base.floatfuncs.isapprox_Number
      (JuliaLean.Proofs.base.floatfuncsArchive20261101.sourceNumberApproxOps T)
      (abs_IEEEFloat (T := T)) (abs_IEEEFloat (T := T)) x y atol rtol nans =
      (eq_IEEEFloat x y ||
        (isfinite_IEEEFloat x && isfinite_IEEEFloat y &&
          le_IEEEFloat (abs_IEEEFloat (sub_IEEEFloat x y))
            (jlMaxFloat atol (mul_IEEEFloat rtol
              (jlMaxFloat (abs_IEEEFloat x) (abs_IEEEFloat y))))) ||
        (nans && isnan_IEEEFloat x && isnan_IEEEFloat y)) := rfl

theorem FloatfuncsIsapproxSymmetricV2_proven :
    JuliaLean.Proofs.base.floatfuncsArchive20261101.IsapproxIEEESymmetric := by
  intro T x y atol rtol nans
  rw [approxExpansion, approxExpansion, approxEqualSymmetry x y,
    approxFinite, approxFinite]
  cases hx : x.isfinite <;> cases hy : y.isfinite
  all_goals simp only [hx, hy, Bool.false_and, Bool.and_false, Bool.true_and,
    Bool.or_false, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  rw [approxAbsSub x y hx hy, approxMaxAbs x y hx hy]

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.ChatGPT.Batch4.Group18

open JuliaLean JuliaLean.C JuliaLean.base.float
open JuliaLean.Promotion (Fl Fmt half)

set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def fmaResultSpec (T : FTy) (x y z result : FV T) : Prop :=
  let productSign := x.signbit != y.signbit
  if x.isnan || y.isnan || z.isnan then result.isnan = true
  else if (x.isinf && y.iszero) || (x.iszero && y.isinf) then result.isnan = true
  else if x.isinf || y.isinf then
    if z.isinf && (productSign != z.signbit) then result.isnan = true
    else result = Fl.inf productSign
  else if z.isinf then result = z
  else
    let (xn, xd) := x.toRat
    let (yn, yd) := y.toRat
    let (zn, zd) := z.toRat
    let numerator := xn * yn * (zd : Int) + zn * (xd : Int) * (yd : Int)
    let denominator := xd * yd * zd
    let negativeZero := (x.iszero || y.iszero) && z.iszero && productSign && z.signbit
    result = Fl.roundRat numerator denominator negativeZero

theorem fmaFiniteOfCases {f : Fmt} (x : Fl f)
    (hn : x.isnan = false) (hi : x.isinf = false) : x.isfinite = true := by
  by_cases he : x.expField = f.emax
  · simp only [Fl.isnan, he, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
    simp only [Fl.isinf, he, hn, beq_self_eq_true, Bool.and_self, Bool.true_eq_false] at hi
  · simp only [Fl.isfinite, bne_iff_ne]
    exact he

theorem fmaRatNumeratorForm {f : Fmt} (x : Fl f) :
    ∃ n : Nat, x.toRat.1 = if x.signbit then -(n : Int) else (n : Int) := by
  by_cases hx : x.isfinite = true
  · let m := x.frac + if x.expField == 0 then 0 else 2 ^ f.sb
    let p : Int := if x.expField == 0 then 1 - (f.bias : Int) - f.sb else (x.expField : Int) - f.bias - f.sb
    refine ⟨if p ≥ 0 then m * 2 ^ p.toNat else m, ?_⟩
    unfold Fl.toRat
    simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (if p ≥ 0 then ((if x.signbit then -(m : Int) else (m : Int)) *
      ((2 ^ p.toNat : Nat) : Int), 1) else (if x.signbit then -(m : Int) else (m : Int),
      2 ^ (-p).toNat)).1 = _
    cases hs : x.signbit <;> split <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul]
  · have hfalse : x.isfinite = false := Bool.eq_false_iff.mpr hx
    refine ⟨0, ?_⟩
    simp only [Fl.toRat, hfalse, Bool.not_false, ↓reduceIte, Int.natCast_zero,
      Int.neg_zero, ite_self]

theorem fmaRatZero {f : Fmt} (x : Fl f) (hx : x.isfinite = true) :
    x.toRat.1 = 0 ↔ x.iszero = true := by
  let m := x.frac + if x.expField == 0 then 0 else 2 ^ f.sb
  let p : Int := if x.expField == 0 then 1 - (f.bias : Int) - f.sb else (x.expField : Int) - f.bias - f.sb
  have hnum : x.toRat.1 = 0 ↔ m = 0 := by
    unfold Fl.toRat
    simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (if p ≥ 0 then ((if x.signbit then -(m : Int) else (m : Int)) *
      ((2 ^ p.toNat : Nat) : Int), 1) else (if x.signbit then -(m : Int) else (m : Int),
      2 ^ (-p).toNat)).1 = 0 ↔ m = 0
    have hp : ((2 ^ p.toNat : Nat) : Int) ≠ 0 := by
      have := Nat.two_pow_pos p.toNat
      omega
    cases hs : x.signbit <;> split <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.mul_eq_zero, hp,
        or_false, Int.neg_eq_zero, Int.natCast_eq_zero]
  rw [hnum]
  change m = 0 ↔ (x.magnitude == 0) = true
  rw [beq_iff_eq]
  have hm : m = 0 ↔ x.frac = 0 ∧ x.expField = 0 := by
    dsimp only [m]
    have hp := Nat.two_pow_pos f.sb
    by_cases he : x.expField = 0
    · simp only [he, beq_self_eq_true, ↓reduceIte, Nat.add_zero, and_true]
    · simp only [beq_eq_false_iff_ne.mpr he, Bool.false_eq_true, ↓reduceIte, he,
        and_false]
      simp only [Nat.add_eq_zero, Nat.ne_of_gt hp, and_false]
  rw [hm, approxFraction, approxExponent]
  have hp := Nat.two_pow_pos f.sb
  have hdiv := Nat.mod_add_div x.magnitude (2 ^ f.sb)
  constructor
  · rintro ⟨hf, he⟩
    rw [hf, he, Nat.mul_zero, Nat.zero_add] at hdiv
    exact hdiv.symm
  · intro hzero
    simp only [hzero, Nat.zero_mod, Nat.zero_div, and_self]

theorem fmaRoundZeroSign (T : FTy) (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true) :
    let n := x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) + z.toRat.1 * (x.toRat.2 : Int) * y.toRat.2
    let d := x.toRat.2 * y.toRat.2 * z.toRat.2
    (Fl.roundRat n d ((x.signbit != y.signbit) && z.signbit) : FV T) =
      Fl.roundRat n d ((x.iszero || y.iszero) && z.iszero && (x.signbit != y.signbit) && z.signbit) := by
  dsimp only
  by_cases hsum : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
      z.toRat.1 * (x.toRat.2 : Int) * y.toRat.2 = 0
  · by_cases hsign : ((x.signbit != y.signbit) && z.signbit) = true
    · have hzsign : z.signbit = true := (Bool.and_eq_true_iff.mp hsign).2
      have hprod : (x.signbit != y.signbit) = true := (Bool.and_eq_true_iff.mp hsign).1
      obtain ⟨nx, hnx⟩ := fmaRatNumeratorForm x
      obtain ⟨ny, hny⟩ := fmaRatNumeratorForm y
      obtain ⟨nz, hnz⟩ := fmaRatNumeratorForm z
      have hxy : x.toRat.1 * y.toRat.1 ≤ 0 := by
        rw [hnx, hny]
        cases hsx : x.signbit <;> cases hsy : y.signbit <;>
          simp only [hsx, hsy, Bool.false_eq_true, ↓reduceIte,
            Bool.false_bne, Bool.true_bne, Bool.not_true,
            Bool.not_false] at hprod ⊢
        all_goals first | contradiction | (
          simp only [Int.neg_mul, Int.mul_neg, ← Int.natCast_mul]
          have := Int.natCast_nonneg (nx * ny)
          omega)
      have hzneg : z.toRat.1 ≤ 0 := by
        rw [hnz, hzsign]
        simp only [↓reduceIte]
        have := Int.natCast_nonneg nz
        omega
      have hdX := Int.natCast_pos.mpr (approxDenominator x hx)
      have hdY := Int.natCast_pos.mpr (approxDenominator y hy)
      have hdZ := Int.natCast_pos.mpr (approxDenominator z hz)
      have ht1 : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hxy (Int.le_of_lt hdZ)
      have ht2 : z.toRat.1 * (x.toRat.2 : Int) * y.toRat.2 ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg
          (Int.mul_nonpos_of_nonpos_of_nonneg hzneg (Int.le_of_lt hdX)) (Int.le_of_lt hdY)
      have ht1z : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) = 0 := by omega
      have ht2z : z.toRat.1 * (x.toRat.2 : Int) * y.toRat.2 = 0 := by omega
      have hxyz : x.toRat.1 = 0 ∨ y.toRat.1 = 0 := by
        have hxy0 : x.toRat.1 * y.toRat.1 = 0 :=
          (Int.mul_eq_zero.mp ht1z).resolve_right (by omega)
        exact Int.mul_eq_zero.mp hxy0
      have hz0 : z.toRat.1 = 0 := by
        have hzdx : z.toRat.1 * (x.toRat.2 : Int) = 0 :=
          (Int.mul_eq_zero.mp ht2z).resolve_right (by omega)
        exact (Int.mul_eq_zero.mp hzdx).resolve_right (by omega)
      have hxyzero : (x.iszero || y.iszero) = true := by
        rcases hxyz with h | h
        · simp only [(fmaRatZero x hx).mp h, Bool.true_or]
        · simp only [(fmaRatZero y hy).mp h, Bool.or_true]
      rw [hxyzero, (fmaRatZero z hz).mp hz0]
      rfl
    · have hfalse : ((x.signbit != y.signbit) && z.signbit) = false := Bool.eq_false_iff.mpr hsign
      have hrequested : ((x.iszero || y.iszero) && z.iszero &&
          (x.signbit != y.signbit) && z.signbit) = false := by
        rw [Bool.and_assoc, Bool.and_assoc, hfalse, Bool.and_false, Bool.and_false]
      rw [hfalse, hrequested]
  · unfold Fl.roundRat
    simp only [beq_eq_false_iff_ne.mpr hsum, Bool.false_eq_true, ↓reduceIte]

theorem fmaRawSpec (T : FTy) (x y z : FV T) :
    fmaResultSpec T x y z (floatFma x y z) := by
  have hinvalid : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
  by_cases hx : x.isnan = true
  · simp only [fmaResultSpec, floatFma, hx, Bool.true_or, ↓reduceIte, approxQuietNan x hx]
  have hnx : x.isnan = false := Bool.eq_false_iff.mpr hx
  by_cases hy : y.isnan = true
  · simp only [fmaResultSpec, floatFma, hnx, hy, Bool.false_or, Bool.true_or,
      Bool.false_eq_true, ↓reduceIte, approxQuietNan y hy]
  have hny : y.isnan = false := Bool.eq_false_iff.mpr hy
  by_cases hz : z.isnan = true
  · simp only [fmaResultSpec, floatFma, hnx, hny, hz, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, approxQuietNan z hz]
  have hnz : z.isnan = false := Bool.eq_false_iff.mpr hz
  have hinvalid_eq : ((x.isinf && y.iszero) || (y.isinf && x.iszero)) =
      ((x.isinf && y.iszero) || (x.iszero && y.isinf)) := by
    rw [Bool.and_comm y.isinf x.iszero]
  by_cases hb : ((x.isinf && y.iszero) || (x.iszero && y.isinf)) = true
  · simp only [fmaResultSpec, floatFma, hnx, hny, hnz, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, hinvalid_eq, hb, hinvalid]
  have hnb : ((x.isinf && y.iszero) || (x.iszero && y.isinf)) = false := Bool.eq_false_iff.mpr hb
  by_cases hi : (x.isinf || y.isinf) = true
  · by_cases hbad : (z.isinf && ((x.signbit != y.signbit) != z.signbit)) = true
    · simp only [fmaResultSpec, floatFma, hnx, hny, hnz, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, hinvalid_eq, hnb, hi, hbad, hinvalid]
    · have hbad0 : (z.isinf && ((x.signbit != y.signbit) != z.signbit)) = false := Bool.eq_false_iff.mpr hbad
      simp only [fmaResultSpec, floatFma, hnx, hny, hnz, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, hinvalid_eq, hnb, hi, hbad0]
  have hni : (x.isinf || y.isinf) = false := Bool.eq_false_iff.mpr hi
  by_cases hzi : z.isinf = true
  · simp only [fmaResultSpec, floatFma, hnx, hny, hnz, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, hinvalid_eq, hnb, hni, hzi]
  have hnzi : z.isinf = false := Bool.eq_false_iff.mpr hzi
  have hnxi : x.isinf = false := by
    cases h : x.isinf <;> simp only [h, Bool.true_or, Bool.true_eq_false] at hni ⊢
  have hnyi : y.isinf = false := by
    cases h : y.isinf <;> simp only [h, Bool.or_true, Bool.true_eq_false] at hni ⊢
  have hxf := fmaFiniteOfCases x hnx hnxi
  have hyf := fmaFiniteOfCases y hny hnyi
  have hzf := fmaFiniteOfCases z hnz hnzi
  simp only [fmaResultSpec, floatFma, hnx, hny, hnz, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, hinvalid_eq, hnb, hni, hnzi]
  simpa only [Int.natCast_mul, Int.mul_assoc] using fmaRoundZeroSign T x y z hxf hyf hzf

theorem fmaResultSwap (T : FTy) (x y z result : FV T) :
    fmaResultSpec T x y z result = fmaResultSpec T y x z result := by
  simp only [fmaResultSpec, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc,
    Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, bne, BEq.comm,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem fmaIntrinsicSpec (T : FTy) (x y z : FV T) :
    fmaResultSpec T x y z (jlFmaFloat x y z) := by
  unfold jlFmaFloat
  rw [approxFinish]
  split
  · rw [fmaResultSwap T x y z]
    exact fmaRawSpec T y x z
  · exact fmaRawSpec T x y z

theorem fmaHardwareSingleRounding (machine : JuliaLean.Bindings.base.math.Machine)
    (T : FTy) (x y z : FV T)
    (hardware : JuliaLean.Bindings.base.math.haveFma machine T = true) :
    fmaResultSpec T x y z
      (JuliaLean.base.floatfuncs.fma_IEEEFloat
        (JuliaLean.Bindings.base.math.floatFmaOps machine) x y z) := by
  simp only [JuliaLean.base.floatfuncs.fma_IEEEFloat,
    JuliaLean.Bindings.base.math.floatFmaOps, hardware, ↓reduceIte]
  exact fmaIntrinsicSpec T x y z

theorem fmaNaNNotFinite {f : Fmt} (x : Fl f) (h : x.isnan = true) : x.isfinite = false := by
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  simp only [Fl.isfinite, h.1, bne_self_eq_false]

theorem fmaInfNotFinite {f : Fmt} (x : Fl f) (h : x.isinf = true) : x.isfinite = false := by
  simp only [Fl.isinf, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Fl.isfinite, h.1, bne_self_eq_false]

theorem fmaInfParts (T : FTy) (s : Bool) :
    (Fl.inf s : FV T).isnan = false ∧ (Fl.inf s : FV T).isinf = true ∧
    (Fl.inf s : FV T).isfinite = false ∧ (Fl.inf s : FV T).signbit = s := by
  cases T <;> cases s <;> decide

theorem fmaAddNaNLeft (T : FTy) (x y : FV T) (h : x.isnan = true) :
    (floatAdd x y).isnan = true := by
  simp only [floatAdd, h, ↓reduceIte, approxQuietNan x h]

theorem fmaAddNaNRight (T : FTy) (x y : FV T) (h : y.isnan = true) :
    (floatAdd x y).isnan = true := by
  by_cases hx : x.isnan = true
  · exact fmaAddNaNLeft T x y hx
  · have hnx : x.isnan = false := Bool.eq_false_iff.mpr hx
    simp only [floatAdd, hnx, Bool.false_eq_true, ↓reduceIte, h, approxQuietNan y h]

theorem fmaAddNonfinite (T : FTy) (x y : FV T)
    (h : x.isfinite = false ∨ y.isfinite = false) : (floatAdd x y).isfinite = false := by
  by_cases hnx : x.isnan = true
  · exact fmaNaNNotFinite _ (fmaAddNaNLeft T x y hnx)
  have hxnan : x.isnan = false := Bool.eq_false_iff.mpr hnx
  by_cases hny : y.isnan = true
  · exact fmaNaNNotFinite _ (fmaAddNaNRight T x y hny)
  have hynan : y.isnan = false := Bool.eq_false_iff.mpr hny
  by_cases hix : x.isinf = true
  · have hinvalid : (invalidFloat T.fmt).isfinite = false := by cases T <;> decide
    simp only [floatAdd, hxnan, hynan, Bool.false_eq_true, ↓reduceIte, hix]
    split
    · exact hinvalid
    · exact fmaInfNotFinite x hix
  have hxinf : x.isinf = false := Bool.eq_false_iff.mpr hix
  by_cases hiy : y.isinf = true
  · simp only [floatAdd, hxnan, hynan, hxinf, Bool.false_eq_true, ↓reduceIte,
      hiy, fmaInfNotFinite y hiy]
  have hyinf : y.isinf = false := Bool.eq_false_iff.mpr hiy
  have hfx := fmaFiniteOfCases x hxnan hxinf
  have hfy := fmaFiniteOfCases y hynan hyinf
  rcases h with h | h <;> simp only [hfx, hfy, Bool.true_eq_false] at h

theorem fmaMulNonfinite (T : FTy) (x y : FV T)
    (h : x.isfinite = false ∨ y.isfinite = false) : (floatMul x y).isfinite = false := by
  by_cases hnx : x.isnan = true
  · simp only [floatMul, hnx, ↓reduceIte]
    exact fmaNaNNotFinite _ (approxQuietNan x hnx)
  have hxnan : x.isnan = false := Bool.eq_false_iff.mpr hnx
  by_cases hny : y.isnan = true
  · simp only [floatMul, hxnan, Bool.false_eq_true, ↓reduceIte, hny]
    exact fmaNaNNotFinite _ (approxQuietNan y hny)
  have hynan : y.isnan = false := Bool.eq_false_iff.mpr hny
  have hinvalid : (invalidFloat T.fmt).isfinite = false := by cases T <;> decide
  have hi : (x.isinf || y.isinf) = true := by
    by_cases hix : x.isinf = true
    · simp only [hix, Bool.true_or]
    have hxinf : x.isinf = false := Bool.eq_false_iff.mpr hix
    by_cases hiy : y.isinf = true
    · simp only [hiy, Bool.or_true]
    have hyinf : y.isinf = false := Bool.eq_false_iff.mpr hiy
    have hfx := fmaFiniteOfCases x hxnan hxinf
    have hfy := fmaFiniteOfCases y hynan hyinf
    rcases h with h | h <;> simp only [hfx, hfy, Bool.true_eq_false] at h
  simp only [floatMul, hxnan, hynan, Bool.false_eq_true, ↓reduceIte, hi]
  split
  · exact hinvalid
  · exact (fmaInfParts T _).2.2.1

theorem fmaNonfiniteProductFlags (T : FTy) (x y : FV T)
    (hi : (x.isinf || y.isinf) = true) : (x.isfinite && y.isfinite) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hf := Bool.and_eq_true_iff.mp h
  rw [approxFiniteNotInf hf.1, approxFiniteNotInf hf.2] at hi
  contradiction

theorem fmaNonfiniteChoiceSpec (T : FTy) (x y z : FV T)
    (h : (x.isfinite && y.isfinite && z.isfinite) = false) :
    fmaResultSpec T x y z
      (if x.isfinite && y.isfinite then z else floatAdd (floatMul x y) z) := by
  have hinvalid : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
  by_cases hx : x.isnan = true
  · simp only [fmaResultSpec, hx, Bool.true_or, ↓reduceIte, fmaNaNNotFinite x hx,
      Bool.false_and, Bool.false_eq_true, floatMul]
    exact fmaAddNaNLeft T _ z (approxQuietNan x hx)
  have hnx : x.isnan = false := Bool.eq_false_iff.mpr hx
  by_cases hy : y.isnan = true
  · simp only [fmaResultSpec, hnx, hy, Bool.false_or, Bool.true_or, ↓reduceIte,
      fmaNaNNotFinite y hy, Bool.and_false, Bool.false_eq_true, floatMul]
    exact fmaAddNaNLeft T _ z (approxQuietNan y hy)
  have hny : y.isnan = false := Bool.eq_false_iff.mpr hy
  by_cases hz : z.isnan = true
  · simp only [fmaResultSpec, hnx, hny, hz, Bool.false_or, ↓reduceIte]
    split
    · exact hz
    · exact fmaAddNaNRight T _ z hz
  have hnz : z.isnan = false := Bool.eq_false_iff.mpr hz
  have hinvalid_eq : ((x.isinf && y.iszero) || (y.isinf && x.iszero)) =
      ((x.isinf && y.iszero) || (x.iszero && y.isinf)) := by
    rw [Bool.and_comm y.isinf x.iszero]
  by_cases hb : ((x.isinf && y.iszero) || (x.iszero && y.isinf)) = true
  · have hiprod : (x.isinf || y.isinf) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb ⊢
      rcases hb with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    have hflags := fmaNonfiniteProductFlags T x y hiprod
    simp only [fmaResultSpec, hnx, hny, hnz, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, hb, hflags, floatMul, hinvalid_eq]
    exact fmaAddNaNLeft T _ z hinvalid
  have hnb : ((x.isinf && y.iszero) || (x.iszero && y.isinf)) = false := Bool.eq_false_iff.mpr hb
  by_cases hi : (x.isinf || y.isinf) = true
  · have hflags := fmaNonfiniteProductFlags T x y hi
    have hresult : (if x.isfinite && y.isfinite then z else floatAdd (floatMul x y) z) =
        floatFma x y z := by
      simp only [hflags, Bool.false_eq_true, ↓reduceIte, floatMul, floatFma, floatAdd,
        hinvalid_eq, hnx, hny, hnz, hnb, hi, (fmaInfParts T _).1,
        (fmaInfParts T _).2.1, (fmaInfParts T _).2.2.2]
    rw [hresult]
    exact fmaRawSpec T x y z
  have hni : (x.isinf || y.isinf) = false := Bool.eq_false_iff.mpr hi
  have hnxi : x.isinf = false := by
    cases h : x.isinf <;> simp only [h, Bool.true_or, Bool.true_eq_false] at hni ⊢
  have hnyi : y.isinf = false := by
    cases h : y.isinf <;> simp only [h, Bool.or_true, Bool.true_eq_false] at hni ⊢
  have hxf := fmaFiniteOfCases x hnx hnxi
  have hyf := fmaFiniteOfCases y hny hnyi
  have hzf : z.isfinite = false := by
    simpa only [hxf, hyf, Bool.true_and] using h
  have hzi : z.isinf = true := by
    by_cases hi : z.isinf = true
    · exact hi
    have hnzi : z.isinf = false := Bool.eq_false_iff.mpr hi
    have := fmaFiniteOfCases z hnz hnzi
    simp only [hzf, Bool.false_eq_true] at this
  simp only [fmaResultSpec, hnx, hny, hnz, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, hnb, hni, hzi, hxf, hyf, Bool.true_and]

theorem fmaTwoMulHigh (ops : JuliaLean.base.floatfuncs.Float64FmaOps) (a b : FV .f64) :
    (JuliaLean.base.floatfuncs.two_mul_Float64 ops a b).1 = ops.mul a b := by
  unfold JuliaLean.base.floatfuncs.two_mul_Float64 JuliaLean.base.floatfuncs.twoMulFloat64Source
  split <;> rfl

theorem fmaEmulated64Fast (ops : JuliaLean.base.floatfuncs.Float64FmaOps) (a b c : FV .f64)
    (hsum : ops.isfinite (ops.add (ops.mul a b) c) = false)
    (hinput : (ops.isfinite c && (ops.isfinite a && ops.isfinite b)) = false) :
    JuliaLean.base.floatfuncs.fma_emulated_Float64 ops a b c =
      if ops.isfinite a && ops.isfinite b then c else ops.add (ops.mul a b) c := by
  generalize hp : JuliaLean.base.floatfuncs.two_mul_Float64 ops a b = pair
  have hh : pair.1 = ops.mul a b := by
    rw [← hp, fmaTwoMulHigh]
  unfold JuliaLean.base.floatfuncs.fma_emulated_Float64
  rw [hp]
  simp only [hh, hsum, Bool.not_false, Bool.true_or, ↓reduceIte, hinput]
  rfl

theorem fmaEmulated64Nonfinite (machine : JuliaLean.Bindings.base.math.Machine)
    (x y z : FV .f64) (h : (x.isfinite && y.isfinite && z.isfinite) = false) :
    fmaResultSpec .f64 x y z
      (JuliaLean.base.floatfuncs.fma_emulated_Float64
        (JuliaLean.Bindings.base.math.fma64Ops machine) x y z) := by
  have hsum : (floatAdd (floatMul x y) z).isfinite = false := by
    by_cases hxy : (x.isfinite && y.isfinite) = true
    · have hzf : z.isfinite = false := by simpa only [hxy, Bool.true_and] using h
      exact fmaAddNonfinite .f64 _ z (Or.inr hzf)
    · have hxy' : (x.isfinite && y.isfinite) = false := Bool.eq_false_iff.mpr hxy
      have hp : x.isfinite = false ∨ y.isfinite = false := by
        cases hx : x.isfinite <;> cases hy : y.isfinite <;>
          simp only [hx, hy, Bool.and_self, Bool.false_and, Bool.and_false,
            Bool.true_eq_false, true_or, or_true] at hxy' ⊢
      exact fmaAddNonfinite .f64 _ z (Or.inl (fmaMulNonfinite .f64 x y hp))
  have hsum' : (JuliaLean.Bindings.base.math.fma64Ops machine).isfinite
      ((JuliaLean.Bindings.base.math.fma64Ops machine).add
        ((JuliaLean.Bindings.base.math.fma64Ops machine).mul x y) z) = false := by
    simpa only [JuliaLean.Bindings.base.math.fma64Ops, add_IEEEFloat, add_float,
      mul_IEEEFloat, mul_float, jlAddFloat, jlMulFloat, approxFinish, approxFinite] using hsum
  have hinput : ((JuliaLean.Bindings.base.math.fma64Ops machine).isfinite z &&
      ((JuliaLean.Bindings.base.math.fma64Ops machine).isfinite x &&
        (JuliaLean.Bindings.base.math.fma64Ops machine).isfinite y)) = false := by
    simpa only [JuliaLean.Bindings.base.math.fma64Ops, approxFinite,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm] using h
  rw [fmaEmulated64Fast _ x y z hsum' hinput]
  simpa only [JuliaLean.Bindings.base.math.fma64Ops, add_IEEEFloat, add_float,
    mul_IEEEFloat, mul_float, jlAddFloat, jlMulFloat, approxFinish, approxFinite]
    using fmaNonfiniteChoiceSpec .f64 x y z h

theorem fmaFloat64Nonfinite (machine : JuliaLean.Bindings.base.math.Machine)
    (x y z : FV .f64) (h : (x.isfinite && y.isfinite && z.isfinite) = false) :
    fmaResultSpec .f64 x y z
      (JuliaLean.base.floatfuncs.fma_IEEEFloat
        (JuliaLean.Bindings.base.math.floatFmaOps machine) x y z) := by
  by_cases hardware : JuliaLean.Bindings.base.math.haveFma machine .f64 = true
  · exact fmaHardwareSingleRounding machine .f64 x y z hardware
  · simp only [JuliaLean.base.floatfuncs.fma_IEEEFloat,
      JuliaLean.Bindings.base.math.floatFmaOps, hardware, ↓reduceIte]
    exact fmaEmulated64Nonfinite machine x y z h

theorem fmaConvertFloatEq (T S : FTy) (x : FV S) :
    convertFloat T x = Fl.convert x := by
  cases T <;> cases S
  all_goals first | rfl | exact (approxOfBits x).symm

theorem fmaConvertNan (T S : FTy) (x : FV S) (hx : x.isnan = true) :
    (Fl.convert x : FV T).isnan = true := by
  by_cases heq : (T.fmt == S.fmt) = true
  · have he : T.fmt = S.fmt := beq_iff_eq.mp heq
    cases T <;> cases S <;> try contradiction
    all_goals simpa only [Fl.convert, beq_self_eq_true, ↓reduceIte, approxOfBits] using hx
  · have hneq : (T.fmt == S.fmt) = false := Bool.eq_false_iff.mpr heq
    let payload := if T.fmt.sb ≥ S.fmt.sb then x.frac * 2 ^ (T.fmt.sb - S.fmt.sb)
      else x.frac / 2 ^ (S.fmt.sb - T.fmt.sb)
    have hpay : payload < 2 ^ T.fmt.sb := by
      dsimp only [payload]
      have hfr : x.frac < 2 ^ S.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
      split
      · rename_i hle
        calc x.frac * 2 ^ (T.fmt.sb-S.fmt.sb) < 2 ^ S.fmt.sb * 2 ^ (T.fmt.sb-S.fmt.sb) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hfr
          _ = 2 ^ T.fmt.sb := by rw [← Nat.pow_add]; congr 1; omega
      · rename_i hlt
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        calc x.frac < 2 ^ S.fmt.sb := hfr
          _ = 2 ^ T.fmt.sb * 2 ^ (S.fmt.sb-T.fmt.sb) := by rw [← Nat.pow_add]; congr 1; omega
    have hhalf : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb := by cases T <;> decide
    have hlor := Nat.or_lt_two_pow hpay hhalf
    change Nat.lor payload (2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.sb at hlor
    have hpos : 0 < Nat.lor payload (2 ^ (T.fmt.sb - 1)) :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) Nat.right_le_or
    have hlimit : T.fmt.emax * 2 ^ T.fmt.sb + 2 ^ T.fmt.sb =
        2 ^ (T.fmt.eb + T.fmt.sb) := by cases T <;> decide
    have hmag : T.fmt.emax * 2 ^ T.fmt.sb + Nat.lor payload (2 ^ (T.fmt.sb - 1)) <
        2 ^ (T.fmt.eb + T.fmt.sb) := by omega
    simp only [Fl.convert, hneq, hx, Bool.false_eq_true, ↓reduceIte]
    rw [approxNaNMag]
    change T.fmt.emax * 2 ^ T.fmt.sb <
      (Fl.ofBits ((if x.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) +
        T.fmt.emax * 2 ^ T.fmt.sb + Nat.lor payload (2 ^ (T.fmt.sb - 1))) : FV T).magnitude
    rw [Nat.add_assoc, approxMagnitudeBits, Nat.mod_eq_of_lt hmag]
    omega

theorem fmaConvertFloatNan (T S : FTy) (x : FV S) (hx : x.isnan = true) :
    (convertFloat T x).isnan = true := by
  rw [fmaConvertFloatEq]
  exact fmaConvertNan T S x hx

theorem fmaSubNaNLeft (T : FTy) (x y : FV T) (h : x.isnan = true) :
    (floatSub x y).isnan = true := by
  simp only [floatSub, h, ↓reduceIte, approxQuietNan x h]

theorem fmaSubNaNRight (T : FTy) (x y : FV T) (h : y.isnan = true) :
    (floatSub x y).isnan = true := by
  by_cases hx : x.isnan = true
  · exact fmaSubNaNLeft T x y hx
  · have hnx : x.isnan = false := Bool.eq_false_iff.mpr hx
    simp only [floatSub, hnx, Bool.false_eq_true, ↓reduceIte, h, approxQuietNan y h]

theorem fmaAbsNaN (T : FTy) (x : FV T) (h : x.isnan = true) :
    (abs_float x).isnan = true := by
  have hbits (y : FV T) : (Fl.ofBits y.magnitude : FV T).magnitude = y.magnitude := by
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      Nat.mod_eq_of_lt (approxSplit y).2] using approxMagnitudeBits T.fmt false y.magnitude
  unfold abs_float jlAbsFloat unaryFloat
  rw [approxFinish]
  split
  · rw [approxNaNMag, hbits]
    exact (approxNaNMag _).mp (approxQuietNan x h)
  · rw [approxNaNMag, hbits]
    exact (approxNaNMag _).mp h

theorem fmaUnsignedToFrom (T : FTy) (b : BitVec T.uintTy.bits) :
    fromJInt (toJInt T.uintTy b) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  simp only [fromJInt, toJInt, hu, Bool.false_eq_true, ↓reduceIte, JInt.wrap,
    wrapInt, BitVec.toNat_ofInt]
  change (b.toNat % 2 ^ T.uintTy.bits) % 2 ^ T.uintTy.bits = b.toNat
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hb]

theorem fmaBitcastRoundtrip (T : FTy) (x : FV T) :
    bitcast_to_float T (bitcast_from_float T.uintTy x) = x := by
  unfold bitcast_to_float bitcast_from_float JuliaLean.base.int.bitcastFloat jlBitcast
  rw [fmaUnsignedToFrom, BitVec.toNat_ofNat]
  have hw : T.uintTy.bits = T.fmt.width := by cases T <;> rfl
  have hb : x.toBits < 2 ^ T.fmt.width := x.bits.isLt
  rw [hw, Nat.mod_eq_of_lt hb, approxOfBits]

theorem fmaUnsignedFromTo (T : FTy) (x : JInt T.uintTy) :
    toJInt T.uintTy (fromJInt x) = x := by
  apply Subtype.ext
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  have hbounds : 0 ≤ x.val ∧ x.val < ((2 ^ T.uintTy.bits : Nat) : Int) := by
    have hx := x.property
    cases T <;> simp only [FTy.uintTy, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
      Bool.false_eq_true, ↓reduceIte] at hx ⊢ <;> omega
  have hm := Int.emod_eq_of_lt hbounds.1 hbounds.2
  simp only [toJInt, fromJInt, hu, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofInt,
    JInt.wrap, hm, Int.toNat_of_nonneg hbounds.1]
  exact wrapInt_of_inRange _ _ x.property

theorem fmaUnsignedAddZero (T : FTy) (x : JInt T.uintTy) :
    JuliaLean.base.int.add_int x (JuliaLean.base.int.lit T.uintTy 0) = x := by
  have hz : fromJInt (JuliaLean.base.int.lit T.uintTy 0) = 0 := by cases T <;> rfl
  unfold JuliaLean.base.int.add_int jlAddInt
  rw [hz]
  have hadd : fromJInt x + (0 : BitVec T.uintTy.bits) = fromJInt x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt (fromJInt x).isLt]
  rw [hadd]
  exact fmaUnsignedFromTo T x


theorem fmaNegClasses (T : FTy) (x : FV T) :
    x.neg.isnan = x.isnan ∧ x.neg.isinf = x.isinf ∧ x.neg.iszero = x.iszero := by
  obtain ⟨hm, hs⟩ := approxNegParts x
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fl.isnan, approxExponent, approxFraction, hm]
  · simp only [Fl.isinf, approxExponent, approxFraction, hm]
  · simp only [Fl.iszero, hm]

theorem fmaZeroParts (T : FTy) (s : Bool) :
    (Fl.zero s : FV T).isnan = false ∧ (Fl.zero s : FV T).isinf = false ∧
    (Fl.zero s : FV T).isfinite = true ∧ (Fl.zero s : FV T).iszero = true ∧
    (Fl.zero s : FV T).signbit = s := by
  cases T <;> cases s <;> decide

def fmaConcreteSmallOps (S : FTy) : JuliaLean.base.floatfuncs.SmallFmaOps S where
  widen := convertFloat (JuliaLean.base.floatfuncs.smallWidenedType S)
  narrow := convertFloat S

theorem fmaRoundExactZero {f : Fmt} (d : Nat) (s : Bool) (hd : 0 < d) :
    (Fl.roundRat 0 d s : Fl f) = Fl.zero s := by
  have hd0 : (d == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp only [Fl.roundRat, hd0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]

theorem fmaZeroNumerator (T : FTy) (s : Bool) : (Fl.zero s : FV T).toRat.1 = 0 :=
  (fmaRatZero (Fl.zero s : FV T) (fmaZeroParts T s).2.2.1).mpr (fmaZeroParts T s).2.2.2.1

theorem fmaZeroRepr (T : FTy) (x : FV T) (h : x.iszero = true) : x = Fl.zero x.signbit := by
  have hm : x.magnitude = 0 := beq_iff_eq.mp h
  have hb := (approxSplit x).1
  rw [hm, Nat.add_zero] at hb
  have hbound : (if x.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) < 2 ^ T.fmt.width := by
    rw [← hb]
    exact x.bits.isLt
  apply approxExt
  unfold Fl.zero
  rw [approxBitsOfBits, Nat.mod_eq_of_lt hbound]
  exact hb

theorem fmaConvertZero (T S : FTy) (s : Bool) :
    convertFloat T (Fl.zero s : FV S) = Fl.zero s := by
  by_cases heq : T = S
  · subst S
    simpa only [fmaConvertFloatEq, Fl.convert, beq_self_eq_true, ↓reduceIte] using
      approxOfBits (Fl.zero s : FV T)
  · have hfmt : (T.fmt == S.fmt) = false := by
      cases T <;> cases S <;> first | contradiction | decide
    simp only [fmaConvertFloatEq, Fl.convert, hfmt, (fmaZeroParts S s).1,
      (fmaZeroParts S s).2.1, Bool.false_eq_true, ↓reduceIte,
      (fmaZeroParts S s).2.2.2.2, fmaZeroNumerator]
    exact fmaRoundExactZero _ s (approxDenominator _ (fmaZeroParts S s).2.2.1)

theorem fmaMulZeros (T : FTy) (sx sy : Bool) :
    floatMul (Fl.zero sx : FV T) (Fl.zero sy) = Fl.zero (sx != sy) := by
  have hd := Nat.mul_pos
    (approxDenominator (Fl.zero sx : FV T) (fmaZeroParts T sx).2.2.1)
    (approxDenominator (Fl.zero sy : FV T) (fmaZeroParts T sy).2.2.1)
  simp only [floatMul, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1,
    (fmaZeroParts T sx).2.1, (fmaZeroParts T sy).2.1,
    (fmaZeroParts T sx).2.2.2.2, (fmaZeroParts T sy).2.2.2.2,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_or,
    fmaZeroNumerator, Int.zero_mul]
  exact fmaRoundExactZero _ _ hd

theorem fmaAddZeros (T : FTy) (sx sy : Bool) :
    floatAdd (Fl.zero sx : FV T) (Fl.zero sy) = Fl.zero (sx && sy) := by
  have hd := Nat.mul_pos
    (approxDenominator (Fl.zero sx : FV T) (fmaZeroParts T sx).2.2.1)
    (approxDenominator (Fl.zero sy : FV T) (fmaZeroParts T sy).2.2.1)
  simp only [floatAdd, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1,
    (fmaZeroParts T sx).2.1, (fmaZeroParts T sy).2.1,
    (fmaZeroParts T sx).2.2.2.2, (fmaZeroParts T sy).2.2.2.2,
    Bool.false_eq_true, ↓reduceIte, fmaZeroNumerator, Int.zero_mul, Int.add_zero]
  exact fmaRoundExactZero _ _ hd

theorem fmaNegZero (T : FTy) (s : Bool) : (Fl.zero s : FV T).neg = Fl.zero (!s) := by
  have hz : (Fl.zero s : FV T).neg.iszero = true :=
    (fmaNegClasses T (Fl.zero s)).2.2.trans (fmaZeroParts T s).2.2.2.1
  rw [fmaZeroRepr T _ hz, (approxNegParts (Fl.zero s : FV T)).2,
    (fmaZeroParts T s).2.2.2.2]

theorem fmaSubZeros (T : FTy) (sx sy : Bool) :
    floatSub (Fl.zero sx : FV T) (Fl.zero sy) = Fl.zero (sx && !sy) := by
  simp only [floatSub, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1,
    Bool.false_eq_true, ↓reduceIte, fmaNegZero, fmaAddZeros]

theorem fmaAbsZeroFloat (T : FTy) (s : Bool) : abs_float (Fl.zero s : FV T) = Fl.zero false := by
  have hm : (Fl.zero s : FV T).magnitude = 0 := beq_iff_eq.mp (fmaZeroParts T s).2.2.2.1
  unfold abs_float jlAbsFloat unaryFloat
  simp only [approxFinish, (fmaZeroParts T s).1, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, hm] <;> rfl

theorem fmaZeroLess (T : FTy) (sx sy : Bool) : lt_float (Fl.zero sx : FV T) (Fl.zero sy) = false := by
  simp only [lt_float, jlLtFloat, Fl.lt, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1,
    (fmaZeroParts T sx).2.2.2.1, (fmaZeroParts T sy).2.2.2.1,
    Bool.false_or, Bool.true_and, ↓reduceIte]

theorem fmaRawZeros (T : FTy) (sx sy sz : Bool) :
    floatFma (Fl.zero sx : FV T) (Fl.zero sy) (Fl.zero sz) = Fl.zero ((sx != sy) && sz) := by
  have hd := Nat.mul_pos (Nat.mul_pos
    (approxDenominator (Fl.zero sx : FV T) (fmaZeroParts T sx).2.2.1)
    (approxDenominator (Fl.zero sy : FV T) (fmaZeroParts T sy).2.2.1))
    (approxDenominator (Fl.zero sz : FV T) (fmaZeroParts T sz).2.2.1)
  simp only [floatFma, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1, (fmaZeroParts T sz).1,
    (fmaZeroParts T sx).2.1, (fmaZeroParts T sy).2.1, (fmaZeroParts T sz).2.1,
    (fmaZeroParts T sx).2.2.2.2, (fmaZeroParts T sy).2.2.2.2, (fmaZeroParts T sz).2.2.2.2,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_or, fmaZeroNumerator,
    Int.zero_mul, Int.add_zero]
  exact fmaRoundExactZero _ _ hd

/-- The requested result predicate specializes to the same signed zero. -/
theorem fmaZeroResultSpec (T : FTy) (sx sy sz : Bool) :
    fmaResultSpec T (Fl.zero sx) (Fl.zero sy) (Fl.zero sz)
      (Fl.zero ((sx != sy) && sz)) := by
  have hd := Nat.mul_pos (Nat.mul_pos
    (approxDenominator (Fl.zero sx : FV T) (fmaZeroParts T sx).2.2.1)
    (approxDenominator (Fl.zero sy : FV T) (fmaZeroParts T sy).2.2.1))
    (approxDenominator (Fl.zero sz : FV T) (fmaZeroParts T sz).2.2.1)
  simpa only [fmaResultSpec, (fmaZeroParts T sx).1, (fmaZeroParts T sy).1,
    (fmaZeroParts T sz).1, (fmaZeroParts T sx).2.1, (fmaZeroParts T sy).2.1,
    (fmaZeroParts T sz).2.1, (fmaZeroParts T sx).2.2.2.1,
    (fmaZeroParts T sy).2.2.2.1, (fmaZeroParts T sz).2.2.2.1,
    (fmaZeroParts T sx).2.2.2.2, (fmaZeroParts T sy).2.2.2.2,
    (fmaZeroParts T sz).2.2.2.2, Bool.false_eq_true, ↓reduceIte,
    Bool.false_or, Bool.false_and, Bool.or_self, Bool.and_self, Bool.true_and,
    fmaZeroNumerator, Int.zero_mul, Int.add_zero] using
      (fmaRoundExactZero (f := T.fmt) _ ((sx != sy) && sz) hd).symm

theorem fmaSmallZeros (T : FTy) (hT : T = .f16 ∨ T = .f32) (sx sy sz : Bool) :
    JuliaLean.base.floatfuncs.fmaEmulatedSmall hT (fmaConcreteSmallOps T)
      (Fl.zero sx) (Fl.zero sy) (Fl.zero sz) = Fl.zero ((sx != sy) && sz) := by
  unfold JuliaLean.base.floatfuncs.fmaEmulatedSmall
  simp only [fmaConcreteSmallOps, fmaConvertZero, mul_float, add_float, sub_float,
    jlMulFloat, jlAddFloat, jlSubFloat, approxFinish, fmaMulZeros, fmaAddZeros,
    fmaSubZeros, fmaAbsZeroFloat, zero_float, fmaZeroLess, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, fmaUnsignedAddZero, fmaBitcastRoundtrip] <;> rfl

/-- The actual small-format emulation satisfies the specification on all signed zeros. -/
theorem fmaSmallZerosSpec (T : FTy) (hT : T = .f16 ∨ T = .f32) (sx sy sz : Bool) :
    fmaResultSpec T (Fl.zero sx) (Fl.zero sy) (Fl.zero sz)
      (JuliaLean.base.floatfuncs.fmaEmulatedSmall hT (fmaConcreteSmallOps T)
        (Fl.zero sx) (Fl.zero sy) (Fl.zero sz)) := by
  rw [fmaSmallZeros T hT sx sy sz]
  exact fmaZeroResultSpec T sx sy sz

theorem fmaEmulated64ZeroFast (ops : JuliaLean.base.floatfuncs.Float64FmaOps)
    (a b c : FV .f64)
    (hsmall : ops.isless (ops.abs (ops.mul a b))
      (ops.nextfloat ops.pow2_neg969 (JuliaLean.base.int.lit .i64 1)) = true)
    (hinput : (ops.isfinite c && (ops.isfinite a && ops.isfinite b)) = true)
    (hzero : (ops.iszero a || ops.iszero b) = true) :
    JuliaLean.base.floatfuncs.fma_emulated_Float64 ops a b c = ops.add (ops.mul a b) c := by
  generalize hp : JuliaLean.base.floatfuncs.two_mul_Float64 ops a b = pair
  have hh : pair.1 = ops.mul a b := by rw [← hp, fmaTwoMulHigh]
  unfold JuliaLean.base.floatfuncs.fma_emulated_Float64
  rw [hp]
  simp only [hh, hsmall, Bool.or_true, Bool.true_or, ↓reduceIte, hinput,
    Bool.not_true, Bool.false_eq_true, hzero] <;> rfl

theorem fmaSourceZero (T : FTy) (s : Bool) : iszero_float (Fl.zero s : FV T) = true := by
  cases T <;> cases s <;> decide


end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.Proofs.base.floatfuncsArchive20261101

open JuliaLean.Registry
def entries : List Entry := [
  { id := "floatfuncs-isapprox-symmetric-v2", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox"],
    statement := "For every Float16, Float32, and Float64 operand pair, same-format absolute and relative tolerances, and NaN policy, isapprox with norm=abs is symmetric, including nonfinite operands.",
    source := "base/floatfuncs.jl:166-190,230-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.floatfuncsArchive20261101.IsapproxIEEESymmetric, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.FloatfuncsIsapproxSymmetricV2_proven },
  { id := "floatfuncs-fma-exact-v2", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["fma"],
    statement := "For every IEEE format, input encoding, and runtime FMA capability, fma rounds the exact product-plus-sum once with the IEEE zero sign and NaN/infinity behavior.",
    source := "base/floatfuncs.jl:342-361,413-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.floatfuncsArchive20261101.FmaSingleRounding, thm := none,
    notes := "No exact full certificate returned. The remaining obligation is finite Float64 software FMA with nonzero multiplicands: unrestricted two_mul decomposition, rescaling, and final single rounding, including overflow and underflow. Partial format/branch lemmas do not settle FmaSingleRounding and are omitted." }
]
end JuliaLean.Proofs.base.floatfuncsArchive20261101
