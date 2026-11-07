import JuliaLean.Registry.Types
import JuliaLean.base.special.trig
import JuliaLean.base.float

/-!
Unproved statements submitted for independent review, not approvals or installed repairs.
The three range contracts cover every bit pattern of each source IEEEFloat format.
They state range and exceptional-input obligations only; the complete numerical
accuracy promise remains a separate blocked contract in the inventory.

The case adapters below reconcile two existing format-tag types without changing
any input module. Every arithmetic/classification operation they expose calls the
source-mirrored float model. They contain no assumed laws and no free callbacks.
-/

namespace JuliaLean.Proofs.base.special.trig

open JuliaLean JuliaLean.Promotion

/-- Source `-(x::IEEEFloat)`; adapter between the existing format tags.
Julia source: base/float.jl:485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Lean binding: JuliaLean/base/float.lean:1609 (`neg_IEEEFloat`, using `neg_float`).
-/
def ieeeNeg : (T : FTy) → FV T → FV T
  | .f16, x => JuliaLean.base.float.neg_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.neg_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.neg_IEEEFloat (T := .f64) x

/-- Independent representable endpoint 1 from the existing source float model. -/
def ieeeOne : (T : FTy) → FV T
  | .f16 => JuliaLean.base.float.one_float .f16
  | .f32 => JuliaLean.base.float.one_float .f32
  | .f64 => JuliaLean.base.float.one_float .f64

/-- Source `<=` comparison, preserving each actual IEEE type. -/
def ieeeLe : (T : FTy) → FV T → FV T → Bool
  | .f16, x, y => JuliaLean.base.float.le_IEEEFloat (T := .f16) x y
  | .f32, x, y => JuliaLean.base.float.le_IEEEFloat (T := .f32) x y
  | .f64, x, y => JuliaLean.base.float.le_IEEEFloat (T := .f64) x y

/-- Source `isnan`, preserving each actual IEEE type. -/
def ieeeIsNaN : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f64) x

/-- Source `isinf`, preserving each actual IEEE type. -/
def ieeeIsInf : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f64) x

end JuliaLean.Proofs.base.special.trig

namespace JuliaLean.Proofs.base.special.trigArchive20261101

open JuliaLean.Proofs.base.special.trig
open JuliaLean JuliaLean.Promotion

/-- Sinpi maps every finite IEEE input into [-1,1], maps every NaN to NaN, and throws DomainError exactly for infinite inputs.
Julia source: base/special/trig.jl:934-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/special/trig.jl:926-930 (sine range and documented exceptional inputs); doc/src/base/math.md:113-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SinPiRangeAndSpecial : Prop :=
  ∀ (T : FTy) (x : FV T),
    match JuliaLean.base.special.trig.sinpi T x with
    | .ok r =>
        if ieeeIsNaN T x then ieeeIsNaN T r = true
        else ieeeIsInf T x = false ∧
          ieeeLe T (ieeeNeg T (ieeeOne T)) r = true ∧
          ieeeLe T r (ieeeOne T) = true
    | .error (.domainError _) => ieeeIsInf T x = true
    | .error _ => False

/-- Cospi maps every finite IEEE input into [-1,1], maps every NaN to NaN, and throws DomainError exactly for infinite inputs.
Julia source: base/special/trig.jl:968-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/special/trig.jl:960-964 (cosine range and documented exceptional inputs); doc/src/base/math.md:113-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CosPiRangeAndSpecial : Prop :=
  ∀ (T : FTy) (x : FV T),
    match JuliaLean.base.special.trig.cospi T x with
    | .ok r =>
        if ieeeIsNaN T x then ieeeIsNaN T r = true
        else ieeeIsInf T x = false ∧
          ieeeLe T (ieeeNeg T (ieeeOne T)) r = true ∧
          ieeeLe T r (ieeeOne T) = true
    | .error (.domainError _) => ieeeIsInf T x = true
    | .error _ => False

/-- Sincospi returns two values in [-1,1] for every finite IEEE input, two NaNs for every NaN, and DomainError exactly for infinities.
Julia source: base/special/trig.jl:1005-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/special/trig.jl:993-998 (sine/cosine ranges and documented exceptional inputs); doc/src/base/math.md:113-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SinCosPiRangeAndSpecial : Prop :=
  ∀ (T : FTy) (x : FV T),
    match JuliaLean.base.special.trig.sincospi T x with
    | .ok (s, c) =>
        if ieeeIsNaN T x then ieeeIsNaN T s = true ∧ ieeeIsNaN T c = true
        else ieeeIsInf T x = false ∧
          ieeeLe T (ieeeNeg T (ieeeOne T)) s = true ∧
          ieeeLe T s (ieeeOne T) = true ∧
          ieeeLe T (ieeeNeg T (ieeeOne T)) c = true ∧
          ieeeLe T c (ieeeOne T) = true
    | .error (.domainError _) => ieeeIsInf T x = true
    | .error _ => False

/- `sincosd(::Missing)` is public propagation plumbing (base/special/trig.jl:1547
at f755f49a9e41380d7da126b3c1db9fe7f83dd027): it returns the fixed pair
`(missing, missing)`. A separate equality would only restate the source model
`sincosdMissing`, so this method has no independent registry promise under check 3c. -/

end JuliaLean.Proofs.base.special.trigArchive20261101

namespace JuliaLean.Proofs.base.special.trig

open JuliaLean.Registry

end JuliaLean.Proofs.base.special.trig


namespace JuliaLean.ChatGPT.Batch4.Group21
open JuliaLean JuliaLean.Promotion
open JuliaLean.Proofs.base.special.trig
open JuliaLean.Proofs.base.special.trigArchive20261101

theorem trigWidthPow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem trigMagnitudeLt {f : Fmt} (x : Fl f) :
    x.magnitude < 2 ^ (f.eb + f.sb) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem trigExpFromMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem trigFracFromMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem trigAbsBits {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).toBits = x.magnitude := by
  change x.magnitude % 2 ^ T.fmt.width = x.magnitude
  apply Nat.mod_eq_of_lt
  rw [trigWidthPow]
  have h := trigMagnitudeLt x
  omega

theorem trigAbsMagnitude {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).magnitude = x.magnitude := by
  change (MathCov.FP.abs x).toBits % 2 ^ (T.fmt.eb + T.fmt.sb) = x.magnitude
  rw [trigAbsBits, Nat.mod_eq_of_lt (trigMagnitudeLt x)]

theorem trigAbsFields {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).expField = x.expField ∧
    (MathCov.FP.abs x).frac = x.frac := by
  constructor
  · rw [trigExpFromMagnitude, trigAbsMagnitude, ← trigExpFromMagnitude]
  · rw [trigFracFromMagnitude, trigAbsMagnitude, ← trigFracFromMagnitude]

theorem trigAbsIsNaN {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).isnan = x.isnan := by
  simp only [Fl.isnan, (trigAbsFields x).1, (trigAbsFields x).2]

theorem trigAbsIsInf {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).isinf = x.isinf := by
  simp only [Fl.isinf, (trigAbsFields x).1, (trigAbsFields x).2]

theorem trigAbsIsFinite {T : FTy} (x : FV T) :
    (MathCov.FP.abs x).isfinite = x.isfinite := by
  simp only [Fl.isfinite, (trigAbsFields x).1]

theorem trigNaNNotFinite {f : Fmt} (x : Fl f) (hn : x.isnan = true) :
    x.isfinite = false := by
  by_cases he : x.expField = f.emax
  · simp [Fl.isfinite, he]
  · simp [Fl.isnan, he] at hn

theorem trigInfClassification {f : Fmt} (x : Fl f) (hi : x.isinf = true) :
    x.isnan = false ∧ x.isfinite = false := by
  by_cases he : x.expField = f.emax
  · by_cases hz : x.frac = 0
    · simp [Fl.isnan, Fl.isfinite, he, hz]
    · simp [Fl.isinf, he, hz] at hi
  · simp [Fl.isinf, he] at hi

theorem trigNonfiniteClassification {f : Fmt} (x : Fl f) (hf : x.isfinite = false) :
    x.isnan = true ∨ x.isinf = true := by
  by_cases he : x.expField = f.emax
  · by_cases hz : x.frac = 0 <;> simp [Fl.isnan, Fl.isinf, he, hz]
  · simp [Fl.isfinite, he] at hf

theorem trigIsNaNAdapter (T : FTy) (x : FV T) :
    ieeeIsNaN T x = x.isnan := by
  cases T <;>
    simp [ieeeIsNaN, base.float.isnan_IEEEFloat, base.float.isnan_AbstractFloat,
      base.float.eq_IEEEFloat, base.float.eq_float, C.jlEqFloat, Fl.eq] <;> rfl

/-- Every NaN input follows the NaN-return branch. -/
theorem trigSinPiNaN (T : FTy) (x : FV T) (hn : x.isnan = true) :
    base.special.trig.sinpi T x = .ok (MathCov.FP.abs x) ∧
    ieeeIsNaN T (MathCov.FP.abs x) = true := by
  have hf := trigNaNNotFinite x hn
  constructor
  · simp [base.special.trig.sinpi, trigAbsIsFinite, trigAbsIsNaN, hf, hn]
  · rw [trigIsNaNAdapter, trigAbsIsNaN, hn]

theorem trigCosPiNaN (T : FTy) (x : FV T) (hn : x.isnan = true) :
    base.special.trig.cospi T x = .ok (MathCov.FP.abs x) ∧
    ieeeIsNaN T (MathCov.FP.abs x) = true := by
  have hf := trigNaNNotFinite x hn
  constructor
  · simp [base.special.trig.cospi, trigAbsIsFinite, trigAbsIsNaN, hf, hn]
  · rw [trigIsNaNAdapter, trigAbsIsNaN, hn]

theorem trigSinCosPiNaN (T : FTy) (x : FV T) (hn : x.isnan = true) :
    base.special.trig.sincospi T x = .ok (MathCov.FP.abs x, MathCov.FP.abs x) ∧
    ieeeIsNaN T (MathCov.FP.abs x) = true := by
  have hf := trigNaNNotFinite x hn
  constructor
  · simp [base.special.trig.sincospi, trigAbsIsFinite, trigAbsIsNaN, hf, hn]
  · rw [trigIsNaNAdapter, trigAbsIsNaN, hn]

theorem trigSinPiInfinity (T : FTy) (x : FV T) (hi : x.isinf = true) :
    base.special.trig.sinpi T x = .error (.domainError "sinpi") := by
  obtain ⟨hn, hf⟩ := trigInfClassification x hi
  simp [base.special.trig.sinpi, trigAbsIsFinite, trigAbsIsNaN, hf, hn,
    base.special.trig.finiteDomainError]

theorem trigCosPiInfinity (T : FTy) (x : FV T) (hi : x.isinf = true) :
    base.special.trig.cospi T x = .error (.domainError "cospi") := by
  obtain ⟨hn, hf⟩ := trigInfClassification x hi
  simp [base.special.trig.cospi, trigAbsIsFinite, trigAbsIsNaN, hf, hn,
    base.special.trig.finiteDomainError]

theorem trigSinCosPiInfinity (T : FTy) (x : FV T) (hi : x.isinf = true) :
    base.special.trig.sincospi T x = .error (.domainError "sincospi") := by
  obtain ⟨hn, hf⟩ := trigInfClassification x hi
  simp [base.special.trig.sincospi, trigAbsIsFinite, trigAbsIsNaN, hf, hn,
    base.special.trig.finiteDomainError]

theorem trigFiniteClassification {f : Fmt} (x : Fl f) (hf : x.isfinite = true) :
    x.isnan = false ∧ x.isinf = false := by
  by_cases he : x.expField = f.emax
  · simp [Fl.isfinite, he] at hf
  · simp [Fl.isnan, Fl.isinf, he]

theorem trigInfMagnitude (T : FTy) (x : FV T) :
    (x.magnitude == (Fl.inf false : FV T).toBits) = x.isinf := by
  have hi : (Fl.inf false : FV T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> decide
  rw [hi]
  simp only [Fl.isinf, trigExpFromMagnitude, trigFracFromMagnitude]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq]
  cases T <;>
    simp only [FTy.fmt, half, single, double, Fmt.emax, Nat.reducePow,
      Nat.reduceSub, Nat.reduceMul] <;> omega

theorem trigSinPiFinite (T : FTy) (x : FV T) (hf : x.isfinite = true) :
    ∃ r, base.special.trig.sinpi T x = .ok r := by
  simp only [base.special.trig.sinpi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl⟩

theorem trigCosPiFinite (T : FTy) (x : FV T) (hf : x.isfinite = true) :
    ∃ r, base.special.trig.cospi T x = .ok r := by
  simp only [base.special.trig.cospi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl⟩

theorem trigSinCosPiFinite (T : FTy) (x : FV T) (hf : x.isfinite = true) :
    ∃ r, base.special.trig.sincospi T x = .ok r := by
  simp only [base.special.trig.sincospi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl⟩

/-- The only outstanding sine obligation is the numerical bound on finite inputs. -/
theorem trigCopyZero (T : FTy) (x : FV T) :
    MathCov.FP.copysign (MathCov.FP.zero T) x = MathCov.FP.zero T x.signbit := by
  have hz : (Fl.zero false : FV T).magnitude = 0 := by
    cases T <;> decide
  change Fl.ofBits ((Fl.zero false : FV T).magnitude +
    if x.signbit then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) = Fl.zero x.signbit
  rw [hz, Nat.zero_add]
  rfl

theorem trigZeroBounds (T : FTy) (s : Bool) :
    ieeeLe T (ieeeNeg T (ieeeOne T)) (MathCov.FP.zero T s) = true ∧
    ieeeLe T (MathCov.FP.zero T s) (ieeeOne T) = true := by
  cases T <;> cases s <;> decide

theorem trigOneBounds (T : FTy) :
    ieeeLe T (ieeeNeg T (ieeeOne T)) (JuliaLean.Promotion.one T) = true ∧
    ieeeLe T (JuliaLean.Promotion.one T) (ieeeOne T) = true := by
  cases T <;> decide

theorem trigSinPiLarge (T : FTy) (x : FV T) (hf : x.isfinite = true)
    (hl : MathCov.FP.le (MathCov.Bits.maxintfloat T) (MathCov.FP.abs x) = true) :
    base.special.trig.sinpi T x = .ok (MathCov.FP.zero T x.signbit) := by
  simp only [base.special.trig.sinpi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false, hl, ite_true, trigCopyZero]

theorem trigCosPiLarge (T : FTy) (x : FV T) (hf : x.isfinite = true)
    (hl : MathCov.FP.le (MathCov.Bits.maxintfloat T) (MathCov.FP.abs x) = true) :
    base.special.trig.cospi T x = .ok (JuliaLean.Promotion.one T) := by
  simp only [base.special.trig.cospi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false, hl, ite_true]

theorem trigSinCosPiLarge (T : FTy) (x : FV T) (hf : x.isfinite = true)
    (hl : MathCov.FP.le (MathCov.Bits.maxintfloat T) (MathCov.FP.abs x) = true) :
    base.special.trig.sincospi T x =
      .ok (MathCov.FP.zero T x.signbit, JuliaLean.Promotion.one T) := by
  simp only [base.special.trig.sincospi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false, hl, ite_true, trigCopyZero]

/-- After the large-input branch, only the argument-reduction/kernel range remains. -/
theorem trigSinCosPiFiniteComponents (T : FTy) (x : FV T)
    (hf : x.isfinite = true) :
    base.special.trig.sincospi T x = (do
      let s ← base.special.trig.sinpi T x
      let c ← base.special.trig.cospi T x
      pure (s, c)) := by
  simp only [base.special.trig.sincospi, base.special.trig.sinpi,
    base.special.trig.cospi, trigAbsIsFinite, hf, Bool.not_true,
    Bool.false_eq_true, ite_false]
  cases hl : MathCov.FP.le (MathCov.Bits.maxintfloat T) (MathCov.FP.abs x) with
  | true =>
      simp only [hl, ite_true] <;> rfl
  | false =>
      simp only [hl, Bool.false_eq_true, ite_false]
      rcases hr : base.special.trig.piReduce (MathCov.FP.abs x) with ⟨rx, n⟩
      simp only [hr]
      by_cases h0 : n == 0
      · simp only [h0, ite_true] <;> rfl
      · by_cases h1 : n == 1
        · simp only [h0, h1, ite_false, ite_true] <;> rfl
        · by_cases h2 : n == 2
          · simp only [h0, h1, h2, ite_false, ite_true] <;> rfl
          · simp only [h0, h1, h2, ite_false] <;> rfl

end JuliaLean.ChatGPT.Batch4.Group21

namespace JuliaLean.Proofs.base.special.trig

open JuliaLean.Registry

def entries : List Entry := [
  { id := "mathcov-special-trig-l934-v2", juliaFile := "base/special/trig.jl",
    juliaFns := ["sinpi"],
    statement := "For every IEEE format, sinpi returns a value within [-1,1] on finite inputs, propagates NaN, and throws DomainError exactly for infinite inputs.",
    source := "base/special/trig.jl:926-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.trigArchive20261101.SinPiRangeAndSpecial, thm := none, notes := "The universal reduced-sine magnitude bound remains unproved for Float16, Float32 and Float64." },
  { id := "mathcov-special-trig-l968-v2", juliaFile := "base/special/trig.jl",
    juliaFns := ["cospi"],
    statement := "For every IEEE format, cospi returns a value within [-1,1] on finite inputs, propagates NaN, and throws DomainError exactly for infinite inputs.",
    source := "base/special/trig.jl:960-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.trigArchive20261101.CosPiRangeAndSpecial, thm := none, notes := "The universal reduced-cosine magnitude bound remains unproved for Float16, Float32 and Float64." },
  { id := "mathcov-special-trig-l1005-v2", juliaFile := "base/special/trig.jl",
    juliaFns := ["sincospi"],
    statement := "For every IEEE format, sincospi returns two values within [-1,1] on finite inputs, two NaNs on NaN inputs, and throws DomainError exactly for infinite inputs.",
    source := "base/special/trig.jl:993-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.trigArchive20261101.SinCosPiRangeAndSpecial, thm := none, notes := "The paired contract still requires both universal reduced-sine and reduced-cosine magnitude bounds." }
]

end JuliaLean.Proofs.base.special.trig
