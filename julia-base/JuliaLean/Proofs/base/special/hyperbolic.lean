import JuliaLean.Registry.Types
import JuliaLean.base.special.hyperbolic
import JuliaLean.base.special.log
import JuliaLean.base.float

/-!
Only unproved public properties. The logarithm record contains the existing
source-mirrored callees, not parameters or assumed laws. The Julia-facing negation,
absolute value and comparison operations use the existing base.float models.
Float observations below
are mathematical observations of the fixed IEEE bit patterns. In particular,
observational equality treats NaNs as NaNs but distinguishes the two signed zeros.
-/

namespace JuliaLean.Proofs.base.special.hyperbolic

open JuliaLean JuliaLean.Promotion

/-- Bind every logarithm callback to its existing source-mirrored definition. -/
def sourceLogCalls : JuliaLean.base.special.hyperbolic.HyperbolicCalls :=
  { log32 := JuliaLean.base.special.log.log_32, log64 := JuliaLean.base.special.log.log_64,
    log1p32 := JuliaLean.base.special.log.log1p32, log1p64 := JuliaLean.base.special.log.log1p64 }

def sameValue : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64 → Prop
  | .f32 x, .f32 y => x = y ∨ (x.isnan = true ∧ y.isnan = true)
  | .f64 x, .f64 y => x = y ∨ (x.isnan = true ∧ y.isnan = true)
  | _, _ => False

def sameFormat : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64 → Prop
  | .f32 _, .f32 _ => True
  | .f64 _, .f64 _ => True
  | _, _ => False

def negValue : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64
  | .f32 x => .f32 (JuliaLean.base.float.neg_IEEEFloat (T := .f32) x)
  | .f64 x => .f64 (JuliaLean.base.float.neg_IEEEFloat (T := .f64) x)

def absValue : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64
  | .f32 x => .f32 (JuliaLean.base.float.abs_IEEEFloat (T := .f32) x)
  | .f64 x => .f64 (JuliaLean.base.float.abs_IEEEFloat (T := .f64) x)

def nanValue : JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x => x.isnan
  | .f64 x => x.isnan

def infValue : JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x => x.isinf
  | .f64 x => x.isinf

def finiteValue : JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x => x.isfinite
  | .f64 x => x.isfinite

def zeroValue : JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x => x.iszero
  | .f64 x => x.iszero

def signValue : JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x => x.signbit
  | .f64 x => x.signbit

def oneLike : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64
  | .f32 _ => .f32 (Fl.ofInt 1)
  | .f64 _ => .f64 (Fl.ofInt 1)

def zeroLike : JuliaLean.base.special.hyperbolic.Float32or64 → Bool → JuliaLean.base.special.hyperbolic.Float32or64
  | .f32 _, s => .f32 (Fl.zero s)
  | .f64 _, s => .f64 (Fl.zero s)

def infLike : JuliaLean.base.special.hyperbolic.Float32or64 → Bool → JuliaLean.base.special.hyperbolic.Float32or64
  | .f32 _, s => .f32 (Fl.inf s)
  | .f64 _, s => .f64 (Fl.inf s)

def leValue : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64 → Prop
  | .f32 x, .f32 y => JuliaLean.base.float.le_IEEEFloat (T := .f32) x y = true
  | .f64 x, .f64 y => JuliaLean.base.float.le_IEEEFloat (T := .f64) x y = true
  | _, _ => False

def ltValue : JuliaLean.base.special.hyperbolic.Float32or64 → JuliaLean.base.special.hyperbolic.Float32or64 → Bool
  | .f32 x, .f32 y => JuliaLean.base.float.lt_IEEEFloat (T := .f32) x y
  | .f64 x, .f64 y => JuliaLean.base.float.lt_IEEEFloat (T := .f64) x y
  | _, _ => false

def domainError (r : Jl JuliaLean.base.special.hyperbolic.Float32or64) : Prop :=
  ∃ message, r = .error (.domainError message)

end JuliaLean.Proofs.base.special.hyperbolic

namespace JuliaLean.Proofs.base.special.hyperbolicArchive20261101

open JuliaLean.Proofs.base.special.hyperbolic
open JuliaLean JuliaLean.Promotion

/-- Tanh is nondecreasing on every ordered pair in each source input format,
 including negative numbers, branch transitions, signed zeros and infinities.
Julia source: base/special/hyperbolic.jl:161-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:326-353; doc/src/base/math.md:124-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TanhMonotone : Prop :=
  ∀ x y : JuliaLean.base.special.hyperbolic.Float32or64, leValue x y → leValue (JuliaLean.base.special.hyperbolic.tanh x) (JuliaLean.base.special.hyperbolic.tanh y)

/-- The inverse hyperbolic functions have their full real domain, NaN, signed
 zero and endpoint classification, including output sign and finiteness.
Julia source: base/special/hyperbolic.jl:183-219,222-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:386-393,488-504; doc/src/base/math.md:130-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def HyperbolicSpecialValues : Prop :=
  ∀ x : JuliaLean.base.special.hyperbolic.Float32or64,
    (∃ y, JuliaLean.base.special.hyperbolic.asinh sourceLogCalls x = .ok y ∧ sameFormat x y ∧
      (nanValue x = true → nanValue y = true) ∧
      (nanValue x = false → signValue y = signValue x) ∧
      (finiteValue x = true → finiteValue y = true) ∧
      (zeroValue x = true → sameValue y x) ∧
      (infValue x = true → sameValue y x)) ∧
    (if nanValue x then
      ∃ y, JuliaLean.base.special.hyperbolic.acosh sourceLogCalls x = .ok y ∧ sameFormat x y ∧ nanValue y = true
    else if ltValue x (oneLike x) then
      domainError (JuliaLean.base.special.hyperbolic.acosh sourceLogCalls x)
    else
      ∃ y, JuliaLean.base.special.hyperbolic.acosh sourceLogCalls x = .ok y ∧ sameFormat x y ∧
        leValue (zeroLike x false) y ∧
        (sameValue x (oneLike x) → sameValue y (zeroLike x false)) ∧
        (finiteValue x = true → finiteValue y = true) ∧
        (infValue x = true → sameValue y (infLike x false))) ∧
    (if nanValue x then
      ∃ y, JuliaLean.base.special.hyperbolic.atanh sourceLogCalls x = .ok y ∧ sameFormat x y ∧ nanValue y = true
    else if ltValue (oneLike x) (absValue x) then
      domainError (JuliaLean.base.special.hyperbolic.atanh sourceLogCalls x)
    else
      ∃ y, JuliaLean.base.special.hyperbolic.atanh sourceLogCalls x = .ok y ∧ sameFormat x y ∧
        signValue y = signValue x ∧
        (zeroValue x = true → sameValue y x) ∧
        (sameValue (absValue x) (oneLike x) → sameValue y (infLike x (signValue x))) ∧
        (ltValue (absValue x) (oneLike x) = true → finiteValue y = true))

/-- Forward hyperbolic results preserve their input format, obey the hyperbolic
 ranges and signs, and handle every NaN, infinity and signed zero input.
Julia source: base/special/hyperbolic.jl:58-88,103-125,161-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:308-353; doc/src/base/math.md:124-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ForwardValueClasses : Prop :=
  (∀ x : JuliaLean.base.special.hyperbolic.Float32or64,
    sameFormat x (JuliaLean.base.special.hyperbolic.sinh x) ∧ sameFormat x (JuliaLean.base.special.hyperbolic.cosh x) ∧ sameFormat x (JuliaLean.base.special.hyperbolic.tanh x) ∧
    (if nanValue x then
      nanValue (JuliaLean.base.special.hyperbolic.sinh x) = true ∧ nanValue (JuliaLean.base.special.hyperbolic.cosh x) = true ∧ nanValue (JuliaLean.base.special.hyperbolic.tanh x) = true
    else
      nanValue (JuliaLean.base.special.hyperbolic.sinh x) = false ∧ signValue (JuliaLean.base.special.hyperbolic.sinh x) = signValue x ∧
      leValue (oneLike x) (JuliaLean.base.special.hyperbolic.cosh x) ∧
      leValue (absValue (JuliaLean.base.special.hyperbolic.tanh x)) (oneLike x) ∧ signValue (JuliaLean.base.special.hyperbolic.tanh x) = signValue x ∧
      (zeroValue x = true → sameValue (JuliaLean.base.special.hyperbolic.sinh x) x ∧ sameValue (JuliaLean.base.special.hyperbolic.tanh x) x ∧
        sameValue (JuliaLean.base.special.hyperbolic.cosh x) (oneLike x)) ∧
      (infValue x = true → sameValue (JuliaLean.base.special.hyperbolic.sinh x) x ∧
        sameValue (JuliaLean.base.special.hyperbolic.cosh x) (infLike x false) ∧
        sameValue (JuliaLean.base.special.hyperbolic.tanh x) (if signValue x then negValue (oneLike x) else oneLike x)))) ∧
  (∀ x : JuliaLean.base.special.hyperbolic.F16,
    if x.isnan then (JuliaLean.base.special.hyperbolic.sinh16 x).isnan = true
    else (JuliaLean.base.special.hyperbolic.sinh16 x).isnan = false ∧ (JuliaLean.base.special.hyperbolic.sinh16 x).signbit = x.signbit ∧
      (x.iszero = true → JuliaLean.base.special.hyperbolic.sinh16 x = x) ∧
      (x.isinf = true → JuliaLean.base.special.hyperbolic.sinh16 x = x))

/-- Reciprocal hyperbolic functions have the correct full-domain symmetries,
 ranges, signs, signed-zero poles, infinite limits and NaN propagation.
Julia source: base/special/hyperbolic.jl:127-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/special/trig.jl:1418-1424; doc/src/base/math.md:136-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ReciprocalValueClasses : Prop :=
  (∀ x : JuliaLean.base.special.hyperbolic.Float32or64,
    sameFormat x (JuliaLean.base.special.hyperbolic.sech x) ∧ sameFormat x (JuliaLean.base.special.hyperbolic.csch x) ∧
    sameValue (JuliaLean.base.special.hyperbolic.sech (negValue x)) (JuliaLean.base.special.hyperbolic.sech x) ∧
    sameValue (JuliaLean.base.special.hyperbolic.csch (negValue x)) (negValue (JuliaLean.base.special.hyperbolic.csch x)) ∧
    (if nanValue x then nanValue (JuliaLean.base.special.hyperbolic.sech x) = true ∧ nanValue (JuliaLean.base.special.hyperbolic.csch x) = true
    else leValue (zeroLike x false) (JuliaLean.base.special.hyperbolic.sech x) ∧ leValue (JuliaLean.base.special.hyperbolic.sech x) (oneLike x) ∧
      nanValue (JuliaLean.base.special.hyperbolic.csch x) = false ∧ signValue (JuliaLean.base.special.hyperbolic.csch x) = signValue x ∧
      (zeroValue x = true → sameValue (JuliaLean.base.special.hyperbolic.sech x) (oneLike x) ∧
        sameValue (JuliaLean.base.special.hyperbolic.csch x) (infLike x (signValue x))) ∧
      (infValue x = true → sameValue (JuliaLean.base.special.hyperbolic.sech x) (zeroLike x false) ∧
        sameValue (JuliaLean.base.special.hyperbolic.csch x) (zeroLike x (signValue x))))) ∧
  (∀ x : JuliaLean.base.special.hyperbolic.F16,
    (JuliaLean.base.special.hyperbolic.sech16 (JuliaLean.base.float.neg_IEEEFloat (T := .f16) x) = JuliaLean.base.special.hyperbolic.sech16 x ∨
      ((JuliaLean.base.special.hyperbolic.sech16 (JuliaLean.base.float.neg_IEEEFloat (T := .f16) x)).isnan = true ∧ (JuliaLean.base.special.hyperbolic.sech16 x).isnan = true)) ∧
    (JuliaLean.base.special.hyperbolic.csch16 (JuliaLean.base.float.neg_IEEEFloat (T := .f16) x) = JuliaLean.base.float.neg_IEEEFloat (T := .f16) (JuliaLean.base.special.hyperbolic.csch16 x) ∨
      ((JuliaLean.base.special.hyperbolic.csch16 (JuliaLean.base.float.neg_IEEEFloat (T := .f16) x)).isnan = true ∧ (JuliaLean.base.special.hyperbolic.csch16 x).isnan = true)) ∧
    (if x.isnan then (JuliaLean.base.special.hyperbolic.sech16 x).isnan = true ∧ (JuliaLean.base.special.hyperbolic.csch16 x).isnan = true
    else JuliaLean.base.float.le_IEEEFloat (T := .f16) (Fl.zero false) (JuliaLean.base.special.hyperbolic.sech16 x) = true ∧
      JuliaLean.base.float.le_IEEEFloat (T := .f16) (JuliaLean.base.special.hyperbolic.sech16 x) (Fl.ofInt 1) = true ∧
      (JuliaLean.base.special.hyperbolic.csch16 x).isnan = false ∧ (JuliaLean.base.special.hyperbolic.csch16 x).signbit = x.signbit ∧
      (x.iszero = true → JuliaLean.base.special.hyperbolic.sech16 x = Fl.ofInt 1 ∧ JuliaLean.base.special.hyperbolic.csch16 x = Fl.inf x.signbit) ∧
      (x.isinf = true → JuliaLean.base.special.hyperbolic.sech16 x = Fl.zero false ∧ JuliaLean.base.special.hyperbolic.csch16 x = Fl.zero x.signbit)))

end JuliaLean.Proofs.base.special.hyperbolicArchive20261101

namespace JuliaLean.Proofs.base.special.hyperbolic

open JuliaLean.Registry

end JuliaLean.Proofs.base.special.hyperbolic

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean.Proofs.base.special.hyperbolic
open JuliaLean.Proofs.base.special.hyperbolicArchive20261101
open JuliaLean.base.special.hyperbolic
open JuliaLean JuliaLean.Promotion

def tanhWitnessLower : Float32or64 := .f32 (Fl.ofBits 0x3dfff085)
def tanhWitnessUpper : Float32or64 := .f32 (Fl.ofBits 0x3dfff086)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tanhWitnessOrdered : leValue tanhWitnessLower tanhWitnessUpper := by
  unfold tanhWitnessLower tanhWitnessUpper leValue
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tanhWitnessDecreases :
    ¬ leValue (JuliaLean.base.special.hyperbolic.tanh tanhWitnessLower)
      (JuliaLean.base.special.hyperbolic.tanh tanhWitnessUpper) := by
  unfold tanhWitnessLower tanhWitnessUpper JuliaLean.base.special.hyperbolic.tanh leValue
  decide

theorem NummiscTanhFloat32NonmonotoneV2_refuted :
    ¬ JuliaLean.Proofs.base.special.hyperbolicArchive20261101.TanhMonotone := by
  intro h
  exact tanhWitnessDecreases (h tanhWitnessLower tanhWitnessUpper tanhWitnessOrdered)

theorem hyperbolicForwardFormats (x : Float32or64) :
    sameFormat x (sinh x) ∧ sameFormat x (cosh x) ∧
      sameFormat x (JuliaLean.base.special.hyperbolic.tanh x) := by
  cases x <;> exact ⟨True.intro, True.intro, True.intro⟩

theorem hyperbolicReciprocalFormats (x : Float32or64) :
    sameFormat x (sech x) ∧ sameFormat x (csch x) := by
  cases x <;> exact ⟨True.intro, True.intro⟩

theorem hyperbolicWrap32Format (x : F32) (r : Jl F32) (y : Float32or64)
    (h : (do let z ← r; pure (Float32or64.f32 z)) = Except.ok y) :
    sameFormat (.f32 x) y := by
  cases r with
  | error e => cases h
  | ok z => cases h; exact True.intro

theorem hyperbolicWrap64Format (x : F64) (r : Jl F64) (y : Float32or64)
    (h : (do let z ← r; pure (Float32or64.f64 z)) = Except.ok y) :
    sameFormat (.f64 x) y := by
  cases r with
  | error e => cases h
  | ok z => cases h; exact True.intro

theorem hyperbolicAsinhFormat (ops : HyperbolicCalls) (x y : Float32or64)
    (h : asinh ops x = .ok y) : sameFormat x y := by
  cases x with
  | f32 x => exact hyperbolicWrap32Format x _ y h
  | f64 x => exact hyperbolicWrap64Format x _ y h

theorem hyperbolicAcoshFormat (ops : HyperbolicCalls) (x y : Float32or64)
    (h : acosh ops x = .ok y) : sameFormat x y := by
  cases x with
  | f32 x => exact hyperbolicWrap32Format x _ y h
  | f64 x => exact hyperbolicWrap64Format x _ y h

theorem hyperbolicAtanhFormat (ops : HyperbolicCalls) (x y : Float32or64)
    (h : atanh ops x = .ok y) : sameFormat x y := by
  cases x with
  | f32 x => exact hyperbolicWrap32Format x _ y h
  | f64 x => exact hyperbolicWrap64Format x _ y h

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

theorem forwardSignMagnitudeNat (u w : Nat) (hw : 0 < w) (hu : u < 2 * w) :
    u = (if w ≤ u then w else 0) + u % w ∧ u % w < w := by
  refine ⟨?_, Nat.mod_lt _ hw⟩
  by_cases h : w ≤ u
  · rw [ite_eq_left h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega), Nat.zero_add]

theorem forwardTogglePartsNat (u w : Nat) (hw : 0 < w) (hu : u < 2 * w) :
    let v := if w ≤ u then u - w else u + w
    v < 2 * w ∧ v % w = u % w ∧ (w ≤ v ↔ u < w) := by
  dsimp only
  by_cases h : w ≤ u
  · simp only [ite_eq_left h]
    have hm : u % w = u - w := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, ?_, by omega⟩
    rw [Nat.mod_eq_of_lt (by omega), hm]
  · simp only [ite_eq_right h]
    refine ⟨by omega, ?_, by omega⟩
    rw [Nat.add_comm, Nat.add_mod_left]

theorem forwardUnsignedPackNat (e p E B : Nat) (he : e < E) (hp : p < B) :
    e * B + p < E * B ∧ (e * B + p) / B = e ∧ (e * B + p) % B = p := by
  have hB : 0 < B := by omega
  have hbound : e * B + p < E * B := by
    have hmul : (e + 1) * B ≤ E * B := Nat.mul_le_mul_right B he
    rw [Nat.succ_mul] at hmul
    omega
  refine ⟨hbound, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hp, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

theorem forwardMagnitudeFieldsNat (u E B : Nat) (hB : 0 < B) (hu : u < E * B) :
    u / B < E ∧ u % B < B ∧ u = (u / B) * B + u % B := by
  refine ⟨(Nat.div_lt_iff_lt_mul hB).mpr hu, Nat.mod_lt _ hB, ?_⟩
  have h := Nat.div_add_mod u B
  rw [Nat.mul_comm] at h
  exact h.symm

theorem forwardSignedPackNat (s : Bool) (e p E B : Nat) (he : e < E) (hp : p < B) :
    let u := (if s then E * B else 0) + (e * B + p)
    u < 2 * (E * B) ∧ u % (E * B) = e * B + p ∧
      u / B % E = e ∧ u % B = p ∧ (E * B ≤ u ↔ s = true) := by
  have hB : 0 < B := by omega
  obtain ⟨hbound, hdiv, hmod⟩ := forwardUnsignedPackNat e p E B he hp
  have hm : ((if s then E * B else 0) + (e * B + p)) % (E * B) = e * B + p := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      Nat.add_mod_left, Nat.mod_eq_of_lt hbound]
  dsimp only
  refine ⟨?_, hm, ?_, ?_, ?_⟩
  · cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega
  · calc
      ((if s then E * B else 0) + (e * B + p)) / B % E =
          (((if s then E * B else 0) + (e * B + p)) % (E * B)) / B := by
            rw [Nat.mul_comm E B, Nat.mod_mul_right_div_self]
      _ = e := by rw [hm, hdiv]
  · calc
      ((if s then E * B else 0) + (e * B + p)) % B =
          (((if s then E * B else 0) + (e * B + p)) % (E * B)) % B := by
            rw [Nat.mul_comm E B, Nat.mod_mul_right_mod]
      _ = p := by rw [hm, hmod]
  · cases s with
    | false =>
      simpa only [Bool.false_eq_true, ite_false, Nat.zero_add] using
        (iff_false_intro (Nat.not_le_of_gt hbound))
    | true =>
      change (E * B ≤ E * B + (e * B + p) ↔ (true = true))
      exact ⟨fun _ => rfl, fun _ => Nat.le_add_right _ _⟩

theorem forwardPayloadWidenNat (p src dst : Nat) (hp : p < 2 ^ src) (h : src ≤ dst) :
    p * 2 ^ (dst - src) < 2 ^ dst := by
  calc
    p * 2 ^ (dst - src) < 2 ^ src * 2 ^ (dst - src) :=
      Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
    _ = 2 ^ dst := by rw [← Nat.pow_add]; congr 1; omega

theorem forwardPayloadNarrowNat (p src dst : Nat) (hp : p < 2 ^ src) (h : dst ≤ src) :
    p / 2 ^ (src - dst) < 2 ^ dst := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  calc
    p < 2 ^ src := hp
    _ = 2 ^ dst * 2 ^ (src - dst) := by rw [← Nat.pow_add]; congr 1; omega

theorem forwardQuietPayloadNat (p k : Nat) (hk : 0 < k) (hp : p < 2 ^ k) :
    0 < Nat.lor p (2 ^ (k - 1)) ∧ Nat.lor p (2 ^ (k - 1)) < 2 ^ k := by
  have hq : 2 ^ (k - 1) < 2 ^ k :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) Nat.right_le_or,
    Nat.or_lt_two_pow hp hq⟩

theorem forwardSetQuietBit64Nat (u : Nat) (hu : u < 2 ^ 64)
    (hp : u % 2 ^ 52 < 2 ^ 51) :
    u + 2 ^ 51 < 2 ^ 64 ∧ (u + 2 ^ 51) / 2 ^ 52 = u / 2 ^ 52 ∧
      (u + 2 ^ 51) % 2 ^ 52 = u % 2 ^ 52 + 2 ^ 51 ∧
      (2 ^ 63 ≤ u + 2 ^ 51 ↔ 2 ^ 63 ≤ u) := by
  have hd := Nat.div_add_mod u (2 ^ 52)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem forwardQuietNaNBits64Nat (u : Nat) (hu : u < 2 ^ 64)
    (he : u / 2 ^ 52 % 2 ^ 11 = 2047) (hp : u % 2 ^ 52 < 2 ^ 51) :
    ((u + 2 ^ 51) % 2 ^ 64) / 2 ^ 52 % 2 ^ 11 = 2047 ∧
      0 < ((u + 2 ^ 51) % 2 ^ 64) % 2 ^ 52 := by
  obtain ⟨hb, hd, hf, _⟩ := forwardSetQuietBit64Nat u hu hp
  rw [Nat.mod_eq_of_lt hb, hd, hf]
  exact ⟨he, by omega⟩

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

theorem recipCoreSignNeg (n : Int) (hn : n ≠ 0) :
    decide (-n < 0) = !decide (n < 0) := by
  by_cases h : n < 0
  · have h' : ¬ -n < 0 := by omega
    simp only [h, h', decide_false, decide_true, Bool.not_true]
  · have h' : -n < 0 := by omega
    simp only [h, h', decide_false, decide_true, Bool.not_false]

theorem recipCoreInvNumeratorNeg (n numerator : Int) (hn : n ≠ 0) :
    (if -n < 0 then -numerator else numerator) =
      -(if n < 0 then -numerator else numerator) := by
  by_cases h : n < 0
  · have h' : ¬ -n < 0 := by omega
    simp only [h, h', ite_true, ite_false, Int.neg_neg]
  · have h' : -n < 0 := by omega
    simp only [h, h', ite_true, ite_false]

theorem recipCoreDivSignNeg (left right : Bool) :
    (left != !right) = !(left != right) := by
  cases left <;> cases right <;> rfl

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

theorem forwardNearestQuotientIntervalNat (n d lo hi : Nat) (hd : 0 < d)
    (hlo : lo * d ≤ n) (hhi : n ≤ hi * d) :
    let q := n / d
    let r := n % d
    let rounded := if decide (d < 2 * r) || (2 * r == d && q % 2 == 1)
      then q + 1 else q
    lo ≤ rounded ∧ rounded ≤ hi := by
  have hlq : lo ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr hlo
  have huq : n / d ≤ hi := Nat.div_le_of_le_mul (by
    rw [Nat.mul_comm d hi]
    exact hhi)
  have hdecomp := Nat.div_add_mod n d
  rw [Nat.mul_comm d (n / d)] at hdecomp
  dsimp only
  cases hg : decide (d < 2 * (n % d)) || (2 * (n % d) == d && (n / d) % 2 == 1) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hlq, huq⟩
  | true =>
    simp only [↓reduceIte]
    have hstrict : n / d < hi := by
      by_cases hq : n / d = hi
      · have hr : n % d = 0 := by
          rw [hq] at hdecomp
          omega
        rcases Bool.or_eq_true_iff.mp hg with hgt | heq
        · have ht : d < 2 * (n % d) := decide_eq_true_iff.mp hgt
          rw [hr, Nat.mul_zero] at ht
          omega
        · have ht : 2 * (n % d) = d :=
            beq_iff_eq.mp (Bool.and_eq_true_iff.mp heq).1
          rw [hr, Nat.mul_zero] at ht
          omega
      · omega
    exact ⟨by omega, by omega⟩

theorem forwardNearestQuotientExactNat (q d : Nat) (hd : 0 < d) :
    let quotient := (q * d) / d
    let remainder := (q * d) % d
    (if decide (d < 2 * remainder) ||
      (2 * remainder == d && quotient % 2 == 1) then quotient + 1 else quotient) = q := by
  have h := forwardNearestQuotientIntervalNat (q * d) d q q hd
    (Nat.le_refl _) (Nat.le_refl _)
  exact Nat.le_antisymm h.2 h.1

theorem forwardNearestQuotientErrorNat (n d : Nat) (hd : 0 < d) :
    let q := n / d
    let r := n % d
    let rounded := if decide (d < 2 * r) || (2 * r == d && q % 2 == 1)
      then q + 1 else q
    2 * n ≤ 2 * (rounded * d) + d ∧ 2 * (rounded * d) ≤ 2 * n + d := by
  have hdecomp := Nat.div_add_mod n d
  rw [Nat.mul_comm d (n / d)] at hdecomp
  have hr := Nat.mod_lt n hd
  dsimp only
  cases hg : decide (d < 2 * (n % d)) || (2 * (n % d) == d && (n / d) % 2 == 1) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hhalf : 2 * (n % d) ≤ d := by
      by_cases h : 2 * (n % d) ≤ d
      · exact h
      · have ht : decide (d < 2 * (n % d)) = true :=
          decide_eq_true_iff.mpr (by omega)
        rw [ht, Bool.true_or] at hg
        cases hg
    constructor <;> omega
  | true =>
    simp only [↓reduceIte, Nat.succ_mul]
    have hhalf : d ≤ 2 * (n % d) := by
      rcases Bool.or_eq_true_iff.mp hg with hgt | heq
      · have ht := decide_eq_true_iff.mp hgt
        omega
      · have ht : 2 * (n % d) = d :=
          beq_iff_eq.mp (Bool.and_eq_true_iff.mp heq).1
        omega
    constructor <;> omega

theorem forwardNormalizedRoundedQuotientNat (n d precision : Nat) (hd : 0 < d)
    (hlo : 2 ^ precision * d ≤ n) (hhi : n < 2 ^ (precision + 1) * d) :
    let q := n / d
    let r := n % d
    let rounded := if decide (d < 2 * r) || (2 * r == d && q % 2 == 1)
      then q + 1 else q
    2 ^ precision ≤ rounded ∧ rounded ≤ 2 ^ (precision + 1) := by
  exact forwardNearestQuotientIntervalNat n d (2 ^ precision) (2 ^ (precision + 1))
    hd hlo (Nat.le_of_lt hhi)

theorem forwardNormalizedCarryNat (q precision : Nat)
    (hlo : 2 ^ precision ≤ q) (hhi : q ≤ 2 ^ (precision + 1)) :
    let mantissa := if q ≥ 2 ^ (precision + 1) then q / 2 else q
    2 ^ precision ≤ mantissa ∧ mantissa < 2 ^ (precision + 1) := by
  have hpow : 2 ^ precision < 2 ^ (precision + 1) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  dsimp only
  split
  next hcarry =>
    have hq : q = 2 ^ (precision + 1) := by omega
    have hdiv : q / 2 = 2 ^ precision := by
      rw [hq, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    rw [hdiv]
    exact ⟨Nat.le_refl _, hpow⟩
  next hcarry =>
    exact ⟨hlo, by omega⟩

theorem forwardFloorLog2PowerNat (a j : Nat) (ha : a ≠ 0) :
    let d := 2 ^ j
    let e : Int := (a.log2 : Int) - (d.log2 : Int)
    let below := if e ≥ 0 then a < d * 2 ^ e.toNat else a * 2 ^ (-e).toNat < d
    (if below then e - 1 else e) = (a.log2 : Int) - (j : Int) := by
  have hlower := Nat.log2_self_le ha
  simp only [Nat.log2_two_pow]
  split
  next hge =>
    have hp : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hnot : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by
      rw [hp]
      exact Nat.not_lt_of_ge hlower
    simp only [hnot, ↓reduceIte]
  next hlt =>
    have hp : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hscaled := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) hlower
    have hnot : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by
      rw [← hp]
      exact Nat.not_lt_of_ge hscaled
    simp only [hnot, ↓reduceIte]

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

theorem forwardLog2ScaleBracketNat (n d shift : Nat) (hn : n ≠ 0) (hd : d ≠ 0)
    (hlog : n.log2 = d.log2 + shift) :
    d * 2 ^ shift < 2 * n ∧ n < 2 * (d * 2 ^ shift) := by
  have hnlo := Nat.log2_self_le hn
  have hdlo := Nat.log2_self_le hd
  have hnhi : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hdhi : d < 2 ^ (d.log2 + 1) := Nat.lt_log2_self
  have hpowlo : 2 ^ (d.log2 + 1) * 2 ^ shift = 2 ^ n.log2 * 2 := by
    rw [← Nat.pow_add, ← Nat.pow_succ]
    congr 1
    omega
  have hpowhi : 2 ^ (n.log2 + 1) = 2 * (2 ^ d.log2 * 2 ^ shift) := by
    rw [hlog, Nat.pow_succ, Nat.pow_add, Nat.mul_comm (2 ^ d.log2 * 2 ^ shift) 2]
  constructor
  · calc
      d * 2 ^ shift < 2 ^ (d.log2 + 1) * 2 ^ shift :=
        Nat.mul_lt_mul_of_pos_right hdhi (Nat.two_pow_pos _)
      _ = 2 ^ n.log2 * 2 := hpowlo
      _ ≤ n * 2 := Nat.mul_le_mul_right 2 hnlo
      _ = 2 * n := Nat.mul_comm n 2
  · calc
      n < 2 ^ (n.log2 + 1) := hnhi
      _ = 2 * (2 ^ d.log2 * 2 ^ shift) := hpowhi
      _ ≤ 2 * (d * 2 ^ shift) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ shift) hdlo)

theorem forwardLog2RatioBracketNat (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    let e : Int := (n.log2 : Int) - (d.log2 : Int)
    if e ≥ 0 then
      d * 2 ^ e.toNat < 2 * n ∧ n < 2 * (d * 2 ^ e.toNat)
    else
      d < 2 * (n * 2 ^ (-e).toNat) ∧ n * 2 ^ (-e).toNat < 2 * d := by
  dsimp only
  split
  next hge =>
    exact forwardLog2ScaleBracketNat n d ((n.log2 : Int) - d.log2).toNat hn hd (by omega)
  next hlt =>
    have h := forwardLog2ScaleBracketNat d n (-((n.log2 : Int) - d.log2)).toNat hd hn (by omega)
    exact ⟨h.2, h.1⟩

theorem forwardFloorLog2NormalizedNat (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    let e : Int := (n.log2 : Int) - (d.log2 : Int)
    let below := if e ≥ 0 then n < d * 2 ^ e.toNat else n * 2 ^ (-e).toNat < d
    let k := if below then e - 1 else e
    if k ≥ 0 then
      d * 2 ^ k.toNat ≤ n ∧ n < 2 * (d * 2 ^ k.toNat)
    else
      d ≤ n * 2 ^ (-k).toNat ∧ n * 2 ^ (-k).toNat < 2 * d := by
  have hbracket := forwardLog2RatioBracketNat n d hn hd
  dsimp only at hbracket ⊢
  generalize (n.log2 : Int) - (d.log2 : Int) = e at hbracket ⊢
  by_cases he : 0 ≤ e
  · have hb : d * 2 ^ e.toNat < 2 * n ∧ n < 2 * (d * 2 ^ e.toNat) := by
      simpa only [he, ↓reduceIte] using hbracket
    simp only [he, ↓reduceIte]
    by_cases hbelow : n < d * 2 ^ e.toNat
    · simp only [hbelow, ↓reduceIte]
      by_cases hk : 0 ≤ e - 1
      · simp only [hk, ↓reduceIte]
        have hshift : e.toNat = (e - 1).toNat + 1 := by omega
        have hp : d * 2 ^ e.toNat = 2 * (d * 2 ^ (e - 1).toNat) := by
          calc
            d * 2 ^ e.toNat = d * (2 ^ (e - 1).toNat * 2) := by
              rw [hshift, Nat.pow_succ]
            _ = (d * 2 ^ (e - 1).toNat) * 2 := (Nat.mul_assoc _ _ _).symm
            _ = 2 * (d * 2 ^ (e - 1).toNat) := Nat.mul_comm _ _
        rw [hp] at hb hbelow
        exact ⟨by omega, hbelow⟩
      · simp only [hk, ↓reduceIte]
        have he0 : e = 0 := by omega
        have heN : e.toNat = 0 := by omega
        have hkN : (-(e - 1)).toNat = 1 := by omega
        have hc : d * 2 ^ e.toNat = d := by
          rw [heN, Nat.pow_zero, Nat.mul_one]
        rw [hc] at hb hbelow
        rw [hkN, Nat.pow_one]
        constructor <;> omega
    · simp only [hbelow, ↓reduceIte, he]
      exact ⟨by omega, hb.2⟩
  · have hb : d < 2 * (n * 2 ^ (-e).toNat) ∧ n * 2 ^ (-e).toNat < 2 * d := by
      simpa only [he, ↓reduceIte] using hbracket
    simp only [he, ↓reduceIte]
    by_cases hbelow : n * 2 ^ (-e).toNat < d
    · simp only [hbelow, ↓reduceIte]
      have hk : ¬ 0 ≤ e - 1 := by omega
      simp only [hk, ↓reduceIte]
      have hshift : (-(e - 1)).toNat = (-e).toNat + 1 := by omega
      have hp : n * 2 ^ (-(e - 1)).toNat = 2 * (n * 2 ^ (-e).toNat) := by
        calc
          n * 2 ^ (-(e - 1)).toNat = n * (2 ^ (-e).toNat * 2) := by
            rw [hshift, Nat.pow_succ]
          _ = (n * 2 ^ (-e).toNat) * 2 := (Nat.mul_assoc _ _ _).symm
          _ = 2 * (n * 2 ^ (-e).toNat) := Nat.mul_comm _ _
      rw [hp]
      constructor <;> omega
    · simp only [hbelow, ↓reduceIte, he]
      exact ⟨by omega, hb.2⟩

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

theorem recipCoreFiniteExponent64 (u : Nat) (hu : u < 2 ^ 64)
    (hpayload : u / 2 ^ 52 % 2048 = 2047 → u % 2 ^ 52 = 0)
    (hinf : u % 2 ^ 63 ≠ 0x7ff0000000000000) :
    u / 2 ^ 52 % 2048 ≠ 2047 := by
  intro he
  have hf := hpayload he
  omega

theorem recipCoreSignificandPositive64 (u : Nat) (hu : u < 2 ^ 64)
    (hzero : u % 2 ^ 63 ≠ 0) :
    0 < u % 2 ^ 52 + (if u / 2 ^ 52 % 2048 == 0 then 0 else 2 ^ 52) := by
  by_cases he : u / 2 ^ 52 % 2048 = 0
  · simp only [he, beq_self_eq_true, ↓reduceIte, Nat.add_zero]
    omega
  · have heb : (u / 2 ^ 52 % 2048 == 0) = false := beq_eq_false_iff_ne.mpr he
    simp only [heb, Bool.false_eq_true, ↓reduceIte]
    omega

theorem recipCoreDecodedNumeratorNeZero (s : Bool) (m : Nat) (p : Int) (hm : m ≠ 0) :
    (if p ≥ 0 then
      (if s then -(m : Int) else (m : Int)) * ((2 ^ p.toNat : Nat) : Int)
     else (if s then -(m : Int) else (m : Int))) ≠ 0 := by
  have hm' : (m : Int) ≠ 0 := Int.ofNat_ne_zero.mpr hm
  have hs : (if s then -(m : Int) else (m : Int)) ≠ 0 := by
    cases s with
    | false => exact hm'
    | true =>
      intro h
      apply hm'
      omega
  have hp : ((2 ^ p.toNat : Nat) : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos _))
  by_cases h : p ≥ 0
  · simpa only [h, ↓reduceIte] using Int.mul_ne_zero hs hp
  · simpa only [h, ↓reduceIte] using hs

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean JuliaLean.Promotion

theorem recipFmtWidth (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem recipOfBitsValue {f : Fmt} (n : Nat) :
    (Fl.ofBits n : Fl f).toBits = n % 2 ^ f.width := rfl

theorem recipOfBitsRoundtrip {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨n, hn⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hn]

theorem recipExtBits {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← recipOfBitsRoundtrip x, ← recipOfBitsRoundtrip y, h]

theorem recipBitsSplit {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
      x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := recipFmtWidth f
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

theorem recipExpFromMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem recipFracFromMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem recipNegParts {f : Fmt} (x : Fl f) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := recipBitsSplit x
  have h2 := recipFmtWidth f
  have hpos : 0 < 2 ^ (f.eb + f.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hs] at hbx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (f.eb + f.sb) < 2 ^ f.width := by omega
    unfold Fl.magnitude Fl.signbit
    rw [recipOfBitsValue, Nat.mod_eq_of_lt hlt]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mod_left]
    · rw [decide_eq_true_iff]
      omega
  · simp only [↓reduceIte, Bool.not_true]
    rw [hs] at hbx
    simp only [↓reduceIte] at hbx
    have hlt : x.toBits - 2 ^ (f.eb + f.sb) < 2 ^ f.width := by omega
    have hsub : x.toBits - 2 ^ (f.eb + f.sb) = x.magnitude := by omega
    unfold Fl.magnitude Fl.signbit
    rw [recipOfBitsValue, Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]
    omega

theorem recipNegClasses {f : Fmt} (x : Fl f) :
    (Fl.neg x).isnan = x.isnan ∧ (Fl.neg x).isinf = x.isinf ∧
      (Fl.neg x).isfinite = x.isfinite ∧ (Fl.neg x).iszero = x.iszero := by
  have hm := (recipNegParts x).1
  simp only [Fl.isnan, Fl.isinf, Fl.isfinite, Fl.iszero,
    recipExpFromMagnitude, recipFracFromMagnitude, hm, and_self]

theorem recipNanNotFinite {f : Fmt} (x : Fl f) (h : x.isnan = true) :
    x.isfinite = false := by
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Fl.isfinite, h.1, bne_self_eq_false]

theorem recipInfNotFinite {f : Fmt} (x : Fl f) (h : x.isinf = true) :
    x.isfinite = false := by
  simp only [Fl.isinf, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Fl.isfinite, h.1, bne_self_eq_false]

theorem recipInfNotNan {f : Fmt} (x : Fl f) (h : x.isinf = true) :
    x.isnan = false := by
  simp only [Fl.isinf, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Fl.isnan, h.1, h.2, beq_self_eq_true, bne_self_eq_false, Bool.and_false]

theorem recipAbsParts {f : Fmt} (x : Fl f) :
    (Fl.ofBits x.magnitude : Fl f).magnitude = x.magnitude ∧
      (Fl.ofBits x.magnitude : Fl f).signbit = false := by
  have hm := (recipBitsSplit x).2
  have hW := recipFmtWidth f
  have hfull : x.magnitude < 2 ^ f.width := by omega
  change (Fl.ofBits x.magnitude : Fl f).toBits % 2 ^ (f.eb + f.sb) = x.magnitude ∧
    decide ((Fl.ofBits x.magnitude : Fl f).toBits ≥ 2 ^ (f.eb + f.sb)) = false
  rw [recipOfBitsValue, Nat.mod_eq_of_lt hfull]
  exact ⟨Nat.mod_eq_of_lt hm, decide_eq_false_iff_not.mpr (by omega)⟩

theorem recipAbsNeg {f : Fmt} (x : Fl f) :
    (Fl.ofBits (Fl.neg x).magnitude : Fl f) = Fl.ofBits x.magnitude := by
  rw [(recipNegParts x).1]

theorem forward_zero_of_sign {f : Fmt} (x : Fl f) (h : x.iszero = true) :
    x = Fl.zero x.signbit := by
  have hm : x.magnitude = 0 := by
    simpa only [Fl.iszero, beq_iff_eq] using h
  apply recipExtBits
  rw [(recipBitsSplit x).1, hm, Nat.add_zero]
  unfold Fl.zero
  rw [recipOfBitsValue, Nat.mod_eq_of_lt]
  have hw := recipFmtWidth f
  have hp := Nat.two_pow_pos (f.eb + f.sb)
  cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem forward_zero_cases {f : Fmt} (x : Fl f) (h : x.iszero = true) :
    x = Fl.zero false ∨ x = Fl.zero true := by
  have hz := forward_zero_of_sign x h
  cases hs : x.signbit
  · exact Or.inl (hs ▸ hz)
  · exact Or.inr (hs ▸ hz)

theorem forward_inf_of_sign {f : Fmt} (x : Fl f) (h : x.isinf = true) :
    x = Fl.inf x.signbit := by
  simp only [Fl.isinf, Bool.and_eq_true, beq_iff_eq] at h
  have hm : x.magnitude = f.emax * 2 ^ f.sb := by
    have hd := Nat.div_add_mod x.magnitude (2 ^ f.sb)
    rw [← recipExpFromMagnitude, ← recipFracFromMagnitude, h.1, h.2,
      Nat.add_zero, Nat.mul_comm] at hd
    exact hd.symm
  have he : f.emax < 2 ^ f.eb := by
    unfold Fmt.emax
    have := Nat.two_pow_pos f.eb
    omega
  have hmag : f.emax * 2 ^ f.sb < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right he (Nat.two_pow_pos _)
  apply recipExtBits
  rw [(recipBitsSplit x).1, hm]
  unfold Fl.inf
  rw [recipOfBitsValue, Nat.mod_eq_of_lt]
  have hw := recipFmtWidth f
  have hp := Nat.two_pow_pos (f.eb + f.sb)
  cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

theorem forward_inf_cases {f : Fmt} (x : Fl f) (h : x.isinf = true) :
    x = Fl.inf false ∨ x = Fl.inf true := by
  have hi := forward_inf_of_sign x h
  cases hs : x.signbit
  · exact Or.inl (hs ▸ hi)
  · exact Or.inr (hs ▸ hi)

def forwardPack {f : Fmt} (s : Bool) (e p : Nat) : Fl f :=
  Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) + (e * 2 ^ f.sb + p))

theorem forwardPackParts {f : Fmt} (s : Bool) (e p : Nat)
    (he : e < 2 ^ f.eb) (hp : p < 2 ^ f.sb) :
    (forwardPack s e p : Fl f).signbit = s ∧
    (forwardPack s e p : Fl f).expField = e ∧
    (forwardPack s e p : Fl f).frac = p := by
  have hP := Nat.two_pow_pos f.sb
  have hM : e * 2 ^ f.sb + p < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    have : (e + 1) * 2 ^ f.sb ≤ 2 ^ f.eb * 2 ^ f.sb :=
      Nat.mul_le_mul_right _ he
    rw [Nat.succ_mul] at this
    omega
  have hw := recipFmtWidth f
  have ht : (forwardPack s e p : Fl f).toBits =
      (if s then 2 ^ (f.eb + f.sb) else 0) + (e * 2 ^ f.sb + p) := by
    unfold forwardPack
    rw [recipOfBitsValue, Nat.mod_eq_of_lt]
    rw [hw]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega
  have hm : (forwardPack s e p : Fl f).magnitude = e * 2 ^ f.sb + p := by
    unfold Fl.magnitude
    rw [ht]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      Nat.add_mod_left, Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_⟩
  · unfold Fl.signbit
    rw [ht]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      decide_eq_false_iff_not, decide_eq_true_iff] <;> omega
  · rw [recipExpFromMagnitude, hm, Nat.add_comm,
      Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hp, Nat.zero_add]
  · rw [recipFracFromMagnitude, hm, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

theorem forwardNanPack {f : Fmt} (s : Bool) (p : Nat)
    (hp0 : 0 < p) (hp : p < 2 ^ f.sb) :
    (Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) +
      f.emax * 2 ^ f.sb + p) : Fl f).isnan = true := by
  have he : f.emax < 2 ^ f.eb := by
    unfold Fmt.emax
    have := Nat.two_pow_pos f.eb
    omega
  have hpack : (Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) +
      f.emax * 2 ^ f.sb + p) : Fl f) = forwardPack s f.emax p := by
    unfold forwardPack
    rw [Nat.add_assoc]
  rw [hpack]
  obtain ⟨_, hex, hfr⟩ := forwardPackParts (f := f) s f.emax p he hp
  simp only [Fl.isnan, hex, hfr, beq_self_eq_true, Bool.true_and, bne_iff_ne]
  omega

theorem forwardConvertNan (S T : FTy) (x : FV T) (hn : x.isnan = true) :
    (Fl.convert x : FV S).isnan = true := by
  by_cases heq : S.fmt = T.fmt
  · have hbits : (Fl.convert x : Fl S.fmt) = Fl.ofBits x.toBits := by
      simp only [Fl.convert, beq_iff_eq.mpr heq, ↓reduceIte]
    rw [hbits, heq, recipOfBitsRoundtrip]
    exact hn
  · have hne : (S.fmt == T.fmt) = false := by
      exact Bool.eq_false_iff.mpr (fun h => heq (beq_iff_eq.mp h))
    have hp : x.frac < 2 ^ T.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hs : 1 ≤ S.fmt.sb := by cases S <;> decide
    have hquiet : 2 ^ (S.fmt.sb - 1) < 2 ^ S.fmt.sb :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    let p := if S.fmt.sb ≥ T.fmt.sb then
        x.frac * 2 ^ (S.fmt.sb - T.fmt.sb)
      else x.frac / 2 ^ (T.fmt.sb - S.fmt.sb)
    have hpbound : p < 2 ^ S.fmt.sb := by
      dsimp only [p]
      split
      next h =>
        calc x.frac * 2 ^ (S.fmt.sb - T.fmt.sb) <
            2 ^ T.fmt.sb * 2 ^ (S.fmt.sb - T.fmt.sb) :=
              Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
          _ = 2 ^ S.fmt.sb := by rw [← Nat.pow_add]; congr 1; omega
      next h =>
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        calc x.frac < 2 ^ T.fmt.sb := hp
          _ = 2 ^ S.fmt.sb * 2 ^ (T.fmt.sb - S.fmt.sb) := by
            rw [← Nat.pow_add]; congr 1; omega
    have hor : Nat.lor p (2 ^ (S.fmt.sb - 1)) < 2 ^ S.fmt.sb :=
      Nat.or_lt_two_pow hpbound hquiet
    have horpos : 0 < Nat.lor p (2 ^ (S.fmt.sb - 1)) :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos _) Nat.right_le_or
    simp only [Fl.convert, hne, Bool.false_eq_true, ↓reduceIte, hn]
    exact forwardNanPack (f := S.fmt) x.signbit _ horpos hor

theorem forwardOf64Nan (x : JuliaLean.Float.F64) :
    (Fl.ofF64 x).isnan = JuliaLean.Float.F64.isnan x := by
  have hx := x.isLt
  simp only [Fl.ofF64, Fl.isnan, Fl.expField, Fl.frac, Fl.toBits,
    Fl.ofBits, double, Fmt.width, Fmt.emax, JuliaLean.Float.F64.toBits,
    JuliaLean.Float.F64.isnan, JuliaLean.Float.F64.exponentField,
    JuliaLean.Float.F64.fraction]
  rw [Nat.mod_eq_of_lt hx]

theorem forwardTo64Nan (x : FV .f64) :
    JuliaLean.Float.F64.isnan (Fl.toF64 x) = x.isnan := by
  let u : Nat := x.toBits
  have hu : u < 2 ^ 64 := x.bits.isLt
  change (u % 2 ^ 64 / 2 ^ 52 % 2048 == 2047 &&
      u % 2 ^ 64 % 2 ^ 52 != 0) =
    (u / 2 ^ 52 % 2048 == 2047 && u % 2 ^ 52 != 0)
  rw [Nat.mod_eq_of_lt hu]

theorem forwardQuiet64Nan (x : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true) :
    JuliaLean.Float.F64.isnan
      (if JuliaLean.Float.F64.fraction x < 2 ^ 51 then
        JuliaLean.Float.F64.ofBits (JuliaLean.Float.F64.toBits x + 2 ^ 51)
       else x) = true := by
  split
  next hsmall =>
    have hx := x.isLt
    have hdiv := Nat.div_add_mod x.toNat (2 ^ 52)
    simp only [JuliaLean.Float.F64.isnan, JuliaLean.Float.F64.exponentField,
      JuliaLean.Float.F64.fraction, JuliaLean.Float.F64.toBits,
      Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
    simp only [JuliaLean.Float.F64.fraction, JuliaLean.Float.F64.toBits] at hsmall
    simp only [JuliaLean.Float.F64.isnan, JuliaLean.Float.F64.exponentField,
      JuliaLean.Float.F64.fraction, JuliaLean.Float.F64.toBits,
      JuliaLean.Float.F64.ofBits, BitVec.toNat_ofNat,
      Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    constructor <;> omega
  next _ => exact h

theorem forwardBinary64Nan (x y fallback : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true) :
    JuliaLean.Float.F64.isnan
      (if JuliaLean.Float.F64.isnan x then
        (if JuliaLean.Float.F64.fraction x < 2 ^ 51 then
          JuliaLean.Float.F64.ofBits (JuliaLean.Float.F64.toBits x + 2 ^ 51) else x)
       else if JuliaLean.Float.F64.isnan y then
        (if JuliaLean.Float.F64.fraction y < 2 ^ 51 then
          JuliaLean.Float.F64.ofBits (JuliaLean.Float.F64.toBits y + 2 ^ 51) else y)
       else fallback) = true := by
  by_cases hx : JuliaLean.Float.F64.isnan x = true
  · simp only [hx, ↓reduceIte]
    exact forwardQuiet64Nan x hx
  · have hxf : JuliaLean.Float.F64.isnan x = false := Bool.eq_false_iff.mpr hx
    have hy : JuliaLean.Float.F64.isnan y = true := h.resolve_left hx
    simp only [hxf, Bool.false_eq_true, ↓reduceIte, hy]
    exact forwardQuiet64Nan y hy

theorem forwardRawAddNan (x y : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true) :
    JuliaLean.Float.F64.isnan (JuliaLean.Float.F64.add x y) = true := by
  exact forwardBinary64Nan x y _ h

theorem forwardRawSubNan (x y : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true) :
    JuliaLean.Float.F64.isnan (JuliaLean.Float.F64.sub x y) = true := by
  exact forwardBinary64Nan x y _ h

theorem forwardRawMulNan (x y : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true) :
    JuliaLean.Float.F64.isnan (JuliaLean.Float.F64.mul x y) = true := by
  exact forwardBinary64Nan x y _ h

theorem forwardRawDivNan (x y : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true) :
    JuliaLean.Float.F64.isnan (JuliaLean.Float.F64.div x y) = true := by
  exact forwardBinary64Nan x y _ h

theorem forwardRawFmaNan (x y z : JuliaLean.Float.F64)
    (h : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true ∨
      JuliaLean.Float.F64.isnan z = true) :
    JuliaLean.Float.F64.isnan (JuliaLean.Float.F64.fma x y z) = true := by
  by_cases hxy : JuliaLean.Float.F64.isnan x = true ∨ JuliaLean.Float.F64.isnan y = true
  · exact forwardBinary64Nan x y _ hxy
  · have hx : JuliaLean.Float.F64.isnan x = false :=
      Bool.eq_false_iff.mpr (fun hx => hxy (Or.inl hx))
    have hy : JuliaLean.Float.F64.isnan y = false :=
      Bool.eq_false_iff.mpr (fun hy => hxy (Or.inr hy))
    have hz : JuliaLean.Float.F64.isnan z = true := by
      rcases h with hx | hy | hz
      · exact False.elim (hxy (Or.inl hx))
      · exact False.elim (hxy (Or.inr hy))
      · exact hz
    simp only [JuliaLean.Float.F64.fma, hx, hy, hz, Bool.false_eq_true, ↓reduceIte]
    exact forwardQuiet64Nan z hz

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.Proofs.base.special.hyperbolic

open JuliaLean.Registry

def entries : List Entry := [
  { id := "nummisc-tanh-float32-nonmonotone-v2", juliaFile := "base/special/hyperbolic.jl",
    juliaFns := ["tanh"],
    statement := "For every ordered same-format Float32 or Float64 pair, tanh is nondecreasing across the entire input domain, including negative values, branch transitions, zeros, and infinities.",
    source := "base/special/hyperbolic.jl:161-177; base/math.jl:326-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .refuted,
    prop := ``JuliaLean.Proofs.base.special.hyperbolicArchive20261101.TanhMonotone, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.NummiscTanhFloat32NonmonotoneV2_refuted,
    issue := "Related JuliaLang/julia#22738 (open) discusses merge returning Dict for identity dictionaries. PR #40893 (merged) changes mutating mergewith! performance. No exact key-loss duplicate established." },
  { id := "nummisc-hyperbolic-special-values-v2", juliaFile := "base/special/hyperbolic.jl",
    juliaFns := ["asinh", "acosh", "atanh"],
    statement := "For every Float32 or Float64 input, asinh, acosh, and atanh preserve their format and obey their real domains, finite-output requirements, signs, signed zeros, endpoint infinities, and NaN propagation.",
    source := "base/special/hyperbolic.jl:183-286; base/math.jl:386-393,488-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.hyperbolicArchive20261101.HyperbolicSpecialValues, thm := none, notes := "Incomplete exact proof: inverse-function finite-output bounds remain open; acosh also needs general in-domain success and nonnegative output. Partial helpers alone do not settle HyperbolicSpecialValues." },
  { id := "hyperbolic-forward-value-classes", juliaFile := "base/special/hyperbolic.jl",
    juliaFns := ["sinh", "cosh", "tanh"],
    statement := "For all Float32 and Float64 inputs, sinh, cosh, and tanh preserve format, obey their mathematical ranges, signs, signed-zero values, infinite limits, and NaN propagation, allowing finite sinh/cosh overflow. Float16 sinh preserves signs, signed zeros, infinities, and NaNs.",
    source := "base/special/hyperbolic.jl:58-88,103-125,161-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.hyperbolicArchive20261101.ForwardValueClasses, thm := none },
  { id := "hyperbolic-reciprocal-value-classes", juliaFile := "base/special/hyperbolic.jl",
    juliaFns := ["sech", "csch"],
    statement := "For every Float16, Float32, and Float64 input, sech is even and within [0,1] on non-NaNs, while csch is odd and preserves sign; both propagate NaN and obey their signed-zero poles and infinite limits.",
    source := "base/special/hyperbolic.jl:127-143; base/special/trig.jl:1418-1424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.hyperbolicArchive20261101.ReciprocalValueClasses, thm := none, notes := "Incomplete exact proof: sech range bounds, exponential-branch non-NaN output and the Float64 small sinh-kernel sign/classification remain open. Special-value and partial symmetry helpers do not settle ReciprocalValueClasses." }
]

end JuliaLean.Proofs.base.special.hyperbolic

namespace JuliaLean.ChatGPT.Batch8.Group3
open JuliaLean JuliaLean.Promotion JuliaLean.ChatGPT.Batch4.Group15

/-- Scaling a normalized positive rational leaves its significand below the precision cap. -/
theorem adFloat3RescaleUpper (n d precision : Nat) (e k : Int)
    (bound : if e ≥ 0 then n < 2 * (d * 2 ^ e.toNat)
      else n * 2 ^ (-e).toNat < 2 * d)
    (scale : e - precision ≤ k) :
    if k ≥ 0 then n < 2 ^ (precision + 1) * (d * 2 ^ k.toNat)
    else n * 2 ^ (-k).toNat < 2 ^ (precision + 1) * d := by
  have ht : 2 ≤ 2 ^ (precision + 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ precision + 1 by omega)
    simpa only [Nat.pow_one] using h
  by_cases he : 0 ≤ e
  · simp only [he, ↓reduceIte] at bound
    by_cases hk : 0 ≤ k
    · simp only [hk, ↓reduceIte]
      calc
        n < 2 * (d * 2 ^ e.toNat) := bound
        _ = d * 2 ^ (e.toNat + 1) := by
          simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ d * 2 ^ (precision + 1 + k.toNat) :=
          Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) (by omega))
        _ = 2 ^ (precision + 1) * (d * 2 ^ k.toNat) := by
          simp only [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · simp only [hk, ↓reduceIte]
      calc
        n * 2 ^ (-k).toNat < (2 * (d * 2 ^ e.toNat)) * 2 ^ (-k).toNat :=
          Nat.mul_lt_mul_of_pos_right bound (Nat.two_pow_pos _)
        _ = d * 2 ^ (e.toNat + 1 + (-k).toNat) := by
          simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ d * 2 ^ (precision + 1) :=
          Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) (by omega))
        _ = 2 ^ (precision + 1) * d := Nat.mul_comm _ _
  · simp only [he, ↓reduceIte] at bound
    by_cases hk : 0 ≤ k
    · simp only [hk, ↓reduceIte]
      have hn : n ≤ n * 2 ^ (-e).toNat := by
        have h := Nat.mul_le_mul_left n (Nat.two_pow_pos (-e).toNat)
        simpa only [Nat.mul_one] using h
      have hd : d ≤ d * 2 ^ k.toNat := by
        have h := Nat.mul_le_mul_left d (Nat.two_pow_pos k.toNat)
        simpa only [Nat.mul_one] using h
      exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hn bound) (Nat.mul_le_mul ht hd)
    · simp only [hk, ↓reduceIte]
      by_cases hek : e ≤ k
      · calc
          n * 2 ^ (-k).toNat ≤ n * 2 ^ (-e).toNat :=
            Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by decide) (by omega))
          _ < 2 * d := bound
          _ ≤ 2 ^ (precision + 1) * d := Nat.mul_le_mul_right d ht
      · have hexp : (-k).toNat = (-e).toNat + (e - k).toNat := by omega
        calc
          n * 2 ^ (-k).toNat = (n * 2 ^ (-e).toNat) * 2 ^ (e - k).toNat := by
            rw [hexp, Nat.pow_add, Nat.mul_assoc]
          _ < (2 * d) * 2 ^ (e - k).toNat :=
            Nat.mul_lt_mul_of_pos_right bound (Nat.two_pow_pos _)
          _ = d * 2 ^ ((e - k).toNat + 1) := by
            simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ d * 2 ^ (precision + 1) :=
            Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) (by omega))
          _ = 2 ^ (precision + 1) * d := Nat.mul_comm _ _

/-- The actual scaled quotient in roundRat has at most one rounding carry bit. -/
theorem adFloat3ScaledRoundedBound (n d precision : Nat) (hn : n ≠ 0) (hd : d ≠ 0)
    (k : Int) (hk : Fl.floorLog2Rat n d - precision ≤ k) :
    let scaled := if k ≥ 0 then (n, d * 2 ^ k.toNat) else (n * 2 ^ (-k).toNat, d)
    Fl.roundQuotient scaled.1 scaled.2 ≤ 2 ^ (precision + 1) := by
  have normalized := forwardFloorLog2NormalizedNat n d hn hd
  change (if Fl.floorLog2Rat n d ≥ 0 then
    d * 2 ^ (Fl.floorLog2Rat n d).toNat ≤ n ∧
      n < 2 * (d * 2 ^ (Fl.floorLog2Rat n d).toNat)
    else d ≤ n * 2 ^ (-Fl.floorLog2Rat n d).toNat ∧
      n * 2 ^ (-Fl.floorLog2Rat n d).toNat < 2 * d) at normalized
  have upper : if Fl.floorLog2Rat n d ≥ 0 then
      n < 2 * (d * 2 ^ (Fl.floorLog2Rat n d).toNat)
      else n * 2 ^ (-Fl.floorLog2Rat n d).toNat < 2 * d := by
    by_cases he : 0 ≤ Fl.floorLog2Rat n d
    · simp only [he, ↓reduceIte] at normalized ⊢
      exact normalized.2
    · simp only [he, ↓reduceIte] at normalized ⊢
      exact normalized.2
  have scaledBound := adFloat3RescaleUpper n d precision (Fl.floorLog2Rat n d) k upper hk
  dsimp only
  by_cases hk0 : 0 ≤ k
  · simp only [hk0, ↓reduceIte] at scaledBound ⊢
    have hp := Nat.mul_pos (show 0 < d by omega) (Nat.two_pow_pos k.toNat)
    have h := forwardNearestQuotientIntervalNat n (d * 2 ^ k.toNat) 0
      (2 ^ (precision + 1)) hp (by simp only [Nat.zero_mul, Nat.zero_le])
      (Nat.le_of_lt scaledBound)
    exact h.2
  · simp only [hk0, ↓reduceIte] at scaledBound ⊢
    have h := forwardNearestQuotientIntervalNat (n * 2 ^ (-k).toNat) d 0
      (2 ^ (precision + 1)) (by omega) (by simp only [Nat.zero_mul, Nat.zero_le])
      (Nat.le_of_lt scaledBound)
    exact h.2

/-- Zero has the requested sign and cannot be NaN. -/
theorem adFloat3ZeroClass (f : Fmt) (s : Bool) :
    (Fl.zero s : Fl f).signbit = s ∧ (Fl.zero s : Fl f).isnan = false := by
  have hz : (Fl.zero s : Fl f) = forwardPack s 0 0 := by
    simp only [Fl.zero, forwardPack, Nat.zero_mul, Nat.add_zero]
  rw [hz]
  obtain ⟨hs, he, hp⟩ := forwardPackParts (f := f) s 0 0
    (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  exact ⟨hs, by simp only [Fl.isnan, hp, bne_self_eq_false, Bool.and_false]⟩

/-- Infinity has the requested sign and cannot be NaN. -/
theorem adFloat3InfClass (f : Fmt) (s : Bool) :
    (Fl.inf s : Fl f).signbit = s ∧ (Fl.inf s : Fl f).isnan = false := by
  have hi : (Fl.inf s : Fl f) = forwardPack s f.emax 0 := by
    simp only [Fl.inf, forwardPack, Nat.add_zero]
  have hmax : f.emax < 2 ^ f.eb := by
    unfold Fmt.emax
    have := Nat.two_pow_pos f.eb
    omega
  rw [hi]
  obtain ⟨hs, he, hp⟩ := forwardPackParts (f := f) s f.emax 0 hmax (Nat.two_pow_pos _)
  exact ⟨hs, by simp only [Fl.isnan, hp, bne_self_eq_false, Bool.and_false]⟩

/-- A bounded significand cannot enter the NaN payload or corrupt its sign. -/
theorem adFloat3PackTailClass (f : Fmt) (hemax : 0 < f.emax)
    (s : Bool) (m : Nat) (p : Int) (hm : m < 2 ^ (f.sb + 1)) :
    let y : Fl f := if p + f.bias + f.sb ≥ f.emax then Fl.inf s else
      Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) +
        (if m < 2 ^ f.sb then m else
          (p + f.bias + f.sb).toNat * 2 ^ f.sb + (m - 2 ^ f.sb)))
    y.signbit = s ∧ y.isnan = false := by
  dsimp only
  by_cases he : p + (f.bias : Int) + f.sb ≥ f.emax
  · simp only [he, ↓reduceIte]
    exact adFloat3InfClass f s
  · simp only [he, ↓reduceIte]
    by_cases hsmall : m < 2 ^ f.sb
    · simp only [hsmall, ↓reduceIte]
      have hpack : (Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) + m) : Fl f) =
          forwardPack s 0 m := by
        simp only [forwardPack, Nat.zero_mul, Nat.zero_add]
      rw [hpack]
      obtain ⟨hs, hexp, _⟩ := forwardPackParts (f := f) s 0 m (Nat.two_pow_pos _) hsmall
      have hne : (0 == f.emax) = false := beq_eq_false_iff_ne.mpr (by omega)
      exact ⟨hs, by simp only [Fl.isnan, hexp, hne, Bool.false_and]⟩
    · simp only [hsmall, ↓reduceIte]
      change (forwardPack s (p + f.bias + f.sb).toNat (m - 2 ^ f.sb) : Fl f).signbit = s ∧
        (forwardPack s (p + f.bias + f.sb).toNat (m - 2 ^ f.sb) : Fl f).isnan = false
      have hraw : (p + (f.bias : Int) + f.sb).toNat < f.emax := by omega
      have hmax : f.emax < 2 ^ f.eb := by
        unfold Fmt.emax
        have := Nat.two_pow_pos f.eb
        omega
      have hfrac : m - 2 ^ f.sb < 2 ^ f.sb := by
        rw [Nat.pow_succ] at hm
        omega
      obtain ⟨hs, hexp, _⟩ := forwardPackParts (f := f) s
        (p + f.bias + f.sb).toNat (m - 2 ^ f.sb) (Nat.lt_trans hraw hmax) hfrac
      have hne : ((p + (f.bias : Int) + f.sb).toNat == f.emax) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hraw)
      exact ⟨hs, by simp only [Fl.isnan, hexp, hne, Bool.false_and]⟩

/-- The complete packing routine preserves sign and produces no NaN at its input bound. -/
theorem adFloat3PackRoundedClass (f : Fmt) (hemax : 0 < f.emax)
    (s : Bool) (q : Nat) (k : Int) (hq : q < 2 ^ (f.sb + 2)) :
    (Fl.packRounded s q k : Fl f).signbit = s ∧
      (Fl.packRounded s q k : Fl f).isnan = false := by
  unfold Fl.packRounded
  by_cases hzero : q = 0
  · simp only [hzero, beq_self_eq_true, ↓reduceIte]
    exact adFloat3ZeroClass f s
  · have hzero' : (q == 0) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hzero', Bool.false_eq_true, ↓reduceIte]
    by_cases hcarry : q ≥ 2 ^ (f.sb + 1)
    · simp only [hcarry, ↓reduceIte]
      apply adFloat3PackTailClass f hemax s (q / 2) (k + 1)
      have hp : 2 ^ (f.sb + 2) = 2 * 2 ^ (f.sb + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp] at hq
      omega
    · simp only [hcarry, ↓reduceIte]
      exact adFloat3PackTailClass f hemax s q k (by omega)

/-- Rounding a rational with positive denominator preserves the nonzero numerator's sign. -/
theorem adFloat3RoundRatNonzeroClass (f : Fmt) (hemax : 0 < f.emax)
    (n : Int) (d : Nat) (zeroSign : Bool) (hn : n ≠ 0) (hd : d ≠ 0) :
    (Fl.roundRat n d zeroSign : Fl f).signbit = decide (n < 0) ∧
      (Fl.roundRat n d zeroSign : Fl f).isnan = false := by
  have hdb : (d == 0) = false := beq_eq_false_iff_ne.mpr hd
  have hnb : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
  have ha : n.natAbs ≠ 0 := by omega
  unfold Fl.roundRat
  simp only [hdb, hnb, Bool.false_eq_true, ↓reduceIte]
  by_cases hover : Fl.floorLog2Rat n.natAbs d ≥ (f.emax : Int) - f.bias
  · simp only [hover, ↓reduceIte]
    exact adFloat3InfClass f _
  · simp only [hover, ↓reduceIte]
    by_cases hunder : Fl.floorLog2Rat n.natAbs d < -((f.bias : Int) + f.sb) - 1
    · simp only [hunder, ↓reduceIte]
      exact adFloat3ZeroClass f _
    · simp only [hunder, ↓reduceIte]
      apply adFloat3PackRoundedClass f hemax
      have hbound := adFloat3ScaledRoundedBound n.natAbs d f.sb ha hd
        (max (Fl.floorLog2Rat n.natAbs d - f.sb) (1 - (f.bias : Int) - f.sb))
        (Int.le_max_left _ _)
      exact Nat.lt_of_le_of_lt hbound (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Positive-denominator rational rounding always avoids NaNs, including an exact zero. -/
theorem adFloat3RoundRatNotNan (f : Fmt) (hemax : 0 < f.emax)
    (n : Int) (d : Nat) (zeroSign : Bool) (hd : d ≠ 0) :
    (Fl.roundRat n d zeroSign : Fl f).isnan = false := by
  by_cases hn : n = 0
  · have hdb : (d == 0) = false := beq_eq_false_iff_ne.mpr hd
    simp only [Fl.roundRat, hdb, hn, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    exact (adFloat3ZeroClass f zeroSign).2
  · exact (adFloat3RoundRatNonzeroClass f hemax n d zeroSign hn hd).2

end JuliaLean.ChatGPT.Batch8.Group3
