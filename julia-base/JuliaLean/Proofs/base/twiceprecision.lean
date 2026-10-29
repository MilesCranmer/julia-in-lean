import JuliaLean.base.twiceprecision
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
set_option linter.unusedSimpArgs false

namespace JuliaLean.Proofs.base.twiceprecision

open JuliaLean JuliaLean.Promotion JuliaLean.Registry JuliaLean.base.twiceprecision JuliaLean.base.range

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun hc => Except.ok.inj hc |> h)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun hc => Except.error.inj hc |> h)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

def floatFraction (x : F64) : Int × Int :=
  let (n, d) := x.toRat
  (n, Int.ofNat d)

def fractionAdd (x y : Int × Int) : Int × Int :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

def fractionMul (x y : Int × Int) : Int × Int := (x.1 * y.1, x.2 * y.2)

def fractionEq (x y : Int × Int) : Prop := x.1 * y.2 = y.1 * x.2

instance (x y : Int × Int) : Decidable (fractionEq x y) := by
  unfold fractionEq; infer_instance

def exactFloatSum (hi lo x y : F64) : Prop :=
  fractionEq (fractionAdd (floatFraction hi) (floatFraction lo))
    (fractionAdd (floatFraction x) (floatFraction y))

def exactTpFraction (x : TwicePrecision F64) : Int × Int :=
  fractionAdd (floatFraction x.hi) (floatFraction x.lo)

def decF64 (n : Int) (d : Nat := 1) : F64 :=
  Fl.roundRat n d false

def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def exactSplit (i : JInt .i64) (p : JlX (F64 × F64)) : Prop :=
  match p with
  | .ok (hi, lo) =>
    let (nh, dh) := hi.toRat
    let (nl, dl) := lo.toRat
    0 < dh ∧ 0 < dl ∧ nh * (dl : Int) + nl * (dh : Int) = i.val * (dh * dl : Nat)
  | .error _ => False

instance (i : JInt .i64) (p : JlX (F64 × F64)) : Decidable (exactSplit i p) := by
  unfold exactSplit; split <;> infer_instance

-- 1. SplitprecExact
def SplitprecExact : Prop :=
  ∀ i : JInt .i64, exactSplit i (splitprecF64 i) ∧
    ∃ tp, tpFromIntegerF64 i = .ok tp ∧ exactSplit i (.ok (tp.hi, tp.lo))

theorem splitprecExact_refuted : ¬ SplitprecExact := by
  intro h
  exact absurd (h (JuliaLean.base.int.typemax .i64)).1 (by decide +kernel)

-- 2. LinspaceFloatSucceeds
def LinspaceFloatSucceeds : Prop :=
  ∀ (a b : F64) (len : JInt .i64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    2 ≤ len.val →
    isOk (rangeStartStopLengthF64 a b len) = true ∧
    isOk (linspaceFloatF64 a b len) = true

theorem linspaceFloatSucceeds_refuted : ¬ LinspaceFloatSucceeds := by
  intro h
  exact absurd (h (decF64 (10^15)) (decF64 (10^15 + 1)) (JuliaLean.base.int.lit .i64 10000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1 (by decide +kernel)

-- 3. LinspaceFloatEndpoints
def LinspaceFloatEndpoints : Prop :=
  ∀ (a b : F64) (len : JInt .i64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    2 ≤ len.val →
    (rangeStartStopLengthF64 a b len = .ok r ∨ linspaceFloatF64 a b len = .ok r) →
    ∃ fst lst, srlFirstF64 r = .ok fst ∧ srlLastF64 r = .ok lst ∧
      JuliaLean.base.float.eq_IEEEFloat fst a = true ∧
      JuliaLean.base.float.eq_IEEEFloat lst b = true

theorem linspaceFloatEndpoints_refuted : ¬ LinspaceFloatEndpoints := by
  intro h
  have hbad : (match linspaceFloatF64 (JuliaLean.base.float.one_float .f64)
      (decF64 1 (10^14)) (JuliaLean.base.int.lit .i64 24) with
    | .ok r => match srlLastF64 r with
      | .ok lst => !JuliaLean.base.float.eq_IEEEFloat lst (decF64 1 (10^14))
      | .error _ => false
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : linspaceFloatF64 (JuliaLean.base.float.one_float .f64)
      (decF64 1 (10^14)) (JuliaLean.base.int.lit .i64 24) with
  | error _ => simp
  | ok r =>
    intro hbad
    obtain ⟨fst, lst, _, hlst, _, heq⟩ := h (JuliaLean.base.float.one_float .f64)
      (decF64 1 (10^14)) (JuliaLean.base.int.lit .i64 24) r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (Or.inr hr)
    simp [hlst, heq] at hbad

-- 4. ColonFirst
def ColonFirst : Prop :=
  ∀ (a s b : F64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    JuliaLean.base.float.isnan_IEEEFloat s = false →
    JuliaLean.base.float.iszero_float s = false →
    colonF64 a s b = .ok r →
    1 ≤ r.len.val →
    ∃ fst, srlFirstF64 r = .ok fst ∧ JuliaLean.base.float.eq_IEEEFloat fst a = true

theorem colonFirst_refuted : ¬ ColonFirst := by
  intro h
  have hbad : (match colonF64 (JuliaLean.base.float.zero_float .f64)
      (JuliaLean.base.float.inf_float .f64) (JuliaLean.base.float.one_float .f64) with
    | .ok r => decide (1 ≤ r.len.val) && (match srlFirstF64 r with
      | .ok fst => !JuliaLean.base.float.eq_IEEEFloat fst (JuliaLean.base.float.zero_float .f64)
      | .error _ => true)
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : colonF64 (JuliaLean.base.float.zero_float .f64)
      (JuliaLean.base.float.inf_float .f64) (JuliaLean.base.float.one_float .f64) with
  | error _ => simp
  | ok r =>
    intro hbad
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    obtain ⟨fst, hfst, heq⟩ := h (JuliaLean.base.float.zero_float .f64)
      (JuliaLean.base.float.inf_float .f64) (JuliaLean.base.float.one_float .f64) r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hr hbad.1
    have h2 := hbad.2
    simp [hfst, heq] at h2

-- 5. ColonEmpty
def ColonEmpty : Prop :=
  ∀ (a s b : F64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat s = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.zero_float .f64) s = true →
    JuliaLean.base.float.lt_IEEEFloat b a = true →
    colonF64 a s b = .ok r →
    r.len.val = 0

theorem colonEmpty_refuted : ¬ ColonEmpty := by
  intro h
  have hbad : (match colonF64 (decF64 1 (10^300)) (decF64 (10^30) 1)
      (JuliaLean.base.float.zero_float .f64) with
    | .ok r => decide (r.len.val ≠ 0)
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : colonF64 (decF64 1 (10^300)) (decF64 (10^30) 1)
      (JuliaLean.base.float.zero_float .f64) with
  | error _ => simp
  | ok r =>
    intro hbad
    simp only [decide_eq_true_eq] at hbad
    exact hbad (h _ _ _ r (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hr)

-- 6. ColonDecimal
def ColonDecimal : Prop :=
  ∀ (a s b : Int) (places : Nat),
    places ≤ 3 → 0 < s → a ≤ b → -(10^9) ≤ a → b ≤ 10^9 → s ≤ 10^9 →
    let scale := 10 ^ places
    let start := decF64 a scale
    let step := decF64 s scale
    let stop := decF64 b scale
    ∀ r, colonF64 start step stop = .ok r →
      r.len.val = (b - a) / s + 1 ∧
      ∀ k : Nat, (k : Int) < r.len.val →
        srlGetF64 r (JuliaLean.base.int.lit .i64 (k + 1)) = .ok (decF64 (a + k * s) scale)

def decimalThresholdRange : SRLF64 :=
  ⟨⟨Fl.ofBits 0, Fl.ofBits 0⟩, ⟨Fl.ofBits 0x3fb999999999999a, Fl.ofBits 0⟩,
    JuliaLean.base.int.lit .i64 167772171, JuliaLean.base.int.lit .i64 1⟩

theorem colonDecimal_refuted : ¬ ColonDecimal := by
  intro h
  have hc : colonF64 (decF64 0 (10^1)) (decF64 1 (10^1)) (decF64 167772170 (10^1)) =
      .ok decimalThresholdRange := by decide +kernel
  have hh := (h 0 1 167772170 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) decimalThresholdRange hc).2 3 (by decide +kernel)
  revert hh
  decide +kernel

-- 7. ColonStopBound
def ColonStopBound : Prop :=
  ∀ (a s b : F64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat s = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.zero_float .f64) s = true →
    colonF64 a s b = .ok r →
    1 ≤ r.len.val →
    ∃ lst, srlLastF64 r = .ok lst ∧ JuliaLean.base.float.le_IEEEFloat lst b = true

theorem colonStopBound_refuted : ¬ ColonStopBound := by
  intro h
  have hbad : (match colonF64 (decF64 1131 10000) (decF64 252 10000) (decF64 (10^15) 1) with
    | .ok r => decide (1 ≤ r.len.val) && (match srlLastF64 r with
      | .ok lst => !JuliaLean.base.float.le_IEEEFloat lst (decF64 (10^15) 1)
      | .error _ => true)
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : colonF64 (decF64 1131 10000) (decF64 252 10000) (decF64 (10^15) 1) with
  | error _ => simp
  | ok r =>
    intro hbad
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    obtain ⟨lst, hlst, hle⟩ := h _ _ _ r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hr hbad.1
    have h2 := hbad.2
    rw [hlst] at h2
    dsimp only at h2
    rw [hle] at h2
    cases h2

-- 8. StartStepNoNaN
def StartStepNoNaN : Prop :=
  ∀ (a s : F64) (len i : JInt .i64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat s = true →
    rangeStartStepLengthF64 a s len = .ok r →
    1 ≤ i.val → i.val ≤ r.len.val →
    ∃ x, unsafeGetindexF64 r i = .ok x ∧ JuliaLean.base.float.isnan_IEEEFloat x = false

theorem startStepNoNaN_refuted : ¬ StartStepNoNaN := by
  intro h
  have hbad : (match rangeStartStepLengthF64 (JuliaLean.base.float.one_float .f64)
      (decF64 (10^308) 1) (JuliaLean.base.int.lit .i64 3) with
    | .ok r => decide (r.len.val = 3) && (match unsafeGetindexF64 r (JuliaLean.base.int.lit .i64 3) with
      | .ok x => JuliaLean.base.float.isnan_IEEEFloat x
      | .error _ => true)
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : rangeStartStepLengthF64 (JuliaLean.base.float.one_float .f64)
      (decF64 (10^308) 1) (JuliaLean.base.int.lit .i64 3) with
  | error _ => simp
  | ok r =>
    intro hbad
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    obtain ⟨x, hx, hnan⟩ := h _ _ (JuliaLean.base.int.lit .i64 3)
      (JuliaLean.base.int.lit .i64 3) r (by decide +kernel) (by decide +kernel) hr
      (by decide) (by rw [hbad.1]; decide)
    have h2 := hbad.2
    simp [hx, hnan] at h2

-- 9. ColonFirstIdentical
def ColonFirstIdentical : Prop :=
  ∀ (a s b : F64) (r : SRLF64),
    JuliaLean.base.float.isfinite_IEEEFloat a = true →
    JuliaLean.base.float.isfinite_IEEEFloat s = true →
    JuliaLean.base.float.isfinite_IEEEFloat b = true →
    JuliaLean.base.float.iszero_float s = false →
    colonF64 a s b = .ok r →
    1 ≤ r.len.val →
    ∃ fst, srlFirstF64 r = .ok fst ∧ JuliaLean.base.float.isequal_IEEEFloat fst a = true

theorem colonFirstIdentical_refuted : ¬ ColonFirstIdentical := by
  intro h
  have hbad : (match colonF64 (Fl.zero true) (JuliaLean.base.float.one_float .f64) (decF64 2 1) with
    | .ok r => decide (1 ≤ r.len.val) && (match srlFirstF64 r with
      | .ok fst => !JuliaLean.base.float.isequal_IEEEFloat fst (Fl.zero true)
      | .error _ => true)
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : colonF64 (Fl.zero true) (JuliaLean.base.float.one_float .f64) (decF64 2 1) with
  | error _ => simp
  | ok r =>
    intro hbad
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    obtain ⟨fst, hfst, heq⟩ := h _ _ _ r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hr hbad.1
    have h2 := hbad.2
    simp [hfst, heq] at h2

-- 10. ColonNonfinite
def ColonNonfinite : Prop :=
  ∀ (a s b : F64),
    JuliaLean.base.float.isfinite_IEEEFloat s = true →
    JuliaLean.base.float.iszero_float s = false →
    (JuliaLean.base.float.isfinite_IEEEFloat a = false ∨
     JuliaLean.base.float.isfinite_IEEEFloat b = false) →
    ∃ msg, colonF64 a s b = .error (.jl (.argumentError msg))

theorem colonNonfinite_refuted : ¬ ColonNonfinite := by
  intro h
  obtain ⟨msg, hmsg⟩ := h (JuliaLean.base.float.zero_float .f64)
    (JuliaLean.base.float.one_float .f64) (JuliaLean.base.float.inf_float .f64)
    (by decide +kernel) (by decide +kernel) (Or.inr (by decide +kernel))
  have hc : colonF64 (JuliaLean.base.float.zero_float .f64)
    (JuliaLean.base.float.one_float .f64) (JuliaLean.base.float.inf_float .f64) =
    .error (.jl (.inexactError "Int64")) := by decide +kernel
  rw [hc] at hmsg
  cases hmsg

-- 11. SrlSumMatches
def intRangeElemVal {t : IntTy} (r : StepRangeLen (JInt t) (JInt t) (JInt t) (JInt .i64))
    (k : Nat) : Int :=
  r.ref.val + ((k : Int) + 1 - r.offset.val) * r.step.val

def intRangeElemsFit {t : IntTy} (r : StepRangeLen (JInt t) (JInt t) (JInt t) (JInt .i64)) : Prop :=
  ∀ k : Nat, k < r.len.val.toNat →
    t.min ≤ intRangeElemVal r k ∧ intRangeElemVal r k ≤ t.max

def intRangeElemSum {t : IntTy} (r : StepRangeLen (JInt t) (JInt t) (JInt t) (JInt .i64)) : Int :=
  ((List.range r.len.val.toNat).map (intRangeElemVal r)).sum

def SrlSumMatches : Prop :=
  ∀ (t : IntTy) (r : StepRangeLen (JInt t) (JInt t) (JInt t) (JInt .i64)),
    0 ≤ r.len.val → 1 ≤ r.offset.val → r.offset.val ≤ max 1 r.len.val →
    intRangeElemsFit r →
    -(2^62) ≤ intRangeElemSum r → intRangeElemSum r ≤ 2^62 →
    ∃ out, sumStepRangeLenInt t r = .ok out ∧ out.val = intRangeElemSum r

def sumCounterexample : StepRangeLen (JInt .i8) (JInt .i8) (JInt .i8) (JInt .i64) :=
  ⟨JuliaLean.base.int.lit .i8 1, JuliaLean.base.int.lit .i8 1,
   JuliaLean.base.int.lit .i64 100, JuliaLean.base.int.lit .i64 1⟩

theorem srlSumMatches_refuted : ¬ SrlSumMatches := by
  intro h
  have hs : intRangeElemSum sumCounterexample = 5050 := by decide +kernel
  have hlen : sumCounterexample.len.val.toNat = 100 := by decide
  have href : sumCounterexample.ref.val = 1 := by decide
  have hoff : sumCounterexample.offset.val = 1 := by decide
  have hstp : sumCounterexample.step.val = 1 := by decide
  have hmin : IntTy.i8.min = -128 := by decide
  have hmax : IntTy.i8.max = 127 := by decide
  have hfit : intRangeElemsFit sumCounterexample := by
    intro k hk
    rw [hlen] at hk
    unfold intRangeElemVal
    rw [href, hoff, hstp, hmin, hmax]
    omega
  obtain ⟨out, hout, _⟩ := h .i8 sumCounterexample (by decide) (by decide) (by decide) hfit
    (by rw [hs]; decide) (by rw [hs]; decide)
  have hbad : isOk (sumStepRangeLenInt .i8 sumCounterexample) = false := by decide +kernel
  rw [hout] at hbad
  cases hbad

-- 12. LinspaceIntSucceeds
def LinspaceIntSucceeds : Prop :=
  ∀ (a b len : JInt .i64),
    a.val ≠ b.val → 2 ≤ len.val →
    isOk (linspaceIntegerTypeF64 a b len) = true

theorem linspaceIntSucceeds_refuted : ¬ LinspaceIntSucceeds := by
  intro h
  exact absurd (h (JuliaLean.base.int.lit .i64 (IntTy.i64.max - 10))
    (JuliaLean.base.int.typemax .i64) (JuliaLean.base.int.lit .i64 3)
    (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- 13. LinspaceIntPositive
def LinspaceIntPositive : Prop :=
  ∀ (a b : JInt .i128) (len : JInt .i64) (r : SRLF64),
    0 < a.val → a.val ≤ b.val → 2 ≤ len.val →
    linspaceRational128F64 a b (JuliaLean.base.int.lit .i128 1) len = .ok r →
    ∃ fst, srlFirstF64 r = .ok fst ∧
      JuliaLean.base.float.lt_IEEEFloat fst (JuliaLean.base.float.zero_float .f64) = false

def bigA128 : JInt .i128 := ⟨2 ^ 126, by decide⟩
def bigB128 : JInt .i128 := ⟨2 ^ 126 + 2 ^ 80, by decide⟩

theorem linspaceIntPositive_refuted : ¬ LinspaceIntPositive := by
  intro h
  have hbad : (match linspaceRational128F64 bigA128 bigB128
      (JuliaLean.base.int.lit .i128 1) (JuliaLean.base.int.lit .i64 4) with
    | .ok r => match srlFirstF64 r with
      | .ok fst => JuliaLean.base.float.lt_IEEEFloat fst (JuliaLean.base.float.zero_float .f64)
      | .error _ => false
    | .error _ => false) = true := by decide +kernel
  revert hbad
  cases hr : linspaceRational128F64 bigA128 bigB128
      (JuliaLean.base.int.lit .i128 1) (JuliaLean.base.int.lit .i64 4) with
  | error _ => simp
  | ok r =>
    intro hbad
    obtain ⟨fst, hfst, hlt⟩ := h bigA128 bigB128 (JuliaLean.base.int.lit .i64 4) r
      (by decide) (by decide) (by decide) hr
    simp [hfst, hlt] at hbad

-- 14. Div12Rounded
def Div12Rounded : Prop :=
  ∀ x y : F64,
    JuliaLean.base.float.isfinite_IEEEFloat x = true →
    JuliaLean.base.float.isfinite_IEEEFloat y = true →
    JuliaLean.base.float.iszero_float y = false →
    let p := div12IEEE f64Arithmetic JuliaLean.base.int.ifelse x y
    JuliaLean.base.float.eq_IEEEFloat
      (JuliaLean.base.float.add_IEEEFloat p.1 p.2)
      (JuliaLean.base.float.div_IEEEFloat x y) = true

theorem div12Rounded_refuted : ¬ Div12Rounded := by
  intro h
  exact absurd (h (Fl.ofBits 0x0030000000000000)
    (JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 6))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- 15. SrlTwiceSumMatches
def SrlTwiceSumMatches : Prop :=
  ∀ (r : SRLF64) (refInt stepInt : Int),
    fractionEq (exactTpFraction r.ref) (refInt, 1) →
    fractionEq (exactTpFraction r.step) (stepInt, 1) →
    0 ≤ r.len.val → 1 ≤ r.offset.val → r.offset.val ≤ r.len.val →
    let expected := r.len.val * refInt +
      (r.len.val * (r.len.val + 1) / 2 - r.len.val * r.offset.val) * stepInt;
    -(2^53) ≤ expected → expected ≤ 2^53 →
    let out := sumStepRangeLenTwiceF64 r;
    JuliaLean.base.float.eq_IEEEFloat out (decF64 expected 1) = true

def srlTwiceSumCounterexample : SRLF64 :=
  ⟨⟨JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 (-51540000771)),
    JuliaLean.base.float.zero_float .f64⟩,
   ⟨JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 3),
    JuliaLean.base.float.zero_float .f64⟩,
   JuliaLean.base.int.lit .i64 34360000515,
   JuliaLean.base.int.lit .i64 1⟩

theorem srlTwiceSumMatches_refuted : ¬ SrlTwiceSumMatches := by
  intro h
  exact absurd (h srlTwiceSumCounterexample (-51540000771) 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

/-! ## Group 1: Range lengths, constructors, slicing, and conversions (21 proven entries) -/

theorem srlNewF64_fields (ref step : TwicePrecision F64) (len offset : JInt .i64) (r : SRLF64)
    (h : srlNewF64 ref step len offset = .ok r) :
    r = ⟨ref, step, len, offset⟩ ∧ r.len = len ∧ r.offset = offset := by
  unfold srlNewF64 at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem srlMakeTpF64_fields (ref step : TwicePrecision F64) (len offset : JInt .i64) (r : SRLF64)
    (h : srlMakeTpF64 ref step len offset = .ok r) :
    r = ⟨ref, step, len, offset⟩ ∧ r.len = len ∧ r.offset = offset :=
  srlNewF64_fields ref step len offset r h

theorem steprangelenHpF64_len_gen {I L R : Type} (ratio : I × I → JlX (TwicePrecision F64))
    (ratioBits : I × I → L → JlX (TwicePrecision F64))
    (make : TwicePrecision F64 → TwicePrecision F64 → L → L → JlX R)
    (length offsetOf : R → L)
    (hmake : ∀ a b n o r, make a b n o = .ok r → length r = n ∧ offsetOf r = o)
    (ref step : I × I) (nb len offset : L) (r : R)
    (h : steprangelenHpF64 ratio ratioBits make ref step nb len offset = .ok r) :
    length r = len ∧ offsetOf r = offset := by
  unfold steprangelenHpF64 at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  exact hmake _ _ _ _ r h

theorem hpRatioF64_len {t : IntTy} (ref step : JInt t × JInt t) (nb len offset : JInt .i64) (r : SRLF64)
    (h : hpRatioF64 ref step nb len offset = .ok r) : r.len = len ∧ r.offset = offset :=
  steprangelenHpF64_len_gen tpRatioF64 tpIntegerRatioBitsF64 srlMakeTpF64
    (fun x => x.len) (fun x => x.offset)
    (fun a b n o res hm => ⟨(srlMakeTpF64_fields a b n o res hm).2.1, (srlMakeTpF64_fields a b n o res hm).2.2⟩)
    ref step nb len offset r h

theorem hpFloat64_len (ref step : F64 ⊕ (F64 × F64)) (nb len offset : JInt .i64) (r : SRLF64)
    (h : hpFloat64 ref step nb len offset = .ok r) : r.len = len ∧ r.offset = offset := by
  have := srlMakeTpF64_fields _ _ _ _ r h
  exact ⟨this.2.1, this.2.2⟩

def HpBuildersLengthLaw {F I L N R : Type} (ops : FloatRangeOps F I L N R)
    (length : R → L) : Prop :=
  (∀ a b nb n o r, ops.hpRatio a b nb n o = .ok r → length r = n) ∧
  (∀ a b nb n o r, ops.hpFloat a b nb n o = .ok r → length r = n)

theorem f64RangeOps_law : HpBuildersLengthLaw f64RangeOps (fun r => r.len) :=
  ⟨fun a b nb n o r h => (hpRatioF64_len a b nb n o r h).1,
   fun a b nb n o r h => (hpFloat64_len (.inl a) (.inl b) nb n o r h).1⟩

theorem floatrange_len_gen {F I LI L N R : Type} (ops : FloatRangeOps F I L N R) (type : Type)
    (lenPlusZero : LI → L) (round : F → JlX L) (clamp : L → L → L → L)
    (floatInt : I → F) (offsetToInt : L → I) (one : L) (length : R → L)
    (hlaw : HpBuildersLengthLaw ops length)
    (start step : I) (len : LI) (den : I) (r : R)
    (h : floatrange ops type lenPlusZero round clamp floatInt offsetToInt one start step len den = .ok r) :
    length r = lenPlusZero len := by
  unfold floatrange at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · exact hlaw.1 _ _ _ _ _ r h
  · split at h
    · cases h
    · exact hlaw.1 _ _ _ _ _ r h

theorem floatrangeF64_len (a s len den : JInt .i64) (r : SRLF64)
    (h : floatrangeF64 a s len den = .ok r) : r.len = len :=
  floatrange_len_gen f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) id (JuliaLean.base.int.lit .i64 1)
    (fun x => x.len) f64RangeOps_law a s len den r h

theorem linspace1_len_gen {T I R : Type} (lenOps : IntegerOps I) (ops : Arithmetic T)
    (showT : T → String) (showLen : I → String) (isSmallFloat : Type → Bool)
    (toF64 : T → F64) (makeSmall : F64 → F64 → I → I → JlX R)
    (makeTwice : TwicePrecision T → TwicePrecision T → I → I → JlX R)
    (formatError : String → T → T → I → String) (length offsetOf : R → I)
    (hsmall : ∀ a b n o out, makeSmall a b n o = .ok out → length out = n ∧ offsetOf out = o)
    (htwice : ∀ a b n o out, makeTwice a b n o = .ok out → length out = n ∧ offsetOf out = o)
    (a b : T) (len : I) (r : R)
    (h : linspace1 lenOps ops showT showLen isSmallFloat toF64 makeSmall makeTwice formatError a b len = .ok r) :
    length r = len ∧ offsetOf r = lenOps.one := by
  unfold linspace1 at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h; · cases h
  split at h
  · split at h; · cases h
    split at h
    · exact hsmall _ _ _ _ r h
    · exact htwice _ _ _ _ r h
  · cases h

theorem linspace1F64_fields (a b : F64) (len : JInt .i64) (r : SRLF64)
    (h : linspace1F64 a b len = .ok r) : r.len = len ∧ r.offset = JuliaLean.base.int.lit .i64 1 :=
  linspace1_len_gen (jintOps .i64) f64Arithmetic (fun _ => "") (fun _ => "") (fun _ => false) id
    (fun _ _ _ _ => .error (.jl (.argumentError "unreachable"))) srlMakeTpF64
    (fun msg _ _ _ => msg) (fun x => x.len) (fun x => x.offset)
    (by intro _ _ _ _ _ hm; cases hm)
    (fun a b n o out hm => ⟨(srlMakeTpF64_fields a b n o out hm).2.1, (srlMakeTpF64_fields a b n o out hm).2.2⟩)
    a b len r h

theorem linspace1F64_len (a b : F64) (len : JInt .i64) (r : SRLF64)
    (h : linspace1F64 a b len = .ok r) : r.len = len :=
  (linspace1F64_fields a b len r h).1

theorem linspaceRational_len_gen {F I L W N R : Type} (ops : FloatRangeOps F I L N R)
    (lenPlusZero : L → L) (ls1 : F → F → L → JlX R)
    (toF64Int : I → F64) (toF64Len : L → F64) (roundInt : F64 → JlX L) (clamp : L → L → L → L)
    (widenLen : L → W) (widenInt : I → W) (wide : Arithmetic W) (one : L)
    (hpRatioWide : W × W → W × W → N → L → L → JlX R) (length : R → L)
    (hls1 : ∀ a b n r, ls1 a b n = .ok r → length r = n)
    (hhp : ∀ a b nb n o r, hpRatioWide a b nb n o = .ok r → length r = n)
    (startN stopN den : I) (len : L) (r : R)
    (h : linspaceRational ops lenPlusZero ls1 toF64Int toF64Len roundInt clamp
      widenLen widenInt wide one hpRatioWide startN stopN den len = .ok r) :
    length r = lenPlusZero len := by
  unfold linspaceRational at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h; · exact hls1 _ _ _ r h
  split at h; · exact hhp _ _ _ _ _ r h
  split at h; · cases h
  exact hhp _ _ _ _ _ r h

theorem linspaceRationalF64_len (a b den len : JInt .i64) (r : SRLF64)
    (h : linspaceRationalF64 a b den len = .ok r) : r.len = len :=
  linspaceRational_len_gen f64RangeOps id linspace1F64
    (JuliaLean.base.float.floatOfInt .f64) (JuliaLean.base.float.floatOfInt .f64)
    roundIntF64 clampI64 (JuliaLean.base.int.widenTo .i128) (JuliaLean.base.int.widenTo .i128)
    (jintArith .i128) (JuliaLean.base.int.lit .i64 1) (hpRatioF64 (t := .i128))
    (fun x => x.len) linspace1F64_len (fun a b nb n o res hm => (hpRatioF64_len a b nb n o res hm).1)
    a b den len r h

theorem linspaceIntegerTypeF64_len (a b len : JInt .i64) (r : SRLF64)
    (h : linspaceIntegerTypeF64 a b len = .ok r) : r.len = len :=
  linspaceRationalF64_len a b (JuliaLean.base.int.lit .i64 1) len r h

theorem linspaceFloat_len_gen {F I N R : Type} (ops : FloatRangeOps F I I N R)
    (lenPlusZero : I → I) (roundInt : F → JlX I) (float : I → F)
    (one : I) (isfinite : F → Bool) (prevfloat : F → F) (floatmax : F)
    (maxF minF : F → F → F) (clampF : F → F → F → F)
    (truncbits : F → N → F) (add12 : F → F → F × F)
    (hp : F × F → F × F → N → I → I → JlX R)
    (errorMessage : F → F → String) (length : R → I)
    (hhp : ∀ ref step nb n o r, hp ref step nb n o = .ok r → length r = n)
    (start stop : F) (len : I) (r : R)
    (h : linspaceFloat ops lenPlusZero roundInt float one isfinite prevfloat floatmax
      maxF minF clampF truncbits add12 hp errorMessage start stop len = .ok r) :
    length r = lenPlusZero len := by
  unfold linspaceFloat at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i imin0 _
      generalize (if (ops.integer.lt ops.integer.one imin0 && ops.integer.lt imin0 (lenPlusZero len)) = true then _ else _) = p at h
      rcases p with ⟨imin, ref, step⟩
      dsimp only at h
      split at h
      · exact hhp _ _ _ _ _ r h
      · exact hhp _ _ _ _ _ r h

theorem linspaceFloatF64_len (a b : F64) (len : JInt .i64) (r : SRLF64)
    (h : linspaceFloatF64 a b len = .ok r) : r.len = len :=
  linspaceFloat_len_gen f64RangeOps id roundIntF64 (JuliaLean.base.float.floatOfInt .f64)
    (JuliaLean.base.int.lit .i64 1) JuliaLean.base.float.isfinite_IEEEFloat
    JuliaLean.base.float.prevfloat (JuliaLean.base.float.floatmax_float .f64)
    fmaxF64 fminF64 fclampF64 truncbitsF64
    (add12Same f64Arithmetic JuliaLean.base.int.ifelse)
    (fun ref step nb l o => hpFloat64 (.inr ref) (.inr step) nb l o)
    (fun _ _ => "start and stop must be finite") (fun x => x.len)
    (fun ref step nb n o res hm => (hpFloat64_len (.inr ref) (.inr step) nb n o res hm).1)
    a b len r h

theorem rangeStartStopLength_len_gen {F I N R : Type} (ops : FloatRangeOps F I I N R)
    (lenPlusZero : I → I) (ls1 lsFloat : F → F → I → JlX R)
    (lsRatio : I → I → I → I → JlX R) (roundInt : F → JlX I)
    (length : R → I) (hlaw : HpBuildersLengthLaw ops length)
    (hls1 : ∀ a b n r, ls1 a b n = .ok r → length r = n)
    (hlsFloat : ∀ a b n r, lsFloat a b n = .ok r → length r = n)
    (hlsRatio : ∀ a b n d r, lsRatio a b n d = .ok r → length r = n)
    (start stop : F) (len one : I) (r : R)
    (h : rangeStartStopLength ops lenPlusZero ls1 lsFloat lsRatio roundInt start stop len one = .ok r) :
    length r = lenPlusZero len := by
  unfold rangeStartStopLength at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h; · exact hls1 _ _ _ r h
  split at h; · exact hlaw.2 _ _ _ _ _ r h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h; · cases h
    split at h
    · split at h; · cases h
      split at h; · cases h
      split at h
      · exact hlsRatio _ _ _ _ r h
      · exact hlsFloat _ _ _ r h
    · exact hlsFloat _ _ _ r h
  · exact hlsFloat _ _ _ r h

theorem rangeStartStopLengthF64_len (a b : F64) (len : JInt .i64) (r : SRLF64)
    (h : rangeStartStopLengthF64 a b len = .ok r) : r.len = len :=
  rangeStartStopLength_len_gen f64RangeOps id linspace1F64 linspaceFloatF64
    (fun s e l d => linspaceRationalF64 s e d l) roundIntF64
    (fun x => x.len) f64RangeOps_law linspace1F64_len linspaceFloatF64_len
    (fun s e l d res hm => linspaceRationalF64_len s e d l res hm)
    a b len (JuliaLean.base.int.lit .i64 1) r h

theorem rangeStartStepLength_len_gen {F I L N R : Type} (ops : FloatRangeOps F I L N R)
    (type : Type) (lenPlusZero : L → L) (round : F → JlX L)
    (clampInt : L → L → L → L) (floatInt : I → F) (offsetToInt : L → I)
    (one : L) (length : R → L) (hlaw : HpBuildersLengthLaw ops length)
    (hIdem : ∀ x, lenPlusZero (lenPlusZero x) = lenPlusZero x)
    (a st : F) (len : L) (r : R)
    (h : rangeStartStepLength ops type lenPlusZero round clampInt floatInt offsetToInt one a st len = .ok r) :
    length r = lenPlusZero len := by
  unfold rangeStartStepLength at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h; · cases h
    split at h
    · rw [floatrange_len_gen ops type lenPlusZero round clampInt floatInt offsetToInt one length hlaw _ _ _ _ r h, hIdem]
    · exact hlaw.2 _ _ _ _ _ r h
  · exact hlaw.2 _ _ _ _ _ r h

theorem rangeStartStepLengthF64_len (a s : F64) (len : JInt .i64) (r : SRLF64)
    (h : rangeStartStepLengthF64 a s len = .ok r) : r.len = len :=
  rangeStartStepLength_len_gen f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) id (JuliaLean.base.int.lit .i64 1)
    (fun x => x.len) f64RangeOps_law (fun _ => rfl) a s len r h

theorem rangeStartStepLengthSameF64_len (a s : F64) (len : JInt .i64) (r : SRLF64)
    (h : rangeStartStepLengthSameF64 a s len = .ok r) : r.len = len :=
  rangeStartStepLengthF64_len a s len r h

theorem srlReverseF64_len (r out : SRLF64) (h : srlReverseF64 r = .ok out) : out.len = r.len :=
  (srlMakeTpF64_fields _ _ _ _ out h).2.1

theorem rangeStepStopLengthF64_len (s b : F64) (len : JInt .i64) (r : SRLF64)
    (h : rangeStepStopLengthF64 s b len = .ok r) : r.len = len := by
  unfold rangeStepStopLengthF64 rangeStepStopLength at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i q hq
    rw [srlReverseF64_len q r h]
    exact rangeStartStepLengthF64_len b (JuliaLean.base.float.neg_IEEEFloat s) len q hq

def FloatrangeLength : Prop :=
  (∀ a s len den r, floatrangeF64 a s len den = .ok r → r.len = len) ∧
  (∀ {F I L N R : Type} (ops : FloatRangeOps F I L N R) (type : Type)
    (lenPlusZero : L → L) (round : F → JlX L) (clamp : L → L → L → L)
    (floatInt : I → F) (offsetToInt : L → I) (one : L) (length : R → L),
    HpBuildersLengthLaw ops length →
    ∀ start step len den r,
      floatrange ops type lenPlusZero round clamp floatInt offsetToInt one
        start step len den = .ok r → length r = lenPlusZero len)

theorem floatrangeLength_proven : FloatrangeLength :=
  ⟨floatrangeF64_len, fun ops type lenPlusZero round clamp floatInt offsetToInt one length hlaw start step len den r h =>
    floatrange_len_gen ops type lenPlusZero round clamp floatInt offsetToInt one length hlaw start step len den r h⟩

def HpRatioLength : Prop :=
  (∀ {t : IntTy} (ref step : JInt t × JInt t) (nb len offset : JInt .i64) r,
    hpRatioF64 ref step nb len offset = .ok r → r.len = len ∧ r.offset = offset) ∧
  (∀ {I L R : Type} (ratio : I × I → JlX (TwicePrecision F64))
    (ratioBits : I × I → L → JlX (TwicePrecision F64))
    (make : TwicePrecision F64 → TwicePrecision F64 → L → L → JlX R)
    (length : R → L),
    (∀ a b n o r, make a b n o = .ok r → length r = n) →
    ∀ ref step nb len offset r,
      steprangelenHpF64 ratio ratioBits make ref step nb len offset = .ok r →
      length r = len)

theorem hpRatioLength_proven : HpRatioLength := by
  refine ⟨fun ref step nb len offset r h => hpRatioF64_len ref step nb len offset r h, ?_⟩
  intro I L R ratio ratioBits make length hmake ref step nb len offset r h
  unfold steprangelenHpF64 at h
  dsimp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  exact hmake _ _ _ _ r h

def HpFloatLength : Prop :=
  (∀ (ref step : F64 ⊕ (F64 × F64)) (nb len offset : JInt .i64) r,
    hpFloat64 ref step nb len offset = .ok r → r.len = len ∧ r.offset = offset) ∧
  (∀ (ref step : TwicePrecision F64) (len offset : JInt .i64) r,
    srlMakeTpF64 ref step len offset = .ok r → r = ⟨ref, step, len, offset⟩) ∧
  (∀ (ref step : TwicePrecision F64) (len offset : JInt .i64),
    JuliaLean.base.int.ltSame len (JuliaLean.base.int.lit .i64 0) = true →
    srlMakeTpF64 ref step len offset = .error (.jl (.argumentError "length cannot be negative"))) ∧
  (∀ {I L : Type} (asParts : F64 ⊕ (F64 × F64) → TwicePrecision F64)
    (truncate : TwicePrecision F64 → I → TwicePrecision F64)
    (make : TwicePrecision F64 → TwicePrecision F64 → L → L → JlX
      (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) L))
    (length : StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) L → L),
    (∀ a b n o r, make a b n o = .ok r → length r = n) →
    ∀ ref step nb len offset r,
      steprangelenHpFloat64 asParts truncate make ref step nb len offset = .ok r →
      length r = len)

theorem hpFloatLength_proven : HpFloatLength := by
  refine ⟨hpFloat64_len, fun ref step len offset r h => (srlMakeTpF64_fields ref step len offset r h).1, ?_, ?_⟩
  · intro ref step len offset hlt
    simp [srlMakeTpF64, stepRangeLenFromTwicePrecision, srlNewF64, hlt]
  · intro I L asParts truncate make length hmake ref step nb len offset r h
    exact hmake _ _ _ _ r h

def HpTupleLength : Prop :=
  ∀ {T I L R : Type} (div : I → I → T) (make : T → T → L → L → JlX R)
    (refOf stepOf : R → T) (length : R → L) (offsetOf : R → L),
    (∀ a b n o r, make a b n o = .ok r →
      refOf r = a ∧ stepOf r = b ∧ length r = n ∧ offsetOf r = o) →
    ∀ ref step nb len offset r,
      steprangelenHpRatioIEEE div make ref step nb len offset = .ok r →
      refOf r = div ref.1 ref.2 ∧ stepOf r = div step.1 step.2 ∧
      length r = len ∧ offsetOf r = offset

theorem hpTupleLength_proven : HpTupleLength := by
  intro T I L R div make refOf stepOf length offsetOf hmake ref step nb len offset r h
  exact hmake _ _ _ _ r h

def HpFloatIEEELength : Prop :=
  (∀ (x : F64), asF64Scalar id x = x) ∧
  (∀ (a b : F64), asF64Pair id (a, b) = JuliaLean.base.float.add_IEEEFloat a b) ∧
  (∀ {F I L R : Type} (convert : F → F64)
    (make : F64 → F64 → L → L → JlX R) (refOf stepOf : R → F64) (length : R → L) (offsetOf : R → L),
    (∀ a b n o result, make a b n o = .ok result →
      refOf result = a ∧ stepOf result = b ∧ length result = n ∧ offsetOf result = o) →
    let asF64 : F ⊕ (F × F) → F64 := fun v => match v with
      | .inl x => asF64Scalar convert x
      | .inr p => asF64Pair convert p;
    ∀ (ref step : F ⊕ (F × F)) (nb : I) (len offset : L) (out : R),
      steprangelenHpFloatIEEE asF64 make ref step nb len offset = .ok out →
      refOf out = asF64 ref ∧ stepOf out = asF64 step ∧ length out = len ∧ offsetOf out = offset)

theorem hpFloatIEEELength_proven : HpFloatIEEELength := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro F I L R convert make refOf stepOf length offsetOf hmake asF64 ref step nb len offset out h
  exact hmake _ _ _ _ out h

def RsslPromoteLength : Prop :=
  (∀ (a : JInt .i64) (s : F64) (len : JInt .i64) r,
    rangeStartStepLengthIntFloatF64 a s len = .ok r → r.len = len) ∧
  (∀ (a : F64) (s : JInt .i64) (len : JInt .i64) r,
    rangeStartStepLengthFloatIntF64 a s len = .ok r → r.len = len) ∧
  (∀ (a s : F64) (len : JInt .i64) r,
    rangeStartStepLengthSameF64 a s len = .ok r → r.len = len)

theorem rsslPromoteLength_proven : RsslPromoteLength :=
  ⟨fun _ _ len r h => rangeStartStepLengthF64_len _ _ len r h,
   fun _ _ len r h => rangeStartStepLengthF64_len _ _ len r h,
   rangeStartStepLengthSameF64_len⟩

def RstslPromoteLength : Prop :=
  (∀ (s : JInt .i64) (b : F64) (len : JInt .i64) r,
    rangeStepStopLengthIntFloatF64 s b len = .ok r → r.len = len) ∧
  (∀ (s : F64) (b : JInt .i64) (len : JInt .i64) r,
    rangeStepStopLengthFloatIntF64 s b len = .ok r → r.len = len)

theorem rstslPromoteLength_proven : RstslPromoteLength :=
  ⟨fun _ _ len r h => rangeStepStopLengthF64_len _ _ len r h,
   fun _ _ len r h => rangeStepStopLengthF64_len _ _ len r h⟩

def LinspaceIntLength : Prop :=
  (∀ (a b len : JInt .i64) r,
    linspaceIntegerTypeF64 a b len = .ok r → r.len = len) ∧
  (∀ {A B I R : Type} (one : A → I) (linspaceRational : A → B → I → I → JlX R)
    (length : R → I),
    (∀ a b n d r, linspaceRational a b n d = .ok r → length r = n) →
    ∀ (a : A) (b : B) (len : I) (r : R),
      linspaceIntegerType one linspaceRational a b len = .ok r → length r = len)

theorem linspaceIntLength_proven : LinspaceIntLength :=
  ⟨linspaceIntegerTypeF64_len, fun _ _ _ hlaw a b len r h => hlaw a b len _ r h⟩

def LinspaceFloatMethod : Prop :=
  (∀ (a b : F64) (len : JInt .i64) r,
    linspaceFloatF64 a b len = .ok r → r.len = len) ∧
  (∀ (a b : F64) (len : JInt .i64),
    (JuliaLean.base.float.isfinite_IEEEFloat a = false ∨
     JuliaLean.base.float.isfinite_IEEEFloat b = false) →
    linspaceFloatF64 a b len = .error (.jl (.argumentError "start and stop must be finite")))

theorem linspaceFloatMethod_proven : LinspaceFloatMethod := by
  refine ⟨linspaceFloatF64_len, ?_⟩
  intro a b len h
  unfold linspaceFloatF64 linspaceFloat
  rcases h with ha | hb
  · simp [ha, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [hb, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

def Linspace1Method : Prop :=
  (∀ (a b : F64) (len : JInt .i64) r,
    linspace1F64 a b len = .ok r → r.len = len ∧ r.offset = JuliaLean.base.int.lit .i64 1) ∧
  (∀ (a b : F64) (len : JInt .i64),
    JuliaLean.base.int.ltSame len (JuliaLean.base.int.lit .i64 0) = true →
    linspace1F64 a b len = .error (.jl (.argumentError "negative length"))) ∧
  (∀ (a b : F64),
    JuliaLean.base.float.eq_IEEEFloat a b = false →
    linspace1F64 a b (JuliaLean.base.int.lit .i64 1) =
      .error (.jl (.argumentError "endpoints differ")))

theorem linspace1Method_proven : Linspace1Method := by
  refine ⟨linspace1F64_fields, ?_, ?_⟩
  · intro a b len hlt
    unfold linspace1F64 linspace1
    simp [jintOps, hlt, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro a b heq
    have hlt : JuliaLean.base.int.ltSame (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 0) = false := by decide
    have hle : JuliaLean.base.int.leSame (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 1) = true := by decide
    have he1 : JuliaLean.base.int.eqSame (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 1) = true := by decide
    unfold linspace1F64 linspace1
    simp [jintOps, f64Arithmetic, fvArithmetic, hlt, hle, he1, heq, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

def RangeConstructorsLength : Prop :=
  (∀ (a b : F64) (len : JInt .i64) r,
    rangeStartStopLengthF64 a b len = .ok r → r.len = len) ∧
  (∀ (a s : F64) (len : JInt .i64) r,
    rangeStartStepLengthF64 a s len = .ok r → r.len = len) ∧
  (∀ (a s : F64) (len : JInt .i64) r,
    rangeStartStepLengthSameF64 a s len = .ok r → r.len = len) ∧
  (∀ (s b : F64) (len : JInt .i64) r,
    rangeStepStopLengthF64 s b len = .ok r → r.len = len) ∧
  FloatrangeLength ∧ LinspaceFloatMethod

theorem rangeConstructorsLength_proven : RangeConstructorsLength :=
  ⟨rangeStartStopLengthF64_len, rangeStartStepLengthF64_len,
   rangeStartStepLengthSameF64_len, rangeStepStopLengthF64_len,
   floatrangeLength_proven, linspaceFloatMethod_proven⟩

def ScalarMulLength : Prop :=
  (∀ (x : F64) (r out : SRLF64),
    scalarMulRangeF64 x r = .ok out → out.len = r.len ∧ out.offset = r.offset) ∧
  (∀ (r : SRLF64) (x : F64) (out : SRLF64),
    scalarMulRangeRightF64 r x = .ok out → out.len = r.len ∧ out.offset = r.offset)

theorem scalarMulLength_proven : ScalarMulLength := by
  refine ⟨?_, ?_⟩
  · intro x r out h
    have := srlMakeTpF64_fields _ _ _ _ out h
    exact ⟨this.2.1, this.2.2⟩
  · intro r x out h
    have := srlMakeTpF64_fields _ _ _ _ out h
    exact ⟨this.2.1, this.2.2⟩

def ScalarDivLength : Prop :=
  ∀ (r : SRLF64) (x : F64) (out : SRLF64),
    scalarDivRangeF64 r x = .ok out → out.len = r.len ∧ out.offset = r.offset

theorem scalarDivLength_proven : ScalarDivLength := by
  intro r x out h
  have := srlMakeTpF64_fields _ _ _ _ out h
  exact ⟨this.2.1, this.2.2⟩

def HiprecBool : Prop :=
  ∀ (r : SRLF64) (b : Bool),
    getindexHiprecF64 (fun _ : Bool => true) (fun b => if b then "true" else "false")
      (fun _ i => .ok (JuliaLean.base.int.lit .i64 (if i then 1 else 0))) r b =
      .error (.jl (.argumentError ("invalid index: " ++ (if b then "true" else "false") ++
        " of type Bool")))

theorem hiprecBool_proven : HiprecBool := by
  intro r b
  unfold getindexHiprecF64 getindexHiprec
  simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem addStepRangeLen_len_gen {T I : Type} (ops : Arithmetic I)
    (len1 len2 : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I → I)
    (addTp : TwicePrecision T → TwicePrecision T → TwicePrecision T)
    (getindexHiprec : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I → I → JlX (TwicePrecision T))
    (roundHalf : I → I → I) (twiceprecision : TwicePrecision T → Nat → TwicePrecision T)
    (nbitslen : Type → I → I → Nat)
    (make : TwicePrecision T → TwicePrecision T → I → I → JlX (StepRangeLen T (TwicePrecision T) (TwicePrecision T) I))
    (hmake : ∀ ref st n o out, make ref st n o = .ok out → out.len = n)
    (r1 r2 out : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I)
    (h : addStepRangeLen ops len1 len2 addTp getindexHiprec roundHalf twiceprecision nbitslen make r1 r2 = .ok out) :
    out.len = len1 r1 := by
  unfold addStepRangeLen at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h; · cases h
  split at h
  · exact hmake _ _ _ _ out h
  · split at h; · cases h
    split at h; · cases h
    exact hmake _ _ _ _ out h

def AddSrlLength : Prop :=
  (∀ (r1 r2 : SRLF64),
    JuliaLean.base.int.eqSame r1.len r2.len = false →
    addStepRangeLenF64 r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ (r1 r2 out : SRLF64),
    addStepRangeLenF64 r1 r2 = .ok out → out.len = r1.len)

theorem addSrlLength_proven : AddSrlLength := by
  refine ⟨?_, ?_⟩
  · intro r1 r2 hne
    unfold addStepRangeLenF64 addStepRangeLen
    simp [jintArith, length_StepRangeLen, hne, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro r1 r2 out h
    exact addStepRangeLen_len_gen (jintArith .i64) length_StepRangeLen length_StepRangeLen
      (addTpSame f64Arithmetic)
      (getindexHiprecF64 (fun _ : JInt .i64 => false) (fun _ => "") (fun _ i => .ok i))
      roundHalfI64 (fun x nb => twiceprecisionTPF64 x (JuliaLean.base.int.lit .i64 nb))
      (fun _ l o => (nbitslenF64 l o).val.toNat) srlMakeTpF64
      (fun ref st n o res hm => (srlMakeTpF64_fields ref st n o res hm).2.1)
      r1 r2 out h

def TpSliceLength : Prop :=
  ∀ {T Ref Step LR U L I N Out : Type}
    (checkbounds : StepRangeLen T Ref Step LR → U → JlX Unit)
    (length : U → L) (stepHp : U → I)
    (stepHpRange : StepRangeLen T Ref Step LR → Step)
    (stepRange : StepRangeLen T Ref Step LR → Step)
    (firstBool : U → Bool) (firstIndex : U → I)
    (firstRange : StepRangeLen T Ref Step LR → T) (lastRange : StepRangeLen T Ref Step LR → T)
    (ops : Arithmetic L) (indexOps : Arithmetic I) (toLen : I → L) (toIndex : L → I)
    (offsetToLen : LR → L) (round : L → L) (clamp : L → L → L → L)
    (oneUnit zeroLen : L) (stepEqualsOne : I → Bool) (lenBelowTwo : L → Bool)
    (mulStep : Step → I → Step) (twiceprecision : Step → N → Step)
    (nbitslen : Type → L → L → N) (addRef : Ref → Step → Ref)
    (scaleStep : L → Step → Step) (makeT : T → Step → L → L → JlX Out)
    (makeRef : Ref → Step → L → L → JlX Out)
    (range : StepRangeLen T Ref Step LR) (slice : U) (out : Out)
    (lengthOut : Out → L),
    (∀ x st n o result, makeT x st n o = .ok result → lengthOut result = n) →
    (∀ x st n o result, makeRef x st n o = .ok result → lengthOut result = n) →
    ((getindexStepRangeLen checkbounds length stepHp stepHpRange stepRange false
        firstBool firstIndex firstRange lastRange ops indexOps toLen toIndex offsetToLen round clamp
        oneUnit zeroLen stepEqualsOne lenBelowTwo mulStep twiceprecision nbitslen addRef scaleStep
        makeT makeRef range slice = .ok out → lengthOut out = length slice) ∧
     (getindexStepRangeLen checkbounds length stepHp stepHpRange stepRange true
        firstBool firstIndex firstRange lastRange ops indexOps toLen toIndex offsetToLen round clamp
        oneUnit zeroLen stepEqualsOne lenBelowTwo mulStep twiceprecision nbitslen addRef scaleStep
        makeT makeRef range slice = .ok out →
        lengthOut out =
          if ops.eq (length slice) zeroLen then zeroLen
          else if ops.eq (length slice) oneUnit then
            (if firstBool slice then oneUnit else zeroLen)
          else oneUnit))

theorem tpSliceLength_proven : TpSliceLength := by
  intro T Ref Step LR U L I N Out checkbounds length stepHp stepHpRange stepRange
    firstBool firstIndex firstRange lastRange ops indexOps toLen toIndex offsetToLen round clamp
    oneUnit zeroLen stepEqualsOne lenBelowTwo mulStep twiceprecision nbitslen addRef scaleStep
    makeT makeRef range slice out lengthOut hmakeT hmakeRef
  refine ⟨?_, ?_⟩
  · intro h
    unfold getindexStepRangeLen at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h <;> exact hmakeRef _ _ _ _ out h
  · intro h
    unfold getindexStepRangeLen at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, ↓reduceIte] at h
    split at h
    · cases h
    · by_cases h0 : ops.eq (length slice) zeroLen = true
      · simp only [h0, ↓reduceIte] at h ⊢
        exact hmakeT _ _ _ _ out h
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases h1 : ops.eq (length slice) oneUnit = true
        · simp only [h1, ↓reduceIte] at h ⊢
          by_cases hf : firstBool slice = true
          · simp only [hf, ↓reduceIte] at h ⊢
            exact hmakeT _ _ _ _ out h
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
            exact hmakeT _ _ _ _ out h
        · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact hmakeT _ _ _ _ out h

def CountedSRLConversion : Prop :=
  ∀ {T U V R S L I : Type}
    (convertR : U → JlX R) (convertS : V → JlX S) (convertL : I → JlX L)
    (length : StepRangeLen T U V I → I)
    (make : R → S → L → L → JlX (StepRangeLen T R S L))
    (r : StepRangeLen T U V I) (out : StepRangeLen T R S L),
    (∀ ref st n o result, make ref st n o = .ok result →
      result.ref = ref ∧ result.step = st ∧ result.len = n ∧ result.offset = o) →
    convertSRLIntegerCounted convertR convertS convertL length make r = .ok out →
    ∃ ref st n o, convertR r.ref = .ok ref ∧ convertS r.step = .ok st ∧
      convertL (length r) = .ok n ∧ convertL r.offset = .ok o ∧
      out.ref = ref ∧ out.step = st ∧ out.len = n ∧ out.offset = o

theorem countedSRLConversion_proven : CountedSRLConversion := by
  intro T U V R S L I convertR convertS convertL length make r out hmake h
  unfold convertSRLIntegerCounted at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  rename_i ref href
  split at h; · cases h
  rename_i st hst
  split at h; · cases h
  rename_i n hn
  split at h; · cases h
  rename_i o ho
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hmake ref st n o out h
  exact ⟨ref, st, n, o, href, hst, hn, ho, hr1, hr2, hr3, hr4⟩

def IntegerRangeSRLConversion : Prop :=
  ∀ {T R S L Q I : Type}
    (first : Q → I) (step : Q → I) (length : Q → I)
    (convertR : I → JlX R) (convertS : I → JlX S) (convertL : I → JlX L)
    (one : L) (make : R → S → L → L → JlX (StepRangeLen T R S L))
    (r : Q) (out : StepRangeLen T R S L),
    (∀ ref st n o result, make ref st n o = .ok result →
      result.ref = ref ∧ result.step = st ∧ result.len = n ∧ result.offset = o) →
    convertSRLIntegerRange first step length convertR convertS convertL one make r = .ok out →
    ∃ ref st n, convertR (first r) = .ok ref ∧ convertS (step r) = .ok st ∧
      convertL (length r) = .ok n ∧ out.ref = ref ∧ out.step = st ∧ out.len = n ∧ out.offset = one

theorem integerRangeSRLConversion_proven : IntegerRangeSRLConversion := by
  intro T R S L Q I first step length convertR convertS convertL one make r out hmake h
  unfold convertSRLIntegerRange at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  rename_i ref href
  split at h; · cases h
  rename_i st hst
  split at h; · cases h
  rename_i n hn
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hmake ref st n one out h
  exact ⟨ref, st, n, href, hst, hn, hr1, hr2, hr3, hr4⟩

def FloatSRLConversionLength : Prop :=
  ∀ {F I L N T R S Q : Type}
    (ops : FloatRangeOps F I L N (StepRangeLen T R S L)) (type : Type)
    (lenPlusZero : L → L) (round : F → JlX L) (clampInt : L → L → L → L)
    (float : I → F) (offsetToInt : L → I) (one : L)
    (first step : Q → F) (length : Q → L) (exact : F → I → I → Bool)
    (fallback : Q → JlX (StepRangeLen T R S L))
    (r : Q) (out : StepRangeLen T R S L),
    (∀ startN stepN n den result,
      floatrange ops type lenPlusZero round clampInt float offsetToInt one
        startN stepN n den = .ok result → result.len = lenPlusZero n) →
    (∀ range result, fallback range = .ok result →
      result.len = lenPlusZero (length range)) →
    convertSRLFloatRange ops type lenPlusZero round clampInt float offsetToInt one
      first step length exact fallback r = .ok out → out.len = lenPlusZero (length r)

theorem floatSRLConversionLength_proven : FloatSRLConversionLength := by
  intro F I L N T R S Q ops type lenPlusZero round clampInt float offsetToInt one
    first step length exact fallback r out hfr hfb h
  unfold convertSRLFloatRange at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h; · cases h
    split at h
    · exact hfr _ _ _ _ out h
    · exact hfb r out h
  · exact hfb r out h

def FallbackSRLConversion : Prop :=
  ∀ {T R S L U V W I : Type} (convertR : V → JlX R) (convertS : W → JlX S)
    (convertL : I → JlX L) (length : StepRangeLen U V W I → I)
    (make : R → S → L → L → JlX (StepRangeLen T R S L))
    (r : StepRangeLen U V W I) (out : StepRangeLen T R S L),
    (∀ a b n o result, make a b n o = .ok result →
      result.ref = a ∧ result.step = b ∧ result.len = n ∧ result.offset = o) →
    convertSRLFallback convertR convertS convertL length make r = .ok out →
    ∃ ref st n o, convertR r.ref = .ok ref ∧ convertS r.step = .ok st ∧
      convertL (length r) = .ok n ∧ convertL r.offset = .ok o ∧
      out.ref = ref ∧ out.step = st ∧ out.len = n ∧ out.offset = o

theorem fallbackSRLConversion_proven : FallbackSRLConversion := by
  intro T R S L U V W I convertR convertS convertL length make r out hmake h
  unfold convertSRLFallback at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  rename_i ref href
  split at h; · cases h
  rename_i st hst
  split at h; · cases h
  rename_i n hn
  split at h; · cases h
  rename_i o ho
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hmake ref st n o out h
  exact ⟨ref, st, n, o, href, hst, hn, ho, hr1, hr2, hr3, hr4⟩

def FallbackRangeConversion : Prop :=
  ∀ {T R S L Q I : Type} (first : Q → I) (step : Q → I) (length : Q → I)
    (convertR : I → JlX R) (convertS : I → JlX S) (convertL : I → JlX L)
    (one : L) (make : R → S → L → L → JlX (StepRangeLen T R S L)) (r : Q)
    (out : StepRangeLen T R S L),
    (∀ a b n o result, make a b n o = .ok result →
      result.ref = a ∧ result.step = b ∧ result.len = n ∧ result.offset = o) →
    convertRangeFallback first step length convertR convertS convertL one make r = .ok out →
    ∃ ref st n, convertR (first r) = .ok ref ∧ convertS (step r) = .ok st ∧
      convertL (length r) = .ok n ∧ out.ref = ref ∧ out.step = st ∧ out.len = n ∧ out.offset = one

theorem fallbackRangeConversion_proven : FallbackRangeConversion := by
  intro T R S L Q I first step length convertR convertS convertL one make r out hmake h
  unfold convertRangeFallback at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · cases h
  rename_i ref href
  split at h; · cases h
  rename_i st hst
  split at h; · cases h
  rename_i n hn
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hmake ref st n one out h
  exact ⟨ref, st, n, href, hst, hn, hr1, hr2, hr3, hr4⟩

def TwiceConversionsComplete : Prop :=
  (∀ {T R S L : Type} (r : StepRangeLen T R S L), stepRangeIdentity r = r) ∧
  (∀ {T R S L R' S' L' : Type} (conv : StepRangeLen T R' S' L' → JlX (StepRangeLen T R S L))
    (r : StepRangeLen T R' S' L'), stepRangeConvert conv r = conv r) ∧
  (∀ {T R S L : Type} (conv : StepRangeLen T R S L → JlX (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int))
    (r : StepRangeLen T R S L), stepRangeFloat64Convert conv r = conv r) ∧
  (∀ {T U R S L : Type} (conv : StepRangeLen U R S L → JlX (StepRangeLen T F64 F64 Int))
    (r : StepRangeLen U R S L), stepRangeIEEEConvert conv r = conv r) ∧
  (∀ {Q : Type} (r : Q) (conv : Q → JlX (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int)),
    stepRangeFloat64AbstractConvert r conv = conv r) ∧
  (∀ {T Q : Type} (r : Q) (conv : Q → JlX (StepRangeLen T F64 F64 Int)),
    stepRangeIEEEAbstractConvert (R := Unit) r conv = conv r) ∧
  CountedSRLConversion ∧ IntegerRangeSRLConversion ∧ FloatSRLConversionLength ∧
  FallbackSRLConversion ∧ FallbackRangeConversion

theorem twiceConversionsComplete_proven : TwiceConversionsComplete :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   countedSRLConversion_proven, integerRangeSRLConversion_proven, floatSRLConversionLength_proven,
   fallbackSRLConversion_proven, fallbackRangeConversion_proven⟩

/-! ## Group 2: Dekker arithmetic, TwicePrecision operations, nbitslen, sumpair, rat, lcm_unchecked (20 proven entries) -/

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

theorem jint_eq {t : IntTy} {x y : JInt t} (h : x.val = y.val) : x = y := Subtype.ext h

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

theorem toJInt_ofInt_val (t : IntTy) (z : Int) :
    (JuliaLean.C.toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  unfold JuliaLean.C.toJInt JInt.wrap
  apply wrapInt_congr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := two_pow_pos_int t.bits; omega)), Int.emod_emod]

theorem neg_int_val {t : IntTy} (x : JInt t) :
    (JuliaLean.base.int.neg x).val = wrapInt t (-x.val) := by
  simp only [JuliaLean.base.int.neg, JuliaLean.base.int.neg_int, JuliaLean.C.jlNegInt, JuliaLean.C.fromJInt]
  rw [← BitVec.ofInt_neg, toJInt_ofInt_val]

theorem add_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.add x y).val = wrapInt t (x.val + y.val) := by
  simp only [JuliaLean.base.int.add, JuliaLean.base.int.add_int, JuliaLean.C.jlAddInt, JuliaLean.C.fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

theorem sub_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.sub x y).val = wrapInt t (x.val - y.val) := by
  simp only [JuliaLean.base.int.sub, JuliaLean.base.int.sub_int, JuliaLean.C.jlSubInt, JuliaLean.C.fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem mul_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.mul x y).val = wrapInt t (x.val * y.val) := by
  simp only [JuliaLean.base.int.mul, JuliaLean.base.int.mul_int, JuliaLean.C.jlMulInt, JuliaLean.C.fromJInt]
  rw [← BitVec.ofInt_mul, toJInt_ofInt_val]

theorem mulSame_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.mulSame x y).val = wrapInt t (x.val * y.val) := by
  cases t <;> exact mul_int_val x y

theorem neg_neg_jint {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.neg (JuliaLean.base.int.neg x) = x := by
  apply jint_eq
  rw [neg_int_val, neg_int_val, ← wrapInt_val x]
  apply wrapInt_congr
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem canonicalize2_jint_lo {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.add (JuliaLean.base.int.sub x (JuliaLean.base.int.add x y)) y =
      JuliaLean.base.int.lit t 0 := by
  apply jint_eq
  rw [add_int_val, sub_int_val, add_int_val]
  show wrapInt t (wrapInt t (x.val - wrapInt t (x.val + y.val)) + y.val) = wrapInt t 0
  apply wrapInt_congr
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem add_zero_jint {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.add x (JuliaLean.base.int.lit t 0) = x := by
  apply jint_eq
  rw [add_int_val, ← wrapInt_val x]
  apply wrapInt_congr
  cases t <;> simp only [JuliaLean.base.int.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem add_comm_jint {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.add x y = JuliaLean.base.int.add y x := by
  apply jint_eq
  rw [add_int_val, add_int_val, Int.add_comm]

theorem add_neg_self_jint {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.add x (JuliaLean.base.int.neg x) = JuliaLean.base.int.lit t 0 := by
  apply jint_eq
  rw [add_int_val, neg_int_val]
  show wrapInt t (x.val + wrapInt t (-x.val)) = wrapInt t 0
  apply wrapInt_congr
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem sub_eq_add_neg_jint {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.sub x y = JuliaLean.base.int.add x (JuliaLean.base.int.neg y) := by
  apply jint_eq
  rw [sub_int_val, add_int_val, neg_int_val]
  apply wrapInt_congr
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem sub_self_jint {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.sub x x = JuliaLean.base.int.lit t 0 := by
  rw [sub_eq_add_neg_jint, add_neg_self_jint]

theorem ltSame_irrefl {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.ltSame x x = false := by
  unfold JuliaLean.base.int.ltSame
  split <;> simp [JuliaLean.base.int.lt_BitSigned, JuliaLean.base.int.lt_BitUnsigned,
    JuliaLean.base.int.slt_int, JuliaLean.base.int.ult_int,
    JuliaLean.C.jlSltInt, JuliaLean.C.jlUltInt]

theorem fmt_width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]

theorem fl_ofBits_toBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem fl_ext_toBits {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← fl_ofBits_toBits x, ← fl_ofBits_toBits y, h]

theorem fl_bits_split {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := fmt_width_pow f
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
    simp [hs]

theorem fl_neg_toBits {f : Fmt} (x : Fl f) :
    (Fl.neg x).toBits =
      if x.toBits ≥ 2 ^ (f.eb + f.sb) then x.toBits - 2 ^ (f.eb + f.sb)
      else x.toBits + 2 ^ (f.eb + f.sb) := by
  obtain ⟨⟨v, hv⟩⟩ := x
  have hw := fmt_width_pow f
  unfold Fl.neg Fl.signbit Fl.toBits Fl.ofBits
  dsimp only
  by_cases hs : v ≥ 2 ^ (f.eb + f.sb)
  · simp only [hs, decide_true, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)

theorem fl_neg_neg {f : Fmt} (x : Fl f) : Fl.neg (Fl.neg x) = x := by
  have hx : x.toBits < 2 * 2 ^ (f.eb + f.sb) := fmt_width_pow f ▸ x.bits.isLt
  apply fl_ext_toBits
  rw [fl_neg_toBits, fl_neg_toBits]
  split <;> split <;> omega

theorem f64_neg_neg (x : F64) :
    JuliaLean.base.float.neg_IEEEFloat (JuliaLean.base.float.neg_IEEEFloat x) = x := by
  have h1 : (JuliaLean.base.float.FTy.f64.fmt == half) = false := rfl
  have h2 : (JuliaLean.base.float.FTy.f64.fmt == JuliaLean.C.bfloat) = false := rfl
  have hneg : ∀ y : F64, JuliaLean.base.float.neg_IEEEFloat y = Fl.neg y := by
    intro y
    unfold JuliaLean.base.float.neg_IEEEFloat JuliaLean.base.float.neg_float
      JuliaLean.C.jlNegFloat JuliaLean.C.unaryFloat JuliaLean.C.finishFloat
    simp only [h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hneg (JuliaLean.base.float.neg_IEEEFloat x), hneg x]
  exact fl_neg_neg x

theorem lt_irrefl_fv {T : JuliaLean.base.float.FTy} (x : JuliaLean.base.float.FV T) :
    JuliaLean.base.float.lt_IEEEFloat x x = false := by
  unfold JuliaLean.base.float.lt_IEEEFloat JuliaLean.base.float.lt_float
    JuliaLean.C.jlLtFloat Fl.lt
  simp [bne_self_eq_false, Nat.lt_irrefl]

-- 1. TruncbitsIdentity (rangescov-truncbits-identity)
theorem fromJInt_reinterpret_Unsigned {T : JuliaLean.base.float.FTy} (x : JuliaLean.base.float.FV T) :
    JuliaLean.C.fromJInt (JuliaLean.base.float.reinterpret_Unsigned x) =
      BitVec.ofNat T.uintTy.bits x.toBits := by
  have hbits : T.uintTy.bits = T.fmt.width := by cases T <;> rfl
  have hx : x.toBits < 2 ^ T.uintTy.bits := hbits ▸ x.bits.isLt
  have hval : (JuliaLean.base.float.reinterpret_Unsigned x).val = (x.toBits : Int) := by
    cases T <;>
      simp only [JuliaLean.base.float.reinterpret_Unsigned,
        JuliaLean.base.float.reinterpret_Unsigned_Float64,
        JuliaLean.base.float.reinterpret_Unsigned_Float32,
        JuliaLean.base.float.reinterpret_Unsigned_Float16,
        JuliaLean.base.float.reinterpret_Int_Float,
        JuliaLean.base.float.bitcast_from_float,
        JuliaLean.base.int.bitcastFloat, JuliaLean.C.jlBitcast,
        JuliaLean.C.toJInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits,
        JuliaLean.base.float.FTy.uintTy, Bool.false_eq_true, ↓reduceIte,
        BitVec.toNat_ofNat] at hx ⊢ <;>
      omega
  apply BitVec.eq_of_toNat_eq
  simp only [JuliaLean.C.fromJInt, hval, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

def TruncbitsIdentity : Prop :=
  (∀ (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV T),
    truncbitsIEEE (bitOpsIEEE T) x (JuliaLean.base.int.lit .i64 0) = x) ∧
  (∀ (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV T),
    truncmaskIEEE (bitOpsIEEE T) x (JuliaLean.base.int.typemax T.uintTy) = x) ∧
  (∀ (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV T),
    truncmaskIEEE (bitOpsIEEE T) x (JuliaLean.base.int.lit T.uintTy 0) =
      JuliaLean.base.float.zero_float T) ∧
  (∀ {α M N : Type} (x : α) (m : M) (nb : N),
    truncmaskGeneric x m = x ∧ truncbitsGeneric x nb = x)

theorem truncmask_typemax (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV T) :
    truncmaskIEEE (bitOpsIEEE T) x (JuliaLean.base.int.typemax T.uintTy) = x := by
  have htm : JuliaLean.C.fromJInt (JuliaLean.base.int.typemax T.uintTy) =
      BitVec.allOnes T.uintTy.bits := by cases T <;> decide +kernel
  have hbits : T.uintTy.bits = T.fmt.width := by cases T <;> rfl
  have hx : x.toBits < 2 ^ T.uintTy.bits := hbits ▸ x.bits.isLt
  unfold truncmaskIEEE bitOpsIEEE
  dsimp only
  have hband : JuliaLean.base.int.band (JuliaLean.base.int.typemax T.uintTy)
      (JuliaLean.base.float.reinterpret_Unsigned x) =
      JuliaLean.base.float.reinterpret_Unsigned x := by
    unfold JuliaLean.base.int.band JuliaLean.base.int.and_int JuliaLean.C.jlAndInt
    rw [htm, BitVec.allOnes_and]
    apply jint_eq
    rw [JuliaLean.C.fromJInt, toJInt_ofInt_val, wrapInt_val]
  rw [hband]
  unfold JuliaLean.base.float.reinterpret_Float_Int JuliaLean.base.float.bitcast_to_float JuliaLean.C.jlBitcast
  rw [fromJInt_reinterpret_Unsigned, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, fl_ofBits_toBits]

theorem truncbitsIdentity_proven : TruncbitsIdentity := by
  refine ⟨?_, truncmask_typemax, ?_, fun _ _ _ => ⟨rfl, rfl⟩⟩
  · intro T x
    have hshl : JuliaLean.base.int.shl_Int (JuliaLean.base.int.typemax T.uintTy)
        (JuliaLean.base.int.lit .i64 0) = JuliaLean.base.int.typemax T.uintTy := by
      cases T <;> decide +kernel
    unfold truncbitsIEEE
    show truncmaskIEEE (bitOpsIEEE T) x
      (JuliaLean.base.int.shl_Int (JuliaLean.base.int.typemax T.uintTy) (JuliaLean.base.int.lit .i64 0)) = x
    rw [hshl]
    exact truncmask_typemax T x
  · intro T x
    have hz : JuliaLean.C.fromJInt (JuliaLean.base.int.lit T.uintTy 0) = 0#T.uintTy.bits := by
      cases T <;> decide +kernel
    unfold truncmaskIEEE bitOpsIEEE
    dsimp only
    have hband : JuliaLean.base.int.band (JuliaLean.base.int.lit T.uintTy 0)
        (JuliaLean.base.float.reinterpret_Unsigned x) =
        JuliaLean.base.int.lit T.uintTy 0 := by
      unfold JuliaLean.base.int.band JuliaLean.base.int.and_int JuliaLean.C.jlAndInt
      rw [hz, BitVec.zero_and]
      cases T <;> decide +kernel
    rw [hband]
    cases T <;> decide +kernel

-- 2. Mul12IntExact (rangescov-mul12-int)
def intArithmetic : Arithmetic Int := {
  add := (· + ·), sub := (· - ·), mul := (· * ·), div := fun a b => a.tdiv b,
  neg := (- ·), abs := fun a => if a < 0 then -a else a,
  lt := fun a b => decide (a < b), le := fun a b => decide (a ≤ b),
  gt := fun a b => decide (a > b), eq := fun a b => decide (a = b),
  zero := 0, one := 1, iszero := fun a => decide (a = 0),
  isfinite := fun _ => true, twoMul := fun a b => (a * b, 0),
  fma := fun a b c => a * b + c, frexp := fun a => (a, 0), ldexp := fun a _ => a,
  truncInt := fun a => .ok a, inv := fun a => 1 / a
}

def intOps : IntegerOps Int := {
  add := (· + ·), sub := (· - ·), mul := (· * ·), div := fun a b => a.tdiv b,
  rem := fun a b => a.tmod b, neg := (- ·),
  abs := fun a => if a < 0 then -a else a, max := max,
  lt := fun a b => decide (a < b), le := fun a b => decide (a ≤ b),
  eq := fun a b => decide (a = b), isEven := fun a => decide (a.tmod 2 = 0),
  shiftRightOne := fun a => Int.fdiv a 2,
  gcd := fun a b => Int.ofNat (Nat.gcd a.natAbs b.natAbs), zero := 0, one := 1
}

def Mul12IntExact : Prop :=
  (∀ x y : Int,
    let p := mul12Generic intArithmetic x y
    p.1 + p.2 = x * y ∧ p.2 = 0) ∧
  (∀ (t : IntTy) (x y : JInt t),
    let p := mul12Generic (jintArith t) x y
    p.1 = JuliaLean.base.int.mulSame x y ∧ p.2 = JuliaLean.base.int.lit t 0) ∧
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    let p := mul12Mixed JuliaLean.base.int.promoteSameSign
      (mul12Generic (jintArith (s.promote t))) x y
    p.1 = JuliaLean.base.int.mulSame (JuliaLean.base.int.widenTo (s.promote t) x)
      (JuliaLean.base.int.widenTo (s.promote t) y) ∧
    p.2 = JuliaLean.base.int.lit (s.promote t) 0)

theorem mul12IntExact_proven : Mul12IntExact := by
  refine ⟨fun x y => by simp [mul12Generic, intArithmetic],
    fun t x y => ⟨rfl, rfl⟩,
    fun s t x y => ⟨rfl, rfl⟩⟩

-- 3. TpNegInvolution (rangescov-tp-neg-involution)
def TpNegInvolution : Prop :=
  (∀ (x : TwicePrecision F64), negTp f64Arithmetic (negTp f64Arithmetic x) = x) ∧
  (∀ (t : IntTy) (x : TwicePrecision (JInt t)),
    negTp (jintArith t) (negTp (jintArith t) x) = x) ∧
  (∀ {T : Type} (ops : Arithmetic T) (x : TwicePrecision T),
    (∀ v, ops.neg (ops.neg v) = v) → negTp ops (negTp ops x) = x)

theorem tpNegInvolution_proven : TpNegInvolution := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; cases x; simp [negTp, f64Arithmetic, fvArithmetic, f64_neg_neg]
  · intro t x; cases x; simp [negTp, jintArith, neg_neg_jint]
  · intro T ops x h; cases x; simp [negTp, h]

-- 4. TpLtIrrefl (rangescov-tp-lt-irrefl)
def TpLtIrrefl : Prop :=
  (∀ (T : JuliaLean.base.float.FTy) (x : TwicePrecision (JuliaLean.base.float.FV T)),
    tpLt (fvArithmetic T) x x = false) ∧
  (∀ (t : IntTy) (x : TwicePrecision (JInt t)),
    tpLt (jintArith t) x x = false) ∧
  (∀ {T : Type} (ops : Arithmetic T) (x : TwicePrecision T),
    (∀ v, ops.lt v v = false) → tpLt ops x x = false)

theorem tpLtIrrefl_proven : TpLtIrrefl := by
  refine ⟨?_, ?_, ?_⟩
  · intro T x; simp [tpLt, fvArithmetic, lt_irrefl_fv]
  · intro t x; simp [tpLt, jintArith, ltSame_irrefl]
  · intro T ops x h; simp [tpLt, h]

-- 5. IsbetweenSymmetric (rangescov-isbetween-symmetric)
def IsbetweenSymmetric : Prop :=
  ∀ {T : Type} (ops : Arithmetic T) (a x b : T),
    isbetween ops a x b = isbetween ops b x a

theorem isbetweenSymmetric_proven : IsbetweenSymmetric := by
  intro T ops a x b
  unfold isbetween
  cases (ops.le a x && ops.le x b) <;> cases (ops.le b x && ops.le x a) <;> rfl

-- 6. SumpairProduct (rangescov-sumpair-product)
def SumpairProduct : Prop :=
  ∀ n : Int, 0 ≤ n → n < 2^62 →
    let p := sumpair intOps n
    2 * p.1 * p.2 = n * (n + 1)

theorem sumpairProduct_proven : SumpairProduct := by
  intro n h0 _
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n = Int.ofNat k := ⟨n.toNat, (Int.toNat_of_nonneg h0).symm⟩
  unfold sumpair intOps
  dsimp only
  have htmod : (Int.ofNat k).tmod 2 = Int.ofNat (k % 2) := rfl
  have hfdiv1 : Int.fdiv (Int.ofNat k) 2 = Int.ofNat (k / 2) := by cases k <;> rfl
  have hcond : decide ((Int.ofNat k).tmod 2 = 0) = decide (k % 2 = 0) := by
    rw [htmod]
    cases k % 2 <;> rfl
  simp only [hfdiv1, hcond]
  by_cases he : k % 2 = 0
  · simp only [he, decide_true, ↓reduceIte]
    change Int.ofNat (2 * (k + 1) * (k / 2)) = Int.ofNat (k * (k + 1))
    congr 1
    have h2 : 2 * (k / 2) = k := by omega
    calc 2 * (k + 1) * (k / 2) = (2 * (k / 2)) * (k + 1) := by ac_rfl
      _ = k * (k + 1) := by rw [h2]
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
    change Int.ofNat (2 * k * ((k + 1) / 2)) = Int.ofNat (k * (k + 1))
    congr 1
    have h2 : 2 * ((k + 1) / 2) = k + 1 := by omega
    calc 2 * k * ((k + 1) / 2) = k * (2 * ((k + 1) / 2)) := by ac_rfl
      _ = k * (k + 1) := by rw [h2]
-- 7. Canonicalize2ExactSum (twiceprecision-canonicalize2-exact-sum)
def fractionSub (x y : Int × Int) : Int × Int :=
  (x.1 * y.2 - y.1 * x.2, x.2 * y.2)

def exactFloatAdd (x y : F64) : Prop :=
  fractionEq (floatFraction (JuliaLean.base.float.add_IEEEFloat x y))
    (fractionAdd (floatFraction x) (floatFraction y))

def exactFloatSub (x y : F64) : Prop :=
  fractionEq (floatFraction (JuliaLean.base.float.sub_IEEEFloat x y))
    (fractionSub (floatFraction x) (floatFraction y))

theorem toRat_den_pos {f : Fmt} (x : Fl f) (h : x.isfinite = true) : 0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases Decidable.em ((if x.expField == 0 then 1 - (f.bias : Int) - f.sb else (x.expField : Int) - f.bias - f.sb) ≥ 0) with hp | hp
  · simp only [hp, ↓reduceIte]; decide
  · simp only [hp, ↓reduceIte]; exact Nat.two_pow_pos _

theorem floatFraction_den_pos (x : F64) (h : x.isfinite = true) : 0 < (floatFraction x).2 := by
  have hd : 0 < x.toRat.2 := toRat_den_pos x h
  change 0 < (x.toRat.2 : Int)
  omega

def Canonicalize2ExactSum : Prop :=
  (∀ big little : Int,
    let p := canonicalize2 (· + ·) (· - ·) big little
    p.1 + p.2 = big + little ∧ p.2 = 0) ∧
  (∀ (t : IntTy) (big little : JInt t),
    let p := canonicalize2 JuliaLean.base.int.add JuliaLean.base.int.sub big little
    p.1 = JuliaLean.base.int.add big little ∧ p.2 = JuliaLean.base.int.lit t 0 ∧
    JuliaLean.base.int.add p.1 p.2 = JuliaLean.base.int.add big little) ∧
  (∀ x y : F64,
    (JuliaLean.base.float.sub_IEEEFloat x (JuliaLean.base.float.add_IEEEFloat x y)).isfinite = true →
    exactFloatSub x (JuliaLean.base.float.add_IEEEFloat x y) →
    exactFloatAdd (JuliaLean.base.float.sub_IEEEFloat x (JuliaLean.base.float.add_IEEEFloat x y)) y →
    let p := canonicalize2 JuliaLean.base.float.add_IEEEFloat JuliaLean.base.float.sub_IEEEFloat x y
    exactFloatSum p.1 p.2 x y)

theorem fraction_cancel_lemma (nhi dhi nb db ns ds na da nlo dlo : Int)
    (hdd : 0 < ds)
    (hsub : ns * (dhi * db) = (nhi * db - nb * dhi) * ds)
    (hadd : na * (ds * dlo) = (ns * dlo + nlo * ds) * da) :
    (nb * da + na * db) * (dhi * dlo) = (nhi * dlo + nlo * dhi) * (db * da) := by
  let A := nb * da * dhi * dlo * ds
  let B := nhi * dlo * db * da * ds
  let C := nlo * dhi * db * da * ds
  have h1 : (na * db) * (dhi * dlo) * ds = (na * (ds * dlo)) * (dhi * db) := by ac_rfl
  have h2 : ((ns * dlo + nlo * ds) * da) * (dhi * db) = (ns * (dhi * db)) * (dlo * da) + C := by
    dsimp only [C]; simp only [Int.add_mul]; ac_rfl
  have h3 : ((nhi * db - nb * dhi) * ds) * (dlo * da) = B - A := by
    dsimp only [A, B]; simp only [Int.sub_mul]; ac_rfl
  have h4 : (nb * da + na * db) * (dhi * dlo) * ds = A + (na * db) * (dhi * dlo) * ds := by
    dsimp only [A]; simp only [Int.add_mul]; ac_rfl
  have h5 : ((nhi * dlo + nlo * dhi) * (db * da)) * ds = B + C := by
    dsimp only [B, C]; simp only [Int.add_mul]; ac_rfl
  rw [h1, hadd, h2, hsub, h3] at h4
  have hmul : ((nb * da + na * db) * (dhi * dlo)) * ds =
      ((nhi * dlo + nlo * dhi) * (db * da)) * ds := by omega
  exact Int.eq_of_mul_eq_mul_right (by omega) hmul

theorem canonicalize2ExactSum_proven : Canonicalize2ExactSum := by
  refine ⟨?_, ?_, ?_⟩
  · intro big little
    dsimp only [canonicalize2]
    omega
  · intro t big little
    dsimp only [canonicalize2]
    rw [canonicalize2_jint_lo, add_zero_jint]
    exact ⟨rfl, rfl, rfl⟩
  · intro x y hfin hsub hadd
    unfold exactFloatSub fractionSub fractionEq at hsub
    unfold exactFloatAdd fractionAdd fractionEq at hadd
    unfold canonicalize2 exactFloatSum fractionAdd fractionEq
    dsimp only at hsub hadd ⊢
    have hdd := floatFraction_den_pos _ hfin
    exact fraction_cancel_lemma _ _ _ _ _ _ _ _ _ _ hdd hsub hadd

-- 8. Add12ExactSum (twiceprecision-add12-exact-sum)
def Add12ExactSum : Prop :=
  (∀ x y : Int,
    let p := add12Same intArithmetic JuliaLean.base.int.ifelse x y
    p.1 + p.2 = x + y ∧ p.2 = 0) ∧
  (∀ (t : IntTy) (x y : JInt t),
    let p := add12Same (jintArith t) JuliaLean.base.int.ifelse x y
    JuliaLean.base.int.add p.1 p.2 = JuliaLean.base.int.add x y ∧ p.2 = JuliaLean.base.int.lit t 0) ∧
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t),
    let p := add12Mixed JuliaLean.base.int.promoteSameSign (jintArith (s.promote t))
      JuliaLean.base.int.ifelse x y
    JuliaLean.base.int.add p.1 p.2 =
      JuliaLean.base.int.add (JuliaLean.base.int.widenTo (s.promote t) x)
        (JuliaLean.base.int.widenTo (s.promote t) y) ∧
    p.2 = JuliaLean.base.int.lit (s.promote t) 0) ∧
  (∀ (T : JuliaLean.base.float.FTy) (x y : JuliaLean.base.float.FV T),
    JuliaLean.base.float.abs_IEEEFloat x ≠ JuliaLean.base.float.abs_IEEEFloat y →
    (JuliaLean.base.float.abs_IEEEFloat x).isnan = false →
    (JuliaLean.base.float.abs_IEEEFloat y).isnan = false →
    add12Same (fvArithmetic T) JuliaLean.base.int.ifelse x y =
      add12Same (fvArithmetic T) JuliaLean.base.int.ifelse y x)

theorem lt_trichotomy_pos_mag {f : Fmt} (a b : Fl f)
    (hne : a ≠ b) (hna : a.isnan = false) (hnb : b.isnan = false)
    (hsa : a.signbit = false) (hsb : b.signbit = false) :
    Fl.lt a b = !Fl.lt b a := by
  have heq : a.toBits ≠ b.toBits := fun h => hne (fl_ext_toBits h)
  unfold Fl.lt
  simp only [hna, hnb, hsa, hsb, Bool.false_or, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [Bool.and_comm b.iszero a.iszero]
  by_cases hz : (a.iszero && b.iszero) = true
  · simp only [Fl.iszero, Bool.and_eq_true, beq_iff_eq] at hz
    have ha := (fl_bits_split a).1
    have hb := (fl_bits_split b).1
    simp only [hsa, hsb, Bool.false_eq_true, ↓reduceIte, hz.1, hz.2] at ha hb
    omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : a.toBits < b.toBits
    · have hgt : ¬ (b.toBits < a.toBits) := by omega
      simp [hlt, hgt]
    · have hgt : b.toBits < a.toBits := by omega
      simp [hlt, hgt]

theorem ofBits_magnitude_signbit {f : Fmt} (y : Fl f) :
    (Fl.ofBits (f := f) y.magnitude).signbit = false := by
  have hw : 0 < 2 ^ (f.eb + f.sb) := Nat.two_pow_pos _
  have hpow := fmt_width_pow f
  have hlt : y.magnitude < 2 ^ (f.eb + f.sb) := Nat.mod_lt _ hw
  have htb : (Fl.ofBits (f := f) y.magnitude).toBits = y.magnitude := by
    unfold Fl.toBits Fl.ofBits
    exact Nat.mod_eq_of_lt (by omega)
  unfold Fl.signbit
  rw [htb]
  exact decide_eq_false (by omega)

theorem abs_signbit_false {T : JuliaLean.base.float.FTy} (x : JuliaLean.base.float.FV T) :
    (JuliaLean.base.float.abs_IEEEFloat x).signbit = false := by
  have h1 : (T.fmt == JuliaLean.C.bfloat) = false := by cases T <;> rfl
  unfold JuliaLean.base.float.abs_IEEEFloat JuliaLean.base.float.abs_float
    JuliaLean.C.jlAbsFloat JuliaLean.C.unaryFloat JuliaLean.C.finishFloat
  rw [h1, Bool.false_and]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  exact ofBits_magnitude_signbit _

theorem add12Same_jint (t : IntTy) (x y : JInt t) :
    let p := add12Same (jintArith t) JuliaLean.base.int.ifelse x y
    JuliaLean.base.int.add p.1 p.2 = JuliaLean.base.int.add x y ∧
    p.2 = JuliaLean.base.int.lit t 0 := by
  unfold add12Same JuliaLean.base.int.ifelse
  rcases Decidable.em ((jintArith t).gt ((jintArith t).abs y) ((jintArith t).abs x) = true) with h | h
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    dsimp only [jintArith, canonicalize2]
    rw [canonicalize2_jint_lo, add_zero_jint, add_comm_jint y x]
    exact ⟨rfl, rfl⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    dsimp only [jintArith, canonicalize2]
    rw [canonicalize2_jint_lo, add_zero_jint]
    exact ⟨rfl, rfl⟩

theorem add12Same_int_eq (x y : Int) :
    add12Same intArithmetic JuliaLean.base.int.ifelse x y = (x + y, 0) := by
  unfold add12Same JuliaLean.base.int.ifelse
  rcases Decidable.em (intArithmetic.gt (intArithmetic.abs y) (intArithmetic.abs x) = true) with h | h <;>
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    dsimp only [intArithmetic, canonicalize2]
    ext <;> dsimp only <;> omega
theorem add12ExactSum_proven : Add12ExactSum := by
  refine ⟨?_, add12Same_jint, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [add12Same_int_eq]
    exact ⟨by omega, rfl⟩
  · intro s t x y
    exact add12Same_jint (s.promote t)
      (JuliaLean.base.int.widenTo (s.promote t) x)
      (JuliaLean.base.int.widenTo (s.promote t) y)
  · intro T x y hne hna hnb
    unfold add12Same JuliaLean.base.int.ifelse fvArithmetic
    dsimp only
    have htri := lt_trichotomy_pos_mag (JuliaLean.base.float.abs_IEEEFloat x)
      (JuliaLean.base.float.abs_IEEEFloat y) hne hna hnb (abs_signbit_false x) (abs_signbit_false y)
    show (let p := if Fl.lt (JuliaLean.base.float.abs_IEEEFloat x) (JuliaLean.base.float.abs_IEEEFloat y) = true then (y, x) else (x, y);
      canonicalize2 JuliaLean.base.float.add_IEEEFloat JuliaLean.base.float.sub_IEEEFloat p.1 p.2) =
      (let p := if Fl.lt (JuliaLean.base.float.abs_IEEEFloat y) (JuliaLean.base.float.abs_IEEEFloat x) = true then (x, y) else (y, x);
      canonicalize2 JuliaLean.base.float.add_IEEEFloat JuliaLean.base.float.sub_IEEEFloat p.1 p.2)
    rw [htri]
    cases Fl.lt (JuliaLean.base.float.abs_IEEEFloat y) (JuliaLean.base.float.abs_IEEEFloat x) <;> rfl

-- 9. Mul12ProductExact (twiceprecision-mul12-exact-product)
def Mul12ProductExact : Prop :=
  (∀ (T : JuliaLean.base.float.FTy) (x y : JuliaLean.base.float.FV T),
    (mul12IEEE (fvArithmetic T) JuliaLean.base.int.ifelse x y).1 =
      JuliaLean.base.float.mul_IEEEFloat x y ∧
    (JuliaLean.base.float.isfinite_IEEEFloat (JuliaLean.base.float.mul_IEEEFloat x y) = false →
      mul12IEEE (fvArithmetic T) JuliaLean.base.int.ifelse x y =
        (JuliaLean.base.float.mul_IEEEFloat x y, JuliaLean.base.float.mul_IEEEFloat x y))) ∧
  (∀ x y : F64,
    let h := JuliaLean.base.float.mul_IEEEFloat x y
    let l := JuliaLean.C.jlFmaFloat x y (JuliaLean.base.float.neg_IEEEFloat h)
    JuliaLean.base.float.isfinite_IEEEFloat h = true →
    fractionEq (fractionAdd (floatFraction h) (floatFraction l))
      (fractionMul (floatFraction x) (floatFraction y)) →
    let p := mul12IEEE f64Arithmetic JuliaLean.base.int.ifelse x y
    fractionEq (fractionAdd (floatFraction p.1) (floatFraction p.2))
      (fractionMul (floatFraction x) (floatFraction y)))

theorem mul12ProductExact_proven : Mul12ProductExact := by
  refine ⟨?_, ?_⟩
  · intro T x y
    refine ⟨?_, ?_⟩
    · unfold mul12IEEE fvArithmetic JuliaLean.base.int.ifelse
      dsimp only
      split <;> rfl
    · intro hnf
      unfold mul12IEEE fvArithmetic JuliaLean.base.int.ifelse
      simp [hnf]
  · intro x y h l hfin hprod
    unfold mul12IEEE f64Arithmetic fvArithmetic JuliaLean.base.int.ifelse
    simp [h, l, hfin, hprod]

-- 10. TpFromSamePreservesValue (twiceprecision-value-constructor)
def TpFromSamePreservesValue : Prop :=
  (∀ x : F64,
    let p := tpFromSame f64Arithmetic x
    p.hi = x ∧ p.lo = JuliaLean.base.float.zero_float .f64 ∧
    fractionEq (exactTpFraction p) (floatFraction x) ∧
    tpOuter (fun _ => F64) (tpFromSame f64Arithmetic) x = p) ∧
  (∀ (t : IntTy) (x : JInt t),
    let p := tpFromSame (jintArith t) x
    JuliaLean.base.int.add p.hi p.lo = x ∧ p.lo = JuliaLean.base.int.lit t 0)

theorem toRat_zero_f64 : (JuliaLean.base.float.zero_float .f64).toRat.1 = 0 := by decide +kernel

theorem exactTpFraction_zero_lo (x : F64) :
    fractionEq (exactTpFraction ⟨x, JuliaLean.base.float.zero_float .f64⟩) (floatFraction x) := by
  unfold exactTpFraction fractionAdd fractionEq floatFraction
  dsimp only
  rw [toRat_zero_f64, Int.zero_mul, Int.add_zero, Int.mul_assoc,
    Int.mul_comm (Int.ofNat (JuliaLean.base.float.zero_float .f64).toRat.2)]
theorem tpFromSamePreservesValue_proven : TpFromSamePreservesValue := by
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨rfl, rfl, exactTpFraction_zero_lo x, rfl⟩
  · intro t x
    exact ⟨add_zero_jint x, rfl⟩

-- 11. TpFromValueExact (twiceprecision-constructor-value)
def TpFromValueExact : Prop :=
  (∀ (x : Int) (approx : Int → Int) (out : TwicePrecision Int),
    tpFromValue (fun n => .ok (approx n)) (fun n hi => n - hi) (fun d => .ok d) x = .ok out →
    out.hi + out.lo = x) ∧
  (∀ (s t : IntTy) (x : JInt s) (out : TwicePrecision (JInt t)),
    tpFromValue (fun i => .ok (JuliaLean.base.int.widenTo t i))
      (fun i hi => JuliaLean.base.int.sub (JuliaLean.base.int.widenTo t i) hi)
      (fun d => .ok d) x = .ok out →
    JuliaLean.base.int.add out.hi out.lo = JuliaLean.base.int.widenTo t x ∧
    out.lo = JuliaLean.base.int.lit t 0)

theorem tpFromValueExact_proven : TpFromValueExact := by
  refine ⟨?_, ?_⟩
  · intro x approx out h
    unfold tpFromValue at h
    cases h
    dsimp only
    omega
  · intro s t x out h
    unfold tpFromValue at h
    cases h
    dsimp only
    rw [sub_self_jint, add_zero_jint]
    exact ⟨rfl, rfl⟩

-- 12. TpRatioValue (twiceprecision-ratio-value)
def TpRatioValue : Prop :=
  (∀ (k d : Int) (out : TwicePrecision Int),
    d ≠ 0 →
    tpRatio (fun n => .ok (tpFromSame intArithmetic n))
      (fun x den => divTpNumber Int.tdiv (fun _ v => .ok (tpFromSame intArithmetic v))
        (fun a b => .ok (divTpSame intArithmetic (mul12Generic intArithmetic)
          JuliaLean.base.int.ifelse a b)) x den)
      (k * d, d) = .ok out →
    out.hi + out.lo = k) ∧
  (∀ {T I : Type} (div : I → I → T) (construct : T → JlX (TwicePrecision T)) (n d : I),
    tpRatioSmall div construct (n, d) = construct (div n d))

theorem tpRatioValue_proven : TpRatioValue := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  intro k d out hd h
  unfold tpRatio divTpNumber divTpSame tpFromSame mul12Generic canonicalize2
    intArithmetic JuliaLean.base.int.ifelse at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases h
  have hmul : d * k = k * d := Int.mul_comm d k
  have hdiv : (k * d).tdiv d = k := by
    rw [← hmul]
    exact Int.mul_tdiv_cancel_left k hd
  rw [hdiv]
  by_cases hk : (decide (k = 0) || !true) = true
  · simp only [Bool.not_true, Bool.or_false, decide_eq_true_eq] at hk
    subst hk; simp
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    have h0 : k * d - k * d = 0 := Int.sub_self _
    simp [h0, Int.zero_tdiv]

-- 13. TwiceprecisionTruncPreservesValue (twiceprecision-truncation-preserves-value)
theorem sub_self_zero_f64 (x : F64) (hfin : x.isfinite = true) :
    JuliaLean.base.float.sub_IEEEFloat x x = JuliaLean.base.float.zero_float .f64 := by
  have hf : x.expField ≠ JuliaLean.base.float.FTy.f64.fmt.emax := by
    unfold Fl.isfinite at hfin
    exact bne_iff_ne.mp hfin
  have hnan_x : x.isnan = false := by
    unfold Fl.isnan
    simp [hf]
  have hinf_x : x.isinf = false := by
    unfold Fl.isinf
    simp [hf]
  have hneg_fields : (Fl.neg x).expField = x.expField ∧ (Fl.neg x).frac = x.frac ∧
      (Fl.neg x).signbit = !x.signbit := by
    have hx : x.toBits < 2 ^ 64 := x.bits.isLt
    have hnb := fl_neg_toBits x
    change (Fl.neg x).toBits = if x.toBits ≥ 2 ^ 63 then x.toBits - 2 ^ 63 else x.toBits + 2 ^ 63 at hnb
    refine ⟨?_, ?_, ?_⟩
    · change (Fl.neg x).toBits / 2 ^ 52 % 2 ^ 11 = x.toBits / 2 ^ 52 % 2 ^ 11
      rw [hnb]; split <;> omega
    · change (Fl.neg x).toBits % 2 ^ 52 = x.toBits % 2 ^ 52
      rw [hnb]; split <;> omega
    · change decide ((Fl.neg x).toBits ≥ 2 ^ 63) = !decide (x.toBits ≥ 2 ^ 63)
      rw [hnb]
      by_cases hs : x.toBits ≥ 2 ^ 63
      · have h2 : ¬ (x.toBits - 2 ^ 63 ≥ 2 ^ 63) := by omega
        simp [hs, h2]
      · have h2 : x.toBits + 2 ^ 63 ≥ 2 ^ 63 := by omega
        simp [hs, h2]
  have hnan_nx : (Fl.neg x).isnan = false := by
    unfold Fl.isnan; rw [hneg_fields.1, hneg_fields.2.1]; exact hnan_x
  have hinf_nx : (Fl.neg x).isinf = false := by
    unfold Fl.isinf; rw [hneg_fields.1, hneg_fields.2.1]; exact hinf_x
  have hfin_nx : (Fl.neg x).isfinite = true := by
    unfold Fl.isfinite; rw [hneg_fields.1]; exact hfin
  have hrat_nx : (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
    unfold Fl.toRat
    simp only [hfin, hfin_nx, hneg_fields.1, hneg_fields.2.1, hneg_fields.2.2,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases x.signbit <;> simp <;> repeat' (split <;> simp [Int.neg_mul])
  have hsub : JuliaLean.base.float.sub_IEEEFloat x x =
      JuliaLean.C.floatAdd x (Fl.neg x) := by
    have hbf : (JuliaLean.base.float.FTy.f64.fmt == JuliaLean.C.bfloat) = false := rfl
    unfold JuliaLean.base.float.sub_IEEEFloat JuliaLean.base.float.sub_float
      JuliaLean.C.jlSubFloat JuliaLean.C.finishFloat JuliaLean.C.floatSub
    simp only [hbf, hnan_x, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hsub]
  unfold JuliaLean.C.floatAdd
  simp only [hnan_x, hnan_nx, hinf_x, hinf_nx, Bool.false_eq_true, ↓reduceIte]
  rw [hrat_nx, hneg_fields.2.2]
  have hsum0 : x.toRat.1 * (x.toRat.2 : Int) + -x.toRat.1 * (x.toRat.2 : Int) = 0 := by
    rw [Int.neg_mul, Int.add_right_neg]
  have hdpos : 0 < x.toRat.2 * x.toRat.2 := Nat.mul_pos (toRat_den_pos x hfin) (toRat_den_pos x hfin)
  have hd0 : (x.toRat.2 * x.toRat.2 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hsb : (x.signbit && !x.signbit) = false := by cases x.signbit <;> rfl
  rw [hsum0, hsb]
  unfold Fl.roundRat
  simp [hd0, JuliaLean.base.float.zero_float]

def TwiceprecisionTruncPreservesValue : Prop :=
  (∀ x : F64, x.isfinite = true →
    let p := twiceprecisionIEEE bitOps64 f64Arithmetic x (JuliaLean.base.int.lit .i64 0)
    p = ⟨x, JuliaLean.base.float.zero_float .f64⟩ ∧
    fractionEq (exactTpFraction p) (floatFraction x)) ∧
  (∀ x : TwicePrecision F64, x.hi.isfinite = true →
    x.lo = JuliaLean.base.float.zero_float .f64 →
    twiceprecisionTPF64 x (JuliaLean.base.int.lit .i64 0) = x) ∧
  (∀ (x : TwicePrecision F64) (nb : JInt .i64),
    (truncbitsF64 x.hi nb).isfinite = true →
    (JuliaLean.base.float.sub_IEEEFloat x.hi (truncbitsF64 x.hi nb)).isfinite = true →
    exactFloatSub x.hi (truncbitsF64 x.hi nb) →
    exactFloatAdd (JuliaLean.base.float.sub_IEEEFloat x.hi (truncbitsF64 x.hi nb)) x.lo →
    fractionEq (exactTpFraction (twiceprecisionTPF64 x nb)) (exactTpFraction x)) ∧
  (∀ {t : IntTy} (nd : JInt t × JInt t) (nb : JInt .i64),
    tpRatioBitsF64 nd nb = tpIntegerRatioBitsF64 nd nb)

theorem twiceprecisionTruncPreservesValue_proven : TwiceprecisionTruncPreservesValue := by
  refine ⟨?_, ?_, ?_, fun _ _ => rfl⟩
  · intro x hfin
    have htb := truncbitsIdentity_proven.1 .f64 x
    unfold twiceprecisionIEEE f64Arithmetic fvArithmetic
    dsimp only
    rw [htb, sub_self_zero_f64 x hfin]
    exact ⟨rfl, exactTpFraction_zero_lo x⟩
  · intro x hfin hlo
    cases x with | mk hi lo =>
    dsimp only at hfin hlo
    subst hlo
    have htb := truncbitsIdentity_proven.1 .f64 hi
    have hadd0 : JuliaLean.base.float.add_IEEEFloat
        (JuliaLean.base.float.zero_float .f64) (JuliaLean.base.float.zero_float .f64) =
        JuliaLean.base.float.zero_float .f64 := by decide +kernel
    unfold twiceprecisionTPF64 twiceprecisionTP f64Arithmetic fvArithmetic
    dsimp only
    rw [htb, sub_self_zero_f64 hi hfin, hadd0]
  · intro x nb hfin_hi hfin_sub hsub hadd
    unfold truncbitsF64 at hfin_sub hsub hadd
    unfold exactFloatSub fractionSub fractionEq at hsub
    unfold exactFloatAdd fractionAdd fractionEq at hadd
    unfold twiceprecisionTPF64 twiceprecisionTP exactTpFraction f64Arithmetic fvArithmetic fractionAdd fractionEq
    dsimp only at hsub hadd ⊢
    have hdd := floatFraction_den_pos _ hfin_sub
    exact fraction_cancel_lemma _ _ _ _ _ _ _ _ _ _ hdd hsub hadd

-- 14. NbitslenCoversOffsets (twiceprecision-nbitslen-offset-capacity)
def tpNbitslenGeneric (len offset : Int) : Nat :=
  nbitslenGeneric (I := Int) (N := Nat)
    (fun a b => decide (a < b)) (fun a b => a - b) (fun a b => max a b)
    (fun a => if a ≤ 0 then 0 else a.toNat.log2 + 1) (fun a b => a + b) 2 1 1 0
    len offset

def tpNbitslen (len offset : Int) : Nat :=
  nbitslenIEEE tpNbitslenGeneric 53 2 cldNat Nat.min len offset

def NbitslenCoversOffsets : Prop :=
  (∀ r : SRLF64, nbitslenRangeF64 r = nbitslenF64 r.len r.offset) ∧
  (∀ len offset : Int, tpNbitslen len offset ≤ 27) ∧
  (∀ len offset : Int, len < 2 → tpNbitslen len offset = 0) ∧
  (∀ len offset : Nat, 2 ≤ len → 1 ≤ offset → offset ≤ len →
    2 ^ (tpNbitslenGeneric (len : Int) (offset : Int) - 1) ≥
      max (offset - 1) (len - offset)) ∧
  (∀ len offset : Nat, 2 ≤ len → 1 ≤ offset → offset ≤ len → len ≤ 2^26 →
    2 ^ (tpNbitslen (len : Int) (offset : Int) - 1) ≥
      max (offset - 1) (len - offset))

theorem tpNbitslenGeneric_eq (len offset : Int) :
    tpNbitslenGeneric len offset =
      if len < 2 then 0
      else
        let m := max (offset - 1) (len - offset) - 1
        (if m ≤ 0 then 0 else m.toNat.log2 + 1) + 1 := by
  unfold tpNbitslenGeneric nbitslenGeneric
  by_cases h : len < 2 <;> simp [h]

theorem nbitslenGeneric_covers (len offset : Nat) (hlen : 2 ≤ len) (hoff1 : 1 ≤ offset) (hoff2 : offset ≤ len) :
    2 ^ (tpNbitslenGeneric (len : Int) (offset : Int) - 1) ≥
      max (offset - 1) (len - offset) := by
  rw [tpNbitslenGeneric_eq]
  have hlt2 : ¬ ((len : Int) < 2) := by omega
  simp only [hlt2, ↓reduceIte]
  have hmax_eq : max ((offset : Int) - 1) ((len : Int) - (offset : Int)) =
      (max (offset - 1) (len - offset) : Nat) := by omega
  rw [hmax_eq]
  generalize hm : max (offset - 1) (len - offset) = m
  have hm1 : 1 ≤ m := by omega
  by_cases hm_eq1 : m = 1
  · subst hm_eq1; decide
  · have hnot_le : ¬ ((m : Int) - 1 ≤ 0) := by omega
    simp only [hnot_le, ↓reduceIte]
    have htoNat : ((m : Int) - 1).toNat = m - 1 := by omega
    rw [htoNat]
    rw [Nat.add_sub_cancel]
    have hpow : m - 1 < 2 ^ ((m - 1).log2 + 1) := Nat.lt_log2_self
    omega

theorem nbitslenCoversOffsets_proven : NbitslenCoversOffsets := by
  refine ⟨fun _ => rfl, ?_, ?_, nbitslenGeneric_covers, ?_⟩
  · intro len offset
    unfold tpNbitslen nbitslenIEEE
    have hcld : cldNat 53 2 = 27 := by decide
    rw [hcld]
    exact Nat.min_le_left 27 _
  · intro len offset hlt
    unfold tpNbitslen nbitslenIEEE
    rw [tpNbitslenGeneric_eq]
    simp [hlt]
  · intro len offset hlen hoff1 hoff2 hbound
    have hgen := nbitslenGeneric_covers len offset hlen hoff1 hoff2
    have hle27 : tpNbitslenGeneric (len : Int) (offset : Int) ≤ 27 := by
      rw [tpNbitslenGeneric_eq]
      have hlt2 : ¬ ((len : Int) < 2) := by omega
      simp only [hlt2, ↓reduceIte]
      have hmax_eq : max ((offset : Int) - 1) ((len : Int) - (offset : Int)) =
          (max (offset - 1) (len - offset) : Nat) := by omega
      rw [hmax_eq]
      generalize hm : max (offset - 1) (len - offset) = m
      have hm_lt : m < 2 ^ 26 := by omega
      split
      · omega
      · rename_i hnot_le
        have htoNat : ((m : Int) - 1).toNat = m - 1 := by omega
        rw [htoNat]
        have hm1_pos : 0 < m - 1 := by omega
        have hlog : (m - 1).log2 < 26 := by
          by_cases h26 : 26 ≤ (m - 1).log2
          · have hpow1 : 2 ^ 26 ≤ 2 ^ (m - 1).log2 := Nat.pow_le_pow_right (by decide) h26
            have hpow2 : 2 ^ (m - 1).log2 ≤ m - 1 := Nat.log2_self_le (by omega)
            omega
          · omega
        omega
    have heq : tpNbitslen (len : Int) (offset : Int) =
        tpNbitslenGeneric (len : Int) (offset : Int) := by
      unfold tpNbitslen nbitslenIEEE
      have hcld : cldNat 53 2 = 27 := by decide
      rw [hcld]
      exact Nat.min_eq_right hle27
    rw [heq]
    exact hgen
-- 15. TpNumberConversions (twiceprecision-number-conversions)
def TpPairConversions : Prop :=
  (∀ x : TwicePrecision F64, tpConvertIdentity x = x) ∧
  (∀ x : TwicePrecision F64, tpIdentity x = x) ∧
  (∀ x : TwicePrecision F64, floatTpAbstractFloat x = x) ∧
  (∀ x : TwicePrecision F64, floatTp (fun v => v) x = x) ∧
  (∀ (convert : F64 → JlX F64) x out,
    (∀ a, convert a = .ok a) → tpConvertParts convert x = .ok out →
    out.hi = x.hi ∧ out.lo = x.lo) ∧
  (∀ (x : TwicePrecision F64) (out : F64),
    convertTpToNumber (tpToNumber pure (fun a b => pure (JuliaLean.base.float.add_IEEEFloat a b))) x = .ok out →
    out = JuliaLean.base.float.add_IEEEFloat x.hi x.lo) ∧
  (∀ (v : F64) (out : TwicePrecision F64),
    convertNumberToTp (fun a => .ok (tpFromSame f64Arithmetic a)) v = .ok out →
    out = tpFromSame f64Arithmetic v) ∧
  (∀ (T R S : Type) (prom : Type → Type → Type),
    eltypeTwicePrecision T = T ∧
    promoteRuleTwicePrecision (R := R) (S := S) prom = TwicePrecision (prom R S) ∧
    promoteRuleTwicePrecisionNumber (R := R) (S := S) prom = TwicePrecision (prom R S))

def TpToNumberValue : Prop :=
  ∀ (x : TwicePrecision F64) (out : F64),
    tpToNumber (fun a => .ok a) (fun a b => .ok (JuliaLean.base.float.add_IEEEFloat a b)) x = .ok out →
    out = JuliaLean.base.float.add_IEEEFloat x.hi x.lo

def TpBigExact : Prop :=
  ∀ x : TwicePrecision F64,
    fractionEq (bigTp floatFraction fractionAdd x) (exactTpFraction x)

def TpNumberConversions : Prop := TpPairConversions ∧ TpToNumberValue ∧ TpBigExact

theorem fractionEq_refl (p : Int × Int) : fractionEq p p := rfl

theorem tpNumberConversions_proven : TpNumberConversions := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun x => by cases x; rfl, ?_, ?_, ?_,
    fun _ _ _ _ => ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
  · intro convert x out hconv h
    unfold tpConvertParts at h
    rw [hconv x.hi, hconv x.lo] at h
    have h' := Except.ok.inj h
    subst h'
    exact ⟨rfl, rfl⟩
  · intro x out h
    exact (Except.ok.inj h).symm
  · intro v out h
    exact (Except.ok.inj h).symm
  · intro x out h
    exact (Except.ok.inj h).symm
  · intro x
    exact fractionEq_refl (exactTpFraction x)

-- 16. TpZeroValue (twiceprecision-zero-representation)
def TpZeroValue : Prop :=
  fractionEq (exactTpFraction (zeroTpType f64Arithmetic)) (0, 1) ∧
  (∀ x : TwicePrecision F64,
    zeroTpValue (fun _ => zeroTpType f64Arithmetic) x = zeroTpType f64Arithmetic ∧
    fractionEq (exactTpFraction (zeroTpValue (fun _ => zeroTpType f64Arithmetic) x)) (0, 1)) ∧
  (∀ (t : IntTy) (x : TwicePrecision (JInt t)),
    zeroTpValue (fun _ => zeroTpType (jintArith t)) x =
      ⟨JuliaLean.base.int.lit t 0, JuliaLean.base.int.lit t 0⟩)

theorem tpZeroValue_proven : TpZeroValue := by
  have hz : fractionEq (exactTpFraction (zeroTpType f64Arithmetic)) (0, 1) := by decide +kernel
  refine ⟨hz, fun _ => ⟨rfl, hz⟩, fun _ _ => rfl⟩

-- 17. TpNumericOperations (twiceprecision-arithmetic-values)
def TpIntRingLaws : Prop :=
  ∀ (x y : TwicePrecision Int) (v : Int),
    let addOut := addTpSame intArithmetic x y
    let subOut := subTpSame intArithmetic x y
    let addNumOut := addTpNumber intArithmetic JuliaLean.base.int.ifelse x v
    let addNumLeft := addNumberTp intArithmetic JuliaLean.base.int.ifelse v x
    let subNumOut := subTpNumber intArithmetic JuliaLean.base.int.ifelse x v
    let subNumLeft := subNumberTp intArithmetic JuliaLean.base.int.ifelse v x
    let mulOut := mulTpSame intArithmetic (mul12Generic intArithmetic) JuliaLean.base.int.ifelse x y
    addOut.hi + addOut.lo = (x.hi + x.lo) + (y.hi + y.lo) ∧
    addOut.lo = 0 ∧
    subOut = addTpSame intArithmetic x (negTp intArithmetic y) ∧
    subOut.hi + subOut.lo = (x.hi + x.lo) - (y.hi + y.lo) ∧
    addNumLeft = addNumOut ∧
    addNumOut.hi + addNumOut.lo = (x.hi + x.lo) + v ∧
    subNumOut.hi + subNumOut.lo = (x.hi + x.lo) - v ∧
    subNumLeft.hi + subNumLeft.lo = v - (x.hi + x.lo) ∧
    ((x.hi = 0 → x.lo = 0) → (y.hi = 0 → y.lo = 0) →
      mulOut.hi + mulOut.lo = x.hi * y.hi + x.hi * y.lo + x.lo * y.hi) ∧
    mulOut.lo = 0 ∧
    ((x.hi = 0 → x.lo = 0) → y.lo = 0 →
      mulOut.hi + mulOut.lo = (x.hi + x.lo) * (y.hi + y.lo))

def TpPromotedLaws : Prop :=
  ∀ (s t : IntTy) (x : TwicePrecision (JInt s)) (y : TwicePrecision (JInt t)),
    let p := s.promote t
    let prom : TwicePrecision (JInt s) → TwicePrecision (JInt t) →
        TwicePrecision (JInt p) × TwicePrecision (JInt p) :=
      fun a b => (⟨JuliaLean.base.int.widenTo p a.hi, JuliaLean.base.int.widenTo p a.lo⟩,
                  ⟨JuliaLean.base.int.widenTo p b.hi, JuliaLean.base.int.widenTo p b.lo⟩)
    addTpPromoted prom (jintArith p) x y =
      addTpSame (jintArith p) (prom x y).1 (prom x y).2 ∧
    mulTpPromoted prom (jintArith p) (mul12Generic (jintArith p)) JuliaLean.base.int.ifelse x y =
      mulTpSame (jintArith p) (mul12Generic (jintArith p)) JuliaLean.base.int.ifelse
        (prom x y).1 (prom x y).2

def TpFloatArithmeticLaws : Prop :=
  (∀ (x y : TwicePrecision F64),
    subTpSame f64Arithmetic x y = addTpSame f64Arithmetic x (negTp f64Arithmetic y)) ∧
  (∀ (x : TwicePrecision F64) (v : F64),
    addNumberTp f64Arithmetic JuliaLean.base.int.ifelse v x =
      addTpNumber f64Arithmetic JuliaLean.base.int.ifelse x v ∧
    subTpNumber f64Arithmetic JuliaLean.base.int.ifelse x v =
      addTpNumber f64Arithmetic JuliaLean.base.int.ifelse x
        (JuliaLean.base.float.neg_IEEEFloat v) ∧
    subNumberTp f64Arithmetic JuliaLean.base.int.ifelse v x =
      addNumberTp f64Arithmetic JuliaLean.base.int.ifelse v (negTp f64Arithmetic x)) ∧
  (∀ (x : TwicePrecision F64) (v : F64),
    let construct := fun _ (b : F64) => .ok (tpFromSame f64Arithmetic b)
    let multiply := fun a b => .ok (mulTpF64 a b)
    mulNumberTp (fun b a => mulTpNumber f64Arithmetic JuliaLean.base.float.mul_IEEEFloat
      construct multiply a b JuliaLean.base.float.iszero_float JuliaLean.base.float.mul_IEEEFloat) v x =
    mulTpNumber f64Arithmetic JuliaLean.base.float.mul_IEEEFloat
      construct multiply x v JuliaLean.base.float.iszero_float JuliaLean.base.float.mul_IEEEFloat ∧
    (JuliaLean.base.float.iszero_float v = true →
      mulTpNumber f64Arithmetic JuliaLean.base.float.mul_IEEEFloat
        construct multiply x v JuliaLean.base.float.iszero_float JuliaLean.base.float.mul_IEEEFloat =
        .ok ⟨JuliaLean.base.float.mul_IEEEFloat x.hi v, JuliaLean.base.float.mul_IEEEFloat x.lo v⟩)) ∧
  (∀ (x : TwicePrecision F64),
    mulTpIntegerF64 x (JuliaLean.base.int.lit .i64 0) =
      ⟨JuliaLean.base.float.mul_IEEEFloat x.hi (JuliaLean.base.float.zero_float .f64),
       JuliaLean.base.float.mul_IEEEFloat x.lo (JuliaLean.base.float.zero_float .f64)⟩) ∧
  (∀ (x : TwicePrecision F64) (v : F64),
    let construct := fun _ (b : F64) => .ok (tpFromSame f64Arithmetic b)
    let divide := fun a b => .ok (divTpF64 a b)
    divTpNumber JuliaLean.base.float.div_IEEEFloat construct divide x v =
      .ok (divTpF64 x (tpFromSame f64Arithmetic v))) ∧
  (∀ (k d : Int), d ≠ 0 →
    let x : TwicePrecision Int := ⟨k * d, 0⟩
    let y : TwicePrecision Int := ⟨d, 0⟩
    let out := divTpSame intArithmetic (mul12Generic intArithmetic) JuliaLean.base.int.ifelse x y
    out.hi + out.lo = k ∧ out.lo = 0)

def TpNumericOperations : Prop :=
  TpIntRingLaws ∧ TpPromotedLaws ∧ TpFloatArithmeticLaws


theorem tpNumericOperations_proven : TpNumericOperations := by
  refine ⟨?_, fun _ _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  · intro x y v
    dsimp only
    refine ⟨?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold addTpSame canonicalize2
      rcases Decidable.em (intArithmetic.gt (intArithmetic.abs x.hi) (intArithmetic.abs y.hi) = true) with h | h <;>
      · simp only [h, ↓reduceIte, intArithmetic]
        omega
    · unfold addTpSame canonicalize2
      rcases Decidable.em (intArithmetic.gt (intArithmetic.abs x.hi) (intArithmetic.abs y.hi) = true) with h | h <;>
      · simp only [h, ↓reduceIte, intArithmetic]
        omega
    · unfold subTpSame addTpSame negTp canonicalize2
      rcases Decidable.em (intArithmetic.gt (intArithmetic.abs x.hi) (intArithmetic.abs (intArithmetic.neg y.hi)) = true) with h | h <;>
      · simp only [h, ↓reduceIte, intArithmetic]
        omega
    · unfold addTpNumber
      rw [add12Same_int_eq]
      dsimp only [canonicalize2, intArithmetic]
      omega
    · unfold subTpNumber addTpNumber
      rw [add12Same_int_eq]
      dsimp only [canonicalize2, intArithmetic]
      omega
    · unfold subNumberTp addNumberTp addTpNumber negTp
      rw [add12Same_int_eq]
      dsimp only [canonicalize2, intArithmetic]
      omega
    · intro hnx hny
      unfold mulTpSame mul12Generic canonicalize2 intArithmetic JuliaLean.base.int.ifelse
      dsimp only
      by_cases hz : (decide (x.hi * y.hi = 0) || !true) = true
      · simp only [Bool.not_true, Bool.or_false, decide_eq_true_eq] at hz
        rcases Int.mul_eq_zero.mp hz with hx0 | hy0
        · simp [hx0, hnx hx0]
        · simp [hy0, hny hy0]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        omega
    · unfold mulTpSame mul12Generic canonicalize2 intArithmetic JuliaLean.base.int.ifelse
      dsimp only
      by_cases hz : (decide (x.hi * y.hi = 0) || !true) = true
      · simp only [Bool.not_true, Bool.or_false, decide_eq_true_eq] at hz
        simp [hz]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        omega
    · intro hnx hylo
      unfold mulTpSame mul12Generic canonicalize2 intArithmetic JuliaLean.base.int.ifelse
      dsimp only
      by_cases hz : (decide (x.hi * y.hi = 0) || !true) = true
      · simp only [Bool.not_true, Bool.or_false, decide_eq_true_eq] at hz
        rcases Int.mul_eq_zero.mp hz with hx0 | hy0
        · simp [hx0, hnx hx0, hylo]
        · simp [hy0, hylo]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte, hylo, Int.mul_zero, Int.zero_add,
          Int.add_zero]
        grind
  · refine ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, fun _ _ => rfl, ?_⟩
    · intro x v
      refine ⟨rfl, ?_⟩
      intro hz
      unfold mulTpNumber
      simp [hz, Pure.pure, Except.pure]
    · intro x
      have heq0 : JuliaLean.base.int.eqSame (JuliaLean.base.int.lit .i64 0)
          (JuliaLean.base.int.lit .i64 0) = true := by decide +kernel
      have hf0 : JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 0) =
          JuliaLean.base.float.zero_float .f64 := by decide +kernel
      unfold mulTpIntegerF64 mulTpInteger
      simp [heq0, hf0]
    · intro k d hd
      dsimp only
      unfold divTpSame mul12Generic canonicalize2 intArithmetic JuliaLean.base.int.ifelse
      dsimp only
      have hmul : d * k = k * d := Int.mul_comm d k
      have hdiv : (k * d).tdiv d = k := by
        rw [← hmul]; exact Int.mul_tdiv_cancel_left k hd
      rw [hdiv]
      by_cases hk : (decide (k = 0) || !true) = true
      · simp only [Bool.not_true, Bool.or_false, decide_eq_true_eq] at hk
        subst hk; simp
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        have h0 : k * d - k * d = 0 := Int.sub_self _
        simp [h0, Int.zero_tdiv]
-- 18. RsslStepReportsInput (twiceprecision-step-range-value)
def RsslStepReportsInput : Prop :=
  (∀ (r : SRLF64),
    stepTpFloat (tpToNumber pure (fun a b => pure (JuliaLean.base.float.add_IEEEFloat a b))) r =
      .ok (JuliaLean.base.float.add_IEEEFloat r.step.hi r.step.lo) ∧
    stepTpGeneric (tpToNumber pure (fun a b => pure (JuliaLean.base.float.add_IEEEFloat a b))) r =
      .ok (JuliaLean.base.float.add_IEEEFloat r.step.hi r.step.lo)) ∧
  (∀ (t : IntTy) (r : StepRangeLen (JInt t) (TwicePrecision (JInt t)) (TwicePrecision (JInt t)) (JInt .i64)),
    stepTpGeneric (tpToNumber pure (fun a b => pure (JuliaLean.base.int.add a b))) r =
      .ok (JuliaLean.base.int.add r.step.hi r.step.lo)) ∧
  (∀ (ref : TwicePrecision F64) (s : F64) (len offset : JInt .i64) (r : SRLF64),
    srlMakeTpF64 ref (tpFromSame f64Arithmetic s) len offset = .ok r →
    stepTpFloat (tpToNumber pure (fun a b => pure (JuliaLean.base.float.add_IEEEFloat a b))) r =
      .ok (JuliaLean.base.float.add_IEEEFloat s (JuliaLean.base.float.zero_float .f64)))

theorem rsslStepReportsInput_proven : RsslStepReportsInput := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, ?_⟩
  intro ref s len offset r h
  have hr := (srlMakeTpF64_fields ref (tpFromSame f64Arithmetic s) len offset r h).1
  subst hr
  rfl

-- 19. RatDenominatorPositive (twiceprecision-rat-terminates)
theorem ratLoop_bound_gen {F I : Type} (fuel : Nat) (ops : RatOps F I) (x y : F)
    (a b c d : I) (n outD : I)
    (hba : ops.integer.le (ops.integer.max (ops.integer.abs a) (ops.integer.abs b))
      (ops.convertBound ops.bound) = true)
    (h : ratLoop fuel ops x y a b c d = .ok (n, outD)) :
    ops.integer.le (ops.integer.max (ops.integer.abs n) (ops.integer.abs outD))
      (ops.convertBound ops.bound) = true := by
  induction fuel generalizing y a b c d with
  | zero =>
    unfold ratLoop at h
    cases h
    exact hba
  | succ k ih =>
    unfold ratLoop at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · cases h; exact hba
    · split at h
      · cases h
      · rename_i f _
        by_cases hle' : ops.integer.le
            (ops.integer.max
              (ops.integer.abs (ops.integer.add (ops.integer.mul f a) c))
              (ops.integer.abs (ops.integer.add (ops.integer.mul f b) d)))
            (ops.convertBound ops.bound) = true
        · simp only [hle', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · cases h; exact hle'
          · exact ih _ _ _ _ _ hle' h
        · have hfalse : ops.integer.le
              (ops.integer.max
                (ops.integer.abs (ops.integer.add (ops.integer.mul f a) c))
                (ops.integer.abs (ops.integer.add (ops.integer.mul f b) d)))
              (ops.convertBound ops.bound) = false := Bool.eq_false_iff.mpr hle'
          simp only [hfalse, Bool.not_false, ↓reduceIte] at h
          cases h
          exact hba

def RatDenominatorPositive : Prop :=
  (∀ {F I : Type} (ops : RatOps F I) (fuel : Nat) (x : F) (n d : I),
    ops.integer.le
      (ops.integer.max (ops.integer.abs ops.integer.one) (ops.integer.abs ops.integer.zero))
      (ops.convertBound ops.bound) = true →
    rat ops x fuel = .ok (n, d) →
    ops.integer.le (ops.integer.max (ops.integer.abs n) (ops.integer.abs d))
      (ops.convertBound ops.bound) = true) ∧
  (∀ (x : F64) (fuel : Nat) (n d : JInt .i64),
    ratF64 x fuel = .ok (n, d) →
    JuliaLean.base.int.leSame
      (JuliaLean.base.int.jmax (JuliaLean.base.int.abs n) (JuliaLean.base.int.abs d))
      (JuliaLean.base.int.lit .i64 16777216) = true) ∧
  (ratF64 (JuliaLean.base.float.zero_float .f64) 100 =
    .ok (JuliaLean.base.int.lit .i64 0, JuliaLean.base.int.lit .i64 1)) ∧
  (∀ (α : Type),
    narrowAbstract α = .f64 ∧ narrowF64 = .f32 ∧ narrowF32 = .f16 ∧ narrowF16 = .f16)

theorem ratDenominatorPositive_proven : RatDenominatorPositive := by
  refine ⟨?_, ?_, by decide +kernel, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro F I ops fuel x n d hinit h
    exact ratLoop_bound_gen fuel ops x x ops.integer.one ops.integer.zero
      ops.integer.zero ops.integer.one n d hinit h
  · intro x fuel n d h
    have hinit : f64RatOps.integer.le
        (f64RatOps.integer.max (f64RatOps.integer.abs f64RatOps.integer.one)
          (f64RatOps.integer.abs f64RatOps.integer.zero))
        (f64RatOps.convertBound f64RatOps.bound) = true := by decide +kernel
    exact ratLoop_bound_gen fuel f64RatOps x x f64RatOps.integer.one f64RatOps.integer.zero
      f64RatOps.integer.zero f64RatOps.integer.one n d hinit h
-- 20. LcmUncheckedMultiple (twiceprecision-lcm-unchecked-multiple)
def LcmUncheckedMultiple : Prop :=
  ∀ a b : Int, Int.gcd a b ≠ 0 →
    lcmUnchecked intOps (fun x y => if y = 0 then
      .error (.jl (.divideError)) else .ok (x.tdiv y)) a b =
      .ok (a * b.tdiv (Int.gcd a b))

theorem lcmUncheckedMultiple_proven : LcmUncheckedMultiple := by
  intro a b hne
  unfold lcmUnchecked intOps
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Int.gcd]
  have hne' : (Int.ofNat (Nat.gcd a.natAbs b.natAbs) : Int) ≠ 0 := by
    simpa [Int.gcd] using hne
  simp only [hne', ↓reduceIte]
  rfl

def entries : List Entry := [
  { id := "floatranges-range-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range(::Float64, ::Float64; length)", "range(::Float64; step, length)", "range(; stop, step, length)", "LinRange(::Float64, ::Float64, ::Int)"],
    statement := "Whenever range(a, b; length=n), range(a; step=s, length=n), range(; stop=b, step=s, length=n) or LinRange(a, b, n) returns, its length is n.",
    source := "range docstring, base/range.jl:80 (a range is uniquely determined by any three of start, step, stop and length)", status := .proven, prop := ``RangeConstructorsLength, thm := some ``rangeConstructorsLength_proven },

  { id := "floatranges-linspace-imin-overflow", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range(::Float64, ::Float64; length)", "_linspace(::Float64, ::Float64, ::Int)"],
    statement := "range(a, b; length=n) returns a range for finite a, b and n >= 2.",
    source := "range docstring, base/range.jl:73-80", status := .refuted, prop := ``LinspaceFloatSucceeds, thm := some ``linspaceFloatSucceeds_refuted, issue := "repro/floatranges-linspace-imin-overflow.jl" },

  { id := "floatranges-linspace-tiny-endpoint", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range(::Float64, ::Float64; length)", "_linspace(::Float64, ::Float64, ::Int)"],
    statement := "first(range(a, b; length=n)) == a and last(range(a, b; length=n)) == b for finite a, b and n >= 2.",
    source := "range docstring, base/range.jl:80; LinRange docstring example contrasting range, base/range.jl:569-587", status := .refuted, prop := ``LinspaceFloatEndpoints, thm := some ``linspaceFloatEndpoints_refuted, issue := "repro/floatranges-linspace-tiny-endpoint.jl" },

  { id := "floatranges-colon-infinite-step", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)"],
    statement := "A nonempty a:s:b with finite endpoints and a nonzero, non-NaN step starts at a.",
    source := "(:) docstring, base/range.jl:42-56", status := .refuted, prop := ``ColonFirst, thm := some ``colonFirst_refuted, issue := "repro/floatranges-colon-infinite-step.jl" },

  { id := "floatranges-colon-underflow-nonempty", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)"],
    statement := "a:s:b is empty when b < a and s > 0 (finite inputs).",
    source := "(:) docstring, base/range.jl:54-55", status := .refuted, prop := ``ColonEmpty, thm := some ``colonEmpty_refuted, issue := "repro/floatranges-colon-underflow-nonempty.jl" },

  { id := "floatranges-colon-decimal-threshold", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)", "rat(::Float64)"],
    statement := "Short decimal inputs give the decimal elements (an + k*sn)/10^j rounded once, and floor((bn-an)/sn)+1 of them.",
    source := "base/twiceprecision.jl:5-7; range docstring, base/range.jl:138", status := .refuted, prop := ``ColonDecimal, thm := some ``colonDecimal_refuted, issue := "repro/floatranges-colon-decimal-threshold.jl" },

  { id := "floatranges-colon-overshoot-stop", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)"],
    statement := "No element of a:s:b exceeds b when s > 0 (finite inputs).",
    source := "(:) docstring, base/range.jl:42-56", status := .refuted, prop := ``ColonStopBound, thm := some ``colonStopBound_refuted, issue := "repro/floatranges-colon-overshoot-stop.jl" },

  { id := "floatranges-start-step-overflow-nan", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range(::Float64; step, length)", "unsafe_getindex(::StepRangeLen{Float64,TwicePrecision})"],
    statement := "No element of range(a; step=s, length=n) is NaN for finite a and s.",
    source := "invariant (a + k*s overflows to Inf, never NaN)", status := .refuted, prop := ``StartStepNoNaN, thm := some ``startStepNoNaN_refuted, issue := "repro/floatranges-start-step-overflow-nan.jl" },

  { id := "floatranges-colon-signed-zero", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)", "range(::Float64; step, length)"],
    statement := "first(a:s:b) is identical (isequal) to a for nonempty ranges with finite inputs.",
    source := "(:) docstring, base/range.jl:42-56", status := .refuted, prop := ``ColonFirstIdentical, thm := some ``colonFirstIdentical_refuted, issue := "repro/floatranges-colon-signed-zero.jl" },

  { id := "floatranges-splitprec-typemax", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["splitprec(::Type{Float64}, ::Int)", "TwicePrecision{Float64}(::Integer)", "StepRangeLen{Float64}(::AbstractRange{<:Integer})"],
    statement := "splitprec(Float64, i) returns hi, lo with hi + lo == i exactly for every Int64 i.",
    source := "splitprec docstring, base/twiceprecision.jl:18-20", status := .refuted, prop := ``SplitprecExact, thm := some ``splitprecExact_refuted, issue := "repro/floatranges-splitprec-typemax.jl" },

  { id := "floatranges-colon-nonfinite-error", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["(:)(::Float64, ::Float64, ::Float64)"],
    statement := "a:s:b with an infinite or NaN endpoint throws ArgumentError, as range(a, b; length) does.",
    source := "base/twiceprecision.jl:672 (start and stop must be finite)", status := .refuted, prop := ``ColonNonfinite, thm := some ``colonNonfinite_refuted, issue := "repro/floatranges-colon-nonfinite-error.jl" },

  { id := "rangescov-twice-conversions", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["StepRangeLen{T,R,S,L}(::StepRangeLen{T,R,S,L})", "StepRangeLen{T,R,S,L}(::StepRangeLen)", "StepRangeLen{Float64}(::StepRangeLen)", "StepRangeLen{T}(::StepRangeLen) where T<:IEEEFloat", "StepRangeLen{Float64}(::AbstractRange)", "StepRangeLen{T}(::AbstractRange) where T<:IEEEFloat", "_convertSRL(::Type, ::StepRangeLen{<:Integer})", "_convertSRL(::Type, ::AbstractRange{<:Integer})", "_convertSRL(::Type, ::AbstractRange{U})", "__convertSRL(::Type, ::StepRangeLen{U})", "__convertSRL(::Type, ::AbstractRange{U})"],
    statement := "TwicePrecision StepRangeLen conversions keep length and offset; the fallbacks store TwicePrecision copies of ref/step (or first/step); the identity method returns its argument; the IEEE StepRangeLen{T} conversion stores Float64 ref/step.",
    source := "base/twiceprecision.jl:541-589", status := .proven, prop := ``TwiceConversionsComplete, thm := some ``twiceConversionsComplete_proven },

  { id := "rangescov-truncbits-identity", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["truncmask(::F, mask) where F<:IEEEFloat", "truncbits(::F, nb) where F<:IEEEFloat"],
    statement := "truncbits(x, 0) == x bitwise for every Float64 x, and truncmask(x, 0) is +0.0.",
    source := "invariant: truncating zero low bits keeps the value; base/twiceprecision.jl:28-35", status := .proven, prop := ``TruncbitsIdentity, thm := some ``truncbitsIdentity_proven },

  { id := "rangescov-mul12-int", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["mul12(::T, ::T) where T"],
    statement := "For integers mul12(x, y) returns (x*y, 0), so hi + lo == x*y.",
    source := "mul12 docstring, base/twiceprecision.jl:118", status := .proven, prop := ``Mul12IntExact, thm := some ``mul12IntExact_proven },

  { id := "rangescov-tp-neg-involution", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["-(::TwicePrecision)"],
    statement := "-(-x) == x for every TwicePrecision{Float64} x.",
    source := "invariant of negation; base/twiceprecision.jl:279", status := .proven, prop := ``TpNegInvolution, thm := some ``tpNegInvolution_proven },

  { id := "rangescov-tp-lt-irrefl", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["<(::TwicePrecision{T}, ::TwicePrecision{T})"],
    statement := "x < x is false for every TwicePrecision{Float64} x.",
    source := "invariant of a strict order; base/twiceprecision.jl:787-788", status := .proven, prop := ``TpLtIrrefl, thm := some ``tpLtIrrefl_proven },

  { id := "rangescov-isbetween-symmetric", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["isbetween(a, x, b)"],
    statement := "isbetween(a, x, b) == isbetween(b, x, a) for all Float64 values.",
    source := "invariant; base/twiceprecision.jl:790", status := .proven, prop := ``IsbetweenSymmetric, thm := some ``isbetweenSymmetric_proven },

  { id := "rangescov-sumpair-product", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["sumpair(::Integer)"],
    statement := "2 * p[1] * p[2] == n * (n + 1) for p = sumpair(n), every Int 0 <= n < 2^62.",
    source := "comment 'sum(1:n) as a product of two integers', base/twiceprecision.jl:624-625", status := .proven, prop := ``SumpairProduct, thm := some ``sumpairProduct_proven },

  { id := "rangescov-steprangelen-sum-small-int", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["sum(::StepRangeLen)"],
    statement := "sum(r) of an integer StepRangeLen equals sum(collect(r)) when all elements are representable and the sum fits in Int.",
    source := "sum docstring (small integers are summed in Int); base/twiceprecision.jl:591-605", status := .refuted, prop := ``SrlSumMatches, thm := some ``srlSumMatches_refuted, issue := "repro/rangescov-steprangelen-sum-small-int.jl" },

  { id := "rangescov-linspace-int-imin-inexact", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_linspace(::Type{T}, ::Integer, ::Integer, ::Integer)", "_linspace(::Type{T}, ::Integer, ::Integer, ::Integer, ::Integer)"],
    statement := "range(a, b; length=n) succeeds for distinct Int endpoints and n >= 2.",
    source := "range docstring", status := .refuted, prop := ``LinspaceIntSucceeds, thm := some ``linspaceIntSucceeds_refuted, issue := "repro/rangescov-linspace-int-imin-inexact.jl" },

  { id := "rangescov-linspace-int-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_linspace(::Type{T}, ::Integer, ::Integer, ::Integer)"],
    statement := "range(a, b; length=n) with Int endpoints has n elements whenever it returns.",
    source := "range docstring; base/twiceprecision.jl:717", status := .proven, prop := ``LinspaceIntLength, thm := some ``linspaceIntLength_proven },

  { id := "rangescov-linspace-int128-overflow", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_linspace(::Type{T}, ::Integer, ::Integer, ::Integer, ::Integer)"],
    statement := "For Int128 endpoints 0 < a <= b, the first element of range(a, b; length=n) is not negative.",
    source := "range docstring (elements lie between start and stop)", status := .refuted, prop := ``LinspaceIntPositive, thm := some ``linspaceIntPositive_refuted, issue := "repro/rangescov-linspace-int128-overflow.jl" },

  { id := "rangescov-floatrange-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["floatrange(::Type{T}, ::Integer, ::Integer, ::Integer, ::Integer)"],
    statement := "floatrange(Float64, start_n, step_n, len, den) has length len whenever it returns.",
    source := "range length invariant; base/twiceprecision.jl:380-392", status := .proven, prop := ``FloatrangeLength, thm := some ``floatrangeLength_proven },

  { id := "rangescov-hp-ratio-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["steprangelen_hp(::Type{Float64}, ::Tuple{Integer,Integer}, ::Tuple{Integer,Integer}, ::Integer, ::Integer, ::Integer)"],
    statement := "steprangelen_hp(Float64, ref::Tuple, step::Tuple, nb, len, offset) has length len.",
    source := "range length invariant; base/twiceprecision.jl:342-347", status := .proven, prop := ``HpRatioLength, thm := some ``hpRatioLength_proven },

  { id := "rangescov-hp-float-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["steprangelen_hp(::Type{Float64}, ::F_or_FF, ::F_or_FF, ::Integer, ::Integer, ::Integer)"],
    statement := "steprangelen_hp(Float64, ref, step, nb, len, offset) with float arguments has length len.",
    source := "range length invariant; base/twiceprecision.jl:360-365", status := .proven, prop := ``HpFloatLength, thm := some ``hpFloatLength_proven },

  { id := "rangescov-rssl-promote-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range_start_step_length(::Real, ::IEEEFloat, ::Integer)", "range_start_step_length(::IEEEFloat, ::Real, ::Integer)"],
    statement := "range(a; step=s, length=n) with one Int and one Float64 argument has n elements.",
    source := "range docstring; base/twiceprecision.jl:441-445", status := .proven, prop := ``RsslPromoteLength, thm := some ``rsslPromoteLength_proven },

  { id := "rangescov-rstsl-promote-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["range_step_stop_length(::Real, ::IEEEFloat, ::Integer)", "range_step_stop_length(::IEEEFloat, ::Real, ::Integer)"],
    statement := "range(; step=s, stop=b, length=n) with one Int and one Float64 argument has n elements.",
    source := "range docstring; base/twiceprecision.jl:468-472", status := .proven, prop := ``RstslPromoteLength, thm := some ``rstslPromoteLength_proven },

  { id := "rangescov-linspace-float-method", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_linspace(::T, ::T, ::Integer) where T<:IEEEFloat"],
    statement := "_linspace(start, stop, len) for Float64 has length len and rejects non-finite endpoints with ArgumentError.",
    source := "range docstring; base/twiceprecision.jl:670-713", status := .proven, prop := ``LinspaceFloatMethod, thm := some ``linspaceFloatMethod_proven },

  { id := "rangescov-linspace1-method", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_linspace1(::Type{T}, start, stop, ::Integer) where T<:IEEEFloat"],
    statement := "_linspace1(Float64, a, b, len) has length len, rejects negative lengths and rejects len == 1 with different endpoints.",
    source := "range docstring; base/twiceprecision.jl:737-750", status := .proven, prop := ``Linspace1Method, thm := some ``linspace1Method_proven },

  { id := "rangescov-scalar-mul-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["*(::Real, ::StepRangeLen{<:Real,<:TwicePrecision})", "*(::StepRangeLen{<:Real,<:TwicePrecision}, ::Real)"],
    statement := "x*r and r*x keep the length and offset of a Float64 StepRangeLen.",
    source := "* on arrays is elementwise (same length); base/twiceprecision.jl:535-537", status := .proven, prop := ``ScalarMulLength, thm := some ``scalarMulLength_proven },

  { id := "rangescov-scalar-div-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["/(::StepRangeLen{<:Real,<:TwicePrecision}, ::Real)"],
    statement := "r/x keeps the length and offset of a Float64 StepRangeLen.",
    source := "/ on arrays by a scalar is elementwise (same length); base/twiceprecision.jl:538-539", status := .proven, prop := ``ScalarDivLength, thm := some ``scalarDivLength_proven },

  { id := "rangescov-hiprec-bool", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_getindex_hiprec(::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision}, ::Integer)"],
    statement := "_getindex_hiprec(r, i) rejects Bool indices with ArgumentError.",
    source := "Bool indices are not integer indices (base/abstractarray.jl); base/twiceprecision.jl:488-495", status := .proven, prop := ``HiprecBool, thm := some ``hiprecBool_proven },

  { id := "rangescov-add-srl-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["+(::StepRangeLen{T,R}, ::StepRangeLen{T,R}) where R<:TwicePrecision"],
    statement := "r1 + r2 of Float64 StepRangeLens throws DimensionMismatch for different lengths and otherwise has the common length.",
    source := "+ on arrays (base/arraymath.jl); base/twiceprecision.jl:627-642", status := .proven, prop := ``AddSrlLength, thm := some ``addSrlLength_proven },

  { id := "rangescov-t556-convert-srl-int", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_convertSRL(::Type,::StepRangeLen{<:Integer})"],
    statement := "Integer counted conversion preserves length and offset.",
    source := "base/twiceprecision.jl:556-558", status := .proven, prop := ``CountedSRLConversion, thm := some ``countedSRLConversion_proven },

  { id := "rangescov-t564-convert-srl-float", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["_convertSRL(::Type,::AbstractRange{U})"],
    statement := "Float conversion transfers exact rational approximations or uses the fallback, preserving length.",
    source := "base/twiceprecision.jl:564-582", status := .proven, prop := ``FloatSRLConversionLength, thm := some ``floatSRLConversionLength_proven },

  { id := "rangescov-t584-convert-srl-fallback", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["__convertSRL(::Type,::StepRangeLen{U})"],
    statement := "The fallback converts stored fields and preserves length and offset.",
    source := "base/twiceprecision.jl:584-586", status := .proven, prop := ``FallbackSRLConversion, thm := some ``fallbackSRLConversion_proven },

  { id := "rangescov-t587-convert-range-fallback", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["__convertSRL(::Type,::AbstractRange{U})"],
    statement := "The fallback converts first, step and length and uses offset one.",
    source := "base/twiceprecision.jl:587-589", status := .proven, prop := ``FallbackRangeConversion, thm := some ``fallbackRangeConversion_proven },

  { id := "twiceprecision-canonicalize2-exact-sum", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["canonicalize2(big, little)"],
    statement := "For finite binary64 inputs whose rounded sum is finite and whose magnitudes satisfy the two-sum ordering condition, the returned high and low parts preserve the exact rational sum.",
    source := "base/twiceprecision.jl:48-51 (two-sum normalization)", status := .proven, prop := ``Canonicalize2ExactSum, thm := some ``canonicalize2ExactSum_proven },

  { id := "twiceprecision-add12-exact-sum", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["add12(x::T, y::T) where {T}", "add12(x, y)"],
    statement := "For finite binary64 inputs whose rounded sum is finite, add12 returns high and low parts whose exact rational sum equals the exact input sum.",
    source := "base/twiceprecision.jl:83-87; two-sum invariant", status := .proven, prop := ``Add12ExactSum, thm := some ``add12ExactSum_proven },

  { id := "twiceprecision-mul12-exact-product", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["mul12(x::T, y::T) where {T<:AbstractFloat}"],
    statement := "For finite binary64 inputs with finite product, mul12 returns two parts whose exact rational sum equals the exact product.",
    source := "base/twiceprecision.jl:114-117 (two-product invariant)", status := .proven, prop := ``Mul12ProductExact, thm := some ``mul12ProductExact_proven },

  { id := "twiceprecision-div12-rounded", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["div12(x::T, y::T) where {T<:AbstractFloat}"],
    statement := "For finite binary64 operands and a nonzero divisor, div12 returns parts whose rounded sum is the floating-point quotient.",
    source := "base/twiceprecision.jl:146-154 (division residual)", status := .refuted, prop := ``Div12Rounded, thm := some ``div12Rounded_refuted, issue := "repro/twiceprecision-div12-rounded.jl" },

  { id := "twiceprecision-value-constructor", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["TwicePrecision{T}(x::T) where {T}"],
    statement := "Constructing a two-part value from a finite binary64 number retains that number when the two parts are added.",
    source := "base/twiceprecision.jl:201 (TwicePrecision representation)", status := .proven, prop := ``TpFromSamePreservesValue, thm := some ``tpFromSamePreservesValue_proven },

  { id := "twiceprecision-constructor-value", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["TwicePrecision{T}(x) where {T}"],
    statement := "For every exactly representable integer, any successful Float64 conversion preserves its exact value in the two parts.",
    source := "base/twiceprecision.jl:205-209 (two-part conversion constructor)", status := .proven, prop := ``TpFromValueExact, thm := some ``tpFromValueExact_proven },

  { id := "twiceprecision-ratio-value", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["TwicePrecision{T}(nd::Tuple{Integer,Integer})", "TwicePrecision{T}(nd::Tuple{Any,Any})"],
    statement := "For bounded exactly representable integer numerators and nonzero denominators, the Float64 ratio constructor rounds the represented quotient to the Float64 division result.",
    source := "base/twiceprecision.jl:217-225 (ratio constructors)", status := .proven, prop := ``TpRatioValue, thm := some ``tpRatioValue_proven },

  { id := "twiceprecision-truncation-preserves-value", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["TwicePrecision{T}(nd::Tuple{I,I}, nb::Integer)", "TwicePrecision{T}(nd::Tuple{Integer,Integer}, nb::Integer)", "twiceprecision(val::T, nb::Integer)", "twiceprecision(val::TwicePrecision{T}, nb::Integer)"],
    statement := "For finite Float64 inputs, splitting or truncating a two-part value preserves its represented value when the low part is added back.",
    source := "base/twiceprecision.jl:227-249 (precision-limited constructors)", status := .proven, prop := ``TwiceprecisionTruncPreservesValue, thm := some ``twiceprecisionTruncPreservesValue_proven },

  { id := "twiceprecision-nbitslen-offset-capacity", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["nbitslen(::Type{T}, len, offset)", "nbitslen(len, offset)"],
    statement := "For lengths through 2^27 and valid offsets, the precision count returned by nbitslen can represent the largest distance from the range offset.",
    source := "base/twiceprecision.jl:252-256 (range index precision)", status := .proven, prop := ``NbitslenCoversOffsets, thm := some ``nbitslenCoversOffsets_proven },

  { id := "twiceprecision-number-conversions", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["convert(::Type{T}, x::TwicePrecision) where {T<:Number}", "convert(::Type{TwicePrecision{T}}, x::TwicePrecision) where {T}", "convert(::Type{TwicePrecision{T}}, x::Number) where {T}", "float(x::TwicePrecision)", "big(x::TwicePrecision)"],
    statement := "Float conversion rounds the sum of the parts, component conversion converts both parts, and BigFloat conversion preserves their exact rational sum.",
    source := "base/twiceprecision.jl:265-277 (conversion and float methods)", status := .proven, prop := ``TpNumberConversions, thm := some ``tpNumberConversions_proven },

  { id := "twiceprecision-zero-representation", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["zero(x::TwicePrecision)", "zero(::Type{TwicePrecision{T}}) where {T}"],
    statement := "The zero of a twice-precision type represents exactly zero.",
    source := "base/twiceprecision.jl:281-285 (zero constructors)", status := .proven, prop := ``TpZeroValue, thm := some ``tpZeroValue_proven },

  { id := "twiceprecision-arithmetic-values", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["+(x::TwicePrecision, y::Number)", "+(x::TwicePrecision{T}, y::TwicePrecision{T})", "-(x::TwicePrecision, y::Number)", "-(x::TwicePrecision, y::TwicePrecision)", "*(x::TwicePrecision, v::Number)", "*(x::TwicePrecision{<:IEEEFloat}, v::Integer)", "*(x::TwicePrecision{T}, y::TwicePrecision{T})", "/(x::TwicePrecision, v::Number)", "/(x::TwicePrecision, y::TwicePrecision)"],
    statement := "For finite Float64 inputs with finite exact results, two-part addition, subtraction, multiplication, and division preserve the represented arithmetic value to their stated rounding precision.",
    source := "base/twiceprecision.jl:289-335 (twice-precision arithmetic)", status := .proven, prop := ``TpNumericOperations, thm := some ``tpNumericOperations_proven },

  { id := "twiceprecision-step-range-value", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["step(r::StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}})"],
    statement := "A successful Float64 start-step-length construction reports the requested step through the StepRangeLen step method.",
    source := "base/twiceprecision.jl:438-439,450-466", status := .proven, prop := ``RsslStepReportsInput, thm := some ``rsslStepReportsInput_proven },

  { id := "twiceprecision-slice-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, s::OrdinalRange{S})"],
    statement := "A successful ordinal-range slice of a twice-precision StepRangeLen has the same length as the slice indices.",
    source := "base/twiceprecision.jl:497-533 (range slicing)", status := .proven, prop := ``TpSliceLength, thm := some ``tpSliceLength_proven },

  { id := "twiceprecision-rat-terminates", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["rat(x)"],
    statement := "For every finite Float64 input, a successful rational approximation has a positive denominator.",
    source := "base/twiceprecision.jl:757-772 (continued-fraction approximation)", status := .proven, prop := ``RatDenominatorPositive, thm := some ``ratDenominatorPositive_proven },

  { id := "twiceprecision-hp-float-generic-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["steprangelen_hp(::Type{T}, ref::F_or_FF, step::F_or_FF, nb, len, offset) where {T<:IEEEFloat}"],
    statement := "The generic IEEE high-precision range builder retains the requested length whenever its constructor succeeds.",
    source := "base/twiceprecision.jl:367-371 (high-precision range construction)", status := .proven, prop := ``HpFloatIEEELength, thm := some ``hpFloatIEEELength_proven },

  { id := "twiceprecision-hp-ratio-generic-length", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["steprangelen_hp(::Type{T}, ref::Tuple{Integer,Integer}, step::Tuple{Integer,Integer}, nb, len, offset) where {T<:IEEEFloat}"],
    statement := "The generic IEEE ratio-based high-precision range builder retains the requested length whenever its constructor succeeds.",
    source := "base/twiceprecision.jl:349-353 (ratio-based high-precision range construction)", status := .proven, prop := ``HpTupleLength, thm := some ``hpTupleLength_proven },

  { id := "twiceprecision-lcm-unchecked-multiple", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["lcm_unchecked(a::T, b::T) where T<:Integer"],
    statement := "For nonzero gcd, lcm_unchecked returns a times the truncated quotient b/gcd(a,b).",
    source := "base/twiceprecision.jl:775 (lcm_unchecked definition)", status := .proven, prop := ``LcmUncheckedMultiple, thm := some ``lcmUncheckedMultiple_proven },

  { id := "twiceprecision-srl-twice-sum-values", juliaFile := "base/twiceprecision.jl",
    juliaFns := ["sum(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision})"],
    statement := "For a finite integer-valued Float64 StepRangeLen whose exact sum fits in the exactly representable Float64 range, the optimized sum equals that exact integer sum.",
    source := "base/twiceprecision.jl:606-622 (twice-precision range sum)", status := .refuted, prop := ``SrlTwiceSumMatches, thm := some ``srlTwiceSumMatches_refuted, issue := "repro/twiceprecision-srl-twice-sum-values.jl" },
]

/-!
## Nothing to promise

* `truncmask@31`: The generic truncmask fallback is an internal identity path with no independent documented guarantee.
* `truncbits@36`: The generic truncbits fallback is an internal identity path with no independent documented guarantee.
* `mul12@119`: The generic mixed-type mul12 fallback only selects promoted arithmetic; the numeric product contract is covered for supported concrete cases.
* `div12@155`: The generic div12 fallback only packages the underlying quotient and zero residual.
* `div12@156`: The generic mixed-type div12 fallback only selects promoted arithmetic.
* `TwicePrecision@214`: This generic outer constructor is a dispatch adapter; the value-preserving constructor contract is stated separately.
* `eltype@258`: eltype is type metadata, not an independent value-level behavior.
* `promote_rule@260`: promote_rule only chooses the promoted element type; this task does not model Julia type dispatch.
* `promote_rule@262`: promote_rule only chooses the promoted element type; this task does not model Julia type dispatch.
* `asF64@357`: asF64 is an internal scalar-conversion adapter used by the high-precision range builder.
* `asF64@358`: asF64 is an internal pair-conversion adapter used by the high-precision range builder.
* `StepRangeLen@375`: The StepRangeLen constructor delegates validation and field construction to the range model.
* `narrow@777`: narrow is a type-level precision-selection helper with no independent value-level contract.
* `narrow@778`: narrow is a type-level precision-selection helper with no independent value-level contract.
* `narrow@779`: narrow is a type-level precision-selection helper with no independent value-level contract.
* `narrow@780`: narrow is a type-level precision-selection helper with no independent value-level contract.
* `_tp_prod@782`: _tp_prod is an internal variadic helper for LogRange arithmetic; pair multiplication is covered separately.
* `_tp_prod@786`: _tp_prod is the empty-product base case for an internal LogRange helper.
* `_exp_allowing_twice64@794`: _exp_allowing_twice64 is an internal LogRange adapter, not a public numeric contract.
* `_exp_allowing_twice64@795`: _exp_allowing_twice64 is an internal LogRange adapter, not a public numeric contract.
* `_log_twice64_unchecked@798`: _log_twice64_unchecked is an internal LogRange helper without an independent documented result contract.
-/

/-! ## Method-to-property coverage -/

def methodProperties : List (String × List String) := [
  ("splitprec@22", ["floatranges-splitprec-typemax"]),
  ("truncmask@28", ["rangescov-truncbits-identity"]),
  ("truncmask@31", ["rangescov-truncbits-identity"]),
  ("truncbits@33", ["rangescov-truncbits-identity"]),
  ("truncbits@36", ["rangescov-truncbits-identity"]),
  ("canonicalize2@48", ["twiceprecision-canonicalize2-exact-sum"]),
  ("add12@83", ["twiceprecision-add12-exact-sum"]),
  ("add12@87", ["twiceprecision-add12-exact-sum"]),
  ("mul12@114", ["twiceprecision-mul12-exact-product"]),
  ("mul12@118", ["rangescov-mul12-int"]),
  ("mul12@119", ["rangescov-mul12-int"]),
  ("div12@146", ["twiceprecision-div12-rounded"]),
  ("div12@155", []),
  ("div12@156", []),
  ("TwicePrecision{T}@201", ["twiceprecision-value-constructor"]),
  ("TwicePrecision{T}@203", ["twiceprecision-number-conversions"]),
  ("TwicePrecision{T}@205", ["twiceprecision-constructor-value"]),
  ("TwicePrecision{T}@211", ["floatranges-splitprec-typemax"]),
  ("TwicePrecision@214", ["twiceprecision-value-constructor"]),
  ("TwicePrecision{T}@217", ["twiceprecision-ratio-value"]),
  ("TwicePrecision{T}@222", ["twiceprecision-ratio-value"]),
  ("TwicePrecision{T}@227", ["twiceprecision-truncation-preserves-value"]),
  ("TwicePrecision{T}@235", ["twiceprecision-truncation-preserves-value"]),
  ("twiceprecision@241", ["twiceprecision-truncation-preserves-value"]),
  ("twiceprecision@246", ["twiceprecision-truncation-preserves-value"]),
  ("nbitslen@251", ["twiceprecision-nbitslen-offset-capacity"]),
  ("nbitslen@252", ["twiceprecision-nbitslen-offset-capacity"]),
  ("nbitslen@256", ["twiceprecision-nbitslen-offset-capacity"]),
  ("eltype@258", ["twiceprecision-number-conversions"]),
  ("promote_rule@260", ["twiceprecision-number-conversions"]),
  ("promote_rule@262", ["twiceprecision-number-conversions"]),
  ("(::Type{T})@265", ["twiceprecision-number-conversions"]),
  ("convert@267", ["twiceprecision-number-conversions"]),
  ("convert@268", ["twiceprecision-number-conversions"]),
  ("convert@271", ["twiceprecision-number-conversions"]),
  ("convert@272", ["twiceprecision-number-conversions"]),
  ("float@274", ["twiceprecision-number-conversions"]),
  ("float@275", ["twiceprecision-number-conversions"]),
  ("big@277", ["twiceprecision-number-conversions"]),
  ("-@279", ["rangescov-tp-neg-involution"]),
  ("zero@281", ["twiceprecision-zero-representation"]),
  ("zero@282", ["twiceprecision-zero-representation"]),
  ("+@289", ["twiceprecision-arithmetic-values"]),
  ("+@293", ["twiceprecision-arithmetic-values"]),
  ("+@295", ["twiceprecision-arithmetic-values"]),
  ("+@300", ["twiceprecision-arithmetic-values"]),
  ("-@302", ["twiceprecision-arithmetic-values"]),
  ("-@303", ["twiceprecision-arithmetic-values"]),
  ("-@304", ["twiceprecision-arithmetic-values"]),
  ("*@306", ["twiceprecision-arithmetic-values"]),
  ("*@310", ["twiceprecision-arithmetic-values"]),
  ("*@316", ["twiceprecision-arithmetic-values"]),
  ("*@318", ["twiceprecision-arithmetic-values"]),
  ("*@323", ["twiceprecision-arithmetic-values"]),
  ("/@325", ["twiceprecision-arithmetic-values"]),
  ("/@329", ["twiceprecision-arithmetic-values"]),
  ("steprangelen_hp@342", ["rangescov-hp-ratio-length"]),
  ("steprangelen_hp@349", ["twiceprecision-hp-ratio-generic-length"]),
  ("asF64@357", ["twiceprecision-hp-float-generic-length"]),
  ("asF64@358", ["twiceprecision-hp-float-generic-length"]),
  ("steprangelen_hp@360", ["rangescov-hp-float-length"]),
  ("steprangelen_hp@367", ["twiceprecision-hp-float-generic-length"]),
  ("StepRangeLen@375", ["rangescov-hp-float-length"]),
  ("floatrange@380", ["rangescov-floatrange-length"]),
  (":@394", ["floatranges-colon-decimal-threshold", "floatranges-colon-infinite-step", "floatranges-colon-nonfinite-error", "floatranges-colon-overshoot-stop", "floatranges-colon-signed-zero", "floatranges-colon-underflow-nonempty"]),
  ("step@438", ["twiceprecision-step-range-value"]),
  ("step@439", ["twiceprecision-step-range-value"]),
  ("range_start_step_length@441", ["rangescov-rssl-promote-length"]),
  ("range_start_step_length@444", ["rangescov-rssl-promote-length"]),
  ("range_start_step_length@447", ["floatranges-range-length"]),
  ("range_start_step_length@450", ["floatranges-range-length"]),
  ("range_step_stop_length@468", ["rangescov-rstsl-promote-length"]),
  ("range_step_stop_length@471", ["rangescov-rstsl-promote-length"]),
  ("range_step_stop_length@474", ["floatranges-range-length"]),
  ("unsafe_getindex@480", ["floatranges-start-step-overflow-nan"]),
  ("_getindex_hiprec@488", ["rangescov-hiprec-bool"]),
  ("getindex@497", ["twiceprecision-slice-length"]),
  ("*@535", ["rangescov-scalar-mul-length"]),
  ("*@537", ["rangescov-scalar-mul-length"]),
  ("/@538", ["rangescov-scalar-div-length"]),
  ("StepRangeLen{T,R,S,L}@541", ["rangescov-twice-conversions"]),
  ("StepRangeLen{T,R,S,L}@543", ["rangescov-twice-conversions"]),
  ("StepRangeLen{Float64}@546", ["rangescov-twice-conversions"]),
  ("StepRangeLen{T}@548", ["rangescov-twice-conversions"]),
  ("StepRangeLen{Float64}@551", ["rangescov-twice-conversions"]),
  ("StepRangeLen{T}@553", ["rangescov-twice-conversions"]),
  ("_convertSRL@556", ["rangescov-twice-conversions", "rangescov-t556-convert-srl-int"]),
  ("_convertSRL@560", ["rangescov-twice-conversions"]),
  ("_convertSRL@564", ["rangescov-twice-conversions", "rangescov-t564-convert-srl-float"]),
  ("__convertSRL@584", ["rangescov-twice-conversions", "rangescov-t584-convert-srl-fallback"]),
  ("__convertSRL@587", ["rangescov-twice-conversions", "rangescov-t587-convert-range-fallback"]),
  ("sum@591", ["rangescov-steprangelen-sum-small-int"]),
  ("sum@606", ["twiceprecision-srl-twice-sum-values"]),
  ("sumpair@625", ["rangescov-sumpair-product"]),
  ("+@627", ["rangescov-add-srl-length"]),
  ("range_start_stop_length@647", ["floatranges-range-length"]),
  ("_linspace@670", ["rangescov-linspace-float-method", "floatranges-linspace-imin-overflow", "floatranges-linspace-tiny-endpoint", "floatranges-range-length"]),
  ("_linspace@717", ["rangescov-linspace-int-imin-inexact", "rangescov-linspace-int-length"]),
  ("_linspace@718", ["rangescov-linspace-int-imin-inexact", "rangescov-linspace-int-length", "rangescov-linspace-int128-overflow"]),
  ("_linspace1@737", ["rangescov-linspace1-method"]),
  ("rat@757", ["twiceprecision-rat-terminates", "floatranges-colon-decimal-threshold"]),
  ("lcm_unchecked@775", ["twiceprecision-lcm-unchecked-multiple"]),
  ("narrow@777", ["twiceprecision-rat-terminates"]),
  ("narrow@778", ["twiceprecision-rat-terminates"]),
  ("narrow@779", ["twiceprecision-rat-terminates"]),
  ("narrow@780", ["twiceprecision-rat-terminates"]),
  ("_tp_prod@782", ["twiceprecision-srl-twice-sum-values"]),
  ("_tp_prod@786", ["twiceprecision-srl-twice-sum-values"]),
  ("<@787", ["rangescov-tp-lt-irrefl"]),
  ("isbetween@790", ["rangescov-isbetween-symmetric"]),
  ("_exp_allowing_twice64@794", []),
  ("_exp_allowing_twice64@795", []),
  ("_log_twice64_unchecked@798", []),
]

end JuliaLean.Proofs.base.twiceprecision
