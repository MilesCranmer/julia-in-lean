import JuliaLean.MathFuncs.PropsTrig

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Proofs of the `sinpi`/`cospi`/`sincospi`/`tanpi`, `rem2pi` and `cbrt` properties stated in
`JuliaLean.MathFuncs.PropsTrig`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

namespace TrigProofs

theorem tbOfBits (n : Nat) : F64.toBits (F64.ofBits n) = n % 2^64 := by
  simp [F64.toBits, F64.ofBits]

theorem tbLt (x : F64) : F64.toBits x < 2^64 := x.isLt

theorem ext {x y : F64} (h : F64.toBits x = F64.toBits y) : x = y := BitVec.eq_of_toNat_eq h

theorem tbAbs (x : F64) : F64.toBits (F64.abs x) = F64.toBits x % 2^63 := by
  have := tbLt x
  unfold F64.abs
  rw [tbOfBits]
  omega

theorem tbNeg (x : F64) : F64.toBits (F64.neg x) =
    if F64.toBits x ≥ 2^63 then F64.toBits x - 2^63 else F64.toBits x + 2^63 := by
  have := tbLt x
  unfold F64.neg F64.signbit
  by_cases h : F64.toBits x ≥ 2^63
  · simp [h, tbOfBits] <;> omega
  · simp [h, tbOfBits] <;> omega

theorem absNeg (x : F64) : F64.abs (F64.neg x) = F64.abs x := by
  apply ext
  have := tbLt x
  rw [tbAbs, tbAbs, tbNeg]
  split <;> omega

theorem signbitNeg (x : F64) : F64.signbit (F64.neg x) = !F64.signbit x := by
  have := tbLt x
  unfold F64.signbit
  rw [tbNeg]
  by_cases h : F64.toBits x ≥ 2^63
  · have h' : ¬ (F64.toBits x - 2^63 ≥ 2^63) := by omega
    simp [h, h']
  · have h' : F64.toBits x + 2^63 ≥ 2^63 := by omega
    simp [h, h']

theorem negNeg (x : F64) : F64.neg (F64.neg x) = x := by
  apply ext
  have := tbLt x
  have h1 := tbNeg x
  have h2 := tbNeg (F64.neg x)
  split at h1 <;> split at h2 <;> omega

theorem isnanIff (x : F64) : F64.isnan x = true ↔
    (F64.toBits x / 2^52 % 2048 = 2047 ∧ F64.toBits x % 2^52 ≠ 0) := by
  simp [F64.isnan, F64.exponentField, F64.fraction]

theorem isfiniteIff (x : F64) : F64.isfinite x = true ↔ F64.toBits x / 2^52 % 2048 ≠ 2047 := by
  simp [F64.isfinite, F64.exponentField]

theorem isinfIff (x : F64) : F64.isinf x = true ↔ F64.toBits x % 2^63 = 2047 * 2^52 := by
  simp [F64.isinf, tbAbs]

theorem isnanAbs (x : F64) : F64.isnan (F64.abs x) = F64.isnan x := by
  have := tbLt x
  unfold F64.isnan F64.exponentField F64.fraction
  rw [tbAbs]
  have h1 : F64.toBits x % 2^63 / 2^52 % 2048 = F64.toBits x / 2^52 % 2048 := by omega
  have h2 : F64.toBits x % 2^63 % 2^52 = F64.toBits x % 2^52 := by omega
  rw [h1, h2]

theorem isfiniteAbs (x : F64) : F64.isfinite (F64.abs x) = F64.isfinite x := by
  have := tbLt x
  unfold F64.isfinite F64.exponentField
  rw [tbAbs]
  have h1 : F64.toBits x % 2^63 / 2^52 % 2048 = F64.toBits x / 2^52 % 2048 := by omega
  rw [h1]

theorem finNotNan {x : F64} (h : F64.isfinite x = true) : F64.isnan x = false := by
  rw [Bool.eq_false_iff, ne_eq, isnanIff]
  rw [isfiniteIff] at h
  omega

theorem finNotInf {x : F64} (h : F64.isfinite x = true) : F64.isinf x = false := by
  have := tbLt x
  rw [Bool.eq_false_iff, ne_eq, isinfIff]
  rw [isfiniteIff] at h
  omega

theorem infNotNan {x : F64} (h : F64.isinf x = true) : F64.isnan x = false := by
  have := tbLt x
  rw [Bool.eq_false_iff, ne_eq, isnanIff]
  rw [isinfIff] at h
  omega

theorem infNotFin {x : F64} (h : F64.isinf x = true) : F64.isfinite x = false := by
  have := tbLt x
  rw [Bool.eq_false_iff, ne_eq, isfiniteIff]
  rw [isinfIff] at h
  omega

theorem nanNotFin {x : F64} (h : F64.isnan x = true) : F64.isfinite x = false := by
  rw [Bool.eq_false_iff, ne_eq, isfiniteIff]
  rw [isnanIff] at h
  omega

theorem nonfinInf {x : F64} (hf : F64.isfinite x = false) (hn : F64.isnan x = false) :
    F64.isinf x = true := by
  have := tbLt x
  rw [isinfIff]
  rw [Bool.eq_false_iff, ne_eq, isfiniteIff] at hf
  rw [Bool.eq_false_iff, ne_eq, isnanIff] at hn
  omega

theorem copysignZeroNeg (x : F64) :
    copysign F64.zero (F64.neg x) = F64.neg (copysign F64.zero x) := by
  unfold copysign
  rw [signbitNeg]
  cases F64.signbit x <;> decide +kernel

theorem isnanNan : F64.isnan F64.nan = true := by decide +kernel

theorem twoPiRoundDown : F64.mul (F64.ofInt 2) piRoundDown = pi4o2H := by decide +kernel

/-- `sincospi` with its private quadrant helper unfolded. -/
theorem sincospiEq (x0 : F64) : sincospi x0 =
    (if (!F64.isfinite (F64.abs x0)) = true then
      (if F64.isnan (F64.abs x0) = true then .ok (F64.abs x0, F64.abs x0)
       else .error (.domainError "sincospi"))
    else if F64.le maxintfloat (F64.abs x0) = true then .ok (copysign F64.zero x0, F64.one)
    else
      let rx := (piReduce (F64.abs x0)).1
      let n := (piReduce (F64.abs x0)).2
      let q :=
        if n == 0 then (sinpiKernel rx, cospiKernel rx)
        else if n == 1 then (cospiKernel rx, F64.sub F64.zero (sinpiKernel rx))
        else if n == 2 then
          (F64.sub F64.zero (sinpiKernel rx), F64.sub F64.zero (cospiKernel rx))
        else (F64.sub F64.zero (cospiKernel rx), sinpiKernel rx)
      .ok (if F64.signbit x0 = true then F64.neg q.1 else q.1, q.2)) := rfl

/-- `cbrtExactCubes` at the offset `n`. -/
def cbrtCubeAt (n : Nat) : Prop :=
  cbrt (F64.ofInt (((n : Int) + 1)^3)) = F64.ofInt ((n : Int) + 1) ∧
    cbrt (F64.ofInt (-((n : Int) + 1)^3)) = F64.ofInt (-((n : Int) + 1))

instance (n : Nat) : Decidable (cbrtCubeAt n) := by unfold cbrtCubeAt; infer_instance

theorem cbrtCubeAt_0 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 0) := by decide +kernel
theorem cbrtCubeAt_1 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 1) := by decide +kernel
theorem cbrtCubeAt_2 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 2) := by decide +kernel
theorem cbrtCubeAt_3 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 3) := by decide +kernel
theorem cbrtCubeAt_4 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 4) := by decide +kernel
theorem cbrtCubeAt_5 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 5) := by decide +kernel
theorem cbrtCubeAt_6 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 6) := by decide +kernel
theorem cbrtCubeAt_7 : ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * 7) := by decide +kernel

theorem cbrtCubeAll (k : Fin 1024) : cbrtCubeAt k.val := by
  have h : ∀ c : Fin 8, ∀ i : Fin 128, cbrtCubeAt (i.val + 128 * c.val) := by
    intro c
    match c with
    | ⟨0, _⟩ => exact cbrtCubeAt_0
    | ⟨1, _⟩ => exact cbrtCubeAt_1
    | ⟨2, _⟩ => exact cbrtCubeAt_2
    | ⟨3, _⟩ => exact cbrtCubeAt_3
    | ⟨4, _⟩ => exact cbrtCubeAt_4
    | ⟨5, _⟩ => exact cbrtCubeAt_5
    | ⟨6, _⟩ => exact cbrtCubeAt_6
    | ⟨7, _⟩ => exact cbrtCubeAt_7
    | ⟨n + 8, hn⟩ => exact absurd hn (by omega)
  have := h ⟨k.val / 128, by omega⟩ ⟨k.val % 128, by omega⟩
  rwa [show k.val % 128 + 128 * (k.val / 128) = k.val by omega] at this

end TrigProofs

open TrigProofs

theorem cospiEven_proven : cospiEven := by
  intro x
  simp only [cospi, cospiWith, absNeg]

theorem piTrigSpecial_proven : piTrigSpecial := by
  intro x
  constructor
  · intro hi
    have hf : F64.isfinite (F64.abs x) = false := by rw [isfiniteAbs]; exact infNotFin hi
    have hn : F64.isnan (F64.abs x) = false := by rw [isnanAbs]; exact infNotNan hi
    refine ⟨⟨"sinpi", ?_⟩, ⟨"cospi", ?_⟩, ⟨"tanpi", ?_⟩, ⟨"sincospi", ?_⟩⟩
    · simp [sinpi, sinpiWith, hf, hn]
    · simp [cospi, cospiWith, hf, hn]
    · simp [tanpi, tanpiWith, hf, hn]
    · simp [sincospiEq, hf, hn]
  · intro hn0
    have hn : F64.isnan (F64.abs x) = true := by rw [isnanAbs]; exact hn0
    have hf : F64.isfinite (F64.abs x) = false := nanNotFin hn
    refine ⟨⟨F64.abs x, ?_, hn⟩, ⟨F64.abs x, ?_, hn⟩, ⟨F64.abs x, ?_, hn⟩,
      ⟨F64.abs x, F64.abs x, ?_, hn, hn⟩⟩
    · simp [sinpi, sinpiWith, hf, hn]
    · simp [cospi, cospiWith, hf, hn]
    · simp [tanpi, tanpiWith, hf, hn]
    · simp [sincospiEq, hf, hn]

theorem piTrigLarge_proven : piTrigLarge := by
  intro x hf hl
  have hf' : F64.isfinite (F64.abs x) = true := by rw [isfiniteAbs]; exact hf
  have hl' : F64.le maxintfloat (F64.abs x) = true := hl
  refine ⟨?_, ?_, ?_⟩
  · simp [sinpi, sinpiWith, hf', hl']
  · simp [cospi, cospiWith, hf', hl']
  · simp [tanpi, tanpiWith, hf', hl']

theorem rem2piNonfinite_proven : rem2piNonfinite := by
  intro x m hm hf
  cases hn : F64.isnan x
  · have hi := nonfinInf hf hn
    refine ⟨F64.nan, ?_, isnanNan⟩
    cases m <;> simp [rem2pi, rem2piNearest, rem2piToZero, rem2piDown, rem2piUp, hn, hi] at hm ⊢
  · refine ⟨x, ?_, hn⟩
    cases m <;> simp [rem2pi, rem2piNearest, rem2piToZero, rem2piDown, rem2piUp, hn] at hm ⊢

theorem rem2piSmallExact_proven : rem2piSmallExact := by
  intro x hf
  have hn := finNotNan hf
  have hi := finNotInf hf
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · simp [rem2pi, rem2piNearest, ltPi, hn, hi, h]
  · simp [rem2pi, rem2piDown, hn, hi, h1, h2]
  · simp [rem2pi, rem2piUp, hn, hi, h1, h2]
  · simp [rem2pi, rem2piToZero, twoPiRoundDown, hn, hi, h]

theorem sinpiOdd_proven : sinpiOdd := by
  intro x hn
  have hn' : F64.isnan (F64.abs x) = false := by rw [isnanAbs]; exact hn
  simp only [sinpi, sinpiWith, absNeg, signbitNeg, copysignZeroNeg]
  cases hf : F64.isfinite (F64.abs x) <;> cases hl : F64.le maxintfloat (F64.abs x) <;>
    cases hs : F64.signbit x <;> simp [hn', negNeg, Except.map]

theorem sincospiConsistent_proven : sincospiConsistent := by
  intro x hinf
  rw [sincospiEq]
  simp only [sinpi, sinpiWith, cospi, cospiWith]
  generalize piReduce (F64.abs x) = p
  obtain ⟨rx, n⟩ := p
  cases hf : F64.isfinite (F64.abs x)
  · cases hn : F64.isnan (F64.abs x)
    · rw [isfiniteAbs] at hf
      rw [isnanAbs] at hn
      rw [nonfinInf hf hn] at hinf
      exact absurd hinf (by decide)
    · simp [Except.bind, Except.map]
  · cases hl : F64.le maxintfloat (F64.abs x)
    · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ (n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2) by omega) with
        h | h | h | ⟨h0, h1, h2⟩
      · subst h; cases F64.signbit x <;> simp [Except.bind, Except.map]
      · subst h; cases F64.signbit x <;> simp [Except.bind, Except.map]
      · subst h; cases F64.signbit x <;> simp [Except.bind, Except.map]
      · cases F64.signbit x <;> simp [h0, h1, h2, Except.bind, Except.map]
    · simp [Except.bind, Except.map]

theorem cbrtSpecial_proven : cbrtSpecial := by
  intro s
  cases s <;> decide +kernel

theorem cbrtExactCubes_proven : cbrtExactCubes := fun k => cbrtCubeAll k

end JuliaLean.MathFuncs
