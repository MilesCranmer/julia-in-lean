import JuliaLean.FloatRanges.StepRangeLen
import JuliaLean.FloatRanges.LinRange
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-!
Properties of Float64 ranges. Refutations evaluate the model on one concrete input
with `decide +kernel`; each has a reproducer `repro/<id>.jl`.
-/

namespace JuliaLean.FloatRanges

open JuliaLean.Float

deriving instance DecidableEq for Except

/-- `p` holds of the result whenever the Julia call returns normally. -/
def okThen {α : Type} (x : Jl α) (p : α → Prop) : Prop :=
  match x with
  | .ok a => p a
  | .error _ => True

instance {α : Type} (x : Jl α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (okThen x p) := by
  unfold okThen; split <;> infer_instance

/-- The Julia call returns normally. -/
def succeeds {α : Type} (x : Jl α) : Prop :=
  match x with
  | .ok _ => True
  | .error _ => False

instance {α : Type} (x : Jl α) : Decidable (succeeds x) := by
  unfold succeeds; split <;> infer_instance

/-! ## Proven properties -/

/-- `r[1] == first(r)` and `r[end] == last(r)` for every nonempty Float64 `StepRangeLen`
(bitwise, so also for NaN elements). -/
def SrlIndexEndpoints : Prop := ∀ r : SRL, 1 ≤ r.len.val →
  r.get (i64 1) = .ok r.first ∧ r.get r.len = .ok r.last

theorem srlIndexEndpoints : SrlIndexEndpoints := by
  intro r h
  have h1 : (i64 1).val = 1 := by decide
  refine ⟨?_, ?_⟩
  · unfold SRL.get SRL.first
    rw [if_pos (by rw [h1]; exact ⟨Int.le_refl 1, h⟩)]
  · unfold SRL.get SRL.last
    rw [if_pos ⟨h, Int.le_refl _⟩]

theorem F64.neg_neg (x : F64) : F64.neg (F64.neg x) = x := by
  have hx : x.toNat < 2^64 := x.isLt
  by_cases h : x.toNat ≥ 2^63
  · have h1 : F64.neg x = BitVec.ofNat 64 (x.toNat - 2^63) := by
      simp [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h]
    have h2 : ¬ ((BitVec.ofNat 64 (x.toNat - 2^63)).toNat ≥ 2^63) := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h2, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · have h1 : F64.neg x = BitVec.ofNat 64 (x.toNat + 2^63) := by
      simp [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h]
    have h2 : (BitVec.ofNat 64 (x.toNat + 2^63)).toNat ≥ 2^63 := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h2, decide_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem TP.neg_neg (x : TP) : x.neg.neg = x := by
  cases x; simp only [TP.neg, F64.neg_neg]

private theorem i64_bounds (x : I64) : -(2^63 : Int) ≤ x.val ∧ x.val ≤ 2^63 - 1 := by
  have := x.property
  simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using this

private theorem rev_off_val (len off : I64) (h1 : 1 ≤ off.val) (h2 : off.val ≤ len.val) :
    (len - off + i64 1).val = len.val - off.val + 1 := by
  have hl := i64_bounds len
  have ho := i64_bounds off
  show wrapInt .i64 (wrapInt .i64 (len.val - off.val) + wrapInt .i64 1) = _
  have e1 : wrapInt .i64 1 = 1 := by decide
  rw [e1, wrapInt_of_inRange .i64 (len.val - off.val)
    (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
  rw [wrapInt_of_inRange .i64 _
    (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]

/-- `reverse(reverse(r)) == r` field by field for every valid Float64 `StepRangeLen`. -/
def SrlReverseInvolution : Prop := ∀ (ref step : TP) (len off : I64) (r : SRL),
  SRL.mk' ref step len off = .ok r → (r.reverse >>= SRL.reverse) = .ok r

private theorem mk'_ok (ref step : TP) (len off : I64) (h1 : ¬ len.val < 0)
    (h2 : 1 ≤ off.val ∧ off.val ≤ max 1 len.val) :
    SRL.mk' ref step len off = .ok ⟨ref, step, len, off⟩ := by
  unfold SRL.mk'; rw [if_neg h1, if_pos h2]

theorem srlReverseInvolution : SrlReverseInvolution := by
  intro ref step len off r h
  unfold SRL.mk' at h
  by_cases hneg : len.val < 0
  · rw [if_pos hneg] at h; cases h
  rw [if_neg hneg] at h
  by_cases hoff : 1 ≤ off.val ∧ off.val ≤ max 1 len.val
  case neg => rw [if_neg hoff] at h; cases h
  rw [if_pos hoff] at h
  cases h
  have key : ∀ (o o' : I64) (st : TP),
      (if len.val = 0 then o else len - o + i64 1) = o' →
      (1 ≤ o'.val ∧ o'.val ≤ max 1 len.val) →
      SRL.reverse ⟨ref, st, len, o⟩ = .ok ⟨ref, st.neg, len, o'⟩ := by
    intro o o' st ho' hc
    show SRL.mk' ref st.neg len (if len.val = 0 then o else len - o + i64 1) = _
    rw [ho']
    exact mk'_ok _ _ _ _ hneg hc
  by_cases hz : len.val = 0
  · rw [key off off step (by rw [if_pos hz]) hoff]
    show SRL.reverse ⟨ref, step.neg, len, off⟩ = _
    rw [key off off step.neg (by rw [if_pos hz]) hoff, TP.neg_neg]
  · have hmax : max 1 len.val = len.val := by omega
    have hoff2 : off.val ≤ len.val := by omega
    have hv := rev_off_val len off hoff.1 hoff2
    have hv2 := rev_off_val len (len - off + i64 1) (by omega) (by omega)
    have hback : len - (len - off + i64 1) + i64 1 = off := by
      apply Subtype.ext; rw [hv2, hv]; omega
    have c1 : 1 ≤ (len - off + i64 1).val ∧ (len - off + i64 1).val ≤ max 1 len.val := by
      rw [hv, hmax]; omega
    rw [key off (len - off + i64 1) step (by rw [if_neg hz]) c1]
    show SRL.reverse ⟨ref, step.neg, len, len - off + i64 1⟩ = _
    rw [key (len - off + i64 1) off step.neg (by rw [if_neg hz]; exact hback) hoff, TP.neg_neg]

/-- Every normal return of `x` has length `n`. -/
def LenIs (n : I64) (x : Jl SRL) : Prop := ∀ r, x = .ok r → r.len = n

theorem mk'_len (ref step : TP) (len off : I64) : LenIs len (SRL.mk' ref step len off) := by
  intro r h
  unfold SRL.mk' at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem hpFloat_len (ref step : TP) (nb : Int) (len off : I64) :
    LenIs len (hpFloat ref step nb len off) := mk'_len _ _ _ _

theorem hpRatio_len {t : IntTy} (a b c d : JInt t) (nb : Int) (len off : I64) :
    LenIs len (hpRatio a b c d nb len off) := by
  intro r h
  unfold hpRatio at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first | exact mk'_len _ _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem linspace1_len (a b : F64) (len : I64) : LenIs len (linspace1 a b len) := by
  intro r h
  unfold linspace1 at h
  repeat' split at h
  all_goals first | exact mk'_len _ _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem floatrange_len (a s len den : I64) : LenIs len (floatrange a s len den) := by
  intro r h
  unfold floatrange at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first | exact hpRatio_len _ _ _ _ _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem linspaceRat_len (a b len den : I64) : LenIs len (linspaceRat a b len den) := by
  intro r h
  unfold linspaceRat at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first | exact hpRatio_len _ _ _ _ _ _ _ r h | exact linspace1_len _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem linspaceFloat_len (a b : F64) (len : I64) : LenIs len (linspaceFloat a b len) := by
  intro r h
  unfold linspaceFloat at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | exact hpFloat_len _ _ _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem rangeStartStopLength_len (a b : F64) (len : I64) :
    LenIs len (rangeStartStopLength a b len) := by
  intro r h
  unfold rangeStartStopLength at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first | exact hpFloat_len _ _ _ _ _ r h | exact linspace1_len _ _ _ r h | exact linspaceRat_len _ _ _ _ r h | exact linspaceFloat_len _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem rangeStartStepLength_len (a s : F64) (len : I64) :
    LenIs len (rangeStartStepLength a s len) := by
  intro r h
  unfold rangeStartStepLength at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first | exact hpFloat_len _ _ _ _ _ r h | exact floatrange_len _ _ _ _ r h | (simp only [reduceCtorEq] at h)

theorem rangeStepStopLength_len (s b : F64) (len : I64) :
    LenIs len (rangeStepStopLength s b len) := by
  intro r h
  simp only [rangeStepStopLength, SRL.reverse, bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i q hq
    rw [mk'_len _ _ _ _ r h]
    exact rangeStartStepLength_len _ _ _ q hq

theorem lin_len (a b : F64) (len : I64) : ∀ r, Lin.mk' a b len = .ok r → r.len = len := by
  intro r h
  simp only [Lin.mk'] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | (simp only [reduceCtorEq] at h)

/-- `length(range(a, b; length=n)) == n`, `length(range(a; step=s, length=n)) == n`,
`length(range(; stop=b, step=s, length=n)) == n` and `length(LinRange(a, b, n)) == n`
whenever Julia returns a range. -/
def RangeLength : Prop := ∀ (a b : F64) (n : I64),
  LenIs n (rangeStartStopLength a b n) ∧ LenIs n (rangeStartStepLength a b n) ∧
  LenIs n (rangeStepStopLength a b n) ∧ ∀ r, Lin.mk' a b n = .ok r → r.len = n

theorem rangeLength : RangeLength := fun a b n =>
  ⟨rangeStartStopLength_len a b n, rangeStartStepLength_len a b n,
    rangeStepStopLength_len a b n, lin_len a b n⟩

/-! ## Refuted properties -/

/-- `range(a, b; length=n)` returns a range for finite endpoints and `n ≥ 2`. -/
def LinspaceSucceeds : Prop := ∀ (a b : F64) (n : I64),
  F64.isfinite a = true → F64.isfinite b = true → 2 ≤ n.val →
  succeeds (rangeStartStopLength a b n)

theorem linspaceSucceeds_refuted : ¬ LinspaceSucceeds := fun h =>
  absurd (h (dec (10^15)) (dec (10^15 + 1)) (i64 10000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `first(range(a, b; length=n)) == a` and `last(range(a, b; length=n)) == b`. -/
def LinspaceEndpoints : Prop := ∀ (a b : F64) (n : I64),
  F64.isfinite a = true → F64.isfinite b = true → 2 ≤ n.val →
  okThen (rangeStartStopLength a b n) (fun r => F64.eq r.first a = true ∧ F64.eq r.last b = true)

theorem linspaceEndpoints_refuted : ¬ LinspaceEndpoints := fun h =>
  absurd (h F64.one (dec 1 (10^14)) (i64 24)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- A nonempty `a:s:b` starts at `a`, for finite endpoints and a nonzero step. -/
def ColonFirst : Prop := ∀ a s b : F64,
  F64.isfinite a = true → F64.isfinite b = true → F64.isnan s = false → F64.iszero s = false →
  okThen (colon a s b) (fun r => 1 ≤ r.len.val → F64.eq r.first a = true)

theorem colonFirst_refuted : ¬ ColonFirst := fun h =>
  absurd (h fzero (F64.inf false) F64.one
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

/-- `a:s:b` is empty when `b < a` and `s > 0` (finite inputs). -/
def ColonEmpty : Prop := ∀ a s b : F64,
  F64.isfinite a = true → F64.isfinite s = true → F64.isfinite b = true →
  F64.lt fzero s = true → F64.lt b a = true →
  okThen (colon a s b) (fun r => r.len.val = 0)

theorem colonEmpty_refuted : ¬ ColonEmpty := fun h =>
  absurd (h (dec 1 (10^300)) (dec (10^30)) fzero (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- Decimal inputs `an/10^j`, `sn/10^j`, `bn/10^j` (|numerators| ≤ 10^9, `sn > 0`) give
`floor((bn-an)/sn) + 1` elements, the k-th being the decimal `(an + k*sn)/10^j` rounded
once, as for `0.0:0.1:0.3`. -/
def ColonDecimal : Prop := ∀ (an sn bn : Int) (j : Nat), j ≤ 4 → 0 < sn →
  an.natAbs ≤ 10^9 → sn.natAbs ≤ 10^9 → bn.natAbs ≤ 10^9 →
  okThen (colon (dec an (10^j)) (dec sn (10^j)) (dec bn (10^j))) (fun r =>
    r.len.val = max 0 ((bn - an) / sn + 1) ∧
    ∀ k : Nat, (k : Int) < r.len.val → r.get (i64 (k + 1)) = .ok (dec (an + k * sn) (10^j)))

/-- `0.0:0.1:16777217.0`, as the model constructs it. -/
def decimalThresholdRange : SRL :=
  ⟨⟨F64.ofBits 0, F64.ofBits 0⟩, ⟨F64.ofBits 0x3fb999999999999a, F64.ofBits 0⟩,
    i64 167772171, i64 1⟩

theorem colonDecimal_refuted : ¬ ColonDecimal := by
  intro h
  have hc : colon (dec 0 (10^1)) (dec 1 (10^1)) (dec 167772170 (10^1)) =
      .ok decimalThresholdRange := by decide +kernel
  have hh := h 0 1 167772170 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hc] at hh
  exact absurd (hh.2 3 (by decide +kernel)) (by decide +kernel)

/-- No element of `a:s:b` lies beyond `b` for finite inputs and `s > 0`. -/
def ColonStopBound : Prop := ∀ a s b : F64,
  F64.isfinite a = true → F64.isfinite s = true → F64.isfinite b = true →
  F64.lt fzero s = true →
  okThen (colon a s b) (fun r => 1 ≤ r.len.val → F64.le r.last b = true)

theorem colonStopBound_refuted : ¬ ColonStopBound := fun h =>
  absurd (h (dec 1131 10000) (dec 252 10000) (dec (10^15)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `x in range(a, b; length=n)` returns a Bool for every `x`. -/
def InRangeSucceeds : Prop := ∀ (a b : F64) (n : I64) (x : F64),
  F64.isfinite a = true → F64.isfinite b = true → 2 ≤ n.val →
  okThen (rangeStartStopLength a b n) (fun r => succeeds (r.contains x))

theorem inRangeSucceeds_refuted : ¬ InRangeSucceeds := fun h =>
  absurd (h (dec (-(10^308))) (dec (10^308)) (i64 3) (dec (10^308))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- Every element of a LinRange with finite endpoints is `in` it. -/
def LinContainsElements : Prop := ∀ (a b : F64) (n i : I64),
  F64.isfinite a = true → F64.isfinite b = true →
  okThen (Lin.mk' a b n) (fun r => 1 ≤ i.val → i.val ≤ r.len.val →
    r.contains (r.unsafeGet i) = .ok true)

theorem linContainsElements_refuted : ¬ LinContainsElements := fun h =>
  absurd (h (dec (-(10^308))) (dec (10^308)) (i64 3) (i64 2)
    (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- Elements of `LinRange(a, b, n)` with `a ≤ b` lie in `[a, b]`. -/
def LinBounded : Prop := ∀ (a b : F64) (n i : I64),
  F64.isfinite a = true → F64.isfinite b = true → F64.le a b = true →
  okThen (Lin.mk' a b n) (fun r => 1 ≤ i.val → i.val ≤ r.len.val →
    F64.le a (r.unsafeGet i) = true ∧ F64.le (r.unsafeGet i) b = true)

theorem linBounded_refuted : ¬ LinBounded := fun h =>
  absurd (h (dec 1 10) (dec 1 10) (i64 6) (i64 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `reverse(r)[i] === r[n+1-i]` for a LinRange. -/
def LinReverse : Prop := ∀ (a b : F64) (n i : I64),
  okThen (Lin.mk' a b n) (fun r => okThen r.reverse (fun q => 1 ≤ i.val → i.val ≤ r.len.val →
    F64.isequal (q.unsafeGet i) (r.unsafeGet (r.len - i + i64 1)) = true))

theorem linReverse_refuted : ¬ LinReverse := fun h =>
  absurd (h fzero F64.one (i64 4) (i64 2)) (by decide +kernel)

/-- `LinRange(a, b, n)` is nondecreasing when `a < b`. -/
def LinMonotone : Prop := ∀ (a b : F64) (n i : I64),
  F64.isfinite a = true → F64.isfinite b = true → F64.lt a b = true →
  okThen (Lin.mk' a b n) (fun r => 1 ≤ i.val → i.val < r.len.val →
    F64.le (r.unsafeGet i) (r.unsafeGet (i + i64 1)) = true)

theorem linMonotone_refuted : ¬ LinMonotone := fun h =>
  absurd (h (dec 621443 10000) (dec 6214430000000095 (10^14)) (i64 283) (i64 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- No element of `range(a; step=s, length=n)` is NaN for finite `a` and `s`. -/
def StartStepNoNaN : Prop := ∀ (a s : F64) (n i : I64),
  F64.isfinite a = true → F64.isfinite s = true →
  okThen (rangeStartStepLength a s n) (fun r => 1 ≤ i.val → i.val ≤ r.len.val →
    F64.isnan (r.unsafeGet i) = false)

theorem startStepNoNaN_refuted : ¬ StartStepNoNaN := fun h =>
  absurd (h F64.one (dec (10^308)) (i64 3) (i64 3) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

/-- `isequal(first(a:s:b), a)` for a nonempty range with finite inputs. -/
def ColonFirstIdentical : Prop := ∀ a s b : F64,
  F64.isfinite a = true → F64.isfinite s = true → F64.isfinite b = true →
  F64.iszero s = false →
  okThen (colon a s b) (fun r => 1 ≤ r.len.val → F64.isequal r.first a = true)

theorem colonFirstIdentical_refuted : ¬ ColonFirstIdentical := fun h =>
  absurd (h (F64.zero true) F64.one (dec 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- `r[1] == first(r)` and `r[end] == last(r)` for a LinRange with non-NaN endpoints. -/
def LinIndexEndpoints : Prop := ∀ (a b : F64) (n : I64),
  F64.isnan a = false → F64.isnan b = false →
  okThen (Lin.mk' a b n) (fun r => 1 ≤ r.len.val →
    (r.get (i64 1)).map (fun x => F64.eq x r.first) = .ok true ∧
    (r.get r.len).map (fun x => F64.eq x r.last) = .ok true)

theorem linIndexEndpoints_refuted : ¬ LinIndexEndpoints := fun h =>
  absurd (h fzero (F64.inf false) (i64 3) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

/-- `x * r` and `x .* r` have identical elements (`*(::Number, ::AbstractArray)` is
broadcasting, `base/arraymath.jl:54`). -/
def ScalarMulBroadcast : Prop := ∀ (a s b x : F64) (i : I64),
  okThen (colon a s b) (fun r => okThen (SRL.scalarMul x r) (fun p =>
    okThen (r.bcastMul x) (fun q => 1 ≤ i.val → i.val ≤ r.len.val →
      F64.isequal (p.unsafeGet i) (q.unsafeGet i) = true)))

theorem scalarMulBroadcast_refuted : ¬ ScalarMulBroadcast := fun h =>
  absurd (h fzero (dec 1 10) (dec 3 10) (dec 3) (i64 4)) (by decide +kernel)

/-- The call throws `ArgumentError`. -/
def throwsArgumentError {α : Type} (x : Jl α) : Prop :=
  match x with
  | .error (.argumentError _) => True
  | _ => False

instance {α : Type} (x : Jl α) : Decidable (throwsArgumentError x) := by
  unfold throwsArgumentError; split <;> infer_instance

/-- `a:s:b` with a nonfinite endpoint throws `ArgumentError`, as `range(a, b; length)` does
(`base/twiceprecision.jl:672`). -/
def ColonNonfiniteArgument : Prop := ∀ a s b : F64,
  F64.isfinite s = true → F64.iszero s = false →
  (F64.isfinite a = false ∨ F64.isfinite b = false) → throwsArgumentError (colon a s b)

theorem colonNonfiniteArgument_refuted : ¬ ColonNonfiniteArgument := fun h =>
  absurd (h fzero F64.one (F64.inf false) (by decide +kernel) (by decide +kernel)
    (Or.inr (by decide +kernel))) (by decide +kernel)

/-- `hi + lo == i` exactly, with both words finite. -/
def exactSplit (x : Jl (F64 × F64)) (i : I64) : Prop :=
  match x with
  | .ok (hi, lo) =>
    let a := F64.toRat hi
    let b := F64.toRat lo
    0 < a.2 ∧ 0 < b.2 ∧ a.1 * b.2 + b.1 * a.2 = i.val * a.2 * b.2
  | .error _ => False

instance (x : Jl (F64 × F64)) (i : I64) : Decidable (exactSplit x i) := by
  unfold exactSplit; split <;> infer_instance

/-- `splitprec(Float64, i)` is exact for every Int64 (`base/twiceprecision.jl:18-20`). -/
def SplitprecExact : Prop := ∀ i : I64, exactSplit (TP.splitprec i) i

theorem splitprecExact_refuted : ¬ SplitprecExact := fun h =>
  absurd (h (JInt.typemax .i64)) (by decide +kernel)

open JuliaLean.Registry

def propertyEntries : List Entry := []

end JuliaLean.FloatRanges
