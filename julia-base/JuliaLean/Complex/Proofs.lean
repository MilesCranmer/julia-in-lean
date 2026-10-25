import JuliaLean.Complex.Props

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

theorem neg_neg_f64 (x : F64) : F64.neg (F64.neg x) = x := by
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

theorem conjInvolution_proven : ConjInvolution := by
  intro z
  cases z with
  | mk a b => simp only [CF64.conj, neg_neg_f64]

theorem hashIsequal_proven : HashIsequal := by
  intro H hH hImag h
  constructor
  · intro z w hzw
    simp only [CF64.isequal, Bool.and_eq_true] at hzw
    unfold CF64.hash
    rw [hH z.im w.im hImag hzw.2, hH z.re w.re _ hzw.1]
  · intro z x hzx
    simp only [CF64.isequalReal, Bool.and_eq_true] at hzx
    unfold CF64.hash
    rw [hH z.im Fl.pzero hImag hzx.2, hH z.re x _ hzx.1]
    simp [UInt64.xor_assoc, UInt64.xor_self]

theorem eq_self_of_not_nan (x : F64) (h : F64.isnan x = false) : F64.eq x x = true := by
  simp [F64.eq, h]

theorem isrealDoc_proven : IsrealDoc := by
  intro z
  constructor
  · intro hz
    simp only [CF64.isequalReal, Bool.and_eq_true] at hz
    have h2 := hz.2
    have hn : F64.isnan Fl.pzero = false := by decide
    simp only [F64.isequal, hn, Bool.and_false, Bool.false_or, beq_iff_eq] at h2
    have him : z.im = Fl.pzero := BitVec.eq_of_toNat_eq h2
    simp only [CF64.isreal, him]
    decide
  · intro hn
    simp only [CF64.eqReal, eq_self_of_not_nan z.re hn, Bool.and_true]

theorem falseStrongZero_proven : FalseStrongZero := by
  have key : ∀ y : F64,
      F64.iszero (Fl.mulBool false y) = true ∧ F64.isnan (Fl.mulBool false y) = false := by
    intro y
    simp only [Fl.mulBool, Fl.copysign, Bool.false_eq_true, ↓reduceIte]
    split <;> decide
  intro z
  simp only [CF64.iszero, CF64.isnan, CF64.boolMul, (key z.re).1, (key z.im).1,
    (key z.re).2, (key z.im).2, Bool.and_self, Bool.or_self, and_self]

theorem boolMulPromotes_proven : BoolMulPromotes := by
  constructor
  · intro z w
    cases z with
    | mk a b =>
      cases w with
      | mk c d => cases a <;> cases b <;> cases c <;> cases d <;> decide
  · decide

theorem signbit_copysign (x y : F64) : F64.signbit (Fl.copysign x y) = F64.signbit y := by
  have hy : y.toNat < 2^64 := y.isLt
  have habs : (F64.abs x).toNat < 2^63 := by
    simp only [F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat]; omega
  unfold Fl.copysign F64.signbit F64.toBits F64.ofBits
  by_cases hs : y.toNat ≥ 2^63
  · have h1 : (BitVec.ofNat 64 ((F64.abs x).toNat + 2^63)).toNat ≥ 2^63 := by
      rw [BitVec.toNat_ofNat]; omega
    simp [hs]
    omega
  · have h1 : ¬ (BitVec.ofNat 64 ((F64.abs x).toNat + 0)).toNat ≥ 2^63 := by
      rw [BitVec.toNat_ofNat]; omega
    simp [hs]
    omega

theorem sqrtBranchCut_proven : SqrtBranchCut := by
  intro x y r hx h
  unfold CF64.sqrt at h
  simp only [hx, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h; done)
    | (cases h; exact signbit_copysign _ _)
    | (cases h; rfl)
    | simp_all

theorem abs_neg_f64 (x : F64) : F64.abs (F64.neg x) = F64.abs x := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.abs F64.neg F64.signbit F64.toBits F64.ofBits
  apply BitVec.eq_of_toNat_eq
  by_cases h : x.toNat ≥ 2^63
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega

theorem absConjNeg_proven : AbsConjNeg := by
  intro z
  constructor <;>
    simp only [CF64.abs, CF64.conj, CF64.neg, CF64.hypot, abs_neg_f64]

end JuliaLean.Complex
