import JuliaLean.Promotion.Ints
import JuliaLean.Promotion.Hash
import JuliaLean.Promotion.Rationalize

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-! ## Mixed integer comparison -/

/-- `==`, `<`, `<=` between any two `BitInteger` types compare the mathematical values. -/
def IntCompareExact : Prop := ∀ (t s : IntTy) (x : JInt t) (y : JInt s),
  intCmp .eq x y = decide (x.val = y.val) ∧ intCmp .lt x y = decide (x.val < y.val) ∧
  intCmp .le x y = decide (x.val ≤ y.val)

theorem promote_range (t s : IntTy) (h : t.signed = s.signed) :
    (t.promote s).min ≤ t.min ∧ t.max ≤ (t.promote s).max ∧
    (t.promote s).min ≤ s.min ∧ s.max ≤ (t.promote s).max := by
  cases t <;> cases s <;> revert h <;> decide

theorem unsignedSigned_exact (op : Op) (u v : IntTy) (hu : u.signed = false) (hv : v.signed = true)
    (x : JInt u) (y : JInt v) : intCmp.unsignedSigned op x y = op.int x.val y.val := by
  have hx := x.property
  have hy := y.property
  unfold intCmp.unsignedSigned
  by_cases hlt : u.bits < v.bits
  · have hb : v.min ≤ u.min ∧ u.max ≤ v.max := by
      revert hlt hu hv; cases u <;> cases v <;> decide
    rw [if_pos hlt]
    have e : (JInt.wrap v x.val).val = x.val := wrapInt_of_inRange v x.val ⟨by omega, by omega⟩
    rw [e]
  · have hb : u.min = 0 ∧ v.toUnsigned.min = 0 ∧ v.max ≤ v.toUnsigned.max ∧ v.max ≤ u.max := by
      revert hlt hu hv; cases u <;> cases v <;> decide
    rw [if_neg hlt]
    by_cases hy0 : 0 ≤ y.val
    · have e1 : (JInt.wrap v.toUnsigned y.val).val = y.val :=
        wrapInt_of_inRange _ _ ⟨by omega, by omega⟩
      have e2 : (JInt.wrap u (JInt.wrap v.toUnsigned y.val).val).val = y.val := by
        rw [e1]; exact wrapInt_of_inRange _ _ ⟨by omega, by omega⟩
      rw [e2]
      simp [hy0]
    · have hx0 : 0 ≤ x.val := by omega
      cases op <;> simp [Op.int, hy0] <;> omega

theorem intCompareExact_proven : IntCompareExact := by
  intro t s x y
  unfold intCmp
  by_cases hs : t.signed = s.signed
  · have hr := promote_range t s hs
    have hx := x.property
    have hy := y.property
    have ex : (JInt.wrap (t.promote s) x.val).val = x.val :=
      wrapInt_of_inRange _ _ ⟨by omega, by omega⟩
    have ey : (JInt.wrap (t.promote s) y.val).val = y.val :=
      wrapInt_of_inRange _ _ ⟨by omega, by omega⟩
    simp only [if_pos hs, ex, ey, Op.int]
    exact ⟨trivial, trivial, trivial⟩
  · simp only [if_neg hs]
    cases ht : t.signed
    · have hs' : s.signed = true := by cases h : s.signed <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      refine ⟨?_, ?_, ?_⟩ <;> rw [unsignedSigned_exact _ t s ht hs' x y] <;> rfl
    · have hs' : s.signed = false := by cases h : s.signed <;> simp_all
      simp only [if_true]
      refine ⟨?_, ?_, ?_⟩
      · rw [unsignedSigned_exact _ s t hs' ht y x]
        exact decide_eq_decide.mpr eq_comm
      · rw [unsignedSigned_exact _ s t hs' ht y x]
        simp only [Op.int]
        by_cases h : y.val ≤ x.val <;> simp [h] <;> omega
      · rw [unsignedSigned_exact _ s t hs' ht y x]
        simp only [Op.int]
        by_cases h : y.val < x.val <;> simp [h] <;> omega

/-! ## Rational/float comparison -/

/-- `cmp(x::AbstractFloat, y::Rational)` follows the `isless` total order, as the `cmp`
docstring promises. -/
def CmpRationalFloatIsless : Prop := ∀ (T : FTy) (t : IntTy) (x : FV T) (y : Rat t), Normalized y →
  cmpFR x y = (if islessFR x y then -1 else if islessRF y x then 1 else 0)

def negZero64 : FV .f64 := Fl.zero true
def zeroRat64 : Rat .i64 := ⟨JInt.lit .i64 0, JInt.lit .i64 1⟩

theorem cmpRationalFloatIsless_refuted : ¬ CmpRationalFloatIsless := by
  intro h
  have bad := h .f64 .i64 negZero64 zeroRat64 (by decide)
  revert bad
  decide

/-! ## Rational{T}(x::Float64) -/

/-- `Rational{T}(x)` for finite `x` returns only a rational exactly equal to `x`
(otherwise it throws `InexactError`). -/
def RationalOfFloatExact : Prop := ∀ (t : IntTy) (x : F64) (r : Rat t),
  rationalOfF64 t x = .ok r → F64.isfinite x = true →
  r.num.val * ((F64.toRat x).2 : Int) = (F64.toRat x).1 * r.den.val

def pointOne : F64 := F64.ofBits 0x3fb999999999999a
def oneTenth8 : Rat .i8 := ⟨JInt.lit .i8 1, JInt.lit .i8 10⟩

theorem rationalOfFloatExact_refuted : ¬ RationalOfFloatExact := by
  intro h
  have bad := h .i8 pointOne oneTenth8 (by decide +kernel) (by decide)
  revert bad
  decide

/-- `Rational{T}(x)` succeeds, returning the normalized value, whenever `x` is finite and
exactly equal to a normalized `Rational{T}`. -/
def RationalOfFloatRepresentable : Prop := ∀ (t : IntTy) (x : F64) (r : Rat t),
  Normalized r → 0 < r.den.val → F64.isfinite x = true →
  r.num.val * ((F64.toRat x).2 : Int) = (F64.toRat x).1 * r.den.val →
  rationalOfF64 t x = .ok r

def minus128 : F64 := F64.ofInt (-128)
def minus128Rat : Rat .i8 := ⟨JInt.lit .i8 (-128), JInt.lit .i8 1⟩

theorem rationalOfFloatRepresentable_refuted : ¬ RationalOfFloatRepresentable := by
  intro h
  have bad := h .i8 minus128 minus128Rat (by decide) (by decide) (by decide) (by decide)
  revert bad
  decide +kernel

/-! ## Float64(x::Rational) -/

/-- `Float64(q)` is the binary64 value closest to `q` (ties to even), as `convert` promises. -/
def RationalToFloatNearest : Prop := ∀ (t : IntTy) (q : Rat t), Normalized q → 0 < q.den.val →
  ratToF64 q = F64.roundRat q.num.val q.den.val.toNat false

def ratNearestCex : Rat .i64 := ⟨JInt.lit .i64 9007199254740995, JInt.lit .i64 3⟩

theorem rationalToFloatNearest_refuted : ¬ RationalToFloatNearest := by
  intro h
  have bad := h .i64 ratNearestCex (by decide) (by decide)
  revert bad
  decide

/-! ## trunc(T, x::Rational) for infinite x -/

/-- `trunc(T, x)` throws `InexactError` when the truncated value is not representable,
including the infinite rationals `±1//0`. -/
def TruncInfiniteInexact : Prop := ∀ (target t : IntTy) (x : Rat t), Normalized x →
  x.den.val = 0 → ∃ s, trunc target x = .error (.inexactError s)

def posInf64 : Rat .i64 := ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩

theorem truncInfiniteInexact_refuted : ¬ TruncInfiniteInexact := by
  intro h
  obtain ⟨s, hs⟩ := h .i64 .i64 posInf64 (by decide) (by decide)
  have actual : trunc .i64 posInf64 = .error .divideError := by decide
  rw [actual] at hs
  cases hs

end JuliaLean.Promotion
