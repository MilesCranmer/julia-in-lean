import JuliaLean.base.checked
import JuliaLean.base.intfuncs
import JuliaLean.Registry.Types

/-!
Julia checked integer arithmetic on the 64-bit platform. The active fallback
sets are Int128 and UInt128; the disabled 32-bit-platform and BrokenSignedInt
branches are not methods in this platform's Julia. Overflow message text is
not modelled. All references below are to master bbfa0ce4150.
-/
namespace JuliaLean.IntArith.Checked

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

private theorem neg_val {t : IntTy} (a : JInt t) :
    (-a).val = wrapInt t (-a.val) := rfl
private theorem mul_val {t : IntTy} (a b : JInt t) :
    (a * b).val = wrapInt t (a.val * b.val) := rfl
private theorem sub_val {t : IntTy} (a b : JInt t) :
    (a - b).val = wrapInt t (a.val - b.val) := rfl
private theorem add_val {t : IntTy} (a b : JInt t) :
    (a + b).val = wrapInt t (a.val + b.val) := rfl
private theorem wrap_val (t : IntTy) (v : Int) : (JInt.wrap t v).val = wrapInt t v := rfl
private theorem lit_val (t : IntTy) (v : Int) : (JInt.lit t v).val = wrapInt t v := rfl
private theorem min_val (t : IntTy) : (JInt.typemin t).val = t.min := by cases t <;> decide
private theorem max_val (t : IntTy) : (JInt.typemax t).val = t.max := by cases t <;> decide
private theorem lt_val {t : IntTy} (a b : JInt t) : (a < b) ↔ a.val < b.val := Iff.rfl

/-- Mathematical contract for an exact result or an OverflowError. -/
def ExactOrOverflow {t : IntTy} (r : Jl (JInt t)) (n : Int) : Prop :=
  if t.min ≤ n ∧ n ≤ t.max then ∃ z, r = .ok z ∧ z.val = n
  else r = .error (.overflowError "")

private theorem exact_ok_iff {t : IntTy} (z : JInt t) (n : Int) :
    ExactOrOverflow (.ok z) n ↔ z.val = n := by
  by_cases h : t.min ≤ n ∧ n ≤ t.max
  · simp [ExactOrOverflow, h]
  · unfold ExactOrOverflow
    split
    · contradiction
    · constructor
      · intro he; cases he
      · intro he
        exact False.elim (h (he ▸ z.property))

private theorem exact_error_iff {t : IntTy} (n : Int) :
    ExactOrOverflow (t := t) (.error (.overflowError "")) n ↔
      ¬ (t.min ≤ n ∧ n ≤ t.max) := by
  by_cases h : t.min ≤ n ∧ n ≤ t.max <;> simp [ExactOrOverflow, h]




theorem exact_intrinsic {t : IntTy} (n : Int) :
    ExactOrOverflow (if (intrinsicResult (t := t) n).2 then
      .error (.overflowError "") else .ok (intrinsicResult (t := t) n).1) n := by
  unfold ExactOrOverflow intrinsicResult
  split <;> rename_i h
  · simp [h]
    exact wrapInt_of_inRange t n h
  · simp [h]

/-- All values of all ten widths, with mathematical exact results. -/
def AddSubExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  ExactOrOverflow (checkedAdd x y) (x.val + y.val) ∧
  ExactOrOverflow (checkedSub x y) (x.val - y.val)

theorem addSubExact : AddSubExact := by
  intro t x y
  exact ⟨exact_intrinsic _, exact_intrinsic _⟩

/-- Genuine arbitrary-input multiplication contract for the LLVM widths. -/
def IntrinsicMulExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  t ≠ .i128 → t ≠ .u128 →
  ExactOrOverflow (checkedMul x y) (x.val * y.val)

theorem intrinsicMulExact : IntrinsicMulExact := by
  intro t x y hi hu
  simpa [checkedMul, mulWithOverflow, hi, hu] using
    (exact_intrinsic (t := t) (x.val * y.val))

/-- Arbitrary input negation at every width, including unsigned underflow. -/
def NegExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ExactOrOverflow (checkedNeg x) (-x.val)

theorem negExact : NegExact := by
  intro t x
  have hz : (JInt.lit t 0).val = 0 := by cases t <;> decide
  simpa [checkedNeg, checkedSub, subWithOverflow, hz] using
    (exact_intrinsic (t := t) (-x.val))

/-- Absolute value's exact mathematical result, for arbitrary inputs. -/
def AbsExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ExactOrOverflow (checkedAbs x) (if x.val < 0 then -x.val else x.val)

theorem absExact : AbsExact := by
  intro t x
  have hb := x.property
  cases t <;>
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb <;>
    simp only [checkedAbs, IntTy.signed, Bool.false_eq_true, ite_false, ite_true]
    <;> (repeat' first | split | simp_all only [exact_ok_iff, exact_error_iff,
      neg_val, wrapInt, IntTy.min, IntTy.max, IntTy.signed,
      IntTy.bits, ite_true])
    <;> simp_all <;> omega

def NegAbsExact : Prop := NegExact ∧ AbsExact

theorem negAbsExact : NegAbsExact := ⟨negExact, absExact⟩

/-- Every input of either manual 128-bit fallback against small signed
factors, covering the zero, positive, negative, and special -1 branches. -/
def ManualSmallFactorsExact : Prop := ∀ (t : IntTy) (x : JInt t) (k : Int),
  (t = .i128 ∨ t = .u128) →
  (k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) →
  ExactOrOverflow (checkedMul x (JInt.lit t k))
    (x.val * (JInt.lit t k).val)

set_option maxHeartbeats 800000 in
theorem manualSmallFactorsExact : ManualSmallFactorsExact := by
  intro t x k ht hk
  have hb := x.property
  rcases ht with rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb <;>
    simp only [checkedMul, mulWithOverflow, JInt.fld, JInt.cld, JInt.div] <;>
    (repeat' first | simp_all [exact_ok_iff, exact_error_iff,
      min_val, max_val, lit_val, wrap_val, lt_val, mul_val, sub_val, add_val,
      Bind.bind, Pure.pure, Except.bind, Except.pure,
      wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] | split at *)
    <;> subst_vars
    <;> (try simp_all [mul_val, lit_val, wrapInt, IntTy.min, IntTy.max,
      IntTy.signed, IntTy.bits]) <;> omega

/-- Checked negative powers can succeed only for the mathematical units ±1. -/
def NegativePowerUnits : Prop := ∀ (t s : IntTy) (x : JInt t) (p : JInt s),
  p.val < 0 → (∃ z, checkedPow x p = .ok z) → x.val = 1 ∨ x.val = -1

theorem negativePowerUnits_refuted : ¬ NegativePowerUnits := by
  intro h
  have bad := h .u8 .i8 (JInt.lit .u8 255) (JInt.lit .i8 (-1))
  have hp : (JInt.lit .i8 (-1)).val < 0 := by decide
  have hz : ∃ z, checkedPow (JInt.lit .u8 255) (JInt.lit .i8 (-1)) = .ok z := by
    exact ⟨JInt.lit .u8 255, by decide⟩
  have hf := bad hp hz
  have hn : ¬ ((JInt.lit .u8 255).val = 1 ∨ (JInt.lit .u8 255).val = -1) := by decide
  exact hn hf

/-- All widths, including Int128/UInt128 manual fallback thresholds. -/
def BoundaryArithmetic : Prop := ∀ t : IntTy,
  checkedAdd (JInt.typemax t) (JInt.lit t 1) = .error (.overflowError "") ∧
  checkedSub (JInt.typemin t) (JInt.lit t 1) = .error (.overflowError "") ∧
  checkedMul (JInt.typemax t) (JInt.lit t 2) = .error (.overflowError "") ∧
  checkedMul (JInt.typemin t) (JInt.lit t (-1)) =
    (if t.signed then .error (.overflowError "") else .ok (JInt.lit t 0)) ∧
  checkedNeg (JInt.typemin t) =
    (if t.signed then .error (.overflowError "") else .ok (JInt.lit t 0)) ∧
  checkedAbs (JInt.typemin t) =
    (if t.signed then .error (.overflowError "") else .ok (JInt.lit t 0))

theorem boundaryArithmetic : BoundaryArithmetic := by
  intro t
  cases t <;> decide

/-- Division overflow uses DivideError; remainders do not overflow. -/
def DivisionBoundaries : Prop := ∀ t : IntTy,
  checkedDiv (JInt.lit t 0) (JInt.lit t 0) = .error .divideError ∧
  (t.signed = true →
    checkedDiv (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedFld (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedCld (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedRem (JInt.typemin t) (JInt.lit t (-1)) = .ok (JInt.lit t 0) ∧
    checkedMod (JInt.typemin t) (JInt.lit t (-1)) = .ok (JInt.lit t 0))

theorem divisionBoundaries : DivisionBoundaries := by
  intro t
  cases t <;> decide

/-- Mixed signedness of every width pair converts before zero division. -/
def PromotionBeforeOperation : Prop := ∀ (t s : IntTy),
  t.signed = true → s.signed = false → (t.promote s).signed = false →
  checkedDivMixed (JInt.lit t (-1)) (JInt.lit s 0) =
    .error (.inexactError (t.promote s).name)

theorem promotionBeforeOperation : PromotionBeforeOperation := by
  intro t s
  cases t <;> cases s <;> decide


def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.Checked
