import JuliaLean.Core
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

/-- base/checked.jl:136-137,200-201,239-240: checked LLVM arithmetic
intrinsics return a wrapping result and the exact overflow flag. -/
def intrinsicResult {t : IntTy} (x : Int) : JInt t × Bool :=
  (JInt.wrap t x, decide (¬ (t.min ≤ x ∧ x ≤ t.max)))

/-- base/checked.jl:135-137. BrokenSignedInt/BrokenUnsignedInt are empty. -/
def addWithOverflow {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  intrinsicResult (x.val + y.val)

/-- base/checked.jl:199-201. BrokenSignedInt/BrokenUnsignedInt are empty. -/
def subWithOverflow {t : IntTy} (x y : JInt t) : JInt t × Bool :=
  intrinsicResult (x.val - y.val)

/-- base/checked.jl:238-280: Int128/UInt128 use manual division thresholds,
including the y == -1 short circuit before fld(typemin, y). Other widths use
LLVM checked multiplication. Jl retains exceptions of intermediate divisions. -/
def mulWithOverflow {t : IntTy} (x y : JInt t) : Jl (JInt t × Bool) := do
  if t = .i128 then
    let f ← if y.val > 0 then do
      let hi ← JInt.fld (JInt.typemax t) y
      if x > hi then pure true else do
        let lo ← JInt.cld (JInt.typemin t) y
        pure (decide (x < lo))
    else if y.val < 0 then do
      let hi ← JInt.cld (JInt.typemax t) y
      if x < hi then pure true
      else if y.val ≠ -1 then do
        let lo ← JInt.fld (JInt.typemin t) y
        pure (decide (x > lo))
      else pure false
    else pure false
    pure (x * y, f)
  else if t = .u128 then
    let f ← if y.val > 0 then do
      let hi ← JInt.fld (JInt.typemax t) y
      pure (decide (x > hi))
    else pure false
    pure (x * y, f)
  else pure (intrinsicResult (x.val * y.val))

/-- base/checked.jl:166-175: getfield extracts the intrinsic result/flag. -/
def checkedAdd {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  let zb := addWithOverflow x y
  if zb.2 then .error (.overflowError "") else .ok zb.1

/-- base/checked.jl:226-231. -/
def checkedSub {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  let zb := subWithOverflow x y
  if zb.2 then .error (.overflowError "") else .ok zb.1

/-- base/checked.jl:290-295, including manual multiplication exceptions. -/
def checkedMul {t : IntTy} (x y : JInt t) : Jl (JInt t) := do
  let zb ← mulWithOverflow x y
  if zb.2 then .error (.overflowError "") else .ok zb.1

/-- base/checked.jl:89-91: active generic negation delegates to checked_sub. -/
def checkedNeg {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  checkedSub (JInt.lit t 0) x

/-- base/checked.jl:121-128: signed ifelse computes wrapping -x, then
rejects a negative result; unsigned abs is the identity. -/
def checkedAbs {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  if t.signed then
    let r := if x.val < 0 then -x else x
    if r.val < 0 then .error (.overflowError "") else .ok r
  else .ok x

/-- base/checked.jl:319: division overflow intentionally throws DivideError. -/
def checkedDiv {t : IntTy} (x y : JInt t) : Jl (JInt t) := JInt.div x y
/-- base/checked.jl:328: signed typemin % -1 returns zero, without overflow. -/
def checkedRem {t : IntTy} (x y : JInt t) : Jl (JInt t) := JInt.remInt x y
/-- base/checked.jl:337. -/
def checkedFld {t : IntTy} (x y : JInt t) : Jl (JInt t) := JInt.fld x y
/-- base/checked.jl:346. -/
def checkedMod {t : IntTy} (x y : JInt t) : Jl (JInt t) := JInt.mod x y
/-- base/checked.jl:355. -/
def checkedCld {t : IntTy} (x y : JInt t) : Jl (JInt t) := JInt.cld x y

/-- base/checked.jl:26-33: promote converts x first, then y, before invoking
any checked operation; an inexact conversion takes priority over its errors. -/
def promoted (op : {t : IntTy} → JInt t → JInt t → Jl (JInt t))
    {t s : IntTy} (x : JInt t) (y : JInt s) : Jl (JInt (t.promote s)) := do
  let a ← JInt.convert (t.promote s) x.val
  let b ← JInt.convert (t.promote s) y.val
  op a b

/-- base/checked.jl:26. -/
def checkedAddMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedAdd x y
/-- base/checked.jl:27. -/
def checkedSubMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedSub x y
/-- base/checked.jl:28. -/
def checkedMulMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedMul x y
/-- base/checked.jl:29. -/
def checkedDivMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedDiv x y
/-- base/checked.jl:30. -/
def checkedRemMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedRem x y
/-- base/checked.jl:31. -/
def checkedFldMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedFld x y
/-- base/checked.jl:32. -/
def checkedModMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedMod x y
/-- base/checked.jl:33. -/
def checkedCldMixed {t s : IntTy} (x : JInt t) (y : JInt s) := promoted @checkedCld x y

/-- base/intfuncs.jl:423,435: trailing_zeros(p), counted up to the operand width.
This helper is used only on the strictly positive exponent branches. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then 1 + trailingZeros fuel (n / 2) else 0

/-- base/intfuncs.jl:430-431,437-438: repeat checked squaring in source order. -/
def squareTimes {t : IntTy} : Nat → JInt t → Jl (JInt t)
  | 0, x => .ok x
  | n + 1, x => do squareTimes n (← checkedMul x x)

/-- base/intfuncs.jl:434-441: each iteration removes trailing zeros and one
set bit, then squares before multiplying the accumulator. -/
def powerLoop {t : IntTy} (width : Nat) (p : Nat) (x y : JInt t) : Jl (JInt t) :=
  match p with
  | 0 => .ok y
  | n + 1 => do
    let z := trailingZeros width (n + 1)
    let x ← squareTimes (z + 1) x
    let y ← checkedMul y x
    powerLoop width ((n + 1) / 2 / 2 ^ z) x y
termination_by p
decreasing_by
  have h := Nat.div_le_self ((n + 1) / 2) (2 ^ trailingZeros width (n + 1))
  have h' := Nat.div_lt_self (by omega : 0 < n + 1) (by omega : 1 < 2)
  omega

/-- base/checked.jl:364-366 and base/intfuncs.jl:399-442. The preliminary
x*x is wrapping and square_is_useful is false for checked_mul. No promotion
with the exponent takes place. The negative-exponent unit test uses wrapping
unary minus, exactly as the source does. -/
def checkedPow {t s : IntTy} (x : JInt t) (p : JInt s) : Jl (JInt t) := do
  let _xSquared := x * x
  if p.val = 1 then pure x
  else if p.val = 0 then pure (JInt.lit t 1)
  else if p.val = 2 then checkedMul x x
  else if p.val < 0 then
    if x.val = 1 then pure x
    else if (-x).val = 1 then
      pure (if p.val % 2 = 0 then JInt.lit t 1 else x)
    else .error (.domainError "")
  else
    let z := trailingZeros s.bits p.val.toNat
    let x ← squareTimes z x
    powerLoop s.bits (p.val.toNat / 2 / 2 ^ z) x x

/-- base/checked.jl:376: the generic fallback returns length(r) unchanged,
including its errors; specialized range checked_length methods are separate. -/
def checkedLength {α β : Type} (length : α → Jl β) (r : α) : Jl β := length r

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


def entries : List JuliaLean.Registry.Entry := [
  { id := "intarith-checked-add-sub-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add", "checked_sub", "add_with_overflow", "sub_with_overflow"],
    statement := "All same-type inputs return the exact mathematical sum/difference or OverflowError precisely when out of range.",
    source := "base/checked.jl:130-137,159-175,194-201,219-231", status := .proven,
    prop := ``AddSubExact, thm := some ``addSubExact,
    notes := "All ten widths. Release uses tuple destructuring in checked_add; master getfield leaves numerical behavior unchanged." },
  { id := "intarith-checked-neg-abs-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_neg", "checked_abs"],
    statement := "For arbitrary input at every width, negation and absolute value return the exact mathematical result or OverflowError precisely when out of range.",
    source := "base/checked.jl:80-128", status := .proven,
    prop := ``NegAbsExact, thm := some ``negAbsExact,
    notes := "Unsigned negation rejects every positive input; unsigned abs is identity. Release and master agree numerically." },
  { id := "intarith-checked-manual-mul-factors", juliaFile := "base/checked.jl",
    juliaFns := ["checked_mul", "mul_with_overflow"],
    statement := "For every Int128/UInt128 input, multiplication by converted -2,-1,0,1,2 returns the exact product or OverflowError precisely when out of range.",
    source := "base/checked.jl:257-280", status := .proven,
    prop := ``ManualSmallFactorsExact, thm := some ``manualSmallFactorsExact,
    notes := "Arbitrary 128-bit first operand. Covers positive, negative, zero, and special -1 thresholds, including unsigned factors modulo UInt128. Release and master agree numerically." },
  { id := "intarith-checked-mul-intrinsic-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_mul", "mul_with_overflow"],
    statement := "All inputs at the eight intrinsic widths return the exact product or OverflowError precisely when out of range.",
    source := "base/checked.jl:233-240,283-295", status := .proven,
    prop := ``IntrinsicMulExact, thm := some ``intrinsicMulExact,
    notes := "Int128 and UInt128 use the source manual thresholds and are covered by arbitrary first operands against five factors plus the boundary property. Release and master agree numerically." },
  { id := "intarith-checked-boundaries", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add", "checked_sub", "checked_mul", "checked_neg", "checked_abs"],
    statement := "Every width detects upper addition/product overflow and lower subtraction/negation/abs overflow; unsigned zero remains zero.",
    source := "base/checked.jl:89-128,166-175,226-280,290-295", status := .proven,
    prop := ``BoundaryArithmetic, thm := some ``boundaryArithmetic,
    notes := "Includes both 128-bit manual multiplication branches. Inactive workaround operators changed to explicit wrapping operators in master; active numeric behavior matches release." },
  { id := "intarith-checked-division-errors", juliaFile := "base/checked.jl",
    juliaFns := ["checked_div", "checked_rem", "checked_fld", "checked_mod", "checked_cld"],
    statement := "Zero division and signed typemin/-1 division throw DivideError, whereas typemin rem/mod -1 equals zero.",
    source := "base/checked.jl:312-355; base/int.jl division primitives", status := .proven,
    prop := ``DivisionBoundaries, thm := some ``divisionBoundaries,
    notes := "DivideError is intentional, inherited from Base.div; the docs promise checking overflow, not the OverflowError class. Release and master agree." },
  { id := "intarith-checked-promotion-order", juliaFile := "base/checked.jl",
    juliaFns := ["checked_div", "promote"],
    statement := "For every signed/unsigned width pair promoted to unsigned, negative input conversion throws InexactError before zero division.",
    source := "base/checked.jl:25-33", status := .proven,
    prop := ``PromotionBeforeOperation, thm := some ``promotionBeforeOperation,
    notes := "Every width pair, including Int128/UInt128. Release and master use identical checked promotion methods." },
  { id := "intarith-checked-negative-pow", juliaFile := "base/checked.jl",
    juliaFns := ["checked_pow", "power_by_squaring"],
    statement := "A successful checked integer power with negative exponent has base +1 or -1.",
    source := "base/intfuncs.jl:388-392,418-421: negative integer power DomainError and unit exceptions", status := .refuted,
    prop := ``NegativePowerUnits, thm := some ``negativePowerUnits_refuted,
    issue := "none found (issues: checked_pow unsigned negative; unsigned negative exponent; power_by_squaring typemax. PRs: power_by_squaring unsigned; checked_pow negative; negative exponent UInt)",
    notes := "UInt8(255) with exponent Int8(-1) returns UInt8(255): wrapping -x equals 1. Master and release both use the wrapping negative-base unit test." }
]

end JuliaLean.IntArith.Checked
