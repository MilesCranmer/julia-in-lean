import JuliaLean.Registry.Types
import JuliaLean.base.boot
import JuliaLean.base.essentials
import JuliaLean.base.expr


section

/-!
Properties of the Core integer conversions (`base/boot.jl:1032-1221`).
-/

namespace JuliaLean.BootCov.IntConv

open JuliaLean
open JuliaLean.BootCov

/-- The value a conversion returns, or `none` when it throws. -/
def resultVal {t : IntTy} : R (JInt t) → Option Int
  | .ok y => some y.val
  | .error _ => none

/-- Whether a conversion threw `InexactError` for target type `To`. -/
def throwsInexactFor {t : IntTy} (To : IntTy) : R (JInt t) → Prop
  | .ok _ => True
  | .error e => ∃ f, e = .inexact f To.name

/-- `do let x ← check_sign_bit(To, x); k(x)`. -/
theorem bind_checkSignBit {β : Type} (To t : IntTy) (x : JInt t) (k : JInt t → R β) :
    (checkSignBit To x >>= k) =
      if wrapInt t.toSigned x.val < 0 then
        throwInexact (if t.bits = To.bits then "convert" else "trunc") To
      else k x := by
  unfold checkSignBit
  split <;> rfl

theorem resultVal_ite {t : IntTy} (c : Prop) [Decidable c] (a b : R (JInt t)) :
    resultVal (if c then a else b) = if c then resultVal a else resultVal b := by
  split <;> rfl
theorem resultVal_ok {t : IntTy} (y : JInt t) : resultVal (.ok y) = some y.val := rfl
theorem resultVal_error {t : IntTy} (e : Exc) : resultVal (.error e : R (JInt t)) = none := rfl
theorem throws_ite {t : IntTy} (To : IntTy) (c : Prop) [Decidable c] (a b : R (JInt t)) :
    throwsInexactFor To (if c then a else b) =
      if c then throwsInexactFor To a else throwsInexactFor To b := by
  split <;> rfl
theorem throws_ok {t : IntTy} (To : IntTy) (y : JInt t) : throwsInexactFor To (.ok y) = True := rfl
theorem throws_error {t : IntTy} (To : IntTy) (f n : String) :
    throwsInexactFor To (.error (.inexact f n) : R (JInt t)) = ∃ g, Exc.inexact f n = .inexact g To.name := rfl

/-! Concrete forms of `wrapInt`, `typemin` and `typemax` for each width. -/
theorem wrap_i8 (x : Int) : wrapInt .i8 x = (x + 128) % 256 - 128 := rfl
theorem min_i8 : IntTy.min .i8 = -128 := rfl
theorem max_i8 : IntTy.max .i8 = 127 := rfl
theorem wrap_i16 (x : Int) : wrapInt .i16 x = (x + 32768) % 65536 - 32768 := rfl
theorem min_i16 : IntTy.min .i16 = -32768 := rfl
theorem max_i16 : IntTy.max .i16 = 32767 := rfl
theorem wrap_i32 (x : Int) : wrapInt .i32 x = (x + 2147483648) % 4294967296 - 2147483648 := rfl
theorem min_i32 : IntTy.min .i32 = -2147483648 := rfl
theorem max_i32 : IntTy.max .i32 = 2147483647 := rfl
theorem wrap_i64 (x : Int) : wrapInt .i64 x = (x + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := rfl
theorem min_i64 : IntTy.min .i64 = -9223372036854775808 := rfl
theorem max_i64 : IntTy.max .i64 = 9223372036854775807 := rfl
theorem wrap_i128 (x : Int) : wrapInt .i128 x = (x + 170141183460469231731687303715884105728) % 340282366920938463463374607431768211456 - 170141183460469231731687303715884105728 := rfl
theorem min_i128 : IntTy.min .i128 = -170141183460469231731687303715884105728 := rfl
theorem max_i128 : IntTy.max .i128 = 170141183460469231731687303715884105727 := rfl
theorem wrap_u8 (x : Int) : wrapInt .u8 x = x % 256 := rfl
theorem min_u8 : IntTy.min .u8 = 0 := rfl
theorem max_u8 : IntTy.max .u8 = 255 := rfl
theorem wrap_u16 (x : Int) : wrapInt .u16 x = x % 65536 := rfl
theorem min_u16 : IntTy.min .u16 = 0 := rfl
theorem max_u16 : IntTy.max .u16 = 65535 := rfl
theorem wrap_u32 (x : Int) : wrapInt .u32 x = x % 4294967296 := rfl
theorem min_u32 : IntTy.min .u32 = 0 := rfl
theorem max_u32 : IntTy.max .u32 = 4294967295 := rfl
theorem wrap_u64 (x : Int) : wrapInt .u64 x = x % 18446744073709551616 := rfl
theorem min_u64 : IntTy.min .u64 = 0 := rfl
theorem max_u64 : IntTy.max .u64 = 18446744073709551615 := rfl
theorem wrap_u128 (x : Int) : wrapInt .u128 x = x % 340282366920938463463374607431768211456 := rfl
theorem min_u128 : IntTy.min .u128 = 0 := rfl
theorem max_u128 : IntTy.max .u128 = 340282366920938463463374607431768211455 := rfl

/-- Unfold one conversion on concrete widths and close it by integer arithmetic. -/
macro "conv_solve" : tactic => `(tactic| (
  simp only [ctor, toInt8, toInt16, toInt32, toInt64, toInt128, toUInt8, toUInt16, toUInt32,
    toUInt64, toUInt128, bind_checkSignBit, checkedTruncSint, checkedTruncUint, throwInexact,
    boolTo, pure, Except.pure]
  try simp only [resultVal_ite, resultVal_ok, resultVal_error, throws_ite, throws_ok, throws_error]
  repeat' split
  all_goals (try simp only [truncInt, sextInt, zextInt, bitcastInt, JInt.wrap,
    BuiltinInt.value, IntTy.toSigned, IntTy.toUnsigned, IntTy.name, resultVal_ok, resultVal_error,
    throws_ok, throws_error,
    wrap_i8, min_i8, max_i8, wrap_i16, min_i16, max_i16, wrap_i32, min_i32, max_i32, wrap_i64, min_i64, max_i64, wrap_i128, min_i128, max_i128, wrap_u8, min_u8, max_u8, wrap_u16, min_u16, max_u16, wrap_u32, min_u32, max_u32, wrap_u64, min_u64, max_u64, wrap_u128, min_u128, max_u128,
    decide_eq_true_eq, Bool.false_eq_true, eq_self_iff_true, Option.some.injEq, reduceCtorEq] at *)
  all_goals first
    | rfl
    | trivial
    | exact ⟨_, rfl⟩
    | omega))

/-- Every Core integer constructor `T(x)` (`base/boot.jl:1184-1193`, through the
`toT` tables at lines 1071-1180) is exact conversion: it returns `x` itself when
`x` is representable in `T`, and otherwise throws `InexactError` for `T`. -/
def CtorExact : Prop :=
  ∀ (To : IntTy) (x : BuiltinInt),
    resultVal (ctor To x) = (if To.min ≤ x.value ∧ x.value ≤ To.max then some x.value else none) ∧
    throwsInexactFor To (ctor To x)

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .i8 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .i8 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .i8 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .i8 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .i8 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .i8 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .i8 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .i8 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .i8 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i8_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .i8 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.i8.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.i8.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i8 (ctor .i8 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .i16 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .i16 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .i16 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .i16 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .i16 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .i16 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .i16 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .i16 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .i16 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i16_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .i16 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.i16.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.i16.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i16 (ctor .i16 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .i32 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .i32 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .i32 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .i32 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .i32 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .i32 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .i32 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .i32 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .i32 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i32_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .i32 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.i32.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.i32.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i32 (ctor .i32 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .i64 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .i64 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .i64 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .i64 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .i64 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .i64 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .i64 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .i64 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .i64 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i64_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .i64 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.i64.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.i64.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i64 (ctor .i64 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .i128 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .i128 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .i128 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .i128 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .i128 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .i128 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .i128 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .i128 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .i128 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_i128_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .i128 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.i128.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.i128.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .i128 (ctor .i128 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .u8 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .u8 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .u8 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .u8 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .u8 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .u8 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .u8 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .u8 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .u8 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u8_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .u8 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.u8.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.u8.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u8 (ctor .u8 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .u16 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .u16 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .u16 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .u16 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .u16 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .u16 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .u16 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .u16 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .u16 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u16_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .u16 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.u16.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.u16.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u16 (ctor .u16 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .u32 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .u32 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .u32 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .u32 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .u32 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .u32 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .u32 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .u32 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .u32 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u32_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .u32 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.u32.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.u32.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u32 (ctor .u32 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .u64 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .u64 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .u64 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .u64 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .u64 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .u64 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .u64 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .u64 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .u64 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u64_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .u64 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.u64.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.u64.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u64 (ctor .u64 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_i8 (v : Int) (hv : IntTy.i8.min ≤ v ∧ v ≤ IntTy.i8.max) :
    resultVal (ctor .u128 (.int .i8 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .i8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i8 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .i8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .i8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_i16 (v : Int) (hv : IntTy.i16.min ≤ v ∧ v ≤ IntTy.i16.max) :
    resultVal (ctor .u128 (.int .i16 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .i16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i16 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .i16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .i16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_i32 (v : Int) (hv : IntTy.i32.min ≤ v ∧ v ≤ IntTy.i32.max) :
    resultVal (ctor .u128 (.int .i32 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .i32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i32 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .i32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .i32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_i64 (v : Int) (hv : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) :
    resultVal (ctor .u128 (.int .i64 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .i64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i64 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .i64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .i64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_i128 (v : Int) (hv : IntTy.i128.min ≤ v ∧ v ≤ IntTy.i128.max) :
    resultVal (ctor .u128 (.int .i128 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .i128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .i128 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .i128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .i128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_u8 (v : Int) (hv : IntTy.u8.min ≤ v ∧ v ≤ IntTy.u8.max) :
    resultVal (ctor .u128 (.int .u8 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .u8 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u8 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .u8 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .u8 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_u16 (v : Int) (hv : IntTy.u16.min ≤ v ∧ v ≤ IntTy.u16.max) :
    resultVal (ctor .u128 (.int .u16 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .u16 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u16 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .u16 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .u16 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_u32 (v : Int) (hv : IntTy.u32.min ≤ v ∧ v ≤ IntTy.u32.max) :
    resultVal (ctor .u128 (.int .u32 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .u32 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u32 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .u32 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .u32 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_u64 (v : Int) (hv : IntTy.u64.min ≤ v ∧ v ≤ IntTy.u64.max) :
    resultVal (ctor .u128 (.int .u64 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .u64 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u64 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .u64 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .u64 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

set_option maxHeartbeats 1000000 in
theorem ctorExact_u128_u128 (v : Int) (hv : IntTy.u128.min ≤ v ∧ v ≤ IntTy.u128.max) :
    resultVal (ctor .u128 (.int .u128 ⟨v, hv⟩)) =
      (if IntTy.u128.min ≤ (BuiltinInt.int .u128 ⟨v, hv⟩).value ∧
          (BuiltinInt.int .u128 ⟨v, hv⟩).value ≤ IntTy.u128.max
        then some (BuiltinInt.int .u128 ⟨v, hv⟩).value else none) ∧
    throwsInexactFor .u128 (ctor .u128 (.int .u128 ⟨v, hv⟩)) := by
  have h1 := hv.1
  have h2 := hv.2
  constructor <;> conv_solve

theorem ctorExact : CtorExact := by
  intro To x
  rcases x with ⟨t, ⟨v, hv⟩⟩ | b
  · exact match To, t with
    | .i8, .i8 => ctorExact_i8_i8 v hv
    | .i8, .i16 => ctorExact_i8_i16 v hv
    | .i8, .i32 => ctorExact_i8_i32 v hv
    | .i8, .i64 => ctorExact_i8_i64 v hv
    | .i8, .i128 => ctorExact_i8_i128 v hv
    | .i8, .u8 => ctorExact_i8_u8 v hv
    | .i8, .u16 => ctorExact_i8_u16 v hv
    | .i8, .u32 => ctorExact_i8_u32 v hv
    | .i8, .u64 => ctorExact_i8_u64 v hv
    | .i8, .u128 => ctorExact_i8_u128 v hv
    | .i16, .i8 => ctorExact_i16_i8 v hv
    | .i16, .i16 => ctorExact_i16_i16 v hv
    | .i16, .i32 => ctorExact_i16_i32 v hv
    | .i16, .i64 => ctorExact_i16_i64 v hv
    | .i16, .i128 => ctorExact_i16_i128 v hv
    | .i16, .u8 => ctorExact_i16_u8 v hv
    | .i16, .u16 => ctorExact_i16_u16 v hv
    | .i16, .u32 => ctorExact_i16_u32 v hv
    | .i16, .u64 => ctorExact_i16_u64 v hv
    | .i16, .u128 => ctorExact_i16_u128 v hv
    | .i32, .i8 => ctorExact_i32_i8 v hv
    | .i32, .i16 => ctorExact_i32_i16 v hv
    | .i32, .i32 => ctorExact_i32_i32 v hv
    | .i32, .i64 => ctorExact_i32_i64 v hv
    | .i32, .i128 => ctorExact_i32_i128 v hv
    | .i32, .u8 => ctorExact_i32_u8 v hv
    | .i32, .u16 => ctorExact_i32_u16 v hv
    | .i32, .u32 => ctorExact_i32_u32 v hv
    | .i32, .u64 => ctorExact_i32_u64 v hv
    | .i32, .u128 => ctorExact_i32_u128 v hv
    | .i64, .i8 => ctorExact_i64_i8 v hv
    | .i64, .i16 => ctorExact_i64_i16 v hv
    | .i64, .i32 => ctorExact_i64_i32 v hv
    | .i64, .i64 => ctorExact_i64_i64 v hv
    | .i64, .i128 => ctorExact_i64_i128 v hv
    | .i64, .u8 => ctorExact_i64_u8 v hv
    | .i64, .u16 => ctorExact_i64_u16 v hv
    | .i64, .u32 => ctorExact_i64_u32 v hv
    | .i64, .u64 => ctorExact_i64_u64 v hv
    | .i64, .u128 => ctorExact_i64_u128 v hv
    | .i128, .i8 => ctorExact_i128_i8 v hv
    | .i128, .i16 => ctorExact_i128_i16 v hv
    | .i128, .i32 => ctorExact_i128_i32 v hv
    | .i128, .i64 => ctorExact_i128_i64 v hv
    | .i128, .i128 => ctorExact_i128_i128 v hv
    | .i128, .u8 => ctorExact_i128_u8 v hv
    | .i128, .u16 => ctorExact_i128_u16 v hv
    | .i128, .u32 => ctorExact_i128_u32 v hv
    | .i128, .u64 => ctorExact_i128_u64 v hv
    | .i128, .u128 => ctorExact_i128_u128 v hv
    | .u8, .i8 => ctorExact_u8_i8 v hv
    | .u8, .i16 => ctorExact_u8_i16 v hv
    | .u8, .i32 => ctorExact_u8_i32 v hv
    | .u8, .i64 => ctorExact_u8_i64 v hv
    | .u8, .i128 => ctorExact_u8_i128 v hv
    | .u8, .u8 => ctorExact_u8_u8 v hv
    | .u8, .u16 => ctorExact_u8_u16 v hv
    | .u8, .u32 => ctorExact_u8_u32 v hv
    | .u8, .u64 => ctorExact_u8_u64 v hv
    | .u8, .u128 => ctorExact_u8_u128 v hv
    | .u16, .i8 => ctorExact_u16_i8 v hv
    | .u16, .i16 => ctorExact_u16_i16 v hv
    | .u16, .i32 => ctorExact_u16_i32 v hv
    | .u16, .i64 => ctorExact_u16_i64 v hv
    | .u16, .i128 => ctorExact_u16_i128 v hv
    | .u16, .u8 => ctorExact_u16_u8 v hv
    | .u16, .u16 => ctorExact_u16_u16 v hv
    | .u16, .u32 => ctorExact_u16_u32 v hv
    | .u16, .u64 => ctorExact_u16_u64 v hv
    | .u16, .u128 => ctorExact_u16_u128 v hv
    | .u32, .i8 => ctorExact_u32_i8 v hv
    | .u32, .i16 => ctorExact_u32_i16 v hv
    | .u32, .i32 => ctorExact_u32_i32 v hv
    | .u32, .i64 => ctorExact_u32_i64 v hv
    | .u32, .i128 => ctorExact_u32_i128 v hv
    | .u32, .u8 => ctorExact_u32_u8 v hv
    | .u32, .u16 => ctorExact_u32_u16 v hv
    | .u32, .u32 => ctorExact_u32_u32 v hv
    | .u32, .u64 => ctorExact_u32_u64 v hv
    | .u32, .u128 => ctorExact_u32_u128 v hv
    | .u64, .i8 => ctorExact_u64_i8 v hv
    | .u64, .i16 => ctorExact_u64_i16 v hv
    | .u64, .i32 => ctorExact_u64_i32 v hv
    | .u64, .i64 => ctorExact_u64_i64 v hv
    | .u64, .i128 => ctorExact_u64_i128 v hv
    | .u64, .u8 => ctorExact_u64_u8 v hv
    | .u64, .u16 => ctorExact_u64_u16 v hv
    | .u64, .u32 => ctorExact_u64_u32 v hv
    | .u64, .u64 => ctorExact_u64_u64 v hv
    | .u64, .u128 => ctorExact_u64_u128 v hv
    | .u128, .i8 => ctorExact_u128_i8 v hv
    | .u128, .i16 => ctorExact_u128_i16 v hv
    | .u128, .i32 => ctorExact_u128_i32 v hv
    | .u128, .i64 => ctorExact_u128_i64 v hv
    | .u128, .i128 => ctorExact_u128_i128 v hv
    | .u128, .u8 => ctorExact_u128_u8 v hv
    | .u128, .u16 => ctorExact_u128_u16 v hv
    | .u128, .u32 => ctorExact_u128_u32 v hv
    | .u128, .u64 => ctorExact_u128_u64 v hv
    | .u128, .u128 => ctorExact_u128_u128 v hv
  · cases To <;> cases b <;> constructor <;> conv_solve

/-- `Signed(x)` and `Unsigned(x)` for fixed-width integers (`base/boot.jl:1206-1215`)
convert exactly to the same-width signed or unsigned type. -/
def SignedUnsignedExact : Prop :=
  ∀ (t : IntTy) (x : JInt t),
    resultVal (signedOf x) =
      (if t.toSigned.min ≤ x.val ∧ x.val ≤ t.toSigned.max then some x.val else none) ∧
    resultVal (unsignedOf x) =
      (if t.toUnsigned.min ≤ x.val ∧ x.val ≤ t.toUnsigned.max then some x.val else none)

theorem signedUnsignedExact : SignedUnsignedExact := by
  intro t x
  exact ⟨(ctorExact t.toSigned (.int t x)).1, (ctorExact t.toUnsigned (.int t x)).1⟩

/-- A failing integer conversion that does not narrow the bit width reports
`convert` as the failing function, as the comment in `check_sign_bit`
(`base/boot.jl:1049-1050`) intends: `trunc` is reserved for narrowing. -/
def WideningErrorNamesConvert : Prop :=
  ∀ (To : IntTy) (x : BuiltinInt), x.bits ≤ To.bits →
    ∀ e, ctor To x = .error e → e = .inexact "convert" To.name

theorem wideningErrorNamesConvert_refuted : ¬ WideningErrorNamesConvert := by
  intro h
  have := h .u16 (.int .i8 (JInt.lit .i8 (-1))) (by decide) (.inexact "trunc" "UInt16") rfl
  simp at this

/-- `Int(p)`/`UInt(p)` of a pointer and `Ptr{T}(x)` (`base/boot.jl:1197-1203`) are bit
casts: converting an address to a pointer and back is the identity, `Ptr{T}()` is the
null pointer, and `Integer`, `Signed`/`Unsigned` on other types and `T(x::T)` pass to the
documented targets. -/
def PtrCastsRoundTrip : Prop :=
  (∀ x : JInt .u64, uintOfPtr (ptrOfUInt x) = x) ∧
  (∀ x : JInt64, intOfPtr (ptrOfInt x) = x) ∧
  (∀ p : Ptr, ptrOfPtr p = p ∧ ptrOfUInt (uintOfPtr p) = p) ∧
  ptrDefault.addr.val = 0 ∧
  (∀ x : JInt .u8, addrSpaceOf x = x) ∧
  (∀ (α : Type) (x : α), sameTypeCtor x = x ∧ integerOfInteger x = x) ∧
  (∀ (α : Type) (intOf : α → R JInt64) (uintOf : α → R (JInt .u64)) (x : α),
    signedOther intOf x = intOf x ∧ unsignedOther uintOf x = uintOf x ∧
    integerOfFloat intOf x = intOf x)

theorem ptrCastsRoundTrip : PtrCastsRoundTrip := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rfl
  · intro ⟨v, hv⟩
    apply Subtype.ext
    simp [intOfPtr, ptrOfInt, bitcastInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits,
      IntTy.min, IntTy.max] at hv ⊢
    omega
  · intro p; exact ⟨rfl, rfl⟩
  · decide
  · intro ⟨v, hv⟩
    apply Subtype.ext
    simp only [addrSpaceOf, bitcastInt, JInt.wrap]
    exact wrapInt_of_inRange .u8 v hv
  · intro α x; exact ⟨rfl, rfl⟩
  · intro α i u x; exact ⟨rfl, rfl, rfl⟩

/-- The sign-bit and truncation helpers (`base/boot.jl:1037-1069`): the top bit is set
exactly for values that are negative as signed numbers, `check_sign_bit` returns its
argument unless the top bit is set, and the checked truncations succeed exactly when the
value survives the round trip through the narrower type. -/
def HelperSemantics : Prop :=
  (∀ (t : IntTy) (x : JInt t), isTopBitSet x = decide (wrapInt t.toSigned x.val < 0)) ∧
  (∀ (To t : IntTy) (x : JInt t), isTopBitSet x = false → checkSignBit To x = .ok x) ∧
  (∀ (To t : IntTy) (x : JInt t), isTopBitSet x = true →
    ∃ f, checkSignBit To x = .error (.inexact f To.name)) ∧
  (∀ (To t : IntTy) (x : JInt t),
    (checkedTruncSint To x = .ok (truncInt To x) ↔ x.val = (sextInt t (truncInt To x)).val)) ∧
  (∀ (To t : IntTy) (x : JInt t),
    (checkedTruncUint To x = .ok (truncInt To x) ↔ x.val = (zextInt t (truncInt To x)).val))

theorem helperSemantics : HelperSemantics := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro To t x h
    simp only [isTopBitSet, decide_eq_false_iff_not] at h
    simp [checkSignBit, h]
  · intro To t x h
    simp only [isTopBitSet, decide_eq_true_eq] at h
    simp [checkSignBit, h, throwInexact]
  · intro To t x
    simp only [checkedTruncSint, throwInexact]
    by_cases h : x.val = (sextInt t (truncInt To x)).val <;> simp [h]
  · intro To t x
    simp only [checkedTruncUint, throwInexact]
    by_cases h : x.val = (zextInt t (truncInt To x)).val <;> simp [h]

end JuliaLean.BootCov.IntConv

end

section

/-!
Properties of the Core struct constructors (`base/boot.jl`).
-/

namespace JuliaLean.BootCov.Objects

open JuliaLean
open JuliaLean.BootCov

/-- Exception constructors store their arguments in field order, leave omitted
fields undefined, and fill the documented defaults: `DomainError(val).msg == ""`,
`AssertionError().msg == ""`, `MethodError(f, args).world == typemax(UInt)`,
`TypeError(where, T, got)` has `func == Symbol(where)` and `context == ""`, and
`UndefVarError(var)` records the current world age with `scope` undefined. -/
def ExceptionFields : Prop :=
  (∀ m, getfieldObj (errorException m) 1 = .ok (.str m)) ∧
  (isdefinedObj boundsError0 1 = false ∧ isdefinedObj boundsError0 2 = false) ∧
  (∀ a, getfieldObj (boundsError1 a) 1 = .ok a ∧ isdefinedObj (boundsError1 a) 2 = false) ∧
  (∀ a i, getfieldObj (boundsError2 a i) 1 = .ok a ∧ getfieldObj (boundsError2 a i) 2 = .ok i) ∧
  (∀ n k, isdefinedObj (fieldless n) k = false) ∧
  (∀ w v, getfieldObj (undefVarError1 w v) 1 = .ok (.sym v) ∧
    getfieldObj (undefVarError1 w v) 2 = .ok (.int w) ∧ isdefinedObj (undefVarError1 w v) 3 = false) ∧
  (∀ w v s, getfieldObj (undefVarError2 w v s) 3 = .ok s) ∧
  (∀ m, getfieldObj (concurrencyViolationError m) 1 = .ok (.str m)) ∧
  (∀ mi, getfieldObj (missingCodeError mi) 1 = .ok mi) ∧
  (∀ v, getfieldObj (domainError1 v) 1 = .ok v ∧ getfieldObj (domainError1 v) 2 = .ok (.str "")) ∧
  (∀ v m, domainError2 v (.str m) = .ok (.obj "DomainError" [some v, some (.str m)])) ∧
  (∀ v m, (∀ s, m ≠ .str s) → domainError2 v m = .error (.method "convert")) ∧
  (∀ f c e g, typeError4 (.sym f) (.sym c) e g =
    .ok (.obj "TypeError" [some (.sym f), some (.sym c), some e, some g])) ∧
  (∀ str w e g, typeError3 str w e g =
    .ok (.obj "TypeError" [some (symbolOf str w), some (.str ""), some e, some g])) ∧
  (∀ f as, getfieldObj (inexactError f as) 2 = .ok (.tuple as)) ∧
  (∀ m, getfieldObj (overflowError m) 1 = .ok (.str m) ∧ getfieldObj (argumentError m) 1 = .ok (.str m)) ∧
  (∀ v, getfieldObj (undefKeywordError v) 1 = .ok (.sym v)) ∧
  (∀ f a w, getfieldObj (methodError3 f a w) 3 = .ok (.int w)) ∧
  (∀ f a, getfieldObj (methodError2 f a) 3 = .ok (.int (2 ^ 64 - 1))) ∧
  (∀ m, getfieldObj (assertionError1 m) 1 = .ok (.str m)) ∧
  getfieldObj assertionError0 1 = .ok (.str "") ∧
  (∀ t f, getfieldObj (fieldError t f) 2 = .ok (.sym f)) ∧
  (∀ f l e, getfieldObj (loadError f l e) 2 = .ok (.int l) ∧ getfieldObj (loadError f l e) 3 = .ok e) ∧
  (∀ m e, getfieldObj (initError m e) 1 = .ok (.sym m) ∧ getfieldObj (initError m e) 2 = .ok e) ∧
  (∀ a d, getfieldObj (abiOverride a d) 2 = .ok d) ∧
  (∀ a, getfieldObj (typeNameError a) 1 = .ok a)

theorem exceptionFields : ExceptionFields := by
  refine ⟨fun _ => rfl, ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, ?_,
    fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, ?_, fun _ _ _ _ => rfl, ?_,
    fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ => rfl, fun _ => rfl⟩
  · intro n k
    simp [isdefinedObj, fieldless]
  · intro v m h
    cases m <;> simp_all [domainError2, toAbstractString, bind, Except.bind]
  · intro str w e g
    cases w <;> rfl

/-- Wrapper and lattice-element constructors store their arguments; `Box()` and
`ReturnNode()`/`UpsilonNode()` leave their single field undefined; `WeakRef()` refers to
`nothing`; `VecElement(x)` is `VecElement{typeof(x)}(x)`; and `Pair(a, b)` stores both
arguments. -/
def WrapperFields : Prop :=
  (∀ s, stringOfString s = s) ∧ nothingCtor = .nothing ∧ emptyTuple = .tuple [] ∧
  (∀ m, getfieldObj (evalInto m) 1 = .ok (.module_ m)) ∧
  (∀ x, getfieldObj (box1 x) 1 = .ok x) ∧ getfieldObj box0 1 = .error .undefRef ∧
  (∀ v, getfieldObj (weakRef1 v) 1 = .ok v) ∧ getfieldObj weakRef0 1 = .ok .nothing ∧
  (∀ x, vecElement x = vecElementT x ∧ getfieldObj (vecElementT x) 1 = .ok x) ∧
  (∀ v, getfieldObj (const_ v) 1 = .ok v) ∧
  (∀ t u f, getfieldObj (partialStruct t u f) 3 = .ok f) ∧
  (∀ s a b, getfieldObj (interConditional s a b) 1 = .ok (.int s) ∧
    getfieldObj (interConditional s a b) 3 = .ok b) ∧
  (∀ s v i f, getfieldObj (interMustAlias s v i f) 3 = .ok (.int i)) ∧
  (∀ t e p s, getfieldObj (partialOpaque t e p s) 4 = .ok s) ∧
  (∀ f, getfieldObj (partialTask f) 1 = .ok f) ∧
  (∀ g a s, getfieldObj (generatedFunctionStub g a s) 1 = .ok g) ∧
  (∀ l v, getfieldObj (macroSource l v) 2 = .ok v) ∧
  (∀ a b, getfieldObj (pair a b) 1 = .ok a ∧ getfieldObj (pair a b) 2 = .ok b)

theorem wrapperFields : WrapperFields := by
  refine ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩

/-- IR node constructors store their arguments; `ReturnNode()`, `UpsilonNode()` and
`EnterNode(dest)` leave the optional field undefined; `LineNumberNode(l)` and
`DebugInfo(def)` fill `nothing`/`svec()`/`""`; `LineNumberNode(l, f)` turns a `String`
file into a `Symbol`, keeps `nothing` or a `Symbol`, and throws `TypeError` otherwise;
and `EnterNode(old, d)` retargets to `d`, keeping `old.scope` exactly when it is defined. -/
def IRNodeFields : Prop :=
  (∀ l, getfieldObj (gotoNode l) 1 = .ok (.int l)) ∧
  (∀ s, getfieldObj (newvarNode s) 1 = .ok s) ∧
  (∀ v, quoteNode v = .quoteNode v) ∧
  (∀ i, getfieldObj (ssaValue i) 1 = .ok (.int i) ∧ getfieldObj (argument i) 1 = .ok (.int i) ∧
    getfieldObj (slotNumber i) 1 = .ok (.int i)) ∧
  (∀ v, getfieldObj (returnNode1 v) 1 = .ok v) ∧ isdefinedObj returnNode0 1 = false ∧
  (∀ c d, getfieldObj (gotoIfNot c d) 2 = .ok (.int d)) ∧
  (∀ d, isdefinedObj (enterNode1 d) 2 = false) ∧
  (∀ d s, getfieldObj (enterNode2 d s) 2 = .ok s) ∧
  (∀ l, lineNumberNode1 l = .lineNode l .nothing) ∧
  (∀ l s, lineNumberNode2 l (.str s) = .ok (.lineNode l (.sym s)) ∧
    lineNumberNode2 l (.sym s) = .ok (.lineNode l (.sym s))) ∧
  (∀ l, lineNumberNode2 l .nothing = .ok (.lineNode l .nothing)) ∧
  (∀ l n, lineNumberNode2 l (.int n) = .error (.typeError "new")) ∧
  (∀ d, debugInfo1 d = debugInfo4 d .nothing (.tuple []) (.str "")) ∧
  (∀ d a b c, getfieldObj (debugInfo4 d a b c) 4 = .ok c) ∧
  (∀ e v, getfieldObj (phiNode e v) 2 = .ok v) ∧
  (∀ v t, getfieldObj (piNode v t) 2 = .ok t) ∧
  (∀ v, getfieldObj (phiCNode v) 1 = .ok v) ∧
  (∀ v, getfieldObj (upsilonNode1 v) 1 = .ok v) ∧ isdefinedObj upsilonNode0 1 = false ∧
  (∀ s p m b, getfieldObj (methodMatch s p m b) 4 = .ok (.bool b)) ∧
  (∀ m me f l i, getfieldObj (lineInfoNode m me f l i) 4 = .ok (.int l)) ∧
  (∀ d d' s, enterNodeRetarget (enterNode2 d s) d' = .ok (enterNode2 d' s)) ∧
  (∀ d d', enterNodeRetarget (enterNode1 d) d' = .ok (enterNode1 d'))

theorem irNodeFields : IRNodeFields := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- The `NamedTuple` constructors (`base/boot.jl:1022-1030`) pair the names with the
arguments in order; `NamedTuple{names}(args)` throws exactly when the counts differ, and
`NamedTuple()` is empty. -/
def NamedTupleCtors : Prop :=
  (∀ names args, names.length = args.length → namedTupleNames names args = .ok (names.zip args)) ∧
  (∀ names args, names.length ≠ args.length → ∃ m, namedTupleNames names args = .error (.error m)) ∧
  (∀ names args (h : names.length = args.length), namedTupleNT names args h = names.zip args) ∧
  namedTupleEmpty = []

theorem namedTupleCtors : NamedTupleCtors := by
  refine ⟨?_, ?_, fun _ _ _ => rfl, rfl⟩
  · intro names args h; simp [namedTupleNames, h]
  · intro names args h
    exact ⟨"NamedTuple names and field types must have matching lengths", by simp [namedTupleNames, h]⟩

/-- The handle constructors pass their arguments to the runtime in order:
`GlobalRef(m, s)` refers to binding `s` of `m`; `Module()` defaults to the name
`:anonymous` with standard imports and default names; `CodeInstance`, `getptls`,
`include`, `eval` and calling an `EvalInto` return what the runtime call returns. -/
def HandleCtors : Prop :=
  (∀ m s, globalRef m s = .globalRef m s) ∧
  moduleCtor = ⟨"anonymous", true, true⟩ ∧
  (∀ n a b, moduleCtor n a b = ⟨n, a, b⟩) ∧
  (∀ (f : List JVal → JVal) as, codeInstance f as = f as) ∧
  (∀ p, getptls p = p) ∧
  (∀ (ld : String → String → R JVal) m f, include_ ld m f = ld m f) ∧
  (∀ (ev : String → JVal → R JVal) m e, eval_ ev m e = ev m e ∧
    evalIntoCall ev (evalInto m) e = ev m e)

theorem handleCtors : HandleCtors :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => ⟨rfl, rfl⟩⟩

end JuliaLean.BootCov.Objects

end

section

/-!
Properties of the type-object functions of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

/-- `Typeof(x)` (`base/boot.jl:300-307`) is `Type{x}` for a type with free typevars,
`Core.TypeEgal{x}` for any other type, and `typeof(x)` for a non-type; `TypeEqOf(x)`
(lines 316-319) is `Type{x}` for every type; `_typeof_captured_variable(t)` (line 387) is
`typeof(t)` for a type with free typevars and `Typeof(t)` otherwise. -/
def TypeofKinds : Prop :=
  (∀ (typeof : JVal → JType) (t : JType), isType t = true →
    typeof_ typeof (.ty t) = (if hasFreeTypevars t then typeKind t else typeEgalKind t) ∧
    typeEqOf typeof (.ty t) = typeKind t) ∧
  (∀ (typeof : JVal → JType) (x : JVal), (∀ t, x ≠ .ty t) →
    typeof_ typeof x = typeof x ∧ typeEqOf typeof x = typeof x) ∧
  (∀ (typeof : JVal → JType) (t : JType), isType t = true → hasFreeTypevars t = true →
    typeofCapturedVariable typeof (.ty t) = typeof (.ty t)) ∧
  (∀ (typeof : JVal → JType) (t : JType), hasFreeTypevars t = false →
    typeofCapturedVariable typeof (.ty t) = typeof_ typeof (.ty t))

theorem typeofKinds : TypeofKinds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro typeof t h
    simp [typeof_, typeEqOf, h]
  · intro typeof x h
    cases x with
    | ty t => exact absurd rfl (h t)
    | _ => exact ⟨rfl, rfl⟩
  · intro typeof t h1 h2
    simp [typeofCapturedVariable, h1, h2]
  · intro typeof t h
    simp [typeofCapturedVariable, h]

/-- `TypeVar(n)`, `TypeVar(n, ub)` and `TypeVar(n, lb, ub)` (`base/boot.jl:370-372`) build a
fresh typevar named `n` with bounds `Union{}`/`Any` by default, throw `TypeError` when `n`
is not a `Symbol` or a bound is not a type; `UnionAll(v, t)` (line 373) throws `TypeError`
unless `v` is a `TypeVar`, returns `v.ub` for `t === v`, returns `t` when `v` does not occur
in `t`, and otherwise wraps `t`. -/
def TypeVarUnionAll : Prop :=
  (∀ (f : Nat) (n : String) (lb ub : JType), isBound lb = true → isBound ub = true →
    typevar3 f (.sym n) lb ub = .ok (.tvar f n lb ub)) ∧
  (∀ (f : Nat) (n : JVal) (lb ub : JType), (∀ s, n ≠ .sym s) →
    typevar3 f n lb ub = .error (.typeError "typeassert")) ∧
  (∀ (f : Nat) (n : JVal), typevar1 f n = typevar3 f n .bottom (.dt "Any" true [])) ∧
  (∀ (f : Nat) (n : JVal) (ub : JType), typevar2 f n ub = typevar3 f n .bottom ub) ∧
  (∀ (f : Nat) (n : String) (lb ub : JType), isBound ub = false →
    typevar3 f (.sym n) lb ub = .error (.typeError "TypeVar")) ∧
  (∀ (v t : JType), (∀ i n lb ub, v ≠ .tvar i n lb ub) →
    unionAllCtor v t = .error (.typeError "typeassert")) ∧
  (∀ (i : Nat) (n : String) (lb ub : JType),
    unionAllCtor (.tvar i n lb ub) (.tvar i n lb ub) = .ok ub) ∧
  (∀ (i : Nat) (n : String) (lb ub : JType) (name : String) (abs : Bool) (ps : List JType),
    unionAllCtor (.tvar i n lb ub) (.dt name abs ps) =
      .ok (if hasTypevar (.dt name abs ps) (.tvar i n lb ub) then
        .unionAll (.tvar i n lb ub) (.dt name abs ps) else .dt name abs ps))

theorem typeVarUnionAll : TypeVarUnionAll := by
  refine ⟨?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro f n lb ub h1 h2
    simp [typevar3, h1, h2]
  · intro f n lb ub h
    cases n with
    | sym s => exact absurd rfl (h s)
    | _ => rfl
  · intro f n lb ub h
    simp only [typevar3, h]
    split <;> rfl
  · intro v t h
    cases v with
    | tvar i n lb ub => exact absurd rfl (h i n lb ub)
    | _ => rfl
  · intro i n lb ub
    simp [unionAllCtor, typeUnionall]
  · intro i n lb ub name abs ps
    simp only [unionAllCtor, typeUnionall]
    split <;> rfl

/-- A `UnionAll` as Julia builds it: the variable is a `TypeVar` that occurs in the body
and the body is a type other than that variable. -/
def NormalSpine : JType → Prop
  | .unionAll v b =>
    (∃ i n lb ub, v = .tvar i n lb ub ∧ hasTypevar b v = true ∧
      (∀ n' lb' ub', b ≠ .tvar i n' lb' ub') ∧
      (∀ T N, b ≠ .vararg T N) ∧ (∀ k, b ≠ .intParam k) ∧ (∀ s, b ≠ .names s) ∧
      (∀ s, b ≠ .other s)) ∧ NormalSpine b
  | _ => True

theorem unionAllCtor_normal (v b : JType)
    (h : ∃ i n lb ub, v = .tvar i n lb ub ∧ hasTypevar b v = true ∧
      (∀ n' lb' ub', b ≠ .tvar i n' lb' ub') ∧
      (∀ T N, b ≠ .vararg T N) ∧ (∀ k, b ≠ .intParam k) ∧ (∀ s, b ≠ .names s) ∧
      (∀ s, b ≠ .other s)) :
    unionAllCtor v b = .ok (.unionAll v b) := by
  obtain ⟨i, n, lb, ub, rfl, hv, hne, hva, hk, hs, ho⟩ := h
  simp only [unionAllCtor, typeUnionall]
  cases b with
  | vararg T N => exact absurd rfl (hva T N)
  | intParam k => exact absurd rfl (hk k)
  | names s => exact absurd rfl (hs s)
  | other s => exact absurd rfl (ho s)
  | tvar j n' lb' ub' =>
    have : j ≠ i := fun e => hne n' lb' ub' (by rw [e])
    simp [this, hv]
  | _ => simp [hv]

/-- `typename` (`base/boot.jl:1310-1318`) sees through `where`: `typename(u)` equals
`typename(unwrap_unionall(u))` for every type; a `Union` has a type name exactly when
both members have the same one; values that are not `DataType`, `Union` or `UnionAll`
(including `Union{}`) throw `TypeNameError`. -/
def TypenameBehaviour : Prop :=
  (∀ u : JType, typename u = typename (unwrapUnionall u)) ∧
  (∀ (a b : JType) (na nb : String), typename a = .ok na → typename b = .ok nb →
    typename (.union a b) = (if na = nb then .ok nb else .error .typeName)) ∧
  (∀ (a b : JType) e, typename a = .error e → typename (.union a b) = .error e) ∧
  (∀ (n : String) (abs : Bool) (ps : List JType), typename (.dt n abs ps) = .ok n) ∧
  typename .bottom = .error .typeName ∧
  (∀ T N, typename (.vararg T N) = .error .typeName)

theorem typename_unwrap : (u : JType) → typename u = typename (unwrapUnionall u)
  | .unionAll _ b => by simp only [typename, unwrapUnionall]; exact typename_unwrap b
  | .dt _ _ _ => by rfl
  | .union _ _ => by rfl
  | .bottom => by rfl
  | .tvar _ _ _ _ => by rfl
  | .vararg _ _ => by rfl
  | .typeApp _ _ => by rfl
  | .intParam _ => by rfl
  | .names _ => by rfl
  | .other _ => by rfl

theorem typenameBehaviour : TypenameBehaviour := by
  refine ⟨typename_unwrap, ?_, ?_, fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩
  · intro a b na nb ha hb
    simp only [typename, ha, hb, bind, Except.bind]
    split <;> rfl
  · intro a b e ha
    simp [typename, ha, bind, Except.bind]

/-- The `TypeApp` machinery (`base/boot.jl:420-467`): `_contains_typeapp` finds a
`TypeApp` itself or under `where`; `apply_type_or_typeapp(tc, params...)` builds the
left-nested `TypeApp` chain when the head is a `TypeVar` or `TypeApp` or some parameter
contains a `TypeApp`, and otherwise calls `apply_type(tc, params...)`; an empty typegroup
resolves to `()`. -/
def TypeAppBehaviour : Prop :=
  (∀ h p, containsTypeapp (typeAppCtor h p) = true) ∧
  (∀ v b, containsTypeapp (.unionAll v b) = containsTypeapp b) ∧
  (∀ tc p ps, typeAppChain tc (p :: ps) = typeAppChain (.typeApp tc p) ps) ∧
  (∀ (ap : JType → List JType → R JType) i n lb ub ps,
    applyTypeOrTypeapp ap (.tvar i n lb ub) ps = .ok (typeAppChain (.tvar i n lb ub) ps)) ∧
  (∀ (ap : JType → List JType → R JType) h p ps,
    applyTypeOrTypeapp ap (.typeApp h p) ps = .ok (typeAppChain (.typeApp h p) ps)) ∧
  (∀ (ap : JType → List JType → R JType) name abs qs ps, ps.any containsTypeapp = true →
    applyTypeOrTypeapp ap (.dt name abs qs) ps = .ok (typeAppChain (.dt name abs qs) ps)) ∧
  (∀ (ap : JType → List JType → R JType) name abs qs ps, ps.any containsTypeapp = false →
    applyTypeOrTypeapp ap (.dt name abs qs) ps = ap (.dt name abs qs) ps) ∧
  (∀ (res : List JVal → List JVal → List JVal → JVal) s o, resolveTypegroup res [] s o = .tuple []) ∧
  (∀ (res : List JVal → List JVal → List JVal → JVal) t ts s o,
    resolveTypegroup res (t :: ts) s o = res (t :: ts) s o)

theorem typeAppBehaviour : TypeAppBehaviour := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, ?_, ?_, fun _ _ _ => rfl, ?_⟩
  · intro ap name abs qs ps h; simp [applyTypeOrTypeapp, h]
  · intro ap name abs qs ps h; simp [applyTypeOrTypeapp, h]
  · intro res t ts s o; simp [resolveTypegroup]

/-- `(>:)(a, b)` is `b <: a` and `(!==)(a, b)` is `!(a === b)` (`base/boot.jl:1322-1323`). -/
def BootOperators : Prop :=
  (∀ {α : Type} (sub : α → α → Bool) a b, supertypeOf sub a b = sub b a) ∧
  (∀ {α : Type} (egal : α → α → Bool) a b, notEgal egal a b = !egal a b)

theorem bootOperators : BootOperators := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end JuliaLean.BootCov.Types

end

section

/-!
Properties of the memory, array, `SimpleVector` and `Symbol` primitives.
-/

namespace JuliaLean.BootCov.Arrays

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv
open JuliaLean.ReinterpretArrays
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem i64_bounds (x : JInt64) : -(2:Int) ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem wrapU64_nonneg (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) : wrapInt .u64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem wrapU64_neg (v : Int) (h0 : -(2:Int) ^ 64 < v) (h1 : v < 0) :
    wrapInt .u64 v = v + 2 ^ 64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem wrapI64_small (v : Int) (h0 : -(2:Int) ^ 63 ≤ v) (h1 : v < 2 ^ 63) : wrapInt .i64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem lit1_val : (JInt.lit .i64 1).val = 1 := rfl
-- Source: base/essentials.jl:385-388
-- placed here to break an import cycle with essentials

theorem sub_lit1_val (i : JInt64) : (i - JInt.lit .i64 1).val = wrapInt .i64 (i.val - 1) := by
  show wrapInt .i64 (i.val - (JInt.lit .i64 1).val) = _
  rw [lit1_val]

/-- `GenericMemory{...}(undef, m)` (`base/boot.jl:762-765`) allocates exactly `m`
undefined slots when `0 ≤ m ≤ maxLen` and throws `ArgumentError` otherwise, for any
runtime limit below `typemax(Int)`; the tuple and empty forms agree. -/
def MemoryCtorCorrect : Prop :=
  ∀ maxLen : Nat, maxLen < 2 ^ 63 → ∀ m : JInt64,
    (0 ≤ m.val ∧ m.val ≤ maxLen → memoryUndef maxLen m = .ok (List.replicate m.val.toNat none)) ∧
    (¬(0 ≤ m.val ∧ m.val ≤ maxLen) → ∃ msg, memoryUndef maxLen m = .error (.argument msg)) ∧
    memoryUndefTuple maxLen m = memoryUndef maxLen m ∧
    memoryEmpty maxLen = .ok []

theorem memoryCtorCorrect : MemoryCtorCorrect := by
  intro maxLen hmax m
  have hm := i64_bounds m
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro ⟨h1, h2⟩
    simp only [memoryUndef, memorynew, wrapU64_nonneg m.val h1 (by omega)]
    rw [if_neg (by omega)]
  · intro h
    refine ⟨"invalid GenericMemory size", ?_⟩
    simp only [memoryUndef, memorynew]
    rw [if_pos]
    by_cases h0 : 0 ≤ m.val
    · rw [wrapU64_nonneg m.val h0 (by omega)]; omega
    · rw [wrapU64_neg m.val (by omega) (by omega)]; omega
  · simp only [memoryEmpty, memoryUndef, memorynew]
    rfl

/-- `memoryref(mem, i)` (`base/boot.jl:769`) for an index of any built-in integer type
returns the reference to slot `i` exactly when `Int(i)` succeeds and `1 ≤ i ≤ length(mem)`,
throws `BoundsError` for other representable indices, and `memoryref(ref, i)`
(`base/boot.jl:770`) moves a valid reference by `i - 1` slots, negative shifts included,
throwing `BoundsError` exactly when the target is outside the memory. -/
def MemoryrefCorrect : Prop :=
  (∀ (mem : Mem) (i : JInt64), mem.length < 2 ^ 63 →
    (1 ≤ i.val ∧ i.val ≤ mem.length → memoryref2 mem (.int .i64 i) = .ok ⟨mem, (i.val - 1).toNat⟩) ∧
    (¬(1 ≤ i.val ∧ i.val ≤ mem.length) → memoryref2 mem (.int .i64 i) = .error .bounds)) ∧
  (∀ (r : MRef) (i : JInt64), r.mem.length < 2 ^ 63 → r.off ≤ r.mem.length →
    (0 ≤ r.off + i.val - 1 ∧ r.off + i.val - 1 < r.mem.length →
      memoryrefRef r (.int .i64 i) = .ok ⟨r.mem, (r.off + i.val - 1).toNat⟩) ∧
    (¬(0 ≤ r.off + i.val - 1 ∧ r.off + i.val - 1 < r.mem.length) →
      memoryrefRef r (.int .i64 i) = .error .bounds)) ∧
  (∀ mem, memoryref1 mem = ⟨mem, 0⟩ ∧ genericMemoryRef1 mem = memoryref1 mem) ∧
  (∀ mem i, genericMemoryRef2 mem i = memoryref2 mem i) ∧
  (∀ r i, genericMemoryRefRef r i = memoryrefRef r i)

theorem memoryrefCorrect : MemoryrefCorrect := by
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro mem i hlen
    have hi := i64_bounds i
    have hc : ctor .i64 (.int .i64 i) = .ok i := rfl
    simp only [memoryref2, hc, bind, Except.bind, memoryrefnewMem]
    constructor
    · intro h
      rw [wrapU64_nonneg (i.val - 1) (by omega) (by omega), if_neg (by omega)]
    · intro h
      rw [if_pos]
      by_cases hp : 0 ≤ i.val - 1
      · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]; omega
      · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]; omega
  · intro r i hlen hoff
    have hi := i64_bounds i
    have hc : ctor .i64 (.int .i64 i) = .ok i := rfl
    simp only [memoryrefRef, hc, bind, Except.bind, memoryrefnewRef]
    by_cases hp : 0 ≤ i.val - 1
    · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]
      rw [wrapU64_nonneg ((r.off : Int) + (i.val - 1)) (by omega) (by omega)]
      rw [show (r.off : Int) + (i.val - 1) = r.off + i.val - 1 by omega]
      constructor
      · intro h; rw [if_neg (by omega)]
      · intro h; rw [if_pos (by omega)]
    · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]
      by_cases hq : 0 ≤ (r.off : Int) + i.val - 1
      · have : wrapInt .u64 (↑r.off + (i.val - 1 + 2 ^ 64)) = ↑r.off + i.val - 1 := by
          simp [wrapInt, IntTy.signed, IntTy.bits]; omega
        rw [this]
        constructor
        · intro h; rw [if_neg (by omega)]
        · intro h; rw [if_pos (by omega)]
      · have : wrapInt .u64 (↑r.off + (i.val - 1 + 2 ^ 64)) = ↑r.off + i.val - 1 + 2 ^ 64 := by
          simp [wrapInt, IntTy.signed, IntTy.bits]; omega
        rw [this]
        constructor
        · intro h; omega
        · intro h; rw [if_pos (by omega)]

/-- Exact product of `Int` dimensions. -/
def prodVals : List JInt64 → Int
  | [] => 1
  | x :: xs => x.val * prodVals xs

theorem uleTypemax_false {x : JInt64} (h : uleTypemax x = false) :
    0 ≤ x.val ∧ x.val < IntTy.max .i64 := by
  simp only [uleTypemax, decide_eq_false_iff_not, not_or] at h
  have := x.property.2
  have h1 := h.1
  have h2 := h.2
  constructor <;> omega

theorem loop_sound : ∀ (d : List JInt64) (a : JInt64) (ovflw neg zero : Bool) (P : Int),
    (zero = true → a.val = 0 ∧ P = 0) → (ovflw = false → a.val = P) →
    (checkedMulDimsLoop d a ovflw neg zero).2 = false →
    (checkedMulDimsLoop d a ovflw neg zero).1.val = P * prodVals d ∧ neg = false ∧
      ∀ x ∈ d, uleTypemax x = false := by
  intro d
  induction d with
  | nil =>
    intro a ovflw neg zero P hz ho h
    simp only [checkedMulDimsLoop, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      Bool.not_eq_false'] at h
    refine ⟨?_, h.1, by simp⟩
    simp only [checkedMulDimsLoop, prodVals, Int.mul_one]
    rcases h.2 with h2 | h2
    · exact ho h2
    · rw [(hz h2).1, (hz h2).2]
  | cons di d ih =>
    intro a ovflw neg zero P hz ho h
    simp only [checkedMulDimsLoop] at h ⊢
    have hmul : (checkedSmul a di).1.val = wrapInt .i64 (a.val * di.val) := rfl
    have hov : (checkedSmul a di).2 = false →
        IntTy.min .i64 ≤ a.val * di.val ∧ a.val * di.val ≤ IntTy.max .i64 := by
      intro h'
      simp only [checkedSmul, decide_eq_false_iff_not, Decidable.not_not] at h'
      exact h'
    have r := ih (checkedSmul a di).1 (ovflw || (checkedSmul a di).2) (neg || uleTypemax di)
      (zero || decide (di.val = 0)) (P * di.val) ?_ ?_ h
    · simp only [Bool.or_eq_false_iff] at r
      refine ⟨?_, r.2.1.1, ?_⟩
      · rw [r.1, prodVals, Int.mul_assoc]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · rw [hx]; exact r.2.1.2
        · exact r.2.2 x hx
    · intro hz'
      rw [hmul]
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hz'
      rcases hz' with hz' | hz'
      · obtain ⟨ha, hP⟩ := hz hz'
        rw [ha, hP]; simp [wrapInt, IntTy.signed, IntTy.bits]
      · rw [hz']; simp [wrapInt, IntTy.signed, IntTy.bits]
    · intro ho'
      simp only [Bool.or_eq_false_iff] at ho'
      rw [hmul, wrapInt_of_inRange .i64 _ (hov ho'.2), ho ho'.1]

theorem checkedDims_ge2 (d : List JInt64) (hd : 2 ≤ d.length) :
    checkedDims d = if (checkedMulDims d).2 then .error (.argumentError "invalid Array dimensions")
      else .ok (checkedMulDims d).1 := by
  match d, hd with
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl

theorem checkedMulDims_two (m n : JInt64) :
    checkedMulDims [m, n] = ((checkedSmul m n).1,
      (checkedSmul m n).2 || uleTypemax m || uleTypemax n) := rfl

theorem checkedMulDims_three (m n o : JInt64) (rest : List JInt64) :
    checkedMulDims (m :: n :: o :: rest) =
      checkedMulDimsLoop (n :: o :: rest) m false (uleTypemax m) false := rfl

/-- `Core.checked_dims(d...)` (`base/boot.jl:811-818`, through `_checked_mul_dims` at
lines 782-809) never returns a wrong length: with two or more dimensions it either throws
`ArgumentError` or returns the exact product of the dimensions, all of which are then
nonnegative and below `typemax(Int)`; `checked_dims()` is 1 and `checked_dims(m)` is `m`. -/
def CheckedDimsSound : Prop :=
  (checkedDims [] = .ok (JInt.lit .i64 1)) ∧
  (∀ m, checkedDims [m] = .ok m) ∧
  (∀ d : List JInt64, 2 ≤ d.length →
    (∀ p, checkedDims d = .ok p → p.val = prodVals d ∧
        ∀ x ∈ d, 0 ≤ x.val ∧ x.val < IntTy.max .i64) ∧
    (∀ e, checkedDims d = .error e → e = .argumentError "invalid Array dimensions"))

theorem checkedDimsSound : CheckedDimsSound := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro d hd
  rw [checkedDims_ge2 d hd]
  refine ⟨?_, ?_⟩
  · intro p hp
    split at hp
    · cases hp
    · rename_i hb
      cases hp
      match d, hd with
      | [m, n], _ =>
        rw [checkedMulDims_two] at hb ⊢
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
        have hm := uleTypemax_false hb.1.2
        have hn := uleTypemax_false hb.2
        have hov : IntTy.min .i64 ≤ m.val * n.val ∧ m.val * n.val ≤ IntTy.max .i64 := by
          have h1 := hb.1.1
          simp only [checkedSmul, decide_eq_false_iff_not, Decidable.not_not] at h1
          exact h1
        refine ⟨?_, ?_⟩
        · show wrapInt .i64 (m.val * n.val) = _
          rw [wrapInt_of_inRange .i64 _ hov]
          simp [prodVals]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx] <;> assumption
      | m :: n :: o :: rest, _ =>
        rw [checkedMulDims_three] at hb ⊢
        have r := loop_sound (n :: o :: rest) m false (uleTypemax m) false m.val
          (by simp) (fun _ => rfl) (by simpa using hb)
        refine ⟨by rw [r.1]; simp only [prodVals], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · rw [hx]; exact uleTypemax_false r.2.1
        · exact uleTypemax_false (r.2.2 x (by simpa using hx))
  · intro e he
    split at he <;> cases he <;> rfl

/-- The `Array{T,N}(undef, dims...)` constructors (`base/boot.jl:821-847`, every
dimension count, the tuple forms and the `Array{T}` and `Vector{T}()` forms) either throw
`ArgumentError` or build an array with exactly the requested dimensions whose memory has
exactly the product of the dimensions as length. -/
def ArrayCtorShape : Prop :=
  ∀ maxLen : Nat, maxLen < 2 ^ 63 → ∀ d : List JInt64,
    (∀ A, arrayUndef maxLen d = .ok A →
      A.dims = d ∧ (A.ref.mem.length : Int) = prodVals d ∧ A.ref.off = 0 ∧ ∀ x ∈ d, 0 ≤ x.val) ∧
    (∀ e, arrayUndef maxLen d = .error e → ∃ msg, e = .argument msg) ∧
    arrayUndefTuple maxLen d = arrayUndef maxLen d ∧ arrayTUndef maxLen d = arrayUndef maxLen d ∧
    arrayTUndefTuple maxLen d = arrayUndef maxLen d ∧
    vectorEmpty maxLen = arrayUndef maxLen [JInt.lit .i64 0]

theorem memoryUndef_ok {maxLen : Nat} (h : maxLen < 2 ^ 63) {m : JInt64} {mem : Mem}
    (hm : memoryUndef maxLen m = .ok mem) : (mem.length : Int) = m.val ∧ 0 ≤ m.val := by
  have c := memoryCtorCorrect maxLen h m
  by_cases hr : 0 ≤ m.val ∧ m.val ≤ maxLen
  · rw [c.1 hr] at hm
    cases hm
    simp
    omega
  · obtain ⟨msg, hmsg⟩ := c.2.1 hr
    rw [hmsg] at hm
    cases hm

theorem memoryUndef_err {maxLen : Nat} (h : maxLen < 2 ^ 63) {m : JInt64} {e : Exc}
    (hm : memoryUndef maxLen m = .error e) : ∃ msg, e = .argument msg := by
  have c := memoryCtorCorrect maxLen h m
  by_cases hr : 0 ≤ m.val ∧ m.val ≤ maxLen
  · rw [c.1 hr] at hm; cases hm
  · obtain ⟨msg, hmsg⟩ := c.2.1 hr
    rw [hmsg] at hm; cases hm; exact ⟨msg, rfl⟩

theorem viaDims_ok {maxLen : Nat} (h : maxLen < 2 ^ 63) {d : List JInt64} (hd : 2 ≤ d.length)
    {A : Arr} (hA : arrayN maxLen d = .ok A) :
    A.dims = d ∧ (A.ref.mem.length : Int) = prodVals d ∧ A.ref.off = 0 ∧ ∀ x ∈ d, 0 ≤ x.val := by
  have s := checkedDimsSound.2.2 d hd
  unfold arrayN at hA
  cases hc : checkedDims d with
  | error e =>
    rw [hc] at hA
    have := s.2 e hc
    subst this
    cases hA
  | ok p =>
    rw [hc] at hA
    simp only [ofJl, bind, Except.bind, newAsMemoryref] at hA
    cases hm : memoryUndef maxLen p with
    | error e => rw [hm] at hA; cases hA
    | ok mem =>
      rw [hm] at hA
      cases hA
      have hp := s.1 p hc
      have hl := memoryUndef_ok h hm
      exact ⟨rfl, by simp [memoryref1, memoryrefnew1]; rw [hl.1, hp.1], rfl,
        fun x hx => (hp.2 x hx).1⟩

theorem viaDims_err {maxLen : Nat} (h : maxLen < 2 ^ 63) {d : List JInt64} (hd : 2 ≤ d.length)
    {e : Exc} (hA : arrayN maxLen d = .error e) : ∃ msg, e = .argument msg := by
  have s := checkedDimsSound.2.2 d hd
  unfold arrayN at hA
  cases hc : checkedDims d with
  | error e' =>
    rw [hc] at hA
    have := s.2 e' hc
    subst this
    simp only [ofJl, bind, Except.bind] at hA
    cases hA
    exact ⟨_, rfl⟩
  | ok p =>
    rw [hc] at hA
    simp only [ofJl, bind, Except.bind, newAsMemoryref] at hA
    cases hm : memoryUndef maxLen p with
    | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
    | ok mem => rw [hm] at hA; cases hA

theorem arrayCtorShape : ArrayCtorShape := by
  intro maxLen h d
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro A hA
    match d with
    | [] =>
      simp only [arrayUndef, arrayN, checkedDims, ofJl, bind, Except.bind, newAsMemoryref] at hA
      cases hm : memoryUndef maxLen (JInt.lit .i64 1) with
      | error e => rw [hm] at hA; cases hA
      | ok mem =>
        rw [hm] at hA; cases hA
        have hl := memoryUndef_ok h hm
        refine ⟨rfl, ?_, rfl, by simp⟩
        simp only [memoryref1, memoryrefnew1, prodVals]
        rw [hl.1]; rfl
    | [m] =>
      simp only [arrayUndef, array1, bind, Except.bind] at hA
      cases hm : memoryUndef maxLen m with
      | error e => rw [hm] at hA; cases hA
      | ok mem =>
        rw [hm] at hA; cases hA
        have hl := memoryUndef_ok h hm
        refine ⟨rfl, ?_, rfl, ?_⟩
        · simp [memoryref1, memoryrefnew1, prodVals, hl.1]
        · simp [hl.2]
    | [m, n] => exact viaDims_ok h (by simp) hA
    | m :: n :: o :: rest =>
      cases rest with
      | nil => exact viaDims_ok h (by simp) hA
      | cons q rest => exact viaDims_ok h (by simp) hA
  · intro e hA
    match d with
    | [] =>
      simp only [arrayUndef, arrayN, checkedDims, ofJl, bind, Except.bind, newAsMemoryref] at hA
      cases hm : memoryUndef maxLen (JInt.lit .i64 1) with
      | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
      | ok mem => rw [hm] at hA; cases hA
    | [m] =>
      simp only [arrayUndef, array1, bind, Except.bind] at hA
      cases hm : memoryUndef maxLen m with
      | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
      | ok mem => rw [hm] at hA; cases hA
    | [m, n] => exact viaDims_err h (by simp) hA
    | m :: n :: o :: rest =>
      cases rest with
      | nil => exact viaDims_err h (by simp) hA
      | cons q rest => exact viaDims_err h (by simp) hA

/-- The `Symbol` constructors (`base/boot.jl:858-873`): `Symbol(s::String)` and
`Symbol(a::Vector{UInt8})` build the symbol with exactly the given bytes (for a vector,
the bytes visible through its reference), throw `ArgumentError` when a byte is `0x00`,
and `Symbol(s::Symbol)` is `s`. -/
def SymbolCtors : Prop :=
  (∀ b : List Nat, 0 ∉ b → symbolOfString b = .ok b) ∧
  (∀ b : List Nat, 0 ∈ b → ∃ msg, symbolOfString b = .error (.argument msg)) ∧
  (∀ (a : List Nat) (off len : Nat), symbolOfVector a off len = symbolOfString ((a.drop off).take len)) ∧
  (∀ s, symbolOfSymbol s = s)

theorem symbolCtors : SymbolCtors := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro b h
    simp [symbolOfString, symbolN, h]
  · intro b h
    exact ⟨"Symbol name may not contain \\0", by simp [symbolOfString, symbolN, h]⟩
  · intro a off len
    simp only [symbolOfVector, symbolOfString]
    rw [List.take_of_length_le (Nat.le_refl _)]

/-- The converting `Array` constructors (`base/boot.jl:849-854`) call the full constructor
with the element type and dimensionality the method signature fixes: the source element
type `S` for `Array{T,N} where T` and for `Array(A)` (with `T = S`), the requested `T` for
`Array{T}(A)` and `AbstractArray{T}(A)`, and always the source dimensionality `N`. -/
def ArrayConversions : Prop :=
  ∀ {A B : Type} (conv : String → Nat → A → B) (elt : String) (N : Nat) (x : A),
    arrayFromAbstract conv elt N x = conv elt N x ∧ arrayOf conv elt N x = conv elt N x ∧
    arrayTOf conv elt N x = conv elt N x ∧ abstractArrayTOf conv elt N x = conv elt N x

theorem arrayConversions : ArrayConversions := fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end JuliaLean.BootCov.Arrays

end

section

/-!
Properties of the macros and doc helpers of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov

/-- `Core.@_total_meta` and `Core.@_foldable_meta` (`base/boot.jl:331-361`) expand to the
purity expression only inside `Core` and to `false` in every other module; the `:total`
form asserts exactly the effects of `@assume_effects :total`. -/
def CoreEffectMetas : Prop :=
  (∀ m, coreIsInternal m = true ↔ m = "Core") ∧
  (∀ m f, m ≠ "Core" → effectMeta (coreIsInternal m) f = .bool false) ∧
  (∀ f, effectMeta (coreIsInternal "Core") f = .expr "meta" [.expr "purity" f.toList]) ∧
  coreTotalMeta = assumeEffects ["total"] ∧
  coreFoldableMeta = { assumeEffects ["foldable"] with notaskstate := true, inaccessiblememonly := true }

theorem coreEffectMetas : CoreEffectMetas := by
  refine ⟨?_, ?_, fun _ => rfl, by decide, by decide⟩
  · intro m; simp [coreIsInternal]
  · intro m f h; simp [effectMeta, coreIsInternal, h]

/-- The marker macros of `Core` (`base/boot.jl:324-367`) expand to the documented
expressions, and `Expr(head, args...)` (line 327) requires a `Symbol` head and at least one
argument. -/
def CoreMarkerMacros : Prop :=
  (∀ x, coreNospecialize x = .expr "escape" [.expr "meta" [.sym "nospecialize", x]]) ∧
  latestworld = .expr "latestworld" [] ∧ inlineMacro = .expr "meta" [.sym "inline"] ∧
  noinlineMacro = .expr "meta" [.sym "noinline"] ∧
  nospecializeinferMacro = .expr "meta" [.sym "nospecializeinfer"] ∧
  boundscheckMarker = .expr "boundscheck" [] ∧
  (∀ h args, exprCtor (.sym h :: args) = .ok (.expr h args)) ∧
  (∀ h args, (∀ s, h ≠ .sym s) → exprCtor (h :: args) = .error (.typeError "Expr")) ∧
  (∃ msg, exprCtor [] = .error (.argument msg))

theorem coreMarkerMacros : CoreMarkerMacros := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, ⟨_, rfl⟩⟩
  intro h args hh
  cases h with
  | sym s => exact absurd rfl (hh s)
  | _ => rfl

/-- The `Core` doc-system helpers (`base/boot.jl:941-960`): `isbasicdoc` accepts exactly
`a.b` expressions, `QuoteNode`s and `Symbol`s; `iscallexpr` sees through `where` to a
`:call` head; `ignoredoc` drops basic and call documentation targets and keeps every other
expression; `@doc` returns an `:escape` result of the hook unchanged and wraps any other
result in a hygienic scope; `@__doc__ x` marks `x` with `Expr(:meta, :doc)`; `atdoc!`
installs and returns the new hook. -/
def DocHelpers : Prop :=
  (∀ args, isbasicdoc (.expr "." args) = true) ∧
  (∀ v, isbasicdoc (.quoteNode v) = true) ∧ (∀ s, isbasicdoc (.sym s) = true) ∧
  (∀ n args, n ≠ "." → isbasicdoc (.expr n args) = false) ∧
  (∀ a args, firstarg a args = a) ∧
  (∀ args, iscallexpr (.expr "call" args) = .ok true) ∧
  (∀ a rest, iscallexpr (.expr "where" (a :: rest)) = iscallexpr a) ∧
  (∀ v, (∀ h args, v ≠ .expr h args) → iscallexpr v = .ok false) ∧
  (∀ e, isbasicdoc e = true → ignoredoc e = (iscallexpr e).map fun _ => .expr "escape" [.nothing]) ∧
  (∀ e, isbasicdoc e = false → iscallexpr e = .ok false → ignoredoc e = .ok (.expr "escape" [e])) ∧
  (∀ (atdoc : JVal → String → List JVal → JVal) src m x args,
    atdoc src m x = .expr "escape" args → docMacro atdoc src m x = .expr "escape" args) ∧
  (∀ (atdoc : JVal → String → List JVal → JVal) src m x,
    (∀ args, atdoc src m x ≠ .expr "escape" args) →
    docMacro atdoc src m x = .expr "escape" [.expr "hygienic-scope" [atdoc src m x, .module_ "Core", src]]) ∧
  (∀ x, docMarker x = .expr "escape" [.expr "block" [.expr "meta" [.sym "doc"], x]]) ∧
  (∀ {α : Type} (old new : α), atdocBang old new = (new, new))

theorem docHelpers : DocHelpers := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, fun _ _ => rfl⟩
  · intro n args hn
    simp only [isbasicdoc]
    split <;> simp_all
  · intro v hv
    cases v with
    | expr h args => exact absurd rfl (hv h args)
    | _ => rfl
  · intro e he
    cases h : iscallexpr e <;>
      simp [ignoredoc, he, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro e he hc
    simp [ignoredoc, he, hc, bind, Except.bind, pure, Except.pure]
  · intro atdoc src m x args h
    simp [docMacro, h]
  · intro atdoc src m x h
    simp only [docMacro]

end JuliaLean.BootCov.Macros

end

section

/-!
Properties of the remaining `base/boot.jl` and `base/essentials.jl` methods.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

theorem printN_append (io : CoreIO) (ss : PrintArg → List Nat) :
    ∀ (xs : List PrintArg) (s : Out),
      printN io ss xs s = emit io (xs.flatMap (printBytes ss)) s := by
  intro xs
  induction xs with
  | nil => intro s; cases io <;> simp [printN, emit]
  | cons x xs ih =>
    intro s
    rw [printN, ih]
    cases io <;> cases x <;>
      simp [print1, emit, printBytes, writeString, unsafeWrite, coreShow, List.append_assoc]

/-- The stand-alone `Core` printing (`base/boot.jl:970-1006`): `write` returns the number
of bytes and appends them; `print(io, xs...)` appends each argument's bytes in order
(characters and strings verbatim, other values through `jl_static_show`); `println`
appends a newline after them; output to one stream leaves the other unchanged; and the
one-argument forms print to `Core.stdout`. -/
def CorePrinting : Prop :=
  coreSTDOUT = .stdout ∧ coreSTDERR = .stderr ∧
  (∀ h, ioPointer h .stdout = h.1 ∧ ioPointer h .stderr = h.2) ∧
  (∀ io bs nb s, (unsafeWrite io bs nb s).1 = nb) ∧
  (∀ bs s, (writeString .stdout bs s) = (bs.length, { s with out := s.out ++ bs })) ∧
  (∀ x s, writeByte .stderr x s = (1, { s with err := s.err ++ [x] })) ∧
  (∀ ss xs s, printlnN .stdout ss xs s =
    { s with out := s.out ++ xs.flatMap (printBytes ss) ++ [10] }) ∧
  (∀ ss xs s, (printlnN .stderr ss xs s).out = s.out) ∧
  (∀ ss xs s, print0 ss xs s = printN .stdout ss xs s ∧
    printlnStdout ss xs s = printlnN .stdout ss xs s) ∧
  (∀ ss x s, show0 ss x s = { s with out := s.out ++ ss x })

theorem corePrinting : CorePrinting := by
  refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, ?_, fun _ _ => rfl, ?_, ?_,
    fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  · intro bs s; simp [writeString, unsafeWrite, emit]
  · intro ss xs s
    simp [printlnN, println0, writeByte, printN_append, emit, List.append_assoc]
  · intro ss xs s
    simp [printlnN, println0, writeByte, printN_append, emit]

/-- The `Core` conversions (`base/boot.jl:381-384`): `convert(Any, x)`, `convert(T, x::T)`
and `unsafe_convert(T, x::T)` return their argument, `Core.cconvert(T, x)` is
`convert(T, x)`; and `Union{}(a...)` and `kwcall(kw, Union{}, a...)` (lines 398-399)
throw `ArgumentError`. -/
def IdentityConversionsBoot : Prop :=
  (∀ {α : Type} (x : α), convertSame x = x ∧ unsafeConvertSame x = x) ∧
  (∀ {α β : Type} (f : α → β) x, coreCconvert f x = f x) ∧
  (∀ {α : Type} (a : List α), ∃ m, unionBottomCtor a = .error (.argument m)) ∧
  (∀ {α : Type} (k : α) (a : List α), kwcallUnionBottom k a = unionBottomCtor a)

theorem identityConversionsBoot : IdentityConversionsBoot :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => ⟨_, rfl⟩, fun _ _ => rfl⟩

/-- The `Core` hooks and shims (`base/boot.jl:1227-1281`): `struct_name_shim` returns the
type under construction exactly when `x === mod` and otherwise reads `getfield(x, name)`;
each `_set...!` installs its hook, returns it and leaves the other hooks alone; and
`_hasmethod(tt)` is true exactly when method lookup in the current world finds a method. -/
def CoreHooks : Prop :=
  (∀ {α : Type} (gf : α → String → R α) x n t, structNameShim gf true x n t = .ok t) ∧
  (∀ {α : Type} (gf : α → String → R α) x n t, structNameShim gf false x n t = gf x n) ∧
  (∀ {α : Type} (h : Hooks α) p, setparser h p = (p, ⟨p, h.lower, h.toplevelEval⟩)) ∧
  (∀ {α : Type} (h : Hooks α) l, setlowerer h l = (l, ⟨h.parse, l, h.toplevelEval⟩)) ∧
  (∀ {α : Type} (h : Hooks α) f, setToplevelEval h f = (f, ⟨h.parse, h.lower, f⟩)) ∧
  (∀ {τ μ : Type} (lookup : τ → Nat → Option μ) w tt,
    hasmethod lookup w tt = true ↔ ∃ m, lookup tt w = some m)

theorem coreHooks : CoreHooks := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, ?_⟩
  · intro τ μ lookup w tt
    simp only [hasmethod]
    cases lookup tt w <;> simp

end JuliaLean.BootCov.Misc

end

namespace JuliaLean.Proofs.base.boot

open JuliaLean.Registry

open JuliaLean.BootCov in
open JuliaLean.Registry in
def entries : List Entry := [
  { id := "bootcov-boot-int-ctors", juliaFile := "base/boot.jl"
    juliaFns := ["toInt8..toUInt128 (110 methods)", "Int8(::BuiltinInts)..UInt128(::BuiltinInts)"]
    statement := "Every Core integer constructor T(x) for a built-in integer or Bool x returns x itself when x is representable in T and otherwise throws InexactError for T."
    source := "convert docstring (base/essentials.jl:428-430); base/boot.jl:1071-1193", status := .proven
    prop := ``IntConv.CtorExact, thm := some ``IntConv.ctorExact },
  { id := "bootcov-boot-int-helpers", juliaFile := "base/boot.jl"
    juliaFns := ["is_top_bit_set", "throw_inexacterror", "check_sign_bit", "checked_trunc_sint", "checked_trunc_uint"]
    statement := "is_top_bit_set tests the signed sign bit; check_sign_bit returns x unless its top bit is set, then throws InexactError for To; the checked truncations succeed exactly when the value survives the round trip through the narrower type."
    source := "base/boot.jl:1037-1069", status := .proven
    prop := ``IntConv.HelperSemantics, thm := some ``IntConv.helperSemantics },
  { id := "bootcov-signbit-func-name", juliaFile := "base/boot.jl"
    juliaFns := ["check_sign_bit", "toUInt16(::Int8)", "toUInt32(::Int8/::Int16)", "toUInt64(::Int8/::Int16/::Int32)", "toUInt128(::Int8..::Int64)"]
    statement := "A failing integer conversion that does not narrow the bit width reports convert, not trunc, as the failing function."
    source := "base/boot.jl:1049-1051 (check_sign_bit comment: if x is signed then bitsizeof(x) === bitsizeof(To))", status := .refuted
    prop := ``IntConv.WideningErrorNamesConvert, thm := some ``IntConv.wideningErrorNamesConvert_refuted
    issue := "none found (queries: InexactError trunc UInt16 Int8, check_sign_bit, InexactError trunc convert widening, InexactError: trunc negative unsigned, InexactError trunc message misleading, InexactError says trunc, bitsizeof check_top_bit, InexactError convert vs trunc)"
    notes := "UInt16(Int8(-1)) throws InexactError(:trunc, UInt16, -1) while UInt16(Int16(-1)) throws InexactError(:convert, ...). Same on 1.13.2." },
  { id := "bootcov-boot-signed-unsigned", juliaFile := "base/boot.jl"
    juliaFns := ["Signed(::UInt8..::UInt128)", "Unsigned(::Int8..::Int128)"]
    statement := "Signed(x) and Unsigned(x) of a fixed-width integer convert exactly to the same-width signed or unsigned type."
    source := "base/boot.jl:1206-1215; convert docstring", status := .proven
    prop := ``IntConv.SignedUnsignedExact, thm := some ``IntConv.signedUnsignedExact },
  { id := "bootcov-boot-ptr-casts", juliaFile := "base/boot.jl"
    juliaFns := ["(::Type{T})(x::T)", "Int(::Ptr)", "UInt(::Ptr)", "Ptr{T}(x)", "AddrSpace(::UInt8)", "Signed(::Float/Bool)", "Unsigned(::Float/Bool)", "Integer(::Integer)", "Integer(::Float)"]
    statement := "Pointer casts are bit casts that round-trip addresses, Ptr{T}() is null, T(x::T) and Integer(x::Integer) return x, and the float/Bool forms of Signed, Unsigned and Integer delegate to Int(x) or UInt(x)."
    source := "base/boot.jl:1195-1221", status := .proven
    prop := ``IntConv.PtrCastsRoundTrip, thm := some ``IntConv.ptrCastsRoundTrip },
  { id := "bootcov-boot-exceptions", juliaFile := "base/boot.jl"
    juliaFns := ["ErrorException", "BoundsError (3 methods)", "DivideError", "OutOfMemoryError", "ReadOnlyMemoryError", "SegmentationFault", "StackOverflowError", "UndefRefError", "UndefVarError (2)", "ConcurrencyViolationError", "MissingCodeError", "InterruptException", "DomainError (2)", "TypeError (2)", "InexactError", "OverflowError", "ArgumentError", "UndefKeywordError", "MethodError (2)", "AssertionError (2)", "FieldError", "LoadError", "InitError", "ABIOverride", "PrecompilableError", "TrimFailure", "PossiblyAmbiguous", "UndefInitializer", "CoreSTDOUT", "CoreSTDERR", "TypeNameError"]
    statement := "Exception and singleton constructors store their arguments in field order, leave omitted fields undefined, convert typed fields (MethodError when impossible) and fill the documented defaults."
    source := "base/boot.jl:470-606, 696, 757, 974-977, 1307", status := .proven
    prop := ``Objects.ExceptionFields, thm := some ``Objects.exceptionFields },
  { id := "bootcov-boot-wrappers", juliaFile := "base/boot.jl"
    juliaFns := ["String(::String)", "Nothing()", "EvalInto", "Box (2)", "WeakRef (2)", "Tuple{}()", "VecElement{T}", "VecElement", "Const", "_PartialStruct", "InterConditional", "InterMustAlias", "PartialOpaque", "PartialTask", "GeneratedFunctionStub", "Pair(a, b)", "MacroSource"]
    statement := "Wrapper and lattice-element constructors store their arguments, Box() leaves its field undefined, WeakRef() refers to nothing, and VecElement(x) is VecElement{typeof(x)}(x)."
    source := "base/boot.jl:611-696, 1012, 1269, 1335", status := .proven
    prop := ``Objects.WrapperFields, thm := some ``Objects.wrapperFields },
  { id := "bootcov-boot-ir-nodes", juliaFile := "base/boot.jl"
    juliaFns := ["GotoNode", "NewvarNode", "QuoteNode", "SSAValue", "Argument", "ReturnNode (2)", "GotoIfNot", "EnterNode (3)", "LineNumberNode (2)", "DebugInfo (2)", "SlotNumber", "PhiNode", "PiNode", "PhiCNode", "UpsilonNode (2)", "MethodMatch", "LineInfoNode"]
    statement := "IR node constructors store their arguments; LineNumberNode(l, f) turns a String file into a Symbol and rejects other non-Symbol files; EnterNode(old, d) keeps old.scope exactly when it is defined."
    source := "base/boot.jl:699-736, 1292-1293", status := .proven
    prop := ``Objects.IRNodeFields, thm := some ``Objects.irNodeFields },
  { id := "bootcov-boot-named-tuples", juliaFile := "base/boot.jl"
    juliaFns := ["NamedTuple()", "NamedTuple{names}(::Tuple)", "NamedTuple{names,T}(::T)"]
    statement := "NamedTuple constructors pair the names with the arguments in order; NamedTuple{names}(args) throws exactly when the counts differ; NamedTuple() is empty."
    source := "base/boot.jl:1022-1030", status := .proven
    prop := ``Objects.NamedTupleCtors, thm := some ``Objects.namedTupleCtors },
  { id := "bootcov-boot-handles", juliaFile := "base/boot.jl"
    juliaFns := ["getptls", "include", "eval", "(::EvalInto)(e)", "CodeInstance", "GlobalRef", "Module"]
    statement := "The runtime-handle constructors and Core.eval/include pass their arguments to the runtime in order; Module() defaults to :anonymous with standard imports and default names."
    source := "base/boot.jl:617-626, 740-751", status := .proven
    prop := ``Objects.HandleCtors, thm := some ``Objects.handleCtors },
  { id := "bootcov-boot-typeof", juliaFile := "base/boot.jl"
    juliaFns := ["(::typeof(Typeof))(x)", "(::typeof(TypeEqOf))(x)", "_typeof_captured_variable"]
    statement := "Typeof(x) is Type{x} for types with free typevars, TypeEgal{x} for other types and typeof(x) otherwise; TypeEqOf(x) is Type{x} for every type; _typeof_captured_variable picks typeof for types with free typevars."
    source := "base/boot.jl:296-319, 387", status := .proven
    prop := ``Types.TypeofKinds, thm := some ``Types.typeofKinds
    notes := "1.13.2 Typeof returns Type{x} for all types and has no TypeEqOf." },
  { id := "bootcov-boot-typevar-unionall", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar (3 methods)", "UnionAll(v, t)"]
    statement := "TypeVar builds a fresh typevar with default bounds Union{} and Any, rejecting non-Symbol names and non-type bounds; UnionAll(v, t) requires a TypeVar, returns v.ub for t === v, returns t when v does not occur in it, and otherwise wraps t."
    source := "base/boot.jl:370-373; src/jltypes.c:1054-1099, 2216-2229", status := .proven
    prop := ``Types.TypeVarUnionAll, thm := some ``Types.typeVarUnionAll },
  { id := "bootcov-boot-typename", juliaFile := "base/boot.jl"
    juliaFns := ["typename (4 methods)"]
    statement := "typename sees through where, returns the shared name of a Union whose members agree, and throws TypeNameError for other values including Union{}."
    source := "base/boot.jl:1310-1318", status := .proven
    prop := ``Types.TypenameBehaviour, thm := some ``Types.typenameBehaviour },
  { id := "bootcov-boot-typeapp", juliaFile := "base/boot.jl"
    juliaFns := ["TypeApp", "_contains_typeapp", "apply_type_or_typeapp", "resolve_typegroup"]
    statement := "apply_type_or_typeapp builds the left-nested TypeApp chain when the head is a TypeVar or TypeApp or a parameter contains a TypeApp, and calls apply_type otherwise; an empty typegroup resolves to ()."
    source := "base/boot.jl:403-467", status := .proven
    prop := ``Types.TypeAppBehaviour, thm := some ``Types.typeAppBehaviour
    notes := "Master only; absent in 1.13.2." },
  { id := "bootcov-boot-operators", juliaFile := "base/boot.jl"
    juliaFns := [">:", "!=="]
    statement := "(>:)(a, b) is b <: a and (!==)(a, b) is !(a === b)."
    source := "base/boot.jl:1322-1323", status := .proven
    prop := ``Types.BootOperators, thm := some ``Types.bootOperators },
  { id := "bootcov-boot-memory", juliaFile := "base/boot.jl"
    juliaFns := ["GenericMemory{kind,T,addrspace}(undef, m)", "GenericMemory{...}(undef, (m,))", "GenericMemory{...}()"]
    statement := "Memory(undef, m) allocates exactly m undefined slots when 0 <= m <= the runtime limit and throws ArgumentError otherwise; the tuple and empty forms agree."
    source := "base/boot.jl:762-765; src/genericmemory.c:55-73", status := .proven
    prop := ``Arrays.MemoryCtorCorrect, thm := some ``Arrays.memoryCtorCorrect },
  { id := "bootcov-boot-memoryref", juliaFile := "base/boot.jl"
    juliaFns := ["memoryref (3 methods)", "GenericMemoryRef (3 methods)"]
    statement := "memoryref(mem, i) refers to slot i exactly when 1 <= i <= length(mem) and throws BoundsError otherwise; memoryref(ref, i) shifts by i - 1, negative shifts included, throwing BoundsError exactly when the target leaves the memory."
    source := "memoryref docstring (base/genericmemory.jl); base/boot.jl:768-773; src/builtins.c (jl_f_memoryrefnew)", status := .proven
    prop := ``Arrays.MemoryrefCorrect, thm := some ``Arrays.memoryrefCorrect },
  { id := "bootcov-boot-checked-dims", juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims (4 methods)", "checked_dims (3 methods)"]
    statement := "checked_dims with two or more dimensions throws ArgumentError or returns the exact product of dimensions that are all nonnegative and below typemax(Int); checked_dims() is 1 and checked_dims(m) is m."
    source := "invariant; base/boot.jl:781-818", status := .proven
    prop := ``Arrays.CheckedDimsSound, thm := some ``Arrays.checkedDimsSound
    notes := "Rejecting a typemax(Int) dimension even when the product fits is reported as reinterpretarrays-reshape-typemax-dim." },
  { id := "bootcov-boot-array-ctors", juliaFile := "base/boot.jl"
    juliaFns := ["Array{T,1/2/3/N}(undef, dims...)", "Array{T,N}(undef, ::NTuple)", "Array{T}(undef, ...)", "Vector{T}()", "new_as_memoryref"]
    statement := "Every Array(undef, dims...) constructor throws ArgumentError or builds an array with exactly the requested dimensions whose memory length is the product of the dimensions."
    source := "Array docstring (base/docs/basedocs.jl); base/boot.jl:779-847", status := .proven
    prop := ``Arrays.ArrayCtorShape, thm := some ``Arrays.arrayCtorShape },
  { id := "bootcov-boot-array-conversions", juliaFile := "base/boot.jl"
    juliaFns := ["(Array{T,N} where T)(::AbstractArray)", "Array(::AbstractArray)", "Array{T}(::AbstractArray)", "AbstractArray{T}(::AbstractArray)"]
    statement := "The converting Array constructors call the full constructor with the element type fixed by the signature and the source dimensionality."
    source := "base/boot.jl:849-854", status := .proven
    prop := ``Arrays.ArrayConversions, thm := some ``Arrays.arrayConversions },
  { id := "bootcov-boot-symbol", juliaFile := "base/boot.jl"
    juliaFns := ["_Symbol", "Symbol(::String)", "Symbol(::Vector{UInt8})", "Symbol(::Symbol)"]
    statement := "Symbol(s) builds the symbol with exactly the bytes of s (for a vector, those visible through its reference), throws ArgumentError for a NUL byte, and Symbol(::Symbol) is the identity."
    source := "Symbol docstring; base/boot.jl:858-873; src/symbol.c:114-119", status := .proven
    prop := ``Arrays.SymbolCtors, thm := some ``Arrays.symbolCtors },
  { id := "bootcov-boot-markers", juliaFile := "base/boot.jl"
    juliaFns := ["@nospecialize(x)", "Expr(args...)", "@latestworld", "@inline", "@noinline", "@nospecializeinfer", "@_boundscheck"]
    statement := "The Core marker macros expand to their meta expressions, and Expr(head, args...) requires a Symbol head and at least one argument."
    source := "base/boot.jl:324-367", status := .proven
    prop := ``Macros.CoreMarkerMacros, thm := some ``Macros.coreMarkerMacros },
  { id := "bootcov-boot-effect-metas", juliaFile := "base/boot.jl"
    juliaFns := ["_is_internal", "@_total_meta", "@_foldable_meta"]
    statement := "Core.@_total_meta and Core.@_foldable_meta expand to their purity expression only inside Core and to false elsewhere; the :total form asserts exactly the @assume_effects :total effects."
    source := "base/boot.jl:331-361; base/expr.jl:1019-1030", status := .proven
    prop := ``Macros.CoreEffectMetas, thm := some ``Macros.coreEffectMetas
    notes := "Core.@_foldable_meta also asserts notaskstate and inaccessiblememonly; see bootcov-foldable-meta-effects." },
  { id := "bootcov-boot-doc", juliaFile := "base/boot.jl"
    juliaFns := ["@doc", "@__doc__", "isbasicdoc", "firstarg", "iscallexpr (2)", "ignoredoc", "atdoc!"]
    statement := "The Core doc helpers drop basic and call documentation targets and keep other expressions, @doc passes :escape results through and wraps others in a hygienic scope, and atdoc! installs the hook."
    source := "base/boot.jl:940-960", status := .proven
    prop := ``Macros.DocHelpers, thm := some ``Macros.docHelpers },
  { id := "bootcov-boot-printing", juliaFile := "base/boot.jl"
    juliaFns := ["CoreSTDOUT", "CoreSTDERR", "io_pointer (2)", "unsafe_write (2)", "write (2)", "show (2)", "print (5)", "println (3)"]
    statement := "Core printing appends each argument's bytes in order to the chosen stream (strings and chars verbatim, others via jl_static_show), println adds a newline, write returns the byte count, and the other stream is untouched."
    source := "base/boot.jl:970-1006", status := .proven
    prop := ``Misc.CorePrinting, thm := some ``Misc.corePrinting },
  { id := "bootcov-boot-identity", juliaFile := "base/boot.jl"
    juliaFns := ["convert(::Type{Any}, x)", "convert(::Type{T}, x::T)", "cconvert(::Type{T}, x)", "unsafe_convert(::Type{T}, x::T)", "Union{}(a...)", "kwcall(kw, ::Type{Union{}}, a...)"]
    statement := "The Core identity conversions return their argument, Core.cconvert is convert, and constructing Union{} throws ArgumentError."
    source := "base/boot.jl:377-399", status := .proven
    prop := ``Misc.IdentityConversionsBoot, thm := some ``Misc.identityConversionsBoot },
  { id := "bootcov-boot-hooks", juliaFile := "base/boot.jl"
    juliaFns := ["struct_name_shim", "_setparser!", "_setlowerer!", "_set_toplevel_eval!", "_hasmethod"]
    statement := "struct_name_shim returns the type under construction exactly for x === mod; each _set...! installs and returns its hook only; _hasmethod is true exactly when lookup finds a method."
    source := "base/boot.jl:1227-1281", status := .proven
    prop := ``Misc.CoreHooks, thm := some ``Misc.coreHooks },
]

end JuliaLean.Proofs.base.boot



namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot
open JuliaLean.Registry

/-- Identity conversion cannot collapse distinct represented values, and applying it
again cannot change its result. These algebraic invariants are independent of the
implementation's return expression. The domain includes every represented value,
including opaque object handles, with no assumption about an observation or callee.
Julia source: base/boot.jl:381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: doc/src/manual/conversion-and-promotion.md:131-135.
-/
def ConvertAnyLossless : Prop :=
  ∀ (L : Type) (x y : Value L),
    (convert_Any x = convert_Any y ↔ x = y) ∧
    convert_Any (convert_Any x) = convert_Any x

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem convertAnyLossless_proven : ConvertAnyLossless := by
  intro L x y
  exact ⟨Iff.rfl, rfl⟩
end

/-- The already-dispatched same-type identity conversion is injective and
idempotent on its complete represented argument domain. The type constraint is
the selected source method's signature; it is not an added numeric specialization.
Julia source: base/boot.jl:382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: doc/src/manual/conversion-and-promotion.md:131-135.
-/
def ConvertSameLossless : Prop :=
  ∀ (L : Type) (x y : Value L),
    (convert_T x = convert_T y ↔ x = y) ∧
    convert_T (convert_T x) = convert_T x

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem convertSameLossless_proven : ConvertSameLossless := by
  intro L x y
  exact ⟨Iff.rfl, rfl⟩
end

/-- The already-dispatched same-type unsafe conversion loses no represented
value distinctions, and repeating it does not change the result. This states a
same-type identity-method invariant, not a contract for other unsafe conversions.
Julia source: base/boot.jl:384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: doc/src/manual/calling-c-and-fortran-code.md:245-275.
-/
def UnsafeConvertSameLossless : Prop :=
  ∀ (L : Type) (x y : Value L),
    (unsafe_convert x = unsafe_convert y ↔ x = y) ∧
    unsafe_convert (unsafe_convert x) = unsafe_convert x

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem unsafeConvertSameLossless_proven : UnsafeConvertSameLossless := by
  intro L x y
  exact ⟨Iff.rfl, rfl⟩
end

/-- A specification-only observation of one dispatched call. The event list is
a mathematical ghost trace, not a Julia tuple or machine-sized container. -/
abbrev Invocation (L : Type) := Value L × List (Value L)

/-- Add a ghost event around an arbitrary dispatch-selected operation. The
underlying operation may return any value, throw any Julia value, mutate its
world arbitrarily, or diverge; no correctness law is imposed on it. The trace is
kept outside that world so the callee cannot erase the observation. This is test
instrumentation for a specification, not a new Julia primitive or model callee.
-/
def recordCall {W L : Type}
    (dispatch : Value L → List (Value L) → CoreM W L (Value L))
    (fn : Value L) (args : List (Value L)) :
    CoreM (W × List (Invocation L)) L (Value L) :=
  fun (world, trace) =>
    match dispatch fn args world with
    | none => none
    | some (.ok (result, world')) =>
        some (.ok (result, (world', trace ++ [(fn, args)])))
    | some (.error (exception, world')) =>
        some (.error (exception, (world', trace ++ [(fn, args)])))

/-- The independent observer compares termination, success/error class, returned
or thrown value, final world, and the number, target and argument order of calls.
It does not call a model or constrain the dispatch implementation. -/
def OneCallObservation {W L : Type}
    (trace : List (Invocation L)) (event : Invocation L)
    (untraced : Option (Except (Value L × W) (Value L × W)))
    (traced : Option (Except
      (Value L × (W × List (Invocation L)))
      (Value L × (W × List (Invocation L))))) : Prop :=
  match untraced, traced with
  | none, none => True
  | some (.ok (value, world)), some (.ok (value', (world', trace'))) =>
      value' = value ∧ world' = world ∧ trace' = trace ++ [event]
  | some (.error (exception, world)), some (.error (exception', (world', trace'))) =>
      exception' = exception ∧ world' = world ∧ trace' = trace ++ [event]
  | _, _ => False

/-- The generic cconvert fallback forwards exactly one dispatch-selected convert
call, with the target type before the original value, and preserves every possible
callee outcome and world effect. This observation detects extra calls, reversed or
changed arguments, caught/replaced errors, changed results, and discarded mutations.
All operations and argument values are quantified without a callee-correctness law.
Only the generic call boundary is instrumented; the complete existing cconvert
method is executed. The trace is ghost specification state, not a Julia allocation.
Julia source: base/boot.jl:383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: doc/src/manual/calling-c-and-fortran-code.md:245-271.
-/
def CConvertSingleDispatch : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (Invocation L)) L)
    (dispatch : Value L → List (Value L) → CoreM W L (Value L))
    (target x : Value L) (world : W) (trace : List (Invocation L)),
    let instrumented := { ops with call := recordCall dispatch }
    OneCallObservation trace (coreV ops "convert", [target, x])
      (dispatch (coreV ops "convert") [target, x] world)
      (cconvert instrumented target x (world, trace))

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem cConvertSingleDispatch_proven : CConvertSingleDispatch := by
  intro W L ops dispatch target x world trace
  change OneCallObservation trace (coreV ops "convert", [target, x])
    (dispatch (coreV ops "convert") [target, x] world)
    (recordCall dispatch (coreV ops "convert") [target, x] (world, trace))
  unfold recordCall
  cases h : dispatch (coreV ops "convert") [target, x] world with
  | none => simp [h, OneCallObservation]
  | some outcome =>
    cases outcome with
    | error error => rcases error with ⟨error, after⟩; simp [h, OneCallObservation]
    | ok result => rcases result with ⟨value, after⟩; simp [h, OneCallObservation]
end

/-- Every function uses the same internal keyword-dispatch token. Stated as a
singleton-range invariant, this fixes which token is returned as well as its
independence of the supplied value; an arbitrary constant function would not
satisfy it. There is no invocation of the token or a type-reflection callback.
Julia source: base/boot.jl:389-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
(the source explicitly identifies kwcall as the keyword-sorter dispatch token).
-/
def KeywordDispatchTokenInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (x candidate : Value L),
    kwfunc ops x = candidate ↔ candidate = coreV ops "kwcall"

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem keywordDispatchTokenInvariant_proven : KeywordDispatchTokenInvariant := by
  intro W L ops x candidate
  exact eq_comm
end

/-- Entries to concatenate into the parent namespace's entriesModels2Group1. -/
def entriesEarlyConversions : List Entry := [
  { id := "boot-convert-any-lossless"
    juliaFile := "base/boot.jl"
    juliaFns := ["convert(::Type{Any}, @nospecialize(x))"]
    statement := "Core's Any identity conversion is injective and idempotent over every represented argument value."
    source := "base/boot.jl:381; doc/src/manual/conversion-and-promotion.md:131-135 (identity conversion)"
    status := .proven
    prop := ``ConvertAnyLossless
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.convertAnyLossless_proven
    notes := "Reuses JuliaLean.base.boot.convert_Any. No proofs or canonical definitions are changed." },
  { id := "boot-convert-same-lossless"
    juliaFile := "base/boot.jl"
    juliaFns := ["convert(::Type{T}, x::T) where {T}"]
    statement := "Core's already-dispatched same-type identity conversion is injective and idempotent over its complete represented argument domain."
    source := "base/boot.jl:382; doc/src/manual/conversion-and-promotion.md:131-135 (identity conversion)"
    status := .proven
    prop := ``ConvertSameLossless
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.convertSameLossless_proven
    notes := "Reuses JuliaLean.base.boot.convert_T. The source signature's same-type dispatch is represented by the selected entry point." },
  { id := "boot-cconvert-single-dispatch"
    juliaFile := "base/boot.jl"
    juliaFns := ["cconvert(::Type{T}, x) where {T}"]
    statement := "The generic cconvert fallback forwards one convert call with unchanged target and value, and preserves arbitrary success, exception, divergence and world effects."
    source := "base/boot.jl:383; doc/src/manual/calling-c-and-fortran-code.md:245-271 (automatic type conversion)"
    status := .proven
    prop := ``CConvertSingleDispatch
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.cConvertSingleDispatch_proven
    notes := "Reuses JuliaLean.base.boot.cconvert. Quantifies arbitrary dispatch with no correctness laws; recordCall and OneCallObservation are independent ghost observations, not model dependencies." },
  { id := "boot-unsafe-convert-same-lossless"
    juliaFile := "base/boot.jl"
    juliaFns := ["unsafe_convert(::Type{T}, x::T) where {T}"]
    statement := "Core's already-dispatched same-type unsafe conversion is injective and idempotent over its complete represented argument domain."
    source := "base/boot.jl:384; invariant of the same-type identity method; doc/src/manual/calling-c-and-fortran-code.md:245-275"
    status := .proven
    prop := ``UnsafeConvertSameLossless
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.unsafeConvertSameLossless_proven
    notes := "Reuses JuliaLean.base.boot.unsafe_convert; no assertion is made about other unsafe_convert methods." },
  { id := "boot-keyword-dispatch-token"
    juliaFile := "base/boot.jl"
    juliaFns := ["kwfunc(@nospecialize(f))"]
    statement := "The internal kwfunc result has the singleton range containing Core.kwcall, independently of its supplied value."
    source := "base/boot.jl:389-392 (keyword-sorter dispatch-token invariant)"
    status := .proven
    prop := ``KeywordDispatchTokenInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.keywordDispatchTokenInvariant_proven
    notes := "Reuses JuliaLean.base.boot.kwfunc; the core field names an existing constant value. Does not claim coverage for kwftype or for keyword dispatch itself." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean
open JuliaLean.Registry

-- Namespace aliases only: these export the existing model names, not new models.
namespace M
export JuliaLean.base.boot.Models2Group1
  (Value Heap ExprCell VectorAny SymbolName symbolName MacroM readExpr readArgs
   allocExpr nospecializeMacro latestworldMacro isInternal totalMetaMacro
   foldableMetaMacro inlineMacro noinlineMacro nospecializeinferMacro boundscheckMacro)
end M

/-!
Specification observers for the finite heap graph. They do not prescribe the
numeric identity chosen for a new object or construct an expected heap by
appending cells. References are logical names in separate Expr/vector spaces.
The heap tables are ghost descriptions of the object graph, not Julia arrays.
-/

/-- Julia Symbol names have no embedded NUL and have a native-sized byte length.
Arbitrary non-UTF-8 byte names are allowed. The bound is a representation
invariant, not an additional precondition on the fixed source literals.
Source context: base/boot.jl:324-367; base/docs/basedocs.jl:2563-2564.
-/
def ValidSymbolName (name : M.SymbolName) : Prop :=
  name.length ≤ IntTy.i64.max.toNat ∧ ∀ byte ∈ name, byte ≠ (0 : UInt8)

/-- A represented value is well-formed when its tracked references name existing
objects of the appropriate kind. This is deliberately nonrecursive: cyclic and
shared graphs are allowed. Opaque values are never inspected by these methods.
-/
def ValidValue {L : Type} (heap : M.Heap L) : M.Value L → Prop
  | .other _ => True
  | .coreModule => True
  | .bool _ => True
  | .symbol name => ValidSymbolName name
  | .exprRef ref => ref < heap.expressions.length
  | .argsRef ref => ref < heap.argsVectors.length

/-- An existing Expr may have either field undefined. Defined fields have the
actual concrete field types: Symbol and a reference to a Vector{Any}.
Source: base/docs/basedocs.jl:712-719.
-/
def ValidExprCell {L : Type} (heap : M.Heap L) (cell : M.ExprCell) : Prop :=
  (∀ head, cell.head = some head → ValidSymbolName head) ∧
  (∀ ref, cell.args = some ref → ref < heap.argsVectors.length)

/-- Every defined slot is a valid value; undefined slots remain allowed. Each
VectorAny already carries its native-Int length invariant in its type. These
local closure checks permit cycles, shared vectors and shared Expr references.
-/
def ValidHeap {L : Type} (heap : M.Heap L) : Prop :=
  (∀ cell ∈ heap.expressions, ValidExprCell heap cell) ∧
  (∀ vector ∈ heap.argsVectors, ∀ slot ∈ vector.data,
    ∀ value, slot = some value → ValidValue heap value)

/-- Every object that was present before a macro is observed with exactly the
same fields or slots afterwards. This includes undefined fields and sharing.
No list-prefix representation or allocation index is assumed here.
-/
def PreservesOldHeap {L : Type} (before after : M.Heap L) : Prop :=
  (∀ ref cell, M.readExpr before ref = some cell →
    M.readExpr after ref = some cell) ∧
  (∀ ref vector, M.readArgs before ref = some vector →
    M.readArgs after ref = some vector)

/-- Count new semantic objects of each concrete kind, without fixing which
logical names they receive or any physical runtime allocation order.
-/
def AllocationCount {L : Type} (before after : M.Heap L) (count : Nat) : Prop :=
  after.expressions.length = before.expressions.length + count ∧
  after.argsVectors.length = before.argsVectors.length + count

/-- A result node and its argument container are both fresh, have the intended
field values, and have the specified arity. Freshness is observed as absence in
the old graph, not as equality to an allocator's chosen list length.
-/
def FreshExprNode {L : Type} (before after : M.Heap L)
    (exprRef argsRef : Nat) (head : M.SymbolName) (arity : Nat) : Prop :=
  M.readExpr before exprRef = none ∧ M.readArgs before argsRef = none ∧
  ∃ (cell : M.ExprCell) (vector : M.VectorAny L),
    M.readExpr after exprRef = some cell ∧
    M.readArgs after argsRef = some vector ∧
    cell.head = some head ∧ cell.args = some argsRef ∧
    vector.data.length = arity

/-- Read a defined argument slot in an observed heap. The zero-based index is a
mathematical observation of the model list; it is not a Julia indexing operation.
Equality of stored values retains their exact tagged references.
-/
def HasSlot {L : Type} (heap : M.Heap L)
    (argsRef index : Nat) (value : M.Value L) : Prop :=
  ∃ vector, M.readArgs heap argsRef = some vector ∧
    vector.data[index]? = some (some value)

/-- The observation of one fresh, fully initialized expression. The contract
retains every old object, requires closure of the resulting graph, and checks
each stored value by indexing rather than duplicating the allocator's body.
-/
def FreshAllocation {L : Type} (before after : M.Heap L)
    (result : M.Value L) (head : M.SymbolName) (arguments : List (M.Value L)) : Prop :=
  ValidHeap after ∧ PreservesOldHeap before after ∧ AllocationCount before after 1 ∧
  ∃ exprRef argsRef,
    result = .exprRef exprRef ∧
    FreshExprNode before after exprRef argsRef head arguments.length ∧
    ∀ index value, arguments[index]? = some value → HasSlot after argsRef index value

/-- The necessary concrete allocation dependency preserves arbitrary valid
cyclic/shared heaps and argument identities while creating a fresh Expr and
fresh, initialized argument vector. All valid Symbol heads and constructible
native-sized argument tuples are included; there is no successful-result premise.
This is deliberately only the valid-head dependency, not coverage of unrestricted
Expr(args...) or its invalid/missing-head error behavior.
Source: base/boot.jl:327; base/docs/basedocs.jl:712-719
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def AllocExprHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L) (head : M.SymbolName)
    (arguments : List (M.Value L))
    (size_ok : arguments.length ≤ IntTy.i64.max.toNat),
    ValidHeap heap → ValidSymbolName head →
    (∀ value ∈ arguments, ValidValue heap value) →
    let observed := M.allocExpr head arguments size_ok heap
    FreshAllocation heap observed.2 observed.1 head arguments

/-- Nospecialize adds two separate fresh syntax nodes with separate fresh
argument vectors, preserves the entire old graph, and stores the original x
itself in the inner node. In particular x may refer to an existing cyclic or
shared graph; it is not copied or recursively rewritten.
Source: base/boot.jl:324-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def NospecializeHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L) (x : M.Value L),
    ValidHeap heap → ValidValue heap x →
    let observed := M.nospecializeMacro x heap
    ValidHeap observed.2 ∧ PreservesOldHeap heap observed.2 ∧
    AllocationCount heap observed.2 2 ∧
    ∃ outer outerArgs inner innerArgs,
      observed.1 = .exprRef outer ∧ outer ≠ inner ∧ outerArgs ≠ innerArgs ∧
      FreshExprNode heap observed.2 outer outerArgs (M.symbolName "escape") 1 ∧
      FreshExprNode heap observed.2 inner innerArgs (M.symbolName "meta") 2 ∧
      HasSlot observed.2 outerArgs 0 (.exprRef inner) ∧
      HasSlot observed.2 innerArgs 0 (.symbol (M.symbolName "nospecialize")) ∧
      HasSlot observed.2 innerArgs 1 x

/-- Latestworld allocates one fresh, empty marker and leaves all previous
objects unchanged. Source: base/boot.jl:329
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def LatestworldHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L), ValidHeap heap →
    let observed := M.latestworldMacro heap
    FreshAllocation heap observed.2 observed.1 (M.symbolName "latestworld") []

/-- Core's actual module identity is the sole accepted value. An unrelated
module with the same printed name, represented as other, remains outside Core.
This property uses value identity, not a supplied equality-correctness law.
Source: base/boot.jl:331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def InternalModuleIdentityInvariant : Prop :=
  ∀ (L : Type) (value : M.Value L),
    M.isInternal value = true ↔ value = .coreModule

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem internalModuleIdentityInvariant_proven : InternalModuleIdentityInvariant := by
  intro L value
  cases value <;> simp [M.isInternal]
end

/-- Named components of the independent EffectsOverride representation.
Source: base/expr.jl:948-960; the boot macros use this ordering.
-/
inductive Effect where
  | consistent
  | effectFree
  | nothrow
  | terminatesGlobally
  | terminatesLocally
  | notaskstate
  | inaccessiblememonly
  | noub
  | noubIfNoinbounds
  | consistentOverlay
  | nortcall
  deriving DecidableEq

/-- Zero-based observation positions of named EffectsOverride fields;
base/expr.jl:948-960, independently of either boot macro implementation.
-/
def effectPosition : Effect → Nat
  | .consistent => 0
  | .effectFree => 1
  | .nothrow => 2
  | .terminatesGlobally => 3
  | .terminatesLocally => 4
  | .notaskstate => 5
  | .inaccessiblememonly => 6
  | .noub => 7
  | .noubIfNoinbounds => 8
  | .consistentOverlay => 9
  | .nortcall => 10

inductive PurityFlavor where
  | total
  | foldable
  deriving DecidableEq

/-- The boot purity annotations do not set the local-only termination,
conditional-no-UB or overlay fields. Both carry the task/memory invariants;
only total promises nothrow. This logical predicate names the advertised
effects instead of repeating either implementation's eleven-element Bool list.
Sources: base/boot.jl:333-361; base/expr.jl:816-833,848-861.
-/
def EffectEnabled (flavor : PurityFlavor) (effect : Effect) : Prop :=
  effect ≠ .terminatesLocally ∧ effect ≠ .noubIfNoinbounds ∧
  effect ≠ .consistentOverlay ∧ (flavor = .total ∨ effect ≠ .nothrow)

/-- Observe a fresh metadata node pointing to a distinct fresh purity node,
all eleven named effect flags, and preservation of every old object. New
Expr/vector identities are existential and need not equal any allocator index.
-/
def PurityObservation {L : Type} (flavor : PurityFlavor)
    (before after : M.Heap L) (result : M.Value L) : Prop :=
  ValidHeap after ∧ PreservesOldHeap before after ∧ AllocationCount before after 2 ∧
  ∃ outer outerArgs purity purityArgs,
    result = .exprRef outer ∧ outer ≠ purity ∧ outerArgs ≠ purityArgs ∧
    FreshExprNode before after outer outerArgs (M.symbolName "meta") 1 ∧
    FreshExprNode before after purity purityArgs (M.symbolName "purity") 11 ∧
    HasSlot after outerArgs 0 (.exprRef purity) ∧
    ∀ effect, ∃ enabled : Bool,
      HasSlot after purityArgs (effectPosition effect) (.bool enabled) ∧
      (enabled = true ↔ EffectEnabled flavor effect)

/-- Total annotations allocate the specified fresh purity graph only in Core.
Every other module returns false with exactly the original heap, so no hidden
allocation or modification occurs on the short-circuit branch. This quantifies
all valid initial heaps and all module-value representations, without asserting
that a model result has already succeeded.
Source: base/boot.jl:333-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def TotalMetaHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L) (mod : M.Value L), ValidHeap heap →
    let observed := M.totalMetaMacro mod heap
    (mod = .coreModule → PurityObservation .total heap observed.2 observed.1) ∧
    (mod ≠ .coreModule → observed.1 = .bool false ∧ observed.2 = heap)

/-- Foldable annotations preserve the full named effect vector, including
the absence of a nothrow promise, and short-circuit with no heap change outside
Core. Source: base/boot.jl:348-361
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def FoldableMetaHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L) (mod : M.Value L), ValidHeap heap →
    let observed := M.foldableMetaMacro mod heap
    (mod = .coreModule → PurityObservation .foldable heap observed.2 observed.1) ∧
    (mod ≠ .coreModule → observed.1 = .bool false ∧ observed.2 = heap)

/-- Inline has one initialized tag and fresh mutable identities, preserving
all previously allocated objects. Source: base/boot.jl:363
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def InlineHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L), ValidHeap heap →
    let observed := M.inlineMacro heap
    FreshAllocation heap observed.2 observed.1 (M.symbolName "meta")
      [.symbol (M.symbolName "inline")]

/-- Noinline has one initialized tag and fresh mutable identities, preserving
all previously allocated objects. Source: base/boot.jl:364
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def NoinlineHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L), ValidHeap heap →
    let observed := M.noinlineMacro heap
    FreshAllocation heap observed.2 observed.1 (M.symbolName "meta")
      [.symbol (M.symbolName "noinline")]

/-- Nospecializeinfer preserves the exact inference tag, allocates a fresh
node and argument vector, and does not modify the old graph.
Source: base/boot.jl:365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def NospecializeinferHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L), ValidHeap heap →
    let observed := M.nospecializeinferMacro heap
    FreshAllocation heap observed.2 observed.1 (M.symbolName "meta")
      [.symbol (M.symbolName "nospecializeinfer")]

/-- The boundscheck marker has no arguments, fresh mutable identities, and
no changes to existing objects. Source: base/boot.jl:367
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def BoundscheckHeapInvariant : Prop :=
  ∀ (L : Type) (heap : M.Heap L), ValidHeap heap →
    let observed := M.boundscheckMacro heap
    FreshAllocation heap observed.2 observed.1 (M.symbolName "boundscheck") []

theorem allocExprHeapInvariant_proven : AllocExprHeapInvariant := by
  intro L heap head arguments size_ok valid headValid argumentsValid
  let vector : M.VectorAny L := ⟨arguments.map some, by simpa using size_ok⟩
  let cell : M.ExprCell := ⟨some head, some heap.argsVectors.length⟩
  let after : M.Heap L := ⟨heap.expressions ++ [cell], heap.argsVectors ++ [vector]⟩
  have extend : ∀ value, ValidValue heap value → ValidValue after value := by
    intro value hv
    cases value <;> simp_all [ValidValue, after] <;> omega
  change FreshAllocation heap after (.exprRef heap.expressions.length) head arguments
  refine ⟨?_, ?_, ?_, heap.expressions.length, heap.argsVectors.length, rfl, ?_, ?_⟩
  · constructor
    · intro current member
      rcases List.mem_append.mp member with old | fresh
      · obtain ⟨heads, refs⟩ := valid.1 current old
        exact ⟨heads, fun ref h => by have := refs ref h; simp [after]; omega⟩
      · have eq := List.mem_singleton.mp fresh
        subst current
        exact ⟨fun name eq => by cases eq; exact headValid,
          fun ref eq => by cases eq; simp [after]⟩
    · intro current member slot slotMember value hv
      rcases List.mem_append.mp member with old | fresh
      · exact extend value (valid.2 current old slot slotMember value hv)
      · have eq := List.mem_singleton.mp fresh
        subst current
        obtain ⟨original, member, equal⟩ := List.mem_map.mp slotMember
        have equalValue : original = value := by
          rw [← equal] at hv
          exact Option.some.inj hv
        subst original
        exact extend value (argumentsValid value member)
  · constructor
    · intro ref current existing
      have hlt := (List.getElem?_eq_some_iff.mp existing).choose
      simpa [M.readExpr, after, List.getElem?_append_left hlt] using existing
    · intro ref current existing
      have hlt := (List.getElem?_eq_some_iff.mp existing).choose
      simpa [M.readArgs, after, List.getElem?_append_left hlt] using existing
  · simp [AllocationCount, after]
  · refine ⟨by simp [M.readExpr], by simp [M.readArgs], cell, vector, ?_, ?_, rfl, rfl, ?_⟩
    · simp [M.readExpr, after]
    · simp [M.readArgs, after]
    · simp [vector]
  · intro index value indexed
    refine ⟨vector, by simp [M.readArgs, after], ?_⟩
    simpa [vector, List.getElem?_map, indexed]

/-- Entries to concatenate into the parent namespace's entriesModels2Group1.
The allocator entry covers a necessary dependency only; it does not certify
the complete public Expr(args...) method.
-/
def entriesHeapMacros : List Entry := [
  { id := "boot-nospecialize-sharing"
    juliaFile := "base/boot.jl"
    juliaFns := ["nospecialize(x)", "Core._expr (valid-head allocation dependency)"]
    statement := "Core.@nospecialize builds distinct fresh escape and metadata nodes with distinct fresh argument vectors, keeps the original argument reference, and preserves arbitrary valid shared or cyclic heaps."
    source := "base/boot.jl:324-326; base/docs/basedocs.jl:712-719; syntax-construction identity and frame invariant"
    status := .todo
    prop := ``NospecializeHeapInvariant
    thm := none
    notes := "Includes every valid represented input and heap, with sharing, cycles and undefined old fields/slots. Depends on the concrete allocExpr dependency." },
  { id := "boot-expr-allocation-graph"
    juliaFile := "base/boot.jl"
    juliaFns := ["Core._expr (valid Symbol head and native-sized argument tuple)"]
    statement := "The concrete valid-head allocation dependency creates one fresh Expr and one fresh initialized argument vector, retaining exact argument identities and every old object."
    source := "base/boot.jl:327; base/docs/basedocs.jl:712-719; allocation/graph invariant for valid Expr construction"
    status := .todo
    prop := ``AllocExprHeapInvariant
    thm := none
    notes := "Necessary runtime dependency only. Does not establish coverage for unrestricted queue row 327, invalid/missing heads, or resource-exhaustion behavior; resource exhaustion is abstracted by the model." },
  { id := "boot-latestworld-freshness"
    juliaFile := "base/boot.jl"
    juliaFns := ["latestworld()", "Core._expr (valid-head allocation dependency)"]
    statement := "Core.@latestworld creates one fresh empty latestworld expression and fresh argument vector while preserving the old heap."
    source := "base/boot.jl:329; base/docs/basedocs.jl:712-719; marker freshness and frame invariant"
    status := .todo
    prop := ``LatestworldHeapInvariant
    thm := none
    notes := "Depends on allocExpr. All valid old heaps, including cyclic/shared/undefined contents, are quantified." },
  { id := "boot-internal-module-identity"
    juliaFile := "base/boot.jl"
    juliaFns := ["_is_internal(__module__)"]
    statement := "_is_internal accepts Core's actual module identity and rejects every other value, including other modules with the same name."
    source := "base/boot.jl:331; module identity invariant"
    status := .proven
    prop := ``InternalModuleIdentityInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.internalModuleIdentityInvariant_proven
    notes := "Uses a disjoint Core identity tag, with no equality callback or assumed equality law. The helper is also exercised by both purity-macro entries." },
  { id := "boot-total-meta-effects"
    juliaFile := "base/boot.jl"
    juliaFns := ["_total_meta()", "_is_internal(__module__)", "Core._expr (valid-head allocation dependency)"]
    statement := "In Core, the total macro constructs fresh nested metadata/purity nodes with all eleven named effects; outside Core it returns false and leaves the heap exactly unchanged."
    source := "base/boot.jl:333-346; base/expr.jl:848-861,948-991; purity flag, identity and frame invariants"
    status := .todo
    prop := ``TotalMetaHeapInvariant
    thm := none
    notes := "Registered dependencies: isInternal and allocExpr. Flags are specified by named EffectsOverride fields and logical conditions rather than a copied Bool list." },
  { id := "boot-foldable-meta-effects"
    juliaFile := "base/boot.jl"
    juliaFns := ["_foldable_meta()", "_is_internal(__module__)", "Core._expr (valid-head allocation dependency)"]
    statement := "In Core, the foldable macro constructs fresh nested metadata/purity nodes with the eleven named effects and no nothrow promise; outside Core it returns false without changing the heap."
    source := "base/boot.jl:348-361; base/expr.jl:816-833,948-991; purity flag, identity and frame invariants"
    status := .todo
    prop := ``FoldableMetaHeapInvariant
    thm := none
    notes := "Registered dependencies: isInternal and allocExpr. The boot-specific task/memory flags are included. All valid old heaps are quantified." },
  { id := "boot-inline-freshness"
    juliaFile := "base/boot.jl"
    juliaFns := ["inline()", "Core._expr (valid-head allocation dependency)"]
    statement := "The zero-argument Core.@inline macro creates fresh metadata and argument-vector identities containing the inline tag, preserving all old objects."
    source := "base/boot.jl:363; base/docs/basedocs.jl:712-719; marker identity/frame invariant"
    status := .todo
    prop := ``InlineHeapInvariant
    thm := none
    notes := "Depends on allocExpr; does not cover Base's other @inline forms." },
  { id := "boot-noinline-freshness"
    juliaFile := "base/boot.jl"
    juliaFns := ["noinline()", "Core._expr (valid-head allocation dependency)"]
    statement := "The zero-argument Core.@noinline macro creates fresh metadata and argument-vector identities containing the noinline tag, preserving all old objects."
    source := "base/boot.jl:364; base/docs/basedocs.jl:712-719; marker identity/frame invariant"
    status := .todo
    prop := ``NoinlineHeapInvariant
    thm := none
    notes := "Depends on allocExpr; does not cover Base's other @noinline forms." },
  { id := "boot-nospecializeinfer-freshness"
    juliaFile := "base/boot.jl"
    juliaFns := ["nospecializeinfer()", "Core._expr (valid-head allocation dependency)"]
    statement := "Core.@nospecializeinfer creates fresh metadata and argument-vector identities with the exact inference tag, leaving every old heap object unchanged."
    source := "base/boot.jl:365; base/docs/basedocs.jl:712-719; marker identity/frame invariant"
    status := .todo
    prop := ``NospecializeinferHeapInvariant
    thm := none
    notes := "Depends on allocExpr; inputs include every valid old heap." },
  { id := "boot-boundscheck-freshness"
    juliaFile := "base/boot.jl"
    juliaFns := ["_boundscheck()", "Core._expr (valid-head allocation dependency)"]
    statement := "Core.@_boundscheck creates a fresh empty boundscheck marker and argument vector without modifying any existing object."
    source := "base/boot.jl:367; base/docs/basedocs.jl:712-719; marker identity/frame invariant"
    status := .todo
    prop := ``BoundscheckHeapInvariant
    thm := none
    notes := "Depends on allocExpr; all properties are unproved and registered todo." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean
open JuliaLean.Registry

/-- The selected positional fallback rejects every native-sized argument tuple
with ArgumentError. This describes the fallback body after Julia dispatch has
selected it, including explicit invocation; it does not constrain other user
methods callable through Union{} or the separate keyword-forwarding wrapper.
The arbitrary value carrier includes all custom values and object handles.
Julia source: base/boot.jl:398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/docs/basedocs.jl:3631-3655 (Union{} is uninhabited).
-/
def BottomConstructionRejected : Prop :=
  ∀ (V : Type) (args : List V), args.length ≤ IntTy.i64.max.toNat →
    match JuliaLean.BootCov.Misc.unionBottomCtor args with
    | .error (.argument _) => True
    | _ => False

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem bottomConstructionRejected_proven : BottomConstructionRejected := by
  intro V args _
  trivial
end

def entriesBottomConstruction : List Entry := [
  { id := "boot-bottom-construction-rejected"
    juliaFile := "base/boot.jl"
    juliaFns := ["Union{}(a...)"]
    statement := "The selected Union{} positional constructor fallback rejects every constructible argument tuple with ArgumentError."
    source := "base/boot.jl:398; base/docs/basedocs.jl:3631-3655 (uninhabited bottom type)"
    status := .proven
    prop := ``BottomConstructionRejected
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.bottomConstructionRejected_proven
    notes := "Reuses JuliaLean.BootCov.Misc.unionBottomCtor, whose result directly represents the fallback's ArgumentError. The separate keyword forwarding method preserves arbitrary generic dispatch in its own additive model." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot

/-- A specification-only named-field observation of immutable Core objects.
Undefined fields are explicit; reference-valued fields retain the original
represented value, rather than a structural copy of the referent. No Julia
callee is replaced by this observer. -/
def ImmutableFields {L : Type} : Obj L → Option (String × List (Option (Value L)))
  | .typeApp h p => some ("TypeApp", [some h, some p])
  | .boundsError a i => some ("BoundsError", [a, i])
  | .divideError => some ("DivideError", [])
  | .outOfMemoryError => some ("OutOfMemoryError", [])
  | .readOnlyMemoryError => some ("ReadOnlyMemoryError", [])
  | .segmentationFault => some ("SegmentationFault", [])
  | .stackOverflowError => some ("StackOverflowError", [])
  | .undefRefError => some ("UndefRefError", [])
  | .interruptException => some ("InterruptException", [])
  | .precompilableError => some ("PrecompilableError", [])
  | .trimFailure => some ("TrimFailure", [])
  | .const x => some ("Const", [some x])
  | .partialTask t => some ("PartialTask", [some t])
  | .possiblyAmbiguous => some ("PossiblyAmbiguous", [])
  | .debugInfo d l e c => some ("DebugInfo", [some d, some l, some e, some c])
  | .methodMatch s p m f => some ("MethodMatch", [some s, some p, some m, some f])
  | .undefInitializer => some ("UndefInitializer", [])
  | _ => none

/-- Observe an object before its pure representation embedding into the shared
value universe. The embedding is universally quantified without any correctness
law. This does not quantify a replacement for the model's body: the actual
existing constructor is evaluated and must have an object witness with the
specified named-field observation. -/
def RepresentsImmutable {W L : Type} (ops : CoreOps W L) (value : Value L)
    (tag : String) (fields : List (Option (Value L))) : Prop :=
  ∃ object : Obj L, value = objV ops object ∧
    ImmutableFields object = some (tag, fields)

/-- A TypeApp records its head and parameter without converting either one.
Both fields accept every Julia value, including custom objects and mutable
references. Julia source: base/boot.jl:413-422; invariant of the two Any fields.
-/
def TypeAppPreservesOperands : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (head param : Value L),
    RepresentsImmutable ops (TypeApp ops head param) "TypeApp" [some head, some param]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem typeAppPreservesOperands_proven : TypeAppPreservesOperands := by
  intro W L ops head param
  exact ⟨.typeApp head param, rfl, rfl⟩
end

/-- BoundsError's omitted fields remain undefined, while supplied fields retain
their original values and aliases. The domain contains arbitrary user values;
no bounds or indexing requirement is imposed on the error's payload itself.
Julia source: base/boot.jl:475-480; base/docs/basedocs.jl (BoundsError constructor).
-/
def BoundsErrorDefinedness : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (a i : Value L),
    RepresentsImmutable ops (BoundsError0 ops) "BoundsError" [none, none] ∧
    RepresentsImmutable ops (BoundsError1 ops a) "BoundsError" [some a, none] ∧
    RepresentsImmutable ops (BoundsError2 ops a i) "BoundsError" [some a, some i]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem boundsErrorDefinedness_proven : BoundsErrorDefinedness := by
  intro W L ops a i
  exact ⟨⟨.boundsError none none, rfl, rfl⟩,
    ⟨.boundsError (some a) none, rfl, rfl⟩,
    ⟨.boundsError (some a) (some i), rfl, rfl⟩⟩
end

/-- Each fieldless exception has its own exception class and zero stored fields.
This distinguishes the exception classes even though their records have no
payload. Julia source: base/boot.jl:482-498,515-516,602-606.
-/
def FieldlessExceptionClasses : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L),
    ∀ item ∈ [
      ("DivideError", DivideError ops),
      ("OutOfMemoryError", OutOfMemoryError ops),
      ("ReadOnlyMemoryError", ReadOnlyMemoryError ops),
      ("SegmentationFault", SegmentationFault ops),
      ("StackOverflowError", StackOverflowError ops),
      ("UndefRefError", UndefRefError ops),
      ("InterruptException", InterruptException ops),
      ("PrecompilableError", PrecompilableError ops),
      ("TrimFailure", TrimFailure ops)],
      RepresentsImmutable ops item.2 item.1 []

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem fieldlessExceptionClasses_proven : FieldlessExceptionClasses := by
  intro W L ops item h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.divideError, rfl, rfl⟩
  · exact ⟨.outOfMemoryError, rfl, rfl⟩
  · exact ⟨.readOnlyMemoryError, rfl, rfl⟩
  · exact ⟨.segmentationFault, rfl, rfl⟩
  · exact ⟨.stackOverflowError, rfl, rfl⟩
  · exact ⟨.undefRefError, rfl, rfl⟩
  · exact ⟨.interruptException, rfl, rfl⟩
  · exact ⟨.precompilableError, rfl, rfl⟩
  · exact ⟨.trimFailure, rfl, rfl⟩
end

/-- The String identity constructor is lossless and idempotent, including for
invalid-UTF-8 strings represented by opaque values. Nothing and the empty tuple
constructors return their unique value. Arguments use the existing selected-
dispatch convention, so String_String's input is already a Julia String.
Julia source: base/boot.jl:611,614,643; doc/src/manual/types.md (singleton values).
-/
def SimpleValueConstructors : Prop :=
  (∀ (L : Type) (x y : Value L),
    (String_String x = String_String y ↔ x = y) ∧
      String_String (String_String x) = String_String x) ∧
  (∀ (W L : Type) (ops : CoreOps W L),
    Nothing_ ops = nothingV ops ∧ Tuple_empty ops = tupleV ops [])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem simpleValueConstructors_proven : SimpleValueConstructors := by
  exact ⟨fun _ _ _ => ⟨Iff.rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
end

/-- The inference wrappers retain every supplied value, without inspecting or
copying it. Their marker constructors have the advertised fieldless class.
Julia source: base/boot.jl:651-655,690-696,755-759; internal record invariants.
-/
def InferenceWrapperFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (value typ : Value L),
    RepresentsImmutable ops (Const ops value) "Const" [some value] ∧
    RepresentsImmutable ops (PartialTask ops typ) "PartialTask" [some typ] ∧
    RepresentsImmutable ops (PossiblyAmbiguous ops) "PossiblyAmbiguous" [] ∧
    RepresentsImmutable ops (UndefInitializer ops) "UndefInitializer" []

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem inferenceWrapperFields_proven : InferenceWrapperFields := by
  intro W L ops value typ
  exact ⟨⟨.const value, rfl, rfl⟩, ⟨.partialTask typ, rfl, rfl⟩,
    ⟨.possiblyAmbiguous, rfl, rfl⟩, ⟨.undefInitializer, rfl, rfl⟩⟩
end

/-- Specification-only observation of immutable IR nodes. Machine integer
fields remain JInt values; absent value/scope fields remain undefined. -/
def IRFields {L : Type} : Value L → Option (String × List I64 × List (Option (Value L)))
  | .gotoNode label => some ("GotoNode", [label], [])
  | .newvarNode slot => some ("NewvarNode", [], [some slot])
  | .quoteNode value => some ("QuoteNode", [], [some value])
  | .ssaValue id => some ("SSAValue", [id], [])
  | .argument n => some ("Argument", [n], [])
  | .returnNode value => some ("ReturnNode", [], [value])
  | .gotoIfNot cond dest => some ("GotoIfNot", [dest], [some cond])
  | .enterNode dest scope => some ("EnterNode", [dest], [scope])
  | .lineNumberNode line file => some ("LineNumberNode", [line], [some file])
  | .slotNumber n => some ("SlotNumber", [n], [])
  | .upsilonNode value => some ("UpsilonNode", [], [value])
  | _ => none

/-- Raw-new immutable IR constructors preserve the complete native-Int field
range and all value references. Missing ReturnNode/UpsilonNode values indicate
unreachable or unassigned values; a missing EnterNode scope is undefined.
There is no undocumented positive-label precondition.
Julia source: base/boot.jl:699-710,719,723-724 (generated methods in eval(Core,quote)).
-/
def ImmutableIRFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (n : I64) (value scope : Value L),
    IRFields (GotoNode (L := L) n) = some ("GotoNode", [n], []) ∧
    IRFields (NewvarNode value) = some ("NewvarNode", [], [some value]) ∧
    IRFields (QuoteNode value) = some ("QuoteNode", [], [some value]) ∧
    IRFields (SSAValue (L := L) n) = some ("SSAValue", [n], []) ∧
    IRFields (Argument (L := L) n) = some ("Argument", [n], []) ∧
    IRFields (ReturnNode1 value) = some ("ReturnNode", [], [some value]) ∧
    IRFields (ReturnNode0 (L := L)) = some ("ReturnNode", [], [none]) ∧
    IRFields (GotoIfNot value n) = some ("GotoIfNot", [n], [some value]) ∧
    IRFields (EnterNode1 (L := L) n) = some ("EnterNode", [n], [none]) ∧
    IRFields (EnterNode2 n scope) = some ("EnterNode", [n], [some scope]) ∧
    IRFields (LineNumberNode1 ops n) = some ("LineNumberNode", [n], [some (nothingV ops)]) ∧
    IRFields (SlotNumber (L := L) n) = some ("SlotNumber", [n], []) ∧
    IRFields (UpsilonNode1 value) = some ("UpsilonNode", [], [some value]) ∧
    IRFields (UpsilonNode0 (L := L)) = some ("UpsilonNode", [], [none])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem immutableIRFields_proven : ImmutableIRFields := by
  unfold ImmutableIRFields
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end

/-- DebugInfo and MethodMatch store the already-dispatched typed arguments;
DebugInfo's convenience constructor fills only the specified empty defaults.
SimpleVector and String payloads remain opaque existing values; no unbounded
Lean list is substituted for an input Julia container.
Julia source: base/boot.jl:715-718,725 (generated raw-new constructors).
-/
def DebugAndMatchFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L)
    (defn linetable edges codelocs specTypes sparams method : Value L) (fullyCovers : Bool),
    RepresentsImmutable ops (DebugInfo4 ops defn linetable edges codelocs) "DebugInfo"
      [some defn, some linetable, some edges, some codelocs] ∧
    RepresentsImmutable ops (DebugInfo1 ops defn) "DebugInfo"
      [some defn, some (nothingV ops), some (.leaf (ops.svec [])), some (strV ops "")] ∧
    RepresentsImmutable ops (MethodMatch ops specTypes sparams method fullyCovers) "MethodMatch"
      [some specTypes, some sparams, some method, some (boolV ops fullyCovers)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem debugAndMatchFields_proven : DebugAndMatchFields := by
  intro W L ops defn linetable edges codelocs specTypes sparams method fullyCovers
  exact ⟨⟨.debugInfo defn linetable edges codelocs, rfl, rfl⟩,
    ⟨.debugInfo defn (nothingV ops) (.leaf (ops.svec [])) (strV ops ""), rfl, rfl⟩,
    ⟨.methodMatch specTypes sparams method (boolV ops fullyCovers), rfl, rfl⟩⟩
end

def entriesReusedConstructors : List Entry := [
  { id := "boot-typeapp-fields", juliaFile := "base/boot.jl"
    juliaFns := ["TypeApp(@nospecialize(head), @nospecialize(param))"]
    statement := "TypeApp preserves its arbitrary head and parameter values in their respective fields."
    source := "base/boot.jl:413-422; invariant of TypeApp's two Any fields"
    status := .proven, prop := ``TypeAppPreservesOperands, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.typeAppPreservesOperands_proven },
  { id := "boot-bounds-error-definedness", juliaFile := "base/boot.jl"
    juliaFns := ["BoundsError()", "BoundsError(@nospecialize(a))", "BoundsError(@nospecialize(a), i)"]
    statement := "BoundsError stores supplied payloads unchanged and leaves each omitted field undefined."
    source := "base/boot.jl:475-480; constructor field and definedness invariant"
    status := .proven, prop := ``BoundsErrorDefinedness, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.boundsErrorDefinedness_proven },
  { id := "boot-fieldless-exception-classes", juliaFile := "base/boot.jl"
    juliaFns := ["DivideError()", "OutOfMemoryError()", "ReadOnlyMemoryError()", "SegmentationFault()", "StackOverflowError()", "UndefRefError()", "InterruptException()", "PrecompilableError()", "TrimFailure()"]
    statement := "Each fieldless exception constructor produces its own exception class with no stored fields."
    source := "base/boot.jl:482-498,515-516,602-606; exception-class invariant"
    status := .proven, prop := ``FieldlessExceptionClasses, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.fieldlessExceptionClasses_proven },
  { id := "boot-simple-value-constructors", juliaFile := "base/boot.jl"
    juliaFns := ["String(s::String)", "Nothing()", "Tuple{}()"]
    statement := "String's identity constructor is injective and idempotent; Nothing and Tuple{} produce their unique empty values."
    source := "base/boot.jl:611,614,643; identity and singleton-value invariants"
    status := .proven, prop := ``SimpleValueConstructors, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.simpleValueConstructors_proven },
  { id := "boot-inference-wrapper-fields", juliaFile := "base/boot.jl"
    juliaFns := ["Const(@nospecialize(v))", "PartialTask(@nospecialize(fetch_type))", "PossiblyAmbiguous()", "UndefInitializer()"]
    statement := "Const and PartialTask retain their arbitrary payload values; PossiblyAmbiguous and UndefInitializer have their specified fieldless classes."
    source := "base/boot.jl:651-655,690-696,755-759; internal record invariants"
    status := .proven, prop := ``InferenceWrapperFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.inferenceWrapperFields_proven },
  { id := "boot-immutable-ir-fields", juliaFile := "base/boot.jl"
    juliaFns := ["GotoNode(label::Int)", "NewvarNode(slot::SlotNumber)", "QuoteNode(@nospecialize value)", "SSAValue(id::Int)", "Argument(n::Int)", "ReturnNode(@nospecialize val)", "ReturnNode()", "GotoIfNot(@nospecialize(cond), dest::Int)", "EnterNode(dest::Int)", "EnterNode(dest::Int, @nospecialize(scope))", "LineNumberNode(l::Int)", "SlotNumber(n::Int)", "UpsilonNode(@nospecialize(val))", "UpsilonNode()"]
    statement := "Immutable raw-new IR constructors retain all native-Int values and supplied references, and preserve the documented undefined value/scope fields."
    source := "base/boot.jl:699-710,719,723-724; generated-method field invariants"
    status := .proven, prop := ``ImmutableIRFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.immutableIRFields_proven },
  { id := "boot-debug-match-fields", juliaFile := "base/boot.jl"
    juliaFns := ["DebugInfo(def, linetable, edges, codelocs)", "DebugInfo(def)", "MethodMatch(spec_types, sparams, method, fully_covers)"]
    statement := "DebugInfo and MethodMatch retain their typed arguments; the short DebugInfo constructor supplies exactly the specified empty metadata defaults."
    source := "base/boot.jl:715-718,725; generated-method field invariants"
    status := .proven, prop := ``DebugAndMatchFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.debugAndMatchFields_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1
open JuliaLean.Registry

/-!
Independent field observations for the typed immutable constructors. These
statements inspect the resulting object's type, set of field names, and defined
field values. Expected values are the original inputs and specified defaults;
none reconstructs the constructor's output as its expected result.

The source signature is the dispatch domain; opaque payloads represent every
accepted subtype or object. Quantification over the wider Lean payload space is
intentional and imposes no additional Julia precondition. Pure encodings are
universally quantified without laws, so even tuple reordering or an incorrect
constant remains falsifiable by an encoding that distinguishes those values.
-/

/-- A specification observation of the immutable constructor tag. Other Obj
variants are outside this observer's selected family. -/
def constructorTag {L : Type} : Obj L → Option String
  | .errorException _ => some "ErrorException"
  | .concurrencyViolationError _ => some "ConcurrencyViolationError"
  | .missingCodeError _ => some "MissingCodeError"
  | .domainError _ _ => some "DomainError"
  | .inexactError _ _ => some "InexactError"
  | .overflowError _ => some "OverflowError"
  | .argumentError _ => some "ArgumentError"
  | .undefKeywordError _ => some "UndefKeywordError"
  | .methodError _ _ _ => some "MethodError"
  | .assertionError _ => some "AssertionError"
  | .fieldError _ _ => some "FieldError"
  | .loadError _ _ _ => some "LoadError"
  | .initError _ _ => some "InitError"
  | .abiOverride _ _ => some "ABIOverride"
  | _ => none

/-- Specification field-name/value observations derived from the immutable
struct layouts at `base/boot.jl:470-600`. Each listed value is a defined field;
these selected structs have no omitted field in the constructors under study. -/
def constructorFields {L : Type} : Obj L → List (String × JuliaLean.base.expr.Value L)
  | .errorException msg => [("msg", msg)]
  | .concurrencyViolationError msg => [("msg", msg)]
  | .missingCodeError mi => [("mi", mi)]
  | .domainError val msg => [("val", val), ("msg", msg)]
  | .inexactError func args => [("func", func), ("args", args)]
  | .overflowError msg => [("msg", msg)]
  | .argumentError msg => [("msg", msg)]
  | .undefKeywordError var => [("var", var)]
  | .methodError f args world => [("f", f), ("args", args), ("world", world)]
  | .assertionError msg => [("msg", msg)]
  | .fieldError typ field => [("type", typ), ("field", field)]
  | .loadError file line error => [("file", file), ("line", line), ("error", error)]
  | .initError mod error => [("mod", mod), ("error", error)]
  | .abiOverride abi defn => [("abi", abi), ("def", defn)]
  | _ => []

/-- Observe whether a named field exists and is defined, without calling any
parameterized Julia operation. This is a specification observer only. -/
def constructorField {L : Type} (obj : Obj L) (name : String) :
    Option (JuliaLean.base.expr.Value L) :=
  (constructorFields obj).lookup name

/-- Type, field count, and defined stored-field observations. The expected
values are specified independently as source arguments or documented defaults. -/
def HasConstructorFields {L : Type} (obj : Obj L) (tag : String)
    (fields : List (String × JuliaLean.base.expr.Value L)) : Prop :=
  constructorTag obj = some tag ∧
  (constructorFields obj).length = fields.length ∧
  ∀ name value, (name, value) ∈ fields → constructorField obj name = some value

/-- Store the accepted AbstractString object itself in ErrorException.msg.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:472`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def ErrorExceptionFields : Prop :=
  ∀ (L : Type) (msg : JuliaLean.base.expr.Value L),
    HasConstructorFields (errorExceptionCtor msg) "ErrorException" [("msg", msg)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem errorExceptionFields_proven : ErrorExceptionFields := by
  unfold ErrorExceptionFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted AbstractString object itself in ConcurrencyViolationError.msg.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:509`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def ConcurrencyViolationFields : Prop :=
  ∀ (L : Type) (msg : JuliaLean.base.expr.Value L),
    HasConstructorFields (concurrencyViolationCtor msg) "ConcurrencyViolationError" [("msg", msg)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem concurrencyViolationFields_proven : ConcurrencyViolationFields := by
  unfold ConcurrencyViolationFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted MethodInstance unchanged in MissingCodeError.mi.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:513`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def MissingCodeFields : Prop :=
  ∀ (L : Type) (mi : JuliaLean.base.expr.Value L),
    HasConstructorFields (missingCodeCtor mi) "MissingCodeError" [("mi", mi)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem missingCodeFields_proven : MissingCodeFields := by
  unfold MissingCodeFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the offending value and initialize DomainError.msg to the empty String.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:521`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def DomainErrorDefaultFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (val : JuliaLean.base.expr.Value L),
    HasConstructorFields (domainErrorDefaultCtor ops val) "DomainError" [("val", val), ("msg", strV ops "")]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem domainErrorDefaultFields_proven : DomainErrorDefaultFields := by
  unfold DomainErrorDefaultFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the function Symbol and the complete, ordered, native-sized varargs tuple in InexactError.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:542`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def InexactErrorFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (f : JuliaLean.base.expr.Value L) (args : ConstructorTuple L),
    HasConstructorFields (inexactErrorCtor ops f args) "InexactError" [("func", f), ("args", tupleV ops args.values)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem inexactErrorFields_proven : InexactErrorFields := by
  unfold InexactErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted AbstractString object itself in OverflowError.msg.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:546`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def OverflowErrorFields : Prop :=
  ∀ (L : Type) (msg : JuliaLean.base.expr.Value L),
    HasConstructorFields (overflowErrorCtor msg) "OverflowError" [("msg", msg)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem overflowErrorFields_proven : OverflowErrorFields := by
  unfold OverflowErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted AbstractString object itself in ArgumentError.msg.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:551`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def ArgumentErrorFields : Prop :=
  ∀ (L : Type) (msg : JuliaLean.base.expr.Value L),
    HasConstructorFields (argumentErrorCtor msg) "ArgumentError" [("msg", msg)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem argumentErrorFields_proven : ArgumentErrorFields := by
  unfold ArgumentErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted Symbol itself in UndefKeywordError.var.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:555`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def UndefKeywordFields : Prop :=
  ∀ (L : Type) (var : JuliaLean.base.expr.Value L),
    HasConstructorFields (undefKeywordCtor var) "UndefKeywordError" [("var", var)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem undefKeywordFields_proven : UndefKeywordFields := by
  unfold UndefKeywordFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the function, argument value, and every native UInt world in MethodError.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:565`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def MethodErrorFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (f args : JuliaLean.base.expr.Value L) (world : JInt .u64),
    HasConstructorFields (methodErrorCtor ops f args world) "MethodError" [("f", f), ("args", args), ("world", intV ops world)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem methodErrorFields_proven : MethodErrorFields := by
  unfold MethodErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Store the accepted AbstractString object itself in AssertionError.msg.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:571`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def AssertionErrorFields : Prop :=
  ∀ (L : Type) (msg : JuliaLean.base.expr.Value L),
    HasConstructorFields (assertionErrorCtor msg) "AssertionError" [("msg", msg)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem assertionErrorFields_proven : AssertionErrorFields := by
  unfold AssertionErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- The zero-argument AssertionError initializes its message to the empty String.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:573`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def AssertionErrorDefaultFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L),
    HasConstructorFields (assertionErrorDefaultCtor ops) "AssertionError" [("msg", strV ops "")]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem assertionErrorDefaultFields_proven : AssertionErrorDefaultFields := by
  unfold AssertionErrorDefaultFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the accepted DataType and field Symbol as FieldError.type and FieldError.field.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:578`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def FieldErrorFields : Prop :=
  ∀ (L : Type) (typ field : JuliaLean.base.expr.Value L),
    HasConstructorFields (fieldErrorCtor typ field) "FieldError" [("type", typ), ("field", field)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem fieldErrorFields_proven : FieldErrorFields := by
  unfold FieldErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the accepted AbstractString filename, every native Int line, and the wrapped error in LoadError.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:587`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def LoadErrorFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (file : JuliaLean.base.expr.Value L) (line : JInt .i64) (error : JuliaLean.base.expr.Value L),
    HasConstructorFields (loadErrorCtor ops file line error) "LoadError" [("file", file), ("line", intV ops line), ("error", error)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem loadErrorFields_proven : LoadErrorFields := by
  unfold LoadErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the accepted module-name Symbol and the wrapped error in InitError.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:593`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def InitErrorFields : Prop :=
  ∀ (L : Type) (mod error : JuliaLean.base.expr.Value L),
    HasConstructorFields (initErrorCtor mod error) "InitError" [("mod", mod), ("error", error)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem initErrorFields_proven : InitErrorFields := by
  unfold InitErrorFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Preserve the accepted Type and MethodInstance in ABIOverride.abi and ABIOverride.def.
Every field is defined, with the advertised constructor type and field count.
Julia source/invariant: `base/boot.jl:599`; constructor conversion semantics:
`base/essentials.jl:1468-1488`. -/
def ABIOverrideFields : Prop :=
  ∀ (L : Type) (abi defn : JuliaLean.base.expr.Value L),
    HasConstructorFields (abiOverrideCtor abi defn) "ABIOverride" [("abi", abi), ("def", defn)]

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem aBIOverrideFields_proven : ABIOverrideFields := by
  unfold ABIOverrideFields
  intros
  refine ⟨rfl, rfl, ?_⟩
  intro name value h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
end

/-- Entries for the sixteen additive immutable-constructor models. The parent
proof namespace concatenates these into entriesModels2Group1. -/
def constructorEntries : List Entry := [
  { id := "boot-constructor-error-exception", juliaFile := "base/boot.jl"
    juliaFns := ["ErrorException(msg::AbstractString)"]
    statement := "Store the accepted AbstractString object itself in ErrorException.msg. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:472; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.ErrorExceptionFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.errorExceptionFields_proven },
  { id := "boot-constructor-concurrency-violation", juliaFile := "base/boot.jl"
    juliaFns := ["ConcurrencyViolationError(msg::AbstractString)"]
    statement := "Store the accepted AbstractString object itself in ConcurrencyViolationError.msg. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:509; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.ConcurrencyViolationFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.concurrencyViolationFields_proven },
  { id := "boot-constructor-missing-code", juliaFile := "base/boot.jl"
    juliaFns := ["MissingCodeError(mi::MethodInstance)"]
    statement := "Store the accepted MethodInstance unchanged in MissingCodeError.mi. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:513; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MissingCodeFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.missingCodeFields_proven },
  { id := "boot-constructor-domain-default", juliaFile := "base/boot.jl"
    juliaFns := ["DomainError(@nospecialize(val))"]
    statement := "Preserve the offending value and initialize DomainError.msg to the empty String. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:521; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DomainErrorDefaultFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.domainErrorDefaultFields_proven },
  { id := "boot-constructor-inexact-error", juliaFile := "base/boot.jl"
    juliaFns := ["InexactError(f::Symbol, @nospecialize(args...))"]
    statement := "Preserve the function Symbol and the complete, ordered, native-sized varargs tuple in InexactError. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:542; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.InexactErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.inexactErrorFields_proven },
  { id := "boot-constructor-overflow-error", juliaFile := "base/boot.jl"
    juliaFns := ["OverflowError(msg::AbstractString)"]
    statement := "Store the accepted AbstractString object itself in OverflowError.msg. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:546; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.OverflowErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.overflowErrorFields_proven },
  { id := "boot-constructor-argument-error", juliaFile := "base/boot.jl"
    juliaFns := ["ArgumentError(msg::AbstractString)"]
    statement := "Store the accepted AbstractString object itself in ArgumentError.msg. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:551; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.ArgumentErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.argumentErrorFields_proven },
  { id := "boot-constructor-undef-keyword", juliaFile := "base/boot.jl"
    juliaFns := ["UndefKeywordError(var::Symbol)"]
    statement := "Store the accepted Symbol itself in UndefKeywordError.var. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:555; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.UndefKeywordFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.undefKeywordFields_proven },
  { id := "boot-constructor-method-error", juliaFile := "base/boot.jl"
    juliaFns := ["MethodError(@nospecialize(f), @nospecialize(args), world::UInt)"]
    statement := "Preserve the function, argument value, and every native UInt world in MethodError. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:565; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MethodErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.methodErrorFields_proven },
  { id := "boot-constructor-assertion-error", juliaFile := "base/boot.jl"
    juliaFns := ["AssertionError(msg::AbstractString)"]
    statement := "Store the accepted AbstractString object itself in AssertionError.msg. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:571; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.AssertionErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.assertionErrorFields_proven },
  { id := "boot-constructor-assertion-default", juliaFile := "base/boot.jl"
    juliaFns := ["AssertionError()"]
    statement := "The zero-argument AssertionError initializes its message to the empty String. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:573; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.AssertionErrorDefaultFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.assertionErrorDefaultFields_proven },
  { id := "boot-constructor-field-error", juliaFile := "base/boot.jl"
    juliaFns := ["FieldError(type::DataType, field::Symbol)"]
    statement := "Preserve the accepted DataType and field Symbol as FieldError.type and FieldError.field. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:578; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.FieldErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.fieldErrorFields_proven },
  { id := "boot-constructor-load-error", juliaFile := "base/boot.jl"
    juliaFns := ["LoadError(file::AbstractString, line::Int, @nospecialize(error))"]
    statement := "Preserve the accepted AbstractString filename, every native Int line, and the wrapped error in LoadError. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:587; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.LoadErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.loadErrorFields_proven },
  { id := "boot-constructor-init-error", juliaFile := "base/boot.jl"
    juliaFns := ["InitError(mod::Symbol, @nospecialize(error))"]
    statement := "Preserve the accepted module-name Symbol and the wrapped error in InitError. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:593; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.InitErrorFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.initErrorFields_proven },
  { id := "boot-constructor-abi-override", juliaFile := "base/boot.jl"
    juliaFns := ["ABIOverride(@nospecialize(abi::Type), def::MethodInstance)"]
    statement := "Preserve the accepted Type and MethodInstance in ABIOverride.abi and ABIOverride.def. All advertised fields are defined and the result has the correct constructor type and field count."
    source := "base/boot.jl:599; invariant of field storage; base/essentials.jl:1468-1488"
    status := .proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.ABIOverrideFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.aBIOverrideFields_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot

/-- Observe fields of the additional immutable constructors independently of
their model bodies. Integer fields use the baseline value encoding. -/
def TypedWrapperFields {L : Type} : Obj L → Option (String × List (JuliaLean.base.expr.Value L))
  | .evalInto mod => some ("EvalInto", [mod])
  | .vecElement T value => some ("VecElement", [T, value])
  | .interConditional slot thentype elsetype => some ("InterConditional", [slot, thentype, elsetype])
  | .interMustAlias slot vartyp fldidx fldtyp => some ("InterMustAlias", [slot, vartyp, fldidx, fldtyp])
  | .lineInfoNode mod method file line inlinedAt => some ("LineInfoNode", [mod, method, file, line, inlinedAt])
  | _ => none

/-- EvalInto retains the module object, rather than its printed name or a
different module with the same name. Julia source: base/boot.jl:622-624. -/
def EvalIntoModuleIdentity : Prop :=
  ∀ (L : Type) (mod : JuliaLean.base.expr.Value L),
    TypedWrapperFields (JuliaLean.base.boot.Models2Group1.evalIntoCtor mod) =
      some ("EvalInto", [mod])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem evalIntoModuleIdentity_proven : EvalIntoModuleIdentity := by
  unfold EvalIntoModuleIdentity
  intros
  rfl
end

/-- The selected typed VecElement constructor preserves the explicit type parameter
and value, whose type already satisfies T.
Julia source: base/boot.jl:645-647. -/
def VecElementTypeAndValue : Prop :=
  ∀ (L : Type) (T value : JuliaLean.base.expr.Value L),
    TypedWrapperFields (JuliaLean.base.boot.Models2Group1.vecElementTypedCtor T value) =
      some ("VecElement", [T, value])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem vecElementTypeAndValue_proven : VecElementTypeAndValue := by
  unfold VecElementTypeAndValue
  intros
  rfl
end

/-- The inference records preserve every native Int, including negative and
extreme values; no range check or conversion is performed by these constructors.
Julia source: base/boot.jl:667-679; invariant of their already-typed fields. -/
def InterInferenceFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (slot fldidx : JInt .i64)
    (thentype elsetype vartyp fldtyp : JuliaLean.base.expr.Value L),
    TypedWrapperFields (JuliaLean.base.boot.Models2Group1.interConditionalCtor ops slot thentype elsetype) =
      some ("InterConditional", [intV ops slot, thentype, elsetype]) ∧
    TypedWrapperFields (JuliaLean.base.boot.Models2Group1.interMustAliasCtor ops slot vartyp fldidx fldtyp) =
      some ("InterMustAlias", [intV ops slot, vartyp, intV ops fldidx, fldtyp])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem interInferenceFields_proven : InterInferenceFields := by
  unfold InterInferenceFields
  intros
  exact ⟨rfl, rfl⟩
end

/-- LineInfoNode retains the actual module and file symbol and the complete
Int32 values of both location fields. Julia source: base/boot.jl:730-736. -/
def LineInfoFields : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L)
    (mod method file : JuliaLean.base.expr.Value L) (line inlinedAt : JInt .i32),
    TypedWrapperFields (JuliaLean.base.boot.Models2Group1.lineInfoCtor ops mod method file line inlinedAt) =
      some ("LineInfoNode", [mod, method, file, intV ops line, intV ops inlinedAt])

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem lineInfoFields_proven : LineInfoFields := by
  unfold LineInfoFields
  intros
  rfl
end

/-- Legacy immutable record models preserve the complete opaque array and
MethodInstance identities. The actual containers may have any constructible
contents, aliases, undefined slots, or lengths; the constructors do not inspect
or copy them. No equal-array-length or well-formed-IR premise is added.
Julia source: base/boot.jl:657-664,682-687. -/
def OpaqueInferenceReferenceFields : Prop :=
  ∀ (typ undefs fields env parent source : JuliaLean.BootCov.JVal),
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialStruct typ undefs fields) 1 = .ok typ ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialStruct typ undefs fields) 2 = .ok undefs ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialStruct typ undefs fields) 3 = .ok fields ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialOpaque typ env parent source) 1 = .ok typ ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialOpaque typ env parent source) 2 = .ok env ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialOpaque typ env parent source) 3 = .ok parent ∧
    JuliaLean.BootCov.getfieldObj (JuliaLean.BootCov.Objects.partialOpaque typ env parent source) 4 = .ok source

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem opaqueInferenceReferenceFields_proven : OpaqueInferenceReferenceFields := by
  unfold OpaqueInferenceReferenceFields
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end

def entriesRemainingTyped : List Entry := [
  { id := "boot-eval-into-module", juliaFile := "base/boot.jl"
    juliaFns := ["EvalInto(m::Module)"]
    statement := "EvalInto's constructor stores the actual module identity unchanged."
    source := "base/boot.jl:622-624; field identity invariant"
    status := .proven, prop := ``EvalIntoModuleIdentity, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.evalIntoModuleIdentity_proven },
  { id := "boot-vec-element-fields", juliaFile := "base/boot.jl"
    juliaFns := ["VecElement{T}(value::T) where {T}"]
    statement := "The typed VecElement constructor retains its explicit type parameter and source-typed value without conversion."
    source := "base/boot.jl:645-647; typed-wrapper invariant"
    status := .proven, prop := ``VecElementTypeAndValue, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.vecElementTypeAndValue_proven },
  { id := "boot-inter-inference-fields", juliaFile := "base/boot.jl"
    juliaFns := ["InterConditional(slot::Int, thentype, elsetype)", "InterMustAlias(slot::Int, vartyp, fldidx::Int, fldtyp)"]
    statement := "InterConditional and InterMustAlias preserve all native integer fields and arbitrary type/value payloads."
    source := "base/boot.jl:667-679; typed-field invariant; base/essentials.jl:1468-1488"
    status := .proven, prop := ``InterInferenceFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.interInferenceFields_proven },
  { id := "boot-line-info-fields", juliaFile := "base/boot.jl"
    juliaFns := ["LineInfoNode(mod::Module, method, file::Symbol, line::Int32, inlined_at::Int32)"]
    statement := "LineInfoNode retains module/file identities and all Int32 line and inlining values."
    source := "base/boot.jl:730-736; typed-field invariant"
    status := .proven, prop := ``LineInfoFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.lineInfoFields_proven },
  { id := "boot-opaque-inference-fields", juliaFile := "base/boot.jl"
    juliaFns := ["_PartialStruct(typ, undef::Array{Union{Nothing,Bool},1}, fields::Array{Any,1})", "PartialOpaque(typ::Type, env, parent::MethodInstance, source)"]
    statement := "_PartialStruct and PartialOpaque store every accepted payload and original array/runtime-object identity without inspecting or copying it."
    source := "base/boot.jl:657-664,682-687; immutable reference-field invariant"
    status := .proven, prop := ``OpaqueInferenceReferenceFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.opaqueInferenceReferenceFields_proven
    notes := "Reuses JuliaLean.BootCov.Objects.partialStruct and partialOpaque; mutable payloads are opaque references, not unbounded lists of container contents." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean
open JuliaLean.Registry

namespace BoxModel
export JuliaLean.base.boot.Models2Group1
  (BoxHandle BoxHeap boxWithValue boxWithoutValue)
end BoxModel

namespace LegacyIR
export JuliaLean.BootCov (JVal getfieldObj isdefinedObj)
export JuliaLean.BootCov.Objects (phiNode piNode phiCNode)
end LegacyIR

/-- Observe the stored field of a named Box. The outer none means no such
object exists; some none means the object exists with its field undefined.
This is an observer, not a model of a general Julia getfield call.
-/
def ReadBoxContents {V : Type} (heap : BoxModel.BoxHeap V)
    (box : BoxModel.BoxHandle) : Option (Option V) := heap[box.ref]?

/-- Preserve each previously allocated object at its original logical identity,
including any undefined field or shared input value. No expected appended store
or particular numeric identity of the new object is specified.
-/
def BoxPreservesOldStore {V : Type}
    (before after : BoxModel.BoxHeap V) : Prop :=
  ∀ (ref : Nat) (contents : Option V),
    before[ref]? = some contents → after[ref]? = some contents

/-- A constructor creates exactly one new logical Box, with the specified
field-definedness and original payload, while preserving all old objects.
Freshness is absence from the old store, not the allocator's chosen address.
-/
def FreshBox {V : Type} (before after : BoxModel.BoxHeap V)
    (box : BoxModel.BoxHandle) (contents : Option V) : Prop :=
  ReadBoxContents before box = none ∧
  ReadBoxContents after box = some contents ∧
  BoxPreservesOldStore before after ∧ after.length = before.length + 1

/-- Box(x) always yields a fresh mutable identity with a defined contents field
containing the exact input value. All old objects and aliases are retained.
The carrier V includes arbitrary actual Julia values and is never inspected.
Source: base/boot.jl:628-632; doc/src/manual/constructors.md:198-203
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def BoxWithValueInvariant : Prop :=
  ∀ (V : Type) (heap : BoxModel.BoxHeap V) (x : V),
    let observed := BoxModel.boxWithValue x heap
    FreshBox heap observed.2 observed.1 (some x)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

private theorem oldBoxAppend {V : Type} (before : List (Option V)) (added : Option V) :
    BoxPreservesOldStore before (before ++ [added]) := by
  intro ref contents h
  induction before generalizing ref with
  | nil => simp at h
  | cons head tail ih =>
    cases ref with
    | zero => exact h
    | succ ref => exact ih ref h

theorem boxWithValueInvariant_proven : BoxWithValueInvariant := by
  intro V heap x
  refine ⟨?_, ?_, oldBoxAppend heap (some x), ?_⟩
  · simp [ReadBoxContents, BoxModel.boxWithValue]
  · simp [ReadBoxContents, BoxModel.boxWithValue]
  · simp [BoxModel.boxWithValue]
end

/-- Box() yields a fresh mutable identity whose existing field is undefined,
preserving every old Box. No successful-output premise or default field value
is introduced. Source: base/boot.jl:628-632;
doc/src/manual/constructors.md:198-203,228-246
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def BoxWithoutValueInvariant : Prop :=
  ∀ (V : Type) (heap : BoxModel.BoxHeap V),
    let observed := BoxModel.boxWithoutValue (V := V) heap
    FreshBox heap observed.2 observed.1 none

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem boxWithoutValueInvariant_proven : BoxWithoutValueInvariant := by
  intro V heap
  refine ⟨?_, ?_, oldBoxAppend heap none, ?_⟩
  · simp [ReadBoxContents, BoxModel.boxWithoutValue]
  · simp [ReadBoxContents, BoxModel.boxWithoutValue]
  · simp [BoxModel.boxWithoutValue]
end

/-- An independent snapshot of a concrete Array{Int32,1}. Uninitialized isbits
storage can have arbitrary Int32 bit patterns, all included by JInt .i32.
This is an observation type, not an added array model or constructor.
-/
structure Int32ArraySnapshot where
  data : List (JInt .i32)
  native_size : data.length ≤ IntTy.i64.max.toNat

/-- An independent snapshot of a concrete Array{Any,1}; every slot may be
undefined, and the length is constructible as a Julia native Int.
-/
structure AnyArraySnapshot where
  data : List (Option LegacyIR.JVal)
  native_size : data.length ≤ IntTy.i64.max.toNat

/-- Global array identities have their actual concrete element type. In
particular one valid opaque identity cannot simultaneously denote an Int32
array and an Any array. This is a representation invariant, not a constructor
check. Every constructible length and every content/#undef pattern is included.
-/
inductive IRArraySnapshot where
  | int32 (array : Int32ArraySnapshot)
  | any (array : AnyArraySnapshot)

abbrev IRArrayHeap := Nat → Option IRArraySnapshot

/-- Dereference an opaque array identity in an arbitrary observed world. The
world can be a later state after either array has been mutated or resized.
There is no assumption about an observer or dispatch implementation.
-/
def ReadIRArrayIdentity (heap : IRArrayHeap) : LegacyIR.JVal → Option IRArraySnapshot
  | .opaque ref => heap ref
  | _ => none

/-- Read the actual stored field first and then dereference its array handle.
The later state is used in the observation, rather than being an unused marker
for hypothetical mutation. This is specification instrumentation only.
-/
def ObserveIRArrayField (heap : IRArrayHeap) (node : LegacyIR.JVal) (field : Nat) :
    JuliaLean.BootCov.R (Option IRArraySnapshot) :=
  (LegacyIR.getfieldObj node field).map (ReadIRArrayIdentity heap)

/-- PhiNode keeps both input array identities, defines both fields, and exposes
the original arrays' current contents through those fields after any subsequent
array-world change. The source constructor does not compare array lengths, so
no SSA well-formedness or equal-length premise is imposed. Both arrays may have
any native-sized length and values may contain arbitrary undefined slots.

The node itself is immutable: base/boot.jl:165-172 and the pinned C identity
model compare its fields. The generated method is inside eval(Core, quote ...
end) at base/boot.jl:699-726, specifically line 720:
PhiNode(edges::Array{Int32, 1}, values::Array{Any, 1}) =
    $(Expr(:new, :PhiNode, :edges, :values)).
Documentation: doc/src/devdocs/ssair.md:69-86.
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def PhiNodeArrayIdentityInvariant : Prop :=
  ∀ (edgeRef valueRef : Nat) (before after : IRArrayHeap),
    (∃ edges, before edgeRef = some (.int32 edges)) →
    (∃ values, before valueRef = some (.any values)) →
    let node := LegacyIR.phiNode (.opaque edgeRef) (.opaque valueRef)
    LegacyIR.getfieldObj node 1 = .ok (.opaque edgeRef) ∧
    LegacyIR.getfieldObj node 2 = .ok (.opaque valueRef) ∧
    LegacyIR.isdefinedObj node 1 = true ∧
    LegacyIR.isdefinedObj node 2 = true ∧
    LegacyIR.getfieldObj node 3 = .error .bounds ∧
    ObserveIRArrayField after node 1 = .ok (after edgeRef) ∧
    ObserveIRArrayField after node 2 = .ok (after valueRef)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem phiNodeArrayIdentityInvariant_proven : PhiNodeArrayIdentityInvariant := by
  unfold PhiNodeArrayIdentityInvariant
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end

/-- PiNode stores both operands in defined Any fields, including when typ is
an AST, an opaque object, or any other Julia value rather than a type object.
The source adds no type assertion or conversion. The third field is absent.
Generated inside eval(Core, quote ... end), base/boot.jl:699-726, line 721:
PiNode(@nospecialize(val), @nospecialize(typ)) =
    $(Expr(:new, :PiNode, :val, :typ)).
Field declarations: base/boot.jl:160-163.
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def PiNodeAnyFieldsInvariant : Prop :=
  ∀ (value typ : LegacyIR.JVal),
    let node := LegacyIR.piNode value typ
    LegacyIR.getfieldObj node 1 = .ok value ∧
    LegacyIR.getfieldObj node 2 = .ok typ ∧
    LegacyIR.isdefinedObj node 1 = true ∧
    LegacyIR.isdefinedObj node 2 = true ∧
    LegacyIR.getfieldObj node 3 = .error .bounds

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem piNodeAnyFieldsInvariant_proven : PiNodeAnyFieldsInvariant := by
  unfold PiNodeAnyFieldsInvariant
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end

/-- PhiCNode keeps its original values-array identity and exposes that same
array in every later world, including changed contents, undefined slots and
resizing. The immutable node has exactly one defined field. No assumptions
about SSA structure or array element values are imposed.
Generated inside eval(Core, quote ... end), base/boot.jl:699-726, line 722:
PhiCNode(values::Array{Any, 1}) = $(Expr(:new, :PhiCNode, :values)).
Field declaration: base/boot.jl:170-172.
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def PhiCNodeArrayIdentityInvariant : Prop :=
  ∀ (valueRef : Nat) (before after : IRArrayHeap),
    (∃ values, before valueRef = some (.any values)) →
    let node := LegacyIR.phiCNode (.opaque valueRef)
    LegacyIR.getfieldObj node 1 = .ok (.opaque valueRef) ∧
    LegacyIR.isdefinedObj node 1 = true ∧
    LegacyIR.getfieldObj node 2 = .error .bounds ∧
    ObserveIRArrayField after node 1 = .ok (after valueRef)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem phiCNodeArrayIdentityInvariant_proven : PhiCNodeArrayIdentityInvariant := by
  unfold PhiCNodeArrayIdentityInvariant
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩
end

def entriesIdentityObjects : List Entry := [
  { id := "boot-box-value-identity"
    juliaFile := "base/boot.jl"
    juliaFns := ["Box(@nospecialize(x))"]
    statement := "Box(x) allocates a fresh mutable identity, retains x exactly in its defined contents field, and preserves every old Box and its contents."
    source := "base/boot.jl:628-632; doc/src/manual/constructors.md:198-203; fresh-allocation and stored-identity invariant"
    status := .proven
    prop := ``BoxWithValueInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.boxWithValueInvariant_proven
    notes := "Uses Models2Group1.boxWithValue, a concrete allocation body with no runtime callback. The carrier includes every Julia value. GC, physical layout and resource exhaustion are abstracted." },
  { id := "boot-box-undefined-identity"
    juliaFile := "base/boot.jl"
    juliaFns := ["Box()"]
    statement := "Box() allocates a fresh mutable identity with an undefined contents field, retaining all pre-existing Boxes unchanged."
    source := "base/boot.jl:628-632; doc/src/manual/constructors.md:198-203,228-246; partial initialization and freshness"
    status := .proven
    prop := ``BoxWithoutValueInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.boxWithoutValueInvariant_proven
    notes := "Uses Models2Group1.boxWithoutValue. Undefined contents is distinct from both an absent Box and a value such as nothing. No user-dispatch or runtime callback is assumed." },
  { id := "boot-phi-array-identities"
    juliaFile := "base/boot.jl"
    juliaFns := ["PhiNode(edges::Array{Int32, 1}, values::Array{Any, 1})"]
    statement := "PhiNode defines both fields with the exact original array identities; reading either through the immutable node observes that array's current contents after arbitrary array-world changes."
    source := "base/boot.jl:165-172,699-726 (generated method at 720); doc/src/devdocs/ssair.md:69-86; constructor field/alias invariant"
    status := .proven
    prop := ``PhiNodeArrayIdentityInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.phiNodeArrayIdentityInvariant_proven
    notes := "Reuses JuliaLean.BootCov.Objects.phiNode. Input arrays use JVal.opaque identities and native-sized observation snapshots. No equal-length premise: the constructor does not enforce SSA well-formedness. Pinned source identifies the node as immutable." },
  { id := "boot-pi-any-fields"
    juliaFile := "base/boot.jl"
    juliaFns := ["PiNode(@nospecialize(val), @nospecialize(typ))"]
    statement := "PiNode defines both Any fields with the exact val and typ inputs, including AST-valued or other non-type typ arguments, without adding a third field."
    source := "base/boot.jl:160-163,699-726 (generated method at 721); raw-new field invariant"
    status := .proven
    prop := ``PiNodeAnyFieldsInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.piNodeAnyFieldsInvariant_proven
    notes := "Reuses JuliaLean.BootCov.Objects.piNode over all JVal operands. No Type-only restriction or arbitrary primitive callback is introduced." },
  { id := "boot-phic-array-identity"
    juliaFile := "base/boot.jl"
    juliaFns := ["PhiCNode(values::Array{Any, 1})"]
    statement := "PhiCNode defines its sole field with the original values-array identity, so later reads through the immutable node observe the same array after arbitrary content or size changes."
    source := "base/boot.jl:170-172,699-726 (generated method at 722); constructor field/alias invariant"
    status := .proven
    prop := ``PhiCNodeArrayIdentityInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.phiCNodeArrayIdentityInvariant_proven
    notes := "Reuses JuliaLean.BootCov.Objects.phiCNode. Native-sized snapshots include every #undef pattern; there is no SSA-domain restriction and no mutable PhiCNode heap is introduced." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot

/-- Observation of UndefVarError's three fields; None means the scope field is
undefined. All other object tags are rejected by the independent observer. -/
def UndefVarFields {L : Type} : Obj L →
    Option (JuliaLean.base.expr.Value L × JuliaLean.base.expr.Value L × Option (JuliaLean.base.expr.Value L))
  | .undefVarError var world scope => some (var, world, scope)
  | _ => none

/-- Both UndefVarError methods retain their Symbol/scope identities, record the
actual current task world at construction, and leave all runtime state intact.
The complete UInt range is included; the one-argument method leaves scope
undefined rather than filling it with nothing. This also registers the concrete
readWorldAge dependency via both calls.
Julia source: base/boot.jl:500-505; field and world-age snapshot invariant. -/
def UndefVarWorldSnapshot : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L)
    (state : JuliaLean.base.boot.Models2Group1.ThreadState W)
    (var scope : JuliaLean.base.expr.Value L),
    let plain := JuliaLean.base.boot.Models2Group1.undefVarErrorCtor ops var state
    let withScope := JuliaLean.base.boot.Models2Group1.undefVarErrorScopeCtor ops var scope state
    plain.2 = state ∧ withScope.2 = state ∧
    UndefVarFields plain.1 = some (var, intV ops state.worldAge, none) ∧
    UndefVarFields withScope.1 = some (var, intV ops state.worldAge, some scope)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem undefVarWorldSnapshot_proven : UndefVarWorldSnapshot := by
  unfold UndefVarWorldSnapshot
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩
end

/-- getptls yields the current task's exact native-width TLS pointer and leaves
its world age and every other state field untouched. The pointer is a concrete
stored value, never an arbitrary callback response.
Julia source: base/boot.jl:617; src/threading.c jl_get_ptls_states. -/
def CurrentTlsPointer : Prop :=
  ∀ (W : Type) (state : JuliaLean.base.boot.Models2Group1.ThreadState W),
    let observed := JuliaLean.base.boot.Models2Group1.getPtls state
    observed.1.addr.val = state.ptls.addr.val ∧ observed.2 = state

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem currentTlsPointer_proven : CurrentTlsPointer := by
  unfold CurrentTlsPointer
  intros
  exact ⟨rfl, rfl⟩
end

def entriesThreadState : List Entry := [
  { id := "boot-undef-var-world", juliaFile := "base/boot.jl"
    juliaFns := ["UndefVarError(var::Symbol)", "UndefVarError(var::Symbol, @nospecialize scope)", "jl_get_tls_world_age (necessary metadata-read dependency)"]
    statement := "UndefVarError retains its payload identities and current native UInt task world, leaves omitted scope undefined, and preserves runtime state."
    source := "base/boot.jl:500-505; current-world snapshot and field-definedness invariants"
    status := .proven, prop := ``UndefVarWorldSnapshot, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.undefVarWorldSnapshot_proven
    notes := "Both public constructors invoke the concrete readWorldAge state read. No runtime callback, conversion law, or unbounded replacement for UInt is assumed." },
  { id := "boot-current-tls-pointer", juliaFile := "base/boot.jl"
    juliaFns := ["getptls()"]
    statement := "getptls returns the current task's exact native TLS pointer and preserves every runtime-state field."
    source := "base/boot.jl:617; pinned src/threading.c jl_get_ptls_states, preserved in JuliaLean/src/threading_c.lean:63-67"
    status := .proven, prop := ``CurrentTlsPointer, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.currentTlsPointer_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry
open JuliaLean.base.boot.Models2Group1

/-!
Independent observations for all three TypeVar constructors. Success is
specified by freshness, heap preservation, initialized field observations, and
the supplied/default bound identities. Failure is specified by the existing
TypeError class, actual context/expected/got fields, and unchanged heap. No
property assumes a callee's correctness or a subtype relation between bounds.
The initial heap validity predicates allow sharing, cycles, arbitrary mutable
bound contents, and undefined fields; only references must denote existing
objects. Source Symbol validity is carried by TypeVarName itself.
-/

/-- A value's references denote existing TypeVars. This representation invariant
does not inspect bounds or rule out cycles. -/
def TypeVarValueValid {L : Type} (heap : TypeVarHeap L) : TypeVarValue L → Prop
  | .typevarRef ref => ref < heap.cells.length
  | _ => True

/-- All initialized bound references in a heap denote existing objects.
Undefined fields are allowed, and bound contents need not themselves be valid
types: jl_is_typevar checks the object's runtime kind without reading them. -/
def TypeVarHeapValid {L : Type} (heap : TypeVarHeap L) : Prop :=
  ∀ cell, cell ∈ heap.cells →
    (∀ value, cell.lower = some value → TypeVarValueValid heap value) ∧
    (∀ value, cell.upper = some value → TypeVarValueValid heap value)

/-- The independent accepted-bound set: Julia type values and TypeVar objects.
It includes types with free variables and does not relate lower and upper
bounds. TypeApp and arbitrary ordinary values are outside this set. -/
def TypeVarAdmissible {L : Type} (value : TypeVarValue L) : Prop :=
  value = .bottom ∨ value = .anyType ∨
    (∃ payload, value = .typeValue payload) ∨
    (∃ ref, value = .typevarRef ref)

/-- Specification observation of a logical TypeVar object's fields. Nat is an
object identifier, not a Julia numeric value or a Julia indexing operation. -/
def typeVarCellAt {L : Type} (heap : TypeVarHeap L) (ref : Nat) :
    Option (TypeVarCell L) := heap.cells[ref]?

/-- Constructor execution does not mutate pre-existing TypeVar objects. -/
def TypeVarOldCellsPreserved {L : Type} (before after : TypeVarHeap L) : Prop :=
  ∀ ref, ref < before.cells.length → typeVarCellAt after ref = typeVarCellAt before ref

/-- Independent allocation and field observations of a constructor result.
There is exactly one fresh TypeVar, its name and both bounds are defined and
equal to the expected original references, and all earlier cells are unchanged.
The formula does not specify the allocator's list-append implementation. -/
def HasFreshTypeVar {L : Type} (before : TypeVarHeap L)
    (result : Except (TypeVarError L) (TypeVarValue L) × TypeVarHeap L)
    (name : TypeVarName) (lower upper : TypeVarValue L) : Prop :=
  ∃ ref cell after,
    result = (.ok (.typevarRef ref), after) ∧
    before.cells.length ≤ ref ∧ ref < after.cells.length ∧
    after.cells.length = before.cells.length + 1 ∧
    typeVarCellAt after ref = some cell ∧
    cell.name = some name ∧ cell.lower = some lower ∧ cell.upper = some upper ∧
    TypeVarOldCellsPreserved before after ∧ TypeVarHeapValid after

/-- Independent exception observations. The post-error heap equals the original
heap: no validation failure can allocate a TypeVar or mutate an existing one. -/
def HasTypeVarError {L : Type} (before : TypeVarHeap L)
    (result : Except (TypeVarError L) (TypeVarValue L) × TypeVarHeap L)
    (func context : String) (expected : TypeVarExpected) (got : TypeVarValue L) : Prop :=
  ∃ error after,
    result = (.error error, after) ∧
    error.exception = JuliaLean.BootCov.Exc.typeError func ∧
    error.context = context ∧ error.expected = expected ∧ error.got = got ∧
    after = before

/-- A Symbol-only TypeVar constructor allocates a fresh mutable identity with
fully initialized name, bottom lower bound, and Any upper bound.
Julia source: base/boot.jl:370; runtime allocation src/builtins.c:2210-2224.
The property depends on newTypeVar and typeVarAssertName and covers their
successful primitive/type-assertion paths. -/
def TypeVarOneArgumentFields : Prop :=
  ∀ (L : Type) (heap : TypeVarHeap L) (name : TypeVarName),
    TypeVarHeapValid heap →
    HasFreshTypeVar heap (typeVar1 (.symbol name) heap) name .bottom .anyType

/-- The two-argument TypeVar constructor retains every accepted upper bound,
including existing mutable TypeVars and types with free variables, and defaults
the lower bound to bottom. It changes no pre-existing object.
Julia source: base/boot.jl:371; src/builtins.c:2210-2224. -/
def TypeVarTwoArgumentFields : Prop :=
  ∀ (L : Type) (heap : TypeVarHeap L) (name : TypeVarName) (upper : TypeVarValue L),
    TypeVarHeapValid heap → TypeVarValueValid heap upper → TypeVarAdmissible upper →
    HasFreshTypeVar heap (typeVar2 (.symbol name) upper heap) name .bottom upper

/-- Every pair of accepted lower/upper bound objects is preserved in a fresh
TypeVar. There is no subtype, consistency, or free-variable premise. Existing
TypeVar bound identities, sharing, cycles, and their current fields survive.
Julia source: base/boot.jl:372; src/builtins.c:2210-2224. -/
def TypeVarThreeArgumentFields : Prop :=
  ∀ (L : Type) (heap : TypeVarHeap L) (name : TypeVarName)
    (lower upper : TypeVarValue L),
    TypeVarHeapValid heap → TypeVarValueValid heap lower → TypeVarValueValid heap upper →
    TypeVarAdmissible lower → TypeVarAdmissible upper →
    HasFreshTypeVar heap (typeVar3 (.symbol name) lower upper heap) name lower upper

/-- Every nonsymbol name fails with the name's TypeError before either supplied
bound is considered, for all three methods. In particular a bad bound cannot
change the error context or cause allocation first.
Julia source: base/boot.jl:370-372; invariant of the explicit n::Symbol assertion. -/
def TypeVarNameErrorPrecedence : Prop :=
  ∀ (L : Type) (heap : TypeVarHeap L) (name lower upper : TypeVarValue L),
    TypeVarHeapValid heap → TypeVarValueValid heap name →
    TypeVarValueValid heap lower → TypeVarValueValid heap upper →
    (∀ symbol, name ≠ .symbol symbol) →
    HasTypeVarError heap (typeVar1 name heap) "typeassert" "" .symbol name ∧
    HasTypeVarError heap (typeVar2 name upper heap) "typeassert" "" .symbol name ∧
    HasTypeVarError heap (typeVar3 name lower upper heap) "typeassert" "" .symbol name

/-- Bound validation rejects exactly ordinary non-type/non-TypeVar values,
including TypeApp, with the correct first failing bound and original offending
value. A bad lower bound wins even when the upper bound is bad too; rejected
upper bounds are reported only after a valid lower bound. No failure allocates.
Julia source: base/boot.jl:371-372; src/builtins.c:2210-2224. This property covers
the concrete newTypeVar validation helpers and both failure paths. -/
def TypeVarBoundErrorPrecedence : Prop :=
  ∀ (L : Type) (heap : TypeVarHeap L) (name : TypeVarName)
    (lower upper : TypeVarValue L),
    TypeVarHeapValid heap → TypeVarValueValid heap lower → TypeVarValueValid heap upper →
    (¬TypeVarAdmissible lower →
      HasTypeVarError heap (typeVar3 (.symbol name) lower upper heap)
        "TypeVar" "lower bound" .type lower) ∧
    (TypeVarAdmissible lower → ¬TypeVarAdmissible upper →
      HasTypeVarError heap (typeVar3 (.symbol name) lower upper heap)
        "TypeVar" "upper bound" .type upper) ∧
    (¬TypeVarAdmissible upper →
      HasTypeVarError heap (typeVar2 (.symbol name) upper heap)
        "TypeVar" "upper bound" .type upper)

/-- Registry entries for the three complete public methods and the concrete
runtime/type-assertion helpers on which their properties depend. -/
def typeVarEntries : List Entry := [
  { id := "boot-typevar-one-fields", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar(@nospecialize(n))"]
    statement := "For every Symbol name, TypeVar allocates one fresh mutable object, preserves the name, initializes bottom/Any bounds, and leaves all old heap cells unchanged."
    source := "base/boot.jl:370; src/builtins.c:2210-2224; independent freshness and stored-field invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeVarOneArgumentFields
    notes := "Covers newTypeVar and typeVarAssertName dependencies. Logical allocation; no physical resource-exhaustion model. No proofs supplied." },
  { id := "boot-typevar-two-fields", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar(@nospecialize(n), @nospecialize(ub))"]
    statement := "TypeVar with an upper bound allocates fresh identity, defaults its lower bound to bottom, and preserves every accepted upper bound including existing TypeVar references and types with free variables."
    source := "base/boot.jl:371; src/builtins.c:2210-2224; independent field/identity invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeVarTwoArgumentFields
    notes := "No subtype or free-variable restriction; input validity is only the representation invariant. Covers the concrete runtime helper." },
  { id := "boot-typevar-three-fields", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub))"]
    statement := "TypeVar preserves both accepted bound objects and the Symbol name in a fully initialized fresh mutable object, with no subtype condition and no mutation of pre-existing objects."
    source := "base/boot.jl:372; src/builtins.c:2210-2224; independent field/freshness invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeVarThreeArgumentFields
    notes := "Covers all accepted runtime kinds, free variables, bound aliases, cycles, and the newTypeVar dependency." },
  { id := "boot-typevar-name-error-order", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar(@nospecialize(n))", "TypeVar(@nospecialize(n), @nospecialize(ub))",
      "TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub))"]
    statement := "A nonsymbol TypeVar name raises the original typeassert TypeError before any bound validation, with its original offending value and no heap change."
    source := "base/boot.jl:370-372; invariant of n::Symbol evaluation order"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeVarNameErrorPrecedence
    notes := "Covers typeVarAssertName and all three public methods; original exception class and context retained." },
  { id := "boot-typevar-bound-error-order", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar(@nospecialize(n), @nospecialize(ub))",
      "TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub))"]
    statement := "TypeVar rejects non-type/non-TypeVar bounds, including TypeApp, in lower-before-upper order with the correct original offending value, TypeError context and unchanged heap."
    source := "base/boot.jl:371-372; src/builtins.c:2210-2224"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeVarBoundErrorPrecedence
    notes := "Explicitly fixes the legacy isBound acceptance of TypeApp. Covers newTypeVar and its concrete runtime-kind predicates; no callee laws." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1
open JuliaLean.Registry

/-!
Field, exception, and effect-trace contracts for the generic constructors.
All dispatch callbacks are arbitrary functions in the existing CoreM, including
state changes, errors, and Option.none divergence. No callback law or totality
assumption is made. Instrumentation records the actual calls and their actual
outcomes; specifications inspect that trace rather than reevaluating a model.

When execution diverges, there is no observable final state or trace. The
properties instead require a reachable dispatched call that itself diverges.
Thus the contracts also reject spurious divergence introduced by a constructor.
-/

/-- Independent description of the fixed field types in `base/boot.jl:518-535`.
This predicate does not use constructorFieldAccepts or a caller-supplied isa law. -/
def SourceFieldFits {L : Type} (target : ConstructorFieldTarget)
    (input : ClassifiedConstructorValue L) : Prop :=
  match target with
  | .abstractString => input.kind = .abstractString
  | .symbol => input.kind = .symbol
  | .context => input.kind = .abstractString ∨ input.kind = .globalRef ∨ input.kind = .symbol

/-- An externally dispatched call, recording the actual source arguments. -/
inductive GenericConstructorCall (L : Type) where
  | convert (target : ConstructorFieldTarget) (argument : ClassifiedConstructorValue L)
  | symbol (argument : ClassifiedConstructorValue L)

/-- The observable outcome and state transition of one dispatched call. -/
inductive GenericConstructorEvent (W L : Type) where
  | returned (call : GenericConstructorCall L) (value : ClassifiedConstructorValue L)
      (before after : W)
  | raised (call : GenericConstructorCall L) (error : JuliaLean.base.expr.Value L)
      (before after : W)

/-- Instrument an arbitrary CoreM callback. Divergence remains none; a completed
call records its unchanged returned value or exception and its actual state change. -/
def observeGenericConstructorCall {W L : Type} (call : GenericConstructorCall L)
    (action : CoreM W L (ClassifiedConstructorValue L)) :
    CoreM (W × List (GenericConstructorEvent W L)) L (ClassifiedConstructorValue L) :=
  fun (before, trace) =>
    match action before with
    | none => none
    | some (.ok (value, after)) =>
        some (.ok (value, (after, trace ++ [.returned call value before after])))
    | some (.error (error, after)) =>
        some (.error (error, (after, trace ++ [.raised call error before after])))

/-- Observe every source dispatch while leaving the callback behavior unrestricted. -/
def observeGenericConstructorDispatch {W L : Type}
    (dispatch : GenericConstructorDispatch (CoreM W L) L) :
    GenericConstructorDispatch (CoreM (W × List (GenericConstructorEvent W L)) L) L where
  convert target argument :=
    observeGenericConstructorCall (.convert target argument) (dispatch.convert target argument)
  symbol argument := observeGenericConstructorCall (.symbol argument) (dispatch.symbol argument)

/-- Field observations on a DomainError result; a different constructor fails. -/
def DomainErrorStores {L : Type} (object : Obj L)
    (original message : JuliaLean.base.expr.Value L) : Prop :=
  match object with
  | .domainError storedValue storedMessage =>
      storedValue = original ∧ storedMessage = message
  | _ => False

/-- Independent named-field observations on a TypeError result. -/
def TypeErrorStores {L : Type} (object : Obj L)
    (func context expected got : JuliaLean.base.expr.Value L) : Prop :=
  match object with
  | .typeError storedFunc storedContext storedExpected storedGot =>
      storedFunc = func ∧ storedContext = context ∧
      storedExpected = expected ∧ storedGot = got
  | _ => False

/-- The exact raw-new TypeError exception contract. The expected type and
rejected returned value are observations, not laws imposed on any conversion. -/
def NewFieldException {W L : Type} (encoding : GenericConstructorEncoding W L)
    (expectedType got error : JuliaLean.base.expr.Value L) : Prop :=
  error = objV encoding.runtime
    (.typeError (.symbol "new") (strV encoding.runtime "") expectedType got)

/-- Evidence for an initialized field value from its observable dispatch trace.
An input already in the field type has no conversion event and no state change.
Otherwise exactly its target conversion returned the observed value. -/
def PreparedFieldTrace {W L : Type} (target : ConstructorFieldTarget)
    (input : ClassifiedConstructorValue L) (before : W)
    (prepared : ClassifiedConstructorValue L) (after : W)
    (trace : List (GenericConstructorEvent W L)) : Prop :=
  (SourceFieldFits target input ∧ prepared = input ∧ after = before ∧ trace = []) ∨
  (¬SourceFieldFits target input ∧
    trace = [.returned (.convert target input) prepared before after])

/-- A field conversion's own exception, including its final state, is propagated. -/
def FailedFieldTrace {W L : Type} (target : ConstructorFieldTarget)
    (input : ClassifiedConstructorValue L) (before : W)
    (error : JuliaLean.base.expr.Value L) (after : W)
    (trace : List (GenericConstructorEvent W L)) : Prop :=
  ¬SourceFieldFits target input ∧
    trace = [.raised (.convert target input) error before after]

/-- All finite DomainError observations: stored original value, correctly typed
message, unchanged accepted input, preserved callback errors, or an accurately
reported wrong-type conversion result. This does not call a constructor model. -/
def DomainErrorTraceContract {W L : Type} (encoding : GenericConstructorEncoding W L)
    (val : JuliaLean.base.expr.Value L) (msg : ClassifiedConstructorValue L) (before : W)
    (result : Except (JuliaLean.base.expr.Value L × W) (Obj L × W))
    (trace : List (GenericConstructorEvent W L)) : Prop :=
  match result with
  | .ok (object, after) =>
      ∃ prepared,
        PreparedFieldTrace .abstractString msg before prepared after trace ∧
        SourceFieldFits .abstractString prepared ∧
        DomainErrorStores object val prepared.value
  | .error (error, after) =>
      FailedFieldTrace .abstractString msg before error after trace ∨
      ∃ prepared,
        PreparedFieldTrace .abstractString msg before prepared after trace ∧
        ¬SourceFieldFits .abstractString prepared ∧
        NewFieldException encoding (coreV encoding.runtime "AbstractString") prepared.value error

/-- All finite TypeError observations. Conversion events for func precede those
for context. Both successful conversion expressions are present before any
raw-new rejection, even if func's conversion returned the wrong type. Source
callback errors take priority over subsequent raw-new checks; after both
expressions return, the first incompatible field determines the exception. -/
def TypeErrorTraceContract {W L : Type} (encoding : GenericConstructorEncoding W L)
    (func context : ClassifiedConstructorValue L)
    (expected got : JuliaLean.base.expr.Value L) (before : W)
    (result : Except (JuliaLean.base.expr.Value L × W) (Obj L × W))
    (trace : List (GenericConstructorEvent W L)) : Prop :=
  match result with
  | .ok (object, after) =>
      ∃ preparedFunc preparedContext middle funcTrace contextTrace,
        PreparedFieldTrace .symbol func before preparedFunc middle funcTrace ∧
        PreparedFieldTrace .context context middle preparedContext after contextTrace ∧
        trace = funcTrace ++ contextTrace ∧
        SourceFieldFits .symbol preparedFunc ∧
        SourceFieldFits .context preparedContext ∧
        TypeErrorStores object preparedFunc.value preparedContext.value expected got
  | .error (error, after) =>
      FailedFieldTrace .symbol func before error after trace ∨
      (∃ preparedFunc middle funcTrace contextTrace,
        PreparedFieldTrace .symbol func before preparedFunc middle funcTrace ∧
        FailedFieldTrace .context context middle error after contextTrace ∧
        trace = funcTrace ++ contextTrace) ∨
      (∃ preparedFunc preparedContext middle funcTrace contextTrace,
        PreparedFieldTrace .symbol func before preparedFunc middle funcTrace ∧
        PreparedFieldTrace .context context middle preparedContext after contextTrace ∧
        trace = funcTrace ++ contextTrace ∧
        ((¬SourceFieldFits .symbol preparedFunc ∧
          NewFieldException encoding (coreV encoding.runtime "Symbol") preparedFunc.value error) ∨
         (SourceFieldFits .symbol preparedFunc ∧ ¬SourceFieldFits .context preparedContext ∧
          NewFieldException encoding encoding.contextType preparedContext.value error)))

/-- A reachable successful field-expression outcome, used only to identify the
state in which a later dispatch might diverge. This states an actual callback
outcome, not a correctness law or a constructor-success hypothesis. -/
def PreparedFieldRun {W L : Type} (dispatch : GenericConstructorDispatch (CoreM W L) L)
    (target : ConstructorFieldTarget) (input : ClassifiedConstructorValue L) (before : W)
    (prepared : ClassifiedConstructorValue L) (after : W) : Prop :=
  (SourceFieldFits target input ∧ prepared = input ∧ after = before) ∨
  (¬SourceFieldFits target input ∧
    dispatch.convert target input before = some (.ok (prepared, after)))

/-- The only possible source of divergence in the DomainError body. -/
def DomainErrorDispatchDiverges {W L : Type}
    (dispatch : GenericConstructorDispatch (CoreM W L) L)
    (msg : ClassifiedConstructorValue L) (before : W) : Prop :=
  ¬SourceFieldFits .abstractString msg ∧ dispatch.convert .abstractString msg before = none

/-- TypeError can diverge only in a required conversion reached after earlier
field expressions returned. A wrong-typed first result still reaches context. -/
def TypeErrorDispatchDiverges {W L : Type}
    (dispatch : GenericConstructorDispatch (CoreM W L) L)
    (func context : ClassifiedConstructorValue L) (before : W) : Prop :=
  (¬SourceFieldFits .symbol func ∧ dispatch.convert .symbol func before = none) ∨
  ∃ preparedFunc middle,
    PreparedFieldRun dispatch .symbol func before preparedFunc middle ∧
    ¬SourceFieldFits .context context ∧ dispatch.convert .context context middle = none

/-- DomainError preserves its value and accepted message; custom conversion
results, exceptions, state changes, and divergence obey the field-type contract.
All input classes and all dispatch callbacks are quantified without laws.
Julia source/invariant: `base/boot.jl:518-523`; `base/essentials.jl:1468-1488`. -/
def GenericDomainErrorSemantics : Prop :=
  ∀ (W L : Type) (encoding : GenericConstructorEncoding W L)
    (dispatch : GenericConstructorDispatch (CoreM W L) L)
    (val : JuliaLean.base.expr.Value L) (msg : ClassifiedConstructorValue L) (before : W),
    match domainErrorCtor encoding (observeGenericConstructorDispatch dispatch) val msg
      (before, []) with
    | none => DomainErrorDispatchDiverges dispatch msg before
    | some (.ok (object, (after, trace))) =>
        DomainErrorTraceContract encoding val msg before (.ok (object, after)) trace
    | some (.error (error, (after, trace))) =>
        DomainErrorTraceContract encoding val msg before (.error (error, after)) trace

/-- TypeError preserves expected/got, conditionally converts func/context in
source order, and delays raw-new checks until both field expressions return.
Custom errors, state, and possible divergence are retained without callback laws.
Julia source/invariant: `base/boot.jl:524-535`; `base/essentials.jl:1468-1488`. -/
def GenericTypeErrorSemantics : Prop :=
  ∀ (W L : Type) (encoding : GenericConstructorEncoding W L)
    (dispatch : GenericConstructorDispatch (CoreM W L) L)
    (func context : ClassifiedConstructorValue L)
    (expected got : JuliaLean.base.expr.Value L) (before : W),
    match typeErrorCtor encoding (observeGenericConstructorDispatch dispatch)
      func context expected got (before, []) with
    | none => TypeErrorDispatchDiverges dispatch func context before
    | some (.ok (object, (after, trace))) =>
        TypeErrorTraceContract encoding func context expected got before (.ok (object, after)) trace
    | some (.error (error, (after, trace))) =>
        TypeErrorTraceContract encoding func context expected got before (.error (error, after)) trace

/-- Independent generic-constructor properties, all intentionally unproved. -/
def genericConstructorEntries : List Entry := [
  { id := "boot-generic-domain-error", juliaFile := "base/boot.jl"
    juliaFns := ["DomainError(@nospecialize(val), @nospecialize(msg))"]
    statement := "DomainError preserves val; an accepted AbstractString message bypasses conversion. Otherwise it preserves the exact custom conversion call, effects, exceptions and divergence, stores an accepted returned message, or reports a raw-new TypeError with the returned wrong value."
    source := "base/boot.jl:518-523; field-storage and effect invariant; base/essentials.jl:1468-1488"
    status := .todo
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.GenericDomainErrorSemantics, thm := none },
  { id := "boot-generic-type-error", juliaFile := "base/boot.jl"
    juliaFns := ["TypeError(func, context, @nospecialize(expected::Type), @nospecialize(got))"]
    statement := "TypeError retains expected and got, bypasses unnecessary conversion, evaluates required func and context conversions in order before raw-new checks, preserves custom errors/state/divergence, and reports the first incompatible prepared field with the correct expected type and returned value."
    source := "base/boot.jl:524-535; field/evaluation-order invariant; base/essentials.jl:1468-1488"
    status := .todo
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.GenericTypeErrorSemantics, thm := none },
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1
open JuliaLean.Registry

/-- Independent observation of the defined native-Int line field. Its type
test follows the LineNumberNode layout at `base/boot.jl:133-136`. -/
def lineNumberObservedLine {L : Type} : JuliaLean.base.expr.Value L → Option (JInt .i64)
  | .lineNumberNode line _ => some line
  | _ => none

/-- Independent observation of the defined file field in a LineNumberNode. -/
def lineNumberObservedFile {L : Type} :
    JuliaLean.base.expr.Value L → Option (JuliaLean.base.expr.Value L)
  | .lineNumberNode _ file => some file
  | _ => none

/-- Success must have the correct constructor and both defined fields,
observed separately rather than rebuilding the expected result. -/
def HasLineNumberFields {L : Type}
    (result : Except (LineNumberError L) (JuliaLean.base.expr.Value L))
    (line : JInt .i64) (file : JuliaLean.base.expr.Value L) : Prop :=
  ∃ node, result = .ok node ∧ lineNumberObservedLine node = some line ∧
    lineNumberObservedFile node = some file

/-- A TypeError's independent named-field observations, from its source
layout at `base/boot.jl:524-536`. All four fields must be defined. -/
def lineNumberTypeErrorFields {L : Type} : Obj L →
    List (String × JuliaLean.base.expr.Value L)
  | .typeError func context expected got =>
      [("func", func), ("context", context), ("expected", expected), ("got", got)]
  | _ => []

/-- Symbols retain their original identity/payload and nothing stays the
singleton; every native Int, including zero and negative lines, is preserved.
Source invariant: `base/boot.jl:711-714`; location representation is documented
in `doc/src/devdocs/ast.md`, Line numbers. -/
def LineNumberSymbolFields : Prop :=
  ∀ (W L : Type) (encoding : LineNumberEncoding W L) (line : JInt .i64)
    (symbol : JuliaLean.base.expr.Value L),
    HasLineNumberFields (lineNumberNode2Ctor encoding line (.symbol symbol)) line symbol ∧
    HasLineNumberFields (lineNumberNode2Ctor encoding line .nothing) line
      (nothingV encoding.runtime)

/-- Every NUL-free concrete String is stored as the interned Symbol with
exactly its original bytes, including empty and invalid-UTF-8 Strings. The line
is unchanged. All pure representations are quantified without correctness
laws. This registered property depends on lineNumberSymbol and the installed
symbolOfString/symbolN dependencies. Source: `base/boot.jl:711-714,864-868`. -/
def LineNumberStringBytes : Prop :=
  ∀ (W L : Type) (encoding : LineNumberEncoding W L) (line : JInt .i64)
    (s : LineNumberString),
    (0 : UInt8) ∉ s.bytes →
    HasLineNumberFields (lineNumberNode2Ctor encoding line (.string s)) line
      (encoding.symbolBytes (s.bytes.map UInt8.toNat))

/-- A concrete String containing any NUL byte raises ArgumentError during
Symbol construction. It must not reach the raw-new TypeError path or produce
a node. Quantification includes NUL at every position and invalid UTF-8.
Source: `base/boot.jl:711-714,864-868`; installed symbolOfString/symbolN rule. -/
def LineNumberStringNulError : Prop :=
  ∀ (W L : Type) (encoding : LineNumberEncoding W L) (line : JInt .i64)
    (s : LineNumberString),
    (0 : UInt8) ∈ s.bytes →
    ∃ error message, lineNumberNode2Ctor encoding line (.string s) = .error error ∧
      error.exception = .argument message ∧ error.typeErrorPayload = none

/-- Every file outside String/Symbol/Nothing, including custom AbstractString
subtypes, fails the raw-new file check. The TypeError identifies new, the fixed
Union{Symbol,Nothing} field type, and the unchanged original offending object.
Source: `base/boot.jl:133-136,711-714`. -/
def LineNumberInvalidFileError : Prop :=
  ∀ (W L : Type) (encoding : LineNumberEncoding W L) (line : JInt .i64)
    (file : JuliaLean.base.expr.Value L),
    ∃ error payload,
      lineNumberNode2Ctor encoding line (.other file) = .error error ∧
      error.exception = .typeError "new" ∧ error.typeErrorPayload = some payload ∧
      (lineNumberTypeErrorFields payload).length = 4 ∧
      (lineNumberTypeErrorFields payload).lookup "func" = some (.symbol "new") ∧
      (lineNumberTypeErrorFields payload).lookup "context" = some (strV encoding.runtime "") ∧
      (lineNumberTypeErrorFields payload).lookup "expected" = some encoding.fileType ∧
      (lineNumberTypeErrorFields payload).lookup "got" = some file

/-- Registered independent coverage for row 711 and its reused concrete
String-to-Symbol dependency. No proofs or callee-correctness assumptions. -/
def lineNumberEntries : List Entry := [
  { id := "boot-line-number-symbol-fields", juliaFile := "base/boot.jl"
    juliaFns := ["LineNumberNode(l::Int, @nospecialize(f))"]
    statement := "LineNumberNode retains every native Int line and stores Symbol file objects unchanged, with nothing accepted as the singleton file value."
    source := "base/boot.jl:133-136,711-714; doc/src/devdocs/ast.md, Line numbers; independent field invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.LineNumberSymbolFields
    notes := "Full Symbol/Nothing cases; original payloads and aliases retained. All pure encodings are quantified." },
  { id := "boot-line-number-string-bytes", juliaFile := "base/boot.jl"
    juliaFns := ["LineNumberNode(l::Int, @nospecialize(f))"]
    statement := "A NUL-free concrete String file becomes the Symbol with exactly its original bytes, including empty and invalid-UTF-8 names, while the native Int line is retained."
    source := "base/boot.jl:711-714,864-868; byte and stored-field invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.LineNumberStringBytes
    notes := "Registers the lineNumberSymbol helper dependency; calls installed BootCov.Arrays.symbolOfString and symbolN on native-sized UInt8 input bytes." },
  { id := "boot-line-number-nul-error", juliaFile := "base/boot.jl"
    juliaFns := ["LineNumberNode(l::Int, @nospecialize(f))"]
    statement := "A concrete String containing NUL raises ArgumentError in Symbol construction, before any raw-new TypeError or node result."
    source := "base/boot.jl:711-714,864-868; installed Symbol NUL rejection invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.LineNumberStringNulError
    notes := "Full NUL-error domain; depends on lineNumberSymbol and its concrete installed Symbol helper. No Unicode-validity premise." },
  { id := "boot-line-number-file-type-error", juliaFile := "base/boot.jl"
    juliaFns := ["LineNumberNode(l::Int, @nospecialize(f))"]
    statement := "All other file values fail the raw-new check with TypeError(:new, empty context, Union{Symbol,Nothing}, original value), retaining the exact offending object."
    source := "base/boot.jl:133-136,711-714; raw-new field invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.LineNumberInvalidFileError
    notes := "Includes custom AbstractString subtypes; no generic conversion, isa, or fieldtype callback. Exception class and transparent fields retained." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

/-- The internal first-argument helper loses no value distinctions, is
idempotent, and is insensitive to every native-sized tail. These algebraic
invariants characterize the projection independently of its one-line body.
Source: base/boot.jl:951. -/
def FirstArgumentProjection : Prop :=
  ∀ (L : Type) (x y : JuliaLean.base.expr.Value L)
    (tail otherTail : List (JuliaLean.base.expr.Value L)),
    tail.length < IntTy.i64.max.toNat → otherTail.length < IntTy.i64.max.toNat →
    (firstarg x tail = firstarg y tail ↔ x = y) ∧
    firstarg (firstarg x tail) tail = firstarg x tail ∧
    firstarg x tail = firstarg x otherTail

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem firstArgumentProjection_proven : FirstArgumentProjection := by
  unfold FirstArgumentProjection
  intros
  exact ⟨Iff.rfl, rfl, rfl⟩
end

/-- The two immutable stream marker constructors denote distinct singleton
types; their results carry no mutable identity or user-provided data.
Source: base/boot.jl:973-978. -/
def CoreStreamMarkers : Prop :=
  JuliaLean.BootCov.Misc.coreSTDOUT ≠ JuliaLean.BootCov.Misc.coreSTDERR ∧
  (∀ stream : JuliaLean.BootCov.Misc.CoreIO,
    stream = JuliaLean.BootCov.Misc.coreSTDOUT ∨
    stream = JuliaLean.BootCov.Misc.coreSTDERR)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem coreStreamMarkers_proven : CoreStreamMarkers := by
  constructor
  · decide
  · intro stream
    cases stream <;> simp [JuliaLean.BootCov.Misc.coreSTDOUT, JuliaLean.BootCov.Misc.coreSTDERR]
end

/-- Observe exactly one arbitrary dispatched call when the caller discards a
successful callee return. Termination, thrown values, state, target, arguments
and trace cardinality remain observable. There is no law on the callee. -/
def DiscardedCallObservation {W L : Type}
    (trace : List (Invocation L)) (event : Invocation L)
    (returned : JuliaLean.base.expr.Value L)
    (untraced : Option (Except (JuliaLean.base.expr.Value L × W)
      (JuliaLean.base.expr.Value L × W)))
    (traced : Option (Except
      (JuliaLean.base.expr.Value L × (W × List (Invocation L)))
      (JuliaLean.base.expr.Value L × (W × List (Invocation L))))) : Prop :=
  match untraced, traced with
  | none, none => True
  | some (.ok (_, world)), some (.ok (value', (world', trace'))) =>
      value' = returned ∧ world' = world ∧ trace' = trace ++ [event]
  | some (.error (error, world)), some (.error (error', (world', trace'))) =>
      error' = error ∧ world' = world ∧ trace' = trace ++ [event]
  | _, _ => False

/-- Instrument the generic write/show boundary, leaving all dispatch targets
arbitrary in the existing CoreM (including errors, state and divergence). -/
def observePrinting {W L : Type} (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L)) :
    JuliaLean.base.boot.Models2Group1.PrintingDispatch
      (CoreM (W × List (Invocation L)) L) L where
  write io x := recordCall dispatch (coreV encoding "write") [io, x]
  showValue io x := recordCall dispatch (coreV encoding "show") [io, x]

/-- print on a String makes one unchanged-argument write call on the actual IO;
it returns nothing on success and retains any error, divergence and state effect.
The opaque x ranges over all source Strings, including invalid UTF-8 bytes.
Source: base/boot.jl:998; output-dispatch invariant. -/
def PrintStringDispatch : Prop :=
  ∀ (W L : Type) (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (io x : JuliaLean.base.expr.Value L) (world : W) (trace : List (Invocation L)),
    DiscardedCallObservation trace (coreV encoding "write", [io, x])
      (nothingV encoding) (dispatch (coreV encoding "write") [io, x] world)
      (JuliaLean.base.boot.Models2Group1.printString encoding
        (observePrinting encoding dispatch) io x (world, trace))

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem printStringDispatch_proven : PrintStringDispatch := by
  intro W L encoding dispatch io x world trace
  unfold printString observePrinting recordCall
  cases h : dispatch (coreV encoding "write") [io, x] world with
  | none => simp [h, DiscardedCallObservation, Bind.bind]
  | some outcome =>
    cases outcome with
    | error error => rcases error with ⟨error, after⟩; simp [h, DiscardedCallObservation, Bind.bind]
    | ok result => rcases result with ⟨value, after⟩; simp [h, DiscardedCallObservation, Bind.bind, Pure.pure]
end

/-- The Any print fallback forwards exactly one show invocation, preserving
its returned value as well as arbitrary error, divergence and state effects.
All IO subtypes and value types are included without callback laws.
Source: base/boot.jl:999; forwarding and effect-order invariant. -/
def PrintAnyDispatch : Prop :=
  ∀ (W L : Type) (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (io x : JuliaLean.base.expr.Value L) (world : W) (trace : List (Invocation L)),
    OneCallObservation trace (coreV encoding "show", [io, x])
      (dispatch (coreV encoding "show") [io, x] world)
      (JuliaLean.base.boot.Models2Group1.printAny (observePrinting encoding dispatch)
        io x (world, trace))

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem printAnyDispatch_proven : PrintAnyDispatch := by
  intro W L encoding dispatch io x world trace
  unfold printAny observePrinting recordCall
  cases h : dispatch (coreV encoding "show") [io, x] world with
  | none => simp [h, OneCallObservation]
  | some outcome =>
    cases outcome with
    | error error => rcases error with ⟨error, after⟩; simp [h, OneCallObservation]
    | ok result => rcases result with ⟨value, after⟩; simp [h, OneCallObservation]
end

/-- println(IO) writes precisely the native UInt8 line-feed through the actual
IO's dispatch, returns nothing on success, and propagates every other outcome.
Source: base/boot.jl:1001; newline and dispatch invariant. -/
def PrintlnByteDispatch : Prop :=
  ∀ (W L : Type) (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (io : JuliaLean.base.expr.Value L) (world : W) (trace : List (Invocation L)),
    let newline := intV encoding (JInt.lit .u8 10)
    DiscardedCallObservation trace (coreV encoding "write", [io, newline])
      (nothingV encoding) (dispatch (coreV encoding "write") [io, newline] world)
      (JuliaLean.base.boot.Models2Group1.printlnIO encoding
        (observePrinting encoding dispatch) io (world, trace))

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem printlnByteDispatch_proven : PrintlnByteDispatch := by
  intro W L encoding dispatch io world trace
  unfold printlnIO observePrinting recordCall
  cases h : dispatch (coreV encoding "write") [io, intV encoding (JInt.lit .u8 10)] world with
  | none => simp [h, DiscardedCallObservation, Bind.bind]
  | some outcome =>
    cases outcome with
    | error error => rcases error with ⟨error, after⟩; simp [h, DiscardedCallObservation, Bind.bind]
    | ok result => rcases result with ⟨value, after⟩; simp [h, DiscardedCallObservation, Bind.bind, Pure.pure]
end

def entriesDocsPrinting : List Entry := [
  { id := "boot-first-argument-projection", juliaFile := "base/boot.jl"
    juliaFns := ["firstarg(arg1, args...)"]
    statement := "firstarg is injective and idempotent in its first value and independent of every constructible tail."
    source := "base/boot.jl:951; internal projection invariant"
    status := .proven, prop := ``FirstArgumentProjection, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.firstArgumentProjection_proven },
  { id := "boot-core-stream-markers", juliaFile := "base/boot.jl"
    juliaFns := ["CoreSTDOUT()", "CoreSTDERR()"]
    statement := "Core's immutable stream markers are distinct singleton types spanning the two Core stream tags."
    source := "base/boot.jl:973-978; fieldless immutable constructor invariant"
    status := .proven, prop := ``CoreStreamMarkers, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.coreStreamMarkers_proven },
  { id := "boot-print-string-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["print(io::IO, x::String)"]
    statement := "String print performs one exact-argument dispatched write, returns nothing on success, and propagates all errors, state changes and divergence."
    source := "base/boot.jl:998; IO dispatch and effect invariant"
    status := .proven, prop := ``PrintStringDispatch, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.printStringDispatch_proven },
  { id := "boot-print-any-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["print(io::IO, @nospecialize x)"]
    statement := "The generic print fallback forwards one exact-argument show call and preserves every callee outcome and effect."
    source := "base/boot.jl:999; IO dispatch and effect invariant"
    status := .proven, prop := ``PrintAnyDispatch, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.printAnyDispatch_proven },
  { id := "boot-println-byte-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["println(io::IO)"]
    statement := "The empty println writes precisely UInt8 line-feed through custom IO dispatch and returns nothing only on successful completion."
    source := "base/boot.jl:1001; newline and dispatch invariant"
    status := .proven, prop := ``PrintlnByteDispatch, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.printlnByteDispatch_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean
open JuliaLean.base.boot
open JuliaLean.Registry

/-!
Independent arithmetic invariants for all seven dimension-checking methods.
The specification uses an exact, unbounded mathematical product and interval
membership; it does not repeat the native multiplication loop, signed/unsigned
intrinsics, intermediate overflow flags, or helper dispatch implementation.
All mathematical lists below are observations, not extra Julia allocations.
Actual source vararg tuples use the model's UInt32-bounded DimensionTuple.
-/

/-- Exact mathematical volume of a tuple of native dimensions, independent of
the model's fixed-width multiplication and left-to-right loop state. -/
def DimensionProduct (dims : List I64) : Int :=
  (dims.map (fun dim => dim.val)).foldr (· * ·) 1

/-- The complete accepted domain of the multiplication helpers: each separate
dimension is nonnegative and strictly below typemax(Int), and the exact
mathematical volume fits the nonnegative Int range. A zero dimension makes the
volume zero even when some earlier positive prefix product would overflow.
Negative and typemax dimensions remain invalid even in a zero-volume tuple.
-/
def AdmissibleDimensions (dims : List I64) : Prop :=
  (∀ dim ∈ dims, 0 ≤ dim.val ∧ dim.val < IntTy.max .i64) ∧
  0 ≤ DimensionProduct dims ∧ DimensionProduct dims ≤ IntTy.max .i64

/-- Observe the wrapped mathematical product and the exact acceptance set.
Neither observation names an intrinsic, an intermediate loop state, or another
dimension-checking implementation. -/
def DimensionPairObservation (dims : List I64) (result : I64 × Bool) : Prop :=
  result.1.val = wrapInt .i64 (DimensionProduct dims) ∧
  (result.2 = false ↔ AdmissibleDimensions dims)

/-- An independent algebraic characterization of the empty product: the result
is the multiplicative unit for every mathematical integer, and never reports
failure. Julia source/invariant: `base/boot.jl:782`.
-/
def CheckedMulDimsEmptyInvariant : Prop :=
  (∀ z : Int, _checked_mul_dims0.1.val * z = z ∧
    z * _checked_mul_dims0.1.val = z) ∧ _checked_mul_dims0.2 = false

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem checkedMulDimsEmptyInvariant_proven : CheckedMulDimsEmptyInvariant := by
  exact ⟨fun z => ⟨Int.one_mul z, Int.mul_one z⟩, rfl⟩
end

/-- Full-domain singleton helper behavior. In particular negative inputs and
typemax(Int) are rejected by the flag while their bit pattern is retained.
Julia source/invariant: `base/boot.jl:783`.
-/
def CheckedMulDimsSingletonInvariant : Prop :=
  ∀ dim : I64, DimensionPairObservation [dim] (_checked_mul_dims1 dim)

/-- Exact native signed-multiply dependency: wrapped mathematical product and
overflow precisely outside the signed Int interval, including negative values,
typemin(Int), and products at either endpoint. The helper is used directly by
the two-argument and variadic dimension methods.
Julia source/invariant: `base/boot.jl:785,800`; installed C intrinsic model.
-/
def DimensionSignedMultiplyInvariant : Prop :=
  ∀ left right : I64,
    let result := checked_smul_int left right
    result.1.val = wrapInt .i64 (left.val * right.val) ∧
    (result.2 = false ↔
      IntTy.min .i64 ≤ left.val * right.val ∧
      left.val * right.val ≤ IntTy.max .i64)

/-- Two native dimensions produce the wrapped mathematical volume and reject
exactly invalid individual dimensions or an unrepresentable nonnegative
volume. Julia source/invariant: `base/boot.jl:784-791`.
-/
def CheckedMulDimsPairInvariant : Prop :=
  ∀ left right : I64,
    DimensionPairObservation [left, right] (_checked_mul_dims2 left right)

/-- The raw variadic helper obeys the mathematical-product specification over
every representable tail tuple, including an empty tail. The additional zero
clause makes the source's overflow-recovery behavior explicit: a zero anywhere
in an otherwise valid tuple prevents failure even after an overflowing prefix.
Julia source/invariant: `base/boot.jl:792-809`; tuple representation bound:
`base/runtime_internals.jl:624-630,716-723`.
-/
def CheckedMulDimsVariadicInvariant : Prop :=
  ∀ (first : I64) (tail : JuliaLean.base.boot.Models2Group1.DimensionTuple),
    let dims := first :: tail.values
    let result := _checked_mul_dimsN first tail.values
    DimensionPairObservation dims result ∧
    ((∀ dim ∈ dims, 0 ≤ dim.val ∧ dim.val < IntTy.max .i64) →
      (∃ dim ∈ dims, dim.val = 0) → result.2 = false ∧ result.1.val = 0)

/-- The empty public checked_dims result is the multiplicative identity,
specified algebraically without repeating its constant return expression.
Julia source/invariant: `base/boot.jl:812`.
-/
def CheckedDimsEmptyInvariant : Prop :=
  ∀ z : Int, checked_dims0.val * z = z ∧ z * checked_dims0.val = z

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem checkedDimsEmptyInvariant_proven : CheckedDimsEmptyInvariant := by
  intro z
  exact ⟨Int.one_mul z, Int.mul_one z⟩
end

/-- The scalar public checked_dims method is injective and idempotent on the
entire native Int domain. Together these exclude every value-changing map;
negative inputs and typemax(Int) are included without a validity precondition.
Julia source/invariant: `base/boot.jl:813` explicitly defers scalar validation.
-/
def CheckedDimsScalarIdentityInvariant : Prop :=
  ∀ left right : I64,
    (checked_dims1 left = checked_dims1 right ↔ left = right) ∧
    checked_dims1 (checked_dims1 left) = checked_dims1 left

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem checkedDimsScalarIdentityInvariant_proven : CheckedDimsScalarIdentityInvariant := by
  intro left right
  exact ⟨Iff.rfl, rfl⟩
end

/-- Independently observe a raw checked_dims result: total termination, exact
mathematical volume on success, the precise rejection domain and exception
class/message on failure, and no change to the runtime world. The caller
provides only the concrete error's data embedding, not a behavior callback.
-/
def CheckedDimensionsObservation {W L : Type} (dims : List I64) (world : W)
    (argumentError : JuliaLean.base.expr.Value L)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value L × W) (I64 × W))) : Prop :=
  match outcome with
  | none => False
  | some (.ok (volume, finalWorld)) =>
      AdmissibleDimensions dims ∧ volume.val = DimensionProduct dims ∧
      finalWorld = world
  | some (.error (error, finalWorld)) =>
      ¬AdmissibleDimensions dims ∧ error = argumentError ∧ finalWorld = world

/-- The raw vararg body validates every arity, including a singleton reached
with explicit invoke; it terminates, returns the exact mathematical volume
precisely for admissible dimensions, and otherwise throws ArgumentError with
the fixed message. It preserves the world in both outcomes. Every possible
representation encoding is quantified without laws or callee assumptions.
Julia source/invariant: `base/boot.jl:814-818`; dimension helper semantics at
`base/boot.jl:782-809`; UInt32 tuple arity at
`base/runtime_internals.jl:624-630,716-723`.
-/
def CheckedDimsVarargsInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L)
    (dims : JuliaLean.base.boot.Models2Group1.DimensionTuple) (world : W),
    CheckedDimensionsObservation dims.values world
      (objV ops (.argumentError (strV ops "invalid Array dimensions")))
      (JuliaLean.base.boot.Models2Group1.checkedDimsVarargs ops dims world)

/-- Entries to concatenate into the assigned proof namespace's
entriesModels2Group1. Existing properties and proof status remain unchanged.
-/
def entriesDimensions : List Entry := [
  { id := "boot-dims-empty-product"
    juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims()"]
    statement := "The empty dimension product is the multiplicative unit and has no rejection flag."
    source := "Invariant; base/boot.jl:782"
    status := .proven
    prop := ``CheckedMulDimsEmptyInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.checkedMulDimsEmptyInvariant_proven
    notes := "Reuses JuliaLean.base.boot._checked_mul_dims0; algebraic unit specification." },
  { id := "boot-dims-singleton-range"
    juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims(m::Int)"]
    statement := "The singleton helper retains the native value and rejects exactly negative or typemax(Int) dimensions."
    source := "Invariant; base/boot.jl:783"
    status := .todo
    prop := ``CheckedMulDimsSingletonInvariant
    thm := none
    notes := "Reuses JuliaLean.base.boot._checked_mul_dims1 over all native Int inputs." },
  { id := "boot-dims-signed-multiply"
    juliaFile := "base/boot.jl"
    juliaFns := ["Intrinsics.checked_smul_int(::Int, ::Int) (dimension-helper dependency)"]
    statement := "Native checked signed multiplication returns the wrapped exact product and flags precisely mathematical products outside the signed native interval."
    source := "Dependency invariant; base/boot.jl:785,800; installed C checked-signed-multiply model"
    status := .todo
    prop := ``DimensionSignedMultiplyInvariant
    thm := none
    notes := "Reuses JuliaLean.base.boot.checked_smul_int and its installed JuliaLean.C implementation; no new primitive or assumed callee law." },
  { id := "boot-dims-pair-volume"
    juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims(m::Int, n::Int)"]
    statement := "Two dimensions return the wrapped exact volume and reject exactly invalid individual dimensions or an unrepresentable nonnegative volume."
    source := "Invariant; base/boot.jl:784-791"
    status := .todo
    prop := ``CheckedMulDimsPairInvariant
    thm := none
    notes := "Reuses JuliaLean.base.boot._checked_mul_dims2; independent mathematical product and interval specification." },
  { id := "boot-dims-vararg-volume"
    juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims(m::Int, d::Int...)"]
    statement := "Every representable variadic dimension tuple has the wrapped mathematical volume and exact rejection flag; a zero cancels earlier multiplication overflow without legitimizing negative or typemax dimensions."
    source := "Invariant; base/boot.jl:792-809; base/runtime_internals.jl:624-630,716-723"
    status := .todo
    prop := ``CheckedMulDimsVariadicInvariant
    thm := none
    notes := "Reuses JuliaLean.base.boot._checked_mul_dimsN and _checked_mul_dims_loop. Covers an empty tail and all UInt32-bounded tuple arities; no loop counter can wrap." },
  { id := "boot-checked-dims-empty"
    juliaFile := "base/boot.jl"
    juliaFns := ["checked_dims()"]
    statement := "The zero-argument checked_dims result is the multiplicative identity."
    source := "Invariant; base/boot.jl:812"
    status := .proven
    prop := ``CheckedDimsEmptyInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.checkedDimsEmptyInvariant_proven
    notes := "Reuses JuliaLean.base.boot.checked_dims0." },
  { id := "boot-checked-dims-scalar"
    juliaFile := "base/boot.jl"
    juliaFns := ["checked_dims(m::Int)"]
    statement := "The scalar checked_dims method is injective and idempotent over all Int values, including negative values and typemax(Int); validation is deferred."
    source := "Invariant; base/boot.jl:813 and its deferred-check source comment"
    status := .proven
    prop := ``CheckedDimsScalarIdentityInvariant
    thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.checkedDimsScalarIdentityInvariant_proven
    notes := "Reuses JuliaLean.base.boot.checked_dims1. Distinct from explicit invocation of the raw vararg body." },
  { id := "boot-checked-dims-vararg"
    juliaFile := "base/boot.jl"
    juliaFns := ["checked_dims(d::Int...)"]
    statement := "The raw vararg body terminates without world changes, returns the exact volume exactly for admissible dimensions, and otherwise throws the specified ArgumentError; every invocation arity is included."
    source := "Invariant; base/boot.jl:814-818; base/runtime_internals.jl:624-630,716-723"
    status := .todo
    prop := ``CheckedDimsVarargsInvariant
    thm := none
    notes := "New complete Models2Group1.checkedDimsVarargs. Concrete dependencies are the existing helper dispatcher/0/1/2/N bodies and Models2Group1.argumentErrorCtor, whose own field property is registered separately. CoreOps fields used here are pure String/object embeddings only." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-- Observe ArgumentError's defined msg field independently of construction.
Source layout: `base/boot.jl:549-552`. -/
def bootstrapArgumentErrorMessage {L : Type} : Obj L → Option (JuliaLean.base.expr.Value L)
  | .argumentError message => some message
  | _ => none

/-- The bootstrap fail helper always throws its documented ArgumentError with
the fixed message and leaves all runtime state unchanged. It neither returns
nor invokes dispatched conversion on the compatible String message.
Source: `base/boot.jl:878`; independent class/message/state invariant. -/
def BootstrapFailThrows : Prop :=
  ∀ (W L A : Type) (ops : CoreOps W L) (world : W),
    ∃ payload, (bootstrapFail (A := A) ops) world = some (.error (objV ops payload, world)) ∧
      bootstrapArgumentErrorMessage payload =
        some (strV ops "unsupported import/using while bootstrapping")

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem bootstrapFailThrows_proven : BootstrapFailThrows := by
  intro W L A ops world
  exact ⟨.argumentError (strV ops "unsupported import/using while bootstrapping"), rfl, rfl⟩
end

def bootstrapFailEntries : List Entry := [
  { id := "boot-bootstrap-fail-throws", juliaFile := "base/boot.jl"
    juliaFns := ["fail()"]
    statement := "The local bootstrap fail helper always throws ArgumentError with its fixed unsupported-import/using message, without changing runtime state or returning."
    source := "base/boot.jl:878; independent exception/message/state invariant"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.bootstrapFailThrows_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.BootstrapFailThrows
    notes := "Covers bootstrapFail and its necessary concrete argumentErrorCtor dependency. No cf, fieldtype, isa, or conversion callback is used for the fixed String." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-- Independent zero-based field observation, used only in specifications. -/
def typedNamedTupleField {L : Type} (tuple : TypedNamedTupleValue L) (i : Nat) :
    Option (JuliaLean.base.expr.Value L) := tuple.fields.values[i]?

/-- Independent conjunction of the actual raw-target metadata requirements. -/
def TypedNamedTupleAllocatable {L : Type} (target : TypedNamedTupleTarget L) : Prop :=
  target.isDataType = true ∧ target.isConcrete = true ∧
    target.hasLayout = true ∧ target.layoutOpaque = false

/-- Observe all success and error outcomes. Target rejection precedes count
checks and retains original NT; success retains exact declared type, count and
all compatible input objects. Source: `base/boot.jl:1029-1030`;
`src/datatype.c:1744-1791`. -/
def TypedNamedTupleOutcome {L : Type} (target : TypedNamedTupleTarget L)
    (args : TypedNamedTupleArguments L)
    (result : Except (TypedNamedTupleError L) (TypedNamedTupleValue L)) : Prop :=
  match result with
  | .ok tuple =>
    TypedNamedTupleAllocatable target ∧ tuple.runtimeType = target.value ∧
      tuple.fields.values.length = target.fieldCount.val.toNat ∧
      tuple.fields.values.length = args.values.length ∧
      (∀ i, i < args.values.length → typedNamedTupleField tuple i = args.values[i]?) ∧
      (∀ i, args.values.length ≤ i → typedNamedTupleField tuple i = none)
  | .error error =>
    (¬TypedNamedTupleAllocatable target ∧ error.exception = .typeError "new" ∧
      error.expected = some "DataType" ∧ error.got = some target.value) ∨
    (TypedNamedTupleAllocatable target ∧ args.values.length ≠ target.fieldCount.val.toNat ∧
      error.expected = none ∧ error.got = none ∧
      error.exception = .argument
        (if args.values.length < target.fieldCount.val.toNat then
          s!"new: too few arguments (expected {(JInt.wrap .i32 target.fieldCount.val).val})"
        else s!"new: too many arguments (expected {(JInt.wrap .i32 target.fieldCount.val).val})"))

/-- All stored target metadata, including nonconcrete/incomplete targets, is
quantified. No allocatability or successful-result premise narrows the domain.
The source's args::T signature supplies field compatibility for valid concrete
NT. Count mismatches are also checked explicitly. Source: `base/boot.jl:1029-1030`;
independent target-error precedence, type and indexed-field observations. -/
def TypedNamedTupleTypeAndFields : Prop :=
  ∀ (L : Type) (target : TypedNamedTupleTarget L) (args : TypedNamedTupleArguments L),
    TypedNamedTupleOutcome target args (typedNamedTupleCtor target args)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem typedNamedTupleTypeAndFields_proven : TypedNamedTupleTypeAndFields := by
  intro L target args
  by_cases htarget : TypedNamedTupleAllocatable target
  · obtain ⟨ha,hb,hc,hd⟩ := htarget
    by_cases hlt : args.values.length < target.fieldCount.val.toNat
    · simp [typedNamedTupleCtor, TypedNamedTupleOutcome, TypedNamedTupleAllocatable,
        ha,hb,hc,hd,hlt, Nat.ne_of_lt hlt, Pure.pure, Bind.bind, MonadExceptOf.throw]
      exact ⟨rfl, rfl, rfl⟩
    · by_cases hgt : args.values.length > target.fieldCount.val.toNat
      · simp [typedNamedTupleCtor, TypedNamedTupleOutcome, TypedNamedTupleAllocatable,
          ha,hb,hc,hd,hlt,hgt, Nat.ne_of_gt hgt, Pure.pure, Bind.bind, MonadExceptOf.throw]
        exact ⟨rfl, rfl, rfl⟩
      · have heq : args.values.length = target.fieldCount.val.toNat := by omega
        simp [typedNamedTupleCtor, TypedNamedTupleOutcome, TypedNamedTupleAllocatable,
          typedNamedTupleField, ha,hb,hc,hd,hlt,hgt,heq, Pure.pure, Bind.bind,
          MonadExceptOf.throw]
        exact ⟨rfl, heq, fun _ _ => rfl, fun i h => by
          change args.values.length ≤ i
          omega⟩
  · cases ha : target.isDataType <;> cases hb : target.isConcrete <;>
      cases hc : target.hasLayout <;> cases hd : target.layoutOpaque <;>
      simp_all [typedNamedTupleCtor, TypedNamedTupleOutcome, TypedNamedTupleAllocatable,
        Pure.pure, Bind.bind, MonadExceptOf.throw] <;> exact ⟨rfl, rfl, rfl⟩
end

/-- Registry remains one public method, with its broadened full-target contract. -/
def typedNamedTupleEntries : List Entry := [
  { id := "boot-typed-named-tuple-type-fields", juliaFile := "base/boot.jl"
    juliaFns := ["(NT::Type{NamedTuple{names,T}})(args::T) where {names, T <: Tuple}"]
    statement := "Typed NamedTuple raw construction rejects nonconcrete or incomplete target metadata before count/field reads, checks exact field count, and otherwise preserves the declared NT type and every original field object."
    source := "base/boot.jl:1029-1030; src/datatype.c:1744-1791; independent target/error/type/indexed-field invariant"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.typedNamedTupleTypeAndFields_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypedNamedTupleTypeAndFields
    notes := "Full actual target metadata is checked, not assumed allocatable. Source args::T implies compatible fields for valid concrete NamedTuple targets (jltypes.c:2726-2773); errors retain original target. UInt32 tuple arity and count, explicit C int conversion in count messages. No callback laws or proofs." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-- A native integer conversion succeeds exactly when the mathematical input
fits the target's documented range. Success preserves that exact integer;
failure must be the source's InexactError with the actual target and original
typed input. This specification does not invoke any conversion helper or
duplicate its sign/truncate/extend branches. The function name is `convert`
at equal widths and `trunc` otherwise, including the source's narrower-signed
to-wider-unsigned negative case (`base/boot.jl:1051,1137,1148-1149,1159-1161,
1170-1173`). Bool's integer meaning is 0 or 1. -/
def NativeConversionContract (target : IntTy)
    (input : JuliaLean.BootCov.IntConv.BuiltinInt)
    (result : Except NativeConversionError (JInt target)) : Prop :=
  let fits := target.min ≤ input.value ∧ input.value ≤ target.max
  match result with
  | .ok value => fits ∧ value.val = input.value
  | .error error =>
      ¬fits ∧ error.target = target ∧ error.input = input ∧
      error.exception = .inexact
        (if target.bits = input.bits then "convert" else "trunc") target.name

/-- Independent observation for an installed pure native branch: termination,
no exception, unchanged complete runtime world, and exact mathematical value.
This does not assume a successful outcome and does not assume a callee law. -/
def NativePureValue {W L : Type} {target : IntTy}
    (action : CoreM W L (JInt target)) (expected : Int) (world : W) : Prop :=
  ∃ value, action world = some (.ok (value, world)) ∧ value.val = expected

/-- Every concrete toInt8 overload and the complete Int8 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1071-1081,1184`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeInt8ExactRange : Prop :=
  (∀ (W L : Type) (x : JInt .i8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt8_Int8 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .i16, NativeConversionContract .i8 (.int .i16 x)
    (nativeToInt8FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .i8 (.int .i32 x)
    (nativeToInt8FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .i8 (.int .i64 x)
    (nativeToInt8FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .i8 (.int .i128 x)
    (nativeToInt8FromInt128 x)) ∧
  (∀ x : JInt .u8, NativeConversionContract .i8 (.int .u8 x)
    (nativeToInt8FromUInt8 x)) ∧
  (∀ x : JInt .u16, NativeConversionContract .i8 (.int .u16 x)
    (nativeToInt8FromUInt16 x)) ∧
  (∀ x : JInt .u32, NativeConversionContract .i8 (.int .u32 x)
    (nativeToInt8FromUInt32 x)) ∧
  (∀ x : JInt .u64, NativeConversionContract .i8 (.int .u64 x)
    (nativeToInt8FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .i8 (.int .u128 x)
    (nativeToInt8FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt8_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .i8 x (nativeInt8Ctor x))

/-- Every concrete toInt16 overload and the complete Int16 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1082-1092,1185`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeInt16ExactRange : Prop :=
  (∀ (W L : Type) (x : JInt .i8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt16_Int8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt16_Int16 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .i32, NativeConversionContract .i16 (.int .i32 x)
    (nativeToInt16FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .i16 (.int .i64 x)
    (nativeToInt16FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .i16 (.int .i128 x)
    (nativeToInt16FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt16_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u16, NativeConversionContract .i16 (.int .u16 x)
    (nativeToInt16FromUInt16 x)) ∧
  (∀ x : JInt .u32, NativeConversionContract .i16 (.int .u32 x)
    (nativeToInt16FromUInt32 x)) ∧
  (∀ x : JInt .u64, NativeConversionContract .i16 (.int .u64 x)
    (nativeToInt16FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .i16 (.int .u128 x)
    (nativeToInt16FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt16_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .i16 x (nativeInt16Ctor x))

/-- Every concrete toInt32 overload and the complete Int32 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1093-1103,1186`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeInt32ExactRange : Prop :=
  (∀ (W L : Type) (x : JInt .i8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_Int8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_Int16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i32) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_Int32 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .i64, NativeConversionContract .i32 (.int .i64 x)
    (nativeToInt32FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .i32 (.int .i128 x)
    (nativeToInt32FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u32, NativeConversionContract .i32 (.int .u32 x)
    (nativeToInt32FromUInt32 x)) ∧
  (∀ x : JInt .u64, NativeConversionContract .i32 (.int .u64 x)
    (nativeToInt32FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .i32 (.int .u128 x)
    (nativeToInt32FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt32_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .i32 x (nativeInt32Ctor x))

/-- Every concrete toInt64 overload and the complete Int64 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1104-1114,1187`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeInt64ExactRange : Prop :=
  (∀ (W L : Type) (x : JInt .i8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_Int8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_Int16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i32) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_Int32 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i64) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_Int64 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .i128, NativeConversionContract .i64 (.int .i128 x)
    (nativeToInt64FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u32) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_UInt32 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u64, NativeConversionContract .i64 (.int .u64 x)
    (nativeToInt64FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .i64 (.int .u128 x)
    (nativeToInt64FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt64_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .i64 x (nativeInt64Ctor x))

/-- Every concrete toInt128 overload and the complete Int128 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1115-1125,1188`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeInt128ExactRange : Prop :=
  (∀ (W L : Type) (x : JInt .i8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Int8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Int16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i32) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Int32 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i64) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Int64 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .i128) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Int128 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u32) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_UInt32 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u64) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_UInt64 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u128, NativeConversionContract .i128 (.int .u128 x)
    (nativeToInt128FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toInt128_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .i128 x (nativeInt128Ctor x))

/-- Every concrete toUInt8 overload and the complete UInt8 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1126-1136,1189`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeUInt8ExactRange : Prop :=
  (∀ x : JInt .i8, NativeConversionContract .u8 (.int .i8 x)
    (nativeToUInt8FromInt8 x)) ∧
  (∀ x : JInt .i16, NativeConversionContract .u8 (.int .i16 x)
    (nativeToUInt8FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .u8 (.int .i32 x)
    (nativeToUInt8FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .u8 (.int .i64 x)
    (nativeToUInt8FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .u8 (.int .i128 x)
    (nativeToUInt8FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt8_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u16, NativeConversionContract .u8 (.int .u16 x)
    (nativeToUInt8FromUInt16 x)) ∧
  (∀ x : JInt .u32, NativeConversionContract .u8 (.int .u32 x)
    (nativeToUInt8FromUInt32 x)) ∧
  (∀ x : JInt .u64, NativeConversionContract .u8 (.int .u64 x)
    (nativeToUInt8FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .u8 (.int .u128 x)
    (nativeToUInt8FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt8_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .u8 x (nativeUInt8Ctor x))

/-- Every concrete toUInt16 overload and the complete UInt16 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1137-1147,1190`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeUInt16ExactRange : Prop :=
  (∀ x : JInt .i8, NativeConversionContract .u16 (.int .i8 x)
    (nativeToUInt16FromInt8 x)) ∧
  (∀ x : JInt .i16, NativeConversionContract .u16 (.int .i16 x)
    (nativeToUInt16FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .u16 (.int .i32 x)
    (nativeToUInt16FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .u16 (.int .i64 x)
    (nativeToUInt16FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .u16 (.int .i128 x)
    (nativeToUInt16FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt16_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt16_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u32, NativeConversionContract .u16 (.int .u32 x)
    (nativeToUInt16FromUInt32 x)) ∧
  (∀ x : JInt .u64, NativeConversionContract .u16 (.int .u64 x)
    (nativeToUInt16FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .u16 (.int .u128 x)
    (nativeToUInt16FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt16_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .u16 x (nativeUInt16Ctor x))

/-- Every concrete toUInt32 overload and the complete UInt32 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1148-1158,1191`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeUInt32ExactRange : Prop :=
  (∀ x : JInt .i8, NativeConversionContract .u32 (.int .i8 x)
    (nativeToUInt32FromInt8 x)) ∧
  (∀ x : JInt .i16, NativeConversionContract .u32 (.int .i16 x)
    (nativeToUInt32FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .u32 (.int .i32 x)
    (nativeToUInt32FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .u32 (.int .i64 x)
    (nativeToUInt32FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .u32 (.int .i128 x)
    (nativeToUInt32FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt32_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt32_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u32) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt32_UInt32 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u64, NativeConversionContract .u32 (.int .u64 x)
    (nativeToUInt32FromUInt64 x)) ∧
  (∀ x : JInt .u128, NativeConversionContract .u32 (.int .u128 x)
    (nativeToUInt32FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt32_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .u32 x (nativeUInt32Ctor x))

/-- Every concrete toUInt64 overload and the complete UInt64 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1159-1169,1192`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeUInt64ExactRange : Prop :=
  (∀ x : JInt .i8, NativeConversionContract .u64 (.int .i8 x)
    (nativeToUInt64FromInt8 x)) ∧
  (∀ x : JInt .i16, NativeConversionContract .u64 (.int .i16 x)
    (nativeToUInt64FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .u64 (.int .i32 x)
    (nativeToUInt64FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .u64 (.int .i64 x)
    (nativeToUInt64FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .u64 (.int .i128 x)
    (nativeToUInt64FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt64_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt64_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u32) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt64_UInt32 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u64) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt64_UInt64 (W := W) (L := L) x) x.val world) ∧
  (∀ x : JInt .u128, NativeConversionContract .u64 (.int .u128 x)
    (nativeToUInt64FromUInt128 x)) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt64_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .u64 x (nativeUInt64Ctor x))

/-- Every concrete toUInt128 overload and the complete UInt128 BuiltinInts
constructor preserve the mathematical input exactly when representable; an
unrepresentable value produces InexactError with its original typed payload.
The pre-existing pure branches additionally preserve every runtime world.
All native bit patterns and both Bool values are included, with no range
premise. Source: `base/boot.jl:1170-1180,1193`; native integer ranges:
`doc/src/manual/integers-and-floating-point-numbers.md`, Integer Types. -/
def NativeUInt128ExactRange : Prop :=
  (∀ x : JInt .i8, NativeConversionContract .u128 (.int .i8 x)
    (nativeToUInt128FromInt8 x)) ∧
  (∀ x : JInt .i16, NativeConversionContract .u128 (.int .i16 x)
    (nativeToUInt128FromInt16 x)) ∧
  (∀ x : JInt .i32, NativeConversionContract .u128 (.int .i32 x)
    (nativeToUInt128FromInt32 x)) ∧
  (∀ x : JInt .i64, NativeConversionContract .u128 (.int .i64 x)
    (nativeToUInt128FromInt64 x)) ∧
  (∀ x : JInt .i128, NativeConversionContract .u128 (.int .i128 x)
    (nativeToUInt128FromInt128 x)) ∧
  (∀ (W L : Type) (x : JInt .u8) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_UInt8 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u16) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_UInt16 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u32) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_UInt32 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u64) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_UInt64 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : JInt .u128) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_UInt128 (W := W) (L := L) x) x.val world) ∧
  (∀ (W L : Type) (x : Bool) (world : W),
    NativePureValue (JuliaLean.base.boot.toUInt128_Bool (W := W) (L := L) x) (if x then 1 else 0) world) ∧
  (∀ x : JuliaLean.BootCov.IntConv.BuiltinInt,
    NativeConversionContract .u128 x (nativeUInt128Ctor x))

/-- Signed/Unsigned preserve the exact input on the full representable
portion of the opposite-signed native domain. Every other input raises
InexactError(:convert, target, original_input); no range premise is imposed.
Source: `base/boot.jl:1206-1215`; signed/unsigned integer range invariant. -/
def NativeSignedUnsignedExactRange : Prop :=
  (∀ x : JInt .u8,
    NativeConversionContract .i8 (.int .u8 x) (nativeSignedFromUInt8 x)) ∧
  (∀ x : JInt .i8,
    NativeConversionContract .u8 (.int .i8 x) (nativeUnsignedFromInt8 x)) ∧
  (∀ x : JInt .u16,
    NativeConversionContract .i16 (.int .u16 x) (nativeSignedFromUInt16 x)) ∧
  (∀ x : JInt .i16,
    NativeConversionContract .u16 (.int .i16 x) (nativeUnsignedFromInt16 x)) ∧
  (∀ x : JInt .u32,
    NativeConversionContract .i32 (.int .u32 x) (nativeSignedFromUInt32 x)) ∧
  (∀ x : JInt .i32,
    NativeConversionContract .u32 (.int .i32 x) (nativeUnsignedFromInt32 x)) ∧
  (∀ x : JInt .u64,
    NativeConversionContract .i64 (.int .u64 x) (nativeSignedFromUInt64 x)) ∧
  (∀ x : JInt .i64,
    NativeConversionContract .u64 (.int .i64 x) (nativeUnsignedFromInt64 x)) ∧
  (∀ x : JInt .u128,
    NativeConversionContract .i128 (.int .u128 x) (nativeSignedFromUInt128 x)) ∧
  (∀ x : JInt .i128,
    NativeConversionContract .u128 (.int .i128 x) (nativeUnsignedFromInt128 x))

/-- New todo entries for the 130 complete native source rows. -/
def nativeConversionEntries : List Entry := [
  { id := "boot-native-int8-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toInt8(x::Int8)", "toInt8(x::Int16)", "toInt8(x::Int32)", "toInt8(x::Int64)", "toInt8(x::Int128)", "toInt8(x::UInt8)", "toInt8(x::UInt16)", "toInt8(x::UInt32)", "toInt8(x::UInt64)", "toInt8(x::UInt128)", "toInt8(x::Bool)", "Int8(x::BuiltinInts)"]
    statement := "All eleven concrete toInt8 overloads and the Int8 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1071-1081,1184; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeInt8ExactRange },
  { id := "boot-native-int16-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toInt16(x::Int8)", "toInt16(x::Int16)", "toInt16(x::Int32)", "toInt16(x::Int64)", "toInt16(x::Int128)", "toInt16(x::UInt8)", "toInt16(x::UInt16)", "toInt16(x::UInt32)", "toInt16(x::UInt64)", "toInt16(x::UInt128)", "toInt16(x::Bool)", "Int16(x::BuiltinInts)"]
    statement := "All eleven concrete toInt16 overloads and the Int16 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1082-1092,1185; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeInt16ExactRange },
  { id := "boot-native-int32-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toInt32(x::Int8)", "toInt32(x::Int16)", "toInt32(x::Int32)", "toInt32(x::Int64)", "toInt32(x::Int128)", "toInt32(x::UInt8)", "toInt32(x::UInt16)", "toInt32(x::UInt32)", "toInt32(x::UInt64)", "toInt32(x::UInt128)", "toInt32(x::Bool)", "Int32(x::BuiltinInts)"]
    statement := "All eleven concrete toInt32 overloads and the Int32 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1093-1103,1186; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeInt32ExactRange },
  { id := "boot-native-int64-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toInt64(x::Int8)", "toInt64(x::Int16)", "toInt64(x::Int32)", "toInt64(x::Int64)", "toInt64(x::Int128)", "toInt64(x::UInt8)", "toInt64(x::UInt16)", "toInt64(x::UInt32)", "toInt64(x::UInt64)", "toInt64(x::UInt128)", "toInt64(x::Bool)", "Int64(x::BuiltinInts)"]
    statement := "All eleven concrete toInt64 overloads and the Int64 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1104-1114,1187; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeInt64ExactRange },
  { id := "boot-native-int128-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toInt128(x::Int8)", "toInt128(x::Int16)", "toInt128(x::Int32)", "toInt128(x::Int64)", "toInt128(x::Int128)", "toInt128(x::UInt8)", "toInt128(x::UInt16)", "toInt128(x::UInt32)", "toInt128(x::UInt64)", "toInt128(x::UInt128)", "toInt128(x::Bool)", "Int128(x::BuiltinInts)"]
    statement := "All eleven concrete toInt128 overloads and the Int128 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1115-1125,1188; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeInt128ExactRange },
  { id := "boot-native-uint8-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toUInt8(x::Int8)", "toUInt8(x::Int16)", "toUInt8(x::Int32)", "toUInt8(x::Int64)", "toUInt8(x::Int128)", "toUInt8(x::UInt8)", "toUInt8(x::UInt16)", "toUInt8(x::UInt32)", "toUInt8(x::UInt64)", "toUInt8(x::UInt128)", "toUInt8(x::Bool)", "UInt8(x::BuiltinInts)"]
    statement := "All eleven concrete toUInt8 overloads and the UInt8 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1126-1136,1189; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeUInt8ExactRange },
  { id := "boot-native-uint16-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toUInt16(x::Int8)", "toUInt16(x::Int16)", "toUInt16(x::Int32)", "toUInt16(x::Int64)", "toUInt16(x::Int128)", "toUInt16(x::UInt8)", "toUInt16(x::UInt16)", "toUInt16(x::UInt32)", "toUInt16(x::UInt64)", "toUInt16(x::UInt128)", "toUInt16(x::Bool)", "UInt16(x::BuiltinInts)"]
    statement := "All eleven concrete toUInt16 overloads and the UInt16 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1137-1147,1190; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeUInt16ExactRange },
  { id := "boot-native-uint32-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toUInt32(x::Int8)", "toUInt32(x::Int16)", "toUInt32(x::Int32)", "toUInt32(x::Int64)", "toUInt32(x::Int128)", "toUInt32(x::UInt8)", "toUInt32(x::UInt16)", "toUInt32(x::UInt32)", "toUInt32(x::UInt64)", "toUInt32(x::UInt128)", "toUInt32(x::Bool)", "UInt32(x::BuiltinInts)"]
    statement := "All eleven concrete toUInt32 overloads and the UInt32 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1148-1158,1191; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeUInt32ExactRange },
  { id := "boot-native-uint64-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toUInt64(x::Int8)", "toUInt64(x::Int16)", "toUInt64(x::Int32)", "toUInt64(x::Int64)", "toUInt64(x::Int128)", "toUInt64(x::UInt8)", "toUInt64(x::UInt16)", "toUInt64(x::UInt32)", "toUInt64(x::UInt64)", "toUInt64(x::UInt128)", "toUInt64(x::Bool)", "UInt64(x::BuiltinInts)"]
    statement := "All eleven concrete toUInt64 overloads and the UInt64 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1159-1169,1192; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeUInt64ExactRange },
  { id := "boot-native-uint128-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["toUInt128(x::Int8)", "toUInt128(x::Int16)", "toUInt128(x::Int32)", "toUInt128(x::Int64)", "toUInt128(x::Int128)", "toUInt128(x::UInt8)", "toUInt128(x::UInt16)", "toUInt128(x::UInt32)", "toUInt128(x::UInt64)", "toUInt128(x::UInt128)", "toUInt128(x::Bool)", "UInt128(x::BuiltinInts)"]
    statement := "All eleven concrete toUInt128 overloads and the UInt128 BuiltinInts constructor return the exact mathematical input iff it lies in the target range; otherwise the original target/input and exact source error-function Symbol are retained in InexactError. Installed pure branches terminate without state changes."
    source := "base/boot.jl:1170-1180,1193; doc/src/manual/integers-and-floating-point-numbers.md, Integer Types; base/boot.jl:1045-1069"
    notes := "Reuses existing source-mirrored native arithmetic and error ordering; new results refine lost exception payloads. Full native/Bool domains, mathematical specification, no callee laws. The registered public property depends on refineNativeResult and the installed native table helpers; no generic-helper source-row coverage is claimed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeUInt128ExactRange },
  { id := "boot-native-signed-unsigned-exact-range", juliaFile := "base/boot.jl"
    juliaFns := ["Signed(x::UInt8)", "Unsigned(x::Int8)", "Signed(x::UInt16)", "Unsigned(x::Int16)", "Signed(x::UInt32)", "Unsigned(x::Int32)", "Signed(x::UInt64)", "Unsigned(x::Int64)", "Signed(x::UInt128)", "Unsigned(x::Int128)"]
    statement := "Each same-width Signed/Unsigned native constructor returns the exact input iff representable and otherwise throws InexactError(:convert) retaining the true target and complete original typed value."
    source := "base/boot.jl:1206-1215; native integer range and exact conversion invariant"
    notes := "All ten concrete source methods; calls their completed integer constructors, with no arbitrary conversion callback or assumed callee law."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NativeSignedUnsignedExactRange }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1.FloatConversion

open JuliaLean
open JuliaLean.base.boot
open JuliaLean.base.boot.Models2Group1.FloatConversion
open JuliaLean.Registry

/-!
Independent conversion promises use exact rational decoding of raw IEEE bits.
They do not repeat the constructors' ordered float comparisons, generated
rounded bounds, truncation, subtraction, or integer conversion intrinsics.
All input bit patterns are quantified, without finiteness/integrality/range
preconditions. Failure preserves the complete original representation in the
InexactError operand tuple, including a NaN's payload and sign bits.
-/

/-- The represented raw IEEE value is exactly the mathematical integer `z`.
The positive denominator excludes both infinities and every NaN representation;
both signed zeros represent integer zero. This observer is independent of the
model's `iszero(x-trunc(x))` computation.
-/
def ExactIEEEInteger (input : IEEEInput) (z : Int) : Prop :=
  0 < input.value.toRat.2 ∧
  input.value.toRat.1 = z * (input.value.toRat.2 : Int)

/-- Mathematical representability in a fixed-width integer type, with no
rounding and no wrapping. This specification does not use a float constructor
or a comparison against the generator's rounded floating-point bounds.
-/
def IEEEIntegerRepresentable (target : IntTy) (input : IEEEInput) : Prop :=
  ∃ z : Int, ExactIEEEInteger input z ∧ target.min ≤ z ∧ z ≤ target.max

/-- An outcome observation for a concrete IEEE-to-native-integer call.
Success preserves the exact value and the world. Failure occurs only outside
the mathematical representability set, keeps the specified exception class,
function Symbol, target type and original operand, and preserves the world.
No diverging outcome is permitted. Expected error fields are independent data
observations; no constructor model is called in this specification.
-/
def NativeFloatOutcome {W L : Type} (ops : CoreOps W L)
    (encode : IEEEInput → L) (target : IntTy) (input : IEEEInput) (world : W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value L × W) (JInt target × W))) : Prop :=
  match outcome with
  | none => False
  | some (.ok (result, finalWorld)) =>
      ExactIEEEInteger input result.val ∧ finalWorld = world
  | some (.error (error, finalWorld)) =>
      ¬IEEEIntegerRepresentable target input ∧
      error = objV ops (.inexactError (.symbol target.name)
        (tupleV ops [coreV ops target.name, .leaf (encode input)])) ∧
      finalWorld = world

/-- Exact Bool-to-native-integer observation: false and true denote zero and
one, respectively. No error or divergence is permitted, and the world is
unchanged. The integer type remains visible in the outcome's type.
-/
def NativeBoolOutcome {W L : Type} (target : IntTy) (input : Bool) (world : W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value L × W) (JInt target × W))) : Prop :=
  match outcome with
  | some (.ok (result, finalWorld)) =>
      result.val = (if input then 1 else 0) ∧ finalWorld = world
  | _ => False

/-- Full-bit-domain `isinteger` dependency invariant: the source's truncation,
subtraction, and zero comparison recognize exactly finite integer-valued IEEE
encodings. Infinities, fractional/subnormal nonzero values, and every NaN bit
pattern are rejected. Julia source: `base/floatfuncs.jl:51`.
-/
def IsIntegerIEEEInvariant : Prop :=
  ∀ (kind : FT) (value : FV kind),
    isIntegerFloat value = true ↔
      ∃ z : Int, ExactIEEEInteger ⟨kind, value⟩ z

/-- Both required concrete floating constructors satisfy the mathematical
representability promise for every Float16/32/64 bit pattern. The generated
Int64 and UInt64 branches are covered independently of the public wrappers.
Julia source: `base/float.jl:881-931`; documentation:
`doc/src/manual/mathematical-operations.md:547-551,568-577`.
-/
def NativeIEEEConstructorsInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (encode : IEEEInput → L)
    (input : IEEEInput) (world : W),
    NativeFloatOutcome ops encode .i64 input world
      (int64FromIEEE ops encode input world) ∧
    NativeFloatOutcome ops encode .u64 input world
      (uint64FromIEEE ops encode input world)

/-- Signed's complete Float16/32/64/Bool union preserves exactly representable
values as Int64, including both signed zeros. Every other float throws the
full InexactError with its original bits; Bool maps to zero or one. All cases
terminate without changing the world. No assumptions restrict representations
or any callback: this model has no behavior callback.
Julia source: `base/boot.jl:1217`; integer-conversion promise:
`doc/src/manual/mathematical-operations.md:547-551,568-577`.
-/
def SignedIEEEBoolInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (encode : IEEEInput → L)
    (input : FloatOrBool) (world : W),
    match input with
    | .float value =>
        NativeFloatOutcome ops encode .i64 value world
          (JuliaLean.base.boot.Models2Group1.FloatConversion.signed ops encode input world)
    | .bool value =>
        NativeBoolOutcome .i64 value world
          (JuliaLean.base.boot.Models2Group1.FloatConversion.signed ops encode input world)

/-- Unsigned's entire union converts exactly nonnegative integral float values
in the UInt64 range, with negative zero accepted as zero. All other raw float
encodings produce the full InexactError; Bool maps to zero or one. Success and
failure preserve the world and always terminate.
Julia source: `base/boot.jl:1218`; integer-conversion promise:
`doc/src/manual/mathematical-operations.md:547-551,568-577`.
-/
def UnsignedIEEEBoolInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (encode : IEEEInput → L)
    (input : FloatOrBool) (world : W),
    match input with
    | .float value =>
        NativeFloatOutcome ops encode .u64 value world
          (JuliaLean.base.boot.Models2Group1.FloatConversion.unsigned ops encode input world)
    | .bool value =>
        NativeBoolOutcome .u64 value world
          (JuliaLean.base.boot.Models2Group1.FloatConversion.unsigned ops encode input world)

/-- Integer's complete Float16/32/64 union follows exact Int64 conversion over
every bit pattern, including integral range endpoints, fractional values,
subnormals, infinities, both zeros and all NaN encodings. Failure retains every
InexactError field and the original world; success retains the exact value.
Julia source: `base/boot.jl:1221`; integer-conversion promise:
`doc/src/manual/mathematical-operations.md:547-551,568-577`.
-/
def IntegerIEEEInvariant : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (encode : IEEEInput → L)
    (input : IEEEInput) (world : W),
    NativeFloatOutcome ops encode .i64 input world
      (JuliaLean.base.boot.Models2Group1.FloatConversion.integer ops encode input world)

/-- Add these entries to the assigned proof namespace's entriesModels2Group1.
The two dependency entries cover the concrete closure used by the three queued
public methods; no extra queue rows are claimed for those dependencies.
-/
def entriesFloatConversions : List Entry := [
  { id := "boot-ieee-isinteger"
    juliaFile := "base/floatfuncs.jl"
    juliaFns := ["isinteger(::Float16)", "isinteger(::Float32)", "isinteger(::Float64) (required concrete dependency)"]
    statement := "For every raw IEEE bit pattern, isinteger's truncation/subtraction/zero-test body recognizes exactly finite values equal to a mathematical integer."
    source := "Invariant; base/floatfuncs.jl:51; base/rounding.jl:480; base/float.jl:458,488,615"
    status := .todo
    prop := ``IsIntegerIEEEInvariant
    thm := none
    notes := "Required concrete closure in Models2Group1.FloatConversion.isIntegerFloat; uses only installed raw-bit IEEE C intrinsic models. No other group's queue is claimed." },
  { id := "boot-native-ieee-constructors"
    juliaFile := "base/float.jl"
    juliaFns := ["Int64(::Union{Float16,Float32,Float64})", "UInt64(::Union{Float16,Float32,Float64}) (required concrete dependencies)"]
    statement := "The required generated native integer constructors accept exactly mathematically representable IEEE values and preserve full InexactError function/type/original-operand fields for every rejected raw bit pattern."
    source := "base/float.jl:881-931; doc/src/manual/mathematical-operations.md:547-551,568-577"
    status := .todo
    prop := ``NativeIEEEConstructorsInvariant
    thm := none
    notes := "Covers int64FromIEEE/uint64FromIEEE, fromInt64/fromUInt64, truncFloat, unsafeTruncInt64/unsafeTruncUInt64, and their installed C primitives. These are necessary local dependencies only; the supplied base/float.lean import is unavailable and was not compiled." },
  { id := "boot-signed-ieee-bool"
    juliaFile := "base/boot.jl"
    juliaFns := ["Signed(x::Union{Float16, Float32, Float64, Bool})"]
    statement := "Signed converts every exactly representable float to its equal Int64 value, maps Bool to zero/one, and otherwise throws the full InexactError while preserving the original float bits and world."
    source := "base/boot.jl:1217; doc/src/manual/mathematical-operations.md:547-551,568-577"
    status := .todo
    prop := ``SignedIEEEBoolInvariant
    thm := none
    notes := "Complete closed union dispatch in Models2Group1.FloatConversion.signed. Quantifies all three IEEE bit-pattern domains and both Bool values, with arbitrary pure representation embeddings and no behavior callbacks." },
  { id := "boot-unsigned-ieee-bool"
    juliaFile := "base/boot.jl"
    juliaFns := ["Unsigned(x::Union{Float16, Float32, Float64, Bool})"]
    statement := "Unsigned converts exactly representable nonnegative integral IEEE values to UInt64, accepts either signed zero, maps Bool to zero/one, and otherwise preserves the original bits in the full InexactError."
    source := "base/boot.jl:1218; doc/src/manual/mathematical-operations.md:547-551,568-577"
    status := .todo
    prop := ``UnsignedIEEEBoolInvariant
    thm := none
    notes := "Complete closed union dispatch in Models2Group1.FloatConversion.unsigned. The source's rounded typemax-plus-one bound is computed in each IEEE format, not approximated using host arithmetic." },
  { id := "boot-integer-ieee"
    juliaFile := "base/boot.jl"
    juliaFns := ["Integer(x::Union{Float16, Float32, Float64})"]
    statement := "Integer converts the entire IEEE union exactly to Int64 when mathematically representable; every fractional, nonfinite or out-of-range encoding throws the full InexactError with unchanged original operand and world."
    source := "base/boot.jl:1221; doc/src/manual/mathematical-operations.md:547-551,568-577"
    status := .todo
    prop := ``IntegerIEEEInvariant
    thm := none
    notes := "Complete concrete Int64 constructor call in Models2Group1.FloatConversion.integer. No finiteness or range premise narrows the source union." }
]

end JuliaLean.Proofs.base.boot.Models2Group1.FloatConversion


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot.Models2Group1

/-- The unsigned mathematical address represented by every accepted Ptr input.
The signed case is specified by congruence modulo 2^64, independently of the
installed bitcast implementation. Source: base/boot.jl:1203. -/
def PointerInputAddress {P : Type} : PointerInput P → Int
  | .signed x => x.val % (2^64 : Int)
  | .unsigned x => x.val
  | .pointer x => x.address.val

/-- Independent pointer-bitcast outcome: the actual target metadata determines
whether an ErrorException is required; successful values retain the target
parameter and the mathematical unsigned address. Source: base/boot.jl:1203;
src/runtime_intrinsics.c:439-453. -/
def PointerCastOutcome {P : Type} (target : PointerTarget P) (address : Int) :
    JuliaLean.BootCov.R (ParameterizedPointer P) → Prop
  | .error exception => target.isConcrete = false ∧
      exception = .error "bitcast: target type not a leaf primitive type"
  | .ok value => target.isConcrete = true ∧ value.parameter = target.parameter ∧
      value.address.val = address

/-- Every native address and actual target metadata state is covered, including
nonconcrete targets. Successful bitcasts retain the target Ptr parameter; the
optional-argument form is exactly its null pointer. No extra concreteness
precondition narrows the source family. Source: base/boot.jl:1203;
src/runtime_intrinsics.c:439-453. -/
def ParameterizedPointerBits : Prop :=
  ∀ (P : Type) (target : PointerTarget P) (input : PointerInput P),
    PointerCastOutcome target (PointerInputAddress input) (pointerCtor target input) ∧
    PointerCastOutcome target 0 (pointerDefault target)

/-- The concrete target-concreteness error or the exact Backend and byte fields
are observable for every AddrSpace input. Source: base/boot.jl:1204;
src/runtime_intrinsics.c:439-453. -/
def AddressSpaceCastOutcome {P : Type} (target : AddressSpaceTarget P) (x : JInt .u8) :
    JuliaLean.BootCov.R (ParameterizedAddressSpace P) → Prop
  | .error exception => target.isConcrete = false ∧
      exception = .error "bitcast: target type not a leaf primitive type"
  | .ok value => target.isConcrete = true ∧ value.backend = target.backend ∧
      value.bits.val = x.val

/-- AddrSpace either rejects a nonconcrete target before bitcasting, or retains
its full Backend parameter and all eight original bits. No target-concreteness
or numeric-range hypothesis is imposed. Source: base/boot.jl:1204. -/
def ParameterizedAddressSpaceBits : Prop :=
  ∀ (P : Type) (target : AddressSpaceTarget P) (x : JInt .u8),
    AddressSpaceCastOutcome target x (addressSpaceCtor target x)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem parameterizedAddressSpaceBits_proven : ParameterizedAddressSpaceBits := by
  intro P target x
  cases h : target.isConcrete <;>
    simp [addressSpaceCtor, AddressSpaceCastOutcome, h, JuliaLean.BootCov.IntConv.addrSpaceOf]
  · rfl
  · refine ⟨rfl, ?_⟩
    change wrapInt .u8 x.val = x.val
    exact wrapInt_of_inRange .u8 x.val x.property
end

/-- Reading an Array size tuple preserves its arity and every stored native
dimension. It is independent of all unobserved array fields, including element
type, memory references and identity. No arbitrary positive-dimension or
well-indexed input restriction is added. Source: base/boot.jl:1287. -/
def ArraySizeTupleFields : Prop :=
  ∀ (V : Type) (array : ConcreteArrayHeader V) (other : V),
    let result := arraySizeTuple array
    result.values.length = array.size.values.length ∧
    (∀ index : Nat, result.values[index]? = array.size.values[index]?) ∧
    (arraySizeTuple { array with otherFields := other }).values = result.values

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem arraySizeTupleFields_proven : ArraySizeTupleFields := by
  intro V array other
  exact ⟨rfl, fun _ => rfl, rfl⟩
end

/-- Independent complete outcome specification in terms of the mathematical
native index and observed size-tuple slots. Nonpositive indices have BoundsError
with the exact original tuple/index; stored dimensions are returned unchanged;
strictly trailing dimensions have size one. Source: base/boot.jl:1288. -/
def ArraySizeOutcome {V : Type} (array : ConcreteArrayHeader V) (i : JInt .i64) :
    Except ArraySizeBoundsError (JInt .i64) → Prop
  | .error error =>
      i.val ≤ 0 ∧ error.exception = .bounds ∧
      error.index = i ∧ error.tuple.values = array.size.values
  | .ok size =>
      (i.val > (array.size.values.length : Int) ∧ size.val = 1) ∨
      (1 ≤ i.val ∧ i.val ≤ (array.size.values.length : Int) ∧
        array.size.values[(i.val-1).toNat]? = some size)

/-- All native Int indices are covered, including typemin, zero and typemax,
for every actual native-size tuple including rank zero. The stored tuple arity
cannot overflow the native count because its runtime nfields field is UInt32.
Source: base/boot.jl:1288; base/runtime_internals.jl:626,716-723. -/
def ArraySizeIndexSemantics : Prop :=
  ∀ (V : Type) (array : ConcreteArrayHeader V) (i : JInt .i64),
    ArraySizeOutcome array i (arraySizeAt array i)

def entriesMetadata : List Entry := [
  { id := "boot-parameterized-pointer-bits", juliaFile := "base/boot.jl"
    juliaFns := ["(PT::Type{Ptr{T}} where T)(x::Union{Int,UInt,Ptr}=0)"]
    statement := "Ptr bitcasts reject nonconcrete target metadata, otherwise preserve all native address bits and target parameters; the omitted argument yields the target null pointer."
    source := "base/boot.jl:1203; native pointer bitcast and null-pointer invariants"
    status := .todo, prop := ``ParameterizedPointerBits, thm := none
    notes := "Covers pointerCtor and the optional-argument pointerDefault dependency. Existing concrete bitcast models are used; no pointer is dereferenced." },
  { id := "boot-parameterized-address-space", juliaFile := "base/boot.jl"
    juliaFns := ["(AS::Type{AddrSpace{Backend}} where Backend)(x::UInt8)"]
    statement := "AddrSpace rejects nonconcrete target metadata before bitcasting and otherwise retains the complete Backend parameter and all eight source bits."
    source := "base/boot.jl:1204; bitcast invariant"
    status := .proven, prop := ``ParameterizedAddressSpaceBits, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.parameterizedAddressSpaceBits_proven },
  { id := "boot-array-size-tuple", juliaFile := "base/boot.jl"
    juliaFns := ["arraysize(a::Array)"]
    statement := "arraysize preserves the stored size tuple's arity and every dimension, independently of unobserved array fields."
    source := "base/boot.jl:1287; Array.size field observation"
    status := .proven, prop := ``ArraySizeTupleFields, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.arraySizeTupleFields_proven },
  { id := "boot-array-size-index", juliaFile := "base/boot.jl"
    juliaFns := ["arraysize(a::Array, i::Int)"]
    statement := "Indexed arraysize returns stored dimensions, returns one past rank, and reports BoundsError with the original size tuple/index for every nonpositive native index."
    source := "base/boot.jl:1288; base/runtime_internals.jl:626,716-723"
    status := .todo, prop := ``ArraySizeIndexSemantics, thm := none }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

/-- DataType's actual TypeName field is invariant under all changes to its
unobserved metadata and its own identity. Identically spelled types are not
collapsed: distinct TypeName handles remain distinct results.
Source: base/boot.jl:1311. -/
def DataTypeNameField : Prop :=
  ∀ (V : Type) (metadata : DataTypeNameMetadata V) (other : V) (identity : Nat),
    typeNameDataType metadata = metadata.name ∧
    typeNameDataType { metadata with rest := other, identity := identity } =
      typeNameDataType metadata

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem dataTypeNameField_proven : DataTypeNameField := by
  unfold DataTypeNameField
  intros
  exact ⟨rfl, rfl⟩
end

def entriesTypeNames : List Entry := [
  { id := "boot-datatype-name-field", juliaFile := "base/boot.jl"
    juliaFns := ["typename(a::DataType)"]
    statement := "DataType typename returns the actual TypeName object identity, independently of other metadata or the DataType object's own identity."
    source := "base/boot.jl:1311; TypeName identity field invariant"
    status := .proven, prop := ``DataTypeNameField, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.dataTypeNameField_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

/-!
Independent coverage for the existing concrete Symbol models. Raw storage is
native-sized UInt8 data, not Lean Unicode text. For Array{UInt8,1}, an offset
and length select the visible array window inside its backing byte storage;
the window validity conditions are representation invariants. The installed
model's Nat offset and length are mathematical byte locations/counts, with no
unbounded replacement of Julia integer arithmetic. Its source performs no
arithmetic on either value, and all counts here fit the native Int range.

Symbols are interned immutable byte names. The result records the name's byte
value independently of any mutable Array backing storage; subsequent changes
to that storage cannot mutate the returned name. No Unicode-validity condition
or additional identifier restriction is imposed.
-/

/-- Native-sized raw storage for String and Array{UInt8,1}. Every source byte,
including invalid UTF-8 and NUL, is represented. -/
structure SymbolStorage where
  bytes : List UInt8
  nativeSize : bytes.length ≤ IntTy.i64.max.toNat

/-- A valid Array{UInt8,1} view of backing storage. Offsets are abstract byte
addresses relative to this storage, not Julia arithmetic. -/
structure SymbolArrayWindow where
  storage : SymbolStorage
  offset : Nat
  length : Nat
  inBounds : offset + length ≤ storage.bytes.length

/-- A valid interned Symbol name. The representation invariants match the
runtime's NUL rule and native-sized storage; no UTF-8 premise is imposed. -/
structure SymbolExistingName where
  storage : SymbolStorage
  noNul : (0 : UInt8) ∉ storage.bytes

/-- Independent byte observations: exact count and every byte by index. -/
def HasSymbolBytes (result : JuliaLean.BootCov.R (List Nat)) (size : Nat)
    (byteAt : Nat → Option Nat) : Prop :=
  ∃ bytes, result = .ok bytes ∧ bytes.length = size ∧
    ∀ i, i < size → bytes[i]? = byteAt i

/-- Symbol(s::String) preserves every byte of each NUL-free native-sized
String, including empty and invalid-UTF-8 names. This uses indexed observations
instead of restating the installed helper's take/contains body.
Source: `base/boot.jl:864-868`; `doc/src/manual/strings.md` permits invalid UTF-8;
`doc/src/manual/metaprogramming.md`, Symbols, describes interned names. -/
def SymbolStringByteObservations : Prop :=
  ∀ s : SymbolStorage, (0 : UInt8) ∉ s.bytes →
    HasSymbolBytes (JuliaLean.BootCov.Arrays.symbolOfString (s.bytes.map UInt8.toNat))
      s.bytes.length (fun i => s.bytes[i]?.map UInt8.toNat)

/-- The concrete String constructor rejects exactly the inputs containing NUL,
and the rejection is ArgumentError rather than another exception class.
Source: `base/boot.jl:864-868`; installed symbolOfString/symbolN runtime rule. -/
def SymbolStringNulExactly : Prop :=
  ∀ s : SymbolStorage,
    ((∃ message, JuliaLean.BootCov.Arrays.symbolOfString (s.bytes.map UInt8.toNat) =
      .error (.argument message)) ↔ (0 : UInt8) ∈ s.bytes) ∧
    ∀ error, JuliaLean.BootCov.Arrays.symbolOfString (s.bytes.map UInt8.toNat) = .error error →
      ∃ message, error = .argument message

/-- Symbol(Array{UInt8,1}) reads exactly the visible array window, retaining
byte order and excluding all prefix/suffix bytes of its backing storage.
NUL outside the visible window does not reject an otherwise valid name.
Source: `base/boot.jl:869-872`; exact-count and indexed-byte invariant. -/
def SymbolArrayByteObservations : Prop :=
  ∀ a : SymbolArrayWindow,
    (∀ i, i < a.length → a.storage.bytes[a.offset + i]? ≠ some (0 : UInt8)) →
    HasSymbolBytes
      (JuliaLean.BootCov.Arrays.symbolOfVector (a.storage.bytes.map UInt8.toNat)
        a.offset a.length)
      a.length (fun i => a.storage.bytes[a.offset + i]?.map UInt8.toNat)

/-- Exactly a NUL in the visible array window causes ArgumentError. Prefix or
suffix NUL bytes outside the window are irrelevant. No other exception class
is returned for a valid native-sized Array{UInt8,1} representation.
Source: `base/boot.jl:869-872`; concrete installed symbolOfVector/symbolN rule. -/
def SymbolArrayNulExactly : Prop :=
  ∀ a : SymbolArrayWindow,
    ((∃ message, JuliaLean.BootCov.Arrays.symbolOfVector (a.storage.bytes.map UInt8.toNat)
      a.offset a.length = .error (.argument message)) ↔
      ∃ i, i < a.length ∧ a.storage.bytes[a.offset + i]? = some (0 : UInt8)) ∧
    ∀ error, JuliaLean.BootCov.Arrays.symbolOfVector (a.storage.bytes.map UInt8.toNat)
      a.offset a.length = .error error → ∃ message, error = .argument message

/-- Existing Symbol input retains its interned identity, represented by its
complete original byte name. Length and every byte are observed independently.
Source: `base/boot.jl:873`; `doc/src/manual/metaprogramming.md`, Symbols. -/
def SymbolIdentityByteObservations : Prop :=
  ∀ s : SymbolExistingName,
    let result := JuliaLean.BootCov.Arrays.symbolOfSymbol (s.storage.bytes.map UInt8.toNat)
    result.length = s.storage.bytes.length ∧
    ∀ i, i < s.storage.bytes.length → result[i]? = s.storage.bytes[i]?.map UInt8.toNat

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem symbolIdentityByteObservations_proven : SymbolIdentityByteObservations := by
  intro s
  simp [JuliaLean.BootCov.Arrays.symbolOfSymbol, List.getElem?_map]
end

/-- The local bootstrap length only observes the number of visible slots.
Slot payloads are uninspected markers for arbitrary element types, including
unassigned slots; representation does not require reading an undefined value.
Native-sized lists represent every valid concrete one-dimensional Array size.
Source: `base/boot.jl:879`; stored-size invariant. -/
def BootstrapArrayLength : Prop :=
  ∀ (L : Type) (slots : List (JuliaLean.base.expr.Value L)),
    slots.length ≤ IntTy.i64.max.toNat →
    (JuliaLean.base.boot.length slots).val = (slots.length : Int)

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem bootstrapArrayLength_proven : BootstrapArrayLength := by
  intro L slots h
  change wrapInt .i64 (slots.length : Int) = (slots.length : Int)
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (slots.length : Int) ∧ (slots.length : Int) ≤ 9223372036854775807
  change slots.length ≤ 9223372036854775807 at h
  omega
end

/-- GeneratedFunctionStub retains all three input objects, including mutable
generator and SimpleVector identities, with exactly three defined fields.
Source: `base/boot.jl:1008-1013`; immutable constructor field invariant. -/
def GeneratedFunctionStubFields : Prop :=
  ∀ (gen argnames spnames : JuliaLean.BootCov.JVal),
    let result := JuliaLean.BootCov.Objects.generatedFunctionStub gen argnames spnames
    (∃ fields, result = .obj "GeneratedFunctionStub" fields ∧ fields.length = 3) ∧
    JuliaLean.BootCov.getfieldObj result 1 = .ok gen ∧
    JuliaLean.BootCov.getfieldObj result 2 = .ok argnames ∧
    JuliaLean.BootCov.getfieldObj result 3 = .ok spnames ∧
    JuliaLean.BootCov.isdefinedObj result 1 = true ∧
    JuliaLean.BootCov.isdefinedObj result 2 = true ∧
    JuliaLean.BootCov.isdefinedObj result 3 = true

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem generatedFunctionStubFields_proven : GeneratedFunctionStubFields := by
  intro gen argnames spnames
  exact ⟨⟨[some gen, some argnames, some spnames], rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
end

/-- The default NamedTuple has no named fields or indexed field values. Its
legacy result carrier is the immutable ordered name/value field sequence;
the zero-argument method has the unique NamedTuple{(),Tuple{}} result type.
Source: `base/boot.jl:1022`; empty-constructor invariant. -/
def EmptyNamedTupleHasNoFields : Prop :=
  JuliaLean.BootCov.Objects.namedTupleEmpty.length = 0 ∧
    ∀ i : Nat, JuliaLean.BootCov.Objects.namedTupleEmpty[i]? = none

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem emptyNamedTupleHasNoFields_proven : EmptyNamedTupleHasNoFields := by
  exact ⟨rfl, fun _ => rfl⟩
end

/-- New todo entries for reused complete methods. The Symbol entries also
cover their installed concrete symbolN dependency without any assumed laws. -/
def symbolBootstrapReuseEntries : List Entry := [
  { id := "boot-symbol-string-byte-observations", juliaFile := "base/boot.jl"
    juliaFns := ["Symbol(s::String)"]
    statement := "Every NUL-free concrete String produces an interned Symbol with the same native-sized byte count and byte at every index, including empty and invalid-UTF-8 names."
    source := "base/boot.jl:864-868; doc/src/manual/strings.md; doc/src/manual/metaprogramming.md, Symbols"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.SymbolStringByteObservations
    notes := "Reuses BootCov.Arrays.symbolOfString; registered dependency symbolN. Native-sized UInt8 input; no UTF-8 restriction or callback law." },
  { id := "boot-symbol-string-nul-exactly", juliaFile := "base/boot.jl"
    juliaFns := ["Symbol(s::String)"]
    statement := "Symbol(s::String) raises ArgumentError exactly when a byte of the String is NUL; no other exception class occurs in its concrete byte-name validation."
    source := "base/boot.jl:864-868; installed symbolN NUL rule"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.SymbolStringNulExactly
    notes := "Full error domain and converse; reuses existing concrete helper, no duplicated model." },
  { id := "boot-symbol-array-byte-observations", juliaFile := "base/boot.jl"
    juliaFns := ["Symbol(a::Array{UInt8, 1})"]
    statement := "Symbol of a UInt8 vector retains exactly its visible window's length and ordered bytes, excluding backing-storage prefix and suffix bytes."
    source := "base/boot.jl:869-872; independent byte-window invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.SymbolArrayByteObservations
    notes := "Reuses BootCov.Arrays.symbolOfVector and symbolN. Native-sized storage and valid offset/window are representation invariants." },
  { id := "boot-symbol-array-nul-exactly", juliaFile := "base/boot.jl"
    juliaFns := ["Symbol(a::Array{UInt8, 1})"]
    statement := "A UInt8 vector produces ArgumentError exactly when its visible window contains NUL; NUL outside that window is irrelevant and no other validation exception occurs."
    source := "base/boot.jl:869-872; installed symbolN NUL rule"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.SymbolArrayNulExactly
    notes := "Error iff uses indexed underlying-storage observations, not the model's drop/take expression. Mutable byte storage is read as a snapshot." },
  { id := "boot-symbol-identity-byte-observations", juliaFile := "base/boot.jl"
    juliaFns := ["Symbol(s::Symbol)"]
    statement := "Symbol(s::Symbol) retains the existing interned name's length and every original byte, preserving Symbol identity."
    source := "base/boot.jl:873; doc/src/manual/metaprogramming.md, interned Symbols"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.symbolIdentityByteObservations_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.SymbolIdentityByteObservations
    notes := "Reuses BootCov.Arrays.symbolOfSymbol over every valid native-sized raw-byte Symbol name." },
  { id := "boot-bootstrap-array-length", juliaFile := "base/boot.jl"
    juliaFns := ["length(a::Array{T, 1}) where {T}"]
    statement := "The bootstrap vector length returns its exact visible slot count as native Int, for every element type and without inspecting initialized or uninitialized slot contents."
    source := "base/boot.jl:879; native Array size invariant"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.bootstrapArrayLength_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.BootstrapArrayLength
    notes := "Reuses boot.length. List elements are uninspected storage-slot markers; only native-sized count matters, so arbitrary T and undefined contents remain represented." },
  { id := "boot-generated-function-stub-fields", juliaFile := "base/boot.jl"
    juliaFns := ["GeneratedFunctionStub(@nospecialize(gen), argnames::SimpleVector, spnames::SimpleVector)"]
    statement := "GeneratedFunctionStub has exactly three defined fields containing the unchanged generator, argument-name SimpleVector, and static-parameter-name SimpleVector."
    source := "base/boot.jl:1008-1013; independent stored-field and definedness invariant"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.generatedFunctionStubFields_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.GeneratedFunctionStubFields
    notes := "Reuses BootCov.Objects.generatedFunctionStub, whose opaque payloads preserve mutable identities and uninspected SimpleVector contents; bypasses the current bad-cf model." },
  { id := "boot-empty-named-tuple-fields", juliaFile := "base/boot.jl"
    juliaFns := ["NamedTuple()"]
    statement := "The zero-argument NamedTuple constructor returns the unique empty named tuple, with zero fields and no indexed field value."
    source := "base/boot.jl:1022; independent empty-field invariant"
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.emptyNamedTupleHasNoFields_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.EmptyNamedTupleHasNoFields
    notes := "Reuses BootCov.Objects.namedTupleEmpty; its result type is fixed to NamedTuple{(),Tuple{}} and the field sequence is empty." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

/-- The same-type Number constructor returns the exact original value,
including every custom Number subtype and opaque mutable identity. Source
dispatch supplies the accepted T <: Number typing; the body does not inspect
the payload or invoke a conversion. Source: `base/boot.jl:1195`. -/
def NumberConstructorIdentity : Prop :=
  ∀ (L : Type) (x : JuliaLean.base.expr.Value L),
    JuliaLean.base.boot.Number_identity x = x

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem numberConstructorIdentity_proven : NumberConstructorIdentity := by
  unfold NumberConstructorIdentity
  intros
  rfl
end

/-- Int(pointer) interprets every 64-bit address as its signed two's-complement
integer, including the upper half of the address space. Pointee type is
unobserved by this integer-returning method. This mathematical specification
does not call the model's wrapping or bitcast helpers.
Source: `base/boot.jl:1197`; native pointer bit-pattern invariant. -/
def PointerIntBitInterpretation : Prop :=
  ∀ p : JuliaLean.BootCov.IntConv.Ptr,
    (JuliaLean.BootCov.IntConv.intOfPtr p).val =
      if p.addr.val < (2 : Int) ^ 63 then p.addr.val else p.addr.val - (2 : Int) ^ 64

/-- UInt(pointer) preserves the exact unsigned address at every possible
64-bit pointer bit pattern. Pointee type and pointed-to contents are not read.
Source: `base/boot.jl:1198`; pointer address invariant. -/
def PointerUIntAddress : Prop :=
  ∀ p : JuliaLean.BootCov.IntConv.Ptr,
    (JuliaLean.BootCov.IntConv.uintOfPtr p).val = p.addr.val

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem pointerUIntAddress_proven : PointerUIntAddress := by
  intro p
  rfl
end

/-- On the source's guarded Int === Int32 platform, Int64(pointer) returns
the nonnegative mathematical 32-bit address without error, divergence, or
state changes. This method is not installed on the packet's 64-bit platform;
the proposition covers precisely its conditional source declaration.
Source: `base/boot.jl:1199-1202`, method at line 1200. -/
def Pointer32ToInt64Exact : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (address : JInt .u32) (world : W),
    ∃ result, JuliaLean.base.boot.Int64_Ptr32 ops address world =
      some (.ok (result, world)) ∧ result.val = address.val

/-- On the source's guarded Int === Int32 platform, UInt64(pointer) returns
the exact unsigned 32-bit address without error, divergence, or state changes.
The guard is part of the source method's installation context, rather than an
additional restriction on pointer values. Source: `base/boot.jl:1199-1202`,
method at line 1201. -/
def Pointer32ToUInt64Exact : Prop :=
  ∀ (W L : Type) (ops : CoreOps W L) (address : JInt .u32) (world : W),
    ∃ result, JuliaLean.base.boot.UInt64_Ptr32 ops address world =
      some (.ok (result, world)) ∧ result.val = address.val

/-- Integer(x::Integer) preserves the original input, including non-native
and user-defined Integer subtypes. Input typing is established by source
dispatch and no operation observes or converts the payload.
Source: `base/boot.jl:1220`; identity-constructor invariant. -/
def IntegerConstructorIdentity : Prop :=
  ∀ (L : Type) (x : JuliaLean.base.expr.Value L),
    JuliaLean.base.boot.Integer_Integer x = x

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem integerConstructorIdentity_proven : IntegerConstructorIdentity := by
  unfold IntegerConstructorIdentity
  intros
  rfl
end

/-- The transparent installed TypeNameError object has precisely one defined
field holding the original arbitrary input, including an opaque mutable object
identity. Observing fields does not require any object-encoding law.
Source: `base/boot.jl:1305-1308`, constructor at line 1307. -/
def TypeNameErrorStoredField : Prop :=
  ∀ input : JuliaLean.BootCov.JVal,
    let result := JuliaLean.BootCov.Objects.typeNameError input
    (∃ fields, result = .obj "TypeNameError" fields ∧ fields.length = 1) ∧
      JuliaLean.BootCov.getfieldObj result 1 = .ok input ∧
      JuliaLean.BootCov.isdefinedObj result 1 = true

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem typeNameErrorStoredField_proven : TypeNameErrorStoredField := by
  intro input
  exact ⟨⟨[some input], rfl, rfl⟩, rfl, rfl⟩
end

/-- MacroSource has exactly its two advertised defined fields, retaining both
original arbitrary input values in their source positions. Raw symbols,
custom objects, and mutable inputs can use the existing opaque identity
carrier; this constructor never inspects or converts either payload.
Source: `base/boot.jl:1332-1336`, constructor at line 1335. -/
def MacroSourceStoredFields : Prop :=
  ∀ (line syntaxVersion : JuliaLean.BootCov.JVal),
    let result := JuliaLean.BootCov.Objects.macroSource line syntaxVersion
    (∃ fields, result = .obj "MacroSource" fields ∧ fields.length = 2) ∧
      JuliaLean.BootCov.getfieldObj result 1 = .ok line ∧
      JuliaLean.BootCov.getfieldObj result 2 = .ok syntaxVersion ∧
      JuliaLean.BootCov.isdefinedObj result 1 = true ∧
      JuliaLean.BootCov.isdefinedObj result 2 = true

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem macroSourceStoredFields_proven : MacroSourceStoredFields := by
  intro line syntaxVersion
  exact ⟨⟨[some line, some syntaxVersion], rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
end

/-- Narrow independent todo properties for nine complete installed methods.
The global-hook setters are excluded: their current Hooks state omits binding
metadata and cannot justify a complete setglobal! error/state claim. -/
def tailReuseEntries : List Entry := [
  { id := "boot-number-constructor-identity", juliaFile := "base/boot.jl"
    juliaFns := ["(::Type{T})(x::T) where {T<:Number}"]
    statement := "The same-type Number constructor preserves the exact input, including every custom Number subtype and original object identity."
    source := "base/boot.jl:1195; identity-constructor invariant"
    notes := "Reuses JuliaLean.base.boot.Number_identity unchanged; source dispatch establishes the accepted input type."
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.numberConstructorIdentity_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NumberConstructorIdentity },
  { id := "boot-pointer-int-bits", juliaFile := "base/boot.jl"
    juliaFns := ["Int(x::Ptr)"]
    statement := "Int(pointer) returns the signed two's-complement interpretation of every 64-bit address, including addresses with the top bit set."
    source := "base/boot.jl:1197; native pointer bit-pattern invariant"
    notes := "Reuses BootCov.IntConv.intOfPtr and its concrete integer bitcast; no pointer contents or pointee type are observed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.PointerIntBitInterpretation },
  { id := "boot-pointer-uint-address", juliaFile := "base/boot.jl"
    juliaFns := ["UInt(x::Ptr)"]
    statement := "UInt(pointer) returns the exact unsigned 64-bit address for every possible pointer bit pattern."
    source := "base/boot.jl:1198; pointer address invariant"
    notes := "Reuses BootCov.IntConv.uintOfPtr; arbitrary pointee types do not affect this integer result."
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.pointerUIntAddress_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.PointerUIntAddress },
  { id := "boot-pointer32-int64-exact", juliaFile := "base/boot.jl"
    juliaFns := ["Int64(x::Ptr)"]
    statement := "Where Int is Int32, Int64(pointer) terminates with its nonnegative mathematical address and leaves runtime state unchanged."
    source := "base/boot.jl:1199-1202, method 1200; explicit 32-bit installation guard"
    notes := "Reuses boot.Int64_Ptr32. All UInt32 address values and all CoreOps/worlds; the selected widening branch has no callbacks or throwing conversion."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.Pointer32ToInt64Exact },
  { id := "boot-pointer32-uint64-exact", juliaFile := "base/boot.jl"
    juliaFns := ["UInt64(x::Ptr)"]
    statement := "Where Int is Int32, UInt64(pointer) terminates with its exact unsigned address and leaves runtime state unchanged."
    source := "base/boot.jl:1199-1202, method 1201; explicit 32-bit installation guard"
    notes := "Reuses boot.UInt64_Ptr32 over every UInt32 pointer address; this guarded method is not installed on the packet's 64-bit platform."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.Pointer32ToUInt64Exact },
  { id := "boot-integer-constructor-identity", juliaFile := "base/boot.jl"
    juliaFns := ["Integer(x::Integer)"]
    statement := "Integer of an already-Integer input preserves the exact original value, including custom and non-native integer subtypes."
    source := "base/boot.jl:1220; identity-constructor invariant"
    notes := "Reuses JuliaLean.base.boot.Integer_Integer unchanged; no native-only restriction."
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.integerConstructorIdentity_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.IntegerConstructorIdentity },
  { id := "boot-type-name-error-field", juliaFile := "base/boot.jl"
    juliaFns := ["TypeNameError(@nospecialize(a))"]
    statement := "TypeNameError has exactly one defined field containing the unchanged arbitrary input object."
    source := "base/boot.jl:1305-1308, constructor 1307; field identity and definedness invariant"
    notes := "Reuses transparent BootCov.Objects.typeNameError and installed field observers; arbitrary payload identities remain opaque and uninspected."
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.typeNameErrorStoredField_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.TypeNameErrorStoredField },
  { id := "boot-macro-source-fields", juliaFile := "base/boot.jl"
    juliaFns := ["MacroSource(@nospecialize(lno), @nospecialize(syntax_ver))"]
    statement := "MacroSource has exactly two defined fields retaining the original line and syntax-version payloads in their source order."
    source := "base/boot.jl:1332-1336, constructor 1335; field identity and definedness invariant"
    notes := "Reuses transparent BootCov.Objects.macroSource over every arbitrary Any payload, including opaque identities. No generic conversion or representation law."
    status := .proven, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.macroSourceStoredFields_proven
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MacroSourceStoredFields }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot.Models2Group1

/-- An independent outcome observer for Expr construction. Successful objects
are checked by fresh identity, field/slot observations, graph validity and the
old-heap frame. Failed validation preserves all old heap cells and exposes the
correct error class and original offending head. The specification never
constructs an expected heap by copying the allocator's append implementation.
Source: base/boot.jl:327; src/builtins.c:2192-2207; src/rtutils.c:102-105. -/
def ExprConstructorOutcome {L : Type} (before : Heap L) (arguments : ExprArgumentTuple L)
    (result : Except (ExprConstructorError L) (Value L) × Heap L) : Prop :=
  match result.1 with
  | .ok value =>
      ∃ head tail, arguments.values = .symbol head :: tail ∧
        FreshAllocation before result.2 value head tail
  | .error error =>
      result.2 = before ∧
      ((arguments.values = [] ∧
        error.exception = .argument "Expr: too few arguments (expected 1)" ∧
        error.context = "" ∧ error.expected = none ∧ error.got = none) ∨
       (∃ head tail, arguments.values = head :: tail ∧
        (∀ name, head ≠ .symbol name) ∧
        error.exception = .typeError "Expr" ∧ error.context = "" ∧
        error.expected = some .symbol ∧ error.got = some head))

/-- Full constructible argument tuples are covered, including empty tuples,
arbitrary invalid head types, every raw-byte Symbol, and shared/cyclic/undefined
objects among the remaining arguments. Only actual heap-reference and Symbol
representation invariants are required. No initialized-tree, successful-result,
termination or native-specialization premise narrows the source method.
Source: base/boot.jl:327; base/docs/basedocs.jl:712-719;
src/builtins.c:2192-2207 with src/julia.h:2430-2436. -/
def ExprConstructorFullDomain : Prop :=
  ∀ (L : Type) (before : Heap L) (arguments : ExprArgumentTuple L),
    ValidHeap before → (∀ value ∈ arguments.values, ValidValue before value) →
    ExprConstructorOutcome before arguments ((exprConstructor arguments).run before)

theorem exprConstructorFullDomain_proven : ExprConstructorFullDomain := by
  intro L before arguments valid valuesValid
  rcases arguments with ⟨values, arity⟩
  cases values with
  | nil =>
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  | cons head tail =>
    cases head with
    | symbol name =>
      have bound : tail.length ≤ IntTy.i64.max.toNat := by
        change tail.length + 1 ≤ 4294967295 at arity
        change tail.length ≤ 9223372036854775807
        omega
      have hs : ValidSymbolName name := valuesValid (.symbol name) (by simp)
      have ht : ∀ value ∈ tail, ValidValue before value :=
        fun value member => valuesValid value (by simp [member])
      refine ⟨name, tail, rfl, ?_⟩
      change FreshAllocation before (allocExpr name tail bound before).2
        (allocExpr name tail bound before).1 name tail
      exact allocExprHeapInvariant_proven L before name tail bound valid hs ht
    | _ =>
      refine ⟨rfl, Or.inr ⟨_, tail, rfl, ?_, rfl, rfl, rfl, rfl⟩⟩
      intro name eq
      cases eq

def entriesExprConstructor : List Entry := [
  { id := "boot-expr-full-constructor", juliaFile := "base/boot.jl"
    juliaFns := ["Expr(@nospecialize args...)"]
    statement := "Expr validates argument count then Symbol head before any Expr/vector allocation; success creates fresh graph identities and preserves every argument alias, while failure preserves the heap and exact error payload."
    source := "base/boot.jl:327; base/docs/basedocs.jl:712-719; pinned src/builtins.c:2192-2207, src/julia.h:2430-2436, src/rtutils.c:102-105"
    status := .proven, prop := ``ExprConstructorFullDomain, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.exprConstructorFullDomain_proven
    notes := "Full argument domain, not only Symbol-headed specialization. Calls the independently registered allocExpr dependency; original pinned C source confirms all validation and allocation ordering." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-!
Independent observations for the documentation methods. The expected result is
not another executable version of a method. Finite runs have source-location
and dispatch-event witnesses: actual heap fields identify each where link,
every splatted slot is present before firstarg, open calls retain actual
arguments/outcomes/worlds, and the final result comes from a terminal head or
the selected custom method. Divergence requires a reachable divergent callback
or arbitrarily long actual where prefixes. No dispatch laws or termination
assumptions are imposed. These statements are deliberately left unproved.
-/

abbrev DocumentationOutcome (W L : Type) :=
  Except (JuliaLean.base.expr.Value (DocumentationException L) × DocumentationWorld W L)
    (DocumentationValue L × DocumentationWorld W L)

def documentationObservedHead {W L : Type} (world : DocumentationWorld W L) (ref : Nat) :
    Option SymbolName := (world.heap.expressions[ref]?).bind ExprCell.head

def documentationObservedSlots {W L : Type} (world : DocumentationWorld W L) (ref : Nat) :
    Option (List (Option (DocumentationValue L))) := do
  let cell ← world.heap.expressions[ref]?
  let vectorRef ← cell.args
  let vector ← world.heap.argsVectors[vectorRef]?
  pure vector.data

def DocumentationNonExpr {L : Type} (value : DocumentationValue L) : Prop :=
  ∀ ref, value ≠ .exprRef ref

/-- The advertised basic forms, expressed as a classification of values and
observable heap fields, independently of executable control flow. -/
def DocumentationBasicForm {W L : Type} (world : DocumentationWorld W L)
    (value : DocumentationValue L) : Prop :=
  (∃ name, value = .symbol name) ∨
  (∃ payload, value = .other (.quoteNode payload)) ∨
  ∃ ref, value = .exprRef ref ∧ documentationObservedHead world ref = some (symbolName ".")

def DocumentationMissingHead {W L : Type} (world : DocumentationWorld W L)
    (value : DocumentationValue L) : Prop :=
  ∃ ref, value = .exprRef ref ∧ documentationObservedHead world ref = none

def documentationUndefError {L : Type} : JuliaLean.base.expr.Value (DocumentationException L) :=
  .leaf (.runtime { exception := .undefRef })

def documentationBoolError {L : Type} (got : DocumentationValue L) :
    JuliaLean.base.expr.Value (DocumentationException L) :=
  .leaf (.runtime { exception := .typeError "if", expected := some "Bool", got := some got })

def DocumentationNotBool {L : Type} (value : DocumentationValue L) : Prop :=
  ∀ b, value ≠ .bool b

/-- Independent observation of the native _apply_iterate argument boundary.
Every source slot must be initialized before any firstarg call; the actual
call tuple is the ordered prefix with arity equal to the mathematical residue
modulo 2^32. This states bytes/count observations without invoking the model's
JInt wrapping or take implementation. Source: `src/builtins.c:828-1050`;
`src/julia.h:2596-2599`, used at `base/boot.jl:952`. -/
def DocumentationReadArguments {W L : Type} (world : DocumentationWorld W L)
    (ref : Nat) (arguments : List (DocumentationValue L)) : Prop :=
  ∃ allArguments : List (DocumentationValue L),
    documentationObservedSlots world ref = some (allArguments.map some) ∧
    arguments.length = allArguments.length % (2^32 : Nat) ∧
    ∀ i, i < arguments.length → arguments[i]? = allArguments[i]?

/-- Every selected isbasicdoc call terminates with the exact basic-form
classification, or UndefRefError for an undefined Expr head, without mutation.
Source: `base/boot.jl:950`; independent type/head and error invariant. -/
def DocumentationBasicObservations : Prop :=
  ∀ (W L : Type) (world : DocumentationWorld W L) (value : DocumentationValue L),
    ∃ outcome, documentationIsBasic value world = some outcome ∧
      match outcome with
      | .ok (result, after) =>
        after = world ∧ ¬DocumentationMissingHead world value ∧
          ∃ b, result = .bool b ∧ (b = true ↔ DocumentationBasicForm world value)
      | .error (error, after) =>
        after = world ∧ DocumentationMissingHead world value ∧ error = documentationUndefError

/-- The selected Any fallback body returns false on its entire domain,
including Expr input supplied through invoke. Source: `base/boot.jl:953`. -/
def DocumentationFallbackAllValues : Prop :=
  ∀ (L : Type) (value : DocumentationValue L),
    documentationIsCallFallback value = .bool false

inductive DocumentationCall (L : Type) where
  | basic (value : DocumentationValue L)
  | first (arguments : List (DocumentationValue L))
  | call (value : DocumentationValue L)
  | expression (arguments : List (DocumentationValue L))

inductive DocumentationEvent (W L : Type) where
  | returned (call : DocumentationCall L) (value : DocumentationValue L)
      (before after : DocumentationWorld W L)
  | raised (call : DocumentationCall L) (error : JuliaLean.base.expr.Value (DocumentationException L))
      (before after : DocumentationWorld W L)

def documentationUnrecord {W L : Type}
    (world : DocumentationWorld (W × List (DocumentationEvent W L)) L) : DocumentationWorld W L :=
  { heap := world.heap, external := world.external.1 }

def documentationRecordWorld {W L : Type} (world : DocumentationWorld W L)
    (events : List (DocumentationEvent W L)) :
    DocumentationWorld (W × List (DocumentationEvent W L)) L :=
  { heap := world.heap, external := (world.external, events) }

/-- Observe the actual open call without changing its value, exception,
heap mutation, external effects, or divergence. -/
def documentationObserveCall {W L : Type} (call : DocumentationCall L)
    (action : DocumentationM W L (DocumentationValue L)) :
    DocumentationM (W × List (DocumentationEvent W L)) L (DocumentationValue L) :=
  fun recorded =>
    let before := documentationUnrecord recorded
    match action before with
    | none => none
    | some (.ok (value, after)) =>
      some (.ok (value, documentationRecordWorld after
        (recorded.external.2 ++ [.returned call value before after])))
    | some (.error (error, after)) =>
      some (.error (error, documentationRecordWorld after
        (recorded.external.2 ++ [.raised call error before after])))

def documentationObserveDispatch {W L : Type} (dispatch : DocumentationDispatch W L) :
    DocumentationDispatch (W × List (DocumentationEvent W L)) L where
  customBasicSelected world value := dispatch.customBasicSelected (documentationUnrecord world) value
  customBasic value := documentationObserveCall (.basic value) (dispatch.customBasic value)
  firstArgument args := documentationObserveCall (.first args) (dispatch.firstArgument args)
  customCallSelected world value := dispatch.customCallSelected (documentationUnrecord world) value
  customCall value := documentationObserveCall (.call value) (dispatch.customCall value)
  customExprSelected world args := dispatch.customExprSelected (documentationUnrecord world) args
  customExpr args := documentationObserveCall (.expression args) (dispatch.customExpr args)

/-- Every firstarg result is the actual generic-call result at precisely the
native-arity argument prefix. This records one observed call, including its
complete state effect, without assuming default method entry or a result type. -/
def DocumentationFirstReturn {W L : Type}
    (before : DocumentationWorld W L) (args : List (DocumentationValue L))
    (value : DocumentationValue L) (after : DocumentationWorld W L)
    (events : List (DocumentationEvent W L)) : Prop :=
  events = [.returned (.first args) value before after]

/-- Finite source-location witnesses. Each where edge identifies actual
stored fields, full initialized splat and native-arity argument prefix; terminal observations use head
classification, exact source errors, or the actual custom call outcome.
These witnesses are logical paths, not a second executable iscallexpr. -/
inductive DocumentationCallTrace {W L : Type} (dispatch : DocumentationDispatch W L) :
    DocumentationWorld W L → DocumentationValue L → DocumentationOutcome W L →
      List (DocumentationEvent W L) → Prop
  | terminal {world ref head}
      (headStored : documentationObservedHead world ref = some head)
      (notWhere : head ≠ symbolName "where") :
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.ok (.bool (head == symbolName "call"), world)) []
  | missingHead {world ref}
      (missing : documentationObservedHead world ref = none) :
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.error (documentationUndefError, world)) []
  | missingArguments {world ref}
      (whereHead : documentationObservedHead world ref = some (symbolName "where"))
      (missing : documentationObservedSlots world ref = none) :
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.error (documentationUndefError, world)) []
  | undefinedSlot {world ref slots}
      (whereHead : documentationObservedHead world ref = some (symbolName "where"))
      (stored : documentationObservedSlots world ref = some slots)
      (undefined : none ∈ slots) :
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.error (documentationUndefError, world)) []
  | firstRaised {world ref args error after}
      (whereHead : documentationObservedHead world ref = some (symbolName "where"))
      (allStored : DocumentationReadArguments world ref args) :
      DocumentationCallTrace dispatch world (.exprRef ref) (.error (error, after))
        [.raised (.first args) error world after]
  | whereEdge {world ref args first after outcome firstEvents restEvents}
      (whereHead : documentationObservedHead world ref = some (symbolName "where"))
      (allStored : DocumentationReadArguments world ref args)
      (firstObserved : DocumentationFirstReturn world args first after firstEvents)
      (continuation : DocumentationCallTrace dispatch after first outcome restEvents) :
      DocumentationCallTrace dispatch world (.exprRef ref) outcome (firstEvents ++ restEvents)
  | fallback {world value}
      (nonExpr : DocumentationNonExpr value)
      (sourceSelected : dispatch.customCallSelected world value = false) :
      DocumentationCallTrace dispatch world value (.ok (.bool false, world)) []
  | customReturned {world value result after}
      (nonExpr : DocumentationNonExpr value)
      (customSelected : dispatch.customCallSelected world value = true) :
      DocumentationCallTrace dispatch world value (.ok (result, after))
        [.returned (.call value) result world after]
  | customRaised {world value error after}
      (nonExpr : DocumentationNonExpr value)
      (customSelected : dispatch.customCallSelected world value = true) :
      DocumentationCallTrace dispatch world value (.error (error, after))
        [.raised (.call value) error world after]

/-- An actual successful firstarg call used when there is no final trace
because execution diverges. Equality to a callback outcome records that
callback's behavior; it is not a correctness assumption on the callback. -/
def DocumentationFirstActualReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (args : List (DocumentationValue L))
    (value : DocumentationValue L) (after : DocumentationWorld W L) : Prop :=
  dispatch.firstArgument args before = some (.ok (value, after))

def DocumentationWhereStep {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (value : DocumentationValue L)
    (after : DocumentationWorld W L) (next : DocumentationValue L) : Prop :=
  ∃ ref args, value = .exprRef ref ∧
    documentationObservedHead before ref = some (symbolName "where") ∧
    DocumentationReadArguments before ref args ∧
    DocumentationFirstActualReturn dispatch before args next after

inductive DocumentationReach {W L : Type} (dispatch : DocumentationDispatch W L) :
    Nat → DocumentationWorld W L → DocumentationValue L →
      DocumentationWorld W L → DocumentationValue L → Prop
  | zero (world value) : DocumentationReach dispatch 0 world value world value
  | step {n world value before current after next}
      (history : DocumentationReach dispatch n world value before current)
      (edge : DocumentationWhereStep dispatch before current after next) :
      DocumentationReach dispatch (n + 1) world value after next

/-- Divergence is justified by a reachable diverging dispatched call or
unboundedly many actual where links, including cycles and callback mutations.
Mathematical path length is unrelated to Julia integer arithmetic. -/
def DocumentationCallDivergence {W L : Type} (dispatch : DocumentationDispatch W L)
    (world : DocumentationWorld W L) (value : DocumentationValue L) : Prop :=
  (∃ n before current, DocumentationReach dispatch n world value before current ∧
    ((∃ ref args, current = .exprRef ref ∧
      documentationObservedHead before ref = some (symbolName "where") ∧
      DocumentationReadArguments before ref args ∧
      dispatch.firstArgument args before = none) ∨
    (DocumentationNonExpr current ∧ dispatch.customCallSelected before current = true ∧
      dispatch.customCall current before = none))) ∨
  ∀ n, ∃ after next, DocumentationReach dispatch n world value after next

/-- Every selected Expr-method execution has a complete finite observation
path or an actual divergence witness. All callbacks, heaps, cycles, undefined
fields/slots, empty arrays, arrays exceeding UInt32 arity, and arbitrary custom results are quantified with
no laws. Source: `base/boot.jl:952`; independent control/effect/path invariant. -/
def DocumentationCallObservations : Prop :=
  ∀ (W L : Type) (dispatch : DocumentationDispatch W L)
    (world : DocumentationWorld W L) (ref : Nat),
    match documentationIsCallExpr (documentationObserveDispatch dispatch) ref
      (documentationRecordWorld world []) with
    | none => DocumentationCallDivergence dispatch world (.exprRef ref)
    | some (.ok (value, after)) =>
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.ok (value, documentationUnrecord after)) after.external.2
    | some (.error (error, after)) =>
      DocumentationCallTrace dispatch world (.exprRef ref)
        (.error (error, documentationUnrecord after)) after.external.2

/-- An observed isbasicdoc result comes from its source classification or an
actually selected custom call, retaining the resulting heap/external world. -/
def DocumentationBasicReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (input result : DocumentationValue L)
    (after : DocumentationWorld W L) (events : List (DocumentationEvent W L)) : Prop :=
  (dispatch.customBasicSelected before input = false ∧ after = before ∧ events = [] ∧
    ¬DocumentationMissingHead before input ∧
    ∃ b, result = .bool b ∧ (b = true ↔ DocumentationBasicForm before input)) ∨
  (dispatch.customBasicSelected before input = true ∧
    events = [.returned (.basic input) result before after])

def DocumentationBasicRaised {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (input : DocumentationValue L)
    (error : JuliaLean.base.expr.Value (DocumentationException L))
    (after : DocumentationWorld W L) (events : List (DocumentationEvent W L)) : Prop :=
  (dispatch.customBasicSelected before input = false ∧ DocumentationMissingHead before input ∧
    error = documentationUndefError ∧ after = before ∧ events = []) ∨
  (dispatch.customBasicSelected before input = true ∧
    events = [.raised (.basic input) error before after])

/-- Fresh source Expr observations relative to the actual pre-allocation
world. Every old object remains unchanged; the new head and indexed argument
slots retain the required values and identities, without calling any model.
-/
def DocumentationFreshExpression {W L : Type} (before after : DocumentationWorld W L)
    (result : DocumentationValue L) (head : SymbolName)
    (arguments : List (DocumentationValue L)) : Prop :=
  after.external = before.external ∧
  after.heap.expressions.length = before.heap.expressions.length + 1 ∧
  after.heap.argsVectors.length = before.heap.argsVectors.length + 1 ∧
  (∀ i, i < before.heap.expressions.length →
    after.heap.expressions[i]? = before.heap.expressions[i]?) ∧
  (∀ i, i < before.heap.argsVectors.length →
    after.heap.argsVectors[i]? = before.heap.argsVectors[i]?) ∧
  ∃ ref vectorRef cell vector,
    result = .exprRef ref ∧ before.heap.expressions.length ≤ ref ∧
    before.heap.argsVectors.length ≤ vectorRef ∧
    after.heap.expressions[ref]? = some cell ∧ cell.head = some head ∧
    cell.args = some vectorRef ∧ after.heap.argsVectors[vectorRef]? = some vector ∧
    vector.data.length = arguments.length ∧
    ∀ i, i < arguments.length → vector.data[i]? = (arguments[i]?).map some

/-- The fixed escape-node shape used by ignoredoc's true branches. -/
def DocumentationFreshEscape {W L : Type} (before after : DocumentationWorld W L)
    (result argument : DocumentationValue L) : Prop :=
  DocumentationFreshExpression before after result (symbolName "escape") [argument]

/-- A generic Expr return is either a concrete fresh source object or the
actual observed custom result at the correct world and exact argument list.
No restriction is imposed on a custom result's type or identity. -/
def DocumentationExpressionReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (head : SymbolName) (arguments : List (DocumentationValue L))
    (before : DocumentationWorld W L) (result : DocumentationValue L)
    (after : DocumentationWorld W L) (events : List (DocumentationEvent W L)) : Prop :=
  (dispatch.customExprSelected before (.symbol head :: arguments) = false ∧
    events = [] ∧ DocumentationFreshExpression before after result head arguments) ∨
  (dispatch.customExprSelected before (.symbol head :: arguments) = true ∧
    events = [.returned (.expression (.symbol head :: arguments)) result before after])

/-- Known-valid source Expr allocations cannot raise semantic errors; an
observed error here must come from the actually selected custom constructor. -/
def DocumentationExpressionRaised {W L : Type} (dispatch : DocumentationDispatch W L)
    (head : SymbolName) (arguments : List (DocumentationValue L))
    (before : DocumentationWorld W L)
    (error : JuliaLean.base.expr.Value (DocumentationException L))
    (after : DocumentationWorld W L) (events : List (DocumentationEvent W L)) : Prop :=
  dispatch.customExprSelected before (.symbol head :: arguments) = true ∧
    events = [.raised (.expression (.symbol head :: arguments)) error before after]

/-- Actual successful constructor observations used to locate a later
nonterminating call. The supplied callback equation records its unrestricted
actual outcome; it does not assume a callee-correctness law. -/
def DocumentationExpressionActualReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (head : SymbolName) (arguments : List (DocumentationValue L))
    (before : DocumentationWorld W L) (result : DocumentationValue L)
    (after : DocumentationWorld W L) : Prop :=
  (dispatch.customExprSelected before (.symbol head :: arguments) = false ∧
    DocumentationFreshExpression before after result head arguments) ∨
  (dispatch.customExprSelected before (.symbol head :: arguments) = true ∧
    dispatch.customExpr (.symbol head :: arguments) before = some (.ok (result, after)))

/-- A finite call-predicate return is witnessed by actual where edges followed
by a terminal stored head, source fallback, or actual selected custom return.
This is not an executable recursion and contains no call to the model. -/
def DocumentationCallActualReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (input result : DocumentationValue L)
    (after : DocumentationWorld W L) : Prop :=
  ∃ n terminalWorld terminal,
    DocumentationReach dispatch n before input terminalWorld terminal ∧
    ((∃ ref head, terminal = .exprRef ref ∧
       documentationObservedHead terminalWorld ref = some head ∧
       head ≠ symbolName "where" ∧ result = .bool (head == symbolName "call") ∧
       after = terminalWorld) ∨
     (DocumentationNonExpr terminal ∧
       ((dispatch.customCallSelected terminalWorld terminal = false ∧
         result = .bool false ∧ after = terminalWorld) ∨
        (dispatch.customCallSelected terminalWorld terminal = true ∧
         dispatch.customCall terminal terminalWorld = some (.ok (result, after))))))

/-- The marker's finite observations record its mandatory metadata object,
then source/default or actual custom block construction, then escape
construction with the returned block value. Effects and errors remain at their
exact call positions. Source: `base/boot.jl:946-948`. -/
def DocumentationMarkerTrace {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (x : DocumentationValue L)
    (outcome : DocumentationOutcome W L) (events : List (DocumentationEvent W L)) : Prop :=
  ∃ metadata metadataWorld,
    DocumentationFreshExpression before metadataWorld metadata (symbolName "meta")
      [.symbol (symbolName "doc")] ∧
    match outcome with
    | .ok (result, after) =>
      ∃ block blockWorld blockEvents escapeEvents,
        DocumentationExpressionReturn dispatch (symbolName "block") [metadata, x]
          metadataWorld block blockWorld blockEvents ∧
        DocumentationExpressionReturn dispatch (symbolName "escape") [block]
          blockWorld result after escapeEvents ∧
        events = blockEvents ++ escapeEvents
    | .error (error, after) =>
      DocumentationExpressionRaised dispatch (symbolName "block") [metadata, x]
        metadataWorld error after events ∨
      ∃ block blockWorld blockEvents escapeEvents,
        DocumentationExpressionReturn dispatch (symbolName "block") [metadata, x]
          metadataWorld block blockWorld blockEvents ∧
        DocumentationExpressionRaised dispatch (symbolName "escape") [block]
          blockWorld error after escapeEvents ∧
        events = blockEvents ++ escapeEvents

/-- Only a reached custom Expr call may diverge in the marker. A source block
return is specified by fresh field observations; a custom one by its actual
outcome. Both preserve prior effects before reaching the outer call. -/
def DocumentationMarkerDivergence {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (x : DocumentationValue L) : Prop :=
  ∃ metadata metadataWorld,
    DocumentationFreshExpression before metadataWorld metadata (symbolName "meta")
      [.symbol (symbolName "doc")] ∧
    ((dispatch.customExprSelected metadataWorld [.symbol (symbolName "block"), metadata, x] = true ∧
      dispatch.customExpr [.symbol (symbolName "block"), metadata, x] metadataWorld = none) ∨
     ∃ block blockWorld,
       DocumentationExpressionActualReturn dispatch (symbolName "block") [metadata, x]
         metadataWorld block blockWorld ∧
       dispatch.customExprSelected blockWorld [.symbol (symbolName "escape"), block] = true ∧
       dispatch.customExpr [.symbol (symbolName "escape"), block] blockWorld = none)

/-- Full marker body over arbitrary input values, custom constructors, heap
mutations, errors and divergence. A selected custom constructor may return any
value and may change subsequent dispatch selection. Source: `base/boot.jl:946-948`.
-/
def DocumentationMarkerObservations : Prop :=
  ∀ (W L : Type) (dispatch : DocumentationDispatch W L)
    (world : DocumentationWorld W L) (x : DocumentationValue L),
    match documentationMarkerMacro (documentationObserveDispatch dispatch) x
      (documentationRecordWorld world []) with
    | none => DocumentationMarkerDivergence dispatch world x
    | some (.ok (value, after)) =>
      DocumentationMarkerTrace dispatch world x
        (.ok (value, documentationUnrecord after)) after.external.2
    | some (.error (error, after)) =>
      DocumentationMarkerTrace dispatch world x
        (.error (error, documentationUnrecord after)) after.external.2

/-- All finite ignoredoc outcomes. True predicates allocate the fixed
nothing escape. Two false predicates reach the actual generic Expr call on
the original input; its default shape or unrestricted custom outcome is
observed after all earlier effects. Non-Bool tests and errors retain order.
-/
def DocumentationIgnoreTrace {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (expr : DocumentationValue L)
    (outcome : DocumentationOutcome W L) (events : List (DocumentationEvent W L)) : Prop :=
  match outcome with
  | .ok (result, after) =>
    (∃ basicWorld,
      DocumentationBasicReturn dispatch before expr (.bool true) basicWorld events ∧
      DocumentationFreshEscape basicWorld after result (.other .nothing)) ∨
    (∃ basicWorld callWorld basicEvents callEvents,
      DocumentationBasicReturn dispatch before expr (.bool false) basicWorld basicEvents ∧
      DocumentationCallTrace dispatch basicWorld expr (.ok (.bool true, callWorld)) callEvents ∧
      events = basicEvents ++ callEvents ∧
      DocumentationFreshEscape callWorld after result (.other .nothing)) ∨
    (∃ basicWorld callWorld basicEvents callEvents expressionEvents,
      DocumentationBasicReturn dispatch before expr (.bool false) basicWorld basicEvents ∧
      DocumentationCallTrace dispatch basicWorld expr (.ok (.bool false, callWorld)) callEvents ∧
      DocumentationExpressionReturn dispatch (symbolName "escape") [expr]
        callWorld result after expressionEvents ∧
      events = basicEvents ++ callEvents ++ expressionEvents)
  | .error (error, after) =>
    DocumentationBasicRaised dispatch before expr error after events ∨
    (∃ bad,
      DocumentationBasicReturn dispatch before expr bad after events ∧
      DocumentationNotBool bad ∧ error = documentationBoolError bad) ∨
    (∃ basicWorld basicEvents callEvents,
      DocumentationBasicReturn dispatch before expr (.bool false) basicWorld basicEvents ∧
      DocumentationCallTrace dispatch basicWorld expr (.error (error, after)) callEvents ∧
      events = basicEvents ++ callEvents) ∨
    (∃ basicWorld basicEvents callEvents bad,
      DocumentationBasicReturn dispatch before expr (.bool false) basicWorld basicEvents ∧
      DocumentationCallTrace dispatch basicWorld expr (.ok (bad, after)) callEvents ∧
      DocumentationNotBool bad ∧ error = documentationBoolError bad ∧
      events = basicEvents ++ callEvents) ∨
    (∃ basicWorld callWorld basicEvents callEvents expressionEvents,
      DocumentationBasicReturn dispatch before expr (.bool false) basicWorld basicEvents ∧
      DocumentationCallTrace dispatch basicWorld expr (.ok (.bool false, callWorld)) callEvents ∧
      DocumentationExpressionRaised dispatch (symbolName "escape") [expr]
        callWorld error after expressionEvents ∧
      events = basicEvents ++ callEvents ++ expressionEvents)

def DocumentationBasicActualReturn {W L : Type} (dispatch : DocumentationDispatch W L)
    (before : DocumentationWorld W L) (input result : DocumentationValue L)
    (after : DocumentationWorld W L) : Prop :=
  (dispatch.customBasicSelected before input = false ∧ after = before ∧
    ¬DocumentationMissingHead before input ∧
    ∃ b, result = .bool b ∧ (b = true ↔ DocumentationBasicForm before input)) ∨
  (dispatch.customBasicSelected before input = true ∧
    dispatch.customBasic input before = some (.ok (result, after)))

def DocumentationIgnoreDivergence {W L : Type} (dispatch : DocumentationDispatch W L)
    (world : DocumentationWorld W L) (expr : DocumentationValue L) : Prop :=
  (dispatch.customBasicSelected world expr = true ∧ dispatch.customBasic expr world = none) ∨
  (∃ basicWorld,
    DocumentationBasicActualReturn dispatch world expr (.bool false) basicWorld ∧
    DocumentationCallDivergence dispatch basicWorld expr) ∨
  (∃ basicWorld callWorld,
    DocumentationBasicActualReturn dispatch world expr (.bool false) basicWorld ∧
    DocumentationCallActualReturn dispatch basicWorld expr (.bool false) callWorld ∧
    dispatch.customExprSelected callWorld [.symbol (symbolName "escape"), expr] = true ∧
    dispatch.customExpr [.symbol (symbolName "escape"), expr] callWorld = none)

/-- Complete ignoredoc observations over every input and every unrestricted
dispatch implementation: short circuit, custom return values, effects/errors,
divergence, native-sized fresh source allocation, original argument identity,
and unrestricted selected custom Expr constructor outcomes.
Source: `base/boot.jl:954-957`; immutable arguments/fresh Expr invariant. -/
def DocumentationIgnoreObservations : Prop :=
  ∀ (W L : Type) (dispatch : DocumentationDispatch W L)
    (world : DocumentationWorld W L) (source mod str expr : DocumentationValue L),
    match documentationIgnore (documentationObserveDispatch dispatch) source mod str expr
      (documentationRecordWorld world []) with
    | none => DocumentationIgnoreDivergence dispatch world expr
    | some (.ok (value, after)) =>
      DocumentationIgnoreTrace dispatch world expr
        (.ok (value, documentationUnrecord after)) after.external.2
    | some (.error (error, after)) =>
      DocumentationIgnoreTrace dispatch world expr
        (.error (error, documentationUnrecord after)) after.external.2

def documentationEntries : List Entry := [
  { id := "boot-documentation-marker-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["__doc__(x)"]
    statement := "The documentation marker first allocates fixed meta/doc metadata, then calls Expr for block and escape in order, preserving original arguments, all custom results/errors/effects/divergence, or the exact fresh source object at each default call."
    source := "base/boot.jl:946-948; independent allocation, argument/event and effect invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DocumentationMarkerObservations
    notes := "Generic Expr construction is open on x and the returned block value. Default calls use the completed Symbol-headed Expr allocator. Custom constructors may return non-Expr values or mutate subsequent dispatch; no callback laws. Covers documentationFixedExpression and documentationExpressionDispatch." },
  { id := "boot-documentation-basic-observations", juliaFile := "base/boot.jl"
    juliaFns := ["isbasicdoc(@nospecialize x)"]
    statement := "isbasicdoc recognizes exactly Symbols, QuoteNodes and dot-headed Exprs, preserving state; an undefined Expr head raises UndefRefError."
    source := "base/boot.jl:950; independent type/head/error invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DocumentationBasicObservations
    notes := "Full heap/value domain, including undefined fields and cyclic/shared graphs. Registers documentationHead and concrete type-test dependencies." },
  { id := "boot-documentation-call-observations", juliaFile := "base/boot.jl"
    juliaFns := ["iscallexpr(ex::Expr)"]
    statement := "iscallexpr follows actual where links, reads all splatted slots before firstarg dispatch, preserves the UInt32 native-arity prefix and every generic lookup/method outcome and effect, and justifies termination, source errors, or divergence by an observed path."
    source := "base/boot.jl:951-953; doc/src/manual/functions.md, splatting; independent path/effect invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DocumentationCallObservations
    notes := "All callbacks quantified without laws; firstarg generic lookup failures, zero-arity methods and arbitrary return values included. Concrete Expr recursion uses partial_fixpoint; cycles never use a finite-fuel default. Covers head/args/splat/native-arity/source-fallback/dispatch helpers; firstarg is an actual open generic call, not a source-entry approximation. All array slots are read before the call arity wraps; the Array domain is not narrowed to UInt32." },
  { id := "boot-documentation-fallback-all-values", juliaFile := "base/boot.jl"
    juliaFns := ["iscallexpr(ex)"]
    statement := "The selected Any fallback body returns false for every value, including Expr arguments passed using invoke."
    source := "base/boot.jl:953; selected-method return invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DocumentationFallbackAllValues
    notes := "This is the actual fallback body, distinct from generic dispatch and concrete Expr recursion." },
  { id := "boot-documentation-ignore-observations", juliaFile := "base/boot.jl"
    juliaFns := ["ignoredoc(source, mod, str, expr)"]
    statement := "ignoredoc preserves predicate short circuit and Bool checks; true predicates allocate a fixed nothing escape, while two false predicates call Expr on the original argument with exact default freshness or unrestricted selected custom results/errors/effects/divergence."
    source := "base/boot.jl:954-957; doc/src/manual/control-flow.md, Short-Circuit Evaluation; independent trace and allocation invariant"
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.DocumentationIgnoreObservations
    notes := "Covers concrete allocExpr via fixed/default Expr calls, condition/error helpers and explicit predicate/constructor dispatch. Source freshness and old-cell preservation are relative to the final preceding custom world. Arbitrary custom Expr outcomes remain unrestricted; no callback laws or proofs supplied." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

/-- Ghost instrumentation of the exact generic print and println call targets.
The callback retains all possible results, state changes, thrown values and
divergence. No callee law is assumed. -/
def observeLinePrinting {W L : Type} (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L)) :
    LinePrintingDispatch (CoreM (W × List (Invocation L)) L) L where
  printValues io values := recordCall dispatch (coreV encoding "print") (io :: values.values)
  printNewline io := recordCall dispatch (coreV encoding "println") [io]

/-- Independent trace/outcome contract for two source calls. Finite traces have
exactly the first completed call, or both calls in order. The last callback's
actual returned/thrown value and world are retained. Divergence has an actual
reachable diverging callback witness; a failure in the first call prevents the
second. Callback outcome equations describe observations, not correctness laws.
Source: base/boot.jl:1002. -/
def PrintlnCallSequence {W L : Type}
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (first last : Invocation L) (world : W) :
    Option (Except
      (JuliaLean.base.expr.Value L × (W × List (Invocation L)))
      (JuliaLean.base.expr.Value L × (W × List (Invocation L)))) → Prop
  | none =>
      dispatch first.1 first.2 world = none ∨
      ∃ ignored middle,
        dispatch first.1 first.2 world = some (.ok (ignored, middle)) ∧
        dispatch last.1 last.2 middle = none
  | some (.ok (value, (after, trace))) =>
      trace = [first, last] ∧
      ∃ ignored middle,
        dispatch first.1 first.2 world = some (.ok (ignored, middle)) ∧
        dispatch last.1 last.2 middle = some (.ok (value, after))
  | some (.error (error, (after, trace))) =>
      (trace = [first] ∧ dispatch first.1 first.2 world = some (.error (error, after))) ∨
      (trace = [first, last] ∧
        ∃ ignored middle,
          dispatch first.1 first.2 world = some (.ok (ignored, middle)) ∧
          dispatch last.1 last.2 middle = some (.error (error, after)))

/-- Every constructible tail, including empty, performs print before newline
with original arguments and the same IO. The final arbitrary result is retained,
while error/divergence may stop the sequence only at a reached custom call.
Source: base/boot.jl:1002; ordering, arity and effects invariant. -/
def PrintlnValuesSequence : Prop :=
  ∀ (W L : Type) (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (io : JuliaLean.base.expr.Value L) (values : PrintingArguments L) (world : W),
    PrintlnCallSequence dispatch
      (coreV encoding "print", io :: values.values)
      (coreV encoding "println", [io]) world
      (printlnValues (observeLinePrinting encoding dispatch) io values (world, []))

/-- show(a) forwards exactly one call to show with the concrete stdout marker
before the original a. Every callback outcome and state effect is preserved.
No special type/range constraint is imposed on the Any argument.
Source: base/boot.jl:1004. -/
def ShowStdoutDispatch : Prop :=
  ∀ (W L : Type) (encoding : CoreOps (W × List (Invocation L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (value : JuliaLean.base.expr.Value L) (world : W) (trace : List (Invocation L)),
    let stream := JuliaLean.base.boot.stdout encoding
    OneCallObservation trace (coreV encoding "show", [stream, value])
      (dispatch (coreV encoding "show") [stream, value] world)
      (showStdout encoding (observePrinting encoding dispatch) value (world, trace))

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem showStdoutDispatch_proven : ShowStdoutDispatch := by
  intro W L encoding dispatch value world trace
  unfold showStdout observePrinting recordCall
  cases h : dispatch (coreV encoding "show") [stdout encoding, value] world with
  | none => simp [h, OneCallObservation]
  | some outcome =>
    cases outcome with
    | error error => rcases error with ⟨error, after⟩; simp [h, OneCallObservation]
    | ok result => rcases result with ⟨value, after⟩; simp [h, OneCallObservation]
end

def entriesIOForwarding : List Entry := [
  { id := "boot-println-values-sequence", juliaFile := "base/boot.jl"
    juliaFns := ["println(io::IO, @nospecialize x...)"]
    statement := "Vararg println preserves original IO/values, print-before-newline order, and every arbitrary dispatch result, error, state change or divergence, including raw empty-tail invocation."
    source := "base/boot.jl:1002; native call-arity invariant from src/julia.h:2591-2598"
    status := .todo, prop := ``PrintlnValuesSequence, thm := none
    notes := "Only calls selected on unfixed IO/value types are parameters. No callback replaces this method's own body or recursion." },
  { id := "boot-show-stdout-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["show(@nospecialize a)"]
    statement := "The stdout show wrapper forwards one unchanged-argument generic show call with the concrete stdout singleton and preserves all outcomes and effects."
    source := "base/boot.jl:1004; forwarding invariant"
    status := .proven, prop := ``ShowStdoutDispatch, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.showStdoutDispatch_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1.Reflection

open JuliaLean
open JuliaLean.Registry

/-- Specification-only identification of an existing object. Nat is a logical
object name; this observer performs no Julia arithmetic or reflection. -/
def ObjectName {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) : JuliaLean.base.boot.Models2Group1.Reflection.Value V → Nat
  | .dataType identity .. | .unionAll identity .. | .unionType identity ..
  | .typeEq identity .. | .typeEgal identity .. | .typeVar identity ..
  | .typeApp identity .. | .intersect identity .. | .vararg identity .. => identity
  | .bottom => types.bottomValue
  | .other header _ => header.identity

/-- A runtime-header observation from the actual representation fields. The
fixed small-tag table supplies named kinds; other objects retain their stored
DataType handle. The observer never invokes typeof or a callback. -/
def HeaderIs {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V)
    (candidate : Nat) : Prop :=
  match value with
  | .dataType .. => candidate = types.dataType
  | .unionAll .. => candidate = types.unionAll
  | .unionType .. => candidate = types.unionType
  | .typeEq .. => candidate = types.typeEq
  | .typeEgal .. => candidate = types.typeEgal
  | .bottom => candidate = types.typeofBottom
  | .typeVar .. => candidate = types.typeVar
  | .typeApp .. => candidate = types.typeApp
  | .intersect .. => candidate = types.intersect
  | .vararg .. => candidate = types.vararg
  | .other header _ => candidate = header.runtimeType

/-- Membership in the actual runtime kind-tag interval. In particular,
TypeVar, TypeApp, Intersect and Vararg are outside that interval. -/
def TypeObject {V : Type} : JuliaLean.base.boot.Models2Group1.Reflection.Value V → Prop
  | .dataType .. | .unionAll .. | .unionType ..
  | .typeEq .. | .typeEgal .. | .bottom => True
  | _ => False

/-- One permitted edge in the scoped metadata graph. Bounds of a UnionAll are
outside the newly introduced binder; only its body is inside. A DataType with
its cache clear has no traversable edges, and an empty environment observes its
cache directly. The relation has no evaluation order and computes no Boolean. -/
inductive ScopeEdge {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) :
    List Nat → JuliaLean.base.boot.Models2Group1.Reflection.Value V → List Nat → JuliaLean.base.boot.Models2Group1.Reflection.Value V → Prop where
  | parameter {bound identity parameters wrapper rest parameter} :
      bound ≠ [] → parameter ∈ parameters →
      ScopeEdge types bound (.dataType identity true parameters wrapper rest) bound parameter
  | lower {bound identity binder lower upper body rest} :
      ObjectName types lower ≠ types.bottomValue →
      ScopeEdge types bound (.unionAll identity binder lower upper body rest) bound lower
  | upper {bound identity binder lower upper body rest} :
      ObjectName types upper ≠ types.anyValue →
      ScopeEdge types bound (.unionAll identity binder lower upper body rest) bound upper
  | body {bound identity binder lower upper body rest} :
      ScopeEdge types bound (.unionAll identity binder lower upper body rest)
        (binder :: bound) body
  | unionLeft {bound identity left right} :
      ScopeEdge types bound (.unionType identity left right) bound left
  | unionRight {bound identity left right} :
      ScopeEdge types bound (.unionType identity left right) bound right
  | intersectLeft {bound identity left right} :
      ScopeEdge types bound (.intersect identity left right) bound left
  | intersectRight {bound identity left right} :
      ScopeEdge types bound (.intersect identity left right) bound right
  | equalityParameter {bound identity parameter} :
      ScopeEdge types bound (.typeEq identity parameter) bound parameter
  | egalityParameter {bound identity parameter} :
      ScopeEdge types bound (.typeEgal identity parameter) bound parameter
  | varargElement {bound identity element count rest} :
      ScopeEdge types bound (.vararg identity (some element) count rest) bound element
  | varargCount {bound identity element count rest} :
      ScopeEdge types bound (.vararg identity (some element) (some count) rest) bound count

/-- Reachability in the scoped metadata graph, independent of the source's
short-circuit recursion and parameter-loop evaluation order. -/
inductive ScopePath {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) :
    List Nat → JuliaLean.base.boot.Models2Group1.Reflection.Value V → List Nat → JuliaLean.base.boot.Models2Group1.Reflection.Value V → Prop where
  | refl {bound value} : ScopePath types bound value bound value
  | step {bound value nextBound next finalBound final} :
      ScopeEdge types bound value nextBound next →
      ScopePath types nextBound next finalBound final →
      ScopePath types bound value finalBound final

/-- The only terminal witnesses to runtime free-variable presence: an unbound
TypeVar identity, a TypeApp node, or a set DataType cache at empty scope. This
uses actual stored cache data and imposes no cache-correctness hypothesis. -/
def FreeTerminal {V : Type} (bound : List Nat) : JuliaLean.base.boot.Models2Group1.Reflection.Value V → Prop
  | .dataType _ cached _ _ _ => bound = [] ∧ cached = true
  | .typeVar identity .. => identity ∉ bound
  | .typeApp .. => True
  | _ => False

/-- A declarative witness is a scoped path to a free terminal. This specification
contains no call to hasFree and no recursive Boolean implementation. -/
def HasFreeWitness {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (bound : List Nat)
    (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V) : Prop :=
  ∃ finalBound terminal, ScopePath types bound value finalBound terminal ∧
    FreeTerminal finalBound terminal

/-- Concrete runtime header decoding and type-kind classification are exact
field/tag observations for every represented value, preserving actual object
names rather than names of Julia types.
Sources: src/builtins.c:612-616; src/julia.h:197-207,1109-1121,1175-1193,1907-1917;
src/subtype.c:4253-4314,780-783,3210-3219,3796-3805, at the packet pin.
-/
def RuntimeMetadataInvariant : Prop :=
  ∀ (V : Type) (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V),
    HeaderIs types value (JuliaLean.base.boot.Models2Group1.Reflection.runtimeType types value) ∧
    (JuliaLean.base.boot.Models2Group1.Reflection.isType value = true ↔ TypeObject value) ∧
    JuliaLean.base.boot.Models2Group1.Reflection.objectIdentity types value = ObjectName types value

/-- Free-variable testing is exactly reachability of a free terminal through
scope-correct metadata edges. Quantification includes every binder environment,
all parameter sequences, both cache states, repeated/shared TypeVar identities,
all bounds and every concrete kind, with no law imposed on an operation.
The parameter scan has an independent existential specification.
Source: src/jltypes.c:126-191, called by base/boot.jl:303,387.
-/
def FreeVariableScopeInvariant : Prop :=
  (∀ (V : Type) (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V) (bound : List Nat),
    JuliaLean.base.boot.Models2Group1.Reflection.hasFree types value bound = true ↔ HasFreeWitness types bound value) ∧
  (∀ (V : Type) (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (parameters : List (JuliaLean.base.boot.Models2Group1.Reflection.Value V))
      (bound : List Nat),
    JuliaLean.base.boot.Models2Group1.Reflection.hasFreeParameters types parameters bound = true ↔
      ∃ parameter ∈ parameters, HasFreeWitness types bound parameter)

/-- Collect every stored wrapper reference exposed by the permitted metadata
paths, retaining their left-to-right order. This observer gathers the complete
candidate sequence; it does not stop at a first candidate like extract_wrapper.
The list is ghost specification data, not a Julia allocation. -/
def WrapperCandidates {V : Type} : JuliaLean.base.boot.Models2Group1.Reflection.Value V → List JuliaLean.base.boot.Models2Group1.Reflection.StoredReference
  | .dataType _ _ _ none _ => []
  | .dataType _ _ _ (some wrapper) _ => [wrapper]
  | .unionAll _ _ _ _ body _ => WrapperCandidates body
  | .unionType _ left right => WrapperCandidates left ++ WrapperCandidates right
  | .typeVar _ _ upper _ => WrapperCandidates upper
  | _ => []

/-- Wrapper extraction returns the first original stored reference reachable
through the allowed metadata paths, and reports NULL exactly when none exists.
It cannot invent a wrapper, follow a lower TypeVar bound, choose a later Union
arm, inspect a DataType parameter, or confuse equal names with object identity.
Source: src/jltypes.c:2192-2205, used by the reachable jl_wrap_Type closure.
-/
def WrapperSubobjectInvariant : Prop :=
  ∀ (V : Type) (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V),
    match JuliaLean.base.boot.Models2Group1.Reflection.extractWrapper value with
    | none => WrapperCandidates value = []
    | some wrapper => ∃ remaining, WrapperCandidates value = wrapper :: remaining

/-- Observable classification and retained parameter of a Typeof result.
Existing handles must be actual runtime types (or the TypeofBottom singleton);
wrapper outputs retain the exact original object and are distinguished by the
presence of a scoped free-variable witness. No model function is called here. -/
def TypeofObservation {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V) :
    JuliaLean.base.boot.Models2Group1.Reflection.Result V → Prop
  | .existing candidate =>
      (¬ TypeObject value ∧ HeaderIs types value candidate) ∨
      (value = .bottom ∧ candidate = types.typeofBottom)
  | .equality parameter =>
      TypeObject value ∧ HasFreeWitness types [] value ∧ parameter = value
  | .egality parameter =>
      TypeObject value ∧ ¬ HasFreeWitness types [] value ∧
      value ≠ .bottom ∧ parameter = value

/-- Typeof distinguishes all runtime type-object kinds from ordinary values,
chooses equality precisely when an actual scoped free-variable witness exists,
and otherwise pins the original closed type by egality. Bottom preserves its
existing TypeofBottom handle. Every actual native-bounded metadata graph is
quantified, including shared identities and all arbitrary opaque payloads.
Sources: base/boot.jl:297-307; src/jltypes.c:126-191,2192-2205,3268-3311;
doc/src/devdocs/types.md (runtime type metadata and type parameters).
-/
def TypeofExactClassification : Prop :=
  ∀ (V : Type) (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes) (value : JuliaLean.base.boot.Models2Group1.Reflection.JuliaValue V),
    TypeofObservation types value.object (JuliaLean.base.boot.Models2Group1.Reflection.typeOf types value)

/-- Independent source-guard classification. The method skips the generic
Typeof call exactly for actual type objects with a scoped free-variable witness. -/
def CapturedDirect {V : Type} (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes)
    (value : JuliaLean.base.boot.Models2Group1.Reflection.Value V) : Prop :=
  TypeObject value ∧ HasFreeWitness types [] value

/-- One ghost dispatch event; this list is specification state, not a Julia
array. The target is retained so a wrong generic function is detectable. -/
abbrev CapturedEvent (L : Type) :=
  JuliaLean.base.expr.Value L × List (JuliaLean.base.expr.Value L)

/-- Instrument unrestricted selected dispatch while preserving every possible
return, thrown value, world effect and divergence. Only the ghost trace changes. -/
def observeCapturedCall {W L : Type}
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L))
    (fn : JuliaLean.base.expr.Value L) (args : List (JuliaLean.base.expr.Value L)) :
    JuliaLean.base.boot.CoreM (W × List (CapturedEvent L)) L (JuliaLean.base.expr.Value L) :=
  fun (world, trace) =>
    match dispatch fn args world with
    | none => none
    | some (.ok (value, after)) => some (.ok (value, (after, trace ++ [(fn, args)])))
    | some (.error (error, after)) => some (.error (error, (after, trace ++ [(fn, args)])))

/-- Compare the complete arbitrary custom outcome with one observed call,
including its target, original argument, result/error, state and divergence.
This does not invoke any model or assume any correctness law on dispatch. -/
def CapturedForwarding {W L : Type} (trace : List (CapturedEvent L))
    (event : CapturedEvent L)
    (plain : Option (Except (JuliaLean.base.expr.Value L × W)
      (JuliaLean.base.expr.Value L × W)))
    (recorded : Option (Except
      (JuliaLean.base.expr.Value L × (W × List (CapturedEvent L)))
      (JuliaLean.base.expr.Value L × (W × List (CapturedEvent L))))) : Prop :=
  match plain, recorded with
  | none, none => True
  | some (.ok (value, after)), some (.ok (recordedValue, (recordedAfter, events))) =>
      recordedValue = value ∧ recordedAfter = after ∧ events = trace ++ [event]
  | some (.error (error, after)), some (.error (recordedError, (recordedAfter, events))) =>
      recordedError = error ∧ recordedAfter = after ∧ events = trace ++ [event]
  | _, _ => False

/-- Every source branch is observed over the full argument and dispatch domain.
Free type objects return their original runtime header without calling Typeof;
otherwise the selected source method satisfies independent type classification,
or exactly one selected custom call retains all arbitrary outcomes and effects.
No generic return is restricted to a type object, Bool, or a source Result.
Source: base/boot.jl:387, its concrete Typeof/free-variable closure, and the
source's generic Typeof dispatch on the argument whose type is unspecified.
-/
def CapturedVariableClassification : Prop :=
  ∀ (W V L : Type)
    (ops : JuliaLean.base.boot.CoreOps (W × List (CapturedEvent L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L))
    (selected : W → JuliaLean.base.boot.Models2Group1.Reflection.JuliaValue V → Bool)
    (representation : JuliaLean.base.boot.Models2Group1.Reflection.CapturedRepresentation V L)
    (types : JuliaLean.base.boot.Models2Group1.Reflection.RuntimeTypes)
    (value : JuliaLean.base.boot.Models2Group1.Reflection.JuliaValue V)
    (world : W) (trace : List (CapturedEvent L)),
    let instrumented := { ops with call := observeCapturedCall dispatch }
    let run := JuliaLean.base.boot.Models2Group1.Reflection.capturedVariableType
      types instrumented (fun recorded input => selected recorded.1 input)
      representation value (world, trace)
    (CapturedDirect types value.object →
      ∃ header, HeaderIs types value.object header ∧
        run = some (.ok (representation.result (.existing header), (world, trace)))) ∧
    (¬ CapturedDirect types value.object →
      (selected world value = true →
        CapturedForwarding trace
          (JuliaLean.base.boot.coreV ops "Typeof", [representation.input value])
          (dispatch (JuliaLean.base.boot.coreV ops "Typeof") [representation.input value] world)
          run) ∧
      (selected world value = false →
        ∃ result, TypeofObservation types value.object result ∧
          run = some (.ok (representation.result result, (world, trace)))))

/-- The ignored argument cannot affect kwftype: its singleton range is exactly
the DataType handle stored on the existing Core.kwcall function object. This
fixes the returned handle and detects an arbitrary wrong constant. The source
reads the existing object's header and calls no dispatch-selected operation.
Source: base/boot.jl:393; src/builtins.c:612-616.
-/
def KeywordFunctionTypeInvariant : Prop :=
  ∀ (V A : Type) (kwcall : JuliaLean.base.boot.Models2Group1.Reflection.KeywordGlobal V) (input : A) (candidate : Nat),
    JuliaLean.base.boot.Models2Group1.Reflection.keywordFunctionType kwcall input = candidate ↔ candidate = kwcall.header.runtimeType

/-- Entries to append to the parent group's single registry list. -/
def entriesReflection : List Entry := [
  { id := "boot-runtime-type-metadata"
    juliaFile := "base/boot.jl"
    juliaFns := ["typeof", "isa(_,Type)", "Typeof", "_typeof_captured_variable", "kwftype"]
    statement := "Runtime typeof and type-kind classification read the exact stored DataType handle and compact kind-tag interval, preserving object identity."
    source := "src/builtins.c:612-616; src/julia.h:197-207,1109-1121,1175-1193,1907-1917; src/subtype.c:4253-4314,780-783,3210-3219,3796-3805; base/boot.jl:300-307,387,393"
    status := .todo
    prop := ``RuntimeMetadataInvariant
    thm := none
    notes := "New concrete metadata closure. Stored headers and global compact-tag table are data, not operation callbacks." },
  { id := "boot-free-variable-scope"
    juliaFile := "base/boot.jl"
    juliaFns := ["has_free_typevars", "Typeof", "_typeof_captured_variable"]
    statement := "The concrete free-variable traversal is true exactly when a scoped metadata path reaches an unbound variable, TypeApp, or an applicable set DataType cache; parameter scanning is existential over all entries."
    source := "src/jltypes.c:126-191; base/boot.jl:303,387; binder and DataType metadata invariants"
    status := .todo
    prop := ``FreeVariableScopeInvariant
    thm := none
    notes := "Independent inductive graph reachability specification; no assumption that a runtime callback computes free variables. Includes UnionAll bounds, identity scope, both cache states, Intersect, TypeEq/TypeEgal and optional Vararg fields." },
  { id := "boot-type-wrapper-subobject"
    juliaFile := "base/boot.jl"
    juliaFns := ["extract_wrapper", "Typeof"]
    statement := "Wrapper extraction selects the first original stored wrapper among the permitted left-to-right metadata paths, or NULL precisely when no candidate exists."
    source := "src/jltypes.c:2192-2205,3268-3292; base/boot.jl:303"
    status := .todo
    prop := ``WrapperSubobjectInvariant
    thm := none
    notes := "Independent complete candidate-sequence observation, preserving stored identity and branch priority. Covers the concrete helper reached before the free-Type canonicalization guard short-circuits." },
  { id := "boot-typeof-classification"
    juliaFile := "base/boot.jl"
    juliaFns := ["(f::typeof(Typeof))(x)"]
    statement := "Typeof returns actual runtime headers for non-types, equality wrappers with the exact original free type, egality wrappers with the exact closed type, and the existing TypeofBottom object for bottom."
    source := "base/boot.jl:297-307; src/jltypes.c:126-191,2192-2205,3268-3311; doc/src/devdocs/types.md"
    status := .todo
    prop := ``TypeofExactClassification
    thm := none
    notes := "Complete source method and reachable concrete dependencies. Native SimpleVector bounds are representation evidence. General TypeEqOf is excluded: closed Type parameters can need jl_types_equal canonicalization." },
  { id := "boot-captured-variable-type"
    juliaFile := "base/boot.jl"
    juliaFns := ["_typeof_captured_variable(@nospecialize t)"]
    statement := "Captured-variable typing returns an original runtime header for free type values without dispatch; otherwise it executes the complete source Typeof method or exactly one selected custom call, preserving arbitrary results, exceptions, effects and divergence."
    source := "base/boot.jl:387; complete Typeof/free-variable runtime closure"
    status := .todo
    prop := ``CapturedVariableClassification
    thm := none
    notes := "Full actual-value domain with stored tag data and real scoped free-variable traversal. The generic Typeof call selects its concrete source body or unrestricted CoreOps.call; pure encodings preserve values. Custom results need not be type objects. No callee-correctness law is imposed." },
  { id := "boot-keyword-function-type"
    juliaFile := "base/boot.jl"
    juliaFns := ["kwftype(@nospecialize(t))"]
    statement := "The kwftype range is the singleton containing the exact runtime DataType handle of the existing Core.kwcall global object, for every input."
    source := "base/boot.jl:393; src/builtins.c:612-616; actual object-header invariant"
    status := .todo
    prop := ``KeywordFunctionTypeInvariant
    thm := none
    notes := "The existing function object's stored header is represented explicitly; typeof has no arbitrary callback." }
]

end JuliaLean.Proofs.base.boot.Models2Group1.Reflection


namespace JuliaLean.Proofs.base.boot.Models2Group1.AliasDispatch

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

abbrev MetaValue (V : Type) := JuliaLean.base.boot.Models2Group1.Reflection.Value V
abbrev ActualValue (V : Type) := JuliaLean.base.boot.Models2Group1.Reflection.JuliaValue V
abbrev RuntimeValue (L : Type) := JuliaLean.base.expr.Value L

/-- Ghost observation of an actual selected generic call, including its exact
arguments and both worlds. The trace is not a Julia array. -/
inductive CallEvent (W L : Type) where
  | returned (fn : RuntimeValue L) (args : List (RuntimeValue L))
      (value : RuntimeValue L) (before after : W)
  | raised (fn : RuntimeValue L) (args : List (RuntimeValue L))
      (error : RuntimeValue L) (before after : W)

/-- Preserve each arbitrary dispatch outcome while adding one inaccessible
ghost event. A custom callee cannot modify or manufacture the event list. -/
def observeCall {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (fn : RuntimeValue L) (args : List (RuntimeValue L)) :
    CoreM (W × List (CallEvent W L)) L (RuntimeValue L) :=
  fun (world, events) =>
    match dispatch fn args world with
    | none => none
    | some (.ok (value, after)) =>
        some (.ok (value, (after, events ++ [.returned fn args value world after])))
    | some (.error (error, after)) =>
        some (.error (error, (after, events ++ [.raised fn args error world after])))

/-- The actual immutable UnionAll body field, independent of executable
recursion and dispatch. All other values have no body edge for this method. -/
def UnionAllBody {V : Type} (value next : MetaValue V) : Prop :=
  match value with
  | .unionAll _ _ _ _ body _ => next = body
  | _ => False

/-- Finite paths consisting only of source-selected recursive edges. The
method returns immediately when it encounters a selected custom call, so all
source edges preceding it retain the same world. -/
inductive DefaultBodyPath {W V : Type}
    (selected : W → MetaValue V → Bool) (world : W) : MetaValue V → MetaValue V → Prop where
  | refl {value} : DefaultBodyPath selected world value value
  | step {value next final} : UnionAllBody value next → selected world next = false →
      DefaultBodyPath selected world next final → DefaultBodyPath selected world value final

/-- Terminal classification by stored kind, not by a recursive model call.
The Any fallback body returns true for TypeApp and false for every non-UnionAll
other kind. A UnionAll is a source edge, never a terminal classification. -/
def ContainsTerminal {V L : Type} (trueValue falseValue : RuntimeValue L)
    (value : MetaValue V) (result : RuntimeValue L) : Prop :=
  match value with
  | .typeApp .. => result = trueValue
  | .unionAll .. => False
  | _ => result = falseValue

/-- The unique possible selected custom call is reached through actual
UnionAll body fields after zero or more source-selected edges. -/
def CustomBodyReached {W V : Type} (selected : W → MetaValue V → Bool)
    (world : W) (start body : MetaValue V) : Prop :=
  ∃ parent, DefaultBodyPath selected world start parent ∧
    UnionAllBody parent body ∧ selected world body = true

/-- Complete finite observations for _contains_typeapp. A no-call run ends at
an actual terminal kind without state mutation; a custom run preserves its one
actual recorded call and arbitrary result or exception, with no Bool assertion.
-/
def ContainsTrace {W V L : Type} (selected : W → MetaValue V → Bool)
    (encode : MetaValue V → RuntimeValue L) (token trueValue falseValue : RuntimeValue L)
    (world : W) (start : MetaValue V)
    (outcome : Except (RuntimeValue L × W) (RuntimeValue L × W))
    (events : List (CallEvent W L)) : Prop :=
  match outcome with
  | .ok (result, after) =>
      (after = world ∧ events = [] ∧
        ∃ terminal, DefaultBodyPath selected world start terminal ∧
          ContainsTerminal trueValue falseValue terminal result) ∨
      (∃ body, CustomBodyReached selected world start body ∧
        events = [.returned token [encode body] result world after])
  | .error (error, after) =>
      ∃ body, CustomBodyReached selected world start body ∧
        events = [.raised token [encode body] error world after]

/-- Every full-domain source execution follows actual immutable body fields,
returns the correct terminal Bool, or forwards one selected custom outcome.
The source recursion is finite on the actual const UnionAll graph, so divergence
must come from a reached custom call. Effects, errors and arbitrary custom
results are preserved without any callback law or assumption of Bool results.
Source: base/boot.jl:426-434; src/jltypes.c:3728-3741.
-/
def ContainsTypeAppObservations : Prop :=
  ∀ (W V L : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (selected : W → MetaValue V → Bool) (encode : MetaValue V → RuntimeValue L)
    (input : ActualValue V) (world : W),
    let instrumented := { ops with call := observeCall dispatch }
    match JuliaLean.base.boot.Models2Group1.AliasDispatch.containsTypeApp
        instrumented (fun state value => selected state.1 value) encode input.object (world, []) with
    | none =>
        ∃ body, CustomBodyReached selected world input.object body ∧
          dispatch (coreV ops "_contains_typeapp") [encode body] world = none
    | some (.ok (result, (after, events))) =>
        ContainsTrace selected encode (coreV ops "_contains_typeapp") (boolV ops true) (boolV ops false) world input.object
          (.ok (result, after)) events
    | some (.error (error, (after, events))) =>
        ContainsTrace selected encode (coreV ops "_contains_typeapp") (boolV ops true) (boolV ops false) world input.object
          (.error (error, after)) events

/-- The two-call contract is expressed by the actual event sequence, without
executing another TypeError implementation. A Symbol exception permits only
one event; success reaches TypeError with its exact result, empty String and
original expected/got, preserving every final value/error and world effect. -/
def TypeErrorTrace {W L : Type}
    (symbolToken typeErrorToken emptyString where_ expected got : RuntimeValue L)
    (before : W) (outcome : Except (RuntimeValue L × W) (RuntimeValue L × W))
    (events : List (CallEvent W L)) : Prop :=
  match outcome with
  | .ok (result, after) =>
      ∃ func intermediate,
        events = [.returned symbolToken [where_] func before intermediate,
          .returned typeErrorToken [func, emptyString, expected, got] result intermediate after]
  | .error (error, after) =>
      events = [.raised symbolToken [where_] error before after] ∨
      ∃ func intermediate,
        events = [.returned symbolToken [where_] func before intermediate,
          .raised typeErrorToken [func, emptyString, expected, got] error intermediate after]

/-- Divergence is attributable to an actual selected call: either Symbol
itself, or TypeError reached after an actual successful Symbol result. The
equalities observe arbitrary callee outcomes and impose no correctness law. -/
def TypeErrorDivergence {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (symbolToken typeErrorToken emptyString where_ expected got : RuntimeValue L)
    (world : W) : Prop :=
  dispatch symbolToken [where_] world = none ∨
  ∃ func intermediate,
    dispatch symbolToken [where_] world = some (.ok (func, intermediate)) ∧
    dispatch typeErrorToken [func, emptyString, expected, got] intermediate = none

/-- The selected three-argument TypeError body preserves the ordered two-call
protocol over every actual argument and unrestricted dispatch implementation.
Custom Symbol and TypeError methods may return any Julia value, mutate, throw,
or diverge; no result is narrowed to Symbol or to a TypeError instance.
Source: base/boot.jl:537-538; open generic-call ordering and identity invariant.
-/
def TypeErrorFromWhereObservations : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (where_ expected got : RuntimeValue L) (world : W),
    let instrumented := { ops with call := observeCall dispatch }
    match JuliaLean.base.boot.Models2Group1.AliasDispatch.typeErrorFromWhere
        instrumented where_ expected got (world, []) with
    | none => TypeErrorDivergence dispatch (coreV ops "Symbol") (coreV ops "TypeError")
        (strV ops "") where_ expected got world
    | some (.ok (result, (after, events))) =>
        TypeErrorTrace (coreV ops "Symbol") (coreV ops "TypeError") (strV ops "")
          where_ expected got world (.ok (result, after)) events
    | some (.error (error, (after, events))) =>
        TypeErrorTrace (coreV ops "Symbol") (coreV ops "TypeError") (strV ops "")
          where_ expected got world (.error (error, after)) events

/-- Immutable EnterNode fields observed independently of the constructors.
None is undefined scope, not a default or a distinguished payload value. -/
def EnterFields {L : Type} : RuntimeValue L → Option (I64 × Option (RuntimeValue L))
  | .enterNode destination scope => some (destination, scope)
  | _ => none

/-- Finite retargeting observations. Source constructor selection preserves
native destination, exact scope value/undefinedness and state; custom selection
preserves the actual constructor call's arbitrary result/error and effects. -/
def EnterTrace {W L : Type} (selected : W → I64 → RuntimeValue L → Bool)
    (token destinationValue : RuntimeValue L) (world : W)
    (scope : Option (RuntimeValue L)) (destination : I64)
    (outcome : Except (RuntimeValue L × W) (RuntimeValue L × W))
    (events : List (CallEvent W L)) : Prop :=
  match scope, outcome with
  | none, .ok (result, after) =>
      EnterFields result = some (destination, none) ∧ after = world ∧ events = []
  | none, .error _ => False
  | some scope, .ok (result, after) =>
      (selected world destination scope = false ∧
        EnterFields result = some (destination, some scope) ∧ after = world ∧ events = []) ∨
      (selected world destination scope = true ∧
        events = [.returned token [destinationValue, scope] result world after])
  | some scope, .error (error, after) =>
      selected world destination scope = true ∧
        events = [.raised token [destinationValue, scope] error world after]

/-- Complete EnterNode retargeting over every native destination and arbitrary
optional scope. The no-scope path uses the fixed source constructor; a defined
scope retains full generic two-argument dispatch. Custom constructor results
need not be EnterNodes, and every error/state effect/divergence is retained.
Source: base/boot.jl:1292-1293, installed concrete constructors at 708-709.
-/
def EnterNodeRetargetObservations : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (selected : W → I64 → RuntimeValue L → Bool)
    (oldDestination newDestination : I64) (scope : Option (RuntimeValue L)) (world : W),
    let instrumented := { ops with call := observeCall dispatch }
    match JuliaLean.base.boot.Models2Group1.AliasDispatch.enterNodeRetarget instrumented
        (fun state destination value => selected state.1 destination value)
        oldDestination scope newDestination (world, []) with
    | none =>
        ∃ value, scope = some value ∧ selected world newDestination value = true ∧
          dispatch (coreV ops "EnterNode") [intV ops newDestination, value] world = none
    | some (.ok (result, (after, events))) =>
        EnterTrace selected (coreV ops "EnterNode") (intV ops newDestination)
          world scope newDestination (.ok (result, after)) events
    | some (.error (error, (after, events))) =>
        EnterTrace selected (coreV ops "EnterNode") (intV ops newDestination)
          world scope newDestination (.error (error, after)) events

/-- Group registry entries for the three repaired full-domain source bodies. -/
def entriesAliasDispatch : List Entry := [
  { id := "boot-contains-typeapp-dispatch"
    juliaFile := "base/boot.jl"
    juliaFns := ["_contains_typeapp(@nospecialize(x))"]
    statement := "The source _contains_typeapp method follows actual UnionAll body fields through concrete default recursion, returns the correct terminal Bool, or forwards one reached custom call's arbitrary value, error, effects or divergence."
    source := "base/boot.jl:426-434; src/jltypes.c:3728-3741; immutable body-path and actual-call invariant"
    status := .todo
    prop := ``ContainsTypeAppObservations
    thm := none
    notes := "Reuses actual Reflection type metadata; default recursion is explicit. Generic recursive call selection may return any value, without a Bool assertion or a callback-correctness law." },
  { id := "boot-typeerror-where-dispatch"
    juliaFile := "base/boot.jl"
    juliaFns := ["TypeError(where, @nospecialize(expected::Type), @nospecialize(got))"]
    statement := "The three-argument TypeError body calls Symbol first, then generic four-argument TypeError with the exact result, empty context and original expected/got, preserving every arbitrary result, error, effect and divergence."
    source := "base/boot.jl:537-538; independent two-call protocol and retained-argument invariant"
    status := .todo
    prop := ``TypeErrorFromWhereObservations
    thm := none
    notes := "Both selected callees dispatch on unfixed arguments through existing CoreOps.call. Constructor results are unrestricted Julia values; the four-argument source constructor remains separately modeled." },
  { id := "boot-enternode-retarget-dispatch"
    juliaFile := "base/boot.jl"
    juliaFns := ["EnterNode(old::EnterNode, new_dest::Int)"]
    statement := "EnterNode retargeting uses the concrete no-scope constructor or the selected source/custom two-argument constructor, preserving exact scope and destination on source paths and every custom outcome/effect otherwise."
    source := "base/boot.jl:1292-1293,708-709; independent field-definedness and actual-call invariant"
    status := .todo
    prop := ``EnterNodeRetargetObservations
    thm := none
    notes := "Reuses installed boot.EnterNode1 and EnterNode2. Generic dispatch on the unfixed defined scope admits arbitrary constructor results, errors, mutation and divergence, without a callee law." }
]

end JuliaLean.Proofs.base.boot.Models2Group1.AliasDispatch


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-- Independent accepted Symbol-name predicate; no implementation validation
helper is used. Source: `src/genericmemory.c:81-82`. -/
def MemoryKindAccepted {L : Type} : MemoryKindParameter L → Prop
  | .symbol name =>
      name.bytes = "not_atomic".toByteArray.toList ∨
        name.bytes = "atomic".toByteArray.toList
  | .other _ => False

/-- Core.CPU's actual module identity and zero byte value, independently of
the model's validation helper. Source: `src/genericmemory.c:83-85`. -/
def MemoryCPUAddress {L : Type} : MemoryAddressParameter L → Prop
  | .address address =>
      match address.backend with
      | .core => address.tag.val = 0
      | .other _ => False
  | .other _ => False

/-- Actual usable type metadata, not a law about allocation or a callback.
Source: `src/genericmemory.c:81-90`. -/
def MemoryUsableType {L : Type} (type : MemoryNativeType L) : Prop :=
  MemoryKindAccepted type.kind ∧ MemoryCPUAddress type.address ∧
    type.hasConcreteSubtype = true ∧ ∃ layout, type.layout = some layout

/-- Mathematical bytes needed for n elements, including one selector byte
per union element. The model uses checked native products/sums instead.
Source: `src/genericmemory.c:59-66,93-101`. -/
def MemoryRequestedBytes (layout : MemoryNativeLayout) (n : Int) : Int :=
  n * (if layout.boxed then 8 else layout.size.val) +
    (if layout.union then n else 0)

/-- Independent exact count/byte representability boundary. Native signed
negative counts fail, and both limits are strict MAXINTVAL-1. No input range
premise is imposed by the public properties. Source: `src/genericmemory.c:65`. -/
def MemoryCountFits (layout : MemoryNativeLayout) (n : Int) : Prop :=
  0 ≤ n ∧ n < (2 : Int) ^ 63 - 2 ∧
    0 ≤ MemoryRequestedBytes layout n ∧
    MemoryRequestedBytes layout n < (2 : Int) ^ 63 - 2

/-- Observe a plain existing exception class/message, not a constructor call.
Source: allocation's ErrorException and ArgumentError branches. -/
def MemoryPlainFault {L : Type} (exception : JuliaLean.BootCov.Exc) :
    JuliaLean.base.expr.Value (MemoryNativeException L) → Prop
  | .leaf (.runtime error) =>
      error.exception = exception ∧ error.context = "" ∧ error.expected = none ∧
        error.got = none ∧ error.boundsObject = none ∧ error.boundsIndex = none
  | _ => False

/-- Actual invalid-element TypeError payload, retaining the original element
parameter even when it is not itself a Type. Source: `src/genericmemory.c:86-87`. -/
def MemoryElementFault {L : Type} (element : JuliaLean.base.expr.Value L) :
    JuliaLean.base.expr.Value (MemoryNativeException L) → Prop
  | .leaf (.runtime error) =>
      error.exception = .typeError "GenericMemory" ∧ error.context = "element type" ∧
        error.expected = some "Type" ∧ error.got = some element ∧
        error.boundsObject = none ∧ error.boundsIndex = none
  | _ => False

/-- Allocation error precedence: kind, address space, element/layout, then
dimension/byte size. Every prior-validity condition describes actual type
metadata; there is no success hypothesis or assumed helper-correctness law.
Source: `src/genericmemory.c:55-102`. -/
def MemoryAllocationFault {L : Type} (type : MemoryNativeType L) (n : Int)
    (error : JuliaLean.base.expr.Value (MemoryNativeException L)) : Prop :=
  (¬MemoryKindAccepted type.kind ∧
    MemoryPlainFault (.error "GenericMemory kind must be :not_atomic or :atomic") error) ∨
  (MemoryKindAccepted type.kind ∧ ¬MemoryCPUAddress type.address ∧
    MemoryPlainFault (.error "GenericMemory addrspace must be Core.CPU") error) ∨
  (MemoryKindAccepted type.kind ∧ MemoryCPUAddress type.address ∧
    (type.hasConcreteSubtype = false ∨ type.layout = none) ∧
    MemoryElementFault type.element error) ∨
  (MemoryUsableType type ∧ ∃ layout, type.layout = some layout ∧
    ¬MemoryCountFits layout n ∧
    MemoryPlainFault (.argument
      "invalid GenericMemory size: the number of elements is either negative or too large for system address width") error)

/-- Independent successful-allocation observations: exact requested native
length and byte count; one fresh identity for nonempty allocation; untouched
old cells and external state; actual zero initialization or unspecified raw
bytes. Zero length returns the pre-existing per-type singleton unchanged.
Source: `src/genericmemory.c:55-73,89-102`. -/
def MemoryAllocationSuccess {W L : Type} (type : MemoryNativeType L)
    (layout : MemoryNativeLayout) (n : Int) (before : MemoryNativeWorld W)
    (result : MemoryNativeObject L) (after : MemoryNativeWorld W) : Prop :=
  result.type = type ∧ result.layout = layout ∧
  if n = 0 then
    type.cachedInstance = some result.identity ∧ after = before
  else
    result.identity = before.heap.nextIdentity ∧
      after.heap.nextIdentity = before.heap.nextIdentity + 1 ∧
      after.external = before.external ∧
      (after.heap.contents result.identity).length.val = n ∧
      (after.heap.contents result.identity).byteCount.val = MemoryRequestedBytes layout n ∧
      (∀ id, id ≠ result.identity → after.heap.contents id = before.heap.contents id) ∧
      (∀ byte : Nat, (byte : Int) < MemoryRequestedBytes layout n →
        (after.heap.contents result.identity).bytes byte =
          if type.zeroInit then some 0 else none)

/-- Allocation must terminate, classify every invalid input, and preserve
state on failure. Success is specified by independent mathematical range,
identity, type, length, byte, and old-state observations.
Source: `base/boot.jl:762-765`; concrete runtime closure at genericmemory.c55-102. -/
def MemoryAllocationObservation {W L : Type} (type : MemoryNativeType L)
    (n : Int) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryNativeObject L × MemoryNativeWorld W))) : Prop :=
  match outcome with
  | none => False
  | some (.error (error, after)) => after = before ∧ MemoryAllocationFault type n error
  | some (.ok (result, after)) =>
      MemoryUsableType type ∧ ∃ layout, type.layout = some layout ∧
        MemoryCountFits layout n ∧ MemoryAllocationSuccess type layout n before result after

/-- All native Int counts and all actual GenericMemory type descriptors,
including bad kind/address space/element/layout, for the direct source method.
Cached zero identity and nonempty freshness are distinguished; byte-count
overflow and signed-negative errors are included. Source: base/boot.jl:762. -/
def MemoryConstructorAllocation : Prop :=
  ∀ (W L : Type) (type : MemoryNativeType L) (n : JInt .i64)
    (before : MemoryNativeWorld W),
    MemoryAllocationObservation type n.val before (memoryUndefCtor type n before)

/-- First references retain exactly their original memory and use its first
pointer-or-offset position, even when length is zero. They never allocate or
mutate a memory object, throw, or diverge. Source: `base/boot.jl:768,771`;
`src/builtins.c:2243-2255`. -/
def MemoryFirstReferenceFields : Prop :=
  ∀ (W L : Type) (memory : MemoryNativeObject L) (world : MemoryNativeWorld W),
    ∃ result, memoryRef memory world = some (.ok (result, world)) ∧
      result.memory = memory ∧ result.data.val = 0

/-- The memory object named by a bounds-check argument. Specification observer.
Source: `src/builtins.c:2262-2297`. -/
def MemoryBoundsReferent {L : Type} : MemoryBoundsValue L → MemoryNativeObject L
  | .memory memory => memory
  | .reference reference => reference.memory

/-- Mathematical signed interpretation of a UInt64 pointer difference.
This does not invoke the implementation's wrapping helper. -/
def MemorySignedDifference (bits : Int) : Int :=
  if bits < (2 : Int) ^ 63 then bits else bits - (2 : Int) ^ 64

/-- Read the represented position before moving a reference. Boxed pointer
differences undergo unsigned size_t division; inline differences use signed
ptrdiff_t division by UInt32 layout size. This observer states representation
meaning, independently of the builtin's native arithmetic/checking program.
Source: `src/builtins.c:2280-2293`. -/
def MemorySourcePosition {L : Type} : MemoryBoundsValue L → Int
  | .memory _ => 0
  | .reference reference =>
    let layout := reference.memory.layout
    if layout.boxed then reference.data.val / 8
    else if layout.union || layout.size.val = 0 then reference.data.val
    else (MemorySignedDifference reference.data.val).tdiv layout.size.val

/-- Initial native pointer-or-offset bits. Memory input denotes its base/zero
position; reference input denotes its exact original bits. -/
def MemorySourceBits {L : Type} : MemoryBoundsValue L → Int
  | .memory _ => 0
  | .reference reference => reference.data.val

/-- Representation distance per element in the selected builtin source case.
Different predicate order for memory/reference inputs follows the actual
runtime flags; valid runtime layouts never simultaneously box union data.
Source: `src/builtins.c:2269-2273,2280-2293`. -/
def MemorySourceStride {L : Type} : MemoryBoundsValue L → Int
  | .memory memory =>
    if memory.layout.union || memory.layout.size.val = 0 then 1
    else if memory.layout.boxed then 8 else memory.layout.size.val
  | .reference reference =>
    if reference.memory.layout.boxed then 8
    else if reference.memory.layout.union || reference.memory.layout.size.val = 0 then 1
    else reference.memory.layout.size.val

/-- The exact BoundsError object/index fields, using the converted native Int
argument rather than the original generic Integer value.
Source: `src/builtins.c:2267,2282,2287,2292`; rtutils.c190-194. -/
def MemoryBoundsFault {L : Type} (source : MemoryBoundsValue L) (index : JInt .i64) :
    JuliaLean.base.expr.Value (MemoryNativeException L) → Prop
  | .leaf (.runtime error) =>
      error.exception = .bounds ∧ error.context = "" ∧ error.expected = none ∧
        error.got = none ∧ error.boundsObject = some source ∧ error.boundsIndex = some index
  | _ => False

/-- Wrong Int(i) result is rejected by the builtin's native Int assertion,
retaining the actual offending result, before bounds checking.
Source: `src/builtins.c:2257`. -/
def MemoryIndexTypeFault {L : Type} (got : JuliaLean.base.expr.Value L) :
    JuliaLean.base.expr.Value (MemoryNativeException L) → Prop
  | .leaf (.runtime error) =>
      error.exception = .typeError "memoryrefnew" ∧ error.context = "" ∧
        error.expected = some "Int64" ∧ error.got = some got ∧
        error.boundsObject = none ∧ error.boundsIndex = none
  | _ => False

/-- Independent native reference observation. The mathematical displaced
position modulo 2^64 must lie below the current memory length, otherwise the
exact source BoundsError is required. Success retains the memory identity and
exact displaced pointer-or-offset bits; either outcome preserves the complete
post-conversion state. The boundscheck Bool does not weaken this invariant.
Source: `src/builtins.c:2256-2297`. -/
def MemoryIndexObservation {W L : Type} (source : MemoryBoundsValue L)
    (index : JInt .i64) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryNativeRef L × MemoryNativeWorld W))) : Prop :=
  let position := (MemorySourcePosition source + index.val - 1) % (2 : Int) ^ 64
  let length := (before.heap.contents (MemoryBoundsReferent source).identity).length.val
  match outcome with
  | none => False
  | some (.error (error, after)) =>
      after = before ∧ length ≤ position ∧ MemoryBoundsFault source index error
  | some (.ok (result, after)) =>
      after = before ∧ position < length ∧ result.memory = MemoryBoundsReferent source ∧
        result.data.val =
          (MemorySourceBits source + MemorySourceStride source * (index.val - 1)) % (2 : Int) ^ 64

/-- Full arbitrary-dispatch outcome specification. The single actual Int(i)
request uses the original generic Integer input. Its errors, prior effects,
and divergence propagate; a returned non-Int triggers the builtin TypeError;
a returned native Int is checked against the post-call memory state. No callee
law, termination premise, success premise, or bounds premise is supplied.
Source: `base/boot.jl:769-770`; builtins.c2257-2297. -/
def MemoryIndexedCallContract {W L : Type} (dispatch : MemoryNativeDispatch W L)
    (source : MemoryBoundsValue L) (input : JuliaLean.base.expr.Value L)
    (before : MemoryNativeWorld W) (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryNativeRef L × MemoryNativeWorld W))) : Prop :=
  match dispatch.toInt input before with
  | none => outcome = none
  | some (.error error) => outcome = some (.error error)
  | some (.ok (.other got, after)) =>
      ∃ error, outcome = some (.error (error, after)) ∧ MemoryIndexTypeFault got error
  | some (.ok (.native index, after)) => MemoryIndexObservation source index after outcome

/-- The selected indexed memory wrapper includes every Integer subtype and every
possible open Int(i) result, exception, effect, or divergence. Both Bool values
retain the runtime's actual unconditional bounds behavior.
Source: `base/boot.jl:769`; independent call/bounds/identity observations. -/
def MemoryIndexedWrapperBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryNativeDispatch W L)
    (memory : MemoryNativeObject L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) (before : MemoryNativeWorld W),
    MemoryIndexedCallContract dispatch (.memory memory) index before
      (memoryRefAt dispatch memory index boundscheck before)

/-- The selected indexed reference wrapper preserves the original referent and native
pointer-or-offset representation, including relative moves with nonpositive
Int indices and wrapping arithmetic. Custom conversion may change the current
memory length; bounds are tested against that actual resulting state.
Source: `base/boot.jl:770`; builtins.c2276-2297. -/
def MemoryShiftedWrapperBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryNativeDispatch W L)
    (reference : MemoryNativeRef L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) (before : MemoryNativeWorld W),
    MemoryIndexedCallContract dispatch (.reference reference) index before
      (memoryRefShift dispatch reference index boundscheck before)

/-- Observable open-call requests for the alias properties. The trace lives
outside the arbitrary supplied world and cannot be erased by a callback. -/
inductive MemoryAliasEvent (L : Type) where
  | conversion (input : JuliaLean.base.expr.Value L)
  | customReference (source : MemoryBoundsValue L) (input : JuliaLean.base.expr.Value L)

structure MemoryAliasTrace (W L : Type) where
  actual : W
  events : List (MemoryAliasEvent L)

/-- Forget only the independent instrumentation; retain the complete actual
heap and arbitrary supplied runtime state. -/
def memoryAliasRawWorld {W L : Type} (world : MemoryNativeWorld (MemoryAliasTrace W L)) :
    MemoryNativeWorld W := ⟨world.heap, world.external.actual⟩

/-- Record one actual request while running an entirely arbitrary callback.
Errors, state effects and divergence are preserved. This is a property-only
observer, not an operation supplied to the model or a callback law. -/
def memoryAliasRecord {W L A : Type} (event : MemoryAliasEvent L)
    (action : MemoryNativeM W L A) : MemoryNativeM (MemoryAliasTrace W L) L A :=
  fun before =>
    match action (memoryAliasRawWorld before) with
    | none => none
    | some (.error (error, after)) =>
        some (.error (error, ⟨after.heap,
          ⟨after.external, before.external.events ++ [event]⟩⟩))
    | some (.ok (value, after)) =>
        some (.ok (value, ⟨after.heap,
          ⟨after.external, before.external.events ++ [event]⟩⟩))

/-- Instrument every actual alias/custom-conversion request without adding
any correctness or termination assumption to the supplied methods. -/
def memoryAliasTracedDispatch {W L : Type} (dispatch : MemoryNativeAliasDispatch W L) :
    MemoryNativeAliasDispatch (MemoryAliasTrace W L) L where
  native := { toInt := fun input =>
    memoryAliasRecord (.conversion input) (dispatch.native.toInt input) }
  customSelected := fun world source input =>
    dispatch.customSelected (memoryAliasRawWorld world) source input
  custom := fun source input =>
    memoryAliasRecord (.customReference source input) (dispatch.custom source input)

/-- Start the independent request trace while preserving all actual input
state. -/
def memoryAliasStart {W L : Type} (world : MemoryNativeWorld W) :
    MemoryNativeWorld (MemoryAliasTrace W L) := ⟨world.heap, ⟨world.external, []⟩⟩

/-- Project the exact supplied result/error and actual state from a traced
outcome; divergence remains divergence. -/
def memoryAliasActualOutcome {W L A : Type} :
    Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryAliasTrace W L))
      (A × MemoryNativeWorld (MemoryAliasTrace W L))) →
    Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (A × MemoryNativeWorld W))
  | none => none
  | some (.error (error, world)) => some (.error (error, memoryAliasRawWorld world))
  | some (.ok (value, world)) => some (.ok (value, memoryAliasRawWorld world))

/-- Every terminating outcome has precisely the expected request trace.
Divergence has no final state; it is constrained separately by the actual
callback outcome in MemoryAliasObservation. -/
def MemoryAliasRequests {W L A : Type} (expected : List (MemoryAliasEvent L)) :
    Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryAliasTrace W L))
      (A × MemoryNativeWorld (MemoryAliasTrace W L))) → Prop
  | none => True
  | some (.error (_, world)) => world.external.events = expected
  | some (.ok (_, world)) => world.external.events = expected

/-- The default alias branch returns a native reference only after executing
the independently specified complete memoryref algorithm. There is no expected
call to that algorithm's model and no assumption that Int(i) succeeds. -/
def MemoryAliasDefaultObservation {W L : Type} (dispatch : MemoryNativeDispatch W L)
    (source : MemoryBoundsValue L) (index : JuliaLean.base.expr.Value L)
    (before : MemoryNativeWorld W) : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryAliasResult L × MemoryNativeWorld W)) → Prop
  | none => MemoryIndexedCallContract dispatch source index before none
  | some (.error error) =>
      MemoryIndexedCallContract dispatch source index before (some (.error error))
  | some (.ok (.reference result, after)) =>
      MemoryIndexedCallContract dispatch source index before (some (.ok (result, after)))
  | some (.ok (.other _, _)) => False

/-- Independent operand/request trace plus full outcome transparency. Custom
memoryref receives the original source object and Integer in source order,
with no extra Int conversion or return-type assertion; default dispatch obeys
the independent mathematical bounds/identity contract. All callbacks, states,
results, errors and divergence are quantified without laws.
Source: `base/boot.jl:772-773`; dispatch and field-identity invariants. -/
def MemoryAliasObservation {W L : Type} (dispatch : MemoryNativeAliasDispatch W L)
    (source : MemoryBoundsValue L) (index : JuliaLean.base.expr.Value L)
    (before : MemoryNativeWorld W) (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryAliasTrace W L))
      (MemoryAliasResult L × MemoryNativeWorld (MemoryAliasTrace W L)))) : Prop :=
  if dispatch.customSelected before source index then
    MemoryAliasRequests [.customReference source index] outcome ∧
      memoryAliasActualOutcome outcome = dispatch.custom source index before
  else
    MemoryAliasRequests [.conversion index] outcome ∧
      MemoryAliasDefaultObservation dispatch.native source index before
        (memoryAliasActualOutcome outcome)

/-- The indexed GenericMemoryRef constructors preserve actual default/custom
memoryref dispatch selected on the unspecified Integer subtype. A custom
result may have any Julia type; its effects/errors/divergence pass through.
The request trace distinguishes custom memoryref from default Int conversion.
Source: `base/boot.jl:772-773`. -/
def MemoryAliasDispatchBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryNativeAliasDispatch W L)
    (memory : MemoryNativeObject L) (reference : MemoryNativeRef L)
    (index : JuliaLean.base.expr.Value L) (boundscheck : Bool) (before : MemoryNativeWorld W),
    MemoryAliasObservation dispatch (.memory memory) index before
      (genericMemoryRefAtCtor (memoryAliasTracedDispatch dispatch) memory index boundscheck
        (memoryAliasStart before)) ∧
    MemoryAliasObservation dispatch (.reference reference) index before
      (genericMemoryRefShiftCtor (memoryAliasTracedDispatch dispatch) reference index boundscheck
        (memoryAliasStart before))

/-- A reference-returning allocation is observed through its actual stored
memory and first-position data. This projects the output, rather than calling
the allocation or reference models as the expected result. -/
def MemoryRefAllocationObservation {W L : Type} (type : MemoryNativeType L)
    (n : Int) (before : MemoryNativeWorld W) (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryNativeRef L × MemoryNativeWorld W))) : Prop :=
  match outcome with
  | none => False
  | some (.error error) => MemoryAllocationObservation type n before (some (.error error))
  | some (.ok (reference, after)) => reference.data.val = 0 ∧
      MemoryAllocationObservation type n before (some (.ok (reference.memory, after)))

/-- Actual open-call requests, recorded independently of the source body.
Source: base/boot.jl:763,765,771,779. -/
inductive MemoryCreationEvent (L : Type) where
  | constructor (type : MemoryNativeType L) (count : JInt .i64)
  | first (memory : MemoryNativeObject L)
  | afterConstructor (value : JuliaLean.base.expr.Value L)

structure MemoryCreationTrace (W L : Type) where
  actual : W
  events : List (MemoryCreationEvent L)

def memoryCreationRawWorld {W L : Type}
    (world : MemoryNativeWorld (MemoryCreationTrace W L)) : MemoryNativeWorld W :=
  ⟨world.heap, world.external.actual⟩

/-- Instrument one arbitrary operation at its actual call boundary. The
operation can change the real heap/world, return any value, throw or diverge. -/
def memoryCreationRecord {W L A : Type} (event : MemoryCreationEvent L)
    (action : MemoryNativeM W L A) : MemoryNativeM (MemoryCreationTrace W L) L A :=
  fun world =>
    let events := world.external.events ++ [event]
    match action (memoryCreationRawWorld world) with
    | none => none
    | some (.error (error, after)) =>
        some (.error (error, ⟨after.heap, ⟨after.external, events⟩⟩))
    | some (.ok (value, after)) =>
        some (.ok (value, ⟨after.heap, ⟨after.external, events⟩⟩))

/-- Trace only the genuine selected operations. Selectors observe the complete
current real state, including mutations by earlier calls. -/
def memoryCreationTracedDispatch {W L : Type} (dispatch : MemoryCreationDispatch W L) :
    MemoryCreationDispatch (MemoryCreationTrace W L) L where
  constructorSelected world type n := dispatch.constructorSelected (memoryCreationRawWorld world) type n
  constructor type n := memoryCreationRecord (.constructor type n) (dispatch.constructor type n)
  firstSelected world memory := dispatch.firstSelected (memoryCreationRawWorld world) memory
  first memory := memoryCreationRecord (.first memory) (dispatch.first memory)
  afterCustomConstructor value :=
    memoryCreationRecord (.afterConstructor value) (dispatch.afterCustomConstructor value)

def memoryCreationStart {W L : Type} (world : MemoryNativeWorld W) :
    MemoryNativeWorld (MemoryCreationTrace W L) := ⟨world.heap, ⟨world.external, []⟩⟩

def memoryCreationProject {W L A : Type} : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (A × MemoryNativeWorld (MemoryCreationTrace W L))) →
    Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (A × MemoryNativeWorld W))
  | none => none
  | some (.error (error, world)) => some (.error (error, memoryCreationRawWorld world))
  | some (.ok (value, world)) => some (.ok (value, memoryCreationRawWorld world))

/-- Divergence has no final observable state; terminal executions have exactly
the prescribed sequence of requests, with original operands and no extras. -/
def MemoryCreationEvents {W L A : Type} (events : List (MemoryCreationEvent L)) :
    Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (A × MemoryNativeWorld (MemoryCreationTrace W L))) → Prop
  | none => True
  | some (.error (_, world)) => world.external.events = events
  | some (.ok (_, world)) => world.external.events = events

/-- Observe the default allocation path through its tracked result. No
constructor/helper implementation is used on the specification side. -/
def MemoryDefaultConstructorObservation {W L : Type} (type : MemoryNativeType L)
    (n : Int) (before : MemoryNativeWorld W) : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld W)
      (MemoryConstructorResult L × MemoryNativeWorld W)) → Prop
  | none => False
  | some (.error error) => MemoryAllocationObservation type n before (some (.error error))
  | some (.ok (.memory memory, after)) =>
      MemoryAllocationObservation type n before (some (.ok (memory, after)))
  | some (.ok (.customResult _, _)) => False

/-- Complete one-call alias contract: the selected user method's value/error/
state/divergence is forwarded, while the default branch satisfies independent
allocation mathematics, freshness and validation priority. -/
def MemoryConstructorAliasObservation {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeType L) (n : JInt .i64) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (MemoryConstructorResult L × MemoryNativeWorld (MemoryCreationTrace W L)))) : Prop :=
  if dispatch.constructorSelected before type n then
    MemoryCreationEvents [.constructor type n] outcome ∧
      match dispatch.constructor type n before with
      | none => outcome = none
      | some (.error error) => memoryCreationProject outcome = some (.error error)
      | some (.ok (value, after)) =>
          memoryCreationProject outcome = some (.ok (.customResult value, after))
  else
    MemoryCreationEvents [] outcome ∧
      MemoryDefaultConstructorObservation type n.val before (memoryCreationProject outcome)

/-- Both constructor aliases quantify all actual type descriptors, native
counts and arbitrary selected methods. Tuple projection and the literal zero
are distinguished by exact traced arguments. Source: base/boot.jl:763,765. -/
def MemoryConstructorAliasBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryCreationDispatch W L) (type : MemoryNativeType L)
    (n : JInt .i64) (before : MemoryNativeWorld W),
    MemoryConstructorAliasObservation dispatch type n before
      (memoryTupleCtor (memoryCreationTracedDispatch dispatch) type n (memoryCreationStart before)) ∧
    MemoryConstructorAliasObservation dispatch type (JInt.wrap .i64 0) before
      (memoryEmptyCtor (memoryCreationTracedDispatch dispatch) type (memoryCreationStart before))

/-- Independent first-reference outcome: default stores the original memory
and zero pointer difference without mutation; selected custom calls forward
all outcomes and record exactly the original memory. -/
def MemorySingleAliasObservation {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (memory : MemoryNativeObject L) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (MemoryAliasResult L × MemoryNativeWorld (MemoryCreationTrace W L)))) : Prop :=
  if dispatch.firstSelected before memory then
    MemoryCreationEvents [.first memory] outcome ∧
      memoryCreationProject outcome = dispatch.first memory before
  else
    MemoryCreationEvents [] outcome ∧ ∃ reference,
      memoryCreationProject outcome = some (.ok (.reference reference, before)) ∧
      reference.memory = memory ∧ reference.data.val = 0

/-- One-argument GenericMemoryRef preserves genuine memoryref dispatch on the
unspecified type parameters, without asserting the custom result's type.
Source: base/boot.jl:771. -/
def MemorySingleAliasBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryCreationDispatch W L) (memory : MemoryNativeObject L)
    (before : MemoryNativeWorld W),
    MemorySingleAliasObservation dispatch memory before
      (genericMemoryRefCtor (memoryCreationTracedDispatch dispatch) memory (memoryCreationStart before))

/-- Source sequencing after selected custom construction: the second call sees
exactly the first call's result and post-call state, and cannot run after an
error or divergence. The second result remains unrestricted. -/
def MemoryCustomConstructionThenReference {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeType L) (n : JInt .i64) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (MemoryAliasResult L × MemoryNativeWorld (MemoryCreationTrace W L)))) : Prop :=
  match dispatch.constructor type n before with
  | none => outcome = none
  | some (.error error) =>
      memoryCreationProject outcome = some (.error error) ∧
      MemoryCreationEvents [.constructor type n] outcome
  | some (.ok (value, middle)) =>
      memoryCreationProject outcome = dispatch.afterCustomConstructor value middle ∧
      MemoryCreationEvents [.constructor type n, .afterConstructor value] outcome

/-- Complete new_as_memoryref source-path invariant. Allocation failures stop
before memoryref, successful default allocation satisfies independent heap and
range observations before the current-world dispatch decision, and arbitrary
custom construction flows to an unrestricted actual memoryref call.
Source: base/boot.jl:779. -/
def NewAsMemoryReferenceObservation {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeRefType L) (n : JInt .i64) (before : MemoryNativeWorld W)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException L) × MemoryNativeWorld (MemoryCreationTrace W L))
      (MemoryAliasResult L × MemoryNativeWorld (MemoryCreationTrace W L)))) : Prop :=
  if dispatch.constructorSelected before type.memoryType n then
    MemoryCustomConstructionThenReference dispatch type.memoryType n before outcome
  else
    (∃ error after,
      MemoryAllocationObservation type.memoryType n.val before (some (.error (error, after))) ∧
      memoryCreationProject outcome = some (.error (error, after)) ∧
      MemoryCreationEvents [] outcome) ∨
    (∃ memory middle,
      MemoryAllocationObservation type.memoryType n.val before (some (.ok (memory, middle))) ∧
      MemorySingleAliasObservation dispatch memory middle outcome)

/-- Every constructor/memoryref selection and every custom outcome, including
divergence, is covered without a callee law or narrowed return type.
Source: base/boot.jl:779. -/
def NewAsMemoryReferenceBehavior : Prop :=
  ∀ (W L : Type) (dispatch : MemoryCreationDispatch W L) (type : MemoryNativeRefType L)
    (n : JInt .i64) (before : MemoryNativeWorld W),
    NewAsMemoryReferenceObservation dispatch type n before
      (newAsMemoryRefCtor (memoryCreationTracedDispatch dispatch) type n (memoryCreationStart before))

/-- Independent todo entries for ten completed GenericMemory source methods
and their concrete allocation, pointer/index, validation and throwing helpers. -/
def memoryNativeEntries : List Entry := [
  { id := "boot-memory-allocation", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind}"]
    statement := "The direct GenericMemory constructor validates kind, CPU address space, element/layout and native count/byte size in source order, retaining exact failures and unchanged state; successful nonempty allocation is fresh and preserves type/length/initialization, while zero returns the existing cached singleton."
    source := "base/boot.jl:762; src/genericmemory.c:55-102; src/builtins.c:2233-2241"
    notes := "Full descriptor and Int domains. Native size_t checks and exact MAXINTVAL-1 limits. Physical allocation/exhaustion abstracted without a budget/callback. Covers memoryNativeAlloc/New/Allocate and metadata/width helpers."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryConstructorAllocation },
  { id := "boot-memory-constructor-alias", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, d::NTuple{1,Int}) where {T,kind,addrspace}",
      "(self::Type{GenericMemory{kind,T,addrspace}})() where {T,kind,addrspace}"]
    statement := "Tuple/empty aliases forward the original type and projected dimension or native zero to the actual selected constructor, preserving arbitrary custom values/effects/errors/divergence; the installed branch retains independent allocation validation, identity and initialization invariants."
    source := "base/boot.jl:763,765; exact independent dispatch trace and allocation observations"
    notes := "Custom specialization on unspecified type parameters is explicit. No custom result type is assumed. Covers memoryNativeConstruct."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryConstructorAliasBehavior },
  { id := "boot-memory-first-reference", juliaFile := "base/boot.jl"
    juliaFns := ["memoryref(mem::GenericMemory)"]
    statement := "The direct first-reference wrapper retains the exact original memory identity/type, uses its first pointer-or-offset position, accepts empty memories, and leaves all heap and external state unchanged."
    source := "base/boot.jl:768; src/builtins.c:2243-2255; src/genericmemory.c:299-308"
    notes := "Concrete type-parameter preservation and pointer-or-offset representation; covers memoryNativeFirst."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryFirstReferenceFields },
  { id := "boot-memory-single-alias", juliaFile := "base/boot.jl"
    juliaFns := ["GenericMemoryRef(mem::GenericMemory)"]
    statement := "The one-argument constructor preserves the actual current-world memoryref choice: custom calls receive the exact original memory and retain every outcome, while the installed branch preserves first-position reference fields and unchanged state."
    source := "base/boot.jl:771; independent actual-call trace and reference-field observation"
    notes := "All selected methods without correctness, termination or reference-return laws. Covers memoryNativeSelectFirst."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemorySingleAliasBehavior },
  { id := "boot-memory-indexed-wrapper", juliaFile := "base/boot.jl"
    juliaFns := ["memoryref(mem::GenericMemory, i::Integer)"]
    statement := "The indexed memory wrappers call Int on the original Integer, retain every conversion effect/error/divergence, reject wrong returned types, and otherwise preserve memory identity with exact native displacement or the exact BoundsError according to the current post-call length. Both Bool values are covered."
    source := "base/boot.jl:769; src/builtins.c:2257-2274; src/rtutils.c:190-194"
    notes := "All custom Integer dispatches without correctness laws. Concrete native Int assertion precedes current-length bounds; the C builtin checks bounds even when its Boolean is false. Covers memoryNativeAssertIndex/IndexMemory and throwing helper."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryIndexedWrapperBehavior },
  { id := "boot-memory-shifted-wrapper", juliaFile := "base/boot.jl"
    juliaFns := ["memoryref(ref::GenericMemoryRef, i::Integer)"]
    statement := "Reference-relative wrappers retain arbitrary conversion outcomes, then check the native displaced position against the current length and preserve exact pointer-or-offset bits, source reference in BoundsError, and post-conversion state. Negative/zero relative moves and UInt64 wrapping remain represented."
    source := "base/boot.jl:770; src/builtins.c:2275-2297; src/rtutils.c:190-194"
    notes := "Concrete boxed, union/zero-size, and inline layout branches, including C integer promotion in pointer-difference division. Quantifies every open dispatch without termination or success assumptions; covers the native quotient/index helpers."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryShiftedWrapperBehavior },
  { id := "boot-memory-alias-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["GenericMemoryRef(mem::GenericMemory, i::Integer)", "GenericMemoryRef(mem::GenericMemoryRef, i::Integer)"]
    statement := "Indexed GenericMemoryRef constructors preserve actual default/custom memoryref dispatch, forwarding the original object and Integer exactly once; custom methods may return any value or change state, throw or diverge, while default methods retain the complete native assertion/bounds/aliasing behavior."
    source := "base/boot.jl:772-773; independent request trace and full outcome/identity invariant"
    notes := "The unspecified Integer type permits more-specific memoryref methods. Instrumentation records exact operands and distinguishes a custom memoryref request from the default Int conversion; no callback-correctness, termination or native-reference return law is assumed."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.MemoryAliasDispatchBehavior },
  { id := "boot-new-as-memory-reference", juliaFile := "base/boot.jl"
    juliaFns := ["new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace}"]
    statement := "new_as_memoryref projects its actual mem type, preserves selected constructor dispatch and arbitrary return values, and only on success calls memoryref on that exact result in the resulting world. Installed allocation retains all size/type checks, while default memoryref retains identity/first-position fields and custom calls retain every outcome."
    source := "base/boot.jl:779; src/genericmemory.c:55-102; exact independent call sequence and heap observations"
    notes := "No fieldtype/type-application callback. Custom constructor results have unfixed type, making subsequent memoryref dispatch genuinely open. Default/custom known-memory selection is explicit, with no correctness or termination assumption."
    status := .todo, thm := none
    prop := ``JuliaLean.Proofs.base.boot.Models2Group1.NewAsMemoryReferenceBehavior }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1.GenericForwarding

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

abbrev RuntimeValue (L : Type) := JuliaLean.base.expr.Value L

/-- An independent observation of one actual generic invocation. The event
records its target, complete argument tuple, original world, result or error,
and final world. It is ghost specification data, not a Julia allocation. -/
inductive CallEvent (W L : Type) where
  | returned (target : RuntimeValue L) (args : List (RuntimeValue L))
      (before : W) (value : RuntimeValue L) (after : W)
  | raised (target : RuntimeValue L) (args : List (RuntimeValue L))
      (before : W) (error : RuntimeValue L) (after : W)

/-- Run an unrestricted actual callback while retaining one inaccessible
ghost event on every finite outcome. The callback cannot erase or manufacture
this event; its actual state, value, exception and divergence are preserved. -/
def observeCall {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (target : RuntimeValue L) (args : List (RuntimeValue L)) :
    CoreM (W × List (CallEvent W L)) L (RuntimeValue L) :=
  fun (before, events) =>
    match dispatch target args before with
    | none => none
    | some (.ok (value, after)) =>
        some (.ok (value, (after, events ++ [.returned target args before value after])))
    | some (.error (error, after)) =>
        some (.error (error, (after, events ++ [.raised target args before error after])))

/-- A forwarding method preserves the entire arbitrary outcome of exactly one
call with the required target and original ordered arguments. This independent
protocol checks target/arguments, call count, termination, result/error identity
and world effects; it is not another executable version of a source method. -/
def ForwardObservation {W L : Type} (prior : List (CallEvent W L))
    (target : RuntimeValue L) (args : List (RuntimeValue L)) (before : W)
    (actualCall : Option (Except (RuntimeValue L × W) (RuntimeValue L × W)))
    (method : Option (Except
      (RuntimeValue L × (W × List (CallEvent W L)))
      (RuntimeValue L × (W × List (CallEvent W L))))) : Prop :=
  match actualCall, method with
  | none, none => True
  | some (.ok (value, after)), some (.ok (observed, (observedAfter, events))) =>
      observed = value ∧ observedAfter = after ∧
        events = prior ++ [.returned target args before value after]
  | some (.error (error, after)), some (.error (observed, (observedAfter, events))) =>
      observed = error ∧ observedAfter = after ∧
        events = prior ++ [.raised target args before error after]
  | _, _ => False

/-- A constructor-then-throw protocol distinguishes a constructor exception
from a successful constructor return that the outer method throws. Both retain
the exact thrown value and post-call world; no successful source-method return
is permitted. Divergence occurs exactly when the actual constructor diverges.
No exception-class promise is invented for arbitrary custom constructors. -/
def ThrowAfterCallObservation {W L A : Type} (prior : List (CallEvent W L))
    (target : RuntimeValue L) (args : List (RuntimeValue L)) (before : W)
    (actualCall : Option (Except (RuntimeValue L × W) (RuntimeValue L × W)))
    (method : Option (Except
      (RuntimeValue L × (W × List (CallEvent W L)))
      (A × (W × List (CallEvent W L))))) : Prop :=
  match actualCall, method with
  | none, none => True
  | some (.ok (value, after)), some (.error (thrown, (observedAfter, events))) =>
      thrown = value ∧ observedAfter = after ∧
        events = prior ++ [.returned target args before value after]
  | some (.error (error, after)), some (.error (thrown, (observedAfter, events))) =>
      thrown = error ∧ observedAfter = after ∧
        events = prior ++ [.raised target args before error after]
  | _, _ => False

/-- Every constructible keyword call discards only kwargs and the dispatch
marker, forwarding all original positional values once to Union{}. The result
need not be an instance of an uninhabited type; custom constructor outcomes,
errors, mutation and divergence remain unrestricted.
Source: base/boot.jl:399; native UInt32 incoming arity includes two fixed operands.
-/
def KeywordBottomForwarding : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (kwargs : RuntimeValue L)
    (args : JuliaLean.base.boot.Models2Group1.GenericForwarding.KeywordBottomArguments L)
    (world : W) (trace : List (CallEvent W L)),
    let instrumented := { ops with call := observeCall dispatch }
    ForwardObservation trace (coreV ops "Union{}") args.values world
      (dispatch (coreV ops "Union{}") args.values world)
      (JuliaLean.base.boot.Models2Group1.GenericForwarding.keywordBottom
        instrumented kwargs args (world, trace))

/-- The MethodError alias forwards original f/args and the mathematical maximum
native UInt value to exactly one selected constructor, preserving its entire
outcome. The native word is characterized by value rather than by a call to
the model's typemax helper; no return-type assertion is allowed.
Source: base/boot.jl:558,567; installed 64-bit UInt representation.
-/
def MethodErrorDefaultForwarding : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (f args : RuntimeValue L) (world : W) (trace : List (CallEvent W L)),
    let instrumented := { ops with call := observeCall dispatch }
    ∃ maximum : JInt .u64, maximum.val = (2 : Int)^64 - 1 ∧
      ForwardObservation trace (coreV ops "MethodError") [f, args, intV ops maximum] world
        (dispatch (coreV ops "MethodError") [f, args, intV ops maximum] world)
        (JuliaLean.base.boot.Models2Group1.GenericForwarding.methodErrorDefault
          instrumented f args (world, trace))

/-- The generic throw helper first invokes InexactError on the exact original
Symbol, target and value. It preserves constructor failure/divergence and throws
an arbitrary successful result without mutation or narrowing of that result.
Source: base/boot.jl:1045; complete constructor-call and throw-order invariant.
-/
def ThrowInexactForwarding : Prop :=
  ∀ (W L A : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (func target input : RuntimeValue L) (world : W) (trace : List (CallEvent W L)),
    let instrumented := { ops with call := observeCall dispatch }
    ThrowAfterCallObservation trace (coreV ops "InexactError") [func, target, input] world
      (dispatch (coreV ops "InexactError") [func, target, input] world)
      (JuliaLean.base.boot.Models2Group1.GenericForwarding.throwInexact (A := A)
        instrumented func target input (world, trace))

/-- Even the selected typename fallback invokes a generic TypeNameError
constructor on its arbitrary argument. The exact constructor result is thrown
only after it returns, while its own error, effects and divergence pass through.
The source does not require custom constructor results to be TypeNameErrors.
Source: base/boot.jl:1310; full actual-call and exception-identity invariant.
-/
def TypeNameFallbackForwarding : Prop :=
  ∀ (W L A : Type) (ops : CoreOps (W × List (CallEvent W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (input : RuntimeValue L) (world : W) (trace : List (CallEvent W L)),
    let instrumented := { ops with call := observeCall dispatch }
    ThrowAfterCallObservation trace (coreV ops "TypeNameError") [input] world
      (dispatch (coreV ops "TypeNameError") [input] world)
      (JuliaLean.base.boot.Models2Group1.GenericForwarding.typeNameFallback (A := A)
        instrumented input (world, trace))

/-- Four complete source methods, all with unproved independent protocol
properties. The existing models, proof entries and native conversions remain
unchanged; integration replaces only earlier incomplete additive aliases. -/
def entriesGenericForwarding : List Entry := [
  { id := "boot-keyword-bottom-forwarding", juliaFile := "base/boot.jl"
    juliaFns := ["kwcall(kwargs, ::Type{Union{}}, a...)"]
    statement := "The keyword Union{} wrapper forwards exactly the original positional values once and preserves every selected constructor result, error, effect and divergence, without imposing the fallback's exception behavior."
    source := "base/boot.jl:399; src/julia.h:2591,2596-2599; independent actual-call invariant"
    status := .todo, thm := none
    prop := ``KeywordBottomForwarding
    notes := "Incoming argument tuple is UInt32-bounded including kwargs and type marker; outgoing arguments fit unchanged. Generic constructor dispatch on unfixed argument types uses existing CoreOps.call, with no laws." },
  { id := "boot-methoderror-default-forwarding", juliaFile := "base/boot.jl"
    juliaFns := ["MethodError(@nospecialize(f), @nospecialize(args))"]
    statement := "The MethodError alias forwards the original f/args and native UInt maximum to one generic constructor and preserves all arbitrary outcomes and effects without a result-type check."
    source := "base/boot.jl:558,567; independent native-value and call/outcome invariant"
    status := .todo, thm := none
    prop := ``MethodErrorDefaultForwarding
    notes := "The direct three-argument inner constructor remains separately complete. This source alias does not force that default method on custom argument types." },
  { id := "boot-throw-inexact-forwarding", juliaFile := "base/boot.jl"
    juliaFns := ["throw_inexacterror(func::Symbol, to, val)"]
    statement := "throw_inexacterror invokes InexactError with the original Symbol/target/value, propagates constructor errors/effects/divergence, and throws exactly any successfully returned Julia value."
    source := "base/boot.jl:1045; independent actual-call and outer-throw invariant"
    status := .todo, thm := none
    prop := ``ThrowInexactForwarding
    notes := "Full generic helper; source-typed Symbol and arbitrary Any target/value. Fixed native conversion branches remain separately modeled with their closed native exception behavior." },
  { id := "boot-typename-fallback-forwarding", juliaFile := "base/boot.jl"
    juliaFns := ["typename(a)"]
    statement := "The selected typename fallback invokes TypeNameError once on the original value and throws its exact arbitrary return, preserving constructor errors, effects and divergence."
    source := "base/boot.jl:1310; independent actual-call and thrown-value invariant"
    status := .todo, thm := none
    prop := ``TypeNameFallbackForwarding
    notes := "The generic exception constructor may be specialized on user argument types. The selected DataType typename method is separately a concrete field read; composite typename recursion is outside this entry." }
]

end JuliaLean.Proofs.base.boot.Models2Group1.GenericForwarding


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

/-- Source-selected nested UnionAll steps follow actual body fields. No generic
call executes during these steps, so each selector observes the same original
world. The path relation does not execute typename or compute its result. -/
inductive UnionAllTypeNamePath {W V : Type}
    (selected : W → JuliaLean.base.boot.Models2Group1.Reflection.Value V → Bool)
    (world : W) :
    JuliaLean.base.boot.Models2Group1.Reflection.Value V →
    JuliaLean.base.boot.Models2Group1.Reflection.Value V → Prop where
  | refl {value} : UnionAllTypeNamePath selected world value value
  | step {value body final} : AliasDispatch.UnionAllBody value body →
      selected world value = true → UnionAllTypeNamePath selected world body final →
      UnionAllTypeNamePath selected world value final

/-- A final actual generic target is either a non-UnionAll value, for which
this source method is inapplicable, or a UnionAll whose selected method is
another method. No output type or correctness promise is imposed on it. -/
def UnionAllTypeNameTarget {W V : Type}
    (selected : W → JuliaLean.base.boot.Models2Group1.Reflection.Value V → Bool)
    (world : W) (start final : JuliaLean.base.boot.Models2Group1.Reflection.Value V) : Prop :=
  UnionAllTypeNamePath selected world start final ∧
    ((∀ body, ¬ AliasDispatch.UnionAllBody final body) ∨ selected world final = false)

/-- The complete selected UnionAll typename body first reads its actual body,
follows zero or more own-source UnionAll steps, then makes exactly one genuine
other-method generic call. Its arbitrary return/exception and post-call world
are retained. Actual path/argument/event witnesses detect skipped or changed
body fields, wrong source selection, extra calls, changed results and discarded
effects. Finite const-body recursion cannot itself diverge; divergence is tied
to the actual reached selected call. No callee-correctness law is assumed.
Source: base/boot.jl:1318; src/jltypes.c:3728-3735.
-/
def TypeNameUnionAllForwarding : Prop :=
  ∀ (W V L : Type)
    (ops : CoreOps (W × List (AliasDispatch.CallEvent W L)) L)
    (dispatch : JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      CoreM W L (JuliaLean.base.expr.Value L))
    (selected : W → JuliaLean.base.boot.Models2Group1.Reflection.Value V → Bool)
    (encode : JuliaLean.base.boot.Models2Group1.Reflection.Value V → JuliaLean.base.expr.Value L)
    (value : JuliaLean.base.boot.Models2Group1.UnionAllTypeNameInput V) (world : W),
    let instrumented := { ops with call := AliasDispatch.observeCall dispatch }
    match JuliaLean.base.boot.Models2Group1.typeNameUnionAllDispatch instrumented
        (fun state input => selected state.1 input) encode value (world, []) with
    | none => ∃ target, UnionAllTypeNameTarget selected world value.body.object target ∧
        dispatch (coreV ops "typename") [encode target] world = none
    | some (.ok (result, (after, events))) =>
        ∃ target, UnionAllTypeNameTarget selected world value.body.object target ∧
          events = [.returned (coreV ops "typename") [encode target] result world after]
    | some (.error (error, (after, events))) =>
        ∃ target, UnionAllTypeNameTarget selected world value.body.object target ∧
          events = [.raised (coreV ops "typename") [encode target] error world after]

/-- Entry for the complete selected UnionAll method and its own recursion. -/
def entriesTypeNameUnionAll : List Entry := [
  { id := "boot-typename-unionall-dispatch"
    juliaFile := "base/boot.jl"
    juliaFns := ["typename(union::UnionAll)"]
    statement := "The selected UnionAll typename method follows actual body fields through explicit own-source recursion, then preserves exactly one reached other generic method's arbitrary result, exception, effects or divergence."
    source := "base/boot.jl:1318; src/jltypes.c:3728-3735; independent actual-body path and call invariant"
    status := .todo
    prop := ``TypeNameUnionAllForwarding
    thm := none
    notes := "Own UnionAll method selection executes structural recursion; only other selected targets on the Any-typed body use existing CoreOps.call. No callee law or TypeName-only return restriction. Does not claim completion of the separate Union method's arbitrary-value === algorithm. Reuses AliasDispatch's call and body-field observers." }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.Registry

/-- The two singleton Core stream methods read the corresponding loaded runtime
pointer slot. Quantification over native UInt64 bit patterns includes null and
every other Ptr{Cvoid} value; the unrelated slot cannot affect the answer.
The legacy handle pair is a snapshot of the actual two global storage slots at
the read, not an implementation parameter. No operation inspects or writes the
stream addressed by the pointer. Source: base/boot.jl:981-982. The fixed pointerref
has index/alignment Int(1), valid primitive element type Ptr{Cvoid}, and reads the
slot without address offset (src/runtime_intrinsics.c:456-473). Physical boxing
and GC are abstracted; the result is pointer bits, not allocation identity. -/
def CoreIOGlobalPointerBits : Prop :=
  ∀ (stdout stderr unrelated : JInt .u64),
    let handles := (stdout.val.toNat, stderr.val.toNat)
    let out := JuliaLean.BootCov.Misc.ioPointer handles .stdout
    let err := JuliaLean.BootCov.Misc.ioPointer handles .stderr
    out = stdout.val.toNat ∧ err = stderr.val.toNat ∧
    out < 2 ^ 64 ∧ err < 2 ^ 64 ∧
    JuliaLean.BootCov.Misc.ioPointer (stdout.val.toNat, unrelated.val.toNat) .stdout = out ∧
    JuliaLean.BootCov.Misc.ioPointer (unrelated.val.toNat, stderr.val.toNat) .stderr = err

section
open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1

theorem coreIOGlobalPointerBits_proven : CoreIOGlobalPointerBits := by
  intro stdout stderr unrelated
  have hs := stdout.property
  have he := stderr.property
  change 0 ≤ stdout.val ∧ stdout.val ≤ 18446744073709551615 at hs
  change 0 ≤ stderr.val ∧ stderr.val ≤ 18446744073709551615 at he
  exact ⟨rfl, rfl, by change stdout.val.toNat < 18446744073709551616; omega,
    by change stderr.val.toNat < 18446744073709551616; omega, rfl, rfl⟩
end

def entriesIOGlobals : List Entry := [
  { id := "boot-core-io-global-pointer-bits"
    juliaFile := "base/boot.jl"
    juliaFns := ["io_pointer(::CoreSTDOUT)", "io_pointer(::CoreSTDERR)"]
    statement := "Each Core stream method returns the complete native pointer bits from its corresponding runtime global slot, including null; changing the other slot cannot affect the result."
    source := "base/boot.jl:981-982; src/runtime_intrinsics.c:456-473, fixed valid pointerref field-read invariant"
    notes := "Reuses the existing explicit ioPointer state-snapshot projection. Inputs are actual loaded global storage values, represented by native UInt64 bits rather than unbounded Julia addresses. No arbitrary cglobal/pointerref or output-runtime implementation is claimed."
    status := .proven, prop := ``CoreIOGlobalPointerBits, thm := some ``JuliaLean.Proofs.base.boot.Models2Group1.coreIOGlobalPointerBits_proven }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot.Models2Group1.PrintMany

open JuliaLean JuliaLean.base.boot JuliaLean.Registry

abbrev RuntimeValue (L : Type) := JuliaLean.base.expr.Value L
abbrev Selection (W L : Type) := JuliaLean.base.boot.Models2Group1.PrintMany.SourceSelected W L
abbrev Outcome (W L : Type) := Except (RuntimeValue L × W) (RuntimeValue L × W)

/-- Ghost observation of an actual generic call and its complete outcome.
The caller cannot manufacture this trace through arbitrary user state. -/
inductive Event (W L : Type) where
  | returned (target : RuntimeValue L) (args : List (RuntimeValue L))
      (before : W) (result : RuntimeValue L) (after : W)
  | raised (target : RuntimeValue L) (args : List (RuntimeValue L))
      (before : W) (error : RuntimeValue L) (after : W)

/-- Instrument exactly the genuine generic calls, preserving all arbitrary
values, exceptions, effects and divergence. This is a specification observer,
not a runtime operation or a law about any callee. -/
def observeCall {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (target : RuntimeValue L) (args : List (RuntimeValue L)) :
    CoreM (W × List (Event W L)) L (RuntimeValue L) :=
  fun (before, events) =>
    match dispatch target args before with
    | none => none
    | some (.ok (result, after)) =>
        some (.ok (result, (after, events ++ [.returned target args before result after])))
    | some (.error (error, after)) =>
        some (.error (error, (after, events ++ [.raised target args before error after])))

/-- A tail is handled by another generic method when it has zero/one payloads
or current dispatch does not select source1000. Fixed-arity999 dominates1000
for one payload; for zero payloads1000 is inapplicable. -/
def OtherTail {W L : Type} (selected : Selection W L) (world : W)
    (io : RuntimeValue L) (tail : List (RuntimeValue L)) : Prop :=
  tail.length < 2 ∨ selected world io tail = false

/-- A declarative prefix of source-selected steps. Each step consumes exactly
one original payload and records exactly one successful two-argument print,
with the identical io handle. Remaining arguments are an original suffix;
source selection is observed only after the actual preceding call's effects.
This relation does not execute a print program or compute an expected result. -/
inductive SourcePrefix {W L : Type} (selected : Selection W L)
    (target io : RuntimeValue L) : W → List (RuntimeValue L) →
      W → List (RuntimeValue L) → List (Event W L) → Prop
  | start (world : W) (values : List (RuntimeValue L)) :
      SourcePrefix selected target io world values world values []
  | advance {before initial current head tail after ignored events}
      (previous : SourcePrefix selected target io before initial current (head :: tail) events)
      (twoOrMore : 2 ≤ tail.length)
      (sourceChosen : selected after io tail = true) :
      SourcePrefix selected target io before initial after tail
        (events ++ [.returned target [io, head] current ignored after])

/-- Finite terminal observation. The first call may raise; otherwise its
arbitrary result is discarded and exactly one generic call receives the full
remaining original suffix (including an empty suffix). The final generic
result/error is returned unchanged, with all worlds connected in order. -/
inductive Terminal {W L : Type} (selected : Selection W L)
    (target io : RuntimeValue L) (before : W) (first : RuntimeValue L)
    (tail : List (RuntimeValue L)) : Outcome W L → List (Event W L) → Prop
  | firstRaised (error : RuntimeValue L) (after : W) :
      Terminal selected target io before first tail (.error (error, after))
        [.raised target [io, first] before error after]
  | returned (ignored : RuntimeValue L) (middle : W)
      (other : OtherTail selected middle io tail)
      (result : RuntimeValue L) (after : W) :
      Terminal selected target io before first tail (.ok (result, after))
        [.returned target [io, first] before ignored middle,
          .returned target (io :: tail) middle result after]
  | tailRaised (ignored : RuntimeValue L) (middle : W)
      (other : OtherTail selected middle io tail)
      (error : RuntimeValue L) (after : W) :
      Terminal selected target io before first tail (.error (error, after))
        [.returned target [io, first] before ignored middle,
          .raised target (io :: tail) middle error after]

/-- Every finite run has an original-order prefix and one terminal call-site
observation. This detects reordered/skipped/duplicated arguments, changes of io,
incorrect method-selection worlds, extra generic calls, swallowed exceptions,
or narrowed custom results. No model function occurs in this specification. -/
def FiniteObservation {W L : Type} (selected : Selection W L)
    (target io : RuntimeValue L) (before : W) (values : List (RuntimeValue L))
    (outcome : Outcome W L) (events : List (Event W L)) : Prop :=
  ∃ middle first tail prefixEvents terminalEvents,
    SourcePrefix selected target io before values middle (first :: tail) prefixEvents ∧
    Terminal selected target io middle first tail outcome terminalEvents ∧
    events = prefixEvents ++ terminalEvents

/-- Actual successful generic outcomes establish a reached source-selected
suffix when no final event list exists because a later callee diverges.
The equations record arbitrary actual callback behavior, not correctness laws. -/
inductive ActualPrefix {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (selected : Selection W L) (target io : RuntimeValue L) :
    W → List (RuntimeValue L) → W → List (RuntimeValue L) → Prop
  | start (world : W) (values : List (RuntimeValue L)) :
      ActualPrefix dispatch selected target io world values world values
  | advance {before initial current first tail ignored after}
      (previous : ActualPrefix dispatch selected target io before initial current (first :: tail))
      (returned : dispatch target [io, first] current = some (.ok (ignored, after)))
      (twoOrMore : 2 ≤ tail.length)
      (sourceChosen : selected after io tail = true) :
      ActualPrefix dispatch selected target io before initial after tail

/-- Structural source recursion strictly consumes payloads, so divergence must
occur in an actually reached generic callee. The witness identifies the exact
first call or final suffix call and includes all preceding successful effects.
The empty suffix call remains the actual print(io), with no assumed result. -/
def DivergenceObservation {W L : Type}
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (selected : Selection W L) (target io : RuntimeValue L) (before : W)
    (values : List (RuntimeValue L)) : Prop :=
  ∃ middle first tail,
    ActualPrefix dispatch selected target io before values middle (first :: tail) ∧
    (dispatch target [io, first] middle = none ∨
      ∃ ignored afterFirst,
        dispatch target [io, first] middle = some (.ok (ignored, afterFirst)) ∧
        OtherTail selected afterFirst io tail ∧
        dispatch target (io :: tail) afterFirst = none)

/-- Complete source1000 property over every native-bounded argument tuple,
all concrete IO subtypes represented by the universal carrier, and every
unrestricted generic dispatch implementation. Source recursion is observed as
an ordered suffix path; only other selected methods use arbitrary callbacks.
Finite results/errors and divergence are all covered without success, purity,
termination or output-type assumptions. Source: base/boot.jl:998-1000;
doc/src/manual/functions.md (varargs/splatting) and methods.md (dispatch).
-/
def PrintManyObservations : Prop :=
  ∀ (W L : Type) (ops : CoreOps (W × List (Event W L)) L)
    (dispatch : RuntimeValue L → List (RuntimeValue L) → CoreM W L (RuntimeValue L))
    (selected : Selection W L) (io : RuntimeValue L)
    (arguments : JuliaLean.base.boot.Models2Group1.PrintMany.Arguments L) (world : W),
    let instrumented := { ops with call := observeCall dispatch }
    match JuliaLean.base.boot.Models2Group1.PrintMany.printMany instrumented
      (fun state output remaining => selected state.1 output remaining)
      io arguments (world, []) with
    | none => DivergenceObservation dispatch selected (coreV ops "print") io world
        (arguments.first :: arguments.tail)
    | some (.ok (value, (after, events))) =>
        FiniteObservation selected (coreV ops "print") io world
          (arguments.first :: arguments.tail) (.ok (value, after)) events
    | some (.error (error, (after, events))) =>
        FiniteObservation selected (coreV ops "print") io world
          (arguments.first :: arguments.tail) (.error (error, after)) events

/-- One unproved entry covers the full variadic method and its source recursion. -/
def entriesPrintMany : List Entry := [
  { id := "boot-print-many-dispatch", juliaFile := "base/boot.jl"
    juliaFns := ["print(io::IO, @nospecialize(x), @nospecialize a...)"]
    statement := "Variadic print preserves the original io and payload order, discards only successful intermediate results, concretely recurses for selected source methods, and forwards final generic results/errors/effects or actual reachable divergence."
    source := "base/boot.jl:998-1000; doc/src/manual/functions.md, varargs/splatting; methods.md, method specificity; independent observed suffix-path invariant"
    status := .todo, thm := none
    prop := ``PrintManyObservations
    notes := "All callbacks and states quantified without laws. Installed fixed-arity999 dominates1000 for one payload; zero payloads cannot select1000. Source selection for ≥2 remaining payloads is evaluated after prior effects; own recursion is structural, not a callback or fuel cutoff. Empty-tail print(io) remains an actual generic call. Incoming UInt32 arity includes io and x." }
]

end JuliaLean.Proofs.base.boot.Models2Group1.PrintMany


namespace JuliaLean.Proofs.base.boot.Models2Group1

open JuliaLean JuliaLean.base.boot JuliaLean.base.boot.Models2Group1 JuliaLean.Registry

/-- Independent mathematical dimension product, with empty product one. -/
def ArrayDimensionProduct (dims : List (JInt .i64)) : Int :=
  (dims.map (fun dim => dim.val)).foldl (· * ·) 1

/-- Actual checked_dims dispatcher acceptance. Zero and one argument bypass
validation; longer argument lists reject negative/typemax dimensions and a
nonzero overflowing mathematical product. Zero products are accepted after all
individual-dimension checks. Source: boot.jl:782-818. -/
def ArrayDimensionsAccepted (dims : List (JInt .i64)) : Prop :=
  dims.length ≤ 1 ∨
    ((∀ dim ∈ dims, 0 ≤ dim.val ∧ dim.val < IntTy.max .i64) ∧
      0 ≤ ArrayDimensionProduct dims ∧ ArrayDimensionProduct dims ≤ IntTy.max .i64)

/-- Independent reference type observation from actual tagged metadata; no
implementation isa/type helper is used. -/
def ArrayReferenceMatches {L : Type} (element : ArrayNativeElement L) :
    MemoryAliasResult (ArrayNativeLeaf L) → Prop
  | .reference reference => reference.memory.type.identity = element.memoryType.identity
  | .other (.leaf (.reference identity _)) => identity = element.memoryType.identity
  | .other _ => False

/-- Independent raw-new success/error/heap observations after all field
expressions have completed. This observes final stored fields and freshness,
without executing the source new/helper as an expected result. -/
def ArrayNewObservation {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) (reference : MemoryAliasResult (ArrayNativeLeaf L))
    (before : ArrayNativeWorld W L) : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L)) → Prop
  | none => False
  | some (.error (error, after)) =>
      after = before ∧
      ((element.concrete = false ∨ element.hasLayout = false) ∧
        ∃ target, error = .leaf (.newSelf target) ∧ target.element = element ∧
          target.rank.val = dims.values.length) ∨
      (after = before ∧ element.concrete = true ∧ element.hasLayout = true ∧
        ¬ArrayReferenceMatches element reference ∧
        error = .leaf (.newReference element.memoryType reference))
  | some (.ok (result, after)) =>
      element.concrete = true ∧ element.hasLayout = true ∧
      ArrayReferenceMatches element reference ∧
      result.identity = before.external.1.cells.length ∧
      result.type.element = element ∧ result.type.rank.val = dims.values.length ∧
      after.heap = before.heap ∧ after.external.2 = before.external.2 ∧
      ∃ cell, after.external.1.cells = before.external.1.cells ++ [cell] ∧
        cell.type = result.type ∧ cell.reference = some reference ∧ cell.dimensions = some dims

/-- Actual installed Base selection, while retaining arbitrary unused custom
operations. This is a concrete Base instantiation, not a correctness law about
any user callback. -/
def arrayInstalledDispatch {W L : Type} (dispatch : ArrayNativeDispatch W L) :
    ArrayNativeDispatch W L where
  memory := { dispatch.memory with
    constructorSelected := fun _ _ _ => false
    firstSelected := fun _ _ => false }
  newAsSelected := fun _ _ _ => false
  newAs := dispatch.newAs

/-- Mathematical allocation/source-error observation for the installed Base
instantiation. Dimension rejection is first and leaves every state unchanged.
Otherwise the complete independent memory allocation contract determines the
intermediate state and object; raw-new assertions/fresh fields follow it. -/
def ArrayInstalledObservation {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) (before : ArrayNativeWorld W L)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L))) : Prop :=
  (ArrayDimensionsAccepted dims.values →
    (∃ error after,
      MemoryAllocationObservation element.memoryType (ArrayDimensionProduct dims.values) before
        (some (.error (error, after))) ∧
      outcome = some (.error (.leaf (.memory error), after))) ∨
    (∃ memory middle,
      MemoryAllocationObservation element.memoryType (ArrayDimensionProduct dims.values) before
        (some (.ok (memory, middle))) ∧
      ∃ reference : MemoryNativeRef (ArrayNativeLeaf L),
        reference.memory = memory ∧ reference.data.val = 0 ∧
        ArrayNewObservation element dims (.reference reference) middle outcome)) ∧
  (¬ArrayDimensionsAccepted dims.values →
    outcome = some (.error (.leaf (.dimensions (.argumentError "invalid Array dimensions")), before)))

/-- Actual source-dispatch request identities. -/
inductive ArrayCallEvent (L : Type) where
  | constructor (type : MemoryNativeType (ArrayNativeLeaf L)) (count : JInt .i64)
  | first (memory : MemoryNativeObject (ArrayNativeLeaf L))
  | afterConstructor (value : JuliaLean.base.expr.Value (ArrayNativeLeaf L))
  | newAs (type : MemoryNativeRefType (ArrayNativeLeaf L)) (count : JInt .i64)
  | arrayConstructor (target : ArrayNativeType L) (dims : ArrayNativeDimensions)

/-- External instrumentation records the Array heap after the last user
operation and the exact reference value returned by the last reference call.
It imposes no restriction on that operation's actual state effects. -/
structure ArrayCallTrace (W L : Type) where
  actual : W
  lastCells : List (ArrayNativeCell L)
  lastReference : Option (MemoryAliasResult (ArrayNativeLeaf L))
  events : List (ArrayCallEvent L)

def arrayCallRawWorld {W L : Type} (world : ArrayNativeWorld (ArrayCallTrace W L) L) :
    ArrayNativeWorld W L := ⟨world.heap, (world.external.1, world.external.2.actual)⟩

def arrayCallStart {W L : Type} (world : ArrayNativeWorld W L) :
    ArrayNativeWorld (ArrayCallTrace W L) L :=
  ⟨world.heap, (world.external.1, ⟨world.external.2, world.external.1.cells, none, []⟩)⟩

/-- Record arbitrary memory-operation outcomes, including their changed Array
heap. `observe` marks only the actual returned reference value; constructor
results remain unrestricted and are not silently asserted to be memories. -/
def arrayRecordMemory {W L A : Type} (event : ArrayCallEvent L)
    (observe : A → Option (MemoryAliasResult (ArrayNativeLeaf L)))
    (action : MemoryNativeM (ArrayNativeHeap L × W) (ArrayNativeLeaf L) A) :
    MemoryNativeM (ArrayNativeHeap L × ArrayCallTrace W L) (ArrayNativeLeaf L) A :=
  fun world =>
    let prior := world.external.2
    match action (arrayCallRawWorld world) with
    | none => none
    | some (.error (error, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          prior.lastReference, prior.events ++ [event]⟩
        some (.error (error, ⟨after.heap, (after.external.1, trace)⟩))
    | some (.ok (value, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          (observe value).or prior.lastReference, prior.events ++ [event]⟩
        some (.ok (value, ⟨after.heap, (after.external.1, trace)⟩))

def arrayRecordNewAs {W L : Type} (type : MemoryNativeRefType (ArrayNativeLeaf L))
    (count : JInt .i64) (action : ArrayNativeM W L (MemoryAliasResult (ArrayNativeLeaf L))) :
    ArrayNativeM (ArrayCallTrace W L) L (MemoryAliasResult (ArrayNativeLeaf L)) :=
  fun world =>
    let prior := world.external.2
    match action (arrayCallRawWorld world) with
    | none => none
    | some (.error (error, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          prior.lastReference, prior.events ++ [.newAs type count]⟩
        some (.error (error, ⟨after.heap, (after.external.1, trace)⟩))
    | some (.ok (value, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          some value, prior.events ++ [.newAs type count]⟩
        some (.ok (value, ⟨after.heap, (after.external.1, trace)⟩))

/-- Exact instrumentation of all genuine custom dispatch sites. Selectors see
the actual current world, not a stale initial snapshot. -/
def arrayTracedDispatch {W L : Type} (dispatch : ArrayNativeDispatch W L) :
    ArrayNativeDispatch (ArrayCallTrace W L) L where
  memory := {
    constructorSelected world type n := dispatch.memory.constructorSelected (arrayCallRawWorld world) type n
    constructor type n := arrayRecordMemory (.constructor type n) (fun _ => none)
      (dispatch.memory.constructor type n)
    firstSelected world memory := dispatch.memory.firstSelected (arrayCallRawWorld world) memory
    first memory := arrayRecordMemory (.first memory) some (dispatch.memory.first memory)
    afterCustomConstructor value := arrayRecordMemory (.afterConstructor value) some
      (dispatch.memory.afterCustomConstructor value) }
  newAsSelected world type n := dispatch.newAsSelected (arrayCallRawWorld world) type n
  newAs type n := arrayRecordNewAs type n (dispatch.newAs type n)

/-- Every type/count request is the original fixed field type and independent
mathematical dimension product. First-reference requests retain that same
memory type. Unspecified custom return values are deliberately unrestricted. -/
def ArrayRequestsMatch {L : Type} (element : ArrayNativeElement L) (dims : List (JInt .i64))
    (events : List (ArrayCallEvent L)) : Prop :=
  ∀ event ∈ events, match event with
    | .constructor type count => type = element.memoryType ∧ count.val = ArrayDimensionProduct dims
    | .first memory => memory.type = element.memoryType
    | .afterConstructor _ => True
    | .newAs type count => type.memoryType = element.memoryType ∧ count.val = ArrayDimensionProduct dims
    | .arrayConstructor _ _ => True

/-- Source-owned effects under every user dispatch. Errors do not allocate an
Array after the last callback. Success creates exactly one fresh Array with
its original type/rank/tuple and the exact actual reference result when user
code supplied it; all previously created/shared arrays remain unchanged.
The separate installed observation excludes spurious divergence or hidden
errors when no custom operation is selected. -/
def ArrayOwnEffects {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeObject L × ArrayNativeWorld (ArrayCallTrace W L) L)) → Prop
  | none => True
  | some (.error (_, after)) =>
      after.external.1.cells = after.external.2.lastCells ∧
      ArrayRequestsMatch element dims.values after.external.2.events
  | some (.ok (result, after)) =>
      element.concrete = true ∧ element.hasLayout = true ∧
      result.identity = after.external.2.lastCells.length ∧
      result.type.element = element ∧ result.type.rank.val = dims.values.length ∧
      ArrayRequestsMatch element dims.values after.external.2.events ∧
      ∃ reference cell,
        ArrayReferenceMatches element reference ∧
        (∀ returned, after.external.2.lastReference = some returned → reference = returned) ∧
        after.external.1.cells = after.external.2.lastCells ++ [cell] ∧
        cell.type = result.type ∧ cell.reference = some reference ∧ cell.dimensions = some dims

/-- Invalid checked dimensions must fail before any user operation, regardless
of its result, effects or termination. No success-domain restriction appears
in the corresponding full constructor properties. -/
def ArrayDimensionErrorFirst {W L : Type} (dims : List (JInt .i64))
    (before : ArrayNativeWorld W L) (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L))) : Prop :=
  ¬ArrayDimensionsAccepted dims →
    outcome = some (.error (.leaf (.dimensions (.argumentError "invalid Array dimensions")), before))

/-- Exact continuation of an actual open reference-call outcome. A callee's
error/divergence is propagated without a later allocation; its successful value
is checked and stored by independent raw-new observations in its actual final
world. This is a call-boundary protocol, not a duplicate constructor body. -/
def ArrayFinishReferenceCall {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions)
    (called : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (MemoryAliasResult (ArrayNativeLeaf L) × ArrayNativeWorld W L)))
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L))) : Prop :=
  match called with
  | none => outcome = none
  | some (.error error) => outcome = some (.error error)
  | some (.ok (reference, after)) => ArrayNewObservation element dims reference after outcome

/-- The same call-boundary protocol for the complete installed memory
composition, preserving its original exception as a transparent refinement.
Its allocation/dispatch/call-order behavior has separate independent registered
MemoryCreation properties; no correctness law is assumed here. -/
def ArrayFinishMemoryCall {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions)
    (called : Option (Except
      (JuliaLean.base.expr.Value (MemoryNativeException (ArrayNativeLeaf L)) × ArrayNativeWorld W L)
      (MemoryAliasResult (ArrayNativeLeaf L) × ArrayNativeWorld W L)))
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L))) : Prop :=
  match called with
  | none => outcome = none
  | some (.error (error, after)) => outcome = some (.error (.leaf (.memory error), after))
  | some (.ok (reference, after)) => ArrayNewObservation element dims reference after outcome

/-- Full source call-boundary invariant. The count is characterized by pure
mathematics, rather than the checked_dims implementation. Rank-one's source
composition uses the independently covered constructor→memoryref helper;
other bodies preserve the actual selected new_as_memoryref boundary. Every
reached callee outcome, including divergence, determines whether raw new can
run and precisely which world/reference it receives. -/
def ArraySourceObservation {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (directOne : Bool) (element : ArrayNativeElement L) (dims : ArrayNativeDimensions)
    (before : ArrayNativeWorld W L)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeObject L × ArrayNativeWorld W L))) : Prop :=
  (¬ArrayDimensionsAccepted dims.values →
    outcome = some (.error (.leaf (.dimensions (.argumentError "invalid Array dimensions")), before))) ∧
  (ArrayDimensionsAccepted dims.values → ∃ count : JInt .i64,
    count.val = ArrayDimensionProduct dims.values ∧
    if directOne then
      ArrayFinishMemoryCall element dims
        (newAsMemoryRefCtor dispatch.memory ⟨element.memoryType⟩ count before) outcome
    else
      (dispatch.newAsSelected before ⟨element.memoryType⟩ count = true →
        ArrayFinishReferenceCall element dims
          (dispatch.newAs ⟨element.memoryType⟩ count before) outcome) ∧
      (dispatch.newAsSelected before ⟨element.memoryType⟩ count = false →
        ArrayFinishMemoryCall element dims
          (newAsMemoryRefCtor dispatch.memory ⟨element.memoryType⟩ count before) outcome))

/-- Complete rank-one domain: all native signed counts, actual element/type
metadata, arbitrary heaps and selected methods. Independent field/freshness
invariants hold around user effects, and the concrete Base instantiation has
exact mathematical allocation/error behavior. Source: boot.jl:821-824. -/
def ArrayNative1Behavior : Prop :=
  ∀ (W L : Type) (dispatch : ArrayNativeDispatch W L) (element : ArrayNativeElement L)
    (m : JInt .i64) (world : ArrayNativeWorld W L),
    ArraySourceObservation dispatch true element ⟨[m], by simp only [List.length_cons,List.length_nil]; decide⟩ world
      (arrayNative1Ctor dispatch element m world) ∧
    ArrayOwnEffects element ⟨[m], by simp only [List.length_cons, List.length_nil]; decide⟩
      (arrayNative1Ctor (arrayTracedDispatch dispatch) element m (arrayCallStart world)) ∧
    ArrayInstalledObservation element ⟨[m], by simp only [List.length_cons, List.length_nil]; decide⟩ world
      (arrayNative1Ctor (arrayInstalledDispatch dispatch) element m world)

/-- Complete rank-two domain and arbitrary dispatch, including exact early
dimension rejection and all source-owned effects. Source: boot.jl:825-827. -/
def ArrayNative2Behavior : Prop :=
  ∀ (W L : Type) (dispatch : ArrayNativeDispatch W L) (element : ArrayNativeElement L)
    (m n : JInt .i64) (world : ArrayNativeWorld W L),
    ArraySourceObservation dispatch false element ⟨[m,n], by simp only [List.length_cons,List.length_nil]; decide⟩ world
      (arrayNative2Ctor dispatch element m n world) ∧
    ArrayOwnEffects element ⟨[m,n], by simp only [List.length_cons, List.length_nil]; decide⟩
      (arrayNative2Ctor (arrayTracedDispatch dispatch) element m n (arrayCallStart world)) ∧
    ArrayDimensionErrorFirst [m,n] world (arrayNative2Ctor dispatch element m n world) ∧
    ArrayInstalledObservation element ⟨[m,n], by simp only [List.length_cons, List.length_nil]; decide⟩ world
      (arrayNative2Ctor (arrayInstalledDispatch dispatch) element m n world)

/-- Complete rank-three domain and arbitrary dispatch, with original dimension
order and independent native-size mathematics. Source: boot.jl:828-830. -/
def ArrayNative3Behavior : Prop :=
  ∀ (W L : Type) (dispatch : ArrayNativeDispatch W L) (element : ArrayNativeElement L)
    (m n o : JInt .i64) (world : ArrayNativeWorld W L),
    ArraySourceObservation dispatch false element ⟨[m,n,o], by simp only [List.length_cons,List.length_nil]; decide⟩ world
      (arrayNative3Ctor dispatch element m n o world) ∧
    ArrayOwnEffects element ⟨[m,n,o], by simp only [List.length_cons, List.length_nil]; decide⟩
      (arrayNative3Ctor (arrayTracedDispatch dispatch) element m n o (arrayCallStart world)) ∧
    ArrayDimensionErrorFirst [m,n,o] world (arrayNative3Ctor dispatch element m n o world) ∧
    ArrayInstalledObservation element ⟨[m,n,o], by simp only [List.length_cons, List.length_nil]; decide⟩ world
      (arrayNative3Ctor (arrayInstalledDispatch dispatch) element m n o world)

/-- Every actual existing Array rank, including zero/one and all tuple sizes
permitted by its native layout. The UInt32 apply boundary preserves every
original dimension; no finite fuel or resource budget narrows the source.
Source: boot.jl:831-833; datatype.c:645-648,825-830; julia.h:2596-2599. -/
def ArrayNativeVarargBehavior : Prop :=
  ∀ (W L : Type) (dispatch : ArrayNativeDispatch W L) (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) (world : ArrayNativeWorld W L),
    arrayNativeSplatDimensions dims = dims.values ∧
    ArraySourceObservation dispatch false element dims world
      (arrayNativeVarargCtor dispatch element dims world) ∧
    ArrayOwnEffects element dims
      (arrayNativeVarargCtor (arrayTracedDispatch dispatch) element dims (arrayCallStart world)) ∧
    ArrayDimensionErrorFirst dims.values world (arrayNativeVarargCtor dispatch element dims world) ∧
    ArrayInstalledObservation element dims world
      (arrayNativeVarargCtor (arrayInstalledDispatch dispatch) element dims world)

/-- Return one actual outer constructor call with its inaccessible request
trace. Arbitrary returned values and errors keep their actual post-call state;
no source-owned Array allocation or result assertion is added. -/
def arrayRecordConstructor {W L : Type} (target : ArrayNativeType L)
    (dims : ArrayNativeDimensions)
    (action : ArrayNativeM W L (JuliaLean.base.expr.Value (ArrayNativeLeaf L))) :
    ArrayNativeM (ArrayCallTrace W L) L (JuliaLean.base.expr.Value (ArrayNativeLeaf L)) :=
  fun world =>
    let prior := world.external.2
    match action (arrayCallRawWorld world) with
    | none => none
    | some (.error (error, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          prior.lastReference, prior.events ++ [.arrayConstructor target dims]⟩
        some (.error (error, ⟨after.heap, (after.external.1, trace)⟩))
    | some (.ok (value, after)) =>
        let trace : ArrayCallTrace W L := ⟨after.external.2, after.external.1.cells,
          prior.lastReference, prior.events ++ [.arrayConstructor target dims]⟩
        some (.ok (value, ⟨after.heap, (after.external.1, trace)⟩))

/-- All user boundaries are instrumented, including the outer constructor
specialization and the known default body’s own generic callees. -/
def arrayTracedWrapperDispatch {W L : Type} (dispatch : ArrayWrapperDispatch W L) :
    ArrayWrapperDispatch (ArrayCallTrace W L) L where
  kernel := arrayTracedDispatch dispatch.kernel
  selected world target dims := dispatch.selected (arrayCallRawWorld world) target dims
  custom target dims := arrayRecordConstructor target dims (dispatch.custom target dims)

/-- Concrete installed Base selection at both the outer call and its callees.
Unused custom operations remain arbitrary, with no correctness assumptions. -/
def arrayInstalledWrapperDispatch {W L : Type} (dispatch : ArrayWrapperDispatch W L) :
    ArrayWrapperDispatch W L where
  kernel := arrayInstalledDispatch dispatch.kernel
  selected := fun _ _ _ => false
  custom := dispatch.custom

def arrayAliasProject {W L : Type} : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeAliasResult L × ArrayNativeWorld (ArrayCallTrace W L) L)) →
    Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeAliasResult L × ArrayNativeWorld W L))
  | none => none
  | some (.error (error, world)) => some (.error (error, arrayCallRawWorld world))
  | some (.ok (value, world)) => some (.ok (value, arrayCallRawWorld world))

def ArrayAliasEvents {W L : Type} (events : List (ArrayCallEvent L)) : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeAliasResult L × ArrayNativeWorld (ArrayCallTrace W L) L)) → Prop
  | none => True
  | some (.error (_, world)) => world.external.2.events = events
  | some (.ok (_, world)) => world.external.2.events = events

/-- On the default branch, the returned object obeys the complete selected
source-body protocol and source-owned heap effects; a custom-result origin tag
is forbidden. Rank1 picks its specialized body before the raw vararg method. -/
def ArrayAliasDefaultObservation {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) (before : ArrayNativeWorld W L)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeAliasResult L × ArrayNativeWorld (ArrayCallTrace W L) L))) : Prop :=
  match outcome with
  | none => ArraySourceObservation dispatch (decide (dims.values.length = 1)) element dims before none
  | some (.error (error, after)) =>
      ArrayOwnEffects element dims (some (.error (error, after))) ∧
      ArraySourceObservation dispatch (decide (dims.values.length = 1)) element dims before
        (some (.error (error, arrayCallRawWorld after)))
  | some (.ok (.array value, after)) =>
      ArrayOwnEffects element dims (some (.ok (value, after))) ∧
      ArraySourceObservation dispatch (decide (dims.values.length = 1)) element dims before
        (some (.ok (value, arrayCallRawWorld after)))
  | some (.ok (.customResult _, _)) => False

/-- One exact outer Array call on the original target and dimension sequence.
If a user method is selected, its entire arbitrary outcome is forwarded with
one request; otherwise the known default body's independent full protocol and
heap/field invariants apply. -/
def ArrayAliasObservation {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) (before : ArrayNativeWorld W L)
    (outcome : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeAliasResult L × ArrayNativeWorld (ArrayCallTrace W L) L))) : Prop :=
  let target : ArrayNativeType L := ⟨element, JInt.wrap .i64 (dims.values.length : Int)⟩
  if dispatch.selected before target dims then
    ArrayAliasEvents [.arrayConstructor target dims] outcome ∧
    match dispatch.custom target dims before with
    | none => outcome = none
    | some (.error error) => arrayAliasProject outcome = some (.error error)
    | some (.ok (value, after)) => arrayAliasProject outcome = some (.ok (.customResult value, after))
  else
    ArrayAliasDefaultObservation dispatch.kernel element dims before outcome

/-- Independent installed allocation/type/field observations through the
outer alias result. It cannot diverge or return a custom-origin value. -/
def ArrayAliasInstalledObservation {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) (before : ArrayNativeWorld W L) : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeAliasResult L × ArrayNativeWorld W L)) → Prop
  | none => False
  | some (.error error) => ArrayInstalledObservation element dims before (some (.error error))
  | some (.ok (.array value, after)) => ArrayInstalledObservation element dims before (some (.ok (value, after)))
  | some (.ok (.customResult _, _)) => False

/-- Combine full arbitrary-dispatch and concrete Base observations for an
actual public alias invocation, independently of its source implementation. -/
def ArrayAliasTwoObservations {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) (before : ArrayNativeWorld W L)
    (traced : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld (ArrayCallTrace W L) L)
      (ArrayNativeAliasResult L × ArrayNativeWorld (ArrayCallTrace W L) L)))
    (installed : Option (Except
      (JuliaLean.base.expr.Value (ArrayNativeException L) × ArrayNativeWorld W L)
      (ArrayNativeAliasResult L × ArrayNativeWorld W L))) : Prop :=
  ArrayAliasObservation dispatch element dims before traced ∧
    ArrayAliasInstalledObservation element dims before installed

/-- All nine complete tuple/fixed-rank/empty aliases, for every original type,
native dimension and world, every existing Array rank, and every actual custom
method outcome. The actual native self-splat retains the entire tuple. Fixed
inferred ranks0/1/2/3 are valid structural family applications; generic inferred
rank845 is deliberately outside this property because type formation can fail
for a tuple too large to embed as an Array.size field.
Source: boot.jl:835-844,847. -/
def ArrayNativeAliasesBehavior : Prop :=
  ∀ (W L : Type) (dispatch : ArrayWrapperDispatch W L) (element : ArrayNativeElement L)
    (m n o : JInt .i64) (dims : ArrayNativeDimensions) (world : ArrayNativeWorld W L),
    let traced := arrayTracedWrapperDispatch dispatch
    let installed := arrayInstalledWrapperDispatch dispatch
    let start := arrayCallStart world
    let d1 : ArrayNativeDimensions := ⟨[m], by simp only [List.length_cons,List.length_nil]; decide⟩
    let d2 : ArrayNativeDimensions := ⟨[m,n], by simp only [List.length_cons,List.length_nil]; decide⟩
    let d3 : ArrayNativeDimensions := ⟨[m,n,o], by simp only [List.length_cons,List.length_nil]; decide⟩
    let dz : ArrayNativeDimensions := ⟨[], by simp only [List.length_nil]; decide⟩
    let de : ArrayNativeDimensions := ⟨[JInt.wrap .i64 0], by simp only [List.length_cons,List.length_nil]; decide⟩
    (arrayNativeSelfSplatDimensions dims).values = dims.values ∧
    ArrayAliasTwoObservations dispatch element d1 world
      (arrayNativeTuple1Ctor traced element m start)
      (arrayNativeTuple1Ctor installed element m world) ∧
    ArrayAliasTwoObservations dispatch element d2 world
      (arrayNativeTuple2Ctor traced element (m,n) start)
      (arrayNativeTuple2Ctor installed element (m,n) world) ∧
    ArrayAliasTwoObservations dispatch element d3 world
      (arrayNativeTuple3Ctor traced element (m,n,o) start)
      (arrayNativeTuple3Ctor installed element (m,n,o) world) ∧
    ArrayAliasTwoObservations dispatch element dims world
      (arrayNativeTupleCtor traced element dims start)
      (arrayNativeTupleCtor installed element dims world) ∧
    ArrayAliasTwoObservations dispatch element d1 world
      (arrayNativeInferred1Ctor traced element m start)
      (arrayNativeInferred1Ctor installed element m world) ∧
    ArrayAliasTwoObservations dispatch element d2 world
      (arrayNativeInferred2Ctor traced element m n start)
      (arrayNativeInferred2Ctor installed element m n world) ∧
    ArrayAliasTwoObservations dispatch element d3 world
      (arrayNativeInferred3Ctor traced element m n o start)
      (arrayNativeInferred3Ctor installed element m n o world) ∧
    ArrayAliasTwoObservations dispatch element dz world
      (arrayNativeInferred0Ctor traced element start)
      (arrayNativeInferred0Ctor installed element world) ∧
    ArrayAliasTwoObservations dispatch element de world
      (arrayNativeEmptyVectorCtor traced element start)
      (arrayNativeEmptyVectorCtor installed element world)

/-- Independent todo entries for thirteen complete Array source bodies and
their concrete native/heap/raw-new and generic forwarding closure. -/
def arrayNativeEntries : List Entry := [
  { id := "boot-array-native-1", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}"]
    statement := "Rank-one undef construction preserves actual constructor/memoryref dispatch and arbitrary effects, then checks raw-new types and creates one fresh Array with the original size and actual reference. The installed Base branch has exact native allocation errors, initialization and cached-zero sharing."
    source := "base/boot.jl:821-824; src/genericmemory.c:55-102; src/datatype.c:1707-1742"
    notes := "Full count/type/world/custom domain, including wrong custom results, throws and divergence; separate concrete Base instantiation. Covers arrayNativeLiftMemory/New/reference classification and the completed memory helpers."
    status := .todo, thm := none, prop := ``ArrayNative1Behavior },
  { id := "boot-array-native-2", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}"]
    statement := "Rank-two construction rejects invalid native dimensions before any selected operation, preserves actual new_as_memoryref/custom effects, and stores the ordered dimensions and exact returned reference in one fresh Array; installed allocation and raw-new errors obey independent mathematical/state observations."
    source := "base/boot.jl:825-827; boot.jl:782-818; src/datatype.c:1707-1742"
    notes := "All native dimensions and arbitrary dispatch outcomes; covers concrete checked_dims lifting and installed/default new_as_memoryref composition."
    status := .todo, thm := none, prop := ``ArrayNative2Behavior },
  { id := "boot-array-native-3", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}"]
    statement := "Rank-three construction retains dimension order, early native dimension errors, arbitrary selected helper outcomes, raw-new checks and fresh Array/reference identity, with exact installed mathematical allocation behavior."
    source := "base/boot.jl:828-830; boot.jl:782-818; src/datatype.c:1707-1742"
    notes := "Full actual type, dimension, heap and custom dispatch domain; no callback correctness or return-type law."
    status := .todo, thm := none, prop := ``ArrayNative3Behavior },
  { id := "boot-array-native-vararg", juliaFile := "base/boot.jl"
    juliaFns := ["(self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}"]
    statement := "The selected vararg body retains every original native dimension across the actual UInt32 apply boundary, handles zero/scalar checked_dims dispatch, preserves arbitrary selected helper effects, and creates a fresh correctly typed Array or exact installed dimension/memory/new error."
    source := "base/boot.jl:831-833; src/datatype.c:645-648,825-830; src/julia.h:2596-2599"
    notes := "Actual Int64 tuple layout gives8*N<=2^32-1, so native apply count does not truncate actual inputs; this is a runtime representation invariant, not a resource budget. Covers arrayNativeSplatDimensions."
    status := .todo, thm := none, prop := ``ArrayNativeVarargBehavior },
  { id := "boot-array-native-aliases", juliaFile := "base/boot.jl"
    juliaFns := [
      "(self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T}",
      "(self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T}",
      "(self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T}",
      "(self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N}",
      "Array{T}(::UndefInitializer, m::Int) where {T}",
      "Array{T}(::UndefInitializer, m::Int, n::Int) where {T}",
      "Array{T}(::UndefInitializer, m::Int, n::Int, o::Int) where {T}",
      "Array{T}(::UndefInitializer, ::Tuple{}) where {T}",
      "(self::Type{Array{T, 1}})() where {T}"]
    statement := "Tuple/fixed-rank/empty aliases preserve the original target and exact ordered dimensions across native apply arity, forward every selected custom constructor outcome unchanged, and otherwise retain complete installed dimension/allocation/raw-new checks, fresh Array identity and shared reference values. Zero-rank allocation uses one element; empty vectors use a cached empty memory but a fresh Array."
    source := "base/boot.jl:835-844,847; exact call trace, complete arbitrary-callee outcome protocol and independent allocation/heap mathematics"
    notes := "Nine complete aliases. Actual Int64 tuple field-offset bound protects native arity. Generic inferred-rank845 remains blocked by additional type-formation layout errors; no partial845 implementation is present. Covers arrayNativeDefaultConstructor/Invoke/SelfSplatDimensions."
    status := .todo, thm := none, prop := ``ArrayNativeAliasesBehavior }
]

end JuliaLean.Proofs.base.boot.Models2Group1


namespace JuliaLean.Proofs.base.boot

/-- Additive batch-2 group-1 property registry. -/
def entriesModels2Group1 : List JuliaLean.Registry.Entry :=
  Models2Group1.entriesHeapMacros ++
  Models2Group1.entriesEarlyConversions ++
  Models2Group1.entriesBottomConstruction ++
  Models2Group1.entriesReusedConstructors ++
  Models2Group1.constructorEntries ++
  Models2Group1.entriesRemainingTyped ++
  Models2Group1.entriesIdentityObjects ++
  Models2Group1.entriesThreadState ++
  Models2Group1.typeVarEntries ++
  Models2Group1.genericConstructorEntries ++
  Models2Group1.lineNumberEntries ++
  Models2Group1.entriesDocsPrinting ++
  Models2Group1.entriesDimensions ++
  Models2Group1.bootstrapFailEntries ++
  Models2Group1.typedNamedTupleEntries ++
  Models2Group1.nativeConversionEntries ++
  Models2Group1.FloatConversion.entriesFloatConversions ++
  Models2Group1.entriesMetadata ++
  Models2Group1.entriesTypeNames ++
  Models2Group1.symbolBootstrapReuseEntries ++
  Models2Group1.tailReuseEntries ++
  Models2Group1.entriesExprConstructor ++
  Models2Group1.documentationEntries ++
  Models2Group1.entriesIOForwarding ++
  Models2Group1.Reflection.entriesReflection ++
  Models2Group1.AliasDispatch.entriesAliasDispatch ++
  Models2Group1.memoryNativeEntries ++
  Models2Group1.GenericForwarding.entriesGenericForwarding ++
  Models2Group1.entriesTypeNameUnionAll ++
  Models2Group1.entriesIOGlobals ++
  Models2Group1.PrintMany.entriesPrintMany ++
  Models2Group1.arrayNativeEntries

end JuliaLean.Proofs.base.boot
