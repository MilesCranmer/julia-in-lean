import JuliaLean.BootCov.IntConv

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
