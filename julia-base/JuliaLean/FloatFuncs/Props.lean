import JuliaLean.FloatFuncs.Round
import JuliaLean.FloatFuncs.Isapprox

/-!
Statements of the FloatFuncs properties that are proven in `FloatFuncs/Proof*.lean`.
`(n, d) = F64.toRat x` is the exact value `n / d` (`d > 0`) of a finite `x`.
-/

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

/-- `f` applied `n` times. -/
def iter (f : F64 → F64) : Nat → F64 → F64
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- `nextfloat(x, n)`: "The result of `n` iterative applications of `nextfloat` to `x` if
`n >= 0`, or `-n` applications of `prevfloat` if `n < 0`" (`base/float.jl:847-853`), and the
mirror statement for `prevfloat(x, n)` (`base/float.jl:865-871`), for every Float64 `x`
(NaN and infinities included) and every integer `n`. `nextfloat(x) = nextfloat(x, 1)` and
`prevfloat(x) = nextfloat(x, -1)` (`base/float.jl:863,879`). -/
def NextfloatIterate : Prop := ∀ (x : F64) (n : Nat),
  F64.nextfloat x n = iter (fun y => F64.nextfloat y 1) n x ∧
  F64.nextfloat x (-(n : Int)) = iter (fun y => F64.nextfloat y (-1)) n x ∧
  F64.prevfloat x n = iter (fun y => F64.nextfloat y (-1)) n x ∧
  F64.prevfloat x (-(n : Int)) = iter (fun y => F64.nextfloat y 1) n x

/-- `trunc(T, x)`: "converts the result to type `T`, throwing an `InexactError` if the
truncated value is not representable a `T`" (`base/rounding.jl:423-424`), for all ten
fixed-width integer types and every Float64 `x` (`base/float.jl:881-931`). -/
def TruncIntExact : Prop := ∀ (t : IntTy) (x : F64),
  F64.truncInt t x =
    (if F64.isfinite x = true ∧
        t.min ≤ (F64.toRat x).1.tdiv (F64.toRat x).2 ∧
        (F64.toRat x).1.tdiv (F64.toRat x).2 ≤ t.max
      then .ok (JInt.wrap t ((F64.toRat x).1.tdiv (F64.toRat x).2))
      else .error (.inexactError "round"))

/-- `T(x::Float64)` for a fixed-width integer type `T` returns the integer equal to `x`, and
throws `InexactError` exactly when `x` is not an integer in `T`'s range (`base/float.jl:895-927`;
`convert` semantics). -/
def IntConvertExact : Prop := ∀ (t : IntTy) (x : F64),
  F64.int t x =
    (if F64.isfinite x = true ∧ (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0 ∧
        t.min ≤ (F64.toRat x).1 / ((F64.toRat x).2 : Int) ∧
        (F64.toRat x).1 / ((F64.toRat x).2 : Int) ≤ t.max
      then .ok (JInt.wrap t ((F64.toRat x).1 / ((F64.toRat x).2 : Int)))
      else .error (.inexactError t.name))

/-- `round(x, r)` for finite Float64 `x` and each of the seven modes is the finite Float64
equal to the exact integer rounding of `x` under `r` (`base/rounding.jl:51-110` mode
definitions, `base/rounding.jl:337`), keeping the sign of `x` (so `round(-0.4) === -0.0`). -/
def RoundModesExact : Prop := ∀ (x : F64) (m : Mode), F64.isfinite x = true →
  F64.isfinite (roundF x m) = true ∧
  F64.signbit (roundF x m) = F64.signbit x ∧
  (F64.toRat (roundF x m)).1 =
    exactRound (F64.toRat x).1 (F64.toRat x).2 m * ((F64.toRat (roundF x m)).2 : Int)

/-- `isapprox(x, y; atol, rtol, nans)` on Float64 is symmetric in `x` and `y`, the
documented criterion `norm(x-y) <= max(atol, rtol*max(norm(x), norm(y)))`
(`base/floatfuncs.jl:166-170`) being symmetric. -/
def IsapproxSymmetric : Prop := ∀ (x y atol rtol : F64) (nans : Bool),
  isapproxF x y atol rtol nans = isapproxF y x atol rtol nans

/-- `isinteger(x)` is true exactly for finite integer-valued Float64 `x`
(`base/floatfuncs.jl:51`, `base/number.jl` docstring "Test whether x is numerically equal
to some integer"). -/
def IsintegerExact : Prop := ∀ x : F64,
  F64.isinteger x = (F64.isfinite x && (F64.toRat x).1 % ((F64.toRat x).2 : Int) == 0)

/-- `maxintfloat(Float64) = 9007199254740992.` (`base/floatfuncs.jl:34`) is "the smallest
positive integer-valued floating-point number n such that n+1 is not exactly
representable" (`base/floatfuncs.jl:27-28`): it equals 2^53, every integer 0..2^53 is a
Float64 value, and no Float64 equals 2^53+1. -/
def MaxintfloatSpec : Prop :=
  F64.toRat (F64.ofBits 0x4340000000000000) = ((2^53 : Int), 1) ∧
  (∀ k : Nat, k ≤ 2^53 → ∃ y : F64, F64.isfinite y = true ∧ (F64.toRat y).1 = k * (F64.toRat y).2) ∧
  (∀ y : F64, F64.isfinite y = true → (F64.toRat y).1 ≠ (2^53 + 1) * (F64.toRat y).2)

/-- `round(T, x, r)` for a fixed-width integer type `T`: RoundToZero uses the range-checked
method of `base/float.jl:888-919` (`F64.truncInt`); every other mode is
`_round_convert(T, round(x, r), x, r) = convert(T, round(x, r))` (`base/rounding.jl:485-491`). -/
def roundIntM (t : IntTy) (x : F64) : Mode → Jl (JInt t)
  | .ToZero => F64.truncInt t x
  | m => F64.int t (roundF x m)

/-- `round(T, x, r)` (also `floor(T, x)`, `ceil(T, x)`) returns the exact rounding of `x`
under `r` and throws `InexactError` exactly when it is not representable in `T`
(`base/rounding.jl:337-339`, `base/rounding.jl:454-455,471-472`), for the six modes other
than RoundToZero (covered by `TruncIntExact`). -/
def RoundIntExact : Prop := ∀ (t : IntTy) (x : F64) (m : Mode), m ≠ .ToZero →
  roundIntM t x m =
    (if F64.isfinite x = true ∧
        t.min ≤ exactRound (F64.toRat x).1 (F64.toRat x).2 m ∧
        exactRound (F64.toRat x).1 (F64.toRat x).2 m ≤ t.max
      then .ok (JInt.wrap t (exactRound (F64.toRat x).1 (F64.toRat x).2 m))
      else .error (.inexactError t.name))

end JuliaLean.FloatFuncs
