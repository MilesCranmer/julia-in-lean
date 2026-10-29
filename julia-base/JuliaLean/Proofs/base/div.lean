import JuliaLean.base.div
import JuliaLean.Registry.Types

/-!
# Properties of `base/div.jl`

These statements give the documented integer quotient, remainder, division-error, and wrapper
contracts for every `BitInteger` width. The expected quotient uses exact mathematical integers,
while the tested methods are the source models in `JuliaLean.base.div` instantiated with
`JuliaLean.base.int` operations.
-/

namespace JuliaLean.Proofs.base.div

open JuliaLean
open JuliaLean.base.div
open JuliaLean.base.float
open JuliaLean.Registry

private def absInt (x : Int) : Int := if x < 0 then -x else x

private def sameSign (x y : Int) : Bool := (x < 0) = (y < 0)

private def awayFromZero (x y q : Int) : Int :=
  q + if sameSign x y then 1 else -1

/-- Exact mathematical quotient rounding for integer inputs; division by zero is excluded by the
specifications below. -/
def roundedIntegerQuotient (x y : Int) (mode : RoundingMode) : Int :=
  if y = 0 then 0 else
    let q := x.tdiv y
    let r := x.tmod y
    match mode with
    | .ToZero => q
    | .Down => x.fdiv y
    | .Up => -((-x).fdiv y)
    | .FromZero => if sameSign x y then -((-x).fdiv y) else x.fdiv y
    | .Nearest | .NearestTiesAway | .NearestTiesUp =>
        let twiceRemainder := 2 * absInt r
        let divisorMagnitude := absInt y
        if twiceRemainder > divisorMagnitude then awayFromZero x y q
        else if twiceRemainder < divisorMagnitude then q
        else if mode = .Nearest then
          if q.tmod 2 = 0 then q else awayFromZero x y q
        else if mode = .NearestTiesAway then awayFromZero x y q
        else if sameSign x y then awayFromZero x y q else q

private def divisionError {t : IntTy} (x y : JInt t) : Prop :=
  y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)

private def remainderError {t : IntTy} (x y : JInt t) (mode : RoundingMode) : Prop :=
  y.val = 0 ∨
    (t.signed = true ∧ x.val = t.min ∧ y.val = -1 ∧
      (mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp))

/-- `div` returns the mathematical quotient rounded in the requested mode, or `DivideError` for
zero divisors and signed `typemin / -1`, for every `BitInteger` type. -/
def BitIntegerDivisionCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (divisionError x y → divBitIntegerMode x y mode = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ q : JInt t,
        divBitIntegerMode x y mode = .ok q ∧
        q.val = roundedIntegerQuotient x.val y.val mode)

/-- `rem` is the exact dividend minus divisor times the quotient rounded in the selected mode;
zero divisors and nearest-mode signed `typemin / -1` raise `DivideError`. -/
def BitIntegerRemainderCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (remainderError x y mode → remBitIntegerMode x y mode = .error .divideError) ∧
    (¬ remainderError x y mode →
      ∃ r : JInt t,
        remBitIntegerMode x y mode = .ok r ∧
        r.val = x.val - y.val * roundedIntegerQuotient x.val y.val mode)

/-- The documented `divrem` pair agrees with separate `div` and `rem` calls for all seven Julia
rounding modes, with errors preserved. -/
def BitIntegerDivremProjection : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    divremBitIntegerMode x y mode = do
      let q ← divBitIntegerMode x y mode
      let r ← remBitIntegerMode x y mode
      pure (q, r)

/-- `divrem` returns the correctly rounded quotient and exact remainder at every fixed-width
integer width, or preserves `DivideError` for invalid divisions. -/
def BitIntegerDivremCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    (divisionError x y →
      divremBitIntegerMode x y mode = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ q r : JInt t,
        divremBitIntegerMode x y mode = .ok (q, r) ∧
        q.val = roundedIntegerQuotient x.val y.val mode ∧
        r.val = x.val - y.val * q.val)

/-- Truncating, floored, ceiled, and nearest integer division return the exact rounded quotient at
every `BitInteger` width; `fld1` retains its documented `cld` result. -/
def BitIntegerFloorCeilingCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    (divisionError x y →
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fld1BitInteger x y = .error .divideError) ∧
    (¬ divisionError x y →
      ∃ f c : JInt t,
        fldBitInteger x y = .ok f ∧ f.val = x.val.fdiv y.val ∧
        cldBitInteger x y = .ok c ∧ c.val = -((-x.val).fdiv y.val) ∧
        fld1BitInteger x y = .ok c)

/-- `fldmod` returns the same floored quotient and modulo as its documented `(fld, mod)` pair,
including `DivideError` at zero and signed `typemin / -1`. -/
def BitIntegerFldmodCorrect : Prop :=
  ∀ (t : IntTy) (x y : JInt t),
    fldmodBitInteger x y = do
      let q ← fldBitInteger x y
      let r ← (if t.signed then JuliaLean.base.int.mod_BitSigned fldBitInteger x y
               else JuliaLean.base.int.mod_Unsigned x y)
      pure (q, r)

/-- Division and `divrem` raise `DivideError` for every zero divisor and for signed
`typemin / -1`; truncating, floored, ceiled, and directed remainder retain their documented
zero-remainder behavior at `typemin / -1`. -/
def BitIntegerDivisionErrorCases : Prop :=
  (∀ (t : IntTy) (x y : JInt t) (mode : RoundingMode),
    y.val = 0 →
      divBitIntegerMode x y mode = .error .divideError ∧
      remBitIntegerMode x y mode = .error .divideError ∧
      divremBitIntegerMode x y mode = .error .divideError ∧
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fldmodBitInteger x y = .error .divideError) ∧
  (∀ (t : IntTy) (x y : JInt t),
    t.signed = true → x.val = t.min → y.val = -1 →
      (∀ mode, divBitIntegerMode x y mode = .error .divideError ∧
        divremBitIntegerMode x y mode = .error .divideError) ∧
      fldBitInteger x y = .error .divideError ∧
      cldBitInteger x y = .error .divideError ∧
      fldmodBitInteger x y = .error .divideError ∧
      remBitIntegerMode x y .ToZero = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .Down = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .Up = .ok (JuliaLean.base.int.lit t 0) ∧
      remBitIntegerMode x y .FromZero = .ok (JuliaLean.base.int.lit t 0) ∧
      (∀ mode, mode = .Nearest ∨ mode = .NearestTiesAway ∨ mode = .NearestTiesUp →
        remBitIntegerMode x y mode = .error .divideError))

private def remainderValuesAgree {q r m : IntTy}
    (pair : JuliaLean.Jl (JInt q × JInt r)) (modValue : JuliaLean.Jl (JInt m)) : Prop :=
  ∀ (quotient : JInt q) (remainder : JInt r) (modulus : JInt m),
    pair = .ok (quotient, remainder) → modValue = .ok modulus →
    remainder.val = modulus.val

/-- The source `fldmod` result and the source `base/int.jl` `mod` result have the same mathematical
remainder for every pair of distinct same-signedness types and every mixed signed/unsigned pair. -/
def BitIntegerMixedFldmodConsistency : Prop :=
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = u.signed → s ≠ u →
    remainderValuesAgree (fldmodMixedSameSign x y) (modMixedSameSign x y)) ∧
  (∀ (s u : IntTy) (x : JInt s) (y : JInt u),
    s.signed = true → u.signed = false →
    remainderValuesAgree (fldmodMixedSignedUnsigned x y) (modMixedSignedUnsigned x y)) ∧
  (∀ (u s : IntTy) (x : JInt u) (y : JInt s),
    u.signed = false → s.signed = true →
    remainderValuesAgree (fldmodMixedUnsignedSigned x y) (modMixedUnsignedSigned x y))

/-! Nothing to promise: div(::Bool,::Bool,::RoundingMode)@422: forwards to ordinary Bool division.
Nothing to promise: generated div(::Bool,::Bool,::RoundingMode)@424-426: forwards to ordinary Bool division.
Nothing to promise: div(::Bool,::Bool,nearest mode)@427: forwards to ordinary Bool division. -/

/-- The float `mod` method returns a value without throwing; this adapter supplies the `Jl` result
expected by the source `rem` model. -/
def floatModJl {T : FTy} (x y : FV T) : JuliaLean.Jl (FV T) :=
  .ok (JuliaLean.base.float.mod_AbstractFloat x y)

/-- For finite `Float64` `x` and positive finite `y`, the documented RoundDown remainder lies in
`[0,y)`. This retains the existing runtime counterexample for the later proof worker. -/
def RoundDownFloatRemainderBound : Prop :=
  ∀ (x y : JuliaLean.base.float.FV .f64),
    JuliaLean.base.float.isfinite_callee x = true →
    JuliaLean.base.float.isfinite_callee y = true →
    JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float .f64) y = true →
    ∃ r : JuliaLean.base.float.FV .f64,
      JuliaLean.base.div.rem_Down floatModJl x y = .ok r ∧
      JuliaLean.base.float.le_float (JuliaLean.base.float.zero_float .f64) r = true ∧
      JuliaLean.base.float.lt_float r y = true

end JuliaLean.Proofs.base.div

namespace JuliaLean.Proofs.base.div

open JuliaLean.base.div
open JuliaLean.base.float
open JuliaLean.Registry


def entries : List Entry := [
  { id := "float-rem-down-bound", juliaFile := "base/div.jl",
    juliaFns := ["rem(::Float64,::Float64,RoundDown)"],
    statement := "For finite x and positive finite y, RoundDown remainder lies in [0,y).",
    source := "rem docstring; base/div.jl:95-97", status := .todo,
    prop := ``RoundDownFloatRemainderBound },
  { id := "intarith-division-fldmod-consistency", juliaFile := "base/div.jl",
    juliaFns := ["fldmod", "mod", "divrem(::Integer,::Integer,::typeof(RoundDown))"],
    statement := "The remainder from fldmod equals mod for all mixed fixed-width integer inputs.",
    source := "fldmod docstring and mixed mod methods; base/div.jl:379-387; base/int.jl:342-352",
    status := .todo, prop := ``BitIntegerMixedFldmodConsistency },
  { id := "floatintcov-divrem-roundup-typemin", juliaFile := "base/div.jl",
    juliaFns := ["divrem(::Integer,::Integer,RoundUp)", "div(::Integer,::Integer,RoundUp)",
      "rem(::Integer,::Integer,RoundUp)"],
    statement := "For every BitInteger width and rounding mode, divrem agrees with the pair of separate div and rem calls, including typemin and zero-divisor errors.",
    source := "divrem docstring; base/div.jl:255-262", status := .todo,
    prop := ``BitIntegerDivremProjection },
  { id := "div-bitinteger-divrem-reconstruction", juliaFile := "base/div.jl",
    juliaFns := ["divrem(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width and rounding mode, divrem returns the rounded integer quotient and exact x - q*y remainder, or DivideError for zero divisors and signed typemin / -1.",
    source := "divrem docstring; base/div.jl:255-262,290-373", status := .todo,
    prop := ``BitIntegerDivremCorrect },
  { id := "div-bitinteger-rounded-quotient", juliaFile := "base/div.jl",
    juliaFns := ["div(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, div returns x/y rounded by the requested mode; zero divisors and signed typemin / -1 raise DivideError.",
    source := "div docstring; base/div.jl:5-21", status := .todo,
    prop := ``BitIntegerDivisionCorrect },
  { id := "div-bitinteger-remainder-equation", juliaFile := "base/div.jl",
    juliaFns := ["rem(::BitInteger,::BitInteger,::RoundingMode)"],
    statement := "For every BitInteger width, rem is the exact x - y*q remainder for the quotient rounded by the selected mode, with DivideError for zero divisors and nearest-mode signed typemin / -1.",
    source := "rem docstring; base/div.jl:79-108", status := .todo,
    prop := ``BitIntegerRemainderCorrect },
  { id := "div-bitinteger-directed-wrapper-correct", juliaFile := "base/div.jl",
    juliaFns := ["fld", "cld", "fld1", "div(::BitInteger,::BitInteger,RoundDown)",
      "div(::BitInteger,::BitInteger,RoundUp)"],
    statement := "For every BitInteger width, fld and cld return the exact floor and ceiling quotients, fld1 returns cld, and signed typemin / -1 raises DivideError.",
    source := "fld and cld docstrings; base/div.jl:151-156,198-203,245-250,458-474", status := .todo,
    prop := ``BitIntegerFloorCeilingCorrect },
  { id := "div-bitinteger-fldmod-contract", juliaFile := "base/div.jl",
    juliaFns := ["fldmod(::BitInteger,::BitInteger)", "fld(::BitInteger,::BitInteger)",
      "mod(::BitInteger,::BitInteger)"],
    statement := "For every BitInteger width, fldmod equals the pair (fld(x,y), mod(x,y)), preserving division errors.",
    source := "fldmod docstring; base/div.jl:379-385", status := .todo,
    prop := ``BitIntegerFldmodCorrect },
  { id := "div-bitinteger-division-error-cases", juliaFile := "base/div.jl",
    juliaFns := ["div", "rem", "divrem", "fld", "cld", "fldmod"],
    statement := "All rounding-mode divisions, divrem, fld, cld, and fldmod raise DivideError on zero divisors and on signed typemin / -1; truncating and directed remainders at typemin / -1 remain zero.",
    source := "checked BitInteger division contract; base/div.jl:127-138,273-325,391-474", status := .todo,
    prop := ``BitIntegerDivisionErrorCases }
]

end JuliaLean.Proofs.base.div
