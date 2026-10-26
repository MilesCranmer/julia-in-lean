import JuliaLean.MathCov.Fmt
import JuliaLean.FloatFuncs.Round

/-!
Models of the methods in `base/mathconstants.jl` at Julia master `bbfa0ce4150`.
The irrational-number conversion primitives are parameters because their implementations
live in `base/irrationals.jl`; these methods only select and forward to them.
-/

namespace JuliaLean.MathCov.MathConstants

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP

inductive KnownIrrational where
  | pi | e | gamma | golden | catalan
  deriving Repr, BEq, DecidableEq

/-- `Rational{BigInt}(::_KnownIrrational)`; `base/mathconstants.jl:23-25`. -/
def rationalBigInt (_x : KnownIrrational) : Jl Unit :=
  .error (.argumentError "irrational cannot be converted to Rational{BigInt}")

/-- `Rational{T}(x::_KnownIrrational)`; `base/mathconstants.jl:26-28`. -/
def rationalInt {α : Type} (irrationalToRational : KnownIrrational → Jl α)
    (x : KnownIrrational) : Jl α := irrationalToRational x

/-- `T(x::_KnownIrrational, r)`; `base/mathconstants.jl:29-31`. -/
def irrationalFloat {α : Type} (convert : KnownIrrational → FloatFuncs.Mode → α)
    (x : KnownIrrational) (r : FloatFuncs.Mode) : α := convert x r

/-- `rationalize(T, x::_KnownIrrational; tol)`; `base/mathconstants.jl:32-34`. -/
def rationalizeIrrational {α β : Type} (rationalize : KnownIrrational → β → α)
    (x : KnownIrrational) (tol : β) : α := rationalize x tol

/-- `lessrational(rx, x::_KnownIrrational)`; `base/mathconstants.jl:35-37`. -/
def lessRational {α : Type} (less : α → KnownIrrational → Bool)
    (rx : α) (x : KnownIrrational) : Bool := less rx x

/-- `ℯ^x = exp(x)` and the generated five operand-type methods; `base/mathconstants.jl:137-140`. -/
def ePow {α : Type} (exp : α → α) (x : α) : α := exp x

/-- `literal_pow(^, ℯ, Val(p)) = exp(p)`; `base/mathconstants.jl:141`. -/
def eLiteralPow {α : Type} (exp : Int → α) (p : Int) : α := exp p

/-- `log(ℯ) = 1`; `base/mathconstants.jl:143`. -/
def logE : Int := 1

/-- `log(ℯ, x) = log(x)`; `base/mathconstants.jl:144`. -/
def logBaseE {α : Type} (log : α → α) (x : α) : α := log x

/-- Exact trigonometric values at the irrational object `π`; `base/mathconstants.jl:146-150`. -/
def sinPi : FV .f64 := zero .f64
def cosPi : FV .f64 := neg (one .f64)
def sincosPi : FV .f64 × FV .f64 := (sinPi, cosPi)
def tanPi : FV .f64 := zero .f64
def cotPi : FV .f64 := inf .f64 true

end JuliaLean.MathCov.MathConstants
