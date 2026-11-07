import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.gmp
import JuliaLean.base.mpfr
import JuliaLean.base.irrationals
import JuliaLean.base.floatfuncs
/-!
# Model of `base/mathconstants.jl`

Julia f755f49a9e41380d7da126b3c1db9fe7f83dd027. Constants are the zero-field
Irrational singleton values created by the source macro. The generated analytic
MPFR constant kernels remain explicitly untranslated in `irrationals.lean`;
the golden-ratio BigFloat expression is executable using the MPFR model.
Methods for the known-constant union retain the generic integer, real, complex,
and number types of the Julia source and call the corresponding generic method.
-/
namespace JuliaLean.base.mathconstants
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.base.irrationals (Irrational)
abbrev M := JuliaLean.base.mpfr.M


/--
Julia source: base/mathconstants.jl:13-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@irrational π        pi
Base.@irrational ℯ        exp(big(1))
Base.@irrational γ        euler
Base.@irrational φ        (1+sqrt(big(5)))/2
Base.@irrational catalan  catalan

const _KnownIrrational = Union{
    typeof(π), typeof(ℯ), typeof(γ), typeof(φ), typeof(catalan)
}
```
-/
def π : Irrational "π" := ⟨⟩
def ℯ : Irrational "ℯ" := ⟨⟩
def γ : Irrational "γ" := ⟨⟩
def φ : Irrational "φ" := ⟨⟩
def catalan : Irrational "catalan" := ⟨⟩

inductive KnownIrrational where
  | pi | e | eulergamma | golden | catalan
  deriving DecidableEq, Repr

def KnownIrrational.symbol : KnownIrrational → String
  | .pi => "π" | .e => "ℯ" | .eulergamma => "γ" | .golden => "φ" | .catalan => "catalan"

def bigGolden (precision : Int) : M JuliaLean.base.mpfr.BigFloat :=
  JuliaLean.base.mpfr.withPrecision (fun (p : Int) (_ : Unit) => JInt.convert "Int64" .i64 p)
    (do
      let root ← JuliaLean.base.mpfr.sqrtBigInt (JuliaLean.base.gmp.ofInt 5)
      let numerator ← JuliaLean.base.mpfr.integerArithmetic .add (JInt.wrap .i64 1) root
      JuliaLean.base.mpfr.arithmeticInteger .div numerator (JInt.wrap .i64 2)) precision ()

/--
Julia source: base/mathconstants.jl:23-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{BigInt}(::_KnownIrrational)
    Base._throw_argument_error_irrational_to_rational_bigint()
end
Base.@assume_effects :foldable function Rational{T}(x::_KnownIrrational) where {T<:Integer}
    Base._irrational_to_rational(T, x)
end
Base.@assume_effects :foldable function (::Type{T})(x::_KnownIrrational, r::RoundingMode) where {T<:Union{Float32,Float64}}
    Base._irrational_to_float(T, x, r)
end
Base.@assume_effects :foldable function Base.rationalize(::Type{T}, x::_KnownIrrational; tol::Real=0) where {T<:Integer}
    Base._rationalize_irrational(T, x, tol)
end
Base.@assume_effects :foldable function Base.lessrational(rx::Rational, x::_KnownIrrational)
    Base._lessrational(rx, x)
end
```
-/
def rationalBigInt {R : Type} (_x : KnownIrrational) : M R :=
  JuliaLean.base.irrationals.throwRationalBigInt

def rational {R : Type} (callee : KnownIrrational → JuliaLean.base.irrationals.Run R)
    (x : KnownIrrational) := callee x

def floatWithRounding (T : JuliaLean.base.irrationals.IEEE32Or64)
    (callee : KnownIrrational → RoundingMode → M (FV T.ty))
    (x : KnownIrrational) (r : RoundingMode) := callee x r

def rationalize {Tol R : Type} (callee : KnownIrrational → Tol → M R)
    (x : KnownIrrational) (tol : Tol) := callee x tol

def lessRational {R : Type} (callee : R → KnownIrrational → M Bool)
    (rx : R) (x : KnownIrrational) := callee rx x

/--
Julia source: base/mathconstants.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
π, const pi = π
```
-/
def pi : Irrational "π" := π

/--
Julia source: base/mathconstants.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ℯ, const e = ℯ
```
-/
def e : Irrational "ℯ" := ℯ

/--
Julia source: base/mathconstants.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
γ, const eulergamma = γ
```
-/
def eulergamma : Irrational "γ" := γ

/--
Julia source: base/mathconstants.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
φ, const golden = φ
```
-/
def golden : Irrational "φ" := φ

/--
Julia source: base/mathconstants.jl:138-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for T in (AbstractIrrational, Rational, Integer, Number, Complex)
    Base.:^(::Irrational{:ℯ}, x::T) = exp(x)
end
Base.literal_pow(::typeof(^), ::Irrational{:ℯ}, ::Val{p}) where {p} = exp(p)

Base.log(::Irrational{:ℯ}) = 1 # use 1 to correctly promote expressions like log(x)/log(ℯ)
Base.log(::Irrational{:ℯ}, x::Number) = log(x)

Base.sin(::Irrational{:π}) = 0.0
Base.cos(::Irrational{:π}) = -1.0
Base.sincos(::Irrational{:π}) = (0.0, -1.0)
Base.tan(::Irrational{:π}) = 0.0
Base.cot(::Irrational{:π}) = -1/0
```
-/
def powE {T R : Type} (exp : T → Jl R) (_e : Irrational "ℯ") (x : T) : Jl R := exp x
def literalPowE {P R : Type} (exp : P → Jl R) (p : P) : Jl R := exp p

def logE (_e : Irrational "ℯ") : JInt .i64 := JInt.wrap .i64 1
def logBaseE {N R : Type} (log : N → Jl R) (_e : Irrational "ℯ") (x : N) := log x

def sinPi (_pi : Irrational "π") : FV .f64 := Fl.zero false
def cosPi (_pi : Irrational "π") : FV .f64 := Fl.roundRat (-1) 1 false
def sincosPi (_pi : Irrational "π") : FV .f64 × FV .f64 :=
  (Fl.zero false,Fl.roundRat (-1) 1 false)
def tanPi (_pi : Irrational "π") : FV .f64 := Fl.zero false
def cotPi (_pi : Irrational "π") : FV .f64 :=
  div_IEEEFloat (Fl.roundRat (-1) 1 false) (Fl.zero false)

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:1-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     Base.MathConstants
-- 
-- Module containing the mathematical constants.
-- See [`π`](@ref), [`ℯ`](@ref), [`γ`](@ref), [`φ`](@ref) and [`catalan`](@ref).
-- """
-- module MathConstants
-- 
-- export π, pi, ℯ, e, γ, eulergamma, catalan, φ, golden
-- 
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:38-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # aliases
-- """
--     π
--     pi
-- 
-- The constant pi.
-- 
-- Unicode `π` can be typed by writing `\\pi` then pressing tab in the Julia REPL, and in many editors.
-- 
-- See also: [`sinpi`](@ref), [`sincospi`](@ref), [`deg2rad`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> pi
-- π = 3.1415926535897...
-- 
-- julia> 1/2pi
-- 0.15915494309189535
-- ```
-- """
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:60-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     ℯ
--     e
-- 
-- The constant ℯ.
-- 
-- Unicode `ℯ` can be typed by writing `\\euler` and pressing tab in the Julia REPL, and in many editors.
-- 
-- See also: [`exp`](@ref), [`cis`](@ref), [`cispi`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> ℯ
-- ℯ = 2.7182818284590...
-- 
-- julia> log(ℯ)
-- 1
-- 
-- julia> ℯ^(im)π ≈ -1
-- true
-- ```
-- """
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:84-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     γ
--     eulergamma
-- 
-- Euler's constant.
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.MathConstants.eulergamma
-- γ = 0.5772156649015...
-- 
-- julia> dx = 10^-6;
-- 
-- julia> sum(-exp(-x) * log(x) for x in dx:dx:100) * dx
-- 0.5772078382499133
-- ```
-- """
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:103-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     φ
--     golden
-- 
-- The golden ratio.
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.MathConstants.golden
-- φ = 1.6180339887498...
-- 
-- julia> (2ans - 1)^2 ≈ 5
-- true
-- ```
-- """
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:120-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     catalan
-- 
-- Catalan's constant.
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.MathConstants.catalan
-- catalan = 0.9159655941772...
-- 
-- julia> sum(log(x)/(1+x^2) for x in 1:0.01:10^6) * 0.01
-- 0.9159466120554123
-- ```
-- """
-- catalan
-- 
-- # loop over types to prevent ambiguities for ^(::Number, x)
-- /Source

-- Untranslated: module declarations or documentation; generated analytic constant conversions are covered by the irrational-macro untranslated block.
-- UNTRANSLATED
-- Source: base/mathconstants.jl:151-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # module
-- /Source



section PiBindings
open JuliaLean.base.irrationals (IEEE32Or64 Irrational)
/-- The fixed precision chosen by `_irrational_to_float` calls the same
Integer constructor and the same external primitive in every rounding mode. -/
def bigPi256 (primitive : JuliaLean.base.irrationals.PiPrimitive) (_pi : Irrational "π")
    (mode : JuliaLean.base.mpfr.Mode) : JuliaLean.base.mpfr.M JuliaLean.base.mpfr.BigFloat :=
  JuliaLean.base.irrationals.constructPiInteger (JuliaLean.base.mpfr.bitsPrecision .i64) (fun _ mode => do
    JuliaLean.base.mpfr.applyPrimitive (JuliaLean.base.irrationals.pi256Primitive primitive (← JuliaLean.base.mpfr.readContext) mode))
    mode (JInt.lit .i64 256)


def irrationalToFloat (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (x : Irrational "π") (r : RoundingMode) :
    JuliaLean.base.mpfr.M (FV T.ty) :=
  JuliaLean.base.irrationals.irrationalToFloat T
    (fun x => do bigPi256 primitive x (JuliaLean.base.mpfr.roundingRaw (← JuliaLean.base.mpfr.readContext))) x r

def piFloatWithRounding (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (x : Irrational "π") (r : RoundingMode) :=
  irrationalToFloat primitive T x r


def knownFloatWithRounding (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (x : Irrational "π") (r : RoundingMode) :=
  irrationalToFloat primitive T x r


/-- Bindings of the generic comparison methods to mathematical π. -/
def ieeeLessPi (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (x : FV T.ty) (pi : Irrational "π") :=
  JuliaLean.base.irrationals.ieeeLess T (knownFloatWithRounding primitive T) x pi

def piLessIEEE (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (pi : Irrational "π") (y : FV T.ty) :=
  JuliaLean.base.irrationals.lessIEEE T (knownFloatWithRounding primitive T) pi y

def float16LessPi (primitive : JuliaLean.base.irrationals.PiPrimitive) (x : FV .f16) (pi : Irrational "π") :=
  JuliaLean.base.irrationals.float16Less (knownFloatWithRounding primitive .f32) x pi

def piLessFloat16 (primitive : JuliaLean.base.irrationals.PiPrimitive) (pi : Irrational "π") (y : FV .f16) :=
  JuliaLean.base.irrationals.lessFloat16 (knownFloatWithRounding primitive .f32) pi y

/-- Value projection for callers whose model records only an IEEE result.
The full state-preserving conversion is irrationalToFloat above. -/
def piDirectedValue (primitive : JuliaLean.base.irrationals.PiPrimitive) (T : IEEE32Or64) (state : JuliaLean.base.mpfr.Context) (r : RoundingMode) : FV T.ty :=
  JuliaLean.base.mpfr.toIEEE T.ty
    (JuliaLean.base.irrationals.pi256Primitive primitive state (JuliaLean.base.mpfr.roundingRaw state)).value r

/-- Concrete replacement for special.rem2pi's pure ltPi input. -/
def ltPi (primitive : JuliaLean.base.irrationals.PiPrimitive) (state : JuliaLean.base.mpfr.Context) (x : FV .f64) : Bool :=
  le_IEEEFloat x (piDirectedValue primitive .f64 state .Down)


end PiBindings

end JuliaLean.base.mathconstants

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
