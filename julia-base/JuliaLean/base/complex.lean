import JuliaLean.Core
import JuliaLean.Float.Extras
import JuliaLean.Promotion.IEEE

/-!
# Model of `base/complex.jl`

Typed source-mirrored model of `base/complex.jl` at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform (`Int === Int64`).
Every method in `base/complex.jl` has a distinct typed Lean definition preceded by its
verbatim Julia source.

* `Complex T` is the parametric struct `Complex{T<:Real}`.
* `ComplexF64`, `ComplexF32`, and `ComplexF16` are `Complex F64`, `Complex (Fl single)`,
  and `Complex (Fl half)`.
* Fixed-width integer components use `JInt t` (`JuliaLean.Core`); binary64 components use
  `F64` (`JuliaLean.Float`).
* Generic methods over `T<:Real` or `Complex{T}` are parameterized by `T` and the scalar
  interface operations of `T`, with concrete instances provided for `F64`, `JInt t`, and `Bool`.
-/

set_option linter.unusedVariables false

namespace JuliaLean.base.complex

open JuliaLean JuliaLean.Float JuliaLean.Promotion

/-! ## Helper types and scalar interfaces -/

/-- Type-level representation of real types `T`, `Complex{T}`, and `Union{}`. -/
inductive ComplexTy (R : Type) where
  | real (t : R)
  | complex (t : R)
  | bottom
  deriving DecidableEq, Repr, Inhabited

/-- Value of `Union{T, Complex{T}}`, retaining whether the runtime argument is a `Real` or a `Complex`. -/
inductive RealOrComplex (R C : Type) where
  | real (x : R)
  | complex (z : C)
  deriving DecidableEq, Repr, Inhabited

/-- Operations of `x_` used by `power_by_squaring` (`base/intfuncs.jl:399-442`). -/
structure MulOps (α : Type) where
  mul : α → α → α
  one : α
  isone : α → Bool
  neg : α → α

/-- `trailing_zeros(p)` for positive `p`; `fuel ≥ 64` covers every 64-bit integer. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n != 0 && n % 2 == 0 then trailingZeros fuel (n / 2) + 1 else 0

/-- `while (t -= 1) >= 0; x = mul(x, x); end` run `k` times (`base/intfuncs.jl:436-438`). -/
def squareN {α : Type} (mul : α → α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => squareN mul k (mul x x)

/-- The outer loop `while p > 0` of `power_by_squaring` (`base/intfuncs.jl:433-440`). -/
def pbsLoop {α : Type} (mul : α → α → α) : Nat → α → α → Nat → α
  | 0, _, y, _ => y
  | fuel + 1, x, y, p =>
    if p = 0 then y
    else
      let t := trailingZeros 64 p + 1
      let x := squareN mul t x
      pbsLoop mul fuel x (mul y x) (p >>> t)

/-- `power_by_squaring(x_, p)` (`base/intfuncs.jl:399-442`). -/
def power_by_squaring {α : Type} (ops : MulOps α) (x : α) (p : JInt .i64) : Jl α :=
  let xsq := ops.mul x x
  if p.val = 1 then .ok x
  else if p.val = 0 then .ok ops.one
  else if p.val = 2 then .ok xsq
  else if p.val < 0 then
    if ops.isone x then .ok x
    else if ops.isone (ops.neg x) then .ok (if p.val % 2 = 0 then ops.one else x)
    else .error (.domainError "Cannot raise an integer x to a negative power")
  else
    let n := p.val.toNat
    let t := trailingZeros 64 n + 1
    let x1 := if t - 1 > 0 then xsq else x
    let x2 := squareN ops.mul (t - 2) x1
    .ok (pbsLoop ops.mul 64 x2 x2 (n >>> t))

/-! Binary64 constants and elementary helpers from earlier Base files (`float.jl`, `floatfuncs.jl`, `number.jl`, `bool.jl`, `math.jl`). -/
namespace Fl64

def pzero : F64 := F64.zero false
def nzero : F64 := F64.zero true
def two : F64 := F64.ofInt 2
def half : F64 := F64.ofBits 0x3fe0000000000000
def inf : F64 := F64.inf false
def ninf : F64 := F64.inf true
def pi : F64 := F64.ofBits 0x400921fb54442d18

/-- `copysign(x::Float64, y::Float64)` (`base/floatfuncs.jl:5`). -/
def copysign (x y : F64) : F64 :=
  F64.ofBits (F64.toBits (F64.abs x) + if F64.signbit y then 2^63 else 0)

/-- `flipsign(x::Float64, y::Float64)` (`base/floatfuncs.jl:10`). -/
def flipsign (x y : F64) : F64 := if F64.signbit y then F64.neg x else x

/-- `sign(x::Real)` (`base/number.jl:212`). -/
def sign (x : F64) : F64 :=
  if F64.lt x pzero then F64.neg F64.one
  else if F64.lt pzero x then F64.one else x

/-- `max(x::Float64, y::Float64)` (`base/math.jl:839`). -/
def max (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt x y then y
  else if F64.lt y x then x
  else if F64.signbit x then y else x

/-- `x * y` for `x::Bool`, `y::Float64` (`base/bool.jl:161-164`). -/
def mulBool (b : Bool) (y : F64) : F64 := if b then y else copysign pzero y

/-- `y * x` for `y::Float64`, `x::Bool` (`base/bool.jl:165`). -/
def mulBoolRight (y : F64) (b : Bool) : F64 := if b then y else copysign pzero y

/-- `eps(Float64)` (`base/float.jl:981`). -/
def eps : F64 := F64.eps

/-- `_hypot(x::Float64, y::Float64)` with hardware `fma` (`base/math.jl:732-786`). -/
def hypot (x y : F64) : Jl F64 := do
  let axu := F64.abs x
  let ayu := F64.abs y
  let ax := F64.div axu F64.one
  let ay := F64.div ayu F64.one
  if F64.isinf ax || F64.isinf ay then return inf
  let (axu, ax, ay) := if F64.lt ax ay then (ayu, ay, ax) else (axu, ax, ay)
  let r ← F64.sqrt (F64.div eps two)
  if F64.le ay (F64.mul ax r) then return axu
  let sfm ← F64.sqrt F64.floatmin
  let shm ← F64.sqrt (F64.div F64.floatmax two)
  let scale := F64.mul eps sfm
  let (ax, ay, scale) :=
    if F64.lt shm ax then (F64.mul ax scale, F64.mul ay scale, F64.div F64.one scale)
    else if F64.lt ay sfm then (F64.div ax scale, F64.div ay scale, scale)
    else (ax, ay, F64.one)
  let h ← F64.sqrt (F64.muladd ax ax (F64.mul ay ay))
  let hsquared := F64.mul h h
  let axsquared := F64.mul ax ax
  let corr := F64.sub
    (F64.add (F64.fma (F64.neg ay) ay (F64.sub hsquared axsquared)) (F64.fma h h (F64.neg hsquared)))
    (F64.fma ax ax (F64.neg axsquared))
  let h := F64.sub h (F64.div corr (F64.mul two h))
  return F64.mul (F64.mul h scale) F64.one

end Fl64

/-- `Bool` arithmetic primitives from `base/bool.jl`. -/
def add_Bool_Bool (x y : Bool) : JInt .i64 :=
  JInt.lit .i64 ((if x then 1 else 0) + (if y then 1 else 0))

def sub_Bool_Bool (x y : Bool) : JInt .i64 :=
  JInt.lit .i64 ((if x then 1 else 0) - (if y then 1 else 0))

def neg_Bool_val (x : Bool) : JInt .i64 :=
  JInt.lit .i64 (if x then -1 else 0)

def mul_Bool_Bool (x y : Bool) : Bool := x && y

def promote_Int_Bool (x : JInt .i64) (y : Bool) : JInt .i64 × JInt .i64 :=
  (x, JInt.lit .i64 (if y then 1 else 0))

def promote_Bool_Int (x : Bool) (y : JInt .i64) : JInt .i64 × JInt .i64 :=
  (JInt.lit .i64 (if x then 1 else 0), y)

/-- Scalar operations for generic float/analytic methods in `base/complex.jl`. -/
structure FloatOps (T : Type) where
  zero : T
  nzero : T
  one : T
  two : T
  half : T
  inf : T
  ninf : T
  nan : T
  pi : T
  floatmin : T
  floatmax : T
  eps : T
  epsOf : T → T
  ofInt : Int → T
  isnan : T → Bool
  isinf : T → Bool
  isfinite : T → Bool
  iszero : T → Bool
  isone : T → Bool
  isinteger : T → Bool
  toInt : T → Jl (JInt .i64)
  signbit : T → Bool
  eq : T → T → Bool
  lt : T → T → Bool
  le : T → T → Bool
  isequal : T → T → Bool
  identical : T → T → Bool
  pos : T → T
  neg : T → T
  abs : T → T
  sign : T → T
  copysign : T → T → T
  flipsign : T → T → T
  max : T → T → T
  add : T → T → T
  sub : T → T → T
  mul : T → T → T
  div : T → T → T
  muladd : T → T → T → T
  inv : T → T
  pow : T → T → T
  sqrt : T → T
  hypot : T → T → T
  exp : T → T
  expm1 : T → T
  exp2 : T → T
  exp10 : T → T
  log : T → T
  log1p : T → T
  sin : T → T
  cos : T → T
  tan : T → T
  asin : T → T
  acos : T → T
  atan : T → T
  atan2 : T → T → T
  sincos : T → T × T
  sincospi : T → T × T
  sinpi : T → T
  cospi : T → T
  sinh : T → T
  cosh : T → T
  tanh : T → T
  asinh : T → T
  acosh : T → T
  atanh : T → T
  nextfloat : T → T
  prevfloat : T → T
  ldexp : T → Int → T
  exponent : T → Int

/-! ## Struct `Complex`, `im`, and type aliases (lines 1-57) -/

/--
Julia source: base/complex.jl:1-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
    Complex{T<:Real} <: Number

Complex number type with real and imaginary part of type `T`.

`ComplexF16`, `ComplexF32` and `ComplexF64` are aliases for
`Complex{Float16}`, `Complex{Float32}` and `Complex{Float64}` respectively.

See also [`Real`](@ref), [`complex`](@ref), [`real`](@ref).
"""
struct Complex{T<:Real} <: Number
    re::T
    im::T
end
```
-/
@[ext] structure Complex (T : Type) where
  re : T
  im : T
  deriving DecidableEq, Repr, Inhabited

/--
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex(x::Real, y::Real) = Complex(promote(x,y)...)
```
-/
def Complex_Real_Real {A B P : Type} (promote : A → B → P × P) (x : A) (y : B) : Complex P :=
  let (re, im) := promote x y
  ⟨re, im⟩

/--
Julia source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex(x::Real) = Complex(x, zero(x))
```
-/
def Complex_Real {T : Type} (zero : T → T) (x : T) : Complex T :=
  ⟨x, zero x⟩

/--
Julia source: base/complex.jl:19-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    im

The imaginary unit.

See also [`imag`](@ref), [`angle`](@ref), [`complex`](@ref).

# Examples
```jldoctest
julia> im * im
-1 + 0im

julia> (2.0 + 3im)^2
-5.0 + 12.0im
```
"""
const im = Complex(false, true)
````
-/
def im : Complex Bool := ⟨false, true⟩

/--
Julia source: base/complex.jl:37-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const ComplexF64  = Complex{Float64}
```
-/
abbrev ComplexF64 := Complex F64

/--
Julia source: base/complex.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ComplexF32  = Complex{Float32}
```
-/
abbrev ComplexF32 := Complex (Fl single)

/--
Julia source: base/complex.jl:40-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ComplexF16  = Complex{Float16}

```
-/
abbrev ComplexF16 := Complex (Fl half)

/--
Julia source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
```
-/
def Complex_T_Real {T A : Type} (convert : A → T) (zeroT : T) (x : A) : Complex T :=
  ⟨convert x, zeroT⟩

/--
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
```
-/
def Complex_T_Complex {T A : Type} (convert : A → T) (z : Complex A) : Complex T :=
  ⟨convert z.re, convert z.im⟩

/--
Julia source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(z::Complex) where {T<:Real} =
    isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
```
-/
def Type_T_Complex {T A : Type} (isreal : Complex A → Bool) (convertT : A → Jl T)
    (nameofT : String) (z : Complex A) : Jl T :=
  if isreal z then convertT z.re else .error (.inexactError nameofT)

/--
Julia source: base/complex.jl:46-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

Complex(z::Complex) = z
```
-/
def Complex_Complex {T : Type} (z : Complex T) : Complex T := z

/--
Julia source: base/complex.jl:48-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real} =
    Complex{promote_type(T,S)}
```
-/
def promote_rule_Complex_Real {R : Type} (promote_type : R → R → R) (T S : R) : ComplexTy R :=
  .complex (promote_type T S)

/--
Julia source: base/complex.jl:51-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real} =
    Complex{promote_type(T,S)}
```
-/
def promote_rule_Complex_Complex {R : Type} (promote_type : R → R → R) (T S : R) : ComplexTy R :=
  .complex (promote_type T S)

/--
Julia source: base/complex.jl:53-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

widen(::Type{Complex{T}}) where {T} = Complex{widen(T)}
```
-/
def widen_Type_Complex {R W : Type} (widenT : R → W) (T : R) : ComplexTy W :=
  .complex (widenT T)

/--
Julia source: base/complex.jl:55-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

float(::Type{Complex{T}}) where {T<:AbstractFloat} = Complex{T}
```
-/
def float_Type_Complex_AbstractFloat {F : Type} (T : F) : ComplexTy F :=
  .complex T

/--
Julia source: base/complex.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{Complex{T}}) where {T} = Complex{float(T)}
```
-/
def float_Type_Complex {R F : Type} (floatT : R → F) (T : R) : ComplexTy F :=
  .complex (floatT T)

/--
Julia source: base/complex.jl:58-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    real(z)

Return the real part of the complex number `z`.

See also [`imag`](@ref), [`reim`](@ref), [`complex`](@ref), [`isreal`](@ref), [`Real`](@ref).

# Examples
```jldoctest
julia> real(1 + 3im)
1
```
"""
real(z::Complex) = z.re
````
-/
def real_Complex {T : Type} (z : Complex T) : T := z.re

/--
Julia source: base/complex.jl:73-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    imag(z)

Return the imaginary part of the complex number `z`.

See also [`conj`](@ref), [`reim`](@ref), [`adjoint`](@ref), [`angle`](@ref).

# Examples
```jldoctest
julia> imag(1 + 3im)
3
```
"""
imag(z::Complex) = z.im
````
-/
def imag_Complex {T : Type} (z : Complex T) : T := z.im

/--
Julia source: base/complex.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(x::Real) = x
```
-/
def real_Real {T : Type} (x : T) : T := x

/--
Julia source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
imag(x::Real) = zero(x)
```
-/
def imag_Real {T : Type} (zero : T → T) (x : T) : T := zero x

/--
Julia source: base/complex.jl:90-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    reim(z)

Return a tuple of the real and imaginary parts of the complex number `z`.

# Examples
```jldoctest
julia> reim(1 + 3im)
(1, 3)
```
"""
reim(z) = (real(z), imag(z))
````
-/
def reim {A R I : Type} (real : A → R) (imag : A → I) (z : A) : R × I :=
  (real z, imag z)

/--
Julia source: base/complex.jl:103-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    real(T::Type)

Return the type that represents the real part of a value of type `T`.
e.g., for `T == Complex{R}`, returns `R`.
Equivalent to `typeof(real(zero(T)))`.

# Examples
```jldoctest
julia> real(Complex{Int})
Int64

julia> real(Float64)
Float64
```
"""
real(T::Type) = typeof(real(zero(T)))
````
-/
def real_Type {Ty V RV RTy : Type} (zeroT : Ty → V) (realV : V → RV) (typeofV : RV → RTy) (T : Ty) : RTy :=
  typeofV (realV (zeroT T))

/--
Julia source: base/complex.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(::Type{T}) where {T<:Real} = T
```
-/
def real_Type_Real {R : Type} (T : R) : ComplexTy R :=
  .real T

/--
Julia source: base/complex.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(C::Type{<:Complex}) = fieldtype(C, 1)
```
-/
def real_Type_Complex {R : Type} (fieldtype1 : ComplexTy R → ComplexTy R) (C : ComplexTy R) : ComplexTy R :=
  fieldtype1 C

/--
Julia source: base/complex.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(::Type{Union{}}) = Union{}
```
-/
def real_Type_Bottom {R : Type} : ComplexTy R :=
  .bottom

/--
Julia source: base/complex.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
real(::Type{Union{}}, slurp...) = throw(MethodError(real, (Union{}, slurp...)))
```
-/
def real_Type_Bottom_slurp {R α : Type} (slurp : List α) : Jl (ComplexTy R) :=
  .error (.methodError "real")

/--
Julia source: base/complex.jl:125-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    isreal(x)::Bool

Test whether `x` or all its elements are numerically equal to some real number
including infinities and NaNs. `isreal(x)` is true if `isequal(x, real(x))`
is true.

# Examples
```jldoctest
julia> isreal(5.)
true

julia> isreal(1 - 3im)
false

julia> isreal(Inf + 0im)
true

julia> isreal([4.; complex(0,1)])
false
```
"""
isreal(x::Real) = true
````
-/
def isreal_Real {T : Type} (x : T) : Bool := true

/--
Julia source: base/complex.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreal(z::Complex) = iszero(imag(z))
```
-/
def isreal_Complex {T : Type} (iszero : T → Bool) (z : Complex T) : Bool :=
  iszero (imag_Complex z)

/--
Julia source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinteger(z::Complex) = isreal(z) & isinteger(real(z))
```
-/
def isinteger_Complex {T : Type} (iszero : T → Bool) (isinteger : T → Bool) (z : Complex T) : Bool :=
  isreal_Complex iszero z && isinteger (real_Complex z)

/--
Julia source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
```
-/
def isfinite_Complex {T : Type} (isfinite : T → Bool) (z : Complex T) : Bool :=
  isfinite (real_Complex z) && isfinite (imag_Complex z)

/--
Julia source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
```
-/
def isnan_Complex {T : Type} (isnan : T → Bool) (z : Complex T) : Bool :=
  isnan (real_Complex z) || isnan (imag_Complex z)

/--
Julia source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
```
-/
def isinf_Complex {T : Type} (isinf : T → Bool) (z : Complex T) : Bool :=
  isinf (real_Complex z) || isinf (imag_Complex z)

/--
Julia source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
```
-/
def iszero_Complex {T : Type} (iszero : T → Bool) (z : Complex T) : Bool :=
  iszero (real_Complex z) && iszero (imag_Complex z)

/--
Julia source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(z::Complex) = isone(real(z)) & iszero(imag(z))
```
-/
def isone_Complex {T : Type} (isone : T → Bool) (iszero : T → Bool) (z : Complex T) : Bool :=
  isone (real_Complex z) && iszero (imag_Complex z)

/--
Julia source: base/complex.jl:156-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    complex(r, [i])

Convert real numbers or arrays to complex. `i` defaults to zero.

# Examples
```jldoctest
julia> complex(7)
7 + 0im
```
"""
complex(z::Complex) = z
````
-/
def complex_Complex {T : Type} (z : Complex T) : Complex T := z

/--
Julia source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
complex(x::Real) = Complex(x)
```
-/
def complex_Real {T : Type} (zero : T → T) (x : T) : Complex T :=
  Complex_Real zero x

/--
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
complex(x::Real, y::Real) = Complex(x, y)
```
-/
def complex_Real_Real {A B P : Type} (promote : A → B → P × P) (x : A) (y : B) : Complex P :=
  Complex_Real_Real promote x y

/--
Julia source: base/complex.jl:171-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    complex(T::Type)

Return an appropriate type which can represent a value of type `T` as a complex number.
Equivalent to `typeof(complex(zero(T)))` if `T` does not contain `Missing`.

# Examples
```jldoctest
julia> complex(Complex{Int})
Complex{Int64}

julia> complex(Int)
Complex{Int64}

julia> complex(Union{Int, Missing})
Union{Missing, Complex{Int64}}
```
"""
complex(::Type{T}) where {T<:Real} = Complex{T}
````
-/
def complex_Type_Real {R : Type} (T : R) : ComplexTy R :=
  .complex T

/--
Julia source: base/complex.jl:191-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
complex(::Type{Complex{T}}) where {T<:Real} = Complex{T}
```
-/
def complex_Type_Complex {R : Type} (T : R) : ComplexTy R :=
  .complex T

/--
Julia source: base/complex.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
complex(::Type{Union{}}) = Union{}
```
-/
def complex_Type_Bottom {R : Type} : ComplexTy R :=
  .bottom

/--
Julia source: base/complex.jl:193-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Keep the slurp signature for bottom-type dispatch pruning,
# but do not let invalid arities contribute a successful result to inference.
complex(::Type{Union{}}, slurp...) = throw(MethodError(complex, (Union{}, slurp...)))
```
-/
def complex_Type_Bottom_slurp {R α : Type} (slurp : List α) : Jl (ComplexTy R) :=
  .error (.methodError "complex")

/--
Julia source: base/complex.jl:196-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
```
-/
def flipsign_Complex_Real {T R : Type} (signbit : R → Bool) (neg : T → T)
    (x : Complex T) (y : R) : Complex T :=
  if signbit y then ⟨neg (real_Complex x), neg (imag_Complex x)⟩ else x

/--
Julia source: base/complex.jl:198-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function show(io::IO, z::Complex)
    r, i = reim(z)
    compact = get(io, :compact, false)::Bool
    show(io, r)
    bufio = IOBuffer()
    show(IOContext(bufio, io), i)
    seekstart(bufio)
    if peek(bufio) === UInt8('-')
        seek(bufio, 1)
        print(io, compact ? "-" : " - ")
        write(io, bufio)
    else
        print(io, compact ? "+" : " + ")
        write(io, bufio)
    end
    if !(isa(i,Signed) || isa(i,AbstractFloat) && isfinite(i))
        print(io, "*")
    end
    print(io, "im")
end
```
-/
def show_Complex {T : Type} (showElem : T → String) (compact : Bool)
    (isaSigned isaAbstractFloat : Bool) (isfinite : T → Bool) (z : Complex T) : String :=
  let (r, i) := reim real_Complex imag_Complex z
  let rStr := showElem r
  let iBuf := showElem i
  let mid :=
    if iBuf.toList.head? == some '-' then
      (if compact then "-" else " - ") ++ String.ofList iBuf.toList.tail
    else
      (if compact then "+" else " + ") ++ iBuf
  let star := if !(isaSigned || (isaAbstractFloat && isfinite i)) then "*" else ""
  rStr ++ mid ++ star ++ "im"

/--
Julia source: base/complex.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, z::Complex{Bool}) =
    print(io, z == im ? "im" : "Complex($(z.re),$(z.im))")
```
-/
def show_Complex_Bool (z : Complex Bool) : String :=
  if z.re == im.re && z.im == im.im then "im"
  else s!"Complex({z.re},{z.im})"

/--
Julia source: base/complex.jl:221-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function show_unquoted(io::IO, z::Complex, ::Int, prec::Int)
    if operator_precedence(:+) <= prec
        print(io, "(")
        show(io, z)
        print(io, ")")
    else
        show(io, z)
    end
end
```
-/
def show_unquoted_Complex {T : Type} (plusPrec : JInt .i64) (showZ : Complex T → String)
    (z : Complex T) (indent prec : JInt .i64) : String :=
  if plusPrec ≤ prec then "(" ++ showZ z ++ ")" else showZ z

/--
Julia source: base/complex.jl:231-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function read(s::IO, ::Type{Complex{T}}) where T<:Real
    r = read(s,T)
    i = read(s,T)
    Complex{T}(r,i)
end
```
-/
def read_Complex {S T : Type} (readT : S → Jl (T × S)) (s : S) : Jl (Complex T × S) := do
  let (r, s1) ← readT s
  let (i, s2) ← readT s1
  return (⟨r, i⟩, s2)

/--
Julia source: base/complex.jl:237-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, z::Complex)
    write(s,real(z),imag(z))
end
```
-/
def write_Complex {S T R : Type} (write2 : S → T → T → R) (s : S) (z : Complex T) : R :=
  write2 s (real_Complex z) (imag_Complex z)

/--
Julia source: base/complex.jl:240-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## byte order swaps: real and imaginary part are swapped individually
bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
```
-/
def bswap_Complex {T : Type} (bswap : T → T) (z : Complex T) : Complex T :=
  ⟨bswap (real_Complex z), bswap (imag_Complex z)⟩

/--
Julia source: base/complex.jl:243-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## equality and hashing of complex numbers ##

==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
```
-/
def eq_Complex {T S : Type} (eq : T → S → Bool) (z : Complex T) (w : Complex S) : Bool :=
  eq (real_Complex z) (real_Complex w) && eq (imag_Complex z) (imag_Complex w)

/--
Julia source: base/complex.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(z::Complex, x::Real) = isreal(z) && real(z) == x
```
-/
def eq_Complex_Real {T R : Type} (iszero : T → Bool) (eq : T → R → Bool)
    (z : Complex T) (x : R) : Bool :=
  isreal_Complex iszero z && eq (real_Complex z) x

/--
Julia source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Real, z::Complex) = isreal(z) && real(z) == x
```
-/
def eq_Real_Complex {R T : Type} (iszero : T → Bool) (eq : T → R → Bool)
    (x : R) (z : Complex T) : Bool :=
  isreal_Complex iszero z && eq (real_Complex z) x

/--
Julia source: base/complex.jl:249-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

isequal(z::Complex, w::Complex) = isequal(real(z),real(w))::Bool & isequal(imag(z),imag(w))::Bool
```
-/
def isequal_Complex {T S : Type} (isequal : T → S → Bool) (z : Complex T) (w : Complex S) : Bool :=
  isequal (real_Complex z) (real_Complex w) && isequal (imag_Complex z) (imag_Complex w)

/--
Julia source: base/complex.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(z::Complex, w::Real) = isequal(real(z),w)::Bool & isequal(imag(z),zero(w))::Bool
```
-/
def isequal_Complex_Real {T R : Type} (isequal : T → R → Bool) (zero : R → R)
    (z : Complex T) (w : R) : Bool :=
  isequal (real_Complex z) w && isequal (imag_Complex z) (zero w)

/--
Julia source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
```
-/
def isequal_Real_Complex {R T : Type} (isequal : R → T → Bool) (zero : R → R)
    (z : R) (w : Complex T) : Bool :=
  isequal z (real_Complex w) && isequal (zero z) (imag_Complex w)

/--
Julia source: base/complex.jl:253-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

in(x::Complex, r::AbstractRange{<:Real}) = isreal(x) && real(x) in r
```
-/
def in_Complex_AbstractRange {T R : Type} (iszero : T → Bool) (mem : T → R → Bool)
    (x : Complex T) (r : R) : Bool :=
  isreal_Complex iszero x && mem (real_Complex x) r

/--
Julia source: base/complex.jl:255-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const h_imag = 0x32a7a07f3e7cd1f9 % UInt
```
-/
def h_imag : UInt64 := 0x32a7a07f3e7cd1f9

/--
Julia source: base/complex.jl:257-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const hash_0_imag = hash(0, h_imag)

```
-/
def hash_0_imag {T : Type} (hashT : T → UInt64 → UInt64) (zeroT : T) : UInt64 :=
  hashT zeroT h_imag

/--
Julia source: base/complex.jl:259-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(z::Complex, h::UInt)
    # TODO: with default argument specialization, this would be better:
    # hash(real(z), h ⊻ hash(imag(z), h ⊻ h_imag) ⊻ hash(0, h ⊻ h_imag))
    hash(real(z), h ⊻ hash(imag(z), h_imag) ⊻ hash_0_imag)
end
```
-/
def hash_Complex {T : Type} (hashT : T → UInt64 → UInt64) (hImag hash0Imag : UInt64)
    (z : Complex T) (h : UInt64) : UInt64 :=
  hashT (real_Complex z) (h ^^^ hashT (imag_Complex z) hImag ^^^ hash0Imag)

/--
Julia source: base/complex.jl:264-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

## generic functions of complex numbers ##

"""
    conj(z)

Compute the complex conjugate of a complex number `z`.

See also [`angle`](@ref), [`adjoint`](@ref).

# Examples
```jldoctest
julia> conj(1 + 3im)
1 - 3im
```
"""
conj(z::Complex) = Complex(real(z),-imag(z))
````
-/
def conj_Complex {T : Type} (neg : T → T) (z : Complex T) : Complex T :=
  ⟨real_Complex z, neg (imag_Complex z)⟩

/--
Julia source: base/complex.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(z::Complex)  = hypot(real(z), imag(z))
```
-/
def abs_Complex {T R : Type} (hypot : T → T → R) (z : Complex T) : R :=
  hypot (real_Complex z) (imag_Complex z)

/--
Julia source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
```
-/
def abs2_Complex {T P S : Type} (mul : T → T → P) (add : P → P → S) (z : Complex T) : S :=
  add (mul (real_Complex z) (real_Complex z)) (mul (imag_Complex z) (imag_Complex z))

/--
Julia source: base/complex.jl:283-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function inv(z::Complex)
    c, d = reim(z)
    (isinf(c) | isinf(d)) && return complex(copysign(zero(c), c), flipsign(-zero(d), d))
    complex(c, -d)/(c * c + d * d)
end
```
-/
def inv_Complex {T : Type} (isinf : T → Bool) (zero : T → T) (neg : T → T)
    (copysign flipsign add mul div : T → T → T) (z : Complex T) : Complex T :=
  let (c, d) := reim real_Complex imag_Complex z
  if isinf c || isinf d then
    ⟨copysign (zero c) c, flipsign (neg (zero d)) d⟩
  else
    let den := add (mul c c) (mul d d)
    ⟨div c den, div (neg d) den⟩

/--
Julia source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inv(z::Complex{<:Integer}) = inv(float(z))
```
-/
def inv_Complex_Integer {T F R : Type} (floatC : Complex T → Complex F)
    (invF : Complex F → R) (z : Complex T) : R :=
  invF (floatC z)

/--
Julia source: base/complex.jl:289-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

+(z::Complex) = Complex(+real(z), +imag(z))
```
-/
def pos_Complex {T R : Type} (pos : T → R) (z : Complex T) : Complex R :=
  ⟨pos (real_Complex z), pos (imag_Complex z)⟩

/--
Julia source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex) = Complex(-real(z), -imag(z))
```
-/
def neg_Complex {T R : Type} (neg : T → R) (z : Complex T) : Complex R :=
  ⟨neg (real_Complex z), neg (imag_Complex z)⟩

/--
Julia source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
```
-/
def add_Complex {A B C : Type} (add : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨add (real_Complex z) (real_Complex w), add (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
```
-/
def sub_Complex {A B C : Type} (sub : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨sub (real_Complex z) (real_Complex w), sub (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
                                    real(z) * imag(w) + imag(z) * real(w))
```
-/
def mul_Complex {A B P S : Type} (mul : A → B → P) (sub add : P → P → S)
    (z : Complex A) (w : Complex B) : Complex S :=
  ⟨sub (mul (real_Complex z) (real_Complex w)) (mul (imag_Complex z) (imag_Complex w)),
   add (mul (real_Complex z) (imag_Complex w)) (mul (imag_Complex z) (real_Complex w))⟩

/--
Julia source: base/complex.jl:296-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

-%(z::Complex) = Complex(-%(real(z)), -%(imag(z)))
```
-/
def negWrap_Complex {T R : Type} (negWrap : T → R) (z : Complex T) : Complex R :=
  ⟨negWrap (real_Complex z), negWrap (imag_Complex z)⟩

/--
Julia source: base/complex.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+%(z::Complex, w::Complex) = Complex(real(z) +% real(w), imag(z) +% imag(w))
```
-/
def addWrap_Complex {A B C : Type} (addWrap : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨addWrap (real_Complex z) (real_Complex w), addWrap (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(z::Complex, w::Complex) = Complex(real(z) -% real(w), imag(z) -% imag(w))
```
-/
def subWrap_Complex {A B C : Type} (subWrap : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨subWrap (real_Complex z) (real_Complex w), subWrap (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*%(z::Complex, w::Complex) = Complex(real(z) *% real(w) -% imag(z) *% imag(w),
                                     real(z) *% imag(w) +% imag(z) *% real(w))
```
-/
def mulWrap_Complex {A B P S : Type} (mulWrap : A → B → P) (subWrap addWrap : P → P → S)
    (z : Complex A) (w : Complex B) : Complex S :=
  ⟨subWrap (mulWrap (real_Complex z) (real_Complex w)) (mulWrap (imag_Complex z) (imag_Complex w)),
   addWrap (mulWrap (real_Complex z) (imag_Complex w)) (mulWrap (imag_Complex z) (real_Complex w))⟩

/--
Julia source: base/complex.jl:302-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

_mulsub(a, b, c) = _mulsub(promote(a, b, c)...)
```
-/
def _mulsub_generic {A B C P R : Type} (promote3 : A → B → C → P × P × P)
    (mulsubP : P → P → P → R) (a : A) (b : B) (c : C) : R :=
  let (pa, pb, pc) := promote3 a b c
  mulsubP pa pb pc

/--
Julia source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mulsub(a::T, b::T, c::T) where {T<:Real} = muladd(a, b, -c)
```
-/
def _mulsub_Real {T : Type} (muladd : T → T → T → T) (neg : T → T) (a b c : T) : T :=
  muladd a b (neg c)

/--
Julia source: base/complex.jl:305-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(z::Complex, w::Complex, x::Complex) =
    Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), real(x))),
            muladd(real(z), imag(w), muladd(imag(z), real(w), imag(x))))
```
-/
def muladd_Complex_Complex_Complex {T : Type} (muladd : T → T → T → T) (neg : T → T)
    (z w x : Complex T) : Complex T :=
  ⟨muladd (real_Complex z) (real_Complex w) (neg (_mulsub_Real muladd neg (imag_Complex z) (imag_Complex w) (real_Complex x))),
   muladd (real_Complex z) (imag_Complex w) (muladd (imag_Complex z) (real_Complex w) (imag_Complex x))⟩

/--
Julia source: base/complex.jl:308-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# handle Bool and Complex{Bool}
# avoid type signature ambiguity warnings
+(x::Bool, z::Complex{Bool}) = Complex(x + real(z), imag(z))
```
-/
def add_Bool_ComplexBool (x : Bool) (z : Complex Bool) : Complex (JInt .i64) :=
  Complex_Real_Real promote_Int_Bool (add_Bool_Bool x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex{Bool}, x::Bool) = Complex(real(z) + x, imag(z))
```
-/
def add_ComplexBool_Bool (z : Complex Bool) (x : Bool) : Complex (JInt .i64) :=
  Complex_Real_Real promote_Int_Bool (add_Bool_Bool (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool, z::Complex{Bool}) = Complex(x - real(z), - imag(z))
```
-/
def sub_Bool_ComplexBool (x : Bool) (z : Complex Bool) : Complex (JInt .i64) :=
  ⟨sub_Bool_Bool x (real_Complex z), neg_Bool_val (imag_Complex z)⟩

/--
Julia source: base/complex.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex{Bool}, x::Bool) = Complex(real(z) - x, imag(z))
```
-/
def sub_ComplexBool_Bool (z : Complex Bool) (x : Bool) : Complex (JInt .i64) :=
  Complex_Real_Real promote_Int_Bool (sub_Bool_Bool (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Bool, z::Complex{Bool}) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Bool_ComplexBool (x : Bool) (z : Complex Bool) : Complex Bool :=
  ⟨mul_Bool_Bool x (real_Complex z), mul_Bool_Bool x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex{Bool}, x::Bool) = Complex(real(z) * x, imag(z) * x)
```
-/
def mul_ComplexBool_Bool (z : Complex Bool) (x : Bool) : Complex Bool :=
  ⟨mul_Bool_Bool (real_Complex z) x, mul_Bool_Bool (imag_Complex z) x⟩

/--
Julia source: base/complex.jl:317-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

+(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
```
-/
def add_Bool_Complex {T S P : Type} (addBool : Bool → T → S) (promote : S → T → P × P)
    (x : Bool) (z : Complex T) : Complex P :=
  Complex_Real_Real promote (addBool x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
```
-/
def add_Complex_Bool {T S P : Type} (addBoolRight : T → Bool → S) (promote : S → T → P × P)
    (z : Complex T) (x : Bool) : Complex P :=
  Complex_Real_Real promote (addBoolRight (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
```
-/
def sub_Bool_Complex {T S N P : Type} (subBool : Bool → T → S) (neg : T → N)
    (promote : S → N → P × P) (x : Bool) (z : Complex T) : Complex P :=
  Complex_Real_Real promote (subBool x (real_Complex z)) (neg (imag_Complex z))

/--
Julia source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex, x::Bool) = Complex(real(z) - x, imag(z))
```
-/
def sub_Complex_Bool {T S P : Type} (subBoolRight : T → Bool → S) (promote : S → T → P × P)
    (z : Complex T) (x : Bool) : Complex P :=
  Complex_Real_Real promote (subBoolRight (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Bool, z::Complex) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Bool_Complex {T P : Type} (mulBool : Bool → T → P) (x : Bool) (z : Complex T) : Complex P :=
  ⟨mulBool x (real_Complex z), mulBool x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
```
-/
def mul_Complex_Bool {T P : Type} (mulBoolRight : T → Bool → P) (z : Complex T) (x : Bool) : Complex P :=
  ⟨mulBoolRight (real_Complex z) x, mulBoolRight (imag_Complex z) x⟩

/--
Julia source: base/complex.jl:324-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

+(x::Real, z::Complex{Bool}) = Complex(x + real(z), imag(z))
```
-/
def add_Real_ComplexBool {R S P : Type} (addRB : R → Bool → S) (promote : S → Bool → P × P)
    (x : R) (z : Complex Bool) : Complex P :=
  Complex_Real_Real promote (addRB x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex{Bool}, x::Real) = Complex(real(z) + x, imag(z))
```
-/
def add_ComplexBool_Real {R S P : Type} (addBR : Bool → R → S) (promote : S → Bool → P × P)
    (z : Complex Bool) (x : R) : Complex P :=
  Complex_Real_Real promote (addBR (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::Real, z::Complex{Bool})
    # we don't want the default type for -(Bool)
    re = x-real(z)
    Complex(re, - oftype(re, imag(z)))
end
```
-/
def sub_Real_ComplexBool {R S : Type} (subRB : R → Bool → S) (oftype : S → Bool → S)
    (neg : S → S) (x : R) (z : Complex Bool) : Complex S :=
  let re := subRB x (real_Complex z)
  ⟨re, neg (oftype re (imag_Complex z))⟩

/--
Julia source: base/complex.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex{Bool}, x::Real) = Complex(real(z) - x, imag(z))
```
-/
def sub_ComplexBool_Real {R S P : Type} (subBR : Bool → R → S) (promote : S → Bool → P × P)
    (z : Complex Bool) (x : R) : Complex P :=
  Complex_Real_Real promote (subBR (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Real, z::Complex{Bool}) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Real_ComplexBool {R P : Type} (mulRB : R → Bool → P) (x : R) (z : Complex Bool) : Complex P :=
  ⟨mulRB x (real_Complex z), mulRB x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex{Bool}, x::Real) = Complex(real(z) * x, imag(z) * x)
```
-/
def mul_ComplexBool_Real {R P : Type} (mulBR : Bool → R → P) (z : Complex Bool) (x : R) : Complex P :=
  ⟨mulBR (real_Complex z) x, mulBR (imag_Complex z) x⟩

/--
Julia source: base/complex.jl:335-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# adding or multiplying real & complex is common
+(x::Real, z::Complex) = Complex(x + real(z), imag(z))
```
-/
def add_Real_Complex {R T S P : Type} (add : R → T → S) (promote : S → T → P × P)
    (x : R) (z : Complex T) : Complex P :=
  Complex_Real_Real promote (add x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, x::Real) = Complex(x + real(z), imag(z))
```
-/
def add_Complex_Real {T R S P : Type} (add : R → T → S) (promote : S → T → P × P)
    (z : Complex T) (x : R) : Complex P :=
  Complex_Real_Real promote (add x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::Real, z::Complex)
    # we don't want the default type for -(Bool)
    re = x - real(z)
    Complex(re, - oftype(re, imag(z)))
end
```
-/
def sub_Real_Complex {R T S : Type} (sub : R → T → S) (oftype : S → T → S)
    (neg : S → S) (x : R) (z : Complex T) : Complex S :=
  let re := sub x (real_Complex z)
  ⟨re, neg (oftype re (imag_Complex z))⟩

/--
Julia source: base/complex.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex, x::Real) = Complex(real(z) - x, imag(z))
```
-/
def sub_Complex_Real {T R S P : Type} (sub : T → R → S) (promote : S → T → P × P)
    (z : Complex T) (x : R) : Complex P :=
  Complex_Real_Real promote (sub (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Real, z::Complex) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Real_Complex {R T P : Type} (mul : R → T → P) (x : R) (z : Complex T) : Complex P :=
  ⟨mul x (real_Complex z), mul x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex, x::Real) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Complex_Real {T R P : Type} (mul : R → T → P) (z : Complex T) (x : R) : Complex P :=
  ⟨mul x (real_Complex z), mul x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

muladd(x::Real, z::Complex, y::Union{Real,Complex}) = muladd(z, x, y)
```
-/
def muladd_Real_Complex_Union {R T Y Out : Type} (muladdZX : Complex T → R → Y → Out)
    (x : R) (z : Complex T) (y : Y) : Out :=
  muladdZX z x y

/--
Julia source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(z::Complex, x::Real, y::Real) = Complex(muladd(real(z),x,y), imag(z)*x)
```
-/
def muladd_Complex_Real_Real {T R Y M P Out : Type} (muladd : T → R → Y → M)
    (mul : T → R → P) (promote : M → P → Out × Out) (z : Complex T) (x : R) (y : Y) : Complex Out :=
  Complex_Real_Real promote (muladd (real_Complex z) x y) (mul (imag_Complex z) x)

/--
Julia source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(z::Complex, x::Real, w::Complex) =
    Complex(muladd(real(z),x,real(w)), muladd(imag(z),x,imag(w)))
```
-/
def muladd_Complex_Real_Complex {T R W M : Type} (muladd : T → R → W → M)
    (z : Complex T) (x : R) (w : Complex W) : Complex M :=
  ⟨muladd (real_Complex z) x (real_Complex w), muladd (imag_Complex z) x (imag_Complex w)⟩

/--
Julia source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(x::Real, y::Real, z::Complex) = Complex(muladd(x,y,real(z)), imag(z))
```
-/
def muladd_Real_Real_Complex {X Y T M Out : Type} (muladd : X → Y → T → M)
    (promote : M → T → Out × Out) (x : X) (y : Y) (z : Complex T) : Complex Out :=
  Complex_Real_Real promote (muladd x y (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(z::Complex, w::Complex, x::Real) =
    Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), x)),
            muladd(real(z), imag(w), imag(z) * real(w)))
```
-/
def muladd_Complex_Complex_Real {T R : Type} (muladd : T → T → T → T)
    (mulsub : T → T → R → T) (neg : T → T) (mul : T → T → T)
    (z w : Complex T) (x : R) : Complex T :=
  ⟨muladd (real_Complex z) (real_Complex w) (neg (mulsub (imag_Complex z) (imag_Complex w) x)),
   muladd (real_Complex z) (imag_Complex w) (mul (imag_Complex z) (real_Complex w))⟩

/--
Julia source: base/complex.jl:356-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

/(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))
```
-/
def div_Real_Complex {R T P Out : Type} (convertC : Complex T → Complex P)
    (invC : Complex P → Complex P) (mulRC : R → Complex P → Complex Out)
    (a : R) (z : Complex T) : Complex Out :=
  mulRC a (invC (convertC z))

/--
Julia source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(z::Complex, x::Real) = Complex(real(z)/x, imag(z)/x)
```
-/
def div_Complex_Real {T R Q : Type} (div : T → R → Q) (z : Complex T) (x : R) : Complex Q :=
  ⟨div (real_Complex z) x, div (imag_Complex z) x⟩

/--
Julia source: base/complex.jl:359-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function /(a::Complex{T}, b::Complex{T}) where T<:Real
    are = real(a); aim = imag(a); bre = real(b); bim = imag(b)
    if (isinf(bre) | isinf(bim))
        if isfinite(a)
            return complex(zero(T)*sign(are)*sign(bre), -zero(T)*sign(aim)*sign(bim))
        end
        return T(NaN)+T(NaN)*im
    end
    if abs(bre) <= abs(bim)
        r = bre / bim
        den = bim + r*bre
        Complex((are*r + aim)/den, (aim*r - are)/den)
    else
        r = bim / bre
        den = bre + r*bim
        Complex((are + aim*r)/den, (aim - are*r)/den)
    end
end
```
-/
def div_Complex_same {T F : Type}
    (isinf isfinite : T → Bool) (zeroF : F) (negF : F → F) (nanF : F)
    (signF : T → F) (absT : T → T) (leT : T → T → Bool)
    (divTT : T → T → F) (mulFT : F → T → F) (mulTF : T → F → F)
    (addTF : T → F → F) (addFT : F → T → F) (subFT : F → T → F) (subTF : T → F → F)
    (divFF mulFF : F → F → F)
    (a b : Complex T) : Complex F :=
  let are := real_Complex a
  let aim := imag_Complex a
  let bre := real_Complex b
  let bim := imag_Complex b
  if isinf bre || isinf bim then
    if isfinite_Complex isfinite a then
      ⟨mulFF (mulFF zeroF (signF are)) (signF bre),
       mulFF (mulFF (negF zeroF) (signF aim)) (signF bim)⟩
    else
      ⟨nanF, nanF⟩
  else if leT (absT bre) (absT bim) then
    let r := divTT bre bim
    let den := addTF bim (mulFT r bre)
    ⟨divFF (addFT (mulTF are r) aim) den, divFF (subFT (mulTF aim r) are) den⟩
  else
    let r := divTT bim bre
    let den := addTF bre (mulFT r bim)
    ⟨divFF (addTF are (mulTF aim r)) den, divFF (subTF aim (mulTF are r)) den⟩

/--
Julia source: base/complex.jl:378-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function /(z::Complex{T}, w::Complex{T}) where {T<:Union{Float16,Float32}}
    c, d = reim(widen(w))
    a, b = reim(widen(z))
    if (isinf(c) | isinf(d))
        if isfinite(z)
            return complex(zero(T)*sign(real(z))*sign(real(w)), -zero(T)*sign(imag(z))*sign(imag(w)))
        end
        return T(NaN)+T(NaN)*im
    end
    mag = inv(muladd(c, c, d^2))
    re_part = muladd(a, c, b*d)
    im_part = muladd(b, c, -a*d)
    return oftype(z, Complex(re_part*mag, im_part*mag))
end
```
-/
def div_Complex_SmallFloat {T W : Type}
    (widen : Complex T → Complex W) (isinfW : W → Bool) (isfiniteT : T → Bool)
    (zeroT nanT : T) (negT : T → T) (signT : T → T) (mulT : T → T → T)
    (invW : W → W) (mulW : W → W → W) (negW : W → W) (muladdW : W → W → W → W)
    (oftypeZ : Complex W → Complex T)
    (z w : Complex T) : Complex T :=
  let (c, d) := reim real_Complex imag_Complex (widen w)
  let (a, b) := reim real_Complex imag_Complex (widen z)
  if isinfW c || isinfW d then
    if isfinite_Complex isfiniteT z then
      ⟨mulT (mulT zeroT (signT (real_Complex z))) (signT (real_Complex w)),
       mulT (mulT (negT zeroT) (signT (imag_Complex z))) (signT (imag_Complex w))⟩
    else
      ⟨nanT, nanT⟩
  else
    let mag := invW (muladdW c c (mulW d d))
    let re_part := muladdW a c (mulW b d)
    let im_part := muladdW b c (mulW (negW a) d)
    oftypeZ ⟨mulW re_part mag, mulW im_part mag⟩

/--
Julia source: base/complex.jl:467-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function robust_cdiv2(a::Float64, b::Float64, c::Float64, d::Float64, r::Float64, t::Float64)
    if r != 0
        br = b*r
        return (br != 0 ? (a+br)*t : a*t + (b*t)*r)
    else
        return (a + d*(b/c)) * t
    end
end
```
-/
def robust_cdiv2 (a b c d r t : F64) : F64 :=
  if !F64.eq r Fl64.pzero then
    let br := F64.mul b r
    if !F64.eq br Fl64.pzero then F64.mul (F64.add a br) t
    else F64.add (F64.mul a t) (F64.mul (F64.mul b t) r)
  else F64.mul (F64.add a (F64.mul d (F64.div b c))) t

/--
Julia source: base/complex.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function robust_cdiv1(a::Float64, b::Float64, c::Float64, d::Float64)
    r = d/c
    t = 1.0/(c+d*r)
    p = robust_cdiv2(a,b,c,d,r,t)
    q = robust_cdiv2(b,-a,c,d,r,t)
    return p,q
end
```
-/
def robust_cdiv1 (a b c d : F64) : F64 × F64 :=
  let r := F64.div d c
  let t := F64.div F64.one (F64.add c (F64.mul d r))
  let p := robust_cdiv2 a b c d r t
  let q := robust_cdiv2 b (F64.neg a) c d r t
  (p, q)

/--
Julia source: base/complex.jl:422-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# sub-functionality for /(z::ComplexF64, w::ComplexF64)
@inline function cdiv(a::Float64, b::Float64, c::Float64, d::Float64)
    if abs(d)<=abs(c)
        p,q = robust_cdiv1(a,b,c,d)
    else
        p,q = robust_cdiv1(b,a,d,c)
        q = -q
    end
    return p,q
end
```
-/
def cdiv (a b c d : F64) : F64 × F64 :=
  if F64.le (F64.abs d) (F64.abs c) then
    robust_cdiv1 a b c d
  else
    let (p, q) := robust_cdiv1 b a d c
    (p, F64.neg q)

/--
Julia source: base/complex.jl:439-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scaleargs_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64)
    ϵ      = eps(Float64)
    halfov = 0.5*floatmax(Float64)
    twounϵ = floatmin(Float64)*2.0/ϵ
    bs     = 2.0/(ϵ*ϵ)

    # scaling
    s = 1.0
    if ab >= halfov
        a*=0.5; b*=0.5; s*=2.0  # scale down a,b
    elseif ab <= twounϵ
        a*=bs;  b*=bs;  s/=bs   # scale up a,b
    end
    if cd >= halfov
        c*=0.5; d*=0.5; s*=0.5  # scale down c,d
    elseif cd <= twounϵ
        c*=bs;  d*=bs;  s*=bs   # scale up c,d
    end

    return a,b,c,d,s
end
```
-/
def scaleargs_cdiv (a b c d ab cd : F64) : F64 × F64 × F64 × F64 × F64 :=
  let eps := Fl64.eps
  let halfov := F64.mul Fl64.half F64.floatmax
  let twounEps := F64.div (F64.mul F64.floatmin Fl64.two) eps
  let bs := F64.div Fl64.two (F64.mul eps eps)
  let s := F64.one
  let (a, b, s) :=
    if F64.le halfov ab then (F64.mul a Fl64.half, F64.mul b Fl64.half, F64.mul s Fl64.two)
    else if F64.le ab twounEps then (F64.mul a bs, F64.mul b bs, F64.div s bs)
    else (a, b, s)
  let (c, d, s) :=
    if F64.le halfov cd then (F64.mul c Fl64.half, F64.mul d Fl64.half, F64.mul s Fl64.half)
    else if F64.le cd twounEps then (F64.mul c bs, F64.mul d bs, F64.mul s bs)
    else (c, d, s)
  (a, b, c, d, s)

/--
Julia source: base/complex.jl:433-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function scaling_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64)
    # this over/underflow functionality is outlined for performance, cf. #29688
    a,b,c,d,s = scaleargs_cdiv(a,b,c,d,ab,cd)
    p,q = cdiv(a,b,c,d)
    return p*s,q*s
end
```
-/
def scaling_cdiv (a b c d ab cd : F64) : F64 × F64 :=
  let (a, b, c, d, s) := scaleargs_cdiv a b c d ab cd
  let (p, q) := cdiv a b c d
  (F64.mul p s, F64.mul q s)

/--
Julia source: base/complex.jl:393-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# robust complex division for double precision
# variables are scaled & unscaled to avoid over/underflow, if necessary
# based on arxiv.1210.4539
#             a + i*b
#  p + i*q = ---------
#             c + i*d
function /(z::ComplexF64, w::ComplexF64)
    a, b = reim(z); c, d = reim(w)
    absa = abs(a); absb = abs(b);  ab = absa >= absb ? absa : absb # equiv. to max(abs(a),abs(b)) but without NaN-handling (faster)
    absc = abs(c); absd = abs(d);  cd = absc >= absd ? absc : absd
    if (isinf(c) | isinf(d))
        if isfinite(z)
            return complex(0.0*sign(a)*sign(c), -0.0*sign(b)*sign(d))
        end
        return NaN+NaN*im
    end
    halfov = 0.5*floatmax(Float64)              # overflow threshold
    twounϵ = floatmin(Float64)*2.0/eps(Float64) # underflow threshold

    # actual division operations
    if  ab>=halfov || ab<=twounϵ || cd>=halfov || cd<=twounϵ # over/underflow case
        p,q = scaling_cdiv(a,b,c,d,ab,cd) # scales a,b,c,d before division (unscales after)
    else
        p,q = cdiv(a,b,c,d)
    end

    return ComplexF64(p,q)
end
```
-/
def div_ComplexF64 (z w : ComplexF64) : ComplexF64 :=
  let (a, b) := reim real_Complex imag_Complex z
  let (c, d) := reim real_Complex imag_Complex w
  let absa := F64.abs a
  let absb := F64.abs b
  let ab := if F64.le absb absa then absa else absb
  let absc := F64.abs c
  let absd := F64.abs d
  let cd := if F64.le absd absc then absc else absd
  if F64.isinf c || F64.isinf d then
    if isfinite_Complex F64.isfinite z then
      ⟨F64.mul (F64.mul Fl64.pzero (Fl64.sign a)) (Fl64.sign c),
       F64.mul (F64.mul Fl64.nzero (Fl64.sign b)) (Fl64.sign d)⟩
    else ⟨F64.add F64.nan (Fl64.mulBool false F64.nan), Fl64.mulBool true F64.nan⟩
  else
    let halfov := F64.mul Fl64.half F64.floatmax
    let twounEps := F64.div (F64.mul F64.floatmin Fl64.two) Fl64.eps
    let (p, q) :=
      if F64.le halfov ab || F64.le ab twounEps || F64.le halfov cd || F64.le cd twounEps then
        scaling_cdiv a b c d ab cd
      else
        cdiv a b c d
    ⟨p, q⟩

/--
Julia source: base/complex.jl:475-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function inv(z::Complex{T}) where T<:Union{Float16,Float32}
    c, d = reim(widen(z))
    (isinf(c) | isinf(d)) && return complex(copysign(zero(T), c), flipsign(-zero(T), d))
    mag = inv(muladd(c, c, d^2))
    return oftype(z, Complex(c*mag, -d*mag))
end
```
-/
def inv_Complex_SmallFloat {T W : Type}
    (widen : Complex T → Complex W) (isinfW : W → Bool)
    (zeroT : T) (negT : T → T) (copysignT flipsignT : T → W → T)
    (invW : W → W) (mulW : W → W → W) (negW : W → W) (muladdW : W → W → W → W)
    (oftypeZ : Complex W → Complex T)
    (z : Complex T) : Complex T :=
  let (c, d) := reim real_Complex imag_Complex (widen z)
  if isinfW c || isinfW d then
    ⟨copysignT zeroT c, flipsignT (negT zeroT) d⟩
  else
    let mag := invW (muladdW c c (mulW d d))
    oftypeZ ⟨mulW c mag, mulW (negW d) mag⟩

/--
Julia source: base/complex.jl:511-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function robust_cinv(c::Float64, d::Float64)
    r = d/c
    z = muladd(d, r, c)
    p = 1.0/z
    q = -r/z
    return p, q
end
```
-/
def robust_cinv (c d : F64) : F64 × F64 :=
  let r := F64.div d c
  let z := F64.muladd d r c
  let p := F64.div F64.one z
  let q := F64.div (F64.neg r) z
  (p, q)

/--
Julia source: base/complex.jl:482-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function inv(w::ComplexF64)
    c, d = reim(w)
    absc, absd = abs(c), abs(d)
    cd, dc = ifelse(absc>absd, (absc, absd), (absd, absc))
    # no overflow from abs2
    if sqrt(floatmin(Float64)/2) <= cd <= sqrt(floatmax(Float64)/2)
        return conj(w) / muladd(cd, cd, dc*dc)
    end
    (isinf(c) | isinf(d)) && return complex(copysign(0.0, c), flipsign(-0.0, d))

    ϵ  = eps(Float64)
    bs = 2/(ϵ*ϵ)

    # scaling
    s = 1.0
    if cd >= floatmax(Float64)/2
        c *= 0.5; d *= 0.5; s = 0.5 # scale down c, d
    elseif cd <= 2floatmin(Float64)/ϵ
        c *= bs;  d *= bs;  s = bs  # scale up c, d
    end

    # inversion operations
    if absd <= absc
        p, q = robust_cinv(c, d)
    else
        q, p = robust_cinv(-d, -c)
    end
    return ComplexF64(p*s, q*s)
end
```
-/
def inv_ComplexF64 (w : ComplexF64) : Jl ComplexF64 := do
  let (c, d) := reim real_Complex imag_Complex w
  let absc := F64.abs c
  let absd := F64.abs d
  let (cd, dc) := if F64.lt absd absc then (absc, absd) else (absd, absc)
  let lo ← F64.sqrt (F64.div F64.floatmin Fl64.two)
  let hi ← F64.sqrt (F64.div F64.floatmax Fl64.two)
  if F64.le lo cd && F64.le cd hi then
    return div_Complex_Real F64.div (conj_Complex F64.neg w) (F64.muladd cd cd (F64.mul dc dc))
  if F64.isinf c || F64.isinf d then
    return ⟨Fl64.copysign Fl64.pzero c, Fl64.flipsign Fl64.nzero d⟩
  let eps := Fl64.eps
  let bs := F64.div Fl64.two (F64.mul eps eps)
  let (c, d, s) :=
    if F64.le (F64.div F64.floatmax Fl64.two) cd then (F64.mul c Fl64.half, F64.mul d Fl64.half, Fl64.half)
    else if F64.le cd (F64.div (F64.mul Fl64.two F64.floatmin) eps) then
      (F64.mul c bs, F64.mul d bs, bs)
    else (c, d, F64.one)
  let (p, q) :=
    if F64.le absd absc then robust_cinv c d
    else
      let (q, p) := robust_cinv (F64.neg d) (F64.neg c)
      (p, q)
  return ⟨F64.mul p s, F64.mul q s⟩

/--
Julia source: base/complex.jl:518-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function ssqs(x::T, y::T) where T<:Real
    k::Int = 0
    ρ = x*x + y*y
    if !isfinite(ρ) && (isinf(x) || isinf(y))
        ρ = convert(T, Inf)
    elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
        m::T = max(abs(x), abs(y))
        k = m==0 ? 0 : exponent(m)
        xk, yk = ldexp(x,-k), ldexp(y,-k)
        ρ = xk*xk + yk*yk
    end
    ρ, k
end
```
-/
def ssqs {T : Type}
    (isfinite isinf : T → Bool) (eq lt : T → T → Bool)
    (zero two inf eps : T) (abs : T → T) (max add mul div : T → T → T)
    (nextfloat : T → T) (exponent : T → Int) (ldexp : T → Int → T)
    (x y : T) : T × JInt .i64 :=
  let ρ := add (mul x x) (mul y y)
  if !isfinite ρ && (isinf x || isinf y) then
    (inf, JInt.lit .i64 0)
  else
    let tiny := div (nextfloat zero) (mul two (mul eps eps))
    if isinf ρ || (eq ρ zero && (!eq x zero || !eq y zero)) || lt ρ tiny then
      let m := max (abs x) (abs y)
      let k : JInt .i64 := if eq m zero then JInt.lit .i64 0 else JInt.lit .i64 (exponent m)
      let xk := ldexp x (-k).val
      let yk := ldexp y (-k).val
      (add (mul xk xk) (mul yk yk), k)
    else
      (ρ, JInt.lit .i64 0)

/--
Julia source: base/complex.jl:532-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function sqrt(z::Complex)
    z = float(z)
    x, y = reim(z)
    if x==y==0
        return Complex(zero(x),y)
    end
    ρ, k::Int = ssqs(x, y)
    if isfinite(x) ρ=ldexp(abs(x),-k)+sqrt(ρ) end
    if isodd(k)
        k = div(k-1,2)
    else
        k = div(k,2)-1
        ρ += ρ
    end
    ρ = ldexp(sqrt(ρ),k) #sqrt((abs(z)+abs(x))/2) without over/underflow
    ξ = ρ
    η = y
    if ρ != 0
        if isfinite(η) η=(η/ρ)/2 end
        if x<0
            ξ = abs(η)
            η = copysign(ρ,y)
        end
    end
    Complex(ξ,η)
end
```
-/
def sqrt_Complex {A T : Type}
    (floatC : Complex A → Complex T)
    (isfinite isinf : T → Bool) (eq lt : T → T → Bool)
    (zero two inf eps : T) (abs : T → T) (max add mul div copysign : T → T → T)
    (nextfloat : T → T) (exponent : T → Int) (ldexp : T → Int → T) (sqrtT : T → T)
    (z : Complex A) : Complex T :=
  let z := floatC z
  let (x, y) := reim real_Complex imag_Complex z
  if eq x y && eq y zero then
    ⟨zero, y⟩
  else
    let (ρ, k) := ssqs isfinite isinf eq lt zero two inf eps abs max add mul div nextfloat exponent ldexp x y
    let ρ := if isfinite x then add (ldexp (abs x) (-k).val) (sqrtT ρ) else ρ
    let (k, ρ) :=
      if k.val % 2 != 0 then
        (JInt.lit .i64 ((k.val - 1).tdiv 2), ρ)
      else
        (JInt.lit .i64 (k.val.tdiv 2) - JInt.lit .i64 1, add ρ ρ)
    let ρ := ldexp (sqrtT ρ) k.val
    if !eq ρ zero then
      let η := if isfinite y then div (div y ρ) two else y
      if lt x zero then
        ⟨abs η, copysign ρ y⟩
      else
        ⟨ρ, η⟩
    else
      ⟨ρ, y⟩

/--
Julia source: base/complex.jl:559-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

# function sqrt(z::Complex)
#     rz = float(real(z))
#     iz = float(imag(z))
#     r = sqrt((hypot(rz,iz)+abs(rz))/2)
#     if r == 0
#         return Complex(zero(iz), iz)
#     end
#     if rz >= 0
#         return Complex(r, iz/r/2)
#     end
#     return Complex(abs(iz)/r/2, copysign(r,iz))
# end

"""
    cis(x)

More efficient method for `exp(im*x)` by using Euler's formula: ``\\cos(x) + i \\sin(x) = \\exp(i x)``.

See also [`cispi`](@ref), [`sincos`](@ref), [`exp`](@ref), [`angle`](@ref).

# Examples
```jldoctest
julia> cis(π) ≈ -1
true
```
"""
function cis end
````
-/
def cis_generic_decl : Unit := ()

/--
Julia source: base/complex.jl:587-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cis(theta::Real)
    s, c = sincos(theta)
    Complex(c, s)
end
```
-/
def cis_Real {A T : Type} (sincos : A → T × T) (theta : A) : Complex T :=
  let (s, c) := sincos theta
  ⟨c, s⟩

/--
Julia source: base/complex.jl:591-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function cis(z::Complex)
    v = exp(-imag(z))
    s, c = sincos(real(z))
    Complex(v * c, v * s)
end
```
-/
def cis_Complex {A T : Type} (neg : A → A) (exp : A → T) (sincos : A → T × T)
    (mul : T → T → T) (z : Complex A) : Complex T :=
  let v := exp (neg (imag_Complex z))
  let (s, c) := sincos (real_Complex z)
  ⟨mul v c, mul v s⟩

/--
Julia source: base/complex.jl:597-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    cispi(x)

More accurate method for `cis(pi*x)` (especially for large `x`).

See also [`cis`](@ref), [`sincospi`](@ref), [`exp`](@ref), [`angle`](@ref).

# Examples
```julia-repl
julia> cispi(10000)
1.0 + 0.0im

julia> cispi(0.25 + 1im)
0.030556854645954562 + 0.03055685464595456im
```

!!! compat "Julia 1.6"
    This function requires Julia 1.6 or later.
"""
function cispi end
````
-/
def cispi_generic_decl : Unit := ()

/--
Julia source: base/complex.jl:618-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cispi(theta::Real) = Complex(reverse(sincospi(theta))...)
```
-/
def cispi_Real {A T : Type} (sincospi : A → T × T) (theta : A) : Complex T :=
  let (s, c) := sincospi theta
  ⟨c, s⟩

/--
Julia source: base/complex.jl:619-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function cispi(z::Complex)
    v = exp(-(pi*imag(z)))
    s, c = sincospi(real(z))
    Complex(v * c, v * s)
end
```
-/
def cispi_Complex {A T : Type} (pi : T) (mulPi : T → A → T) (neg : T → T)
    (exp : T → T) (sincospi : A → T × T) (mul : T → T → T) (z : Complex A) : Complex T :=
  let v := exp (neg (mulPi pi (imag_Complex z)))
  let (s, c) := sincospi (real_Complex z)
  ⟨mul v c, mul v s⟩

/--
Julia source: base/complex.jl:625-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    angle(z)

Compute the phase angle in radians of a complex number `z`.

Returns a number `-pi ≤ angle(z) ≤ pi`, and is thus discontinuous
along the negative real axis.

See also [`atan`](@ref), [`cis`](@ref), [`rad2deg`](@ref).

# Examples
```jldoctest
julia> rad2deg(angle(1 + im))
45.0

julia> rad2deg(angle(1 - im))
-45.0

julia> rad2deg(angle(-1 + 1e-20im))
180.0

julia> rad2deg(angle(-1 - 1e-20im))
-180.0
```
"""
angle(z::Complex) = atan(imag(z), real(z))
````
-/
def angle_Complex {A T : Type} (atan2 : A → A → T) (z : Complex A) : T :=
  atan2 (imag_Complex z) (real_Complex z)

/--
Julia source: base/complex.jl:652-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function log(z::Complex)
    z = float(z)
    T = typeof(real(z))
    T1  = convert(T,5)/convert(T,4)
    T2  = convert(T,3)
    ln2 = log(convert(T,2))  #0.6931471805599453
    x, y = reim(z)
    ρ, k = ssqs(x,y)
    ax = abs(x)
    ay = abs(y)
    if ax < ay
        θ, β = ax, ay
    else
        θ, β = ay, ax
    end
    if k==0 && (0.5 < β*β) && (β <= T1 || ρ < T2)
        ρρ = log1p((β-1)*(β+1)+θ*θ)/2
    else
        ρρ = log(ρ)/2 + k*ln2
    end
    Complex(ρρ, angle(z))
end
```
-/
def log_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (ssqsF : T → T → T × JInt .i64) (z : Complex A) : Complex T :=
  let z := floatC z
  let T1 := o.div (o.ofInt 5) (o.ofInt 4)
  let T2 := o.ofInt 3
  let ln2 := o.log (o.ofInt 2)
  let (x, y) := reim real_Complex imag_Complex z
  let (ρ, k) := ssqsF x y
  let ax := o.abs x
  let ay := o.abs y
  let (θ, β) := if o.lt ax ay then (ax, ay) else (ay, ax)
  let ρρ :=
    if k.val == 0 && o.lt o.half (o.mul β β) && (o.le β T1 || o.lt ρ T2) then
      o.div (o.log1p (o.add (o.mul (o.sub β o.one) (o.add β o.one)) (o.mul θ θ))) o.two
    else
      o.add (o.div (o.log ρ) o.two) (o.mul (o.ofInt k.val) ln2)
  ⟨ρρ, angle_Complex o.atan2 z⟩

/--
Julia source: base/complex.jl:675-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# function log(z::Complex)
#     ar = abs(real(z))
#     ai = abs(imag(z))
#     if ar < ai
#         r = ar/ai
#         re = log(ai) + log1p(r*r)/2
#     else
#         if ar == 0
#             re = isnan(ai) ? ai : -inv(ar)
#         elseif isinf(ai)
#             re = oftype(ar,Inf)
#         else
#             r = ai/ar
#             re = log(ar) + log1p(r*r)/2
#         end
#     end
#     Complex(re, angle(z))
# end

function log10(z::Complex)
    a = log(z)
    a/log(oftype(real(a),10))
end
```
-/
def log10_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (ssqsF : T → T → T × JInt .i64) (z : Complex A) : Complex T :=
  let a := log_Complex o floatC ssqsF z
  div_Complex_Real o.div a (o.log (o.ofInt 10))

/--
Julia source: base/complex.jl:699-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function log2(z::Complex)
    a = log(z)
    a/log(oftype(real(a),2))
end
```
-/
def log2_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (ssqsF : T → T → T × JInt .i64) (z : Complex A) : Complex T :=
  let a := log_Complex o floatC ssqsF z
  div_Complex_Real o.div a (o.log (o.ofInt 2))

/--
Julia source: base/complex.jl:703-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function exp(z::Complex)
    zr, zi = reim(z)
    if isnan(zr)
        Complex(zr, zi==0 ? zi : zr)
    elseif !isfinite(zi)
        if zr == Inf
            Complex(-zr, oftype(zr,NaN))
        elseif zr == -Inf
            Complex(-zero(zr), copysign(zero(zi), zi))
        else
            Complex(oftype(zr,NaN), oftype(zi,NaN))
        end
    else
        er = exp(zr)
        if iszero(zi)
            Complex(er, zi)
        else
            s, c = sincos(zi)
            Complex(er * c, er * s)
        end
    end
end
```
-/
def exp_Complex {T : Type} (o : FloatOps T) (z : Complex T) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isnan zr then
    ⟨zr, if o.eq zi o.zero then zi else zr⟩
  else if !o.isfinite zi then
    if o.eq zr o.inf then
      ⟨o.neg zr, o.nan⟩
    else if o.eq zr o.ninf then
      ⟨o.neg o.zero, o.copysign o.zero zi⟩
    else
      ⟨o.nan, o.nan⟩
  else
    let er := o.exp zr
    if o.iszero zi then
      ⟨er, zi⟩
    else
      let (s, c) := o.sincos zi
      ⟨o.mul er c, o.mul er s⟩

/--
Julia source: base/complex.jl:726-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function expm1(z::Complex{T}) where T<:Real
    Tf = float(T)
    zr,zi = reim(z)
    if isnan(zr)
        Complex(zr, zi==0 ? zi : zr)
    elseif !isfinite(zi)
        if zr == Inf
            Complex(-zr, oftype(zr,NaN))
        elseif zr == -Inf
            Complex(-one(zr), copysign(zero(zi), zi))
        else
            Complex(oftype(zr,NaN), oftype(zi,NaN))
        end
    else
        erm1 = expm1(zr)
        if zi == 0
            Complex(erm1, zi)
        else
            er = erm1+one(erm1)
            if isfinite(er)
                wr = erm1 - 2 * er * (sin(convert(Tf, 0.5) * zi))^2
                return Complex(wr, er * sin(zi))
            else
                s, c = sincos(zi)
                return Complex(er * c, er * s)
            end
        end
    end
end
```
-/
def expm1_Complex {T : Type} (o : FloatOps T) (z : Complex T) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isnan zr then
    ⟨zr, if o.eq zi o.zero then zi else zr⟩
  else if !o.isfinite zi then
    if o.eq zr o.inf then
      ⟨o.neg zr, o.nan⟩
    else if o.eq zr o.ninf then
      ⟨o.neg o.one, o.copysign o.zero zi⟩
    else
      ⟨o.nan, o.nan⟩
  else
    let erm1 := o.expm1 zr
    if o.eq zi o.zero then
      ⟨erm1, zi⟩
    else
      let er := o.add erm1 o.one
      if o.isfinite er then
        let sh := o.sin (o.mul o.half zi)
        let wr := o.sub erm1 (o.mul (o.mul o.two er) (o.mul sh sh))
        ⟨wr, o.mul er (o.sin zi)⟩
      else
        let (s, c) := o.sincos zi
        ⟨o.mul er c, o.mul er s⟩

/--
Julia source: base/complex.jl:756-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function log1p(z::Complex{T}) where T
    zr,zi = reim(z)
    if isfinite(zr)
        isinf(zi) && return log(z)
        # This is based on a well-known trick for log1p of real z,
        # allegedly due to Kahan, only modified to handle real(u) <= 0
        # differently to avoid inaccuracy near z==-2 and for correct branch cut
        u = one(float(T)) + z
        u == 1 ? convert(typeof(u), z) : real(u) <= 0 ? log(u) : log(u)*(z/(u-1))
    elseif isnan(zr)
        Complex(zr, zr)
    elseif isfinite(zi)
        Complex(T(Inf), copysign(zr > 0 ? zero(T) : convert(T, pi), zi))
    else
        Complex(T(Inf), T(NaN))
    end
end
```
-/
def log1p_Complex {T : Type} (o : FloatOps T) (ssqsF : T → T → T × JInt .i64)
    (z : Complex T) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isfinite zr then
    if o.isinf zi then
      log_Complex o id ssqsF z
    else
      let u : Complex T := ⟨o.add o.one zr, zi⟩
      if eq_Complex_Real o.iszero o.eq u o.one then
        z
      else if o.le (real_Complex u) o.zero then
        log_Complex o id ssqsF u
      else
        let uMinus1 : Complex T := ⟨o.sub (real_Complex u) o.one, imag_Complex u⟩
        let q := div_Complex_same o.isinf o.isfinite o.zero o.neg o.nan o.sign o.abs o.le
          o.div o.mul o.mul o.add o.add o.sub o.sub o.div o.mul z uMinus1
        mul_Complex o.mul o.sub o.add (log_Complex o id ssqsF u) q
  else if o.isnan zr then
    ⟨zr, zr⟩
  else if o.isfinite zi then
    ⟨o.inf, o.copysign (if o.lt o.zero zr then o.zero else o.pi) zi⟩
  else
    ⟨o.inf, o.nan⟩

/--
Julia source: base/complex.jl:774-781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function exp2(z::Complex{T}) where T
    z = float(z)
    er = exp2(real(z))
    theta = imag(z) * log(convert(float(T), 2))
    s, c = sincos(theta)
    Complex(er * c, er * s)
end
```
-/
def exp2_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (z : Complex A) : Complex T :=
  let z := floatC z
  let er := o.exp2 (real_Complex z)
  let theta := o.mul (imag_Complex z) (o.log (o.ofInt 2))
  let (s, c) := o.sincos theta
  ⟨o.mul er c, o.mul er s⟩

/--
Julia source: base/complex.jl:782-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function exp10(z::Complex{T}) where T
    z = float(z)
    er = exp10(real(z))
    theta = imag(z) * log(convert(float(T), 10))
    s, c = sincos(theta)
    Complex(er * c, er * s)
end
```
-/
def exp10_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (z : Complex A) : Complex T :=
  let z := floatC z
  let er := o.exp10 (real_Complex z)
  let theta := o.mul (imag_Complex z) (o.log (o.ofInt 10))
  let (s, c) := o.sincos theta
  ⟨o.mul er c, o.mul er s⟩

/--
Julia source: base/complex.jl:790-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# _cpow helper function to avoid method ambiguity with ^(::Complex,::Real)
function _cpow(z::Union{T,Complex{T}}, p::Union{T,Complex{T}}) where T
    z = float(z)
    p = float(p)
    Tf = float(T)
    if isreal(p)
        pᵣ = real(p)
        if isinteger(pᵣ) && abs(pᵣ) < typemax(Int32)
            # |p| < typemax(Int32) serves two purposes: it prevents overflow
            # when converting p to Int, and it also turns out to be roughly
            # the crossover point for exp(p*log(z)) or similar to be faster.
            if iszero(pᵣ) # fix signs of imaginary part for z^0
                zer = flipsign(copysign(zero(Tf),pᵣ), imag(z))
                return Complex(one(Tf), zer)
            end
            ip = convert(Int, pᵣ)
            if isreal(z)
                zᵣ = real(z)
                if ip < 0
                    iszero(z) && return Complex(Tf(NaN),Tf(NaN))
                    re = power_by_squaring(inv(zᵣ), -ip)
                    im = -imag(z)
                else
                    re = power_by_squaring(zᵣ, ip)
                    im = imag(z)
                end
                # slightly tricky to get the correct sign of zero imag. part
                return Complex(re, ifelse(iseven(ip) & signbit(zᵣ), -im, im))
            else
                return ip < 0 ? power_by_squaring(inv(z), -ip) : power_by_squaring(z, ip)
            end
        elseif isreal(z)
            # (note: if both z and p are complex with ±0.0 imaginary parts,
            #  the sign of the ±0.0 imaginary part of the result is ambiguous)
            if iszero(real(z))
                return pᵣ > 0 ? complex(z) : Complex(Tf(NaN),Tf(NaN)) # 0 or NaN+NaN*im
            elseif real(z) > 0
                return Complex(real(z)^pᵣ, z isa Real ? ifelse(real(z) < 1, -imag(p), imag(p)) : flipsign(imag(z), pᵣ))
            else
                zᵣ = real(z)
                rᵖ = (-zᵣ)^pᵣ
                if isfinite(pᵣ)
                    # figuring out the sign of 0.0 when p is a complex number
                    # with zero imaginary part and integer/2 real part could be
                    # improved here, but it's not clear if it's worth it…
                    return rᵖ * complex(cospi(pᵣ), flipsign(sinpi(pᵣ),imag(z)))
                else
                    iszero(rᵖ) && return zero(Complex{Tf}) # no way to get correct signs of 0.0
                    return Complex(Tf(NaN),Tf(NaN)) # non-finite phase angle or NaN input
                end
            end
        else
            rᵖ = abs(z)^pᵣ
            ϕ = pᵣ*angle(z)
        end
    elseif isreal(z)
        iszero(z) && return real(p) > 0 ? complex(z) : Complex(Tf(NaN),Tf(NaN)) # 0 or NaN+NaN*im
        zᵣ = real(z)
        pᵣ, pᵢ = reim(p)
        if zᵣ > 0
            rᵖ = zᵣ^pᵣ
            ϕ = pᵢ*log(zᵣ)
        else
            r = -zᵣ
            θ = copysign(Tf(π),imag(z))
            logr = log(r)
            re_log, im_phase = pᵣ*logr, pᵢ*θ
            lim = log(floatmax(Tf)) - one(Tf)
            rᵖ = (abs(re_log) < lim && abs(im_phase) < lim) ?
                r^pᵣ * exp(-im_phase) : exp(re_log - im_phase)
            ϕ = pᵣ*θ + pᵢ*logr
        end
    else
        pᵣ, pᵢ = reim(p)
        r = abs(z)
        θ = angle(z)
        logr = log(r)
        re_log, im_phase = pᵣ*logr, pᵢ*θ
        lim = log(floatmax(Tf)) - one(Tf)
        rᵖ = (abs(re_log) < lim && abs(im_phase) < lim) ?
            r^pᵣ * exp(-im_phase) : exp(re_log - im_phase)
        ϕ = pᵣ*θ + pᵢ*logr
    end

    if isfinite(ϕ)
        return rᵖ * cis(ϕ)
    else
        iszero(rᵖ) && return zero(Complex{Tf}) # no way to get correct signs of 0.0
        return Complex(Tf(NaN),Tf(NaN)) # non-finite phase angle or NaN input
    end
end
```
-/
def _cpow {A T : Type} (o : FloatOps T)
    (floatArg : RealOrComplex A (Complex A) → Complex T)
    (invC : Complex T → Jl (Complex T))
    (z0 p0 : RealOrComplex A (Complex A)) : Jl (Complex T) := do
  let zWasReal := match z0 with | .real _ => true | .complex _ => false
  let z := floatArg z0
  let p := floatArg p0
  let finish (rp phi : T) : Complex T :=
    if o.isfinite phi then
      mul_Real_Complex o.mul rp (cis_Real o.sincos phi)
    else if o.iszero rp then
      ⟨o.zero, o.zero⟩
    else
      ⟨o.nan, o.nan⟩
  let polarMag (r pr re_log im_phase : T) : T :=
    let lim := o.sub (o.log o.floatmax) o.one
    if o.lt (o.abs re_log) lim && o.lt (o.abs im_phase) lim then
      o.mul (o.pow r pr) (o.exp (o.neg im_phase))
    else
      o.exp (o.sub re_log im_phase)
  if isreal_Complex o.iszero p then
    let pr := real_Complex p
    if o.isinteger pr && o.lt (o.abs pr) (o.ofInt 2147483647) then
      if o.iszero pr then
        let zer := o.flipsign (o.copysign o.zero pr) (imag_Complex z)
        return ⟨o.one, zer⟩
      let ip ← o.toInt pr
      let rops : MulOps T := ⟨o.mul, o.one, o.isone, o.neg⟩
      let cops : MulOps (Complex T) :=
        ⟨mul_Complex o.mul o.sub o.add, ⟨o.one, o.zero⟩, isone_Complex o.isone o.iszero, neg_Complex o.neg⟩
      if isreal_Complex o.iszero z then
        let zr := real_Complex z
        if ip.val < 0 then
          if iszero_Complex o.iszero z then return ⟨o.nan, o.nan⟩
          let re ← power_by_squaring rops (o.inv zr) (-ip)
          let im := o.neg (imag_Complex z)
          return ⟨re, if decide (ip.val % 2 = 0) && o.signbit zr then o.neg im else im⟩
        else
          let re ← power_by_squaring rops zr ip
          let im := imag_Complex z
          return ⟨re, if decide (ip.val % 2 = 0) && o.signbit zr then o.neg im else im⟩
      else
        if ip.val < 0 then do
          let w ← invC z
          power_by_squaring cops w (-ip)
        else
          power_by_squaring cops z ip
    else if isreal_Complex o.iszero z then
      if o.iszero (real_Complex z) then
        return if o.lt o.zero pr then z else ⟨o.nan, o.nan⟩
      else if o.lt o.zero (real_Complex z) then
        let imPart :=
          if zWasReal then
            if o.lt (real_Complex z) o.one then o.neg (imag_Complex p) else imag_Complex p
          else
            o.flipsign (imag_Complex z) pr
        return ⟨o.pow (real_Complex z) pr, imPart⟩
      else
        let zr := real_Complex z
        let rp := o.pow (o.neg zr) pr
        if o.isfinite pr then
          return mul_Real_Complex o.mul rp ⟨o.cospi pr, o.flipsign (o.sinpi pr) (imag_Complex z)⟩
        else if o.iszero rp then
          return ⟨o.zero, o.zero⟩
        else
          return ⟨o.nan, o.nan⟩
    else
      let rp := o.pow (abs_Complex o.hypot z) pr
      let phi := o.mul pr (angle_Complex o.atan2 z)
      return finish rp phi
  else if isreal_Complex o.iszero z then
    if iszero_Complex o.iszero z then
      return if o.lt o.zero (real_Complex p) then z else ⟨o.nan, o.nan⟩
    let zr := real_Complex z
    let (pr, pi) := reim real_Complex imag_Complex p
    if o.lt o.zero zr then
      let rp := o.pow zr pr
      let phi := o.mul pi (o.log zr)
      return finish rp phi
    else
      let r := o.neg zr
      let theta := o.copysign o.pi (imag_Complex z)
      let logr := o.log r
      let re_log := o.mul pr logr
      let im_phase := o.mul pi theta
      let rp := polarMag r pr re_log im_phase
      let phi := o.add (o.mul pr theta) (o.mul pi logr)
      return finish rp phi
  else
    let (pr, pi) := reim real_Complex imag_Complex p
    let r := abs_Complex o.hypot z
    let theta := angle_Complex o.atan2 z
    let logr := o.log r
    let re_log := o.mul pr logr
    let im_phase := o.mul pi theta
    let rp := polarMag r pr re_log im_phase
    let phi := o.add (o.mul pr theta) (o.mul pi logr)
    return finish rp phi

/--
Julia source: base/complex.jl:882-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{T}, p::Complex{T}) where T<:Real = _cpow(z, p)
```
-/
def pow_Complex_Complex {A T : Type} (o : FloatOps T)
    (floatArg : RealOrComplex A (Complex A) → Complex T)
    (invC : Complex T → Jl (Complex T))
    (z p : Complex A) : Jl (Complex T) :=
  _cpow o floatArg invC (.complex z) (.complex p)

/--
Julia source: base/complex.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{T}, p::T) where T<:Real = _cpow(z, p)
```
-/
def pow_Complex_Real_same {A T : Type} (o : FloatOps T)
    (floatArg : RealOrComplex A (Complex A) → Complex T)
    (invC : Complex T → Jl (Complex T))
    (z : Complex A) (p : A) : Jl (Complex T) :=
  _cpow o floatArg invC (.complex z) (.real p)

/--
Julia source: base/complex.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::T, p::Complex{T}) where T<:Real = _cpow(z, p)
```
-/
def pow_Real_Complex_same {A T : Type} (o : FloatOps T)
    (floatArg : RealOrComplex A (Complex A) → Complex T)
    (invC : Complex T → Jl (Complex T))
    (z : A) (p : Complex A) : Jl (Complex T) :=
  _cpow o floatArg invC (.real z) (.complex p)

/--
Julia source: base/complex.jl:885-886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

^(z::Complex, n::Bool) = n ? z : one(z)
```
-/
def pow_Complex_Bool {T : Type} (oneC : Complex T → Complex T) (z : Complex T) (n : Bool) : Complex T :=
  if n then z else oneC z

/--
Julia source: base/complex.jl:887-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex, n::Integer) = z^Complex(n)
```
-/
def pow_Complex_Integer_generic {T I Out : Type} (zeroI : I → I)
    (powCC : Complex T → Complex I → Out) (z : Complex T) (n : I) : Out :=
  powCC z (Complex_Real zeroI n)

/--
Julia source: base/complex.jl:888-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
```
-/
def pow_ComplexFloat_Bool {T : Type} (oneT zeroT : T) (z : Complex T) (n : Bool) : Complex T :=
  if n then z else ⟨oneT, zeroT⟩

/--
Julia source: base/complex.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)        # to resolve ambiguity
```
-/
def pow_ComplexInteger_Bool {t : IntTy} (z : Complex (JInt t)) (n : Bool) : Complex (JInt t) :=
  if n then z else ⟨JInt.lit t 1, JInt.lit t 0⟩

/--
Julia source: base/complex.jl:891-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

^(z::Complex{<:AbstractFloat}, n::Integer) =
    n>=0 ? power_by_squaring(z,n) : power_by_squaring(inv(z),-n)
```
-/
def pow_ComplexFloat_Integer {T : Type} (ops : MulOps (Complex T))
    (invC : Complex T → Jl (Complex T)) (z : Complex T) (n : JInt .i64) : Jl (Complex T) :=
  if n.val ≥ 0 then power_by_squaring ops z n
  else do
    let w ← invC z
    power_by_squaring ops w (-n)

/--
Julia source: base/complex.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{<:Integer}, n::Integer) = power_by_squaring(z,n) # DomainError for n<0
```
-/
def pow_ComplexInteger_Integer {t : IntTy} (z : Complex (JInt t)) (n : JInt .i64) : Jl (Complex (JInt t)) :=
  let ops : MulOps (Complex (JInt t)) :=
    ⟨mul_Complex (· * ·) (· - ·) (· + ·),
     ⟨JInt.lit t 1, JInt.lit t 0⟩,
     isone_Complex (fun x => x.val == 1) (fun x => x.val == 0),
     neg_Complex Neg.neg⟩
  power_by_squaring ops z n

/--
Julia source: base/complex.jl:895-899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function ^(z::Complex{T}, p::S) where {T<:Real,S<:Real}
    P = promote_type(T,S)
    return Complex{P}(z) ^ P(p)
end
```
-/
def pow_Complex_Real_promoted {T S P Out : Type}
    (convertT : T → P) (convertS : S → P) (powCP : Complex P → P → Out)
    (z : Complex T) (p : S) : Out :=
  powCP (Complex_T_Complex convertT z) (convertS p)

/--
Julia source: base/complex.jl:900-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ^(z::T, p::Complex{S}) where {T<:Real,S<:Real}
    P = promote_type(T,S)
    return P(z) ^ Complex{P}(p)
end
```
-/
def pow_Real_Complex_promoted {T S P Out : Type}
    (convertT : T → P) (convertS : S → P) (powPC : P → Complex P → Out)
    (z : T) (p : Complex S) : Out :=
  powPC (convertT z) (Complex_T_Complex convertS p)

/--
Julia source: base/complex.jl:904-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function sin(z::Complex{T}) where T
    F = float(T)
    zr, zi = reim(z)
    if zr == 0
        Complex(F(zr), sinh(zi))
    elseif !isfinite(zr)
        if zi == 0 || isinf(zi)
            Complex(F(NaN), F(zi))
        else
            Complex(F(NaN), F(NaN))
        end
    else
        s, c = sincos(zr)
        Complex(s * cosh(zi), c * sinh(zi))
    end
end
```
-/
def sin_Complex {A T : Type} (o : FloatOps T) (floatT : A → T) (z : Complex A) : Complex T :=
  let zr := floatT (real_Complex z)
  let zi := floatT (imag_Complex z)
  if o.eq zr o.zero then
    ⟨zr, o.sinh zi⟩
  else if !o.isfinite zr then
    if o.eq zi o.zero || o.isinf zi then
      ⟨o.nan, zi⟩
    else
      ⟨o.nan, o.nan⟩
  else
    let (s, c) := o.sincos zr
    ⟨o.mul s (o.cosh zi), o.mul c (o.sinh zi)⟩

/--
Julia source: base/complex.jl:921-940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


function cos(z::Complex{T}) where T
    F = float(T)
    zr, zi = reim(z)
    if zr == 0
        Complex(cosh(zi), isnan(zi) ? F(zr) : -flipsign(F(zr),zi))
    elseif !isfinite(zr)
        if zi == 0
            Complex(F(NaN), isnan(zr) ? zero(F) : -flipsign(F(zi),zr))
        elseif isinf(zi)
            Complex(F(Inf), F(NaN))
        else
            Complex(F(NaN), F(NaN))
        end
    else
        s, c = sincos(zr)
        Complex(c * cosh(zi), -s * sinh(zi))
    end
end
```
-/
def cos_Complex {A T : Type} (o : FloatOps T) (floatT : A → T) (z : Complex A) : Complex T :=
  let zr := floatT (real_Complex z)
  let zi := floatT (imag_Complex z)
  if o.eq zr o.zero then
    ⟨o.cosh zi, if o.isnan zi then zr else o.neg (o.flipsign zr zi)⟩
  else if !o.isfinite zr then
    if o.eq zi o.zero then
      ⟨o.nan, if o.isnan zr then o.zero else o.neg (o.flipsign zi zr)⟩
    else if o.isinf zi then
      ⟨o.inf, o.nan⟩
    else
      ⟨o.nan, o.nan⟩
  else
    let (s, c) := o.sincos zr
    ⟨o.mul c (o.cosh zi), o.neg (o.mul s (o.sinh zi))⟩

/--
Julia source: base/complex.jl:1001-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function tanh(z::Complex{T}) where T
    z = float(z)
    Tf = float(T)
    Ω = prevfloat(typemax(Tf))
    ξ, η = reim(z)
    if isnan(ξ) && η==0 return Complex(ξ, η) end
    if 4*abs(ξ) > asinh(Ω) #Overflow?
        Complex(copysign(one(Tf),ξ),
                copysign(zero(Tf),η*(isfinite(η) ? sin(2*abs(η)) : one(η))))
    else
        t = tan(η)
        β = 1+t*t #sec(η)^2
        s = sinh(ξ)
        ρ = sqrt(1 + s*s) #cosh(ξ)
        if isinf(t)
            Complex(ρ/s,1/t)
        else
            Complex(β*ρ*s,t)/(1+β*s*s)
        end
    end
end
```
-/
def tanh_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (z : Complex A) : Complex T :=
  let z := floatC z
  let Ω := o.prevfloat o.inf
  let (ξ, η) := reim real_Complex imag_Complex z
  if o.isnan ξ && o.eq η o.zero then
    ⟨ξ, η⟩
  else if o.lt (o.asinh Ω) (o.mul (o.ofInt 4) (o.abs ξ)) then
    ⟨o.copysign o.one ξ,
     o.copysign o.zero (o.mul η (if o.isfinite η then o.sin (o.mul o.two (o.abs η)) else o.one))⟩
  else
    let t := o.tan η
    let β := o.add o.one (o.mul t t)
    let s := o.sinh ξ
    let ρ := o.sqrt (o.add o.one (o.mul s s))
    if o.isinf t then
      ⟨o.div ρ s, o.div o.one t⟩
    else
      div_Complex_Real o.div ⟨o.mul (o.mul β ρ) s, t⟩ (o.add o.one (o.mul β (o.mul s s)))

/--
Julia source: base/complex.jl:941-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


function tan(z::Complex)
    zr, zi = reim(z)
    w = tanh(Complex(-zi, zr))
    Complex(imag(w), -real(w))
end
```
-/
def tan_Complex {A T : Type} (o : FloatOps T) (negA : A → A)
    (floatC : Complex A → Complex T) (z : Complex A) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  let w := tanh_Complex o floatC ⟨negA zi, zr⟩
  ⟨imag_Complex w, o.neg (real_Complex w)⟩

/--
Julia source: base/complex.jl:948-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function asin(z::Complex)
    zr, zi = reim(z)
    if isinf(zr) && isinf(zi)
        return Complex(copysign(oftype(zr,pi)/4, zr),zi)
    elseif isnan(zi) && isinf(zr)
        return Complex(zi, oftype(zr, Inf))
    end
    ξ = zr == 0       ? zr :
        !isfinite(zr) ? oftype(zr,pi)/2 * sign(zr) :
        atan(zr, real(sqrt(1-z)*sqrt(1+z)))
    η = asinh(copysign(imag(sqrt(conj(1-z))*sqrt(1+z)), imag(z)))
    Complex(ξ,η)
end
```
-/
def asin_Complex {T : Type} (o : FloatOps T) (sqrtC : Complex T → Complex T)
    (z : Complex T) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isinf zr && o.isinf zi then
    ⟨o.copysign (o.div o.pi (o.ofInt 4)) zr, zi⟩
  else if o.isnan zi && o.isinf zr then
    ⟨zi, o.inf⟩
  else
    let oneMinusZ : Complex T := sub_Real_Complex o.sub (fun _ y => y) o.neg o.one z
    let onePlusZ : Complex T := add_Real_Complex o.add (fun a b => (a, b)) o.one z
    let s1 := sqrtC oneMinusZ
    let s2 := sqrtC onePlusZ
    let ξ :=
      if o.eq zr o.zero then zr
      else if !o.isfinite zr then o.mul (o.div o.pi o.two) (o.sign zr)
      else o.atan2 zr (real_Complex (mul_Complex o.mul o.sub o.add s1 s2))
    let s1c := sqrtC (conj_Complex o.neg oneMinusZ)
    let η := o.asinh (o.copysign (imag_Complex (mul_Complex o.mul o.sub o.add s1c s2)) (imag_Complex z))
    ⟨ξ, η⟩

/--
Julia source: base/complex.jl:962-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function acos(z::Complex)
    z = float(z)
    zr, zi = reim(z)
    if isnan(zr)
        if isinf(zi) return Complex(zr, -zi)
        else         return Complex(zr, zr) end
    elseif isnan(zi)
        if isinf(zr) return Complex(zi, abs(zr))
        elseif zr==0 return Complex(oftype(zr,pi)/2, zi)
        else         return Complex(zi, zi) end
    elseif zr==zi==0
        return Complex(oftype(zr,pi)/2, -zi)
    elseif zr==Inf && zi===0.0
        return Complex(zi, -zr)
    elseif zr==-Inf && zi===-0.0
        return Complex(oftype(zi,pi), -zr)
    end
    ξ = 2*atan(real(sqrt(1-z)), real(sqrt(1+z)))
    η = asinh(imag(sqrt(conj(1+z))*sqrt(1-z)))
    if isinf(zr) && isinf(zi) ξ -= oftype(η,pi)/4 * sign(zr) end
    Complex(ξ,η)
end
```
-/
def acos_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (sqrtC : Complex T → Complex T) (z : Complex A) : Complex T :=
  let z := floatC z
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isnan zr then
    if o.isinf zi then ⟨zr, o.neg zi⟩ else ⟨zr, zr⟩
  else if o.isnan zi then
    if o.isinf zr then ⟨zi, o.abs zr⟩
    else if o.eq zr o.zero then ⟨o.div o.pi o.two, zi⟩
    else ⟨zi, zi⟩
  else if o.eq zr zi && o.eq zi o.zero then
    ⟨o.div o.pi o.two, o.neg zi⟩
  else if o.eq zr o.inf && o.identical zi o.zero then
    ⟨zi, o.neg zr⟩
  else if o.eq zr o.ninf && o.identical zi o.nzero then
    ⟨o.pi, o.neg zr⟩
  else
    let oneMinusZ : Complex T := sub_Real_Complex o.sub (fun _ y => y) o.neg o.one z
    let onePlusZ : Complex T := add_Real_Complex o.add (fun a b => (a, b)) o.one z
    let s1 := sqrtC oneMinusZ
    let s2 := sqrtC onePlusZ
    let ξ0 := o.mul o.two (o.atan2 (real_Complex s1) (real_Complex s2))
    let s2c := sqrtC (conj_Complex o.neg onePlusZ)
    let η := o.asinh (imag_Complex (mul_Complex o.mul o.sub o.add s2c s1))
    let ξ := if o.isinf zr && o.isinf zi then
        o.sub ξ0 (o.mul (o.div o.pi (o.ofInt 4)) (o.sign zr))
      else ξ0
    ⟨ξ, η⟩

/--
Julia source: base/complex.jl:1047-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function atanh(z::Complex{T}) where T
    z = float(z)
    Tf = float(T)
    x, y = reim(z)
    ax = abs(x)
    ay = abs(y)
    θ = sqrt(floatmax(Tf))/4
    if ax > θ || ay > θ #Prevent overflow
        if isnan(y)
            if isinf(x)
                return Complex(copysign(zero(x),x), y)
            else
                return Complex(real(inv(z)), y)
            end
        end
        if isinf(y)
            return Complex(copysign(zero(x),x), copysign(oftype(y,pi)/2, y))
        end
        return Complex(real(inv(z)), copysign(oftype(y,pi)/2, y))
    end
    β = copysign(one(Tf), x)
    z *= β
    x, y = reim(z)
    if x == 1
        if y == 0
            ξ = oftype(x, Inf)
            η = y
        else
            ξ = log(sqrt(sqrt(muladd(y, y, 4)))/sqrt(ay))
            η = copysign(oftype(y,pi)/2 + atan(ay/2), y)/2
        end
    else #Normal case
        ysq = ay^2
        if x == 0
            ξ = x
        else
            ξ = log1p(4x/(muladd(1-x, 1-x, ysq)))/4
        end
        η = angle(Complex((1-x)*(1+x)-ysq, 2y))/2
    end
    β * Complex(ξ, η)
end
```
-/
def atanh_Complex {A T : Type} (o : FloatOps T) (floatC : Complex A → Complex T)
    (invC : Complex T → Complex T) (z : Complex A) : Complex T :=
  let z := floatC z
  let (x, y) := reim real_Complex imag_Complex z
  let ax := o.abs x
  let ay := o.abs y
  let θ := o.div (o.sqrt o.floatmax) (o.ofInt 4)
  if o.lt θ ax || o.lt θ ay then
    if o.isnan y then
      if o.isinf x then ⟨o.copysign o.zero x, y⟩
      else ⟨real_Complex (invC z), y⟩
    else if o.isinf y then
      ⟨o.copysign o.zero x, o.copysign (o.div o.pi o.two) y⟩
    else
      ⟨real_Complex (invC z), o.copysign (o.div o.pi o.two) y⟩
  else
    let β := o.copysign o.one x
    let z := mul_Complex_Real o.mul z β
    let (x, y) := reim real_Complex imag_Complex z
    let (ξ, η) :=
      if o.eq x o.one then
        if o.eq y o.zero then
          (o.inf, y)
        else
          let ξ := o.log (o.div (o.sqrt (o.sqrt (o.muladd y y (o.ofInt 4)))) (o.sqrt ay))
          let η := o.div (o.copysign (o.add (o.div o.pi o.two) (o.atan (o.div ay o.two))) y) o.two
          (ξ, η)
      else
        let ysq := o.mul ay ay
        let ξ :=
          if o.eq x o.zero then x
          else o.div (o.log1p (o.div (o.mul (o.ofInt 4) x) (o.muladd (o.sub o.one x) (o.sub o.one x) ysq))) (o.ofInt 4)
        let η := o.div (angle_Complex o.atan2 ⟨o.sub (o.mul (o.sub o.one x) (o.add o.one x)) ysq, o.mul o.two y⟩) o.two
        (ξ, η)
    mul_Real_Complex o.mul β ⟨ξ, η⟩

/--
Julia source: base/complex.jl:985-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function atan(z::Complex)
    w = atanh(Complex(-imag(z),real(z)))
    Complex(imag(w),-real(w))
end
```
-/
def atan_Complex {A T : Type} (o : FloatOps T) (negA : A → A)
    (floatC : Complex A → Complex T) (invC : Complex T → Complex T)
    (z : Complex A) : Complex T :=
  let w := atanh_Complex o floatC invC ⟨negA (imag_Complex z), real_Complex z⟩
  ⟨imag_Complex w, o.neg (real_Complex w)⟩

/--
Julia source: base/complex.jl:990-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function sinh(z::Complex)
    zr, zi = reim(z)
    w = sin(Complex(zi, zr))
    Complex(imag(w),real(w))
end
```
-/
def sinh_Complex {A T : Type} (o : FloatOps T) (floatT : A → T)
    (z : Complex A) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  let w := sin_Complex o floatT ⟨zi, zr⟩
  ⟨imag_Complex w, real_Complex w⟩

/--
Julia source: base/complex.jl:996-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function cosh(z::Complex)
    zr, zi = reim(z)
    cos(Complex(zi,-zr))
end
```
-/
def cosh_Complex {A T : Type} (o : FloatOps T) (negA : A → A) (floatT : A → T)
    (z : Complex A) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  cos_Complex o floatT ⟨zi, negA zr⟩

/--
Julia source: base/complex.jl:1023-1027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function asinh(z::Complex)
    w = asin(Complex(-imag(z),real(z)))
    Complex(imag(w),-real(w))
end
```
-/
def asinh_Complex {T : Type} (o : FloatOps T) (sqrtC : Complex T → Complex T)
    (z : Complex T) : Complex T :=
  let w := asin_Complex o sqrtC ⟨o.neg (imag_Complex z), real_Complex z⟩
  ⟨imag_Complex w, o.neg (real_Complex w)⟩

/--
Julia source: base/complex.jl:1028-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function acosh(z::Complex)
    zr, zi = reim(z)
    if isnan(zr) || isnan(zi)
        if isinf(zr) || isinf(zi)
            return Complex(oftype(zr, Inf), oftype(zi, NaN))
        else
            return Complex(oftype(zr, NaN), oftype(zi, NaN))
        end
    elseif zr==-Inf && zi===-0.0 #Edge case is wrong - WHY?
        return Complex(oftype(zr,Inf), oftype(zi, -pi))
    end
    ξ = asinh(real(sqrt(conj(z-1))*sqrt(z+1)))
    η = 2*atan(imag(sqrt(z-1)),real(sqrt(z+1)))
    if isinf(zr) && isinf(zi)
        η -= oftype(η,pi)/4 * sign(zi) * sign(zr)
    end
    Complex(ξ, η)
end
```
-/
def acosh_Complex {T : Type} (o : FloatOps T) (sqrtC : Complex T → Complex T)
    (z : Complex T) : Complex T :=
  let (zr, zi) := reim real_Complex imag_Complex z
  if o.isnan zr || o.isnan zi then
    if o.isinf zr || o.isinf zi then ⟨o.inf, o.nan⟩ else ⟨o.nan, o.nan⟩
  else if o.eq zr o.ninf && o.identical zi o.nzero then
    ⟨o.inf, o.neg o.pi⟩
  else
    let zMinus1 : Complex T := sub_Complex_Real o.sub (fun a b => (a, b)) z o.one
    let zPlus1 : Complex T := add_Complex_Real o.add (fun a b => (a, b)) z o.one
    let s1c := sqrtC (conj_Complex o.neg zMinus1)
    let s1 := sqrtC zMinus1
    let s2 := sqrtC zPlus1
    let ξ := o.asinh (real_Complex (mul_Complex o.mul o.sub o.add s1c s2))
    let η0 := o.mul o.two (o.atan2 (imag_Complex s1) (real_Complex s2))
    let η := if o.isinf zr && o.isinf zi then
        o.sub η0 (o.mul (o.mul (o.div o.pi (o.ofInt 4)) (o.sign zi)) (o.sign zr))
      else η0
    ⟨ξ, η⟩

/--
Julia source: base/complex.jl:1090-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

#Rounding complex numbers
#Requires two different RoundingModes for the real and imaginary components
"""
    round(z::Complex[, RoundingModeReal, [RoundingModeImaginary]])
    round(z::Complex[, RoundingModeReal, [RoundingModeImaginary]]; digits=0, base=10)
    round(z::Complex[, RoundingModeReal, [RoundingModeImaginary]]; sigdigits, base=10)

Return the nearest integral value of the same type as the complex-valued `z` to `z`,
breaking ties using the specified [`RoundingMode`](@ref)s. The first
[`RoundingMode`](@ref) is used for rounding the real components while the
second is used for rounding the imaginary components.


`RoundingModeReal` and `RoundingModeImaginary` default to [`RoundNearest`](@ref),
which rounds to the nearest integer, with ties (fractional values of 0.5)
being rounded to the nearest even integer.

# Examples
```jldoctest
julia> round(3.14 + 4.5im)
3.0 + 4.0im

julia> round(3.14 + 4.5im, RoundUp, RoundNearestTiesUp)
4.0 + 5.0im

julia> round(3.14159 + 4.512im; digits = 1)
3.1 + 4.5im

julia> round(3.14159 + 4.512im; sigdigits = 3)
3.14 + 4.51im
```
"""
function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
    Complex(round(real(z), rr; kwargs...),
            round(imag(z), ri; kwargs...))
end
````
-/
def round_Complex {T RM KW R : Type} (roundElem : T → RM → KW → R)
    (z : Complex T) (rr : RM) (ri : RM := rr) (kw : KW) : Complex R :=
  ⟨roundElem (real_Complex z) rr kw, roundElem (imag_Complex z) ri kw⟩

/--
Julia source: base/complex.jl:1127-1129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


float(z::Complex{<:AbstractFloat}) = z
```
-/
def float_Complex_AbstractFloat {T : Type} (z : Complex T) : Complex T := z

/--
Julia source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(z::Complex) = Complex(float(real(z)), float(imag(z)))
```
-/
def float_Complex {T F : Type} (floatT : T → F) (z : Complex T) : Complex F :=
  ⟨floatT (real_Complex z), floatT (imag_Complex z)⟩

/--
Julia source: base/complex.jl:1131-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
```
-/
def big_Type_Complex {R B : Type} (bigT : R → B) (T : R) : ComplexTy B :=
  .complex (bigT T)

/--
Julia source: base/complex.jl:1133-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(z::Complex{T}) where {T<:Real} = Complex{big(T)}(z)
```
-/
def big_Complex {T B : Type} (convertBig : T → B) (z : Complex T) : Complex B :=
  Complex_T_Complex convertBig z

/--
Julia source: base/complex.jl:1134-1153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

## Array operations on complex numbers ##
"""
    complex(A::AbstractArray)

Return an array containing the complex analog of each entry in array `A`.

Equivalent to `complex.(A)`, except that the return value may share memory with all or
part of `A` in accordance with the behavior of `convert(T, A)` given output type `T`.

# Examples
```jldoctest
julia> complex([1, 2, 3])
3-element Vector{Complex{Int64}}:
 1 + 0im
 2 + 0im
 3 + 0im
```
"""
complex(A::AbstractArray{<:Complex}) = A
````
-/
def complex_AbstractArray_Complex {Arr : Type} (A : Arr) : Arr := A

/--
Julia source: base/complex.jl:1154-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function complex(A::AbstractArray{T}) where T
    if !isconcretetype(T)
        error("`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
    end
    convert(AbstractArray{typeof(complex(zero(T)))}, A)
end
```
-/
def complex_AbstractArray {Arr Out : Type} (isconcretetype : Bool)
    (convertArray : Arr → Out) (A : Arr) : Jl Out :=
  if !isconcretetype then
    .error (.argumentError "`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
  else
    .ok (convertArray A)

/--
Julia source: base/complex.jl:1161-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Machine epsilon for complex ##

eps(z::Complex{<:AbstractFloat}) = hypot(eps(real(z)), eps(imag(z)))
```
-/
def eps_Complex {T R : Type} (eps : T → T) (hypot : T → T → R) (z : Complex T) : R :=
  hypot (eps (real_Complex z)) (eps (imag_Complex z))

/--
Julia source: base/complex.jl:1165-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

eps(::Type{Complex{T}}) where {T<:AbstractFloat} = sqrt(2*one(T))*eps(T)
```
-/
def eps_Type_Complex {T R : Type} (twoOne epsT : T) (sqrt : T → R) (mul : R → T → R) : R :=
  mul (sqrt twoOne) epsT

/-! ## Concrete instantiations on `ComplexF64`, `Complex (JInt t)`, and `Complex Bool` -/

/-- `abs(x::Signed) = flipsign(x, x)` (`base/int.jl:234`), `abs(x::Unsigned) = x`. -/
def iabs {t : IntTy} (x : JInt t) : JInt t :=
  if t.signed && x.val < 0 then -x else x

/-- `sign(x)` of a `JInt t` converted to `F64`. -/
def isignF64 {t : IntTy} (x : JInt t) : F64 :=
  if x.val < 0 then F64.neg F64.one
  else if 0 < x.val then F64.one
  else Fl64.pzero

/-- `/(a::Complex{T}, b::Complex{T}) where T<:Real` (`base/complex.jl:360-377`) specialized to `T = JInt t`. -/
def div_Complex_JInt {t : IntTy} (a b : Complex (JInt t)) : ComplexF64 :=
  div_Complex_same
    (fun _ => false)
    (fun _ => true)
    Fl64.pzero F64.neg F64.nan isignF64 iabs (fun x y => decide (x.val ≤ y.val))
    (fun x y => F64.div (F64.ofJInt x) (F64.ofJInt y))
    (fun r x => F64.mul r (F64.ofJInt x))
    (fun x r => F64.mul (F64.ofJInt x) r)
    (fun x r => F64.add (F64.ofJInt x) r)
    (fun r x => F64.add r (F64.ofJInt x))
    (fun r x => F64.sub r (F64.ofJInt x))
    (fun x r => F64.sub (F64.ofJInt x) r)
    F64.div F64.mul a b

/-- Scalar transcendental and exponentiation callees from `base/math.jl` and `base/special/` on `F64`. -/
structure F64Transcendentals where
  sincos : F64 → F64 × F64
  sincospi : F64 → F64 × F64
  tan : F64 → F64
  asin : F64 → F64
  acos : F64 → F64
  atan : F64 → F64
  atan2 : F64 → F64 → F64
  sinh : F64 → F64
  cosh : F64 → F64
  tanh : F64 → F64
  asinh : F64 → F64
  acosh : F64 → F64
  atanh : F64 → F64
  exp : F64 → F64
  expm1 : F64 → F64
  exp2 : F64 → F64
  exp10 : F64 → F64
  log : F64 → F64
  log1p : F64 → F64
  pow : F64 → F64 → F64
  sqrt : F64 → F64
  ldexp : F64 → Int → F64
  exponent : F64 → Int

def isone_F64 (x : F64) : Bool := F64.eq x F64.one
def isinteger_F64 (x : F64) : Bool :=
  F64.isfinite x && (F64.iszero x || ((F64.toRat x).1 % ((F64.toRat x).2 : Int) == 0))
def toInt_F64 (x : F64) : Jl (JInt .i64) :=
  if F64.iszero x then .ok (JInt.lit .i64 0)
  else
    let v := (F64.toRat x).1.tdiv ((F64.toRat x).2 : Int)
    if F64.isfinite x && ((F64.toRat x).1 % ((F64.toRat x).2 : Int) == 0) &&
       decide (IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) then
      .ok (JInt.lit .i64 v)
    else .error (.inexactError "Int64")
def sqrt_F64 (x : F64) : F64 :=
  match F64.sqrt x with | .ok r => r | .error _ => F64.nan
def hypot_F64 (x y : F64) : F64 :=
  match Fl64.hypot x y with | .ok r => r | .error _ => F64.nan
def exponent_F64 (x : F64) : Int :=
  match F64.exponent x with | .ok k => k | .error _ => 0

/-- Concrete `FloatOps F64` binding all `base/float.jl` operations on `F64` and taking `tr : F64Transcendentals` for `base/math.jl` and `base/special/` callees. -/
def f64Ops (tr : F64Transcendentals) : FloatOps F64 where
  zero := Fl64.pzero
  nzero := Fl64.nzero
  one := F64.one
  two := Fl64.two
  half := Fl64.half
  inf := Fl64.inf
  ninf := Fl64.ninf
  nan := F64.nan
  pi := Fl64.pi
  floatmin := F64.floatmin
  floatmax := F64.floatmax
  eps := Fl64.eps
  epsOf := fun x => F64.eps x
  ofInt := F64.ofInt
  isnan := F64.isnan
  isinf := F64.isinf
  isfinite := F64.isfinite
  iszero := F64.iszero
  isone := isone_F64
  isinteger := isinteger_F64
  toInt := toInt_F64
  signbit := F64.signbit
  eq := F64.eq
  lt := F64.lt
  le := F64.le
  isequal := F64.isequal
  identical := (· == ·)
  pos := id
  neg := F64.neg
  abs := F64.abs
  sign := Fl64.sign
  copysign := Fl64.copysign
  flipsign := Fl64.flipsign
  max := Fl64.max
  add := F64.add
  sub := F64.sub
  mul := F64.mul
  div := F64.div
  muladd := F64.muladd
  inv := F64.div F64.one
  pow := tr.pow
  sqrt := tr.sqrt
  hypot := hypot_F64
  exp := tr.exp
  expm1 := tr.expm1
  exp2 := tr.exp2
  exp10 := tr.exp10
  log := tr.log
  log1p := tr.log1p
  sin := fun x => (tr.sincos x).1
  cos := fun x => (tr.sincos x).2
  tan := tr.tan
  asin := tr.asin
  acos := tr.acos
  atan := tr.atan
  atan2 := tr.atan2
  sincos := tr.sincos
  sincospi := tr.sincospi
  sinpi := fun x => (tr.sincospi x).1
  cospi := fun x => (tr.sincospi x).2
  sinh := tr.sinh
  cosh := tr.cosh
  tanh := tr.tanh
  asinh := tr.asinh
  acosh := tr.acosh
  atanh := tr.atanh
  nextfloat := F64.nextfloat
  prevfloat := F64.prevfloat
  ldexp := tr.ldexp
  exponent := tr.exponent

@[simp] theorem f64Ops_zero (tr : F64Transcendentals) : (f64Ops tr).zero = Fl64.pzero := rfl
@[simp] theorem f64Ops_nzero (tr : F64Transcendentals) : (f64Ops tr).nzero = Fl64.nzero := rfl
@[simp] theorem f64Ops_one (tr : F64Transcendentals) : (f64Ops tr).one = F64.one := rfl
@[simp] theorem f64Ops_two (tr : F64Transcendentals) : (f64Ops tr).two = Fl64.two := rfl
@[simp] theorem f64Ops_half (tr : F64Transcendentals) : (f64Ops tr).half = Fl64.half := rfl
@[simp] theorem f64Ops_inf (tr : F64Transcendentals) : (f64Ops tr).inf = Fl64.inf := rfl
@[simp] theorem f64Ops_ninf (tr : F64Transcendentals) : (f64Ops tr).ninf = Fl64.ninf := rfl
@[simp] theorem f64Ops_nan (tr : F64Transcendentals) : (f64Ops tr).nan = F64.nan := rfl
@[simp] theorem f64Ops_pi (tr : F64Transcendentals) : (f64Ops tr).pi = Fl64.pi := rfl
@[simp] theorem f64Ops_floatmin (tr : F64Transcendentals) : (f64Ops tr).floatmin = F64.floatmin := rfl
@[simp] theorem f64Ops_floatmax (tr : F64Transcendentals) : (f64Ops tr).floatmax = F64.floatmax := rfl
@[simp] theorem f64Ops_eps (tr : F64Transcendentals) : (f64Ops tr).eps = Fl64.eps := rfl
@[simp] theorem f64Ops_epsOf (tr : F64Transcendentals) : (f64Ops tr).epsOf = fun x => F64.eps x := rfl
@[simp] theorem f64Ops_ofInt (tr : F64Transcendentals) : (f64Ops tr).ofInt = F64.ofInt := rfl
@[simp] theorem f64Ops_isnan (tr : F64Transcendentals) : (f64Ops tr).isnan = F64.isnan := rfl
@[simp] theorem f64Ops_isinf (tr : F64Transcendentals) : (f64Ops tr).isinf = F64.isinf := rfl
@[simp] theorem f64Ops_isfinite (tr : F64Transcendentals) : (f64Ops tr).isfinite = F64.isfinite := rfl
@[simp] theorem f64Ops_iszero (tr : F64Transcendentals) : (f64Ops tr).iszero = F64.iszero := rfl
@[simp] theorem f64Ops_isone (tr : F64Transcendentals) : (f64Ops tr).isone = isone_F64 := rfl
@[simp] theorem f64Ops_isinteger (tr : F64Transcendentals) : (f64Ops tr).isinteger = isinteger_F64 := rfl
@[simp] theorem f64Ops_toInt (tr : F64Transcendentals) : (f64Ops tr).toInt = toInt_F64 := rfl
@[simp] theorem f64Ops_signbit (tr : F64Transcendentals) : (f64Ops tr).signbit = F64.signbit := rfl
@[simp] theorem f64Ops_eq (tr : F64Transcendentals) : (f64Ops tr).eq = F64.eq := rfl
@[simp] theorem f64Ops_lt (tr : F64Transcendentals) : (f64Ops tr).lt = F64.lt := rfl
@[simp] theorem f64Ops_le (tr : F64Transcendentals) : (f64Ops tr).le = F64.le := rfl
@[simp] theorem f64Ops_isequal (tr : F64Transcendentals) : (f64Ops tr).isequal = F64.isequal := rfl
@[simp] theorem f64Ops_identical (tr : F64Transcendentals) : (f64Ops tr).identical = (· == ·) := rfl
@[simp] theorem f64Ops_pos (tr : F64Transcendentals) : (f64Ops tr).pos = id := rfl
@[simp] theorem f64Ops_neg (tr : F64Transcendentals) : (f64Ops tr).neg = F64.neg := rfl
@[simp] theorem f64Ops_abs (tr : F64Transcendentals) : (f64Ops tr).abs = F64.abs := rfl
@[simp] theorem f64Ops_sign (tr : F64Transcendentals) : (f64Ops tr).sign = Fl64.sign := rfl
@[simp] theorem f64Ops_copysign (tr : F64Transcendentals) : (f64Ops tr).copysign = Fl64.copysign := rfl
@[simp] theorem f64Ops_flipsign (tr : F64Transcendentals) : (f64Ops tr).flipsign = Fl64.flipsign := rfl
@[simp] theorem f64Ops_max (tr : F64Transcendentals) : (f64Ops tr).max = Fl64.max := rfl
@[simp] theorem f64Ops_add (tr : F64Transcendentals) : (f64Ops tr).add = F64.add := rfl
@[simp] theorem f64Ops_sub (tr : F64Transcendentals) : (f64Ops tr).sub = F64.sub := rfl
@[simp] theorem f64Ops_mul (tr : F64Transcendentals) : (f64Ops tr).mul = F64.mul := rfl
@[simp] theorem f64Ops_div (tr : F64Transcendentals) : (f64Ops tr).div = F64.div := rfl
@[simp] theorem f64Ops_muladd (tr : F64Transcendentals) : (f64Ops tr).muladd = F64.muladd := rfl
@[simp] theorem f64Ops_inv (tr : F64Transcendentals) : (f64Ops tr).inv = F64.div F64.one := rfl
@[simp] theorem f64Ops_pow (tr : F64Transcendentals) : (f64Ops tr).pow = tr.pow := rfl
@[simp] theorem f64Ops_sqrt (tr : F64Transcendentals) : (f64Ops tr).sqrt = tr.sqrt := rfl
@[simp] theorem f64Ops_hypot (tr : F64Transcendentals) : (f64Ops tr).hypot = hypot_F64 := rfl
@[simp] theorem f64Ops_exp (tr : F64Transcendentals) : (f64Ops tr).exp = tr.exp := rfl
@[simp] theorem f64Ops_expm1 (tr : F64Transcendentals) : (f64Ops tr).expm1 = tr.expm1 := rfl
@[simp] theorem f64Ops_exp2 (tr : F64Transcendentals) : (f64Ops tr).exp2 = tr.exp2 := rfl
@[simp] theorem f64Ops_exp10 (tr : F64Transcendentals) : (f64Ops tr).exp10 = tr.exp10 := rfl
@[simp] theorem f64Ops_log (tr : F64Transcendentals) : (f64Ops tr).log = tr.log := rfl
@[simp] theorem f64Ops_log1p (tr : F64Transcendentals) : (f64Ops tr).log1p = tr.log1p := rfl
@[simp] theorem f64Ops_sin (tr : F64Transcendentals) : (f64Ops tr).sin = fun x => (tr.sincos x).1 := rfl
@[simp] theorem f64Ops_cos (tr : F64Transcendentals) : (f64Ops tr).cos = fun x => (tr.sincos x).2 := rfl
@[simp] theorem f64Ops_tan (tr : F64Transcendentals) : (f64Ops tr).tan = tr.tan := rfl
@[simp] theorem f64Ops_asin (tr : F64Transcendentals) : (f64Ops tr).asin = tr.asin := rfl
@[simp] theorem f64Ops_acos (tr : F64Transcendentals) : (f64Ops tr).acos = tr.acos := rfl
@[simp] theorem f64Ops_atan (tr : F64Transcendentals) : (f64Ops tr).atan = tr.atan := rfl
@[simp] theorem f64Ops_atan2 (tr : F64Transcendentals) : (f64Ops tr).atan2 = tr.atan2 := rfl
@[simp] theorem f64Ops_sincos (tr : F64Transcendentals) : (f64Ops tr).sincos = tr.sincos := rfl
@[simp] theorem f64Ops_sincospi (tr : F64Transcendentals) : (f64Ops tr).sincospi = tr.sincospi := rfl
@[simp] theorem f64Ops_sinpi (tr : F64Transcendentals) : (f64Ops tr).sinpi = fun x => (tr.sincospi x).1 := rfl
@[simp] theorem f64Ops_cospi (tr : F64Transcendentals) : (f64Ops tr).cospi = fun x => (tr.sincospi x).2 := rfl
@[simp] theorem f64Ops_sinh (tr : F64Transcendentals) : (f64Ops tr).sinh = tr.sinh := rfl
@[simp] theorem f64Ops_cosh (tr : F64Transcendentals) : (f64Ops tr).cosh = tr.cosh := rfl
@[simp] theorem f64Ops_tanh (tr : F64Transcendentals) : (f64Ops tr).tanh = tr.tanh := rfl
@[simp] theorem f64Ops_asinh (tr : F64Transcendentals) : (f64Ops tr).asinh = tr.asinh := rfl
@[simp] theorem f64Ops_acosh (tr : F64Transcendentals) : (f64Ops tr).acosh = tr.acosh := rfl
@[simp] theorem f64Ops_atanh (tr : F64Transcendentals) : (f64Ops tr).atanh = tr.atanh := rfl
@[simp] theorem f64Ops_nextfloat (tr : F64Transcendentals) : (f64Ops tr).nextfloat = F64.nextfloat := rfl
@[simp] theorem f64Ops_prevfloat (tr : F64Transcendentals) : (f64Ops tr).prevfloat = F64.prevfloat := rfl
@[simp] theorem f64Ops_ldexp (tr : F64Transcendentals) : (f64Ops tr).ldexp = tr.ldexp := rfl
@[simp] theorem f64Ops_exponent (tr : F64Transcendentals) : (f64Ops tr).exponent = tr.exponent := rfl

/-- `ssqs(x::Float64, y::Float64)` (`base/complex.jl:519-531`) instantiated on `F64`. -/
def ssqs_F64 (x y : F64) : F64 × JInt .i64 :=
  ssqs F64.isfinite F64.isinf F64.eq F64.lt
    Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
    Fl64.max F64.add F64.mul F64.div F64.nextfloat exponent_F64 F64.ldexp x y

/-- `ssqs(x::Float64, y::Float64)` (`base/complex.jl:519-531`) with `tr : F64Transcendentals`. -/
def ssqs_F64_tr (tr : F64Transcendentals) (x y : F64) : F64 × JInt .i64 :=
  ssqs F64.isfinite F64.isinf F64.eq F64.lt
    Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
    Fl64.max F64.add F64.mul F64.div F64.nextfloat tr.exponent tr.ldexp x y

/-- `sqrt(z::ComplexF64)` (`base/complex.jl:533-558`) instantiated on `F64`. -/
def sqrt_ComplexF64 (z : ComplexF64) : ComplexF64 :=
  sqrt_Complex id F64.isfinite F64.isinf F64.eq F64.lt
    Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
    Fl64.max F64.add F64.mul F64.div Fl64.copysign F64.nextfloat exponent_F64 F64.ldexp sqrt_F64 z

/-- `sqrt(z::ComplexF64)` (`base/complex.jl:533-558`) with `tr : F64Transcendentals`. -/
def sqrt_ComplexF64_tr (tr : F64Transcendentals) (z : ComplexF64) : ComplexF64 :=
  sqrt_Complex id F64.isfinite F64.isinf F64.eq F64.lt
    Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
    Fl64.max F64.add F64.mul F64.div Fl64.copysign F64.nextfloat tr.exponent tr.ldexp tr.sqrt z

/-- `inv(z::Complex)` (`base/complex.jl:283-287`) instantiated on `ComplexF64`. -/
def inv_Complex_F64 (z : ComplexF64) : ComplexF64 :=
  inv_Complex F64.isinf (fun _ => Fl64.pzero) F64.neg Fl64.copysign Fl64.flipsign
    F64.add F64.mul F64.div z

/-- `inv(z::Complex{T}) where T<:Union{Float16,Float32}` (`base/complex.jl:476-481`) instantiated with `F64` arithmetic. -/
def inv_Complex_SmallFloat_F64 (z : ComplexF64) : ComplexF64 :=
  inv_Complex_SmallFloat id F64.isinf Fl64.pzero F64.neg Fl64.copysign Fl64.flipsign
    (F64.div F64.one) F64.mul F64.neg F64.muladd id z

/-- `/(z::Complex{T}, w::Complex{T}) where T<:Union{Float16,Float32}` (`base/complex.jl:379-392`) instantiated with `F64` arithmetic. -/
def div_Complex_SmallFloat_F64 (z w : ComplexF64) : ComplexF64 :=
  div_Complex_SmallFloat id F64.isinf F64.isfinite Fl64.pzero F64.nan F64.neg
    Fl64.sign F64.mul (F64.div F64.one) F64.mul F64.neg F64.muladd id z w
/-- `MulOps` for `ComplexF64`. -/
def ops_ComplexF64 : MulOps ComplexF64 :=
  ⟨mul_Complex F64.mul F64.sub F64.add,
   ⟨F64.one, Fl64.pzero⟩,
   isone_Complex (fun x => F64.eq x F64.one) F64.iszero,
   neg_Complex F64.neg⟩

/-- `^(z::ComplexF64, n::Int)` (`base/complex.jl:892-893`). -/
def pow_ComplexF64_Int (z : ComplexF64) (n : JInt .i64) : Jl ComplexF64 :=
  pow_ComplexFloat_Integer ops_ComplexF64 inv_ComplexF64 z n

/-- `*(z::Complex{Bool}, w::Complex{Bool})` (`base/complex.jl:294-295`):
`Bool * Bool = x & y`, `Bool - Bool = Int(x) - Int(y)`, `Bool + Bool = Int(x) + Int(y)`. -/
def mul_ComplexBool (z w : Complex Bool) : Complex (JInt .i64) :=
  mul_Complex mul_Bool_Bool sub_Bool_Bool add_Bool_Bool z w

/-- `Complex{Int}(z::Complex{Bool})` (`base/complex.jl:43`). -/
def toComplexInt_Bool (z : Complex Bool) : Complex (JInt .i64) :=
  Complex_T_Complex (fun b => JInt.lit .i64 (if b then 1 else 0)) z

/-- Callees from earlier Base files (`boot.jl`, `int.jl`, `number.jl`, `bool.jl`, `promotion.jl`, `float.jl`) on `JInt t`, `F64`, and `Bool`. -/
def zero_JInt {t : IntTy} (_x : JInt t) : JInt t := JInt.lit t 0
def one_JInt {t : IntTy} (_x : JInt t) : JInt t := JInt.lit t 1
def iszero_JInt {t : IntTy} (x : JInt t) : Bool := x.val == 0
def isone_JInt {t : IntTy} (x : JInt t) : Bool := x.val == 1
def isinteger_JInt {t : IntTy} (_x : JInt t) : Bool := true
def isfinite_JInt {t : IntTy} (_x : JInt t) : Bool := true
def isnan_JInt {t : IntTy} (_x : JInt t) : Bool := false
def isinf_JInt {t : IntTy} (_x : JInt t) : Bool := false
def signbit_JInt {t : IntTy} (x : JInt t) : Bool := decide (x.val < 0)
def pos_JInt {t : IntTy} (x : JInt t) : JInt t := x
def neg_JInt {t : IntTy} (x : JInt t) : JInt t := -x
def add_JInt {t : IntTy} (x y : JInt t) : JInt t := x + y
def sub_JInt {t : IntTy} (x y : JInt t) : JInt t := x - y
def mul_JInt {t : IntTy} (x y : JInt t) : JInt t := x * y
def muladd_JInt {t : IntTy} (a b c : JInt t) : JInt t := a * b + c
def oftype_JInt {t : IntTy} (_x y : JInt t) : JInt t := y
def promote_same {α : Type} (x y : α) : α × α := (x, y)
def ofBool_JInt (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)
def add_Bool_JInt {t : IntTy} (b : Bool) (x : JInt t) : JInt t := ofBool_JInt t b + x
def add_JInt_Bool {t : IntTy} (x : JInt t) (b : Bool) : JInt t := x + ofBool_JInt t b
def sub_Bool_JInt {t : IntTy} (b : Bool) (x : JInt t) : JInt t := ofBool_JInt t b - x
def sub_JInt_Bool {t : IntTy} (x : JInt t) (b : Bool) : JInt t := x - ofBool_JInt t b
def mul_Bool_JInt {t : IntTy} (b : Bool) (x : JInt t) : JInt t := if b then x else JInt.lit t 0
def mul_JInt_Bool {t : IntTy} (x : JInt t) (b : Bool) : JInt t := if b then x else JInt.lit t 0
def oftype_JInt_Bool {t : IntTy} (_x : JInt t) (b : Bool) : JInt t := ofBool_JInt t b
def widen_JInt (w : IntTy) {t : IntTy} (x : JInt t) : JInt w := JInt.lit w x.val
def widen_IntTy : IntTy → IntTy
  | .i8 => .i16 | .i16 => .i32 | .i32 => .i64 | .i64 => .i128
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128
  | t => t
def convert_JInt_ok {t : IntTy} (x : JInt t) : Jl (JInt t) := .ok x
def fieldtype1_ComplexTy {R : Type} : ComplexTy R → ComplexTy R
  | .complex r => .real r
  | x => x
def read_List {T : Type} : List T → Jl (T × List T)
  | x :: xs => .ok (x, xs)
  | [] => .error (.argumentError "EOF")
def write2_List {T : Type} (s : List T) (r i : T) : List T := r :: i :: s
def complex_List_JInt (t : IntTy) (A : List (JInt t)) : List (Complex (JInt t)) :=
  A.map (complex_Real zero_JInt)

def zero_F64 (_x : F64) : F64 := Fl64.pzero
def one_ComplexF64 (_z : ComplexF64) : ComplexF64 := ⟨F64.one, Fl64.pzero⟩
def convert_F64_ok (x : F64) : Jl F64 := .ok x
def mem_List_F64 (x : F64) (r : List F64) : Bool := r.contains x
def inv_F64 (x : F64) : F64 := F64.div F64.one x
def epsOf_F64 (x : F64) : F64 := F64.eps x
def round_F64 (x : F64) (m : Rounding) (_ : Unit) : F64 := F64.round x m
def mul_Jl_F64 (r : Jl F64) (e : F64) : Jl F64 := r.map (fun s => F64.mul s e)
def floatArg_F64 : RealOrComplex F64 ComplexF64 → ComplexF64
  | .real x => ⟨x, Fl64.pzero⟩
  | .complex w => w
def floatArg_F64_zero (sz : Bool) : RealOrComplex F64 ComplexF64 → ComplexF64
  | .real x => ⟨x, F64.zero sz⟩
  | .complex w => w

/-- Sign-preserving float formatter on `F64` matching Julia's `show` conventions on `±0.0`, `±1.0`, `±Inf`, and `NaN`. -/
def show_F64 (x : F64) : String :=
  (if F64.signbit x && !F64.isnan x then "-" else "") ++
    (if F64.isnan x then "NaN"
     else if F64.isinf x then "Inf"
     else if F64.iszero x then "0.0"
     else "1.0")

end JuliaLean.base.complex
