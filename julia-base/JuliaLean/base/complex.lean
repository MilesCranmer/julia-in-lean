import JuliaLean.base.number
import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.Runtime.Float

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

def constructTypedComplex {T A B : Type}
    (convertReal : A → Jl T) (convertImag : B → Jl T)
    (re : A) (im : B) : Jl (Complex T) := do
  let re' ← convertReal re
  let im' ← convertImag im
  pure ⟨re', im'⟩

def complexOfPromoted {A B P : Type} (promote : A → B → P × P) (x : A) (y : B) : Complex P :=
  let (re, im) := promote x y
  ⟨re, im⟩

/--
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex(x::Real, y::Real) = Complex(promote(x,y)...)
```
-/
def Complex_Real_Real {A B P : Type}
    (promote : A → B → Jl (P × P)) (x : A) (y : B) :
    Jl (Complex P) := do
  let (re, im) ← promote x y
  pure ⟨re, im⟩

/--
Julia source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex(x::Real) = Complex(x, zero(x))
```
-/
def Complex_Real {A B P : Type}
    (zero : A → Jl B) (construct : A → B → Jl (Complex P))
    (x : A) : Jl (Complex P) := do
  let im ← zero x
  construct x im

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
def Complex_T_Real {T A : Type}
    (construct : A → JInt .i64 → Jl (Complex T))
    (x : A) : Jl (Complex T) :=
  construct x (JInt.lit .i64 0)

/--
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
```
-/
def Complex_T_Complex {T A : Type}
    (construct : A → A → Jl (Complex T))
    (z : Complex A) : Jl (Complex T) :=
  construct z.re z.im

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
def complex_Real {A B P : Type}
    (zero : A → Jl B) (construct : A → B → Jl (Complex P))
    (x : A) : Jl (Complex P) :=
  Complex_Real zero construct x

/--
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
complex(x::Real, y::Real) = Complex(x, y)
```
-/
def complex_Real_Real {A B P : Type}
    (promote : A → B → Jl (P × P)) (x : A) (y : B) :
    Jl (Complex P) :=
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
def conj_ComplexM {m : Type → Type} [Monad m] {T U C : Type}
    (neg : T → m U) (complex : T → U → m C) (z : Complex T) : m C := do
  let r := real_Complex z
  let i ← neg (imag_Complex z)
  complex r i

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
def abs2_ComplexM {m : Type → Type} [Monad m] {T P S : Type}
    (mul : T → T → m P) (add : P → P → m S) (z : Complex T) : m S := do
  let r2 ← mul (real_Complex z) (real_Complex z)
  let i2 ← mul (imag_Complex z) (imag_Complex z)
  add r2 i2

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
def inv_ComplexM {m : Type → Type} [Monad m] {T Z N CS FS C P S Q : Type}
    (isinf : T → Bool) (zero : T → m Z) (negZero : Z → m N)
    (copysign : Z → T → m CS) (flipsign : N → T → m FS)
    (complexInf : CS → FS → m Q)
    (neg : T → m N) (complexNum : T → N → m C)
    (mul : T → T → m P) (add : P → P → m S)
    (div : C → S → m Q) (z : Complex T) : m Q := do
  let (c, d) := reim real_Complex imag_Complex z
  if isinf c || isinf d then
    let zc ← zero c
    let r ← copysign zc c
    let zd ← zero d
    let nzd ← negZero zd
    let i ← flipsign nzd d
    complexInf r i
  else
    let nd ← neg d
    let num ← complexNum c nd
    let cc ← mul c c
    let dd ← mul d d
    let den ← add cc dd
    div num den

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
def pos_ComplexM {m : Type → Type} [Monad m] {T R : Type}
    (pos : T → m R) (z : Complex T) : m (Complex R) := do
  let r ← pos (real_Complex z)
  let i ← pos (imag_Complex z)
  return ⟨r, i⟩

def pos_Complex {T R : Type} (pos : T → R) (z : Complex T) : Complex R :=
  ⟨pos (real_Complex z), pos (imag_Complex z)⟩

/--
Julia source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex) = Complex(-real(z), -imag(z))
```
-/
def neg_ComplexM {m : Type → Type} [Monad m] {T R : Type}
    (neg : T → m R) (z : Complex T) : m (Complex R) := do
  let r ← neg (real_Complex z)
  let i ← neg (imag_Complex z)
  return ⟨r, i⟩

def neg_Complex {T R : Type} (neg : T → R) (z : Complex T) : Complex R :=
  ⟨neg (real_Complex z), neg (imag_Complex z)⟩

/--
Julia source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
```
-/
def add_ComplexM {m : Type → Type} [Monad m] {A B C : Type}
    (add : A → B → m C) (z : Complex A) (w : Complex B) : m (Complex C) := do
  let r ← add (real_Complex z) (real_Complex w)
  let i ← add (imag_Complex z) (imag_Complex w)
  return ⟨r, i⟩

def add_Complex {A B C : Type} (add : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨add (real_Complex z) (real_Complex w), add (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
```
-/
def sub_ComplexM {m : Type → Type} [Monad m] {A B C : Type}
    (sub : A → B → m C) (z : Complex A) (w : Complex B) : m (Complex C) := do
  let r ← sub (real_Complex z) (real_Complex w)
  let i ← sub (imag_Complex z) (imag_Complex w)
  return ⟨r, i⟩

def sub_Complex {A B C : Type} (sub : A → B → C) (z : Complex A) (w : Complex B) : Complex C :=
  ⟨sub (real_Complex z) (real_Complex w), sub (imag_Complex z) (imag_Complex w)⟩

/--
Julia source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
                                    real(z) * imag(w) + imag(z) * real(w))
```
-/
def mul_ComplexM {m : Type → Type} [Monad m] {A B P S : Type}
    (mul : A → B → m P) (sub add : P → P → m S)
    (z : Complex A) (w : Complex B) : m (Complex S) := do
  let rr ← mul (real_Complex z) (real_Complex w)
  let ii ← mul (imag_Complex z) (imag_Complex w)
  let r ← sub rr ii
  let ri ← mul (real_Complex z) (imag_Complex w)
  let ir ← mul (imag_Complex z) (real_Complex w)
  let i ← add ri ir
  return ⟨r, i⟩

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
  complexOfPromoted promote_Int_Bool (add_Bool_Bool x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex{Bool}, x::Bool) = Complex(real(z) + x, imag(z))
```
-/
def add_ComplexBool_Bool (z : Complex Bool) (x : Bool) : Complex (JInt .i64) :=
  complexOfPromoted promote_Int_Bool (add_Bool_Bool (real_Complex z) x) (imag_Complex z)

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
  complexOfPromoted promote_Int_Bool (sub_Bool_Bool (real_Complex z) x) (imag_Complex z)

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
  complexOfPromoted promote (addBool x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
```
-/
def add_Complex_Bool {T S P : Type} (addBoolRight : T → Bool → S) (promote : S → T → P × P)
    (z : Complex T) (x : Bool) : Complex P :=
  complexOfPromoted promote (addBoolRight (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
```
-/
def sub_Bool_Complex {T S N P : Type} (subBool : Bool → T → S) (neg : T → N)
    (promote : S → N → P × P) (x : Bool) (z : Complex T) : Complex P :=
  complexOfPromoted promote (subBool x (real_Complex z)) (neg (imag_Complex z))

/--
Julia source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(z::Complex, x::Bool) = Complex(real(z) - x, imag(z))
```
-/
def sub_Complex_Bool {T S P : Type} (subBoolRight : T → Bool → S) (promote : S → T → P × P)
    (z : Complex T) (x : Bool) : Complex P :=
  complexOfPromoted promote (subBoolRight (real_Complex z) x) (imag_Complex z)

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
  complexOfPromoted promote (addRB x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex{Bool}, x::Real) = Complex(real(z) + x, imag(z))
```
-/
def add_ComplexBool_Real {R S P : Type} (addBR : Bool → R → S) (promote : S → Bool → P × P)
    (z : Complex Bool) (x : R) : Complex P :=
  complexOfPromoted promote (addBR (real_Complex z) x) (imag_Complex z)

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
  complexOfPromoted promote (subBR (real_Complex z) x) (imag_Complex z)

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
  complexOfPromoted promote (add x (real_Complex z)) (imag_Complex z)

/--
Julia source: base/complex.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(z::Complex, x::Real) = Complex(x + real(z), imag(z))
```
-/
def add_Complex_Real {T R S P : Type} (add : R → T → S) (promote : S → T → P × P)
    (z : Complex T) (x : R) : Complex P :=
  complexOfPromoted promote (add x (real_Complex z)) (imag_Complex z)

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
  complexOfPromoted promote (sub (real_Complex z) x) (imag_Complex z)

/--
Julia source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Real, z::Complex) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Real_ComplexM {m : Type → Type} [Monad m] {R T P : Type}
    (mul : R → T → m P) (x : R) (z : Complex T) : m (Complex P) := do
  let r ← mul x (real_Complex z)
  let i ← mul x (imag_Complex z)
  return ⟨r, i⟩

def mul_Real_Complex {R T P : Type} (mul : R → T → P) (x : R) (z : Complex T) : Complex P :=
  ⟨mul x (real_Complex z), mul x (imag_Complex z)⟩

/--
Julia source: base/complex.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(z::Complex, x::Real) = Complex(x * real(z), x * imag(z))
```
-/
def mul_Complex_RealM {m : Type → Type} [Monad m] {T R P : Type}
    (mul : R → T → m P) (z : Complex T) (x : R) : m (Complex P) := do
  let r ← mul x (real_Complex z)
  let i ← mul x (imag_Complex z)
  return ⟨r, i⟩

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
  complexOfPromoted promote (muladd (real_Complex z) x y) (mul (imag_Complex z) x)

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
  complexOfPromoted promote (muladd x y (real_Complex z)) (imag_Complex z)

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
def div_Complex_RealM {m : Type → Type} [Monad m] {T R Q : Type}
    (div : T → R → m Q) (z : Complex T) (x : R) : m (Complex Q) := do
  let r ← div (real_Complex z) x
  let i ← div (imag_Complex z) x
  return ⟨r, i⟩

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
  powCC z ⟨n, zeroI n⟩

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
  powCP ⟨convertT z.re, convertT z.im⟩ (convertS p)

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
  powPC (convertT z) ⟨convertS p.re, convertS p.im⟩

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
  ⟨convertBig z.re, convertBig z.im⟩

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
  ⟨JInt.lit .i64 (if z.re then 1 else 0), JInt.lit .i64 (if z.im then 1 else 0)⟩

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
  A.map (fun x => ⟨x, zero_JInt x⟩)

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

namespace JuliaLean.base.complex.Models1Group19

open JuliaLean JuliaLean.Float JuliaLean.Promotion

/-- Closed two-BitInteger promote dispatch. Same-type values take the identity
method; other pairs compute the promotion type and convert left to right.
The result type statically establishes that not_sametype cannot fail.
Julia source: base/promotion.jl:397-401,423-428,441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/promotion.jl:397-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _promote(x::T, y::S) where {T,S}
--     @inline
--     R = promote_type(T, S)
--     return (convert(R, x), convert(R, y))
-- end
-- /Source
-- Source: base/promotion.jl:423-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote(x, y)
--     @inline
--     px, py = _promote(x, y)
--     not_sametype((x,y), (px,py))
--     px, py
-- end
-- /Source
-- Source: base/promotion.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote(x::T, y::T, zs::T...) where {T} = (x, y, zs...)
-- /Source
def promoteInts : {t s : IntTy} → JInt t → JInt s →
    Jl (JInt (IntTy.promote t s) × JInt (IntTy.promote t s))
  | .i8, .i8, x, y => .ok (x, y)
  | .i16, .i16, x, y => .ok (x, y)
  | .i32, .i32, x, y => .ok (x, y)
  | .i64, .i64, x, y => .ok (x, y)
  | .i128, .i128, x, y => .ok (x, y)
  | .u8, .u8, x, y => .ok (x, y)
  | .u16, .u16, x, y => .ok (x, y)
  | .u32, .u32, x, y => .ok (x, y)
  | .u64, .u64, x, y => .ok (x, y)
  | .u128, .u128, x, y => .ok (x, y)
  | t, s, x, y => do
      let a ← JInt.convert (IntTy.name (IntTy.promote t s)) (IntTy.promote t s) x.val
      let b ← JInt.convert (IntTy.name (IntTy.promote t s)) (IntTy.promote t s) y.val
      return (a, b)

/-- `Complex(x,y)` on every pair of machine integer types, including failed promotion.
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real, y::Real) = Complex(promote(x,y)...)
-- /Source
def complexIntPair {t s : IntTy} (x : JInt t) (y : JInt s) : Jl (Complex (JInt (IntTy.promote t s))) :=
  Complex_Real_Real promoteInts x y

/-- Same-type Float64 constructor; identity promotion preserves every bit.
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real, y::Real) = Complex(promote(x,y)...)
-- /Source
def complexF64Pair (x y : F64) : Jl ComplexF64 :=
  Complex_Real_Real (fun a b => .ok (a, b)) x y

/-- Same-type Bool constructor uses identity promotion.
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real, y::Real) = Complex(promote(x,y)...)
-- /Source
def complexBoolPair (x y : Bool) : Jl (Complex Bool) :=
  Complex_Real_Real (fun a b => .ok (a, b)) x y

/-- Mixed integer/Float64 constructor; promotes only the integer coordinate through the actual width-specific converter.
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real, y::Real) = Complex(promote(x,y)...)
-- /Source
def complexIntF64Pair {t : IntTy} (x : JInt t) (y : F64) : Jl ComplexF64 :=
  Complex_Real_Real (fun a b => .ok (F64.ofJInt a, b)) x y

/-- Mixed Float64/integer constructor; retains every real Float64 bit and converts the integer imaginary field.
Julia source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real, y::Real) = Complex(promote(x,y)...)
-- /Source
def complexF64IntPair {t : IntTy} (x : F64) (y : JInt t) : Jl ComplexF64 :=
  Complex_Real_Real (fun a b => .ok (a, F64.ofJInt b)) x y

/-- One-argument machine integer constructor with zero of the input type.
Julia source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real) = Complex(x, zero(x))
-- /Source
def complexIntReal {t : IntTy} (x : JInt t) : Jl (Complex (JInt t)) :=
  Complex_Real (fun a => .ok (zero_JInt a))
    (fun a b => .ok ⟨a, b⟩) x

/-- One-argument Float64 constructor; the imaginary zero is positive even for negative-zero x.
Julia source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real) = Complex(x, zero(x))
-- /Source
def complexF64Real (x : F64) : Jl ComplexF64 :=
  Complex_Real (fun _ => .ok Fl64.pzero) complexF64Pair x

/-- One-argument Bool constructor.
Julia source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real) = Complex(x, zero(x))
-- /Source
def complexBoolReal (x : Bool) : Jl (Complex Bool) :=
  Complex_Real (fun _ => .ok false) complexBoolPair x

/-- Typed machine integer constructor; the source literal zero has type Int64.
Julia source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
def complexIntAsInt (t : IntTy) {s : IntTy} (x : JInt s) : Jl (Complex (JInt t)) :=
  Complex_T_Real
    (constructTypedComplex (fun a => JInt.convert t.name t a.val)
      (fun b => JInt.convert t.name t b.val)) x

/-- Typed machine integer constructor from Float64, using the actual checked conversion.
Julia source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
def complexF64AsInt (t : IntTy) (x : F64) : Jl (Complex (JInt t)) :=
  Complex_T_Real
    (constructTypedComplex (F64.int t) (fun b => JInt.convert t.name t b.val)) x

/-- Typed Float64 constructor from every BitInteger width, retaining the 128-bit conversion algorithm.
Julia source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
def complexIntAsF64 {s : IntTy} (x : JInt s) : Jl ComplexF64 :=
  Complex_T_Real
    (constructTypedComplex (fun a => .ok (F64.ofJInt a))
      (fun b => .ok (F64.ofJInt b))) x

/-- Typed Float64 constructor from Float64; real field is not rounded again.
Julia source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
def complexF64AsF64 (x : F64) : Jl ComplexF64 :=
  Complex_T_Real
    (constructTypedComplex (fun a => .ok a) (fun b => .ok (F64.ofJInt b))) x

/-- Convert the real field before the imaginary field, with checked machine-integer conversions.
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def convertComplexInt (t : IntTy) {s : IntTy} (z : Complex (JInt s)) : Jl (Complex (JInt t)) :=
  Complex_T_Complex
    (constructTypedComplex (fun a => JInt.convert t.name t a.val)
      (fun b => JInt.convert t.name t b.val)) z

/-- Checked Float64-to-machine-integer complex conversion in source evaluation order.
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def convertComplexF64ToInt (t : IntTy) (z : ComplexF64) : Jl (Complex (JInt t)) :=
  Complex_T_Complex (constructTypedComplex (F64.int t) (F64.int t)) z

/-- Float64 conversion of a machine-integer complex number; both scalar calls are executable.
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def convertComplexIntToF64 {s : IntTy} (z : Complex (JInt s)) : Jl ComplexF64 :=
  Complex_T_Complex
    (constructTypedComplex (fun a => .ok (F64.ofJInt a))
      (fun b => .ok (F64.ofJInt b))) z

/-- Identity element conversion, preserving signed zeros and NaN payloads.
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def convertComplexF64 (z : ComplexF64) : Jl ComplexF64 :=
  Complex_T_Complex (constructTypedComplex (fun a => .ok a) (fun b => .ok b)) z

/-- Complex machine-integer to scalar machine-integer conversion, rejecting imaginary values first.
Julia source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realIntAsInt (t : IntTy) {s : IntTy} (z : Complex (JInt s)) : Jl (JInt t) :=
  Type_T_Complex (isreal_Complex iszero_JInt)
    (fun a => JInt.convert t.name t a.val) t.name z

/-- ComplexF64 to machine integer, preserving isreal-before-conversion order.
Julia source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realF64AsInt (t : IntTy) (z : ComplexF64) : Jl (JInt t) :=
  Type_T_Complex (isreal_Complex F64.iszero) (F64.int t) t.name z

/-- Complex machine-integer to Float64 conversion with imaginary rejection.
Julia source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realIntAsF64 {s : IntTy} (z : Complex (JInt s)) : Jl F64 :=
  Type_T_Complex (isreal_Complex iszero_JInt)
    (fun a => .ok (F64.ofJInt a)) "Float64" z

/-- ComplexF64 to Float64 accepts either signed imaginary zero and rejects NaN imaginary parts.
Julia source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realF64AsF64 (z : ComplexF64) : Jl F64 :=
  Type_T_Complex (isreal_Complex F64.iszero) (fun a => .ok a) "Float64" z

/-- Closed machine-integer type promotion.
Julia source: base/complex.jl:49-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:49-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- /Source
def promoteComplexIntRealType (t s : IntTy) : ComplexTy IntTy :=
  promote_rule_Complex_Real IntTy.promote t s

/-- Closed type promotion for two machine-integer complex types.
Julia source: base/complex.jl:51-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:51-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- /Source
def promoteComplexIntType (t s : IntTy) : ComplexTy IntTy :=
  promote_rule_Complex_Complex IntTy.promote t s

/-- Type descriptor for the result of widening a BitInteger. The BigInt tag
represents a type, not an invented executable BigInt value implementation. -/
inductive WidenedIntegerType where
  | machine (t : IntTy)
  | bigInt
  deriving DecidableEq, Repr

/-- Scalar type-level widening dependency at base/int.jl:911-918 and base/gmp.jl:298-299. -/
-- Source: base/int.jl:911-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int8}) = Int16
-- widen(::Type{Int16}) = Int32
-- widen(::Type{Int32}) = Int64
-- widen(::Type{Int64}) = Int128
-- widen(::Type{UInt8}) = UInt16
-- widen(::Type{UInt16}) = UInt32
-- widen(::Type{UInt32}) = UInt64
-- widen(::Type{UInt64}) = UInt128
-- /Source
-- Source: base/gmp.jl:298-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int128})  = BigInt
-- widen(::Type{UInt128}) = BigInt
-- /Source
def widenedIntegerType : IntTy → WidenedIntegerType
  | .i8 => .machine .i16 | .i16 => .machine .i32
  | .i32 => .machine .i64 | .i64 => .machine .i128
  | .u8 => .machine .u16 | .u16 => .machine .u32
  | .u32 => .machine .u64 | .u64 => .machine .u128
  | .i128 | .u128 => .bigInt

/-- Widen complex machine-integer types, retaining BigInt at the 128-bit endpoint.
Julia source: base/complex.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Complex{T}}) where {T} = Complex{widen(T)}
-- /Source
def widenComplexIntType (t : IntTy) : ComplexTy WidenedIntegerType :=
  widen_Type_Complex widenedIntegerType t

/-- Every BitInteger component type floats to Float64, including 128-bit types.
Julia source: base/complex.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(::Type{Complex{T}}) where {T} = Complex{float(T)}
-- /Source
def floatComplexIntType (t : IntTy) : ComplexTy Fmt :=
  float_Type_Complex (fun _ : IntTy => double) t

/-- Imaginary part of a machine-integer real value.
Julia source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- imag(x::Real) = zero(x)
-- /Source
def imaginaryIntReal {t : IntTy} (x : JInt t) : JInt t :=
  imag_Real zero_JInt x

/-- Imaginary part of a Float64 real value is positive zero, including NaN and negative zero.
Julia source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- imag(x::Real) = zero(x)
-- /Source
def imaginaryF64Real (x : F64) : F64 :=
  imag_Real zero_F64 x

/-- Close the reim scalar interface for every concrete Complex T representation.
Julia source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reim(z) = (real(z), imag(z))
-- /Source
def reimComplex {T : Type} (z : Complex T) : T × T :=
  reim real_Complex imag_Complex z

/-- Closed reim for machine-integer real inputs.
Julia source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reim(z) = (real(z), imag(z))
-- /Source
def reimInt {t : IntTy} (x : JInt t) : JInt t × JInt t :=
  reim real_Real imaginaryIntReal x

/-- Closed reim for all Float64 real bit patterns.
Julia source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reim(z) = (real(z), imag(z))
-- /Source
def reimF64 (x : F64) : F64 × F64 :=
  reim real_Real imaginaryF64Real x

/-- Read the component type of a concrete Complex{T} descriptor; UnionAll reflection remains outside this representation.
Julia source: base/complex.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(C::Type{<:Complex}) = fieldtype(C, 1)
-- /Source
def realConcreteComplexType {R : Type} (t : R) : ComplexTy R :=
  real_Type_Complex fieldtype1_ComplexTy (.complex t)

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- /Source
def integerInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  isinteger_Complex iszero_JInt isinteger_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- /Source
def integerF64 (z : ComplexF64) : Bool :=
  isinteger_Complex F64.iszero F64.isinteger z

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- /Source
def finiteInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  isfinite_Complex isfinite_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- /Source
def finiteF64 (z : ComplexF64) : Bool :=
  isfinite_Complex F64.isfinite z

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- /Source
def nanInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  isnan_Complex isnan_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- /Source
def nanF64 (z : ComplexF64) : Bool :=
  isnan_Complex F64.isnan z

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- /Source
def infiniteInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  isinf_Complex isinf_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- /Source
def infiniteF64 (z : ComplexF64) : Bool :=
  isinf_Complex F64.isinf z

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- /Source
def zeroInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  iszero_Complex iszero_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- /Source
def zeroF64 (z : ComplexF64) : Bool :=
  iszero_Complex F64.iszero z

/-- Closed machine-integer complex predicate. Scalar primitives are pure and total, so both eager operand evaluations have no omitted errors or effects.
Julia source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
def oneInt {t : IntTy} (z : Complex (JInt t)) : Bool :=
  isone_Complex isone_JInt iszero_JInt z

/-- Closed Float64 complex predicate over all bit patterns. Scalar primitives are pure and total.
Julia source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
def oneF64 (z : ComplexF64) : Bool :=
  isone_Complex isone_F64 F64.iszero z

/-- The public complex(x) alias on all machine-integer widths.
Julia source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real) = Complex(x)
-- /Source
def asComplexInt {t : IntTy} (x : JInt t) : Jl (Complex (JInt t)) :=
  complex_Real (fun a => .ok (zero_JInt a)) (fun a b => .ok ⟨a,b⟩) x

/-- The public complex(x) alias on Float64.
Julia source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real) = Complex(x)
-- /Source
def asComplexF64 (x : F64) : Jl ComplexF64 :=
  complex_Real (fun _ => .ok Fl64.pzero) complexF64Pair x

/-- Public complex(x,y), with exact ordered integer promotion.
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
def asComplexIntPair {t s : IntTy} (x : JInt t) (y : JInt s) : Jl (Complex (JInt (IntTy.promote t s))) :=
  complex_Real_Real promoteInts x y

/-- Public complex(x,y) on Float64, preserving fields without arithmetic.
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
def asComplexF64Pair (x y : F64) : Jl ComplexF64 :=
  complex_Real_Real (fun a b => .ok (a,b)) x y

/-- Public complex(x,y) delegates to the closed mixed integer/Float64 constructor.
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
def asComplexIntF64Pair {t : IntTy} (x : JInt t) (y : F64) : Jl ComplexF64 :=
  complexIntF64Pair x y

/-- Public complex(x,y) delegates to the closed mixed Float64/integer constructor.
Julia source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
def asComplexF64IntPair {t : IntTy} (x : F64) (y : JInt t) : Jl ComplexF64 :=
  complexF64IntPair x y

/-- Primitive ifelse specialization evaluates the sign and the negated complex argument before selection.
Julia source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
def flipsignInt {t s : IntTy} (x : Complex (JInt t)) (y : JInt s) : Complex (JInt t) :=
  let sign := signbit_JInt y
  let negative := neg_Complex neg_JInt x
  if sign then negative else x

/-- Float64 ifelse specialization preserves the source operand evaluation order.
Julia source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
def flipsignF64 (x : ComplexF64) (y : F64) : ComplexF64 :=
  let sign := F64.signbit y
  let negative := neg_Complex F64.neg x
  if sign then negative else x

/-- Bool negation changes component type to Int64. The tagged result retains this dispatch-visible type distinction.
Julia source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
def flipsignBoolF64 (x : Complex Bool) (y : F64) : Sum (Complex (JInt .i64)) (Complex Bool) :=
  let sign := F64.signbit y
  let negative := neg_Complex neg_Bool_val x
  if sign then .inl negative else .inr x

/-- Same-type BitInteger equality using exact machine value equality.
Julia source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
def equalInt {t : IntTy} (z w : Complex (JInt t)) : Bool :=
  eq_Complex (fun a b => decide (a = b)) z w

/-- Closed IEEE complex equality, retaining NaN and signed-zero rules.
Julia source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
def equalF64 (z w : ComplexF64) : Bool :=
  eq_Complex F64.eq z w

/-- Scalar-to-complex equality on the complete same-integer-type domain.
Julia source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Real, z::Complex) = isreal(z) && real(z) == x
-- /Source
def equalRealInt {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Bool :=
  eq_Real_Complex iszero_JInt (fun a b => decide (a = b)) x z

/-- Scalar-to-complex IEEE equality checks isreal first.
Julia source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Real, z::Complex) = isreal(z) && real(z) == x
-- /Source
def equalRealF64 (x : F64) (z : ComplexF64) : Bool :=
  eq_Real_Complex F64.iszero F64.eq x z

/-- Closed isequal for same machine-integer type.
Julia source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
def isequalRealInt {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Bool :=
  isequal_Real_Complex (fun a b => decide (a = b)) zero_JInt x z

/-- Closed isequal, accepting equal NaNs and requiring positive imaginary zero.
Julia source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
def isequalRealF64 (x : F64) (z : ComplexF64) : Bool :=
  isequal_Real_Complex F64.isequal zero_F64 x z

/-- Machine-integer squared norm retains separate wrapping products and sum.
Julia source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
-- /Source
def abs2Int {t : IntTy} (z : Complex (JInt t)) : JInt t :=
  abs2_Complex mul_JInt add_JInt z

/-- Float64 squared norm uses two separately rounded products followed by addition.
Julia source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
-- /Source
def abs2F64 (z : ComplexF64) : F64 :=
  abs2_Complex F64.mul F64.add z

/-- Binary64 reciprocal with the source chained-comparison evaluation order.
Julia source: base/complex.jl:482-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def inverseF64 (w : ComplexF64) : Jl ComplexF64 := do
  let (c, d) := reim real_Complex imag_Complex w
  let absc := F64.abs c
  let absd := F64.abs d
  let (cd, dc) := if F64.lt absd absc then (absc, absd) else (absd, absc)
  let lo ← F64.sqrt (F64.div F64.floatmin Fl64.two)
  let inRange ← if F64.le lo cd then do
      let hi ← F64.sqrt (F64.div F64.floatmax Fl64.two)
      pure (F64.le cd hi)
    else pure false
  if inRange then
    return div_Complex_Real F64.div (conj_Complex F64.neg w)
      (F64.muladd cd cd (F64.mul dc dc))
  if F64.isinf c || F64.isinf d then
    return ⟨Fl64.copysign Fl64.pzero c, Fl64.flipsign Fl64.nzero d⟩
  let eps := Fl64.eps
  let bs := F64.div Fl64.two (F64.mul eps eps)
  let (c, d, s) :=
    if F64.le (F64.div F64.floatmax Fl64.two) cd then
      (F64.mul c Fl64.half, F64.mul d Fl64.half, Fl64.half)
    else if F64.le cd (F64.div (F64.mul Fl64.two F64.floatmin) eps) then
      (F64.mul c bs, F64.mul d bs, bs)
    else (c, d, F64.one)
  let (p, q) :=
    if F64.le absd absc then robust_cinv c d
    else
      let (q, p) := robust_cinv (F64.neg d) (F64.neg c)
      (p, q)
  return ⟨F64.mul p s, F64.mul q s⟩

/-- Integer inverse dispatches to the actual Float64 method after the existing source-mirrored float conversion. No reciprocal callback is left open.
Julia source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(z::Complex{<:Integer}) = inv(float(z))
-- /Source
def inverseInt {t : IntTy} (z : Complex (JInt t)) : Jl ComplexF64 :=
  inv_Complex_Integer (float_Complex F64.ofJInt) inverseF64 z

/-- Closed machine-integer unary plus.
Julia source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex) = Complex(+real(z), +imag(z))
-- /Source
def positiveInt {t : IntTy} (z : Complex (JInt t)) : Complex (JInt t) :=
  pos_Complex pos_JInt z

/-- Closed Float64 unary plus, preserving all bits.
Julia source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex) = Complex(+real(z), +imag(z))
-- /Source
def positiveF64 (z : ComplexF64) : ComplexF64 :=
  pos_Complex (fun x => x) z

/-- Closed wrapping machine-integer unary minus.
Julia source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex) = Complex(-real(z), -imag(z))
-- /Source
def negativeInt {t : IntTy} (z : Complex (JInt t)) : Complex (JInt t) :=
  neg_Complex neg_JInt z

/-- Closed Float64 unary minus, toggling both component signs.
Julia source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex) = Complex(-real(z), -imag(z))
-- /Source
def negativeF64 (z : ComplexF64) : ComplexF64 :=
  neg_Complex F64.neg z

/-- Closed same-type machine-integer complex arithmetic with wrapping at each scalar operation.
Julia source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- /Source
def addInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  add_Complex add_JInt z w

/-- Closed same-type machine-integer complex arithmetic with wrapping at each scalar operation.
Julia source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
def subtractInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  sub_Complex sub_JInt z w

/-- Closed same-type machine-integer complex arithmetic with wrapping at each scalar operation.
Julia source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
def multiplyInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  mul_Complex mul_JInt sub_JInt add_JInt z w

/-- Explicit wrapping complex unary minus.
Julia source: base/complex.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex) = Complex(-%(real(z)), -%(imag(z)))
-- /Source
def negativeWrapInt {t : IntTy} (z : Complex (JInt t)) : Complex (JInt t) :=
  negWrap_Complex neg_JInt z

/-- Explicit wrapping complex operation closed over machine-integer primitives.
Julia source: base/complex.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +%(z::Complex, w::Complex) = Complex(real(z) +% real(w), imag(z) +% imag(w))
-- /Source
def addWrapInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  addWrap_Complex add_JInt z w

/-- Explicit wrapping complex operation closed over machine-integer primitives.
Julia source: base/complex.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex, w::Complex) = Complex(real(z) -% real(w), imag(z) -% imag(w))
-- /Source
def subtractWrapInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  subWrap_Complex sub_JInt z w

/-- Explicit wrapping complex operation closed over machine-integer primitives.
Julia source: base/complex.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *%(z::Complex, w::Complex) = Complex(real(z) *% real(w) -% imag(z) *% imag(w),
--                                      real(z) *% imag(w) +% imag(z) *% real(w))
-- /Source
def multiplyWrapInt {t : IntTy} (z w : Complex (JInt t)) : Complex (JInt t) :=
  mulWrap_Complex mul_JInt sub_JInt add_JInt z w

/-- Closed mixed-width integer helper: determine the common type, convert a/b/c in order, then invoke the same-type helper. The same-type case is semantically the more-specific dispatch.
Julia source: base/complex.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mulsub(a, b, c) = _mulsub(promote(a, b, c)...)
-- /Source
def mulsubMixedInt {t s u : IntTy} (a : JInt t) (b : JInt s) (c : JInt u) : Jl (JInt (IntTy.promote (IntTy.promote t s) u)) :=
  do
    let r := IntTy.promote (IntTy.promote t s) u
    let pa ← JInt.convert r.name r a.val
    let pb ← JInt.convert r.name r b.val
    let pc ← JInt.convert r.name r c.val
    return _mulsub_Real muladd_JInt neg_JInt pa pb pc

/-- Closed same-type machine-integer _mulsub; every arithmetic operation wraps.
Julia source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mulsub(a::T, b::T, c::T) where {T<:Real} = muladd(a, b, -c)
-- /Source
def mulsubInt {t : IntTy} (a b c : JInt t) : JInt t :=
  _mulsub_Real muladd_JInt neg_JInt a b c

/-- Closed Float64 helper using the bundled fused muladd semantics.
Julia source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mulsub(a::T, b::T, c::T) where {T<:Real} = muladd(a, b, -c)
-- /Source
def mulsubF64 (a b c : F64) : F64 :=
  _mulsub_Real F64.muladd F64.neg a b c

/-- Closed Bool/machine-integer complex arithmetic with source operand order.
Julia source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addBoolInt {t : IntTy} (x : Bool) (z : Complex (JInt t)) : Complex (JInt t) :=
  add_Bool_Complex add_Bool_JInt promote_same x z

/-- Closed Bool/machine-integer complex arithmetic with source operand order.
Julia source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
-- /Source
def addIntBool {t : IntTy} (x : Bool) (z : Complex (JInt t)) : Complex (JInt t) :=
  add_Complex_Bool add_JInt_Bool promote_same z x

/-- Closed Bool/machine-integer complex arithmetic with source operand order.
Julia source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
-- /Source
def subtractBoolInt {t : IntTy} (x : Bool) (z : Complex (JInt t)) : Complex (JInt t) :=
  sub_Bool_Complex sub_Bool_JInt neg_JInt promote_same x z

/-- Closed Bool/machine-integer complex arithmetic with source operand order.
Julia source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Bool) = Complex(real(z) - x, imag(z))
-- /Source
def subtractIntBool {t : IntTy} (x : Bool) (z : Complex (JInt t)) : Complex (JInt t) :=
  sub_Complex_Bool sub_JInt_Bool promote_same z x

/-- Closed right Bool multiplication on machine-integer complex values.
Julia source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyIntBool {t : IntTy} (z : Complex (JInt t)) (x : Bool) : Complex (JInt t) :=
  mul_Complex_Bool mul_JInt_Bool z x

/-- Closed right Bool multiplication with Float64 strong-zero semantics.
Julia source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyF64Bool (z : ComplexF64) (x : Bool) : ComplexF64 :=
  mul_Complex_Bool Fl64.mulBoolRight z x

/-- Integer plus ComplexBool; constructor promotion converts only the imaginary Bool field.
Julia source: base/complex.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Real, z::Complex{Bool}) = Complex(x + real(z), imag(z))
-- /Source
def addRealIntComplexBool {t : IntTy} (x : JInt t) (z : Complex Bool) : Complex (JInt t) :=
  add_Real_ComplexBool add_JInt_Bool (fun a b => (a, ofBool_JInt t b)) x z

/-- ComplexBool plus integer.
Julia source: base/complex.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex{Bool}, x::Real) = Complex(real(z) + x, imag(z))
-- /Source
def addComplexBoolRealInt {t : IntTy} (z : Complex Bool) (x : JInt t) : Complex (JInt t) :=
  add_ComplexBool_Real add_Bool_JInt (fun a b => (a, ofBool_JInt t b)) z x

/-- Compute the real result, convert the imaginary Bool to that result type, then negate.
Julia source: base/complex.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex{Bool})
--     # we don't want the default type for -(Bool)
--     re = x-real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
def subtractRealIntComplexBool {t : IntTy} (x : JInt t) (z : Complex Bool) : Complex (JInt t) :=
  sub_Real_ComplexBool sub_JInt_Bool oftype_JInt_Bool neg_JInt x z

/-- ComplexBool minus integer, including unsigned wrapping.
Julia source: base/complex.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex{Bool}, x::Real) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexBoolRealInt {t : IntTy} (z : Complex Bool) (x : JInt t) : Complex (JInt t) :=
  sub_ComplexBool_Real sub_Bool_JInt (fun a b => (a, ofBool_JInt t b)) z x

/-- Integer times ComplexBool using both Bool multiplications.
Julia source: base/complex.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex{Bool}) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyRealIntComplexBool {t : IntTy} (x : JInt t) (z : Complex Bool) : Complex (JInt t) :=
  mul_Real_ComplexBool mul_JInt_Bool x z

/-- ComplexBool times integer with source argument order.
Julia source: base/complex.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex{Bool}, x::Real) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyComplexBoolRealInt {t : IntTy} (z : Complex Bool) (x : JInt t) : Complex (JInt t) :=
  mul_ComplexBool_Real mul_Bool_JInt z x

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Real, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addRealInt {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  add_Real_Complex add_JInt promote_same x z

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Real) = Complex(x + real(z), imag(z))
-- /Source
def addIntReal {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  add_Complex_Real add_JInt promote_same z x

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex)
--     # we don't want the default type for -(Bool)
--     re = x - real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
def subtractRealInt {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  sub_Real_Complex sub_JInt oftype_JInt neg_JInt x z

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Real) = Complex(real(z) - x, imag(z))
-- /Source
def subtractIntReal {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  sub_Complex_Real sub_JInt promote_same z x

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyRealInt {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  mul_Real_Complex mul_JInt x z

/-- Closed same-type scalar/complex machine-integer arithmetic.
Julia source: base/complex.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Real) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyIntReal {t : IntTy} (x : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  mul_Complex_Real mul_JInt z x

/-- Resolve the Real-or-Complex third argument by actual typed branches, then call the installed source-mirrored callee with closed scalar primitives.
Julia source: base/complex.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::Real, z::Complex, y::Union{Real,Complex}) = muladd(z, x, y)
-- /Source
def muladdRealIntComplexUnion {t : IntTy} (x : JInt t) (z : Complex (JInt t))
    (y : RealOrComplex (JInt t) (Complex (JInt t))) : Complex (JInt t) :=
  muladd_Real_Complex_Union
    (fun z x y => match y with
      | .real y => muladd_Complex_Real_Real muladd_JInt mul_JInt promote_same z x y
      | .complex w => muladd_Complex_Real_Complex muladd_JInt z x w) x z y

/-- Closed Complex/Real/Real machine-integer muladd.
Julia source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, y::Real) = Complex(muladd(real(z),x,y), imag(z)*x)
-- /Source
def muladdIntRealReal {t : IntTy} (z : Complex (JInt t)) (x y : JInt t) : Complex (JInt t) :=
  muladd_Complex_Real_Real muladd_JInt mul_JInt promote_same z x y

/-- Closed Complex/Real/Complex machine-integer muladd.
Julia source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, w::Complex) =
--     Complex(muladd(real(z),x,real(w)), muladd(imag(z),x,imag(w)))
-- /Source
def muladdIntRealComplex {t : IntTy} (z : Complex (JInt t)) (x : JInt t) (w : Complex (JInt t)) : Complex (JInt t) :=
  muladd_Complex_Real_Complex muladd_JInt z x w

/-- Closed Real/Real/Complex machine-integer muladd.
Julia source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::Real, y::Real, z::Complex) = Complex(muladd(x,y,real(z)), imag(z))
-- /Source
def muladdRealRealInt {t : IntTy} (x y : JInt t) (z : Complex (JInt t)) : Complex (JInt t) :=
  muladd_Real_Real_Complex muladd_JInt promote_same x y z

/-- Closed Complex/Complex/Real machine-integer muladd, retaining nested scalar association.
Julia source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, w::Complex, x::Real) =
--     Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), x)),
--             muladd(real(z), imag(w), imag(z) * real(w)))
-- /Source
def muladdIntIntReal {t : IntTy} (z w : Complex (JInt t)) (x : JInt t) : Complex (JInt t) :=
  muladd_Complex_Complex_Real muladd_JInt mulsubInt neg_JInt mul_JInt z w x

/-- Resolve the promoted complex type, convert only z first, then invert and multiply by the original scalar. Conversion failures are propagated.
Julia source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))
-- /Source
def divideRealIntByComplexInt {t s : IntTy} (a : JInt t) (z : Complex (JInt s)) : Jl ComplexF64 :=
  do
    let promoted := IntTy.promote t s
    let converted ← convertComplexInt promoted z
    let reciprocal ← inverseInt converted
    return mul_Real_Complex (fun a b => F64.mul (F64.ofJInt a) b) a reciprocal

/-- Closed Float64 real-by-complex division, preserving the actual reciprocal Jl error channel.
Julia source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))
-- /Source
def divideRealF64ByComplex (a : F64) (z : ComplexF64) : Jl ComplexF64 :=
  do
    let converted ← convertComplexF64 z
    let reciprocal ← inverseF64 converted
    return mul_Real_Complex F64.mul a reciprocal

/-- Closed machine-integer complex/scalar division with actual Float64 conversion algorithms.
Julia source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(z::Complex, x::Real) = Complex(real(z)/x, imag(z)/x)
-- /Source
def divideComplexIntByReal {t s : IntTy} (z : Complex (JInt t)) (x : JInt s) : ComplexF64 :=
  div_Complex_Real (fun a b => F64.div (F64.ofJInt a) (F64.ofJInt b)) z x

/-- Closed Float64 component division; no error or default-value shortcut.
Julia source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(z::Complex, x::Real) = Complex(real(z)/x, imag(z)/x)
-- /Source
def divideComplexF64ByReal (z : ComplexF64) (x : F64) : ComplexF64 :=
  div_Complex_Real F64.div z x

/-! The small-float methods need Float32 arithmetic while the supplied callable
imports expose only Float64 arithmetic. The following bounded dependencies port
`quietFloat`, `invalidFloat`, `floatAdd`, `floatMul`, `floatDiv`, and `floatFma`
from the bundled `JuliaLean/src/runtime_intrinsics_c.lean:479-521`. The bodies
are executable exact-rational semantics, not callbacks. Only half/single are
used here. Double-precision operations reuse the supplied F64 implementation.
The inherited target policy is nearest-even, gradual underflow, fused muladd
for Float32/Float64, and the existing x86 NaN policy. -/

/-- The two and only two component types in base/complex.jl:379 and 476. -/
inductive SmallFloatKind where
  | f16 | f32
  deriving DecidableEq, Repr

/-- Representation of the source type parameter at base/complex.jl:379. -/
def smallFormat : SmallFloatKind → Fmt
  | .f16 => half | .f32 => single

/-- Widened format used at base/complex.jl:380,477. -/
def wideFormat : SmallFloatKind → Fmt
  | .f16 => single | .f32 => double

abbrev SmallValue (k : SmallFloatKind) := Fl (smallFormat k)
abbrev WideValue (k : SmallFloatKind) := Fl (wideFormat k)

/-- NaN quieting dependency of mul_float. Exact bounded copy of existing
JuliaLean.C.quietFloat; no floating arithmetic is executed by the host.
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
-- /Source
def quietFloatAt {f : Fmt} (x : Fl f) : Fl f :=
  Fl.ofBits (Nat.lor x.toBits (2 ^ (f.sb - 1)))

/-- Existing x86 invalid-operation NaN pattern, ported from JuliaLean.C.invalidFloat.
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
-- /Source
def invalidFloatAt (f : Fmt) : Fl f :=
  Fl.ofBits (2 ^ (f.eb + f.sb) + f.emax * 2 ^ f.sb + 2 ^ (f.sb - 1))

/-- Exact local port of JuliaLean.C.floatAdd for the small-format dependency.
The result is rounded once by the existing Fl.roundRat primitive.
Julia source: base/float.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::T, y::T) where {T<:IEEEFloat} = add_float(x, y)
-- /Source
def addFloatAt {f : Fmt} (x y : Fl f) : Fl f :=
  if x.isnan then quietFloatAt x else if y.isnan then quietFloatAt y
  else if x.isinf then (if y.isinf && x.signbit != y.signbit then invalidFloatAt f else x)
  else if y.isinf then y
  else let a := x.toRat; let b := y.toRat
       Fl.roundRat (a.1 * (b.2 : Int) + b.1 * (a.2 : Int)) (a.2 * b.2) (x.signbit && y.signbit)

/-- Exact local port of JuliaLean.C.floatMul for Float16/Float32 dependency calls.
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
-- /Source
def multiplyFloatAt {f : Fmt} (x y : Fl f) : Fl f :=
  if x.isnan then quietFloatAt x else if y.isnan then quietFloatAt y
  else if (x.isinf && y.iszero) || (y.isinf && x.iszero) then invalidFloatAt f
  else if x.isinf || y.isinf then Fl.inf (x.signbit != y.signbit)
  else let a := x.toRat; let b := y.toRat
       Fl.roundRat (a.1 * b.1) (a.2 * b.2) (x.signbit != y.signbit)

/-- Exact local port of JuliaLean.C.floatDiv; used for widened Float32 reciprocal.
Julia source: base/float.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::T, y::T) where {T<:IEEEFloat} = div_float(x, y)
-- /Source
def divideFloatAt {f : Fmt} (x y : Fl f) : Fl f :=
  let neg := x.signbit != y.signbit
  if x.isnan then quietFloatAt x else if y.isnan then quietFloatAt y
  else if (x.isinf && y.isinf) || (x.iszero && y.iszero) then invalidFloatAt f
  else if x.isinf then Fl.inf neg else if y.isinf then Fl.zero neg else if y.iszero then Fl.inf neg
  else let a := x.toRat; let b := y.toRat
       Fl.roundRat (if b.1 < 0 then -(a.1 * (b.2 : Int)) else a.1 * (b.2 : Int))
         (a.2 * b.1.natAbs) neg

/-- Exact local port of JuliaLean.C.floatFma at single precision, as used by
JuliaLean.C.jlMuladdFloat. The target fused policy is the same as the bundled Float64 model.
Julia source: base/float.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::T, y::T, z::T) where {T<:IEEEFloat} = muladd_float(x, y, z)
-- /Source
def muladdFloat32 (x y z : Fl single) : Fl single :=
  let neg := x.signbit != y.signbit
  if x.isnan then quietFloatAt x else if y.isnan then quietFloatAt y else if z.isnan then quietFloatAt z
  else if (x.isinf && y.iszero) || (y.isinf && x.iszero) then invalidFloatAt single
  else if x.isinf || y.isinf then
    if z.isinf && neg != z.signbit then invalidFloatAt single else Fl.inf neg
  else if z.isinf then z
  else let a := x.toRat; let b := y.toRat; let c := z.toRat
       Fl.roundRat (a.1 * b.1 * (c.2 : Int) + c.1 * ((a.2 * b.2 : Nat) : Int))
         (a.2 * b.2 * c.2) (neg && z.signbit)

/-- Widened scalar multiplication dispatch. Reuses existing F64.mul at double precision.
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
-- /Source
def wideMultiply : (k : SmallFloatKind) → WideValue k → WideValue k → WideValue k
  | .f16, x, y => multiplyFloatAt x y
  | .f32, x, y => Fl.ofF64 (F64.mul (Fl.toF64 x) (Fl.toF64 y))

/-- Widened muladd dispatch; double precision directly reuses the installed callee.
Julia source: base/float.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::T, y::T, z::T) where {T<:IEEEFloat} = muladd_float(x, y, z)
-- /Source
def wideMuladd : (k : SmallFloatKind) → WideValue k → WideValue k → WideValue k → WideValue k
  | .f16, x, y, z => muladdFloat32 x y z
  | .f32, x, y, z => Fl.ofF64 (F64.muladd (Fl.toF64 x) (Fl.toF64 y) (Fl.toF64 z))

/-- The scalar reciprocal dependency is one(T)/x, with actual single/double operations.
Julia source: base/float.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::T, y::T) where {T<:IEEEFloat} = div_float(x, y)
-- /Source
def wideInverse : (k : SmallFloatKind) → WideValue k → WideValue k
  | .f16, x => divideFloatAt (Fl.ofInt 1) x
  | .f32, x => Fl.ofF64 (F64.div F64.one (Fl.toF64 x))

/-- Widened complex construction via the existing total format conversions, in real
then imaginary order. The target type maps follow base/float.jl:481-482.
Julia source: base/operators.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/operators.jl:975-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::T) where {T} = convert(widen(T), x)
-- /Source
def widenSmallComplex (k : SmallFloatKind) (z : Complex (SmallValue k)) : Complex (WideValue k) :=
  let re := Fl.convert (f := wideFormat k) z.re
  let im := Fl.convert (f := wideFormat k) z.im
  ⟨re, im⟩

/-- Typed oftype conversion back to the original component format; preserves order and all IEEE values.
Julia source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def narrowSmallComplex (k : SmallFloatKind) (z : Complex (WideValue k)) : Complex (SmallValue k) :=
  let re := Fl.convert (f := smallFormat k) z.re
  let im := Fl.convert (f := smallFormat k) z.im
  ⟨re, im⟩

/-- Real sign dependency at the existing scalar interface; input zero/NaN survives
when neither ordered comparison holds. All operations here are pure and total.
Julia source: base/number.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sign(x::Real) = ifelse(x < zero(x), oftype(one(x),-1), ifelse(x > zero(x), one(x), typeof(one(x))(x)))
-- /Source
def smallSign {k : SmallFloatKind} (x : SmallValue k) : SmallValue k :=
  let zero : SmallValue k := Fl.zero false
  if Fl.lt x zero then Fl.neg (Fl.ofInt 1)
  else if Fl.lt zero x then Fl.ofInt 1 else x

/-- Small floating multiplication by Bool, including signed strong zero.
The zero case is the exact copysign(zero(x),x) result.
Julia source: base/bool.jl:161-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/bool.jl:161-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function *(x::Bool, y::T)::promote_type(Bool,T) where T<:AbstractFloat
--     return ifelse(x, y, copysign(zero(y), y))
-- end
-- *(y::AbstractFloat, x::Bool) = x * y
--
-- /Source
def smallStrongBool {k : SmallFloatKind} (x : SmallValue k) (b : Bool) : SmallValue k :=
  if b then x else Fl.zero x.signbit

/-- Complete Float16/Float32 division over the source union. Preserves widening,
ordered intermediates, nonfinite branches and final narrowing. Scalar dependencies are closed executable definitions.
Julia source: base/complex.jl:379-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:379-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function /(z::Complex{T}, w::Complex{T}) where {T<:Union{Float16,Float32}}
--     c, d = reim(widen(w))
--     a, b = reim(widen(z))
--     if (isinf(c) | isinf(d))
--         if isfinite(z)
--             return complex(zero(T)*sign(real(z))*sign(real(w)), -zero(T)*sign(imag(z))*sign(imag(w)))
--         end
--         return T(NaN)+T(NaN)*im
--     end
--     mag = inv(muladd(c, c, d^2))
--     re_part = muladd(a, c, b*d)
--     im_part = muladd(b, c, -a*d)
--     return oftype(z, Complex(re_part*mag, im_part*mag))
-- end
-- /Source
def divideSmall (k : SmallFloatKind) (z w : Complex (SmallValue k)) : Complex (SmallValue k) :=
  let (c, d) := reimComplex (widenSmallComplex k w)
  let (a, b) := reimComplex (widenSmallComplex k z)
  if c.isinf || d.isinf then
    if isfinite_Complex Fl.isfinite z then
      let zero : SmallValue k := Fl.zero false
      ⟨multiplyFloatAt (multiplyFloatAt zero (smallSign z.re)) (smallSign w.re),
       multiplyFloatAt (multiplyFloatAt (Fl.neg zero) (smallSign z.im)) (smallSign w.im)⟩
    else
      let nan : SmallValue k := Fl.convert (Fl.ofF64 F64.nan)
      let nanImag := mul_Real_ComplexBool smallStrongBool nan im
      add_Real_Complex addFloatAt promote_same nan nanImag
  else
    let mag := wideInverse k (wideMuladd k c c (wideMultiply k d d))
    let rePart := wideMuladd k a c (wideMultiply k b d)
    let imPart := wideMuladd k b c (wideMultiply k (Fl.neg a) d)
    narrowSmallComplex k ⟨wideMultiply k rePart mag, wideMultiply k imPart mag⟩

/-- Complete Float16/Float32 reciprocal. The infinite branch implements the exact
copysign(zero(T),c) and flipsign(-zero(T),d) bit effects; finite arithmetic is widened before narrowing.
Julia source: base/complex.jl:476-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:476-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function inv(z::Complex{T}) where T<:Union{Float16,Float32}
--     c, d = reim(widen(z))
--     (isinf(c) | isinf(d)) && return complex(copysign(zero(T), c), flipsign(-zero(T), d))
--     mag = inv(muladd(c, c, d^2))
--     return oftype(z, Complex(c*mag, -d*mag))
-- end
-- /Source
def inverseSmall (k : SmallFloatKind) (z : Complex (SmallValue k)) : Complex (SmallValue k) :=
  let (c, d) := reimComplex (widenSmallComplex k z)
  if c.isinf || d.isinf then
    ⟨Fl.zero c.signbit, Fl.zero (!d.signbit)⟩
  else
    let mag := wideInverse k (wideMuladd k c c (wideMultiply k d d))
    narrowSmallComplex k ⟨wideMultiply k c mag, wideMultiply k (Fl.neg d) mag⟩

/-- Closed Float64 ssqs retains the actual exponent error channel instead of a
default on error. The exponent return range [-1074,1023] fits Julia Int64.
Julia source: base/complex.jl:519-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:519-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ssqs(x::T, y::T) where T<:Real
--     k::Int = 0
--     ρ = x*x + y*y
--     if !isfinite(ρ) && (isinf(x) || isinf(y))
--         ρ = convert(T, Inf)
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
--         m::T = max(abs(x), abs(y))
--         k = m==0 ? 0 : exponent(m)
--         xk, yk = ldexp(x,-k), ldexp(y,-k)
--         ρ = xk*xk + yk*yk
--     end
--     ρ, k
-- end
-- /Source
def scaledSquaresF64 (x y : F64) : Jl (F64 × JInt .i64) :=
  do
    let k := JInt.lit .i64 0
    let rho := F64.add (F64.mul x x) (F64.mul y y)
    if !F64.isfinite rho && (F64.isinf x || F64.isinf y) then
      return (F64.inf false, k)
    else if F64.isinf rho || (F64.eq rho Fl64.pzero &&
        (!F64.eq x Fl64.pzero || !F64.eq y Fl64.pzero)) ||
        F64.lt rho (F64.div (F64.nextfloat Fl64.pzero)
          (F64.mul Fl64.two (F64.mul Fl64.eps Fl64.eps))) then
      let m := Fl64.max (F64.abs x) (F64.abs y)
      let k ← if F64.eq m Fl64.pzero then pure (JInt.lit .i64 0)
        else do
          let exponent ← F64.exponent m
          pure (JInt.lit .i64 exponent)
      let xk := F64.ldexp x (-k).val
      let yk := F64.ldexp y (-k).val
      return (F64.add (F64.mul xk xk) (F64.mul yk yk), k)
    else
      return (rho, k)

/-- Closed source integer sinpi dependency. The original integer sign is tested
before conversion; machine-integer input is retained explicitly.
Julia source: base/special/trig.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/special/trig.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sinpi(x::Integer) = x >= 0 ? zero(float(x)) : -zero(float(x))
-- /Source
def sinpiIntPrimitive {t : IntTy} (x : JInt t) : F64 :=
  if x.val ≥ 0 then zero_F64 (F64.ofJInt x) else F64.neg (zero_F64 (F64.ofJInt x))

/-- Closed integer cospi dependency. Parity is tested on the integer, never on a
rounded Float64 conversion, so large 64/128-bit odd inputs remain correct.
Julia source: base/special/trig.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/special/trig.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cospi(x::Integer) = isodd(x) ? -one(float(x)) : one(float(x))
-- /Source
def cospiIntPrimitive {t : IntTy} (x : JInt t) : F64 :=
  if x.val % 2 != 0 then
    let _xf := F64.ofJInt x
    F64.neg F64.one
  else
    let _xf := F64.ofJInt x
    F64.one

/-- Integer sincospi dependency with explicit source evaluation order.
Julia source: base/special/trig.jl:1078-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/special/trig.jl:1078-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sincospi(x::Integer) = (sinpi(x), cospi(x))
-- /Source
def sincospiIntPrimitive {t : IntTy} (x : JInt t) : F64 × F64 :=
  let s := sinpiIntPrimitive x
  let c := cospiIntPrimitive x
  (s, c)

/-- Complete cispi specialization for all ten BitInteger types; uses parity before any floating conversion.
Julia source: base/complex.jl:618-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:618-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cispi(theta::Real) = Complex(reverse(sincospi(theta))...)
-- /Source
def cispiInt {t : IntTy} (x : JInt t) : ComplexF64 :=
  cispi_Real sincospiIntPrimitive x

/-- Close the Float64 Boolean exponent method with one(z) = ComplexF64(1,+0).
In particular false does not copy the input imaginary zero sign.
Julia source: base/complex.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
-- /Source
def powerF64Bool (z : ComplexF64) (b : Bool) : ComplexF64 :=
  pow_ComplexFloat_Bool F64.one Fl64.pzero z b

/-- Close both small IEEE Boolean exponent methods, preserving true-branch bits.
Julia source: base/complex.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
-- /Source
def powerSmallBool (k : SmallFloatKind) (z : Complex (SmallValue k)) (b : Bool) : Complex (SmallValue k) :=
  pow_ComplexFloat_Bool (Fl.ofInt 1) (Fl.zero false) z b

/-- Bool component type retains Bool one/zero under one(z). Machine-integer
component types reuse the already closed pow_ComplexInteger_Bool definition.
Julia source: base/complex.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)        # to resolve ambiguity
-- /Source
def powerBoolComplex (z : Complex Bool) (b : Bool) : Complex Bool :=
  pow_Complex_Bool (fun _ => ⟨true, false⟩) z b

/-- The five modes already represented by Float.Extras, plus the two other
standard public rounding modes. This represents all seven built-in modes, not
custom user-defined RoundingMode parameters. Source: base/rounding.jl:26-110. -/
inductive StandardRounding where
  | primitive (mode : Rounding)
  | nearestTiesUp
  | fromZero
  deriving DecidableEq, Repr

/-- Exact scalar RoundNearestTiesUp dependency, retaining both rounded additions
and the final copysign rather than replacing them with an ideal rounding oracle.
Julia source: base/floatfuncs.jl:156-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/floatfuncs.jl:156-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(x::T, ::RoundingMode{:NearestTiesUp}) where {T <: AbstractFloat}
--     copysign(floor((x + (T(0.25) - eps(T(0.5)))) + (T(0.25) + eps(T(0.5)))), x)
-- end
-- /Source
def roundNearestTiesUpF64 (x : F64) : F64 :=
  let quarter := F64.ofBits 0x3fd0000000000000
  let epsHalf := F64.eps Fl64.half
  let lo := F64.sub quarter epsHalf
  let hi := F64.add quarter epsHalf
  Fl64.copysign (F64.floor (F64.add (F64.add x lo) hi)) x

/-- Exact scalar RoundFromZero dependency at Float64.
Julia source: base/floatfuncs.jl:160-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/floatfuncs.jl:160-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.round(x::AbstractFloat, ::typeof(RoundFromZero))
--     signbit(x) ? round(x, RoundDown) : round(x, RoundUp)
-- end
-- /Source
def roundFromZeroF64 (x : F64) : F64 :=
  if F64.signbit x then F64.round x .RoundDown else F64.round x .RoundUp

/-- Closed scalar dispatch for the standard rounding arguments used by complex round.
The five primitive modes reuse F64.round; two source-defined modes are provided locally.
Julia source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundScalarF64 (x : F64) : StandardRounding → F64
  | .primitive m => F64.round x m
  | .nearestTiesUp => roundNearestTiesUpF64 x
  | .fromZero => roundFromZeroF64 x

/-- Float64 complex rounding with every standard rounding mode and no keywords.
Defaults preserve the source rule ri=rr. Keyword modes remain explicitly blocked.
Julia source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundComplexF64 (z : ComplexF64) (rr : StandardRounding := .primitive .RoundNearest)
    (ri : StandardRounding := rr) : ComplexF64 :=
  round_Complex (fun x m (_ : Unit) => roundScalarF64 x m) z rr ri ()

/-- Machine-integer complex rounding with no keywords. The scalar method at base/rounding.jl:497 is identity for every rounding mode.
Julia source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundComplexInt {t : IntTy} (z : Complex (JInt t)) (rr : StandardRounding := .primitive .RoundNearest)
    (ri : StandardRounding := rr) : Complex (JInt t) :=
  round_Complex (fun x (_ : StandardRounding) (_ : Unit) => x) z rr ri ()

/-- Bool is an Integer; no-keyword scalar rounding is the same identity method at base/rounding.jl:497.
Julia source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundComplexBool (z : Complex Bool) (rr : StandardRounding := .primitive .RoundNearest)
    (ri : StandardRounding := rr) : Complex Bool :=
  round_Complex (fun x (_ : StandardRounding) (_ : Unit) => x) z rr ri ()

/-- Close integer float conversion with actual source-specific Int128/UInt128 behavior.
Julia source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(z::Complex) = Complex(float(real(z)), float(imag(z)))
-- /Source
def floatComplexInt {t : IntTy} (z : Complex (JInt t)) : ComplexF64 :=
  float_Complex F64.ofJInt z

/-- Closed Bool-to-Float64 conversion, in real then imaginary order.
Julia source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(z::Complex) = Complex(float(real(z)), float(imag(z)))
-- /Source
def floatComplexBool (z : Complex Bool) : ComplexF64 :=
  float_Complex (fun b => if b then F64.one else Fl64.pzero) z

/-- Type-only targets of big; no GMP/MPFR value or allocation semantics are asserted. -/
inductive BigComponentType where
  | integer | floating
  deriving DecidableEq, Repr

/-- Closed type-level big for all BitInteger component types, using base/gmp.jl:489.
Julia source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
-- /Source
def bigComplexIntegerType (t : IntTy) : ComplexTy BigComponentType :=
  big_Type_Complex (fun _ : IntTy => BigComponentType.integer) t

/-- Closed type-level big for Bool, which dispatches as Integer at base/gmp.jl:489.
Julia source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
-- /Source
def bigComplexBoolType : ComplexTy BigComponentType :=
  big_Type_Complex (fun _ : Unit => BigComponentType.integer) ()

/-- Closed type-level big for Float64 using base/mpfr.jl:561. This returns a type tag, not an executable BigFloat value.
Julia source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
-- /Source
def bigComplexF64Type : ComplexTy BigComponentType :=
  big_Type_Complex (fun _ : Unit => BigComponentType.floating) ()

/-- Closed type-level big for Float16/Float32 using base/mpfr.jl:561.
Julia source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
-- /Source
def bigComplexSmallType (k : SmallFloatKind) : ComplexTy BigComponentType :=
  big_Type_Complex (fun _ : SmallFloatKind => BigComponentType.floating) k

/-- Closed ComplexF64 epsilon using actual scalar eps and hardware-FMA hypot.
The Jl result propagates any hypot error; no fallback is installed.
Julia source: base/complex.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(z::Complex{<:AbstractFloat}) = hypot(eps(real(z)), eps(imag(z)))
-- /Source
def epsilonComplexF64 (z : ComplexF64) : Jl F64 :=
  eps_Complex epsOf_F64 Fl64.hypot z

/-- Closed ComplexF64 type epsilon. The scalar square-root error channel remains
intact and multiplication is performed only after a successful sqrt.
Julia source: base/complex.jl:1166-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:1166-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(::Type{Complex{T}}) where {T<:AbstractFloat} = sqrt(2*one(T))*eps(T)
-- /Source
def epsilonTypeF64 : Jl F64 :=
  eps_Type_Complex Fl64.two Fl64.eps F64.sqrt mul_Jl_F64

end JuliaLean.base.complex.Models1Group19


namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-!
Effectful source-method bodies.  The type parameters of operation records are
carriers, not an assertion that Julia's result has the argument's runtime type.
They can be tagged sums of every runtime value admitted at that call site.
Only calls selected on types the source method leaves unfixed are parameters.
Native field projections and native Bool combination are executable.  Generic
callers retain selected component-query dispatch at every source call site.
-/

/-- Component queries selected on an unfixed Complex component type.  A is a
runtime-value carrier, not a claim that query results retain the stored field's
Julia type: it may be a tagged universe containing all input and output values.
The stored fields obey the source Complex representation invariant; selected
queries may return arbitrary tags, mutate, throw, or diverge.
Source reference: base/complex.jl:72,87; used by callers with unfixed types. -/
-- Source: base/complex.jl:72-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(z::Complex) = z.re
-- 
-- """
--     imag(z)
-- 
-- Return the imaginary part of the complex number `z`.
-- 
-- See also [`conj`](@ref), [`reim`](@ref), [`adjoint`](@ref), [`angle`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> imag(1 + 3im)
-- 3
-- ```
-- """
-- imag(z::Complex) = z.im
-- /Source
structure ComponentOps (m : Type → Type) (A : Type) where
  real : Complex A → m A
  imag : Complex A → m A

/-- The inherited component-query methods use the installed field projections.
This is an explicit native instance, not a restriction on generic callers.
Source reference: base/complex.jl:72,87. -/
-- Source: base/complex.jl:72-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(z::Complex) = z.re
-- 
-- """
--     imag(z)
-- 
-- Return the imaginary part of the complex number `z`.
-- 
-- See also [`conj`](@ref), [`reim`](@ref), [`adjoint`](@ref), [`angle`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> imag(1 + 3im)
-- 3
-- ```
-- """
-- imag(z::Complex) = z.im
-- /Source
def nativeComponents {m : Type → Type} [Pure m] {A : Type} : ComponentOps m A where
  real := fun z => pure (real_Complex z)
  imag := fun z => pure (imag_Complex z)

/-- Local exception extension for Julia's explicit type assertions.  `jl`
retains the installed exception classes; `user` permits arbitrary exceptions
from selected dispatch.  No existing error representation is changed.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
inductive Error (UserError : Type) where
  | jl (error : JlError)
  | typeError (context : String)
  | errorException (message : String)
  | undefRefError
  | user (error : UserError)

/-- A runtime subtype-test result retaining the actual accepted or rejected
value.  This is a representation partition, not an assumption about a callee.
In particular a selected constructor may return either branch.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
inductive Checked (Expected Other : Type) where
  | accepted (value : Expected)
  | rejected (value : Other)

/-- The fixed Core type-assertion operation, after its operand has evaluated.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def assertChecked {m : Type → Type} [Monad m] {E A Other : Type}
    [MonadExceptOf (Error E) m] (context : String) : Checked A Other → m A
  | .accepted value => pure value
  | .rejected _ => throwThe (Error E) (.typeError context)

/-- Dispatch of isreal on a Complex whose component type is unfixed.  The
inherited branch has the actual Base body when that target is fixed.  The
selectedCustom branch retains an open selected callee on an unfixed type,
including per-value method selection in recursive callers.  This is a call-site
adaptor used by the queued callers, not a callback for any caller's own body.
Source reference: base/complex.jl:149. -/
-- Source: base/complex.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isreal(z::Complex) = iszero(imag(z))
-- /Source
inductive IsRealDispatch (m : Type → Type) (A Result : Type) where
  | inherited (iszero : A → m Result)
  | selectedCustom (call : Complex A → m Result)

/-- The inherited isreal body still dispatches imag(z) on the unfixed
component type.  A selected custom isreal receives the original z instead.
No scalar return-type or correctness law is imposed.
Source reference: base/complex.jl:149. -/
-- Source: base/complex.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isreal(z::Complex) = iszero(imag(z))
-- /Source
def isRealComplex {m : Type → Type} [Monad m] {A Result : Type}
    (target : IsRealDispatch m A Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  match target with
  | .inherited iszero => do iszero (← parts.imag z)
  | .selectedCustom call => call z

/-- Operations selected by Complex(x::Real)'s unfixed argument/result types.
The two-argument call is not the one-argument method being modelled.
Source reference: base/complex.jl:18. -/
-- Source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real) = Complex(x, zero(x))
-- /Source
structure RealConstructorOps (m : Type → Type) (A Zero Result : Type) where
  zero : A → m Zero
  construct : A → Zero → m Result

/-- Preserve zero-before-construction, arbitrary changed result types, state,
and exceptions.  The two-argument constructor is open dispatch, not a supplied
implementation of this method or of its own recursion.
Source reference: base/complex.jl:18. -/
-- Source: base/complex.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex(x::Real) = Complex(x, zero(x))
-- /Source
def complexReal {m : Type → Type} [Monad m] {A Zero Result : Type}
    (ops : RealConstructorOps m A Zero Result) (x : A) : m Result := do
  let zero ← ops.zero x
  ops.construct x zero

/-- Dispatch of the two-argument typed constructor.  The target component
type and the argument type are not fixed by the source wrapper.
The record is specialized to the exact source target Complex{T}; Result does
not encode that target because a custom constructor may return another type.
Source reference: base/complex.jl:42. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
structure TypedRealConstructorOps (m : Type → Type) (A Result : Type) where
  construct : A → JInt .i64 → m Result

/-- The literal is Julia's native Int zero, not zero(x) and not an unbounded
Lean integer.  Custom two-argument construction is allowed to change type.
Source reference: base/complex.jl:42. -/
-- Source: base/complex.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(x::Real) where {T<:Real} = Complex{T}(x,0)
-- /Source
def complexTypedReal {m : Type → Type} {A Result : Type}
    (ops : TypedRealConstructorOps m A Result) (x : A) : m Result :=
  ops.construct x (JInt.lit .i64 0)

/-- The selected two-argument typed constructor for an unfixed component type.
The record is specialized to the exact target Complex{T}, independently of
the result carrier, which need not itself be Complex{T}.
Source reference: base/complex.jl:43. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
structure TypedComplexConstructorOps (m : Type → Type) (A Result : Type) where
  construct : A → A → m Result

/-- Retain each selected query and both arguments to the selected typed
constructor without converting or asserting them prematurely.
Source reference: base/complex.jl:43. -/
-- Source: base/complex.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Complex{T}(z::Complex) where {T<:Real} = Complex{T}(real(z),imag(z))
-- /Source
def complexTypedComplex {m : Type → Type} [Monad m] {A Result : Type}
    (ops : TypedComplexConstructorOps m A Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let r ← parts.real z
  let i ← parts.imag z
  ops.construct r i

/-- Open iszero/isreal and T(real(z)) dispatch, exposing both the condition's
runtime Bool check and the source's explicit result type assertion.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
structure RealConversionOps (m : Type → Type) (A T NotBool NotT : Type) where
  isreal : IsRealDispatch m A (Checked Bool NotBool)
  construct : A → m (Checked T NotT)
  typeName : String

/-- Check the imaginary part before attempting real conversion.  A bad
condition raises TypeError; a false condition raises InexactError; a successful
constructor return is checked by the explicit ::T assertion.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realFromComplex {m : Type → Type} [Monad m] {E A T NotBool NotT : Type}
    [MonadExceptOf (Error E) m]
    (ops : RealConversionOps m A T NotBool NotT) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents)
    (onInexact : Complex A → m T := fun _ =>
      throwThe (Error E) (.jl (.inexactError ops.typeName))) : m T := do
  let condition ← isRealComplex ops.isreal z parts
  let real ← assertChecked (E := E) "if" condition
  if real then
    let r ← parts.real z
    let value ← ops.construct r
    assertChecked (E := E) "T(real(z))::T" value
  else
    onInexact z

/-- The actual argument to Core.apply_type(Complex, ...), classified by the
builtin's admissibility test.  Parameter includes admitted type variables,
abstract/union/bottom parameters, not just concrete Real DataTypes.  Rejected
retains arbitrary non-admissible results of custom type-level operations.
Source reference: base/complex.jl:49-57. -/
-- Source: base/complex.jl:49-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- 
-- widen(::Type{Complex{T}}) where {T} = Complex{widen(T)}
-- 
-- float(::Type{Complex{T}}) where {T<:AbstractFloat} = Complex{T}
-- float(::Type{Complex{T}}) where {T} = Complex{float(T)}
-- /Source
inductive TypeParameter (Parameter Rejected : Type) where
  | admissible (parameter : Parameter)
  | rejected (argument : Rejected)

/-- Effectful promote_type on the two unfixed component-type arguments.
Source reference: base/complex.jl:49-52. -/
-- Source: base/complex.jl:49-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real} =
--     Complex{promote_type(T,S)}
-- /Source
structure PromoteTypeOps (m : Type → Type) (R Parameter Rejected : Type) where
  promote : R → R → m (TypeParameter Parameter Rejected)

/-- Effectful scalar-type widening, with unrestricted returned runtime values.
Source reference: base/complex.jl:54. -/
-- Source: base/complex.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Complex{T}}) where {T} = Complex{widen(T)}
-- /Source
structure WidenTypeOps (m : Type → Type) (R Parameter Rejected : Type) where
  widen : R → m (TypeParameter Parameter Rejected)

/-- Effectful float(T), including custom non-type and inadmissible results.
Source reference: base/complex.jl:57. -/
-- Source: base/complex.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(::Type{Complex{T}}) where {T} = Complex{float(T)}
-- /Source
structure FloatTypeOps (m : Type → Type) (R Parameter Rejected : Type) where
  toFloat : R → m (TypeParameter Parameter Rejected)

/-- The scalar zero operation is dispatched on the unfixed Real type.
Source reference: base/complex.jl:89. -/
-- Source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- imag(x::Real) = zero(x)
-- /Source
structure ImaginaryRealOps (m : Type → Type) (A Result : Type) where
  zero : A → m Result

/-- Type-changing, effectful imaginary-part query for Real values.
Source reference: base/complex.jl:89. -/
-- Source: base/complex.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- imag(x::Real) = zero(x)
-- /Source
def imaginaryReal {m : Type → Type} {A Result : Type}
    (ops : ImaginaryRealOps m A Result) (x : A) : m Result :=
  ops.zero x

/-- The argument of reim is unrestricted, so both component queries are open
dispatch and their result carriers need not agree.
Source reference: base/complex.jl:102. -/
-- Source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reim(z) = (real(z), imag(z))
-- /Source
structure ReimOps (m : Type → Type) (A R I : Type) where
  real : A → m R
  imag : A → m I

/-- Tuple construction evaluates real before imag, preserving errors and
state from each selected call.
Source reference: base/complex.jl:102. -/
-- Source: base/complex.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reim(z) = (real(z), imag(z))
-- /Source
def realImaginary {m : Type → Type} [Monad m] {A R I : Type}
    (ops : ReimOps m A R I) (x : A) : m (R × I) := do
  let r ← ops.real x
  let i ← ops.imag x
  pure (r, i)

/-- Dependent runtime values carry their actual typeof tag.  A returned type
object has its own DataType/UnionAll runtime tag, not the type it denotes.
Source reference: base/complex.jl:120. -/
-- Source: base/complex.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(T::Type) = typeof(real(zero(T)))
-- /Source
structure RealTypeQueryOps (m : Type → Type) (Tag : Type) (Value : Tag → Type) where
  zero : Tag → m (Sigma Value)
  real : Sigma Value → m (Sigma Value)

/-- The fixed typeof primitive is a tag projection, not an arbitrary callee.
Both preceding operations retain their full effects and changed result types.
Source reference: base/complex.jl:120. -/
-- Source: base/complex.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(T::Type) = typeof(real(zero(T)))
-- /Source
def realTypeQuery {m : Type → Type} [Monad m] {Tag : Type} {Value : Tag → Type}
    (ops : RealTypeQueryOps m Tag Value) (t : Tag) : m Tag := do
  let zero ← ops.zero t
  let value ← ops.real zero
  pure value.1

/-- Scalar predicates have no enforced return annotation.  Bool results have
a closed native branch; all other result types remain explicit in Other.
Source reference: base/complex.jl:150-155. -/
-- Source: base/complex.jl:150-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
inductive PredicateValue (Other : Type) where
  | boolean (value : Bool)
  | other (value : Other)

/-- All leaves are dispatch-selected on unfixed types.  Bool/Bool combination
does not call andOther or orOther.  Those fields cover only other operand types.
Source reference: base/complex.jl:150-155. -/
-- Source: base/complex.jl:150-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
structure PredicateOps (m : Type → Type) (A Other : Type) where
  isreal : IsRealDispatch m A (PredicateValue Other)
  isinteger : A → m (PredicateValue Other)
  isfinite : A → m (PredicateValue Other)
  isnan : A → m (PredicateValue Other)
  isinf : A → m (PredicateValue Other)
  iszero : A → m (PredicateValue Other)
  isone : A → m (PredicateValue Other)
  andOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)
  orOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)

/-- Native Bool & is fixed; both operands have already been evaluated.
Source reference: base/bool.jl:14; base/complex.jl:150-155. -/
-- Source: base/bool.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (&)(x::Bool, y::Bool) = and_int(x, y)
-- /Source
def predicateAnd {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (x y : PredicateValue Other) : m (PredicateValue Other) :=
  match x, y with
  | .boolean a, .boolean b => pure (.boolean (a && b))
  | _, _ => ops.andOther x y

/-- Native Bool | is fixed; its eager evaluation is supplied by each caller.
Source reference: base/bool.jl:15; base/complex.jl:152-153. -/
-- Source: base/bool.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (|)(x::Bool, y::Bool) = or_int(x, y)
-- /Source
def predicateOr {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (x y : PredicateValue Other) : m (PredicateValue Other) :=
  match x, y with
  | .boolean a, .boolean b => pure (.boolean (a || b))
  | _, _ => ops.orOther x y

/-- The second test is eager even when isreal returned false.
Source reference: base/complex.jl:150. -/
-- Source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- /Source
def integerComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← isRealComplex ops.isreal z parts
  let value ← parts.real z
  let i ← ops.isinteger value
  predicateAnd ops r i

/-- Finiteness evaluates both components before & dispatch.
Source reference: base/complex.jl:151. -/
-- Source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- /Source
def finiteComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← ops.isfinite (← parts.real z)
  let i ← ops.isfinite (← parts.imag z)
  predicateAnd ops r i

/-- NaN detection evaluates the imaginary predicate even after true.
Source reference: base/complex.jl:152. -/
-- Source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- /Source
def nanComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← ops.isnan (← parts.real z)
  let i ← ops.isnan (← parts.imag z)
  predicateOr ops r i

/-- Infinity detection retains both component calls and their exceptions.
Source reference: base/complex.jl:153. -/
-- Source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- /Source
def infiniteComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← ops.isinf (← parts.real z)
  let i ← ops.isinf (← parts.imag z)
  predicateOr ops r i

/-- Both scalar zero tests precede the eager combination.
Source reference: base/complex.jl:154. -/
-- Source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- /Source
def zeroComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← ops.iszero (← parts.real z)
  let i ← ops.iszero (← parts.imag z)
  predicateAnd ops r i

/-- The real coordinate is tested for one and the imaginary coordinate for
zero, in that order, without short circuiting.
Source reference: base/complex.jl:155. -/
-- Source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
def oneComplex {m : Type → Type} [Monad m] {A Other : Type}
    (ops : PredicateOps m A Other) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let r ← ops.isone (← parts.real z)
  let i ← ops.iszero (← parts.imag z)
  predicateAnd ops r i

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-!
Concrete two-argument Core.getfield for the fixed native indices used by Julia
lowering.  Object representations contain actual field storage; no primitive
result, exception, or effect is supplied by a callback.  Immutable storage is
part of a value's representation.  Mutable storage is read anew from FieldHeap
for every field access, preserving object identity and aliasing across selected
iterator calls.  All Julia runtime objects are included: type objects and other
runtime structures have their actual fields, primitive zero-field objects have
empty storage, and modules use the explicit getglobal path.

The local C excerpts have documented exact-pin provenance in adjacent packet
metadata and notes; no independently authenticated network retrieval is claimed.
The output NOTES.md records the local file hashes and provenance details.
-/

/-- The logical contents of a stored field.  A value includes initialized
references, singleton/inline values, and the actual arbitrary bits of an
uninitialized isbits field.  nullReference denotes an actual missing reference,
including an inline aggregate's runtime undefined-reference sentinel; it does
not classify all uninitialized data as an error.
Source reference: src/datatype.c:1886-1943. -/
-- Source: src/datatype.c:1936-1943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_get_nth_field_checked(jl_value_t *v, size_t i)
-- {
--     jl_value_t *r = jl_get_nth_field(v, i);
--     if (__unlikely(r == NULL))
--         jl_throw(jl_undefref_exception);
--     return r;
-- }
-- 
-- /Source
inductive FieldSlot (V : Type) where
  | value (value : V)
  | nullReference

/-- Actual field storage with the runtime layout's UInt32 field count.  The
array is representation data, not a Julia array argument or an unbounded list
standing in for one.  The count equality enforces the actual machine-sized
layout and lets bounds checks inspect the stored slots directly.
Source reference: src/datatype.c:190-205. -/
-- Source: src/datatype.c:190-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- static jl_datatype_layout_t *jl_get_layout(uint32_t sz,
--                                            uint32_t nfields,
--                                            uint32_t npointers,
--                                            uint32_t alignment,
--                                            int haspadding,
--                                            int isbitsegal,
--                                            int arrayelem,
--                                            uint8_t unused_bits,
--                                            jl_fielddesc32_t desc[],
--                                            uint32_t pointers[]) JL_NOTSAFEPOINT
-- {
--     assert(alignment); // should have been verified by caller
-- 
--     // compute the smallest fielddesc type that can hold the layout description
--     int fielddesc_type = JL_FIELDDESC_8;
-- /Source
structure FieldStorage (V : Type) where
  count : JInt .u32
  slots : Array (FieldSlot V)
  count_eq : slots.size = count.val.toNat

/-- Pure representation metadata distinguishes the module special case from
actual immutable fields and a mutable object's stable heap identity.  This
partition does not return a field-access outcome or run user code.
Source reference: src/builtins.c:1217-1221. -/
-- Source: src/builtins.c:1217-1221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     jl_value_t *v = args[0];
--     jl_value_t *vt = jl_typeof(v);
--     if (vt == (jl_value_t*)jl_module_type)
--         return jl_f_getglobal(NULL, args, 2); // we just ignore the atomic order and boundschecks
--     jl_datatype_t *st = (jl_datatype_t*)vt;
-- /Source
inductive FieldDescriptor (Ref V : Type) where
  | moduleValue
  | immutableValue (storage : FieldStorage V)
  | mutableValue (reference : Ref)

/-- The current object store.  Every referenced object has its actual field
storage here, including undefined-reference slots.  Selected callees share
this state and can mutate stored fields; a read never caches both fields of
an iterator result in advance.  Ref is an object identity, not an array index.
Source reference: src/datatype.c:1886-1895. -/
-- Source: src/datatype.c:1886-1895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_get_nth_field(jl_value_t *v, size_t i)
-- {
--     jl_datatype_t *st = (jl_datatype_t*)jl_typeof(v);
--     if (i >= jl_datatype_nfields(st))
--         jl_bounds_error_int(v, i + 1);
--     size_t offs = jl_field_offset(st, i);
--     if (jl_field_isptr(st, i)) {
--         return jl_atomic_load_relaxed((_Atomic(jl_value_t*)*)((char*)v + offs));
--     }
--     jl_value_t *ty = jl_field_type_concrete(st, i);
-- /Source
structure FieldHeap (Ref V : Type) where
  objects : Ref → FieldStorage V

/-- The only native field indices introduced by the two-value destructuring
lowering.  No arbitrary Julia indexing or machine arithmetic is substituted.
Source reference: src/julia-syntax.scm:1888-1910. -/
-- Source: src/julia-syntax.scm:1888-1910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (define (lower-tuple-assignment lhss x (wrap (lambda (x i) x)))
--   (let ((t (make-ssavalue)))
--     `(block
--       (= ,t ,x)
--       ,@(let loop ((lhs lhss)
--                    (i   1))
--           (if (null? lhs) '()
--               (cons (if (eventually-call? (car lhs))
--                         ;; if this is a function assignment, avoid putting our ssavalue
--                         ;; inside the function and instead create a capture-able variable.
--                         ;; issue #22032
--                         (let ((temp (gensy)))
--                           `(block
--                             (local-def ,temp)
--                             (= ,temp (call (core getfield) ,t ,i))
--                             ,(wrap `(= ,(car lhs) ,temp) i)))
--                         (wrap
--                           `(= ,(car lhs)
--                             (call (core getfield) ,t ,i)) i))
--                     (loop (cdr lhs)
--                           (+ i 1)))))
--       ,t)))
-- 
-- /Source
inductive FieldIndex where
  | first
  | second

/-- Complete Core.getfield(value, 1/2) behavior at its fixed two-argument
call shape.  Module values fail getglobal's Symbol check before bounds logic.
Every other runtime object uses its actual field count, then reads the actual
stored value or raises UndefRefError for a missing reference.  The default
unspecified order accepts both atomic and non-atomic fields; the runtime's
inline boxing/copy retains the represented value and internal references.
Source reference: src/builtins.c:1173-1234,1572-1584; src/datatype.c:1886-1943. -/
-- Source: src/builtins.c:1202-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_getfield)
-- {
--     enum jl_memory_order order = jl_memory_order_unspecified;
--     JL_NARGS(getfield, 2, 4);
--     if (nargs == 4) {
--         JL_TYPECHK(getfield, symbol, args[2]);
--         JL_TYPECHK(getfield, bool, args[3]);
--         order = jl_get_atomic_order_checked((jl_sym_t*)args[2], 1, 0);
--     }
--     else if (nargs == 3) {
--         if (!jl_is_bool(args[2])) {
--             JL_TYPECHK(getfield, symbol, args[2]);
--             order = jl_get_atomic_order_checked((jl_sym_t*)args[2], 1, 0);
--         }
--     }
--     jl_value_t *v = args[0];
--     jl_value_t *vt = jl_typeof(v);
--     if (vt == (jl_value_t*)jl_module_type)
--         return jl_f_getglobal(NULL, args, 2); // we just ignore the atomic order and boundschecks
--     jl_datatype_t *st = (jl_datatype_t*)vt;
--     size_t idx = get_checked_fieldindex("getfield", st, v, args[1], 0);
--     int isatomic = jl_field_isatomic(st, idx);
--     if (!isatomic && order != jl_memory_order_notatomic && order != jl_memory_order_unspecified)
--         jl_atomic_error("getfield: non-atomic field cannot be accessed atomically");
--     if (isatomic && order == jl_memory_order_notatomic)
--         jl_atomic_error("getfield: atomic field cannot be accessed non-atomically");
--     if (order >= jl_memory_order_seq_cst)
--         jl_fence();
--     v = jl_get_nth_field_checked(v, idx); // `v` already had at least consume ordering
--     if (order >= jl_memory_order_acquire)
--         jl_fence();
--     return v;
-- }
-- /Source
-- Source: src/builtins.c:1173-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t get_checked_fieldindex(const char *name, jl_datatype_t *st, jl_value_t *v, jl_value_t *arg, int mutabl) JL_CANSAFEPOINT
-- {
--     if (mutabl) {
--         if (st == jl_module_type)
--             jl_error("cannot assign variables in other modules");
--         if (!st->name->mutabl)
--             jl_errorf("%s: immutable struct of type %s cannot be changed", name, jl_symbol_name(st->name->name));
--     }
--     size_t idx;
--     if (jl_is_long(arg)) {
--         idx = jl_unbox_long(arg) - 1;
--         if (idx >= jl_datatype_nfields(st))
--             jl_bounds_error(v, arg);
--     }
--     else if (jl_is_symbol(arg)) {
--         idx = jl_field_index(st, (jl_sym_t*)arg, 1);
--     }
--     else {
--         jl_value_t *ts[2] = {(jl_value_t*)jl_long_type, (jl_value_t*)jl_symbol_type};
--         jl_value_t *t = jl_type_union(ts, 2);
--         jl_type_error(name, t, arg);
--     }
-- /Source
-- Source: src/builtins.c:1572-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_getglobal)
-- {
--     enum jl_memory_order order = jl_memory_order_monotonic;
--     JL_NARGS(getglobal, 2, 3);
--     if (nargs == 3) {
--         JL_TYPECHK(getglobal, symbol, args[2]);
--         order = jl_get_atomic_order_checked((jl_sym_t*)args[2], 1, 0);
--     }
--     jl_module_t *mod = (jl_module_t*)args[0];
--     jl_sym_t *sym = (jl_sym_t*)args[1];
--     JL_TYPECHK(getglobal, module, (jl_value_t*)mod);
--     JL_TYPECHK(getglobal, symbol, (jl_value_t*)sym);
--     if (order == jl_memory_order_notatomic)
-- /Source
-- Source: src/datatype.c:1886-1943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_get_nth_field(jl_value_t *v, size_t i)
-- {
--     jl_datatype_t *st = (jl_datatype_t*)jl_typeof(v);
--     if (i >= jl_datatype_nfields(st))
--         jl_bounds_error_int(v, i + 1);
--     size_t offs = jl_field_offset(st, i);
--     if (jl_field_isptr(st, i)) {
--         return jl_atomic_load_relaxed((_Atomic(jl_value_t*)*)((char*)v + offs));
--     }
--     jl_value_t *ty = jl_field_type_concrete(st, i);
--     int isatomic = jl_field_isatomic(st, i);
--     if (jl_is_uniontype(ty)) {
--         assert(!isatomic);
--         size_t fsz = jl_field_size(st, i);
--         uint8_t sel = ((uint8_t*)v)[offs + fsz - 1];
--         ty = jl_nth_union_component(ty, sel);
--         jl_value_t *layout_ty = normalize_typeofbottom_layout_alias(ty);
--         if (jl_is_datatype_singleton((jl_datatype_t*)layout_ty))
--             return ((jl_datatype_t*)layout_ty)->instance;
--     }
--     jl_value_t *layout_ty = normalize_typeofbottom_layout_alias(ty);
--     jl_value_t *r;
--     size_t fsz = jl_datatype_size(layout_ty);
--     int needlock = (isatomic && fsz > MAX_ATOMIC_SIZE);
--     if (isatomic && !needlock) {
--         r = jl_atomic_new_bits(layout_ty, (char*)v + offs);
--     }
--     else if (needlock) {
--         jl_task_t *ct = jl_current_task;
--         r = jl_gc_alloc(ct->ptls, fsz, layout_ty);
--         jl_lock_value((jl_mutex_t*)v);
--         memcpy((char*)r, (char*)v + offs, fsz);
--         jl_unlock_value((jl_mutex_t*)v);
--     }
--     else {
--         // TODO: a finalizer here could make the isunion case not quite right
--         r = jl_new_bits(layout_ty, (char*)v + offs);
--     }
--     return undefref_check((jl_datatype_t*)layout_ty, r);
-- }
-- 
-- JL_DLLEXPORT jl_value_t *jl_get_nth_field_noalloc(jl_value_t *v JL_PROPAGATES_ROOT, size_t i) JL_NOTSAFEPOINT
-- {
--     jl_datatype_t *st = (jl_datatype_t*)jl_typeof(v);
--     assert(i < jl_datatype_nfields(st));
--     size_t offs = jl_field_offset(st,i);
--     assert(jl_field_isptr(st,i));
--     return jl_atomic_load_relaxed((_Atomic(jl_value_t*)*)((char*)v + offs));
-- }
-- 
-- JL_DLLEXPORT jl_value_t *jl_get_nth_field_checked(jl_value_t *v, size_t i)
-- {
--     jl_value_t *r = jl_get_nth_field(v, i);
--     if (__unlikely(r == NULL))
--         jl_throw(jl_undefref_exception);
--     return r;
-- }
-- 
-- /Source
def getfieldFixed {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (value : V) (index : FieldIndex) : m V := do
  let storage : FieldStorage V ← match view value with
    | .moduleValue => throwThe (Error E) (.typeError "getglobal")
    | .immutableValue storage => pure storage
    | .mutableValue reference => do
        let heap ← getThe (FieldHeap Ref V)
        pure (heap.objects reference)
  let position : Nat := match index with | .first => 0 | .second => 1
  match storage.slots[position]? with
  | none => throwThe (Error E) (.jl .boundsError)
  | some .nullReference => throwThe (Error E) .undefRefError
  | some (.value actual) => pure actual

/-- Actual indexed_iterate dispatch on the unfixed iterable result type.
The return is an arbitrary runtime value, never assumed to be a tuple or a
pair of value/state.  first and next receive their literal native Int indices
and the actual state extracted from the first result at the source call sites.
Source reference: base/tuple.jl:161-172; src/julia-syntax.scm:2601-2609. -/
-- Source: base/tuple.jl:161-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (@inline; (a[i], i+1))
-- function indexed_iterate(I, i)
--     x = iterate(I)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- function indexed_iterate(I, i, state)
--     x = iterate(I, state)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- /Source
structure IndexedIterateOps (m : Type → Type) (V : Type) where
  first : V → JInt .i64 → m V
  next : V → JInt .i64 → V → m V

/-- Full two-value destructuring of an arbitrary selected result.  Julia
reads first-result field one, then field two; passes that actual state to the
second indexed_iterate; and reads only field one of the second result.  In
particular a one-field second result is sufficient, while an absent or
undefined first-result state fails before the second iterator call.  Effects
and errors retain the shared heap at every boundary.
Source reference: src/julia-syntax.scm:1888-1910,2564-2609. -/
-- Source: src/julia-syntax.scm:2601-2609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             (cons (expand-forms
--                     (lower-tuple-assignment
--                       (if (= i n)
--                           (list lhs-)
--                           (list lhs- st))
--                       `(call (top indexed_iterate)
--                              ,xx ,i ,@(if (eq? i 1) '() `(,st))) wrapfirst))
--                   (destructure- (+ i 1) (cdr lhss) xx n st end wrap))))))
-- 
-- /Source
def destructureTwo {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : IndexedIterateOps m V)
    (iterable : V) : m (V × V) := do
  let firstResult ← ops.first iterable (JInt.lit .i64 1)
  let firstValue ← getfieldFixed (E := E) view firstResult .first
  let state ← getfieldFixed (E := E) view firstResult .second
  let secondResult ← ops.next iterable (JInt.lit .i64 2) state
  let secondValue ← getfieldFixed (E := E) view secondResult .first
  pure (firstValue, secondValue)

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean
open scoped Lean.Order

/-- Exact dispatch classification at a scalar predicate call.  A contains
arbitrary runtime values, including a Complex returned by a custom getter.
An inherited payload decodes that same value without changing its identity;
selectedOther means any different selected method.  This is runtime metadata,
not a callee correctness premise.
Source reference: base/complex.jl:150-155. -/
-- Source: base/complex.jl:150-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
inductive PredicateTarget (A : Type) where
  | inherited (value : Complex A)
  | selectedOther

/-- Full same-method recursion at selected isfinite calls.  The one-step
source body is the helper finiteComplex; its recursive callback is supplied
here by the model itself, never by a caller.  Partial fixed points preserve
nontermination without a fuel cutoff or a fabricated successful result.
Source reference: base/complex.jl:151. -/
-- Source: base/complex.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isfinite(z::Complex) = isfinite(real(z)) & isfinite(imag(z))
-- /Source
def finiteComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents) :
    m (PredicateValue Other) :=
  finiteComplex
    { ops with
      isfinite := fun value => match target value with
        | .inherited next => finiteComplexFull ops target next parts
        | .selectedOther => ops.isfinite value }
    z parts
partial_fixpoint monotonicity by
  unfold finiteComplex predicateAnd
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Explicit selected-method recursion, including type-changing custom
component queries.  Calls to a different selected method retain their arbitrary
results and effects; this exact fallback never goes through a caller callback.
Source reference: base/complex.jl:150. -/
-- Source: base/complex.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(z::Complex) = isreal(z) & isinteger(real(z))
-- /Source
def integerComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents)
    (isrealCall : Complex A → m (PredicateValue Other) :=
      fun value => isRealComplex ops.isreal value parts) : m (PredicateValue Other) :=
  integerComplex
    { ops with
      isreal := .selectedCustom isrealCall
      isinteger := fun value => match target value with
        | .inherited next => integerComplexFull ops target next parts isrealCall
        | .selectedOther => ops.isinteger value }
    z parts
partial_fixpoint monotonicity by
  unfold integerComplex predicateAnd
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Explicit selected-method recursion, including type-changing custom
component queries.  Calls to a different selected method retain their arbitrary
results and effects; this exact fallback never goes through a caller callback.
Source reference: base/complex.jl:152. -/
-- Source: base/complex.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnan(z::Complex) = isnan(real(z)) | isnan(imag(z))
-- /Source
def nanComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents) :
    m (PredicateValue Other) :=
  nanComplex
    { ops with
      isnan := fun value => match target value with
        | .inherited next => nanComplexFull ops target next parts
        | .selectedOther => ops.isnan value }
    z parts
partial_fixpoint monotonicity by
  unfold nanComplex predicateOr
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Explicit selected-method recursion, including type-changing custom
component queries.  Calls to a different selected method retain their arbitrary
results and effects; this exact fallback never goes through a caller callback.
Source reference: base/complex.jl:153. -/
-- Source: base/complex.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(z::Complex) = isinf(real(z)) | isinf(imag(z))
-- /Source
def infiniteComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents) :
    m (PredicateValue Other) :=
  infiniteComplex
    { ops with
      isinf := fun value => match target value with
        | .inherited next => infiniteComplexFull ops target next parts
        | .selectedOther => ops.isinf value }
    z parts
partial_fixpoint monotonicity by
  unfold infiniteComplex predicateOr
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Explicit selected-method recursion, including type-changing custom
component queries.  Calls to a different selected method retain their arbitrary
results and effects; this exact fallback never goes through a caller callback.
Source reference: base/complex.jl:154. -/
-- Source: base/complex.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iszero(z::Complex) = iszero(real(z)) & iszero(imag(z))
-- /Source
def zeroComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents) :
    m (PredicateValue Other) :=
  zeroComplex
    { ops with
      iszero := fun value => match target value with
        | .inherited next => zeroComplexFull ops target next parts
        | .selectedOther => ops.iszero value }
    z parts
partial_fixpoint monotonicity by
  unfold zeroComplex predicateAnd
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Explicit selected-method recursion, including type-changing custom
component queries.  Calls to a different selected method retain their arbitrary
results and effects; this exact fallback never goes through a caller callback.
Source reference: base/complex.jl:155. -/
-- Source: base/complex.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isone(z::Complex) = isone(real(z)) & iszero(imag(z))
-- /Source
def oneComplexFull {m : Type → Type} [Monad m] {A Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : PredicateOps m A Other) (target : A → PredicateTarget A)
    (z : Complex A) (parts : ComponentOps m A := nativeComponents) :
    m (PredicateValue Other) :=
  oneComplex
    { ops with
      isone := fun value => match target value with
        | .inherited next => oneComplexFull ops target next parts
        | .selectedOther => ops.isone value }
    z parts
partial_fixpoint monotonicity by
  unfold oneComplex predicateAnd
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Both error-branch callees are selected on the original unfixed target T.
The record is specialized to that exact T: nameOf is nameof(T), and makeInexact
is InexactError(name,T,z).  Error E represents the actual returned throw object,
including a custom constructor result that is not an Exception subtype.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
structure ConversionFailureOps (m : Type → Type) (E A Name : Type) where
  nameOf : m Name
  makeInexact : Name → Complex A → m (Error E)

/-- Conversion can reselect the same T(::Complex) fallback if a selected
real getter returns another Complex.  The payload decodes that exact argument;
selectedOther means a different constructor method.  A recursive return already
satisfies T, so the enclosing source assertion receives its accepted partition.
Source reference: base/complex.jl:44-45. -/
-- Source: base/complex.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(z::Complex) where {T<:Real} =
--     isreal(z) ? T(real(z))::T : throw(InexactError(nameof(T), T, z))
-- /Source
def realFromComplexFull {m : Type → Type} [Monad m] {E A T NotBool NotT Name : Type}
    [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : RealConversionOps m A T NotBool NotT)
    (target : A → PredicateTarget A) (failure : ConversionFailureOps m E A Name)
    (z : Complex A)
    (parts : ComponentOps m A := nativeComponents)
    (isrealCall : Complex A → m (Checked Bool NotBool) :=
      fun value => isRealComplex ops.isreal value parts) : m T :=
  realFromComplex (E := E)
    { ops with
      isreal := .selectedCustom isrealCall
      construct := fun value => match target value with
        | .inherited next => do
            let result ← realFromComplexFull (E := E) ops target failure next parts isrealCall
            pure (.accepted result)
        | .selectedOther => ops.construct value }
    z parts (fun value => do
      let name ← failure.nameOf
      let thrown ← failure.makeInexact name value
      throwThe (Error E) thrown)
partial_fixpoint monotonicity by
  unfold realFromComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Exact real(::Type) dispatch metadata after zero(T), including a value
which is itself a type object.  The inherited case names the original decoded
argument type; all different real methods remain selectedOther.
Source reference: base/complex.jl:120. -/
-- Source: base/complex.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(T::Type) = typeof(real(zero(T)))
-- /Source
inductive RealTypeQueryTarget (Tag : Type) where
  | inherited (argument : Tag)
  | selectedOther

/-- A recursive real(::Type) result is a type object.  typeObject is its
faithful representation injection, carrying the object's actual typeof tag
(DataType, UnionAll, etc.); it is not another dispatched Julia operation.
The outer typeof therefore inspects the returned type object, rather than
incorrectly returning the inner recursive type descriptor directly.
Source reference: base/complex.jl:120. -/
-- Source: base/complex.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- real(T::Type) = typeof(real(zero(T)))
-- /Source
def realTypeQueryFull {m : Type → Type} [Monad m] {Tag : Type} {Value : Tag → Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : RealTypeQueryOps m Tag Value)
    (target : Sigma Value → RealTypeQueryTarget Tag)
    (typeObject : Tag → Sigma Value) (t : Tag) : m Tag :=
  realTypeQuery
    { ops with
      real := fun value => match target value with
        | .inherited next => do
            let result ← realTypeQueryFull ops target typeObject next
            pure (typeObject result)
        | .selectedOther => ops.real value }
    t
partial_fixpoint monotonicity by
  unfold realTypeQuery
  dsimp only
  repeat' (first | assumption | monotonicity)

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- One-argument constructor selection on the unfixed scalar type.
Source reference: base/complex.jl:169. -/
-- Source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real) = Complex(x)
-- /Source
structure PublicOneOps (m : Type → Type) (A Result : Type) where
  construct : A → m Result

/-- Public complex(x) retains the selected one-argument construction.
Source reference: base/complex.jl:169. -/
-- Source: base/complex.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real) = Complex(x)
-- /Source
def publicComplexOne {m : Type → Type} {A Result : Type}
    (ops : PublicOneOps m A Result) (x : A) : m Result :=
  ops.construct x

/-- Two-argument constructor selection on the unfixed scalar argument types.
Source reference: base/complex.jl:170. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
structure PublicTwoOps (m : Type → Type) (A B Result : Type) where
  construct : A → B → m Result

/-- Public complex(x,y) passes the original two values in source order.
Source reference: base/complex.jl:170. -/
-- Source: base/complex.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- complex(x::Real, y::Real) = Complex(x, y)
-- /Source
def publicComplexTwo {m : Type → Type} {A B Result : Type}
    (ops : PublicTwoOps m A B Result) (x : A) (y : B) : m Result :=
  ops.construct x y

/-- Result injections for an ordinary ifelse call with differently typed
branches.  Selected non-Bool-condition methods may have a third result type.
Source reference: base/complex.jl:197. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
inductive IfElseResult (Then Else Custom : Type) where
  | thenValue (value : Then)
  | elseValue (value : Else)
  | customValue (value : Custom)

/-- signbit and complex negation dispatch on unfixed scalar/component types.
ifelse is also selected on unfixed branch-value types, even for a Bool
condition; a more-specific user method can override the inherited fallback.
Source reference: base/complex.jl:197. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
structure FlipSignOps (m : Type → Type) (A Sign OtherSign Negative Custom : Type) where
  signbit : Sign → m (PredicateValue OtherSign)
  negate : Complex A → m Negative
  ifelse : PredicateValue OtherSign → Negative → Complex A → m Custom

/-- The inherited Bool-condition method of ifelse; the result injections
retain different branch types.  This is a closed concrete callee for native
instantiations, not an imposed law for selected custom dispatch.
Source reference: base/essentials.jl:894. -/
-- Source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
-- /Source
def nativeIfElse {Then Else : Type} (condition : Bool) (yes : Then) (no : Else) :
    IfElseResult Then Else Empty :=
  if condition then .thenValue yes else .elseValue no

/-- Evaluate signbit and then -x before the ordinary ifelse call.  A false
sign does not suppress negation effects or errors; a more-specific ifelse
method can be selected on any of the argument types, including Bool conditions.
Source reference: base/complex.jl:197. -/
-- Source: base/complex.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Complex, y::Real) = ifelse(signbit(y), -x, x)
-- /Source
def flipSignComplex {m : Type → Type} [Monad m]
    {A Sign OtherSign Negative Custom : Type}
    (ops : FlipSignOps m A Sign OtherSign Negative Custom)
    (x : Complex A) (y : Sign) : m Custom := do
  let sign ← ops.signbit y
  let negative ← ops.negate x
  ops.ifelse sign negative x

/-- String printing is selected on the unfixed IO subtype, retaining the
handle, state effects, errors, and the selected method's actual return value.
Source reference: base/complex.jl:219-220. -/
-- Source: base/complex.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, z::Complex{Bool}) =
--     print(io, z == im ? "im" : "Complex($(z.re),$(z.im))")
-- /Source
structure BoolShowOps (m : Type → Type) (IO Result : Type) where
  print : IO → String → m Result

/-- The fixed Complex{Bool} formatting is the installed complete renderer;
this caller performs the source print operation on the supplied IO handle.
Source reference: base/complex.jl:219-220. -/
-- Source: base/complex.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, z::Complex{Bool}) =
--     print(io, z == im ? "im" : "Complex($(z.re),$(z.im))")
-- /Source
def showBoolComplex {m : Type → Type} {IO Result : Type}
    (ops : BoolShowOps m IO Result) (io : IO) (z : Complex Bool) : m Result :=
  ops.print io (show_Complex_Bool z)

/-- Input and component types are not fixed by read(s, Complex{T}).  Each
read receives the same mutable stream handle and the record is specialized to
the original target T.  Its returned values may have arbitrary runtime types.
Source reference: base/complex.jl:232-236. -/
-- Source: base/complex.jl:232-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function read(s::IO, ::Type{Complex{T}}) where T<:Real
--     r = read(s,T)
--     i = read(s,T)
--     Complex{T}(r,i)
-- end
-- /Source
structure ReadComplexOps (m : Type → Type) (IO Value Result : Type) where
  read : IO → m Value
  construct : Value → Value → m Result

/-- Two ordered reads followed by the selected typed constructor.  The
monad can retain the first read's stream mutation when the second read fails.
Source reference: base/complex.jl:232-236. -/
-- Source: base/complex.jl:232-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function read(s::IO, ::Type{Complex{T}}) where T<:Real
--     r = read(s,T)
--     i = read(s,T)
--     Complex{T}(r,i)
-- end
-- /Source
def readComplex {m : Type → Type} [Monad m] {IO Value Result : Type}
    (ops : ReadComplexOps m IO Value Result) (io : IO) : m Result := do
  let r ← ops.read io
  let i ← ops.read io
  ops.construct r i

/-- The scalar operation and subsequent construction are selected on types
unfixed by the generic method.  B may contain values of multiple Julia types;
Result need not be Complex B.  Known native instances use installed callees.
Source reference: base/complex.jl:242,290-291,297. -/
-- Source: base/complex.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
-- /Source
structure UnaryConstructOps (m : Type → Type) (A B Result : Type) where
  scalar : A → m B
  construct : B → B → m Result

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Real then imaginary byte swapping, followed by constructor dispatch.
Source reference: base/complex.jl:242. -/
-- Source: base/complex.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
-- /Source
def byteSwapComplex {m : Type → Type} [Monad m] {A B Result : Type}
    (ops : UnaryConstructOps m A B Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.scalar real
  let imag ← parts.imag z
  let i ← ops.scalar imag
  ops.construct r i

/-- Scalar equality has no Bool return assertion; arbitrary returned types
are retained and select the subsequent & operation.  Bool/Bool is closed.
Source reference: base/complex.jl:246. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
structure EqualityOps (m : Type → Type) (A B Other : Type) where
  equal : A → B → m (PredicateValue Other)
  andOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Both component comparisons execute, even if the real comparison is false.
Source reference: base/complex.jl:246. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
def equalComplex {m : Type → Type} [Monad m] {A B Other : Type}
    (ops : EqualityOps m A B Other) (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m (PredicateValue Other) := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.equal zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.equal zi wi
  match r, i with
  | .boolean a, .boolean b => pure (.boolean (a && b))
  | _, _ => ops.andOther r i

/-- The condition is checked as Bool, but the final equality result is not
asserted as Bool by &&.  Its operands are real(z), x, in that order.
Source reference: base/complex.jl:248. -/
-- Source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Real, z::Complex) = isreal(z) && real(z) == x
-- /Source
structure RealEqualityOps (m : Type → Type) (R A NotBool Other : Type) where
  isreal : IsRealDispatch m A (Checked Bool NotBool)
  equal : A → R → m (PredicateValue Other)

/-- Keep the actual short circuit and reversed scalar equality argument order.
Source reference: base/complex.jl:248. -/
-- Source: base/complex.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Real, z::Complex) = isreal(z) && real(z) == x
-- /Source
def equalRealComplex {m : Type → Type} [Monad m] {E R A NotBool Other : Type}
    [MonadExceptOf (Error E) m] (ops : RealEqualityOps m R A NotBool Other)
    (x : R) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let condition ← isRealComplex ops.isreal z parts
  if (← assertChecked (E := E) "&& condition" condition) then
    let real ← parts.real z
    ops.equal real x
  else pure (.boolean false)

/-- Type-changing zero and both explicitly Bool-asserted isequal calls.
Source reference: base/complex.jl:252. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
structure RealIsequalOps (m : Type → Type) (R A Zero NotBool1 NotBool2 : Type) where
  first : R → A → m (Checked Bool NotBool1)
  zero : R → m Zero
  second : Zero → A → m (Checked Bool NotBool2)

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Assert the first comparison before zero(z), then evaluate and assert the
second comparison even when the first was false.  Finally apply native Bool &.
Source reference: base/complex.jl:252. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
def isequalRealComplex {m : Type → Type} [Monad m]
    {E R A Zero NotBool1 NotBool2 : Type} [MonadExceptOf (Error E) m]
    (ops : RealIsequalOps m R A Zero NotBool1 NotBool2)
    (z : R) (w : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Bool := do
  let real ← parts.real w
  let first ← ops.first z real
  let r ← assertChecked (E := E) "isequal(real)::Bool" first
  let zero ← ops.zero z
  let imag ← parts.imag w
  let second ← ops.second zero imag
  let i ← assertChecked (E := E) "isequal(imag)::Bool" second
  pure (r && i)

/-- Membership dispatch is on an arbitrary AbstractRange subtype; the range
is an object handle, not an unbounded list masquerading as a Julia range.
Source reference: base/complex.jl:254. -/
-- Source: base/complex.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- in(x::Complex, r::AbstractRange{<:Real}) = isreal(x) && real(x) in r
-- /Source
structure MembershipOps (m : Type → Type) (A Range NotBool Other : Type) where
  isreal : IsRealDispatch m A (Checked Bool NotBool)
  contains : A → Range → m (PredicateValue Other)

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 The scalar range test is skipped for a nonreal input.  An arbitrary
successful membership return is retained rather than coerced to Bool.
Source reference: base/complex.jl:254. -/
-- Source: base/complex.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- in(x::Complex, r::AbstractRange{<:Real}) = isreal(x) && real(x) in r
-- /Source
def memberComplex {m : Type → Type} [Monad m] {E A Range NotBool Other : Type}
    [MonadExceptOf (Error E) m] (ops : MembershipOps m A Range NotBool Other)
    (z : Complex A) (range : Range)
    (parts : ComponentOps m A := nativeComponents) : m (PredicateValue Other) := do
  let condition ← isRealComplex ops.isreal z parts
  if (← assertChecked (E := E) "&& condition" condition) then
    let real ← parts.real z
    ops.contains real range
  else pure (.boolean false)

/-- World-passing partial computations use the same representation as the
installed scopedvalues model: none is divergence, not a Julia default result.
Source reference: base/complex.jl:288. -/
-- Source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(z::Complex{<:Integer}) = inv(float(z))
-- /Source
abbrev PartialResult (E World A : Type) :=
  World → Option (Except (E × World) (A × World))

/-- Actual post-float dispatch classification.  A custom float may return
another Complex{<:Integer}; integerComplex means dispatch actually reselects
this fallback.  Other denotes a different selected inverse method, including a
more-specific user method on an integer complex value.
Source reference: base/complex.jl:288. -/
-- Source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(z::Complex{<:Integer}) = inv(float(z))
-- /Source
inductive IntegerFloatResult (A Other : Type) where
  | integerComplex (value : Complex A)
  | other (value : Other)

/-- Scalar-carrier A may represent every Integer runtime subtype; recursion
therefore also covers a change of integer component type after float.
Source reference: base/complex.jl:288. -/
-- Source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(z::Complex{<:Integer}) = inv(float(z))
-- /Source
structure IntegerInverseOps (E World A Other Result : Type) where
  toFloat : Complex A → PartialResult E World (IntegerFloatResult A Other)
  inverseOther : Other → PartialResult E World Result

/-- Explicit recursion, including divergent custom float cycles, rather than
a callback standing for this method.  No fuel bound or fabricated error.
Source reference: base/complex.jl:288. -/
-- Source: base/complex.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(z::Complex{<:Integer}) = inv(float(z))
-- /Source
def inverseIntegerComplex {E World A Other Result : Type}
    (ops : IntegerInverseOps E World A Other Result) (z : Complex A) :
    PartialResult E World Result := fun world =>
  match ops.toFloat z world with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (.integerComplex next, nextWorld)) =>
      inverseIntegerComplex ops next nextWorld
  | some (.ok (.other value, nextWorld)) => ops.inverseOther value nextWorld
partial_fixpoint

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Unary plus evaluates both scalar calls before constructor dispatch.
Source reference: base/complex.jl:290. -/
-- Source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex) = Complex(+real(z), +imag(z))
-- /Source
def positiveComplex {m : Type → Type} [Monad m] {A B Result : Type}
    (ops : UnaryConstructOps m A B Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.scalar real
  let imag ← parts.imag z
  let i ← ops.scalar imag
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Unary minus permits Bool-to-Int and arbitrary other result-type changes.
Source reference: base/complex.jl:291. -/
-- Source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex) = Complex(-real(z), -imag(z))
-- /Source
def negativeComplex {m : Type → Type} [Monad m] {A B Result : Type}
    (ops : UnaryConstructOps m A B Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.scalar real
  let imag ← parts.imag z
  let i ← ops.scalar imag
  ops.construct r i

/-- Binary scalar arithmetic and the later constructor are independently
selected on the unfixed input and result types.
Source reference: base/complex.jl:292-293,298-299. -/
-- Source: base/complex.jl:292-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
structure BinaryConstructOps (m : Type → Type) (A B Scalar Result : Type) where
  scalar : A → B → m Scalar
  construct : Scalar → Scalar → m Result

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Real sum, then imaginary sum, then construction.
Source reference: base/complex.jl:292. -/
-- Source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- /Source
def addComplex {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    (ops : BinaryConstructOps m A B Scalar Result) (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.scalar zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.scalar zi wi
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Real difference, then imaginary difference, then construction.
Source reference: base/complex.jl:293. -/
-- Source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
def subtractComplex {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    (ops : BinaryConstructOps m A B Scalar Result) (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.scalar zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.scalar zi wi
  ops.construct r i

/-- Product/subtraction/addition results may have different runtime types;
the constructor remains selected on those results rather than silently storing
them in a fixed same-type Complex.
Source reference: base/complex.jl:294-295,300-301. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
structure MultiplyConstructOps (m : Type → Type) (A B Product R I Result : Type) where
  multiply : A → B → m Product
  subtract : Product → Product → m R
  add : Product → Product → m I
  construct : R → I → m Result

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Preserve all four scalar products and the interleaved subtraction before
the cross products, exactly as the eager source expressions are evaluated.
Source reference: base/complex.jl:294-295. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
def multiplyComplex {m : Type → Type} [Monad m] {A B Product R I Result : Type}
    (ops : MultiplyConstructOps m A B Product R I Result)
    (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr₁ ← partsA.real z
  let wr₁ ← partsB.real w
  let rr ← ops.multiply zr₁ wr₁
  let zi₁ ← partsA.imag z
  let wi₁ ← partsB.imag w
  let ii ← ops.multiply zi₁ wi₁
  let r ← ops.subtract rr ii
  let zr₂ ← partsA.real z
  let wi₂ ← partsB.imag w
  let ri ← ops.multiply zr₂ wi₂
  let zi₂ ← partsA.imag z
  let wr₂ ← partsB.real w
  let ir ← ops.multiply zi₂ wr₂
  let i ← ops.add ri ir
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Wrapping unary negation dispatch, without assuming a native scalar type.
Source reference: base/complex.jl:297. -/
-- Source: base/complex.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex) = Complex(-%(real(z)), -%(imag(z)))
-- /Source
def negativeWrapComplex {m : Type → Type} [Monad m] {A B Result : Type}
    (ops : UnaryConstructOps m A B Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.scalar real
  let imag ← parts.imag z
  let i ← ops.scalar imag
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Wrapping addition retains the source calls and constructor selection.
Source reference: base/complex.jl:298. -/
-- Source: base/complex.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +%(z::Complex, w::Complex) = Complex(real(z) +% real(w), imag(z) +% imag(w))
-- /Source
def addWrapComplex {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    (ops : BinaryConstructOps m A B Scalar Result) (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.scalar zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.scalar zi wi
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Wrapping subtraction retains both ordered scalar operations.
Source reference: base/complex.jl:299. -/
-- Source: base/complex.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex, w::Complex) = Complex(real(z) -% real(w), imag(z) -% imag(w))
-- /Source
def subtractWrapComplex {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    (ops : BinaryConstructOps m A B Scalar Result) (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.scalar zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.scalar zi wi
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Wrapping complex multiplication, with the same eager sequencing as *.
Source reference: base/complex.jl:300-301. -/
-- Source: base/complex.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *%(z::Complex, w::Complex) = Complex(real(z) *% real(w) -% imag(z) *% imag(w),
--                                      real(z) *% imag(w) +% imag(z) *% real(w))
-- /Source
def multiplyWrapComplex {m : Type → Type} [Monad m] {A B Product R I Result : Type}
    (ops : MultiplyConstructOps m A B Product R I Result)
    (z : Complex A) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr₁ ← partsA.real z
  let wr₁ ← partsB.real w
  let rr ← ops.multiply zr₁ wr₁
  let zi₁ ← partsA.imag z
  let wi₁ ← partsB.imag w
  let ii ← ops.multiply zi₁ wi₁
  let r ← ops.subtract rr ii
  let zr₂ ← partsA.real z
  let wi₂ ← partsB.imag w
  let ri ← ops.multiply zr₂ wi₂
  let zi₂ ← partsA.imag z
  let wr₂ ← partsB.real w
  let ir ← ops.multiply zi₂ wr₂
  let i ← ops.add ri ir
  ops.construct r i

/-- Internal same-input-type _mulsub has a potentially different negation
result type, e.g. Bool negation to Int.  muladd is then selected on that type.
Source reference: base/complex.jl:304. -/
-- Source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mulsub(a::T, b::T, c::T) where {T<:Real} = muladd(a, b, -c)
-- /Source
structure MulsubOps (m : Type → Type) (A Negative Result : Type) where
  negate : A → m Negative
  muladd : A → A → Negative → m Result

/-- Internal helper body, with no invented algebraic contract for arbitrary
selected scalar methods.  Its registered property records call/effect safety.
Source reference: base/complex.jl:304. -/
-- Source: base/complex.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _mulsub(a::T, b::T, c::T) where {T<:Real} = muladd(a, b, -c)
-- /Source
def mulsubSameType {m : Type → Type} [Monad m] {A Negative Result : Type}
    (ops : MulsubOps m A Negative Result) (a b c : A) : m Result := do
  let negative ← ops.negate c
  ops.muladd a b negative

/-- The stream and both coordinate queries retain their selected methods.
Source reference: base/complex.jl:237-239. -/
-- Source: base/complex.jl:237-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function write(s::IO, z::Complex)
--     write(s,real(z),imag(z))
-- end
-- /Source
structure WriteComplexOps (m : Type → Type) (IO A Result : Type) where
  write : IO → A → A → m Result

/-- Query real, query imag, then call the selected multi-value writer on the
original stream.  Getter mutations and exceptions precede the write.
Source reference: base/complex.jl:237-239. -/
-- Source: base/complex.jl:237-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function write(s::IO, z::Complex)
--     write(s,real(z),imag(z))
-- end
-- /Source
def writeComplex {m : Type → Type} [Monad m] {IO A Result : Type}
    (ops : WriteComplexOps m IO A Result) (io : IO) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let r ← parts.real z
  let i ← parts.imag z
  ops.write io r i

/-- Products and addition retain arbitrary scalar dispatch and result types.
Source reference: base/complex.jl:282. -/
-- Source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
-- /Source
structure SquaredNormOps (m : Type → Type) (A Product Result : Type) where
  multiply : A → A → m Product
  add : Product → Product → m Result

/-- The source calls each getter twice.  A selected getter can mutate or
return a different value on each call, so no query is cached.
Source reference: base/complex.jl:282. -/
-- Source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
-- /Source
def squaredNormComplex {m : Type → Type} [Monad m] {A Product Result : Type}
    (ops : SquaredNormOps m A Product Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let r₁ ← parts.real z
  let r₂ ← parts.real z
  let rr ← ops.multiply r₁ r₂
  let i₁ ← parts.imag z
  let i₂ ← parts.imag z
  let ii ← ops.multiply i₁ i₂
  ops.add rr ii

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Actual selected-method metadata at a unary scalar call.  `same` decodes the
argument when dispatch reselects this exact Complex method; `none` means a distinct
selected target.  `embed` is the identity representation injection of a returned
Julia value into the scalar-result carrier, never a dispatched Julia operation.
Source reference: base/complex.jl:242,290-291,297,1130,1164. -/
-- Source: base/complex.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
-- /Source
structure UnaryRecursiveDispatch (A Scalar Result : Type) where
  same : A → Option (Complex A)
  embed : Result → Scalar

/-- Shared explicit recursion for the source's two scalar calls followed by
construction.  It is used only by the listed identical source body shapes.
Selected coordinate getters may return Complex values and thereby reselect the
same method.  Neither those recursive calls nor their divergence are delegated.
Source reference: base/complex.jl:242,290-291,297,1130,1164. -/
-- Source: base/complex.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
-- /Source
def unaryComplexRecursive {m : Type → Type} [Monad m] {A Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A Scalar Result)
    (dispatch : UnaryRecursiveDispatch A Scalar Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result := do
  let real ← parts.real z
  let r : Scalar ← match dispatch.same real with
    | some next => do
        let result ← unaryComplexRecursive ops dispatch next parts
        pure (dispatch.embed result)
    | none => ops.scalar real
  let imag ← parts.imag z
  let i : Scalar ← match dispatch.same imag with
    | some next => do
        let result ← unaryComplexRecursive ops dispatch next parts
        pure (dispatch.embed result)
    | none => ops.scalar imag
  ops.construct r i
partial_fixpoint

/-- Full bswap body, including redispatch to itself through selected getters.
Source reference: base/complex.jl:242. -/
-- Source: base/complex.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- bswap(z::Complex) = Complex(bswap(real(z)), bswap(imag(z)))
-- /Source
def byteSwapComplexFull {m : Type → Type} [Monad m] {A Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A Scalar Result) (dispatch : UnaryRecursiveDispatch A Scalar Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive ops dispatch z parts

/-- Full unary plus retains recursive scalar dispatch and exact evaluation order.
Source reference: base/complex.jl:290. -/
-- Source: base/complex.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex) = Complex(+real(z), +imag(z))
-- /Source
def positiveComplexFull {m : Type → Type} [Monad m] {A Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A Scalar Result) (dispatch : UnaryRecursiveDispatch A Scalar Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive ops dispatch z parts

/-- Full unary minus retains recursive scalar dispatch and result representation.
Source reference: base/complex.jl:291. -/
-- Source: base/complex.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex) = Complex(-real(z), -imag(z))
-- /Source
def negativeComplexFull {m : Type → Type} [Monad m] {A Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A Scalar Result) (dispatch : UnaryRecursiveDispatch A Scalar Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive ops dispatch z parts

/-- Full wrapping unary negation includes selected recursive Complex arguments.
Source reference: base/complex.jl:297. -/
-- Source: base/complex.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex) = Complex(-%(real(z)), -%(imag(z)))
-- /Source
def negativeWrapComplexFull {m : Type → Type} [Monad m] {A Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A Scalar Result) (dispatch : UnaryRecursiveDispatch A Scalar Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive ops dispatch z parts

/-- Actual redispatch to a two-Complex source method, with exact decoded
operands.  Other selected calls retain their own effects in ops.scalar.
The result embedding preserves Julia object/value identity across carriers.
Source reference: base/complex.jl:292-293,298-299. -/
-- Source: base/complex.jl:292-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
structure BinaryRecursiveDispatch (A B Scalar Result : Type) where
  same : A → B → Option (Complex A × Complex B)
  embed : Result → Scalar

/-- The recursive body common to ordinary/wrapping addition and subtraction.
Every scalar site either executes this body on the decoded operands or invokes
a distinct selected method; repeated getter calls are never cached.
Source reference: base/complex.jl:292-293,298-299. -/
-- Source: base/complex.jl:292-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
def binaryComplexRecursive {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : BinaryConstructOps m A B Scalar Result)
    (dispatch : BinaryRecursiveDispatch A B Scalar Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r : Scalar ← match dispatch.same zr wr with
    | some (a, b) => do
        let result ← binaryComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.scalar zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i : Scalar ← match dispatch.same zi wi with
    | some (a, b) => do
        let result ← binaryComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.scalar zi wi
  ops.construct r i
partial_fixpoint

/-- Full source arithmetic body, including redispatch of scalar sites to
this same Complex method.  The supplied scalar operation is a distinct target.
Source reference: base/complex.jl:292. -/
-- Source: base/complex.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, w::Complex) = Complex(real(z) + real(w), imag(z) + imag(w))
-- /Source
def addComplexFull {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : BinaryConstructOps m A B Scalar Result)
    (dispatch : BinaryRecursiveDispatch A B Scalar Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := binaryComplexRecursive ops dispatch z w partsA partsB

/-- Full source arithmetic body, including redispatch of scalar sites to
this same Complex method.  The supplied scalar operation is a distinct target.
Source reference: base/complex.jl:293. -/
-- Source: base/complex.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, w::Complex) = Complex(real(z) - real(w), imag(z) - imag(w))
-- /Source
def subtractComplexFull {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : BinaryConstructOps m A B Scalar Result)
    (dispatch : BinaryRecursiveDispatch A B Scalar Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := binaryComplexRecursive ops dispatch z w partsA partsB

/-- Full source arithmetic body, including redispatch of scalar sites to
this same Complex method.  The supplied scalar operation is a distinct target.
Source reference: base/complex.jl:298. -/
-- Source: base/complex.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +%(z::Complex, w::Complex) = Complex(real(z) +% real(w), imag(z) +% imag(w))
-- /Source
def addWrapComplexFull {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : BinaryConstructOps m A B Scalar Result)
    (dispatch : BinaryRecursiveDispatch A B Scalar Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := binaryComplexRecursive ops dispatch z w partsA partsB

/-- Full source arithmetic body, including redispatch of scalar sites to
this same Complex method.  The supplied scalar operation is a distinct target.
Source reference: base/complex.jl:299. -/
-- Source: base/complex.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(z::Complex, w::Complex) = Complex(real(z) -% real(w), imag(z) -% imag(w))
-- /Source
def subtractWrapComplexFull {m : Type → Type} [Monad m] {A B Scalar Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : BinaryConstructOps m A B Scalar Result)
    (dispatch : BinaryRecursiveDispatch A B Scalar Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := binaryComplexRecursive ops dispatch z w partsA partsB

/-- Redispatch classification for each product.  The decoded operands are
exactly the values supplied to this same source multiplication method; `embed`
is only their returned value's carrier injection.
Source reference: base/complex.jl:294-295,300-301. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
structure MultiplyRecursiveDispatch (A B Product Result : Type) where
  same : A → B → Option (Complex A × Complex B)
  embed : Result → Product

/-- Explicit four-site recursive multiplication.  The real subtraction
precedes every cross-product query; all eight selected component queries remain
separate, and every recursive result flows to the original scalar result slot.
Source reference: base/complex.jl:294-295,300-301. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
def multiplyComplexRecursive {m : Type → Type} [Monad m] {A B Product R I Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : MultiplyConstructOps m A B Product R I Result)
    (dispatch : MultiplyRecursiveDispatch A B Product Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := do
  let zr₁ ← partsA.real z
  let wr₁ ← partsB.real w
  let rr : Product ← match dispatch.same zr₁ wr₁ with
    | some (a, b) => do
        let result ← multiplyComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.multiply zr₁ wr₁
  let zi₁ ← partsA.imag z
  let wi₁ ← partsB.imag w
  let ii : Product ← match dispatch.same zi₁ wi₁ with
    | some (a, b) => do
        let result ← multiplyComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.multiply zi₁ wi₁
  let r ← ops.subtract rr ii
  let zr₂ ← partsA.real z
  let wi₂ ← partsB.imag w
  let ri : Product ← match dispatch.same zr₂ wi₂ with
    | some (a, b) => do
        let result ← multiplyComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.multiply zr₂ wi₂
  let zi₂ ← partsA.imag z
  let wr₂ ← partsB.real w
  let ir : Product ← match dispatch.same zi₂ wr₂ with
    | some (a, b) => do
        let result ← multiplyComplexRecursive ops dispatch a b partsA partsB
        pure (dispatch.embed result)
    | none => ops.multiply zi₂ wr₂
  let i ← ops.add ri ir
  ops.construct r i
partial_fixpoint

/-- Full multiplication source body with explicit recursive scalar redispatch.
Source reference: base/complex.jl:294-295. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
def multiplyComplexFull {m : Type → Type} [Monad m] {A B Product R I Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : MultiplyConstructOps m A B Product R I Result)
    (dispatch : MultiplyRecursiveDispatch A B Product Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := multiplyComplexRecursive ops dispatch z w partsA partsB

/-- Full multiplication source body with explicit recursive scalar redispatch.
Source reference: base/complex.jl:300-301. -/
-- Source: base/complex.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *%(z::Complex, w::Complex) = Complex(real(z) *% real(w) -% imag(z) *% imag(w),
--                                      real(z) *% imag(w) +% imag(z) *% real(w))
-- /Source
def multiplyWrapComplexFull {m : Type → Type} [Monad m] {A B Product R I Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : MultiplyConstructOps m A B Product R I Result)
    (dispatch : MultiplyRecursiveDispatch A B Product Result)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m Result := multiplyComplexRecursive ops dispatch z w partsA partsB

/-- Actual selection of this exact two-Complex equality method at a scalar
comparison.  Nonmatching selections remain in the open scalar equality callee.
Source reference: base/complex.jl:246. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
structure EqualityRecursiveDispatch (A B : Type) where
  same : A → B → Option (Complex A × Complex B)

/-- Full equality preserves eager comparisons, Bool conjunction, arbitrary
other & dispatch, and recursion when selected getters return Complex operands.
Source reference: base/complex.jl:246. -/
-- Source: base/complex.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex, w::Complex) = (real(z) == real(w)) & (imag(z) == imag(w))
-- /Source
def equalComplexFull {m : Type → Type} [Monad m] {A B Other : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : EqualityOps m A B Other) (dispatch : EqualityRecursiveDispatch A B)
    (z : Complex A) (w : Complex B) (partsA : ComponentOps m A) (partsB : ComponentOps m B) :
    m (PredicateValue Other) := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← match dispatch.same zr wr with
    | some (a, b) => equalComplexFull ops dispatch a b partsA partsB
    | none => ops.equal zr wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← match dispatch.same zi wi with
    | some (a, b) => equalComplexFull ops dispatch a b partsA partsB
    | none => ops.equal zi wi
  match r, i with
  | .boolean a, .boolean b => pure (.boolean (a && b))
  | _, _ => ops.andOther r i
partial_fixpoint

/-- Exact decoded Real/Complex arguments if either scalar comparison selects
this same source method.  A is a runtime universe, so nested complex components
and zero results may change Julia types while preserving their representations.
Source reference: base/complex.jl:252. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
structure IsequalRecursiveDispatch (R A Zero : Type) where
  first : R → A → Option (R × Complex A)
  second : Zero → A → Option (R × Complex A)

/-- Full real-complex isequal implements both possible recursive call sites.
A recursive result is a native Bool because this very source body asserts both
comparisons.  Distinct selected comparisons may still return non-Bools and fail
at the original assertions.  Getter and zero evaluation order is unchanged.
Source reference: base/complex.jl:252. -/
-- Source: base/complex.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isequal(z::Real, w::Complex) = isequal(z,real(w))::Bool & isequal(zero(z),imag(w))::Bool
-- /Source
def isequalRealComplexFull {m : Type → Type} [Monad m]
    {E R A Zero NotBool1 NotBool2 : Type} [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : RealIsequalOps m R A Zero NotBool1 NotBool2)
    (dispatch : IsequalRecursiveDispatch R A Zero)
    (z : R) (w : Complex A) (parts : ComponentOps m A) : m Bool := do
  let real ← parts.real w
  let first : Checked Bool NotBool1 ← match dispatch.first z real with
    | some (a, b) => do
        let result ← isequalRealComplexFull (E := E) ops dispatch a b parts
        pure (.accepted result)
    | none => ops.first z real
  let r ← assertChecked (E := E) "isequal(real)::Bool" first
  let zero ← ops.zero z
  let imag ← parts.imag w
  let second : Checked Bool NotBool2 ← match dispatch.second zero imag with
    | some (a, b) => do
        let result ← isequalRealComplexFull (E := E) ops dispatch a b parts
        pure (.accepted result)
    | none => ops.second zero imag
  let i ← assertChecked (E := E) "isequal(imag)::Bool" second
  pure (r && i)
partial_fixpoint

/-- isreal is a distinct selected callee at every recursive depth; the runtime
may select its inherited body or a more-specific method for the current decoded
component type.  The contains operation excludes this exact fallback when same
selects recursion.  Range handles and their identity are preserved.
Source reference: base/complex.jl:254. -/
-- Source: base/complex.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- in(x::Complex, r::AbstractRange{<:Real}) = isreal(x) && real(x) in r
-- /Source
structure MembershipRecursiveOps (m : Type → Type) (A Range NotBool Other : Type) where
  isreal : Complex A → m (Checked Bool NotBool)
  contains : A → Range → m (PredicateValue Other)
  same : A → Range → Option (Complex A)

/-- Full membership preserves its short circuit and native Bool assertion,
and recursively executes this body when real(x) selects complex membership
again.  The original range handle is retained at every depth.
Source reference: base/complex.jl:254. -/
-- Source: base/complex.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- in(x::Complex, r::AbstractRange{<:Real}) = isreal(x) && real(x) in r
-- /Source
def memberComplexFull {m : Type → Type} [Monad m] {E A Range NotBool Other : Type}
    [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : MembershipRecursiveOps m A Range NotBool Other)
    (z : Complex A) (range : Range) (parts : ComponentOps m A) : m (PredicateValue Other) := do
  let condition ← ops.isreal z
  if (← assertChecked (E := E) "&& condition" condition) then
    let real ← parts.real z
    match ops.same real range with
    | some next => memberComplexFull (E := E) ops next range parts
    | none => ops.contains real range
  else pure (.boolean false)
partial_fixpoint

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Fixed parser precedence of the concrete Symbol `:+`.  The pinned
operator_precedence documentation at base/show.jl:1706-1707 gives 11; its
implementation at 1713 returns the parser's Cint as native Int.  On the packet's
64-bit platform this closed result is exactly Int64(11), with no user dispatch
or arbitrary precedence parameter.  The helper models only this fixed call,
not the general parser table.
Source reference: base/show.jl:1694-1713. -/
-- Source: base/show.jl:1694-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     operator_precedence(s::Symbol)
-- 
-- Return an integer representing the precedence of a binary operator `s`, relative to
-- other operators. Higher-numbered operators take precedence over lower-numbered
-- operators. Return `0` if `s` is not a valid binary operator.
-- 
-- (The precedence of *unary* operators is handled differently, including cases like `+`
-- where an operator can be either unary or binary.)
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.operator_precedence(:+), Base.operator_precedence(:*), Base.operator_precedence(:.)
-- (11, 12, 17)
-- 
-- julia> Base.operator_precedence(:sin), Base.operator_precedence(:+=), Base.operator_precedence(:(=))  # (Note the necessary parens on `:(=)`)
-- (0, 1, 1)
-- ```
-- """
-- operator_precedence(s::Symbol) = Int(ccall(:jl_operator_precedence, Cint, (Cstring,), s))
-- /Source
def plusOperatorPrecedence : JInt .i64 := JInt.lit .i64 11

/-- Return-type injection records whether the source returned the last print
result or the show result.  The wrappers preserve the actual returned values,
including arbitrary user-defined return types; they do not allocate Julia
objects or force either branch to return nothing.
Source reference: base/complex.jl:222-230. -/
-- Source: base/complex.jl:222-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show_unquoted(io::IO, z::Complex, ::Int, prec::Int)
--     if operator_precedence(:+) <= prec
--         print(io, "(")
--         show(io, z)
--         print(io, ")")
--     else
--         show(io, z)
--     end
-- end
-- /Source
inductive ShowUnquotedResult (Printed Shown : Type) where
  | printed (value : Printed)
  | shown (value : Shown)

/-- The IO subtype and complex component type remain unfixed, so print and
show are selected operations that may mutate state, throw, or change return
type.  show is the separate source callee, not this show_unquoted method.
Source reference: base/complex.jl:222-230. -/
-- Source: base/complex.jl:222-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show_unquoted(io::IO, z::Complex, ::Int, prec::Int)
--     if operator_precedence(:+) <= prec
--         print(io, "(")
--         show(io, z)
--         print(io, ")")
--     else
--         show(io, z)
--     end
-- end
-- /Source
structure ShowUnquotedOps (m : Type → Type) (IO A Printed Shown : Type) where
  print : IO → String → m Printed
  showValue : IO → Complex A → m Shown

/-- Use the fixed native precedence and installed JInt comparison.  The high
precedence branch prints an opening parenthesis, shows the original value,
and prints a closing parenthesis in that order.  Each call's exception and
state effects are retained.  The unnamed Int argument is ignored by the source.
Source reference: base/complex.jl:222-230. -/
-- Source: base/complex.jl:222-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show_unquoted(io::IO, z::Complex, ::Int, prec::Int)
--     if operator_precedence(:+) <= prec
--         print(io, "(")
--         show(io, z)
--         print(io, ")")
--     else
--         show(io, z)
--     end
-- end
-- /Source
def showUnquotedComplex {m : Type → Type} [Monad m]
    {IO A Printed Shown : Type} (ops : ShowUnquotedOps m IO A Printed Shown)
    (io : IO) (z : Complex A) (_indent prec : JInt .i64) :
    m (ShowUnquotedResult Printed Shown) := do
  if plusOperatorPrecedence ≤ prec then
    let _ ← ops.print io "("
    let _ ← ops.showValue io z
    return .printed (← ops.print io ")")
  else
    return .shown (← ops.showValue io z)

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- A scalar/real-coordinate operation followed by construction with the
actual imaginary-query result.  No commutativity or promotion law is assumed.  Generic callers retain
each component query at its literal source position.
Source reference: base/complex.jl:318,325,337-338. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
structure ScalarLeftOps (m : Type → Type) (Scalar A R Result : Type) where
  operation : Scalar → A → m R
  construct : R → A → m Result

/-- The ordered real-coordinate/scalar counterpart.
Source reference: base/complex.jl:319,321,326,332,344. -/
-- Source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
-- /Source
structure ScalarRightOps (m : Type → Type) (A Scalar R Result : Type) where
  operation : A → Scalar → m R
  construct : R → A → m Result

/-- Both coordinate calls put the scalar on the left.
Source reference: base/complex.jl:333,345-346. -/
-- Source: base/complex.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex{Bool}) = Complex(x * real(z), x * imag(z))
-- /Source
structure ScaleLeftOps (m : Type → Type) (Scalar A Product Result : Type) where
  operation : Scalar → A → m Product
  construct : Product → Product → m Result

/-- Both coordinate calls put the scalar on the right.  This is also the
operation shape of complex/scalar division.
Source reference: base/complex.jl:323,334,358. -/
-- Source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
-- /Source
structure ScaleRightOps (m : Type → Type) (A Scalar Product Result : Type) where
  operation : A → Scalar → m Product
  construct : Product → Product → m Result

/-- Bool minus a complex uses scalar subtraction followed by scalar negation.
Source reference: base/complex.jl:320. -/
-- Source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
-- /Source
structure BoolSubtractOps (m : Type → Type) (A R I Result : Type) where
  subtract : Bool → A → m R
  negate : A → m I
  construct : R → I → m Result

/-- Internal finite composition used by `subtractBoolComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Preserve the real subtraction before imaginary negation.
Source reference: base/complex.jl:320. -/
-- Source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
-- /Source
def subtractBoolComplex {m : Type → Type} [Monad m] {A R I Result : Type}
    (ops : BoolSubtractOps m A R I Result) (x : Bool) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.subtract x real
  let imag ← parts.imag z
  let i ← ops.negate imag
  ops.construct r i


/-- oftype is itself selected on the unfixed difference/coordinate types.
Its selected fallback must implement base/essentials.jl:718, including isa
bypass and ::typeof(x), when instantiated concretely.  No such correctness
law is an input to this caller model.
Source reference: base/complex.jl:327-331,339-343. -/
-- Source: base/complex.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex{Bool})
--     # we don't want the default type for -(Bool)
--     re = x-real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
structure RealSubtractOps (m : Type → Type)
    (Scalar A Difference Converted Negative Result : Type) where
  subtract : Scalar → A → m Difference
  oftype : Difference → A → m Converted
  negate : Converted → m Negative
  construct : Difference → Negative → m Result

/-- Compute the real difference, convert the Bool imaginary coordinate using
that actual result, negate the converted value, then construct.
Source reference: base/complex.jl:327-331. -/
-- Source: base/complex.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex{Bool})
--     # we don't want the default type for -(Bool)
--     re = x-real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
def subtractRealComplexBool {m : Type → Type} [Monad m]
    {Scalar Difference Converted Negative Result : Type}
    (ops : RealSubtractOps m Scalar Bool Difference Converted Negative Result)
    (x : Scalar) (z : Complex Bool) : m Result := do
  let r ← ops.subtract x (real_Complex z)
  let converted ← ops.oftype r (imag_Complex z)
  let i ← ops.negate converted
  ops.construct r i

/-- Internal finite composition used by `subtractRealComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
The same source algorithm over an arbitrary Real component type.
Source reference: base/complex.jl:339-343. -/
-- Source: base/complex.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex)
--     # we don't want the default type for -(Bool)
--     re = x - real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
def subtractRealComplex {m : Type → Type} [Monad m]
    {Scalar A Difference Converted Negative Result : Type}
    (ops : RealSubtractOps m Scalar A Difference Converted Negative Result)
    (x : Scalar) (z : Complex A) (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.subtract x real
  let imag ← parts.imag z
  let converted ← ops.oftype r imag
  let i ← ops.negate converted
  ops.construct r i


/-- Scalar muladd and product may return different types; construction is
selected only after both eager arguments have been evaluated.
Source reference: base/complex.jl:349. -/
-- Source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, y::Real) = Complex(muladd(real(z),x,y), imag(z)*x)
-- /Source
structure MuladdComplexRealRealOps (m : Type → Type)
    (A X Y R I Result : Type) where
  muladd : A → X → Y → m R
  multiply : A → X → m I
  construct : R → I → m Result

/-- Internal finite composition used by `muladdComplexRealRealRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Real muladd precedes the imaginary-coordinate product.
Source reference: base/complex.jl:349. -/
-- Source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, y::Real) = Complex(muladd(real(z),x,y), imag(z)*x)
-- /Source
def muladdComplexRealReal {m : Type → Type} [Monad m] {A X Y R I Result : Type}
    (ops : MuladdComplexRealRealOps m A X Y R I Result)
    (z : Complex A) (x : X) (y : Y)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.muladd real x y
  let imag ← parts.imag z
  let i ← ops.multiply imag x
  ops.construct r i


/-- Component muladd operations with an unfixed common middle argument.
Source reference: base/complex.jl:350-351. -/
-- Source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, w::Complex) =
--     Complex(muladd(real(z),x,real(w)), muladd(imag(z),x,imag(w)))
-- /Source
structure MuladdComplexRealComplexOps (m : Type → Type)
    (A X B Part Result : Type) where
  muladd : A → X → B → m Part
  construct : Part → Part → m Result

/-- Internal finite composition used by `muladdComplexRealComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Preserve the two separate component muladd calls and their order.
Source reference: base/complex.jl:350-351. -/
-- Source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, w::Complex) =
--     Complex(muladd(real(z),x,real(w)), muladd(imag(z),x,imag(w)))
-- /Source
def muladdComplexRealComplex {m : Type → Type} [Monad m] {A X B Part Result : Type}
    (ops : MuladdComplexRealComplexOps m A X B Part Result)
    (z : Complex A) (x : X) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr ← partsA.real z
  let wr ← partsB.real w
  let r ← ops.muladd zr x wr
  let zi ← partsA.imag z
  let wi ← partsB.imag w
  let i ← ops.muladd zi x wi
  ops.construct r i


/-- The imaginary coordinate is forwarded unchanged after the scalar muladd.
Source reference: base/complex.jl:352. -/
-- Source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::Real, y::Real, z::Complex) = Complex(muladd(x,y,real(z)), imag(z))
-- /Source
structure MuladdRealRealComplexOps (m : Type → Type)
    (X Y A R Result : Type) where
  muladd : X → Y → A → m R
  construct : R → A → m Result

/-- Internal finite composition used by `muladdRealRealComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Compute the real muladd, then query and forward the actual imaginary result.
Source reference: base/complex.jl:352. -/
-- Source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::Real, y::Real, z::Complex) = Complex(muladd(x,y,real(z)), imag(z))
-- /Source
def muladdRealRealComplex {m : Type → Type} [Monad m] {X Y A R Result : Type}
    (ops : MuladdRealRealComplexOps m X Y A R Result)
    (x : X) (y : Y) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.muladd x y real
  let imag ← parts.imag z
  ops.construct r imag


/-- _mulsub dispatch depends on the two unfixed component types and x.  Its
result, negation result, and product result remain distinct carriers.
Source reference: base/complex.jl:353-355. -/
-- Source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, w::Complex, x::Real) =
--     Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), x)),
--             muladd(real(z), imag(w), imag(z) * real(w)))
-- /Source
structure MuladdComplexComplexRealOps (m : Type → Type)
    (A B X Difference Negative Product R I Result : Type) where
  mulsub : A → B → X → m Difference
  negate : Difference → m Negative
  muladdReal : A → B → Negative → m R
  multiply : A → B → m Product
  muladdImag : A → B → Product → m I
  construct : R → I → m Result

/-- Internal finite composition used by `muladdComplexComplexRealRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
_mulsub and its negation are evaluated before the real muladd; only then
does the imaginary coordinate evaluate its own four component queries, product,
muladd and constructor.  All repeated component queries retain dispatch and effects.
Source reference: base/complex.jl:353-355. -/
-- Source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, w::Complex, x::Real) =
--     Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), x)),
--             muladd(real(z), imag(w), imag(z) * real(w)))
-- /Source
def muladdComplexComplexReal {m : Type → Type} [Monad m]
    {A B X Difference Negative Product R I Result : Type}
    (ops : MuladdComplexComplexRealOps m A B X Difference Negative Product R I Result)
    (z : Complex A) (w : Complex B) (x : X)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result := do
  let zr₁ ← partsA.real z
  let wr₁ ← partsB.real w
  let zi₁ ← partsA.imag z
  let wi₁ ← partsB.imag w
  let difference ← ops.mulsub zi₁ wi₁ x
  let negative ← ops.negate difference
  let r ← ops.muladdReal zr₁ wr₁ negative
  let zr₂ ← partsA.real z
  let wi₂ ← partsB.imag w
  let zi₂ ← partsA.imag z
  let wr₂ ← partsB.real w
  let product ← ops.multiply zi₂ wr₂
  let i ← ops.muladdImag zr₂ wi₂ product
  ops.construct r i


/-- The source type parameters are retained explicitly, independently of
value carriers.  A returned promote_type value need not itself be a Type;
the subsequent call uses its actual selected callable dispatch.
Source reference: base/complex.jl:357. -/
-- Source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))
-- /Source
structure DivideRealComplexOps (m : Type → Type)
    (Scalar A RealType ComplexType Target Converted Inverse Result : Type) where
  promoteType : RealType → ComplexType → m Target
  construct : Target → Complex A → m Converted
  inverse : Converted → m Inverse
  multiply : Scalar → Inverse → m Result

/-- Promotion is evaluated first, then T(z), inverse, and multiplication.
Source reference: base/complex.jl:357. -/
-- Source: base/complex.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))
-- /Source
def divideRealComplex {m : Type → Type} [Monad m]
    {Scalar A RealType ComplexType Target Converted Inverse Result : Type}
    (ops : DivideRealComplexOps m Scalar A RealType ComplexType Target Converted Inverse Result)
    (rType : RealType) (sType : ComplexType) (a : Scalar) (z : Complex A) : m Result := do
  let target ← ops.promoteType rType sType
  let value ← ops.construct target z
  let inverse ← ops.inverse value
  ops.multiply a inverse

/-- Internal finite composition used by `addBoolComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:318. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addBoolComplex {m : Type → Type} [Monad m] {A R Result : Type}
    (ops : ScalarLeftOps m Bool A R Result) (x : Bool) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation x real
  let imag ← parts.imag z
  ops.construct r imag


/-- Internal finite composition used by `addComplexBoolRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:319. -/
-- Source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
-- /Source
def addComplexBool {m : Type → Type} [Monad m] {A R Result : Type}
    (ops : ScalarRightOps m A Bool R Result) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation real x
  let imag ← parts.imag z
  ops.construct r imag


/-- Internal finite composition used by `subtractComplexBoolRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:321. -/
-- Source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Bool) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexBool {m : Type → Type} [Monad m] {A R Result : Type}
    (ops : ScalarRightOps m A Bool R Result) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation real x
  let imag ← parts.imag z
  ops.construct r imag


/-- Internal finite composition used by `multiplyComplexBoolRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:323. -/
-- Source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyComplexBool {m : Type → Type} [Monad m] {A Product Result : Type}
    (ops : ScaleRightOps m A Bool Product Result) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation real x
  let imag ← parts.imag z
  let i ← ops.operation imag x
  ops.construct r i


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:325. -/
-- Source: base/complex.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Real, z::Complex{Bool}) = Complex(x + real(z), imag(z))
-- /Source
def addRealComplexBool {m : Type → Type} [Monad m] {Scalar R Result : Type}
    (ops : ScalarLeftOps m Scalar Bool R Result) (x : Scalar) (z : Complex Bool) : m Result := do
  let r ← ops.operation x (real_Complex z)
  ops.construct r (imag_Complex z)


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:326. -/
-- Source: base/complex.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex{Bool}, x::Real) = Complex(real(z) + x, imag(z))
-- /Source
def addComplexBoolReal {m : Type → Type} [Monad m] {Scalar R Result : Type}
    (ops : ScalarRightOps m Bool Scalar R Result) (z : Complex Bool) (x : Scalar) : m Result := do
  let r ← ops.operation (real_Complex z) x
  ops.construct r (imag_Complex z)


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:332. -/
-- Source: base/complex.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex{Bool}, x::Real) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexBoolReal {m : Type → Type} [Monad m] {Scalar R Result : Type}
    (ops : ScalarRightOps m Bool Scalar R Result) (z : Complex Bool) (x : Scalar) : m Result := do
  let r ← ops.operation (real_Complex z) x
  ops.construct r (imag_Complex z)


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:333. -/
-- Source: base/complex.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex{Bool}) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyRealComplexBool {m : Type → Type} [Monad m] {Scalar Product Result : Type}
    (ops : ScaleLeftOps m Scalar Bool Product Result) (x : Scalar) (z : Complex Bool) : m Result := do
  let r ← ops.operation x (real_Complex z)
  let i ← ops.operation x (imag_Complex z)
  ops.construct r i


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:334. -/
-- Source: base/complex.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex{Bool}, x::Real) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyComplexBoolReal {m : Type → Type} [Monad m] {Scalar Product Result : Type}
    (ops : ScaleRightOps m Bool Scalar Product Result) (z : Complex Bool) (x : Scalar) : m Result := do
  let r ← ops.operation (real_Complex z) x
  let i ← ops.operation (imag_Complex z) x
  ops.construct r i


/-- Internal finite composition used by `addRealComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:337. -/
-- Source: base/complex.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Real, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addRealComplex {m : Type → Type} [Monad m] {Scalar A R Result : Type}
    (ops : ScalarLeftOps m Scalar A R Result) (x : Scalar) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation x real
  let imag ← parts.imag z
  ops.construct r imag


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:338. -/
-- Source: base/complex.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Real) = Complex(x + real(z), imag(z))
-- /Source
def addComplexReal {m : Type → Type} [Monad m] {Scalar A R Result : Type}
    (ops : ScalarLeftOps m Scalar A R Result) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation x real
  let imag ← parts.imag z
  ops.construct r imag


/-- Internal finite composition used by `subtractComplexRealRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:344. -/
-- Source: base/complex.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Real) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexReal {m : Type → Type} [Monad m] {Scalar A R Result : Type}
    (ops : ScalarRightOps m A Scalar R Result) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation real x
  let imag ← parts.imag z
  ops.construct r imag


/-- Internal finite composition used by `multiplyRealComplexRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:345. -/
-- Source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyRealComplex {m : Type → Type} [Monad m] {Scalar A Product Result : Type}
    (ops : ScaleLeftOps m Scalar A Product Result) (x : Scalar) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation x real
  let imag ← parts.imag z
  let i ← ops.operation x imag
  ops.construct r i


/-- Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:346. -/
-- Source: base/complex.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Real) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyComplexReal {m : Type → Type} [Monad m] {Scalar A Product Result : Type}
    (ops : ScaleLeftOps m Scalar A Product Result) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation x real
  let imag ← parts.imag z
  let i ← ops.operation x imag
  ops.construct r i


/-- Internal finite composition used by `divideComplexRealRecursive`.
That full wrapper supplies actual inherited recursion for the operation slots.
Effectful source body with exact scalar argument order and constructor dispatch.
Source reference: base/complex.jl:358. -/
-- Source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(z::Complex, x::Real) = Complex(real(z)/x, imag(z)/x)
-- /Source
def divideComplexReal {m : Type → Type} [Monad m] {A Scalar Product Result : Type}
    (ops : ScaleRightOps m A Scalar Product Result) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.operation real x
  let imag ← parts.imag z
  let i ← ops.operation imag x
  ops.construct r i

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean
open scoped Lean.Order

/-- Actual method-table selection for a call whose argument runtime types are
unfixed.  An inherited payload decodes the actual arguments unchanged and means
this exact source method is selected again.  selectedOther excludes that exact
method, including cases where a more-specific method is selected on the same
argument types.  Classification is pure representation metadata, not a Julia
callee or a supplied implementation of recursion.
Source reference: base/complex.jl:318-358. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
inductive SelfCall (MethodArgs : Type) where
  | selectedOther
  | inherited (arguments : MethodArgs)

/-- Pure dispatch metadata plus identity-of-runtime-value representation
injection for a recursively returned result.  Result and OperationResult are
Lean carriers; neither denotes a single Julia runtime type.  embedReturn only
re-encodes the same actual returned value in the caller's carrier, with no
Julia call, allocation, error, mutation, or conversion.  A universal tagged
carrier can use the identity map.  This metadata imposes no behavioral law on
selected arithmetic callees and never supplies the recursive method body.
Source reference: base/complex.jl:318-358. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
structure SelfDispatch (CallArgs MethodArgs Result OperationResult : Type) where
  classify : CallArgs → SelfCall MethodArgs
  embedReturn : Result → OperationResult

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:318-318. -/
-- Source: base/complex.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addBoolComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A R Result : Type}
    (ops : ScalarLeftOps m Bool A R Result)
    (self : SelfDispatch (Bool × A) (Bool × Complex A) Result R) (x : Bool) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  addBoolComplex
    { ops with
      operation := fun x real =>
        match self.classify (x, real) with
        | .selectedOther => ops.operation x real
        | .inherited (nextX, nextZ) => do
            let result ← addBoolComplexRecursive ops self nextX nextZ parts
            pure (self.embedReturn result)
    }
    x z parts
partial_fixpoint monotonicity by
  unfold addBoolComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:319-319. -/
-- Source: base/complex.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(z::Complex, x::Bool) = Complex(real(z) + x, imag(z))
-- /Source
def addComplexBoolRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A R Result : Type}
    (ops : ScalarRightOps m A Bool R Result)
    (self : SelfDispatch (A × Bool) (Complex A × Bool) Result R) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  addComplexBool
    { ops with
      operation := fun real x =>
        match self.classify (real, x) with
        | .selectedOther => ops.operation real x
        | .inherited (nextZ, nextX) => do
            let result ← addComplexBoolRecursive ops self nextZ nextX parts
            pure (self.embedReturn result)
    }
    z x parts
partial_fixpoint monotonicity by
  unfold addComplexBool
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:320-320. -/
-- Source: base/complex.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Bool, z::Complex) = Complex(x - real(z), - imag(z))
-- /Source
def subtractBoolComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A R I Result : Type}
    (ops : BoolSubtractOps m A R I Result)
    (self : SelfDispatch (Bool × A) (Bool × Complex A) Result R) (x : Bool) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  subtractBoolComplex
    { ops with
      subtract := fun x real =>
        match self.classify (x, real) with
        | .selectedOther => ops.subtract x real
        | .inherited (nextX, nextZ) => do
            let result ← subtractBoolComplexRecursive ops self nextX nextZ parts
            pure (self.embedReturn result)
    }
    x z parts
partial_fixpoint monotonicity by
  unfold subtractBoolComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:321-321. -/
-- Source: base/complex.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Bool) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexBoolRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A R Result : Type}
    (ops : ScalarRightOps m A Bool R Result)
    (self : SelfDispatch (A × Bool) (Complex A × Bool) Result R) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  subtractComplexBool
    { ops with
      operation := fun real x =>
        match self.classify (real, x) with
        | .selectedOther => ops.operation real x
        | .inherited (nextZ, nextX) => do
            let result ← subtractComplexBoolRecursive ops self nextZ nextX parts
            pure (self.embedReturn result)
    }
    z x parts
partial_fixpoint monotonicity by
  unfold subtractComplexBool
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:323-323. -/
-- Source: base/complex.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, x::Bool) = Complex(real(z) * x, imag(z) * x)
-- /Source
def multiplyComplexBoolRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A Product Result : Type}
    (ops : ScaleRightOps m A Bool Product Result)
    (self : SelfDispatch (A × Bool) (Complex A × Bool) Result Product) (z : Complex A) (x : Bool)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  multiplyComplexBool
    { ops with
      operation := fun part x =>
        match self.classify (part, x) with
        | .selectedOther => ops.operation part x
        | .inherited (nextZ, nextX) => do
            let result ← multiplyComplexBoolRecursive ops self nextZ nextX parts
            pure (self.embedReturn result)
    }
    z x parts
partial_fixpoint monotonicity by
  unfold multiplyComplexBool
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:337-337. -/
-- Source: base/complex.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Real, z::Complex) = Complex(x + real(z), imag(z))
-- /Source
def addRealComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {Scalar A R Result : Type}
    (ops : ScalarLeftOps m Scalar A R Result)
    (self : SelfDispatch (Scalar × A) (Scalar × Complex A) Result R) (x : Scalar) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  addRealComplex
    { ops with
      operation := fun x real =>
        match self.classify (x, real) with
        | .selectedOther => ops.operation x real
        | .inherited (nextX, nextZ) => do
            let result ← addRealComplexRecursive ops self nextX nextZ parts
            pure (self.embedReturn result)
    }
    x z parts
partial_fixpoint monotonicity by
  unfold addRealComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:339-343. -/
-- Source: base/complex.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Real, z::Complex)
--     # we don't want the default type for -(Bool)
--     re = x - real(z)
--     Complex(re, - oftype(re, imag(z)))
-- end
-- /Source
def subtractRealComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    {Scalar A Difference Converted Negative Result : Type}
    (ops : RealSubtractOps m Scalar A Difference Converted Negative Result)
    (self : SelfDispatch (Scalar × A) (Scalar × Complex A) Result Difference)
    (x : Scalar) (z : Complex A) (parts : ComponentOps m A := nativeComponents) : m Result :=
  subtractRealComplex
    { ops with
      subtract := fun x real =>
        match self.classify (x, real) with
        | .selectedOther => ops.subtract x real
        | .inherited (nextX, nextZ) => do
            let result ← subtractRealComplexRecursive ops self nextX nextZ parts
            pure (self.embedReturn result)
    }
    x z parts
partial_fixpoint monotonicity by
  unfold subtractRealComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:344-344. -/
-- Source: base/complex.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(z::Complex, x::Real) = Complex(real(z) - x, imag(z))
-- /Source
def subtractComplexRealRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {Scalar A R Result : Type}
    (ops : ScalarRightOps m A Scalar R Result)
    (self : SelfDispatch (A × Scalar) (Complex A × Scalar) Result R) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  subtractComplexReal
    { ops with
      operation := fun real x =>
        match self.classify (real, x) with
        | .selectedOther => ops.operation real x
        | .inherited (nextZ, nextX) => do
            let result ← subtractComplexRealRecursive ops self nextZ nextX parts
            pure (self.embedReturn result)
    }
    z x parts
partial_fixpoint monotonicity by
  unfold subtractComplexReal
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:345-345. -/
-- Source: base/complex.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Real, z::Complex) = Complex(x * real(z), x * imag(z))
-- /Source
def multiplyRealComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {Scalar A Product Result : Type}
    (ops : ScaleLeftOps m Scalar A Product Result)
    (self : SelfDispatch (Scalar × A) (Scalar × Complex A) Result Product) (x : Scalar) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  multiplyRealComplex
    { ops with
      operation := fun x part =>
        match self.classify (x, part) with
        | .selectedOther => ops.operation x part
        | .inherited (nextX, nextZ) => do
            let result ← multiplyRealComplexRecursive ops self nextX nextZ parts
            pure (self.embedReturn result)
    }
    x z parts
partial_fixpoint monotonicity by
  unfold multiplyRealComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:349-349. -/
-- Source: base/complex.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, y::Real) = Complex(muladd(real(z),x,y), imag(z)*x)
-- /Source
def muladdComplexRealRealRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A X Y R I Result : Type}
    (ops : MuladdComplexRealRealOps m A X Y R I Result)
    (self : SelfDispatch (A × X × Y) (Complex A × X × Y) Result R)
    (z : Complex A) (x : X) (y : Y)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  muladdComplexRealReal
    { ops with
      muladd := fun real x y =>
        match self.classify (real, x, y) with
        | .selectedOther => ops.muladd real x y
        | .inherited (nextZ, nextX, nextY) => do
            let result ← muladdComplexRealRealRecursive ops self nextZ nextX nextY parts
            pure (self.embedReturn result)
    }
    z x y parts
partial_fixpoint monotonicity by
  unfold muladdComplexRealReal
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:350-351. -/
-- Source: base/complex.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, x::Real, w::Complex) =
--     Complex(muladd(real(z),x,real(w)), muladd(imag(z),x,imag(w)))
-- /Source
def muladdComplexRealComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A X B Part Result : Type}
    (ops : MuladdComplexRealComplexOps m A X B Part Result)
    (self : SelfDispatch (A × X × B) (Complex A × X × Complex B) Result Part)
    (z : Complex A) (x : X) (w : Complex B)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result :=
  muladdComplexRealComplex
    { ops with
      muladd := fun left x right =>
        match self.classify (left, x, right) with
        | .selectedOther => ops.muladd left x right
        | .inherited (nextZ, nextX, nextW) => do
            let result ← muladdComplexRealComplexRecursive ops self nextZ nextX nextW partsA partsB
            pure (self.embedReturn result)
    }
    z x w partsA partsB
partial_fixpoint monotonicity by
  unfold muladdComplexRealComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:352-352. -/
-- Source: base/complex.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(x::Real, y::Real, z::Complex) = Complex(muladd(x,y,real(z)), imag(z))
-- /Source
def muladdRealRealComplexRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {X Y A R Result : Type}
    (ops : MuladdRealRealComplexOps m X Y A R Result)
    (self : SelfDispatch (X × Y × A) (X × Y × Complex A) Result R)
    (x : X) (y : Y) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  muladdRealRealComplex
    { ops with
      muladd := fun x y real =>
        match self.classify (x, y, real) with
        | .selectedOther => ops.muladd x y real
        | .inherited (nextX, nextY, nextZ) => do
            let result ← muladdRealRealComplexRecursive ops self nextX nextY nextZ parts
            pure (self.embedReturn result)
    }
    x y z parts
partial_fixpoint monotonicity by
  unfold muladdRealRealComplex
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:353-355. -/
-- Source: base/complex.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- muladd(z::Complex, w::Complex, x::Real) =
--     Complex(muladd(real(z), real(w), -_mulsub(imag(z), imag(w), x)),
--             muladd(real(z), imag(w), imag(z) * real(w)))
-- /Source
def muladdComplexComplexRealRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    {A B X Difference Negative Product R I Result : Type}
    (ops : MuladdComplexComplexRealOps m A B X Difference Negative Product R I Result)
    (selfReal : SelfDispatch (A × B × Negative) (Complex A × Complex B × X) Result R)
    (selfImag : SelfDispatch (A × B × Product) (Complex A × Complex B × X) Result I)
    (z : Complex A) (w : Complex B) (x : X)
    (partsA : ComponentOps m A := nativeComponents)
    (partsB : ComponentOps m B := nativeComponents) : m Result :=
  muladdComplexComplexReal
    { ops with
      muladdReal := fun left right negative =>
        match selfReal.classify (left, right, negative) with
        | .selectedOther => ops.muladdReal left right negative
        | .inherited (nextZ, nextW, nextX) => do
            let result ← muladdComplexComplexRealRecursive ops selfReal selfImag nextZ nextW nextX partsA partsB
            pure (selfReal.embedReturn result)
      muladdImag := fun left right product =>
        match selfImag.classify (left, right, product) with
        | .selectedOther => ops.muladdImag left right product
        | .inherited (nextZ, nextW, nextX) => do
            let result ← muladdComplexComplexRealRecursive ops selfReal selfImag nextZ nextW nextX partsA partsB
            pure (selfImag.embedReturn result)
    }
    z w x partsA partsB
partial_fixpoint monotonicity by
  unfold muladdComplexComplexReal
  dsimp only
  repeat' (first | assumption | monotonicity)

/-- Full source method with explicit inherited reentry.  The existing finite
body helper remains the actual implementation of every iteration; its selected
operation is replaced only by dispatch to another method or this real recursive
body.  All other selected callees, component accessors, state transitions,
exceptions, argument order, and dynamic result carriers remain unchanged.
The same accessor and dispatch records are used at every recursive entry;
partial_fixpoint represents divergence without fuel or a fabricated error.
Source reference: base/complex.jl:358-358. -/
-- Source: base/complex.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(z::Complex, x::Real) = Complex(real(z)/x, imag(z)/x)
-- /Source
def divideComplexRealRecursive {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m] {A Scalar Product Result : Type}
    (ops : ScaleRightOps m A Scalar Product Result)
    (self : SelfDispatch (A × Scalar) (Complex A × Scalar) Result Product) (z : Complex A) (x : Scalar)
    (parts : ComponentOps m A := nativeComponents) : m Result :=
  divideComplexReal
    { ops with
      operation := fun part x =>
        match self.classify (part, x) with
        | .selectedOther => ops.operation part x
        | .inherited (nextZ, nextX) => do
            let result ← divideComplexRealRecursive ops self nextZ nextX parts
            pure (self.embedReturn result)
    }
    z x parts
partial_fixpoint monotonicity by
  unfold divideComplexReal
  dsimp only
  repeat' (first | assumption | monotonicity)

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Runtime division selection after intermediate arithmetic.  The inherited
case stores the actual same-component-type Complex operands and their component
type tag; it means dispatch selects precisely base/complex.jl:360-377.  The
selectedOther case means any different selected method, including a more-specific
user method on Complex values.  This is a runtime dispatch representation, not
an assumed behavioral law about an arithmetic callee.  Selection is pure
runtime metadata: inherited payloads decode the original operands unchanged,
and selectedOther excludes this exact inherited method.
Source reference: base/complex.jl:360-377. -/
-- Source: base/complex.jl:360-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function /(a::Complex{T}, b::Complex{T}) where T<:Real
--     are = real(a); aim = imag(a); bre = real(b); bim = imag(b)
--     if (isinf(bre) | isinf(bim))
--         if isfinite(a)
--             return complex(zero(T)*sign(are)*sign(bre), -zero(T)*sign(aim)*sign(bim))
--         end
--         return T(NaN)+T(NaN)*im
--     end
--     if abs(bre) <= abs(bim)
--         r = bre / bim
--         den = bim + r*bre
--         Complex((are*r + aim)/den, (aim*r - are)/den)
--     else
--         r = bim / bre
--         den = bre + r*bim
--         Complex((are + aim*r)/den, (aim - are*r)/den)
--     end
-- end
-- /Source
inductive DivideSameTarget (V T : Type) where
  | inherited (componentType : T) (numerator denominator : Complex V)
  | selectedOther

/-- A universal runtime-value carrier is allowed here: V need not denote one
Julia type.  The input fields have the source Complex{T} representation invariant;
selected intermediate operations may return arbitrary runtime types.  T is the
original type tag, including an abstract Real field type.  divideTarget records
the actual runtime method selection.  Initially a and b have component type
t and every stored field is a Real; every inherited dispatch payload carries
the same invariant for its own next component tag.  V may still encode other
intermediate runtime types.  divideOther is used only for a different selected
method.  An inherited selection never passes through a supplied callee.
Source reference: base/complex.jl:360-377. -/
-- Source: base/complex.jl:360-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function /(a::Complex{T}, b::Complex{T}) where T<:Real
--     are = real(a); aim = imag(a); bre = real(b); bim = imag(b)
--     if (isinf(bre) | isinf(bim))
--         if isfinite(a)
--             return complex(zero(T)*sign(are)*sign(bre), -zero(T)*sign(aim)*sign(bim))
--         end
--         return T(NaN)+T(NaN)*im
--     end
--     if abs(bre) <= abs(bim)
--         r = bre / bim
--         den = bim + r*bre
--         Complex((are*r + aim)/den, (aim*r - are)/den)
--     else
--         r = bim / bre
--         den = bre + r*bim
--         Complex((are + aim*r)/den, (aim - are*r)/den)
--     end
-- end
-- /Source
structure DivideSameOps (m : Type → Type) (V T Other NotBool : Type) where
  isinf : V → m (PredicateValue Other)
  orOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)
  isfinite : Complex V → m (Checked Bool NotBool)
  zero : T → m V
  sign : V → m V
  negate : V → m V
  multiply : V → V → m V
  multiplyThree : V → V → V → m V
  publicComplex : V → V → m V
  fromNaN : T → JuliaLean.Float.F64 → m V
  multiplyImaginaryUnit : V → Complex Bool → m V
  add : V → V → m V
  subtract : V → V → m V
  abs : V → m V
  le : V → V → m (Checked Bool NotBool)
  divideTarget : V → V → DivideSameTarget V T
  divideOther : V → V → m V
  construct : V → V → m V

/-- Smith division and its exceptional branches, with every scalar call,
boolean check, type-level zero, and constructor retained in source order.
Each chained exceptional product is one selected ternary multiplication,
after both sign calls finish (manual/mathematical-operations.md:430-432,503).
All four selected component accessors run in the literal source order.
Their results share a dynamic value carrier and may change runtime types.
Intermediate divisions that select this same inherited method recurse here,
using the same component-accessor dispatch record.
The monad's partial order supports an actual least fixed point, including
divergence; no fuel limit, successful default, or recursion callback is used.
Source reference: base/complex.jl:360-377. -/
-- Source: base/complex.jl:360-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function /(a::Complex{T}, b::Complex{T}) where T<:Real
--     are = real(a); aim = imag(a); bre = real(b); bim = imag(b)
--     if (isinf(bre) | isinf(bim))
--         if isfinite(a)
--             return complex(zero(T)*sign(are)*sign(bre), -zero(T)*sign(aim)*sign(bim))
--         end
--         return T(NaN)+T(NaN)*im
--     end
--     if abs(bre) <= abs(bim)
--         r = bre / bim
--         den = bim + r*bre
--         Complex((are*r + aim)/den, (aim*r - are)/den)
--     else
--         r = bim / bre
--         den = bre + r*bim
--         Complex((are + aim*r)/den, (aim - are*r)/den)
--     end
-- end
-- /Source
def divideSameComplex {m : Type → Type} [Monad m] {E V T Other NotBool : Type}
    [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : DivideSameOps m V T Other NotBool)
    (t : T) (a b : Complex V)
    (parts : ComponentOps m V := nativeComponents) : m V := do
  let divide := fun x y =>
    match ops.divideTarget x y with
    | .inherited nextType nextA nextB =>
        divideSameComplex (E := E) ops nextType nextA nextB parts
    | .selectedOther => ops.divideOther x y
  let are ← parts.real a
  let aim ← parts.imag a
  let bre ← parts.real b
  let bim ← parts.imag b
  let ri ← ops.isinf bre
  let ii ← ops.isinf bim
  let inf ← match ri, ii with
    | .boolean x, .boolean y => pure (.boolean (x || y))
    | _, _ => ops.orOther ri ii
  let infinite ← match inf with
    | .boolean value => pure value
    | .other _ => throwThe (Error E) (.typeError "if")
  if infinite then
    let finite ← assertChecked (E := E) "if" (← ops.isfinite a)
    if finite then
      let zr ← ops.zero t
      let sar ← ops.sign are
      let sbr ← ops.sign bre
      let r ← ops.multiplyThree zr sar sbr
      let zi ← ops.zero t
      let nzi ← ops.negate zi
      let sai ← ops.sign aim
      let sbi ← ops.sign bim
      let i ← ops.multiplyThree nzi sai sbi
      return ← ops.publicComplex r i
    let r ← ops.fromNaN t JuliaLean.Float.F64.nan
    let i ← ops.fromNaN t JuliaLean.Float.F64.nan
    let p ← ops.multiplyImaginaryUnit i im
    return ← ops.add r p
  let ar ← ops.abs bre
  let ai ← ops.abs bim
  let smallReal ← assertChecked (E := E) "if" (← ops.le ar ai)
  if smallReal then
    let r ← divide bre bim
    let product ← ops.multiply r bre
    let den ← ops.add bim product
    let rproduct ← ops.multiply are r
    let rn ← ops.add rproduct aim
    let re ← divide rn den
    let iproduct ← ops.multiply aim r
    let inn ← ops.subtract iproduct are
    let imag ← divide inn den
    ops.construct re imag
  else
    let r ← divide bim bre
    let product ← ops.multiply r bim
    let den ← ops.add bre product
    let rproduct ← ops.multiply aim r
    let rn ← ops.add are rproduct
    let re ← divide rn den
    let iproduct ← ops.multiply are r
    let inn ← ops.subtract aim iproduct
    let imag ← divide inn den
    ops.construct re imag
partial_fixpoint

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Exact static Val{2} argument of the lowered literal power.  The function
argument is the fixed Base ^ function; only dispatch on the unfixed value is
open.  The lowering is documented at base/intfuncs.jl:453-460.
Source reference: base/complex.jl:524. -/
-- Source: base/complex.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
-- /Source
inductive SsqsLiteralExponent where
  | two

/-- Actual runtime result of exponent, partitioned by the concrete Int64
assignment target.  An Int64 result uses the installed identity conversion;
all other runtime types retain their selected convert(Int, value) call.
Source reference: base/complex.jl:526. -/
-- Source: base/complex.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         k = m==0 ? 0 : exponent(m)
-- /Source
inductive SsqsExponentValue (Other : Type) where
  | int64 (value : JInt .i64)
  | other (value : Other)

/-- Actual max result partitioned by the original T.  This is runtime type
metadata for the fixed isa test inserted by local-variable lowering, not a
selected isa callback.  Both constructors retain the unchanged runtime value.
Source reference: base/complex.jl:525; src/julia-syntax.scm:3870-3893. -/
-- Source: base/complex.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         m::T = max(abs(x), abs(y))
-- /Source
inductive SsqsMaximum (V : Type) where
  | inType (value : V)
  | other (value : V)

/-- Full generic scalar dispatch for ssqs.  V is a runtime-value carrier, not
an assertion that arithmetic retains the source component type.  Tag denotes
its original T<:Real; Checked partitions actual conversion results by isa T or
isa Int64, without imposing a correctness law on either conversion.
The max result partition executes the fixed isa guard inserted by local-variable
lowering: convertMax runs only for a value outside T, followed by ::T.
convertInf has no following type assertion because rho is untyped.
The literalPower target is literal_pow(^, value, Val{2}()), never an arbitrary
implementation of ssqs.  All selected callees differ from ssqs itself.
Source reference: base/complex.jl:519-531; typed assignment: manual/types.md:85-89. -/
-- Source: base/complex.jl:519-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ssqs(x::T, y::T) where T<:Real
--     k::Int = 0
--     ρ = x*x + y*y
--     if !isfinite(ρ) && (isinf(x) || isinf(y))
--         ρ = convert(T, Inf)
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
--         m::T = max(abs(x), abs(y))
--         k = m==0 ? 0 : exponent(m)
--         xk, yk = ldexp(x,-k), ldexp(y,-k)
--         ρ = xk*xk + yk*yk
--     end
--     ρ, k
-- end
-- /Source
structure SsqsOps (m : Type → Type) (Tag V Other NotT ExponentOther NotInt : Type) where
  multiply : V → V → m V
  add : V → V → m V
  isfinite : V → m (PredicateValue Other)
  notOther : Other → m (PredicateValue Other)
  isinf : V → m (PredicateValue Other)
  convertInf : Tag → JuliaLean.Float.F64 → m V
  equalZero : V → JInt .i64 → m (PredicateValue Other)
  notEqualZero : V → JInt .i64 → m (PredicateValue Other)
  zero : Tag → m V
  nextfloat : V → m V
  epsilon : Tag → m V
  literalPower : V → SsqsLiteralExponent → m V
  multiplyInt : JInt .i64 → V → m V
  divide : V → V → m V
  less : V → V → m (PredicateValue Other)
  abs : V → m V
  max : V → V → m (SsqsMaximum V)
  convertMax : Tag → V → m (Checked V NotT)
  exponent : V → m (SsqsExponentValue ExponentOther)
  convertInt : ExponentOther → m (Checked (JInt .i64) NotInt)
  ldexp : V → JInt .i64 → m V

/-- Fixed Boolean condition assertion at each source short-circuit, ternary,
and if boundary.  Predicate dispatch may return a non-Bool; it is rejected at
this exact use, after all effects of the predicate call and before later calls.
Source reference: base/complex.jl:522-526. -/
-- Source: base/complex.jl:522-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if !isfinite(ρ) && (isinf(x) || isinf(y))
--         ρ = convert(T, Inf)
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
--         m::T = max(abs(x), abs(y))
--         k = m==0 ? 0 : exponent(m)
-- /Source
def ssqsCondition {m : Type → Type} [Monad m] {E Other : Type}
    [MonadExceptOf (Error E) m] : PredicateValue Other → m Bool
  | .boolean value => pure value
  | .other _ => throwThe (Error E) (.typeError "ssqs Boolean condition")

/-- Typed assignment to the native Int local.  Conversion of a native Int64
result is fixed identity; the other branch executes selected conversion and
then the fixed Int64 assertion, preserving its exact throw point.
Source reference: base/complex.jl:520,526; manual/types.md:85-89. -/
-- Source: base/complex.jl:520-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     k::Int = 0
--     ρ = x*x + y*y
--     if !isfinite(ρ) && (isinf(x) || isinf(y))
--         ρ = convert(T, Inf)
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
--         m::T = max(abs(x), abs(y))
--         k = m==0 ? 0 : exponent(m)
-- /Source
def ssqsAssignExponent {m : Type → Type} [Monad m]
    {E Tag V Other NotT ExponentOther NotInt : Type}
    [MonadExceptOf (Error E) m]
    (ops : SsqsOps m Tag V Other NotT ExponentOther NotInt) :
    SsqsExponentValue ExponentOther → m (JInt .i64)
  | .int64 value => pure value
  | .other value => do
      assertChecked (E := E) "ssqs k::Int" (← ops.convertInt value)

/-- The elseif test preserves every short-circuit boundary.  In particular,
zero/nextfloat/epsilon/literal power and division are evaluated only if both
earlier disjuncts are false, and are evaluated in the original argument order.
Source reference: base/complex.jl:524. -/
-- Source: base/complex.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
-- /Source
def ssqsNeedsScaling {m : Type → Type} [Monad m]
    {E Tag V Other NotT ExponentOther NotInt : Type}
    [MonadExceptOf (Error E) m]
    (ops : SsqsOps m Tag V Other NotT ExponentOther NotInt)
    (tag : Tag) (x y rho : V) : m Bool := do
  if ← ssqsCondition (E := E) (← ops.isinf rho) then return true
  let rhoZero ← ssqsCondition (E := E) (← ops.equalZero rho (JInt.lit .i64 0))
  if rhoZero then
    if ← ssqsCondition (E := E) (← ops.notEqualZero x (JInt.lit .i64 0)) then return true
    if ← ssqsCondition (E := E) (← ops.notEqualZero y (JInt.lit .i64 0)) then return true
  let zero ← ops.zero tag
  let next ← ops.nextfloat zero
  let epsilon ← ops.epsilon tag
  let square ← ops.literalPower epsilon .two
  let denominator ← ops.multiplyInt (JInt.lit .i64 2) square
  let threshold ← ops.divide next denominator
  ssqsCondition (E := E) (← ops.less rho threshold)

/-- Complete source body of the internal scaled-sum helper.  The source's
rho local is untyped; all changes of its runtime type remain visible.  Both
typed assignments retain the inserted isa guards, conversions and assertions.  The paired ldexp
right-hand side is a matching syntactic two-tuple: tuple-to-assignments
lowering evaluates its elements into temporaries without indexed_iterate
(src/julia-syntax.scm:1789-1886,2610-2623).  Each native -k uses installed wrapping Int64
negation, including typemin(Int64), and the final result is the actual pair.
Source reference: base/complex.jl:519-531; manual/types.md:85-89. -/
-- Source: base/complex.jl:519-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ssqs(x::T, y::T) where T<:Real
--     k::Int = 0
--     ρ = x*x + y*y
--     if !isfinite(ρ) && (isinf(x) || isinf(y))
--         ρ = convert(T, Inf)
--     elseif isinf(ρ) || (ρ==0 && (x!=0 || y!=0)) || ρ<nextfloat(zero(T))/(2*eps(T)^2)
--         m::T = max(abs(x), abs(y))
--         k = m==0 ? 0 : exponent(m)
--         xk, yk = ldexp(x,-k), ldexp(y,-k)
--         ρ = xk*xk + yk*yk
--     end
--     ρ, k
-- end
-- /Source
def scaledSquares {m : Type → Type} [Monad m]
    {E Tag V Other NotT ExponentOther NotInt : Type}
    [MonadExceptOf (Error E) m]
    (ops : SsqsOps m Tag V Other NotT ExponentOther NotInt)
    (tag : Tag) (x y : V) : m (V × JInt .i64) := do
  let initialK := JInt.lit .i64 0
  let xx ← ops.multiply x x
  let yy ← ops.multiply y y
  let rho ← ops.add xx yy
  let finite ← ops.isfinite rho
  let notFinite ← match finite with
    | .boolean value => pure (.boolean (!value))
    | .other value => ops.notOther value
  let notFiniteCondition ← ssqsCondition (E := E) notFinite
  let infiniteInput ← if notFiniteCondition then do
      if ← ssqsCondition (E := E) (← ops.isinf x) then pure true
      else ssqsCondition (E := E) (← ops.isinf y)
    else pure false
  if infiniteInput then
    let converted ← ops.convertInf tag (JuliaLean.Float.F64.inf false)
    return (converted, initialK)
  if ← ssqsNeedsScaling (E := E) ops tag x y rho then
    let ax ← ops.abs x
    let ay ← ops.abs y
    let maximum ← match ← ops.max ax ay with
      | .inType value => pure value
      | .other value => assertChecked (E := E) "ssqs m::T" (← ops.convertMax tag value)
    let zeroMaximum ← ssqsCondition (E := E)
      (← ops.equalZero maximum (JInt.lit .i64 0))
    let k ← if zeroMaximum then pure (JInt.lit .i64 0)
      else ssqsAssignExponent (E := E) ops (← ops.exponent maximum)
    let xk ← ops.ldexp x (-k)
    let yk ← ops.ldexp y (-k)
    let xx ← ops.multiply xk xk
    let yy ← ops.multiply yk yk
    let rho ← ops.add xx yy
    return (rho, k)
  else
    return (rho, initialK)

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- The logarithm result, its real query, literal conversion, scalar log,
and quotient all retain the types actually selected at their call sites.
Source reference: base/complex.jl:695-702. -/
-- Source: base/complex.jl:695-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log10(z::Complex)
--     a = log(z)
--     a/log(oftype(real(a),10))
-- end
-- function log2(z::Complex)
--     a = log(z)
--     a/log(oftype(real(a),2))
-- end
-- /Source
structure LogBaseOps (m : Type → Type) (A Logged Real Converted Denominator Result : Type) where
  logarithm : Complex A → m Logged
  real : Logged → m Real
  oftype : Real → JInt .i64 → m Converted
  scalarLog : Converted → m Denominator
  divide : Logged → Denominator → m Result

/-- Evaluate the complex log once and retain it for the final division.
Source reference: base/complex.jl:695-698. -/
-- Source: base/complex.jl:695-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log10(z::Complex)
--     a = log(z)
--     a/log(oftype(real(a),10))
-- end
-- /Source
def logarithm10Complex {m : Type → Type} [Monad m]
    {A Logged Real Converted Denominator Result : Type}
    (ops : LogBaseOps m A Logged Real Converted Denominator Result)
    (z : Complex A) : m Result := do
  let a ← ops.logarithm z
  let r ← ops.real a
  let converted ← ops.oftype r (JInt.lit .i64 10)
  let denominator ← ops.scalarLog converted
  ops.divide a denominator

/-- The base-two variant uses native Int 2 at the original conversion point.
Source reference: base/complex.jl:699-702. -/
-- Source: base/complex.jl:699-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log2(z::Complex)
--     a = log(z)
--     a/log(oftype(real(a),2))
-- end
-- /Source
def logarithm2Complex {m : Type → Type} [Monad m]
    {A Logged Real Converted Denominator Result : Type}
    (ops : LogBaseOps m A Logged Real Converted Denominator Result)
    (z : Complex A) : m Result := do
  let a ← ops.logarithm z
  let r ← ops.real a
  let converted ← ops.oftype r (JInt.lit .i64 2)
  let denominator ← ops.scalarLog converted
  ops.divide a denominator

/-- _cpow is selected on the source's unfixed type T.  These power wrappers
do not replace their own body or recursion: each makes this one distinct call.
Source reference: base/complex.jl:882-884. -/
-- Source: base/complex.jl:882-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{T}, p::Complex{T}) where T<:Real = _cpow(z, p)
-- ^(z::Complex{T}, p::T) where T<:Real = _cpow(z, p)
-- ^(z::T, p::Complex{T}) where T<:Real = _cpow(z, p)
-- /Source
structure CPowOps (m : Type → Type) (A Result : Type) where
  call : RealOrComplex A (Complex A) → RealOrComplex A (Complex A) → m Result

/-- The two complex arguments are passed unchanged to the selected helper.
Source reference: base/complex.jl:882. -/
-- Source: base/complex.jl:882-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{T}, p::Complex{T}) where T<:Real = _cpow(z, p)
-- /Source
def powerComplexComplex {m : Type → Type} {A Result : Type}
    (ops : CPowOps m A Result) (z p : Complex A) : m Result :=
  ops.call (.complex z) (.complex p)

/-- Same-T real exponent forwarding, with its runtime Real tag preserved.
Source reference: base/complex.jl:883. -/
-- Source: base/complex.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{T}, p::T) where T<:Real = _cpow(z, p)
-- /Source
def powerComplexRealSame {m : Type → Type} {A Result : Type}
    (ops : CPowOps m A Result) (z : Complex A) (p : A) : m Result :=
  ops.call (.complex z) (.real p)

/-- Same-T real base forwarding, without coercing it to a Complex first.
Source reference: base/complex.jl:884. -/
-- Source: base/complex.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::T, p::Complex{T}) where T<:Real = _cpow(z, p)
-- /Source
def powerRealComplexSame {m : Type → Type} {A Result : Type}
    (ops : CPowOps m A Result) (z : A) (p : Complex A) : m Result :=
  ops.call (.real z) (.complex p)

/-- Return embeddings for a possible type-changing one(z).  They encode
the original object or the selected method's value, not new Julia objects.
Source reference: base/complex.jl:886,889-890. -/
-- Source: base/complex.jl:886-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Bool) = n ? z : one(z)
-- ^(z::Complex, n::Integer) = z^Complex(n)
-- 
-- ^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
-- ^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)        # to resolve ambiguity
-- /Source
inductive BooleanPowerResult (A One : Type) where
  | original (value : Complex A)
  | identity (value : One)

/-- one(z) dispatch depends on an unfixed component type, including arbitrary
Integer/AbstractFloat subtypes.  Its return is not silently restricted to A.
Source reference: base/complex.jl:886,889-890. -/
-- Source: base/complex.jl:886-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Bool) = n ? z : one(z)
-- ^(z::Complex, n::Integer) = z^Complex(n)
-- 
-- ^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
-- ^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)        # to resolve ambiguity
-- /Source
structure BooleanPowerOps (m : Type → Type) (A One : Type) where
  one : Complex A → m One

/-- The true branch returns the input object without calling one.
Source reference: base/complex.jl:886. -/
-- Source: base/complex.jl:886-886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Bool) = n ? z : one(z)
-- /Source
def powerComplexBool {m : Type → Type} [Monad m] {A One : Type}
    (ops : BooleanPowerOps m A One) (z : Complex A) (n : Bool) :
    m (BooleanPowerResult A One) := do
  if n then pure (.original z) else return .identity (← ops.one z)

/-- Post-construction exponent dispatch.  Recur means the actual dispatcher
reselected this fallback; selectedOther includes any more-specific integer
power method as well as non-integer exponents.
Source reference: base/complex.jl:887. -/
-- Source: base/complex.jl:887-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Integer) = z^Complex(n)
-- /Source
inductive IntegerPowerExponent (Integer Other : Type) where
  | recur (value : Integer)
  | selectedOther (value : Other)

/-- The integer carrier may include every Integer subtype.  The constructor
is selected on that unfixed input, and its result need not be a Complex.
Source reference: base/complex.jl:887. -/
-- Source: base/complex.jl:887-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Integer) = z^Complex(n)
-- /Source
structure IntegerPowerOps (E World A Integer Other Result : Type) where
  construct : Integer → PartialResult E World (IntegerPowerExponent Integer Other)
  powerOther : Complex A → Other → PartialResult E World Result

/-- Explicit fallback recursion handles a custom Complex(n) that returns an
integer selecting this same method again.  Divergence remains none.
Source reference: base/complex.jl:887. -/
-- Source: base/complex.jl:887-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex, n::Integer) = z^Complex(n)
-- /Source
def powerComplexInteger {E World A Integer Other Result : Type}
    (ops : IntegerPowerOps E World A Integer Other Result)
    (z : Complex A) (n : Integer) : PartialResult E World Result := fun world =>
  match ops.construct n world with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (.recur exponent, nextWorld)) => powerComplexInteger ops z exponent nextWorld
  | some (.ok (.selectedOther exponent, nextWorld)) => ops.powerOther z exponent nextWorld
partial_fixpoint

/-- AbstractFloat components retain custom one(z) dispatch and all effects.
Source reference: base/complex.jl:889. -/
-- Source: base/complex.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)  # to resolve ambiguity
-- /Source
def powerComplexFloatBool {m : Type → Type} [Monad m] {A One : Type}
    (ops : BooleanPowerOps m A One) (z : Complex A) (n : Bool) :
    m (BooleanPowerResult A One) := do
  if n then pure (.original z) else return .identity (← ops.one z)

/-- Integer components include Bool, BigInt and arbitrary user Integer
subtypes through their carrier and selected one(z) operation.
Source reference: base/complex.jl:890. -/
-- Source: base/complex.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)        # to resolve ambiguity
-- /Source
def powerComplexIntegerBool {m : Type → Type} [Monad m] {A One : Type}
    (ops : BooleanPowerOps m A One) (z : Complex A) (n : Bool) :
    m (BooleanPowerResult A One) := do
  if n then pure (.original z) else return .identity (← ops.one z)

/-- Rotation wrappers share only this operation shape.  Each record is
specialized to its named transcendental target; unknown constructor and
transcendental results retain arbitrary types and component-query dispatch.
Source reference: base/complex.jl:986-989,1024-1027. -/
-- Source: base/complex.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function atan(z::Complex)
--     w = atanh(Complex(-imag(z),real(z)))
--     Complex(imag(w),-real(w))
-- end
-- /Source
structure RotationOps (m : Type → Type) (A Negative Built W I R NegR Result : Type) where
  negateInput : A → m Negative
  constructInput : Negative → A → m Built
  transcendental : Built → m W
  imag : W → m I
  real : W → m R
  negateOutput : R → m NegR
  constructOutput : I → NegR → m Result

/-- atan uses the same explicit rotation around the selected atanh method.
Source reference: base/complex.jl:986-989. -/
-- Source: base/complex.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function atan(z::Complex)
--     w = atanh(Complex(-imag(z),real(z)))
--     Complex(imag(w),-real(w))
-- end
-- /Source
def arctangentComplex {m : Type → Type} [Monad m]
    {A Negative Built W I R NegR Result : Type}
    (ops : RotationOps m A Negative Built W I R NegR Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let imag ← parts.imag z
  let negative ← ops.negateInput imag
  let real ← parts.real z
  let built ← ops.constructInput negative real
  let w ← ops.transcendental built
  let i ← ops.imag w
  let r ← ops.real w
  let negativeReal ← ops.negateOutput r
  ops.constructOutput i negativeReal

/-- asinh's rotation around asin retains every selected call and error point.
Source reference: base/complex.jl:1024-1027. -/
-- Source: base/complex.jl:1024-1027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function asinh(z::Complex)
--     w = asin(Complex(-imag(z),real(z)))
--     Complex(imag(w),-real(w))
-- end
-- /Source
def inverseHyperbolicSineComplex {m : Type → Type} [Monad m]
    {A Negative Built W I R NegR Result : Type}
    (ops : RotationOps m A Negative Built W I R NegR Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let imag ← parts.imag z
  let negative ← ops.negateInput imag
  let real ← parts.real z
  let built ← ops.constructInput negative real
  let w ← ops.transcendental built
  let i ← ops.imag w
  let r ← ops.real w
  let negativeReal ← ops.negateOutput r
  ops.constructOutput i negativeReal

/-- Keyword arguments are an opaque Julia keyword bundle passed unchanged to
each scalar call.  It includes empty kwargs, digits, sigdigits, base, unknown
keywords and any selected custom RoundingMode behavior.  nearest denotes the
fixed Base RoundNearest value, not a user-supplied numerical correctness law.
Source reference: base/complex.jl:1123-1126. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
structure RoundOps (m : Type → Type) (A Mode Keywords Rounded Result : Type) where
  nearest : Mode
  round : A → Mode → Keywords → m Rounded
  construct : Rounded → Rounded → m Result

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Real rounding, imaginary rounding, then construction, with both source
defaults retained and no restriction to a finite subset of modes or keywords.
Source reference: base/complex.jl:1123-1126. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundComplex {m : Type → Type} [Monad m] {A Mode Keywords Rounded Result : Type}
    (ops : RoundOps m A Mode Keywords Rounded Result) (z : Complex A)
    (rr : Mode := ops.nearest) (ri : Mode := rr) (keywords : Keywords)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.round real rr keywords
  let imag ← parts.imag z
  let i ← ops.round imag ri keywords
  ops.construct r i

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Generic component conversion to floating values preserves effects, type
changes, and constructor dispatch.  The AbstractFloat identity specialization
in the baseline remains unchanged.
Source reference: base/complex.jl:1130. -/
-- Source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(z::Complex) = Complex(float(real(z)), float(imag(z)))
-- /Source
def floatComplex {m : Type → Type} [Monad m] {A B Result : Type}
    (ops : UnaryConstructOps m A B Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.scalar real
  let imag ← parts.imag z
  let i ← ops.scalar imag
  ops.construct r i

/-- big(T) is selected on an unfixed type, with arbitrary returned values.
Source reference: base/complex.jl:1132-1133. -/
-- Source: base/complex.jl:1132-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}
-- big(z::Complex{T}) where {T<:Real} = Complex{big(T)}(z)
-- /Source
structure BigTypeOps (m : Type → Type) (T Parameter Rejected : Type) where
  big : T → m (TypeParameter Parameter Rejected)

/-- The target constructor receives the actual constructed type, after its
type-parameter check; it can return arbitrary values or raise exceptions.
Source reference: base/complex.jl:1133. -/
-- Source: base/complex.jl:1133-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(z::Complex{T}) where {T<:Real} = Complex{big(T)}(z)
-- /Source
structure BigValueOps (m : Type → Type) (T Parameter Rejected A Result : Type) where
  big : T → m (TypeParameter Parameter Rejected)
  construct : ComplexTy Parameter → Complex A → m Result

/-- Exact source element-type descriptor: the tag identifies T and concrete
is intrinsic type metadata.  The source calls the generic isconcretetype;
this metadata does not replace that selected call or constrain its result.
Source reference: base/complex.jl:1155-1160. -/
-- Source: base/complex.jl:1155-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function complex(A::AbstractArray{T}) where T
--     if !isconcretetype(T)
--         error("`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
--     end
--     convert(AbstractArray{typeof(complex(zero(T)))}, A)
-- end
-- /Source
structure ArrayElementType (Tag : Type) where
  tag : Tag
  concrete : Bool

/-- AbstractArray{element}, with its dimension parameter left unconstrained.
Every actual typeof tag is a legal element type; no conversion has occurred.
Source reference: base/complex.jl:1159. -/
-- Source: base/complex.jl:1159-1159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     convert(AbstractArray{typeof(complex(zero(T)))}, A)
-- /Source
structure AbstractArrayType (Tag : Type) where
  element : Tag

/-- Actual dispatch of complex(zero(T)).  An inherited selection decodes the
original zero result as an array handle with its exact element-type metadata;
selectedOther excludes this exact fallback.  This is runtime dispatch metadata,
not a behavioral assumption about zero or any selected complex method.
Source reference: base/complex.jl:1155-1160. -/
-- Source: base/complex.jl:1155-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function complex(A::AbstractArray{T}) where T
--     if !isconcretetype(T)
--         error("`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
--     end
--     convert(AbstractArray{typeof(complex(zero(T)))}, A)
-- end
-- /Source
inductive ArrayComplexTarget (Tag Array : Type) where
  | inherited (element : ArrayElementType Tag) (array : Array)
  | selectedOther

/-- Array handles preserve their original axes, memory and identity in the
effect monad.  isconcretetype dispatches on the unfixed element type, including
more-specific methods with arbitrary results, effects and errors.  Bool ! is
closed in the caller; notOther is selected only for an actual non-Bool result.
Every value carries its actual typeof tag, including a recursive array result.
complexOther is used only when dispatch selects a different method.
Source reference: base/complex.jl:1155-1160. -/
-- Source: base/complex.jl:1155-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function complex(A::AbstractArray{T}) where T
--     if !isconcretetype(T)
--         error("`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
--     end
--     convert(AbstractArray{typeof(complex(zero(T)))}, A)
-- end
-- /Source
structure ArrayComplexOps (m : Type → Type) (Tag : Type) (Value : Tag → Type)
    (Array NotBool : Type) where
  isConcrete : Tag → m (PredicateValue NotBool)
  notOther : NotBool → m (Checked Bool NotBool)
  zero : Tag → m (Sigma Value)
  complexTarget : Sigma Value → ArrayComplexTarget Tag Array
  complexOther : Sigma Value → m (Sigma Value)
  convert : AbstractArrayType Tag → Array → m (Sigma Value)

/-- Query isconcretetype(T) on every entry, negate its actual result, and
assert the if condition as Bool.  A true condition raises the fixed source
ErrorException before zero or conversion.  Otherwise use the actual
complex(zero(T)) runtime type and pass the original array handle to convert,
retaining aliasing, effects and conversion errors.
If complex(zero(T)) selects this same method, recur explicitly without a fuel
bound; the actual recursive return supplies the typeof tag for outer convert.
Source reference: base/complex.jl:1155-1160. -/
-- Source: base/complex.jl:1155-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function complex(A::AbstractArray{T}) where T
--     if !isconcretetype(T)
--         error("`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
--     end
--     convert(AbstractArray{typeof(complex(zero(T)))}, A)
-- end
-- /Source
def complexArray {m : Type → Type} [Monad m] {E Tag : Type} {Value : Tag → Type}
    {Array NotBool : Type} [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : ArrayComplexOps m Tag Value Array NotBool)
    (t : ArrayElementType Tag) (array : Array) : m (Sigma Value) := do
  let concrete ← ops.isConcrete t.tag
  let condition ← match concrete with
    | .boolean value => pure (!value)
    | .other value => assertChecked (E := E) "if" (← ops.notOther value)
  if condition then
    throwThe (Error E) (.errorException
      "`complex` not defined on abstractly-typed arrays; please convert to a more specific type")
  else
    let zero ← ops.zero t.tag
    let converted ← match ops.complexTarget zero with
      | .inherited element next => complexArray (E := E) ops element next
      | .selectedOther => ops.complexOther zero
    ops.convert ⟨converted.1⟩ array
partial_fixpoint

/-- Scalar epsilon results need not retain the component type, and hypot is
selected only after both calls have completed.
Source reference: base/complex.jl:1164. -/
-- Source: base/complex.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(z::Complex{<:AbstractFloat}) = hypot(eps(real(z)), eps(imag(z)))
-- /Source
structure EpsilonValueOps (m : Type → Type) (A Epsilon Result : Type) where
  epsilon : A → m Epsilon
  hypot : Epsilon → Epsilon → m Result

/-- Internal one-step body used by registered native and finite-call invariants.
The corresponding Full declaration implements every possible self-recursive selection.
 Evaluate eps(real(z)), then eps(imag(z)), then their selected hypot.
Source reference: base/complex.jl:1164. -/
-- Source: base/complex.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(z::Complex{<:AbstractFloat}) = hypot(eps(real(z)), eps(imag(z)))
-- /Source
def epsilonComplex {m : Type → Type} [Monad m] {A Epsilon Result : Type}
    (ops : EpsilonValueOps m A Epsilon Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let real ← parts.real z
  let r ← ops.epsilon real
  let imag ← parts.imag z
  let i ← ops.epsilon imag
  ops.hypot r i

/-- Keep the native Int factor 2, scalar one(T), sqrt result and eps(T) in
their actual distinct intermediate types.  T may be a custom AbstractFloat.
Source reference: base/complex.jl:1166. -/
-- Source: base/complex.jl:1166-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(::Type{Complex{T}}) where {T<:AbstractFloat} = sqrt(2*one(T))*eps(T)
-- /Source
structure EpsilonTypeOps (m : Type → Type) (T One Product Root Epsilon Result : Type) where
  one : T → m One
  multiplyTwo : JInt .i64 → One → m Product
  sqrt : Product → m Root
  epsilon : T → m Epsilon
  multiply : Root → Epsilon → m Result

/-- sqrt(2*one(T)) is completed before eps(T) is evaluated.
Source reference: base/complex.jl:1166. -/
-- Source: base/complex.jl:1166-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(::Type{Complex{T}}) where {T<:AbstractFloat} = sqrt(2*one(T))*eps(T)
-- /Source
def epsilonComplexType {m : Type → Type} [Monad m] {T One Product Root Epsilon Result : Type}
    (ops : EpsilonTypeOps m T One Product Root Epsilon Result) (t : T) : m Result := do
  let one ← ops.one t
  let product ← ops.multiplyTwo (JInt.lit .i64 2) one
  let root ← ops.sqrt product
  let epsilon ← ops.epsilon t
  ops.multiply root epsilon

/-- Two-argument atan is selected on the actual queried coordinate values.
Source reference: base/complex.jl:651. -/
-- Source: base/complex.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- angle(z::Complex) = atan(imag(z), real(z))
-- /Source
structure AngleOps (m : Type → Type) (A Result : Type) where
  atan2 : A → A → m Result

/-- Query imaginary before real, then retain atan's argument order and
all getter/callee effects.  This includes more-specific coordinate methods.
Source reference: base/complex.jl:651. -/
-- Source: base/complex.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- angle(z::Complex) = atan(imag(z), real(z))
-- /Source
def angleComplex {m : Type → Type} [Monad m] {A Result : Type}
    (ops : AngleOps m A Result) (z : Complex A)
    (parts : ComponentOps m A := nativeComponents) : m Result := do
  let imag ← parts.imag z
  let real ← parts.real z
  ops.atan2 imag real

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Runtime selection of this same round method at a scalar call.  The stored
Complex argument is the original decoded value, while the mode and keywords
remain the actual scalar call's arguments.  embed is a pure identity injection
between runtime carriers, not a replacement for Julia conversion or dispatch.
Source reference: base/complex.jl:1123-1126. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
structure RoundRecursiveDispatch (A Mode Keywords Rounded Result : Type) where
  same : A → Mode → Keywords → Option (Complex A)
  embed : Result → Rounded

/-- Full round body including recursive Complex values returned by selected
coordinate getters.  Each scalar round has one supplied mode, so a recursive
selection receives that mode as both rr and its default ri; the original keyword
bundle is retained.  Recursive divergence is represented by the monad's bottom.
Source reference: base/complex.jl:1123-1126. -/
-- Source: base/complex.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)
--     Complex(round(real(z), rr; kwargs...),
--             round(imag(z), ri; kwargs...))
-- end
-- /Source
def roundComplexFull {m : Type → Type} [Monad m] {A Mode Keywords Rounded Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : RoundOps m A Mode Keywords Rounded Result)
    (dispatch : RoundRecursiveDispatch A Mode Keywords Rounded Result)
    (z : Complex A) (rr : Mode := ops.nearest) (ri : Mode := rr) (keywords : Keywords)
    (parts : ComponentOps m A) : m Result := do
  let real ← parts.real z
  let r : Rounded ← match dispatch.same real rr keywords with
    | some next => do
        let result ← roundComplexFull ops dispatch next rr rr keywords parts
        pure (dispatch.embed result)
    | none => ops.round real rr keywords
  let imag ← parts.imag z
  let i : Rounded ← match dispatch.same imag ri keywords with
    | some next => do
        let result ← roundComplexFull ops dispatch next ri ri keywords parts
        pure (dispatch.embed result)
    | none => ops.round imag ri keywords
  ops.construct r i
partial_fixpoint

/-- Full componentwise float includes redispatch to this source method at
both scalar sites.  A Complex AbstractFloat identity selection is a distinct
method and therefore remains in the selected scalar callee, not the recursive
metadata branch.  Every query, conversion, constructor and failure keeps order.
Source reference: base/complex.jl:1130. -/
-- Source: base/complex.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(z::Complex) = Complex(float(real(z)), float(imag(z)))
-- /Source
def floatComplexFull {m : Type → Type} [Monad m] {A B Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : UnaryConstructOps m A B Result) (dispatch : UnaryRecursiveDispatch A B Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive ops dispatch z parts

/-- Full epsilon body uses the explicit two-site recursive algorithm with
its actual scalar eps and terminal hypot operations.  The same-method metadata
requires the decoded Complex value to select this AbstractFloat-component source
method, rather than merely to have a Complex runtime tag.
Source reference: base/complex.jl:1164. -/
-- Source: base/complex.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eps(z::Complex{<:AbstractFloat}) = hypot(eps(real(z)), eps(imag(z)))
-- /Source
def epsilonComplexFull {m : Type → Type} [Monad m] {A Epsilon Result : Type}
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (ops : EpsilonValueOps m A Epsilon Result)
    (dispatch : UnaryRecursiveDispatch A Epsilon Result)
    (z : Complex A) (parts : ComponentOps m A) : m Result :=
  unaryComplexRecursive { scalar := ops.epsilon, construct := ops.hypot } dispatch z parts

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Exact input shapes for the two heterogeneous power fallbacks.  Tags are
the actual source type parameters.  V is a universal runtime-value carrier;
the decoded input values obey the stated Real/Complex field invariants.
Source reference: base/complex.jl:896-903. -/
-- Source: base/complex.jl:896-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ^(z::Complex{T}, p::S) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return Complex{P}(z) ^ P(p)
-- end
-- function ^(z::T, p::Complex{S}) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return P(z) ^ Complex{P}(p)
-- end
-- /Source
inductive PromotedPowerCall (V Tag : Type) where
  | complexReal (componentType exponentType : Tag) (base : Complex V) (exponent : V)
  | realComplex (baseType componentType : Tag) (base : V) (exponent : Complex V)

/-- Actual power dispatch after both constructors.  An inherited payload
decodes these same values into one of the two source fallbacks; selectedOther
excludes both fallbacks, including more-specific selected power methods.
Classification is pure method-table metadata and never a recursive callback.
Source reference: base/complex.jl:896-903. -/
-- Source: base/complex.jl:896-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ^(z::Complex{T}, p::S) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return Complex{P}(z) ^ P(p)
-- end
-- function ^(z::T, p::Complex{S}) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return P(z) ^ Complex{P}(p)
-- end
-- /Source
inductive PromotedPowerTarget (V Tag : Type) where
  | inherited (call : PromotedPowerCall V Tag)
  | selectedOther

/-- The promoted object is retained even if it is not an admissible Complex
type parameter.  In the real-base method P(z) runs before Complex{P} is applied,
so an inadmissible but callable P may have effects before TypeError.  Selected
constructors may change result type.  All outputs use the same runtime universe
so recursive power returns require no conversion or representation cast.
Source reference: base/complex.jl:896-903. -/
-- Source: base/complex.jl:896-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ^(z::Complex{T}, p::S) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return Complex{P}(z) ^ P(p)
-- end
-- function ^(z::T, p::Complex{S}) where {T<:Real,S<:Real}
--     P = promote_type(T,S)
--     return P(z) ^ Complex{P}(p)
-- end
-- /Source
structure PromotedPowerOps (m : Type → Type) (V Tag Rejected : Type) where
  promote : Tag → Tag → m (TypeParameter Tag Rejected)
  scalarConstruct : TypeParameter Tag Rejected → V → m V
  complexConstruct : ComplexTy Tag → Complex V → m V
  powerTarget : V → V → PromotedPowerTarget V Tag
  powerOther : V → V → m V

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-!
These callers retain arbitrary runtime values returned by reim, sincos,
indexed_iterate, scalar operations, and constructors.  The shared Core field
reader implements the actual destructuring lowering, including undefined
references and heap reads.  V is a runtime carrier, with the input's declared
Julia Real/Complex representation as its only input restriction.  No selected
callee's result is assumed to be a tuple or a Complex.
-/

/-- Open sincos and constructor calls for a Real argument; iteration retains
its arbitrary result and shares the caller's heap.
Source reference: base/complex.jl:587-590. -/
-- Source: base/complex.jl:587-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cis(theta::Real)
--     s, c = sincos(theta)
--     Complex(c, s)
-- end
-- /Source
structure CisRealOps (m : Type → Type) (V : Type) where
  sincos : V → m V
  iteration : IndexedIterateOps m V
  construct : V → V → m V

/-- Two-value destructuring is the actual lowered indexed_iterate/getfield
sequence, followed by the constructor with cosine before sine.
Source reference: base/complex.jl:587-590. -/
-- Source: base/complex.jl:587-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cis(theta::Real)
--     s, c = sincos(theta)
--     Complex(c, s)
-- end
-- /Source
def cisReal {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : CisRealOps m V) (theta : V) : m V := do
  let result ← ops.sincos theta
  let (s, c) ← destructureTwo (E := E) view ops.iteration result
  ops.construct c s

/-- Distinct selected operations remain open on all unfixed runtime values.
The two products are separate effectful calls to the selected multiplication.
Source reference: base/complex.jl:592-596. -/
-- Source: base/complex.jl:592-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cis(z::Complex)
--     v = exp(-imag(z))
--     s, c = sincos(real(z))
--     Complex(v * c, v * s)
-- end
-- /Source
structure CisComplexOps (m : Type → Type) (V : Type) where
  negate : V → m V
  exponential : V → m V
  sincos : V → m V
  iteration : IndexedIterateOps m V
  multiply : V → V → m V
  construct : V → V → m V

/-- The damping factor is computed before querying the real component;
constructor arguments evaluate cosine product before sine product.
Source reference: base/complex.jl:592-596. -/
-- Source: base/complex.jl:592-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cis(z::Complex)
--     v = exp(-imag(z))
--     s, c = sincos(real(z))
--     Complex(v * c, v * s)
-- end
-- /Source
def cisComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : CisComplexOps m V)
    (z : Complex V) (parts : ComponentOps m V) : m V := do
  let imaginary ← parts.imag z
  let negative ← ops.negate imaginary
  let v ← ops.exponential negative
  let real ← parts.real z
  let result ← ops.sincos real
  let (s, c) ← destructureTwo (E := E) view ops.iteration result
  let re ← ops.multiply v c
  let im ← ops.multiply v s
  ops.construct re im

/-- multiplyPi is specialized to the actual first argument
Base.MathConstants.pi : Irrational{:π}, not an approximating Float64 value.
Its second argument is unfixed, so the selected multiplication remains open.
Source reference: base/complex.jl:620-624; base/mathconstants.jl:13,59. -/
-- Source: base/complex.jl:620-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cispi(z::Complex)
--     v = exp(-(pi*imag(z)))
--     s, c = sincospi(real(z))
--     Complex(v * c, v * s)
-- end
-- /Source
structure CisPiComplexOps (m : Type → Type) (V : Type) where
  multiplyPi : V → m V
  negate : V → m V
  exponential : V → m V
  sincospi : V → m V
  iteration : IndexedIterateOps m V
  multiply : V → V → m V
  construct : V → V → m V

/-- Preserve π-times-imaginary, negation, exponentiation, the independent
real query and sincospi destructuring, then both products in source order.
Source reference: base/complex.jl:620-624. -/
-- Source: base/complex.jl:620-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cispi(z::Complex)
--     v = exp(-(pi*imag(z)))
--     s, c = sincospi(real(z))
--     Complex(v * c, v * s)
-- end
-- /Source
def cispiComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : CisPiComplexOps m V)
    (z : Complex V) (parts : ComponentOps m V) : m V := do
  let imaginary ← parts.imag z
  let scaled ← ops.multiplyPi imaginary
  let negative ← ops.negate scaled
  let v ← ops.exponential negative
  let real ← parts.real z
  let result ← ops.sincospi real
  let (s, c) ← destructureTwo (E := E) view ops.iteration result
  let re ← ops.multiply v c
  let im ← ops.multiply v s
  ops.construct re im

/-- reim and tanh remain selected calls on unfixed types.  Their results,
including each output component query, retain the full runtime carrier.
Source reference: base/complex.jl:943-947. -/
-- Source: base/complex.jl:943-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tan(z::Complex)
--     zr, zi = reim(z)
--     w = tanh(Complex(-zi, zr))
--     Complex(imag(w), -real(w))
-- end
-- /Source
structure TangentOps (m : Type → Type) (V : Type) where
  reim : Complex V → m V
  iteration : IndexedIterateOps m V
  negateInput : V → m V
  constructInput : V → V → m V
  hyperbolicTangent : V → m V
  imag : V → m V
  real : V → m V
  negateOutput : V → m V
  constructOutput : V → V → m V

/-- The selected reim value is destructured with actual Core field access;
rotations retain both selected negations and all intermediate return types.
Source reference: base/complex.jl:943-947. -/
-- Source: base/complex.jl:943-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tan(z::Complex)
--     zr, zi = reim(z)
--     w = tanh(Complex(-zi, zr))
--     Complex(imag(w), -real(w))
-- end
-- /Source
def tangentComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : TangentOps m V) (z : Complex V) : m V := do
  let result ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration result
  let negative ← ops.negateInput zi
  let argument ← ops.constructInput negative zr
  let w ← ops.hyperbolicTangent argument
  let imaginary ← ops.imag w
  let real ← ops.real w
  let negReal ← ops.negateOutput real
  ops.constructOutput imaginary negReal

/-- Hyperbolic sine uses one selected reim, one sin call, and two independent
output component queries; neither intermediate value is forced to Complex.
Source reference: base/complex.jl:991-995. -/
-- Source: base/complex.jl:991-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sinh(z::Complex)
--     zr, zi = reim(z)
--     w = sin(Complex(zi, zr))
--     Complex(imag(w),real(w))
-- end
-- /Source
structure HyperbolicSineOps (m : Type → Type) (V : Type) where
  reim : Complex V → m V
  iteration : IndexedIterateOps m V
  constructInput : V → V → m V
  sine : V → m V
  imag : V → m V
  real : V → m V
  constructOutput : V → V → m V

/-- Swap the selected real/imaginary values at the input constructor, then
query sine's imaginary output before its real output.
Source reference: base/complex.jl:991-995. -/
-- Source: base/complex.jl:991-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sinh(z::Complex)
--     zr, zi = reim(z)
--     w = sin(Complex(zi, zr))
--     Complex(imag(w),real(w))
-- end
-- /Source
def hyperbolicSineComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : HyperbolicSineOps m V)
    (z : Complex V) : m V := do
  let result ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration result
  let argument ← ops.constructInput zi zr
  let w ← ops.sine argument
  let imaginary ← ops.imag w
  let real ← ops.real w
  ops.constructOutput imaginary real

/-- Hyperbolic cosine's cosine result is returned directly, with no output
constructor, component query, type assertion, or coercion.
Source reference: base/complex.jl:997-1000. -/
-- Source: base/complex.jl:997-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cosh(z::Complex)
--     zr, zi = reim(z)
--     cos(Complex(zi,-zr))
-- end
-- /Source
structure HyperbolicCosineOps (m : Type → Type) (V : Type) where
  reim : Complex V → m V
  iteration : IndexedIterateOps m V
  negate : V → m V
  construct : V → V → m V
  cosine : V → m V

/-- The negation is applied only to the destructured real value; the first
constructor argument remains the original destructured imaginary value.
Source reference: base/complex.jl:997-1000. -/
-- Source: base/complex.jl:997-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cosh(z::Complex)
--     zr, zi = reim(z)
--     cos(Complex(zi,-zr))
-- end
-- /Source
def hyperbolicCosineComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : HyperbolicCosineOps m V)
    (z : Complex V) : m V := do
  let result ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration result
  let negative ← ops.negate zr
  let argument ← ops.construct zi negative
  ops.cosine argument

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Selected callees of the generic Complex inverse.  V contains actual
runtime values, so reim, its selected iterator targets, scalar calls and the
lowercase complex constructor can change runtime types.  Bool | Bool is closed
to native eager disjunction; orOther is called only when at least one actual
predicate result is non-Bool.  None of these targets replaces inv itself.
Source reference: base/complex.jl:283-287. -/
-- Source: base/complex.jl:283-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function inv(z::Complex)
--     c, d = reim(z)
--     (isinf(c) | isinf(d)) && return complex(copysign(zero(c), c), flipsign(-zero(d), d))
--     complex(c, -d)/(c * c + d * d)
-- end
-- /Source
structure InverseReopenedOps (m : Type → Type) (A V Other : Type) where
  reim : Complex A → m V
  iterations : IndexedIterateOps m V
  isinf : V → m (PredicateValue Other)
  orOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)
  zero : V → m V
  negate : V → m V
  copysign : V → V → m V
  flipsign : V → V → m V
  publicComplex : V → V → m V
  multiply : V → V → m V
  add : V → V → m V
  divide : V → V → m V

/-- Complete generic inv body.  Selected reim is evaluated once, then its
actual result is destructured through the source's indexed_iterate calls and
closed numeric Core.getfield reads of the current heap.  Both isinf calls run
before eager | dispatch and the Boolean condition assertion.  The infinite
branch constructs its two signed zeros left to right; the finite branch fully
evaluates complex(c,-d) before either denominator product.  Every returned
value and every exception retains its actual runtime origin.
Source reference: base/complex.jl:283-287. -/
-- Source: base/complex.jl:283-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function inv(z::Complex)
--     c, d = reim(z)
--     (isinf(c) | isinf(d)) && return complex(copysign(zero(c), c), flipsign(-zero(d), d))
--     complex(c, -d)/(c * c + d * d)
-- end
-- /Source
def inverseComplexReopened {m : Type → Type} [Monad m]
    {E Ref A V Other : Type} [MonadStateOf (FieldHeap Ref V) m]
    [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V)
    (ops : InverseReopenedOps m A V Other) (z : Complex A) : m V := do
  let components ← ops.reim z
  let (c, d) ← destructureTwo (E := E) view ops.iterations components
  let cInfinite ← ops.isinf c
  let dInfinite ← ops.isinf d
  let infinite ← match cInfinite, dInfinite with
    | .boolean a, .boolean b => pure (.boolean (a || b))
    | a, b => ops.orOther a b
  let infinite ← match infinite with
    | .boolean value => pure value
    | .other _ => throwThe (Error E) (.typeError "inv Boolean condition")
  if infinite then
    let cZero ← ops.zero c
    let real ← ops.copysign cZero c
    let dZero ← ops.zero d
    let negativeDZero ← ops.negate dZero
    let imag ← ops.flipsign negativeDZero d
    ops.publicComplex real imag
  else
    let negativeD ← ops.negate d
    let numerator ← ops.publicComplex c negativeD
    let cc ← ops.multiply c c
    let dd ← ops.multiply d d
    let denominator ← ops.add cc dd
    ops.divide numerator denominator

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Actual same-method exp2/exp10 selection after real(float(z)).  Payloads
decode the original argument and its actual component type without conversion;
none selects a different scalar or custom exponential method.  All intermediate
values use a universal runtime carrier, including changed constructor types.
The operation record is specialized to the named exponential function.
Source reference: base/complex.jl:775-789. -/
-- Source: base/complex.jl:775-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp2(z::Complex{T}) where T
--     z = float(z)
--     er = exp2(real(z))
--     theta = imag(z) * log(convert(float(T), 2))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- 
-- function exp10(z::Complex{T}) where T
--     z = float(z)
--     er = exp10(real(z))
--     theta = imag(z) * log(convert(float(T), 10))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- /Source
structure ExponentialBaseOps (m : Type → Type) (V Tag Target : Type) where
  floatValue : Complex V → m V
  real : V → m V
  imag : V → m V
  same : V → Option (Tag × Complex V)
  scalarExponential : V → m V
  floatType : Tag → m Target
  convert : Target → JInt .i64 → m V
  logarithm : V → m V
  multiply : V → V → m V
  sincos : V → m V
  iterate : IndexedIterateOps m V
  construct : V → V → m V

/-- Shared explicit bodies for exp2 and exp10.  The literal is supplied only
by the two public wrappers below.  float(z) runs before real(z); an actual
recursive exponential completes before imag(z), float(T), conversion and log.
The selected sincos result is destructured through real indexed_iterate calls
and the closed Core field reads, retaining malformed-return errors and heap
mutation.  Final products are er*c followed by er*s.
Source reference: base/complex.jl:775-789. -/
-- Source: base/complex.jl:775-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp2(z::Complex{T}) where T
--     z = float(z)
--     er = exp2(real(z))
--     theta = imag(z) * log(convert(float(T), 2))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- 
-- function exp10(z::Complex{T}) where T
--     z = float(z)
--     er = exp10(real(z))
--     theta = imag(z) * log(convert(float(T), 10))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- /Source
def exponentialBaseComplex {m : Type → Type} [Monad m] {E V Ref Tag Target : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : ExponentialBaseOps m V Tag Target)
    (literal : JInt .i64) (t : Tag) (z : Complex V) : m V := do
  let floating ← ops.floatValue z
  let real ← ops.real floating
  let er ← match ops.same real with
    | some (nextType, next) => exponentialBaseComplex (E := E) view ops literal nextType next
    | none => ops.scalarExponential real
  let imaginary ← ops.imag floating
  let target ← ops.floatType t
  let converted ← ops.convert target literal
  let logarithm ← ops.logarithm converted
  let theta ← ops.multiply imaginary logarithm
  let pair ← ops.sincos theta
  let values ← destructureTwo (E := E) view ops.iterate pair
  let re ← ops.multiply er values.2
  let im ← ops.multiply er values.1
  ops.construct re im
partial_fixpoint

/-- Base-two exponential, with the fixed Julia native Int literal 2.
Source reference: base/complex.jl:775-781. -/
-- Source: base/complex.jl:775-781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp2(z::Complex{T}) where T
--     z = float(z)
--     er = exp2(real(z))
--     theta = imag(z) * log(convert(float(T), 2))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- /Source
def exponential2Complex {m : Type → Type} [Monad m] {E V Ref Tag Target : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : ExponentialBaseOps m V Tag Target)
    (t : Tag) (z : Complex V) : m V :=
  exponentialBaseComplex (E := E) view ops (JInt.lit .i64 2) t z

/-- Base-ten exponential, with the fixed Julia native Int literal 10.
Source reference: base/complex.jl:783-789. -/
-- Source: base/complex.jl:783-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp10(z::Complex{T}) where T
--     z = float(z)
--     er = exp10(real(z))
--     theta = imag(z) * log(convert(float(T), 10))
--     s, c = sincos(theta)
--     Complex(er * c, er * s)
-- end
-- /Source
def exponential10Complex {m : Type → Type} [Monad m] {E V Ref Tag Target : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : ExponentialBaseOps m V Tag Target)
    (t : Tag) (z : Complex V) : m V :=
  exponentialBaseComplex (E := E) view ops (JInt.lit .i64 10) t z

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Selected operations of the full generic complex logarithm.  V is a
universal runtime-value carrier: float, real, reim, ssqs, conversions, scalar
operations and constructors may change type, mutate, throw, or diverge.
In particular rho and k obtained from ssqs are both untyped source locals.
typeOf is exact Core runtime type metadata, while sameLog is exact dispatch
metadata decoding only selections of this same log(::Complex) body.  The
logOther callee excludes that selected method and is never its replacement.
Source reference: base/complex.jl:653-674. -/
-- Source: base/complex.jl:653-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log(z::Complex)
--     z = float(z)
--     T = typeof(real(z))
--     T1  = convert(T,5)/convert(T,4)
--     T2  = convert(T,3)
--     ln2 = log(convert(T,2))  #0.6931471805599453
--     x, y = reim(z)
--     ρ, k = ssqs(x,y)
--     ax = abs(x)
--     ay = abs(y)
--     if ax < ay
--         θ, β = ax, ay
--     else
--         θ, β = ay, ax
--     end
--     if k==0 && (0.5 < β*β) && (β <= T1 || ρ < T2)
--         ρρ = log1p((β-1)*(β+1)+θ*θ)/2
--     else
--         ρρ = log(ρ)/2 + k*ln2
--     end
--     Complex(ρρ, angle(z))
-- end
-- /Source
structure LogComplexOps (m : Type → Type) (Tag V Other : Type) where
  float : Complex V → m V
  real : V → m V
  typeOf : V → Tag
  convert : Tag → JInt .i64 → m V
  divide : V → V → m V
  sameLog : V → Option (Complex V)
  logOther : V → m V
  reim : V → m V
  ssqs : V → V → m V
  iteration : IndexedIterateOps m V
  abs : V → m V
  less : V → V → m (PredicateValue Other)
  equalZero : V → JInt .i64 → m (PredicateValue Other)
  halfLess : JuliaLean.Float.F64 → V → m (PredicateValue Other)
  lessEqual : V → V → m (PredicateValue Other)
  multiply : V → V → m V
  subtractInt : V → JInt .i64 → m V
  addInt : V → JInt .i64 → m V
  add : V → V → m V
  log1p : V → m V
  divideInt : V → JInt .i64 → m V
  angle : V → m V
  construct : V → V → m V

/-- Native Bool checking at each source control-flow boundary.  A selected
comparison may return any other runtime value, which fails here after its
own effects and before the next comparison or branch body.
Source reference: base/complex.jl:663-671. -/
-- Source: base/complex.jl:663-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if ax < ay
--         θ, β = ax, ay
--     else
--         θ, β = ay, ax
--     end
--     if k==0 && (0.5 < β*β) && (β <= T1 || ρ < T2)
--         ρρ = log1p((β-1)*(β+1)+θ*θ)/2
--     else
--         ρρ = log(ρ)/2 + k*ln2
-- /Source
def logCondition {m : Type → Type} [Monad m] {E Other : Type}
    [MonadExceptOf (Error E) m] : PredicateValue Other → m Bool
  | .boolean truth => pure truth
  | .other _ => throwThe (Error E) (.typeError "log Boolean condition")

/-- The complete lazy near-unit condition.  Native Int zero and literal
Float64 one-half are passed at their actual source sites; the beta product,
<= comparison, and final rho comparison retain the three short circuits.
Source reference: base/complex.jl:668. -/
-- Source: base/complex.jl:668-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if k==0 && (0.5 < β*β) && (β <= T1 || ρ < T2)
-- /Source
def logNearUnit {m : Type → Type} [Monad m] {E Tag V Other : Type}
    [MonadExceptOf (Error E) m] (ops : LogComplexOps m Tag V Other)
    (k beta rho t1 t2 : V) : m Bool := do
  if !(← logCondition (E := E) (← ops.equalZero k (JInt.lit .i64 0))) then
    return false
  let square ← ops.multiply beta beta
  if !(← logCondition (E := E) (← ops.halfLess Fl64.half square)) then
    return false
  if ← logCondition (E := E) (← ops.lessEqual beta t1) then
    return true
  logCondition (E := E) (← ops.less rho t2)

/-- Complete generic complex logarithm.  Conversion/logarithm calls occur
before either arbitrary-result destructuring, and the original floated value
is retained for angle.  The two syntactic local swaps need no iterator.  The
selected recursive log calls at ln2 and rho execute this same body without a
fuel bound, preserving possible divergence and every effectful recursive frame.
Both actual reim and ssqs results use the concrete shared-heap lowering helper.
Source reference: base/complex.jl:653-674. -/
-- Source: base/complex.jl:653-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log(z::Complex)
--     z = float(z)
--     T = typeof(real(z))
--     T1  = convert(T,5)/convert(T,4)
--     T2  = convert(T,3)
--     ln2 = log(convert(T,2))  #0.6931471805599453
--     x, y = reim(z)
--     ρ, k = ssqs(x,y)
--     ax = abs(x)
--     ay = abs(y)
--     if ax < ay
--         θ, β = ax, ay
--     else
--         θ, β = ay, ax
--     end
--     if k==0 && (0.5 < β*β) && (β <= T1 || ρ < T2)
--         ρρ = log1p((β-1)*(β+1)+θ*θ)/2
--     else
--         ρρ = log(ρ)/2 + k*ln2
--     end
--     Complex(ρρ, angle(z))
-- end
-- /Source
def logComplexFull {m : Type → Type} [Monad m] {E Ref Tag V Other : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : LogComplexOps m Tag V Other)
    (original : Complex V) : m V := do
  let logarithm := fun value => match ops.sameLog value with
    | some next => logComplexFull (E := E) view ops next
    | none => ops.logOther value
  let z ← ops.float original
  let real ← ops.real z
  let t := ops.typeOf real
  let five ← ops.convert t (JInt.lit .i64 5)
  let four ← ops.convert t (JInt.lit .i64 4)
  let t1 ← ops.divide five four
  let t2 ← ops.convert t (JInt.lit .i64 3)
  let two ← ops.convert t (JInt.lit .i64 2)
  let ln2 ← logarithm two
  let parts ← ops.reim z
  let (x, y) ← destructureTwo (E := E) view ops.iteration parts
  let scaled ← ops.ssqs x y
  let (rho, k) ← destructureTwo (E := E) view ops.iteration scaled
  let ax ← ops.abs x
  let ay ← ops.abs y
  let ordered ← logCondition (E := E) (← ops.less ax ay)
  let (theta, beta) := if ordered then (ax, ay) else (ay, ax)
  let near ← logNearUnit (E := E) ops k beta rho t1 t2
  let magnitude ← if near then do
      let minus ← ops.subtractInt beta (JInt.lit .i64 1)
      let plus ← ops.addInt beta (JInt.lit .i64 1)
      let product ← ops.multiply minus plus
      let square ← ops.multiply theta theta
      let sum ← ops.add product square
      let logarithm ← ops.log1p sum
      ops.divideInt logarithm (JInt.lit .i64 2)
    else do
      let logarithm ← logarithm rho
      let half ← ops.divideInt logarithm (JInt.lit .i64 2)
      let scaledLog ← ops.multiply k ln2
      ops.add half scaledLog
  let angle ← ops.angle z
  ops.construct magnitude angle
partial_fixpoint

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.base.complex.Models2Group9

open JuliaLean JuliaLean.Float

/-- Fixed Julia Boolean assertion at an if/elseif/ternary guard.  The predicate
partition is actual runtime Bool metadata, not a supplied truth conversion.
Source reference: base/complex.jl:706-722,730-752. -/
-- Source: base/complex.jl:704-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr)
--         Complex(zr, zi==0 ? zi : zr)
--     elseif !isfinite(zi)
--         if zr == Inf
--             Complex(-zr, oftype(zr,NaN))
--         elseif zr == -Inf
--             Complex(-zero(zr), copysign(zero(zi), zi))
--         else
--             Complex(oftype(zr,NaN), oftype(zi,NaN))
--         end
--     else
--         er = exp(zr)
--         if iszero(zi)
--             Complex(er, zi)
--         else
--             s, c = sincos(zi)
--             Complex(er * c, er * s)
--         end
--     end
-- end
-- /Source
def exponentialCondition {m : Type → Type} [Monad m] {E V : Type}
    [MonadExceptOf (Error E) m] (value : PredicateValue V) : m Bool :=
  assertChecked (E := E) "if" (match value with
    | .boolean result => .accepted result
    | .other result => .rejected result)

/-- Full selected scalar operations for the Complex exponential.  V is a
runtime carrier; no intermediate is forced to retain the component's type.
The same classification is actual dispatch metadata for exp(zr): some decodes
this exact fallback's argument, while none uses the genuinely selected other
callee.  No callback replaces this method's own recursive execution.
Source reference: base/complex.jl:704-725. -/
-- Source: base/complex.jl:704-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr)
--         Complex(zr, zi==0 ? zi : zr)
--     elseif !isfinite(zi)
--         if zr == Inf
--             Complex(-zr, oftype(zr,NaN))
--         elseif zr == -Inf
--             Complex(-zero(zr), copysign(zero(zi), zi))
--         else
--             Complex(oftype(zr,NaN), oftype(zi,NaN))
--         end
--     else
--         er = exp(zr)
--         if iszero(zi)
--             Complex(er, zi)
--         else
--             s, c = sincos(zi)
--             Complex(er * c, er * s)
--         end
--     end
-- end
-- /Source
structure ExponentialOps (m : Type → Type) (V : Type) where
  reim : Complex V → m V
  iteration : IndexedIterateOps m V
  isnan : V → m (PredicateValue V)
  equalZero : V → JInt .i64 → m (PredicateValue V)
  isfinite : V → m (PredicateValue V)
  notOther : V → m (PredicateValue V)
  equalFloat : V → F64 → m (PredicateValue V)
  negate : V → m V
  oftype : V → F64 → m V
  zero : V → m V
  copysign : V → V → m V
  same : V → Option (Complex V)
  scalarExp : V → m V
  iszero : V → m (PredicateValue V)
  sincos : V → m V
  multiply : V → V → m V
  construct : V → V → m V

/-- Exact Complex exp control flow with open predicates, real Core destructuring,
native Int zero and Float64 infinity/NaN literals, and explicit own recursion.
Both isfinite Bool negation and each condition assertion are closed operations;
non-Bool ! dispatch runs before its result is asserted as the branch condition.
Source reference: base/complex.jl:704-725. -/
-- Source: base/complex.jl:704-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function exp(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr)
--         Complex(zr, zi==0 ? zi : zr)
--     elseif !isfinite(zi)
--         if zr == Inf
--             Complex(-zr, oftype(zr,NaN))
--         elseif zr == -Inf
--             Complex(-zero(zr), copysign(zero(zi), zi))
--         else
--             Complex(oftype(zr,NaN), oftype(zi,NaN))
--         end
--     else
--         er = exp(zr)
--         if iszero(zi)
--             Complex(er, zi)
--         else
--             s, c = sincos(zi)
--             Complex(er * c, er * s)
--         end
--     end
-- end
-- /Source
def exponentialComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : ExponentialOps m V)
    (z : Complex V) : m V := do
  let pair ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration pair
  if ← exponentialCondition (E := E) (← ops.isnan zr) then
    let im ← if ← exponentialCondition (E := E) (← ops.equalZero zi (JInt.lit .i64 0))
      then pure zi else pure zr
    ops.construct zr im
  else
    let finite ← ops.isfinite zi
    let notFinite ← match finite with
      | .boolean value => pure (.boolean (!value))
      | .other value => ops.notOther value
    if ← exponentialCondition (E := E) notFinite then
      if ← exponentialCondition (E := E) (← ops.equalFloat zr Fl64.inf) then
        let negative ← ops.negate zr
        let nan ← ops.oftype zr F64.nan
        ops.construct negative nan
      else if ← exponentialCondition (E := E) (← ops.equalFloat zr (F64.neg Fl64.inf)) then
        let reZero ← ops.zero zr
        let negative ← ops.negate reZero
        let imZero ← ops.zero zi
        let signed ← ops.copysign imZero zi
        ops.construct negative signed
      else
        let re ← ops.oftype zr F64.nan
        let im ← ops.oftype zi F64.nan
        ops.construct re im
    else
      let er ← match ops.same zr with
        | some next => exponentialComplex (E := E) view ops next
        | none => ops.scalarExp zr
      if ← exponentialCondition (E := E) (← ops.iszero zi) then
        ops.construct er zi
      else
        let pair ← ops.sincos zi
        let (s, c) ← destructureTwo (E := E) view ops.iteration pair
        let re ← ops.multiply er c
        let im ← ops.multiply er s
        ops.construct re im
partial_fixpoint

/-- Full expm1 selected-call interface.  Tf is an arbitrary runtime result of
float(T), not silently a native floating type.  The exact original T and each
recursive Complex component tag are representation metadata.  literalPower is
specialized to Base.literal_pow(Base.^, value, Val{2}()); multiplyThree is the
single selected vararg multiplication *(2, er, square), with its arguments all
evaluated before dispatch (manual/mathematical-operations.md:430-432,503).
Source reference: base/complex.jl:727-755. -/
-- Source: base/complex.jl:727-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expm1(z::Complex{T}) where T<:Real
--     Tf = float(T)
--     zr,zi = reim(z)
--     if isnan(zr)
--         Complex(zr, zi==0 ? zi : zr)
--     elseif !isfinite(zi)
--         if zr == Inf
--             Complex(-zr, oftype(zr,NaN))
--         elseif zr == -Inf
--             Complex(-one(zr), copysign(zero(zi), zi))
--         else
--             Complex(oftype(zr,NaN), oftype(zi,NaN))
--         end
--     else
--         erm1 = expm1(zr)
--         if zi == 0
--             Complex(erm1, zi)
--         else
--             er = erm1+one(erm1)
--             if isfinite(er)
--                 wr = erm1 - 2 * er * (sin(convert(Tf, 0.5) * zi))^2
--                 return Complex(wr, er * sin(zi))
--             else
--                 s, c = sincos(zi)
--                 return Complex(er * c, er * s)
--             end
--         end
--     end
-- end
-- /Source
structure ExponentialMinusOneOps (m : Type → Type) (V Tag : Type) where
  floatType : Tag → m V
  reim : Complex V → m V
  iteration : IndexedIterateOps m V
  isnan : V → m (PredicateValue V)
  equalZero : V → JInt .i64 → m (PredicateValue V)
  isfiniteImag : V → m (PredicateValue V)
  notOther : V → m (PredicateValue V)
  equalFloat : V → F64 → m (PredicateValue V)
  negate : V → m V
  oftype : V → F64 → m V
  one : V → m V
  zero : V → m V
  copysign : V → V → m V
  same : V → Option (Tag × Complex V)
  scalarExpm1 : V → m V
  add : V → V → m V
  isfiniteExp : V → m (PredicateValue V)
  convert : V → F64 → m V
  multiply : V → V → m V
  sine : V → m V
  literalPower : V → SsqsLiteralExponent → m V
  multiplyThree : JInt .i64 → V → V → m V
  subtract : V → V → m V
  sincos : V → m V
  construct : V → V → m V

/-- Compute float(T) before reim, retain every special-value guard and exact
native literal, and recurse explicitly if scalar expm1 selects this method.
The finite-er branch computes the power argument before the ternary product;
no multiplication, conversion, promotion, or type assertion is moved earlier.
Source reference: base/complex.jl:727-755. -/
-- Source: base/complex.jl:727-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function expm1(z::Complex{T}) where T<:Real
--     Tf = float(T)
--     zr,zi = reim(z)
--     if isnan(zr)
--         Complex(zr, zi==0 ? zi : zr)
--     elseif !isfinite(zi)
--         if zr == Inf
--             Complex(-zr, oftype(zr,NaN))
--         elseif zr == -Inf
--             Complex(-one(zr), copysign(zero(zi), zi))
--         else
--             Complex(oftype(zr,NaN), oftype(zi,NaN))
--         end
--     else
--         erm1 = expm1(zr)
--         if zi == 0
--             Complex(erm1, zi)
--         else
--             er = erm1+one(erm1)
--             if isfinite(er)
--                 wr = erm1 - 2 * er * (sin(convert(Tf, 0.5) * zi))^2
--                 return Complex(wr, er * sin(zi))
--             else
--                 s, c = sincos(zi)
--                 return Complex(er * c, er * s)
--             end
--         end
--     end
-- end
-- /Source
def exponentialMinusOneComplex {m : Type → Type} [Monad m] {E Ref V Tag : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    [∀ α, Lean.Order.CCPO (m α)] [monotoneBind : Lean.Order.MonoBind m]
    (view : V → FieldDescriptor Ref V) (ops : ExponentialMinusOneOps m V Tag)
    (t : Tag) (z : Complex V) : m V := do
  let tf ← ops.floatType t
  let pair ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration pair
  if ← exponentialCondition (E := E) (← ops.isnan zr) then
    let im ← if ← exponentialCondition (E := E) (← ops.equalZero zi (JInt.lit .i64 0))
      then pure zi else pure zr
    ops.construct zr im
  else
    let finite ← ops.isfiniteImag zi
    let notFinite ← match finite with
      | .boolean value => pure (.boolean (!value))
      | .other value => ops.notOther value
    if ← exponentialCondition (E := E) notFinite then
      if ← exponentialCondition (E := E) (← ops.equalFloat zr Fl64.inf) then
        let negative ← ops.negate zr
        let nan ← ops.oftype zr F64.nan
        ops.construct negative nan
      else if ← exponentialCondition (E := E) (← ops.equalFloat zr (F64.neg Fl64.inf)) then
        let reOne ← ops.one zr
        let negative ← ops.negate reOne
        let imZero ← ops.zero zi
        let signed ← ops.copysign imZero zi
        ops.construct negative signed
      else
        let re ← ops.oftype zr F64.nan
        let im ← ops.oftype zi F64.nan
        ops.construct re im
    else
      let erm1 ← match ops.same zr with
        | some (nextType, next) => exponentialMinusOneComplex (E := E) view ops nextType next
        | none => ops.scalarExpm1 zr
      if ← exponentialCondition (E := E) (← ops.equalZero zi (JInt.lit .i64 0)) then
        ops.construct erm1 zi
      else
        let one ← ops.one erm1
        let er ← ops.add erm1 one
        if ← exponentialCondition (E := E) (← ops.isfiniteExp er) then
          let half ← ops.convert tf Fl64.half
          let angle ← ops.multiply half zi
          let sine ← ops.sine angle
          let square ← ops.literalPower sine .two
          let correction ← ops.multiplyThree (JInt.lit .i64 2) er square
          let wr ← ops.subtract erm1 correction
          let sine ← ops.sine zi
          let im ← ops.multiply er sine
          ops.construct wr im
        else
          let pair ← ops.sincos zi
          let (s, c) ← destructureTwo (E := E) view ops.iteration pair
          let re ← ops.multiply er c
          let im ← ops.multiply er s
          ops.construct re im
partial_fixpoint

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Runtime values carry their actual typeof tag.  Tag denotes all runtime
types, not only the original component type, and the dependent payload may
contain arbitrary Julia values.  Thus typeof(u) is the concrete first
projection; it is never a selected user callback.
Source reference: base/complex.jl:765. -/
-- Source: base/complex.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         u == 1 ? convert(typeof(u), z) : real(u) <= 0 ? log(u) : log(u)*(z/(u-1))
-- /Source
abbrev Log1pValue {Tag : Type} (Value : Tag → Type) := Sigma Value

/-- Actual selected dispatch in generic log1p.  Original Complex arguments
remain separate from unrestricted returned values and are passed unchanged.
Type-level float may return an arbitrary runtime value.  fromFloat represents
T(literal), while convertPi represents convert(T, Base.MathConstants.pi), with
the actual Irrational{:π} constant fixed; no rounded Float64 substitutes for pi.
Source reference: base/complex.jl:757-773; base/mathconstants.jl:13,59. -/
-- Source: base/complex.jl:757-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log1p(z::Complex{T}) where T
--     zr,zi = reim(z)
--     if isfinite(zr)
--         isinf(zi) && return log(z)
--         # This is based on a well-known trick for log1p of real z,
--         # allegedly due to Kahan, only modified to handle real(u) <= 0
--         # differently to avoid inaccuracy near z==-2 and for correct branch cut
--         u = one(float(T)) + z
--         u == 1 ? convert(typeof(u), z) : real(u) <= 0 ? log(u) : log(u)*(z/(u-1))
--     elseif isnan(zr)
--         Complex(zr, zr)
--     elseif isfinite(zi)
--         Complex(T(Inf), copysign(zr > 0 ? zero(T) : convert(T, pi), zi))
--     else
--         Complex(T(Inf), T(NaN))
--     end
-- end
-- /Source
structure Log1pReopenedOps (m : Type → Type) (A Tag Other : Type) (Value : Tag → Type) where
  reim : Complex A → m (Log1pValue Value)
  iterations : IndexedIterateOps m (Log1pValue Value)
  isfinite : Log1pValue Value → m (PredicateValue Other)
  isinf : Log1pValue Value → m (PredicateValue Other)
  isnan : Log1pValue Value → m (PredicateValue Other)
  logOriginal : Complex A → m (Log1pValue Value)
  floatType : Tag → m (Log1pValue Value)
  one : Log1pValue Value → m (Log1pValue Value)
  addOriginal : Log1pValue Value → Complex A → m (Log1pValue Value)
  equalInt : Log1pValue Value → JInt .i64 → m (PredicateValue Other)
  convertOriginal : Tag → Complex A → m (Log1pValue Value)
  real : Log1pValue Value → m (Log1pValue Value)
  lessEqualInt : Log1pValue Value → JInt .i64 → m (PredicateValue Other)
  log : Log1pValue Value → m (Log1pValue Value)
  subtractInt : Log1pValue Value → JInt .i64 → m (Log1pValue Value)
  divideOriginal : Complex A → Log1pValue Value → m (Log1pValue Value)
  multiply : Log1pValue Value → Log1pValue Value → m (Log1pValue Value)
  construct : Log1pValue Value → Log1pValue Value → m (Log1pValue Value)
  fromFloat : Tag → JuliaLean.Float.F64 → m (Log1pValue Value)
  greaterInt : Log1pValue Value → JInt .i64 → m (PredicateValue Other)
  zeroType : Tag → m (Log1pValue Value)
  convertPi : Tag → m (Log1pValue Value)
  copysign : Log1pValue Value → Log1pValue Value → m (Log1pValue Value)

/-- Fixed Boolean assertion for log1p's source if/elseif, && and ternary
conditions.  A non-Bool selected predicate result fails at that use.
Source reference: base/complex.jl:759-769. -/
-- Source: base/complex.jl:759-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if isfinite(zr)
--         isinf(zi) && return log(z)
--         # This is based on a well-known trick for log1p of real z,
--         # allegedly due to Kahan, only modified to handle real(u) <= 0
--         # differently to avoid inaccuracy near z==-2 and for correct branch cut
--         u = one(float(T)) + z
--         u == 1 ? convert(typeof(u), z) : real(u) <= 0 ? log(u) : log(u)*(z/(u-1))
--     elseif isnan(zr)
--         Complex(zr, zr)
--     elseif isfinite(zi)
--         Complex(T(Inf), copysign(zr > 0 ? zero(T) : convert(T, pi), zi))
-- /Source
def log1pCondition {m : Type → Type} [Monad m] {E Other : Type}
    [MonadExceptOf (Error E) m] : PredicateValue Other → m Bool
  | .boolean value => pure value
  | .other _ => throwThe (Error E) (.typeError "log1p Boolean condition")

/-- Complete generic log1p body.  It checks the original selected reim
components before any float(T) call.  All short-circuit and ternary branches
are explicit.  The corrected-product branch evaluates log(u), then u-1, then
selected z/(u-1), then multiplication.  It never substitutes a particular
complex division algorithm.  Nonfinite branches retain original T calls and
argument evaluation order, including T(Inf) before the zr>0 test.
Source reference: base/complex.jl:757-773. -/
-- Source: base/complex.jl:757-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function log1p(z::Complex{T}) where T
--     zr,zi = reim(z)
--     if isfinite(zr)
--         isinf(zi) && return log(z)
--         # This is based on a well-known trick for log1p of real z,
--         # allegedly due to Kahan, only modified to handle real(u) <= 0
--         # differently to avoid inaccuracy near z==-2 and for correct branch cut
--         u = one(float(T)) + z
--         u == 1 ? convert(typeof(u), z) : real(u) <= 0 ? log(u) : log(u)*(z/(u-1))
--     elseif isnan(zr)
--         Complex(zr, zr)
--     elseif isfinite(zi)
--         Complex(T(Inf), copysign(zr > 0 ? zero(T) : convert(T, pi), zi))
--     else
--         Complex(T(Inf), T(NaN))
--     end
-- end
-- /Source
def log1pComplexReopened {m : Type → Type} [Monad m]
    {E Ref A Tag Other : Type} {Value : Tag → Type}
    [MonadStateOf (FieldHeap Ref (Log1pValue Value)) m]
    [MonadExceptOf (Error E) m]
    (view : Log1pValue Value → FieldDescriptor Ref (Log1pValue Value))
    (ops : Log1pReopenedOps m A Tag Other Value) (t : Tag) (z : Complex A) :
    m (Log1pValue Value) := do
  let components ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iterations components
  if ← log1pCondition (E := E) (← ops.isfinite zr) then
    if ← log1pCondition (E := E) (← ops.isinf zi) then
      return ← ops.logOriginal z
    let floated ← ops.floatType t
    let one ← ops.one floated
    let u ← ops.addOriginal one z
    if ← log1pCondition (E := E) (← ops.equalInt u (JInt.lit .i64 1)) then
      ops.convertOriginal u.1 z
    else
      let real ← ops.real u
      if ← log1pCondition (E := E) (← ops.lessEqualInt real (JInt.lit .i64 0)) then
        ops.log u
      else
        let logarithm ← ops.log u
        let denominator ← ops.subtractInt u (JInt.lit .i64 1)
        let ratio ← ops.divideOriginal z denominator
        ops.multiply logarithm ratio
  else if ← log1pCondition (E := E) (← ops.isnan zr) then
    ops.construct zr zr
  else if ← log1pCondition (E := E) (← ops.isfinite zi) then
    let real ← ops.fromFloat t (JuliaLean.Float.F64.inf false)
    let positive ← log1pCondition (E := E) (← ops.greaterInt zr (JInt.lit .i64 0))
    let magnitude ← if positive then ops.zeroType t else ops.convertPi t
    let imag ← ops.copysign magnitude zi
    ops.construct real imag
  else
    let real ← ops.fromFloat t (JuliaLean.Float.F64.inf false)
    let imag ← ops.fromFloat t JuliaLean.Float.F64.nan
    ops.construct real imag

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Full generic _cpow dispatch.  V is the runtime universe, and T is the
original source type tag.  Both floated operands, Tf, and convert(Int,pReal)
remain untyped values, so custom calls may change type or fail.  isaReal and
complexParameter are pure runtime representation metadata; only the latter
feeds the concrete Complex type-application check.  The pi call fixes the actual
Irrational pi constant, never a rounded Float64 approximation.  Every effectful
callee has a different source function/method from _cpow itself.
Source reference: base/complex.jl:792-881. -/
-- Source: base/complex.jl:792-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _cpow(z::Union{T,Complex{T}}, p::Union{T,Complex{T}}) where T
--     z = float(z)
--     p = float(p)
--     Tf = float(T)
--     if isreal(p)
--         pᵣ = real(p)
--         if isinteger(pᵣ) && abs(pᵣ) < typemax(Int32)
--             # |p| < typemax(Int32) serves two purposes: it prevents overflow
--             # when converting p to Int, and it also turns out to be roughly
--             # the crossover point for exp(p*log(z)) or similar to be faster.
--             if iszero(pᵣ) # fix signs of imaginary part for z^0
--                 zer = flipsign(copysign(zero(Tf),pᵣ), imag(z))
--                 return Complex(one(Tf), zer)
--             end
--             ip = convert(Int, pᵣ)
--             if isreal(z)
--                 zᵣ = real(z)
--                 if ip < 0
--                     iszero(z) && return Complex(Tf(NaN),Tf(NaN))
--                     re = power_by_squaring(inv(zᵣ), -ip)
--                     im = -imag(z)
--                 else
--                     re = power_by_squaring(zᵣ, ip)
--                     im = imag(z)
--                 end
--                 # slightly tricky to get the correct sign of zero imag. part
--                 return Complex(re, ifelse(iseven(ip) & signbit(zᵣ), -im, im))
--             else
--                 return ip < 0 ? power_by_squaring(inv(z), -ip) : power_by_squaring(z, ip)
--             end
--         elseif isreal(z)
--             # (note: if both z and p are complex with ±0.0 imaginary parts,
--             #  the sign of the ±0.0 imaginary part of the result is ambiguous)
--             if iszero(real(z))
--                 return pᵣ > 0 ? complex(z) : Complex(Tf(NaN),Tf(NaN)) # 0 or NaN+NaN*im
--             elseif real(z) > 0
--                 return Complex(real(z)^pᵣ, z isa Real ? ifelse(real(z) < 1, -imag(p), imag(p)) : flipsign(imag(z), pᵣ))
--             else
--                 zᵣ = real(z)
--                 rᵖ = (-zᵣ)^pᵣ
--                 if isfinite(pᵣ)
--                     # figuring out the sign of 0.0 when p is a complex number
--                     # with zero imaginary part and integer/2 real part could be
--                     # improved here, but it's not clear if it's worth it…
--                     return rᵖ * complex(cospi(pᵣ), flipsign(sinpi(pᵣ),imag(z)))
--                 else
--                     iszero(rᵖ) && return zero(Complex{Tf}) # no way to get correct signs of 0.0
--                     return Complex(Tf(NaN),Tf(NaN)) # non-finite phase angle or NaN input
--                 end
--             end
--         else
--             rᵖ = abs(z)^pᵣ
--             ϕ = pᵣ*angle(z)
--         end
--     elseif isreal(z)
--         iszero(z) && return real(p) > 0 ? complex(z) : Complex(Tf(NaN),Tf(NaN)) # 0 or NaN+NaN*im
--         zᵣ = real(z)
--         pᵣ, pᵢ = reim(p)
--         if zᵣ > 0
--             rᵖ = zᵣ^pᵣ
--             ϕ = pᵢ*log(zᵣ)
--         else
--             r = -zᵣ
--             θ = copysign(Tf(π),imag(z))
--             logr = log(r)
--             re_log, im_phase = pᵣ*logr, pᵢ*θ
--             lim = log(floatmax(Tf)) - one(Tf)
--             rᵖ = (abs(re_log) < lim && abs(im_phase) < lim) ?
--                 r^pᵣ * exp(-im_phase) : exp(re_log - im_phase)
--             ϕ = pᵣ*θ + pᵢ*logr
--         end
--     else
--         pᵣ, pᵢ = reim(p)
--         r = abs(z)
--         θ = angle(z)
--         logr = log(r)
--         re_log, im_phase = pᵣ*logr, pᵢ*θ
--         lim = log(floatmax(Tf)) - one(Tf)
--         rᵖ = (abs(re_log) < lim && abs(im_phase) < lim) ?
--             r^pᵣ * exp(-im_phase) : exp(re_log - im_phase)
--         ϕ = pᵣ*θ + pᵢ*logr
--     end
-- 
--     if isfinite(ϕ)
--         return rᵖ * cis(ϕ)
--     else
--         iszero(rᵖ) && return zero(Complex{Tf}) # no way to get correct signs of 0.0
--         return Complex(Tf(NaN),Tf(NaN)) # non-finite phase angle or NaN input
--     end
-- end
-- /Source
structure CPowFullOps (m : Type → Type) (Tag V Other Rejected : Type) where
  floatValue : V → m V
  floatType : Tag → m V
  isreal : V → m (PredicateValue Other)
  real : V → m V
  imag : V → m V
  isinteger : V → m (PredicateValue Other)
  abs : V → m V
  lessInt32 : V → JInt .i32 → m (PredicateValue Other)
  iszero : V → m (PredicateValue Other)
  zero : V → m V
  one : V → m V
  copysign : V → V → m V
  flipsign : V → V → m V
  construct : V → V → m V
  convertInt : V → m V
  lessInt : V → JInt .i64 → m (PredicateValue Other)
  greaterInt : V → JInt .i64 → m (PredicateValue Other)
  fromFloat : V → JuliaLean.Float.F64 → m V
  inverse : V → m V
  negate : V → m V
  powerBySquaring : V → V → m V
  iseven : V → m (PredicateValue Other)
  signbit : V → m (PredicateValue Other)
  andOther : PredicateValue Other → PredicateValue Other → m (PredicateValue Other)
  ifelse : PredicateValue Other → V → V → m V
  publicComplexOne : V → m V
  publicComplexTwo : V → V → m V
  power : V → V → m V
  isaReal : V → Bool
  cospi : V → m V
  sinpi : V → m V
  isfinite : V → m (PredicateValue Other)
  complexParameter : V → TypeParameter Tag Rejected
  zeroComplexType : ComplexTy Tag → m V
  angle : V → m V
  reim : V → m V
  iterations : IndexedIterateOps m V
  callPi : V → m V
  log : V → m V
  floatmax : V → m V
  subtract : V → V → m V
  less : V → V → m (PredicateValue Other)
  multiply : V → V → m V
  exp : V → m V
  add : V → V → m V
  cis : V → m V

/-- Fixed native Boolean use at source if, && and ternary boundaries.
Ordinary ifelse remains a selected call because its branch types are unfixed;
its arguments are evaluated eagerly and no caller Bool assertion is invented.
Source reference: base/complex.jl:796-880. -/
-- Source: base/complex.jl:796-800 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if isreal(p)
--         pᵣ = real(p)
--         if isinteger(pᵣ) && abs(pᵣ) < typemax(Int32)
--             # |p| < typemax(Int32) serves two purposes: it prevents overflow
--             # when converting p to Int, and it also turns out to be roughly
-- /Source
def cpowCondition {m : Type → Type} [Monad m] {E Other : Type}
    [MonadExceptOf (Error E) m] : PredicateValue Other → m Bool
  | .boolean value => pure value
  | .other _ => throwThe (Error E) (.typeError "_cpow Boolean condition")

/-- Both T(NaN) calls remain separate and ordered before Complex dispatch.
Source reference: base/complex.jl:810,826,839,847,879. -/
-- Source: base/complex.jl:879-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         return Complex(Tf(NaN),Tf(NaN)) # non-finite phase angle or NaN input
-- /Source
def cpowNaN {m : Type → Type} [Monad m] {Tag V Other Rejected : Type}
    (ops : CPowFullOps m Tag V Other Rejected) (tf : V) : m V := do
  let real ← ops.fromFloat tf JuliaLean.Float.F64.nan
  let imag ← ops.fromFloat tf JuliaLean.Float.F64.nan
  ops.construct real imag

/-- The two source polar branches have this identical ordered magnitude
calculation.  The second abs/limit comparison is short-circuited; every scalar
result and type-level operation remains arbitrary and effectful.
Source reference: base/complex.jl:858-860,869-871. -/
-- Source: base/complex.jl:869-871 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         lim = log(floatmax(Tf)) - one(Tf)
--         rᵖ = (abs(re_log) < lim && abs(im_phase) < lim) ?
--             r^pᵣ * exp(-im_phase) : exp(re_log - im_phase)
-- /Source
def cpowPolarMagnitude {m : Type → Type} [Monad m] {E Tag V Other Rejected : Type}
    [MonadExceptOf (Error E) m] (ops : CPowFullOps m Tag V Other Rejected)
    (tf radius realExponent reLog imPhase : V) : m V := do
  let maximum ← ops.floatmax tf
  let logarithm ← ops.log maximum
  let one ← ops.one tf
  let limit ← ops.subtract logarithm one
  let absReal ← ops.abs reLog
  let first ← cpowCondition (E := E) (← ops.less absReal limit)
  let bounded ← if first then do
      let absImag ← ops.abs imPhase
      cpowCondition (E := E) (← ops.less absImag limit)
    else pure false
  if bounded then
    let power ← ops.power radius realExponent
    let negative ← ops.negate imPhase
    let exponential ← ops.exp negative
    ops.multiply power exponential
  else
    let difference ← ops.subtract reLog imPhase
    ops.exp difference

/-- Eager native Bool & when both operands are Bool; otherwise selected
& retains its actual dispatch.  This does not make ifelse lazy.
Source reference: base/complex.jl:818. -/
-- Source: base/complex.jl:818-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 return Complex(re, ifelse(iseven(ip) & signbit(zᵣ), -im, im))
-- /Source
def cpowAnd {m : Type → Type} [Monad m] {Tag V Other Rejected : Type}
    (ops : CPowFullOps m Tag V Other Rejected)
    (left right : PredicateValue Other) : m (PredicateValue Other) :=
  match left, right with
  | .boolean a, .boolean b => pure (.boolean (a && b))
  | _, _ => ops.andOther left right

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Selected targets for the generic Complex sine/cosine bodies.  V is a
universal runtime carrier; float(T), reim, sincos, scalar calls and constructors
may return arbitrary actual values.  The actual returned F is passed as the
call target at every F(...) expression.  Only native Bool negation and source
literal values are closed.  Neither body contains a direct sin or cos call.
Source reference: base/complex.jl:905-940. -/
-- Source: base/complex.jl:905-940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sin(z::Complex{T}) where T
--     F = float(T)
--     zr, zi = reim(z)
--     if zr == 0
--         Complex(F(zr), sinh(zi))
--     elseif !isfinite(zr)
--         if zi == 0 || isinf(zi)
--             Complex(F(NaN), F(zi))
--         else
--             Complex(F(NaN), F(NaN))
--         end
--     else
--         s, c = sincos(zr)
--         Complex(s * cosh(zi), c * sinh(zi))
--     end
-- end
-- 
-- 
-- function cos(z::Complex{T}) where T
--     F = float(T)
--     zr, zi = reim(z)
--     if zr == 0
--         Complex(cosh(zi), isnan(zi) ? F(zr) : -flipsign(F(zr),zi))
--     elseif !isfinite(zr)
--         if zi == 0
--             Complex(F(NaN), isnan(zr) ? zero(F) : -flipsign(F(zi),zr))
--         elseif isinf(zi)
--             Complex(F(Inf), F(NaN))
--         else
--             Complex(F(NaN), F(NaN))
--         end
--     else
--         s, c = sincos(zr)
--         Complex(c * cosh(zi), -s * sinh(zi))
--     end
-- end
-- /Source
structure TrigReopenedOps (m : Type → Type) (A Tag V Other : Type) where
  floatType : Tag → m V
  reim : Complex A → m V
  iterations : IndexedIterateOps m V
  equalZero : V → JInt .i64 → m (PredicateValue Other)
  isfinite : V → m (PredicateValue Other)
  notOther : Other → m (PredicateValue Other)
  isinf : V → m (PredicateValue Other)
  isnan : V → m (PredicateValue Other)
  callFloat : V → V → m V
  callFloatLiteral : V → JuliaLean.Float.F64 → m V
  zero : V → m V
  sinh : V → m V
  cosh : V → m V
  sincos : V → m V
  multiply : V → V → m V
  flipsign : V → V → m V
  negate : V → m V
  construct : V → V → m V

/-- Fixed condition assertion after the actual selected predicate result.
Source reference: base/complex.jl:908-910,926-932. -/
-- Source: base/complex.jl:908-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if zr == 0
--         Complex(F(zr), sinh(zi))
--     elseif !isfinite(zr)
-- /Source
def trigReopenedCondition {m : Type → Type} [Monad m] {E Other : Type}
    [MonadExceptOf (Error E) m] : PredicateValue Other → m Bool
  | .boolean value => pure value
  | .other _ => throwThe (Error E) (.typeError "complex sin/cos Boolean condition")

/-- ! is native for a Bool result; any other result retains selected !
dispatch before the source condition assertion.
Source reference: base/complex.jl:910,928. -/
-- Source: base/complex.jl:910-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     elseif !isfinite(zr)
-- /Source
def trigReopenedNot {m : Type → Type} [Monad m] {A Tag V Other : Type}
    (ops : TrigReopenedOps m A Tag V Other) : PredicateValue Other → m (PredicateValue Other)
  | .boolean value => pure (.boolean (!value))
  | .other value => ops.notOther value

/-- Complete generic sine.  float(T) precedes reim, but the components
are not preconverted.  Short-circuit checks inspect the actual original
components, and F is called only on the source branches.  The finite branch
unpacks the actual sincos result and evaluates each hyperbolic call and product
left to right before invoking the Complex constructor.
Source reference: base/complex.jl:905-920. -/
-- Source: base/complex.jl:905-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sin(z::Complex{T}) where T
--     F = float(T)
--     zr, zi = reim(z)
--     if zr == 0
--         Complex(F(zr), sinh(zi))
--     elseif !isfinite(zr)
--         if zi == 0 || isinf(zi)
--             Complex(F(NaN), F(zi))
--         else
--             Complex(F(NaN), F(NaN))
--         end
--     else
--         s, c = sincos(zr)
--         Complex(s * cosh(zi), c * sinh(zi))
--     end
-- end
-- /Source
def sinComplexReopened {m : Type → Type} [Monad m]
    {E Ref A Tag V Other : Type} [MonadStateOf (FieldHeap Ref V) m]
    [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : TrigReopenedOps m A Tag V Other)
    (t : Tag) (z : Complex A) : m V := do
  let floated ← ops.floatType t
  let components ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iterations components
  if ← trigReopenedCondition (E := E) (← ops.equalZero zr (JInt.lit .i64 0)) then
    let real ← ops.callFloat floated zr
    let imag ← ops.sinh zi
    ops.construct real imag
  else if ← trigReopenedCondition (E := E)
      (← trigReopenedNot ops (← ops.isfinite zr)) then
    let exceptional ← if ← trigReopenedCondition (E := E)
        (← ops.equalZero zi (JInt.lit .i64 0)) then pure true
      else trigReopenedCondition (E := E) (← ops.isinf zi)
    if exceptional then
      let real ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      let imag ← ops.callFloat floated zi
      ops.construct real imag
    else
      let real ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      let imag ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      ops.construct real imag
  else
    let result ← ops.sincos zr
    let (s, c) ← destructureTwo (E := E) view ops.iterations result
    let hyperbolicCosine ← ops.cosh zi
    let real ← ops.multiply s hyperbolicCosine
    let hyperbolicSine ← ops.sinh zi
    let imag ← ops.multiply c hyperbolicSine
    ops.construct real imag

/-- Complete generic cosine, including the source's eager constructor-argument
order around nested ternaries.  In the finite branch unary -s executes before
sinh(zi), and only then is their product evaluated; no reassociation to a
negated product is made.  Repeated F(NaN) calls remain distinct and errorful.
Source reference: base/complex.jl:923-940. -/
-- Source: base/complex.jl:923-940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function cos(z::Complex{T}) where T
--     F = float(T)
--     zr, zi = reim(z)
--     if zr == 0
--         Complex(cosh(zi), isnan(zi) ? F(zr) : -flipsign(F(zr),zi))
--     elseif !isfinite(zr)
--         if zi == 0
--             Complex(F(NaN), isnan(zr) ? zero(F) : -flipsign(F(zi),zr))
--         elseif isinf(zi)
--             Complex(F(Inf), F(NaN))
--         else
--             Complex(F(NaN), F(NaN))
--         end
--     else
--         s, c = sincos(zr)
--         Complex(c * cosh(zi), -s * sinh(zi))
--     end
-- end
-- /Source
def cosComplexReopened {m : Type → Type} [Monad m]
    {E Ref A Tag V Other : Type} [MonadStateOf (FieldHeap Ref V) m]
    [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : TrigReopenedOps m A Tag V Other)
    (t : Tag) (z : Complex A) : m V := do
  let floated ← ops.floatType t
  let components ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iterations components
  if ← trigReopenedCondition (E := E) (← ops.equalZero zr (JInt.lit .i64 0)) then
    let real ← ops.cosh zi
    let imag ← if ← trigReopenedCondition (E := E) (← ops.isnan zi) then
        ops.callFloat floated zr
      else do
        let converted ← ops.callFloat floated zr
        let signed ← ops.flipsign converted zi
        ops.negate signed
    ops.construct real imag
  else if ← trigReopenedCondition (E := E)
      (← trigReopenedNot ops (← ops.isfinite zr)) then
    if ← trigReopenedCondition (E := E) (← ops.equalZero zi (JInt.lit .i64 0)) then
      let real ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      let imag ← if ← trigReopenedCondition (E := E) (← ops.isnan zr) then
          ops.zero floated
        else do
          let converted ← ops.callFloat floated zi
          let signed ← ops.flipsign converted zr
          ops.negate signed
      ops.construct real imag
    else if ← trigReopenedCondition (E := E) (← ops.isinf zi) then
      let real ← ops.callFloatLiteral floated (JuliaLean.Float.F64.inf false)
      let imag ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      ops.construct real imag
    else
      let real ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      let imag ← ops.callFloatLiteral floated JuliaLean.Float.F64.nan
      ops.construct real imag
  else
    let result ← ops.sincos zr
    let (s, c) ← destructureTwo (E := E) view ops.iterations result
    let hyperbolicCosine ← ops.cosh zi
    let real ← ops.multiply c hyperbolicCosine
    let negativeS ← ops.negate s
    let hyperbolicSine ← ops.sinh zi
    let imag ← ops.multiply negativeS hyperbolicSine
    ops.construct real imag

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Each constructor denotes one actual selected callee at the corresponding
source call.  Original Complex arguments and arbitrary returned runtime values
are kept distinct.  oftypePi fixes the actual Irrational{:π} argument; the
Float64 and native-Int arguments are explicit values.  No constructor denotes
the asin caller or its branch composition.
Source reference: base/complex.jl:949-961. -/
-- Source: base/complex.jl:949-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function asin(z::Complex)
--     zr, zi = reim(z)
--     if isinf(zr) && isinf(zi)
--         return Complex(copysign(oftype(zr,pi)/4, zr),zi)
--     elseif isnan(zi) && isinf(zr)
--         return Complex(zi, oftype(zr, Inf))
--     end
--     ξ = zr == 0       ? zr :
--         !isfinite(zr) ? oftype(zr,pi)/2 * sign(zr) :
--         atan(zr, real(sqrt(1-z)*sqrt(1+z)))
--     η = asinh(copysign(imag(sqrt(conj(1-z))*sqrt(1+z)), imag(z)))
--     Complex(ξ,η)
-- end
-- /Source
inductive ArcSineCall (A V : Type) where
  | reim (z : Complex A)
  | indexedFirst (value : V) (index : JInt .i64)
  | indexedNext (value : V) (index : JInt .i64) (state : V)
  | isinf (value : V)
  | isnan (value : V)
  | isfinite (value : V)
  | equalInt (value : V) (literal : JInt .i64)
  | notOther (value : V)
  | oftypePi (value : V)
  | oftypeFloat (value : V) (literal : JuliaLean.Float.F64)
  | divideInt (value : V) (literal : JInt .i64)
  | sign (value : V)
  | copysign (magnitude sign : V)
  | multiply (left right : V)
  | subtractOriginal (literal : JInt .i64) (z : Complex A)
  | addOriginal (literal : JInt .i64) (z : Complex A)
  | squareRoot (value : V)
  | conjugate (value : V)
  | real (value : V)
  | imag (value : V)
  | imagOriginal (z : Complex A)
  | atan (y x : V)
  | asinh (value : V)
  | construct (real imag : V)

/-- A selected-call interface indexed by actual function identity and complete
arguments.  boolValue is the pure runtime Bool representation view, not a
selected predicate.  V may be a tagged universe containing every Julia result
type, including malformed iterator results and type-changing custom arithmetic.
Source reference: base/complex.jl:949-961. -/
-- Source: base/complex.jl:949-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function asin(z::Complex)
--     zr, zi = reim(z)
--     if isinf(zr) && isinf(zi)
--         return Complex(copysign(oftype(zr,pi)/4, zr),zi)
--     elseif isnan(zi) && isinf(zr)
--         return Complex(zi, oftype(zr, Inf))
--     end
--     ξ = zr == 0       ? zr :
--         !isfinite(zr) ? oftype(zr,pi)/2 * sign(zr) :
--         atan(zr, real(sqrt(1-z)*sqrt(1+z)))
--     η = asinh(copysign(imag(sqrt(conj(1-z))*sqrt(1+z)), imag(z)))
--     Complex(ξ,η)
-- end
-- /Source
structure ArcSineOps (m : Type → Type) (A V : Type) where
  selected : ArcSineCall A V → m V
  boolValue : V → Option Bool

/-- Native Boolean assertion at the caller's if, elseif, short-circuit or
ternary use.  No conversion is inserted for a non-Bool result.
Source reference: base/complex.jl:951-957. -/
-- Source: base/complex.jl:951-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if isinf(zr) && isinf(zi)
--         return Complex(copysign(oftype(zr,pi)/4, zr),zi)
--     elseif isnan(zi) && isinf(zr)
--         return Complex(zi, oftype(zr, Inf))
--     end
--     ξ = zr == 0       ? zr :
--         !isfinite(zr) ? oftype(zr,pi)/2 * sign(zr) :
-- /Source
def arcSineCondition {m : Type → Type} [Monad m] {E A V : Type}
    [MonadExceptOf (Error E) m] (ops : ArcSineOps m A V) (value : V) : m Bool :=
  match ops.boolValue value with
  | some result => pure result
  | none => throwThe (Error E) (.typeError "if")

/-- Complete asin source body with both short-circuit early-return guards,
the three real-part branches, all repeated 1±z computations, and the final
imaginary-part computation in source order.  Native unpacking uses the shared
heap model; every other source call is selected on an unfixed runtime type.
Native Bool negation is closed; non-Bool ! retains selected dispatch followed
by the actual caller assertion.  No asin call is replaced by a callback.
Source reference: base/complex.jl:949-961. -/
-- Source: base/complex.jl:949-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function asin(z::Complex)
--     zr, zi = reim(z)
--     if isinf(zr) && isinf(zi)
--         return Complex(copysign(oftype(zr,pi)/4, zr),zi)
--     elseif isnan(zi) && isinf(zr)
--         return Complex(zi, oftype(zr, Inf))
--     end
--     ξ = zr == 0       ? zr :
--         !isfinite(zr) ? oftype(zr,pi)/2 * sign(zr) :
--         atan(zr, real(sqrt(1-z)*sqrt(1+z)))
--     η = asinh(copysign(imag(sqrt(conj(1-z))*sqrt(1+z)), imag(z)))
--     Complex(ξ,η)
-- end
-- /Source
def arcSineComplex {m : Type → Type} [Monad m] {E Ref A V : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    (view : V → FieldDescriptor Ref V) (ops : ArcSineOps m A V) (z : Complex A) : m V := do
  let parts ← ops.selected (.reim z)
  let iterations : IndexedIterateOps m V :=
    { first := fun value index => ops.selected (.indexedFirst value index)
      next := fun value index state => ops.selected (.indexedNext value index state) }
  let (zr, zi) ← destructureTwo (E := E) view iterations parts
  let realInfinite ← arcSineCondition (E := E) ops (← ops.selected (.isinf zr))
  let bothInfinite ← if realInfinite then
      arcSineCondition (E := E) ops (← ops.selected (.isinf zi))
    else pure false
  if bothInfinite then
    let pi ← ops.selected (.oftypePi zr)
    let quarter ← ops.selected (.divideInt pi (JInt.lit .i64 4))
    let real ← ops.selected (.copysign quarter zr)
    return ← ops.selected (.construct real zi)
  let imaginaryNaN ← arcSineCondition (E := E) ops (← ops.selected (.isnan zi))
  let nonfiniteNaN ← if imaginaryNaN then
      arcSineCondition (E := E) ops (← ops.selected (.isinf zr))
    else pure false
  if nonfiniteNaN then
    let imag ← ops.selected (.oftypeFloat zr (JuliaLean.Float.F64.inf false))
    return ← ops.selected (.construct zi imag)
  let realZero ← arcSineCondition (E := E) ops
    (← ops.selected (.equalInt zr (JInt.lit .i64 0)))
  let xi ← if realZero then pure zr else do
    let finite ← ops.selected (.isfinite zr)
    let nonfinite ← match ops.boolValue finite with
      | some boolean => pure (!boolean)
      | none => arcSineCondition (E := E) ops (← ops.selected (.notOther finite))
    if nonfinite then
      let pi ← ops.selected (.oftypePi zr)
      let half ← ops.selected (.divideInt pi (JInt.lit .i64 2))
      let sign ← ops.selected (.sign zr)
      ops.selected (.multiply half sign)
    else
      let difference ← ops.selected (.subtractOriginal (JInt.lit .i64 1) z)
      let firstRoot ← ops.selected (.squareRoot difference)
      let sum ← ops.selected (.addOriginal (JInt.lit .i64 1) z)
      let secondRoot ← ops.selected (.squareRoot sum)
      let product ← ops.selected (.multiply firstRoot secondRoot)
      let real ← ops.selected (.real product)
      ops.selected (.atan zr real)
  let difference ← ops.selected (.subtractOriginal (JInt.lit .i64 1) z)
  let conjugate ← ops.selected (.conjugate difference)
  let firstRoot ← ops.selected (.squareRoot conjugate)
  let sum ← ops.selected (.addOriginal (JInt.lit .i64 1) z)
  let secondRoot ← ops.selected (.squareRoot sum)
  let product ← ops.selected (.multiply firstRoot secondRoot)
  let imaginary ← ops.selected (.imag product)
  let originalImaginary ← ops.selected (.imagOriginal z)
  let signed ← ops.selected (.copysign imaginary originalImaginary)
  let eta ← ops.selected (.asinh signed)
  ops.selected (.construct xi eta)

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean JuliaLean.Float

/-- Concrete Core identity when one operand is a fixed Float64 value.  The
asFloat64 view decodes the actual native type and bits: none means a different
runtime type, including Float32 even when its numerical value is signed zero.
This is representation metadata, not a callback computing equality.  Native
Float64 identity is bit identity after the exact-type check; no conversion runs.
Source reference: base/complex.jl:975,977; base/boot.jl:272;
src/julia.h:2083-2102; src/builtins.c:374-385. -/
-- Source: src/julia.h:2083-2102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE int jl_egal__unboxed_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, uintptr_t dtag) JL_NOTSAFEPOINT
-- {
--     if (dtag < jl_max_tags << 4) {
--         if (dtag == jl_symbol_tag << 4 || dtag == jl_bool_tag << 4 || dtag == jl_nothing_tag << 4)
--             return 0;
--     }
--     else if (((jl_datatype_t*)dtag)->name->mutabl)
--         return 0;
--     return jl_egal__bitstag(a, b, dtag);
-- }
-- 
-- STATIC_INLINE int jl_egal_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED) JL_NOTSAFEPOINT
-- {
--     if (a == b)
--         return 1;
--     uintptr_t dtag = jl_typetagof(a);
--     if (dtag != jl_typetagof(b))
--         return 0;
--     return jl_egal__unboxed_(a, b, dtag);
-- }
-- /Source
-- Source: src/builtins.c:374-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inline int jl_egal__bits(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     size_t sz = jl_datatype_size(dt);
--     if (sz == 0)
--         return 1;
--     size_t nf = jl_datatype_nfields(dt);
--     if (nf == 0)
--         return dt->layout->flags.haspadding ? primitive_bits_equal(a, b, dt) : bits_equal(a, b, sz);
--     if (!dt->layout->flags.haspadding && dt->layout->flags.isbitsegal)
--         return bits_equal(a, b, sz);
--     return compare_fields(a, b, dt);
-- }
-- /Source
-- Source: base/boot.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- primitive type Float64 <: AbstractFloat 64 end
-- /Source
def identicalFloat64 {V : Type} (asFloat64 : V → Option F64)
    (value : V) (literal : F64) : Bool :=
  match asFloat64 value with
  | none => false
  | some actual => decide (actual.toBits = literal.toBits)

/-- Selected callees of acos after float(z), with every intermediate retained
in the runtime carrier.  oftypePi fixes the actual Irrational{:π} second
argument; it does not supply an approximate Float64 π.  asFloat64 is exact
runtime representation decoding for the two closed identity tests.
Source reference: base/complex.jl:963-984. -/
-- Source: base/complex.jl:963-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function acos(z::Complex)
--     z = float(z)
--     zr, zi = reim(z)
--     if isnan(zr)
--         if isinf(zi) return Complex(zr, -zi)
--         else         return Complex(zr, zr) end
--     elseif isnan(zi)
--         if isinf(zr) return Complex(zi, abs(zr))
--         elseif zr==0 return Complex(oftype(zr,pi)/2, zi)
--         else         return Complex(zi, zi) end
--     elseif zr==zi==0
--         return Complex(oftype(zr,pi)/2, -zi)
--     elseif zr==Inf && zi===0.0
--         return Complex(zi, -zr)
--     elseif zr==-Inf && zi===-0.0
--         return Complex(oftype(zi,pi), -zr)
--     end
--     ξ = 2*atan(real(sqrt(1-z)), real(sqrt(1+z)))
--     η = asinh(imag(sqrt(conj(1+z))*sqrt(1-z)))
--     if isinf(zr) && isinf(zi) ξ -= oftype(η,pi)/4 * sign(zr) end
--     Complex(ξ,η)
-- end
-- /Source
structure ArccosineOps (m : Type → Type) (V : Type) where
  floatValue : Complex V → m V
  reim : V → m V
  iteration : IndexedIterateOps m V
  isnan : V → m (PredicateValue V)
  isinf : V → m (PredicateValue V)
  equalSame : V → V → m (PredicateValue V)
  equalZero : V → JInt .i64 → m (PredicateValue V)
  equalFloat : V → F64 → m (PredicateValue V)
  asFloat64 : V → Option F64
  negate : V → m V
  abs : V → m V
  oftypePi : V → m V
  divideInt : V → JInt .i64 → m V
  subtractFromOne : JInt .i64 → V → m V
  addToOne : JInt .i64 → V → m V
  sqrt : V → m V
  real : V → m V
  atan : V → V → m V
  multiplyInt : JInt .i64 → V → m V
  conjugate : V → m V
  multiply : V → V → m V
  imag : V → m V
  inverseHyperbolicSine : V → m V
  sign : V → m V
  subtract : V → V → m V
  construct : V → V → m V

/-- Full generic acos with actual float/reim dispatch and closed Float64
identity.  The scalar chain zr==zi==0 lowers to short-circuit &&; its operands
are already local values, so the equality calls retain left-to-right order.
Both square roots of 1-z and both computations of 1+z are repeated exactly at
the source sites, and the second 1+z is conjugated before its square root.
Source reference: base/complex.jl:963-984; src/julia-syntax.scm:28-77. -/
-- Source: base/complex.jl:963-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function acos(z::Complex)
--     z = float(z)
--     zr, zi = reim(z)
--     if isnan(zr)
--         if isinf(zi) return Complex(zr, -zi)
--         else         return Complex(zr, zr) end
--     elseif isnan(zi)
--         if isinf(zr) return Complex(zi, abs(zr))
--         elseif zr==0 return Complex(oftype(zr,pi)/2, zi)
--         else         return Complex(zi, zi) end
--     elseif zr==zi==0
--         return Complex(oftype(zr,pi)/2, -zi)
--     elseif zr==Inf && zi===0.0
--         return Complex(zi, -zr)
--     elseif zr==-Inf && zi===-0.0
--         return Complex(oftype(zi,pi), -zr)
--     end
--     ξ = 2*atan(real(sqrt(1-z)), real(sqrt(1+z)))
--     η = asinh(imag(sqrt(conj(1+z))*sqrt(1-z)))
--     if isinf(zr) && isinf(zi) ξ -= oftype(η,pi)/4 * sign(zr) end
--     Complex(ξ,η)
-- end
-- /Source
def arccosineComplex {m : Type → Type} [Monad m] {E Ref V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : ArccosineOps m V)
    (original : Complex V) : m V := do
  let z ← ops.floatValue original
  let pair ← ops.reim z
  let (zr, zi) ← destructureTwo (E := E) view ops.iteration pair
  if ← exponentialCondition (E := E) (← ops.isnan zr) then
    if ← exponentialCondition (E := E) (← ops.isinf zi) then
      let negative ← ops.negate zi
      return ← ops.construct zr negative
    else return ← ops.construct zr zr
  else if ← exponentialCondition (E := E) (← ops.isnan zi) then
    if ← exponentialCondition (E := E) (← ops.isinf zr) then
      let absolute ← ops.abs zr
      return ← ops.construct zi absolute
    else if ← exponentialCondition (E := E) (← ops.equalZero zr (JInt.lit .i64 0)) then
      let pi ← ops.oftypePi zr
      let halfPi ← ops.divideInt pi (JInt.lit .i64 2)
      return ← ops.construct halfPi zi
    else return ← ops.construct zi zi
  let same ← exponentialCondition (E := E) (← ops.equalSame zr zi)
  let zero ← if same then exponentialCondition (E := E) (← ops.equalZero zi (JInt.lit .i64 0))
    else pure false
  if zero then
    let pi ← ops.oftypePi zr
    let halfPi ← ops.divideInt pi (JInt.lit .i64 2)
    let negative ← ops.negate zi
    return ← ops.construct halfPi negative
  let positiveInfinite ← exponentialCondition (E := E) (← ops.equalFloat zr Fl64.inf)
  if positiveInfinite && identicalFloat64 ops.asFloat64 zi Fl64.pzero then
    let negative ← ops.negate zr
    return ← ops.construct zi negative
  let negativeInfinite ← exponentialCondition (E := E) (← ops.equalFloat zr (F64.neg Fl64.inf))
  if negativeInfinite && identicalFloat64 ops.asFloat64 zi (F64.neg Fl64.pzero) then
    let pi ← ops.oftypePi zi
    let negative ← ops.negate zr
    return ← ops.construct pi negative
  let firstDifference ← ops.subtractFromOne (JInt.lit .i64 1) z
  let firstRoot ← ops.sqrt firstDifference
  let firstReal ← ops.real firstRoot
  let firstSum ← ops.addToOne (JInt.lit .i64 1) z
  let secondRoot ← ops.sqrt firstSum
  let secondReal ← ops.real secondRoot
  let argument ← ops.atan firstReal secondReal
  let xi ← ops.multiplyInt (JInt.lit .i64 2) argument
  let secondSum ← ops.addToOne (JInt.lit .i64 1) z
  let conjugate ← ops.conjugate secondSum
  let thirdRoot ← ops.sqrt conjugate
  let secondDifference ← ops.subtractFromOne (JInt.lit .i64 1) z
  let fourthRoot ← ops.sqrt secondDifference
  let product ← ops.multiply thirdRoot fourthRoot
  let imaginary ← ops.imag product
  let eta ← ops.inverseHyperbolicSine imaginary
  let realInfinite ← exponentialCondition (E := E) (← ops.isinf zr)
  let bothInfinite ← if realInfinite then exponentialCondition (E := E) (← ops.isinf zi)
    else pure false
  let xi ← if bothInfinite then do
      let pi ← ops.oftypePi eta
      let quarterPi ← ops.divideInt pi (JInt.lit .i64 4)
      let sign ← ops.sign zr
      let correction ← ops.multiply quarterPi sign
      ops.subtract xi correction
    else pure xi
  ops.construct xi eta

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Actual selected calls in generic tanh.  V retains all runtime type
changes.  Native integer literals remain explicit arguments.  multiply3 is
the single selected three-operand * call, including beta*rho*s and beta*s*s;
no binary association or arithmetic correctness is imposed.  The apparent
squares in source are binary products, not literal_pow calls.
Source reference: base/complex.jl:1002-1022. -/
-- Source: base/complex.jl:1002-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     Ω = prevfloat(typemax(Tf))
--     ξ, η = reim(z)
--     if isnan(ξ) && η==0 return Complex(ξ, η) end
--     if 4*abs(ξ) > asinh(Ω) #Overflow?
--         Complex(copysign(one(Tf),ξ),
--                 copysign(zero(Tf),η*(isfinite(η) ? sin(2*abs(η)) : one(η))))
--     else
--         t = tan(η)
--         β = 1+t*t #sec(η)^2
--         s = sinh(ξ)
--         ρ = sqrt(1 + s*s) #cosh(ξ)
--         if isinf(t)
--             Complex(ρ/s,1/t)
--         else
--             Complex(β*ρ*s,t)/(1+β*s*s)
--         end
--     end
-- end
-- /Source
inductive TanhReopenedCall (A Tag V : Type) where
  | float (original : Complex A)
  | floatType (tag : Tag)
  | typemax (value : V)
  | prevfloat (value : V)
  | reim (value : V)
  | indexedFirst (value : V) (index : JInt .i64)
  | indexedNext (value : V) (index : JInt .i64) (state : V)
  | isnan (value : V)
  | equalInt (value : V) (literal : JInt .i64)
  | construct (real imag : V)
  | abs (value : V)
  | multiplyIntLeft (literal : JInt .i64) (value : V)
  | asinh (value : V)
  | greater (left right : V)
  | one (value : V)
  | copysign (magnitude sign : V)
  | zero (value : V)
  | isfinite (value : V)
  | sin (value : V)
  | multiply (left right : V)
  | tan (value : V)
  | addIntLeft (literal : JInt .i64) (value : V)
  | sinh (value : V)
  | squareRoot (value : V)
  | isinf (value : V)
  | divide (numerator denominator : V)
  | divideIntLeft (literal : JInt .i64) (denominator : V)
  | multiply3 (first second third : V)

/-- Arbitrary selected effects with pure runtime Bool representation metadata.
boolValue recognizes the actual stored Bool value; it is not a callback that
supplies an operation's result.  No direct tanh call occurs in the body.
Source reference: base/complex.jl:1002-1022. -/
-- Source: base/complex.jl:1002-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     Ω = prevfloat(typemax(Tf))
--     ξ, η = reim(z)
--     if isnan(ξ) && η==0 return Complex(ξ, η) end
--     if 4*abs(ξ) > asinh(Ω) #Overflow?
--         Complex(copysign(one(Tf),ξ),
--                 copysign(zero(Tf),η*(isfinite(η) ? sin(2*abs(η)) : one(η))))
--     else
--         t = tan(η)
--         β = 1+t*t #sec(η)^2
--         s = sinh(ξ)
--         ρ = sqrt(1 + s*s) #cosh(ξ)
--         if isinf(t)
--             Complex(ρ/s,1/t)
--         else
--             Complex(β*ρ*s,t)/(1+β*s*s)
--         end
--     end
-- end
-- /Source
structure TanhReopenedOps (m : Type → Type) (A Tag V : Type) where
  selected : TanhReopenedCall A Tag V → m V
  boolValue : V → Option Bool

/-- Fixed Boolean use at if, && and ternary boundaries.
Source reference: base/complex.jl:1007-1017. -/
-- Source: base/complex.jl:1007-1017 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if isnan(ξ) && η==0 return Complex(ξ, η) end
--     if 4*abs(ξ) > asinh(Ω) #Overflow?
--         Complex(copysign(one(Tf),ξ),
--                 copysign(zero(Tf),η*(isfinite(η) ? sin(2*abs(η)) : one(η))))
--     else
--         t = tan(η)
--         β = 1+t*t #sec(η)^2
--         s = sinh(ξ)
--         ρ = sqrt(1 + s*s) #cosh(ξ)
--         if isinf(t)
--             Complex(ρ/s,1/t)
-- /Source
def tanhReopenedCondition {m : Type → Type} [Monad m] {E A Tag V : Type}
    [MonadExceptOf (Error E) m] (ops : TanhReopenedOps m A Tag V) (value : V) : m Bool :=
  match ops.boolValue value with
  | some result => pure result
  | none => throwThe (Error E) (.typeError "tanh Boolean condition")

/-- Complete generic tanh source body.  Float conversion and both type-level
queries precede reim.  The NaN shortcut and overflow ternary keep their exact
short circuits.  Overflow signs evaluate the real constructor argument before
zero(Tf) and the imaginary factor.  In the ordinary branch both three-operand
products remain actual selected calls, and the numerator constructor executes
before denominator arithmetic and division.
Source reference: base/complex.jl:1002-1022. -/
-- Source: base/complex.jl:1002-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     Ω = prevfloat(typemax(Tf))
--     ξ, η = reim(z)
--     if isnan(ξ) && η==0 return Complex(ξ, η) end
--     if 4*abs(ξ) > asinh(Ω) #Overflow?
--         Complex(copysign(one(Tf),ξ),
--                 copysign(zero(Tf),η*(isfinite(η) ? sin(2*abs(η)) : one(η))))
--     else
--         t = tan(η)
--         β = 1+t*t #sec(η)^2
--         s = sinh(ξ)
--         ρ = sqrt(1 + s*s) #cosh(ξ)
--         if isinf(t)
--             Complex(ρ/s,1/t)
--         else
--             Complex(β*ρ*s,t)/(1+β*s*s)
--         end
--     end
-- end
-- /Source
def tanhComplexReopened {m : Type → Type} [Monad m] {E Ref A Tag V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : TanhReopenedOps m A Tag V)
    (tag : Tag) (original : Complex A) : m V := do
  let z ← ops.selected (.float original)
  let tf ← ops.selected (.floatType tag)
  let maximum ← ops.selected (.typemax tf)
  let omega ← ops.selected (.prevfloat maximum)
  let parts ← ops.selected (.reim z)
  let iterations : IndexedIterateOps m V :=
    { first := fun value index => ops.selected (.indexedFirst value index)
      next := fun value index state => ops.selected (.indexedNext value index state) }
  let (xi, eta) ← destructureTwo (E := E) view iterations parts
  let realNaN ← tanhReopenedCondition (E := E) ops (← ops.selected (.isnan xi))
  let immediate ← if realNaN then
      tanhReopenedCondition (E := E) ops (← ops.selected (.equalInt eta (JInt.lit .i64 0)))
    else pure false
  if immediate then return ← ops.selected (.construct xi eta)
  let magnitude ← ops.selected (.abs xi)
  let scaled ← ops.selected (.multiplyIntLeft (JInt.lit .i64 4) magnitude)
  let threshold ← ops.selected (.asinh omega)
  if ← tanhReopenedCondition (E := E) ops (← ops.selected (.greater scaled threshold)) then
    let one ← ops.selected (.one tf)
    let real ← ops.selected (.copysign one xi)
    let zero ← ops.selected (.zero tf)
    let factor ← if ← tanhReopenedCondition (E := E) ops (← ops.selected (.isfinite eta)) then do
        let magnitude ← ops.selected (.abs eta)
        let doubled ← ops.selected (.multiplyIntLeft (JInt.lit .i64 2) magnitude)
        ops.selected (.sin doubled)
      else ops.selected (.one eta)
    let sign ← ops.selected (.multiply eta factor)
    let imag ← ops.selected (.copysign zero sign)
    ops.selected (.construct real imag)
  else
    let tangent ← ops.selected (.tan eta)
    let tangentSquare ← ops.selected (.multiply tangent tangent)
    let beta ← ops.selected (.addIntLeft (JInt.lit .i64 1) tangentSquare)
    let sine ← ops.selected (.sinh xi)
    let sineSquare ← ops.selected (.multiply sine sine)
    let sum ← ops.selected (.addIntLeft (JInt.lit .i64 1) sineSquare)
    let rho ← ops.selected (.squareRoot sum)
    if ← tanhReopenedCondition (E := E) ops (← ops.selected (.isinf tangent)) then
      let real ← ops.selected (.divide rho sine)
      let imag ← ops.selected (.divideIntLeft (JInt.lit .i64 1) tangent)
      ops.selected (.construct real imag)
    else
      let product ← ops.selected (.multiply3 beta rho sine)
      let numerator ← ops.selected (.construct product tangent)
      let denominatorProduct ← ops.selected (.multiply3 beta sine sine)
      let denominator ← ops.selected (.addIntLeft (JInt.lit .i64 1) denominatorProduct)
      ops.selected (.divide numerator denominator)

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Unary minus on the concrete Irrational{:π} first uses the constant native
Float64 conversion generated by @irrational, then installed Float64 negation.
In particular -pi is a rounded Float64, not an exact negative irrational.
The existing Fl64.pi is the installed binary64 value of that conversion.
Source reference: base/complex.jl:1037; base/irrationals.jl:215,269-303;
base/mathconstants.jl:13. -/
-- Source: base/irrationals.jl:215-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::AbstractIrrational) = -Float64(x)
-- /Source
-- Source: base/irrationals.jl:269-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- function irrational(sym, val, def)
--     esym = esc(sym)
--     qsym = esc(Expr(:quote, sym))
--     bigconvert = isa(def,Symbol) ? quote
--         function Base.BigFloat(::Irrational{$qsym}, r::MPFR.MPFRRoundingMode=Rounding.rounding_raw(BigFloat); precision=precision(BigFloat))
--             c = BigFloat(;precision=precision)
--             ccall(($(string("mpfr_const_", def)), Base.MPFR.libmpfr),
--                   Cint, (Ref{BigFloat}, MPFR.MPFRRoundingMode), c, r)
--             return c
--         end
--     end : quote
--         function Base.BigFloat(::Irrational{$qsym}; precision=precision(BigFloat))
--             setprecision(BigFloat, precision) do
--                 $(esc(def))
--             end
--         end
--     end
--     quote
--         const $esym = Irrational{$qsym}()
--         $bigconvert
--         let v = $val, v64 = Float64(v), v32 = Float32(v)
--             Base.Float64(::Irrational{$qsym}) = v64
--             Base.Float32(::Irrational{$qsym}) = v32
--         end
--         @assert isa(big($esym), BigFloat)
--         @assert Float64($esym) == Float64(big($esym))
--         @assert Float32($esym) == Float32(big($esym))
--     end
-- end
-- 
-- big(x::AbstractIrrational) = BigFloat(x)
-- big(::Type{<:AbstractIrrational}) = BigFloat
-- 
-- # align along = for nice Array printing
-- /Source
-- Source: base/mathconstants.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@irrational π        pi
-- /Source
def arcCoshNegativePi : JuliaLean.Float.F64 :=
  JuliaLean.Float.F64.neg Fl64.pi

/-- One selected call with its actual function identity and source arguments.
The oftypePi case fixes Irrational{:π}; oftypeFloat carries an actual Float64
argument.  Original Complex input calls keep that exact input unchanged.
Source reference: base/complex.jl:1029-1046. -/
-- Source: base/complex.jl:1029-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function acosh(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr) || isnan(zi)
--         if isinf(zr) || isinf(zi)
--             return Complex(oftype(zr, Inf), oftype(zi, NaN))
--         else
--             return Complex(oftype(zr, NaN), oftype(zi, NaN))
--         end
--     elseif zr==-Inf && zi===-0.0 #Edge case is wrong - WHY?
--         return Complex(oftype(zr,Inf), oftype(zi, -pi))
--     end
--     ξ = asinh(real(sqrt(conj(z-1))*sqrt(z+1)))
--     η = 2*atan(imag(sqrt(z-1)),real(sqrt(z+1)))
--     if isinf(zr) && isinf(zi)
--         η -= oftype(η,pi)/4 * sign(zi) * sign(zr)
--     end
--     Complex(ξ, η)
-- end
-- /Source
inductive ArcCoshCall (A V : Type) where
  | reim (z : Complex A)
  | indexedFirst (value : V) (index : JInt .i64)
  | indexedNext (value : V) (index : JInt .i64) (state : V)
  | isnan (value : V)
  | isinf (value : V)
  | equalFloat (value : V) (literal : JuliaLean.Float.F64)
  | oftypeFloat (value : V) (literal : JuliaLean.Float.F64)
  | oftypePi (value : V)
  | subtractIntOriginal (z : Complex A) (literal : JInt .i64)
  | addIntOriginal (z : Complex A) (literal : JInt .i64)
  | conjugate (value : V)
  | squareRoot (value : V)
  | multiply (left right : V)
  | multiplyThree (first second third : V)
  | multiplyNative (literal : JInt .i64) (value : V)
  | real (value : V)
  | imag (value : V)
  | asinh (value : V)
  | atan (y x : V)
  | divideInt (value : V) (literal : JInt .i64)
  | sign (value : V)
  | subtract (left right : V)
  | construct (real imag : V)

/-- Universal runtime carrier and selected operations.  Both views decode
actual primitive representations: boolValue recognizes exactly Bool values;
asFloat64 recognizes exactly Float64 with its stored bits.  Core identity is
implemented by identicalFloat64, not supplied as a result callback.
Source reference: base/complex.jl:1029-1046. -/
-- Source: base/complex.jl:1029-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function acosh(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr) || isnan(zi)
--         if isinf(zr) || isinf(zi)
--             return Complex(oftype(zr, Inf), oftype(zi, NaN))
--         else
--             return Complex(oftype(zr, NaN), oftype(zi, NaN))
--         end
--     elseif zr==-Inf && zi===-0.0 #Edge case is wrong - WHY?
--         return Complex(oftype(zr,Inf), oftype(zi, -pi))
--     end
--     ξ = asinh(real(sqrt(conj(z-1))*sqrt(z+1)))
--     η = 2*atan(imag(sqrt(z-1)),real(sqrt(z+1)))
--     if isinf(zr) && isinf(zi)
--         η -= oftype(η,pi)/4 * sign(zi) * sign(zr)
--     end
--     Complex(ξ, η)
-- end
-- /Source
structure ArcCoshOps (m : Type → Type) (A V : Type) where
  selected : ArcCoshCall A V → m V
  boolValue : V → Option Bool
  asFloat64 : V → Option JuliaLean.Float.F64

/-- Exact native Bool requirement at every condition in this source body.
Source reference: base/complex.jl:1031-1043. -/
-- Source: base/complex.jl:1031-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if isnan(zr) || isnan(zi)
--         if isinf(zr) || isinf(zi)
--             return Complex(oftype(zr, Inf), oftype(zi, NaN))
--         else
--             return Complex(oftype(zr, NaN), oftype(zi, NaN))
--         end
--     elseif zr==-Inf && zi===-0.0 #Edge case is wrong - WHY?
--         return Complex(oftype(zr,Inf), oftype(zi, -pi))
--     end
--     ξ = asinh(real(sqrt(conj(z-1))*sqrt(z+1)))
--     η = 2*atan(imag(sqrt(z-1)),real(sqrt(z+1)))
--     if isinf(zr) && isinf(zi)
--         η -= oftype(η,pi)/4 * sign(zi) * sign(zr)
-- /Source
def arcCoshCondition {m : Type → Type} [Monad m] {E A V : Type}
    [MonadExceptOf (Error E) m] (ops : ArcCoshOps m A V) (value : V) : m Bool :=
  match ops.boolValue value with
  | some result => pure result
  | none => throwThe (Error E) (.typeError "if")

/-- Full generic acosh body.  It retains both short-circuit NaN/Inf guards,
the exact negative-zero Float64 identity edge, repeated square-root arguments,
and the final eager ternary product in the infinite-coordinate correction.
The source's questioned edge is preserved, including rounded Float64 -pi.
Every selected call keeps arbitrary results, mutation and exceptions; native
unpacking and primitive identity are closed.  There is no direct acosh call.
Source reference: base/complex.jl:1029-1046. -/
-- Source: base/complex.jl:1029-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function acosh(z::Complex)
--     zr, zi = reim(z)
--     if isnan(zr) || isnan(zi)
--         if isinf(zr) || isinf(zi)
--             return Complex(oftype(zr, Inf), oftype(zi, NaN))
--         else
--             return Complex(oftype(zr, NaN), oftype(zi, NaN))
--         end
--     elseif zr==-Inf && zi===-0.0 #Edge case is wrong - WHY?
--         return Complex(oftype(zr,Inf), oftype(zi, -pi))
--     end
--     ξ = asinh(real(sqrt(conj(z-1))*sqrt(z+1)))
--     η = 2*atan(imag(sqrt(z-1)),real(sqrt(z+1)))
--     if isinf(zr) && isinf(zi)
--         η -= oftype(η,pi)/4 * sign(zi) * sign(zr)
--     end
--     Complex(ξ, η)
-- end
-- /Source
def arcCoshComplex {m : Type → Type} [Monad m] {E Ref A V : Type}
    [MonadExceptOf (Error E) m] [MonadStateOf (FieldHeap Ref V) m]
    (view : V → FieldDescriptor Ref V) (ops : ArcCoshOps m A V) (z : Complex A) : m V := do
  let parts ← ops.selected (.reim z)
  let iterations : IndexedIterateOps m V :=
    { first := fun value index => ops.selected (.indexedFirst value index)
      next := fun value index state => ops.selected (.indexedNext value index state) }
  let (zr, zi) ← destructureTwo (E := E) view iterations parts
  let realNaN ← arcCoshCondition (E := E) ops (← ops.selected (.isnan zr))
  let eitherNaN ← if realNaN then pure true else
    arcCoshCondition (E := E) ops (← ops.selected (.isnan zi))
  if eitherNaN then
    let realInfinite ← arcCoshCondition (E := E) ops (← ops.selected (.isinf zr))
    let eitherInfinite ← if realInfinite then pure true else
      arcCoshCondition (E := E) ops (← ops.selected (.isinf zi))
    if eitherInfinite then
      let real ← ops.selected (.oftypeFloat zr (JuliaLean.Float.F64.inf false))
      let imag ← ops.selected (.oftypeFloat zi JuliaLean.Float.F64.nan)
      return ← ops.selected (.construct real imag)
    else
      let real ← ops.selected (.oftypeFloat zr JuliaLean.Float.F64.nan)
      let imag ← ops.selected (.oftypeFloat zi JuliaLean.Float.F64.nan)
      return ← ops.selected (.construct real imag)
  let negativeInfinite ← arcCoshCondition (E := E) ops
    (← ops.selected (.equalFloat zr (JuliaLean.Float.F64.neg (JuliaLean.Float.F64.inf false))))
  if negativeInfinite then
    if identicalFloat64 ops.asFloat64 zi
        (JuliaLean.Float.F64.neg (JuliaLean.Float.F64.zero false)) then
      let real ← ops.selected (.oftypeFloat zr (JuliaLean.Float.F64.inf false))
      let imag ← ops.selected (.oftypeFloat zi arcCoshNegativePi)
      return ← ops.selected (.construct real imag)
  let difference ← ops.selected (.subtractIntOriginal z (JInt.lit .i64 1))
  let conjugate ← ops.selected (.conjugate difference)
  let firstRoot ← ops.selected (.squareRoot conjugate)
  let sum ← ops.selected (.addIntOriginal z (JInt.lit .i64 1))
  let secondRoot ← ops.selected (.squareRoot sum)
  let product ← ops.selected (.multiply firstRoot secondRoot)
  let real ← ops.selected (.real product)
  let xi ← ops.selected (.asinh real)
  let difference ← ops.selected (.subtractIntOriginal z (JInt.lit .i64 1))
  let thirdRoot ← ops.selected (.squareRoot difference)
  let imag ← ops.selected (.imag thirdRoot)
  let sum ← ops.selected (.addIntOriginal z (JInt.lit .i64 1))
  let fourthRoot ← ops.selected (.squareRoot sum)
  let real ← ops.selected (.real fourthRoot)
  let angle ← ops.selected (.atan imag real)
  let eta ← ops.selected (.multiplyNative (JInt.lit .i64 2) angle)
  let realInfinite ← arcCoshCondition (E := E) ops (← ops.selected (.isinf zr))
  let bothInfinite ← if realInfinite then
      arcCoshCondition (E := E) ops (← ops.selected (.isinf zi))
    else pure false
  let eta ← if bothInfinite then do
      let pi ← ops.selected (.oftypePi eta)
      let quarter ← ops.selected (.divideInt pi (JInt.lit .i64 4))
      let imaginarySign ← ops.selected (.sign zi)
      let realSign ← ops.selected (.sign zr)
      let correction ← ops.selected (.multiplyThree quarter imaginarySign realSign)
      ops.selected (.subtract eta correction)
    else pure eta
  ops.selected (.construct xi eta)

end JuliaLean.base.complex.Models2Group9
namespace JuliaLean.base.complex.Models2Group9

open JuliaLean

/-- Actual selected calls of generic atanh.  All results use one universal
runtime-value carrier, so float, the reassignment z *= beta, and every scalar
operation can change type.  oftypePi fixes Irrational{:pi}; oftypeFloat preserves
the literal Float64 argument.  literalPowerTwo denotes the exact selected
Base.literal_pow(Base.^, value, Val{2}()) call; neither power nor dispatch is
replaced by repeated multiplication.  All calls are to methods other than this
atanh source body, so no own-method recursion is delegated to an operation.
Source reference: base/complex.jl:1048-1089. -/
-- Source: base/complex.jl:1048-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function atanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     x, y = reim(z)
--     ax = abs(x)
--     ay = abs(y)
--     θ = sqrt(floatmax(Tf))/4
--     if ax > θ || ay > θ #Prevent overflow
--         if isnan(y)
--             if isinf(x)
--                 return Complex(copysign(zero(x),x), y)
--             else
--                 return Complex(real(inv(z)), y)
--             end
--         end
--         if isinf(y)
--             return Complex(copysign(zero(x),x), copysign(oftype(y,pi)/2, y))
--         end
--         return Complex(real(inv(z)), copysign(oftype(y,pi)/2, y))
--     end
--     β = copysign(one(Tf), x)
--     z *= β
--     x, y = reim(z)
--     if x == 1
--         if y == 0
--             ξ = oftype(x, Inf)
--             η = y
--         else
--             ξ = log(sqrt(sqrt(muladd(y, y, 4)))/sqrt(ay))
--             η = copysign(oftype(y,pi)/2 + atan(ay/2), y)/2
--         end
--     else #Normal case
--         ysq = ay^2
--         if x == 0
--             ξ = x
--         else
--             ξ = log1p(4x/(muladd(1-x, 1-x, ysq)))/4
--         end
--         η = angle(Complex((1-x)*(1+x)-ysq, 2y))/2
--     end
--     β * Complex(ξ, η)
-- end
-- /Source
inductive ArcTanhCall (A Tag V : Type) where
  | float (original : Complex A)
  | floatType (tag : Tag)
  | reim (value : V)
  | indexedFirst (value : V) (index : JInt .i64)
  | indexedNext (value : V) (index : JInt .i64) (state : V)
  | abs (value : V)
  | floatmax (value : V)
  | squareRoot (value : V)
  | divideInt (value : V) (literal : JInt .i64)
  | greater (left right : V)
  | isnan (value : V)
  | isinf (value : V)
  | zero (value : V)
  | copysign (left right : V)
  | construct (real imag : V)
  | inverse (value : V)
  | real (value : V)
  | oftypePi (value : V)
  | one (value : V)
  | multiply (left right : V)
  | equalInt (value : V) (literal : JInt .i64)
  | oftypeFloat (value : V) (literal : JuliaLean.Float.F64)
  | muladdInt (first second : V) (third : JInt .i64)
  | divide (left right : V)
  | log (value : V)
  | atan (value : V)
  | add (left right : V)
  | literalPowerTwo (value : V)
  | multiplyIntLeft (literal : JInt .i64) (value : V)
  | subtractIntLeft (literal : JInt .i64) (value : V)
  | addIntLeft (literal : JInt .i64) (value : V)
  | muladd (first second third : V)
  | log1p (value : V)
  | subtract (left right : V)
  | angle (value : V)

/-- Selected arbitrary effects plus the exact primitive Bool representation.
boolValue recognizes stored Bool values; it is not a callee result oracle.
Source reference: base/complex.jl:1048-1089. -/
-- Source: base/complex.jl:1048-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function atanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     x, y = reim(z)
--     ax = abs(x)
--     ay = abs(y)
--     θ = sqrt(floatmax(Tf))/4
--     if ax > θ || ay > θ #Prevent overflow
--         if isnan(y)
--             if isinf(x)
--                 return Complex(copysign(zero(x),x), y)
--             else
--                 return Complex(real(inv(z)), y)
--             end
--         end
--         if isinf(y)
--             return Complex(copysign(zero(x),x), copysign(oftype(y,pi)/2, y))
--         end
--         return Complex(real(inv(z)), copysign(oftype(y,pi)/2, y))
--     end
--     β = copysign(one(Tf), x)
--     z *= β
--     x, y = reim(z)
--     if x == 1
--         if y == 0
--             ξ = oftype(x, Inf)
--             η = y
--         else
--             ξ = log(sqrt(sqrt(muladd(y, y, 4)))/sqrt(ay))
--             η = copysign(oftype(y,pi)/2 + atan(ay/2), y)/2
--         end
--     else #Normal case
--         ysq = ay^2
--         if x == 0
--             ξ = x
--         else
--             ξ = log1p(4x/(muladd(1-x, 1-x, ysq)))/4
--         end
--         η = angle(Complex((1-x)*(1+x)-ysq, 2y))/2
--     end
--     β * Complex(ξ, η)
-- end
-- /Source
structure ArcTanhOps (m : Type → Type) (A Tag V : Type) where
  selected : ArcTanhCall A Tag V → m V
  boolValue : V → Option Bool

/-- Native Bool use at every if and disjunction boundary.
Source reference: base/complex.jl:1055-1087. -/
-- Source: base/complex.jl:1055-1068 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     if ax > θ || ay > θ #Prevent overflow
--         if isnan(y)
--             if isinf(x)
--                 return Complex(copysign(zero(x),x), y)
--             else
--                 return Complex(real(inv(z)), y)
--             end
--         end
--         if isinf(y)
--             return Complex(copysign(zero(x),x), copysign(oftype(y,pi)/2, y))
--         end
--         return Complex(real(inv(z)), copysign(oftype(y,pi)/2, y))
--     end
--     β = copysign(one(Tf), x)
-- /Source
def arcTanhCondition {m : Type → Type} [Monad m] {E A Tag V : Type}
    [MonadExceptOf (Error E) m] (ops : ArcTanhOps m A Tag V) (value : V) : m Bool :=
  match ops.boolValue value with
  | some result => pure result
  | none => throwThe (Error E) (.typeError "if")

/-- Complete generic atanh source body.  Both reim results are unpacked by
selected indexed_iterate calls and concrete current-heap field reads.  The
first ay remains unchanged after z is multiplied and x/y are reassigned.  Every
literal, repeated 1-x call, native short circuit, scalar call and constructor
keeps its source order and actual result.  The final multiplication uses beta
on the left; no inherited numerical formula or scalar correctness is assumed.
Source reference: base/complex.jl:1048-1089. -/
-- Source: base/complex.jl:1048-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function atanh(z::Complex{T}) where T
--     z = float(z)
--     Tf = float(T)
--     x, y = reim(z)
--     ax = abs(x)
--     ay = abs(y)
--     θ = sqrt(floatmax(Tf))/4
--     if ax > θ || ay > θ #Prevent overflow
--         if isnan(y)
--             if isinf(x)
--                 return Complex(copysign(zero(x),x), y)
--             else
--                 return Complex(real(inv(z)), y)
--             end
--         end
--         if isinf(y)
--             return Complex(copysign(zero(x),x), copysign(oftype(y,pi)/2, y))
--         end
--         return Complex(real(inv(z)), copysign(oftype(y,pi)/2, y))
--     end
--     β = copysign(one(Tf), x)
--     z *= β
--     x, y = reim(z)
--     if x == 1
--         if y == 0
--             ξ = oftype(x, Inf)
--             η = y
--         else
--             ξ = log(sqrt(sqrt(muladd(y, y, 4)))/sqrt(ay))
--             η = copysign(oftype(y,pi)/2 + atan(ay/2), y)/2
--         end
--     else #Normal case
--         ysq = ay^2
--         if x == 0
--             ξ = x
--         else
--             ξ = log1p(4x/(muladd(1-x, 1-x, ysq)))/4
--         end
--         η = angle(Complex((1-x)*(1+x)-ysq, 2y))/2
--     end
--     β * Complex(ξ, η)
-- end
-- /Source
def arcTanhComplex {m : Type → Type} [Monad m] {E Ref A Tag V : Type}
    [MonadStateOf (FieldHeap Ref V) m] [MonadExceptOf (Error E) m]
    (view : V → FieldDescriptor Ref V) (ops : ArcTanhOps m A Tag V)
    (tag : Tag) (original : Complex A) : m V := do
  let z ← ops.selected (.float original)
  let tf ← ops.selected (.floatType tag)
  let iterations : IndexedIterateOps m V :=
    { first := fun value index => ops.selected (.indexedFirst value index)
      next := fun value index state => ops.selected (.indexedNext value index state) }
  let parts ← ops.selected (.reim z)
  let (x, y) ← destructureTwo (E := E) view iterations parts
  let ax ← ops.selected (.abs x)
  let ay ← ops.selected (.abs y)
  let maximum ← ops.selected (.floatmax tf)
  let root ← ops.selected (.squareRoot maximum)
  let theta ← ops.selected (.divideInt root (JInt.lit .i64 4))
  let first ← arcTanhCondition (E := E) ops (← ops.selected (.greater ax theta))
  let overflow ← if first then pure true else
    arcTanhCondition (E := E) ops (← ops.selected (.greater ay theta))
  if overflow then
    if ← arcTanhCondition (E := E) ops (← ops.selected (.isnan y)) then
      if ← arcTanhCondition (E := E) ops (← ops.selected (.isinf x)) then
        let zero ← ops.selected (.zero x)
        let real ← ops.selected (.copysign zero x)
        return ← ops.selected (.construct real y)
      else
        let inverse ← ops.selected (.inverse z)
        let real ← ops.selected (.real inverse)
        return ← ops.selected (.construct real y)
    if ← arcTanhCondition (E := E) ops (← ops.selected (.isinf y)) then
      let zero ← ops.selected (.zero x)
      let real ← ops.selected (.copysign zero x)
      let pi ← ops.selected (.oftypePi y)
      let half ← ops.selected (.divideInt pi (JInt.lit .i64 2))
      let imag ← ops.selected (.copysign half y)
      return ← ops.selected (.construct real imag)
    let inverse ← ops.selected (.inverse z)
    let real ← ops.selected (.real inverse)
    let pi ← ops.selected (.oftypePi y)
    let half ← ops.selected (.divideInt pi (JInt.lit .i64 2))
    let imag ← ops.selected (.copysign half y)
    return ← ops.selected (.construct real imag)
  let one ← ops.selected (.one tf)
  let beta ← ops.selected (.copysign one x)
  let z ← ops.selected (.multiply z beta)
  let parts ← ops.selected (.reim z)
  let (x, y) ← destructureTwo (E := E) view iterations parts
  let (xi, eta) ← if ← arcTanhCondition (E := E) ops
      (← ops.selected (.equalInt x (JInt.lit .i64 1))) then do
      if ← arcTanhCondition (E := E) ops (← ops.selected (.equalInt y (JInt.lit .i64 0))) then
        let xi ← ops.selected (.oftypeFloat x (JuliaLean.Float.F64.inf false))
        pure (xi, y)
      else
        let sum ← ops.selected (.muladdInt y y (JInt.lit .i64 4))
        let firstRoot ← ops.selected (.squareRoot sum)
        let secondRoot ← ops.selected (.squareRoot firstRoot)
        let ayRoot ← ops.selected (.squareRoot ay)
        let quotient ← ops.selected (.divide secondRoot ayRoot)
        let xi ← ops.selected (.log quotient)
        let pi ← ops.selected (.oftypePi y)
        let piHalf ← ops.selected (.divideInt pi (JInt.lit .i64 2))
        let ayHalf ← ops.selected (.divideInt ay (JInt.lit .i64 2))
        let angle ← ops.selected (.atan ayHalf)
        let sum ← ops.selected (.add piHalf angle)
        let signed ← ops.selected (.copysign sum y)
        let eta ← ops.selected (.divideInt signed (JInt.lit .i64 2))
        pure (xi, eta)
    else do
      let ysq ← ops.selected (.literalPowerTwo ay)
      let xi ← if ← arcTanhCondition (E := E) ops
          (← ops.selected (.equalInt x (JInt.lit .i64 0))) then pure x else do
          let numerator ← ops.selected (.multiplyIntLeft (JInt.lit .i64 4) x)
          let first ← ops.selected (.subtractIntLeft (JInt.lit .i64 1) x)
          let second ← ops.selected (.subtractIntLeft (JInt.lit .i64 1) x)
          let denominator ← ops.selected (.muladd first second ysq)
          let quotient ← ops.selected (.divide numerator denominator)
          let logarithm ← ops.selected (.log1p quotient)
          ops.selected (.divideInt logarithm (JInt.lit .i64 4))
      let first ← ops.selected (.subtractIntLeft (JInt.lit .i64 1) x)
      let second ← ops.selected (.addIntLeft (JInt.lit .i64 1) x)
      let product ← ops.selected (.multiply first second)
      let real ← ops.selected (.subtract product ysq)
      let imag ← ops.selected (.multiplyIntLeft (JInt.lit .i64 2) y)
      let complex ← ops.selected (.construct real imag)
      let angle ← ops.selected (.angle complex)
      let eta ← ops.selected (.divideInt angle (JInt.lit .i64 2))
      pure (xi, eta)
  let complex ← ops.selected (.construct xi eta)
  ops.selected (.multiply beta complex)

end JuliaLean.base.complex.Models2Group9

namespace JuliaLean.NumbersCov

open JuliaLean

namespace ComplexModel

structure Cx (α : Type) where
  re : α
  im : α
  deriving DecidableEq, Repr

structure ScalarOps (α : Type) extends GenericOps α where
  identical : α → α → Bool
  ofInt : Int → α
  sin : α → α
  cos : α → α
  sinpi : α → α
  cospi : α → α
  sinh : α → α
  cosh : α → α
  tan : α → α
  tanh : α → α
  asinh : α → α
  muladd : α → α → α → α
  exp : α → α
  expm1 : α → α
  exp2 : α → α
  exp10 : α → α
  log : α → α
  log1p : α → α
  sqrt : α → α
  abs : α → α
  copysign : α → α → α
  round : α → α
  eps : α → α
  nextfloat : α → α
  prevfloat : α → α
  exponent : α → Int
  ldexp : α → Int → α
  floatmin : α
  floatmax : α
  pi : α

/-- Constructors and accessors; `base/complex.jl:17-18,42-47,72-124`. -/
def make (x y : α) : Cx α := ⟨x, y⟩
def ofReal (o : GenericOps α) (x : α) : Cx α := ⟨x, o.zero x⟩
def real (z : Cx α) : α := z.re
def imag (z : Cx α) : α := z.im
def reim (z : Cx α) : α × α := (z.re, z.im)

def constructPromoted (promote : α → β → γ × γ) (x : α) (y : β) : Cx γ :=
  let p := promote x y
  ⟨p.1, p.2⟩
def constructTypedReal (convert : α → β) (zero : β) (x : α) : Cx β :=
  ⟨convert x, zero⟩
def constructTypedComplex (convert : α → β) (z : Cx α) : Cx β :=
  ⟨convert z.re, convert z.im⟩
def realConvert (isreal : Cx α → Bool) (convert : α → β)
    (typeName : String) (z : Cx α) : Jl β :=
  if isreal z then .ok (convert z.re) else .error (.inexactError typeName)
def complexIdentity (z : Cx α) : Cx α := z
def realOfReal (x : α) : α := x
def imagOfReal (zero : α → α) (x : α) : α := zero x
def reimGeneric (real imag : α → β) (z : α) : β × β := (real z, imag z)

/-- Type-level promotion, widening, and real/complex component selection;
`base/complex.jl:49-57,120-124,190-195`. -/
def promoteType (promote : α → β → γ) (complexType : γ → δ) (a : α) (b : β) : δ :=
  complexType (promote a b)
def mapType (f : α → β) (complexType : β → γ) (t : α) : γ := complexType (f t)
def realTypeGeneric (zero : α → β) (real : β → γ) (typeOf : γ → δ) (t : α) : δ :=
  typeOf (real (zero t))
def realTypeIdentity (t : α) : α := t
def realTypeComplex (fieldType : α → β) (t : α) : β := fieldType t
def bottomType : Jl α := .error (.methodError "bottom type")

/-- Predicates; `base/complex.jl:148-155`. -/
def isreal (o : GenericOps α) (z : Cx α) : Bool := o.eq z.im (o.zero z.im)
def isinteger (o : GenericOps α) (integer : α → Bool) (z : Cx α) : Bool :=
  isreal o z && integer z.re
def isfinite (o : GenericOps α) (z : Cx α) : Bool := o.isfinite z.re && o.isfinite z.im
def isnan (o : GenericOps α) (z : Cx α) : Bool := o.isnan z.re || o.isnan z.im
def isinf (o : GenericOps α) (z : Cx α) : Bool := o.isinf z.re || o.isinf z.im
def iszero (o : GenericOps α) (z : Cx α) : Bool := o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im)
def isone (o : GenericOps α) (z : Cx α) : Bool := o.eq z.re (o.one z.re) && o.eq z.im (o.zero z.im)

/-- Equality, total equality, and range membership; `base/complex.jl:246-254`. -/
def eq (o : GenericOps α) (z w : Cx α) : Bool := o.eq z.re w.re && o.eq z.im w.im
def eqReal (o : GenericOps α) (z : Cx α) (x : α) : Bool := isreal o z && o.eq z.re x
def eqRealLeft (o : GenericOps α) (x : α) (z : Cx α) : Bool := isreal o z && o.eq z.re x
def isequal (eq : α → α → Bool) (z w : Cx α) : Bool := eq z.re w.re && eq z.im w.im
def isequalComplexReal (eq : α → α → Bool) (zero : α → α)
    (z : Cx α) (x : α) : Bool := eq z.re x && eq z.im (zero x)
def isequalRealComplex (eq : α → α → Bool) (zero : α → α)
    (x : α) (z : Cx α) : Bool := eq x z.re && eq (zero x) z.im
def memRealRange (o : GenericOps α) (mem : α → β → Bool) (z : Cx α) (r : β) : Bool :=
  isreal o z && mem z.re r

def flipsign (o : GenericOps α) (z : Cx α) (y : α) : Cx α :=
  if NumberModel.signbit o y then ⟨o.neg z.re, o.neg z.im⟩ else z

/-- Observable display and binary I/O shapes; `base/complex.jl:199-242`. -/
def showParts (realText imagText : String) (compact needsStar : Bool) : String :=
  let negative := imagText.startsWith "-"
  let imagText := if negative then (imagText.drop 1).toString else imagText
  realText ++
    (if negative then (if compact then "-" else " - ")
     else if compact then "+" else " + ") ++
    imagText ++ (if needsStar then "*" else "") ++ "im"
def showBool (isImaginaryUnit : Bool) (re im : Bool) : String :=
  if isImaginaryUnit then "im" else s!"Complex({re},{im})"
def showUnquoted (render : α → String) (needsParens : Bool) (z : α) : String :=
  if needsParens then "(" ++ render z ++ ")" else render z
def readPair (read : Unit → α × α) : Cx α :=
  let p := read (); ⟨p.1, p.2⟩
def writePair (write : α → α → β) (z : Cx α) : β := write z.re z.im
def bswap (swap : α → α) (z : Cx α) : Cx α := ⟨swap z.re, swap z.im⟩
def hash (hashScalar : α → Nat → Nat) (hImag hashZero : Nat) (z : Cx α) (h : Nat) : Nat :=
  hashScalar z.re (Nat.xor h (Nat.xor (hashScalar z.im hImag) hashZero))

/-- Componentwise arithmetic; `base/complex.jl:280-355`. -/
def conj (o : GenericOps α) (z : Cx α) : Cx α := ⟨z.re, o.neg z.im⟩
def abs2 (o : GenericOps α) (z : Cx α) : α := o.add (o.mul z.re z.re) (o.mul z.im z.im)
def pos (o : GenericOps α) (z : Cx α) : Cx α := ⟨o.pos z.re, o.pos z.im⟩
def neg (o : GenericOps α) (z : Cx α) : Cx α := ⟨o.neg z.re, o.neg z.im⟩
def add (o : GenericOps α) (z w : Cx α) : Cx α := ⟨o.add z.re w.re, o.add z.im w.im⟩
def sub (o : GenericOps α) (z w : Cx α) : Cx α := ⟨o.sub z.re w.re, o.sub z.im w.im⟩
def mul (o : GenericOps α) (z w : Cx α) : Cx α :=
  ⟨o.sub (o.mul z.re w.re) (o.mul z.im w.im),
   o.add (o.mul z.re w.im) (o.mul z.im w.re)⟩
def addReal (o : GenericOps α) (x : α) (z : Cx α) : Cx α := ⟨o.add x z.re, z.im⟩
def subRealComplex (o : GenericOps α) (x : α) (z : Cx α) : Cx α :=
  ⟨o.sub x z.re, o.neg z.im⟩
def subComplexReal (o : GenericOps α) (z : Cx α) (x : α) : Cx α := ⟨o.sub z.re x, z.im⟩
def mulReal (o : GenericOps α) (x : α) (z : Cx α) : Cx α := ⟨o.mul x z.re, o.mul x z.im⟩
def divReal (o : GenericOps α) (z : Cx α) (x : α) : Cx α := ⟨o.div z.re x, o.div z.im x⟩

def invGeneric (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isinf z.re || o.isinf z.im then
    ⟨o.copysign (o.zero z.re) z.re, o.neg (o.copysign (o.zero z.im) z.im)⟩
  else
    divReal o.toGenericOps ⟨z.re, o.neg z.im⟩
      (o.add (o.mul z.re z.re) (o.mul z.im z.im))

def invInteger (float : Cx α → Cx β) (inv : Cx β → Cx β) (z : Cx α) : Cx β :=
  inv (float z)

def mulsub (muladd : α → α → α → α) (neg : α → α) (a b c : α) : α :=
  muladd a b (neg c)
def mulsubPromoted (promote : α → β → γ → δ × δ × δ)
    (mulsub : δ → δ → δ → ε) (a : α) (b : β) (c : γ) : ε :=
  let p := promote a b c
  mulsub p.1 p.2.1 p.2.2

def muladdComplex (muladd : α → α → α → α) (mulsub : α → α → α → α)
    (neg : α → α) (z w x : Cx α) : Cx α :=
  ⟨muladd z.re w.re (neg (mulsub z.im w.im x.re)),
   muladd z.re w.im (muladd z.im w.re x.im)⟩

def muladdComplexReal (muladd : α → α → α → α) (mul : α → α → α)
    (z : Cx α) (x y : α) : Cx α :=
  ⟨muladd z.re x y, mul z.im x⟩
def muladdComplexScalar (muladd : α → α → α → α) (z : Cx α) (x : α)
    (w : Cx α) : Cx α := ⟨muladd z.re x w.re, muladd z.im x w.im⟩
def muladdRealRealComplex (muladd : α → α → α → α) (x y : α) (z : Cx α) : Cx α :=
  ⟨muladd x y z.re, z.im⟩
def muladdSwap (muladd : Cx α → α → β → γ) (x : α) (z : Cx α) (y : β) : γ :=
  muladd z x y
def muladdComplexComplexReal (muladd : α → α → α → α)
    (mulsub : α → α → α → α) (neg : α → α) (mul : α → α → α)
    (z w : Cx α) (x : α) : Cx α :=
  ⟨muladd z.re w.re (neg (mulsub z.im w.im x)),
   muladd z.re w.im (mul z.im w.re)⟩

def realDivComplex (promote : α → Cx β → γ × Cx γ) (mul : γ → Cx γ → Cx γ)
    (inv : Cx γ → Cx γ) (a : α) (z : Cx β) : Cx γ :=
  let p := promote a z
  mul p.1 (inv p.2)

/-- Generic same-component complex division; `base/complex.jl:360-377`. -/
def divGeneric (o : ScalarOps α) (a b : Cx α) : Cx α :=
  if o.isinf b.re || o.isinf b.im then
    if isfinite o.toGenericOps a then
      ⟨o.mul (o.mul (o.zero a.re) (NumberModel.signReal o.toGenericOps a.re))
          (NumberModel.signReal o.toGenericOps b.re),
       o.mul (o.neg (o.mul (o.zero a.im) (NumberModel.signReal o.toGenericOps a.im)))
          (NumberModel.signReal o.toGenericOps b.im)⟩
    else
      let nan := o.div (o.zero a.re) (o.zero a.re)
      ⟨nan, nan⟩
  else if o.le (o.abs b.re) (o.abs b.im) then
    let r := o.div b.re b.im
    let den := o.add b.im (o.mul r b.re)
    ⟨o.div (o.add (o.mul a.re r) a.im) den,
     o.div (o.sub (o.mul a.im r) a.re) den⟩
  else
    let r := o.div b.im b.re
    let den := o.add b.re (o.mul r b.im)
    ⟨o.div (o.add a.re (o.mul a.im r)) den,
     o.div (o.sub a.im (o.mul a.re r)) den⟩

/-- Widened Float16/Float32 division; `base/complex.jl:379-392`. -/
def divSmall (small : ScalarOps α) (wide : ScalarOps β)
    (widen : Cx α → Cx β) (narrow : Cx β → Cx α) (z w : Cx α) : Cx α :=
  let ww := widen w
  let zz := widen z
  if wide.isinf ww.re || wide.isinf ww.im then
    if isfinite small.toGenericOps z then
      ⟨small.mul (small.mul (small.zero z.re) (NumberModel.signReal small.toGenericOps z.re))
          (NumberModel.signReal small.toGenericOps w.re),
       small.mul (small.neg (small.mul (small.zero z.im) (NumberModel.signReal small.toGenericOps z.im)))
          (NumberModel.signReal small.toGenericOps w.im)⟩
    else
      let nan := small.div (small.zero z.re) (small.zero z.re)
      ⟨nan, nan⟩
  else
    let mag := wide.div (wide.one ww.re)
      (wide.muladd ww.re ww.re (wide.mul ww.im ww.im))
    let re := wide.muladd zz.re ww.re (wide.mul zz.im ww.im)
    let im := wide.muladd zz.im ww.re (wide.neg (wide.mul zz.re ww.im))
    narrow ⟨wide.mul re mag, wide.mul im mag⟩

def invSmall (small : ScalarOps α) (wide : ScalarOps β)
    (widen : Cx α → Cx β) (narrow : Cx β → Cx α) (z : Cx α) : Cx α :=
  let w := widen z
  if wide.isinf w.re || wide.isinf w.im then
    ⟨small.copysign (small.zero z.re) z.re,
     small.neg (small.copysign (small.zero z.im) z.im)⟩
  else
    let mag := wide.div (wide.one w.re)
      (wide.muladd w.re w.re (wide.mul w.im w.im))
    narrow ⟨wide.mul w.re mag, wide.neg (wide.mul w.im mag)⟩

/-- Generic `ssqs`; `base/complex.jl:519-531`. -/
def ssqs (o : ScalarOps α) (x y : α) : α × Int :=
  let rho0 := o.add (o.mul x x) (o.mul y y)
  let inf := o.div (o.one x) (o.zero x)
  if !o.isfinite rho0 && (o.isinf x || o.isinf y) then (inf, 0)
  else
    let threshold := o.div (o.nextfloat (o.zero x))
      (o.mul (o.ofInt 2) (o.mul (o.eps x) (o.eps x)))
    if o.isinf rho0 ||
        (o.eq rho0 (o.zero rho0) && (!o.eq x (o.zero x) || !o.eq y (o.zero y))) ||
        o.lt rho0 threshold then
      let m := if o.lt (o.abs x) (o.abs y) then o.abs y else o.abs x
      let k := if o.eq m (o.zero m) then 0 else o.exponent m
      let xk := o.ldexp x (-k)
      let yk := o.ldexp y (-k)
      (o.add (o.mul xk xk) (o.mul yk yk), k)
    else (rho0, 0)

/-- Main dispatch skeleton of `_cpow`; integer real exponents take the exact
power path and every other input takes the polar/logarithmic path. The supplied
callbacks implement the corresponding source blocks at `base/complex.jl:792-881`. -/
def cpow (float : Cx α → Cx α) (isreal : Cx α → Bool) (isinteger : α → Bool)
    (integerPower : Cx α → α → Cx α) (generalPower : Cx α → Cx α → Cx α)
    (z p : Cx α) : Cx α :=
  let z := float z
  let p := float p
  if isreal p && isinteger p.re then integerPower z p.re else generalPower z p

def cscale (o : GenericOps α) (r : α) (z : Cx α) : Cx α :=
  ⟨o.mul r z.re, o.mul r z.im⟩

def polarFinish (o : ScalarOps α) (cisF : α → Cx α) (r phi : α) : Cx α :=
  if o.isfinite phi then cscale o.toGenericOps r (cisF phi)
  else if o.eq r (o.zero r) then ⟨o.zero r, o.zero r⟩
  else
    let nan := o.div (o.zero r) (o.zero r)
    ⟨nan, nan⟩

def polarMagnitude (o : ScalarOps α) (r pr reLog imPhase : α) : α :=
  let lim := o.sub (o.log o.floatmax) (o.one o.floatmax)
  if o.lt (o.abs reLog) lim && o.lt (o.abs imPhase) lim then
    o.mul (o.pow r pr) (o.exp (o.neg imPhase))
  else o.exp (o.sub reLog imPhase)

/-- `_cpow` at `base/complex.jl:792-881`. Real Julia operands are represented
as complex values with zero imaginary component; `zWasReal` retains the source
union arm needed for the signed-zero rule at line 828. -/
def cpowFull (o : ScalarOps α) (float : Cx α → Cx α)
    (isinteger : α → Bool) (toInt : α → Int)
    (powerC : Cx α → Int → Cx α) (invC : Cx α → Cx α)
    (absC : Cx α → α) (cisF : α → Cx α) (angleF : Cx α → α)
    (zWasReal : Bool) (z0 p0 : Cx α) : Cx α :=
  let z := float z0
  let p := float p0
  let nan := o.div (o.zero z.re) (o.zero z.re)
  if isreal o.toGenericOps p then
    let pr := p.re
    if isinteger pr && o.lt (o.abs pr) (o.ofInt 2147483647) then
      if o.eq pr (o.zero pr) then
        let zi := if NumberModel.signbit o.toGenericOps p.re != NumberModel.signbit o.toGenericOps z.im
          then o.neg (o.zero z.im) else o.zero z.im
        ⟨o.one z.re, zi⟩
      else
        let ip := toInt pr
        if isreal o.toGenericOps z then
          if ip < 0 then
            if iszero o.toGenericOps z then ⟨nan, nan⟩
            else
              let re := o.pow (o.div (o.one z.re) z.re) (o.ofInt (-ip))
              let im := o.neg z.im
              ⟨re, if decide (ip % 2 = 0) && NumberModel.signbit o.toGenericOps z.re
                then o.neg im else im⟩
          else
            let re := o.pow z.re (o.ofInt ip)
            ⟨re, if decide (ip % 2 = 0) && NumberModel.signbit o.toGenericOps z.re
              then o.neg z.im else z.im⟩
        else if ip < 0 then powerC (invC z) (-ip) else powerC z ip
    else if isreal o.toGenericOps z then
      if o.eq z.re (o.zero z.re) then
        if o.lt (o.zero pr) pr then z else ⟨nan, nan⟩
      else if o.lt (o.zero z.re) z.re then
        let im := if zWasReal then
          (if o.lt z.re (o.one z.re) then o.neg p.im else p.im)
          else if NumberModel.signbit o.toGenericOps pr then o.neg z.im else z.im
        ⟨o.pow z.re pr, im⟩
      else
        let rp := o.pow (o.neg z.re) pr
        if o.isfinite pr then
          cscale o.toGenericOps rp
            ⟨o.cospi pr, if NumberModel.signbit o.toGenericOps z.im then o.neg (o.sinpi pr) else o.sinpi pr⟩
        else if o.eq rp (o.zero rp) then ⟨o.zero rp, o.zero rp⟩ else ⟨nan, nan⟩
    else
      let rp := o.pow (absC z) pr
      let phi := o.mul pr (angleF z)
      polarFinish o cisF rp phi
  else if isreal o.toGenericOps z then
    if iszero o.toGenericOps z then
      if o.lt (o.zero p.re) p.re then z else ⟨nan, nan⟩
    else if o.lt (o.zero z.re) z.re then
      let rp := o.pow z.re p.re
      let phi := o.mul p.im (o.log z.re)
      polarFinish o cisF rp phi
    else
      let r := o.neg z.re
      let theta := o.copysign o.pi z.im
      let logr := o.log r
      let reLog := o.mul p.re logr
      let imPhase := o.mul p.im theta
      let rp := polarMagnitude o r p.re reLog imPhase
      let phi := o.add (o.mul p.re theta) (o.mul p.im logr)
      polarFinish o cisF rp phi
  else
    let r := absC z
    let theta := angleF z
    let logr := o.log r
    let reLog := o.mul p.re logr
    let imPhase := o.mul p.im theta
    let rp := polarMagnitude o r p.re reLog imPhase
    let phi := o.add (o.mul p.re theta) (o.mul p.im logr)
    polarFinish o cisF rp phi

def powerBool (one : Cx α → Cx α) (z : Cx α) (n : Bool) : Cx α :=
  if n then z else one z
def powerCpow (cpow : Cx α → Cx β → Cx γ) (z : Cx α) (p : Cx β) : Cx γ :=
  cpow z p
def powerViaComplexExponent (toComplex : Int → Cx α)
    (pow : Cx α → Cx α → Cx α) (z : Cx α) (n : Int) : Cx α :=
  pow z (toComplex n)
def powerPromotedComplexReal (promote : α → β → γ)
    (convertComplex : γ → Cx α → Cx δ) (convertReal : γ → β → δ)
    (pow : Cx δ → δ → Cx δ) (component : α) (z : Cx α) (p : β) : Cx δ :=
  let t := promote component p
  pow (convertComplex t z) (convertReal t p)
def powerPromotedRealComplex (promote : α → β → γ)
    (convertReal : γ → α → δ) (convertComplex : γ → Cx β → Cx δ)
    (pow : δ → Cx δ → Cx δ) (z : α) (component : β) (p : Cx β) : Cx δ :=
  let t := promote z component
  pow (convertReal t z) (convertComplex t p)

/-- `cis` and `cispi`; `base/complex.jl:587-624`. -/
def cis (o : ScalarOps α) (theta : α) : Cx α := ⟨o.cos theta, o.sin theta⟩
def cisComplex (o : ScalarOps α) (z : Cx α) : Cx α :=
  let v := o.exp (o.neg z.im)
  ⟨o.mul v (o.cos z.re), o.mul v (o.sin z.re)⟩
def cispi (o : ScalarOps α) (theta : α) : Cx α :=
  ⟨o.cospi theta, o.sinpi theta⟩

def cispiComplex (o : ScalarOps α) (z : Cx α) : Cx α :=
  let v := o.exp (o.neg (o.mul o.pi z.im))
  ⟨o.mul v (o.cospi z.re), o.mul v (o.sinpi z.re)⟩

/-- Complex angle; `base/complex.jl:651`. -/
def angle (o : ScalarOps α) (z : Cx α) : α := o.atan2 z.im z.re

/-- Complex logarithm; `ssqs` supplies the source helper from
`base/complex.jl:519-531`; `base/complex.jl:653-674`. -/
def log (o : ScalarOps α) (ssqs : α → α → α × Int) (z : Cx α) : Cx α :=
  let p := ssqs z.re z.im
  let rho := p.1
  let k := p.2
  let ax := o.abs z.re
  let ay := o.abs z.im
  let theta := if o.lt ax ay then ax else ay
  let beta := if o.lt ax ay then ay else ax
  let one := o.ofInt 1
  let half := o.div one (o.ofInt 2)
  let near := o.lt half (o.mul beta beta) &&
    (!o.lt (o.div (o.ofInt 5) (o.ofInt 4)) beta || o.lt rho (o.ofInt 3))
  let mag := if k = 0 && near then
      o.div (o.log1p (o.add (o.mul (o.sub beta one) (o.add beta one)) (o.mul theta theta))) (o.ofInt 2)
    else o.add (o.div (o.log rho) (o.ofInt 2)) (o.mul (o.ofInt k) (o.log (o.ofInt 2)))
  ⟨mag, angle o z⟩

/-- Complex exponential, including source special-value branches;
`base/complex.jl:704-725`. -/
def exp (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isnan z.re then ⟨z.re, if o.eq z.im (o.zero z.im) then z.im else z.re⟩
  else if !o.isfinite z.im then
    if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re then
      ⟨o.neg z.re, o.div (o.zero z.re) (o.zero z.re)⟩
    else if o.isinf z.re then ⟨o.neg (o.zero z.re), o.copysign (o.zero z.im) z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let er := o.exp z.re
    if o.eq z.im (o.zero z.im) then ⟨er, z.im⟩
    else ⟨o.mul er (o.cos z.im), o.mul er (o.sin z.im)⟩

/-- Complex `expm1`; `base/complex.jl:727-755`. -/
def expm1 (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isnan z.re then ⟨z.re, if o.eq z.im (o.zero z.im) then z.im else z.re⟩
  else if !o.isfinite z.im then
    if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re then
      ⟨o.neg z.re, o.div (o.zero z.re) (o.zero z.re)⟩
    else if o.isinf z.re then ⟨o.neg (o.one z.re), o.copysign (o.zero z.im) z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let em1 := o.expm1 z.re
    if o.eq z.im (o.zero z.im) then ⟨em1, z.im⟩
    else
      let er := o.add em1 (o.one em1)
      if o.isfinite er then
        let half := o.div (o.one z.im) (o.ofInt 2)
        ⟨o.sub em1 (o.mul (o.ofInt 2) (o.mul er (o.mul (o.sin (o.mul half z.im)) (o.sin (o.mul half z.im))))),
         o.mul er (o.sin z.im)⟩
      else ⟨o.mul er (o.cos z.im), o.mul er (o.sin z.im)⟩

/-- Complex `log1p`; `base/complex.jl:757-773`. -/
def log1p (o : ScalarOps α) (logC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isfinite z.re then
    if o.isinf z.im then logC z
    else
      let u := add o.toGenericOps ⟨o.one z.re, o.zero z.im⟩ z
      if eq o.toGenericOps u ⟨o.one z.re, o.zero z.im⟩ then z
      else if !o.lt (o.zero u.re) u.re then logC u
      else mul o.toGenericOps (logC u) (divReal o.toGenericOps z (o.sub u.re (o.one u.re)))
  else if o.isnan z.re then ⟨z.re, z.re⟩
  else if o.isfinite z.im then
    ⟨o.div (o.one z.re) (o.zero z.re), o.copysign (if o.lt (o.zero z.re) z.re then o.zero z.re else o.pi) z.im⟩
  else ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩

/-- Complex `exp2` and `exp10`; `base/complex.jl:775-789`. -/
def exp2 (o : ScalarOps α) (z : Cx α) : Cx α :=
  let er := o.exp2 z.re
  let theta := o.mul z.im (o.log (o.ofInt 2))
  ⟨o.mul er (o.cos theta), o.mul er (o.sin theta)⟩
def exp10 (o : ScalarOps α) (z : Cx α) : Cx α :=
  let er := o.exp10 z.re
  let theta := o.mul z.im (o.log (o.ofInt 10))
  ⟨o.mul er (o.cos theta), o.mul er (o.sin theta)⟩

/-- Complex sine and cosine; `base/complex.jl:905-940`. -/
def sin (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.eq z.re (o.zero z.re) then ⟨z.re, o.sinh z.im⟩
  else if !o.isfinite z.re then
    if o.eq z.im (o.zero z.im) || o.isinf z.im then
      ⟨o.div (o.zero z.re) (o.zero z.re), z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
  else ⟨o.mul (o.sin z.re) (o.cosh z.im), o.mul (o.cos z.re) (o.sinh z.im)⟩

def cos (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.eq z.re (o.zero z.re) then
    ⟨o.cosh z.im, if o.isnan z.im then z.re else o.neg (o.copysign z.re z.im)⟩
  else if !o.isfinite z.re then
    if o.eq z.im (o.zero z.im) then
      ⟨o.div (o.zero z.re) (o.zero z.re), if o.isnan z.re then o.zero z.re else o.neg (o.copysign z.im z.re)⟩
    else if o.isinf z.im then ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
  else ⟨o.mul (o.cos z.re) (o.cosh z.im), o.neg (o.mul (o.sin z.re) (o.sinh z.im))⟩

/-- Complex inverse sine; `base/complex.jl:949-961`. -/
def asin (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isinf z.re && o.isinf z.im then
    ⟨o.copysign (o.div o.pi (o.ofInt 4)) z.re, z.im⟩
  else if o.isnan z.im && o.isinf z.re then
    ⟨z.im, o.div (o.one z.re) (o.zero z.re)⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let oneMinus := sub o.toGenericOps one z
    let onePlus := add o.toGenericOps one z
    let a := sqrtC oneMinus
    let b := sqrtC onePlus
    let xi := if o.eq z.re (o.zero z.re) then z.re
      else if !o.isfinite z.re then o.mul (o.div o.pi (o.ofInt 2)) (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re)
      else o.atan2 z.re (mul o.toGenericOps a b).re
    let etaTerm := mul o.toGenericOps (sqrtC (conj o.toGenericOps oneMinus)) b
    let eta := o.asinh (o.copysign etaTerm.im z.im)
    ⟨xi, eta⟩

/-- Complex inverse cosine; `base/complex.jl:963-984`. -/
def acos (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isnan z.re then
    if o.isinf z.im then ⟨z.re, o.neg z.im⟩ else ⟨z.re, z.re⟩
  else if o.isnan z.im then
    if o.isinf z.re then ⟨z.im, o.abs z.re⟩
    else if o.eq z.re (o.zero z.re) then ⟨o.div o.pi (o.ofInt 2), z.im⟩ else ⟨z.im, z.im⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps one z)
    let b := sqrtC (add o.toGenericOps one z)
    let xi := o.mul (o.ofInt 2) (o.atan2 a.re b.re)
    let eta := o.asinh (mul o.toGenericOps (conj o.toGenericOps b) a).im
    ⟨xi, eta⟩

/-- Full `acos` including signed-zero and infinite branches;
`base/complex.jl:963-984`. -/
def acosFull (o : ScalarOps α) (float : Cx α → Cx α)
    (sqrtC : Cx α → Cx α) (z0 : Cx α) : Cx α :=
  let z := float z0
  if o.isnan z.re then
    if o.isinf z.im then ⟨z.re, o.neg z.im⟩ else ⟨z.re, z.re⟩
  else if o.isnan z.im then
    if o.isinf z.re then ⟨z.im, o.abs z.re⟩
    else if o.eq z.re (o.zero z.re) then ⟨o.div o.pi (o.ofInt 2), z.im⟩
    else ⟨z.im, z.im⟩
  else if o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im) then
    ⟨o.div o.pi (o.ofInt 2), o.neg z.im⟩
  else if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.zero z.im) then
    ⟨z.im, o.neg z.re⟩
  else if o.isinf z.re && NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.neg (o.zero z.im)) then
    ⟨o.pi, o.neg z.re⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps one z)
    let b := sqrtC (add o.toGenericOps one z)
    let xi0 := o.mul (o.ofInt 2) (o.atan2 a.re b.re)
    let eta := o.asinh (mul o.toGenericOps (conj o.toGenericOps b) a).im
    let xi := if o.isinf z.re && o.isinf z.im then
      o.sub xi0 (o.mul (o.div o.pi (o.ofInt 4))
        (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re))
      else xi0
    ⟨xi, eta⟩

/-- Complex hyperbolic tangent, retaining the source overflow split;
`base/complex.jl:1002-1022`. -/
def tanh (o : ScalarOps α) (overflowThreshold : α) (z : Cx α) : Cx α :=
  if o.isnan z.re && o.eq z.im (o.zero z.im) then z
  else if o.lt overflowThreshold (o.mul (o.ofInt 4) (o.abs z.re)) then
    ⟨o.copysign (o.one z.re) z.re,
     o.copysign (o.zero z.im) (o.mul z.im (if o.isfinite z.im then o.sin (o.mul (o.ofInt 2) (o.abs z.im)) else o.one z.im))⟩
  else
    let t := o.tan z.im
    let beta := o.add (o.one t) (o.mul t t)
    let s := o.sinh z.re
    let rho := o.sqrt (o.add (o.one s) (o.mul s s))
    if o.isinf t then ⟨o.div rho s, o.div (o.one t) t⟩
    else divReal o.toGenericOps ⟨o.mul beta (o.mul rho s), t⟩
      (o.add (o.one s) (o.mul beta (o.mul s s)))

/-- Complex inverse hyperbolic cosine; `base/complex.jl:1029-1046`. -/
def acosh (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isnan z.re || o.isnan z.im then
    if o.isinf z.re || o.isinf z.im then
      ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps z one)
    let b := sqrtC (add o.toGenericOps z one)
    ⟨o.asinh (mul o.toGenericOps (conj o.toGenericOps a) b).re,
     o.mul (o.ofInt 2) (o.atan2 a.im b.re)⟩

def acoshFull (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let nan := o.div (o.zero z.re) (o.zero z.re)
  if o.isnan z.re || o.isnan z.im then
    if o.isinf z.re || o.isinf z.im then
      ⟨o.div (o.one z.re) (o.zero z.re), nan⟩ else ⟨nan, nan⟩
  else if o.isinf z.re && NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.neg (o.zero z.im)) then
    ⟨o.div (o.one z.re) (o.zero z.re), o.neg o.pi⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps z one)
    let b := sqrtC (add o.toGenericOps z one)
    let xi := o.asinh (mul o.toGenericOps (conj o.toGenericOps a) b).re
    let eta0 := o.mul (o.ofInt 2) (o.atan2 a.im b.re)
    let eta := if o.isinf z.re && o.isinf z.im then
      o.sub eta0 (o.mul (o.div o.pi (o.ofInt 4))
        (o.mul (if o.lt z.im (o.zero z.im) then o.neg (o.one z.im) else o.one z.im)
          (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re)))
      else eta0
    ⟨xi, eta⟩

/-- Complex inverse hyperbolic tangent; `base/complex.jl:1048-1089`. -/
def atanh (o : ScalarOps α) (large : α) (invC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let ax := o.abs z.re
  let ay := o.abs z.im
  if o.lt large ax || o.lt large ay then
    if o.isnan z.im then
      if o.isinf z.re then ⟨o.copysign (o.zero z.re) z.re, z.im⟩ else ⟨(invC z).re, z.im⟩
    else ⟨(invC z).re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
  else
    let beta := o.copysign (o.one z.re) z.re
    let x := o.mul z.re beta
    let y := o.mul z.im beta
    let ysq := o.mul (o.abs y) (o.abs y)
    let xi := if o.eq x (o.zero x) then x
      else o.div (o.log1p (o.div (o.mul (o.ofInt 4) x)
        (o.add (o.mul (o.sub (o.one x) x) (o.sub (o.one x) x)) ysq))) (o.ofInt 4)
    let eta := o.div (o.atan2 (o.mul (o.ofInt 2) y)
      (o.sub (o.mul (o.sub (o.one x) x) (o.add (o.one x) x)) ysq)) (o.ofInt 2)
    ⟨o.mul beta xi, o.mul beta eta⟩

def atanhFull (o : ScalarOps α) (large : α) (invC : Cx α → Cx α)
    (z : Cx α) : Cx α :=
  let ax := o.abs z.re
  let ay := o.abs z.im
  if o.lt large ax || o.lt large ay then
    if o.isnan z.im then
      if o.isinf z.re then ⟨o.copysign (o.zero z.re) z.re, z.im⟩
      else ⟨(invC z).re, z.im⟩
    else if o.isinf z.im then
      ⟨o.copysign (o.zero z.re) z.re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
    else ⟨(invC z).re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
  else
    let beta := o.copysign (o.one z.re) z.re
    let x := o.mul z.re beta
    let y := o.mul z.im beta
    let xiEta :=
      if o.eq x (o.one x) then
        if o.eq y (o.zero y) then
          (o.div (o.one x) (o.zero x), y)
        else
          let xi := o.log (o.div (o.sqrt (o.sqrt (o.add (o.mul y y) (o.ofInt 4))))
            (o.sqrt ay))
          let eta := o.div (o.copysign
            (o.add (o.div o.pi (o.ofInt 2)) (o.atan2 ay (o.ofInt 2))) y) (o.ofInt 2)
          (xi, eta)
      else
        let ysq := o.mul ay ay
        let xi := if o.eq x (o.zero x) then x
          else o.div (o.log1p (o.div (o.mul (o.ofInt 4) x)
            (o.add (o.mul (o.sub (o.one x) x) (o.sub (o.one x) x)) ysq))) (o.ofInt 4)
        let eta := o.div (o.atan2 (o.mul (o.ofInt 2) y)
          (o.sub (o.mul (o.sub (o.one x) x) (o.add (o.one x) x)) ysq)) (o.ofInt 2)
        (xi, eta)
    ⟨o.mul beta xiEta.1, o.mul beta xiEta.2⟩

/-- Analytic identities used by the short wrapper methods;
`base/complex.jl:695-702,943-1000,1024-1027`. -/
def logBase (o : ScalarOps α) (base : α) (logz : Cx α) : Cx α := divReal o.toGenericOps logz (o.log base)
def tanFromTanh (o : ScalarOps α) (tanhC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := tanhC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩
def atanFromAtanh (o : ScalarOps α) (atanhC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := atanhC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩
def sinhFromSin (_o : ScalarOps α) (sinC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := sinC ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩
def coshFromCos (o : ScalarOps α) (cosC : Cx α → Cx α) (z : Cx α) : Cx α :=
  cosC ⟨z.im, o.neg z.re⟩
def asinhFromAsin (o : ScalarOps α) (asinC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := asinC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩

/-- Componentwise rounding and conversions; `base/complex.jl:1123-1166`. -/
def round (rr ri : α → α) (z : Cx α) : Cx α := ⟨rr z.re, ri z.im⟩
def mapComponents (f : α → β) (z : Cx α) : Cx β := ⟨f z.re, f z.im⟩
def floatIdentity (z : Cx α) : Cx α := z
def bigType (big : α → β) (complexType : β → γ) (t : α) : γ := complexType (big t)
def bigValue (big : α → β) (convert : β → Cx α → Cx γ)
    (t : α) (z : Cx α) : Cx γ := convert (big t) z
def arrayComplexIdentity (xs : α) : α := xs
def arrayComplexConvert (isConcrete : Bool) (convert : α → β) (xs : α) : Jl β :=
  if isConcrete then .ok (convert xs)
  else .error (.argumentError "complex abstractly typed array")
def epsValue (o : ScalarOps α) (z : Cx α) : α :=
  o.sqrt (o.add (o.mul (o.eps z.re) (o.eps z.re)) (o.mul (o.eps z.im) (o.eps z.im)))
def epsType (o : ScalarOps α) (sample : α) : α :=
  o.mul (o.sqrt (o.add (o.one sample) (o.one sample))) (o.eps sample)

end ComplexModel

end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

abbrev C := ComplexModel.Cx

def m17 (promote : α → β → γ × γ) x y := ComplexModel.constructPromoted promote x y
def m18 (zero : α → α) x := ComplexModel.Cx.mk x (zero x)
def m42 (convert : α → β) (zero : β) x := ComplexModel.Cx.mk (convert x) zero
def m43 (convert : α → β) (z : C α) := ComplexModel.Cx.mk (convert z.re) (convert z.im)
def m44 (isreal : C α → Bool) (convert : α → β) name z :=
  ComplexModel.realConvert isreal convert name z
def m47 (z : C α) := z
def m49 (promote : α → β → γ) (complexType : γ → δ) t s := complexType (promote t s)
def m51 := @m49
def m54 (widen : α → β) (complexType : β → γ) t := complexType (widen t)
def m56 (complexType : α → β) t := complexType t
def m57 (float : α → β) (complexType : β → γ) t := complexType (float t)
def m72 (z : C α) := z.re
def m87 (z : C α) := z.im
def m88 (x : α) := x
def m89 (zero : α → α) x := zero x
def m102 (real imag : α → β) z := (real z, imag z)
def m120 (zero : α → β) (real : β → γ) (typeOf : γ → δ) t := typeOf (real (zero t))
def m121 (t : α) := t
def m122 (fieldType : α → β) t := fieldType t
def m123 : Option α := none
def m124 : Jl α := .error (.methodError "real")
def m148 (_ : α) := true
def m150 (o : GenericOps α) (integer : α → Bool) z := ComplexModel.isinteger o integer z
def m151 (o : GenericOps α) z := ComplexModel.isfinite o z
def m152 (o : GenericOps α) z := ComplexModel.isnan o z
def m153 (o : GenericOps α) z := ComplexModel.isinf o z
def m154 (o : GenericOps α) z := ComplexModel.iszero o z
def m155 (o : GenericOps α) z := ComplexModel.isone o z
def m168 (z : C α) := z
def m169 (zero : α → α) x := ComplexModel.Cx.mk x (zero x)
def m170 (promote : α → β → γ × γ) x y := ComplexModel.constructPromoted promote x y
def m190 (complexType : α → β) t := complexType t
def m191 := @m190
def m192 : Option α := none
def m195 : Jl α := .error (.methodError "complex")
def m197 (o : GenericOps α) z y := ComplexModel.flipsign o z y
def m199 realText imagText compact star := ComplexModel.showParts realText imagText compact star
def m219 re im isUnit := ComplexModel.showBool isUnit re im
def m222 (render : α → String) parens z := ComplexModel.showUnquoted render parens z
def m232 (read : Unit → α × α) := ComplexModel.readPair read
def m237 (write : α → α → β) z := ComplexModel.writePair write z
def m242 (swap : α → α) z := ComplexModel.bswap swap z
def m246 (o : GenericOps α) z w := ComplexModel.eq o z w
def m248 (o : GenericOps α) x z := ComplexModel.eqRealLeft o x z
def m252 (eq : α → α → Bool) (zero : α → α) x z := ComplexModel.isequalRealComplex eq zero x z
def m254 (o : GenericOps α) (mem : α → β → Bool) z r := ComplexModel.memRealRange o mem z r
def m282 (o : GenericOps α) z := ComplexModel.abs2 o z
def m283 (o : ComplexModel.ScalarOps α) z := ComplexModel.invGeneric o z
def m288 (float : C α → C β) (inv : C β → C β) z := ComplexModel.invInteger float inv z
def m290 (o : GenericOps α) z := ComplexModel.pos o z
def m291 (o : GenericOps α) z := ComplexModel.neg o z
def m292 (o : GenericOps α) z w := ComplexModel.add o z w
def m293 (o : GenericOps α) z w := ComplexModel.sub o z w
def m294 (o : GenericOps α) z w := ComplexModel.mul o z w
def m297 := @m291
def m298 := @m292
def m299 := @m293
def m300 := @m294
def m303 {A B C D E : Type} (promote : A → B → C → D × D × D)
    (mulsub : D → D → D → E) (a : A) (b : B) (c : C) :=
  ComplexModel.mulsubPromoted promote mulsub a b c
def m304 {α : Type} (muladd : α → α → α → α) (neg : α → α) (a b c : α) :=
  ComplexModel.mulsub muladd neg a b c
def scalarLeftAdd {α β γ δ : Type} (complex : γ → β → δ) (add : α → β → γ) x (z : C β) :=
  complex (add x z.re) z.im
def scalarRightAdd {α β γ δ : Type} (complex : γ → β → δ) (add : β → α → γ) (z : C β) x :=
  complex (add z.re x) z.im
def scalarLeftSub {α β γ δ : Type} (complex : γ → β → δ) (sub : α → β → γ) (neg : β → β) x (z : C β) :=
  complex (sub x z.re) (neg z.im)
def scalarRightSub {α β γ δ : Type} (complex : γ → β → δ) (sub : β → α → γ) (z : C β) x :=
  complex (sub z.re x) z.im
def scalarLeftMul {α β γ δ ε : Type} (complex : γ → δ → ε) (mulR : α → β → γ) (mulI : α → β → δ) x (z : C β) :=
  complex (mulR x z.re) (mulI x z.im)
def scalarRightMul {α β γ δ ε : Type} (complex : γ → δ → ε) (mulR : β → α → γ) (mulI : β → α → δ) (z : C β) x :=
  complex (mulR z.re x) (mulI z.im x)

def m311 := @scalarLeftAdd
def m312 := @scalarRightAdd
def m313 := @scalarLeftSub
def m314 := @scalarRightSub
def m315 := @scalarLeftMul
def m316 := @scalarRightMul
def m318 := @scalarLeftAdd
def m319 := @scalarRightAdd
def m320 := @scalarLeftSub
def m321 := @scalarRightSub
def m323 := @scalarRightMul
def m325 := @scalarLeftAdd
def m326 := @scalarRightAdd
def m327 := @scalarLeftSub
def m332 := @scalarRightSub
def m333 := @scalarLeftMul
def m334 := @scalarRightMul
def m337 := @scalarLeftAdd
def m338 := @scalarRightAdd
def m339 := @scalarLeftSub
def m344 := @scalarRightSub
def m345 := @scalarLeftMul
def m346 := @scalarRightMul

def m348 (muladd : C α → β → γ → δ) (x : β) (z : C α) (y : γ) := muladd z x y
def m349 := @ComplexModel.muladdComplexReal
def m350 := @ComplexModel.muladdComplexScalar
def m352 := @ComplexModel.muladdRealRealComplex
def m353 := @ComplexModel.muladdComplexComplexReal
def m357 := @ComplexModel.realDivComplex
def m358 := @ComplexModel.divReal
def m360 := @ComplexModel.divGeneric
def m379 := @ComplexModel.divSmall
def m424 := @JuliaLean.base.complex.cdiv
def m433 := @JuliaLean.base.complex.scaling_cdiv
def m439 := @JuliaLean.base.complex.scaleargs_cdiv
def m476 := @ComplexModel.invSmall
def m482 := @JuliaLean.base.complex.inv_ComplexF64
def m511 := @JuliaLean.base.complex.robust_cinv
def m519 := @ComplexModel.ssqs

end JuliaLean.NumbersCov.Rows.Complex

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def m587 := @ComplexModel.cis
def m592 := @ComplexModel.cisComplex
def m618 := @ComplexModel.cispi
def m620 := @ComplexModel.cispiComplex
def m651 := @ComplexModel.angle
def m653 := @ComplexModel.log
def m695 (o : ComplexModel.ScalarOps α) (logC : C α → C α) z :=
  ComplexModel.logBase o (o.ofInt 10) (logC z)
def m699 (o : ComplexModel.ScalarOps α) (logC : C α → C α) z :=
  ComplexModel.logBase o (o.ofInt 2) (logC z)
def m704 := @ComplexModel.exp
def m727 := @ComplexModel.expm1
def m757 := @ComplexModel.log1p
def m775 := @ComplexModel.exp2
def m783 := @ComplexModel.exp10
def m792 := @ComplexModel.cpowFull
def m882 (cpow : C α → C α → C α) z p := ComplexModel.powerCpow cpow z p
def m883 (cpow : C α → C α → C α) (toComplex : α → C α) z p := cpow z (toComplex p)
def m884 (cpow : C α → C α → C α) (toComplex : α → C α) z p := cpow (toComplex z) p
def m886 := @ComplexModel.powerBool
def m887 := @ComplexModel.powerViaComplexExponent
def m889 := @ComplexModel.powerBool
def m890 := @ComplexModel.powerBool
def m896 := @ComplexModel.powerPromotedComplexReal
def m900 := @ComplexModel.powerPromotedRealComplex
def m905 := @ComplexModel.sin
def m923 := @ComplexModel.cos
def m943 := @ComplexModel.tanFromTanh
def m949 := @ComplexModel.asin
def m963 := @ComplexModel.acosFull
def m986 := @ComplexModel.atanFromAtanh
def m991 := @ComplexModel.sinhFromSin
def m997 := @ComplexModel.coshFromCos
def m1002 := @ComplexModel.tanh
def m1024 := @ComplexModel.asinhFromAsin
def m1029 := @ComplexModel.acoshFull
def m1048 := @ComplexModel.atanhFull
def m1123 := @ComplexModel.round
def m1129 := @ComplexModel.floatIdentity
def m1130 := @ComplexModel.mapComponents
def m1132 := @ComplexModel.bigType
def m1133 := @ComplexModel.bigValue
def m1153 := @ComplexModel.arrayComplexIdentity
def m1155 := @ComplexModel.arrayComplexConvert
def m1164 := @ComplexModel.epsValue
def m1166 := @ComplexModel.epsType

end JuliaLean.NumbersCov.Rows.Complex

namespace JuliaLean.MathCov.MathMisc

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathCov.TrigPi (Cx)

/-- `muladd(z::Complex, x::Real, y::Real)` and `muladd(x::Real, z::Complex, y::Real)`:
`Complex(muladd(real(z), x, y), imag(z)*x)`; `base/complex.jl`. -/
def muladdCR {T : FTy} (a : FV T) (z : Cx T) (b : FV T) : Cx T := ⟨muladd z.re a b, mul z.im a⟩

end JuliaLean.MathCov.MathMisc
