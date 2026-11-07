import JuliaLean.base.float
import JuliaLean.base.rounding

/-!
# Model of `base/floatfuncs.jl`

Typed models of `base/floatfuncs.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Float arguments use `FV T` for IEEE types and generic operation records for other
`AbstractFloat` and `Real` types. Calls into other Base files remain typed interfaces.
-/

namespace JuliaLean.base.floatfuncs

open JuliaLean JuliaLean.base.float JuliaLean.base.rounding
open JuliaLean.Promotion hiding FV FTy
abbrev RoundMode := JuliaLean.base.rounding.RoundingMode

/--
Julia source: base/floatfuncs.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Float64, y::Float64) = copysign_float(x, y)
```
-/
def copysign_Float64 (x y : FV .f64) : FV .f64 := copysign_float x y

/--
Julia source: base/floatfuncs.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Float32, y::Float32) = copysign_float(x, y)
```
-/
def copysign_Float32 (x y : FV .f32) : FV .f32 := copysign_float x y

/--
Julia source: base/floatfuncs.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Float32, y::Real) = copysign(x, Float32(y))
```
-/
def copysign_Float32_Real {R : Type} (convert : R → FV .f32) (x : FV .f32) (y : R) : FV .f32 :=
  copysign_Float32 x (convert y)

/--
Julia source: base/floatfuncs.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Float64, y::Real) = copysign(x, Float64(y))
```
-/
def copysign_Float64_Real {R : Type} (convert : R → FV .f64) (x : FV .f64) (y : R) : FV .f64 :=
  copysign_Float64 x (convert y)

/--
Julia source: base/floatfuncs.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Float64, y::Float64) = bitcast(Float64, xor_int(bitcast(UInt64, x), and_int(bitcast(UInt64, y), 0x8000000000000000)))
```
-/
def flipsign_Float64 (x y : FV .f64) : FV .f64 :=
  let xb := bitcast_from_float .u64 x
  let yb := bitcast_from_float .u64 y
  let signMask := JuliaLean.base.int.lit .u64 0x8000000000000000
  bitcast_to_float .f64 (JuliaLean.base.int.xor_int xb (JuliaLean.base.int.and_int yb signMask))

/--
Julia source: base/floatfuncs.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Float32, y::Float32) = bitcast(Float32, xor_int(bitcast(UInt32, x), and_int(bitcast(UInt32, y), 0x80000000)))
```
-/
def flipsign_Float32 (x y : FV .f32) : FV .f32 :=
  let xb := bitcast_from_float .u32 x
  let yb := bitcast_from_float .u32 y
  let signMask := JuliaLean.base.int.lit .u32 0x80000000
  bitcast_to_float .f32 (JuliaLean.base.int.xor_int xb (JuliaLean.base.int.and_int yb signMask))

/--
Julia source: base/floatfuncs.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Float32, y::Real) = flipsign(x, Float32(y))
```
-/
def flipsign_Float32_Real {R : Type} (convert : R → FV .f32) (x : FV .f32) (y : R) : FV .f32 :=
  flipsign_Float32 x (convert y)

/--
Julia source: base/floatfuncs.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Float64, y::Real) = flipsign(x, Float64(y))
```
-/
def flipsign_Float64_Real {R : Type} (convert : R → FV .f64) (x : FV .f64) (y : R) : FV .f64 :=
  flipsign_Float64 x (convert y)

/--
Julia source: base/floatfuncs.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Float64) = signbit(bitcast(Int64, x))
```
-/
def signbit_Float64 (x : FV .f64) : Bool :=
  JuliaLean.base.int.signbit (bitcast_from_float .i64 x)

/--
Julia source: base/floatfuncs.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Float32) = signbit(bitcast(Int32, x))
```
-/
def signbit_Float32 (x : FV .f32) : Bool :=
  JuliaLean.base.int.signbit (bitcast_from_float .i32 x)

/--
Julia source: base/floatfuncs.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Float16) = signbit(bitcast(Int16, x))
```
-/
def signbit_Float16 (x : FV .f16) : Bool :=
  JuliaLean.base.int.signbit (bitcast_from_float .i16 x)

inductive FloatKind where
  | f16 | f32 | f64 | abstractFloat | integer | other
  deriving DecidableEq, Repr

structure FloatTypeOps (F : Type) where
  kind : FloatKind
  fromF16 : FV .f16 → F
  fromF32 : FV .f32 → F
  fromF64 : FV .f64 → F
  maxintfloatOther : F

def maxintfloatType (T : FTy) : FV T :=
  match T with
  | .f16 => Fl.ofInt 2048
  | .f32 => Fl.ofInt 16777216
  | .f64 => Fl.ofInt 9007199254740992

/--
Julia source: base/floatfuncs.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(::Type{Float64}) = 9007199254740992.
```
-/
def maxintfloat_Float64 : FV .f64 := Fl.ofInt 9007199254740992

/--
Julia source: base/floatfuncs.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(::Type{Float32}) = Float32(16777216.)
```
-/
def maxintfloat_Float32 : FV .f32 := Fl.ofInt 16777216

/--
Julia source: base/floatfuncs.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(::Type{Float16}) = Float16(2048f0)
```
-/
def maxintfloat_Float16 : FV .f16 := Fl.ofInt 2048

def maxintfloatTypeDispatch {F : Type} (ops : FloatTypeOps F) : F :=
  match ops.kind with
  | .f16 => ops.fromF16 maxintfloat_Float16
  | .f32 => ops.fromF32 maxintfloat_Float32
  | .f64 => ops.fromF64 maxintfloat_Float64
  | .abstractFloat | .integer | .other => ops.maxintfloatOther
/--
Julia source: base/floatfuncs.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(x::T) where {T<:AbstractFloat} = maxintfloat(T)
```
-/
def maxintfloat_AbstractFloat {F : Type} (ops : FloatTypeOps F) (_x : F) : F :=
  maxintfloatTypeDispatch ops

structure IntegerTypeOps (I : Type) where
  typemax : I

/--
Julia source: base/floatfuncs.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(::Type{S}, ::Type{T}) where {S<:AbstractFloat, T<:Integer} = min(maxintfloat(S), S(typemax(T)))
```
-/
def maxintfloat_AbstractFloat_Integer {F I : Type} (floatType : FloatTypeOps F)
    (integerType : IntegerTypeOps I) (convert : I → F) (min : F → F → F) : F :=
  min (maxintfloatTypeDispatch floatType) (convert integerType.typemax)

/--
Julia source: base/floatfuncs.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat() = maxintfloat(Float64)
```
-/
def maxintfloat_Default : FV .f64 := maxintfloat_Float64

/--
Julia source: base/floatfuncs.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(::Type{Union{}}, slurp...) = throw(MethodError(maxintfloat, (Union{}, slurp...)))
```
-/
def maxintfloat_UnionBottom {A : Type} (_slurp : List A) : Jl A :=
  .error (.methodError "maxintfloat")

/--
Julia source: base/floatfuncs.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(x, ::Type{Union{}}, slurp...) = throw(MethodError(maxintfloat, (x, Union{}, slurp...)))
```
-/
def maxintfloat_ValueUnionBottom {X A : Type} (_x : X) (_slurp : List A) : Jl X :=
  .error (.methodError "maxintfloat")

structure FloatPredicateOps (F : Type) where
  iszero : F → Bool
  sub : F → F → F
  trunc : F → F

/--
Julia source: base/floatfuncs.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinteger(x::AbstractFloat) = iszero(x - trunc(x)) # note: x == trunc(x) would be incorrect for x=Inf
```
-/
def isinteger_AbstractFloat {F : Type} (ops : FloatPredicateOps F) (x : F) : Bool :=
  ops.iszero (ops.sub x (ops.trunc x))

structure FloatOps (F I : Type) where
  kind : FloatKind
  toF16 : F → FV .f16
  toF32 : F → FV .f32
  toF64 : F → FV .f64
  fromF16 : FV .f16 → F
  fromF32 : FV .f32 → F
  fromF64 : FV .f64 → F
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  div : F → F → F
  neg : F → F
  abs : F → F
  lt : F → F → Bool
  eq : F → F → Bool
  isfinite : F → Bool
  iszero : F → Bool
  isnan : F → Bool
  isinf : F → Bool
  issubnormal : F → Bool
  signbit : F → Bool
  copysignOther : F → F → F
  zero : F → F
  infinity : F → F
  ofInt : Int → F
  ofType : F → I → F
  powInteger : F → I → F
  pow : F → F → F
  halfInteger : I → F
  trunc : F → F
  floor : F → F
  floorInt : F → Jl I
  exponent : F → Int
  log10 : F → F
  log : I → F → F
  epsAt : F → F
  quarter : F
  epsHalf : F
  round : F → RoundMode → F
  nextfloat : F → Int → F
  ldexp : F → Int → F

structure IntegerOps (I : Type) where
  value : I → Int
  ofInt : Int → I
  lt : I → I → Bool
  sub : I → I → I
  neg : I → I
  add : I → I → I
  ndigits0z : I → I → I
  widenValue : I → Int

structure RealOps (R F I : Type) where
  category : R → FloatKind
  isfinite : R → Bool
  float : R → Jl F
  toInteger : R → I
  toFloat : R → F


/--
Julia source: base/floatfuncs.jl:82-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_invstep(x, invstep, r::RoundingMode)
    y = round(x * invstep, r) / invstep
    if !isfinite(y)
        return x
    end
    return y
end
```
-/
def roundInvstep {F I : Type} (ops : FloatOps F I) (x invstep : F) (r : RoundMode) : F :=
  let y := ops.div (ops.round (ops.mul x invstep) r) invstep
  if !ops.isfinite y then x else y

/--
Julia source: base/floatfuncs.jl:92-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_invstepsqrt(x, invstepsqrt, r::RoundingMode)
    y = round((x * invstepsqrt) * invstepsqrt, r) / invstepsqrt / invstepsqrt
    if !isfinite(y)
        return x
    end
    return y
end
```
-/
def roundInvstepsqrt {F I : Type} (ops : FloatOps F I) (x invstepsqrt : F)
    (r : RoundMode) : F :=
  let y := ops.div (ops.div (ops.round (ops.mul (ops.mul x invstepsqrt) invstepsqrt) r)
    invstepsqrt) invstepsqrt
  if !ops.isfinite y then x else y

/--
Julia source: base/floatfuncs.jl:101-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_step(x, step, r::RoundingMode)
    # TODO: use div with rounding mode
    y = round(x / step, r) * step
    if !isfinite(y)
        if x > 0
            return (r == RoundUp ? oftype(x, Inf) : zero(x))
        elseif x < 0
            return (r == RoundDown ? -oftype(x, Inf) : -zero(x))
        else
            return x
        end
    end
    return y
end
```
-/
def roundStep {F I : Type} (ops : FloatOps F I) (x step : F) (r : RoundMode) : F :=
  let y := ops.mul (ops.round (ops.div x step) r) step
  if !ops.isfinite y then
    if ops.lt (ops.zero x) x then
      if r = RoundUp then ops.infinity x else ops.zero x
    else if ops.lt x (ops.zero x) then
      if r = RoundDown then ops.neg (ops.infinity x) else ops.neg (ops.zero x)
    else x
  else y

/--
Julia source: base/floatfuncs.jl:116-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_digits(x, r::RoundingMode, digits::Integer, base)
    fx = float(x)
    if digits >= 0
        invstep = oftype(fx, base)^digits
        if isfinite(invstep)
            return _round_invstep(fx, invstep, r)
        else
            invstepsqrt = oftype(fx, base)^oftype(fx, digits/2)
            return _round_invstepsqrt(fx, invstepsqrt, r)
        end
    else
        step = oftype(fx, base)^-digits
        return _round_step(fx, step, r)
    end
end
```
-/
def roundDigits {R F I : Type} (realOps : RealOps R F I) (ops : FloatOps F I)
    (iops : IntegerOps I) (x : R) (r : RoundMode) (digits base : I) : Jl F := do
  let fx ← realOps.float x
  if 0 ≤ iops.value digits then
    let invstep := ops.powInteger (ops.ofType fx base) digits
    if ops.isfinite invstep then
      pure (roundInvstep ops fx invstep r)
    else
      let invstepsqrt := ops.pow (ops.ofType fx base) (ops.halfInteger digits)
      pure (roundInvstepsqrt ops fx invstepsqrt r)
  else
    let step := ops.powInteger (ops.ofType fx base) (iops.neg digits)
    pure (roundStep ops fx step r)

/--
Julia source: base/floatfuncs.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hidigit(x::Integer, base) = ndigits0z(x, base)
```
-/
def hidigit_Integer {I : Type} (iops : IntegerOps I) (x base : I) : I :=
  iops.ndigits0z x base

/--
Julia source: base/floatfuncs.jl:133-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hidigit(x::AbstractFloat, base)
    iszero(x) && return 0
    if base == 10
        return 1 + floor(Int, log10(abs(x)))
    elseif base == 2
        return 1 + exponent(x)
    else
        return 1 + floor(Int, log(base, abs(x)))
    end
end
```
-/
def hidigit_AbstractFloat {F I : Type} (ops : FloatOps F I) (iops : IntegerOps I)
    (x : F) (base : I) : Jl I := do
  if ops.iszero x then
    pure (iops.ofInt 0)
  else if iops.value base = 10 then
    let f ← ops.floorInt (ops.log10 (ops.abs x))
    pure (iops.add (iops.ofInt 1) f)
  else if iops.value base = 2 then
    pure (iops.ofInt (1 + ops.exponent x))
  else
    let f ← ops.floorInt (ops.log base (ops.abs x))
    pure (iops.add (iops.ofInt 1) f)

/--
Julia source: base/floatfuncs.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hidigit(x::Real, base) = hidigit(float(x), base)
```
-/
def hidigit_Real {R F I : Type} (realOps : RealOps R F I) (ops : FloatOps F I)
    (iops : IntegerOps I) (x : R) (base : I) : Jl I := do
  let fx ← realOps.float x
  hidigit_AbstractFloat ops iops fx base

def hidigitDispatch {R F I : Type} (realOps : RealOps R F I) (ops : FloatOps F I)
    (iops : IntegerOps I) (x : R) (base : I) : Jl I :=
  match realOps.category x with
  | .integer => pure (hidigit_Integer iops (realOps.toInteger x) base)
  | .f16 | .f32 | .f64 | .abstractFloat => hidigit_AbstractFloat ops iops (realOps.toFloat x) base
  | .other => hidigit_Real realOps ops iops x base

/--
Julia source: base/floatfuncs.jl:145-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _round_sigdigits(x, r::RoundingMode, sigdigits::Integer, base)
    h = hidigit(x, base)
    _round_digits(x, r, sigdigits-h, base)
end
```
-/
def roundSigdigits {R F I : Type} (realOps : RealOps R F I) (ops : FloatOps F I)
    (iops : IntegerOps I) (x : R) (r : RoundMode) (sigdigits base : I) : Jl F := do
  let h ← hidigitDispatch realOps ops iops x base
  roundDigits realOps ops iops x r (iops.sub sigdigits h) base

/--
Julia source: base/floatfuncs.jl:56-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(x::Real, r::RoundingMode=RoundNearest;
               digits::Union{Nothing,Integer}=nothing, sigdigits::Union{Nothing,Integer}=nothing, base::Union{Nothing,Integer}=nothing)
    if digits === nothing
        if sigdigits === nothing
            if base === nothing
                # avoid recursive calls
                throw(MethodError(round, (x,r)))
            else
                round(x,r)
                # or throw(ArgumentError("`round` cannot use `base` argument without `digits` or `sigdigits` arguments."))
            end
        else
            isfinite(x) || return float(x)
            _round_sigdigits(x, r, sigdigits, base === nothing ? 10 : base)
        end
    else
        if sigdigits === nothing
            isfinite(x) || return float(x)
            _round_digits(x, r, digits, base === nothing ? 10 : base)
        else
            throw(ArgumentError("`round` cannot use both `digits` and `sigdigits` arguments."))
        end
    end
end
```
-/
def round_Real {R F I : Type} (realOps : RealOps R F I) (floatOps : FloatOps F I)
    (integerOps : IntegerOps I) (roundDefault : R → RoundMode → Jl R)
    (x : R) (r : RoundMode) (digits sigdigits base : Option I) : Jl (R ⊕ F) := do
  match digits, sigdigits, base with
  | none, none, none => .error (.methodError "round")
  | none, none, some _ =>
      (roundDefault x r).map Sum.inl
  | none, some sig, b =>
      if !realOps.isfinite x then
        (realOps.float x).map Sum.inr
      else
        (roundSigdigits realOps floatOps integerOps x r sig
          (b.getD (integerOps.ofInt 10))).map Sum.inr
  | some digs, none, b =>
      if !realOps.isfinite x then
        (realOps.float x).map Sum.inr
      else
        (roundDigits realOps floatOps integerOps x r digs
          (b.getD (integerOps.ofInt 10))).map Sum.inr
  | some _, some _, _ => .error (.argumentError "`round` cannot use both `digits` and `sigdigits` arguments.")
def copysignDispatch {F I : Type} (ops : FloatOps F I) (x y : F) : F :=
  match ops.kind with
  | .f32 => ops.fromF32 (copysign_Float32 (ops.toF32 x) (ops.toF32 y))
  | .f64 => ops.fromF64 (copysign_Float64 (ops.toF64 x) (ops.toF64 y))
  | _ => ops.copysignOther x y

def signbitDispatch {F I : Type} (ops : FloatOps F I) (x : F) : Bool :=
  match ops.kind with
  | .f16 => signbit_Float16 (ops.toF16 x)
  | .f32 => signbit_Float32 (ops.toF32 x)
  | .f64 => signbit_Float64 (ops.toF64 x)
  | _ => ops.signbit x

/--
Julia source: base/floatfuncs.jl:151-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway})
    y = trunc(x)
    ifelse(x==y,y,trunc(2*x-y))
end
```
-/
def round_TiesAway {F I : Type} (ops : FloatOps F I) (x : F) : F :=
  let y := ops.trunc x
  if ops.eq x y then y else ops.trunc (ops.sub (ops.mul (ops.ofInt 2) x) y)

/--
Julia source: base/floatfuncs.jl:156-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(x::T, ::RoundingMode{:NearestTiesUp}) where {T <: AbstractFloat}
    copysign(floor((x + (T(0.25) - eps(T(0.5)))) + (T(0.25) + eps(T(0.5)))), x)
end
```
-/
def round_TiesUp {F I : Type} (ops : FloatOps F I) (x : F) : F :=
  let lowQuarter := ops.sub ops.quarter ops.epsHalf
  let highQuarter := ops.add ops.quarter ops.epsHalf
  let y := ops.floor (ops.add (ops.add x lowQuarter) highQuarter)
  copysignDispatch ops y x

/--
Julia source: base/floatfuncs.jl:160-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.round(x::AbstractFloat, ::typeof(RoundFromZero))
    signbit(x) ? round(x, RoundDown) : round(x, RoundUp)
end
```
-/
def round_FromZero {F I : Type} (ops : FloatOps F I) (x : F) : F :=
  if signbitDispatch ops x then ops.round x RoundDown else ops.round x RoundUp

structure NumberApproxOps (N P D C : Type) where
  equal : N → N → Bool
  promote : N → N → P × P
  isfinite : N → Bool
  sub : N → N → D
  normDifference : D → C
  normValue : P → C
  max : C → C → C
  mul : C → C → C
  le : C → C → Bool
  isnan : N → Bool

/--
Julia source: base/floatfuncs.jl:230-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isapprox(x::Number, y::Number;
                  atol::Number=zero(real(x)), rtol::Real=rtoldefault(x,y,atol),
                  nans::Bool=false, norm::Function=abs)
    x′, y′ = promote(x, y) # to avoid integer overflow
    x == y ||
        (isfinite(x) && isfinite(y) && norm(x-y) <= max(atol, rtol*max(norm(x′), norm(y′)))) ||
         (nans && isnan(x) && isnan(y))
end
```
-/
def isapprox_Number {N P D C : Type} (ops : NumberApproxOps N P D C)
    (normDifference : D → C) (normValue : P → C) (x y : N)
    (atol rtol : C) (nans : Bool) : Bool :=
  let promoted := ops.promote x y
  ops.equal x y ||
    (ops.isfinite x && ops.isfinite y &&
      ops.le (normDifference (ops.sub x y))
        (ops.max atol (ops.mul rtol (ops.max (normValue promoted.1) (normValue promoted.2))))) ||
    (nans && ops.isnan x && ops.isnan y)

structure IntegerDifferenceOps (X Y D C : Type) where
  less : X → Y → Bool
  subXY : X → Y → D
  subYX : Y → X → D
  leBound : D → C → Bool

/--
Julia source: base/floatfuncs.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff(x::Integer, y::Integer) = x < y ? y - x : x - y
```
-/
def uabsdiff_Integer {X Y D C : Type} (ops : IntegerDifferenceOps X Y D C)
    (x : X) (y : Y) : D :=
  if ops.less x y then ops.subYX y x else ops.subXY x y

structure BoolBitIntegerOps (B U D : Type) where
  oftype : U → B → U
  uabsdiff : U → U → D

/--
Julia source: base/floatfuncs.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff(x::Bool, y::BitInteger) = _uabsdiff(oftype(y, x), y)
```
-/
def uabsdiff_Bool_BitInteger {B U D : Type} (ops : BoolBitIntegerOps B U D)
    (x : B) (y : U) : D :=
  ops.uabsdiff (ops.oftype y x) y

/--
Julia source: base/floatfuncs.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff(x::BitInteger, y::Bool) = _uabsdiff(x, oftype(x, y))
```
-/
def uabsdiff_BitInteger_Bool {B U D : Type} (ops : BoolBitIntegerOps B U D)
    (x : U) (y : B) : D :=
  ops.uabsdiff x (ops.oftype x y)

structure UabsdiffUnsignedOps (U D : Type) where
  minmax : U → U → U × U
  sub : U → U → D

/--
Julia source: base/floatfuncs.jl:249-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uabsdiff(x::BitUnsigned, y::BitUnsigned)
    lo, hi = minmax(x, y)
    return hi - lo
end
```
-/
def uabsdiff_BitUnsigned {U D : Type} (ops : UabsdiffUnsignedOps U D)
    (x y : U) : D :=
  let (lo, hi) := ops.minmax x y
  ops.sub hi lo

structure UabsdiffSignedOps (S U D : Type) where
  minmax : S → S → S × S
  unsigned : S → U
  sub : U → U → D

/--
Julia source: base/floatfuncs.jl:253-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uabsdiff(x::BitSigned, y::BitSigned)
    lo, hi = minmax(x, y)
    # Unsigned subtraction gives the exact distance even across zero.
    return unsigned(hi) - unsigned(lo)
end
```
-/
def uabsdiff_BitSigned {S U D : Type} (ops : UabsdiffSignedOps S U D)
    (x y : S) : D :=
  let (lo, hi) := ops.minmax x y
  ops.sub (ops.unsigned hi) (ops.unsigned lo)

structure MixedUabsdiffResult (U : Type) where
  m : U
  u : U
  d : U
  carried : Bool

structure MixedUabsdiffOps (S T U : Type) where
  unsignedSigned : S → U
  unsigned : T → U
  lessMixed : S → T → Bool
  sub : U → U → U
  neg : U → U
  less : U → U → Bool
  isnegative : S → Bool

/--
Julia source: base/floatfuncs.jl:261-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mixed_uabsdiff(x::BitSigned, y::BitUnsigned)
    U = promote_type(unsigned(typeof(x)), typeof(y))
    v, u = x % U, y % U
    d = ifelse(x < y, u - v, v - u)
    # For x < 0, the distance is |x| + y, which carries exactly when d < u.
    return -v, u, d, (x < 0) & (d < u)
end
```
-/
def mixedUabsdiff {S T U : Type} (ops : MixedUabsdiffOps S T U)
    (x : S) (y : T) : MixedUabsdiffResult U :=
  let v := ops.unsignedSigned x
  let u := ops.unsigned y
  let dUV := ops.sub u v
  let dVU := ops.sub v u
  let d := if ops.lessMixed x y then dUV else dVU
  let carried := Bool.and (ops.isnegative x) (ops.less d u)
  ⟨ops.neg v, u, d, carried⟩

structure UabsdiffMixedResultOps (U D : Type) where
  narrow : U → D
  widenedSum : U → U → D

/--
Julia source: base/floatfuncs.jl:269-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uabsdiff(x::BitSigned, y::BitUnsigned)
    m, u, d, carried = _mixed_uabsdiff(x, y)
    return carried ? widen(m) + widen(u) : d
end
```
-/
def uabsdiff_BitSigned_BitUnsigned {S T U D : Type}
    (mixedOps : MixedUabsdiffOps S T U) (resultOps : UabsdiffMixedResultOps U D)
    (x : S) (y : T) : D :=
  let result := mixedUabsdiff mixedOps x y
  if result.carried then resultOps.widenedSum result.m result.u else resultOps.narrow result.d

/--
Julia source: base/floatfuncs.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff(x::BitUnsigned, y::BitSigned) = _uabsdiff(y, x)
```
-/
def uabsdiff_BitUnsigned_BitSigned {S T U D : Type}
    (mixedOps : MixedUabsdiffOps S T U) (resultOps : UabsdiffMixedResultOps U D)
    (x : T) (y : S) : D :=
  uabsdiff_BitSigned_BitUnsigned mixedOps resultOps y x

/--
Julia source: base/floatfuncs.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff_le(x::Integer, y::Integer, b::Real) = _uabsdiff(x, y) <= b
```
-/
def uabsdiffLe_Integer {X Y D C : Type} (ops : IntegerDifferenceOps X Y D C)
    (distance : X → Y → D) (x : X) (y : Y) (bound : C) : Bool :=
  ops.leBound (distance x y) bound

structure WidesumLeOps (U W R : Type) where
  widen : U → W
  add : W → W → W
  le : W → R → Bool

/--
Julia source: base/floatfuncs.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _widesum_le(m::T, u::T, b::Real) where {T<:BitUnsigned} = widen(m) + widen(u) <= b
```
-/
def widesumLe {U W R : Type} (ops : WidesumLeOps U W R)
    (m u : U) (bound : R) : Bool :=
  ops.le (ops.add (ops.widen m) (ops.widen u)) bound

structure MixedUabsdiffLeOps (S T U W R : Type) where
  mixedOps : MixedUabsdiffOps S T U
  boundGreaterThanTypemax : R → U → Bool
  widesumOps : WidesumLeOps U W R
  distanceLe : U → R → Bool

/--
Julia source: base/floatfuncs.jl:278-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uabsdiff_le(x::BitSigned, y::BitUnsigned, b::Real)
    m, u, d, carried = _mixed_uabsdiff(x, y)
    # Widen only if both the distance and the bound exceed typemax(d).
    carried & (b > typemax(d)) && return _widesum_le(m, u, b)
    return (d <= b) & !carried
end
```
-/
def uabsdiffLe_BitSigned_BitUnsigned {S T U W R : Type}
    (ops : MixedUabsdiffLeOps S T U W R) (x : S) (y : T) (bound : R) : Bool :=
  let result := mixedUabsdiff ops.mixedOps x y
  let boundExceedsMax := ops.boundGreaterThanTypemax bound result.d
  if result.carried && boundExceedsMax then
    widesumLe ops.widesumOps result.m result.u bound
  else
    Bool.and (ops.distanceLe result.d bound) (!result.carried)

/--
Julia source: base/floatfuncs.jl:284-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff_le(x::BitUnsigned, y::BitSigned, b::Real) = _uabsdiff_le(y, x, b)
```
-/
def uabsdiffLe_BitUnsigned_BitSigned {S T U W R : Type}
    (ops : MixedUabsdiffLeOps S T U W R) (x : T) (y : S) (bound : R) : Bool :=
  uabsdiffLe_BitSigned_BitUnsigned ops y x bound


structure ScaledRtolOps (R W B : Type) where
  bitInteger : Bool
  mulReal : R → W → Jl B
  bitRtol : R → Jl W
  bitScale : W → Jl W
  promote : W → W → Jl (W × W)
  mulWithOverflow : W → W → Jl (B × Bool)

/--
Julia source: base/floatfuncs.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_scaled_rtol(rtol::Real, scale::Integer) = (rtol * scale, false)
```
-/
def scaledRtol_Real_Integer {R W B : Type} (mul : R → W → Jl B)
    (rtol : R) (scale : W) : Jl (B × Bool) :=
  (mul rtol scale).map (fun value => (value, false))

/--
Julia source: base/floatfuncs.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol, scale)...)
```
-/
def scaledRtol_BitInteger {W B : Type} (promote : W → W → Jl (W × W))
    (mulWithOverflow : W → W → Jl (B × Bool)) (rtol scale : W) : Jl (B × Bool) := do
  let promoted ← promote rtol scale
  mulWithOverflow promoted.1 promoted.2

def scaledRtolDispatch {R W B : Type} (ops : ScaledRtolOps R W B)
    (rtol : R) (scale : W) : Jl (B × Bool) :=
  if ops.bitInteger then do
    let rtol ← ops.bitRtol rtol
    let scale ← ops.bitScale scale
    scaledRtol_BitInteger ops.promote ops.mulWithOverflow rtol scale
  else
    scaledRtol_Real_Integer ops.mulReal rtol scale

structure IntegerApproxOps (X Y D W R B : Type) where
  equal : X → Y → Bool
  normIsAbs : Bool
  atolLessOne : R → Bool
  rtolIsZero : R → Bool
  uabsX : X → W
  uabsY : Y → W
  maxMagnitude : W → W → W
  scaledRtol : ScaledRtolOps R W B
  difference : IntegerDifferenceOps X Y D B
  uabsdiff : X → Y → D
  uabsdiffLe : X → Y → B → Jl Bool
  normDifference : D → B
  normUabsX : X → B
  normUabsY : Y → B
  maxValues : B → B → B
  maxBound : R → B → B
  mulBound : R → B → B
  le : B → B → Bool

/--
Julia source: base/floatfuncs.jl:289-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isapprox(x::Integer, y::Integer;
                  atol::Real=0, rtol::Real=rtoldefault(x,y,atol),
                  nans::Bool=false, norm::Function=abs)
    if norm === abs
        atol < 1 && rtol == 0 && return x == y
        # Check equality before forming the bound, since Inf * 0 is NaN.
        x == y && return true
        # uabs handles typemin and avoids signed/unsigned promotion.
        b, overflowed = _scaled_rtol(rtol, max(uabs(x), uabs(y)))
        # Overflow implies rtol >= 2, hence rtol * max(|x|, |y|) >= |x - y|.
        return overflowed || _uabsdiff_le(x, y, max(atol, b))
    end
    return x == y ||
        norm(_uabsdiff(x, y)) <= max(atol, rtol*max(norm(uabs(x)), norm(uabs(y))))
end
```
-/
def isapprox_Integer {X Y D W R B : Type} (ops : IntegerApproxOps X Y D W R B)
    (x : X) (y : Y) (atol rtol : R) : Jl Bool :=
  if ops.normIsAbs then
    if ops.atolLessOne atol && ops.rtolIsZero rtol then
      .ok (ops.equal x y)
    else if ops.equal x y then
      .ok true
    else do
      let scaled ← scaledRtolDispatch ops.scaledRtol rtol
        (ops.maxMagnitude (ops.uabsX x) (ops.uabsY y))
      if scaled.2 then .ok true
      else ops.uabsdiffLe x y (ops.maxBound atol scaled.1)
  else
    .ok (ops.equal x y ||
      ops.le (ops.normDifference (ops.uabsdiff x y))
        (ops.maxBound atol
          (ops.mulBound rtol (ops.maxValues (ops.normUabsX x) (ops.normUabsY y)))))
/--
Julia source: base/floatfuncs.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isapprox(y; kwargs...) = x -> isapprox(x, y; kwargs...)
```
-/
def isapprox_Curried {N K : Type} (isapprox : N → N → K → Jl Bool) (y : N)
    (kwargs : K) : N → Jl Bool :=
  fun x => isapprox x y kwargs

/--
Julia source: base/floatfuncs.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
≉(args...; kws...) = !≈(args...; kws...)
```
-/
def notApproximately {A K : Type} (approximately : A → K → Jl Bool) (args : A)
    (kwargs : K) : Jl Bool :=
  (approximately args kwargs).map (!·)

structure RtolFloatOps (F : Type) where
  eps : Jl F
  sqrt : F → Jl F

/--
Julia source: base/floatfuncs.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rtoldefault(::Type{T}) where {T<:AbstractFloat} = sqrt(eps(T))
```
-/
def rtoldefault_AbstractFloat {F : Type} (ops : RtolFloatOps F) : Jl F := do
  ops.sqrt (← ops.eps)

/--
Julia source: base/floatfuncs.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rtoldefault(::Type{<:Real}) = 0
```
-/
def rtoldefault_Real : Int := 0

structure NumberTypeOps (T R : Type) where
  oneType : T → Jl T
  sameType : T → T → Bool
  default : T → Jl R

/--
Julia source: base/floatfuncs.jl:330-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rtoldefault(::Type{T}) where {T<:Number}
    S = typeof(one(T))
    S === T && throw(MethodError(rtoldefault, (T,)))
    return rtoldefault(S)
end
```
-/
def rtoldefault_Number {T R : Type} (ops : NumberTypeOps T R) (t : T) : Jl R := do
  let s ← ops.oneType t
  if ops.sameType s t then
    .error (.methodError "rtoldefault")
  else
    ops.default s

structure RtolPairOps (T A R : Type) where
  realType : T → T
  default : T → Jl R
  max : R → R → Jl R
  zeroAtol : A → Jl A
  atolGreater : A → A → Jl Bool
  zeroRtol : R → Jl R

/--
Julia source: base/floatfuncs.jl:335-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rtoldefault(x::Union{T,Type{T}}, y::Union{S,Type{S}}, atol::Number) where {T<:Number,S<:Number}
    rtol = max(rtoldefault(real(T)),rtoldefault(real(S)))
    return atol > zero(atol) ? zero(rtol) : rtol
end
```
-/
def rtoldefault_Values {T A R : Type} (ops : RtolPairOps T A R)
    (xType yType : T) (atol : A) : Jl R := do
  let rtolX ← ops.default (ops.realType xType)
  let rtolY ← ops.default (ops.realType yType)
  let rtol ← ops.max rtolX rtolY
  let zeroAtol ← ops.zeroAtol atol
  if ← ops.atolGreater atol zeroAtol then ops.zeroRtol rtol else pure rtol

/-- `widen(T)` for the Float16 and Float32 FMA methods. -/
def smallWidenedType : FTy → FTy
  | .f16 => JuliaLean.base.float.widen_Float16
  | .f32 => JuliaLean.base.float.widen_Float32
  | .f64 => .f64
structure SmallFmaOps (T : FTy) where
  widen : FV T → FV (smallWidenedType T)
  narrow : FV (smallWidenedType T) → FV T

/--
Julia source: base/floatfuncs.jl:350-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fma_emulated(a::T, b::T, c::T) where {T<:Union{Float16, Float32}}
    W = widen(T)
    ab = W(a) * b # exact
    res = ab + c
    bb = res - ab
    err = (ab - (res - bb)) + (c - bb) # exact error of ab + c (TwoSum)
    # Round res to odd, so that rounding it to T (which has at least 2 fewer bits) is correct
    u = reinterpret(Unsigned, res)
    adjust = (abs(err) > 0) & iseven(u) # false if err is zero or NaN (from Inf/NaN inputs)
    u += ifelse(adjust, ifelse(signbit(err) == signbit(res), one(u), -one(u)), zero(u))
    return T(reinterpret(W, u))
end
```
-/
def fmaEmulatedSmall {T : FTy} (_format : T = .f16 ∨ T = .f32)
    (ops : SmallFmaOps T) (a b c : FV T) : FV T := Id.run do
  let W : FTy := smallWidenedType T
  let aw := ops.widen a
  let bw := ops.widen b
  let cw := ops.widen c
  let ab := JuliaLean.base.float.mul_float aw bw
  let res := JuliaLean.base.float.add_float ab cw
  let bb := JuliaLean.base.float.sub_float res ab
  let err := JuliaLean.base.float.add_float
    (JuliaLean.base.float.sub_float ab (JuliaLean.base.float.sub_float res bb))
    (JuliaLean.base.float.sub_float cw bb)
  let u := JuliaLean.base.float.bitcast_from_float W.uintTy res
  let adjust := Bool.and
    (JuliaLean.base.float.lt_float (JuliaLean.base.float.zero_float W)
      (JuliaLean.base.float.abs_float err))
    (decide (u.val % 2 = 0))
  let one := JuliaLean.base.int.lit W.uintTy 1
  let delta := if adjust then
      if JuliaLean.base.float.signbit_float err = JuliaLean.base.float.signbit_float res then
        one
      else
        JuliaLean.base.int.neg_int one
    else
      JuliaLean.base.int.lit W.uintTy 0
  let u := JuliaLean.base.int.add_int u delta
  return ops.narrow (JuliaLean.base.float.bitcast_to_float W u)

/--
Julia source: base/floatfuncs.jl:363-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
""" Splits a Float64 into a hi bit and a low bit where the high bit has 27 trailing 0s and the low bit has 26 trailing 0s"""
@inline function splitbits(x::Float64)
    hi = truncbits(x, 27)
    return hi, x-hi
end
```
-/
def splitbits_Float64 (truncbits : FV .f64 → Nat → FV .f64) (x : FV .f64) :
    FV .f64 × FV .f64 :=
  let hi := truncbits x 27
  (hi, JuliaLean.base.float.sub_float x hi)

/--
Julia source: base/floatfuncs.jl:371-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function two_mul(x::T, y::T) where {T<:Number}
    xy = x*y
    xy, fma(x, y, -xy)
end
```
-/
def two_mul_Number {N : Type} (mul : N → N → Jl N) (neg : N → Jl N)
    (fma : N → N → N → Jl N) (x y : N) : Jl (N × N) := do
  let xy ← mul x y
  let negativeXY ← neg xy
  let lo ← fma x y negativeXY
  pure (xy, lo)

structure Float64FmaOps where
  haveFma : Bool
  truncbits : FV .f64 → Nat → FV .f64
  isfinite : FV .f64 → Bool
  isinf : FV .f64 → Bool
  iszero : FV .f64 → Bool
  issubnormal : FV .f64 → Bool
  signbit : FV .f64 → Bool
  isless : FV .f64 → FV .f64 → Bool
  equal : FV .f64 → FV .f64 → Bool
  abs : FV .f64 → FV .f64
  add : FV .f64 → FV .f64 → FV .f64
  sub : FV .f64 → FV .f64 → FV .f64
  mul : FV .f64 → FV .f64 → FV .f64
  neg : FV .f64 → FV .f64
  nextfloat : FV .f64 → JInt .i64 → FV .f64
  ldexp : FV .f64 → JInt .i64 → FV .f64
  exponent : FV .f64 → JInt .i64
  cmpZero : FV .f64 → JInt .i64
  bits : FV .f64 → JInt .u64
  fromBits : JInt .u64 → FV .f64
  exponentMask : JInt .u64
  exponentOne : JInt .u64
  floatmin : FV .f64
  pow2_52 : FV .f64
  pow2_neg969 : FV .f64

/--
Julia source: base/floatfuncs.jl:376-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :consistent @inline function two_mul(x::Float64, y::Float64)
    if Core.Intrinsics.have_fma(Float64)
        xy = x*y
        return xy, fma_float(x, y, -xy)
    end
    # fma-free fallback; `fma_emulated` relies on this branch never calling `fma`
    xhi, xlo = splitbits(x)
    yhi, ylo = splitbits(y)
    xy = x*y
    ylohi, ylolo = splitbits(ylo)
    xylo = xlo*ylohi - (((xy - xhi*yhi) - xlo*yhi) - xhi*ylo) + ylolo*xlo
    return xy, xylo
end
```
-/
-- Source: base/floatfuncs.jl:376-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def twoMulFloat64Source (haveFma : Bool) (truncbits : FV .f64 → Nat → FV .f64)
    (add sub mul : FV .f64 → FV .f64 → FV .f64) (neg : FV .f64 → FV .f64)
    (x y : FV .f64) : FV .f64 × FV .f64 :=
  if haveFma then
    let xy := mul x y
    (xy, JuliaLean.C.jlFmaFloat x y (neg xy))
  else
    let (xhi, xlo) := splitbits_Float64 truncbits x
    let (yhi, ylo) := splitbits_Float64 truncbits y
    let xy := mul x y
    let (ylohi, ylolo) := splitbits_Float64 truncbits ylo
    let xylo := add
      (sub (mul xlo ylohi)
        (sub (sub (sub xy (mul xhi yhi)) (mul xlo yhi)) (mul xhi ylo)))
      (mul ylolo xlo)
    (xy, xylo)

def two_mul_Float64 (ops : Float64FmaOps) (x y : FV .f64) : FV .f64 × FV .f64 :=
  twoMulFloat64Source ops.haveFma ops.truncbits ops.add ops.sub ops.mul ops.neg x y

structure SmallTwoMulOps (T : FTy) where
  haveFma : Bool
  widen : FV T → FV (smallWidenedType T)
  narrow : FV (smallWidenedType T) → FV T

/--
Julia source: base/floatfuncs.jl:390-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :consistent @inline function two_mul(x::T, y::T) where T<:Union{Float16, Float32}
    if Core.Intrinsics.have_fma(T)
        xy = x*y
        return xy, fma(x, y, -xy)
    end
    xy = widen(x)*y
    Txy = T(xy)
    return Txy, T(xy-Txy)
end
```
-/
def two_mul_Small {T : FTy} (_format : T = .f16 ∨ T = .f32)
    (ops : SmallTwoMulOps T) (fma : FV T → FV T → FV T → FV T)
    (x y : FV T) : FV T × FV T :=
  if ops.haveFma then
    let xy := JuliaLean.base.float.mul_float x y
    (xy, fma x y (JuliaLean.base.float.neg_float xy))
  else
    let xy := JuliaLean.base.float.mul_float (ops.widen x) (ops.widen y)
    let Txy := ops.narrow xy
    (Txy, ops.narrow (JuliaLean.base.float.sub_float xy (ops.widen Txy)))

/--
Julia source: base/floatfuncs.jl:403-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function fma_correction(abhi::Float64, ablo::Float64, c::Float64, r::Float64)
    e = (abs(abhi) > abs(c)) ? (abhi-r+c) : (c-r+abhi) # exact
    s = e + ablo
    serr = (abs(e) > abs(ablo)) ? (e-s+ablo) : (ablo-s+e) # exact
    if !iszero(serr) && iseven(reinterpret(UInt64, s))
        s = nextfloat(s, serr > 0 ? 1 : -1)
    end
    return s
end
```
-/
def fma_correction (ops : Float64FmaOps) (abhi ablo c r : FV .f64) : FV .f64 :=
  let e := if ops.isless (ops.abs c) (ops.abs abhi) then
      ops.add (ops.sub abhi r) c
    else
      ops.add (ops.sub c r) abhi
  let s := ops.add e ablo
  let serr := if ops.isless (ops.abs ablo) (ops.abs e) then
      ops.add (ops.sub e s) ablo
    else
      ops.add (ops.sub ablo s) e
  if !ops.iszero serr && decide ((ops.bits s).val % 2 = 0) then
    ops.nextfloat s
      (if ops.isless (JuliaLean.base.float.zero_float .f64) serr then
        JuliaLean.base.int.lit .i64 1
      else
        JuliaLean.base.int.lit .i64 (-1))
  else
    s

def fmaEmulatedFinish (ops : Float64FmaOps) (abhi ablo c : FV .f64) : FV .f64 :=
  let r := ops.add abhi c
  let s := fma_correction ops abhi ablo c r
  ops.add r s

/--
Julia source: base/floatfuncs.jl:413-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fma_emulated(a::Float64, b::Float64,c::Float64)
    abhi, ablo = @inline two_mul(a, b)
    # two_mul is only exact if the low parts of a and b (and their product) don't underflow
    if !isfinite(abhi+c) || isless(abs(abhi), nextfloat(0x1p-969)) || isless(abs(a), 0x1p-969) || isless(abs(b), 0x1p-969)
        aandbfinite = isfinite(a) && isfinite(b)
        if !(isfinite(c) && aandbfinite)
            return aandbfinite ? c : abhi+c
        end
        (iszero(a) || iszero(b)) && return abhi+c
        # The checks above satisfy exponent's nothrow precondition
        bias = Math._exponent_finite_nonzero(a) + Math._exponent_finite_nonzero(b)
        c_denorm = ldexp(c, -bias)
        if isfinite(c_denorm)
            # rescale a and b to [1,2), equivalent to ldexp(a, -exponent(a))
            issubnormal(a) && (a *= 0x1p52)
            issubnormal(b) && (b *= 0x1p52)
            a = reinterpret(Float64, (reinterpret(UInt64, a) & ~Base.exponent_mask(Float64)) | Base.exponent_one(Float64))
            b = reinterpret(Float64, (reinterpret(UInt64, b) & ~Base.exponent_mask(Float64)) | Base.exponent_one(Float64))
            # If c underflowed when rescaled, it is far below every rounding boundary
            # of a*b, so only its sign matters (to break ties). Keep it nonzero.
            c = ldexp(c_denorm, bias) == c ? c_denorm : copysign(floatmin(Float64), c)
            abhi, ablo = two_mul(a, b)
            # abhi <= 4 -> isfinite(r)      (α)
            r = abhi+c
            # s ≈ 0                         (β)
            s = fma_correction(abhi, ablo, c, r)
            # α ⩓ β -> isfinite(sumhi)      (γ)
            sumhi = r+s
            # If result is subnormal, ldexp will cause double rounding because subnormals have fewer mantisa bits.
            # As such, we need to check whether round to even would lead to double rounding and manually round sumhi to avoid it.
            # This must be decided before rounding, which can carry the result to 0 or floatmin.
            # finite: See γ
            if !iszero(sumhi) && (bits_lost = -bias-Math._exponent_finite_nonzero(sumhi)-1022) > 0
                sumlo = r-sumhi+s
                sumhiInt = reinterpret(UInt64, sumhi)
                if (bits_lost != 1) ⊻ (sumhiInt&1 == 1)
                    sumhi = nextfloat(sumhi, cmp(sumlo, 0))
                end
            end
            return ldexp(sumhi, bias)
        end
        isinf(abhi) && signbit(c) == signbit(a*b) && return abhi
        # fall through
    end
    r = abhi+c
    s = fma_correction(abhi, ablo, c, r)
    return r+s
end
```
-/
def fma_emulated_Float64 (ops : Float64FmaOps) (a b c : FV .f64) : FV .f64 := Id.run do
  let (abhi, ablo) := two_mul_Float64 ops a b
  if !ops.isfinite (ops.add abhi c) ||
      ops.isless (ops.abs abhi) (ops.nextfloat ops.pow2_neg969 (JuliaLean.base.int.lit .i64 1)) ||
      ops.isless (ops.abs a) ops.pow2_neg969 ||
      ops.isless (ops.abs b) ops.pow2_neg969 then
    let aandbfinite := ops.isfinite a && ops.isfinite b
    if !(ops.isfinite c && aandbfinite) then
      return if aandbfinite then c else ops.add abhi c
    if ops.iszero a || ops.iszero b then
      return ops.add abhi c
    let bias := JuliaLean.base.int.add_int (ops.exponent a) (ops.exponent b)
    let cDenorm := ops.ldexp c (JuliaLean.base.int.neg_int bias)
    if ops.isfinite cDenorm then
      let a := if ops.issubnormal a then ops.mul a ops.pow2_52 else a
      let b := if ops.issubnormal b then ops.mul b ops.pow2_52 else b
      let aBits := JuliaLean.base.int.or_int
        (JuliaLean.base.int.and_int (ops.bits a) (JuliaLean.base.int.not_int ops.exponentMask))
        ops.exponentOne
      let bBits := JuliaLean.base.int.or_int
        (JuliaLean.base.int.and_int (ops.bits b) (JuliaLean.base.int.not_int ops.exponentMask))
        ops.exponentOne
      let a := ops.fromBits aBits
      let b := ops.fromBits bBits
      let c := if ops.equal (ops.ldexp cDenorm bias) c then cDenorm
        else copysign_Float64 ops.floatmin c
      let (abhi, ablo) := two_mul_Float64 ops a b
      let r := ops.add abhi c
      let s := fma_correction ops abhi ablo c r
      let sumhi := ops.add r s
      if !ops.iszero sumhi then
        let bitsLost := JuliaLean.base.int.sub_int
          (JuliaLean.base.int.sub_int (JuliaLean.base.int.neg_int bias) (ops.exponent sumhi))
          (JuliaLean.base.int.lit .i64 1022)
        if JuliaLean.base.int.slt_int (JuliaLean.base.int.lit .i64 0) bitsLost then
          let sumlo := ops.add (ops.sub r sumhi) s
          let sumhiInt := ops.bits sumhi
          let lostNotOne := !(JuliaLean.base.int.eq_int bitsLost (JuliaLean.base.int.lit .i64 1))
          let sumhiOdd := decide (sumhiInt.val % 2 = 1)
          if (lostNotOne && !sumhiOdd) || (!lostNotOne && sumhiOdd) then
            let sumhi := ops.nextfloat sumhi (ops.cmpZero sumlo)
            return ops.ldexp sumhi bias
      return ops.ldexp sumhi bias
    if ops.isinf abhi && ops.signbit c = ops.signbit (ops.mul a b) then
      return abhi
  return fmaEmulatedFinish ops abhi ablo c

/-- The three emulated `fma` implementations selected by the IEEE format. -/
structure FloatFmaOps where
  haveFma : FTy → Bool
  fma16 : SmallFmaOps .f16
  fma32 : SmallFmaOps .f32
  fma64 : Float64FmaOps

/--
Julia source: base/floatfuncs.jl:464-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :consistent function fma(x::T, y::T, z::T) where {T<:IEEEFloat}
    Core.Intrinsics.have_fma(T) ? fma_float(x,y,z) : fma_emulated(x,y,z)
end
```
-/
def fma_IEEEFloat {T : FTy} (ops : FloatFmaOps) (x y z : FV T) : FV T :=
  if ops.haveFma T then
    JuliaLean.C.jlFmaFloat x y z
  else
    match T with
    | .f16 => fmaEmulatedSmall (Or.inl rfl) ops.fma16 x y z
    | .f32 => fmaEmulatedSmall (Or.inr rfl) ops.fma32 x y z
    | .f64 => fma_emulated_Float64 ops.fma64 x y z

/-!
Julia source: base/floatfuncs.jl:468-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This is necessary at least on 32-bit Intel Linux, since fma_float may
# have called glibc, and some broken glibc fma implementations don't
# properly restore the rounding mode
Rounding.setrounding_raw(Float32, Rounding.JL_FE_TONEAREST)
Rounding.setrounding_raw(Float64, Rounding.JL_FE_TONEAREST)
```
-/
def initializeNearestRoundingRaw {S : Type} (setRaw : FTy → Int → S → S)
    (nearestCode : Int) (state : S) : S :=
  setRaw .f64 nearestCode (setRaw .f32 nearestCode state)
end JuliaLean.base.floatfuncs

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `copysign_float`; `base/floatfuncs.jl:5`. -/
def copysign (x y : F64) : F64 :=
  F64.ofBits (F64.toBits x % 2^63 + (if F64.signbit y then 2^63 else 0))

/-- `flipsign(x::Float64, y::Float64)`: xor with the sign of `y`; `base/floatfuncs.jl:10`. -/
def flipsign (x y : F64) : F64 := if F64.signbit y then F64.neg x else x

/-- `two_mul(x::Float64, y::Float64)` with hardware fma; `base/floatfuncs.jl:376-380`. -/
def twoMul (x y : F64) : F64 × F64 :=
  let xy := F64.mul x y
  (xy, F64.fma x y (F64.neg xy))

end JuliaLean.MathFuncs

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

/-- `round(x::IEEEFloat, r)` for every mode: `base/float.jl:458-461` (ToZero, Down, Up,
Nearest), `base/floatfuncs.jl:151-154` (NearestTiesAway, via `F64.round`),
`base/floatfuncs.jl:156-158` (NearestTiesUp) and `base/floatfuncs.jl:160-162` (FromZero). -/
def roundF (x : F64) : Mode → F64
  | .Nearest => F64.round x .RoundNearest
  | .NearestTiesAway => F64.round x .RoundNearestTiesAway
  | .ToZero => F64.round x .RoundToZero
  | .Up => F64.round x .RoundUp
  | .Down => F64.round x .RoundDown
  | .FromZero => if F64.signbit x then F64.round x .RoundDown else F64.round x .RoundUp
  | .NearestTiesUp =>
    -- copysign(floor((x + (T(0.25) - eps(T(0.5)))) + (T(0.25) + eps(T(0.5)))), x)
    let quarter := F64.ofBits 0x3fd0000000000000
    let e := F64.eps (F64.ofBits 0x3fe0000000000000)
    copysign (F64.floor (F64.add (F64.add x (F64.sub quarter e)) (F64.add quarter e))) x


/-- `_round_invstep(x, invstep, r)`; `base/floatfuncs.jl:82-88`. -/
def roundInvstep (x invstep : F64) (r : Mode) : F64 :=
  let y := F64.div (roundF (F64.mul x invstep) r) invstep
  if !F64.isfinite y then x else y

/-- `_round_invstepsqrt(x, invstepsqrt, r)`; `base/floatfuncs.jl:92-98`. -/
def roundInvstepsqrt (x s : F64) (r : Mode) : F64 :=
  let y := F64.div (F64.div (roundF (F64.mul (F64.mul x s) s) r) s) s
  if !F64.isfinite y then x else y

/-- `_round_step(x, step, r)`; `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : F64) (r : Mode) : F64 :=
  let y := F64.mul (roundF (F64.div x step) r) step
  if !F64.isfinite y then
    if F64.lt (F64.zero false) x then (if r = .Up then F64.inf false else F64.zero false)
    else if F64.lt x (F64.zero false) then (if r = .Down then F64.inf true else F64.zero true)
    else x
  else y

/-- `_round_digits(x, r, digits, 10)` for Float64 `x` and Int64 `digits`;
`base/floatfuncs.jl:116-130`. `digits/2` is the Float64 quotient of `/(::Int, ::Int)`. -/
def roundDigits (powFI : F64 → Int → F64) (powFF : F64 → F64 → Jl F64)
    (x : F64) (r : Mode) (digits : JInt .i64) : Jl F64 :=
  let ten := F64.ofInt 10
  if digits.val ≥ 0 then
    let invstep := powFI ten digits.val
    if F64.isfinite invstep then .ok (roundInvstep x invstep r)
    else do
      let s ← powFF ten (F64.div (F64.ofInt digits.val) (F64.ofInt 2))
      pure (roundInvstepsqrt x s r)
  else .ok (roundStep x (powFI ten (-digits).val) r)

/-- `hidigit(x::AbstractFloat, 10) = 1 + floor(Int, log10(abs(x)))`, zero for `x == 0`;
`base/floatfuncs.jl:133-136`. `floor(Int, y)` is `F64.floorInt .i64`. -/
def hidigit (log10 : F64 → Jl F64) (x : F64) : Jl (JInt .i64) :=
  if F64.iszero x then .ok (JInt.wrap .i64 0)
  else do
    let l ← log10 (F64.abs x)
    let f ← F64.floorInt .i64 l
    pure (JInt.wrap .i64 1 + f)

/-- `round(x, r; digits)` for Float64; `base/floatfuncs.jl:56-79` (`isfinite(x) || return x`). -/
def roundDigitsKw (powFI : F64 → Int → F64) (powFF : F64 → F64 → Jl F64)
    (x : F64) (r : Mode) (digits : JInt .i64) : Jl F64 :=
  if !F64.isfinite x then .ok x else roundDigits powFI powFF x r digits

/-- `round(x, r; sigdigits)` for Float64: `_round_sigdigits`, `base/floatfuncs.jl:145-148`,
behind the finiteness check of `base/floatfuncs.jl:68`. -/
def roundSigdigits (powFI : F64 → Int → F64) (powFF : F64 → F64 → Jl F64)
    (log10 : F64 → Jl F64) (x : F64) (r : Mode) (sigdigits : JInt .i64) : Jl F64 :=
  if !F64.isfinite x then .ok x
  else do
    let h ← hidigit log10 x
    roundDigits powFI powFF x r (sigdigits - h)

/-- `rtoldefault(Float64, Float64, atol)`: `sqrt(eps(Float64))` unless `atol > 0`;
`base/floatfuncs.jl:326,335-338`. -/
def rtolDefault (atol : F64) : F64 :=
  if F64.lt (F64.zero false) atol then F64.zero false else F64.ofBits 0x3e50000000000000

/-- `isapprox(x::Float64, y::Float64; atol, rtol, nans, norm=abs)`;
`base/floatfuncs.jl:230-237`. `max` is the `max_float` intrinsic (`MathFuncs.fmax`). -/
def isapproxF (fmax : F64 → F64 → F64) (x y atol rtol : F64) (nans : Bool) : Bool :=
  F64.eq x y ||
    (F64.isfinite x && F64.isfinite y &&
      F64.le (F64.abs (F64.sub x y))
        (fmax atol (F64.mul rtol (fmax (F64.abs x) (F64.abs y))))) ||
    (nans && F64.isnan x && F64.isnan y)

/-- `x ≈ y` with default keywords: `atol = zero(real(x))`, `rtol = rtoldefault(x, y, atol)`,
`nans = false`; `base/floatfuncs.jl:231-232,317`. -/
def approxDefault (fmax : F64 → F64 → F64) (x y : F64) : Bool :=
  isapproxF fmax x y (F64.zero false) (rtolDefault (F64.zero false)) false

/--
`isapprox(x::Int64, y::Int64; atol::Int64, rtol::Int64, norm=abs)` on master,
`base/floatfuncs.jl:289-300`:
`_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol, scale)...)`
promotes `rtol` to `UInt64` with `convert` (`base/floatfuncs.jl:287`); `max(atol, b)` with
`b::UInt64` is the mixed BitInteger `max`, `ifelse(x < y, y % R, x % R)` with an exact
mixed comparison (`base/int.jl:591-594`); `_uabsdiff(x, y) = unsigned(hi) - unsigned(lo)`
(`base/floatfuncs.jl:253-257`) and `_uabsdiff_le(x, y, b) = _uabsdiff(x, y) <= b`
(`base/floatfuncs.jl:275`).
-/
def isapproxI64 (x y atol rtol : JInt .i64) : Jl Bool :=
  if atol.val < 1 && rtol.val == 0 then .ok (x.val == y.val)
  else if x.val == y.val then .ok true
  else do
    let scale := max (uabs64 x) (uabs64 y)
    let r ← JInt.convert (IntTy.u64.name) .u64 rtol.val
    let prod := r.val.toNat * scale
    if prod ≥ 2^64 then pure true
    else do
      let bound : Nat := if atol.val < (prod : Int) then prod
        else (JInt.wrap .u64 atol.val).val.toNat
      let lo := min x.val y.val
      let hi := max x.val y.val
      let d := (JInt.wrap .u64 hi - JInt.wrap .u64 lo).val.toNat
      pure (decide (d ≤ bound))

end JuliaLean.FloatFuncs

namespace JuliaLean.ParsePrint.RoundDigits

open JuliaLean JuliaLean.Float

/-- `_round_step(x, step, r)`, `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : F64) (r : Rounding) : F64 :=
  let y := F64.mul (F64.round (F64.div x step) r) step
  if !F64.isfinite y then
    if F64.lt F64.zero x then (if r = .RoundUp then F64.inf else F64.zero)
    else if F64.lt x F64.zero then (if r = .RoundDown then F64.inf true else F64.zero true)
    else x
  else y

/-- `round(x, r; digits=-k)` for `k ≥ 1`, `base/floatfuncs.jl:73-74,126-128`, given
Julia's value `pow = 10.0^k` of the step. -/
def roundDigitsNeg (x pow : F64) (r : Rounding) : F64 :=
  if !F64.isfinite x then x else roundStep x pow r

end JuliaLean.ParsePrint.RoundDigits

namespace JuliaLean.MathCov.Bits

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatIntCov.Float (signMask exponentMask exponentOne significandBits
  exponentBits exponentBias exponentRawMax leadingZeros uintTy)

variable {T : FTy}

/-- `signbit(x::Float64/Float32/Float16) = signbit(bitcast(Int, x))`;
`base/floatfuncs.jl:15-17`. -/
def signbitBits (x : FV T) : Bool := decide (wrapInt (FloatIntCov.Float.intTy T) x.toBits < 0)

/-- `copysign(x::Float32, y::Float32) = copysign_float(x, y)`; `base/floatfuncs.jl:5-6`. -/
def copysignF (x y : FV T) : FV T := copysign x y

/-- `copysign(x::Float32/Float64, y::Real) = copysign(x, T(y))` for a float `y` of any
format; `base/floatfuncs.jl:7-8`. -/
def copysignReal {S : FTy} (x : FV T) (y : FV S) : FV T := copysign x (conv y)

/-- `flipsign(x::Float32, y::Float32)`: xor of the sign bits; `base/floatfuncs.jl:11`. -/
def flipsignF (x y : FV T) : FV T :=
  Fl.ofBits (Nat.xor x.toBits (y.toBits / signMask T % 2 * signMask T))

/-- `flipsign(x::Float32/Float64, y::Real) = flipsign(x, T(y))`; `base/floatfuncs.jl:12-13`. -/
def flipsignReal {S : FTy} (x : FV T) (y : FV S) : FV T := flipsignF x (conv y)

/-- `maxintfloat(::Type{T})` for the three formats; `base/floatfuncs.jl:34-36`. -/
def maxintfloat (T : FTy) : FV T := ofInt T (2 ^ (significandBits T + 1))

/-- `maxintfloat(x::T) = maxintfloat(T)`; `base/floatfuncs.jl:37`. -/
def maxintfloatOf (_x : FV T) : FV T := maxintfloat T

/-- `maxintfloat(::Type{S}, ::Type{T}) = min(maxintfloat(S), S(typemax(T)))` for an
integer type `t`; `base/floatfuncs.jl:46`. `min` is `min_float`. -/
def maxintfloatInt (S : FTy) (t : IntTy) : FV S :=
  let a := maxintfloat S
  let b : FV S := Fl.ofInt t.max
  if lt b a then b else a

/-- `maxintfloat() = maxintfloat(Float64)`; `base/floatfuncs.jl:47`. -/
def maxintfloatDefault : FV .f64 := maxintfloat .f64

/-- The two `Union{}` maxintfloat methods throw `MethodError`; `base/floatfuncs.jl:48-49`. -/
def maxintfloatBottom {α : Type} : Jl α := .error (.methodError "maxintfloat")

-- placed here to break an import cycle with base/math
/-- Bit width of `T`. -/
def width (T : FTy) : Nat := T.fmt.width

/-- `x +% y` on `Int64`. -/
def addWrap64 (a b : Int) : Int := wrapInt .i64 (a + b)

/-- `ldexp(x::T, e::Integer) where T<:IEEEFloat`; `base/math.jl:854-897`. The integer
`e` is the exact value of any `Integer` type. -/
def ldexp (x : FV T) (e : Int) : FV T := Id.run do
  let xu0 := x.toBits
  let xs := xu0 % signMask T
  if xs ≥ exponentMask T then return x
  let mut xu := xu0
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return x
    let m := leadingZeros (width T) xs - exponentBits T
    let ys := xs * 2 ^ m
    xu := ys + (if x.signbit then signMask T else 0)
    k := 1 - (m : Int)
    if e < -50000 then return flipsign (zero T) x
  if e > IntTy.max .i64 then return flipsign (inf T) x
  else if e < IntTy.min .i64 then return flipsign (zero T) x
  let n := wrapInt .i64 e
  k := addWrap64 k n
  if k ≥ exponentRawMax T then return flipsign (inf T) x
  if k > 0 then
    xu := (xu % 2 ^ significandBits T) + (if xu ≥ signMask T then signMask T else 0)
      + k.toNat * 2 ^ significandBits T
    return Fl.ofBits xu
  else
    if k ≤ -((significandBits T : Int)) - 1 then
      if e > 50000 then return flipsign (inf T) x
      return flipsign (zero T) x
    k := k + significandBits T + 1
    let z : FV T := Fl.ofBits ((exponentBias T - significandBits T - 1) * 2 ^ significandBits T)
    xu := (xu % 2 ^ significandBits T) + (if xu ≥ signMask T then signMask T else 0)
      + k.toNat * 2 ^ significandBits T
    return mul z (Fl.ofBits xu)

/-- `ldexp(x::Float16, q::Integer) = Float16(ldexp(Float32(x), q))`; `base/math.jl:898`. -/
def ldexp16 (x : FV .f16) (q : Int) : FV .f16 := conv (ldexp (conv x : FV .f32) q)

/-- `throw1(x)` and `throw2(x)` inside `exponent`; `base/math.jl:937-938`. -/
def exponentThrow1 : Jl Int := .error (.domainError "Cannot be NaN or Inf.")
def exponentThrow2 : Jl Int := .error (.domainError "Cannot be ±0.0.")

/-- `exponent(x::T) where T<:IEEEFloat`; `base/math.jl:936-950`. -/
def exponent (x : FV T) : Jl Int :=
  let xs := x.toBits % signMask T
  if xs ≥ exponentMask T then exponentThrow1
  else
    let k : Int := (xs / 2 ^ significandBits T : Nat)
    if k == 0 then
      if xs == 0 then exponentThrow2
      else
        let m : Int := (leadingZeros (width T) xs : Int) - exponentBits T
        .ok ((1 - m) - exponentBias T)
    else .ok (k - exponentBias T)

/-- `_exponent_finite_nonzero(x::T)`; `base/math.jl:956-965`. -/
def exponentFiniteNonzero (x : FV T) : Int :=
  let xs := x.toBits % signMask T
  let k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    let m : Int := (leadingZeros (width T) xs : Int) - exponentBits T
    (1 - m) - exponentBias T
  else k - exponentBias T

end JuliaLean.MathCov.Bits

namespace JuliaLean.MathCov.Exp

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP

/-- `two_mul(x, y)` with hardware fma for `Float32`/`Float16`; `base/floatfuncs.jl:390-394`. -/
def twoMulG {T : FTy} (x y : FV T) : FV T × FV T :=
  let xy := mul x y
  (xy, fma x y (neg xy))

end JuliaLean.MathCov.Exp


/-!
Methods of `base/floatfuncs.jl` at Julia master `bbfa0ce4150` not modelled by the
`FloatFuncs` area, generic over the three IEEE formats: the `round` keyword dispatcher,
`_round_invstep`, `_round_invstepsqrt`, `hidigit`, `_round_sigdigits`, the three
non-intrinsic rounding modes, `isapprox` and its integer helpers, `rtoldefault`,
`fma_emulated`, `splitbits`, `two_mul`, `fma_correction` and `fma`.
-/

namespace JuliaLean.MathCov.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatFuncs (Mode)

variable {T : FTy}

/-- `round(x::T, r)` for the four `llvm` modes (`base/float.jl:458-461`) and the three
`base/floatfuncs.jl` methods below. -/
def roundM (x : FV T) : Mode → FV T
  | .Nearest => roundI x .RoundNearest
  | .ToZero => trunc x
  | .Up => ceil x
  | .Down => floor x
  | .NearestTiesAway =>
    let y := trunc x
    if eq x y then y else trunc (sub (mul (ofInt T 2) x) y)
  | .NearestTiesUp =>
    let q : FV T := div (one T) (ofInt T 4)
    let e := epsOf (div (one T) (ofInt T 2))
    copysign (floor (add (add x (sub q e)) (add q e))) x
  | .FromZero => if x.signbit then floor x else ceil x

/-- `round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway})`; `base/floatfuncs.jl:151-154`. -/
def roundTiesAway (x : FV T) : FV T := roundM x .NearestTiesAway
/-- `round(x::T, ::RoundingMode{:NearestTiesUp})`; `base/floatfuncs.jl:156-158`. -/
def roundTiesUp (x : FV T) : FV T := roundM x .NearestTiesUp
/-- `round(x::AbstractFloat, ::typeof(RoundFromZero))`; `base/floatfuncs.jl:160-162`. -/
def roundFromZero (x : FV T) : FV T := roundM x .FromZero

/-- `_round_invstep(x, invstep, r)`; `base/floatfuncs.jl:82-88`. -/
def roundInvstep (x invstep : FV T) (r : Mode) : FV T :=
  let y := div (roundM (mul x invstep) r) invstep
  if !y.isfinite then x else y

/-- `_round_invstepsqrt(x, invstepsqrt, r)`; `base/floatfuncs.jl:92-98`. -/
def roundInvstepsqrt (x s : FV T) (r : Mode) : FV T :=
  let y := div (div (roundM (mul (mul x s) s) r) s) s
  if !y.isfinite then x else y

/-- `_round_step(x, step, r)`; `base/floatfuncs.jl:101-114`. -/
def roundStep (x step : FV T) (r : Mode) : FV T :=
  let y := mul (roundM (div x step) r) step
  if !y.isfinite then
    if lt (zero T) x then (if r = .Up then inf T else zero T)
    else if lt x (zero T) then (if r = .Down then inf T true else zero T true)
    else x
  else y

/-- `_round_digits(x, r, digits, base)` for a float `x`; `base/floatfuncs.jl:116-130`. -/
def roundDigits (powI : FV T → Int → FV T) (powF : FV T → FV T → Jl (FV T))
    (x : FV T) (r : Mode) (digits base : Int) : Jl (FV T) :=
  let b := ofInt T base
  if digits ≥ 0 then
    let invstep := powI b digits
    if invstep.isfinite then .ok (roundInvstep x invstep r)
    else do
      let s ← powF b (conv (div (ofInt .f64 digits) (ofInt .f64 2)))
      return roundInvstepsqrt x s r
  else .ok (roundStep x (powI b (-digits)) r)

/-- `floor(Int, y)`: `InexactError` outside `Int64`. -/
def floorInt (y : FV T) : Jl Int :=
  let f := floor y
  if f.isfinite && IntTy.min .i64 ≤ f.truncVal && f.truncVal ≤ IntTy.max .i64 then .ok f.truncVal
  else .error (.inexactError "Int64")

/-- `hidigit(x::AbstractFloat, base)` for `base = 10` and `base = 2`; `log(base, abs(x))`
for other bases is `logBase`; `base/floatfuncs.jl:133-142`. -/
def hidigit (log10T : FV T → Jl (FV T))
    (x : FV T) (base : Int) (logBase : FV T → Jl (FV T)) : Jl Int := do
  if x.iszero then return 0
  if base == 10 then return 1 + (← floorInt (← log10T (abs x)))
  else if base == 2 then return 1 + (← Bits.exponent x)
  else return 1 + (← floorInt (← logBase (abs x)))

def hidigitInt (ndigits0z : Int → Nat → Nat) (x : Int) (b : Nat) : Nat := ndigits0z x b

/-- `hidigit(x::Real, base) = hidigit(float(x), base)`; `base/floatfuncs.jl:143`. -/
def hidigitReal (log10T : FV T → Jl (FV T)) {α : Type} (float : α → FV T) (x : α) (base : Int) (lb : FV T → Jl (FV T)) : Jl Int :=
  hidigit log10T (float x) base lb

/-- `_round_sigdigits(x, r, sigdigits, base)`; `base/floatfuncs.jl:145-148`. -/
def roundSigdigits (powI : FV T → Int → FV T) (powF : FV T → FV T → Jl (FV T))
    (log10T : FV T → Jl (FV T)) (x : FV T) (r : Mode) (sigdigits base : Int) (lb : FV T → Jl (FV T)) :
    Jl (FV T) := do
  let h ← hidigit log10T x base lb
  roundDigits powI powF x r (sigdigits - h) base

/-- `round(x::Real, r; digits, sigdigits, base)` for a float `x`; `base/floatfuncs.jl:56-79`.
`none` is `nothing`; `round(x, r)` without keywords is `roundM`. -/
def roundKw (powI : FV T → Int → FV T) (powF : FV T → FV T → Jl (FV T))
    (log10T : FV T → Jl (FV T)) (x : FV T) (r : Mode) (digits sigdigits base : Option Int)
    (lb : FV T → Jl (FV T)) : Jl (FV T) :=
  match digits, sigdigits with
  | none, none =>
    match base with
    | none => .error (.methodError "round")
    | some _ => .ok (roundM x r)
  | none, some s => if !x.isfinite then .ok x else roundSigdigits powI powF log10T x r s (base.getD 10) lb
  | some d, none => if !x.isfinite then .ok x else roundDigits powI powF x r d (base.getD 10)
  | some _, some _ => .error (.argumentError "`round` cannot use both `digits` and `sigdigits` arguments.")

/-! ## isapprox -/

/-- The exact value of a finite float as a rational; `none` for nonfinite values. -/
def ratOf (x : FV T) : Option (Int × Nat) := if x.isfinite then some x.toRat else none

/-- `isapprox(x::Number, y::Number; atol, rtol, nans, norm=abs)` for floats of one format
with float tolerances: `x == y || (isfinite(x) && isfinite(y) && abs(x-y) <=
max(atol, rtol*max(abs(x), abs(y)))) || (nans && isnan(x) && isnan(y))`;
`base/floatfuncs.jl:230-237`. `max` is `max_float`. -/
def isapproxF (maxFloat : FV T → FV T → FV T) (x y atol rtol : FV T) (nans : Bool) : Bool :=
  eq x y ||
    (x.isfinite && y.isfinite &&
      le (abs (sub x y)) (maxFloat atol (mul rtol (maxFloat (abs x) (abs y))))) ||
    (nans && x.isnan && y.isnan)

/-- `rtoldefault(::Type{T}) = sqrt(eps(T))` for a float type; `base/floatfuncs.jl:326`. -/
def rtoldefaultT (T : FTy) : FV T := sqrtLlvm (epsT T)
/-- `rtoldefault(::Type{<:Real}) = 0`; `base/floatfuncs.jl:327`. -/
def rtoldefaultReal : Int := 0
/-- `rtoldefault(::Type{T}) where {T<:Number}`: recurse into `typeof(one(T))`, throwing
`MethodError` when it is `T` itself; `base/floatfuncs.jl:330-334`. -/
def rtoldefaultNumber {τ : Type} [DecidableEq τ] (oneType : τ → τ) (rt : τ → Jl (FV .f64))
    (t : τ) : Jl (FV .f64) :=
  if oneType t = t then .error (.methodError "rtoldefault") else rt (oneType t)
/-- `rtoldefault(x, y, atol)`: `max` of the two type defaults, zero if `atol > 0`;
`base/floatfuncs.jl:335-338`. Each default is a float of the format or `0` (`none`). -/
def rtoldefault3 (maxFloat : FV T → FV T → FV T) (rx ry : Option (FV T)) (atolPos : Bool) : Option (FV T) :=
  let m := match rx, ry with
    | some a, some b => some (maxFloat a b)
    | some a, none => some a
    | none, some b => some b
    | none, none => none
  if atolPos then (m.map fun _ => zero T) else m

/-- An integer argument of `isapprox`: its type (`none` for `Bool`) and value. -/
structure IntArg where
  ty : Option IntTy
  val : Int

/-- `_uabsdiff(x, y)` on integers: the exact absolute difference (`base/floatfuncs.jl:244-273`);
each fixed-width method computes it in its unsigned type, widening on carry. -/
def uabsdiff (x y : Int) : Int := if x < y then y - x else x - y

/-- `_uabsdiff(x::BitUnsigned, y::BitUnsigned)`: `hi - lo` in the promoted unsigned type. -/
def uabsdiffUU (t : IntTy) (x y : Int) : Int := wrapInt t (max x y - min x y)

/-- `_uabsdiff(x::BitSigned, y::BitSigned)`: `unsigned(hi) - unsigned(lo)` in the promoted
type's unsigned counterpart. -/
def uabsdiffSS (t : IntTy) (x y : Int) : Int :=
  let u := t.toUnsigned
  wrapInt u (wrapInt u (max x y) - wrapInt u (min x y))

/-- `_mixed_uabsdiff(x::BitSigned, y::BitUnsigned)` returning `(m, u, d, carried)` in
`U = promote_type(unsigned(typeof(x)), typeof(y))`; `base/floatfuncs.jl:261-267`. -/
def mixedUabsdiff (U : IntTy) (x y : Int) : Int × Int × Int × Bool :=
  let v := wrapInt U x
  let u := wrapInt U y
  let d := if x < y then wrapInt U (u - v) else wrapInt U (v - u)
  (wrapInt U (-v), u, d, x < 0 && d < u)

/-- `_uabsdiff(x::BitSigned, y::BitUnsigned)`; `base/floatfuncs.jl:269-272`. -/
def uabsdiffSU (U : IntTy) (x y : Int) : Int :=
  let (m, u, d, carried) := mixedUabsdiff U x y
  if carried then m + u else d

/-- `_uabsdiff_le(x::BitSigned, y::BitUnsigned, b)` for a bound `b` given as an exact
rational (`lean` of `b > typemax(d)` and `d <= b` compare exactly);
`base/floatfuncs.jl:275-284`. -/
def uabsdiffLeSU (U : IntTy) (x y : Int) (bNum : Int) (bDen : Nat) : Bool :=
  let (m, u, d, carried) := mixedUabsdiff U x y
  let le (a : Int) : Bool := decide (a * (bDen : Int) ≤ bNum)
  if carried && !(le U.max) then le (m + u)
  else le d && !carried

/-- `_uabsdiff_le(x::Integer, y::Integer, b::Real)` for an integral bound. -/
def uabsdiffLe (x y bound : Int) : Bool := decide (uabsdiff x y ≤ bound)

/-- `_widesum_le(m, u, b)` for an integral bound. -/
def widesumLe (m u bound : Int) : Bool := decide (m + u ≤ bound)

/-- `_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol,
scale)...)`; `base/floatfuncs.jl:287`. Returns the wrapped product and the overflow flag. -/
def scaledRtolInt (t : IntTy) (rtol scale : Int) : Int × Bool :=
  let p := wrapInt t rtol * wrapInt t scale
  (wrapInt t p, decide (wrapInt t p ≠ p))

/-- `_scaled_rtol(rtol::Real, scale::Integer) = (rtol * scale, false)`; `base/floatfuncs.jl:286`. -/
def scaledRtolReal {α : Type} (mulα : α → Int → α) (rtol : α) (scale : Int) : α × Bool :=
  (mulα rtol scale, false)

/-- The `norm === abs` branch of integer `isapprox`; `base/floatfuncs.jl:289-303`.
The fixed-width type `t` controls the overflow-aware tolerance product. -/
def isapproxInt (t : IntTy) (x y atol rtol : Int) : Bool :=
  if atol < 1 && rtol == 0 then x == y
  else if x == y then true
  else
    let (bound, overflowed) := scaledRtolInt t rtol (max x.natAbs y.natAbs)
    overflowed || decide (uabsdiff x y ≤ max atol bound)

/-- `isapprox(y; kwargs...) = x -> isapprox(x, y; kwargs...)`; `base/floatfuncs.jl:315`. -/
def isapproxCurried {α : Type} (approx : α → α → Bool) (y : α) : α → Bool := fun x => approx x y

/-- `≉(args...; kws...) = !≈(args...; kws...)`; `base/floatfuncs.jl:323`. -/
def napprox {α : Type} (approx : α → α → Bool) (x y : α) : Bool := !approx x y

/-! ## fma and its emulation -/

/-- `two_mul(x::T, y::T) where {T<:Number} = (x*y, fma(x, y, -x*y))`; `base/floatfuncs.jl:371-374`;
and `two_mul(x::T, y::T)` for `Float16`/`Float32` with hardware fma (`base/floatfuncs.jl:390-394`). -/
def twoMul (x y : FV T) : FV T × FV T := Exp.twoMulG x y

/-- The fma-free branch of `two_mul(x::Float16/Float32)`: `xy = widen(x)*y`, `(T(xy),
T(xy - T(xy)))`; `base/floatfuncs.jl:395-397`. -/
def twoMulNoFma (x y : FV T) : FV T × FV T :=
  let xy : FV .f64 := mul (conv x) (conv y)
  let txy : FV T := conv xy
  (txy, conv (sub xy (conv txy)))

/-- `truncbits(x, 27)`: clear the low 27 significand bits; `base/twiceprecision.jl:33-35`. -/
def truncbits27 (x : FV .f64) : FV .f64 := Fl.ofBits (x.toBits / 2 ^ 27 * 2 ^ 27)

/-- `splitbits(x::Float64) = (hi, x - hi)`; `base/floatfuncs.jl:364-367`. -/
def splitbits (x : FV .f64) : FV .f64 × FV .f64 := let hi := truncbits27 x; (hi, sub x hi)

/-- `two_mul(x::Float64, y::Float64)`; `base/floatfuncs.jl:376-388`. `hasFma` is
`Core.Intrinsics.have_fma(Float64)` (true on the x86-64 worker). -/
def twoMul64 (hasFma : Bool) (x y : FV .f64) : FV .f64 × FV .f64 :=
  if hasFma then let xy := mul x y; (xy, fma x y (neg xy))
  else
    let (xhi, xlo) := splitbits x
    let (yhi, ylo) := splitbits y
    let xy := mul x y
    let (ylohi, ylolo) := splitbits ylo
    let xylo := add (sub (mul xlo ylohi) (sub (sub (sub xy (mul xhi yhi)) (mul xlo yhi)) (mul xhi ylo)))
      (mul ylolo xlo)
    (xy, xylo)

/-- `fma_emulated(a::T, b::T, c::T)` for `T = Float16, Float32` (round to odd in the
wider type); `base/floatfuncs.jl:350-361`. -/
def fmaEmulatedNarrow (a b c : FV T) : FV T :=
  let W := Special.widenTy T
  let ab : FV W := mul (conv a) (conv b)
  let res : FV W := add ab (conv c)
  let bb := sub res ab
  let err := add (sub ab (sub res bb)) (sub (conv c) bb)
  let u := res.toBits
  let adjust := lt (zero W) (abs err) && u % 2 == 0
  let u' := if adjust then (if err.signbit == res.signbit then u + 1 else u + 2 ^ W.fmt.width - 1) else u
  conv (Fl.ofBits u' : FV W)

/-- `fma_correction(abhi, ablo, c, r)`; `base/floatfuncs.jl:403-411`. -/
def fmaCorrection (abhi ablo c r : FV .f64) : FV .f64 :=
  let e := if lt (abs c) (abs abhi) then add (sub abhi r) c else add (sub c r) abhi
  let s := add e ablo
  let serr := if lt (abs ablo) (abs e) then add (sub e s) ablo else add (sub ablo s) e
  if !serr.iszero && s.toBits % 2 == 0 then nextfloat s (if lt (zero .f64) serr then 1 else -1)
  else s

/-- `isless(abs(x), c)` for the thresholds of `fma_emulated`. -/
def isless64 (x y : FV .f64) : Bool := Fl.isless x y

/-- `fma_emulated(a::Float64, b::Float64, c::Float64)`; `base/floatfuncs.jl:413-460`. -/
def fmaEmulated64 (hasFma : Bool) (a b c : FV .f64) : FV .f64 := Id.run do
  let (abhi, ablo) := twoMul64 hasFma a b
  let t969 : FV .f64 := lit .f64 0x0360000000000000
  if !(add abhi c).isfinite || isless64 (abs abhi) (nextfloat t969) ||
      isless64 (abs a) t969 || isless64 (abs b) t969 then
    let aandbfinite := a.isfinite && b.isfinite
    if !(c.isfinite && aandbfinite) then return (if aandbfinite then c else add abhi c)
    if a.iszero || b.iszero then return add abhi c
    let bias := Bits.exponentFiniteNonzero a + Bits.exponentFiniteNonzero b
    let cDenorm := Bits.ldexp c (-bias)
    if cDenorm.isfinite then
      let a := if FloatIntCov.Float.isSubnormal a then mul a (lit .f64 0x4330000000000000) else a
      let b := if FloatIntCov.Float.isSubnormal b then mul b (lit .f64 0x4330000000000000) else b
      let a : FV .f64 := Fl.ofBits (a.toBits % 2 ^ 52 + (if a.signbit then 2 ^ 63 else 0) + 0x3ff0000000000000)
      let b : FV .f64 := Fl.ofBits (b.toBits % 2 ^ 52 + (if b.signbit then 2 ^ 63 else 0) + 0x3ff0000000000000)
      let c := if eq (Bits.ldexp cDenorm bias) c then cDenorm else copysign (floatminT .f64) c
      let (abhi, ablo) := twoMul64 hasFma a b
      let r := add abhi c
      let s := fmaCorrection abhi ablo c r
      let mut sumhi := add r s
      if !sumhi.iszero then
        let bitsLost := -bias - Bits.exponentFiniteNonzero sumhi - 1022
        if bitsLost > 0 then
          let sumlo := add (sub r sumhi) s
          if (bitsLost != 1) != (sumhi.toBits % 2 == 1) then
            sumhi := nextfloat sumhi (if lt (zero .f64) sumlo then 1 else if lt sumlo (zero .f64) then -1 else 0)
      return Bits.ldexp sumhi bias
    if abhi.isinf && c.signbit == (mul a b).signbit then return abhi
  let r := add abhi c
  let s := fmaCorrection abhi ablo c r
  return add r s

/-- `fma(x::T, y::T, z::T) where {T<:IEEEFloat}`: `have_fma(T) ? fma_float : fma_emulated`;
`base/floatfuncs.jl:464-466`. -/
def fmaDispatch (hasFma : Bool) (x y z : FV T) : FV T :=
  if hasFma then fma x y z
  else match T, x, y, z with
    | .f64, x, y, z => fmaEmulated64 false x y z
    | _, x, y, z => fmaEmulatedNarrow x y z

end JuliaLean.MathCov.FloatFuncs

namespace JuliaLean.MathFuncs

/-- Float32 sign-copy intrinsic; `base/floatfuncs.jl:6`. -/
def copysign32 (x y : F32) : F32 :=
  BitVec.ofNat 32 (x.toNat % 2^31 + (if F32.signbit y then 2^31 else 0))

end JuliaLean.MathFuncs
