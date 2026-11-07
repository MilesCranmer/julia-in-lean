import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.float
import JuliaLean.base.gmp
import JuliaLean.base.mpfr
import JuliaLean.Spec.Pi
import JuliaLean.base.rational
import JuliaLean.base.reduce
/-!
# Model of `base/irrationals.jl`

Typed source models at Julia f755f49a9e41380d7da126b3c1db9fe7f83dd027.
`Irrational symbol` is Julia's zero-field singleton type. AbstractIrrational
methods stay polymorphic over user-defined types and their conversions.
The precision-search loops use the shared fuel-free loop semantics. None is
divergence; terminating results retain MPFR state and Julia exceptions.
-/
namespace JuliaLean.base.irrationals
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
abbrev BigFloat := JuliaLean.base.mpfr.BigFloat
abbrev Clong := JInt .i64
abbrev M := JuliaLean.base.mpfr.M
abbrev Context := JuliaLean.base.mpfr.Context
abbrev Run (A : Type) := Context → Option (Jl A × Context)

/-- The exact Union{Float32,Float64} domain of the directed conversion methods. -/
inductive IEEE32Or64 where
  | f32 | f64
  deriving DecidableEq, Repr

def IEEE32Or64.ty : IEEE32Or64 → FTy
  | .f32 => .f32
  | .f64 => .f64


/--
Julia source: base/irrationals.jl:29-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Irrational{sym} <: AbstractIrrational end

typemin(::Type{T}) where {T<:Irrational} = T()
typemax(::Type{T}) where {T<:Irrational} = T()
```
-/
structure Irrational (symbol : String) where
  deriving DecidableEq, Repr, Inhabited

def typemin (symbol : String) : Irrational symbol := ⟨⟩
def typemax (symbol : String) : Irrational symbol := ⟨⟩

/--
Julia source: base/irrationals.jl:34-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, x::Irrational{sym}) where {sym} = print(io, sym)

function show(io::IO, ::MIME"text/plain", x::Irrational{sym}) where {sym}
    if get(io, :compact, false)::Bool
        print(io, sym)
    else
        print(io, sym, " = ", string(float(x))[1:min(end,15)], "...")
    end
end
```
-/
def showSymbol {IO : Type} (print : IO → String → Jl IO)
    (io : IO) (_x : Irrational symbol) : Jl IO := print io symbol

def showPlain {IO A : Type} (compact : IO → Jl Bool)
    (floatString : A → Jl String) (print : IO → String → Jl IO)
    (symbol : String) (io : IO) (x : A) : Jl IO := do
  if ← compact io then print io symbol else
    let text ← floatString x
    print io (symbol ++ " = " ++ String.ofList (text.toList.take 15) ++ "...")

/--
Julia source: base/irrationals.jl:44-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{<:AbstractIrrational}, ::Type{Float16}) = Float16
promote_rule(::Type{<:AbstractIrrational}, ::Type{Float32}) = Float32
promote_rule(::Type{<:AbstractIrrational}, ::Type{<:AbstractIrrational}) = Float64
promote_rule(::Type{<:AbstractIrrational}, ::Type{T}) where {T<:Real} = promote_type(Float64, T)

function promote_rule(::Type{S}, ::Type{T}) where {S<:AbstractIrrational,T<:Number}
    U = promote_type(S, real(T))
    if S <: U
        # prevent infinite recursion
        promote_type(Float64, T)
    else
        promote_type(U, T)
    end
end
```
-/
def promoteFloat16 : FTy := .f16
def promoteFloat32 : FTy := .f32
def promoteIrrationals : FTy := .f64
def promoteReal {T : Type} (promoteFloat64 : T → Jl T) (t : T) := promoteFloat64 t

def promoteNumber {T : Type} (real : T → Jl T) (promote : T → T → Jl T)
    (float64 : T) (subtype : T → T → Bool) (s t : T) : Jl T := do
  let u ← promote s (← real t)
  if subtype s u then promote float64 t else promote u t

/--
Julia source: base/irrationals.jl:59-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractFloat(x::AbstractIrrational) = Float64(x)::Float64
Float16(x::AbstractIrrational) = Float16(Float32(x)::Float32)
Complex{T}(x::AbstractIrrational) where {T<:Real} = Complex{T}(T(x))
```
-/
def abstractFloat {A : Type} (convert : A → Jl (FV .f64)) (x : A) := convert x
def float16 {A : Type} (convert : A → Jl (FV .f32)) (x : A) : Jl (FV .f16) := do
  return convertFloat .f16 (← convert x)
def complex {A T C : Type} (convert : A → Jl T) (complex : T → Jl C) (x : A) : Jl C := do
  complex (← convert x)

def loopM {S A : Type} (step : S → M (Sum A S)) (initial : S) : Run A := fun state =>
  let result : Option (Except Empty (Jl A × Context)) :=
    JuliaLean.base.reduce.whileLoop (fun (s,state) =>
      let (result,state) := (step s).run state
      pure (match result with
        | .error error => .inl (.error error,state)
        | .ok (.inl value) => .inl (.ok value,state)
        | .ok (.inr next) => .inr (next,state))) (initial,state)
  result.map (fun result => match result with | .ok pair => pair | .error impossible => nomatch impossible)

def withRunRounding (mode : JuliaLean.base.mpfr.Mode) (action : Run A) : Run A := fun state =>
  let previous := state.scopedRounding
  (action { state with scopedRounding := some mode }).map
    (fun (result,after) => (result,{ after with scopedRounding := previous }))


/--
Julia source: base/irrationals.jl:63-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _irrational_to_rational_at_current_precision(::Type{T}, x::AbstractIrrational) where {T <: Integer}
    bx = BigFloat(x)
    r = rationalize(T, bx, tol = 0)
    if abs(BigFloat(r) - bx) > eps(bx)
        r
    else
        nothing  # Error is too small, repeat with greater precision.
    end
end
function _irrational_to_rational_at_precision(::Type{T}, x::AbstractIrrational, p::Int) where {T <: Integer}
    f = let x = x
        () -> _irrational_to_rational_at_current_precision(T, x)
    end
    setprecision(f, BigFloat, p)
end
```
-/
def rationalAtCurrentPrecision {A R : Type} (big : A → M BigFloat)
    (rationalize : BigFloat → M R) (bigRational : R → M BigFloat)
    (abs eps : BigFloat → M BigFloat) (x : A) : M (Option R) := do
  let bx ← big x
  let r ← rationalize bx
  let converted ← bigRational r
  let diff ← abs (← JuliaLean.base.mpfr.arithmetic .sub converted bx)
  let tolerance ← eps bx
  if JuliaLean.base.mpfr.less tolerance diff then return some r else return none

def rationalAtPrecision {A R : Type} (atCurrent : A → M (Option R))
    (x : A) (p : Clong) : M (Option R) :=
  JuliaLean.base.mpfr.withPrecision (fun (p : Clong) (_base : Unit) => pure p)
    (atCurrent x) p ()

/--
Julia source: base/irrationals.jl:78-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _irrational_to_rational_at_current_rounding_mode(::Type{T}, x::AbstractIrrational) where {T <: Integer}
    if T <: BigInt
        _throw_argument_error_irrational_to_rational_bigint()  # avoid infinite loop
    end
    p = 256
    while true
        r = _irrational_to_rational_at_precision(T, x, p)
        if r isa Number
            return r
        end
        p += 32
    end
end
function _irrational_to_rational(::Type{T}, x::AbstractIrrational) where {T <: Integer}
    f = let x = x
        () -> _irrational_to_rational_at_current_rounding_mode(T, x)
    end
    setrounding(f, BigFloat, RoundNearest)
end
Rational{T}(x::AbstractIrrational) where {T<:Integer} = _irrational_to_rational(T, x)
_throw_argument_error_irrational_to_rational_bigint() = throw(ArgumentError("Cannot convert an AbstractIrrational to a Rational{BigInt}: use rationalize(BigInt, x) instead"))
Rational{BigInt}(::AbstractIrrational) = _throw_argument_error_irrational_to_rational_bigint()
```
-/
def throwRationalBigInt {R : Type} : M R :=
  throw (.argumentError "Cannot convert an AbstractIrrational to a Rational{BigInt}: use rationalize(BigInt, x) instead")

def rationalAtCurrentRounding {A R : Type} (targetBigInt : Bool)
    (atPrecision : A → Clong → M (Option R)) (x : A) : Run R :=
  if targetBigInt then fun state => some ((throwRationalBigInt : M R).run state)
  else loopM (fun p => do
    let r ← atPrecision x p
    match r with
    | some r => return .inl r
    | none => return .inr (p+JInt.wrap .i64 32)) (JInt.wrap .i64 256)

def irrationalToRational {A R : Type} (atCurrentRounding : A → Run R) (x : A) : Run R :=
  withRunRounding .nearest (atCurrentRounding x)
def rational {A R : Type} (convert : A → Run R) (x : A) : Run R := convert x
def rationalBigInt {A R : Type} (_x : A) : M R := throwRationalBigInt

/--
Julia source: base/irrationals.jl:101-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _irrational_to_float(::Type{T}, x::AbstractIrrational, r::RoundingMode) where T<:Union{Float32,Float64}
    setprecision(BigFloat, 256) do
        T(BigFloat(x)::BigFloat, r)
    end
end
(::Type{T})(x::AbstractIrrational, r::RoundingMode) where {T<:Union{Float32,Float64}} = _irrational_to_float(T, x, r)
```
-/
def irrationalToFloat {A : Type} (T : IEEE32Or64) (big : A → M BigFloat)
    (x : A) (r : RoundingMode) : M (FV T.ty) :=
  JuliaLean.base.mpfr.withPrecision (fun (p : Clong) (_ : Unit) => pure p)
    (do return JuliaLean.base.mpfr.toIEEE T.ty (← big x) r) (JInt.wrap .i64 256) ()
def floatWithRounding {A : Type} (T : IEEE32Or64) (big : A → M BigFloat)
    (x : A) (r : RoundingMode) := irrationalToFloat T big x r

/--
Julia source: base/irrationals.jl:108-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{<:AbstractIrrational}) = Float64

==(::Irrational{s}, ::Irrational{s}) where {s} = true
==(::AbstractIrrational, ::AbstractIrrational) = false

<(::Irrational{s}, ::Irrational{s}) where {s} = false
function <(x::AbstractIrrational, y::AbstractIrrational)
    Float64(x) != Float64(y) || throw(MethodError(<, (x, y)))
    return Float64(x) < Float64(y)
end

<=(::Irrational{s}, ::Irrational{s}) where {s} = true
<=(x::AbstractIrrational, y::AbstractIrrational) = x==y || x<y

# Irrationals, by definition, can't have a finite representation equal them exactly
==(x::AbstractIrrational, y::Real) = false
==(x::Real, y::AbstractIrrational) = false
```
-/
def floatType : FTy := .f64
def equalSame (_x _y : Irrational symbol) : Bool := true
def equalAbstract {A B : Type} (_x : A) (_y : B) : Bool := false
def lessSame (_x _y : Irrational symbol) : Bool := false

def lessAbstract {A B : Type} (floatA : A → Jl (FV .f64)) (floatB : B → Jl (FV .f64))
    (x : A) (y : B) : Jl Bool := do
  let xf ← floatA x
  let yf ← floatB y
  if eq_IEEEFloat xf yf then throw (.methodError "<")
  let xf ← floatA x
  let yf ← floatB y
  return lt_IEEEFloat xf yf

def lessEqualSame (_x _y : Irrational symbol) : Bool := true
def lessEqualAbstract {A B : Type} (equal : A → B → Jl Bool) (less : A → B → Jl Bool)
    (x : A) (y : B) : Jl Bool := do
  if ← equal x y then pure true else less x y

def equalRealRight {A R : Type} (_x : A) (_y : R) : Bool := false
def equalRealLeft {R A : Type} (_x : R) (_y : A) : Bool := false

/--
Julia source: base/irrationals.jl:127-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::AbstractIrrational, y::Float64) = Float64(x,RoundUp) <= y
<(x::Float64, y::AbstractIrrational) = x <= Float64(y,RoundDown)
<(x::AbstractIrrational, y::Float32) = Float32(x,RoundUp) <= y
<(x::Float32, y::AbstractIrrational) = x <= Float32(y,RoundDown)
<(x::AbstractIrrational, y::Float16) = Float32(x,RoundUp) <= y
<(x::Float16, y::AbstractIrrational) = x <= Float32(y,RoundDown)
<(x::AbstractIrrational, y::BigFloat) = setprecision(precision(y)+32) do
    big(x) < y
end
<(x::BigFloat, y::AbstractIrrational) = setprecision(precision(x)+32) do
    x < big(y)
end

<=(x::AbstractIrrational, y::AbstractFloat) = x < y
<=(x::AbstractFloat, y::AbstractIrrational) = x < y
```
-/
def lessIEEE {m : Type → Type} [Monad m] {A : Type} (T : IEEE32Or64) (convert : A → RoundingMode → m (FV T.ty))
    (x : A) (y : FV T.ty) : m Bool := do return le_IEEEFloat (← convert x .Up) y

def ieeeLess {m : Type → Type} [Monad m] {A : Type} (T : IEEE32Or64) (convert : A → RoundingMode → m (FV T.ty))
    (x : FV T.ty) (y : A) : m Bool := do return le_IEEEFloat x (← convert y .Down)

def lessFloat16 {m : Type → Type} [Monad m] {A : Type} (convert : A → RoundingMode → m (FV .f32))
    (x : A) (y : FV .f16) : m Bool := do
  return le_IEEEFloat (← convert x .Up) (convertFloat .f32 y)
def float16Less {m : Type → Type} [Monad m] {A : Type} (convert : A → RoundingMode → m (FV .f32))
    (x : FV .f16) (y : A) : m Bool := do
  return le_IEEEFloat (convertFloat .f32 x) (← convert y .Down)

def lessBigFloat {A : Type} (big : A → M BigFloat) (x : A) (y : BigFloat) : M Bool :=
  JuliaLean.base.mpfr.withPrecision (fun (p : Clong) (_ : Unit) => pure p)
    (do return JuliaLean.base.mpfr.less (← big x) y) (y.prec+JInt.wrap .i64 32) ()
def bigFloatLess {A : Type} (big : A → M BigFloat) (x : BigFloat) (y : A) : M Bool :=
  JuliaLean.base.mpfr.withPrecision (fun (p : Clong) (_ : Unit) => pure p)
    (do return JuliaLean.base.mpfr.less x (← big y)) (x.prec+JInt.wrap .i64 32) ()

def lessEqualFloatRight {A F : Type} (less : A → F → Jl Bool) (x : A) (y : F) := less x y
def lessEqualFloatLeft {F A : Type} (less : F → A → Jl Bool) (x : F) (y : A) := less x y

/--
Julia source: base/irrationals.jl:144-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rationalize_irrational(::Type{T}, x::AbstractIrrational, tol::Real) where {T<:Integer}
    return rationalize(T, big(x), tol=tol)
end
function rationalize(::Type{T}, x::AbstractIrrational; tol::Real=0) where {T<:Integer}
    return _rationalize_irrational(T, x, tol)
end
function _lessrational(rx::Rational, x::AbstractIrrational)
    return rx < big(x)
end
function lessrational(rx::Rational, x::AbstractIrrational)
    return _lessrational(rx, x)
end
```
-/
def rationalizeIrrational {A R Tol : Type} (big : A → M BigFloat)
    (rationalize : BigFloat → Tol → M R) (x : A) (tol : Tol) : M R := do
  rationalize (← big x) tol
def rationalize {A R Tol : Type} (callee : A → Tol → M R) (x : A) (tol : Tol) := callee x tol

def lessRationalInner {R A : Type} (big : A → M BigFloat)
    (less : R → BigFloat → M Bool) (rx : R) (x : A) : M Bool := do less rx (← big x)
def lessRational {R A : Type} (callee : R → A → M Bool) (rx : R) (x : A) := callee rx x

/--
Julia source: base/irrationals.jl:156-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <(x::AbstractIrrational, y::Rational{T}) where T
    T <: Unsigned && x < 0.0 && return true
    rx = rationalize(T, x)
    if lessrational(rx, x)
        return rx < y
    else
        return rx <= y
    end
end
function <(x::Rational{T}, y::AbstractIrrational) where T
    T <: Unsigned && y < 0.0 && return false
    ry = rationalize(T, y)
    if lessrational(ry, y)
        return x <= ry
    else
        return x < ry
    end
end
```
-/
def lessRationalRight {A R : Type} (unsigned : Bool) (negative : A → M Bool)
    (rationalize : A → M R) (lessRational : R → A → M Bool)
    (less lessEqual : R → R → M Bool) (x : A) (y : R) : M Bool := do
  if unsigned then if ← negative x then return true
  let rx ← rationalize x
  if ← lessRational rx x then less rx y else lessEqual rx y

def rationalLessLeft {R A : Type} (unsigned : Bool) (negative : A → M Bool)
    (rationalize : A → M R) (lessRational : R → A → M Bool)
    (less lessEqual : R → R → M Bool) (x : R) (y : A) : M Bool := do
  if unsigned then if ← negative y then return false
  let ry ← rationalize y
  if ← lessRational ry y then lessEqual x ry else less x ry

/--
Julia source: base/irrationals.jl:174-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function <(x::AbstractIrrational, y::Rational{BigInt})
    Float64(x) != Float64(y) && return Float64(x) < Float64(y)
    p = precision(BigFloat) + 32
    @assume_effects :terminates_locally while true
        xf, yf = BigFloat(x; precision=p), BigFloat(y; precision=p)
        xf != yf && return xf < yf
        p *= 2
    end
end
<(x::Rational{BigInt}, y::AbstractIrrational) = !(y < x)
```
-/
def lessRationalBigInt {A R : Type} (floatA : A → M (FV .f64))
    (floatR : R → M (FV .f64)) (bigA : A → Clong → M BigFloat)
    (bigR : R → Clong → M BigFloat) (x : A) (y : R) : Run Bool := fun state =>
  let action : M (Option Bool) := do
    let xf ← floatA x
    let yf ← floatR y
    if !eq_IEEEFloat xf yf then
      let xf ← floatA x
      let yf ← floatR y
      return some (lt_IEEEFloat xf yf)
    return none
  let (initial,state) := action.run state
  match initial with
  | .error error => some (.error error,state)
  | .ok (some value) => some (.ok value,state)
  | .ok none =>
    let p := JuliaLean.base.mpfr.precisionType state+JInt.wrap .i64 32
    loopM (fun p => do
      let xf ← bigA x p
      let yf ← bigR y p
      if !JuliaLean.base.mpfr.equal xf yf then return .inl (JuliaLean.base.mpfr.less xf yf)
      return .inr (p*JInt.wrap .i64 2)) p state

def rationalBigIntLess {R A : Type} (less : A → R → Run Bool) (x : R) (y : A) : Run Bool :=
  fun state => (less y x state).map (fun (result,state) => (result.map not,state))

/--
Julia source: base/irrationals.jl:185-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::AbstractIrrational, y::Rational) = x < y
<=(x::Rational, y::AbstractIrrational) = x < y

cmp(::Irrational{s}, ::Irrational{s}) where {s} = 0
cmp(x::AbstractIrrational, y::AbstractIrrational) = x < y ? -1 : 1
cmp(x::AbstractIrrational, y::Real) = x < y ? -1 : 1
cmp(x::Real, y::AbstractIrrational) = x < y ? -1 : 1

cmp(<, ::Irrational{s}, ::Irrational{s}) where {s} = 0
cmp(<, x::AbstractIrrational, y::AbstractIrrational) = x < y ? -1 : 1
cmp(<, x::AbstractIrrational, y::Real) = x < y ? -1 : 1
cmp(<, x::Real, y::AbstractIrrational) = x < y ? -1 : 1
```
-/
def lessEqualRationalRight {A R : Type} (less : A → R → M Bool) (x : A) (y : R) := less x y
def lessEqualRationalLeft {R A : Type} (less : R → A → M Bool) (x : R) (y : A) := less x y

def cmpSame (_x _y : Irrational symbol) : Clong := JInt.wrap .i64 0
def cmp {A B : Type} (less : A → B → Jl Bool) (x : A) (y : B) : Jl Clong := do
  return JInt.wrap .i64 (if ← less x y then -1 else 1)
def cmpWithLessSame (_x _y : Irrational symbol) : Clong := JInt.wrap .i64 0
def cmpWithLess {A B : Type} (less : A → B → Jl Bool) (x : A) (y : B) : Jl Clong := do
  return JInt.wrap .i64 (if ← less x y then -1 else 1)

/--
Julia source: base/irrationals.jl:198-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(::AbstractIrrational) = true
isinteger(::AbstractIrrational) = false
iszero(::AbstractIrrational) = false
isone(::AbstractIrrational) = false

hash(x::Irrational, h::UInt) = 3 *% h -% objectid(x)

widen(::Type{T}) where {T<:Irrational} = T

zero(::AbstractIrrational) = false
zero(::Type{<:AbstractIrrational}) = false

one(::AbstractIrrational) = true
one(::Type{<:AbstractIrrational}) = true
```
-/
def isfinite {A : Type} (_x : A) : Bool := true
def isinteger {A : Type} (_x : A) : Bool := false
def iszero {A : Type} (_x : A) : Bool := false
def isone {A : Type} (_x : A) : Bool := false

def hash (objectid : Irrational symbol → JInt .u64) (x : Irrational symbol) (h : JInt .u64) : JInt .u64 :=
  JInt.wrap .u64 3 * h - objectid x

def widen {T : Type} (type : T) : T := type
def zero {A : Type} (_x : A) : Bool := false
def zeroType {T : Type} (_t : T) : Bool := false
def one {A : Type} (_x : A) : Bool := true
def oneType {T : Type} (_t : T) : Bool := true

/--
Julia source: base/irrationals.jl:213-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::AbstractIrrational) = ifelse(x < zero(x), -1.0, 1.0)

-(x::AbstractIrrational) = -Float64(x)
for op in Symbol[:+, :-, :*, :/, :^]
    @eval $op(x::AbstractIrrational, y::AbstractIrrational) = $op(Float64(x),Float64(y))
end
*(x::Bool, y::AbstractIrrational) = ifelse(x, Float64(y), 0.0)

^(x::AbstractIrrational, y::Integer) = float(x)^y

round(x::Irrational, r::RoundingMode) = round(float(x), r)
```
-/
def sign {A : Type} (negative : A → Jl Bool) (x : A) : Jl (FV .f64) := do
  return Fl.roundRat (if ← negative x then -1 else 1) 1 false

def neg {A : Type} (convert : A → Jl (FV .f64)) (x : A) : Jl (FV .f64) := do
  return neg_IEEEFloat (← convert x)

def binary {A B : Type} (floatA : A → Jl (FV .f64)) (floatB : B → Jl (FV .f64))
    (op : FV .f64 → FV .f64 → Jl (FV .f64)) (x : A) (y : B) : Jl (FV .f64) := do
  let x ← floatA x
  let y ← floatB y
  op x y

def boolMul {A : Type} (convert : A → Jl (FV .f64)) (x : Bool) (y : A) : Jl (FV .f64) := do
  let y ← convert y
  return if x then y else Fl.zero false

def powInteger {A I R : Type} (float : A → Jl (FV .f64))
    (pow : FV .f64 → I → Jl R) (x : A) (y : I) : Jl R := do pow (← float x) y

def round {R : Type} (float : Irrational symbol → Jl (FV .f64))
    (round : FV .f64 → RoundingMode → Jl R) (x : Irrational symbol) (r : RoundingMode) : Jl R := do
  round (← float x) r

/--
Julia source: base/irrationals.jl:300-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(x::AbstractIrrational) = BigFloat(x)
big(::Type{<:AbstractIrrational}) = BigFloat
```
-/
def big {A : Type} (convert : A → M BigFloat) (x : A) := convert x
def bigType : JuliaLean.base.mpfr.BigFloatType := .type

/--
Julia source: base/irrationals.jl:304-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alignment(io::IO, x::AbstractIrrational)
    m = match(r"^(.*?)(=.*)$", sprint(show, x, context=io, sizehint=0))
    m === nothing ? (length(sprint(show, x, context=io, sizehint=0)), 0) :
    (length(something(m.captures[1])), length(something(m.captures[2])))
end
```
-/
def alignment {IO A : Type} (sprint : IO → A → Jl String)
    (matchEquals : String → Jl (Option (String × String)))
    (length : String → Clong) (io : IO) (x : A) : Jl (Clong × Clong) := do
  let m ← matchEquals (← sprint io x)
  match m with
  | none => return (length (← sprint io x),JInt.wrap .i64 0)
  | some (left,right) => return (length left,length right)

/--
Julia source: base/irrationals.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inv(x::AbstractIrrational) = 1/x
```
-/
def inv {A R : Type} (divide : Clong → A → Jl R) (x : A) : Jl R :=
  divide (JInt.wrap .i64 1) x

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:1-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## general machinery for irrational mathematical constants
-- 
-- """
--     AbstractIrrational <: Real
-- 
-- Number type representing an exact irrational value, which is automatically rounded to the correct precision in
-- arithmetic operations with other numeric quantities.
-- 
-- Subtypes `MyIrrational <: AbstractIrrational` should implement at least `==(::MyIrrational, ::MyIrrational)`,
-- `hash(x::MyIrrational, h::UInt)`, and `convert(::Type{F}, x::MyIrrational) where {F <: Union{BigFloat,Float32,Float64}}`.
-- 
-- If a subtype is used to represent values that may occasionally be rational (e.g. a square-root type that represents `√n`
-- for integers `n` will give a rational result when `n` is a perfect square), then it should also implement
-- `isinteger`, `iszero`, `isone`, and `==` with `Real` values (since all of these default to `false` for
-- `AbstractIrrational` types), as well as defining [`hash`](@ref) to equal that of the corresponding `Rational`.
-- """
-- abstract type AbstractIrrational <: Real end
-- 
-- """
--     Irrational{sym} <: AbstractIrrational
-- 
-- Number type representing an exact irrational value denoted by the
-- symbol `sym`, such as [`π`](@ref pi), [`ℯ`](@ref) and [`γ`](@ref Base.MathConstants.eulergamma).
-- 
-- See also [`AbstractIrrational`](@ref).
-- """
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:125-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Irrational vs AbstractFloat
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:142-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Irrational vs Rational
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- UNTRANSLATED
-- Source: base/irrationals.jl:224-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @irrational sym [val] def
-- 
-- Define a new `Irrational` value, `sym`, with arbitrary-precision definition in terms
-- of `BigFloat`s given by the expression `def`.
-- 
-- Optionally provide a pre-computed `Float64` value `val` which must equal `Float64(def)`.
-- `val` will be computed automatically if omitted.
-- 
-- An `AssertionError` is thrown when either `big(def) isa BigFloat` or `Float64(val) == Float64(def)`
-- returns `false`.
-- 
-- !!! warning
--     This macro should not be used outside of `Base` Julia.
-- 
--     The macro creates a new type `Irrational{:sym}` regardless of where it's invoked. This can
--     lead to conflicting definitions if two packages define an irrational number with the same
--     name but different values.
-- 
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.@irrational twoπ 2*big(π)
-- 
-- julia> twoπ
-- twoπ = 6.2831853071795...
-- 
-- julia> Base.@irrational sqrt2 1.4142135623730950488 √big(2)
-- 
-- julia> sqrt2
-- sqrt2 = 1.4142135623730...
-- 
-- julia> Base.@irrational sqrt2 1.4142135623730950488 big(2)
-- ERROR: AssertionError: big($(Expr(:escape, :sqrt2))) isa BigFloat
-- 
-- julia> Base.@irrational sqrt2 1.41421356237309 √big(2)
-- ERROR: AssertionError: Float64($(Expr(:escape, :sqrt2))) == Float64(big($(Expr(:escape, :sqrt2))))
-- ```
-- """
-- macro irrational(sym, val, def)
--     irrational(sym, val, def)
-- end
-- macro irrational(sym, def)
--     irrational(sym, :(big($(esc(sym)))), def)
-- end
-- /Source
-- Reason: The `@irrational` overloads are macro front-ends; the ordinary helper below builds their expansion.

/-- Operations on literal symbols and strings supplied by the expression runtime. -/
structure IrrationalAstOps (L : Type) where
  baseModule : L
  mpfrModule : L
  roundingModule : L
  isSymbol : JuliaLean.base.expr.Value L → Bool
  symbolName : JuliaLean.base.expr.Value L → String
  stringLiteral : String → L
/--
Julia source: base/irrationals.jl:270-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function irrational(sym, val, def)
    esym = esc(sym)
    qsym = esc(Expr(:quote, sym))
    bigconvert = isa(def,Symbol) ? quote
        function Base.BigFloat(::Irrational{$qsym}, r::MPFR.MPFRRoundingMode=Rounding.rounding_raw(BigFloat); precision=precision(BigFloat))
            c = BigFloat(;precision=precision)
            ccall(($(string("mpfr_const_", def)), Base.MPFR.libmpfr),
                  Cint, (Ref{BigFloat}, MPFR.MPFRRoundingMode), c, r)
            return c
        end
    end : quote
        function Base.BigFloat(::Irrational{$qsym}; precision=precision(BigFloat))
            setprecision(BigFloat, precision) do
                $(esc(def))
            end
        end
    end
    quote
        const $esym = Irrational{$qsym}()
        $bigconvert
        let v = $val, v64 = Float64(v), v32 = Float32(v)
            Base.Float64(::Irrational{$qsym}) = v64
            Base.Float32(::Irrational{$qsym}) = v32
        end
        @assert isa(big($esym), BigFloat)
        @assert Float64($esym) == Float64(big($esym))
        @assert Float32($esym) == Float32(big($esym))
    end
end
```
-/

def irrational {L : Type} (ops : IrrationalAstOps L)
    (symbol value definition : JuliaLean.base.expr.Value L) : JuliaLean.base.expr.Value L := Id.run do
  let makeExpr := fun (head : String) (args : List (JuliaLean.base.expr.Value L)) =>
    JuliaLean.base.expr.Value.expr head args
  let base := fun (name : String) => JuliaLean.base.expr.Value.globalRef ops.baseModule name
  let global := fun (module : L) (name : String) =>
    JuliaLean.base.expr.Value.globalRef module name
  let call := fun (callee : JuliaLean.base.expr.Value L)
      (args : List (JuliaLean.base.expr.Value L)) =>
    makeExpr "call" (callee :: args)
  let assign := fun (left right : JuliaLean.base.expr.Value L) =>
    makeExpr "=" [left, right]
  let block := fun (values : List (JuliaLean.base.expr.Value L)) =>
    makeExpr "block" values
  let name := symbol
  let escapedName := JuliaLean.base.expr.esc name
  let quotedName := JuliaLean.base.expr.esc (makeExpr "quote" [name])
  let irrationalType := makeExpr "curly" [base "Irrational", quotedName]
  let precisionDefault := call (base "precision") [base "BigFloat"]
  let precisionKeyword := makeExpr "kw" [.symbol "precision", precisionDefault]
  let parameters := makeExpr "parameters" [precisionKeyword]
  let roundingMode := global ops.mpfrModule "MPFRRoundingMode"
  let rawRounding := call (global ops.roundingModule "rounding_raw") [base "BigFloat"]
  let bigFloatMethod := base "BigFloat"
  let generatedBigFloatMethod := if ops.isSymbol definition then
    let roundingArgument := makeExpr "=" [makeExpr "::" [.symbol "r", roundingMode], rawRounding]
    let signature := makeExpr "call"
      [bigFloatMethod, parameters, makeExpr "::" [irrationalType], roundingArgument]
    let precisionArgument := makeExpr "parameters"
      [makeExpr "kw" [.symbol "precision", .symbol "precision"]]
    let allocation := assign (.symbol "c") (call bigFloatMethod [precisionArgument])
    let library := makeExpr "tuple" [
      .leaf (ops.stringLiteral ("mpfr_const_" ++ ops.symbolName definition)),
      global ops.mpfrModule "libmpfr"]
    let argumentTypes := makeExpr "tuple" [
      makeExpr "curly" [base "Ref", bigFloatMethod], roundingMode]
    let nativeCall := call (base "ccall")
      [library, base "Cint", argumentTypes, .symbol "c", .symbol "r"]
    let body := block [allocation, nativeCall, makeExpr "return" [.symbol "c"]]
    block [makeExpr "function" [signature, body]]
  else
    let signature := makeExpr "call"
      [bigFloatMethod, parameters, makeExpr "::" [irrationalType]]
    let precisionCall := call (base "setprecision") [base "BigFloat", .symbol "precision"]
    let evaluation := makeExpr "do" [
      precisionCall, makeExpr "->" [makeExpr "tuple" [], block [JuliaLean.base.expr.esc definition]]]
    block [makeExpr "function" [signature, block [evaluation]]]
  let v := JuliaLean.base.expr.Value.symbol "v"
  let v64 := JuliaLean.base.expr.Value.symbol "v64"
  let v32 := JuliaLean.base.expr.Value.symbol "v32"
  let floatBindings := block [
    assign v value,
    assign v64 (call (base "Float64") [v]),
    assign v32 (call (base "Float32") [v])]
  let floatMethods := block [
    assign (call (base "Float64") [makeExpr "::" [irrationalType]]) v64,
    assign (call (base "Float32") [makeExpr "::" [irrationalType]]) v32]
  let cachedFloatMethods := makeExpr "let" [floatBindings, floatMethods]
  let macroCall := fun (line : Nat) (expression : JuliaLean.base.expr.Value L) =>
    makeExpr "macrocall" [
      base "@assert",
      .lineNumberNode (JuliaLean.base.expr.i64 (Int.ofNat line)) (.symbol "irrationals.jl"),
      expression]
  let checkBigFloat := macroCall 294 (call (base "isa")
    [call (base "big") [escapedName], base "BigFloat"])
  let checkFloat64 := macroCall 295 (call (.symbol "==") [
    call (base "Float64") [escapedName],
    call (base "Float64") [call (base "big") [escapedName]]])
  let checkFloat32 := macroCall 296 (call (.symbol "==") [
    call (base "Float32") [escapedName],
    call (base "Float32") [call (base "big") [escapedName]]])
  let constant := makeExpr "const"
    [assign escapedName (call irrationalType [])]
  return makeExpr "quote" [block [
    constant, generatedBigFloatMethod, cachedFloatMethods,
    checkBigFloat, checkFloat64, checkFloat32]]

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:302-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # align along = for nice Array printing
-- /Source

-- Untranslated: macro expansion or source documentation; generated constant kernels other than pi are not represented.
-- UNTRANSLATED
-- Source: base/irrationals.jl:309-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # inv
-- /Source

structure IrrationalFloatValues where
  float64 : FV .f64
  float32 : FV .f32

def cacheIrrationalFloatValues (value : M BigFloat) : M IrrationalFloatValues := do
  let value ← value
  let state ← JuliaLean.base.mpfr.readContext
  let mode := JuliaLean.base.mpfr.roundingRaw state
  pure ⟨JuliaLean.base.mpfr.toFloat64 value mode, JuliaLean.base.mpfr.toFloat32 value mode⟩

def withIrrationalPrecision {A : Type} (precision : Option Int) (action : M A) : M A := do
  let state ← JuliaLean.base.mpfr.readContext
  let precision := precision.getD (JuliaLean.base.mpfr.precisionType state).val
  if precision < 1 then throw (.domainError "`precision` cannot be less than 1.")
  JuliaLean.base.mpfr.withPrecision
    (fun p (_ : Unit) => JInt.convert "Int64" .i64 p) action precision ()

-- Generic equality and hashing above apply to each concrete `Irrational{sym}` type.

-- Macro block: base/irrationals.jl:264-298; @irrational use: base/mathconstants.jl:13.
def bigFloatPi (ops : JuliaLean.base.mpfr.AnalyticOps) (_x : Irrational "π")
    (rounding : Option JuliaLean.base.mpfr.Mode := none) (precision : Option Int := none) :
    M BigFloat := do
  let state ← JuliaLean.base.mpfr.readContext
  let mode := rounding.getD (JuliaLean.base.mpfr.roundingRaw state)
  let precision := precision.getD (JuliaLean.base.mpfr.precisionType state).val
  JuliaLean.base.mpfr.constantWithPrecision ops .pi precision mode
def piFloatValues (ops : JuliaLean.base.mpfr.AnalyticOps) : M IrrationalFloatValues :=
  cacheIrrationalFloatValues (bigFloatPi ops (⟨⟩ : Irrational "π"))
def float64Pi (values : IrrationalFloatValues) (_x : Irrational "π") : FV .f64 :=
  values.float64
def float32Pi (values : IrrationalFloatValues) (_x : Irrational "π") : FV .f32 :=
  values.float32

-- Macro block: base/irrationals.jl:264-298; @irrational use: base/mathconstants.jl:14.
def bigFloatEuler (ops : JuliaLean.base.mpfr.AnalyticOps) (_x : Irrational "ℯ")
    (precision : Option Int := none) : M BigFloat :=
  withIrrationalPrecision precision (do
    let state ← JuliaLean.base.mpfr.readContext
    let one ← JuliaLean.base.mpfr.fromLong (JInt.wrap .i64 1)
      (JuliaLean.base.mpfr.roundingRaw state) (JuliaLean.base.mpfr.precisionType state).val
    JuliaLean.base.mpfr.expBigFloat ops one)
def eulerFloatValues (ops : JuliaLean.base.mpfr.AnalyticOps) : M IrrationalFloatValues :=
  cacheIrrationalFloatValues (bigFloatEuler ops (⟨⟩ : Irrational "ℯ"))
def float64Euler (values : IrrationalFloatValues) (_x : Irrational "ℯ") : FV .f64 :=
  values.float64
def float32Euler (values : IrrationalFloatValues) (_x : Irrational "ℯ") : FV .f32 :=
  values.float32

-- Macro block: base/irrationals.jl:264-298; @irrational use: base/mathconstants.jl:15.
def bigFloatGamma (ops : JuliaLean.base.mpfr.AnalyticOps) (_x : Irrational "γ")
    (rounding : Option JuliaLean.base.mpfr.Mode := none) (precision : Option Int := none) :
    M BigFloat := do
  let state ← JuliaLean.base.mpfr.readContext
  let mode := rounding.getD (JuliaLean.base.mpfr.roundingRaw state)
  let precision := precision.getD (JuliaLean.base.mpfr.precisionType state).val
  JuliaLean.base.mpfr.constantWithPrecision ops .euler precision mode
def gammaFloatValues (ops : JuliaLean.base.mpfr.AnalyticOps) : M IrrationalFloatValues :=
  cacheIrrationalFloatValues (bigFloatGamma ops (⟨⟩ : Irrational "γ"))
def float64Gamma (values : IrrationalFloatValues) (_x : Irrational "γ") : FV .f64 :=
  values.float64
def float32Gamma (values : IrrationalFloatValues) (_x : Irrational "γ") : FV .f32 :=
  values.float32

-- Macro block: base/irrationals.jl:264-298; @irrational use: base/mathconstants.jl:16.
def bigFloatPhi (ops : JuliaLean.base.mpfr.AnalyticOps) (_x : Irrational "φ")
    (precision : Option Int := none) : M BigFloat :=
  withIrrationalPrecision precision (do
    let state ← JuliaLean.base.mpfr.readContext
    let mode := JuliaLean.base.mpfr.roundingRaw state
    let currentPrecision := (JuliaLean.base.mpfr.precisionType state).val
    let five ← JuliaLean.base.mpfr.fromLong (JInt.wrap .i64 5) mode currentPrecision
    let root ← JuliaLean.base.mpfr.sqrt five
    let numerator ← JuliaLean.base.mpfr.integerArithmetic .add (JInt.wrap .i64 1) root
    JuliaLean.base.mpfr.arithmeticInteger .div numerator (JInt.wrap .i64 2))
def phiFloatValues (ops : JuliaLean.base.mpfr.AnalyticOps) : M IrrationalFloatValues :=
  cacheIrrationalFloatValues (bigFloatPhi ops (⟨⟩ : Irrational "φ"))
def float64Phi (values : IrrationalFloatValues) (_x : Irrational "φ") : FV .f64 :=
  values.float64
def float32Phi (values : IrrationalFloatValues) (_x : Irrational "φ") : FV .f32 :=
  values.float32

-- Macro block: base/irrationals.jl:264-298; @irrational use: base/mathconstants.jl:17.
def bigFloatCatalan (ops : JuliaLean.base.mpfr.AnalyticOps) (_x : Irrational "catalan")
    (rounding : Option JuliaLean.base.mpfr.Mode := none) (precision : Option Int := none) :
    M BigFloat := do
  let state ← JuliaLean.base.mpfr.readContext
  let mode := rounding.getD (JuliaLean.base.mpfr.roundingRaw state)
  let precision := precision.getD (JuliaLean.base.mpfr.precisionType state).val
  JuliaLean.base.mpfr.constantWithPrecision ops .catalan precision mode
def catalanFloatValues (ops : JuliaLean.base.mpfr.AnalyticOps) : M IrrationalFloatValues :=
  cacheIrrationalFloatValues (bigFloatCatalan ops (⟨⟩ : Irrational "catalan"))
def float64Catalan (values : IrrationalFloatValues) (_x : Irrational "catalan") : FV .f64 :=
  values.float64
def float32Catalan (values : IrrationalFloatValues) (_x : Irrational "catalan") : FV .f32 :=
  values.float32


section PiGenerated
open JuliaLean.base.mpfr
/-- Typed external mpfr_const_pi call. Only the five documented rounding modes
have a result law. MPFR §4.4 guarantees neither faithful support for this
constant function nor a faithful ternary value or inexact flag; that call stays
opaque at every precision. -/
structure PiPrimitive where
  call : Context → Clong → Mode → PrimitiveResult
  correct : ∀ state precision mode, 0 < precision.val → mode ≠ .faithful →
    JuliaLean.Spec.Pi.PiRounded state precision mode (call state precision mode)

/-- Fixed destination precision requested by `_irrational_to_float`.
Every mode calls `mpfr_const_pi`; no executable π algorithm replaces that call.
The primitive contract imposes no faithful value, ternary, or flag law. -/
def pi256Primitive (primitive : PiPrimitive) (state : Context) (mode : Mode) : PrimitiveResult :=
  primitive.call state (JInt.wrap .i64 256) mode

/-- Shared generated constructor body; keyword dispatch occurs before this
Integer-only path, and allocation/conversion precedes the constant C call. -/
def constructPiInteger {I : Type} (ops : JuliaLean.base.mpfr.IntegerPrecision I)
    (constant : BigFloat → Mode → M BigFloat) (mode : Mode) (precision : I) : M BigFloat := do
  let c ← JuliaLean.base.mpfr.constructInteger ops precision
  constant c mode

def constructPi (constant : BigFloat → Mode → M BigFloat)
    (mode : Mode) (precision : JuliaLean.base.mpfr.PrecisionKeyword) : JuliaLean.base.mpfr.KeywordM BigFloat :=
  match precision with
  | .nonInteger actual => throw (.typeError "precision" "Integer" actual)
  | .integer ops value => JuliaLean.base.mpfr.liftMPFR (constructPiInteger ops constant mode value)


/--
Julia source: base/irrationals.jl:274-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function Base.BigFloat(::Irrational{$qsym}, r::MPFR.MPFRRoundingMode=Rounding.rounding_raw(BigFloat); precision=precision(BigFloat))
            c = BigFloat(;precision=precision)
            ccall(($(string("mpfr_const_", def)), Base.MPFR.libmpfr),
                  Cint, (Ref{BigFloat}, MPFR.MPFRRoundingMode), c, r)
            return c
        end
```
-/

def bigPi (primitive : PiPrimitive) (_pi : Irrational "π")
    (mode : Option JuliaLean.base.mpfr.Mode := none)
    (precision : Option JuliaLean.base.mpfr.PrecisionKeyword := none) : JuliaLean.base.mpfr.KeywordM JuliaLean.base.mpfr.BigFloat := do
  let state ← get
  constructPi (fun c mode => do
    JuliaLean.base.mpfr.applyPrimitive (primitive.call (← JuliaLean.base.mpfr.readContext) c.prec mode))
    (mode.getD (JuliaLean.base.mpfr.roundingRaw state))
    (precision.getD (JuliaLean.base.mpfr.defaultPrecisionKeyword state))


end PiGenerated

end JuliaLean.base.irrationals

namespace JuliaLean.NumMisc

/-! ## AbstractIrrational conversion -/

inductive RoundMode where
  | nearest | down | up | toZero
  deriving DecidableEq, Repr

inductive Side where
  | below | equal | above
  deriving DecidableEq, Repr

/-- An exact positive irrational close to 1. `separationBits = p` means its
distance from 1 is below the resolution of a `p`-bit intermediate. -/
structure IrrationalNearOne where
  side : Side
  separationBits : Nat
  deriving DecidableEq, Repr

inductive UnitFloat where
  | prev | one | next
  deriving DecidableEq, Repr

def roundNearOne : Side → RoundMode → UnitFloat
  | .equal, _ => .one
  | .above, .up => .next
  | .above, _ => .one
  | .below, .down => .prev
  | .below, .toZero => .prev
  | .below, _ => .one

/-- `BigFloat(x)` inside a 256-bit precision scope, `base/irrationals.jl:101-104`.
Values closer than that resolution collapse to exactly 1. -/
def bigAt256 (x : IrrationalNearOne) : Side :=
  if x.separationBits > 256 then .equal else x.side

def sourceIrrationalConvert (x : IrrationalNearOne) (r : RoundMode) : UnitFloat :=
  roundNearOne (bigAt256 x) r

namespace Coverage

open JuliaLean

/-! ## `base/irrationals.jl:31-223` -/

inductive PromoteIrr where | f16 | f32 | f64 | promoted | fallback deriving DecidableEq, Repr

def irrationalPromotion (other : PromoteIrr) : PromoteIrr :=
  match other with | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | _ => .promoted

def irrationalBound (value : Nat) : Nat := value
def irrationalDefaultFloat : FloatKind := .f64
def irrationalWiden (kind : Nat) : Nat := kind

def firstStableRational : List (Option Nat) → Jl Nat
  | [] => .error (.argumentError "precision search did not converge")
  | none :: rest => firstStableRational rest
  | some value :: _ => .ok value

def irrationalCompare (left64 right64 : Int) : Jl Bool :=
  if left64 == right64 then .error (.methodError "<") else .ok (left64 < right64)

def irrationalRationalLess (approxBelow : Bool) (approx rational : Int) : Bool :=
  if approxBelow then decide (approx < rational) else decide (approx ≤ rational)

def irrationalBinary (op : Int → Int → Int) (left right : Int) : Int := op left right

def irrationalSameEq (_left _right : Nat) : Bool := true
def irrationalCrossEq (_left _right : Nat) : Bool := false
def irrationalPredicates (_value : Nat) : Bool × Bool × Bool × Bool := (true, false, false, false)
def irrationalZero : Bool := false
def irrationalOne : Bool := true
def irrationalSign (lessThanZero : Bool) : Int := if lessThanZero then -1 else 1
def irrationalUnary (convert : Nat → Int) (op : Int → Int) (x : Nat) : Int := op (convert x)

/-! ## `base/irrationals.jl:264-311` -/

inductive IrrationalDeclEvent where
  | constant | bigMethod | float64Method | float32Method | assertBig | assert64 | assert32
  deriving DecidableEq, Repr

def irrationalDeclaration (_symbolDefinition : Bool) : List IrrationalDeclEvent :=
  [.constant, .bigMethod, .float64Method, .float32Method, .assertBig, .assert64, .assert32]

def irrationalShow (compact : Bool) (symbol digits : String) : String :=
  if compact then symbol else symbol ++ " = " ++ digits.take 15 ++ "..."

def irrationalAlignment (before after : Nat) (matched : Bool) : Nat × Nat :=
  if matched then (before, after) else (before + after, 0)

end Coverage
end JuliaLean.NumMisc

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `x < pi` for a Float64 `x` and the Irrational π, decided exactly as
`x <= Float64(pi, RoundDown)`; `base/irrationals.jl:128`. -/
def ltPi (x : F64) : Bool := F64.le x piRoundDown

end JuliaLean.MathFuncs
