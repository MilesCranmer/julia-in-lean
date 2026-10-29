import JuliaLean.base.float
import JuliaLean.base.complex
import JuliaLean.base.promotion
import JuliaLean.base.reduce
import JuliaLean.base.error
namespace JuliaLean.base.math

open JuliaLean JuliaLean.Promotion JuliaLean.base.float
/--
Julia source: base/math.jl:32-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_complex_domainerror(f::Symbol, x)
    throw(DomainError(x,
        LazyString(f," was called with a negative real argument but will only return a complex result if called with a complex argument. Try ", f,"(Complex(x)).")))
end
```
-/
def throwComplexDomainError {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError (f ++ " was called with a negative real argument but will only return a complex result if called with a complex argument. Try " ++ f ++ "(Complex(x))."))
/--
Julia source: base/math.jl:1265-1265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(x,y,z) = x*y+z
```
-/
def muladd {α : Type} (mul add : α → α → α) (x y z : α) : α :=
  mul x y |> fun product => add product z



structure IEEEOps (T : FTy) where
  sqrtLlvm : FV T → FV T
  eps : FV T
  floatmin : FV T
  floatmax : FV T
  invFloatmin : FV T
  pi : FV T
  fma : FV T → FV T → FV T → FV T
  twoMul : FV T → FV T → FV T × FV T
  trunc : FV T → FV T
  rem : FV T → FV T → FV T
  flipsign : FV T → FV T → FV T
  minFloat : FV T → FV T → FV T
  maxFloat : FV T → FV T → FV T
  clampUnsigned : Nat → Nat → Nat → Nat
  addFast : FV T → FV T → FV T
  pow : FV T → FV T → FV T
  oneunit : FV T → FV T
  inverse : FV T → FV T
  greater : FV T → FV T → Bool
  muladd : FV T → FV T → FV T → FV T
  abs2 : FV T → FV T
  haveFma : Bool

structure GenericHypotOps (α β : Type) where
  abs : α → β
  oneunit : β → β
  isinf : β → Bool
  isnan : β → Bool
  iszero : β → Bool
  isless : β → β → Bool
  lt : β → β → Bool
  greater : β → β → Bool
  le : β → β → Bool
  zero : β
  one : β
  infinity : β
  eps : β
  floatmin : β
  floatmax : β
  two : β
  four : β
  inverse : β → β
  sqrt : β → Jl β
  mul : β → β → β
  div : β → β → β
  add : β → β → β
  sub : β → β → β
  muladd : β → β → β → β
  fma : β → β → β → β
  divideInput : α → β → α
  abs2 : α → β
  haveFma : Bool
structure HypotDispatch (α β : Type) where
  pair : α → α → Jl β
  tuple : List α → Jl β
structure AbstractFloatOps (α : Type) where
  typeName : String
  ofInt : Int → α
  pi : α
  mul : α → α → α
  div : α → α → α
  pow : α → α → α
  abs : α → α
  isnan : α → Bool
  signbit : α → Bool
  lt : α → α → Bool
  rad2degFactor : α → α
  deg2radFactor : α → α

structure HypotFloatReductionOps (T : FTy) where
  iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
    JuliaLean.base.reduce.EltypeStatus
  booleanOr : JuliaLean.base.reduce.Reducer Bool Bool
  Signed : Type
  reinterpretSigned : FV T → Signed
  reinterpretFloat : Signed → FV T
  maximumReducer : JuliaLean.base.reduce.Reducer Signed Signed
  sumReducer : JuliaLean.base.reduce.Reducer (FV T) (FV T)

structure IntegerStepOps (Unsigned : Type) where
  one : Unsigned
  add : Unsigned → Unsigned → Unsigned
  mul : Unsigned → Unsigned → Unsigned
  ge : Unsigned → Unsigned → Bool
  shiftRight : Unsigned → Int → Unsigned
  checkedAdd : Int → Int → Jl Int

structure IntegerExponentOps (Integer Unsigned : Type) where
  iszero : Integer → Bool
  uabs : Integer → Unsigned
  step : IntegerStepOps Unsigned
abbrev Cx (T : FTy) := JuliaLean.base.complex.Complex (FV T)
inductive EvalpolyResult (T : FTy) where
  | real (value : FV T)
  | complex (value : Cx T)
structure JuliaSyntax where
  source : String
  deriving DecidableEq, Repr

inductive JuliaQuote where
  | escaped (node : JuliaSyntax)
  | tupleSplat (items : List JuliaQuote)
  | call (callee : String) (args : List JuliaQuote)
  | invoke (callee signature : String) (args : List JuliaQuote)


abbrev add {T : FTy} := JuliaLean.base.float.add_float (T := T)
abbrev sub {T : FTy} := JuliaLean.base.float.sub_float (T := T)
abbrev mul {T : FTy} := JuliaLean.base.float.mul_float (T := T)
abbrev div {T : FTy} := JuliaLean.base.float.div_float (T := T)
abbrev fzero (T : FTy) := JuliaLean.base.float.zero_float T
abbrev fone (T : FTy) := JuliaLean.base.float.one_float T
abbrev finf (T : FTy) := JuliaLean.base.float.inf_float T
abbrev fnan (T : FTy) := JuliaLean.base.float.nan_float T
abbrev fabs {T : FTy} := JuliaLean.base.float.abs_float (T := T)
abbrev fneg {T : FTy} := JuliaLean.base.float.neg_float (T := T)
abbrev feq {T : FTy} := JuliaLean.base.float.eq_float (T := T)
abbrev flt {T : FTy} := JuliaLean.base.float.lt_float (T := T)
abbrev fle {T : FTy} := JuliaLean.base.float.le_float (T := T)
abbrev fisnan {T : FTy} := JuliaLean.base.float.isnan_callee (T := T)
abbrev fisinf {T : FTy} := JuliaLean.base.float.isinf_callee (T := T)
abbrev fisfinite {T : FTy} := JuliaLean.base.float.isfinite_callee (T := T)
abbrev fiszero {T : FTy} := JuliaLean.base.float.iszero_float (T := T)
abbrev fsignbit {T : FTy} := JuliaLean.base.float.signbit_float (T := T)

private def bitMask (width : Nat) : Nat := 2 ^ width - 1
private def signMask (T : FTy) : Nat := 2 ^ (T.fmt.eb + T.fmt.sb)
private def exponentMask (T : FTy) : Nat := T.fmt.emax * 2 ^ T.fmt.sb
private def exponentRawMax (T : FTy) : Nat := T.fmt.emax
private def significandBits (T : FTy) : Nat := T.fmt.sb
private def exponentBits (T : FTy) : Nat := T.fmt.eb
private def exponentBias (T : FTy) : Nat := T.fmt.bias
private def leadingZeros (width bits : Nat) : Nat :=
  if bits = 0 then width else width - bits.log2 - 1
private def withoutBits (value mask width : Nat) : Nat := Nat.land value (bitMask width - mask)
private def hornerLoop {α : Type} (mul add : α → α → α) (x acc : α) : List α → α
  | [] => acc
  | c :: cs => hornerLoop mul add x (muladd mul add x acc c) cs

private def hornerValue {α : Type} (mul add : α → α → α) (x : α) (p : List α) : Option α :=
  match p.reverse with
  | [] => none
  | c :: cs => some (hornerLoop mul add x c cs)


private def maximumBy {α : Type} (isless : α → α → Bool) (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: rest => some (rest.foldl (fun m y => if isless m y then y else m) x)



/--
Julia source: base/math.jl:90-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _evalpoly(x, p)
    Base.require_one_based_indexing(p)
    N = length(p)
    ex = p[end]
    for i in N-1:-1:1
        ex = muladd(x, ex, p[i])
    end
    ex
end
```
-/
def evalpolyReal {α : Type} (mul add : α → α → α)
    (requireOneBased : List α → Jl Unit) (x : α) (p : List α) : Jl α := do
  let _ ← requireOneBased p
  match hornerValue mul add x p with
  | some value => pure value
  | none => .error .boundsError

/--
Julia source: base/math.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(x, p::AbstractVector) = _evalpoly(x, p)
```
-/
def evalpolyVector {α : Type} (mul add : α → α → α)
    (requireOneBased : List α → Jl Unit) (x : α) (p : List α) : Jl α :=
  evalpolyReal mul add requireOneBased x p

/--
Julia source: base/math.jl:75-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function evalpoly(x, p::Tuple)
    if @generated
        N = length(p.parameters::Core.SimpleVector)
        ex = :(p[end])
        for i in N-1:-1:1
            ex = :(muladd(x, $ex, p[$i]))
        end
        ex
    else
        _evalpoly(x, p)
    end
end
```
-/
def evalpolyTuple {α : Type} (mul add : α → α → α)
    (requireOneBased : List α → Jl Unit) (generated : Bool) (x : α) (p : List α) : Jl α :=
  if generated then
    match hornerValue mul add x p with
    | some value => .ok value
    | none => .error .boundsError
  else evalpolyVector mul add requireOneBased x p
def evalpolyComplexBody {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) := Id.run do
  match p.reverse with
  | [] => return .error .boundsError
  | [c] => return .ok (.real c)
  | a :: b :: rest =>
    let x := z.re
    let y := z.im
    let r := add x x
    let s := muladd (mul (T := T)) (add (T := T)) x x (mul y y)
    let (a, b) := rest.foldl (fun (ab : FV T × FV T) pi =>
      let ai := ab.1
      (muladd (mul (T := T)) (add (T := T)) r ai ab.2,
       muladd (mul (T := T)) (add (T := T)) (fneg s) ai pi)) (a, b)
    return .ok (.complex (complexMuladd a z b))


/--
Julia source: base/math.jl:130-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _evalpoly(z::Complex, p)
    Base.require_one_based_indexing(p)
    length(p) == 1 && return p[1]
    N = length(p)
    a = p[end]
    b = p[end-1]

    x = real(z)
    y = imag(z)
    r = 2x
    s = muladd(x, x, y*y)
    for i in N-2:-1:1
        ai = a
        a = muladd(r, ai, b)
        b = muladd(-s, ai, p[i])
    end
    ai = a
    muladd(ai, z, b)
end
```
-/
def evalpolyComplex {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (requireOneBased : List (FV T) → Jl Unit) (z : Cx T)
    (p : List (FV T)) : Jl (EvalpolyResult T) := do
  let _ ← requireOneBased p
  evalpolyComplexBody complexMuladd z p


/--
Julia source: base/math.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(z::Complex, p::AbstractVector) = _evalpoly(z, p)
```
-/
def evalpolyComplexVector {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (requireOneBased : List (FV T) → Jl Unit) (z : Cx T) (p : List (FV T)) :
    Jl (EvalpolyResult T) :=
  evalpolyComplex complexMuladd requireOneBased z p

/--
Julia source: base/math.jl:100-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function evalpoly(z::Complex, p::Tuple)
    if @generated
        N = length(p.parameters)
        a = :(p[end])
        b = :(p[end-1])
        as = []
        for i in N-2:-1:1
            ai = Symbol("a", i)
            push!(as, :($ai = $a))
            a = :(muladd(r, $ai, $b))
            b = :(muladd(-s, $ai, p[$i]))
        end
        ai = :a0
        push!(as, :($ai = $a))
        Expr(:block,
             :(x = real(z)),
             :(y = imag(z)),
             :(r = x + x),
             :(s = muladd(x, x, y*y)),
             as...,
             :(muladd($ai, z, $b)))
    else
        _evalpoly(z, p)
    end
end
```
-/
def evalpolyComplexTuple {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (requireOneBased : List (FV T) → Jl Unit) (generated : Bool)
    (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) :=
  if generated then evalpolyComplexBody complexMuladd z p
  else evalpolyComplexVector complexMuladd requireOneBased z p

/--
Julia source: base/math.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]
```
-/
def evalpolyComplexOne {T : FTy} (_z : Cx T) (c : FV T) : FV T := c

/--
Julia source: base/math.jl:157-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro horner(x, p...)
     xesc, pesc = esc(x), esc.(p)
    :(invoke(evalpoly, Tuple{Any, Tuple}, $xesc, ($(pesc...),)))
end
```
-/
def hornerMacro (x : JuliaSyntax) (p : List JuliaSyntax) : JuliaQuote :=
  .invoke "evalpoly" "Tuple{Any, Tuple}"
    [.escaped x, .tupleSplat (p.map JuliaQuote.escaped)]

/--
Julia source: base/math.jl:189-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro evalpoly(z, p...)
    zesc, pesc = esc(z), esc.(p)
    :(evalpoly($zesc, ($(pesc...),)))
end
```
-/
def evalpolyMacro (z : JuliaSyntax) (p : List JuliaSyntax) : JuliaQuote :=
  .call "evalpoly" [.escaped z, .tupleSplat (p.map JuliaQuote.escaped)]

/--
Julia source: base/math.jl:203-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _exthorner(i::Int, x::T, p::Tuple{T,T,T}, hi::T, lo::T) where T<:Union{Float32,Float64}
    i == 2 || i == 1 || error("unexpected index")
    pi = p[i]
    prod, err = two_mul(hi,x)
    hi = pi+prod
    lo = fma(lo, x, prod - (hi - pi) + err)
    return hi, lo
end
```
-/
def exthornerStep {T : FTy} (_wide : T = .f32 ∨ T = .f64)
    (o : IEEEOps T) (i : Int) (x : FV T)
    (p : FV T × FV T × FV T) (hi lo : FV T) :
    Except JuliaLean.base.error.JuliaException (FV T × FV T) := do
  if i != 2 && i != 1 then
    JuliaLean.base.error.errorVararg [.abstractString "unexpected index"]
  else
    let pi := if i = 2 then p.2.1 else p.1
    let (prod, err) := o.twoMul hi x
    let hi := add pi prod
    let lo := o.fma lo x (sub (sub prod (sub hi pi)) (fneg err))
    pure (hi, lo)
/--
Julia source: base/math.jl:196-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exthorner(x::T, p::Tuple{T,T,T}) where T<:Union{Float32,Float64}
    hi, lo = p[lastindex(p)], zero(x)
    hi, lo = _exthorner(2, x, p, hi, lo)
    hi, lo = _exthorner(1, x, p, hi, lo)
    return hi, lo
end
```
-/
def exthorner {T : FTy} (wide : T = .f32 ∨ T = .f64)
    (o : IEEEOps T) (x : FV T) (p : FV T × FV T × FV T) :
    Except JuliaLean.base.error.JuliaException (FV T × FV T) := do
  let hi := p.2.2
  let lo := fzero T
  let (hi, lo) ← exthornerStep wide o 2 x p hi lo
  exthornerStep wide o 1 x p hi lo

/--
Julia source: base/math.jl:937-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline throw1(x) = throw(DomainError(x, "Cannot be NaN or Inf."))
```
-/
def exponentThrow1 {T : FTy} (_x : FV T) : Jl Int := .error (.domainError "Cannot be NaN or Inf.")

/--
Julia source: base/math.jl:938-938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline throw2(x) = throw(DomainError(x, "Cannot be ±0.0."))
```
-/
def exponentThrow2 {T : FTy} (_x : FV T) : Jl Int := .error (.domainError "Cannot be ±0.0.")

/--
Julia source: base/math.jl:936-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::T) where T<:IEEEFloat
    @noinline throw1(x) = throw(DomainError(x, "Cannot be NaN or Inf."))
    @noinline throw2(x) = throw(DomainError(x, "Cannot be ±0.0."))
    xs = reinterpret(Unsigned, x) & ~sign_mask(T)
    xs >= exponent_mask(T) && throw1(x)
    # use `% Int` instead of `Int(...)` to preserve `:nothrow` (the shifted value
    # always fits in `exponent_bits(T)` bits, well below `typemax(Int)`)
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && throw2(x)
        m = leading_zeros(xs) - exponent_bits(T)
        k = 1 - m
    end
    return k - exponent_bias(T)
end
```
-/
def exponentFloat {T : FTy} (x : FV T) : Jl Int :=
  let xs := withoutBits x.toBits (signMask T) T.fmt.width
  if xs >= exponentMask T then exponentThrow1 x
  else
    let k : Int := (xs / 2 ^ significandBits T : Nat)
    if k == 0 then
      if xs == 0 then exponentThrow2 x
      else
        let m := leadingZeros T.fmt.width xs - exponentBits T
        .ok ((1 - (m : Int)) - exponentBias T)
    else .ok (k - exponentBias T)

/--
Julia source: base/math.jl:629-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sqrt(x::IEEEFloat)
    x < zero(x) && throw_complex_domainerror(:sqrt, x)
    sqrt_llvm(x)
end
```
-/
def sqrtIEEE {T : FTy} (o : IEEEOps T) (x : FV T) : Jl (FV T) :=
  if flt x (fzero T) then throwComplexDomainError "sqrt" x else .ok (o.sqrtLlvm x)

/--
Julia source: base/math.jl:1100-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scaleinv(x::T) where T<:IEEEFloat
    # by removing the sign and significand and restricting values to a limited range,
    # we can invert a number using bit-twiddling instead of division
    U = uinttype(T)
    umin = reinterpret(U, floatmin(T))
    umax = reinterpret(U, inv(floatmin(T)))
    emask = exponent_mask(T) # used to strip sign and significand
    u = clamp(reinterpret(U, x) & emask, umin, umax)
    scale = reinterpret(T, u)
    invscale = reinterpret(T, umin + umax - u) # inv(scale)
    return scale, invscale
end
```
-/
def scaleinv {T : FTy} (o : IEEEOps T) (x : FV T) : FV T × FV T :=
  let umin := o.floatmin.toBits
  let umax := o.invFloatmin.toBits
  let e := (x.toBits / 2 ^ significandBits T % 2 ^ exponentBits T) * 2 ^ significandBits T
  let u := o.clampUnsigned e umin umax
  (Fl.ofBits u, Fl.ofBits (umin + umax - u))

/--
Julia source: base/math.jl:826-826 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    add_fast(x, y) = Core.Intrinsics.add_float_fast(x, y) # @fastmath is not available during bootstrap
```
-/
def addFast {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.addFast x y

def hypotOpsOfIEEE {T : FTy} (o : IEEEOps T) : GenericHypotOps (FV T) (FV T) :=
  { abs := fabs
    oneunit := o.oneunit
    isinf := fisinf
    isnan := fisnan
    iszero := fiszero
    isless := Fl.isless
    lt := flt
    greater := o.greater
    le := fle
    zero := fzero T
    one := fone T
    infinity := finf T
    eps := o.eps
    floatmin := o.floatmin
    floatmax := o.floatmax
    two := Fl.ofInt 2
    four := Fl.ofInt 4
    inverse := o.inverse
    sqrt := sqrtIEEE o
    mul := mul
    div := div
    add := add
    sub := sub
    muladd := o.muladd
    fma := o.fma
    divideInput := div
    abs2 := o.abs2
    haveFma := o.haveFma }
/--
Julia source: base/math.jl:732-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x, y)
    # preserves unit
    axu = abs(x)
    ayu = abs(y)

    # unitless
    ax = axu / oneunit(axu)
    ay = ayu / oneunit(ayu)

    # Return Inf if either or both inputs is Inf (Compliance with IEEE754)
    if isinf(ax) || isinf(ay)
        return typeof(axu)(Inf)
    end

    # Order the operands
    if ay > ax
        axu = ayu
        ax, ay = ay, ax
    end

    # Widely varying operands
    if ay <= ax*sqrt(eps(typeof(ax))/2)  #Note: This also gets ay == 0
        return axu
    end

    # Operands do not vary widely
    scale = eps(typeof(ax))*sqrt(floatmin(ax))  #Rescaling constant
    if ax > sqrt(floatmax(ax)/2)
        ax = ax*scale
        ay = ay*scale
        scale = inv(scale)
    elseif ay < sqrt(floatmin(ax))
        ax = ax/scale
        ay = ay/scale
    else
        scale = oneunit(scale)
    end
    h = sqrt(muladd(ax, ax, ay*ay))
    # This branch is correctly rounded but requires a native hardware fma.
    if Core.Intrinsics.have_fma(typeof(h))
        hsquared = h*h
        axsquared = ax*ax
        h -= (fma(-ay, ay, hsquared-axsquared) + fma(h, h,-hsquared) - fma(ax, ax, -axsquared))/(2*h)
    # This branch is within one ulp of correctly rounded.
    else
        if h <= 2*ay
            delta = h-ay
            h -= muladd(delta, delta-2*(ax-ay), ax*(2*delta - ax))/(2*h)
        else
            delta = h-ax
            h -= muladd(delta, delta, muladd(ay, (4*delta - ay), 2*delta*(ax - 2*ay)))/(2*h)
        end
    end
    return h*scale*oneunit(axu)
end
```
-/
def hypotGeneric {α β : Type} (o : GenericHypotOps α β) (x y : α) : Jl β := do
  let axu0 := o.abs x
  let ayu := o.abs y
  let ax0 := o.div axu0 (o.oneunit axu0)
  let ay0 := o.div ayu (o.oneunit ayu)
  if o.isinf ax0 || o.isinf ay0 then return o.infinity
  let (axu, ax, ay) :=
    if o.greater ay0 ax0 then (ayu, ay0, ax0) else (axu0, ax0, ay0)
  let cutoff ← o.sqrt (o.div o.eps o.two)
  if o.le ay (o.mul ax cutoff) then return axu
  let minRoot ← o.sqrt o.floatmin
  let scale0 := o.mul o.eps minRoot
  let bigRoot ← o.sqrt (o.div o.floatmax o.two)
  let (ax, ay, scale) :=
    if o.greater ax bigRoot then
      (o.mul ax scale0, o.mul ay scale0, o.inverse scale0)
    else if o.lt ay minRoot then
      (o.div ax scale0, o.div ay scale0, scale0)
    else (ax, ay, o.oneunit scale0)
  let h0 ← o.sqrt (o.muladd ax ax (o.mul ay ay))
  let h :=
    if o.haveFma then
      let hsquared := o.mul h0 h0
      let axsquared := o.mul ax ax
      let correction := o.sub
        (o.add (o.fma (o.sub o.zero ay) ay (o.sub hsquared axsquared))
          (o.fma h0 h0 (o.sub o.zero hsquared)))
        (o.fma ax ax (o.sub o.zero axsquared))
      o.sub h0 (o.div correction (o.mul o.two h0))
    else if o.le h0 (o.mul o.two ay) then
      let delta := o.sub h0 ay
      o.sub h0 (o.div
        (o.muladd delta (o.sub delta (o.mul o.two (o.sub ax ay)))
          (o.mul ax (o.sub (o.mul o.two delta) ax)))
        (o.mul o.two h0))
    else
      let delta := o.sub h0 ax
      let inner := o.muladd ay
        (o.sub (o.mul o.four delta) ay)
        (o.mul o.two (o.mul delta (o.sub ax (o.mul o.two ay))))
      o.sub h0 (o.div (o.muladd delta delta inner) (o.mul o.two h0))
  return o.mul (o.mul h scale) (o.oneunit axu)

/--
Julia source: base/math.jl:805-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x::NTuple{N,<:Number}) where {N}
    maxabs = maximum(abs, x)
    if isnan(maxabs) && any(isinf, x)
        return typeof(maxabs)(Inf)
    elseif (iszero(maxabs) || isinf(maxabs))
        return maxabs
    else
        return maxabs * sqrt(sum(y -> abs2(y / maxabs), x))
    end
end
```
-/
def hypotTupleGeneric {α β : Type} (o : GenericHypotOps α β)
    (iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
      JuliaLean.base.reduce.EltypeStatus)
    (maximumReducer sumReducer : JuliaLean.base.reduce.Reducer β β)
    (isinfInput : α → Bool) (xs : List α) : Jl β := do
  let maxabs ← JuliaLean.base.reduce.maximum_f iteratorEltype o.abs maximumReducer
    (.values xs) .initial
  if o.isnan maxabs && xs.any isinfInput then return o.infinity
  else if o.iszero maxabs || o.isinf maxabs then return maxabs
  else
    let sum ← JuliaLean.base.reduce.sum_f iteratorEltype
      (fun y => o.abs2 (o.divideInput y maxabs)) sumReducer (.values xs) .initial
    let root ← o.sqrt sum
    pure (o.mul maxabs root)
/--
Julia source: base/math.jl:816-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x::NTuple{N,<:IEEEFloat}) where {N}
    T = eltype(x)
    infT = convert(T, Inf)
    x = abs.(x) # doesn't change result but enables computational shortcuts
    # note: any() was causing this to not inline for N=3 but mapreduce() was not
    mapreduce(==(infT), |, x) && return infT # return Inf even if an argument is NaN
    maxabs = reinterpret(T, maximum(z -> reinterpret(Signed, z), x)) # for abs(::IEEEFloat) values, a ::BitInteger cast does not change the result
    maxabs > zero(T) || return maxabs # catch NaN before the @fastmath below, but also shortcut 0 since we can (remove if no more @fastmath below)
    scale,invscale = scaleinv(maxabs)
     # @fastmath(+) to allow reassociation (see #48129)
    add_fast(x, y) = Core.Intrinsics.add_float_fast(x, y) # @fastmath is not available during bootstrap
    return scale * sqrt(mapreduce(y -> abs2(y * invscale), add_fast, x))
end
```
-/
def hypotTupleIEEE {T : FTy} (o : IEEEOps T)
    (ops : HypotFloatReductionOps T) (xs : List (FV T)) : Jl (FV T) := do
  let xs := xs.map fabs
  let hasInfinity ← JuliaLean.base.reduce.mapreduce ops.iteratorEltype
    (fun x => feq x (finf T)) ops.booleanOr (.values xs) .initial
  if hasInfinity then return finf T
  let maxSigned ← JuliaLean.base.reduce.maximum_f ops.iteratorEltype
    ops.reinterpretSigned ops.maximumReducer (.values xs) .initial
  let maxabs := ops.reinterpretFloat maxSigned
  if !flt (fzero T) maxabs then return maxabs
  let (scale, invscale) := scaleinv o maxabs
  let sum ← JuliaLean.base.reduce.mapreduce ops.iteratorEltype
    (fun y => o.abs2 (mul y invscale)) ops.sumReducer (.values xs) .initial
  let root ← sqrtIEEE o sum
  pure (mul scale root)

/--
Julia source: base/math.jl:789-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function _hypot(x::Float32, y::Float32)
    if isinf(x) || isinf(y)
        return Inf32
    end
    _x, _y = Float64(x), Float64(y)
    return Float32(sqrt(muladd(_x, _x, _y*_y)))
end
```
-/
def hypot32 (o64 : IEEEOps .f64) (x y : FV .f32) : Jl (FV .f32) := do
  if fisinf x || fisinf y then return finf .f32
  let x64 := Fl.convert x
  let y64 := Fl.convert y
  let r ← sqrtIEEE o64 (muladd (mul (T := .f64)) (add (T := .f64)) x64 x64 (mul y64 y64))
  pure (Fl.convert r)

/--
Julia source: base/math.jl:796-802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function _hypot(x::Float16, y::Float16)
    if isinf(x) || isinf(y)
        return Inf16
    end
    _x, _y = Float32(x), Float32(y)
    return Float16(sqrt(muladd(_x, _x, _y*_y)))
end
```
-/
def hypot16 (o32 : IEEEOps .f32) (x y : FV .f16) : Jl (FV .f16) := do
  if fisinf x || fisinf y then return finf .f16
  let x32 := Fl.convert x
  let y32 := Fl.convert y
  let r ← sqrtIEEE o32 (muladd (mul (T := .f32)) (add (T := .f32)) x32 x32 (mul y32 y32))
  pure (Fl.convert r)

/--
Julia source: base/math.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hypot(x::ComplexF16, y::ComplexF16) = Float16(_hypot(ComplexF32(x), ComplexF32(y)))
```
-/
def hypotComplex16 (o32 : GenericHypotOps (Cx .f32) (FV .f32))
    (x y : Cx .f16) : Jl (FV .f16) := do
  let x32 : Cx .f32 := ⟨Fl.convert x.re, Fl.convert x.im⟩
  let y32 : Cx .f32 := ⟨Fl.convert y.re, Fl.convert y.im⟩
  let r ← hypotGeneric o32 x32 y32
  pure (Fl.convert r)
def hypotDispatchFloat16 (o16 : IEEEOps .f16) (o32 : IEEEOps .f32)
    (reduce16 : HypotFloatReductionOps .f16) :
    HypotDispatch (FV .f16) (FV .f16) :=
  { pair := hypot16 o32, tuple := hypotTupleIEEE o16 reduce16 }

def hypotDispatchFloat32 (o32 : IEEEOps .f32) (o64 : IEEEOps .f64)
    (reduce32 : HypotFloatReductionOps .f32) :
    HypotDispatch (FV .f32) (FV .f32) :=
  { pair := hypot32 o64, tuple := hypotTupleIEEE o32 reduce32 }

def hypotDispatchFloat64 (o64 : IEEEOps .f64)
    (reduce64 : HypotFloatReductionOps .f64) :
    HypotDispatch (FV .f64) (FV .f64) :=
  { pair := hypotGeneric (hypotOpsOfIEEE o64), tuple := hypotTupleIEEE o64 reduce64 }

def hypotDispatchComplex16
    (iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
      JuliaLean.base.reduce.EltypeStatus)
    (maximumReducer sumReducer : JuliaLean.base.reduce.Reducer (FV .f16) (FV .f16))
    (isinfInput : Cx .f16 → Bool)
    (pairOps : GenericHypotOps (Cx .f32) (FV .f32))
    (tupleOps : GenericHypotOps (Cx .f16) (FV .f16)) :
    HypotDispatch (Cx .f16) (FV .f16) :=
  { pair := hypotComplex16 pairOps
    tuple := hypotTupleGeneric tupleOps iteratorEltype maximumReducer sumReducer isinfInput }

/--
Julia source: base/math.jl:729-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number) = abs(float(x))
```
-/
def hypotOne {α β γ : Type} (float : α → β) (abs : β → γ) (x : α) : γ :=
  abs (float x)

/--
Julia source: base/math.jl:730-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number, y::Number) = _hypot(float.(promote(x, y))...)
```
-/
def hypotTwo {α β γ δ ε : Type} (promote : α → β → γ × γ) (float : γ → δ)
    (dispatch : HypotDispatch δ ε) (x : α) (y : β) : Jl ε := do
  let (xp, yp) := promote x y
  dispatch.pair (float xp) (float yp)

/--
Julia source: base/math.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number, y::Number, xs::Number...) = _hypot(float.(promote(x, y, xs...)))
```
-/
def hypotMany {α β γ δ : Type} (promote : List α → List β) (float : β → γ)
    (dispatch : HypotDispatch γ δ) (xs : List α) : Jl δ :=
  dispatch.tuple ((promote xs).map float)

/--
Julia source: base/math.jl:854-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ldexp(x::T, e::Integer) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x # NaN or Inf
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && return x # +-0
        m = leading_zeros(xs) - exponent_bits(T)
        ys = xs << unsigned(m)
        xu = ys | (xu & sign_mask(T))
        k = 1 - m
        # underflow, otherwise may have integer underflow in the following n + k
        e < -50000 && return flipsign(T(0.0), x)
    end
    # For cases where e of an Integer larger than Int make sure we properly
    # overflow/underflow; this is optimized away otherwise.
    if e > typemax(Int)
        return flipsign(T(Inf), x)
    elseif e < typemin(Int)
        return flipsign(T(0.0), x)
    end
    n = e % Int
    k = k +% n
    # overflow, if k is larger than maximum possible exponent
    if k >= exponent_raw_max(T)
        return flipsign(T(Inf), x)
    end
    if k > 0 # normal case
        xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
        return reinterpret(T, xu)
    else # subnormal case
        # results with k == -significand_bits(T) are at least nextfloat(zero(T))/2, so may round up
        if k <= -significand_bits(T) - 1 # underflow
            # overflow, for the case of integer overflow in n + k
            e > 50000 && return flipsign(T(Inf), x)
            return flipsign(T(0.0), x)
        end
        k += significand_bits(T) + 1
        # z = T(2.0) ^ (-significand_bits(T) - 1)
        z = reinterpret(T, rem(exponent_bias(T)-significand_bits(T)-1, uinttype(T)) << significand_bits(T))
        xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
        return z*reinterpret(T, xu)
    end
end
```
-/
def ldexp {T : FTy} (o : IEEEOps T) (x : FV T) (e : Int) : FV T := Id.run do
  let xu0 := x.toBits
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return x
  let mut xu := xu0
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return x
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let ys := xs * 2 ^ m
    xu := ys + (if fsignbit x then signMask T else 0)
    k := 1 - (m : Int)
    if e < -50000 then return o.flipsign (fzero T) x
  if e > IntTy.max .i64 then return o.flipsign (finf T) x
  else if e < IntTy.min .i64 then return o.flipsign (fzero T) x
  let n := wrapInt .i64 e
  k := wrapInt .i64 (k + n)
  if k >= exponentRawMax T then return o.flipsign (finf T) x
  if k > 0 then
    xu := withoutBits xu (exponentMask T) T.fmt.width + k.toNat * 2 ^ significandBits T
    return Fl.ofBits xu
  else
    if k <= -(significandBits T : Int) - 1 then
      if e > 50000 then return o.flipsign (finf T) x
      return o.flipsign (fzero T) x
    k := k + significandBits T + 1
    let z : FV T := Fl.ofBits ((exponentBias T - significandBits T - 1) * 2 ^ significandBits T)
    xu := withoutBits xu (exponentMask T) T.fmt.width + k.toNat * 2 ^ significandBits T
    return mul z (Fl.ofBits xu)

/--
Julia source: base/math.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ldexp(x::Float16, q::Integer) = Float16(ldexp(Float32(x), q))
```
-/
def ldexp16 (o32 : IEEEOps .f32) (x : FV .f16) (q : Int) : FV .f16 :=
  Fl.convert (ldexp o32 (Fl.convert x) q)

/--
Julia source: base/math.jl:967-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ilog2_step(y::T, d::T, s) where {T<:Integer}
    if (y >> s) >= d
        y, n = _ilog2_step(y, d*d, s+s)
    else
        n = 0
    end
    if y >= d
        y >>= s
        n = Base.checked_add(n, s)
    end
    return y, n
end
```
-/
def ilog2Step {T : Type} (o : IntegerStepOps T) (y d : T) (s : Int)
    (continuation : Jl (T × Int) → Jl (T × Int) := id) :
    Option (Jl (T × Int)) :=
  let finish := fun result => continuation (do
    let (y, n) ← result
    if o.ge y d then
      let n ← o.checkedAdd n s
      pure (o.shiftRight y s, n)
    else pure (y, n))
  if o.ge (o.shiftRight y s) d then
    ilog2Step o y (o.mul d d) (s + s) finish
  else some (finish (.ok (y, 0)))
partial_fixpoint

/--
Julia source: base/math.jl:980-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Integer)
    iszero(x) && throw(DomainError(x, "cannot be zero"))
    ux = Base.uabs(x)
    _, n = _ilog2_step(ux, one(ux) + one(ux), 1)
    return n
end
```
-/
def exponentInteger {X U : Type} (o : IntegerExponentOps X U) (x : X) :
    Option (Jl Int) :=
  if o.iszero x then some (.error (.domainError "cannot be zero"))
  else
    let ux := o.uabs x
    (ilog2Step o.step ux (o.step.add o.step.one o.step.one) 1).map
      (fun result => result.map Prod.snd)

/--
Julia source: base/math.jl:987-991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Base.BitInteger)
    iszero(x) && throw(DomainError(x, "cannot be zero"))
    ux = Base.uabs(x)
    return 8sizeof(ux) - leading_zeros(ux) - 1
end
```
-/
def exponentBitInteger {t : IntTy} (x : JInt t) : Jl Int :=
  if x.val == 0 then .error (.domainError "cannot be zero")
  else .ok ((t.bits : Int) - leadingZeros t.bits x.val.natAbs - 1)

/--
Julia source: base/math.jl:993-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Bool)
    if x
        0
    else
        throw(DomainError(x, "cannot be zero"))
    end
end
```
-/
def exponentBool (x : Bool) : Jl Int :=
  if x then .ok 0 else .error (.domainError "cannot be zero")

/--
Julia source: base/math.jl:1276-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::UInt64)  = (x >>> 32) % UInt32
```
-/
def highwordUInt64 (x : JInt .u64) : JInt .u32 :=
  JInt.wrap .u32 (x.val.toNat / 2 ^ 32)

/--
Julia source: base/math.jl:1275-1275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::Float64) = highword(reinterpret(UInt64, x))
```
-/
def highword64 (x : FV .f64) : JInt .u32 :=
  highwordUInt64 (JInt.wrap .u64 x.toBits)

/--
Julia source: base/math.jl:1277-1277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::Float32) = reinterpret(UInt32, x)
```
-/
def highword32 (x : FV .f32) : JInt .u32 := JInt.wrap .u32 x.toBits

/--
Julia source: base/math.jl:1289-1289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::UInt64)  = highword(x) & 0x7fffffff
```
-/
def poshighwordUInt64 (x : JInt .u64) : JInt .u32 :=
  JInt.wrap .u32 (Nat.land (x.val.toNat / 2 ^ 32) 0x7fffffff)

/--
Julia source: base/math.jl:1288-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::Float64) = poshighword(reinterpret(UInt64, x))
```
-/
def poshighword64 (x : FV .f64) : JInt .u32 :=
  poshighwordUInt64 (JInt.wrap .u64 x.toBits)

/--
Julia source: base/math.jl:1279-1279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline fromhighword(::Type{Float64}, u::UInt32) = reinterpret(Float64, UInt64(u) << 32)
```
-/
def fromhighword64 (u : JInt .u32) : FV .f64 := Fl.ofBits (u.val.toNat * 2 ^ 32)

/--
Julia source: base/math.jl:1280-1280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline fromhighword(::Type{Float32}, u::UInt32) = reinterpret(Float32, u)
```
-/
def fromhighword32 (u : JInt .u32) : FV .f32 := Fl.ofBits u.val.toNat

/--
Julia source: base/math.jl:1290-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::Float32) = highword(x) & 0x7fffffff
```
-/
def poshighword32 (x : FV .f32) : JInt .u32 :=
  JInt.wrap .u32 (Nat.land x.toBits 0x7fffffff)


/--
Julia source: base/math.jl:36-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_complex_domainerror_neg1(f::Symbol, x)
    throw(DomainError(x,
        LazyString(f," was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try ", f,"(Complex(x)).")))
end
```
-/
def throwComplexDomainErrorNeg1 {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError (f ++ " was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try " ++ f ++ "(Complex(x))."))

/--
Julia source: base/math.jl:40-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_finite_domainerror(f::Symbol, x)
    throw(DomainError(x, LazyString("`", f, "(x)` is only defined for finite `x`.")))
end
```
-/
def throwFiniteDomainError {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError ("`" ++ f ++ "(x)` is only defined for finite `x`."))

/--
Julia source: base/math.jl:43-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_exp_domainerror(x)
    throw(DomainError(x, LazyString(
        "Exponentiation yielding a complex result requires a ",
        "complex argument.\nReplace x^y with (x+0im)^y, ",
        "Complex(x)^y, or similar.")))
end
```
-/
def throwExpDomainError {α : Type} (_x : α) : Jl α :=
  .error (.domainError "Exponentiation yielding a complex result requires a complex argument.\nReplace x^y with (x+0im)^y, Complex(x)^y, or similar.")

/--
Julia source: base/math.jl:213-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _180_over_pi(z::AbstractFloat)
    180 / oftype(z, pi)
end
```
-/
def oneEightyOverPi {α : Type} (o : AbstractFloatOps α) (_z : α) : α :=
  o.div (o.ofInt 180) o.pi

/--
Julia source: base/math.jl:216-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pi_over_180(z::AbstractFloat)
    oftype(z, pi) / 180
end
```
-/
def piOverOneEighty {α : Type} (o : AbstractFloatOps α) (_z : α) : α :=
  o.div o.pi (o.ofInt 180)

/--
Julia source: base/math.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_180_over_pi(::Float16) = Float16(57.28)
```
-/
def oneEightyOverPi16 : FV .f16 := Fl.roundRat 5728 100 false

/--
Julia source: base/math.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_180_over_pi(::Float32) = 57.29578f0
```
-/
def oneEightyOverPi32 : FV .f32 := Fl.roundRat 5729578 100000 false

/--
Julia source: base/math.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pi_over_180(::Float16) = Float16(0.01746)
```
-/
def piOverOneEighty16 : FV .f16 := Fl.roundRat 1746 100000 false
def oneEightyOverPiDispatch : (T : FTy) → IEEEOps T → FV T → FV T
  | .f16, _, _ => oneEightyOverPi16
  | .f32, _, _ => oneEightyOverPi32
  | .f64, o, _ => div (Fl.ofInt 180) o.pi

def piOverOneEightyDispatch : (T : FTy) → IEEEOps T → FV T → FV T
  | .f16, _, _ => piOverOneEighty16
  | .f32, o, _ => div o.pi (Fl.ofInt 180)
  | .f64, o, _ => div o.pi (Fl.ofInt 180)
def abstractFloatOpsOfIEEE {T : FTy} (o : IEEEOps T) : AbstractFloatOps (FV T) where
  typeName := match T with
    | .f16 => "Float16"
    | .f32 => "Float32"
    | .f64 => "Float64"
  ofInt := Fl.ofInt
  pi := o.pi
  mul := mul
  div := div
  pow := o.pow
  abs := fabs
  isnan := fisnan
  signbit := fsignbit
  lt := flt
  rad2degFactor := oneEightyOverPiDispatch T o
  deg2radFactor := piOverOneEightyDispatch T o

/--
Julia source: base/math.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::AbstractFloat) = z * _180_over_pi(z)
```
-/
def rad2degFloat {α : Type} (o : AbstractFloatOps α) (z : α) : α :=
  o.mul z (o.rad2degFactor z)

/--
Julia source: base/math.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::AbstractFloat) = z * _pi_over_180(z)
```
-/
def deg2radFloat {α : Type} (o : AbstractFloatOps α) (z : α) : α :=
  o.mul z (o.deg2radFactor z)

/--
Julia source: base/math.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::Real) = rad2deg(float(z))
```
-/
def rad2degReal {α β : Type} (o : AbstractFloatOps β) (float : α → β) (z : α) : β :=
  rad2degFloat o (float z)

/--
Julia source: base/math.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::Real) = deg2rad(float(z))
```
-/
def deg2radReal {α β : Type} (o : AbstractFloatOps β) (float : α → β) (z : α) : β :=
  deg2radFloat o (float z)

/--
Julia source: base/math.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::Number) = (z/pi)*180
```
-/
def rad2degNumber {α : Type} (div mul : α → α → α) (pi : α) (z : α) (oneEighty : α) : α :=
  mul (div z pi) oneEighty

/--
Julia source: base/math.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::Number) = (z*pi)/180
```
-/
def deg2radNumber {α : Type} (mul div : α → α → α) (pi : α) (z : α) (oneEighty : α) : α :=
  div (mul z pi) oneEighty

/--
Julia source: base/math.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
log(b::T, x::T) where {T<:Number} = log(x)/log(b)
```
-/
def logBase {α : Type} (logFn : α → Jl α) (divFn : α → α → α) (b x : α) : Jl α := do
  return divFn (← logFn x) (← logFn b)

/--
Julia source: base/math.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
log(b::Number, x::Number) = log(promote(b,x)...)
```
-/
def logBaseNumber {α β γ : Type} (promote : α → β → γ × γ)
    (logFn : γ → Jl γ) (divFn : γ → γ → γ) (b : α) (x : β) : Jl γ :=
  let (b, x) := promote b x
  logBase logFn divFn b x

/--
Julia source: base/math.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline nan_dom_err(out, x) = isnan(out) & !isnan(x) ? throw(DomainError(x, "NaN result for non-NaN input.")) : out
```
-/
def nanDomErr {T S : FTy} (out : FV T) (x : FV S) : Jl (FV T) :=
  if fisnan out && !fisnan x then .error (.domainError "NaN result for non-NaN input.") else .ok out

/--
Julia source: base/math.jl:685-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fourthroot(x::Number) = sqrt(sqrt(x))
```
-/
def fourthroot {α : Type} (sqrtFn : α → Jl α) (x : α) : Jl α := do
  sqrtFn (← sqrtFn x)

/--
Julia source: base/math.jl:830-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(y::Real, x::Real) = atan(promote(float(y),float(x))...)
```
-/
def atanReal {α β γ : Type} (float : α → β) (float2 : γ → β)
    (promote : β → β → β × β) (atanFloat : β → β → Jl β) (y : α) (x : γ) : Jl β :=
  let (yp, xp) := promote (float y) (float2 x)
  atanFloat yp xp

/--
Julia source: base/math.jl:831-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(y::T, x::T) where {T<:AbstractFloat} = Base.no_op_err("atan", T)
```
-/
def atanNoOp {α : Type} (o : AbstractFloatOps α) : Except
    JuliaLean.base.error.JuliaException α :=
  JuliaLean.base.promotion.noOpErr (fun (_ : Unit) => o.typeName)
    (fun message => JuliaLean.base.error.errorVararg [.abstractString message]) "atan" ()

/--
Julia source: base/math.jl:833-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isless(x::T, y::T) where {T<:AbstractFloat} = (x < y) || (signbit(x) > signbit(y))
```
-/
def islessFloat {α : Type} (o : AbstractFloatOps α) (x y : α) : Bool :=
  o.lt x y || (o.signbit x && !o.signbit y)

/--
Julia source: base/math.jl:834-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:AbstractFloat} = isnan(x) || ~isnan(y) && _isless(x, y) ? x : y
```
-/
def minGeneric {α : Type} (o : AbstractFloatOps α) (x y : α) : α :=
  if o.isnan x || (!o.isnan y && islessFloat o x y) then x else y

/--
Julia source: base/math.jl:835-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:AbstractFloat} = isnan(x) || ~isnan(y) && _isless(y, x) ? x : y
```
-/
def maxGeneric {α : Type} (o : AbstractFloatOps α) (x y : α) : α :=
  if o.isnan x || (!o.isnan y && islessFloat o y x) then x else y


/--
Julia source: base/math.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:IEEEFloat} = min_float(x, y)
```
-/
def minIEEE {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.minFloat x y

/--
Julia source: base/math.jl:839-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:IEEEFloat} = max_float(x, y)
```
-/
def maxIEEE {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.maxFloat x y

/--
Julia source: base/math.jl:836-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::T, y::T) where {T<:AbstractFloat} = min(x, y), max(x, y)
```
-/
def minmaxGeneric {α : Type} (minFn maxFn : α → α → α) (x y : α) : α × α :=
  (minFn x y, maxFn x y)
/--
Julia source: base/math.jl:956-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _exponent_finite_nonzero(x::T) where T<:IEEEFloat
    # @precond :nothrow !isnan(x) && !isinf(x) && !iszero(x)
    xs = reinterpret(Unsigned, x) & ~sign_mask(T)
    k = rem(xs >> significand_bits(T), Int)
    if k == 0 # x is subnormal
        m = leading_zeros(xs) - exponent_bits(T)
        k = 1 - m
    end
    return k - exponent_bias(T)
end
```
-/
def exponentFiniteNonzero {T : FTy} (x : FV T) : Int :=
  let xs := withoutBits x.toBits (signMask T) T.fmt.width
  let k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    let m := leadingZeros T.fmt.width xs - exponentBits T
    (1 - (m : Int)) - exponentBias T
  else k - exponentBias T

/--
Julia source: base/math.jl:1026-1038 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function significand(x::T) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x # NaN or Inf
    if xs <= (~exponent_mask(T) & ~sign_mask(T)) # x is subnormal
        xs == 0 && return x # +-0
        m = unsigned(leading_zeros(xs) - exponent_bits(T))
        xs <<= m
        xu = xs | (xu & sign_mask(T))
    end
    xu = (xu & ~exponent_mask(T)) | exponent_one(T)
    return reinterpret(T, xu)
end
```
-/
def significand {T : FTy} (x : FV T) : FV T := Id.run do
  let xu0 := x.toBits
  let mut xu := xu0
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return x
  if xs <= bitMask T.fmt.width - exponentMask T - signMask T then
    if xs == 0 then return x
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let xs := xs * 2 ^ m
    xu := xs + (if fsignbit x then signMask T else 0)
  xu := withoutBits xu (exponentMask T) T.fmt.width + exponentBias T * 2 ^ significandBits T
  return Fl.ofBits xu

/--
Julia source: base/math.jl:1060-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frexp(x::T) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x, 0 # NaN or Inf
    # use `% Int` instead of `Int(...)` to preserve `:nothrow` (after masking the sign
    # bit, xs >> significand_bits(T) is at most 2^exponent_bits(T)-1, which always fits in Int)
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && return x, 0 # +-0
        m = leading_zeros(xs) - exponent_bits(T)
        xs <<= unsigned(m)
        xu = xs | (xu & sign_mask(T))
        k = 1 - m
    end
    k -= (exponent_bias(T) - 1)
    xu = (xu & ~exponent_mask(T)) | exponent_half(T)
    return reinterpret(T, xu), k
end
```
-/
def frexp {T : FTy} (x : FV T) : FV T × Int := Id.run do
  let xu0 := x.toBits
  let mut xu := xu0
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return (x, 0)
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return (x, 0)
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let xs := xs * 2 ^ m
    xu := xs + (if fsignbit x then signMask T else 0)
    k := 1 - m
  k := k - (exponentBias T - 1)
  xu := withoutBits xu (exponentMask T) T.fmt.width + (exponentBias T - 1) * 2 ^ significandBits T
  return (Fl.ofBits xu, k)

/--
Julia source: base/math.jl:1122-1145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::T, p::T, ::RoundingMode{:Nearest}) where T<:IEEEFloat
    (iszero(p) || !isfinite(x) || isnan(p)) && return T(NaN)
    x == p && return copysign(zero(T), x)
    oldx = x
    x = abs(rem(x, 2p))  # 2p may overflow but that's okay
    p = abs(p)
    if p < 2 * floatmin(T)  # Check whether dividing p by 2 will underflow
        if 2x > p
            x -= p
            if 2x >= p
                x -= p
            end
        end
    else
        p_half = p / 2
        if x > p_half
            x -= p
            if x >= p_half
                x -= p
            end
        end
    end
    return flipsign(x, oldx)
end
```
-/
def remNearest {T : FTy} (o : IEEEOps T) (x0 p0 : FV T) : FV T := Id.run do
  if fiszero p0 || !fisfinite x0 || fisnan p0 then return fnan T
  if feq x0 p0 then return JuliaLean.base.float.copysign_float (fzero T) x0
  let oldx := x0
  let mut x := fabs (o.rem x0 (mul p0 (Fl.ofInt 2)))
  let p := fabs p0
  if flt p (mul (Fl.ofInt 2) o.floatmin) then
    if flt p (mul (Fl.ofInt 2) x) then
      x := sub x p
      if fle p (mul (Fl.ofInt 2) x) then x := sub x p
  else
    let pHalf := div p (Fl.ofInt 2)
    if flt pHalf x then
      x := sub x p
      if fle pHalf x then x := sub x p
  return o.flipsign x oldx

/--
Julia source: base/math.jl:1163-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
modf(x) = isinf(x) ? (flipsign(zero(x), x), x) : (rem(x, one(x)), trunc(x))
```
-/
def modfGeneric {α : Type} (isinf : α → Bool) (zero one trunc : α → α)
    (flip rem : α → α → α) (x : α) : α × α :=
  if isinf x then (flip (zero x) x, x) else (rem x (one x), trunc x)

/--
Julia source: base/math.jl:1165-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modf(x::T) where T<:IEEEFloat
    isinf(x) && return (copysign(zero(T), x), x)
    ix = trunc(x)
    rx = copysign(x - ix, x)
    return (rx, ix)
end
```
-/
def modfIEEE {T : FTy} (o : IEEEOps T) (x : FV T) : FV T × FV T :=
  if fisinf x then (JuliaLean.base.float.copysign_float (fzero T) x, x)
  else
    let ix := o.trunc x
    let rx := JuliaLean.base.float.copysign_float (sub x ix) x
    (rx, ix)

/--
Julia source: base/math.jl:1176-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add22condh(xh::Float64, xl::Float64, yh::Float64, yl::Float64)
    # This algorithm, due to Dekker, computes the sum of two
    # double-double numbers and returns the high double. References:
    # [1] http://www.digizeitschriften.de/en/dms/img/?PID=GDZPPN001170007
    # [2] https://doi.org/10.1007/BF01397083
    r = xh+yh
    s = (abs(xh) > abs(yh)) ? (xh-r+yh+yl+xl) : (yh-r+xh+xl+yl)
    zh = r+s
    return zh
end
```
-/
def add22condh (xh xl yh yl : FV .f64) : FV .f64 :=
  let r := add xh yh
  let s := if flt (fabs yh) (fabs xh)
    then add (add (add (sub xh r) yh) yl) xl
    else add (add (add (sub yh r) xh) xl) yl
  let zh := add r s
  zh

/--
Julia source: base/math.jl:1241-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod2pi(x) = rem2pi(x,RoundDown)
```
-/
def mod2pi {α : Type} (rem2pi : α → JuliaLean.base.float.RoundingMode → α) (x : α) : α :=
  rem2pi x .Down

/--
Julia source: base/math.jl:1309-1309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $func(a::Float16) = Float16($func(Float32(a)))
```
-/
def float16Via32 (f : FV .f32 → Jl (FV .f32)) (a : FV .f16) : Jl (FV .f16) := do
  return Fl.convert (← f (Fl.convert a))

/--
Julia source: base/math.jl:1310-1310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))
```
-/
def complex16Via32 (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let result ← f ⟨Fl.convert a.re, Fl.convert a.im⟩
  return ⟨Fl.convert result.re, Fl.convert result.im⟩

/--
Julia source: base/math.jl:1315-1315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
     @eval $func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))
```
-/
def complex16Via32Second (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let result ← f ⟨Fl.convert a.re, Fl.convert a.im⟩
  return ⟨Fl.convert result.re, Fl.convert result.im⟩

/--
Julia source: base/math.jl:1319-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(a::Float16,b::Float16) = Float16(atan(Float32(a),Float32(b)))
```
-/
def atan16 (atan32 : FV .f32 → FV .f32 → Jl (FV .f32))
    (a b : FV .f16) : Jl (FV .f16) := do
  return Fl.convert (← atan32 (Fl.convert a) (Fl.convert b))

/--
Julia source: base/math.jl:1320-1320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos(a::Float16) = Float16.(sincos(Float32(a)))
```
-/
def sincos16 (sincos32 : FV .f32 → Jl (FV .f32 × FV .f32))
    (a : FV .f16) : Jl (FV .f16 × FV .f16) := do
  let result ← sincos32 (Fl.convert a)
  return (Fl.convert result.1, Fl.convert result.2)

/--
Julia source: base/math.jl:1326-1330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function ($f)(x::Real)
        xf = float(x)
        xf isa typeof(x) && throw(MethodError($f, (x,)))
        return ($f)(xf)
    end
```
-/
def realFallback {α β γ : Type} (float : α → β) (sameType : α → Bool)
    (fName : String) (f : β → Jl γ) (x : α) : Jl γ :=
  if sameType x then .error (.methodError fName) else f (float x)

/--
Julia source: base/math.jl:1331-1331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing) = missing
```
-/
def missingUnary {α : Type} (_x : Option α) : Option α := none

/--
Julia source: base/math.jl:1335-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing, ::Missing) = missing
```
-/
def missingBoth {α β γ : Type} (_x : Option α) (_y : Option β) : Option γ := none

/--
Julia source: base/math.jl:1336-1336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Number, ::Missing) = missing
```
-/
def missingRight {α β γ : Type} (_x : α) (_y : Option β) : Option γ := none

/--
Julia source: base/math.jl:1337-1337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing, ::Number) = missing
```
-/
def missingLeft {α β γ : Type} (_x : Option α) (_y : β) : Option γ := none

/--
Julia source: base/math.jl:1340-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp2(x::AbstractFloat) = 2^x
```
-/
def exp2Float {α : Type} (o : AbstractFloatOps α) (x : α) : α :=
  o.pow (o.ofInt 2) x

/--
Julia source: base/math.jl:1341-1341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp10(x::AbstractFloat) = 10^x
```
-/
def exp10Float {α : Type} (o : AbstractFloatOps α) (x : α) : α :=
  o.pow (o.ofInt 10) x

/--
Julia source: base/math.jl:1342-1342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fourthroot(::Missing) = missing
```
-/
def fourthrootMissing {α : Type} (_x : Option α) : Option α := none


end JuliaLean.base.math
