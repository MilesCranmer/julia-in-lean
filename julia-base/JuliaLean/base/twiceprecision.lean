import JuliaLean.Core
import JuliaLean.base.range
import JuliaLean.base.float

set_option linter.unusedVariables false

namespace JuliaLean.base.twiceprecision

open JuliaLean JuliaLean.base.range

abbrev F64 := JuliaLean.base.float.FV .f64
abbrev IEEEType := JuliaLean.base.float.FTy

structure Arithmetic (T : Type) where
  add : T → T → T
  sub : T → T → T
  mul : T → T → T
  div : T → T → T
  neg : T → T
  abs : T → T
  lt : T → T → Bool
  le : T → T → Bool
  gt : T → T → Bool
  eq : T → T → Bool
  zero : T
  one : T
  iszero : T → Bool
  isfinite : T → Bool
  twoMul : T → T → T × T
  fma : T → T → T → T
  frexp : T → T × Int
  ldexp : T → Int → T
  truncInt : T → JlX Int
  inv : T → T

structure BitOps (F U M N : Type) where
  reinterpretTo : F → U
  reinterpretFrom : U → F
  bitAnd : M → U → U
  typemax : M
  shiftLeft : M → N → M

structure IntegerOps (I : Type) where
  add : I → I → I
  sub : I → I → I
  mul : I → I → I
  div : I → I → I
  rem : I → I → I
  neg : I → I
  abs : I → I
  max : I → I → I
  lt : I → I → Bool
  le : I → I → Bool
  eq : I → I → Bool
  isEven : I → Bool
  shiftRightOne : I → I
  gcd : I → I → I
  zero : I
  one : I

structure RatOps (F I : Type) where
  float : Arithmetic F
  integer : IntegerOps I
  bound : F
  convertBound : F → I
  truncInt : F → JlX I
  ofInt : I → F

structure FloatRangeOps (F I L N R : Type) where
  float : Arithmetic F
  integer : IntegerOps I
  lengthInteger : IntegerOps L
  ofInt : I → F
  ofLength : L → F
  convertInt : I → JlX I
  roundInt : F → JlX L
  rat : F → JlX (I × I)
  lcmUnchecked : I → I → JlX I
  maxintfloat : F
  zeroN : N
  nbitslen : Type → L → L → N
  isbetween : F → F → F → Bool
  hpRatio : I × I → I × I → N → L → L → JlX R
  hpFloat : F → F → N → L → L → JlX R


def ratLoop {F I : Type} : Nat → RatOps F I → F → F → I → I → I → I →
    JlX (I × I)
  | 0, _, _, _, a, b, _, _ => .ok (a, b)
  | fuel + 1, ops, x, y, a, b, c, d => do
    if !ops.float.le (ops.float.abs y) ops.bound then return (a, b)
    let f ← ops.truncInt y
    let y := ops.float.sub y (ops.ofInt f)
    let a' := ops.integer.add (ops.integer.mul f a) c
    let c := a
    let b' := ops.integer.add (ops.integer.mul f b) d
    let d := b
    if !ops.integer.le (ops.integer.max (ops.integer.abs a') (ops.integer.abs b'))
        (ops.convertBound ops.bound) then return (c, d)
    if ops.float.eq (ops.float.div (ops.ofInt a') (ops.ofInt b')) x then return (a', b')
    ratLoop fuel ops x (ops.float.inv y) a' b' c d
/--
Julia source: base/twiceprecision.jl:22-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splitprec(::Type{F}, i::Integer) where {F<:AbstractFloat}
    hi = truncbits(F(i), cld(precision(F), 2))
    ihi = oftype(i, hi)
    hi, F(i - ihi)
end
```

-/
def splitprec {F I U M N : Type} (bits : BitOps F U M N) (truncbits : F → Nat → F)
    (precision : Nat) (ceilDiv : Nat → Nat → Nat) (ofFloat : I → F)
    (oftype : I → F → JlX I) (subInt : I → I → I) (i : I) : JlX (F × F) := do
  let hi := truncbits (ofFloat i) (ceilDiv precision 2)
  let ihi ← oftype i hi
  pure (hi, ofFloat (subInt i ihi))

/--
Julia source: base/twiceprecision.jl:28-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncmask(x::F, mask) where {F<:IEEEFloat}
    reinterpret(F, mask & reinterpret(uinttype(F), x))
end
```

-/
def truncmaskIEEE {F U M N : Type} (bits : BitOps F U M N) (x : F) (mask : M) : F :=
  bits.reinterpretFrom (bits.bitAnd mask (bits.reinterpretTo x))

/--
Julia source: base/twiceprecision.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
truncmask(x, mask) = x
```

-/
def truncmaskGeneric {T M : Type} (x : T) (_mask : M) : T := x

/--
Julia source: base/twiceprecision.jl:33-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncbits(x::F, nb) where {F<:IEEEFloat}
    truncmask(x, typemax(uinttype(F)) << nb)
end
```

-/
def truncbitsIEEE {F U M N : Type} (bits : BitOps F U M N) (x : F) (nb : N) : F :=
  truncmaskIEEE bits x (bits.shiftLeft bits.typemax nb)

/--
Julia source: base/twiceprecision.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
truncbits(x, nb) = x
```

-/
def truncbitsGeneric {T N : Type} (x : T) (_nb : N) : T := x

/--
Julia source: base/twiceprecision.jl:48-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function canonicalize2(big, little)
    h = big+little
    h, (big - h) + little
end
```

-/
def canonicalize2 {T : Type} (add sub : T → T → T) (big little : T) : T × T :=
  let h := add big little
  (h, add (sub big h) little)

/--
Julia source: base/twiceprecision.jl:83-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add12(x::T, y::T) where {T}
    x, y = ifelse(abs(y) > abs(x), (y, x), (x, y))
    canonicalize2(x, y)
end
```

-/
def add12Same {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x y : T) : T × T :=
  let (x, y) := ifelse (ops.gt (ops.abs y) (ops.abs x)) (y, x) (x, y)
  canonicalize2 ops.add ops.sub x y

/--
Julia source: base/twiceprecision.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add12(x, y) = add12(promote(x, y)...)
```

-/
def add12Mixed {X Y T : Type} (promote : X → Y → T × T) (ops : Arithmetic T)
    (ifelse : {A : Type} → Bool → A → A → A) (x : X) (y : Y) : T × T :=
  let (x, y) := promote x y
  add12Same ops ifelse x y

/--
Julia source: base/twiceprecision.jl:114-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mul12(x::T, y::T) where {T<:AbstractFloat}
    (h, l) = two_mul(x, y)
    ifelse(!isfinite(h), (h, h), (h, l))
end
```

-/
def mul12IEEE {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x y : T) : T × T :=
  let (h, l) := ops.twoMul x y
  ifelse (!ops.isfinite h) (h, h) (h, l)

/--
Julia source: base/twiceprecision.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul12(x::T, y::T) where {T} = (p = x * y; (p, zero(p)))
```

-/
def mul12Generic {T : Type} (ops : Arithmetic T) (x y : T) : T × T :=
  let p := ops.mul x y
  (p, ops.zero)

/--
Julia source: base/twiceprecision.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul12(x, y) = mul12(promote(x, y)...)
```

-/
def mul12Mixed {X Y T : Type} (promote : X → Y → T × T) (mul12 : T → T → T × T)
    (x : X) (y : Y) : T × T :=
  let (x, y) := promote x y
  mul12 x y

/--
Julia source: base/twiceprecision.jl:146-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div12(x::T, y::T) where {T<:AbstractFloat}
    # We lose precision if any intermediate calculation results in a subnormal.
    # To prevent this from happening, standardize the values.
    xs, xe = frexp(x)
    ys, ye = frexp(y)
    r = xs / ys
    rh, rl = canonicalize2(r, -fma(r, ys, -xs)/ys)
    ifelse(iszero(r) | !isfinite(r), (r, r), (ldexp(rh, xe-ye), ldexp(rl, xe-ye)))
end
```

-/
def div12IEEE {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x y : T) : T × T :=
  let (xs, xe) := ops.frexp x
  let (ys, ye) := ops.frexp y
  let r := ops.div xs ys
  let (rh, rl) := canonicalize2 ops.add ops.sub r
    (ops.div (ops.neg (ops.fma r ys (ops.neg xs))) ys)
  ifelse (ops.iszero r || !ops.isfinite r) (r, r)
    (ops.ldexp rh (xe - ye), ops.ldexp rl (xe - ye))

/--
Julia source: base/twiceprecision.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div12(x::T, y::T) where {T} = (p = x / y; (p, zero(p)))
```

-/
def div12Generic {T : Type} (ops : Arithmetic T) (x y : T) : T × T :=
  let p := ops.div x y
  (p, ops.zero)

/--
Julia source: base/twiceprecision.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div12(x, y) = div12(promote(x, y)...)
```

-/
def div12Mixed {X Y T : Type} (promote : X → Y → T × T) (div12 : T → T → T × T)
    (x : X) (y : Y) : T × T :=
  let (x, y) := promote x y
  div12 x y

/--
Julia source: base/twiceprecision.jl:196-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TwicePrecision{T}
    hi::T    # most significant bits
    lo::T    # least significant bits
end
```

-/
structure TwicePrecision (T : Type) where
  hi : T
  lo : T
  deriving DecidableEq, Repr

/--
Julia source: base/twiceprecision.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TwicePrecision{T}(x::T) where {T} = TwicePrecision{T}(x, zero(T))
```

-/
def tpFromSame {T : Type} (ops : Arithmetic T) (x : T) : TwicePrecision T :=
  ⟨x, ops.zero⟩

/--
Julia source: base/twiceprecision.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TwicePrecision{T}(x::TwicePrecision{T}) where {T} = x
```

-/
def tpIdentity {T : Type} (x : TwicePrecision T) : TwicePrecision T := x

/--
Julia source: base/twiceprecision.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TwicePrecision{T}(x) where {T}
    xT = T(x)
    Δx = x - xT
    TwicePrecision{T}(xT, T(Δx))
end
```

-/
def tpFromValue {T X D : Type} (convert : X → JlX T) (sub : X → T → D)
    (convertDelta : D → JlX T) (x : X) : JlX (TwicePrecision T) := do
  let xT ← convert x
  let Δx := sub x xT
  pure ⟨xT, ← convertDelta Δx⟩

/--
Julia source: base/twiceprecision.jl:211-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TwicePrecision{T}(i::Integer) where {T<:AbstractFloat} =
    TwicePrecision{T}(canonicalize2(splitprec(T, i)...)...)
```

-/
def tpFromInteger {T I U M N : Type} (bits : BitOps T U M N)
    (truncbits : T → Nat → T) (precision : Nat) (ceilDiv : Nat → Nat → Nat)
    (ofFloat : I → T) (oftype : I → T → JlX I) (subInt : I → I → I)
    (ops : Arithmetic T) (i : I) : JlX (TwicePrecision T) := do
  let (hi, lo) ← splitprec bits truncbits precision ceilDiv ofFloat oftype subInt i
  let (h, l) := canonicalize2 ops.add ops.sub hi lo
  pure ⟨h, l⟩

/--
Julia source: base/twiceprecision.jl:214-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TwicePrecision(x) = TwicePrecision{typeof(x)}(x)
```

-/
def tpOuter {X : Type} (typeOf : X → Type)
    (construct : (x : X) → TwicePrecision (typeOf x)) (x : X) : TwicePrecision (typeOf x) :=
  construct x

/--
Julia source: base/twiceprecision.jl:217-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TwicePrecision{T}(nd::Tuple{Integer,Integer}) where {T<:Union{Float16,Float32}}
    n, d = nd
    TwicePrecision{T}(n/d)
end
```

-/
def tpRatioSmall {T I : Type} (div : I → I → T) (construct : T → JlX (TwicePrecision T))
    (nd : I × I) : JlX (TwicePrecision T) :=
  let (n, d) := nd
  construct (div n d)

/--
Julia source: base/twiceprecision.jl:222-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TwicePrecision{T}(nd::Tuple{Any,Any}) where {T}
    n, d = nd
    TwicePrecision{T}(TwicePrecision{T}(n) / d)
end
```

-/
def tpRatio {T N D : Type} (construct : N → JlX (TwicePrecision T))
    (divide : TwicePrecision T → D → JlX (TwicePrecision T)) (nd : N × D) :
    JlX (TwicePrecision T) := do
  let (n, d) := nd
  divide (← construct n) d

/--
Julia source: base/twiceprecision.jl:227-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TwicePrecision{T}(nd::Tuple{I,I}, nb::Integer) where {T,I}
    twiceprecision(TwicePrecision{T}(nd), nb)
end
```

-/
def tpRatioBits {T N I : Type} (ratio : N → JlX (TwicePrecision T))
    (truncate : TwicePrecision T → I → JlX (TwicePrecision T)) (nd : N) (nb : I) :
    JlX (TwicePrecision T) := do
  truncate (← ratio nd) nb

/--
Julia source: base/twiceprecision.jl:235-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TwicePrecision{T}(nd::Tuple{Integer,Integer}, nb::Integer) where T
    twiceprecision(TwicePrecision{T}(nd), nb)
end
```

-/
def tpIntegerRatioBits {T N I : Type} (ratio : N → JlX (TwicePrecision T))
    (truncate : TwicePrecision T → I → JlX (TwicePrecision T)) (nd : N) (nb : I) :
    JlX (TwicePrecision T) := do
  truncate (← ratio nd) nb

/--
Julia source: base/twiceprecision.jl:241-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function twiceprecision(val::T, nb::Integer) where {T<:IEEEFloat}
    hi = truncbits(val, nb)
    TwicePrecision{T}(hi, val - hi)
end
```

-/
def twiceprecisionIEEE {T U M N : Type} (bits : BitOps T U M N) (ops : Arithmetic T)
    (val : T) (nb : N) : TwicePrecision T :=
  let hi := truncbitsIEEE bits val nb
  ⟨hi, ops.sub val hi⟩

/--
Julia source: base/twiceprecision.jl:246-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function twiceprecision(val::TwicePrecision{T}, nb::Integer) where {T<:IEEEFloat}
    hi = truncbits(val.hi, nb)
    TwicePrecision{T}(hi, (val.hi - hi) + val.lo)
end
```

-/
def twiceprecisionTP {T U M N : Type} (bits : BitOps T U M N) (ops : Arithmetic T)
    (val : TwicePrecision T) (nb : N) : TwicePrecision T :=
  let hi := truncbitsIEEE bits val.hi nb
  ⟨hi, ops.add (ops.sub val.hi hi) val.lo⟩

/--
Julia source: base/twiceprecision.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nbitslen(r::StepRangeLen) = nbitslen(eltype(r), length(r), r.offset)
```

-/
def nbitslenRange {T R S L N : Type} (eltype : Type) (length : StepRangeLen T R S L → L)
    (nbitslen : Type → L → L → N) (r : StepRangeLen T R S L) : N :=
  nbitslen eltype (length r) r.offset

/--
Julia source: base/twiceprecision.jl:252-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nbitslen(::Type{T}, len, offset) where {T<:IEEEFloat} =
    min(cld(precision(T), 2), nbitslen(len, offset))
```

-/
def nbitslenIEEE {I N : Type} (nbitslenGeneric : I → I → N)
    (precision twoN : N) (cld min : N → N → N) (len offset : I) : N :=
  min (cld precision twoN) (nbitslenGeneric len offset)

/--
Julia source: base/twiceprecision.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nbitslen(len, offset) = len < 2 ? 0 : top_set_bit(max(offset-1, len-offset) - 1) + 1
```

-/
def nbitslenGeneric {I N : Type} (lt : I → I → Bool) (sub max : I → I → I)
    (topSetBit : I → N) (add : N → N → N) (twoI oneI : I) (oneN zeroN : N)
    (len offset : I) : N :=
  if lt len twoI then zeroN
  else add (topSetBit (sub (max (sub offset oneI) (sub len offset)) oneI)) oneN

/--
Julia source: base/twiceprecision.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{TwicePrecision{T}}) where {T} = T
```

-/
def eltypeTwicePrecision (T : Type) : Type := T

/--
Julia source: base/twiceprecision.jl:260-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{TwicePrecision{R}}, ::Type{TwicePrecision{S}}) where {R,S} =
    TwicePrecision{promote_type(R,S)}
```

-/
def promoteRuleTwicePrecision {R S : Type} (promoteType : Type → Type → Type) : Type :=
  TwicePrecision (promoteType R S)

/--
Julia source: base/twiceprecision.jl:262-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{TwicePrecision{R}}, ::Type{S}) where {R,S<:Number} =
    TwicePrecision{promote_type(R,S)}
```

-/
def promoteRuleTwicePrecisionNumber {R S : Type} (promoteType : Type → Type → Type) : Type :=
  TwicePrecision (promoteType R S)

/--
Julia source: base/twiceprecision.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::TwicePrecision) where {T<:Number} = (T(x.hi) + T(x.lo))::T
```

-/
def tpToNumber {T U : Type} (convert : T → JlX U) (add : U → U → JlX U)
    (x : TwicePrecision T) : JlX U := do
  add (← convert x.hi) (← convert x.lo)

/--
Julia source: base/twiceprecision.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{TwicePrecision{T}}, x::TwicePrecision{T}) where {T} = x
```

-/
def tpConvertIdentity {T : Type} (x : TwicePrecision T) : TwicePrecision T := x

/--
Julia source: base/twiceprecision.jl:268-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{TwicePrecision{T}}, x::TwicePrecision) where {T} =
    TwicePrecision{T}(convert(T, x.hi), convert(T, x.lo))::TwicePrecision{T}
```

-/
def tpConvertParts {T U : Type} (convert : T → JlX U) (x : TwicePrecision T) :
    JlX (TwicePrecision U) := do
  pure ⟨← convert x.hi, ← convert x.lo⟩

/--
Julia source: base/twiceprecision.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::TwicePrecision) where {T<:Number} = T(x)::T
```

-/
def convertTpToNumber {T U : Type} (convert : TwicePrecision T → JlX U)
    (x : TwicePrecision T) : JlX U := convert x

/--
Julia source: base/twiceprecision.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{TwicePrecision{T}}, x::Number) where {T} = TwicePrecision{T}(x)::TwicePrecision{T}
```

-/
def convertNumberToTp {T N : Type} (construct : N → JlX (TwicePrecision T))
    (x : N) : JlX (TwicePrecision T) := construct x

/--
Julia source: base/twiceprecision.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(x::TwicePrecision{<:AbstractFloat}) = x
```

-/
def floatTpAbstractFloat {T : Type} (x : TwicePrecision T) : TwicePrecision T := x

/--
Julia source: base/twiceprecision.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(x::TwicePrecision) = TwicePrecision(float(x.hi), float(x.lo))
```

-/
def floatTp {T U : Type} (float : T → U) (x : TwicePrecision T) : TwicePrecision U :=
  ⟨float x.hi, float x.lo⟩

/--
Julia source: base/twiceprecision.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(x::TwicePrecision) = big(x.hi) + big(x.lo)
```

-/
def bigTp {T B : Type} (big : T → B) (add : B → B → B) (x : TwicePrecision T) : B :=
  add (big x.hi) (big x.lo)

/--
Julia source: base/twiceprecision.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::TwicePrecision) = TwicePrecision(-x.hi, -x.lo)
```

-/
def negTp {T : Type} (ops : Arithmetic T) (x : TwicePrecision T) : TwicePrecision T :=
  ⟨ops.neg x.hi, ops.neg x.lo⟩

/--
Julia source: base/twiceprecision.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::TwicePrecision) = zero(typeof(x))
```

-/
def zeroTpValue {T : Type} (zeroType : Type → TwicePrecision T) (_x : TwicePrecision T) :
    TwicePrecision T := zeroType T

/--
Julia source: base/twiceprecision.jl:282-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function zero(::Type{TwicePrecision{T}}) where {T}
    z = zero(T)
    TwicePrecision{T}(z, z)
end
```

-/
def zeroTpType {T : Type} (ops : Arithmetic T) : TwicePrecision T :=
  let z := ops.zero
  ⟨z, z⟩

/--
Julia source: base/twiceprecision.jl:289-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(x::TwicePrecision, y::Number)
    s_hi, s_lo = add12(x.hi, y)
    TwicePrecision(canonicalize2(s_hi, s_lo+x.lo)...)
end
```

-/
def addTpNumber {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x : TwicePrecision T) (y : T) : TwicePrecision T :=
  let (s_hi, s_lo) := add12Same ops ifelse x.hi y
  let (h, l) := canonicalize2 ops.add ops.sub s_hi (ops.add s_lo x.lo)
  ⟨h, l⟩

/--
Julia source: base/twiceprecision.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Number, y::TwicePrecision) = y+x
```

-/
def addNumberTp {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x : T) (y : TwicePrecision T) : TwicePrecision T := addTpNumber ops ifelse y x

/--
Julia source: base/twiceprecision.jl:295-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(x::TwicePrecision{T}, y::TwicePrecision{T}) where T
    r = x.hi + y.hi
    s = abs(x.hi) > abs(y.hi) ? (((x.hi - r) + y.hi) + y.lo) + x.lo : (((y.hi - r) + x.hi) + x.lo) + y.lo
    TwicePrecision(canonicalize2(r, s)...)
end
```

-/
def addTpSame {T : Type} (ops : Arithmetic T) (x y : TwicePrecision T) : TwicePrecision T :=
  let r := ops.add x.hi y.hi
  let s := if ops.gt (ops.abs x.hi) (ops.abs y.hi)
    then ops.add (ops.add (ops.add (ops.sub x.hi r) y.hi) y.lo) x.lo
    else ops.add (ops.add (ops.add (ops.sub y.hi r) x.hi) x.lo) y.lo
  let (h, l) := canonicalize2 ops.add ops.sub r s
  ⟨h, l⟩

/--
Julia source: base/twiceprecision.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::TwicePrecision, y::TwicePrecision) = +(promote(x, y)...)
```

-/
def addTpPromoted {R S T : Type} (promote : TwicePrecision R → TwicePrecision S →
    TwicePrecision T × TwicePrecision T) (ops : Arithmetic T)
    (x : TwicePrecision R) (y : TwicePrecision S) : TwicePrecision T :=
  let (x, y) := promote x y
  addTpSame ops x y

/--
Julia source: base/twiceprecision.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::TwicePrecision, y::TwicePrecision) = x + (-y)
```

-/
def subTpSame {T : Type} (ops : Arithmetic T) (x y : TwicePrecision T) : TwicePrecision T :=
  addTpSame ops x (negTp ops y)

/--
Julia source: base/twiceprecision.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::TwicePrecision, y::Number) = x + (-y)
```

-/
def subTpNumber {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x : TwicePrecision T) (y : T) : TwicePrecision T :=
  addTpNumber ops ifelse x (ops.neg y)

/--
Julia source: base/twiceprecision.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Number, y::TwicePrecision) = x + (-y)
```

-/
def subNumberTp {T : Type} (ops : Arithmetic T) (ifelse : {A : Type} → Bool → A → A → A)
    (x : T) (y : TwicePrecision T) : TwicePrecision T :=
  addNumberTp ops ifelse x (negTp ops y)

/--
Julia source: base/twiceprecision.jl:306-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::TwicePrecision, v::Number)
    v == 0 && return TwicePrecision(x.hi*v, x.lo*v)
    x * TwicePrecision(oftype(x.hi*v, v))
end
```

-/
def mulTpNumber {T N : Type} (ops : Arithmetic T) (mulValue : T → N → T)
    (construct : T → N → JlX (TwicePrecision T)) (mulTp : TwicePrecision T →
    TwicePrecision T → JlX (TwicePrecision T)) (x : TwicePrecision T) (v : N)
    (vIsZero : N → Bool) (zeroMul : T → N → T) : JlX (TwicePrecision T) := do
  if vIsZero v then return ⟨zeroMul x.hi v, zeroMul x.lo v⟩
  mulTp x (← construct (mulValue x.hi v) v)

/--
Julia source: base/twiceprecision.jl:310-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::TwicePrecision{<:IEEEFloat}, v::Integer)
    v == 0 && return TwicePrecision(x.hi*v, x.lo*v)
    nb = top_set_bit(abs(v)-1)
    u = truncbits(x.hi, nb)
    TwicePrecision(canonicalize2(u*v, ((x.hi-u) + x.lo)*v)...)
end
```

-/
def mulTpInteger {T I U M N : Type} (bits : BitOps T U M N) (ops : Arithmetic T)
    (integer : IntegerOps I) (topSetBit : I → N) (float : I → T) (x : TwicePrecision T)
    (v : I) (vIsZero : I → Bool) (zeroMul : T → I → T) : TwicePrecision T :=
  if vIsZero v then ⟨zeroMul x.hi v, zeroMul x.lo v⟩
  else
    let nb := topSetBit (integer.sub (integer.abs v) integer.one)
    let u := truncbitsIEEE bits x.hi nb
    let (h, l) := canonicalize2 ops.add ops.sub (ops.mul u (float v))
      (ops.mul (ops.add (ops.sub x.hi u) x.lo) (float v))
    ⟨h, l⟩

/--
Julia source: base/twiceprecision.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(v::Number, x::TwicePrecision) = x*v
```

-/
def mulNumberTp {T N : Type} (mul : N → TwicePrecision T → JlX (TwicePrecision T))
    (v : N) (x : TwicePrecision T) : JlX (TwicePrecision T) := mul v x

/--
Julia source: base/twiceprecision.jl:318-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::TwicePrecision{T}, y::TwicePrecision{T}) where {T}
    zh, zl = mul12(x.hi, y.hi)
    ret = TwicePrecision{T}(canonicalize2(zh, (x.hi * y.lo + x.lo * y.hi) + zl)...)
    ifelse(iszero(zh) | !isfinite(zh), TwicePrecision{T}(zh, zh), ret)
end
```

-/
def mulTpSame {T : Type} (ops : Arithmetic T) (mul12 : T → T → T × T)
    (ifelse : {A : Type} → Bool → A → A → A) (x y : TwicePrecision T) :
    TwicePrecision T :=
  let (zh, zl) := mul12 x.hi y.hi
  let (h, l) := canonicalize2 ops.add ops.sub zh
    (ops.add (ops.add (ops.mul x.hi y.lo) (ops.mul x.lo y.hi)) zl)
  let ret : TwicePrecision T := ⟨h, l⟩
  ifelse (ops.iszero zh || !ops.isfinite zh) ⟨zh, zh⟩ ret

/--
Julia source: base/twiceprecision.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::TwicePrecision, y::TwicePrecision) = *(promote(x, y)...)
```

-/
def mulTpPromoted {R S T : Type} (promote : TwicePrecision R → TwicePrecision S →
    TwicePrecision T × TwicePrecision T) (ops : Arithmetic T) (mul12 : T → T → T × T)
    (ifelse : {A : Type} → Bool → A → A → A) (x : TwicePrecision R) (y : TwicePrecision S) :
    TwicePrecision T :=
  let (x, y) := promote x y
  mulTpSame ops mul12 ifelse x y

/--
Julia source: base/twiceprecision.jl:325-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function /(x::TwicePrecision, v::Number)
    x / TwicePrecision(oftype(x.hi/v, v))
end
```

-/
def divTpNumber {T N : Type} (divValue : T → N → T)
    (construct : T → N → JlX (TwicePrecision T)) (divTp : TwicePrecision T →
    TwicePrecision T → JlX (TwicePrecision T)) (x : TwicePrecision T) (v : N) :
    JlX (TwicePrecision T) := do
  let y ← construct (divValue x.hi v) v
  divTp x y

/--
Julia source: base/twiceprecision.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function /(x::TwicePrecision, y::TwicePrecision)
    hi = x.hi / y.hi
    uh, ul = mul12(hi, y.hi)
    lo = ((((x.hi - uh) - ul) + x.lo) - hi*y.lo)/y.hi
    ret = TwicePrecision(canonicalize2(hi, lo)...)
    ifelse(iszero(hi) | !isfinite(hi), TwicePrecision(hi, hi), ret)
end
```

-/
def divTpSame {T : Type} (ops : Arithmetic T) (mul12 : T → T → T × T)
    (ifelse : {A : Type} → Bool → A → A → A) (x y : TwicePrecision T) :
    TwicePrecision T :=
  let hi := ops.div x.hi y.hi
  let (uh, ul) := mul12 hi y.hi
  let lo := ops.div (ops.sub (ops.add (ops.sub (ops.sub x.hi uh) ul) x.lo)
    (ops.mul hi y.lo)) y.hi
  let (h, l) := canonicalize2 ops.add ops.sub hi lo
  ifelse (ops.iszero hi || !ops.isfinite hi) ⟨hi, hi⟩ ⟨h, l⟩

/--
Julia source: base/twiceprecision.jl:342-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprangelen_hp(::Type{Float64}, ref::Tuple{Integer,Integer},
                         step::Tuple{Integer,Integer}, nb::Integer,
                         len::Integer, offset::Integer)
    StepRangeLen(TwicePrecision{Float64}(ref),
                 TwicePrecision{Float64}(step, nb), len, offset)
end
```

-/
def steprangelenHpF64 {I L R : Type} (ratio : I × I → JlX (TwicePrecision F64))
    (ratioBits : I × I → L → JlX (TwicePrecision F64))
    (make : TwicePrecision F64 → TwicePrecision F64 → L → L → JlX R)
    (ref step : I × I) (nb len offset : L) : JlX R := do
  make (← ratio ref) (← ratioBits step nb) len offset

/--
Julia source: base/twiceprecision.jl:349-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprangelen_hp(::Type{T}, ref::Tuple{Integer,Integer},
                         step::Tuple{Integer,Integer}, nb::Integer,
                         len::Integer, offset::Integer) where {T<:IEEEFloat}
    StepRangeLen{T}(ref[1]/ref[2], step[1]/step[2], len, offset)
end
```

-/
def steprangelenHpRatioIEEE {T I L R : Type} (div : I → I → T)
    (make : T → T → L → L → JlX R) (ref step : I × I) (_nb : L) (len offset : L) :
    JlX R := do
  let refValue := div ref.1 ref.2
  let stepValue := div step.1 step.2
  make refValue stepValue len offset

/--
Julia source: base/twiceprecision.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
asF64(x::AbstractFloat) = Float64(x)
```

-/
def asF64Scalar {F : Type} (convert : F → F64) (x : F) : F64 := convert x

/--
Julia source: base/twiceprecision.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
asF64(x::Tuple{AbstractFloat,AbstractFloat}) = Float64(x[1]) + Float64(x[2])
```

-/
def asF64Pair {F : Type} (convert : F → F64) (x : F × F) : F64 :=
  let (a, b) := x
  JuliaLean.base.float.add_IEEEFloat (convert a) (convert b)

/--
Julia source: base/twiceprecision.jl:360-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprangelen_hp(::Type{Float64}, ref::F_or_FF,
                         step::F_or_FF, nb::Integer,
                         len::Integer, offset::Integer)
    StepRangeLen(TwicePrecision{Float64}(ref...),
                 twiceprecision(TwicePrecision{Float64}(step...), nb), len, offset)
end
```

-/
def steprangelenHpFloat64 {I L : Type} (asParts : F64 ⊕ (F64 × F64) → TwicePrecision F64)
    (truncate : TwicePrecision F64 → I → TwicePrecision F64)
    (make : TwicePrecision F64 → TwicePrecision F64 → L → L → JlX (StepRangeLen F64
      (TwicePrecision F64) (TwicePrecision F64) L))
    (ref step : F64 ⊕ (F64 × F64)) (nb : I) (len offset : L) :
    JlX (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) L) := do
  make (asParts ref) (truncate (asParts step) nb) len offset

/--
Julia source: base/twiceprecision.jl:367-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprangelen_hp(::Type{T}, ref::F_or_FF,
                         step::F_or_FF, nb::Integer,
                         len::Integer, offset::Integer) where {T<:IEEEFloat}
    StepRangeLen{T}(asF64(ref), asF64(step), len, offset)
end
```

-/
def steprangelenHpFloatIEEE {F I L R : Type} (asF64 : F ⊕ (F × F) → F64)
    (make : F64 → F64 → L → L → JlX R) (ref step : F ⊕ (F × F)) (_nb : I)
    (len offset : L) : JlX R := do
  let refValue := asF64 ref
  let stepValue := asF64 step
  make refValue stepValue len offset

/--
Julia source: base/twiceprecision.jl:375-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen(ref::TwicePrecision{T}, step::TwicePrecision{T},
             len::Integer, offset::Integer=1) where {T} =
    StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}}(ref, step, len, offset)
```

-/
def stepRangeLenFromTwicePrecision {T L : Type}
    (make : TwicePrecision T → TwicePrecision T → L → L → JlX
      (StepRangeLen T (TwicePrecision T) (TwicePrecision T) L))
    (ref step : TwicePrecision T) (len offset : L) :
    JlX (StepRangeLen T (TwicePrecision T) (TwicePrecision T) L) :=
  make ref step len offset

/--
Julia source: base/twiceprecision.jl:380-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function floatrange(::Type{T}, start_n::Integer, step_n::Integer, len::Integer, den::Integer) where T
    len = len + 0 # promote with Int
    if len < 2 || step_n == 0
        return steprangelen_hp(T, (start_n, den), (step_n, den), 0, len, oneunit(len))
    end
    # index of smallest-magnitude value
    L = typeof(len)
    imin = clamp(round(typeof(len), -start_n/step_n+1), oneunit(L), len)
    # Compute smallest-magnitude element to 2x precision
    ref_n = start_n+(imin-1)*step_n  # this shouldn't overflow, so don't check
    nb = nbitslen(T, len, imin)
    steprangelen_hp(T, (ref_n, den), (step_n, den), nb, len, imin)
end
```

-/
def floatrange {F I LI L N R : Type} (ops : FloatRangeOps F I L N R) (type : Type)
    (lenPlusZero : LI → L) (round : F → JlX L) (clamp : L → L → L → L)
    (floatInt : I → F) (offsetToInt : L → I) (one : L)
    (startN stepN : I) (lenInput : LI) (den : I) : JlX R := do
  let len := lenPlusZero lenInput
  if ops.lengthInteger.lt len (ops.lengthInteger.add one one) ||
      ops.integer.eq stepN ops.integer.zero then
    return ← ops.hpRatio (startN, den) (stepN, den) ops.zeroN len one
  let q := ops.float.add
    (ops.float.div (ops.float.neg (floatInt startN)) (floatInt stepN)) ops.float.one
  let imin0 ← round q
  let imin := clamp imin0 one len
  let refN := ops.integer.add startN
    (ops.integer.mul (offsetToInt (ops.lengthInteger.sub imin one)) stepN)
  ops.hpRatio (refN, den) (stepN, den) (ops.nbitslen type len imin) len imin

/--
Julia source: base/twiceprecision.jl:394-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (:)(start::T, step::T, stop::T) where T<:IEEEFloat
    step == 0 && throw(ArgumentError("range step cannot be zero"))
    # see if the inputs have exact rational approximations (and if so,
    # perform all computations in terms of the rationals)
    step_n, step_d = rat(step)
    if step_d != 0 && T(step_n/step_d) == step
        start_n, start_d = rat(start)
        stop_n, stop_d = rat(stop)
        if start_d != 0 && stop_d != 0 &&
                T(start_n/start_d) == start && T(stop_n/stop_d) == stop
            den = lcm_unchecked(start_d, step_d) # use same denominator for start and step
            m = maxintfloat(T, Int)
            if den != 0 && abs(start*den) <= m && abs(step*den) <= m &&  # will round succeed?
                    rem(den, start_d) == 0 && rem(den, step_d) == 0      # check lcm overflow
                # scale the rationals exactly: start*den can round to a different
                # integer when T has little precision (e.g. Float16)
                start_n *= div(den, start_d)
                step_n *= div(den, step_d)
                len = max(0, Int(div(den*stop_n - stop_d*start_n + step_n*stop_d, step_n*stop_d)))
                # Integer ops could overflow, so check that this makes sense
                if isbetween(start, start + (len-1)*step, stop + step/2) &&
                        !isbetween(start, start + len*step, stop)
                    # Return a 2x precision range
                    return floatrange(T, start_n, step_n, len, den)
                end
            end
        end
    end
    # Fallback, taking start and step literally
    # n.b. we use Int as the default length type for IEEEFloats
    lf = (stop-start)/step
    if lf < 0
        len = 0
    elseif lf == 0
        len = 1
    else
        len = round(Int, lf) + 1
        stop′ = start + (len-1)*step
        # if we've overshot the end, subtract one:
        len -= (start < stop < stop′) + (start > stop > stop′)
    end
    steprangelen_hp(T, start, step, 0, len, 1)
end
```

-/
def colon {F I N R : Type} (ops : FloatRangeOps F I I N R) (type : Type)
    (lenPlusZero : I → I) (round : F → JlX I) (clampInt : I → I → I → I)
    (float : I → F) (one : I) (start step stop : F) : JlX R := do
  if ops.float.eq step ops.float.zero then throw (.jl (.argumentError "range step cannot be zero"))
  let (stepN, stepD) ← ops.rat step
  if !ops.integer.eq stepD ops.integer.zero &&
      ops.float.eq (ops.float.div (ops.ofInt stepN) (ops.ofInt stepD)) step then
    let (startN, startD) ← ops.rat start
    let (stopN, stopD) ← ops.rat stop
    if !ops.integer.eq startD ops.integer.zero && !ops.integer.eq stopD ops.integer.zero &&
        ops.float.eq (ops.float.div (ops.ofInt startN) (ops.ofInt startD)) start &&
        ops.float.eq (ops.float.div (ops.ofInt stopN) (ops.ofInt stopD)) stop then
      let den ← ops.lcmUnchecked startD stepD
      let m := ops.maxintfloat
      if !ops.integer.eq den ops.integer.zero &&
          ops.float.le (ops.float.abs (ops.float.mul start (ops.ofInt den))) m &&
          ops.float.le (ops.float.abs (ops.float.mul step (ops.ofInt den))) m &&
          ops.integer.eq (ops.integer.rem den startD) ops.integer.zero &&
          ops.integer.eq (ops.integer.rem den stepD) ops.integer.zero then
        let startN := ops.integer.mul startN (ops.integer.div den startD)
        let stepN := ops.integer.mul stepN (ops.integer.div den stepD)
        let numer := ops.integer.add
          (ops.integer.sub (ops.integer.mul den stopN) (ops.integer.mul stopD startN))
          (ops.integer.mul stepN stopD)
        let denom := ops.integer.mul stepN stopD
        let len := ops.integer.max ops.integer.zero (← ops.convertInt
          (ops.integer.div numer denom))
        if ops.isbetween start
            (ops.float.add start (ops.float.mul (ops.ofInt (ops.integer.sub len ops.integer.one)) step))
            (ops.float.add stop (ops.float.div step (ops.float.add ops.float.one ops.float.one))) &&
            !ops.isbetween start
              (ops.float.add start (ops.float.mul (ops.ofInt len) step)) stop then
          return ← floatrange ops type (fun n => n) round clampInt ops.ofInt (fun n => n)
            ops.integer.one startN stepN len den
  let lf := ops.float.div (ops.float.sub stop start) step
  let len ←
    if ops.float.lt lf ops.float.zero then pure ops.integer.zero
    else if ops.float.eq lf ops.float.zero then pure ops.integer.one
    else do
      let r ← round lf
      let len := ops.integer.add r ops.integer.one
      let stopPrime := ops.float.add start
        (ops.float.mul (ops.ofInt (ops.integer.sub len ops.integer.one)) step)
      let over := ops.integer.add
        (if ops.float.lt start stop && ops.float.lt stop stopPrime then ops.integer.one
          else ops.integer.zero)
        (if ops.float.lt stop start && ops.float.lt stopPrime stop then ops.integer.one
          else ops.integer.zero)
      pure (ops.integer.sub len over)
  ops.hpFloat start step ops.zeroN len ops.integer.one

/--
Julia source: base/twiceprecision.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}}) where {T<:AbstractFloat} = T(r.step)
```

-/
def stepTpFloat {T R S L : Type} (convert : S → JlX T) (r : StepRangeLen T R S L) : JlX T :=
  convert r.step

/--
Julia source: base/twiceprecision.jl:439-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}}) where {T} = T(r.step)
```

-/
def stepTpGeneric {T R S L : Type} (convert : S → JlX T) (r : StepRangeLen T R S L) : JlX T :=
  convert r.step

/--
Julia source: base/twiceprecision.jl:441-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_step_length(a::Real, st::IEEEFloat, len::Integer) =
    range_start_step_length(promote(a, st)..., len)
```

-/
def rangeStartStepLengthRealFloat {F A I R : Type}
    (promote : A → F → F × F) (rangeStartStepLength : F → F → I → JlX R)
    (a : A) (st : F) (len : I) : JlX R :=
  let (a, st) := promote a st
  rangeStartStepLength a st len

/--
Julia source: base/twiceprecision.jl:444-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_step_length(a::IEEEFloat, st::Real, len::Integer) =
    range_start_step_length(promote(a, st)..., len)
```

-/
def rangeStartStepLengthFloatReal {F A I R : Type}
    (promote : F → A → F × F) (rangeStartStepLength : F → F → I → JlX R)
    (a : F) (st : A) (len : I) : JlX R :=
  let (a, st) := promote a st
  rangeStartStepLength a st len

/--
Julia source: base/twiceprecision.jl:447-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_step_length(a::IEEEFloat, st::IEEEFloat, len::Integer) =
    range_start_step_length(promote(a, st)..., len)
```

-/
def rangeStartStepLengthFloatFloat {F G I R : Type}
    (promote : F → F → G × G) (rangeStartStepLength : G → G → I → JlX R)
    (a st : F) (len : I) : JlX R :=
  let (a, st) := promote a st
  rangeStartStepLength a st len

/--
Julia source: base/twiceprecision.jl:450-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function range_start_step_length(a::T, st::T, len::Integer) where T<:IEEEFloat
    len = len + 0 # promote with Int
    start_n, start_d = rat(a)
    step_n, step_d = rat(st)
    if start_d != 0 && step_d != 0 &&
            T(start_n/start_d) == a && T(step_n/step_d) == st
        den = lcm_unchecked(start_d, step_d)
        m = maxintfloat(T, Int)
        if abs(den*a) <= m && abs(den*st) <= m &&
                rem(den, start_d) == 0 && rem(den, step_d) == 0
            start_n *= div(den, start_d)
            step_n *= div(den, step_d)
            return floatrange(T, start_n, step_n, len, den)
        end
    end
    steprangelen_hp(T, a, st, 0, len, 1)
end
```

-/
def rangeStartStepLength {F I L N R : Type} (ops : FloatRangeOps F I L N R)
    (type : Type) (lenPlusZero : L → L) (round : F → JlX L)
    (clampInt : L → L → L → L) (floatInt : I → F) (offsetToInt : L → I)
    (one : L) (a st : F) (len : L) : JlX R := do
  let len := lenPlusZero len
  let (startN, startD) ← ops.rat a
  let (stepN, stepD) ← ops.rat st
  if !ops.integer.eq startD ops.integer.zero && !ops.integer.eq stepD ops.integer.zero &&
      ops.float.eq (ops.float.div (ops.ofInt startN) (ops.ofInt startD)) a &&
      ops.float.eq (ops.float.div (ops.ofInt stepN) (ops.ofInt stepD)) st then
    let den ← ops.lcmUnchecked startD stepD
    let m := ops.maxintfloat
    if ops.float.le (ops.float.abs (ops.float.mul (ops.ofInt den) a)) m &&
        ops.float.le (ops.float.abs (ops.float.mul (ops.ofInt den) st)) m &&
        ops.integer.eq (ops.integer.rem den startD) ops.integer.zero &&
        ops.integer.eq (ops.integer.rem den stepD) ops.integer.zero then
      let startN := ops.integer.mul startN (ops.integer.div den startD)
      let stepN := ops.integer.mul stepN (ops.integer.div den stepD)
      return ← floatrange ops type lenPlusZero round clampInt floatInt offsetToInt one
        startN stepN len den
  ops.hpFloat a st ops.zeroN len one

/--
Julia source: base/twiceprecision.jl:468-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_step_stop_length(step::Real, stop::IEEEFloat, len::Integer) =
    range_step_stop_length(promote(step, stop)..., len)
```

-/
def rangeStepStopLengthRealFloat {F A I R : Type}
    (promote : A → F → F × F) (rangeStepStopLength : F → F → I → JlX R)
    (step : A) (stop : F) (len : I) : JlX R :=
  let (step, stop) := promote step stop
  rangeStepStopLength step stop len

/--
Julia source: base/twiceprecision.jl:471-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_step_stop_length(step::IEEEFloat, stop::Real, len::Integer) =
    range_step_stop_length(promote(step, stop)..., len)
```

-/
def rangeStepStopLengthFloatReal {F A I R : Type}
    (promote : F → A → F × F) (rangeStepStopLength : F → F → I → JlX R)
    (step : F) (stop : A) (len : I) : JlX R :=
  let (step, stop) := promote step stop
  rangeStepStopLength step stop len

/--
Julia source: base/twiceprecision.jl:474-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function range_step_stop_length(step::IEEEFloat, stop::IEEEFloat, len::Integer)
    r = range_start_step_length(stop, negate(step), len)
    reverse(r)
end
```

-/
def rangeStepStopLength {F I L N R : Type} (ops : FloatRangeOps F I L N R)
    (type : Type) (lenPlusZero : L → L) (round : F → JlX L)
    (clampInt : L → L → L → L) (floatInt : I → F) (offsetToInt : L → I) (one : L)
    (negate : F → F) (reverse : R → JlX R) (step stop : F) (len : L) : JlX R := do
  let r ← rangeStartStepLength ops type lenPlusZero round clampInt floatInt offsetToInt one
    stop (negate step) len
  reverse r

/--
Julia source: base/twiceprecision.jl:480-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, i::Integer) where T
    # Very similar to _getindex_hiprec, but optimized to avoid a 2nd call to add12
    u = oftype(r.offset, i) - r.offset
    shift_hi, shift_lo = u*r.step.hi, u*r.step.lo
    x_hi, x_lo = add12(r.ref.hi, shift_hi)
    T(x_hi + (x_lo + (shift_lo + r.ref.lo)))
end
```

-/
def unsafeGetindex {T F L I : Type} (oftype : L → I → JlX L)
    (sub : L → L → L) (mul : L → F → F) (add : F → F → F)
    (add12 : F → F → F × F) (convert : F → JlX T)
    (r : StepRangeLen T (TwicePrecision F) (TwicePrecision F) L) (i : I) : JlX T := do
  let u := sub (← oftype r.offset i) r.offset
  let shift_hi := mul u r.step.hi
  let shift_lo := mul u r.step.lo
  let (x_hi, x_lo) := add12 r.ref.hi shift_hi
  convert (add x_hi (add x_lo (add shift_lo r.ref.lo)))

/--
Julia source: base/twiceprecision.jl:488-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex_hiprec(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision}, i::Integer)
    i isa Bool && throw(ArgumentError("invalid index: $i of type Bool"))
    u = oftype(r.offset, i) - r.offset
    shift_hi, shift_lo = u*r.step.hi, u*r.step.lo
    x_hi, x_lo = add12(r.ref.hi, shift_hi)
    x_hi, x_lo = add12(x_hi, x_lo + (shift_lo + r.ref.lo))
    TwicePrecision(x_hi, x_lo)
end
```

-/
def getindexHiprec {F L I : Type} (isBool : I → Bool) (showIndex : I → String)
    (oftype : L → I → JlX L) (sub : L → L → L) (mul : L → F → F) (add : F → F → F)
    (add12 : F → F → F × F)
    (r : StepRangeLen F (TwicePrecision F) (TwicePrecision F) L) (i : I) :
    JlX (TwicePrecision F) := do
  if isBool i then throw (.jl (.argumentError ("invalid index: " ++ showIndex i ++ " of type Bool")))
  let u := sub (← oftype r.offset i) r.offset
  let shift_hi := mul u r.step.hi
  let shift_lo := mul u r.step.lo
  let (x_hi, x_lo) := add12 r.ref.hi shift_hi
  let (x_hi, x_lo) := add12 x_hi (add x_lo (add shift_lo r.ref.lo))
  pure ⟨x_hi, x_lo⟩

/--
Julia source: base/twiceprecision.jl:497-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, s::OrdinalRange{S}) where {T, S<:Integer}
    @boundscheck checkbounds(r, s)
    len = length(s)
    L = typeof(len)
    sstep = step_hp(s)
    rstep = step_hp(r)
    if S === Bool
        #rstep *= one(sstep)
        if len == 0
            return StepRangeLen{T}(first(r), rstep, zero(L), oneunit(L))
        elseif len == 1
            if first(s)
                return StepRangeLen{T}(first(r), rstep, oneunit(L), oneunit(L))
            else
                return StepRangeLen{T}(first(r), rstep, zero(L), oneunit(L))
            end
        else # len == 2
            return StepRangeLen{T}(last(r), step(r), oneunit(L), oneunit(L))
        end
    else
        soffset = round(L, (r.offset - first(s))/sstep + 1)
        soffset = clamp(soffset, oneunit(L), len)
        ioffset = L(first(s) + (soffset - oneunit(L)) * sstep)
        if sstep == 1 || len < 2
            newstep = rstep #* one(sstep)
        else
            newstep = rstep * sstep
            newstep = twiceprecision(newstep, nbitslen(T, len, soffset))
        end
        soffset = max(oneunit(L), soffset)
        if ioffset == r.offset
            return StepRangeLen{T}(r.ref, newstep, len, soffset)
        else
            return StepRangeLen{T}(r.ref + (ioffset-r.offset)*rstep, newstep, len, soffset)
        end
    end
end
```

-/
def getindexStepRangeLen {T Ref Step LR U L I N Out : Type}
    (checkbounds : StepRangeLen T Ref Step LR → U → JlX Unit)
    (length : U → L) (stepHp : U → I) (stepHpRange : StepRangeLen T Ref Step LR → Step)
    (stepRange : StepRangeLen T Ref Step LR → Step)
    (isBoolRange : Bool) (firstBool : U → Bool) (firstIndex : U → I)
    (firstRange : StepRangeLen T Ref Step LR → T)
    (lastRange : StepRangeLen T Ref Step LR → T)
    (ops : Arithmetic L) (indexOps : Arithmetic I) (toLen : I → L) (toIndex : L → I)
    (offsetToLen : LR → L)
    (round : L → L) (clamp : L → L → L → L) (oneUnit zeroLen : L)
    (stepEqualsOne : I → Bool) (lenBelowTwo : L → Bool)
    (mulStep : Step → I → Step) (twiceprecision : Step → N → Step)
    (nbitslen : Type → L → L → N) (addRef : Ref → Step → Ref)
    (scaleStep : L → Step → Step) (makeT : T → Step → L → L → JlX Out)
    (makeRef : Ref → Step → L → L → JlX Out)
    (r : StepRangeLen T Ref Step LR) (s : U) : JlX Out := do
  checkbounds r s
  let len := length s
  let sstep := stepHp s
  let rstep := stepHpRange r
  if isBoolRange then
    if ops.eq len zeroLen then
      return ← makeT (firstRange r) rstep zeroLen oneUnit
    else if ops.eq len oneUnit then
      if firstBool s then return ← makeT (firstRange r) rstep oneUnit oneUnit
      else return ← makeT (firstRange r) rstep zeroLen oneUnit
    else
      return ← makeT (lastRange r) (stepRange r) oneUnit oneUnit
  let first := toLen (firstIndex s)
  let soffset := clamp (round (ops.add (ops.div (ops.sub (offsetToLen r.offset) first)
    (toLen sstep)) oneUnit)) oneUnit len
  let ioffset := toLen (indexOps.add (firstIndex s) (indexOps.mul (toIndex (ops.sub soffset oneUnit)) sstep))
  let newstep :=
    if stepEqualsOne sstep || lenBelowTwo len then rstep
    else twiceprecision (mulStep rstep sstep) (nbitslen T len soffset)
  let soffset := if ops.lt oneUnit soffset then soffset else oneUnit
  if ops.eq ioffset (offsetToLen r.offset) then
    makeRef r.ref newstep len soffset
  else
    makeRef (addRef r.ref (scaleStep (ops.sub ioffset (offsetToLen r.offset)) rstep))
      newstep len soffset

/--
Julia source: base/twiceprecision.jl:535-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Real, r::StepRangeLen{<:Real,<:TwicePrecision}) =
    StepRangeLen(x*r.ref, twiceprecision(x*r.step, nbitslen(r)), length(r), r.offset)
```

-/
def scalarMulRange {T R S L X R' S' Out N : Type}
    (mul : X → R → R') (mulStep : X → S → S') (twiceprecision : S' → N → S')
    (nbitslen : StepRangeLen T R S L → N) (length : StepRangeLen T R S L → L)
    (make : R' → S' → L → L → JlX Out) (x : X) (r : StepRangeLen T R S L) : JlX Out :=
  make (mul x r.ref) (twiceprecision (mulStep x r.step) (nbitslen r)) (length r) r.offset

/--
Julia source: base/twiceprecision.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(r::StepRangeLen{<:Real,<:TwicePrecision}, x::Real) = x*r
```

-/
def scalarMulRangeRight {T R S L X Out : Type}
    (scalarMul : X → StepRangeLen T R S L → JlX Out) (r : StepRangeLen T R S L) (x : X) :
    JlX Out := scalarMul x r

/--
Julia source: base/twiceprecision.jl:538-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(r::StepRangeLen{<:Real,<:TwicePrecision}, x::Real) =
    StepRangeLen(r.ref/x, twiceprecision(r.step/x, nbitslen(r)), length(r), r.offset)
```

-/
def scalarDivRange {T R S L X R' S' Out N : Type}
    (div : R → X → R') (divStep : S → X → S') (twiceprecision : S' → N → S')
    (nbitslen : StepRangeLen T R S L → N) (length : StepRangeLen T R S L → L)
    (make : R' → S' → L → L → JlX Out) (r : StepRangeLen T R S L) (x : X) : JlX Out :=
  make (div r.ref x) (twiceprecision (divStep r.step x) (nbitslen r)) (length r) r.offset

/--
Julia source: base/twiceprecision.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S,L}(r::StepRangeLen{T,R,S,L}) where {T<:AbstractFloat,R<:TwicePrecision,S<:TwicePrecision,L} = r
```

-/
def stepRangeIdentity {T R S L : Type} (r : StepRangeLen T R S L) : StepRangeLen T R S L := r

/--
Julia source: base/twiceprecision.jl:543-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S,L}(r::StepRangeLen) where {T<:AbstractFloat,R<:TwicePrecision,S<:TwicePrecision,L} =
    _convertSRL(StepRangeLen{T,R,S,L}, r)
```

-/
def stepRangeConvert {T R S L R' S' L' : Type}
    (convertSRL : StepRangeLen T R' S' L' → JlX (StepRangeLen T R S L))
    (r : StepRangeLen T R' S' L') : JlX (StepRangeLen T R S L) := convertSRL r

/--
Julia source: base/twiceprecision.jl:546-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{Float64}(r::StepRangeLen) =
    _convertSRL(StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}, r)
```

-/
def stepRangeFloat64Convert {T R S L : Type}
    (convertSRL : StepRangeLen T R S L → JlX
      (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int))
    (r : StepRangeLen T R S L) : JlX
      (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int) := convertSRL r

/--
Julia source: base/twiceprecision.jl:548-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T}(r::StepRangeLen) where {T<:IEEEFloat} =
    _convertSRL(StepRangeLen{T,Float64,Float64,Int}, r)
```

-/
def stepRangeIEEEConvert {T U R S L : Type}
    (convertSRL : StepRangeLen U R S L → JlX (StepRangeLen T F64 F64 Int))
    (r : StepRangeLen U R S L) : JlX (StepRangeLen T F64 F64 Int) := convertSRL r

/--
Julia source: base/twiceprecision.jl:551-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{Float64}(r::AbstractRange) =
    _convertSRL(StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}, r)
```

-/
def stepRangeFloat64AbstractConvert {Q : Type} (range : Q)
    (convertSRL : Q → JlX (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int)) :
    JlX (StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) Int) := convertSRL range

/--
Julia source: base/twiceprecision.jl:553-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T}(r::AbstractRange) where {T<:IEEEFloat} =
    _convertSRL(StepRangeLen{T,Float64,Float64,Int}, r)
```

-/
def stepRangeIEEEAbstractConvert {T Q R : Type} (range : Q)
    (convertSRL : Q → JlX (StepRangeLen T F64 F64 Int)) : JlX (StepRangeLen T F64 F64 Int) :=
  convertSRL range

/--
Julia source: base/twiceprecision.jl:556-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::StepRangeLen{<:Integer}) where {T,R,S,L}
    StepRangeLen{T,R,S,L}(R(r.ref), S(r.step), L(length(r)), L(r.offset))
end
```

-/
def convertSRLIntegerCounted {T U V R S L I : Type}
    (convertR : U → JlX R) (convertS : V → JlX S) (convertL : I → JlX L)
    (length : StepRangeLen T U V I → I)
    (make : R → S → L → L → JlX (StepRangeLen T R S L))
    (r : StepRangeLen T U V I) : JlX (StepRangeLen T R S L) := do
  make (← convertR r.ref) (← convertS r.step) (← convertL (length r)) (← convertL r.offset)

/--
Julia source: base/twiceprecision.jl:560-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{<:Integer}) where {T,R,S,L}
    StepRangeLen{T,R,S,L}(R(first(r)), S(step(r)), L(length(r)))
end
```

-/
def convertSRLIntegerRange {T R S L Q I : Type}
    (first : Q → I) (step : Q → I) (length : Q → I) (convertR : I → JlX R)
    (convertS : I → JlX S) (convertL : I → JlX L) (one : L)
    (make : R → S → L → L → JlX (StepRangeLen T R S L)) (r : Q) :
    JlX (StepRangeLen T R S L) := do
  make (← convertR (first r)) (← convertS (step r)) (← convertL (length r)) one

/--
Julia source: base/twiceprecision.jl:564-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{U}) where {T,R,S,L,U}
    # if start and step have a rational approximation in the old type,
    # then we transfer that rational approximation to the new type
    f, s = first(r), step(r)
    start_n, start_d = rat(f)
    step_n, step_d = rat(s)
    if start_d != 0 && step_d != 0 &&
            U(start_n/start_d) == f && U(step_n/step_d) == s
        den = lcm_unchecked(start_d, step_d)
        m = maxintfloat(T, Int)
        if den != 0 && abs(f*den) <= m && abs(s*den) <= m &&
                rem(den, start_d) == 0 && rem(den, step_d) == 0
            start_n *= div(den, start_d)
            step_n *= div(den, step_d)
            return floatrange(T, start_n, step_n, L(length(r)), den)
        end
    end
    return __convertSRL(StepRangeLen{T,R,S,L}, r)
end
```

-/
def convertSRLFloatRange {T R S L Q F I N : Type}
    (ops : FloatRangeOps F I L N (StepRangeLen T R S L)) (type : Type)
    (lenPlusZero : L → L) (round : F → JlX L) (clampInt : L → L → L → L)
    (float : I → F) (offsetToInt : L → I) (one : L)
    (first : Q → F) (step : Q → F) (length : Q → L) (exact : F → I → I → Bool)
    (fallback : Q → JlX (StepRangeLen T R S L)) (r : Q) :
    JlX (StepRangeLen T R S L) := do
  let f := first r
  let s := step r
  let (startN, startD) ← ops.rat f
  let (stepN, stepD) ← ops.rat s
  if !ops.integer.eq startD ops.integer.zero && !ops.integer.eq stepD ops.integer.zero &&
      exact f startN startD && exact s stepN stepD then
    let den ← ops.lcmUnchecked startD stepD
    let m := ops.maxintfloat
    if !ops.integer.eq den ops.integer.zero &&
        ops.float.le (ops.float.abs (ops.float.mul f (ops.ofInt den))) m &&
        ops.float.le (ops.float.abs (ops.float.mul s (ops.ofInt den))) m &&
        ops.integer.eq (ops.integer.rem den startD) ops.integer.zero &&
        ops.integer.eq (ops.integer.rem den stepD) ops.integer.zero then
      let startN := ops.integer.mul startN (ops.integer.div den startD)
      let stepN := ops.integer.mul stepN (ops.integer.div den stepD)
      return ← floatrange ops type lenPlusZero round clampInt float offsetToInt one
        startN stepN (length r) den
  fallback r

/--
Julia source: base/twiceprecision.jl:584-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::StepRangeLen{U}) where {T,R,S,L,U}
    StepRangeLen{T,R,S,L}(R(r.ref), S(r.step), L(length(r)), L(r.offset))
end
```

-/
def convertSRLFallback {T R S L U V W I : Type}
    (convertR : V → JlX R) (convertS : W → JlX S) (convertL : I → JlX L)
    (length : StepRangeLen U V W I → I)
    (make : R → S → L → L → JlX (StepRangeLen T R S L))
    (r : StepRangeLen U V W I) : JlX (StepRangeLen T R S L) := do
  make (← convertR r.ref) (← convertS r.step) (← convertL (length r)) (← convertL r.offset)

/--
Julia source: base/twiceprecision.jl:587-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __convertSRL(::Type{StepRangeLen{T,R,S,L}}, r::AbstractRange{U}) where {T,R,S,L,U}
    StepRangeLen{T,R,S,L}(R(first(r)), S(step(r)), L(length(r)))
end
```

-/
def convertRangeFallback {T R S L Q I : Type}
    (first : Q → I) (step : Q → I) (length : Q → I) (convertR : I → JlX R)
    (convertS : I → JlX S) (convertL : I → JlX L) (one : L)
    (make : R → S → L → L → JlX (StepRangeLen T R S L)) (r : Q) :
    JlX (StepRangeLen T R S L) := do
  make (← convertR (first r)) (← convertS (step r)) (← convertL (length r)) one

/--
Julia source: base/twiceprecision.jl:591-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sum(r::StepRangeLen)
    l = length(r)
    # Compute the contribution of step over all indices.
    # Indexes on opposite side of r.offset contribute with opposite sign,
    #    r.step * (sum(1:np) - sum(1:nn))
    np, nn = l - r.offset, r.offset - 1  # positive, negative
    # To prevent overflow in sum(1:n), multiply its factors by the step
    sp, sn = sumpair(np), sumpair(nn)
    W = widen(typeof(l))
    Δn = W(sp[1]) * W(sp[2]) - W(sn[1]) * W(sn[2])
    s = r.step * Δn
    # Add in contributions of ref
    ref = r.ref * l
    convert(eltype(r), s + ref)
end
```

-/
def sumStepRangeLen {T R S L W P Q V : Type}
    (length : StepRangeLen T R S L → L) (sumpair : L → L × L)
    (subL : L → L → L) (one : L) (widen : L → W) (mulW subW : W → W → W)
    (mulStep : S → W → P) (mulRef : R → L → Q) (addResult : P → Q → V)
    (convert : V → JlX T) (r : StepRangeLen T R S L) : JlX T := do
  let l := length r
  let np := subL l r.offset
  let nn := subL r.offset one
  let sp := sumpair np
  let sn := sumpair nn
  let Δn := subW (mulW (widen sp.1) (widen sp.2)) (mulW (widen sn.1) (widen sn.2))
  let s := mulStep r.step Δn
  let ref := mulRef r.ref l
  convert (addResult s ref)

/--
Julia source: base/twiceprecision.jl:606-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sum(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision})
    l = length(r)
    # Compute the contribution of step over all indices.
    # Indexes on opposite side of r.offset contribute with opposite sign,
    #    r.step * (sum(1:np) - sum(1:nn))
    np, nn = l - r.offset, r.offset - 1  # positive, negative
    # To prevent overflow in sum(1:n), multiply its factors by the step
    sp, sn = sumpair(np), sumpair(nn)
    tp = _tp_prod(r.step, sp[1], sp[2])
    tn = _tp_prod(r.step, sn[1], sn[2])
    s_hi, s_lo = add12(tp.hi, -tn.hi)
    s_lo += tp.lo - tn.lo
    # Add in contributions of ref
    ref = r.ref * l
    sm_hi, sm_lo = add12(s_hi, ref.hi)
    add12(sm_hi, sm_lo + s_lo + ref.lo)[1]
end
```

-/
def sumStepRangeLenTwice {T I : Type} (ops : Arithmetic T)
    (length : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I → I)
    (sumpair : I → I × I) (subI : I → I → I) (one : I)
    (tpProd : TwicePrecision T → I → I → TwicePrecision T)
    (mulTpInt : TwicePrecision T → I → TwicePrecision T)
    (add12 : T → T → T × T) (r : StepRangeLen T (TwicePrecision T)
      (TwicePrecision T) I) : T :=
  let l := length r
  let np := subI l r.offset
  let nn := subI r.offset one
  let sp := sumpair np
  let sn := sumpair nn
  let tp := tpProd r.step sp.1 sp.2
  let tn := tpProd r.step sn.1 sn.2
  let (sHi, sLo) := add12 tp.hi (ops.neg tn.hi)
  let sLo := ops.add sLo (ops.sub tp.lo tn.lo)
  let ref := mulTpInt r.ref l
  let (smHi, smLo) := add12 sHi ref.hi
  (add12 smHi (ops.add (ops.add smLo sLo) ref.lo)).1

/--
Julia source: base/twiceprecision.jl:625-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sumpair(n::Integer) = iseven(n) ? (n+1, n>>1) : (n, (n+1)>>1)
```

-/
def sumpair {I : Type} (ops : IntegerOps I) (n : I) : I × I :=
  if ops.isEven n then (ops.add n ops.one, ops.shiftRightOne n)
  else (n, ops.shiftRightOne (ops.add n ops.one))

/--
Julia source: base/twiceprecision.jl:627-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(r1::StepRangeLen{T,R}, r2::StepRangeLen{T,R}) where T where R<:TwicePrecision
    len = length(r1)
    (len == length(r2) ||
        throw(DimensionMismatch("argument dimensions must match")))
    if r1.offset == r2.offset
        imid = r1.offset
        ref = r1.ref + r2.ref
    else
        imid = round(typeof(len), (r1.offset+r2.offset)/2)
        ref1mid = _getindex_hiprec(r1, imid)
        ref2mid = _getindex_hiprec(r2, imid)
        ref = ref1mid + ref2mid
    end
    step = twiceprecision(r1.step + r2.step, nbitslen(T, len, imid))
    StepRangeLen{T,typeof(ref),typeof(step),typeof(len)}(ref, step, len, imid)
end
```

-/
def addStepRangeLen {T I : Type}
    (ops : Arithmetic I) (len1 len2 : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I → I)
    (addTp : TwicePrecision T → TwicePrecision T → TwicePrecision T)
    (getindexHiprec : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I → I →
      JlX (TwicePrecision T))
    (roundHalf : I → I → I) (twiceprecision : TwicePrecision T → Nat → TwicePrecision T)
    (nbitslen : Type → I → I → Nat)
    (make : TwicePrecision T → TwicePrecision T → I → I → JlX
      (StepRangeLen T (TwicePrecision T) (TwicePrecision T) I))
    (r1 r2 : StepRangeLen T (TwicePrecision T) (TwicePrecision T) I) :
    JlX (StepRangeLen T (TwicePrecision T) (TwicePrecision T) I) := do
  let len := len1 r1
  if !ops.eq len (len2 r2) then throw (.dimensionMismatch "argument dimensions must match")
  let (imid, ref) ← if ops.eq r1.offset r2.offset then pure (r1.offset, addTp r1.ref r2.ref)
    else do
      let imid := roundHalf r1.offset r2.offset
      let ref1mid ← getindexHiprec r1 imid
      let ref2mid ← getindexHiprec r2 imid
      pure (imid, addTp ref1mid ref2mid)
  let step := twiceprecision (addTp r1.step r2.step) (nbitslen T len imid)
  make ref step len imid

/--
Julia source: base/twiceprecision.jl:647-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function range_start_stop_length(start::T, stop::T, len::Integer) where {T<:IEEEFloat}
    len = len + 0 # promote with Int
    len < 2 && return _linspace1(T, start, stop, len)
    if start == stop
        return steprangelen_hp(T, start, zero(T), 0, len, 1)
    end
    # Attempt to find exact rational approximations
    _, start_d = rat(start)
    _, stop_d = rat(stop)
    if start_d != 0 && stop_d != 0
        den = lcm_unchecked(start_d, stop_d)
        m = maxintfloat(T, Int)
        if den != 0 && abs(den*start) <= m && abs(den*stop) <= m
            start_n = round(Int, den*start)
            stop_n = round(Int, den*stop)
            if T(start_n/den) == start && T(stop_n/den) == stop
                return _linspace(T, start_n, stop_n, len, den)
            end
        end
    end
    _linspace(start, stop, len)
end
```

-/
def rangeStartStopLength {F I R : Type} (ops : FloatRangeOps F I I N R)
    (lenPlusZero : I → I) (linspace1 : F → F → I → JlX R)
    (linspaceFloat : F → F → I → JlX R) (linspaceRatio : I → I → I → I → JlX R)
    (roundInt : F → JlX I) (start stop : F) (len : I) (one : I) : JlX R := do
  let len := lenPlusZero len
  if ops.integer.lt len (ops.integer.add one one) then return ← linspace1 start stop len
  if ops.float.eq start stop then
    return ← ops.hpFloat start ops.float.zero ops.zeroN len one
  let (_, startD) ← ops.rat start
  let (_, stopD) ← ops.rat stop
  if !ops.integer.eq startD ops.integer.zero && !ops.integer.eq stopD ops.integer.zero then
    let den ← ops.lcmUnchecked startD stopD
    let m := ops.maxintfloat
    if !ops.integer.eq den ops.integer.zero &&
        ops.float.le (ops.float.abs (ops.float.mul (ops.ofInt den) start)) m &&
        ops.float.le (ops.float.abs (ops.float.mul (ops.ofInt den) stop)) m then
      let startN ← roundInt (ops.float.mul (ops.ofInt den) start)
      let stopN ← roundInt (ops.float.mul (ops.ofInt den) stop)
      if ops.float.eq (ops.float.div (ops.ofInt startN) (ops.ofInt den)) start &&
          ops.float.eq (ops.float.div (ops.ofInt stopN) (ops.ofInt den)) stop then
        return ← linspaceRatio startN stopN len den
  linspaceFloat start stop len

/--
Julia source: base/twiceprecision.jl:670-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _linspace(start::T, stop::T, len::Integer) where {T<:IEEEFloat}
    len = len + 0 # promote with Int
    (isfinite(start) && isfinite(stop)) || throw(ArgumentError("start and stop must be finite, got $start and $stop"))
    # Find the index that returns the smallest-magnitude element
    Δ, Δfac = stop-start, 1
    if !isfinite(Δ)   # handle overflow for large endpoints
        Δ, Δfac = stop/len - start/len, len
    end
    tmin = -(start/Δ)/Δfac            # t such that (1-t)*start + t*stop == 0
    L = typeof(len)
    lenn1 = len - oneunit(L)
    imin = round(L, tmin*lenn1 + 1) # index approximately corresponding to t
    if 1 < imin < len
        # The smallest-magnitude element is in the interior
        t = (imin - 1)/lenn1
        ref = T((1-t)*start + t*stop)
        step = imin-1 < len-imin ? (ref-start)/(imin-1) : (stop-ref)/(len-imin)
    elseif imin <= 1
        imin = oneunit(L)
        ref = start
        step = (Δ/(lenn1))*Δfac
    else
        imin = len
        ref = stop
        step = (Δ/(lenn1))*Δfac
    end
    if len == 2 && !isfinite(step)
        # For very large endpoints where step overflows, exploit the
        # split-representation to handle the overflow
        return steprangelen_hp(T, start, (-start, stop), 0, len, oneunit(L))
    end
    # 2x calculations to get high precision endpoint matching while also
    # preventing overflow in ref_hi+(i-offset)*step_hi
    m, k = prevfloat(floatmax(T)), max(imin-1, len-imin)
    step_hi_pre = clamp(step, max(-(m+ref)/k, (-m+ref)/k), min((m-ref)/k, (m+ref)/k))
    nb = nbitslen(T, len, imin)
    step_hi = truncbits(step_hi_pre, nb)
    x1_hi, x1_lo = add12((1-imin)*step_hi, ref)
    x2_hi, x2_lo = add12((len-imin)*step_hi, ref)
    a, b = (start - x1_hi) - x1_lo, (stop - x2_hi) - x2_lo
    step_lo = (b - a)/(len - 1)
    ref_lo = a - (1 - imin)*step_lo
    steprangelen_hp(T, (ref, ref_lo), (step_hi, step_lo), 0, len, imin)
end
```

-/
def linspaceFloat {F I R : Type} (ops : FloatRangeOps F I I N R)
    (lenPlusZero : I → I) (roundInt : F → JlX I) (float : I → F)
    (one : I) (isfinite : F → Bool) (prevfloat : F → F) (floatmax : F)
    (maxF minF : F → F → F) (clampF : F → F → F → F)
    (truncbits : F → N → F) (add12 : F → F → F × F)
    (hp : F × F → F × F → N → I → I → JlX R)
    (errorMessage : F → F → String) (start stop : F) (len : I) : JlX R := do
  let len := lenPlusZero len
  if !(isfinite start && isfinite stop) then
    throw (.jl (.argumentError (errorMessage start stop)))
  let (Δ, Δfac) := if isfinite (ops.float.sub stop start) then
      (ops.float.sub stop start, ops.integer.one)
    else (ops.float.sub (ops.float.div stop (float len)) (ops.float.div start (float len)), len)
  let tmin := ops.float.div (ops.float.neg (ops.float.div start Δ)) (float Δfac)
  let lenn1 := ops.integer.sub len ops.integer.one
  let imin0 ← roundInt (ops.float.add (ops.float.mul tmin (float lenn1)) ops.float.one)
  let (imin, ref, step) :=
    if ops.integer.lt ops.integer.one imin0 && ops.integer.lt imin0 len then
      let t := ops.float.div (float (ops.integer.sub imin0 ops.integer.one)) (float lenn1)
      let ref := ops.float.add (ops.float.mul (ops.float.sub ops.float.one t) start)
        (ops.float.mul t stop)
      let step := if ops.integer.lt (ops.integer.sub imin0 ops.integer.one)
          (ops.integer.sub len imin0) then
        ops.float.div (ops.float.sub ref start) (float (ops.integer.sub imin0 ops.integer.one))
      else ops.float.div (ops.float.sub stop ref) (float (ops.integer.sub len imin0))
      (imin0, ref, step)
    else if ops.integer.le imin0 ops.integer.one then
      (ops.integer.one, start,
        ops.float.mul (ops.float.div Δ (float lenn1)) (float Δfac))
    else (len, stop, ops.float.mul (ops.float.div Δ (float lenn1)) (float Δfac))
  if ops.integer.eq len (ops.integer.add ops.integer.one ops.integer.one) && !isfinite step then
    return ← hp (start, ops.float.zero) (ops.float.neg start, stop) ops.zeroN len
      ops.integer.one
  let m := prevfloat floatmax
  let k := float (ops.integer.max (ops.integer.sub imin ops.integer.one) (ops.integer.sub len imin))
  let lower := maxF (ops.float.div (ops.float.neg (ops.float.add m ref)) k)
    (ops.float.div (ops.float.add (ops.float.neg m) ref) k)
  let upper := minF (ops.float.div (ops.float.sub m ref) k) (ops.float.div (ops.float.add m ref) k)
  let stepHiPre := clampF step lower upper
  let nb := ops.nbitslen F len imin
  let stepHi := truncbits stepHiPre nb
  let (x1Hi, x1Lo) := add12 (ops.float.mul (float (ops.integer.sub ops.integer.one imin)) stepHi) ref
  let (x2Hi, x2Lo) := add12 (ops.float.mul (float (ops.integer.sub len imin)) stepHi) ref
  let a := ops.float.sub (ops.float.sub start x1Hi) x1Lo
  let b := ops.float.sub (ops.float.sub stop x2Hi) x2Lo
  let stepLo := ops.float.div (ops.float.sub b a) (float (ops.integer.sub len ops.integer.one))
  let refLo := ops.float.sub a (ops.float.mul (float (ops.integer.sub ops.integer.one imin)) stepLo)
  hp (ref, refLo) (stepHi, stepLo) ops.zeroN len imin

/--
Julia source: base/twiceprecision.jl:717-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where {T<:IEEEFloat} = _linspace(T, start, stop, len, one(start))
```

-/
def linspaceIntegerType {A B I R : Type} (one : A → I)
    (linspaceRational : A → B → I → I → JlX R) (start : A) (stop : B) (len : I) :
    JlX R := linspaceRational start stop len (one start)

/--
Julia source: base/twiceprecision.jl:718-734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _linspace(::Type{T}, start_n::Integer, stop_n::Integer, len::Integer, den::Integer) where T<:IEEEFloat
    len = len + 0 # promote with Int
    len < 2 && return _linspace1(T, start_n/den, stop_n/den, len)
    L = typeof(len)
    start_n == stop_n && return steprangelen_hp(T, (start_n, den), (zero(start_n), den), 0, len, oneunit(L))
    tmin = -start_n/(Float64(stop_n) - Float64(start_n))
    imin = round(typeof(len), tmin*(len-1)+1)
    imin = clamp(imin, oneunit(L), len)
    W = widen(L)
    start_n = W(start_n)
    stop_n = W(stop_n)
    ref_num = W(len-imin) * start_n + W(imin-1) * stop_n
    ref_denom = W(len-1) * den
    ref = (ref_num, ref_denom)
    step_full = (stop_n - start_n, ref_denom)
    steprangelen_hp(T, ref, step_full, nbitslen(T, len, imin), len, imin)
end
```

-/
def linspaceRational {F I L W N R : Type} (ops : FloatRangeOps F I L N R)
    (lenPlusZero : L → L) (linspace1 : F → F → L → JlX R)
    (toF64Int : I → F64) (toF64Len : L → F64) (roundInt : F64 → JlX L) (clamp : L → L → L → L)
    (widenLen : L → W) (widenInt : I → W) (wide : Arithmetic W) (one : L)
    (hpRatioWide : W × W → W × W → N → L → L → JlX R)
    (startN stopN den : I) (len : L) : JlX R := do
  let len := lenPlusZero len
  if ops.lengthInteger.lt len (ops.lengthInteger.add one one) then
    return ← linspace1 (ops.float.div (ops.ofInt startN) (ops.ofInt den))
      (ops.float.div (ops.ofInt stopN) (ops.ofInt den)) len
  if ops.integer.eq startN stopN then
    return ← hpRatioWide (widenInt startN, widenInt den) (wide.zero, widenInt den)
      ops.zeroN len one
  let tmin := JuliaLean.base.float.div_IEEEFloat
    (JuliaLean.base.float.neg_IEEEFloat (toF64Int startN))
    (JuliaLean.base.float.sub_IEEEFloat (toF64Int stopN) (toF64Int startN))
  let imin0 ← roundInt (JuliaLean.base.float.add_IEEEFloat
    (JuliaLean.base.float.mul_IEEEFloat tmin (toF64Len (ops.lengthInteger.sub len one)))
    (JuliaLean.base.float.one_float .f64))
  let imin := clamp imin0 one len
  let refNum := wide.add
    (wide.mul (widenLen (ops.lengthInteger.sub len imin)) (widenInt startN))
    (wide.mul (widenLen (ops.lengthInteger.sub imin one)) (widenInt stopN))
  let refDenom := wide.mul (widenLen (ops.lengthInteger.sub len one)) (widenInt den)
  hpRatioWide (refNum, refDenom)
    (wide.sub (widenInt stopN) (widenInt startN), refDenom)
    (ops.nbitslen F len imin) len imin

/--
Julia source: base/twiceprecision.jl:737-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _linspace1(::Type{T}, start, stop, len::Integer) where T<:IEEEFloat
    len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
    if len <= 1
        len == 1 && (start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ")))
        # Ensure that first(r)==start and last(r)==stop even for len==0
        # The output type must be consistent with steprangelen_hp
        if T<:Union{Float32,Float16}
            return StepRangeLen{T}(Float64(start), Float64(start) - Float64(stop), len, 1)
        else # T == Float64
            return StepRangeLen(TwicePrecision(start, zero(T)), TwicePrecision(start, -stop), len, 1)
        end
    end
    throw(ArgumentError("should only be called for len < 2, got $len"))
end
```

-/
def linspace1 {T I R : Type} (lenOps : IntegerOps I) (ops : Arithmetic T)
    (showT : T → String) (showLen : I → String) (isSmallFloat : Type → Bool)
    (toF64 : T → F64) (makeSmall : F64 → F64 → I → I → JlX R)
    (makeTwice : TwicePrecision T → TwicePrecision T → I → I → JlX R)
    (formatError : String → T → T → I → String) (start stop : T) (len : I) : JlX R := do
  if lenOps.lt len lenOps.zero then
    throw (.jl (.argumentError (formatError "negative length" start stop len)))
  if lenOps.le len lenOps.one then
    if lenOps.eq len lenOps.one && !ops.eq start stop then
      throw (.jl (.argumentError (formatError "endpoints differ" start stop len)))
    if isSmallFloat T then
      return ← makeSmall (toF64 start) (JuliaLean.base.float.sub_IEEEFloat (toF64 start) (toF64 stop)) len lenOps.one
    return ← makeTwice ⟨start, ops.zero⟩ ⟨start, ops.neg stop⟩ len lenOps.one
  throw (.jl (.argumentError ("should only be called for len < 2, got " ++ showLen len)))

/--
Julia source: base/twiceprecision.jl:757-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rat(x)
    y = x
    a = d = 1
    b = c = 0
    m = maxintfloat(narrow(typeof(x)), Int)
    while abs(y) <= m
        f = trunc(Int, y)
        y -= f
        a, c = f*a + c, a
        b, d = f*b + d, b
        max(abs(a), abs(b)) <= convert(Int,m) || return c, d
        oftype(x,a)/oftype(x,b) == x && break
        y = inv(y)
    end
    return a, b
end
```

-/
def rat {F I : Type} (ops : RatOps F I) (x : F) (fuel : Nat := 100) : JlX (I × I) :=
  ratLoop fuel ops x x ops.integer.one ops.integer.zero ops.integer.zero ops.integer.one

/--
Julia source: base/twiceprecision.jl:775-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lcm_unchecked(a::T, b::T) where T<:Integer = a * div(b, gcd(a, b))
```

-/
def lcmUnchecked {I : Type} (ops : IntegerOps I) (div : I → I → JlX I)
    (a b : I) : JlX I := do
  let q ← div b (ops.gcd a b)
  pure (ops.mul a q)

/--
Julia source: base/twiceprecision.jl:777-777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
narrow(::Type{T}) where {T<:AbstractFloat} = Float64
```

-/
def narrowAbstract (_ : Type) : IEEEType := .f64

/--
Julia source: base/twiceprecision.jl:778-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
narrow(::Type{Float64}) = Float32
```

-/
def narrowF64 : IEEEType := .f32

/--
Julia source: base/twiceprecision.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
narrow(::Type{Float32}) = Float16
```

-/
def narrowF32 : IEEEType := .f16

/--
Julia source: base/twiceprecision.jl:780-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
narrow(::Type{Float16}) = Float16
```

-/
def narrowF16 : IEEEType := .f16

/--
Julia source: base/twiceprecision.jl:782-785 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _tp_prod(t::TwicePrecision, x, y...)
    @inline
    _tp_prod(t * x, y...)
end
```

-/
def tpProdRecursive {T X : Type} (mul : TwicePrecision T → X → TwicePrecision T)
    (recurse : TwicePrecision T → List X → TwicePrecision T)
    (t : TwicePrecision T) (x : X) (ys : List X) : TwicePrecision T :=
  recurse (mul t x) ys

/--
Julia source: base/twiceprecision.jl:786-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tp_prod(t::TwicePrecision) = t
```

-/
def tpProdBase {T : Type} (t : TwicePrecision T) : TwicePrecision T := t

/--
Julia source: base/twiceprecision.jl:787-788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::TwicePrecision{T}, y::TwicePrecision{T}) where {T} =
    x.hi < y.hi || ((x.hi == y.hi) & (x.lo < y.lo))
```

-/
def tpLt {T : Type} (ops : Arithmetic T) (x y : TwicePrecision T) : Bool :=
  ops.lt x.hi y.hi || (ops.eq x.hi y.hi && ops.lt x.lo y.lo)

/--
Julia source: base/twiceprecision.jl:790-790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbetween(a, x, b) = a <= x <= b || b <= x <= a
```

-/
def isbetween {T : Type} (ops : Arithmetic T) (a x b : T) : Bool :=
  (ops.le a x && ops.le x b) || (ops.le b x && ops.le x a)

/--
Julia source: base/twiceprecision.jl:794-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_exp_allowing_twice64(x::Number) = exp(x)
```

-/
def expAllowingTwiceNumber {N R : Type} (exp : N → R) (x : N) : R := exp x

/--
Julia source: base/twiceprecision.jl:795-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_exp_allowing_twice64(x::TwicePrecision{Float64}) = Math.exp_impl(x.hi, x.lo, Val(:ℯ))
```

-/
def expAllowingTwice64 (expImpl : F64 → F64 → Unit → F64) (euler : Unit)
    (x : TwicePrecision F64) : F64 := expImpl x.hi x.lo euler

/--
Julia source: base/twiceprecision.jl:798-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _log_twice64_unchecked(x::Float64)
    xu = reinterpret(UInt64, x)
    if xu < (UInt64(1)<<52) # x is subnormal
        xu = reinterpret(UInt64, x * 0x1p52) # normalize x
        xu &= ~sign_mask(Float64)
        xu -%= (UInt64(52) << 52) # mess with the exponent
    end
    TwicePrecision(Math._log_ext(xu)...)
end
```

-/
def logTwice64Unchecked (logExt : JInt .u64 → F64 × F64)
    (x : F64) : TwicePrecision F64 :=
  let xu := JuliaLean.base.float.reinterpret_Unsigned_Float64 x
  let xu := if JuliaLean.base.int.lt_BitUnsigned xu
      (JuliaLean.base.int.shl_Int (JuliaLean.base.int.lit .u64 1) (JuliaLean.base.int.lit .i64 52)) then
    let two52 : F64 := JuliaLean.Promotion.Fl.ofBits 0x4330000000000000
    let xu := JuliaLean.base.float.reinterpret_Unsigned_Float64 (JuliaLean.base.float.mul_IEEEFloat x two52)
    let xu := JuliaLean.base.int.band xu (JuliaLean.base.int.bnot JuliaLean.base.float.sign_mask_Float64)
    JuliaLean.base.int.subWrap xu
      (JuliaLean.base.int.shl_Int (JuliaLean.base.int.lit .u64 52) (JuliaLean.base.int.lit .i64 52))
    else xu
  let (hi, lo) := logExt xu
  ⟨hi, lo⟩


/-! ## Concrete `IEEEFloat` (`JuliaLean.base.float`) and `BitInteger` (`JuliaLean.base.int`) dispatch -/

def liftJl {α : Type} (r : Jl α) : JlX α :=
  match r with
  | .ok x => .ok x
  | .error e => .error (.jl e)

def frexpFl {f : JuliaLean.Promotion.Fmt} (x : JuliaLean.Promotion.Fl f) :
    JuliaLean.Promotion.Fl f × Int :=
  if !x.isfinite || x.iszero then (x, 0)
  else if x.expField > 0 then
    let xs := JuliaLean.Promotion.Fl.ofBits
      ((if x.signbit then 2 ^ (f.eb + f.sb) else 0) + (f.bias - 1) * 2 ^ f.sb + x.frac)
    (xs, (x.expField : Int) - ((f.bias - 1 : Nat) : Int))
  else
    let k := x.frac.log2
    let m := x.frac * 2 ^ (f.sb - k)
    let xs := JuliaLean.Promotion.Fl.ofBits
      ((if x.signbit then 2 ^ (f.eb + f.sb) else 0) + (f.bias - 1) * 2 ^ f.sb + (m - 2 ^ f.sb))
    (xs, (k : Int) - ((f.bias + f.sb - 2 : Nat) : Int))

def ldexpFl {f : JuliaLean.Promotion.Fmt} (x : JuliaLean.Promotion.Fl f) (e : Int) :
    JuliaLean.Promotion.Fl f :=
  if !x.isfinite || x.iszero then x
  else if e > 2100 then JuliaLean.Promotion.Fl.inf x.signbit
  else if e < -2100 then JuliaLean.Promotion.Fl.zero x.signbit
  else
    let (n, d) := x.toRat
    if e ≥ 0 then JuliaLean.Promotion.Fl.roundRat (n * (2 ^ e.toNat : Nat)) d x.signbit
    else JuliaLean.Promotion.Fl.roundRat n (d * 2 ^ (-e).toNat) x.signbit

def fvArithmetic (T : JuliaLean.base.float.FTy) : Arithmetic (JuliaLean.base.float.FV T) := {
  add := JuliaLean.base.float.add_IEEEFloat,
  sub := JuliaLean.base.float.sub_IEEEFloat,
  mul := JuliaLean.base.float.mul_IEEEFloat,
  div := JuliaLean.base.float.div_IEEEFloat,
  neg := JuliaLean.base.float.neg_IEEEFloat,
  abs := JuliaLean.base.float.abs_IEEEFloat,
  lt := JuliaLean.base.float.lt_IEEEFloat,
  le := JuliaLean.base.float.le_IEEEFloat,
  gt := fun x y => JuliaLean.base.float.lt_IEEEFloat y x,
  eq := JuliaLean.base.float.eq_IEEEFloat,
  zero := JuliaLean.base.float.zero_float T,
  one := JuliaLean.base.float.one_float T,
  iszero := JuliaLean.base.float.iszero_float,
  isfinite := JuliaLean.base.float.isfinite_IEEEFloat,
  twoMul := fun x y =>
    let h := JuliaLean.base.float.mul_IEEEFloat x y
    (h, JuliaLean.C.jlFmaFloat x y (JuliaLean.base.float.neg_IEEEFloat h)),
  fma := JuliaLean.C.jlFmaFloat,
  frexp := frexpFl,
  ldexp := ldexpFl,
  truncInt := fun x =>
    match JuliaLean.base.float.round_ToZero .i64 x with
    | .ok i => .ok i.val
    | .error e => .error (.jl e),
  inv := fun x => JuliaLean.base.float.div_IEEEFloat (JuliaLean.base.float.one_float T) x
}

abbrev f64Arithmetic : Arithmetic F64 := fvArithmetic .f64

def bitOpsIEEE (T : JuliaLean.base.float.FTy) :
    BitOps (JuliaLean.base.float.FV T) (JInt T.uintTy) (JInt T.uintTy) (JInt .i64) := {
  reinterpretTo := JuliaLean.base.float.reinterpret_Unsigned,
  reinterpretFrom := JuliaLean.base.float.reinterpret_Float_Int T,
  bitAnd := JuliaLean.base.int.band,
  typemax := JuliaLean.base.int.typemax T.uintTy,
  shiftLeft := JuliaLean.base.int.shl_Int
}

abbrev bitOps64 := bitOpsIEEE .f64

def jintOps (t : IntTy) : IntegerOps (JInt t) := {
  add := JuliaLean.base.int.add,
  sub := JuliaLean.base.int.sub,
  mul := JuliaLean.base.int.mulSame,
  div := fun a b =>
    match JuliaLean.base.int.divSame a b with
    | .ok q => q
    | .error _ => JuliaLean.base.int.lit t 0,
  rem := fun a b =>
    match JuliaLean.base.int.remSame a b with
    | .ok r => r
    | .error _ => JuliaLean.base.int.lit t 0,
  neg := JuliaLean.base.int.neg,
  abs := JuliaLean.base.int.abs,
  max := fun a b => JuliaLean.base.int.remT t (JuliaLean.base.int.jmax a b),
  lt := JuliaLean.base.int.ltSame,
  le := JuliaLean.base.int.leSame,
  eq := JuliaLean.base.int.eqSame,
  isEven := fun a =>
    JuliaLean.base.int.eq (JuliaLean.base.int.binop JuliaLean.base.int.band a (JuliaLean.base.int.lit .i64 1))
      (JuliaLean.base.int.lit .i64 0),
  shiftRightOne := fun a => JuliaLean.base.int.shr_Int a (JuliaLean.base.int.lit .i64 1),
  gcd := fun a b => JuliaLean.base.int.lit t (Nat.gcd a.val.natAbs b.val.natAbs),
  zero := JuliaLean.base.int.lit t 0,
  one := JuliaLean.base.int.lit t 1
}

def jintArith (t : IntTy) : Arithmetic (JInt t) := {
  add := JuliaLean.base.int.add,
  sub := JuliaLean.base.int.sub,
  mul := JuliaLean.base.int.mulSame,
  div := fun a b =>
    match JuliaLean.base.int.divSame a b with
    | .ok q => q
    | .error _ => JuliaLean.base.int.lit t 0,
  neg := JuliaLean.base.int.neg,
  abs := JuliaLean.base.int.abs,
  lt := JuliaLean.base.int.ltSame,
  le := JuliaLean.base.int.leSame,
  gt := fun a b => JuliaLean.base.int.ltSame b a,
  eq := JuliaLean.base.int.eqSame,
  zero := JuliaLean.base.int.lit t 0,
  one := JuliaLean.base.int.lit t 1,
  iszero := fun a => JuliaLean.base.int.eqSame a (JuliaLean.base.int.lit t 0),
  isfinite := fun _ => true,
  twoMul := fun a b => (JuliaLean.base.int.mulSame a b, JuliaLean.base.int.lit t 0),
  fma := fun a b c => JuliaLean.base.int.add (JuliaLean.base.int.mulSame a b) c,
  frexp := fun a => (a, 0),
  ldexp := fun a _ => a,
  truncInt := fun a => .ok a.val,
  inv := fun a =>
    match JuliaLean.base.int.divSame (JuliaLean.base.int.lit t 1) a with
    | .ok q => q
    | .error _ => JuliaLean.base.int.lit t 0
}

def cldNat (a b : Nat) : Nat := (a + b - 1) / b
def cldI64 (a b : JInt .i64) : JInt .i64 :=
  JuliaLean.base.int.lit .i64 ((a.val + b.val - 1) / b.val)

def truncbitsF64 (x : F64) (nb : JInt .i64) : F64 := truncbitsIEEE bitOps64 x nb

def splitprecF64 {t : IntTy} (i : JInt t) : JlX (F64 × F64) :=
  splitprec bitOps64 (fun x nb => truncbitsIEEE bitOps64 x (JuliaLean.base.int.lit .i64 nb))
    (JuliaLean.base.float.precision_Type_default .f64).val.toNat cldNat
    (JuliaLean.base.float.floatOfInt .f64)
    (fun _ x => liftJl (JuliaLean.base.float.intOfFloat t x))
    JuliaLean.base.int.sub i

def tpFromIntegerF64 {t : IntTy} (i : JInt t) : JlX (TwicePrecision F64) :=
  tpFromInteger bitOps64 (fun x nb => truncbitsIEEE bitOps64 x (JuliaLean.base.int.lit .i64 nb))
    (JuliaLean.base.float.precision_Type_default .f64).val.toNat cldNat
    (JuliaLean.base.float.floatOfInt .f64)
    (fun _ x => liftJl (JuliaLean.base.float.intOfFloat t x))
    JuliaLean.base.int.sub f64Arithmetic i

def mulTpF64 (x y : TwicePrecision F64) : TwicePrecision F64 :=
  mulTpSame f64Arithmetic (mul12IEEE f64Arithmetic JuliaLean.base.int.ifelse)
    JuliaLean.base.int.ifelse x y

def divTpF64 (x y : TwicePrecision F64) : TwicePrecision F64 :=
  divTpSame f64Arithmetic (mul12IEEE f64Arithmetic JuliaLean.base.int.ifelse)
    JuliaLean.base.int.ifelse x y

def divTpNumberF64 {t : IntTy} (x : TwicePrecision F64) (d : JInt t) :
    JlX (TwicePrecision F64) :=
  divTpNumber (fun a b => JuliaLean.base.float.div_IEEEFloat a (JuliaLean.base.float.floatOfInt .f64 b))
    (fun _ b => .ok (tpFromSame f64Arithmetic (JuliaLean.base.float.floatOfInt .f64 b)))
    (fun a b => .ok (divTpF64 a b)) x d

def tpRatioF64 {t : IntTy} (nd : JInt t × JInt t) : JlX (TwicePrecision F64) :=
  tpRatio tpFromIntegerF64 divTpNumberF64 nd

def twiceprecisionTPF64 (val : TwicePrecision F64) (nb : JInt .i64) : TwicePrecision F64 :=
  twiceprecisionTP bitOps64 f64Arithmetic val nb

def tpRatioBitsF64 {t : IntTy} (nd : JInt t × JInt t) (nb : JInt .i64) :
    JlX (TwicePrecision F64) :=
  tpRatioBits tpRatioF64 (fun v b => .ok (twiceprecisionTPF64 v b)) nd nb

def tpIntegerRatioBitsF64 {t : IntTy} (nd : JInt t × JInt t) (nb : JInt .i64) :
    JlX (TwicePrecision F64) :=
  tpIntegerRatioBits tpRatioF64 (fun v b => .ok (twiceprecisionTPF64 v b)) nd nb

def nbitslen0I64 (len offset : JInt .i64) : JInt .i64 :=
  nbitslenGeneric JuliaLean.base.int.ltSame JuliaLean.base.int.sub JuliaLean.base.int.jmax
    JuliaLean.base.int.top_set_bit JuliaLean.base.int.add
    (JuliaLean.base.int.lit .i64 2) (JuliaLean.base.int.lit .i64 1)
    (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 0) len offset

def nbitslenF64 (len offset : JInt .i64) : JInt .i64 :=
  nbitslenIEEE nbitslen0I64 (JuliaLean.base.float.precision_Type_default .f64)
    (JuliaLean.base.int.lit .i64 2) cldI64 JuliaLean.base.int.jmin len offset

abbrev SRLF64 := StepRangeLen F64 (TwicePrecision F64) (TwicePrecision F64) (JInt .i64)

def srlNewF64 (ref step : TwicePrecision F64) (len offset : JInt .i64) : JlX SRLF64 :=
  if JuliaLean.base.int.ltSame len (JuliaLean.base.int.lit .i64 0) then
    .error (.jl (.argumentError "length cannot be negative"))
  else if JuliaLean.base.int.leSame (JuliaLean.base.int.lit .i64 1) offset &&
      JuliaLean.base.int.leSame offset (JuliaLean.base.int.jmax (JuliaLean.base.int.lit .i64 1) len) then
    .ok ⟨ref, step, len, offset⟩
  else
    .error (.jl (.argumentError "StepRangeLen: offset must be in [1,len]"))

def srlMakeTpF64 (ref step : TwicePrecision F64) (len offset : JInt .i64) : JlX SRLF64 :=
  stepRangeLenFromTwicePrecision srlNewF64 ref step len offset

def asPartsF64 : F64 ⊕ (F64 × F64) → TwicePrecision F64
  | .inl x => tpFromSame f64Arithmetic x
  | .inr (hi, lo) => ⟨hi, lo⟩

def hpRatioF64 {t : IntTy} (ref step : JInt t × JInt t) (nb len offset : JInt .i64) :
    JlX SRLF64 :=
  steprangelenHpF64 tpRatioF64 tpIntegerRatioBitsF64 srlMakeTpF64 ref step nb len offset

def hpFloat64 (ref step : F64 ⊕ (F64 × F64)) (nb len offset : JInt .i64) : JlX SRLF64 :=
  steprangelenHpFloat64 asPartsF64 twiceprecisionTPF64 srlMakeTpF64 ref step nb len offset

def f64RatOps : RatOps F64 (JInt .i64) := {
  float := f64Arithmetic,
  integer := jintOps .i64,
  bound := JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 16777216),
  convertBound := fun _ => JuliaLean.base.int.lit .i64 16777216,
  truncInt := fun x => liftJl (JuliaLean.base.float.round_ToZero .i64 x),
  ofInt := JuliaLean.base.float.floatOfInt .f64
}

def ratF64 (x : F64) (fuel : Nat := 100) : JlX (JInt .i64 × JInt .i64) :=
  rat f64RatOps x fuel

def lcmUncheckedI64 (a b : JInt .i64) : JlX (JInt .i64) :=
  lcmUnchecked (jintOps .i64) (fun x y => liftJl (JuliaLean.base.int.divSame x y)) a b

def roundIntF64 (x : F64) : JlX (JInt .i64) :=
  liftJl (JuliaLean.base.float.intOfFloat .i64 (JuliaLean.base.float.round_Nearest_llvm x))

def clampI64 (x lo hi : JInt .i64) : JInt .i64 :=
  if JuliaLean.base.int.ltSame hi x then hi
  else if JuliaLean.base.int.ltSame x lo then lo
  else x

def f64RangeOps : FloatRangeOps F64 (JInt .i64) (JInt .i64) (JInt .i64) SRLF64 := {
  float := f64Arithmetic,
  integer := jintOps .i64,
  lengthInteger := jintOps .i64,
  ofInt := JuliaLean.base.float.floatOfInt .f64,
  ofLength := JuliaLean.base.float.floatOfInt .f64,
  convertInt := pure,
  roundInt := roundIntF64,
  rat := fun x => ratF64 x 100,
  lcmUnchecked := lcmUncheckedI64,
  maxintfloat := JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 9007199254740992),
  zeroN := JuliaLean.base.int.lit .i64 0,
  nbitslen := fun _ len offset => nbitslenF64 len offset,
  isbetween := isbetween f64Arithmetic,
  hpRatio := hpRatioF64,
  hpFloat := fun a b nb len offset => hpFloat64 (.inl a) (.inl b) nb len offset
}

def floatrangeF64 (startN stepN len den : JInt .i64) : JlX SRLF64 :=
  floatrange f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) id (JuliaLean.base.int.lit .i64 1)
    startN stepN len den

def colonF64 (start step stop : F64) : JlX SRLF64 :=
  colon f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) (JuliaLean.base.int.lit .i64 1)
    start step stop

def rangeStartStepLengthF64 (a st : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStartStepLength f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) id (JuliaLean.base.int.lit .i64 1)
    a st len

def srlReverseF64 (r : SRLF64) : JlX SRLF64 :=
  let newOffset := if JuliaLean.base.int.eqSame r.len (JuliaLean.base.int.lit .i64 0) then r.offset
    else JuliaLean.base.int.add (JuliaLean.base.int.sub r.len r.offset) (JuliaLean.base.int.lit .i64 1)
  srlMakeTpF64 r.ref (negTp f64Arithmetic r.step) r.len newOffset

def rangeStepStopLengthF64 (step stop : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStepStopLength f64RangeOps F64 id roundIntF64 clampI64
    (JuliaLean.base.float.floatOfInt .f64) id (JuliaLean.base.int.lit .i64 1)
    JuliaLean.base.float.neg_IEEEFloat srlReverseF64 step stop len

def linspace1F64 (start stop : F64) (len : JInt .i64) : JlX SRLF64 :=
  linspace1 (jintOps .i64) f64Arithmetic (fun _ => "") (fun _ => "") (fun _ => false) id
    (fun _ _ _ _ => .error (.jl (.argumentError "unreachable"))) srlMakeTpF64
    (fun msg _ _ _ => msg) start stop len

def fislessF64 (x y : F64) : Bool :=
  JuliaLean.base.float.lt_IEEEFloat x y || (x.signbit && !y.signbit)

def fmaxF64 (x y : F64) : F64 :=
  if JuliaLean.base.float.isnan_IEEEFloat x || (!JuliaLean.base.float.isnan_IEEEFloat y && fislessF64 y x)
    then x else y

def fminF64 (x y : F64) : F64 :=
  if JuliaLean.base.float.isnan_IEEEFloat x || (!JuliaLean.base.float.isnan_IEEEFloat y && fislessF64 x y)
    then x else y

def fclampF64 (x lo hi : F64) : F64 :=
  if JuliaLean.base.float.lt_IEEEFloat hi x then hi
  else if JuliaLean.base.float.lt_IEEEFloat x lo then lo
  else x

def linspaceFloatF64 (start stop : F64) (len : JInt .i64) : JlX SRLF64 :=
  linspaceFloat f64RangeOps id roundIntF64 (JuliaLean.base.float.floatOfInt .f64)
    (JuliaLean.base.int.lit .i64 1) JuliaLean.base.float.isfinite_IEEEFloat
    JuliaLean.base.float.prevfloat (JuliaLean.base.float.floatmax_float .f64)
    fmaxF64 fminF64 fclampF64 truncbitsF64
    (add12Same f64Arithmetic JuliaLean.base.int.ifelse)
    (fun ref step nb l o => hpFloat64 (.inr ref) (.inr step) nb l o)
    (fun _ _ => "start and stop must be finite") start stop len

def f64RangeOps128 : FloatRangeOps F64 (JInt .i128) (JInt .i64) (JInt .i64) SRLF64 := {
  float := f64Arithmetic,
  integer := jintOps .i128,
  lengthInteger := jintOps .i64,
  ofInt := JuliaLean.base.float.floatOfInt .f64,
  ofLength := JuliaLean.base.float.floatOfInt .f64,
  convertInt := pure,
  roundInt := roundIntF64,
  rat := fun _ => .ok (JuliaLean.base.int.lit .i128 1, JuliaLean.base.int.lit .i128 0),
  lcmUnchecked := fun a b => lcmUnchecked (jintOps .i128) (fun x y => liftJl (JuliaLean.base.int.divSame x y)) a b,
  maxintfloat := JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 9007199254740992),
  zeroN := JuliaLean.base.int.lit .i64 0,
  nbitslen := fun _ len offset => nbitslenF64 len offset,
  isbetween := isbetween f64Arithmetic,
  hpRatio := hpRatioF64,
  hpFloat := fun a b nb len offset => hpFloat64 (.inl a) (.inl b) nb len offset
}

def linspaceRationalF64 (startN stopN den : JInt .i64) (len : JInt .i64) : JlX SRLF64 :=
  linspaceRational f64RangeOps id linspace1F64
    (JuliaLean.base.float.floatOfInt .f64) (JuliaLean.base.float.floatOfInt .f64)
    roundIntF64 clampI64 (JuliaLean.base.int.widenTo .i128) (JuliaLean.base.int.widenTo .i128)
    (jintArith .i128) (JuliaLean.base.int.lit .i64 1) (hpRatioF64 (t := .i128))
    startN stopN den len

def linspaceRational128F64 (startN stopN den : JInt .i128) (len : JInt .i64) : JlX SRLF64 :=
  linspaceRational f64RangeOps128 id linspace1F64
    (JuliaLean.base.float.floatOfInt .f64) (JuliaLean.base.float.floatOfInt .f64)
    roundIntF64 clampI64 (JuliaLean.base.int.widenTo .i128) id
    (jintArith .i128) (JuliaLean.base.int.lit .i64 1) (hpRatioF64 (t := .i128))
    startN stopN den len

def linspaceIntegerTypeF64 (start stop len : JInt .i64) : JlX SRLF64 :=
  linspaceIntegerType (fun _ => JuliaLean.base.int.lit .i64 1)
    (fun a b n d => linspaceRationalF64 a b d n) start stop len

def rangeStartStopLengthF64 (start stop : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStartStopLength f64RangeOps id linspace1F64 linspaceFloatF64
    (fun a b n d => linspaceRationalF64 a b d n) roundIntF64
    start stop len (JuliaLean.base.int.lit .i64 1)

def unsafeGetindexF64 (r : SRLF64) (i : JInt .i64) : JlX F64 :=
  unsafeGetindex (fun _ idx => .ok idx) JuliaLean.base.int.sub
    (fun u s => JuliaLean.base.float.mul_IEEEFloat (JuliaLean.base.float.floatOfInt .f64 u) s)
    JuliaLean.base.float.add_IEEEFloat
    (add12Same f64Arithmetic JuliaLean.base.int.ifelse) pure r i

def srlFirstF64 (r : SRLF64) : JlX F64 :=
  unsafeGetindexF64 r (JuliaLean.base.int.lit .i64 1)

def srlLastF64 (r : SRLF64) : JlX F64 :=
  unsafeGetindexF64 r r.len

def srlGetF64 (r : SRLF64) (i : JInt .i64) : JlX F64 :=
  if JuliaLean.base.int.leSame (JuliaLean.base.int.lit .i64 1) i &&
      JuliaLean.base.int.leSame i r.len then
    unsafeGetindexF64 r i
  else
    .error (.jl .boundsError)

def mulTpIntegerF64 (x : TwicePrecision F64) (v : JInt .i64) : TwicePrecision F64 :=
  mulTpInteger bitOps64 f64Arithmetic (jintOps .i64) JuliaLean.base.int.top_set_bit
    (JuliaLean.base.float.floatOfInt .f64) x v
    (fun n => JuliaLean.base.int.eqSame n (JuliaLean.base.int.lit .i64 0))
    (fun a n => JuliaLean.base.float.mul_IEEEFloat a (JuliaLean.base.float.floatOfInt .f64 n))

def tpProd2F64 (t : TwicePrecision F64) (x y : JInt .i64) : TwicePrecision F64 :=
  tpProdRecursive mulTpIntegerF64
    (fun acc ys => match ys with
      | [] => tpProdBase acc
      | z :: _ => tpProdRecursive mulTpIntegerF64 (fun acc2 _ => tpProdBase acc2) acc z [])
    t x [y]

def sumStepRangeLenTwiceF64 (r : SRLF64) : F64 :=
  sumStepRangeLenTwice f64Arithmetic length_StepRangeLen (sumpair (jintOps .i64))
    JuliaLean.base.int.sub (JuliaLean.base.int.lit .i64 1)
    tpProd2F64 mulTpIntegerF64
    (add12Same f64Arithmetic JuliaLean.base.int.ifelse) r


def rangeStartStepLengthIntFloatF64 (a : JInt .i64) (st : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStartStepLengthRealFloat (fun x y => (JuliaLean.base.float.floatOfInt .f64 x, y))
    rangeStartStepLengthF64 a st len

def rangeStartStepLengthFloatIntF64 (a : F64) (st : JInt .i64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStartStepLengthFloatReal (fun x y => (x, JuliaLean.base.float.floatOfInt .f64 y))
    rangeStartStepLengthF64 a st len

def rangeStartStepLengthSameF64 (a st : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStartStepLengthFloatFloat (fun x y => (x, y)) rangeStartStepLengthF64 a st len

def rangeStepStopLengthIntFloatF64 (st : JInt .i64) (stop : F64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStepStopLengthRealFloat (fun x y => (JuliaLean.base.float.floatOfInt .f64 x, y))
    rangeStepStopLengthF64 st stop len

def rangeStepStopLengthFloatIntF64 (st : F64) (stop : JInt .i64) (len : JInt .i64) : JlX SRLF64 :=
  rangeStepStopLengthFloatReal (fun x y => (x, JuliaLean.base.float.floatOfInt .f64 y))
    rangeStepStopLengthF64 st stop len

def mulF64Tp (x : F64) (v : TwicePrecision F64) : TwicePrecision F64 :=
  if JuliaLean.base.float.iszero_float x then
    ⟨JuliaLean.base.float.mul_IEEEFloat v.hi x, JuliaLean.base.float.mul_IEEEFloat v.lo x⟩
  else mulTpF64 v (tpFromSame f64Arithmetic x)

def divTpF64Scalar (v : TwicePrecision F64) (x : F64) : TwicePrecision F64 :=
  divTpF64 v (tpFromSame f64Arithmetic x)

def nbitslenRangeF64 (r : SRLF64) : JInt .i64 :=
  nbitslenRange F64 length_StepRangeLen (fun _ len off => nbitslenF64 len off) r

def scalarMulRangeF64 (x : F64) (r : SRLF64) : JlX SRLF64 :=
  scalarMulRange mulF64Tp mulF64Tp twiceprecisionTPF64 nbitslenRangeF64
    length_StepRangeLen srlMakeTpF64 x r

def scalarMulRangeRightF64 (r : SRLF64) (x : F64) : JlX SRLF64 :=
  scalarMulRangeRight scalarMulRangeF64 r x

def scalarDivRangeF64 (r : SRLF64) (x : F64) : JlX SRLF64 :=
  scalarDivRange divTpF64Scalar divTpF64Scalar twiceprecisionTPF64 nbitslenRangeF64
    length_StepRangeLen srlMakeTpF64 r x

def getindexHiprecF64 {I : Type} (isBool : I → Bool) (showIndex : I → String)
    (oftype : JInt .i64 → I → JlX (JInt .i64)) (r : SRLF64) (i : I) : JlX (TwicePrecision F64) :=
  getindexHiprec isBool showIndex oftype JuliaLean.base.int.sub
    (fun u s => JuliaLean.base.float.mul_IEEEFloat (JuliaLean.base.float.floatOfInt .f64 u) s)
    JuliaLean.base.float.add_IEEEFloat (add12Same f64Arithmetic JuliaLean.base.int.ifelse) r i

def roundHalfI64 (a b : JInt .i64) : JInt .i64 :=
  let s := JuliaLean.base.int.add a b
  let two := JuliaLean.base.float.floatOfInt .f64 (JuliaLean.base.int.lit .i64 2)
  let q := JuliaLean.base.float.div_IEEEFloat (JuliaLean.base.float.floatOfInt .f64 s) two
  match roundIntF64 q with
  | .ok m => m
  | .error _ => a

def addStepRangeLenF64 (r1 r2 : SRLF64) : JlX SRLF64 :=
  addStepRangeLen (jintArith .i64) length_StepRangeLen length_StepRangeLen
    (addTpSame f64Arithmetic)
    (getindexHiprecF64 (fun _ : JInt .i64 => false) (fun _ => "") (fun _ i => .ok i))
    roundHalfI64
    (fun x nb => twiceprecisionTPF64 x (JuliaLean.base.int.lit .i64 nb))
    (fun _ l o => (nbitslenF64 l o).val.toNat)
    srlMakeTpF64 r1 r2

def sumStepRangeLenInt (t : IntTy) (r : StepRangeLen (JInt t) (JInt t) (JInt t) (JInt .i64)) :
    JlX (JInt t) :=
  sumStepRangeLen length_StepRangeLen (sumpair (jintOps .i64))
    JuliaLean.base.int.sub (JuliaLean.base.int.lit .i64 1)
    (JuliaLean.base.int.widenTo .i128)
    JuliaLean.base.int.mulSame JuliaLean.base.int.sub
    (fun s dn => JuliaLean.base.int.mulSame (JuliaLean.base.int.widenTo .i128 s) dn)
    (fun rf l => JuliaLean.base.int.mulSame (JuliaLean.base.int.widenTo .i128 rf)
      (JuliaLean.base.int.widenTo .i128 l))
    JuliaLean.base.int.add
    (fun v => liftJl (JuliaLean.base.int.convert t v)) r

end JuliaLean.base.twiceprecision
