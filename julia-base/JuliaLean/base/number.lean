import JuliaLean.Core

/-!
# Model of `base/number.jl`

Each method is a typed function over the concrete value types that Julia dispatch selects. Calls to
other generic or user-extensible functions are typed parameters; Julia's dispatch is trusted.
-/

namespace JuliaLean.base.number

open JuliaLean

/--
Julia source: base/number.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T)      where {T<:Number} = x
```
-/
def convertSame {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::Number) where {T<:Number} = T(x)::T
```
-/
def convertNumber {α β : Type} (convert : α → Jl β) (x : α) : Jl β := convert x

/--
Julia source: base/number.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinteger(x::Integer) = true
```
-/
def isintegerInteger {α : Type} (_x : α) : Bool := true

/--
Julia source: base/number.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x) = x == zero(x) # fallback method
```
-/
def iszero {α : Type} (zero : α → Jl α) (equal : α → α → Jl Bool) (x : α) : Jl Bool := do
  let z ← zero x
  equal x z

/--
Julia source: base/number.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(x) = x == one(x) # fallback method
```
-/
def isone {α : Type} (one : α → Jl α) (equal : α → α → Jl Bool) (x : α) : Jl Bool := do
  let o ← one x
  equal x o

/--
Julia source: base/number.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite(x::Number) = iszero(x - x)
```
-/
def isfinite {α : Type} (iszero : α → Jl Bool) (sub : α → α → Jl α) (x : α) : Jl Bool := do
  let difference ← sub x x
  iszero difference

/--
Julia source: base/number.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(x::Number) = ()
```
-/
def size {α : Type} (_x : α) : Unit := ()

/--
Julia source: base/number.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(x::Number, d::Integer) = d < 1 ? throw(BoundsError()) : 1
```
-/
def sizeDim {α δ : Type} (lessThanOne : δ → Jl Bool) (_x : α) (d : δ) : Jl JInt64 := do
  let invalid ← lessThanOne d
  if invalid then throw .boundsError else pure (JInt.lit .i64 1)

/--
Julia source: base/number.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(x::Number) = ()
```
-/
def axes {α : Type} (_x : α) : Unit := ()

/--
Julia source: base/number.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(x::Number, d::Integer) = d < 1 ? throw(BoundsError()) : OneTo(1)
```
-/
def axesDim {α δ β : Type} (lessThanOne : δ → Jl Bool) (oneTo : JInt64 → Jl β)
    (_x : α) (d : δ) : Jl β := do
  let invalid ← lessThanOne d
  if invalid then throw .boundsError else oneTo (JInt.lit .i64 1)

/--
Julia source: base/number.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{T}) where {T<:Number} = T
```
-/
def eltype {α : Type} (tag : α) : α := tag

/--
Julia source: base/number.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(x::Number) = 0
```
-/
def ndimsValue {α : Type} (_x : α) : JInt64 := JInt.lit .i64 0

/--
Julia source: base/number.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::Type{<:Number}) = 0
```
-/
def ndimsType {α : Type} (_tag : α) : JInt64 := JInt.lit .i64 0

/--
Julia source: base/number.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(x::Number) = 1
```
-/
def length {α : Type} (_x : α) : JInt64 := JInt.lit .i64 1

/--
Julia source: base/number.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(x::Number) = 1
```
-/
def firstindex {α : Type} (_x : α) : JInt64 := JInt.lit .i64 1

/--
Julia source: base/number.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(x::Number, d::Int) = d < 1 ? throw(BoundsError()) : 1
```
-/
def firstindexDim {α : Type} (_x : α) (d : JInt64) : Jl JInt64 :=
  if d.val < 1 then .error .boundsError else .ok (JInt.lit .i64 1)

/--
Julia source: base/number.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(x::Number) = 1
```
-/
def lastindex {α : Type} (_x : α) : JInt64 := JInt.lit .i64 1

/--
Julia source: base/number.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(x::Number, d::Int) = d < 1 ? throw(BoundsError()) : 1
```
-/
def lastindexDim {α : Type} (_x : α) (d : JInt64) : Jl JInt64 :=
  if d.val < 1 then .error .boundsError else .ok (JInt.lit .i64 1)

/--
Julia source: base/number.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Number}) = HasShape{0}()
```
-/
def iteratorSize {α β : Type} (_tag : α) (hasShapeZero : Unit → β) : β := hasShapeZero ()

/--
Julia source: base/number.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(::Number) = OneTo(1)
```
-/
def keys {α β : Type} (_x : α) (oneTo : JInt64 → β) : β := oneTo (JInt.lit .i64 1)

/--
Julia source: base/number.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(x::Number) = x
```
-/
def getindex0 {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:102-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(x::Number, i::Integer)
    @inline
    @boundscheck i == 1 || throw(BoundsError(x, i))
    x
end
```
-/
def getindexOne {α β : Type} (equalOne : β → Jl Bool) (x : α) (i : β) : Jl α := do
  let valid ← equalOne i
  if valid then pure x else throw .boundsError

/--
Julia source: base/number.jl:107-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(x::Number, I::Integer...)
    @inline
    @boundscheck all(isone, I) || throw(BoundsError(x, I))
    x
end
```
-/
def getindexMany {α β γ : Type} (all : (β → Jl Bool) → γ → Jl Bool)
    (isone : β → Jl Bool) (x : α) (indices : γ) : Jl α := do
  let valid ← all isone indices
  if valid then pure x else throw .boundsError

/--
Julia source: base/number.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(x::Number, i::Integer, default) = isone(i) ? x : default
```
-/
def getDefaultIndex {α β : Type} (isOne : β → Jl Bool) (x default : α) (i : β) : Jl α := do
  let valid ← isOne i
  pure (if valid then x else default)

/--
Julia source: base/number.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(x::Number, ind::Tuple, default) = all(isone, ind) ? x : default
```
-/
def getDefaultTuple {α β γ : Type} (all : (β → Jl Bool) → γ → Jl Bool)
    (isone : β → Jl Bool) (x default : α) (indices : γ) : Jl α := do
  let valid ← all isone indices
  pure (if valid then x else default)

/--
Julia source: base/number.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, x::Number, i::Integer) = isone(i) ? x : f()
```
-/
def getThunkIndex {α β : Type} (isOne : β → Jl Bool) (f : Unit → Jl α) (x : α) (i : β) : Jl α := do
  let valid ← isOne i
  if valid then pure x else f ()

/--
Julia source: base/number.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, x::Number, ind::Tuple) = all(isone, ind) ? x : f()
```
-/
def getThunkTuple {α β γ : Type} (all : (β → Jl Bool) → γ → Jl Bool)
    (isone : β → Jl Bool) (f : Unit → Jl α) (x : α) (indices : γ) : Jl α := do
  let valid ← all isone indices
  if valid then pure x else f ()

/--
Julia source: base/number.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(x::Number) = x
```
-/
def first {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(x::Number) = x
```
-/
def last {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(x::Number) = x # some code treats numbers as collection-like
```
-/
def copy {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Real) = x < 0
```
-/
def signbit {α : Type} (lessThanZero : α → Jl Bool) (x : α) : Jl Bool := lessThanZero x

/--
Julia source: base/number.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispositive(x::Real) = x > 0
```
-/
def ispositive {α : Type} (greaterThanZero : α → Jl Bool) (x : α) : Jl Bool := greaterThanZero x

/--
Julia source: base/number.jl:187-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnegative(x::Real) = x < 0
```
-/
def isnegative {α : Type} (lessThanZero : α → Jl Bool) (x : α) : Jl Bool := lessThanZero x

/--
Julia source: base/number.jl:211-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::Number) = iszero(x) ? x/abs(oneunit(x)) : x/abs(x)
```
-/
def signNumber {α β γ : Type} (iszero : α → Jl Bool) (oneunit : α → Jl α)
    (abs : α → Jl β) (divide : α → β → Jl γ) (x : α) : Jl γ := do
  let isZero ← iszero x
  if isZero then do
    let unit ← oneunit x
    let magnitude ← abs unit
    divide x magnitude
  else do
    let magnitude ← abs x
    divide x magnitude

/--
Julia source: base/number.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::Real) = ifelse(x < zero(x), oftype(one(x),-1), ifelse(x > zero(x), one(x), typeof(one(x))(x)))
```
-/
def signReal {α : Type} (zero : α → Jl α) (less greater : α → α → Jl Bool)
    (one : α → Jl α) (oftype : α → Int → Jl α) (constructLike : α → α → Jl α)
    (ifelse : Bool → α → α → α) (x : α) : Jl α := do
  let zeroForLess ← zero x
  let isNegative ← less x zeroForLess
  let oneForNegative ← one x
  let negativeOne ← oftype oneForNegative (-1)
  let zeroForGreater ← zero x
  let isPositive ← greater x zeroForGreater
  let oneForPositive ← one x
  let oneForCast ← one x
  let castValue ← constructLike oneForCast x
  pure (ifelse isNegative negativeOne (ifelse isPositive oneForPositive castValue))

/--
Julia source: base/number.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::Unsigned) = ifelse(x > zero(x), one(x), oftype(one(x),0))
```
-/
def signUnsigned {α : Type} (zero : α → Jl α) (greater : α → α → Jl Bool)
    (one : α → Jl α) (oftype : α → Int → Jl α) (ifelse : Bool → α → α → α)
    (x : α) : Jl α := do
  let zeroValue ← zero x
  let isPositive ← greater x zeroValue
  let oneForPositive ← one x
  let oneForZero ← one x
  let zeroOfType ← oftype oneForZero 0
  pure (ifelse isPositive oneForPositive zeroOfType)

/--
Julia source: base/number.jl:214-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Real) = ifelse(signbit(x), -x, x)
```
-/
def absReal {α : Type} (signbit : α → Jl Bool) (negate : α → Jl α)
    (ifelse : Bool → α → α → α) (x : α) : Jl α := do
  let negative ← signbit x
  let negated ← negate x
  pure (ifelse negative negated x)

/--
Julia source: base/number.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs2(x::Number) = abs(x)^2
```
-/
def abs2Number {α β γ : Type} (abs : α → Jl β) (power : β → Int → Jl γ) (x : α) : Jl γ := do
  let magnitude ← abs x
  power magnitude 2

/--
Julia source: base/number.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs2(x::Real) = x*x
```
-/
def abs2Real {α β : Type} (multiply : α → α → Jl β) (x : α) : Jl β := multiply x x

/--
Julia source: base/number.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Real, y::Real) = ifelse(signbit(y), -x, +x) # the + is for type-stability on Bool
```
-/
def flipsign {α β γ : Type} (signbit : β → Jl Bool) (negate positive : α → Jl γ)
    (ifelse : Bool → γ → γ → γ) (x : α) (y : β) : Jl γ := do
  let negative ← signbit y
  let negated ← negate x
  let unchanged ← positive x
  pure (ifelse negative negated unchanged)

/--
Julia source: base/number.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Real, y::Real) = ifelse(signbit(x)!=signbit(y), -x, +x)
```
-/
def copysign {α β γ : Type} (signbitX : α → Jl Bool) (signbitY : β → Jl Bool)
    (negate positive : α → Jl γ) (ifelse : Bool → γ → γ → γ) (x : α) (y : β) : Jl γ := do
  let xNegative ← signbitX x
  let yNegative ← signbitY y
  let signsDiffer := decide (xNegative ≠ yNegative)
  let negated ← negate x
  let unchanged ← positive x
  pure (ifelse signsDiffer negated unchanged)

/--
Julia source: base/number.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
conj(x::Real) = x
```
-/
def conj {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transpose(x::Number) = x
```
-/
def transpose {α : Type} (x : α) : α := x

/--
Julia source: base/number.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
adjoint(x::Number) = conj(x)
```
-/
def adjoint {α β : Type} (conj : α → Jl β) (x : α) : Jl β := conj x

/--
Julia source: base/number.jl:276-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
angle(z::Real) = atan(zero(z), z)
```
-/
def angle {α β : Type} (zero : α → Jl α) (atan : α → α → Jl β) (z : α) : Jl β := do
  let zzero ← zero z
  atan zzero z

/--
Julia source: base/number.jl:305-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inv(x::Number) = one(x)/x
```
-/
def inv {α β γ : Type} (one : α → Jl β) (divide : β → α → Jl γ) (x : α) : Jl γ := do
  let identity ← one x
  divide identity x

/--
Julia source: base/number.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Number, y::Number) = widen(x)*widen(y)
```
-/
def widemul {α β γ δ ε : Type} (widenX : α → Jl β) (widenY : γ → Jl δ)
    (multiply : β → δ → Jl ε) (x : α) (y : γ) : Jl ε := do
  let wideX ← widenX x
  let wideY ← widenY y
  multiply wideX wideY

/--
Julia source: base/number.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(x::Number) = (x, nothing)
```
-/
def iterate {α : Type} (x : α) : Option (α × Option Unit) := some (x, none)

/--
Julia source: base/number.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(x::Number, ::Any) = nothing
```
-/
def iterateNext {α σ : Type} (_x : α) (_state : σ) : Option (α × Option Unit) := none

/--
Julia source: base/number.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(x::Number) = false
```
-/
def isempty {α : Type} (_x : α) : Bool := false

/--
Julia source: base/number.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::Number, y::Number) = x == y
```
-/
def inNumber {α β : Type} (equal : α → β → Jl Bool) (x : α) (y : β) : Jl Bool := equal x y

/--
Julia source: base/number.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, x::Number, ys::Number...) = f(x, ys...)
```
-/
def map {α Args γ : Type} (applySplat : α → Args → Jl γ) (x : α) (ys : Args) : Jl γ :=
  applySplat x ys

/--
Julia source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::Number) = oftype(x,0)
```
-/
def zeroValue {α : Type} (oftype : α → Int → Jl α) (x : α) : Jl α := oftype x 0

/--
Julia source: base/number.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(::Type{T}) where {T<:Number} = convert(T,0)
```
-/
def zeroType {α β : Type} (convert : α → Int → Jl β) (tag : α) : Jl β := convert tag 0

/--
Julia source: base/number.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(::Type{Union{}}, slurp...) = Union{}(0)
```
-/
def zeroBottom {α β : Type} (constructBottom : Int → Jl α) (_slurp : List β) : Jl α :=
  constructBottom 0

/--
Julia source: base/number.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(::Type{T}) where {T<:Number} = convert(T,1)
```
-/
def oneType {α β : Type} (convert : α → Int → Jl β) (tag : α) : Jl β := convert tag 1

/--
Julia source: base/number.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(x::T) where {T<:Number} = one(T)
```
-/
def oneValue {α β : Type} (typeOf : β → α) (oneType : α → Jl β) (x : β) : Jl β :=
  oneType (typeOf x)

/--
Julia source: base/number.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(::Type{Union{}}, slurp...) = Union{}(1)
```
-/
def oneBottom {α β : Type} (constructBottom : Int → Jl α) (_slurp : List β) : Jl α :=
  constructBottom 1

/--
Julia source: base/number.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(x::T) where {T} = T(one(x))
```
-/
def oneunitValue {α β : Type} (one : α → Jl β) (constructT : β → Jl α) (x : α) : Jl α := do
  let value ← one x
  constructT value

/--
Julia source: base/number.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(::Type{T}) where {T} = T(one(T))
```
-/
def oneunitType {α β γ : Type} (oneType : α → Jl β) (constructT : β → Jl γ)
    (tag : α) : Jl γ := do
  let value ← oneType tag
  constructT value

/--
Julia source: base/number.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(::Type{Union{}}, slurp...) = Union{}(1)
```
-/
def oneunitBottom {α β : Type} (constructBottom : Int → Jl α) (_slurp : List β) : Jl α :=
  constructBottom 1

/--
Julia source: base/number.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(::Type{T}) where {T<:Number} = typeof(big(zero(T)))
```
-/
def bigType {α β γ δ : Type} (zero : α → Jl β) (big : β → Jl γ)
    (typeOf : γ → δ) (tag : α) : Jl δ := do
  let zeroValue ← zero tag
  let bigValue ← big zeroValue
  pure (typeOf bigValue)

/--
Julia source: base/number.jl:453-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(::Type{Union{}}, slurp...) = Union{}(0)
```
-/
def bigBottom {α β : Type} (constructBottom : Int → Jl α) (_slurp : List β) : Jl α :=
  constructBottom 0

end JuliaLean.base.number
