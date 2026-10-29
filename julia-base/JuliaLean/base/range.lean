import JuliaLean.Core

/-!
# `base/range.jl`

A typed, source-mirrored model of `base/range.jl` at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Every Julia method is one Lean definition named
`<juliaName>_<shortSignature>` (operators spelled `colon`, `eq`, `neg`, `plus`, `minus`), preceded
by its verbatim source. The body follows the Julia body statement by statement: the same `let`s,
branches, early returns, checks, calls and errors, in the same order. Nested functions
(`throwbool`, `overflow_case`, ...) are separate definitions named `<enclosing>.<name>`.

* Exceptions. A Julia exception is an `Exc`: a `JlError` from `JuliaLean.Core`
  (`ArgumentError`, `BoundsError`, `InexactError`, `OverflowError`, `DomainError`, ...), an
  `ErrorException` from `error(msg)`, or a `DimensionMismatch`. Messages are the strings Julia
  builds; `DomainError(val, msg)` keeps only `msg`. A call that may throw returns
  `JlX α = Except Exc α`.
* Interface classes. Julia's dispatch is trusted and is not modelled here: this file has no
  instances for range types or numbers. Every call to a generic function that has several
  methods, is defined in a later file (range.jl loads before number.jl, int.jl, float.jl,
  show.jl, twiceprecision.jl, ...), or is extended by users is a call to a method of a class,
  one class per Julia generic function and arity (`JFirst` is `first(r)`, `JColon3` is
  `(:)(a, s, b)`, `JStepRangeTS3` is `StepRange{T,S}(a, s, b)`). Result types are `outParam`s,
  so the argument types determine them, as in Julia; constructors whose Julia signature fixes
  the result type (`StepRange{T,S}(...)`) have that result type. A body calls another
  definition of this file directly only when that callee is an internal helper with a single
  method (`steprange_last`, `_empty_stop`, `lerpi`, the `range_*` helpers, ...).
* Pure and `JlX`. `+`, `-`, `*`, `/` are Lean's `HAdd`, `HSub`, `HMul`, `HDiv`; comparisons
  (`JEq` is `==`, `JLt` is `<`, `JLe` is `<=`, `a > b` is `b < a`), predicates (`JIszero`,
  ...), constants (`JZero`, `JOneunit`, ...) and type tests (`JType`) are pure. Everything that
  can throw for a Base type (`convert`, `oftype`, `T(x)`, `div`, `mod`, `checked_add`, `max`,
  `promote`, every range constructor and every range generic function) returns `JlX`.
  Arithmetic on two `Int` values uses `JuliaLean.Core`'s `JInt` operations (the `int.jl`
  intrinsics). Bool operands of `&`, `|`, `!`, `⊻` use Lean's `Bool` operations.
* Types. A Julia type parameter is a Lean type variable. Argument type annotations only select
  methods (dispatch), so they are not repeated as constraints. `T === Bool`, `x isa Signed`,
  `T <: Integer` are fields of `JType`; `JType.bool_eq` turns a `T === Bool` test into the type
  equality Julia's branch relies on. When a variable or a result has a type that depends on the
  branch taken for Base argument types, it is a sum `α ⊕ β` in branch order, and later calls
  take the sum (dispatch then acts on the runtime type). When Julia's branch types coincide for
  every Base type (for example `s = -s`), the model requires them to be equal.
* Calls. Nested calls are evaluated left to right, as in Julia. `&&`, `||` and chained
  comparisons short-circuit; `&` and `|` evaluate both operands. Omitted optional positional
  arguments are written out with their default value; a method with a default argument also
  has the generated shorter method, preceded by the same source. Keyword arguments are passed
  positionally, with `nothing` for omitted ones. Julia's `new` converts its arguments to the
  field types; the model inserts `convert` where the types differ.
* Values. Julia's `Int` is `JInt64`; `nothing` is `Nothing.nothing`; a tuple of one element
  type and a `Vector` are `List`s; `show`/`print` methods return the text written to the
  `IO`.
* Loops. A loop over a `List` is Lean's `for`. A loop over a range follows Julia's iteration
  protocol (`iterate`) for at most `fuel` steps; `fuel` is an explicit argument, sufficient
  when it is at least the number of elements, and running out of fuel returns
  `.error (.errorException "fuel")`.
-/

set_option linter.unusedVariables false

namespace JuliaLean.base.range

open JuliaLean

/-- A Julia exception thrown by a range method. -/
inductive Exc where
  | jl (e : JlError)
  | errorException (msg : String)
  | dimensionMismatch (msg : String)
  /-- An `@inbounds` access outside the array: undefined behaviour in Julia. -/
  | inboundsViolation
  deriving DecidableEq, Repr

/-- A Julia computation that may throw. -/
abbrev JlX (α : Type) := Except Exc α

/-- The `Int` literal `n`. -/
def jint (n : Int) : JInt64 := JInt.lit .i64 n

/-- `nothing`, the only value of type `Nothing`. -/
inductive Nothing where
  | nothing
  deriving DecidableEq, Repr

/-- `Colon()`, the value of `:` used as an index. -/
structure Colon where
  deriving DecidableEq, Repr

/-- An `IO` stream. A `show` model returns the text it writes to the stream. -/
structure JIO where
  deriving DecidableEq, Repr

/-- `IOContext(io, :typeinfo => T)`. -/
structure IOTypeinfo (T : Type) where
  io : JIO

/-- A one-element tuple `(x,)`. -/
structure Tuple1 (α : Type) where
  _1 : α
  deriving DecidableEq, Repr

/-- The traits `Ordered()` and `ArithmeticRounds()` (traits.jl) and the range step styles. -/
structure Ordered where
structure ArithmeticRounds where
structure RangeStepRegular where
structure RangeStepIrregular where

/-- The operators `+` and `-` that `_define_range_op` generates methods for. -/
structure PlusOp where
structure MinusOp where



/-! ## Range types -/

/--
Julia source: base/range.jl:289-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

## ordinal ranges

"""
    OrdinalRange{T, S} <: AbstractRange{T}

Supertype for ordinal ranges with elements of type `T` with
spacing(s) of type `S`. The steps should be always-exact
multiples of [`oneunit`](@ref), and `T` should be a "discrete"
type, which cannot have values smaller than `oneunit`. For example,
`Integer` or `Date` types would qualify, whereas `Float64` would not (since this
type can represent values smaller than `oneunit(Float64)`.
[`UnitRange`](@ref), [`StepRange`](@ref), and other types are subtypes of this.
"""
abstract type OrdinalRange{T,S} <: AbstractRange{T} end

"""
    AbstractUnitRange{T} <: OrdinalRange{T, T}

Supertype for ranges with a step size of [`oneunit(T)`](@ref) with elements of type `T`.
[`UnitRange`](@ref) and other types are subtypes of this.
"""
abstract type AbstractUnitRange{T} <: OrdinalRange{T,T} end

"""
    StepRange{T, S} <: OrdinalRange{T, S}

Ranges with elements of type `T` with spacing of type `S`. The step
between each element is constant, and the range is defined in terms
of a `start` and `stop` of type `T` and a `step` of type `S`. Neither
`T` nor `S` should be floating point types. The syntax `a:b:c` with `b != 0`
and `a`, `b`, and `c` all integers creates a `StepRange`.

# Examples
```jldoctest
julia> collect(StepRange(1, Int8(2), 10))
5-element Vector{Int64}:
 1
 3
 5
 7
 9

julia> typeof(StepRange(1, Int8(2), 10))
StepRange{Int64, Int8}

julia> typeof(1:3:6)
StepRange{Int64, Int64}
```
"""
struct StepRange{T,S} <: OrdinalRange{T,S}
    start::T
    step::S
    stop::T

````
-/
structure StepRange (T S : Type) where
  start : T
  step : S
  stop : T
  deriving DecidableEq, Repr

/--
Julia source: base/range.jl:405-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    UnitRange{T<:Real}

A range parameterized by a `start` and `stop` of type `T`, filled
with elements spaced by `1` from `start` until `stop` is exceeded.
The syntax `a:b` with `a` and `b` both `Integer`s creates a `UnitRange`.

# Examples
```jldoctest
julia> collect(UnitRange(2.3, 5.2))
3-element Vector{Float64}:
 2.3
 3.3
 4.3

julia> typeof(1:10)
UnitRange{Int64}
```
"""
struct UnitRange{T<:Real} <: AbstractUnitRange{T}
    start::T
    stop::T
````
-/
structure UnitRange (T : Type) where
  start : T
  stop : T
  deriving DecidableEq, Repr

/--
Julia source: base/range.jl:467-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    Base.AbstractOneTo

Abstract type for ranges that start at 1 and have a step size of 1.

!!! compat "Julia 1.13"
    This type requires at least Julia 1.13.
"""
abstract type AbstractOneTo{T} <: AbstractUnitRange{T} end

"""
    Base.OneTo(n)

Define an `AbstractUnitRange` that behaves like `1:n`, with the added
distinction that the lower limit is guaranteed (by the type system) to
be 1.
"""
struct OneTo{T<:Integer} <: AbstractOneTo{T}
    stop::T # invariant: stop >= zero(stop)
```
-/
structure OneTo (T : Type) where
  stop : T
  deriving DecidableEq, Repr

/--
Julia source: base/range.jl:508-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Step ranges parameterized by length

"""
    StepRangeLen(         ref::R, step::S, len, [offset=1]) where {  R,S}
    StepRangeLen{T,R,S}(  ref::R, step::S, len, [offset=1]) where {T,R,S}
    StepRangeLen{T,R,S,L}(ref::R, step::S, len, [offset=1]) where {T,R,S,L}

A range `r` where `r[i]` produces values of type `T` (in the first
form, `T` is deduced automatically), parameterized by a `ref`erence
value, a `step`, and the `len`gth. By default `ref` is the starting
value `r[1]`, but alternatively you can supply it as the value of
`r[offset]` for some other index `1 <= offset <= len`. The syntax `a:b`
or `a:b:c`, where any of `a`, `b`, or `c` are floating-point numbers, creates a
`StepRangeLen`.

!!! compat "Julia 1.7"
    The 4th type parameter `L` requires at least Julia 1.7.
"""
struct StepRangeLen{T,R,S,L<:Integer} <: AbstractRange{T}
    ref::R       # reference value (might be smallest-magnitude value in the range)
    step::S      # step value
    len::L       # length of the range
    offset::L    # the index of ref

```
-/
structure StepRangeLen (T R S L : Type) where
  ref : R
  step : S
  len : L
  offset : L
  deriving DecidableEq, Repr

/--
Julia source: base/range.jl:552-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

## range with computed step

"""
    LinRange{T,L}

A range with `len` linearly spaced elements between its `start` and `stop`.
The size of the spacing is controlled by `len`, which must
be an `Integer`.

# Examples
```jldoctest
julia> LinRange(1.5, 5.5, 9)
9-element LinRange{Float64, Int64}:
 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5
```

Compared to using [`range`](@ref), directly constructing a `LinRange` should
have less overhead but won't try to correct for floating point errors:
```jldoctest
julia> collect(range(-0.1, 0.3, length=5))
5-element Vector{Float64}:
 -0.1
  0.0
  0.1
  0.2
  0.3

julia> collect(LinRange(-0.1, 0.3, 5))
5-element Vector{Float64}:
 -0.1
 -1.3877787807814457e-17
  0.09999999999999999
  0.19999999999999998
  0.3
```

See also [`Base.LogRange`](@ref Base.LogRange) for logarithmically spaced points.
"""
struct LinRange{T,L<:Integer} <: AbstractRange{T}
    start::T
    stop::T
    len::L
    lendiv::L

````
-/
structure LinRange (T L : Type) where
  start : T
  stop : T
  len : L
  lendiv : L
  deriving DecidableEq, Repr

/--
Julia source: base/range.jl:1604-1659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia


"""
    LogRange{T}(start, stop, len) <: AbstractVector{T}

A range whose elements are spaced logarithmically between `start` and `stop`,
with spacing controlled by `len`. Returned by [`logrange`](@ref).

Like [`LinRange`](@ref), the first and last elements will be exactly those
provided, but intermediate values may have small floating-point errors.
These are calculated using the logs of the endpoints, which are
stored on construction, often in higher precision than `T`.

# Examples
```jldoctest
julia> logrange(1, 4, length=5)
5-element Base.LogRange{Float64, Base.TwicePrecision{Float64}}:
 1.0, 1.41421, 2.0, 2.82843, 4.0

julia> Base.LogRange{Float16}(1, 4, 5)
5-element Base.LogRange{Float16, Float64}:
 1.0, 1.414, 2.0, 2.828, 4.0

julia> logrange(1e-310, 1e-300, 11)[1:2:end]
6-element Vector{Float64}:
 1.0e-310
 9.999999999999974e-309
 9.999999999999981e-307
 9.999999999999988e-305
 9.999999999999994e-303
 1.0e-300

julia> prevfloat(1e-308, 5) == ans[2]
true
```

Note that integer eltype `T` is not allowed.
Use for instance `round.(Int, xs)`, or explicit powers of some integer base:

```jldoctest
julia> xs = logrange(1, 512, 4)
4-element Base.LogRange{Float64, Base.TwicePrecision{Float64}}:
 1.0, 8.0, 64.0, 512.0

julia> 2 .^ (0:3:9) |> println
[1, 8, 64, 512]
```

!!! compat "Julia 1.11"
    This type requires at least Julia 1.11.
"""
struct LogRange{T<:Real,X} <: AbstractArray{T,1}
    start::T
    stop::T
    len::Int
    extra::Tuple{X,X}
````
-/
structure LogRange (T X : Type) where
  start : T
  stop : T
  len : JInt64
  extra : X × X


/-! ## Julia type tests and helpers -/

/-- The Julia type tests range.jl performs on a type `α`: `α === Bool`, `α <: Signed`,
`α <: Integer`, `α <: AbstractFloat`. `bool_eq` is what Julia's `T === Bool` branch relies on. -/
class JType (α : Type) where
  isBool : Bool
  isSigned : Bool
  isInteger : Bool
  isAbstractFloat : Bool
  bool_eq : isBool = true → α = Bool

/-- `x !== nothing`. -/
class JIsNothing (α : Type) where
  isNothing : α → Bool

/-- `print(io, x)`: the text string interpolation `"$x"` writes. -/
class JPrint (α : Type) where
  print : α → String

/-- `repr(x)`. -/
class JRepr (α : Type) where
  repr : α → JlX String

/-- `show(io, x)` (and `show(IOContext(io, :typeinfo => T), x)` when `T` is given). -/
class JShow (α : Type) where
  showValue : α → JlX String

/-- `show(io, T)` for a type `T` (the type is the class argument). -/
class JShowType (T : Type) where
  showType : String

/-! ## Arithmetic and comparison (defined in later files; pure for every Base number type) -/

/-- `x == y`. -/
class JEq (α β : Type) where
  eq : α → β → Bool
/-- `x < y` (`y > x` is `x < y`). -/
class JLt (α β : Type) where
  lt : α → β → Bool
/-- `x <= y` (`y >= x` is `x <= y`). -/
class JLe (α β : Type) where
  le : α → β → Bool
/-- `isless(x, y)`. -/
class JIsless (α β : Type) where
  isless : α → β → Bool
/-- `zero(x)`, `zero(T)`. -/
class JZero (α : Type) where
  zero : α
/-- `oneunit(x)`, `oneunit(T)`. -/
class JOneunit (α : Type) where
  oneunit : α
/-- `one(x)`, `one(T)`. -/
class JOne (α : Type) where
  one : α
/-- `iszero(x)`. -/
class JIszero (α : Type) where
  iszero : α → Bool
/-- `isone(x)`. -/
class JIsone (α : Type) where
  isone : α → Bool
/-- `iseven(x)`. -/
class JIseven (α : Type) where
  iseven : α → Bool
/-- `isinteger(x)`. -/
class JIsinteger (α : Type) where
  isinteger : α → Bool
/-- `isfinite(x)`. -/
class JIsfinite (α : Type) where
  isfinite : α → Bool
/-- Unary `-x`. -/
class JNeg (α : Type) (β : outParam Type) where
  neg : α → β
/-- Unary `+x`. -/
class JPos (α : Type) (β : outParam Type) where
  pos : α → β
/-- `negate(x)` (int.jl): `-x`, and `-convert(Signed, x)` for unsigned `x`. -/
class JNegate (α : Type) (β : outParam Type) where
  negate : α → JlX β
/-- `x +% y`. -/
class JWrappingAdd (α β : Type) (γ : outParam Type) where
  wrappingAdd : α → β → γ
/-- `x -% y`. -/
class JWrappingSub (α β : Type) (γ : outParam Type) where
  wrappingSub : α → β → γ
/-- `x *% y`. -/
class JWrappingMul (α β : Type) (γ : outParam Type) where
  wrappingMul : α → β → γ
/-- `unsigned(x)`. -/
class JUnsigned (α : Type) (β : outParam Type) where
  unsigned : α → β
/-- `flipsign(x, y)`. -/
class JFlipsign (α β : Type) where
  flipsign : α → β → α
/-- `widemul(x, y)`. -/
class JWidemul (α β : Type) (γ : outParam Type) where
  widemul : α → β → γ
/-- `x >> n`. -/
class JShr (α β : Type) (γ : outParam Type) where
  shr : α → β → γ
/-- `x ⊻ y`. -/
class JXor (α β : Type) (γ : outParam Type) where
  xor : α → β → γ
/-- `ifelse(c, x, y)` on `Bool` operands of `&`. -/
class JAnd (α β : Type) (γ : outParam Type) where
  and : α → β → γ

/-! ## Functions that can throw for some Base type -/

/-- `convert(T, x)`; also `oftype(y::T, x)` and `x::T` return-type conversion. -/
class JConvert (T α : Type) where
  convert : α → JlX T
/-- The constructor call `T(x)`. -/
class JCtor (T α : Type) where
  ctor : α → JlX T
/-- `convert(Integer, x)`. -/
class JConvertInteger (α : Type) (β : outParam Type) where
  convertInteger : α → JlX β
/-- `Integer(x)`. -/
class JInteger (α : Type) (β : outParam Type) where
  integer : α → JlX β
/-- `promote(a, b)`. -/
class JPromote2 (α β : Type) (γ : outParam Type) where
  promote : α → β → JlX (γ × γ)
/-- `promote(a, b, c)`. -/
class JPromote3 (α β δ : Type) (γ : outParam Type) where
  promote : α → β → δ → JlX (γ × γ × γ)
/-- `promote_type(A, B)`: a type-level function, no runtime behaviour. -/
class JPromoteType (α β : Type) (γ : outParam Type) where
/-- `float(T)`: a type-level function. -/
class JFloatType (α : Type) (β : outParam Type) where
/-- `div(x, y)`. -/
class JDiv (α β : Type) (γ : outParam Type) where
  div : α → β → JlX γ
/-- `x % y`, `rem(x, y)`. -/
class JRem (α β : Type) (γ : outParam Type) where
  rem : α → β → JlX γ
/-- `mod(x, y)`. -/
class JMod (α β : Type) (γ : outParam Type) where
  mod : α → β → JlX γ
/-- `mod1(x, y)`. -/
class JMod1 (α β : Type) (γ : outParam Type) where
  mod1 : α → β → JlX γ
/-- `fld(x, y)`. -/
class JFld (α β : Type) (γ : outParam Type) where
  fld : α → β → JlX γ
/-- `cld(x, y)`. -/
class JCld (α β : Type) (γ : outParam Type) where
  cld : α → β → JlX γ
/-- `checked_add(x, y)`. -/
class JCheckedAdd (α β : Type) (γ : outParam Type) where
  checkedAdd : α → β → JlX γ
/-- `checked_sub(x, y)`. -/
class JCheckedSub (α β : Type) (γ : outParam Type) where
  checkedSub : α → β → JlX γ
/-- `min(x, y)`. -/
class JMin (α β : Type) (γ : outParam Type) where
  min : α → β → JlX γ
/-- `max(x, y)`. -/
class JMax (α β : Type) (γ : outParam Type) where
  max : α → β → JlX γ
/-- `floor(x)`. -/
class JFloor (α : Type) (β : outParam Type) where
  floor : α → JlX β
/-- `round(Integer, x)`. -/
class JRoundInteger (α : Type) (β : outParam Type) where
  roundInteger : α → JlX β
/-- `round(L, x)` for an integer type `L`. -/
class JRoundTo (L α : Type) where
  roundTo : α → JlX L
/-- `lcm(x, y)`. -/
class JLcm (α β : Type) (γ : outParam Type) where
  lcm : α → β → JlX γ
/-- `gcdx(x, y)`. -/
class JGcdx (α β : Type) (γ : outParam Type) where
  gcdx : α → β → JlX (γ × γ × γ)
/-- `log(x)`. -/
class JLog (α : Type) (β : outParam Type) where
  log : α → JlX β
/-- `_log_twice64_unchecked(x)` (twiceprecision.jl). -/
class JLogTwice64 (α : Type) (β : outParam Type) where
  logTwice64 : α → JlX β
/-- `_exp_allowing_twice64(x)` (twiceprecision.jl). -/
class JExpTwice64 (α : Type) (β : outParam Type) where
  expTwice64 : α → JlX β
/-- `x / y` when it can throw (for `TwicePrecision` and integer `len-1`). -/
class JSlash (α β : Type) (γ : outParam Type) where
  slash : α → β → JlX γ


/-! ## Range generic functions and constructors called through dispatch -/

/-- `(:)(a, b)`. -/
class JColon2 (α β : Type) (ρ : outParam Type) where
  colon : α → β → JlX ρ
/-- `(:)(a, s, b)`. -/
class JColon3 (α σ β : Type) (ρ : outParam Type) where
  colon : α → σ → β → JlX ρ
/-- `OrderStyle(T)` (traits.jl). -/
class JOrderStyle (T : Type) (σ : outParam Type) where
  orderStyle : σ
/-- `ArithmeticStyle(T)` (traits.jl). -/
class JArithmeticStyle (T : Type) (σ : outParam Type) where
  arithmeticStyle : σ
/-- `_colon(order, arithmetic, start, step, stop)`. -/
class JColonStyle (O A α σ β : Type) (ρ : outParam Type) where
  colonStyle : O → A → α → σ → β → JlX ρ
/-- `_range_wrapping_add(x, y)`. -/
class JRangeWrappingAdd (α β : Type) (γ : outParam Type) where
  rangeWrappingAdd : α → β → γ
/-- `_range_wrapping_sub(x, y)`. -/
class JRangeWrappingSub (α β : Type) (γ : outParam Type) where
  rangeWrappingSub : α → β → γ
/-- `_range_wrapping_mul(x, y)`. -/
class JRangeWrappingMul (α β : Type) (γ : outParam Type) where
  rangeWrappingMul : α → β → γ
/-- `_range(start, step, stop, len)`. -/
class JRangeImpl (α σ β Λ : Type) (ρ : outParam Type) where
  rangeImpl : α → σ → β → Λ → JlX ρ
/-- `range_stop(stop)`. -/
class JRangeStop (β : Type) (ρ : outParam Type) where
  rangeStop : β → JlX ρ
/-- `range_start_stop_length(start, stop, len)`. -/
class JRangeStartStopLength (α β Λ : Type) (ρ : outParam Type) where
  rangeStartStopLength : α → β → Λ → JlX ρ
/-- `_linspace(T, start, stop, len)`. -/
class JLinspace (T α β Λ : Type) (ρ : outParam Type) where
  linspace : α → β → Λ → JlX ρ
/-- `steprange_last_empty(start, step, stop)`. -/
class JSteprangeLastEmpty (α σ β : Type) where
  steprangeLastEmpty : α → σ → β → JlX β
/-- `steprange_last(start, step, stop)`. -/
class JSteprangeLast (α σ β : Type) where
  steprangeLast : α → σ → β → JlX β
/-- `unitrange_last(start, stop)`. -/
class JUnitrangeLast (α β : Type) where
  unitrangeLast : α → β → JlX β
/-- `StepRange{T,S}(start, step, stop)`. -/
class JStepRangeTS (T S α σ β : Type) where
  stepRangeTS : α → σ → β → JlX (StepRange T S)
/-- `StepRange{T}(start, step, stop)`. -/
class JStepRangeT (T α σ β : Type) (ρ : outParam Type) where
  stepRangeT : α → σ → β → JlX ρ
/-- `StepRange(start, step, stop)`. -/
class JStepRange3 (α σ β : Type) (ρ : outParam Type) where
  stepRange : α → σ → β → JlX ρ
/-- `UnitRange{T}(start, stop)`. -/
class JUnitRangeT (T α β : Type) where
  unitRangeT : α → β → JlX (UnitRange T)
/-- `UnitRange(start, stop)`. -/
class JUnitRange2 (α β : Type) (ρ : outParam Type) where
  unitRange : α → β → JlX ρ
/-- `OneTo{T}(x)`. -/
class JOneToT (T α : Type) where
  oneToT : α → JlX (OneTo T)
/-- `OneTo(x)`. -/
class JOneTo1 (α : Type) (ρ : outParam Type) where
  oneTo : α → JlX ρ
/-- `StepRangeLen{T,R,S,L}(ref, step, len, offset)`. -/
class JStepRangeLenTRSL (T R S L ρ σ Λ ο : Type) where
  stepRangeLenTRSL : ρ → σ → Λ → ο → JlX (StepRangeLen T R S L)
/-- `StepRangeLen{T,R,S}(ref, step, len, offset)`. -/
class JStepRangeLenTRS (T R S ρ σ Λ ο : Type) (out : outParam Type) where
  stepRangeLenTRS : ρ → σ → Λ → ο → JlX out
/-- `StepRangeLen{T}(ref, step, len, offset)`. -/
class JStepRangeLenT (T ρ σ Λ ο : Type) (out : outParam Type) where
  stepRangeLenT : ρ → σ → Λ → ο → JlX out
/-- `StepRangeLen(ref, step, len, offset)`. -/
class JStepRangeLen4 (ρ σ Λ ο : Type) (out : outParam Type) where
  stepRangeLen : ρ → σ → Λ → ο → JlX out
/-- `StepRangeLen(ref, step, len)`. -/
class JStepRangeLen3 (ρ σ Λ : Type) (out : outParam Type) where
  stepRangeLen : ρ → σ → Λ → JlX out
/-- `LinRange{T,L}(start, stop, len)`. -/
class JLinRangeTL (T L α β Λ : Type) where
  linRangeTL : α → β → Λ → JlX (LinRange T L)
/-- `LinRange{T}(start, stop, len)`. -/
class JLinRangeT (T α β Λ : Type) (out : outParam Type) where
  linRangeT : α → β → Λ → JlX out
/-- `LinRange(start, stop, len)`. -/
class JLinRange3 (α β Λ : Type) (out : outParam Type) where
  linRange : α → β → Λ → JlX out
/-- `LogRange{T}(start, stop, len)`. -/
class JLogRangeT (T α β Λ : Type) (out : outParam Type) where
  logRangeT : α → β → Λ → JlX out
/-- `LogRange(start, stop, len)`. -/
class JLogRange3 (α β Λ : Type) (out : outParam Type) where
  logRange : α → β → Λ → JlX out
/-- `_logrange_extra(a, b, len)`. -/
class JLograngeExtra (α β : Type) (X : outParam Type) where
  lograngeExtra : α → β → JInt64 → JlX (X × X)

/-- `first(r)`. -/
class JFirst (R : Type) (T : outParam Type) where
  first : R → JlX T
/-- `last(r)`. -/
class JLast (R : Type) (T : outParam Type) where
  last : R → JlX T
/-- `step(r)`. -/
class JStep (R : Type) (S : outParam Type) where
  step : R → JlX S
/-- `step_hp(r)`. -/
class JStepHp (R : Type) (S : outParam Type) where
  stepHp : R → JlX S
/-- `length(r)`. -/
class JLength (R : Type) (L : outParam Type) where
  length : R → JlX L
/-- `checked_length(r)`. -/
class JCheckedLength (R : Type) (L : outParam Type) where
  checkedLength : R → JlX L
/-- `isempty(r)`. -/
class JIsempty (R : Type) where
  isempty : R → JlX Bool
/-- `firstindex(r)`. -/
class JFirstindex (R : Type) (I : outParam Type) where
  firstindex : R → JlX I
/-- `lastindex(r)`. -/
class JLastindex (R : Type) (I : outParam Type) where
  lastindex : R → JlX I
/-- `size(r)`. -/
class JSize (R : Type) (Z : outParam Type) where
  size : R → JlX Z
/-- `eachindex(r)`. -/
class JEachindex (R : Type) (Z : outParam Type) where
  eachindex : R → JlX Z
/-- `LinearIndices(r)`. -/
class JLinearIndices (R : Type) (Z : outParam Type) where
  linearIndices : R → JlX Z
/-- `getindex(r, i)`, `r[i]`. -/
class JGetindex (R I : Type) (T : outParam Type) where
  getindex : R → I → JlX T
/-- `unsafe_getindex(r, i)`. -/
class JUnsafeGetindex (R I : Type) (T : outParam Type) where
  unsafeGetindex : R → I → JlX T
/-- `checkbounds(r, i)`: throws `BoundsError` unless `i` indexes `r`. -/
class JCheckbounds (R I : Type) where
  checkbounds : R → I → JlX Unit
/-- `checkbounds(Bool, r, i)`. -/
class JCheckboundsBool (R I : Type) where
  checkboundsBool : R → I → JlX Bool
/-- `throw_boundserror(r, i)`. -/
class JThrowBoundserror (R I : Type) where
  throwBoundserror : R → I → JlX Empty
/-- `require_one_based_indexing(r)` (abstractarray.jl). -/
class JRequireOneBased (R : Type) where
  requireOneBased : R → JlX Unit
/-- `iterate(r)`. -/
class JIterate1 (R : Type) (T S : outParam Type) where
  iterate : R → JlX (Option (T × S))
/-- `iterate(r, state)`. -/
class JIterate2 (R S : Type) (T : outParam Type) where
  iterate : R → S → JlX (Option (T × S))
/-- `isempty(r)` for the shorter-range test. -/
class JHasLengthOne (R : Type) where
  hasLengthOne : R → JlX Bool
/-- `minimum(r)`. -/
class JMinimum (R : Type) (T : outParam Type) where
  minimum : R → JlX T
/-- `maximum(r)`. -/
class JMaximum (R : Type) (T : outParam Type) where
  maximum : R → JlX T
/-- `copy(r)`. -/
class JCopy (R : Type) (ρ : outParam Type) where
  copy : R → JlX ρ
/-- Unary `-r` for a range `r`. -/
class JNegRange (R : Type) (ρ : outParam Type) where
  negRange : R → JlX ρ
/-- `reverse(r)`. -/
class JReverse (R : Type) (ρ : outParam Type) where
  reverse : R → JlX ρ
/-- `issorted(r)`. -/
class JIssorted (R : Type) where
  issorted : R → JlX Bool
/-- `x ∈ r`, `in(x, r)`. -/
class JIn (α R : Type) where
  isIn : α → R → JlX Bool
/-- `intersect(r, s)`. -/
class JIntersect (R S : Type) (ρ : outParam Type) where
  intersect : R → S → JlX ρ
/-- `unique(r)`. -/
class JUnique (R : Type) (ρ : outParam Type) where
  unique : R → JlX ρ
/-- `cmp(x, y)`. -/
class JCmp (α β : Type) where
  cmp : α → β → JlX JInt64
/-- The field `r.start` of a range type that has one. -/
class JFieldStart (R : Type) (A : outParam Type) where
  start : R → A
/-- The field `r.stop` of a range type that has one. -/
class JFieldStop (R : Type) (A : outParam Type) where
  stop : R → A
/-- The field `r.step` of a range type that has one. -/
class JFieldStep (R : Type) (A : outParam Type) where
  step : R → A
/-- `first_step_last_ascending(r)`. -/
class JFirstStepLastAscending (R : Type) (T S : outParam Type) where
  firstStepLastAscending : R → JlX (T × S × T)
/-- `StepRange{T,S}(r)` for a range `r`. -/
class JStepRangeTSOf (T S R : Type) where
  stepRangeTSOf : R → JlX (StepRange T S)
/-- `UnitRange{T}(r)` for a range `r`. -/
class JUnitRangeTOf (T R : Type) where
  unitRangeTOf : R → JlX (UnitRange T)
/-- `OneTo{T}(r)` for a range `r`. -/
class JOneToTOf (T R : Type) where
  oneToTOf : R → JlX (OneTo T)
/-- `AbstractUnitRange{T}(r)`. -/
class JAbstractUnitRangeT (T R : Type) (ρ : outParam Type) where
  abstractUnitRangeT : R → JlX ρ
/-- `StepRangeLen{T,R,S,L}(r)` for a range `r`. -/
class JStepRangeLenTRSLOf (T R S L ρ : Type) where
  stepRangeLenTRSLOf : ρ → JlX (StepRangeLen T R S L)
/-- `StepRangeLen{T}(r)` for a range `r`. -/
class JStepRangeLenTOf (T ρ : Type) (out : outParam Type) where
  stepRangeLenTOf : ρ → JlX out
/-- `StepRange{T}(r)` for a range `r`. -/
class JStepRangeTOf (T ρ : Type) (out : outParam Type) where
  stepRangeTOf : ρ → JlX out
/-- `LinRange{T,L}(r)` for a range `r`. -/
class JLinRangeTLOf (T L ρ : Type) where
  linRangeTLOf : ρ → JlX (LinRange T L)
/-- `LinRange{T}(r)` for a range `r`. -/
class JLinRangeTOf (T ρ : Type) (out : outParam Type) where
  linRangeTOf : ρ → JlX out
/-- `eltype(x)` as a value-free type-level function. -/
class JEltype (R : Type) (T : outParam Type) where
/-- `typeof(r)(fields...)`: the default constructor of the range's own type. -/
class JSameType3 (R α β γ : Type) where
  make : α → β → γ → JlX R
/-- `typeof(r)(ref, step, len, offset)`. -/
class JSameType4 (R α β γ δ : Type) where
  make : α → β → γ → δ → JlX R
/-- `Array(r)` for a range `r`. -/
class JArray (R : Type) (ρ : outParam Type) where
  array : R → JlX ρ
/-- `f(r1, r2)` for the range operators `+`/`-` that `_define_range_op` generates. -/
class JRangeOp (F R S : Type) (ρ : outParam Type) where
  rangeOp : R → S → JlX ρ
/-- `f(x, y)` for the scalar operators `+`/`-` used by `_define_range_op`. -/
class JScalarOp (F α β : Type) (γ : outParam Type) where
  scalarOp : α → β → γ
/-- `promote(r1, r2)` for ranges. -/
class JPromoteRanges (R S : Type) (ρ : outParam Type) where
  promoteRanges : R → S → JlX (ρ × ρ)


/-! ## `(:)`, wrapping helpers and `range` (lines 1-271) -/

/-- `oftype(x, y)` (essentials.jl): `y` converted to the type of `x`. -/
def oftype {D α : Type} [JConvert D α] (x : D) (y : α) : JlX D := JConvert.convert y

/--
Julia source: base/range.jl:1-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

(:)(a::Real, b::Real) = (:)(promote(a, b)...)
```
-/
def colon_Real_Real {α β γ ρ : Type} [JPromote2 α β γ] [JColon2 γ γ ρ] (a : α) (b : β) : JlX ρ := do
  let (a, b) ← JPromote2.promote a b
  JColon2.colon a b

/--
Julia source: base/range.jl:4-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
```
-/
def colon_T_T_Real {T : Type} [JUnitRangeT T T T] (start stop : T) : JlX (UnitRange T) :=
  JUnitRangeT.unitRangeT start stop

/--
Julia source: base/range.jl:6-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(:)(start::T, stop::T) where {T} = (:)(start, oftype(stop >= start ? stop - start : start - stop, 1), stop)
```
-/
def colon_T_T {T D ρ : Type} [JLe T T] [HSub T T D] [JConvert D JInt64] [JColon3 T D T ρ]
    (start stop : T) : JlX ρ := do
  let one ← oftype (if JLe.le start stop then stop - start else start - stop) (jint 1)
  JColon3.colon start one stop

/--
Julia source: base/range.jl:8-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# promote start and stop, leaving step alone
(:)(start::A, step, stop::C) where {A<:Real, C<:Real} =
    (:)(convert(promote_type(A, C), start), step, convert(promote_type(A, C), stop))
```
-/
def colon_A_step_C {A S C P ρ : Type} [JPromoteType A C P] [JConvert P A] [JConvert P C]
    [JColon3 P S P ρ] (start : A) (step : S) (stop : C) : JlX ρ := do
  let a ← JConvert.convert (T := P) start
  let b ← JConvert.convert (T := P) stop
  JColon3.colon a step b

/--
Julia source: base/range.jl:12-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# AbstractFloat specializations
(:)(a::T, b::T) where {T<:AbstractFloat} = (:)(a, T(1), b)
```
-/
def colon_T_T_AbstractFloat {T ρ : Type} [JCtor T JInt64] [JColon3 T T T ρ] (a b : T) : JlX ρ := do
  let one ← JCtor.ctor (T := T) (jint 1)
  JColon3.colon a one b

/--
Julia source: base/range.jl:15-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(:)(a::T, b::AbstractFloat, c::T) where {T<:Real} = (:)(promote(a, b, c)...)
```
-/
def colon_T_AbstractFloat_T_Real {T β P ρ : Type} [JPromote3 T β T P] [JColon3 P P P ρ]
    (a : T) (b : β) (c : T) : JlX ρ := do
  let (x, y, z) ← JPromote3.promote a b c
  JColon3.colon x y z

/--
Julia source: base/range.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(:)(a::T, b::AbstractFloat, c::T) where {T<:AbstractFloat} = (:)(promote(a, b, c)...)
```
-/
def colon_T_AbstractFloat_T_AbstractFloat {T β P ρ : Type} [JPromote3 T β T P] [JColon3 P P P ρ]
    (a : T) (b : β) (c : T) : JlX ρ := do
  let (x, y, z) ← JPromote3.promote a b c
  JColon3.colon x y z

/--
Julia source: base/range.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(:)(a::T, b::Real, c::T) where {T<:AbstractFloat} = (:)(promote(a, b, c)...)
```
-/
def colon_T_Real_T_AbstractFloat {T β P ρ : Type} [JPromote3 T β T P] [JColon3 P P P ρ]
    (a : T) (b : β) (c : T) : JlX ρ := do
  let (x, y, z) ← JPromote3.promote a b c
  JColon3.colon x y z

/--
Julia source: base/range.jl:19-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(:)(start::T, step::T, stop::T) where {T<:AbstractFloat} =
    _colon(OrderStyle(T), ArithmeticStyle(T), start, step, stop)
```
-/
def colon_T_T_T_AbstractFloat {T O A ρ : Type} [JOrderStyle T O] [JArithmeticStyle T A]
    [JColonStyle O A T T T ρ] (start step stop : T) : JlX ρ :=
  JColonStyle.colonStyle (JOrderStyle.orderStyle T) (JArithmeticStyle.arithmeticStyle T)
    start step stop

/--
Julia source: base/range.jl:22-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(:)(start::T, step::T, stop::T) where {T<:Real} =
    _colon(OrderStyle(T), ArithmeticStyle(T), start, step, stop)
```
-/
def colon_T_T_T_Real {T O A ρ : Type} [JOrderStyle T O] [JArithmeticStyle T A]
    [JColonStyle O A T T T ρ] (start step stop : T) : JlX ρ :=
  JColonStyle.colonStyle (JOrderStyle.orderStyle T) (JArithmeticStyle.arithmeticStyle T)
    start step stop

/--
Julia source: base/range.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_colon(::Ordered, ::Any, start::T, step, stop::T) where {T} = StepRange(start, step, stop)
```
-/
def _colon_Ordered_Any {A T S ρ : Type} [JStepRange3 T S T ρ]
    (o : Ordered) (a : A) (start : T) (step : S) (stop : T) : JlX ρ :=
  JStepRange3.stepRange start step stop

/--
Julia source: base/range.jl:25-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# for T<:Union{Float16,Float32,Float64} see twiceprecision.jl
_colon(::Ordered, ::ArithmeticRounds, start::T, step, stop::T) where {T} =
    StepRangeLen(start, step, convert(Integer, fld(stop - start, step)) + 1)
```
-/
def _colon_Ordered_ArithmeticRounds {T S D Q I J ρ : Type} [HSub T T D] [JFld D S Q]
    [JConvertInteger Q I] [HAdd I JInt64 J] [JStepRangeLen3 T S J ρ]
    (o : Ordered) (a : ArithmeticRounds) (start : T) (step : S) (stop : T) : JlX ρ := do
  let q ← JFld.fld (stop - start) step
  let n ← JConvertInteger.convertInteger q
  JStepRangeLen3.stepRangeLen start step (n + jint 1)

/--
Julia source: base/range.jl:28-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_colon(::Any, ::Any, start::T, step, stop::T) where {T} =
    StepRangeLen(start, step, convert(Integer, fld(stop - start, step)) + 1)
```
-/
def _colon_Any_Any {O A T S D Q I J ρ : Type} [HSub T T D] [JFld D S Q]
    [JConvertInteger Q I] [HAdd I JInt64 J] [JStepRangeLen3 T S J ρ]
    (o : O) (a : A) (start : T) (step : S) (stop : T) : JlX ρ := do
  let q ← JFld.fld (stop - start) step
  let n ← JConvertInteger.convertInteger q
  JStepRangeLen3.stepRangeLen start step (n + jint 1)

/--
Julia source: base/range.jl:30-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const _RangeWrappingInteger = Union{
    Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128}

_range_wrapping_add(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x +% y
```
-/
def _range_wrapping_add_BitInteger {α β γ : Type} [JWrappingAdd α β γ] (x : α) (y : β) : γ :=
  JWrappingAdd.wrappingAdd x y

/--
Julia source: base/range.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_add(x, y) = x + y
```
-/
def _range_wrapping_add_Any {α β γ : Type} [HAdd α β γ] (x : α) (y : β) : γ := x + y

/--
Julia source: base/range.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_sub(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x -% y
```
-/
def _range_wrapping_sub_BitInteger {α β γ : Type} [JWrappingSub α β γ] (x : α) (y : β) : γ :=
  JWrappingSub.wrappingSub x y

/--
Julia source: base/range.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_sub(x, y) = x - y
```
-/
def _range_wrapping_sub_Any {α β γ : Type} [HSub α β γ] (x : α) (y : β) : γ := x - y

/--
Julia source: base/range.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_mul(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x *% y
```
-/
def _range_wrapping_mul_BitInteger {α β γ : Type} [JWrappingMul α β γ] (x : α) (y : β) : γ :=
  JWrappingMul.wrappingMul x y

/--
Julia source: base/range.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_mul(x, y) = x * y
```
-/
def _range_wrapping_mul_Any {α β γ : Type} [HMul α β γ] (x : α) (y : β) : γ := x * y

/--
Julia source: base/range.jl:66-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# without the second method above, the first method above is ambiguous with
# (:)(start::A, step, stop::C) where {A<:Real,C<:Real}
function _colon(start::T, step, stop::T) where T
    T′ = typeof(start+zero(step))
    StepRange(convert(T′,start), step, convert(T′,stop))
end
```
-/
def _colon_T_step_T {T S T' ρ : Type} [JZero S] [HAdd T S T'] [JConvert T' T]
    [JStepRange3 T' S T' ρ] (start : T) (step : S) (stop : T) : JlX ρ := do
  -- `T′ = typeof(start+zero(step))`: the value is computed for its type only
  let _t : T' := start + (JZero.zero : S)
  let a ← JConvert.convert (T := T') start
  let b ← JConvert.convert (T := T') stop
  JStepRange3.stepRange a step b

/--
Julia source: base/range.jl:40-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    (:)(start, [step], stop)

Range operator. `a:b` constructs a range from `a` to `b` with a step size
equal to +1, which produces:

* a [`UnitRange`](@ref) when `a` and `b` are integers, or
* a [`StepRange`](@ref) when `a` and `b` are characters, or
* a [`StepRangeLen`](@ref) when `a` and/or `b` are floating-point.

`a:s:b` is similar but uses a step size of `s` (a [`StepRange`](@ref) or
[`StepRangeLen`](@ref)). See also [`range`](@ref) for more control.

To create a descending range, use `reverse(a:b)` or a negative step size, e.g. `b:-1:a`.
Otherwise, when `b < a`, an empty range will be constructed and normalized to `a:a-1`.

The operator `:` is also used in indexing to select whole dimensions, e.g. in `A[:, 1]`.

`:` is also used to [`quote`](@ref) code, e.g. `:(x + y) isa Expr` and `:x isa Symbol`.
Since `:2 isa Int`, it does *not* create a range in indexing: `v[:2] == v[2] != v[begin:2]`.
"""
(:)(::Any, ::Any, ::Any)

(:)(start::T, step, stop::T) where {T} = _colon(start, step, stop)
```
-/
def colon_T_step_T {T S T' ρ : Type} [JZero S] [HAdd T S T'] [JConvert T' T]
    [JStepRange3 T' S T' ρ] (start : T) (step : S) (stop : T) : JlX ρ :=
  _colon_T_step_T start step stop

/--
Julia source: base/range.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(:)(start::T, step, stop::T) where {T<:Real} = _colon(start, step, stop)
```
-/
def colon_T_step_T_Real {T S T' ρ : Type} [JZero S] [HAdd T S T'] [JConvert T' T]
    [JStepRange3 T' S T' ρ] (start : T) (step : S) (stop : T) : JlX ρ :=
  _colon_T_step_T start step stop


/--
Julia source: base/range.jl:242-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function range_error(start, step, stop, length)
    hasstart  = start !== nothing
    hasstep   = step  !== nothing
    hasstop   = stop  !== nothing
    haslength = start !== nothing

    hint = if hasstart && hasstep && hasstop && haslength
        "Try specifying only three arguments"
    elseif !hasstop && !haslength
        "At least one of `length` or `stop` must be specified."
    elseif !hasstep && !haslength
        "At least one of `length` or `step` must be specified."
    elseif !hasstart && !hasstop
        "At least one of `start` or `stop` must be specified."
    else
        "Try specifying more arguments."
    end

    msg = """
    Cannot construct range from arguments:
    start = $start
    step = $step
    stop = $stop
    length = $length
    $hint
    """
    throw(ArgumentError(msg))
end

```
-/
def range_error {α σ β Λ ρ : Type} [JIsNothing α] [JIsNothing σ] [JIsNothing β] [JIsNothing Λ]
    [JPrint α] [JPrint σ] [JPrint β] [JPrint Λ]
    (start : α) (step : σ) (stop : β) (length : Λ) : JlX ρ := do
  let hasstart := !JIsNothing.isNothing start
  let hasstep := !JIsNothing.isNothing step
  let hasstop := !JIsNothing.isNothing stop
  let haslength := !JIsNothing.isNothing start
  let hint :=
    if hasstart && hasstep && hasstop && haslength then "Try specifying only three arguments"
    else if !hasstop && !haslength then "At least one of `length` or `stop` must be specified."
    else if !hasstep && !haslength then "At least one of `length` or `step` must be specified."
    else if !hasstart && !hasstop then "At least one of `start` or `stop` must be specified."
    else "Try specifying more arguments."
  let msg := "Cannot construct range from arguments:\nstart = " ++ JPrint.print start ++
    "\nstep = " ++ JPrint.print step ++ "\nstop = " ++ JPrint.print stop ++
    "\nlength = " ++ JPrint.print length ++ "\n" ++ hint ++ "\n"
  throw (.jl (.argumentError msg))

/--
Julia source: base/range.jl:191-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Length as the only argument
range_length(len::Integer) = OneTo(len)
```
-/
def range_length {Λ ρ : Type} [JOneTo1 Λ ρ] (len : Λ) : JlX ρ := JOneTo1.oneTo len

/--
Julia source: base/range.jl:229-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

range_start_stop(start, stop) = start:stop
```
-/
def range_start_stop {α β ρ : Type} [JColon2 α β ρ] (start : α) (stop : β) : JlX ρ :=
  JColon2.colon start stop

/--
Julia source: base/range.jl:194-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Stop as the only argument
range_stop(stop) = range_start_stop(oftype(stop, 1), stop)
```
-/
def range_stop_Any {β ρ : Type} [JConvert β JInt64] [JColon2 β β ρ] (stop : β) : JlX ρ := do
  let one ← oftype stop (jint 1)
  range_start_stop one stop

/--
Julia source: base/range.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_stop(stop::Integer) = range_length(stop)
```
-/
def range_stop_Integer {β ρ : Type} [JOneTo1 β ρ] (stop : β) : JlX ρ := range_length stop

/--
Julia source: base/range.jl:198-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function range_step_stop_length(step, a, len::Integer)
    start = _range_wrapping_sub(a, _range_wrapping_mul(step, len - oneunit(len)))
    if start isa Signed
        # overflow in recomputing length from stop is okay
        return StepRange{typeof(start),typeof(step)}(start, step, convert(typeof(start), a))
    end
    return StepRangeLen{typeof(start),typeof(start),typeof(step)}(start, step, len)
end
```
-/
def range_step_stop_length {S A L M P Q ρ : Type} [JOneunit L] [HSub L L M]
    [JRangeWrappingMul S M P] [JRangeWrappingSub A P Q] [JType Q] [JConvert Q A]
    [JStepRangeTS Q S Q S Q] [JStepRangeLenTRS Q Q S Q S L JInt64 ρ]
    (step : S) (a : A) (len : L) : JlX (StepRange Q S ⊕ ρ) := do
  let start := JRangeWrappingSub.rangeWrappingSub a
    (JRangeWrappingMul.rangeWrappingMul step (len - (JOneunit.oneunit : L)))
  if JType.isSigned Q then
    let stop ← JConvert.convert (T := Q) a
    return .inl (← JStepRangeTS.stepRangeTS start step stop)
  return .inr (← JStepRangeLenTRS.stepRangeLenTRS (T := Q) (R := Q) (S := S) start step len (jint 1))

/--
Julia source: base/range.jl:207-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Stop and length as the only argument
function range_stop_length(a, len::Integer)
    step = oftype(a - a, 1) # assert that step is representable
    start = _range_wrapping_sub(a, len - oneunit(len))
    if start isa Signed
        # overflow in recomputing length from stop is okay
        return UnitRange(start, oftype(start, a))
    end
    return StepRangeLen{typeof(start),typeof(start),typeof(step)}(start, step, len)
end
```
-/
def range_stop_length {A D L M Q U ρ : Type} [HSub A A D] [JConvert D JInt64] [JOneunit L]
    [HSub L L M] [JRangeWrappingSub A M Q] [JType Q] [JConvert Q A] [JUnitRange2 Q Q U]
    [JStepRangeLenTRS Q Q D Q D L JInt64 ρ] (a : A) (len : L) : JlX (U ⊕ ρ) := do
  let step ← oftype (a - a) (jint 1)
  let start := JRangeWrappingSub.rangeWrappingSub a (len - (JOneunit.oneunit : L))
  if JType.isSigned Q then
    let stop ← oftype start a
    return .inl (← JUnitRange2.unitRange start stop)
  return .inr (← JStepRangeLenTRS.stepRangeLenTRS (T := Q) (R := Q) (S := D) start step len (jint 1))

/--
Julia source: base/range.jl:218-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Start and length as the only argument
function range_start_length(a, len::Integer)
    step = oftype(a - a, 1) # assert that step is representable
    stop = _range_wrapping_add(a, len - oneunit(len))
    if stop isa Signed
        # overflow in recomputing length from stop is okay
        return UnitRange(oftype(stop, a), stop)
    end
    return StepRangeLen{typeof(stop),typeof(a),typeof(step)}(a, step, len)
end
```
-/
def range_start_length {A D L M Q U ρ : Type} [HSub A A D] [JConvert D JInt64] [JOneunit L]
    [HSub L L M] [JRangeWrappingAdd A M Q] [JType Q] [JConvert Q A] [JUnitRange2 Q Q U]
    [JStepRangeLenTRS Q A D A D L JInt64 ρ] (a : A) (len : L) : JlX (U ⊕ ρ) := do
  let step ← oftype (a - a) (jint 1)
  let stop := JRangeWrappingAdd.rangeWrappingAdd a (len - (JOneunit.oneunit : L))
  if JType.isSigned Q then
    let start ← oftype stop a
    return .inl (← JUnitRange2.unitRange start stop)
  return .inr (← JStepRangeLenTRS.stepRangeLenTRS (T := Q) (R := A) (S := D) a step len (jint 1))

/--
Julia source: base/range.jl:231-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function range_start_step_length(a, step, len::Integer)
    stop = _range_wrapping_add(a, _range_wrapping_mul(step, len - oneunit(len)))
    if stop isa Signed
        # overflow in recomputing length from stop is okay
        return StepRange{typeof(stop),typeof(step)}(convert(typeof(stop), a), step, stop)
    end
    return StepRangeLen{typeof(stop),typeof(a),typeof(step)}(a, step, len)
end
```
-/
def range_start_step_length {A S L M P Q ρ : Type} [JOneunit L] [HSub L L M]
    [JRangeWrappingMul S M P] [JRangeWrappingAdd A P Q] [JType Q] [JConvert Q A]
    [JStepRangeTS Q S Q S Q] [JStepRangeLenTRS Q A S A S L JInt64 ρ]
    (a : A) (step : S) (len : L) : JlX (StepRange Q S ⊕ ρ) := do
  let stop := JRangeWrappingAdd.rangeWrappingAdd a
    (JRangeWrappingMul.rangeWrappingMul step (len - (JOneunit.oneunit : L)))
  if JType.isSigned Q then
    let start ← JConvert.convert (T := Q) a
    return .inl (← JStepRangeTS.stepRangeTS start step stop)
  return .inr (← JStepRangeLenTRS.stepRangeLenTRS (T := Q) (R := A) (S := S) a step len (jint 1))

/--
Julia source: base/range.jl:240-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

range_start_step_stop(start, step, stop) = start:step:stop
```
-/
def range_start_step_stop {α σ β ρ : Type} [JColon3 α σ β ρ] (start : α) (step : σ) (stop : β) :
    JlX ρ :=
  JColon3.colon start step stop

/--
Julia source: base/range.jl:174-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

_range(start::Nothing, step::Nothing, stop::Nothing, len::Nothing) = range_error(start, step, stop, len)
```
-/
def _range_N_N_N_N {ρ : Type} [JIsNothing Nothing] [JPrint Nothing]
    (start step stop len : Nothing) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Nothing, stop::Nothing, len::Any    ) = range_length(len)
```
-/
def _range_N_N_N_A {Λ ρ : Type} [JOneTo1 Λ ρ] (start step stop : Nothing) (len : Λ) : JlX ρ :=
  range_length len

/--
Julia source: base/range.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Nothing, stop::Any    , len::Nothing) = range_stop(stop)
```
-/
def _range_N_N_A_N {β ρ : Type} [JRangeStop β ρ] (start step : Nothing) (stop : β)
    (len : Nothing) : JlX ρ :=
  JRangeStop.rangeStop stop

/--
Julia source: base/range.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Nothing, stop::Any    , len::Any    ) = range_stop_length(stop, len)
```
-/
def _range_N_N_A_A {A D L M Q U ρ : Type} [HSub A A D] [JConvert D JInt64] [JOneunit L]
    [HSub L L M] [JRangeWrappingSub A M Q] [JType Q] [JConvert Q A] [JUnitRange2 Q Q U]
    [JStepRangeLenTRS Q Q D Q D L JInt64 ρ] (start step : Nothing) (stop : A) (len : L) :
    JlX (U ⊕ ρ) :=
  range_stop_length stop len

/--
Julia source: base/range.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Any    , stop::Nothing, len::Nothing) = range_error(start, step, stop, len)
```
-/
def _range_N_A_N_N {σ ρ : Type} [JIsNothing Nothing] [JPrint Nothing] [JIsNothing σ] [JPrint σ]
    (start : Nothing) (step : σ) (stop len : Nothing) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Any    , stop::Nothing, len::Any    ) = range_error(start, step, stop, len)
```
-/
def _range_N_A_N_A {σ Λ ρ : Type} [JIsNothing Nothing] [JPrint Nothing] [JIsNothing σ] [JPrint σ]
    [JIsNothing Λ] [JPrint Λ] (start : Nothing) (step : σ) (stop : Nothing) (len : Λ) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Any    , stop::Any    , len::Nothing) = range_error(start, step, stop, len)
```
-/
def _range_N_A_A_N {σ β ρ : Type} [JIsNothing Nothing] [JPrint Nothing] [JIsNothing σ] [JPrint σ]
    [JIsNothing β] [JPrint β] (start : Nothing) (step : σ) (stop : β) (len : Nothing) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Nothing, step::Any    , stop::Any    , len::Any    ) = range_step_stop_length(step, stop, len)
```
-/
def _range_N_A_A_A {S A L M P Q ρ : Type} [JOneunit L] [HSub L L M]
    [JRangeWrappingMul S M P] [JRangeWrappingSub A P Q] [JType Q] [JConvert Q A]
    [JStepRangeTS Q S Q S Q] [JStepRangeLenTRS Q Q S Q S L JInt64 ρ]
    (start : Nothing) (step : S) (stop : A) (len : L) : JlX (StepRange Q S ⊕ ρ) :=
  range_step_stop_length step stop len

/--
Julia source: base/range.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Nothing, stop::Nothing, len::Nothing) = range_error(start, step, stop, len)
```
-/
def _range_A_N_N_N {α ρ : Type} [JIsNothing Nothing] [JPrint Nothing] [JIsNothing α] [JPrint α]
    (start : α) (step stop len : Nothing) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Nothing, stop::Nothing, len::Any    ) = range_start_length(start, len)
```
-/
def _range_A_N_N_A {A D L M Q U ρ : Type} [HSub A A D] [JConvert D JInt64] [JOneunit L]
    [HSub L L M] [JRangeWrappingAdd A M Q] [JType Q] [JConvert Q A] [JUnitRange2 Q Q U]
    [JStepRangeLenTRS Q A D A D L JInt64 ρ] (start : A) (step stop : Nothing) (len : L) :
    JlX (U ⊕ ρ) :=
  range_start_length start len

/--
Julia source: base/range.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Nothing, stop::Any    , len::Nothing) = range_start_stop(start, stop)
```
-/
def _range_A_N_A_N {α β ρ : Type} [JColon2 α β ρ] (start : α) (step : Nothing) (stop : β)
    (len : Nothing) : JlX ρ :=
  range_start_stop start stop

/--
Julia source: base/range.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Nothing, stop::Any    , len::Any    ) = range_start_stop_length(start, stop, len)
```
-/
def _range_A_N_A_A {α β Λ ρ : Type} [JRangeStartStopLength α β Λ ρ] (start : α) (step : Nothing)
    (stop : β) (len : Λ) : JlX ρ :=
  JRangeStartStopLength.rangeStartStopLength start stop len

/--
Julia source: base/range.jl:187-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Any    , stop::Nothing, len::Nothing) = range_error(start, step, stop, len)
```
-/
def _range_A_A_N_N {α σ ρ : Type} [JIsNothing Nothing] [JPrint Nothing] [JIsNothing α] [JPrint α]
    [JIsNothing σ] [JPrint σ] (start : α) (step : σ) (stop len : Nothing) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Any    , stop::Nothing, len::Any    ) = range_start_step_length(start, step, len)
```
-/
def _range_A_A_N_A {A S L M P Q ρ : Type} [JOneunit L] [HSub L L M]
    [JRangeWrappingMul S M P] [JRangeWrappingAdd A P Q] [JType Q] [JConvert Q A]
    [JStepRangeTS Q S Q S Q] [JStepRangeLenTRS Q A S A S L JInt64 ρ]
    (start : A) (step : S) (stop : Nothing) (len : L) : JlX (StepRange Q S ⊕ ρ) :=
  range_start_step_length start step len

/--
Julia source: base/range.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Any    , stop::Any    , len::Nothing) = range_start_step_stop(start, step, stop)
```
-/
def _range_A_A_A_N {α σ β ρ : Type} [JColon3 α σ β ρ] (start : α) (step : σ) (stop : β)
    (len : Nothing) : JlX ρ :=
  range_start_step_stop start step stop

/--
Julia source: base/range.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range(start::Any    , step::Any    , stop::Any    , len::Any    ) = range_error(start, step, stop, len)
```
-/
def _range_A_A_A_A {α σ β Λ ρ : Type} [JIsNothing α] [JPrint α] [JIsNothing σ] [JPrint σ]
    [JIsNothing β] [JPrint β] [JIsNothing Λ] [JPrint Λ]
    (start : α) (step : σ) (stop : β) (len : Λ) : JlX ρ :=
  range_error start step stop len

/--
Julia source: base/range.jl:72-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    range(start, stop, length)
    range(start, stop; length, step)
    range(start; length, stop, step)
    range(;start, length, stop, step)

Construct a specialized array with evenly spaced elements and optimized storage (an [`AbstractRange`](@ref)) from the arguments.
Mathematically a range is uniquely determined by any three of `start`, `step`, `stop` and `length`.
Valid invocations of range are:
* Call `range` with any three of `start`, `step`, `stop`, `length`.
* Call `range` with two of `start`, `stop`, `length`. In this case `step` will be assumed
  to be positive one. If both arguments are Integers, a [`UnitRange`](@ref) will be returned.
* Call `range` with one of `stop` or `length`. `start` and `step` will be assumed to be positive one.

To construct a descending range, specify a negative step size, e.g. `range(5, 1; step = -1)` => [5,4,3,2,1]. Otherwise,
a `stop` value less than the `start` value, with the default `step` of `+1`, constructs an empty range. Empty ranges
are normalized such that the `stop` is one less than the `start`, e.g. `range(5, 1) == 5:4`.

See Extended Help for additional details on the returned type.
See also [`logrange`](@ref) for logarithmically spaced points.

# Examples
```jldoctest
julia> range(1, length=100)
1:100

julia> range(1, stop=100)
1:100

julia> range(1, step=5, length=100)
1:5:496

julia> range(1, step=5, stop=100)
1:5:96

julia> range(1, 10, length=101)
1.0:0.09:10.0

julia> range(1, 100, step=5)
1:5:96

julia> range(stop=10, length=5)
6:10

julia> range(stop=10, step=1, length=5)
6:1:10

julia> range(start=1, step=1, stop=10)
1:1:10

julia> range(; length = 10)
Base.OneTo(10)

julia> range(; stop = 6)
Base.OneTo(6)

julia> range(; stop = 6.5)
1.0:1.0:6.0
```
If `length` is not specified and `stop - start` is not an integer multiple of `step`, a range that ends before `stop` will be produced.
```jldoctest
julia> range(1, 3.5, step=2)
1.0:2.0:3.0
```

Special care is taken to ensure intermediate values are computed rationally.
To avoid this induced overhead, see the [`LinRange`](@ref) constructor.

!!! compat "Julia 1.1"
    `stop` as a positional argument requires at least Julia 1.1.

!!! compat "Julia 1.7"
    The versions without keyword arguments and `start` as a keyword argument
    require at least Julia 1.7.

!!! compat "Julia 1.8"
    The versions with `stop` as a sole keyword argument,
    or `length` as a sole keyword argument require at least Julia 1.8.


# Extended Help

`range` will produce a `Base.OneTo` when the arguments are Integers and
* Only `length` is provided
* Only `stop` is provided

`range` will produce a `UnitRange` when the arguments are Integers and
* Only `start`  and `stop` are provided
* Only `length` and `stop` are provided

A `UnitRange` is not produced if `step` is provided even if specified as one.
"""
function range end
````
-/
class JRangeStartKw (α β Λ σ : Type) (ρ : outParam Type) where
  range : α → β → Λ → σ → JlX ρ

/-- `range(start, stop; length, step)` (the same generic function, keywords positional). -/
class JRangeStartStopKw (α β Λ σ : Type) (ρ : outParam Type) where
  range : α → β → Λ → σ → JlX ρ

/--
Julia source: base/range.jl:166-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing) =
    _range(start, step, stop, length)
```
-/
def range_start_kw {α β Λ σ ρ : Type} [JRangeImpl α σ β Λ ρ]
    (start : α) (stop : β) (length : Λ) (step : σ) : JlX ρ :=
  JRangeImpl.rangeImpl start step stop length

/--
Julia source: base/range.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing) = _range(start, step, stop, length)
```
-/
def range_start_stop_kw {α β Λ σ ρ : Type} [JRangeImpl α σ β Λ ρ]
    (start : α) (stop : β) (length : Λ) (step : σ) : JlX ρ :=
  JRangeImpl.rangeImpl start step stop length

/--
Julia source: base/range.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range(start, stop, length::Integer) = _range(start, nothing, stop, length)
```
-/
def range_start_stop_length3 {α β Λ ρ : Type} [JRangeImpl α Nothing β Λ ρ]
    (start : α) (stop : β) (length : Λ) : JlX ρ :=
  JRangeImpl.rangeImpl start Nothing.nothing stop length

/--
Julia source: base/range.jl:171-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing) =
    _range(start, step, stop, length)
```
-/
def range_kw {α β Λ σ ρ : Type} [JRangeImpl α σ β Λ ρ]
    (start : α) (stop : β) (length : Λ) (step : σ) : JlX ρ :=
  JRangeImpl.rangeImpl start step stop length


/-! ## Range types: constructors (lines 272-551) -/

/-- `not_sametype(x, y)` (promotion.jl): throws when promotion left the argument types unchanged. -/
class JNotSametype (α β : Type) where
  notSametype : α → β → JlX Unit

/--
Julia source: base/range.jl:272-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## 1-dimensional ranges ##

"""
    AbstractRange{T} <: AbstractVector{T}

Supertype for linear ranges with elements of type `T`.
[`UnitRange`](@ref), [`LinRange`](@ref) and other types are subtypes of this.

All subtypes must define [`step`](@ref).
Thus [`LogRange`](@ref Base.LogRange) is not a subtype of `AbstractRange`.
"""
abstract type AbstractRange{T} <: AbstractArray{T,1} end

RangeStepStyle(::Type{<:AbstractRange}) = RangeStepIrregular()
```
-/
def RangeStepStyle_AbstractRange (R : Type) : RangeStepIrregular := {}

/--
Julia source: base/range.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
RangeStepStyle(::Type{<:AbstractRange{<:Integer}}) = RangeStepRegular()
```
-/
def RangeStepStyle_AbstractRange_Integer (R : Type) : RangeStepRegular := {}

/-- `r isa T`: whether the range value already has the target range type. -/
class JIsa (R T : Type) where
  isa : R → Option T

/--
Julia source: base/range.jl:287-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

convert(::Type{T}, r::AbstractRange) where {T<:AbstractRange} = r isa T ? r : T(r)::T
```
-/
def convert_Type_AbstractRange (T : Type) {R : Type} [JIsa R T] [JCtor T R] (r : R) : JlX T :=
  match JIsa.isa r with
  | some t => pure t
  | none => JCtor.ctor r

/--
Julia source: base/range.jl:377-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
```
-/
def steprange_last.overflow_case {D A U Q : Type} [JUnsigned D U] [JRem U A Q] [JConvert D Q]
    (absdiff : D) (absstep : A) : JlX D := do
  let r ← JRem.rem (JUnsigned.unsigned absdiff) absstep
  JConvert.convert r

/--
Julia source: base/range.jl:353-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprange_last(start, step, stop)::typeof(stop)
    if isa(start, AbstractFloat) || isa(step, AbstractFloat)
        throw(ArgumentError("StepRange should not be used with floating point"))
    end
    if isa(start, Integer) && !isinteger(start + step)
        throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
    end
    z = zero(step)
    step == z && throw(ArgumentError("step cannot be zero"))

    if stop == start
        last = stop
    else
        if (step > z) != (stop > start)
            last = steprange_last_empty(start, step, stop)
        else
            # Compute absolute value of difference between `start` and `stop`
            # (to simplify handling both signed and unsigned T and checking for signed overflow):
            absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
                                                (_range_wrapping_sub(start, stop), -step)

            # Compute remainder as a non-negative number:
            if absdiff isa Signed && absdiff < zero(absdiff)
                # unlikely, but handle the signed overflow case with unsigned rem
                overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
                remain = overflow_case(absdiff, absstep)
            else
                remain = convert(typeof(absdiff), absdiff % absstep)
            end
            # Move `stop` closer to `start` if there is a remainder:
            last = stop > start ? stop - remain : stop + remain
        end
    end
    return last
end

```
-/
def steprange_last {A S T D N U Q R E F : Type} [JType A] [JType S] [HAdd A S F] [JIsinteger F]
    [JZero S] [JEq S S] [JEq T A] [JLt S S] [JLt A T] [JSteprangeLastEmpty A S T]
    [JRangeWrappingSub T A D] [JRangeWrappingSub A T D] [JNeg S N] [JType D] [JZero D] [JLt D D]
    [JUnsigned D U] [JRem U (S ⊕ N) Q] [JConvert D Q] [JRem D (S ⊕ N) R] [JConvert D R]
    [HSub T D E] [HAdd T D E] [JConvert T T] [JConvert T E] (start : A) (step : S) (stop : T) :
    JlX T := do
  if JType.isAbstractFloat A || JType.isAbstractFloat S then
    throw (.jl (.argumentError "StepRange should not be used with floating point"))
  if JType.isInteger A && !JIsinteger.isinteger (start + step) then
    throw (.jl (.argumentError "StepRange{<:Integer} cannot have non-integer step"))
  let z : S := JZero.zero
  if JEq.eq step z then throw (.jl (.argumentError "step cannot be zero"))
  let last : T ⊕ E ←
    if JEq.eq stop start then
      pure (.inl stop)
    else
      if JLt.lt z step != JLt.lt start stop then
        .inl <$> JSteprangeLastEmpty.steprangeLastEmpty start step stop
      else
        let (absdiff, absstep) : D × (S ⊕ N) := if JLt.lt start stop then
            (JRangeWrappingSub.rangeWrappingSub stop start, .inl step)
          else (JRangeWrappingSub.rangeWrappingSub start stop, .inr (JNeg.neg step))
        let remain ← if JType.isSigned D && JLt.lt absdiff (JZero.zero : D) then
            steprange_last.overflow_case absdiff absstep
          else do
            let r ← JRem.rem absdiff absstep
            JConvert.convert (T := D) r
        pure (.inr (if JLt.lt start stop then stop - remain else stop + remain))
  match last with
  | .inl x => JConvert.convert (T := T) x
  | .inr x => JConvert.convert (T := T) x

/--
Julia source: base/range.jl:389-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
    # empty range has a special representation where stop = start-1,
    # which simplifies arithmetic for Signed numbers
    if step > zero(step)
        last = _range_wrapping_sub(start, oneunit(step))
    else
        last = _range_wrapping_add(start, oneunit(step))
    end
    return last
end
```
-/
def steprange_last_empty_Integer {T S Q : Type} [JZero S] [JLt S S] [JOneunit S]
    [JRangeWrappingSub T S Q] [JRangeWrappingAdd T S Q] [JConvert T Q]
    (start : T) (step : S) (stop : T) : JlX T := do
  let last : Q := if JLt.lt (JZero.zero : S) step then
      JRangeWrappingSub.rangeWrappingSub start (JOneunit.oneunit : S)
    else JRangeWrappingAdd.rangeWrappingAdd start (JOneunit.oneunit : S)
  JConvert.convert (T := T) last

/--
Julia source: base/range.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
steprange_last_empty(start::Bool, step, stop) = start ⊻ (step > zero(step)) # isnegative(step) ? start : !start
```
-/
def steprange_last_empty_Bool {S : Type} [JZero S] [JLt S S]
    (start : Bool) (step : S) (stop : Bool) : JlX Bool :=
  pure (xor start (JLt.lt (JZero.zero : S) step))

/--
Julia source: base/range.jl:400-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For types where x+oneunit(x) may not be well-defined use the user-given value for stop
steprange_last_empty(start, step, stop) = stop
```
-/
def steprange_last_empty_Any {T S β : Type} (start : T) (step : S) (stop : β) : JlX β :=
  pure stop

/--
Julia source: base/range.jl:344-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function StepRange{T,S}(start, step, stop) where {T,S}
        start = convert(T, start)
        step = convert(S, step)
        stop = convert(T, stop)
        return new(start, step, steprange_last(start, step, stop))
    end
end

# to make StepRange constructor inlineable, so optimizer can see `step` value
```
-/
def StepRange_TS_new (T S : Type) {α σ β : Type} [JConvert T α] [JConvert S σ] [JConvert T β]
    [JSteprangeLast T S T] (start : α) (step : σ) (stop : β) : JlX (StepRange T S) := do
  let start ← JConvert.convert (T := T) start
  let step ← JConvert.convert (T := S) step
  let stop ← JConvert.convert (T := T) stop
  return ⟨start, step, ← JSteprangeLast.steprangeLast start step stop⟩

/--
Julia source: base/range.jl:402-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

StepRange{T}(start, step::S, stop) where {T,S} = StepRange{T,S}(start, step, stop)
```
-/
def StepRange_T {T α S β : Type} [JStepRangeTS T S α S β] (start : α) (step : S) (stop : β) :
    JlX (StepRange T S) :=
  JStepRangeTS.stepRangeTS start step stop

/--
Julia source: base/range.jl:404-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange(start::T, step::S, stop::T) where {T,S} = StepRange{T,S}(start, step, stop)
```
-/
def StepRange_T_S_T {T S : Type} [JStepRangeTS T S T S T] (start : T) (step : S) (stop : T) :
    JlX (StepRange T S) :=
  JStepRangeTS.stepRangeTS start step stop

/--
Julia source: base/range.jl:428-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
end
```
-/
def UnitRange_T_new {T : Type} [JUnitrangeLast T T] (start stop : T) : JlX (UnitRange T) := do
  return ⟨start, ← JUnitrangeLast.unitrangeLast start stop⟩

/--
Julia source: base/range.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange{T}(start, stop) where {T<:Real} = UnitRange{T}(convert(T, start), convert(T, stop))
```
-/
def UnitRange_T {T α β : Type} [JConvert T α] [JConvert T β] [JUnitrangeLast T T]
    (start : α) (stop : β) : JlX (UnitRange T) := do
  let a ← JConvert.convert (T := T) start
  let b ← JConvert.convert (T := T) stop
  UnitRange_T_new a b

/--
Julia source: base/range.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
```
-/
def UnitRange_T_T {T : Type} [JUnitRangeT T T T] (start stop : T) : JlX (UnitRange T) :=
  JUnitRangeT.unitRangeT start stop

/--
Julia source: base/range.jl:432-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function UnitRange(start, stop)
    startstop_promoted = promote(start, stop)
    not_sametype((start, stop), startstop_promoted)
    UnitRange(startstop_promoted...)
end
```
-/
def UnitRange_Any_Any {α β P ρ : Type} [JPromote2 α β P] [JNotSametype (α × β) (P × P)]
    [JUnitRange2 P P ρ] (start : α) (stop : β) : JlX ρ := do
  let startstop_promoted ← JPromote2.promote start stop
  JNotSametype.notSametype (start, stop) startstop_promoted
  JUnitRange2.unitRange startstop_promoted.1 startstop_promoted.2

/--
Julia source: base/range.jl:437-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# if stop and start are integral, we know that their difference is a multiple of 1
unitrange_last(start::Integer, stop::Integer) =
    stop >= start ? stop : convert(typeof(stop),
        _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
```
-/
def unitrange_last_Integer {A T D Q : Type} [JLe A T] [JRangeWrappingSub A T D] [JOneunit D]
    [JRangeWrappingSub A D Q] [JConvert T Q] (start : A) (stop : T) : JlX T :=
  if JLe.le start stop then pure stop
  else
    -- `oneunit(x)` depends only on the type of `x = _range_wrapping_sub(start, stop)`
    let _x : D := JRangeWrappingSub.rangeWrappingSub start stop
    JConvert.convert (T := T) (JRangeWrappingSub.rangeWrappingSub start (JOneunit.oneunit : D))

/--
Julia source: base/range.jl:442-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# otherwise, use `floor` as a more efficient way to compute modulus with step=1
unitrange_last(start, stop) =
    stop >= start ? convert(typeof(stop), start + floor(stop - start)) :
                    convert(typeof(stop), start - oneunit(start - stop))

```
-/
def unitrange_last_Any {T β D F E O : Type} [JLe T β] [HSub β T D] [JFloor D F] [HAdd T F E]
    [JConvert β E] [HSub T β D] [JOneunit D] [HSub T D O] [JConvert β O]
    (start : T) (stop : β) : JlX β :=
  if JLe.le start stop then do
    let f ← JFloor.floor (stop - start)
    JConvert.convert (T := β) (start + f)
  else
    -- `oneunit(x)` depends only on the type of `x = start - stop`
    let _x : D := start - stop
    JConvert.convert (T := β) (start - (JOneunit.oneunit : D))

/--
Julia source: base/range.jl:447-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unitrange(x::AbstractUnitRange) = UnitRange(x) # convenience conversion for promoting the range type

```
-/
def unitrange {R ρ : Type} [JCtor ρ R] (x : R) : JlX ρ := JCtor.ctor x

/-- `t[i]` for a tuple whose elements all have type `α`, modelled as a `List α`
(tuple.jl `getindex(t::Tuple, i::Int)`; other index types convert to `Int`). -/
class JTupleGetindex (I : Type) where
  tupleGetindex {α : Type} : List α → I → JlX α

/-- `front(t)` (tuple.jl) for a tuple modelled as a list; throws `ArgumentError` on `()`. -/
def tupleFront {α : Type} (t : List α) : JlX (List α) :=
  if t.isEmpty then throw (.jl (.argumentError "Cannot call front on an empty tuple."))
  else pure t.dropLast

/-- `tail(t)` (essentials.jl) for a tuple modelled as a list; throws `ArgumentError` on `()`. -/
def tupleTail {α : Type} (t : List α) : JlX (List α) :=
  if t.isEmpty then throw (.jl (.argumentError "Cannot call tail on an empty tuple."))
  else pure t.tail

/-- The loop `for x in r` collecting `f(x)`, following the iteration protocol for at most
`fuel` elements after the first. -/
def collectIter {R E St β : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R) (f : E → JlX β)
    (fuel : Nat) : JlX (List β) := do
  let rec go : Nat → St → List β → JlX (List β)
    | 0, _, _ => throw (.errorException "fuel")
    | n + 1, s, acc => do
        match ← JIterate2.iterate r s with
        | none => pure acc.reverse
        | some (x, s') => go n s' ((← f x) :: acc)
  match ← JIterate1.iterate r with
  | none => pure []
  | some (x, s) => go fuel s [← f x]

/--
Julia source: base/range.jl:449-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if isdefined(Main, :Base)
    # Constant-fold-able indexing into tuples to functionally expose Base.tail and Base.front
    function getindex(@nospecialize(t::Tuple), r::AbstractUnitRange)
        @inline
        require_one_based_indexing(r)
        if length(r) <= 10
            return ntuple(i -> t[i + first(r) - 1], length(r))
        elseif first(r) == 1
            last(r) == length(t)   && return t
            last(r) == length(t)-1 && return front(t)
            last(r) == length(t)-2 && return front(front(t))
        elseif last(r) == length(t)
            first(r) == 2 && return tail(t)
            first(r) == 3 && return tail(tail(t))
        end
        return (eltype(t)[t[ri] for ri in r]...,)
    end
end
```
-/
def getindex_Tuple_AbstractUnitRange {α R E St I : Type} [JRequireOneBased R] [JLength R JInt64]
    [JFirst R E] [JLast R E] [HAdd JInt64 E I] [HSub I JInt64 I] [JTupleGetindex I]
    [JTupleGetindex E] [JEq E JInt64] [JIterate1 R E St] [JIterate2 R St E]
    (t : List α) (r : R) (fuel : Nat) : JlX (List α) := do
  -- the tuple `t` is a `List α`: Julia's `ntuple` and splatted comprehension build tuples
  JRequireOneBased.requireOneBased r
  if (← JLength.length r).val ≤ 10 then
    let n ← JLength.length r
    -- `ntuple(f, n)` (ntuple.jl:17, 36): `ArgumentError` for a negative `n`, else `(f(1), ..., f(n))`
    if n.val < 0 then
      throw (.jl (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))
    return ← (List.range n.val.toNat).mapM fun (k : Nat) => do
      JTupleGetindex.tupleGetindex t (jint ((k : Int) + 1) + (← JFirst.first r) - jint 1)
  else if JEq.eq (← JFirst.first r) (jint 1) then
    if JEq.eq (← JLast.last r) (jint t.length) then return t
    if JEq.eq (← JLast.last r) (jint t.length - jint 1) then return ← tupleFront t
    if JEq.eq (← JLast.last r) (jint t.length - jint 2) then return ← tupleFront (← tupleFront t)
  else if JEq.eq (← JLast.last r) (jint t.length) then
    if JEq.eq (← JFirst.first r) (jint 2) then return ← tupleTail t
    if JEq.eq (← JFirst.first r) (jint 3) then return ← tupleTail (← tupleTail t)
  collectIter r (fun ri => JTupleGetindex.tupleGetindex t ri) fuel

/--
Julia source: base/range.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
```
-/
def OneTo_T.throwbool {α β : Type} [JPrint α] (r : α) : JlX β :=
  throw (.jl (.argumentError ("invalid index: " ++ JPrint.print r ++ " of type Bool")))

/--
Julia source: base/range.jl:487-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function OneTo{T}(stop) where {T<:Integer}
        throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
        T === Bool && throwbool(stop)
        return new(max(zero(T), stop))
    end

```
-/
def OneTo_T_stop {T α : Type} [JType T] [JPrint α] [JZero T] [JMax T α T] (stop : α) :
    JlX (OneTo T) := do
  if JType.isBool T then OneTo_T.throwbool stop
  return ⟨← JMax.max (JZero.zero : T) stop⟩

/--
Julia source: base/range.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
```
-/
def OneTo_T_range.throwstart {R T β : Type} [JFirst R T] [JPrint T] (r : R) : JlX β := do
  throw (.jl (.argumentError ("first element must be 1, got " ++ JPrint.print (← JFirst.first r))))

/--
Julia source: base/range.jl:495-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
```
-/
def OneTo_T_range.throwstep {R S β : Type} [JStep R S] [JPrint S] (r : R) : JlX β := do
  throw (.jl (.argumentError ("step must be 1, got " ++ JPrint.print (← JStep.step r))))

/--
Julia source: base/range.jl:496-496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
```
-/
def OneTo_T_range.throwbool {R β : Type} [JPrint R] (r : R) : JlX β :=
  throw (.jl (.argumentError ("invalid index: " ++ JPrint.print r ++ " of type Bool")))

/--
Julia source: base/range.jl:493-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function OneTo{T}(r::AbstractRange) where {T<:Integer}
        throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
        throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
        throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
        first(r) == 1 || throwstart(r)
        step(r)  == 1 || throwstep(r)
        T === Bool && throwbool(r)
        return new(max(zero(T), last(r)))
    end

```
-/
def OneTo_T_range {T R E S : Type} [JFirst R E] [JPrint E] [JEq E JInt64] [JStep R S] [JPrint S]
    [JEq S JInt64] [JType T] [JPrint R] [JLast R E] [JZero T] [JMax T E T] (r : R) :
    JlX (OneTo T) := do
  unless JEq.eq (← JFirst.first r) (jint 1) do OneTo_T_range.throwstart r
  unless JEq.eq (← JStep.step r) (jint 1) do OneTo_T_range.throwstep r
  if JType.isBool T then OneTo_T_range.throwbool r
  return ⟨← JMax.max (JZero.zero : T) (← JLast.last r)⟩

/--
Julia source: base/range.jl:503-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
end
```
-/
def unchecked_oneto {T : Type} (stop : T) : OneTo T := ⟨stop⟩

/--
Julia source: base/range.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
```
-/
def OneTo_stop {T : Type} [JOneToT T T] (stop : T) : JlX (OneTo T) := JOneToT.oneToT stop

/--
Julia source: base/range.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OneTo(r::AbstractRange{T}) where {T<:Integer} = OneTo{T}(r)
```
-/
def OneTo_AbstractRange {T R : Type} [JOneToT T R] (r : R) : JlX (OneTo T) := JOneToT.oneToT r

/--
Julia source: base/range.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneto(r) = OneTo(r)
```
-/
def oneto {R ρ : Type} [JOneTo1 R ρ] (r : R) : JlX ρ := JOneTo1.oneTo r

/--
Julia source: base/range.jl:533-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
        if T <: Integer && !isinteger(ref + step)
            throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
        end
        len = convert(L, len)
        len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
        offset = convert(L, offset)
        L1 = oneunit(typeof(len))
        L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
        return new(ref, step, len, offset)
    end
end

```
-/
def StepRangeLen_TRSL_new (T : Type) {R S X L Λ O : Type} [JType T] [HAdd R S X] [JIsinteger X]
    [JConvert L Λ] [JZero L] [JLe L L] [JPrint L] [JConvert L O] [JOneunit L] [JMax L L L]
    (ref : R) (step : S) (len : Λ) (offset : O) : JlX (StepRangeLen T R S L) := do
  if JType.isInteger T && !JIsinteger.isinteger (ref + step) then
    throw (.jl (.argumentError "StepRangeLen{<:Integer} cannot have non-integer step"))
  let len ← JConvert.convert (T := L) len
  unless JLe.le (JZero.zero : L) len do
    throw (.jl (.argumentError ("length cannot be negative, got " ++ JPrint.print len)))
  let offset ← JConvert.convert (T := L) offset
  let L1 : L := JOneunit.oneunit
  unless JLe.le L1 offset && JLe.le offset (← JMax.max L1 len) do
    throw (.jl (.argumentError ("StepRangeLen: offset must be in [1," ++ JPrint.print len ++
      "], got " ++ JPrint.print offset)))
  return ⟨ref, step, len, offset⟩

/--
Julia source: base/range.jl:546-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S} =
    StepRangeLen{T,R,S,promote_type(Int,typeof(len))}(ref, step, len, offset)
```
-/
def StepRangeLen_TRS {T R S Λ O L : Type} [JPromoteType JInt64 Λ L]
    [JStepRangeLenTRSL T R S L R S Λ O] (ref : R) (step : S) (len : Λ) (offset : O) :
    JlX (StepRangeLen T R S L) :=
  JStepRangeLenTRSL.stepRangeLenTRSL ref step len offset

/--
Julia source: base/range.jl:548-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S} =
    StepRangeLen{typeof(ref+zero(step)),R,S,promote_type(Int,typeof(len))}(ref, step, len, offset)
```
-/
def StepRangeLen_ref_step {R S Λ O L T : Type} [JZero S] [HAdd R S T] [JPromoteType JInt64 Λ L]
    [JStepRangeLenTRSL T R S L R S Λ O] (ref : R) (step : S) (len : Λ) (offset : O) :
    JlX (StepRangeLen T R S L) :=
  -- `typeof(ref+zero(step))` is the element type `T`
  let _t : T := ref + (JZero.zero : S)
  JStepRangeLenTRSL.stepRangeLenTRSL ref step len offset

/--
Julia source: base/range.jl:550-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S} =
    StepRangeLen{T,R,S,promote_type(Int,typeof(len))}(ref, step, len, offset)
```
-/
def StepRangeLen_T {T R S Λ O L : Type} [JPromoteType JInt64 Λ L]
    [JStepRangeLenTRSL T R S L R S Λ O] (ref : R) (step : S) (len : Λ) (offset : O) :
    JlX (StepRangeLen T R S L) :=
  JStepRangeLenTRSL.stepRangeLenTRSL ref step len offset


/-! ## `LinRange` constructors, `range_start_stop_length`, `show(::LinRange)` (lines 552-702) -/

/--
Julia source: base/range.jl:597-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}
        len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
        onelen = oneunit(typeof(len))
        if len == onelen
            start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ"))
            return new(start, stop, len, len)
        end
        lendiv = max(len - onelen, onelen)
        if T <: Integer && !iszero(mod(stop-start, lendiv))
            throw(ArgumentError("LinRange{<:Integer} cannot have non-integer step"))
        end
        return new(start, stop, len, lendiv)
    end
end

```
-/
def LinRange_TL_new {T L : Type} [JLe JInt64 L] [JPrint T] [JPrint L] [JOneunit L] [JEq L L]
    [JEq T T] [HSub L L L] [JMax L L L] [JType T] {D M : Type} [HSub T T D] [JMod D L M] [JIszero M]
    (start stop : T) (len : L) : JlX (LinRange T L) := do
  unless JLe.le (jint 0) len do
    throw (.jl (.argumentError ("range(" ++ JPrint.print start ++ ", stop=" ++ JPrint.print stop ++
      ", length=" ++ JPrint.print len ++ "): negative length")))
  let onelen : L := JOneunit.oneunit
  if JEq.eq len onelen then
    unless JEq.eq start stop do
      throw (.jl (.argumentError ("range(" ++ JPrint.print start ++ ", stop=" ++ JPrint.print stop ++
        ", length=" ++ JPrint.print len ++ "): endpoints differ")))
    return ⟨start, stop, len, len⟩
  let lendiv ← JMax.max (len - onelen) onelen
  if JType.isInteger T && !JIszero.iszero (← JMod.mod (stop - start) lendiv) then
    throw (.jl (.argumentError "LinRange{<:Integer} cannot have non-integer step"))
  return ⟨start, stop, len, lendiv⟩

/--
Julia source: base/range.jl:612-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function LinRange{T,L}(start, stop, len::Integer) where {T,L}
    LinRange{T,L}(convert(T, start), convert(T, stop), convert(L, len))
end

```
-/
def LinRange_TL {T L α β Λ : Type} [JConvert T α] [JConvert T β] [JConvert L Λ]
    [JLinRangeTL T L T T L] (start : α) (stop : β) (len : Λ) : JlX (LinRange T L) := do
  let a ← JConvert.convert (T := T) start
  let b ← JConvert.convert (T := T) stop
  let n ← JConvert.convert (T := L) len
  JLinRangeTL.linRangeTL a b n

/--
Julia source: base/range.jl:616-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function LinRange{T}(start, stop, len::Integer) where T
    LinRange{T,promote_type(Int,typeof(len))}(start, stop, len)
end

```
-/
def LinRange_T {T α β Λ L : Type} [JPromoteType JInt64 Λ L] [JLinRangeTL T L α β Λ]
    (start : α) (stop : β) (len : Λ) : JlX (LinRange T L) :=
  JLinRangeTL.linRangeTL start stop len

/--
Julia source: base/range.jl:620-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function LinRange(start, stop, len::Integer)
    T = typeof((zero(stop) - zero(start)) / oneunit(len))
    LinRange{T}(start, stop, len)
end

```
-/
def LinRange_start_stop_len {α β Λ D T ρ : Type} [JZero α] [JZero β] [HSub β α D] [JOneunit Λ]
    [HDiv D Λ T] [JLinRangeT T α β Λ ρ] (start : α) (stop : β) (len : Λ) : JlX ρ :=
  -- `T = typeof((zero(stop) - zero(start)) / oneunit(len))`
  let _t : T := ((JZero.zero : β) - (JZero.zero : α)) / (JOneunit.oneunit : Λ)
  JLinRangeT.linRangeT (T := T) start stop len

/--
Julia source: base/range.jl:625-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_stop_length(start, stop, len::Integer) =
    range_start_stop_length(promote(start, stop)..., len)
```
-/
def range_start_stop_length_Any {α β Λ P ρ : Type} [JPromote2 α β P]
    [JRangeStartStopLength P P Λ ρ] (start : α) (stop : β) (len : Λ) : JlX ρ := do
  let (a, b) ← JPromote2.promote start stop
  JRangeStartStopLength.rangeStartStopLength a b len

/--
Julia source: base/range.jl:627-627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_stop_length(start::T, stop::T, len::Integer) where {T} = LinRange(start, stop, len)
```
-/
def range_start_stop_length_T {T Λ ρ : Type} [JLinRange3 T T Λ ρ] (start stop : T) (len : Λ) :
    JlX ρ :=
  JLinRange3.linRange start stop len

/--
Julia source: base/range.jl:628-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
range_start_stop_length(start::T, stop::T, len::Integer) where {T<:Integer} =
    _linspace(float(T), start, stop, len)
```
-/
def range_start_stop_length_Integer {T Λ F ρ : Type} [JFloatType T F] [JLinspace F T T Λ ρ]
    (start stop : T) (len : Λ) : JlX ρ :=
  JLinspace.linspace (T := F) start stop len

/--
Julia source: base/range.jl:630-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## for Float16, Float32, and Float64 we hit twiceprecision.jl to lift to higher precision StepRangeLen
# for all other types we fall back to a plain old LinRange
_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where T = LinRange{T}(start, stop, len)

```
-/
def _linspace (T : Type) {α β Λ ρ : Type} [JLinRangeT T α β Λ ρ] (start : α) (stop : β)
    (len : Λ) : JlX ρ :=
  JLinRangeT.linRangeT (T := T) start stop len

/-- `show(IOContext(io, :typeinfo => T), x)`. -/
class JShowTypeinfo (T α : Type) where
  showTypeinfo : α → JlX String

/--
Julia source: base/range.jl:634-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, r::LinRange{T}) where {T}
    print(io, "LinRange{")
    show(io, T)
    print(io, "}(")
    ioc = IOContext(io, :typeinfo=>T)
    show(ioc, first(r))
    print(io, ", ")
    show(ioc, last(r))
    print(io, ", ")
    show(io, length(r))
    print(io, ')')
end

```
-/
def show_LinRange {T L Λ : Type} [JShowType T] [JFirst (LinRange T L) T] [JLast (LinRange T L) T]
    [JShowTypeinfo T T] [JLength (LinRange T L) Λ] [JShow Λ] (io : JIO) (r : LinRange T L) :
    JlX String := do
  let mut out := "LinRange{"
  out := out ++ JShowType.showType T
  out := out ++ "}("
  let _ioc : IOTypeinfo T := ⟨io⟩
  out := out ++ (← JShowTypeinfo.showTypeinfo (T := T) (← JFirst.first r))
  out := out ++ ", "
  out := out ++ (← JShowTypeinfo.showTypeinfo (T := T) (← JLast.last r))
  out := out ++ ", "
  out := out ++ (← JShow.showValue (← JLength.length r))
  out := out ++ ")"
  return out

-- Reason: terminal-layout printing helper for `show(::MIME"text/plain", r)`: depends on `displaysize`, `alignment` and `print_matrix_row` (arrayshow.jl); its output is not a property of the range values.
-- UNTRANSLATED
-- Source: base/range.jl:647-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
-- `print_range(io, r)` prints out a nice looking range r in terms of its elements
-- as if it were `collect(r)`, dependent on the size of the
-- terminal, and taking into account whether compact numbers should be shown.
-- It figures out the width in characters of each element, and if they
-- end up too wide, it shows the first and last elements separated by a
-- horizontal ellipsis. Typical output will look like `1.0, 2.0, …, 5.0, 6.0`.
-- 
-- `print_range(io, r, pre, sep, post, hdots)` uses optional
-- parameters `pre` and `post` characters for each printed row,
-- `sep` separator string between printed elements,
-- `hdots` string for the horizontal ellipsis.
-- """
-- function print_range(io::IO, r::AbstractArray,
--                      pre::AbstractString = " ",
--                      sep::AbstractString = ", ",
--                      post::AbstractString = "",
--                      hdots::AbstractString = ", \u2026, ") # horiz ellipsis
--     # This function borrows from print_matrix() in show.jl
--     # and should be called by show and display
--     sz = displaysize(io)
--     if !haskey(io, :compact)
--         io = IOContext(io, :compact => true)
--     end
--     _, screenwidth = sz[1] - 4, sz[2]
--     screenwidth -= length(pre) + length(post)
--     sepsize = length(sep)
--     m = 1 # treat the range as a one-row matrix
--     n = length(r)
--     # Figure out spacing alignments for r, but only need to examine the
--     # left and right edge columns, as many as could conceivably fit on the
--     # screen, with the middle columns summarized by horz, vert, or diag ellipsis
--     maxpossiblecols = div(screenwidth, 1+sepsize) # assume each element is at least 1 char + 1 separator
--     colsr = n <= maxpossiblecols ? (1:n) : [1:div(maxpossiblecols,2)+1; (n-div(maxpossiblecols,2)):n]
--     rowmatrix = reshape(r[colsr], 1, length(colsr)) # treat the range as a one-row matrix for print_matrix_row
--     nrow, idxlast = size(rowmatrix, 2), last(axes(rowmatrix, 2))
--     A = alignment(io, rowmatrix, 1:m, 1:length(rowmatrix), screenwidth, screenwidth, sepsize, nrow) # how much space range takes
--     if n <= length(A) # cols fit screen, so print out all elements
--         print(io, pre) # put in pre chars
--         print_matrix_row(io,rowmatrix,A,1,1:n,sep,idxlast) # the entire range
--         print(io, post) # add the post characters
--     else # cols don't fit so put horiz ellipsis in the middle
--         # how many chars left after dividing width of screen in half
--         # and accounting for the horiz ellipsis
--         c = div(screenwidth-length(hdots)+1,2)+1 # chars remaining for each side of rowmatrix
--         alignR = reverse(alignment(io, rowmatrix, 1:m, length(rowmatrix):-1:1, c, c, sepsize, nrow)) # which cols of rowmatrix to put on the right
--         c = screenwidth - sum(map(sum,alignR)) - (length(alignR)-1)*sepsize - length(hdots)
--         alignL = alignment(io, rowmatrix, 1:m, 1:length(rowmatrix), c, c, sepsize, nrow) # which cols of rowmatrix to put on the left
--         print(io, pre)   # put in pre chars
--         print_matrix_row(io, rowmatrix,alignL,1,1:length(alignL),sep,idxlast) # left part of range
--         print(io, hdots) # horizontal ellipsis
--         print_matrix_row(io, rowmatrix,alignR,1,length(rowmatrix)-length(alignR)+1:length(rowmatrix),sep,idxlast) # right part of range
--         print(io, post)  # post chars
--     end
-- end
-- 
-- /Source

/-! ## Interface implementations: `length`, `isempty`, `step` (lines 703-866) -/

/--
Julia source: base/range.jl:703-705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## interface implementations

length(r::AbstractRange) = error("length implementation missing") # catch mistakes
```
-/
def length_AbstractRange {R : Type} {α : Type} (r : R) : JlX α :=
  throw (.errorException "length implementation missing")

/--
Julia source: base/range.jl:706-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(r::AbstractRange) = (@inline; (length(r),))

```
-/
def size_AbstractRange {R L : Type} [JLength R L] (r : R) : JlX (Tuple1 L) := do
  return ⟨← JLength.length r⟩

/--
Julia source: base/range.jl:708-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(r::StepRange) =
    # steprange_last(r.start, r.step, r.stop) == r.stop
    (r.start != r.stop) & ((r.step > zero(r.step)) != (r.stop > r.start))
```
-/
def isempty_StepRange {T S : Type} [JEq T T] [JZero S] [JLt S S] [JLt T T] (r : StepRange T S) :
    Bool :=
  (!JEq.eq r.start r.stop) && (JLt.lt (JZero.zero : S) r.step != JLt.lt r.start r.stop)

/--
Julia source: base/range.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(r::AbstractUnitRange) = first(r) > last(r)
```
-/
def isempty_AbstractUnitRange {R T : Type} [JFirst R T] [JLast R T] [JLt T T] (r : R) :
    JlX Bool := do
  let f ← JFirst.first r
  let l ← JLast.last r
  return JLt.lt l f

/--
Julia source: base/range.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(r::StepRangeLen) = length(r) == 0
```
-/
def isempty_StepRangeLen {T R S L Λ : Type} [JLength (StepRangeLen T R S L) Λ] [JEq Λ JInt64]
    (r : StepRangeLen T R S L) : JlX Bool := do
  return JEq.eq (← JLength.length r) (jint 0)

/--
Julia source: base/range.jl:713-714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(r::LinRange) = length(r) == 0

```
-/
def isempty_LinRange {T L Λ : Type} [JLength (LinRange T L) Λ] [JEq Λ JInt64] (r : LinRange T L) :
    JlX Bool := do
  return JEq.eq (← JLength.length r) (jint 0)

/--
Julia source: base/range.jl:715-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    step(r)

Get the step size of an [`AbstractRange`](@ref) object.

# Examples
```jldoctest
julia> step(1:10)
1

julia> step(1:2:10)
2

julia> step(2.5:0.3:10.9)
0.3

julia> step(range(2.5, stop=10.9, length=85))
0.1
```
"""
step(r::StepRange) = r.step
````
-/
def step_StepRange {T S : Type} (r : StepRange T S) : S := r.step

/--
Julia source: base/range.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::AbstractUnitRange{T}) where {T} = oneunit(T) - zero(T)
```
-/
def step_AbstractUnitRange {R T D : Type} [JEltype R T] [JOneunit T] [JZero T] [HSub T T D]
    (r : R) : D :=
  (JOneunit.oneunit : T) - (JZero.zero : T)

/--
Julia source: base/range.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::AbstractUnitRange{Bool}) = true
```
-/
def step_AbstractUnitRange_Bool {R : Type} (r : R) : Bool := true

/--
Julia source: base/range.jl:738-738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::StepRangeLen) = r.step
```
-/
def step_StepRangeLen {T R S L : Type} (r : StepRangeLen T R S L) : S := r.step

/--
Julia source: base/range.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
```
-/
def step_StepRangeLen_AbstractFloat {T R S L : Type} [JCtor T S] (r : StepRangeLen T R S L) :
    JlX T :=
  JCtor.ctor r.step

/--
Julia source: base/range.jl:740-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step(r::LinRange) = (last(r)-first(r))/r.lendiv

```
-/
def step_LinRange {T L D Q : Type} [JLast (LinRange T L) T] [JFirst (LinRange T L) T] [HSub T T D]
    [HDiv D L Q] (r : LinRange T L) : JlX Q := do
  let l ← JLast.last r
  let f ← JFirst.first r
  return (l - f) / r.lendiv

/--
Julia source: base/range.jl:742-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# high-precision step
step_hp(r::StepRangeLen) = r.step
```
-/
def step_hp_StepRangeLen {T R S L : Type} (r : StepRangeLen T R S L) : S := r.step

/--
Julia source: base/range.jl:744-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
step_hp(r::AbstractRange) = step(r)

```
-/
def step_hp_AbstractRange {R S : Type} [JStep R S] (r : R) : JlX S := JStep.step r

/--
Julia source: base/range.jl:746-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Needed to ensure `has_offset_axes` can constant-fold.
has_offset_axes(::StepRange) = false
```
-/
def has_offset_axes_StepRange {T S : Type} (r : StepRange T S) : Bool := false

/--
Julia source: base/range.jl:748-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# n.b. checked_length for these is defined iff checked_add and checked_sub are
# defined between the relevant types
function checked_length(r::OrdinalRange{T}) where T
    s = step(r)
    start = first(r)
    if isempty(r)
        return Integer(div(start - start, oneunit(s)))
    end
    stop = last(r)
    if isless(s, zero(s))
        diff = checked_sub(start, stop)
        s = -s
    else
        diff = checked_sub(stop, start)
    end
    a = div(diff, s)
    return Integer(checked_add(a, oneunit(a)))
end
```
-/
def checked_length_OrdinalRange {R S T D Q N I A J : Type} [JStep R S] [JFirst R T] [JIsempty R]
    [HSub T T D] [JOneunit S] [JDiv D S Q] [JInteger Q I] [JLast R T] [JIsless S S] [JZero S]
    [JCheckedSub T T D] [JNeg S N] [JDiv D (S ⊕ N) A] [JOneunit A] [JCheckedAdd A A A]
    [JInteger A J] (r : R) : JlX (I ⊕ J) := do
  let s ← JStep.step r
  let start ← JFirst.first r
  if ← JIsempty.isempty r then
    return .inl (← JInteger.integer (← JDiv.div (start - start) (JOneunit.oneunit : S)))
  let stop ← JLast.last r
  let (diff, s) : D × (S ⊕ N) ← if JIsless.isless s (JZero.zero : S) then do
      let diff ← JCheckedSub.checkedSub start stop
      pure (diff, .inr (JNeg.neg s))
    else do
      let diff ← JCheckedSub.checkedSub stop start
      pure (diff, .inl s)
  let a ← JDiv.div diff s
  return .inr (← JInteger.integer (← JCheckedAdd.checkedAdd a (JOneunit.oneunit : A)))

/--
Julia source: base/range.jl:767-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function checked_length(r::AbstractUnitRange{T}) where T
    # compiler optimization: remove dead cases from above
    if isempty(r)
        return Integer(first(r) - first(r))
    end
    a = checked_sub(last(r), first(r))
    return Integer(checked_add(a, oneunit(a)))
end
```
-/
def checked_length_AbstractUnitRange {R T D I A J : Type} [JIsempty R] [JFirst R T] [HSub T T D]
    [JInteger D I] [JLast R T] [JCheckedSub T T A] [JOneunit A] [JCheckedAdd A A A] [JInteger A J]
    (r : R) : JlX (I ⊕ J) := do
  if ← JIsempty.isempty r then
    let f1 ← JFirst.first r
    let f2 ← JFirst.first r
    return .inl (← JInteger.integer (f1 - f2))
  let a ← JCheckedSub.checkedSub (← JLast.last r) (← JFirst.first r)
  return .inr (← JInteger.integer (← JCheckedAdd.checkedAdd a (JOneunit.oneunit : A)))

/--
Julia source: base/range.jl:776-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function length(r::OrdinalRange{T}) where T
    s = step(r)
    start = first(r)
    if isempty(r)
        return Integer(div(start - start, oneunit(s)))
    end
    stop = last(r)
    if isless(s, zero(s))
        diff = start - stop
        s = -s
    else
        diff = stop - start
    end
    a = div(diff, s)
    return Integer(a + oneunit(a))
end
```
-/
def length_OrdinalRange {R S T D Q N I A J : Type} [JStep R S] [JFirst R T] [JIsempty R]
    [HSub T T D] [JOneunit S] [JDiv D S Q] [JInteger Q I] [JLast R T] [JIsless S S] [JZero S]
    [JNeg S N] [JDiv D (S ⊕ N) A] [JOneunit A] [HAdd A A A] [JInteger A J] (r : R) :
    JlX (I ⊕ J) := do
  let s ← JStep.step r
  let start ← JFirst.first r
  if ← JIsempty.isempty r then
    return .inl (← JInteger.integer (← JDiv.div (start - start) (JOneunit.oneunit : S)))
  let stop ← JLast.last r
  let (diff, s) : D × (S ⊕ N) := if JIsless.isless s (JZero.zero : S) then
      (start - stop, .inr (JNeg.neg s))
    else (stop - start, .inl s)
  let a ← JDiv.div diff s
  return .inr (← JInteger.integer (a + (JOneunit.oneunit : A)))

/--
Julia source: base/range.jl:793-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function length(r::AbstractUnitRange{T}) where T
    @inline
    start, stop = first(r), last(r)
    a = oneunit(zero(stop) - zero(start))
    if a isa Signed || stop >= start
        a += stop - start # Signed are allowed to go negative
    else
        a = zero(a) # Unsigned don't necessarily underflow
    end
    return Integer(a)
end

```
-/
def length_AbstractUnitRange {R T D I : Type} [JFirst R T] [JLast R T] [JZero T] [HSub T T D]
    [JOneunit D] [JType D] [JLe T T] [HAdd D D D] [JZero D] [JInteger D I] (r : R) : JlX I := do
  let start ← JFirst.first r
  let stop ← JLast.last r
  let mut a : D := JOneunit.oneunit
  if JType.isSigned D || JLe.le start stop then
    a := a + (stop - start)
  else
    a := JZero.zero
  JInteger.integer a

/--
Julia source: base/range.jl:806-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::OneTo) = Integer(r.stop - zero(r.stop))
```
-/
def length_OneTo {T D I : Type} [JZero T] [HSub T T D] [JInteger D I] (r : OneTo T) : JlX I :=
  JInteger.integer (r.stop - (JZero.zero : T))

/--
Julia source: base/range.jl:807-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::StepRangeLen) = r.len
```
-/
def length_StepRangeLen {T R S L : Type} (r : StepRangeLen T R S L) : L := r.len

/--
Julia source: base/range.jl:808-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::LinRange) = r.len

```
-/
def length_LinRange {T L : Type} (r : LinRange T L) : L := r.len

/--
Julia source: base/range.jl:810-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
    smallints = (Int === Int64 ?
                Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
                Union{Int8, UInt8, Int16, UInt16}),
    bitints = Union{bigints, smallints}
    global length, checked_length, firstindex
    # compile optimization for which promote_type(T, Int) == T
    length(r::OneTo{T}) where {T<:bigints} = r.stop
```
-/
def length_OneTo_bigints {T : Type} (r : OneTo T) : T := r.stop

/-- `x % T` for integers (`rem(x, T)`): conversion to `T` by wrapping. -/
class JRemType (T α : Type) where
  remType : α → T

/--
Julia source: base/range.jl:818-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    # slightly more accurate length and checked_length in extreme cases
    # (near typemax) for types with known `unsigned` functions
    function length(r::OrdinalRange{T}) where T<:bigints
        s = step(r)
        diff = last(r) -% first(r)
        isempty(r) && return zero(diff)
        # Compute `(diff ÷ s) + 1` in a manner robust to signed overflow
        # by using the absolute values as unsigneds for non-empty ranges.
        # Note that `s` may be a different type from T and diff; it may not
        # even be a BitInteger that supports `unsigned`. Handle with care.
        a = div(unsigned(flipsign(diff, s)), s) % typeof(diff)
        return flipsign(a, s) + oneunit(a)
    end
```
-/
def length_OrdinalRange_bigints {R S T D U Q : Type} [JStep R S] [JLast R T] [JFirst R T]
    [JWrappingSub T T D] [JIsempty R] [JZero D] [JFlipsign D S] [JUnsigned D U] [JDiv U S Q]
    [JRemType D Q] [JOneunit D] [HAdd D D D] (r : R) : JlX D := do
  let s ← JStep.step r
  let diff := JWrappingSub.wrappingSub (← JLast.last r) (← JFirst.first r)
  if ← JIsempty.isempty r then return JZero.zero
  let a : D := JRemType.remType (← JDiv.div (JUnsigned.unsigned (JFlipsign.flipsign diff s)) s)
  return JFlipsign.flipsign a s + JOneunit.oneunit

/--
Julia source: base/range.jl:831-849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function checked_length(r::OrdinalRange{T}) where T<:bigints
        s = step(r)
        stop, start = last(r), first(r)
        ET = promote_type(typeof(stop), typeof(start))
        isempty(r) && return zero(ET)
        # n.b. !(s isa T)
        if s > 1
            diff = stop -% start
            a = convert(ET, div(unsigned(diff), s))
        elseif s < -1
            diff = start -% stop
            a = convert(ET, div(unsigned(diff), -s))
        elseif s > 0
            a = convert(ET, div(checked_sub(stop, start), s))
        else
            a = convert(ET, div(checked_sub(start, stop), -s))
        end
        return checked_add(a, oneunit(a))
    end
```
-/
def checked_length_OrdinalRange_bigints {R S T ET D U Q1 Q2 Q3 Q4 N : Type} [JStep R S]
    [JLast R T] [JFirst R T] [JPromoteType T T ET] [JIsempty R] [JZero ET] [JLt JInt64 S]
    [JLt S JInt64] [JWrappingSub T T D] [JUnsigned D U] [JDiv U S Q1] [JConvert ET Q1] [JNeg S N]
    [JDiv U N Q2] [JConvert ET Q2] [JCheckedSub T T D] [JDiv D S Q3] [JConvert ET Q3]
    [JDiv D N Q4] [JConvert ET Q4] [JOneunit ET] [JCheckedAdd ET ET ET] (r : R) : JlX ET := do
  let s ← JStep.step r
  let stop ← JLast.last r
  let start ← JFirst.first r
  if ← JIsempty.isempty r then return JZero.zero
  let a : ET ←
    if JLt.lt (jint 1) s then do
      let diff := JWrappingSub.wrappingSub stop start
      JConvert.convert (← JDiv.div (JUnsigned.unsigned diff) s)
    else if JLt.lt s (jint (-1)) then do
      let diff := JWrappingSub.wrappingSub start stop
      JConvert.convert (← JDiv.div (JUnsigned.unsigned diff) (JNeg.neg s))
    else if JLt.lt (jint 0) s then do
      JConvert.convert (← JDiv.div (← JCheckedSub.checkedSub stop start) s)
    else do
      JConvert.convert (← JDiv.div (← JCheckedSub.checkedSub start stop) (JNeg.neg s))
  JCheckedAdd.checkedAdd a (JOneunit.oneunit : ET)

/--
Julia source: base/range.jl:850-852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    firstindex(r::StepRange{<:bigints,<:bitints}) = one(last(r)-first(r))

    # some special cases to favor default Int type
```
-/
def firstindex_StepRange_bigints {T S D : Type} [JLast (StepRange T S) T] [JFirst (StepRange T S) T]
    [HSub T T D] [JOne D] (r : StepRange T S) : JlX D := do
  let l ← JLast.last r
  let f ← JFirst.first r
  let _d : D := l - f
  return JOne.one

/--
Julia source: base/range.jl:853-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function length(r::OrdinalRange{<:smallints})
        s = step(r)
        isempty(r) && return 0
        # n.b. !(step isa T)
        return Int(div(Int(last(r)) - Int(first(r)), s)) + 1
    end
```
-/
def length_OrdinalRange_smallints {R S T Q : Type} [JStep R S] [JIsempty R] [JLast R T]
    [JFirst R T] [JCtor JInt64 T] [JDiv JInt64 S Q] [JCtor JInt64 Q] (r : R) : JlX JInt64 := do
  let s ← JStep.step r
  if ← JIsempty.isempty r then return jint 0
  let l : JInt64 ← JCtor.ctor (← JLast.last r)
  let f : JInt64 ← JCtor.ctor (← JFirst.first r)
  let q : JInt64 ← JCtor.ctor (← JDiv.div (l - f) s)
  return q + jint 1

/--
Julia source: base/range.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(r::AbstractUnitRange{<:smallints}) = Int(last(r)) - Int(first(r)) + 1
```
-/
def length_AbstractUnitRange_smallints {R T : Type} [JLast R T] [JFirst R T] [JCtor JInt64 T]
    (r : R) : JlX JInt64 := do
  let l : JInt64 ← JCtor.ctor (← JLast.last r)
  let f : JInt64 ← JCtor.ctor (← JFirst.first r)
  return l - f + jint 1

/--
Julia source: base/range.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(r::OneTo{<:smallints}) = Int(r.stop)
```
-/
def length_OneTo_smallints {T : Type} [JCtor JInt64 T] (r : OneTo T) : JlX JInt64 :=
  JCtor.ctor r.stop

/--
Julia source: base/range.jl:861-861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    checked_length(r::OrdinalRange{<:smallints}) = length(r)
```
-/
def checked_length_OrdinalRange_smallints {R L : Type} [JLength R L] (r : R) : JlX L :=
  JLength.length r

/--
Julia source: base/range.jl:862-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    checked_length(r::AbstractUnitRange{<:smallints}) = length(r)
```
-/
def checked_length_AbstractUnitRange_smallints {R L : Type} [JLength R L] (r : R) : JlX L :=
  JLength.length r

/--
Julia source: base/range.jl:863-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    checked_length(r::OneTo{<:smallints}) = length(r)
```
-/
def checked_length_OneTo_smallints {T L : Type} [JLength (OneTo T) L] (r : OneTo T) : JlX L :=
  JLength.length r

/--
Julia source: base/range.jl:864-866 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    firstindex(::StepRange{<:smallints,<:bitints}) = 1
end

```
-/
def firstindex_StepRange_smallints {T S : Type} (r : StepRange T S) : JInt64 := jint 1


/-! ## `first`, `last`, extrema, iteration and scalar indexing (lines 867-999) -/

/-- The value `x : S` as a `Bool`, in a branch where Julia has established `S === Bool`. -/
def asBool {S : Type} [JType S] (h : JType.isBool S = true) (x : S) : Bool :=
  cast (JType.bool_eq h) x

/--
Julia source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
```
-/
def first_OrdinalRange {R T A : Type} [JEltype R T] [JFieldStart R A] [JConvert T A] (r : R) :
    JlX T :=
  JConvert.convert (JFieldStart.start r)

/--
Julia source: base/range.jl:868-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::OneTo{T}) where {T} = oneunit(T)
```
-/
def first_OneTo {T : Type} [JOneunit T] (r : OneTo T) : T := JOneunit.oneunit

/--
Julia source: base/range.jl:869-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::StepRangeLen) = unsafe_getindex(r, 1)
```
-/
def first_StepRangeLen {T R S L : Type} [JUnsafeGetindex (StepRangeLen T R S L) JInt64 T]
    (r : StepRangeLen T R S L) : JlX T :=
  JUnsafeGetindex.unsafeGetindex r (jint 1)

/--
Julia source: base/range.jl:870-871 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::LinRange) = r.start

```
-/
def first_LinRange {T L : Type} (r : LinRange T L) : T := r.start

/--
Julia source: base/range.jl:872-876 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first(r::OneTo, n::Integer)
    n < 0 && throw(ArgumentError("Number of elements must be non-negative"))
    OneTo(oftype(r.stop, min(r.stop, n)))
end

```
-/
def first_OneTo_n {T I M : Type} [JLt I JInt64] [JMin T I M] [JConvert T M] [JOneTo1 T (OneTo T)]
    (r : OneTo T) (n : I) : JlX (OneTo T) := do
  if JLt.lt n (jint 0) then throw (.jl (.argumentError "Number of elements must be non-negative"))
  JOneTo1.oneTo (← oftype r.stop (← JMin.min r.stop n))

/--
Julia source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
```
-/
def last_OrdinalRange {R T A : Type} [JEltype R T] [JFieldStop R A] [JConvert T A] (r : R) :
    JlX T :=
  JConvert.convert (JFieldStop.stop r)

/--
Julia source: base/range.jl:878-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::StepRangeLen) = unsafe_getindex(r, length(r))
```
-/
def last_StepRangeLen {T R S L : Type} [JLength (StepRangeLen T R S L) L]
    [JUnsafeGetindex (StepRangeLen T R S L) L T] (r : StepRangeLen T R S L) : JlX T := do
  JUnsafeGetindex.unsafeGetindex r (← JLength.length r)

/--
Julia source: base/range.jl:879-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::LinRange) = r.stop

```
-/
def last_LinRange {T L : Type} (r : LinRange T L) : T := r.stop

/--
Julia source: base/range.jl:881-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(r::AbstractUnitRange) = isempty(r) ? throw(ArgumentError("range must be non-empty")) : first(r)
```
-/
def minimum_AbstractUnitRange {R T : Type} [JIsempty R] [JFirst R T] (r : R) : JlX T := do
  if ← JIsempty.isempty r then throw (.jl (.argumentError "range must be non-empty"))
  JFirst.first r

/--
Julia source: base/range.jl:882-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(r::AbstractUnitRange) = isempty(r) ? throw(ArgumentError("range must be non-empty")) : last(r)
```
-/
def maximum_AbstractUnitRange {R T : Type} [JIsempty R] [JLast R T] (r : R) : JlX T := do
  if ← JIsempty.isempty r then throw (.jl (.argumentError "range must be non-empty"))
  JLast.last r

/--
Julia source: base/range.jl:883-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(r::AbstractRange)  = isempty(r) ? throw(ArgumentError("range must be non-empty")) : min(first(r), last(r))
```
-/
def minimum_AbstractRange {R T M : Type} [JIsempty R] [JFirst R T] [JLast R T] [JMin T T M]
    (r : R) : JlX M := do
  if ← JIsempty.isempty r then throw (.jl (.argumentError "range must be non-empty"))
  JMin.min (← JFirst.first r) (← JLast.last r)

/--
Julia source: base/range.jl:884-885 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(r::AbstractRange)  = isempty(r) ? throw(ArgumentError("range must be non-empty")) : max(first(r), last(r))

```
-/
def maximum_AbstractRange {R T M : Type} [JIsempty R] [JFirst R T] [JLast R T] [JMax T T M]
    (r : R) : JlX M := do
  if ← JIsempty.isempty r then throw (.jl (.argumentError "range must be non-empty"))
  JMax.max (← JFirst.first r) (← JLast.last r)

/--
Julia source: base/range.jl:886-901 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    argmin(r::AbstractRange)

Ranges can have multiple minimal elements. In that case
`argmin` will return a minimal index, but not necessarily the
first one.
"""
function argmin(r::AbstractRange)
    if isempty(r)
        throw(ArgumentError("range must be non-empty"))
    elseif step(r) > 0
        firstindex(r)
    else
        lastindex(r)
    end
end
```
-/
def argmin_AbstractRange {R S I : Type} [JIsempty R] [JStep R S] [JLt JInt64 S] [JFirstindex R I]
    [JLastindex R I] (r : R) : JlX I := do
  if ← JIsempty.isempty r then
    throw (.jl (.argumentError "range must be non-empty"))
  else if JLt.lt (jint 0) (← JStep.step r) then
    JFirstindex.firstindex r
  else
    JLastindex.lastindex r

/--
Julia source: base/range.jl:902-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    argmax(r::AbstractRange)

Ranges can have multiple maximal elements. In that case
`argmax` will return a maximal index, but not necessarily the
first one.
"""
function argmax(r::AbstractRange)
    if isempty(r)
        throw(ArgumentError("range must be non-empty"))
    elseif step(r) > 0
        lastindex(r)
    else
        firstindex(r)
    end
end
```
-/
def argmax_AbstractRange {R S I : Type} [JIsempty R] [JStep R S] [JLt JInt64 S] [JFirstindex R I]
    [JLastindex R I] (r : R) : JlX I := do
  if ← JIsempty.isempty r then
    throw (.jl (.argumentError "range must be non-empty"))
  else if JLt.lt (jint 0) (← JStep.step r) then
    JLastindex.lastindex r
  else
    JFirstindex.firstindex r

/--
Julia source: base/range.jl:919-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

extrema(r::AbstractRange) = (minimum(r), maximum(r))
```
-/
def extrema_AbstractRange {R A B : Type} [JMinimum R A] [JMaximum R B] (r : R) : JlX (A × B) := do
  let a ← JMinimum.minimum r
  let b ← JMaximum.maximum r
  return (a, b)

/--
Julia source: base/range.jl:921-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Ranges are immutable
copy(r::AbstractRange) = r


## iteration

```
-/
def copy_AbstractRange {R : Type} (r : R) : R := r

/--
Julia source: base/range.jl:928-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))
    @inline
    i += oneunit(i)
    length(r) < i && return nothing
    unsafe_getindex(r, i), i
end

```
-/
def iterate_StepRangeLen_LinRange {R I L T : Type} [JOneunit I] [HAdd I I I] [JLength R L]
    [JLt L I] [JUnsafeGetindex R I T] (r : R) (i : I) : JlX (Option (T × I)) := do
  let i := i + (JOneunit.oneunit : I)
  if JLt.lt (← JLength.length r) i then return none
  return some (← JUnsafeGetindex.unsafeGetindex r i, i)

/--
Julia source: base/range.jl:928-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))
    @inline
    i += oneunit(i)
    length(r) < i && return nothing
    unsafe_getindex(r, i), i
end

```
-/
def iterate_StepRangeLen_LinRange_default {R L T : Type} [JLength R L] [JZero L]
    [JIterate2 R L T] (r : R) : JlX (Option (T × L)) := do
  let _l ← JLength.length r
  JIterate2.iterate r (JZero.zero : L)

/--
Julia source: base/range.jl:935-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))

```
-/
def iterate_OrdinalRange {R T : Type} [JIsempty R] [JFirst R T] (r : R) : JlX (Option (T × T)) := do
  if ← JIsempty.isempty r then return none
  return some (← JFirst.first r, ← JFirst.first r)

/--
Julia source: base/range.jl:937-945 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(r::OrdinalRange{T}, i) where {T}
    @inline
    i == last(r) && return nothing
    next = convert(T, i + step(r))
    (next, next)
end

## indexing

```
-/
def iterate_OrdinalRange_state {R T I S E : Type} [JEltype R T] [JLast R T] [JEq I T] [JStep R S]
    [HAdd I S E] [JConvert T E] (r : R) (i : I) : JlX (Option (T × T)) := do
  if JEq.eq i (← JLast.last r) then return none
  let next ← JConvert.convert (T := T) (i + (← JStep.step r))
  return some (next, next)

/--
Julia source: base/range.jl:946-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(r::AbstractRange, i::Integer)
    i isa Bool && throw(ArgumentError("invalid index: $i of type Bool"))
    firstindex(r) <= i <= lastindex(r)
end

```
-/
def isassigned_AbstractRange {R I J : Type} [JType I] [JPrint I] [JFirstindex R J]
    [JLastindex R J] [JLe J I] [JLe I J] (r : R) (i : I) : JlX Bool := do
  if JType.isBool I then throw (.jl (.argumentError ("invalid index: " ++ JPrint.print i ++
    " of type Bool")))
  let lo ← JFirstindex.firstindex r
  if !JLe.le lo i then return false
  return JLe.le i (← JLastindex.lastindex r)

/--
Julia source: base/range.jl:951-956 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `_getindex` is like `getindex` but does not check if `i isa Bool`
function _getindex(v::AbstractRange, i::Integer)
    @boundscheck checkbounds(v, i)
    unsafe_getindex(v, i)
end

```
-/
def _getindex_AbstractRange {R I T : Type} [JCheckbounds R I] [JUnsafeGetindex R I T]
    (v : R) (i : I) : JlX T := do
  JCheckbounds.checkbounds v i
  JUnsafeGetindex.unsafeGetindex v i

/--
Julia source: base/range.jl:957-958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_in_unit_range(v::UnitRange, val, i::Integer) = i > 0 && val <= v.stop && val >= v.start

```
-/
def _in_unit_range {T V I : Type} [JLt JInt64 I] [JLe V T] [JLe T V] (v : UnitRange T) (val : V)
    (i : I) : Bool :=
  JLt.lt (jint 0) i && JLe.le val v.stop && JLe.le v.start val

/--
Julia source: base/range.jl:959-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(v::UnitRange{T}, i::Integer) where T
    val = convert(T, v.start + (i - oneunit(i)))
    @boundscheck _in_unit_range(v, val, i) || throw_boundserror(v, i)
    val
end

```
-/
def _getindex_UnitRange {T I D E : Type} [JOneunit I] [HSub I I D] [HAdd T D E] [JConvert T E]
    [JLt JInt64 I] [JLe T T] [JThrowBoundserror (UnitRange T) I] (v : UnitRange T) (i : I) :
    JlX T := do
  let val ← JConvert.convert (T := T) (v.start + (i - (JOneunit.oneunit : I)))
  unless _in_unit_range v val i do
    let e ← JThrowBoundserror.throwBoundserror v i
    Empty.elim e
  return val

/--
Julia source: base/range.jl:965-973 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const OverflowSafe = Union{Bool,Int8,Int16,Int32,Int64,Int128,
                           UInt8,UInt16,UInt32,UInt64,UInt128}

function _getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}
    val = v.start + (i - oneunit(i))
    @boundscheck _in_unit_range(v, val, i) || throw_boundserror(v, i)
    val % T
end

```
-/
def _getindex_UnitRange_OverflowSafe {T I D E : Type} [JOneunit I] [HSub I I D] [HAdd T D E]
    [JLt JInt64 I] [JLe E T] [JLe T E] [JThrowBoundserror (UnitRange T) I] [JRemType T E]
    (v : UnitRange T) (i : I) : JlX T := do
  let val : E := v.start + (i - (JOneunit.oneunit : I))
  unless _in_unit_range v val i do
    let e ← JThrowBoundserror.throwBoundserror v i
    Empty.elim e
  return JRemType.remType val

/--
Julia source: base/range.jl:974-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let BitInteger64 = Union{Int8,Int16,Int32,Int64,UInt8,UInt16,UInt32,UInt64} # for bootstrapping
    global function checkbounds(::Type{Bool}, v::StepRange{<:BitInteger64, <:BitInteger64}, i::BitInteger64)
        res = widemul(step(v), i-oneunit(i)) + first(v)
        (0 < i) & ifelse(0 < step(v), res <= last(v), res >= last(v))
    end
end

```
-/
def checkbounds_Bool_StepRange_BitInteger64 {T S I D W X : Type} [JStep (StepRange T S) S]
    [JOneunit I] [HSub I I D] [JWidemul S D W] [JFirst (StepRange T S) T] [HAdd W T X]
    [JLt JInt64 I] [JLt JInt64 S] [JLast (StepRange T S) T] [JLe X T] [JLe T X]
    (v : StepRange T S) (i : I) : JlX Bool := do
  let res := JWidemul.widemul (← JStep.step v) (i - (JOneunit.oneunit : I)) + (← JFirst.first v)
  let c1 := JLt.lt (jint 0) i
  let s ← JStep.step v
  let l1 ← JLast.last v
  let l2 ← JLast.last v
  return c1 && (if JLt.lt (jint 0) s then JLe.le res l1 else JLe.le l2 res)

/--
Julia source: base/range.jl:981-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# unsafe_getindex is separate to make it useful even when running with --check-bounds=yes
# it assumes the index is inbounds but does not segfault even if the index is out of bounds.
# it does not check if the index isa bool.
unsafe_getindex(v::OneTo{T}, i::Integer) where T = convert(T, i)
```
-/
def unsafe_getindex_OneTo {T I : Type} [JConvert T I] (v : OneTo T) (i : I) : JlX T :=
  JConvert.convert i

/--
Julia source: base/range.jl:985-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_getindex(v::AbstractRange{T}, i::Integer) where T = convert(T, first(v) + (i - oneunit(i))*step_hp(v))
```
-/
def unsafe_getindex_AbstractRange {R T I D S P E : Type} [JEltype R T] [JFirst R T] [JOneunit I]
    [HSub I I D] [JStepHp R S] [HMul D S P] [HAdd T P E] [JConvert T E] (v : R) (i : I) :
    JlX T := do
  let f ← JFirst.first v
  let s ← JStepHp.stepHp v
  JConvert.convert (T := T) (f + (i - (JOneunit.oneunit : I)) * s)

/--
Julia source: base/range.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T
    u = oftype(r.offset, i) - r.offset
    convert(T, (r.ref + u*r.step))
end
```
-/
def unsafe_getindex_StepRangeLen {T R S L I P E : Type} [JConvert L I] [HSub L L L] [HMul L S P]
    [HAdd R P E] [JConvert T E] (r : StepRangeLen T R S L) (i : I) : JlX T := do
  let u := (← oftype r.offset i) - r.offset
  JConvert.convert (T := T) (r.ref + u * r.step)

/-- `lerpi(j, d, a, b)`. -/
class JLerpi (J D T : Type) where
  lerpi : J → D → T → T → JlX T

/--
Julia source: base/range.jl:990-991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_getindex(r::LinRange, i::Integer) = lerpi(i-oneunit(i), r.lendiv, r.start, r.stop)

```
-/
def unsafe_getindex_LinRange {T L I J : Type} [JOneunit I] [HSub I I J] [JLerpi J L T]
    (r : LinRange T L) (i : I) : JlX T :=
  JLerpi.lerpi (i - (JOneunit.oneunit : I)) r.lendiv r.start r.stop

/--
Julia source: base/range.jl:992-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lerpi(j::Integer, d::Integer, a::T, b::T) where T
    t = j/d # ∈ [0,1]
    # compute approximately fma(t, b, -fma(t, a, a))
    return T((1-t)*a + t*b)
end

# non-scalar indexing

```
-/
def lerpi {J D T F G H K : Type} [HDiv J D F] [HSub JInt64 F G] [HMul G T H] [HMul F T K]
    [HAdd H K H] [JCtor T H] (j : J) (d : D) (a b : T) : JlX T :=
  let t : F := j / d
  JCtor.ctor ((jint 1 - t) * a + t * b)

/-! ## Non-scalar indexing (lines 1000-1134) -/

/--
Julia source: base/range.jl:1000-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(r::AbstractRange, ::Colon) = copy(r)

```
-/
def getindex_AbstractRange_Colon {R ρ : Type} [JCopy R ρ] (r : R) (c : Colon) : JlX ρ :=
  JCopy.copy r

/--
Julia source: base/range.jl:1002-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _empty_stop(start, step)
    if step > zero(step)
        stop = start - oneunit(step)
        stop < start && return stop
    else
        stop = start + oneunit(step)
        stop > start && return stop
    end
    throw(OverflowError(LazyString("cannot represent an empty range starting at ", start)))
end

```
-/
def _empty_stop {T S E : Type} [JZero S] [JLt S S] [JOneunit S] [HSub T S E] [HAdd T S E]
    [JLt E T] [JLt T E] [JPrint T] (start : T) (step : S) : JlX E := do
  if JLt.lt (JZero.zero : S) step then
    let stop := start - (JOneunit.oneunit : S)
    if JLt.lt stop start then return stop
  else
    let stop := start + (JOneunit.oneunit : S)
    if JLt.lt start stop then return stop
  throw (.jl (.overflowError ("cannot represent an empty range starting at " ++ JPrint.print start)))

/-- `_empty_stop(start, step)`. -/
class JEmptyStop (T S : Type) (E : outParam Type) where
  emptyStop : T → S → JlX E

/--
Julia source: base/range.jl:1013-1027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::AbstractUnitRange, s::AbstractUnitRange{T}) where {T<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    if T === Bool
        return range(first(s) ? first(r) : last(r), length = last(s))
    else
        f = first(r)
        start = oftype(f, f + first(s) - firstindex(r))
        len = length(s)
        stop = oftype(f, isempty(s) ? _empty_stop(start, step(r)) : _range_wrapping_add(start, len - oneunit(len)))
        return range(start, stop)
    end
end

```
-/
def getindex_AbstractUnitRange_AbstractUnitRange {R U F E I L M Q Q' ρ₁ ρ₂ : Type} [JType E]
    [JCheckbounds R U] [JFirst U E] [JFirst R F] [JLast R F] [JLast U E]
    [JRangeStartKw F Nothing E Nothing ρ₁]
    [HAdd F E Q] [JFirstindex R I] [HSub Q I Q'] [JConvert F Q'] [JLength U L] [JIsempty U]
    {S : Type} [JStep R S] [JEmptyStop F S M] [JOneunit L] [HSub L L L]
    {W : Type} [JRangeWrappingAdd F L W] [JConvert F M] [JConvert F W]
    [JRangeStartStopKw F F Nothing Nothing ρ₂] (r : R) (s : U) : JlX (ρ₁ ⊕ ρ₂) := do
  JCheckbounds.checkbounds r s
  if h : JType.isBool E then
    let start ← if asBool h (← JFirst.first s) then JFirst.first r else JLast.last r
    return .inl (← JRangeStartKw.range start Nothing.nothing (← JLast.last s) Nothing.nothing)
  else
    let f ← JFirst.first r
    let start ← oftype f (f + (← JFirst.first s) - (← JFirstindex.firstindex r))
    let len ← JLength.length s
    let stop ← if ← JIsempty.isempty s then do oftype f (← JEmptyStop.emptyStop start (← JStep.step r))
      else oftype f (JRangeWrappingAdd.rangeWrappingAdd start (len - (JOneunit.oneunit : L)))
    return .inr (← JRangeStartStopKw.range start stop Nothing.nothing Nothing.nothing)

/--
Julia source: base/range.jl:1028-1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::OneTo{T}, s::OneTo) where T
    @inline
    @boundscheck checkbounds(r, s)
    return OneTo(T(s.stop))
end

```
-/
def getindex_OneTo_OneTo {T U : Type} [JCheckbounds (OneTo T) (OneTo U)] [JCtor T U]
    [JOneTo1 T (OneTo T)] (r : OneTo T) (s : OneTo U) : JlX (OneTo T) := do
  JCheckbounds.checkbounds r s
  JOneTo1.oneTo (← JCtor.ctor (T := T) s.stop)

/--
Julia source: base/range.jl:1034-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::AbstractUnitRange, s::StepRange{T}) where {T<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    if T === Bool
        len = Int(last(s))
        return range(first(s) ? first(r) : last(r), step=oneunit(eltype(r)), length=len)
    else
        f = first(r)
        start = oftype(f, f + s.start - firstindex(r))
        st = step(s)
        len = length(s)
        stop = oftype(f, isempty(s) ? _empty_stop(start, st) : start + (len - oneunit(len)) * st)
        return range(start, stop; step=st)
    end
end

```
-/
def getindex_AbstractUnitRange_StepRange {R T S F E ρ₁ ρ₂ I Q Q' L M P W : Type} [JType T]
    [JCheckbounds R (StepRange T S)] [JLast (StepRange T S) T] [JCtor JInt64 T]
    [JFirst (StepRange T S) T] [JFirst R F] [JLast R F] [JEltype R E] [JOneunit E]
    [JRangeStartKw F Nothing JInt64 E ρ₁]
    [HAdd F T Q] [JFirstindex R I] [HSub Q I Q'] [JConvert F Q'] [JStep (StepRange T S) S]
    [JLength (StepRange T S) L] [JIsempty (StepRange T S)] [JEmptyStop F S M] [JConvert F M]
    [JOneunit L] [HSub L L L] [HMul L S P] [HAdd F P W] [JConvert F W]
    [JRangeStartStopKw F F Nothing S ρ₂] (r : R) (s : StepRange T S) : JlX (ρ₁ ⊕ ρ₂) := do
  JCheckbounds.checkbounds r s
  if h : JType.isBool T then
    let len ← JCtor.ctor (T := JInt64) (← JLast.last s)
    let start ← if asBool h (← JFirst.first s) then JFirst.first r else JLast.last r
    return .inl (← JRangeStartKw.range start Nothing.nothing len (JOneunit.oneunit : E))
  else
    let f ← JFirst.first r
    let start ← oftype f (f + s.start - (← JFirstindex.firstindex r))
    let st ← JStep.step s
    let len ← JLength.length s
    let stop ← if ← JIsempty.isempty s then do oftype f (← JEmptyStop.emptyStop start st)
      else oftype f (start + (len - (JOneunit.oneunit : L)) * st)
    return .inr (← JRangeStartStopKw.range start stop Nothing.nothing st)

/--
Julia source: base/range.jl:1051-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::StepRange, s::AbstractRange{T}) where {T<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    if T === Bool
        # treat as a zero, one, or two-element vector, where at most one element is true
        # staying inbounds on the original range (preserving either start or
        # stop as either stop or start, depending on the length)
        st = step(s)
        nonempty = st > zero(st) ? last(s) : first(s)
        # n.b. isempty(r) implies isempty(r) which means !nonempty and !first(s)
        range((first(s) ⊻ nonempty) ⊻ isempty(r) ? last(r) : first(r), step=step(r), length=Int(nonempty))
    else
        f = r.start
        fs = first(s)
        st = r.step
        start = oftype(f, f + (fs - firstindex(r)) * st)
        st *= step(s)
        len = length(s)
        stop = oftype(f, isempty(s) ? _empty_stop(start, st) : start + (len - oneunit(len)) * st)
        return range(start, stop; step=st)
    end
end

```
-/
def getindex_StepRange_AbstractRange {T S U E SS ρ₁ ρ₂ I D P Q Q2 Λ M SS' W : Type} [JType E]
    [JCheckbounds (StepRange T S) U] [JStep U SS] [JZero SS] [JLt SS SS] [JLast U E] [JFirst U E]
    [JIsempty (StepRange T S)] [JLast (StepRange T S) T] [JFirst (StepRange T S) T]
    [JStep (StepRange T S) S] [JCtor JInt64 Bool] [JRangeStartKw T Nothing JInt64 S ρ₁]
    [JFirstindex (StepRange T S) I] [HSub E I D] [HMul D S P] [HAdd T P Q] [JConvert T Q]
    [HMul S SS SS'] [JLength U Λ] [JIsempty U] [JEmptyStop T SS' M] [JConvert T M] [JOneunit Λ]
    [HSub Λ Λ Λ] [HMul Λ SS' W] [HAdd T W Q2] [JConvert T Q2] [JRangeStartStopKw T T Nothing SS' ρ₂]
    (r : StepRange T S) (s : U) : JlX (ρ₁ ⊕ ρ₂) := do
  JCheckbounds.checkbounds r s
  if h : JType.isBool E then
    let st ← JStep.step s
    let nonempty := asBool h (← if JLt.lt (JZero.zero : SS) st then JLast.last s else JFirst.first s)
    let c := xor (xor (asBool h (← JFirst.first s)) nonempty) (← JIsempty.isempty r)
    let start ← if c then JLast.last r else JFirst.first r
    let stp ← JStep.step r
    return .inl (← JRangeStartKw.range start Nothing.nothing (← JCtor.ctor (T := JInt64) nonempty) stp)
  else
    let f := r.start
    let fs ← JFirst.first s
    let st := r.step
    let start ← oftype f (f + (fs - (← JFirstindex.firstindex r)) * st)
    let st : SS' := st * (← JStep.step s)
    let len ← JLength.length s
    let stop ← if ← JIsempty.isempty s then do oftype f (← JEmptyStop.emptyStop start st)
      else oftype f (start + (len - (JOneunit.oneunit : Λ)) * st)
    return .inr (← JRangeStartStopKw.range start stop Nothing.nothing st)

/-- `_getindex_hiprec(r, i)`. -/
class JGetindexHiprec (R I : Type) (V : outParam Type) where
  getindexHiprec : R → I → JlX V

/--
Julia source: base/range.jl:1075-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::StepRangeLen{T}, s::OrdinalRange{S}) where {T, S<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    len = length(s)
    sstep = step_hp(s)
    rstep = step_hp(r)
    L = typeof(len)
    if S === Bool
        rstep *= one(sstep)
        if len == 0
            return StepRangeLen{T}(first(r), rstep, zero(L), oneunit(L))
        elseif len == 1
            if first(s)
                return StepRangeLen{T}(first(r), rstep, oneunit(L), oneunit(L))
            else
                return StepRangeLen{T}(first(r), rstep, zero(L), oneunit(L))
            end
        else # len == 2
            return StepRangeLen{T}(last(r), rstep, oneunit(L), oneunit(L))
        end
    else
        # Find closest approach to offset by s
        ind = LinearIndices(s)
        offset = L(max(min(1 + round(L, (r.offset - first(s))/sstep), last(ind)), first(ind)))
        ref = _getindex_hiprec(r, first(s) + (offset - oneunit(offset)) * sstep)
        return StepRangeLen{T}(ref, rstep*sstep, len, offset)
    end
end

```
-/
def getindex_StepRangeLen_OrdinalRange {T R S L U E Λ SS RS RS' ρ₁ Z F D O Q V P ρ₂ : Type} [JType E]
    [JCheckbounds (StepRangeLen T R S L) U] [JLength U Λ] [JStepHp U SS]
    [JStepHp (StepRangeLen T R S L) RS] [JOne SS] [HMul RS SS RS'] [JEq Λ JInt64] [JZero Λ]
    [JOneunit Λ] [JFirst (StepRangeLen T R S L) T] [JLast (StepRangeLen T R S L) T] [JFirst U E]
    [JStepRangeLenT T T RS' Λ Λ ρ₁] [JLinearIndices U Z] [HSub L E F]
    [HDiv F SS D] [JRoundTo Λ D] [HAdd JInt64 Λ O] [JLast Z Q] [JMin O Q O] [JFirst Z Q]
    [JMax O Q O] [JCtor Λ O] [HSub Λ Λ Λ] [HMul Λ SS P] [HAdd E P V]
    {H : Type} [JGetindexHiprec (StepRangeLen T R S L) V H]
    [JStepRangeLenT T H RS' Λ Λ ρ₂] (r : StepRangeLen T R S L) (s : U) : JlX (ρ₁ ⊕ ρ₂) := do
  JCheckbounds.checkbounds r s
  let len ← JLength.length s
  let sstep ← JStepHp.stepHp s
  let rstep ← JStepHp.stepHp r
  if h : JType.isBool E then
    let rstep : RS' := rstep * (JOne.one : SS)
    if JEq.eq len (jint 0) then
      return .inl (← JStepRangeLenT.stepRangeLenT (T := T) (← JFirst.first r) rstep
        (JZero.zero : Λ) (JOneunit.oneunit : Λ))
    else if JEq.eq len (jint 1) then
      if asBool h (← JFirst.first s) then
        return .inl (← JStepRangeLenT.stepRangeLenT (T := T) (← JFirst.first r) rstep
          (JOneunit.oneunit : Λ) (JOneunit.oneunit : Λ))
      else
        return .inl (← JStepRangeLenT.stepRangeLenT (T := T) (← JFirst.first r) rstep
          (JZero.zero : Λ) (JOneunit.oneunit : Λ))
    else
      return .inl (← JStepRangeLenT.stepRangeLenT (T := T) (← JLast.last r) rstep
        (JOneunit.oneunit : Λ) (JOneunit.oneunit : Λ))
  else
    let ind ← JLinearIndices.linearIndices s
    let x ← JRoundTo.roundTo (L := Λ) ((r.offset - (← JFirst.first s)) / sstep)
    let lo ← JMin.min (jint 1 + x) (← JLast.last ind)
    let offset ← JCtor.ctor (T := Λ) (← JMax.max lo (← JFirst.first ind))
    let ref ← JGetindexHiprec.getindexHiprec r
      ((← JFirst.first s) + (offset - (JOneunit.oneunit : Λ)) * sstep)
    return .inr (← JStepRangeLenT.stepRangeLenT (T := T) ref (rstep * sstep) len offset)

/--
Julia source: base/range.jl:1105-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex_hiprec(r::StepRangeLen, i::Integer)  # without rounding by T
    u = oftype(r.offset, i) - r.offset
    r.ref + u*r.step
end

```
-/
def _getindex_hiprec {T R S L I P V : Type} [JConvert L I] [HSub L L L] [HMul L S P] [HAdd R P V]
    (r : StepRangeLen T R S L) (i : I) : JlX V := do
  let u := (← oftype r.offset i) - r.offset
  return r.ref + u * r.step

/--
Julia source: base/range.jl:1110-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::LinRange{T}, s::OrdinalRange{S}) where {T, S<:Integer}
    @inline
    @boundscheck checkbounds(r, s)

    len = length(s)
    L = typeof(len)
    if S === Bool
        if len == 0
            return LinRange{T}(first(r), first(r), len)
        elseif len == 1
            if first(s)
                return LinRange{T}(first(r), first(r), len)
            else
                return LinRange{T}(first(r), first(r), zero(L))
            end
        else # length(s) == 2
            return LinRange{T}(last(r), last(r), oneunit(L))
        end
    else
        vfirst = unsafe_getindex(r, first(s))
        vlast  = unsafe_getindex(r, last(s))
        return LinRange{T}(vfirst, vlast, len)
    end
end

```
-/
def getindex_LinRange_OrdinalRange {T L U E Λ ρ : Type} [JType E]
    [JCheckbounds (LinRange T L) U] [JLength U Λ] [JEq Λ JInt64] [JZero Λ] [JOneunit Λ]
    [JFirst (LinRange T L) T] [JLast (LinRange T L) T] [JFirst U E] [JLast U E]
    [JLinRangeT T T T Λ ρ] [JUnsafeGetindex (LinRange T L) E T] (r : LinRange T L) (s : U) :
    JlX ρ := do
  JCheckbounds.checkbounds r s
  let len ← JLength.length s
  if h : JType.isBool E then
    if JEq.eq len (jint 0) then
      JLinRangeT.linRangeT (T := T) (← JFirst.first r) (← JFirst.first r) len
    else if JEq.eq len (jint 1) then
      if asBool h (← JFirst.first s) then
        JLinRangeT.linRangeT (T := T) (← JFirst.first r) (← JFirst.first r) len
      else
        JLinRangeT.linRangeT (T := T) (← JFirst.first r) (← JFirst.first r) (JZero.zero : Λ)
    else
      JLinRangeT.linRangeT (T := T) (← JLast.last r) (← JLast.last r) (JOneunit.oneunit : Λ)
  else
    let vfirst ← JUnsafeGetindex.unsafeGetindex r (← JFirst.first s)
    let vlast ← JUnsafeGetindex.unsafeGetindex r (← JLast.last s)
    JLinRangeT.linRangeT (T := T) vfirst vlast len


/-! ## `show`, `==`, `cmp`, `intersect`, `union`, `issubset` (lines 1135-1321) -/

/--
Julia source: base/range.jl:1135-1135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, r::AbstractRange) = print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
```
-/
def show_AbstractRange {R T S : Type} [JFirst R T] [JRepr T] [JStep R S] [JRepr S] [JLast R T]
    (io : JIO) (r : R) : JlX String := do
  let a ← JRepr.repr (← JFirst.first r)
  let b ← JRepr.repr (← JStep.step r)
  let c ← JRepr.repr (← JLast.last r)
  return a ++ ":" ++ b ++ ":" ++ c

/--
Julia source: base/range.jl:1136-1140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, r::UnitRange)
    show(io, first(r))
    print(io, ':')
    show(io, last(r))
end
```
-/
def show_UnitRange {T : Type} [JFirst (UnitRange T) T] [JShow T] [JLast (UnitRange T) T]
    (io : JIO) (r : UnitRange T) : JlX String := do
  let mut out ← JShow.showValue (← JFirst.first r)
  out := out ++ ":"
  out := out ++ (← JShow.showValue (← JLast.last r))
  return out

/--
Julia source: base/range.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, r::OneTo) = print(io, "Base.OneTo(", r.stop, ")")
```
-/
def show_OneTo {T : Type} [JPrint T] (io : JIO) (r : OneTo T) : JlX String :=
  pure ("Base.OneTo(" ++ JPrint.print r.stop ++ ")")

/--
Julia source: base/range.jl:1142-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, r::StepRangeLen)
    if !iszero(step(r))
        print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
    else
        # ugly temporary printing, to avoid 0:0:0 etc.
        print(io, "StepRangeLen(", repr(first(r)), ", ", repr(step(r)), ", ", repr(length(r)), ")")
    end
end

```
-/
def show_StepRangeLen {T R S L U Λ : Type} [JStep (StepRangeLen T R S L) U] [JIszero U]
    [JFirst (StepRangeLen T R S L) T] [JRepr T] [JRepr U] [JLast (StepRangeLen T R S L) T]
    [JLength (StepRangeLen T R S L) Λ] [JRepr Λ] (io : JIO) (r : StepRangeLen T R S L) :
    JlX String := do
  if !JIszero.iszero (← JStep.step r) then
    let a ← JRepr.repr (← JFirst.first r)
    let b ← JRepr.repr (← JStep.step r)
    let c ← JRepr.repr (← JLast.last r)
    return a ++ ":" ++ b ++ ":" ++ c
  else
    let a ← JRepr.repr (← JFirst.first r)
    let b ← JRepr.repr (← JStep.step r)
    let c ← JRepr.repr (← JLength.length r)
    return "StepRangeLen(" ++ a ++ ", " ++ b ++ ", " ++ c ++ ")"

/--
Julia source: base/range.jl:1151-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(r::T, s::T) where {T<:AbstractRange}
    isempty(r) && return isempty(s)
    _has_length_one(r) && return _has_length_one(s) & (first(r) == first(s))
    (first(r) == first(s)) & (step(r) == step(s)) & (last(r) == last(s))
end

```
-/
def eq_T_T_AbstractRange {R T S : Type} [JIsempty R] [JHasLengthOne R] [JFirst R T] [JEq T T]
    [JStep R S] [JEq S S] [JLast R T] (r s : R) : JlX Bool := do
  if ← JIsempty.isempty r then return ← JIsempty.isempty s
  if ← JHasLengthOne.hasLengthOne r then
    return (← JHasLengthOne.hasLengthOne s) && JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e1 := JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e2 := JEq.eq (← JStep.step r) (← JStep.step s)
  let e3 := JEq.eq (← JLast.last r) (← JLast.last s)
  return e1 && e2 && e3

/--
Julia source: base/range.jl:1157-1162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(r::OrdinalRange, s::OrdinalRange)
    isempty(r) && return isempty(s)
    _has_length_one(r) && return _has_length_one(s) & (first(r) == first(s))
    (first(r) == first(s)) & (step(r) == step(s)) & (last(r) == last(s))
end

```
-/
def eq_OrdinalRange_OrdinalRange {R Q T U S V : Type} [JIsempty R] [JIsempty Q] [JHasLengthOne R]
    [JHasLengthOne Q] [JFirst R T] [JFirst Q U] [JEq T U] [JStep R S] [JStep Q V] [JEq S V]
    [JLast R T] [JLast Q U] (r : R) (s : Q) : JlX Bool := do
  if ← JIsempty.isempty r then return ← JIsempty.isempty s
  if ← JHasLengthOne.hasLengthOne r then
    let a ← JHasLengthOne.hasLengthOne s
    return a && JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e1 := JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e2 := JEq.eq (← JStep.step r) (← JStep.step s)
  let e3 := JEq.eq (← JLast.last r) (← JLast.last s)
  return e1 && e2 && e3

/--
Julia source: base/range.jl:1163-1165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(r::AbstractUnitRange, s::AbstractUnitRange) =
    (isempty(r) & isempty(s)) | ((first(r) == first(s)) & (last(r) == last(s)))

```
-/
def eq_AbstractUnitRange_AbstractUnitRange {R Q T U : Type} [JIsempty R] [JIsempty Q]
    [JFirst R T] [JFirst Q U] [JEq T U] [JLast R T] [JLast Q U] (r : R) (s : Q) : JlX Bool := do
  let e1 ← JIsempty.isempty r
  let e2 ← JIsempty.isempty s
  let f := JEq.eq (← JFirst.first r) (← JFirst.first s)
  let l := JEq.eq (← JLast.last r) (← JLast.last s)
  return (e1 && e2) || (f && l)

/--
Julia source: base/range.jl:1166-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(r::OneTo, s::OneTo) = last(r) == last(s)

```
-/
def eq_OneTo_OneTo {T U : Type} [JLast (OneTo T) T] [JLast (OneTo U) U] [JEq T U] (r : OneTo T)
    (s : OneTo U) : JlX Bool := do
  return JEq.eq (← JLast.last r) (← JLast.last s)

/--
Julia source: base/range.jl:1168-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(r::T, s::T) where {T<:Union{StepRangeLen,LinRange}} =
    (isempty(r) & isempty(s)) | ((first(r) == first(s)) & (length(r) == length(s)) & (last(r) == last(s)))

```
-/
def eq_T_T_StepRangeLen_LinRange {R T Λ : Type} [JIsempty R] [JFirst R T] [JEq T T] [JLength R Λ]
    [JEq Λ Λ] [JLast R T] (r s : R) : JlX Bool := do
  let e1 ← JIsempty.isempty r
  let e2 ← JIsempty.isempty s
  let f := JEq.eq (← JFirst.first r) (← JFirst.first s)
  let n := JEq.eq (← JLength.length r) (← JLength.length s)
  let l := JEq.eq (← JLast.last r) (← JLast.last s)
  return (e1 && e2) || (f && n && l)

/--
Julia source: base/range.jl:1171-1176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(r::Union{StepRange{T},StepRangeLen{T,T}}, s::Union{StepRange{T},StepRangeLen{T,T}}) where {T}
    isempty(r) && return isempty(s)
    _has_length_one(r) && return _has_length_one(s) & (first(r) == first(s))
    (first(r) == first(s)) & (step(r) == step(s)) & (last(r) == last(s))
end

```
-/
def eq_StepRange_StepRangeLen {R Q T S V : Type} [JIsempty R] [JIsempty Q] [JHasLengthOne R]
    [JHasLengthOne Q] [JFirst R T] [JFirst Q T] [JEq T T] [JStep R S] [JStep Q V] [JEq S V]
    [JLast R T] [JLast Q T] (r : R) (s : Q) : JlX Bool := do
  if ← JIsempty.isempty r then return ← JIsempty.isempty s
  if ← JHasLengthOne.hasLengthOne r then
    let a ← JHasLengthOne.hasLengthOne s
    return a && JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e1 := JEq.eq (← JFirst.first r) (← JFirst.first s)
  let e2 := JEq.eq (← JStep.step r) (← JStep.step s)
  let e3 := JEq.eq (← JLast.last r) (← JLast.last s)
  return e1 && e2 && e3

/--
Julia source: base/range.jl:1177-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_has_length_one(r::OrdinalRange) = first(r) == last(r)
```
-/
def _has_length_one_OrdinalRange {R T : Type} [JFirst R T] [JLast R T] [JEq T T] (r : R) :
    JlX Bool := do
  return JEq.eq (← JFirst.first r) (← JLast.last r)

/--
Julia source: base/range.jl:1178-1179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_has_length_one(r::AbstractRange) = isone(length(r))

```
-/
def _has_length_one_AbstractRange {R Λ : Type} [JLength R Λ] [JIsone Λ] (r : R) : JlX Bool := do
  return JIsone.isone (← JLength.length r)

/--
Julia source: base/range.jl:1180-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(r::AbstractRange, s::AbstractRange)
    lr = length(r)
    if lr != length(s)
        return false
    elseif iszero(lr)
        return true
    end
    yr, ys = iterate(r), iterate(s)
    while yr !== nothing
        yr[1] == ys[1] || return false
        yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
    end
    return true
end

```
-/
def eq_AbstractRange_AbstractRange {R Q Λ M T U SR SQ : Type} [JLength R Λ] [JLength Q M]
    [JEq Λ M] [JIszero Λ] [JIterate1 R T SR] [JIterate1 Q U SQ] [JEq T U] [JIterate2 R SR T]
    [JIterate2 Q SQ U] (r : R) (s : Q) (fuel : Nat) : JlX Bool := do
  let lr ← JLength.length r
  if !JEq.eq lr (← JLength.length s) then return false
  else if JIszero.iszero lr then return true
  let yr ← JIterate1.iterate r
  let ys ← JIterate1.iterate s
  let rec loop : Nat → Option (T × SR) → Option (U × SQ) → JlX Bool
    | _, none, _ => pure true
    | 0, some _, _ => throw (.errorException "fuel")
    | _ + 1, some _, none => throw (.jl (.methodError "getindex(::Nothing, ::Int)"))
    | n + 1, some (x, sr), some (y, sq) => do
        if !JEq.eq x y then return false
        let yr ← JIterate2.iterate r sr
        let ys ← JIterate2.iterate s sq
        loop n yr ys
  loop fuel yr ys

/--
Julia source: base/range.jl:1195-1205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(r1::T, r2::T) where {T <: AbstractRange}
    firstindex(r1) == firstindex(r2) || return cmp(firstindex(r1), firstindex(r2))
    (isempty(r1) || isempty(r2)) && return cmp(isempty(r2), isempty(r1))
    first(r1) != first(r2) && return cmp(first(r1), first(r2))
    # Assume that ranges are monotonic and use the last shared element as a high precision proxy for step.
    n = min(lastindex(r1), lastindex(r2))
    x1, x2 = r1[n], r2[n]
    x1 != x2 && return cmp(x1, x2)
    cmp(length(r1), length(r2))
end

```
-/
def cmp_T_T_AbstractRange {R I T Λ : Type} [JFirstindex R I] [JEq I I] [JCmp I I] [JIsempty R]
    [JCmp Bool Bool] [JFirst R T] [JEq T T] [JCmp T T] [JLastindex R I] [JMin I I I]
    [JGetindex R I T] [JLength R Λ] [JCmp Λ Λ] (r1 r2 : R) : JlX JInt64 := do
  unless JEq.eq (← JFirstindex.firstindex r1) (← JFirstindex.firstindex r2) do
    return ← JCmp.cmp (← JFirstindex.firstindex r1) (← JFirstindex.firstindex r2)
  if (← JIsempty.isempty r1) || (← do JIsempty.isempty r2) then
    return ← JCmp.cmp (← JIsempty.isempty r2) (← JIsempty.isempty r1)
  if !JEq.eq (← JFirst.first r1) (← JFirst.first r2) then
    return ← JCmp.cmp (← JFirst.first r1) (← JFirst.first r2)
  let n ← JMin.min (← JLastindex.lastindex r1) (← JLastindex.lastindex r2)
  let x1 ← JGetindex.getindex r1 n
  let x2 ← JGetindex.getindex r2 n
  if !JEq.eq x1 x2 then return ← JCmp.cmp x1 x2
  JCmp.cmp (← JLength.length r1) (← JLength.length r2)

/--
Julia source: base/range.jl:1206-1206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(r::OneTo, s::OneTo) = OneTo(min(r.stop,s.stop))
```
-/
def intersect_OneTo_OneTo {T U M ρ : Type} [JMin T U M] [JOneTo1 M ρ] (r : OneTo T) (s : OneTo U) :
    JlX ρ := do
  JOneTo1.oneTo (← JMin.min r.stop s.stop)

/--
Julia source: base/range.jl:1207-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union(r::OneTo, s::OneTo) = OneTo(max(r.stop,s.stop))

```
-/
def union_OneTo_OneTo {T U M ρ : Type} [JMax T U M] [JOneTo1 M ρ] (r : OneTo T) (s : OneTo U) :
    JlX ρ := do
  JOneTo1.oneTo (← JMax.max r.stop s.stop)

/--
Julia source: base/range.jl:1209-1210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer}) = max(first(r),first(s)):min(last(r),last(s))

```
-/
def intersect_AbstractUnitRange_AbstractUnitRange {R Q T U A B ρ : Type} [JFirst R T] [JFirst Q U]
    [JMax T U A] [JLast R T] [JLast Q U] [JMin T U B] [JColon2 A B ρ] (r : R) (s : Q) : JlX ρ := do
  let a ← JMax.max (← JFirst.first r) (← JFirst.first s)
  let b ← JMin.min (← JLast.last r) (← JLast.last s)
  JColon2.colon a b

/--
Julia source: base/range.jl:1211-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(i::Integer, r::AbstractUnitRange{<:Integer}) = range(max(i, first(r)), length=in(i, r))

```
-/
def intersect_Integer_AbstractUnitRange {I R T M ρ : Type} [JFirst R T] [JMax I T M] [JIn I R]
    [JRangeStartKw M Nothing Bool Nothing ρ] (i : I) (r : R) : JlX ρ := do
  let start ← JMax.max i (← JFirst.first r)
  JRangeStartKw.range start Nothing.nothing (← JIn.isIn i r) Nothing.nothing

/--
Julia source: base/range.jl:1213-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(r::AbstractUnitRange{<:Integer}, i::Integer) = intersect(i, r)

```
-/
def intersect_AbstractUnitRange_Integer {R I ρ : Type} [JIntersect I R ρ] (r : R) (i : I) :
    JlX ρ :=
  JIntersect.intersect i r

/--
Julia source: base/range.jl:1215-1228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(r::AbstractUnitRange{<:Integer}, s::StepRange{<:Integer})
    T = promote_type(eltype(r), eltype(s))
    if isempty(s)
        StepRange{T}(first(r), +step(s), first(r)-step(s))
    else
        sta, ste, sto = first_step_last_ascending(s)
        lo = first(r)
        hi = last(r)
        i0 = max(sta, lo + mod(sta - lo, ste))
        i1 = min(sto, hi - mod(hi - sta, ste))
        StepRange{T}(i0, ste, i1)
    end
end

```
-/
def intersect_AbstractUnitRange_StepRange {R E1 E2 T2 S T S' D D2 M M2 A B A' B' ρ : Type}
    [JEltype R E1] [JPromoteType E1 T2 T] [JIsempty (StepRange T2 S)] [JFirst R E1]
    [JStep (StepRange T2 S) S] [JPos S S'] [HSub E1 S E2] [JStepRangeT T E1 S' E2 ρ]
    [JFirstStepLastAscending (StepRange T2 S) T2 S'] [JLast R E1] [HSub T2 E1 D] [JMod D S' M]
    [HAdd E1 M A] [JMax T2 A A'] [HSub E1 T2 D2] [JMod D2 S' M2] [HSub E1 M2 B] [JMin T2 B B']
    [JStepRangeT T A' S' B' ρ] (r : R) (s : StepRange T2 S) : JlX ρ := do
  if ← JIsempty.isempty s then
    let f1 ← JFirst.first r
    let st ← JStep.step s
    let f2 ← JFirst.first r
    let st2 ← JStep.step s
    JStepRangeT.stepRangeT (T := T) f1 (JPos.pos st) (f2 - st2)
  else
    let (sta, ste, sto) ← JFirstStepLastAscending.firstStepLastAscending s
    let lo ← JFirst.first r
    let hi ← JLast.last r
    let i0 ← JMax.max sta (lo + (← JMod.mod (sta - lo) ste))
    let i1 ← JMin.min sto (hi - (← JMod.mod (hi - sta) ste))
    JStepRangeT.stepRangeT (T := T) i0 ste i1

/--
Julia source: base/range.jl:1229-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first_step_last_ascending(r::StepRange)
    if step(r) < zero(step(r))
        last(r), -step(r), first(r)
    else
        first(r), +step(r), last(r)
    end
end

```
-/
def first_step_last_ascending {T S S' : Type} [JStep (StepRange T S) S] [JZero S] [JLt S S]
    [JLast (StepRange T S) T] [JNeg S S'] [JFirst (StepRange T S) T] [JPos S S']
    (r : StepRange T S) : JlX (T × S' × T) := do
  if JLt.lt (← JStep.step r) (JZero.zero : S) then
    let a ← JLast.last r
    let b := JNeg.neg (← JStep.step r)
    let c ← JFirst.first r
    return (a, b, c)
  else
    let a ← JFirst.first r
    let b := JPos.pos (← JStep.step r)
    let c ← JLast.last r
    return (a, b, c)

/--
Julia source: base/range.jl:1237-1244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(r::StepRange{<:Integer}, s::AbstractUnitRange{<:Integer})
    if step(r) < 0
        reverse(intersect(s, reverse(r)))
    else
        intersect(s, r)
    end
end

```
-/
def intersect_StepRange_AbstractUnitRange {T S Q V W ρ₁ ρ₂ : Type} [JStep (StepRange T S) S]
    [JLt S JInt64] [JReverse (StepRange T S) V] [JIntersect Q V W] [JReverse W ρ₁]
    [JIntersect Q (StepRange T S) ρ₂] (r : StepRange T S) (s : Q) : JlX (ρ₁ ⊕ ρ₂) := do
  if JLt.lt (← JStep.step r) (jint 0) then
    return .inl (← JReverse.reverse (← JIntersect.intersect s (← JReverse.reverse r)))
  else
    return .inr (← JIntersect.intersect s r)

/--
Julia source: base/range.jl:1245-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(r::StepRange, s::StepRange)
    T = promote_type(eltype(r), eltype(s))
    S = promote_type(typeof(step(r)), typeof(step(s)))
    if isempty(r) || isempty(s)
        return StepRange{T,S}(first(r), step(r), first(r)-step(r))
    end

    start1, step1, stop1 = first_step_last_ascending(r)
    start2, step2, stop2 = first_step_last_ascending(s)
    a = lcm(step1, step2)

    g, x, _ = gcdx(step1, step2)

    if !iszero(rem(start1 - start2, g))
        # Unaligned, no overlap possible.
        if  step(r) < zero(step(r))
            return StepRange{T,S}(stop1, -a, stop1+a)
        else
            return StepRange{T,S}(start1, a, start1-a)
        end
    end

    z = div(start1 - start2, g)
    b = start1 - x * z * step1
    # Possible points of the intersection of r and s are
    # ..., b-2a, b-a, b, b+a, b+2a, ...
    # Determine where in the sequence to start and stop.
    m = max(start1 + mod(b - start1, a), start2 + mod(b - start2, a))
    n = min(stop1 - mod(stop1 - b, a), stop2 - mod(stop2 - b, a))
    step(r) < zero(step(r)) ? StepRange{T,S}(n, -a, m) : StepRange{T,S}(m, a, n)
end

```
-/
def intersect_StepRange_StepRange {T1 S1 T2 S2 T S E A G D Rm Z P B M N F1 F2 : Type}
    [JPromoteType T1 T2 T] [JStep (StepRange T1 S1) S1] [JStep (StepRange T2 S2) S2]
    [JPromoteType S1 S2 S] [JIsempty (StepRange T1 S1)] [JIsempty (StepRange T2 S2)]
    [JFirst (StepRange T1 S1) T1] [HSub T1 S1 T1] [JStepRangeTS T S T1 S1 T1]
    [JFirstStepLastAscending (StepRange T1 S1) T1 E] [JFirstStepLastAscending (StepRange T2 S2) T2 E]
    [JLcm E E A] [JGcdx E E G] [HSub T1 T2 D] [JRem D G Rm] [JIszero Rm] [JZero S1] [JLt S1 S1]
    [JNeg A A] [HAdd T1 A T1] [HSub T1 A T1] [JStepRangeTS T S T1 A T1] [JDiv D G Z]
    [HMul G Z P] [HMul P E P] [HSub T1 P B] [HSub B T1 D] [JMod D A M] [HAdd T1 M F1]
    [HSub B T2 D] [HAdd T2 M F2] [JMax F1 F2 F1] [HSub T1 B D] [HSub T1 M N] [HSub T2 B D]
    [HSub T2 M N] [JMin N N N] [JStepRangeTS T S N A F1] [JStepRangeTS T S F1 A N]
    (r : StepRange T1 S1) (s : StepRange T2 S2) :
    JlX (StepRange T S) := do
  let _ ← JStep.step r
  let _ ← JStep.step s
  if (← JIsempty.isempty r) || (← do JIsempty.isempty s) then
    let f1 ← JFirst.first r
    let st1 ← JStep.step r
    let f2 ← JFirst.first r
    let st2 ← JStep.step r
    return ← JStepRangeTS.stepRangeTS f1 st1 (f2 - st2)
  let (start1, step1, stop1) ← JFirstStepLastAscending.firstStepLastAscending r
  let (start2, step2, stop2) ← JFirstStepLastAscending.firstStepLastAscending s
  let a ← JLcm.lcm step1 step2
  let (g, x, _) ← JGcdx.gcdx step1 step2
  if !JIszero.iszero (← JRem.rem (start1 - start2) g) then
    if JLt.lt (← JStep.step r) (JZero.zero : S1) then
      return ← JStepRangeTS.stepRangeTS stop1 (JNeg.neg a) (stop1 + a)
    else
      return ← JStepRangeTS.stepRangeTS start1 a (start1 - a)
  let z ← JDiv.div (start1 - start2) g
  let b := start1 - x * z * step1
  let m ← JMax.max (start1 + (← JMod.mod (b - start1) a)) (start2 + (← JMod.mod (b - start2) a))
  let n ← JMin.min (stop1 - (← JMod.mod (stop1 - b) a)) (stop2 - (← JMod.mod (stop2 - b) a))
  if JLt.lt (← JStep.step r) (JZero.zero : S1) then
    JStepRangeTS.stepRangeTS n (JNeg.neg a) m
  else
    JStepRangeTS.stepRangeTS m a n

/-- The loop `for x in r ... end` over a range, following the iteration protocol for at most
`fuel` steps; `body` updates the loop state. -/
def forIn {R E St σ : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R) (init : σ)
    (body : E → σ → JlX σ) (fuel : Nat) : JlX σ := do
  let rec go : Nat → St → σ → JlX σ
    | 0, _, _ => throw (.errorException "fuel")
    | n + 1, s, acc => do
        match ← JIterate2.iterate r s with
        | none => pure acc
        | some (x, s') => go n s' (← body x acc)
  match ← JIterate1.iterate r with
  | none => pure init
  | some (x, s) => go fuel s (← body x init)

/--
Julia source: base/range.jl:1277-1286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(r1::AbstractRange, r2::AbstractRange)
    # To iterate over the shorter range
    length(r1) > length(r2) && return intersect(r2, r1)

    r1 = unique(r1)
    T = promote_eltype(r1, r2)

    return T[x for x in r1 if x ∈ r2]
end

```
-/
def intersect_AbstractRange_AbstractRange {R Q Λ M U E St T ρ : Type} [JLength R Λ] [JLength Q M]
    [JLt M Λ] [JIntersect Q R ρ] [JUnique R U] [JIterate1 U E St] [JIterate2 U St E] [JIn E Q]
    [JConvert T E] (r1 : R) (r2 : Q) (fuel : Nat) : JlX (ρ ⊕ List T) := do
  if JLt.lt (← JLength.length r2) (← JLength.length r1) then
    return .inl (← JIntersect.intersect r2 r1)
  let r1 ← JUnique.unique r1
  -- `T = promote_eltype(r1, r2)` is the type parameter `T`; the comprehension iterates `r1`
  let out ← forIn r1 ([] : List T) (fun x out => do
    if ← JIn.isIn x r2 then return out ++ [← JConvert.convert (T := T) x] else return out) fuel
  return .inr out

/--
Julia source: base/range.jl:1287-1295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)
    i = intersect(intersect(r1, r2), r3)
    for t in r
        i = intersect(i, t)
    end
    i
end

# _findin (the index of intersection)
```
-/
def intersect_AbstractRange_3 {R1 R2 R3 R4 I J : Type} [JIntersect R1 R2 I] [JIntersect I R3 J]
    [JIntersect J R4 J] (r1 : R1) (r2 : R2) (r3 : R3) (r : List R4) : JlX J := do
  -- the loop variable `i` keeps the type of `intersect(intersect(r1, r2), r3)`
  let mut i ← JIntersect.intersect (← JIntersect.intersect r1 r2) r3
  for t in r do
    i ← JIntersect.intersect i t
  return i

/-- `r isa AbstractUnitRange`. -/
class JIsAbstractUnitRange (R : Type) where
  isAbstractUnitRange : Bool

/--
Julia source: base/range.jl:1296-1314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findin(r::AbstractRange{<:Integer}, span::AbstractUnitRange{<:Integer})
    fspan = first(span)
    lspan = last(span)
    fr = first(r)
    lr = last(r)
    sr = step(r)
    if sr > 0
        ifirst = fr >= fspan ? 1 : cld(fspan-fr, sr)+1
        ilast = lr <= lspan ? length(r) : length(r) - cld(lr-lspan, sr)
    elseif sr < 0
        ifirst = fr <= lspan ? 1 : cld(lspan-fr, sr)+1
        ilast = lr >= fspan ? length(r) : length(r) - cld(lr-fspan, sr)
    else
        ifirst = fr >= fspan ? 1 : length(r)+1
        ilast = fr <= lspan ? length(r) : 0
    end
    r isa AbstractUnitRange ? (ifirst:ilast) : (ifirst:1:ilast)
end

```
-/
def _findin {R Q E T S C I ρ₁ ρ₂ : Type} [JFirst Q T] [JLast Q T] [JFirst R E] [JLast R E]
    [JStep R S] [JLt JInt64 S] [JLt S JInt64] [JLe T E] [JLe E T] [JOne I] [JZero I]
    [HSub T E T] [HSub E T E] [JCld T S C] [JCld E S C] [HAdd C JInt64 I] [JLength R I]
    [HSub I C I] [HAdd I JInt64 I] [JIsAbstractUnitRange R] [JColon2 I I ρ₁]
    [JColon3 I JInt64 I ρ₂] (r : R) (span : Q) : JlX (ρ₁ ⊕ ρ₂) := do
  -- `ifirst` and `ilast` are `Int` literals or values of the type `I` of `cld(...)+1`; the
  -- literals are written in `I`, the type the final colon promotes both endpoints to
  let fspan ← JFirst.first span
  let lspan ← JLast.last span
  let fr ← JFirst.first r
  let lr ← JLast.last r
  let sr ← JStep.step r
  let (ifirst, ilast) : I × I ←
    if JLt.lt (jint 0) sr then do
      let ifirst ← if JLe.le fspan fr then pure JOne.one
        else do pure ((← JCld.cld (fspan - fr) sr) + jint 1)
      let ilast ← if JLe.le lr lspan then JLength.length r
        else do pure ((← JLength.length r) - (← JCld.cld (lr - lspan) sr))
      pure (ifirst, ilast)
    else if JLt.lt sr (jint 0) then do
      let ifirst ← if JLe.le fr lspan then pure JOne.one
        else do pure ((← JCld.cld (lspan - fr) sr) + jint 1)
      let ilast ← if JLe.le fspan lr then JLength.length r
        else do pure ((← JLength.length r) - (← JCld.cld (lr - fspan) sr))
      pure (ifirst, ilast)
    else do
      let ifirst ← if JLe.le fspan fr then pure JOne.one
        else do pure ((← JLength.length r) + jint 1)
      let ilast ← if JLe.le fr lspan then JLength.length r else pure JZero.zero
      pure (ifirst, ilast)
  if JIsAbstractUnitRange.isAbstractUnitRange R then
    return .inl (← JColon2.colon ifirst ilast)
  else
    return .inr (← JColon3.colon ifirst (jint 1) ilast)

/--
Julia source: base/range.jl:1315-1316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issubset(r::OneTo, s::OneTo) = r.stop <= s.stop

```
-/
def issubset_OneTo_OneTo {T U : Type} [JLe T U] (r : OneTo T) (s : OneTo U) : Bool :=
  JLe.le r.stop s.stop

/--
Julia source: base/range.jl:1317-1321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer}) =
    isempty(r) || (first(r) >= first(s) && last(r) <= last(s))

## linear operations on ranges ##

```
-/
def issubset_AbstractUnitRange_AbstractUnitRange {R Q T U : Type} [JIsempty R] [JFirst R T]
    [JFirst Q U] [JLe U T] [JLast R T] [JLast Q U] [JLe T U] (r : R) (s : Q) : JlX Bool := do
  if ← JIsempty.isempty r then return true
  if !JLe.le (← JFirst.first s) (← JFirst.first r) then return false
  return JLe.le (← JLast.last r) (← JLast.last s)


/-! ## Unary minus, conversions and promotion (lines 1322-1414) -/

/--
Julia source: base/range.jl:1322-1322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(r::OrdinalRange) = range(-first(r), step=negate(step(r)), length=length(r))
```
-/
def neg_OrdinalRange {R T T' S S' Λ ρ : Type} [JFirst R T] [JNeg T T'] [JStep R S] [JNegate S S']
    [JLength R Λ] [JRangeStartKw T' Nothing Λ S' ρ] (r : R) : JlX ρ := do
  let start := JNeg.neg (← JFirst.first r)
  let step ← JNegate.negate (← JStep.step r)
  JRangeStartKw.range start Nothing.nothing (← JLength.length r) step

/--
Julia source: base/range.jl:1323-1324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(r::StepRangeLen{T,R,S,L}) where {T,R,S,L} =
    StepRangeLen{T,R,S,L}(-r.ref, -r.step, r.len, r.offset)
```
-/
def neg_StepRangeLen {T R S L : Type} [JNeg R R] [JNeg S S] [JStepRangeLenTRSL T R S L R S L L]
    (r : StepRangeLen T R S L) : JlX (StepRangeLen T R S L) :=
  JStepRangeLenTRSL.stepRangeLenTRSL (JNeg.neg r.ref) (JNeg.neg r.step) r.len r.offset

/--
Julia source: base/range.jl:1325-1329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(r::LinRange)
    start = -r.start
    LinRange{typeof(start)}(start, -r.stop, length(r))
end

```
-/
def neg_LinRange {T L T' Λ ρ : Type} [JNeg T T'] [JLength (LinRange T L) Λ] [JLinRangeT T' T' T' Λ ρ]
    (r : LinRange T L) : JlX ρ := do
  let start := JNeg.neg r.start
  JLinRangeT.linRangeT (T := T') start (JNeg.neg r.stop) (← JLength.length r)

/-- Julia types as values of a type `τ`, for the type-level methods `el_same` and
`promote_rule`: the range type constructors `UnitRange{T}`, `OneTo{T}`, `StepRange{T,S}`,
`StepRangeLen{T,R,S,L}`, `LinRange{T,L}` and the type `Int`. -/
class JRangeTypeOf (τ : Type) where
  unitRange : τ → τ
  oneTo : τ → τ
  stepRange : τ → τ → τ
  stepRangeLen : τ → τ → τ → τ → τ
  linRange : τ → τ → τ
  int : τ
/-- `eltype(T)` of a type value. -/
class JEltypeOf (τ : Type) where
  eltypeOf : τ → τ
/-- `promote_type(T, S)` of type values (promotion.jl). -/
class JPromoteTypeOf (τ : Type) where
  promoteTypeOf : τ → τ → τ
/-- `promote_typejoin(a, b)` of type values (promotion.jl). -/
class JPromoteTypejoinOf (τ : Type) where
  promoteTypejoinOf : τ → τ → τ
/-- `el_same(T, a, b)`, the generic function with the four methods below. -/
class JElSameOf (τ : Type) where
  elSame : τ → τ → τ → τ
/-- `promote_rule(a, b)` of type values (promotion.jl and the methods below). -/
class JPromoteRuleOf (τ : Type) where
  promoteRule : τ → τ → τ

/--
Julia source: base/range.jl:1330-1331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# promote eltype if at least one container wouldn't change, otherwise join container types.
el_same(::Type{T}, a::Type{<:AbstractArray{T,n}}, b::Type{<:AbstractArray{T,n}}) where {T,n}   = a # we assume a === b
```
-/
def el_same_T_T {τ : Type} (T a b : τ) : τ := a

/--
Julia source: base/range.jl:1332-1332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
el_same(::Type{T}, a::Type{<:AbstractArray{T,n}}, b::Type{<:AbstractArray{S,n}}) where {T,S,n} = a
```
-/
def el_same_T_S {τ : Type} (T a b : τ) : τ := a

/--
Julia source: base/range.jl:1333-1333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
el_same(::Type{T}, a::Type{<:AbstractArray{S,n}}, b::Type{<:AbstractArray{T,n}}) where {T,S,n} = b
```
-/
def el_same_S_T {τ : Type} (T a b : τ) : τ := b

/--
Julia source: base/range.jl:1334-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
el_same(::Type, a, b) = promote_typejoin(a, b)

```
-/
def el_same_Any {τ : Type} [JPromoteTypejoinOf τ] (T a b : τ) : τ :=
  JPromoteTypejoinOf.promoteTypejoinOf a b

/--
Julia source: base/range.jl:1336-1337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{UnitRange{T1}}, b::Type{UnitRange{T2}}) where {T1,T2} =
    el_same(promote_type(T1, T2), a, b)
```
-/
def promote_rule_UnitRange_UnitRange {τ : Type} [JRangeTypeOf τ] [JPromoteTypeOf τ] [JElSameOf τ]
    (T1 T2 : τ) : τ :=
  let a := JRangeTypeOf.unitRange T1
  let b := JRangeTypeOf.unitRange T2
  JElSameOf.elSame (JPromoteTypeOf.promoteTypeOf T1 T2) a b

/--
Julia source: base/range.jl:1338-1338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange{T}(r::UnitRange{T}) where {T<:Real} = r
```
-/
def UnitRange_T_UnitRange_T {T : Type} (r : UnitRange T) : UnitRange T := r

/--
Julia source: base/range.jl:1339-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange{T}(r::UnitRange) where {T<:Real} = UnitRange{T}(r.start, r.stop)

```
-/
def UnitRange_T_UnitRange {T U : Type} [JUnitRangeT T U U] (r : UnitRange U) : JlX (UnitRange T) :=
  JUnitRangeT.unitRangeT r.start r.stop

/--
Julia source: base/range.jl:1341-1342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{OneTo{T1}}, b::Type{OneTo{T2}}) where {T1,T2} =
    el_same(promote_type(T1, T2), a, b)
```
-/
def promote_rule_OneTo_OneTo {τ : Type} [JRangeTypeOf τ] [JPromoteTypeOf τ] [JElSameOf τ]
    (T1 T2 : τ) : τ :=
  let a := JRangeTypeOf.oneTo T1
  let b := JRangeTypeOf.oneTo T2
  JElSameOf.elSame (JPromoteTypeOf.promoteTypeOf T1 T2) a b

/--
Julia source: base/range.jl:1343-1343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OneTo{T}(r::OneTo{T}) where {T<:Integer} = r
```
-/
def OneTo_T_OneTo_T {T : Type} (r : OneTo T) : OneTo T := r

/--
Julia source: base/range.jl:1344-1345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OneTo{T}(r::OneTo) where {T<:Integer} = OneTo{T}(r.stop)

```
-/
def OneTo_T_OneTo {T U : Type} [JOneToT T U] (r : OneTo U) : JlX (OneTo T) :=
  JOneToT.oneToT r.stop

/--
Julia source: base/range.jl:1346-1348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{OneTo{T1}}, ::Type{UR}) where {T1,UR<:AbstractUnitRange} =
    promote_rule(UnitRange{T1}, UR)

```
-/
def promote_rule_OneTo_UR {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ] (T1 UR : τ) : τ :=
  JPromoteRuleOf.promoteRule (JRangeTypeOf.unitRange T1) UR

/--
Julia source: base/range.jl:1349-1350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{UnitRange{T1}}, ::Type{UR}) where {T1,UR<:AbstractUnitRange} =
    promote_rule(a, UnitRange{eltype(UR)})
```
-/
def promote_rule_UnitRange_UR {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ] [JEltypeOf τ]
    (T1 UR : τ) : τ :=
  let a := JRangeTypeOf.unitRange T1
  JPromoteRuleOf.promoteRule a (JRangeTypeOf.unitRange (JEltypeOf.eltypeOf UR))

/--
Julia source: base/range.jl:1351-1351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange{T}(r::AbstractUnitRange) where {T<:Real} = UnitRange{T}(first(r), last(r))
```
-/
def UnitRange_T_AbstractUnitRange {T R E : Type} [JFirst R E] [JLast R E] [JUnitRangeT T E E]
    (r : R) : JlX (UnitRange T) := do
  JUnitRangeT.unitRangeT (← JFirst.first r) (← JLast.last r)

/--
Julia source: base/range.jl:1352-1353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnitRange(r::AbstractUnitRange) = UnitRange(first(r), last(r))

```
-/
def UnitRange_AbstractUnitRange {R E ρ : Type} [JFirst R E] [JLast R E] [JUnitRange2 E E ρ]
    (r : R) : JlX ρ := do
  JUnitRange2.unitRange (← JFirst.first r) (← JLast.last r)

/--
Julia source: base/range.jl:1354-1354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractUnitRange{T}(r::AbstractUnitRange{T}) where {T} = r
```
-/
def AbstractUnitRange_T_AbstractUnitRange_T {R : Type} (r : R) : R := r

/--
Julia source: base/range.jl:1355-1355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractUnitRange{T}(r::UnitRange) where {T} = UnitRange{T}(r)
```
-/
def AbstractUnitRange_T_UnitRange {T U : Type} [JUnitRangeTOf T (UnitRange U)] (r : UnitRange U) :
    JlX (UnitRange T) :=
  JUnitRangeTOf.unitRangeTOf r

/--
Julia source: base/range.jl:1356-1357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractUnitRange{T}(r::OneTo) where {T} = OneTo{T}(r)

```
-/
def AbstractUnitRange_T_OneTo {T U : Type} [JOneToTOf T (OneTo U)] (r : OneTo U) : JlX (OneTo T) :=
  JOneToTOf.oneToTOf r

/--
Julia source: base/range.jl:1358-1358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OrdinalRange{T, S}(r::OrdinalRange) where {T, S} = StepRange{T, S}(r)
```
-/
def OrdinalRange_TS_OrdinalRange {T S R : Type} [JStepRangeTSOf T S R] (r : R) :
    JlX (StepRange T S) :=
  JStepRangeTSOf.stepRangeTSOf r

/--
Julia source: base/range.jl:1359-1360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OrdinalRange{T, T}(r::AbstractUnitRange) where {T} = AbstractUnitRange{T}(r)

```
-/
def OrdinalRange_TT_AbstractUnitRange {T R ρ : Type} [JAbstractUnitRangeT T R ρ] (r : R) : JlX ρ :=
  JAbstractUnitRangeT.abstractUnitRangeT (T := T) r

/--
Julia source: base/range.jl:1361-1365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(::Type{StepRange{T1a,T1b}}, ::Type{StepRange{T2a,T2b}}) where {T1a,T1b,T2a,T2b}
    Tb = promote_type(T1b, T2b)
    # el_same only operates on array element type, so just promote second type parameter
    el_same(promote_type(T1a, T2a), StepRange{T1a,Tb}, StepRange{T2a,Tb})
end
```
-/
def promote_rule_StepRange_StepRange {τ : Type} [JRangeTypeOf τ] [JPromoteTypeOf τ]
    [JElSameOf τ] (T1a T1b T2a T2b : τ) : τ :=
  let Tb := JPromoteTypeOf.promoteTypeOf T1b T2b
  JElSameOf.elSame (JPromoteTypeOf.promoteTypeOf T1a T2a) (JRangeTypeOf.stepRange T1a Tb)
    (JRangeTypeOf.stepRange T2a Tb)

/--
Julia source: base/range.jl:1366-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange{T1,T2}(r::StepRange{T1,T2}) where {T1,T2} = r
```
-/
def StepRange_TS_StepRange_TS {T S : Type} (r : StepRange T S) : StepRange T S := r

/--
Julia source: base/range.jl:1367-1367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange{T}(r::StepRange{T}) where {T} = r
```
-/
def StepRange_T_StepRange_T {T S : Type} (r : StepRange T S) : StepRange T S := r

/--
Julia source: base/range.jl:1368-1369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange(r::StepRange) = r

```
-/
def StepRange_StepRange {T S : Type} (r : StepRange T S) : StepRange T S := r

/--
Julia source: base/range.jl:1370-1371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{StepRange{T1a,T1b}}, ::Type{UR}) where {T1a,T1b,UR<:AbstractUnitRange} =
    promote_rule(a, StepRange{eltype(UR), eltype(UR)})
```
-/
def promote_rule_StepRange_UR {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ] [JEltypeOf τ]
    (T1a T1b UR : τ) : τ :=
  let a := JRangeTypeOf.stepRange T1a T1b
  JPromoteRuleOf.promoteRule a
    (JRangeTypeOf.stepRange (JEltypeOf.eltypeOf UR) (JEltypeOf.eltypeOf UR))

/--
Julia source: base/range.jl:1372-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange{T1,T2}(r::AbstractRange) where {T1,T2} =
    StepRange{T1,T2}(convert(T1, first(r)), convert(T2, step(r)), convert(T1, last(r)))
```
-/
def StepRange_TS_AbstractRange {T1 T2 R E S : Type} [JFirst R E] [JConvert T1 E] [JStep R S]
    [JConvert T2 S] [JLast R E] [JStepRangeTS T1 T2 T1 T2 T1] (r : R) :
    JlX (StepRange T1 T2) := do
  let a ← JConvert.convert (T := T1) (← JFirst.first r)
  let b ← JConvert.convert (T := T2) (← JStep.step r)
  let c ← JConvert.convert (T := T1) (← JLast.last r)
  JStepRangeTS.stepRangeTS a b c

/--
Julia source: base/range.jl:1374-1374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange(r::OrdinalRange{T,S}) where {T,S} = StepRange{T,S}(first(r), step(r), last(r))
```
-/
def StepRange_OrdinalRange {R T S : Type} [JFirst R T] [JStep R S] [JLast R T]
    [JStepRangeTS T S T S T] (r : R) : JlX (StepRange T S) := do
  JStepRangeTS.stepRangeTS (← JFirst.first r) (← JStep.step r) (← JLast.last r)

/--
Julia source: base/range.jl:1375-1375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange{T}(r::OrdinalRange{<:Any,S}) where {T,S} = StepRange{T,S}(first(r), step(r), last(r))
```
-/
def StepRange_T_OrdinalRange {T R E S : Type} [JFirst R E] [JStep R S] [JLast R E]
    [JStepRangeTS T S E S E] (r : R) : JlX (StepRange T S) := do
  JStepRangeTS.stepRangeTS (← JFirst.first r) (← JStep.step r) (← JLast.last r)

/--
Julia source: base/range.jl:1376-1376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(StepRange{T1,T2} where T1)(r::AbstractRange) where {T2} = StepRange{eltype(r),T2}(r)
```
-/
def StepRange_S_AbstractRange {T2 R E : Type} [JEltype R E] [JStepRangeTSOf E T2 R] (r : R) :
    JlX (StepRange E T2) :=
  JStepRangeTSOf.stepRangeTSOf r

/--
Julia source: base/range.jl:1377-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange(r::StepRangeLen) = StepRange{eltype(r)}(r)
```
-/
def StepRange_StepRangeLen {T R S L ρ : Type} [JStepRangeTOf T (StepRangeLen T R S L) ρ]
    (r : StepRangeLen T R S L) : JlX ρ :=
  JStepRangeTOf.stepRangeTOf (T := T) r

/--
Julia source: base/range.jl:1378-1379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRange{T}(r::StepRangeLen{<:Any,<:Any,S}) where {T,S} = StepRange{T,S}(r)

```
-/
def StepRange_T_StepRangeLen {T U R S L : Type} [JStepRangeTSOf T S (StepRangeLen U R S L)]
    (r : StepRangeLen U R S L) : JlX (StepRange T S) :=
  JStepRangeTSOf.stepRangeTSOf r

/--
Julia source: base/range.jl:1380-1383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(::Type{StepRangeLen{T1,R1,S1,L1}},::Type{StepRangeLen{T2,R2,S2,L2}}) where {T1,T2,R1,R2,S1,S2,L1,L2}
    R, S, L = promote_type(R1, R2), promote_type(S1, S2), promote_type(L1, L2)
    el_same(promote_type(T1, T2), StepRangeLen{T1,R,S,L}, StepRangeLen{T2,R,S,L})
end
```
-/
def promote_rule_StepRangeLen_StepRangeLen {τ : Type} [JRangeTypeOf τ] [JPromoteTypeOf τ]
    [JElSameOf τ] (T1 R1 S1 L1 T2 R2 S2 L2 : τ) : τ :=
  let R := JPromoteTypeOf.promoteTypeOf R1 R2
  let S := JPromoteTypeOf.promoteTypeOf S1 S2
  let L := JPromoteTypeOf.promoteTypeOf L1 L2
  JElSameOf.elSame (JPromoteTypeOf.promoteTypeOf T1 T2) (JRangeTypeOf.stepRangeLen T1 R S L)
    (JRangeTypeOf.stepRangeLen T2 R S L)

/--
Julia source: base/range.jl:1384-1384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S,L}(r::StepRangeLen{T,R,S,L}) where {T,R,S,L} = r
```
-/
def StepRangeLen_TRSL_same {T R S L : Type} (r : StepRangeLen T R S L) : StepRangeLen T R S L := r

/--
Julia source: base/range.jl:1385-1386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S,L}(r::StepRangeLen) where {T,R,S,L} =
    StepRangeLen{T,R,S,L}(convert(R, r.ref), convert(S, r.step), convert(L, r.len), convert(L, r.offset))
```
-/
def StepRangeLen_TRSL_StepRangeLen {T R S L T' R' S' L' : Type} [JConvert R R'] [JConvert S S']
    [JConvert L L'] [JStepRangeLenTRSL T R S L R S L L] (r : StepRangeLen T' R' S' L') :
    JlX (StepRangeLen T R S L) := do
  let a ← JConvert.convert (T := R) r.ref
  let b ← JConvert.convert (T := S) r.step
  let c ← JConvert.convert (T := L) r.len
  let d ← JConvert.convert (T := L) r.offset
  JStepRangeLenTRSL.stepRangeLenTRSL a b c d

/--
Julia source: base/range.jl:1387-1389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T}(r::StepRangeLen) where {T} =
    StepRangeLen(convert(T, r.ref), convert(T, r.step), r.len, r.offset)

```
-/
def StepRangeLen_T_StepRangeLen {T T' R' S' L' ρ : Type} [JConvert T R'] [JConvert T S']
    [JStepRangeLen4 T T L' L' ρ] (r : StepRangeLen T' R' S' L') : JlX ρ := do
  let a ← JConvert.convert (T := T) r.ref
  let b ← JConvert.convert (T := T) r.step
  JStepRangeLen4.stepRangeLen a b r.len r.offset

/--
Julia source: base/range.jl:1390-1391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{StepRangeLen{T,R,S,L}}, ::Type{OR}) where {T,R,S,L,OR<:AbstractRange} =
    promote_rule(a, StepRangeLen{eltype(OR), eltype(OR), eltype(OR), Int})
```
-/
def promote_rule_StepRangeLen_OR {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ] [JEltypeOf τ]
    (T R S L OR : τ) : τ :=
  let a := JRangeTypeOf.stepRangeLen T R S L
  let E := JEltypeOf.eltypeOf OR
  JPromoteRuleOf.promoteRule a (JRangeTypeOf.stepRangeLen E E E JRangeTypeOf.int)

/--
Julia source: base/range.jl:1392-1393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T,R,S,L}(r::AbstractRange) where {T,R,S,L} =
    StepRangeLen{T,R,S,L}(R(first(r)), S(step(r)), length(r))
```
-/
def StepRangeLen_TRSL_AbstractRange {T R S L Q E U Λ : Type} [JFirst Q E] [JCtor R E] [JStep Q U]
    [JCtor S U] [JLength Q Λ] [JStepRangeLenTRSL T R S L R S Λ JInt64] (r : Q) :
    JlX (StepRangeLen T R S L) := do
  let a ← JCtor.ctor (T := R) (← JFirst.first r)
  let b ← JCtor.ctor (T := S) (← JStep.step r)
  JStepRangeLenTRSL.stepRangeLenTRSL a b (← JLength.length r) (jint 1)

/--
Julia source: base/range.jl:1394-1395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen{T}(r::AbstractRange) where {T} =
    StepRangeLen(T(first(r)), T(step(r)), length(r))
```
-/
def StepRangeLen_T_AbstractRange {T Q E U Λ ρ : Type} [JFirst Q E] [JCtor T E] [JStep Q U]
    [JCtor T U] [JLength Q Λ] [JStepRangeLen3 T T Λ ρ] (r : Q) : JlX ρ := do
  let a ← JCtor.ctor (T := T) (← JFirst.first r)
  let b ← JCtor.ctor (T := T) (← JStep.step r)
  JStepRangeLen3.stepRangeLen a b (← JLength.length r)

/--
Julia source: base/range.jl:1396-1397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StepRangeLen(r::AbstractRange) = StepRangeLen{eltype(r)}(r)

```
-/
def StepRangeLen_AbstractRange {Q E ρ : Type} [JEltype Q E] [JStepRangeLenTOf E Q ρ] (r : Q) :
    JlX ρ :=
  JStepRangeLenTOf.stepRangeLenTOf (T := E) r

/--
Julia source: base/range.jl:1398-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_rule(a::Type{LinRange{T1,L1}}, b::Type{LinRange{T2,L2}}) where {T1,T2,L1,L2}
    L = promote_type(L1, L2)
    el_same(promote_type(T1, T2), LinRange{T1,L}, LinRange{T2,L})
end
```
-/
def promote_rule_LinRange_LinRange {τ : Type} [JRangeTypeOf τ] [JPromoteTypeOf τ] [JElSameOf τ]
    (T1 L1 T2 L2 : τ) : τ :=
  let L := JPromoteTypeOf.promoteTypeOf L1 L2
  JElSameOf.elSame (JPromoteTypeOf.promoteTypeOf T1 T2) (JRangeTypeOf.linRange T1 L)
    (JRangeTypeOf.linRange T2 L)

/--
Julia source: base/range.jl:1402-1402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinRange{T,L}(r::LinRange{T,L}) where {T,L} = r
```
-/
def LinRange_TL_same {T L : Type} (r : LinRange T L) : LinRange T L := r

/--
Julia source: base/range.jl:1403-1403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinRange{T,L}(r::AbstractRange) where {T,L} = LinRange{T,L}(first(r), last(r), length(r))
```
-/
def LinRange_TL_AbstractRange {T L Q E Λ : Type} [JFirst Q E] [JLast Q E] [JLength Q Λ]
    [JLinRangeTL T L E E Λ] (r : Q) : JlX (LinRange T L) := do
  JLinRangeTL.linRangeTL (← JFirst.first r) (← JLast.last r) (← JLength.length r)

/--
Julia source: base/range.jl:1404-1404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinRange{T}(r::AbstractRange) where {T} = LinRange{T,typeof(length(r))}(first(r), last(r), length(r))
```
-/
def LinRange_T_AbstractRange {T Q E Λ : Type} [JLength Q Λ] [JFirst Q E] [JLast Q E]
    [JLinRangeTL T Λ E E Λ] (r : Q) : JlX (LinRange T Λ) := do
  let _l ← JLength.length r
  JLinRangeTL.linRangeTL (← JFirst.first r) (← JLast.last r) (← JLength.length r)

/--
Julia source: base/range.jl:1405-1406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinRange(r::AbstractRange{T}) where {T} = LinRange{T}(r)

```
-/
def LinRange_AbstractRange {Q T ρ : Type} [JEltype Q T] [JLinRangeTOf T Q ρ] (r : Q) : JlX ρ :=
  JLinRangeTOf.linRangeTOf (T := T) r

/--
Julia source: base/range.jl:1407-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{LinRange{T,L}}, ::Type{OR}) where {T,L,OR<:OrdinalRange} =
    promote_rule(a, LinRange{eltype(OR),L})

```
-/
def promote_rule_LinRange_OR {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ] [JEltypeOf τ]
    (T L OR : τ) : τ :=
  let a := JRangeTypeOf.linRange T L
  JPromoteRuleOf.promoteRule a (JRangeTypeOf.linRange (JEltypeOf.eltypeOf OR) L)

/--
Julia source: base/range.jl:1410-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{LinRange{A,L}}, b::Type{StepRangeLen{T2,R2,S2,L2}}) where {A,L,T2,R2,S2,L2} =
    promote_rule(StepRangeLen{A,A,A,L}, b)

## concatenation ##

```
-/
def promote_rule_LinRange_StepRangeLen {τ : Type} [JRangeTypeOf τ] [JPromoteRuleOf τ]
    (A L T2 R2 S2 L2 : τ) : τ :=
  let b := JRangeTypeOf.stepRangeLen T2 R2 S2 L2
  JPromoteRuleOf.promoteRule (JRangeTypeOf.stepRangeLen A A A L) b

/-! ## Concatenation, collection, reversal, sorting, `sum`, `in` (lines 1415-1501) -/

/-- `Vector{T}(undef, n)`: a vector of `n` unassigned slots (`none`). -/
class JVectorUndef (T : Type) where
  vectorUndef : JInt64 → JlX (List (Option T))

/-- `@inbounds a[i] = x` on a vector: in bounds, the write; out of bounds, Julia's behaviour is
undefined, recorded as `Exc.inboundsViolation`. -/
def setindexInbounds {T : Type} (a : List (Option T)) (x : T) (i : JInt64) :
    JlX (List (Option T)) :=
  if 1 ≤ i.val ∧ i.val ≤ a.length then pure (a.set (i.val.toNat - 1) (some x))
  else throw .inboundsViolation

/--
Julia source: base/range.jl:1415-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vcat(rs::AbstractRange{T}...) where T
    n::Int = 0
    for ra in rs
        n = checked_add(n, length(ra))
    end
    a = Vector{T}(undef, n)
    i = 1
    for ra in rs, x in ra
        @inbounds a[i] = x
        i += 1
    end
    return a
end

# This method differs from that for AbstractArrays as it
# use iteration instead of indexing. This works even if certain
# non-standard ranges don't support indexing.
# See https://github.com/JuliaLang/julia/pull/27302
# Similarly, collect(r::AbstractRange) uses iteration
```
-/
def vcat_AbstractRange {R T Λ C St : Type} [JLength R Λ] [JCheckedAdd JInt64 Λ C]
    [JConvert JInt64 C] [JVectorUndef T] [JIterate1 R T St] [JIterate2 R St T] (rs : List R)
    (fuel : Nat) : JlX (List (Option T)) := do
  -- the varargs `rs` are ranges of one type `R`; `n::Int` converts each sum to `Int`
  let mut n : JInt64 := jint 0
  for ra in rs do
    n ← JConvert.convert (T := JInt64) (← JCheckedAdd.checkedAdd n (← JLength.length ra))
  let mut a ← JVectorUndef.vectorUndef (T := T) n
  let mut i : JInt64 := jint 1
  for ra in rs do
    (a, i) ← forIn ra (a, i) (fun x (a, i) => do
      let a ← setindexInbounds a x i
      pure (a, i + jint 1)) fuel
  return a

/--
Julia source: base/range.jl:1434-1442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Array{T,1}(r::AbstractRange{T}) where {T}
    a = Vector{T}(undef, length(r))
    i = 1
    for x in r
        @inbounds a[i] = x
        i += 1
    end
    return a
end
```
-/
def Array_T_1_AbstractRange {R T Λ St : Type} [JLength R Λ] [JConvert JInt64 Λ] [JVectorUndef T]
    [JIterate1 R T St] [JIterate2 R St T] (r : R) (fuel : Nat) : JlX (List (Option T)) := do
  let n ← JConvert.convert (T := JInt64) (← JLength.length r)
  let a ← JVectorUndef.vectorUndef (T := T) n
  let i : JInt64 := jint 1
  let (a, _) ← forIn r (a, i) (fun x (a, i) => do
    let a ← setindexInbounds a x i
    pure (a, i + jint 1)) fuel
  return a

/--
Julia source: base/range.jl:1443-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect(r::AbstractRange) = Array(r)

```
-/
def collect_AbstractRange {R ρ : Type} [JArray R ρ] (r : R) : JlX ρ := JArray.array r

/--
Julia source: base/range.jl:1445-1445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse(r::OrdinalRange, ::Colon) = (:)(last(r), negate(step(r)), first(r))
```
-/
def _reverse_OrdinalRange {R T S S' ρ : Type} [JLast R T] [JStep R S] [JNegate S S'] [JFirst R T]
    [JColon3 T S' T ρ] (r : R) (c : Colon) : JlX ρ := do
  let a ← JLast.last r
  let b ← JNegate.negate (← JStep.step r)
  let c ← JFirst.first r
  JColon3.colon a b c

/--
Julia source: base/range.jl:1446-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reverse(r::StepRangeLen, ::Colon)
    # If `r` is empty, `length(r) - r.offset + 1 will be nonpositive hence
    # invalid. As `reverse(r)` is also empty, any offset would work so we keep
    # `r.offset`
    offset = isempty(r) ? r.offset : length(r)-r.offset+1
    return typeof(r)(r.ref, negate(r.step), length(r), offset)
end
```
-/
def _reverse_StepRangeLen {T R S L S' Λ : Type} [JIsempty (StepRangeLen T R S L)]
    [JLength (StepRangeLen T R S L) L] [HSub L L L] [HAdd L JInt64 L] [JNegate S S']
    [JSameType4 (StepRangeLen T R S L) R S' L L] (r : StepRangeLen T R S L) (c : Colon) :
    JlX (StepRangeLen T R S L) := do
  let offset ← if ← JIsempty.isempty r then pure r.offset
    else do pure ((← JLength.length r) - r.offset + jint 1)
  JSameType4.make r.ref (← JNegate.negate r.step) (← JLength.length r) offset

/--
Julia source: base/range.jl:1453-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse(r::LinRange{T}, ::Colon) where {T} = typeof(r)(r.stop, r.start, length(r))

## sorting ##

```
-/
def _reverse_LinRange {T L Λ : Type} [JLength (LinRange T L) Λ] [JSameType3 (LinRange T L) T T Λ]
    (r : LinRange T L) (c : Colon) : JlX (LinRange T L) := do
  JSameType3.make r.stop r.start (← JLength.length r)

/--
Julia source: base/range.jl:1457-1457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issorted(r::AbstractUnitRange) = true
```
-/
def issorted_AbstractUnitRange {R : Type} (r : R) : Bool := true

/--
Julia source: base/range.jl:1458-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issorted(r::AbstractRange) = length(r) <= 1 || step(r) >= zero(step(r))

```
-/
def issorted_AbstractRange {R Λ S : Type} [JLength R Λ] [JLe Λ JInt64] [JStep R S] [JZero S]
    [JLe S S] (r : R) : JlX Bool := do
  if JLe.le (← JLength.length r) (jint 1) then return true
  let s ← JStep.step r
  -- `zero(step(r))` evaluates `step(r)` again for its type
  let _s ← JStep.step r
  return JLe.le (JZero.zero : S) s

/--
Julia source: base/range.jl:1460-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort(r::AbstractUnitRange) = r
```
-/
def sort_AbstractUnitRange {R : Type} (r : R) : R := r

/--
Julia source: base/range.jl:1461-1462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort!(r::AbstractUnitRange) = r

```
-/
def sort!_AbstractUnitRange {R : Type} (r : R) : R := r

/--
Julia source: base/range.jl:1463-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort(r::AbstractRange) = issorted(r) ? r : reverse(r)

```
-/
def sort_AbstractRange {R ρ : Type} [JIssorted R] [JReverse R ρ] (r : R) : JlX (R ⊕ ρ) := do
  if ← JIssorted.issorted r then return .inl r
  return .inr (← JReverse.reverse r)

/--
Julia source: base/range.jl:1465-1465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sortperm(r::AbstractUnitRange) = eachindex(r)
```
-/
def sortperm_AbstractUnitRange {R ρ : Type} [JEachindex R ρ] (r : R) : JlX ρ :=
  JEachindex.eachindex r

/--
Julia source: base/range.jl:1466-1467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sortperm(r::AbstractRange) = issorted(r) ? (firstindex(r):1:lastindex(r)) : (lastindex(r):-1:firstindex(r))

```
-/
def sortperm_AbstractRange {R I ρ : Type} [JIssorted R] [JFirstindex R I] [JLastindex R I]
    [JColon3 I JInt64 I ρ] (r : R) : JlX ρ := do
  if ← JIssorted.issorted r then
    JColon3.colon (← JFirstindex.firstindex r) (jint 1) (← JLastindex.lastindex r)
  else
    JColon3.colon (← JLastindex.lastindex r) (jint (-1)) (← JFirstindex.firstindex r)

/--
Julia source: base/range.jl:1468-1474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sum(r::AbstractRange{<:Real})
    l = length(r)
    # note that a little care is required to avoid overflow in l*(l-1)/2
    return l * first(r) + (iseven(l) ? (step(r) * (l-1)) * (l>>1)
                                     : (step(r) * l) * ((l-1)>>1))
end

```
-/
def sum_AbstractRange {R Λ T S P A B C D : Type} [JLength R Λ] [HMul Λ T P] [JFirst R T]
    [JIseven Λ] [JStep R S] [HSub Λ JInt64 Λ] [HMul S Λ A] [JShr Λ JInt64 Λ] [HMul A Λ B]
    [HAdd P B C] (r : R) : JlX C := do
  let l ← JLength.length r
  let p := l * (← JFirst.first r)
  let q ← if JIseven.iseven l then do
      pure ((← JStep.step r) * (l - jint 1) * JShr.shr l (jint 1))
    else do
      pure ((← JStep.step r) * l * JShr.shr (l - jint 1) (jint 1))
  return p + q

/--
Julia source: base/range.jl:1475-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _in_range(x, r::AbstractRange)
    isempty(r) && return false
    f, l = first(r), last(r)
    # check for NaN, Inf, and large x that may overflow in the next calculation
    f <= x <= l || l <= x <= f || return false
    iszero(step(r)) && return true
    n = round(Integer, (x - f) / step(r)) + 1
    n >= 1 && n <= length(r) && r[n] == x
end
```
-/
def _in_range {X R T S D Q N Λ : Type} [JIsempty R] [JFirst R T] [JLast R T] [JLe T X] [JLe X T]
    [JStep R S] [JIszero S] [HSub X T D] [HDiv D S Q] [JRoundInteger Q N] [HAdd N JInt64 N]
    [JLe JInt64 N] [JLength R Λ] [JLe N Λ] [JGetindex R N T] [JEq T X] (x : X) (r : R) :
    JlX Bool := do
  if ← JIsempty.isempty r then return false
  let f ← JFirst.first r
  let l ← JLast.last r
  unless (JLe.le f x && JLe.le x l) || (JLe.le l x && JLe.le x f) do return false
  if JIszero.iszero (← JStep.step r) then return true
  let n := (← JRoundInteger.roundInteger ((x - f) / (← JStep.step r))) + jint 1
  if !JLe.le (jint 1) n then return false
  if !JLe.le n (← JLength.length r) then return false
  return JEq.eq (← JGetindex.getindex r n) x

/-- `_in_range(x, r)`. -/
class JInRange (X R : Type) where
  inRange : X → R → JlX Bool

/--
Julia source: base/range.jl:1484-1484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::Real, r::AbstractRange{<:Real}) = _in_range(x, r)
```
-/
def in_Real_AbstractRange {X R : Type} [JInRange X R] (x : X) (r : R) : JlX Bool :=
  JInRange.inRange x r

/--
Julia source: base/range.jl:1485-1487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This method needs to be defined separately since -(::T, ::T) can be implemented
# even if -(::T, ::Real) is not
in(x::T, r::AbstractRange{T}) where {T} = _in_range(x, r)
```
-/
def in_T_AbstractRange {X R : Type} [JInRange X R] (x : X) (r : R) : JlX Bool :=
  JInRange.inRange x r

/--
Julia source: base/range.jl:1488-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

in(x::Integer, r::AbstractUnitRange{<:Integer}) = (first(r) <= x) & (x <= last(r))
```
-/
def in_Integer_AbstractUnitRange {X R T : Type} [JFirst R T] [JLe T X] [JLast R T] [JLe X T]
    (x : X) (r : R) : JlX Bool := do
  let a := JLe.le (← JFirst.first r) x
  let b := JLe.le x (← JLast.last r)
  return a && b

/--
Julia source: base/range.jl:1490-1494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

in(x::Real, r::AbstractRange{T}) where {T<:Integer} =
    isinteger(x) && !isempty(r) &&
    (iszero(step(r)) ? x == first(r) : (x >= minimum(r) && x <= maximum(r) &&
        (mod(convert(T,x),step(r))-mod(first(r),step(r)) == 0)))
```
-/
def in_Real_AbstractRange_Integer {X R T S M : Type} [JIsinteger X] [JIsempty R] [JStep R S]
    [JIszero S] [JFirst R T] [JEq X T] [JMinimum R T] [JLe T X] [JMaximum R T] [JLe X T]
    [JConvert T X] [JMod T S M] [HSub M M M] [JEq M JInt64] (x : X) (r : R) : JlX Bool := do
  if !JIsinteger.isinteger x then return false
  if ← JIsempty.isempty r then return false
  if JIszero.iszero (← JStep.step r) then
    return JEq.eq x (← JFirst.first r)
  else
    if !JLe.le (← JMinimum.minimum r) x then return false
    if !JLe.le x (← JMaximum.maximum r) then return false
    let a ← JMod.mod (← JConvert.convert (T := T) x) (← JStep.step r)
    let b ← JMod.mod (← JFirst.first r) (← JStep.step r)
    return JEq.eq (a - b) (jint 0)

/--
Julia source: base/range.jl:1495-1501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::AbstractChar, r::AbstractRange{<:AbstractChar}) =
    !isempty(r) &&
    (iszero(step(r)) ? x == first(r) : (x >= minimum(r) && x <= maximum(r) &&
        (mod(Int(x) - Int(first(r)), step(r)) == 0)))

# Addition/subtraction of ranges

```
-/
def in_AbstractChar_AbstractRange {X R T S M : Type} [JIsempty R] [JStep R S] [JIszero S]
    [JFirst R T] [JEq X T] [JMinimum R T] [JLe T X] [JMaximum R T] [JLe X T] [JCtor JInt64 X]
    [JCtor JInt64 T] [JMod JInt64 S M] [JEq M JInt64] (x : X) (r : R) : JlX Bool := do
  if ← JIsempty.isempty r then return false
  if JIszero.iszero (← JStep.step r) then
    return JEq.eq x (← JFirst.first r)
  else
    if !JLe.le (← JMinimum.minimum r) x then return false
    if !JLe.le x (← JMaximum.maximum r) then return false
    let a : JInt64 ← JCtor.ctor x
    let b : JInt64 ← JCtor.ctor (← JFirst.first r)
    return JEq.eq (← JMod.mod (a - b) (← JStep.step r)) (jint 0)


/-! ## Range addition and subtraction (lines 1502-1535) -/

-- Reason: `_define_range_op(f)` is a metaprogram that `@eval`s three methods of `f` for `f` in `+`, `-` (lines 1524-1525); the generated methods are modelled below, generic in the operator `F` (`JScalarOp F` is `f` on scalars, `JRangeOp F` is `f` on ranges).
-- UNTRANSLATED
-- Source: base/range.jl:1502-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _define_range_op(@nospecialize f)
--     @eval begin
--         function $f(r1::OrdinalRange, r2::OrdinalRange)
--             r1l = length(r1)
--             (r1l == length(r2) ||
--              throw(DimensionMismatch("argument dimensions must match: length of r1 is $r1l, length of r2 is $(length(r2))")))
--             StepRangeLen($f(first(r1), first(r2)), $f(step(r1), step(r2)), r1l)
--         end
-- 
--         function $f(r1::LinRange{T}, r2::LinRange{T}) where T
--             len = r1.len
--             (len == r2.len ||
--              throw(DimensionMismatch("argument dimensions must match: length of r1 is $len, length of r2 is $(r2.len)")))
--             LinRange{T}(convert(T, $f(first(r1), first(r2))),
--                         convert(T, $f(last(r1), last(r2))), len)
--         end
-- 
--         $f(r1::Union{StepRangeLen, OrdinalRange, LinRange},
--            r2::Union{StepRangeLen, OrdinalRange, LinRange}) =
--                $f(promote(r1, r2)...)
--     end
-- end
-- _define_range_op(:+)
-- _define_range_op(:-)
-- 
-- /Source

/--
Julia source: base/range.jl:1504-1509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $f(r1::OrdinalRange, r2::OrdinalRange)
            r1l = length(r1)
            (r1l == length(r2) ||
             throw(DimensionMismatch("argument dimensions must match: length of r1 is $r1l, length of r2 is $(length(r2))")))
            StepRangeLen($f(first(r1), first(r2)), $f(step(r1), step(r2)), r1l)
        end
```
-/
def rangeop_OrdinalRange_OrdinalRange (F : Type) {R Q T U S V L M A B ρ : Type} [JLength R L]
    [JLength Q M] [JEq L M] [JPrint L] [JPrint M] [JFirst R T] [JFirst Q U] [JScalarOp F T U A]
    [JStep R S] [JStep Q V] [JScalarOp F S V B] [JStepRangeLen3 A B L ρ] (r1 : R) (r2 : Q) :
    JlX ρ := do
  let r1l ← JLength.length r1
  unless JEq.eq r1l (← JLength.length r2) do
    throw (.dimensionMismatch ("argument dimensions must match: length of r1 is " ++
      JPrint.print r1l ++ ", length of r2 is " ++ JPrint.print (← JLength.length r2)))
  let a := JScalarOp.scalarOp F (← JFirst.first r1) (← JFirst.first r2)
  let b := JScalarOp.scalarOp F (← JStep.step r1) (← JStep.step r2)
  JStepRangeLen3.stepRangeLen a b r1l

/--
Julia source: base/range.jl:1511-1517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $f(r1::LinRange{T}, r2::LinRange{T}) where T
            len = r1.len
            (len == r2.len ||
             throw(DimensionMismatch("argument dimensions must match: length of r1 is $len, length of r2 is $(r2.len)")))
            LinRange{T}(convert(T, $f(first(r1), first(r2))),
                        convert(T, $f(last(r1), last(r2))), len)
        end
```
-/
def rangeop_LinRange_LinRange (F : Type) {T L A ρ : Type} [JEq L L] [JPrint L]
    [JFirst (LinRange T L) T] [JLast (LinRange T L) T] [JScalarOp F T T A] [JConvert T A]
    [JLinRangeT T T T L ρ] (r1 r2 : LinRange T L) : JlX ρ := do
  let len := r1.len
  unless JEq.eq len r2.len do
    throw (.dimensionMismatch ("argument dimensions must match: length of r1 is " ++
      JPrint.print len ++ ", length of r2 is " ++ JPrint.print r2.len))
  let a ← JConvert.convert (T := T) (JScalarOp.scalarOp F (← JFirst.first r1) (← JFirst.first r2))
  let b ← JConvert.convert (T := T) (JScalarOp.scalarOp F (← JLast.last r1) (← JLast.last r2))
  JLinRangeT.linRangeT (T := T) a b len

/--
Julia source: base/range.jl:1519-1521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f(r1::Union{StepRangeLen, OrdinalRange, LinRange},
           r2::Union{StepRangeLen, OrdinalRange, LinRange}) =
               $f(promote(r1, r2)...)
```
-/
def rangeop_promote (F : Type) {R Q P ρ : Type} [JPromoteRanges R Q P] [JRangeOp F P P ρ]
    (r1 : R) (r2 : Q) : JlX ρ := do
  let (a, b) ← JPromoteRanges.promoteRanges r1 r2
  JRangeOp.rangeOp F a b

/--
Julia source: base/range.jl:1527-1533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S}) where {T,S}
    len = length(r1)
    (len == length(r2) ||
     throw(DimensionMismatch("argument dimensions must match: length of r1 is $len, length of r2 is $(length(r2))")))
    StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), len)
end

```
-/
def plus_StepRangeLen_StepRangeLen {T S R L L' A B ρ : Type}
    [JLength (StepRangeLen T S R L) L'] [JEq L' L'] [JPrint L'] [JFirst (StepRangeLen T S R L) T]
    [HAdd T T A] [JStep (StepRangeLen T S R L) R] [HAdd R R B] [JStepRangeLen3 A B L' ρ]
    (r1 r2 : StepRangeLen T S R L) : JlX ρ := do
  let len ← JLength.length r1
  unless JEq.eq len (← JLength.length r2) do
    throw (.dimensionMismatch ("argument dimensions must match: length of r1 is " ++
      JPrint.print len ++ ", length of r2 is " ++ JPrint.print (← JLength.length r2)))
  let a := (← JFirst.first r1) + (← JFirst.first r2)
  let b := (← JStep.step r1) + (← JStep.step r2)
  JStepRangeLen3.stepRangeLen a b len

/--
Julia source: base/range.jl:1534-1535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(r1::StepRangeLen, r2::StepRangeLen) = +(r1, -r2)

```
-/
def minus_StepRangeLen_StepRangeLen {R Q N ρ : Type} [JNegRange Q N] [JRangeOp PlusOp R N ρ]
    (r1 : R) (r2 : Q) : JlX ρ := do
  JRangeOp.rangeOp PlusOp r1 (← JNegRange.negRange r2)

/-! ## `mod`, `logrange`, `LogRange` (lines 1536-1746) -/

/--
Julia source: base/range.jl:1536-1558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
# Modular arithmetic on ranges

"""
    mod(x::Integer, r::AbstractUnitRange)

Find `y` in the range `r` such that `x` ≡ `y` (mod `n`), where `n = length(r)`,
i.e. `y = mod(x - first(r), n) + first(r)`.

See also [`mod1`](@ref).

# Examples
```jldoctest
julia> mod(0, Base.OneTo(3))  # mod1(0, 3)
3

julia> mod(3, 0:2)  # mod(3, 3)
0
```

!!! compat "Julia 1.3"
     This method requires at least Julia 1.3.
"""
mod(i::Integer, r::OneTo) = mod1(i, last(r))
````
-/
def mod_Integer_OneTo {I T M : Type} [JLast (OneTo T) T] [JMod1 I T M] (i : I) (r : OneTo T) :
    JlX M := do
  JMod1.mod1 i (← JLast.last r)

/--
Julia source: base/range.jl:1559-1561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(i::Integer, r::AbstractUnitRange{<:Integer}) = mod(i-first(r), length(r)) + first(r)


```
-/
def mod_Integer_AbstractUnitRange {I R T D Λ M A : Type} [JFirst R T] [HSub I T D] [JLength R Λ]
    [JMod D Λ M] [HAdd M T A] (i : I) (r : R) : JlX A := do
  let m ← JMod.mod (i - (← JFirst.first r)) (← JLength.length r)
  return m + (← JFirst.first r)

/--
Julia source: base/range.jl:1562-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    logrange(start, stop, length)
    logrange(start, stop; length)

Construct a specialized array whose elements are spaced logarithmically
between the given endpoints. That is, the ratio of successive elements is
a constant, calculated from the length.

This is similar to `geomspace` in Python. Unlike `PowerRange` in Mathematica,
you specify the number of elements not the ratio.
Unlike `logspace` in Python and Matlab, the `start` and `stop` arguments are
always the first and last elements of the result, not powers applied to some base.

# Examples
```jldoctest
julia> logrange(10, 4000, length=3)
3-element Base.LogRange{Float64, Base.TwicePrecision{Float64}}:
 10.0, 200.0, 4000.0

julia> ans[2] ≈ sqrt(10 * 4000)  # middle element is the geometric mean
true

julia> range(10, 40, length=3)[2] ≈ (10 + 40)/2  # arithmetic mean
true

julia> logrange(1f0, 32f0, 11)
11-element Base.LogRange{Float32, Float64}:
 1.0, 1.41421, 2.0, 2.82843, 4.0, 5.65685, 8.0, 11.3137, 16.0, 22.6274, 32.0

julia> logrange(1, 1000, length=4) ≈ 10 .^ (0:3)
true
```

See the [`LogRange`](@ref Base.LogRange) type for further details.

See also [`range`](@ref) for linearly spaced points.

!!! compat "Julia 1.11"
    This function requires at least Julia 1.11.
"""
logrange(start::Real, stop::Real, length::Integer) = LogRange(start, stop, Int(length))
````
-/
def logrange {A B Λ ρ : Type} [JCtor JInt64 Λ] [JLogRange3 A B JInt64 ρ] (start : A) (stop : B)
    (length : Λ) : JlX ρ := do
  JLogRange3.logRange start stop (← JCtor.ctor (T := JInt64) length)

/-- `logrange(start, stop, length)`. -/
class JLogrange3 (A B Λ : Type) (ρ : outParam Type) where
  logrange : A → B → Λ → JlX ρ

/--
Julia source: base/range.jl:1603-1605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
logrange(start::Real, stop::Real; length::Integer) = logrange(start, stop, length)


```
-/
def logrange_kw {A B Λ ρ : Type} [JLogrange3 A B Λ ρ] (start : A) (stop : B) (length : Λ) :
    JlX ρ :=
  JLogrange3.logrange start stop length

/--
Julia source: base/range.jl:1660-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function LogRange{T}(start::T, stop::T, len::Int) where {T<:Real}
        if T <: Integer
            # LogRange{Int}(1, 512, 4) produces InexactError: Int64(7.999999999999998)
            throw(ArgumentError("LogRange{T} does not support integer types"))
        end
        if iszero(start) || iszero(stop)
            throw(DomainError((start, stop),
                "LogRange cannot start or stop at zero"))
        elseif start < 0 || stop < 0
            # log would throw, but _log_twice64_unchecked does not
            throw(DomainError((start, stop),
                "LogRange does not accept negative numbers"))
        elseif !isfinite(start) || !isfinite(stop)
            throw(DomainError((start, stop),
                "LogRange is only defined for finite start & stop"))
        elseif len < 0
            throw(ArgumentError(LazyString(
                "LogRange(", start, ", ", stop, ", ", len, "): can't have negative length")))
        elseif len == 1 && start != stop
            throw(ArgumentError(LazyString(
                "LogRange(", start, ", ", stop, ", ", len, "): endpoints differ, while length is 1")))
        end
        ex = _logrange_extra(start, stop, len)
        new{T,typeof(ex[1])}(start, stop, len, ex)
    end
end

```
-/
def LogRange_T_new {T X : Type} [JType T] [JIszero T] [JLt T JInt64] [JIsfinite T] [JPrint T]
    [JEq T T] [JLograngeExtra T T X] (start stop : T) (len : JInt64) : JlX (LogRange T X) := do
  if JType.isInteger T then
    throw (.jl (.argumentError "LogRange{T} does not support integer types"))
  if JIszero.iszero start || JIszero.iszero stop then
    throw (.jl (.domainError "LogRange cannot start or stop at zero"))
  else if JLt.lt start (jint 0) || JLt.lt stop (jint 0) then
    throw (.jl (.domainError "LogRange does not accept negative numbers"))
  else if !JIsfinite.isfinite start || !JIsfinite.isfinite stop then
    throw (.jl (.domainError "LogRange is only defined for finite start & stop"))
  else if len.val < 0 then
    throw (.jl (.argumentError ("LogRange(" ++ JPrint.print start ++ ", " ++ JPrint.print stop ++
      ", " ++ toString len.val ++ "): can't have negative length")))
  else if len.val = 1 && !JEq.eq start stop then
    throw (.jl (.argumentError ("LogRange(" ++ JPrint.print start ++ ", " ++ JPrint.print stop ++
      ", " ++ toString len.val ++ "): endpoints differ, while length is 1")))
  let ex ← JLograngeExtra.lograngeExtra start stop len
  return ⟨start, stop, len, ex⟩

/--
Julia source: base/range.jl:1687-1689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function LogRange{T}(start::Real, stop::Real, len::Integer) where {T}
    LogRange{T}(convert(T, start), convert(T, stop), convert(Int, len))
end
```
-/
def LogRange_T_Real {T A B Λ ρ : Type} [JConvert T A] [JConvert T B] [JConvert JInt64 Λ]
    [JLogRangeT T T T JInt64 ρ] (start : A) (stop : B) (len : Λ) : JlX ρ := do
  let a ← JConvert.convert (T := T) start
  let b ← JConvert.convert (T := T) stop
  let n ← JConvert.convert (T := JInt64) len
  JLogRangeT.logRangeT (T := T) a b n

/--
Julia source: base/range.jl:1690-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function LogRange(start::Real, stop::Real, len::Integer)
    T = float(promote_type(typeof(start), typeof(stop)))
    LogRange{T}(convert(T, start), convert(T, stop), convert(Int, len))
end

```
-/
def LogRange_Real {A B Λ P T ρ : Type} [JPromoteType A B P] [JFloatType P T] [JConvert T A]
    [JConvert T B] [JConvert JInt64 Λ] [JLogRangeT T T T JInt64 ρ] (start : A) (stop : B)
    (len : Λ) : JlX ρ := do
  let a ← JConvert.convert (T := T) start
  let b ← JConvert.convert (T := T) stop
  let n ← JConvert.convert (T := JInt64) len
  JLogRangeT.logRangeT (T := T) a b n

/--
Julia source: base/range.jl:1695-1695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(r::LogRange) = (r.len,)
```
-/
def size_LogRange {T X : Type} (r : LogRange T X) : Tuple1 JInt64 := ⟨r.len⟩

/--
Julia source: base/range.jl:1696-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::LogRange) = r.len

```
-/
def length_LogRange {T X : Type} (r : LogRange T X) : JInt64 := r.len

/--
Julia source: base/range.jl:1698-1698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::LogRange) = r.start
```
-/
def first_LogRange {T X : Type} (r : LogRange T X) : T := r.start

/--
Julia source: base/range.jl:1699-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::LogRange) = r.stop

```
-/
def last_LogRange {T X : Type} (r : LogRange T X) : T := r.stop

/-- The `Float64` literal `1.0`. -/
class JFloat64Lit (F : Type) where
  one : F

/--
Julia source: base/range.jl:1701-1705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _logrange_extra(a::Real, b::Real, len::Int)
    loga = log(1.0 * a)  # widen to at least Float64
    logb = log(1.0 * b)
    (loga/(len-1), logb/(len-1))
end
```
-/
def _logrange_extra_Real {A B F P Q X : Type} [JFloat64Lit F] [HMul F A P] [JLog P X]
    [HMul F B Q] [JLog Q X] [HDiv X JInt64 X] (a : A) (b : B) (len : JInt64) : JlX (X × X) := do
  let loga ← JLog.log ((JFloat64Lit.one : F) * a)
  let logb ← JLog.log ((JFloat64Lit.one : F) * b)
  return (loga / (len - jint 1), logb / (len - jint 1))

/--
Julia source: base/range.jl:1706-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _logrange_extra(a::Float64, b::Float64, len::Int)
    loga = _log_twice64_unchecked(a)
    logb = _log_twice64_unchecked(b)
    # The reason not to do linear interpolation on log(a)..log(b) in `getindex` is
    # that division of TwicePrecision is quite slow, so do it once on construction:
    (loga/(len-1), logb/(len-1))
end

```
-/
def _logrange_extra_Float64 {F X : Type} [JLogTwice64 F X] [JSlash X JInt64 X] (a b : F)
    (len : JInt64) : JlX (X × X) := do
  let loga ← JLogTwice64.logTwice64 a
  let logb ← JLogTwice64.logTwice64 b
  return (← JSlash.slash loga (len - jint 1), ← JSlash.slash logb (len - jint 1))

/--
Julia source: base/range.jl:1714-1725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(r::LogRange{T}, i::Int) where {T}
    @inline
    @boundscheck checkbounds(r, i)
    i == 1 && return r.start
    i == r.len && return r.stop
    # Main path uses Math.exp_impl for TwicePrecision, but is not perfectly
    # accurate, hence the special cases for endpoints above.
    logx = (r.len-i) * r.extra[1] + (i-1) * r.extra[2]
    x = _exp_allowing_twice64(logx)
    return T(x)
end

```
-/
def getindex_LogRange {T X P W E : Type} [JCheckbounds (LogRange T X) JInt64]
    [HMul JInt64 X P] [HAdd P P W] [JExpTwice64 W E] [JCtor T E]
    (r : LogRange T X) (i : JInt64) : JlX T := do
  JCheckbounds.checkbounds r i
  if i.val = 1 then return r.start
  if i.val = r.len.val then return r.stop
  let logx : W := (r.len - i) * r.extra.1 + (i - jint 1) * r.extra.2
  let x ← JExpTwice64.expTwice64 logx
  JCtor.ctor (T := T) x

/--
Julia source: base/range.jl:1726-1736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, r::LogRange{T}) where {T}
    print(io, "LogRange{", T, "}(")
    ioc = IOContext(io, :typeinfo => T)
    show(ioc, first(r))
    print(io, ", ")
    show(ioc, last(r))
    print(io, ", ")
    show(io, length(r))
    print(io, ')')
end

```
-/
def show_LogRange {T X : Type} [JShowType T] [JFirst (LogRange T X) T] [JLast (LogRange T X) T]
    [JShowTypeinfo T T] [JLength (LogRange T X) JInt64] [JShow JInt64] (io : JIO) (r : LogRange T X) : JlX String := do
  let mut out := "LogRange{" ++ JShowType.showType T ++ "}("
  let _ioc : IOTypeinfo T := ⟨io⟩
  out := out ++ (← JShowTypeinfo.showTypeinfo (T := T) (← JFirst.first r))
  out := out ++ ", "
  out := out ++ (← JShowTypeinfo.showTypeinfo (T := T) (← JLast.last r))
  out := out ++ ", "
  out := out ++ (← JShow.showValue (← JLength.length r))
  out := out ++ ")"
  return out

-- Reason: `_resolve_in_world` validates a binding partition of the running system image for the `@world` macro (essentials.jl); it operates on compiler world-age state, which this model does not represent.
-- UNTRANSLATED
-- Source: base/range.jl:1737-1746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Implementation detail of @world
-- # The rest of this is defined in essentials.jl, but UnitRange is not available
-- function _resolve_in_world(worlds::UnitRange, gr::GlobalRef)
--     # Validate that this binding's reference covers the entire world range
--     bpart = lookup_binding_partition(UInt(first(worlds)), gr)
--     if bpart.max_world < last(worlds)
--         error("Binding does not cover the full world range")
--     end
--     _resolve_in_world(UInt(last(worlds)), gr)
-- end
-- /Source

end JuliaLean.base.range
