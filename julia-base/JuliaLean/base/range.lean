import JuliaLean.base.checked
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.Runtime.Strings
import JuliaLean.base.bool
import JuliaLean.base.ntuple
import JuliaLean.Runtime.Collections

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
  | showError (error : JuliaLean.Strings.ShowErrorKind)
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

-- Reason: The docstring of `print_range`: no method body.
-- UNTRANSLATED
-- Source: base/range.jl:647-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source

/-- `div(a, b)` of two `Int`s: `DivideError` for `b == 0` and for `div(typemin(Int), -1)`. -/
def divInt (a b : JInt64) : JlX JInt64 :=
  if b.val = 0 || (a.val = IntTy.i64.min && b.val = -1) then .error (.jl .divideError)
  else .ok (JInt.wrap .i64 (a.val.tdiv b.val))

/-- The `Int` range `a:b` as a list. -/
def unitRangeList (a b : JInt64) : List JInt64 :=
  if b.val < a.val then [] else (List.range (b.val - a.val + 1).toNat).map fun (k : Nat) => a + jint (k : Int)


/--
Julia source: base/range.jl:660-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_range(io::IO, r::AbstractArray,
                     pre::AbstractString = " ",
                     sep::AbstractString = ", ",
                     post::AbstractString = "",
                     hdots::AbstractString = ", \u2026, ") # horiz ellipsis
    # This function borrows from print_matrix() in show.jl
    # and should be called by show and display
    sz = displaysize(io)
    if !haskey(io, :compact)
        io = IOContext(io, :compact => true)
    end
    _, screenwidth = sz[1] - 4, sz[2]
    screenwidth -= length(pre) + length(post)
    sepsize = length(sep)
    m = 1 # treat the range as a one-row matrix
    n = length(r)
    # Figure out spacing alignments for r, but only need to examine the
    # left and right edge columns, as many as could conceivably fit on the
    # screen, with the middle columns summarized by horz, vert, or diag ellipsis
    maxpossiblecols = div(screenwidth, 1+sepsize) # assume each element is at least 1 char + 1 separator
    colsr = n <= maxpossiblecols ? (1:n) : [1:div(maxpossiblecols,2)+1; (n-div(maxpossiblecols,2)):n]
    rowmatrix = reshape(r[colsr], 1, length(colsr)) # treat the range as a one-row matrix for print_matrix_row
    nrow, idxlast = size(rowmatrix, 2), last(axes(rowmatrix, 2))
    A = alignment(io, rowmatrix, 1:m, 1:length(rowmatrix), screenwidth, screenwidth, sepsize, nrow) # how much space range takes
    if n <= length(A) # cols fit screen, so print out all elements
        print(io, pre) # put in pre chars
        print_matrix_row(io,rowmatrix,A,1,1:n,sep,idxlast) # the entire range
        print(io, post) # add the post characters
    else # cols don't fit so put horiz ellipsis in the middle
        # how many chars left after dividing width of screen in half
        # and accounting for the horiz ellipsis
        c = div(screenwidth-length(hdots)+1,2)+1 # chars remaining for each side of rowmatrix
        alignR = reverse(alignment(io, rowmatrix, 1:m, length(rowmatrix):-1:1, c, c, sepsize, nrow)) # which cols of rowmatrix to put on the right
        c = screenwidth - sum(map(sum,alignR)) - (length(alignR)-1)*sepsize - length(hdots)
        alignL = alignment(io, rowmatrix, 1:m, 1:length(rowmatrix), c, c, sepsize, nrow) # which cols of rowmatrix to put on the left
        print(io, pre)   # put in pre chars
        print_matrix_row(io, rowmatrix,alignL,1,1:length(alignL),sep,idxlast) # left part of range
        print(io, hdots) # horizontal ellipsis
        print_matrix_row(io, rowmatrix,alignR,1,length(rowmatrix)-length(alignR)+1:length(rowmatrix),sep,idxlast) # right part of range
        print(io, post)  # post chars
    end
end

```
-/
def print_range {Io R E : Type} (displaysize : Io → JlX (JInt64 × JInt64))
    (haskeyCompact : Io → Bool) (withCompact : Io → Io) (length : R → JlX JInt64)
    (getindex : R → JInt64 → JlX E)
    (alignment : Io → List E → List JInt64 → List JInt64 → JInt64 → JInt64 → JInt64 → JInt64 →
      JlX (List (JInt64 × JInt64)))
    (print_matrix_row : Io → List E → List (JInt64 × JInt64) → JInt64 → List JInt64 → String →
      JInt64 → JlX String)
    (io : Io) (r : R) (pre : String := " ") (sep : String := ", ") (post : String := "")
    (hdots : String := ", \u2026, ") : JlX String := do
  let len (s : String) : JInt64 := jint s.length
  let sz ← displaysize io
  let io := if !haskeyCompact io then withCompact io else io
  let screenwidth := sz.2
  let screenwidth := screenwidth - (len pre + len post)
  let sepsize := len sep
  let m := jint 1
  let n ← length r
  let maxpossiblecols ← divInt screenwidth (jint 1 + sepsize)
  let colsr ← if n.val ≤ maxpossiblecols.val then pure (unitRangeList (jint 1) n)
    else do
      let half ← divInt maxpossiblecols (jint 2)
      pure (unitRangeList (jint 1) (half + jint 1) ++ unitRangeList (n - half) n)
  let rowmatrix ← colsr.mapM (getindex r)
  let nrow := jint rowmatrix.length
  let idxlast := jint rowmatrix.length
  let A ← alignment io rowmatrix (unitRangeList (jint 1) m) (unitRangeList (jint 1) (jint rowmatrix.length))
    screenwidth screenwidth sepsize nrow
  if n.val ≤ A.length then
    let row ← print_matrix_row io rowmatrix A (jint 1) (unitRangeList (jint 1) n) sep idxlast
    pure (pre ++ row ++ post)
  else
    let c := (← divInt (screenwidth - len hdots + jint 1) (jint 2)) + jint 1
    let alignR := (← alignment io rowmatrix (unitRangeList (jint 1) m)
      (unitRangeList (jint 1) (jint rowmatrix.length)).reverse c c sepsize nrow).reverse
    let widths := alignR.foldl (fun acc (a, b) => acc + (a + b)) (jint 0)
    let c := screenwidth - widths - (jint alignR.length - jint 1) * sepsize - len hdots
    let alignL ← alignment io rowmatrix (unitRangeList (jint 1) m)
      (unitRangeList (jint 1) (jint rowmatrix.length)) c c sepsize nrow
    let left ← print_matrix_row io rowmatrix alignL (jint 1) (unitRangeList (jint 1) (jint alignL.length))
      sep idxlast
    let right ← print_matrix_row io rowmatrix alignR (jint 1)
      (unitRangeList (jint rowmatrix.length - jint alignR.length + jint 1) (jint rowmatrix.length)) sep idxlast
    pure (pre ++ left ++ hdots ++ right ++ post)

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
def inUnitRange {Element Value Index : Type} {m : Type → Type} [Monad m]
    (positive : Index → m Bool) (leStop : Value → Element → m Bool)
    (leStart : Element → Value → m Bool)
    (range : UnitRange Element) (value : Value) (index : Index) : m Bool := do
  if !(← positive index) then return false
  if !(← leStop value range.stop) then return false
  leStart range.start value

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
def getindexUnitRange {Element Index Difference Value : Type} {m : Type → Type} [Monad m]
    (oneunit : Index → m Index) (sub : Index → Index → m Difference)
    (add : Element → Difference → m Value) (convert : Value → m Element)
    (bounds : UnitRange Element → Element → Index → m Bool)
    (throwBounds : UnitRange Element → Index → m Empty)
    (range : UnitRange Element) (index : Index) : m Element := do
  let value ← convert (← add range.start (← sub index (← oneunit index)))
  if !(← bounds range value index) then
    return Empty.elim (← throwBounds range index)
  pure value

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
def getindexUnitRangeOverflowSafe {Element Index Difference Value : Type} {m : Type → Type} [Monad m]
    (oneunit : Index → m Index) (sub : Index → Index → m Difference)
    (add : Element → Difference → m Value)
    (bounds : UnitRange Element → Value → Index → m Bool)
    (throwBounds : UnitRange Element → Index → m Empty)
    (remainder : Value → m Element)
    (range : UnitRange Element) (index : Index) : m Element := do
  let value ← add range.start (← sub index (← oneunit index))
  if !(← bounds range value index) then
    return Empty.elim (← throwBounds range index)
  remainder value

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

structure FindinOps (m : Type → Type) (R Span Z Out : Type) where
  integer : Int → Z
  firstSpan : Span → m Z
  lastSpan : Span → m Z
  firstRange : R → m Z
  lastRange : R → m Z
  step : R → m Z
  length : R → m Z
  less : Z → Z → m Bool
  lessEqual : Z → Z → m Bool
  subtract : Z → Z → m Z
  add : Z → Z → m Z
  cld : Z → Z → m Z
  isAbstractUnitRange : R → Bool
  colon2 : Z → Z → m Out
  colon3 : Z → Z → Z → m Out

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
def findinRange {R Span Z Out : Type} {m : Type → Type} [Monad m]
    (ops : FindinOps m R Span Z Out) (range : R) (span : Span) : m Out := do
  let firstSpan ← ops.firstSpan span
  let lastSpan ← ops.lastSpan span
  let firstRange ← ops.firstRange range
  let lastRange ← ops.lastRange range
  let step ← ops.step range
  let (firstIndex, lastIndex) ←
    if ← ops.less (ops.integer 0) step then do
      let firstIndex ← if ← ops.lessEqual firstSpan firstRange then pure (ops.integer 1)
        else ops.add (← ops.cld (← ops.subtract firstSpan firstRange) step) (ops.integer 1)
      let lastIndex ← if ← ops.lessEqual lastRange lastSpan then ops.length range
        else ops.subtract (← ops.length range) (← ops.cld (← ops.subtract lastRange lastSpan) step)
      pure (firstIndex, lastIndex)
    else if ← ops.less step (ops.integer 0) then do
      let firstIndex ← if ← ops.lessEqual firstRange lastSpan then pure (ops.integer 1)
        else ops.add (← ops.cld (← ops.subtract lastSpan firstRange) step) (ops.integer 1)
      let lastIndex ← if ← ops.lessEqual firstSpan lastRange then ops.length range
        else ops.subtract (← ops.length range) (← ops.cld (← ops.subtract lastRange firstSpan) step)
      pure (firstIndex, lastIndex)
    else do
      let firstIndex ← if ← ops.lessEqual firstSpan firstRange then pure (ops.integer 1)
        else ops.add (← ops.length range) (ops.integer 1)
      let lastIndex ← if ← ops.lessEqual firstRange lastSpan then ops.length range
        else pure (ops.integer 0)
      pure (firstIndex, lastIndex)
  if ops.isAbstractUnitRange range then ops.colon2 firstIndex lastIndex
  else ops.colon3 firstIndex (ops.integer 1) lastIndex

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

inductive RangeMethodKind where
  | ordinalRange
  | linRange
  | promotedRanges
  deriving DecidableEq

structure RangeMethodInstaller (F : Type) where
  /-- Registers the generated signature with the body modelled below. -/
  install : F → RangeMethodKind → Jl Unit

/-!
Julia source: base/range.jl:1502-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _define_range_op(@nospecialize f)
    @eval begin
        function $f(r1::OrdinalRange, r2::OrdinalRange)
            r1l = length(r1)
            (r1l == length(r2) ||
             throw(DimensionMismatch("argument dimensions must match: length of r1 is $r1l, length of r2 is $(length(r2))")))
            StepRangeLen($f(first(r1), first(r2)), $f(step(r1), step(r2)), r1l)
        end

        function $f(r1::LinRange{T}, r2::LinRange{T}) where T
            len = r1.len
            (len == r2.len ||
             throw(DimensionMismatch("argument dimensions must match: length of r1 is $len, length of r2 is $(r2.len)")))
            LinRange{T}(convert(T, $f(first(r1), first(r2))),
                        convert(T, $f(last(r1), last(r2))), len)
        end

        $f(r1::Union{StepRangeLen, OrdinalRange, LinRange},
           r2::Union{StepRangeLen, OrdinalRange, LinRange}) =
               $f(promote(r1, r2)...)
    end
end
```
-/
def defineRangeOp {F : Type} (ops : RangeMethodInstaller F) (f : F) : Jl Unit := do
  ops.install f .ordinalRange
  ops.install f .linRange
  ops.install f .promotedRanges

-- Reason: These top-level forms invoke the typed registrar; they are not method definitions.
-- UNTRANSLATED
-- Source: base/range.jl:1524-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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

-- Reason: A comment.
-- UNTRANSLATED
-- Source: base/range.jl:1737-1738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Implementation detail of @world
-- # The rest of this is defined in essentials.jl, but UnitRange is not available
-- /Source


/--
Julia source: base/range.jl:1739-1746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _resolve_in_world(worlds::UnitRange, gr::GlobalRef)
    # Validate that this binding's reference covers the entire world range
    bpart = lookup_binding_partition(UInt(first(worlds)), gr)
    if bpart.max_world < last(worlds)
        error("Binding does not cover the full world range")
    end
    _resolve_in_world(UInt(last(worlds)), gr)
end
```
-/
-- Source: base/range.jl:1739-1746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def resolveInWorldRange {T E F GR BP Out : Type}
    (first : UnitRange T → JlX E) (toUIntFirst : E → JlX (JInt .u64))
    (lookup : JInt .u64 → GR → JlX BP) (maxWorld : BP → JInt .u64)
    (last : UnitRange T → JlX F) (less : JInt .u64 → F → JlX Bool)
    (toUIntLast : F → JlX (JInt .u64)) (resolve : JInt .u64 → GR → JlX Out)
    (worlds : UnitRange T) (gr : GR) : JlX Out := do
  let bpart ← lookup (← toUIntFirst (← first worlds)) gr
  if ← less (maxWorld bpart) (← last worlds) then
    throw (.errorException "Binding does not cover the full world range")
  resolve (← toUIntLast (← last worlds)) gr

-- Source: base/range.jl:1739-1746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def _resolve_in_world {GR BP α : Type} (lookup_binding_partition : JInt .u64 → GR → JlX BP)
    (max_world : BP → JInt .u64) (resolveInWorldUInt : JInt .u64 → GR → JlX α)
    (worlds : UnitRange JInt64) (gr : GR) : JlX α :=
  let toUInt (x : JInt64) : JlX (JInt .u64) :=
    (JInt.convert "convert" .u64 x.val).mapError .jl
  resolveInWorldRange (fun r => .ok r.start) toUInt lookup_binding_partition max_world
    (fun r => .ok r.stop) (fun a b => .ok (decide (a.val < b.val)))
    toUInt resolveInWorldUInt worlds gr

/-! The `Int` instances behind `colon_T_T_Real` at `T = Int`, so a model can call range.jl:5
without importing a proof file. -/

section IntRangeInstances

variable {s t : IntTy}

open JuliaLean.base.range
open JuliaLean.base.int (le lit subWrap)

/-- A `base/int.jl` computation inside a range method: its `JlError` is the range exception. -/
def liftJl {α : Type} (x : Jl α) : JlX α :=
  match x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-- `x <= y` on BitIntegers (`base/int.jl`). -/
instance : JLe (JInt s) (JInt t) := ⟨le⟩
/-- `oneunit(T) = T(one(T))` (`number.jl`). -/
instance : JOneunit (JInt t) := ⟨lit t 1⟩
/-- `x -% y` (`base/int.jl:92`). -/
instance : JWrappingSub (JInt t) (JInt t) (JInt t) := ⟨subWrap⟩
/-- range.jl:36. -/
instance : JRangeWrappingSub (JInt t) (JInt t) (JInt t) := ⟨_range_wrapping_sub_BitInteger⟩
/-- `convert(T, x)` between BitIntegers (`boot.jl` checked conversions, `base/int.jl`). -/
instance : JConvert (JInt t) (JInt s) := ⟨fun x => liftJl (JuliaLean.base.int.convert t x)⟩
/-- `unitrange_last(start::Integer, stop::Integer)`, range.jl:439. -/
instance : JUnitrangeLast (JInt t) (JInt t) := ⟨unitrange_last_Integer⟩
/-- `UnitRange{T}(start::T, stop::T)`, range.jl:428. -/
instance : JUnitRangeT (JInt t) (JInt t) (JInt t) := ⟨UnitRange_T_new⟩

end IntRangeInstances

end JuliaLean.base.range

namespace JuliaLean.base.range.Models1Group7

open JuliaLean

/-- Closed BitInteger instantiation of the existing Bool conversion model.
Julia source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
-- /Source
def boolOfBitInteger {t : IntTy} (x : JInt t) : JlX Bool :=
  liftJl (JuliaLean.base.bool.boolFromReal
    (fun value n => pure (JuliaLean.base.int.eq value (jint n))) x)

/-- The empty integer-range endpoint has the independently specified stop type.
The two arithmetic branches may have different intermediate result types; the declared
Julia return type converts only the branch actually selected.
Julia source: base/range.jl:389-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:389-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
def steprangeLastEmptyInteger {A S T D P : Type}
    [JZero S] [JLt S S] [JOneunit S]
    [JRangeWrappingSub A S D] [JRangeWrappingAdd A S P]
    [JConvert T D] [JConvert T P]
    (start : A) (step : S) (stop : T) : JlX T := do
  let last : D ⊕ P :=
    if JLt.lt (JZero.zero : S) step then
      .inl (JRangeWrappingSub.rangeWrappingSub start (JOneunit.oneunit : S))
    else
      .inr (JRangeWrappingAdd.rangeWrappingAdd start (JOneunit.oneunit : S))
  match last with
  | .inl value => JConvert.convert (T := T) value
  | .inr value => JConvert.convert (T := T) value

/-- The Bool empty-endpoint helper ignores stop, with no restriction on its type.
There is no declared return conversion in this specialization.
Julia source: base/range.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- steprange_last_empty(start::Bool, step, stop) = start ⊻ (step > zero(step)) # isnegative(step) ? start : !start
-- /Source
def steprangeLastEmptyBool {S B : Type} [JZero S] [JLt S S]
    (start : Bool) (step : S) (stop : B) : JlX Bool :=
  pure (xor start (JLt.lt (JZero.zero : S) step))

/-- OneTo scalar construction with the conversion performed by new.
The intermediate max result has its own type M. The existing Bool error helper is reused.
The field conversion is mandated by doc/src/manual/conversion-and-promotion.md:99-107.
Julia source: base/range.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source
def oneToStop {T A M : Type} [JType T] [JPrint A] [JZero T]
    [JMax T A M] [JConvert T M] (stop : A) : JlX (OneTo T) := do
  if JType.isBool T then
    OneTo_T.throwbool stop
  let value ← JMax.max (JZero.zero : T) stop
  let stored ← JConvert.convert (T := T) value
  return ⟨stored⟩

/-- OneTo range construction keeps the first/step/Bool checks and their error order.
The existing throw helpers perform their additional first/step observation at the original
point. Only after these checks are last, max and the implicit field conversion evaluated.
First and last may have independently represented result types.
Julia source: base/range.jl:493-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:493-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(r::AbstractRange) where {T<:Integer}
--         throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
--         throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         first(r) == 1 || throwstart(r)
--         step(r)  == 1 || throwstep(r)
--         T === Bool && throwbool(r)
--         return new(max(zero(T), last(r)))
--     end
-- /Source
def oneToRange {T R F S E M : Type}
    [JFirst R F] [JPrint F] [JEq F JInt64]
    [JStep R S] [JPrint S] [JEq S JInt64]
    [JType T] [JPrint R] [JLast R E] [JZero T]
    [JMax T E M] [JConvert T M] (r : R) : JlX (OneTo T) := do
  unless JEq.eq (← JFirst.first r) (jint 1) do
    OneTo_T_range.throwstart r
  unless JEq.eq (← JStep.step r) (jint 1) do
    OneTo_T_range.throwstep r
  if JType.isBool T then
    OneTo_T_range.throwbool r
  let zero : T := JZero.zero
  let last ← JLast.last r
  let value ← JMax.max zero last
  let stored ← JConvert.convert (T := T) value
  return ⟨stored⟩


/-- StepRangeLen inner construction keeps the chained offset comparison short-circuited.
The upper bound and max are evaluated only after the lower bound succeeds. The maximum
may have an independent intermediate type M; no new interface class is introduced.
Julia source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- /Source
def stepRangeLenNew (T : Type) {R S X L N O M : Type}
    [JType T] [HAdd R S X] [JIsinteger X]
    [JConvert L N] [JZero L] [JLe L L] [JPrint L]
    [JConvert L O] [JOneunit L] [JMax L L M] [JLe L M]
    (ref : R) (step : S) (len : N) (offset : O) :
    JlX (StepRangeLen T R S L) := do
  if JType.isInteger T then
    unless JIsinteger.isinteger (ref + step) do
      throw (.jl (.argumentError "StepRangeLen{<:Integer} cannot have non-integer step"))
  let len ← JConvert.convert (T := L) len
  unless JLe.le (JZero.zero : L) len do
    throw (.jl (.argumentError ("length cannot be negative, got " ++ JPrint.print len)))
  let offset ← JConvert.convert (T := L) offset
  let L1 : L := JOneunit.oneunit
  unless JLe.le L1 offset do
    throw (.jl (.argumentError ("StepRangeLen: offset must be in [1," ++ JPrint.print len ++
      "], got " ++ JPrint.print offset)))
  unless JLe.le offset (← JMax.max L1 len) do
    throw (.jl (.argumentError ("StepRangeLen: offset must be in [1," ++ JPrint.print len ++
      "], got " ++ JPrint.print offset)))
  return ⟨ref, step, len, offset⟩

/-- The generated shorter StepRangeLen inner-constructor method supplies the Int literal 1.
The full source body above is shared through stepRangeLenNew.
Julia source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- /Source
def stepRangeLenNewDefault (T : Type) {R S X L N M : Type}
    [JType T] [HAdd R S X] [JIsinteger X]
    [JConvert L N] [JZero L] [JLe L L] [JPrint L]
    [JConvert L JInt64] [JOneunit L] [JMax L L M] [JLe L M]
    (ref : R) (step : S) (len : N) : JlX (StepRangeLen T R S L) :=
  stepRangeLenNew T ref step len (jint 1)

/-- LinRange inner construction permits the subtraction and maximum to change the
length type, including the Bool length case. The stored lendiv is converted only at new.
The integer-only remainder test is explicitly short-circuited; noninteger endpoints do not
evaluate the remainder callee. All other callees remain the original explicit interface.
Julia source: base/range.jl:597-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:597-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}
--         len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
--         onelen = oneunit(typeof(len))
--         if len == onelen
--             start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ"))
--             return new(start, stop, len, len)
--         end
--         lendiv = max(len - onelen, onelen)
--         if T <: Integer && !iszero(mod(stop-start, lendiv))
--             throw(ArgumentError("LinRange{<:Integer} cannot have non-integer step"))
--         end
--         return new(start, stop, len, lendiv)
--     end
-- /Source
def linRangeNew {T L D M A B : Type}
    [JLe JInt64 L] [JPrint T] [JPrint L] [JOneunit L]
    [JEq L L] [JEq T T] [HSub L L D] [JMax D L M]
    [JType T] [HSub T T A] [JMod A M B] [JIszero B]
    [JConvert L M] (start stop : T) (len : L) : JlX (LinRange T L) := do
  unless JLe.le (jint 0) len do
    throw (.jl (.argumentError ("range(" ++ JPrint.print start ++ ", stop=" ++
      JPrint.print stop ++ ", length=" ++ JPrint.print len ++ "): negative length")))
  let onelen : L := JOneunit.oneunit
  if JEq.eq len onelen then
    unless JEq.eq start stop do
      throw (.jl (.argumentError ("range(" ++ JPrint.print start ++ ", stop=" ++
        JPrint.print stop ++ ", length=" ++ JPrint.print len ++ "): endpoints differ")))
    return ⟨start, stop, len, len⟩
  let lendiv ← JMax.max (len - onelen) onelen
  if JType.isInteger T then
    let remainder ← JMod.mod (stop - start) lendiv
    unless JIszero.iszero remainder do
      throw (.jl (.argumentError "LinRange{<:Integer} cannot have non-integer step"))
  let storedDiv ← JConvert.convert (T := L) lendiv
  return ⟨start, stop, len, storedDiv⟩

end JuliaLean.base.range.Models1Group7

/-! Closed dispatch bindings for the OneTo constructors.
All dictionaries here are closed values, installed only with letI. They add no global instances.
The concrete numeric domain is the ten BitInteger types; the range domain is Int64 StepRange.
The existing pure JPrint boundary observes decimal text, not general mutable IO execution.
-/
namespace JuliaLean.base.range.Models1Group7

open JuliaLean

/-- Closed type metadata for a machine integer; this is dispatch data, not an invented callee. -/
def oneToBitIntegerType (t : IntTy) : JType (JInt t) where
  isBool := false
  isSigned := t.signed
  isInteger := true
  isAbstractFloat := false
  bool_eq := by intro h; cases h

/-- Closed Bool type metadata for the existing dispatch boundary. -/
def oneToBoolType : JType Bool where
  isBool := true
  isSigned := false
  isInteger := true
  isAbstractFloat := false
  bool_eq := fun _ => rfl

/-- Closed BitInteger instantiation of OneTo scalar construction, base/range.jl:487.
The numeric operations are the existing int.jl models. Decimal JPrint is the same pure
observation boundary used by the frozen proof world; it handles every signed/unsigned input.
No callee or correctness law is supplied by the user of this function. -/
-- Source: base/range.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source
def oneToStopBits (target source : IntTy) (stop : JInt source) :
    JlX (OneTo (JInt target)) :=
  letI : JType (JInt target) := oneToBitIntegerType target
  letI : JPrint (JInt source) := ⟨fun x => toString x.val⟩
  letI : JZero (JInt target) := ⟨JuliaLean.base.int.lit target 0⟩
  letI : JMax (JInt target) (JInt source) (JInt (target.promote source)) :=
    ⟨fun x y => pure (JuliaLean.base.int.jmax x y)⟩
  letI : JConvert (JInt target) (JInt (target.promote source)) :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert target x)⟩
  oneToStop (T := JInt target) (M := JInt (target.promote source)) stop

/-- Closed Bool-target instantiation for every BitInteger stop, base/range.jl:487.
The otherwise unreachable numeric dictionaries are nevertheless genuine: Bool promotes to
its numeric partner (base/bool.jl:6), and boolOfBitInteger implements base/bool.jl:170.
No default-value substitute is used for a failing conversion. -/
-- Source: base/range.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source
def oneToStopBitsBoolTarget (source : IntTy) (stop : JInt source) :
    JlX (OneTo Bool) :=
  letI : JType Bool := oneToBoolType
  letI : JPrint (JInt source) := ⟨fun x => toString x.val⟩
  letI : JZero Bool := ⟨false⟩
  letI : JMax Bool (JInt source) (JInt source) :=
    ⟨fun x y => pure (JuliaLean.base.int.remT source
      (JuliaLean.base.int.jmax (JuliaLean.base.int.ofBool source x) y))⟩
  letI : JConvert Bool (JInt source) := ⟨boolOfBitInteger⟩
  oneToStop (T := Bool) (M := JInt source) stop

/-- Closed OneTo conversion of an Int64 StepRange, base/range.jl:493.
first, step, and last call the frozen range models. Printing is a closed interpretation of
the existing JPrint text boundary; its value is truthful even on the unused Bool-error path.
The corresponding property restricts raw records only by a constructible-field invariant. -/
-- Source: base/range.jl:493-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(r::AbstractRange) where {T<:Integer}
--         throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
--         throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         first(r) == 1 || throwstart(r)
--         step(r)  == 1 || throwstep(r)
--         T === Bool && throwbool(r)
--         return new(max(zero(T), last(r)))
--     end
-- /Source
def oneToRangeI64 (target : IntTy) (r : StepRange JInt64 JInt64) :
    JlX (OneTo (JInt target)) :=
  letI : JType (JInt target) := oneToBitIntegerType target
  letI : JPrint JInt64 := ⟨fun x => toString x.val⟩
  letI : JEq JInt64 JInt64 := ⟨JuliaLean.base.int.eq⟩
  letI : JConvert JInt64 JInt64 :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert .i64 x)⟩
  letI : JEltype (StepRange JInt64 JInt64) JInt64 := ⟨⟩
  letI : JFieldStart (StepRange JInt64 JInt64) JInt64 := ⟨StepRange.start⟩
  letI : JFieldStop (StepRange JInt64 JInt64) JInt64 := ⟨StepRange.stop⟩
  letI : JFirst (StepRange JInt64 JInt64) JInt64 := ⟨first_OrdinalRange⟩
  letI : JStep (StepRange JInt64 JInt64) JInt64 := ⟨fun q => pure (step_StepRange q)⟩
  letI : JLast (StepRange JInt64 JInt64) JInt64 := ⟨last_OrdinalRange⟩
  -- Concrete interpretation of the EXISTING pure JPrint observation boundary.
  -- Default Int64 StepRange interpolation uses range.jl:1135 and Signed repr:
  -- decimal first, ':', decimal step, ':', decimal last.
  -- This does not introduce or claim a replacement mutable IO/show model.
  letI : JPrint (StepRange JInt64 JInt64) :=
    ⟨fun q => toString q.start.val ++ ":" ++ toString q.step.val ++ ":" ++ toString q.stop.val⟩
  letI : JZero (JInt target) := ⟨JuliaLean.base.int.lit target 0⟩
  letI : JMax (JInt target) JInt64 (JInt (target.promote .i64)) :=
    ⟨fun x y => pure (JuliaLean.base.int.jmax x y)⟩
  letI : JConvert (JInt target) (JInt (target.promote .i64)) :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert target x)⟩
  oneToRange (T := JInt target) (F := JInt64) (S := JInt64) (E := JInt64)
    (M := JInt (target.promote .i64)) r

/-- Closed Bool-target OneTo conversion of an Int64 StepRange, base/range.jl:493.
This exercises the source priority first check, then step check, then Bool rejection.
The max and Bool conversion bindings remain correct although that final path cannot run. -/
-- Source: base/range.jl:493-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(r::AbstractRange) where {T<:Integer}
--         throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
--         throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         first(r) == 1 || throwstart(r)
--         step(r)  == 1 || throwstep(r)
--         T === Bool && throwbool(r)
--         return new(max(zero(T), last(r)))
--     end
-- /Source
def oneToRangeI64BoolTarget (r : StepRange JInt64 JInt64) : JlX (OneTo Bool) :=
  letI : JType Bool := oneToBoolType
  letI : JPrint JInt64 := ⟨fun x => toString x.val⟩
  letI : JEq JInt64 JInt64 := ⟨JuliaLean.base.int.eq⟩
  letI : JConvert JInt64 JInt64 :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert .i64 x)⟩
  letI : JEltype (StepRange JInt64 JInt64) JInt64 := ⟨⟩
  letI : JFieldStart (StepRange JInt64 JInt64) JInt64 := ⟨StepRange.start⟩
  letI : JFieldStop (StepRange JInt64 JInt64) JInt64 := ⟨StepRange.stop⟩
  letI : JFirst (StepRange JInt64 JInt64) JInt64 := ⟨first_OrdinalRange⟩
  letI : JStep (StepRange JInt64 JInt64) JInt64 := ⟨fun q => pure (step_StepRange q)⟩
  letI : JLast (StepRange JInt64 JInt64) JInt64 := ⟨last_OrdinalRange⟩
  -- Concrete interpretation of the EXISTING pure JPrint observation boundary.
  -- Default Int64 StepRange interpolation uses range.jl:1135 and Signed repr:
  -- decimal first, ':', decimal step, ':', decimal last.
  -- This does not introduce or claim a replacement mutable IO/show model.
  letI : JPrint (StepRange JInt64 JInt64) :=
    ⟨fun q => toString q.start.val ++ ":" ++ toString q.step.val ++ ":" ++ toString q.stop.val⟩
  letI : JZero Bool := ⟨false⟩
  letI : JMax Bool JInt64 JInt64 :=
    ⟨fun x y => pure (JuliaLean.base.int.remT .i64
      (JuliaLean.base.int.jmax (JuliaLean.base.int.ofBool .i64 x) y))⟩
  letI : JConvert Bool JInt64 := ⟨boolOfBitInteger⟩
  oneToRange (T := Bool) (F := JInt64) (S := JInt64) (E := JInt64) (M := JInt64) r

end JuliaLean.base.range.Models1Group7


namespace JuliaLean.base.range.Models1Group7

open JuliaLean

/-- Closed BitInteger dispatch for the repaired StepRangeLen inner constructor. Every
scalar argument and stored length uses JInt. Arithmetic, comparisons, maximum and conversion
call imported base.int models. The concrete isinteger binding is the constant Integer method
of base/number.jl:22; type tests are exact facts about the selected IntTy.
Julia source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- /Source
def stepRangeLenBits (t l : IntTy) {r s n o : IntTy}
    (ref : JInt r) (step : JInt s) (len : JInt n) (offset : JInt o) :
    JlX (StepRangeLen (JInt t) (JInt r) (JInt s) (JInt l)) :=
  letI : JType (JInt t) :=
    { isBool := false, isSigned := t.signed, isInteger := true,
      isAbstractFloat := false, bool_eq := by intro h; cases h }
  letI : HAdd (JInt r) (JInt s) (JInt (r.promote s)) :=
    ⟨fun x y => JuliaLean.base.int.binop JuliaLean.base.int.add x y⟩
  letI : JIsinteger (JInt (r.promote s)) := ⟨fun _ => true⟩
  letI : JConvert (JInt l) (JInt n) :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert l x)⟩
  letI : JConvert (JInt l) (JInt o) :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert l x)⟩
  letI : JZero (JInt l) := ⟨JuliaLean.base.int.lit l 0⟩
  letI : JLe (JInt l) (JInt l) := ⟨JuliaLean.base.int.le⟩
  letI : JPrint (JInt l) := ⟨fun x => toString x.val⟩
  letI : JOneunit (JInt l) := ⟨JuliaLean.base.int.lit l 1⟩
  letI : JMax (JInt l) (JInt l) (JInt (l.promote l)) :=
    ⟨fun x y => pure (JuliaLean.base.int.jmax x y)⟩
  letI : JLe (JInt l) (JInt (l.promote l)) := ⟨JuliaLean.base.int.le⟩
  stepRangeLenNew (JInt t) (L := JInt l) ref step len offset

/-- Closed BitInteger dispatch for the generated default-offset constructor. The default
is the Julia Int value one, including when the explicit length has another machine type.
Julia source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:533-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- /Source
def stepRangeLenBitsDefault (t l : IntTy) {r s n : IntTy}
    (ref : JInt r) (step : JInt s) (len : JInt n) :
    JlX (StepRangeLen (JInt t) (JInt r) (JInt s) (JInt l)) :=
  letI : JType (JInt t) :=
    { isBool := false, isSigned := t.signed, isInteger := true,
      isAbstractFloat := false, bool_eq := by intro h; cases h }
  letI : HAdd (JInt r) (JInt s) (JInt (r.promote s)) :=
    ⟨fun x y => JuliaLean.base.int.binop JuliaLean.base.int.add x y⟩
  letI : JIsinteger (JInt (r.promote s)) := ⟨fun _ => true⟩
  letI : JConvert (JInt l) (JInt n) :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert l x)⟩
  letI : JConvert (JInt l) JInt64 :=
    ⟨fun x => liftJl (JuliaLean.base.int.convert l x)⟩
  letI : JZero (JInt l) := ⟨JuliaLean.base.int.lit l 0⟩
  letI : JLe (JInt l) (JInt l) := ⟨JuliaLean.base.int.le⟩
  letI : JPrint (JInt l) := ⟨fun x => toString x.val⟩
  letI : JOneunit (JInt l) := ⟨JuliaLean.base.int.lit l 1⟩
  letI : JMax (JInt l) (JInt l) (JInt (l.promote l)) :=
    ⟨fun x y => pure (JuliaLean.base.int.jmax x y)⟩
  letI : JLe (JInt l) (JInt (l.promote l)) := ⟨JuliaLean.base.int.le⟩
  stepRangeLenNewDefault (JInt t) (L := JInt l) ref step len

/-- Closed Int64-endpoint, Bool-length dispatch of linRangeNew. Both Bool lengths and
all Int64 endpoints are represented, including overflowing endpoint subtraction. Required
Bool subtraction/conversion are concrete local source models. The promoted max returns Int64
until the final Bool field conversion.
Julia source: base/range.jl:597-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:597-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}
--         len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
--         onelen = oneunit(typeof(len))
--         if len == onelen
--             start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ"))
--             return new(start, stop, len, len)
--         end
--         lendiv = max(len - onelen, onelen)
--         if T <: Integer && !iszero(mod(stop-start, lendiv))
--             throw(ArgumentError("LinRange{<:Integer} cannot have non-integer step"))
--         end
--         return new(start, stop, len, lendiv)
--     end
-- /Source
def linRangeBoolLength (start stop : JInt64) (len : Bool) : JlX (LinRange JInt64 Bool) :=
  letI : JLe JInt64 Bool :=
    ⟨fun x y => JuliaLean.base.int.le x (JuliaLean.base.int.ofBool .i64 y)⟩
  letI : JPrint JInt64 := ⟨fun x => toString x.val⟩
  letI : JPrint Bool := ⟨fun b => if b then "true" else "false"⟩
  letI : JOneunit Bool := ⟨true⟩
  letI : JEq Bool Bool := ⟨fun x y => x == y⟩
  letI : JEq JInt64 JInt64 := ⟨JuliaLean.base.int.eq⟩
  letI : HSub Bool Bool JInt64 := ⟨JuliaLean.base.bool.subBool⟩
  letI : JMax JInt64 Bool JInt64 :=
    ⟨fun x y => pure (JuliaLean.base.int.jmax x (JuliaLean.base.int.ofBool .i64 y))⟩
  letI : JType JInt64 :=
    { isBool := false, isSigned := true, isInteger := true,
      isAbstractFloat := false, bool_eq := by intro h; cases h }
  letI : HSub JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.sub⟩
  letI : JMod JInt64 JInt64 JInt64 :=
    ⟨fun x y => liftJl (JuliaLean.base.int.mod_BitSigned JInt.fld x y)⟩
  letI : JIszero JInt64 := ⟨fun x => JuliaLean.base.int.eq x (jint 0)⟩
  letI : JConvert Bool JInt64 := ⟨boolOfBitInteger⟩
  linRangeNew start stop len

end JuliaLean.base.range.Models1Group7

namespace JuliaLean.base.range.Models1Group8

open JuliaLean

/-- Explicit iteration with the actual type of `i + oneunit(i)`.
The source accepts Bool states, whose increment has type Int64. All calls use the
unchanged pre-existing dispatch interfaces; no callee correctness is assumed.
Julia source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))
--     @inline
--     i += oneunit(i)
--     length(r) < i && return nothing
--     unsafe_getindex(r, i), i
-- end
-- /Source
def iterateStepRangeLenLinRange {R I J L T : Type}
    [JOneunit I] [HAdd I I J] [JLength R L] [JLt L J] [JUnsafeGetindex R J T]
    (r : R) (i : I) : JlX (Option (T × J)) := do
  let nextIndex : J := i + (JOneunit.oneunit : I)
  let len ← JLength.length r
  if JLt.lt len nextIndex then return none
  let value ← JUnsafeGetindex.unsafeGetindex r nextIndex
  return some (value, nextIndex)

/-- The generated default-argument iteration method. It evaluates `length(r)` to
obtain the default's type/value before entering the explicit method, which evaluates
length again. Direct reuse of the generalized body permits a different returned state
type, unlike the baseline fixed-state `JIterate2` interface.
Julia source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))
--     @inline
--     i += oneunit(i)
--     length(r) < i && return nothing
--     unsafe_getindex(r, i), i
-- end
-- /Source
def iterateStepRangeLenLinRangeDefault {R L J T : Type}
    [JLength R L] [JZero L] [JOneunit L] [HAdd L L J]
    [JLt L J] [JUnsafeGetindex R J T]
    (r : R) : JlX (Option (T × J)) := do
  let _len ← JLength.length r
  iterateStepRangeLenLinRange (J := J) r (JZero.zero : L)

/-- Concrete dispatch for every Int64-field StepRangeLen and Bool iteration state.
The Bool addition dependency is exactly `base/bool.jl:145`: Int(x) +% Int(y),
using the existing int.jl conversion and wrapping-add models. Length and unsafe
indexing reuse their existing range.jl models. This is a specialization, not an
extra Julia method or a claim about arbitrary numeric implementations.
Julia source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:928-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))
--     @inline
--     i += oneunit(i)
--     length(r) < i && return nothing
--     unsafe_getindex(r, i), i
-- end
-- /Source
def iterateInt64RangeWithBool
    (r : StepRangeLen JInt64 JInt64 JInt64 JInt64) (i : Bool) :
    JlX (Option (JInt64 × JInt64)) :=
  letI : JOneunit Bool := ⟨true⟩
  letI : HAdd Bool Bool JInt64 := ⟨fun x y =>
    JuliaLean.base.int.addWrap (JuliaLean.base.int.ofBool .i64 x)
      (JuliaLean.base.int.ofBool .i64 y)⟩
  letI : JLength (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 :=
    ⟨fun a => .ok (length_StepRangeLen a)⟩
  letI : JLt JInt64 JInt64 := ⟨JuliaLean.base.int.lt⟩
  letI : JUnsafeGetindex (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 JInt64 :=
    ⟨unsafe_getindex_StepRangeLen⟩
  iterateStepRangeLenLinRange (J := JInt64) r i

/-- Unrounded index displacement can have a different type from the stored offset.
In particular, Bool offsets subtract to Int64. Conversion to the offset type still
happens first, and conversion to the element type still happens last.
Julia source: base/range.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T
--     u = oftype(r.offset, i) - r.offset
--     convert(T, (r.ref + u*r.step))
-- end
-- /Source
def unsafeGetindexStepRangeLen {T R S L I D P E : Type}
    [JConvert L I] [HSub L L D] [HMul D S P] [HAdd R P E] [JConvert T E]
    (r : StepRangeLen T R S L) (i : I) : JlX T := do
  let converted ← oftype r.offset i
  let u : D := converted - r.offset
  JConvert.convert (T := T) (r.ref + u * r.step)

/-- High-precision internal indexing with a separately typed offset difference.
This retains the source's absence of the final conversion to the element type.
Julia source: base/range.jl:1105-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1105-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _getindex_hiprec(r::StepRangeLen, i::Integer)  # without rounding by T
--     u = oftype(r.offset, i) - r.offset
--     r.ref + u*r.step
-- end
-- /Source
def getindexHiprec {T R S L I D P V : Type}
    [JConvert L I] [HSub L L D] [HMul D S P] [HAdd R P V]
    (r : StepRangeLen T R S L) (i : I) : JlX V := do
  let converted ← oftype r.offset i
  let u : D := converted - r.offset
  return r.ref + u * r.step

/-- Internal ascending-endpoint helper. The two step calls in the sign test are
kept, including the one inside zero(step(r)). Unary plus and unary minus have
independent result types; a sum tag records the actual type selected by the branch.
Julia source: base/range.jl:1229-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1229-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function first_step_last_ascending(r::StepRange)
--     if step(r) < zero(step(r))
--         last(r), -step(r), first(r)
--     else
--         first(r), +step(r), last(r)
--     end
-- end
-- /Source
def firstStepLastAscending {T S N P : Type}
    [JStep (StepRange T S) S] [JZero S] [JLt S S]
    [JLast (StepRange T S) T] [JNeg S N]
    [JFirst (StepRange T S) T] [JPos S P]
    (r : StepRange T S) : JlX (T × (N ⊕ P) × T) := do
  let step ← JStep.step r
  let _zeroStep ← JStep.step r
  if JLt.lt step (JZero.zero : S) then
    let first ← JLast.last r
    let step ← JStep.step r
    let ascendingStep : N := JNeg.neg step
    let last ← JFirst.first r
    return (first, .inl ascendingStep, last)
  else
    let first ← JFirst.first r
    let step ← JStep.step r
    let ascendingStep : P := JPos.pos step
    let last ← JLast.last r
    return (first, .inr ascendingStep, last)

/-- Internal index-of-intersection helper with the original Int64 literal types.
The two index variables retain their branch-dependent runtime types through sums,
as prescribed by the baseline model convention. Final colon dispatch receives those
tags; there is no premature conversion of literal 0 or 1 to the length type.
Julia source: base/range.jl:1296-1313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1296-1313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _findin(r::AbstractRange{<:Integer}, span::AbstractUnitRange{<:Integer})
--     fspan = first(span)
--     lspan = last(span)
--     fr = first(r)
--     lr = last(r)
--     sr = step(r)
--     if sr > 0
--         ifirst = fr >= fspan ? 1 : cld(fspan-fr, sr)+1
--         ilast = lr <= lspan ? length(r) : length(r) - cld(lr-lspan, sr)
--     elseif sr < 0
--         ifirst = fr <= lspan ? 1 : cld(lspan-fr, sr)+1
--         ilast = lr >= fspan ? length(r) : length(r) - cld(lr-fspan, sr)
--     else
--         ifirst = fr >= fspan ? 1 : length(r)+1
--         ilast = fr <= lspan ? length(r) : 0
--     end
--     r isa AbstractUnitRange ? (ifirst:ilast) : (ifirst:1:ilast)
-- end
-- /Source
def findin {R Q E T S D1 D2 C1 C2 I1 I2 L I3 Out1 Out2 : Type}
    [JFirst Q T] [JLast Q T] [JFirst R E] [JLast R E] [JStep R S]
    [JLt JInt64 S] [JLt S JInt64] [JLe T E] [JLe E T]
    [HSub T E D1] [HSub E T D2] [JCld D1 S C1] [JCld D2 S C2]
    [HAdd C1 JInt64 I1] [JLength R L] [HSub L C2 I3] [HAdd L JInt64 I2]
    [JIsAbstractUnitRange R]
    [JColon2 (JInt64 ⊕ (I1 ⊕ I2)) (L ⊕ (I3 ⊕ JInt64)) Out1]
    [JColon3 (JInt64 ⊕ (I1 ⊕ I2)) JInt64 (L ⊕ (I3 ⊕ JInt64)) Out2]
    (r : R) (span : Q) : JlX (Out1 ⊕ Out2) := do
  let fspan ← JFirst.first span
  let lspan ← JLast.last span
  let fr ← JFirst.first r
  let lr ← JLast.last r
  let sr ← JStep.step r
  let indices : (JInt64 ⊕ (I1 ⊕ I2)) × (L ⊕ (I3 ⊕ JInt64)) ←
    if JLt.lt (jint 0) sr then do
      let firstIndex : JInt64 ⊕ (I1 ⊕ I2) ←
        if JLe.le fspan fr then pure (.inl (jint 1))
        else do
          let count ← JCld.cld (fspan - fr) sr
          pure (.inr (.inl (count + jint 1)))
      let lastIndex : L ⊕ (I3 ⊕ JInt64) ←
        if JLe.le lr lspan then pure (.inl (← JLength.length r))
        else do
          let len ← JLength.length r
          let count ← JCld.cld (lr - lspan) sr
          pure (.inr (.inl (len - count)))
      pure (firstIndex, lastIndex)
    else if JLt.lt sr (jint 0) then do
      let firstIndex : JInt64 ⊕ (I1 ⊕ I2) ←
        if JLe.le fr lspan then pure (.inl (jint 1))
        else do
          let count ← JCld.cld (lspan - fr) sr
          pure (.inr (.inl (count + jint 1)))
      let lastIndex : L ⊕ (I3 ⊕ JInt64) ←
        if JLe.le fspan lr then pure (.inl (← JLength.length r))
        else do
          let len ← JLength.length r
          let count ← JCld.cld (lr - fspan) sr
          pure (.inr (.inl (len - count)))
      pure (firstIndex, lastIndex)
    else do
      let firstIndex : JInt64 ⊕ (I1 ⊕ I2) ←
        if JLe.le fspan fr then pure (.inl (jint 1))
        else do
          let len ← JLength.length r
          pure (.inr (.inr (len + jint 1)))
      let lastIndex : L ⊕ (I3 ⊕ JInt64) ←
        if JLe.le fr lspan then pure (.inl (← JLength.length r))
        else pure (.inr (.inr (jint 0)))
      pure (firstIndex, lastIndex)
  if JIsAbstractUnitRange.isAbstractUnitRange R then
    return .inl (← JColon2.colon indices.1 indices.2)
  else
    return .inr (← JColon3.colon indices.1 (jint 1) indices.2)

/-- Source-ordered subset test at the existing dispatch boundary.
The left `first` call precedes the right `first` call, even though the comparison
is represented using the existing reversed-operand `JLe` interface.
Julia source: base/range.jl:1317-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1317-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer}) =
--     isempty(r) || (first(r) >= first(s) && last(r) <= last(s))
-- /Source
def issubsetAbstractUnitRange {R Q T U : Type}
    [JIsempty R] [JFirst R T] [JFirst Q U] [JLe U T]
    [JLast R T] [JLast Q U] [JLe T U]
    (r : R) (s : Q) : JlX Bool := do
  if ← JIsempty.isempty r then return true
  let firstR ← JFirst.first r
  let firstS ← JFirst.first s
  if !JLe.le firstS firstR then return false
  let lastR ← JLast.last r
  let lastS ← JLast.last s
  return JLe.le lastR lastS

/-- Concrete dispatch for mixed-width BitInteger UnitRanges, reusing first, last,
isempty, convert and comparison models. No supplied correctness law or callback
is used. Constructor validity is a property premise, not a run-time filter.
Julia source: base/range.jl:1317-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1317-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer}) =
--     isempty(r) || (first(r) >= first(s) && last(r) <= last(s))
-- /Source
def issubsetIntegerUnitRange {t u : IntTy}
    (r : UnitRange (JInt t)) (s : UnitRange (JInt u)) : JlX Bool :=
  letI : JEltype (UnitRange (JInt t)) (JInt t) := ⟨⟩
  letI : JEltype (UnitRange (JInt u)) (JInt u) := ⟨⟩
  letI : JFieldStart (UnitRange (JInt t)) (JInt t) := ⟨UnitRange.start⟩
  letI : JFieldStart (UnitRange (JInt u)) (JInt u) := ⟨UnitRange.start⟩
  letI : JFieldStop (UnitRange (JInt t)) (JInt t) := ⟨UnitRange.stop⟩
  letI : JFieldStop (UnitRange (JInt u)) (JInt u) := ⟨UnitRange.stop⟩
  letI : JFirst (UnitRange (JInt t)) (JInt t) := ⟨first_OrdinalRange⟩
  letI : JFirst (UnitRange (JInt u)) (JInt u) := ⟨first_OrdinalRange⟩
  letI : JLast (UnitRange (JInt t)) (JInt t) := ⟨last_OrdinalRange⟩
  letI : JLast (UnitRange (JInt u)) (JInt u) := ⟨last_OrdinalRange⟩
  letI : JLt (JInt t) (JInt t) := ⟨JuliaLean.base.int.lt⟩
  letI : JIsempty (UnitRange (JInt t)) := ⟨isempty_AbstractUnitRange⟩
  issubsetAbstractUnitRange r s

/-- Internal reverse preserves the distinct types of the empty offset, the
length-minus-offset difference, and the addition of the Int literal 1. Both branches
then call the existing same-type constructor boundary with the actual offset type.
Julia source: base/range.jl:1446-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1446-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _reverse(r::StepRangeLen, ::Colon)
--     # If `r` is empty, `length(r) - r.offset + 1 will be nonpositive hence
--     # invalid. As `reverse(r)` is also empty, any offset would work so we keep
--     # `r.offset`
--     offset = isempty(r) ? r.offset : length(r)-r.offset+1
--     return typeof(r)(r.ref, negate(r.step), length(r), offset)
-- end
-- /Source
def reverseStepRangeLen {T R S L N D O S' : Type}
    [JIsempty (StepRangeLen T R S L)] [JLength (StepRangeLen T R S L) N]
    [HSub N L D] [HAdd D JInt64 O] [JNegate S S']
    [JSameType4 (StepRangeLen T R S L) R S' N L]
    [JSameType4 (StepRangeLen T R S L) R S' N O]
    (r : StepRangeLen T R S L) (_c : Colon) : JlX (StepRangeLen T R S L) := do
  let offset : L ⊕ O ← if ← JIsempty.isempty r then
      pure (.inl r.offset)
    else do
      let len ← JLength.length r
      pure (.inr ((len - r.offset) + jint 1))
  let step ← JNegate.negate r.step
  let len ← JLength.length r
  match offset with
  | .inl value => JSameType4.make r.ref step len value
  | .inr value => JSameType4.make r.ref step len value

/-- The arithmetic-series implementation with independent types for length minus
Int(1), both shifts, both products, and both branch results. The sum tags only
represent the actual runtime result type; they introduce no numerical conversion.
Julia source: base/range.jl:1468-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1468-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sum(r::AbstractRange{<:Real})
--     l = length(r)
--     # note that a little care is required to avoid overflow in l*(l-1)/2
--     return l * first(r) + (iseven(l) ? (step(r) * (l-1)) * (l>>1)
--                                      : (step(r) * l) * ((l-1)>>1))
-- end
-- /Source
def sumAbstractRange {R L T S P D H1 H2 A1 A2 B1 B2 C1 C2 : Type}
    [JLength R L] [JFirst R T] [HMul L T P] [JIseven L] [JStep R S]
    [HSub L JInt64 D] [HMul S D A1] [JShr L JInt64 H1] [HMul A1 H1 B1]
    [HMul S L A2] [JShr D JInt64 H2] [HMul A2 H2 B2]
    [HAdd P B1 C1] [HAdd P B2 C2]
    (r : R) : JlX (C1 ⊕ C2) := do
  let len ← JLength.length r
  let first ← JFirst.first r
  let p : P := len * first
  if JIseven.iseven len then
    let step ← JStep.step r
    let q : B1 := (step * (len - jint 1)) * JShr.shr len (jint 1)
    return .inl (p + q)
  else
    let step ← JStep.step r
    let q : B2 := (step * len) * JShr.shr (len - jint 1) (jint 1)
    return .inr (p + q)

/-- Local fixed-divisor binding of the existing Core checked remainder primitive.
The nonzero-divisor proof only removes an impossible error constructor; no error is
replaced by a value and no public contract is proved. This is needed to instantiate
the pre-existing pure iseven dispatch boundary. Julia source: base/int.jl:356 and
base/int.jl:181; Core.lean documents remInt as the checked signed remainder primitive. -/
-- Source: base/int.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::T, y::T) where {T<:BitSigned64} = checked_srem_int(x, y)
-- /Source

def remainderTwoInt64 (n : JInt64) : JInt64 :=
  JuliaLean.base.int.okOf (JInt.remInt n (jint 2)) (by
    intro e h
    have htwo : (jint 2).val ≠ 0 := by decide
    simp [JInt.remInt, htwo] at h)

/-- Concrete binding of the existing iseven_Real body. For Int64,
isinteger is true (base/number.jl:22), Integer is identity (base/boot.jl:1220),
the body supplies the literal divisor 2, and iszero compares with zero
(base/number.jl:44). Julia source: base/int.jl:181. -/
-- Source: base/int.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))
-- /Source

def isevenInt64 (n : JInt64) : Bool :=
  JuliaLean.base.int.iseven_Real (fun (_ : JInt64) => true) id
    (fun value (_two : JInt64) => remainderTwoInt64 value)
    (fun value => JuliaLean.base.int.eq value (JuliaLean.base.int.zero value)) n

/-- Concrete arithmetic-series dispatch for all Int64-field StepRangeLens.
First, step, length, shift and wrapping arithmetic reuse existing models. The
iseven dependency reuses the existing iseven_Real body and Core checked remainder
primitive, matching the Integer parity rule. The return sum is erased after
dispatch because both runtime branches have the same Int64 result type.
Julia source: base/range.jl:1468-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1468-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sum(r::AbstractRange{<:Real})
--     l = length(r)
--     # note that a little care is required to avoid overflow in l*(l-1)/2
--     return l * first(r) + (iseven(l) ? (step(r) * (l-1)) * (l>>1)
--                                      : (step(r) * l) * ((l-1)>>1))
-- end
-- /Source
def sumInt64StepRangeLen (r : StepRangeLen JInt64 JInt64 JInt64 JInt64) : JlX JInt64 :=
  letI : JLength (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 :=
    ⟨fun a => .ok (length_StepRangeLen a)⟩
  letI : JUnsafeGetindex (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 JInt64 :=
    ⟨unsafe_getindex_StepRangeLen⟩
  letI : JFirst (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 :=
    ⟨first_StepRangeLen⟩
  letI : JStep (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 :=
    ⟨fun a => .ok (step_StepRangeLen a)⟩
  letI : JIseven JInt64 := ⟨isevenInt64⟩
  letI : JShr JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.shr_Int⟩
  (sumAbstractRange r).map (fun result =>
    match result with
    | .inl value => value
    | .inr value => value)

/-- Generated + and - methods on two LinRanges whose length types need not agree.
The full surrounding @eval generator and its two invocations are quoted below.
This represents the generated method body; the existing method-installation
runtime remains separate and is not assumed correct.
Julia source: base/range.jl:1502-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
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
def rangeopLinRange (F : Type) {T L1 L2 A Out : Type}
    [JEq L1 L2] [JPrint L1] [JPrint L2]
    [JFirst (LinRange T L1) T] [JFirst (LinRange T L2) T]
    [JLast (LinRange T L1) T] [JLast (LinRange T L2) T]
    [JScalarOp F T T A] [JConvert T A] [JLinRangeT T T T L1 Out]
    (r1 : LinRange T L1) (r2 : LinRange T L2) : JlX Out := do
  let len := r1.len
  unless JEq.eq len r2.len do
    throw (.dimensionMismatch ("argument dimensions must match: length of r1 is " ++
      JPrint.print len ++ ", length of r2 is " ++ JPrint.print r2.len))
  let first1 ← JFirst.first r1
  let first2 ← JFirst.first r2
  let start ← JConvert.convert (T := T) (JScalarOp.scalarOp F first1 first2)
  let last1 ← JLast.last r1
  let last2 ← JLast.last r2
  let stop ← JConvert.convert (T := T) (JScalarOp.scalarOp F last1 last2)
  JLinRangeT.linRangeT (T := T) start stop len

/-- Addition shares only T and the stored reference type R, as in Julia's
StepRangeLen{T,R} signature. Stored step types, length types, observed step types,
and observed length types remain independent. Repeated right-length evaluation
in the error message is preserved.
Julia source: base/range.jl:1527-1532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:1527-1532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function +(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S}) where {T,S}
--     len = length(r1)
--     (len == length(r2) ||
--      throw(DimensionMismatch("argument dimensions must match: length of r1 is $len, length of r2 is $(length(r2))")))
--     StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), len)
-- end
-- /Source
def plusStepRangeLen {T R S1 L1 S2 L2 N1 N2 U1 U2 A B Out : Type}
    [JLength (StepRangeLen T R S1 L1) N1]
    [JLength (StepRangeLen T R S2 L2) N2]
    [JEq N1 N2] [JPrint N1] [JPrint N2]
    [JFirst (StepRangeLen T R S1 L1) T]
    [JFirst (StepRangeLen T R S2 L2) T] [HAdd T T A]
    [JStep (StepRangeLen T R S1 L1) U1]
    [JStep (StepRangeLen T R S2 L2) U2] [HAdd U1 U2 B]
    [JStepRangeLen3 A B N1 Out]
    (r1 : StepRangeLen T R S1 L1) (r2 : StepRangeLen T R S2 L2) : JlX Out := do
  let len ← JLength.length r1
  let len2 ← JLength.length r2
  unless JEq.eq len len2 do
    let repeatedLen2 ← JLength.length r2
    throw (.dimensionMismatch ("argument dimensions must match: length of r1 is " ++
      JPrint.print len ++ ", length of r2 is " ++ JPrint.print repeatedLen2))
  let first1 ← JFirst.first r1
  let first2 ← JFirst.first r2
  let a : A := first1 + first2
  let step1 ← JStep.step r1
  let step2 ← JStep.step r2
  let b : B := step1 + step2
  JStepRangeLen3.stepRangeLen a b len

end JuliaLean.base.range.Models1Group8


namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-!
Additive, effect-aware models for models batch 2, group 20. The original
declarations above remain untouched. A dispatch result carrier may be a tagged
union of Julia values; it need not denote one concrete Julia runtime type.
`Monad` parameters can carry errors, mutations, and divergence of selected callees.
-/

/-- A term denoting the Julia type parameter `T`, without fixing its renderer.
Used for the literal `T` arguments at base/range.jl:636,638. -/
-- Source: base/range.jl:634-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LinRange{T}) where {T}
--     print(io, "LinRange{")
--     show(io, T)
--     print(io, "}(")
--     ioc = IOContext(io, :typeinfo=>T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
structure TypeToken (T : Type) where

/-- The literal context keys used by the queued display methods.  Source use: base/range.jl:634-645. -/
-- Source: base/range.jl:634-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LinRange{T}) where {T}
--     print(io, "LinRange{")
--     show(io, T)
--     print(io, "}(")
--     ioc = IOContext(io, :typeinfo=>T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
inductive ContextKey where
  | typeinfo
  | compact
  deriving DecidableEq, Repr

/-- Open dispatch in `show(io::IO, r::LinRange{T})`, base/range.jl:634-645.
The IO subtype is not fixed by this method. Context creation and all stream
operations therefore retain their selected, effectful dispatch targets.
`T`, endpoint and length renderers, and every ignored/final result are separate.
No renderer or context-constructor correctness law is imposed. -/
-- Source: base/range.jl:634-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LinRange{T}) where {T}
--     print(io, "LinRange{")
--     show(io, T)
--     print(io, "}(")
--     ioc = IOContext(io, :typeinfo=>T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
structure LinShowOps (m : Type → Type)
    (Stream Context T L PrintResult TypeResult ValueResult LengthResult Result : Type) where
  printString : Stream → String → m PrintResult
  showType : Stream → TypeToken T → m TypeResult
  context : Stream → ContextKey → TypeToken T → m Context
  showValue : Context → T → m ValueResult
  showLength : Stream → L → m LengthResult
  printChar : Stream → Char → m Result

/-- Incremental `LinRange` display, base/range.jl:634-645. Known LinRange
accessors call their installed bodies; no callback replaces them. The final
print result is returned unchanged, including a custom printer's return value.
Earlier writes are never reassembled into a final string. -/
-- Source: base/range.jl:634-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LinRange{T}) where {T}
--     print(io, "LinRange{")
--     show(io, T)
--     print(io, "}(")
--     ioc = IOContext(io, :typeinfo=>T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
def showLinRange {m : Type → Type} [Monad m]
    {Stream Context T L PrintResult TypeResult ValueResult LengthResult Result : Type}
    (ops : LinShowOps m Stream Context T L PrintResult TypeResult ValueResult LengthResult Result)
    (io : Stream) (r : LinRange T L) : m Result := do
  let _ ← ops.printString io "LinRange{"
  let _ ← ops.showType io ⟨⟩
  let _ ← ops.printString io "}("
  let ioc ← ops.context io .typeinfo ⟨⟩
  let _ ← ops.showValue ioc (first_LinRange r)
  let _ ← ops.printString io ", "
  let _ ← ops.showValue ioc (last_LinRange r)
  let _ ← ops.printString io ", "
  let _ ← ops.showLength io (length_LinRange r)
  ops.printChar io ')'

/-- An argument is a native Julia Int literal or the result of open dispatch.
`dynamic` can contain a tagged Julia value of any runtime type.  Source use: base/range.jl:660-701. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
inductive CallArg (V : Type) where
  | native (value : JInt64)
  | dynamic (value : V)

/-- The implicit Boolean-condition check distinguishes actual Bool values.  Source use: base/range.jl:660-701. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
inductive Condition (Other : Type) where
  | bool (value : Bool)
  | other (value : Other)

/-- Caller-introduced errors: TypeError at a non-Bool condition, or the exact
Base error from the concrete native range constructor. Callees may additionally
throw arbitrary errors through the effect monad.  Source use: base/range.jl:660-701. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
inductive PrintRangeError (Other : Type) where
  | typeError (value : Other)
  | base (error : Exc)

/-- Identity of the Julia `sum` generic function, passed to open `map` dispatch.  Source use: base/range.jl:660-701. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
structure SumFunction where

/-- Selected calls in base/range.jl:660-701. AbstractArray, AbstractString and
IO subtypes and their result types are not fixed by this caller. Dynamic
carriers include changing runtime types without a callee-correctness law.
Literal `1:m` is absent from this interface: the body calls installed native
colon. `mapSum` receives the actual `sum` function token; outer sum is separate. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
structure PrintRangeOps (m : Type → Type)
    (Stream R Str Size V Cols Cat Slice Matrix Axis Index Align Mapped HasKey Bad Result RowResult : Type) where
  displaysize : Stream → m Size
  haskey : Stream → ContextKey → m HasKey
  not : HasKey → m (Condition Bad)
  context : Stream → ContextKey → Bool → m Stream
  sizeGetindex : Size → JInt64 → m V
  lengthString : Str → m V
  lengthRange : R → m V
  add : CallArg V → CallArg V → m V
  sub : CallArg V → CallArg V → m V
  mul : CallArg V → CallArg V → m V
  div : CallArg V → CallArg V → m V
  le : V → V → m (Condition Bad)
  colon2 : CallArg V → CallArg V → m Cols
  colon3 : CallArg V → JInt64 → JInt64 → m Cols
  vcat : Cols → Cols → m Cat
  getindex : R → Sum Cols Cat → m Slice
  lengthSelection : Sum Cols Cat → m V
  reshape : Slice → JInt64 → V → m Matrix
  size : Matrix → JInt64 → m V
  axes : Matrix → JInt64 → m Axis
  lastAxis : Axis → m Index
  lengthMatrix : Matrix → m V
  alignment : Stream → Matrix → UnitRange JInt64 → Cols → V → V → V → V → m Align
  lengthAlignment : Align → m V
  reverse : Align → m Align
  mapSum : SumFunction → Align → m Mapped
  sum : Mapped → m V
  print : Stream → Str → m Result
  printMatrixRow : Stream → Matrix → Align → JInt64 → Cols → Str → Index → m RowResult

/-- `print_range`, base/range.jl:660-701. Preserves every repeated evaluation,
the unused `sz[1]-4`, nonstandard axes, one dispatched vector-index operation,
and every incremental print. Known native `1:m` uses `colon_T_T_Real`.
Optional arguments are explicit, as in the installed model convention. -/
-- Source: base/range.jl:660-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
-- /Source
def printRange {m : Type → Type} [Monad m]
    {Stream R Str Size V Cols Cat Slice Matrix Axis Index Align Mapped HasKey Bad Result RowResult : Type}
    [MonadExceptOf (PrintRangeError Bad) m]
    (ops : PrintRangeOps m Stream R Str Size V Cols Cat Slice Matrix Axis Index Align Mapped HasKey Bad Result RowResult)
    (io : Stream) (r : R) (pre sep post hdots : Str) : m Result := do
  let test (c : Condition Bad) : m Bool :=
    match c with
    | .bool value => pure value
    | .other value => throw (PrintRangeError.typeError value)
  let sz ← ops.displaysize io
  let hasCompact ← ops.haskey io .compact
  let addCompact ← test (← ops.not hasCompact)
  let io ← if addCompact then ops.context io .compact true else pure io
  let height ← ops.sizeGetindex sz (jint 1)
  let _ ← ops.sub (.dynamic height) (.native (jint 4))
  let screenwidth ← ops.sizeGetindex sz (jint 2)
  let preLength ← ops.lengthString pre
  let postLength ← ops.lengthString post
  let margins ← ops.add (.dynamic preLength) (.dynamic postLength)
  let screenwidth ← ops.sub (.dynamic screenwidth) (.dynamic margins)
  let sepsize ← ops.lengthString sep
  let rowCount := jint 1
  let n ← ops.lengthRange r
  let minimumColumn ← ops.add (.native (jint 1)) (.dynamic sepsize)
  let maxpossiblecols ← ops.div (.dynamic screenwidth) (.dynamic minimumColumn)
  let fitsEstimate ← test (← ops.le n maxpossiblecols)
  let colsr : Sum Cols Cat ← if fitsEstimate then do
      pure (.inl (← ops.colon2 (.native (jint 1)) (.dynamic n)))
    else do
      let half ← ops.div (.dynamic maxpossiblecols) (.native (jint 2))
      let leftEnd ← ops.add (.dynamic half) (.native (jint 1))
      let left ← ops.colon2 (.native (jint 1)) (.dynamic leftEnd)
      let half ← ops.div (.dynamic maxpossiblecols) (.native (jint 2))
      let rightStart ← ops.sub (.dynamic n) (.dynamic half)
      let right ← ops.colon2 (.dynamic rightStart) (.dynamic n)
      pure (.inr (← ops.vcat left right))
  let slice ← ops.getindex r colsr
  let selectedLength ← ops.lengthSelection colsr
  let rowmatrix ← ops.reshape slice (jint 1) selectedLength
  let nrow ← ops.size rowmatrix (jint 2)
  let rowAxis ← ops.axes rowmatrix (jint 2)
  let idxlast ← ops.lastAxis rowAxis
  let nativeRows : m (UnitRange JInt64) :=
    match colon_T_T_Real (jint 1) rowCount with
    | .ok rows => pure rows
    | .error error => throw (PrintRangeError.base error)
  let rows ← nativeRows
  let matrixLength ← ops.lengthMatrix rowmatrix
  let columns ← ops.colon2 (.native (jint 1)) (.dynamic matrixLength)
  let a ← ops.alignment io rowmatrix rows columns screenwidth screenwidth sepsize nrow
  let aLength ← ops.lengthAlignment a
  let fits ← test (← ops.le n aLength)
  if fits then
    let _ ← ops.print io pre
    let columns ← ops.colon2 (.native (jint 1)) (.dynamic n)
    let _ ← ops.printMatrixRow io rowmatrix a (jint 1) columns sep idxlast
    ops.print io post
  else
    let dotsLength ← ops.lengthString hdots
    let c ← ops.sub (.dynamic screenwidth) (.dynamic dotsLength)
    let c ← ops.add (.dynamic c) (.native (jint 1))
    let c ← ops.div (.dynamic c) (.native (jint 2))
    let c ← ops.add (.dynamic c) (.native (jint 1))
    let rows ← nativeRows
    let matrixLength ← ops.lengthMatrix rowmatrix
    let columns ← ops.colon3 (.dynamic matrixLength) (jint (-1)) (jint 1)
    let rightAlignment ← ops.alignment io rowmatrix rows columns c c sepsize nrow
    let alignR ← ops.reverse rightAlignment
    let totals ← ops.mapSum ⟨⟩ alignR
    let total ← ops.sum totals
    let c ← ops.sub (.dynamic screenwidth) (.dynamic total)
    let rightLength ← ops.lengthAlignment alignR
    let separators ← ops.sub (.dynamic rightLength) (.native (jint 1))
    let separators ← ops.mul (.dynamic separators) (.dynamic sepsize)
    let c ← ops.sub (.dynamic c) (.dynamic separators)
    let dotsLength ← ops.lengthString hdots
    let c ← ops.sub (.dynamic c) (.dynamic dotsLength)
    let rows ← nativeRows
    let matrixLength ← ops.lengthMatrix rowmatrix
    let columns ← ops.colon2 (.native (jint 1)) (.dynamic matrixLength)
    let alignL ← ops.alignment io rowmatrix rows columns c c sepsize nrow
    let _ ← ops.print io pre
    let leftLength ← ops.lengthAlignment alignL
    let columns ← ops.colon2 (.native (jint 1)) (.dynamic leftLength)
    let _ ← ops.printMatrixRow io rowmatrix alignL (jint 1) columns sep idxlast
    let _ ← ops.print io hdots
    let matrixLength ← ops.lengthMatrix rowmatrix
    let rightLength ← ops.lengthAlignment alignR
    let rightStart ← ops.sub (.dynamic matrixLength) (.dynamic rightLength)
    let rightStart ← ops.add (.dynamic rightStart) (.native (jint 1))
    let matrixLength ← ops.lengthMatrix rowmatrix
    let columns ← ops.colon2 (.dynamic rightStart) (.dynamic matrixLength)
    let _ ← ops.printMatrixRow io rowmatrix alignR (jint 1) columns sep idxlast
    ops.print io post

end JuliaLean.base.range.Models2Group20

namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-- Selected scalar calls for `isempty(::StepRange)`, base/range.jl:708-710.
The element/step types are not fixed. Neither comparison nor `!=` nor `&`
is forced to return Bool; `zero(step)` may have a distinct result type.
Each operation retains its own errors and mutations through `m`. -/
-- Source: base/range.jl:708-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::StepRange) =
--     # steprange_last(r.start, r.step, r.stop) == r.stop
--     (r.start != r.stop) & ((r.step > zero(r.step)) != (r.stop > r.start))
-- /Source
structure StepEmptyOps (m : Type → Type) (T S Z E G H D Result : Type) where
  neEndpoints : T → T → m E
  zeroStep : S → m Z
  gtStep : S → Z → m G
  gtEndpoints : T → T → m H
  neDirections : G → H → m D
  and : E → D → m Result

/-- Eager emptiness test, base/range.jl:708-710. All operands are evaluated
left to right before the selected `&`; no implicit Bool check or short circuit
is inserted. The final dispatched result is returned unchanged. -/
-- Source: base/range.jl:708-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::StepRange) =
--     # steprange_last(r.start, r.step, r.stop) == r.stop
--     (r.start != r.stop) & ((r.step > zero(r.step)) != (r.stop > r.start))
-- /Source
def isemptyStepRange {m : Type → Type} [Monad m]
    {T S Z E G H D Result : Type}
    (ops : StepEmptyOps m T S Z E G H D Result) (r : StepRange T S) : m Result := do
  let unequal ← ops.neEndpoints r.start r.stop
  let zero ← ops.zeroStep r.step
  let positive ← ops.gtStep r.step zero
  let increasing ← ops.gtEndpoints r.stop r.start
  let directions ← ops.neDirections positive increasing
  ops.and unequal directions

/-- Open subtraction and division for `step(::LinRange)`, base/range.jl:740.
Both arithmetic operations can throw or mutate state, and their result types
need not equal either endpoint or length type. -/
-- Source: base/range.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::LinRange) = (last(r)-first(r))/r.lendiv
-- /Source
structure LinStepOps (m : Type → Type) (T L Difference Result : Type) where
  sub : T → T → m Difference
  div : Difference → L → m Result

/-- `LinRange` spacing, base/range.jl:740. The concrete range's installed
first/last accessors are used. Subtraction occurs before division, permitting
checked Rational arithmetic and other dispatched failures at their source point.
The denominator is the stored `lendiv`, not the stored count. -/
-- Source: base/range.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::LinRange) = (last(r)-first(r))/r.lendiv
-- /Source
def stepLinRange {m : Type → Type} [Monad m]
    {T L Difference Result : Type}
    (ops : LinStepOps m T L Difference Result) (r : LinRange T L) : m Result := do
  let stop := last_LinRange r
  let start := first_LinRange r
  let difference ← ops.sub stop start
  ops.div difference r.lendiv

/-- Open calls in `length(::AbstractUnitRange)`, base/range.jl:794-804.
`Sum Signed Other` carries the runtime `isa Signed` classification of the
value returned by `oneunit`; this is type metadata, not a supplied comparison
or correctness law. Each operation has its own result carrier, including the
first/last results and the two branches' changed accumulator types. -/
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
structure UnitLengthOps (m : Type → Type)
    (R First Last ZeroLast ZeroFirst ZeroDiff Signed Other Diff Updated Empty Result Bad : Type) where
  first : R → m First
  last : R → m Last
  zeroLast : Last → m ZeroLast
  zeroFirst : First → m ZeroFirst
  subZeros : ZeroLast → ZeroFirst → m ZeroDiff
  oneunit : ZeroDiff → m (Sum Signed Other)
  ge : Last → First → m (Condition Bad)
  subEndpoints : Last → First → m Diff
  add : Sum Signed Other → Diff → m Updated
  zeroOther : Other → m Empty
  integerUpdated : Updated → m Result
  integerEmpty : Empty → m Result

/-- Generic unit-range length, base/range.jl:794-804. Derive the unit from
value-sensitive endpoint zeros before testing its runtime Signed classification.
Signed units bypass endpoint comparison; a non-Bool comparison raises TypeError
at the condition. Both branch arithmetic and Integer conversion remain effectful.
No native specialization or arithmetic correctness premise restricts the domain. -/
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
def lengthAbstractUnitRange {m : Type → Type} [Monad m]
    {R First Last ZeroLast ZeroFirst ZeroDiff Signed Other Diff Updated Empty Result Bad : Type}
    [MonadExceptOf (PrintRangeError Bad) m]
    (ops : UnitLengthOps m R First Last ZeroLast ZeroFirst ZeroDiff Signed Other Diff Updated Empty Result Bad)
    (r : R) : m Result := do
  let start ← ops.first r
  let stop ← ops.last r
  let zeroStop ← ops.zeroLast stop
  let zeroStart ← ops.zeroFirst start
  let zeroDifference ← ops.subZeros zeroStop zeroStart
  let a ← ops.oneunit zeroDifference
  match a with
  | .inl signed =>
      let difference ← ops.subEndpoints stop start
      let updated ← ops.add (.inl signed) difference
      ops.integerUpdated updated
  | .inr other =>
      let condition ← ops.ge stop start
      match condition with
      | .other bad => throw (.typeError bad)
      | .bool true =>
          let difference ← ops.subEndpoints stop start
          let updated ← ops.add (.inr other) difference
          ops.integerUpdated updated
      | .bool false =>
          let empty ← ops.zeroOther other
          ops.integerEmpty empty

end JuliaLean.base.range.Models2Group20


namespace JuliaLean.base.range.Models2Group20

/-- Open, effectful dispatch used by `show(::IO, ::AbstractRange)`,
base/range.jl:1135. First, step, last and all three repr results have independent
carriers, which may contain tagged values with changing Julia runtime types.
The variadic print is one call with its exact five value arguments. -/
-- Source: base/range.jl:1135-1135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, r::AbstractRange) = print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
-- /Source
structure AbstractShowOps (m : Type → Type)
    (Stream R First Step Last FirstText StepText LastText Result : Type) where
  first : R → m First
  reprFirst : First → m FirstText
  step : R → m Step
  reprStep : Step → m StepText
  last : R → m Last
  reprLast : Last → m LastText
  print5 : Stream → FirstText → Char → StepText → Char → LastText → m Result

/-- Generic range display, base/range.jl:1135. Repr arguments are evaluated
left to right before the single variadic stream call. Its return is retained;
the monad also retains exceptions and all earlier mutations. -/
-- Source: base/range.jl:1135-1135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, r::AbstractRange) = print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
-- /Source
def showAbstractRange {m : Type → Type} [Monad m]
    {Stream R First Step Last FirstText StepText LastText Result : Type}
    (ops : AbstractShowOps m Stream R First Step Last FirstText StepText LastText Result)
    (io : Stream) (r : R) : m Result := do
  let first ← ops.first r
  let firstText ← ops.reprFirst first
  let step ← ops.step r
  let stepText ← ops.reprStep step
  let last ← ops.last r
  let lastText ← ops.reprLast last
  ops.print5 io firstText ':' stepText ':' lastText

/-- Effectful open conversion and output targets of UnitRange display,
base/range.jl:1136-1140. `Converted` and `Result` can be tagged dynamic carriers;
conversion is not silently assumed to return a value of its requested type.
The concrete first/last source bodies are implemented below. -/
-- Source: base/range.jl:1136-1140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::UnitRange)
--     show(io, first(r))
--     print(io, ':')
--     show(io, last(r))
-- end
-- /Source
structure UnitShowOps (m : Type → Type) (Stream T Converted ColonResult Result : Type) where
  convert : TypeToken T → T → m Converted
  showValue : Stream → Converted → m Result
  printChar : Stream → Char → m ColonResult

/-- The UnitRange specialization of the concrete ordinal accessor,
base/range.jl:867. It selects the stored start itself and calls the selected
`convert(T, value)` at that point. The installed accessor uses fixed `JlX`;
this additive helper preserves arbitrary conversion state and exceptions. -/
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source
def unitRangeFirstEffectful {m : Type → Type} {T Converted : Type}
    (convert : TypeToken T → T → m Converted) (r : UnitRange T) : m Converted :=
  convert ⟨⟩ r.start

/-- The UnitRange specialization of the concrete ordinal accessor,
base/range.jl:877. Stored stop selection and effectful conversion are explicit;
no arbitrary callback replaces `last(::UnitRange)` itself. -/
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
def unitRangeLastEffectful {m : Type → Type} {T Converted : Type}
    (convert : TypeToken T → T → m Converted) (r : UnitRange T) : m Converted :=
  convert ⟨⟩ r.stop

/-- Incremental UnitRange display, base/range.jl:1136-1140. The last endpoint
is converted only after the first show and colon print have succeeded. The
final show result is returned unchanged; a later failure retains prior writes. -/
-- Source: base/range.jl:1136-1140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::UnitRange)
--     show(io, first(r))
--     print(io, ':')
--     show(io, last(r))
-- end
-- /Source
def showUnitRange {m : Type → Type} [Monad m]
    {Stream T Converted ColonResult Result : Type}
    (ops : UnitShowOps m Stream T Converted ColonResult Result)
    (io : Stream) (r : UnitRange T) : m Result := do
  let first ← unitRangeFirstEffectful ops.convert r
  let _ ← ops.showValue io first
  let _ ← ops.printChar io ':'
  let last ← unitRangeLastEffectful ops.convert r
  ops.showValue io last

/-- One variadic print dispatch for `show(::IO, ::OneTo)`, base/range.jl:1141.
The arbitrary IO subtype selects the stream method; the stored stop is passed
as its actual value, without conversion or pre-rendering. -/
-- Source: base/range.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, r::OneTo) = print(io, "Base.OneTo(", r.stop, ")")
-- /Source
structure OneToShowOps (m : Type → Type) (Stream T Result : Type) where
  print3 : Stream → String → T → String → m Result

/-- OneTo display, base/range.jl:1141: exactly one variadic print invocation
receives the original stream and stored stop, returning its result unchanged. -/
-- Source: base/range.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, r::OneTo) = print(io, "Base.OneTo(", r.stop, ")")
-- /Source
def showOneTo {m : Type → Type} {Stream T Result : Type}
    (ops : OneToShowOps m Stream T Result) (io : Stream) (r : OneTo T) : m Result :=
  ops.print3 io "Base.OneTo(" r.stop ")"

end JuliaLean.base.range.Models2Group20

namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-!
Effectful `show(::StepRangeLen)` with explicit closed accessor dispatch.
The argument constructors record the selected built-in representation cases,
as `OffsetArgument` does in the installed abstract-array example. A pair in the
TwicePrecision cases is the stored `(hi, lo)` field view, not a Julia Tuple
substituted for the numeric value. Reference and step scalar types are independent.
-/

/-- Runtime representation/dispatch cases needed by base/range.jl:1142.
`ordinaryStored` is the non-AbstractFloat fallback with at least one field type
not TwicePrecision; `ordinaryConverted` is its AbstractFloat counterpart.
`twiceStored` has two TwicePrecision field types, non-AbstractFloat T, and is
outside the exact matching T/T/T step specialization. `twiceConverted` covers
AbstractFloat T or matching TwicePrecision{T} reference and step, including
non-floating T. These tags describe actual type selection, not a caller-supplied
implementation or a law about arithmetic. The four original fields remain stored;
all constructible length/offset values are included. -/
-- Source: base/range.jl:738-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::StepRangeLen) = r.step
-- step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
-- /Source
inductive StepLenArgument (T R S L F G : Type) where
  | ordinaryStored (range : StepRangeLen T R S L)
  | ordinaryConverted (range : StepRangeLen T R S L)
  | twiceStored (range : StepRangeLen T (F × F) (G × G) L)
  | twiceConverted (range : StepRangeLen T (F × F) (G × G) L)

/-- Arguments to scalar dispatch preserve their original runtime categories.
The dynamic carrier may contain values of changing Julia types. `twiceStep`
retains the actual immutable TwicePrecision step through its two stored fields;
its tag is distinct from a Julia tuple. No arithmetic result is fixed to L, F,
G, or the represented element type T.  Source use: base/twiceprecision.jl:196-199. -/
-- Source: base/twiceprecision.jl:196-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct TwicePrecision{T}
--     hi::T    # most significant bits
--     lo::T    # least significant bits
-- end
-- /Source
inductive StepLenScalar (R S L F G V : Type) where
  | reference (value : R)
  | step (value : S)
  | length (value : L)
  | referencePart (value : F)
  | stepPart (value : G)
  | twiceStep (parts : G × G)
  | dynamic (value : V)

/-- The observable field view of any object returned by open indexed_iterate.
A Module is distinguished because integer Core.getfield on it raises TypeError.
Every other object exposes its actual UInt32 field count and first two stored
slots; none in an existing slot is #undef, whereas a missing numbered field is
out of bounds. All remaining fields are unobserved. This is concrete runtime
metadata, not an arbitrary getfield function. It extends the installed
BootCov.getfieldObj slot model without an unbounded tuple/list assumption.
Source use: base/twiceprecision.jl:484; Core documentation:
base/docs/basedocs.jl:2609-2620. Default-order reads of these fields have no
user dispatch; the view is taken after each indexed_iterate returns. -/
-- Source: base/twiceprecision.jl:484-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     x_hi, x_lo = add12(r.ref.hi, shift_hi)
-- /Source
inductive StepLenIndexedObject (V : Type) where
  | moduleValue
  | fields (count : JInt .u32) (first second : Option V)

/-- Only the first and second primitive field positions occur in the lowering
of this two-target assignment at base/twiceprecision.jl:484. -/
-- Source: base/twiceprecision.jl:484-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     x_hi, x_lo = add12(r.ref.hi, shift_hi)
-- /Source
inductive StepLenProjection where
  | first
  | second
  deriving DecidableEq, Repr

/-- Errors introduced by this caller and its concrete destructuring helper.
Other exceptions remain in the selected effect monad. Both non-Bool conditions
and integer getfield on Modules are TypeError; undefined existing fields are
UndefRefError and nonexistent fields are the installed BoundsError class.  Source use: base/range.jl:1142-1149. -/
-- Source: base/range.jl:1142-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::StepRangeLen)
--     if !iszero(step(r))
--         print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
--     else
--         # ugly temporary printing, to avoid 0:0:0 etc.
--         print(io, "StepRangeLen(", repr(first(r)), ", ", repr(step(r)), ", ", repr(length(r)), ")")
--     end
-- end
-- /Source
inductive StepLenError (Bad : Type) where
  | conditionTypeError (value : Bad)
  | getfieldTypeError
  | undefRefError
  | jl (error : JlError)

/-- Primitive positional projection used by the lowering of the add12
assignment at base/twiceprecision.jl:484. No user callback replaces the field
read. Native UInt32 field-count metadata separates a missing field from #undef.
Core field-read semantics follow the installed BootCov.getfieldObj model;
base/docs/basedocs.jl:2609-2620 specifies positional access and bounds checking;
the installed BootCov.getfieldObj model supplies BoundsError/UndefRefError
slot semantics.
The Module special case keeps Core's Symbol-only global lookup TypeError. -/
-- Source: base/twiceprecision.jl:484-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     x_hi, x_lo = add12(r.ref.hi, shift_hi)
-- /Source
def stepLenIndexedField {m : Type → Type} [Monad m] {V Bad : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (object : StepLenIndexedObject V) (position : StepLenProjection) : m V := do
  match object with
  | .moduleValue => throw StepLenError.getfieldTypeError
  | .fields count first second =>
      let index : JInt .u32 := JInt.wrap .u32 (match position with | .first => 1 | .second => 2)
      if count.val < index.val then throw (StepLenError.jl .boundsError)
      match (match position with | .first => first | .second => second) with
      | none => throw StepLenError.undefRefError
      | some value => pure value

/-- One variadic print argument is a literal String, a literal Char, or an
unrestricted result of open repr dispatch. The fixed five/seven argument lists
in the method are constructible Julia tuples; no arbitrary array is introduced.  Source use: base/range.jl:1142-1149. -/
-- Source: base/range.jl:1142-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::StepRangeLen)
--     if !iszero(step(r))
--         print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
--     else
--         # ugly temporary printing, to avoid 0:0:0 etc.
--         print(io, "StepRangeLen(", repr(first(r)), ", ", repr(step(r)), ", ", repr(length(r)), ")")
--     end
-- end
-- /Source
inductive StepLenPrintArg (P : Type) where
  | text (value : String)
  | char (value : Char)
  | rendered (value : P)

/-- Open leaves in the StepRangeLen accessors and display. Arithmetic,
oftype, element conversion/construction, add12, indexed_iterate, iszero, !,
repr and print dispatch on types this source does not fix. The concrete range
accessors and both unsafe_getindex algorithms are absent from this interface:
they are implemented below. add12 may return any Julia object A, with arbitrary
indexed_iterate effects and result shapes. State values use V and can change
runtime type between calls. No callee-correctness law is assumed.  Source use: base/range.jl:1142-1149. -/
-- Source: base/range.jl:1142-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::StepRangeLen)
--     if !iszero(step(r))
--         print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
--     else
--         # ugly temporary printing, to avoid 0:0:0 etc.
--         print(io, "StepRangeLen(", repr(first(r)), ", ", repr(step(r)), ", ", repr(length(r)), ")")
--     end
-- end
-- /Source
structure StepLenShowOps (m : Type → Type)
    (T R S L F G V A Z Bad P Stream Output : Type) where
  oftype : L → Sum JInt64 L → m V
  sub : StepLenScalar R S L F G V → StepLenScalar R S L F G V → m V
  mul : StepLenScalar R S L F G V → StepLenScalar R S L F G V → m V
  add : StepLenScalar R S L F G V → StepLenScalar R S L F G V → m V
  convertElement : TypeToken T → V → m V
  constructElement : TypeToken T → StepLenScalar R S L F G V → m V
  add12 : F → V → m A
  indexedIterateFirst : A → JInt64 → m (StepLenIndexedObject V)
  indexedIterateNext : A → JInt64 → V → m (StepLenIndexedObject V)
  iszero : StepLenScalar R S L F G V → m Z
  not : Z → m (Condition Bad)
  repr : StepLenScalar R S L F G V → m P
  print : Stream → List (StepLenPrintArg P) → m Output

/-- Concrete stored length, base/range.jl:807, for all four representations.
Each branch reuses the installed accessor. In particular custom integer L and
all constructible counts remain unchanged. -/
-- Source: base/range.jl:807-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(r::StepRangeLen) = r.len
-- /Source
def stepLenLength {T R S L F G : Type} (r : StepLenArgument T R S L F G) : L :=
  match r with
  | .ordinaryStored r | .ordinaryConverted r => length_StepRangeLen r
  | .twiceStored r | .twiceConverted r => length_StepRangeLen r

/-- Closed selection of the actual step bodies, base/range.jl:738-739 and
base/twiceprecision.jl:438-439. Stored access calls the installed accessor;
selected T(step) invokes the open scalar constructor at its original point.
The twiceConverted branch includes the non-floating matching T specialization. -/
-- Source: base/range.jl:738-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::StepRangeLen) = r.step
-- step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
-- /Source
-- Source: base/twiceprecision.jl:438-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- step(r::StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}}) where {T<:AbstractFloat} = T(r.step)
-- step(r::StepRangeLen{T,TwicePrecision{T},TwicePrecision{T}}) where {T} = T(r.step)
-- /Source
def stepLenStep {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepLenArgument T R S L F G) : m (StepLenScalar R S L F G V) := do
  match r with
  | .ordinaryStored r => pure (.step (step_StepRangeLen r))
  | .ordinaryConverted r =>
      pure (.dynamic (← ops.constructElement ⟨⟩ (.step (step_StepRangeLen r))))
  | .twiceStored r => pure (.twiceStep (step_StepRangeLen r))
  | .twiceConverted r =>
      pure (.dynamic (← ops.constructElement ⟨⟩ (.twiceStep (step_StepRangeLen r))))

/-- Ordinary unsafe_getindex body, base/range.jl:986-989. Native 1 and the
stored L-valued length remain distinct arguments to oftype. Every arithmetic
result uses V, so subtraction/multiplication can change runtime type or throw.
The final call is convert(T, value), not the constructor T(value). -/
-- Source: base/range.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T
--     u = oftype(r.offset, i) - r.offset
--     convert(T, (r.ref + u*r.step))
-- end
-- /Source
def stepLenUnsafeOrdinary {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepRangeLen T R S L) (i : Sum JInt64 L) : m V := do
  let converted ← ops.oftype r.offset i
  let u ← ops.sub (.dynamic converted) (.length r.offset)
  let shift ← ops.mul (.dynamic u) (.step r.step)
  let value ← ops.add (.reference r.ref) (.dynamic shift)
  ops.convertElement ⟨⟩ value

/-- Actual two-target destructuring of the open add12 result at
base/twiceprecision.jl:484. Source lowering uses indexed_iterate at 1, extracts
value then state, calls indexed_iterate at 2 with that state, and extracts only
the second value. Core field projections are concrete above; no tuple-return
law for custom add12 or indexed_iterate is assumed. -/
-- Source: base/twiceprecision.jl:484-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     x_hi, x_lo = add12(r.ref.hi, shift_hi)
-- /Source
def stepLenDestructure {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (result : A) : m (V × V) := do
  let first ← ops.indexedIterateFirst result (jint 1)
  let high ← stepLenIndexedField (Bad := Bad) first .first
  let state ← stepLenIndexedField (Bad := Bad) first .second
  let second ← ops.indexedIterateNext result (jint 2) state
  let low ← stepLenIndexedField (Bad := Bad) second .first
  pure (high, low)

/-- Optimized unsafe_getindex, base/twiceprecision.jl:480-486. The reference
parts F and step parts G are independently typed, exactly as the two separate
<:TwicePrecision constraints permit. Multiplication, add12 and nested additions
retain all errors/effects. The final operation is constructor T(value), distinct
from the ordinary branch's convert. Stored parts are direct fields, not arbitrary
whole-accessor callbacks. -/
-- Source: base/twiceprecision.jl:480-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, i::Integer) where T
--     # Very similar to _getindex_hiprec, but optimized to avoid a 2nd call to add12
--     u = oftype(r.offset, i) - r.offset
--     shift_hi, shift_lo = u*r.step.hi, u*r.step.lo
--     x_hi, x_lo = add12(r.ref.hi, shift_hi)
--     T(x_hi + (x_lo + (shift_lo + r.ref.lo)))
-- end
-- /Source
def stepLenUnsafeTwice {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepRangeLen T (F × F) (G × G) L) (i : Sum JInt64 L) : m V := do
  let converted ← ops.oftype r.offset i
  let u ← ops.sub (.dynamic converted) (.length r.offset)
  let shiftHigh ← ops.mul (.dynamic u) (.stepPart r.step.1)
  let shiftLow ← ops.mul (.dynamic u) (.stepPart r.step.2)
  let decomposition ← ops.add12 r.ref.1 shiftHigh
  let (high, low) ← stepLenDestructure ops decomposition
  let lowTail ← ops.add (.dynamic shiftLow) (.referencePart r.ref.2)
  let lowTotal ← ops.add (.dynamic low) (.dynamic lowTail)
  let value ← ops.add (.dynamic high) (.dynamic lowTotal)
  ops.constructElement ⟨⟩ (.dynamic value)

/-- Closed unsafe_getindex dispatch needed by first/last at
base/range.jl:869,878. Both TwicePrecision cases use the optimized body, whether
the public step accessor stores or constructs its result. Ordinary cases use
the actual ordinary body. No callback can replace either algorithm. -/
-- Source: base/range.jl:986-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T
--     u = oftype(r.offset, i) - r.offset
--     convert(T, (r.ref + u*r.step))
-- end
-- /Source
def stepLenUnsafeIndex {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepLenArgument T R S L F G) (i : Sum JInt64 L) : m V :=
  match r with
  | .ordinaryStored r | .ordinaryConverted r => stepLenUnsafeOrdinary ops r i
  | .twiceStored r | .twiceConverted r => stepLenUnsafeTwice ops r i

/-- Concrete first accessor, base/range.jl:869. The source index is native
Julia Int(1), not a conversion to the stored length type before calling oftype. -/
-- Source: base/range.jl:869-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::StepRangeLen) = unsafe_getindex(r, 1)
-- /Source
def stepLenFirst {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepLenArgument T R S L F G) : m V :=
  stepLenUnsafeIndex ops r (.inl (jint 1))

/-- Concrete last accessor, base/range.jl:878. Stored length uses its
installed accessor and is passed unchanged to the selected indexing body. -/
-- Source: base/range.jl:878-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::StepRangeLen) = unsafe_getindex(r, length(r))
-- /Source
def stepLenLast {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (r : StepLenArgument T R S L F G) : m V :=
  stepLenUnsafeIndex ops r (.inr (stepLenLength r))

/-- Full effectful StepRangeLen show caller, base/range.jl:1142-1149.
Every concrete range accessor uses its real body, including TwicePrecision
indexing. iszero and ! retain open dispatch, followed by the native Bool check.
The step accessor is evaluated twice; its first value is never cached for repr.
All three repr argument evaluations precede the single variadic print invocation,
whose return value and effects are retained unchanged. -/
-- Source: base/range.jl:1142-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::StepRangeLen)
--     if !iszero(step(r))
--         print(io, repr(first(r)), ':', repr(step(r)), ':', repr(last(r)))
--     else
--         # ugly temporary printing, to avoid 0:0:0 etc.
--         print(io, "StepRangeLen(", repr(first(r)), ", ", repr(step(r)), ", ", repr(length(r)), ")")
--     end
-- end
-- /Source
def showStepRangeLen {m : Type → Type} [Monad m]
    {T R S L F G V A Z Bad P Stream Output : Type}
    [MonadExceptOf (StepLenError Bad) m]
    (ops : StepLenShowOps m T R S L F G V A Z Bad P Stream Output)
    (io : Stream) (r : StepLenArgument T R S L F G) : m Output := do
  let initialStep ← stepLenStep ops r
  let zero ← ops.iszero initialStep
  let condition ← ops.not zero
  let nonzero ← match condition with
    | .bool value => pure value
    | .other value => throw (StepLenError.conditionTypeError value)
  if nonzero then
    let first ← ops.repr (.dynamic (← stepLenFirst ops r))
    let step ← ops.repr (← stepLenStep ops r)
    let last ← ops.repr (.dynamic (← stepLenLast ops r))
    ops.print io [.rendered first, .char ':', .rendered step, .char ':', .rendered last]
  else
    let first ← ops.repr (.dynamic (← stepLenFirst ops r))
    let step ← ops.repr (← stepLenStep ops r)
    let length ← ops.repr (.length (stepLenLength r))
    ops.print io [.text "StepRangeLen(", .rendered first, .text ", ", .rendered step,
      .text ", ", .rendered length, .text ")"]

end JuliaLean.base.range.Models2Group20

namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-- A state/error computation with a separate divergent outcome. A failure
retains the world reached at its throw point. This local representation follows
the installed `base.io.M` pattern without adding an unavailable IO import.  Source use: base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
abbrev RangeEffect (Error World A : Type) :=
  World → Option (Except (Error × World) (A × World))

/-- Sequential state/error composition for base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
scoped instance rangeEffectMonad {Error World : Type} : Monad (RangeEffect Error World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => do
    match ← action world with
    | .error error => pure (.error error)
    | .ok (value, world) => next value world

/-- Error handling preserves the changed world, base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
scoped instance rangeEffectExcept {Error World : Type} : MonadExceptOf Error (RangeEffect Error World) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

/-- A tagged carrier can include every Julia runtime type. Its tag and payload
may change at every iteration, rather than fixing one Julia state type.  Source use: base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
abbrev Dynamic (Code : Type) (Value : Code → Type) := Sigma Value

/-- The equality caller introduces only a Boolean-context TypeError or the
known getindex(::Nothing, ::Int) MethodError. Callee errors are unrestricted.  Source use: base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
inductive EqualityError (Value Foreign : Type) where
  | base (error : Exc)
  | typeError (value : Value)
  | callee (error : Foreign)

/-- Open calls of base/range.jl:1180-1193. An iterate result is either actual
nothing or an arbitrary dynamic object, not an assumed pair. Its getindex
calls are therefore retained. Both ranges and all returned types are open. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
structure RangeEqualityOps (m : Type → Type) (R S V : Type) where
  lengthR : R → m V
  lengthS : S → m V
  ne : V → V → m (Condition V)
  iszero : V → m (Condition V)
  iterateR : R → m (Option V)
  iterateS : S → m (Option V)
  getindex : V → JInt64 → m V
  eq : V → V → m (Condition V)
  nextR : R → V → m (Option V)
  nextS : S → V → m (Option V)

/-- Actual fuel-free recursion for the source while-loop. `none` denotes a
divergent execution; there is no synthetic exhaustion error. The step is built
from the caller's explicit body below, not supplied as its implementation.  Source use: base/range.jl:1180-1193. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
def equalityWhile {Error World State : Type}
    (step : State → RangeEffect Error World (Sum Bool State))
    (state : State) : RangeEffect Error World Bool := fun world =>
  match step state world with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (.inl value, world)) => some (.ok (value, world))
  | some (.ok (.inr next, world)) => equalityWhile step next world
partial_fixpoint

/-- One source loop iteration, base/range.jl:1188-1192. The left iterator
controls exhaustion. A prematurely exhausted right iterator raises MethodError
only after reading the current left element. Next-state indexing and iteration
remain interleaved left then right as in the tuple-assignment RHS. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
def equalityIteration {R S V Foreign World : Type}
    (ops : RangeEqualityOps (RangeEffect (EqualityError V Foreign) World) R S V)
    (r : R) (s : S) (state : Option V × Option V) :
    RangeEffect (EqualityError V Foreign) World (Sum Bool (Option V × Option V)) := do
  match state.1 with
  | none => pure (.inl true)
  | some yr =>
      let left ← ops.getindex yr (jint 1)
      let right ← match state.2 with
        | none => throw (EqualityError.base (.jl (.methodError "getindex")))
        | some ys => ops.getindex ys (jint 1)
      let condition ← ops.eq left right
      match condition with
      | .other bad => throw (EqualityError.typeError bad)
      | .bool false => pure (.inl false)
      | .bool true =>
          let rstate ← ops.getindex yr (jint 2)
          let yr ← ops.nextR r rstate
          let sstate ← match state.2 with
            | none => throw (EqualityError.base (.jl (.methodError "getindex")))
            | some ys => ops.getindex ys (jint 2)
          let ys ← ops.nextS s sstate
          pure (.inr (yr, ys))

/-- Full generic range equality, base/range.jl:1180-1193. Length checks precede
iteration, while iterations have genuinely changing dynamic states. The two
initial iterations run even when the first returns nothing. The loop is actual
recursion over the error/state semantics and can diverge without inventing a
Julia error. No callee-correctness or termination law is required. -/
-- Source: base/range.jl:1180-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(r::AbstractRange, s::AbstractRange)
--     lr = length(r)
--     if lr != length(s)
--         return false
--     elseif iszero(lr)
--         return true
--     end
--     yr, ys = iterate(r), iterate(s)
--     while yr !== nothing
--         yr[1] == ys[1] || return false
--         yr, ys = iterate(r, yr[2]), iterate(s, ys[2])
--     end
--     return true
-- end
-- /Source
def eqAbstractRange {R S Code Foreign World : Type} {Value : Code → Type}
    (ops : RangeEqualityOps
      (RangeEffect (EqualityError (Dynamic Code Value) Foreign) World)
      R S (Dynamic Code Value)) (r : R) (s : S) :
    RangeEffect (EqualityError (Dynamic Code Value) Foreign) World Bool := do
  let lr ← ops.lengthR r
  let ls ← ops.lengthS s
  let different ← ops.ne lr ls
  match different with
  | .other bad => throw (EqualityError.typeError bad)
  | .bool true => pure false
  | .bool false =>
      let zero ← ops.iszero lr
      match zero with
      | .other bad => throw (EqualityError.typeError bad)
      | .bool true => pure true
      | .bool false =>
          let yr ← ops.iterateR r
          let ys ← ops.iterateS s
          equalityWhile (equalityIteration ops r s) (yr, ys)

end JuliaLean.base.range.Models2Group20

namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-- A constructible heterogeneous vararg tuple. Its field count fits the actual UInt32
runtime layout metadata, and its native length and terminal state fit Julia Int. Each element has its own runtime tag;
the carrier does not require the ranges to share a concrete Julia type.
This is the tuple representation for base/range.jl:1287-1293. -/
-- Source: base/range.jl:1287-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)
--     i = intersect(intersect(r1, r2), r3)
--     for t in r
--         i = intersect(i, t)
--     end
--     i
-- end
-- /Source
structure RangeArguments (Code : Type) (Value : Code → Type) where
  values : List (Dynamic Code Value)
  fieldCountFits : values.length ≤ IntTy.u32.max.toNat

/-- Concrete tuple length from field-count metadata, base/tuple.jl:28.
The UInt32 runtime bound (base/runtime_internals.jl:624-627) makes this an exact
native Int value; no unbounded mathematical length replaces source arithmetic. -/
-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source
def rangeArgumentsLength {Code : Type} {Value : Code → Type}
    (arguments : RangeArguments Code Value) : JInt64 :=
  ⟨(arguments.values.length : Int), by
    have bound := arguments.fieldCountFits
    simp [IntTy.max, IntTy.min, IntTy.signed, IntTy.bits] at bound ⊢
    omega⟩

/-- Concrete native-state Tuple iteration, base/tuple.jl:69-73. The positional
field read follows both source bounds checks; the stored immutable field is
selected by a proved in-bounds address. The returned state uses installed
wrapping Int addition. No callback or fuel substitutes for Tuple iteration. -/
-- Source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(@nospecialize(t::Tuple), i::Int=1)
--     @inline
--     @_nothrow_meta
--     return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
-- end
-- /Source
def rangeArgumentsIterate {Code : Type} {Value : Code → Type}
    (arguments : RangeArguments Code Value) (index : JInt64 := jint 1) :
    Option (Dynamic Code Value × JInt64) :=
  let length := rangeArgumentsLength arguments
  if checked : 1 ≤ index.val ∧ index.val ≤ length.val then
    let position : Fin arguments.values.length := ⟨(index.val - 1).toNat, by
      change 1 ≤ index.val ∧ index.val ≤ (arguments.values.length : Int) at checked
      omega⟩
    some (arguments.values[position], index + jint 1)
  else none

/-- Selected binary intersection calls, base/range.jl:1287-1293. The changing
accumulator is explicitly a tagged dynamic value and may become an Array or
another type after any call. No closure over one fixed Julia accumulator type
or one fixed Julia type for the remaining ranges is assumed. -/
-- Source: base/range.jl:1287-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)
--     i = intersect(intersect(r1, r2), r3)
--     for t in r
--         i = intersect(i, t)
--     end
--     i
-- end
-- /Source
structure IntersectManyOps (m : Type → Type) (R1 R2 R3 RangeValue AccValue : Type) where
  firstTwo : R1 → R2 → m AccValue
  third : AccValue → R3 → m AccValue
  next : AccValue → RangeValue → m AccValue

/-- Actual traversal of the concrete tuple in base/range.jl:1289-1291.
Tuple iteration calls the concrete native helper and visits stored fields in
order. The UInt32 field-count bound excludes native-state overflow. This helper
performs the actual loop recursion, preserving every call result and world. -/
-- Source: base/range.jl:1287-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)
--     i = intersect(intersect(r1, r2), r3)
--     for t in r
--         i = intersect(i, t)
--     end
--     i
-- end
-- /Source
def intersectManyTail {R1 R2 R3 RangeCode AccValue Error World : Type}
    {RangeValue : RangeCode → Type}
    (ops : IntersectManyOps (RangeEffect Error World) R1 R2 R3
      (Dynamic RangeCode RangeValue) AccValue)
    (arguments : RangeArguments RangeCode RangeValue) (acc : AccValue)
    (index : JInt64) : RangeEffect Error World AccValue := fun world =>
  match rangeArgumentsIterate arguments index with
  | none => some (.ok (acc, world))
  | some (current, nextIndex) =>
      match ops.next acc current world with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (next, after)) => intersectManyTail ops arguments next nextIndex after
partial_fixpoint

/-- Three-or-more range intersection, base/range.jl:1287-1293. Retains the
left-associated first two calls and the ordered concrete tuple loop. Both
remaining arguments and successive accumulator results may change Julia type;
exceptions, state changes and arbitrary callee return values are preserved. -/
-- Source: base/range.jl:1287-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)
--     i = intersect(intersect(r1, r2), r3)
--     for t in r
--         i = intersect(i, t)
--     end
--     i
-- end
-- /Source
def intersectRangesMany {R1 R2 R3 RangeCode AccCode Error World : Type}
    {RangeValue : RangeCode → Type} {AccValue : AccCode → Type}
    (ops : IntersectManyOps (RangeEffect Error World) R1 R2 R3
      (Dynamic RangeCode RangeValue) (Dynamic AccCode AccValue))
    (r1 : R1) (r2 : R2) (r3 : R3) (rest : RangeArguments RangeCode RangeValue) :
    RangeEffect Error World (Dynamic AccCode AccValue) := do
  let first ← ops.firstTwo r1 r2
  let initial ← ops.third first r3
  intersectManyTail ops rest initial (jint 1)

end JuliaLean.base.range.Models2Group20


namespace JuliaLean.base.range.Models2Group20

open JuliaLean

/-- Open IO dispatch of LogRange show, base/range.jl:1726-1735. The initial
print is a single variadic invocation containing the actual type argument.
All result carriers are independent; context and endpoint display are effectful. -/
-- Source: base/range.jl:1726-1735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LogRange{T}) where {T}
--     print(io, "LogRange{", T, "}(")
--     ioc = IOContext(io, :typeinfo => T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
structure LogShowOps (m : Type → Type)
    (Stream Context T OpeningResult PrintResult ValueResult LengthResult Result : Type) where
  printType : Stream → String → TypeToken T → String → m OpeningResult
  context : Stream → ContextKey → TypeToken T → m Context
  showValue : Context → T → m ValueResult
  printString : Stream → String → m PrintResult
  showLength : Stream → JInt64 → m LengthResult
  printChar : Stream → Char → m Result

/-- Incremental LogRange display, base/range.jl:1726-1735. It uses the installed
concrete first/last/length models, retains the opening variadic call, and sends
only endpoint displays to the returned context. Later failures preserve earlier
writes in state-preserving effect instantiations. No cached-log field is read. -/
-- Source: base/range.jl:1726-1735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, r::LogRange{T}) where {T}
--     print(io, "LogRange{", T, "}(")
--     ioc = IOContext(io, :typeinfo => T)
--     show(ioc, first(r))
--     print(io, ", ")
--     show(ioc, last(r))
--     print(io, ", ")
--     show(io, length(r))
--     print(io, ')')
-- end
-- /Source
def showLogRange {m : Type → Type} [Monad m]
    {Stream Context T X OpeningResult PrintResult ValueResult LengthResult Result : Type}
    (ops : LogShowOps m Stream Context T OpeningResult PrintResult ValueResult LengthResult Result)
    (io : Stream) (r : LogRange T X) : m Result := do
  let _ ← ops.printType io "LogRange{" ⟨⟩ "}("
  let ioc ← ops.context io .typeinfo ⟨⟩
  let _ ← ops.showValue ioc (first_LogRange r)
  let _ ← ops.printString io ", "
  let _ ← ops.showValue ioc (last_LogRange r)
  let _ ← ops.printString io ", "
  let _ ← ops.showLength io (length_LogRange r)
  ops.printChar io ')'

end JuliaLean.base.range.Models2Group20

namespace JuliaLean.Multidim

/-- An `OrdinalRange{Int,Int}`: `start`, `step` and `length`. -/
structure Rng where
  start : I64
  step : I64
  len : Nat
  deriving DecidableEq, Repr

/-- The exact value of the `j`-th element (0-based). -/
def Rng.elem (r : Rng) (j : Int) : Int := r.start.val + j * r.step.val

/-- `last(r)`: the normalised `stop` field, `start + (len-1)*step` (for an empty range
`start - step`, as `steprange_last_empty` produces), `base/range.jl`. -/
def Rng.last (r : Rng) : I64 := JInt.wrap .i64 (r.elem ((r.len : Int) - 1))

/-- The elements of `r`, in iteration order. -/
def Rng.elems (r : Rng) : List I64 :=
  (List.range r.len).map fun (j : Nat) => JInt.wrap .i64 (r.elem j)

/-- `in(x, r)` for an integer range: `x` is one of its elements. -/
def Rng.contains (r : Rng) (x : I64) : Bool := r.elems.contains x

/-- 0-based position of the exact integer `x` in `r`, if it is an element. -/
def Rng.pos (r : Rng) (x : Int) : Option Nat :=
  if r.step.val ≠ 0 ∧ (x - r.start.val) % r.step.val = 0 ∧ 0 ≤ (x - r.start.val) / r.step.val ∧
      (x - r.start.val) / r.step.val < r.len
  then some ((x - r.start.val) / r.step.val).toNat else none

/-- The unit range `lo:hi` (`UnitRange{Int}`), converted for a `CartesianIndices`. -/
def unitRng (lo hi : Int) : Rng := ⟨i64 lo, i64 1, (hi - lo + 1).toNat⟩

end JuliaLean.Multidim

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- A `UnitRange{Int}` `lo:hi`. -/
structure URange where
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

/-- `length(lo:hi)` (exact for the modelled inputs; `checked_length` throws on overflow). -/
def URange.len (r : URange) : Nat := (r.hi.val - r.lo.val + 1).toNat

/-- The elements of `lo:hi`. -/
def URange.elems (r : URange) : List I64 := (List.range r.len).map (fun k : Nat => r.lo + i64 k)

/-- `+(r1::OrdinalRange, r2::OrdinalRange)`, `base/range.jl:1493-1498`: throws `DimensionMismatch`
unless the lengths are equal, else `StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), r1l)`,
whose elements are `(first(r1)+first(r2)) + k*(1+1)`. Reached from
`broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r1::AbstractRange, r2::AbstractRange) = r1 + r2`
(`base/broadcast.jl:1198`). -/
def bcAddRanges (r1 r2 : URange) : R (List I64) :=
  if r1.len = r2.len then
    .ok ((List.range r1.len).map (fun k : Nat => (r1.lo + r2.lo) + i64 k * (i64 1 + i64 1)))
  else .error .dimensionMismatch

/-- Julia `UInt64`. -/
abbrev U64 := JInt .u64

/-- `r[i]` for the `StepRangeLen` built by `floatrangeU` (exact value of the `TwicePrecision`
evaluation): `u = oftype(r.offset, i) - r.offset` is a `UInt64` difference
(`base/range.jl:1096`), then `ref + u*step`. -/
def srlElemU (ref : Int) (offset : U64) (stepN : Int) (i : Nat) : Int :=
  ref + (JInt.wrap .u64 ((i : Int) - offset.val)).val * stepN

/-- Julia `UInt8` and `Int8`. -/
abbrev U8 := JInt .u8
abbrev I8 := JInt .i8

/-- A `StepRange{UInt8,Int8}` after construction: `start`, `step`, normalised `stop`. -/
structure SRange8 where
  start : U8
  step : I8
  stop : U8
  deriving DecidableEq, Repr

/-- `steprange_last(start, step, stop)`, `base/range.jl:353-387` (exact: the differences of `UInt8`
values fit), with `steprange_last_empty` (389-397) for an empty range. -/
def steprangeLast (start : U8) (step : I8) (stop : U8) : R U8 :=
  if step.val = 0 then .error .argumentError
  else if stop.val = start.val then .ok stop
  else if (step.val > 0) ≠ (stop.val > start.val) then
    .ok (if step.val > 0 then JInt.wrap .u8 (start.val - 1) else JInt.wrap .u8 (start.val + 1))
  else
    let absdiff := if stop.val > start.val then stop.val - start.val else start.val - stop.val
    let absstep := if stop.val > start.val then step.val else -step.val
    let remain := absdiff % absstep
    .ok (if stop.val > start.val then JInt.wrap .u8 (stop.val - remain) else JInt.wrap .u8 (stop.val + remain))

/-- `start:step:stop` for `UInt8` endpoints and an `Int8` step (`StepRange` constructor). -/
def mkSRange8 (start : U8) (step : I8) (stop : U8) : R SRange8 := do
  let last ← steprangeLast start step stop
  pure ⟨start, step, last⟩

/-- The elements of a `StepRange{UInt8,Int8}`: `length = div(stop - start, step) + 1` when the
range is nonempty (`base/range.jl`, `length(::OrdinalRange)`), elements `start + k*step` in `UInt8`. -/
def SRange8.elems (r : SRange8) : List U8 :=
  let n := (r.stop.val - r.start.val) / r.step.val + 1
  if (r.step.val > 0 ∧ r.stop.val < r.start.val) ∨ (r.step.val < 0 ∧ r.stop.val > r.start.val) then []
  else (List.range n.toNat).map (fun k : Nat => JInt.wrap .u8 (r.start.val + (k : Int) * r.step.val))

/-- `negate(x::Unsigned) = -convert(Signed, x)`, `base/int.jl:97`, for the `UInt8` step `1`. -/
def negateOne8 : I8 := -(JInt.lit .i8 1)

/-- The elements of `lo:hi::UnitRange{UInt8}`. -/
def urange8Elems (lo hi : U8) : List U8 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun k : Nat => JInt.wrap .u8 (lo.val + (k : Int)))

end JuliaLean.BroadcastViews

namespace JuliaLean.AbstractArraySpecs

/-- `length(r)`: `r.stop` for `OneTo` (base/range.jl:806), else
`oneunit + (stop - start)` with wrapping `Int` arithmetic (base/range.jl:794-805). -/
def axLength (r : Ax) : I64 :=
  match r.kind with
  | .oneTo => r.hi
  | .unit => i64 1 + (r.hi - r.lo)

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)` (base/range.jl:711). -/
def axIsEmpty (r : Ax) : Bool := decide (r.hi < r.lo)

/-- `==` on two `AbstractUnitRange{Int}` (base/range.jl:1141-1150): empty ranges are
equal, a length-one range equals a length-one range with the same first element,
otherwise first, step (always 1) and last must agree. -/
def axEq (r s : Ax) : Bool :=
  if axIsEmpty r then axIsEmpty s
  else if axLength r == i64 1 then (axLength s == i64 1) && (r.lo == s.lo)
  else (r.lo == s.lo) && (r.hi == s.hi)

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.Ranges

/-- `base/range.jl:339-350,425-429,486-511`: integer ordinal range representations. -/
inductive RangeKind where
  | unit | step | oneTo
  deriving DecidableEq, Repr

/-- `base/range.jl:339-350,425-429,486-511`: stored endpoints and step. -/
structure Rng where
  kind : RangeKind
  start : Num
  stride : Num
  stop : Num
  deriving DecidableEq

/-- `base/range.jl:867-868`: OneTo supplies a type-level lower endpoint. -/
def first (r : Rng) : Num :=
  if r.kind = .oneTo then Num.one r.stop.ty else r.start

/-- `base/range.jl:877`: constructors store the normalized last endpoint. -/
def last (r : Rng) : Num := r.stop

/-- `base/range.jl:735-737`: Bool unit steps stay Bool; other units subtract zero. -/
def step (r : Rng) : Num :=
  if r.kind = .step then r.stride
  else if r.start.ty = .bool then Num.one .bool
  else Num.sub (Num.one r.start.ty) (Num.zero r.start.ty)

/-- `base/range.jl:708-711`: emptiness uses direction and normalized endpoints. -/
def isEmpty (r : Rng) : Bool :=
  if r.kind = .step then
    !Num.eq r.start r.stop && ((decide (r.stride.val > 0)) != (decide (r.stop.val > r.start.val)))
  else decide ((first r).val > (last r).val)

/-- `base/range.jl:439-441`: integral UnitRange empty normalization. -/
def unitrangeLast (a b : Num) : Jl Num :=
  if b.val ≥ a.val then .ok b
  else Num.cast b.ty (Num.sub a (Num.one (Num.sub a b).ty))

/-- `base/range.jl:428-435`: UnitRange promotes endpoints by exact conversion. -/
def unit (a b : Num) : Jl Rng := do
  let ty := Num.promote a.ty b.ty
  let a ← Num.cast ty a
  let b ← Num.cast ty b
  let z ← unitrangeLast a b
  pure ⟨.unit, a, Num.one ty, z⟩

/-- `base/range.jl:389-399`: empty StepRange uses oneunit(step), with a Bool xor specialization. -/
def steprangeLastEmpty (a s b : Num) : Jl Num :=
  if a.ty = .bool then
    .ok (Num.lit .bool (if decide (a.val ≠ 0) != decide (s.val > 0) then 1 else 0))
  else Num.cast b.ty (if s.val > 0 then Num.sub a (Num.one s.ty) else Num.add a (Num.one s.ty))

/-- `base/range.jl:353-387`: signed-overflow remainder uses unsigned(absdiff), including typemin steps. -/
def steprangeLast (a s b : Num) : Jl Num := do
  if s.val = 0 then .error (.argumentError "step cannot be zero")
  else if b.val = a.val then pure b
  else if decide (s.val > 0) != decide (b.val > a.val) then steprangeLastEmpty a s b
  else
    let (diff, st) := if b.val > a.val then (Num.sub b a, s) else (Num.sub a b, Num.neg s)
    let rem ← Num.rem (if diff.ty.signed && decide (diff.val < 0) then Num.unsigned diff else diff) st
    let rem ← Num.cast diff.ty rem
    Num.cast b.ty (if b.val > a.val then Num.sub b rem else Num.add b rem)

/-- `base/range.jl:339-350,404-405`: the unparameterized StepRange requires equal endpoint types. -/
def stepRange (a s b : Num) : Jl Rng := do
  if a.ty ≠ b.ty then .error (.methodError "StepRange")
  else
    let z ← steprangeLast a s b
    pure ⟨.step, a, s, z⟩

/-- `base/range.jl:3-5`: two-argument colon promotes exactly and constructs UnitRange. -/
def colon2 (a b : Num) : Jl Rng := unit a b

/-- `base/range.jl:10-11,22-24,64-70`: colon preserves step type, widening endpoints through start+zero(step). -/
def colon3 (a s b : Num) : Jl Rng := do
  let ty := Num.promote a.ty b.ty
  let a ← Num.cast ty a
  let b ← Num.cast ty b
  if ty = s.ty then stepRange a s b
  else
    let ty' := (Num.add a (Num.zero s.ty)).ty
    let a ← Num.cast ty' a
    let b ← Num.cast ty' b
    stepRange a s b

/-- `base/range.jl:486-492,513`: OneTo rejects Bool, then clips negative stops to zero. -/
def oneTo (n : Num) : Jl Rng :=
  if n.ty = .bool then .error (.argumentError "invalid index of type Bool")
  else .ok ⟨.oneTo, Num.one n.ty, Num.one n.ty, Num.max (Num.zero n.ty) n⟩

/-- `base/range.jl:777-791`: generic ordinal length, used for Bool element ranges. -/
def genericLength (r : Rng) : Jl Num := do
  let s := step r
  let a := first r
  if isEmpty r then Num.div (Num.sub a a) (Num.one s.ty)
  else
    let (diff, s) := if s.val < 0 then (Num.sub a (last r), Num.neg s) else (Num.sub (last r) a, s)
    let q ← Num.div diff s
    pure (Num.add q (Num.one q.ty))

/-- `base/range.jl:794-806,817-829,853-860`: all built-in integer length specializations. -/
def length (r : Rng) : Jl Num := do
  let a := first r
  let b := last r
  if r.kind = .oneTo then
    if b.ty.small then Num.cast (.bit .i64) b else pure b
  else if a.ty.small then
    let a ← Num.cast (.bit .i64) a
    let b ← Num.cast (.bit .i64) b
    if r.kind ≠ .step then pure (Num.add (Num.sub b a) (Num.one (.bit .i64)))
    else if isEmpty r then pure (Num.zero (.bit .i64))
    else
      let q ← Num.div (Num.sub b a) (step r)
      let q ← Num.cast (.bit .i64) q
      pure (Num.add q (Num.one (.bit .i64)))
  else if r.kind ≠ .step then
    let unit := Num.one (Num.sub (Num.zero b.ty) (Num.zero a.ty)).ty
    if unit.ty.signed || decide (b.val ≥ a.val) then pure (Num.add unit (Num.sub b a))
    else pure (Num.zero unit.ty)
  else if a.ty = .bool then genericLength r
  else
    let s := step r
    let diff := Num.sub b a
    if isEmpty r then pure (Num.zero diff.ty)
    else
      let q ← Num.div (Num.unsigned (Num.flipsign diff s)) s
      let q := Num.lit diff.ty q.val
      pure (Num.add (Num.flipsign q s) (Num.one q.ty))

/-- `base/range.jl:751-775`: generic checked ordinal/unit length (Bool element specialization). -/
def genericCheckedLength (r : Rng) : Jl Num := do
  let a := first r
  if r.kind ≠ .step then
    if isEmpty r then pure (Num.sub a a)
    else
      let q ← Num.checkedSub (last r) a
      Num.checkedAdd q (Num.one q.ty)
  else
    let s := step r
    if isEmpty r then Num.div (Num.sub a a) (Num.one s.ty)
    else
      let diff ← if s.val < 0 then Num.checkedSub a (last r) else Num.checkedSub (last r) a
      let q ← Num.div diff (if s.val < 0 then Num.neg s else s)
      Num.checkedAdd q (Num.one q.ty)

/-- `base/range.jl:768-775,831-848,861-863`: checked length preserves intermediate conversions/errors. -/
def checkedLength (r : Rng) : Jl Num := do
  let a := first r
  if a.ty.small then length r
  else if r.kind ≠ .step ∨ a.ty = .bool then genericCheckedLength r
  else
    let s := step r
    let b := last r
    let ty := Num.promote b.ty a.ty
    if isEmpty r then pure (Num.zero ty)
    else
      let q ← if s.val > 1 then
          Num.div (Num.unsigned (Num.sub b a)) s
        else if s.val < -1 then
          Num.div (Num.unsigned (Num.sub a b)) (Num.neg s)
        else if s.val > 0 then do
          let diff ← Num.checkedSub b a
          Num.div diff s
        else do
          let diff ← Num.checkedSub a b
          Num.div diff (Num.neg s)
      let q ← Num.cast ty q
      Num.checkedAdd q (Num.one q.ty)

/-- Mathematical cardinality of normalized ordinal ranges, without machine-width overflow. -/
def trueCount (r : Rng) : Int :=
  if isEmpty r then 0
  else if r.kind ≠ .step then (last r).val - (first r).val + 1
  else ((last r).val - (first r).val).tdiv (step r).val + 1

/-- `base/range.jl:974-978`: specialized bounds arithmetic widens products before adding first. -/
def stepBounds64 (r : Rng) (i : Num) (hs : (step r).ty.bits ≤ 64) (hi : i.ty.bits ≤ 64) : Bool :=
  let j := Num.sub i (Num.one i.ty)
  let res := Num.add (Num.widemul64 (step r) j hs (Num.sub_one_bits_le64 i hi)) (first r)
  decide (0 < i.val) && (if (step r).val > 0 then decide (res.val ≤ (last r).val) else decide (res.val ≥ (last r).val))

/-- `base/range.jl:950-953,974-978`, `base/abstractarray.jl` linear bounds: StepRange64 avoids length. -/
def scalarBounds (r : Rng) (i : Num) : Jl Bool := do
  if h : r.kind = .step ∧ r.start.ty ≠ .bool ∧ r.stride.ty ≠ .bool ∧ i.ty ≠ .bool ∧
      r.start.ty.bits ≤ 64 ∧ r.stride.ty.bits ≤ 64 ∧ i.ty.bits ≤ 64 then
    have hs : (step r).ty.bits ≤ 64 := by simpa [step, h.1] using h.2.2.2.2.2.1
    pure (stepBounds64 r i hs h.2.2.2.2.2.2)
  else
    let n ← length r
    pure (decide (1 ≤ i.val ∧ i.val ≤ n.val))

/-- `base/range.jl:950-971,984-985`, `base/abstractarray.jl`: scalar indexing rejects Bool before bounds. -/
def getindex (r : Rng) (i : Num) : Jl Num := do
  if i.ty = .bool then .error (.argumentError "invalid index of type Bool")
  else if r.kind = .unit then
    let v := Num.add r.start (Num.sub i (Num.one i.ty))
    if i.val > 0 ∧ v.val ≤ r.stop.val ∧ v.val ≥ r.start.val then
      pure (Num.lit r.start.ty v.val)
    else .error .boundsError
  else
    let valid ← scalarBounds r i
    if !valid then .error .boundsError
    else if r.kind = .oneTo then Num.cast r.stop.ty i
    else Num.cast r.start.ty (Num.add (first r) (Num.mul (Num.sub i (Num.one i.ty)) (step r)))

/-- `base/range.jl:935-942`: ordinal iteration carries the current element, terminating at last. -/
def iterate (r : Rng) (state : Option Num := none) : Jl (Option Num) := do
  match state with
  | none => pure (if isEmpty r then none else some (first r))
  | some i =>
      if Num.eq i (last r) then pure none
      else
        let n ← Num.cast r.start.ty (Num.add i (step r))
        pure (some n)

/-- Integer-element `StepRangeLen` fields, base/range.jl:530-535. -/
structure RngLen where
  ref : Num
  stride : Num
  len : Num
  offset : Num
  elementTy : NType
  deriving DecidableEq

inductive ResultRng where
  | ordinal (r : Rng)
  | counted (r : RngLen)
  deriving DecidableEq

/-- `StepRangeLen{T,R,S}` and default length promotion, base/range.jl:537-561.
Only integer reference and step types are in this model. -/
def countedRange (elementTy : NType) (ref stride len : Num)
    (offset : Num := Num.lit (.bit .i64) 1) : Jl ResultRng := do
  let L := Num.promote (.bit .i64) len.ty
  let n ← Num.cast L len
  if n.val < 0 then
    throw (.argumentError "length cannot be negative")
  let o ← Num.cast L offset
  if o.val < 1 ∨ o.val > max 1 n.val then
    throw (.argumentError "StepRangeLen: offset must be in range")
  return .counted ⟨ref, stride, n, o, elementTy⟩

/-- `range_start_length`, base/range.jl:217-226. -/
def rangeStartLength (a len : Num) : Jl ResultRng := do
  let stride ← Num.cast (Num.sub a a).ty (Num.lit (.bit .i64) 1)
  let stop := Num.add a (Num.sub len (Num.one len.ty))
  match stop.ty with
  | .bit t =>
    if t.signed then
      let start ← Num.cast stop.ty a
      return .ordinal (← unit start stop)
    else
      countedRange stop.ty a stride len
  | .bool => countedRange stop.ty a stride len

/-- `range_stop_length`, base/range.jl:206-215. -/
def rangeStopLength (a len : Num) : Jl ResultRng := do
  let stride ← Num.cast (Num.sub a a).ty (Num.lit (.bit .i64) 1)
  let start := Num.sub a (Num.sub len (Num.one len.ty))
  match start.ty with
  | .bit t =>
    if t.signed then
      let stop ← Num.cast start.ty a
      return .ordinal (← unit start stop)
    else
      countedRange start.ty start stride len
  | .bool => countedRange start.ty start stride len

/-- `range_start_step_length`, base/range.jl:230-238. -/
def rangeStartStepLength (a stride len : Num) : Jl ResultRng := do
  let stop := Num.add a (Num.mul stride (Num.sub len (Num.one len.ty)))
  match stop.ty with
  | .bit t =>
    if t.signed then
      let start ← Num.cast stop.ty a
      return .ordinal (← stepRange start stride stop)
    else
      countedRange stop.ty a stride len
  | .bool => countedRange stop.ty a stride len

/-- `range_step_stop_length`, base/range.jl:195-204. -/
def rangeStepStopLength (stride a len : Num) : Jl ResultRng := do
  let start := Num.sub a (Num.mul stride (Num.sub len (Num.one len.ty)))
  match start.ty with
  | .bit t =>
    if t.signed then
      let stop ← Num.cast start.ty a
      return .ordinal (← stepRange start stride stop)
    else
      countedRange start.ty start stride len
  | .bool => countedRange start.ty start stride len

/-- `length(::StepRangeLen)` and ordinal dispatch, base/range.jl:811-813. -/
def resultLength : ResultRng → Jl Num
  | .ordinal r => length r
  | .counted r => .ok r.len

/-- `unsafe_getindex(::StepRangeLen)` with generic scalar index validation,
base/range.jl:976-984 and base/abstractarray.jl scalar Bool-index rejection. -/
def resultGetindex (r : ResultRng) (i : Num) : Jl Num := do
  match r with
  | .ordinal r => getindex r i
  | .counted r =>
    if i.ty = .bool then throw (.argumentError "invalid index of type Bool")
    if i.val < 1 ∨ i.val > r.len.val then throw .boundsError
    let ii ← Num.cast r.offset.ty i
    let u := Num.sub ii r.offset
    Num.cast r.elementTy (Num.add r.ref (Num.mul u r.stride))

/-- `range_error` hint, base/range.jl:243-259. Line 247 reads
`haslength = start !== nothing`, so `haslength` copies `hasstart`. Only the hint
line of the ArgumentError message (base/range.jl:261-269) is modelled. -/
def rangeErrorHint (start step stop _len : Option Num) : String :=
  let hasstart := start.isSome
  let hasstep := step.isSome
  let hasstop := stop.isSome
  let haslength := start.isSome
  if hasstart && hasstep && hasstop && haslength then "Try specifying only three arguments"
  else if !hasstop && !haslength then "At least one of `length` or `stop` must be specified."
  else if !hasstep && !haslength then "At least one of `length` or `step` must be specified."
  else if !hasstart && !hasstop then "At least one of `start` or `stop` must be specified."
  else "Try specifying more arguments."

/-- `range_error`, base/range.jl:243-270: always throws an ArgumentError. -/
def rangeError (start step stop len : Option Num) : Jl ResultRng :=
  .error (.argumentError (rangeErrorHint start step stop len))

/-- `range(...)` front ends (base/range.jl:167-173) and the sixteen `_range`
methods (base/range.jl:175-190); `none` is an argument left as `nothing`.
`range_length`/`range_stop(::Integer)` build `OneTo` (base/range.jl:193,197).
The result is `none` only for start/stop/length (base/range.jl:186), whose
integer arguments produce floating-point elements outside this model. -/
def rangeKw : Option Num → Option Num → Option Num → Option Num → Option (Jl ResultRng)
  | none, none, none, some n => some (.ordinal <$> oneTo n)
  | none, none, some b, none => some (.ordinal <$> oneTo b)
  | none, none, some b, some n => some (rangeStopLength b n)
  | none, some s, some b, some n => some (rangeStepStopLength s b n)
  | some a, none, none, some n => some (rangeStartLength a n)
  | some a, none, some b, none => some (.ordinal <$> colon2 a b)
  | some _, none, some _, some _ => none
  | some a, some s, none, some n => some (rangeStartStepLength a s n)
  | some a, some s, some b, none => some (.ordinal <$> colon3 a s b)
  | a, s, b, n => some (rangeError a s b n)

/-- `mod(i, r)` and `mod1` dispatch, base/range.jl:1548-1549,
base/operators.jl:914, base/promotion.jl:522. -/
def modRange (i : Num) (r : Rng) : Jl Num := do
  if r.kind = .oneTo then
    let ty := Num.promote i.ty (last r).ty
    let i ← Num.cast ty i
    let stop ← Num.cast ty (last r)
    let m ← Num.mod i stop
    pure (if m.val = 0 then stop else m)
  else
    let n ← length r
    let m ← Num.mod (Num.sub i (first r)) n
    pure (Num.add m (first r))

/-- `base/range.jl:537-550`: the integer-only inner constructor, including exact length/offset conversions. -/
def countedNewTyped (elementTy lengthTy : NType) (ref stride len offset : Num) : Jl RngLen := do
  let n ← Num.cast lengthTy len
  if n.val < 0 then throw (.argumentError "length cannot be negative")
  let o ← Num.cast lengthTy offset
  if o.val < 1 ∨ o.val > max 1 n.val then
    throw (.argumentError "StepRangeLen: offset must be in range")
  return ⟨ref, stride, n, o, elementTy⟩

/-- `base/range.jl:554-561`: `StepRangeLen{T}` promotes the length type with Int. -/
def countedNew (elementTy : NType) (ref stride len : Num)
    (offset : Num := Num.lit (.bit .i64) 1) : Jl RngLen :=
  countedNewTyped elementTy (Num.promote (.bit .i64) len.ty) ref stride len offset

/-- `base/range.jl:1095-1098`: high-precision indexing retains the reference and step types. -/
def countedHiprec (r : RngLen) (i : Num) : Jl Num := do
  let i ← Num.cast r.offset.ty i
  return Num.add r.ref (Num.mul (Num.sub i r.offset) r.stride)

/-- `base/range.jl:981-984`: conversion to the element type occurs after the arithmetic. -/
def countedUnsafeGetindex (r : RngLen) (i : Num) : Jl Num := do
  Num.cast r.elementTy (← countedHiprec r i)

/-- `base/range.jl:869`: first indexes at the literal Int 1, even for an empty range. -/
def countedFirst (r : RngLen) : Jl Num :=
  countedUnsafeGetindex r (Num.lit (.bit .i64) 1)

/-- `base/range.jl:878`: last indexes at the stored length, including zero. -/
def countedLast (r : RngLen) : Jl Num := countedUnsafeGetindex r r.len

/-- `base/range.jl:738`: the integer element specialization returns the stored step. -/
def countedStep (r : RngLen) : Num := r.stride

/-- `base/range.jl:712`: emptiness tests length, independently of endpoint overflow. -/
def countedIsEmpty (r : RngLen) : Bool := decide (r.len.val = 0)

/-- `base/checked.jl:376`, `base/range.jl:807`: checked length uses the stored-length fallback. -/
def countedCheckedLength (r : RngLen) : Jl Num := .ok r.len

/-- `base/range.jl:928-933`: iteration increments its integer state before testing length. -/
def countedIterate (r : RngLen) (state : Option Num := none) : Jl (Option (Num × Num)) := do
  let i := state.getD (Num.zero r.len.ty)
  let i := Num.add i (Num.one i.ty)
  if r.len.val < i.val then return none
  return some (← countedUnsafeGetindex r i, i)

/-- `base/range.jl:1436-1442`: reverse preserves all four type parameters. -/
def countedReverse (r : RngLen) : Jl RngLen := do
  let offset := if countedIsEmpty r then r.offset
    else Num.add (Num.sub r.len r.offset) (Num.lit (.bit .i64) 1)
  let stride ← Num.negate r.stride
  if stride.ty ≠ r.stride.ty then throw (.methodError "StepRangeLen")
  countedNewTyped r.elementTy r.len.ty r.ref stride r.len offset


/-- `base/range.jl:881-884`: extrema inspect endpoints, with the empty check first. -/
def countedMinimum (r : RngLen) : Jl Num := do
  if countedIsEmpty r then throw (.argumentError "range must be non-empty")
  let a ← countedFirst r
  let b ← countedLast r
  return Num.min a b

/-- `base/range.jl:881-884`: maximum uses endpoint max after the empty check. -/
def countedMaximum (r : RngLen) : Jl Num := do
  if countedIsEmpty r then throw (.argumentError "range must be non-empty")
  let a ← countedFirst r
  let b ← countedLast r
  return Num.max a b

/-- `base/range.jl:920`: evaluate minimum before maximum. -/
def countedExtrema (r : RngLen) : Jl (Num × Num) := do
  let a ← countedMinimum r
  let b ← countedMaximum r
  return (a, b)

/-- `base/range.jl:1481-1484`: integer-element membership retains both separate mod calls. -/
def countedContains (r : RngLen) (x : Num) : Jl Bool := do
  if countedIsEmpty r then return false
  if r.stride.val = 0 then return Num.eq x (← countedFirst r)
  let lo ← countedMinimum r
  if x.val < lo.val then return false
  let hi ← countedMaximum r
  if x.val > hi.val then return false
  let x ← Num.cast r.elementTy x
  let a ← Num.mod x r.stride
  let b ← Num.mod (← countedFirst r) r.stride
  return decide ((Num.sub a b).val = 0)

/-- `base/range.jl:1458-1463`, `base/int.jl:610-620`: arithmetic right shift by one. -/
def countedHalf (x : Num) : Num := Num.lit x.ty (x.val / 2)

/-- `base/range.jl:1458-1463`: arithmetic-series sum, retaining parity and product order. -/
def countedSum (r : RngLen) : Jl Num := do
  let l := r.len
  let a ← countedFirst r
  let lm1 := Num.sub l (Num.lit (.bit .i64) 1)
  let tail := if l.val % 2 = 0 then
      Num.mul (Num.mul r.stride lm1) (countedHalf l)
    else Num.mul (Num.mul r.stride l) (countedHalf lm1)
  return Num.add (Num.mul l a) tail

/-- `base/abstractarray.jl:756-757`, `base/multidimensional.jl:910-917`: logical masks check length; ordinary ranges check endpoints. -/
def countedSliceBounds (r : RngLen) (s : Rng) : Jl Bool := do
  if (first s).ty = .bool then
    return Num.eq (← length s) r.len
  if isEmpty s then return true
  return decide (1 ≤ (first s).val ∧ (first s).val ≤ r.len.val ∧
    1 ≤ (last s).val ∧ (last s).val ≤ r.len.val)

/-- `base/range.jl:1158-1159`: all four parameters determine identical counted range types. -/
def countedSameType (r s : RngLen) : Bool :=
  decide (r.elementTy = s.elementTy ∧ r.ref.ty = s.ref.ty ∧
    r.stride.ty = s.stride.ty ∧ r.len.ty = s.len.ty)

/-- `base/range.jl:1158-1159`: same-type counted equality eagerly compares first, length, and last. -/
def countedSameTypeEq (r s : RngLen) : Jl Bool := do
  let empty := countedIsEmpty r && countedIsEmpty s
  let rf ← countedFirst r
  let sf ← countedFirst s
  let rl ← countedLast r
  let sl ← countedLast s
  return empty || (Num.eq rf sf && Num.eq r.len s.len && Num.eq rl sl)

/-- `base/range.jl:1161-1165`: the same-element/reference specialization short-circuits empty and singleton ranges. -/
def countedExactEq (r s : RngLen) : Jl Bool := do
  if countedIsEmpty r then return countedIsEmpty s
  if r.len.val = 1 then
    let a ← countedFirst r
    let b ← countedFirst s
    return decide (s.len.val = 1) && Num.eq a b
  let a ← countedFirst r
  let b ← countedFirst s
  let c ← countedLast r
  let d ← countedLast s
  return Num.eq a b && Num.eq r.stride s.stride && Num.eq c d

/-- `base/range.jl:1161-1165`: the StepRange/StepRangeLen{T,T} specialization, in either argument order. -/
def countedOrdinalExactEq (r : RngLen) (s : Rng) (countedLeft : Bool) : Jl Bool := do
  if countedLeft then
    if countedIsEmpty r then return isEmpty s
    if r.len.val = 1 then return Num.eq (first s) (last s) && Num.eq (← countedFirst r) (first s)
  else
    if isEmpty s then return countedIsEmpty r
    if Num.eq (first s) (last s) then return decide (r.len.val = 1) && Num.eq (first s) (← countedFirst r)
  let a ← countedFirst r
  let b ← countedLast r
  return Num.eq a (first s) && Num.eq r.stride (step s) && Num.eq b (last s)

/-- `base/range.jl:928-942`: generic equality observes both yielded element and Julia iteration state. -/
def countedResultIterate (r : ResultRng) (state : Option Num := none) : Jl (Option (Num × Num)) := do
  match r with
  | .counted r => countedIterate r state
  | .ordinal r =>
    let next ← iterate r state
    return next.map (fun x => (x, x))

/-- `base/range.jl:1178-1183`: finite evaluations of the generic equality loop.
An inductive execution relation preserves wrapping iteration states without an artificial fuel cutoff. -/
inductive CountedEqLoop (r s : ResultRng) :
    Jl (Option (Num × Num)) → Jl (Option (Num × Num)) → Jl Bool → Prop where
  | leftError (e) (ys) : CountedEqLoop r s (.error e) ys (.error e)
  | rightError (yr) (e) : CountedEqLoop r s (.ok yr) (.error e) (.error e)
  | stop (ys) : CountedEqLoop r s (.ok none) (.ok ys) (.ok true)
  | rightAbsent (x : Num × Num) :
      CountedEqLoop r s (.ok (some x)) (.ok none) (.error (.methodError "getindex"))
  | mismatch (x y : Num × Num) (h : Num.eq x.1 y.1 = false) :
      CountedEqLoop r s (.ok (some x)) (.ok (some y)) (.ok false)
  | next (x y : Num × Num) (out) (h : Num.eq x.1 y.1 = true)
      (tail : CountedEqLoop r s (countedResultIterate r (some x.2))
        (countedResultIterate s (some y.2)) out) :
      CountedEqLoop r s (.ok (some x)) (.ok (some y)) out

/-- `base/range.jl:1170-1184`: generic equality compares lengths before entering iteration. -/
def countedGenericEq (r s : ResultRng) (out : Jl Bool) : Prop :=
  match resultLength r, resultLength s with
  | .error e, _ => out = .error e
  | .ok _, .error e => out = .error e
  | .ok lr, .ok ls =>
    if !Num.eq lr ls then out = .ok false
    else if lr.val = 0 then out = .ok true
    else CountedEqLoop r s (countedResultIterate r) (countedResultIterate s) out

/-- `base/range.jl:1158-1184`: counted/counted equality dispatch. -/
def countedEq (r s : RngLen) (out : Jl Bool) : Prop :=
  if r.elementTy = s.elementTy ∧ r.ref.ty = r.elementTy ∧ s.ref.ty = s.elementTy then
    out = countedExactEq r s
  else if countedSameType r s then out = countedSameTypeEq r s
  else countedGenericEq (.counted r) (.counted s) out

/-- `base/range.jl:1161-1184`: counted/ordinal equality dispatch, including argument order. -/
def countedOrdinalEq (r : RngLen) (s : Rng) (out : Jl Bool)
    (countedLeft : Bool := true) : Prop :=
  if s.kind = .step ∧ r.elementTy = (first s).ty ∧ r.ref.ty = r.elementTy then
    out = countedOrdinalExactEq r s countedLeft
  else if countedLeft then countedGenericEq (.counted r) (.ordinal s) out
  else countedGenericEq (.ordinal s) (.counted r) out

end JuliaLean.Ranges

namespace JuliaLean.AbstractArraySpecs

/-- An `AbstractRange{Int}` whose elements are `first + k * step` for `k < len`
(`UnitRange`, `StepRange`, `OneTo`, `StepRangeLen` with `Int` step). -/
structure Rg where
  first : I64
  step : I64
  len : Nat
  deriving DecidableEq, Repr

/-- The `k`-th element (0-based). -/
def Rg.at (r : Rg) (k : Nat) : I64 := i64 (r.first.val + (k : Int) * r.step.val)

/-- The elements from the `k`-th on, `m` of them. -/
def Rg.elemsFrom (r : Rg) : Nat → Nat → List I64
  | _, 0 => []
  | k, m + 1 => r.at k :: r.elemsFrom (k + 1) m

/-- The elements in iteration order. -/
def Rg.elems (r : Rg) : List I64 := r.elemsFrom 0 r.len

end JuliaLean.AbstractArraySpecs

namespace JuliaLean.Tuples

/-- `unitrange_last(start, stop)`, `base/range.jl:439-441`: `stop` when `stop >= start`,
else `start - 1` (wrapping). -/
def unitrangeLast {t : IntTy} (start stop : JInt t) : JInt t :=
  if stop.val ≥ start.val then stop else start - JInt.lit t 1

/-- `start:stop` for `BitInteger`s (`(:)(a::Real, b::Real) = (:)(promote(a, b)...)` and
`UnitRange{T}(start, stop)`, `base/range.jl:3,5,428`), then `convert(OrdinalRangeInt, r)`
in `CartesianIndices` (`base/multidimensional.jl:299-301`, `base/range.jl:1341`): the
`Int` endpoints `(first, last)`. -/
def unitRangeInt {s t : IntTy} (a : JInt s) (b : JInt t) : R (Int × Int) := do
  let p ← promoteInts a b
  let f ← liftJ (JInt.convert (IntTy.i64.name) .i64 p.1.val)
  let l ← liftJ (JInt.convert (IntTy.i64.name) .i64 (unitrangeLast p.1 p.2).val)
  pure (f.val, l.val)

/-- `length(r::UnitRange{Int})`, `base/range.jl:820-833`: `0` when empty, else
`(last -% first) + 1`. -/
def rangeLength (r : Int × Int) : Int :=
  if r.1 > r.2 then 0 else (JInt.wrap .i64 (r.2 - r.1 + 1)).val

end JuliaLean.Tuples

namespace JuliaLean.ArrayOps

open JuliaLean

/-- `length(r::UnitRange{T})` for a nonempty range, `base/range.jl:794-804, 859`:
`Int(last) - Int(first) + 1` for types narrower than `Int`, else
`last - first + 1` in `T`, wrapping. The result type is `Int` or `T`. -/
def unitLengthTy (t : IntTy) : IntTy := if t.bits ≤ 32 then .i64 else t

def unitLength {t : IntTy} (lo hi : JInt t) : JInt (unitLengthTy t) :=
  JInt.wrap _ (hi.val - lo.val + 1)

end JuliaLean.ArrayOps

namespace JuliaLean.ArrayOps

open JuliaLean

variable {α β : Type}

/-- The elements of `lo:hi` (`UnitRange{Int}`, `hi ≥ lo - 1`). -/
def unitElems (lo hi : JInt64) : List JInt64 :=
  (List.range (hi.val - lo.val + 1).toNat).map fun (k : Nat) => JInt.wrap .i64 (lo.val + (k : Int))

/-- `vcat(rs::AbstractRange{T}...)` for unit ranges of `Int`, `base/range.jl:1405-1417`:
`n = checked_add(n, length(ra))` over the ranges (`length` wraps, `base/range.jl:794-804`),
then every element is stored. Elements are only stored while `i ≤ n`; the model reports
`BoundsError` if an element would land past `n` (Julia stores it with `@inbounds`). -/
def vcatRanges (rs : List (JInt64 × JInt64)) : Jl (List JInt64) := do
  let n ← rs.foldlM (fun n r => checkedAdd64 n (JInt.wrap .i64 (r.2.val - r.1.val + 1)))
    (JInt.lit .i64 0)
  let elems := rs.flatMap fun r => unitElems r.1 r.2
  if elems.length ≤ n.val then pure elems else throw .boundsError

end JuliaLean.ArrayOps

namespace JuliaLean.Dicts

open JuliaLean.Float

/-- `StepRangeLen{Float64,Float64,Float64}(ref, step, len, offset)`. -/
structure SRL where
  ref : F64
  step : F64
  len : Nat
  offset : Int

/-- `unsafe_getindex(r::StepRangeLen{T}, i)`, `base/range.jl:986-989`:
`u = i - r.offset; convert(T, r.ref + u*r.step)`, with `Int * Float64`
promoting `u` exactly (`|u| < 2^53` here). -/
def SRL.elem (r : SRL) (i : Nat) : F64 :=
  F64.add r.ref (F64.mul (F64.ofInt ((i : Int) - r.offset)) r.step)

/-- `collect(r)`: elements `1:length(r)`. -/
def SRL.collect (r : SRL) : List F64 := (List.range r.len).map fun i => r.elem (i + 1)

end JuliaLean.Dicts

namespace JuliaLean.ReduceCov.Indices

/-- `el_same(T, a, b)`, `base/range.jl:1321-1324`: `a` when `eltype(a) == T`, `b` when
`eltype(b) == T`, otherwise `promote_typejoin(a, b)`. -/
def elSame (T : ElT) (a b : WT) : WT :=
  if a.eltype = T then a else if b.eltype = T then b else WT.typejoin a b

end JuliaLean.ReduceCov.Indices
