import JuliaLean.Core

/-!
# Model of `base/rounding.jl`

Typed models of the concrete methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
The mode and environment values are explicit so the generic methods and calls into native code
remain typed. Methods implemented by other Base files are parameters at their call sites.
-/

namespace JuliaLean.base.rounding

open JuliaLean

/-! ## Rounding modes -/

/-- The mode tags used by `RoundingMode{T}`. `Other` represents an extension tag. -/
inductive ModeTag where
  | Nearest | ToZero | Up | Down | FromZero | NearestTiesAway | NearestTiesUp
  | Other (name : String)
  deriving Repr, DecidableEq

/-- A value of Julia's `RoundingMode{T}`. -/
structure RoundingMode where
  tag : ModeTag
  deriving Repr, DecidableEq

/-!
Julia source: base/rounding.jl:26-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundingMode

A type used for controlling the rounding mode of floating point operations (via
[`rounding`](@ref)/[`setrounding`](@ref) functions), or as
optional arguments for rounding to the nearest integer (via the [`round`](@ref)
function).

Currently supported rounding modes are:

- [`RoundNearest`](@ref) (default)
- [`RoundNearestTiesAway`](@ref)
- [`RoundNearestTiesUp`](@ref)
- [`RoundToZero`](@ref)
- [`RoundFromZero`](@ref)
- [`RoundUp`](@ref)
- [`RoundDown`](@ref)

!!! compat "Julia 1.9"
    `RoundFromZero` requires at least Julia 1.9. Prior versions support
    `RoundFromZero` for `BigFloat`s only.
"""
struct RoundingMode{T} end
```
-/

/-!
Julia source: base/rounding.jl:50-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundNearest

The default rounding mode. Rounds to the nearest integer, with ties (fractional values of
0.5) being rounded to the nearest even integer.
"""
const RoundNearest = RoundingMode{:Nearest}()
```
-/
def RoundNearest : RoundingMode := ⟨.Nearest⟩

/-!
Julia source: base/rounding.jl:58-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundToZero

[`round`](@ref) using this rounding mode is an alias for [`trunc`](@ref).
"""
const RoundToZero = RoundingMode{:ToZero}()
```
-/
def RoundToZero : RoundingMode := ⟨.ToZero⟩

/-!
Julia source: base/rounding.jl:65-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundUp

[`round`](@ref) using this rounding mode is an alias for [`ceil`](@ref).
"""
const RoundUp = RoundingMode{:Up}()
```
-/
def RoundUp : RoundingMode := ⟨.Up⟩

/-!
Julia source: base/rounding.jl:72-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundDown

[`round`](@ref) using this rounding mode is an alias for [`floor`](@ref).
"""
const RoundDown = RoundingMode{:Down}()
```
-/
def RoundDown : RoundingMode := ⟨.Down⟩

/-!
Julia source: base/rounding.jl:79-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    RoundFromZero

Rounds away from zero.

!!! compat "Julia 1.9"
    `RoundFromZero` requires at least Julia 1.9. Prior versions support
    `RoundFromZero` for `BigFloat`s only.

# Examples
```jldoctest
julia> BigFloat("1.0000000000000001", 5, RoundFromZero)
1.06
```
"""
const RoundFromZero = RoundingMode{:FromZero}()
````
-/
def RoundFromZero : RoundingMode := ⟨.FromZero⟩

/-!
Julia source: base/rounding.jl:96-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundNearestTiesAway

Rounds to nearest integer, with ties rounded away from zero (C/C++
[`round`](@ref) behaviour).
"""
const RoundNearestTiesAway = RoundingMode{:NearestTiesAway}()
```
-/
def RoundNearestTiesAway : RoundingMode := ⟨.NearestTiesAway⟩

/-!
Julia source: base/rounding.jl:104-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    RoundNearestTiesUp

Rounds to nearest integer, with ties rounded toward positive infinity (Java/JavaScript
[`round`](@ref) behaviour).
"""
const RoundNearestTiesUp = RoundingMode{:NearestTiesUp}()
```
-/
def RoundNearestTiesUp : RoundingMode := ⟨.NearestTiesUp⟩

/-! ## Rounding mode predicates -/

/-!
Julia source: base/rounding.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(::RoundingMode) = false
```
-/
def roundsToNearestDefault (_mode : RoundingMode) : Bool := false

/-!
Julia source: base/rounding.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(::RoundingMode{:Nearest}) = true
```
-/
def roundsToNearestNearest : Bool := true

/-!
Julia source: base/rounding.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(::RoundingMode{:NearestTiesUp}) = true
```
-/
def roundsToNearestTiesUp : Bool := true

/-!
Julia source: base/rounding.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(::RoundingMode{:NearestTiesAway}) = true
```
-/
def roundsToNearestTiesAway : Bool := true

/-- *dispatch*: Select the `rounds_to_nearest` method for a mode tag. -/
def roundsToNearest (mode : RoundingMode) : Bool :=
  match mode.tag with
  | .Nearest => roundsToNearestNearest
  | .NearestTiesUp => roundsToNearestTiesUp
  | .NearestTiesAway => roundsToNearestTiesAway
  | _ => roundsToNearestDefault mode

/-!
Julia source: base/rounding.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_away_from_zero(::RoundingMode{:Up},   sign_bit::Bool) = !sign_bit
```
-/
def roundsAwayFromZeroUp (signBit : Bool) : Bool := !signBit

/-!
Julia source: base/rounding.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_away_from_zero(::RoundingMode{:Down}, sign_bit::Bool) = sign_bit
```
-/
def roundsAwayFromZeroDown (signBit : Bool) : Bool := signBit

/-!
Julia source: base/rounding.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool) = true
```
-/
def roundsAwayFromZeroFromZero (_signBit : Bool) : Bool := true

/-!
Julia source: base/rounding.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_away_from_zero(::RoundingMode{:ToZero},   ::Bool) = false
```
-/
def roundsAwayFromZeroToZero (_signBit : Bool) : Bool := false

/-- *dispatch*: Select the `rounds_away_from_zero` method for a mode tag. -/
def roundsAwayFromZero (mode : RoundingMode) (signBit : Bool) : Jl Bool :=
  match mode.tag with
  | .Up => .ok (roundsAwayFromZeroUp signBit)
  | .Down => .ok (roundsAwayFromZeroDown signBit)
  | .FromZero => .ok (roundsAwayFromZeroFromZero signBit)
  | .ToZero => .ok (roundsAwayFromZeroToZero signBit)
  | _ => .error (.methodError "rounds_away_from_zero")

/-!
Julia source: base/rounding.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_is_to_even(::RoundingMode{:Nearest}) = true
```
-/
def tieBreakerIsToEvenNearest : Bool := true

/-!
Julia source: base/rounding.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp}) = false
```
-/
def tieBreakerIsToEvenTiesUp : Bool := false

/-!
Julia source: base/rounding.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway}) = false
```
-/
def tieBreakerIsToEvenTiesAway : Bool := false

/-- *dispatch*: Select the `tie_breaker_is_to_even` method for a mode tag. -/
def tieBreakerIsToEven (mode : RoundingMode) : Jl Bool :=
  match mode.tag with
  | .Nearest => .ok tieBreakerIsToEvenNearest
  | .NearestTiesUp => .ok tieBreakerIsToEvenTiesUp
  | .NearestTiesAway => .ok tieBreakerIsToEvenTiesAway
  | _ => .error (.methodError "tie_breaker_is_to_even")

/-!
Julia source: base/rounding.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, sign_bit::Bool) = !sign_bit
```
-/
def tieBreakerRoundsAwayTiesUp (signBit : Bool) : Bool := !signBit

/-!
Julia source: base/rounding.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway},       ::Bool) = true
```
-/
def tieBreakerRoundsAwayTiesAway (_signBit : Bool) : Bool := true

/-- *dispatch*: Select the `tie_breaker_rounds_away_from_zero` method for a mode tag. -/
def tieBreakerRoundsAway (mode : RoundingMode) (signBit : Bool) : Jl Bool :=
  match mode.tag with
  | .NearestTiesUp => .ok (tieBreakerRoundsAwayTiesUp signBit)
  | .NearestTiesAway => .ok (tieBreakerRoundsAwayTiesAway signBit)
  | _ => .error (.methodError "tie_breaker_rounds_away_from_zero")

/-!
Julia source: base/rounding.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(t::Tuple{Any,Bool}) = rounds_to_nearest(first(t))
```
-/
def roundsToNearestTuple {μ β : Type} (roundsToNearest : μ → β) (t : μ × Bool) : β :=
  roundsToNearest t.1

/-!
Julia source: base/rounding.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_away_from_zero(t::Tuple{Any,Bool}) = rounds_away_from_zero(t...)
```
-/
def roundsAwayFromZeroTuple {μ β : Type} (roundsAwayFromZero : μ → Bool → β) (t : μ × Bool) : β :=
  roundsAwayFromZero t.1 t.2

/-!
Julia source: base/rounding.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_is_to_even(t::Tuple{Any,Bool}) = tie_breaker_is_to_even(first(t))
```
-/
def tieBreakerIsToEvenTuple {μ β : Type} (tieBreakerIsToEven : μ → β) (t : μ × Bool) : β :=
  tieBreakerIsToEven t.1

/-!
Julia source: base/rounding.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tie_breaker_rounds_away_from_zero(t::Tuple{Any,Bool}) = tie_breaker_rounds_away_from_zero(t...)
```
-/
def tieBreakerRoundsAwayTuple {μ β : Type} (tieBreakerRoundsAway : μ → Bool → β)
    (t : μ × Bool) : β :=
  tieBreakerRoundsAway t.1 t.2

/-!
Julia source: base/rounding.jl:134-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FinalBit end
struct RoundBit end
struct StickyBit end
```
-/
inductive RoundingBit where
  | FinalBit | RoundBit | StickyBit
  deriving Repr, DecidableEq

/-!
Julia source: base/rounding.jl:138-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function correct_rounding_requires_increment(x, rounding_mode, sign_bit::Bool)
    r = (rounding_mode, sign_bit)
    f = let y = x
        (z::Union{FinalBit,RoundBit,StickyBit}) -> y(z)::Bool
    end
    if rounds_to_nearest(r)
        if f(RoundBit())
            if f(StickyBit())
                true
            else
                if tie_breaker_is_to_even(r)
                    f(FinalBit())
                else
                    tie_breaker_rounds_away_from_zero(r)::Bool
                end
            end
        else
            false
        end
    else
        if rounds_away_from_zero(r)
            if f(RoundBit())
                true
            else
                f(StickyBit())
            end
        else
            false
        end
    end::Bool
end
```
-/
def correctRoundingRequiresIncrement {α μ : Type}
    (roundsToNearest : μ → Jl Bool)
    (roundsAwayFromZero : μ → Bool → Jl Bool)
    (tieBreakerIsToEven : μ → Jl Bool)
    (tieBreakerRoundsAway : μ → Bool → Jl Bool)
    (bits : RoundingBit → α)
    (asBool : α → Jl Bool) (mode : μ) (signBit : Bool) : Jl Bool := do
  let r := (mode, signBit)
  let f := fun z : RoundingBit => asBool (bits z)
  if ← roundsToNearestTuple roundsToNearest r then
    if ← f .RoundBit then
      if ← f .StickyBit then
        pure true
      else if ← tieBreakerIsToEvenTuple tieBreakerIsToEven r then
        f .FinalBit
      else
        tieBreakerRoundsAwayTuple tieBreakerRoundsAway r
    else
      pure false
  else if ← roundsAwayFromZeroTuple roundsAwayFromZero r then
    if ← f .RoundBit then pure true else f .StickyBit
  else
    pure false

/-! ## Floating-point environment -/

/-!
Julia source: base/rounding.jl:5-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let fenv_consts = Array{Cint,1}(undef, 9)
    ccall(:jl_get_fenv_consts, Cvoid, (Ptr{Cint},), fenv_consts)
    global const JL_FE_INEXACT = fenv_consts[1]
    global const JL_FE_UNDERFLOW = fenv_consts[2]
    global const JL_FE_OVERFLOW = fenv_consts[3]
    global const JL_FE_DIVBYZERO = fenv_consts[4]
    global const JL_FE_INVALID = fenv_consts[5]

    global const JL_FE_TONEAREST = fenv_consts[6]
    global const JL_FE_UPWARD = fenv_consts[7]
    global const JL_FE_DOWNWARD = fenv_consts[8]
    global const JL_FE_TOWARDZERO = fenv_consts[9]
end
```
-/
structure FEnvCodes where
  inexact : Int
  underflow : Int
  overflow : Int
  divideByZero : Int
  invalid : Int
  toNearest : Int
  upward : Int
  downward : Int
  towardZero : Int
  deriving Repr, DecidableEq

/-- The raw C floating-point environment is supplied by the runtime. -/
structure FEnv where
  rounding : Int
  zeroSubnormals : Bool
  deriving Repr, DecidableEq

inductive FEnvFloatType where
  | Float32 | Float64
  deriving Repr, DecidableEq

/-!
Julia source: base/rounding.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_fenv(::RoundingMode{:Nearest}) = JL_FE_TONEAREST
```
-/
def toFenvNearest (codes : FEnvCodes) : Int := codes.toNearest

/-!
Julia source: base/rounding.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_fenv(::RoundingMode{:ToZero}) = JL_FE_TOWARDZERO
```
-/
def toFenvToZero (codes : FEnvCodes) : Int := codes.towardZero

/-!
Julia source: base/rounding.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_fenv(::RoundingMode{:Up}) = JL_FE_UPWARD
```
-/
def toFenvUp (codes : FEnvCodes) : Int := codes.upward

/-!
Julia source: base/rounding.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_fenv(::RoundingMode{:Down}) = JL_FE_DOWNWARD
```
-/
def toFenvDown (codes : FEnvCodes) : Int := codes.downward

/-- *dispatch*: Select the `to_fenv` method for a supported rounding mode. -/
def toFenv (codes : FEnvCodes) (mode : RoundingMode) : Jl Int :=
  match mode.tag with
  | .Nearest => .ok (toFenvNearest codes)
  | .ToZero => .ok (toFenvToZero codes)
  | .Up => .ok (toFenvUp codes)
  | .Down => .ok (toFenvDown codes)
  | _ => .error (.methodError "to_fenv")

/-!
Julia source: base/rounding.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function from_fenv(r::Integer)
    if r == JL_FE_TONEAREST
        return RoundNearest
    elseif r == JL_FE_DOWNWARD
        return RoundDown
    elseif r == JL_FE_UPWARD
        return RoundUp
    elseif r == JL_FE_TOWARDZERO
        return RoundToZero
    else
        throw(ArgumentError("invalid rounding mode code: $r"))
    end
end
```
-/
def fromFenv {I : Type} (codes : FEnvCodes) (equals : I → Int → Bool) (showInt : I → String)
    (r : I) : Jl RoundingMode :=
  if equals r codes.toNearest then .ok RoundNearest
  else if equals r codes.downward then .ok RoundDown
  else if equals r codes.upward then .ok RoundUp
  else if equals r codes.towardZero then .ok RoundToZero
  else .error (.argumentError ("invalid rounding mode code: " ++ showInt r))

/-!
Julia source: base/rounding.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setrounding(T::Type, mode)
```
-/
def setroundingDecl {T α : Type} (setMode : T → α → FEnv → Jl FEnv)
    (target : T) (mode : α) (env : FEnv) : Jl FEnv :=
  setMode target mode env
/-!
Julia source: base/rounding.jl:219-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setrounding_raw(::Type{<:Union{Float32,Float64}}, i::Integer) = ccall(:jl_set_fenv_rounding, Int32, (Int32,), i)
```
-/
def setroundingRaw {I : Type} (asCInt : I → Int) (setNative : Int → FEnv → Int × FEnv)
    (_T : FEnvFloatType) (i : I) (env : FEnv) : Int × FEnv := setNative (asCInt i) env

/-!
Julia source: base/rounding.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounding_raw(::Type{<:Union{Float32,Float64}}) = ccall(:jl_get_fenv_rounding, Int32, ())
```
-/
def roundingRaw (getNative : FEnv → Int) (_T : FEnvFloatType) (env : FEnv) : Int := getNative env

/-!
Julia source: base/rounding.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounding(::Type{T}) where {T<:Union{Float32,Float64}} = from_fenv(rounding_raw(T))
```
-/
def rounding (codes : FEnvCodes) (equals : Int → Int → Bool) (showInt : Int → String)
    (getNative : FEnv → Int) (T : FEnvFloatType) (env : FEnv) : Jl RoundingMode :=
  fromFenv codes equals showInt (roundingRaw getNative T env)

/-!
Julia source: base/rounding.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounding(::Type{Union{}}, slurp...) = throw(MethodError(rounding, (Union{}, slurp...)))
```
-/
def roundingBottom {α : Type} (_slurp : List α) : Jl RoundingMode :=
  .error (.methodError "rounding")

/-!
Julia source: base/rounding.jl:238-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setrounding(f::Function, ::Type{T}, rounding::RoundingMode) where T
    old_rounding_raw = rounding_raw(T)
    setrounding(T,rounding)
    try
        return f()
    finally
        setrounding_raw(T,old_rounding_raw)
    end
end
```
-/
def setroundingScoped {T α : Type} (getNative : T → FEnv → Int)
    (setNative : T → Int → FEnv → Int × FEnv)
    (setMode : T → RoundingMode → FEnv → Jl FEnv)
    (f : FEnv → Jl α × FEnv) (target : T) (mode : RoundingMode) (env : FEnv) :
    Jl α × FEnv :=
  let oldMode := getNative target env
  match setMode target mode env with
  | .error err => (.error err, env)
  | .ok changed =>
    let (result, afterCall) := f changed
    let (_, restored) := setNative target oldMode afterCall
    (result, restored)

/-!
Julia source: base/rounding.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setrounding(f, ::Type{Union{}}, slurp...) = throw(MethodError(setrounding, (f, Union{}, slurp...)))
```
-/
def setroundingBottom {α β γ : Type} (_f : α) (_slurp : List β) : Jl γ :=
  .error (.methodError "setrounding")

/-!
Julia source: base/rounding.jl:248-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setrounding_raw(f::Function, ::Type{T}, rounding) where T
    old_rounding_raw = rounding_raw(T)
    setrounding_raw(T,rounding)
    try
        return f()
    finally
        setrounding_raw(T,old_rounding_raw)
    end
end
```
-/
def setroundingRawScoped {T I α : Type} (asCInt : I → Int)
    (getNative : T → FEnv → Int) (setNative : T → Int → FEnv → Int × FEnv)
    (f : FEnv → Jl α × FEnv) (target : T) (mode : I) (env : FEnv) : Jl α × FEnv :=
  let oldMode := getNative target env
  let (_, changed) := setNative target (asCInt mode) env
  let (result, afterCall) := f changed
  let (_, restored) := setNative target oldMode afterCall
  (result, restored)

/-- Operations called by the generic directed conversion methods. -/
structure ConvertRoundingOps (α β : Type) where
  convert : α → Jl β
  greater : β → α → Jl Bool
  less : β → α → Jl Bool
  positive : α → Jl Bool
  negative : α → Jl Bool
  prevfloat : β → β
  nextfloat : β → β


/-!
Julia source: base/rounding.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Nearest}) where {T<:AbstractFloat} = convert(T,x)::T
```
-/
def convertRoundingNearest {α β : Type} (ops : ConvertRoundingOps α β) (x : α) : Jl β :=
  ops.convert x

/-!
Julia source: base/rounding.jl:270-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Down}) where T<:AbstractFloat
    y = convert(T,x)::T
    y > x ? prevfloat(y) : y
end
```
-/
def convertRoundingDown {α β : Type} (ops : ConvertRoundingOps α β) (x : α) : Jl β := do
  let y ← ops.convert x
  if ← ops.greater y x then pure (ops.prevfloat y) else pure y

/-!
Julia source: base/rounding.jl:274-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Up}) where T<:AbstractFloat
    y = convert(T,x)::T
    y < x ? nextfloat(y) : y
end
```
-/
def convertRoundingUp {α β : Type} (ops : ConvertRoundingOps α β) (x : α) : Jl β := do
  let y ← ops.convert x
  if ← ops.less y x then pure (ops.nextfloat y) else pure y

/-!
Julia source: base/rounding.jl:278-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:ToZero}) where T<:AbstractFloat
    y = convert(T,x)::T
    if x > 0.0
        y > x ? prevfloat(y) : y
    else
        y < x ? nextfloat(y) : y
    end
end
```
-/
def convertRoundingToZero {α β : Type} (ops : ConvertRoundingOps α β) (x : α) : Jl β := do
  let y ← ops.convert x
  if ← ops.positive x then
    if ← ops.greater y x then pure (ops.prevfloat y) else pure y
  else if ← ops.less y x then
    pure (ops.nextfloat y)
  else
    pure y

/-!
Julia source: base/rounding.jl:286-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:FromZero}) where T<:AbstractFloat
    y = convert(T,x)::T
    if x < 0.0
        y > x ? prevfloat(y) : y
    else
        y < x ? nextfloat(y) : y
    end
end
```
-/
def convertRoundingFromZero {α β : Type} (ops : ConvertRoundingOps α β) (x : α) : Jl β := do
  let y ← ops.convert x
  if ← ops.negative x then
    if ← ops.greater y x then pure (ops.prevfloat y) else pure y
  else if ← ops.less y x then
    pure (ops.nextfloat y)
  else
    pure y

def convertRounding {α β : Type} (ops : ConvertRoundingOps α β) (mode : RoundingMode)
    (x : α) : Jl β :=
  match mode.tag with
  | .Nearest => convertRoundingNearest ops x
  | .Down => convertRoundingDown ops x
  | .Up => convertRoundingUp ops x
  | .ToZero => convertRoundingToZero ops x
  | .FromZero => convertRoundingFromZero ops x
  | _ => .error (.methodError "_convert_rounding")
/-!
Julia source: base/rounding.jl:259-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Should be equivalent to:
#   setrounding(Float64,r) do
#       convert(T,x)
#   end
# but explicit checks are currently quicker (~20x).
# Assumes conversion is performed by rounding to nearest value.

# To avoid ambiguous dispatch with methods in mpfr.jl:
(::Type{T})(x::Real, r::RoundingMode) where {T<:AbstractFloat} = _convert_rounding(T,x,r)::T
```
-/
def convertRoundingType {α β : Type} (ops : ConvertRoundingOps α β) (x : α)
    (mode : RoundingMode) : Jl β := convertRounding ops mode x

/-! ## Zeroing subnormals -/

/-!
Julia source: base/rounding.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
set_zero_subnormals(yes::Bool) = ccall(:jl_set_zero_subnormals,Int32,(Int8,),yes)==0
```
-/
def setZeroSubnormals (setNative : Bool → Int) (yes : Bool) : Bool := setNative yes == 0

/-!
Julia source: base/rounding.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_zero_subnormals() = ccall(:jl_get_zero_subnormals,Int32,())!=0
```
-/
def getZeroSubnormals (getNative : Unit → Int) : Bool := getNative () != 0

/-! ## Generic rounding declarations and forwarders -/

/-!
Julia source: base/rounding.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round end
```
-/

/-!
Julia source: base/rounding.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trunc end
```
-/

/-!
Julia source: base/rounding.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function floor end
```
-/

/-!
Julia source: base/rounding.jl:478-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ceil end
```
-/

/-!
Julia source: base/rounding.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trunc(x; kws...) = round(x, RoundToZero; kws...)
```
-/
def truncKeyword {α κ β : Type} (roundValue : α → RoundingMode → κ → β) (x : α) (kws : κ) : β :=
  roundValue x RoundToZero kws

/-!
Julia source: base/rounding.jl:481-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floor(x; kws...) = round(x, RoundDown; kws...)
```
-/
def floorKeyword {α κ β : Type} (roundValue : α → RoundingMode → κ → β) (x : α) (kws : κ) : β :=
  roundValue x RoundDown kws

/-!
Julia source: base/rounding.jl:482-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
 ceil(x; kws...) = round(x, RoundUp; kws...)
```
-/
def ceilKeyword {α κ β : Type} (roundValue : α → RoundingMode → κ → β) (x : α) (kws : κ) : β :=
  roundValue x RoundUp kws

/-!
Julia source: base/rounding.jl:483-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x; kws...) = round(x, RoundNearest; kws...)
```
-/
def roundKeyword {α κ β : Type} (roundValue : α → RoundingMode → κ → β) (x : α) (kws : κ) : β :=
  roundValue x RoundNearest kws
/-!
Julia source: base/rounding.jl:491-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_round_convert(::Type{T}, x_integer, x, r) where T = convert(T, x_integer)
```
-/
def roundConvert {τ β α : Type} (resultType : τ → Type)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (xInteger : β)
    (_x : α) (_mode : RoundingMode) : Jl (resultType T) := convert T xInteger

/-!
Julia source: base/rounding.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x, r::RoundingMode) where T = _round_convert(T, round(x, r), x, r)
```
-/
def roundTypeWithMode {τ α β : Type} (resultType : τ → Type)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (x : α)
    (mode : RoundingMode) : Jl (resultType T) := do
  let xInteger ← roundValue x mode
  roundConvert resultType convert T xInteger x mode
/-!
Julia source: base/rounding.jl:485-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trunc(::Type{T}, x) where T = round(T, x, RoundToZero)
```
-/
def truncType {τ α β : Type} (resultType : τ → Type)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (x : α) : Jl (resultType T) :=
  roundTypeWithMode resultType roundValue convert T x RoundToZero

/-!
Julia source: base/rounding.jl:486-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floor(::Type{T}, x) where T = round(T, x, RoundDown)
```
-/
def floorType {τ α β : Type} (resultType : τ → Type)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (x : α) : Jl (resultType T) :=
  roundTypeWithMode resultType roundValue convert T x RoundDown

/-!
Julia source: base/rounding.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
 ceil(::Type{T}, x) where T = round(T, x, RoundUp)
```
-/
def ceilType {τ α β : Type} (resultType : τ → Type)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (x : α) : Jl (resultType T) :=
  roundTypeWithMode resultType roundValue convert T x RoundUp

/-!
Julia source: base/rounding.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{T}, x) where T = round(T, x, RoundNearest)
```
-/
def roundType {τ α β : Type} (resultType : τ → Type)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) (T : τ) (x : α) : Jl (resultType T) :=
  roundTypeWithMode resultType roundValue convert T x RoundNearest



/-!
Julia source: base/rounding.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trunc(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(trunc, (Union{}, slurp...)))
```
-/
def truncBottom {α κ β : Type} (_slurp : List α) (_kwargs : κ) : Jl β :=
  .error (.methodError "trunc")

/-!
Julia source: base/rounding.jl:493-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
floor(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(floor, (Union{}, slurp...)))
```
-/
def floorBottom {α κ β : Type} (_slurp : List α) (_kwargs : κ) : Jl β :=
  .error (.methodError "floor")

/-!
Julia source: base/rounding.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
 ceil(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(ceil, (Union{}, slurp...)))
```
-/
def ceilBottom {α κ β : Type} (_slurp : List α) (_kwargs : κ) : Jl β :=
  .error (.methodError "ceil")

/-!
Julia source: base/rounding.jl:495-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(round, (Union{}, slurp...)))
```
-/
def roundBottom {α κ β : Type} (_slurp : List α) (_kwargs : κ) : Jl β :=
  .error (.methodError "round")

/-!
Julia source: base/rounding.jl:497-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::Integer, r::RoundingMode) = x
```
-/
def roundInteger {α : Type} (x : α) (_mode : RoundingMode) : α := x

end JuliaLean.base.rounding
