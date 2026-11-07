import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.promotion

/-!
# Model of `base/div.jl`

Typed source models of Julia's division and remainder methods. `JuliaLean.base.int` supplies the
same-type BitInteger division and remainder callees; the definitions below retain generic callees
for methods that dispatch across integer, floating-point, and user-defined numeric types.
-/

namespace JuliaLean.base.div

open JuliaLean
open JuliaLean.base.float

inductive DirectedMode where
  | ToZero | Down | Up
  deriving DecidableEq, Repr

inductive NearestMode where
  | Nearest | NearestTiesAway | NearestTiesUp
  deriving DecidableEq, Repr

inductive TiesMode where
  | NearestTiesAway | NearestTiesUp
  deriving DecidableEq, Repr

inductive BoolRoundingMode where
  | Up | Down | ToZero | FromZero
  deriving DecidableEq, Repr

abbrev DivJl (α β γ : Type) := α → β → Jl γ
abbrev DivRoundJl (α β γ : Type) := α → β → RoundingMode → Jl γ
abbrev DivremJl (α β γ δ : Type) := α → β → Jl (γ × δ)
abbrev DivremRoundJl (α β γ δ : Type) := α → β → RoundingMode → Jl (γ × δ)

/--
Julia source: base/div.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(a, b) = div(a, b, RoundToZero)
```
-/
def div_default {α β γ : Type} (divRound : DivRoundJl α β γ) (a : α) (b : β) : Jl γ :=
  divRound a b .ToZero

/--
Julia source: base/div.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x, y, ::RoundingMode{:ToZero}) = rem(x, y)
```
-/
def rem_ToZero {α β γ : Type} (rem : DivJl α β γ) (x : α) (y : β) : Jl γ := rem x y

/--
Julia source: base/div.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x, y, ::RoundingMode{:Down}) = mod(x, y)
```
-/
def rem_Down {α β γ : Type} (mod : DivJl α β γ) (x : α) (y : β) : Jl γ := mod x y

/--
Julia source: base/div.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x, y, ::RoundingMode{:Up}) = mod(x, -y)
```
-/
def rem_Up {α β γ : Type} (mod : DivJl α β γ) (neg : β → β) (x : α) (y : β) : Jl γ :=
  mod x (neg y)

/--
Julia source: base/div.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x, y, r::RoundingMode{:Nearest}) = x - y * div(x, y, r)
```
-/
def rem_Nearest {α β γ σ : Type} (divRound : DivRoundJl α β γ)
    (mul : β → γ → σ) (sub : α → σ → γ) (x : α) (y : β) : Jl γ := do
  let q ← divRound x y .Nearest
  pure (sub x (mul y q))

/--
Julia source: base/div.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, y::Integer, r::RoundingMode{:Nearest}) = divrem(x, y, r)[2]
```
-/
def rem_Integer_Nearest {α β γ δ : Type} (divrem : DivremRoundJl α β γ δ)
    (x : α) (y : β) : Jl δ := do
  let pair ← divrem x y .Nearest
  pure pair.2

/--
Julia source: base/div.jl:132-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::Integer, y::Integer, rnd::Union{typeof(RoundNearestTiesAway),
                                                typeof(RoundNearestTiesUp)})
    divrem(x, y, rnd)[2]
end
```
-/
def rem_Integer_Ties {α β γ δ : Type} (divrem : DivremRoundJl α β γ δ)
    (mode : TiesMode) (x : α) (y : β) : Jl δ := do
  let pair ← divrem x y (match mode with
    | .NearestTiesAway => .NearestTiesAway
    | .NearestTiesUp => .NearestTiesUp)
  pure pair.2

/--
Julia source: base/div.jl:136-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x, y, ::typeof(RoundFromZero))
    signbit(x) == signbit(y) ? rem(x, y, RoundUp) : rem(x, y, RoundDown)
end
```
-/
def rem_FromZero {α β γ : Type} (signbitX : α → Bool) (signbitY : β → Bool)
    (remRound : DivRoundJl α β γ) (x : α) (y : β) : Jl γ :=
  if signbitX x = signbitY y then remRound x y .Up else remRound x y .Down

/--
Julia source: base/div.jl:139-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::AbstractFloat, y::AbstractFloat, rnd::Union{typeof(RoundNearestTiesAway),
                                                            typeof(RoundNearestTiesUp)})
    r = mod(x, y)
    isnan(r) && return r
    if !iszero(r)
        m, n = abs(r) < floatmax(r)/2 ? abs.((2r, y)) : abs.((r, y/2))
        m < n && return r
        m > n && return mod(x, -y)
    end
    rnd === RoundNearestTiesUp || signbit(x) == signbit(y) ? mod(x, -y) : r
end
```
-/
def rem_AbstractFloat_Ties {α : Type} (mod : α → α → α) (isnan iszero : α → Bool)
    (lt : α → α → Bool) (floatmax abs : α → α) (two : α)
    (mul div : α → α → α) (neg : α → α) (signbit : α → Bool) (tiesUp : Bool)
    (x y : α) : α := Id.run do
  let r := mod x y
  if isnan r then return r
  if !iszero r then
    let (m, n) := if lt (abs r) (div (floatmax r) two)
      then (abs (mul two r), abs y)
      else (abs r, abs (div y two))
    if lt m n then return r
    if lt n m then return mod x (neg y)
  return if tiesUp || signbit x = signbit y then mod x (neg y) else r

/--
Julia source: base/div.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(a, b) = div(a, b, RoundDown)
```
-/
def fld {α β γ : Type} (divRound : DivRoundJl α β γ) (a : α) (b : β) : Jl γ :=
  divRound a b .Down

/--
Julia source: base/div.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(a, b) = div(a, b, RoundUp)
```
-/
def cld {α β γ : Type} (divRound : DivRoundJl α β γ) (a : α) (b : β) : Jl γ :=
  divRound a b .Up

/--
Julia source: base/div.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld1(a, b) = cld(a, b)
```
-/
def fld1 {α β γ : Type} (cld : DivJl α β γ) (a : α) (b : β) : Jl γ := cld a b

/--
Julia source: base/div.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
divrem(x, y) = divrem(x, y, RoundToZero)
```
-/
def divrem_default {α β γ δ : Type} (divremRound : DivremRoundJl α β γ δ)
    (x : α) (y : β) : Jl (γ × δ) := divremRound x y .ToZero

/--
Julia source: base/div.jl:276-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(a, b, r::RoundingMode)
    if r === RoundToZero
        # For compat. Remove in 2.0.
        (div(a, b), rem(a, b))
    elseif r === RoundDown
        # For compat. Remove in 2.0.
        (fld(a, b), mod(a, b))
    else
        (div(a, b, r), rem(a, b, r))
    end
end
```
-/
def divrem_RoundingMode {α β γ δ : Type}
    (div : DivJl α β γ) (rem : DivJl α β δ) (fld : DivJl α β γ) (mod : DivJl α β δ)
    (divRound : DivRoundJl α β γ) (remRound : DivRoundJl α β δ)
    (a : α) (b : β) (r : RoundingMode) : Jl (γ × δ) := do
  if r = .ToZero then
    let q ← div a b
    let remValue ← rem a b
    pure (q, remValue)
  else if r = .Down then
    let q ← fld a b
    let remValue ← mod a b
    pure (q, remValue)
  else
    let q ← divRound a b r
    let remValue ← remRound a b r
    pure (q, remValue)

/--
Julia source: base/div.jl:290-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(a::Integer, b::Integer, r::Union{typeof(RoundUp),
                                                typeof(RoundDown),
                                                typeof(RoundToZero)})
    if r === RoundToZero
        # For compat. Remove in 2.0.
        d = div(a, b)
        (d, a - d * b)
    elseif r === RoundDown
        # For compat. Remove in 2.0.
        d = fld(a, b)
        (d, a - d * b)
    elseif r === RoundUp
        # For compat. Remove in 2.0.
        d = div(a, b, r)
        (d, a - d * b)
    end
end
```
-/
def divrem_Integer_Directed {α β γ σ δ : Type}
    (div : DivJl α β γ) (fld : DivJl α β γ) (divRound : DivRoundJl α β γ)
    (mul : γ → β → σ) (sub : α → σ → δ)
    (a : α) (b : β) (r : DirectedMode) : Jl (γ × δ) := do
  if r = .ToZero then
    let d ← div a b
    pure (d, sub a (mul d b))
  else if r = .Down then
    let d ← fld a b
    pure (d, sub a (mul d b))
  else
    let d ← divRound a b .Up
    pure (d, sub a (mul d b))

/--
Julia source: base/div.jl:312-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(a::T, b::T, r::Union{typeof(RoundUp),
                                     typeof(RoundDown),
                                     typeof(RoundToZero)}) where T<:BitSigned
    if r === RoundToZero
        d = div(a, b)
        (d, a - d * b)
    elseif r === RoundDown
        d = fld(a, b)
        (d, a -% d *% b)
    elseif r === RoundUp
        d = div(a, b, r)
        (d, a -% d *% b)
    end
end
```
-/
def divrem_BitSigned_Directed {t : IntTy} (div : JInt t → JInt t → Jl (JInt t))
    (fld : JInt t → JInt t → Jl (JInt t))
    (divRound : JInt t → JInt t → RoundingMode → Jl (JInt t))
    (mul sub : JInt t → JInt t → JInt t) (a b : JInt t) (r : DirectedMode) :
    Jl (JInt t × JInt t) := do
  if r = .ToZero then
    let d ← div a b
    pure (d, sub a (mul d b))
  else if r = .Down then
    let d ← fld a b
    pure (d, sub a (mul d b))
  else
    let d ← divRound a b .Up
    pure (d, sub a (mul d b))

def boolInt (b : Bool) : Int := if b then 1 else 0

/--
Julia source: base/div.jl:326-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::Integer, y::Integer, rnd::typeof(RoundNearest))
    (q, r) = divrem(x, y)
    if x >= 0
        if y >= 0
            r >=        (y÷2) + (isodd(y) | iseven(q)) ? (q+true, r-y) : (q, r)
        else
            r >=       -(y÷2) + (isodd(y) | iseven(q)) ? (q-true, r+y) : (q, r)
        end
    else
        if y >= 0
            r <= -signed(y÷2) - (isodd(y) | iseven(q)) ? (q-true, r+y) : (q, r)
        else
            r <=        (y÷2) - (isodd(y) | iseven(q)) ? (q+true, r-y) : (q, r)
        end
    end
end
```
-/
def divrem_Integer_Nearest {α β γ δ : Type}
    (divrem : DivremJl α β γ δ) (xval : α → Int) (yval : β → Int)
    (rval : δ → Int) (half signedHalf : β → Int)
    (isoddY : β → Bool) (isevenQ : γ → Bool)
    (addQ subQ : γ → Bool → γ) (addR : δ → β → δ) (subR : δ → β → δ)
    (x : α) (y : β) : Jl (γ × δ) := do
  let (q, r) ← divrem x y
  let tie := isoddY y || isevenQ q
  if xval x ≥ 0 then
    if yval y ≥ 0 then
      if rval r ≥ half y + boolInt tie then pure (addQ q true, subR r y) else pure (q, r)
    else
      if rval r ≥ -(half y) + boolInt tie then pure (subQ q true, addR r y) else pure (q, r)
  else if yval y ≥ 0 then
    if rval r ≤ -signedHalf y - boolInt tie then pure (subQ q true, addR r y) else pure (q, r)
  else if rval r ≤ half y - boolInt tie then pure (addQ q true, subR r y)
  else pure (q, r)

/--
Julia source: base/div.jl:342-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::Integer, y::Integer, rnd:: typeof(RoundNearestTiesAway))
    (q, r) = divrem(x, y)
    if x >= 0
        if y >= 0
            r >=        (y÷2) + isodd(y) ? (q+true, r-y) : (q, r)
        else
            r >=       -(y÷2) + isodd(y) ? (q-true, r+y) : (q, r)
        end
    else
        if y >= 0
            r <= -signed(y÷2) - isodd(y) ? (q-true, r+y) : (q, r)
        else
            r <=        (y÷2) - isodd(y) ? (q+true, r-y) : (q, r)
        end
    end
end
```
-/
def divrem_Integer_NearestTiesAway {α β γ δ : Type}
    (divrem : DivremJl α β γ δ) (xval : α → Int) (yval : β → Int)
    (rval : δ → Int) (half signedHalf : β → Int) (isoddY : β → Bool)
    (addQ subQ : γ → Bool → γ) (addR : δ → β → δ) (subR : δ → β → δ)
    (x : α) (y : β) : Jl (γ × δ) := do
  let (q, r) ← divrem x y
  if xval x ≥ 0 then
    if yval y ≥ 0 then
      if rval r ≥ half y + boolInt (isoddY y) then pure (addQ q true, subR r y) else pure (q, r)
    else
      if rval r ≥ -(half y) + boolInt (isoddY y) then pure (subQ q true, addR r y) else pure (q, r)
  else if yval y ≥ 0 then
    if rval r ≤ -signedHalf y - boolInt (isoddY y) then pure (subQ q true, addR r y) else pure (q, r)
  else if rval r ≤ half y - boolInt (isoddY y) then pure (addQ q true, subR r y)
  else pure (q, r)

/--
Julia source: base/div.jl:358-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::Integer, y::Integer, rnd::typeof(RoundNearestTiesUp))
    (q, r) = divrem(x, y)
    if x >= 0
        if y >= 0
            r >=        (y÷2) + isodd(y) ? (q+true, r-y) : (q, r)
        else
            r >=       -(y÷2) + true     ? (q-true, r+y) : (q, r)
        end
    else
        if y >= 0
            r <= -signed(y÷2) - true     ? (q-true, r+y) : (q, r)
        else
            r <=        (y÷2) - isodd(y) ? (q+true, r-y) : (q, r)
        end
    end
end
```
-/
def divrem_Integer_NearestTiesUp {α β γ δ : Type}
    (divrem : DivremJl α β γ δ) (xval : α → Int) (yval : β → Int)
    (rval : δ → Int) (half signedHalf : β → Int) (isoddY : β → Bool)
    (addQ subQ : γ → Bool → γ) (addR : δ → β → δ) (subR : δ → β → δ)
    (x : α) (y : β) : Jl (γ × δ) := do
  let (q, r) ← divrem x y
  if xval x ≥ 0 then
    if yval y ≥ 0 then
      if rval r ≥ half y + boolInt (isoddY y) then pure (addQ q true, subR r y) else pure (q, r)
    else
      if rval r ≥ -(half y) + 1 then pure (subQ q true, addR r y) else pure (q, r)
  else if yval y ≥ 0 then
    if rval r ≤ -signedHalf y - 1 then pure (subQ q true, addR r y) else pure (q, r)
  else if rval r ≤ half y - boolInt (isoddY y) then pure (addQ q true, subR r y)
  else pure (q, r)

/--
Julia source: base/div.jl:375-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x, y, ::typeof(RoundFromZero))
    signbit(x) == signbit(y) ? divrem(x, y, RoundUp) : divrem(x, y, RoundDown)
end
```
-/
def divrem_FromZero {α β γ δ : Type} (signbitX : α → Bool) (signbitY : β → Bool)
    (divremRound : DivremRoundJl α β γ δ) (x : α) (y : β) : Jl (γ × δ) :=
  if signbitX x = signbitY y then divremRound x y .Up else divremRound x y .Down

/--
Julia source: base/div.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fldmod(x, y) = divrem(x, y, RoundDown)
```
-/
def fldmod {α β γ δ : Type} (divremRound : DivremRoundJl α β γ δ)
    (x : α) (y : β) : Jl (γ × δ) := divremRound x y .Down

/--
Julia source: base/div.jl:391-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Signed, y::Unsigned, ::typeof(RoundDown))
    (q, r) = divrem(x, y)
    q - (signbit(x) & (r != 0))
end
```
-/
def div_Signed_Unsigned_Down {α β γ δ : Type} (divrem : DivremJl α β γ δ)
    (signbit : α → Bool) (rzero : δ → Bool) (subBool : γ → Bool → γ)
    (x : α) (y : β) : Jl γ := do
  let (q, r) ← divrem x y
  pure (subBool q (signbit x && !rzero r))

/--
Julia source: base/div.jl:395-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Unsigned, y::Signed, ::typeof(RoundDown))
    (q, r) = divrem(x, y)
    q - (signbit(y) & (r != 0))
end
```
-/
def div_Unsigned_Signed_Down {α β γ δ : Type} (divrem : DivremJl α β γ δ)
    (signbit : β → Bool) (rzero : δ → Bool) (subBool : γ → Bool → γ)
    (x : α) (y : β) : Jl γ := do
  let (q, r) ← divrem x y
  pure (subBool q (signbit y && !rzero r))

/--
Julia source: base/div.jl:400-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Signed, y::Unsigned, ::typeof(RoundUp))
    (q, r) = divrem(x, y)
    q + (!signbit(x) & (r != 0))
end
```
-/
def div_Signed_Unsigned_Up {α β γ δ : Type} (divrem : DivremJl α β γ δ)
    (signbit : α → Bool) (rzero : δ → Bool) (addBool : γ → Bool → γ)
    (x : α) (y : β) : Jl γ := do
  let (q, r) ← divrem x y
  pure (addBool q (!signbit x && !rzero r))

/--
Julia source: base/div.jl:404-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Unsigned, y::Signed, ::typeof(RoundUp))
    (q, r) = divrem(x, y)
    q + (!signbit(y) & (r != 0))
end
```
-/
def div_Unsigned_Signed_Up {α β γ δ : Type} (divrem : DivremJl α β γ δ)
    (signbit : β → Bool) (rzero : δ → Bool) (addBool : γ → Bool → γ)
    (x : α) (y : β) : Jl γ := do
  let (q, r) ← divrem x y
  pure (addBool q (!signbit y && !rzero r))

/--
Julia source: base/div.jl:409-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Integer, y::Integer, rnd::Union{typeof(RoundNearest),
                                              typeof(RoundNearestTiesAway),
                                              typeof(RoundNearestTiesUp)})
    divrem(x, y, rnd)[1]
end
```
-/
def div_Integer_Nearest {α β γ δ : Type} (divrem : DivremRoundJl α β γ δ)
    (mode : NearestMode) (x : α) (y : β) : Jl γ := do
  let pair ← divrem x y (match mode with
    | .Nearest => .Nearest
    | .NearestTiesAway => .NearestTiesAway
    | .NearestTiesUp => .NearestTiesUp)
  pure pair.1

/--
Julia source: base/div.jl:415-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Integer, y::Integer, ::typeof(RoundFromZero))
    signbit(x) == signbit(y) ? div(x, y, RoundUp) : div(x, y, RoundDown)
end
```
-/
def div_Integer_FromZero {α β γ : Type} (signbitX : α → Bool) (signbitY : β → Bool)
    (divRound : DivRoundJl α β γ) (x : α) (y : β) : Jl γ :=
  if signbitX x = signbitY y then divRound x y .Up else divRound x y .Down

/--
Julia source: base/div.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(a::T, b::T, ::typeof(RoundToZero)) where {T<:Union{BitSigned, BitUnsigned}} = div(a, b)
```
-/
def div_BitInteger_ToZero {t : IntTy} (div : JInt t → JInt t → Jl (JInt t))
    (a : JInt t) (b : JInt t) : Jl (JInt t) := div a b

/--
Julia source: base/div.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(a::Bool, b::Bool, r::RoundingMode) = div(a, b)
```
-/
def div_Bool_RoundingMode (div : Bool → Bool → Jl Bool) (a b : Bool)
    (_r : RoundingMode) : Jl Bool := div a b

/--
Julia source: base/div.jl:424-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for rm in (RoundUp, RoundDown, RoundToZero, RoundFromZero)
    @eval div(a::Bool, b::Bool, r::$(typeof(rm))) = div(a, b)
end
```
-/
def div_Bool_Generated (div : Bool → Bool → Jl Bool) (a b : Bool)
    (_r : BoolRoundingMode) : Jl Bool := div a b

/--
Julia source: base/div.jl:427-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Bool, y::Bool, rnd::Union{typeof(RoundNearest),
                                        typeof(RoundNearestTiesAway),
                                        typeof(RoundNearestTiesUp)})
    div(x, y)
end
```
-/
def div_Bool_Nearest (div : Bool → Bool → Jl Bool) (x y : Bool)
    (_r : NearestMode) : Jl Bool := div x y

/--
Julia source: base/div.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(a::T, b::T) where {T<:Union{Integer,AbstractFloat}} = div(a, b, RoundDown)
```
-/
def fld_same_numeric {α γ : Type} (divRound : DivRoundJl α α γ) (a b : α) : Jl γ :=
  divRound a b .Down

/--
Julia source: base/div.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(a::T, b::T) where {T<:Union{Integer,AbstractFloat}} = div(a, b, RoundUp)
```
-/
def cld_same_numeric {α γ : Type} (divRound : DivRoundJl α α γ) (a b : α) : Jl γ :=
  divRound a b .Up

/--
Julia source: base/div.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(x::Real, y::Real) = div(promote(x, y)..., RoundDown)
```
-/
def fld_Real_Real {α β γ : Type} (promote : α → β → γ × γ)
    (divRound : DivRoundJl γ γ γ) (x : α) (y : β) : Jl γ :=
  let (a, b) := promote x y
  divRound a b .Down

/--
Julia source: base/div.jl:439-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(x::Real, y::Real) = div(promote(x, y)..., RoundUp)
```
-/
def cld_Real_Real {α β γ : Type} (promote : α → β → γ × γ)
    (divRound : DivRoundJl γ γ γ) (x : α) (y : β) : Jl γ :=
  let (a, b) := promote x y
  divRound a b .Up

/--
Julia source: base/div.jl:440-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(x::Signed, y::Unsigned) = div(x, y, RoundDown)
```
-/
def fld_Signed_Unsigned {α β γ : Type} (divRound : DivRoundJl α β γ)
    (x : α) (y : β) : Jl γ := divRound x y .Down

/--
Julia source: base/div.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(x::Unsigned, y::Signed) = div(x, y, RoundDown)
```
-/
def fld_Unsigned_Signed {α β γ : Type} (divRound : DivRoundJl α β γ)
    (x : α) (y : β) : Jl γ := divRound x y .Down

/--
Julia source: base/div.jl:442-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(x::Signed, y::Unsigned) = div(x, y, RoundUp)
```
-/
def cld_Signed_Unsigned {α β γ : Type} (divRound : DivRoundJl α β γ)
    (x : α) (y : β) : Jl γ := divRound x y .Up

/--
Julia source: base/div.jl:443-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(x::Unsigned, y::Signed) = div(x, y, RoundUp)
```
-/
def cld_Unsigned_Signed {α β γ : Type} (divRound : DivRoundJl α β γ)
    (x : α) (y : β) : Jl γ := divRound x y .Up

/--
Julia source: base/div.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fld(x::T, y::T) where {T<:Real} = throw(MethodError(div, (x, y, RoundDown)))
```
-/
def fld_Real_SameType_MethodError {α : Type} (_x _y : α) : Jl α :=
  .error (.methodError "div")

/--
Julia source: base/div.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cld(x::T, y::T) where {T<:Real} = throw(MethodError(div, (x, y, RoundUp)))
```
-/
def cld_Real_SameType_MethodError {α : Type} (_x _y : α) : Jl α :=
  .error (.methodError "div")

/--
Julia source: base/div.jl:448-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Real, y::Real, r::RoundingMode)
    typeof(x) === typeof(y) && throw(MethodError(div, (x, y, r)))
    if r === RoundToZero
        # For compat. Remove in 2.0.
        div(promote(x, y)...)
    else
        div(promote(x, y)..., r)
    end
end
```
-/
def div_Real_Real {α β γ : Type} (sameType : α → β → Bool)
    (promote : α → β → γ × γ) (div : γ → γ → Jl γ)
    (divRound : DivRoundJl γ γ γ) (x : α) (y : β) (r : RoundingMode) : Jl γ := do
  if sameType x y then .error (.methodError "div")
  else
    let (a, b) := promote x y
    if r = .ToZero then div a b else divRound a b r

/--
Julia source: base/div.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T, ::typeof(RoundDown)) where {T<:Unsigned} = div(x, y)
```
-/
def div_Unsigned_Down {α : Type} (div : DivJl α α α) (x y : α) : Jl α := div x y

/--
Julia source: base/div.jl:461-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::T, y::T, ::typeof(RoundDown)) where T<:Integer
    d = div(x, y, RoundToZero)
    return d - (signbit(x ⊻ y) & (d * y != x))
end
```
-/
def div_Integer_Down {α : Type} (divZero : DivJl α α α)
    (signbit : α → Bool) (xor : α → α → α) (mul : α → α → α)
    (neq : α → α → Bool) (subBool : α → Bool → α) (x y : α) : Jl α := do
  let d ← divZero x y
  pure (subBool d (signbit (xor x y) && neq (mul d y) x))

/--
Julia source: base/div.jl:467-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::T, y::T, ::typeof(RoundUp)) where T<:Unsigned
    d = div(x, y, RoundToZero)
    return d + (d * y != x)
end
```
-/
def div_Unsigned_Up {α : Type} (divZero : DivJl α α α) (mul : α → α → α)
    (neq : α → α → Bool) (addBool : α → Bool → α) (x y : α) : Jl α := do
  let d ← divZero x y
  pure (addBool d (neq (mul d y) x))

/--
Julia source: base/div.jl:471-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::T, y::T, ::typeof(RoundUp)) where T<:Integer
    d = div(x, y, RoundToZero)
    return d + (((x > 0) == (y > 0)) & (d * y != x))
end
```
-/
def div_Integer_Up {α : Type} (divZero : DivJl α α α)
    (gtZero : α → Bool) (mul : α → α → α) (neq : α → α → Bool)
    (addBool : α → Bool → α) (x y : α) : Jl α := do
  let d ← divZero x y
  pure (addBool d ((gtZero x = gtZero y) && neq (mul d y) x))

/--
Julia source: base/div.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T, r::RoundingMode) where {T<:AbstractFloat} = round(x / y - rem(x, y, r) / y)
```
-/
def div_AbstractFloat {α : Type} (div : α → α → α) (rem : α → α → RoundingMode → α)
    (sub : α → α → α) (round : α → α) (x y : α) (r : RoundingMode) : α :=
  round (sub (div x y) (div (rem x y r) y))

/-- BitInteger operator adapters used by the source methods above. -/
def bitSignbit {t : IntTy} (x : JInt t) : Bool := JuliaLean.base.int.signbit x
def bitXor {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.xor_int x y
def bitMul {t : IntTy} (x y : JInt t) : JInt t := JuliaLean.base.int.mulSame x y
def bitNeq {t : IntTy} (x y : JInt t) : Bool := decide (x.val ≠ y.val)
def bitAddBool {t : IntTy} (x : JInt t) (b : Bool) : JInt t :=
  x + JuliaLean.base.int.ofBool t b
def bitSubBool {t : IntTy} (x : JInt t) (b : Bool) : JInt t :=
  x - JuliaLean.base.int.ofBool t b
def bitAdd {t : IntTy} (x y : JInt t) : JInt t := x + y
def bitSub {t : IntTy} (x y : JInt t) : JInt t := x - y
def bitHalf {t : IntTy} (x : JInt t) : Int := x.val.tdiv 2
def bitIsOdd {t : IntTy} (x : JInt t) : Bool := x.val.tmod 2 ≠ 0
def bitIsEven {t : IntTy} (x : JInt t) : Bool := x.val.tmod 2 = 0
def bitGtZero {t : IntTy} (x : JInt t) : Bool := x.val > 0
def bitIsZero {t : IntTy} (x : JInt t) : Bool := x.val = 0

/-- *dispatch*: same-type BitInteger division by truncation. -/
def divBitIntegerToZero {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  div_BitInteger_ToZero JuliaLean.base.int.divSame x y

/-- *dispatch*: same-type BitInteger floor and ceiling division methods. -/
def divBitIntegerDown {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  if t.signed then
    div_Integer_Down divBitIntegerToZero bitSignbit bitXor bitMul bitNeq bitSubBool x y
  else
    div_Unsigned_Down JuliaLean.base.int.divSame x y

def divBitIntegerUp {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  if t.signed then
    div_Integer_Up divBitIntegerToZero bitGtZero bitMul bitNeq bitAddBool x y
  else
    div_Unsigned_Up divBitIntegerToZero bitMul bitNeq bitAddBool x y

/-- A dispatch adapter used only for Julia's RoundFromZero branches. -/
def divBitIntegerUpDown {t : IntTy} (x y : JInt t) (r : RoundingMode) :
    Jl (JInt t) :=
  if r = .Up then divBitIntegerUp x y
  else if r = .Down then divBitIntegerDown x y
  else .error (.methodError "div")

/-- `divrem`'s same-type truncating path, using the source directed method. -/
def divremBitIntegerToZero {t : IntTy} (x y : JInt t) : Jl (JInt t × JInt t) :=
  if t.signed then
    divrem_BitSigned_Directed divBitIntegerToZero divBitIntegerDown divBitIntegerUpDown
      bitMul bitSub x y .ToZero
  else
    divrem_Integer_Directed divBitIntegerToZero divBitIntegerDown divBitIntegerUpDown
      bitMul bitSub x y .ToZero
def bitVal {t : IntTy} (x : JInt t) : Int := x.val


def divremBitIntegerNearest {t : IntTy} (x y : JInt t) :
    Jl (JInt t × JInt t) :=
  divrem_Integer_Nearest divremBitIntegerToZero
    bitVal bitVal bitVal
    bitHalf bitHalf bitIsOdd bitIsEven bitAddBool bitSubBool bitAdd bitSub x y

def divremBitIntegerTiesAway {t : IntTy} (x y : JInt t) :
    Jl (JInt t × JInt t) :=
  divrem_Integer_NearestTiesAway divremBitIntegerToZero
    bitVal bitVal bitVal
    bitHalf bitHalf bitIsOdd bitAddBool bitSubBool bitAdd bitSub x y

def divremBitIntegerTiesUp {t : IntTy} (x y : JInt t) :
    Jl (JInt t × JInt t) :=
  divrem_Integer_NearestTiesUp divremBitIntegerToZero
    bitVal bitVal bitVal
    bitHalf bitHalf bitIsOdd bitAddBool bitSubBool bitAdd bitSub x y

def divremBitIntegerNearestModes {t : IntTy} (x y : JInt t) (r : RoundingMode) :
    Jl (JInt t × JInt t) :=
  if r = .Nearest then divremBitIntegerNearest x y
  else if r = .NearestTiesAway then divremBitIntegerTiesAway x y
  else if r = .NearestTiesUp then divremBitIntegerTiesUp x y
  else .error (.methodError "divrem")

/-- *dispatch*: same-type BitInteger `div` for each source rounding mode. -/
def divBitIntegerMode {t : IntTy} (x y : JInt t) (r : RoundingMode) : Jl (JInt t) :=
  if r = .ToZero then divBitIntegerToZero x y
  else if r = .Down then divBitIntegerDown x y
  else if r = .Up then divBitIntegerUp x y
  else if r = .FromZero then
    div_Integer_FromZero bitSignbit bitSignbit divBitIntegerUpDown x y
  else if r = .Nearest then
    div_Integer_Nearest divremBitIntegerNearestModes .Nearest x y
  else if r = .NearestTiesAway then
    div_Integer_Nearest divremBitIntegerNearestModes .NearestTiesAway x y
  else
    div_Integer_Nearest divremBitIntegerNearestModes .NearestTiesUp x y

/-- *dispatch*: same-type BitInteger `fld` and `cld`. -/
def fldBitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  fld_same_numeric divBitIntegerMode x y

def cldBitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  cld_same_numeric divBitIntegerMode x y

def modBitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  if t.signed then JuliaLean.base.int.mod_BitSigned fldBitInteger x y
  else JuliaLean.base.int.mod_Unsigned x y

def remBitIntegerUpDown {t : IntTy} (x y : JInt t) (r : RoundingMode) :
    Jl (JInt t) :=
  if r = .Up then rem_Up modBitInteger JuliaLean.base.int.neg x y
  else if r = .Down then rem_Down modBitInteger x y
  else .error (.methodError "rem")

/-- *dispatch*: same-type BitInteger `rem` for each source rounding mode. -/
def remBitIntegerMode {t : IntTy} (x y : JInt t) (r : RoundingMode) : Jl (JInt t) :=
  if r = .ToZero then rem_ToZero JuliaLean.base.int.remSame x y
  else if r = .Down then rem_Down modBitInteger x y
  else if r = .Up then rem_Up modBitInteger JuliaLean.base.int.neg x y
  else if r = .FromZero then
    rem_FromZero bitSignbit bitSignbit remBitIntegerUpDown x y
  else if r = .Nearest then
    rem_Integer_Nearest divremBitIntegerNearestModes x y
  else if r = .NearestTiesAway then
    rem_Integer_Ties divremBitIntegerNearestModes .NearestTiesAway x y
  else
    rem_Integer_Ties divremBitIntegerNearestModes .NearestTiesUp x y

def divremBitIntegerDirected {t : IntTy} (x y : JInt t) (r : DirectedMode) :
    Jl (JInt t × JInt t) :=
  if t.signed then
    divrem_BitSigned_Directed divBitIntegerToZero fldBitInteger divBitIntegerMode
      bitMul bitSub x y r
  else
    divrem_Integer_Directed divBitIntegerToZero fldBitInteger divBitIntegerMode
      bitMul bitSub x y r

def divremBitIntegerUpDown {t : IntTy} (x y : JInt t) (r : RoundingMode) :
    Jl (JInt t × JInt t) :=
  if r = .Up then divremBitIntegerDirected x y .Up
  else if r = .Down then divremBitIntegerDirected x y .Down
  else .error (.methodError "divrem")

/-- *dispatch*: same-type BitInteger `divrem` for each source rounding mode. -/
def divremBitIntegerMode {t : IntTy} (x y : JInt t) (r : RoundingMode) :
    Jl (JInt t × JInt t) :=
  if r = .ToZero then divremBitIntegerToZero x y
  else if r = .Down then divremBitIntegerDirected x y .Down
  else if r = .Up then divremBitIntegerDirected x y .Up
  else if r = .Nearest then divremBitIntegerNearest x y
  else if r = .NearestTiesAway then divremBitIntegerTiesAway x y
  else if r = .NearestTiesUp then divremBitIntegerTiesUp x y
  else divrem_FromZero bitSignbit bitSignbit divremBitIntegerUpDown x y

/-- *dispatch*: `fld1` is `cld` for same-type BitInteger arguments. -/
def fld1BitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  fld1 cldBitInteger x y

/-- *dispatch*: `fldmod` uses the source `divrem` method at RoundDown. -/
def fldmodBitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t × JInt t) :=
  fldmod divremBitIntegerMode x y

/-- *dispatch*: generic two-argument BitInteger division uses RoundToZero. -/
def divDefaultBitInteger {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  div_default divBitIntegerMode x y

end JuliaLean.base.div
namespace JuliaLean.base.div

private def mixedBoolAdd {t : IntTy} (x : JInt t) (b : Bool) : JInt t :=
  x + JuliaLean.base.int.ofBool t b

private def mixedBoolSub {t : IntTy} (x : JInt t) (b : Bool) : JInt t :=
  x - JuliaLean.base.int.ofBool t b

private def mixedIsZero {t : IntTy} (x : JInt t) : Bool := x.val = 0

private def mixedDivSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign x y
  divBitIntegerMode a b .ToZero

private def mixedRemSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign x y
  JuliaLean.base.int.remSame a b

private def mixedDivremSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u) × JInt (s.promote u)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign x y
  divremBitIntegerMode a b .ToZero

def mixedDivRoundSameSign {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) : Jl (JInt (s.promote u)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign x y
  divBitIntegerMode a b mode

private def mixedDivRoundPromoted {t : IntTy} (x y : JInt t)
    (mode : JuliaLean.base.float.RoundingMode) : Jl (JInt t) :=
  divBitIntegerMode x y mode

private def mixedFldSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u)) :=
  fld_Real_Real JuliaLean.base.int.promoteSameSign mixedDivRoundPromoted x y

private def mixedModSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u)) := do
  let (a, b) := JuliaLean.base.int.promoteSameSign x y
  if (s.promote u).signed then JuliaLean.base.int.mod_BitSigned fldBitInteger a b
  else JuliaLean.base.int.mod_Unsigned a b

private def mixedDivremSameSignRound {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (s.promote u) × JInt (s.promote ((s.promote u).promote u))) :=
  if mode = .ToZero then
    divrem_Integer_Directed mixedDivSameSign mixedFldSameSign mixedDivRoundSameSign
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .ToZero
  else if mode = .Down then
    divrem_Integer_Directed mixedDivSameSign mixedFldSameSign mixedDivRoundSameSign
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Down
  else if mode = .Up then
    divrem_Integer_Directed mixedDivSameSign mixedFldSameSign mixedDivRoundSameSign
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Up
  else .error (.methodError "divrem")

inductive NearestRemainder (R RA RS : Type) where
  | unchanged : R → NearestRemainder R RA RS
  | added : RA → NearestRemainder R RA RS
  | subtracted : RS → NearestRemainder R RA RS

structure NearestTypedOps
    (A B Q R H SH NH NSH HP NP HM NM RA RS : Type) where
  truncDivrem : A → B → Jl (Q × R)
  nonnegativeX : A → Jl Bool
  nonnegativeY : B → Jl Bool
  half : B → Jl H
  signedHalf : H → Jl SH
  negateHalf : H → Jl NH
  negateSignedHalf : SH → Jl NSH
  oddY : B → Jl Bool
  evenQ : Q → Jl Bool
  addHalf : H → Bool → Jl HP
  addNegativeHalf : NH → Bool → Jl NP
  subtractHalf : H → Bool → Jl HM
  subtractNegativeSignedHalf : NSH → Bool → Jl NM
  gePositiveThreshold : R → HP → Jl Bool
  geNegativeThreshold : R → NP → Jl Bool
  leNegativeSignedThreshold : R → NM → Jl Bool
  leHalfThreshold : R → HM → Jl Bool
  addQ : Q → Bool → Jl Q
  subtractQ : Q → Bool → Jl Q
  addR : R → B → Jl RA
  subtractR : R → B → Jl RS

def nearestDivremTyped
    {A B Q R H SH NH NSH HP NP HM NM RA RS : Type}
    (o : NearestTypedOps A B Q R H SH NH NSH HP NP HM NM RA RS)
    (mode : NearestMode) (x : A) (y : B) :
    Jl (Q × NearestRemainder R RA RS) := do
  let (q,r) ← o.truncDivrem x y
  let tie := fun (_ : Unit) => do
    let odd ← o.oddY y
    if mode = .Nearest then
      let even ← o.evenQ q
      pure (odd || even)
    else pure odd
  if ← o.nonnegativeX x then
    if ← o.nonnegativeY y then
      let h ← o.half y
      let threshold ← o.addHalf h (← tie ())
      if ← o.gePositiveThreshold r threshold then
        let q ← o.addQ q true
        let r ← o.subtractR r y
        pure (q,.subtracted r)
      else pure (q,.unchanged r)
    else
      let h ← o.negateHalf (← o.half y)
      let tie ← if mode = .NearestTiesUp then pure true else tie ()
      let threshold ← o.addNegativeHalf h tie
      if ← o.geNegativeThreshold r threshold then
        let q ← o.subtractQ q true
        let r ← o.addR r y
        pure (q,.added r)
      else pure (q,.unchanged r)
  else if ← o.nonnegativeY y then
    let h ← o.negateSignedHalf (← o.signedHalf (← o.half y))
    let tie ← if mode = .NearestTiesUp then pure true else tie ()
    let threshold ← o.subtractNegativeSignedHalf h tie
    if ← o.leNegativeSignedThreshold r threshold then
      let q ← o.subtractQ q true
      let r ← o.addR r y
      pure (q,.added r)
    else pure (q,.unchanged r)
  else
    let h ← o.half y
    let threshold ← o.subtractHalf h (← tie ())
    if ← o.leHalfThreshold r threshold then
      let q ← o.addQ q true
      let r ← o.subtractR r y
      pure (q,.subtracted r)
    else pure (q,.unchanged r)

def sameSignTruncDivrem {a b : IntTy} (x : JInt a) (y : JInt b) :
    Jl (JInt (a.promote b) × JInt (a.promote b)) := do
  let (x,y) := JuliaLean.base.int.promoteSameSign x y
  divremBitIntegerToZero x y

def mixedNativeMode {A B Q R H SH NH NSH HP NP HM NM RA RS : Type}
    (o : NearestTypedOps A B Q R H SH NH NSH HP NP HM NM RA RS)
    (trunc down up : A → B → Jl Q)
    (signbitX : A → Bool) (signbitY : B → Bool)
    (x : A) (y : B) (mode : JuliaLean.base.float.RoundingMode) : Jl Q :=
  if mode = .ToZero then trunc x y
  else if mode = .Down then down x y
  else if mode = .Up then up x y
  else if mode = .FromZero then
    div_Integer_FromZero signbitX signbitY
      (fun a b r => if r = .Up then up a b else down a b) x y
  else
    div_Integer_Nearest
      (fun a b r => nearestDivremTyped o
        (if r = .Nearest then .Nearest
         else if r = .NearestTiesAway then .NearestTiesAway
         else .NearestTiesUp) a b)
      (if mode = .Nearest then .Nearest
       else if mode = .NearestTiesAway then .NearestTiesAway
       else .NearestTiesUp) x y

private def isoddUnsigned {u : IntTy} (y : JInt u) : Jl Bool := do
  let r ← JuliaLean.base.int.rem_Unsigned_BitSigned mixedRemSameSign y (JInt.lit .i64 2)
  pure (JuliaLean.base.int.isodd_Real (fun _ => true) id (fun _ _ => r)
    (fun z => JuliaLean.base.int.eq z (JInt.lit .i64 0)) y)

private def isoddSigned {s : IntTy} (y : JInt s) : Jl Bool := do
  let r ← mixedRemSameSign y (JInt.lit .i64 2)
  pure (JuliaLean.base.int.isodd_Real (fun _ => true) id (fun _ _ => r)
    (fun z => JuliaLean.base.int.eq z (JInt.lit .i64 0)) y)

private def isevenSigned {s : IntTy} (q : JInt s) : Jl Bool := do
  let r ← mixedRemSameSign q (JInt.lit .i64 2)
  pure (JuliaLean.base.int.iseven_Real (fun _ => true) id (fun _ _ => r)
    (fun z => JuliaLean.base.int.eq z (JInt.lit .i64 0)) q)

private def isevenUnsigned {u : IntTy} (q : JInt u) : Jl Bool := do
  let r ← JuliaLean.base.int.rem_Unsigned_BitSigned mixedRemSameSign q (JInt.lit .i64 2)
  pure (JuliaLean.base.int.iseven_Real (fun _ => true) id (fun _ _ => r)
    (fun z => JuliaLean.base.int.eq z (JInt.lit .i64 0)) q)

def signedUnsignedNearestOps {s u : IntTy} :
    NearestTypedOps
      (JInt s) (JInt u)
      (JInt (s.toUnsigned.promote u).toSigned)
      (JInt (s.toUnsigned.promote u).toSigned)
      (JInt (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned)
      (JInt (JuliaLean.base.int.signedType (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned))
      (JInt (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned)
      (JInt (JuliaLean.base.int.signedType (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned))
      (JInt (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned)
      (JInt (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned)
      (JInt (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned)
      (JInt (JuliaLean.base.int.signedType (u.promote IntTy.i64.toUnsigned).toSigned.toUnsigned))
      (JInt (((s.toUnsigned.promote u).toSigned).promote u))
      (JInt (((s.toUnsigned.promote u).toSigned).promote u)) where
  truncDivrem := JuliaLean.base.int.divrem_BitSigned_Unsigned sameSignTruncDivrem
  nonnegativeX x := .ok (JuliaLean.base.int.le (JInt.lit .i64 0) x)
  nonnegativeY y := .ok (JuliaLean.base.int.le (JInt.lit .i64 0) y)
  half y := JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign y (JInt.lit .i64 2)
  signedHalf h := .ok (JuliaLean.base.int.signed h)
  negateHalf h := .ok (JuliaLean.base.int.neg h)
  negateSignedHalf sh := .ok (JuliaLean.base.int.neg sh)
  oddY := isoddUnsigned
  evenQ := isevenSigned
  addHalf h b := .ok (bitAddBool h b)
  addNegativeHalf nh b := .ok (bitAddBool nh b)
  subtractHalf h b := .ok (bitSubBool h b)
  subtractNegativeSignedHalf nsh b := .ok (bitSubBool nsh b)
  gePositiveThreshold r hp := .ok (JuliaLean.base.int.le hp r)
  geNegativeThreshold r np := .ok (JuliaLean.base.int.le np r)
  leNegativeSignedThreshold r nm := .ok (JuliaLean.base.int.le r nm)
  leHalfThreshold r hm := .ok (JuliaLean.base.int.le r hm)
  addQ q b := .ok (bitAddBool q b)
  subtractQ q b := .ok (bitSubBool q b)
  addR r y := .ok (JuliaLean.base.int.binop JuliaLean.base.int.add r y)
  subtractR r y := .ok (JuliaLean.base.int.binop JuliaLean.base.int.sub r y)

def mixedDivSignedUnsigned {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  mixedNativeMode signedUnsignedNearestOps
    (JuliaLean.base.int.div_BitSigned_Unsigned mixedDivSameSign)
    (div_Signed_Unsigned_Down
      (JuliaLean.base.int.divrem_BitSigned_Unsigned sameSignTruncDivrem)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolSub)
    (div_Signed_Unsigned_Up
      (JuliaLean.base.int.divrem_BitSigned_Unsigned sameSignTruncDivrem)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolAdd)
    JuliaLean.base.int.signbit JuliaLean.base.int.signbit x y mode
private def mixedFldSignedUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  fld_Signed_Unsigned mixedDivSignedUnsigned x y

private def mixedDivremSignedUnsignedRound {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (s.toUnsigned.promote u).toSigned ×
      JInt (s.promote ((s.toUnsigned.promote u).toSigned.promote u))) :=
  if mode = .Down then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_BitSigned_Unsigned mixedDivSameSign)
      mixedFldSignedUnsigned mixedDivSignedUnsigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Down
  else if mode = .ToZero then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_BitSigned_Unsigned mixedDivSameSign)
      mixedFldSignedUnsigned mixedDivSignedUnsigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .ToZero
  else if mode = .Up then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_BitSigned_Unsigned mixedDivSameSign)
      mixedFldSignedUnsigned mixedDivSignedUnsigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Up
  else .error (.methodError "divrem")

def unsignedSignedNearestOps {u s : IntTy} :
    NearestTypedOps
      (JInt u) (JInt s)
      (JInt (u.promote s.toUnsigned).toSigned.toUnsigned)
      (JInt (u.promote s.toUnsigned))
      (JInt (s.promote .i64))
      (JInt (JuliaLean.base.int.signedType (s.promote .i64)))
      (JInt (s.promote .i64))
      (JInt (JuliaLean.base.int.signedType (s.promote .i64)))
      (JInt (s.promote .i64))
      (JInt (s.promote .i64))
      (JInt (s.promote .i64))
      (JInt (JuliaLean.base.int.signedType (s.promote .i64)))
      (JInt ((u.promote s.toUnsigned).promote s))
      (JInt ((u.promote s.toUnsigned).promote s)) where
  truncDivrem := JuliaLean.base.int.divrem_Unsigned_BitSigned sameSignTruncDivrem
  nonnegativeX x := .ok (JuliaLean.base.int.le (JInt.lit .i64 0) x)
  nonnegativeY y := .ok (JuliaLean.base.int.le (JInt.lit .i64 0) y)
  half y := mixedDivSameSign y (JInt.lit .i64 2)
  signedHalf h := .ok (JuliaLean.base.int.signed h)
  negateHalf h := .ok (JuliaLean.base.int.neg h)
  negateSignedHalf sh := .ok (JuliaLean.base.int.neg sh)
  oddY := isoddSigned
  evenQ := isevenUnsigned
  addHalf h b := .ok (bitAddBool h b)
  addNegativeHalf nh b := .ok (bitAddBool nh b)
  subtractHalf h b := .ok (bitSubBool h b)
  subtractNegativeSignedHalf nsh b := .ok (bitSubBool nsh b)
  gePositiveThreshold r hp := .ok (JuliaLean.base.int.le hp r)
  geNegativeThreshold r np := .ok (JuliaLean.base.int.le np r)
  leNegativeSignedThreshold r nm := .ok (JuliaLean.base.int.le r nm)
  leHalfThreshold r hm := .ok (JuliaLean.base.int.le r hm)
  addQ q b := .ok (bitAddBool q b)
  subtractQ q b := .ok (bitSubBool q b)
  addR r y := .ok (JuliaLean.base.int.binop JuliaLean.base.int.add r y)
  subtractR r y := .ok (JuliaLean.base.int.binop JuliaLean.base.int.sub r y)

def mixedDivUnsignedSigned {u s : IntTy} (x : JInt u) (y : JInt s)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned) :=
  mixedNativeMode unsignedSignedNearestOps
    (JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign)
    (div_Unsigned_Signed_Down
      (JuliaLean.base.int.divrem_Unsigned_BitSigned sameSignTruncDivrem)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolSub)
    (div_Unsigned_Signed_Up
      (JuliaLean.base.int.divrem_Unsigned_BitSigned sameSignTruncDivrem)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolAdd)
    JuliaLean.base.int.signbit JuliaLean.base.int.signbit x y mode
private def mixedFldUnsignedSigned {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned) :=
  fld_Unsigned_Signed mixedDivUnsignedSigned x y

private def mixedDivremUnsignedSignedRound {u s : IntTy} (x : JInt u) (y : JInt s)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned ×
      JInt (u.promote ((u.promote s.toUnsigned).toSigned.toUnsigned.promote s))) :=
  if mode = .Down then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign)
      mixedFldUnsignedSigned mixedDivUnsignedSigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Down
  else if mode = .ToZero then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign)
      mixedFldUnsignedSigned mixedDivUnsignedSigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .ToZero
  else if mode = .Up then
    divrem_Integer_Directed
      (JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign)
      mixedFldUnsignedSigned mixedDivUnsignedSigned
      (JuliaLean.base.int.binop JuliaLean.base.int.mul_int)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub_int) x y .Up
  else .error (.methodError "divrem")

/-- *dispatch*: the mixed fixed-width `fldmod` paths use the source generic `divrem` method and
the actual mixed `mod` methods from `base/int.jl`. -/
def fldmodMixedSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u) × JInt (s.promote ((s.promote u).promote u))) :=
  fldmod mixedDivremSameSignRound x y

def modMixedSameSign {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.promote u)) :=
  mixedModSameSign x y

def fldmodMixedSignedUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.toUnsigned.promote u).toSigned ×
      JInt (s.promote ((s.toUnsigned.promote u).toSigned.promote u))) :=
  fldmod mixedDivremSignedUnsignedRound x y

def modMixedSignedUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt ((s.toUnsigned.promote u).toSigned.promote u).toUnsigned) :=
  JuliaLean.base.int.mod_BitSigned_Unsigned mixedRemSameSign x y

def fldmodMixedUnsignedSigned {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned ×
      JInt (u.promote ((u.promote s.toUnsigned).toSigned.toUnsigned.promote s))) :=
  fldmod mixedDivremUnsignedSignedRound x y

def modMixedUnsignedSigned {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt ((u.promote s.toUnsigned).toSigned.promote s)) :=
  JuliaLean.base.int.mod_Unsigned_Signed mixedRemSameSign x y

def divMixedResultTy (s u : IntTy) : IntTy :=
  if s.signed == u.signed then s.promote u
  else if s.signed then (s.toUnsigned.promote u).toSigned
  else (s.promote u.toUnsigned).toSigned.toUnsigned

/-- *dispatch*: heterogeneous BitInteger rounded `div(x, y, mode)` across all signedness combinations
and all source rounding modes (`base/div.jl:326-373,391-417,448-456`). -/
def divBitIntegerMixedMode {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) : Jl (JInt (divMixedResultTy s u)) :=
  let rec go (b1 b2 : Bool) :
      Jl (JInt (if b1 then s.promote u
        else if b2 then (s.toUnsigned.promote u).toSigned
        else (s.promote u.toUnsigned).toSigned.toUnsigned)) :=
    match b1, b2 with
    | true, _ => mixedDivRoundSameSign x y mode
    | false, true => mixedDivSignedUnsigned x y mode
    | false, false => mixedDivUnsignedSigned x y mode
  go (s.signed == u.signed) s.signed

end JuliaLean.base.div

namespace JuliaLean.Float.F64

/-- `base/div.jl:127-149`, `base/math.jl:1122-1145`: mode-specific remainder dispatch. -/
def remMode (x y : F64) (mode : Rounding) : F64 := Id.run do
  match mode with
  | .RoundToZero => return rem x y
  | .RoundDown => return mod x y
  | .RoundUp => return mod x (neg y)
  | .RoundNearest => return JuliaLean.Float.F64.extraRemNearest x y
  | .RoundNearestTiesAway =>
    let r := mod x y
    if isnan r then return r
    if !iszero r then
      let two := ofInt 2
      let (m, n) := if lt (abs r) (div floatmax two) then (abs (mul two r), abs y)
                    else (abs r, abs (div y two))
      if lt m n then return r
      if lt n m then return mod x (neg y)
    return if signbit x == signbit y then mod x (neg y) else r
/-- `base/div.jl:77,480`: each division and subtraction rounds before nearest-even rounding. -/
def divInteger (x y : F64) (mode : Rounding := .RoundToZero) : F64 :=
  round (sub (div x y) (div (remMode x y mode) y))
/-- `base/div.jl:432`: floored quotient wrapper. -/
def fld (x y : F64) : F64 := divInteger x y .RoundDown
/-- `base/div.jl:433`: ceiling quotient wrapper. -/
def cld (x y : F64) : F64 := divInteger x y .RoundUp

/--
Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:111-122` and `base/math.jl:1137-1160`.
The release has no Float64 ties-away remainder method; master adds it at
`base/div.jl:139-149`.
-/
def remModeRelease (x y : F64) (mode : Rounding) : Jl F64 :=
  match mode with
  | .RoundToZero => .ok (rem x y)
  | .RoundDown => .ok (mod x y)
  | .RoundUp => .ok (mod x (neg y))
  | .RoundNearest => .ok (JuliaLean.Float.F64.extraRemNearest x y)
  | .RoundNearestTiesAway => .error (.methodError "rem")

/--
Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:383`: subtraction precedes division.
Master `base/div.jl:480` instead divides both terms before subtracting.
-/
def divIntegerRelease (x y : F64) (mode : Rounding := .RoundToZero) : Jl F64 := do
  let r ← remModeRelease x y mode
  pure (round (div (sub x r) y))

/-- Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:336`: release floored quotient. -/
def fldRelease (x y : F64) : Jl F64 := divIntegerRelease x y .RoundDown
/-- Julia 1.13.2 (`45b6d15e34b`), `base/div.jl:337`: release ceiling quotient. -/
def cldRelease (x y : F64) : Jl F64 := divIntegerRelease x y .RoundUp

end JuliaLean.Float.F64

namespace JuliaLean.IntArith.Division

/-- Same-signedness division after checked promotion, `base/div.jl:448-455`;
`base/int.jl:355-358,1085-1089` supplies the primitive (64-bit platform). -/
def promotedDiv (x y : Value) : Jl Value := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert (t.name) t x.int.val
  let b ← JInt.convert (t.name) t y.int.val
  pure (pack (← JInt.div a b))

/-- Same-signedness `divrem`, `base/div.jl:290-324`: quotient first,
then wrapping multiply and subtract, including at typemin. -/
def promotedDivrem (x y : Value) : Jl (Value × Value) := do
  let q ← promotedDiv x y
  pure (q, sub x (mul q y))

/-- `base/div.jl:391-398,438-443,460-464`: mixed floor uses mixed
`divrem`; same-signedness operands use checked promotion and same-type fld. -/
def fld (x y : Value) : Jl Value := do
  if x.ty.signed != y.ty.signed then
    let (q, r) ← divrem promotedDivrem x y
    let neg := if x.ty.signed then signbit x else signbit y
    pure (pack (q.int - JInt.lit q.ty (if neg && r.int.val != 0 then 1 else 0)))
  else
    let t := IntTy.promote x.ty y.ty
    let a ← JInt.convert (t.name) t x.int.val
    let b ← JInt.convert (t.name) t y.int.val
    pure (pack (← JInt.fld a b))

/-- `base/div.jl:400-407,438-443,467-474`: ceiled mixed quotient
corrects unsigned-magnitude divrem and wraps in the quotient's own type. -/
def cld (x y : Value) : Jl Value := do
  if x.ty.signed != y.ty.signed then
    let (q, r) ← divrem promotedDivrem x y
    let neg := if x.ty.signed then signbit x else signbit y
    pure (pack (q.int + JInt.lit q.ty (if !neg && r.int.val != 0 then 1 else 0)))
  else
    let t := IntTy.promote x.ty y.ty
    let a ← JInt.convert (t.name) t x.int.val
    let b ← JInt.convert (t.name) t y.int.val
    pure (pack (← JInt.cld a b))

/-- `base/div.jl:290-324,387`: fldmod uses the generic integer
reconstruction, rather than calling mixed mod. -/
def fldmod (x y : Value) : Jl (Value × Value) := do
  let q ← fld x y
  pure (q, sub x (mul q y))

end JuliaLean.IntArith.Division

namespace JuliaLean.IntArith.PowersDigits

/-- `base/int.jl:275-288`, `base/div.jl:391-407,438-443`: mixed-sign division
uses magnitude division followed by wrapping sign/rounding corrections.
Same-sign arguments use promotion and the Core checked quotient. -/
def quotient (roundUp roundDown : Bool) (a b : Box) : Jl Box := do
  let ⟨ta,x⟩ := a
  let ⟨tb,y⟩ := b
  if ta.signed = tb.signed then
    let t := IntTy.promote ta tb
    let x := JInt.rem t x
    let y := JInt.rem t y
    let q ← if roundUp then JInt.cld x y else if roundDown then JInt.fld x y else JInt.div x y
    pure ⟨t,q⟩
  else
    let u := IntTy.promote ta.toUnsigned tb.toUnsigned
    let ax := JInt.rem u (if x.val < 0 then -x else x)
    let ay := JInt.rem u (if y.val < 0 then -y else y)
    let q ← JInt.div ax ay
    let r ← JInt.remInt ax ay
    let s := JInt.rem u.toSigned q
    let s := if (x.val < 0) != (y.val < 0) then -s else s
    let t := if ta.signed then u.toSigned else u
    let q := JInt.rem t s
    let q := if roundDown && ((x.val < 0) != (y.val < 0)) && r.val != 0 then
      q - JInt.lit t 1 else q
    let q := if roundUp && ((x.val < 0) == (y.val < 0)) && r.val != 0 then
      q + JInt.lit t 1 else q
    pure ⟨t,q⟩

end JuliaLean.IntArith.PowersDigits

namespace JuliaLean.IntArith.Rational

/-- Integer rounding mirrors every sign and tie branch of `divrem`, using
wrapping intermediates, including the explicit signed half-divisor;
base/div.jl:326-373,409-416,421,460-474. -/
def roundedDiv {t} (x y : JInt t) (mode : Rounding) : Jl (JInt t) := do
  match mode with
  | .toZero => JInt.div x y
  | .down => JInt.fld x y
  | .up => JInt.cld x y
  | .fromZero => if x.val < 0 ↔ y.val < 0 then JInt.cld x y else JInt.fld x y
  | .nearest | .nearestAway | .nearestUp =>
    let q ← JInt.div x y
    let r := x - q * y
    let half ← JInt.div y (JInt.lit t 2)
    let oddY := decide (y.val % 2 ≠ 0)
    let evenQ := decide (q.val % 2 = 0)
    let tie : Bool := match mode with
      | .nearest => oddY || evenQ
      | .nearestAway => oddY
      | _ => if x.val < 0 ↔ y.val < 0 then oddY else true
    let c := JInt.lit t (if tie then 1 else 0)
    if x.val ≥ 0 then
      if y.val ≥ 0 then return if r ≥ half + c then q + JInt.lit t 1 else q
      else return if r ≥ -half + c then q - JInt.lit t 1 else q
    else
      if y.val ≥ 0 then
        let shalf := JInt.wrap t.toSigned half.val
        let threshold := -shalf - JInt.lit t.toSigned (if tie then 1 else 0)
        return if r.val ≤ threshold.val then q - JInt.lit t 1 else q
      else return if r ≤ half - c then q + JInt.lit t 1 else q

end JuliaLean.IntArith.Rational

namespace JuliaLean.FloatIntCov.Div

open JuliaLean JuliaLean.IntArith.Division JuliaLean.Float

inductive Mode where
  | toZero | down | up | nearest | tiesAway | tiesUp | fromZero
  deriving DecidableEq, Repr

/-- `base/div.jl:326-373`: nearest integer quotient adjustments. -/
def nearestDivrem (x y : Value) (mode : Mode) : Jl (Value × Value) := do
  let (q, r) ← divrem promotedDivrem x y
  let yh := y.int.val.tdiv 2
  let odd := y.int.val % 2 != 0
  let evenq := q.int.val % 2 = 0
  let adjustUp := match mode with
    | .nearest => odd || evenq
    | .tiesAway | .tiesUp => odd
    | _ => false
  let posAdjust := add q (lit q.ty 1)
  let negAdjust := sub q (lit q.ty 1)
  if x.int.val ≥ 0 then
    if y.int.val ≥ 0 then
      if r.int.val ≥ yh + (if adjustUp then 1 else 0) then pure (posAdjust, sub r y) else pure (q, r)
    else
      let tie := if mode = .tiesUp then 1 else if adjustUp then 1 else 0
      if r.int.val ≥ -yh + tie then pure (negAdjust, add r y) else pure (q, r)
  else if y.int.val ≥ 0 then
    let tie := if mode = .tiesUp then 1 else if adjustUp then 1 else 0
    if r.int.val ≤ -yh - tie then pure (negAdjust, add r y) else pure (q, r)
  else if r.int.val ≤ yh - (if adjustUp then 1 else 0) then pure (posAdjust, sub r y)
  else pure (q, r)

/-- `base/div.jl:290-325`: quotient first, then source-type reconstruction. -/
def directedDivrem (x y : Value) : Mode → Jl (Value × Value)
  | .toZero => divrem promotedDivrem x y
  | .down => do
      let q ← fld x y
      pure (q, sub x (mul q y))
  | .up => do
      let q ← cld x y
      pure (q, sub x (mul q y))
  | m => nearestDivrem x y m

/-- `base/div.jl:273-286,375-377`: complete mode dispatch. -/
def divremMode (x y : Value) : Mode → Jl (Value × Value)
  | .toZero => directedDivrem x y .toZero
  | .down => directedDivrem x y .down
  | .up => directedDivrem x y .up
  | .nearest => nearestDivrem x y .nearest
  | .tiesAway => nearestDivrem x y .tiesAway
  | .tiesUp => nearestDivrem x y .tiesUp
  | .fromZero => if signbit x = signbit y then directedDivrem x y .up else directedDivrem x y .down

/-- `base/div.jl:77,127-138,196,243,252,387,391-475`. -/
def divMode (x y : Value) (m : Mode := .toZero) : Jl Value := do
  pure (← divremMode x y m).1

def negValue (x : Value) : Value := pack (-x.int)

/-- The actual remainder methods at `base/div.jl:127-138`; unlike `divrem`,
RoundUp negates the fixed-width divisor before calling mod. -/
def remMode (x y : Value) : Mode → Jl Value
  | .toZero => rem promotedRem x y
  | .down => mod (rem promotedRem) x y
  | .up => mod (rem promotedRem) x (negValue y)
  | .nearest => do pure (← divremMode x y .nearest).2
  | .tiesAway => do pure (← divremMode x y .tiesAway).2
  | .tiesUp => do pure (← divremMode x y .tiesUp).2
  | .fromZero => if signbit x = signbit y then mod (rem promotedRem) x (negValue y) else mod (rem promotedRem) x y

def fldMethod (x y : Value) : Jl Value := divMode x y .down
def cldMethod (x y : Value) : Jl Value := divMode x y .up
def fld1Method (x y : Value) : Jl Value := cldMethod x y
def fldmodMethod (x y : Value) : Jl (Value × Value) := divremMode x y .down

/-- `base/div.jl:422-430`: Bool division ignores the supplied rounding mode. -/
def boolDiv (_mode : Mode) (x y : Bool) : Jl Bool :=
  if !y then .error .divideError else .ok x

/-- `base/div.jl:139-149`: Float64 nearest ties-away and ties-up remainder. -/
def floatTieRem (x y : F64) (tiesUp : Bool) : F64 := Id.run do
  let r := F64.mod x y
  if F64.isnan r then return r
  if !F64.iszero r then
    let two := F64.ofInt 2
    let (m, n) := if F64.lt (F64.abs r) (F64.div F64.floatmax two)
      then (F64.abs (F64.mul two r), F64.abs y)
      else (F64.abs r, F64.abs (F64.div y two))
    if F64.lt m n then return r
    if F64.lt n m then return F64.mod x (F64.neg y)
  return if tiesUp || F64.signbit x == F64.signbit y then F64.mod x (F64.neg y) else r

/-- Binary64 remainder dispatch at `base/div.jl:127-149`. -/
def floatRemMode (x y : F64) : Mode → F64
  | .toZero => F64.rem x y
  | .down => F64.mod x y
  | .up => F64.mod x (F64.neg y)
  | .nearest => F64.remMode x y .RoundNearest
  | .tiesAway => floatTieRem x y false
  | .tiesUp => floatTieRem x y true
  | .fromZero => if F64.signbit x == F64.signbit y then F64.mod x (F64.neg y) else F64.mod x y

/-- `base/div.jl:480`, with the requested integral-rounding primitive explicit. -/
def floatDivMode (rounder : F64 → Mode → F64) (x y : F64) (m : Mode) : F64 :=
  rounder (F64.sub (F64.div x y) (F64.div (floatRemMode x y m) y)) m

/-- Generic compatibility/promotion routes at `base/div.jl:276-286,438-455`. -/
def defaultDiv {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .toZero

def genericRemMode {α : Type} (rem mod : α → α → Jl α) (neg : α → α)
    (sub mul : α → α → α) (divRound : α → α → Mode → Jl α)
    (signbit : α → Bool) (x y : α) : Mode → Jl α
  | .toZero => rem x y
  | .down => mod x y
  | .up => mod x (neg y)
  | .nearest => do pure (sub x (mul y (← divRound x y .nearest)))
  | .fromZero => if signbit x == signbit y then mod x (neg y) else mod x y
  | m => do pure (sub x (mul y (← divRound x y m)))

def genericFld {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .down

def genericCld {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) : Jl α :=
  divRound x y .up

def genericDivrem {α : Type} (div rem fld mod : α → α → Jl α)
    (divRound remRound : α → α → Mode → Jl α) (x y : α) (m : Mode) : Jl (α × α) :=
  match m with
  | .toZero => do pure (← div x y, ← rem x y)
  | .down => do pure (← fld x y, ← mod x y)
  | _ => do pure (← divRound x y m, ← remRound x y m)

def promotedDiv {α : Type} (sameType : Bool) (promote : α → α → α × α)
    (div divRound : α → α → Mode → Jl α) (x y : α) (m : Mode) : Jl α :=
  if sameType then .error (.methodError "div")
  else
    let p := promote x y
    if m = .toZero then div p.1 p.2 .toZero else divRound p.1 p.2 m

end JuliaLean.FloatIntCov.Div
