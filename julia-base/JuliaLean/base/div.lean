import JuliaLean.base.int
import JuliaLean.base.float

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

private def mixedDivRoundSameSign {s u : IntTy} (x : JInt s) (y : JInt u)
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

private def mixedDivSignedUnsignedUpDown {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  if mode = .Down then
    div_Signed_Unsigned_Down
      (JuliaLean.base.int.divrem_BitSigned_Unsigned mixedDivremSameSign)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolSub x y
  else if mode = .Up then
    div_Signed_Unsigned_Up
      (JuliaLean.base.int.divrem_BitSigned_Unsigned mixedDivremSameSign)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolAdd x y
  else .error (.methodError "div")

private def mixedDivSignedUnsigned {s u : IntTy} (x : JInt s) (y : JInt u)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  if mode = .ToZero then
    JuliaLean.base.int.div_BitSigned_Unsigned mixedDivSameSign x y
  else if mode = .FromZero then
    div_Integer_FromZero JuliaLean.base.int.signbit JuliaLean.base.int.signbit
      mixedDivSignedUnsignedUpDown x y
  else mixedDivSignedUnsignedUpDown x y mode

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

private def mixedDivUnsignedSignedUpDown {u s : IntTy} (x : JInt u) (y : JInt s)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned) :=
  if mode = .Down then
    div_Unsigned_Signed_Down
      (JuliaLean.base.int.divrem_Unsigned_BitSigned mixedDivremSameSign)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolSub x y
  else if mode = .Up then
    div_Unsigned_Signed_Up
      (JuliaLean.base.int.divrem_Unsigned_BitSigned mixedDivremSameSign)
      JuliaLean.base.int.signbit mixedIsZero mixedBoolAdd x y
  else .error (.methodError "div")

private def mixedDivUnsignedSigned {u s : IntTy} (x : JInt u) (y : JInt s)
    (mode : JuliaLean.base.float.RoundingMode) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned) :=
  if mode = .ToZero then
    JuliaLean.base.int.div_Unsigned_BitSigned mixedDivSameSign x y
  else if mode = .FromZero then
    div_Integer_FromZero JuliaLean.base.int.signbit JuliaLean.base.int.signbit
      mixedDivUnsignedSignedUpDown x y
  else mixedDivUnsignedSignedUpDown x y mode

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

end JuliaLean.base.div
