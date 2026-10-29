import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Int

open JuliaLean
open JuliaLean.C

/--
Julia source: base/int.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<)(x::T, y::T) where {T<:BitSigned}  = slt_int(x, y)
```
-/
def ltBitSigned : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(<)(x::T, y::T): arity"
  return mkBool ((← asInt x) < (← asInt y))

/--
Julia source: base/int.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::BitInteger)                    = neg_int(x)
```
-/
def negBitInt : Body := fun _ args => do
  let [x] := args | throwMethodError "(-)(x::BitInteger): arity"
  let ty ← typeOfObj x
  return .bits ty (wrapInt64 (-(← asInt x)))

/--
Julia source: base/int.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::T, y::T) where {T<:BitInteger} = sub_int(x, y)
```
-/
def subBitInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(-)(x::T, y::T): arity"
  let ty ← typeOfObj x
  return .bits ty (wrapInt64 ((← asInt x) - (← asInt y)))

/--
Julia source: base/int.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::T, y::T) where {T<:BitInteger} = add_int(x, y)
```
-/
def addBitInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(+)(x::T, y::T): arity"
  let ty ← typeOfObj x
  return .bits ty (wrapInt64 ((← asInt x) + (← asInt y)))

/--
Julia source: base/int.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(*)(x::T, y::T) where {T<:BitInteger} = mul_int(x, y)
```
-/
def mulBitInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(*)(x::T, y::T): arity"
  let ty ← typeOfObj x
  return .bits ty (wrapInt64 ((← asInt x) * (← asInt y)))

/--
Julia source: base/int.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-%)(x::BitInteger)                    = neg_int(x)
```
-/
def negWrapBitInt : Body := negBitInt

/--
Julia source: base/int.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-%)(x::T, y::T) where {T<:BitInteger} = sub_int(x, y)
```
-/
def subWrapBitInt : Body := subBitInt

/--
Julia source: base/int.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x) = x % typeof(convert(Unsigned, zero(x)))
```
-/
def unsignedGeneric : Body := fun call args => do
  let [x] := args | throwMethodError "unsigned(x): arity"
  let z ← call "Base.zero" [x]
  let c ← call "Base.convert" [.type (.datatype "Core.Unsigned" []), z]
  let t ← typeOfObj c
  call "Base.rem" [x, .type t]

/--
Julia source: base/int.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::BitSigned) = reinterpret(typeof(convert(Unsigned, zero(x))), x)
```
-/
def unsignedBitSigned : Body := fun call args => do
  let [x] := args | throwMethodError "unsigned(x::BitSigned): arity"
  call "Base.reinterpret" [.type uint64Type, x]

/--
Julia source: base/int.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T) where {T<:BitSigned64} = checked_sdiv_int(x, y)
```
-/
def divBitSigned64 : Body := fun _ args => do
  let [x, y] := args | throwMethodError "div(x::T, y::T): arity"
  let xv ← asInt x
  let yv ← asInt y
  if yv == 0 || (xv == -(1 <<< 63) && yv == -1) then
    throwDivideError "DivideError"
  let ty ← typeOfObj x
  return .bits ty (xv.tdiv yv)

/--
Julia source: base/int.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, y::T) where {T<:BitSigned64} = checked_srem_int(x, y)
```
-/
def remBitSigned64 : Body := fun _ args => do
  let [x, y] := args | throwMethodError "rem(x::T, y::T): arity"
  let xv ← asInt x
  let yv ← asInt y
  if yv == 0 then
    throwDivideError "DivideError"
  let ty ← typeOfObj x
  return .bits ty (xv.tmod yv)

/--
Julia source: base/int.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T) where {T<:BitUnsigned64} = checked_udiv_int(x, y)
```
-/
def divBitUnsigned64 : Body := fun _ args => do
  let [x, y] := args | throwMethodError "div(x::T, y::T): arity"
  let xv := wrapUInt64 (← asInt x)
  let yv := wrapUInt64 (← asInt y)
  if yv == 0 then
    throwDivideError "DivideError"
  let ty ← typeOfObj x
  return .bits ty (xv / yv)

/--
Julia source: base/int.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, y::T) where {T<:BitUnsigned64} = checked_urem_int(x, y)
```
-/
def remBitUnsigned64 : Body := fun _ args => do
  let [x, y] := args | throwMethodError "rem(x::T, y::T): arity"
  let xv := wrapUInt64 (← asInt x)
  let yv := wrapUInt64 (← asInt y)
  if yv == 0 then
    throwDivideError "DivideError"
  let ty ← typeOfObj x
  return .bits ty (xv % yv)

/--
Julia source: base/int.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::T, y::T) where {T<:BitInteger} = and_int(x, y)
```
-/
def andBitInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(&)(x::T, y::T): arity"
  let ty ← typeOfObj x
  let ua : UInt64 := UInt64.ofNat (wrapUInt64 (← asInt x)).toNat
  let ub : UInt64 := UInt64.ofNat (wrapUInt64 (← asInt y)).toNat
  let r := Int.ofNat (ua &&& ub).toNat
  return .bits ty (if ty == int64Type then wrapInt64 r else r)

/--
Julia source: base/int.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::T, y::T) where {T<:BitInteger} = or_int(x, y)
```
-/
def orBitInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(|)(x::T, y::T): arity"
  let ty ← typeOfObj x
  let ua : UInt64 := UInt64.ofNat (wrapUInt64 (← asInt x)).toNat
  let ub : UInt64 := UInt64.ofNat (wrapUInt64 (← asInt y)).toNat
  let r := Int.ofNat (ua ||| ub).toNat
  return .bits ty (if ty == int64Type then wrapInt64 r else r)

/--
Julia source: base/int.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(< )(x::T, y::T) where {T<:BitUnsigned} = ult_int(x, y)
```
-/
def ltBitUnsigned : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(<)(x::T, y::T): arity"
  return mkBool (ultInt64 (← asInt x) (← asInt y))

/--
Julia source: base/int.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:BitSigned}   = sle_int(x, y)
```
-/
def leBitSigned : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(<=)(x::T, y::T): arity"
  return mkBool ((← asInt x) ≤ (← asInt y))

/--
Julia source: base/int.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:BitUnsigned} = ule_int(x, y)
```
-/
def leBitUnsigned : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(<=)(x::T, y::T): arity"
  let xv ← asInt x
  let yv ← asInt y
  return mkBool (wrapUInt64 xv ≤ wrapUInt64 yv)

/--
Julia source: base/int.jl:577-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::BitSigned, y::BitUnsigned) = y == x
```
-/
def eqSignedUnsigned : Body := fun call args => do
  let [x, y] := args | throwMethodError "==(x::BitSigned, y::BitUnsigned): arity"
  call "Base.==" [y, x]

/--
Julia source: base/int.jl:578-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::BitSigned, y::BitUnsigned) = !(y <= x)
```
-/
def ltSignedUnsigned : Body := fun call args => do
  let [x, y] := args | throwMethodError "<(x::BitSigned, y::BitUnsigned): arity"
  let c ← call "Base.<=" [y, x]
  call "Base.!" [c]

/--
Julia source: base/int.jl:579-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::BitSigned, y::BitUnsigned) = !(y < x)
```
-/
def leSignedUnsigned : Body := fun call args => do
  let [x, y] := args | throwMethodError "<=(x::BitSigned, y::BitUnsigned): arity"
  let c ← call "Base.<" [y, x]
  call "Base.!" [c]

/--
Julia source: base/int.jl:591-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function max(x::S, y::T) where {S <: BitInteger, T <: BitInteger}
    R = promote_type(S, T)
    ifelse(x < y, y % R, x % R)
end
```
-/
def maxBitInt : Body := fun call args => do
  let [x, y] := args | throwMethodError "max(x::S, y::T): arity"
  let S ← typeOfObj x
  let T ← typeOfObj y
  let R ← call "Base.promote_type" [.type S, .type T]
  let c ← call "Base.<" [x, y]
  let yr ← call "Base.rem" [y, R]
  let xr ← call "Base.rem" [x, R]
  if ← asBool c then return yr else return xr

/--
Julia source: base/int.jl:695-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, ::Type{T}) where {T<:Integer} = x
```
-/
def remIdentityType : Body := fun _ args => do
  let [x, _] := args | throwMethodError "rem(x::T, ::Type{T}): arity"
  return x

/--
Julia source: base/int.jl:698-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, T::Type{<:Integer}) = convert(T, x)  # `x % T` falls back to `convert`
```
-/
def remConvertType : Body := fun call args => do
  let [x, T] := args | throwMethodError "rem(x::Integer, T::Type{<:Integer}): arity"
  call "Base.convert" [T, x]

/--
Julia source: base/int.jl:699-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, ::Type{Bool}) = ((x & 1) != 0)
```
-/
def remBoolType : Body := fun _ args => do
  let [x, _] := args | throwMethodError "rem(x::Integer, ::Type{Bool}): arity"
  return mkBool ((← asInt x) % 2 != 0)

/--
Julia source: base/int.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{T}, x::Integer) where {T<:Integer} = rem(x, T)
```
-/
def unsafeTruncInteger : Body := fun call args => do
  let [T, x] := args | throwMethodError "unsafe_trunc(::Type{T}, x::Integer): arity"
  call "Base.rem" [x, T]


def bodies : List (String × Body) :=
  [ ("base/int.jl:84", ltBitSigned)
  , ("base/int.jl:86", negBitInt)
  , ("base/int.jl:87", subBitInt)
  , ("base/int.jl:88", addBitInt)
  , ("base/int.jl:89", mulBitInt)
  , ("base/int.jl:91", negWrapBitInt)
  , ("base/int.jl:92", subWrapBitInt)
  , ("base/int.jl:261", unsignedGeneric)
  , ("base/int.jl:262", unsignedBitSigned)
  , ("base/int.jl:355", divBitSigned64)
  , ("base/int.jl:356", remBitSigned64)
  , ("base/int.jl:357", divBitUnsigned64)
  , ("base/int.jl:358", remBitUnsigned64)
  , ("base/int.jl:407", andBitInt)
  , ("base/int.jl:432", orBitInt)
  , ("base/int.jl:573", ltBitUnsigned)
  , ("base/int.jl:574", leBitSigned)
  , ("base/int.jl:575", leBitUnsigned)
  , ("base/int.jl:577", eqSignedUnsigned)
  , ("base/int.jl:578", ltSignedUnsigned)
  , ("base/int.jl:579", leSignedUnsigned)
  , ("base/int.jl:591", maxBitInt)
  , ("base/int.jl:695", remIdentityType)
  , ("base/int.jl:698", remConvertType)
  , ("base/int.jl:699", remBoolType)
  , ("base/int.jl:704", unsafeTruncInteger)
  ]

end JuliaLean.Pilot.Base.Int
