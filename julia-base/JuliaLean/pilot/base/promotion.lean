import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Promotion

open JuliaLean
open JuliaLean.C

/--
Julia source: base/promotion.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_type(::Type{T}, ::Type{T}) where {T} = T
```
-/
def promoteTypeSame : Body := fun _ args => do
  let [T, _] := args | throwMethodError "promote_type(::Type{T}, ::Type{T}): arity"
  return T

/--
Julia source: base/promotion.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(==)(x::T, y::T) where {T<:Number} = x === y
```
-/
def eqSameNumber : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(==)(x::T, y::T): arity"
  return mkBool (x == y)

/--
Julia source: base/promotion.jl:667-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:Real} = (x == y) | (x < y)
```
-/
def leSameReal : Body := fun call args => do
  let [x, y] := args | throwMethodError "(<=)(x::T, y::T): arity"
  let c1 ← call "Base.==" [x, y]
  let c2 ← call "Base.<" [x, y]
  call "Base.|" [c1, c2]

/--
Julia source: base/promotion.jl:676-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:Real} = ifelse(y < x, x, y)
```
-/
def maxSameReal : Body := fun call args => do
  let [x, y] := args | throwMethodError "max(x::T, y::T): arity"
  let c ← call "Base.<" [y, x]
  if ← asBool c then return x else return y

/--
Julia source: base/promotion.jl:677-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:Real} = ifelse(y < x, y, x)
```
-/
def minSameReal : Body := fun call args => do
  let [x, y] := args | throwMethodError "min(x::T, y::T): arity"
  let c ← call "Base.<" [y, x]
  if ← asBool c then return y else return x

def bodies : List (String × Body) :=
  [ ("base/promotion.jl:332", promoteTypeSame)
  , ("base/promotion.jl:665", eqSameNumber)
  , ("base/promotion.jl:667", leSameReal)
  , ("base/promotion.jl:676", maxSameReal)
  , ("base/promotion.jl:677", minSameReal)
  ]

end JuliaLean.Pilot.Base.Promotion
