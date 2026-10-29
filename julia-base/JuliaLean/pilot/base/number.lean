import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Number

open JuliaLean
open JuliaLean.C

/--
Julia source: base/number.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T)      where {T<:Number} = x
```
-/
def convertSameNumber : Body := fun _ args => do
  let [_, x] := args | throwMethodError "convert(::Type{T}, x::T): arity"
  return x

/--
Julia source: base/number.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::Number) where {T<:Number} = T(x)::T
```
-/
def convertOtherNumber : Body := fun call args => do
  let [T, x] := args | throwMethodError "convert(::Type{T}, x::Number): arity"
  callObj call T [x]

/--
Julia source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(x::Number) = oftype(x,0)
```
-/
def zeroNumber : Body := fun call args => do
  let [x] := args | throwMethodError "zero(x::Number): arity"
  call "Base.oftype" [x, mkInt 0]

/--
Julia source: base/number.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zero(::Type{T}) where {T<:Number} = convert(T,0)
```
-/
def zeroType : Body := fun call args => do
  let [T] := args | throwMethodError "zero(::Type{T}): arity"
  call "Base.convert" [T, mkInt 0]

/--
Julia source: base/number.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(::Type{T}) where {T<:Number} = convert(T,1)
```
-/
def oneType : Body := fun call args => do
  let [T] := args | throwMethodError "one(::Type{T}): arity"
  call "Base.convert" [T, mkInt 1]

/--
Julia source: base/number.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(x::T) where {T<:Number} = one(T)
```
-/
def oneNumber : Body := fun call args => do
  let [x] := args | throwMethodError "one(x::T): arity"
  let T ← typeOfObj x
  call "Base.one" [.type T]

/--
Julia source: base/number.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(x::T) where {T} = T(one(x))
```
-/
def oneunitVal : Body := fun call args => do
  let [x] := args | throwMethodError "oneunit(x::T): arity"
  let T ← typeOfObj x
  let o ← call "Base.one" [x]
  callObj call (.type T) [o]

/--
Julia source: base/number.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneunit(::Type{T}) where {T} = T(one(T))
```
-/
def oneunitType : Body := fun call args => do
  let [T] := args | throwMethodError "oneunit(::Type{T}): arity"
  let o ← call "Base.one" [T]
  callObj call T [o]

def bodies : List (String × Body) :=
  [ ("base/number.jl:6", convertSameNumber)
  , ("base/number.jl:7", convertOtherNumber)
  , ("base/number.jl:363", zeroNumber)
  , ("base/number.jl:364", zeroType)
  , ("base/number.jl:405", oneType)
  , ("base/number.jl:406", oneNumber)
  , ("base/number.jl:430", oneunitVal)
  , ("base/number.jl:431", oneunitType)
  ]

end JuliaLean.Pilot.Base.Number
