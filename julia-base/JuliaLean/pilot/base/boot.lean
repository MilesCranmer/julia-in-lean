import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Boot

open JuliaLean
open JuliaLean.C

/--
Julia source: base/boot.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt64(x::Int64)     = x
```
-/
def toInt64Identity : Body := fun _ args => do
  let [x] := args | throwMethodError "toInt64(x::Int64): arity"
  return x

/--
Julia source: base/boot.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt64(x::Bool)      = zext_int(Int64, x)
```
-/
def toInt64Bool : Body := fun _ args => do
  let [x] := args | throwMethodError "toInt64(x::Bool): arity"
  let v ← asInt x
  return mkInt v

/--
Julia source: base/boot.jl:1187-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Int64(x::BuiltinInts)   = toInt64(x)::Int64
```

Julia source: base/boot.jl:1195-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::T) where {T<:Number} = x
```
-/
def int64Ctor : Body := fun call args => do
  let [x] := args | throwMethodError "Int64(x): arity"
  let ty ← typeOfObj x
  if ty == int64Type then
    return x
  else if ty == boolType then
    let result ← call "Core.toInt64" [x]
    if !(← isaObj result int64Type) then throwTypeError "Int64: typeassert failed"
    return result
  else
    throw (.unmodelled s!"unmodelled: Int64 constructor for {repr ty}")

def bodies : List (String × Body) :=
  [ ("base/boot.jl:1107", toInt64Identity)
  , ("base/boot.jl:1114", toInt64Bool)
  , ("Core.Int64", int64Ctor)
  ]

end JuliaLean.Pilot.Base.Boot
