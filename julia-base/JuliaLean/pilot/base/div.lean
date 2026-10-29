import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Div

open JuliaLean
open JuliaLean.C

/-- `Base.RoundToZero` (`RoundingMode{:ToZero}()`). -/
def roundToZeroObj : Obj :=
  .imm (.datatype "Base.Rounding.RoundingMode" [.symbol "ToZero"]) []

def roundDownObj : Obj :=
  .imm (.datatype "Base.Rounding.RoundingMode" [.symbol "Down"]) []

def roundUpObj : Obj :=
  .imm (.datatype "Base.Rounding.RoundingMode" [.symbol "Up"]) []

/--
Julia source: base/div.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
divrem(x, y) = divrem(x, y, RoundToZero)
```
-/
def divrem2 : Body := fun call args => do
  let [x, y] := args | throwMethodError "divrem(x, y): arity"
  call "Base.divrem" [x, y, roundToZeroObj]

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
def divremIntegerMode : Body := fun call args => do
  let [a, b, mode] := args | throwMethodError "divrem(a::Integer, b::Integer, r): arity"
  if mode == roundToZeroObj then
    let d ← call "Base.div" [a, b]
    let db ← call "Base.*" [d, b]
    let rem ← call "Base.-" [a, db]
    mkTupleR [d, rem]
  else if mode == roundDownObj then
    let d ← call "Base.fld" [a, b]
    let db ← call "Base.*" [d, b]
    let rem ← call "Base.-" [a, db]
    mkTupleR [d, rem]
  else if mode == roundUpObj then
    let d ← call "Base.div" [a, b, mode]
    let db ← call "Base.*" [d, b]
    let rem ← call "Base.-" [a, db]
    mkTupleR [d, rem]
  else
    return nothingObj

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
def divremBitSignedMode : Body := fun call args => do
  let [a, b, mode] := args | throwMethodError "divrem(a::T, b::T, r): arity"
  if mode == roundToZeroObj then
    let d ← call "Base.div" [a, b]
    let db ← call "Base.*" [d, b]
    let rem ← call "Base.-" [a, db]
    mkTupleR [d, rem]
  else if mode == roundDownObj then
    let d ← call "Base.fld" [a, b]
    let db ← call "Base.*%" [d, b]
    let rem ← call "Base.-%" [a, db]
    mkTupleR [d, rem]
  else if mode == roundUpObj then
    let d ← call "Base.div" [a, b, mode]
    let db ← call "Base.*%" [d, b]
    let rem ← call "Base.-%" [a, db]
    mkTupleR [d, rem]
  else
    return nothingObj

def bodies : List (String × Body) :=
  [ ("base/div.jl:273", divrem2)
  , ("base/div.jl:290", divremIntegerMode)
  , ("base/div.jl:312", divremBitSignedMode)
  ]

end JuliaLean.Pilot.Base.Div
