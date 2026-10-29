import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Operators

open JuliaLean
open JuliaLean.C

/--
Julia source: base/operators.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!=(x, y) = !(x == y)
```
-/
def neGeneric : Body := fun call args => do
  let [x, y] := args | throwMethodError "!=(x, y): arity"
  let eq ← call "Base.==" [x, y]
  call "Base.!" [eq]

/--
Julia source: base/operators.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x, y) = (x < y) | (x == y)
```
-/
def leGeneric : Body := fun call args => do
  let [x, y] := args | throwMethodError "<=(x, y): arity"
  let c1 ← call "Base.<" [x, y]
  let c2 ← call "Base.==" [x, y]
  call "Base.|" [c1, c2]

/--
Julia source: base/operators.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>=(x, y) = (y <= x)
```
-/
def geGeneric : Body := fun call args => do
  let [x, y] := args | throwMethodError ">=(x, y): arity"
  call "Base.<=" [y, x]

/--
Julia source: base/operators.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Number) = x
```
-/
def posNumber : Body := fun _ args => do
  let [x] := args | throwMethodError "+(x::Number): arity"
  return x

/--
Julia source: base/operators.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Number) = x
```
-/
def mulSingleNumber : Body := fun _ args => do
  let [x] := args | throwMethodError "*(x::Number): arity"
  return x

/--
Julia source: base/operators.jl:609-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::Integer) = x
```
-/
def andSingleInteger : Body := fun _ args => do
  let [x] := args | throwMethodError "(&)(x::Integer): arity"
  return x

/--
Julia source: base/operators.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::Integer) = x
```
-/
def orSingleInteger : Body := fun _ args => do
  let [x] := args | throwMethodError "(|)(x::Integer): arity"
  return x

/--
Julia source: base/operators.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
afoldl(op, a) = a
```
-/
def afoldlBase : Body := fun _ args => do
  let [_, a] := args | throwMethodError "afoldl(op, a): arity"
  return a

/--
Julia source: base/operators.jl:623-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function afoldl(op, a, bs...)
    @_terminates_locally_meta
    l = length(bs)
    i =  0; y = a;            l == i && return y
    #@nexprs 31 i -> (y = op(y, bs[i]); l == i && return y)
    i =  1; y = op(y, bs[i]); l == i && return y
    i =  2; y = op(y, bs[i]); l == i && return y
    i =  3; y = op(y, bs[i]); l == i && return y
    i =  4; y = op(y, bs[i]); l == i && return y
    i =  5; y = op(y, bs[i]); l == i && return y
    i =  6; y = op(y, bs[i]); l == i && return y
    i =  7; y = op(y, bs[i]); l == i && return y
    i =  8; y = op(y, bs[i]); l == i && return y
    i =  9; y = op(y, bs[i]); l == i && return y
    i = 10; y = op(y, bs[i]); l == i && return y
    i = 11; y = op(y, bs[i]); l == i && return y
    i = 12; y = op(y, bs[i]); l == i && return y
    i = 13; y = op(y, bs[i]); l == i && return y
    i = 14; y = op(y, bs[i]); l == i && return y
    i = 15; y = op(y, bs[i]); l == i && return y
    i = 16; y = op(y, bs[i]); l == i && return y
    i = 17; y = op(y, bs[i]); l == i && return y
    i = 18; y = op(y, bs[i]); l == i && return y
    i = 19; y = op(y, bs[i]); l == i && return y
    i = 20; y = op(y, bs[i]); l == i && return y
    i = 21; y = op(y, bs[i]); l == i && return y
    i = 22; y = op(y, bs[i]); l == i && return y
    i = 23; y = op(y, bs[i]); l == i && return y
    i = 24; y = op(y, bs[i]); l == i && return y
    i = 25; y = op(y, bs[i]); l == i && return y
    i = 26; y = op(y, bs[i]); l == i && return y
    i = 27; y = op(y, bs[i]); l == i && return y
    i = 28; y = op(y, bs[i]); l == i && return y
    i = 29; y = op(y, bs[i]); l == i && return y
    i = 30; y = op(y, bs[i]); l == i && return y
    i = 31; y = op(y, bs[i]); l == i && return y
    for i in (i + 1):l
        y = op(y, bs[i])
    end
    return y
end
```
-/
def afoldlStep : Body := fun call args => do
  let op :: a :: bs := args | throwMethodError "afoldl(op, a, bs...): arity"
  let mut y := a
  for b in bs do
    y ← callObj call op [y, b]
  return y

/--
Julia source: base/operators.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op)(a, b, c, xs...) = (@inline; afoldl($op, ($op)(($op)(a,b),c), xs...))
```
-/
def opVararg : Body := fun call args => do
  let a :: b :: c :: xs := args | throwMethodError "op(a, b, c, xs...): arity"
  let self ← getSelf
  let ab ← callObj call self [a, b]
  let abc ← callObj call self [ab, c]
  call "Base.afoldl" (self :: abc :: xs)

/--
Julia source: base/operators.jl:1035-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(obj::Returns)(@nospecialize(args...); @nospecialize(kw...)) = obj.value
```
-/
def returnsCall : Body := fun _ _ => do
  let obj ← getSelf
  getfieldIdx obj 1

def bodies : List (String × Body) :=
  [ ("base/operators.jl:338", neGeneric)
  , ("base/operators.jl:467", leGeneric)
  , ("base/operators.jl:499", geGeneric)
  , ("base/operators.jl:607", posNumber)
  , ("base/operators.jl:608", mulSingleNumber)
  , ("base/operators.jl:609", andSingleInteger)
  , ("base/operators.jl:610", orSingleInteger)
  , ("base/operators.jl:622", afoldlBase)
  , ("base/operators.jl:623", afoldlStep)
  , ("base/operators.jl:671", opVararg)
  , ("base/operators.jl:1035", returnsCall)
  ]

end JuliaLean.Pilot.Base.Operators
