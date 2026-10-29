import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Bool

open JuliaLean
open JuliaLean.C

/--
Julia source: base/bool.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(x::Bool, y::Bool) = and_int(x, y)
```
-/
def andBool : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(&)(x::Bool, y::Bool): arity"
  return mkBool ((← asBool x) && (← asBool y))

/--
Julia source: base/bool.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(|)(x::Bool, y::Bool) = or_int(x, y)
```
-/
def orBool : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(|)(x::Bool, y::Bool): arity"
  return mkBool ((← asBool x) || (← asBool y))

/--
Julia source: base/bool.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::Bool, y::Bool) = y&!x
```
-/
def ltBool : Body := fun call args => do
  let [x, y] := args | throwMethodError "<(x::Bool, y::Bool): arity"
  let nx ← call "Base.!" [x]
  call "Base.&" [y, nx]

/--
Julia source: base/bool.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Bool, y::Bool) = y|!x
```
-/
def leBool : Body := fun call args => do
  let [x, y] := args | throwMethodError "<=(x::Bool, y::Bool): arity"
  let nx ← call "Base.!" [x]
  call "Base.|" [y, nx]

/--
Julia source: base/bool.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Bool)  =    Int(x)
```
-/
def posBool : Body := fun call args => do
  let [x] := args | throwMethodError "+(x::Bool): arity"
  call "Core.Int64" [x]

/--
Julia source: base/bool.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool)  = -%(Int(x))
```
-/
def negBool : Body := fun call args => do
  let [x] := args | throwMethodError "-(x::Bool): arity"
  let ix ← call "Core.Int64" [x]
  call "Base.-%" [ix]

/--
Julia source: base/bool.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Bool) = -%(Int(x))
```
-/
def negWrapBool : Body := negBool

/--
Julia source: base/bool.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Bool, y::Bool) = Int(x) +% Int(y)
```
-/
def addBool : Body := fun call args => do
  let [x, y] := args | throwMethodError "+(x::Bool, y::Bool): arity"
  let ix ← call "Core.Int64" [x]
  let iy ← call "Core.Int64" [y]
  call "Base.+" [ix, iy]

/--
Julia source: base/bool.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Bool, y::Bool) = Int(x) -% Int(y)
```
-/
def subBool : Body := fun call args => do
  let [x, y] := args | throwMethodError "-(x::Bool, y::Bool): arity"
  let ix ← call "Core.Int64" [x]
  let iy ← call "Core.Int64" [y]
  call "Base.-%" [ix, iy]

/--
Julia source: base/bool.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Bool, y::Bool) = Int(x) -% Int(y)
```
-/
def subWrapBool : Body := subBool

/--
Julia source: base/bool.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::Bool, y::Bool) = x & y
```
-/
def mulBool : Body := fun call args => do
  let [x, y] := args | throwMethodError "*(x::Bool, y::Bool): arity"
  call "Base.&" [x, y]

def bodies : List (String × Body) :=
  [ ("base/bool.jl:14", andBool)
  , ("base/bool.jl:15", orBool)
  , ("base/bool.jl:135", ltBool)
  , ("base/bool.jl:136", leBool)
  , ("base/bool.jl:140", posBool)
  , ("base/bool.jl:142", negBool)
  , ("base/bool.jl:143", negWrapBool)
  , ("base/bool.jl:145", addBool)
  , ("base/bool.jl:146", subBool)
  , ("base/bool.jl:148", subWrapBool)
  , ("base/bool.jl:149", mulBool)
  ]

end JuliaLean.Pilot.Base.Bool
