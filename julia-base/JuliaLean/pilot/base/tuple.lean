import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Tuple

open JuliaLean
open JuliaLean.C

/--
Julia source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(@nospecialize t::Tuple) = nfields(t)
```
-/
def lengthTuple : Body := fun _ args => do
  let [t] := args | throwMethodError "length(t::Tuple): arity"
  return mkInt (← nfieldsObj t)

/--
Julia source: base/tuple.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(@nospecialize t::Tuple) = 1
```
-/
def firstindexTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "firstindex(t::Tuple): arity"
  return mkInt 1

/--
Julia source: base/tuple.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(@nospecialize t::Tuple) = length(t)
```
-/
def lastindexTuple : Body := fun call args => do
  let [t] := args | throwMethodError "lastindex(t::Tuple): arity"
  call "Base.length" [t]

/--
Julia source: base/tuple.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(@nospecialize(t::Tuple), d::Integer) = (d == 1) ? length(t) : throw(ArgumentError("invalid tuple dimension $d"))
```
-/
def sizeTupleDim : Body := fun call args => do
  let [t, d] := args | throwMethodError "size(t::Tuple, d::Integer): arity"
  let eq ← call "Base.==" [d, mkInt 1]
  if ← asBool eq then
    call "Base.length" [t]
  else
    throwArgumentError "invalid tuple dimension"

/--
Julia source: base/tuple.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(@nospecialize t::Tuple) = (OneTo(length(t)),)
```
-/
def axesTuple : Body := fun call args => do
  let [t] := args | throwMethodError "axes(t::Tuple): arity"
  let len ← call "Base.length" [t]
  let r ← call "Base.OneTo" [len]
  mkTupleR [r]

/--
Julia source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
```
-/
def getindexTupleInt : Body := fun _ args => do
  let [t, i] := args | throwMethodError "getindex(t::Tuple, i::Int): arity"
  getfieldIdx t (← asInt i) true

/--
Julia source: base/tuple.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(@nospecialize(t::Tuple), i::Integer) = getfield(t, convert(Int, i), @_boundscheck)
```
-/
def getindexTupleInteger : Body := fun call args => do
  let [t, i] := args | throwMethodError "getindex(t::Tuple, i::Integer): arity"
  let idx ← call "Base.convert" [.type int64Type, i]
  getfieldIdx t (← asInt idx) true

/--
Julia source: base/tuple.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(t::Tuple, i::Integer, default) = i in 1:length(t) ? getindex(t, i) : default
```
-/
def getTupleDefault : Body := fun call args => do
  let [t, i, defaultVal] := args | throwMethodError "get(t::Tuple, i::Integer, default): arity"
  let len ← call "Base.length" [t]
  let rng ← call "Base.:" [mkInt 1, len]
  let cond ← call "Base.in" [i, rng]
  if ← asBool cond then
    call "Base.getindex" [t, i]
  else
    return defaultVal

/--
Julia source: base/tuple.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(@nospecialize(t::Tuple), i::Int=1)
    @inline
    @_nothrow_meta
    return (1 <= i <= length(t)) ? (t[i], i + 1) : nothing
end
```
-/
def iterateTuple : Body := fun call args => do
  match args with
  | [t] => call "Base.iterate" [t, mkInt 1]
  | [t, i] =>
    let c1 ← call "Base.<=" [mkInt 1, i]
    if !(← asBool c1) then
      return nothingObj
    let len ← call "Base.length" [t]
    let c2 ← call "Base.<=" [i, len]
    if ← asBool c2 then
      let elem ← call "Base.getindex" [t, i]
      let nextI ← call "Base.+" [i, mkInt 1]
      mkTupleR [elem, nextI]
    else
      return nothingObj
  | _ => throwMethodError "iterate(t::Tuple, [i::Int]): arity"

/--
Julia source: base/tuple.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(::Tuple{}) = throw(ArgumentError("tuple must be non-empty"))
```
-/
def firstEmptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "first(::Tuple{}): arity"
  throwArgumentError "tuple must be non-empty"

/--
Julia source: base/tuple.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(t::Tuple) = t[1]
```
-/
def firstTuple : Body := fun call args => do
  let [t] := args | throwMethodError "first(t::Tuple): arity"
  call "Base.getindex" [t, mkInt 1]

/--
Julia source: base/tuple.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
safe_tail(t::Tuple) = tail(t)
```
-/
def safeTailTuple : Body := fun call args => do
  let [t] := args | throwMethodError "safe_tail(t::Tuple): arity"
  call "Base.tail" [t]

/--
Julia source: base/tuple.jl:324-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
safe_tail(t::Tuple{}) = ()
```
-/
def safeTailEmptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "safe_tail(t::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/tuple.jl:344-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function front(t::Tuple)
    @inline
    _front(t...)
end
```
-/
def frontTuple : Body := fun call args => do
  let [t] := args | throwMethodError "front(t::Tuple): arity"
  let elems ← unpackTuple t
  call "Base._front" elems

/--
Julia source: base/tuple.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_front() = throw(ArgumentError("Cannot call front on an empty tuple."))
```
-/
def frontHelper0 : Body := fun _ args => do
  let [] := args | throwMethodError "_front(): arity"
  throwArgumentError "Cannot call front on an empty tuple."

/--
Julia source: base/tuple.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_front(v) = ()
```
-/
def frontHelper1 : Body := fun _ args => do
  let [_] := args | throwMethodError "_front(v): arity"
  mkTupleR []

/--
Julia source: base/tuple.jl:350-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _front(v, t...)
    @inline
    (v, _front(t...)...)
end
```
-/
def frontHelperVar : Body := fun call args => do
  let v :: t := args | throwMethodError "_front(v, t...): arity"
  let restTup ← call "Base._front" t
  let rest ← unpackTuple restTup
  mkTupleR (v :: rest)

/--
Julia source: base/tuple.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{})              = ()
```
-/
def mapTuple0 : Body := fun _ args => do
  let [_, _] := args | throwMethodError "map(f, t::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/tuple.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any,})          = (@inline; (f(t[1]),))
```
-/
def mapTuple1 : Body := fun call args => do
  let [f, t] := args | throwMethodError "map(f, t::Tuple{Any}): arity"
  let t1 ← call "Base.getindex" [t, mkInt 1]
  let r1 ← callObj call f [t1]
  mkTupleR [r1]

/--
Julia source: base/tuple.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any, Any})      = (@inline; (f(t[1]), f(t[2])))
```
-/
def mapTuple2 : Body := fun call args => do
  let [f, t] := args | throwMethodError "map(f, t::Tuple{Any, Any}): arity"
  let t1 ← call "Base.getindex" [t, mkInt 1]
  let r1 ← callObj call f [t1]
  let t2 ← call "Base.getindex" [t, mkInt 2]
  let r2 ← callObj call f [t2]
  mkTupleR [r1, r2]

/--
Julia source: base/tuple.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple{Any, Any, Any}) = (@inline; (f(t[1]), f(t[2]), f(t[3])))
```
-/
def mapTuple3 : Body := fun call args => do
  let [f, t] := args | throwMethodError "map(f, t::Tuple{Any, Any, Any}): arity"
  let t1 ← call "Base.getindex" [t, mkInt 1]
  let r1 ← callObj call f [t1]
  let t2 ← call "Base.getindex" [t, mkInt 2]
  let r2 ← callObj call f [t2]
  let t3 ← call "Base.getindex" [t, mkInt 3]
  let r3 ← callObj call f [t3]
  mkTupleR [r1, r2, r3]

/--
Julia source: base/tuple.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, t::Tuple)                = (@inline; (f(t[1]), map(f,tail(t))...))
```
-/
def mapTupleVar : Body := fun call args => do
  let [f, t] := args | throwMethodError "map(f, t::Tuple): arity"
  let t1 ← call "Base.getindex" [t, mkInt 1]
  let r1 ← callObj call f [t1]
  let tt ← call "Base.tail" [t]
  let restTup ← call "Base.map" [f, tt]
  let rest ← unpackTuple restTup
  mkTupleR (r1 :: rest)

/--
Julia source: base/tuple.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(x::Tuple{}) = true
```
-/
def isemptyEmptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "isempty(x::Tuple{}): arity"
  return mkBool true

/--
Julia source: base/tuple.jl:666-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(@nospecialize x::Tuple) = false
```
-/
def isemptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "isempty(x::Tuple): arity"
  return mkBool false

/--
Julia source: base/tuple.jl:688-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(x::Tuple{}) = 1
```
-/
def prodEmptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "prod(x::Tuple{}): arity"
  return mkInt 1

/--
Julia source: base/tuple.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
```
-/
def prodIntTuple : Body := fun call args => do
  let [x] := args | throwMethodError "prod(x::Tuple{Int, Vararg{Int}}): arity"
  let xs ← unpackTuple x
  call "Base.*" xs

def bodies : List (String × Body) :=
  [ ("base/tuple.jl:28", lengthTuple)
  , ("base/tuple.jl:29", firstindexTuple)
  , ("base/tuple.jl:30", lastindexTuple)
  , ("base/tuple.jl:31", sizeTupleDim)
  , ("base/tuple.jl:32", axesTuple)
  , ("base/tuple.jl:33", getindexTupleInt)
  , ("base/tuple.jl:34", getindexTupleInteger)
  , ("base/tuple.jl:40", getTupleDefault)
  , ("base/tuple.jl:69", iterateTuple)
  , ("base/tuple.jl:270", firstEmptyTuple)
  , ("base/tuple.jl:271", firstTuple)
  , ("base/tuple.jl:323", safeTailTuple)
  , ("base/tuple.jl:324", safeTailEmptyTuple)
  , ("base/tuple.jl:344", frontTuple)
  , ("base/tuple.jl:348", frontHelper0)
  , ("base/tuple.jl:349", frontHelper1)
  , ("base/tuple.jl:350", frontHelperVar)
  , ("base/tuple.jl:358", mapTuple0)
  , ("base/tuple.jl:359", mapTuple1)
  , ("base/tuple.jl:360", mapTuple2)
  , ("base/tuple.jl:361", mapTuple3)
  , ("base/tuple.jl:362", mapTupleVar)
  , ("base/tuple.jl:665", isemptyEmptyTuple)
  , ("base/tuple.jl:666", isemptyTuple)
  , ("base/tuple.jl:688", prodEmptyTuple)
  , ("base/tuple.jl:693", prodIntTuple)
  ]

end JuliaLean.Pilot.Base.Tuple
