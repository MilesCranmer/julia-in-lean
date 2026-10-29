import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.AnyAll

open JuliaLean
open JuliaLean.C

/--
Julia source: base/anyall.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
all(f, itr) = _all(f, itr, :)
```
-/
def allPredItr : Body := fun call args => do
  let [f, itr] := args | throwMethodError "all(f, itr): arity"
  call "Base._all" [f, itr, colonObj]

/--
Julia source: base/anyall.jl:207-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function _all(f, itr::$ItrT, ::Colon)
        $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
        anymissing = false
        for x in itr
            v = f(x)
            if ismissing(v)
                anymissing = true
            else
                v || return false
            end
        end
        return anymissing ? missing : true
    end
```
-/
def allLoop : Body := fun call args => do
  let [f, itr, _] := args | throwMethodError "_all(f, itr, ::Colon): arity"
  let mut anymissing := false
  let mut next ← call "Base.iterate" [itr]
  for _ in [0:1024] do
    if (← typeOfObj next) == nothingType then
      if anymissing then
        return .imm (.datatype "Base.Missing" []) []
      else
        return mkBool true
    let [x, state] ← unpackTuple next | throwTypeError "iterate: expected 2-tuple"
    let v ← callObj call f [x]
    let m ← call "Base.ismissing" [v]
    if ← asBool m then
      anymissing := true
    else
      if !(← asBool v) then
        return mkBool false
    next ← call "Base.iterate" [itr, state]
  throw (.exc stackOverflowErrorType "_all: iteration budget exhausted")

/--
Julia source: base/anyall.jl:238-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function all(f, itr::Tuple)
    if itr isa NTuple || length(itr) > 32
        return _all(f, itr, :)
    end
    _all_tuple(f, false, itr...)
end
```
-/
def allPredTuple : Body := fun call args => do
  let [f, itr] := args | throwMethodError "all(f, itr::Tuple): arity"
  let elems ← unpackTuple itr
  let isHomogeneous : Bool ← do
    match elems with
    | [] => pure true
    | e0 :: rest =>
      let t0 ← typeOfObj e0
      rest.allM fun e => do return (← typeOfObj e) == t0
  let useLoop ← if isHomogeneous then pure true else do
    let len ← call "Base.length" [itr]
    let gt32 ← call "Base.<" [mkInt 32, len]
    asBool gt32
  if useLoop then
    call "Base._all" [f, itr, colonObj]
  else
    call "Base._all_tuple" (f :: mkBool false :: elems)

/--
Julia source: base/anyall.jl:245-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _all_tuple(f, anymissing::Bool, x, rest...)
    v = f(x)
    if ismissing(v)
        anymissing = true
    # this syntax allows throwing a TypeError for non-Bool, for consistency with any
    elseif v
        nothing
    else
        return false
    end
    return _all_tuple(f, anymissing, rest...)
end
```
-/
def allTupleStep : Body := fun call args => do
  let f :: anymissingObj :: x :: rest := args | throwMethodError "_all_tuple: arity"
  let mut anymissing ← asBool anymissingObj
  let v ← callObj call f [x]
  let m ← call "Base.ismissing" [v]
  if ← asBool m then
    anymissing := true
  else if ← asBool v then
    pure ()
  else
    return mkBool false
  call "Base._all_tuple" (f :: mkBool anymissing :: rest)

/--
Julia source: base/anyall.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
```
-/
def allTupleBase : Body := fun _ args => do
  let [_, anymissingObj] := args | throwMethodError "_all_tuple(_, anymissing::Bool): arity"
  if ← asBool anymissingObj then
    return .imm (.datatype "Base.Missing" []) []
  else
    return mkBool true

def bodies : List (String × Body) :=
  [ ("base/anyall.jl:202", allPredItr)
  , ("base/anyall.jl:207", allLoop)
  , ("base/anyall.jl:238", allPredTuple)
  , ("base/anyall.jl:245", allTupleStep)
  , ("base/anyall.jl:257", allTupleBase)
  ]

end JuliaLean.Pilot.Base.AnyAll
