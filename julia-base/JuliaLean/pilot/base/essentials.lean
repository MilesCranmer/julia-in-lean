import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Essentials

open JuliaLean
open JuliaLean.C

/--
Julia source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::Array) = getfield(a, :size)
```
-/
def sizeArray : Body := fun _ args => do
  let [a] := args | throwMethodError "size(a::Array): arity"
  getfieldSym a "size"

/--
Julia source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::AbstractArray) = (@inline; prod(size(t)))
```
-/
def lengthAbstractArray : Body := fun call args => do
  let [t] := args | throwMethodError "length(t::AbstractArray): arity"
  let s ← call "Base.size" [t]
  call "Base.prod" [s]

/--
Julia source: base/essentials.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::GenericMemory) = (getfield(a, :length),)
```
-/
def sizeGenericMemory : Body := fun _ args => do
  let [a] := args | throwMethodError "size(a::GenericMemory): arity"
  let len ← getfieldSym a "length"
  mkTupleR [len]

/--
Julia source: base/essentials.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserror1 : Body := fun _ args => do
  let [_] := args | throwMethodError "throw_boundserror(A): arity"
  throwBoundsError "BoundsError"

/--
Julia source: base/essentials.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, I) = (@noinline; throw(BoundsError(A, I)))
```
-/
def throwBoundserror2 : Body := fun _ args => do
  let [_, _] := args | throwMethodError "throw_boundserror(A, I): arity"
  throwBoundsError "BoundsError"

/--
Julia source: base/essentials.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, i1, i2, I...) = (@noinline; throw(BoundsError(A, (i1, i2, I...))))
```
-/
def throwBoundserrorVar : Body := fun _ args => do
  match args with
  | _ :: _ :: _ :: _ => throwBoundsError "BoundsError"
  | _ => throwMethodError "throw_boundserror(A, i1, i2, I...): arity"

/--
Julia source: base/essentials.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserrorIndices1 : Body := fun _ args => do
  let [_] := args | throwMethodError "_throw_boundserror_indices(A): arity"
  throwBoundsError "BoundsError"

/--
Julia source: base/essentials.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
```
-/
def throwBoundserrorIndicesVar : Body := fun _ args => do
  match args with
  | _ :: _ :: _ => throwBoundsError "BoundsError"
  | _ => throwMethodError "_throw_boundserror_indices(A, i1, I...): arity"

/--
Julia source: base/essentials.jl:385-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
    @inline
    ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
end
```
-/
def checkboundsBoolArrayInt : Body := fun call args => do
  let [_, A, i] := args | throwMethodError "checkbounds(::Type{Bool}, A, i::Int): arity"
  let iv ← asInt i
  let lenObj ← call "Base.length" [A]
  let len ← asInt lenObj
  return mkBool (ultInt64 (wrapInt64 (iv - 1)) len)

/--
Julia source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(A::AbstractArray, I...)
    @inline
    checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
    nothing
end
```
-/
def checkboundsAbstractArray : Body := fun call args => do
  let A :: I := args | throwMethodError "checkbounds(A::AbstractArray, I...): arity"
  let okObj ← call "Base.checkbounds" (.type boolType :: A :: I)
  if !(← asBool okObj) then
    let _ ← call "Base._throw_boundserror_indices" (A :: I)
  return nothingObj

/--
Julia source: base/essentials.jl:400-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::GenericMemory, i::Int)
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i)
    memoryrefget(memoryrefnew(A, i, false), default_access_order(A), false)
end
```
-/
def getindexGenericMemory : Body := fun call args => do
  let [A, i] := args | throwMethodError "getindex(A::GenericMemory, i::Int): arity"
  let _ ← call "Base.checkbounds" [A, i]
  let iv ← asInt i
  let ref ← memoryrefnew A iv false
  memoryrefget ref "not_atomic" false

/--
Julia source: base/essentials.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(A::GenericMemoryRef) = memoryrefget(A, default_access_order(A), @_boundscheck)
```
-/
def getindexGenericMemoryRef : Body := fun _ args => do
  let [A] := args | throwMethodError "getindex(A::GenericMemoryRef): arity"
  memoryrefget A "not_atomic" true

/--
Julia source: base/essentials.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(x::Tuple) = argtail(x...)
```
-/
def tailTuple : Body := fun _ args => do
  let [x] := args | throwMethodError "tail(x::Tuple): arity"
  let xs ← unpackTuple x
  argtail xs

/--
Julia source: base/essentials.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(::Tuple{}) = throw(ArgumentError("Cannot call tail on an empty tuple."))
```
-/
def tailEmptyTuple : Body := fun _ args => do
  let [_] := args | throwMethodError "tail(::Tuple{}): arity"
  throwArgumentError "Cannot call tail on an empty tuple."

/--
Julia source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrap_unionall(@nospecialize(a))
    @_foldable_meta
    while isa(a,UnionAll)
        a = a.body
    end
    return a
end
```
-/
def unwrapUnionall : Body := fun _ args => do
  let [a] := args | throwMethodError "unwrap_unionall(a): arity"
  match a with
  | .type t => return .type t.unwrapUnionall
  | _ => return a

/--
Julia source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
```
-/
def oftypeGeneric : Body := fun call args => do
  let [x, y] := args | throwMethodError "oftype(x, y): arity"
  let tx ← typeOfObj x
  if ← isaObj y tx then
    return y
  else
    let conv ← call "Base.convert" [.type tx, y]
    if !(← isaObj conv tx) then
      throwTypeError "oftype: typeassert failed"
    return conv

/--
Julia source: base/essentials.jl:720-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::Int) = reinterpret(UInt, x)
```
-/
def unsignedInt : Body := fun call args => do
  let [x] := args | throwMethodError "unsigned(x::Int): arity"
  call "Base.reinterpret" [.type uint64Type, x]

/--
Julia source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reinterpret(::Type{Out}, x) where {Out}
    @inline
    if isprimitivetype(Out) && isprimitivetype(typeof(x))
        return bitcast(Out, x)
    end
    # only available when Base is fully loaded.
    return _reinterpret(Out, x)
end
```
-/
def reinterpretType : Body := fun call args => do
  let [.type Out, x] := args | throwMethodError "reinterpret(::Type{Out}, x): arity"
  let outPrimitive ← call "Base.isprimitivetype" [.type Out]
  if ← asBool outPrimitive then
    let tx ← typeOfObj x
    let inPrimitive ← call "Base.isprimitivetype" [.type tx]
    if ← asBool inPrimitive then
      let .bits _ v := x | throwTypeError "bitcast: expected primitive value"
      if Out == uint64Type then return .bits uint64Type (wrapUInt64 v)
      else if Out == int64Type then return .bits int64Type (wrapInt64 v)
      else return .bits Out v
  call "Base._reinterpret" [.type Out, x]

/--
Julia source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, i::Int)
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
end
```
-/
def getindexArrayInt : Body := fun call args => do
  let [A, i] := args | throwMethodError "getindex(A::Array, i::Int): arity"
  let _ ← call "Base.checkbounds" [A, i]
  let ref ← getfieldSym A "ref"
  let iv ← asInt i
  let mref ← memoryrefnew ref iv false
  memoryrefget mref "not_atomic" false

/--
Julia source: base/essentials.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::Int, y::Int) = add_int(x, y)
```
-/
def addInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(+)(x::Int, y::Int): arity"
  return mkInt (wrapInt64 ((← asInt x) + (← asInt y)))

/--
Julia source: base/essentials.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::Int, y::Int) = sub_int(x, y)
```
-/
def subInt : Body := fun _ args => do
  let [x, y] := args | throwMethodError "(-)(x::Int, y::Int): arity"
  return mkInt (wrapInt64 ((← asInt x) - (← asInt y)))

/--
Julia source: base/essentials.jl:1294-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(x::Bool) = not_int(x)
```
-/
def notBool : Body := fun _ args => do
  let [x] := args | throwMethodError "!(x::Bool): arity"
  return mkBool (!(← asBool x))

/--
Julia source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
```
-/
def lengthVector : Body := fun _ args => do
  let [a] := args | throwMethodError "length(a::Array{T,1}): arity"
  let sz ← getfieldSym a "size"
  getfieldIdx sz 1

/--
Julia source: base/essentials.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismissing(x) = x === missing
```
-/
def ismissingAny : Body := fun _ args => do
  let [x] := args | throwMethodError "ismissing(x): arity"
  let ty ← typeOfObj x
  return mkBool (ty == .datatype "Base.Missing" [])

def bodies : List (String × Body) :=
  [ ("base/essentials.jl:12", sizeArray)
  , ("base/essentials.jl:13", lengthAbstractArray)
  , ("base/essentials.jl:14", sizeGenericMemory)
  , ("base/essentials.jl:15", throwBoundserror1)
  , ("base/essentials.jl:16", throwBoundserror2)
  , ("base/essentials.jl:17", throwBoundserrorVar)
  , ("base/essentials.jl:18", throwBoundserrorIndices1)
  , ("base/essentials.jl:19", throwBoundserrorIndicesVar)
  , ("base/essentials.jl:385", checkboundsBoolArrayInt)
  , ("base/essentials.jl:389", checkboundsAbstractArray)
  , ("base/essentials.jl:400", getindexGenericMemory)
  , ("base/essentials.jl:406", getindexGenericMemoryRef)
  , ("base/essentials.jl:541", tailTuple)
  , ("base/essentials.jl:542", tailEmptyTuple)
  , ("base/essentials.jl:544", unwrapUnionall)
  , ("base/essentials.jl:718", oftypeGeneric)
  , ("base/essentials.jl:720", unsignedInt)
  , ("base/essentials.jl:787", reinterpretType)
  , ("base/essentials.jl:1073", getindexArrayInt)
  , ("base/essentials.jl:1267", addInt)
  , ("base/essentials.jl:1268", subInt)
  , ("base/essentials.jl:1294", notBool)
  , ("base/essentials.jl:1296", lengthVector)
  , ("base/essentials.jl:1542", ismissingAny)
  ]

end JuliaLean.Pilot.Base.Essentials
