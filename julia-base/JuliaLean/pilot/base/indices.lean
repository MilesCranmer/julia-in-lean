import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Indices

open JuliaLean
open JuliaLean.C

/--
Julia source: base/indices.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(A::AbstractArray) = IndexStyle(typeof(A))
```
-/
def indexStyleAbstractArray : Body := fun call args => do
  let [A] := args | throwMethodError "IndexStyle(A::AbstractArray): arity"
  let ty ← typeOfObj A
  call "Base.IndexStyle" [.type ty]

/--
Julia source: base/indices.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{Union{}}) = IndexLinear()
```
-/
def indexStyleBottom : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{Union{}}): arity"
  return indexLinearObj

/--
Julia source: base/indices.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{Union{}}, slurp...) = throw(MethodError(IndexStyle, (Union{}, slurp...)))
```
-/
def indexStyleBottomSlurp : Body := fun _ _ =>
  throwMethodError "IndexStyle(::Type{Union{}}, slurp...)"

/--
Julia source: base/indices.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:AbstractArray}) = IndexCartesian()
```
-/
def indexStyleTypeAbstractArray : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{<:AbstractArray}): arity"
  return indexCartesianObj

/--
Julia source: base/indices.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:Array}) = IndexLinear()
```
-/
def indexStyleTypeArray : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{<:Array}): arity"
  return indexLinearObj

/--
Julia source: base/indices.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:AbstractRange}) = IndexLinear()
```
-/
def indexStyleTypeRange : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{<:AbstractRange}): arity"
  return indexLinearObj

/--
Julia source: base/indices.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(A::AbstractArray, B::AbstractArray) = IndexStyle(IndexStyle(A), IndexStyle(B))
```
-/
def indexStyleTwo : Body := fun call args => do
  let [A, B] := args | throwMethodError "IndexStyle(A, B): arity"
  let sA ← call "Base.IndexStyle" [A]
  let sB ← call "Base.IndexStyle" [B]
  call "Base.IndexStyle" [sA, sB]

/--
Julia source: base/indices.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(A::AbstractArray, B::AbstractArray...) = IndexStyle(IndexStyle(A), IndexStyle(B...))
```
-/
def indexStyleVararg : Body := fun call args => do
  let A :: B := args | throwMethodError "IndexStyle(A, B...): arity"
  let sA ← call "Base.IndexStyle" [A]
  let sB ← call "Base.IndexStyle" B
  call "Base.IndexStyle" [sA, sB]

/--
Julia source: base/indices.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexLinear, ::IndexLinear) = IndexLinear()
```
-/
def indexStyleLinearLinear : Body := fun _ args => do
  let [_, _] := args | throwMethodError "IndexStyle(::IndexLinear, ::IndexLinear): arity"
  return indexLinearObj

/--
Julia source: base/indices.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexStyle, ::IndexStyle) = IndexCartesian()
```
-/
def indexStyleFallback : Body := fun _ args => do
  let [_, _] := args | throwMethodError "IndexStyle(::IndexStyle, ::IndexStyle): arity"
  return indexCartesianObj

/--
Julia source: base/indices.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(A, i) = to_index(i)
```
-/
def toIndex2 : Body := fun call args => do
  let [_, i] := args | throwMethodError "to_index(A, i): arity"
  call "Base.to_index" [i]

/--
Julia source: base/indices.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(A::Array, i::UInt) = reinterpret(Int, i)
```
-/
def toIndexArrayUInt : Body := fun call args => do
  let [_, i] := args | throwMethodError "to_index(A::Array, i::UInt): arity"
  call "Base.reinterpret" [.type int64Type, i]

/--
Julia source: base/indices.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i::Integer) = convert(Int,i)::Int
```
-/
def toIndexInteger : Body := fun call args => do
  let [i] := args | throwMethodError "to_index(i::Integer): arity"
  let r ← call "Base.convert" [.type int64Type, i]
  if !(← isaObj r int64Type) then
    throwTypeError "to_index: expected Int"
  return r

/--
Julia source: base/indices.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i::Bool) = throw(ArgumentError("invalid index: $i of type Bool"))
```
-/
def toIndexBool : Body := fun _ args => do
  let [_] := args | throwMethodError "to_index(i::Bool): arity"
  throwArgumentError "invalid index of type Bool"

/--
Julia source: base/indices.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(::Colon) = throw(ArgumentError("colons must be converted by to_indices(...)"))
```
-/
def toIndexColon : Body := fun _ args => do
  let [_] := args | throwMethodError "to_index(::Colon): arity"
  throwArgumentError "colons must be converted by to_indices(...)"

/--
Julia source: base/indices.jl:266-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i) = throw(ArgumentError(LazyString("invalid index: ", limitrepr(i), " of type ", typeof(i))))
```
-/
def toIndexFallback : Body := fun _ args => do
  let [_] := args | throwMethodError "to_index(i): arity"
  throwArgumentError "invalid index"

/--
Julia source: base/indices.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple) = (@inline; _to_indices(A, _drop_zerodim(I), I))
```
-/
def toIndicesTuple : Body := fun call args => do
  let [A, I] := args | throwMethodError "to_indices(A, I::Tuple): arity"
  let dropped ← call "Base._drop_zerodim" [I]
  call "Base._to_indices" [A, dropped, I]

/--
Julia source: base/indices.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Any}) = (@inline; to_indices(A, (eachindex(IndexLinear(), A),), I))
```
-/
def toIndicesTuple1 : Body := fun call args => do
  let [A, I] := args | throwMethodError "to_indices(A, I::Tuple{Any}): arity"
  let ei ← call "Base.eachindex" [indexLinearObj, A]
  let inds ← mkTupleR [ei]
  call "Base.to_indices" [A, inds, I]

/--
Julia source: base/indices.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_indices(A, ::Tuple, I::Tuple) = (@inline; to_indices(A, axes(A), I))
```
-/
def toIndicesHelperTuple : Body := fun call args => do
  let [A, _, I] := args | throwMethodError "_to_indices(A, ::Tuple, I::Tuple): arity"
  let ax ← call "Base.axes" [A]
  call "Base.to_indices" [A, ax, I]

/--
Julia source: base/indices.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_indices(A, J::Tuple{Any}, ::Tuple) = (@inline; to_indices(A, J))
```
-/
def toIndicesHelperTuple1 : Body := fun call args => do
  let [A, J, _] := args | throwMethodError "_to_indices(A, J::Tuple{Any}, ::Tuple): arity"
  call "Base.to_indices" [A, J]

/--
Julia source: base/indices.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(::Tuple{}) = ()
```
-/
def dropZerodimEmpty : Body := fun _ args => do
  let [_] := args | throwMethodError "_drop_zerodim(::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/indices.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(I::Tuple) = (@inline; (I[1], _drop_zerodim(tail(I))...))
```
-/
def dropZerodimTuple : Body := fun call args => do
  let [I] := args | throwMethodError "_drop_zerodim(I::Tuple): arity"
  let i1 ← call "Base.getindex" [I, mkInt 1]
  let tI ← call "Base.tail" [I]
  let restTup ← call "Base._drop_zerodim" [tI]
  let rest ← unpackTuple restTup
  mkTupleR (i1 :: rest)

/--
Julia source: base/indices.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{}) = ()
```
-/
def toIndicesEmpty : Body := fun _ args => do
  let [_, _] := args | throwMethodError "to_indices(A, I::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/indices.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Vararg{Int}}) = I
```
-/
def toIndicesInts : Body := fun _ args => do
  let [_, I] := args | throwMethodError "to_indices(A, I::Tuple{Vararg{Int}}): arity"
  return I

/--
Julia source: base/indices.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, I::Tuple{Vararg{Integer}}) = (@inline; to_indices(A, (), I))
```
-/
def toIndicesIntegers : Body := fun call args => do
  let [A, I] := args | throwMethodError "to_indices(A, I::Tuple{Vararg{Integer}}): arity"
  let emptyTup ← mkTupleR []
  call "Base.to_indices" [A, emptyTup, I]

/--
Julia source: base/indices.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, inds, ::Tuple{}) = ()
```
-/
def toIndices3Empty : Body := fun _ args => do
  let [_, _, _] := args | throwMethodError "to_indices(A, inds, ::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/indices.jl:322-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_indices(A, inds, I::Tuple{Any, Vararg}) =
    (@inline; (to_index(A, I[1]), to_indices(A, safe_tail(inds), tail(I))...))
```
-/
def toIndices3Cons : Body := fun call args => do
  let [A, inds, I] := args | throwMethodError "to_indices(A, inds, I::Tuple{Any, Vararg}): arity"
  let i1 ← call "Base.getindex" [I, mkInt 1]
  let idx1 ← call "Base.to_index" [A, i1]
  let indsTail ← call "Base.safe_tail" [inds]
  let iTail ← call "Base.tail" [I]
  let restTup ← call "Base.to_indices" [A, indsTail, iTail]
  let rest ← unpackTuple restTup
  mkTupleR (idx1 :: rest)

/--
Julia source: base/indices.jl:482-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LinearIndices(::Tuple{}) = LinearIndices{0,typeof(())}(())
LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}}) where {N} =
    LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))
LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}}) where {N} =
    LinearIndices(map(_convert2ind, inds))
LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))
```
-/
def linearIndicesCtor : Body := fun call args => do
  let [arg] := args | throwMethodError "LinearIndices: arity"
  let ty ← typeOfObj arg
  if ty.name? == some tupleName then
    let elems ← unpackTuple arg
    let n := Int.ofNat elems.length
    let rTy ← typeOfObj arg
    return .imm (.datatype "Base.LinearIndices" [.long n, rTy]) [arg]
  else
    let ax ← call "Base.axes" [arg]
    call "Base.LinearIndices" [ax]

/--
Julia source: base/indices.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_convert2ind(i::Integer) = oneto(i)
```
-/
def convert2indInteger : Body := fun call args => do
  let [i] := args | throwMethodError "_convert2ind(i::Integer): arity"
  call "Base.oneto" [i]

/--
Julia source: base/indices.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_convert2ind(ind::AbstractUnitRange) = first(ind):last(ind)
```
-/
def convert2indUnitRange : Body := fun call args => do
  let [ind] := args | throwMethodError "_convert2ind(ind::AbstractUnitRange): arity"
  let f ← call "Base.first" [ind]
  let l ← call "Base.last" [ind]
  call "Base.:" [f, l]

/--
Julia source: base/indices.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:LinearIndices}) = IndexLinear()
```
-/
def indexStyleLinearIndices : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{<:LinearIndices}): arity"
  return indexLinearObj

/--
Julia source: base/indices.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(iter::LinearIndices) = map(axes1, iter.indices)
```
-/
def axesLinearIndices : Body := fun call args => do
  let [iter] := args | throwMethodError "axes(iter::LinearIndices): arity"
  let inds ← getfieldSym iter "indices"
  call "Base.map" [.fn "Base.axes1", inds]

/--
Julia source: base/indices.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(iter::LinearIndices) = map(length, iter.indices)
```
-/
def sizeLinearIndices : Body := fun call args => do
  let [iter] := args | throwMethodError "size(iter::LinearIndices): arity"
  let inds ← getfieldSym iter "indices"
  call "Base.map" [.fn "Base.length", inds]

/--
Julia source: base/indices.jl:509-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(iter::LinearIndices, i::Int)
    @inline
    @boundscheck checkbounds(iter, i)
    i
end
```
-/
def getindexLinearIndicesInt : Body := fun call args => do
  let [iter, i] := args | throwMethodError "getindex(iter::LinearIndices, i::Int): arity"
  let _ ← call "Base.checkbounds" [iter, i]
  return i

/--
Julia source: base/indices.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(iter::LinearIndices) = 1
```
-/
def firstLinearIndices : Body := fun _ args => do
  let [_] := args | throwMethodError "first(iter::LinearIndices): arity"
  return mkInt 1

/--
Julia source: base/indices.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(iter::LinearIndices{1}) = (@inline; first(axes1(iter.indices[1])))
```
-/
def firstLinearIndices1 : Body := fun call args => do
  let [iter] := args | throwMethodError "first(iter::LinearIndices{1}): arity"
  let inds ← getfieldSym iter "indices"
  let ind1 ← call "Base.getindex" [inds, mkInt 1]
  let ax1 ← call "Base.axes1" [ind1]
  call "Base.first" [ax1]

/--
Julia source: base/indices.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::LinearIndices) = (@inline; length(iter))
```
-/
def lastLinearIndices : Body := fun call args => do
  let [iter] := args | throwMethodError "last(iter::LinearIndices): arity"
  call "Base.length" [iter]

/--
Julia source: base/indices.jl:529-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::LinearIndices{1}) = (@inline; last(axes1(iter.indices[1])))
```
-/
def lastLinearIndices1 : Body := fun call args => do
  let [iter] := args | throwMethodError "last(iter::LinearIndices{1}): arity"
  let inds ← getfieldSym iter "indices"
  let ind1 ← call "Base.getindex" [inds, mkInt 1]
  let ax1 ← call "Base.axes1" [ind1]
  call "Base.last" [ax1]

def bodies : List (String × Body) :=
  [ ("base/indices.jl:94", indexStyleAbstractArray)
  , ("base/indices.jl:95", indexStyleBottom)
  , ("base/indices.jl:96", indexStyleBottomSlurp)
  , ("base/indices.jl:97", indexStyleTypeAbstractArray)
  , ("base/indices.jl:98", indexStyleTypeArray)
  , ("base/indices.jl:99", indexStyleTypeRange)
  , ("base/indices.jl:101", indexStyleTwo)
  , ("base/indices.jl:102", indexStyleVararg)
  , ("base/indices.jl:103", indexStyleLinearLinear)
  , ("base/indices.jl:104", indexStyleFallback)
  , ("base/indices.jl:243", toIndex2)
  , ("base/indices.jl:247", toIndexArrayUInt)
  , ("base/indices.jl:258", toIndexInteger)
  , ("base/indices.jl:259", toIndexBool)
  , ("base/indices.jl:265", toIndexColon)
  , ("base/indices.jl:266", toIndexFallback)
  , ("base/indices.jl:310", toIndicesTuple)
  , ("base/indices.jl:311", toIndicesTuple1)
  , ("base/indices.jl:312", toIndicesHelperTuple)
  , ("base/indices.jl:313", toIndicesHelperTuple1)
  , ("base/indices.jl:314", dropZerodimEmpty)
  , ("base/indices.jl:315", dropZerodimTuple)
  , ("base/indices.jl:318", toIndicesEmpty)
  , ("base/indices.jl:319", toIndicesInts)
  , ("base/indices.jl:320", toIndicesIntegers)
  , ("base/indices.jl:321", toIndices3Empty)
  , ("base/indices.jl:322", toIndices3Cons)
  , ("Base.LinearIndices", linearIndicesCtor)
  , ("base/indices.jl:489", convert2indInteger)
  , ("base/indices.jl:490", convert2indUnitRange)
  , ("base/indices.jl:505", indexStyleLinearIndices)
  , ("base/indices.jl:506", axesLinearIndices)
  , ("base/indices.jl:507", sizeLinearIndices)
  , ("base/indices.jl:509", getindexLinearIndicesInt)
  , ("base/indices.jl:526", firstLinearIndices)
  , ("base/indices.jl:527", firstLinearIndices1)
  , ("base/indices.jl:528", lastLinearIndices)
  , ("base/indices.jl:529", lastLinearIndices1)
  ]

end JuliaLean.Pilot.Base.Indices
