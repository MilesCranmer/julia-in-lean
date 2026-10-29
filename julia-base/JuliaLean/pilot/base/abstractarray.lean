import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.AbstractArray

open JuliaLean
open JuliaLean.C

/--
Julia source: base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function size(t::AbstractArray, dim)
    d = Int(dim)::Int
    s = size(t)
    d <= length(s) ? s[d] : 1
end
```
-/
def sizeAbstractArrayDim : Body := fun call args => do
  let [t, dim] := args | throwMethodError "size(t::AbstractArray, dim): arity"
  let d ← call "Core.Int64" [dim]
  if !(← isaObj d int64Type) then
    throwTypeError "size: expected Int"
  let s ← call "Base.size" [t]
  let len ← call "Base.length" [s]
  let cmp ← call "Base.<=" [d, len]
  if ← asBool cmp then
    call "Base.getindex" [s, d]
  else
    return mkInt 1

/--
Julia source: base/abstractarray.jl:79-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(A::AbstractArray{T,N}, d) where {T,N}
    @inline
    d::Integer <= N ? axes(A)[d] : OneTo(1)
end
```
-/
def axesAbstractArrayDim : Body := fun call args => do
  let [A, d] := args | throwMethodError "axes(A::AbstractArray{T,N}, d): arity"
  if !(← isaObj d (.datatype "Core.Integer" [])) then
    throwTypeError "axes: expected Integer"
  let (_, ndims) ← abstractArrayParams A
  let cmp ← call "Base.<=" [d, mkInt ndims]
  if ← asBool cmp then
    let ax ← call "Base.axes" [A]
    call "Base.getindex" [ax, d]
  else
    call "Base.OneTo" [mkInt 1]

/--
Julia source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(A)
    @inline
    map(unchecked_oneto, size(A))
end
```
-/
def axesGeneric : Body := fun call args => do
  let [A] := args | throwMethodError "axes(A): arity"
  let sz ← call "Base.size" [A]
  call "Base.map" [.fn "Base.unchecked_oneto", sz]

/--
Julia source: base/abstractarray.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(A::AbstractArray{<:Any,0}) = OneTo(1)
```
-/
def axes1ZeroDim : Body := fun call args => do
  let [_] := args | throwMethodError "axes1(A::AbstractArray{<:Any,0}): arity"
  call "Base.OneTo" [mkInt 1]

/--
Julia source: base/abstractarray.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(A::AbstractArray) = (@inline; axes(A)[1])
```
-/
def axes1AbstractArray : Body := fun call args => do
  let [A] := args | throwMethodError "axes1(A::AbstractArray): arity"
  let ax ← call "Base.axes" [A]
  call "Base.getindex" [ax, mkInt 1]

/--
Julia source: base/abstractarray.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(iter) = oneto(length(iter))
```
-/
def axes1Iter : Body := fun call args => do
  let [iter] := args | throwMethodError "axes1(iter): arity"
  let len ← call "Base.length" [iter]
  call "Base.oneto" [len]

/--
Julia source: base/abstractarray.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(A::AbstractVector) = (@inline(); axes1(A))
```
-/
def eachindexAbstractVector : Body := fun call args => do
  let [A] := args | throwMethodError "eachindex(A::AbstractVector): arity"
  call "Base.axes1" [A]

/--
Julia source: base/abstractarray.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(A::AbstractArray) = (@inline(); eachindex(IndexStyle(A), A))
```
-/
def eachindexAbstractArray : Body := fun call args => do
  let [A] := args | throwMethodError "eachindex(A::AbstractArray): arity"
  let st ← call "Base.IndexStyle" [A]
  call "Base.eachindex" [st, A]

/--
Julia source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
```
-/
def eachindexLinearArray : Body := fun call args => do
  let [_, A] := args | throwMethodError "eachindex(::IndexLinear, A::Union{Array, Memory}): arity"
  let len ← call "Base.length" [A]
  call "Base.unchecked_oneto" [len]

/--
Julia source: base/abstractarray.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::AbstractArray) = (@inline; oneto(length(A)))
```
-/
def eachindexLinearAbstractArray : Body := fun call args => do
  let [_, A] := args | throwMethodError "eachindex(::IndexLinear, A::AbstractArray): arity"
  let len ← call "Base.length" [A]
  call "Base.oneto" [len]

/--
Julia source: base/abstractarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
```
-/
def eachindexLinearAbstractVector : Body := fun call args => do
  let [_, A] := args | throwMethodError "eachindex(::IndexLinear, A::AbstractVector): arity"
  call "Base.axes1" [A]

/--
Julia source: base/abstractarray.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(a::AbstractArray) = (@inline; last(eachindex(IndexLinear(), a)))
```
-/
def lastindexAbstractArray : Body := fun call args => do
  let [a] := args | throwMethodError "lastindex(a::AbstractArray): arity"
  let idx ← call "Base.eachindex" [indexLinearObj, a]
  call "Base.last" [idx]

/--
Julia source: base/abstractarray.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(a, d) = (@inline; last(axes(a, d)))
```
-/
def lastindexDim : Body := fun call args => do
  let [a, d] := args | throwMethodError "lastindex(a, d): arity"
  let ax ← call "Base.axes" [a, d]
  call "Base.last" [ax]

/--
Julia source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
```
-/
def firstindexAbstractArray : Body := fun call args => do
  let [a] := args | throwMethodError "firstindex(a::AbstractArray): arity"
  let idx ← call "Base.eachindex" [indexLinearObj, a]
  call "Base.first" [idx]

/--
Julia source: base/abstractarray.jl:453-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(a, d) = (@inline; first(axes(a, d)))
```
-/
def firstindexDim : Body := fun call args => do
  let [a, d] := args | throwMethodError "firstindex(a, d): arity"
  let ax ← call "Base.axes" [a, d]
  call "Base.first" [ax]

/--
Julia source: base/abstractarray.jl:455-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds first(a::AbstractArray) = a[first(eachindex(a))]
```
-/
def firstAbstractArray : Body := fun call args => do
  let [a] := args | throwMethodError "first(a::AbstractArray): arity"
  let idx ← call "Base.eachindex" [a]
  let f ← call "Base.first" [idx]
  call "Base.getindex" [a, f]

/--
Julia source: base/abstractarray.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(a) = a[end]
```
-/
def lastGeneric : Body := fun call args => do
  let [a] := args | throwMethodError "last(a): arity"
  let l ← call "Base.lastindex" [a]
  call "Base.getindex" [a, l]

/--
Julia source: base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::AbstractArray, I...)
    @inline
    checkbounds_indices(Bool, axes(A), I)
end
```
-/
def checkboundsBoolVararg : Body := fun call args => do
  let _ :: A :: I := args | throwMethodError "checkbounds(::Type{Bool}, A::AbstractArray, I...): arity"
  let ax ← call "Base.axes" [A]
  let iTup ← mkTupleR I
  call "Base.checkbounds_indices" [.type boolType, ax, iTup]

/--
Julia source: base/abstractarray.jl:690-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::AbstractArray, i)
    @inline
    return checkindex(Bool, eachindex(IndexLinear(), A), i)
end
```
-/
def checkboundsBoolSingle : Body := fun call args => do
  let [_, A, i] := args | throwMethodError "checkbounds(::Type{Bool}, A::AbstractArray, i): arity"
  let inds ← call "Base.eachindex" [indexLinearObj, A]
  call "Base.checkindex" [.type boolType, inds, i]

/--
Julia source: base/abstractarray.jl:722-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
    @inline
    return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
        checkbounds_indices(Bool, safe_tail(inds), tail(I))
end
```
-/
def checkboundsIndicesCons : Body := fun call args => do
  let [_, inds, I] := args | throwMethodError "checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg}): arity"
  let oneTo1 ← call "Base.OneTo" [mkInt 1]
  let ind1 ← call "Base.get" [inds, mkInt 1, oneTo1]
  let i1 ← call "Base.getindex" [I, mkInt 1]
  let c1 ← call "Base.checkindex" [.type boolType, ind1, i1]
  if !(← asBool c1) then
    return mkBool false
  let indsTail ← call "Base.safe_tail" [inds]
  let iTail ← call "Base.tail" [I]
  call "Base.checkbounds_indices" [.type boolType, indsTail, iTail]

/--
Julia source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
```
-/
def checkboundsLenEq1Closure : Body := fun call args => do
  let [x] := args | throwMethodError "x->length(x)==1: arity"
  let len ← call "Base.length" [x]
  call "Base.==" [len, mkInt 1]

/--
Julia source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
```
-/
def checkboundsIndicesNil : Body := fun call args => do
  let [_, inds, _] := args | throwMethodError "checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}): arity"
  call "Base.all" [.fn "Base.checkbounds_indices.predicate", inds]

/--
Julia source: base/abstractarray.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds, i) = throw(ArgumentError(LazyString("unable to check bounds for indices of type ", typeof(i))))
```
-/
def checkindexFallback : Body := fun _ args => do
  let [_, _, _] := args | throwMethodError "checkindex(::Type{Bool}, inds, i): arity"
  throwArgumentError "unable to check bounds for indices"

/--
Julia source: base/abstractarray.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, i::Real) = (first(inds) <= i) & (i <= last(inds))
```
-/
def checkindexUnitRangeReal : Body := fun call args => do
  let [_, inds, i] := args | throwMethodError "checkindex(::Type{Bool}, inds::AbstractUnitRange, i::Real): arity"
  let f ← call "Base.first" [inds]
  let c1 ← call "Base.<=" [f, i]
  let l ← call "Base.last" [inds]
  let c2 ← call "Base.<=" [i, l]
  call "Base.&" [c1, c2]

/--
Julia source: base/abstractarray.jl:752-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::IdentityUnitRange, i::Real) = checkindex(Bool, inds.indices, i)
```
-/
def checkindexIdentityUnitRange : Body := fun call args => do
  let [_, inds, i] := args | throwMethodError "checkindex(::Type{Bool}, inds::IdentityUnitRange, i::Real): arity"
  let inner ← getfieldSym inds "indices"
  call "Base.checkindex" [.type boolType, inner, i]

/--
Julia source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
```
-/
def checkindexOneToBitInt : Body := fun call args => do
  let [_, inds, i] := args | throwMethodError "checkindex(::Type{Bool}, inds::OneTo{T}, i::T): arity"
  let oneI ← call "Base.one" [i]
  let diff ← call "Base.-%" [i, oneI]
  let u1 ← call "Base.unsigned" [diff]
  let l ← call "Base.last" [inds]
  let u2 ← call "Base.unsigned" [l]
  call "Base.<" [u1, u2]

/--
Julia source: base/abstractarray.jl:754-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Colon) = true
```
-/
def checkindexColon : Body := fun _ args => do
  let [_, _, _] := args | throwMethodError "checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Colon): arity"
  return mkBool true

/--
Julia source: base/abstractarray.jl:755-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Slice) = true
```
-/
def checkindexSlice : Body := fun _ args => do
  let [_, _, _] := args | throwMethodError "checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Slice): arity"
  return mkBool true

/--
Julia source: base/abstractarray.jl:1262-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(a::AbstractArray) = (length(a) == 0)
```
-/
def isemptyAbstractArray : Body := fun call args => do
  let [a] := args | throwMethodError "isempty(a::AbstractArray): arity"
  let len ← call "Base.length" [a]
  call "Base.==" [len, mkInt 0]

/--
Julia source: base/abstractarray.jl:1363-1367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::AbstractArray, I...)
    @_propagate_inbounds_meta
    error_if_canonical_getindex(IndexStyle(A), A, I...)
    _getindex(IndexStyle(A), A, to_indices(A, I)...)
end
```
-/
def getindexAbstractArray : Body := fun call args => do
  let A :: I := args | throwMethodError "getindex(A::AbstractArray, I...): arity"
  let st1 ← call "Base.IndexStyle" [A]
  let _ ← call "Base.error_if_canonical_getindex" (st1 :: A :: I)
  let st2 ← call "Base.IndexStyle" [A]
  let iTup ← mkTupleR I
  let indsTup ← call "Base.to_indices" [A, iTup]
  let inds ← unpackTuple indsTup
  call "Base._getindex" (st2 :: A :: inds)

/--
Julia source: base/abstractarray.jl:1369-1369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(A::Array, i1::Integer, I::Integer...) = A[to_indices(A, (i1, I...))...]
```
-/
def getindexArrayIntegers : Body := fun call args => do
  let A :: i1 :: I := args | throwMethodError "getindex(A::Array, i1::Integer, I::Integer...): arity"
  let iTup ← mkTupleR (i1 :: I)
  let indsTup ← call "Base.to_indices" [A, iTup]
  let inds ← unpackTuple indsTup
  call "Base.getindex" (A :: inds)

/--
Julia source: base/abstractarray.jl:1379-1380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexLinear, A::AbstractArray, ::Int) =
    throw(CanonicalIndexError("getindex", typeof(A)))
```
-/
def errorIfCanonicalLinear : Body := fun _ args => do
  let [_, _, _] := args | throwMethodError "error_if_canonical_getindex(::IndexLinear, A, ::Int): arity"
  throwCanonicalIndexError "CanonicalIndexError: getindex"

/--
Julia source: base/abstractarray.jl:1381-1382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexCartesian, A::AbstractArray{T,N}, ::Vararg{Int,N}) where {T,N} =
    throw(CanonicalIndexError("getindex", typeof(A)))
```
-/
def errorIfCanonicalCartesian : Body := fun _ args => do
  let _ :: _ :: _ := args | throwMethodError "error_if_canonical_getindex(::IndexCartesian, A, I...): arity"
  throwCanonicalIndexError "CanonicalIndexError: getindex"

/--
Julia source: base/abstractarray.jl:1383-1383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_if_canonical_getindex(::IndexStyle, ::AbstractArray, ::Any...) = nothing
```
-/
def errorIfCanonicalOther : Body := fun _ args => do
  let _ :: _ :: _ := args | throwMethodError "error_if_canonical_getindex(::IndexStyle, A, I...): arity"
  return nothingObj

/--
Julia source: base/abstractarray.jl:1386-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexStyle, A::AbstractArray, I...) =
    error("getindex for $(typeof(A)) with types $(typeof(I)) is not supported")
```
-/
def getindexFallbackError : Body := fun _ args => do
  let _ :: _ :: _ := args | throwMethodError "_getindex(::IndexStyle, A::AbstractArray, I...): arity"
  throwErrorException "getindex not supported"

/--
Julia source: base/abstractarray.jl:1390-1390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexLinear, A::AbstractVector, i::Int) = (@_propagate_inbounds_meta; getindex(A, i))  # ambiguity resolution in case packages specialize this (to be avoided if at all possible, but see Interpolations.jl)
```
-/
def getindexLinearVector : Body := fun call args => do
  let [_, A, i] := args | throwMethodError "_getindex(::IndexLinear, A::AbstractVector, i::Int): arity"
  call "Base.getindex" [A, i]

/--
Julia source: base/abstractarray.jl:1391-1391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_getindex(::IndexLinear, A::AbstractArray, i::Int) = (@_propagate_inbounds_meta; getindex(A, i))
```
-/
def getindexLinearArray : Body := fun call args => do
  let [_, A, i] := args | throwMethodError "_getindex(::IndexLinear, A::AbstractArray, i::Int): arity"
  call "Base.getindex" [A, i]

/--
Julia source: base/abstractarray.jl:1392-1397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexLinear, A::AbstractArray, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...) # generally _to_linear_index requires bounds checking
    @inbounds r = getindex(A, _to_linear_index(A, I...))
    r
end
```
-/
def getindexLinearMulti : Body := fun call args => do
  let _ :: A :: I := args | throwMethodError "_getindex(::IndexLinear, A::AbstractArray, I::Vararg{Int,M}): arity"
  let _ ← call "Base.checkbounds" (A :: I)
  let lin ← call "Base._to_linear_index" (A :: I)
  call "Base.getindex" [A, lin]

/--
Julia source: base/abstractarray.jl:1398-1398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray, i::Integer) = i
```
-/
def toLinearIndexSingle : Body := fun _ args => do
  let [_, i] := args | throwMethodError "_to_linear_index(A::AbstractArray, i::Integer): arity"
  return i

/--
Julia source: base/abstractarray.jl:1399-1399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractVector, i::Integer, I::Integer...) = i
```
-/
def toLinearIndexVector : Body := fun _ args => do
  let _ :: i :: _ := args | throwMethodError "_to_linear_index(A::AbstractVector, i::Integer, I::Integer...): arity"
  return i

/--
Julia source: base/abstractarray.jl:1400-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray) = first(LinearIndices(A))
```
-/
def toLinearIndexZero : Body := fun call args => do
  let [A] := args | throwMethodError "_to_linear_index(A::AbstractArray): arity"
  let li ← call "Base.LinearIndices" [A]
  call "Base.first" [li]

/--
Julia source: base/abstractarray.jl:1401-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_linear_index(A::AbstractArray, I::Integer...) = (@inline; _sub2ind(A, I...))
```
-/
def toLinearIndexMulti : Body := fun call args => do
  let A :: I := args | throwMethodError "_to_linear_index(A::AbstractArray, I::Integer...): arity"
  call "Base._sub2ind" (A :: I)

/--
Julia source: base/abstractarray.jl:1404-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexCartesian, A::AbstractArray, I::Vararg{Int,M}) where M
    @inline
    @boundscheck checkbounds(A, I...) # generally _to_subscript_indices requires bounds checking
    @inbounds r = getindex(A, _to_subscript_indices(A, I...)...)
    r
end
```
-/
def getindexCartesianMulti : Body := fun call args => do
  let _ :: A :: I := args | throwMethodError "_getindex(::IndexCartesian, A::AbstractArray, I::Vararg{Int,M}): arity"
  let _ ← call "Base.checkbounds" (A :: I)
  let subsTup ← call "Base._to_subscript_indices" (A :: I)
  let subs ← unpackTuple subsTup
  call "Base.getindex" (A :: subs)

/--
Julia source: base/abstractarray.jl:1410-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexCartesian, A::AbstractArray{T,N}, I::Vararg{Int, N}) where {T,N}
    @_propagate_inbounds_meta
    getindex(A, I...)
end
```
-/
def getindexCartesianExact : Body := fun call args => do
  let _ :: A :: I := args | throwMethodError "_getindex(::IndexCartesian, A::AbstractArray{T,N}, I::Vararg{Int,N}): arity"
  call "Base.getindex" (A :: I)

/--
Julia source: base/abstractarray.jl:1414-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray, i::Integer) = (@inline; _unsafe_ind2sub(A, i))
```
-/
def toSubscriptIndicesSingle : Body := fun call args => do
  let [A, i] := args | throwMethodError "_to_subscript_indices(A::AbstractArray, i::Integer): arity"
  call "Base._unsafe_ind2sub" [A, i]

/--
Julia source: base/abstractarray.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,N}) where {T,N} = (@inline; map(first, axes(A)))
```
-/
def toSubscriptIndicesEmpty : Body := fun call args => do
  let [A] := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,N}): arity"
  let ax ← call "Base.axes" [A]
  call "Base.map" [.fn "Base.first", ax]

/--
Julia source: base/abstractarray.jl:1416-1416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}) where {T} = ()
```
-/
def toSubscriptIndices0D0 : Body := fun _ args => do
  let [_] := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,0}): arity"
  mkTupleR []

/--
Julia source: base/abstractarray.jl:1417-1417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}, i::Integer) where {T} = ()
```
-/
def toSubscriptIndices0D1 : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,0}, i::Integer): arity"
  mkTupleR []

/--
Julia source: base/abstractarray.jl:1418-1418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,0}, I::Integer...) where {T} = ()
```
-/
def toSubscriptIndices0DMulti : Body := fun _ args => do
  let _ :: _ := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,0}, I::Integer...): arity"
  mkTupleR []

/--
Julia source: base/abstractarray.jl:1419-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _to_subscript_indices(A::AbstractArray{T,N}, I::Integer...) where {T,N}
    @inline
    J, Jrem = IteratorsMD.split(I, Val(N))
    _to_subscript_indices(A, J, Jrem)
end
```
-/
def toSubscriptIndicesMulti : Body := fun call args => do
  let A :: I := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,N}, I::Integer...): arity"
  let (_, ndims) ← abstractArrayParams A
  let iTup ← mkTupleR I
  let valN : Obj := .imm (valType (.long ndims)) []
  let splitRes ← call "Base.IteratorsMD.split" [iTup, valN]
  let [J, Jrem] ← unpackTuple splitRes | throwTypeError "IteratorsMD.split: expected 2-tuple"
  call "Base._to_subscript_indices" [A, J, Jrem]

/--
Julia source: base/abstractarray.jl:1424-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray, J::Tuple, Jrem::Tuple{}) =
    __to_subscript_indices(A, axes(A), J, Jrem)
```
-/
def toSubscriptIndicesJEmpty : Body := fun call args => do
  let [A, J, Jrem] := args | throwMethodError "_to_subscript_indices(A::AbstractArray, J::Tuple, Jrem::Tuple{}): arity"
  let ax ← call "Base.axes" [A]
  call "Base.__to_subscript_indices" [A, ax, J, Jrem]

/--
Julia source: base/abstractarray.jl:1426-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __to_subscript_indices(A::AbstractArray,
        ::Tuple{AbstractUnitRange,Vararg{AbstractUnitRange}}, J::Tuple, Jrem::Tuple{})
    @inline
    (J..., map(first, tail(_remaining_size(J, axes(A))))...)
end
```
-/
def toSubscriptIndicesInner : Body := fun call args => do
  let [A, _, J, _] := args | throwMethodError "__to_subscript_indices: arity"
  let ax ← call "Base.axes" [A]
  let remSz ← call "Base._remaining_size" [J, ax]
  let tailSz ← call "Base.tail" [remSz]
  let mapped ← call "Base.map" [.fn "Base.first", tailSz]
  let jElems ← unpackTuple J
  let mElems ← unpackTuple mapped
  mkTupleR (jElems ++ mElems)

/--
Julia source: base/abstractarray.jl:1431-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A, J::Tuple, Jrem::Tuple) = J # already bounds-checked, safe to drop
```
-/
def toSubscriptIndicesJRem : Body := fun _ args => do
  let [_, J, _] := args | throwMethodError "_to_subscript_indices(A, J::Tuple, Jrem::Tuple): arity"
  return J

/--
Julia source: base/abstractarray.jl:1432-1432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_to_subscript_indices(A::AbstractArray{T,N}, I::Vararg{Int,N}) where {T,N} = I
```
-/
def toSubscriptIndicesExact : Body := fun _ args => do
  let _ :: I := args | throwMethodError "_to_subscript_indices(A::AbstractArray{T,N}, I::Vararg{Int,N}): arity"
  mkTupleR I

/--
Julia source: base/abstractarray.jl:1433-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_remaining_size(::Tuple{Any}, t::Tuple) = t
```
-/
def remainingSizeOne : Body := fun _ args => do
  let [_, t] := args | throwMethodError "_remaining_size(::Tuple{Any}, t::Tuple): arity"
  return t

/--
Julia source: base/abstractarray.jl:1434-1434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_remaining_size(h::Tuple, t::Tuple) = (@inline; _remaining_size(tail(h), tail(t)))
```
-/
def remainingSizeStep : Body := fun call args => do
  let [h, t] := args | throwMethodError "_remaining_size(h::Tuple, t::Tuple): arity"
  let th ← call "Base.tail" [h]
  let tt ← call "Base.tail" [t]
  call "Base._remaining_size" [th, tt]

/--
Julia source: base/abstractarray.jl:1435-1435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unsafe_ind2sub(::Tuple{}, i) = () # _ind2sub may throw(BoundsError()) in this case
```
-/
def unsafeInd2subEmpty : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_unsafe_ind2sub(::Tuple{}, i): arity"
  mkTupleR []

/--
Julia source: base/abstractarray.jl:1436-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unsafe_ind2sub(sz, i) = (@inline; _ind2sub(sz, i))
```
-/
def unsafeInd2subGeneric : Body := fun call args => do
  let [sz, i] := args | throwMethodError "_unsafe_ind2sub(sz, i): arity"
  call "Base._ind2sub" [sz, i]

/--
Julia source: base/abstractarray.jl:3167-3170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind(A::AbstractArray, I...)
    @inline
    _sub2ind(axes(A), I...)
end
```
-/
def sub2indAbstractArray : Body := fun call args => do
  let A :: I := args | throwMethodError "_sub2ind(A::AbstractArray, I...): arity"
  let ax ← call "Base.axes" [A]
  call "Base._sub2ind" (ax :: I)

/--
Julia source: base/abstractarray.jl:3172-3175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub(A::AbstractArray, ind)
    @inline
    _ind2sub(axes(A), ind)
end
```
-/
def ind2subAbstractArray : Body := fun call args => do
  let [A, ind] := args | throwMethodError "_ind2sub(A::AbstractArray, ind): arity"
  let ax ← call "Base.axes" [A]
  call "Base._ind2sub" [ax, ind]

/--
Julia source: base/abstractarray.jl:3178-3178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Tuple{}) = 1
```
-/
def sub2indEmpty0 : Body := fun _ args => do
  let [_] := args | throwMethodError "_sub2ind(::Tuple{}): arity"
  return mkInt 1

/--
Julia source: base/abstractarray.jl:3179-3179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::DimsInteger) = 1
```
-/
def sub2indDims0 : Body := fun _ args => do
  let [_] := args | throwMethodError "_sub2ind(::DimsInteger): arity"
  return mkInt 1

/--
Julia source: base/abstractarray.jl:3180-3180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Indices) = 1
```
-/
def sub2indIndices0 : Body := fun _ args => do
  let [_] := args | throwMethodError "_sub2ind(::Indices): arity"
  return mkInt 1

/--
Julia source: base/abstractarray.jl:3181-3181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(::Tuple{}, I::Integer...) = (@inline; _sub2ind_recurse((), 1, 1, I...))
```
-/
def sub2indEmptyVar : Body := fun call args => do
  let _ :: I := args | throwMethodError "_sub2ind(::Tuple{}, I::Integer...): arity"
  let emptyTup ← mkTupleR []
  call "Base._sub2ind_recurse" (emptyTup :: mkInt 1 :: mkInt 1 :: I)

/--
Julia source: base/abstractarray.jl:3184-3184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(dims::DimsInteger, I::Integer...) = (@inline; _sub2ind_recurse(dims, 1, 1, I...))
```
-/
def sub2indDimsVar : Body := fun call args => do
  let dims :: I := args | throwMethodError "_sub2ind(dims::DimsInteger, I::Integer...): arity"
  call "Base._sub2ind_recurse" (dims :: mkInt 1 :: mkInt 1 :: I)

/--
Julia source: base/abstractarray.jl:3185-3185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Indices, I::Integer...) = (@inline; _sub2ind_recurse(inds, 1, 1, I...))
```
-/
def sub2indIndicesVar : Body := fun call args => do
  let inds :: I := args | throwMethodError "_sub2ind(inds::Indices, I::Integer...): arity"
  call "Base._sub2ind_recurse" (inds :: mkInt 1 :: mkInt 1 :: I)

/--
Julia source: base/abstractarray.jl:3188-3189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Indices{1}, I::Integer...) =
    throw(ArgumentError("Linear indexing is not defined for one-dimensional arrays"))
```
-/
def sub2indIndices1Err : Body := fun _ args => do
  let _ :: _ := args | throwMethodError "_sub2ind(inds::Indices{1}, I::Integer...): arity"
  throwArgumentError "Linear indexing is not defined for one-dimensional arrays"

/--
Julia source: base/abstractarray.jl:3190-3190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Tuple{OneTo}, I::Integer...) = (@inline; _sub2ind_recurse(inds, 1, 1, I...)) # only OneTo is safe
```
-/
def sub2indOneTo1Var : Body := fun call args => do
  let inds :: I := args | throwMethodError "_sub2ind(inds::Tuple{OneTo}, I::Integer...): arity"
  call "Base._sub2ind_recurse" (inds :: mkInt 1 :: mkInt 1 :: I)

/--
Julia source: base/abstractarray.jl:3191-3191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind(inds::Tuple{OneTo}, i::Integer)    = i
```
-/
def sub2indOneTo1Single : Body := fun _ args => do
  let [_, i] := args | throwMethodError "_sub2ind(inds::Tuple{OneTo}, i::Integer): arity"
  return i

/--
Julia source: base/abstractarray.jl:3193-3193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sub2ind_recurse(::Any, L, ind) = ind
```
-/
def sub2indRecurseBase : Body := fun _ args => do
  let [_, _, ind] := args | throwMethodError "_sub2ind_recurse(::Any, L, ind): arity"
  return ind

/--
Julia source: base/abstractarray.jl:3194-3197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind_recurse(::Tuple{}, L, ind, i::Integer, I::Integer...)
    @inline
    _sub2ind_recurse((), L, ind+(i-1)*L, I...)
end
```
-/
def sub2indRecurseEmpty : Body := fun call args => do
  let _ :: L :: ind :: i :: I := args | throwMethodError "_sub2ind_recurse(::Tuple{}, L, ind, i, I...): arity"
  let emptyTup ← mkTupleR []
  let iMinus1 ← call "Base.-" [i, mkInt 1]
  let prod ← call "Base.*" [iMinus1, L]
  let nextInd ← call "Base.+" [ind, prod]
  call "Base._sub2ind_recurse" (emptyTup :: L :: nextInd :: I)

/--
Julia source: base/abstractarray.jl:3198-3202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sub2ind_recurse(inds, L, ind, i::Integer, I::Integer...)
    @inline
    r1 = inds[1]
    _sub2ind_recurse(tail(inds), nextL(L, r1), ind+offsetin(i, r1)*L, I...)
end
```
-/
def sub2indRecurseStep : Body := fun call args => do
  let inds :: L :: ind :: i :: I := args | throwMethodError "_sub2ind_recurse(inds, L, ind, i, I...): arity"
  let r1 ← call "Base.getindex" [inds, mkInt 1]
  let tailInds ← call "Base.tail" [inds]
  let nL ← call "Base.nextL" [L, r1]
  let off ← call "Base.offsetin" [i, r1]
  let prod ← call "Base.*" [off, L]
  let nextInd ← call "Base.+" [ind, prod]
  call "Base._sub2ind_recurse" (tailInds :: nL :: nextInd :: I)

/--
Julia source: base/abstractarray.jl:3204-3204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, l::Integer) = L*l
```
-/
def nextLInteger : Body := fun call args => do
  let [L, l] := args | throwMethodError "nextL(L, l::Integer): arity"
  call "Base.*" [L, l]

/--
Julia source: base/abstractarray.jl:3205-3205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, r::AbstractUnitRange) = L*length(r)
```
-/
def nextLUnitRange : Body := fun call args => do
  let [L, r] := args | throwMethodError "nextL(L, r::AbstractUnitRange): arity"
  let len ← call "Base.length" [r]
  call "Base.*" [L, len]

/--
Julia source: base/abstractarray.jl:3206-3206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextL(L, r::Slice) = L*length(r.indices)
```
-/
def nextLSlice : Body := fun call args => do
  let [L, r] := args | throwMethodError "nextL(L, r::Slice): arity"
  let inds ← getfieldSym r "indices"
  let len ← call "Base.length" [inds]
  call "Base.*" [L, len]

/--
Julia source: base/abstractarray.jl:3207-3207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offsetin(i, l::Integer) = i-1
```
-/
def offsetinInteger : Body := fun call args => do
  let [i, _] := args | throwMethodError "offsetin(i, l::Integer): arity"
  call "Base.-" [i, mkInt 1]

/--
Julia source: base/abstractarray.jl:3208-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offsetin(i, r::AbstractUnitRange) = i-first(r)
```
-/
def offsetinUnitRange : Body := fun call args => do
  let [i, r] := args | throwMethodError "offsetin(i, r::AbstractUnitRange): arity"
  let f ← call "Base.first" [r]
  call "Base.-" [i, f]

/--
Julia source: base/abstractarray.jl:3210-3210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(::Tuple{}, ind::Integer) = (@inline; ind == 1 ? () : throw(BoundsError()))
```
-/
def ind2subEmpty : Body := fun call args => do
  let [_, ind] := args | throwMethodError "_ind2sub(::Tuple{}, ind::Integer): arity"
  let eq ← call "Base.==" [ind, mkInt 1]
  if ← asBool eq then
    mkTupleR []
  else
    throwBoundsError "BoundsError"

/--
Julia source: base/abstractarray.jl:3211-3211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(dims::DimsInteger, ind::Integer) = (@inline; _ind2sub_recurse(dims, ind-1))
```
-/
def ind2subDims : Body := fun call args => do
  let [dims, ind] := args | throwMethodError "_ind2sub(dims::DimsInteger, ind::Integer): arity"
  let m ← call "Base.-" [ind, mkInt 1]
  call "Base._ind2sub_recurse" [dims, m]

/--
Julia source: base/abstractarray.jl:3212-3212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Indices, ind::Integer)     = (@inline; _ind2sub_recurse(inds, ind-1))
```
-/
def ind2subIndices : Body := fun call args => do
  let [inds, ind] := args | throwMethodError "_ind2sub(inds::Indices, ind::Integer): arity"
  let m ← call "Base.-" [ind, mkInt 1]
  call "Base._ind2sub_recurse" [inds, m]

/--
Julia source: base/abstractarray.jl:3213-3214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Indices{1}, ind::Integer) =
    throw(ArgumentError("Linear indexing is not defined for one-dimensional arrays"))
```
-/
def ind2subIndices1Err : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_ind2sub(inds::Indices{1}, ind::Integer): arity"
  throwArgumentError "Linear indexing is not defined for one-dimensional arrays"

/--
Julia source: base/abstractarray.jl:3215-3215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub(inds::Tuple{OneTo}, ind::Integer) = (ind,)
```
-/
def ind2subOneTo1 : Body := fun _ args => do
  let [_, ind] := args | throwMethodError "_ind2sub(inds::Tuple{OneTo}, ind::Integer): arity"
  mkTupleR [ind]

/--
Julia source: base/abstractarray.jl:3217-3217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ind2sub_recurse(::Tuple{}, ind) = (ind+1,)
```
-/
def ind2subRecurseEmpty : Body := fun call args => do
  let [_, ind] := args | throwMethodError "_ind2sub_recurse(::Tuple{}, ind): arity"
  let v ← call "Base.+" [ind, mkInt 1]
  mkTupleR [v]

/--
Julia source: base/abstractarray.jl:3218-3221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub_recurse(indslast::NTuple{1}, ind)
    @inline
    (_lookup(ind, indslast[1]),)
end
```
-/
def ind2subRecurse1 : Body := fun call args => do
  let [indslast, ind] := args | throwMethodError "_ind2sub_recurse(indslast::NTuple{1}, ind): arity"
  let r1 ← call "Base.getindex" [indslast, mkInt 1]
  let v ← call "Base._lookup" [ind, r1]
  mkTupleR [v]

/--
Julia source: base/abstractarray.jl:3222-3227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ind2sub_recurse(inds, ind)
    @inline
    r1 = inds[1]
    indnext, indsub = divrem(ind, _indexlength(r1))
    (_lookup(indsub, r1), _ind2sub_recurse(tail(inds), indnext)...)
end
```
-/
def ind2subRecurseStep : Body := fun call args => do
  let [inds, ind] := args | throwMethodError "_ind2sub_recurse(inds, ind): arity"
  let r1 ← call "Base.getindex" [inds, mkInt 1]
  let len ← call "Base._indexlength" [r1]
  let dr ← call "Base.divrem" [ind, len]
  let [indnext, indsub] ← unpackTuple dr | throwTypeError "divrem: expected 2-tuple"
  let firstElem ← call "Base._lookup" [indsub, r1]
  let tailInds ← call "Base.tail" [inds]
  let restTup ← call "Base._ind2sub_recurse" [tailInds, indnext]
  let restElems ← unpackTuple restTup
  mkTupleR (firstElem :: restElems)

/--
Julia source: base/abstractarray.jl:3229-3229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indexlength(d::Integer) = d
```
-/
def indexlengthInteger : Body := fun _ args => do
  let [d] := args | throwMethodError "_indexlength(d::Integer): arity"
  return d

/--
Julia source: base/abstractarray.jl:3230-3230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indexlength(r::AbstractUnitRange) = length(r)
```
-/
def indexlengthUnitRange : Body := fun call args => do
  let [r] := args | throwMethodError "_indexlength(r::AbstractUnitRange): arity"
  call "Base.length" [r]

/--
Julia source: base/abstractarray.jl:3231-3231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_lookup(ind, d::Integer) = ind+1
```
-/
def lookupInteger : Body := fun call args => do
  let [ind, _] := args | throwMethodError "_lookup(ind, d::Integer): arity"
  call "Base.+" [ind, mkInt 1]

/--
Julia source: base/abstractarray.jl:3232-3232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_lookup(ind, r::AbstractUnitRange) = ind+first(r)
```
-/
def lookupUnitRange : Body := fun call args => do
  let [ind, r] := args | throwMethodError "_lookup(ind, r::AbstractUnitRange): arity"
  let f ← call "Base.first" [r]
  call "Base.+" [ind, f]

def bodies : List (String × Body) :=
  [ ("base/abstractarray.jl:42", sizeAbstractArrayDim)
  , ("base/abstractarray.jl:79", axesAbstractArrayDim)
  , ("base/abstractarray.jl:100", axesGeneric)
  , ("base/abstractarray.jl:140", axes1ZeroDim)
  , ("base/abstractarray.jl:141", axes1AbstractArray)
  , ("base/abstractarray.jl:142", axes1Iter)
  , ("base/abstractarray.jl:325", eachindexAbstractVector)
  , ("base/abstractarray.jl:384", eachindexAbstractArray)
  , ("base/abstractarray.jl:394", eachindexLinearArray)
  , ("base/abstractarray.jl:395", eachindexLinearAbstractArray)
  , ("base/abstractarray.jl:396", eachindexLinearAbstractVector)
  , ("base/abstractarray.jl:429", lastindexAbstractArray)
  , ("base/abstractarray.jl:430", lastindexDim)
  , ("base/abstractarray.jl:452", firstindexAbstractArray)
  , ("base/abstractarray.jl:453", firstindexDim)
  , ("base/abstractarray.jl:455", firstAbstractArray)
  , ("base/abstractarray.jl:530", lastGeneric)
  , ("base/abstractarray.jl:682", checkboundsBoolVararg)
  , ("base/abstractarray.jl:690", checkboundsBoolSingle)
  , ("base/abstractarray.jl:722", checkboundsIndicesCons)
  , ("base/abstractarray.jl:728", checkboundsIndicesNil)
  , ("Base.checkbounds_indices.predicate@base/abstractarray.jl:728", checkboundsLenEq1Closure)
  , ("base/abstractarray.jl:750", checkindexFallback)
  , ("base/abstractarray.jl:751", checkindexUnitRangeReal)
  , ("base/abstractarray.jl:752", checkindexIdentityUnitRange)
  , ("base/abstractarray.jl:753", checkindexOneToBitInt)
  , ("base/abstractarray.jl:754", checkindexColon)
  , ("base/abstractarray.jl:755", checkindexSlice)
  , ("base/abstractarray.jl:1262", isemptyAbstractArray)
  , ("base/abstractarray.jl:1363", getindexAbstractArray)
  , ("base/abstractarray.jl:1369", getindexArrayIntegers)
  , ("base/abstractarray.jl:1379", errorIfCanonicalLinear)
  , ("base/abstractarray.jl:1381", errorIfCanonicalCartesian)
  , ("base/abstractarray.jl:1383", errorIfCanonicalOther)
  , ("base/abstractarray.jl:1386", getindexFallbackError)
  , ("base/abstractarray.jl:1390", getindexLinearVector)
  , ("base/abstractarray.jl:1391", getindexLinearArray)
  , ("base/abstractarray.jl:1392", getindexLinearMulti)
  , ("base/abstractarray.jl:1398", toLinearIndexSingle)
  , ("base/abstractarray.jl:1399", toLinearIndexVector)
  , ("base/abstractarray.jl:1400", toLinearIndexZero)
  , ("base/abstractarray.jl:1401", toLinearIndexMulti)
  , ("base/abstractarray.jl:1404", getindexCartesianMulti)
  , ("base/abstractarray.jl:1410", getindexCartesianExact)
  , ("base/abstractarray.jl:1414", toSubscriptIndicesSingle)
  , ("base/abstractarray.jl:1415", toSubscriptIndicesEmpty)
  , ("base/abstractarray.jl:1416", toSubscriptIndices0D0)
  , ("base/abstractarray.jl:1417", toSubscriptIndices0D1)
  , ("base/abstractarray.jl:1418", toSubscriptIndices0DMulti)
  , ("base/abstractarray.jl:1419", toSubscriptIndicesMulti)
  , ("base/abstractarray.jl:1424", toSubscriptIndicesJEmpty)
  , ("base/abstractarray.jl:1426", toSubscriptIndicesInner)
  , ("base/abstractarray.jl:1431", toSubscriptIndicesJRem)
  , ("base/abstractarray.jl:1432", toSubscriptIndicesExact)
  , ("base/abstractarray.jl:1433", remainingSizeOne)
  , ("base/abstractarray.jl:1434", remainingSizeStep)
  , ("base/abstractarray.jl:1435", unsafeInd2subEmpty)
  , ("base/abstractarray.jl:1436", unsafeInd2subGeneric)
  , ("base/abstractarray.jl:3167", sub2indAbstractArray)
  , ("base/abstractarray.jl:3172", ind2subAbstractArray)
  , ("base/abstractarray.jl:3178", sub2indEmpty0)
  , ("base/abstractarray.jl:3179", sub2indDims0)
  , ("base/abstractarray.jl:3180", sub2indIndices0)
  , ("base/abstractarray.jl:3181", sub2indEmptyVar)
  , ("base/abstractarray.jl:3184", sub2indDimsVar)
  , ("base/abstractarray.jl:3185", sub2indIndicesVar)
  , ("base/abstractarray.jl:3188", sub2indIndices1Err)
  , ("base/abstractarray.jl:3190", sub2indOneTo1Var)
  , ("base/abstractarray.jl:3191", sub2indOneTo1Single)
  , ("base/abstractarray.jl:3193", sub2indRecurseBase)
  , ("base/abstractarray.jl:3194", sub2indRecurseEmpty)
  , ("base/abstractarray.jl:3198", sub2indRecurseStep)
  , ("base/abstractarray.jl:3204", nextLInteger)
  , ("base/abstractarray.jl:3205", nextLUnitRange)
  , ("base/abstractarray.jl:3206", nextLSlice)
  , ("base/abstractarray.jl:3207", offsetinInteger)
  , ("base/abstractarray.jl:3208", offsetinUnitRange)
  , ("base/abstractarray.jl:3210", ind2subEmpty)
  , ("base/abstractarray.jl:3211", ind2subDims)
  , ("base/abstractarray.jl:3212", ind2subIndices)
  , ("base/abstractarray.jl:3213", ind2subIndices1Err)
  , ("base/abstractarray.jl:3215", ind2subOneTo1)
  , ("base/abstractarray.jl:3217", ind2subRecurseEmpty)
  , ("base/abstractarray.jl:3218", ind2subRecurse1)
  , ("base/abstractarray.jl:3222", ind2subRecurseStep)
  , ("base/abstractarray.jl:3229", indexlengthInteger)
  , ("base/abstractarray.jl:3230", indexlengthUnitRange)
  , ("base/abstractarray.jl:3231", lookupInteger)
  , ("base/abstractarray.jl:3232", lookupUnitRange)
  ]

end JuliaLean.Pilot.Base.AbstractArray
