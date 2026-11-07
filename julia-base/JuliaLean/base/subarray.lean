import JuliaLean.base.abstractarray
import JuliaLean.Core
import JuliaLean.base.int

/-!
# Model of `base/subarray.jl`

Typed, source-mirrored models of the view, indexing, layout, pointer, and axis methods in Julia Base.
Julia integers are represented as `JInt .i64`; operations use the integer model so wrapping occurs
at the same operations as in Julia. Calls to methods defined by other Base files or extended by
user array types are explicit function parameters.
Mutation models return a view carrying the updated parent value.
Reindexing may preserve the original parent or nest the prior view as its parent.
-/

namespace JuliaLean.base.subarray

open JuliaLean JuliaLean.base.int

abbrev I64 := JInt .i64

def int64 (n : Int) : I64 := lit .i64 n
def iadd (x y : I64) : I64 := add x y
def isub (x y : I64) : I64 := sub x y
def imul (x y : I64) : I64 := mul x y

namespace Models1Group17

-- Source: base/tuple.jl:270-271
def tupleFirst {A : Type} : List A → Jl A
  | [] => .error (.argumentError "tuple must be non-empty")
  | first :: _ => .ok first

-- Source: base/essentials.jl:541-542
def tupleTail {A : Type} : List A → Jl (List A)
  | [] => .error (.argumentError "Cannot call tail on an empty tuple.")
  | _ :: rest => .ok rest

end Models1Group17

structure Axis where
  first : I64
  last : I64
  deriving DecidableEq

inductive Index where
  | scalar (value : I64)
  | colon
  | slice (axis : Axis)
  | unitRange (axis : Axis)
  | oneTo (length : I64)
  | identity (axis : Axis)
  | stepRange (first step count : I64)
  | stepRangeLen (first step count : I64)
  | ordinalRange (first step count : I64)
  | linRange (first last count : I64)
  | values (axes : List Axis) (items : List I64)
  | cartesianValues (axes : List Axis) (elementRank : Nat) (items : List (List I64))
  | mask (values : List Bool)
  | other
  | cartesian (coordinates : List I64)
  deriving DecidableEq

inductive IndexStyle where
  | linear
  | cartesian
  deriving DecidableEq

structure SubArray (P T : Type) where
  parent : P
  indices : List Index
  offset1 : I64
  stride1 : I64
  linear : Bool
  dimensions : List Bool
  deriving DecidableEq
inductive ReindexedView (P T : Type) where
  | flattened (view : SubArray P T)
  | nested (view : SubArray (SubArray P T) T)

  deriving DecidableEq

namespace Index

def isScalar : Index → Bool
  | .scalar _ => true
  | _ => false

def isRange : Index → Bool
  | .slice _ | .unitRange _ | .oneTo _ | .identity _ | .stepRange _ _ _ |
    .stepRangeLen _ _ _ | .ordinalRange _ _ _ | .linRange _ _ _ => true
  | _ => false

def isUnitRange : Index → Bool
  | .slice _ | .unitRange _ | .oneTo _ | .identity _ => true
  | _ => false

def isArray : Index → Bool
  | .values _ _ | .cartesianValues _ _ _ | .mask _ => true
  | _ => false

def scalarValue : Index → Option I64
  | .scalar x => some x
  | _ => none

def allScalar (indices : List Index) : Bool := indices.all isScalar

def indexAxes : Index → List Axis
  | .scalar _ | .colon | .other | .cartesian _ => []
  | .slice a | .identity a => [a]
  | .unitRange a => [{ first := int64 1, last := int64 (a.last.val - a.first.val + 1) }]
  | .oneTo n => [{ first := int64 1, last := n }]
  | .stepRange _ _ n | .stepRangeLen _ _ n | .ordinalRange _ _ n =>
      [{ first := int64 1, last := n }]
  | .linRange _ _ n => [{ first := int64 1, last := n }]
  | .values axes _ | .cartesianValues axes _ _ => axes
  | .mask maskBits => [{ first := int64 1, last := int64 (maskBits.filter id).length }]

end Index

/--
Julia source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
        @inline
        check_parent_index_match(parent, indices)
        new(parent, indices, offset1, stride1)
    end
```
-/
def subarrayInner {P T : Type} (parent : P) (indices : List Index) (offset1 stride1 : I64)
    (linear : Bool) (dimensions : List Bool) (check : P → List Index → Jl Unit) : Jl (SubArray P T) := do
  check parent indices
  pure ⟨parent, indices, offset1, stride1, linear, dimensions⟩

/--
Julia source: base/subarray.jl:26-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function SubArray(parent::AbstractArray, indices::Tuple)
    @inline
    SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
end
```
-/
def subarrayOuter {P T : Type} (parent : P) (indices : List Index)
    (viewindexing : List Index → IndexStyle) (parentStyle : P → IndexStyle)
    (combine : IndexStyle → IndexStyle → IndexStyle)
    (ensureIndexable : List Index → List Index) (indexDimsum : List Index → List Bool)
    (construct : IndexStyle → P → List Index → List Bool → Jl (SubArray P T)) : Jl (SubArray P T) :=
  construct (combine (viewindexing indices) (parentStyle parent)) parent
    (ensureIndexable indices) (indexDimsum indices)

/--
Julia source: base/subarray.jl:30-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
    @inline
    SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
end
```
-/
def subarrayCartesian {P T : Type} (parent : P) (indices : List Index) (dimensions : List Bool)
    (check : P → List Index → Jl Unit) : Jl (SubArray P T) :=
  subarrayInner parent indices (int64 0) (int64 0) false dimensions check

/--
Julia source: base/subarray.jl:34-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
    @inline
    offset1, stride1 = _compute_linear_layout(parent, indices)
    SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
end
```
-/
def subarrayLinear {P T : Type} (parent : P) (indices : List Index) (dimensions : List Bool)
    (check : P → List Index → Jl Unit)
    (computeLayout : P → List Index → Jl (I64 × I64)) : Jl (SubArray P T) := do
  let (offset1, stride1) ← computeLayout parent indices
  subarrayInner parent indices offset1 stride1 true dimensions check

/--
Julia source: base/subarray.jl:40-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _compute_linear_layout(parent, indices)
    @inline
    stride1 = Int(compute_stride1(parent, indices))
    return Int(compute_offset1(parent, stride1, indices)), stride1
end
```
-/
def computeLinearLayout {P : Type} (parent : P) (indices : List Index)
    (computeStride1 : P → List Index → Jl I64)
    (computeOffset1 : P → I64 → List Index → Jl I64) : Jl (I64 × I64) := do
  let stride1 ← computeStride1 parent indices
  let offset1 ← computeOffset1 parent stride1 indices
  pure (offset1, stride1)

/--
Julia source: base/subarray.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
```
-/
def checkParentIndexMatch {P : Type} (parent : P) (indices : List Index)
    (indexNdims : List Index → List Bool) (checkShape : P → List Bool → Jl Unit) : Jl Unit :=
  checkShape parent (indexNdims indices)

/--
Julia source: base/subarray.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
```
-/
def checkParentIndexMatchArray {P : Type} (parent : P) (_dimensions : List Bool) : Jl Unit := .ok ()

/--
Julia source: base/subarray.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
    throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
```
-/
def checkParentIndexMatchMismatch {P : Type} (parent : P) (dimensions : List Bool)
    (ndims : P → Jl Nat) : Jl Unit := do
  let parentDims ← ndims parent
  .error (.argumentError s!"number of indices ({dimensions.length}) must match the parent dimensionality ({parentDims})")
/--
Julia source: base/subarray.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{}) = IndexLinear()
```
-/
def viewIndexingEmpty : IndexStyle := .linear

/--
Julia source: base/subarray.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{ScalarIndex, Vararg{Any}}) = (@inline; viewindexing(tail(I)))
```
-/
def viewIndexingScalar (tail : List Index → IndexStyle) (head : Index) (rest : List Index) : IndexStyle :=
  tail rest

/--
Julia source: base/subarray.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{Slice, Slice, Vararg{Any}}) = (@inline; viewindexing(tail(I)))
```
-/
def viewIndexingSlices (tail : List Index → IndexStyle) (first second : Index) (rest : List Index) : IndexStyle :=
  tail (second :: rest)

/--
Julia source: base/subarray.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{Slice, AbstractUnitRange, Vararg{ScalarIndex}}) = IndexLinear()
```
-/
def viewIndexingSliceUnitRange (_slice : Index) (_range : Index) (_scalars : List Index) : IndexStyle := .linear

/--
Julia source: base/subarray.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{Slice, Slice, Vararg{ScalarIndex}}) = IndexLinear() # disambiguate
```
-/
def viewIndexingSliceSliceScalars (_first _second : Index) (_scalars : List Index) : IndexStyle := .linear

/--
Julia source: base/subarray.jl:60-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# In general, scalar ranges are only fast if all other indices are scalar
# Other ranges, such as those of `CartesianIndex`es, are not fast even if these
# are followed by `ScalarIndex`es
viewindexing(I::Tuple{AbstractRange{<:ScalarIndex}, Vararg{ScalarIndex}}) = IndexLinear()
```
-/
def viewIndexingScalarRange (_range : Index) (_scalars : List Index) : IndexStyle := .linear

/--
Julia source: base/subarray.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{Vararg{Any}}) = IndexCartesian()
```
-/
def viewIndexingFallback (_indices : List Index) : IndexStyle := .cartesian

/--
Julia source: base/subarray.jl:66-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Of course, all other array types are slow
viewindexing(I::Tuple{AbstractArray, Vararg{Any}}) = IndexCartesian()
```
-/
def viewIndexingArray (_indices : List Index) : IndexStyle := .cartesian

/-- Source-level dispatch for the `viewindexing` methods above. -/
def viewIndexing : List Index → IndexStyle
  | [] => viewIndexingEmpty
  | .scalar _ :: rest => viewIndexing rest
  | .slice _ :: .slice secondAxis :: rest =>
      if Index.allScalar rest then .linear else viewIndexing (.slice secondAxis :: rest)
  | .slice axis :: .unitRange range :: rest =>
      if Index.allScalar rest then viewIndexingSliceUnitRange (.slice axis) (.unitRange range) rest
      else viewIndexingFallback (.slice axis :: .unitRange range :: rest)
  | .slice axis :: .oneTo length :: rest =>
      if Index.allScalar rest then viewIndexingSliceUnitRange (.slice axis) (.oneTo length) rest
      else viewIndexingFallback (.slice axis :: .oneTo length :: rest)
  | .slice axis :: .identity range :: rest =>
      if Index.allScalar rest then viewIndexingSliceUnitRange (.slice axis) (.identity range) rest
      else viewIndexingFallback (.slice axis :: .identity range :: rest)
  | .slice _ :: rest => if Index.allScalar rest then .linear else .cartesian
  | index :: rest =>
      if index.isRange && Index.allScalar rest then viewIndexingScalarRange index rest
      else if index.isArray then viewIndexingArray (index :: rest) else viewIndexingFallback (index :: rest)
termination_by structural indices => indices

def indexStyleCombine : IndexStyle → IndexStyle → IndexStyle
  | .linear, .linear => .linear
  | _, _ => .cartesian

/--
Julia source: base/subarray.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(V::SubArray) = (@inline; map(length, axes(V)))
```
-/
def sizeSubArray {P T : Type} (V : SubArray P T) (axes : SubArray P T → List Axis)
    (length : Axis → I64) : List I64 := (axes V).map length

/--
Julia source: base/subarray.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
```
-/
def similarSubArrayValue {P T R : Type} (V : SubArray P T) (elementType : R) (dims : List I64)
    (similarParent : P → R → List I64 → Jl R) : Jl R :=
  similarParent V.parent elementType dims

/--
Julia source: base/subarray.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
```
-/
def similarSubArrayType (parentType : Type) (dims : List I64)
    (similarParent : Type → List I64 → Type) : Type :=
  similarParent parentType dims

/--
Julia source: base/subarray.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(V::SubArray) = length(V) * sizeof(eltype(V))
```
-/
def sizeofSubArray {P T : Type} (V : SubArray P T) (length : SubArray P T → I64)
    (sizeofElement : Type → I64) : I64 := imul (length V) (sizeofElement T)

/--
Julia source: base/subarray.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(V::SubArray{<:Any,<:Any,<:Array}) = length(V) * elsize(V.parent)
```
-/
def sizeofArraySubArray {P T : Type} (V : SubArray P T) (length : SubArray P T → I64)
    (elsize : P → I64) : I64 := imul (length V) (elsize V.parent)

/--
Julia source: base/subarray.jl:78-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.copy(V::SubArray)
    v = V.parent[V.indices...]
    ndims(V) == 0 || return v
    x = similar(V) # ensure proper type of x
    x[] = v
    return x
end
```
-/
def copySubArray {P T R : Type} (V : SubArray P T) (getParent : P → List Index → Jl R)
    (ndims : SubArray P T → Nat) (similar : SubArray P T → Jl R)
    (setEmpty : R → R → Jl Unit) : Jl R := do
  let value ← getParent V.parent V.indices
  if ndims V != 0 then return value
  let result ← similar V
  setEmpty result value
  return result

/--
Julia source: base/subarray.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(V::SubArray) = V.parent
```
-/
def parentSubArray {P T : Type} (V : SubArray P T) : P := V.parent

/--
Julia source: base/subarray.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentindices(V::SubArray) = V.indices
```
-/
def parentindicesSubArray {P T : Type} (V : SubArray P T) : List Index := V.indices

/--
Julia source: base/subarray.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentindices(a::AbstractArray) = map(oneto, size(a))
```
-/
def parentindicesArray {P : Type} (a : P) (size : P → List I64)
    (oneto : I64 → Axis) : List Axis := (size a).map oneto
/--
Julia source: base/subarray.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(A::SubArray) = (dataids(A.parent)..., _splatmap(dataids, A.indices)...)
```
-/
def dataidsSubArray {P T β : Type} (A : SubArray P T)
    (dataids : P → Jl (List β)) (splatmap : (Index → Jl (List β)) → List Index → Jl (List β))
    (dataidsIndex : Index → Jl (List β)) : Jl (List β) := do
  let parentIds ← dataids A.parent
  let indexIds ← splatmap dataidsIndex A.indices
  pure (parentIds ++ indexIds)

/--
Julia source: base/subarray.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_splatmap(f, ::Tuple{}) = ()
```
-/
def splatmapEmpty {A B : Type} (_f : A → Jl (List B)) : Jl (List B) := .ok []

/--
Julia source: base/subarray.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_splatmap(f, t::Tuple) = (f(t[1])..., _splatmap(f, tail(t))...)
```
-/
def splatmap {A B : Type} (f : A → Jl (List B)) : List A → Jl (List B)
  | [] => splatmapEmpty f
  | x :: xs => do
      let first ← f x
      let rest ← splatmap f xs
      pure (first ++ rest)

/--
Julia source: base/subarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(A::SubArray) = typeof(A)(unaliascopy(A.parent), map(unaliascopy, A.indices), A.offset1, A.stride1)
```
-/
def unaliascopySubArray {P T : Type} (A : SubArray P T)
    (unaliasParent : P → Jl P) (unaliasIndex : Index → Jl Index)
    (construct : P → List Index → I64 → I64 → Bool → List Bool → Jl (SubArray P T)) :
    Jl (SubArray P T) := do
  let parent ← unaliasParent A.parent
  let indices ← A.indices.mapM unaliasIndex
  construct parent indices A.offset1 A.stride1 A.linear A.dimensions

/--
Julia source: base/subarray.jl:119-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
    dest = Array{T}(undef, _trimmedshape(V.indices...))
    trimmedpind = _trimmedpind(V.indices...)
    vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
    copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
    indices = map(_trimmedindex, V.indices)
    if LD
        offset1, stride1 = _compute_linear_layout(dest, indices)
    else
        offset1, stride1 = 0, 0
    end
    SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
end
```
-/
def unaliascopyArraySubArray {P T S : Type} (V : SubArray P T)
    (allocate : List I64 → Jl P) (trimShape : List Index → List I64)
    (trimParentIndices : List Index → List Index) (isColonSelection : List Index → Bool)
    (makeView : P → List Index → Jl P) (copyTo : P → S → Jl Unit)
    (makeSourceView : SubArray P T → List Index → Jl S)
    (trimViewIndices : List Index → List Index) (trimIndex : Index → Jl Index)
    (computeLayout : P → List Index → Jl (I64 × I64))
    (construct : P → List Index → I64 → I64 → Bool → List Bool → Jl (SubArray P T)) :
    Jl (SubArray P T) := do
  let dest ← allocate (trimShape V.indices)
  let trimmedpind := trimParentIndices V.indices
  let vdest ← if isColonSelection trimmedpind then pure dest else makeView dest trimmedpind
  let source ← makeSourceView V (trimViewIndices V.indices)
  copyTo vdest source
  let indices ← V.indices.mapM trimIndex
  let (offset1, stride1) ← if V.linear then computeLayout dest indices else pure (int64 0, int64 0)
  construct dest indices offset1 stride1 V.linear V.dimensions

/--
Julia source: base/subarray.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
```
-/
def trimmedShapeScalar {A : Type} (_index : A) (rest : List A)
    (trimmedShape : List A → List I64) : List I64 := int64 1 :: trimmedShape rest

/--
Julia source: base/subarray.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
```
-/
def trimmedShapeAbstractRange {A : Type} (index : A) (rest : List A)
    (isempty : A → Bool) (zeroElement : A → I64) (maximum : A → I64)
    (trimmedShape : List A → List I64) : List I64 :=
  (if isempty index then zeroElement index else maximum index) :: trimmedShape rest

/--
Julia source: base/subarray.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
```
-/
def trimmedShapeDenseRange {A : Type} (index : A) (rest : List A)
    (length : A → I64) (trimmedShape : List A → List I64) : List I64 :=
  length index :: trimmedShape rest

/--
Julia source: base/subarray.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
```
-/
def trimmedShapeScalarArray {A : Type} (index : A) (rest : List A)
    (length : A → I64) (trimmedShape : List A → List I64) : List I64 :=
  length index :: trimmedShape rest

/--
Julia source: base/subarray.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
```
-/
def trimmedShapeCartesianZero {A : Type} (_index : A) (rest : List A)
    (trimmedShape : List A → List I64) : List I64 := trimmedShape rest

/--
Julia source: base/subarray.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
```
-/
def trimmedShapeCartesian {A : Type} (rank : Nat) (index : A) (rest : List A)
    (length : A → I64) (trimmedShape : List A → List I64) : List I64 :=
  length index :: List.replicate (rank - 1) (int64 1) ++ trimmedShape rest

/--
Julia source: base/subarray.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedshape() = ()
```
-/
def trimmedShapeEmpty : List I64 := []

/--
Julia source: base/subarray.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
```
-/
def trimmedParentIndicesSource {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (trimmed : List A → List Index) : List Index :=
  (axes index).map (fun _ => Index.colon) ++ trimmed rest

-- Source: base/subarray.jl:141
def trimmedParentIndices {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (_colon : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  trimmedParentIndicesSource index rest axes trimmed

/--
Julia source: base/subarray.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
```
-/
def trimmedParentRange (index : Index) (rest : List Index)
    (trimmed : List Index → List Index) : List Index := index :: trimmed rest

/--
Julia source: base/subarray.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
```
-/
def trimmedParentDenseRange {A : Type} (_index : A) (rest : List A)
    (trimmed : List A → List Index) : List Index := .colon :: trimmed rest

/--
Julia source: base/subarray.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
```
-/
def trimmedParentCartesianZero {A : Type} (_index : A) (rest : List A)
    (trimmed : List A → List Index) : List Index := trimmed rest

/--
Julia source: base/subarray.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedpind() = ()
```
-/
def trimmedParentEmpty : List Index := []

/--
Julia source: base/subarray.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
```
-/
def trimmedViewIndicesSource {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (trimmed : List A → List Index) : List Index :=
  (axes index).map (fun _ => Index.colon) ++ trimmed rest

-- Source: base/subarray.jl:146
def trimmedViewIndices {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (_colon : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  trimmedViewIndicesSource index rest axes trimmed

/--
Julia source: base/subarray.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
```
-/
def trimmedViewCartesianZeroSource {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (trimmed : List A → List Index) : List Index :=
  (axes index).map (fun axis => Index.scalar axis.first) ++ trimmed rest

-- Source: base/subarray.jl:147
def trimmedViewCartesianZero {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (_first : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  trimmedViewCartesianZeroSource index rest axes trimmed

/--
Julia source: base/subarray.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedvind() = ()
```
-/
def trimmedViewEmpty : List Index := []

/--
Julia source: base/subarray.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedindex(i::ScalarIndex) = oftype(i, 1)
```
-/
def trimmedIndexScalar (index : Index) (ofType : Index → I64 → Index) : Index :=
  ofType index (int64 1)

/--
Julia source: base/subarray.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedindex(i::AbstractRange) = i
```
-/
def trimmedIndexRange (index : Index) : Index := index

/--
Julia source: base/subarray.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
```
-/
def trimmedIndexDenseRange (index : Index) (length : Index → I64)
    (ofType : Index → Index → Index) (oneto : I64 → Index) : Index :=
  ofType index (oneto (length index))

/--
Julia source: base/subarray.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
```
-/
def trimmedIndexScalarArray {A : Type} (index : A)
    (eachindex : A → List IndexStyle → List Index) (reshape : List Index → List Axis → A)
    (axes : A → List Axis) (ofType : A → A → A) : A :=
  ofType index (reshape (eachindex index [.linear]) (axes index))

/--
Julia source: base/subarray.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
```
-/
def trimmedIndexCartesianZero {A : Type} (index : A) (copy : A → A)
    (ofType : A → A → A) : A := ofType index (copy index)

/--
Julia source: base/subarray.jl:155-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
    padding = ntuple(Returns(1), Val(N - 1))
    ax1 = eachindex(IndexLinear(), i)
    return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
end
```
-/
def trimmedIndexCartesianSource {m : Type → Type} [Monad m]
    {A AxisValue Axes Cartesian Shaped Result : Type} (rank : Nat) (index : A)
    (eachindex : IndexStyle → A → m AxisValue)
    (cartesianIndices : AxisValue → List I64 → m Cartesian)
    (reshape : Cartesian → Axes → m Shaped) (axes : A → m Axes)
    (oftype : A → Shaped → m Result) : m Result := do
  let padding := List.replicate (rank - 1) (int64 1)
  let ax1 ← eachindex .linear index
  let cartesian ← cartesianIndices ax1 padding
  let shape ← axes index
  let shaped ← reshape cartesian shape
  oftype index shaped

-- Source: base/subarray.jl:155-159
def trimmedIndexCartesian {A : Type} (rank : Nat) (index : A)
    (eachindex : A → List IndexStyle → List Index) (cartesianIndices : List Index → A)
    (reshape : A → List Axis → A) (axes : A → List Axis) (ofType : A → A → A) : A :=
  trimmedIndexCartesianSource (m := Id) rank index
    (fun style index => pure (eachindex index [style]))
    (fun axis padding => pure (cartesianIndices (axis ++ padding.map Index.scalar)))
    (fun value shape => pure (reshape value shape)) (fun index => pure (axes index))
    (fun index value => pure (ofType index value))

/--
Julia source: base/subarray.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
```
-/
def maybeReshapeParentOne {A : Type} (array : A) (reshape : A → Nat → Jl A) : Jl A :=
  reshape array 1

/--
Julia source: base/subarray.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
```
-/
def maybeReshapeVectorParent {A : Type} (array : A) (reshape : A → Nat → Jl A) : Jl A :=
  reshape array 1

/--
Julia source: base/subarray.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
```
-/
def maybeReshapeParentSameRank {A : Type} (array : A) (_dimensions : List Bool) : Jl A := .ok array

/--
Julia source: base/subarray.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
```
-/
def maybeReshapeParent {A : Type} (array : A) (dimensions : List Bool)
    (reshape : A → Nat → Jl A) : Jl A :=
  reshape array dimensions.length

/--
Julia source: base/subarray.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rm_singleton_indices(ndims::Tuple, J1, Js...) = (J1, rm_singleton_indices(IteratorsMD._splitrest(ndims, index_ndims(J1)), Js...)...)
```
-/
def removeSingletonIndices {A : Type} (dimensions : List Bool) (first : A) (rest : List A)
    (indexNdims : A → List Bool) (splitRest : List Bool → List Bool → List Bool)
    (recurse : List Bool → List A → List A) : List A :=
  first :: recurse (splitRest dimensions (indexNdims first)) rest

/--
Julia source: base/subarray.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rm_singleton_indices(::Tuple{}, ::ScalarIndex, Js...) = rm_singleton_indices((), Js...)
```
-/
def removeSingletonScalarEmpty {A : Type} (_scalar : A) (rest : List A)
    (recurse : List Bool → List A → List A) : List A := recurse [] rest

/--
Julia source: base/subarray.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rm_singleton_indices(::Tuple) = ()
```
-/
def removeSingletonIndicesEmpty {A : Type} : List A := []
/--
Julia source: base/subarray.jl:221-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(A::AbstractArray, I::Vararg{Any,M}) where {M}
    @inline
    J = map(i->unalias(A,i), to_indices(A, I))
    @boundscheck checkbounds(A, J...)
    J′ = rm_singleton_indices(ntuple(Returns(true), Val(ndims(A))), J...)
    unsafe_view(_maybe_reshape_parent(A, index_ndims(J′...)), J′...)
end
```
-/
def viewArray {A R : Type} (array : A) (indices : List Index)
    (unalias : A → Index → Index) (toIndices : A → List Index → List Index)
    (checkBounds : A → List Index → Jl Unit) (ndims : A → Nat)
    (removeSingletons : List Bool → List Index → List Index)
    (reshapeParent : A → List Bool → Jl A) (indexNdims : List Index → List Bool)
    (unsafeView : A → List Index → Jl R) : Jl R := do
  let J := (toIndices array indices).map (unalias array)
  checkBounds array J
  let dimensions := List.replicate (ndims array) true
  let JPrime := removeSingletons dimensions J
  let parent ← reshapeParent array (indexNdims JPrime)
  unsafeView parent JPrime

/--
Julia source: base/subarray.jl:230-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::AbstractUnitRange, r2::AbstractUnitRange{<:Integer})
    @_propagate_inbounds_meta
    getindex(r1, r2)
end
```
-/
def viewUnitRangeUnitRange {A B R : Type} (r1 : A) (r2 : B) (getindex : A → B → Jl R) : Jl R :=
  getindex r1 r2

/--
Julia source: base/subarray.jl:234-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::AbstractUnitRange, r2::StepRange{<:Integer})
    @_propagate_inbounds_meta
    getindex(r1, r2)
end
```
-/
def viewUnitRangeStepRange {A B R : Type} (r1 : A) (r2 : B) (getindex : A → B → Jl R) : Jl R :=
  getindex r1 r2

/--
Julia source: base/subarray.jl:238-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::StepRange, r2::AbstractRange{<:Integer})
    @_propagate_inbounds_meta
    getindex(r1, r2)
end
```
-/
def viewStepRangeAbstractRange {A B R : Type} (r1 : A) (r2 : B) (getindex : A → B → Jl R) : Jl R :=
  getindex r1 r2

/--
Julia source: base/subarray.jl:242-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::StepRangeLen, r2::OrdinalRange{<:Integer})
    @_propagate_inbounds_meta
    getindex(r1, r2)
end
```
-/
def viewStepRangeLenOrdinalRange {A B R : Type} (r1 : A) (r2 : B) (getindex : A → B → Jl R) : Jl R :=
  getindex r1 r2

/--
Julia source: base/subarray.jl:246-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::LinRange, r2::OrdinalRange{<:Integer})
    @_propagate_inbounds_meta
    getindex(r1, r2)
end
```
-/
def viewLinRangeOrdinalRange {A B R : Type} (r1 : A) (r2 : B) (getindex : A → B → Jl R) : Jl R :=
  getindex r1 r2

/--
Julia source: base/subarray.jl:252-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function view(r1::AbstractRange, c::Colon)
    @_propagate_inbounds_meta
    getindex(r1, c)
end
```
-/
def viewAbstractRangeColon {A R : Type} (r1 : A) (colon : Index) (getindex : A → Index → Jl R) : Jl R :=
  getindex r1 colon

/--
Julia source: base/subarray.jl:257-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_view(A::AbstractArray, I::Vararg{ViewIndex,N}) where {N}
    @inline
    SubArray(A, I)
end
```
-/
def unsafeViewArray {P T : Type} (array : P) (indices : List Index)
    (construct : P → List Index → Jl (SubArray P T)) : Jl (SubArray P T) :=
  construct array indices

/--
Julia source: base/subarray.jl:267-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_view(V::SubArray, I::Vararg{ViewIndex,N}) where {N} =
    (@inline; _maybe_reindex(V, I))
```
-/
def unsafeViewSubArray {P T : Type} (V : SubArray P T) (indices : List Index)
    (maybeReindex : SubArray P T → List Index → Jl (ReindexedView P T)) :
    Jl (ReindexedView P T) :=
  maybeReindex V indices

/--
Julia source: base/subarray.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reindex(V, I) = (@inline; _maybe_reindex(V, I, I))
```
-/
def maybeReindex {P T : Type} (V : SubArray P T) (indices : List Index)
    (dispatch : SubArray P T → List Index → List Index → Jl (ReindexedView P T)) :
    Jl (ReindexedView P T) :=
  dispatch V indices indices

/--
Julia source: base/subarray.jl:270-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reindex(V, I, ::Tuple{AbstractArray{<:AbstractCartesianIndex}, Vararg{Any}}) =
    (@inline; SubArray(V, I))
```
-/
def maybeReindexCartesianArray {P T : Type} (V : SubArray P T) (indices : List Index)
    (construct : SubArray P T → List Index → Jl (SubArray (SubArray P T) T)) :
    Jl (ReindexedView P T) := do
  let nested ← construct V indices
  pure (.nested nested)

/--
Julia source: base/subarray.jl:273-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reindex(V, I, A::Tuple{AbstractArray{<:AbstractCartesianIndex{1}}, Vararg{Any}}) =
    (@inline; _maybe_reindex(V, I, tail(A)))
```
-/
def maybeReindexCartesianVector {P T : Type} (V : SubArray P T) (indices tailIndices : List Index)
    (recurse : SubArray P T → List Index → List Index → Jl (ReindexedView P T)) :
    Jl (ReindexedView P T) :=
  recurse V indices tailIndices

/--
Julia source: base/subarray.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reindex(V, I, A::Tuple{Any, Vararg{Any}}) = (@inline; _maybe_reindex(V, I, tail(A)))
```
-/
def maybeReindexTail {P T : Type} (V : SubArray P T) (indices tailIndices : List Index)
    (recurse : SubArray P T → List Index → List Index → Jl (ReindexedView P T)) :
    Jl (ReindexedView P T) :=
  recurse V indices tailIndices

/--
Julia source: base/subarray.jl:276-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _maybe_reindex(V, I, ::Tuple{})
    @inline
    @inbounds idxs = to_indices(V.parent, reindex(V.indices, I))
    SubArray(V.parent, idxs)
end
```
-/
def maybeReindexEmpty {P T : Type} (V : SubArray P T) (indices : List Index)
    (reindex : List Index → List Index → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (construct : P → List Index → Jl (SubArray P T)) : Jl (ReindexedView P T) := do
  let reindexed ← reindex V.indices indices
  let indices ← toIndices V.parent reindexed
  let flattened ← construct V.parent indices
  pure (.flattened flattened)
/--
Julia source: base/subarray.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(::Tuple{}, ::Tuple{}) = ()
```
-/
def reindexEmpty : Jl (List Index) := .ok []

/--
Julia source: base/subarray.jl:295-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(idxs::Tuple{ScalarIndex, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) =
    (@_propagate_inbounds_meta; (idxs[1], reindex(tail(idxs), subidxs)...))
```
-/
def reindexScalar (index : Index) (rest subindices : List Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  let tail ← reindex rest subindices
  pure (index :: tail)

/--
Julia source: base/subarray.jl:299-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(idxs::Tuple{Slice, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
    (@_propagate_inbounds_meta; (subidxs[1], reindex(tail(idxs), tail(subidxs))...))
```
-/
def reindexSlice (rest subindices : List Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  match subindices with
  | [] => .error .boundsError
  | index :: subindices =>
      let tail ← reindex rest subindices
      pure (index :: tail)

/--
Julia source: base/subarray.jl:303-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(idxs::Tuple{AbstractVector, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
    (@_propagate_inbounds_meta; (idxs[1][subidxs[1]], reindex(tail(idxs), tail(subidxs))...))
```
-/
def reindexVector (index : Index) (rest subindices : List Index)
    (getindex : Index → Index → Jl Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  match subindices with
  | [] => .error .boundsError
  | subindex :: subindices =>
      let value ← getindex index subindex
      let tail ← reindex rest subindices
      pure (value :: tail)

/--
Julia source: base/subarray.jl:307-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(idxs::Tuple{AbstractMatrix, Vararg{Any}}, subidxs::Tuple{Any, Any, Vararg{Any}}) =
    (@_propagate_inbounds_meta; (idxs[1][subidxs[1], subidxs[2]], reindex(tail(idxs), tail(tail(subidxs)))...))
```
-/
def reindexMatrix (index : Index) (rest subindices : List Index)
    (getindex : Index → Index → Index → Jl Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  match subindices with
  | first :: second :: subindices =>
      let value ← getindex index first second
      let tail ← reindex rest subindices
      pure (value :: tail)
  | _ => .error .boundsError

/--
Julia source: base/subarray.jl:311-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reindex(idxs::Tuple{AbstractArray{<:Any,N}, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) where {N} =
    (@_propagate_inbounds_meta; (idxs[1][subidxs[1:N]...], reindex(tail(idxs), subidxs[N+1:end])...))
```
-/
def reindexArraySource (rank : Nat) (index : Index) (rest subindices : List Index)
    (getindex : Index → List Index → Jl Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  if subindices.length < rank then .error .boundsError
  else do
    let selected := subindices.take rank
    let value ← getindex index selected
    let tail ← reindex rest (subindices.drop rank)
    pure (value :: tail)

-- Source: base/subarray.jl:311-312
def reindexArray (rank : Nat) (index : Index) (rest subindices : List Index)
    (getindex : Index → List Index → Jl Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) :=
  reindexArraySource rank index rest subindices getindex reindex

def reindexDispatch (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) : List Index → List Index → Jl (List Index)
  | [], [] => reindexEmpty
  | [], _ :: _ => .error (.methodError "reindex")
  | .scalar value :: rest, subindices => do
      let tail ← reindexDispatch getVector getMatrix getArray rest subindices
      pure (.scalar value :: tail)
  | .slice _ :: rest, [] => .error .boundsError
  | .slice _ :: rest, index :: subindices => do
      let tail ← reindexDispatch getVector getMatrix getArray rest subindices
      pure (index :: tail)
  | .colon :: _, _ => .error (.methodError "reindex")
  | .other :: _, _ => .error (.methodError "reindex")
  | .cartesian _ :: _, _ => .error (.methodError "reindex")
  | index :: rest, subindices =>
      match index.indexAxes.length with
      | 1 =>
          match subindices with
          | [] => .error .boundsError
          | subindex :: subindices => do
              let value ← getVector index subindex
              let tail ← reindexDispatch getVector getMatrix getArray rest subindices
              pure (value :: tail)
      | 2 =>
          match subindices with
          | first :: second :: subindices => do
              let value ← getMatrix index first second
              let tail ← reindexDispatch getVector getMatrix getArray rest subindices
              pure (value :: tail)
          | _ => .error .boundsError
      | rank => do
          if subindices.length < rank then return ← .error .boundsError
          let value ← getArray index (subindices.take rank)
          let tail ← reindexDispatch getVector getMatrix getArray rest (subindices.drop rank)
          pure (value :: tail)
termination_by structural indices subindices => indices

def maybeReindexDispatch {P T : Type} (view : SubArray P T) (indices : List Index)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index))
    (constructParent : P → List Index → Jl (SubArray P T))
    (constructNested : SubArray P T → List Index → Jl (SubArray (SubArray P T) T)) :
    List Index → Jl (ReindexedView P T)
  | [] =>
      maybeReindexEmpty view indices
        (reindexDispatch getVector getMatrix getArray) toIndices constructParent
  | .cartesianValues _ elementRank _ :: rest =>
      if elementRank = 1 then
        maybeReindexDispatch view indices getVector getMatrix getArray
          toIndices constructParent constructNested rest
      else maybeReindexCartesianArray view indices constructNested
  | _ :: rest =>
      maybeReindexDispatch view indices getVector getMatrix getArray
        toIndices constructParent constructNested rest
termination_by structural scan => scan
/--
Julia source: base/subarray.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _reindexlinear(V::FastSubArray, i::Int) = V.offset1 + V.stride1*i
```
-/
def reindexLinear {P T : Type} (V : SubArray P T) (index : I64) : I64 :=
  iadd V.offset1 (imul V.stride1 index)
/--
Julia source: base/subarray.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _reindexlinear(V::FastContiguousSubArray, i::Int) = V.offset1 + i
```
-/
def reindexLinearContiguous {P T : Type} (V : SubArray P T) (index : I64) : I64 :=
  iadd V.offset1 index

/-- Trusted dispatch for `_reindexlinear` on the FastContiguousSubArray type alias. -/
def reindexLinearDispatch {P T : Type} (view : SubArray P T) (index : I64) : I64 :=
  if (match view.indices with
    | [] => true
    | first :: _ => first.isUnitRange || Index.allScalar view.indices) then
    reindexLinearContiguous view index
  else reindexLinear view index

/--
Julia source: base/subarray.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _reindexlinear(V::FastSubArray, i::AbstractUnitRange{Int}) = V.offset1 .+ V.stride1 .* i
```
-/
def reindexLinearUnitRangeSource {V I M A R : Type} (view : V) (indices : I)
    (offset stride : V → I64)
    (broadcastMultiply : I64 → I → Jl M) (broadcastAdd : I64 → M → Jl A)
    (materialize : A → Jl R) : Jl R := do
  let scaled ← broadcastMultiply (stride view) indices
  let expression ← broadcastAdd (offset view) scaled
  materialize expression

-- Source: base/subarray.jl:328
def reindexLinearUnitRange {P T R : Type} (V : SubArray P T) (indices : R)
    (broadcastMultiply : I64 → R → Jl R) (broadcastAdd : I64 → R → Jl R) : Jl R :=
  reindexLinearUnitRangeSource V indices SubArray.offset1 SubArray.stride1
    broadcastMultiply broadcastAdd .ok

/--
Julia source: base/subarray.jl:316-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(V::SubArray{T,N}, I::Vararg{Int,N}) where {T,N}
    @inline
    @boundscheck checkbounds(V, I...)
    @inbounds r = V.parent[reindex(V.indices, I)...]
    r
end
```
-/
def getindexSubArray {P T R : Type} (V : SubArray P T) (indices : List I64)
    (checkBounds : SubArray P T → List I64 → Jl Unit)
    (reindex : List Index → List Index → Jl (List Index))
    (getParent : P → List Index → Jl R) : Jl R := do
  checkBounds V indices
  let parentIndices ← reindex V.indices (indices.map Index.scalar)
  getParent V.parent parentIndices

/--
Julia source: base/subarray.jl:330-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(V::FastSubArray, i::Int)
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds r = V.parent[_reindexlinear(V, i)]
    r
end
```
-/
def getindexFastSubArray {P T R : Type} (V : SubArray P T) (index : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (getParent : P → I64 → Jl R) : Jl R := do
  checkBounds V index
  getParent V.parent (reindexLinearDispatch V index)

/--
Julia source: base/subarray.jl:339-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(V::FastSubArray{<:Any, 1}, i::Int)
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds r = V.parent[_reindexlinear(V, i)]
    r
end
```
-/
def getindexFastVectorSubArray {P T R : Type} (V : SubArray P T) (index : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (getParent : P → I64 → Jl R) : Jl R := do
  checkBounds V index
  getParent V.parent (reindexLinearDispatch V index)


/--
Julia source: base/subarray.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _reindexlinear(V::FastContiguousSubArray, i::AbstractUnitRange{Int}) = V.offset1 .+ i
```
-/
def reindexLinearContiguousUnitRangeSource {V I A R : Type} (view : V) (indices : I)
    (offset : V → I64) (broadcastAdd : I64 → I → Jl A)
    (materialize : A → Jl R) : Jl R := do
  materialize (← broadcastAdd (offset view) indices)

-- Source: base/subarray.jl:352
def reindexLinearContiguousUnitRange {P T R : Type} (V : SubArray P T) (indices : R)
    (broadcastAdd : I64 → R → Jl R) : Jl R :=
  reindexLinearContiguousUnitRangeSource V indices SubArray.offset1 broadcastAdd .ok

/--
Julia source: base/subarray.jl:376-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(V::FastContiguousSubArray, i::_OneBasedRanges)
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds r = V.parent[_reindexlinear(V, i)]
    r
end
```
-/
def getindexFastContiguousRange {P T I O Q : Type} (V : SubArray P T) (index : I)
    (checkBounds : SubArray P T → I → Jl Unit)
    (reindex : SubArray P T → I → Jl Q)
    (getParent : P → Q → Jl O) : Jl O := do
  checkBounds V index
  let parentIndex ← reindex V index
  getParent V.parent parentIndex

/--
Julia source: base/subarray.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline getindex(V::FastContiguousSubArray, i::Colon) = getindex(V, to_indices(V, (:,))...)
```
-/
def getindexFastContiguousColonSource {V R : Type} (view : V)
    (toIndices : V → List Index → Jl (List Index))
    (getindex : V → List Index → Jl R) : Jl R := do
  let indices ← toIndices view [.colon]
  getindex view indices

-- Source: base/subarray.jl:383
def getindexFastContiguousColon {P T R : Type} (V : SubArray P T) (_colon : Index)
    (toIndices : SubArray P T → List Index → Jl (List Index))
    (getindex : SubArray P T → Index → Jl R) : Jl R :=
  getindexFastContiguousColonSource V toIndices fun view indices =>
    match indices with
    | [index] => getindex view index
    | _ => .error (.methodError "getindex")
/--
Julia source: base/subarray.jl:386-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(V::SubArray{T,N}, x, I::Vararg{Int,N}) where {T,N}
    @inline
    @boundscheck checkbounds(V, I...)
    @inbounds V.parent[reindex(V.indices, I)...] = x
    V
end
```
-/
def setindexSubArray {P T R : Type} (V : SubArray P T) (value : R) (indices : List I64)
    (checkBounds : SubArray P T → List I64 → Jl Unit)
    (reindex : List Index → List Index → Jl (List Index))
    (setParent : P → List Index → R → Jl P) : Jl (SubArray P T) := do
  checkBounds V indices
  let parentIndices ← reindex V.indices (indices.map Index.scalar)
  let parent ← setParent V.parent parentIndices value
  pure {V with parent}

/--
Julia source: base/subarray.jl:392-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(V::FastSubArray, x, i::Int)
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds V.parent[_reindexlinear(V, i)] = x
    V
end
```
-/
def setindexFastSubArray {P T R : Type} (V : SubArray P T) (value : R) (index : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (setParent : P → I64 → R → Jl P) : Jl (SubArray P T) := do
  checkBounds V index
  let parent ← setParent V.parent (reindexLinearDispatch V index) value
  pure {V with parent}

/--
Julia source: base/subarray.jl:398-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(V::FastSubArray{<:Any, 1}, x, i::Int)
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds V.parent[_reindexlinear(V, i)] = x
    V
end
```
-/
def setindexFastVectorSubArray {P T R : Type} (V : SubArray P T) (value : R) (index : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (setParent : P → I64 → R → Jl P) : Jl (SubArray P T) := do
  checkBounds V index
  let parent ← setParent V.parent (reindexLinearDispatch V index) value
  pure {V with parent}

/--
Julia source: base/subarray.jl:405-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(V::FastSubArray, x, i::AbstractUnitRange{Int})
    @inline
    @boundscheck checkbounds(V, i)
    @inbounds V.parent[_reindexlinear(V, i)] = x
    V
end
```
-/
def setindexFastUnitRange {P T R Q : Type} (V : SubArray P T) (value : R) (indices : Q)
    (checkBounds : SubArray P T → Q → Jl Unit)
    (reindex : SubArray P T → Q → Jl Q)
    (setParent : P → Q → R → Jl P) : Jl (SubArray P T) := do
  checkBounds V indices
  let parentIndices ← reindex V indices
  let parent ← setParent V.parent parentIndices value
  pure {V with parent}

/--
Julia source: base/subarray.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline setindex!(V::FastSubArray, x, i::Colon) = setindex!(V, x, to_indices(V, (i,))...)
```
-/
def setindexFastColonSource {V X : Type} (view : V) (value : X)
    (toIndices : V → List Index → Jl (List Index))
    (setindex : V → X → List Index → Jl V) : Jl V := do
  let indices ← toIndices view [.colon]
  setindex view value indices

-- Source: base/subarray.jl:412
def setindexFastColon {P T R : Type} (V : SubArray P T) (value : R) (_colon : Index)
    (toIndices : SubArray P T → List Index → Jl (List Index))
    (setindex : SubArray P T → R → Index → Jl (SubArray P T)) : Jl (SubArray P T) :=
  setindexFastColonSource V value toIndices fun view value indices =>
    match indices with
    | [index] => setindex view value index
    | _ => .error (.methodError "setindex!")

/--
Julia source: base/subarray.jl:414-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(V::SubArray{T,N}, I::Vararg{Int,N}) where {T,N}
    @inline
    @boundscheck checkbounds(Bool, V, I...) || return false
    @inbounds r = isassigned(V.parent, reindex(V.indices, I)...)
    r
end
```
-/
def isassignedSubArray {P T : Type} (V : SubArray P T) (indices : List I64)
    (checkBounds : SubArray P T → List I64 → Bool)
    (reindex : List Index → List Index → Jl (List Index))
    (isassignedParent : P → List Index → Jl Bool) : Jl Bool := do
  if !(checkBounds V indices) then return false
  let parentIndices ← reindex V.indices (indices.map Index.scalar)
  isassignedParent V.parent parentIndices

/--
Julia source: base/subarray.jl:420-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(V::FastSubArray, i::Int)
    @inline
    @boundscheck checkbounds(Bool, V, i) || return false
    @inbounds r = isassigned(V.parent, _reindexlinear(V, i))
    r
end
```
-/
def isassignedFastSubArray {P T : Type} (V : SubArray P T) (index : I64)
    (checkBounds : SubArray P T → I64 → Bool)
    (isassignedParent : P → I64 → Jl Bool) : Jl Bool := do
  if !(checkBounds V index) then return false
  isassignedParent V.parent (reindexLinearDispatch V index)

/--
Julia source: base/subarray.jl:426-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(V::FastSubArray{<:Any, 1}, i::Int)
    @inline
    @boundscheck checkbounds(Bool, V, i) || return false
    @inbounds r = isassigned(V.parent, _reindexlinear(V, i))
    r
end
```
-/
def isassignedFastVectorSubArray {P T : Type} (V : SubArray P T) (index : I64)
    (checkBounds : SubArray P T → I64 → Bool)
    (isassignedParent : P → I64 → Jl Bool) : Jl Bool := do
  if !(checkBounds V index) then return false
  isassignedParent V.parent (reindexLinearDispatch V index)

/--
Julia source: base/subarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:FastSubArray}) = IndexLinear()
```
-/
def indexStyleFastSubArray : IndexStyle := .linear

/--
Julia source: base/subarray.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strides(V::SubArray) = substrides(strides(V.parent), V.indices)
```
-/
def stridesSubArray {P T : Type} (V : SubArray P T) (strides : P → Jl (List I64))
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  substrides (← strides V.parent) V.indices

/--
Julia source: base/subarray.jl:439-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::Tuple{}, ::Tuple{}) = ()
```
-/
def substridesEmpty : Jl (List I64) := .ok []

/--
Julia source: base/subarray.jl:440-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{ScalarIndex, Vararg{Any}}) where N = (substrides(tail(strds), tail(I))...,)
```
-/
def substridesScalarSource (strides : List I64) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  let tail ← Models1Group17.tupleTail strides
  substrides tail rest

-- Source: base/subarray.jl:440
def substridesScalar (strides : List I64) (_scalar : Index) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) :=
  substridesScalarSource strides rest substrides

/--
Julia source: base/subarray.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{Slice, Vararg{Any}}) where N = (first(strds), substrides(tail(strds), tail(I))...)
```
-/
def substridesSliceSource (strides : List I64) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  let stride ← Models1Group17.tupleFirst strides
  let tail ← Models1Group17.tupleTail strides
  let rest ← substrides tail rest
  pure (stride :: rest)

-- Source: base/subarray.jl:441
def substridesSlice (strides : List I64) (_slice : Index) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) :=
  substridesSliceSource strides rest substrides

/--
Julia source: base/subarray.jl:442-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{AbstractRange, Vararg{Any}}) where N = (first(strds)*Int(step(I[1])), substrides(tail(strds), tail(I))...)
```
-/
def substridesRangeSource {StepValue : Type} (strides : List I64) (index : Index) (rest : List Index)
    (step : Index → Jl StepValue) (toInt : StepValue → Jl I64)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  let stride ← Models1Group17.tupleFirst strides
  let step ← step index
  let step ← toInt step
  let product := imul stride step
  let tail ← Models1Group17.tupleTail strides
  let rest ← substrides tail rest
  pure (product :: rest)

-- Source: base/subarray.jl:442
def substridesRange (strides : List I64) (index : Index) (rest : List Index)
    (step : Index → I64) (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) :=
  substridesRangeSource strides index rest (fun index => .ok (step index)) .ok substrides

/--
Julia source: base/subarray.jl:443-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds, I::Tuple{Any, Vararg{Any}}) = throw(ArgumentError(
    LazyString("strides is invalid for SubArrays with indices of type ", typeof(I[1]))))
```
-/
def substridesInvalid (strides : List I64) (indexType : String) : Jl (List I64) :=
  .error (.argumentError s!"strides is invalid for SubArrays with indices of type {indexType}")

def substridesDispatch (step : Index → I64) (typeName : Index → String) :
    List I64 → List Index → Jl (List I64)
  | [], [] => substridesEmpty
  | _ :: _, [] => .error (.methodError "substrides")
  | strides, .scalar value :: rest =>
      substridesScalar strides (.scalar value) rest
        (fun tail _ => substridesDispatch step typeName tail rest)
  | strides, .slice axis :: rest =>
      substridesSlice strides (.slice axis) rest
        (fun tail _ => substridesDispatch step typeName tail rest)
  | strides, index :: rest =>
      if Index.isRange index then
        substridesRange strides index rest step
          (fun tail _ => substridesDispatch step typeName tail rest)
      else substridesInvalid strides (typeName index)
termination_by structural strides indices => indices

/--
Julia source: base/subarray.jl:446-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stride(V::SubArray, d::Integer) = d <= ndims(V) ? strides(V)[d] : strides(V)[end] * size(V)[end]
```
-/
def strideSubArraySource {V D : Type} (view : V) (dimension : D)
    (ndims : V → Jl Nat) (le : D → Nat → Jl Bool)
    (strides size : V → Jl (List I64))
    (get : List I64 → D → Jl I64) (last : List I64 → Jl I64) : Jl I64 := do
  let rank ← ndims view
  if ← le dimension rank then
    get (← strides view) dimension
  else
    let stride ← last (← strides view)
    let count ← last (← size view)
    pure (imul stride count)

-- Source: base/subarray.jl:446
def strideSubArray {P T D : Type} (V : SubArray P T) (dimension : D)
    (toInt : D → I64) (ndims : SubArray P T → Nat) (strides size : SubArray P T → Jl (List I64))
    (get : List I64 → I64 → Jl I64) (last : List I64 → Jl I64) : Jl I64 :=
  strideSubArraySource V dimension (fun view => .ok (ndims view))
    (fun d rank => .ok (decide ((toInt d).val ≤ (rank : Int))))
    strides size (fun values d => get values (toInt d)) last

/--
Julia source: base/subarray.jl:448-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(parent::AbstractArray, I::NTuple{N,Any}) where {N} =
    (@inline; compute_stride1(1, fill_to_length(axes(parent), OneTo(1), Val(N)), I))
```
-/
def computeStride1 {P : Type} (parent : P) (indices : List Index)
    (axes : P → List Axis) (fillToLength : List Axis → Axis → Nat → Jl (List Axis))
    (computeRec : I64 → List Axis → List Index → Jl I64) : Jl I64 := do
  let filled ← fillToLength (axes parent) { first := int64 1, last := int64 1 } indices.length
  computeRec (int64 1) filled indices

/--
Julia source: base/subarray.jl:450-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{}) = s
```
-/
def computeStride1Empty (stride : I64) (_indices : List Axis) : Jl I64 := .ok stride

/--
Julia source: base/subarray.jl:451-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{Vararg{ScalarIndex}}) = s
```
-/
def computeStride1Scalars (stride : I64) (_indices : List Axis) (_scalars : List Index) : Jl I64 := .ok stride

/--
Julia source: base/subarray.jl:452-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{ScalarIndex, Vararg{Any}}) =
    (@inline; compute_stride1(s*Int(length(inds[1])), tail(inds), tail(I)))
```
-/
def computeStride1ScalarSource {S A Next R : Type} (stride : S) (axes : List A)
    (rest : List Index) (lengthInt : A → Jl I64) (mul : S → I64 → Jl Next)
    (recurse : Next → List A → List Index → Jl R) : Jl R := do
  let axis ← match axes with
    | [] => .error .boundsError
    | axis :: _ => .ok axis
  let size ← lengthInt axis
  let next ← mul stride size
  recurse next (axes.drop 1) rest

-- Source: base/subarray.jl:452-453
def computeStride1Scalar (stride : I64) (axes : List Axis) (_scalar : Index) (rest : List Index)
    (length : Axis → I64) (computeRec : I64 → List Axis → List Index → Jl I64) : Jl I64 :=
  computeStride1ScalarSource stride axes rest (fun axis => .ok (length axis))
    (fun a b => .ok (imul a b)) computeRec

/--
Julia source: base/subarray.jl:454-454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{AbstractRange, Vararg{Any}}) = s * Int(step(I[1]))
```
-/
def computeStride1RangeSource {S I Step R : Type} (stride : S) (range : I)
    (step : I → Jl Step) (toInt : Step → Jl I64) (mul : S → I64 → Jl R) : Jl R := do
  let increment ← step range
  mul stride (← toInt increment)

-- Source: base/subarray.jl:454
def computeStride1Range (stride : I64) (_axes : List Axis) (range : Index)
    (step : Index → I64) : Jl I64 :=
  computeStride1RangeSource stride range (fun range => .ok (step range)) .ok
    (fun a b => .ok (imul a b))

/--
Julia source: base/subarray.jl:455-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{Slice, Vararg{Any}}) = s
```
-/
def computeStride1Slice (stride : I64) (_axes : List Axis) (_slice : Index)
    (_rest : List Index) : Jl I64 := .ok stride

/--
Julia source: base/subarray.jl:456-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{Any, Vararg{Any}}) = throw(ArgumentError(LazyString("invalid strided index type ", typeof(I[1]))))
```
-/
def computeStride1Invalid (_stride : I64) (_axes : List Axis) (index : Index)
    (typeName : Index → String) : Jl I64 :=
  .error (.argumentError s!"invalid strided index type {typeName index}")

def computeStride1Dispatch (length : Axis → I64) (step : Index → I64)
    (typeName : Index → String) : I64 → List Axis → List Index → Jl I64
  | stride, axes, [] => computeStride1Empty stride axes
  | stride, axes, .scalar value :: rest =>
      if rest.all Index.isScalar then computeStride1Scalars stride axes (.scalar value :: rest)
      else
        match axes with
        | [] => .error .boundsError
        | axis :: tail => computeStride1Dispatch length step typeName
            (imul stride (length axis)) tail rest
  | stride, axes, .slice axis :: rest =>
      computeStride1Slice stride axes (.slice axis) rest
  | stride, axes, index :: _ =>
      if Index.isRange index then computeStride1Range stride axes index step
      else computeStride1Invalid stride axes index typeName
termination_by structural stride axes indices => indices
/--
Julia source: base/subarray.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(::Type{<:SubArray{<:Any,<:Any,P}}) where {P} = elsize(P)
```
-/
def elsizeSubArray {P T : Type} (_view : SubArray P T) (elsize : Type → I64) : I64 :=
  elsize P

/--
Julia source: base/subarray.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscontiguous(A::SubArray) = iscontiguous(typeof(A))
```
-/
def iscontiguousSubArray {P T : Type} (_array : SubArray P T)
    (iscontiguousType : Type → Bool) : Bool :=
  iscontiguousType (SubArray P T)

/--
Julia source: base/subarray.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscontiguous(::Type{<:SubArray}) = false
```
-/
def iscontiguousSubArrayType : Bool := false

/--
Julia source: base/subarray.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscontiguous(::Type{<:FastContiguousSubArray}) = true
```
-/
def iscontiguousFastContiguousSubArrayType : Bool := true

/--
Julia source: base/subarray.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first_index(V::FastSubArray) = V.offset1 + V.stride1 * firstindex(V) # cached for fast linear SubArrays
```
-/
def firstIndexFastSubArraySource {m : Type → Type} [Monad m] {V I Product R : Type}
    (view : V) (offset stride : V → I64) (firstindex : V → m I)
    (mul : I64 → I → m Product) (add : I64 → Product → m R) : m R := do
  let first ← firstindex view
  add (offset view) (← mul (stride view) first)

-- Source: base/subarray.jl:464
def firstIndexFastSubArray {P T : Type} (V : SubArray P T)
    (firstindex : SubArray P T → I64) : I64 :=
  firstIndexFastSubArraySource (m := Id) V SubArray.offset1 SubArray.stride1
    (fun view => pure (firstindex view)) (fun a b => pure (imul a b))
    (fun a b => pure (iadd a b))

/--
Julia source: base/subarray.jl:465-465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first_index(V::SubArray) = compute_linindex(parent(V), V.indices)
```
-/
def firstIndexSubArray {P T : Type} (V : SubArray P T)
    (computeLinindex : P → List Index → Jl I64) : Jl I64 :=
  computeLinindex (parentSubArray V) V.indices

/--
Julia source: base/subarray.jl:471-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent::AbstractVector, stride1::Integer, I::Tuple{AbstractRange}) =
    (@inline; Int(first(I[1])) - stride1*Int(first(axes1(I[1]))))
```
-/
def computeOffset1VectorRangeSource {I S Product R : Type} (index : I) (stride : S)
    (firstInt axisFirstInt : I → Jl I64) (mul : S → I64 → Jl Product)
    (sub : I64 → Product → Jl R) : Jl R := do
  let first ← firstInt index
  let origin ← axisFirstInt index
  sub first (← mul stride origin)

-- Source: base/subarray.jl:471-472
def computeOffset1VectorRange (index : Index) (stride1 : I64)
    (first : Index → Jl I64) (axes1First : Index → Jl I64) : Jl I64 :=
  computeOffset1VectorRangeSource index stride1 first axes1First
    (fun a b => .ok (imul a b)) (fun a b => .ok (isub a b))

/--
Julia source: base/subarray.jl:478-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, I::Tuple) =
    (@inline; compute_offset1(parent, stride1, find_extended_dims(1, I...), find_extended_inds(I...), I))
```
-/
def computeOffset1 {P : Type} (parent : P) (stride1 : I64) (indices : List Index)
    (findExtendedDims : I64 → List Index → List I64)
    (findExtendedIndices : List Index → List Index)
    (dispatch : P → I64 → List I64 → List Index → List Index → Jl I64) : Jl I64 :=
  dispatch parent stride1 (findExtendedDims (int64 1) indices)
    (findExtendedIndices indices) indices

/--
Julia source: base/subarray.jl:480-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, dims::Tuple{Int}, inds::Tuple{Slice}, I::Tuple) =
    (@inline; compute_linindex(parent, I) - stride1*Int(first(axes(parent, dims[1]))))  # index-preserving case
```
-/
def computeOffset1SliceSource {P I S Product R : Type} (parent : P) (stride : S)
    (dimension : I64) (indices : I) (linear : P → I → Jl I64)
    (axisFirstInt : P → I64 → Jl I64) (mul : S → I64 → Jl Product)
    (sub : I64 → Product → Jl R) : Jl R := do
  let address ← linear parent indices
  let origin ← axisFirstInt parent dimension
  sub address (← mul stride origin)

-- Source: base/subarray.jl:480-481
def computeOffset1Slice {P : Type} (parent : P) (stride1 : I64) (dimension : I64)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64)
    (axisFirst : P → I64 → Jl I64) : Jl I64 :=
  computeOffset1SliceSource parent stride1 dimension indices computeLinindex axisFirst
    (fun a b => .ok (imul a b)) (fun a b => .ok (isub a b))

/--
Julia source: base/subarray.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, dims, inds::Tuple{AbstractRange}, I::Tuple) =
    (@inline; compute_linindex(parent, I) - stride1*Int(first(axes1(inds[1])))) # potentially index-offsetting case
```
-/
def computeOffset1RangeSource {P I A S Product R : Type} (parent : P) (stride : S)
    (index : A) (indices : I) (linear : P → I → Jl I64)
    (axisFirstInt : A → Jl I64) (mul : S → I64 → Jl Product)
    (sub : I64 → Product → Jl R) : Jl R := do
  let address ← linear parent indices
  let origin ← axisFirstInt index
  sub address (← mul stride origin)

-- Source: base/subarray.jl:482-483
def computeOffset1Range {P : Type} (parent : P) (stride1 : I64) (index : Index)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64)
    (axisFirst : Index → Jl I64) : Jl I64 :=
  computeOffset1RangeSource parent stride1 index indices computeLinindex axisFirst
    (fun a b => .ok (imul a b)) (fun a b => .ok (isub a b))

/--
Julia source: base/subarray.jl:484-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, dims, inds, I::Tuple) =
    (@inline; compute_linindex(parent, I) - stride1)
```
-/
def computeOffset1FallbackSource {P I S R : Type} (parent : P) (stride : S) (indices : I)
    (linear : P → I → Jl I64) (sub : I64 → S → Jl R) : Jl R := do
  sub (← linear parent indices) stride

-- Source: base/subarray.jl:484-485
def computeOffset1Fallback {P : Type} (parent : P) (stride1 : I64)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64) : Jl I64 :=
  computeOffset1FallbackSource parent stride1 indices computeLinindex
    (fun a b => .ok (isub a b))

/--
Julia source: base/subarray.jl:486-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_linindex(parent, I::NTuple{N,Any}) where N
    @inline
    IP = fill_to_length(axes(parent), OneTo(1), Val(N))
    compute_linindex(Int(first(LinearIndices(parent))), 1, IP, I)
end
```
-/
def computeLinindex {P : Type} (parent : P) (indices : List Index)
    (axes : P → List Axis) (fillToLength : List Axis → Axis → Nat → Jl (List Axis))
    (firstLinearIndex : P → Jl I64)
    (computeRec : I64 → I64 → List Axis → List Index → Jl I64) : Jl I64 := do
  let parentIndices ← fillToLength (axes parent) { first := int64 1, last := int64 1 } indices.length
  let firstIndex ← firstLinearIndex parent
  computeRec firstIndex (int64 1) parentIndices indices

/--
Julia source: base/subarray.jl:491-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_linindex(f, s, IP::Tuple, I::Tuple{Any, Any, Vararg{Any}})
    @inline
    Δi = Int(first(I[1])) - Int(first(IP[1]))
    compute_linindex(f + Δi*s, s*Int(length(IP[1])), tail(IP), tail(I))
end
```
-/
def computeLinindexMany {A : Type} (f stride : I64) (axes : List Axis)
    (index : Index) (rest : List Index) (first : Index → Jl I64)
    (axisFirst length : Axis → I64)
    (computeRec : I64 → I64 → List Axis → List Index → Jl I64) : Jl I64 := do
  let delta ← first index
  let axis ← match axes with
    | [] => .error .boundsError
    | axis :: _ => .ok axis
  let offset := isub delta (axisFirst axis)
  computeRec (iadd f (imul offset stride)) (imul stride (length axis)) (axes.drop 1) rest

/--
Julia source: base/subarray.jl:496-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_linindex(f, s, IP::Tuple, I::Tuple{Any})
    @inline
    Δi = Int(first(I[1])) - Int(first(IP[1]))
    f + Δi*s
end
```
-/
def computeLinindexLast (f stride : I64) (axis : Axis) (index : Index)
    (first : Index → Jl I64) (axisFirst : Axis → I64) : Jl I64 := do
  let delta ← first index
  pure (iadd f (imul (isub delta (axisFirst axis)) stride))

/--
Julia source: base/subarray.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_linindex(f, s, IP::Tuple, I::Tuple{}) = f
```
-/
def computeLinindexEmpty (f _stride : I64) (_axes : List Axis) : Jl I64 := .ok f

def computeLinindexDispatch (first : Index → Jl I64)
    (axisFirst length : Axis → I64) : I64 → I64 → List Axis → List Index → Jl I64
  | f, stride, axes, [] => computeLinindexEmpty f stride axes
  | f, stride, axes, [index] =>
      match axes with
      | [] => .error .boundsError
      | axis :: _ => computeLinindexLast f stride axis index first axisFirst
  | f, stride, axes, index :: second :: rest =>
      match axes with
      | [] => .error .boundsError
      | axis :: tail => do
          let delta ← first index
          let offset := isub delta (axisFirst axis)
          computeLinindexDispatch first axisFirst length
            (iadd f (imul offset stride)) (imul stride (length axis)) tail (second :: rest)
termination_by structural f stride axes indices => indices

/--
Julia source: base/subarray.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_dims(dim, ::ScalarIndex, I...) = (@inline; find_extended_dims(dim + 1, I...))
```
-/
def findExtendedDimsScalar (dimension : I64) (_scalar : Index) (rest : List Index)
    (recurse : I64 → List Index → List I64) : List I64 :=
  recurse (iadd dimension (int64 1)) rest

/--
Julia source: base/subarray.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_dims(dim, i1, I...) = (@inline; (dim, find_extended_dims(dim + 1, I...)...))
```
-/
def findExtendedDimsIndex (dimension : I64) (_index : Index) (rest : List Index)
    (recurse : I64 → List Index → List I64) : List I64 :=
  dimension :: recurse (iadd dimension (int64 1)) rest

/--
Julia source: base/subarray.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_dims(dim) = ()
```
-/
def findExtendedDimsEmpty (_dimension : I64) : List I64 := []

/--
Julia source: base/subarray.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_inds(::ScalarIndex, I...) = (@inline; find_extended_inds(I...))
```
-/
def findExtendedIndicesScalar (_scalar : Index) (rest : List Index)
    (recurse : List Index → List Index) : List Index := recurse rest

/--
Julia source: base/subarray.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_inds(i1, I...) = (@inline; (i1, find_extended_inds(I...)...))
```
-/
def findExtendedIndicesIndex (index : Index) (rest : List Index)
    (recurse : List Index → List Index) : List Index := index :: recurse rest

/--
Julia source: base/subarray.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
find_extended_inds() = ()
```
-/
def findExtendedIndicesEmpty : List Index := []

def findExtendedDimsDispatch : I64 → List Index → List I64
  | _, [] => []
  | dimension, .scalar _ :: rest =>
      findExtendedDimsDispatch (iadd dimension (int64 1)) rest
  | dimension, _ :: rest =>
      dimension :: findExtendedDimsDispatch (iadd dimension (int64 1)) rest
termination_by structural dimension indices => indices

def findExtendedIndicesDispatch : List Index → List Index
  | [] => []
  | .scalar _ :: rest => findExtendedIndicesDispatch rest
  | index :: rest => index :: findExtendedIndicesDispatch rest
termination_by structural indices => indices

def computeOffset1Dispatch {P : Type} (parent : P) (stride1 : I64)
    (dimensions : List I64) (indices originalIndices : List Index)
    (isVector : P → Bool) (computeLinindex : P → List Index → Jl I64)
    (first : Index → Jl I64) (axes1First : Index → Jl I64)
    (axisFirst : P → I64 → Jl I64) : Jl I64 :=
  if isVector parent then
    match indices with
    | [index] =>
        if Index.isRange index then computeOffset1VectorRange index stride1 first axes1First
        else computeOffset1Fallback parent stride1 originalIndices computeLinindex
    | _ => computeOffset1Fallback parent stride1 originalIndices computeLinindex
  else
    match dimensions, indices with
    | [dimension], [.slice _] =>
        computeOffset1Slice parent stride1 dimension originalIndices computeLinindex axisFirst
    | _, [index] =>
        if Index.isRange index then computeOffset1Range parent stride1 index originalIndices
          computeLinindex axes1First
        else computeOffset1Fallback parent stride1 originalIndices computeLinindex
    | _, _ => computeOffset1Fallback parent stride1 originalIndices computeLinindex

/--
Julia source: base/subarray.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(V::FastSubArray, i::Int) = pointer(V.parent, V.offset1 + V.stride1*i)
```
-/
def pointerFastSubArray {P T R : Type} (V : SubArray P T) (index : I64)
    (pointerParent : P → I64 → Jl R) : Jl R :=
  pointerParent V.parent (reindexLinear V index)

/--
Julia source: base/subarray.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(V::FastContiguousSubArray, i::Int) = pointer(V.parent, V.offset1 + i)
```
-/
def pointerFastContiguousSubArray {P T R : Type} (V : SubArray P T) (index : I64)
    (pointerParent : P → I64 → Jl R) : Jl R :=
  pointerParent V.parent (reindexLinearContiguous V index)

/--
Julia source: base/subarray.jl:513-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pointer(V::SubArray{<:Any,<:Any,<:Array,<:Tuple{Vararg{RangeIndex}}}, is::AbstractCartesianIndex{N}) where {N}
    index = first_index(V)
    strds = strides(V)
    for d = 1:N
        index += (is[d]-1)*strds[d]
    end
    return pointer(V.parent, index)
end
```
-/
def pointerCartesianSubArraySource {V I Address Strides Coordinate Delta Stride Product R : Type}
    (view : V) (indices : I) (rank : Nat)
    (firstIndex : V → Jl Address) (strides : V → Jl Strides)
    (coordinate : I → I64 → Jl Coordinate) (subtract : Coordinate → I64 → Jl Delta)
    (strideAt : Strides → I64 → Jl Stride) (mul : Delta → Stride → Jl Product)
    (add : Address → Product → Jl Address) (pointer : V → Address → Jl R) : Jl R := do
  let mut index ← firstIndex view
  let strds ← strides view
  for d in [:rank] do
    let dimension := int64 ((d : Int) + 1)
    let displacement ← subtract (← coordinate indices dimension) (int64 1)
    let product ← mul displacement (← strideAt strds dimension)
    index ← add index product
  pointer view index

-- Source: base/subarray.jl:513-520
def pointerCartesianSubArray {P T R : Type} (V : SubArray P T) (indices : List I64)
    (firstIndex : SubArray P T → Jl I64) (strides : SubArray P T → Jl (List I64))
    (atOneBased : List I64 → I64 → Jl I64) (pointerParent : P → I64 → Jl R) : Jl R :=
  pointerCartesianSubArraySource V indices indices.length firstIndex strides atOneBased
    (fun a b => .ok (isub a b)) atOneBased
    (fun a b => .ok (imul a b)) (fun a b => .ok (iadd a b))
    (fun view address => pointerParent view.parent address)

/--
Julia source: base/subarray.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(S::SubArray) = (@inline; _indices_sub(S.indices...))
```
-/
def axesSubArray {P T : Type} (S : SubArray P T)
    (indicesSub : List Index → List Axis) : List Axis := indicesSub S.indices

/--
Julia source: base/subarray.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indices_sub(::Real, I...) = (@inline; _indices_sub(I...))
```
-/
def indicesSubScalar (_scalar : Index) (rest : List Index)
    (indicesSub : List Index → List Axis) : List Axis := indicesSub rest

/--
Julia source: base/subarray.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indices_sub() = ()
```
-/
def indicesSubEmpty : List Axis := []

/--
Julia source: base/subarray.jl:528-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _indices_sub(i1::AbstractArray, I...)
    @inline
    (axes(i1)..., _indices_sub(I...)...)
end
```
-/
def indicesSubArray (index : Index) (rest : List Index)
    (axes : Index → List Axis) (indicesSub : List Index → List Axis) : List Axis :=
  axes index ++ indicesSub rest

def indicesSubDispatch : List Index → List Axis
  | [] => indicesSubEmpty
  | .scalar _ :: rest => indicesSubDispatch rest
  | index :: rest => Index.indexAxes index ++ indicesSubDispatch rest
termination_by structural indices => indices

def axesSubArrayModel {P T : Type} (view : SubArray P T) : List Axis :=
  axesSubArray view indicesSubDispatch


/--
Julia source: base/subarray.jl:533-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(::SubArray{<:Any,0}) = OneTo(1)
```
-/
def axes1ZeroDimSubArray : Axis := { first := int64 1, last := int64 1 }

/--
Julia source: base/subarray.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes1(S::SubArray) = (@inline; _axes1_sub(S.indices...))
```
-/
def axes1SubArray {P T : Type} (S : SubArray P T)
    (axes1Sub : List Index → Option Axis) : Option Axis := axes1Sub S.indices

/--
Julia source: base/subarray.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes1_sub() = ()
```
-/
def axes1SubEmpty : Option Axis := none

/--
Julia source: base/subarray.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
```
-/
def axes1SubScalar (_scalar : Index) (rest : List Index)
    (axes1Sub : List Index → Option Axis) : Option Axis := axes1Sub rest

/--
Julia source: base/subarray.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
```
-/
def axes1SubZeroDimArray (_array : Index) (rest : List Index)
    (axes1Sub : List Index → Option Axis) : Option Axis := axes1Sub rest

/--
Julia source: base/subarray.jl:538-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _axes1_sub(i1::AbstractArray, I...)
    @inline
    axes1(i1)
end
```
-/
def axes1SubFirstArray (index : Index) (_rest : List Index)
    (axes1 : Index → Option Axis) : Option Axis := axes1 index

def axes1SubDispatch : List Index → Option Axis
  | [] => axes1SubEmpty
  | .scalar _ :: rest => axes1SubDispatch rest
  | .values [] _ :: rest => axes1SubDispatch rest
  | .cartesianValues [] _ _ :: rest => axes1SubDispatch rest
  | index :: _ => (Index.indexAxes index).head?
termination_by structural indices => indices

def axes1SubArrayModel {P T : Type} (view : SubArray P T) : Option Axis :=
  if view.dimensions.length = 0 then some axes1ZeroDimSubArray
  else axes1SubArray view axes1SubDispatch

/--
Julia source: base/subarray.jl:543-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(S::SubArray) = has_offset_axes(S.indices...)
```
-/
def hasOffsetAxesSubArray {P T : Type} (S : SubArray P T)
    (hasOffsetAxes : List Index → Bool) : Bool := hasOffsetAxes S.indices

/--
Julia source: base/subarray.jl:545-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_in_print_matrix(S::SubArray{<:Any,2,<:AbstractMatrix}, i::Integer, j::Integer, s::AbstractString)
    replace_in_print_matrix(S.parent, to_indices(S.parent, reindex(S.indices, (i,j)))..., s)
end
```
-/
def replaceInPrintMatrixSource {P T D : Type} (S : SubArray P T) (i j : D) (string : String)
    (reindex : List Index → List D → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → String → Jl String) : Jl String := do
  let indices ← reindex S.indices [i, j]
  let parentIndices ← toIndices S.parent indices
  replaceParent S.parent parentIndices string

-- Source: base/subarray.jl:545-547
def replaceInPrintMatrix {P T D : Type} (S : SubArray P T) (i j : D) (toInt : D → I64) (string : String)
    (reindex : List Index → List Index → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → String → Jl String) : Jl String :=
  replaceInPrintMatrixSource S i j string
    (fun parents indices => reindex parents (indices.map (fun i => Index.scalar (toInt i))))
    toIndices replaceParent

/--
Julia source: base/subarray.jl:548-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_in_print_matrix(S::SubArray{<:Any,1,<:AbstractVector}, i::Integer, j::Integer, s::AbstractString)
    replace_in_print_matrix(S.parent, to_indices(S.parent, reindex(S.indices, (i,)))..., j, s)
end
```
-/
def replaceInPrintVectorSource {P T D : Type} (S : SubArray P T) (i j : D) (string : String)
    (reindex : List Index → List D → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → D → String → Jl String) : Jl String := do
  let indices ← reindex S.indices [i]
  let parentIndices ← toIndices S.parent indices
  replaceParent S.parent parentIndices j string

-- Source: base/subarray.jl:548-550
def replaceInPrintVector {P T D : Type} (S : SubArray P T) (i j : D) (toInt : D → I64) (string : String)
    (reindex : List Index → List Index → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → I64 → String → Jl String) : Jl String :=
  replaceInPrintVectorSource S i j string
    (fun parents indices => reindex parents (indices.map (fun i => Index.scalar (toInt i))))
    toIndices (fun parent indices column text => replaceParent parent indices (toInt column) text)

/--
Julia source: base/subarray.jl:553-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(::Type{Vector{UInt8}}, s::FastContiguousSubArray{UInt8,1,Vector{UInt8}}) = unsafe_wrap(Vector{UInt8}, pointer(s), size(s))
```
-/
def unsafeWrapContiguousSubArraySource {V Pointer Result : Type} (view : V)
    (pointer : V → Jl Pointer) (size : V → Jl (List I64))
    (unsafeWrap : Pointer → List I64 → Jl Result) : Jl Result := do
  let ptr ← pointer view
  let dims ← size view
  unsafeWrap ptr dims

-- Source: base/subarray.jl:553
def unsafeWrapContiguousSubArray {P T R : Type} (view : SubArray P T)
    (pointer : SubArray P T → Jl R) (size : SubArray P T → Jl (List I64))
    (unsafeWrap : R → List I64 → Jl R) : Jl R :=
  unsafeWrapContiguousSubArraySource view pointer size unsafeWrap

structure ParentArrayOps (P : Type) where
  parentStyle : P → IndexStyle
  isArrayRank : P → Nat → Bool
  ndims : P → Jl Nat
  indexNdims : List Index → List Bool
  indexDimsum : List Index → List Bool
  ensureIndexable : List Index → List Index
  axes : P → List Axis
  strides : P → Jl (List I64)
  fillToLength : List Axis → Axis → Nat → Jl (List Axis)
  firstLinearIndex : P → Jl I64
  axisFirst : Axis → I64
  axisLength : Axis → I64
  indexFirst : Index → Jl I64
  indexStep : Index → I64
  indexTypeName : Index → String
  axes1First : Index → Jl I64
  isVector : P → Bool

def axisFirstAt (axes : List Axis) (dimension : I64) : Jl I64 :=
  match axes[dimension.val.toNat - 1]? with
  | some axis => .ok axis.first
  | none => .error .boundsError

def checkParentIndexMatchWithOps {P : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) : Jl Unit :=
  checkParentIndexMatch parent indices ops.indexNdims fun p dimensions =>
    if ops.isArrayRank p dimensions.length then checkParentIndexMatchArray p dimensions
    else checkParentIndexMatchMismatch p dimensions ops.ndims

def subarrayInnerConfigured {P T : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) (offset1 stride1 : I64)
    (linear : Bool) (dimensions : List Bool) : Jl (SubArray P T) :=
  subarrayInner parent indices offset1 stride1 linear dimensions
    (checkParentIndexMatchWithOps ops)

def computeLinindexWithOps {P : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) : Jl I64 :=
  computeLinindex parent indices ops.axes ops.fillToLength ops.firstLinearIndex
    (computeLinindexDispatch ops.indexFirst ops.axisFirst ops.axisLength)

def computeStride1WithOps {P : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) : Jl I64 :=
  computeStride1 parent indices ops.axes ops.fillToLength
    (computeStride1Dispatch ops.axisLength ops.indexStep ops.indexTypeName)

def computeOffset1WithOps {P : Type} (ops : ParentArrayOps P)
    (parent : P) (stride1 : I64) (indices : List Index) : Jl I64 :=
  computeOffset1 parent stride1 indices findExtendedDimsDispatch findExtendedIndicesDispatch
    (fun p stride dimensions nonScalarIndices originalIndices =>
      computeOffset1Dispatch p stride dimensions nonScalarIndices originalIndices ops.isVector
        (computeLinindexWithOps ops) ops.indexFirst ops.axes1First
        (fun p dimension => axisFirstAt (ops.axes p) dimension))

def computeLinearLayoutWithOps {P : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) : Jl (I64 × I64) :=
  computeLinearLayout parent indices (computeStride1WithOps ops) (computeOffset1WithOps ops)

def constructSubArrayByStyle {P T : Type} (ops : ParentArrayOps P)
    (style : IndexStyle) (parent : P) (indices : List Index) (dimensions : List Bool) :
    Jl (SubArray P T) :=
  match style with
  | .linear =>
      subarrayLinear parent indices dimensions (checkParentIndexMatchWithOps ops)
        (computeLinearLayoutWithOps ops)
  | .cartesian =>
      subarrayCartesian parent indices dimensions (checkParentIndexMatchWithOps ops)

def constructSubArrayConfigured {P T : Type} (ops : ParentArrayOps P)
    (parent : P) (indices : List Index) : Jl (SubArray P T) :=
  subarrayOuter parent indices viewIndexing ops.parentStyle indexStyleCombine
    ops.ensureIndexable ops.indexDimsum (constructSubArrayByStyle ops)

def parentArrayOpsSubArray {P T : Type} (ops : ParentArrayOps P)
    (firstLinearIndex : SubArray P T → Jl I64) : ParentArrayOps (SubArray P T) where
  parentStyle := fun view => if view.linear then .linear else .cartesian
  isArrayRank := fun view rank => decide (view.dimensions.length = rank)
  ndims := fun view => .ok view.dimensions.length
  indexNdims := ops.indexNdims
  indexDimsum := ops.indexDimsum
  ensureIndexable := ops.ensureIndexable
  axes := axesSubArrayModel
  strides := fun view =>
    stridesSubArray view ops.strides (substridesDispatch ops.indexStep ops.indexTypeName)
  fillToLength := ops.fillToLength
  firstLinearIndex := firstLinearIndex
  axisFirst := fun axis => axis.first
  axisLength := ops.axisLength
  indexFirst := ops.indexFirst
  indexStep := ops.indexStep
  indexTypeName := ops.indexTypeName
  axes1First := ops.axes1First
  isVector := fun view => decide (view.dimensions.length = 1)

def maybeReindexConfigured {P T : Type} (ops : ParentArrayOps P)
    (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index))
    (view : SubArray P T) (indices : List Index) : Jl (ReindexedView P T) :=
  maybeReindex view indices fun view indices scan =>
    maybeReindexDispatch view indices getVector getMatrix getArray toIndices
      (constructSubArrayConfigured ops)
      (constructSubArrayConfigured (parentArrayOpsSubArray ops firstLinearIndex)) scan

def unsafeViewSubArrayConfigured {P T : Type} (ops : ParentArrayOps P)
    (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index))
    (view : SubArray P T) (indices : List Index) : Jl (ReindexedView P T) :=
  unsafeViewSubArray view indices
    (maybeReindexConfigured ops firstLinearIndex getVector getMatrix getArray toIndices)

/-- Bounds and parent-array operations supplied by other Base files. -/
structure ViewBounds (P T : Type) where
  cartesian : SubArray P T → List I64 → Jl Unit
  linear : SubArray P T → I64 → Jl Unit

structure ViewReadOps (P T R : Type) extends ViewBounds P T where
  getVector : Index → Index → Jl Index
  getMatrix : Index → Index → Index → Jl Index
  getArray : Index → List Index → Jl Index
  getParentCartesian : P → List Index → Jl R
  getParentLinear : P → I64 → Jl R

/-- Trusted method dispatch for scalar-coordinate reads of a SubArray. -/
def getindexSubArrayConfigured {P T R : Type} (view : SubArray P T)
    (coordinates : List I64) (ops : ViewReadOps P T R) : Jl R :=
  if view.linear then
    match coordinates with
    | [index] =>
        if view.dimensions.length = 1 then
          getindexFastVectorSubArray view index ops.linear ops.getParentLinear
        else getindexFastSubArray view index ops.linear ops.getParentLinear
    | _ => getindexSubArray view coordinates ops.cartesian
        (reindexDispatch ops.getVector ops.getMatrix ops.getArray) ops.getParentCartesian
  else getindexSubArray view coordinates ops.cartesian
    (reindexDispatch ops.getVector ops.getMatrix ops.getArray) ops.getParentCartesian

/-- Dispatch normalizes integer and CartesianIndex arguments before selecting a SubArray method. -/
def getindexSubArrayArguments {P T R : Type} (view : SubArray P T) (indices : List Index)
    (normalizeCoordinates : List Index → Jl (List I64)) (ops : ViewReadOps P T R) : Jl R := do
  let coordinates ← normalizeCoordinates indices
  getindexSubArrayConfigured view coordinates ops

/-- Reads of a SubArray parent use the same source methods, rather than a replacement getter. -/
def viewParentReadOps {P T R : Type} (ops : ViewReadOps P T R)
    (bounds : ViewBounds (SubArray P T) T)
    (normalizeCoordinates : List Index → Jl (List I64)) : ViewReadOps (SubArray P T) T R where
  toViewBounds := bounds
  getVector := ops.getVector
  getMatrix := ops.getMatrix
  getArray := ops.getArray
  getParentCartesian := fun view indices => getindexSubArrayArguments view indices normalizeCoordinates ops
  getParentLinear := fun view index => getindexSubArrayConfigured view [index] ops

def readReindexedView {P T R : Type} (view : ReindexedView P T) (coordinates : List I64)
    (ops : ViewReadOps P T R) (bounds : ViewBounds (SubArray P T) T)
    (normalizeCoordinates : List Index → Jl (List I64)) : Jl R :=
  match view with
  | .flattened view => getindexSubArrayConfigured view coordinates ops
  | .nested view =>
      getindexSubArrayConfigured view coordinates (viewParentReadOps ops bounds normalizeCoordinates)

def reindexedViewAxes {P T : Type} : ReindexedView P T → List Axis
  | .flattened view => axesSubArrayModel view
  | .nested view => axesSubArrayModel view

end JuliaLean.base.subarray

/-!
## Models batch 1, group 17 additions

All earlier declarations are preserved verbatim. These additions close finite
pieces of the existing index representation without adding callee callbacks.
The declarations labelled partial have an explicit `Option` result: `none`
means that this proposal has no semantics for that input. It is not a Julia
exception, successful default, or coverage claim. See NOTES.md for the precise
method-level status and the unavailable compiler check.
-/

namespace JuliaLean.base.subarray.Models1Group17

open JuliaLean JuliaLean.base.int

-- Source: base/multidimensional.jl:792-799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline index_ndims(i1, I...) = (true, index_ndims(I...)...)
-- @inline function index_ndims(i1::CartesianIndex, I...)
--     (map(Returns(true), i1.I)..., index_ndims(I...)...)
-- end
-- @inline function index_ndims(i1::AbstractArray{CartesianIndex{N}}, I...) where N
--     (ntuple(Returns(true), Val(N))..., index_ndims(I...)...)
-- end
-- index_ndims() = ()
-- /Source
/-- Concrete `index_ndims` dependency for `rm_singleton_indices` at
base/subarray.jl:170. Mirrors base/multidimensional.jl:792-799.
The existing `.cartesian` and `.cartesianValues` tags here mean concrete
CartesianIndex and arrays with concrete CartesianIndex element type.
The opaque `.other` tag selects the generic non-Real, non-Cartesian dispatch.
Tuple arity and type-level Cartesian rank are represented by list structure/Nat;
no arithmetic on Julia Int values is replaced by Nat arithmetic. -/
def indexNdims : List Index → List Bool
  | [] => []
  | .cartesian coordinates :: rest =>
      coordinates.map (fun _ => true) ++ indexNdims rest
  | .cartesianValues _ rank _ :: rest =>
      List.replicate rank true ++ indexNdims rest
  | _ :: rest => true :: indexNdims rest

-- Source: base/multidimensional.jl:528-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))
--     # exit either when we've exhausted the input or reference tuple
--     _split1(::Tuple{}, ::Tuple{}) = ()
--     _split1(::Tuple{}, ref) = ()
--     _split1(t, ::Tuple{}) = ()
--     _splitrest(::Tuple{}, ::Tuple{}) = ()
--     _splitrest(t, ::Tuple{}) = t
--     _splitrest(::Tuple{}, ref) = ()
-- /Source
/-- Saturating tuple-tail dependency `IteratorsMD._splitrest`,
base/multidimensional.jl:528,533-535, needed at base/subarray.jl:170.
Only tuple structure is consumed; tuple elements are never inspected. -/
def splitRest {A B : Type} : List A → List B → List A
  | input, [] => input
  | [], _ :: _ => []
  | _ :: input, _ :: reference => splitRest input reference

-- Source: base/subarray.jl:133-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- # We can avoid the repetition from `AbstractArray{CartesianIndex{0}}`
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- # Transform indices to be "dense"
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- /Source
/-- Explicit result type for usable partial translations of
base/subarray.jl:133-159 and later layout helpers.
`none` is unmodelled semantics; `some (.error e)` is a modelled Julia exception.
This distinction prevents unsupported dispatch from becoming a fake Julia error. -/
abbrev Partial (A : Type) := Option (Jl A)

-- Source: base/subarray.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape() = ()
-- /Source
/-- Internal result injection used by the partial models, including the empty
tuple at base/subarray.jl:139. It is not a Julia method or runtime boundary. -/
def partialPure {A : Type} (value : A) : Partial A := some (.ok value)

-- Source: base/subarray.jl:133-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- /Source
/-- Sequential composition for partial models of base/subarray.jl:133-139.
Unknown semantics remains unknown; a known Julia exception short-circuits
before evaluating the continuation. No correctness law is supplied as input. -/
def partialBind {A B : Type} (value : Partial A) (next : A → Partial B) : Partial B :=
  match value with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok result) => next result

-- Source: base/subarray.jl:133-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- /Source
/-- Result mapping for the tuple constructors at base/subarray.jl:133-139.
This is ordinary structural composition, not a modelled callee oracle. -/
def partialMap {A B : Type} (f : A → B) (value : Partial A) : Partial B :=
  partialBind value (fun result => partialPure (f result))

-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
-- Source: base/boot.jl:1220-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Integer(x::Integer) = x
-- /Source
/-- Int64 UnitRange-length arithmetic from base/range.jl:794-804,
used for the represented built-in range cases at base/subarray.jl:135.
The axis endpoints must be those of a constructor-normalized range; raw
arbitrary endpoint pairs are not asserted to be Julia UnitRange values.
This follows the selected AbstractUnitRange method, not the separate bigints
OrdinalRange length method used for StepRange. The source's zero subtraction
and oneunit have Int64 type, so the Signed arm always applies and does not
evaluate the alternative stop>=start condition. The final Integer conversion
is same-type. The bundled range proof dispatch also selects this method for
Int64 UnitRange (Proofs/base/range.lean:764-777); no module is imported from it. -/
def unitLength (axis : Axis) : Jl I64 := do
  let start := axis.first
  let stop := axis.last
  let _zeroDifference := isub (int64 0) (int64 0)
  let a := int64 1
  let a := iadd a (isub stop start)
  return a

-- Source: base/subarray.jl:119-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- /Source
/-- Mathematical cardinality used only in a representation invariant for the
arrays used at base/subarray.jl:119-131,136-138. This is not Julia arithmetic
and is never used to replace a source machine-integer computation. -/
def shapeCardinality : List Axis → Nat
  | [] => 1
  | axis :: rest => (axis.last.val - axis.first.val + 1).toNat * shapeCardinality rest

-- Source: base/subarray.jl:119-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- /Source
/-- A represented actual array axis has a nonnegative, machine-sized number of
positions. Needed by the partial array branches at base/subarray.jl:136-138.
This is a type/representation invariant, not a premise about any model result. -/
def AxisValid (axis : Axis) : Prop :=
  0 ≤ axis.last.val - axis.first.val + 1 ∧
    axis.last.val - axis.first.val + 1 ≤ IntTy.i64.max

-- Source: base/subarray.jl:119-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- /Source
/-- Actual array payloads at base/subarray.jl:119-131,136-138 have consistent
axes and item count, a machine-sized rank, and a machine-sized length.
This prevents unrestricted Lean lists from silently becoming Julia arrays. -/
def ArrayPayloadValid (axes : List Axis) (count : Nat) : Prop :=
  Int.ofNat axes.length ≤ IntTy.i64.max ∧
  (∀ axis ∈ axes, AxisValid axis) ∧
  shapeCardinality axes = count ∧ Int.ofNat count ≤ IntTy.i64.max

-- Source: base/subarray.jl:119-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- # Get the proper trimmed shape
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- # We can avoid the repetition from `AbstractArray{CartesianIndex{0}}`
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- # Transform indices to be "dense"
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- /Source
/-- Representation-domain predicate for the partial helpers at
base/subarray.jl:133-159. It checks actual stored array shapes, Cartesian rank,
and logical-index storage length; it supplies no callee correctness law.
Range/scalar branches are separately documented as concrete Int64 encodings. -/
def IndexPayloadValid : Index → Prop
  | .values axes items => ArrayPayloadValid axes items.length
  | .cartesianValues axes rank items =>
      ArrayPayloadValid axes items.length ∧ Int.ofNat rank ≤ IntTy.i64.max ∧
        ∀ item ∈ items, item.length = rank
  | .mask bits => Int.ofNat bits.length ≤ IntTy.i64.max
  | .cartesian coordinates => Int.ofNat coordinates.length ≤ IntTy.i64.max
  | _ => True

-- Source: base/range.jl:425-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UnitRange{T<:Real} <: AbstractUnitRange{T}
--     start::T
--     stop::T
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- end
-- UnitRange{T}(start, stop) where {T<:Real} = UnitRange{T}(convert(T, start), convert(T, stop))
-- UnitRange(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- function UnitRange(start, stop)
--     startstop_promoted = promote(start, stop)
--     not_sametype((start, stop), startstop_promoted)
--     UnitRange(startstop_promoted...)
-- end
-- 
-- # if stop and start are integral, we know that their difference is a multiple of 1
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source
/-- Constructor invariant for an Int64 UnitRange used by the partial helpers
at base/subarray.jl:134-159. This describes endpoints, not any model's output.
The full Int64 endpoint span is admitted, including wrapped zero/negative
lengths. The empty-stop subtraction is Julia's wrapping subtraction. -/
def NormalizedUnitAxis (axis : Axis) : Prop :=
  axis.first.val ≤ axis.last.val ∨ axis.last = isub axis.first (int64 1)

-- Source: base/range.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- /Source
-- Source: base/indices.jl:337-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Slice{T<:AbstractUnitRange} <: AbstractUnitRange{Int}
--     indices::T
-- end
-- Slice(S::Slice) = S
-- Slice{T}(S::Slice) where {T<:AbstractUnitRange} = Slice{T}(T(S.indices))
-- 
-- axes(S::Slice) = (axes1(S),)
-- axes1(S::Slice) = IdentityUnitRange(S.indices)
-- axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices
-- 
-- first(S::Slice) = first(S.indices)
-- last(S::Slice) = last(S.indices)
-- /Source
-- Source: base/indices.jl:363-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct IdentityUnitRange{T<:AbstractUnitRange} <: AbstractUnitRange{Int}
--     indices::T
-- end
-- IdentityUnitRange(S::IdentityUnitRange) = S
-- IdentityUnitRange{T}(S::IdentityUnitRange) where {T<:AbstractUnitRange} = IdentityUnitRange{T}(T(S.indices))
-- 
-- # IdentityUnitRanges are offset and thus have offset axes, so they are their own axes
-- axes(S::IdentityUnitRange) = (axes1(S),)
-- axes1(S::IdentityUnitRange) = S
-- axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices
-- 
-- first(S::IdentityUnitRange) = first(S.indices)
-- last(S::IdentityUnitRange) = last(S.indices)
-- /Source
/-- Domain of the endpoint-erased Slice/IdentityUnitRange tags used at
base/subarray.jl:134,525-543: a direct wrapper of a normalized UnitRange{Int64},
or a direct wrapper of unchecked_oneto(Int64). The latter admits every stored
stop, including negative ones. Nested/custom underlying range types are not
claimed by this concrete encoding. -/
def WrappedUnitAxis (axis : Axis) : Prop :=
  NormalizedUnitAxis axis ∨ axis.first = int64 1

-- Source: base/range.jl:339-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRange{T,S} <: OrdinalRange{T,S}
--     start::T
--     step::S
--     stop::T
-- 
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- end
-- 
-- # to make StepRange constructor inlineable, so optimizer can see `step` value
-- function steprange_last(start, step, stop)::typeof(stop)
--     if isa(start, AbstractFloat) || isa(step, AbstractFloat)
--         throw(ArgumentError("StepRange should not be used with floating point"))
--     end
--     if isa(start, Integer) && !isinteger(start + step)
--         throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
--     end
--     z = zero(step)
--     step == z && throw(ArgumentError("step cannot be zero"))
-- 
--     if stop == start
--         last = stop
--     else
--         if (step > z) != (stop > start)
--             last = steprange_last_empty(start, step, stop)
--         else
--             # Compute absolute value of difference between `start` and `stop`
--             # (to simplify handling both signed and unsigned T and checking for signed overflow):
--             absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
--                                                 (_range_wrapping_sub(start, stop), -step)
-- 
--             # Compute remainder as a non-negative number:
--             if absdiff isa Signed && absdiff < zero(absdiff)
--                 # unlikely, but handle the signed overflow case with unsigned rem
--                 overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
--                 remain = overflow_case(absdiff, absstep)
--             else
--                 remain = convert(typeof(absdiff), absdiff % absstep)
--             end
--             # Move `stop` closer to `start` if there is a remainder:
--             last = stop > start ? stop - remain : stop + remain
--         end
--     end
--     return last
-- end
-- 
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
-- Source: base/range.jl:810-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
--     # slightly more accurate length and checked_length in extreme cases
--     # (near typemax) for types with known `unsigned` functions
--     function length(r::OrdinalRange{T}) where T<:bigints
--         s = step(r)
--         diff = last(r) -% first(r)
--         isempty(r) && return zero(diff)
--         # Compute `(diff ÷ s) + 1` in a manner robust to signed overflow
--         # by using the absolute values as unsigneds for non-empty ranges.
--         # Note that `s` may be a different type from T and diff; it may not
--         # even be a BitInteger that supports `unsigned`. Handle with care.
--         a = div(unsigned(flipsign(diff, s)), s) % typeof(diff)
--         return flipsign(a, s) + oneunit(a)
--     end
-- /Source
/-- Independent constructibility invariant for the old count-erased-stop
StepRange tag used at base/subarray.jl:135,525-543. A nonempty mathematical
sequence has representable endpoints and its stored Int64 length is its
cardinality modulo 2^64. An empty sequence requires a representable empty
endpoint in the direction opposite the step. No nonoverflow premise is imposed.
All Int/Nat arithmetic here is specification arithmetic, never a model body. -/
def StoredStepRangeValid (first step count : I64) : Prop :=
  step.val ≠ 0 ∧
    ((count.val = 0 ∧
      ((0 < step.val ∧ IntTy.i64.min < first.val) ∨
        (step.val < 0 ∧ first.val < IntTy.i64.max))) ∨
      ∃ cardinality : Nat,
        0 < cardinality ∧ Int.ofNat cardinality ≤ (2 : Int) ^ 64 ∧
        count = int64 (Int.ofNat cardinality) ∧
        IntTy.i64.min ≤ first.val + (Int.ofNat cardinality - 1) * step.val ∧
        first.val + (Int.ofNat cardinality - 1) * step.val ≤ IntTy.i64.max)

-- Source: base/range.jl:527-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRangeLen{T,R,S,L<:Integer} <: AbstractRange{T}
--     ref::R       # reference value (might be smallest-magnitude value in the range)
--     step::S      # step value
--     len::L       # length of the range
--     offset::L    # the index of ref
-- 
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- end
-- /Source
/-- Constructibility of the concrete Int64 ref/step/length, offset=1 encoding
of the old StepRangeLen tag used at base/subarray.jl:525-543. Its first field is
the Int64 ref, so it also equals first(r). This predicate is enough for shape
metadata; it does not supply erased floating or twice-precision element
semantics. Source constructor count must be nonnegative. -/
def StoredStepRangeLenValid (_first _step count : I64) : Prop :=
  0 ≤ count.val

-- Source: base/range.jl:591-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct LinRange{T,L<:Integer} <: AbstractRange{T}
--     start::T
--     stop::T
--     len::L
--     lendiv::L
-- 
--     function LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}
--         len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
--         onelen = oneunit(typeof(len))
--         if len == onelen
--             start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ"))
--             return new(start, stop, len, len)
--         end
--         lendiv = max(len - onelen, onelen)
--         if T <: Integer && !iszero(mod(stop-start, lendiv))
--             throw(ArgumentError("LinRange{<:Integer} cannot have non-integer step"))
--         end
--         return new(start, stop, len, lendiv)
--     end
-- /Source
/-- Int64 element/length LinRange constructor invariant needed at
base/subarray.jl:134,525-543. The divisibility test uses the source's wrapped
endpoint subtraction. The remaining Int arithmetic only describes the
positive stored lendiv. Count one requires equal endpoints; count zero is
admitted without requiring equal endpoints. -/
def StoredLinRangeValid (first last count : I64) : Prop :=
  0 ≤ count.val ∧
    (if count.val = 1 then first = last
      else (isub last first).val % max (count.val - 1) 1 = 0)

-- Source: base/range.jl:339-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRange{T,S} <: OrdinalRange{T,S}
--     start::T
--     step::S
--     stop::T
-- 
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- end
-- 
-- # to make StepRange constructor inlineable, so optimizer can see `step` value
-- function steprange_last(start, step, stop)::typeof(stop)
--     if isa(start, AbstractFloat) || isa(step, AbstractFloat)
--         throw(ArgumentError("StepRange should not be used with floating point"))
--     end
--     if isa(start, Integer) && !isinteger(start + step)
--         throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
--     end
--     z = zero(step)
--     step == z && throw(ArgumentError("step cannot be zero"))
-- 
--     if stop == start
--         last = stop
--     else
--         if (step > z) != (stop > start)
--             last = steprange_last_empty(start, step, stop)
--         else
--             # Compute absolute value of difference between `start` and `stop`
--             # (to simplify handling both signed and unsigned T and checking for signed overflow):
--             absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
--                                                 (_range_wrapping_sub(start, stop), -step)
-- 
--             # Compute remainder as a non-negative number:
--             if absdiff isa Signed && absdiff < zero(absdiff)
--                 # unlikely, but handle the signed overflow case with unsigned rem
--                 overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
--                 remain = overflow_case(absdiff, absstep)
--             else
--                 remain = convert(typeof(absdiff), absdiff % absstep)
--             end
--             # Move `stop` closer to `start` if there is a remainder:
--             last = stop > start ? stop - remain : stop + remain
--         end
--     end
--     return last
-- end
-- 
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
-- Source: base/range.jl:425-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UnitRange{T<:Real} <: AbstractUnitRange{T}
--     start::T
--     stop::T
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- end
-- UnitRange{T}(start, stop) where {T<:Real} = UnitRange{T}(convert(T, start), convert(T, stop))
-- UnitRange(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- function UnitRange(start, stop)
--     startstop_promoted = promote(start, stop)
--     not_sametype((start, stop), startstop_promoted)
--     UnitRange(startstop_promoted...)
-- end
-- 
-- # if stop and start are integral, we know that their difference is a multiple of 1
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source
-- Source: base/range.jl:485-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct OneTo{T<:Integer} <: AbstractOneTo{T}
--     stop::T # invariant: stop >= zero(stop)
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- 
--     function OneTo{T}(r::AbstractRange) where {T<:Integer}
--         throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
--         throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         first(r) == 1 || throwstart(r)
--         step(r)  == 1 || throwstep(r)
--         T === Bool && throwbool(r)
--         return new(max(zero(T), last(r)))
--     end
-- 
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- end
-- OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
-- OneTo(r::AbstractRange{T}) where {T<:Integer} = OneTo{T}(r)
-- oneto(r) = OneTo(r)
-- /Source
-- Source: base/range.jl:527-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRangeLen{T,R,S,L<:Integer} <: AbstractRange{T}
--     ref::R       # reference value (might be smallest-magnitude value in the range)
--     step::S      # step value
--     len::L       # length of the range
--     offset::L    # the index of ref
-- 
--     function StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S,L}
--         if T <: Integer && !isinteger(ref + step)
--             throw(ArgumentError("StepRangeLen{<:Integer} cannot have non-integer step"))
--         end
--         len = convert(L, len)
--         len >= zero(len) || throw(ArgumentError("length cannot be negative, got $len"))
--         offset = convert(L, offset)
--         L1 = oneunit(typeof(len))
--         L1 <= offset <= max(L1, len) || throw(ArgumentError("StepRangeLen: offset must be in [1,$len], got $offset"))
--         return new(ref, step, len, offset)
--     end
-- end
-- /Source
-- Source: base/range.jl:591-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct LinRange{T,L<:Integer} <: AbstractRange{T}
--     start::T
--     stop::T
--     len::L
--     lendiv::L
-- 
--     function LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}
--         len >= 0 || throw(ArgumentError("range($start, stop=$stop, length=$len): negative length"))
--         onelen = oneunit(typeof(len))
--         if len == onelen
--             start == stop || throw(ArgumentError("range($start, stop=$stop, length=$len): endpoints differ"))
--             return new(start, stop, len, len)
--         end
--         lendiv = max(len - onelen, onelen)
--         if T <: Integer && !iszero(mod(stop-start, lendiv))
--             throw(ArgumentError("LinRange{<:Integer} cannot have non-integer step"))
--         end
--         return new(start, stop, len, lendiv)
--     end
-- /Source
/-- Actual built-in range representation conditions for the partial helpers
at base/subarray.jl:133-159,525-543. OneTo includes unchecked_oneto and therefore
has no sign restriction. The opaque ordinalRange tag is not made concrete by
this predicate; shape/axis models below return unknown for that tag. -/
def IndexRangeValid : Index → Prop
  | .unitRange axis => NormalizedUnitAxis axis
  | .slice axis | .identity axis => WrappedUnitAxis axis
  | .stepRange first step count => StoredStepRangeValid first step count
  | .stepRangeLen first step count => StoredStepRangeLenValid first step count
  | .linRange first last count => StoredLinRangeValid first last count
  | _ => True



-- Source: base/subarray.jl:119-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- # Get the proper trimmed shape
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- # We can avoid the repetition from `AbstractArray{CartesianIndex{0}}`
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- # Transform indices to be "dense"
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- /Source
/-- Constructible array-payload input to the partial tuple helpers at
base/subarray.jl:133-148. These proof fields encode representation invariants;
they are not additional source checks and do not assume the output. -/
structure Input where
  indices : List Index
  arityFits : Int.ofNat indices.length ≤ IntTy.i64.max
  payloadsValid : ∀ index ∈ indices, IndexPayloadValid index
  rangesValid : ∀ index ∈ indices, IndexRangeValid index

-- Source: base/range.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- /Source
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
-- Source: base/range.jl:810-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
-- /Source
/-- Partial-axis length dependency for base/subarray.jl:452-453,491-500.
An Axis is a constructor-normalized Int64 unit range or the endpoint-erased
form of unchecked_oneto. For first==1, the model takes the stored OneTo stop;
otherwise it executes the Int64 range-length specialization. Valid actual
array axes have the same result for either possible concrete type at first==1.
This helper is not a claim to implement arbitrary user-defined axis types. -/
def axisLength (axis : Axis) : Jl I64 :=
  if axis.first.val = 1 then .ok axis.last else unitLength axis

-- Source: base/subarray.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(V::SubArray) = (@inline; map(length, axes(V)))
-- /Source
-- Source: base/subarray.jl:525-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::SubArray) = (@inline; _indices_sub(S.indices...))
-- _indices_sub(::Real, I...) = (@inline; _indices_sub(I...))
-- _indices_sub() = ()
-- function _indices_sub(i1::AbstractArray, I...)
--     @inline
--     (axes(i1)..., _indices_sub(I...)...)
-- end
-- 
-- axes1(::SubArray{<:Any,0}) = OneTo(1)
-- axes1(S::SubArray) = (@inline; _axes1_sub(S.indices...))
-- _axes1_sub() = ()
-- _axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
-- _axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
-- function _axes1_sub(i1::AbstractArray, I...)
--     @inline
--     axes1(i1)
-- end
-- 
-- has_offset_axes(S::SubArray) = has_offset_axes(S.indices...)
-- /Source
/-- Domain-carrying input for the finite shape/axis partials at
base/subarray.jl:70,525-543. Array payload validity comes from Input; actual
range constructor conditions are explicit and independent of the results.
The .mask interpretation is the immutable construction snapshot documented by
logicalSnapshotLength. No Julia callee or callee-correctness premise is input. -/
structure ShapeAxesInput where
  data : Input

-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
-- Source: base/subarray.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(V::SubArray) = (@inline; map(length, axes(V)))
-- /Source
-- Source: base/subarray.jl:525-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::SubArray) = (@inline; _indices_sub(S.indices...))
-- _indices_sub(::Real, I...) = (@inline; _indices_sub(I...))
-- _indices_sub() = ()
-- function _indices_sub(i1::AbstractArray, I...)
--     @inline
--     (axes(i1)..., _indices_sub(I...)...)
-- end
-- 
-- axes1(::SubArray{<:Any,0}) = OneTo(1)
-- axes1(S::SubArray) = (@inline; _axes1_sub(S.indices...))
-- _axes1_sub() = ()
-- _axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
-- _axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
-- function _axes1_sub(i1::AbstractArray, I...)
--     @inline
--     axes1(i1)
-- end
-- 
-- has_offset_axes(S::SubArray) = has_offset_axes(S.indices...)
-- /Source
/-- A represented SubArray together with its actual index-domain metadata,
for the partial methods at base/subarray.jl:70,525-543. The equality relates
input fields, not a function result. No consistency between N and the number
of retained axes is imposed: source axes1 dispatches on N even for directly
constructed SubArray values. -/
structure ShapeAxesViewInput (P T : Type) where
  view : SubArray P T
  indices : ShapeAxesInput
  indicesMatch : view.indices = indices.data.indices
  rankFits : Int.ofNat view.dimensions.length ≤ IntTy.i64.max

-- Source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- /Source
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
/-- Finite tag check for concrete Array shape metadata used by
base/subarray.jl:525-543. Together with Input.ArrayPayloadValid this is exactly
one-based stored-size axes; arbitrary offset/custom array overrides are not
claimed. The check is a meta-level domain test, not an added Julia runtime
check. Nonstandard origins remain supported by Slice/IdentityUnitRange. -/
def concreteArrayAxes (axes : List Axis) : Bool :=
  axes.all (fun axis => decide (axis.first = int64 1))

-- Source: base/subarray.jl:526-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _indices_sub(::Real, I...) = (@inline; _indices_sub(I...))
-- _indices_sub() = ()
-- function _indices_sub(i1::AbstractArray, I...)
--     @inline
--     (axes(i1)..., _indices_sub(I...)...)
-- end
-- /Source
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
-- Source: base/range.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- /Source
-- Source: base/range.jl:705-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(r::AbstractRange) = error("length implementation missing") # catch mistakes
-- size(r::AbstractRange) = (@inline; (length(r),))
-- /Source
-- Source: base/indices.jl:343-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::Slice) = (axes1(S),)
-- axes1(S::Slice) = IdentityUnitRange(S.indices)
-- axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
-- Source: base/indices.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::IdentityUnitRange) = (axes1(S),)
-- axes1(S::IdentityUnitRange) = S
-- axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
-- Source: base/multidimensional.jl:834-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct LogicalIndex{T, A<:AbstractArray{Bool}} <: AbstractVector{T}
--     mask::A
--     sum::Int
--     LogicalIndex{T,A}(mask::A) where {T,A<:AbstractArray{Bool}} = new(mask, count(mask))
-- end
-- LogicalIndex(mask::AbstractVector{Bool}) = LogicalIndex{Int, typeof(mask)}(mask)
-- LogicalIndex(mask::AbstractArray{Bool, N}) where {N} = LogicalIndex{CartesianIndex{N}, typeof(mask)}(mask)
-- LogicalIndex{Int}(mask::AbstractArray) = LogicalIndex{Int, typeof(mask)}(mask)
-- size(L::LogicalIndex) = (L.sum,)
-- /Source
/-- Supported pure finite dispatch for _indices_sub at base/subarray.jl:526-531.
Range validity is provided separately by ShapeAxesInput. Opaque/custom ranges,
colon and Cartesian scalar tags are outside this method's supported domain.
Mask bits carry the construction-snapshot meaning of logicalSnapshotLength. -/
def finiteAxesTag : Index → Bool
  | .scalar _ | .slice _ | .identity _ | .unitRange _ | .oneTo _ |
    .stepRange _ _ _ | .stepRangeLen _ _ _ | .linRange _ _ _ | .mask _ => true
  | .values axes _ | .cartesianValues axes _ _ => concreteArrayAxes axes
  | _ => false

-- Source: base/subarray.jl:526-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _indices_sub(::Real, I...) = (@inline; _indices_sub(I...))
-- _indices_sub() = ()
-- function _indices_sub(i1::AbstractArray, I...)
--     @inline
--     (axes(i1)..., _indices_sub(I...)...)
-- end
-- /Source
/-- Finite pure partial _indices_sub at base/subarray.jl:526-531. Reuses the
existing closed dispatcher on its actual built-in domain. All admitted callees
are pure and total, so the support test introduces no reordered source effect
or swallowed Julia error. Unknown dispatch remains outer none. -/
def indicesSubFinite (input : ShapeAxesInput) : Partial (List Axis) :=
  if input.data.indices.all finiteAxesTag then
    partialPure (JuliaLean.base.subarray.indicesSubDispatch input.data.indices)
  else none

-- Source: base/subarray.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::SubArray) = (@inline; _indices_sub(S.indices...))
-- /Source
/-- Finite public axes(SubArray) partial at base/subarray.jl:525. The old
closed axesSubArrayModel is reused verbatim after checking the supported tag
domain. The generic method and custom axes overrides remain unmodelled. -/
def axesSubArrayFinite {P T : Type} (input : ShapeAxesViewInput P T) :
    Partial (List Axis) :=
  if input.view.indices.all finiteAxesTag then
    partialPure (JuliaLean.base.subarray.axesSubArrayModel input.view)
  else none

-- Source: base/tuple.jl:358-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(f, t::Tuple{})              = ()
-- map(f, t::Tuple{Any,})          = (@inline; (f(t[1]),))
-- map(f, t::Tuple{Any, Any})      = (@inline; (f(t[1]), f(t[2])))
-- map(f, t::Tuple{Any, Any, Any}) = (@inline; (f(t[1]), f(t[2]), f(t[3])))
-- map(f, t::Tuple)                = (@inline; (f(t[1]), map(f,tail(t))...))
-- /Source
-- Source: base/range.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- /Source
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
-- Source: base/range.jl:810-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
-- /Source
/-- Concrete left-to-right tuple map(length,axes) dependency for
base/subarray.jl:70. Reuses the group's closed normalized-unit/unchecked-OneTo
length helper. A Julia exception, if produced, is propagated before the tail;
no value is extracted from an error with a default. -/
def mapAxisLengths : List Axis → Jl (List I64)
  | [] => pure []
  | axis :: rest => do
      let head ← axisLength axis
      let tail ← mapAxisLengths rest
      return head :: tail

-- Source: base/subarray.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(V::SubArray) = (@inline; map(length, axes(V)))
-- /Source
/-- Finite public size(SubArray) partial at base/subarray.jl:70. First obtains
the closed represented axes, then maps the concrete length dependency in
source order. Unchecked OneTo axes retain negative/zero wrapped range lengths.
Generic custom array/range shape semantics remain outside this partial. -/
def sizeSubArrayFinite {P T : Type} (input : ShapeAxesViewInput P T) :
    Partial (List I64) :=
  partialBind (axesSubArrayFinite input) fun axes => some (mapAxisLengths axes)



-- Source: base/range.jl:711-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- isempty(r::StepRangeLen) = length(r) == 0
-- isempty(r::LinRange) = length(r) == 0
-- /Source
-- Source: base/range.jl:808-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(r::LinRange) = r.len
-- /Source
-- Source: base/indices.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::Slice) = first(S.indices)
-- last(S::Slice) = last(S.indices)
-- /Source
-- Source: base/indices.jl:374-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::IdentityUnitRange) = first(S.indices)
-- last(S::IdentityUnitRange) = last(S.indices)
-- /Source
/-- Closed isempty dependencies for the represented generic AbstractRange
branch at base/subarray.jl:134. Slice/Identity use endpoints, so a full-width
range with wrapped zero length is still nonempty. LinRange uses stored len.
Other tags are outside this helper's partial dispatch domain. -/
def trimmedRangeEmpty : Index → Partial Bool
  | .slice axis | .identity axis =>
      partialPure (decide (axis.first.val > axis.last.val))
  | .linRange _ _ count => partialPure (decide (count.val = 0))
  | _ => none

-- Source: base/range.jl:711-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- isempty(r::StepRangeLen) = length(r) == 0
-- isempty(r::LinRange) = length(r) == 0
-- /Source
-- Source: base/range.jl:870-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::LinRange) = r.start
-- /Source
-- Source: base/range.jl:879-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::LinRange) = r.stop
-- 
-- minimum(r::AbstractUnitRange) = isempty(r) ? throw(ArgumentError("range must be non-empty")) : first(r)
-- maximum(r::AbstractUnitRange) = isempty(r) ? throw(ArgumentError("range must be non-empty")) : last(r)
-- minimum(r::AbstractRange)  = isempty(r) ? throw(ArgumentError("range must be non-empty")) : min(first(r), last(r))
-- maximum(r::AbstractRange)  = isempty(r) ? throw(ArgumentError("range must be non-empty")) : max(first(r), last(r))
-- /Source
-- Source: base/indices.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::Slice) = first(S.indices)
-- last(S::Slice) = last(S.indices)
-- /Source
-- Source: base/indices.jl:374-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::IdentityUnitRange) = first(S.indices)
-- last(S::IdentityUnitRange) = last(S.indices)
-- /Source
-- Source: base/int.jl:591-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function max(x::S, y::T) where {S <: BitInteger, T <: BitInteger}
--     R = promote_type(S, T)
--     ifelse(x < y, y % R, x % R)
-- end
-- /Source
/-- Closed maximum dependencies used at base/subarray.jl:134. The source's
own isempty check and ArgumentError are retained even though the outer trim
branch only calls maximum after a successful nonempty test. Int64 max reuses
the existing closed BitInteger model, including same-type promotion. -/
def trimmedRangeMaximum : Index → Partial I64
  | index@(.slice axis) | index@(.identity axis) =>
      partialBind (trimmedRangeEmpty index) fun empty =>
        if empty then some (.error (.argumentError "range must be non-empty"))
        else partialPure axis.last
  | index@(.linRange first last _) =>
      partialBind (trimmedRangeEmpty index) fun empty =>
        if empty then some (.error (.argumentError "range must be non-empty"))
        else partialPure (JuliaLean.base.int.max_BitInteger first last)
  | _ => none

-- Source: base/subarray.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- /Source
/-- Concrete Int64 head evaluation for the generic AbstractRange method at
base/subarray.jl:134. Zero(eltype(i)) is Int64 zero. No maximum call is made for
an empty range; a negative nonempty maximum is retained. Dense UnitRange,
StepRange and OneTo tags deliberately remain outside this helper, because
source line 135 has the more-specific length dispatch. -/
def trimmedAbstractRangeHead (index : Index) : Partial I64 :=
  partialBind (trimmedRangeEmpty index) fun empty =>
    if empty then partialPure (int64 0) else trimmedRangeMaximum index

-- Source: base/multidimensional.jl:834-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct LogicalIndex{T, A<:AbstractArray{Bool}} <: AbstractVector{T}
--     mask::A
--     sum::Int
--     LogicalIndex{T,A}(mask::A) where {T,A<:AbstractArray{Bool}} = new(mask, count(mask))
-- end
-- LogicalIndex(mask::AbstractVector{Bool}) = LogicalIndex{Int, typeof(mask)}(mask)
-- LogicalIndex(mask::AbstractArray{Bool, N}) where {N} = LogicalIndex{CartesianIndex{N}, typeof(mask)}(mask)
-- LogicalIndex{Int}(mask::AbstractArray) = LogicalIndex{Int, typeof(mask)}(mask)
-- size(L::LogicalIndex) = (L.sum,)
-- /Source
-- Source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
-- Source: base/tuple.jl:688-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prod(x::Tuple{}) = 1
-- # This is consistent with the regular prod because there is no need for size promotion
-- # if all elements in the tuple are of system size.
-- # It is defined here separately in order to support bootstrap, because it's needed earlier
-- # than the general prod definition is available.
-- prod(x::Tuple{Int, Vararg{Int}}) = *(x...)
-- /Source
-- Source: base/operators.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::Number) = x
-- /Source
/-- Cached-length projection of the existing scalar LogicalIndex snapshot
encoding, usable in the row-136 branch of base/subarray.jl. Here bits are the
mask at LogicalIndex{Int}'s construction, not a live mutable mask. The cached
sum is encoded by the selected-position list's length, as in the old Index
axes/selection representation. This is a field decoding, not a translation of
count(mask), pointer loads, or later mutation. Input bounds make the field
machine-sized. Source length is prod((sum,)) and singleton multiplication
returns that cached Int field unchanged. -/
def logicalSnapshotLength (bits : List Bool) : I64 :=
  int64 (Int.ofNat (bits.filter id).length)



-- Source: base/subarray.jl:133-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- /Source
/-- Partial closed `_trimmedshape`, base/subarray.jl:133-139.
The supported branches are Int64 scalars, valid UnitRange/StepRange/OneTo,
direct Slice/Identity wrappers, Int64 LinRange, and concrete one-based
scalar/Cartesian Array metadata. Scalar LogicalIndex uses an explicitly frozen
construction snapshot. Generic range extrema and custom array methods remain
unsupported; no custom offset-array method is inferred from stored metadata.
Array lengths are stored-list lengths only for a valid, machine-sized array
representation. The model does not claim unrestricted Lean lists are arrays. -/
private def trimmedShapeCore : List Index → Partial (List I64)
  | [] => partialPure JuliaLean.base.subarray.trimmedShapeEmpty
  | .scalar _ :: rest =>
      partialMap (fun tail => int64 1 :: tail) (trimmedShapeCore rest)
  | .unitRange axis :: rest =>
      partialBind (some (unitLength axis)) fun length =>
        partialMap (fun tail => length :: tail) (trimmedShapeCore rest)
  | .oneTo length :: rest | .stepRange _ _ length :: rest =>
      partialMap (fun tail => length :: tail) (trimmedShapeCore rest)
  | index@(.slice _) :: rest | index@(.identity _) :: rest |
    index@(.linRange _ _ _) :: rest =>
      partialBind (trimmedAbstractRangeHead index) fun head =>
        partialMap (fun tail => head :: tail) (trimmedShapeCore rest)
  | .values axes items :: rest =>
      if concreteArrayAxes axes then
        let length := int64 (Int.ofNat items.length)
        partialMap (fun tail => length :: tail) (trimmedShapeCore rest)
      else none
  | .cartesianValues _ 0 _ :: rest => trimmedShapeCore rest
  | .cartesianValues axes (rank + 1) items :: rest =>
      if concreteArrayAxes axes then
        let length := int64 (Int.ofNat items.length)
        let padding := List.replicate rank (int64 1)
        partialMap (fun tail => length :: (padding ++ tail)) (trimmedShapeCore rest)
      else none
  | .mask bits :: rest =>
      partialMap (fun tail => logicalSnapshotLength bits :: tail) (trimmedShapeCore rest)
  | _ => none

-- Source: base/subarray.jl:133-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- /Source
/-- Domain-carrying partial `_trimmedshape`, base/subarray.jl:133-139.
Array lengths, ranks, and range constructors satisfy the explicit `Input`
representation invariants.
The private recursion above supplies the complete implemented method body. -/
def trimmedShape (input : Input) : Partial (List I64) :=
  trimmedShapeCore input.indices

-- Source: base/subarray.jl:141-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- /Source
/-- Partial closed `_trimmedpind`, base/subarray.jl:141-145.
The finite tags have concrete axes/ranks in the bundled model. Generic custom
array/range `axes` effects and unsupported colon/Cartesian scalar inputs are
not replaced by defaults. All represented axis offsets are retained where the
source retains a range. Existing empty leaf is reused. -/
private def trimmedParentIndicesCore : List Index → Partial (List Index)
  | [] => partialPure JuliaLean.base.subarray.trimmedParentEmpty
  | .cartesianValues _ 0 _ :: rest => trimmedParentIndicesCore rest
  | .unitRange _ :: rest | .stepRange _ _ _ :: rest | .oneTo _ :: rest =>
      partialMap (fun tail => .colon :: tail) (trimmedParentIndicesCore rest)
  | index@(.slice _) :: rest | index@(.identity _) :: rest |
    index@(.stepRangeLen _ _ _) :: rest | index@(.ordinalRange _ _ _) :: rest |
    index@(.linRange _ _ _) :: rest =>
      partialMap (fun tail => index :: tail) (trimmedParentIndicesCore rest)
  | .scalar _ :: rest => trimmedParentIndicesCore rest
  | .values axes _ :: rest | .cartesianValues axes (_ + 1) _ :: rest =>
      if concreteArrayAxes axes then
        let headIndices := axes.map (fun _ => Index.colon)
        partialMap (fun tail => headIndices ++ tail) (trimmedParentIndicesCore rest)
      else none
  | .mask _ :: rest =>
      partialMap (fun tail => .colon :: tail) (trimmedParentIndicesCore rest)
  | _ => none

-- Source: base/subarray.jl:141-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- /Source
/-- Domain-carrying partial `_trimmedpind`, base/subarray.jl:141-145.
No output is asserted for a tuple with unmodelled index semantics. -/
def trimmedParentIndices (input : Input) : Partial (List Index) :=
  trimmedParentIndicesCore input.indices

-- Source: base/subarray.jl:146-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- /Source
/-- Partial closed `_trimmedvind`, base/subarray.jl:146-148.
Concrete CartesianIndex{0} arrays contribute their actual axis origins.
Other supported concrete arrays contribute colons; custom offset-array axes
remain unknown rather than being inferred from a stored metadata field.
The `.mask` tag denotes the existing logical-index vector representation.
There are no mutable-storage or `axes` callbacks in this helper. -/
private def trimmedViewIndicesCore : List Index → Partial (List Index)
  | [] => partialPure JuliaLean.base.subarray.trimmedViewEmpty
  | .cartesianValues axes 0 _ :: rest =>
      if concreteArrayAxes axes then
        let headIndices := axes.map (fun axis => Index.scalar axis.first)
        partialMap (fun tail => headIndices ++ tail) (trimmedViewIndicesCore rest)
      else none
  | .scalar _ :: rest => trimmedViewIndicesCore rest
  | .values axes _ :: rest | .cartesianValues axes (_ + 1) _ :: rest =>
      if concreteArrayAxes axes then
        let headIndices := axes.map (fun _ => Index.colon)
        partialMap (fun tail => headIndices ++ tail) (trimmedViewIndicesCore rest)
      else none
  | .slice _ :: rest | .identity _ :: rest | .unitRange _ :: rest |
    .oneTo _ :: rest | .stepRange _ _ _ :: rest | .stepRangeLen _ _ _ :: rest |
    .linRange _ _ _ :: rest | .mask _ :: rest =>
      partialMap (fun tail => .colon :: tail) (trimmedViewIndicesCore rest)
  | _ => none

-- Source: base/subarray.jl:146-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- /Source
/-- Domain-carrying partial `_trimmedvind`, base/subarray.jl:146-148,
with explicit array payload and range-constructor invariants. -/
def trimmedViewIndices (input : Input) : Partial (List Index) :=
  trimmedViewIndicesCore input.indices

-- Source: base/subarray.jl:150-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- /Source
/-- Partial closed `_trimmedindex`, base/subarray.jl:150-159.
The Int64 scalar and built-in dense range cases preserve their represented
concrete type. AbstractRange identity uses the existing faithful method.
Array cases remain unsupported because `oftype`, allocation identity and
reshape/copy semantics are not supplied by this representation. -/
private def trimmedIndexCore : Index → Partial Index
  | .scalar _ => partialPure (.scalar (int64 1))
  | .unitRange axis =>
      partialBind (some (unitLength axis)) fun length =>
        let stop := if length.val < 0 then int64 0 else length
        partialPure (.unitRange ⟨int64 1, stop⟩)
  | .oneTo length =>
      let stop := if length.val < 0 then int64 0 else length
      partialPure (.oneTo stop)
  | .stepRange _ _ length =>
      let stop := if length.val < 0 then int64 0 else length
      partialPure (.stepRange (int64 1) (int64 1) stop)
  | index@(.slice _) | index@(.identity _) | index@(.stepRangeLen _ _ _) |
    index@(.ordinalRange _ _ _) | index@(.linRange _ _ _) =>
      partialPure (JuliaLean.base.subarray.trimmedIndexRange index)
  | _ => none

-- Source: base/subarray.jl:150-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- /Source
/-- Domain-carrying partial `_trimmedindex`, base/subarray.jl:150-159.
The range predicate is an actual constructor/representation condition, not a
callee-correctness assumption. Non-range scalar cases need no extra condition;
unsupported array cases retain outer none in the private core. -/
def trimmedIndex (index : Index) (_rangeValid : IndexRangeValid index) : Partial Index :=
  trimmedIndexCore index

-- Source: base/subarray.jl:170-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rm_singleton_indices(ndims::Tuple, J1, Js...) = (J1, rm_singleton_indices(IteratorsMD._splitrest(ndims, index_ndims(J1)), Js...)...)
-- rm_singleton_indices(::Tuple{}, ::ScalarIndex, Js...) = rm_singleton_indices((), Js...)
-- rm_singleton_indices(::Tuple) = ()
-- /Source
/-- Closed `rm_singleton_indices`, base/subarray.jl:170-172.
The more-specific empty-dimensions/scalar method is selected first. Every
other head is retained and consumes its effective number of parent dimensions.
There is deliberately no bounds check here: the caller checks bounds first.
Reuses the existing empty-input leaf instead of duplicating it. -/
def removeSingletonIndices : List Bool → List Index → List Index
  | _, [] => JuliaLean.base.subarray.removeSingletonIndicesEmpty
  | [], .scalar _ :: rest => removeSingletonIndices [] rest
  | dimensions, index :: rest =>
      index :: removeSingletonIndices
        (splitRest dimensions (indexNdims [index])) rest
termination_by structural dimensions indices => indices

-- Source: base/range.jl:425-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UnitRange{T<:Real} <: AbstractUnitRange{T}
--     start::T
--     stop::T
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- end
-- UnitRange{T}(start, stop) where {T<:Real} = UnitRange{T}(convert(T, start), convert(T, stop))
-- UnitRange(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- function UnitRange(start, stop)
--     startstop_promoted = promote(start, stop)
--     not_sametype((start, stop), startstop_promoted)
--     UnitRange(startstop_promoted...)
-- end
-- 
-- # if stop and start are integral, we know that their difference is a multiple of 1
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source
/-- Concrete UnitRange{Int64} input representation for the partial public
specialization of `view` at base/subarray.jl:230-233. Two machine endpoints
are enough to construct the range, including huge ranges whose length wraps;
no no-overflow bound is imposed. The proof field enforces Julia's empty-stop
normalization rather than assuming any function's result. -/
structure UnitRange64 where
  endpoints : Axis
  normalized : endpoints.first.val ≤ endpoints.last.val ∨
    endpoints.last = isub endpoints.first (int64 1)

-- Source: base/range.jl:425-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UnitRange{T<:Real} <: AbstractUnitRange{T}
--     start::T
--     stop::T
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- end
-- UnitRange{T}(start, stop) where {T<:Real} = UnitRange{T}(convert(T, start), convert(T, stop))
-- UnitRange(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- function UnitRange(start, stop)
--     startstop_promoted = promote(start, stop)
--     not_sametype((start, stop), startstop_promoted)
--     UnitRange(startstop_promoted...)
-- end
-- 
-- # if stop and start are integral, we know that their difference is a multiple of 1
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source
/-- Int64 UnitRange constructor dependency for base/subarray.jl:230-233 via
range.jl:1013-1026. `range(start, stop)` reaches this constructor through
range_start_stop and colon. The discarded difference determines oneunit's
Int64 type in the source; the normalized empty stop uses wrapping subtraction. -/
def unitRangeFromEndpoints (start stop : I64) : Axis :=
  let normalizedStop := if stop.val ≥ start.val then stop else
    let _difference := isub start stop
    isub start (int64 1)
  ⟨start, normalizedStop⟩

-- Source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- /Source
/-- Concrete OneTo{Int64} bounds test used by the range-view dependency of
base/subarray.jl:230-233. Preserves the unsigned intermediate and comparison,
including the case where the unchecked OneTo stop is a negative wrapped length. -/
def oneToContainsInt64 (stop index : I64) : Bool :=
  let shifted := isub index (int64 1)
  let unsignedIndex : JInt .u64 := JInt.rem .u64 shifted
  let unsignedStop : JInt .u64 := JInt.rem .u64 stop
  decide (unsignedIndex.val < unsignedStop.val)

-- Source: base/essentials.jl:389-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- 
-- /Source
-- Source: base/abstractarray.jl:690-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- /Source
-- Source: base/abstractarray.jl:756-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange) =
--     isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
-- /Source
/-- Concrete bounds-check dependency for UnitRange{Int64} selected by another
UnitRange{Int64}, needed by base/subarray.jl:230-233.
Parent axes1 is unchecked_oneto(length(parent)); source `|` and `&` evaluate
both endpoint tests even for an empty selector. No mathematical nonnegative-
length replacement is made for the machine-length bounds check. -/
def checkUnitRangeSelection (parent selector : Axis) : Jl Unit := do
  let parentLength ← unitLength parent
  let empty := decide (selector.first.val > selector.last.val)
  let firstOK := oneToContainsInt64 parentLength selector.first
  let lastOK := oneToContainsInt64 parentLength selector.last
  if empty || (firstOK && lastOK) then return ()
  else .error .boundsError

-- Source: base/range.jl:1002-1011 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _empty_stop(start, step)
--     if step > zero(step)
--         stop = start - oneunit(step)
--         stop < start && return stop
--     else
--         stop = start + oneunit(step)
--         stop > start && return stop
--     end
--     throw(OverflowError(LazyString("cannot represent an empty range starting at ", start)))
-- end
-- /Source
/-- Concrete Int64 `_empty_stop`, range.jl:1002-1011, needed by the assigned
range-view method at base/subarray.jl:230-233. The source deliberately checks
whether wrapping destroyed the needed strict inequality and raises
OverflowError at that point. -/
def emptyRangeStop (start step : I64) : Jl I64 := do
  if step.val > 0 then
    let stop := isub start (int64 1)
    if stop.val < start.val then return stop
  else
    let stop := iadd start (int64 1)
    if stop.val > start.val then return stop
  .error (.overflowError s!"cannot represent an empty range starting at {start.val}")

-- Source: base/range.jl:1013-1026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(r::AbstractUnitRange, s::AbstractUnitRange{T}) where {T<:Integer}
--     @inline
--     @boundscheck checkbounds(r, s)
-- 
--     if T === Bool
--         return range(first(s) ? first(r) : last(r), length = last(s))
--     else
--         f = first(r)
--         start = oftype(f, f + first(s) - firstindex(r))
--         len = length(s)
--         stop = oftype(f, isempty(s) ? _empty_stop(start, step(r)) : _range_wrapping_add(start, len - oneunit(len)))
--         return range(start, stop)
--     end
-- end
-- /Source
/-- Concrete Int64/Int64 UnitRange getindex dependency for
base/subarray.jl:230-233. The selector element type is Int64, so the source Bool
branch is inapplicable. All `oftype` conversions are same-type identities.
Bounds are checked before affine arithmetic; len is evaluated before the
empty-selector branch; output endpoints are normalized by the actual constructor.
The UInt64 bounds behavior of huge parent ranges is retained. -/
def getindexUnitRange64 (parent selector : Axis) : Jl Axis := do
  checkUnitRangeSelection parent selector
  let first := parent.first
  let start := isub (iadd first selector.first) (int64 1)
  let length ← unitLength selector
  let stop ← if selector.first.val > selector.last.val then
      emptyRangeStop start (int64 1)
    else pure (iadd start (isub length (int64 1)))
  return unitRangeFromEndpoints start stop

-- Source: base/subarray.jl:230-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function view(r1::AbstractUnitRange, r2::AbstractUnitRange{<:Integer})
--     @_propagate_inbounds_meta
--     getindex(r1, r2)
-- end
-- /Source
/-- Complete concrete UnitRange{Int64}/UnitRange{Int64} specialization of
`view`, base/subarray.jl:230-233, using a closed getindex callee.
The unrestricted AbstractUnitRange method remains blocked: Bool, other element
types, offset range types, and custom implementations are not covered by this
explicit input type. This is a usable partial result for that inventory row. -/
def viewUnitRange64 (parent selector : UnitRange64) : Jl Axis :=
  getindexUnitRange64 parent.endpoints selector.endpoints

-- Source: base/array.jl:3219-3226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds function getindex(v::AbstractRange, i::Integer)
--     if i isa Bool # Not via dispatch to avoid ambiguities
--         throw(ArgumentError("invalid index: $i of type Bool"))
--     else
--         _getindex(v, i)
--     end
-- end
-- 
-- /Source
-- Source: base/range.jl:957-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _in_unit_range(v::UnitRange, val, i::Integer) = i > 0 && val <= v.stop && val >= v.start
-- /Source
-- Source: base/range.jl:965-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const OverflowSafe = Union{Bool,Int8,Int16,Int32,Int64,Int128,
--                            UInt8,UInt16,UInt32,UInt64,UInt128}
-- 
-- function _getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}
--     val = v.start + (i - oneunit(i))
--     @boundscheck _in_unit_range(v, val, i) || throw_boundserror(v, i)
--     val % T
-- end
-- /Source
/-- Concrete scalar getindex observation for the range-view property of
base/subarray.jl:230-233. Mirrors the OverflowSafe UnitRange Int64 path in
range.jl:967-972, including value computation before its bounds check.
The integer index has Int64 type, so Bool-index dispatch does not apply. -/
def readUnitRange64 (range : Axis) (index : I64) : Jl I64 :=
  let value := iadd range.first (isub index (int64 1))
  if index.val > 0 ∧ value.val ≤ range.last.val ∧ value.val ≥ range.first.val then
    .ok (JInt.rem .i64 value)
  else .error .boundsError

/-!
The following fragment is intended inside the existing
`JuliaLean.base.subarray.Models1Group17` namespace, with the existing imports
and `open JuliaLean JuliaLean.base.int`. All declarations are UNCHECKED.
These are concrete callee dependencies for assigned view methods, not claims
that the full generic AbstractRange methods have been translated.
-/

-- Source: base/range.jl:339-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRange{T,S} <: OrdinalRange{T,S}
--     start::T
--     step::S
--     stop::T
-- 
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- end
-- /Source
/-- Concrete StepRange{Int64,Int64} field representation from
base/range.jl:339-350, needed by view dependencies at base/subarray.jl:234-241.
The stop is the actual normalized endpoint, not a cached length. This retains
the source inputs needed by overflow-aware length and endpoint arithmetic. -/
structure StepRangeFields where
  start : I64
  step : I64
  stop : I64
  deriving DecidableEq

-- Source: base/range.jl:339-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRange{T,S} <: OrdinalRange{T,S}
--     start::T
--     step::S
--     stop::T
-- 
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- end
-- 
-- # to make StepRange constructor inlineable, so optimizer can see `step` value
-- function steprange_last(start, step, stop)::typeof(stop)
--     if isa(start, AbstractFloat) || isa(step, AbstractFloat)
--         throw(ArgumentError("StepRange should not be used with floating point"))
--     end
--     if isa(start, Integer) && !isinteger(start + step)
--         throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
--     end
--     z = zero(step)
--     step == z && throw(ArgumentError("step cannot be zero"))
-- 
--     if stop == start
--         last = stop
--     else
--         if (step > z) != (stop > start)
--             last = steprange_last_empty(start, step, stop)
--         else
--             # Compute absolute value of difference between `start` and `stop`
--             # (to simplify handling both signed and unsigned T and checking for signed overflow):
--             absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
--                                                 (_range_wrapping_sub(start, stop), -step)
-- 
--             # Compute remainder as a non-negative number:
--             if absdiff isa Signed && absdiff < zero(absdiff)
--                 # unlikely, but handle the signed overflow case with unsigned rem
--                 overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
--                 remain = overflow_case(absdiff, absstep)
--             else
--                 remain = convert(typeof(absdiff), absdiff % absstep)
--             end
--             # Move `stop` closer to `start` if there is a remainder:
--             last = stop > start ? stop - remain : stop + remain
--         end
--     end
--     return last
-- end
-- 
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
/-- Structural/mathematical input invariant for StepRange{Int64,Int64},
base/range.jl:339-398. A nonempty range has an oriented endpoint displacement
that is a nonnegative multiple of the step magnitude. An empty range has the
source's canonical neighboring stop. This is not a correctness hypothesis
about any new model function. Mathematical Int arithmetic occurs only in
this representation predicate; no length or no-overflow bound is imposed. -/
def NormalizedStepRange (range : StepRangeFields) : Prop :=
  range.step.val ≠ 0 ∧
  ((0 < range.step.val ∧
      ((range.start.val ≤ range.stop.val ∧
          (range.stop.val - range.start.val) % range.step.val = 0) ∨
        range.stop.val = range.start.val - 1)) ∨
    (range.step.val < 0 ∧
      ((range.stop.val ≤ range.start.val ∧
          (range.start.val - range.stop.val) % (-range.step.val) = 0) ∨
        range.stop.val = range.start.val + 1)))

-- Source: base/range.jl:339-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct StepRange{T,S} <: OrdinalRange{T,S}
--     start::T
--     step::S
--     stop::T
-- 
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- end
-- 
-- # to make StepRange constructor inlineable, so optimizer can see `step` value
-- function steprange_last(start, step, stop)::typeof(stop)
--     if isa(start, AbstractFloat) || isa(step, AbstractFloat)
--         throw(ArgumentError("StepRange should not be used with floating point"))
--     end
--     if isa(start, Integer) && !isinteger(start + step)
--         throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
--     end
--     z = zero(step)
--     step == z && throw(ArgumentError("step cannot be zero"))
-- 
--     if stop == start
--         last = stop
--     else
--         if (step > z) != (stop > start)
--             last = steprange_last_empty(start, step, stop)
--         else
--             # Compute absolute value of difference between `start` and `stop`
--             # (to simplify handling both signed and unsigned T and checking for signed overflow):
--             absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
--                                                 (_range_wrapping_sub(start, stop), -step)
-- 
--             # Compute remainder as a non-negative number:
--             if absdiff isa Signed && absdiff < zero(absdiff)
--                 # unlikely, but handle the signed overflow case with unsigned rem
--                 overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
--                 remain = overflow_case(absdiff, absstep)
--             else
--                 remain = convert(typeof(absdiff), absdiff % absstep)
--             end
--             # Move `stop` closer to `start` if there is a remainder:
--             last = stop > start ? stop - remain : stop + remain
--         end
--     end
--     return last
-- end
-- 
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
/-- Constructible concrete input domain for the StepRange selector/parent at
base/subarray.jl:234-241. Large ranges whose Int64 length wraps are retained.
The normal-form proof is independent of `stepRangeLast` and its output. -/
abbrev StepRange64 := {range : StepRangeFields // NormalizedStepRange range}

-- Source: base/range.jl:389-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function steprange_last_empty(start::Integer, step, stop)::typeof(stop)
--     # empty range has a special representation where stop = start-1,
--     # which simplifies arithmetic for Signed numbers
--     if step > zero(step)
--         last = _range_wrapping_sub(start, oneunit(step))
--     else
--         last = _range_wrapping_add(start, oneunit(step))
--     end
--     return last
-- end
-- /Source
/-- Int64 specialization of steprange_last_empty, base/range.jl:389-398,
needed by the constructor reached from base/subarray.jl:234-241.
The result has the same Int64 type as stop. The Bool and generic non-Integer
source methods are inapplicable. Addition/subtraction use existing wrapping
machine operations, including at machine endpoints. -/
def stepRangeLastEmpty (start step _stop : I64) : I64 :=
  if step.val > 0 then isub start (int64 1)
  else iadd start (int64 1)

-- Source: base/range.jl:353-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function steprange_last(start, step, stop)::typeof(stop)
--     if isa(start, AbstractFloat) || isa(step, AbstractFloat)
--         throw(ArgumentError("StepRange should not be used with floating point"))
--     end
--     if isa(start, Integer) && !isinteger(start + step)
--         throw(ArgumentError("StepRange{<:Integer} cannot have non-integer step"))
--     end
--     z = zero(step)
--     step == z && throw(ArgumentError("step cannot be zero"))
-- 
--     if stop == start
--         last = stop
--     else
--         if (step > z) != (stop > start)
--             last = steprange_last_empty(start, step, stop)
--         else
--             # Compute absolute value of difference between `start` and `stop`
--             # (to simplify handling both signed and unsigned T and checking for signed overflow):
--             absdiff, absstep = stop > start ? (_range_wrapping_sub(stop, start), step) :
--                                                 (_range_wrapping_sub(start, stop), -step)
-- 
--             # Compute remainder as a non-negative number:
--             if absdiff isa Signed && absdiff < zero(absdiff)
--                 # unlikely, but handle the signed overflow case with unsigned rem
--                 overflow_case(absdiff, absstep) = (@noinline; convert(typeof(absdiff), unsigned(absdiff) % absstep))
--                 remain = overflow_case(absdiff, absstep)
--             else
--                 remain = convert(typeof(absdiff), absdiff % absstep)
--             end
--             # Move `stop` closer to `start` if there is a remainder:
--             last = stop > start ? stop - remain : stop + remain
--         end
--     end
--     return last
-- end
-- /Source
/-- Closed Int64 steprange_last specialization, base/range.jl:353-387,
for the constructor needed by base/subarray.jl:234-241.
The Float and non-integer-step rejection branches are statically inapplicable
for Int64 arguments; the source's start+step computation is still represented.
The zero-step check precedes endpoint equality. Signed-overflow remainder uses
the existing mixed UInt64/Int64 rem wrapper with closed primitive arguments,
followed by a checked Int64 conversion rather than a wrapping cast.
No output invariant or callee-correctness law is assumed. -/
def stepRangeLast (start step stop : I64) : Jl I64 := do
  let _integerStepCheck := iadd start step
  let zero := int64 0
  if step.val = zero.val then
    throw (JlError.argumentError "step cannot be zero")
  if stop.val = start.val then
    return stop
  let stepPositive := decide (step.val > zero.val)
  let stopAboveStart := decide (stop.val > start.val)
  if stepPositive != stopAboveStart then
    return stepRangeLastEmpty start step stop
  let (absdiff, absstep) :=
    if stop.val > start.val then (isub stop start, step)
    else (isub start stop, JuliaLean.base.int.neg step)
  let remain ←
    if absdiff.val < 0 then do
      let unsignedDiff : JInt .u64 := JInt.rem .u64 absdiff
      let unsignedRemainder ← JuliaLean.base.int.Generic.rem_Unsigned_BitSigned
        (fun (value : I64) => flipsign_int value value)
        (fun (value : I64) => JInt.rem .u64 value)
        (fun (left right : JInt .u64) => JInt.remInt left right)
        unsignedDiff absstep
      JuliaLean.base.int.convert .i64 unsignedRemainder
    else do
      let signedRemainder ← JInt.remInt absdiff absstep
      JuliaLean.base.int.convert .i64 signedRemainder
  return if stop.val > start.val then isub stop remain else iadd stop remain

-- Source: base/range.jl:344-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function StepRange{T,S}(start, step, stop) where {T,S}
--         start = convert(T, start)
--         step = convert(S, step)
--         stop = convert(T, stop)
--         return new(start, step, steprange_last(start, step, stop))
--     end
-- /Source
/-- Closed StepRange{Int64,Int64} constructor at base/range.jl:344-349,
needed by base/subarray.jl:234-241. Same-type checked conversions execute in
source order, followed by endpoint normalization. The output is raw fields:
no theorem or supplied assertion is used to manufacture a normalization proof. -/
def stepRangeFromEndpoints (start step stop : I64) : Jl StepRangeFields := do
  let start ← JuliaLean.base.int.convert .i64 start
  let step ← JuliaLean.base.int.convert .i64 step
  let stop ← JuliaLean.base.int.convert .i64 stop
  let last ← stepRangeLast start step stop
  return ⟨start, step, last⟩

-- Source: base/range.jl:708-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::StepRange) =
--     # steprange_last(r.start, r.step, r.stop) == r.stop
--     (r.start != r.stop) & ((r.step > zero(r.step)) != (r.stop > r.start))
-- /Source
/-- Concrete isempty(::StepRange), base/range.jl:708-710, needed for
base/subarray.jl:234-241. Both source bitwise-and operands are formed before
combining them; no array elements or length operation is observed. -/
def stepRangeEmpty (range : StepRangeFields) : Bool :=
  let differentEndpoints := decide (range.start.val ≠ range.stop.val)
  let positiveStep := decide (range.step.val > 0)
  let increasingEndpoints := decide (range.stop.val > range.start.val)
  let directionMismatch := positiveStep != increasingEndpoints
  differentEndpoints && directionMismatch

-- Source: base/range.jl:810-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
--     # slightly more accurate length and checked_length in extreme cases
--     # (near typemax) for types with known `unsigned` functions
--     function length(r::OrdinalRange{T}) where T<:bigints
--         s = step(r)
--         diff = last(r) -% first(r)
--         isempty(r) && return zero(diff)
--         # Compute `(diff ÷ s) + 1` in a manner robust to signed overflow
--         # by using the absolute values as unsigneds for non-empty ranges.
--         # Note that `s` may be a different type from T and diff; it may not
--         # even be a BitInteger that supports `unsigned`. Handle with care.
--         a = div(unsigned(flipsign(diff, s)), s) % typeof(diff)
--         return flipsign(a, s) + oneunit(a)
--     end
-- /Source
/-- Closed Int64/Int64 OrdinalRange length specialization,
base/range.jl:820-830, needed by base/subarray.jl:234-241.
Preserves the source's wrapping endpoint difference, early empty return,
UInt64 intermediate, mixed signedness division, and wrapping final increment.
Typemin step and full-width endpoint spans are included. The Generic division
wrapper is fully instantiated with concrete compiled integer primitives.
The source's enclosing method-generation let context is included above. -/
def stepRangeLength (range : StepRangeFields) : Jl I64 := do
  let step := range.step
  let diff := isub range.stop range.start
  if stepRangeEmpty range then return int64 0
  let unsignedDiff : JInt .u64 := JInt.rem .u64 (flipsign_int diff step)
  let quotient ← JuliaLean.base.int.Generic.div_Unsigned_BitSigned
    (fun (value : I64) => flipsign_int value value)
    (fun (value : I64) => JInt.rem .u64 value)
    (fun (left right : JInt .u64) => JInt.div left right)
    (fun (value : JInt .u64) => JInt.rem .i64 value)
    (fun (left right : I64) => flipsign_int left right)
    (fun (value : I64) => JInt.rem .u64 value)
    unsignedDiff step
  let a := JInt.rem .i64 quotient
  return iadd (flipsign_int a step) (int64 1)


-- Source: base/abstractarray.jl:753-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Colon) = true
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Slice) = true
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange) =
--     isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
-- /Source
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
/-- Concrete range-bounds dependency for the assigned method at
base/subarray.jl:234-237. Both endpoint tests are evaluated after the selector
emptiness test, matching source `|`/`&`; the parent stop is a wrapped length. -/
def checkStepSelectionIntoUnit (parent : Axis) (selector : StepRangeFields) : Jl Unit := do
  let length ← unitLength parent
  let empty := stepRangeEmpty selector
  let firstOK := oneToContainsInt64 length selector.start
  let lastOK := oneToContainsInt64 length selector.stop
  if empty || (firstOK && lastOK) then return ()
  else .error .boundsError

-- Source: base/range.jl:1034-1049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(r::AbstractUnitRange, s::StepRange{T}) where {T<:Integer}
--     @inline
--     @boundscheck checkbounds(r, s)
-- 
--     if T === Bool
--         len = Int(last(s))
--         return range(first(s) ? first(r) : last(r), step=oneunit(eltype(r)), length=len)
--     else
--         f = first(r)
--         start = oftype(f, f + s.start - firstindex(r))
--         st = step(s)
--         len = length(s)
--         stop = oftype(f, isempty(s) ? _empty_stop(start, st) : start + (len - oneunit(len)) * st)
--         return range(start, stop; step=st)
--     end
-- end
-- /Source
/-- Closed UnitRange{Int64}/StepRange{Int64,Int64} selection dependency for
base/subarray.jl:234-237. The source Bool branch is excluded by the concrete
selector element type. The output step constructor still runs and may throw;
it is never replaced by a first/step/count record with unchecked normalization. -/
def getindexUnitRangeStep64 (parent : Axis) (selector : StepRangeFields) : Jl StepRangeFields := do
  checkStepSelectionIntoUnit parent selector
  let first := parent.first
  let start := isub (iadd first selector.start) (int64 1)
  let step := selector.step
  let length ← stepRangeLength selector
  let stop ← if stepRangeEmpty selector then emptyRangeStop start step
    else pure (iadd start (imul (isub length (int64 1)) step))
  stepRangeFromEndpoints start step stop

-- Source: base/subarray.jl:234-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function view(r1::AbstractUnitRange, r2::StepRange{<:Integer})
--     @_propagate_inbounds_meta
--     getindex(r1, r2)
-- end
-- /Source
/-- Concrete Int64 UnitRange/StepRange specialization of `view`,
base/subarray.jl:234-237. This closes the actual getindex callee on the complete
normalized endpoint-based input types. The generic inventory method remains
blocked for other element types, Bool selectors, and custom range dispatch. -/
def viewUnitRangeStep64 (parent : UnitRange64) (selector : StepRange64) : Jl StepRangeFields :=
  getindexUnitRangeStep64 parent.endpoints selector.val

-- Source: base/range.jl:1051-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(r::StepRange, s::AbstractRange{T}) where {T<:Integer}
--     @inline
--     @boundscheck checkbounds(r, s)
-- 
--     if T === Bool
--         # treat as a zero, one, or two-element vector, where at most one element is true
--         # staying inbounds on the original range (preserving either start or
--         # stop as either stop or start, depending on the length)
--         st = step(s)
--         nonempty = st > zero(st) ? last(s) : first(s)
--         # n.b. isempty(r) implies isempty(r) which means !nonempty and !first(s)
--         range((first(s) ⊻ nonempty) ⊻ isempty(r) ? last(r) : first(r), step=step(r), length=Int(nonempty))
--     else
--         f = r.start
--         fs = first(s)
--         st = r.step
--         start = oftype(f, f + (fs - firstindex(r)) * st)
--         st *= step(s)
--         len = length(s)
--         stop = oftype(f, isempty(s) ? _empty_stop(start, st) : start + (len - oneunit(len)) * st)
--         return range(start, stop; step=st)
--     end
-- end
-- /Source
/-- Explicit supported selector types for the partial public method at
base/subarray.jl:238-241. This sum encodes concrete UnitRange and StepRange,
not arbitrary AbstractRange callbacks. Both variants carry normalized values. -/
inductive OrdinalSelector64 where
  | unit (range : UnitRange64)
  | step (range : StepRange64)

-- Source: base/range.jl:867-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- first(r::OneTo{T}) where {T} = oneunit(T)
-- first(r::StepRangeLen) = unsafe_getindex(r, 1)
-- first(r::LinRange) = r.start
-- /Source
/-- Concrete first(selector), needed at base/subarray.jl:238-241 through
range.jl:1065. Both supported element types are already Int64. -/
def selectorFirst : OrdinalSelector64 → I64
  | .unit range => range.endpoints.first
  | .step range => range.val.start

-- Source: base/range.jl:877-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- last(r::StepRangeLen) = unsafe_getindex(r, length(r))
-- last(r::LinRange) = r.stop
-- /Source
/-- Concrete last(selector) for the bounds dependency of
base/subarray.jl:238-241. No interpolation or custom method is assumed. -/
def selectorLast : OrdinalSelector64 → I64
  | .unit range => range.endpoints.last
  | .step range => range.val.stop

-- Source: base/range.jl:733-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ```
-- """
-- step(r::StepRange) = r.step
-- step(r::AbstractUnitRange{T}) where {T} = oneunit(T) - zero(T)
-- step(r::AbstractUnitRange{Bool}) = true
-- step(r::StepRangeLen) = r.step
-- step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
-- /Source
/-- Concrete step(selector), needed by base/subarray.jl:238-241 through
range.jl:1068. The UnitRange step has the represented Int64 type. -/
def selectorStep : OrdinalSelector64 → I64
  | .unit _ => int64 1
  | .step range => range.val.step

-- Source: base/range.jl:708-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::StepRange) =
--     # steprange_last(r.start, r.step, r.stop) == r.stop
--     (r.start != r.stop) & ((r.step > zero(r.step)) != (r.stop > r.start))
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- isempty(r::StepRangeLen) = length(r) == 0
-- isempty(r::LinRange) = length(r) == 0
-- /Source
/-- Concrete isempty(selector), needed by base/subarray.jl:238-241 through
range.jl:1070. Nonzero step and canonical empty endpoints belong to the input
representation; no count-equals-zero shortcut is used for StepRange. -/
def selectorEmpty : OrdinalSelector64 → Bool
  | .unit range => decide (range.endpoints.first.val > range.endpoints.last.val)
  | .step range => stepRangeEmpty range.val

-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
-- Source: base/range.jl:810-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
--     # slightly more accurate length and checked_length in extreme cases
--     # (near typemax) for types with known `unsigned` functions
--     function length(r::OrdinalRange{T}) where T<:bigints
--         s = step(r)
--         diff = last(r) -% first(r)
--         isempty(r) && return zero(diff)
--         # Compute `(diff ÷ s) + 1` in a manner robust to signed overflow
--         # by using the absolute values as unsigneds for non-empty ranges.
--         # Note that `s` may be a different type from T and diff; it may not
--         # even be a BitInteger that supports `unsigned`. Handle with care.
--         a = div(unsigned(flipsign(diff, s)), s) % typeof(diff)
--         return flipsign(a, s) + oneunit(a)
--     end
-- /Source
/-- Concrete length(selector), needed by base/subarray.jl:238-241 through
range.jl:1069. Both branches reuse the exact machine-integer length helpers. -/
def selectorLength : OrdinalSelector64 → Jl I64
  | .unit range => unitLength range.endpoints
  | .step range => stepRangeLength range.val

-- Source: base/abstractarray.jl:753-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Colon) = true
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, ::Slice) = true
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange) =
--     isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
-- /Source
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
/-- Concrete bounds dependency of base/subarray.jl:238-241.
The parent StepRange uses its actual wrapped length to form the OneTo bound;
this is different from the scalar StepRange widened-coordinate bounds rule. -/
def checkOrdinalSelectionIntoStep (parent : StepRangeFields) (selector : OrdinalSelector64) : Jl Unit := do
  let length ← stepRangeLength parent
  let empty := selectorEmpty selector
  let firstOK := oneToContainsInt64 length (selectorFirst selector)
  let lastOK := oneToContainsInt64 length (selectorLast selector)
  if empty || (firstOK && lastOK) then return ()
  else .error .boundsError

-- Source: base/range.jl:1051-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(r::StepRange, s::AbstractRange{T}) where {T<:Integer}
--     @inline
--     @boundscheck checkbounds(r, s)
-- 
--     if T === Bool
--         # treat as a zero, one, or two-element vector, where at most one element is true
--         # staying inbounds on the original range (preserving either start or
--         # stop as either stop or start, depending on the length)
--         st = step(s)
--         nonempty = st > zero(st) ? last(s) : first(s)
--         # n.b. isempty(r) implies isempty(r) which means !nonempty and !first(s)
--         range((first(s) ⊻ nonempty) ⊻ isempty(r) ? last(r) : first(r), step=step(r), length=Int(nonempty))
--     else
--         f = r.start
--         fs = first(s)
--         st = r.step
--         start = oftype(f, f + (fs - firstindex(r)) * st)
--         st *= step(s)
--         len = length(s)
--         stop = oftype(f, isempty(s) ? _empty_stop(start, st) : start + (len - oneunit(len)) * st)
--         return range(start, stop; step=st)
--     end
-- end
-- /Source
/-- Closed supported Int64 StepRange selection dependency for
base/subarray.jl:238-241. Start is computed with the old parent step; only then
is the step multiplied by the selector step. A wrapped zero output step reaches
the source StepRange constructor's ArgumentError. Empty selectors can throw
earlier in `_empty_stop`, preserving that exception order. -/
def getindexStepRangeOrdinal64 (parent : StepRangeFields) (selector : OrdinalSelector64) : Jl StepRangeFields := do
  checkOrdinalSelectionIntoStep parent selector
  let first := parent.start
  let selectedFirst := selectorFirst selector
  let step := parent.step
  let start := iadd first (imul (isub selectedFirst (int64 1)) step)
  let step := imul step (selectorStep selector)
  let length ← selectorLength selector
  let stop ← if selectorEmpty selector then emptyRangeStop start step
    else pure (iadd start (imul (isub length (int64 1)) step))
  stepRangeFromEndpoints start step stop

-- Source: base/subarray.jl:238-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function view(r1::StepRange, r2::AbstractRange{<:Integer})
--     @_propagate_inbounds_meta
--     getindex(r1, r2)
-- end
-- /Source
/-- Concrete endpoint-based Int64 StepRange view with a UnitRange/StepRange
selector, base/subarray.jl:238-241. No count reconstruction or callback getter is
used. The full generic row remains blocked for the other AbstractRange types,
Bool selectors, numeric promotions, and custom source method implementations. -/
def viewStepRangeOrdinal64 (parent : StepRange64) (selector : OrdinalSelector64) : Jl StepRangeFields :=
  getindexStepRangeOrdinal64 parent.val selector

-- Source: base/range.jl:974-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let BitInteger64 = Union{Int8,Int16,Int32,Int64,UInt8,UInt16,UInt32,UInt64} # for bootstrapping
--     global function checkbounds(::Type{Bool}, v::StepRange{<:BitInteger64, <:BitInteger64}, i::BitInteger64)
--         res = widemul(step(v), i-oneunit(i)) + first(v)
--         (0 < i) & ifelse(0 < step(v), res <= last(v), res >= last(v))
--     end
-- end
-- 
-- /Source
-- Source: base/number.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widemul(x::Number, y::Number) = widen(x)*widen(y)
-- /Source
/-- Closed Int64 StepRange scalar bounds for the independent observations of
base/subarray.jl:234-241. Int64 index-minus-one occurs before widening; the
product and addition then have Int128 type. Both eager ifelse comparison
arguments are computed before selecting the result. -/
def stepBoundsInt64 (start step stop index : I64) : Bool :=
  let delta := isub index (int64 1)
  let product := JuliaLean.base.int.mul
    (JuliaLean.base.int.widenTo .i128 step)
    (JuliaLean.base.int.widenTo .i128 delta)
  let result := JuliaLean.base.int.add product
    (JuliaLean.base.int.widenTo .i128 start)
  let positiveIndex := JuliaLean.base.int.lt_BitSigned (int64 0) index
  let positiveStep := JuliaLean.base.int.lt_BitSigned (int64 0) step
  let upper := JuliaLean.base.int.lePromote result stop
  let lower := JuliaLean.base.int.lePromote stop result
  positiveIndex && (if positiveStep then upper else lower)

-- Source: base/range.jl:733-744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ```
-- """
-- step(r::StepRange) = r.step
-- step(r::AbstractUnitRange{T}) where {T} = oneunit(T) - zero(T)
-- step(r::AbstractUnitRange{Bool}) = true
-- step(r::StepRangeLen) = r.step
-- step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
-- step(r::LinRange) = (last(r)-first(r))/r.lendiv
-- 
-- # high-precision step
-- step_hp(r::StepRangeLen) = r.step
-- step_hp(r::AbstractRange) = step(r)
-- /Source
-- Source: base/range.jl:985-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_getindex(v::AbstractRange{T}, i::Integer) where T = convert(T, first(v) + (i - oneunit(i))*step_hp(v))
-- /Source
/-- Closed StepRange Int64 unsafe scalar read for the view observations at
base/subarray.jl:234-241. The source read uses Int64 multiply/add, separately
from the widened bounds calculation, then performs its final same-type
conversion. The concrete step_hp dispatch reads the stored StepRange step. -/
def stepUnsafeScalarInt64 (start step index : I64) : Jl I64 := do
  let first := start
  let delta := isub index (int64 1)
  let product := imul delta step
  let value := iadd first product
  JuliaLean.base.int.convert .i64 value

-- Source: base/array.jl:3219-3226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds function getindex(v::AbstractRange, i::Integer)
--     if i isa Bool # Not via dispatch to avoid ambiguities
--         throw(ArgumentError("invalid index: $i of type Bool"))
--     else
--         _getindex(v, i)
--     end
-- end
-- 
-- /Source
-- Source: base/range.jl:952-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _getindex(v::AbstractRange, i::Integer)
--     @boundscheck checkbounds(v, i)
--     unsafe_getindex(v, i)
-- end
-- /Source
/-- Checked concrete StepRange scalar observation for
base/subarray.jl:234-241. BoundsError occurs before the unsafe read. The public
getindex Bool arm is inapplicable to the explicit Int64 index type. -/
def readStepRange64 (range : StepRangeFields) (index : I64) : Jl I64 :=
  if stepBoundsInt64 range.start range.step range.stop index then
    stepUnsafeScalarInt64 range.start range.step index
  else .error .boundsError

-- Source: base/array.jl:3219-3226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds function getindex(v::AbstractRange, i::Integer)
--     if i isa Bool # Not via dispatch to avoid ambiguities
--         throw(ArgumentError("invalid index: $i of type Bool"))
--     else
--         _getindex(v, i)
--     end
-- end
-- 
-- /Source
/-- Concrete getindex dispatch on the two supported selector types for the
independent view observations at base/subarray.jl:230-241. Both arms call
closed scalar models, rather than accepting an observation/correctness oracle. -/
def readSelector64 (selector : OrdinalSelector64) (index : I64) : Jl I64 :=
  match selector with
  | .unit range => readUnitRange64 range.endpoints index
  | .step range => readStepRange64 range.val index

-- Source: base/range.jl:923-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copy(r::AbstractRange) = r
-- /Source
/-- Closed built-in immutable-range copy dependency for
base/subarray.jl:252-255. This is the exact existing copy(AbstractRange) body;
the separate base.range module containing that leaf is absent from the supplied
prebuilt closure. It is instantiated only at the concrete range sum below. -/
def copyBuiltinRange (range : OrdinalSelector64) : OrdinalSelector64 := range

-- Source: base/range.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(r::AbstractRange, ::Colon) = copy(r)
-- /Source
/-- Closed Colon getindex dependency of base/subarray.jl:252-255 for the
explicit built-in UnitRange/StepRange representation. Custom range overrides
are not routed through this helper. -/
def getindexOrdinalColon64 (range : OrdinalSelector64) : Jl OrdinalSelector64 :=
  .ok (copyBuiltinRange range)

-- Source: base/subarray.jl:252-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function view(r1::AbstractRange, c::Colon)
--     @_propagate_inbounds_meta
--     getindex(r1, c)
-- end
-- /Source
/-- Concrete built-in ordinal-range Colon view, base/subarray.jl:252-255.
Reuses the existing view wrapper with a closed source getindex implementation.
The generic AbstractRange row remains blocked for custom dispatch and other
unrepresented range types; no custom copy behavior is assumed. -/
def viewOrdinalColon64 (range : OrdinalSelector64) : Jl OrdinalSelector64 :=
  JuliaLean.base.subarray.viewAbstractRangeColon range Index.colon
    (fun range _ => getindexOrdinalColon64 range)



/-!
Standalone fragment for insertion inside
`JuliaLean.base.subarray.Models1Group17`, after the concrete range-read
dependencies. UNCHECKED: no Lean compiler was available for this fragment.

These are partial models of ordinary checked execution. The Julia methods
propagate a caller's inbounds context; no BoundsError claim below is made for
an invalid access after that check has been elided. `none` means that source
semantics is not provided, rather than a Julia return value or exception.
-/

-- Source: base/subarray.jl:292-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reindex(::Tuple{}, ::Tuple{}) = ()
-- 
-- # Skip dropped scalars, so simply peel them off the parent indices and continue
-- reindex(idxs::Tuple{ScalarIndex, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1], reindex(tail(idxs), subidxs)...))
-- 
-- # Slices simply pass their subindices straight through
-- reindex(idxs::Tuple{Slice, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (subidxs[1], reindex(tail(idxs), tail(subidxs))...))
-- 
-- # Re-index into parent vectors with one subindex
-- reindex(idxs::Tuple{AbstractVector, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1]], reindex(tail(idxs), tail(subidxs))...))
-- 
-- # Parent matrices are re-indexed with two sub-indices
-- reindex(idxs::Tuple{AbstractMatrix, Vararg{Any}}, subidxs::Tuple{Any, Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1], subidxs[2]], reindex(tail(idxs), tail(tail(subidxs)))...))
-- 
-- # In general, we index N-dimensional parent arrays with N indices
-- reindex(idxs::Tuple{AbstractArray{<:Any,N}, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) where {N} =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1:N]...], reindex(tail(idxs), subidxs[N+1:end])...))
-- /Source
/-- Partial closed `reindex` dispatch, base/subarray.jl:292-312, in an ordinary
checked context. Scalars do not consume a subindex; Slice passes one through
without inspecting its value or invoking its getter. These two branches work
for every represented subindex tag. A normalized built-in UnitRange{Int64}
with an Int64 scalar subindex uses the already closed scalar read before
recursing. The normalization test is a model-domain check returning none for
unrepresented inputs, not an extra Julia runtime check.

The empty/extra-subindex and known nonarray-parent cases raise MethodError.
A Slice or vector with no subindex reaches the generic array fallback, whose
typed tuple comprehension first needs unavailable temporary-array allocation;
that whole-call path therefore remains outer none. Other array reads,
arbitrary custom dispatch, and the
baseline count-only StepRange tag remain unsupported. In particular no last endpoint is inferred
from a possibly wrapped count. Use reindexOrdinalHead64 for an explicit
normalized StepRange head. Constructible complete tuple inputs are provided
by the reindexPartial wrapper below. -/
def reindexPartialCore : List Index → List Index → Partial (List Index)
  | [], [] => some JuliaLean.base.subarray.reindexEmpty
  | [], _ :: _ => some (.error (.methodError "reindex"))
  | .scalar value :: rest, subindices =>
      partialMap (fun indices => Index.scalar value :: indices)
        (reindexPartialCore rest subindices)
  | .slice _ :: rest, subindex :: subindices =>
      partialMap (fun indices => subindex :: indices)
        (reindexPartialCore rest subindices)
  | .unitRange axis :: rest, .scalar position :: subindices =>
      if axis.first.val ≤ axis.last.val ∨
          axis.last = isub axis.first (int64 1) then
        partialBind (some (readUnitRange64 axis position)) fun value =>
          partialMap (fun indices => Index.scalar value :: indices)
            (reindexPartialCore rest subindices)
      else none
  | .colon :: _, _ => some (.error (.methodError "reindex"))
  | .cartesian _ :: _, _ => some (.error (.methodError "reindex"))
  | _ :: _, _ => none
termination_by structural parents subindices => parents

-- Source: base/subarray.jl:292-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reindex(::Tuple{}, ::Tuple{}) = ()
-- 
-- # Skip dropped scalars, so simply peel them off the parent indices and continue
-- reindex(idxs::Tuple{ScalarIndex, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1], reindex(tail(idxs), subidxs)...))
-- 
-- # Slices simply pass their subindices straight through
-- reindex(idxs::Tuple{Slice, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (subidxs[1], reindex(tail(idxs), tail(subidxs))...))
-- 
-- # Re-index into parent vectors with one subindex
-- reindex(idxs::Tuple{AbstractVector, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1]], reindex(tail(idxs), tail(subidxs))...))
-- 
-- # Parent matrices are re-indexed with two sub-indices
-- reindex(idxs::Tuple{AbstractMatrix, Vararg{Any}}, subidxs::Tuple{Any, Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1], subidxs[2]], reindex(tail(idxs), tail(tail(subidxs)))...))
-- 
-- # In general, we index N-dimensional parent arrays with N indices
-- reindex(idxs::Tuple{AbstractArray{<:Any,N}, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) where {N} =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1:N]...], reindex(tail(idxs), subidxs[N+1:end])...))
-- /Source
/-- Constructible-input interface to the partial checked reindex model at
base/subarray.jl:292-312. Existing Input fields bound tuple arity, array rank,
and stored array payload lengths, and ensure shape/payload consistency.
Generic method rows remain blocked: this interface does not convert partial
coverage of the concrete Int64 and Slice branches into generic translation. -/
def reindexPartial (parents subindices : Input) : Partial (List Index) :=
  reindexPartialCore parents.indices subindices.indices

-- Source: base/subarray.jl:303-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reindex(idxs::Tuple{AbstractVector, Vararg{Any}}, subidxs::Tuple{Any, Vararg{Any}}) =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1]], reindex(tail(idxs), tail(subidxs))...))
-- /Source
-- Source: base/subarray.jl:311-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reindex(idxs::Tuple{AbstractArray{<:Any,N}, Vararg{Any}}, subidxs::Tuple{Vararg{Any}}) where {N} =
--     (@_propagate_inbounds_meta; (idxs[1][subidxs[1:N]...], reindex(tail(idxs), subidxs[N+1:end])...))
-- /Source
/-- Concrete UnitRange{Int64} or StepRange{Int64,Int64} vector-head
specialization of base/subarray.jl:303-304. Reuses the existing normalized
endpoint representations and closed scalar observers. The extra proof field
bounds the complete parent tuple, including its separately supplied head;
it is only a representation invariant. The scalar getter runs
before recursion, preserving its error precedence over any later parent.
A missing subindex selects the N=1 generic fallback at :311-312 and reaches
unavailable temporary-array allocation before any checked tuple field read;
it therefore remains unknown. Nonscalar indexing is explicitly unsupported.
Remaining parents use the structural partial dispatcher above;
no new index representation or getter callback is introduced. -/
def reindexOrdinalHead64 (range : OrdinalSelector64)
    (rest subindices : Input)
    (_parentArityFits : Int.ofNat rest.indices.length + 1 ≤ IntTy.i64.max) :
    Partial (List Index) :=
  match subindices.indices with
  | [] => none
  | .scalar position :: tail =>
      partialBind (some (readSelector64 range position)) fun value =>
        partialMap (fun indices => Index.scalar value :: indices)
          (reindexPartialCore rest.indices tail)
  | _ :: _ => none



-- Source: base/range.jl:733-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ```
-- """
-- step(r::StepRange) = r.step
-- step(r::AbstractUnitRange{T}) where {T} = oneunit(T) - zero(T)
-- step(r::AbstractUnitRange{Bool}) = true
-- step(r::StepRangeLen) = r.step
-- step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)
-- /Source
/-- Partial concrete `Int(step(index))` dependency for base/subarray.jl:442,454.
The returned step already has the Int64 type represented by these tags, so the
source Int conversion is an identity conversion. LinRange's possibly inexact
floating quotient and opaque custom OrdinalRange steps remain unsupported. -/
def rangeStepInt : Index → Partial I64
  | .slice _ | .unitRange _ | .oneTo _ | .identity _ => partialPure (int64 1)
  | .stepRange _ step _ | .stepRangeLen _ step _ => partialPure step
  | _ => none

-- Source: base/subarray.jl:439-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- substrides(strds::Tuple{}, ::Tuple{}) = ()
-- substrides(strds::NTuple{N,Int}, I::Tuple{ScalarIndex, Vararg{Any}}) where N = (substrides(tail(strds), tail(I))...,)
-- substrides(strds::NTuple{N,Int}, I::Tuple{Slice, Vararg{Any}}) where N = (first(strds), substrides(tail(strds), tail(I))...)
-- substrides(strds::NTuple{N,Int}, I::Tuple{AbstractRange, Vararg{Any}}) where N = (first(strds)*Int(step(I[1])), substrides(tail(strds), tail(I))...)
-- substrides(strds, I::Tuple{Any, Vararg{Any}}) = throw(ArgumentError(
--     LazyString("strides is invalid for SubArrays with indices of type ", typeof(I[1]))))
-- /Source
/-- Partial closed `substrides`, base/subarray.jl:439-444.
Source evaluation order is preserved: first stride, Int(step), multiplication,
then tail recursion. Known invalid index tags raise the source ArgumentError;
its LazyString type-name rendering is intentionally abstracted because no
property in this proposal observes message text. A range with an unimplemented
step instead returns meta-level `none`, never that fallback Julia error. -/
def substrides : List I64 → List Index → Partial (List I64)
  | [], [] => some JuliaLean.base.subarray.substridesEmpty
  | _ :: _, [] => some (.error (.methodError "substrides"))
  | strides, .scalar _ :: rest =>
      partialBind (some (tupleTail strides)) fun tail => substrides tail rest
  | strides, .slice _ :: rest =>
      partialBind (some (tupleFirst strides)) fun first =>
        partialBind (some (tupleTail strides)) fun tail =>
          partialMap (fun tailStrides => first :: tailStrides) (substrides tail rest)
  | strides, index :: rest =>
      if index.isRange then
        partialBind (some (tupleFirst strides)) fun first =>
          partialBind (rangeStepInt index) fun step =>
            let headStride := imul first step
            partialBind (some (tupleTail strides)) fun tail =>
              partialMap (fun tailStrides => headStride :: tailStrides)
                (substrides tail rest)
      else some (.error (.argumentError "strides is invalid for SubArrays with these index types"))
termination_by structural strides indices => indices

-- Source: base/subarray.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compute_stride1(s, inds, I::Tuple{}) = s
-- compute_stride1(s, inds, I::Tuple{Vararg{ScalarIndex}}) = s
-- compute_stride1(s, inds, I::Tuple{ScalarIndex, Vararg{Any}}) =
--     (@inline; compute_stride1(s*Int(length(inds[1])), tail(inds), tail(I)))
-- compute_stride1(s, inds, I::Tuple{AbstractRange, Vararg{Any}}) = s * Int(step(I[1]))
-- compute_stride1(s, inds, I::Tuple{Slice, Vararg{Any}}) = s
-- compute_stride1(s, inds, I::Tuple{Any, Vararg{Any}}) = throw(ArgumentError(LazyString("invalid strided index type ", typeof(I[1]))))
-- /Source
/-- Partial closed recursive `compute_stride1`, base/subarray.jl:450-456.
The all-scalar specialization is chosen before touching axes. A scalar with
a nonscalar tail indexes inds[1], computes its length, multiplies, then recurses.
The slice branch returns the stride without inspecting the remaining indices.
Unsupported range steps remain unknown; invalid nonrange tags give ArgumentError
at the source throw site, with diagnostic type-name text abstracted. -/
def computeStride1Rec : I64 → List Axis → List Index → Partial I64
  | stride, axes, [] => some (JuliaLean.base.subarray.computeStride1Empty stride axes)
  | stride, axes, .scalar value :: rest =>
      if Index.allScalar rest then
        some (JuliaLean.base.subarray.computeStride1Scalars stride axes (.scalar value :: rest))
      else
        match axes with
        | [] => some (.error .boundsError)
        | axis :: tail =>
            partialBind (some (axisLength axis)) fun length =>
              let nextStride := imul stride length
              computeStride1Rec nextStride tail rest
  | stride, axes, .slice axis :: rest =>
      some (JuliaLean.base.subarray.computeStride1Slice stride axes (.slice axis) rest)
  | stride, _, index :: _ =>
      if index.isRange then partialMap (fun step => imul stride step) (rangeStepInt index)
      else some (.error (.argumentError "invalid strided index type"))
termination_by structural stride axes indices => indices

-- Source: base/subarray.jl:347-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # or if all the indices are scalars, i.e. the view is for a single value only
-- FastContiguousSubArray{T,N,P,I<:Union{Tuple{AbstractUnitRange, Vararg{Any}},
--                                       Tuple{Vararg{ScalarIndex}}}} = SubArray{T,N,P,I,true}
-- 
-- /Source
-- Source: base/subarray.jl:460-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscontiguous(A::SubArray) = iscontiguous(typeof(A))
-- iscontiguous(::Type{<:SubArray}) = false
-- iscontiguous(::Type{<:FastContiguousSubArray}) = true
-- /Source
/-- Closed type dispatch for `iscontiguous(A::SubArray)`,
base/subarray.jl:460-462, using the FastContiguousSubArray alias at :348-349.
The source trait depends on the stored type tags and L flag, not actual stride,
offset, array elements, or numerical range values. Existing true/false type
leaves are reused. The baseline Index tags describe concrete tuple element
types; an opaque `.other` is not a disguised AbstractUnitRange or Real. -/
def iscontiguous {P T : Type} (view : SubArray P T) : Bool :=
  if view.linear then
    match view.indices with
    | [] => JuliaLean.base.subarray.iscontiguousFastContiguousSubArrayType
    | first :: _ =>
        if first.isUnitRange || Index.allScalar view.indices then
          JuliaLean.base.subarray.iscontiguousFastContiguousSubArrayType
        else JuliaLean.base.subarray.iscontiguousSubArrayType
  else JuliaLean.base.subarray.iscontiguousSubArrayType

-- Source: base/number.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(x::Number) = x
-- /Source
-- Source: base/range.jl:867-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- first(r::OneTo{T}) where {T} = oneunit(T)
-- first(r::StepRangeLen) = unsafe_getindex(r, 1)
-- first(r::LinRange) = r.start
-- /Source
-- Source: base/indices.jl:347-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::Slice) = first(S.indices)
-- /Source
-- Source: base/indices.jl:374-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(S::IdentityUnitRange) = first(S.indices)
-- /Source
/-- Partial concrete `Int(first(index))` for base/subarray.jl:471-472,491-500.
These concrete scalar/range payloads already have Int64 element type. The
StepRangeLen first-element path is deliberately unsupported: its true source
uses unsafe_getindex and ref/offset fields erased by the baseline Index tag.
Array first-element reads and opaque OrdinalRange conversions are also unknown. -/
def firstAsInt : Index → Partial I64
  | .scalar value => partialPure value
  | .slice axis | .identity axis | .unitRange axis => partialPure axis.first
  | .oneTo _ => partialPure (int64 1)
  | .stepRange first _ _ | .linRange first _ _ => partialPure first
  | _ => none

-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
-- Source: base/indices.jl:343-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::Slice) = (axes1(S),)
-- axes1(S::Slice) = IdentityUnitRange(S.indices)
-- axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
-- Source: base/indices.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::IdentityUnitRange) = (axes1(S),)
-- axes1(S::IdentityUnitRange) = S
-- axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
/-- Partial concrete first(axes1(range)) for base/subarray.jl:471-472.
Slice/Identity preserve the represented underlying origins. Ordinary concrete
range axes start at one. This does not inspect range elements or call a getter. -/
def firstAxisAsInt : Index → Partial I64
  | .slice axis | .identity axis => partialPure axis.first
  | .unitRange _ | .oneTo _ | .stepRange _ _ _ | .stepRangeLen _ _ _ |
    .linRange _ _ _ => partialPure (int64 1)
  | _ => none

-- Source: base/subarray.jl:471-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- compute_offset1(parent::AbstractVector, stride1::Integer, I::Tuple{AbstractRange}) =
--     (@inline; Int(first(I[1])) - stride1*Int(first(axes1(I[1]))))
-- /Source
/-- Partial closed vector/range `compute_offset1`, base/subarray.jl:471-472.
The source's parent parameter is unused. The Int64 stride input matches the
actual caller's prior Int conversion. Generic wider Integer strides, arbitrary
range first/axis conversions and StepRangeLen first-element computation remain
outside this partial declaration. -/
def computeOffset1VectorRange (index : Index) (stride : I64) : Partial I64 :=
  partialBind (firstAsInt index) fun first =>
    partialBind (firstAxisAsInt index) fun firstAxis =>
      partialPure (isub first (imul stride firstAxis))

-- Source: base/subarray.jl:491-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function compute_linindex(f, s, IP::Tuple, I::Tuple{Any, Any, Vararg{Any}})
--     @inline
--     Δi = Int(first(I[1])) - Int(first(IP[1]))
--     compute_linindex(f + Δi*s, s*Int(length(IP[1])), tail(IP), tail(I))
-- end
-- function compute_linindex(f, s, IP::Tuple, I::Tuple{Any})
--     @inline
--     Δi = Int(first(I[1])) - Int(first(IP[1]))
--     f + Δi*s
-- end
-- compute_linindex(f, s, IP::Tuple, I::Tuple{}) = f
-- /Source
/-- Partial closed `compute_linindex` recursion, base/subarray.jl:491-501.
Int(first(I[1])) is evaluated before indexing IP[1]. The non-final step then
computes the displacement, next f, and length-scaled next stride in source
order. The final step does not evaluate axis length or consume any more axes.
No unsupported first operation is turned into an error or arbitrary result. -/
def computeLinindexRec : I64 → I64 → List Axis → List Index → Partial I64
  | first, stride, axes, [] =>
      some (JuliaLean.base.subarray.computeLinindexEmpty first stride axes)
  | first, stride, axes, [index] =>
      partialBind (firstAsInt index) fun indexFirst =>
        match axes with
        | [] => some (.error .boundsError)
        | axis :: _ =>
            let displacement := isub indexFirst axis.first
            partialPure (iadd first (imul displacement stride))
  | first, stride, axes, index :: second :: rest =>
      partialBind (firstAsInt index) fun indexFirst =>
        match axes with
        | [] => some (.error .boundsError)
        | axis :: tail =>
            let displacement := isub indexFirst axis.first
            let nextFirst := iadd first (imul displacement stride)
            partialBind (some (axisLength axis)) fun length =>
              let nextStride := imul stride length
              computeLinindexRec nextFirst nextStride tail (second :: rest)
termination_by structural first stride axes indices => indices

-- Source: base/subarray.jl:535-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _axes1_sub() = ()
-- _axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
-- _axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
-- function _axes1_sub(i1::AbstractArray, I...)
--     @inline
--     axes1(i1)
-- end
-- /Source
/-- Meta-level supported-prefix check for _axes1_sub at base/subarray.jl:535-541.
The first positive-dimensional supported array ends inspection, as in the
source. A zero-dimensional Cartesian ELEMENT does not itself skip an array;
only an empty axes tuple does. Unknown tails after the answer are not read. -/
def axes1PrefixKnown : List Index → Bool
  | [] => true
  | .scalar _ :: rest | .values [] _ :: rest | .cartesianValues [] _ _ :: rest =>
      axes1PrefixKnown rest
  | index :: _ => finiteAxesTag index

-- Source: base/subarray.jl:535-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _axes1_sub() = ()
-- _axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
-- _axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
-- function _axes1_sub(i1::AbstractArray, I...)
--     @inline
--     axes1(i1)
-- end
-- /Source
/-- Finite _axes1_sub partial at base/subarray.jl:535-541, reusing the old
closed dispatcher. The inner none is the source empty tuple; outer none means
unmodelled semantics. This distinction preserves the actual empty leaf. -/
def axes1SubFinite (input : ShapeAxesInput) : Partial (Option Axis) :=
  if axes1PrefixKnown input.data.indices then
    partialPure (JuliaLean.base.subarray.axes1SubDispatch input.data.indices)
  else none

-- Source: base/subarray.jl:533-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes1(::SubArray{<:Any,0}) = OneTo(1)
-- axes1(S::SubArray) = (@inline; _axes1_sub(S.indices...))
-- _axes1_sub() = ()
-- _axes1_sub(::Real, I...) = (@inline; _axes1_sub(I...))
-- _axes1_sub(::AbstractArray{<:Any,0}, I...) = _axes1_sub(I...)
-- function _axes1_sub(i1::AbstractArray, I...)
--     @inline
--     axes1(i1)
-- end
-- /Source
/-- Finite public axes1(SubArray) partial at base/subarray.jl:533-541. N=0
returns OneTo(1) immediately without consulting even unsupported indices.
The general method reuses the old closed dispatcher only up to its first
answer. some(ok none) is the legitimate source empty tuple. -/
def axes1SubArrayFinite {P T : Type} (input : ShapeAxesViewInput P T) :
    Partial (Option Axis) :=
  if input.view.dimensions.length = 0 then
    partialPure (some JuliaLean.base.subarray.axes1ZeroDimSubArray)
  else if axes1PrefixKnown input.view.indices then
    partialPure (JuliaLean.base.subarray.axes1SubArrayModel input.view)
  else none

-- Source: base/abstractarray.jl:114-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes() = false
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- /Source
-- Source: base/abstractarray.jl:140-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes1(A::AbstractArray{<:Any,0}) = OneTo(1)
-- axes1(A::AbstractArray) = (@inline; axes(A)[1])
-- axes1(iter) = oneto(length(iter))
-- /Source
-- Source: base/abstractarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
-- /Source
-- Source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
-- /Source
-- Source: base/number.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(x::Number) = ()
-- /Source
-- Source: base/range.jl:747-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(::StepRange) = false
-- /Source
-- Source: base/indices.jl:343-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::Slice) = (axes1(S),)
-- axes1(S::Slice) = IdentityUnitRange(S.indices)
-- axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
-- Source: base/indices.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(S::IdentityUnitRange) = (axes1(S),)
-- axes1(S::IdentityUnitRange) = S
-- axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices
-- /Source
/-- Concrete single-argument has_offset_axes dependency for
base/subarray.jl:543. Concrete Array uses its false specialization. Ranges and
logical-index vectors have one-based axes except Slice/Identity, whose first
axis element is the stored origin even when empty. Conversion Int(Int64) is
identity. Custom array axes/firstindex overrides are left unknown. -/
def hasOffsetAxesFiniteIndex : Index → Partial Bool
  | .scalar _ | .colon | .unitRange _ | .oneTo _ | .stepRange _ _ _ |
    .stepRangeLen _ _ _ | .linRange _ _ _ | .mask _ => partialPure false
  | .slice axis | .identity axis => partialPure (decide (axis.first.val ≠ 1))
  | .values axes _ | .cartesianValues axes _ _ =>
      if concreteArrayAxes axes then partialPure false else none
  | _ => none

-- Source: base/abstractarray.jl:114-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes() = false
-- has_offset_axes(A) = _any_tuple(x->Int(first(x))::Int != 1, false, axes(A)...)
-- has_offset_axes(A::AbstractVector) = Int(firstindex(A))::Int != 1 # improve performance of a common case (ranges)
-- has_offset_axes(::Colon) = false
-- has_offset_axes(::Array) = false
-- # note: this could call `any` directly if the compiler can infer it. We don't use _any_tuple
-- # here because it stops full elision in some cases (#49332) and we don't need handling of
-- # `missing` (has_offset_axes(A) always returns a Bool)
-- has_offset_axes(A, As...) = has_offset_axes(A) || has_offset_axes(As...)
-- /Source
/-- Concrete variadic has_offset_axes dependency for base/subarray.jl:543.
Preserves short circuit: a known true head does not evaluate an unsupported
tail. Empty arguments use the source false leaf. -/
def hasOffsetAxesFiniteCore : List Index → Partial Bool
  | [] => partialPure false
  | index :: rest =>
      partialBind (hasOffsetAxesFiniteIndex index) fun offset =>
        if offset then partialPure true else hasOffsetAxesFiniteCore rest

-- Source: base/subarray.jl:543-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_offset_axes(S::SubArray) = has_offset_axes(S.indices...)
-- /Source
/-- Finite public has_offset_axes(SubArray) partial at base/subarray.jl:543.
It observes the stored index tuple and preserves variadic short circuit,
without adding an arbitrary user-defined axes or firstindex callback. -/
def hasOffsetAxesSubArrayFinite {P T : Type} (input : ShapeAxesViewInput P T) :
    Partial Bool :=
  hasOffsetAxesFiniteCore input.view.indices


end JuliaLean.base.subarray.Models1Group17


namespace JuliaLean.base.subarray.Models2Group14
open JuliaLean JuliaLean.base.subarray
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
inductive FieldInput (Expected Other : Type) where
  | typed (value : Expected)
  | needsConversion (value : Other)
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure View (Tag Parent Indices : Type) where
  typeTag : Tag
  parent : Parent
  indices : Indices
  offset1 : I64
  stride1 : I64
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
inductive NewField where
  | parent | indices | offset1 | stride1
  deriving DecidableEq, Repr
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
inductive Error (External : Type) where
  | julia (error : JlError)
  | isaTypeError (field : NewField)
  | newTargetTypeError
  | newTypeError (field : NewField)
  | external (error : External)
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure ConstructorTarget (Tag : Type) where
  typeTag : Tag
  parentFieldIsType : Bool
  indicesFieldIsType : Bool
  newEligible : Bool
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure InnerOps (m : Type → Type)
    (Parent Indices ParentInput IndicesInput OffsetInput StrideInput Check Bad : Type) where
  checkParentIndexMatch : FieldInput Parent ParentInput →
    FieldInput Indices IndicesInput → m Check
  convertParent : ParentInput → m (FieldInput Parent Bad)
  convertIndices : IndicesInput → m (FieldInput Indices Bad)
  convertOffset : OffsetInput → m (FieldInput I64 Bad)
  convertStride : StrideInput → m (FieldInput I64 Bad)
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def prepareField {m : Type → Type} [Monad m] {Expected Other Bad : Type}
    (convert : Other → m (FieldInput Expected Bad)) :
    FieldInput Expected Other → m (FieldInput Expected Bad)
  | .typed value => pure (.typed value)
  | .needsConversion value => convert value
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def inner {m : Type → Type} [Monad m] {External : Type}
    [MonadExceptOf (Error External) m]
    {Tag Parent Indices ParentInput IndicesInput OffsetInput StrideInput Check Bad : Type}
    (ops : InnerOps m Parent Indices ParentInput IndicesInput OffsetInput StrideInput Check Bad)
    (target : ConstructorTarget Tag) (parent : FieldInput Parent ParentInput)
    (indices : FieldInput Indices IndicesInput)
    (offset1 : FieldInput I64 OffsetInput) (stride1 : FieldInput I64 StrideInput) :
    m (View Tag Parent Indices) := do
  let _ ← ops.checkParentIndexMatch parent indices
  if !target.parentFieldIsType then throw (.isaTypeError .parent)
  let parent ← prepareField ops.convertParent parent
  if !target.indicesFieldIsType then throw (.isaTypeError .indices)
  let indices ← prepareField ops.convertIndices indices
  let offset1 ← prepareField ops.convertOffset offset1
  let stride1 ← prepareField ops.convertStride stride1
  if !target.newEligible then throw .newTargetTypeError
  match parent, indices, offset1, stride1 with
  | .typed p, .typed i, .typed o, .typed s => pure ⟨target.typeTag, p, i, o, s⟩
  | .needsConversion _, _, _, _ => throw (.newTypeError .parent)
  | _, .needsConversion _, _, _ => throw (.newTypeError .indices)
  | _, _, .needsConversion _, _ => throw (.newTypeError .offset1)
  | _, _, _, .needsConversion _ => throw (.newTypeError .stride1)
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure Tuple (Element : Type) where
  values : List Element
  nativeArity : values.length ≤ 2 ^ 32 - 1
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure MismatchOps (m : Type → Type) (Parent Dim OtherMessage External : Type) where
  ndims : Parent → m Dim
  string : String → I64 → String → Dim → String → m (FieldInput String OtherMessage)
  argumentErrorOther : OtherMessage → m (Error External)
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def checkParentIndexMismatch {m : Type → Type} [Monad m]
    {Parent Dim OtherMessage External : Type} [MonadExceptOf (Error External) m]
    (ops : MismatchOps m Parent Dim OtherMessage External)
    (parent : Parent) (indices : Tuple Bool) : m Unit := do
  let dimensions ← ops.ndims parent
  let message ← ops.string "number of indices (" (int64 (Int.ofNat indices.values.length))
    ") must match the parent dimensionality (" dimensions ")"
  match message with
  | .typed text => throw (.julia (.argumentError text))
  | .needsConversion other =>
      let error ← ops.argumentErrorOther other
      throw error
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-49. -/
-- Source: base/subarray.jl:19-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
structure Dims where
  values : List I64
  nativeArity : values.length ≤ (2 ^ 32 - 1) / 8
end JuliaLean.base.subarray.Models2Group14
namespace JuliaLean.base.subarray.Models2Group14

open JuliaLean JuliaLean.base.subarray


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure SimilarValueOps (m : Type → Type) (Parent ElementType Result : Type) where
  similar : Parent → ElementType → Dims → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def similarValue {m : Type → Type} {Tag Parent Indices ElementType Result : Type}
    (ops : SimilarValueOps m Parent ElementType Result)
    (view : View Tag Parent Indices) (elementType : ElementType) (dims : Dims) : m Result :=
  ops.similar view.parent elementType dims


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure ViewType (ParentType OtherBindings : Type) where
  parentType : ParentType
  otherBindings : OtherBindings


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure SimilarTypeOps (m : Type → Type) (ParentType Result : Type) where
  similar : ParentType → Dims → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def similarType {m : Type → Type} {ParentType OtherBindings Result : Type}
    (ops : SimilarTypeOps m ParentType Result)
    (viewType : ViewType ParentType OtherBindings) (dims : Dims) : m Result :=
  ops.similar viewType.parentType dims

end JuliaLean.base.subarray.Models2Group14
namespace JuliaLean.base.subarray.Models2Group14

open JuliaLean JuliaLean.base.subarray


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
structure TrimScalarOps (m : Type → Type) (Scalar Result : Type) where
  oftype : Scalar → I64 → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def trimmedScalar {m : Type → Type} {Scalar Result : Type}
    (ops : TrimScalarOps m Scalar Result) (index : Scalar) : m Result :=
  ops.oftype index (int64 1)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
structure TrimScalarArrayOps (m : Type → Type) (A Indices Axes Shaped Result : Type) where
  eachindex : IndexStyle → A → m Indices
  axes : A → m Axes
  reshape : Indices → Axes → m Shaped
  oftype : A → Shaped → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def trimmedScalarArray {m : Type → Type} [Monad m]
    {A Indices Axes Shaped Result : Type}
    (ops : TrimScalarArrayOps m A Indices Axes Shaped Result) (index : A) : m Result := do
  let indices ← ops.eachindex .linear index
  let axes ← ops.axes index
  let shaped ← ops.reshape indices axes
  ops.oftype index shaped


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
structure TrimCartesianZeroOps (m : Type → Type) (A Copied Result : Type) where
  copy : A → m Copied
  oftype : A → Copied → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def trimmedCartesianZero {m : Type → Type} [Monad m] {A Copied Result : Type}
    (ops : TrimCartesianZeroOps m A Copied Result) (index : A) : m Result := do
  let copied ← ops.copy index
  ops.oftype index copied


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
structure ValRank where
  value : I64


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
structure ReshapeParentOps (m : Type → Type) (A Result : Type) where
  reshape : A → ValRank → m Result


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def reshapeParentOne {m : Type → Type} {A Result : Type}
    (ops : ReshapeParentOps m A Result) (array : A) (_dimension : Bool) : m Result :=
  ops.reshape array ⟨int64 1⟩


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def reshapeParentRank {m : Type → Type} {A Result : Type}
    (ops : ReshapeParentOps m A Result) (array : A) (dimensions : Tuple Bool) : m Result :=
  ops.reshape array ⟨int64 dimensions.values.length⟩

end JuliaLean.base.subarray.Models2Group14

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `compute_linindex(f, s, IP, I)`, `base/subarray.jl:491-501`, for 1-based parent axes of lengths
`ips` (padded with `OneTo(1)` by `fill_to_length`, line 488) and indices whose `first` are `is`:
`Δi = first(I[1]) - first(IP[1])`. -/
def computeLinindex (f s : JInt64) : List JInt64 → List JInt64 → JInt64
  | _, [] => f
  | _, [i] => f + (i - JInt.lit .i64 1) * s
  | ips, i :: is => computeLinindex (f + (i - JInt.lit .i64 1) * s) (s * ips.headD (JInt.lit .i64 1)) ips.tail is

/-- `(offset1, stride1)` of `view(A, r, c2, ..., ck)` for a range `r = start:step:stop` and integer
scalars `cs`, `base/subarray.jl:34-44`: `compute_stride1` (lines 448-454) is `1 * step(r)`;
`compute_offset1` is `first(r) - stride1 * first(axes1(r))` for a vector parent (line 471) and
`compute_linindex(parent, I) - stride1 * first(axes1(r))` otherwise (lines 478-483, 486-490), with
`first(axes1(r)) == 1` and `first(LinearIndices(parent)) == 1`. -/
def viewLayout (sizes : List JInt64) (start step : JInt64) (cs : List JInt64) : JInt64 × JInt64 :=
  let stride1 := JInt.lit .i64 1 * step
  match cs with
  | [] => (start - stride1 * JInt.lit .i64 1, stride1)
  | _ => (computeLinindex (JInt.lit .i64 1) (JInt.lit .i64 1) sizes (start :: cs) - stride1 * JInt.lit .i64 1, stride1)

/-- `_reindexlinear(V, i) = V.offset1 + V.stride1*i`, `base/subarray.jl:327`: the parent linear index
read by `V[i]` (`base/subarray.jl:330-344`). -/
def viewParentIndex (layout : JInt64 × JInt64) (i : JInt64) : JInt64 := layout.1 + layout.2 * i

end JuliaLean.ReinterpretArrays

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- A view index after `to_indices`. -/
inductive VIdx where
  | scalar (i : Int)
  | slice (n : Nat)
  | vec (xs : List Int)
  deriving DecidableEq, Repr

/-- `xs[k]` for a one-based vector index. -/
def at1 (xs : List Int) (k : Int) : Int := xs.getD (k - 1).toNat 0

/-- `idxs[1][subidxs[1]]` for a vector parent index (`base/subarray.jl:304`): indexing a vector
with an `Int`, a `Slice(OneTo(m))` or a vector. -/
def index1 (xs : List Int) : VIdx → VIdx
  | .scalar k => .scalar (at1 xs k)
  | .slice m => .vec ((List.range m).map (fun k : Nat => at1 xs ((k : Int) + 1)))
  | .vec ks => .vec (ks.map (at1 xs))

/-- `reindex(idxs, subidxs)`, `base/subarray.jl:292-304`: scalars are kept and consume no
sub-index (295-296), a `Slice` passes its sub-index through (299-300), a vector index is indexed by
its sub-index (303-304). -/
def reindex : List VIdx → List VIdx → List VIdx
  | [], _ => []
  | .scalar i :: is, js => .scalar i :: reindex is js
  | .slice _ :: is, j :: js => j :: reindex is js
  | .vec xs :: is, j :: js => index1 xs j :: reindex is js
  | _ :: _, [] => []

/-- The parent subscripts read by `V[K...]` for a view with stored indices `I` and `Int`
subscripts `K` (`getindex(V::SubArray, I::Vararg{Int,N})`, line 319). -/
def readSubs (I : List VIdx) (K : List Int) : List VIdx := reindex I (K.map .scalar)

end JuliaLean.BroadcastViews

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- A parent index of a view, after `to_indices`. -/
inductive LIdx where
  | scalar (c : I64)
  | slice
  | urange (lo len : I64)
  | srange (start step len : I64)
  deriving DecidableEq, Repr

def LIdx.isScalar : LIdx → Bool
  | .scalar _ => true
  | _ => false

/-- `viewindexing(I)` is `IndexLinear()`, `base/subarray.jl:52-67`: leading scalars are skipped
(54), `Slice`s may be followed by more `Slice`s (56) and then by one `AbstractUnitRange` and
scalars (58) or only scalars (59, 63); a single range followed by scalars is linear (63); all other
tuples are `IndexCartesian()` (65, 67). -/
def viewLinear : List LIdx → Bool
  | [] => true
  | .scalar _ :: is => viewLinear is
  | .slice :: .slice :: is => viewLinear (.slice :: is)
  | .slice :: .urange _ _ :: is => is.all LIdx.isScalar
  | .slice :: is => is.all LIdx.isScalar
  | .urange _ _ :: is => is.all LIdx.isScalar
  | .srange _ _ _ :: is => is.all LIdx.isScalar

/-- `compute_stride1(s, inds, I)`, `base/subarray.jl:450-456`: all-scalar tuples return `s`
(451), a leading scalar multiplies `s` by the length of its parent axis (452-453), a `Slice`
returns `s` (455), another range returns `s * Int(step(I[1]))` (454). -/
def computeStride1 (s : I64) : List I64 → List LIdx → I64
  | _, [] => s
  | ns, i :: is =>
    if (i :: is).all LIdx.isScalar then s
    else match i, ns with
      | .scalar _, n :: ns' => computeStride1 (s * n) ns' is
      | .scalar _, [] => computeStride1 (s * i64 1) [] is
      | .slice, _ => s
      | .urange _ _, _ => s * i64 1
      | .srange _ st _, _ => s * st

/-- `first(I[d])` for an index. -/
def LIdx.first : LIdx → I64
  | .scalar c => c
  | .slice => i64 1
  | .urange lo _ => lo
  | .srange st _ _ => st

/-- `compute_linindex(f, s, IP, I)`, `base/subarray.jl:491-501`, with one-based parent axes:
`Δi = first(I[1]) - first(IP[1])`, `f + Δi*s`, next stride `s*length(IP[1])`. -/
def computeLinindex (f s : I64) : List I64 → List LIdx → I64
  | _, [] => f
  | _, [i] => f + (i.first - i64 1) * s
  | ns, i :: is => computeLinindex (f + (i.first - i64 1) * s) (s * ns.headD (i64 1)) ns.tail is

/-- `compute_offset1(parent, stride1, I)`, `base/subarray.jl:478-485`: with exactly one non-scalar
index, `compute_linindex(parent, I) - stride1*first(axes(...))` where that first axis element is 1
(480-483); otherwise `compute_linindex(parent, I) - stride1` (484-485). -/
def computeOffset1 (ns : List I64) (stride1 : I64) (I : List LIdx) : I64 :=
  let L := computeLinindex (i64 1) (i64 1) ns I
  if (I.filter (fun i => !i.isScalar)).length = 1 then L - stride1 * i64 1 else L - stride1

/-- The parent linear index read by `V[i]` for a fast linear view: `V.offset1 + V.stride1*i`
(`_reindexlinear`, line 327; `FastContiguousSubArray` uses `V.offset1 + i`, line 351, with
`stride1 == 1`). -/
def fastParentIndex (ns : List I64) (I : List LIdx) (i : I64) : I64 :=
  let stride1 := computeStride1 (i64 1) ns I
  computeOffset1 ns stride1 I + stride1 * i

end JuliaLean.BroadcastViews

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `substrides(strds, I)`, `base/subarray.jl:439-444`: scalars drop their stride, a `Slice` keeps
it, a range multiplies it by its step. -/
def substrides : List I64 → List LIdx → List I64
  | _ :: st, .scalar _ :: is => substrides st is
  | s :: st, .slice :: is => s :: substrides st is
  | s :: st, .urange _ _ :: is => s * i64 1 :: substrides st is
  | s :: st, .srange _ step _ :: is => s * step :: substrides st is
  | _, _ => []

/-- `size(V)`: the lengths of the non-scalar indices (`length(Slice(OneTo(n))) == n`). -/
def viewSize : List I64 → List LIdx → List I64
  | _ :: ns, .scalar _ :: is => viewSize ns is
  | n :: ns, .slice :: is => n :: viewSize ns is
  | _ :: ns, .urange _ len :: is => len :: viewSize ns is
  | _ :: ns, .srange _ _ len :: is => len :: viewSize ns is
  | _, _ => []

/-- `stride(V::SubArray, d) = d <= ndims(V) ? strides(V)[d] : strides(V)[end] * size(V)[end]`
(`base/subarray.jl:446`), with `strides(V) = substrides(strides(V.parent), V.indices)` (437) and
`strides(::Array) = size_to_strides(1, size(a)...)` (`base/reinterpretarray.jl:204`). Indexing the
empty tuple `()[end]` throws `BoundsError`. -/
def strideSub (ns : List I64) (I : List LIdx) (d : Nat) : R I64 :=
  let st := substrides (sizeToStrides (i64 1) ns) I
  let sz := viewSize ns I
  if d ≤ st.length then .ok (st.getD (d - 1) (i64 0))
  else match st.getLast?, sz.getLast? with
    | some a, some b => .ok (a * b)
    | _, _ => .error .boundsError

end JuliaLean.BroadcastViews

namespace JuliaLean.Multidim

/-- Axis lengths seen by `k` consumed dimensions of an array of size `sz`: trailing
dimensions beyond `ndims` have length 1; with fewer indices than dimensions the last
index spans the remaining dimensions (linear indexing). -/
def axesFor (sz : List Nat) (k : Nat) : List Nat :=
  if sz.length ≤ k then sz ++ List.replicate (k - sz.length) 1
  else sz.take (k - 1) ++ [(sz.drop (k - 1)).foldl (· * ·) 1]

/-- Split the axis lengths among the indices. -/
def splitAxes : List Idx → List Nat → List (Idx × List Nat)
  | [], _ => []
  | i :: is, ax => (i, ax.take i.ndims) :: splitAxes is (ax.drop i.ndims)


/-- Length of the view dimension an index produces (`none`: dropped, scalar). -/
def idxLen : Idx → List Nat → Option Nat
  | .urange lo hi, _ => some (hi - lo + 1).toNat
  | .colon, ns => some (ns.foldl (· * ·) 1)
  | .slice n, _ => some n
  | _, _ => none

/-- `view(A, I...)` for an `Array` of size `sz` (`base/subarray.jl`): `to_indices`
rejects `Bool` scalars with `ArgumentError` (`to_index(::Bool)`), then `checkbounds`
throws `BoundsError`. Returns the size of the view. -/
def view (sz : List Nat) (I : List Idx) : R (List Nat) :=
  let parts := splitAxes I (axesFor sz (I.foldl (fun k i => k + i.ndims) 0))
  if I.any (fun i => match i with | .bool _ => true | _ => false) then .error .argumentError
  else if !(parts.all fun (i, ns) => checkIdx i ns) then .error .boundsError
  else .ok (parts.filterMap fun (i, ns) => idxLen i ns)

end JuliaLean.Multidim

namespace JuliaLean.ReinterpretArrays

/-- First-dimension view indices: `Base.Slice(IdentityUnitRange(lo:hi))` or `IdentityUnitRange(lo:hi)`. -/
inductive RowIndex where
  | slice (lo hi : Int)
  | iur (lo hi : Int)
  deriving DecidableEq, Repr

/-- `first` and `last` of a row index. -/
def RowIndex.lo : RowIndex → Int | .slice lo _ => lo | .iur lo _ => lo
def RowIndex.hi : RowIndex → Int | .slice _ hi => hi | .iur _ hi => hi

/-- `offset1` of `SubArray(M, (I1, c))` for an `s1 × s2` matrix, `base/subarray.jl:34-44,478-490`:
`stride1 = 1` (`compute_stride1`, lines 448-455); a `Slice` first index takes the index-preserving
branch `compute_linindex(parent, I) - stride1*first(axes(parent, 1))` (line 481), any other range
`compute_linindex(parent, I) - stride1*first(axes1(I1))` (line 483). `compute_linindex` is
`1 + (first(I1) - 1) + (c - 1) * s1` (lines 486-500). -/
def offset1 (s1 : Int) (I1 : RowIndex) (c : Int) : Int :=
  let lin := 1 + (I1.lo - 1) + (c - 1) * s1
  match I1 with
  | .slice _ _ => lin - 1
  | .iur lo _ => lin - lo

/-- `view(view(M, IdentityUnitRange(lo:hi), c), :)`: `to_indices` turns `:` into
`Slice(axes(V, 1)) = Slice(IdentityUnitRange(lo:hi))`; `_maybe_reindex` (`base/subarray.jl:276-280`)
builds `SubArray(M, reindex(V.indices, I))`, and `reindex` (line 303) indexes
`IdentityUnitRange(lo:hi)[Slice(IdentityUnitRange(lo:hi))]`, which
`getindex(::IdentityUnitRange, ::AbstractUnitRange)` (`base/indices.jl`) returns as the `Slice`
itself. Returns the parent linear index read by `W[i]` (`_reindexlinear`, line 327). -/
def nestedColonParentIndex (s1 lo hi c i : Int) : Int :=
  offset1 s1 (.slice lo hi) c + 1 * i

end JuliaLean.ReinterpretArrays
