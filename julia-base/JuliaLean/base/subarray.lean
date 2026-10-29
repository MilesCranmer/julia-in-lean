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
def trimmedParentIndices {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (colon : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  (axes index).map colon ++ trimmed rest

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
def trimmedViewIndices {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (colon : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  (axes index).map colon ++ trimmed rest

/--
Julia source: base/subarray.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
```
-/
def trimmedViewCartesianZero {A : Type} (index : A) (rest : List A)
    (axes : A → List Axis) (first : Axis → Index)
    (trimmed : List A → List Index) : List Index :=
  (axes index).map first ++ trimmed rest

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
def trimmedIndexCartesian {A : Type} (rank : Nat) (index : A)
    (eachindex : A → List IndexStyle → List Index) (cartesianIndices : List Index → A)
    (reshape : A → List Axis → A) (axes : A → List Axis) (ofType : A → A → A) : A := Id.run do
  let padding := List.replicate (rank - 1) (Index.scalar (int64 1))
  let ax1 := eachindex index [.linear]
  return ofType index (reshape (cartesianIndices (ax1 ++ padding)) (axes index))

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
def reindexArray (rank : Nat) (index : Index) (rest subindices : List Index)
    (getindex : Index → List Index → Jl Index)
    (reindex : List Index → List Index → Jl (List Index)) : Jl (List Index) := do
  let selected := subindices.take rank
  let value ← getindex index selected
  let tail ← reindex rest (subindices.drop rank)
  pure (value :: tail)

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
def reindexLinearUnitRange {P T R : Type} (V : SubArray P T) (indices : R)
    (broadcastMultiply : I64 → R → Jl R) (broadcastAdd : I64 → R → Jl R) : Jl R := do
  let scaled ← broadcastMultiply V.stride1 indices
  broadcastAdd V.offset1 scaled

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
def reindexLinearContiguousUnitRange {P T R : Type} (V : SubArray P T) (indices : R)
    (broadcastAdd : I64 → R → Jl R) : Jl R := broadcastAdd V.offset1 indices

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
def getindexFastContiguousColon {P T R : Type} (V : SubArray P T) (colon : Index)
    (toIndices : SubArray P T → List Index → Jl (List Index))
    (getindex : SubArray P T → Index → Jl R) : Jl R := do
  let indices ← toIndices V [colon]
  match indices with
  | [index] => getindex V index
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
def setindexFastColon {P T R : Type} (V : SubArray P T) (value : R) (colon : Index)
    (toIndices : SubArray P T → List Index → Jl (List Index))
    (setindex : SubArray P T → R → Index → Jl (SubArray P T)) : Jl (SubArray P T) := do
  let indices ← toIndices V [colon]
  match indices with
  | [index] => setindex V value index
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
def substridesScalar (strides : List I64) (_scalar : Index) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) :=
  substrides (strides.drop 1) rest

/--
Julia source: base/subarray.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{Slice, Vararg{Any}}) where N = (first(strds), substrides(tail(strds), tail(I))...)
```
-/
def substridesSlice (strides : List I64) (_slice : Index) (rest : List Index)
    (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  match strides with
  | [] => .error .boundsError
  | stride :: tail => return stride :: (← substrides tail rest)

/--
Julia source: base/subarray.jl:442-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{AbstractRange, Vararg{Any}}) where N = (first(strds)*Int(step(I[1])), substrides(tail(strds), tail(I))...)
```
-/
def substridesRange (strides : List I64) (index : Index) (rest : List Index)
    (step : Index → I64) (substrides : List I64 → List Index → Jl (List I64)) : Jl (List I64) := do
  match strides with
  | [] => .error .boundsError
  | stride :: tail => return imul stride (step index) :: (← substrides tail rest)

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
  | strides, .scalar _ :: rest =>
      substridesDispatch step typeName (strides.drop 1) rest
  | [], .slice _ :: _ => .error .boundsError
  | stride :: tail, .slice _ :: rest => do
      let restStrides ← substridesDispatch step typeName tail rest
      pure (stride :: restStrides)
  | [], index :: _ =>
      if Index.isRange index then .error .boundsError
      else substridesInvalid [] (typeName index)
  | stride :: tail, index :: rest =>
      if Index.isRange index then do
        let restStrides ← substridesDispatch step typeName tail rest
        pure (imul stride (step index) :: restStrides)
      else substridesInvalid (stride :: tail) (typeName index)
termination_by structural strides indices => indices

/--
Julia source: base/subarray.jl:446-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stride(V::SubArray, d::Integer) = d <= ndims(V) ? strides(V)[d] : strides(V)[end] * size(V)[end]
```
-/
def strideSubArray {P T D : Type} (V : SubArray P T) (dimension : D)
    (toInt : D → I64) (ndims : SubArray P T → Nat) (strides size : SubArray P T → Jl (List I64))
    (get : List I64 → I64 → Jl I64) (last : List I64 → Jl I64) : Jl I64 := do
  let ds ← strides V
  if (toInt dimension).val ≤ (ndims V : Int) then get ds (toInt dimension)
  else
    let sizes ← size V
    pure (imul (← last ds) (← last sizes))

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
def computeStride1Scalar (stride : I64) (axes : List Axis) (_scalar : Index) (rest : List Index)
    (length : Axis → I64) (computeRec : I64 → List Axis → List Index → Jl I64) : Jl I64 :=
  match axes with
  | [] => .error .boundsError
  | axis :: tail => computeRec (imul stride (length axis)) tail rest

/--
Julia source: base/subarray.jl:454-454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{AbstractRange, Vararg{Any}}) = s * Int(step(I[1]))
```
-/
def computeStride1Range (stride : I64) (_axes : List Axis) (range : Index)
    (step : Index → I64) : Jl I64 := .ok (imul stride (step range))

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
def firstIndexFastSubArray {P T : Type} (V : SubArray P T)
    (firstindex : SubArray P T → I64) : I64 :=
  iadd V.offset1 (imul V.stride1 (firstindex V))

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
def computeOffset1VectorRange (index : Index) (stride1 : I64)
    (first : Index → Jl I64) (axes1First : Index → Jl I64) : Jl I64 := do
  let indexFirst ← first index
  let axisFirst ← axes1First index
  pure (isub indexFirst (imul stride1 axisFirst))

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
def computeOffset1Slice {P : Type} (parent : P) (stride1 : I64) (dimension : I64)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64)
    (axisFirst : P → I64 → Jl I64) : Jl I64 := do
  let linearIndex ← computeLinindex parent indices
  let first ← axisFirst parent dimension
  pure (isub linearIndex (imul stride1 first))

/--
Julia source: base/subarray.jl:482-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, dims, inds::Tuple{AbstractRange}, I::Tuple) =
    (@inline; compute_linindex(parent, I) - stride1*Int(first(axes1(inds[1])))) # potentially index-offsetting case
```
-/
def computeOffset1Range {P : Type} (parent : P) (stride1 : I64) (index : Index)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64)
    (axisFirst : Index → Jl I64) : Jl I64 := do
  let linearIndex ← computeLinindex parent indices
  let first ← axisFirst index
  pure (isub linearIndex (imul stride1 first))

/--
Julia source: base/subarray.jl:484-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent, stride1::Integer, dims, inds, I::Tuple) =
    (@inline; compute_linindex(parent, I) - stride1)
```
-/
def computeOffset1Fallback {P : Type} (parent : P) (stride1 : I64)
    (indices : List Index) (computeLinindex : P → List Index → Jl I64) : Jl I64 := do
  let linearIndex ← computeLinindex parent indices
  pure (isub linearIndex stride1)

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
def pointerCartesianSubArray {P T R : Type} (V : SubArray P T) (indices : List I64)
    (firstIndex : SubArray P T → Jl I64) (strides : SubArray P T → Jl (List I64))
    (atOneBased : List I64 → I64 → Jl I64) (pointerParent : P → I64 → Jl R) : Jl R := do
  let mut index ← firstIndex V
  let strides ← strides V
  for d in [:indices.length] do
    let dimension := int64 ((d : Int) + 1)
    let coordinate ← atOneBased indices dimension
    let stride ← atOneBased strides dimension
    index := iadd index (imul (isub coordinate (int64 1)) stride)
  pointerParent V.parent index

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
def replaceInPrintMatrix {P T D : Type} (S : SubArray P T) (i j : D) (toInt : D → I64) (string : String)
    (reindex : List Index → List Index → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → String → Jl String) : Jl String := do
  let indices ← reindex S.indices [Index.scalar (toInt i), Index.scalar (toInt j)]
  let parentIndices ← toIndices S.parent indices
  replaceParent S.parent parentIndices string

/--
Julia source: base/subarray.jl:548-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_in_print_matrix(S::SubArray{<:Any,1,<:AbstractVector}, i::Integer, j::Integer, s::AbstractString)
    replace_in_print_matrix(S.parent, to_indices(S.parent, reindex(S.indices, (i,)))..., j, s)
end
```
-/
def replaceInPrintVector {P T D : Type} (S : SubArray P T) (i j : D) (toInt : D → I64) (string : String)
    (reindex : List Index → List Index → Jl (List Index))
    (toIndices : P → List Index → Jl (List Index))
    (replaceParent : P → List Index → I64 → String → Jl String) : Jl String := do
  let indices ← reindex S.indices [Index.scalar (toInt i)]
  let parentIndices ← toIndices S.parent indices
  replaceParent S.parent parentIndices (toInt j) string

/--
Julia source: base/subarray.jl:553-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(::Type{Vector{UInt8}}, s::FastContiguousSubArray{UInt8,1,Vector{UInt8}}) = unsafe_wrap(Vector{UInt8}, pointer(s), size(s))
```
-/
def unsafeWrapContiguousSubArray {P T R : Type} (view : SubArray P T)
    (pointer : SubArray P T → Jl R) (size : SubArray P T → Jl (List I64))
    (unsafeWrap : R → List I64 → Jl R) : Jl R := do
  let ptr ← pointer view
  let dims ← size view
  unsafeWrap ptr dims

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
