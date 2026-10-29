import JuliaLean.Core
import JuliaLean.base.abstractarray

/-!
# Model of `base/slicearray.jl`

Typed source models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform.
Array operations from other Base files remain typed interfaces. Dimension tuples and axis tuples
are represented as lists, so the model accepts every dimension count and preserves tuple order.
-/

namespace JuliaLean.base.slicearray

open JuliaLean

abbrev I64 := JInt .i64
abbrev Result := JuliaLean.base.abstractarray.Result

def int (z : Int) : I64 := JInt.lit .i64 z

/-- An AbstractUnitRange axis, represented by its first index, length, and index type. -/
structure SliceAxis where
  first : I64
  length : I64
  indexType : String

/-- The type of one argument passed to `view`: a colon or an axis index type. -/
inductive SliceViewArgument where
  | colon
  | index (indexType : String)

structure Slices (Parent : Type) (N : Nat) where
  parent : Parent
  viewType : String
  slicemap : List (Option Nat)
  axes : List SliceAxis
  axes_length : axes.length = N

def SliceConstruction (Parent : Type) :=
  Σ N : Nat, Slices Parent N

/-- The array operations supplied by AbstractArray and view methods. -/
structure SliceArrayOps (Parent View Value Element : Type) where
  parentType : String
  ndims : Parent → Nat
  axes : {Dimension : Type} → Parent → Dimension → SliceAxis
  showInteger : {Dimension : Type} → Dimension → String
  showIntegerTuple : {Dimension : Type} → List Dimension → String
  view : Parent → List (Option I64) → Result View
  getindexView : View → List I64 → Result Element
  getindexParent : Parent → List I64 → Result Element
  setindexParent : Parent → List (Option I64) → Value → Result Value
  getindexValue : Value → List I64 → Result Element
  promoteView : String → List SliceViewArgument → String

def oneToAxis (length : I64) : SliceAxis :=
  { first := int 1, length, indexType := "Int64" }

/-- An N-index tuple for the fixed-arity `getindex` and `setindex!` methods. -/
structure IntegerIndices (N : Nat) where
  values : List I64
  length_eq : values.length = N

/--
Julia source: base/slicearray.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unitaxis(::AbstractArray) = Base.OneTo(1)
```
-/
def unitaxis {A : Type} (_array : A) : SliceAxis := oneToAxis (int 1)

/--
Julia source: base/slicearray.jl:41-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Slices(A::P, slicemap::SM, ax::AX) where {P,SM,AX}
    length(slicemap) >= ndims(A) ||
        throw(ArgumentError("Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))
    N = length(ax)
    parent_axes = ntuple(d -> axes(A, d), length(slicemap))
    argT = map((a,l) -> l === (:) ? Colon : eltype(a), parent_axes, slicemap)
    S = Base.promote_op(view, P, argT...)
    Slices{P,SM,AX,S,N}(A, slicemap, ax)
end
```
-/
def slicesConstructor {A View Value Element : Type}
    (ops : SliceArrayOps A View Value Element)
    (a : A) (slicemap : List (Option Nat)) (ax : List SliceAxis) :
    Result (SliceConstruction A) :=
  if slicemap.length < ops.ndims a then
    .error (.julia (.argumentError
      "Slices cannot be constructed with a slicemap of fewer elements than the parent has dimensions"))
  else
    let n := ax.length
    let parentAxes := (List.range slicemap.length).map fun d : Nat => ops.axes a (int (Int.ofNat (d + 1)))
    let argT := List.zipWith
      (fun axis entry => match entry with
        | none => .colon
        | some _ => .index axis.indexType)
      parentAxes slicemap
    let viewType := ops.promoteView ops.parentType argT
    .ok ⟨n,
      { parent := a, viewType, slicemap, axes := ax, axes_length := rfl }⟩

/--
Julia source: base/slicearray.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_slice_check_dims() = nothing
```
-/
def sliceCheckDimsEmpty : Result Unit := .ok ()

/--
Julia source: base/slicearray.jl:52-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _slice_check_dims(dim, dims...)
    1 <= dim || throw(DimensionMismatch("Invalid dimension $dim"))
    dim in dims && throw(DimensionMismatch("Dimensions $dims are not unique"))
    _slice_check_dims(dims...)
end
```
-/
def sliceCheckDims {D : Type} (dimensionValue : D → Int)
    (showInteger : D → String) (showIntegerTuple : List D → String) :
    List D → Result Unit
  | [] => sliceCheckDimsEmpty
  | dimension :: dimensions =>
      if dimensionValue dimension < 1 then
        .error (.dimensionMismatch ("Invalid dimension " ++ showInteger dimension))
      else if dimensions.any (fun other => dimensionValue other == dimensionValue dimension) then
        .error (.dimensionMismatch
          ("Dimensions " ++ showIntegerTuple dimensions ++ " are not unique"))
      else
        sliceCheckDims dimensionValue showInteger showIntegerTuple dimensions

/-- Find the one-based tuple position of a selected dimension. -/
def slicePosition {D : Type} (dimensionValue : D → Int)
    (dimensions : List D) (position : Nat) : Option Nat :=
  (dimensions.findIdx? fun dimension =>
    dimensionValue dimension == Int.ofNat (position + 1)).map (· + 1)

/--
Julia source: base/slicearray.jl:58-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function _eachslice(A::AbstractArray{T,N}, dims::NTuple{M,Integer}, drop::Bool) where {T,N,M}
    _slice_check_dims(dims...)
    N_ = foldl(max, dims; init=N)

    if drop
        # if N = 4, dims = (3,1) then
        # axes = (axes(A,3), axes(A,1))
        # slicemap = (2, :, 1, :)
        ax = map(dim -> axes(A,dim), dims)
        slicemap = ntuple(dim -> something(findfirst(isequal(dim), dims), (:)),  N_)
        return Slices(A, slicemap, ax)
    else
        # if N = 4, dims = (3,1) then
        # axes = (axes(A,1), OneTo(1), axes(A,3), OneTo(1))
        # slicemap = (1, :, 3, :)
        ax = ntuple(dim -> dim in dims ? axes(A,dim) : unitaxis(A), N_)
        slicemap = ntuple(dim -> dim in dims ? dim : (:), N_)
        return Slices(A, slicemap, ax)
    end
end
```
-/
def eachsliceTuple {A View Value Element D : Type}
    (ops : SliceArrayOps A View Value Element)
    (dimensionValue : D → Int) (a : A) (dims : List D) (drop : Bool) :
    Result (SliceConstruction A) := do
  let _ ← sliceCheckDims dimensionValue ops.showInteger ops.showIntegerTuple dims
  let rank := dims.foldl (fun n dim => max n (dimensionValue dim).toNat) (ops.ndims a)
  if drop then
    let ax := dims.map (ops.axes a)
    let slicemap := (List.range rank).map (slicePosition dimensionValue dims)
    slicesConstructor ops a slicemap ax
  else
    let ax := (List.range rank).map fun d : Nat =>
      if dims.any (fun dimension => dimensionValue dimension == Int.ofNat (d + 1))
      then ops.axes a (int (Int.ofNat (d + 1)))
      else unitaxis a
    let slicemap := (List.range rank).map fun d : Nat =>
      if dims.any (fun dimension => dimensionValue dimension == Int.ofNat (d + 1))
      then some (d + 1) else none
    slicesConstructor ops a slicemap ax

/--
Julia source: base/slicearray.jl:78-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _eachslice(A::AbstractArray, dim::Integer, drop::Bool)
    _eachslice(A, (dim,), drop)
end
```
-/
def eachsliceDimension {A View Value Element D : Type}
    (ops : SliceArrayOps A View Value Element)
    (dimensionValue : D → Int) (a : A) (dim : D) (drop : Bool) :
    Result (SliceConstruction A) :=
  eachsliceTuple ops dimensionValue a [dim] drop

/--
Julia source: base/slicearray.jl:132-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function eachslice(A; dims, drop=true)
    _eachslice(A, dims, drop)
end
```
-/
def eachslice {A D R : Type} (slice : A → D → Bool → Result R)
    (a : A) (dims : D) (drop : Bool) : Result R :=
  slice a dims drop

/--
Julia source: base/slicearray.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrow(A::AbstractMatrix) = _eachslice(A, (1,), true)
```
-/
def eachrowMatrix {A : Type}
    (slice : A → List I64 → Bool → Result (SliceConstruction A))
    (a : A) : Result (SliceConstruction A) :=
  slice a [int 1] true

/--
Julia source: base/slicearray.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrow(A::AbstractVector) = eachrow(reshape(A, size(A,1), 1))
```
-/
def eachrowVector {A B : Type}
    (sizeDim : A → I64 → Result I64)
    (reshape : A → I64 → I64 → Result B)
    (eachrow : B → Result (SliceConstruction B))
    (a : A) : Result (SliceConstruction B) := do
  let firstSize ← sizeDim a (int 1)
  let reshaped ← reshape a firstSize (int 1)
  eachrow reshaped

/--
Julia source: base/slicearray.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachcol(A::AbstractMatrix) = _eachslice(A, (2,), true)
```
-/
def eachcolMatrix {A : Type}
    (slice : A → List I64 → Bool → Result (SliceConstruction A))
    (a : A) : Result (SliceConstruction A) :=
  slice a [int 2] true

/--
Julia source: base/slicearray.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachcol(A::AbstractVector) = eachcol(reshape(A, size(A, 1), 1))
```
-/
def eachcolVector {A B : Type}
    (sizeDim : A → I64 → Result I64)
    (reshape : A → I64 → I64 → Result B)
    (eachcol : B → Result (SliceConstruction B))
    (a : A) : Result (SliceConstruction B) := do
  let firstSize ← sizeDim a (int 1)
  let reshaped ← reshape a firstSize (int 1)
  eachcol reshaped

/--
Julia source: base/slicearray.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(s::Slices) = s.axes
```
-/
def axes {Parent : Type} {N : Nat} (s : Slices Parent N) : List SliceAxis := s.axes

/--
Julia source: base/slicearray.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(s::Slices) = map(length, s.axes)
```
-/
def size {Parent : Type} {N : Nat} (s : Slices Parent N) : List I64 :=
  s.axes.map fun axis => axis.length

/--
Julia source: base/slicearray.jl:236-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _slice_index(s::Slices, c...)
    return map(l -> l === (:) ? (:) : c[l], s.slicemap)
end
```
-/
def sliceIndex {Parent : Type} {N : Nat}
    (s : Slices Parent N) (coordinates : List I64) :
    Result (List (Option I64)) :=
  s.slicemap.mapM fun entry =>
    match entry with
    | none => pure none
    | some dimension => do
        let coordinate ← JuliaLean.base.abstractarray.tupleGet coordinates (int (Int.ofNat dimension))
        pure (some coordinate)

/--
Julia source: base/slicearray.jl:240-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(s::Slices{P,SM,AX,S,N}, I::Vararg{Int,N}) where {P,SM,AX,S,N}
    @boundscheck checkbounds(s, I...)
    @inbounds view(s.parent, _slice_index(s, I...)...)
end
```
-/
def getindex {Parent View Value Element : Type} {N : Nat}
    (checkbounds : Slices Parent N → IntegerIndices N → Result Unit)
    (ops : SliceArrayOps Parent View Value Element)
    (s : Slices Parent N) (indices : IntegerIndices N) : Result View := do
  let _ ← checkbounds s indices
  ops.view s.parent (← sliceIndex s indices.values)
/--
Julia source: base/slicearray.jl:244-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(s::Slices{P,SM,AX,S,N}, val, I::Vararg{Int,N}) where {P,SM,AX,S,N}
    @boundscheck checkbounds(s, I...)
    @inbounds s.parent[_slice_index(s, I...)...] = val
end
```
-/
def setindex! {Parent View Value Element : Type} {N : Nat}
    (checkbounds : Slices Parent N → IntegerIndices N → Result Unit)
    (ops : SliceArrayOps Parent View Value Element)
    (s : Slices Parent N) (value : Value) (indices : IntegerIndices N) : Result Value := do
  let _ ← checkbounds s indices
  ops.setindexParent s.parent (← sliceIndex s indices.values) value

/--
Julia source: base/slicearray.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(s::Slices) = s.parent
```
-/
def parent {Parent : Type} {N : Nat} (s : Slices Parent N) : Parent := s.parent

end JuliaLean.base.slicearray
