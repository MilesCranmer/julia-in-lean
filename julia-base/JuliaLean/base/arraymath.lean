import JuliaLean.Core
import JuliaLean.base.array
import JuliaLean.base.abstractarray

/-!
# Model of `base/arraymath.jl`

Typed models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform.
Arrays, axes, mapping, allocation, mutation, and later-loaded arithmetic are typed interfaces.
The effect type preserves Julia call order and errors. Index and dimension values are `Int64`.
-/

namespace JuliaLean.base.arraymath

open JuliaLean

abbrev I64 := JuliaLean.base.abstractarray.I64
abbrev Result := JuliaLean.base.abstractarray.Result

/-- The AbstractArray axis interface used by dimension-indexed methods. -/
structure ArrayIndexOps (m : Type → Type) (A Axis : Type) where
  liftResult : {α : Type} → Result α → m α
  axes : A → Result (List Axis)
  ndims : A → I64
  oneTo : I64 → Axis
  first : Axis → Result I64
  last : Axis → Result I64
  indices : Axis → List I64
def resultIndexOps {m : Type → Type} {A Axis : Type} (ops : ArrayIndexOps m A Axis) :
    ArrayIndexOps Result A Axis :=
  { liftResult := fun result => result, axes := ops.axes, ndims := ops.ndims,
    oneTo := ops.oneTo, first := ops.first, last := ops.last, indices := ops.indices }

/-- The source `axes(A, d)` method, instantiated with the real AbstractArray model. -/
def axisAtResult {A Axis : Type} (ops : ArrayIndexOps Result A Axis)
    (a : A) (dim : I64) : Result Axis :=
  JuliaLean.base.abstractarray.axesDim
    (fun d n => decide (d.val ≤ n.val)) ops.axes
    (fun axes d => JuliaLean.base.abstractarray.tupleGet axes d)
    ops.oneTo (ops.ndims a) a dim

def axisAt [Monad m] {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (a : A) (dim : I64) : m Axis :=
  ops.liftResult (axisAtResult (resultIndexOps ops) a dim)

def firstIndexAt [Monad m] {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (a : A) (dim : I64) : m I64 :=
  ops.liftResult (JuliaLean.base.abstractarray.firstindexDim
    (axisAtResult (resultIndexOps ops)) ops.first a dim)

def lastIndexAt [Monad m] {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (a : A) (dim : I64) : m I64 :=
  ops.liftResult (JuliaLean.base.abstractarray.lastindexDim
    (axisAtResult (resultIndexOps ops)) ops.last a dim)

def sizeAt [Monad m] {A : Type} (liftResult : {α : Type} → Result α → m α)
    (size : A → Result (List I64)) (a : A) (dim : I64) : m I64 :=
  liftResult (JuliaLean.base.abstractarray.sizeDim (fun d => .ok d) size a dim)

def dimensions (rank : Nat) : List I64 :=
  (List.range rank).map fun k => JuliaLean.base.abstractarray.int (Int.ofNat (k + 1))

def cartesianIndices : List (List I64) → List (List I64)
  | [] => [[]]
  | axis :: axes => (cartesianIndices axes).flatMap fun tail =>
      axis.map fun index => index :: tail

def reflectedIndex (reversed : List Bool) (offsets index : List I64) : List I64 :=
  ((reversed.zip offsets).zip index).map fun item =>
    if item.1.1 then item.1.2 - item.2 else item.2

/-! ## Zero-dimensional-preserving broadcast helpers -/

/--
Julia source: base/arraymath.jl:5-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _broadcast_preserving_zero_d(f, A, B)
    broadcast_preserving_zero_d(f, A, B)
end
```
-/
def broadcastDefault {F A B R : Type} (broadcast : F → A → B → Result R)
    (f : F) (a : A) (b : B) : Result R :=
  broadcast f a b

/--
Julia source: base/arraymath.jl:12-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _broadcast_preserving_zero_d(f, A::Array{<:Any,N}, B::Array{<:Any,N}, Cs::Array{<:Any,N}...) where {N}
    map(f, A, B, Cs...)
end
```
-/
def broadcastSameRank {F A R : Type} (mapArrays : F → A → A → List A → Result R)
    (f : F) (a b : A) (cs : List A) : Result R :=
  mapArrays f a b cs

/--
Julia source: base/arraymath.jl:16-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _broadcast_preserving_zero_d(f, A::Array, B::Array, Cs::Array...)
    # we already know that the shapes are compatible.
    # We just need to select the size corresponding to the highest ndims
    # and reshape all the arrays to that size
    arrays = (A, B, Cs...)
    sz = mapreduce(size, (x,y) -> length(x) > length(y) ? x : y, arrays)
    # Skip reshaping where possible to avoid the overhead
    arrays_sameshape = map(x -> length(sz) == ndims(x) ? x : reshape(x, sz), arrays)
    map(f, arrays_sameshape...)
end
```
-/
def broadcastArrayRanks {F A Shape R : Type}
    (size : A → Result Shape) (lengthShape : Shape → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape)
    (ndims : A → I64) (reshape : A → Shape → Result A)
    (mapArrays : F → List A → Result R) (f : F) (a b : A) (cs : List A) : Result R := do
  let arrays := a :: b :: cs
  let shape ← mapreduce size (fun x y => if lengthShape x > lengthShape y then x else y) arrays
  let arraysSameShape ← arrays.mapM fun array =>
    if lengthShape shape = ndims array then pure array else reshape array shape
  mapArrays f arraysSameShape

/--
Julia source: base/arraymath.jl:27-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _broadcast_preserving_zero_d(f, A::Array, B::Number)
    map(Fix2(f, B), A)
end
```
-/
def broadcastArrayScalar {F A B G R : Type} (fix2 : F → B → G)
    (map : G → A → Result R) (f : F) (a : A) (b : B) : Result R :=
  map (fix2 f b) a

/--
Julia source: base/arraymath.jl:31-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _broadcast_preserving_zero_d(f, A::Number, B::Array)
    map(Fix1(f, A), B)
end
```
-/
def broadcastScalarArray {F A B G R : Type} (fix1 : F → A → G)
    (map : G → B → Result R) (f : F) (a : A) (b : B) : Result R :=
  map (fix1 f a) b

def broadcastSameRankBinary {F A R : Type}
    (mapArrays : F → A → A → List A → Result R)
    (f : F) (a b : A) : Result R :=
  broadcastSameRank mapArrays f a b []

def broadcastArrayRanksBinary {F A Shape R : Type}
    (size : A → Result Shape) (shapeLength : Shape → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape)
    (ndims : A → I64) (reshape : A → Shape → Result A)
    (mapArrays : F → List A → Result R) (f : F) (a b : A) : Result R :=
  broadcastArrayRanks size shapeLength mapreduce ndims reshape mapArrays f a b []

/--
Julia source: base/arraymath.jl:35-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:+, :-)
    @eval function ($f)(A::AbstractArray, B::AbstractArray)
        promote_shape(A, B) # check size compatibility
        _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def addAbstractArrays {F A B R : Type} (promoteShape : A → B → Result Unit)
    (broadcast : F → A → B → Result R) (f : F) (a : A) (b : B) : Result R := do
  promoteShape a b
  broadcast f a b


/--
Julia source: base/arraymath.jl:35-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:+, :-)
    @eval function ($f)(A::AbstractArray, B::AbstractArray)
        promote_shape(A, B) # check size compatibility
        _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def subtractAbstractArrays {F A B R : Type} (promoteShape : A → B → Result Unit)
    (broadcast : F → A → B → Result R) (f : F) (a : A) (b : B) : Result R := do
  promoteShape a b
  broadcast f a b
/--
Julia source: base/arraymath.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(A::Array) = map(+, A)
```
-/
def unaryArrayPlus {A F R : Type} (map : F → A → Result R)
    (plus : F) (a : A) : Result R :=
  map plus a

/--
Julia source: base/arraymath.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(A::Array, B::Array, Cs::Array...)
    promote_shape(A, B)
    for C in Cs
        promote_shape(A, C) # check size compatibility
    end
    _broadcast_preserving_zero_d(+, A, B, Cs...)
end
```
-/
def addArrayMany {A F R : Type} (promoteShape : A → A → Result Unit)
    (broadcast : F → A → A → List A → Result R) (plus : F)
    (a b : A) (cs : List A) : Result R := do
  promoteShape a b
  for c in cs do
    promoteShape a c
  broadcast plus a b cs

/--
Julia source: base/arraymath.jl:52-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:/, :\, :*)
    if f !== :/
        @eval ($f)(A::Number, B::AbstractArray) = _broadcast_preserving_zero_d($f, A, B)
    end
    if f !== :\
        @eval ($f)(A::AbstractArray, B::Number) = _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def ldivScalarArray {F A B R : Type} (broadcast : F → A → B → Result R)
    (leftDivision : F) (scalar : A) (arrayValue : B) : Result R :=
  broadcast leftDivision scalar arrayValue

/--
Julia source: base/arraymath.jl:52-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:/, :\, :*)
    if f !== :/
        @eval ($f)(A::Number, B::AbstractArray) = _broadcast_preserving_zero_d($f, A, B)
    end
    if f !== :\
        @eval ($f)(A::AbstractArray, B::Number) = _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def mulScalarArray {F A B R : Type} (broadcast : F → A → B → Result R)
    (multiply : F) (scalar : A) (arrayValue : B) : Result R :=
  broadcast multiply scalar arrayValue

/--
Julia source: base/arraymath.jl:52-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:/, :\, :*)
    if f !== :/
        @eval ($f)(A::Number, B::AbstractArray) = _broadcast_preserving_zero_d($f, A, B)
    end
    if f !== :\
        @eval ($f)(A::AbstractArray, B::Number) = _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def divArrayScalar {F A B R : Type} (broadcast : F → A → B → Result R)
    (division : F) (arrayValue : A) (scalar : B) : Result R :=
  broadcast division arrayValue scalar

/--
Julia source: base/arraymath.jl:52-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:/, :\, :*)
    if f !== :/
        @eval ($f)(A::Number, B::AbstractArray) = _broadcast_preserving_zero_d($f, A, B)
    end
    if f !== :\
        @eval ($f)(A::AbstractArray, B::Number) = _broadcast_preserving_zero_d($f, A, B)
    end
end
```
-/
def mulArrayScalar {F A B R : Type} (broadcast : F → A → B → Result R)
    (multiply : F) (arrayValue : A) (scalar : B) : Result R :=
  broadcast multiply arrayValue scalar

/-! ## Reversal -/

structure ReverseOps (m : Type → Type) (A V Axis : Type) where
  index : ArrayIndexOps m A Axis
  size : A → Result (List I64)
  divide : I64 → I64 → m I64
  getindex : A → List I64 → m V
  setindex : A → List I64 → V → m Unit
  view : A → List (List I64) → m A
  raise : {α : Type} → JuliaLean.base.abstractarray.ArrayError → m α
  showDims : List I64 → String

/--
Julia source: base/arraymath.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(A::AbstractArray; dims::D=:) where {D} = _reverse(A, dims)
```
-/
def reverse [Monad m] {A D : Type} (reverseImpl : A → D → m A)
    (a : A) (dims : D) : m A :=
  reverseImpl a dims

/--
Julia source: base/arraymath.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse(A, dims::D) where {D} = reverse!(copymutable(A); dims)
```
-/
def reverseCopy [Monad m] {A D : Type} (copyMutable : A → m A)
    (reverseBang : A → D → m A) (a : A) (dims : D) : m A := do
  let copy ← copyMutable a
  reverseBang copy dims

/--
Julia source: base/arraymath.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse!(A::AbstractArray; dims::D=:) where {D} = _reverse!(A, dims)
```
-/
def reverseBang [Monad m] {A D : Type} (reverseImpl : A → D → m A)
    (a : A) (dims : D) : m A :=
  reverseImpl a dims

/--
Julia source: base/arraymath.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse!(A::AbstractArray{<:Any,N}, ::Colon) where {N} = _reverse!(A, ntuple(identity, Val{N}()))
```
-/
def reverseBangColon [Monad m] {A : Type} (reverseCore : A → List I64 → m A)
    (rank : Nat) (a : A) : m A :=
  reverseCore a (dimensions rank)

/--
Julia source: base/arraymath.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse!(A, dim::Integer) = _reverse!(A, (Int(dim),))
```
-/
def reverseBangInteger [Monad m] {A D : Type} (reverseCore : A → List I64 → m A)
    (toInt : D → m I64) (a : A) (dim : D) : m A := do
  let dimension ← toInt dim
  reverseCore a [dimension]

/--
Julia source: base/arraymath.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse!(A, dims::NTuple{M,Integer}) where {M} = _reverse!(A, Int.(dims))
```
-/
def reverseBangIntegerTuple [Monad m] {A D : Type} (reverseCore : A → List I64 → m A)
    (toInt : D → m I64) (a : A) (dims : List D) : m A := do
  let dimensions ← dims.mapM toInt
  reverseCore a dimensions

/--
Julia source: base/arraymath.jl:107-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reverse!(A::AbstractArray{<:Any,N}, dims::NTuple{M,Int}) where {N,M}
    dims === () && return A # nothing to reverse
    dimrev = ntuple(k -> k in dims, Val{N}()) # boolean tuple indicating reversed dims

    if N < M || M != sum(dimrev)
        throw(ArgumentError("invalid dimensions $dims in reverse!"))
    end

    # swapping loop only needs to traverse ≈half of the array
    halfsz = ntuple(k -> k == dims[1] ? size(A,k) ÷ 2 : size(A,k), Val{N}())

    last1 = ntuple(k -> lastindex(A,k)+firstindex(A,k), Val{N}()) # offset for reversed index
    for i in CartesianIndices(ntuple(k -> firstindex(A,k):firstindex(A,k)-1+@inbounds(halfsz[k]), Val{N}()))
        iₜ = Tuple(i)
        iᵣ = CartesianIndex(ifelse.(dimrev, last1 .- iₜ, iₜ))
        @inbounds A[iᵣ], A[i] = A[i], A[iᵣ]
    end
    if M > 1 && isodd(size(A, dims[1]))
        # middle slice for odd dimensions must be recursively flipped
        mid = firstindex(A, dims[1]) + (size(A, dims[1]) ÷ 2)
        midslice = CartesianIndices(ntuple(k -> k == dims[1] ? (mid:mid) : (firstindex(A,k):lastindex(A,k)), Val{N}()))
        _reverse!(view(A, midslice), dims[2:end])
    end
    return A
end
```
-/

def reverseBangCore [Monad m] {A V Axis : Type} (ops : ReverseOps m A V Axis)
    (rank : Nat) (a : A) : List I64 → m A
  | [] => pure a
  | dimensionsList@(leading :: remaining) => do
      let reversed := (dimensions rank).map fun dimension => dimensionsList.contains dimension
      if rank < dimensionsList.length || dimensionsList.length != reversed.count true then
        ops.raise (.julia (.argumentError
          ("invalid dimensions " ++ ops.showDims dimensionsList ++ " in reverse!")))
      else
        let halfSizes ← (dimensions rank).mapM fun dimension => do
          let extent ← sizeAt ops.index.liftResult ops.size a dimension
          if dimension == leading then ops.divide extent (JuliaLean.base.abstractarray.int 2)
          else pure extent
        let offsets ← (dimensions rank).mapM fun dimension => do
          let last ← lastIndexAt ops.index a dimension
          let first ← firstIndexAt ops.index a dimension
          pure (last + first)
        let halfAxes ← ((dimensions rank).zip halfSizes).mapM fun item => do
          let first ← firstIndexAt ops.index a item.1
          let firstAgain ← firstIndexAt ops.index a item.1
          let upper := firstAgain - JuliaLean.base.abstractarray.int 1 + item.2
          pure (JuliaLean.base.array.intRange first upper)
        let _ ← (cartesianIndices halfAxes).foldlM (fun _ index => do
          let reflected := reflectedIndex reversed offsets index
          let value ← ops.getindex a index
          let reflectedValue ← ops.getindex a reflected
          ops.setindex a reflected value
          ops.setindex a index reflectedValue) ()
        if !remaining.isEmpty then
          let extent ← sizeAt ops.index.liftResult ops.size a leading
          if extent.val % 2 != 0 then
            let first ← firstIndexAt ops.index a leading
            let extentAgain ← sizeAt ops.index.liftResult ops.size a leading
            let middle := first + (← ops.divide extentAgain (JuliaLean.base.abstractarray.int 2))
            let middleAxes ← (dimensions rank).mapM fun dimension => do
              if dimension == leading then
                pure (JuliaLean.base.array.intRange middle middle)
              else do
                let lower ← firstIndexAt ops.index a dimension
                let upper ← lastIndexAt ops.index a dimension
                pure (JuliaLean.base.array.intRange lower upper)
            let middleSlice ← ops.view a middleAxes
            let _ ← reverseBangCore ops rank middleSlice remaining
            pure a
          else pure a
        else pure a
termination_by dims => dims.length

/--
Julia source: base/arraymath.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse!(A::AbstractVector, dim::Tuple{Int}) = _reverse!(A, first(dim))
```
-/
def reverseBangVectorTuple [Monad m] {A : Type} (reverseInteger : A → I64 → m A)
    (a : A) (dims : I64 × Unit) : m A :=
  reverseInteger a dims.1

/-! ## Matrix rotations -/

/-- Abstract matrix access used by the three direct rotation methods. -/
structure MatrixOps (m : Type → Type) (A B V Axis : Type) where
  index : ArrayIndexOps m A Axis
  similar : A → Axis → Axis → m B
  similarSame : A → m B
  values : Axis → List I64
  getindex : A → I64 → I64 → m V
  setindex : B → I64 → I64 → V → m Unit

def firstAxis [Monad m] {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (axis : Axis) : m I64 := ops.liftResult (ops.first axis)

def lastAxis [Monad m] {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (axis : Axis) : m I64 := ops.liftResult (ops.last axis)

/--
Julia source: base/arraymath.jl:154-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rotl90(A::AbstractMatrix)
    ind1, ind2 = axes(A)
    B = similar(A, (ind2,ind1))
    n = first(ind2)+last(ind2)
    for i=axes(A,1), j=ind2
        B[n-j,i] = A[i,j]
    end
    return B
end
```
-/
def rotateLeftMatrix [Monad m] {A B V Axis : Type} (ops : MatrixOps m A B V Axis)
    (a : A) : m B := do
  let axes ← ops.index.liftResult (ops.index.axes a)
  let ind1 ← ops.index.liftResult (JuliaLean.base.abstractarray.tupleGet axes (JuliaLean.base.abstractarray.int 1))
  let ind2 ← ops.index.liftResult (JuliaLean.base.abstractarray.tupleGet axes (JuliaLean.base.abstractarray.int 2))
  let output ← ops.similar a ind2 ind1
  let first ← firstAxis ops.index ind2
  let last ← lastAxis ops.index ind2
  let offset := first + last
  let outer ← axisAt ops.index a (JuliaLean.base.abstractarray.int 1)
  let _ ← (ops.values outer).foldlM (fun _ i =>
    (ops.values ind2).foldlM (fun _ j => do
      let value ← ops.getindex a i j
      ops.setindex output (offset - j) i value) ()) ()
  pure output

/--
Julia source: base/arraymath.jl:182-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rotr90(A::AbstractMatrix)
    ind1, ind2 = axes(A)
    B = similar(A, (ind2,ind1))
    m = first(ind1)+last(ind1)
    for i=ind1, j=axes(A,2)
        B[j,m-i] = A[i,j]
    end
    return B
end
```
-/
def rotateRightMatrix [Monad m] {A B V Axis : Type} (ops : MatrixOps m A B V Axis)
    (a : A) : m B := do
  let axes ← ops.index.liftResult (ops.index.axes a)
  let ind1 ← ops.index.liftResult (JuliaLean.base.abstractarray.tupleGet axes (JuliaLean.base.abstractarray.int 1))
  let ind2 ← ops.index.liftResult (JuliaLean.base.abstractarray.tupleGet axes (JuliaLean.base.abstractarray.int 2))
  let output ← ops.similar a ind2 ind1
  let first ← firstAxis ops.index ind1
  let last ← lastAxis ops.index ind1
  let offset := first + last
  let _ ← (ops.values ind1).foldlM (fun _ i => do
    let inner ← axisAt ops.index a (JuliaLean.base.abstractarray.int 2)
    (ops.values inner).foldlM (fun _ j => do
      let value ← ops.getindex a i j
      ops.setindex output j (offset - i) value) ()) ()
  pure output

/--
Julia source: base/arraymath.jl:209-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rot180(A::AbstractMatrix)
    B = similar(A)
    ind1, ind2 = axes(A,1), axes(A,2)
    m, n = first(ind1)+last(ind1), first(ind2)+last(ind2)
    for j=ind2, i=ind1
        B[m-i,n-j] = A[i,j]
    end
    return B
end
```
-/
def rotateHalfMatrix [Monad m] {A B V Axis : Type} (ops : MatrixOps m A B V Axis)
    (a : A) : m B := do
  let output ← ops.similarSame a
  let ind1 ← axisAt ops.index a (JuliaLean.base.abstractarray.int 1)
  let ind2 ← axisAt ops.index a (JuliaLean.base.abstractarray.int 2)
  let first1 ← firstAxis ops.index ind1
  let last1 ← lastAxis ops.index ind1
  let first2 ← firstAxis ops.index ind2
  let last2 ← lastAxis ops.index ind2
  let offset1 := first1 + last1
  let offset2 := first2 + last2
  let _ ← (ops.values ind2).foldlM (fun _ j =>
    (ops.values ind1).foldlM (fun _ i => do
      let value ← ops.getindex a i j
      ops.setindex output (offset1 - i) (offset2 - j) value) ()) ()
  pure output

/--
Julia source: base/arraymath.jl:252-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rotl90(A::AbstractMatrix, k::Integer)
    k = mod(k, 4)
    k == 1 ? rotl90(A) :
    k == 2 ? rot180(A) :
    k == 3 ? rotr90(A) : copy(A)
end
```
-/
def rotateLeftCounted [Monad m] {A K B : Type} (mod : K → I64 → m K)
    (equals : K → I64 → m Bool) (left half right copy : A → m B)
    (a : A) (k : K) : m B := do
  let count ← mod k (JuliaLean.base.abstractarray.int 4)
  if ← equals count (JuliaLean.base.abstractarray.int 1) then left a
  else if ← equals count (JuliaLean.base.abstractarray.int 2) then half a
  else if ← equals count (JuliaLean.base.abstractarray.int 3) then right a
  else copy a

/--
Julia source: base/arraymath.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rotr90(A::AbstractMatrix, k::Integer) = rotl90(A,-k)
```
-/
def rotateRightCounted [Monad m] {A K B : Type} (negate : K → m K)
    (mod : K → I64 → m K) (equals : K → I64 → m Bool)
    (left half right copy : A → m B) (a : A) (k : K) : m B := do
  let negative ← negate k
  rotateLeftCounted mod equals left half right copy a negative

/--
Julia source: base/arraymath.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rot180(A::AbstractMatrix, k::Integer) = mod(k, 2) == 1 ? rot180(A) : copy(A)
```
-/
def rotateHalfCounted [Monad m] {A K B : Type} (mod : K → I64 → m K)
    (equals : K → I64 → m Bool) (half copy : A → m B) (a : A) (k : K) : m B := do
  let count ← mod k (JuliaLean.base.abstractarray.int 2)
  if ← equals count (JuliaLean.base.abstractarray.int 1) then half a else copy a

end JuliaLean.base.arraymath
