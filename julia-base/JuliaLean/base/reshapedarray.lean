import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.abstractarray
import JuliaLean.base.array
import JuliaLean.base.subarray

/-!
# Model of `base/reshapedarray.jl`

Typed source model for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform.
Array storage, Julia dispatch, and calls into other Base files remain typed interfaces. Index arithmetic
uses the `JInt .i64` operations from `JuliaLean.base.int`.
-/

namespace JuliaLean.base.reshapedarray

open JuliaLean JuliaLean.base.int

abbrev I64 := JInt .i64
inductive ReshapedError where
  | dimensionMismatch
  | errorException
  | argumentError
  | boundsError
  | methodError (name : String)
  | overflowError
  | inexactError (name : String)
  | divideError
  deriving Repr, DecidableEq, Inhabited

abbrev RResult (α : Type) := Except ReshapedError α

inductive IndexStyle where
  | linear
  | cartesian
  deriving Repr, DecidableEq, Inhabited

structure ArrayValue (T : Type) (N : Nat) (Ref : Type) where
  ref : Ref
  dims : Vector I64 N

structure ReshapedArray (T : Type) (N : Nat) (P : Type) (MI : Type) where
  parent : P
  dims : Vector I64 N
  mi : List MI

abbrev ReshapedArrayLF (T : Type) (N : Nat) (P : Type) := ReshapedArray T N P Unit
abbrev ReshapedRange (T : Type) (N : Nat) (A : Type) := ReshapedArray T N A Unit
abbrev ReshapedUnitRange (T : Type) (N : Nat) (A : Type) := ReshapedArray T N A Unit

structure ReshapedArrayIterator (I : Type) (M : Nat) (MI : Type) where
  iter : I
  mi : List MI

structure ReshapedIndex (I : Type) where
  parentindex : I

inductive ShapeArg (I : Type) where
  | integer (value : I)
  | colon
  deriving Repr, DecidableEq

structure OffsetCConvert (T C : Type) where
  byteOffset : I64
  cconvParent : C

inductive StridedSubArrayIndex (I R : Type) where
  | integer (index : I)
  | range (range : R)
  | reshapedRange (range : R)
  deriving Repr

/--
Julia source: base/reshapedarray.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReshapedArray(parent::AbstractArray{T}, dims::NTuple{N,Int}, mi) where {T,N} = ReshapedArray{T,N,typeof(parent),typeof(mi)}(parent, dims, mi)
```
-/
def reshapedArrayConstructor {T : Type} {N : Nat} {P MI : Type}
    (parent : P) (dims : Vector I64 N) (mi : List MI) : ReshapedArray T N P MI :=
  ⟨parent, dims, mi⟩

/--
Julia source: base/reshapedarray.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReshapedArrayIterator(A::ReshapedArray) = _rs_iterator(parent(A), A.mi)
```
-/
def reshapedArrayIteratorConstructor {T : Type} {N M : Nat} {P MI I : Type}
    (parent : ReshapedArray T N P MI → P)
    (rsIterator : P → List MI → I) (array : ReshapedArray T N P MI) : I :=
  rsIterator (parent array) array.mi

/--
Julia source: base/reshapedarray.jl:21-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rs_iterator(P, mi::NTuple{M}) where M
    iter = eachindex(P)
    ReshapedArrayIterator{typeof(iter),M}(iter, mi)
end
```
-/
def rsIterator {P MI I : Type} {M : Nat}
    (eachindex : P → I) (parent : P) (mi : List MI) : ReshapedArrayIterator I M MI :=
  let iter := eachindex parent
  ⟨iter, mi⟩

/--
Julia source: base/reshapedarray.jl:31-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(R::ReshapedArrayIterator, i...)
    item, inext = iterate(R.iter, i...)
    ReshapedIndex(item), inext
end
```
-/
def iterateReshapedIterator {I V S : Type} {M : Nat} {MI : Type}
    (iterate : I → List S → Option (V × S))
    (iterator : ReshapedArrayIterator I M MI) (state : List S) :
    RResult (Option (ReshapedIndex V × S)) :=
  match iterate iterator.iter state with
  | none => .error (.methodError "iterate")
  | some (item, next) => .ok (some (⟨item⟩, next))

/--
Julia source: base/reshapedarray.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(R::ReshapedArrayIterator) = length(R.iter)
```
-/
def reshapedIteratorLength {I : Type} {M : Nat} {MI : Type}
    (length : I → I64) (iterator : ReshapedArrayIterator I M MI) : I64 :=
  length iterator.iter

/--
Julia source: base/reshapedarray.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:ReshapedArrayIterator{I}}) where {I} = @isdefined(I) ? ReshapedIndex{eltype(I)} : Any
```
-/
def reshapedIteratorEltype (isDefined : Type → Bool) (eltype : Type → Type)
    (iteratorType anyType : Type) : Type :=
  if isDefined iteratorType then eltype iteratorType else anyType

/--
Julia source: base/reshapedarray.jl:38-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_dmrsa(dims, len) =
    throw(DimensionMismatch(LazyString("new dimensions ", dims, " must be consistent with array length ", len)))
```
-/
def throw_dmrsa {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {D L α : Type} (_dims : D) (_length : L) : m α :=
  throw .dimensionMismatch

/--
Julia source: base/reshapedarray.jl:43-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function reshape(a::Array{T,M}, dims::NTuple{N,Int}) where {T,N,M}
    len = Core.checked_dims(dims...) # make sure prod(dims) doesn't overflow (and because of the comparison to length(a))
    if len != length(a)
        throw_dmrsa(dims, length(a))
    end
    ref = a.ref
    # or we could use `a = Array{T,N}(undef, ntuple(i->0, Val(N))); a.ref = ref; a.size = dims; return a` here to avoid the eval
    return $(Expr(:new, :(Array{T,N}), :ref, :dims))
end
```
-/
def reshapeArray {T : Type} {M N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → RResult I64)
    (length : ArrayValue T M Ref → RResult I64)
    (array : ArrayValue T M Ref) (dims : Vector I64 N) : RResult (ArrayValue T N Ref) := do
  let product ← checkedDims dims
  let actualLength ← length array
  if product != actualLength then
    let actualLength ← length array
    throw_dmrsa dims actualLength
  else
    .ok ⟨array.ref, dims⟩

/--
Julia source: base/reshapedarray.jl:55-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reshape!(a::Array{T,N}, dims::NTuple{N,Int}) where {T,N}
    len = Core.checked_dims(dims...) # make sure prod(dims) doesn't overflow (and because of the comparison to length(a))
    if len != length(a)
        throw_dmrsa(dims, length(a))
    end
    setfield!(a, :dims, dims)
    return a
end
```
-/
def reshapeBang {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → m I64)
    (length : ArrayValue T N Ref → m I64)
    (setfield : ArrayValue T N Ref → Vector I64 N → m Unit)
    (array : ArrayValue T N Ref) (dims : Vector I64 N) : m (ArrayValue T N Ref) := do
  let product ← checkedDims dims
  let actualLength ← length array
  if product != actualLength then
    let actualLength ← length array
    throw_dmrsa dims actualLength
  else do
    setfield array dims
    pure array

/--
Julia source: base/reshapedarray.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::IntOrInd...) = reshape(parent, dims)
```
-/
def reshapeIntOrInd {P D R : Type}
    (reshapeTuple : P → List D → R) (parent : P) (dims : List D) : R :=
  reshapeTuple parent dims

/--
Julia source: base/reshapedarray.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, shp::Tuple{Union{Integer,AbstractOneTo}, Vararg{Union{Integer,AbstractOneTo}}}) = reshape(parent, to_shape(shp))
```
-/
def reshapeShapeTuple {P D S R : Type}
    (toShape : D → RResult S) (reshape : P → S → RResult R)
    (parent : P) (shape : D) : RResult R := do
  let dims ← toShape shape
  reshape parent dims

/--
Julia source: base/reshapedarray.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, shp::Tuple{Union{Integer,OneTo}, Vararg{Union{Integer,OneTo}}}) = reshape(parent, to_shape(shp))
```
-/
def reshapeLegacyShapeTuple {P D S R : Type}
    (toShape : D → RResult S) (reshape : P → S → RResult R)
    (parent : P) (shape : D) : RResult R := do
  let dims ← toShape shape
  reshape parent dims

/--
Julia source: base/reshapedarray.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Tuple{Integer, Vararg{Integer}}) = reshape(parent, map(Int, dims))
```
-/
def reshapeIntegerTuple {P D R : Type}
    (convertInt : D → RResult I64) (reshape : P → List I64 → RResult R)
    (parent : P) (dims : List D) : RResult R := do
  let converted ← dims.mapM convertInt
  reshape parent converted

/--
Julia source: base/reshapedarray.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Dims)        = _reshape(parent, dims)
```
-/
def reshapeDims {P D R : Type}
    (reshapeInternal : P → D → R) (parent : P) (dims : D) : R :=
  reshapeInternal parent dims

/--
Julia source: base/reshapedarray.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractVector, ::Colon) = parent
```
-/
def reshapeVectorColon {P : Type} (parent : P) : P := parent

/--
Julia source: base/reshapedarray.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractVector, ::Tuple{Colon}) = parent
```
-/
def reshapeVectorColonTuple {P : Type} (parent : P) : P := parent

/--
Julia source: base/reshapedarray.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Int...) = reshape(parent, dims)
```
-/
def reshapeIntVarargs {P D R : Type}
    (reshapeTuple : P → List D → R) (parent : P) (dims : List D) : R :=
  reshapeTuple parent dims

/--
Julia source: base/reshapedarray.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Integer...) = reshape(parent, dims)
```
-/
def reshapeIntegerVarargs {P D R : Type}
    (reshapeTuple : P → List D → R) (parent : P) (dims : List D) : R :=
  reshapeTuple parent dims

/--
Julia source: base/reshapedarray.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Union{Integer,Colon}...) = reshape(parent, dims)
```
-/
def reshapeIntegerColonVarargs {P D R : Type}
    (reshapeTuple : P → List D → R) (parent : P) (dims : List D) : R :=
  reshapeTuple parent dims

/--
Julia source: base/reshapedarray.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray, dims::Tuple{Vararg{Union{Integer,Colon}}}) = reshape(parent, _reshape_uncolon(parent, dims))
```
-/
def reshapeColonTuple {P D S R : Type}
    (reshapeTuple : P → S → R) (reshapeUncolon : P → D → S)
    (parent : P) (dims : D) : R :=
  reshapeTuple parent (reshapeUncolon parent dims)

/--
Julia source: base/reshapedarray.jl:138-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw1(dims) = throw(DimensionMismatch(LazyString("new dimensions ", dims,
        " may have at most one omitted dimension specified by `Colon()`")))
```
-/
def throw1 {D α : Type} (_dims : D) : RResult α :=
  .error .dimensionMismatch

/--
Julia source: base/reshapedarray.jl:140-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw2(lenA, dims) = throw(DimensionMismatch(string("array size ", lenA,
    " must be divisible by the product of the new dimensions ", dims)))
```
-/
def throw2 {L D α : Type} (_length : L) (_dims : D) : RResult α :=
  .error .dimensionMismatch

/--
Julia source: base/reshapedarray.jl:143-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _reshape_uncolon(A, _dims::Tuple{Vararg{Union{Integer, Colon}}})
    # promote the dims to `Int` at least
    dims = map(x -> x isa Colon ? x : promote_type(typeof(x), Int)(x), _dims)
    pre = _before_colon(dims...)
    post = _after_colon(dims...)
    _any_colon(post...) && throw1(dims)
    len = length(A)
    _reshape_uncolon_computesize(len, dims, pre, post)
end
```
-/
def reshapeUncolon {A D S L : Type}
    (isColon : D → Bool) (promoteInt : D → RResult D)
    (beforeColon afterColon : List D → RResult (List D))
    (anyColon : List D → Bool) (length : A → RResult L)
    (compute : L → List D → List D → List D → RResult S)
    (array : A) (rawDims : List D) : RResult S := do
  let dims ← rawDims.mapM fun dim =>
    if isColon dim then .ok dim else promoteInt dim
  let pre ← beforeColon dims
  let post ← afterColon dims
  if anyColon post then
    throw1 dims
  else do
    let len ← length array
    compute len dims pre post

/--
Julia source: base/reshapedarray.jl:152-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _reshape_uncolon_computesize(len::Int, dims, pre::Tuple{Vararg{Int}}, post::Tuple{Vararg{Int}})
    sz = if iszero(len)
        0
    else
        let pr = Core.checked_dims(pre..., post...)  # safe product
            quo = _reshape_uncolon_computesize_nonempty(len, dims, pr)
            convert(Int, quo)
        end
    end
    (pre..., sz, post...)
end
```
-/
def reshapeComputeSizeInt {D : Type}
    (checkedDims : List I64 → RResult I64)
    (computeNonempty : I64 → D → I64 → RResult I64)
    (convertInt : I64 → RResult I64)
    (len : I64) (dims : D) (pre post : List I64) : RResult (List I64) := do
  let size ← if len.val == 0 then .ok (JInt.lit .i64 0) else do
    let product ← checkedDims (pre ++ post)
    let quotient ← computeNonempty len dims product
    convertInt quotient
  .ok (pre ++ [size] ++ post)

/--
Julia source: base/reshapedarray.jl:163-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _reshape_uncolon_computesize(len, dims, pre, post)
    pr = prod((pre..., post...))
    sz = if iszero(len)
        promote(len, pr)[1] # zero of the correct type
    else
        _reshape_uncolon_computesize_nonempty(len, dims, pr)
    end
    (pre..., sz, post...)
end
```
-/
def reshapeComputeSizeGeneric {D N : Type}
    (product : List N → RResult N) (iszero : N → RResult Bool)
    (promote : N → N → RResult (N × N))
    (computeNonempty : N → D → N → RResult N)
    (len : N) (dims : D) (pre post : List N) : RResult (List N) := do
  let pr ← product (pre ++ post)
  let zero ← iszero len
  let size ← if zero then do
      let pair ← promote len pr
      .ok pair.1
    else
      computeNonempty len dims pr
  .ok (pre ++ [size] ++ post)

/--
Julia source: base/reshapedarray.jl:172-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _reshape_uncolon_computesize_nonempty(len, dims, pr)
    iszero(pr) && throw2(len, dims)
    (quo, rem) = divrem(len, pr)
    iszero(rem) || throw2(len, dims)
    quo
end
```
-/
def reshapeComputeNonempty {N D : Type}
    (iszero : N → RResult Bool) (divrem : N → N → RResult (N × N))
    (len : N) (dims : D) (product : N) : RResult N := do
  if ← iszero product then
    throw2 len dims
  let (quotient, remainder) ← divrem len product
  if !(← iszero remainder) then
    throw2 len dims
  .ok quotient

/--
Julia source: base/reshapedarray.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _any_colon() = false
```
-/
def anyColonNone : Bool := false

/--
Julia source: base/reshapedarray.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _any_colon(dim::Colon, tail...) = true
```
-/
def anyColonHeadColon {D : Type} (_tail : List D) : Bool := true

/--
Julia source: base/reshapedarray.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _any_colon(dim::Any, tail...) = _any_colon(tail...)
```
-/
def anyColonHeadAny {D : Type}
    (anyColon : List D → Bool) (_head : D) (tail : List D) : Bool :=
  anyColon tail

/--
Julia source: base/reshapedarray.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _before_colon(dim::Any, tail...) = (dim, _before_colon(tail...)...)
```
-/
def beforeColonHeadAny {D : Type}
    (beforeColon : List D → List D) (head : D) (tail : List D) : List D :=
  head :: beforeColon tail

/--
Julia source: base/reshapedarray.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _before_colon(dim::Colon, tail...) = ()
```
-/
def beforeColonHeadColon {D : Type} (_tail : List D) : List D := []

/--
Julia source: base/reshapedarray.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _after_colon(dim::Any, tail...) =  _after_colon(tail...)
```
-/
def afterColonHeadAny {D : Type}
    (afterColon : List D → List D) (_head : D) (tail : List D) : List D :=
  afterColon tail

/--
Julia source: base/reshapedarray.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _after_colon(dim::Colon, tail...) = tail
```
-/
def afterColonHeadColon {D : Type} (tail : List D) : List D := tail

/--
Julia source: base/reshapedarray.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(parent::AbstractArray{T,N}, ndims::Val{N}) where {T,N} = parent
```
-/
def reshapeValEqual {T : Type} {N : Nat} {P : Type}
    (parent : ReshapedArray T N P Unit) : ReshapedArray T N P Unit := parent

/--
Julia source: base/reshapedarray.jl:187-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reshape(parent::AbstractArray, ndims::Val{N}) where N
    reshape(parent, rdims(Val(N), axes(parent)))
end
```
-/
def reshapeValRank {P AX D R : Type}
    (axes : P → RResult AX) (rdims : Nat → AX → RResult D)
    (reshape : P → D → RResult R) (parent : P) (rank : Nat) : RResult R := do
  let parentAxes ← axes parent
  let dims ← rdims rank parentAxes
  reshape parent dims

/--
Julia source: base/reshapedarray.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims_trailing(l, inds...) = length(l) * rdims_trailing(inds...)
```
-/
def rdimsTrailingMany {A N : Type}
    (length : A → RResult N) (multiply : N → N → RResult N)
    (recurse : List A → RResult N)
    (first second : A) (rest : List A) : RResult N := do
  let firstLength ← length first
  let tailLength ← recurse (second :: rest)
  multiply firstLength tailLength

/--
Julia source: base/reshapedarray.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims_trailing(l) = length(l)
```
-/
def rdimsTrailingSingle {A N : Type}
    (length : A → RResult N) (last : A) : RResult N :=
  length last

/--
Julia source: base/reshapedarray.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Val{N}, inds::Tuple) where {N} = rdims(ntuple(Returns(OneTo(1)), Val(N)), inds)
```
-/
def rdimsVal {AX I R : Type}
    (oneToOne : RResult AX) (ntuple : Nat → AX → RResult (List AX))
    (rdims : List AX → I → RResult R) (rank : Nat) (indices : I) : RResult R := do
  let one ← oneToOne
  let out ← ntuple rank one
  rdims out indices

/--
Julia source: base/reshapedarray.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{}, inds::Tuple{}) = () # N == 0, M == 0
```
-/
def rdimsEmptyEmpty {A B : Type} (_out : List A) (_inds : List B) : List B := []

/--
Julia source: base/reshapedarray.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{}, inds::Tuple{Any}) = ()
```
-/
def rdimsEmptyOne {A B : Type} (_out : List A) (_inds : List B) : List B := []

/--
Julia source: base/reshapedarray.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{}, inds::NTuple{M,Any}) where {M} = ()
```
-/
def rdimsEmptyMany {A B : Type} (_out : List A) (_inds : List B) : List B := []

/--
Julia source: base/reshapedarray.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{Any}, inds::Tuple{}) = out # N == 1, M == 0
```
-/
def rdimsSingletonEmpty {A B : Type} (out : List A) (_inds : List B) : List A := out

/--
Julia source: base/reshapedarray.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::NTuple{N,Any}, inds::Tuple{}) where {N} = out # N > 1, M == 0
```
-/
def rdimsManyEmpty {A B : Type} (out : List A) (_inds : List B) : List A := out

/--
Julia source: base/reshapedarray.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{Any}, inds::Tuple{Any}) = inds # N == 1, M == 1
```
-/
def rdimsSingletonOne {A B : Type} (_out : List A) (inds : List B) : List B := inds

/--
Julia source: base/reshapedarray.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::Tuple{Any}, inds::NTuple{M,Any}) where {M} = (oneto(rdims_trailing(inds...)),) # N == 1, M > 1
```
-/
def rdimsSingletonMany {A B N : Type}
    (trailing : List B → RResult N) (oneto : N → RResult A)
    (_out : List A) (first second : B) (rest : List B) : RResult (List A) := do
  let product ← trailing (second :: rest)
  let axis ← oneto product
  .ok [axis]

/--
Julia source: base/reshapedarray.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::NTuple{N,Any}, inds::NTuple{N,Any}) where {N} = inds # N > 1, M == N
```
-/
def rdimsEqualRank {A B : Type} (out : List A) (inds : List B) : List B := inds

/--
Julia source: base/reshapedarray.jl:205-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rdims(out::NTuple{N,Any}, inds::NTuple{M,Any}) where {N,M} = (first(inds), rdims(tail(out), tail(inds))...) # N > 1, M > 1, M != N
```
-/
def rdimsRecursive {A B : Type}
    (first : List B → RResult B)
    (tailOut : List A → RResult (List A)) (tailIn : List B → RResult (List B))
    (recurse : List A → List B → RResult (List B))
    (outFirst : A) (outTail : List A) (inFirst : B) (inTail : List B) : RResult (List B) := do
  let head ← first (inFirst :: inTail)
  let outputTail ← tailOut (outFirst :: outTail)
  let inputTail ← tailIn (inFirst :: inTail)
  let rest ← recurse outputTail inputTail
  .ok (head :: rest)

/--
Julia source: base/reshapedarray.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reshape(parent::Vector, dims::Dims{1}) = parent
```
-/
def reshapeVectorArrayIdentity {T N : Type} (parent : T) (_dims : N) : T := parent

/--
Julia source: base/reshapedarray.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reshape(parent::Array, dims::Dims{1}) = reshape(parent, dims)
```
-/
def reshapeDenseVector {P D R : Type}
    (reshape : P → D → R) (parent : P) (dims : D) : R :=
  reshape parent dims

/--
Julia source: base/reshapedarray.jl:211-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reshape(parent::Array, dims::Dims) = reshape(parent, dims)
```
-/
def reshapeDenseArray {P D R : Type}
    (reshape : P → D → R) (parent : P) (dims : D) : R :=
  reshape parent dims

/--
Julia source: base/reshapedarray.jl:214-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reshape(v::AbstractVector, dims::Dims{1})
    require_one_based_indexing(v)
    len = dims[1]
    len == length(v) || _throw_dmrs(length(v), "length", len)
    v
end
```
-/
def reshapeAbstractVector {P : Type}
    (requireOneBased : P → RResult Unit)
    (firstDim : Vector I64 1 → RResult I64)
    (length : P → RResult I64)
    (throwDmrs : I64 → String → I64 → RResult P)
    (vector : P) (dims : Vector I64 1) : RResult P := do
  requireOneBased vector
  let requested ← firstDim dims
  let actual ← length vector
  if requested != actual then
    let actual ← length vector
    throwDmrs actual "length" requested
  else
    .ok vector

/--
Julia source: base/reshapedarray.jl:221-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reshape(parent::AbstractArray, dims::Dims)
    n = length(parent)
    Core.checked_dims(dims...) == n || _throw_dmrs(n, "size", dims)
    __reshape((parent, IndexStyle(parent)), dims)
end
```
-/
def reshapeAbstractArray {P D S R : Type}
    (length : P → RResult I64) (checkedDims : D → RResult I64)
    (throwDmrs : I64 → String → D → RResult R)
    (indexStyle : P → RResult S)
    (construct : P × S → D → RResult R)
    (parent : P) (dims : D) : RResult R := do
  let n ← length parent
  let product ← checkedDims dims
  if product != n then
    throwDmrs n "size" dims
  else do
    let style ← indexStyle parent
    construct (parent, style) dims

/--
Julia source: base/reshapedarray.jl:227-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _throw_dmrs(n, str, dims)
    throw(DimensionMismatch("parent has $n elements, which is incompatible with $str $dims ($(prod(dims)) elements)"))
end
```
-/
def throwDmrs {D α : Type} (product : D → RResult I64)
    (_length : I64) (_kind : String) (dims : D) : RResult α := do
  let _ ← product dims
  .error .dimensionMismatch

/--
Julia source: base/reshapedarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reshape(v::ReshapedArray{<:Any,1}, dims::Dims{1}) = _reshape(v.parent, dims)
```
-/
def reshapeReshapedVector {T : Type} {P R : Type}
    (reshape : P → List I64 → RResult R)
    (array : ReshapedArray T 1 P Unit) (dims : List I64) : RResult R :=
  reshape array.parent dims

/--
Julia source: base/reshapedarray.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reshape(R::ReshapedArray, dims::Dims) = _reshape(R.parent, dims)
```
-/
def reshapeReshapedArray {T : Type} {N : Nat} {P R : Type} {MI : Type}
    (reshape : P → List I64 → RResult R)
    (array : ReshapedArray T N P MI) (dims : List I64) : RResult R :=
  reshape array.parent dims

/--
Julia source: base/reshapedarray.jl:235-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __reshape(p::Tuple{AbstractArray,IndexStyle}, dims::Dims)
    parent = p[1]
    szs = front(size(parent))
    szs1 = map(s -> max(1, Int(s)), szs) # for resizing empty arrays
    mi = map(SignedMultiplicativeInverse, szs1)
    ReshapedArray(parent, dims, mi)
end
```
-/
def constructReshapedCartesian {T : Type} {N : Nat} {P A S MI : Type}
    (size : P → RResult (List S)) (front : List S → List S)
    (toInt : S → RResult I64) (makeInverse : I64 → MI)
    (pair : P × A) (dims : Vector I64 N) : RResult (ReshapedArray T N P MI) := do
  let parent := pair.1
  let shape ← size parent
  let leading := front shape
  let adjusted ← leading.mapM fun value => do
    let n ← toInt value
    .ok (if n.val < 1 then JInt.lit .i64 1 else n)
  let inverses := adjusted.map makeInverse
  .ok (reshapedArrayConstructor parent dims inverses)

/--
Julia source: base/reshapedarray.jl:243-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __reshape(p::Tuple{AbstractArray{<:Any,0},IndexCartesian}, dims::Dims)
    parent = p[1]
    ReshapedArray(parent, dims, ())
end
```
-/
def constructReshapedCartesianZero {T : Type} {N : Nat} {P A : Type}
    (pair : P × A) (dims : Vector I64 N) : RResult (ReshapedArray T N P Unit) :=
  .ok (reshapedArrayConstructor pair.1 dims [])

/--
Julia source: base/reshapedarray.jl:248-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __reshape(p::Tuple{AbstractArray,IndexLinear}, dims::Dims)
    parent = p[1]
    ReshapedArray(parent, dims, ())
end
```
-/
def constructReshapedLinear {T : Type} {N : Nat} {P A : Type}
    (pair : P × A) (dims : Vector I64 N) : RResult (ReshapedArray T N P Unit) :=
  .ok (reshapedArrayConstructor pair.1 dims [])

/--
Julia source: base/reshapedarray.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(A::ReshapedArray) = A.dims
```
-/
def reshapedSize {T : Type} {N : Nat} {P MI : Type}
    (array : ReshapedArray T N P MI) : Vector I64 N := array.dims

/--
Julia source: base/reshapedarray.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(A::ReshapedArray) = length(parent(A))
```
-/
def reshapedLength {T : Type} {N : Nat} {P MI : Type}
    (length : P → RResult I64) (array : ReshapedArray T N P MI) : RResult I64 :=
  length array.parent

/--
Julia source: base/reshapedarray.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(A::ReshapedArray, eltype::Type, dims::Dims) = similar(parent(A), eltype, dims)
```
-/
def reshapedSimilar {T : Type} {N : Nat} {P MI E D R : Type}
    (similar : P → E → D → RResult R)
    (array : ReshapedArray T N P MI) (elementType : E) (dims : D) : RResult R :=
  similar array.parent elementType dims

/--
Julia source: base/reshapedarray.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:ReshapedArray{T,N,P}} = similar(P, dims)
```
-/
def reshapedSimilarType {TA P D R : Type}
    (similar : P → D → RResult R) (parentType : TA → P)
    (typeValue : TA) (dims : D) : RResult R :=
  similar (parentType typeValue) dims

/--
Julia source: base/reshapedarray.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:ReshapedArrayLF}) = IndexLinear()
```
-/
def reshapedIndexStyle {T : Type} {N : Nat} {P : Type} (_type : ReshapedArrayLF T N P) : IndexStyle :=
  .linear

/--
Julia source: base/reshapedarray.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(A::ReshapedArray) = A.parent
```
-/
def reshapedParent {T : Type} {N : Nat} {P MI : Type}
    (array : ReshapedArray T N P MI) : P := array.parent

/--
Julia source: base/reshapedarray.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentindices(A::ReshapedArray) = map(oneto, size(parent(A)))
```
-/
def reshapedParentIndices {T : Type} {N : Nat} {P MI AX : Type}
    (size : P → RResult (List I64)) (oneto : I64 → RResult AX)
    (array : ReshapedArray T N P MI) : RResult (List AX) := do
  let parentSize ← size array.parent
  parentSize.mapM oneto

/--
Julia source: base/reshapedarray.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(::Type{<:ReshapedArray{<:Any,<:Any,P}}) where {P} = elsize(P)
```
-/
def reshapedElsize {T : Type} {N : Nat} {P MI : Type}
    (elsize : P → RResult I64) (_parentType : P) : RResult I64 :=
  elsize _parentType

/--
Julia source: base/reshapedarray.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(A::ReshapedArray) = typeof(A)(unaliascopy(A.parent), A.dims, A.mi)
```
-/
def reshapedUnaliascopy {T : Type} {N : Nat} {P MI R : Type}
    (unaliascopy : P → RResult P) (construct : P → Vector I64 N → List MI → R)
    (array : ReshapedArray T N P MI) : RResult R := do
  let parentCopy ← unaliascopy array.parent
  .ok (construct parentCopy array.dims array.mi)

/--
Julia source: base/reshapedarray.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(A::ReshapedArray) = dataids(A.parent)
```
-/
def reshapedDataids {T : Type} {N : Nat} {P MI D : Type}
    (dataids : P → RResult D) (array : ReshapedArray T N P MI) : RResult D :=
  dataids array.parent

/--
Julia source: base/reshapedarray.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mightalias(A::ReshapedArray, B::ReshapedArray) = mightalias(parent(A), parent(B))
```
-/
def mightAliasReshaped {T U : Type} {N M : Nat} {P Q MI MJ : Type}
    (mightalias : P → Q → Bool)
    (left : ReshapedArray T N P MI) (right : ReshapedArray U M Q MJ) : Bool :=
  mightalias (reshapedParent left) (reshapedParent right)

/--
Julia source: base/reshapedarray.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mightalias(A::ReshapedArray, B::SubArray) = mightalias(parent(A), B)
```
-/
def mightAliasReshapedSub {T : Type} {N : Nat} {P MI S : Type}
    (mightalias : P → S → Bool)
    (left : ReshapedArray T N P MI) (right : S) : Bool :=
  mightalias (reshapedParent left) right

/--
Julia source: base/reshapedarray.jl:268-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mightalias(A::SubArray, B::ReshapedArray) = mightalias(A, parent(B))
```
-/
def mightAliasSubReshaped {T : Type} {N : Nat} {P MI S : Type}
    (mightalias : S → P → Bool)
    (left : S) (right : ReshapedArray T N P MI) : Bool :=
  mightalias left (reshapedParent right)

/--
Julia source: base/reshapedarray.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ind2sub_rs(ax, ::Tuple{}, i::Int) = (i,)
```
-/
def ind2subRsEmpty {AX : Type} (_axes : List AX) (index : I64) : List I64 :=
  [index]

/--
Julia source: base/reshapedarray.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ind2sub_rs(ax, szs, i) = _ind2sub_rs(ax, szs, i - 1)
```
-/
def ind2subRs {AX MI : Type}
    (aux : List AX → List MI → I64 → RResult (List I64))
    (axes : List AX) (multipliers : List MI) (index : I64) : RResult (List I64) :=
  aux axes multipliers (sub_int index (JInt.lit .i64 1))

/--
Julia source: base/reshapedarray.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _ind2sub_rs(ax, ::Tuple{}, ind) = (ind + first(ax[end]),)
```
-/
def ind2subRsAuxEmpty {AX I : Type}
    (lastAxis : List AX → RResult AX) (first : AX → RResult I)
    (add : I → I64 → RResult I)
    (axes : List AX) (index : I64) : RResult (List I) := do
  let axis ← lastAxis axes
  let origin ← first axis
  let coordinate ← add origin index
  .ok [coordinate]

/--
Julia source: base/reshapedarray.jl:273-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _ind2sub_rs(ax, szs, ind)
    d, r = divrem(ind, szs[1])
    (r + first(ax[1]), _ind2sub_rs(tail(ax), tail(szs), d)...)
end
```
-/
def ind2subRsAux {AX MI I : Type}
    (divrem : I64 → MI → RResult (I64 × I64))
    (firstAxis : List AX → RResult AX) (first : AX → RResult I)
    (add : I64 → I → RResult I)
    (tailAxes : List AX → RResult (List AX))
    (lastAxis : List AX → RResult AX)
    (firstLast : AX → RResult I)
    (addLast : I → I64 → RResult I)
    (axes : List AX) (size : MI) (tailSizes : List MI) (index : I64) : RResult (List I) := do
  let (quotient, remainder) ← divrem index size
  let axis ← firstAxis axes
  let origin ← first axis
  let coordinate ← add remainder origin
  let remainingAxes ← tailAxes axes
  let tailCoordinates ← match tailSizes with
    | [] => ind2subRsAuxEmpty (AX := AX) (I := I) lastAxis firstLast addLast remainingAxes quotient
    | nextSize :: rest =>
        (ind2subRsAux (AX := AX) (MI := MI) (I := I) divrem firstAxis first add tailAxes
          lastAxis firstLast addLast remainingAxes nextSize rest quotient)
  .ok (coordinate :: tailCoordinates)
termination_by tailSizes.length

def ind2subRsAuxDispatch {AX MI I : Type}
    (divrem : I64 → MI → RResult (I64 × I64))
    (firstAxis : List AX → RResult AX) (first : AX → RResult I)
    (add : I64 → I → RResult I)
    (tailAxes : List AX → RResult (List AX))
    (lastAxis : List AX → RResult AX)
    (firstLast : AX → RResult I) (addLast : I → I64 → RResult I)
    (axes : List AX) (sizes : List MI) (index : I64) : RResult (List I) :=
  match sizes with
  | [] => ind2subRsAuxEmpty lastAxis firstLast addLast axes index
  | size :: tail => ind2subRsAux divrem firstAxis first add tailAxes
      lastAxis firstLast addLast axes size tail index

/--
Julia source: base/reshapedarray.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offset_if_vec(i::Integer, axs::Tuple{<:AbstractUnitRange}) = i + first(axs[1]) - 1
```
-/
def offsetIfVec {I AX O : Type}
    (firstAxis : AX → RResult I) (add : I → I → RResult O)
    (subOne : O → RResult O)
    (index : I) (axis : AX) : RResult O := do
  let origin ← firstAxis axis
  let shifted ← add index origin
  subOne shifted

/--
Julia source: base/reshapedarray.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
offset_if_vec(i::Integer, axs::Tuple) = i
```
-/
def offsetIfGeneral {I AX : Type} (index : I) (_axes : List AX) : I := index

/--
Julia source: base/reshapedarray.jl:280-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function isassigned(A::ReshapedArrayLF, index::Int)
    @boundscheck checkbounds(Bool, A, index) || return false
    indexparent = index - firstindex(A) + firstindex(parent(A))
    @inbounds ret = isassigned(parent(A), indexparent)
    ret
end
```
-/
def isassignedReshapedLinear {T : Type} {N : Nat} {P : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArrayLF T N P → I64 → Bool)
    (firstArray : ReshapedArrayLF T N P → RResult I64)
    (firstParent : P → RResult I64) (isassigned : P → I64 → RResult Bool)
    (array : ReshapedArrayLF T N P) (index : I64) : RResult Bool := do
  if boundsChecking && !(checkbounds array index) then
    .ok false
  else do
    let arrayFirst ← firstArray array
    let parentArray := reshapedParent array
    let parentFirst ← firstParent (reshapedParent array)
    let indexParent := add_int (sub_int index arrayFirst) parentFirst
    isassigned parentArray indexParent

/--
Julia source: base/reshapedarray.jl:286-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function isassigned(A::ReshapedArray{T,N}, indices::Vararg{Int, N}) where {T,N}
    @boundscheck checkbounds(Bool, A, indices...) || return false
    axp = axes(A.parent)
    i = offset_if_vec(_sub2ind(size(A), indices...), axp)
    I = ind2sub_rs(axp, A.mi, i)
    @inbounds isassigned(A.parent, I...)
end
```
-/
def isassignedReshapedCartesian {T : Type} {N : Nat} {P AX MI : Type}
    (boundsChecking : Bool)
    (checkbounds : ReshapedArray T N P MI → List I64 → Bool)
    (axes : P → RResult (List AX))
    (sub2ind : Vector I64 N → List I64 → RResult I64)
    (offset : I64 → List AX → RResult I64)
    (ind2sub : List AX → List MI → I64 → RResult (List I64))
    (isassigned : P → List I64 → RResult Bool)
    (array : ReshapedArray T N P MI) (indices : List I64) : RResult Bool := do
  if boundsChecking && !(checkbounds array indices) then
    .ok false
  else do
    let parentAxes ← axes array.parent
    let linear ← sub2ind (reshapedSize array) indices
    let adjusted ← offset linear parentAxes
    let parentIndices ← ind2sub parentAxes array.mi adjusted
    isassigned array.parent parentIndices

/--
Julia source: base/reshapedarray.jl:294-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(A::ReshapedArrayLF, index::Int)
    @boundscheck checkbounds(A, index)
    indexparent = index - firstindex(A) + firstindex(parent(A))
    @inbounds ret = parent(A)[indexparent]
    ret
end
```
-/
def getindexReshapedLinear {T : Type} {N : Nat} {P E : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArrayLF T N P → I64 → RResult Unit)
    (firstArray : ReshapedArrayLF T N P → RResult I64)
    (firstParent : P → RResult I64) (getindex : P → I64 → RResult E)
    (array : ReshapedArrayLF T N P) (index : I64) : RResult E := do
  if boundsChecking then checkbounds array index
  let arrayFirst ← firstArray array
  let parentArray := reshapedParent array
  let parentFirst ← firstParent (reshapedParent array)
  let indexParent := add_int (sub_int index arrayFirst) parentFirst
  getindex parentArray indexParent

/--
Julia source: base/reshapedarray.jl:300-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(A::ReshapedArray{T,N}, indices::Vararg{Int,N}) where {T,N}
    @boundscheck checkbounds(A, indices...)
    _unsafe_getindex(A, indices...)
end
```
-/
def getindexReshapedCartesian {T : Type} {N : Nat} {P MI E : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArray T N P MI → List I64 → RResult Unit)
    (unsafeGet : ReshapedArray T N P MI → List I64 → RResult E)
    (array : ReshapedArray T N P MI) (indices : List I64) : RResult E := do
  if boundsChecking then checkbounds array indices
  unsafeGet array indices

/--
Julia source: base/reshapedarray.jl:304-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(A::ReshapedArray, index::ReshapedIndex)
    @boundscheck checkbounds(parent(A), index.parentindex)
    @inbounds ret = parent(A)[index.parentindex]
    ret
end
```
-/
def getindexReshapedIndex {T : Type} {N : Nat} {P I E : Type} {MI : Type}
    (boundsChecking : Bool) (checkbounds : P → I → RResult Unit)
    (getindex : P → I → RResult E)
    (array : ReshapedArray T N P MI) (index : ReshapedIndex I) : RResult E := do
  if boundsChecking then checkbounds (reshapedParent array) index.parentindex
  getindex (reshapedParent array) index.parentindex

/--
Julia source: base/reshapedarray.jl:310-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_getindex(A::ReshapedArray{T,N}, indices::Vararg{Int,N}) where {T,N}
    axp = axes(A.parent)
    i = offset_if_vec(_sub2ind(size(A), indices...), axp)
    I = ind2sub_rs(axp, A.mi, i)
    _unsafe_getindex_rs(parent(A), I)
end
```
-/
def unsafeGetindexReshaped {T : Type} {N : Nat} {P AX MI E : Type}
    (axes : P → RResult (List AX))
    (sub2ind : Vector I64 N → List I64 → RResult I64)
    (offset : I64 → List AX → RResult I64)
    (ind2sub : List AX → List MI → I64 → RResult (List I64))
    (unsafeGet : P → List I64 → RResult E)
    (array : ReshapedArray T N P MI) (indices : List I64) : RResult E := do
  let parentAxes ← axes array.parent
  let linear ← sub2ind (reshapedSize array) indices
  let adjusted ← offset linear parentAxes
  let parentIndices ← ind2sub parentAxes array.mi adjusted
  unsafeGet (reshapedParent array) parentIndices

/--
Julia source: base/reshapedarray.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _unsafe_getindex_rs(A, i::Integer) = (@inbounds ret = A[i]; ret)
```
-/
def unsafeGetindexReshapedScalar {A I E : Type}
    (getindex : A → I → RResult E) (array : A) (index : I) : RResult E :=
  getindex array index

/--
Julia source: base/reshapedarray.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _unsafe_getindex_rs(A, I) = (@inbounds ret = A[I...]; ret)
```
-/
def unsafeGetindexReshapedTuple {A I E : Type}
    (getindex : A → I → RResult E) (array : A) (indices : I) : RResult E :=
  getindex array indices

/--
Julia source: base/reshapedarray.jl:319-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(A::ReshapedArrayLF, val, index::Int)
    @boundscheck checkbounds(A, index)
    indexparent = index - firstindex(A) + firstindex(parent(A))
    @inbounds parent(A)[indexparent] = val
    val
end
```
-/
def setindexReshapedLinear {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P V : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArrayLF T N P → I64 → m Unit)
    (firstArray : ReshapedArrayLF T N P → m I64)
    (firstParent : P → m I64) (setindex : P → I64 → V → m Unit)
    (array : ReshapedArrayLF T N P) (value : V) (index : I64) : m V := do
  if boundsChecking then checkbounds array index
  let arrayFirst ← firstArray array
  let parentArray := reshapedParent array
  let parentFirst ← firstParent (reshapedParent array)
  let indexParent := add_int (sub_int index arrayFirst) parentFirst
  setindex parentArray indexParent value
  pure value

/--
Julia source: base/reshapedarray.jl:325-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(A::ReshapedArray{T,N}, val, indices::Vararg{Int,N}) where {T,N}
    @boundscheck checkbounds(A, indices...)
    _unsafe_setindex!(A, val, indices...)
end
```
-/
def setindexReshapedCartesian {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI V R : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArray T N P MI → List I64 → m Unit)
    (unsafeSet : ReshapedArray T N P MI → V → List I64 → m R)
    (array : ReshapedArray T N P MI) (value : V) (indices : List I64) : m R := do
  if boundsChecking then checkbounds array indices
  unsafeSet array value indices

/--
Julia source: base/reshapedarray.jl:329-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(A::ReshapedArray, val, index::ReshapedIndex)
    @boundscheck checkbounds(parent(A), index.parentindex)
    @inbounds parent(A)[index.parentindex] = val
    val
end
```
-/
def setindexReshapedIndex {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI V I : Type}
    (boundsChecking : Bool) (checkbounds : P → I → m Unit)
    (setindex : P → I → V → m Unit)
    (array : ReshapedArray T N P MI) (value : V) (index : ReshapedIndex I) : m V := do
  if boundsChecking then checkbounds (reshapedParent array) index.parentindex
  setindex (reshapedParent array) index.parentindex value
  pure value

/--
Julia source: base/reshapedarray.jl:335-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_setindex!(A::ReshapedArray{T,N}, val, indices::Vararg{Int,N}) where {T,N}
    axp = axes(A.parent)
    i = offset_if_vec(_sub2ind(size(A), indices...), axp)
    @inbounds parent(A)[ind2sub_rs(axes(A.parent), A.mi, i)...] = val
    val
end
```
-/
def unsafeSetindexReshaped {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI V AX : Type}
    (axes : P → m (List AX))
    (sub2ind : Vector I64 N → List I64 → m I64)
    (offset : I64 → List AX → m I64)
    (ind2sub : List AX → List MI → I64 → m (List I64))
    (setindex : P → List I64 → V → m Unit)
    (array : ReshapedArray T N P MI) (value : V) (indices : List I64) : m V := do
  let axisForOffset ← axes array.parent
  let linear ← sub2ind (reshapedSize array) indices
  let adjusted ← offset linear axisForOffset
  let axisForSubscripts ← axes array.parent
  let parentIndices ← ind2sub axisForSubscripts array.mi adjusted
  setindex (reshapedParent array) parentIndices value
  pure value

/--
Julia source: base/reshapedarray.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::ReshapedRange, val, index::Int) = _rs_setindex!_err()
```
-/
def setindexReshapedRangeLinear {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {A V I : Type}
    (rangeError : Unit → m Unit)
    (_array : ReshapedRange T N A) (_value : V) (_index : I) : m Unit :=
  rangeError ()

/--
Julia source: base/reshapedarray.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::ReshapedRange{T,N}, val, indices::Vararg{Int,N}) where {T,N} = _rs_setindex!_err()
```
-/
def setindexReshapedRangeCartesian {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {A V I : Type}
    (rangeError : Unit → m Unit)
    (_array : ReshapedRange T N A) (_value : V) (_indices : I) : m Unit :=
  rangeError ()

/--
Julia source: base/reshapedarray.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::ReshapedRange, val, index::ReshapedIndex) = _rs_setindex!_err()
```
-/
def setindexReshapedRangeIndex {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {A V I : Type}
    (rangeError : Unit → m Unit)
    (_array : ReshapedRange T N A) (_value : V) (_index : ReshapedIndex I) : m Unit :=
  rangeError ()

/--
Julia source: base/reshapedarray.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _rs_setindex!_err() = error("indexed assignment fails for a reshaped range; consider calling collect")
```
-/
def rsSetindexError {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    (_ : Unit) : m Unit :=
  throw .errorException

/--
Julia source: base/reshapedarray.jl:350-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{T}}, a::ReshapedArray{T}) where {T} = cconvert(Ptr{T}, parent(a))
```
-/
def cconvertReshaped {T P Ptr C : Type} {N : Nat} {MI : Type}
    (cconvert : Ptr → P → RResult C)
    (pointerType : Ptr) (array : ReshapedArray T N P MI) : RResult C :=
  cconvert pointerType (reshapedParent array)

/--
Julia source: base/reshapedarray.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::ReshapedArray{T}) where {T} = unsafe_convert(Ptr{T}, a.parent)
```
-/
def unsafeConvertReshaped {T P Ptr : Type} {N : Nat} {MI : Type}
    (unsafeConvert : Ptr → P → RResult Ptr)
    (pointerType : Ptr) (array : ReshapedArray T N P MI) : RResult Ptr :=
  unsafeConvert pointerType array.parent

/--
Julia source: base/reshapedarray.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{Slice, ReshapedUnitRange, Vararg{ScalarIndex}}) = IndexLinear()
```
-/
def viewindexingSliceReshaped {A : Type} (_indices : A) : IndexStyle :=
  .linear

/--
Julia source: base/reshapedarray.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
viewindexing(I::Tuple{ReshapedRange, Vararg{ScalarIndex}}) = IndexLinear()
```
-/
def viewindexingReshapedRange {A : Type} (_indices : A) : IndexStyle :=
  .linear

/--
Julia source: base/reshapedarray.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_stride1(s, inds, I::Tuple{ReshapedRange, Vararg{Any}}) = s * Int(step(I[1].parent))
```
-/
def computeStride1 {S R P Step : Type} {N : Nat}
    (first : List R → R) (parent : R → P) (step : P → Step)
    (toInt : Step → RResult I64) (multiply : S → I64 → RResult S)
    (stride : S) (indices : List R) : RResult S := do
  let range := first indices
  let parentRange := parent range
  let parentStep := step parentRange
  let integerStep ← toInt parentStep
  multiply stride integerStep

/--
Julia source: base/reshapedarray.jl:358-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
compute_offset1(parent::AbstractVector, stride1::Integer, I::Tuple{ReshapedRange}) =
    (@inline; Int(first(I[1])) - Int(first(axes1(I[1])))*stride1)
```
-/
def computeOffset1 {R AX S I : Type}
    (firstRange : List R → R) (first : R → S)
    (axes1 : R → AX) (firstAxis : AX → S)
    (toInt : S → RResult I64) (multiply : I64 → I64 → I64)
    (subtract : I64 → I64 → I64)
    (stride1 : I64) (indices : List R) : RResult I64 := do
  let rangeOrigin ← toInt (first (firstRange indices))
  let rangeAxes := axes1 (firstRange indices)
  let axisOrigin ← toInt (firstAxis rangeAxes)
  let scaled := multiply axisOrigin stride1
  .ok (subtract rangeOrigin scaled)

/--
Julia source: base/reshapedarray.jl:360-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
substrides(strds::NTuple{N,Int}, I::Tuple{ReshapedRange{<:Integer}, Vararg{Any}}) where N =
    (size_to_strides(strds[1]*Int(step(I[1].parent)), size(I[1])...)..., substrides(tail(strds), tail(I))...)
```
-/
def substridesReshapedRange {R S : Type}
    (first : List R → R) (parent : R → S) (step : S → I64)
    (toInt : I64 → RResult I64) (size : R → RResult (List I64))
    (multiply : I64 → I64 → I64)
    (sizeToStrides : I64 → List I64 → RResult (List I64))
    (tailSubstrides : List I64 → List R → RResult (List I64))
    (strides : List I64) (indices : List R) : RResult (List I64) := do
  let stride := strides.headD (JInt.lit .i64 0)
  let range := first indices
  let parentRange := parent range
  let parentStep ← toInt (step parentRange)
  let rangeSize ← size range
  let firstStrides ← sizeToStrides (multiply stride parentStep) rangeSize
  let rest ← tailSubstrides (strides.drop 1) (indices.drop 1)
  .ok (firstStrides ++ rest)

/--
Julia source: base/reshapedarray.jl:368-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{S}}, V::SubArray{T,N,P,<:Tuple{Vararg{StridedSubArrayIndex}}}) where {S,T,N,P}
    parent = V.parent
    Δmem = if _checkcontiguous(Bool, parent)
        (first_index(V) - firstindex(parent)) * elsize(parent)
    else
        _memory_offset(parent, map(first, V.indices)...)
    end
    return Ptr{S}(unsafe_convert(Ptr{T}, parent) + Int(Δmem))
end
```
-/
def unsafeConvertSubArray {T P PtrT PtrS : Type}
    (checkcontiguous : P → Bool)
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent : P → RResult I64) (elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (unsafeConvert : PtrT → P → RResult PtrT)
    (ptrAdd : PtrT → I64 → RResult PtrT)
    (pointer : PtrT → RResult PtrS) (pointerTypeT : PtrT)
    (view : JuliaLean.base.subarray.SubArray P T) : RResult PtrS := do
  let parent := view.parent
  let memoryDelta ← if checkcontiguous parent then do
      let viewFirst ← firstIndexView view
      let parentFirst ← firstIndexParent parent
      let elementSize ← elsize parent
      .ok (mul_int (sub_int viewFirst parentFirst) elementSize)
    else do
      let indices ← firstIndices view.indices
      memoryOffset parent indices
  let parentPointer ← unsafeConvert pointerTypeT parent
  let adjusted ← ptrAdd parentPointer memoryDelta
  pointer adjusted

/--
Julia source: base/reshapedarray.jl:384-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _offset_cconvert(::Type{Ptr{T}}, byte_offset::Int, cconv_parent::OffsetCConvert{T}) where {T}
    _offset_cconvert(
        Ptr{T},
        cconv_parent.byte_offset + byte_offset,
        cconv_parent.cconv_parent,
    )
end
```
-/
def offsetCconvertNested {T C PtrT : Type}
    (offsetCconvert : PtrT → I64 → C → RResult (OffsetCConvert T C))
    (pointerType : PtrT) (byteOffset : I64) (parent : OffsetCConvert T C) :
    RResult (OffsetCConvert T C) :=
  offsetCconvert pointerType (add_int parent.byteOffset byteOffset) parent.cconvParent

/--
Julia source: base/reshapedarray.jl:391-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _offset_cconvert(::Type{Ptr{T}}, byte_offset::Int, cconv_parent::C) where {T,C}
    OffsetCConvert{T,C}(
        byte_offset,
        cconv_parent,
    )
end
```
-/
def offsetCconvertBase {T C PtrT : Type}
    (_pointerType : PtrT) (byteOffset : I64) (parent : C) : RResult (OffsetCConvert T C) :=
  .ok ⟨byteOffset, parent⟩

/--
Julia source: base/reshapedarray.jl:398-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{S}}, c::OffsetCConvert{T}) where {S, T}
    Ptr{S}(unsafe_convert(Ptr{T}, c.cconv_parent) + c.byte_offset)
end
```
-/
def unsafeConvertOffsetCconvert {T C PtrT PtrS : Type}
    (unsafeConvert : PtrT → C → RResult PtrT) (ptrAdd : PtrT → I64 → RResult PtrT)
    (pointer : PtrT → RResult PtrS) (pointerTypeT : PtrT)
    (conversion : OffsetCConvert T C) : RResult PtrS := do
  let parentPointer ← unsafeConvert pointerTypeT conversion.cconvParent
  let adjusted ← ptrAdd parentPointer conversion.byteOffset
  pointer adjusted

/--
Julia source: base/reshapedarray.jl:402-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert(::Type{Ptr{S}}, V::SubArray{T,N,P,<:Tuple{Vararg{StridedSubArrayIndex}}}) where {S,T,N,P}
    parent = V.parent
    p = cconvert(Ptr{T}, parent)
    Δmem = if _checkcontiguous(Bool, parent)
        (first_index(V) - firstindex(parent)) * elsize(parent)
    else
        _memory_offset(parent, map(first, V.indices)...)
    end
    _offset_cconvert(
        Ptr{T},
        Int(Δmem),
        p,
    )
end
```
-/
def cconvertSubArray {T P PtrT C : Type}
    (cconvert : PtrT → P → RResult C)
    (checkcontiguous : P → Bool)
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent : P → RResult I64) (elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (offsetCconvert : PtrT → I64 → C → RResult (OffsetCConvert T C))
    (pointerType : PtrT) (view : JuliaLean.base.subarray.SubArray P T) :
    RResult (OffsetCConvert T C) := do
  let parent := view.parent
  let parentConversion ← cconvert pointerType parent
  let memoryDelta ← if checkcontiguous parent then do
      let viewFirst ← firstIndexView view
      let parentFirst ← firstIndexParent parent
      let elementSize ← elsize parent
      .ok (mul_int (sub_int viewFirst parentFirst) elementSize)
    else do
      let indices ← firstIndices view.indices
      memoryOffset parent indices
  offsetCconvert pointerType memoryDelta parentConversion

/--
Julia source: base/reshapedarray.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::AbstractArray) = false
```
-/
def checkcontiguousAbstract {A : Type} (_type : Type) (_array : A) : Bool :=
  false

/--
Julia source: base/reshapedarray.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::DenseArray) = true
```
-/
def checkcontiguousDense {A : Type} (_type : Type) (_array : A) : Bool :=
  true

/--
Julia source: base/reshapedarray.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::ReshapedArray) = _checkcontiguous(Bool, parent(A))
```
-/
def checkcontiguousReshaped {T : Type} {N : Nat} {P MI : Type}
    (checkcontiguous : P → Bool) (_type : Type)
    (array : ReshapedArray T N P MI) : Bool :=
  checkcontiguous (reshapedParent array)

/--
Julia source: base/reshapedarray.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::FastContiguousSubArray) = _checkcontiguous(Bool, parent(A))
```
-/
def checkcontiguousSubArray {P T : Type}
    (checkcontiguous : P → Bool) (_type : Type)
    (array : JuliaLean.base.subarray.SubArray P T) : Bool :=
  checkcontiguous array.parent

/--
Julia source: base/reshapedarray.jl:424-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function strides(a::ReshapedArray)
    _checkcontiguous(Bool, a) && return size_to_strides(1, size(a)...)
    apsz::Dims = size(a.parent)
    apst::Dims = strides(a.parent)
    msz, mst, n = merge_adjacent_dim(apsz, apst) # Try to perform "lazy" reshape
    n == ndims(a.parent) && return size_to_strides(mst, size(a)...) # Parent is stridevector like
    return _reshaped_strides(size(a), 1, msz, mst, n, apsz, apst)
end
```
-/
def stridesReshaped {T : Type} {N : Nat} {P MI : Type}
    (checkcontiguous : ReshapedArray T N P MI → Bool)
    (parentSize : P → RResult (List I64)) (parentStrides : P → RResult (List I64))
    (merge : List I64 → List I64 → RResult (I64 × I64 × I64))
    (ndims : P → RResult I64)
    (sizeToStrides : I64 → List I64 → RResult (List I64))
    (reshapedStrides : List I64 → I64 → I64 → I64 → I64 → List I64 → List I64 → RResult (List I64))
    (array : ReshapedArray T N P MI) : RResult (List I64) := do
  if checkcontiguous array then
    sizeToStrides (JInt.lit .i64 1) (reshapedSize array).toList
  else do
    let parentSizes ← parentSize array.parent
    let parentSteps ← parentStrides array.parent
    let (mergedSize, mergedStride, mergedRank) ← merge parentSizes parentSteps
    if mergedRank == (← ndims array.parent) then
      sizeToStrides mergedStride (reshapedSize array).toList
    else
      reshapedStrides (reshapedSize array).toList (JInt.lit .i64 1) mergedSize mergedStride
        mergedRank parentSizes parentSteps

/--
Julia source: base/reshapedarray.jl:433-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reshaped_strides(::Dims{0}, reshaped::Int, msz::Int, ::Int, ::Int, ::Dims, ::Dims)
    reshaped == msz && return ()
    throw(ArgumentError("Input is not strided."))
end
```
-/
def reshapedStridesEmpty (_sizes : Vector I64 0)
    (reshaped mergedSize : I64) (_mergedStride _rank : I64)
    (_parentSizes _parentStrides : List I64) : RResult (List I64) :=
  if reshaped == mergedSize then .ok [] else .error .argumentError

/--
Julia source: base/reshapedarray.jl:437-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reshaped_strides(sz::Dims, reshaped::Int, msz::Int, mst::Int, n::Int, apsz::Dims, apst::Dims)
    st = reshaped * mst
    reshaped = reshaped * sz[1]
    if length(sz) > 1 && reshaped == msz && sz[2] != 1
        msz, mst, n = merge_adjacent_dim(apsz, apst, n + 1)
        reshaped = 1
    end
    sts = _reshaped_strides(tail(sz), reshaped, msz, mst, n, apsz, apst)
    return (st, sts...)
end
```
-/
def reshapedStridesRecursive
    (multiply : I64 → I64 → I64)
    (firstDim secondDim : List I64 → Nat → RResult I64)
    (merge : List I64 → List I64 → I64 → RResult (I64 × I64 × I64))
    (recurse : List I64 → I64 → I64 → I64 → I64 → List I64 → List I64 → RResult (List I64))
    (sizes : List I64) (reshaped mergedSize mergedStride rank : I64)
    (parentSizes parentStrides : List I64) : RResult (List I64) := do
  let firstSize ← firstDim sizes 1
  let stride := multiply reshaped mergedStride
  let newReshaped := multiply reshaped firstSize
  let shouldMerge ← if sizes.length > 1 && newReshaped == mergedSize then do
      let nextSize ← secondDim sizes 2
      .ok (nextSize.val != 1)
    else
      .ok false
  let (nextMergedSize, nextMergedStride, nextRank, nextReshaped) ←
    if shouldMerge then do
      let (size, step, n) ← merge parentSizes parentStrides (add_int rank (JInt.lit .i64 1))
      .ok (size, step, n, JInt.lit .i64 1)
    else
      .ok (mergedSize, mergedStride, rank, newReshaped)
  let rest ← recurse (sizes.drop 1) nextReshaped nextMergedSize nextMergedStride
    nextRank parentSizes parentStrides
  .ok (stride :: rest)

/--
Julia source: base/reshapedarray.jl:448-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge_adjacent_dim(::Dims{0}, ::Dims{0}) = 1, 1, 0
```
-/
def mergeAdjacentDimEmpty : I64 × I64 × I64 :=
  (JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 0)

/--
Julia source: base/reshapedarray.jl:449-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge_adjacent_dim(apsz::Dims{1}, apst::Dims{1}) = apsz[1], apst[1], 1
```
-/
def mergeAdjacentDimOne (sizes strides : Vector I64 1) : I64 × I64 × I64 :=
  (sizes.get ⟨0, by decide⟩, strides.get ⟨0, by decide⟩, JInt.lit .i64 1)

/--
Julia source: base/reshapedarray.jl:450-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge_adjacent_dim(apsz::Dims{N}, apst::Dims{N}, n::Int = 1) where {N}
    sz, st = apsz[n], apst[n]
    while n < N
        szₙ, stₙ = apsz[n+1], apst[n+1]
        if sz == 1
            sz, st = szₙ, stₙ
        elseif stₙ == st * sz || szₙ == 1
            sz *= szₙ
        else
            break
        end
        n += 1
    end
    return sz, st, n
end
```
-/
def mergeAdjacentDimMany {N : Nat}
    (getDim : Vector I64 N → I64 → RResult I64)
    (sizes strides : Vector I64 N) (start : I64) : RResult (I64 × I64 × I64) := do
  let mut size ← getDim sizes start
  let mut stride ← getDim strides start
  let mut n := start
  while n.val < Int.ofNat N do
    let nextIndex := add_int n (JInt.lit .i64 1)
    let nextSize ← getDim sizes nextIndex
    let nextStride ← getDim strides nextIndex
    if size.val == 1 then
      size := nextSize
      stride := nextStride
    else if nextStride == mul_int stride size || nextSize.val == 1 then
      size := mul_int size nextSize
    else
      break
    n := nextIndex
  .ok (size, stride, n)

/--
Julia source: base/reshapedarray.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, R::ReshapedArray) = reshape(map(f, parent(R)), size(R))
```
-/
def mapReshapedArray {T U : Type} {N : Nat} {P MI M R : Type}
    (map : (T → U) → P → RResult M) (reshape : M → Vector I64 N → RResult R)
    (f : T → U) (array : ReshapedArray T N P MI) : RResult R := do
  let mapped ← map f (reshapedParent array)
  reshape mapped (reshapedSize array)

/--
Julia source: base/reshapedarray.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(R::ReshapedArray) = iterate(parent(R))
```
-/
def iterateReshapedArray {T : Type} {N : Nat} {P MI E S : Type}
    (iterate : P → Option (E × S)) (array : ReshapedArray T N P MI) : Option (E × S) :=
  iterate (reshapedParent array)

/--
Julia source: base/reshapedarray.jl:469-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(R::ReshapedArray, state) = iterate(parent(R), state)
```
-/
def iterateReshapedArrayState {T : Type} {N : Nat} {P MI E S : Type}
    (iterate : P → S → Option (E × S)) (array : ReshapedArray T N P MI) (state : S) :
    Option (E × S) :=
  iterate (reshapedParent array) state

/--
Julia source: base/reshapedarray.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapfoldl_impl(f, op, nt, R::ReshapedArray) = mapfoldl_impl(f, op, nt, parent(R))
```
-/
def mapfoldlReshaped {T : Type} {N : Nat} {P MI F O E R : Type}
    (mapfoldl : F → O → E → P → RResult R)
    (f : F) (op : O) (neutral : E) (array : ReshapedArray T N P MI) : RResult R :=
  mapfoldl f op neutral (reshapedParent array)

/--
Julia source: base/reshapedarray.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapfoldr_impl(f, op, nt, R::ReshapedArray) = mapfoldr_impl(f, op, nt, parent(R))
```
-/
def mapfoldrReshaped {T : Type} {N : Nat} {P MI F O E R : Type}
    (mapfoldr : F → O → E → P → RResult R)
    (f : F) (op : O) (neutral : E) (array : ReshapedArray T N P MI) : RResult R :=
  mapfoldr f op neutral (reshapedParent array)

/--
Julia source: base/reshapedarray.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x, R::ReshapedArray) = in(x, parent(R))
```
-/
def inReshapedArray {T : Type} {N : Nat} {P MI R : Type}
    (contains : T → P → RResult Bool) (value : T)
    (array : ReshapedArray T N P MI) : RResult Bool :=
  contains value (reshapedParent array)

end JuliaLean.base.reshapedarray
