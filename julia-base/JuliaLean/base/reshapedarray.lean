import JuliaLean.base.boot
import JuliaLean.base.multinverses
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
  | undefinedReference
  | showError (error : JuliaLean.Strings.ShowErrorKind)
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
  let product ← trailing (first :: second :: rest)
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
def reshapeAbstractArray {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {P D S R : Type}
    (length : P → m I64) (checkedDims : D → m I64)
    (throwDmrs : I64 → String → D → m R)
    (indexStyle : P → m S)
    (construct : P × S → D → m R)
    (parent : P) (dims : D) : m R := do
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
def constructReshapedCartesian {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P A S MI : Type}
    (size : P → m (List S)) (front : List S → m (List S))
    (toInt : S → m I64) (makeInverse : I64 → m MI)
    (pair : P × A) (dims : Vector I64 N) : m (ReshapedArray T N P MI) := do
  let parent := pair.1
  let shape ← size parent
  let leading ← front shape
  let adjusted ← leading.mapM fun value => do
    let n ← toInt value
    pure (if n.val < 1 then JInt.lit .i64 1 else n)
  let inverses ← adjusted.mapM makeInverse
  pure (reshapedArrayConstructor parent dims inverses)

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
def getindexReshapedLinear {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P E : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArrayLF T N P → I64 → m Unit)
    (firstArray : ReshapedArrayLF T N P → m I64)
    (firstParent : P → m I64) (getindex : P → I64 → m E)
    (array : ReshapedArrayLF T N P) (index : I64) : m E := do
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
def getindexReshapedCartesian {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI E : Type}
    (boundsChecking : Bool) (checkbounds : ReshapedArray T N P MI → List I64 → m Unit)
    (unsafeGet : ReshapedArray T N P MI → List I64 → m E)
    (array : ReshapedArray T N P MI) (indices : List I64) : m E := do
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
def getindexReshapedIndex {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P I E : Type} {MI : Type}
    (boundsChecking : Bool) (checkbounds : P → I → m Unit)
    (getindex : P → I → m E)
    (array : ReshapedArray T N P MI) (index : ReshapedIndex I) : m E := do
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
def unsafeGetindexReshaped {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P AX MI E : Type}
    (axes : P → m (List AX))
    (sub2ind : Vector I64 N → List I64 → m I64)
    (offset : I64 → List AX → m I64)
    (ind2sub : List AX → List MI → I64 → m (List I64))
    (unsafeGet : P → List I64 → m E)
    (array : ReshapedArray T N P MI) (indices : List I64) : m E := do
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
def unsafeGetindexReshapedScalar {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {A I E : Type}
    (getindex : A → I → m E) (array : A) (index : I) : m E :=
  getindex array index

/--
Julia source: base/reshapedarray.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _unsafe_getindex_rs(A, I) = (@inbounds ret = A[I...]; ret)
```
-/
def unsafeGetindexReshapedTuple {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {A I E : Type}
    (getindex : A → I → m E) (array : A) (indices : I) : m E :=
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

/-- reshapedarray.lean `inReshapedArray` (reshapedarray.jl:474 `in(x, R::ReshapedArray)
= in(x, parent(R))`) with the parent's `in` in any monad, since `RResult` cannot carry the
parent's exceptions, and with its result type (`Truth` here). -/
def inReshapedArrayM {m : Type → Type} {T : Type} {N : Nat} {P MI γ : Type}
    (contains : T → P → m γ) (value : T) (array : ReshapedArray T N P MI) :
    m γ :=
  contains value (reshapedParent array)

end JuliaLean.base.reshapedarray

namespace JuliaLean.ArrayCov

/-- `iterate(R::ReshapedArrayIterator, i...)`, `base/reshapedarray.jl:31-34`.
The body calls the parent iterator and destructures its result immediately;
destructuring `nothing` raises the modelled `MethodError`. -/
def reshapedIteratorStep
    (parentIterate : Nat → Option (Nat × Nat)) (state : Nat) :
    Jl (Option (Nat × Nat)) :=
  match parentIterate state with
  | some (item, nextState) => .ok (some (item, nextState))
  | none => .error (.methodError "iterate")

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


structure ReshapedValue where
  parent : List Int
  dims : List Int
  mi : List Int
  deriving Repr, DecidableEq

structure ReshapedIteratorValue where
  iter : List Int
  mi : List Int
  deriving Repr, DecidableEq

inductive ReshapedError where
  | dimensionMismatch
  | errorException
  deriving Repr, DecidableEq

abbrev ReshapedJl (α : Type) := Except ReshapedError α

/-- Outer constructor, `base/reshapedarray.jl:10`. -/
def reshaped10Constructor (parent : List Int) (dims mi : List Int) : ReshapedValue :=
  ⟨parent, dims, mi⟩

/-- Iterator constructor wrapper, `base/reshapedarray.jl:20`. -/
def reshaped20IteratorConstructor
    (parent : ReshapedValue → List Int)
    (rsIterator : List Int → List Int → ReshapedIteratorValue)
    (array : ReshapedValue) : ReshapedIteratorValue :=
  rsIterator (parent array) array.mi

/-- `_rs_iterator`, `base/reshapedarray.jl:21-24`. -/
def reshaped21Iterator (eachIndex : List Int → List Int)
    (parent mi : List Int) : ReshapedIteratorValue :=
  let iter := eachIndex parent
  ⟨iter, mi⟩

/-- Iterator length forwarding, `base/reshapedarray.jl:35`. -/
def reshaped35IteratorLength (length : List Int → Nat)
    (iterator : ReshapedIteratorValue) : Nat := length iterator.iter

/-- Iterator eltype branch, `base/reshapedarray.jl:36`. -/
def reshaped36IteratorEltype (isDefined : Int → Bool) (eltype : Int → Int)
    (iteratorType anyType : Int) : Int :=
  if isDefined iteratorType then eltype iteratorType else anyType

/-- `throw_dmrsa`, `base/reshapedarray.jl:38-39`. -/
def reshaped38ThrowDimensionMismatch (_dims : List Int) (_length : Int) : ReshapedJl Unit :=
  .error .dimensionMismatch
/-- `size(A::ReshapedArray)`, `base/reshapedarray.jl:253`. -/
def reshaped253Size (array : ReshapedValue) : List Int := array.dims

/-- `length(A::ReshapedArray)`, `base/reshapedarray.jl:254`. -/
def reshaped254Length (length : List Int → Nat) (array : ReshapedValue) : Nat :=
  length array.parent

/-- `similar(A, eltype, dims)`, `base/reshapedarray.jl:255`. -/
def reshaped255Similar (similar : List Int → Int → List Int → Jl Int)
    (array : ReshapedValue) (elementType : Int) (dims : List Int) : Jl Int :=
  similar array.parent elementType dims

/-- Type-level `similar`, `base/reshapedarray.jl:256`. -/
def reshaped256SimilarType (similar : Int → List Int → Jl Int)
    (parentType : Int) (dims : List Int) : Jl Int := similar parentType dims

/-- Linear index style specialization, `base/reshapedarray.jl:257`. -/
def reshaped257IndexStyle (_ : Unit) : Int := 1

def reshaped258Parent (array : ReshapedValue) : List Int := array.parent

/-- `parentindices`, `base/reshapedarray.jl:259`. -/
def reshaped259ParentIndices (size : List Int → List Int) (oneto : Int → Int)
    (array : ReshapedValue) : List Int :=
  (size array.parent).map oneto

/-- Parent elsize forwarding, `base/reshapedarray.jl:260`. -/
def reshaped260Elsize (elsize : Int → JInt64) (parentType : Int) : JInt64 :=
  elsize parentType

/-- `unaliascopy`, `base/reshapedarray.jl:262`. -/
def reshaped262UnaliasCopy (copy : List Int → List Int)
    (array : ReshapedValue) : ReshapedValue :=
  ⟨copy array.parent, array.dims, array.mi⟩

def reshaped263DataIds (dataids : List Int → List Int)
    (array : ReshapedValue) : List Int := dataids array.parent

def reshaped265MightAlias (mightAlias : List Int → List Int → Bool)
    (left right : ReshapedValue) : Bool := mightAlias left.parent right.parent

def reshaped267MightAliasSub (mightAlias : List Int → List Int → Bool)
    (left : ReshapedValue) (right : List Int) : Bool := mightAlias left.parent right

def reshaped268SubMightAlias (mightAlias : List Int → List Int → Bool)
    (left : List Int) (right : ReshapedValue) : Bool := mightAlias left right.parent
/-- `_rs_setindex!_err`, `base/reshapedarray.jl:348`. -/
def reshaped348SetRangeError (_ : Unit) : ReshapedJl Unit :=
  .error .errorException

def reshaped344SetRangeLinear (_array _value _index : Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped345SetRangeCartesian (_array _value : Int) (_indices : List Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped346SetRangeIndex (_array _value _parentIndex : Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped350Cconvert (cconvert : List Int → Int) (array : ReshapedValue) : Int :=
  cconvert array.parent

def reshaped351UnsafeConvert (unsafeConvert : List Int → Int)
    (array : ReshapedValue) : Int := unsafeConvert array.parent

def reshaped355ViewIndexingSlice (_ : Unit) : Int := 1
def reshaped356ViewIndexingRange (_ : Unit) : Int := 1

/-- `compute_stride1`, `base/reshapedarray.jl:357`, with wrapping Int multiplication. -/
def reshaped357ComputeStride (step : Int → JInt64) (stride : JInt64)
    (parentRange : Int) : JInt64 := stride * step parentRange

def reshaped417ContiguousAbstract (_ : Unit) : Bool := false
def reshaped420ContiguousDense (_ : Unit) : Bool := true
def reshaped421ContiguousReshaped (parentContiguous : List Int → Bool)
    (array : ReshapedValue) : Bool := parentContiguous array.parent
def reshaped422ContiguousSubarray (parentContiguous : List Int → Bool)
    (parent : List Int) : Bool := parentContiguous parent

def reshaped448MergeEmpty (_ : Unit) : Int × Int × Int := (1, 1, 0)
def reshaped449MergeOne (size stride : Int) : Int × Int × Int := (size, stride, 1)

def reshaped466Map (mapParent : (Int → Int) → List Int → List Int)
    (reshape : List Int → List Int → Jl ReshapedValue)
    (f : Int → Int) (array : ReshapedValue) : Jl ReshapedValue :=
  reshape (mapParent f array.parent) array.dims

def reshaped468Iterate (iterate : List Int → Option (Int × Int))
    (array : ReshapedValue) : Option (Int × Int) := iterate array.parent

def reshaped469IterateState (iterate : List Int → Int → Option (Int × Int))
    (array : ReshapedValue) (state : Int) : Option (Int × Int) :=
  iterate array.parent state

def reshaped471Mapfoldl (mapfold : (Int → Int) → (Int → Int → Int) → Int → List Int → Int)
    (f : Int → Int) (op : Int → Int → Int) (neutral : Int)
    (array : ReshapedValue) : Int := mapfold f op neutral array.parent

def reshaped472Mapfoldr (mapfold : (Int → Int) → (Int → Int → Int) → Int → List Int → Int)
    (f : Int → Int) (op : Int → Int → Int) (neutral : Int)
    (array : ReshapedValue) : Int := mapfold f op neutral array.parent

def reshaped474In (contains : Int → List Int → Bool)
    (value : Int) (array : ReshapedValue) : Bool := contains value array.parent

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive ReshapeDim where
  | integer (value : Int)
  | colon
  deriving Repr, DecidableEq

def reshaped122Varargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped123AbstractAxes (toShape : List Int → List Int)
    (reshapeTuple : List Int → Jl Int) (shape : List Int) : Jl Int :=
  reshapeTuple (toShape shape)

def reshaped126OneToAxes (toShape : List Int → List Int)
    (reshapeTuple : List Int → Jl Int) (shape : List Int) : Jl Int :=
  reshapeTuple (toShape shape)

def reshaped127ConvertDims (convertInt : Int → Jl Int)
    (reshapeTuple : List Int → Jl Int) (dims : List Int) : Jl Int := do
  let dims ← dims.mapM convertInt
  reshapeTuple dims

def reshaped128Dims (_reshape : List Int → Jl Int) (dims : List Int) : Jl Int :=
  _reshape dims

def reshaped131VectorColon (parent : List Int) : List Int := parent
def reshaped132VectorColonTuple (parent : List Int) : List Int := parent

def reshaped133IntVarargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped134IntegerVarargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped135ColonVarargs (reshapeTuple : List ReshapeDim → Jl Int)
    (dims : List ReshapeDim) : Jl Int := reshapeTuple dims

def reshaped136ColonTuple (uncolon : List ReshapeDim → Jl (List Int))
    (reshapeDims : List Int → Jl Int) (dims : List ReshapeDim) : Jl Int := do
  let dims ← uncolon dims
  reshapeDims dims

def reshapeAnyColon : List ReshapeDim → Bool
  | [] => false
  | .colon :: _ => true
  | .integer _ :: tail => reshapeAnyColon tail

abbrev ReshapeTupleResult := Except JlError (List ReshapeDim)

def reshapeBeforeColon : List ReshapeDim → ReshapeTupleResult
  | [] => .error (.methodError "_before_colon")
  | .colon :: _ => .ok []
  | head@(.integer _) :: tail => do
      let rest ← reshapeBeforeColon tail
      .ok (head :: rest)

def reshapeAfterColon : List ReshapeDim → ReshapeTupleResult
  | [] => .error (.methodError "_after_colon")
  | .colon :: tail => .ok tail
  | .integer _ :: tail => reshapeAfterColon tail

def reshaped186SameRank (parent : List Int) (_rank : Nat) : List Int := parent

def reshaped194Trailing : List JInt64 → JInt64
  | [] => JInt.lit .i64 1
  | length :: rest => length * reshaped194Trailing rest

def reshaped195TrailingOne (length : JInt64) : JInt64 := length

def reshaped196RdimsVal (rdims : List JInt64 → List JInt64 → List JInt64)
    (rank : Nat) (indices : List JInt64) : List JInt64 :=
  rdims (List.replicate rank (JInt.lit .i64 1)) indices

def reshaped197RdimsEmptyEmpty (_ : Unit) : List JInt64 := []
def reshaped198RdimsEmptyOne (_index : JInt64) : List JInt64 := []
def reshaped199RdimsEmptyMany (_indices : List JInt64) : List JInt64 := []
def reshaped200RdimsOneEmpty (output : JInt64) : List JInt64 := [output]
def reshaped201RdimsManyEmpty (output : List JInt64) : List JInt64 := output
def reshaped202RdimsOneOne (index : JInt64) : List JInt64 := [index]

def reshaped203RdimsOneMany (oneto : JInt64 → JInt64)
    (indices : List JInt64) : List JInt64 :=
  [oneto (reshaped194Trailing indices)]

def reshaped204RdimsEqual (indices : List JInt64) : List JInt64 := indices

def reshaped205RdimsRecursive
    (rdims : List JInt64 → List JInt64 → List JInt64)
    (output indices : List JInt64) : List JInt64 :=
  match indices with
  | [] => output
  | first :: tail => first :: rdims output.tail tail

def reshaped209VectorOne (parent : List Int) (_dims : List Int) : List Int := parent
def reshaped210ArrayOne (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped211ArrayDims (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped232NestedVector (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped233Nested (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


structure ReshapedView where
  parent : List Int
  firstIndex : JInt64
  parentFirstIndex : JInt64
  firstIndices : List JInt64
  deriving Repr, DecidableEq

structure OffsetConvertModel where
  byteOffset : JInt64
  parent : Int
  deriving Repr, DecidableEq

def reshaped358ComputeOffset (firstRange axesFirst : Int → JInt64)
    (stride : JInt64) (range : Int) : JInt64 :=
  firstRange range - axesFirst range * stride

def reshaped360Substrides (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (step : Int → JInt64) (size : Int → List JInt64)
    (recurse : List JInt64 → List Int → List JInt64)
    (strides : List JInt64) (indices : List Int) : List JInt64 :=
  match strides, indices with
  | stride :: restStrides, range :: restIndices =>
      sizeToStrides (stride * step range) (size range) ++ recurse restStrides restIndices
  | _, _ => recurse strides indices

def reshaped368UnsafeConvert (contiguous : List Int → Bool)
    (elsize : List Int → JInt64)
    (memoryOffset : List Int → List JInt64 → JInt64)
    (unsafeConvert : List Int → JInt64)
    (view : ReshapedView) : JInt64 :=
  let delta := if contiguous view.parent then
    (view.firstIndex - view.parentFirstIndex) * elsize view.parent
  else memoryOffset view.parent view.firstIndices
  unsafeConvert view.parent + delta

def reshaped384OffsetNested (recurse : JInt64 → Int → OffsetConvertModel)
    (byteOffset : JInt64) (parent : OffsetConvertModel) : OffsetConvertModel :=
  recurse (parent.byteOffset + byteOffset) parent.parent

def reshaped391OffsetNew (byteOffset : JInt64) (parent : Int) : OffsetConvertModel :=
  ⟨byteOffset, parent⟩

def reshaped398UnsafeOffset (unsafeConvert : Int → JInt64)
    (offset : OffsetConvertModel) : JInt64 :=
  unsafeConvert offset.parent + offset.byteOffset

def reshaped402Cconvert (cconvert : List Int → Int)
    (contiguous : List Int → Bool) (elsize : List Int → JInt64)
    (memoryOffset : List Int → List JInt64 → JInt64)
    (offsetConvert : JInt64 → Int → OffsetConvertModel)
    (view : ReshapedView) : OffsetConvertModel :=
  let parent := cconvert view.parent
  let delta := if contiguous view.parent then
    (view.firstIndex - view.parentFirstIndex) * elsize view.parent
  else memoryOffset view.parent view.firstIndices
  offsetConvert delta parent

inductive ReshapedStrideError where
  | notStrided
  deriving Repr, DecidableEq

abbrev ReshapedStrideJl (α : Type) := Except ReshapedStrideError α

def reshaped424Strides (contiguous : ReshapedValue → Bool)
    (sizeArray : ReshapedValue → List JInt64)
    (sizeParent stridesParent : List Int → List JInt64)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (merge : List JInt64 → List JInt64 → JInt64 × JInt64 × Nat)
    (recurse : List JInt64 → JInt64 → JInt64 → JInt64 → Nat →
      List JInt64 → List JInt64 → ReshapedStrideJl (List JInt64))
    (array : ReshapedValue) : ReshapedStrideJl (List JInt64) :=
  if contiguous array then .ok (sizeToStrides (JInt.lit .i64 1) (sizeArray array))
  else
    let parentSize := sizeParent array.parent
    let parentStrides := stridesParent array.parent
    let (mergedSize, mergedStride, n) := merge parentSize parentStrides
    if n = parentSize.length then .ok (sizeToStrides mergedStride (sizeArray array))
    else recurse (sizeArray array) (JInt.lit .i64 1) mergedSize mergedStride n
      parentSize parentStrides

def reshaped433StridesEmpty (reshaped mergedSize : JInt64) :
    ReshapedStrideJl (List JInt64) :=
  if reshaped = mergedSize then .ok [] else .error .notStrided

def reshaped437Strides (merge : List JInt64 → List JInt64 → Nat →
      JInt64 × JInt64 × Nat)
    (recurse : List JInt64 → JInt64 → JInt64 → JInt64 → Nat →
      List JInt64 → List JInt64 → ReshapedStrideJl (List JInt64))
    (size : List JInt64) (reshaped mergedSize mergedStride : JInt64)
    (n : Nat) (parentSize parentStrides : List JInt64) : ReshapedStrideJl (List JInt64) :=
  match size with
  | [] => reshaped433StridesEmpty reshaped mergedSize
  | first :: tail => do
      let stride := reshaped * mergedStride
      let reshaped := reshaped * first
      let (mergedSize, mergedStride, n, reshaped) :=
        if !tail.isEmpty && reshaped = mergedSize && tail.getD 0 (JInt.lit .i64 0) != JInt.lit .i64 1 then
          let merged := merge parentSize parentStrides (n + 1)
          (merged.1, merged.2.1, merged.2.2, JInt.lit .i64 1)
        else (mergedSize, mergedStride, n, reshaped)
      let rest ← recurse tail reshaped mergedSize mergedStride n parentSize parentStrides
      pure (stride :: rest)

def reshaped450MergeLoop : List JInt64 → List JInt64 → Nat → Nat →
    JInt64 × JInt64 × Nat
  | sizes, strides, n, 0 =>
      (sizes.getD (n - 1) (JInt.lit .i64 1),
       strides.getD (n - 1) (JInt.lit .i64 1), n)
  | sizes, strides, n, fuel + 1 =>
      let size := sizes.getD (n - 1) (JInt.lit .i64 1)
      let stride := strides.getD (n - 1) (JInt.lit .i64 1)
      if n ≥ sizes.length then (size, stride, n)
      else
        let nextSize := sizes.getD n (JInt.lit .i64 1)
        let nextStride := strides.getD n (JInt.lit .i64 1)
        if size = JInt.lit .i64 1 then
          let sizes := sizes.set (n - 1) nextSize
          let strides := strides.set (n - 1) nextStride
          reshaped450MergeLoop sizes strides (n + 1) fuel
        else if nextStride = stride * size || nextSize = JInt.lit .i64 1 then
          let sizes := sizes.set (n - 1) (size * nextSize)
          reshaped450MergeLoop sizes strides (n + 1) fuel
        else (size, stride, n)

def reshaped450Merge (sizes strides : List JInt64) (n : Nat) :
    JInt64 × JInt64 × Nat :=
  reshaped450MergeLoop sizes strides n (sizes.length - n)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


def reshaped270Ind2subEmpty (_axes : List (List JInt64)) (index : JInt64) : List JInt64 :=
  [index]

def reshaped271Ind2sub (aux : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (axes : List (List JInt64)) (divisors : List JInt64) (index : JInt64) : List JInt64 :=
  aux axes divisors (index - JInt.lit .i64 1)

def reshaped272Ind2subAuxEmpty (first : List JInt64 → JInt64)
    (axes : List (List JInt64)) (index : JInt64) : List JInt64 :=
  [index + first (axes.getLastD [])]

def reshaped273Ind2subAux (divrem : JInt64 → JInt64 → JInt64 × JInt64)
    (first : List JInt64 → JInt64) :
    List (List JInt64) → List JInt64 → JInt64 → List JInt64
  | axes, [], index => reshaped272Ind2subAuxEmpty first axes index
  | [], _ :: _, index => [index]
  | axis :: axes, divisor :: divisors, index =>
      let (quotient, remainder) := divrem index divisor
      (remainder + first axis) ::
        reshaped273Ind2subAux divrem first axes divisors quotient

def reshaped277OffsetVector (first : List JInt64 → JInt64)
    (index : JInt64) (axes : List (List JInt64)) : JInt64 :=
  index + first (axes.getD 0 []) - JInt.lit .i64 1

def reshaped278OffsetGeneral (index : JInt64) (_axes : List (List JInt64)) : JInt64 :=
  index

inductive ReshapedIndexError where
  | bounds
  deriving Repr, DecidableEq

abbrev ReshapedIndexJl (α : Type) := Except ReshapedIndexError α

structure ReshapedAccessState where
  parent : List Int
  dims : List JInt64
  axes : List (List JInt64)
  divisors : List JInt64
  deriving Repr, DecidableEq

def reshaped280IsAssignedLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (isassigned : List Int → JInt64 → Bool)
    (array : ReshapedAccessState) (index : JInt64) : Bool :=
  if !checkbounds array index then false
  else
    let parentIndex := index - firstArray array + firstParent array
    isassigned array.parent parentIndex

def reshaped286IsAssignedCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (isassigned : List Int → List JInt64 → Bool)
    (array : ReshapedAccessState) (indices : List JInt64) : Bool :=
  if !checkbounds array indices then false
  else
    let parentAxes := axes array.parent
    let linear := offset (sub2ind (size array) indices) parentAxes
    isassigned array.parent (ind2sub parentAxes array.divisors linear)

def reshaped294GetLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (getindex : List Int → JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (index : JInt64) : ReshapedIndexJl Int := do
  if checkbounds array index then pure () else throw .bounds
  let parentIndex := index - firstArray array + firstParent array
  getindex array.parent parentIndex

def reshaped300GetCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (unsafeGet : ReshapedAccessState → List JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (indices : List JInt64) : ReshapedIndexJl Int := do
  if checkbounds array indices then pure () else throw .bounds
  unsafeGet array indices

def reshaped304GetReshapedIndex (checkbounds : List Int → JInt64 → Bool)
    (getindex : List Int → JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (parentIndex : JInt64) : ReshapedIndexJl Int := do
  if checkbounds array.parent parentIndex then pure () else throw .bounds
  getindex array.parent parentIndex

def reshaped310UnsafeGet
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (unsafeGetParent : List Int → List JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (indices : List JInt64) : ReshapedIndexJl Int :=
  let parentAxes := axes array.parent
  let linear := offset (sub2ind (size array) indices) parentAxes
  unsafeGetParent array.parent (ind2sub parentAxes array.divisors linear)

def reshaped316UnsafeGetScalar (getindex : List Int → JInt64 → Int)
    (parent : List Int) (index : JInt64) : Int := getindex parent index

def reshaped317UnsafeGetTuple (getindex : List Int → List JInt64 → Int)
    (parent : List Int) (indices : List JInt64) : Int := getindex parent indices

def reshaped319SetLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (setindex : List Int → Int → JInt64 → ReshapedIndexJl (List Int))
    (array : ReshapedAccessState) (value : Int) (index : JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array index then pure () else throw .bounds
  let parentIndex := index - firstArray array + firstParent array
  let parent ← setindex array.parent value parentIndex
  pure (value, parent)

def reshaped325SetCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (unsafeSet : ReshapedAccessState → Int → List JInt64 →
      ReshapedIndexJl (Int × List Int))
    (array : ReshapedAccessState) (value : Int) (indices : List JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array indices then pure () else throw .bounds
  unsafeSet array value indices

def reshaped329SetReshapedIndex (checkbounds : List Int → JInt64 → Bool)
    (setindex : List Int → Int → JInt64 → ReshapedIndexJl (List Int))
    (array : ReshapedAccessState) (value : Int) (parentIndex : JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array.parent parentIndex then pure () else throw .bounds
  let parent ← setindex array.parent value parentIndex
  pure (value, parent)

def reshaped335UnsafeSet
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (setindex : List Int → Int → List JInt64 → List Int)
    (array : ReshapedAccessState) (value : Int) (indices : List JInt64) : Int × List Int :=
  let parentAxes := axes array.parent
  let linear := offset (sub2ind (size array) indices) parentAxes
  let parentIndices := ind2sub parentAxes array.divisors linear
  (value, setindex array.parent value parentIndices)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive ReshapeCoreError where
  | argumentError
  | dimensionMismatch
  | methodError
  deriving Repr, DecidableEq

abbrev ReshapeCoreJl (α : Type) := Except ReshapeCoreError α

structure ArrayReshapeState where
  parent : List Int
  dims : List JInt64
  mi : List JInt64 := []
  deriving Repr, DecidableEq

def reshaped43Array (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (parent : List Int) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let length ← checkedDims dims
  if length.val != parent.length then throw .dimensionMismatch
  pure ⟨parent, dims, []⟩

def reshaped55ArrayBang (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (array : ArrayReshapeState) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let length ← checkedDims dims
  if length.val != array.parent.length then throw .dimensionMismatch
  pure { array with dims := dims }

def reshaped138ThrowManyColon (_dims : List ReshapeDim) : ReshapeCoreJl Unit :=
  .error .dimensionMismatch

def reshaped140ThrowIndivisible (_length : JInt64) (_dims : List ReshapeDim) :
    ReshapeCoreJl Unit := .error .dimensionMismatch

def reshaped143Uncolon (promote : Int → ReshapeCoreJl Int)
    (before : List ReshapeDim → ReshapeCoreJl (List JInt64))
    (after : List ReshapeDim → ReshapeCoreJl (List ReshapeDim))
    (anyColon : List ReshapeDim → Bool)
    (compute : JInt64 → List ReshapeDim → List JInt64 → List JInt64 →
      ReshapeCoreJl (List JInt64))
    (parent : List Int) (rawDims : List ReshapeDim) : ReshapeCoreJl (List JInt64) := do
  let dims ← rawDims.mapM fun dim =>
    match dim with
    | .colon => pure .colon
    | .integer value => .integer <$> promote value
  let pre ← before dims
  let post ← after dims
  if anyColon post then throw .dimensionMismatch
  let post := post.filterMap fun dim => match dim with
    | .colon => none
    | .integer value => some (JInt.lit .i64 value)
  compute (JInt.lit .i64 parent.length) dims pre post

def reshaped152ComputeInt (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (length : JInt64) (_dims : List ReshapeDim) (pre post : List JInt64) :
    ReshapeCoreJl (List JInt64) := do
  let size ← if length.val = 0 then pure (JInt.lit .i64 0) else do
    let product ← checkedDims (pre ++ post)
    if product.val = 0 then throw .dimensionMismatch
    let quotient ← JInt.div length product |>.mapError fun _ => .argumentError
    let remainder ← JInt.remInt length product |>.mapError fun _ => .argumentError
    if remainder.val != 0 then throw .dimensionMismatch
    pure quotient
  pure (pre ++ [size] ++ post)

def reshaped172ComputeNonempty (isZero : Int → Bool)
    (divrem : Int → Int → ReshapeCoreJl (Int × Int))
    (length : Int) (_dims : List ReshapeDim) (product : Int) : ReshapeCoreJl Int := do
  if isZero product then throw .dimensionMismatch
  let (quotient, remainder) ← divrem length product
  if !isZero remainder then throw .dimensionMismatch
  pure quotient

def reshaped163ComputeGeneric (product : List Int → Int)
    (isZero : Int → Bool) (promotedZero : Int → Int → Int)
    (compute : Int → List ReshapeDim → Int → ReshapeCoreJl Int)
    (length : Int) (dims : List ReshapeDim) (pre post : List Int) :
    ReshapeCoreJl (List Int) := do
  let product := product (pre ++ post)
  let size ← if isZero length then pure (promotedZero length product)
    else compute length dims product
  pure (pre ++ [size] ++ post)

def reshaped187Val (axes : List Int → List Int)
    (rdims : Nat → List Int → List JInt64)
    (reshape : List Int → List JInt64 → ReshapeCoreJl ArrayReshapeState)
    (parent : List Int) (rank : Nat) : ReshapeCoreJl ArrayReshapeState :=
  reshape parent (rdims rank (axes parent))

def reshaped214VectorOne (oneBased : List Int → ReshapeCoreJl Unit)
    (parent : List Int) (length : JInt64) : ReshapeCoreJl (List Int) := do
  oneBased parent
  if length.val != parent.length then throw .dimensionMismatch
  pure parent

def reshaped221General (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (construct : List Int → List JInt64 → ReshapeCoreJl ArrayReshapeState)
    (parent : List Int) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let product ← checkedDims dims
  if product.val != parent.length then throw .dimensionMismatch
  construct parent dims

def reshaped227ThrowDmrs (_length : JInt64) (_kind : String) (_dims : List JInt64) :
    ReshapeCoreJl Unit := .error .dimensionMismatch

def reshaped235ConstructCartesian (size : List Int → List JInt64)
    (makeMi : List JInt64 → List JInt64) (parent : List Int)
    (dims : List JInt64) : ArrayReshapeState :=
  let sizes := (size parent).dropLast.map fun value =>
    if value.val < 1 then JInt.lit .i64 1 else value
  ⟨parent, dims, makeMi sizes⟩

def reshaped243ConstructZero (parent : List Int) (dims : List JInt64) : ArrayReshapeState :=
  ⟨parent, dims, []⟩

def reshaped248ConstructLinear (parent : List Int) (dims : List JInt64) : ArrayReshapeState :=
  ⟨parent, dims, []⟩

end JuliaLean.ArrayCov

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Julia's `DimensionMismatch`, recorded as a distinct exception. -/
def dimensionMismatch : JlError := .argumentError "DimensionMismatch"

/-- The size check of `_reshape(parent::AbstractArray, dims::Dims)`, `base/reshapedarray.jl:221-225`,
for a parent with `n = length(parent)` elements; on success `__reshape` wraps the parent. -/
def reshapeCheck (n : JInt64) (dims : List JInt64) : Jl Unit := do
  let p ← checkedDims dims
  if p = n then pure () else throw dimensionMismatch

/-- `_reshape_uncolon` and `_reshape_uncolon_computesize` for `Int` dimensions with one `Colon`,
`base/reshapedarray.jl:143-162,172-177`: `pre` and `post` are the dimensions before and after
the colon, `len = length(A)`. -/
def reshapeUncolon (len : JInt64) (pre post : List JInt64) : Jl (List JInt64) := do
  let sz ← if len.val = 0 then pure (JInt.lit .i64 0) else do
    let pr ← checkedDims (pre ++ post)
    if pr.val = 0 then throw dimensionMismatch
    let quo ← JInt.div len pr
    let rem ← JInt.remInt len pr
    if rem.val ≠ 0 then throw dimensionMismatch
    pure quo
  pure (pre ++ [sz] ++ post)

/-- `reshape(A, pre..., :, post...)` for a generic parent with `len` elements,
`base/reshapedarray.jl:136,128,221-225`. -/
def reshapeColon (len : JInt64) (pre post : List JInt64) : Jl (List JInt64) := do
  let dims ← reshapeUncolon len pre post
  reshapeCheck len dims
  pure dims

/-- `SignedMultiplicativeInverse.(max.(1, front(size(parent))))`, `base/reshapedarray.jl:235-241`.
`SmiNewAll szs mis` holds when the constructor returns `mis` for the sizes `szs`. -/
def SmiNewAll : List JInt64 → List (SignedMI .i64) → Prop
  | [], [] => True
  | s :: szs, m :: mis => SmiNew (if s.val < 1 then JInt.lit .i64 1 else s) m ∧ SmiNewAll szs mis
  | _, _ => False

/-- `_ind2sub_rs(ax, szs, ind)`, `base/reshapedarray.jl:272-276`, for a parent whose axes start at
`firsts`: `divrem(ind, mi)` is `div(ind, mi)` and `ind - d * mi.divisor`
(`base/multinverses.jl:151-154`). -/
def ind2subRsAux : List JInt64 → List (SignedMI .i64) → JInt64 → List JInt64
  | firsts, [], ind => [ind + firsts.getLastD (JInt.lit .i64 1)]
  | f :: firsts, mi :: mis, ind =>
    let d := smiDiv ind mi
    let r := ind - d * mi.divisor
    (r + f) :: ind2subRsAux firsts mis d
  | [], _ :: _, ind => [ind]

/-- `ind2sub_rs(ax, szs, i)`, `base/reshapedarray.jl:270-271`. -/
def ind2subRs (firsts : List JInt64) (mis : List (SignedMI .i64)) (i : JInt64) : List JInt64 :=
  match mis with
  | [] => [i]
  | _ => ind2subRsAux firsts mis (i - JInt.lit .i64 1)

end JuliaLean.ReinterpretArrays
