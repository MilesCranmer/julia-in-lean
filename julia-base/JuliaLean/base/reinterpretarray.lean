import JuliaLean.Core
import JuliaLean.base.int

/-!
# Typed model of `base/reinterpretarray.jl`

The model stores array contents as their byte image and keeps Julia's type-layout data explicit.
Native pointer operations are typed interfaces where this model does not represent Julia's
allocator, garbage collector, or compiler-generated type metadata.
-/

namespace JuliaLean.base.reinterpretarray

universe u

open JuliaLean JuliaLean.base.int

abbrev I64 := JInt .i64
abbrev Bytes := List UInt8

inductive ReinterpretError where
  | argument | padding | bounds | divide | nonIntegralStride | noncontiguous | assertion
  deriving Repr, DecidableEq, Inhabited

abbrev RResult (α : Type u) := Except ReinterpretError α

structure Axis where
  first : I64
  length : I64
  deriving Repr, DecidableEq

structure FieldLayout where
  offset : Nat
  size : Nat
  packed : Bool
  usedOffsets : List Nat
  bitPadding : Bool
  deriving Repr, DecidableEq

structure TypeLayout where
  id : Nat
  bits : Nat
  alignedSize : I64
  isBits : Bool
  primitive : Bool
  union : Bool
  singleton : Bool
  bitPadding : Bool
  datatypePadding : Bool
  fields : List FieldLayout
  unionBitPadding : List Bool
  deriving Repr, DecidableEq

structure ArrayInput (A : Type) where
  parent : A
  bytes : Bytes
  rank : Nat
  firstAxis : Axis
  size : List I64

structure ReinterpretArray (T S A : Type) where
  parent : A
  bytes : Bytes
  rank : Nat
  target : TypeLayout
  source : TypeLayout
  readable : Bool
  writable : Bool
  reshaped : Bool
  pointerParent : Bool
  size : List I64
  axes : List Axis

inductive ReinterpretOutcome (A B C : Type) where
  | parent (array : A)
  | view (array : B)
  | nested (array : C)

inductive IndexStyleModel where
  | linear | cartesian | staticCartesian (k : Nat)
  deriving Repr, DecidableEq

structure SCartesianIndex2 where
  i : I64
  j : I64
  deriving Repr, DecidableEq

structure SCartesianIndices2 (K : Nat) where
  indices2 : List I64
  deriving Repr, DecidableEq

structure PaddingErrorModel where
  source : String
  target : String
  deriving Repr, DecidableEq

inductive PointerReadOps (A : Type) where
  | mk (checkbounds : A → List I64 → RResult Unit)
      (linearIndex : A → List I64 → I64)
      (cconvert : A → Nat)
      (unsafeConvert : Nat → Nat)
      (elsize : A → I64)
      (firstindex : A → I64)
      (addPointer : Nat → I64 → Nat)
      (unsafeLoad : Nat → RResult Bytes)

inductive PointerWriteOps (A : Type) where
  | mk (checkbounds : A → List I64 → RResult Unit)
      (linearIndex : A → List I64 → I64)
      (cconvert : A → Nat)
      (unsafeConvert : Nat → Nat)
      (elsize : A → I64)
      (firstindex : A → I64)
      (addPointer : Nat → I64 → Nat)
      (unsafeStore : Nat → Bytes → RResult Unit)

structure PairIndex where
  i : Nat
  j : Nat
  deriving Repr, DecidableEq

/-! Byte layout helpers used by methods which inspect Julia's runtime type metadata. -/

def overwriteBytes (output : Bytes) (offset : Nat) (bytes : Bytes) : Bytes :=
  output.take offset ++ bytes ++ output.drop (offset + bytes.length)

def setTrueAt (bytes : List Bool) (index : Nat) : List Bool := bytes.set index true

def setTrueOffsets (bytes : List Bool) (offsets : List Nat) : List Bool :=
  offsets.foldl (fun used index => setTrueAt used index) bytes

partial def cycleSubpaddingFuel (source target : List Bool) (i j fuel : Nat) : Bool :=
  if fuel == 0 then true
  else if source.getD i false && !target.getD j false then false
  else
    let i' := if i + 1 >= source.length then 0 else i + 1
    let j' := if j + 1 >= target.length then 0 else j + 1
    if i' == 0 && j' == 0 then true else cycleSubpaddingFuel source target i' j' (fuel - 1)

def cycleSubpadding (source target : List Bool) (i j : Nat) : Bool :=
  cycleSubpaddingFuel source target i j (source.length * target.length + 1)

/-! Methods are in Julia source order. A source block remains visible when a runtime-only operation
cannot be represented without inventing Julia dispatch, GC, or pointer semantics. -/
mutual
/-
Julia source: base/reinterpretarray.jl:14-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwbits(S::Type, T::Type, U::Type)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret `", S, "` as `", T, "`, type `", U, "` is not a bits type")))
    end
```
-/
def m14_throwbits {α : Type} (_source _target _culprit : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:18-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwsize0(S::Type, T::Type, msg)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret a zero-dimensional `", S, "` array to `", T,
            "` which is of a ", msg, " size")))
    end
```
-/
def m18_throwsize0 {α : Type} (_source _target : TypeLayout) (_message : String) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:23-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwsingleton(S::Type, T::Type)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T, "` which is a singleton type")))
    end
```
-/
def m23_throwsingleton {α : Type} (_source _target : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:27-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwbitpadding(S::Type, T::Type, U::Type)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
            "` because type `", U, "` contains non-byte-aligned primitive fields")))
    end
```
-/
def m27_throwbitpadding {α : Type} (_source _target _culprit : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
        function thrownonint(S::Type, T::Type, dim)
            @noinline
            throw(ArgumentError(LazyString(
                "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
                "`. The resulting array would have a non-integral first dimension.")))
        end
        function throwaxes1(S::Type, T::Type, ax1)
            @noinline
            throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
                "` when the first axis is ", ax1, ". Try reshaping first.")))
        end
        isbitstype(T) || throwbits(S, T, T)
        isbitstype(S) || throwbits(S, T, S)
        has_bit_padding(T) && throwbitpadding(S, T, T)
        has_bit_padding(S) && throwbitpadding(S, T, S)
        (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
        if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
            ax1 = axes(a)[1]
            dim = length(ax1)
            if issingletontype(T)
                issingletontype(S) || throwsingleton(S, T)
            else
                rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
            end
            first(ax1) == 1 || throwaxes1(S, T, ax1)
        end
        readable = array_subpadding(T, S)
        writable = array_subpadding(S, T)
        new{T, N, S, A, false}(a, readable, writable)
    end
```
-/
def m73_reinterpret {T S A : Type} (target source : TypeLayout) (a : ArrayInput A) :
    RResult (ReinterpretArray T S (ArrayInput A)) := do
  if !target.isBits then m14_throwbits source target target
  if !source.isBits then m14_throwbits source target source
  if target.bitPadding then m27_throwbitpadding source target target
  if source.bitPadding then m27_throwbitpadding source target source
  if a.rank == 0 && target.alignedSize != source.alignedSize then
    m18_throwsize0 source target "different"
  if a.rank != 0 && source.alignedSize != target.alignedSize then
    if target.singleton then
      if !source.singleton then m23_throwsingleton source target
    else
      let remainder ← (JInt.remInt (a.firstAxis.length * source.alignedSize) target.alignedSize).mapError (fun _ => .divide)
      if remainder.val != 0 then m74_thrownonint source target a.firstAxis.length
    if a.firstAxis.first.val != 1 then m80_throwaxes1 source target a.firstAxis
  let readable ← m772_arraySubpadding target source
  let writable ← m772_arraySubpadding source target
  pure ⟨a, a.bytes, a.rank, target, source, readable, writable, false, false, a.size,
    [a.firstAxis]⟩
/-
Julia source: base/reinterpretarray.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function thrownonint(S::Type, T::Type, dim)
            @noinline
            throw(ArgumentError(LazyString(
                "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
                "`. The resulting array would have a non-integral first dimension.")))
        end
```
-/
def m74_thrownonint {α : Type} (_source _target : TypeLayout) (_dim : I64) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:80-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function throwaxes1(S::Type, T::Type, ax1)
            @noinline
            throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
                "` when the first axis is ", ax1, ". Try reshaping first.")))
        end
```
-/
def m80_throwaxes1 {α : Type} (_source _target : TypeLayout) (_axis : Axis) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
```
-/
def m104_reinterpretIdentity {A : Type} (array : A) : A := array
/-
Julia source: base/reinterpretarray.jl:107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
        function throwintmult(S::Type, T::Type)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
                aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
        end
        function throwsize1(a::AbstractArray, T::Type)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
                " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
                aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
        end
        function throwfromsingleton(S, T)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
                " requires that ", T, " be a singleton type, since ", S, " is one")))
        end
        isbitstype(T) || throwbits(S, T, T)
        isbitstype(S) || throwbits(S, T, S)
        has_bit_padding(T) && throwbitpadding(S, T, T)
        has_bit_padding(S) && throwbitpadding(S, T, S)
        if aligned_sizeof(S) == aligned_sizeof(T)
            N = ndims(a)
        elseif aligned_sizeof(S) > aligned_sizeof(T)
            issingletontype(T) && throwsingleton(S, T)
            rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
            N = ndims(a) + 1
        else
            issingletontype(S) && throwfromsingleton(S, T)
            rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
            N = ndims(a) - 1
            N > -1 || throwsize0(S, T, "larger")
            axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
        end
        readable = array_subpadding(T, S)
        writable = array_subpadding(S, T)
        new{T, N, S, A, true}(a, readable, writable)
    end
```
-/
def m107_reinterpretReshape {T S A : Type} (target source : TypeLayout) (a : ArrayInput A) :
    RResult (ReinterpretArray T S (ArrayInput A)) := do
  if !target.isBits then m14_throwbits source target target
  if !source.isBits then m14_throwbits source target source
  if target.bitPadding then m27_throwbitpadding source target target
  if source.bitPadding then m27_throwbitpadding source target source
  let rank ← if source.alignedSize == target.alignedSize then pure a.rank
    else if target.alignedSize < source.alignedSize then do
      if target.singleton then m23_throwsingleton source target
      let rem ← (JInt.remInt source.alignedSize target.alignedSize).mapError (fun _ => .divide)
      if rem.val != 0 then m108_throwintmult source target
      pure (a.rank + 1)
    else do
      if source.singleton then m119_throwfromsingleton source target
      let rem ← (JInt.remInt target.alignedSize source.alignedSize).mapError (fun _ => .divide)
      if rem.val != 0 then m108_throwintmult source target
      if a.rank == 0 then m18_throwsize0 source target "larger"
      let newRank := a.rank - 1
      let expected ← (JInt.div target.alignedSize source.alignedSize).mapError (fun _ => .divide)
      if a.firstAxis.first.val != 1 || a.firstAxis.length != expected then
        m113_throwsize1 a target
      pure newRank
  let readable ← m772_arraySubpadding target source
  let writable ← m772_arraySubpadding source target
  pure ⟨a, a.bytes, rank, target, source, readable, writable, true, false, a.size,
    [a.firstAxis]⟩
/-
Julia source: base/reinterpretarray.jl:108-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function throwintmult(S::Type, T::Type)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
                aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
        end
```
-/
def m108_throwintmult {α : Type} (_source _target : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function throwsize1(a::AbstractArray, T::Type)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
                " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
                aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
        end
```
-/
def m113_throwsize1 {α : Type} (_array : ArrayInput A) (_target : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:119-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function throwfromsingleton(S, T)
            @noinline
            throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
                " requires that ", T, " be a singleton type, since ", S, " is one")))
        end
```
-/
def m119_throwfromsingleton {α : Type} (_source _target : TypeLayout) : RResult α := .error .argument
/-
Julia source: base/reinterpretarray.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray{T}) where {T} = a
```
-/
def m145_reinterpretReshapeIdentity {A : Type} (array : A) : A := array
-- UNTRANSLATED: The Julia file declares this method without providing its body.
/-
Julia source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
```
-/
/-
Julia source: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{T}, a::NonReshapedReinterpretArray) where {T} = reinterpret(T, a.parent)
```
-/
def m190_reinterpretParent {T S A : Type} (target : TypeLayout)
    (a : ReinterpretArray T S (ArrayInput A)) : RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) :=
  if target.id == a.source.id then .ok (.parent a.parent)
  else (m73_reinterpret target a.source a.parent).map ReinterpretOutcome.view
/-
Julia source: base/reinterpretarray.jl:191-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reinterpret(::typeof(reshape), ::Type{T}, a::ReshapedReinterpretArray{S,N,P}) where {T,S,N,P}
    t, s, p = aligned_sizeof(T), aligned_sizeof(S), aligned_sizeof(P)
    return t == s || t == p || s == p ? reinterpret(reshape, T, a.parent) : ReinterpretArray{T}(reshape, a)
end
```
-/
def m191_reinterpretReshapedParent {T S P A : Type} (target : TypeLayout)
    (a : ReinterpretArray S P (ArrayInput A)) : RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A))
      (ReinterpretArray T S (ArrayInput (ReinterpretArray S P (ArrayInput A))))) := do
  if target.alignedSize == a.target.alignedSize || target.alignedSize == a.source.alignedSize ||
      a.target.alignedSize == a.source.alignedSize then
    if target.id == a.source.id then return .parent a.parent
    else return .view (← m107_reinterpretReshape target a.source a.parent)
  else
    let input : ArrayInput (ReinterpretArray S P (ArrayInput A)) :=
      ⟨a, a.bytes, a.rank, a.axes.headD a.parent.firstAxis, a.size⟩
    return .nested (← m107_reinterpretReshape target a.target input)
/-
Julia source: base/reinterpretarray.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strides(a::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}) = size_to_strides(1, size(a)...)
```
-/
def m207_strides {A : Type} (size : A → List I64)
    (sizeToStrides : I64 → List I64 → List I64) (a : A) : List I64 :=
  sizeToStrides (JInt.lit .i64 1) (size a)
/-
Julia source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
    k ≤ ndims(A) ? strides(A)[k] : length(A)
```
-/
def m208_stride {A K : Type} (ndims : A → I64) (strides : A → List I64)
    (length : A → I64) (lessEq : K → I64 → Bool) (get : List I64 → K → I64)
    (a : A) (k : K) : I64 :=
  if lessEq k (ndims a) then get (strides a) k else length a
/-
Julia source: base/reinterpretarray.jl:211-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function strides(a::ReinterpretArray{T,<:Any,S,<:AbstractArray{S},IsReshaped}) where {T,S,IsReshaped}
    _checkcontiguous(Bool, a) && return size_to_strides(1, size(a)...)
    stp = strides(parent(a))
    els, elp = aligned_sizeof(T), aligned_sizeof(S)
    els == elp && return stp # 0dim parent is also handled here.
    # Note: ep typically equals elp, but a custom strided parent may define elsize differently
    ep = elsize(parent(a))
    byte_strides = map(i -> i * ep, stp)
    IsReshaped && els < elp && return (1, _checked_strides(byte_strides, els)...)
    first(byte_strides) == elp || throw(ArgumentError("Parent must be contiguous in the 1st dimension!"))
    st′ = _checked_strides(tail(byte_strides), els)
    return IsReshaped ? st′ : (1, st′...)
end
```
-/
def m211_strides {T S A : Type} (contiguous : A → Bool)
    (sizeToStrides : I64 → List I64 → List I64) (parentStrides : A → List I64)
    (parentElsize : A → I64) (divrem : I64 → I64 → RResult (I64 × I64))
    (iszero : I64 → Bool) (a : ReinterpretArray T S A) : RResult (List I64) := do
  if contiguous a.parent then return sizeToStrides (JInt.lit .i64 1) a.size
  let stp := parentStrides a.parent
  let els := a.target.alignedSize
  let elp := a.source.alignedSize
  if els == elp then return stp
  let ep := parentElsize a.parent
  let byteStrides := stp.map (fun i => i * ep)
  if a.reshaped && els < elp then
    return JInt.lit .i64 1 :: (← m225_checkedStrides divrem iszero byteStrides els)
  if byteStrides.headD (JInt.lit .i64 0) != elp then .error .noncontiguous
  let st ← m225_checkedStrides divrem iszero (byteStrides.drop 1) els
  return if a.reshaped then st else JInt.lit .i64 1 :: st
/-
Julia source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _checked_strides(byte_strides::Tuple, els::Integer)
    drs = map(i -> divrem(i, els), byte_strides)
    all(i->iszero(i[2]), drs) ||
        throw(ArgumentError("Parent's strides could not be exactly divided!"))
    map(first, drs)
end
```
-/
def m225_checkedStrides {I : Type} (divrem : I → I → RResult (I × I))
    (iszero : I → Bool) (strides : List I) (els : I) : RResult (List I) := do
  let results ← strides.mapM (fun stride => divrem stride els)
  let exact := results.map (fun pair => iszero pair.2)
  if exact.all id then pure (results.map Prod.fst) else .error .nonIntegralStride
/-
Julia source: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::ReinterpretArray) = _checkcontiguous(Bool, parent(A))
```
-/
def m232_checkcontiguous {A : Type} (check : A → Bool) (a : A) : Bool := check a
/-
Julia source: base/reinterpretarray.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::ReinterpretArray, T::Type, d::Dims) = similar(a.parent, T, d)
```
-/
def m234_similar {A T D R : Type} (similar : A → T → D → R)
    (a : ReinterpretArray T S A) (type : T) (dims : D) : R := similar a.parent type dims
/-
Julia source: base/reinterpretarray.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{TA}, dims::Dims) where {T,N,O,P,TA<:ReinterpretArray{T,N,O,P}} = similar(P, dims)
```
-/
def m235_similarType {_T _N _O P TA D R : Type} (similar : P → D → R)
    (_type : TA) (dims : D) (parentType : P) : R := similar parentType dims
/-
Julia source: base/reinterpretarray.jl:237-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}
    # See comment in check_writable
    if !a.readable && !array_subpadding(T, S)
        throw(PaddingError(T, S))
    end
end
```
-/
def m237_checkReadable {T S A : Type} (a : ReinterpretArray T S A) : RResult Unit := do
  if !a.readable && !(← m772_arraySubpadding a.target a.source) then .error .padding else pure ()
/-
Julia source: base/reinterpretarray.jl:244-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}
    # `array_subpadding` is relatively expensive (compared to a simple arrayref),
    # so it is cached in the array. However, it is computable at compile time if,
    # inference has the types available. By using this form of the check, we can
    # get the best of both worlds for the success case. If the types were not
    # available to inference, we simply need to check the field (relatively cheap)
    # and if they were we should be able to fold this check away entirely.
    if !a.writable && !array_subpadding(S, T)
        throw(PaddingError(T, S))
    end
end
```
-/
def m244_checkWritable {T S A : Type} (a : ReinterpretArray T S A) : RResult Unit := do
  if !a.writable && !(← m772_arraySubpadding a.source a.target) then .error .padding else pure ()
/-
Julia source: base/reinterpretarray.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}} =
    IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
```
-/
def m263_indexStyle {A : Type} (parentStyle : A → IndexStyleModel) (parentType : A) : IndexStyleModel :=
  if parentStyle parentType == .linear then .linear else .cartesian
/-
Julia source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
    if aligned_sizeof(T) < aligned_sizeof(S)
        IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
        return IndexCartesian()
    end
    return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
end
```
-/
def m266_indexStyleReshaped {A : Type} (parentStyle : A → IndexStyleModel) (parentType : A)
    (targetSize sourceSize : Nat) : IndexStyleModel :=
  if targetSize < sourceSize then
    if parentStyle parentType == .linear then .staticCartesian (sourceSize / targetSize) else .cartesian
  else if parentStyle parentType == .linear then .linear else .cartesian
/-
Julia source: base/reinterpretarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
```
-/
def m273_combineStyle {K : Nat} (_left _right : IndexStyleModel) : IndexStyleModel := .staticCartesian K
/-
Julia source: base/reinterpretarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i::SCartesianIndex2) = i
```
-/
def m279_toIndex (index : SCartesianIndex2) : SCartesianIndex2 := index
/-
Julia source: base/reinterpretarray.jl:280-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
    i.i < K ? SCartesianIndex2{K}(i.i + 1, i.j) : SCartesianIndex2{K}(1, i.j + 1)
```
-/
def m280_nextIndex (K : I64) (index : SCartesianIndex2) : SCartesianIndex2 :=
  if index.i < K then ⟨index.i + JInt.lit .i64 1, index.j⟩
  else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩
/-
Julia source: base/reinterpretarray.jl:282-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
    i.i > 1 ? SCartesianIndex2{K}(i.i - 1, i.j) : SCartesianIndex2{K}(K, i.j - 1)
```
-/
def m282_prevIndex (K : I64) (index : SCartesianIndex2) : SCartesianIndex2 :=
  if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
  else ⟨K, index.j - JInt.lit .i64 1⟩
/-
Julia source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
```
-/
def m288_indicesConstructor (K : Nat) (indices : List I64) : RResult (SCartesianIndices2 K) :=
  if 1 < K then .ok ⟨indices⟩ else .error .assertion
/-
Julia source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
```
-/
def m290_eachindexReshaped {A : Type} {K : Nat} (each : IndexStyleModel → A → List I64)
    (construct : List I64 → RResult (SCartesianIndices2 K)) (a : ReinterpretArray T S A) : RResult (SCartesianIndices2 K) :=
  construct (each .linear a.parent)
/-
Julia source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
    iter = eachindex(style, A)
    itersBs = map(C->eachindex(style, C), B)
    all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
    return iter
end
```
-/
def m291_eachindex {A : Type} {K : Nat} (each : IndexStyleModel → A → List I64)
    (mismatch : List Axis → List (List Axis) → RResult (SCartesianIndices2 K))
    (style : IndexStyleModel) (a : A) (rest : List A) (axes : A → List Axis) : RResult (SCartesianIndices2 K) := do
  let iter := each style a
  let others := rest.map (each style)
  if others.all (· == iter) then .ok ⟨iter⟩ else mismatch (axes a) (rest.map axes)
/-
Julia source: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
```
-/
def m298_indicesSize {K : Nat} (iter : SCartesianIndices2 K) : Nat × Nat :=
  (K, iter.indices2.length)
/-
Julia source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
```
-/
def m299_indicesAxes {K : Nat} (iter : SCartesianIndices2 K) : List Axis :=
  [⟨JInt.lit .i64 1, JInt.lit .i64 K⟩, ⟨JInt.lit .i64 1, JInt.lit .i64 iter.indices2.length⟩]
/-
Julia source: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
```
-/
def m301_indicesFirst {K : Nat} (first : List I64 → RResult I64)
    (iter : SCartesianIndices2 K) : RResult SCartesianIndex2 := do
  let item ← first iter.indices2
  pure ⟨JInt.lit .i64 1, item⟩
/-
Julia source: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
```
-/
def m302_indicesLast {K : Nat} (last : List I64 → RResult I64)
    (iter : SCartesianIndices2 K) : RResult SCartesianIndex2 := do
  let item ← last iter.indices2
  pure ⟨JInt.lit .i64 K, item⟩
/-
Julia source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
    @boundscheck checkbounds(iter, i, j)
    return SCartesianIndex2{K}(i, iter.indices2[j])
end
```
-/
def m304_indicesGet {K : Nat} (checkbounds : SCartesianIndices2 K → I64 → I64 → Bool)
    (get : List I64 → I64 → RResult I64) (iter : SCartesianIndices2 K) (i j : I64) : RResult SCartesianIndex2 := do
  if checkbounds iter i j then pure () else .error .bounds
  let item ← get iter.indices2 j
  pure ⟨i, item⟩
/-
Julia source: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(iter::SCartesianIndices2{K}) where {K}
    ret = iterate(iter.indices2)
    ret === nothing && return nothing
    item2, state2 = ret
    return SCartesianIndex2{K}(1, item2), (1, item2, state2)
end
```
-/
def m309_indicesIterate {K : Nat} (iterate : List I64 → Option (I64 × σ))
    (iter : SCartesianIndices2 K) : Option (SCartesianIndex2 × (I64 × I64 × σ)) :=
  match iterate iter.indices2 with
  | none => none
  | some (item, state) => some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))
/-
Julia source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
    if state1 < K
        item1 = state1 + 1
        return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
    end
    ret = iterate(iter.indices2, state2)
    ret === nothing && return nothing
    item2, state2 = ret
    return SCartesianIndex2{K}(1, item2), (1, item2, state2)
end
```
-/
def m316_indicesIterateState {K : Nat} (iterate : List I64 → σ → Option (I64 × σ))
    (iter : SCartesianIndices2 K) (state1 item2 : I64) (state2 : σ) :
    Option (SCartesianIndex2 × (I64 × I64 × σ)) :=
  if state1 < JInt.lit .i64 K then
    let item1 := state1 + JInt.lit .i64 1
    some (⟨item1, item2⟩, (item1, item2, state2))
  else match iterate iter.indices2 state2 with
    | none => none
    | some (item, state) => some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))
/-
Julia source: base/reinterpretarray.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimdLoop.simd_outer_range(iter::SCartesianIndices2) = iter.indices2
```
-/
def m327_simdOuter {K : Nat} (iter : SCartesianIndices2 K) : List I64 := iter.indices2
/-
Julia source: base/reinterpretarray.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimdLoop.simd_inner_length(::SCartesianIndices2{K}, ::Any) where K = K
```
-/
def m328_simdInnerLength {K : Nat} (_iter : SCartesianIndices2 K) (_ : α) : Nat := K
/-
Julia source: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}
    SCartesianIndex2{K}(I1+1, Ilast)
end
```
-/
def m329_simdIndex {_K : Nat} (_last i1 : I64) : SCartesianIndex2 :=
  ⟨i1 + JInt.lit .i64 1, _last⟩
/-
Julia source: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...) = _maybe_reshape(IndexCartesian(), A, I...)
```
-/
def m333_maybeReshape {A R : Type} (fallback : IndexStyleModel → A → List I64 → R)
    (a : A) (indices : List I64) : R := fallback .cartesian a indices
/-
Julia source: base/reinterpretarray.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexSCartesian2, A::ReshapedReinterpretArray, I...) = A
```
-/
def m334_maybeReshapeIdentity {A : Type} (a : A) (_indices : List I64) : A := a
/-
Julia source: base/reinterpretarray.jl:337-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(::IndexSCartesian2, A::AbstractArray, I::Vararg{Int, N}) where {N}
    @_propagate_inbounds_meta
    _getindex(IndexCartesian(), A, I...)
end
```
-/
def m337_getindexFallback {A R : Type} (getCartesian : A → List I64 → R)
    (a : A) (indices : List I64) : R := getCartesian a indices
/-
Julia source: base/reinterpretarray.jl:341-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(::IndexSCartesian2, A::AbstractArray, v, I::Vararg{Int, N}) where {N}
    @_propagate_inbounds_meta
    _setindex!(IndexCartesian(), A, v, I...)
end
```
-/
def m341_setindexFallback {A V R : Type} (setCartesian : A → V → List I64 → R)
    (a : A) (value : V) (indices : List I64) : R := setCartesian a value indices
/-
Julia source: base/reinterpretarray.jl:347-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(style::IndexSCartesian2, A::AbstractArray, ind::SCartesianIndex2)
    @_propagate_inbounds_meta
    getindex(A, first(axes(A, 1)) + ind.i - 1, _scartesian2_trailing(style, A, ind)...)
end
```
-/
def m347_getindexCartesian {A R : Type} (firstAxis : A → I64)
    (eachOuter : IndexStyleModel → A → List I64) (axes : A → List Axis)
    (first : List I64 → I64) (cartesianIndices : List Axis → I64 → List I64)
    (getindex : A → List I64 → R) (style : IndexStyleModel) (a : A)
    (index : SCartesianIndex2) : R :=
  getindex a ((firstAxis a + index.i - JInt.lit .i64 1) ::
    m359_scartesian2Trailing eachOuter axes first cartesianIndices style a index)
/-
Julia source: base/reinterpretarray.jl:352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(style::IndexSCartesian2, A::AbstractArray, v, ind::SCartesianIndex2)
    @_propagate_inbounds_meta
    setindex!(A, v, first(axes(A, 1)) + ind.i - 1, _scartesian2_trailing(style, A, ind)...)
end
```
-/
def m352_setindexCartesian {A V R : Type} (firstAxis : A → I64)
    (eachOuter : IndexStyleModel → A → List I64) (axes : A → List Axis)
    (first : List I64 → I64) (cartesianIndices : List Axis → I64 → List I64)
    (setindex : A → V → List I64 → R) (style : IndexStyleModel) (a : A) (value : V)
    (index : SCartesianIndex2) : R :=
  setindex a value ((firstAxis a + index.i - JInt.lit .i64 1) ::
    m359_scartesian2Trailing eachOuter axes first cartesianIndices style a index)
/-
Julia source: base/reinterpretarray.jl:359-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _scartesian2_trailing(style::IndexSCartesian2, A::AbstractArray, ind::SCartesianIndex2)
    k = ind.j - first(eachindex(style, A).indices2)
    ax = tail(axes(A))
    return length(ax) == 1 ? (first(ax[1]) + k,) : Tuple(CartesianIndices(ax)[k + 1])
end
```
-/
def m359_scartesian2Trailing {A : Type} (eachOuter : IndexStyleModel → A → List I64)
    (axes : A → List Axis) (first : List I64 → I64)
    (cartesianIndices : List Axis → I64 → List I64)
    (style : IndexStyleModel) (a : A) (index : SCartesianIndex2) : List I64 :=
  let k := index.j - first (eachOuter style a)
  let tailAxes := (axes a).drop 1
  match tailAxes with
  | [axis] => [axis.first + k]
  | _ => cartesianIndices tailAxes (k + JInt.lit .i64 1)
/-
Julia source: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(style::IndexSCartesian2, A::AbstractArray) = eachindex(style, parent(A))
```
-/
def m365_eachindex {A R : Type} (each : IndexStyleModel → A → R)
    (style : IndexStyleModel) (a : ReinterpretArray T S A) : R := each style a.parent
/-
Julia source: base/reinterpretarray.jl:369-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(a::ReinterpretArray) = a.parent
```
-/
def m369_parent {T S A : Type} (a : ReinterpretArray T S A) : A := a.parent
/-
Julia source: base/reinterpretarray.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(a::ReinterpretArray) = dataids(a.parent)
```
-/
def m370_dataids {T S A R : Type} (dataids : A → R) (a : ReinterpretArray T S A) : R := dataids a.parent
/-
Julia source: base/reinterpretarray.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(a::NonReshapedReinterpretArray{T}) where {T} = reinterpret(T, unaliascopy(a.parent))
```
-/
def m371_unaliascopy {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) := do
  let p ← copy a.parent
  if a.target.id == a.source.id then return .parent p
  return .view (← m73_reinterpret a.target a.source p)
/-
Julia source: base/reinterpretarray.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(a::ReshapedReinterpretArray{T}) where {T} = reinterpret(reshape, T, unaliascopy(a.parent))
```
-/
def m372_unaliascopyReshaped {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) := do
  let p ← copy a.parent
  if a.target.id == a.source.id then return .parent p
  return .view (← m107_reinterpretReshape a.target a.source p)
/-
Julia source: base/reinterpretarray.jl:374-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function size(a::NonReshapedReinterpretArray{T,N,S} where {N}) where {T,S}
    psize = size(a.parent)
    size1 = issingletontype(T) ? psize[1] : div(psize[1]*aligned_sizeof(S), aligned_sizeof(T))
    tuple(size1, tail(psize)...)
end
```
-/
def m374_sizeNonReshaped {T S A : Type} (divide : I64 → I64 → RResult I64)
    (a : ReinterpretArray T S A) : RResult (List I64) := do
  let psize := a.size
  let size1 ← if a.target.singleton then pure (psize.getD 0 (JInt.lit .i64 0))
    else divide ((psize.getD 0 (JInt.lit .i64 0)) * a.source.alignedSize) a.target.alignedSize
  pure (size1 :: psize.drop 1)
/-
Julia source: base/reinterpretarray.jl:379-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function size(a::ReshapedReinterpretArray{T,N,S} where {N}) where {T,S}
    psize = size(a.parent)
    aligned_sizeof(S) > aligned_sizeof(T) && return (div(aligned_sizeof(S), aligned_sizeof(T)), psize...)
    aligned_sizeof(S) < aligned_sizeof(T) && return tail(psize)
    return psize
end
```
-/
def m379_sizeReshaped {T S A : Type} (divide : I64 → I64 → RResult I64)
    (a : ReinterpretArray T S A) : RResult (List I64) := do
  let psize := a.size
  if a.source.alignedSize > a.target.alignedSize then
    let ratio ← divide a.source.alignedSize a.target.alignedSize
    pure (ratio :: psize)
  else if a.source.alignedSize < a.target.alignedSize then pure (psize.drop 1)
  else pure psize
/-
Julia source: base/reinterpretarray.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::NonReshapedReinterpretArray{T,0}) where {T} = ()
```
-/
def m385_sizeZero {T S A : Type} (_a : ReinterpretArray T S A) : List I64 := []
/-
Julia source: base/reinterpretarray.jl:387-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(a::NonReshapedReinterpretArray{T,N,S} where {N}) where {T,S}
    paxs = axes(a.parent)
    f, l = first(paxs[1]), length(paxs[1])
    size1 = issingletontype(T) ? l : div(l*aligned_sizeof(S), aligned_sizeof(T))
    tuple(oftype(paxs[1], f:f+size1-1), tail(paxs)...)
end
```
-/
def m387_axesNonReshaped {T S A : Type} (divide : I64 → I64 → RResult I64)
    (oftype : Axis → I64 → Axis) (a : ReinterpretArray T S A) : RResult (List Axis) := do
  let paxs := a.axes
  let axis := paxs.headD ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
  let size1 ← if a.target.singleton then pure axis.length
    else divide (axis.length * a.source.alignedSize) a.target.alignedSize
  pure (oftype axis size1 :: paxs.drop 1)
/-
Julia source: base/reinterpretarray.jl:393-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function axes(a::ReshapedReinterpretArray{T,N,S} where {N}) where {T,S}
    paxs = axes(a.parent)
    aligned_sizeof(S) > aligned_sizeof(T) && return (OneTo(div(aligned_sizeof(S), aligned_sizeof(T))), paxs...)
    aligned_sizeof(S) < aligned_sizeof(T) && return tail(paxs)
    return paxs
end
```
-/
def m393_axesReshaped {T S A : Type} (divide : I64 → I64 → RResult I64)
    (a : ReinterpretArray T S A) : RResult (List Axis) := do
  let paxs := a.axes
  if a.source.alignedSize > a.target.alignedSize then
    let ratio ← divide a.source.alignedSize a.target.alignedSize
    pure (⟨JInt.lit .i64 1, ratio⟩ :: paxs)
  else if a.source.alignedSize < a.target.alignedSize then pure (paxs.drop 1)
  else pure paxs
/-
Julia source: base/reinterpretarray.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(a::NonReshapedReinterpretArray{T,0}) where {T} = ()
```
-/
def m399_axesZero {T S A : Type} (_a : ReinterpretArray T S A) : List Axis := []
/-
Julia source: base/reinterpretarray.jl:401-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(a::ReinterpretArray) = has_offset_axes(a.parent)
```
-/
def m401_hasOffset {T S A R : Type} (hasOffset : A → R) (a : ReinterpretArray T S A) : R := hasOffset a.parent
/-
Julia source: base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function elsize(::Type{<:ReinterpretArray{T,<:Any,S,A}}) where {T,S,A}
    if aligned_sizeof(T) == aligned_sizeof(S)
        elsize(A)
    else
        aligned_sizeof(T)
    end
end
```
-/
def m403_elsize (parentElsize : Nat) (targetSize sourceSize : Nat) : Nat :=
  if targetSize == sourceSize then parentElsize else targetSize
/-
Julia source: base/reinterpretarray.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = cconvert(Ptr{S}, a.parent)
```
-/
def m410_cconvert {T S A R : Type} (cconvert : TypeLayout → A → R)
    (a : ReinterpretArray T S A) : R := cconvert a.source a.parent
/-
Julia source: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = Ptr{T}(unsafe_convert(Ptr{S},a.parent))
```
-/
def m411_unsafeConvert {T S A R : Type} (unsafeConvert : TypeLayout → A → R)
    (castPointer : TypeLayout → R → R) (target : TypeLayout) (a : ReinterpretArray T S A) : R :=
  castPointer target (unsafeConvert a.source a.parent)
/-
Julia source: base/reinterpretarray.jl:413-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(a::NonReshapedReinterpretArray{T,0,S}) where {T,S}
    if _is_scalar_reinterpret_applicable(T, S)
        reinterpret(T, a.parent[])
    else
        a[firstindex(a)]
    end
end
```
-/
def m413_getindexZero {T S A : Type} (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (parentIndexStyle : A → IndexStyleModel) (ops : PointerReadOps A)
    (firstindex : ReinterpretArray T S A → I64) (a : ReinterpretArray T S A) : RResult Bytes := do
  if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent (JInt.lit .i64 1) []
    m882_reinterpret (fun t => t.fields.length) (fun t i => (t.fields.getD i ⟨0,0,true,[],false⟩).offset) fieldtype a.target a.source bytes
  else m442_getindexLinear ops parentIndexStyle (fun _ _ => []) firstindex (fun arr i _ => checkbounds arr i []) fieldtype getParent a (firstindex a)
/-
Julia source: base/reinterpretarray.jl:421-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_ptr_indexable(a::ReinterpretArray{T,<:Any,S}) where {T,S}
    aligned_sizeof(T) === aligned_sizeof(S) && return false
    return check_ptr_indexable(parent(a))
end
```
-/
def m421_checkPtrIndexable {T S A : Type} (a : ReinterpretArray T S A) : Bool :=
  if a.target.alignedSize == a.source.alignedSize then false else a.pointerParent
/-
Julia source: base/reinterpretarray.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::ReshapedArray) = check_ptr_indexable(parent(a))
```
-/
def m425_checkPtrReshaped {A : Type} (checkParent : A → Bool) (a : A) : Bool := checkParent a
/-
Julia source: base/reinterpretarray.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::FastContiguousSubArray) = check_ptr_indexable(parent(a))
```
-/
def m426_checkPtrSubarray {A : Type} (checkParent : A → Bool) (a : A) : Bool := checkParent a
/-
Julia source: base/reinterpretarray.jl:427-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::Union{Array, Memory}) = true
```
-/
def m427_checkPtrDense (_a : A) : Bool := true
/-
Julia source: base/reinterpretarray.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::AbstractArray) = false
```
-/
def m428_checkPtrAbstract (_a : A) : Bool := false
/-
Julia source: base/reinterpretarray.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(a::ReshapedReinterpretArray{T,0}) where {T} = a[firstindex(a)]
```
-/
def m430_getindexZeroReshaped {T S A : Type} (ops : PointerReadOps A)
    (parentIndexStyle : A → IndexStyleModel) (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → I64 → List I64 → RResult Bytes) (a : ReinterpretArray T S A) : RResult Bytes :=
  m442_getindexLinear ops parentIndexStyle toSubscripts firstindex checkbounds
    (fun t _ => t) getParent a (firstindex a)
/-
Julia source: base/reinterpretarray.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isassigned(a::ReinterpretArray, inds::Integer...) = checkbounds(Bool, a, inds...) && (check_ptr_indexable(a) || _isassigned_ra(a, inds...))
```
-/
def m432_isassigned {T S A : Type} (checkbounds : ReinterpretArray T S A → List I64 → Bool)
    (a : ReinterpretArray T S A) (indices : List I64) : Bool :=
  checkbounds a indices && (m421_checkPtrIndexable a || m434_isassignedRa a indices)
/-
Julia source: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isassigned(a::ReinterpretArray, inds::SCartesianIndex2) = isassigned(a.parent, inds.j)
```
-/
def m433_isassignedCartesian {T S A : Type} (parentAssigned : A → I64 → Bool)
    (a : ReinterpretArray T S A) (index : SCartesianIndex2) : Bool := parentAssigned a.parent index.j
/-
Julia source: base/reinterpretarray.jl:434-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds _isassigned_ra(a::ReinterpretArray, inds...) = true # that is not entirely true, but computing exactly which indexes will be accessed in the parent requires a lot of duplication from the _getindex_ra code
```
-/
def m434_isassignedRa {T S A : Type} (_a : ReinterpretArray T S A) (_indices : List I64) : Bool := true
/-
Julia source: base/reinterpretarray.jl:436-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(a::ReinterpretArray{T,N,S}, inds::Vararg{Int, N}) where {T,N,S}
    check_readable(a)
    check_ptr_indexable(a) && return _getindex_ptr(a, inds...)
    _getindex_ra(a, inds[1], tail(inds))
end
```
-/
def m436_getindex {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (ops : PointerReadOps A) (parentIndexStyle : A → IndexStyleModel)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes) (i1 : I64) (tail : List I64)
    (a : ReinterpretArray T S A) : RResult Bytes := do
  m237_checkReadable a
  if m421_checkPtrIndexable a then m461_getindexPtr ops a (i1 :: tail)
  else if a.reshaped then
    m527_getindexReshaped checkbounds fieldtype getParent parentIndexStyle a i1 tail
  else m473_getindexNonReshaped checkbounds fieldtype getParent a i1 tail
/-
Julia source: base/reinterpretarray.jl:442-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(a::ReinterpretArray{T,N,S}, i::Int) where {T,N,S}
    check_readable(a)
    check_ptr_indexable(a) && return _getindex_ptr(a, i)
    if isa(IndexStyle(a), IndexLinear)
        return _getindex_ra(a, i, ())
    end
    # Convert to full indices here, to avoid needing multiple conversions in
    # the loop in _getindex_ra
    inds = _to_subscript_indices(a, i)
    isempty(inds) ? _getindex_ra(a, firstindex(a), ()) : _getindex_ra(a, inds[1], tail(inds))
end
```
-/
def m442_getindexLinear {T S A : Type} (ops : PointerReadOps A)
    (parentIndexStyle : A → IndexStyleModel) (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes) (a : ReinterpretArray T S A) (i : I64) : RResult Bytes := do
  m237_checkReadable a
  if m421_checkPtrIndexable a then m461_getindexPtr ops a [i]
  else if parentIndexStyle a.parent == .linear then
    if a.reshaped then m527_getindexReshaped checkbounds fieldtype getParent parentIndexStyle a i []
    else m473_getindexNonReshaped checkbounds fieldtype getParent a i []
  else
    let inds := toSubscripts a i
    if inds.isEmpty then
      if a.reshaped then m527_getindexReshaped checkbounds fieldtype getParent parentIndexStyle a (firstindex a) []
      else m473_getindexNonReshaped checkbounds fieldtype getParent a (firstindex a) []
    else
      let first := inds.headD (JInt.lit .i64 1)
      let rest := inds.drop 1
      if a.reshaped then m527_getindexReshaped checkbounds fieldtype getParent parentIndexStyle a first rest
      else m473_getindexNonReshaped checkbounds fieldtype getParent a first rest
/-
Julia source: base/reinterpretarray.jl:454-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(a::ReshapedReinterpretArray{T,N,S}, ind::SCartesianIndex2) where {T,N,S}
    check_readable(a)
    s = Ref{S}(a.parent[ind.j])
    tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
    GC.@preserve s return unsafe_load(tptr, ind.i)
end
```
-/
def m454_getindexCartesian {T S A : Type} (parentGet : A → I64 → RResult Bytes)
    (loadElement : Bytes → I64 → RResult Bytes)
    (a : ReinterpretArray T S A) (index : SCartesianIndex2) : RResult Bytes := do
  m237_checkReadable a
  let s ← parentGet a.parent index.j
  loadElement s index.i
/-
Julia source: base/reinterpretarray.jl:461-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _getindex_ptr(a::ReinterpretArray{T}, inds...) where {T}
    @boundscheck checkbounds(a, inds...)
    li = _to_linear_index(a, inds...)
    ap = cconvert(Ptr{T}, a)
    p = unsafe_convert(Ptr{T}, ap) + elsize(a) * (li - firstindex(a))
    GC.@preserve ap return unsafe_load(p)
end
```
-/
def m461_getindexPtr {T S A : Type} (ops : PointerReadOps A)
    (a : ReinterpretArray T S A) (indices : List I64) : RResult Bytes := do
  match ops with
  | .mk checkbounds linearIndex cconvert unsafeConvert elsize firstindex addPointer unsafeLoad => do
    checkbounds a.parent indices
    let li := linearIndex a.parent indices
    let ap := cconvert a.parent
    let ptr := unsafeConvert ap
    let p := addPointer ptr (elsize a.parent * (li - firstindex a.parent))
    unsafeLoad p
/-
Julia source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _is_scalar_reinterpret_applicable(T, S)
    isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
end
```
-/
def m469_scalarApplicable (target source : TypeLayout) : Bool :=
  target.primitive && source.primitive && target.bits == source.bits
/-
Julia source: base/reinterpretarray.jl:473-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _getindex_ra(a::NonReshapedReinterpretArray{T,N,S}, i1::Int, tailinds::TT) where {T,N,S,TT}
    if issingletontype(T) # singleton types
        @boundscheck checkbounds(a, i1, tailinds...)
        return T.instance
    elseif _is_scalar_reinterpret_applicable(T, S)
        return reinterpret(T, a.parent[i1, tailinds...])
    else
        @boundscheck checkbounds(a, i1, tailinds...)
        ind_start, sidx = divrem((i1-1)*aligned_sizeof(T), aligned_sizeof(S))
        # Optimizations that avoid branches
        if aligned_sizeof(T) % aligned_sizeof(S) == 0
            # T is bigger than S and contains an integer number of them
            n = aligned_sizeof(T) ÷ aligned_sizeof(S)
            t = Ref{T}()
            GC.@preserve t begin
                sptr = Ptr{S}(unsafe_convert(Ref{T}, t))
                for i = 1:n
                     s = a.parent[ind_start + i, tailinds...]
                     unsafe_store!(sptr, s, i)
                end
            end
            return t[]
        elseif aligned_sizeof(S) % aligned_sizeof(T) == 0
            # S is bigger than T and contains an integer number of them
            s = Ref{S}(a.parent[ind_start + 1, tailinds...])
            GC.@preserve s begin
                tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
                return unsafe_load(tptr + sidx)
            end
        else
            i = 1
            nbytes_copied = 0
            # This is a bit complicated to deal with partial elements
            # at both the start and the end. LLVM will fold as appropriate,
            # once it knows the data layout
            s = Ref{S}()
            t = Ref{T}()
            GC.@preserve s t begin
                sptr = Ptr{S}(unsafe_convert(Ref{S}, s))
                tptr = Ptr{T}(unsafe_convert(Ref{T}, t))
                while nbytes_copied < aligned_sizeof(T)
                    s[] = a.parent[ind_start + i, tailinds...]
                    nb = min(aligned_sizeof(S) - sidx, aligned_sizeof(T)-nbytes_copied)
                    memcpy(tptr + nbytes_copied, sptr + sidx, nb)
                    nbytes_copied += nb
                    sidx = 0
                    i += 1
                end
            end
            return t[]
        end
    end
end
```
-/
def m473_getindexNonReshaped {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes) (a : ReinterpretArray T S A)
    (i1 : I64) (tail : List I64) : RResult Bytes := do
  if a.target.singleton then
    checkbounds a i1 tail
    return []
  if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent i1 tail
    return ← m882_reinterpret (fun t => t.fields.length) (fun t i => (t.fields.getD i ⟨0,0,true,[],false⟩).offset) fieldtype a.target a.source bytes
  checkbounds a i1 tail
  let ts := a.target.alignedSize.val.toNat
  let ss := a.source.alignedSize.val.toNat
  let byteOffset := (i1.val - 1).toNat * ts
  let start := byteOffset / ss
  let offset := byteOffset % ss
  if ts % ss == 0 then
    let n := ts / ss
    let mut result : Bytes := []
    for j in List.range n do
      let bytes ← getParent a.parent (JInt.lit .i64 (start + j + 1)) tail
      result := result ++ bytes
    return result
  else if ss % ts == 0 then
    let bytes ← getParent a.parent (JInt.lit .i64 (start + 1)) tail
    return (bytes.drop offset).take ts
  else
    let mut copied := 0
    let mut sourceOffset := offset
    let mut element := start
    let mut result : Bytes := []
    while copied < ts do
      let bytes ← getParent a.parent (JInt.lit .i64 (element + 1)) tail
      let n := min (ss - sourceOffset) (ts - copied)
      result := result ++ (bytes.drop sourceOffset).take n
      copied := copied + n
      sourceOffset := 0
      element := element + 1
    return result
/-
Julia source: base/reinterpretarray.jl:527-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _getindex_ra(a::ReshapedReinterpretArray{T,N,S}, i1::Int, tailinds::TT) where {T,N,S,TT}
    if issingletontype(T) # singleton types
        @boundscheck checkbounds(a, i1, tailinds...)
        return T.instance
    elseif _is_scalar_reinterpret_applicable(T, S)
        return reinterpret(T, a.parent[i1, tailinds...])
    end
    @boundscheck checkbounds(a, i1, tailinds...)
    if aligned_sizeof(T) >= aligned_sizeof(S)
        t = Ref{T}()
        GC.@preserve t begin
            sptr = Ptr{S}(unsafe_convert(Ref{T}, t))
            if aligned_sizeof(T) > aligned_sizeof(S)
                # Extra dimension in the parent array
                n = aligned_sizeof(T) ÷ aligned_sizeof(S)
                if isempty(tailinds) && IndexStyle(a.parent) === IndexLinear()
                    offset = n * (i1 - firstindex(a))
                    for i = 1:n
                        s = a.parent[i + offset]
                        unsafe_store!(sptr, s, i)
                    end
                else
                    for i = 1:n
                        s = a.parent[i, i1, tailinds...]
                        unsafe_store!(sptr, s, i)
                    end
                end
            else
                # No extra dimension
                s = a.parent[i1, tailinds...]
                unsafe_store!(sptr, s)
            end
        end
        return t[]
    end
    # S is bigger than T and contains an integer number of them
    # n = aligned_sizeof(S) ÷ aligned_sizeof(T)
    s = Ref{S}()
    GC.@preserve s begin
        tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
        s[] = a.parent[tailinds...]
        return unsafe_load(tptr, i1)
    end
end
```
-/
def m527_getindexReshaped {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (getParent : A → I64 → List I64 → RResult Bytes) (parentIndexStyle : A → IndexStyleModel)
    (a : ReinterpretArray T S A) (i1 : I64) (tail : List I64) : RResult Bytes := do
  if a.target.singleton then
    checkbounds a i1 tail
    return []
  if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent i1 tail
    return ← m882_reinterpret (fun t => t.fields.length) (fun t i => (t.fields.getD i ⟨0,0,true,[],false⟩).offset) fieldtype a.target a.source bytes
  checkbounds a i1 tail
  let ts := a.target.alignedSize.val.toNat
  let ss := a.source.alignedSize.val.toNat
  if ts >= ss then
    let n := ts / ss
    let mut result : Bytes := []
    for j in List.range n do
      let index := if ts > ss && tail.isEmpty && parentIndexStyle a.parent == .linear then
        (n * (i1.val - 1).toNat + j + 1, []) else (j + 1, i1 :: tail)
      let bytes ← getParent a.parent (JInt.lit .i64 index.1) index.2
      result := result ++ bytes
    return result
  let bytes ← getParent a.parent (JInt.lit .i64 0) tail
  return (bytes.drop ((i1.val - 1).toNat * ts)).take ts
/-
Julia source: base/reinterpretarray.jl:572-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(a::NonReshapedReinterpretArray{T,0,S}, v) where {T,S}
    if _is_scalar_reinterpret_applicable(T, S)
        a.parent[] = reinterpret(S, convert(T, v)::T)
        return a
    end
    setindex!(a, v, firstindex(a))
end
```
-/
def m572_setindexZero {T S A V : Type} (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (isScalar : TypeLayout → TypeLayout → Bool)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (parentIndexStyle : A → IndexStyleModel)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) : RResult (ReinterpretArray T S A) := do
  if isScalar a.target a.source then
    let bytes ← convertValue a.target value
    let sourceBytes ← m882_reinterpret fieldcount fieldoffset fieldtype a.source a.target bytes
    let changed := overwriteBytes a.bytes 0 sourceBytes
    let parent ← setParent a.parent changed
    pure { a with parent := parent, bytes := changed }
  else
    m588_setindexLinear checkWritable ops parentIndexStyle toSubscripts firstindex
      fieldcount fieldoffset fieldtype convertValue setParent checkbounds a value (firstindex a)
/-
Julia source: base/reinterpretarray.jl:580-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds setindex!(a::ReshapedReinterpretArray{T,0}, v) where {T} = setindex!(a, v, firstindex(a))
```
-/
def m580_setindexZeroReshaped {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (parentIndexStyle : A → IndexStyleModel)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) : RResult (ReinterpretArray T S A) :=
  m588_setindexLinear checkWritable ops parentIndexStyle toSubscripts firstindex
    fieldcount fieldoffset fieldtype convertValue setParent checkbounds a value (firstindex a)
/-
Julia source: base/reinterpretarray.jl:582-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(a::ReinterpretArray{T,N,S}, v, inds::Vararg{Int, N}) where {T,N,S}
    check_writable(a)
    check_ptr_indexable(a) && return _setindex_ptr!(a, v, inds...)
    _setindex_ra!(a, v, inds[1], tail(inds))
end
```
-/
def m582_setindex {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (convertValue : TypeLayout → V → RResult Bytes)
    (setParent : A → Bytes → RResult A) (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  checkWritable a
  if m421_checkPtrIndexable a then m610_setindexPtr ops a (← convertValue a.target value) (i1 :: tail)
  else if a.reshaped then m688_setindexReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value i1 tail
  else m619_setindexNonReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value i1 tail
/-
Julia source: base/reinterpretarray.jl:588-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(a::ReinterpretArray{T,N,S}, v, i::Int) where {T,N,S}
    check_writable(a)
    check_ptr_indexable(a) && return _setindex_ptr!(a, v, i)
    if isa(IndexStyle(a), IndexLinear)
        return _setindex_ra!(a, v, i, ())
    end
    inds = _to_subscript_indices(a, i)
    isempty(inds) ? _setindex_ra!(a, v, firstindex(a), ()) : _setindex_ra!(a, v, inds[1], tail(inds))
end
```
-/
def m588_setindexLinear {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (ops : PointerWriteOps A) (parentIndexStyle : A → IndexStyleModel)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (firstindex : ReinterpretArray T S A → I64)
    (fieldcount : TypeLayout → Nat) (fieldoffset : TypeLayout → Nat → Nat)
    (fieldtype : TypeLayout → Nat → TypeLayout) (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (a : ReinterpretArray T S A) (value : V) (i : I64) : RResult (ReinterpretArray T S A) := do
  checkWritable a
  if m421_checkPtrIndexable a then m610_setindexPtr ops a (← convertValue a.target value) [i]
  else if parentIndexStyle a.parent == .linear then
    if a.reshaped then m688_setindexReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value i []
    else m619_setindexNonReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value i []
  else
    let inds := toSubscripts a i
    let first := if inds.isEmpty then firstindex a else inds.headD (JInt.lit .i64 1)
    let rest := if inds.isEmpty then [] else inds.drop 1
    if a.reshaped then m688_setindexReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value first rest
    else m619_setindexNonReshaped fieldcount fieldoffset fieldtype checkbounds convertValue setParent a value first rest
/-
Julia source: base/reinterpretarray.jl:598-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(a::ReshapedReinterpretArray{T,N,S}, v, ind::SCartesianIndex2) where {T,N,S}
    check_writable(a)
    v = convert(T, v)::T
    s = Ref{S}(a.parent[ind.j])
    GC.@preserve s begin
        tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
        unsafe_store!(tptr, v, ind.i)
    end
    a.parent[ind.j] = s[]
    return a
end
```
-/
def m598_setindexCartesian {T S A V : Type} (checkWritable : ReinterpretArray T S A → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parentGet : A → I64 → RResult Bytes)
    (parentSet : A → I64 → Bytes → RResult A) (a : ReinterpretArray T S A)
    (value : V) (index : SCartesianIndex2) : RResult (ReinterpretArray T S A) := do
  checkWritable a
  let valueBytes ← convertValue a.target value
  let old ← parentGet a.parent index.j
  let changedValue := overwriteBytes old ((index.i.val - 1).toNat) valueBytes
  let parent ← parentSet a.parent index.j changedValue
  pure { a with parent := parent }
/-
Julia source: base/reinterpretarray.jl:610-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _setindex_ptr!(a::ReinterpretArray{T}, v, inds...) where {T}
    @boundscheck checkbounds(a, inds...)
    li = _to_linear_index(a, inds...)
    ap = cconvert(Ptr{T}, a)
    p = unsafe_convert(Ptr{T}, ap) + elsize(a) * (li - firstindex(a))
    GC.@preserve ap unsafe_store!(p, v)
    return a
end
```
-/
def m610_setindexPtr {T S A : Type} (ops : PointerWriteOps A)
    (a : ReinterpretArray T S A) (value : Bytes) (indices : List I64) : RResult (ReinterpretArray T S A) := do
  match ops with
  | .mk checkbounds linearIndex cconvert unsafeConvert elsize firstindex addPointer unsafeStore => do
    checkbounds a.parent indices
    let li := linearIndex a.parent indices
    let ap := cconvert a.parent
    let ptr := unsafeConvert ap
    let p := addPointer ptr (elsize a.parent * (li - firstindex a.parent))
    unsafeStore p value
    pure a
/-
Julia source: base/reinterpretarray.jl:619-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _setindex_ra!(a::NonReshapedReinterpretArray{T,N,S}, v, i1::Int, tailinds::TT) where {T,N,S,TT}
    v = convert(T, v)::T
    if issingletontype(T) # singleton types
        @boundscheck checkbounds(a, i1, tailinds...)
        # setindex! is a noop except for the index check
    elseif _is_scalar_reinterpret_applicable(T, S)
        setindex!(a.parent, reinterpret(S, v), i1, tailinds...)
    else
        @boundscheck checkbounds(a, i1, tailinds...)
        ind_start, sidx = divrem((i1-1)*aligned_sizeof(T), aligned_sizeof(S))
        # Optimizations that avoid branches
        if aligned_sizeof(T) % aligned_sizeof(S) == 0
            # T is bigger than S and contains an integer number of them
            t = Ref{T}(v)
            GC.@preserve t begin
                sptr = Ptr{S}(unsafe_convert(Ref{T}, t))
                n = aligned_sizeof(T) ÷ aligned_sizeof(S)
                for i = 1:n
                    s = unsafe_load(sptr, i)
                    a.parent[ind_start + i, tailinds...] = s
                end
            end
        elseif aligned_sizeof(S) % aligned_sizeof(T) == 0
            # S is bigger than T and contains an integer number of them
            s = Ref{S}(a.parent[ind_start + 1, tailinds...])
            GC.@preserve s begin
                tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
                unsafe_store!(tptr + sidx, v)
                a.parent[ind_start + 1, tailinds...] = s[]
            end
        else
            t = Ref{T}(v)
            s = Ref{S}()
            GC.@preserve t s begin
                tptr = Ptr{UInt8}(unsafe_convert(Ref{T}, t))
                sptr = Ptr{UInt8}(unsafe_convert(Ref{S}, s))
                nbytes_copied = 0
                i = 1
                # Deal with any partial elements at the start. We'll have to copy in the
                # element from the original array and overwrite the relevant parts
                if sidx != 0
                    s[] = a.parent[ind_start + i, tailinds...]
                    nb = min((aligned_sizeof(S) - sidx) % UInt, aligned_sizeof(T) % UInt)
                    memcpy(sptr + sidx, tptr, nb)
                    nbytes_copied += nb
                    a.parent[ind_start + i, tailinds...] = s[]
                    i += 1
                end
                # Deal with the main body of elements
                while nbytes_copied < aligned_sizeof(T) && (aligned_sizeof(T) - nbytes_copied) > aligned_sizeof(S)
                    nb = min(aligned_sizeof(S), aligned_sizeof(T) - nbytes_copied)
                    memcpy(sptr, tptr + nbytes_copied, nb)
                    nbytes_copied += nb
                    a.parent[ind_start + i, tailinds...] = s[]
                    i += 1
                end
                # Deal with trailing partial elements
                if nbytes_copied < aligned_sizeof(T)
                    s[] = a.parent[ind_start + i, tailinds...]
                    nb = min(aligned_sizeof(S), aligned_sizeof(T) - nbytes_copied)
                    memcpy(sptr, tptr + nbytes_copied, nb)
                    a.parent[ind_start + i, tailinds...] = s[]
                end
            end
        end
    end
    return a
end
```
-/
def m619_setindexNonReshaped {T S A V : Type} (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  let valueBytes ← convertValue a.target value
  if a.target.singleton then
    checkbounds a i1 tail
    return a
  if m469_scalarApplicable a.target a.source then
    let sourceBytes ← m882_reinterpret fieldcount fieldoffset fieldtype a.source a.target valueBytes
    checkbounds a i1 tail
    let offset := ((i1.val - 1).toNat * a.target.alignedSize.val.toNat)
    let changed := overwriteBytes a.bytes offset sourceBytes
    let parent ← setParent a.parent changed
    return { a with parent := parent, bytes := changed }
  checkbounds a i1 tail
  let ts := a.target.alignedSize.val.toNat
  let ss := a.source.alignedSize.val.toNat
  let byteOffset := (i1.val - 1).toNat * ts
  let start := byteOffset / ss
  let sidx := byteOffset % ss
  let mut changed := a.bytes
  if ts % ss == 0 then
    let n := ts / ss
    for i in List.range n do
      let sourceBytes := (valueBytes.drop (i * ss)).take ss
      changed := overwriteBytes changed (start * ss + i * ss) sourceBytes
  else if ss % ts == 0 then
    let sourceBytes := (changed.drop (start * ss)).take ss
    let updated := overwriteBytes sourceBytes sidx valueBytes
    changed := overwriteBytes changed (start * ss) updated
  else
    let copiedAtStart := if sidx != 0 then min ((ss - sidx) % 8) (ts % 8) else 0
    if sidx != 0 then
      changed := overwriteBytes changed (start * ss + sidx) (valueBytes.take copiedAtStart)
    let mut copied := copiedAtStart
    let mut element := start + if sidx != 0 then 1 else 0
    while copied < ts && ts - copied > ss do
      let count := min ss (ts - copied)
      changed := overwriteBytes changed (element * ss) ((valueBytes.drop copied).take count)
      copied := copied + count
      element := element + 1
    if copied < ts then
      changed := overwriteBytes changed (element * ss) ((valueBytes.drop copied).take (min ss (ts - copied)))
  let parent ← setParent a.parent changed
  pure { a with parent := parent, bytes := changed }
/-
Julia source: base/reinterpretarray.jl:688-734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _setindex_ra!(a::ReshapedReinterpretArray{T,N,S}, v, i1::Int, tailinds::TT) where {T,N,S,TT}
    v = convert(T, v)::T
    if issingletontype(T) # singleton types
        @boundscheck checkbounds(a, i1, tailinds...)
        # setindex! is a noop except for the index check
    elseif _is_scalar_reinterpret_applicable(T, S)
        setindex!(a.parent, reinterpret(S, v), i1, tailinds...)
    else
        @boundscheck checkbounds(a, i1, tailinds...)
        if aligned_sizeof(T) >= aligned_sizeof(S)
            t = Ref{T}(v)
            GC.@preserve t begin
                sptr = Ptr{S}(unsafe_convert(Ref{T}, t))
                if aligned_sizeof(T) > aligned_sizeof(S)
                    # Extra dimension in the parent array
                    n = aligned_sizeof(T) ÷ aligned_sizeof(S)
                    if isempty(tailinds) && IndexStyle(a.parent) === IndexLinear()
                        offset = n * (i1 - firstindex(a))
                        for i = 1:n
                            s = unsafe_load(sptr, i)
                            a.parent[i + offset] = s
                        end
                    else
                        for i = 1:n
                            s = unsafe_load(sptr, i)
                            a.parent[i, i1, tailinds...] = s
                        end
                    end
                else # aligned_sizeof(T) == aligned_sizeof(S)
                    # No extra dimension
                    s = unsafe_load(sptr)
                    a.parent[i1, tailinds...] = s
                end
            end
        else
            # S is bigger than T and contains an integer number of them
            s = Ref{S}()
            GC.@preserve s begin
                tptr = Ptr{T}(unsafe_convert(Ref{S}, s))
                s[] = a.parent[tailinds...]
                unsafe_store!(tptr, v, i1)
                a.parent[tailinds...] = s[]
            end
        end
    end
    return a
end
```
-/
def m688_setindexReshaped {T S A V : Type} (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (setParent : A → Bytes → RResult A)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  let valueBytes ← convertValue a.target value
  if a.target.singleton then
    checkbounds a i1 tail
    return a
  if m469_scalarApplicable a.target a.source then
    let sourceBytes ← m882_reinterpret fieldcount fieldoffset fieldtype a.source a.target valueBytes
    checkbounds a i1 tail
    let changed := overwriteBytes a.bytes ((i1.val - 1).toNat * a.target.alignedSize.val.toNat) sourceBytes
    let parent ← setParent a.parent changed
    return { a with parent := parent, bytes := changed }
  checkbounds a i1 tail
  let ts := a.target.alignedSize.val.toNat
  let ss := a.source.alignedSize.val.toNat
  let start := (i1.val - 1).toNat * ts
  let mut changed := a.bytes
  if ts >= ss then
    if ts > ss then
      let n := ts / ss
      for i in List.range n do
        let sourceBytes := (valueBytes.drop (i * ss)).take ss
        changed := overwriteBytes changed (start + i * ss) sourceBytes
    else
      changed := overwriteBytes changed start valueBytes
  else
    let sourceBytes := (changed.take (tail.length * ss)).drop (tail.length * ss)
    changed := overwriteBytes changed start valueBytes
    let _ := sourceBytes
  let parent ← setParent a.parent changed
  pure { a with parent := parent, bytes := changed }
/-
Julia source: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, p::PaddingError)
    print(io, "Padding of type $(p.S) is not compatible with type $(p.T).")
end
```
-/
def m741_showerror (p : PaddingErrorModel) : String :=
  "Padding of type " ++ p.source ++ " is not compatible with type " ++ p.target ++ "."
/-
Julia source: base/reinterpretarray.jl:750-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function non_padding_bytes(T::DataType)::Memory{Bool}
    # @assert isbitstype(T)
    has_bit_padding(T) && throw(ArgumentError(LazyString("type `", T,
        "` contains non-byte-aligned primitive fields, so its padding bytes are not defined")))
    used = Memory{Bool}(undef, aligned_sizeof(T))
    fill!(used, false)
    fill_nonpadding_bytes!(T, 0, used)
    used
end
```
-/
def m750_nonPaddingBytes (layout : TypeLayout) : RResult (List Bool) := do
  if m828_hasBitPadding layout then .error .argument
  let used := List.replicate layout.alignedSize.val.toNat false
  pure (m756_fillNonpadding layout 0 used)
/-
Julia source: base/reinterpretarray.jl:759-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill_nonpadding_bytes!(T::DataType, offset::Int, used::Memory{Bool})
    if isprimitivetype(T)
        # sizeof rounds the value bytes up to a multiple of the alignment, so the
        # bytes past them are padding
        for i in 1:cld(Core.bitsizeof(T), 8)
            used[i + offset] = true
        end
    else
        for i in 1:fieldcount(T)
            fill_nonpadding_bytes!(fieldtype(T, i), offset + Int(fieldoffset(T, i)), used)
        end
    end
end
```
-/
def m756_fillNonpadding (layout : TypeLayout) (offset : Nat) (used : List Bool) : List Bool :=
  if layout.primitive then
    setTrueOffsets used ((List.range ((layout.bits + 7) / 8)).map (· + offset))
  else
    layout.fields.foldl (fun bytes field =>
      setTrueOffsets bytes (field.usedOffsets.map (fun i => i + offset + field.offset))) used
/-
Julia source: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function array_subpadding(S, T)
    # Fast path: if every byte of `T` is a non-padding byte, any byte can be
    # read. This also covers zero-size `T`.
    if ispacked(T)
        return true
    end
    # `T` has at least one padding byte here. If `S` has none, the byte cycle
    # below visits every byte of `T`, so some readable byte of `S` must land on
    # padding in `T`. This also covers zero-size `S`.
    if ispacked(S)
        return false
    end
    s_used, t_used = non_padding_bytes(S), non_padding_bytes(T)
    # zero-size T and S are unreachable here (handled by the fast paths above);
    # these guards only keep the loop below well-defined
    isempty(t_used) && return true
    isempty(s_used) && return false
    s_n, t_n = length(s_used), length(t_used)
    s_i, t_i = 1, 1
    while true
        # If a byte can be read in S, but is padding in T, return false
        if s_used[s_i] && !t_used[t_i]
            return false
        end
        # Advance the indexes with wrapping around
        s_i += 1
        if s_i > s_n
            s_i = 1
        end
        t_i += 1
        if t_i > t_n
            t_i = 1
        end
        # We made it back to the start
        if isone(s_i) && isone(t_i)
            return true
        end
    end
end
```
-/
def m772_arraySubpadding (source target : TypeLayout) : RResult Bool := do
  if !target.datatypePadding then pure true
  else if !source.datatypePadding then pure false
  else
    let sUsed ← m750_nonPaddingBytes source
    let tUsed ← m750_nonPaddingBytes target
    if tUsed.isEmpty then pure true
    else if sUsed.isEmpty then pure false
    else pure (cycleSubpaddingFuel sUsed tUsed 0 0 (sUsed.length * tUsed.length + 1))
/-
Julia source: base/reinterpretarray.jl:815-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function struct_subpadding(Out, In)
    non_padding_bytes(Out) == non_padding_bytes(In)
end
```
-/
def m812_structSubpadding (output input : TypeLayout) : RResult Bool := do
  let outputUsed ← m750_nonPaddingBytes output
  let inputUsed ← m750_nonPaddingBytes input
  pure (outputUsed == inputUsed)
/-
Julia source: base/reinterpretarray.jl:819-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function packedsize(T)
    if !datatype_haspadding(T)
        sizeof(T)
    else
        count(non_padding_bytes(T))
    end
end
```
-/
def m816_packedsize (layout : TypeLayout) : RResult Nat :=
  if !layout.datatypePadding then pure layout.alignedSize.val.toNat
  else (m750_nonPaddingBytes layout).map (List.countP id)
/-
Julia source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function ispacked(T)
    !datatype_haspadding(T)
end
```
-/
def m824_ispacked (layout : TypeLayout) : Bool := !layout.datatypePadding
/-
Julia source: base/reinterpretarray.jl:831-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function has_bit_padding(::Type{T}) where T
    if isprimitivetype(T)
        return Core.bitsizeof(T) % 8 != 0
    end
    T isa Union && return any(has_bit_padding, uniontypes(T))
    for i in 1:fieldcount(T)
        has_bit_padding(fieldtype(T, i)) && return true
    end
    return false
end
```
-/
def m828_hasBitPadding (layout : TypeLayout) : Bool :=
  if layout.primitive then layout.bits % 8 != 0
  else if layout.union then layout.unionBitPadding.any id
  else layout.fields.any FieldLayout.bitPadding
/-
Julia source: base/reinterpretarray.jl:842-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copytopacked!(ptr_out::Ptr{Out}, ptr_in::Ptr{In}) where {Out, In}
    if isprimitivetype(In)
        memcpy(ptr_out, ptr_in, packedsize(In))
        return
    end
    writeoffset = 0
    for i ∈ 1:fieldcount(In)
        readoffset = fieldoffset(In, i)
        fT = fieldtype(In, i)
        if ispacked(fT)
            readsize = sizeof(fT)
            memcpy(ptr_out + writeoffset, ptr_in + readoffset, readsize)
            writeoffset += readsize
        else # nested padded type
            _copytopacked!(ptr_out + writeoffset, Ptr{fT}(ptr_in + readoffset))
            writeoffset += packedsize(fT)
        end
    end
end
```
-/
def m842_copytopacked (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (sizeof : TypeLayout → Nat) (layout : TypeLayout) (input : Bytes) : RResult Bytes := do
  if layout.primitive then return input.take (← m816_packedsize layout)
  let mut packed : Bytes := []
  for i in List.range (fieldcount layout) do
    let offset := fieldoffset layout i
    let child := fieldtype layout i
    let offsets := if m824_ispacked child then List.range (sizeof child)
      else (layout.fields.getD i ⟨offset, sizeof child, false, [], false⟩).usedOffsets
    for byteOffset in offsets do
      packed := packed ++ (input.drop (offset + byteOffset)).take 1
  pure packed
/-
Julia source: base/reinterpretarray.jl:862-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyfrompacked!(ptr_out::Ptr{Out}, ptr_in::Ptr{In}) where {Out, In}
    if isprimitivetype(Out)
        memcpy(ptr_out, ptr_in, packedsize(Out))
        return
    end
    readoffset = 0
    for i ∈ 1:fieldcount(Out)
        writeoffset = fieldoffset(Out, i)
        fT = fieldtype(Out, i)
        if ispacked(fT)
            writesize = sizeof(fT)
            memcpy(ptr_out + writeoffset, ptr_in + readoffset, writesize)
            readoffset += writesize
        else # nested padded type
            _copyfrompacked!(Ptr{fT}(ptr_out + writeoffset), ptr_in + readoffset)
            readoffset += packedsize(fT)
        end
    end
end
```
-/
def m862_copyfrompacked (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (sizeof : TypeLayout → Nat) (layout : TypeLayout) (packed : Bytes) : RResult Bytes := do
  if layout.primitive then return packed.take (sizeof layout)
  let mut output := List.replicate layout.alignedSize.val.toNat (0 : UInt8)
  let mut readOffset := 0
  for i in List.range (fieldcount layout) do
    let offset := fieldoffset layout i
    let child := fieldtype layout i
    let field := layout.fields.getD i ⟨offset, sizeof child, false, [], false⟩
    let offsets := if m824_ispacked child then List.range (sizeof child) else field.usedOffsets
    for byteOffset in offsets do
      output := overwriteBytes output (offset + byteOffset) ((packed.drop readOffset).take 1)
      readOffset := readOffset + 1
  pure output
/-
Julia source: base/reinterpretarray.jl:882-909 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _reinterpret(::Type{Out}, x::In) where {Out, In}
    # handle non-primitive types
    isbitstype(Out) || throw(ArgumentError("Target type for `reinterpret` must be isbits"))
    isbitstype(In) || throw(ArgumentError("Source type for `reinterpret` must be isbits"))
    has_bit_padding(Out) && throw(ArgumentError(LazyString(
        "cannot `reinterpret` type ", Out, " containing non-byte-aligned primitive fields")))
    has_bit_padding(In) && throw(ArgumentError(LazyString(
        "cannot `reinterpret` type ", In, " containing non-byte-aligned primitive fields")))
    inpackedsize = packedsize(In)
    outpackedsize = packedsize(Out)
    inpackedsize == outpackedsize ||
        throw(ArgumentError(LazyString("Packed sizes of types ", Out, " and ", In,
            " do not match; got ", outpackedsize, " and ", inpackedsize, ", respectively.")))
    in = Ref{In}(x)
    out = Ref{Out}()
    if (ispacked(In) && ispacked(Out)) || struct_subpadding(Out, In)
        # if packed the same, just copy
        GC.@preserve in out begin
            ptr_in = unsafe_convert(Ptr{In}, in)
            ptr_out = unsafe_convert(Ptr{Out}, out)
            memcpy(ptr_out, ptr_in, sizeof(Out))
        end
        return out[]
    else
        # mismatched padding
        return _reinterpret_padding(Out, x)
    end
end
```
-/
def m882_reinterpret (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (output input : TypeLayout) (bytes : Bytes) : RResult Bytes := do
  if !output.isBits then .error .argument
  if !input.isBits then .error .argument
  if m828_hasBitPadding output then .error .argument
  if m828_hasBitPadding input then .error .argument
  let outputSize ← m816_packedsize output
  let inputSize ← m816_packedsize input
  if inputSize != outputSize then .error .argument
  let samePadding ← m812_structSubpadding output input
  if (m824_ispacked input && m824_ispacked output) || samePadding then
    return bytes.take output.alignedSize.val.toNat
  else m913_reinterpretPadding fieldcount fieldoffset fieldtype output input bytes
/-
Julia source: base/reinterpretarray.jl:913-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reinterpret_padding(::Type{Out}, x::In) where {Out, In}
    inpackedsize = packedsize(In)
    in = Ref{In}(x)
    out = Ref{Out}()
    GC.@preserve in out begin
        ptr_in = unsafe_convert(Ptr{In}, in)
        ptr_out = unsafe_convert(Ptr{Out}, out)

        if fieldcount(In) > 0 && ispacked(Out)
            _copytopacked!(ptr_out, ptr_in)
        elseif fieldcount(Out) > 0 && ispacked(In)
            _copyfrompacked!(ptr_out, ptr_in)
        else
            packed = Ref{NTuple{inpackedsize, UInt8}}()
            GC.@preserve packed begin
                ptr_packed = unsafe_convert(Ptr{NTuple{inpackedsize, UInt8}}, packed)
                _copytopacked!(ptr_packed, ptr_in)
                _copyfrompacked!(ptr_out, ptr_packed)
            end
        end
    end
    return out[]
end
```
-/
def m913_reinterpretPadding (fieldcount : TypeLayout → Nat)
    (fieldoffset : TypeLayout → Nat → Nat) (fieldtype : TypeLayout → Nat → TypeLayout)
    (output input : TypeLayout) (bytes : Bytes) : RResult Bytes := do
  let _inputPackedSize ← m816_packedsize input
  if fieldcount input > 0 && m824_ispacked output then
    m842_copytopacked fieldcount fieldoffset fieldtype (fun t => t.alignedSize.val.toNat) input bytes
  else if fieldcount output > 0 && m824_ispacked input then
    m862_copyfrompacked fieldcount fieldoffset fieldtype (fun t => t.alignedSize.val.toNat) output bytes
  else do
    let packed ← m842_copytopacked fieldcount fieldoffset fieldtype
      (fun t => t.alignedSize.val.toNat) input bytes
    m862_copyfrompacked fieldcount fieldoffset fieldtype
      (fun t => t.alignedSize.val.toNat) output packed
/-
Julia source: base/reinterpretarray.jl:937-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(v::ReinterpretArray{UInt8,1,S,<:Union{Vector{S},Memory{S}},IsReshaped}) where {S,IsReshaped}
    len = length(v)
    len == 0 && return ""
    check_readable(v) # stringifying empty arrays is always allowed
    return ccall(:jl_pchar_to_string, Ref{String}, (Ptr{UInt8}, Int), v, len)
end
```
-/
def m937_string {T S A R : Type} (emptyString : R) (callString : Nat → RResult R)
    (a : ReinterpretArray T S A) : RResult R := do
  let len := a.bytes.length
  if len == 0 then return emptyString
  m237_checkReadable a
  callString len
end

mutual
/-
Julia source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
    inds = eachindex(style, A)
    n = size(inds)[2]
    if n == 0
        return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
    else
        return mapreduce_impl(f, op, A, first(inds), last(inds))
    end
end
```
-/
partial def m946_mapreduce {A F OP X V E : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → List (SCartesianIndices2 K))
    (columnCount : List (SCartesianIndices2 K) → Nat)
    (iteratorEltype : A → E) (empty : F → OP → A → E → RResult V)
    (first : List (SCartesianIndices2 K) → SCartesianIndex2)
    (last : List (SCartesianIndices2 K) → SCartesianIndex2)
    (blocksize : F → OP → Nat) (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (f : F) (op : OP) (style : IndexStyleModel) (a : A) : RResult V := do
  let inds := eachindex style a
  if columnCount inds == 0 then
    empty f op a (iteratorEltype a)
  else m984_mapreduceDefault (K := K) blocksize get map combine a f op (first inds) (last inds)
/-
Julia source: base/reinterpretarray.jl:956-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted,
                                  ifirst::SCI, ilast::SCI, blksize::Int) where {F,OP,SCI<:SCartesianIndex2{K}} where K
    if ilast.j - ifirst.j < blksize
        # sequential portion
        @inbounds a1 = A[ifirst]
        @inbounds a2 = A[SCI(2,ifirst.j)]
        v = op(f(a1), f(a2))
        @simd for i = ifirst.i + 2 : K
            @inbounds ai = A[SCI(i,ifirst.j)]
            v = op(v, f(ai))
        end
        # Remaining columns
        for j = ifirst.j+1 : ilast.j
            @simd for i = 1:K
                @inbounds ai = A[SCI(i,j)]
                v = op(v, f(ai))
            end
        end
        return v
    else
        # pairwise portion
        jmid = ifirst.j + (ilast.j - ifirst.j) >> 1
        v1 = mapreduce_impl(f, op, A, ifirst, SCI(K,jmid), blksize)
        v2 = mapreduce_impl(f, op, A, SCI(1,jmid+1), ilast, blksize)
        return op(v1, v2)
    end
end
```
-/
partial def m956_mapreduceImpl {A F OP X V : Type} {K : Nat}
    (get : A → SCartesianIndex2 → RResult X) (map : F → X → RResult V)
    (combine : OP → V → V → RResult V) (a : A) (f : F) (op : OP)
    (ifirst ilast : SCartesianIndex2) (blocksize : Nat) : RResult V := do
  if ilast.j.val - ifirst.j.val < (blocksize : Int) then
    let a1 ← get a ifirst
    let a2 ← get a ⟨JInt.lit .i64 2, ifirst.j⟩
    let mut value ← combine op (← map f a1) (← map f a2)
    for i in List.range K do
      if (i : Int) + 1 ≥ ifirst.i.val + 2 then
        let ai ← get a ⟨JInt.lit .i64 (i + 1), ifirst.j⟩
        value ← combine op value (← map f ai)
    for j in List.range ((ilast.j.val - ifirst.j.val).toNat) do
      for i in List.range K do
        let ai ← get a ⟨JInt.lit .i64 (i + 1), JInt.lit .i64 (ifirst.j.val + (j : Int) + 1)⟩
        value ← combine op value (← map f ai)
    return value
  else
    let mid := ifirst.j.val + (ilast.j.val - ifirst.j.val) / 2
    let v1 ← m956_mapreduceImpl (K := K) get map combine a f op ifirst ⟨JInt.lit .i64 K, JInt.lit .i64 mid⟩ blocksize
    let v2 ← m956_mapreduceImpl (K := K) get map combine a f op ⟨JInt.lit .i64 1, JInt.lit .i64 (mid + 1)⟩ ilast blocksize
    combine op v1 v2
/-
Julia source: base/reinterpretarray.jl:984-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted, ifirst::SCartesianIndex2, ilast::SCartesianIndex2) where {F,OP} =
    mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
```
-/
partial def m984_mapreduceDefault {A F OP X V : Type} {K : Nat}
    (blocksize : F → OP → Nat) (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (a : A) (f : F) (op : OP) (ifirst ilast : SCartesianIndex2) : RResult V :=
  m956_mapreduceImpl (K := K) get map combine a f op ifirst ilast (blocksize f op)
end

/-
Julia source: base/reinterpretarray.jl:990-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _totuple(T::Type{All32{E,N}}, itr::Union{Array,Memory}) where {E,N}
    len = N + 32
    length(itr) >= len || _totuple_err(T)
    if isbitstype(E) && eltype(itr) === E
        v = length(itr) == len ? itr : view(itr, 1:len)
        return @inbounds reinterpret(T, v)[1]
    end
    elts = collect(E, Iterators.take(itr, len))
    return (elts...,)
end
```
-/
def m990_totuple {A R X : Type} (arrayLength : ArrayInput A → Nat)
    (totupleError : TypeLayout → RResult R) (isBits : TypeLayout → Bool)
    (eltypeMatches : ArrayInput A → TypeLayout → Bool)
    (viewPrefix : ArrayInput A → Nat → RResult (ArrayInput A))
    (fieldtype : TypeLayout → Nat → TypeLayout)
    (pointerOps : PointerReadOps (ArrayInput A))
    (parentIndexStyle : ArrayInput A → IndexStyleModel)
    (toSubscripts : ReinterpretArray R X (ArrayInput A) → I64 → List I64)
    (firstindex : ReinterpretArray R X (ArrayInput A) → I64)
    (checkbounds : ReinterpretArray R X (ArrayInput A) → I64 → List I64 → RResult Unit)
    (getParent : ArrayInput A → I64 → List I64 → RResult Bytes)
    (tupleFromBytes : Bytes → RResult R)
    (collectTuple : TypeLayout → ArrayInput A → Nat → RResult R)
    (tupleType elementType : TypeLayout) (n : Nat) (itr : ArrayInput A) : RResult R := do
  let len := arrayLength itr
  let needed := n + 32
  if len < needed then
    totupleError tupleType
  else if isBits elementType && eltypeMatches itr elementType then
    let view ← if len == needed then pure itr else viewPrefix itr needed
    let reinterpret : ReinterpretArray R X (ArrayInput A) ←
      m73_reinterpret.{0,0,0,0,0} (T := R) (S := X) (A := A) tupleType elementType view
    let bytes ← m442_getindexLinear.{0,0,0,0,0} (T := R) (S := X) (A := ArrayInput A)
      pointerOps parentIndexStyle toSubscripts firstindex checkbounds fieldtype getParent
      reinterpret (JInt.lit .i64 1)
    tupleFromBytes bytes
  else
    collectTuple elementType itr needed

end JuliaLean.base.reinterpretarray
