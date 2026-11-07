import JuliaLean.base.boot
import JuliaLean.base.essentials
import JuliaLean.base.runtime_internals
import JuliaLean.base.bool
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.genericmemory
import JuliaLean.base.iterators
import JuliaLean.base.pointer

/-!
# Typed model of `base/reinterpretarray.jl`

Array values retain their parent. Element accesses and mutations go through the parent's
indexing interface. `Bytes` represents a single isbits value's storage, never an array's
backing store. Pointer loads and stores use the shared `pointer.ByteHeap`; stores return the
parent with its updated heap. Native references and copying use byte-addressed value storage.
Runtime type metadata is a finite tree of fields and union members.
-/

namespace JuliaLean.base.reinterpretarray
open JuliaLean JuliaLean.base.int
abbrev I64 := JInt .i64
abbrev Bytes := List UInt8
inductive ReinterpretError where
  | argument | padding | bounds | divide | nonIntegralStride | noncontiguous | assertion
  | pointer (error : JuliaLean.base.pointer.PointerError)
  deriving Repr, DecidableEq, Inhabited
abbrev RResult (α : Type) := Except ReinterpretError α
structure Axis where
  first : I64
  length : I64
  deriving Repr, DecidableEq
structure LayoutInfo where
  id : Nat
  bits : Nat
  alignedSize : I64
  isBits : Bool
  primitive : Bool
  union : Bool
  singleton : Bool
  datatypePadding : Bool
  deriving Repr, DecidableEq
inductive TypeLayout where
  | mk (info : LayoutInfo) (fields : List (Nat × TypeLayout)) (members : List TypeLayout)
  deriving Repr
def TypeLayout.info : TypeLayout → LayoutInfo | .mk info _ _ => info
def TypeLayout.fields : TypeLayout → List (Nat × TypeLayout) | .mk _ fields _ => fields
def TypeLayout.members : TypeLayout → List TypeLayout | .mk _ _ members => members
def TypeLayout.id (t : TypeLayout) : Nat := t.info.id
def TypeLayout.bits (t : TypeLayout) : Nat := t.info.bits
def TypeLayout.alignedSize (t : TypeLayout) : I64 := t.info.alignedSize
def TypeLayout.isBits (t : TypeLayout) : Bool := t.info.isBits
def TypeLayout.primitive (t : TypeLayout) : Bool := t.info.primitive
def TypeLayout.union (t : TypeLayout) : Bool := t.info.union
def TypeLayout.singleton (t : TypeLayout) : Bool := t.info.singleton
def TypeLayout.datatypePadding (t : TypeLayout) : Bool := t.info.datatypePadding

structure ArrayInput (A : Type) where
  parent : A
  rank : Nat
  size : List I64
  axes : List Axis
structure ReinterpretArray (T S A : Type) where
  parent : A
  rank : Nat
  target : TypeLayout
  source : TypeLayout
  readable : Bool
  writable : Bool
  reshaped : Bool
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
  indices2 : Axis
  deriving Repr, DecidableEq
structure PaddingErrorModel where
  source : String
  target : String
  deriving Repr, DecidableEq
structure ParentOps (A : Type) where
  get : A → List I64 → RResult Bytes
  set : A → List I64 → Bytes → RResult A
structure PointerReadOps (T S A : Type) where
  checkbounds : ReinterpretArray T S A → List I64 → RResult Unit
  linearIndex : ReinterpretArray T S A → List I64 → I64
  parentCconvert : TypeLayout → A → Nat
  unsafeConvert : TypeLayout → Nat → Nat
  parentElsize : A → I64
  firstindex : ReinterpretArray T S A → I64
  addPointer : Nat → I64 → Nat
  Element : Type
  codec : JuliaLean.base.pointer.ByteCodec Element
  heap : A → JuliaLean.base.pointer.ByteHeap
structure PointerWriteOps (T S A V : Type) where
  checkbounds : ReinterpretArray T S A → List I64 → RResult Unit
  linearIndex : ReinterpretArray T S A → List I64 → I64
  parentCconvert : TypeLayout → A → Nat
  unsafeConvert : TypeLayout → Nat → Nat
  parentElsize : A → I64
  firstindex : ReinterpretArray T S A → I64
  addPointer : Nat → I64 → Nat
  Element : Type
  codec : JuliaLean.base.pointer.ByteCodec Element
  convert : V → JuliaLean.base.pointer.PtrResult Element
  heap : A → JuliaLean.base.pointer.ByteHeap
  withHeap : A → JuliaLean.base.pointer.ByteHeap → A

def pointerStorageBytes (bytes : List JuliaLean.base.pointer.Byte) : Bytes :=
  bytes.map (fun byte => UInt8.ofNat byte.val.toNat)

def PointerReadOps.load {T S A : Type} (ops : PointerReadOps T S A)
    (parent : A) (address : Nat) : RResult Bytes :=
  ((JuliaLean.base.pointer.unsafeLoad ops.codec (fun i : I64 => .ok i)
    ⟨JInt.wrap .u64 address⟩ (ops.heap parent) oneI64).map
      (fun value => pointerStorageBytes (ops.codec.encode value))).mapError ReinterpretError.pointer
where
  oneI64 : I64 := JInt.lit .i64 1

def PointerWriteOps.store {T S A V : Type} (ops : PointerWriteOps T S A V)
    (parent : A) (address : Nat) (value : V) : RResult A :=
  ((JuliaLean.base.pointer.unsafeStoreTyped ops.codec ops.convert (fun i : I64 => .ok i)
    ⟨JInt.wrap .u64 address⟩ (ops.heap parent) value (JInt.lit .i64 1)).map
      (fun result => ops.withHeap parent result.1)).mapError ReinterpretError.pointer

def overwriteBytes (output : Bytes) (offset : Nat) (bytes : Bytes) : Bytes :=
  output.take offset ++ bytes ++ output.drop (offset + bytes.length)
def byteWindow (bytes : Bytes) (offset size : Nat) : Bytes := (bytes.drop offset).take size
def divInt (x y : I64) : RResult I64 := (JInt.div x y).mapError (fun _ => .divide)
def remInt (x y : I64) : RResult I64 := (JInt.remInt x y).mapError (fun _ => .divide)
def divremInt (x y : I64) : RResult (I64 × I64) := do
  return (← divInt x y, ← remInt x y)
def one : I64 := JInt.lit .i64 1
def zero : I64 := JInt.lit .i64 0
/-- The finite Julia `lo:hi` iteration range, including its machine-integer endpoints. -/
def intRange (lo hi : I64) : List I64 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun (k : Nat) => lo + JInt.lit .i64 (k : Int))
/-- Byte copies operate on one temporary reference's storage. -/
def memcpyValue (dst src : Bytes) (writeOffset readOffset count : I64) : Bytes :=
  overwriteBytes dst writeOffset.val.toNat (byteWindow src readOffset.val.toNat count.val.toNat)

/--
Julia source: base/reinterpretarray.jl:14-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwbits(S::Type, T::Type, U::Type)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret `", S, "` as `", T, "`, type `", U, "` is not a bits type")))
    end
```
-/
def m14_throwbits {α : Type} (_source _target _culprit : TypeLayout) : RResult α := .error .argument

/--
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

/--
Julia source: base/reinterpretarray.jl:23-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throwsingleton(S::Type, T::Type)
        @noinline
        throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T, "` which is a singleton type")))
    end
```
-/
def m23_throwsingleton {α : Type} (_source _target : TypeLayout) : RResult α := .error .argument

/--
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

/--
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

/--
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

/--
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
  else if layout.union then layout.members.attach.any (fun member => m828_hasBitPadding member.val)
  else layout.fields.attach.any (fun field => m828_hasBitPadding field.val.2)
termination_by sizeOf layout
decreasing_by
  · have h := List.sizeOf_lt_of_mem member.property
    cases layout
    simp_all [TypeLayout.members]
    omega
  · have h := List.sizeOf_lt_of_mem field.property
    have hp : sizeOf field.val.2 < sizeOf field.val := by
      rcases field with ⟨⟨offset, child⟩, hm⟩
      simp
      omega
    cases layout
    simp_all [TypeLayout.fields]
    omega

/--
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
def m756_fillNonpadding (layout : TypeLayout) (offset : I64) (used : List Bool) : List Bool :=
  if layout.primitive then
    (intRange one (JInt.lit .i64 ((layout.bits + 7) / 8))).foldl
      (fun bytes i => bytes.set ((i + offset - one).val.toNat) true) used
  else layout.fields.attach.foldl (fun bytes field =>
    m756_fillNonpadding field.val.2 (offset + JInt.lit .i64 field.val.1) bytes) used
termination_by sizeOf layout
decreasing_by
  cases layout
  have h := List.sizeOf_lt_of_mem field.property
  have hp : sizeOf field.val.2 < sizeOf field.val := by
    rcases field with ⟨⟨off, child⟩, hm⟩
    simp
    omega
  simp_all [TypeLayout.fields]
  omega

/--
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
  pure (m756_fillNonpadding layout zero used)

/--
Julia source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable function ispacked(T)
    !datatype_haspadding(T)
end
```
-/
def m824_ispacked (layout : TypeLayout) : Bool := !layout.datatypePadding

/--
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
  if m824_ispacked target then return true
  if m824_ispacked source then return false
  let sUsed ← m750_nonPaddingBytes source
  let tUsed ← m750_nonPaddingBytes target
  if tUsed.isEmpty then return true
  if sUsed.isEmpty then return false
  let sn := JInt.lit .i64 sUsed.length
  let tn := JInt.lit .i64 tUsed.length
  loop sUsed tUsed sn tn one one
where
  loop (sUsed tUsed : List Bool) (sn tn si ti : I64) : RResult Bool := do
    if sUsed.getD (si - one).val.toNat false && !tUsed.getD (ti - one).val.toNat false then
      return false
    let si := si + one
    let si := if sn < si then one else si
    let ti := ti + one
    let ti := if tn < ti then one else ti
    if si == one && ti == one then return true
    else loop sUsed tUsed sn tn si ti
  partial_fixpoint

/--
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
  if m828_hasBitPadding target then m27_throwbitpadding source target target
  if m828_hasBitPadding source then m27_throwbitpadding source target source
  if a.rank == 0 && target.alignedSize != source.alignedSize then
    m18_throwsize0 source target "different"
  if a.rank != 0 && source.alignedSize != target.alignedSize then
    let ax := a.axes.headD ⟨one, zero⟩
    if target.singleton then
      if !source.singleton then m23_throwsingleton source target
    else
      let remainder ← remInt (ax.length * source.alignedSize) target.alignedSize
      if remainder != zero then m74_thrownonint source target ax.length
    if ax.first != one then m80_throwaxes1 source target ax
  let readable ← m772_arraySubpadding target source
  let writable ← m772_arraySubpadding source target
  pure ⟨a, a.rank, target, source, readable, writable, false⟩

/--
Julia source: base/reinterpretarray.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
```
-/
def m104_reinterpretIdentity {A : Type} (array : A) : A := array

/--
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

/--
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
def m113_throwsize1 {A α : Type} (_array : ArrayInput A) (_target : TypeLayout) : RResult α := .error .argument

/--
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

/--
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
  if m828_hasBitPadding target then m27_throwbitpadding source target target
  if m828_hasBitPadding source then m27_throwbitpadding source target source
  let rank ← if source.alignedSize == target.alignedSize then pure a.rank
    else if target.alignedSize < source.alignedSize then do
      if target.singleton then m23_throwsingleton source target
      if (← remInt source.alignedSize target.alignedSize) != zero then m108_throwintmult source target
      pure (a.rank + 1)
    else do
      if source.singleton then m119_throwfromsingleton source target
      if (← remInt target.alignedSize source.alignedSize) != zero then m108_throwintmult source target
      if a.rank == 0 then m18_throwsize0 source target "larger"
      let ratio ← divInt target.alignedSize source.alignedSize
      if a.axes.headD ⟨one, zero⟩ != ⟨one, ratio⟩ then m113_throwsize1 a target
      pure (a.rank - 1)
  let readable ← m772_arraySubpadding target source
  let writable ← m772_arraySubpadding source target
  pure ⟨a, rank, target, source, readable, writable, true⟩

/--
Julia source: base/reinterpretarray.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray{T}) where {T} = a
```
-/
def m145_reinterpretReshapeIdentity {A : Type} (array : A) : A := array

/--
Julia source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
```
-/
def m188_reinterpretReshape {T S A : Type} (target source : TypeLayout) (a : ArrayInput A) :
    RResult (ReinterpretArray T S (ArrayInput A)) := m107_reinterpretReshape target source a

/--
Julia source: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinterpret(::Type{T}, a::NonReshapedReinterpretArray) where {T} = reinterpret(T, a.parent)
```
-/
def m190_reinterpretParent {T S A : Type} (target : TypeLayout)
    (a : ReinterpretArray T S (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) :=
  if target.id == a.source.id then .ok (.parent (m104_reinterpretIdentity a.parent))
  else (m73_reinterpret target a.source a.parent).map ReinterpretOutcome.view

/--
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
def m379_sizeReshaped {T S A : Type} (size : A → List I64)
    (divide : I64 → I64 → RResult I64) (a : ReinterpretArray T S A) : RResult (List I64) := do
  let psize := size a.parent
  if a.source.alignedSize > a.target.alignedSize then
    let ratio ← divide a.source.alignedSize a.target.alignedSize
    pure (ratio :: psize)
  else if a.source.alignedSize < a.target.alignedSize then pure (psize.drop 1)
  else pure psize

/--
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
def m393_axesReshaped {T S A : Type} (axes : A → List Axis)
    (divide : I64 → I64 → RResult I64) (a : ReinterpretArray T S A) : RResult (List Axis) := do
  let paxs := axes a.parent
  if a.source.alignedSize > a.target.alignedSize then
    let ratio ← divide a.source.alignedSize a.target.alignedSize
    pure (⟨one, ratio⟩ :: paxs)
  else if a.source.alignedSize < a.target.alignedSize then pure (paxs.drop 1)
  else pure paxs

/--
Julia source: base/reinterpretarray.jl:191-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reinterpret(::typeof(reshape), ::Type{T}, a::ReshapedReinterpretArray{S,N,P}) where {T,S,N,P}
    t, s, p = aligned_sizeof(T), aligned_sizeof(S), aligned_sizeof(P)
    return t == s || t == p || s == p ? reinterpret(reshape, T, a.parent) : ReinterpretArray{T}(reshape, a)
end
```
-/
def m191_reinterpretReshapedParent {T S P A : Type} (target : TypeLayout)
    (parentSize : ArrayInput A → List I64) (parentAxes : ArrayInput A → List Axis)
    (a : ReinterpretArray S P (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A))
      (ReinterpretArray T S (ArrayInput (ReinterpretArray S P (ArrayInput A))))) := do
  if target.alignedSize == a.target.alignedSize || target.alignedSize == a.source.alignedSize ||
      a.target.alignedSize == a.source.alignedSize then
    if target.id == a.source.id then return .parent (m145_reinterpretReshapeIdentity a.parent)
    else return .view (← m188_reinterpretReshape target a.source a.parent)
  else
    let dims ← m379_sizeReshaped parentSize divInt a
    let axs ← m393_axesReshaped parentAxes divInt a
    let input : ArrayInput (ReinterpretArray S P (ArrayInput A)) := ⟨a, a.rank, dims, axs⟩
    return .nested (← m107_reinterpretReshape target a.target input)

/--
Julia source: base/reinterpretarray.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strides(a::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}) = size_to_strides(1, size(a)...)
```
-/
def m207_strides {A : Type} (size : A → List I64)
    (sizeToStrides : I64 → List I64 → List I64) (a : A) : List I64 :=
  sizeToStrides (JInt.lit .i64 1) (size a)

/--
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

/--
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

/--
Julia source: base/reinterpretarray.jl:369-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(a::ReinterpretArray) = a.parent
```
-/
def m369_parent {T S A : Type} (a : ReinterpretArray T S A) : A := a.parent

/--
Julia source: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_checkcontiguous(::Type{Bool}, A::ReinterpretArray) = _checkcontiguous(Bool, parent(A))
```
-/
def m232_checkcontiguous {T S A : Type} (check : A → Bool)
    (a : ReinterpretArray T S A) : Bool := check (m369_parent a)

/--
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
    (size : ReinterpretArray T S A → List I64)
    (sizeToStrides : I64 → List I64 → List I64) (parentStrides : A → List I64)
    (parentElsize : A → I64) (divrem : I64 → I64 → RResult (I64 × I64))
    (iszero : I64 → Bool) (a : ReinterpretArray T S A) : RResult (List I64) := do
  if m232_checkcontiguous contiguous a then return sizeToStrides one (size a)
  let stp := parentStrides (m369_parent a)
  let els := a.target.alignedSize
  let elp := a.source.alignedSize
  if els == elp then return stp
  let ep := parentElsize (m369_parent a)
  let byteStrides := stp.map (fun i => i * ep)
  if a.reshaped && els < elp then
    return one :: (← m225_checkedStrides divrem iszero byteStrides els)
  if byteStrides.headD zero != elp then .error .noncontiguous
  let st ← m225_checkedStrides divrem iszero (byteStrides.drop 1) els
  return if a.reshaped then st else one :: st

/--
Julia source: base/reinterpretarray.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::ReinterpretArray, T::Type, d::Dims) = similar(a.parent, T, d)
```
-/
def m234_similar {A T D R : Type} (similar : A → T → D → R)
    (a : ReinterpretArray T S A) (type : T) (dims : D) : R := similar a.parent type dims

/--
Julia source: base/reinterpretarray.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{TA}, dims::Dims) where {T,N,O,P,TA<:ReinterpretArray{T,N,O,P}} = similar(P, dims)
```
-/
def m235_similarType {_T _N _O P TA D R : Type} (similar : P → D → R)
    (_type : TA) (dims : D) (parentType : P) : R := similar parentType dims

/--
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
  if !a.readable then
    if !(← m772_arraySubpadding a.target a.source) then .error .padding else pure ()
  else pure ()

/--
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
  if !a.writable then
    if !(← m772_arraySubpadding a.source a.target) then .error .padding else pure ()
  else pure ()

/--
Julia source: base/reinterpretarray.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}} =
    IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
```
-/
def m263_indexStyle {A : Type} (parentStyle : A → IndexStyleModel) (parentType : A) : IndexStyleModel :=
  if parentStyle parentType == .linear then .linear else .cartesian

/--
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

/--
Julia source: base/reinterpretarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
```
-/
def m273_combineStyle {K : Nat} (_left _right : IndexStyleModel) : IndexStyleModel := .staticCartesian K

/--
Julia source: base/reinterpretarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(i::SCartesianIndex2) = i
```
-/
def m279_toIndex (index : SCartesianIndex2) : SCartesianIndex2 := index

/--
Julia source: base/reinterpretarray.jl:280-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
    i.i < K ? SCartesianIndex2{K}(i.i + 1, i.j) : SCartesianIndex2{K}(1, i.j + 1)
```
-/
def m280_nextIndex (K : I64) (index : SCartesianIndex2) : SCartesianIndex2 :=
  if index.i < K then ⟨index.i + JInt.lit .i64 1, index.j⟩
  else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩

/--
Julia source: base/reinterpretarray.jl:282-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
    i.i > 1 ? SCartesianIndex2{K}(i.i - 1, i.j) : SCartesianIndex2{K}(K, i.j - 1)
```
-/
def m282_prevIndex (K : I64) (index : SCartesianIndex2) : SCartesianIndex2 :=
  if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
  else ⟨K, index.j - JInt.lit .i64 1⟩

/--
Julia source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
```
-/
def m288_indicesConstructor (K : Nat) (indices : Axis) : RResult (SCartesianIndices2 K) :=
  if 1 < K then .ok ⟨indices⟩ else .error .assertion

/--
Julia source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
```
-/
def m290_eachindexReshaped {A T S : Type} {K : Nat} (each : IndexStyleModel → A → Axis)
    (a : ReinterpretArray T S A) : RResult (SCartesianIndices2 K) :=
  m288_indicesConstructor K (each .linear (m369_parent a))

/--
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
def m291_eachindex {A : Type} {K : Nat} (each : IndexStyleModel → A → RResult (SCartesianIndices2 K))
    (mismatch : List Axis → List (List Axis) → RResult (SCartesianIndices2 K))
    (style : IndexStyleModel) (a : A) (rest : List A) (axes : A → List Axis) : RResult (SCartesianIndices2 K) := do
  let iter ← each style a
  let others ← rest.mapM (each style)
  if others.all (· == iter) then return iter else mismatch (axes a) (rest.map axes)

/--
Julia source: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
```
-/
def m298_indicesSize {K : Nat} (iter : SCartesianIndices2 K) : Nat × I64 :=
  (K, iter.indices2.length)

/--
Julia source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
```
-/
def m299_indicesAxes {K : Nat} (iter : SCartesianIndices2 K) : List Axis :=
  [⟨one, JInt.lit .i64 K⟩, iter.indices2]

/--
Julia source: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
```
-/
def m301_indicesFirst {K : Nat} (iter : SCartesianIndices2 K) : SCartesianIndex2 :=
  ⟨one, iter.indices2.first⟩

/--
Julia source: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
```
-/
def m302_indicesLast {K : Nat} (iter : SCartesianIndices2 K) : SCartesianIndex2 :=
  ⟨JInt.lit .i64 K, iter.indices2.first + iter.indices2.length - one⟩

/--
Julia source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
    @boundscheck checkbounds(iter, i, j)
    return SCartesianIndex2{K}(i, iter.indices2[j])
end
```
-/
def m304_indicesGet {K : Nat} (checkbounds : SCartesianIndices2 K → I64 → I64 → RResult Unit)
    (rangeGet : Axis → I64 → RResult I64) (iter : SCartesianIndices2 K) (i j : I64) : RResult SCartesianIndex2 := do
  checkbounds iter i j
  return ⟨i, ← rangeGet iter.indices2 j⟩

/--
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
def m309_indicesIterate {K : Nat} {σ : Type} (iterate : Axis → Option (I64 × σ))
    (iter : SCartesianIndices2 K) : Option (SCartesianIndex2 × (I64 × I64 × σ)) :=
  match iterate iter.indices2 with
  | none => none
  | some (item, state) => some (⟨one, item⟩, (one, item, state))

/--
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
def m316_indicesIterateState {K : Nat} {σ : Type} (iterate : Axis → σ → Option (I64 × σ))
    (iter : SCartesianIndices2 K) (state1 item2 : I64) (state2 : σ) :
    Option (SCartesianIndex2 × (I64 × I64 × σ)) :=
  if state1 < JInt.lit .i64 K then
    let item1 := state1 + one
    some (⟨item1, item2⟩, (item1, item2, state2))
  else match iterate iter.indices2 state2 with
    | none => none
    | some (item, state) => some (⟨one, item⟩, (one, item, state))

/--
Julia source: base/reinterpretarray.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimdLoop.simd_outer_range(iter::SCartesianIndices2) = iter.indices2
```
-/
def m327_simdOuter {K : Nat} (iter : SCartesianIndices2 K) : Axis := iter.indices2

/--
Julia source: base/reinterpretarray.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimdLoop.simd_inner_length(::SCartesianIndices2{K}, ::Any) where K = K
```
-/
def m328_simdInnerLength {K : Nat} (_iter : SCartesianIndices2 K) (_ : α) : Nat := K

/--
Julia source: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}
    SCartesianIndex2{K}(I1+1, Ilast)
end
```
-/
def m329_simdIndex {_K : Nat} (_last i1 : I64) : SCartesianIndex2 :=
  ⟨i1 + JInt.lit .i64 1, _last⟩

/--
Julia source: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...) = _maybe_reshape(IndexCartesian(), A, I...)
```
-/
def m333_maybeReshape {A R : Type} (fallback : IndexStyleModel → A → List I64 → R)
    (a : A) (indices : List I64) : R := fallback .cartesian a indices

/--
Julia source: base/reinterpretarray.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexSCartesian2, A::ReshapedReinterpretArray, I...) = A
```
-/
def m334_maybeReshapeIdentity {A : Type} (a : A) (_indices : List I64) : A := a

/--
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

/--
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

/--
Julia source: base/reinterpretarray.jl:359-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _scartesian2_trailing(style::IndexSCartesian2, A::AbstractArray, ind::SCartesianIndex2)
    k = ind.j - first(eachindex(style, A).indices2)
    ax = tail(axes(A))
    return length(ax) == 1 ? (first(ax[1]) + k,) : Tuple(CartesianIndices(ax)[k + 1])
end
```
-/
def m359_scartesian2Trailing {A : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → SCartesianIndices2 K)
    (axes : A → List Axis)
    (cartesianIndices : List Axis → I64 → List I64)
    (style : IndexStyleModel) (a : A) (index : SCartesianIndex2) : List I64 :=
  let k := index.j - (eachindex style a).indices2.first
  let tailAxes := (axes a).drop 1
  match tailAxes with
  | [axis] => [axis.first + k]
  | _ => cartesianIndices tailAxes (k + one)

/--
Julia source: base/reinterpretarray.jl:347-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getindex(style::IndexSCartesian2, A::AbstractArray, ind::SCartesianIndex2)
    @_propagate_inbounds_meta
    getindex(A, first(axes(A, 1)) + ind.i - 1, _scartesian2_trailing(style, A, ind)...)
end
```
-/
def m347_getindexCartesian {A R : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → SCartesianIndices2 K) (axes : A → List Axis)
    (cartesianIndices : List Axis → I64 → List I64)
    (getindex : A → List I64 → R) (style : IndexStyleModel) (a : A)
    (index : SCartesianIndex2) : R :=
  let firstAx1 := ((axes a).headD ⟨one, zero⟩).first
  getindex a ((firstAx1 + index.i - one) ::
    m359_scartesian2Trailing eachindex axes cartesianIndices style a index)

/--
Julia source: base/reinterpretarray.jl:352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(style::IndexSCartesian2, A::AbstractArray, v, ind::SCartesianIndex2)
    @_propagate_inbounds_meta
    setindex!(A, v, first(axes(A, 1)) + ind.i - 1, _scartesian2_trailing(style, A, ind)...)
end
```
-/
def m352_setindexCartesian {A V R : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → SCartesianIndices2 K) (axes : A → List Axis)
    (cartesianIndices : List Axis → I64 → List I64)
    (setindex : A → V → List I64 → R) (style : IndexStyleModel) (a : A) (value : V)
    (index : SCartesianIndex2) : R :=
  let firstAx1 := ((axes a).headD ⟨one, zero⟩).first
  setindex a value ((firstAx1 + index.i - one) ::
    m359_scartesian2Trailing eachindex axes cartesianIndices style a index)

/--
Julia source: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachindex(style::IndexSCartesian2, A::AbstractArray) = eachindex(style, parent(A))
```
-/
def m365_eachindex {A R : Type} (each : IndexStyleModel → A → R)
    (style : IndexStyleModel) (a : ReinterpretArray T S A) : R := each style (m369_parent a)
/--
Julia source: base/reinterpretarray.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(a::ReinterpretArray) = dataids(a.parent)
```
-/
def m370_dataids {T S A R : Type} (dataids : A → R) (a : ReinterpretArray T S A) : R := dataids a.parent

/--
Julia source: base/reinterpretarray.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(a::NonReshapedReinterpretArray{T}) where {T} = reinterpret(T, unaliascopy(a.parent))
```
-/
def m371_unaliascopy {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) := do
  let p ← copy a.parent
  if a.target.id == a.source.id then return .parent (m104_reinterpretIdentity p)
  return .view (← m73_reinterpret a.target a.source p)

/--
Julia source: base/reinterpretarray.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unaliascopy(a::ReshapedReinterpretArray{T}) where {T} = reinterpret(reshape, T, unaliascopy(a.parent))
```
-/
def m372_unaliascopyReshaped {T S A : Type} (copy : ArrayInput A → RResult (ArrayInput A))
    (a : ReinterpretArray T S (ArrayInput A)) :
    RResult (ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit) := do
  let p ← copy a.parent
  if a.target.id == a.source.id then return .parent (m145_reinterpretReshapeIdentity p)
  return .view (← m188_reinterpretReshape a.target a.source p)

/--
Julia source: base/reinterpretarray.jl:374-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function size(a::NonReshapedReinterpretArray{T,N,S} where {N}) where {T,S}
    psize = size(a.parent)
    size1 = issingletontype(T) ? psize[1] : div(psize[1]*aligned_sizeof(S), aligned_sizeof(T))
    tuple(size1, tail(psize)...)
end
```
-/
def m374_sizeNonReshaped {T S A : Type} (size : A → List I64)
    (divide : I64 → I64 → RResult I64) (a : ReinterpretArray T S A) : RResult (List I64) := do
  let psize := size a.parent
  let size1 ← if a.target.singleton then pure (psize.headD zero)
    else divide (psize.headD zero * a.source.alignedSize) a.target.alignedSize
  pure (size1 :: psize.drop 1)

/--
Julia source: base/reinterpretarray.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::NonReshapedReinterpretArray{T,0}) where {T} = ()
```
-/
def m385_sizeZero {T S A : Type} (_a : ReinterpretArray T S A) : List I64 := []

/--
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
def m387_axesNonReshaped {T S A : Type} (axes : A → List Axis)
    (divide : I64 → I64 → RResult I64) (oftype : Axis → I64 → I64 → Axis)
    (a : ReinterpretArray T S A) : RResult (List Axis) := do
  let paxs := axes a.parent
  let axis := paxs.headD ⟨one, zero⟩
  let size1 ← if a.target.singleton then pure axis.length
    else divide (axis.length * a.source.alignedSize) a.target.alignedSize
  pure (oftype axis axis.first (axis.first + size1 - one) :: paxs.drop 1)

/--
Julia source: base/reinterpretarray.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(a::NonReshapedReinterpretArray{T,0}) where {T} = ()
```
-/
def m399_axesZero {T S A : Type} (_a : ReinterpretArray T S A) : List Axis := []

/--
Julia source: base/reinterpretarray.jl:401-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_offset_axes(a::ReinterpretArray) = has_offset_axes(a.parent)
```
-/
def m401_hasOffset {T S A R : Type} (hasOffset : A → R) (a : ReinterpretArray T S A) : R := hasOffset a.parent

/--
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
def m403_elsize {T S A : Type} (parentElsize : A → I64) (a : ReinterpretArray T S A) : I64 :=
  if a.target.alignedSize == a.source.alignedSize then parentElsize a.parent else a.target.alignedSize

/--
Julia source: base/reinterpretarray.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = cconvert(Ptr{S}, a.parent)
```
-/
def m410_cconvert {T S A R : Type} (cconvert : TypeLayout → A → R)
    (a : ReinterpretArray T S A) : R := cconvert a.source a.parent

/--
Julia source: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = Ptr{T}(unsafe_convert(Ptr{S},a.parent))
```
-/
def m411_unsafeConvert {T S A R : Type} (unsafeConvert : TypeLayout → A → R)
    (castPointer : TypeLayout → R → R) (target : TypeLayout) (a : ReinterpretArray T S A) : R :=
  castPointer target (unsafeConvert a.source a.parent)

/--
Julia source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _is_scalar_reinterpret_applicable(T, S)
    isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
end
```
-/
def m469_scalarApplicable (target source : TypeLayout) : Bool :=
  target.primitive && source.primitive && target.bits == source.bits

/--
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

/--
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

/--
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
def m842_copytopacked (layout : TypeLayout) (output input : Bytes)
    (outOffset inOffset : I64) : RResult Bytes := do
  if layout.primitive then
    return memcpyValue output input outOffset inOffset (JInt.lit .i64 (← m816_packedsize layout))
  let mut result := output
  let mut writeOffset := zero
  for field in layout.fields.attach do
    let readOffset := JInt.lit .i64 field.val.1
    let child := field.val.2
    if m824_ispacked child then
      let readSize := child.alignedSize
      result := memcpyValue result input (outOffset + writeOffset) (inOffset + readOffset) readSize
      writeOffset := writeOffset + readSize
    else
      result ← m842_copytopacked child result input (outOffset + writeOffset) (inOffset + readOffset)
      writeOffset := writeOffset + JInt.lit .i64 (← m816_packedsize child)
  return result
termination_by sizeOf layout
decreasing_by
  cases layout
  have h := List.sizeOf_lt_of_mem field.property
  have hp : sizeOf field.val.2 < sizeOf field.val := by
    rcases field with ⟨⟨off, child⟩, hm⟩
    simp
    omega
  simp_all [TypeLayout.fields]
  omega

/--
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
def m862_copyfrompacked (layout : TypeLayout) (output input : Bytes)
    (outOffset inOffset : I64) : RResult Bytes := do
  if layout.primitive then
    return memcpyValue output input outOffset inOffset (JInt.lit .i64 (← m816_packedsize layout))
  let mut result := output
  let mut readOffset := zero
  for field in layout.fields.attach do
    let writeOffset := JInt.lit .i64 field.val.1
    let child := field.val.2
    if m824_ispacked child then
      let writeSize := child.alignedSize
      result := memcpyValue result input (outOffset + writeOffset) (inOffset + readOffset) writeSize
      readOffset := readOffset + writeSize
    else
      result ← m862_copyfrompacked child result input (outOffset + writeOffset) (inOffset + readOffset)
      readOffset := readOffset + JInt.lit .i64 (← m816_packedsize child)
  return result
termination_by sizeOf layout
decreasing_by
  cases layout
  have h := List.sizeOf_lt_of_mem field.property
  have hp : sizeOf field.val.2 < sizeOf field.val := by
    rcases field with ⟨⟨off, child⟩, hm⟩
    simp
    omega
  simp_all [TypeLayout.fields]
  omega

/--
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
def m913_reinterpretPadding (output input : TypeLayout) (bytes initial : Bytes) : RResult Bytes := do
  let inputPackedSize ← m816_packedsize input
  if 0 < input.fields.length && m824_ispacked output then
    m842_copytopacked input initial bytes zero zero
  else if 0 < output.fields.length && m824_ispacked input then
    m862_copyfrompacked output initial bytes zero zero
  else
    let packed ← m842_copytopacked input (List.replicate inputPackedSize 0) bytes zero zero
    m862_copyfrompacked output initial packed zero zero

/--
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
def m882_reinterpret (output input : TypeLayout) (bytes initial : Bytes) : RResult Bytes := do
  if !output.isBits then .error .argument
  if !input.isBits then .error .argument
  if m828_hasBitPadding output then .error .argument
  if m828_hasBitPadding input then .error .argument
  let inputSize ← m816_packedsize input
  let outputSize ← m816_packedsize output
  if inputSize != outputSize then .error .argument
  let samePadding ← if m824_ispacked input && m824_ispacked output then pure true
    else m812_structSubpadding output input
  if samePadding then
    return memcpyValue initial bytes zero zero output.alignedSize
  else m913_reinterpretPadding output input bytes initial

/--
Julia source: base/reinterpretarray.jl:421-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_ptr_indexable(a::ReinterpretArray{T,<:Any,S}) where {T,S}
    aligned_sizeof(T) === aligned_sizeof(S) && return false
    return check_ptr_indexable(parent(a))
end
```
-/
def m421_checkPtrIndexable {T S A : Type} (checkParent : A → Bool)
    (a : ReinterpretArray T S A) : Bool :=
  if a.target.alignedSize == a.source.alignedSize then false else checkParent (m369_parent a)

/--
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
def m461_getindexPtr {T S A : Type} (ops : PointerReadOps T S A)
    (a : ReinterpretArray T S A) (indices : List I64) : RResult Bytes := do
  ops.checkbounds a indices
  let li := ops.linearIndex a indices
  let ap := m410_cconvert ops.parentCconvert a
  let p := ops.addPointer (ops.unsafeConvert a.target ap) (m403_elsize ops.parentElsize a * (li - ops.firstindex a))
  ops.load a.parent p

/--
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
def m473_getindexNonReshaped {T S A : Type}
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes) (a : ReinterpretArray T S A)
    (i1 : I64) (tail : List I64) : RResult Bytes := do
  if a.target.singleton then
    checkbounds a i1 tail
    return []
  else if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent (i1 :: tail)
    return ← m882_reinterpret a.target a.source bytes (List.replicate a.target.alignedSize.val.toNat 0)
  else
    checkbounds a i1 tail
    let ts := a.target.alignedSize
    let ss := a.source.alignedSize
    let (start, offset) ← divremInt ((i1 - one) * ts) ss
    if (← remInt ts ss) == zero then
      let n ← divInt ts ss
      let mut result := List.replicate ts.val.toNat 0
      for i in intRange one n do
        let bytes ← getParent a.parent ((start + i) :: tail)
        result := memcpyValue result bytes ((i - one) * ss) zero ss
      return result
    else if (← remInt ss ts) == zero then
      let bytes ← getParent a.parent ((start + one) :: tail)
      return byteWindow bytes offset.val.toNat ts.val.toNat
    else
      copyLoop getParent a.parent tail start ss ts one zero offset (List.replicate ts.val.toNat 0)
where
  copyLoop (getParent : A → List I64 → RResult Bytes) (parent : A) (tail : List I64)
      (start ss ts i copied sidx : I64) (result : Bytes) : RResult Bytes :=
    if copied < ts then
      match getParent parent ((start + i) :: tail) with
      | .error e => .error e
      | .ok bytes =>
        let nb := if ss - sidx < ts - copied then ss - sidx else ts - copied
        let result := memcpyValue result bytes copied sidx nb
        copyLoop getParent parent tail start ss ts (i + one) (copied + nb) zero result
    else
      .ok result
  partial_fixpoint

/--
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
def m527_getindexReshaped {T S A : Type}
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes) (parentIndexStyle : A → IndexStyleModel)
    (firstindex : ReinterpretArray T S A → I64)
    (a : ReinterpretArray T S A) (i1 : I64) (tail : List I64) : RResult Bytes := do
  if a.target.singleton then
    checkbounds a i1 tail
    return []
  else if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent (i1 :: tail)
    return ← m882_reinterpret a.target a.source bytes (List.replicate a.target.alignedSize.val.toNat 0)
  checkbounds a i1 tail
  let ts := a.target.alignedSize
  let ss := a.source.alignedSize
  if ss ≤ ts then
    let mut result := List.replicate ts.val.toNat 0
    if ss < ts then
      let n ← divInt ts ss
      if tail.isEmpty && parentIndexStyle a.parent == .linear then
        let offset := n * (i1 - firstindex a)
        for i in intRange one n do
          let bytes ← getParent a.parent [i + offset]
          result := memcpyValue result bytes ((i - one) * ss) zero ss
      else
        for i in intRange one n do
          let bytes ← getParent a.parent (i :: i1 :: tail)
          result := memcpyValue result bytes ((i - one) * ss) zero ss
    else
      let bytes ← getParent a.parent (i1 :: tail)
      result := memcpyValue result bytes zero zero ss
    return result
  let bytes ← getParent a.parent tail
  return byteWindow bytes ((i1 - one) * ts).val.toNat ts.val.toNat

/--
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
def m442_getindexLinear {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) (i : I64) : RResult Bytes := do
  m237_checkReadable a
  if m421_checkPtrIndexable checkParent a then return ← m461_getindexPtr ops a [i]
  let style := if a.reshaped then
    m266_indexStyleReshaped parentIndexStyle a.parent a.target.alignedSize.val.toNat a.source.alignedSize.val.toNat
    else m263_indexStyle parentIndexStyle a.parent
  let inds := if style == .linear then [i] else toSubscripts a i
  let first := if inds.isEmpty then firstindex a else inds.headD one
  let rest := inds.drop 1
  if a.reshaped then m527_getindexReshaped checkbounds getParent parentIndexStyle firstindex a first rest
  else m473_getindexNonReshaped checkbounds getParent a first rest

/--
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
def m413_getindexZero {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) : RResult Bytes := do
  if m469_scalarApplicable a.target a.source then
    let bytes ← getParent a.parent []
    m882_reinterpret a.target a.source bytes (List.replicate a.target.alignedSize.val.toNat 0)
  else m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a (firstindex a)

/--
Julia source: base/reinterpretarray.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::ReshapedArray) = check_ptr_indexable(parent(a))
```
-/
def m425_checkPtrReshaped {A P : Type} (parent : A → P) (checkParent : P → Bool)
    (a : A) : Bool := checkParent (parent a)

/--
Julia source: base/reinterpretarray.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::FastContiguousSubArray) = check_ptr_indexable(parent(a))
```
-/
def m426_checkPtrSubarray {A P : Type} (parent : A → P) (checkParent : P → Bool)
    (a : A) : Bool := checkParent (parent a)

/--
Julia source: base/reinterpretarray.jl:427-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::Union{Array, Memory}) = true
```
-/
def m427_checkPtrDense (_a : A) : Bool := true

/--
Julia source: base/reinterpretarray.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_ptr_indexable(a::AbstractArray) = false
```
-/
def m428_checkPtrAbstract (_a : A) : Bool := false

/--
Julia source: base/reinterpretarray.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(a::ReshapedReinterpretArray{T,0}) where {T} = a[firstindex(a)]
```
-/
def m430_getindexZeroReshaped {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) : RResult Bytes :=
  m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a (firstindex a)

/--
Julia source: base/reinterpretarray.jl:434-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds _isassigned_ra(a::ReinterpretArray, inds...) = true # that is not entirely true, but computing exactly which indexes will be accessed in the parent requires a lot of duplication from the _getindex_ra code
```
-/
def m434_isassignedRa {T S A : Type} (_a : ReinterpretArray T S A) (_indices : List I64) : Bool := true

/--
Julia source: base/reinterpretarray.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isassigned(a::ReinterpretArray, inds::Integer...) = checkbounds(Bool, a, inds...) && (check_ptr_indexable(a) || _isassigned_ra(a, inds...))
```
-/
def m432_isassigned {T S A : Type} (checkbounds : ReinterpretArray T S A → List I64 → Bool)
    (checkParent : A → Bool) (a : ReinterpretArray T S A) (indices : List I64) : Bool :=
  checkbounds a indices && (m421_checkPtrIndexable checkParent a || m434_isassignedRa a indices)

/--
Julia source: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isassigned(a::ReinterpretArray, inds::SCartesianIndex2) = isassigned(a.parent, inds.j)
```
-/
def m433_isassignedCartesian {T S A : Type} (parentAssigned : A → I64 → Bool)
    (a : ReinterpretArray T S A) (index : SCartesianIndex2) : Bool := parentAssigned a.parent index.j

/--
Julia source: base/reinterpretarray.jl:436-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(a::ReinterpretArray{T,N,S}, inds::Vararg{Int, N}) where {T,N,S}
    check_readable(a)
    check_ptr_indexable(a) && return _getindex_ptr(a, inds...)
    _getindex_ra(a, inds[1], tail(inds))
end
```
-/
def m436_getindex {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel)
    (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (getParent : A → List I64 → RResult Bytes)
    (a : ReinterpretArray T S A) (i1 : I64) (tail : List I64) : RResult Bytes := do
  m237_checkReadable a
  if m421_checkPtrIndexable checkParent a then m461_getindexPtr ops a (i1 :: tail)
  else if a.reshaped then m527_getindexReshaped checkbounds getParent parentIndexStyle firstindex a i1 tail
  else m473_getindexNonReshaped checkbounds getParent a i1 tail

/--
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
def m454_getindexCartesian {T S A : Type} (getParent : A → List I64 → RResult Bytes)
    (a : ReinterpretArray T S A) (index : SCartesianIndex2) : RResult Bytes := do
  m237_checkReadable a
  let s ← getParent a.parent [index.j]
  let ts := a.target.alignedSize
  return byteWindow s ((index.i - one) * ts).val.toNat ts.val.toNat

/--
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
def m610_setindexPtr {T S A V : Type} (ops : PointerWriteOps T S A V)
    (a : ReinterpretArray T S A) (value : V) (indices : List I64) : RResult (ReinterpretArray T S A) := do
  ops.checkbounds a indices
  let li := ops.linearIndex a indices
  let ap := m410_cconvert ops.parentCconvert a
  let p := ops.addPointer (ops.unsafeConvert a.target ap) (m403_elsize ops.parentElsize a * (li - ops.firstindex a))
  let parent ← ops.store a.parent p value
  pure { a with parent := parent }

/--
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
def m619_setindexNonReshaped {T S A V : Type}
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  let valueBytes ← convertValue a.target value
  if a.target.singleton then
    checkbounds a i1 tail
    return a
  else if m469_scalarApplicable a.target a.source then
    let sourceBytes ← m882_reinterpret a.source a.target valueBytes (List.replicate a.source.alignedSize.val.toNat 0)
    let p ← parent.set a.parent (i1 :: tail) sourceBytes
    return { a with parent := p }
  else
    checkbounds a i1 tail
    let ts := a.target.alignedSize
    let ss := a.source.alignedSize
    let (start, sidx) ← divremInt ((i1 - one) * ts) ss
    let mut p := a.parent
    if (← remInt ts ss) == zero then
      let n ← divInt ts ss
      for i in intRange one n do
        let bytes := byteWindow valueBytes ((i - one) * ss).val.toNat ss.val.toNat
        p ← parent.set p ((start + i) :: tail) bytes
    else if (← remInt ss ts) == zero then
      let old ← parent.get p ((start + one) :: tail)
      let bytes := memcpyValue old valueBytes sidx zero ts
      p ← parent.set p ((start + one) :: tail) bytes
    else
      let mut copied := zero
      let mut i := one
      let mut s := List.replicate ss.val.toNat 0
      if sidx != zero then
        s ← parent.get p ((start + i) :: tail)
        let nb := if ss - sidx < ts then ss - sidx else ts
        s := memcpyValue s valueBytes sidx zero nb
        copied := copied + nb
        p ← parent.set p ((start + i) :: tail) s
        i := i + one
      let (p', _, copied', i') ← mainLoop parent tail valueBytes start ss ts p s copied i
      p := p'
      if copied' < ts then
        let s' ← parent.get p ((start + i') :: tail)
        let nb := if ss < ts - copied' then ss else ts - copied'
        let s' := memcpyValue s' valueBytes zero copied' nb
        p ← parent.set p ((start + i') :: tail) s'
    return { a with parent := p }
where
  mainLoop (parent : ParentOps A) (tail : List I64) (valueBytes : Bytes)
      (start ss ts : I64) (p : A) (s : Bytes) (copied i : I64) :
      RResult (A × Bytes × I64 × I64) :=
    if copied < ts && ss < ts - copied then
      let nb := if ss < ts - copied then ss else ts - copied
      let s := memcpyValue s valueBytes zero copied nb
      let copied := copied + nb
      match parent.set p ((start + i) :: tail) s with
      | .error e => .error e
      | .ok p => mainLoop parent tail valueBytes start ss ts p s copied (i + one)
    else
      .ok (p, s, copied, i)
  partial_fixpoint

/--
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
def m688_setindexReshaped {T S A V : Type}
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  let valueBytes ← convertValue a.target value
  if a.target.singleton then
    checkbounds a i1 tail
    return a
  else if m469_scalarApplicable a.target a.source then
    let sourceBytes ← m882_reinterpret a.source a.target valueBytes (List.replicate a.source.alignedSize.val.toNat 0)
    let p ← parent.set a.parent (i1 :: tail) sourceBytes
    return { a with parent := p }
  else
    checkbounds a i1 tail
    let ts := a.target.alignedSize
    let ss := a.source.alignedSize
    let mut p := a.parent
    if ss ≤ ts then
      if ss < ts then
        let n ← divInt ts ss
        if tail.isEmpty && parentIndexStyle a.parent == .linear then
          let offset := n * (i1 - firstindex a)
          for i in intRange one n do
            let bytes := byteWindow valueBytes ((i - one) * ss).val.toNat ss.val.toNat
            p ← parent.set p [i + offset] bytes
        else
          for i in intRange one n do
            let bytes := byteWindow valueBytes ((i - one) * ss).val.toNat ss.val.toNat
            p ← parent.set p (i :: i1 :: tail) bytes
      else
        p ← parent.set p (i1 :: tail) (byteWindow valueBytes 0 ss.val.toNat)
    else
      let s ← parent.get p tail
      let bytes := memcpyValue s valueBytes ((i1 - one) * ts) zero ts
      p ← parent.set p tail bytes
    return { a with parent := p }

/--
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
def m588_setindexLinear {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) (value : V) (i : I64) : RResult (ReinterpretArray T S A) := do
  m244_checkWritable a
  if m421_checkPtrIndexable checkParent a then return ← m610_setindexPtr ops a value [i]
  let style := if a.reshaped then
    m266_indexStyleReshaped parentIndexStyle a.parent a.target.alignedSize.val.toNat a.source.alignedSize.val.toNat
    else m263_indexStyle parentIndexStyle a.parent
  let inds := if style == .linear then [i] else toSubscripts a i
  let first := if inds.isEmpty then firstindex a else inds.headD one
  let rest := inds.drop 1
  if a.reshaped then m688_setindexReshaped checkbounds convertValue parent parentIndexStyle firstindex a value first rest
  else m619_setindexNonReshaped checkbounds convertValue parent a value first rest

/--
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
def m572_setindexZero {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) (value : V) : RResult (ReinterpretArray T S A) := do
  if m469_scalarApplicable a.target a.source then
    let bytes ← convertValue a.target value
    let sourceBytes ← m882_reinterpret a.source a.target bytes (List.replicate a.source.alignedSize.val.toNat 0)
    let p ← parent.set a.parent [] sourceBytes
    pure { a with parent := p }
  else m588_setindexLinear ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a value (firstindex a)

/--
Julia source: base/reinterpretarray.jl:580-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds setindex!(a::ReshapedReinterpretArray{T,0}, v) where {T} = setindex!(a, v, firstindex(a))
```
-/
def m580_setindexZeroReshaped {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (toSubscripts : ReinterpretArray T S A → I64 → List I64)
    (a : ReinterpretArray T S A) (value : V) : RResult (ReinterpretArray T S A) :=
  m588_setindexLinear ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a value (firstindex a)

/--
Julia source: base/reinterpretarray.jl:582-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(a::ReinterpretArray{T,N,S}, v, inds::Vararg{Int, N}) where {T,N,S}
    check_writable(a)
    check_ptr_indexable(a) && return _setindex_ptr!(a, v, inds...)
    _setindex_ra!(a, v, inds[1], tail(inds))
end
```
-/
def m582_setindex {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
    (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
    (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (a : ReinterpretArray T S A) (value : V) (i1 : I64) (tail : List I64) :
    RResult (ReinterpretArray T S A) := do
  m244_checkWritable a
  if m421_checkPtrIndexable checkParent a then m610_setindexPtr ops a value (i1 :: tail)
  else if a.reshaped then m688_setindexReshaped checkbounds convertValue parent parentIndexStyle firstindex a value i1 tail
  else m619_setindexNonReshaped checkbounds convertValue parent a value i1 tail

/--
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
def m598_setindexCartesian {T S A V : Type}
    (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
    (a : ReinterpretArray T S A) (value : V) (index : SCartesianIndex2) : RResult (ReinterpretArray T S A) := do
  m244_checkWritable a
  let valueBytes ← convertValue a.target value
  let old ← parent.get a.parent [index.j]
  let changed := memcpyValue old valueBytes ((index.i - one) * a.target.alignedSize) zero a.target.alignedSize
  let p ← parent.set a.parent [index.j] changed
  pure { a with parent := p }

/--
Julia source: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, p::PaddingError)
    print(io, "Padding of type $(p.S) is not compatible with type $(p.T).")
end
```
-/
def m741_showerror (p : PaddingErrorModel) : String :=
  "Padding of type " ++ p.source ++ " is not compatible with type " ++ p.target ++ "."

/--
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
def m937_string {T S A R : Type} (length : ReinterpretArray T S A → I64)
    (emptyString : R) (callString : ReinterpretArray T S A → I64 → RResult R)
    (a : ReinterpretArray T S A) : RResult R := do
  let len := length a
  if len == zero then return emptyString
  m237_checkReadable a
  callString a len

/--
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
def m956_mapreduceImpl {A F OP X V : Type} {K : Nat}
    (get : A → SCartesianIndex2 → RResult X) (map : F → X → RResult V)
    (combine : OP → V → V → RResult V) (a : A) (f : F) (op : OP)
    (ifirst ilast : SCartesianIndex2) (blocksize : I64) : Option (RResult V) := do
  if ilast.j - ifirst.j < blocksize then return (← pure (do
    let a1 ← get a ifirst
    let a2 ← get a ⟨JInt.lit .i64 2, ifirst.j⟩
    let mut value ← combine op (← map f a1) (← map f a2)
    for i in intRange (ifirst.i + JInt.lit .i64 2) (JInt.lit .i64 K) do
      let ai ← get a ⟨i, ifirst.j⟩
      value ← combine op value (← map f ai)
    for j in intRange (ifirst.j + one) ilast.j do
      for i in intRange one (JInt.lit .i64 K) do
        let ai ← get a ⟨i, j⟩
        value ← combine op value (← map f ai)
    return value : RResult V))
  else
    let mid := ifirst.j + ashr_int (ilast.j - ifirst.j) one
    let r1 ← m956_mapreduceImpl (K := K) get map combine a f op ifirst ⟨JInt.lit .i64 K, mid⟩ blocksize
    match r1 with
    | .error e => return .error e
    | .ok v1 =>
      let r2 ← m956_mapreduceImpl (K := K) get map combine a f op ⟨one, mid + one⟩ ilast blocksize
      return do
        let v2 ← r2
        combine op v1 v2
partial_fixpoint

/--
Julia source: base/reinterpretarray.jl:984-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted, ifirst::SCartesianIndex2, ilast::SCartesianIndex2) where {F,OP} =
    mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
```
-/
def m984_mapreduceDefault {A F OP X V : Type} {K : Nat}
    (blocksize : F → OP → I64) (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (a : A) (f : F) (op : OP) (ifirst ilast : SCartesianIndex2) : Option (RResult V) :=
  m956_mapreduceImpl (K := K) get map combine a f op ifirst ilast (blocksize f op)

/--
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
def m946_mapreduce {A F OP X V E : Type} {K : Nat}
    (eachindex : IndexStyleModel → A → RResult (SCartesianIndices2 K))
    (iteratorEltype : A → E) (empty : F → OP → A → E → RResult V)
    (blocksize : F → OP → I64) (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (f : F) (op : OP) (style : IndexStyleModel) (a : A) : Option (RResult V) :=
  match eachindex style a with
  | .error e => some (.error e)
  | .ok inds =>
    let n := (m298_indicesSize inds).2
    if n == zero then some (empty f op a (iteratorEltype a))
    else m984_mapreduceDefault (K := K) blocksize get map combine a f op (m301_indicesFirst inds) (m302_indicesLast inds)

/--
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
def m990_totuple {A R X : Type} (arrayLength : ArrayInput A → I64)
    (totupleError : TypeLayout → RResult R) (eltypeMatches : ArrayInput A → TypeLayout → Bool)
    (viewPrefix : ArrayInput A → I64 → RResult (ArrayInput A))
    (ops : PointerReadOps R X (ArrayInput A))
    (checkParent : ArrayInput A → Bool) (parentIndexStyle : ArrayInput A → IndexStyleModel)
    (firstindex : ReinterpretArray R X (ArrayInput A) → I64)
    (checkbounds : ReinterpretArray R X (ArrayInput A) → I64 → List I64 → RResult Unit)
    (getParent : ArrayInput A → List I64 → RResult Bytes)
    (toSubscripts : ReinterpretArray R X (ArrayInput A) → I64 → List I64)
    (tupleFromBytes : Bytes → RResult R)
    (collectTuple : TypeLayout → JuliaLean.base.iterators.Take (ArrayInput A) → RResult R)
    (tupleType elementType : TypeLayout) (n : I64) (itr : ArrayInput A) : RResult R := do
  let needed := n + JInt.lit .i64 32
  if arrayLength itr < needed then totupleError tupleType
  else if elementType.isBits && eltypeMatches itr elementType then
    let view ← if arrayLength itr == needed then pure itr else viewPrefix itr needed
    let reinterpret : ReinterpretArray R X (ArrayInput A) ← m73_reinterpret tupleType elementType view
    let bytes ← m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts reinterpret one
    tupleFromBytes bytes
  else
    let taken ← match JuliaLean.base.iterators.takeModel (JuliaLean.base.int.convert .i64)
        (JuliaLean.base.iterators.mkTake
          (fun n => pure (JuliaLean.base.int.lt n (JInt.lit .i64 0)))
          (JuliaLean.base.int.convert .i64) (fun message => .error (.argumentError message))) itr needed with
      | .ok t => pure t
      | .error _ => .error .argument
    collectTuple elementType taken

end JuliaLean.base.reinterpretarray




namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- Reuse the installed native-arity tuple representation at base/reinterpretarray.jl:91. -/
-- Source: base/reinterpretarray.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             ax1 = axes(a)[1]
-- /Source
abbrev NativeTuple := JuliaLean.base.abstractarray.Models1Group1.Tuple

/-- Effect channel for the additive models. Existing concrete callees retain their own error constructors; invalid runtime type parameters produce Julia TypeError. A larger surrounding monad may additionally carry arbitrary user exceptions.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
inductive Error where
  | reinterpret (error : ReinterpretError)
  | array (error : JuliaLean.base.abstractarray.ArrayError)
  | range (error : JuliaLean.base.range.Exc)
  | tuple (error : JuliaLean.base.tuple.TupleError)
  | typeError
  deriving Repr, DecidableEq

/-- Effect channel for the additive models. Existing concrete callees retain their own error constructors; invalid runtime type parameters produce Julia TypeError. A larger surrounding monad may additionally carry arbitrary user exceptions.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
def liftResult {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {E α : Type} (wrap : E → Error) : Except E α → m α
  | .ok a => pure a
  | .error e => throw (wrap e)

/-- Effect channel for the additive models. Existing concrete callees retain their own error constructors; invalid runtime type parameters produce Julia TypeError. A larger surrounding monad may additionally carry arbitrary user exceptions.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
def liftReinterpret {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {α : Type} (r : RResult α) : m α := liftResult Error.reinterpret r

/-- A scalar retaining its actual native-Int or other runtime type. Other may be a tagged heterogeneous carrier. The parameter flag records runtime membership in the class of admissible Julia type-parameter values, not a callee correctness assumption. Native arithmetic is always the installed wrapping Int arithmetic.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
inductive Value (Other : Type) where
  | native (value : I64)
  | other (value : Other) (typeParameter : Bool)
  deriving Repr

/-- A scalar retaining its actual native-Int or other runtime type. Other may be a tagged heterogeneous carrier. The parameter flag records runtime membership in the class of admissible Julia type-parameter values, not a callee correctness assumption. Native arithmetic is always the installed wrapping Int arithmetic.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
structure ValueOps (m : Type → Type) (Other : Type) where
  multiplyInt : Other → I64 → m (Value Other)
  remainderInt : Other → I64 → m (Value Other)
  equalInt : Other → I64 → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  notEqualInt : Other → I64 → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  addInt : Other → I64 → m (Value Other)
  subtractInt : Other → I64 → m (Value Other)
  greaterInt : Other → I64 → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  divideFromInt : I64 → Other → m (Value Other)

/-- A scalar retaining its actual native-Int or other runtime type. Other may be a tagged heterogeneous carrier. The parameter flag records runtime membership in the class of admissible Julia type-parameter values, not a callee correctness assumption. Native arithmetic is always the installed wrapping Int arithmetic.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
def requireBool {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type} :
    JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O) → m Bool
  | .accepted b => pure b
  | .rejected _ => throw Error.typeError

/-- A scalar retaining its actual native-Int or other runtime type. Other may be a tagged heterogeneous carrier. The parameter flag records runtime membership in the class of admissible Julia type-parameter values, not a callee correctness assumption. Native arithmetic is always the installed wrapping Int arithmetic.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
def addInt {m : Type → Type} [Monad m] {O : Type}
    (ops : ValueOps m O) (x : Value O) (y : I64) : m (Value O) :=
  match x with
  | .native n => pure (.native (n + y))
  | .other n _ => ops.addInt n y

/-- The same immutable parent-backed view fields as the installed model, retaining the full runtime rank value rather than coercing it to Nat. Parent values may be heap handles, so no parent copy or loss of alias identity occurs.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
structure View (Other A : Type) where
  parent : A
  rank : Value Other
  target : TypeLayout
  source : TypeLayout
  readable : Bool
  writable : Bool
  reshaped : Bool

/-- Open array and scalar dispatch in the two constructor bodies. Native axes tuples have representable arity; Axis and Other retain custom/non-native Julia values. Only operations whose argument types are unfixed are fields. Concrete padding recursion, tuple indexing, native arithmetic, and OneTo construction are called directly by the models. The eltype observations in diagnostics remain separate effectful calls.
Source reference: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
--     reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
-- 
--     # With reshaping
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
inductive AxesValue (Axis Other : Type) where
  | tuple (axes : NativeTuple Axis)
  | other (value : Other)

/-- Open array and scalar dispatch in the two constructor bodies. Native axes tuples have representable arity; Axis and Other retain custom/non-native Julia values. Only operations whose argument types are unfixed are fields. Concrete padding recursion, tuple indexing, native arithmetic, and OneTo construction are called directly by the models. The eltype observations in diagnostics remain separate effectful calls.
Source reference: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
--     reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
-- 
--     # With reshaping
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
inductive TypeValue (Other : Type) where
  | type (layout : TypeLayout)
  | other (value : Other)

/-- Open array and scalar dispatch in the two constructor bodies. Native axes tuples have representable arity; Axis and Other retain custom/non-native Julia values. Only operations whose argument types are unfixed are fields. Concrete padding recursion, tuple indexing, native arithmetic, and OneTo construction are called directly by the models. The eltype observations in diagnostics remain separate effectful calls.
Source reference: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
--     reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
-- 
--     # With reshaping
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
structure ConstructorOps (m : Type → Type) (A Axis Other : Type) where
  values : ValueOps m Other
  axes : A → m (AxesValue Axis Other)
  axesGet : Other → I64 → m Axis
  length : Axis → m (Value Other)
  first : Axis → m (Value Other)
  ndims : A → m (Value Other)
  axis : A → I64 → m Axis
  equalOneTo : Axis → JuliaLean.base.range.OneTo I64 →
    m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  eltype : A → m (TypeValue Other)
  alignedSizeOther : Other → m (Value Other)

/-- Open array and scalar dispatch in the two constructor bodies. Native axes tuples have representable arity; Axis and Other retain custom/non-native Julia values. Only operations whose argument types are unfixed are fields. Concrete padding recursion, tuple indexing, native arithmetic, and OneTo construction are called directly by the models. The eltype observations in diagnostics remain separate effectful calls.
Source reference: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
--     reinterpret(::Type{T}, a::AbstractArray{T}) where {T} = a
-- 
--     # With reshaping
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
def axesGet {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : ConstructorOps m A Axis O)
    (axes : AxesValue Axis O) (i : I64) : m Axis :=
  match axes with
  | .tuple tuple => liftResult Error.array
      (JuliaLean.base.abstractarray.tupleGet tuple.values i)
  | .other value => ops.axesGet value i

/-- Payload-polymorphic diagnostic. LazyString captures msg without printing or converting it. At the installed exception-class boundary this throws ArgumentError for every msg, including non-string objects.
Source reference: base/reinterpretarray.jl:18-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:18-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function throwsize0(S::Type, T::Type, msg)
--         @noinline
--         throw(ArgumentError(LazyString("cannot reinterpret a zero-dimensional `", S, "` array to `", T,
--             "` which is of a ", msg, " size")))
--     end
-- /Source
def throwSize0 {Msg α : Type} (_source _target : TypeLayout) (_msg : Msg) : RResult α :=
  .error .argument

/-- Payload-polymorphic diagnostic retaining all accepted dimension values. LazyString only captures dim, so no conversion or display dispatch occurs here.
Source reference: base/reinterpretarray.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:74-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
-- /Source
def throwNonIntegral {Dim α : Type} (_source _target : TypeLayout) (_dim : Dim) : RResult α :=
  .error .argument

/-- Payload-polymorphic diagnostic for arbitrary custom first-axis values. No axis method or display method is evaluated while capturing this LazyString.
Source reference: base/reinterpretarray.jl:80-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:80-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
-- /Source
def throwFirstAxis {Axis α : Type} (_source _target : TypeLayout) (_axis : Axis) : RResult α :=
  .error .argument

/-- The source accepts arbitrary S and T. LazyString stores both payloads and throws ArgumentError without inspecting or rendering them.
Source reference: base/reinterpretarray.jl:119-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:119-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
-- /Source
def throwFromSingleton {S T α : Type} (_source : S) (_target : T) : RResult α :=
  .error .argument

/-- The generic reshape wrapper calls the concrete ReinterpretArray constructor, with the original array handle. It performs no preliminary size, axes, or parent materialization.
Source reference: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
-- /Source
inductive ConstructorArgument (A Custom : Type) where
  | generic (array : A)
  | custom (array : Custom)

/-- The generic reshape wrapper calls the concrete ReinterpretArray constructor, with the original array handle. It performs no preliminary size, axes, or parent materialization.
Source reference: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
-- /Source
structure ReshapeDispatchOps (m : Type → Type) (Custom R : Type) where
  custom : TypeLayout → Custom → m R

/-- Open parent dispatch: the type of a.parent is not fixed by this method. The selected reinterpret call retains its original arguments and effect channel. The complete known generic constructor is separate above and may be selected through the interface.
Source reference: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::Type{T}, a::NonReshapedReinterpretArray) where {T} = reinterpret(T, a.parent)
-- /Source
structure ParentReinterpretOps (m : Type → Type) (A R : Type) where
  reinterpret : TypeLayout → A → m R

/-- Open parent dispatch: the type of a.parent is not fixed by this method. The selected reinterpret call retains its original arguments and effect channel. The complete known generic constructor is separate above and may be selected through the interface.
Source reference: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::Type{T}, a::NonReshapedReinterpretArray) where {T} = reinterpret(T, a.parent)
-- /Source
def reinterpretParent {m : Type → Type} {A R O : Type}
    (ops : ParentReinterpretOps m A R) (target : TypeLayout) (a : View O A) : m R :=
  ops.reinterpret target a.parent

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- Only non-native operand pairs select these arbitrary scalar methods. Their argument and result runtime types, mutations and errors remain unrestricted. The concrete native/native helpers below never call these fields.
Source reference: base/reinterpretarray.jl:89-99; base/reinterpretarray.jl:128-139; base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
-- /Source
-- Source: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
-- /Source
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
structure ScalarOps (m : Type → Type) (Other : Type) where
  equal : Value Other → Value Other → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  notEqual : Value Other → Value Other → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  greater : Value Other → Value Other → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  less : Value Other → Value Other → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  add : Value Other → Value Other → m (Value Other)
  subtract : Value Other → Value Other → m (Value Other)
  multiply : Value Other → Value Other → m (Value Other)
  remainder : Value Other → Value Other → m (Value Other)
  divide : Value Other → Value Other → m (Value Other)

/-- Native Int comparison is concrete; other operand types retain their selected comparison and its Bool-context type assertion, including errors and preceding effects.
Source reference: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
-- /Source
def scalarEqual {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m Bool := do
  match left, right with
  | .native left, .native right => pure (left == right)
  | _, _ => requireBool (← ops.equal left right)

/-- Native Int comparison is concrete; other operand types retain their selected comparison and its Bool-context type assertion, including errors and preceding effects.
Source reference: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
-- /Source
def scalarNotEqual {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m Bool := do
  match left, right with
  | .native left, .native right => pure (left != right)
  | _, _ => requireBool (← ops.notEqual left right)

/-- Native Int comparison is concrete; other operand types retain their selected comparison and its Bool-context type assertion, including errors and preceding effects.
Source reference: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
-- /Source
def scalarGreater {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m Bool := do
  match left, right with
  | .native left, .native right => pure (decide (left > right))
  | _, _ => requireBool (← ops.greater left right)

/-- Native Int comparison is concrete; other operand types retain their selected comparison and its Bool-context type assertion, including errors and preceding effects.
Source reference: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
def scalarLess {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m Bool := do
  match left, right with
  | .native left, .native right => pure (decide (left < right))
  | _, _ => requireBool (← ops.less left right)

/-- Native Int arithmetic uses the installed fixed-width wrapping operation; every other operand pair is a selected arbitrary dispatch with its exact argument order.
Source reference: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
-- /Source
def scalarAdd {m : Type → Type} [Monad m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m (Value O) :=
  match left, right with
  | .native left, .native right => pure (.native (left + right))
  | _, _ => ops.add left right

/-- Native Int arithmetic uses the installed fixed-width wrapping operation; every other operand pair is a selected arbitrary dispatch with its exact argument order.
Source reference: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
-- /Source
def scalarSubtract {m : Type → Type} [Monad m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m (Value O) :=
  match left, right with
  | .native left, .native right => pure (.native (left - right))
  | _, _ => ops.subtract left right

/-- Native Int arithmetic uses the installed fixed-width wrapping operation; every other operand pair is a selected arbitrary dispatch with its exact argument order.
Source reference: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
-- /Source
def scalarMultiply {m : Type → Type} [Monad m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m (Value O) :=
  match left, right with
  | .native left, .native right => pure (.native (left * right))
  | _, _ => ops.multiply left right

/-- Native signed Int division/remainder retains its concrete DivideError behavior and wrapping representation; other operand pairs retain their selected operation and arbitrary result.
Source reference: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
-- /Source
def scalarRemainder {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m (Value O) :=
  match left, right with
  | .native left, .native right => return .native (← liftReinterpret (remInt left right))
  | _, _ => ops.remainder left right

/-- Native signed Int division/remainder retains its concrete DivideError behavior and wrapping representation; other operand pairs retain their selected operation and arbitrary result.
Source reference: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:128-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
-- /Source
def scalarDivide {m : Type → Type} [Monad m] [MonadExceptOf Error m] {O : Type}
    (ops : ScalarOps m O) (left right : Value O) : m (Value O) :=
  match left, right with
  | .native left, .native right => return .native (← liftReinterpret (divInt left right))
  | _, _ => ops.divide left right

/-- Type{T}/Type{S} are unfixed dispatch arguments, so every type query retains its selected method, non-native/non-Bool return and effects. TypeLayout.id preserves type identity; no query result is inferred from static layout flags. Subpadding stays raw until new performs Bool field conversion.
Source reference: base/reinterpretarray.jl:85-103; base/reinterpretarray.jl:124-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:85-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:124-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
structure TypeQueryOps (m : Type → Type) (Other : Type) where
  isBits : TypeLayout → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  bitPadding : TypeLayout → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  singleton : TypeLayout → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  alignedSize : TypeLayout → m (Value Other)
  alignedOther : Other → m (Value Other)
  subpadding : TypeLayout → TypeLayout → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))

/-- An arbitrary eltype result may be an actual Type value or a non-Type custom object. Both aligned_sizeof dispatches remain selected and effectful; neither branch reads a cached static size.
Source reference: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
-- /Source
def alignedSizeValue {m : Type → Type} {O : Type}
    (ops : TypeQueryOps m O) : TypeValue O → m (Value O)
  | .type layout => ops.alignedSize layout
  | .other value => ops.alignedOther value

/-- Core type application accepts each admissible runtime type-parameter value and rejects every other value before any subsequent field conversion or object allocation. The admission tag is runtime metadata, not a law about a selected callee.
Source reference: base/reinterpretarray.jl:100-103; base/reinterpretarray.jl:141-144; base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:141-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
def checkRuntimeParameter {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (value : Value O) : m Unit :=
  match value with
  | .other _ false => throw Error.typeError
  | _ => pure ()

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean


/-- The integer-multiple diagnostic evaluates both selected aligned_sizeof calls, target before source, before capturing their arbitrary values in the lazy message. Neither result is consumed as an integer or Boolean. A selected call may mutate state or throw before the final ArgumentError.
Source reference: base/reinterpretarray.jl:108-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:108-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
-- /Source
def throwIntMultiple {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O α : Type} (types : TypeQueryOps m O) (source target : TypeLayout) : m α := do
  let _targetSize ← types.alignedSize target
  let _sourceSize ← types.alignedSize source
  throw (.reinterpret .argument)


/-- Preserve all eager diagnostic argument evaluation, including both eltype calls, the intervening axis query, selected target-size query, and the second element-type-dependent size query. The actual two size results are divided with native behavior only when both are native Int. Every selected error and state effect precedes the final ArgumentError; no diagnostic payload is rendered eagerly.
Source reference: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
-- /Source
def throwSize1Dispatched {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O α : Type} (arrays : ConstructorOps m A Axis O)
    (types : TypeQueryOps m O) (scalars : ScalarOps m O)
    (a : A) (target : TypeLayout) : m α := do
  let _firstElementType ← arrays.eltype a
  let _axis ← arrays.axis a one
  let targetSize ← types.alignedSize target
  let secondElementType ← arrays.eltype a
  let sourceSize ← alignedSizeValue types secondElementType
  let _ratio ← scalarDivide scalars targetSize sourceSize
  throw (.reinterpret .argument)


end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- Complete constructor dispatch boundaries: TypeLayout retains the identity of any admissible element parameter, including a non-Type parameter of AbstractArray; its layout flags are not consulted. isType records actual runtime Type membership, used only for local diagnostic method signature dispatch. Array operations retain the full tuple/custom-axis representation, unfixed parameter queries stay effectful, every non-native scalar pair retains selected dispatch, and non-native OneTo/Bool conversion results remain arbitrary. Source bodies perform control flow and allocation explicitly.
Source reference: base/reinterpretarray.jl:73-103; base/reinterpretarray.jl:107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
structure DynamicConstructorOps (m : Type → Type) (A Axis Other : Type) where
  arrays : ConstructorOps m A Axis Other
  isType : TypeLayout → Bool
  types : TypeQueryOps m Other
  scalars : ScalarOps m Other
  convertBool : Other → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  oneToOther : Other → m (Value Other)
  equalAxisOther : Axis → Value Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))

/-- Prepare a Bool field exactly as new lowering does: an already-Bool value skips convert, a native Int uses the installed concrete Bool constructor, and another runtime type selects convert(Bool,value). A wrong conversion return is retained until all fields are prepared and new performs its final type checks. Conversion exceptions still stop immediately.
Source reference: base/reinterpretarray.jl:100-103; base/reinterpretarray.jl:141-144; base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:141-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
-- Source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
-- /Source
def prepareViewBool {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : DynamicConstructorOps m A Axis O)
    (value : JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O)) :
    m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O)) := do
  match value with
  | .accepted boolean => pure (.accepted boolean)
  | .rejected (.native native) =>
      let boolean ← liftResult (fun error => Error.array (.julia error))
        (JuliaLean.base.bool.boolFromReal (fun (x : I64) n => pure (decide (x.val = n))) native)
      pure (.accepted boolean)
  | .rejected (.other other _) => ops.convertBool other

/-- The concrete new expression applies runtime type parameters before field conversion, preserves the parent because a::A already passes its field isa guard, converts readable before writable, and validates returned field types only after both conversion expressions finish. This ordering follows pinned src/julia-syntax.scm795-806,826-830,3870-3893; no constructor or type-application callback replaces it.
Source reference: base/reinterpretarray.jl:100-103; base/reinterpretarray.jl:141-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
-- Source: base/reinterpretarray.jl:141-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
def newDynamicView {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : DynamicConstructorOps m A Axis O)
    (target source : TypeLayout) (a : A) (rank : Value O)
    (readable writable : JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
    (reshaped : Bool) : m (View O A) := do
  checkRuntimeParameter rank
  let readable ← prepareViewBool ops readable
  let writable ← prepareViewBool ops writable
  match readable, writable with
  | .accepted readable, .accepted writable =>
      pure ⟨a, rank, target, source, readable, writable, reshaped⟩
  | _, _ => throw Error.typeError

/-- Mirror every original validation and repeated selected type query in order. Native operands use concrete wrapping arithmetic; arbitrary custom results remain open until their actual Boolean context. Both raw padding results are evaluated before new checks rank and prepares its Bool fields. No static layout flag substitutes for an unfixed Type query.
Source reference: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S, N}}
--         function thrownonint(S::Type, T::Type, dim)
--             @noinline
--             throw(ArgumentError(LazyString(
--                 "cannot reinterpret an `", S, "` array to `", T, "` whose first dimension has size `", dim,
--                 "`. The resulting array would have a non-integral first dimension.")))
--         end
--         function throwaxes1(S::Type, T::Type, ax1)
--             @noinline
--             throw(ArgumentError(LazyString("cannot reinterpret a `", S, "` array to `", T,
--                 "` when the first axis is ", ax1, ". Try reshaping first.")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         (N != 0 || aligned_sizeof(T) == aligned_sizeof(S)) || throwsize0(S, T, "different")
--         if N != 0 && aligned_sizeof(S) != aligned_sizeof(T)
--             ax1 = axes(a)[1]
--             dim = length(ax1)
--             if issingletontype(T)
--                 issingletontype(S) || throwsingleton(S, T)
--             else
--                 rem(dim*aligned_sizeof(S),aligned_sizeof(T)) == 0 || thrownonint(S, T, dim)
--             end
--             first(ax1) == 1 || throwaxes1(S, T, ax1)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, false}(a, readable, writable)
--     end
-- /Source
def reinterpret {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : DynamicConstructorOps m A Axis O)
    (target source : TypeLayout) (rank : Value O) (a : A) : m (View O A) := do
  unless (← requireBool (← ops.types.isBits target)) do
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbits")))
    liftReinterpret (m14_throwbits source target target)
  unless (← requireBool (← ops.types.isBits source)) do
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbits")))
    liftReinterpret (m14_throwbits source target source)
  if ← requireBool (← ops.types.bitPadding target) then
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbitpadding")))
    liftReinterpret (m27_throwbitpadding source target target)
  if ← requireBool (← ops.types.bitPadding source) then
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbitpadding")))
    liftReinterpret (m27_throwbitpadding source target source)
  unless (← scalarNotEqual ops.scalars rank (.native zero)) do
    let targetSize ← ops.types.alignedSize target
    let sourceSize ← ops.types.alignedSize source
    unless (← scalarEqual ops.scalars targetSize sourceSize) do
      unless ops.isType source && ops.isType target do
        throw (Error.array (.julia (.methodError "throwsize0")))
      liftReinterpret (throwSize0 source target "different")
  if ← scalarNotEqual ops.scalars rank (.native zero) then
    let sourceSize ← ops.types.alignedSize source
    let targetSize ← ops.types.alignedSize target
    if ← scalarNotEqual ops.scalars sourceSize targetSize then
      let axes ← ops.arrays.axes a
      let axis ← axesGet ops.arrays axes one
      let dimension ← ops.arrays.length axis
      if ← requireBool (← ops.types.singleton target) then
        unless (← requireBool (← ops.types.singleton source)) do
          unless ops.isType source && ops.isType target do
            throw (Error.array (.julia (.methodError "throwsingleton")))
          liftReinterpret (m23_throwsingleton source target)
      else
        let sourceSize ← ops.types.alignedSize source
        let product ← scalarMultiply ops.scalars dimension sourceSize
        let targetSize ← ops.types.alignedSize target
        let remainder ← scalarRemainder ops.scalars product targetSize
        unless (← scalarEqual ops.scalars remainder (.native zero)) do
          unless ops.isType source && ops.isType target do
            throw (Error.array (.julia (.methodError "thrownonint")))
          liftReinterpret (throwNonIntegral source target dimension)
      let first ← ops.arrays.first axis
      unless (← scalarEqual ops.scalars first (.native one)) do
        unless ops.isType source && ops.isType target do
          throw (Error.array (.julia (.methodError "throwaxes1")))
        liftReinterpret (throwFirstAxis source target axis)
  let readable ← ops.types.subpadding target source
  let writable ← ops.types.subpadding source target
  newDynamicView ops target source a rank readable writable false

/-- Preserve source-then-target query order and every repeated aligned_sizeof call across equality, ordering, remainder, diagnostic and division branches. The dimension query occurs only in its selected branch; native rank arithmetic wraps. The axes query precedes ratio/OneTo/comparison. Raw padding results precede final type application and delayed Bool field validation.
Source reference: base/reinterpretarray.jl:107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}
--         function throwintmult(S::Type, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
--                 aligned_sizeof(T), ") and `Base.elsize(Array{eltype(a)})` (got ", aligned_sizeof(S), ") be an integer multiple of the other")))
--         end
--         function throwsize1(a::AbstractArray, T::Type)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", eltype(a),
--                 " requires that `axes(a, 1)` (got ", axes(a, 1), ") be equal to 1:",
--                 aligned_sizeof(T) ÷ aligned_sizeof(eltype(a)), " (from the ratio of element sizes)")))
--         end
--         function throwfromsingleton(S, T)
--             @noinline
--             throw(ArgumentError(LazyString("`reinterpret(reshape, ", T, ", a)` where `eltype(a)` is ", S,
--                 " requires that ", T, " be a singleton type, since ", S, " is one")))
--         end
--         isbitstype(T) || throwbits(S, T, T)
--         isbitstype(S) || throwbits(S, T, S)
--         has_bit_padding(T) && throwbitpadding(S, T, T)
--         has_bit_padding(S) && throwbitpadding(S, T, S)
--         if aligned_sizeof(S) == aligned_sizeof(T)
--             N = ndims(a)
--         elseif aligned_sizeof(S) > aligned_sizeof(T)
--             issingletontype(T) && throwsingleton(S, T)
--             rem(aligned_sizeof(S), aligned_sizeof(T)) == 0 || throwintmult(S, T)
--             N = ndims(a) + 1
--         else
--             issingletontype(S) && throwfromsingleton(S, T)
--             rem(aligned_sizeof(T), aligned_sizeof(S)) == 0 || throwintmult(S, T)
--             N = ndims(a) - 1
--             N > -1 || throwsize0(S, T, "larger")
--             axes(a, 1) == OneTo(aligned_sizeof(T) ÷ aligned_sizeof(S)) || throwsize1(a, T)
--         end
--         readable = array_subpadding(T, S)
--         writable = array_subpadding(S, T)
--         new{T, N, S, A, true}(a, readable, writable)
--     end
-- /Source
def reinterpretReshape {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : DynamicConstructorOps m A Axis O)
    (target source : TypeLayout) (a : A) : m (View O A) := do
  unless (← requireBool (← ops.types.isBits target)) do
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbits")))
    liftReinterpret (m14_throwbits source target target)
  unless (← requireBool (← ops.types.isBits source)) do
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbits")))
    liftReinterpret (m14_throwbits source target source)
  if ← requireBool (← ops.types.bitPadding target) then
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbitpadding")))
    liftReinterpret (m27_throwbitpadding source target target)
  if ← requireBool (← ops.types.bitPadding source) then
    unless ops.isType source && ops.isType target do
      throw (Error.array (.julia (.methodError "throwbitpadding")))
    liftReinterpret (m27_throwbitpadding source target source)
  let sourceSize ← ops.types.alignedSize source
  let targetSize ← ops.types.alignedSize target
  let equal ← scalarEqual ops.scalars sourceSize targetSize
  let rank ← if equal then ops.arrays.ndims a else do
    let sourceSize ← ops.types.alignedSize source
    let targetSize ← ops.types.alignedSize target
    if ← scalarGreater ops.scalars sourceSize targetSize then
      if ← requireBool (← ops.types.singleton target) then
        unless ops.isType source && ops.isType target do
          throw (Error.array (.julia (.methodError "throwsingleton")))
        liftReinterpret (m23_throwsingleton source target)
      let sourceSize ← ops.types.alignedSize source
      let targetSize ← ops.types.alignedSize target
      let remainder ← scalarRemainder ops.scalars sourceSize targetSize
      unless (← scalarEqual ops.scalars remainder (.native zero)) do
        unless ops.isType source && ops.isType target do
          throw (Error.array (.julia (.methodError "throwintmult")))
        throwIntMultiple ops.types source target
      let dimensions ← ops.arrays.ndims a
      scalarAdd ops.scalars dimensions (.native one)
    else
      if ← requireBool (← ops.types.singleton source) then
        liftReinterpret (throwFromSingleton source target)
      let targetSize ← ops.types.alignedSize target
      let sourceSize ← ops.types.alignedSize source
      let remainder ← scalarRemainder ops.scalars targetSize sourceSize
      unless (← scalarEqual ops.scalars remainder (.native zero)) do
        unless ops.isType source && ops.isType target do
          throw (Error.array (.julia (.methodError "throwintmult")))
        throwIntMultiple ops.types source target
      let dimensions ← ops.arrays.ndims a
      let n ← scalarSubtract ops.scalars dimensions (.native one)
      unless (← scalarGreater ops.scalars n (.native (JInt.lit .i64 (-1)))) do
        unless ops.isType source && ops.isType target do
          throw (Error.array (.julia (.methodError "throwsize0")))
        liftReinterpret (throwSize0 source target "larger")
      let axis ← ops.arrays.axis a one
      let targetSize ← ops.types.alignedSize target
      let sourceSize ← ops.types.alignedSize source
      let ratio ← scalarDivide ops.scalars targetSize sourceSize
      let sameAxis ← match ratio with
        | .native ratio => do
            let expected ← liftResult Error.range
              (JuliaLean.base.range.Models1Group7.oneToStopBits .i64 .i64 ratio)
            requireBool (← ops.arrays.equalOneTo axis expected)
        | .other ratio _ => do
            let expected ← ops.oneToOther ratio
            requireBool (← ops.equalAxisOther axis expected)
      unless sameAxis do
        unless ops.isType target do
          throw (Error.array (.julia (.methodError "throwsize1")))
        throwSize1Dispatched ops.arrays ops.types ops.scalars a target
      pure n
  let readable ← ops.types.subpadding target source
  let writable ← ops.types.subpadding source target
  newDynamicView ops target source a rank readable writable true

/-- The known generic reshape constructor is called directly with no premature parent/axis/size observation. All selected type and array queries remain in the actual constructor body.
Source reference: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
-- /Source
def reinterpretReshapeDefault {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O : Type} (ops : DynamicConstructorOps m A Axis O)
    (target source : TypeLayout) (a : A) : m (View O A) :=
  reinterpretReshape ops target source a

/-- The argument tag records actual constructor-method selection, including user specializations on target type or array type. The generic branch invokes its complete body; any selected user constructor preserves arbitrary result, errors and effects.
Source reference: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T} = ReinterpretArray{T}(reshape, a)
-- /Source
def reinterpretReshapeArray {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Axis O Custom R : Type} (ops : DynamicConstructorOps m A Axis O)
    (dispatch : ReshapeDispatchOps m Custom R) (target source : TypeLayout) :
    ConstructorArgument A Custom → m (Sum (View O A) R)
  | .generic a => return .inl (← reinterpretReshapeDefault ops target source a)
  | .custom a => return .inr (← dispatch.custom target a)

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- The selected strides call may return its documented tuple or a custom indexable object. Keeping the latter also preserves generic getindex behavior for custom array implementations.
Source reference: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
--     k ≤ ndims(A) ? strides(A)[k] : length(A)
-- /Source
inductive StrideContainer (Other Container : Type) where
  | tuple (values : NativeTuple (Value Other))
  | other (value : Container)

/-- A user Integer conversion need not return Int. Core.getfield also accepts Symbol;
all other runtime result types fail its Int-or-Symbol check. Symbol payloads are retained
as opaque runtime objects, without assuming a spelling or symbol encoding.
Source reference: base/tuple.jl:34; src/builtins.c:1173-1194. -/
-- Source: base/tuple.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Integer) = getfield(t, convert(Int, i), @_boundscheck)
-- /Source
inductive TupleFieldArgument (Other : Type) where
  | native (index : I64)
  | symbol (name : Other)
  | other (value : Other)

/-- Open array, comparison, conversion, and custom-indexing calls for stride(A,k). The input k ranges over native Int and other Integer values. Comparison results retain a rejected non-Bool case. Native tuple access uses its installed model; generic conversion retains every result type before the concrete field check.
Source reference: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
--     k ≤ ndims(A) ? strides(A)[k] : length(A)
-- /Source
structure StrideSelectOps (m : Type → Type) (A Other Container : Type) where
  ndims : A → m (Value Other)
  strides : A → m (StrideContainer Other Container)
  length : A → m (Value Other)
  nativeLeOther : I64 → Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  otherLe : Other → Value Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  selectTupleIndex : NativeTuple (Value Other) → Other → Bool
  tupleCustomGet : NativeTuple (Value Other) → Other → m (Value Other)
  convertIndex : Other → m (TupleFieldArgument Other)
  customGet : Container → Value Other → m (Value Other)

/-- The comparison is native for two Int values and otherwise selects an unfixed scalar method. A non-Bool result raises TypeError at the original conditional.
Source reference: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
--     k ≤ ndims(A) ? strides(A)[k] : length(A)
-- /Source
def strideLessEqual {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O C : Type} (ops : StrideSelectOps m A O C)
    (left right : Value O) : m Bool := do
  match left, right with
  | .native x, .native y => pure (decide (x ≤ y))
  | .native x, .other y _ => requireBool (← ops.nativeLeOther x y)
  | .other x _, y => requireBool (← ops.otherLe x y)

/-- Concrete tuple field access after a selected conversion: native Int uses the installed
bounds-checked tuple read; Symbol cannot match any tuple field name and raises FieldError;
every other result type raises TypeError. Tuple types share the empty symbol-name vector
(src/jltypes.c:3797-3799), so Symbol("1") is not a numeric tuple field index.
Source reference: base/tuple.jl:33-34; src/builtins.c:1173-1194;
src/datatype.c:1859-1884; src/rtutils.c:170-173. -/
-- Source: base/tuple.jl:33-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- getindex(@nospecialize(t::Tuple), i::Integer) = getfield(t, convert(Int, i), @_boundscheck)
-- /Source
-- Source: src/builtins.c:1173-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t get_checked_fieldindex(const char *name, jl_datatype_t *st, jl_value_t *v, jl_value_t *arg, int mutabl) JL_CANSAFEPOINT
-- {
--     if (mutabl) {
--         if (st == jl_module_type)
--             jl_error("cannot assign variables in other modules");
--         if (!st->name->mutabl)
--             jl_errorf("%s: immutable struct of type %s cannot be changed", name, jl_symbol_name(st->name->name));
--     }
--     size_t idx;
--     if (jl_is_long(arg)) {
--         idx = jl_unbox_long(arg) - 1;
--         if (idx >= jl_datatype_nfields(st))
--             jl_bounds_error(v, arg);
--     }
--     else if (jl_is_symbol(arg)) {
--         idx = jl_field_index(st, (jl_sym_t*)arg, 1);
--     }
--     else {
--         jl_value_t *ts[2] = {(jl_value_t*)jl_long_type, (jl_value_t*)jl_symbol_type};
--         jl_value_t *t = jl_type_union(ts, 2);
--         jl_type_error(name, t, arg);
--     }
-- /Source
-- Source: src/datatype.c:1859-1884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT int jl_field_index(jl_datatype_t *t, jl_sym_t *fld, int err)
-- {
--     if (jl_is_namedtuple_type(t)) {
--         jl_value_t *ns = jl_tparam0(t);
--         if (jl_is_tuple(ns)) {
--             size_t i, n = jl_nfields(ns);
--             for (i = 0; i < n; i++) {
--                 if (jl_get_nth_field(ns, i) == (jl_value_t*)fld) {
--                     return (int)i;
--                 }
--             }
--         }
--     }
--     else {
--         jl_svec_t *fn = jl_field_names(t);
--         size_t i, n = jl_svec_len(fn);
--         for (i = 0; i < n; i++) {
--             if (jl_svecref(fn, i) == (jl_value_t*)fld) {
--                 return (int)i;
--             }
--         }
--     }
--     if (err)
--         jl_has_no_field_error(t, fld);
--     return -1;
-- }
-- /Source
-- Source: src/rtutils.c:170-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT void JL_NORETURN JL_NO_SAFEPOINT_ANALYSIS jl_has_no_field_error(jl_datatype_t *t, jl_sym_t *var)
-- {
--     jl_throw(jl_new_struct(jl_fielderror_type, t, var));
-- }
-- /Source
-- Source: src/jltypes.c:3797-3799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     jl_anytuple_type = jl_new_datatype(jl_symbol("Tuple"), core, jl_any_type, anytuple_params,
--                                        jl_emptysvec, anytuple_params, jl_emptysvec, 0, 0, 0);
--     jl_tuple_typename = jl_anytuple_type->name;
-- /Source
def tupleFieldRead {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (values : NativeTuple (Value O)) (index : TupleFieldArgument O) : m (Value O) :=
  match index with
  | .native index => liftResult Error.tuple
      (JuliaLean.base.tuple.getindexInt values.values index)
  | .symbol _ => throw (.tuple .fieldError)
  | .other _ => throw Error.typeError

/-- Native tuple indexing uses the installed Int method. A non-native Integer may
select a more-specific tuple indexing method; otherwise its selected convert(Int,k)
result flows into concrete Core.getfield classification, without an invented Int
assertion. Custom indexable containers retain the original k.
Source reference: base/reinterpretarray.jl:208-209; base/tuple.jl:33-34. -/
-- Source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
--     k ≤ ndims(A) ? strides(A)[k] : length(A)
-- /Source
-- Source: base/tuple.jl:33-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- getindex(@nospecialize(t::Tuple), i::Integer) = getfield(t, convert(Int, i), @_boundscheck)
-- /Source
def strideGet {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O C : Type} (ops : StrideSelectOps m A O C)
    (container : StrideContainer O C) (index : Value O) : m (Value O) := do
  match container, index with
  | .other a, k => ops.customGet a k
  | .tuple tuple, .native k =>
      liftResult Error.tuple (JuliaLean.base.tuple.getindexInt tuple.values k)
  | .tuple tuple, .other k _ =>
      if ops.selectTupleIndex tuple k then ops.tupleCustomGet tuple k
      else tupleFieldRead tuple (← ops.convertIndex k)

/-- Preserve the source conditional: ndims and comparison precede either strides/getindex or length. Negative and zero indices reach the real tuple BoundsError; non-native Integer conversion errors and every custom effect remain observable.
Source reference: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer) =
--     k ≤ ndims(A) ? strides(A)[k] : length(A)
-- /Source
def stride {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O C : Type} (ops : StrideSelectOps m A O C)
    (a : A) (k : Value O) : m (Value O) := do
  let rank ← ops.ndims a
  if ← strideLessEqual ops k rank then
    strideGet ops (← ops.strides a) k
  else
    ops.length a

/-- A divrem result may be a concrete tuple of arbitrary arity or a custom object. The latter preserves the source generic getindex(result,2) and first(result) dispatch; the former uses installed tuple operations. Native divrem produces its actual two-element tuple.
Source reference: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
inductive StrideDivision (Other Custom : Type) where
  | tuple (values : NativeTuple (Value Other))
  | other (value : Custom)

/-- Predicate values distinguish Bool, Missing, and any other Julia result. The other case keeps custom ismissing dispatch before the Bool-context TypeError, rather than assuming every user iszero returns Bool.
Source reference: base/reinterpretarray.jl:225-230; base/anyall.jl:245-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
-- Source: base/anyall.jl:245-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
inductive StridePredicate (Other : Type) where
  | boolean (value : Bool)
  | missing
  | other (value : Other)

/-- Only open scalar/result dispatch is parameterized. Concrete native divrem, tuple map, tuple indexing, first, and short-circuit all are implemented separately. All fields preserve caller state and arbitrary exceptions.
Source reference: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
structure CheckedStrideOps (m : Type → Type) (Other Custom PredicateOther : Type) where
  divremOtherLeft : Other → Value Other → m (StrideDivision Other Custom)
  divremNativeOther : I64 → Other → m (StrideDivision Other Custom)
  resultGet : Custom → I64 → m (Value Other)
  resultFirst : Custom → m (Value Other)
  iszeroOther : Other → m (StridePredicate PredicateOther)
  ismissingOther : PredicateOther → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))

/-- Native Int division uses the installed checked divrem and returns its actual quotient/remainder tuple. All other operand-type combinations are open dispatch; neither operand nor result is narrowed to a homogeneous type.
Source reference: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
def checkedStrideDivide {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O C P : Type} (ops : CheckedStrideOps m O C P)
    (value divisor : Value O) : m (StrideDivision O C) := do
  match value, divisor with
  | .native x, .native y =>
      let (q, r) ← liftReinterpret (divremInt x y)
      pure (.tuple ⟨[.native q, .native r], by change (2 : Nat) ≤ 2 ^ 63 - 1; decide⟩)
  | .native x, .other y _ => ops.divremNativeOther x y
  | .other x _, y => ops.divremOtherLeft x y

/-- The source accesses the second result element using native Int index 2. A tuple with insufficient arity throws its real BoundsError; a custom result invokes its own indexing method.
Source reference: base/reinterpretarray.jl:225-230; base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def checkedStrideRemainder {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O C P : Type} (ops : CheckedStrideOps m O C P)
    (result : StrideDivision O C) : m (Value O) :=
  match result with
  | .tuple values => liftResult Error.tuple
      (JuliaLean.base.tuple.getindexInt values.values (JInt.lit .i64 2))
  | .other value => ops.resultGet value (JInt.lit .i64 2)

/-- The final map invokes first only after every remainder passes. Empty tuples use the installed more-specific ArgumentError method; nonempty tuples and custom results use their respective first methods.
Source reference: base/reinterpretarray.jl:225-230; base/tuple.jl:270-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
-- Source: base/tuple.jl:270-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(::Tuple{}) = throw(ArgumentError("tuple must be non-empty"))
-- first(t::Tuple) = t[1]
-- /Source
def checkedStrideFirst {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O C P : Type} (ops : CheckedStrideOps m O C P)
    (result : StrideDivision O C) : m (Value O) :=
  match result with
  | .tuple values =>
      match values.values with
      | [] => liftResult Error.tuple JuliaLean.base.tuple.firstEmpty
      | _ :: _ => liftResult Error.tuple (JuliaLean.base.tuple.firstTuple values.values)
  | .other value => ops.resultFirst value

/-- Native iszero is the concrete Int comparison with zero. Other remainder types retain their selected predicate result, including Missing and non-Bool values.
Source reference: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:225-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _checked_strides(byte_strides::Tuple, els::Integer)
--     drs = map(i -> divrem(i, els), byte_strides)
--     all(i->iszero(i[2]), drs) ||
--         throw(ArgumentError("Parent's strides could not be exactly divided!"))
--     map(first, drs)
-- end
-- /Source
def checkedStrideZero {m : Type → Type} [Monad m]
    {O C P : Type} (ops : CheckedStrideOps m O C P)
    (value : Value O) : m (StridePredicate P) :=
  match value with
  | .native value => pure (.boolean (value == zero))
  | .other value _ => ops.iszeroOther value

/-- The closed short-circuit tuple traversal shared by the source _all tuple loop and _all_tuple recursion. Every remainder indexing and iszero call occurs here, not in a preliminary map. False returns immediately, Missing is remembered, and a non-Bool surviving ismissing raises TypeError at its original Boolean context.
Source reference: base/anyall.jl:204-220; base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/anyall.jl:204-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _all(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v || return false
--             end
--         end
--         return anymissing ? missing : true
--     end
-- end
-- /Source
-- Source: base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This is similar to any(f, ::Tuple) defined above.
-- function all(f, itr::Tuple)
--     if itr isa NTuple || length(itr) > 32
--         return _all(f, itr, :)
--     end
--     _all_tuple(f, false, itr...)
-- end
-- 
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def checkedStrideAll {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O C P : Type} (ops : CheckedStrideOps m O C P)
    (anymissing : Bool) : List (StrideDivision O C) → m (Option Bool)
  | [] => pure (if anymissing then none else some true)
  | result :: rest => do
      let remainder ← checkedStrideRemainder ops result
      let value ← checkedStrideZero ops remainder
      match value with
      | .missing => checkedStrideAll ops true rest
      | .boolean false => pure (some false)
      | .boolean true => checkedStrideAll ops anymissing rest
      | .other value =>
          if ← requireBool (← ops.ismissingOther value) then
            checkedStrideAll ops true rest
          else
            throw Error.typeError

/-- The stored parent type is open, so its selected Bool-form contiguity query is an effectful interface call. The source imposes no Bool assertion on the returned value; Result therefore remains arbitrary.
Source reference: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _checkcontiguous(::Type{Bool}, A::ReinterpretArray) = _checkcontiguous(Bool, parent(A))
-- /Source
structure CheckContiguousOps (m : Type → Type) (A Result : Type) where
  checkBool : A → m Result

/-- Forward exactly the stored parent and the fixed Bool-form query. View metadata and cached permission flags are not inspected, and the arbitrary callee result or exception is returned unchanged.
Source reference: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _checkcontiguous(::Type{Bool}, A::ReinterpretArray) = _checkcontiguous(Bool, parent(A))
-- /Source
def checkContiguous {m : Type → Type} {A R O : Type}
    (ops : CheckContiguousOps m A R) (a : View O A) : m R :=
  ops.checkBool a.parent

/-- A runtime IndexStyle result distinguishes the exact IndexLinear singleton from all other values; arbitrary static parameters and custom styles retain their payloads. The source uses identity, not overloaded equality.
Source reference: base/reinterpretarray.jl:263-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:263-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}} =
--     IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- 
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
-- /Source
inductive RuntimeIndexStyle (Other : Type) where
  | linear
  | cartesian
  | static (parameter : Value Other)
  | other (value : Other)

/-- IndexStyle on the unfixed parent array type is the open call of plain routing. Its effects, errors, and arbitrary result are preserved.
Source reference: base/reinterpretarray.jl:263-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:263-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}} =
--     IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- 
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
-- /Source
structure IndexStyleOps (m : Type → Type) (ParentType Other : Type) where
  parentStyle : ParentType → m (RuntimeIndexStyle Other)

/-- Retain linear indexing exactly for the actual IndexLinear singleton; every other successful parent style becomes ordinary Cartesian. Parent dispatch errors occur before any result is constructed.
Source reference: base/reinterpretarray.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:263-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}} =
--     IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- /Source
def plainIndexStyle {m : Type → Type} [Monad m] {P O : Type}
    (ops : IndexStyleOps m P O) (parentType : P) : m (RuntimeIndexStyle O) := do
  match ← ops.parentStyle parentType with
  | .linear => pure .linear
  | _ => pure .cartesian

/-- The two source arguments are singleton values of the same IndexSCartesian2{K} type. K is a valid runtime type-parameter payload of any accepted kind; it is not restricted to Nat or native Int.
Source reference: base/reinterpretarray.jl:260-260; base/reinterpretarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct IndexSCartesian2{K} <: IndexStyle end   # K = aligned_sizeof(S) ÷ aligned_sizeof(T), a static-sized 2d cartesian iterator
-- /Source
-- Source: base/reinterpretarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
-- /Source
structure StaticStyleToken (Parameter : Type) (parameter : Parameter) where

/-- Retain the full type parameter K beside the installed pair of native Int coordinate fields. K may be any valid Julia type parameter; the source scalar index constructor has no K::Int assertion.
Source reference: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
structure RuntimeStaticIndex (Other : Type) where
  parameter : Value Other
  coordinates : SCartesianIndex2

/-- The scalar index conversion returns the entire original value, including its runtime type parameter K. It performs no field conversion, array query, or allocation that changes observable identity.
Source reference: base/reinterpretarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_index(i::SCartesianIndex2) = i
-- /Source
def toStaticIndex {O : Type} (index : RuntimeStaticIndex O) : RuntimeStaticIndex O :=
  index

/-- Only comparison against a non-native K and field conversion from that K are open. Invalid Boolean results and failed Int-field assertions remain explicit, while native comparisons and all coordinate arithmetic stay concrete.
Source reference: base/reinterpretarray.jl:280-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:280-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
--     i.i < K ? SCartesianIndex2{K}(i.i + 1, i.j) : SCartesianIndex2{K}(1, i.j + 1)
-- prevind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
--     i.i > 1 ? SCartesianIndex2{K}(i.i - 1, i.j) : SCartesianIndex2{K}(K, i.j - 1)
-- /Source
structure StaticIndexOps (m : Type → Type) (Other : Type) where
  intLessOther : I64 → Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  convertInt : Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion I64 (Value Other))

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- Actual dispatch for the zero-argument parameterized style constructor. K is
unfixed in the callers, so a selected specialized constructor can return any value;
the concrete generated constructor remains the default branch.
Source reference: base/reinterpretarray.jl:260,266-273. -/
-- Source: base/reinterpretarray.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct IndexSCartesian2{K} <: IndexStyle end   # K = aligned_sizeof(S) ÷ aligned_sizeof(T), a static-sized 2d cartesian iterator
-- /Source
-- Source: base/reinterpretarray.jl:266-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
-- /Source
structure StaticStyleConstructorOps (m : Type → Type) (Other : Type) where
  selectCustom : Value Other → Bool
  custom : Value Other → m (RuntimeIndexStyle Other)

/-- Type-object metadata calls remain selected on the unfixed T/S types. Scalar operators are native for native operands and otherwise preserve selected dispatch. The singleton style constructor can itself select a specialized method on its full parameterized Type; its result is unrestricted.
Source reference: base/reinterpretarray.jl:266-272. -/
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
structure ReshapedIndexStyleOps (m : Type → Type) (ParentType Other : Type) where
  types : TypeQueryOps m Other
  scalars : ScalarOps m Other
  parentStyle : ParentType → m (RuntimeIndexStyle Other)
  constructors : StaticStyleConstructorOps m Other

/-- Type application checks the actual runtime parameter before any zero-argument constructor is selected. The generated empty struct retains K exactly; a specialized selected constructor keeps its arbitrary result, effects and errors.
Source reference: base/reinterpretarray.jl:266-272. -/
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
def constructRuntimeStyle {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (ops : StaticStyleConstructorOps m O)
    (parameter : Value O) : m (RuntimeIndexStyle O) := do
  checkRuntimeParameter parameter
  if ops.selectCustom parameter then
    ops.custom parameter
  else
    pure (.static parameter)

/-- Observe target size then source size before comparison. Only a shrinking-size result with a linear parent performs the second pair of size queries, now source before target, followed by division and type application. No width is cached across calls. Each parent style is queried exactly once after the size test succeeds.
Source reference: base/reinterpretarray.jl:266-272. -/
-- Source: base/reinterpretarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}
--     if aligned_sizeof(T) < aligned_sizeof(S)
--         IndexStyle(A) === IndexLinear() && return IndexSCartesian2{aligned_sizeof(S) ÷ aligned_sizeof(T)}()
--         return IndexCartesian()
--     end
--     return IndexStyle(A) === IndexLinear() ? IndexLinear() : IndexCartesian()
-- end
-- /Source
def reshapedIndexStyle {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {P O : Type} (ops : ReshapedIndexStyleOps m P O) (parentType : P)
    (target source : TypeLayout) : m (RuntimeIndexStyle O) := do
  let targetSize ← ops.types.alignedSize target
  let sourceSize ← ops.types.alignedSize source
  if ← scalarLess ops.scalars targetSize sourceSize then
    match ← ops.parentStyle parentType with
    | .linear =>
        let sourceSize ← ops.types.alignedSize source
        let targetSize ← ops.types.alignedSize target
        let ratio ← scalarDivide ops.scalars sourceSize targetSize
        constructRuntimeStyle ops.constructors ratio
    | _ => pure .cartesian
  else
    match ← ops.parentStyle parentType with
    | .linear => pure .linear
    | _ => pure .cartesian

/-- Both input style singletons carry exactly the same K. The output constructor
is still dispatched on that parameterized Type, so selected specialized constructor
results and effects are preserved rather than forced back into the generated singleton.
Source reference: base/reinterpretarray.jl:273. -/
-- Source: base/reinterpretarray.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K} = IndexSCartesian2{K}()
-- /Source
def combineStaticStyle {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (ops : StaticStyleConstructorOps m O) {k : Value O}
    (_left _right : StaticStyleToken (Value O) k) : m (RuntimeIndexStyle O) :=
  constructRuntimeStyle ops k

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- The static iterator retains its actual range handle and complete runtime type parameter. The generated two-parameter constructor can create values without the outer K::Int assertion; only the explicit outer constructor below imposes that check. Range is the existing AbstractUnitRange{Int} runtime carrier, including custom subtypes.
Source reference: base/reinterpretarray.jl:285-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:285-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndices2{K,R<:AbstractUnitRange{Int}} <: AbstractMatrix{SCartesianIndex2{K}}
--     indices2::R
-- end
-- SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
-- /Source
structure RuntimeStaticIndices (Other Range : Type) where
  parameter : Value Other
  indices2 : Range

/-- The outer constructor calls SCartesianIndices2{K,R} with R=typeof(range). An R- or K-specific selected constructor can return any runtime result even though the argument is an AbstractUnitRange{Int}; actual method-selection metadata distinguishes it from generated field storage.
Source reference: base/reinterpretarray.jl:285-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:285-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndices2{K,R<:AbstractUnitRange{Int}} <: AbstractMatrix{SCartesianIndex2{K}}
--     indices2::R
-- end
-- SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
-- /Source
structure StaticRangeConstructorOps (m : Type → Type) (O R Out : Type) where
  selectCustom : Value O → R → Bool
  custom : Value O → R → m (Sum (RuntimeStaticIndices O R) Out)

/-- First perform the source native-Int type assertion, then its greater-than-one assertion, then call the actual selected two-parameter constructor. Generated storage preserves the exact range object; a selected K/R-specific constructor retains every arbitrary result and effect. Negative native counts are AssertionError; every non-native count is TypeError, even if numerically greater than one.
Source reference: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
-- /Source
def staticIndicesConstructor {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O R Out : Type} (ops : StaticRangeConstructorOps m O R Out)
    (parameter : Value O) (range : R) : m (Sum (RuntimeStaticIndices O R) Out) := do
  match parameter with
  | .native k =>
      if k.val > 1 then
        if ops.selectCustom parameter range then ops.custom parameter range
        else pure (.inl ⟨parameter, range⟩)
      else throw (.reinterpret .assertion)
  | .other _ _ => throw Error.typeError

/-- A selected constructor call distinguishes its known AbstractUnitRange{Int} outer method from a genuinely selected custom or missing-method dispatch, including K-specific constructors on an AbstractUnitRange{Int} result. The classification is runtime dispatch information, not a correctness assumption about eachindex.
Source reference: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
-- /Source
inductive StaticRangeArgument (Range Custom : Type) where
  | known (range : Range)
  | custom (value : Custom)

/-- The parent eachindex target is selected on an unfixed parent type. A custom constructor branch is likewise a selected user method; the known branch calls staticIndicesConstructor directly.
Source reference: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
-- /Source
structure StaticEachOps (m : Type → Type) (A R C Out O : Type) where
  constructors : StaticRangeConstructorOps m O R Out
  eachindex : RuntimeIndexStyle O → A → m (StaticRangeArgument R C)
  customConstructor : Value O → C → m Out

/-- Call parent eachindex with IndexLinear before attempting any K assertion. The known constructor retains the original range; selected custom constructors retain their arbitrary result, errors and effects.
Source reference: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
-- /Source
def staticEachindexReshaped {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A R C Out O : Type} (ops : StaticEachOps m A R C Out O)
    (parameter : Value O) (view : View O A) :
    m (Sum (RuntimeStaticIndices O R) Out) := do
  let result ← ops.eachindex .linear view.parent
  match result with
  | .known range => staticIndicesConstructor ops.constructors parameter range
  | .custom value => return .inr (← ops.customConstructor parameter value)

/-- Actual outer diagnostic and recursive join methods may specialize on an unfixed axis type. The fixed axes label is still passed explicitly. Pure selection metadata distinguishes these genuine user methods from the concrete default helper and lazy construction; no callback replaces default recursion.
Source reference: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
structure StaticMismatchOps (m : Type → Type) (A O : Type) where
  selectMismatch : String → A → List A → Bool
  customMismatch : String → A → List A → m (Value O)
  selectJoin : A → List A → Bool
  customJoin : A → List A → m (Value O)

/-- The actual lazy join retains default captured axis objects and arbitrary selected join returns without showing or converting them. Nested default wrappers preserve their original leading axis and exact inner payload.
Source reference: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
inductive StaticJoinedDiagnostic (A O : Type) where
  | pair (first second : A)
  | more (first : A) (rest : StaticJoinedDiagnostic A O)
  | custom (value : Value O)

/-- Perform actual join selection at every recursive arity. A selected method retains its arbitrary result/errors/effects, including the one-argument case. Default two-argument construction captures both objects; larger defaults evaluate the inner join first; a one-argument default is the real MethodError.
Source reference: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- /Source
def captureStaticAxesDispatched {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O : Type} (ops : StaticMismatchOps m A O) (first : A)
    (others : List A) : m (StaticJoinedDiagnostic A O) := do
  if ops.selectJoin first others then
    return .custom (← ops.customJoin first others)
  else
    match others with
    | [] => throw (.array (.julia (.methodError "_join_comma_and")))
    | [second] => pure (.pair first second)
    | second :: third :: rest =>
        let captured ← captureStaticAxesDispatched ops second (third :: rest)
        pure (.more first captured)
termination_by others.length

/-- The actual default mismatch method performs the full dispatched join before fixed lazy message construction and DimensionMismatch. Every custom join exception/state effect is retained. Successful selected join values remain captured without rendering; this default outer body never returns normally.
Source reference: base/abstractarray.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
def throwStaticEachMismatch {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O Out : Type} (ops : StaticMismatchOps m A O)
    (first : A) (others : List A) : m Out := do
  let _message ← captureStaticAxesDispatched ops first others
  throw (.array (.dimensionMismatch "all inputs to eachindex must have the same axes"))

/-- The actual outer mismatch-helper selection occurs after every axis query. Selected custom code receives the literal axes label and complete original argument tuple, and may return successfully; the caller ignores that value. Default selection calls the concrete complete mismatch body.
Source reference: base/reinterpretarray.jl:291-296; base/abstractarray.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
-- Source: base/abstractarray.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
def staticMismatchCall {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O : Type} (ops : StaticMismatchOps m A O)
    (first : A) (others : List A) : m Unit := do
  if ops.selectMismatch "axes" first others then
    let _ ← ops.customMismatch "axes" first others
    pure ()
  else throwStaticEachMismatch ops first others

/-- Each array and iterator result may carry its own selected Julia runtime type. The known unary equality method creates its concrete Fix2 closure. A genuinely selected unary == method may instead return an arbitrary callable; its subsequent all call remains selected on that unfixed function type. A more-specific all method for a Fix2 carrying user-defined types is selected separately; its default remains concrete tuple recursion. Callback tuple lists are only the bounded mapped varargs from this public input, never arbitrary unbounded input lists. Known Fix2 invocation has argument order other == iter. Axes diagnostics and non-Bool/missing equality results retain their own effects and Boolean-context errors.
Source reference: base/reinterpretarray.jl:291-296; base/operators.jl:1262-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
-- Source: base/operators.jl:1262-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ==(x)
-- 
-- Create a function that compares its argument to `x` using [`==`](@ref), i.e.
-- a function equivalent to `y -> y == x`.
-- 
-- The returned function is of type `Base.Fix2{typeof(==)}`, which can be
-- used to implement specialized methods.
-- """
-- ==(x) = Fix2(==, x)
-- /Source
structure StaticManyOps (m : Type → Type) (A Iter Ax Pred O F : Type) where
  eachindex : RuntimeIndexStyle O → A → m Iter
  selectEqualityClosure : Iter → Bool
  equalityClosure : Iter → m F
  allCustom : F → List Iter → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  selectAllCustom : Iter → List Iter → Bool
  customAllFixed : Iter → List Iter → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  equal : Iter → Iter → m (StridePredicate Pred)
  ismissingOther : Pred → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  axes : A → m Ax
  mismatch : StaticMismatchOps m Ax O

/-- Concrete short-circuit tuple all for the equality predicate. All eachindex results already exist before this traversal starts. False stops immediately, missing is remembered, and a non-Bool surviving ismissing raises TypeError at its original condition.
Source reference: base/anyall.jl:204-220; base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/anyall.jl:204-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _all(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v || return false
--             end
--         end
--         return anymissing ? missing : true
--     end
-- end
-- /Source
-- Source: base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This is similar to any(f, ::Tuple) defined above.
-- function all(f, itr::Tuple)
--     if itr isa NTuple || length(itr) > 32
--         return _all(f, itr, :)
--     end
--     _all_tuple(f, false, itr...)
-- end
-- 
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def staticEachAll {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A Iter Ax Pred O F : Type} (ops : StaticManyOps m A Iter Ax Pred O F)
    (iter : Iter) (anymissing : Bool) : List Iter → m (Option Bool)
  | [] => pure (if anymissing then none else some true)
  | other :: rest => do
      match ← ops.equal other iter with
      | .boolean false => pure (some false)
      | .boolean true => staticEachAll ops iter anymissing rest
      | .missing => staticEachAll ops iter true rest
      | .other value =>
          if ← requireBool (← ops.ismissingOther value) then
            staticEachAll ops iter true rest
          else throw Error.typeError

/-- A constructor can return an index of any runtime K, or a completely different Julia value when a more-specific user method is selected. The tag records the actual result runtime shape, not a promise that constructors return their named type.
Source reference: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
inductive StaticIndexResult (Other : Type) where
  | index (value : RuntimeStaticIndex Other)
  | other (value : Value Other)

/-- Constructor dispatch metadata distinguishes the generated Base conversion method from a more-specific selected user method on K or coordinate argument types. selectCustom is pure runtime method-selection data. After generated-method selection, Int/Int field construction remains concrete and skips all conversion calls.
Source reference: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
structure StaticConstructorOps (m : Type → Type) (Other : Type) where
  coordinates : StaticIndexOps m Other
  selectCustom : Value Other → Value Other → Value Other → Bool
  custom : Value Other → Value Other → Value Other → m (StaticIndexResult Other)

/-- Only operations on the unfixed range subtype are parameters. Length and endpoint results retain arbitrary runtime values; the constructor preserves generated conversion or selected more-specific user dispatch.
Source reference: base/reinterpretarray.jl:298-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:298-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- 
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
structure StaticRangeOps (m : Type → Type) (Range Other : Type) where
  constructors : StaticConstructorOps m Other
  length : Range → m (Value Other)
  first : Range → m (Value Other)
  last : Range → m (Value Other)

/-- Known Int-field construction: a native Int needs no conversion; other values call selected convert(Int, value). The raw return-type tag is retained without asserting until all field conversion expressions have completed.
Source reference: base/reinterpretarray.jl:275-278; base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
-- Source: base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         end
--     end
-- 
--     # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
--     # Build lambda body using Core.Argument references
--     nstmts = ((n - nany) + (n - nany)) + 1
--     body_args = Array{Any,1}(Core.undef, nstmts)
--     new_args = Array{Any,1}(Core.undef, n)
--     i = 1
--     bidx = 1
--     while i !== n + 1
--         ft = fts[i]
--         if ft === Any
--             @inbounds new_args[i] = Core.Argument(i + 1)
--         else
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
--     lambda = Expr(:lambda, argnames,
-- /Source
def staticCoordinate {m : Type → Type} [Monad m]
    {O : Type} (ops : StaticIndexOps m O) (value : Value O) :
    m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion I64 (Value O)) :=
  match value with
  | .native n => pure (.accepted n)
  | .other value _ => ops.convertInt value

/-- The generated scalar-index constructor converts i before j, then validates both result types at new, retaining exact K. Even a wrong first conversion result permits the second conversion to run; a first conversion exception still stops immediately. Source default constructor generation is shown explicitly.
Source reference: base/reinterpretarray.jl:275-278; base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
-- Source: base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         end
--     end
-- 
--     # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
--     # Build lambda body using Core.Argument references
--     nstmts = ((n - nany) + (n - nany)) + 1
--     body_args = Array{Any,1}(Core.undef, nstmts)
--     new_args = Array{Any,1}(Core.undef, n)
--     i = 1
--     bidx = 1
--     while i !== n + 1
--         ft = fts[i]
--         if ft === Any
--             @inbounds new_args[i] = Core.Argument(i + 1)
--         else
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
--     lambda = Expr(:lambda, argnames,
-- /Source
def constructStaticIndex {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (ops : StaticIndexOps m O) (parameter i j : Value O) :
    m (RuntimeStaticIndex O) := do
  let first ← staticCoordinate ops i
  let second ← staticCoordinate ops j
  match first, second with
  | .accepted i, .accepted j => pure ⟨parameter, ⟨i, j⟩⟩
  | _, _ => throw Error.typeError

/-- Actual constructor selection includes K-specific methods even when both coordinates are native Int. A selected user method retains arbitrary result/errors/effects. Otherwise the generated constructor stays concrete, skips conversion for native fields, and evaluates both conversions before new validates their result types. No callee correctness law is assumed.
Source reference: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
def callStaticIndexConstructor {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (ops : StaticConstructorOps m O) (parameter i j : Value O) :
    m (StaticIndexResult O) := do
  if ops.selectCustom parameter i j then
    ops.custom parameter i j
  else
    return .index (← constructStaticIndex ops.coordinates parameter i j)

/-- Return K without a native conversion, then evaluate the actual custom range length. The two-element output tuple preserves each component runtime type.
Source reference: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
-- /Source
def staticIndicesSize {m : Type → Type} [Monad m] {R O : Type}
    (ops : StaticRangeOps m R O) (iter : RuntimeStaticIndices O R) :
    m (Value O × Value O) := do
  let length ← ops.length iter.indices2
  pure (iter.parameter, length)

/-- Only non-native K leaves OneTo dispatch open; the native branch calls the installed checked Base constructor. The custom result carrier is unrestricted.
Source reference: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
structure StaticAxesOps (m : Type → Type) (Other Axis : Type) where
  oneToOther : Other → m Axis

/-- Construct the first axis using the known native OneTo model or the selected non-native dispatch. The original second-axis object is returned unchanged, including its identity and custom runtime type.
Source reference: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
def staticIndicesAxes {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticAxesOps m O Ax) (iter : RuntimeStaticIndices O R) :
    m (Sum (JuliaLean.base.range.OneTo I64) Ax × R) := do
  let first ← match iter.parameter with
    | .native k => do
        let axis ← liftResult Error.range
          (JuliaLean.base.range.Models1Group7.oneToStopBits .i64 .i64 k)
        pure (.inl axis)
    | .other k _ => do pure (.inr (← ops.oneToOther k))
  pure (first, iter.indices2)

/-- Observe first(range) before constructing the index. Generated construction converts its result to the native j field and preserves K; a more-specific constructor may instead return any runtime value.
Source reference: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- /Source
def staticIndicesFirst {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O : Type} (ops : StaticRangeOps m R O) (iter : RuntimeStaticIndices O R) :
    m (StaticIndexResult O) := do
  let outer ← ops.first iter.indices2
  callStaticIndexConstructor ops.constructors iter.parameter (.native one) outer

/-- Observe last(range) before constructor selection or either generated field conversion. More-specific constructors receive the original K and endpoint and retain arbitrary output; a failing generated K conversion follows the endpoint effects.
Source reference: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def staticIndicesLast {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O : Type} (ops : StaticRangeOps m R O) (iter : RuntimeStaticIndices O R) :
    m (StaticIndexResult O) := do
  let outer ← ops.last iter.indices2
  callStaticIndexConstructor ops.constructors iter.parameter iter.parameter outer

/-- Actual axes results retain arbitrary tuple arity and non-tuple results. Native OneTo axes remain tagged for closed checkindex/length; original ranges and custom axis values retain selected operations.
Source reference: base/reinterpretarray.jl:299-299; base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
-- Source: base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- 
-- # Linear indexing is explicitly allowed when there is only one (non-cartesian) index;
-- # indices that do not allow linear indexing (e.g., logical arrays, cartesian indices, etc)
-- # must add specialized methods to implement their restrictions
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- """
--     checkbounds(A, I...)
-- 
-- Throw an error if the specified indices `I` are not in bounds for the given array `A`.
-- """
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- `IA`. This function recursively consumes elements of these tuples,
-- usually in a 1-for-1 fashion,
-- 
--     checkbounds_indices(Bool, (IA1, IA...), (I1, I...)) = checkindex(Bool, IA1, I1) &
--                                                           checkbounds_indices(Bool, IA, I)
-- 
-- Note that [`checkindex`](@ref) is being used to perform the actual
-- bounds-check for a single dimension of the array.
-- 
-- There are two important exceptions to the 1-1 rule: linear indexing and
-- CartesianIndex{N}, both of which may "consume" more than one element
-- of `IA`.
-- 
-- See also [`checkbounds`](@ref).
-- """
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
inductive StaticBoundsAxis (R Ax : Type) where
  | native (range : JuliaLean.base.range.OneTo I64)
  | range (value : R)
  | custom (value : Ax)

/-- Selected axes overrides preserve any native-sized tuple or arbitrary non-tuple result, with no assumed two-axis invariant.
Source reference: base/reinterpretarray.jl:299-299; base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
-- Source: base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- 
-- # Linear indexing is explicitly allowed when there is only one (non-cartesian) index;
-- # indices that do not allow linear indexing (e.g., logical arrays, cartesian indices, etc)
-- # must add specialized methods to implement their restrictions
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- """
--     checkbounds(A, I...)
-- 
-- Throw an error if the specified indices `I` are not in bounds for the given array `A`.
-- """
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- `IA`. This function recursively consumes elements of these tuples,
-- usually in a 1-for-1 fashion,
-- 
--     checkbounds_indices(Bool, (IA1, IA...), (I1, I...)) = checkindex(Bool, IA1, I1) &
--                                                           checkbounds_indices(Bool, IA, I)
-- 
-- Note that [`checkindex`](@ref) is being used to perform the actual
-- bounds-check for a single dimension of the array.
-- 
-- There are two important exceptions to the 1-1 rule: linear indexing and
-- CartesianIndex{N}, both of which may "consume" more than one element
-- of `IA`.
-- 
-- See also [`checkbounds`](@ref).
-- """
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
inductive StaticBoundsAxes (R O Ax : Type) where
  | tuple (values : NativeTuple (StaticBoundsAxis R Ax))
  | other (value : O)

/-- Actual selected K/R-dependent methods are separate at checkbounds, Bool checkbounds, axes and failed-bounds dispatch. Tuple checkbounds_indices uses explicit recursion unless a genuine specialized method is selected at that call. Callback lists are bounded source tuples or their tails, never unbounded public inputs.
Source reference: base/reinterpretarray.jl:304-307; base/abstractarray.jl:682-728; base/essentials.jl:18-19; base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
-- Source: base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- 
-- # Linear indexing is explicitly allowed when there is only one (non-cartesian) index;
-- # indices that do not allow linear indexing (e.g., logical arrays, cartesian indices, etc)
-- # must add specialized methods to implement their restrictions
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- """
--     checkbounds(A, I...)
-- 
-- Throw an error if the specified indices `I` are not in bounds for the given array `A`.
-- """
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- `IA`. This function recursively consumes elements of these tuples,
-- usually in a 1-for-1 fashion,
-- 
--     checkbounds_indices(Bool, (IA1, IA...), (I1, I...)) = checkindex(Bool, IA1, I1) &
--                                                           checkbounds_indices(Bool, IA, I)
-- 
-- Note that [`checkindex`](@ref) is being used to perform the actual
-- bounds-check for a single dimension of the array.
-- 
-- There are two important exceptions to the 1-1 rule: linear indexing and
-- CartesianIndex{N}, both of which may "consume" more than one element
-- of `IA`.
-- 
-- See also [`checkbounds`](@ref).
-- """
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/essentials.jl:18-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
-- _throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
-- /Source
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
structure StaticGetOps (m : Type → Type) (R O Ax : Type) where
  axes : StaticAxesOps m O Ax
  constructors : StaticConstructorOps m O
  selectCheckbounds : RuntimeStaticIndices O R → I64 → I64 → Bool
  customCheckbounds : RuntimeStaticIndices O R → I64 → I64 → m (Value O)
  selectCheckboundsBool : RuntimeStaticIndices O R → I64 → I64 → Bool
  customCheckboundsBool : RuntimeStaticIndices O R → I64 → I64 → m (StridePredicate (Value O))
  selectAxes : RuntimeStaticIndices O R → Bool
  customAxes : RuntimeStaticIndices O R → m (StaticBoundsAxes R O Ax)
  selectTupleIndices : List (StaticBoundsAxis R Ax) → List I64 → Bool
  customTupleIndices : List (StaticBoundsAxis R Ax) → List I64 → m (StridePredicate (Value O))
  selectOtherIndices : O → List I64 → Bool
  customOtherIndices : O → List I64 → m (StridePredicate (Value O))
  selectThrowBounds : RuntimeStaticIndices O R → I64 → I64 → Bool
  customThrowBounds : RuntimeStaticIndices O R → I64 → I64 → m (Value O)
  checkCustomFirst : Ax → I64 → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  checkRange : R → I64 → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  lengthCustom : Ax → m (Value O)
  lengthRange : R → m (Value O)
  equalLengthOne : O → I64 → m (StridePredicate (Value O))
  ismissingOther : O → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  getRange : R → I64 → m (Value O)

/-- The explicit checkindex Bool assertion is preserved. Native OneTo uses the installed checker; other axis types retain selected operations.
Source reference: base/abstractarray.jl:722-728; base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- /Source
def staticBoundsCheckAxis {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (axis : StaticBoundsAxis R Ax) (index : I64) : m Bool := do
  match axis with
  | .native range => pure (JuliaLean.base.abstractarray.checkindexOneTo range.stop index)
  | .range range => requireBool (← ops.checkRange range index)
  | .custom custom => requireBool (← ops.checkCustomFirst custom index)

/-- The trailing-axis predicate evaluates actual length before equality. Native OneTo length and native Int conversion use installed models; non-native lengths and equality retain selected dispatch.
Source reference: base/abstractarray.jl:728-728; base/range.jl:860-860; base/boot.jl:1104-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/range.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     length(r::OneTo{<:smallints}) = Int(r.stop)
-- /Source
-- Source: base/boot.jl:1104-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt64(x::Int8)      = sext_int(Int64, x)
-- toInt64(x::Int16)     = sext_int(Int64, x)
-- toInt64(x::Int32)     = sext_int(Int64, x)
-- toInt64(x::Int64)     = x
-- toInt64(x::Int128)    = checked_trunc_sint(Int64, x)
-- toInt64(x::UInt8)     = zext_int(Int64, x)
-- toInt64(x::UInt16)    = zext_int(Int64, x)
-- toInt64(x::UInt32)    = zext_int(Int64, x)
-- toInt64(x::UInt64)    = bitcast(Int64, check_sign_bit(Int64, x))
-- toInt64(x::UInt128)   = checked_trunc_sint(Int64, check_sign_bit(Int64, x))
-- toInt64(x::Bool)      = zext_int(Int64, x)
-- /Source
def staticBoundsSingleton {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (axis : StaticBoundsAxis R Ax) : m (StridePredicate (Value O)) := do
  let length ← match axis with
    | .native range => do
        letI : JuliaLean.base.range.JCtor I64 I64 := ⟨fun x =>
          (JuliaLean.BootCov.IntConv.toInt64 (.int .i64 x)).mapError
            (fun _ => JuliaLean.base.range.Exc.jl (.inexactError "Int64"))⟩
        return .native (← liftResult Error.range
          (JuliaLean.base.range.length_OneTo_smallints range))
    | .range range => ops.lengthRange range
    | .custom custom => ops.lengthCustom custom
  match length with
  | .native native => pure (.boolean (decide (native = one)))
  | .other other _ => ops.equalLengthOne other one

/-- Concrete all over trailing tuple axes short-circuits false and remembers missing. Non-Bool values undergo actual ismissing dispatch; a concrete Int cannot be missing and fails its Bool context. Recursion is explicit.
Source reference: base/abstractarray.jl:728-728; base/anyall.jl:204-220; base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/anyall.jl:204-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _all(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v || return false
--             end
--         end
--         return anymissing ? missing : true
--     end
-- end
-- /Source
-- Source: base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This is similar to any(f, ::Tuple) defined above.
-- function all(f, itr::Tuple)
--     if itr isa NTuple || length(itr) > 32
--         return _all(f, itr, :)
--     end
--     _all_tuple(f, false, itr...)
-- end
-- 
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def staticBoundsTrailingAll {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (anymissing : Bool) : List (StaticBoundsAxis R Ax) → m (StridePredicate (Value O))
  | [] => pure (if anymissing then .missing else .boolean true)
  | axis :: rest => do
      match ← staticBoundsSingleton ops axis with
      | .boolean false => pure (.boolean false)
      | .boolean true => staticBoundsTrailingAll ops anymissing rest
      | .missing => staticBoundsTrailingAll ops true rest
      | .other (.native _) => throw Error.typeError
      | .other (.other other _) =>
          if ← requireBool (← ops.ismissingOther other) then
            staticBoundsTrailingAll ops true rest
          else throw Error.typeError

/-- Each recursive tuple dispatch stays selectable. The default calls installed tuple get with eagerly constructed OneTo(1), asserts the selected checkindex result, and recurses only after true. Concrete tuple tails retain their structural native bound. No callback replaces the recursion.
Source reference: base/abstractarray.jl:722-728; base/tuple.jl:40-40; base/tuple.jl:323-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/tuple.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- get(t::Tuple, i::Integer, default) = i in 1:length(t) ? getindex(t, i) : default
-- /Source
-- Source: base/tuple.jl:323-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- safe_tail(t::Tuple) = tail(t)
-- safe_tail(t::Tuple{}) = ()
-- /Source
def staticBoundsTuple {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (axes : List (StaticBoundsAxis R Ax)) (indices : List I64) :
    m (StridePredicate (Value O)) := do
  if ops.selectTupleIndices axes indices then
    ops.customTupleIndices axes indices
  else
    match indices with
    | [] => staticBoundsTrailingAll ops false axes
    | index :: rest => do
        let defaultAxis ← liftResult Error.range
          (JuliaLean.base.range.Models1Group7.oneToStopBits .i64 .i64 one)
        let axis ← liftResult Error.tuple
          (JuliaLean.base.tuple.getDefault axes (.integer .i64 one) (.native defaultAxis))
        if ← staticBoundsCheckAxis ops axis index then
          staticBoundsTuple ops axes.tail rest
        else pure (.boolean false)
termination_by indices.length

/-- Axes selection occurs only inside default Bool checkbounds. The default calls the full existing axes model and retains its exact two components; selected overrides preserve arbitrary tuple/non-tuple results.
Source reference: base/reinterpretarray.jl:299-299; base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
-- Source: base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- /Source
def staticBoundsAxes {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (iter : RuntimeStaticIndices O R) : m (StaticBoundsAxes R O Ax) := do
  if ops.selectAxes iter then ops.customAxes iter
  else
    let axes ← staticIndicesAxes ops.axes iter
    let first := match axes.1 with
      | .inl native => StaticBoundsAxis.native native
      | .inr custom => StaticBoundsAxis.custom custom
    pure (.tuple ⟨[first, .range axes.2], by change 2 ≤ 2 ^ 63 - 1; decide⟩)

/-- Bool checkbounds preserves selected overrides. Its default evaluates axes then concrete tuple recursion or actual non-tuple dispatch; a missing non-tuple method raises MethodError. Raw Bool/missing/other values reach the outer Boolean context unchanged.
Source reference: base/abstractarray.jl:682-685; base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:682-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- /Source
-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
def staticIndicesCheckboundsBool {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (iter : RuntimeStaticIndices O R) (i j : I64) : m (StridePredicate (Value O)) := do
  if ops.selectCheckboundsBool iter i j then ops.customCheckboundsBool iter i j
  else
    match ← staticBoundsAxes ops iter with
    | .tuple axes => staticBoundsTuple ops axes.values [i, j]
    | .other other =>
        if ops.selectOtherIndices other [i, j] then ops.customOtherIndices other [i, j]
        else throw (Error.array (.julia (.methodError "checkbounds_indices")))

/-- The checkbounds call respects actual K/R-dependent selection. Its default consumes the full Bool-check result and preserves selected failed-bounds helpers, including a successful return. The closed default failing branch uses installed checkboundsGeneric and raises BoundsError. The caller ignores arbitrary successful custom return values.
Source reference: base/essentials.jl:18-19; base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:18-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
-- _throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
-- /Source
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
def staticIndicesCheckbounds {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (iter : RuntimeStaticIndices O R) (i j : I64) : m Unit := do
  if ops.selectCheckbounds iter i j then
    let _ ← ops.customCheckbounds iter i j
    pure ()
  else
    let valid ← match ← staticIndicesCheckboundsBool ops iter i j with
      | .boolean valid => pure valid
      | _ => throw Error.typeError
    if !valid && ops.selectThrowBounds iter i j then
      let _ ← ops.customThrowBounds iter i j
      pure ()
    else
      liftResult (fun (_ : JuliaLean.BootCov.Exc) => Error.array (.julia .boundsError))
        (JuliaLean.base.essentials.checkboundsGeneric (fun _ _ => valid)
          (fun _ _ => .error .bounds) iter [i, j])

/-- When bounds checking is enabled, complete actual checkbounds selection before lookup. Default bounds remain explicit with arbitrary custom axes; the range result then enters actual scalar-index constructor selection. The flag is source execution mode, not a domain precondition.
Source reference: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
def staticIndicesGet {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O Ax : Type} (ops : StaticGetOps m R O Ax)
    (boundscheck : Bool) (iter : RuntimeStaticIndices O R) (i j : I64) :
    m (StaticIndexResult O) := do
  if boundscheck then staticIndicesCheckbounds ops iter i j
  let outer ← ops.getRange iter.indices2 j
  callStaticIndexConstructor ops.constructors iter.parameter (.native i) outer

/-- Iteration replies distinguish the exact nothing singleton, concrete tuple results of any native-representable arity, and genuinely custom objects whose destructuring dispatch remains open.
Source reference: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
inductive StaticIterationReply (Other Custom : Type) where
  | nothing
  | tuple (values : NativeTuple (Value Other))
  | custom (value : Custom)

/-- A supplied state may itself be any destructurable object; tuple states keep their actual components without native narrowing. The generic branch retains custom indexed_iterate effects at function entry.
Source reference: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
inductive StaticStateArgument (Other Custom : Type) where
  | tuple (values : NativeTuple (Value Other))
  | custom (value : Custom)

/-- The returned state is a concrete three-tuple. It retains pre-conversion item values: conversion into scalar-index Int fields does not rewrite the state tuple components.
Source reference: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
structure StaticIterationState (Other : Type) where
  state1 : Value Other
  item2 : Value Other
  state2 : Value Other

/-- Fault classes from ordinary numeric Core.getfield observation. These are local runtime faults, not callbacks: missing numeric fields are BoundsError, undefined existing references are UndefRefError, and invalid object/index-kind access is TypeError. No memory-ordering failure is invented.
Source reference: base/docs/basedocs.jl:2609-2620; base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/docs/basedocs.jl:2609-2620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     getfield(value, name::Symbol, [order::Symbol], [boundscheck::Bool=true])
--     getfield(value, i::Int, [order::Symbol], [boundscheck::Bool=true])
-- 
-- Extract a field from a composite `value` by name or position.
-- 
-- Optionally, an ordering can be defined for the operation.
-- If the field was declared `@atomic`, the specification is strongly recommended to be
-- compatible with the stores to that location.
-- Otherwise, if not declared as `@atomic`, this parameter must be `:not_atomic` if specified.
-- 
-- The bounds check may be disabled, in which case the behavior of this function is
-- undefined if `i` is out of bounds.
-- /Source
-- Source: base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UndefRefError       <: Exception
--     UndefRefError() = new()
-- end
-- /Source
inductive StaticFieldFault where
  | bounds
  | undefinedField
  | invalidType
  deriving Repr, DecidableEq

/-- Runtime layout metadata for a single checked numeric field observation, including tuples and non-tuple composite objects. Extra fields are irrelevant. Present payloads are arbitrary; no selected function is required to return a valid two-field object.
Source reference: base/docs/basedocs.jl:2609-2620; base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/docs/basedocs.jl:2609-2620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     getfield(value, name::Symbol, [order::Symbol], [boundscheck::Bool=true])
--     getfield(value, i::Int, [order::Symbol], [boundscheck::Bool=true])
-- 
-- Extract a field from a composite `value` by name or position.
-- 
-- Optionally, an ordering can be defined for the operation.
-- If the field was declared `@atomic`, the specification is strongly recommended to be
-- compatible with the stores to that location.
-- Otherwise, if not declared as `@atomic`, this parameter must be `:not_atomic` if specified.
-- 
-- The bounds check may be disabled, in which case the behavior of this function is
-- undefined if `i` is out of bounds.
-- /Source
-- Source: base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UndefRefError       <: Exception
--     UndefRefError() = new()
-- end
-- /Source
inductive StaticField (A : Type) where
  | present (value : A)
  | absent
  | undefined
  | invalidType

/-- Read an ordinary numeric field from its runtime descriptor. Every invalid shape throws its actual exception class at observation; it is never replaced by a default value or hidden inside selected dispatch.
Source reference: base/docs/basedocs.jl:2609-2620; base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/docs/basedocs.jl:2609-2620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     getfield(value, name::Symbol, [order::Symbol], [boundscheck::Bool=true])
--     getfield(value, i::Int, [order::Symbol], [boundscheck::Bool=true])
-- 
-- Extract a field from a composite `value` by name or position.
-- 
-- Optionally, an ordering can be defined for the operation.
-- If the field was declared `@atomic`, the specification is strongly recommended to be
-- compatible with the stores to that location.
-- Otherwise, if not declared as `@atomic`, this parameter must be `:not_atomic` if specified.
-- 
-- The bounds check may be disabled, in which case the behavior of this function is
-- undefined if `i` is out of bounds.
-- /Source
-- Source: base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UndefRefError       <: Exception
--     UndefRefError() = new()
-- end
-- /Source
def readStaticField {m : Type → Type} [Monad m] [MonadExceptOf StaticFieldFault m]
    {A : Type} : StaticField A → m A
  | .present value => pure value
  | .absent => throw StaticFieldFault.bounds
  | .undefined => throw StaticFieldFault.undefinedField
  | .invalidType => throw StaticFieldFault.invalidType

/-- The actual custom indexed_iterate return object exposes descriptors of its first two numeric fields, with no validity assumption. The final destructuring call needs only the first field; missing or undefined second fields are therefore preserved without premature errors.
Source reference: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
structure StaticIndexedReply (Other DestructureState : Type) where
  first : StaticField (Value Other)
  second : StaticField DestructureState

/-- Only operations on the unfixed range, arbitrary returned iterable, or non-native state values are fields. indexedFirst/indexedNext end at the selected indexed_iterate calls and expose the raw field layout; ordered Core.getfield observations remain explicit in the model. Native tuple destructuring and native scalar arithmetic are implemented concretely.
Source reference: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
structure StaticIterationOps (m : Type → Type) (Range Other Custom DestructureState : Type) where
  constructors : StaticConstructorOps m Other
  values : ValueOps m Other
  start : Range → m (StaticIterationReply Other Custom)
  step : Range → Value Other → m (StaticIterationReply Other Custom)
  indexedFirst : Custom → I64 → m (StaticIndexedReply Other DestructureState)
  indexedNext : Custom → I64 → DestructureState → m (StaticIndexedReply Other DestructureState)
  lessOtherInt : Other → I64 → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  lessOthers : Other → Other → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))

/-- Destructure the two values required by Julia assignment. Concrete tuples call their installed indexed_iterate model twice and ignore additional components, as assignment does. Custom iterable results retain both ordered selected calls and the state passed between them.
Source reference: base/reinterpretarray.jl:309-314; base/tuple.jl:159-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
-- Source: base/tuple.jl:159-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # this allows partial evaluation of bounded sequences of next() calls on tuples,
-- # while reducing to plain next() for arbitrary iterables.
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (@inline; (a[i], i+1))
-- function indexed_iterate(I, i)
--     x = iterate(I)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- function indexed_iterate(I, i, state)
--     x = iterate(I, state)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- /Source
def staticUnpackTwo {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf StaticFieldFault m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS) :
    StaticStateArgument O C → m (Value O × Value O)
  | .tuple values => do
      let first ← liftResult Error.tuple
        (JuliaLean.base.tuple.indexedIterateTuple values.values 1)
      let second ← liftResult Error.tuple
        (JuliaLean.base.tuple.indexedIterateTuple values.values 2 first.2)
      pure (first.1, second.1)
  | .custom value => do
      let firstReply ← ops.indexedFirst value one
      let first ← readStaticField firstReply.first
      let state ← readStaticField firstReply.second
      let secondReply ← ops.indexedNext value (JInt.lit .i64 2) state
      let second ← readStaticField secondReply.first
      pure (first, second)

/-- Destructure the function state argument before testing any branch. Tuple access remains checked; custom destructuring carries the state from the first call to the second and third without assuming its type or value.
Source reference: base/reinterpretarray.jl:316-325; base/tuple.jl:159-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
-- Source: base/tuple.jl:159-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # this allows partial evaluation of bounded sequences of next() calls on tuples,
-- # while reducing to plain next() for arbitrary iterables.
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (@inline; (a[i], i+1))
-- function indexed_iterate(I, i)
--     x = iterate(I)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- function indexed_iterate(I, i, state)
--     x = iterate(I, state)
--     x === nothing && throw(BoundsError(I, i))
--     x
-- end
-- /Source
def staticUnpackThree {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf StaticFieldFault m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS) :
    StaticStateArgument O C → m (StaticIterationState O)
  | .tuple values => do
      let first ← liftResult Error.tuple
        (JuliaLean.base.tuple.indexedIterateTuple values.values 1)
      let second ← liftResult Error.tuple
        (JuliaLean.base.tuple.indexedIterateTuple values.values 2 first.2)
      let third ← liftResult Error.tuple
        (JuliaLean.base.tuple.indexedIterateTuple values.values 3 second.2)
      pure ⟨first.1, second.1, third.1⟩
  | .custom value => do
      let firstReply ← ops.indexedFirst value one
      let first ← readStaticField firstReply.first
      let firstState ← readStaticField firstReply.second
      let secondReply ← ops.indexedNext value (JInt.lit .i64 2) firstState
      let second ← readStaticField secondReply.first
      let secondState ← readStaticField secondReply.second
      let thirdReply ← ops.indexedNext value (JInt.lit .i64 3) secondState
      let third ← readStaticField thirdReply.first
      pure ⟨first, second, third⟩

/-- The shared post-iterate branch preserves the exact nothing test, destructures only a non-nothing reply, constructs its scalar index with ordered Int conversions, and retains unconverted state payloads.
Source reference: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def staticIterationResult {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf StaticFieldFault m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS) (parameter : Value O) :
    StaticIterationReply O C →
      m (Option (StaticIndexResult O × StaticIterationState O))
  | .nothing => pure none
  | .tuple values => do
      let (item, state) ← staticUnpackTwo ops (.tuple values)
      let index ← callStaticIndexConstructor ops.constructors parameter (.native one) item
      pure (some (index, ⟨.native one, item, state⟩))
  | .custom value => do
      let (item, state) ← staticUnpackTwo ops (.custom value)
      let index ← callStaticIndexConstructor ops.constructors parameter (.native one) item
      pure (some (index, ⟨.native one, item, state⟩))

/-- The initial iteration calls the actual outer range once. A nothing result stops immediately; every other result is destructured before native field construction, with no law assumed about the range iterator.
Source reference: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def staticIndicesIterate {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf StaticFieldFault m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS)
    (iter : RuntimeStaticIndices O R) :
    m (Option (StaticIndexResult O × StaticIterationState O)) := do
  let reply ← ops.start iter.indices2
  staticIterationResult ops iter.parameter reply

/-- Native state/K comparison is the installed Int comparison. Every mixed or non-native pair uses its selected less-than operation and then the explicit Bool assertion at the if condition.
Source reference: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def staticStateLess {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS)
    (left right : Value O) : m Bool := do
  match left, right with
  | .native left, .native right => pure (decide (left < right))
  | .native left, .other right _ =>
      requireBool (← ops.constructors.coordinates.intLessOther left right)
  | .other left _, .native right => requireBool (← ops.lessOtherInt left right)
  | .other left _, .other right _ => requireBool (← ops.lessOthers left right)

/-- State destructuring precedes the branch. The within-channel path uses wrapping native or selected custom addition, makes no parent-iteration call, and preserves state2. The boundary path passes precisely state2 to the parent iterator and follows the same real non-nothing processing as initial iteration.
Source reference: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def staticIndicesIterateState {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    [MonadExceptOf StaticFieldFault m]
    {R O C DS : Type} (ops : StaticIterationOps m R O C DS)
    (iter : RuntimeStaticIndices O R) (argument : StaticStateArgument O C) :
    m (Option (StaticIndexResult O × StaticIterationState O)) := do
  let state ← staticUnpackThree ops argument
  if ← staticStateLess ops state.state1 iter.parameter then
    let item ← addInt ops.values state.state1 one
    let index ← callStaticIndexConstructor ops.constructors iter.parameter item state.item2
    pure (some (index, ⟨item, state.item2, state.state2⟩))
  else
    let reply ← ops.step iter.indices2 state.state2
    staticIterationResult ops iter.parameter reply

/-- SIMD outer iteration exposes the original custom range object, preserving its identity and runtime type rather than replacing it by endpoint geometry.
Source reference: base/reinterpretarray.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SimdLoop.simd_outer_range(iter::SCartesianIndices2) = iter.indices2
-- /Source
def staticSimdOuter {O R : Type} (iter : RuntimeStaticIndices O R) : R :=
  iter.indices2

/-- SIMD channel length is the exact type parameter K; it is not converted or checked here, and the unrelated argument is not inspected.
Source reference: base/reinterpretarray.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SimdLoop.simd_inner_length(::SCartesianIndices2{K}, ::Any) where K = K
-- /Source
def staticSimdInnerLength {O R A : Type}
    (iter : RuntimeStaticIndices O R) (_other : A) : Value O := iter.parameter

/-- The inner native coordinate is incremented with installed wrapping arithmetic before actual SCartesianIndex2{K} constructor selection. The default constructor retains K and both coordinates; a K-specific selected method may return any runtime value and effects. The range object is not inspected.
Source reference: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}
--     SCartesianIndex2{K}(I1+1, Ilast)
-- end
-- /Source
def staticSimdIndex {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O R : Type} (ops : StaticConstructorOps m O) (iter : RuntimeStaticIndices O R)
    (last inner : I64) : m (StaticIndexResult O) :=
  callStaticIndexConstructor ops iter.parameter (.native (inner + one)) (.native last)

/-- The Cartesian fallback target remains selected on the unfixed array type. Varargs carry arbitrary values and a machine-representable tuple arity, as the Julia method does not restrict I.
Source reference: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...) = _maybe_reshape(IndexCartesian(), A, I...)
-- /Source
structure StaticMaybeReshapeOps (m : Type → Type) (A I R O : Type) where
  fallback : RuntimeIndexStyle O → A → NativeTuple I → m R

/-- Forward all original index payloads to the Cartesian style without inspecting or converting them. The arbitrary result and effect channel are unchanged.
Source reference: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...) = _maybe_reshape(IndexCartesian(), A, I...)
-- /Source
def staticMaybeReshape {m : Type → Type} {A I R O : Type}
    (ops : StaticMaybeReshapeOps m A I R O) (array : A) (indices : NativeTuple I) : m R :=
  ops.fallback .cartesian array indices

/-- The already-reshaped specialization preserves the exact array handle and ignores every index payload, including non-native values.
Source reference: base/reinterpretarray.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _maybe_reshape(::IndexSCartesian2, A::ReshapedReinterpretArray, I...) = A
-- /Source
def staticMaybeReshapeIdentity {A I : Type} (array : A) (_indices : NativeTuple I) : A :=
  array

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- Compare the actual i against K, then pass the complete K and native coordinates
into the selected parameterized constructor. Native K reuses installed wrapping coordinate
arithmetic. K-specific constructors may return any value even with native coordinates;
the generated fallback alone constructs the known scalar-index fields.
Source reference: base/reinterpretarray.jl:280-281. -/
-- Source: base/reinterpretarray.jl:280-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
--     i.i < K ? SCartesianIndex2{K}(i.i + 1, i.j) : SCartesianIndex2{K}(1, i.j + 1)
-- /Source
def nextStaticIndex {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O : Type} (ops : StaticConstructorOps m O) (_array : A)
    (index : RuntimeStaticIndex O) : m (StaticIndexResult O) := do
  match index.parameter with
  | .native k =>
      let coordinates := m280_nextIndex k index.coordinates
      callStaticIndexConstructor ops index.parameter
        (.native coordinates.i) (.native coordinates.j)
  | .other k _ =>
      if ← requireBool (← ops.coordinates.intLessOther index.coordinates.i k) then
        callStaticIndexConstructor ops index.parameter
          (.native (index.coordinates.i + one)) (.native index.coordinates.j)
      else
        callStaticIndexConstructor ops index.parameter
          (.native one) (.native (index.coordinates.j + one))

/-- Perform native coordinate arithmetic before the actual constructor dispatch.
A K-specific constructor may accept native coordinates or non-native K and may return
any value. Only its generated fallback performs the concrete field conversions.
The original array is never inspected.
Source reference: base/reinterpretarray.jl:282-283. -/
-- Source: base/reinterpretarray.jl:282-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- prevind(::AbstractArray, i::SCartesianIndex2{K}) where {K} =
--     i.i > 1 ? SCartesianIndex2{K}(i.i - 1, i.j) : SCartesianIndex2{K}(K, i.j - 1)
-- /Source
def previousStaticIndex {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O : Type} (ops : StaticConstructorOps m O) (_array : A)
    (index : RuntimeStaticIndex O) : m (StaticIndexResult O) := do
  match index.parameter with
  | .native k =>
      let coordinates := m282_prevIndex k index.coordinates
      callStaticIndexConstructor ops index.parameter
        (.native coordinates.i) (.native coordinates.j)
  | .other _ _ =>
      if index.coordinates.i > one then
        callStaticIndexConstructor ops index.parameter
          (.native (index.coordinates.i - one)) (.native index.coordinates.j)
      else
        callStaticIndexConstructor ops index.parameter index.parameter
          (.native (index.coordinates.j - one))

end JuliaLean.base.reinterpretarray.Models2Group12


namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- Both parent and eachindex dispatch on unfixed argument types. Parent may return a different Julia type. Style retains the exact IndexSCartesian2 type-parameter value; it is not restricted to native or nonnegative channel counts.
Source reference: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(style::IndexSCartesian2, A::AbstractArray) = eachindex(style, parent(A))
-- /Source
structure EachIndexAbstractOps (m : Type → Type) (A Parent Style R : Type) where
  parent : A → m Parent
  eachindex : Style → Parent → m R

/-- The selected generic AbstractArray eachindex body evaluates parent(A) before invoking eachindex with the unchanged style. Every selected operation may mutate state, fail, or return an arbitrary represented value.
Source reference: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(style::IndexSCartesian2, A::AbstractArray) = eachindex(style, parent(A))
-- /Source
def eachIndexAbstract {m : Type → Type} [Monad m]
    {A Parent Style R : Type} (ops : EachIndexAbstractOps m A Parent Style R)
    (style : Style) (a : A) : m R := do
  let parent ← ops.parent a
  ops.eachindex style parent

/-- Open unaliascopy and reinterpret dispatch. Copied is independent of Parent because a custom copy can change Julia array type. The plain and reshape argument lists remain distinct selected operations, and neither return type is restricted to a ReinterpretArray.
Source reference: base/reinterpretarray.jl:371-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:371-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unaliascopy(a::NonReshapedReinterpretArray{T}) where {T} = reinterpret(T, unaliascopy(a.parent))
-- unaliascopy(a::ReshapedReinterpretArray{T}) where {T} = reinterpret(reshape, T, unaliascopy(a.parent))
-- /Source
structure UnaliasCopyOps (m : Type → Type) (Parent Copied R : Type) where
  copy : Parent → m Copied
  plain : TypeLayout → Copied → m R
  reshaped : TypeLayout → Copied → m R

/-- The nonreshaped unaliascopy overload first copies the stored parent, then calls the selected plain reinterpret operation with that exact result and the original target type. The surrounding monad retains failures and mutations.
Source reference: base/reinterpretarray.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unaliascopy(a::NonReshapedReinterpretArray{T}) where {T} = reinterpret(T, unaliascopy(a.parent))
-- /Source
def unaliasCopyPlain {m : Type → Type} [Monad m]
    {A Copied R O : Type} (ops : UnaliasCopyOps m A Copied R)
    (a : View O A) : m R := do
  let copied ← ops.copy a.parent
  ops.plain a.target copied

/-- The reshaped unaliascopy overload first copies the stored parent, then calls the reshape reinterpret overload with the original target type. It preserves the fixed reshape marker even if the copied parent changes type.
Source reference: base/reinterpretarray.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unaliascopy(a::ReshapedReinterpretArray{T}) where {T} = reinterpret(reshape, T, unaliascopy(a.parent))
-- /Source
def unaliasCopyReshaped {m : Type → Type} [Monad m]
    {A Copied R O : Type} (ops : UnaliasCopyOps m A Copied R)
    (a : View O A) : m R := do
  let copied ← ops.copy a.parent
  ops.reshaped a.target copied

/-- Runtime input partition for Ptr{T}(x). The three native runtime shapes are precisely Int, UInt and Ptr from the pinned Core constructor. Pointer element metadata is retained separately from its address bits. Custom denotes another runtime input type. Actual Ptr{T} method selection is recorded separately, because a T-specific method can handle a native-shaped input.
Source reference: base/boot.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/boot.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (PT::Type{Ptr{T}} where T)(x::Union{Int,UInt,Ptr}=0) = bitcast(PT, x)
-- /Source
inductive PointerArgument (Custom : Type) where
  | signed (value : I64)
  | unsigned (value : JInt .u64)
  | pointer (element : TypeLayout) (value : JuliaLean.BootCov.IntConv.Ptr)
  | custom (value : Custom)

/-- A constructor can return either a pointer with its actual element metadata or an arbitrary nonpointer result from custom dispatch. Other can be a heterogeneous tagged carrier; a custom constructor is not assumed to return the requested pointer type.
Source reference: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = Ptr{T}(unsafe_convert(Ptr{S},a.parent))
-- /Source
inductive PointerConstruction (Other : Type) where
  | pointer (element : TypeLayout) (value : JuliaLean.BootCov.IntConv.Ptr)
  | other (value : Other)

/-- Selected parent unsafe_convert and custom pointer construction operations. The TypeLayout argument to either field denotes the element parameter of Ptr{S} or Ptr{T}; the selectCustom field is pure actual method-selection metadata for the target and complete input runtime shape. A selected T-specific constructor may accept native Int, UInt or Ptr arguments and return any result. Parent conversion may return every represented runtime shape.
Source reference: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = Ptr{T}(unsafe_convert(Ptr{S},a.parent))
-- /Source
structure UnsafeConvertViewOps (m : Type → Type) (A Custom Other : Type) where
  parentUnsafe : TypeLayout → A → m (PointerArgument Custom)
  selectCustom : TypeLayout → PointerArgument Custom → Bool
  customConstruct : TypeLayout → PointerArgument Custom → m (PointerConstruction Other)

/-- Evaluate unsafe_convert(Ptr{S}, a.parent) first. The following Ptr{T} call first observes actual target-dependent method selection. Selected user constructors receive the complete original argument, including native shapes. On the known Core branch, Int/UInt/Ptr use installed ptrOfInt/ptrOfUInt/ptrOfPtr; other runtime types retain their selected constructor call. Core source for the native calls is base/boot.jl:1203. Pointer bits are never converted through unbounded arithmetic here.
Source reference: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S} = Ptr{T}(unsafe_convert(Ptr{S},a.parent))
-- /Source
def unsafeConvertView {m : Type → Type} [Monad m]
    {A Custom Other O : Type} (ops : UnsafeConvertViewOps m A Custom Other)
    (a : View O A) : m (PointerConstruction Other) := do
  let value ← ops.parentUnsafe a.source a.parent
  if ops.selectCustom a.target value then
    ops.customConstruct a.target value
  else
    match value with
    | .signed x => pure (.pointer a.target (JuliaLean.BootCov.IntConv.ptrOfInt x))
    | .unsigned x => pure (.pointer a.target (JuliaLean.BootCov.IntConv.ptrOfUInt x))
    | .pointer _ pointer => pure (.pointer a.target (JuliaLean.BootCov.IntConv.ptrOfPtr pointer))
    | .custom _ => ops.customConstruct a.target value

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean


/-- Both element Type parameters are unfixed dispatch inputs. Their selected size queries, scalar equality and parent-TYPE elsize operation retain arbitrary return values and effects. No size query is inferred from the static TypeLayout metadata.
Source reference: base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function elsize(::Type{<:ReinterpretArray{T,<:Any,S,A}}) where {T,S,A}
--     if aligned_sizeof(T) == aligned_sizeof(S)
--         elsize(A)
--     else
--         aligned_sizeof(T)
--     end
-- end
-- /Source
structure DynamicElementSizeOps (m : Type → Type) (ParentType O : Type) where
  types : TypeQueryOps m O
  scalars : ScalarOps m O
  elsize : ParentType → m (Value O)


/-- Evaluate target size and then source size before their equality condition. The equal branch calls elsize on the actual parent TYPE; the unequal branch queries target size again instead of caching its first result. Invalid equality results throw at the original Boolean condition, and every selected return type, exception and state effect is preserved.
Source reference: base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function elsize(::Type{<:ReinterpretArray{T,<:Any,S,A}}) where {T,S,A}
--     if aligned_sizeof(T) == aligned_sizeof(S)
--         elsize(A)
--     else
--         aligned_sizeof(T)
--     end
-- end
-- /Source
def elementSizeOfType {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {ParentType O : Type} (ops : DynamicElementSizeOps m ParentType O)
    (target source : TypeLayout) (parentType : ParentType) : m (Value O) := do
  let targetSize ← ops.types.alignedSize target
  let sourceSize ← ops.types.alignedSize source
  if ← scalarEqual ops.scalars targetSize sourceSize then
    ops.elsize parentType
  else
    ops.types.alignedSize target


end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- The parent pointer-indexability call has an unfixed array type and arbitrary result. The caller chooses its actual selected method; no Bool result law or purity assumption is imposed.
Source reference: base/reinterpretarray.jl:421-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:421-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_ptr_indexable(a::ReinterpretArray{T,<:Any,S}) where {T,S}
--     aligned_sizeof(T) === aligned_sizeof(S) && return false
--     return check_ptr_indexable(parent(a))
-- end
-- check_ptr_indexable(a::ReshapedArray) = check_ptr_indexable(parent(a))
-- check_ptr_indexable(a::FastContiguousSubArray) = check_ptr_indexable(parent(a))
-- check_ptr_indexable(a::Union{Array, Memory}) = true
-- check_ptr_indexable(a::AbstractArray) = false
-- /Source
structure ParentPointerOps (m : Type → Type) (A R : Type) where
  check : A → m R

/-- A parent-field view of a concrete wrapper, retaining the rest of the original wrapper as an unrestricted metadata payload. This is data, not a supplied parent callback: the source methods below only project parent. It can encode every ReshapedArray and FastContiguousSubArray without restricting axes, index types or inverse metadata. This representation adapter is necessary because the installed wrapper models restrict or erase that metadata; it does not replace their existing parent definitions.
Source reference: base/reshapedarray.jl:5-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reshapedarray.jl:5-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct ReshapedArray{T,N,P<:AbstractArray,MI<:Tuple{Vararg{SignedMultiplicativeInverse{Int}}}} <: AbstractArray{T,N}
--     parent::P
--     dims::NTuple{N,Int}
--     mi::MI
-- end
-- ReshapedArray(parent::AbstractArray{T}, dims::NTuple{N,Int}, mi) where {T,N} = ReshapedArray{T,N,typeof(parent),typeof(mi)}(parent, dims, mi)
-- /Source
structure StoredParent (P Metadata : Type) where
  parent : P
  metadata : Metadata

/-- Concrete ReshapedArray parent projection for the full stored-field representation. No selected user method replaces this known Base operation.
Source reference: base/reshapedarray.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reshapedarray.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- parent(A::ReshapedArray) = A.parent
-- /Source
def reshapedStoredParent {P Metadata : Type} (array : StoredParent P Metadata) : P :=
  array.parent

/-- Concrete SubArray parent projection for the full stored-field representation. FastContiguousSubArray is a source type alias; the parent field is the same.
Source reference: base/subarray.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/subarray.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- parent(V::SubArray) = V.parent
-- /Source
def subarrayStoredParent {P Metadata : Type} (array : StoredParent P Metadata) : P :=
  array.parent

/-- Call the actual concrete ReshapedArray parent projection and then the unfixed parent pointer-indexability method, retaining all results and effects.
Source reference: base/reinterpretarray.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_ptr_indexable(a::ReshapedArray) = check_ptr_indexable(parent(a))
-- /Source
def checkPointerReshaped {m : Type → Type} {P Metadata R : Type}
    (ops : ParentPointerOps m P R) (array : StoredParent P Metadata) : m R :=
  ops.check (reshapedStoredParent array)

/-- Call the actual concrete SubArray parent projection and then the unfixed parent pointer-indexability method. Metadata is carried unchanged and is not evaluated.
Source reference: base/reinterpretarray.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_ptr_indexable(a::FastContiguousSubArray) = check_ptr_indexable(parent(a))
-- /Source
def checkPointerSubarray {m : Type → Type} {P Metadata R : Type}
    (ops : ParentPointerOps m P R) (array : StoredParent P Metadata) : m R :=
  ops.check (subarrayStoredParent array)

/-- The selected parent isassigned method is open. Its array argument and native Int index are retained, while the surrounding effect monad carries state, exceptions and arbitrary return values.
Source reference: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds isassigned(a::ReinterpretArray, inds::SCartesianIndex2) = isassigned(a.parent, inds.j)
-- /Source
structure ParentAssignedOps (m : Type → Type) (A R : Type) where
  isassigned : A → I64 → m R

/-- Forward the stored parent and the outer coordinate j. The original static parameter and inner coordinate are not converted or inspected, and parent dispatch may return any accepted Julia value.
Source reference: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds isassigned(a::ReinterpretArray, inds::SCartesianIndex2) = isassigned(a.parent, inds.j)
-- /Source
def isAssignedStatic {m : Type → Type} {A R O K : Type}
    (ops : ParentAssignedOps m A R) (view : View O A)
    (index : RuntimeStaticIndex K) : m R :=
  ops.isassigned view.parent index.coordinates.j

/-- The internal fallback returns true for every accepted vararg tuple, including heterogeneous and non-integer values. The tuple only enforces constructible arity; it imposes no value restriction.
Source reference: base/reinterpretarray.jl:434-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:434-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @propagate_inbounds _isassigned_ra(a::ReinterpretArray, inds...) = true # that is not entirely true, but computing exactly which indexes will be accessed in the parent requires a lot of duplication from the _getindex_ra code
-- /Source
def isAssignedFallback {A O I : Type} (_view : View O A)
    (_indices : NativeTuple I) : Bool := true

/-- PaddingError stores actual Type objects, represented by the supplied type-object carrier. No early rendering into a String is performed.
Source reference: base/reinterpretarray.jl:736-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:736-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct PaddingError <: Exception
--     S::Type
--     T::Type
-- end
-- /Source
structure PaddingException (TypeObject : Type) where
  source : TypeObject
  target : TypeObject

/-- String interpolation lowers to the selected string call on literal segments and the two unfixed runtime Type objects; printing dispatch depends on the unfixed IO subtype and string-call result. These are selected leaf calls, not a replacement for the showerror composition.
Source reference: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror(io::IO, p::PaddingError)
--     print(io, "Padding of type $(p.S) is not compatible with type $(p.T).")
-- end
-- /Source
structure PaddingDisplayOps (m : Type → Type) (IO TypeObject Text Result : Type) where
  string : String → TypeObject → String → TypeObject → String → m Text
  print : IO → Text → m Result

/-- Build the interpolated error text before invoking the selected print method. Every literal and type-object argument is preserved, and an interpolation error prevents printing. Both calls retain their effects and arbitrary return types.
Source reference: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:741-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror(io::IO, p::PaddingError)
--     print(io, "Padding of type $(p.S) is not compatible with type $(p.T).")
-- end
-- /Source
def showPaddingError {m : Type → Type} [Monad m] {IO Ty Text R : Type}
    (ops : PaddingDisplayOps m IO Ty Text R) (io : IO)
    (error : PaddingException Ty) : m R := do
  let message ← ops.string "Padding of type " error.source
    " is not compatible with type " error.target "."
  ops.print io message

end JuliaLean.base.reinterpretarray.Models2Group12


namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- Source exception classes for non-Bool conditional values and rejected Core.bitsizeof arguments. Both non-DataType and nonprimitive bitsizeof failures are Julia ErrorException; message rendering is not exposed by this model.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
inductive ScalarPredicateError where
  | typeError
  | errorException
  deriving Repr, DecidableEq

/-- Actual isprimitivetype method selection. Default uses the installed generic metadata implementation; selected retains any other genuine method, including Type{CustomT} specialization or a method on primitive instances. Both cases preserve the complete original Julia value for the later Core builtin.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
inductive PrimitiveQueryArgument (V : Type) where
  | default (value : V)
  | selected (value : V)

/-- Recover the original argument without inspecting or converting its runtime value.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
def PrimitiveQueryArgument.value {V : Type} : PrimitiveQueryArgument V → V
  | .default value => value
  | .selected value => value

/-- The existing type-runtime boundary retains type/instance classification and metadata identity. PrimitiveLayout is the effective immutable layout data of a primitive DataType (including wrapper-inherited layout); it is not a supplied bitsizeof computation. Other datatypes never read that field. Only selected isprimitivetype methods remain arbitrary effectful calls; their returns retain Bool or non-Bool classification.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
structure ScalarPrimitiveOps (m : Type → Type)
    (World V D N Mod P Sym Other : Type) where
  runtime : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym
  primitiveLayout : D → JuliaLean.base.runtime_internals.DataTypeLayout
  selectedPrimitive : V → m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool Other)

/-- Compute the declared width from concrete layout data. The seven unused-bit flags occupy bits8–14. The C helper returns uint32_t, so size multiplication and subtraction use native unsigned32 wrapping before the result is widened to Julia Int64. Pinned src/julia.h:1693-1697 supplies the complete arithmetic.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- C Source: src/julia.h:1693-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE uint32_t jl_datatype_nbits(jl_datatype_t *t) JL_NOTSAFEPOINT
-- {
--     const jl_datatype_layout_t *layout = jl_datatype_layout(t);
--     return layout->size * 8 - layout->flags.unused_bits;
-- }
-- /C Source
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
def declaredBitCount (layout : JuliaLean.base.runtime_internals.DataTypeLayout) :
    JInt .u32 :=
  let shifted := JuliaLean.base.int.lshr_int layout.flags (JInt.lit .u16 8)
  let unused := JuliaLean.base.int.and_int shifted (JInt.lit .u16 127)
  layout.size * JInt.lit .u32 8 - JInt.wrap .u32 unused.val

/-- Concrete Core.bitsizeof adapter, including primitive instances and rejected type objects. Core classifies a Type object itself, but otherwise examines typeof(value); unlike isprimitivetype it does not unwrap UnionAll. It then checks the actual DataType primitive flag and computes the native declared bit count. No selected callback replaces this builtin. Exception messages are omitted under the established exception-class boundary. Pinned src/builtins.c:680-692 is the full builtin body.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- C Source: src/builtins.c:680-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_bitsizeof)
-- {
--     JL_NARGS(bitsizeof, 1, 1);
--     jl_value_t *x = args[0];
--     // Only primitive types have a bit size: for anything else, padding bits could be
--     // counted or excluded, and either choice would be hard to revise once relied upon.
--     jl_value_t *t = jl_is_type(x) ? x : jl_typeof(x);
--     if (!jl_is_datatype(t))
--         jl_error("Only a primitive DataType or an instance of one has a bit size.");
--     if (!jl_is_primitivetype(t))
--         jl_errorf("Type %s is not a primitive type and has no bit size.", jl_typename_str(t));
--     return jl_box_long(jl_datatype_nbits((jl_datatype_t*)t));
-- }
-- /C Source
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
def coreBitSizeOf {m : Type → Type} {World V D N Mod P Sym Other : Type}
    (ops : ScalarPrimitiveOps m World V D N Mod P Sym Other)
    (value : V) : Except ScalarPredicateError I64 := do
  let datatype := if ops.runtime.isAType value then ops.runtime.asDatatype value
    else some (ops.runtime.typeof value)
  let some datatype := datatype | throw .errorException
  if !JuliaLean.base.runtime_internals.has16 (ops.runtime.dataFlags datatype) 128 then
    throw .errorException
  pure (JInt.wrap .i64 (declaredBitCount (ops.primitiveLayout datatype)).val)

/-- Evaluate the selected isprimitivetype query and consume its result in the source boolean context. Native fallback uses the installed method; a selected non-Bool result raises TypeError at this position, before any following query or bitsizeof.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
def primitiveQuery {m : Type → Type} [Monad m] [MonadExceptOf ScalarPredicateError m]
    {World V D N Mod P Sym Other : Type}
    (ops : ScalarPrimitiveOps m World V D N Mod P Sym Other) :
    PrimitiveQueryArgument V → m Bool
  | .default value => pure (JuliaLean.base.runtime_internals.isprimitivetype ops.runtime value)
  | .selected value => do
    match ← ops.selectedPrimitive value with
    | .accepted result => pure result
    | .rejected _ => throw .typeError

/-- The source queries S before T, short-circuits on false and rejects non-Bool predicate returns. Only after both true results does it call concrete Core.bitsizeof on T then S and compare their native Int results by identity. It includes user-specialized type queries and primitive-instance arguments without narrowing the source signature.
Source reference: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_scalar_reinterpret_applicable(T, S)
--     isprimitivetype(S) && isprimitivetype(T) && Core.bitsizeof(T) === Core.bitsizeof(S)
-- end
-- /Source
def scalarReinterpretApplicable {m : Type → Type} [Monad m]
    [MonadExceptOf ScalarPredicateError m] {World V D N Mod P Sym Other : Type}
    (ops : ScalarPrimitiveOps m World V D N Mod P Sym Other)
    (target source : PrimitiveQueryArgument V) : m Bool := do
  unless (← primitiveQuery ops source) do return false
  unless (← primitiveQuery ops target) do return false
  let targetBits ← match coreBitSizeOf ops target.value with
    | .ok value => pure value
    | .error error => throw error
  let sourceBits ← match coreBitSizeOf ops source.value with
    | .ok value => pure value
    | .error error => throw error
  pure (targetBits == sourceBits)

end JuliaLean.base.reinterpretarray.Models2Group12


namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- Dispatch partition for the unrestricted ispacked method. The first two
cases select the installed DataType and DataTypeLayout overloads of
datatype_haspadding. Selected retains every other genuinely selected method,
including a Type{CustomT} specialization whose value is a DataType object.
Source reference: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function ispacked(T)
--     !datatype_haspadding(T)
-- end
-- /Source
inductive PackedArgument (Datatype Other : Type) where
  | datatype (value : Datatype)
  | layout (value : JuliaLean.base.runtime_internals.DataTypeLayout)
  | selected (value : Other)

/-- A datatype_haspadding or negation result retains its actual Bool or
non-Bool runtime type. This is a dispatch tag, not a Bool return assertion.
Other may be a tagged heterogeneous carrier including functions and exceptions
as ordinary returned values.
Source reference: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function ispacked(T)
--     !datatype_haspadding(T)
-- end
-- /Source
inductive PackedValue (Other : Type) where
  | boolean (value : Bool)
  | other (value : Other)

/-- The installed runtime interface supplies concrete DataType metadata access.
Only another selected datatype_haspadding method and ! on a non-Bool result
remain dispatch parameters. The established io.M carrier retains state,
exceptions, and divergence; neither selected target has a correctness law.
Source reference: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function ispacked(T)
--     !datatype_haspadding(T)
-- end
-- /Source
structure IsPackedOps (World V D N Mod P Sym Input Other : Type) where
  runtime : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym
  haspadding : Input → JuliaLean.base.io.M World (PackedValue Other)
  negate : Other → JuliaLean.base.io.M World (PackedValue Other)

/-- Evaluate datatype_haspadding first, preserving native layout-null errors
and selected custom effects. A Bool result uses the installed native ! model;
another actual runtime type invokes its selected ! operation. The final result
is unrestricted, just as in the Julia body, with no added conditional check.
Source reference: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function ispacked(T)
--     !datatype_haspadding(T)
-- end
-- /Source
def isPackedDispatched {World V D N Mod P Sym Input Other : Type}
    (ops : IsPackedOps World V D N Mod P Sym Input Other)
    (argument : PackedArgument D Input) : JuliaLean.base.io.M World (PackedValue Other) := do
  let padding ← match argument with
    | .datatype value => do
      pure (.boolean (← JuliaLean.base.runtime_internals.datatypeHaspadding ops.runtime value))
    | .layout value =>
      pure (.boolean (JuliaLean.base.runtime_internals.datatypeHaspaddingLayout value))
    | .selected value => ops.haspadding value
  match padding with
  | .boolean value =>
    pure (.boolean (JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool value))
  | .other value => ops.negate value

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- Both source arguments are unrestricted. Each non_padding_bytes call is selected on its actual argument type, and equality is selected on the two returned runtime types. Neither returned masks nor the equality result are forced to Memory or Bool.
Source reference: base/reinterpretarray.jl:815-817. -/
-- Source: base/reinterpretarray.jl:815-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function struct_subpadding(Out, In)
--     non_padding_bytes(Out) == non_padding_bytes(In)
-- end
-- /Source
structure StructSubpaddingOps (m : Type → Type) (TypeObject Mask Result : Type) where
  nonPadding : TypeObject → m Mask
  equal : Mask → Mask → m Result

/-- Evaluate output non-padding data before input non-padding data, then pass those exact values to selected equality. Arbitrary results, errors and prior state changes survive the composition.
Source reference: base/reinterpretarray.jl:815-817. -/
-- Source: base/reinterpretarray.jl:815-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function struct_subpadding(Out, In)
--     non_padding_bytes(Out) == non_padding_bytes(In)
-- end
-- /Source
def structSubpadding {m : Type → Type} [Monad m] {Ty Mask R : Type}
    (ops : StructSubpaddingOps m Ty Mask R) (output input : Ty) : m R := do
  let outputMask ← ops.nonPadding output
  let inputMask ← ops.nonPadding input
  ops.equal outputMask inputMask

/-- Native Bool negation is the installed Base primitive. Every non-Bool runtime type retains its selected unary ! method and arbitrary result; no conditional type assertion is performed by negation itself.
Source reference: base/reinterpretarray.jl:819-825. -/
-- Source: base/reinterpretarray.jl:819-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function packedsize(T)
--     if !datatype_haspadding(T)
--         sizeof(T)
--     else
--         count(non_padding_bytes(T))
--     end
-- end
-- /Source
def packedNegate {m : Type → Type} [Monad m] {O : Type}
    (negate : O → m (PackedValue O)) (value : PackedValue O) : m (PackedValue O) :=
  match value with
  | .boolean value =>
      pure (.boolean (JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool value))
  | .other value => negate value

/-- The source if consumes a Bool after unary negation has finished. A non-Bool result becomes TypeError at this point, preserving every preceding effect.
Source reference: base/reinterpretarray.jl:819-825. -/
-- Source: base/reinterpretarray.jl:819-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function packedsize(T)
--     if !datatype_haspadding(T)
--         sizeof(T)
--     else
--         count(non_padding_bytes(T))
--     end
-- end
-- /Source
def requirePackedBool {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O : Type} (value : PackedValue O) : m Bool :=
  match value with
  | .boolean value => pure value
  | .other _ => throw Error.typeError

/-- The type/object input and every selected metadata/container result type are unfixed by packedsize. The separate leaf methods retain their exact call positions; only native Bool negation and the conditional assertion are closed.
Source reference: base/reinterpretarray.jl:819-825. -/
-- Source: base/reinterpretarray.jl:819-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function packedsize(T)
--     if !datatype_haspadding(T)
--         sizeof(T)
--     else
--         count(non_padding_bytes(T))
--     end
-- end
-- /Source
structure PackedSizeOps (m : Type → Type) (TypeObject Other Mask Result : Type) where
  hasPadding : TypeObject → m (PackedValue Other)
  negate : Other → m (PackedValue Other)
  sizeOf : TypeObject → m Result
  nonPadding : TypeObject → m Mask
  count : Mask → m Result

/-- Observe haspadding, negate its actual result, then require a Boolean condition. The true branch returns selected sizeof(T); the false branch obtains non-padding data then counts that exact result. Source return types are unrestricted.
Source reference: base/reinterpretarray.jl:819-825. -/
-- Source: base/reinterpretarray.jl:819-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function packedsize(T)
--     if !datatype_haspadding(T)
--         sizeof(T)
--     else
--         count(non_padding_bytes(T))
--     end
-- end
-- /Source
def packedSize {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {Ty O Mask R : Type} (ops : PackedSizeOps m Ty O Mask R) (type : Ty) : m R := do
  let padding ← ops.hasPadding type
  let negated ← packedNegate ops.negate padding
  if ← requirePackedBool negated then
    ops.sizeOf type
  else
    let bytes ← ops.nonPadding type
    ops.count bytes

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean


/-- The source does not fix either input type or any selected non_padding_bytes return type. Preserve the selected packing, mask, emptiness, length, indexing, non-Bool negation and non-native comparison calls. Only the native Int loop counters and native Bool negation are fixed Base operations. The installed io.M carrier retains state, every represented exception and divergence; no callee-correctness laws are imposed.
Source reference: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function array_subpadding(S, T)
--     # Fast path: if every byte of `T` is a non-padding byte, any byte can be
--     # read. This also covers zero-size `T`.
--     if ispacked(T)
--         return true
--     end
--     # `T` has at least one padding byte here. If `S` has none, the byte cycle
--     # below visits every byte of `T`, so some readable byte of `S` must land on
--     # padding in `T`. This also covers zero-size `S`.
--     if ispacked(S)
--         return false
--     end
--     s_used, t_used = non_padding_bytes(S), non_padding_bytes(T)
--     # zero-size T and S are unreachable here (handled by the fast paths above);
--     # these guards only keep the loop below well-defined
--     isempty(t_used) && return true
--     isempty(s_used) && return false
--     s_n, t_n = length(s_used), length(t_used)
--     s_i, t_i = 1, 1
--     while true
--         # If a byte can be read in S, but is padding in T, return false
--         if s_used[s_i] && !t_used[t_i]
--             return false
--         end
--         # Advance the indexes with wrapping around
--         s_i += 1
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
--         # We made it back to the start
--         if isone(s_i) && isone(t_i)
--             return true
--         end
--     end
-- end
-- /Source
structure ArrayPaddingOps (World TypeArg Container Other : Type) where
  isPacked : TypeArg → JuliaLean.base.io.M World (PackedValue Other)
  nonPadding : TypeArg → JuliaLean.base.io.M World Container
  isEmpty : Container → JuliaLean.base.io.M World (PackedValue Other)
  length : Container → JuliaLean.base.io.M World (Value Other)
  getindex : Container → I64 → JuliaLean.base.io.M World (PackedValue Other)
  negate : Other → JuliaLean.base.io.M World (PackedValue Other)
  greaterOther : I64 → Other → JuliaLean.base.io.M World (PackedValue Other)


/-- A conditional consumes an actual Bool. Every other returned runtime type raises TypeError at this precise point, after all preceding selected effects. Error messages are not part of the property contract; the established IO runtime exception class is retained.
Source reference: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function array_subpadding(S, T)
--     # Fast path: if every byte of `T` is a non-padding byte, any byte can be
--     # read. This also covers zero-size `T`.
--     if ispacked(T)
--         return true
--     end
--     # `T` has at least one padding byte here. If `S` has none, the byte cycle
--     # below visits every byte of `T`, so some readable byte of `S` must land on
--     # padding in `T`. This also covers zero-size `S`.
--     if ispacked(S)
--         return false
--     end
--     s_used, t_used = non_padding_bytes(S), non_padding_bytes(T)
--     # zero-size T and S are unreachable here (handled by the fast paths above);
--     # these guards only keep the loop below well-defined
--     isempty(t_used) && return true
--     isempty(s_used) && return false
--     s_n, t_n = length(s_used), length(t_used)
--     s_i, t_i = 1, 1
--     while true
--         # If a byte can be read in S, but is padding in T, return false
--         if s_used[s_i] && !t_used[t_i]
--             return false
--         end
--         # Advance the indexes with wrapping around
--         s_i += 1
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
--         # We made it back to the start
--         if isone(s_i) && isone(t_i)
--             return true
--         end
--     end
-- end
-- /Source
def arrayPaddingCondition {World O : Type} (value : PackedValue O) :
    JuliaLean.base.io.M World Bool :=
  match value with
  | .boolean boolean => pure boolean
  | .other _ => throw (JuliaLean.base.io.Error.foreignError "TypeError" "non-boolean condition")


/-- Compare a fixed native Int counter with the actual returned length. Native Int lengths use concrete signed comparison; another length type selects its own greater-than method and then the original Boolean condition.
Source reference: base/reinterpretarray.jl:801-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:801-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
--         # We made it back to the start
-- /Source
def arrayPaddingGreater {World T C O : Type}
    (ops : ArrayPaddingOps World T C O) (index : I64) (length : Value O) :
    JuliaLean.base.io.M World Bool := do
  match length with
  | .native length => pure (decide (index > length))
  | .other length _ => arrayPaddingCondition (← ops.greaterOther index length)


/-- Advance one native Int loop counter with wrapping, then apply the source
comparison against the actual selected length value. Only a true comparison
resets to native one; arbitrary selected effects, errors and divergence precede
that reset. This is the identical common body of the two source updates.
Source reference: base/reinterpretarray.jl:800-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:800-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         s_i += 1
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
-- /Source
def arrayPaddingAdvance {World T C O : Type}
    (ops : ArrayPaddingOps World T C O) (index : I64) (length : Value O) :
    JuliaLean.base.io.M World I64 := do
  let incremented := index + one
  if ← arrayPaddingGreater ops incremented length then pure one else pure incremented


/-- The source counter is a fixed native Int, so isone calls its installed
Base model with concrete native one and equality operations. It is pure for
these concrete leaves and retains the installed Julia-error lifting boundary.
Source reference: base/reinterpretarray.jl:809-811; base/number.jl:66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:809-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         if isone(s_i) && isone(t_i)
--             return true
--         end
-- /Source
def arrayPaddingIsOne {World : Type} (index : I64) : JuliaLean.base.io.M World Bool :=
  JuliaLean.base.io.liftJl (JuliaLean.base.number.isone
    (fun (_ : I64) => .ok one) (fun x y => .ok (x == y)) index)


/-- The loop body is explicit. A false source byte skips both target indexing and negation. Counters advance with native 64-bit wrapping, source comparison precedes target comparison, and only the return to the initial pair ends a successful cycle. The installed fuel-free while-loop preserves infinite executions and partial state on errors; no callback replaces this recursion.
Source reference: base/reinterpretarray.jl:795-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:795-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         # If a byte can be read in S, but is padding in T, return false
--         if s_used[s_i] && !t_used[t_i]
--             return false
--         end
--         # Advance the indexes with wrapping around
--         s_i += 1
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
--         # We made it back to the start
--         if isone(s_i) && isone(t_i)
--             return true
--         end
--     end
-- /Source
def arrayPaddingLoop {World T C O : Type}
    (ops : ArrayPaddingOps World T C O) (sourceMask targetMask : C)
    (sourceLength targetLength : Value O) (sourceIndex targetIndex : I64) :
    JuliaLean.base.io.M World Bool :=
  JuliaLean.base.io.whileLoop (fun (indices : I64 × I64) => do
    let sourceReadable ← arrayPaddingCondition (← ops.getindex sourceMask indices.1)
    if sourceReadable then
      let targetReadable ← ops.getindex targetMask indices.2
      let targetPadding ← match targetReadable with
        | .boolean value => pure (PackedValue.boolean (JuliaLean.base.bool.notBool value))
        | .other value => ops.negate value
      if ← arrayPaddingCondition targetPadding then return .inl false
    let nextSource ← arrayPaddingAdvance ops indices.1 sourceLength
    let nextTarget ← arrayPaddingAdvance ops indices.2 targetLength
    if ← arrayPaddingIsOne nextSource then
      if ← arrayPaddingIsOne nextTarget then return .inl true
    return .inr (nextSource, nextTarget)) (sourceIndex, targetIndex)


/-- Full generic array_subpadding composition. The fast paths query target packing before source packing, then obtain source and target masks, test target emptiness before source emptiness, and obtain both lengths before starting the real native-index cycle. All operations on unfixed input/result types are selected dispatch targets; no cached native layout or detached buffer specialization substitutes for them.
Source reference: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @assume_effects :foldable function array_subpadding(S, T)
--     # Fast path: if every byte of `T` is a non-padding byte, any byte can be
--     # read. This also covers zero-size `T`.
--     if ispacked(T)
--         return true
--     end
--     # `T` has at least one padding byte here. If `S` has none, the byte cycle
--     # below visits every byte of `T`, so some readable byte of `S` must land on
--     # padding in `T`. This also covers zero-size `S`.
--     if ispacked(S)
--         return false
--     end
--     s_used, t_used = non_padding_bytes(S), non_padding_bytes(T)
--     # zero-size T and S are unreachable here (handled by the fast paths above);
--     # these guards only keep the loop below well-defined
--     isempty(t_used) && return true
--     isempty(s_used) && return false
--     s_n, t_n = length(s_used), length(t_used)
--     s_i, t_i = 1, 1
--     while true
--         # If a byte can be read in S, but is padding in T, return false
--         if s_used[s_i] && !t_used[t_i]
--             return false
--         end
--         # Advance the indexes with wrapping around
--         s_i += 1
--         if s_i > s_n
--             s_i = 1
--         end
--         t_i += 1
--         if t_i > t_n
--             t_i = 1
--         end
--         # We made it back to the start
--         if isone(s_i) && isone(t_i)
--             return true
--         end
--     end
-- end
-- /Source
def arraySubpaddingDispatched {World T C O : Type}
    (ops : ArrayPaddingOps World T C O) (source target : T) : JuliaLean.base.io.M World Bool := do
  if ← arrayPaddingCondition (← ops.isPacked target) then return true
  if ← arrayPaddingCondition (← ops.isPacked source) then return false
  let sourceMask ← ops.nonPadding source
  let targetMask ← ops.nonPadding target
  if ← arrayPaddingCondition (← ops.isEmpty targetMask) then return true
  if ← arrayPaddingCondition (← ops.isEmpty sourceMask) then return false
  let sourceLength ← ops.length sourceMask
  let targetLength ← ops.length targetMask
  arrayPaddingLoop ops sourceMask targetMask sourceLength targetLength one one


end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- The generated PaddingError stores both converted actual Type arguments. A specialized constructor may return any Julia value, represented by Thrown, which the caller must then really throw. Default exceptions retain the established exception-class boundary when raised.
Source reference: base/reinterpretarray.jl:736-739. -/
-- Source: base/reinterpretarray.jl:736-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct PaddingError <: Exception
--     S::Type
--     T::Type
-- end
-- /Source
inductive PaddingFailure (Thrown : Type) where
  | standard (first second : TypeLayout)
  | custom (value : Thrown)

/-- Cached permission flags are native Bool fields. Subpadding and non-Bool negation remain selected on unfixed type/value arguments. Error-constructor metadata selects the actual specialized method before the generated Type-field constructor; no error correctness law is assumed.
Source reference: base/reinterpretarray.jl:237-254. -/
-- Source: base/reinterpretarray.jl:237-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # See comment in check_writable
--     if !a.readable && !array_subpadding(T, S)
--         throw(PaddingError(T, S))
--     end
-- end
-- 
-- function check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # `array_subpadding` is relatively expensive (compared to a simple arrayref),
--     # so it is cached in the array. However, it is computable at compile time if,
--     # inference has the types available. By using this form of the check, we can
--     # get the best of both worlds for the success case. If the types were not
--     # available to inference, we simply need to check the field (relatively cheap)
--     # and if they were we should be able to fold this check away entirely.
--     if !a.writable && !array_subpadding(S, T)
--         throw(PaddingError(T, S))
--     end
-- end
-- /Source
-- Source: base/reinterpretarray.jl:736-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct PaddingError <: Exception
--     S::Type
--     T::Type
-- end
-- /Source
structure PermissionOps (m : Type → Type) (Other Thrown : Type) where
  subpadding : TypeLayout → TypeLayout → m (PackedValue Other)
  negate : Other → m (PackedValue Other)
  selectCustomError : TypeLayout → TypeLayout → Bool
  constructCustomError : TypeLayout → TypeLayout → m Thrown
  isType : TypeLayout → Bool
  convertType : TypeLayout → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion TypeLayout (Value Other))

/-- Element parameters are opaque descriptors and can be non-Type admissible Julia
values. The generated PaddingError constructor tests isa Type, calls selected convert(Type,x)
only when needed, then performs final Type-field validation after both conversions. A wrong
first result does not suppress the second conversion. A selected specialized constructor
runs before this generated fallback and may return any object.
Source reference: base/reinterpretarray.jl:237-254,736-739;
base/essentials.jl:1456-1488; doc/src/manual/types.md:1321-1344. -/
-- Source: base/reinterpretarray.jl:237-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # See comment in check_writable
--     if !a.readable && !array_subpadding(T, S)
--         throw(PaddingError(T, S))
--     end
-- end
-- 
-- function check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # `array_subpadding` is relatively expensive (compared to a simple arrayref),
--     # so it is cached in the array. However, it is computable at compile time if,
--     # inference has the types available. By using this form of the check, we can
--     # get the best of both worlds for the success case. If the types were not
--     # available to inference, we simply need to check the field (relatively cheap)
--     # and if they were we should be able to fold this check away entirely.
--     if !a.writable && !array_subpadding(S, T)
--         throw(PaddingError(T, S))
--     end
-- end
-- /Source
-- Source: base/reinterpretarray.jl:736-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct PaddingError <: Exception
--     S::Type
--     T::Type
-- end
-- /Source
-- Source: base/essentials.jl:1456-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
--     # Build lambda body using Core.Argument references
--     nstmts = ((n - nany) + (n - nany)) + 1
--     body_args = Array{Any,1}(Core.undef, nstmts)
--     new_args = Array{Any,1}(Core.undef, n)
--     i = 1
--     bidx = 1
--     while i !== n + 1
--         ft = fts[i]
--         if ft === Any
--             @inbounds new_args[i] = Core.Argument(i + 1)
--         else
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
-- /Source
def constructPaddingFailure {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {O E : Type} (ops : PermissionOps m O E) (first second : TypeLayout) : m (PaddingFailure E) := do
  if ops.selectCustomError first second then
    pure (.custom (← ops.constructCustomError first second))
  else
    let first ← if ops.isType first then pure (.accepted first) else ops.convertType first
    let second ← if ops.isType second then pure (.accepted second) else ops.convertType second
    match first, second with
    | .accepted first, .accepted second => pure (.standard first second)
    | _, _ => throw Error.typeError

/-- Raise the actual constructed object after constructor effects. Generated PaddingError uses the established model exception class; every selected-constructor result is passed to the genuine exception effect without forcing it to be an Exception subtype.
Source reference: base/reinterpretarray.jl:237-254. -/
-- Source: base/reinterpretarray.jl:237-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # See comment in check_writable
--     if !a.readable && !array_subpadding(T, S)
--         throw(PaddingError(T, S))
--     end
-- end
-- 
-- function check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # `array_subpadding` is relatively expensive (compared to a simple arrayref),
--     # so it is cached in the array. However, it is computable at compile time if,
--     # inference has the types available. By using this form of the check, we can
--     # get the best of both worlds for the success case. If the types were not
--     # available to inference, we simply need to check the field (relatively cheap)
--     # and if they were we should be able to fold this check away entirely.
--     if !a.writable && !array_subpadding(S, T)
--         throw(PaddingError(T, S))
--     end
-- end
-- /Source
def throwPaddingFailure {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {E X : Type} [MonadExceptOf E m] (failure : PaddingFailure E) : m X :=
  match failure with
  | .standard _ _ => throwThe Error (.reinterpret .padding)
  | .custom value => throwThe E value

/-- The cached readable flag short-circuits every selected operation. Otherwise query target/source subpadding, negate its actual result, assert Bool at the if condition, construct PaddingError with target/source arguments and then throw that exact returned object.
Source reference: base/reinterpretarray.jl:237-242. -/
-- Source: base/reinterpretarray.jl:237-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # See comment in check_writable
--     if !a.readable && !array_subpadding(T, S)
--         throw(PaddingError(T, S))
--     end
-- end
-- /Source
def checkReadable {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O V E : Type} [MonadExceptOf E m]
    (ops : PermissionOps m O E) (view : View V A) : m Unit := do
  if JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool view.readable then
    let padding ← ops.subpadding view.target view.source
    let negated ← packedNegate ops.negate padding
    if ← requirePackedBool negated then
      let failure ← constructPaddingFailure ops view.target view.source
      throwPaddingFailure failure
  pure ()

/-- The cached writable flag short-circuits every selected operation. The subpadding query uses source/target order, while the error constructor keeps target/source order. Non-Bool negation, condition errors, constructor effects and the final throw remain separate source steps.
Source reference: base/reinterpretarray.jl:244-254. -/
-- Source: base/reinterpretarray.jl:244-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}
--     # `array_subpadding` is relatively expensive (compared to a simple arrayref),
--     # so it is cached in the array. However, it is computable at compile time if,
--     # inference has the types available. By using this form of the check, we can
--     # get the best of both worlds for the success case. If the types were not
--     # available to inference, we simply need to check the field (relatively cheap)
--     # and if they were we should be able to fold this check away entirely.
--     if !a.writable && !array_subpadding(S, T)
--         throw(PaddingError(T, S))
--     end
-- end
-- /Source
def checkWritable {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O V E : Type} [MonadExceptOf E m]
    (ops : PermissionOps m O E) (view : View V A) : m Unit := do
  if JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool view.writable then
    let padding ← ops.subpadding view.source view.target
    let negated ← packedNegate ops.negate padding
    if ← requirePackedBool negated then
      let failure ← constructPaddingFailure ops view.target view.source
      throwPaddingFailure failure
  pure ()

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

open JuliaLean

/-- A selected eachindex call can return the concrete static iterator or any other runtime object. The exact stored range and K are retained in the concrete branch.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
inductive MapreduceIndices (Other Range Custom : Type) where
  | static (indices : RuntimeStaticIndices Other Range)
  | other (indices : Custom)

/-- A size result retains a machine-arity-bounded native tuple or a selected custom object. Its elements are not assumed to be native Int.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
inductive MapreduceSize (Other Custom : Type) where
  | tuple (values : NativeTuple (Value Other))
  | other (value : Custom)

/-- Only selected targets on unfixed function, operator, array, iterator and scalar types are parameterized. Actual K/R-specific size/first/last dispatch on a static iterator is selected separately from its concrete Base fallback. Native tuple indexing remains concrete. Each endpoint may be any result of selected methods or constructors.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
structure StaticMapreduceOps (m : Type → Type)
    (F OP A Other Range IterCustom SizeCustom Eltype R : Type) where
  eachindex : RuntimeIndexStyle Other → A → m (MapreduceIndices Other Range IterCustom)
  range : StaticRangeOps m Range Other
  selectSizeCustom : RuntimeStaticIndices Other Range → Bool
  sizeStaticCustom : RuntimeStaticIndices Other Range → m (MapreduceSize Other SizeCustom)
  selectFirstCustom : RuntimeStaticIndices Other Range → Bool
  firstStaticCustom : RuntimeStaticIndices Other Range → m (StaticIndexResult Other)
  selectLastCustom : RuntimeStaticIndices Other Range → Bool
  lastStaticCustom : RuntimeStaticIndices Other Range → m (StaticIndexResult Other)
  sizeOther : IterCustom → m (MapreduceSize Other SizeCustom)
  sizeGetOther : SizeCustom → I64 → m (Value Other)
  equalZeroOther : Other → I64 → m
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value Other))
  iteratorEltype : A → m Eltype
  empty : F → OP → A → Eltype → m R
  firstOther : IterCustom → m (StaticIndexResult Other)
  lastOther : IterCustom → m (StaticIndexResult Other)
  reduce : F → OP → A → StaticIndexResult Other → StaticIndexResult Other → m R

/-- Select actual size dispatch on the static iterator's unfixed K/R. The default branch calls its complete effectful size method and constructs the actual two-element tuple; a more-specific method retains arbitrary size output and effects. Other iterator types retain their selected size dispatch.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def staticMapreduceSize {m : Type → Type} [Monad m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (indices : MapreduceIndices O Range IterCustom) : m (MapreduceSize O SizeCustom) := do
  match indices with
  | .static indices =>
      if ops.selectSizeCustom indices then ops.sizeStaticCustom indices
      else
        let pair ← staticIndicesSize ops.range indices
        pure (.tuple ⟨[pair.1, pair.2], by simp⟩)
  | .other indices => ops.sizeOther indices

/-- The literal index two is a native Int. Native tuples use the installed checked getindex method, including BoundsError on short tuples; other size objects keep generic getindex dispatch.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def staticMapreduceSecondSize {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (size : MapreduceSize O SizeCustom) : m (Value O) := do
  match size with
  | .tuple values =>
      liftResult Error.tuple
        (JuliaLean.base.tuple.getindexInt values.values (JInt.lit .i64 2))
  | .other value => ops.sizeGetOther value (JInt.lit .i64 2)

/-- The zero test is concrete for native Int and otherwise retains selected equality followed by the source conditional Bool assertion.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def staticMapreduceIsZero {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (value : Value O) : m Bool := do
  match value with
  | .native n => pure (n == zero)
  | .other value _ => requireBool (← ops.equalZeroOther value zero)

/-- Actual first dispatch on unfixed static K/R precedes the default body. The known fallback preserves range observation, selected constructor dispatch and generated coordinate conversion. Other iterator types retain their selected first method.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def staticMapreduceFirst {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (indices : MapreduceIndices O Range IterCustom) : m (StaticIndexResult O) :=
  match indices with
  | .static indices =>
      if ops.selectFirstCustom indices then ops.firstStaticCustom indices
      else staticIndicesFirst ops.range indices
  | .other indices => ops.firstOther indices

/-- Actual last dispatch on unfixed static K/R precedes the default body. The known fallback observes the range before constructor dispatch and conversions. Other iterator types retain their selected last method.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def staticMapreduceLast {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (indices : MapreduceIndices O Range IterCustom) : m (StaticIndexResult O) :=
  match indices with
  | .static indices =>
      if ops.selectLastCustom indices then ops.lastStaticCustom indices
      else staticIndicesLast ops.range indices
  | .other indices => ops.lastOther indices

/-- Obtain eachindex, size and its second element before the zero test. Only the empty branch observes IteratorEltype; only the nonempty branch observes first then last. The selected empty/worker methods receive the original function, operator and array without conversion. The style is the complete zero-field IndexSCartesian2 singleton represented by its original K parameter.
Source reference: base/reinterpretarray.jl:946-954. -/
-- Source: base/reinterpretarray.jl:946-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}
--     inds = eachindex(style, A)
--     n = size(inds)[2]
--     if n == 0
--         return mapreduce_empty_iter(f, op, A, IteratorEltype(A))
--     else
--         return mapreduce_impl(f, op, A, first(inds), last(inds))
--     end
-- end
-- /Source
def mapreduceStatic {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps m F OP A O Range IterCustom SizeCustom Eltype R)
    (f : F) (op : OP) {parameter : Value O}
    (_style : StaticStyleToken (Value O) parameter) (array : A) : m R := do
  let indices ← ops.eachindex (.static parameter) array
  let size ← staticMapreduceSize ops indices
  let n ← staticMapreduceSecondSize ops size
  if ← staticMapreduceIsZero ops n then
    let kind ← ops.iteratorEltype array
    ops.empty f op array kind
  else
    let first ← staticMapreduceFirst ops indices
    let last ← staticMapreduceLast ops indices
    ops.reduce f op array first last

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.base.reinterpretarray.Models2Group12

/-- Both selected overloads depend on the unfixed function, operator and array types.
The tuning result remains unrestricted because this five-argument caller performs no
native-Int assertion. The endpoint parameters need not have the same runtime type.
Source reference: base/reinterpretarray.jl:984-985. -/
-- Source: base/reinterpretarray.jl:984-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted, ifirst::SCartesianIndex2, ilast::SCartesianIndex2) where {F,OP} =
--     mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
-- /Source
structure DefaultMapreduceOps (m : Type → Type)
    (F OP A FirstOther LastOther Block R : Type) where
  pairwiseBlocksize : F → OP → m Block
  reduce : F → OP → A → RuntimeStaticIndex FirstOther →
    RuntimeStaticIndex LastOther → Block → m R

/-- Obtain the selected pairwise block size, then dispatch with every original argument
unchanged. The two endpoint type parameters may differ, and the selected worker handles
the full dispatch result, including MethodError. All preceding state changes survive errors.
Source reference: base/reinterpretarray.jl:984-985. -/
-- Source: base/reinterpretarray.jl:984-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted, ifirst::SCartesianIndex2, ilast::SCartesianIndex2) where {F,OP} =
--     mapreduce_impl(f, op, A, ifirst, ilast, pairwise_blocksize(f, op))
-- /Source
def mapreduceDefault {m : Type → Type} [Monad m]
    {F OP A FirstOther LastOther Block R : Type}
    (ops : DefaultMapreduceOps m F OP A FirstOther LastOther Block R)
    (f : F) (op : OP) (array : A) (first : RuntimeStaticIndex FirstOther)
    (last : RuntimeStaticIndex LastOther) : m R := do
  let block ← ops.pairwiseBlocksize f op
  ops.reduce f op array first last block

end JuliaLean.base.reinterpretarray.Models2Group12

namespace JuliaLean.ArrayCov

structure ReinterpretValue where
  parent : List Int
  deriving Repr, DecidableEq

def reinterpret104Identity (array : List Int) : List Int := array
def reinterpret145ReshapeIdentity (array : List Int) : List Int := array

def reinterpret190Nested (reinterpretCall : Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall type array.parent

def reinterpret191NestedReshape
    (reinterpretCall : Bool → Int → List Int → Jl ReinterpretValue)
    (construct : Int → ReinterpretValue → Jl ReinterpretValue)
    (targetSize sourceSize parentSize : Nat)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  if targetSize = sourceSize ∨ targetSize = parentSize ∨ sourceSize = parentSize then
    reinterpretCall true type array.parent
  else construct type array

def reinterpret204Strides (size : ReinterpretValue → List JInt64)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (array : ReinterpretValue) : List JInt64 :=
  sizeToStrides (JInt.lit .i64 1) (size array)

def reinterpret229Contiguous (parentContiguous : List Int → Bool)
    (array : ReinterpretValue) : Bool := parentContiguous array.parent

def reinterpret231Similar (similar : List Int → Int → List Int → Jl Int)
    (array : ReinterpretValue) (type : Int) (dims : List Int) : Jl Int :=
  similar array.parent type dims

def reinterpret232SimilarType (similar : Int → List Int → Jl Int)
    (parentType : Int) (dims : List Int) : Jl Int := similar parentType dims


structure SCartesianIndexModel where
  i : JInt64
  j : JInt64
  deriving Repr, DecidableEq

structure SCartesianIndicesModel where
  k : JInt64
  indices2 : List JInt64
  deriving Repr, DecidableEq

def reinterpret270CombineStyle (k : JInt64) : JInt64 := k
def reinterpret276ToIndex (index : SCartesianIndexModel) : SCartesianIndexModel := index

def reinterpret277NextIndex (k : JInt64) (index : SCartesianIndexModel) : SCartesianIndexModel :=
  if index.i < k then ⟨index.i + JInt.lit .i64 1, index.j⟩
  else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩

def reinterpret279PrevIndex (k : JInt64) (index : SCartesianIndexModel) : SCartesianIndexModel :=
  if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
  else ⟨k, index.j - JInt.lit .i64 1⟩

inductive ReinterpretSimpleError where
  | assertionError
  deriving Repr, DecidableEq

abbrev ReinterpretSimpleJl (α : Type) := Except ReinterpretSimpleError α

def reinterpret285IndicesConstructor (k : JInt64) (indices : List JInt64) :
    ReinterpretSimpleJl SCartesianIndicesModel :=
  if JInt.lit .i64 1 < k then .ok ⟨k, indices⟩ else .error .assertionError

def reinterpret287EachIndex (eachIndex : Int → List Int → List JInt64)
    (construct : JInt64 → List JInt64 → ReinterpretSimpleJl SCartesianIndicesModel)
    (k : JInt64) (array : ReinterpretValue) : ReinterpretSimpleJl SCartesianIndicesModel :=
  construct k (eachIndex 1 array.parent)

def reinterpret295IndicesSize (iter : SCartesianIndicesModel) : JInt64 × JInt64 :=
  (iter.k, JInt.lit .i64 iter.indices2.length)

def reinterpret296IndicesAxes (oneTo : JInt64 → List JInt64)
    (iter : SCartesianIndicesModel) : List JInt64 × List JInt64 :=
  (oneTo iter.k, iter.indices2)

def reinterpret298IndicesFirst (first : List JInt64 → JInt64)
    (iter : SCartesianIndicesModel) : SCartesianIndexModel :=
  ⟨JInt.lit .i64 1, first iter.indices2⟩

def reinterpret299IndicesLast (last : List JInt64 → JInt64)
    (iter : SCartesianIndicesModel) : SCartesianIndexModel :=
  ⟨iter.k, last iter.indices2⟩

def reinterpret324SimdOuter (iter : SCartesianIndicesModel) : List JInt64 := iter.indices2
def reinterpret325SimdLength (iter : SCartesianIndicesModel) (_ : Int) : JInt64 := iter.k

def reinterpret326SimdIndex (_k last i1 : JInt64) : SCartesianIndexModel :=
  ⟨i1 + JInt.lit .i64 1, last⟩

def reinterpret330MaybeReshapeFallback
    (fallback : Int → ReinterpretValue → List Int → ReinterpretValue)
    (array : ReinterpretValue) (indices : List Int) : ReinterpretValue :=
  fallback 0 array indices

def reinterpret331MaybeReshapeIdentity (array : ReinterpretValue) (_indices : List Int) : ReinterpretValue :=
  array

def reinterpret362EachIndex (each : Int → ReinterpretValue → List Int)
    (style : Int) (parent : ReinterpretValue → ReinterpretValue)
    (array : ReinterpretValue) : List Int :=
  each style (parent array)


def reinterpret366Parent (array : ReinterpretValue) : List Int := array.parent
def reinterpret367DataIds (dataids : List Int → List Int)
    (array : ReinterpretValue) : List Int := dataids array.parent

def reinterpret368Unalias (copy : List Int → List Int)
    (reinterpretCall : Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall type (copy array.parent)

def reinterpret369UnaliasReshape (copy : List Int → List Int)
    (reinterpretCall : Bool → Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall true type (copy array.parent)

def reinterpret382SizeZero (_ : ReinterpretValue) : List Int := []
def reinterpret396AxesZero (_ : ReinterpretValue) : List Int := []
def reinterpret398HasOffset (hasOffset : List Int → Bool)
    (array : ReinterpretValue) : Bool := hasOffset array.parent

def reinterpret407Cconvert (cconvert : Int → List Int → Int)
    (sourceType : Int) (array : ReinterpretValue) : Int :=
  cconvert sourceType array.parent

structure PointerModel where
  targetType : Int
  address : Int
  deriving Repr, DecidableEq

def reinterpret408UnsafeConvert (unsafeConvert : Int → List Int → Int)
    (sourceType targetType : Int) (array : ReinterpretValue) : PointerModel :=
  ⟨targetType, unsafeConvert sourceType array.parent⟩

def reinterpret422CheckPtrReshaped (check : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue) (array : ReinterpretValue) : Bool :=
  check (parent array)

def reinterpret423CheckPtrSubarray (check : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue) (array : ReinterpretValue) : Bool :=
  check (parent array)

def reinterpret424CheckPtrDense (_ : ReinterpretValue) : Bool := true
def reinterpret425CheckPtrAbstract (_ : ReinterpretValue) : Bool := false

def reinterpret427GetZero (firstIndex : ReinterpretValue → Int)
    (getindex : ReinterpretValue → Int → Jl Int) (array : ReinterpretValue) : Jl Int :=
  getindex array (firstIndex array)

def reinterpret429IsAssigned (checkbounds : ReinterpretValue → List Int → Bool)
    (ptrIndexable : ReinterpretValue → Bool)
    (assignedRa : ReinterpretValue → List Int → Bool)
    (array : ReinterpretValue) (indices : List Int) : Bool :=
  checkbounds array indices && (ptrIndexable array || assignedRa array indices)

def reinterpret430IsAssignedCartesian (isassigned : List Int → JInt64 → Bool)
    (array : ReinterpretValue) (index : SCartesianIndexModel) : Bool :=
  isassigned array.parent index.j

def reinterpret431AssignedRa (_array : ReinterpretValue) (_indices : List Int) : Bool := true

def reinterpret577SetZero (firstIndex : ReinterpretValue → Int)
    (setindex : ReinterpretValue → Int → Int → Jl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) : Jl ReinterpretValue :=
  setindex array value (firstIndex array)


end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov

structure TypeLayoutModel where
  id : Int
  isBits : Bool
  hasBitPadding : Bool
  isSingleton : Bool
  alignedSize : JInt64
  deriving Repr, DecidableEq

structure AxisModel where
  first : JInt64
  length : JInt64
  deriving Repr, DecidableEq

structure ReinterpretInputModel where
  values : List Int
  rank : Int
  firstAxis : AxisModel
  deriving Repr, DecidableEq

structure ReinterpretConstructedModel where
  parent : ReinterpretInputModel
  rank : Int
  source : TypeLayoutModel
  target : TypeLayoutModel
  reshaped : Bool
  readable : Bool
  writable : Bool
  deriving Repr, DecidableEq

inductive ReinterpretConstructError where
  | targetNotBits | sourceNotBits | targetBitPadding | sourceBitPadding
  | zeroDimSize | singletonTarget | nonIntegral | badFirstAxis
  | nonMultiple | sourceSingleton | wrongFirstAxis
  deriving Repr, DecidableEq

abbrev ReinterpretConstructJl (α : Type) := Except ReinterpretConstructError α

def reinterpret14ThrowBits (_source target culprit : TypeLayoutModel) :
    ReinterpretConstructJl Unit :=
  if culprit.id = target.id then .error .targetNotBits else .error .sourceNotBits

def reinterpret18ThrowSizeZero (_source _target : TypeLayoutModel) (_message : String) :
    ReinterpretConstructJl Unit := .error .zeroDimSize

def reinterpret23ThrowSingleton (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .singletonTarget

def reinterpret27ThrowBitPadding (_source target culprit : TypeLayoutModel) :
    ReinterpretConstructJl Unit :=
  if culprit.id = target.id then .error .targetBitPadding else .error .sourceBitPadding

def reinterpret74ThrowNonIntegral (_source _target : TypeLayoutModel) (_dim : JInt64) :
    ReinterpretConstructJl Unit := .error .nonIntegral

def reinterpret80ThrowAxes (_source _target : TypeLayoutModel) (_axis : AxisModel) :
    ReinterpretConstructJl Unit := .error .badFirstAxis

def reinterpret108ThrowMultiple (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .nonMultiple

def reinterpret113ThrowSizeOne (_array : ReinterpretInputModel) (_target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .wrongFirstAxis

def reinterpret119ThrowSingletonSource (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .sourceSingleton
def reinterpret73Construct (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (array : ReinterpretInputModel) :
    ReinterpretConstructJl ReinterpretConstructedModel := do
  if !target.isBits then throw .targetNotBits
  if !source.isBits then throw .sourceNotBits
  if target.hasBitPadding then throw .targetBitPadding
  if source.hasBitPadding then throw .sourceBitPadding
  if array.rank = 0 && target.alignedSize != source.alignedSize then throw .zeroDimSize
  if array.rank != 0 && source.alignedSize != target.alignedSize then
    if target.isSingleton then
      if !source.isSingleton then throw .singletonTarget
    else
      let remainder ← JInt.remInt (array.firstAxis.length * source.alignedSize)
        target.alignedSize |>.mapError fun _ => .nonIntegral
      if remainder.val != 0 then throw .nonIntegral
    if array.firstAxis.first.val != 1 then throw .badFirstAxis
  let readable := subpadding target source
  let writable := subpadding source target
  pure ⟨array, array.rank, source, target, false, readable, writable⟩

def reinterpret107ConstructReshape
    (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (array : ReinterpretInputModel) :
    ReinterpretConstructJl ReinterpretConstructedModel := do
  if !target.isBits then throw .targetNotBits
  if !source.isBits then throw .sourceNotBits
  if target.hasBitPadding then throw .targetBitPadding
  if source.hasBitPadding then throw .sourceBitPadding
  let rank ← if source.alignedSize = target.alignedSize then pure array.rank
    else if target.alignedSize < source.alignedSize then do
      if target.isSingleton then throw .singletonTarget
      let remainder ← JInt.remInt source.alignedSize target.alignedSize
        |>.mapError fun _ => .nonMultiple
      if remainder.val != 0 then throw .nonMultiple
      pure (array.rank + 1)
    else do
      if source.isSingleton then throw .sourceSingleton
      let remainder ← JInt.remInt target.alignedSize source.alignedSize
        |>.mapError fun _ => .nonMultiple
      if remainder.val != 0 then throw .nonMultiple
      let rank := array.rank - 1
      if rank < 0 then throw .zeroDimSize
      let expected ← JInt.div target.alignedSize source.alignedSize
        |>.mapError fun _ => .wrongFirstAxis
      if array.firstAxis.first.val != 1 || array.firstAxis.length != expected then
        throw .wrongFirstAxis
      pure rank
  let readable := subpadding target source
  let writable := subpadding source target
  pure ⟨array, rank, source, target, true, readable, writable⟩

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive ReinterpretShapeError where
  | padding | nonIntegralStride | noncontiguous | arithmetic
  deriving Repr, DecidableEq

abbrev ReinterpretShapeJl (α : Type) := Except ReinterpretShapeError α

def reinterpret205Stride (ndims : ReinterpretValue → Int)
    (strides : ReinterpretValue → List JInt64) (length : ReinterpretValue → JInt64)
    (get : List JInt64 → Int → JInt64) (array : ReinterpretValue) (k : Int) : JInt64 :=
  if k ≤ ndims array then get (strides array) k else length array

def reinterpret222CheckedStrides : List JInt64 → JInt64 →
    ReinterpretShapeJl (List JInt64)
  | [], _ => .ok []
  | stride :: rest, elementSize => do
      let quotient ← JInt.div stride elementSize |>.mapError fun _ => .arithmetic
      let remainder ← JInt.remInt stride elementSize |>.mapError fun _ => .arithmetic
      if remainder.val != 0 then throw .nonIntegralStride
      let tail ← reinterpret222CheckedStrides rest elementSize
      pure (quotient :: tail)

def reinterpret208Strides
    (contiguous : ReinterpretValue → Bool)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (size stridesParent : ReinterpretValue → List JInt64)
    (elsizeParent : ReinterpretValue → JInt64)
    (targetSize sourceSize : JInt64) (isReshaped : Bool)
    (array : ReinterpretValue) : ReinterpretShapeJl (List JInt64) := do
  if contiguous array then return sizeToStrides (JInt.lit .i64 1) (size array)
  let parentStrides := stridesParent array
  if targetSize = sourceSize then return parentStrides
  let byteStrides := parentStrides.map (· * elsizeParent array)
  if isReshaped && targetSize < sourceSize then
    return JInt.lit .i64 1 :: (← reinterpret222CheckedStrides byteStrides targetSize)
  if byteStrides.getD 0 (JInt.lit .i64 0) != sourceSize then throw .noncontiguous
  let tail ← reinterpret222CheckedStrides byteStrides.tail targetSize
  if isReshaped then return tail else return JInt.lit .i64 1 :: tail

def reinterpret234CheckReadable (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (readable : Bool) : ReinterpretShapeJl Unit :=
  if !readable && !subpadding target source then .error .padding else .ok ()

def reinterpret241CheckWritable (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (writable : Bool) : ReinterpretShapeJl Unit :=
  if !writable && !subpadding source target then .error .padding else .ok ()

inductive IndexStyleModel where
  | linear | cartesian | staticCartesian (k : JInt64)
  deriving Repr, DecidableEq

def reinterpret260IndexStyle (parentStyle : Int → IndexStyleModel)
    (parentType : Int) : IndexStyleModel :=
  if parentStyle parentType = .linear then .linear else .cartesian

def reinterpret263IndexStyleReshaped (parentStyle : Int → IndexStyleModel)
    (parentType : Int) (targetSize sourceSize : JInt64) : ReinterpretShapeJl IndexStyleModel := do
  if targetSize < sourceSize then
    if parentStyle parentType = .linear then
      let k ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
      return .staticCartesian k
    return .cartesian
  return if parentStyle parentType = .linear then .linear else .cartesian

def reinterpret371Size (sizeParent : ReinterpretValue → List JInt64)
    (singletonTarget : Bool) (sourceSize targetSize : JInt64)
    (array : ReinterpretValue) : ReinterpretShapeJl (List JInt64) := do
  let parentSize := sizeParent array
  let first := parentSize.getD 0 (JInt.lit .i64 0)
  let size1 ← if singletonTarget then pure first else do
    JInt.div (first * sourceSize) targetSize |>.mapError fun _ => .arithmetic
  pure (size1 :: parentSize.tail)

def reinterpret376SizeReshaped (sizeParent : ReinterpretValue → List JInt64)
    (sourceSize targetSize : JInt64) (array : ReinterpretValue) :
    ReinterpretShapeJl (List JInt64) := do
  let parentSize := sizeParent array
  if targetSize < sourceSize then
    let ratio ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
    return ratio :: parentSize
  if sourceSize < targetSize then return parentSize.tail
  return parentSize

def reinterpret384Axes (axesParent : ReinterpretValue → List AxisModel)
    (singletonTarget : Bool) (sourceSize targetSize : JInt64)
    (array : ReinterpretValue) : ReinterpretShapeJl (List AxisModel) := do
  let parentAxes := axesParent array
  let axis := parentAxes.getD 0 ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
  let size1 ← if singletonTarget then pure axis.length else
    JInt.div (axis.length * sourceSize) targetSize |>.mapError fun _ => .arithmetic
  pure (⟨axis.first, size1⟩ :: parentAxes.tail)

def reinterpret390AxesReshaped (axesParent : ReinterpretValue → List AxisModel)
    (sourceSize targetSize : JInt64) (array : ReinterpretValue) :
    ReinterpretShapeJl (List AxisModel) := do
  let parentAxes := axesParent array
  if targetSize < sourceSize then
    let ratio ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
    return ⟨JInt.lit .i64 1, ratio⟩ :: parentAxes
  if sourceSize < targetSize then return parentAxes.tail
  return parentAxes

def reinterpret400Elsize (parentElsize : JInt64)
    (targetSize sourceSize : JInt64) : JInt64 :=
  if targetSize = sourceSize then parentElsize else targetSize

def reinterpret410GetZero (scalarApplicable : TypeLayoutModel → TypeLayoutModel → Bool)
    (reinterpretScalar : TypeLayoutModel → Int → Int)
    (parentGetZero : ReinterpretValue → Int)
    (firstIndex : ReinterpretValue → Int)
    (getindex : ReinterpretValue → Int → Int)
    (source target : TypeLayoutModel) (array : ReinterpretValue) : Int :=
  if scalarApplicable target source then reinterpretScalar target (parentGetZero array)
  else getindex array (firstIndex array)

def reinterpret418CheckPtr (parentCheck : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue)
    (targetSize sourceSize : JInt64) (array : ReinterpretValue) : Bool :=
  if targetSize = sourceSize then false else parentCheck (parent array)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive CartesianRouteError where
  | bounds
  | mismatch
  deriving Repr, DecidableEq

abbrev CartesianJl (α : Type) := Except CartesianRouteError α

def reinterpret288EachIndex (eachIndex : Int → ReinterpretValue → List SCartesianIndexModel)
    (axes : ReinterpretValue → List Int)
    (mismatch : List Int → List (List Int) → CartesianJl (List SCartesianIndexModel))
    (style : Int) (first : ReinterpretValue) (rest : List ReinterpretValue) :
    CartesianJl (List SCartesianIndexModel) :=
  let iter := eachIndex style first
  let otherIters := rest.map (eachIndex style)
  if otherIters.all (· == iter) then .ok iter
  else mismatch (axes first) (rest.map axes)

def reinterpret301GetIndex (checkbounds : SCartesianIndicesModel → JInt64 → JInt64 → Bool)
    (get : List JInt64 → JInt64 → CartesianJl JInt64)
    (iter : SCartesianIndicesModel) (i j : JInt64) : CartesianJl SCartesianIndexModel := do
  if checkbounds iter i j then pure () else throw .bounds
  let item ← get iter.indices2 j
  pure ⟨i, item⟩

def reinterpret306Iterate (iterate : List JInt64 → Option (JInt64 × JInt64))
    (iter : SCartesianIndicesModel) :
    Option (SCartesianIndexModel × (JInt64 × JInt64 × JInt64)) :=
  match iterate iter.indices2 with
  | none => none
  | some (item, state) =>
      some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))

def reinterpret313IterateState
    (iterate : List JInt64 → JInt64 → Option (JInt64 × JInt64))
    (iter : SCartesianIndicesModel)
    (state1 item2 state2 : JInt64) :
    Option (SCartesianIndexModel × (JInt64 × JInt64 × JInt64)) :=
  if state1 < iter.k then
    let item1 := state1 + JInt.lit .i64 1
    some (⟨item1, item2⟩, (item1, item2, state2))
  else
    match iterate iter.indices2 state2 with
    | none => none
    | some (item, state) =>
        some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))

def reinterpret334GetFallback
    (getCartesian : ReinterpretValue → List Int → Jl Int)
    (array : ReinterpretValue) (indices : List Int) : Jl Int :=
  getCartesian array indices

def reinterpret338SetFallback
    (setCartesian : ReinterpretValue → Int → List Int → Jl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (indices : List Int) : Jl ReinterpretValue :=
  setCartesian array value indices

def reinterpret344GetCartesian
    (firstAxis : ReinterpretValue → JInt64)
    (trailing : Int → ReinterpretValue → SCartesianIndexModel → List JInt64)
    (getindex : ReinterpretValue → List JInt64 → Jl Int)
    (style : Int) (array : ReinterpretValue) (index : SCartesianIndexModel) : Jl Int :=
  let first := firstAxis array + index.i - JInt.lit .i64 1
  getindex array (first :: trailing style array index)

def reinterpret349SetCartesian
    (firstAxis : ReinterpretValue → JInt64)
    (trailing : Int → ReinterpretValue → SCartesianIndexModel → List JInt64)
    (setindex : ReinterpretValue → Int → List JInt64 → Jl ReinterpretValue)
    (style : Int) (array : ReinterpretValue) (value : Int)
    (index : SCartesianIndexModel) : Jl ReinterpretValue :=
  let first := firstAxis array + index.i - JInt.lit .i64 1
  setindex array value (first :: trailing style array index)

def reinterpret356Trailing
    (eachIndices2 : Int → ReinterpretValue → List JInt64)
    (axes : ReinterpretValue → List (List JInt64))
    (first : List JInt64 → JInt64)
    (cartesianAt : List (List JInt64) → JInt64 → List JInt64)
    (style : Int) (array : ReinterpretValue) (index : SCartesianIndexModel) : List JInt64 :=
  let k := index.j - first (eachIndices2 style array)
  let tailAxes := (axes array).tail
  match tailAxes with
  | [axis] => [first axis + k]
  | _ => cartesianAt tailAxes (k + JInt.lit .i64 1)

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


inductive ReinterpretAccessError where
  | bounds | unreadable | unwritable | conversion
  deriving Repr, DecidableEq

abbrev ReinterpretAccessJl (α : Type) := Except ReinterpretAccessError α

def reinterpret433Get (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (getPtr : ReinterpretValue → List JInt64 → ReinterpretAccessJl Int)
    (getRa : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (indices : List JInt64) : ReinterpretAccessJl Int := do
  checkReadable array
  if ptrIndexable array then return ← getPtr array indices
  getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret439GetLinear (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (getPtr : ReinterpretValue → JInt64 → ReinterpretAccessJl Int)
    (linearStyle : ReinterpretValue → Bool)
    (toSubscripts : ReinterpretValue → JInt64 → List JInt64)
    (firstIndex : ReinterpretValue → JInt64)
    (getRa : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (index : JInt64) : ReinterpretAccessJl Int := do
  checkReadable array
  if ptrIndexable array then return ← getPtr array index
  if linearStyle array then return ← getRa array index []
  let indices := toSubscripts array index
  if indices.isEmpty then getRa array (firstIndex array) []
  else getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret451GetCartesian (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (parentGet : List Int → JInt64 → ReinterpretAccessJl Int)
    (extract : Int → JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (index : SCartesianIndexModel) : ReinterpretAccessJl Int := do
  checkReadable array
  let parentValue ← parentGet array.parent index.j
  extract parentValue index.i

def reinterpret458GetPtr (checkbounds : ReinterpretValue → List JInt64 → Bool)
    (linearIndex : ReinterpretValue → List JInt64 → JInt64)
    (firstIndex : ReinterpretValue → JInt64) (elsize : ReinterpretValue → JInt64)
    (cconvert : ReinterpretValue → JInt64)
    (load : JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (indices : List JInt64) : ReinterpretAccessJl Int := do
  if checkbounds array indices then pure () else throw .bounds
  let linear := linearIndex array indices
  let pointer := cconvert array + elsize array * (linear - firstIndex array)
  load pointer

def reinterpret466ScalarApplicable (singleton primitive : Int → Bool)
    (target source : Int) : Bool :=
  singleton target || (primitive target && target = source)

def reinterpret524GetRaReshaped
    (checkbounds : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Unit)
    (singleton : Int → Bool) (singletonValue : Int → Int)
    (scalarApplicable : Int → Int → Bool)
    (scalarGet : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (assembleLarger : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (assembleEqual : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (extractSmaller : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (target source : Int) (targetSize sourceSize : JInt64)
    (array : ReinterpretValue) (first : JInt64) (tail : List JInt64) :
    ReinterpretAccessJl Int := do
  if singleton target then
    checkbounds array first tail
    return singletonValue target
  if scalarApplicable target source then return ← scalarGet array first tail
  checkbounds array first tail
  if sourceSize < targetSize then assembleLarger array first tail
  else if targetSize = sourceSize then assembleEqual array first tail
  else extractSmaller array first tail

def reinterpret569SetZero (scalarApplicable : Int → Int → Bool)
    (convert : Int → ReinterpretAccessJl Int)
    (reinterpretScalar : Int → Int → Int)
    (parentSet : List Int → Int → ReinterpretAccessJl (List Int))
    (firstIndex : ReinterpretValue → JInt64)
    (setindex : ReinterpretValue → Int → JInt64 → ReinterpretAccessJl ReinterpretValue)
    (target source : Int) (array : ReinterpretValue) (value : Int) :
    ReinterpretAccessJl ReinterpretValue :=
  if scalarApplicable target source then do
    let value ← convert value
    let parent ← parentSet array.parent (reinterpretScalar source value)
    pure ⟨parent⟩
  else setindex array value (firstIndex array)

def reinterpret579Set (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (setPtr : ReinterpretValue → Int → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (setRa : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (indices : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  if ptrIndexable array then return ← setPtr array value indices
  setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret585SetLinear (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (setPtr : ReinterpretValue → Int → JInt64 → ReinterpretAccessJl ReinterpretValue)
    (linearStyle : ReinterpretValue → Bool)
    (toSubscripts : ReinterpretValue → JInt64 → List JInt64)
    (firstIndex : ReinterpretValue → JInt64)
    (setRa : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (index : JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  if ptrIndexable array then return ← setPtr array value index
  if linearStyle array then return ← setRa array value index []
  let indices := toSubscripts array index
  if indices.isEmpty then setRa array value (firstIndex array) []
  else setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret595SetCartesian (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (convert : Int → ReinterpretAccessJl Int)
    (parentGet : List Int → JInt64 → ReinterpretAccessJl Int)
    (overwrite : Int → Int → JInt64 → Int)
    (parentSet : List Int → JInt64 → Int → ReinterpretAccessJl (List Int))
    (array : ReinterpretValue) (value : Int) (index : SCartesianIndexModel) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  let value ← convert value
  let parentValue ← parentGet array.parent index.j
  let parent ← parentSet array.parent index.j (overwrite parentValue value index.i)
  pure ⟨parent⟩

def reinterpret607SetPtr (checkbounds : ReinterpretValue → List JInt64 → Bool)
    (linearIndex : ReinterpretValue → List JInt64 → JInt64)
    (firstIndex : ReinterpretValue → JInt64) (elsize : ReinterpretValue → JInt64)
    (cconvert : ReinterpretValue → JInt64)
    (store : JInt64 → Int → ReinterpretAccessJl Unit)
    (array : ReinterpretValue) (value : Int) (indices : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  if checkbounds array indices then pure () else throw .bounds
  let pointer := cconvert array + elsize array * (linearIndex array indices - firstIndex array)
  store pointer value
  pure array

def reinterpret685SetRaReshaped
    (convert : Int → ReinterpretAccessJl Int)
    (checkbounds : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Unit)
    (singleton : Int → Bool) (scalarApplicable : Int → Int → Bool)
    (scalarSet : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeLarger : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeEqual : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeSmaller : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (target source : Int) (targetSize sourceSize : JInt64)
    (array : ReinterpretValue) (value : Int) (first : JInt64) (tail : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  let value ← convert value
  if singleton target then
    checkbounds array first tail
    return array
  if scalarApplicable target source then return ← scalarSet array value first tail
  checkbounds array first tail
  if sourceSize < targetSize then writeLarger array value first tail
  else if targetSize = sourceSize then writeEqual array value first tail
  else writeSmaller array value first tail

end JuliaLean.ArrayCov

namespace JuliaLean.ArrayCov


structure FieldLayoutModel where
  offset : Nat
  size : Nat
  packed : Bool
  typeId : Int
  deriving Repr, DecidableEq

structure LayoutInfoModel where
  typeId : Int
  isBits : Bool
  primitive : Bool
  bitSize : Nat
  alignedSize : Nat
  datatypePadding : Bool
  bitPadding : Bool
  fields : List FieldLayoutModel
  deriving Repr, DecidableEq

inductive PaddingRouteError where
  | argument | padding
  deriving Repr, DecidableEq

abbrev PaddingJl (α : Type) := Except PaddingRouteError α

def reinterpret738ShowError (source target : String) : String :=
  s!"Padding of type {source} is not compatible with type {target}."

def setTrueRange (used : List Bool) (offset count : Nat) : List Bool :=
  (List.range count).foldl (fun result index => result.set (offset + index) true) used

def reinterpret756FillFields
    (recurse : Int → Nat → List Bool → PaddingJl (List Bool)) :
    List FieldLayoutModel → Nat → List Bool → PaddingJl (List Bool)
  | [], _, used => .ok used
  | field :: rest, offset, used => do
      let used ← recurse field.typeId (offset + field.offset) used
      reinterpret756FillFields recurse rest offset used

def reinterpret756FillNonpadding
    (recurse : Int → Nat → List Bool → PaddingJl (List Bool))
    (layout : LayoutInfoModel) (offset : Nat) (used : List Bool) :
    PaddingJl (List Bool) :=
  if layout.primitive then
    .ok (setTrueRange used offset ((layout.bitSize + 7) / 8))
  else reinterpret756FillFields recurse layout.fields offset used

def reinterpret747Nonpadding
    (fill : LayoutInfoModel → Nat → List Bool → PaddingJl (List Bool))
    (layout : LayoutInfoModel) : PaddingJl (List Bool) := do
  if layout.bitPadding then throw .argument
  let used := List.replicate layout.alignedSize false
  fill layout 0 used

def cycleSubpadding : List Bool → List Bool → Nat → Nat → Nat → Bool
  | _, _, _, _, 0 => true
  | source, target, sourceIndex, targetIndex, fuel + 1 =>
      if source.getD sourceIndex false && !target.getD targetIndex false then false
      else
        let sourceIndex := if sourceIndex + 1 ≥ source.length then 0 else sourceIndex + 1
        let targetIndex := if targetIndex + 1 ≥ target.length then 0 else targetIndex + 1
        if sourceIndex = 0 && targetIndex = 0 then true
        else cycleSubpadding source target sourceIndex targetIndex fuel

def reinterpret772ArraySubpadding (isPacked : LayoutInfoModel → Bool)
    (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (source target : LayoutInfoModel) : PaddingJl Bool := do
  if isPacked target then return true
  if isPacked source then return false
  let sourceUsed ← nonpadding source
  let targetUsed ← nonpadding target
  if targetUsed.isEmpty then return true
  if sourceUsed.isEmpty then return false
  return cycleSubpadding sourceUsed targetUsed 0 0
    (sourceUsed.length * targetUsed.length + 1)

def reinterpret812StructSubpadding (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (output input : LayoutInfoModel) : PaddingJl Bool := do
  let outputUsed ← nonpadding output
  let inputUsed ← nonpadding input
  pure (outputUsed == inputUsed)

def reinterpret816PackedSize (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (layout : LayoutInfoModel) : PaddingJl Nat :=
  if !layout.datatypePadding then .ok layout.alignedSize
  else (nonpadding layout).map (·.count true)

def reinterpret824IsPacked (layout : LayoutInfoModel) : Bool := !layout.datatypePadding

def reinterpret828HasBitPadding (anyField : List FieldLayoutModel → Bool)
    (isUnion : LayoutInfoModel → Bool) (anyUnion : LayoutInfoModel → Bool)
    (layout : LayoutInfoModel) : Bool :=
  if layout.primitive then layout.bitSize % 8 != 0
  else if isUnion layout then anyUnion layout
  else anyField layout.fields

def overwriteBytes (output : List UInt8) (offset : Nat) (bytes : List UInt8) : List UInt8 :=
  output.take offset ++ bytes ++ output.drop (offset + bytes.length)

def reinterpret839CopyToPackedFields
    (recurse : Int → List UInt8 → PaddingJl (List UInt8)) :
    List FieldLayoutModel → List UInt8 → PaddingJl (List UInt8)
  | [], _input => .ok []
  | field :: rest, input => do
      let bytes ← if field.packed then
        pure ((input.drop field.offset).take field.size)
      else recurse field.typeId (input.drop field.offset)
      let tail ← reinterpret839CopyToPackedFields recurse rest input
      pure (bytes ++ tail)

def reinterpret839CopyToPacked
    (packedSize : LayoutInfoModel → Nat)
    (recurse : Int → List UInt8 → PaddingJl (List UInt8))
    (layout : LayoutInfoModel) (input : List UInt8) : PaddingJl (List UInt8) :=
  if layout.primitive then .ok (input.take (packedSize layout))
  else reinterpret839CopyToPackedFields recurse layout.fields input

def reinterpret859CopyFromPackedFields
    (recurse : Int → List UInt8 → PaddingJl (List UInt8)) :
    List FieldLayoutModel → List UInt8 → List UInt8 → Nat → PaddingJl (List UInt8)
  | [], _packed, output, _ => .ok output
  | field :: rest, packed, output, readOffset => do
      let fieldBytes ← if field.packed then pure ((packed.drop readOffset).take field.size)
        else recurse field.typeId (packed.drop readOffset)
      let output := overwriteBytes output field.offset fieldBytes
      reinterpret859CopyFromPackedFields recurse rest packed output (readOffset + fieldBytes.length)

def reinterpret859CopyFromPacked
    (packedSize : LayoutInfoModel → Nat)
    (recurse : Int → List UInt8 → PaddingJl (List UInt8))
    (layout : LayoutInfoModel) (packed : List UInt8) : PaddingJl (List UInt8) :=
  if layout.primitive then .ok (packed.take (packedSize layout))
  else reinterpret859CopyFromPackedFields recurse layout.fields packed
    (List.replicate layout.alignedSize 0) 0

def reinterpret879Scalar
    (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (structSubpadding : LayoutInfoModel → LayoutInfoModel → PaddingJl Bool)
    (paddingRoute : LayoutInfoModel → LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (output input : LayoutInfoModel) (bytes : List UInt8) : PaddingJl (List UInt8) := do
  if !output.isBits || !input.isBits then throw .argument
  if output.bitPadding || input.bitPadding then throw .argument
  let outputSize ← reinterpret816PackedSize nonpadding output
  let inputSize ← reinterpret816PackedSize nonpadding input
  if outputSize != inputSize then throw .argument
  let samePadding ← structSubpadding output input
  if (reinterpret824IsPacked input && reinterpret824IsPacked output) || samePadding then
    pure (bytes.take output.alignedSize)
  else paddingRoute output input bytes

def reinterpret910Padding
    (copyTo : LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (copyFrom : LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (output input : LayoutInfoModel) (bytes : List UInt8) : PaddingJl (List UInt8) :=
  if !input.fields.isEmpty && reinterpret824IsPacked output then copyTo input bytes
  else if !output.fields.isEmpty && reinterpret824IsPacked input then copyFrom output bytes
  else do
    let packed ← copyTo input bytes
    copyFrom output packed

def reinterpret934String (checkReadable : ReinterpretAccessJl Unit)
    (copyString : List UInt8 → String) (bytes : List UInt8) :
    Except ReinterpretAccessError String :=
  if bytes.isEmpty then .ok ""
  else do
    checkReadable
    pure (copyString bytes)

end JuliaLean.ArrayCov

namespace JuliaLean.ReinterpretArrays

open JuliaLean

abbrev Bytes := List UInt8

/-- `a.parent[j, tailinds...]` for a 1-based parent column. -/
def colGet (col : List Bytes) (j : Int) : Jl Bytes :=
  if 1 ≤ j ∧ j ≤ col.length then .ok (col.getD (j - 1).toNat []) else .error .boundsError

/-- `a.parent[j, tailinds...] = s`. -/
def colSet (col : List Bytes) (j : Int) (s : Bytes) : Jl (List Bytes) :=
  if 1 ≤ j ∧ j ≤ col.length then .ok (col.set (j - 1).toNat s) else .error .boundsError

/-- `size(a, 1)` of `reinterpret(T, A)` for `size(A, 1) = len`, `base/reinterpretarray.jl:371-375`:
`div(psize[1]*aligned_sizeof(S), aligned_sizeof(T))` in `Int`. -/
def raSize1 (sS sT : Nat) (len : JInt64) : Jl JInt64 :=
  if sT = 0 then .ok len
  else JInt.div (len * JInt.lit .i64 sS) (JInt.lit .i64 sT)

/-- The first-dimension check of `reinterpret(T, a)`, `base/reinterpretarray.jl:90-99`, for
`dim = length(axes(a, 1))`, `first(axes(a, 1)) == 1` and `aligned_sizeof(S) != aligned_sizeof(T)`. -/
def raNewCheck (sS sT : Nat) (dim : JInt64) : Jl Unit := do
  if sT = 0 then
    if sS = 0 then pure () else throw (.argumentError "singleton")
  else
    let r ← JInt.remInt (dim * JInt.lit .i64 sS) (JInt.lit .i64 sT)
    if r.val = 0 then pure () else throw (.argumentError "non-integral first dimension")

/-- `checkbounds(a, i1, tailinds...)` on the first dimension. -/
def checkFirst (sz1 : JInt64) (i1 : JInt64) : Jl Unit :=
  if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then .ok () else .error .boundsError

/-- Partial-element copy loop of `_getindex_ra`, `base/reinterpretarray.jl:500-519`: reads
`a.parent[ind_start + i]` for `i = 1, 2, ...` (here the remaining column `elems`) until
`aligned_sizeof(T)` bytes are copied. -/
def raGetLoop (sS sT : Nat) : Nat → Nat → List Bytes → Bytes → Jl Bytes
  | sidx, copied, elems, acc =>
    if copied < sT then
      match elems with
      | [] => .error .boundsError
      | s :: rest =>
        let nb := min (sS - sidx) (sT - copied)
        raGetLoop sS sT 0 (copied + nb) rest (acc ++ (s.drop sidx).take nb)
    else .ok acc

/-- `_getindex_ra(a::NonReshapedReinterpretArray, i1, tailinds)`, `base/reinterpretarray.jl:470-522`,
on the parent column `col` with `size(a, 1) = sz1`. -/
def raGet (sS sT : Nat) (scalar : Bool) (col : List Bytes) (sz1 i1 : JInt64) : Jl Bytes := do
  if sT = 0 then
    checkFirst sz1 i1
    pure []
  else if scalar then
    colGet col i1.val
  else
    checkFirst sz1 i1
    let x := (i1 - JInt.lit .i64 1) * JInt.lit .i64 sT
    let indStart ← JInt.div x (JInt.lit .i64 sS)
    let sidx ← JInt.remInt x (JInt.lit .i64 sS)
    if sT % sS = 0 then
      let n := sT / sS
      let parts ← (List.range n).mapM (fun (i : Nat) => colGet col (indStart.val + ((i : Int) + 1)))
      pure parts.flatten
    else if sS % sT = 0 then
      let s ← colGet col (indStart.val + 1)
      pure ((s.drop sidx.val.toNat).take sT)
    else
      raGetLoop sS sT sidx.val.toNat 0 (col.drop indStart.val.toNat) []

/-- `memcpy(dst + off, src, nb)` on byte lists. -/
def overwrite (dst : Bytes) (off : Nat) (src : Bytes) : Bytes :=
  dst.take off ++ src ++ dst.drop (off + src.length)

/-- `_setindex_ra!(a::NonReshapedReinterpretArray, v, i1, tailinds)`,
`base/reinterpretarray.jl:616-683`, on the parent column `col`; returns the new column.
`s = Ref{S}()` starts as the zero element: it is only read after being fully overwritten. -/
def raSet (sS sT : Nat) (scalar : Bool) (col : List Bytes) (sz1 i1 : JInt64) (v : Bytes) :
    Jl (List Bytes) := do
  if sT = 0 then
    checkFirst sz1 i1
    pure col
  else if scalar then
    colSet col i1.val v
  else
    checkFirst sz1 i1
    let x := (i1 - JInt.lit .i64 1) * JInt.lit .i64 sT
    let indStart ← JInt.div x (JInt.lit .i64 sS)
    let sidx ← JInt.remInt x (JInt.lit .i64 sS)
    if sT % sS = 0 then
      let n := sT / sS
      (List.range n).foldlM (fun c (i : Nat) =>
        colSet c (indStart.val + ((i : Int) + 1)) ((v.drop (i * sS)).take sS)) col
    else if sS % sT = 0 then
      let s ← colGet col (indStart.val + 1)
      colSet col (indStart.val + 1) (overwrite s sidx.val.toNat v)
    else
      let sidx := sidx.val.toNat
      let st0 : List Bytes × Bytes × Nat × Int := (col, List.replicate sS 0, 0, 1)
      let st1 ← if sidx ≠ 0 then do
          let (c, _, copied, i) := st0
          let s ← colGet c (indStart.val + i)
          let nb := min (sS - sidx) sT
          let s := overwrite s sidx (v.take nb)
          let c ← colSet c (indStart.val + i) s
          pure (c, s, copied + nb, i + 1)
        else pure st0
      let st2 ← raSetMain sS sT indStart.val v st1.1 st1.2.1 st1.2.2.1 st1.2.2.2 sT
      let (c, _, copied, i) := st2
      if copied < sT then
        let s ← colGet c (indStart.val + i)
        let nb := min sS (sT - copied)
        colSet c (indStart.val + i) (overwrite s 0 ((v.drop copied).take nb))
      else pure c
where
  /-- The main-body loop, `base/reinterpretarray.jl:665-671`; `fuel` bounds the iterations
  (each copies `aligned_sizeof(S) ≥ 1` bytes, so `aligned_sizeof(T)` passes suffice). -/
  raSetMain (sS sT : Nat) (indStart : Int) (v : Bytes) :
      List Bytes → Bytes → Nat → Int → Nat → Jl (List Bytes × Bytes × Nat × Int)
    | c, s, copied, i, 0 => .ok (c, s, copied, i)
    | c, s, copied, i, fuel + 1 =>
      if copied < sT ∧ sT - copied > sS then do
        let nb := min sS (sT - copied)
        let s := overwrite s 0 ((v.drop copied).take nb)
        let c ← colSet c (indStart + i) s
        raSetMain sS sT indStart v c s (copied + nb) (i + 1) fuel
      else .ok (c, s, copied, i)

/-- `size(reinterpret(reshape, T, a))` for `size(a) = dims`, `base/reinterpretarray.jl:128-140`
(constructor checks) and `base/reinterpretarray.jl:376-381` (`size`). -/
def rrSize (sS sT : Nat) (dims : List Nat) : Jl (List Nat) :=
  if sS = sT then .ok dims
  else if sS > sT then
    if sT = 0 then .error (.argumentError "singleton")
    else if sS % sT ≠ 0 then .error (.argumentError "integer multiple")
    else .ok (sS / sT :: dims)
  else
    if sS = 0 then .error (.argumentError "from singleton")
    else if sT % sS ≠ 0 then .error (.argumentError "integer multiple")
    else match dims with
      | [] => .error (.argumentError "zero-dimensional")
      | d1 :: rest => if d1 = sT / sS then .ok rest else .error (.argumentError "axes(a, 1)")

/-- Nested `reinterpret(reshape, ...)` dispatches to the original parent when
two aligned element sizes coincide, and otherwise keeps the intermediate view. -/
def rrNestedSize (sU sS sT : Nat) (dims : List Nat) : Jl (List Nat) := do
  let intermediate ← rrSize sU sS dims
  if sT = sS ∨ sT = sU ∨ sS = sU then rrSize sU sT dims
  else rrSize sS sT intermediate

/-- Historical nested dispatch on the previous source and release. -/
def rrNestedSizeRelease (sU sS sT : Nat) (dims : List Nat) : Jl (List Nat) := do
  let _ ← rrSize sU sS dims
  rrSize sU sT dims

end JuliaLean.ReinterpretArrays
