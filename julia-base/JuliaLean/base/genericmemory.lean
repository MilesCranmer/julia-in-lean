import JuliaLean.Core

/-!
# Typed model of `base/genericmemory.jl`

The storage runtime, pointers, allocation, and atomic memory operations are typed interfaces to
Julia's other Base files or runtime. Each method below preserves this file's argument types,
control flow, checks, and same-file calls.
-/

namespace JuliaLean.base.genericmemory

open JuliaLean

abbrev I64 := JInt .i64

def int (n : _root_.Int) : I64 := JInt.lit .i64 n

instance (n : Nat) : OfNat I64 n where
  ofNat := JInt.lit .i64 n

instance : Min I64 where
  min a b := if a ≤ b then a else b

inductive MemoryIndexStyle where
  | linear
  deriving Repr, DecidableEq

inductive MemoryKind where
  | notAtomic
  | atomic
  deriving Repr, DecidableEq

structure GenericMemoryType where
  kind : MemoryKind
  elementType : Type
  addressSpace : Type

inductive MemoryOrder where
  | notAtomic
  | monotonic
  | acquire
  | release
  | acqRel
  | seqCst
  | other (name : String)
  deriving Repr, DecidableEq

/-- The reference payload mirrors Julia's memory and pointer-or-offset fields. -/
structure GenericMemoryRef (M P : Type) where
  mem : M
  ptr_or_offset : P

abbrev MemoryRef (M P : Type) := GenericMemoryRef M P
abbrev AtomicMemoryRef (M P : Type) := GenericMemoryRef M P

inductive MemoryOrArray (M A : Type) where
  | memory : M → MemoryOrArray M A
  | array : A → MemoryOrArray M A

inductive SortDirection where
  | forward
  deriving Repr, DecidableEq

structure Fix2In (X : Type) where
  x : X

/-- Operations provided by Julia's memory runtime and the other Base files. -/
structure MemoryAccessOps (m : Type → Type) (M P T V : Type) [Monad m] where
  memoryref : M → m (GenericMemoryRef M P)
  memoryrefAt : M → I64 → m (GenericMemoryRef M P)
  memoryrefNew : GenericMemoryRef M P → I64 → Bool → m (GenericMemoryRef M P)
  memoryrefIsAssigned : GenericMemoryRef M P → MemoryOrder → Bool → m Bool
  memoryrefUnset : GenericMemoryRef M P → MemoryOrder → Bool → m Unit
  memoryrefSet : GenericMemoryRef M P → T → MemoryOrder → Bool → m Unit
  defaultOrderMemory : M → MemoryOrder
  defaultOrderRef : GenericMemoryRef M P → MemoryOrder
  checkboundsBool : M → I64 → m Bool
  checkbounds : M → I64 → m Unit
  castElement : V → Option T
  convertElement : V → m T
  getindex : M → I64 → m V

/-- Pointer, copy-range, and ABI operations supplied by Julia's array/runtime layers. -/
structure MemoryCopyOps (m : Type → Type) (M P D S N I Ptr Token : Type) [Monad m] where
  isZero : N → Bool
  toInt : N → m I64
  byteCount : Type → N → m I64
  checkEnd : GenericMemoryRef M P → N → m (GenericMemoryRef M P)
  memoryrefDest : M → D → m (GenericMemoryRef M P)
  memoryrefSource : M → S → m (GenericMemoryRef M P)
  memoryrefoffset : GenericMemoryRef M P → I64
  isBitsType : Type → Bool
  gcPreserveBegin : GenericMemoryRef M P → Token
  gcPreserveEnd : Token → m Unit
  unsafeConvert : GenericMemoryRef M P → m Ptr
  memmove : Ptr → Ptr → I64 → m Unit
  ccallCopy : M → P → M → P → I64 → m Unit
  pointerDest : M → D → m Ptr
  pointerSource : M → S → m Ptr
  pointerLess : Ptr → Ptr → Bool
  pointerGreater : Ptr → Ptr → Bool
  sourceEnd : S → N → m S
  forwardRange : N → m (List I)
  backwardRange : N → m (List I)
  destIndex : D → I → m I64
  sourceIndex : S → I → m I64

/--
Julia source: base/genericmemory.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:GenericMemory}) = IndexLinear()
```
-/
def indexStyle (_MemoryType : GenericMemoryType) : MemoryIndexStyle := .linear

/--
Julia source: base/genericmemory.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(ref::GenericMemoryRef) = ref.mem
```
-/
def parent {M P : Type} (ref : GenericMemoryRef M P) : M := ref.mem

/--
Julia source: base/genericmemory.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
memoryindex(ref::GenericMemoryRef) = memoryrefoffset(ref)
```
-/
def memoryindex {M P : Type} (memoryrefoffset : GenericMemoryRef M P → I64)
    (ref : GenericMemoryRef M P) : I64 := memoryrefoffset ref

/--
Julia source: base/genericmemory.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(mem::GenericMemoryRef) = unsafe_convert(Ptr{Cvoid}, mem) # no bounds check, even for empty array
```
-/
def pointer {m : Type → Type} [Monad m] {M P Ptr : Type}
    (unsafeConvert : GenericMemoryRef M P → m Ptr) (mem : GenericMemoryRef M P) : m Ptr :=
  unsafeConvert mem

/--
Julia source: base/genericmemory.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsetindex!(A::MemoryRef) = (@_propagate_inbounds_meta; Core.memoryrefunset!(A, :not_atomic, @_boundscheck); A)
```
-/
def unsetindexRef {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (A : GenericMemoryRef M P) : m (GenericMemoryRef M P) := do
  ops.memoryrefUnset A .notAtomic boundsChecking
  pure A

/--
Julia source: base/genericmemory.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsetindex!(A::Memory, i::Int) = (@_propagate_inbounds_meta; unsetindex!(memoryref(A, i)); A)
```
-/
def unsetindexMemoryInt {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (A : M) (i : I64) : m M := do
  let ref ← ops.memoryrefAt A i
  let _ ← unsetindexRef ops boundsChecking ref
  pure A

/--
Julia source: base/genericmemory.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsetindex!(A::Union{Array, Memory}, i::Integer) = unsetindex!(A, to_index(i))
```
-/
def unsetindexUnionInteger {m : Type → Type} [Monad m] {M A P T V I : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (toIndex : I → m I64) (unsetArray : A → I64 → m Unit)
    (Avalue : MemoryOrArray M A) (i : I) : m (MemoryOrArray M A) := do
  let index ← toIndex i
  match Avalue with
  | .memory mem => return .memory (← unsetindexMemoryInt ops boundsChecking mem index)
  | .array array =>
      unsetArray array index
      return .array array

/--
Julia source: base/genericmemory.jl:160-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex_atomic!(A::AtomicMemoryRef, order::Symbol)
    @_propagate_inbounds_meta
    Core.memoryrefunset!(A, order, @_boundscheck)
    return A
end
```
-/
def unsetindexAtomicRef {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool) (A : GenericMemoryRef M P)
    (order : MemoryOrder) : m (GenericMemoryRef M P) := do
  ops.memoryrefUnset A order boundsChecking
  return A

/--
Julia source: base/genericmemory.jl:175-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex_atomic!(A::AtomicMemory, order::Symbol, i::Int)
    @_propagate_inbounds_meta
    unsetindex_atomic!(memoryref(A, i), order)
    return A
end

```
-/
def unsetindexAtomicMemoryInt {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool) (A : M) (order : MemoryOrder)
    (i : I64) : m M := do
  let ref ← ops.memoryrefAt A i
  let _ ← unsetindexAtomicRef ops boundsChecking ref order
  return A

/--
Julia source: base/genericmemory.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsetindex_atomic!(A::AtomicMemory, order::Symbol, i::Integer)
    return unsetindex_atomic!(A, order, to_index(i))
end
```
-/
def unsetindexAtomicMemoryInteger {m : Type → Type} [Monad m] {M P T V I : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool) (toIndex : I → m I64)
    (A : M) (order : MemoryOrder) (i : I) : m M := do
  let index ← toIndex i
  unsetindexAtomicMemoryInt ops boundsChecking A order index

/--
Julia source: base/genericmemory.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(@nospecialize _::Type{A}) where {T,A<:GenericMemory{<:Any,T}} = aligned_sizeof(T) # XXX: probably supposed to be the stride?
```
-/
def elsize {T : Type} (alignedSizeof : Type → I64) (_MemoryType : Type) : I64 :=
  alignedSizeof T

/--
Julia source: base/genericmemory.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(a::GenericMemory) = Core.sizeof(a)
```
-/
def sizeof {M : Type} (coreSizeof : M → I64) (a : M) : I64 := coreSizeof a

/--
Julia source: base/genericmemory.jl:189-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(a::GenericMemory, i::Int)
    @inline
    @boundscheck checkbounds(Bool, a, i) || return false
    return @inbounds memoryref_isassigned(memoryref(a, i), default_access_order(a), false)
end
```
-/
def isassignedMemory {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool) (a : M) (i : I64) : m Bool := do
  if boundsChecking then
    if !(← ops.checkboundsBool a i) then return false
  ops.memoryrefIsAssigned (← ops.memoryrefAt a i) (ops.defaultOrderMemory a) false

/--
Julia source: base/genericmemory.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isassigned(a::GenericMemoryRef) = memoryref_isassigned(a, default_access_order(a), @_boundscheck)
```
-/
def isassignedRef {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (a : GenericMemoryRef M P) : m Bool :=
  ops.memoryrefIsAssigned a (ops.defaultOrderRef a) boundsChecking

/--
Julia source: base/genericmemory.jl:198-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::MemoryRef{T}, src::MemoryRef{T}, n) where {T}
    @_terminates_globally_notaskstate_meta
    n == 0 && return dest
    @boundscheck memoryref(dest, n), memoryref(src, n)
    if isbitstype(T)
        tdest = @_gc_preserve_begin dest
        tsrc = @_gc_preserve_begin src
        pdest = unsafe_convert(Ptr{Cvoid}, dest)
        psrc = unsafe_convert(Ptr{Cvoid}, src)
        memmove(pdest, psrc, aligned_sizeof(T) * n)
        @_gc_preserve_end tdest
        @_gc_preserve_end tsrc
    else
        ccall(:jl_genericmemory_copyto, Cvoid, (Any, Ptr{Cvoid}, Any, Ptr{Cvoid}, Int), dest.mem, dest.ptr_or_offset, src.mem, src.ptr_or_offset, Int(n))
    end
    return dest
end
```
-/
def unsafeCopytoRefs {m : Type → Type} [Monad m] {M P T N D S I Ptr Token : Type}
    (copy : MemoryCopyOps m M P D S N I Ptr Token) (boundsChecking : Bool)
    (dest src : GenericMemoryRef M P) (n : N) : m (GenericMemoryRef M P) := do
  if copy.isZero n then return dest
  if boundsChecking then
    let _ ← copy.checkEnd dest n
    let _ ← copy.checkEnd src n
  if copy.isBitsType T then
    let tdest := copy.gcPreserveBegin dest
    let tsrc := copy.gcPreserveBegin src
    let pdest ← copy.unsafeConvert dest
    let psrc ← copy.unsafeConvert src
    copy.memmove pdest psrc (← copy.byteCount T n)
    copy.gcPreserveEnd tdest
    copy.gcPreserveEnd tsrc
  else
    copy.ccallCopy dest.mem dest.ptr_or_offset src.mem src.ptr_or_offset (← copy.toInt n)
  return dest

mutual
/--
Julia source: base/genericmemory.jl:216-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::GenericMemoryRef, src::GenericMemoryRef, n)
    n == 0 && return dest
    @boundscheck memoryref(dest, n), memoryref(src, n)
    unsafe_copyto!(dest.mem, memoryrefoffset(dest), src.mem, memoryrefoffset(src), n)
    return dest
end
```
-/
def unsafeCopytoGenericRefs {m : Type → Type} [Monad m]
    {M P TD TS VS N I Ptr Token : Type}
    (destOps : MemoryAccessOps m M P TD VS) (srcOps : MemoryAccessOps m M P TS VS)
    (copy : MemoryCopyOps m M P I64 I64 N I Ptr Token) (boundsChecking : Bool)
    (memoryrefoffset : GenericMemoryRef M P → I64)
    (sameElementType : Decidable (TD = TS)) (dest src : GenericMemoryRef M P) (n : N) : m (GenericMemoryRef M P) := do
  if copy.isZero n then return dest
  if boundsChecking then
    let _ ← copy.checkEnd dest n
    let _ ← copy.checkEnd src n
  match sameElementType with
  | isTrue _ =>
      let _ ← unsafeCopytoMemoryTyped (T := TD) copy boundsChecking dest.mem
        (memoryrefoffset dest) src.mem (memoryrefoffset src) n
      return dest
  | isFalse _ =>
      let _ ← unsafeCopytoMemoryFallback destOps srcOps copy dest.mem
        (memoryrefoffset dest) src.mem (memoryrefoffset src) n
      return dest

/--
Julia source: base/genericmemory.jl:223-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::Memory{T}, doffs, src::Memory{T}, soffs, n) where{T}
    n == 0 && return dest
    unsafe_copyto!(memoryref(dest, doffs), memoryref(src, soffs), n)
    return dest
end
```
-/
def unsafeCopytoMemoryTyped {m : Type → Type} [Monad m]
    {M P T D S N I Ptr Token : Type}
    (copy : MemoryCopyOps m M P D S N I Ptr Token)
    (boundsChecking : Bool) (dest : M) (doffs : D) (src : M) (soffs : S) (n : N) : m M := do
  if copy.isZero n then return dest
  let destref ← copy.memoryrefDest dest doffs
  let srcref ← copy.memoryrefSource src soffs
  let _ ← unsafeCopytoRefs (T := T) copy boundsChecking destref srcref n
  return dest

/--
Julia source: base/genericmemory.jl:230-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::Memory, doffs, src::Memory, soffs, n)
    @_terminates_locally_meta
    n == 0 && return dest
    # use pointer math to determine if they are deemed to alias
    destp = pointer(dest, doffs)
    srcp = pointer(src, soffs)
    endp = pointer(src, soffs + n - 1)
    @inbounds if destp < srcp || destp > endp
        for i = 1:n
            if isassigned(src, soffs + i - 1)
                dest[doffs + i - 1] = src[soffs + i - 1]
            else
                unsetindex!(dest, doffs + i - 1)
            end
        end
    else
        for i = n:-1:1
            if isassigned(src, soffs + i - 1)
                dest[doffs + i - 1] = src[soffs + i - 1]
            else
                unsetindex!(dest, doffs + i - 1)
            end
        end
    end
    return dest
end
```
-/
def unsafeCopytoMemoryFallback {m : Type → Type} [Monad m]
    {M P TD TS VS D S N I Ptr Token : Type}
    (destOps : MemoryAccessOps m M P TD VS) (srcOps : MemoryAccessOps m M P TS VS)
    (copy : MemoryCopyOps m M P D S N I Ptr Token)
    (dest : M) (doffs : D) (src : M) (soffs : S) (n : N) : m M := do
  if copy.isZero n then return dest
  let destp ← copy.pointerDest dest doffs
  let srcp ← copy.pointerSource src soffs
  let endOffset ← copy.sourceEnd soffs n
  let endp ← copy.pointerSource src endOffset
  if copy.pointerLess destp srcp || copy.pointerGreater destp endp then
    for i in ← copy.forwardRange n do
      let sourceIndex ← copy.sourceIndex soffs i
      if ← isassignedMemory srcOps false src sourceIndex then
        let destIndex ← copy.destIndex doffs i
        let value ← srcOps.getindex src sourceIndex
        let _ ← setindexMemory destOps false dest value destIndex
      else
        let destIndex ← copy.destIndex doffs i
        let _ ← unsetindexMemoryInt destOps false dest destIndex
  else
    for i in ← copy.backwardRange n do
      let sourceIndex ← copy.sourceIndex soffs i
      if ← isassignedMemory srcOps false src sourceIndex then
        let destIndex ← copy.destIndex doffs i
        let value ← srcOps.getindex src sourceIndex
        let _ ← setindexMemory destOps false dest value destIndex
      else
        let destIndex ← copy.destIndex doffs i
        let _ ← unsetindexMemoryInt destOps false dest destIndex
  return dest

/--
Julia source: base/genericmemory.jl:257-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy(a::T) where {T<:Memory}
    # `copy` only throws when the size exceeds the max allocation size,
    # but since we're copying an existing array, we're guaranteed that this will not happen.
    @_nothrow_meta
    newmem = T(undef, length(a))
    @inbounds unsafe_copyto!(newmem, 1, a, 1, length(a))
end
```
-/
def copyMemory {m : Type → Type} [Monad m] {M P T Ptr Token : Type}
    (copy : MemoryCopyOps m M P I64 I64 I64 I64 Ptr Token)
    (length : M → m I64) (construct : I64 → m M) (a : M) : m M := do
  let newmem ← do construct (← length a)
  unsafeCopytoMemoryTyped (T := T) copy false newmem 1 a 1 (← length a)

/--
Julia source: base/genericmemory.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory, src::Memory) = copyto!(dest, 1, src, 1, length(src))
```
-/
def copytoMemory {m : Type → Type} [Monad m] {M N : Type}
    (length : M → m N) (copyImpl : M → I64 → M → I64 → N → m M)
    (dest src : M) : m M := do
  copytoMemoryOffsets copyImpl dest 1 src 1 (← length src)

/--
Julia source: base/genericmemory.jl:266-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::Memory, doffs::Integer, src::Memory, soffs::Integer, n::Integer) =
    _copyto_impl!(dest, doffs, src, soffs, n)
```
-/
def copytoMemoryOffsets {m : Type → Type} [Monad m] {M D S N : Type}
    (copyImpl : M → D → M → S → N → m M)
    (dest : M) (doffs : D) (src : M) (soffs : S) (n : N) : m M :=
  copyImpl dest doffs src soffs n

/--
Julia source: base/genericmemory.jl:272-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::GenericMemory) =
    typeof(a)(undef, length(a))
```
-/
def similarMemory {m : Type → Type} [Monad m] {M : Type}
    (length : M → m I64) (construct : I64 → m M) (a : M) : m M :=
  do construct (← length a)

/--
Julia source: base/genericmemory.jl:274-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::GenericMemory{kind,<:Any,AS}, T::Type) where {kind,AS} =
    GenericMemory{kind,T,AS}(undef, length(a))
```
-/
def similarMemoryElementType {m : Type → Type} [Monad m] {M R T : Type}
    (length : M → m I64) (construct : Type → I64 → m R) (a : M) (_T : Type) : m R :=
  do construct T (← length a)

/--
Julia source: base/genericmemory.jl:276-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::GenericMemory, m::Int) =
    typeof(a)(undef, m)
```
-/
def similarMemoryLength {m : Type → Type} [Monad m] {M : Type}
    (construct : I64 → m M) (_a : M) (mSize : I64) : m M :=
  construct mSize

/--
Julia source: base/genericmemory.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::GenericMemory{kind,<:Any,AS}, T::Type, dims::Dims{1}) where {kind,AS} =
    GenericMemory{kind,T,AS}(undef, dims[1])
```
-/
def similarMemoryElementDims {m : Type → Type} [Monad m] {M R T D : Type}
    (construct : Type → I64 → m R) (firstDim : D → m I64)
    (_a : M) (_T : Type) (dims : D) : m R := do
  construct T (← firstDim dims)

/--
Julia source: base/genericmemory.jl:280-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(a::GenericMemory, dims::Dims{1}) =
    typeof(a)(undef, dims[1])
```
-/
def similarMemoryDims {m : Type → Type} [Monad m] {M D : Type}
    (construct : I64 → m M) (firstDim : D → m I64) (_a : M) (dims : D) : m M :=
  do construct (← firstDim dims)

/--
Julia source: base/genericmemory.jl:283-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill!(a::Union{Memory{UInt8}, Memory{Int8}}, x::Integer)
    t = @_gc_preserve_begin a
    p = unsafe_convert(Ptr{Cvoid}, a)
    T = eltype(a)
    memset(p, x isa T ? x : convert(T, x), length(a) % UInt)
    @_gc_preserve_end t
    return a
end

```
-/
def fillByteMemory {m : Type → Type} [Monad m] {M P X U USize Token : Type}
    (elementType : M → Type) (isInteger : X → Prop)
    (castElement : Type → X → Option U) (convert : Type → X → m U)
    (preserveBegin : M → Token) (preserveEnd : Token → m Unit)
    (unsafeConvert : M → m P) (memset : P → U → USize → m Unit)
    (lengthModUInt : M → m USize) (a : M) (x : X)
    (_integer : isInteger x) : m M := do
  let token := preserveBegin a
  let p ← unsafeConvert a
  let T := elementType a
  let value ← match castElement T x with | some v => pure v | none => convert T x
  memset p value (← lengthModUInt a)
  preserveEnd token
  return a

/--
Julia source: base/genericmemory.jl:294-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, a::AbstractArray) where {T<:Memory} = a isa T ? a : T(a)::T
```
-/
def convertMemory {m : Type → Type} [Monad m] {M A : Type}
    (asTarget : A → Option M) (construct : A → m M) (a : A) : m M :=
  match asTarget a with | some value => pure value | none => construct a

/--
Julia source: base/genericmemory.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(a::Type{Memory{T}}, b::Type{Memory{S}}) where {T,S} = el_same(promote_type(T,S), a, b)
```
-/
def promoteRuleMemory {R : Type}
    (promoteType : Type → Type → Type) (elSame : Type → Type → Type → R)
    (T S : Type) : R := elSame (promoteType T S) T S

/--
Julia source: base/genericmemory.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Memory{T}(x::AbstractArray{S,1}) where {T,S} = copyto_axcheck!(Memory{T}(undef, size(x)), x)
```
-/
def memoryFromArray {m : Type → Type} [Monad m] {M A D : Type}
    (size : A → m D) (constructUndef : D → m M)
    (copytoAxcheck : M → A → m M) (x : A) : m M := do
  copytoAxcheck (← constructUndef (← size x)) x

/--
Julia source: base/genericmemory.jl:308-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Memory, I::AbstractUnitRange{<:Integer})
    @inline
    @boundscheck checkbounds(A, I)
    lI = length(I)
    X = similar(A, axes(I))
    if lI > 0
        copyto!(X, firstindex(X), A, first(I), lI)
    end
    return X
end
```
-/
def getindexMemoryRange {m : Type → Type} [Monad m] {M I : Type}
    (copyImpl : M → I64 → M → I64 → I64 → m M)
    (checkbounds : M → I → m Unit) (rangeLength : I → m I64) (rangeAxes : I → m I64)
    (rangeFirst : I → m I64) (firstindex : M → m I64)
    (construct : I64 → m M) (A : M) (I : I) (boundsChecking : Bool) : m M := do
  if boundsChecking then checkbounds A I
  let lI ← rangeLength I
  let X ← similarMemoryDims construct (fun d => pure d) A (← rangeAxes I)
  if lI > 0 then
    let _ ← copytoMemoryOffsets copyImpl X (← firstindex X) A (← rangeFirst I) lI
  return X

/--
Julia source: base/genericmemory.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(a::Memory, r::AbstractUnitRange{Bool}) = getindex(a, to_index(r))
```
-/
def getindexMemoryBoolRange {m : Type → Type} [Monad m] {M I J : Type}
    (construct : I64 → m M) (copyImpl : M → I64 → M → I64 → I64 → m M)
    (checkbounds : M → J → m Unit) (rangeLength : J → m I64) (rangeAxes : J → m I64)
    (rangeFirst : J → m I64) (firstindex : M → m I64) (toIndex : I → m J)
    (a : M) (r : I) (boundsChecking : Bool) : m M := do
  getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
    construct a (← toIndex r) boundsChecking

/--
Julia source: base/genericmemory.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(A::Memory, c::Colon) = copy(A)
```
-/
def getindexMemoryColon {m : Type → Type} [Monad m] {M P T Ptr Token : Type}
    (copy : MemoryCopyOps m M P I64 I64 I64 I64 Ptr Token)
    (length : M → m I64) (construct : I64 → m M) (a : M) : m M :=
  copyMemory (T := T) copy length construct a

/--
Julia source: base/genericmemory.jl:326-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(A::Memory{T}, x::T, i1::Int) where {T}
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i1)
    memoryrefset!(memoryrefnew(memoryref(A), i1, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexMemoryRaw {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (A : M) (x : T) (i1 : I64) : m M := do
  if boundsChecking then ops.checkbounds A i1
  let baseRef ← ops.memoryref A
  let targetRef ← ops.memoryrefNew baseRef i1 false
  ops.memoryrefSet targetRef x .notAtomic false
  return A

/--
Julia source: base/genericmemory.jl:333-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{T}, x, i1::Int) where {T}
    @_propagate_inbounds_meta
    val = x isa T ? x : convert(T,x)::T
    return _setindex!(A, val, i1)
end
```
-/
def setindexMemory {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (A : M) (x : V) (i1 : I64) : m M := do
  let val ← match ops.castElement x with | some v => pure v | none => ops.convertElement x
  setindexMemoryRaw ops boundsChecking A val i1

/--
Julia source: base/genericmemory.jl:339-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{T}, x, i1::Int, i2::Int, I::Int...) where {T}
    @inline
    @boundscheck (i2 == 1 && all(==(1), I)) || throw_boundserror(A, i1, i2, I...)
    setindex!(A, x, i1)
end
```
-/
def setindexMemoryCartesian {m : Type → Type} [Monad m] {M P T V : Type}
    (ops : MemoryAccessOps m M P T V) (boundsChecking : Bool)
    (throwBounds : M → I64 → I64 → List I64 → m Unit)
    (A : M) (x : V) (i1 i2 : I64) (I : List I64) : m M := do
  if boundsChecking && !(i2 == 1 && I.all (fun i => i == 1)) then
    throwBounds A i1 i2 I
  setindexMemory ops boundsChecking A x i1

/--
Julia source: base/genericmemory.jl:346-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{T}, X::Memory{T}, I::AbstractUnitRange{Int}) where T
    @inline
    @boundscheck checkbounds(A, I)
    lI = length(I)
    setindex_shape_check(X, lI)
    if lI > 0
        unsafe_copyto!(A, first(I), X, 1, lI)
    end
    return A
end
```
-/
def setindexMemoryRange {m : Type → Type} [Monad m] {M P T I : Type}
    (copy : MemoryCopyOps m M P I64 I64 I64 I64 P Unit)
    (checkbounds : M → I → m Unit) (rangeLength : I → m I64) (rangeFirst : I → m I64)
    (shapeCheck : M → I64 → m Unit) (boundsChecking : Bool)
    (A X : M) (indices : I) : m M := do
  if boundsChecking then checkbounds A indices
  let lI ← rangeLength indices
  shapeCheck X lI
  if lI > 0 then
    let _ ← unsafeCopytoMemoryTyped (T := T) copy boundsChecking A (← rangeFirst indices) X 1 lI
  return A

/--
Julia source: base/genericmemory.jl:356-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{T}, X::Memory{T}, c::Colon) where T
    @inline
    lI = length(A)
    setindex_shape_check(X, lI)
    if lI > 0
        unsafe_copyto!(A, 1, X, 1, lI)
    end
    return A
end
```
-/
def setindexMemoryColon {m : Type → Type} [Monad m] {M P T : Type}
    (copy : MemoryCopyOps m M P I64 I64 I64 I64 P Unit)
    (length : M → m I64) (shapeCheck : M → I64 → m Unit) (boundsChecking : Bool)
    (A X : M) : m M := do
  let lI ← length A
  shapeCheck X lI
  if lI > 0 then
    let _ ← unsafeCopytoMemoryTyped (T := T) copy boundsChecking A 1 X 1 lI
  return A

end

/--
Julia source: base/genericmemory.jl:367-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(a::Memory{UInt8}, b::Memory{UInt8})
    ta = @_gc_preserve_begin a
    tb = @_gc_preserve_begin b
    pa = unsafe_convert(Ptr{Cvoid}, a)
    pb = unsafe_convert(Ptr{Cvoid}, b)
    c = memcmp(pa, pb, min(length(a),length(b)))
    @_gc_preserve_end ta
    @_gc_preserve_end tb
    return c < 0 ? -1 : c > 0 ? +1 : cmp(length(a),length(b))
end
```
-/
def cmpByteMemory {m : Type → Type} [Monad m] {M Ptr Tok : Type}
    (length : M → m I64) (gcPreserveBegin : M → Tok) (gcPreserveEnd : Tok → m Unit)
    (unsafeConvert : M → m Ptr) (memcmp : Ptr → Ptr → I64 → m I64)
    (cmpLength : I64 → I64 → m I64) (a b : M) : m I64 := do
  let ta := gcPreserveBegin a
  let tb := gcPreserveBegin b
  let pa ← unsafeConvert a
  let pb ← unsafeConvert b
  let c ← memcmp pa pb (min (← length a) (← length b))
  gcPreserveEnd ta
  gcPreserveEnd tb
  if c < 0 then return -1 else if c > 0 then return 1 else cmpLength (← length a) (← length b)

/--
Julia source: base/genericmemory.jl:380-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::M, b::M) where {M <: BitIntegerMemory}
    if length(a) == length(b)
        ta = @_gc_preserve_begin a
        tb = @_gc_preserve_begin b
        pa = unsafe_convert(Ptr{Cvoid}, a)
        pb = unsafe_convert(Ptr{Cvoid}, b)
        c = memcmp(pa, pb, sizeof(eltype(M)) * length(a))
        @_gc_preserve_end ta
        @_gc_preserve_end tb
        return c == 0
    else
        return false
    end
end
```
-/
def equalBitIntegerMemory {m : Type → Type} [Monad m] {M Ptr Tok : Type}
    (length : M → m I64) (gcPreserveBegin : M → Tok) (gcPreserveEnd : Tok → m Unit)
    (unsafeConvert : M → m Ptr) (sizeofElement : Type → I64) (elementType : M → Type)
    (memcmp : Ptr → Ptr → I64 → m I64) (a b : M) : m Bool := do
  if (← length a) == (← length b) then
    let ta := gcPreserveBegin a
    let tb := gcPreserveBegin b
    let pa ← unsafeConvert a
    let pb ← unsafeConvert b
    let c ← memcmp pa pb (sizeofElement (elementType a) * (← length a))
    gcPreserveEnd ta
    gcPreserveEnd tb
    return c == 0
  else
    return false

/--
Julia source: base/genericmemory.jl:395-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(pred::Fix2{typeof(in),<:Union{Memory{<:Real},Real}}, x::Memory{<:Real})
    if issorted(x, Sort.Forward) && issorted(pred.x, Sort.Forward)
        return _sortedfindin(x, pred.x)
    else
        return _findin(x, pred.x)
    end
end
```
-/
def findallMemory {m : Type → Type} [Monad m] {M X R : Type}
    (issortedMemory : M → SortDirection → m Bool) (issortedNeedle : X → SortDirection → m Bool)
    (sortedFindin : M → X → m R) (findin : M → X → m R)
    (pred : Fix2In X) (x : M) : m R := do
  if (← issortedMemory x .forward) then
    if (← issortedNeedle pred.x .forward) then
      sortedFindin x pred.x
    else
      findin x pred.x
  else
    findin x pred.x

/--
Julia source: base/genericmemory.jl:404-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indcopy(sz::Dims, I::GenericMemory)
    n = length(I)
    s = sz[n]
    for i = n+1:length(sz)
        s *= sz[i]
    end
    dst = eltype(I)[_findin(I[i], i < n ? (1:sz[i]) : (1:s)) for i = 1:n]
    src = eltype(I)[I[i][_findin(I[i], i < n ? (1:sz[i]) : (1:s))] for i = 1:n]
    dst, src
end
```
-/
def indcopy {m : Type → Type} [Monad m] {M X Y Vector : Type}
    (sizeAt : List I64 → I64 → m I64) (sizeLength : List I64 → I64)
    (rangeFromTo : I64 → I64 → m (List I64)) (oneRange : I64 → m (List I64))
    (addInt : I64 → I64 → m I64) (mulInt : I64 → I64 → m I64)
    (length : M → m I64) (getindex : M → I64 → m X)
    (findin : X → List I64 → m Y) (subindex : X → Y → m Y)
    (toVector : List Y → m Vector) (sz : List I64) (I : M) : m (Vector × Vector) := do
  let n ← length I
  let mut s ← sizeAt sz n
  for i in ← rangeFromTo (← addInt n 1) (sizeLength sz) do
    s ← mulInt s (← sizeAt sz i)
  let indices ← rangeFromTo 1 n
  let dst ← indices.mapM fun i => do
    let interval ← if i < n then oneRange (← sizeAt sz i) else oneRange s
    findin (← getindex I i) interval
  let src ← indices.mapM fun i => do
    let x ← getindex I i
    let interval ← if i < n then oneRange (← sizeAt sz i) else oneRange s
    subindex x (← findin x interval)
  return (← toVector dst, ← toVector src)

/--
Julia source: base/genericmemory.jl:416-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex_atomic(mem::GenericMemory, order::Symbol, i::Int)
    @_propagate_inbounds_meta
    memref = memoryref(mem, i)
    return memoryrefget(memref, order, @_boundscheck)
end

```
-/
def getindexAtomic {m : Type → Type} [Monad m] {M P V : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (memoryrefGet : GenericMemoryRef M P → MemoryOrder → Bool → m V) (boundsChecking : Bool)
    (mem : M) (order : MemoryOrder) (i : I64) : m V := do
  let memref ← memoryrefAt mem i
  memoryrefGet memref order boundsChecking

/--
Julia source: base/genericmemory.jl:422-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex_atomic!(mem::GenericMemory, order::Symbol, val, i::Int)
    @_propagate_inbounds_meta
    T = eltype(mem)
    memref = memoryref(mem, i)
    return memoryrefset!(
        memref,
        val isa T ? val : convert(T, val)::T,
        order,
        @_boundscheck
    )
end
```
-/
def setindexAtomic {m : Type → Type} [Monad m] {M P T V R : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (castElement : V → Option T) (convert : V → m T)
    (memoryrefSet : GenericMemoryRef M P → T → MemoryOrder → Bool → m R) (boundsChecking : Bool)
    (mem : M) (order : MemoryOrder) (val : V) (i : I64) : m R := do
  let memref ← memoryrefAt mem i
  let stored ← match castElement val with | some v => pure v | none => convert val
  memoryrefSet memref stored order boundsChecking

/--
Julia source: base/genericmemory.jl:434-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindexonce_atomic!(
    mem::GenericMemory,
    success_order::Symbol,
    fail_order::Symbol,
    val,
    i::Int,
)
    @_propagate_inbounds_meta
    T = eltype(mem)
    memref = memoryref(mem, i)
    return Core.memoryrefsetonce!(
        memref,
        val isa T ? val : convert(T, val)::T,
        success_order,
        fail_order,
        @_boundscheck
    )
end
```
-/
def setindexonceAtomic {m : Type → Type} [Monad m] {M P T V R : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (castElement : V → Option T) (convert : V → m T)
    (memoryrefSetOnce : GenericMemoryRef M P → T → MemoryOrder → MemoryOrder → Bool → m R)
    (boundsChecking : Bool) (mem : M) (successOrder failOrder : MemoryOrder) (val : V) (i : I64) : m R := do
  let memref ← memoryrefAt mem i
  let stored ← match castElement val with | some v => pure v | none => convert val
  memoryrefSetOnce memref stored successOrder failOrder boundsChecking

/--
Julia source: base/genericmemory.jl:453-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modifyindex_atomic!(mem::GenericMemory, order::Symbol, op, val, i::Int)
    @_propagate_inbounds_meta
    memref = memoryref(mem, i)
    return Core.memoryrefmodify!(memref, op, val, order, @_boundscheck)
end
```
-/
def modifyindexAtomic {m : Type → Type} [Monad m] {M P Op V R : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (memoryrefModify : GenericMemoryRef M P → Op → V → MemoryOrder → Bool → m R)
    (boundsChecking : Bool) (mem : M) (order : MemoryOrder) (op : Op) (val : V) (i : I64) : m R := do
  let memref ← memoryrefAt mem i
  memoryrefModify memref op val order boundsChecking

/--
Julia source: base/genericmemory.jl:459-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function swapindex_atomic!(mem::GenericMemory, order::Symbol, val, i::Int)
    @_propagate_inbounds_meta
    T = eltype(mem)
    memref = memoryref(mem, i)
    return Core.memoryrefswap!(
        memref,
        val isa T ? val : convert(T, val)::T,
        order,
        @_boundscheck
    )
end
```
-/
def swapindexAtomic {m : Type → Type} [Monad m] {M P T V R : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (castElement : V → Option T) (convert : V → m T)
    (memoryrefSwap : GenericMemoryRef M P → T → MemoryOrder → Bool → m R) (boundsChecking : Bool)
    (mem : M) (order : MemoryOrder) (val : V) (i : I64) : m R := do
  let memref ← memoryrefAt mem i
  let stored ← match castElement val with | some v => pure v | none => convert val
  memoryrefSwap memref stored order boundsChecking

/--
Julia source: base/genericmemory.jl:471-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replaceindex_atomic!(
    mem::GenericMemory,
    success_order::Symbol,
    fail_order::Symbol,
    expected,
    desired,
    i::Int,
)
    @_propagate_inbounds_meta
    T = eltype(mem)
    memref = memoryref(mem, i)
    return Core.memoryrefreplace!(
        memref,
        expected,
        desired isa T ? desired : convert(T, desired)::T,
        success_order,
        fail_order,
        @_boundscheck,
    )
end
```
-/
def replaceindexAtomic {m : Type → Type} [Monad m] {M P T E V R : Type}
    (memoryrefAt : M → I64 → m (GenericMemoryRef M P))
    (castElement : V → Option T) (convert : V → m T)
    (memoryrefReplace : GenericMemoryRef M P → E → T → MemoryOrder → MemoryOrder → Bool → m R)
    (boundsChecking : Bool) (mem : M) (successOrder failOrder : MemoryOrder) (expected : E)
    (desired : V) (i : I64) : m R := do
  let memref ← memoryrefAt mem i
  let newval ← match castElement desired with | some v => pure v | none => convert desired
  memoryrefReplace memref expected newval successOrder failOrder boundsChecking

end JuliaLean.base.genericmemory
