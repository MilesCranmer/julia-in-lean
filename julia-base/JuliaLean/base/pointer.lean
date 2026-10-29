import JuliaLean.Core
import JuliaLean.base.genericmemory

/-!
# Typed model of `base/pointer.jl`

Pointer values carry a Julia element type and a 64-bit address. `ByteHeap` stores the address
space one byte at a time; `ByteCodec` gives each element type its byte layout. A `WrappedArray`
or `WrappedMemory` keeps the original pointer, so every access goes through the same heap.
Runtime conversions and Julia's generic dispatch remain typed inputs where their definitions live
in other Base files or in the runtime.
-/

namespace JuliaLean.base.pointer

open JuliaLean JuliaLean.base.genericmemory

abbrev U64 := JInt .u64
abbrev I64 := JInt .i64
abbrev Byte := JInt .u8

inductive PointerError where
  | julia (error : JlError)
  | errorException (message : String)
  | methodError (functionName : String)
  deriving DecidableEq, Repr

abbrev PtrResult (α : Type) := Except PointerError α

def u64 (n : Int) : U64 := JInt.lit .u64 n
def i64 (n : Int) : I64 := JInt.lit .i64 n
def oneI64 : I64 := i64 1

def int64ToUInt64 (value : I64) : U64 := JInt.wrap .u64 value.val

/--
Julia source: base/pointer.jl:3-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Ptr{T}

A memory address referring to data of type `T`.  However, there is no guarantee that the
memory is actually valid, or that it actually represents data of the specified type.
"""
Ptr
```
-/
structure Ptr (T : Type) where
  address : U64


/--
Julia source: base/pointer.jl:13-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    C_NULL

The C null pointer constant, sometimes used when calling external code.
"""
const C_NULL = bitcast(Ptr{Cvoid}, 0)
```
-/
def C_NULL : Ptr Unit := ⟨u64 0⟩

/-- A native Julia `Int` or `UInt`, the only integer input types of `Ptr{T}(x)`. -/
inductive NativeInt where
  | signed (value : I64)
  | unsigned (value : U64)

def NativeInt.toUInt64 : NativeInt → U64
  | .signed value => int64ToUInt64 value
  | .unsigned value => value

def convertPtrToInteger {T I : Type} (toInteger : U64 → PtrResult I)
    (pointer : Ptr T) : PtrResult I :=
  toInteger pointer.address

def convertIntegerToPtr {T : Type} (value : NativeInt) : Ptr T :=
  ⟨value.toUInt64⟩

/-- `convert(Ptr{T}, p::Ptr{T})`: the pointer value is unchanged. -/
def convertPtrSame {T : Type} (pointer : Ptr T) : Ptr T := pointer

/-- `convert(Ptr{T}, p::Ptr)` for a different element type preserves the address bits. -/
def convertPtrType {S T : Type} (pointer : Ptr T) : Ptr S := ⟨pointer.address⟩

def convertPtrDispatch {S T : Type} (sameType : Decidable (S = T))
    (pointer : Ptr T) : Ptr S :=
  match sameType with
  | .isTrue h =>
      convertPtrSame (cast (congrArg (fun A => Ptr A) h.symm) pointer)
  | .isFalse _ => convertPtrType pointer

/-- The interned symbol's NUL-terminated name pointer. -/
structure PointerSymbol where
  namePointer : Ptr Byte

/--
Julia source: base/pointer.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::Ptr) where {T<:Integer} = T(UInt(x))::T
```
-/
def convertPtrToIntegerMethod {T I : Type} (toInteger : U64 → PtrResult I)
    (pointer : Ptr T) : PtrResult I := convertPtrToInteger toInteger pointer

/--
Julia source: base/pointer.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ptr{T}}, x::Union{Int,UInt}) where {T} = Ptr{T}(x)
```
-/
def convertIntegerToPtrMethod {T : Type} (value : NativeInt) : Ptr T := convertIntegerToPtr value

/--
Julia source: base/pointer.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ptr{T}}, p::Ptr{T}) where {T} = p
```
-/
def convertSamePtrMethod {T : Type} (pointer : Ptr T) : Ptr T := convertPtrSame pointer

/--
Julia source: base/pointer.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ptr{T}}, p::Ptr) where {T} = bitcast(Ptr{T}, p)::Ptr{T}
```
-/
def convertDifferentPtrMethod {S T : Type} (pointer : Ptr T) : Ptr S := convertPtrType pointer


/-- Memory metadata used to resolve a `GenericMemoryRef` pointer or element offset. -/
structure PointerMemoryObject (T : Type) where
  ptr : Ptr Unit
  arrayElement : Nat
  layoutBytes : I64

abbrev PointerMemoryRef (T : Type) := GenericMemoryRef (PointerMemoryObject T) U64

/-- A pointer-compatible view of an array argument. -/
inductive AbstractArrayPointerInput (T : Type) where
  | array (reference : PointerMemoryRef T)
  | other (typeName : String)

/--
Julia source: base/pointer.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{UInt8}}, s::AbstractString) = String(s)
```
-/
def cconvertStringUInt8 {S : Type} (toString : S → String) (s : S) : String := toString s

/--
Julia source: base/pointer.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{Int8}}, s::AbstractString) = String(s)
```
-/
def cconvertStringInt8 {S : Type} (toString : S → String) (s : S) : String := toString s

/--
Julia source: base/pointer.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{UInt8}}, x::Symbol) = ccall(:jl_symbol_name, Ptr{UInt8}, (Any,), x)
```
-/
def unsafeConvertSymbolUInt8 (symbolName : PointerSymbol → Ptr Byte) (x : PointerSymbol) : Ptr Byte :=
  symbolName x

/--
Julia source: base/pointer.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Int8}}, x::Symbol) = ccall(:jl_symbol_name, Ptr{Int8}, (Any,), x)
```
-/
def unsafeConvertSymbolInt8 (symbolName : PointerSymbol → Ptr Byte) (x : PointerSymbol) : Ptr (JInt .i8) :=
  convertPtrType (symbolName x)

/--
Julia source: base/pointer.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{<:Ptr}, a::Array) = getfield(a, :ref)
```
-/
def cconvertArray {A R : Type} (getRef : A → R) (array : A) : R := getRef array

/--
Julia source: base/pointer.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{<:Ptr}, a::GenericMemory) = a
```
-/
def cconvertGenericMemory {M : Type} (memory : M) : M := memory

/--
Julia source: base/pointer.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Cvoid}}, a::GenericMemory{T}) where {T} = getfield(a, :ptr)
```
-/
def unsafeConvertMemoryCvoid {T : Type} (memory : PointerMemoryObject T) : Ptr Unit :=
  memory.ptr

/--
Julia source: base/pointer.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::GenericMemory) where {T} = convert(Ptr{T}, getfield(a, :ptr))
```
-/
def unsafeConvertMemory {T S : Type} (memory : PointerMemoryObject T) : Ptr S :=
  convertPtrType (unsafeConvertMemoryCvoid memory)

/--
Julia source: base/pointer.jl:75-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{Cvoid}}, a::GenericMemoryRef{<:Any,T,Core.CPU}) where {T}
    mem = getfield(a, :mem)
    offset = getfield(a, :ptr_or_offset)
    MemT = typeof(mem)
    arrayelem = datatype_arrayelem(MemT)
    elsz = datatype_layoutsize(MemT)
    isunion = 2
    if arrayelem == isunion || elsz == 0
        offset = UInt(offset) * elsz
        offset += unsafe_convert(Ptr{Cvoid}, mem)
    end
    return offset
end
```
-/
def unsafeConvertMemoryRefCvoid {T : Type} (reference : PointerMemoryRef T) : Ptr Unit := Id.run do
  let mem := reference.mem
  let offset := reference.ptr_or_offset
  let arrayelem := mem.arrayElement
  let elsz := mem.layoutBytes
  let isunion := 2
  if arrayelem == isunion || elsz.val == 0 then
    let byteOffset := offset * int64ToUInt64 elsz
    return ⟨mem.ptr.address + byteOffset⟩
  return ⟨offset⟩

/--
Julia source: base/pointer.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::GenericMemoryRef) where {T} = convert(Ptr{T}, unsafe_convert(Ptr{Cvoid}, a))
```
-/
def unsafeConvertMemoryRef {T S : Type} (reference : PointerMemoryRef T) : Ptr S :=
  convertPtrType (unsafeConvertMemoryRefCvoid reference)

/--
Julia source: base/pointer.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::Array{T}) where {T} = unsafe_convert(Ptr{T}, a.ref)
```
-/
def unsafeConvertArray {T : Type} (reference : PointerMemoryRef T) : Ptr T :=
  unsafeConvertMemoryRef reference

/--
Julia source: base/pointer.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{T}}, a::AbstractArray{T}) where {T} = error("conversion to pointer not defined for $(typeof(a))")
```
-/
def unsafeConvertUnsupportedArray {T : Type} (typeName : String) : PtrResult (Ptr T) :=
  .error (.errorException ("conversion to pointer not defined for " ++ typeName))

def unsafeConvertPtrArray {T : Type} : AbstractArrayPointerInput T → PtrResult (Ptr T)
  | .array reference => .ok (unsafeConvertArray reference)
  | .other typeName => unsafeConvertUnsupportedArray typeName

/--
Julia source: base/pointer.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{S}}, a::AbstractArray{T}) where {S,T} = convert(Ptr{S}, unsafe_convert(Ptr{T}, a))
```
-/
def unsafeConvertAbstractArray {S T : Type} (sameType : Decidable (S = T))
    (array : AbstractArrayPointerInput T) : PtrResult (Ptr S) := do
  let typed ← unsafeConvertPtrArray array
  pure (convertPtrDispatch sameType typed)



/-- The bytes of a Julia value are stored at addresses in a typed byte heap. -/
structure ByteHeap where
  byteAt : Nat → Byte
  validByte : Nat → Bool

/-- Address arithmetic in the heap wraps in the 64-bit pointer address space. -/
def addressMod (address : Nat) : Nat := address % 2 ^ 64

def ByteHeap.readByte (heap : ByteHeap) (address : Nat) : Byte :=
  heap.byteAt (addressMod address)

def ByteHeap.writeByte (heap : ByteHeap) (address : Nat) (value : Byte) : ByteHeap :=
  { heap with byteAt := fun location =>
      if addressMod location == addressMod address then value else heap.byteAt location }

def ByteHeap.readBytes (heap : ByteHeap) (address size : Nat) : List Byte :=
  (List.range size).map (fun offset => heap.readByte (address + offset))

def ByteHeap.writeBytes (heap : ByteHeap) (address : Nat) : List Byte → ByteHeap
  | [] => heap
  | value :: rest => (heap.writeByte address value).writeBytes (address + 1) rest

def ByteHeap.validRange (heap : ByteHeap) (address size : Nat) : Prop :=
  ∀ offset, offset < size → heap.validByte (addressMod (address + offset)) = true

/-- The typed byte representation used by loads, stores, and pointer-backed views. -/
structure ByteCodec (T : Type) where
  elementSize : I64
  size_nonnegative : 0 ≤ elementSize.val
  encode : T → List Byte
  decode : List Byte → T
  encode_length : ∀ value, (encode value).length = elementSize.val.toNat
  decode_encode : ∀ value, decode (encode value) = value

/-- Add a byte offset to a pointer, wrapping at the native address width. -/
def addPtrBytes {T : Type} (pointer : Ptr T) (offset : U64) : Ptr T :=
  ⟨pointer.address + offset⟩

/-- Subtract a byte offset from a pointer, wrapping at the native address width. -/
def subPtrBytes {T : Type} (pointer : Ptr T) (offset : U64) : Ptr T :=
  ⟨pointer.address - offset⟩

/-- The address selected by `pointerref` and `pointerset`: `(i - 1) * sizeof(T)` bytes. -/
def indexedPointer {T : Type} (codec : ByteCodec T) (pointer : Ptr T) (index : I64) : Ptr T :=
  let byteOffset := codec.elementSize * (index - oneI64)
  addPtrBytes pointer (int64ToUInt64 byteOffset)

def pointerRef {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (index _alignment : I64) : T :=
  codec.decode (heap.readBytes (indexedPointer codec pointer index).address.val.toNat
    codec.elementSize.val.toNat)

def pointerSet {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (value : T) (index _alignment : I64) : ByteHeap × Ptr T :=
  (heap.writeBytes (indexedPointer codec pointer index).address.val.toNat (codec.encode value), pointer)

/-- An array or memory view stores a pointer, so reads and writes use the same `ByteHeap`. -/
structure TupleN (α : Type) (n : Nat) where
  values : List α
  length_eq : values.length = n

def TupleN.one {α : Type} (value : α) : TupleN α 1 := ⟨[value], rfl⟩

def TupleN.first {α : Type} (tuple : TupleN α 1) : α :=
  tuple.values[0]'(by rw [tuple.length_eq]; omega)

structure WrappedArray (T : Type) (N : Nat) where
  pointer : Ptr T
  dims : TupleN I64 N
  owns : Bool

structure WrappedMemory (T : Type) where
  pointer : Ptr T
  length : U64
  kind : MemoryKind
  owns : Bool

inductive WrappedView (T : Type) (N : Nat) where
  | array (view : WrappedArray T N)
  | memory (view : WrappedMemory T)

inductive WrapTarget (T : Type) (N : Nat) where
  | array
  | memory (kind : MemoryKind)

/--
Julia source: base/pointer.jl:91-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_wrap(Array, pointer::Ptr{T}, dims; own = false)

Wrap a Julia `Array` object around the data at the address given by `pointer`,
without making a copy.  The pointer element type `T` determines the array
element type. `dims` is either an integer (for a 1d array) or a tuple of the array dimensions.
`own` optionally specifies whether Julia should take ownership of the memory,
calling `free` on the pointer when the array is no longer referenced.

This function is labeled "unsafe" because it will crash if `pointer` is not
a valid memory address to data of the requested length. Unlike [`unsafe_load`](@ref)
and [`unsafe_store!`](@ref), the programmer is responsible also for ensuring that the
underlying data is not accessed through two arrays of different element type, similar
to the strict aliasing rule in C.
"""
function unsafe_wrap(::Union{Type{Array},Type{Array{T}},Type{Array{T,N}}},
                     p::Ptr{T}, dims::NTuple{N,Int}; own::Bool = false) where {T,N}
    ccall(:jl_ptr_to_array, Array{T,N}, (Any, Ptr{Cvoid}, Any, Int32),
          Array{T,N}, p, dims, own)
end
```
-/
def unsafeWrapArrayTuple {T : Type} {N : Nat} (pointer : Ptr T) (dims : TupleN I64 N)
    (own : Bool := false) : WrappedArray T N := ⟨pointer, dims, own⟩

/--
Julia source: base/pointer.jl:111-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_wrap(::Union{Type{Array},Type{Array{T}},Type{Array{T,1}}},
                     p::Ptr{T}, d::Integer; own::Bool = false) where {T}
    ccall(:jl_ptr_to_array_1d, Array{T,1},
          (Any, Ptr{Cvoid}, Csize_t, Cint), Array{T,1}, p, d, own)
end
```
-/
def unsafeWrapArrayInteger {T I : Type} (pointer : Ptr T) (dimension : I)
    (toSize : I → U64) (own : Bool := false) : WrappedArray T 1 :=
  unsafeWrapArrayTuple pointer (TupleN.one (i64 (toSize dimension).val)) own

/--
Julia source: base/pointer.jl:116-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_wrap(::Union{Type{GenericMemory{kind,<:Any,Core.CPU}},Type{GenericMemory{kind,T,Core.CPU}}},
                     p::Ptr{T}, dims::Tuple{Int}; own::Bool = false) where {kind,T}
    ccall(:jl_ptr_to_genericmemory, Ref{GenericMemory{kind,T,Core.CPU}},
          (Any, Ptr{Cvoid}, Csize_t, Cint), GenericMemory{kind,T,Core.CPU}, p, dims[1], own)
end
```
-/
def unsafeWrapMemoryTuple {T : Type} (kind : MemoryKind) (pointer : Ptr T)
    (dims : TupleN I64 1) (own : Bool := false) : WrappedMemory T :=
  ⟨pointer, int64ToUInt64 dims.first, kind, own⟩

/--
Julia source: base/pointer.jl:121-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_wrap(::Union{Type{GenericMemory{kind,<:Any,Core.CPU}},Type{GenericMemory{kind,T,Core.CPU}}},
                     p::Ptr{T}, d::Integer; own::Bool = false) where {kind,T}
    ccall(:jl_ptr_to_genericmemory, Ref{GenericMemory{kind,T,Core.CPU}},
          (Any, Ptr{Cvoid}, Csize_t, Cint), GenericMemory{kind,T,Core.CPU}, p, d, own)
end
```
-/
def unsafeWrapMemoryInteger {T I : Type} (kind : MemoryKind) (pointer : Ptr T)
    (dimension : I) (toSize : I → U64) (own : Bool := false) : WrappedMemory T :=
  ⟨pointer, toSize dimension, kind, own⟩

/--
Julia source: base/pointer.jl:126-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(Atype::Union{Type{Array},Type{Array{T}},Type{Array{T,N}},Type{GenericMemory{kind,<:Any,Core.CPU}},Type{GenericMemory{kind,T,Core.CPU}}} where {kind},
            p::Ptr{T}, dims::NTuple{N,<:Integer}; own::Bool = false) where {T,N} =
    unsafe_wrap(Atype, p, convert(Tuple{Vararg{Int}}, dims), own = own)
```
-/
def unsafeWrapGenericDims {T I : Type} {N : Nat} (target : WrapTarget T N)
    (convertDims : TupleN I N → PtrResult (TupleN I64 N))
    (pointer : Ptr T) (dims : TupleN I N) (own : Bool := false) : PtrResult (WrappedView T N) := do
  let dimensions ← convertDims dims
  match target with
  | .array => pure (.array (unsafeWrapArrayTuple pointer dimensions own))
  | .memory kind =>
      if h : N = 1 then
        let oneDim : TupleN I64 1 := h ▸ dimensions
        pure (.memory (unsafeWrapMemoryTuple kind pointer oneDim own))
      else
        .error (.methodError "unsafe_wrap")

/--
Julia source: base/pointer.jl:131-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_load(p::Ptr{T}, i::Integer=1)
    unsafe_load(p::Ptr{T}, order::Symbol)
    unsafe_load(p::Ptr{T}, i::Integer, order::Symbol)

Load a value of type `T` from the address of the `i`th element (1-indexed) starting at `p`.
This is equivalent to the C expression `p[i-1]`. Optionally, an atomic memory ordering can
be provided.

The `unsafe` prefix on this function indicates that no validation is performed on the
pointer `p` to ensure that it is valid. Like C, the programmer is responsible for ensuring
that referenced memory is not freed or garbage collected while invoking this function.
Incorrect usage may segfault your program or return garbage answers. Unlike C, dereferencing
memory region allocated as different type may be valid provided that the types are compatible.

!!! compat "Julia 1.10"
     The `order` argument is available as of Julia 1.10.

See also: [`atomic`](@ref)
"""
unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
```
-/
def unsafeLoad {T I : Type} [OfNat I 1] (codec : ByteCodec T) (toInt : I → PtrResult I64)
    (pointer : Ptr T) (heap : ByteHeap) (index : I := 1) : PtrResult T := do
  let i ← toInt index
  pure (pointerRef codec heap pointer i oneI64)

def atomicPointerRef {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (_order : MemoryOrder) : T := pointerRef codec heap pointer oneI64 oneI64
/--
Julia source: base/pointer.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_load(p::Ptr, order::Symbol) = atomic_pointerref(p, order)
```
-/

def unsafeLoadAtomic {T : Type} (codec : ByteCodec T) (pointer : Ptr T) (heap : ByteHeap)
    (order : MemoryOrder) : PtrResult T := .ok (atomicPointerRef codec heap pointer order)

/--
Julia source: base/pointer.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Ptr, y::Integer) = add_ptr(x, (y % UInt) % UInt)
```
-/
def ptrAddInteger {T I : Type} (toUInt : I → U64) (pointer : Ptr T) (offset : I) : Ptr T :=
  addPtrBytes pointer (toUInt offset)

def ptrAddI64 {T : Type} (pointer : Ptr T) (offset : I64) : Ptr T :=
  ptrAddInteger int64ToUInt64 pointer offset

/--
Julia source: base/pointer.jl:153-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_load(p::Ptr, i::Integer, order::Symbol)
    unsafe_load(p + (elsize(typeof(p)) * (Int(i) - 1)), order)
end
```
-/
def unsafeLoadAtomicIndex {T I : Type} (codec : ByteCodec T) (toInt : I → PtrResult I64)
    (pointer : Ptr T) (heap : ByteHeap) (index : I) (order : MemoryOrder) : PtrResult T := do
  let i ← toInt index
  let byteOffset := codec.elementSize * (i - oneI64)
  unsafeLoadAtomic codec (ptrAddI64 pointer byteOffset) heap order

/-- The atomic pointer operations are one typed read or write of the byte heap. -/
def atomicPointerSet {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (value : T) (_order : MemoryOrder) : ByteHeap × Ptr T :=
  pointerSet codec heap pointer value oneI64 oneI64

def atomicPointerSwap {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (value : T) (_order : MemoryOrder) : ByteHeap × T :=
  let old := pointerRef codec heap pointer oneI64 oneI64
  let (heap', _) := atomicPointerSet codec heap pointer value .notAtomic
  (heap', old)

def atomicPointerModify {T X : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
    (operation : T → X → T) (value : X) (_order : MemoryOrder) : ByteHeap × (T × T) :=
  let old := pointerRef codec heap pointer oneI64 oneI64
  let new := operation old value
  let (heap', _) := atomicPointerSet codec heap pointer new .notAtomic
  (heap', (old, new))

structure ReplaceResult (T : Type) where
  old : T
  success : Bool
  deriving Repr

def atomicPointerReplace {T E : Type} (codec : ByteCodec T) (same : T → E → Bool)
    (heap : ByteHeap) (pointer : Ptr T) (expected : E) (desired : T)
    (_successOrder _failOrder : MemoryOrder) : ByteHeap × ReplaceResult T :=
  let old := pointerRef codec heap pointer oneI64 oneI64
  if same old expected then
    let (heap', _) := atomicPointerSet codec heap pointer desired .notAtomic
    (heap', ⟨old, true⟩)
  else
    (heap, ⟨old, false⟩)

/--
Julia source: base/pointer.jl:157-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_store!(p::Ptr{T}, x, i::Integer=1)
    unsafe_store!(p::Ptr{T}, x, order::Symbol)
    unsafe_store!(p::Ptr{T}, x, i::Integer, order::Symbol)

Store a value of type `T` to the address of the `i`th element (1-indexed) starting at `p`.
This is equivalent to the C expression `p[i-1] = x`. Optionally, an atomic memory ordering
can be provided.

The `unsafe` prefix on this function indicates that no validation is performed on the
pointer `p` to ensure that it is valid. Like C, the programmer is responsible for ensuring
that referenced memory is not freed or garbage collected while invoking this function.
Incorrect usage may segfault your program. Unlike C, storing memory region allocated as
different type may be valid provided that the types are compatible.

!!! compat "Julia 1.10"
     The `order` argument is available as of Julia 1.10.

See also: [`atomic`](@ref)
"""
unsafe_store!(p::Ptr{Any}, @nospecialize(x), i::Integer=1) = pointerset(p, x, Int(i), 1)
```
-/
def unsafeStoreAny {T I : Type} [OfNat I 1] (codec : ByteCodec T) (toInt : I → PtrResult I64)
    (pointer : Ptr T) (heap : ByteHeap) (value : T) (index : I := 1) : PtrResult (ByteHeap × Ptr T) := do
  let i ← toInt index
  pure (pointerSet codec heap pointer value i oneI64)

/--
Julia source: base/pointer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_store!(p::Ptr{T}, x, i::Integer=1) where {T} = pointerset(p, convert(T,x), Int(i), 1)
```
-/
def unsafeStoreTyped {T V I : Type} [OfNat I 1] (codec : ByteCodec T)
    (convert : V → PtrResult T) (toInt : I → PtrResult I64)
    (pointer : Ptr T) (heap : ByteHeap) (value : V) (index : I := 1) : PtrResult (ByteHeap × Ptr T) := do
  let converted ← convert value
  let i ← toInt index
  pure (pointerSet codec heap pointer converted i oneI64)

/--
Julia source: base/pointer.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_store!(p::Ptr{T}, x, order::Symbol) where {T} = atomic_pointerset(p, x isa T ? x : convert(T,x), order)
```
-/
def unsafeStoreAtomic {T V : Type} (codec : ByteCodec T) (cast : V → Option T)
    (convert : V → PtrResult T) (pointer : Ptr T) (heap : ByteHeap) (value : V)
    (order : MemoryOrder) : PtrResult (ByteHeap × Ptr T) := do
  let converted ← match cast value with
    | some typed => pure typed
    | none => convert value
  pure (atomicPointerSet codec heap pointer converted order)

/--
Julia source: base/pointer.jl:180-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_store!(p::Ptr, x, i::Integer, order::Symbol)
    unsafe_store!(p + (elsize(typeof(p)) * (Int(i) - 1)), x, order)
end
```
-/
def unsafeStoreAtomicIndex {T V I : Type} (codec : ByteCodec T) (cast : V → Option T)
    (convert : V → PtrResult T) (toInt : I → PtrResult I64)
    (pointer : Ptr T) (heap : ByteHeap) (value : V) (index : I) (order : MemoryOrder) :
    PtrResult (ByteHeap × Ptr T) := do
  let i ← toInt index
  let byteOffset := codec.elementSize * (i - oneI64)
  unsafeStoreAtomic codec cast convert (ptrAddI64 pointer byteOffset) heap value order

/--
Julia source: base/pointer.jl:184-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_modify!(p::Ptr{T}, op, x, [order::Symbol])::Pair

These atomically perform the operations to get and set a memory address after applying
the function `op`. If supported by the hardware (for example, atomic increment), this may be
optimized to the appropriate hardware instruction, otherwise its execution will be
similar to:

    y = unsafe_load(p)
    z = op(y, x)
    unsafe_store!(p, z)
    return y => z

The `unsafe` prefix on this function indicates that no validation is performed on the
pointer `p` to ensure that it is valid. Like C, the programmer is responsible for ensuring
that referenced memory is not freed or garbage collected while invoking this function.
Incorrect usage may segfault your program.

!!! compat "Julia 1.10"
     This function requires at least Julia 1.10.

See also: [`modifyproperty!`](@ref Base.modifyproperty!), [`atomic`](@ref)
"""
function unsafe_modify!(p::Ptr, op, x, order::Symbol=:not_atomic)
    return atomic_pointermodify(p, op, x, order)
end
```
-/
def unsafeModify {T X : Type} (codec : ByteCodec T) (pointer : Ptr T) (heap : ByteHeap)
    (operation : T → X → T) (value : X) (order : MemoryOrder := .notAtomic) :
    ByteHeap × (T × T) :=
  atomicPointerModify codec heap pointer operation value order

/--
Julia source: base/pointer.jl:211-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_replace!(p::Ptr{T}, expected, desired,
                   [success_order::Symbol[, fail_order::Symbol=success_order]]) -> (; old, success::Bool)

These atomically perform the operations to get and conditionally set a memory address to
a given value. If supported by the hardware, this may be optimized to the appropriate
hardware instruction, otherwise its execution will be similar to:

    y = unsafe_load(p, fail_order)
    ok = y === expected
    if ok
        unsafe_store!(p, desired, success_order)
    end
    return (; old = y, success = ok)

The `unsafe` prefix on this function indicates that no validation is performed on the
pointer `p` to ensure that it is valid. Like C, the programmer is responsible for ensuring
that referenced memory is not freed or garbage collected while invoking this function.
Incorrect usage may segfault your program.

!!! compat "Julia 1.10"
     This function requires at least Julia 1.10.

See also: [`replaceproperty!`](@ref Base.replaceproperty!), [`atomic`](@ref)
"""
function unsafe_replace!(p::Ptr{T}, expected, desired, success_order::Symbol=:not_atomic, fail_order::Symbol=success_order) where {T}
    @inline
    xT = desired isa T ? desired : convert(T, desired)
    return atomic_pointerreplace(p, expected, xT, success_order, fail_order)
end
```
-/
def unsafeReplaceTyped {T E V : Type} (codec : ByteCodec T) (same : T → E → Bool)
    (cast : V → Option T) (convert : V → PtrResult T) (pointer : Ptr T) (heap : ByteHeap)
    (expected : E) (desired : V) (successOrder : MemoryOrder := .notAtomic)
    (failOrder : MemoryOrder := successOrder) : PtrResult (ByteHeap × ReplaceResult T) := do
  let typed ← match cast desired with
    | some value => pure value
    | none => convert desired
  pure (atomicPointerReplace codec same heap pointer expected typed successOrder failOrder)

/--
Julia source: base/pointer.jl:241-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_replace!(p::Ptr{Any}, @nospecialize(expected), @nospecialize(desired), success_order::Symbol=:not_atomic, fail_order::Symbol=success_order)
    return atomic_pointerreplace(p, expected, desired, success_order, fail_order)
end
```
-/
def unsafeReplaceAny {T : Type} (codec : ByteCodec T) (same : T → T → Bool)
    (pointer : Ptr T) (heap : ByteHeap) (expected desired : T)
    (successOrder : MemoryOrder := .notAtomic) (failOrder : MemoryOrder := successOrder) :
    ByteHeap × ReplaceResult T :=
  atomicPointerReplace codec same heap pointer expected desired successOrder failOrder

/--
Julia source: base/pointer.jl:245-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_swap!(p::Ptr{T}, x, [order::Symbol])

These atomically perform the operations to simultaneously get and set a memory address.
If supported by the hardware, this may be optimized to the appropriate hardware
instruction, otherwise its execution will be similar to:

    y = unsafe_load(p)
    unsafe_store!(p, x)
    return y

The `unsafe` prefix on this function indicates that no validation is performed on the
pointer `p` to ensure that it is valid. Like C, the programmer is responsible for ensuring
that referenced memory is not freed or garbage collected while invoking this function.
Incorrect usage may segfault your program.

!!! compat "Julia 1.10"
     This function requires at least Julia 1.10.

See also: [`swapproperty!`](@ref Base.swapproperty!), [`atomic`](@ref)
"""
function unsafe_swap!(p::Ptr{Any}, x, order::Symbol=:not_atomic)
    return atomic_pointerswap(p, x, order)
end
```
-/
def unsafeSwapAny {T : Type} (codec : ByteCodec T) (pointer : Ptr T) (heap : ByteHeap)
    (value : T) (order : MemoryOrder := .notAtomic) : ByteHeap × T :=
  atomicPointerSwap codec heap pointer value order

/--
Julia source: base/pointer.jl:269-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_swap!(p::Ptr{T}, x, order::Symbol=:not_atomic) where {T}
    @inline
    xT = x isa T ? x : convert(T, x)
    return atomic_pointerswap(p, xT, order)
end
```
-/
def unsafeSwapTyped {T V : Type} (codec : ByteCodec T) (cast : V → Option T)
    (convert : V → PtrResult T) (pointer : Ptr T) (heap : ByteHeap) (value : V)
    (order : MemoryOrder := .notAtomic) : PtrResult (ByteHeap × T) := do
  let typed ← match cast value with
    | some item => pure item
    | none => convert value
  pure (atomicPointerSwap codec heap pointer typed order)

/--
Julia source: base/pointer.jl:276-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    unsafe_pointer_to_objref(p::Ptr)

Convert a `Ptr` to an object reference. Assumes the pointer refers to a valid heap-allocated
Julia object. If this is not the case, undefined behavior results, hence this function is
considered "unsafe" and should be used with care.

See also [`pointer_from_objref`](@ref).
"""
unsafe_pointer_to_objref(x::Ptr) = ccall(:jl_value_ptr, Any, (Ptr{Cvoid},), x)
```
-/
def unsafePointerToObjref {T A : Type} (objectFromPointer : Ptr Unit → A) (pointer : Ptr T) : A :=
  objectFromPointer (convertPtrType pointer)

/--
Julia source: base/pointer.jl:287-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    pointer_from_objref(x)

Get the memory address of a Julia object as a `Ptr`. The existence of the resulting `Ptr`
will not protect the object from garbage collection, so you must ensure that the object
remains referenced for the whole time that the `Ptr` will be used.

This function may not be called on immutable objects, since they do not have
stable memory addresses.

See also [`unsafe_pointer_to_objref`](@ref).
"""
function pointer_from_objref(@nospecialize(x))
    @inline
    ismutable(x) || error("pointer_from_objref cannot be used on immutable objects")
    ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), x)
end
```
-/
def pointerFromObjref {A : Type} (ismutable : A → Bool) (objectAddress : A → Ptr Unit)
    (value : A) : PtrResult (Ptr Unit) :=
  if ismutable value then .ok (objectAddress value)
  else .error (.errorException "pointer_from_objref cannot be used on immutable objects")

/--
Julia source: base/pointer.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(x::Ptr, y::Ptr) = (x === y)
```
-/
def isequalPtr {S T : Type} (typeId : Type → Nat) (left : Ptr S) (right : Ptr T) : Bool :=
  (typeId S == typeId T) && (left.address.val == right.address.val)




/--
Julia source: base/pointer.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::Ptr,  y::Ptr) = UInt(x) < UInt(y)
```
-/
def ptrLess {S T : Type} (left : Ptr S) (right : Ptr T) : Bool :=
  left.address.val < right.address.val

/--
Julia source: base/pointer.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::Ptr{T}, y::Ptr{T}) where {T} = x < y
```
-/
def islessPtr {T : Type} (left right : Ptr T) : Bool := ptrLess left right

/--
Julia source: base/pointer.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Ptr, y::Ptr) = UInt(x) == UInt(y)
```
-/
def ptrEqual {S T : Type} (left : Ptr S) (right : Ptr T) : Bool :=
  left.address.val == right.address.val

/--
Julia source: base/pointer.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Ptr,  y::Ptr) = UInt(x) -% UInt(y)
```
-/
def ptrDifference {S T : Type} (left : Ptr S) (right : Ptr T) : U64 := left.address - right.address

/--
Julia source: base/pointer.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Ptr,  y::Ptr) = UInt(x) -% UInt(y)
```
-/
def ptrDifferenceWrap {S T : Type} (left : Ptr S) (right : Ptr T) : U64 :=
  left.address - right.address



/--
Julia source: base/pointer.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Ptr, y::Integer) = sub_ptr(x, (y % UInt) % UInt)
```
-/
def ptrSubInteger {T I : Type} (toUInt : I → U64) (pointer : Ptr T) (offset : I) : Ptr T :=
  subPtrBytes pointer (toUInt offset)

/--
Julia source: base/pointer.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Integer, y::Ptr) = y + x
```
-/
def ptrAddIntegerLeft {T I : Type} (toUInt : I → U64) (offset : I) (pointer : Ptr T) : Ptr T :=
  ptrAddInteger toUInt pointer offset

/--
Julia source: base/pointer.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::Ptr) = UInt(x)
```
-/
def ptrUnsigned {T : Type} (pointer : Ptr T) : U64 := pointer.address

/--
Julia source: base/pointer.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x::Ptr) = Int(x)
```
-/
def ptrSigned {T : Type} (pointer : Ptr T) : I64 := JInt.wrap .i64 pointer.address.val

end JuliaLean.base.pointer
