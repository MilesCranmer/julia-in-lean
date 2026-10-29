import JuliaLean.base.pointer
import JuliaLean.base.abstractarray
import JuliaLean.base.int
import JuliaLean.Registry.Types

/-!
# Properties of `base/pointer.jl`

Properties describe address-bit conversion, typed byte access, aliasing of pointer-backed views,
and atomic updates. Pointer operations require valid addresses and live backing objects as stated
by the Julia documentation. `pointer(::AbstractArray, i)` and `_memory_offset` are instantiated
from their source-mirrored model in `JuliaLean.base.abstractarray`.
-/

namespace JuliaLean.Proofs.base.pointer

open JuliaLean JuliaLean.base.pointer

abbrev MemoryOrder := JuliaLean.base.genericmemory.MemoryOrder
abbrev MemoryKind := JuliaLean.base.genericmemory.MemoryKind

abbrev ArrayResult (α : Type) := JuliaLean.base.abstractarray.Result α

def pointerU64Result (value : U64) : PtrResult U64 := .ok value
def pointerI64Result (value : I64) : PtrResult I64 := .ok value

def resultI64 (value : I64) : ArrayResult I64 := .ok value

def pointerAddArrayResult {T : Type} (pointer : Ptr T) (offset : I64) : ArrayResult (Ptr T) :=
  .ok (ptrAddI64 pointer offset)

def pointerOffsetSub (left right : I64) : ArrayResult I64 :=
  .ok (JuliaLean.base.int.sub left right)

def pointerOffsetMul (left right : I64) : ArrayResult I64 :=
  .ok (JuliaLean.base.int.mul left right)

def castOrConverted {V T : Type} (cast : V → Option T) (convert : V → PtrResult T)
    (value : V) (typed : T) : Prop :=
  cast value = some typed ∨ (cast value = none ∧ convert value = .ok typed)

/-- Pointer equality and ordering use unsigned address bits; arithmetic wraps at 64 bits. -/
def PointerAddressArithmetic : Prop :=
  (∀ {S T : Type} (left : Ptr S) (right : Ptr T),
    ptrEqual left right = decide (left.address.val = right.address.val)) ∧
  (∀ {S T : Type} (left : Ptr S) (right : Ptr T),
    ptrLess left right = decide (left.address.val < right.address.val)) ∧
  (∀ {S T : Type} (left : Ptr S) (right : Ptr T),
    (ptrDifference left right).val = wrapInt .u64 (left.address.val - right.address.val)) ∧
  (∀ {S T : Type} (left : Ptr S) (right : Ptr T),
    (ptrDifferenceWrap left right).val = wrapInt .u64 (left.address.val - right.address.val)) ∧
  (∀ {T I : Type} (toUInt : I → U64) (pointer : Ptr T) (offset : I),
    (ptrAddInteger toUInt pointer offset).address.val =
      wrapInt .u64 (pointer.address.val + (toUInt offset).val)) ∧
  (∀ {T I : Type} (toUInt : I → U64) (pointer : Ptr T) (offset : I),
    (ptrSubInteger toUInt pointer offset).address.val =
      wrapInt .u64 (pointer.address.val - (toUInt offset).val)) ∧
  (∀ {T I : Type} (toUInt : I → U64) (offset : I) (pointer : Ptr T),
    ptrAddIntegerLeft toUInt offset pointer = ptrAddInteger toUInt pointer offset) ∧
  (∀ {T : Type} (pointer : Ptr T), ptrUnsigned pointer = pointer.address) ∧
  (∀ {T : Type} (pointer : Ptr T),
    (ptrSigned pointer).val = wrapInt .i64 pointer.address.val) ∧
  (∀ {S T : Type} (typeId : Type → Nat) (left : Ptr S) (right : Ptr T),
    isequalPtr typeId left right =
      ((typeId S == typeId T) && (left.address.val == right.address.val)))

/-- Converting between `Ptr` and native integers preserves the 64 address bits. -/
def PointerIntegerConversions : Prop :=
  (∀ {T : Type} (pointer : Ptr T),
    convertPtrToIntegerMethod pointerU64Result pointer = .ok pointer.address) ∧
  (∀ {T : Type} (value : NativeInt),
    (convertIntegerToPtrMethod (T := T) value).address = value.toUInt64) ∧
  (∀ {T : Type} (pointer : Ptr T), convertSamePtrMethod pointer = pointer) ∧
  (∀ {S T : Type} (pointer : Ptr T),
    (convertDifferentPtrMethod (S := S) pointer).address = pointer.address)

/-- `cconvert` returns the String, array reference, or GenericMemory object to keep alive. -/
def PointerCconvertAndSymbolConversion : Prop :=
  (∀ {S : Type} (toString : S → String) (value : S),
    cconvertStringUInt8 toString value = toString value) ∧
  (∀ {S : Type} (toString : S → String) (value : S),
    cconvertStringInt8 toString value = toString value) ∧
  (∀ {A R : Type} (getRef : A → R) (array : A),
    cconvertArray getRef array = getRef array) ∧
  (∀ {M : Type} (memory : M), cconvertGenericMemory memory = memory) ∧
  (∀ (symbolName : PointerSymbol → Ptr Byte) (symbol : PointerSymbol),
    unsafeConvertSymbolUInt8 symbolName symbol = symbolName symbol) ∧
  (∀ (symbolName : PointerSymbol → Ptr Byte) (symbol : PointerSymbol),
    (unsafeConvertSymbolInt8 symbolName symbol).address = (symbolName symbol).address)

/-- GenericMemoryRef uses element offsets for union or zero-size layouts, and byte pointers otherwise. -/
def PointerMemoryReferenceOffset : Prop :=
  ∀ {T : Type} (reference : PointerMemoryRef T),
    let memory := reference.mem
    let offset := reference.ptr_or_offset
    let elementBytes := memory.layoutBytes
    (unsafeConvertMemoryRefCvoid reference).address =
      if memory.arrayElement == 2 || elementBytes.val == 0 then
        memory.ptr.address + (offset * int64ToUInt64 elementBytes)
      else offset

/-- Array and memory pointer conversion retains the data address, including pointer reinterpretation. -/
def PointerArrayMemoryConversion : Prop :=
  (∀ {T : Type} (reference : PointerMemoryRef T),
    (unsafeConvertArray reference).address = (unsafeConvertMemoryRef (S := T) reference).address) ∧
  (∀ {T : Type} (memory : PointerMemoryObject T),
    unsafeConvertMemoryCvoid memory = memory.ptr) ∧
  (∀ {T S : Type} (memory : PointerMemoryObject T),
    (unsafeConvertMemory memory : Ptr S).address = memory.ptr.address) ∧
  (∀ {S T : Type} (sameType : Decidable (S = T)) (array : AbstractArrayPointerInput T)
      (typed : Ptr T),
    unsafeConvertPtrArray array = .ok typed →
      unsafeConvertAbstractArray sameType array = .ok (convertPtrDispatch sameType typed)) ∧
  (∀ {T : Type} (typeName : String),
    unsafeConvertUnsupportedArray (T := T) typeName =
      .error (.errorException ("conversion to pointer not defined for " ++ typeName)))

/-! `pointer(array, i)` is defined in `abstractarray.jl`; its layout and arithmetic callees use
the source-mirrored memory-offset model and pointer addition model, respectively. -/

/-- The byte offset is the dense linear-index difference times the element size. -/
def PointerArrayElementOffset : Prop :=
  ∀ {A T : Type} (pointer : A → ArrayResult (Ptr T))
    (toLinearIndex : A → I64 → ArrayResult I64)
    (linearIndices : A → ArrayResult I64) (first : I64 → ArrayResult I64)
    (elsize : A → ArrayResult I64) (array : A)
    (index linear linearBase origin size : I64) (base : Ptr T),
    pointer array = .ok base →
    toLinearIndex array index = .ok linear →
    linearIndices array = .ok linearBase →
    first linearBase = .ok origin →
    elsize array = .ok size →
    JuliaLean.base.abstractarray.pointerIndex pointer
      (JuliaLean.base.abstractarray.memoryOffsetDense toLinearIndex linearIndices first
        pointerOffsetSub elsize pointerOffsetMul)
      resultI64 pointerAddArrayResult array index =
        .ok (ptrAddI64 base (JuliaLean.base.int.mul
          (JuliaLean.base.int.sub linear origin) size))


/-- `unsafe_wrap` keeps the supplied pointer, dimensions, ownership flag, and backing bytes. -/
def PointerUnsafeWrapAliases : Prop :=
  (∀ {T : Type} {N : Nat} (pointer : Ptr T) (dims : TupleN I64 N) (own : Bool),
    let view := unsafeWrapArrayTuple pointer dims own
    view.pointer.address = pointer.address ∧ view.dims = dims ∧ view.owns = own) ∧
  (∀ {T : Type} {N : Nat} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
      (dims : TupleN I64 N) (own : Bool) (index : I64) (value : T),
    heap.validRange (indexedPointer codec pointer index).address.val.toNat codec.elementSize.val.toNat →
    let view := unsafeWrapArrayTuple pointer dims own
    match unsafeStoreAny codec pointerI64Result view.pointer heap value index with
    | .ok (stored, _) => unsafeLoad codec pointerI64Result pointer stored index = .ok value
    | .error _ => False) ∧
  (∀ {T I : Type} (pointer : Ptr T) (dimension : I) (toSize : I → U64) (own : Bool),
    let view := unsafeWrapArrayInteger pointer dimension toSize own
    view.pointer.address = pointer.address ∧ view.owns = own ∧
      view.dims.values = [i64 (toSize dimension).val]) ∧
  (∀ {T : Type} (kind : MemoryKind) (pointer : Ptr T) (dims : TupleN I64 1) (own : Bool),
    let view := unsafeWrapMemoryTuple kind pointer dims own
    view.pointer.address = pointer.address ∧ view.owns = own ∧
      view.length = int64ToUInt64 dims.first) ∧
  (∀ {T I : Type} (kind : MemoryKind) (pointer : Ptr T) (dimension : I)
      (toSize : I → U64) (own : Bool),
    let view := unsafeWrapMemoryInteger kind pointer dimension toSize own
    view.pointer.address = pointer.address ∧ view.owns = own ∧ view.length = toSize dimension) ∧
  (∀ {T I : Type} {N : Nat} (convertDims : TupleN I N → PtrResult (TupleN I64 N))
      (pointer : Ptr T) (dims : TupleN I N) (own : Bool) (converted : TupleN I64 N),
    convertDims dims = .ok converted →
    unsafeWrapGenericDims (.array : WrapTarget T N) convertDims pointer dims own =
      .ok (.array (unsafeWrapArrayTuple pointer converted own))) ∧
  (∀ {T I : Type} (convertDims : TupleN I 1 → PtrResult (TupleN I64 1))
      (kind : MemoryKind) (pointer : Ptr T) (dims : TupleN I 1) (own : Bool)
      (converted : TupleN I64 1),
    convertDims dims = .ok converted →
    unsafeWrapGenericDims (.memory kind : WrapTarget T 1) convertDims pointer dims own =
      .ok (.memory (unsafeWrapMemoryTuple kind pointer converted own)))

/-- A valid typed byte range loads the value encoded in its one-based slot. -/
def PointerLoadsReadOneBasedElements : Prop :=
  (∀ {T I : Type} [OfNat I 1] (codec : ByteCodec T) (toInt : I → PtrResult I64)
      (heap : ByteHeap) (pointer : Ptr T) (index : I) (slot : I64) (value : T),
    toInt index = .ok slot →
    heap.validRange (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat →
    heap.readBytes (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat =
      codec.encode value →
    unsafeLoad codec toInt pointer heap index = .ok value) ∧
  (∀ {T I : Type} [OfNat I 1] (codec : ByteCodec T) (toInt : I → PtrResult I64)
      (heap : ByteHeap) (pointer : Ptr T) (index : I) (slot : I64) (value : T),
    toInt index = .ok slot →
    heap.validRange (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat →
    heap.readBytes (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat =
      codec.encode value →
    unsafeLoadAtomicIndex codec toInt pointer heap index .seqCst = .ok value) ∧
  (∀ {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T) (value : T),
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
    heap.readBytes pointer.address.val.toNat codec.elementSize.val.toNat = codec.encode value →
    unsafeLoadAtomic codec pointer heap .seqCst = .ok value)

/-- Stores write the encoded value to the addressed slot and preserve the pointer return. -/
def PointerStoresWriteOneBasedElements : Prop :=
  (∀ {T V I : Type} [OfNat I 1] (codec : ByteCodec T) (convert : V → PtrResult T)
      (toInt : I → PtrResult I64) (heap : ByteHeap) (pointer : Ptr T)
      (value : V) (index : I) (slot : I64) (typed : T) (stored : ByteHeap),
    convert value = .ok typed → toInt index = .ok slot →
    heap.validRange (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat →
    unsafeStoreTyped codec convert toInt pointer heap value index = .ok (stored, pointer) →
    stored.readBytes (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat =
      codec.encode typed) ∧
(∀ {T I : Type} [OfNat I 1] (codec : ByteCodec T) (toInt : I → PtrResult I64)
    (heap : ByteHeap) (pointer : Ptr T) (value : T) (index : I) (slot : I64) (stored : ByteHeap),
    toInt index = .ok slot →
    heap.validRange (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat →
    unsafeStoreAny codec toInt pointer heap value index = .ok (stored, pointer) →
    stored.readBytes (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat =
      codec.encode value) ∧
  (∀ {T V : Type} (codec : ByteCodec T) (cast : V → Option T)
      (convert : V → PtrResult T) (heap : ByteHeap) (pointer : Ptr T)
      (value : V) (typed : T) (stored : ByteHeap) (order : MemoryOrder),
    castOrConverted cast convert value typed →
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
    unsafeStoreAtomic codec cast convert pointer heap value order = .ok (stored, pointer) →
    stored.readBytes pointer.address.val.toNat codec.elementSize.val.toNat = codec.encode typed) ∧
  (∀ {T V I : Type} (codec : ByteCodec T) (cast : V → Option T)
      (convert : V → PtrResult T) (toInt : I → PtrResult I64)
      (heap : ByteHeap) (pointer : Ptr T) (value : V) (index : I) (slot : I64)
      (typed : T) (stored : ByteHeap),
    castOrConverted cast convert value typed → toInt index = .ok slot →
    heap.validRange (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat →
    unsafeStoreAtomicIndex codec cast convert toInt pointer heap value index .seqCst =
      .ok (stored, ptrAddI64 pointer (codec.elementSize * (slot - oneI64))) →
    stored.readBytes (indexedPointer codec pointer slot).address.val.toNat codec.elementSize.val.toNat =
      codec.encode typed)

/-- Atomic modify, replace and swap return the documented old and updated values. -/
def PointerAtomicOperations : Prop :=
  (∀ {T X : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
      (operation : T → X → T) (value : X) (old : T) (order : MemoryOrder),
    pointerRef codec heap pointer oneI64 oneI64 = old →
    let (stored, result) := unsafeModify codec pointer heap operation value order
    result = (old, operation old value) ∧
      pointerRef codec stored pointer oneI64 oneI64 = operation old value) ∧
  (∀ {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
      (value old : T) (order : MemoryOrder),
    pointerRef codec heap pointer oneI64 oneI64 = old →
    let (stored, result) := unsafeSwapAny codec pointer heap value order
    result = old ∧ pointerRef codec stored pointer oneI64 oneI64 = value) ∧
  (∀ {T : Type} (codec : ByteCodec T) (same : T → T → Bool)
      (heap : ByteHeap) (pointer : Ptr T) (expected desired old : T)
      (successOrder failOrder : MemoryOrder),
    pointerRef codec heap pointer oneI64 oneI64 = old →
    let (stored, result) := unsafeReplaceAny codec same pointer heap expected desired successOrder failOrder
    result.old = old ∧ result.success = same old expected ∧
      pointerRef codec stored pointer oneI64 oneI64 =
        if same old expected then desired else old) ∧
(∀ {T E V : Type} (codec : ByteCodec T) (same : T → E → Bool)
    (cast : V → Option T) (convert : V → PtrResult T)
    (heap : ByteHeap) (pointer : Ptr T) (expected : E) (desired : V) (typed old : T)
    (successOrder failOrder : MemoryOrder),
  castOrConverted cast convert desired typed →
  pointerRef codec heap pointer oneI64 oneI64 = old →
  unsafeReplaceTyped codec same cast convert pointer heap expected desired successOrder failOrder =
    .ok (atomicPointerReplace codec same heap pointer expected typed successOrder failOrder) ∧
  (let (stored, result) := atomicPointerReplace codec same heap pointer expected typed successOrder failOrder
   result.old = old ∧ result.success = same old expected ∧
     pointerRef codec stored pointer oneI64 oneI64 =
       if same old expected then typed else old)) ∧
(∀ {T V : Type} (codec : ByteCodec T) (cast : V → Option T)
    (convert : V → PtrResult T) (heap : ByteHeap) (pointer : Ptr T)
    (value : V) (typed old : T) (order : MemoryOrder),
  castOrConverted cast convert value typed →
  pointerRef codec heap pointer oneI64 oneI64 = old →
  unsafeSwapTyped codec cast convert pointer heap value order =
    .ok (atomicPointerSwap codec heap pointer typed order) ∧
  (let (stored, previous) := atomicPointerSwap codec heap pointer typed order
   previous = old ∧ pointerRef codec stored pointer oneI64 oneI64 = typed))

/-- `pointer_from_objref` rejects immutable values; valid object pointers convert back. -/
def PointerObjectReferenceBehavior : Prop :=
  (∀ {A : Type} (ismutable : A → Bool) (objectAddress : A → Ptr Unit) (value : A),
    pointerFromObjref ismutable objectAddress value =
      if ismutable value then .ok (objectAddress value)
      else .error (.errorException "pointer_from_objref cannot be used on immutable objects")) ∧
  (∀ {A T : Type} (objectFromPointer : Ptr Unit → A) (pointer : Ptr T),
    unsafePointerToObjref objectFromPointer pointer = objectFromPointer (convertPtrType pointer)) ∧
  (∀ {A : Type} (objectFromPointer : Ptr Unit → A) (objectAddress : A → Ptr Unit)
      (value : A),
    objectFromPointer (objectAddress value) = value →
    unsafePointerToObjref objectFromPointer (objectAddress value) = value)

/-- Registry entries for the source-mirrored `base/pointer.jl` model. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "pointer-address-arithmetic", juliaFile := "base/pointer.jl",
    juliaFns := ["isequal(::Ptr,::Ptr)", "isless(::Ptr{T},::Ptr{T})", "==(::Ptr,::Ptr)", "<(::Ptr,::Ptr)",
      "-(::Ptr,::Ptr)", "-%(::Ptr,::Ptr)", "+(::Ptr,::Integer)", "-(::Ptr,::Integer)",
      "+(::Integer,::Ptr)", "unsigned(::Ptr)", "signed(::Ptr)"],
    statement := "Pointer comparisons use unsigned address order and pointer differences and byte offsets wrap in the UInt64 address space.",
    source := "invariant; base/pointer.jl:307-320; src/runtime_intrinsics.c:1848-1853",
    status := .todo, prop := ``PointerAddressArithmetic, thm := none },
  { id := "pointer-integer-conversions", juliaFile := "base/pointer.jl",
    juliaFns := ["convert(::Type{T<:Integer},::Ptr)", "convert(::Type{Ptr{T}},::Union{Int,UInt})",
      "convert(::Type{Ptr{T}},::Ptr{T})", "convert(::Type{Ptr{T}},::Ptr)", "unsigned(::Ptr)", "signed(::Ptr)"],
    statement := "Converting a pointer to an integer or another pointer type preserves its 64-bit address pattern; signed conversion reinterprets those bits.",
    source := "invariant; base/pointer.jl:23,26,29-30,319-320",
    status := .todo, prop := ``PointerIntegerConversions, thm := none },
  { id := "pointer-cconvert-symbol-roots", juliaFile := "base/pointer.jl",
    juliaFns := ["cconvert(::Type{Ptr{UInt8}},::AbstractString)", "cconvert(::Type{Ptr{Int8}},::AbstractString)",
      "unsafe_convert(::Type{Ptr{UInt8}},::Symbol)", "unsafe_convert(::Type{Ptr{Int8}},::Symbol)",
      "cconvert(::Type{<:Ptr},::Array)", "cconvert(::Type{<:Ptr},::GenericMemory)"],
    statement := "cconvert yields the String or backing object that callers keep alive during pointer use, and symbol conversions use the symbol-name address.",
    source := "unsafe_convert docstring and base/pointer.jl:58-63,71",
    status := .todo, prop := ``PointerCconvertAndSymbolConversion, thm := none },
  { id := "pointer-memoryref-byte-offset", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{Cvoid}},::GenericMemory)", "unsafe_convert(::Type{Ptr{T}},::GenericMemory)",
      "unsafe_convert(::Type{Ptr{Cvoid}},::GenericMemoryRef)", "unsafe_convert(::Type{Ptr{T}},::GenericMemoryRef)"],
    statement := "GenericMemoryRef conversion scales element offsets by layout size for union and zero-size layouts, and otherwise preserves the stored pointer address.",
    source := "invariant; base/pointer.jl:72-88",
    status := .todo, prop := ``PointerMemoryReferenceOffset, thm := none },
  { id := "pointer-array-memory-conversion", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{S}},::AbstractArray{T})", "unsafe_convert(::Type{Ptr{T}},::Array{T})",
      "unsafe_convert(::Type{Ptr{T}},::AbstractArray{T})"],
    statement := "Array pointer conversion keeps the same storage address, reinterprets only the pointer element type, and rejects unsupported abstract arrays.",
    source := "unsafe_convert docstring and base/pointer.jl:64-66",
    status := .todo, prop := ``PointerArrayMemoryConversion, thm := none },
  { id := "pointer-array-index-offset", juliaFile := "base/pointer.jl",
    juliaFns := ["+(::Ptr,::Integer)", "pointer(::AbstractArray{T},::Integer) [base/abstractarray.jl:1280-1283]"],
    statement := "For dense arrays, pointer(A,i) advances by (linearIndex(i)-first(LinearIndices(A))) * elsize(A) bytes.",
    source := "base/abstractarray.jl:1280-1286; base/pointer.jl:315",
    status := .todo, prop := ``PointerArrayElementOffset, thm := none },
  { id := "pointer-unsafe-wrap-alias", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_wrap(::Array,::Ptr,::NTuple)", "unsafe_wrap(::Array,::Ptr,::Integer)",
      "unsafe_wrap(::GenericMemory,::Ptr,::Tuple{Int})", "unsafe_wrap(::GenericMemory,::Ptr,::Integer)",
      "unsafe_wrap(::Union{Array,GenericMemory},::Ptr,::NTuple{N,<:Integer})"],
    statement := "unsafe_wrap creates a view over the supplied bytes without copying and preserves the requested dimensions and ownership flag.",
    source := "unsafe_wrap docstring; base/pointer.jl:91-128",
    status := .todo, prop := ``PointerUnsafeWrapAliases, thm := none },
  { id := "pointer-unsafe-load-index", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_load(::Ptr,::Integer)", "unsafe_load(::Ptr,::Symbol)", "unsafe_load(::Ptr,::Integer,::Symbol)"],
    statement := "unsafe_load reads the requested one-based element, whose byte address is p + (i-1)*elsize(T), including the atomic-order overload.",
    source := "unsafe_load docstring; base/pointer.jl:151-155",
    status := .todo, prop := ``PointerLoadsReadOneBasedElements, thm := none },
  { id := "pointer-unsafe-store-index", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_store!(::Ptr{Any},x,::Integer)", "unsafe_store!(::Ptr{T},x,::Integer)",
      "unsafe_store!(::Ptr{T},x,::Symbol)", "unsafe_store!(::Ptr,x,::Integer,::Symbol)"],
    statement := "unsafe_store! writes the converted value to the requested one-based element, using (i-1)*elsize(T) byte offsets for ordered stores.",
    source := "unsafe_store! docstring; base/pointer.jl:177-182",
    status := .todo, prop := ``PointerStoresWriteOneBasedElements, thm := none },
  { id := "pointer-atomic-modify-replace-swap", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_modify!(::Ptr,op,x,::Symbol)", "unsafe_replace!(::Ptr{T},expected,desired,::Symbol,::Symbol)",
      "unsafe_replace!(::Ptr{Any},expected,desired,::Symbol,::Symbol)", "unsafe_swap!(::Ptr{Any},x,::Symbol)",
      "unsafe_swap!(::Ptr{T},x,::Symbol)"],
    statement := "Atomic modification returns the old and new values, replacement stores only when old === expected, and swap returns the old value.",
    source := "unsafe_modify!, unsafe_replace!, and unsafe_swap! docstrings; base/pointer.jl:207-273",
    status := .todo, prop := ``PointerAtomicOperations, thm := none },
  { id := "pointer-object-reference-mutability", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_pointer_to_objref(::Ptr)", "pointer_from_objref(::Any)"],
    statement := "A valid object pointer converts back to its object, and pointer_from_objref rejects immutable objects while returning a mutable object's address.",
    source := "unsafe_pointer_to_objref and pointer_from_objref docstrings; base/pointer.jl:285,299-303",
    status := .todo, prop := ``PointerObjectReferenceBehavior, thm := none }
]

end JuliaLean.Proofs.base.pointer
