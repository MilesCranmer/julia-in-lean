import JuliaLean.base.pointer
import JuliaLean.base.abstractarray
import JuliaLean.base.int
import JuliaLean.Proofs.base.int

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

def pointerI64Result (value : I64) : PtrResult I64 := .ok value



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
  (∀ {S T : Type} (sameType : Decidable (S = T)) (left : Ptr S) (right : Ptr T),
    isequalPtr sameType left right = ptrIdentity sameType left right)

structure StringCconvertCalls (S : Type) where
  toString : S → String
  representsSameText : String → S → Prop
  keepsStringRooted : String → Prop
  toString_represents : ∀ value, representsSameText (toString value) value
  toString_rooted : ∀ value, keepsStringRooted (toString value)

structure ArrayRefRooting (A R : Type) where
  getRef : A → R
  keepsArrayRooted : R → A → Prop
  getRef_keepsArrayRooted : ∀ array, keepsArrayRooted (getRef array) array

structure GenericMemoryRooting (M : Type) where
  keepsMemoryRooted : M → Prop
  memory_is_root : ∀ memory, keepsMemoryRooted memory

structure SymbolNameCalls where
  jlSymbolName : PointerSymbol → Ptr Byte
  returnsNamePointer : ∀ symbol, jlSymbolName symbol = symbol.namePointer

/-- Pointer conversions preserve unsigned bits and use the supplied Julia primitive contracts. -/
def PointerIntegerConversions : Prop :=
  (∀ {T I : Type} (toUInt : Ptr T → U64) (fromUInt : U64 → PtrResult I)
      (integerValue : I → Int) (pointer : Ptr T) (converted : I),
    (∀ p, toUInt p = p.address) →
    (∀ address value, fromUInt address = .ok value → integerValue value = address.val) →
    convertPtrToIntegerMethod toUInt fromUInt pointer = .ok converted →
      integerValue converted = pointer.address.val) ∧
  (∀ {T : Type} (construct : NativeInt → Ptr T),
    (∀ value, (construct value).address = value.toUInt64) →
    ∀ value, (convertIntegerToPtrMethod construct value).address = value.toUInt64) ∧
  (∀ {T : Type} (pointer : Ptr T), convertSamePtrMethod pointer = pointer) ∧
  (∀ {S T : Type} (bitcast : Ptr T → Ptr S),
    (∀ pointer, (bitcast pointer).address = pointer.address) →
    ∀ pointer, (convertDifferentPtrMethod bitcast pointer).address = pointer.address) ∧
  (∀ {T : Type} (pointer : Ptr T), ptrUnsigned pointer = pointer.address) ∧
  (∀ {T : Type} (pointer : Ptr T),
    (ptrSigned pointer).val = wrapInt .i64 pointer.address.val)

/-- String conversion preserves text and its returned String is a GC root; array references keep
their source arrays rooted, and symbol-name conversion uses the runtime name-pointer call. -/
def PointerCconvertAndSymbolConversion : Prop :=
  (∀ {S : Type} (calls : StringCconvertCalls S) (value : S),
    calls.representsSameText (cconvertStringUInt8 calls.toString value) value ∧
    calls.keepsStringRooted (cconvertStringUInt8 calls.toString value)) ∧
  (∀ {S : Type} (calls : StringCconvertCalls S) (value : S),
    calls.representsSameText (cconvertStringInt8 calls.toString value) value ∧
    calls.keepsStringRooted (cconvertStringInt8 calls.toString value)) ∧
  (∀ {A R : Type} (calls : ArrayRefRooting A R) (array : A),
    calls.keepsArrayRooted (cconvertArray calls.getRef array) array) ∧
  (∀ {M : Type} (calls : GenericMemoryRooting M) (memory : M),
    calls.keepsMemoryRooted (cconvertGenericMemory memory)) ∧
  (∀ (calls : SymbolNameCalls) (symbol : PointerSymbol),
    (unsafeConvertSymbolUInt8 calls.jlSymbolName symbol).address =
      symbol.namePointer.address) ∧
  (∀ (calls : SymbolNameCalls) (symbol : PointerSymbol),
    (unsafeConvertSymbolInt8 calls.jlSymbolName symbol).address =
      symbol.namePointer.address)

def pointerMemoryRefAddress {T : Type} (reference : PointerMemoryRef T) : U64 :=
  if reference.mem.arrayElement == 2 || reference.mem.layoutBytes.val == 0 then
    reference.mem.ptr.address +
      reference.ptr_or_offset * int64ToUInt64 reference.mem.layoutBytes
  else reference.ptr_or_offset
/-- A GenericMemoryRef conversion points to the selected element bytes, so an unsafe load through
the converted pointer reads the encoding stored at that element's layout-derived address. -/
def PointerMemoryReferenceOffset : Prop :=
  (∀ {T : Type} (memory : PointerMemoryObject T) (codec : ByteCodec T)
      (heap : ByteHeap) (value : T),
    heap.validRange memory.ptr.address.val.toNat codec.elementSize.val.toNat →
    heap.readBytes memory.ptr.address.val.toNat codec.elementSize.val.toNat = codec.encode value →
    unsafeLoad codec pointerI64Result (unsafeConvertMemory (S := T) memory) heap oneI64 = .ok value) ∧
  (∀ {T : Type} (reference : PointerMemoryRef T) (codec : ByteCodec T)
      (heap : ByteHeap) (index : I64) (value : T),
    let expectedPointer : Ptr T := ⟨pointerMemoryRefAddress reference⟩
    heap.validRange (indexedPointer codec expectedPointer index).address.val.toNat
      codec.elementSize.val.toNat →
    heap.readBytes (indexedPointer codec expectedPointer index).address.val.toNat
      codec.elementSize.val.toNat = codec.encode value →
    unsafeLoad codec pointerI64Result (unsafeConvertMemoryRef (S := T) reference)
      heap index = .ok value)

/-- Supported array references always convert to a pointer, including reinterpreted element
types; unsupported AbstractArray values report their actual type name. -/
def PointerArrayMemoryConversion : Prop :=
  (∀ {T : Type} (reference : PointerMemoryRef T) (codec : ByteCodec T)
      (heap : ByteHeap) (index : I64) (value : T),
    heap.validRange (indexedPointer codec (unsafeConvertMemoryRef (S := T) reference) index).address.val.toNat
      codec.elementSize.val.toNat →
    heap.readBytes (indexedPointer codec (unsafeConvertMemoryRef (S := T) reference) index).address.val.toNat
      codec.elementSize.val.toNat = codec.encode value →
    unsafeLoad codec pointerI64Result (unsafeConvertArray reference) heap index = .ok value) ∧
  (∀ {S T : Type} (sameType : Decidable (S = T)) (reference : PointerMemoryRef T),
    ∃ converted, unsafeConvertAbstractArray sameType (.array reference) = .ok converted ∧
      converted.address = (unsafeConvertArray reference).address) ∧
  (∀ {S T A : Type} (sameType : Decidable (S = T)) (typeof : A → String) (array : A),
    unsafeConvertAbstractArray sameType (.other array typeof) =
      .error (.errorException ("conversion to pointer not defined for " ++ typeof array)))

/-! `pointer(array, i)` uses the source-mirrored Int subtraction, multiplication and Ptr addition
models; only the array's linear-index and element-size queries remain typed interface inputs. -/

/-- For dense arrays, pointer(A,i) advances by (linearIndex(i)-first(LinearIndices(A))) *
elsize(A), with Julia's modeled Int and Ptr operations. -/
def PointerArrayElementOffset : Prop :=
  ∀ {A T : Type} (pointer : A → ArrayResult (Ptr T))
    (toLinearIndex : A → I64 → ArrayResult I64)
    (linearIndices : A → ArrayResult I64) (first : I64 → ArrayResult I64)
    (elsize : A → ArrayResult I64) (array : A) (index linear linearBase origin size : I64)
    (base : Ptr T),
    pointer array = .ok base →
    toLinearIndex array index = .ok linear →
    linearIndices array = .ok linearBase →
    first linearBase = .ok origin →
    elsize array = .ok size →
    ∃ result,
      JuliaLean.base.abstractarray.pointerIndex pointer
        (JuliaLean.base.abstractarray.memoryOffsetDense toLinearIndex linearIndices first
          (fun left right => .ok (JuliaLean.base.int.sub left right))
          elsize (fun difference elementSize => .ok (JuliaLean.base.int.mul difference elementSize)))
        (fun offset => .ok offset)
        (fun p offset => .ok
          (JuliaLean.base.pointer.ptrAddInteger int64ToUInt64 p offset))
        array index = .ok result ∧
      result.address.val =
        wrapInt .u64 (base.address.val +
          wrapInt .u64 (wrapInt .i64
            (wrapInt .i64 (linear.val - origin.val) * size.val)))

/-- `unsafe_wrap` keeps the supplied pointer, dimensions, ownership flag, and backing bytes. -/
def PointerUnsafeWrapAliases : Prop :=
  (∀ {T : Type} {N : Nat} (calls : UnsafeWrapCalls) (pointer : Ptr T)
      (dims : TupleN I64 N) (own : Bool),
    let view := unsafeWrapArrayTuple calls pointer dims own
    view.pointer.address = pointer.address ∧ view.dims = dims ∧ view.owns = own) ∧
  (∀ {T I : Type} (calls : UnsafeWrapCalls) (pointer : Ptr T)
      (dimension : I) (toSize : I → U64) (own : Bool),
    let view := unsafeWrapArrayInteger calls pointer dimension toSize own
    view.pointer.address = pointer.address ∧ view.owns = own ∧
      view.dims.values = [i64 (toSize dimension).val]) ∧
  (∀ {T : Type} (calls : UnsafeWrapCalls) (kind : MemoryKind) (pointer : Ptr T)
      (dims : TupleN I64 1) (own : Bool),
    let view := unsafeWrapMemoryTuple calls kind pointer dims own
    view.pointer.address = pointer.address ∧ view.owns = own ∧
      view.length = int64ToUInt64 dims.first) ∧
  (∀ {T I : Type} (calls : UnsafeWrapCalls) (kind : MemoryKind) (pointer : Ptr T)
      (dimension : I) (toSize : I → U64) (own : Bool),
    let view := unsafeWrapMemoryInteger calls kind pointer dimension toSize own
    view.pointer.address = pointer.address ∧ view.owns = own ∧
      view.length = toSize dimension) ∧
  (∀ {T : Type} {N : Nat} (calls : UnsafeWrapCalls) (codec : ByteCodec T)
      (heap : ByteHeap) (pointer : Ptr T) (dims : TupleN I64 N)
      (own : Bool) (index : I64),
    unsafeLoad codec pointerI64Result (unsafeWrapArrayTuple calls pointer dims own).pointer
      heap index =
    unsafeLoad codec pointerI64Result pointer heap index) ∧
  (∀ {T I : Type} {N : Nat} (calls : UnsafeWrapCalls)
      (convertDims : TupleN I N → PtrResult (TupleN I64 N))
      (pointer : Ptr T) (dims : TupleN I N) (own : Bool) (converted : TupleN I64 N),
    convertDims dims = .ok converted →
    unsafeWrapGenericDims calls (.array : WrapTarget T N) convertDims pointer dims own =
      .ok (.array (unsafeWrapArrayTuple calls pointer converted own))) ∧
  (∀ {T : Type} (calls : UnsafeWrapCalls)
      (convertDims : TupleN I64 1 → PtrResult (TupleN I64 1))
      (kind : MemoryKind) (pointer : Ptr T) (dims : TupleN I64 1)
      (own : Bool) (converted : TupleN I64 1),
    convertDims dims = .ok converted →
    unsafeWrapGenericDims calls (.memory kind : WrapTarget T 1) convertDims pointer dims own =
      .ok (.memory (unsafeWrapMemoryTuple calls kind pointer converted own)))
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

private theorem addressMod_eq_of_lt (address : Nat) (h : address < 2 ^ 64) :
    addressMod address = address := by
  simp [addressMod, Nat.mod_eq_of_lt h]

private theorem byteHeap_readByte_writeByte_ne (heap : ByteHeap) (address target : Nat)
    (value : Byte) (h : addressMod target ≠ addressMod address) :
    (heap.writeByte address value).readByte target = heap.readByte target := by
  have hIdem : addressMod (addressMod target) = addressMod target := by
    simp [addressMod]
  simp [ByteHeap.readByte, ByteHeap.writeByte, hIdem, h]

private theorem byteHeap_readByte_writeBytes_outside (heap : ByteHeap) (base target : Nat)
    (bytes : List Byte) (hNoWrap : base + bytes.length ≤ 2 ^ 64)
    (hTarget : target < 2 ^ 64)
    (hOutside : ∀ offset, offset < bytes.length → target ≠ base + offset) :
    (heap.writeBytes base bytes).readByte target = heap.readByte target := by
  induction bytes generalizing heap base with
  | nil => simp [ByteHeap.writeBytes]
  | cons value rest ih =>
      simp only [List.length_cons] at hNoWrap hOutside
      simp only [ByteHeap.writeBytes]
      have hTailNoWrap : base + 1 + rest.length ≤ 2 ^ 64 := by omega
      have hTailOutside : ∀ offset, offset < rest.length → target ≠ base + 1 + offset := by
        intro offset hOffset
        have h := hOutside (offset + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      rw [ih (heap.writeByte base value) (base + 1) hTailNoWrap hTailOutside]
      have hBase : base < 2 ^ 64 := by omega
      have hAddress : addressMod target ≠ addressMod base := by
        rw [addressMod_eq_of_lt target hTarget, addressMod_eq_of_lt base hBase]
        exact hOutside 0 (by simp)
      exact byteHeap_readByte_writeByte_ne heap base target value hAddress

private theorem byteHeap_readBytes_writeBytes (heap : ByteHeap) (base : Nat)
    (bytes : List Byte) (hNoWrap : base + bytes.length ≤ 2 ^ 64) :
    (heap.writeBytes base bytes).readBytes base bytes.length = bytes := by
  induction bytes generalizing heap base with
  | nil => simp [ByteHeap.writeBytes, ByteHeap.readBytes]
  | cons value rest ih =>
      simp only [List.length_cons] at hNoWrap
      have hTailNoWrap : base + 1 + rest.length ≤ 2 ^ 64 := by omega
      have hBase : base < 2 ^ 64 := by omega
      have hTailOutside : ∀ offset, offset < rest.length → base ≠ base + 1 + offset := by
        intro offset hOffset
        omega
      have hFirst :
          ((heap.writeByte base value).writeBytes (base + 1) rest).readByte base = value := by
        rw [byteHeap_readByte_writeBytes_outside (heap.writeByte base value)
          (base + 1) base rest hTailNoWrap hBase hTailOutside]
        have hIdem : addressMod (addressMod base) = addressMod base := by
          simp [addressMod]
        simp [ByteHeap.readByte, ByteHeap.writeByte, hIdem]
      have hRest := ih (heap.writeByte base value) (base + 1) hTailNoWrap
      simp only [ByteHeap.writeBytes, ByteHeap.readBytes, List.length_cons]
      rw [hFirst, hRest]

private theorem pointerRef_afterWrite {T : Type} (codec : ByteCodec T) (heap : ByteHeap)
    (pointer : Ptr T) (index : I64) (value : T) (base : Nat)
    (hAddress : (indexedPointer codec pointer index).address.val.toNat = base)
    (hNoWrap : base + codec.elementSize.val.toNat ≤ 2 ^ 64) :
    pointerRef codec (heap.writeBytes base (codec.encode value)) pointer index oneI64 = value := by
  have hBytesNoWrap : base + (codec.encode value).length ≤ 2 ^ 64 := by
    rw [codec.encode_length value]
    exact hNoWrap
  have hRead := byteHeap_readBytes_writeBytes heap base (codec.encode value) hBytesNoWrap
  have hReadSize :
      (heap.writeBytes base (codec.encode value)).readBytes base codec.elementSize.val.toNat =
        codec.encode value := by
    rw [← codec.encode_length value]
    exact hRead
  unfold pointerRef
  rw [hAddress, hReadSize, codec.decode_encode]


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
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
    pointerRef codec heap pointer oneI64 oneI64 = old →
    let (stored, result) := unsafeModify codec pointer heap operation value order
    result = (old, operation old value) ∧
      pointerRef codec stored pointer oneI64 oneI64 = operation old value) ∧
  (∀ {T : Type} (codec : ByteCodec T) (heap : ByteHeap) (pointer : Ptr T)
      (value old : T) (order : MemoryOrder),
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
    pointerRef codec heap pointer oneI64 oneI64 = old →
    let (stored, result) := unsafeSwapAny codec pointer heap value order
    result = old ∧ pointerRef codec stored pointer oneI64 oneI64 = value) ∧
  (∀ {T : Type} (codec : ByteCodec T) (same : T → T → Bool)
      (heap : ByteHeap) (pointer : Ptr T) (expected desired old : T)
      (successOrder failOrder : MemoryOrder),
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
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
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
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
    heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat →
    pointerRef codec heap pointer oneI64 oneI64 = old →
    unsafeSwapTyped codec cast convert pointer heap value order =
      .ok (atomicPointerSwap codec heap pointer typed order) ∧
    (let (stored, previous) := atomicPointerSwap codec heap pointer typed order
     previous = old ∧ pointerRef codec stored pointer oneI64 oneI64 = typed))
structure PointerObjectReferenceCalls (A : Type) where
  ismutable : A → Bool
  objectAddress : A → Ptr Unit
  objectFromPointer : Ptr Unit → A
  pointsToObject : Ptr Unit → A → Prop
  objectAddress_pointsTo : ∀ value, pointsToObject (objectAddress value) value
  pointer_returns_object : ∀ pointer value,
    pointsToObject pointer value → objectFromPointer pointer = value

/-- Mutable objects have stable addresses, and converting a valid object pointer back yields the
object identified by the runtime pointer call. -/
def PointerObjectReferenceBehavior : Prop :=
  (∀ {A : Type} (calls : PointerObjectReferenceCalls A) (value : A),
    calls.ismutable value = true →
    pointerFromObjref calls.ismutable calls.objectAddress value = .ok (calls.objectAddress value) ∧
      calls.pointsToObject (calls.objectAddress value) value) ∧
  (∀ {A : Type} (calls : PointerObjectReferenceCalls A) (value : A),
    calls.ismutable value = false →
    pointerFromObjref calls.ismutable calls.objectAddress value =
      .error (.errorException "pointer_from_objref cannot be used on immutable objects")) ∧
  (∀ {A T : Type} (calls : PointerObjectReferenceCalls A) (pointer : Ptr T) (value : A),
    calls.pointsToObject (convertPtrType pointer) value →
    unsafePointerToObjref calls.objectFromPointer pointer = value)


private theorem convertPtrDispatch_address {S T : Type}
    (sameType : Decidable (S = T)) (pointer : Ptr T) :
    (convertPtrDispatch sameType pointer).address = pointer.address := by
  cases sameType with
  | isTrue h => subst S; simp [convertPtrDispatch, convertPtrSame]
  | isFalse h => simp [convertPtrDispatch, convertPtrType]

theorem pointerAddressArithmetic_proven : PointerAddressArithmetic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S T left right
    cases h : (left.address.val == right.address.val) with
    | false =>
        have hne : left.address.val ≠ right.address.val := beq_eq_false_iff_ne.mp h
        simp [ptrEqual, h, hne]
    | true =>
        have heq : left.address.val = right.address.val := beq_iff_eq.mp h
        simp [ptrEqual, h, heq]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem pointerIntegerConversions_proven : PointerIntegerConversions := by
  unfold PointerIntegerConversions
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T I toUInt fromUInt integerValue pointer converted hToUInt hFromUInt hConvert
    have hCast : fromUInt (toUInt pointer) = .ok converted := by
      simpa [convertPtrToIntegerMethod] using hConvert
    have hValue := hFromUInt (toUInt pointer) converted hCast
    rw [hToUInt pointer] at hValue
    exact hValue
  · intro T construct hConstruct value
    simpa [convertIntegerToPtrMethod] using hConstruct value
  · intros
    rfl
  · intro S T bitcast hBitcast pointer
    exact hBitcast pointer
  · intros
    rfl
  · intros
    rfl
theorem pointerCconvertAndSymbolConversion_proven :
    PointerCconvertAndSymbolConversion := by
  unfold PointerCconvertAndSymbolConversion
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S calls value
    exact ⟨calls.toString_represents value, calls.toString_rooted value⟩
  · intro S calls value
    exact ⟨calls.toString_represents value, calls.toString_rooted value⟩
  · intro A R calls array
    exact calls.getRef_keepsArrayRooted array
  · intro M calls memory
    exact calls.memory_is_root memory
  · intro calls symbol
    simp [unsafeConvertSymbolUInt8, calls.returnsNamePointer]
  · intro calls symbol
    simp [unsafeConvertSymbolInt8, convertPtrType, calls.returnsNamePointer]


private theorem elementOffsetZero {T : Type} (codec : ByteCodec T) :
    codec.elementSize * (oneI64 - oneI64) = i64 0 := by
  have hSub : oneI64 - oneI64 = i64 0 := by
    apply Subtype.ext
    decide
  rw [hSub]
  apply Subtype.ext
  have hZero : (i64 0).val = 0 := by decide
  change wrapInt .i64 (codec.elementSize.val * (i64 0).val) = (i64 0).val
  rw [hZero]
  simp [wrapInt, IntTy.signed, IntTy.bits]

private theorem int64ToUInt64_zero : int64ToUInt64 (i64 0) = u64 0 := by
  apply Subtype.ext
  have hZero : (i64 0).val = 0 := by decide
  change wrapInt .u64 (i64 0).val = (u64 0).val
  rw [hZero]
  rfl

private theorem indexedPointer_one {T : Type} (codec : ByteCodec T) (pointer : Ptr T) :
    indexedPointer codec pointer oneI64 = pointer := by
  rw [show indexedPointer codec pointer oneI64 =
    addPtrBytes pointer (int64ToUInt64 (codec.elementSize * (oneI64 - oneI64))) by
      rfl]
  rw [elementOffsetZero, int64ToUInt64_zero]
  simp only [addPtrBytes]
  cases pointer with
  | mk address =>
      apply congrArg Ptr.mk
      apply Subtype.ext
      change wrapInt .u64 (address.val + (u64 0).val) = address.val
      have hZero : (u64 0).val = 0 := by decide
      rw [hZero, Int.add_zero]
      exact wrapInt_of_inRange .u64 address.val address.property
private theorem pointerRef_afterAtomicSet {T : Type} (codec : ByteCodec T)
    (heap : ByteHeap) (pointer : Ptr T) (value : T) (order : MemoryOrder)
    (hValid : heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat) :
    pointerRef codec (atomicPointerSet codec heap pointer value order).1
      pointer oneI64 oneI64 = value := by
  have hAddress : (indexedPointer codec pointer oneI64).address.val.toNat =
      pointer.address.val.toNat := by
    rw [indexedPointer_one]
  have hWritten := pointerRef_afterWrite codec heap pointer oneI64 value
    pointer.address.val.toNat hAddress hValid.1
  simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hWritten
private theorem unsafeStoreAtomic_writes {T V : Type} (codec : ByteCodec T)
    (cast : V → Option T) (convert : V → PtrResult T) (heap : ByteHeap)
    (pointer : Ptr T) (value : V) (typed : T) (stored : ByteHeap) (order : MemoryOrder)
    (hCast : castOrConverted cast convert value typed)
    (hValid : heap.validRange pointer.address.val.toNat codec.elementSize.val.toNat)
    (hStore : unsafeStoreAtomic codec cast convert pointer heap value order =
      .ok (stored, pointer)) :
    stored.readBytes pointer.address.val.toNat codec.elementSize.val.toNat = codec.encode typed := by
  have hMemory : stored = heap.writeBytes pointer.address.val.toNat (codec.encode typed) := by
    cases hcast : cast value with
    | some castValue =>
        have htyped : castValue = typed := by
          rcases hCast with hSome | ⟨hNone, _hConvert⟩
          · rw [hcast] at hSome
            exact Option.some.inj hSome
          · rw [hcast] at hNone
            cases hNone
        subst castValue
        have hPair :
            atomicPointerSet codec heap pointer typed order = (stored, pointer) := by
          simpa [unsafeStoreAtomic, hcast, bind, Except.bind, pure, Except.pure] using hStore
        have hFirst := congrArg Prod.fst hPair
        simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hFirst.symm
    | none =>
        have hConvert : convert value = .ok typed := by
          rcases hCast with hSome | ⟨hNone, hConvert⟩
          · rw [hcast] at hSome
            cases hSome
          · exact hConvert
        have hPair :
            atomicPointerSet codec heap pointer typed order = (stored, pointer) := by
          simpa [unsafeStoreAtomic, hcast, hConvert, bind, Except.bind,
            pure, Except.pure] using hStore
        have hFirst := congrArg Prod.fst hPair
        simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hFirst.symm
  have hNoWrap : pointer.address.val.toNat + (codec.encode typed).length ≤ 2 ^ 64 := by
    rw [codec.encode_length typed]
    exact hValid.1
  have hRead := byteHeap_readBytes_writeBytes heap pointer.address.val.toNat
    (codec.encode typed) hNoWrap
  rw [hMemory, ← codec.encode_length typed]
  exact hRead
/-- Stores write the encoded value to the addressed slot and preserve the pointer return. -/
theorem pointerStoresWriteOneBasedElements_proven : PointerStoresWriteOneBasedElements := by
  unfold PointerStoresWriteOneBasedElements
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T V I _inst codec convert toInt heap pointer value index slot typed stored
      hConvert hIndex hValid hStore
    have hPair : pointerSet codec heap pointer typed slot oneI64 = (stored, pointer) := by
      simpa [unsafeStoreTyped, hConvert, hIndex, bind, Except.bind,
        pure, Except.pure, Functor.map, Except.map] using hStore
    have hFirst := congrArg Prod.fst hPair
    have hMemory : stored = heap.writeBytes
        (indexedPointer codec pointer slot).address.val.toNat (codec.encode typed) := by
      simpa [pointerSet] using hFirst.symm
    have hNoWrap : (indexedPointer codec pointer slot).address.val.toNat +
        (codec.encode typed).length ≤ 2 ^ 64 := by
      rw [codec.encode_length typed]
      exact hValid.1
    have hRead := byteHeap_readBytes_writeBytes heap
      (indexedPointer codec pointer slot).address.val.toNat (codec.encode typed) hNoWrap
    rw [hMemory, ← codec.encode_length typed]
    exact hRead
  · intro T I _inst codec toInt heap pointer value index slot stored hIndex hValid hStore
    have hPair : pointerSet codec heap pointer value slot oneI64 = (stored, pointer) := by
      simpa [unsafeStoreAny, hIndex, bind, Except.bind,
        pure, Except.pure, Functor.map, Except.map] using hStore
    have hFirst := congrArg Prod.fst hPair
    have hMemory : stored = heap.writeBytes
        (indexedPointer codec pointer slot).address.val.toNat (codec.encode value) := by
      simpa [pointerSet] using hFirst.symm
    have hNoWrap : (indexedPointer codec pointer slot).address.val.toNat +
        (codec.encode value).length ≤ 2 ^ 64 := by
      rw [codec.encode_length value]
      exact hValid.1
    have hRead := byteHeap_readBytes_writeBytes heap
      (indexedPointer codec pointer slot).address.val.toNat (codec.encode value) hNoWrap
    rw [hMemory, ← codec.encode_length value]
    exact hRead
  · intro T V codec cast convert heap pointer value typed stored order hCast hValid hStore
    exact unsafeStoreAtomic_writes codec cast convert heap pointer value typed stored order
      hCast hValid hStore
  · intro T V I codec cast convert toInt heap pointer value index slot typed stored
      hCast hIndex hValid hStore
    let shifted := ptrAddI64 pointer (codec.elementSize * (slot - oneI64))
    have hPointer : shifted = indexedPointer codec pointer slot := rfl
    have hValidShifted : heap.validRange shifted.address.val.toNat codec.elementSize.val.toNat := by
      simpa [hPointer] using hValid
    have hAtomic : unsafeStoreAtomic codec cast convert shifted heap value .seqCst =
        .ok (stored, shifted) := by
      simpa [unsafeStoreAtomicIndex, hIndex, shifted, bind, Except.bind,
        pure, Except.pure, Functor.map, Except.map] using hStore
    have hRead := unsafeStoreAtomic_writes codec cast convert heap shifted value typed stored
      .seqCst hCast hValidShifted hAtomic
    simpa [hPointer] using hRead

theorem pointerAtomicOperations_proven : PointerAtomicOperations := by
  unfold PointerAtomicOperations
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T X codec heap pointer operation value old order hValid hOld
    have hWritten := pointerRef_afterAtomicSet codec heap pointer (operation old value)
      order hValid
    constructor
    · simp [unsafeModify, atomicPointerModify, hOld]
    · simpa [unsafeModify, atomicPointerModify, atomicPointerSet, pointerSet,
        indexedPointer_one, hOld] using hWritten
  · intro T codec heap pointer value old order hValid hOld
    have hWritten := pointerRef_afterAtomicSet codec heap pointer value order hValid
    constructor
    · simp [unsafeSwapAny, atomicPointerSwap, hOld]
    · simpa [unsafeSwapAny, atomicPointerSwap, atomicPointerSet, pointerSet,
        indexedPointer_one, hOld] using hWritten
  · intro T codec same heap pointer expected desired old successOrder failOrder hValid hOld
    by_cases hSame : same old expected
    · have hWritten := pointerRef_afterAtomicSet codec heap pointer desired .notAtomic hValid
      have hWrite : pointerRef codec
          (heap.writeBytes pointer.address.val.toNat (codec.encode desired))
          pointer oneI64 oneI64 = desired := by
        simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hWritten
      simp [unsafeReplaceAny, atomicPointerReplace, atomicPointerSet, pointerSet,
        indexedPointer_one, hOld, hSame, hWrite]
    · simp [unsafeReplaceAny, atomicPointerReplace, hOld, hSame]
  · intro T E V codec same cast convert heap pointer expected desired typed old
      successOrder failOrder hCast hValid hOld
    have hCall : unsafeReplaceTyped codec same cast convert pointer heap expected desired
        successOrder failOrder =
      .ok (atomicPointerReplace codec same heap pointer expected typed successOrder failOrder) := by
      rcases hCast with hSome | ⟨hNone, hConvert⟩
      · simp [unsafeReplaceTyped, hSome, bind, Except.bind, pure, Except.pure]
      · simp [unsafeReplaceTyped, hNone, hConvert, bind, Except.bind, pure, Except.pure]
    constructor
    · exact hCall
    · by_cases hSame : same old expected
      · have hWritten := pointerRef_afterAtomicSet codec heap pointer typed .notAtomic hValid
        have hWrite : pointerRef codec
            (heap.writeBytes pointer.address.val.toNat (codec.encode typed))
            pointer oneI64 oneI64 = typed := by
          simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hWritten
        simp [atomicPointerReplace, atomicPointerSet, pointerSet, indexedPointer_one,
          hOld, hSame, hWrite]
      · simp [atomicPointerReplace, hOld, hSame]
  · intro T V codec cast convert heap pointer value typed old order hCast hValid hOld
    have hCall : unsafeSwapTyped codec cast convert pointer heap value order =
      .ok (atomicPointerSwap codec heap pointer typed order) := by
      rcases hCast with hSome | ⟨hNone, hConvert⟩
      · simp [unsafeSwapTyped, hSome, bind, Except.bind, pure, Except.pure]
      · simp [unsafeSwapTyped, hNone, hConvert, bind, Except.bind, pure, Except.pure]
    constructor
    · exact hCall
    · have hWritten := pointerRef_afterAtomicSet codec heap pointer typed .notAtomic hValid
      have hWrite : pointerRef codec
          (heap.writeBytes pointer.address.val.toNat (codec.encode typed))
          pointer oneI64 oneI64 = typed := by
        simpa [atomicPointerSet, pointerSet, indexedPointer_one] using hWritten
      simp [atomicPointerSwap, atomicPointerSet, pointerSet, indexedPointer_one, hOld, hWrite]

private theorem pointerRef_readsEncoded {T : Type} (codec : ByteCodec T) (heap : ByteHeap)
    (pointer : Ptr T) (index alignment : I64) (value : T)
    (hBytes : heap.readBytes (indexedPointer codec pointer index).address.val.toNat
      codec.elementSize.val.toNat = codec.encode value) :
    pointerRef codec heap pointer index alignment = value := by
  simp [pointerRef, hBytes, codec.decode_encode]

private theorem unsafeLoad_readsEncoded {T I : Type} [OfNat I 1]
    (codec : ByteCodec T) (toInt : I → PtrResult I64) (heap : ByteHeap)
    (pointer : Ptr T) (index : I) (slot : I64) (value : T)
    (hIndex : toInt index = .ok slot)
    (hBytes : heap.readBytes (indexedPointer codec pointer slot).address.val.toNat
      codec.elementSize.val.toNat = codec.encode value) :
    unsafeLoad codec toInt pointer heap index = .ok value := by
  simp [unsafeLoad, hIndex,
    pointerRef_readsEncoded codec heap pointer slot oneI64 value hBytes,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

private theorem unsafeConvertMemoryRef_address {T : Type} (reference : PointerMemoryRef T) :
    (unsafeConvertMemoryRef (S := T) reference).address =
      pointerMemoryRefAddress reference := by
  by_cases h : reference.mem.arrayElement == 2 || reference.mem.layoutBytes.val == 0
  · simp [unsafeConvertMemoryRef, unsafeConvertMemoryRefCvoid, unsafeConvertMemoryCvoid,
      convertPtrType, pointerMemoryRefAddress, h]
  · simp [unsafeConvertMemoryRef, unsafeConvertMemoryRefCvoid, unsafeConvertMemoryCvoid,
      convertPtrType, pointerMemoryRefAddress, h]

theorem pointerMemoryReferenceOffset_proven : PointerMemoryReferenceOffset := by
  unfold PointerMemoryReferenceOffset
  refine ⟨?_, ?_⟩
  · intro T memory codec heap value _hValid hBytes
    have hRead : heap.readBytes
        (indexedPointer codec (unsafeConvertMemory (S := T) memory) oneI64).address.val.toNat
        codec.elementSize.val.toNat = codec.encode value := by
      simpa [unsafeConvertMemory, unsafeConvertMemoryCvoid, convertPtrType,
        indexedPointer_one] using hBytes
    exact unsafeLoad_readsEncoded codec pointerI64Result heap
      (unsafeConvertMemory (S := T) memory) oneI64 oneI64 value rfl hRead
  · intro T reference codec heap index value
    dsimp
    intro _hValid hBytes
    have hAddress := unsafeConvertMemoryRef_address reference
    have hRead : heap.readBytes
        (indexedPointer codec (unsafeConvertMemoryRef (S := T) reference) index).address.val.toNat
        codec.elementSize.val.toNat = codec.encode value := by
      simpa [indexedPointer, addPtrBytes, hAddress] using hBytes
    exact unsafeLoad_readsEncoded codec pointerI64Result heap
      (unsafeConvertMemoryRef (S := T) reference) index index value rfl hRead
theorem pointerArrayMemoryConversion_proven : PointerArrayMemoryConversion := by
  unfold PointerArrayMemoryConversion
  refine ⟨?_, ?_, ?_⟩
  · intro T reference codec heap index value _hValid hBytes
    have hRead : heap.readBytes
        (indexedPointer codec (unsafeConvertArray reference) index).address.val.toNat
        codec.elementSize.val.toNat = codec.encode value := by
      simpa [unsafeConvertArray] using hBytes
    exact unsafeLoad_readsEncoded codec pointerI64Result heap
      (unsafeConvertArray reference) index index value rfl hRead
  · intro S T sameType reference
    refine ⟨convertPtrDispatch sameType (unsafeConvertArray reference), ?_, ?_⟩
    · simp [unsafeConvertAbstractArray, unsafeConvertPtrArray,
        bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    · exact convertPtrDispatch_address sameType (unsafeConvertArray reference)
  · intro S T A sameType typeof array
    simp [unsafeConvertAbstractArray, unsafeConvertPtrArray, unsafeConvertUnsupportedArray,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map]


theorem pointerArrayElementOffset_proven : PointerArrayElementOffset := by
  intro A T pointer toLinearIndex linearIndices first elsize array index
    linear linearBase origin size base hPointer hLinear hIndices hFirst hSize
  let byteOffset := JuliaLean.base.int.mul (JuliaLean.base.int.sub linear origin) size
  let result := JuliaLean.base.pointer.ptrAddInteger int64ToUInt64 base byteOffset
  refine ⟨result, ?_, ?_⟩
  · simp [JuliaLean.base.abstractarray.pointerIndex,
      JuliaLean.base.abstractarray.memoryOffsetDense,
      hPointer, hLinear, hIndices, hFirst, hSize, byteOffset, result,
      bind, Except.bind, pure, Except.pure]
  · have hSub :
        (JuliaLean.base.int.sub linear origin).val =
          wrapInt .i64 (linear.val - origin.val) := by
      simpa [JuliaLean.base.int.sub] using
        JuliaLean.Proofs.base.int.sub_int_val linear origin
    have hMul :
        byteOffset.val =
          wrapInt .i64 ((JuliaLean.base.int.sub linear origin).val * size.val) := by
      simpa [byteOffset, JuliaLean.base.int.mul] using
        JuliaLean.Proofs.base.int.mul_int_val (JuliaLean.base.int.sub linear origin) size
    have hAddress :
        result.address.val =
          wrapInt .u64 (base.address.val + wrapInt .u64 byteOffset.val) := by
      rfl
    rw [hAddress, hMul, hSub]


theorem pointerUnsafeWrapAliases_proven : PointerUnsafeWrapAliases := by
  unfold PointerUnsafeWrapAliases
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T N calls pointer dims own
    simpa [unsafeWrapArrayTuple] using calls.arrayTuple_result pointer dims own
  · intro T I calls pointer dimension toSize own
    simpa [unsafeWrapArrayInteger] using
      calls.arrayInteger_result pointer (toSize dimension) own
  · intro T calls kind pointer dims own
    have h := calls.memoryTuple_result kind pointer (int64ToUInt64 dims.first) own
    refine ⟨?_, ?_, ?_⟩
    · simpa [unsafeWrapMemoryTuple] using h.1
    · exact h.2.2.2
    · simpa [unsafeWrapMemoryTuple] using h.2.1
  · intro T I calls kind pointer dimension toSize own
    have h := calls.memoryInteger_result kind pointer (toSize dimension) own
    exact ⟨h.1, h.2.2.2, h.2.1⟩
  · intro T N calls codec heap pointer dims own index
    have hAddress : (unsafeWrapArrayTuple calls pointer dims own).pointer.address =
        pointer.address := by
      have hCall := calls.arrayTuple_result pointer dims own
      simpa [unsafeWrapArrayTuple] using hCall.1
    simp [unsafeLoad, pointerI64Result, pointerRef, indexedPointer, addPtrBytes,
      hAddress, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · intro T I N calls convertDims pointer dims own converted hDims
    simp [unsafeWrapGenericDims, hDims, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map]
  · intro T calls convertDims kind pointer dims own converted hDims
    simp [unsafeWrapGenericDims, hDims, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map]

theorem pointerLoadsReadOneBasedElements_proven : PointerLoadsReadOneBasedElements := by
  unfold PointerLoadsReadOneBasedElements
  refine ⟨?_, ?_, ?_⟩
  · intro T I inst codec toInt heap pointer index slot value hIndex _hValid hBytes
    exact unsafeLoad_readsEncoded codec toInt heap pointer index slot value hIndex hBytes
  · intro T I inst codec toInt heap pointer index slot value hIndex _hValid hBytes
    have hPointer :
        ptrAddI64 pointer (codec.elementSize * (slot - oneI64)) =
          indexedPointer codec pointer slot := rfl
    have hRead : heap.readBytes
        (indexedPointer codec (ptrAddI64 pointer (codec.elementSize * (slot - oneI64)))
          oneI64).address.val.toNat codec.elementSize.val.toNat = codec.encode value := by
      simpa [indexedPointer_one, hPointer] using hBytes
    simp [unsafeLoadAtomicIndex, unsafeLoadAtomic, hIndex, atomicPointerRef, pointerRef,
      indexedPointer_one, hPointer, hBytes, codec.decode_encode,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · intro T codec heap pointer value _hValid hBytes
    have hRead : heap.readBytes (indexedPointer codec pointer oneI64).address.val.toNat
        codec.elementSize.val.toNat = codec.encode value := by
      simpa [indexedPointer_one] using hBytes
    change (Except.ok (atomicPointerRef codec heap pointer .seqCst) : PtrResult T) =
      (Except.ok value : PtrResult T)
    exact congrArg (Except.ok : T → PtrResult T)
      (pointerRef_readsEncoded codec heap pointer oneI64 oneI64 value hRead)

theorem pointerObjectReferenceBehavior_proven : PointerObjectReferenceBehavior := by
  unfold PointerObjectReferenceBehavior
  refine ⟨?_, ?_, ?_⟩
  · intro A calls value hMutable
    exact ⟨by simp [pointerFromObjref, hMutable], calls.objectAddress_pointsTo value⟩
  · intro A calls value hImmutable
    simp [pointerFromObjref, hImmutable]
  · intro A T calls pointer value hPointsTo
    exact calls.pointer_returns_object (convertPtrType pointer) value hPointsTo

end JuliaLean.Proofs.base.pointer

namespace JuliaLean.ChatGPT.Batch4.Group12
open JuliaLean.Proofs.base.pointer

/-- pointer-address-arithmetic: Pointer comparisons use unsigned address order and pointer differences and byte offsets wrap in the UInt64 address space. -/
theorem PointerAddressArithmetic_proven : JuliaLean.Proofs.base.pointer.PointerAddressArithmetic :=
  JuliaLean.Proofs.base.pointer.pointerAddressArithmetic_proven

/-- pointer-integer-conversions: Converting a pointer to an integer or another pointer type preserves its 64-bit address pattern; signed conversion reinterprets those bits. -/
theorem PointerIntegerConversions_proven : JuliaLean.Proofs.base.pointer.PointerIntegerConversions :=
  JuliaLean.Proofs.base.pointer.pointerIntegerConversions_proven

/-- pointer-cconvert-symbol-roots: cconvert yields the String or backing object that callers keep alive during pointer use, and symbol conversions use the symbol-name address. -/
theorem PointerCconvertSymbolRoots_proven : JuliaLean.Proofs.base.pointer.PointerCconvertAndSymbolConversion :=
  JuliaLean.Proofs.base.pointer.pointerCconvertAndSymbolConversion_proven

/-- pointer-array-memory-conversion: Array pointer conversion keeps the same storage address, reinterprets only the pointer element type, and rejects unsupported abstract arrays. -/
theorem PointerArrayMemoryConversion_proven : JuliaLean.Proofs.base.pointer.PointerArrayMemoryConversion :=
  JuliaLean.Proofs.base.pointer.pointerArrayMemoryConversion_proven

/-- pointer-array-index-offset: For dense arrays, pointer(A,i) uses wrapped Int subtraction and multiplication, then wrapping UInt64 pointer addition, to advance by the linear-index difference times elsize(A). -/
theorem PointerArrayIndexOffset_proven : JuliaLean.Proofs.base.pointer.PointerArrayElementOffset :=
  JuliaLean.Proofs.base.pointer.pointerArrayElementOffset_proven

/-- pointer-unsafe-wrap-alias: unsafe_wrap creates a view over the supplied bytes without copying and preserves the requested dimensions and ownership flag. -/
theorem PointerUnsafeWrapAlias_proven : JuliaLean.Proofs.base.pointer.PointerUnsafeWrapAliases :=
  JuliaLean.Proofs.base.pointer.pointerUnsafeWrapAliases_proven

/-- pointer-unsafe-load-index: unsafe_load reads the requested one-based element, whose byte address is p + (i-1)*elsize(T), including the atomic-order overload. -/
theorem PointerUnsafeLoadIndex_proven : JuliaLean.Proofs.base.pointer.PointerLoadsReadOneBasedElements :=
  JuliaLean.Proofs.base.pointer.pointerLoadsReadOneBasedElements_proven

/-- pointer-unsafe-store-index: unsafe_store! writes the converted value to the requested one-based element, using (i-1)*elsize(T) byte offsets for ordered stores. -/
theorem PointerUnsafeStoreIndex_proven : JuliaLean.Proofs.base.pointer.PointerStoresWriteOneBasedElements :=
  JuliaLean.Proofs.base.pointer.pointerStoresWriteOneBasedElements_proven

/-- pointer-atomic-modify-replace-swap: Atomic modification returns the old and new values, replacement stores only when old === expected, and swap returns the old value. -/
theorem PointerAtomicModifyReplaceSwap_proven : JuliaLean.Proofs.base.pointer.PointerAtomicOperations :=
  JuliaLean.Proofs.base.pointer.pointerAtomicOperations_proven

/-- pointer-object-reference-mutability: A valid object pointer converts back to its object, and pointer_from_objref rejects immutable objects while returning a mutable object's address. -/
theorem PointerObjectReferenceMutability_proven : JuliaLean.Proofs.base.pointer.PointerObjectReferenceBehavior :=
  JuliaLean.Proofs.base.pointer.pointerObjectReferenceBehavior_proven

end JuliaLean.ChatGPT.Batch4.Group12

namespace JuliaLean.Proofs.base.pointer

open JuliaLean.Registry
/-- Registry entries for the source-mirrored `base/pointer.jl` model. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "pointer-address-arithmetic", juliaFile := "base/pointer.jl",
    juliaFns := ["isequal(::Ptr,::Ptr)", "isless(::Ptr{T},::Ptr{T})", "==(::Ptr,::Ptr)", "<(::Ptr,::Ptr)",
      "-(::Ptr,::Ptr)", "-%(::Ptr,::Ptr)", "+(::Ptr,::Integer)", "-(::Ptr,::Integer)",
      "+(::Integer,::Ptr)", "unsigned(::Ptr)", "signed(::Ptr)"],
    statement := "Pointer comparisons use unsigned address order and pointer differences and byte offsets wrap in the UInt64 address space.",
    source := "invariant; base/pointer.jl:307-320; src/runtime_intrinsics.c:1848-1853",
    status := .proven, prop := ``PointerAddressArithmetic, thm := some ``JuliaLean.Proofs.base.pointer.pointerAddressArithmetic_proven },
  { id := "pointer-integer-conversions", juliaFile := "base/pointer.jl",
    juliaFns := ["convert(::Type{T<:Integer},::Ptr)", "convert(::Type{Ptr{T}},::Union{Int,UInt})",
      "convert(::Type{Ptr{T}},::Ptr{T})", "convert(::Type{Ptr{T}},::Ptr)", "unsigned(::Ptr)", "signed(::Ptr)"],
    statement := "Converting a pointer to an integer or another pointer type preserves its 64-bit address pattern; signed conversion reinterprets those bits.",
    source := "invariant; base/pointer.jl:23,26,29-30,319-320",
    status := .proven, prop := ``PointerIntegerConversions, thm := some ``JuliaLean.Proofs.base.pointer.pointerIntegerConversions_proven },
  { id := "pointer-cconvert-symbol-roots", juliaFile := "base/pointer.jl",
    juliaFns := ["cconvert(::Type{Ptr{UInt8}},::AbstractString)", "cconvert(::Type{Ptr{Int8}},::AbstractString)",
      "unsafe_convert(::Type{Ptr{UInt8}},::Symbol)", "unsafe_convert(::Type{Ptr{Int8}},::Symbol)",
      "cconvert(::Type{<:Ptr},::Array)", "cconvert(::Type{<:Ptr},::GenericMemory)"],
    statement := "cconvert yields the String or backing object that callers keep alive during pointer use, and symbol conversions use the symbol-name address.",
    source := "unsafe_convert docstring and base/pointer.jl:58-63,71",
    status := .proven, prop := ``PointerCconvertAndSymbolConversion, thm := some ``JuliaLean.Proofs.base.pointer.pointerCconvertAndSymbolConversion_proven },
  { id := "pointer-memoryref-byte-offset", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{Cvoid}},::GenericMemory)", "unsafe_convert(::Type{Ptr{T}},::GenericMemory)",
      "unsafe_convert(::Type{Ptr{Cvoid}},::GenericMemoryRef)", "unsafe_convert(::Type{Ptr{T}},::GenericMemoryRef)"],
    statement := "GenericMemory and GenericMemoryRef pointers load the bytes encoded at the memory base or the reference's layout-derived element address.",
    source := "invariant; base/pointer.jl:72-88",
    status := .proven, prop := ``PointerMemoryReferenceOffset, thm := some ``pointerMemoryReferenceOffset_proven },
  { id := "pointer-array-memory-conversion", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{S}},::AbstractArray{T})", "unsafe_convert(::Type{Ptr{T}},::Array{T})",
      "unsafe_convert(::Type{Ptr{T}},::AbstractArray{T})"],
    statement := "Array pointer conversion keeps the same storage address, reinterprets only the pointer element type, and rejects unsupported abstract arrays.",
    source := "unsafe_convert docstring and base/pointer.jl:64-66",
    status := .proven, prop := ``PointerArrayMemoryConversion, thm := some ``JuliaLean.Proofs.base.pointer.pointerArrayMemoryConversion_proven },
  { id := "pointer-array-index-offset", juliaFile := "base/pointer.jl",
    juliaFns := ["+(::Ptr,::Integer)", "pointer(::AbstractArray{T},::Integer) [base/abstractarray.jl:1280-1283]"],
    statement := "For dense arrays, pointer(A,i) uses wrapped Int subtraction and multiplication, then wrapping UInt64 pointer addition, to advance by the linear-index difference times elsize(A).",
    source := "base/abstractarray.jl:1280-1286; base/pointer.jl:315",
    status := .proven, prop := ``PointerArrayElementOffset, thm := some ``JuliaLean.Proofs.base.pointer.pointerArrayElementOffset_proven },
  { id := "pointer-unsafe-wrap-alias", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_wrap(::Array,::Ptr,::NTuple)", "unsafe_wrap(::Array,::Ptr,::Integer)",
      "unsafe_wrap(::GenericMemory,::Ptr,::Tuple{Int})", "unsafe_wrap(::GenericMemory,::Ptr,::Integer)",
      "unsafe_wrap(::Union{Array,GenericMemory},::Ptr,::NTuple{N,<:Integer})"],
    statement := "unsafe_wrap creates a view over the supplied bytes without copying and preserves the requested dimensions and ownership flag.",
    source := "unsafe_wrap docstring; base/pointer.jl:91-128",
    status := .proven, prop := ``PointerUnsafeWrapAliases, thm := some ``JuliaLean.Proofs.base.pointer.pointerUnsafeWrapAliases_proven },
  { id := "pointer-unsafe-load-index", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_load(::Ptr,::Integer)", "unsafe_load(::Ptr,::Symbol)", "unsafe_load(::Ptr,::Integer,::Symbol)"],
    statement := "unsafe_load reads the requested one-based element, whose byte address is p + (i-1)*elsize(T), including the atomic-order overload.",
    source := "unsafe_load docstring; base/pointer.jl:151-155",
    status := .proven, prop := ``PointerLoadsReadOneBasedElements, thm := some ``JuliaLean.Proofs.base.pointer.pointerLoadsReadOneBasedElements_proven },
  { id := "pointer-unsafe-store-index", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_store!(::Ptr{Any},x,::Integer)", "unsafe_store!(::Ptr{T},x,::Integer)",
      "unsafe_store!(::Ptr{T},x,::Symbol)", "unsafe_store!(::Ptr,x,::Integer,::Symbol)"],
    statement := "unsafe_store! writes the converted value to the requested one-based element, using (i-1)*elsize(T) byte offsets for ordered stores.",
    source := "unsafe_store! docstring; base/pointer.jl:177-182",
    status := .proven, prop := ``PointerStoresWriteOneBasedElements, thm := some ``JuliaLean.Proofs.base.pointer.pointerStoresWriteOneBasedElements_proven },
  { id := "pointer-atomic-modify-replace-swap", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_modify!(::Ptr,op,x,::Symbol)", "unsafe_replace!(::Ptr{T},expected,desired,::Symbol,::Symbol)",
      "unsafe_replace!(::Ptr{Any},expected,desired,::Symbol,::Symbol)", "unsafe_swap!(::Ptr{Any},x,::Symbol)",
      "unsafe_swap!(::Ptr{T},x,::Symbol)"],
    statement := "Atomic modification returns the old and new values, replacement stores only when old === expected, and swap returns the old value.",
    source := "unsafe_modify!, unsafe_replace!, and unsafe_swap! docstrings; base/pointer.jl:207-273",
    status := .proven, prop := ``PointerAtomicOperations, thm := some ``JuliaLean.Proofs.base.pointer.pointerAtomicOperations_proven },
  { id := "pointer-object-reference-mutability", juliaFile := "base/pointer.jl",
    juliaFns := ["unsafe_pointer_to_objref(::Ptr)", "pointer_from_objref(::Any)"],
    statement := "A valid object pointer converts back to its object, and pointer_from_objref rejects immutable objects while returning a mutable object's address.",
    source := "unsafe_pointer_to_objref and pointer_from_objref docstrings; base/pointer.jl:285,299-303",
    status := .proven, prop := ``PointerObjectReferenceBehavior, thm := some ``JuliaLean.Proofs.base.pointer.pointerObjectReferenceBehavior_proven },
]

end JuliaLean.Proofs.base.pointer
