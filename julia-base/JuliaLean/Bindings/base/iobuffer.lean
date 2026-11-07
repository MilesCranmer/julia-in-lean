import JuliaLean.base.iobuffer
import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.cancellation
import JuliaLean.base.genericmemory
import JuliaLean.base.io
import JuliaLean.base.pointer
import JuliaLean.base.subarray
import JuliaLean.base.indices

/-!
# IOBuffer bind7

The write dispatch is instantiated for dense `Array`/`Memory` byte vectors and for `SubArray`
views backed by those vectors. Other user-defined `AbstractVector{UInt8}` values remain a named
gap.
-/

namespace JuliaLean.Bindings.base.iobuffer

open JuliaLean

abbrev I := JuliaLean.base.iobuffer.I
abbrev U := JuliaLean.base.iobuffer.U
abbrev Byte := JuliaLean.base.iobuffer.Byte

inductive Error (E : Type) where
  | buffer (error : JuliaLean.base.iobuffer.IOErr)
  | array (error : JuliaLean.base.array.Error)
  | pointer (error : JuliaLean.base.pointer.PointerError)
  | io (error : JuliaLean.base.io.Error)
  | cancel (error : JuliaLean.base.cancellation.CancelError)
  | external (error : E)
  | undefinedBehavior (operation : String)

def RuntimeM (E World A : Type) :=
  World → Option (Except (Error E × World) (A × World))

def getWorld {E World : Type} : RuntimeM E World World :=
  fun world => some (.ok (world, world))

def setWorld {E World : Type} (next : World) : RuntimeM E World Unit :=
  fun _ => some (.ok ((), next))

export JuliaLean.base.iobuffer (BufferHeap findBufferFields replaceBufferFields)
instance {E World : Type} : Monad (RuntimeM E World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => do
    match ← action world with
    | .error failure => pure (.error failure)
    | .ok (value, world) => next value world

instance {E World : Type} : MonadExceptOf (Error E) (RuntimeM E World) where
  throw failure := fun world => some (.error (failure, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (failure, world)) => handler failure world

private def tryCatchMapped {E World A X : Type} (project : Error E → Option X)
    (action : RuntimeM E World A) (handler : X → RuntimeM E World A) : RuntimeM E World A :=
  fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (failure, world)) =>
      match project failure with
      | some error => handler error world
      | none => some (.error (failure, world))

instance {E World : Type} : MonadExceptOf JuliaLean.base.iobuffer.IOErr (RuntimeM E World) where
  throw error := fun world => some (.error (.buffer error, world))
  tryCatch action handler := tryCatchMapped (fun | .buffer error => some error | _ => none) action handler

instance {E World : Type} : MonadExceptOf JuliaLean.base.array.Error (RuntimeM E World) where
  throw error := fun world => some (.error (.array error, world))
  tryCatch action handler := tryCatchMapped (fun | .array error => some error | _ => none) action handler

instance {E World : Type} : MonadExceptOf JuliaLean.base.pointer.PointerError (RuntimeM E World) where
  throw error := fun world => some (.error (.pointer error, world))
  tryCatch action handler := tryCatchMapped (fun | .pointer error => some error | _ => none) action handler

instance {E World : Type} : MonadExceptOf JuliaLean.base.io.Error (RuntimeM E World) where
  throw error := fun world => some (.error (.io error, world))
  tryCatch action handler := tryCatchMapped (fun | .io error => some error | _ => none) action handler

instance {E World : Type} : MonadExceptOf JuliaLean.base.cancellation.CancelError (RuntimeM E World) where
  throw error := fun world => some (.error (.cancel error, world))
  tryCatch action handler := tryCatchMapped (fun | .cancel error => some error | _ => none) action handler

instance {E World : Type} : MonadExceptOf E (RuntimeM E World) where
  throw error := fun world => some (.error (.external error, world))
  tryCatch action handler := tryCatchMapped (fun | .external error => some error | _ => none) action handler

/-- One lift for the source model's pure IOBuffer result type. -/
def liftBufferResult {E World A : Type} : Except JuliaLean.base.iobuffer.IOErr A → RuntimeM E World A
  | .ok value => pure value
  | .error error => throwThe (Error E) (.buffer error)

/-- One lift for the installed mutable IO model. Its World is the shared runtime World. -/
def liftIOModel {E World A : Type} (action : JuliaLean.base.io.M World A) : RuntimeM E World A :=
  fun world =>
    match action world with
    | none => none
    | some (.ok (value, world)) => some (.ok (value, world))
    | some (.error (error, world)) => some (.error (.io error, world))

/-- One lift for cancellation operations that use their own error sum over the shared World. -/
def liftCancellationModel {E World A : Type}
    (action : JuliaLean.base.cancellation.M World A) : RuntimeM E World A :=
  fun world =>
    match action world with
    | none => none
    | some (.ok (value, world)) => some (.ok (value, world))
    | some (.error (error, world)) => some (.error (.cancel error, world))
/-- IOBuffer's cancellation check calls the installed entry-check method and preserves World
mutations and cancellation failures. -/
def precheckCancelArg {E World Source Task Scope : Type}
    (scopeOps : JuliaLean.base.cancellation.ScopeOps World Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps World Source)
    (slow : Task → JuliaLean.base.cancellation.M World
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M World Unit)
    (cancel : JuliaLean.base.cancellation.CancelTokenArg Source) : RuntimeM E World Unit := do
  let _ ← liftCancellationModel
    (JuliaLean.base.cancellation.precheckCancelArg scopeOps tokenOps slow handleCancellation cancel)
  pure ()

/-- One lift for pointer operations, which return the installed pointer error sum. -/
def liftPointerResult {E World A : Type}
    (result : JuliaLean.base.pointer.PtrResult A) : RuntimeM E World A :=
  match result with
  | .ok value => pure value
  | .error error => throwThe (Error E) (.pointer error)

export JuliaLean.base.iobuffer (ObjectRuntime byteCodec loadBytePointer storeBytePointer
  copyBytePointer setMemoryByte setArrayByte vectorBounds getArrayByte copyVector
  fillVectorRange VectorMethods arrayVectorMethods bindStorage)

/-- IOBuffer fields are stored in the shared heap. Invalid references are C undefined behavior. -/
def bindAccess {E Ref Data Other : Type}
    (calls : ObjectRuntime (RuntimeM E (BufferHeap Ref Data Other)) Ref Data) :
    JuliaLean.base.iobuffer.Access (RuntimeM E (BufferHeap Ref Data Other)) Ref Data :=
  JuliaLean.base.iobuffer.bindHeapAccess getWorld setWorld
    (fun msg => throwThe (Error E) (.undefinedBehavior msg)) calls

/-- Pointer models read and write the same ByteHeap used by the array runtime. -/
def bindPointerHeap {E Ref Data Other : Type} :
    JuliaLean.base.iobuffer.HeapAccess (RuntimeM E (BufferHeap Ref Data Other)) :=
  JuliaLean.base.iobuffer.bindHeapPointerHeap getWorld setWorld
/-- `IOBuffer(::Vector{UInt8})` uses Array's installed reference, memory, offset, length, and
memory-length operations (`iobuffer.jl:141-161`). -/
def genericIOBufferVector {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Vector Memory P N : Type} (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (conversions : JuliaLean.base.iobuffer.IntegerConversions N) (data : Vector)
    (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m Ref :=
  JuliaLean.base.iobuffer.source_GenericIOBuffer_Vector access arrayOps.ref
    (fun reference => pure reference.mem)
    (fun reference => pure (arrayOps.offset reference))
    arrayOps.length arrayOps.memLength
    (fun value => JuliaLean.base.iobuffer.liftNative (conversions.toNative value))
    data readable writable seekable append maxsize truncate

/-- Exact generic one-based AbstractVector constructor (`iobuffer.jl:134-137`), with selected
`firstindex` and `length` methods and installed integer conversions. -/
def genericIOBufferAbstractVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {Ref Data Index Length N : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (firstIndex : Data → m Index) (indexConversion : JuliaLean.base.iobuffer.IntegerConversions Index)
    (length : Data → m Length) (lengthConversion : JuliaLean.base.iobuffer.IntegerConversions Length)
    (maxConversion : JuliaLean.base.iobuffer.IntegerConversions N) (data : Data)
    (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m Ref :=
  JuliaLean.base.iobuffer.source_GenericIOBuffer access firstIndex
    (fun index => JuliaLean.base.iobuffer.liftNative (indexConversion.toNative index))
    length
    (fun value => JuliaLean.base.iobuffer.liftNative (lengthConversion.toNative value))
    (fun value => JuliaLean.base.iobuffer.liftNative (maxConversion.toNative value))
    data readable writable seekable append maxsize truncate

/-- Top-level `IOBuffer(data; ...)` binds the installed constructor and integer-conversion adapter. -/
def ioBufferData {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {Data Hint N Ref Index Length : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (firstIndex : Data → m Index) (toIntIndex : Index → m I)
    (length : Data → m Length) (toIntLength : Length → m I)
    (sizehint : Data → Hint → m Unit)
    (conversions : JuliaLean.base.iobuffer.IntegerConversions N)
    (data : Data) (read write append truncate : Option Bool)
    (maxsize : N) (hint : Option Hint) : m Ref :=
  JuliaLean.base.iobuffer.iobufferData access firstIndex toIntIndex length toIntLength
    sizehint conversions data read write append truncate maxsize hint

/-- `IOBuffer()` binds StringMemory allocation and constructor conversions. -/
def emptyIOBuffer {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {N Hint StringRef Memory Length Ref : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (maximum : JuliaLean.base.iobuffer.IntegerConversions N)
    (hintConversion : JuliaLean.base.iobuffer.IntegerConversions Hint)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (length : Memory → m Length) (toLength : Length → m I)
    (read write append truncate : Option Bool) (maxsize : N) (hint : Option Hint) : m Ref :=
  JuliaLean.base.iobuffer.iobufferEmpty access maximum hintConversion allocateString
    stringToMemory length toLength read write append truncate maxsize hint

/-- `PipeBuffer(maxsize::Integer)` binds the installed constructor and conversion adapter. -/
def pipeBufferMaxsize {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {N StringRef Memory Ref : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (conversions : JuliaLean.base.iobuffer.IntegerConversions N)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (length : Memory → m I) (toLength : I → m I) (maxsize : N) : m Ref :=
  JuliaLean.base.iobuffer.pipeBufferN access conversions allocateString stringToMemory
    length toLength maxsize

/-- StringMemory allocation is the installed `stringN` followed by `unsafeWrapMemory`
(`strings/string.jl:184-185`, `195`). Only the C allocation and String-to-Memory runtime calls
remain typed external calls. -/
def stringMemory {m : Type → Type} [Monad m] {N StringRef Memory : Type}
    (toCsize : N → m U) (allocateString : U → m StringRef)
    (stringToMemory : StringRef → m Memory) (count : N) : m Memory :=
  JuliaLean.base.iobuffer.source_StringMemory toCsize allocateString stringToMemory count

/-- Exact `take!(::GenericIOBuffer)` method (`iobuffer.jl:731-753`). `readBytes` is the installed
`readbytes!` path; the adapter returns the destination vector as `read!` does. -/
def takeGeneric {m : Type → Type} [Monad m] {Ref Data Vector : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data) (allocate : I → m Vector)
    (copyTo : Vector → I → Data → I → I → m Vector)
    (readBytes : Ref → Vector → m I) (ref : Ref) : m Vector :=
  JuliaLean.base.iobuffer.source_take_generic access allocate copyTo
    (fun ref vector => do let _ ← readBytes ref vector; pure vector) ref

/-- Installed `StringVector(::Int)` path. String allocation and the Array object constructor are
runtime calls; the byte length is read from the runtime Memory object. -/
private def allocateStringVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Memory P StringRef Vector : Type}
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (newArray : JuliaLean.base.genericmemory.GenericMemoryRef Memory P → List I → m Vector)
    (length : I) : m Vector :=
  JuliaLean.base.iobuffer.source_StringVector
    (fun count : I => JuliaLean.base.iobuffer.liftNative
      (JuliaLean.base.int.convert .u64 count))
    allocateString stringToMemory memoryOps.memoryref memoryLength newArray length

/-- Installed Array `_wrap` check for a memory reference. `memoryLength` reads the immutable
length field from the runtime Memory object (`array.jl:3236-3242`). -/
private def wrapMemoryVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Memory P Vector : Type}
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I) (checkedDims : List I → m I)
    (newArray : JuliaLean.base.genericmemory.GenericMemoryRef Memory P → List I → m Vector)
    (memory : Memory) (first length : I) : m Vector := do
  let reference ← memoryOps.memoryrefAt memory first
  let wrap := JuliaLean.base.array.wrapCheck
    arrayOps.memory memoryLength arrayOps.offset checkedDims
  JuliaLean.base.array.wrapRefLength pure wrap newArray reference length

/-- Installed Array `_wrap` check for a memory reference already selected by `MemoryRef`. -/
private def wrapMemoryRef {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Memory P Vector : Type}
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryLength : Memory → I) (checkedDims : List I → m I)
    (reference : JuliaLean.base.genericmemory.GenericMemoryRef Memory P)
    (dims : List I) : m (JuliaLean.base.genericmemory.GenericMemoryRef Memory P) :=
  JuliaLean.base.array.wrapCheck
    arrayOps.memory memoryLength arrayOps.offset checkedDims reference dims

/-- Installed `copyto!(::Array{UInt8}, ::Memory{UInt8})` composition. -/
private def copyMemoryToVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Vector Memory P Pointer Token : Type}
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (copyOps : JuliaLean.base.genericmemory.MemoryCopyOps m Memory P I I I I Pointer Token)
    (destination : Vector) (destinationIndex : I)
    (source : Memory) (sourceIndex count : I) : m Vector :=
  JuliaLean.base.array.copytoImpl
    (fun n : I => pure (decide (n.val = 0)))
    (fun n : I => pure (decide (n.val > 0)))
    arrayOps.length arrayOps.memLength
    (vectorBounds arrayOps) memoryOps.checkbounds
    (fun length index => pure (JuliaLean.base.int.sub length index))
    (fun length index => pure (JuliaLean.base.int.sub length index))
    (fun difference count => pure (JuliaLean.base.int.add difference count))
    (fun difference count => pure (JuliaLean.base.int.add difference count))
    (fun copied remaining => pure (JuliaLean.base.int.le copied remaining))
    (fun copied remaining => pure (JuliaLean.base.int.le copied remaining))
    (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
    pure pure pure
    (fun vector index => do
      let reference ← arrayOps.ref vector
      arrayOps.shiftref reference (JuliaLean.base.int.sub index JuliaLean.base.iobuffer.one))
    (fun memory index => memoryOps.memoryrefAt memory index)
    (fun destination source count => do
      let _ ← JuliaLean.base.genericmemory.unsafeCopytoGenericRefs
        memoryOps memoryOps copyOps (fun byte => pure byte) (fun byte => pure byte)
        false copyOps.memoryrefoffset (isTrue rfl) destination source count
      pure ())
    destination destinationIndex source sourceIndex count
export JuliaLean.base.iobuffer (copyStringMemory takeStringMemory)
/-- `_unsafe_take!(::IOBuffer)` uses StringMemory, GenericMemory, and Array models directly. -/
def unsafeTake {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Ref Memory Vector P StringRef : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (checkedDims : List I → m I)
    (newArray : JuliaLean.base.genericmemory.GenericMemoryRef Memory P → List I → m Vector)
    (ref : Ref) : m Vector :=
  JuliaLean.base.iobuffer.source_unsafe_take access
    (JuliaLean.base.iobuffer.source_StringMemory
      (fun size : I => JuliaLean.base.iobuffer.liftNative
        (JuliaLean.base.int.convert .u64 size))
      allocateString stringToMemory JuliaLean.base.iobuffer.zero)
    memoryOps.memoryrefAt
    (wrapMemoryRef arrayOps memoryLength checkedDims)
    newArray pure ref


/-- Exact `_unsafe_takestring!(::IOBuffer)` body (`iobuffer.jl:795-809`), using the installed
StringMemory, GenericMemory copy, and `unsafe_takestring` bodies. String allocation and conversion
remain runtime calls. -/
def unsafeTakeString {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Ref Memory P Pointer Token StringRef : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I)
    (copyOps : JuliaLean.base.genericmemory.MemoryCopyOps m Memory P I I I I Pointer Token)
    (emptyString : m StringRef) (memoryToString : Memory → I → m StringRef)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (ref : Ref) : m StringRef :=
  JuliaLean.base.iobuffer.source_unsafe_takestring access
    (fun first last => pure (JuliaLean.base.iobuffer.rangeLength first last))
    (fun first last => pure (JuliaLean.base.int.lt last first))
    emptyString memoryToString
    (fun count : U => stringMemory (fun size : U => pure size)
      allocateString stringToMemory count)
    (copyStringMemory memoryOps copyOps)
    (takeStringMemory memoryLength emptyString memoryToString)
    ref

/-- Exact `takestring!(::GenericIOBuffer)` forwarding method (`iobuffer.jl:862`). -/
def takeStringGeneric {m : Type → Type} [Monad m] {Ref Vector StringRef : Type}
    (take : Ref → m Vector) (convertString : Vector → m StringRef) (ref : Ref) : m StringRef :=
  JuliaLean.base.iobuffer.source_takestring_generic take convertString ref

/-- Exact `read(io::GenericIOBuffer)` body (`iobuffer.jl:977`). `readBytes` is installed
`readbytes!` through the selected Array operations. -/
def readAll {m : Type → Type} [Monad m] {Ref Data Array : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data) (allocate : I → m Array)
    (readBytes : Ref → Array → m I) (ref : Ref) : m Array :=
  JuliaLean.base.iobuffer.source_read_all access allocate
    (fun ref destination => do let _ ← readBytes ref destination; pure destination) ref

/-- Exact `read(io::GenericIOBuffer, n::Integer)` body (`iobuffer.jl:982`). `readBytes` is the
installed `readbytes!` path. -/
def readN {m : Type → Type} [Monad m] {Ref Data Array N Count : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (minCount : N → I → m Count) (allocate : Count → m Array)
    (readBytes : Ref → Array → m I) (ref : Ref) (count : N) : m Array :=
  JuliaLean.base.iobuffer.source_read_n access minCount allocate
    (fun ref destination => do let _ ← readBytes ref destination; pure destination) ref count

/-- Julia selects one of the two `unsafe_read!` methods by data type. -/
inductive UnsafeReadMethod where
  | abstractVector
  | denseArray
  deriving DecidableEq, Repr

/-- `unsafe_read!(::AbstractVector{UInt8})` uses the installed pointer store. -/
def unsafeReadVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {Data : Type}
    (sourceIndex : I → U → m I) (getindex : Data → I → m Byte)
    (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (destination : JuliaLean.base.pointer.Ptr Byte) (data : Data) (start : I) (count : U) :
    m Unit :=
  JuliaLean.base.iobuffer.source_unsafe_read_vector sourceIndex getindex
    (fun pointer byte index => storeBytePointer heap pointer byte index)
    destination data start count

/-- `unsafe_read!(::DenseBytes)` uses the installed Array copy and pointer-copy methods. -/
def unsafeReadDense {m : Type → Type} [Monad m] {Data : Type}
    (pointerForData : Data → I → m (JuliaLean.base.pointer.Ptr Byte))
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (destination : JuliaLean.base.pointer.Ptr Byte) (data : Data) (start : I) (count : U) :
    m Unit :=
  JuliaLean.base.iobuffer.source_unsafe_read_dense pointerForData
    (fun destination source count => copyBytePointer memmove destination source count)
    destination data start count

/-- Generic `unsafe_read` binds its data-type dispatch to the installed vector and dense bodies. -/
def unsafeRead {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    {Ref Data : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (method : UnsafeReadMethod) (sourceIndex : I → U → m I)
    (getindex : Data → I → m Byte) (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (pointerForData : Data → I → m (JuliaLean.base.pointer.Ptr Byte))
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (ref : Ref) (destination : JuliaLean.base.pointer.Ptr Byte) (count : U) : m Unit :=
  JuliaLean.base.iobuffer.source_unsafe_read access
    (fun destination data start count =>
      match method with
      | .abstractVector =>
          unsafeReadVector sourceIndex getindex heap destination data start count
      | .denseArray => unsafeReadDense pointerForData memmove destination data start count)
    ref destination count

/-- Installed `readbytes!` body (`iobuffer.jl:961-964`) with selected Array operations. -/
def readBytesInt {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data Array : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (length : Array → m I) (resize : Array → I → m Unit)
    (checkBounds : Array → I → m Unit)
    (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (readBang : JuliaLean.base.pointer.Ptr Byte → Data → I → U → m Unit)
    (ref : Ref) (destination : Array) (count : I) : m I :=
  JuliaLean.base.iobuffer.source_readbytes_int access length resize checkBounds pointer
    readBang ref destination count

/-- Installed default-count `readbytes!` body (`iobuffer.jl:965`). -/
def readBytesDefault {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data Array N : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (length : Array → m N) (toInt : N → m I) (lengthInt : Array → m I)
    (resize : Array → I → m Unit) (checkBounds : Array → I → m Unit)
    (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (readBang : JuliaLean.base.pointer.Ptr Byte → Data → I → U → m Unit)
    (ref : Ref) (destination : Array) (count : Option N) : m I :=
  JuliaLean.base.iobuffer.source_readbytes_default access length toInt lengthInt resize
    checkBounds pointer readBang ref destination count
/-- Binds integer-count `readbytes!` to installed one-based Array methods and unsafe-read dispatch. -/
def readBytesVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    {Ref BufferData Array Memory P : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref BufferData)
    (arrayOps : JuliaLean.base.array.Storage m Array Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (methods : VectorMethods m (JuliaLean.base.genericmemory.GenericMemoryRef Memory P) Array Array)
    (method : UnsafeReadMethod) (sourceIndex : I → U → m I)
    (getindex : BufferData → I → m Byte)
    (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (pointerForData : BufferData → I → m (JuliaLean.base.pointer.Ptr Byte))
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (ref : Ref) (destination : Array) (count : I) : m I :=
  readBytesInt access arrayOps.length methods.resize (vectorBounds arrayOps) pointer
    (fun destination data start count =>
      match method with
      | .abstractVector =>
          unsafeReadVector sourceIndex getindex heap destination data start count
      | .denseArray => unsafeReadDense pointerForData memmove destination data start count)
    ref destination count

/-- Binds default-count `readbytes!` to installed one-based Array methods. -/
def readBytesDefaultVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    {Ref BufferData Array Memory P : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref BufferData)
    (arrayOps : JuliaLean.base.array.Storage m Array Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (methods : VectorMethods m (JuliaLean.base.genericmemory.GenericMemoryRef Memory P) Array Array)
    (method : UnsafeReadMethod) (sourceIndex : I → U → m I)
    (getindex : BufferData → I → m Byte)
    (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (pointerForData : BufferData → I → m (JuliaLean.base.pointer.Ptr Byte))
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (ref : Ref) (destination : Array) (count : Option I) : m I :=
  readBytesDefault access arrayOps.length pure arrayOps.length methods.resize
    (vectorBounds arrayOps) pointer
    (fun destination data start count =>
      match method with
      | .abstractVector =>
          unsafeReadVector sourceIndex getindex heap destination data start count
      | .denseArray => unsafeReadDense pointerForData memmove destination data start count)
    ref destination count

/-- `read(::GenericIOBuffer, ::UInt8)` binds the installed Array/GenericMemory getindex path. -/
def readUInt8 {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (getindex : Data → I → m Byte) (ref : Ref) : m Byte :=
  JuliaLean.base.iobuffer.source_read_uint8 access getindex ref

/-- `read(::GenericIOBuffer, ::UInt8)` binds Vector access to Array bounds and GenericMemory loads. -/
def readUInt8Vector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Ref Data Memory P : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (ref : Ref) : m Byte :=
  readUInt8 access (getArrayByte arrayOps memoryOps) ref

/--
Julia source: base/iobuffer.jl:558-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncate(io::GenericIOBuffer, n::Integer)
    io.writable || throw(ArgumentError("truncate failed, IOBuffer is not writeable"))
    io.seekable || throw(ArgumentError("truncate failed, IOBuffer is not seekable"))
    n < 0 && throw(ArgumentError("truncate failed, n bytes must be ≥ 0, got $n"))
    n > io.maxsize && throw(ArgumentError("truncate failed, $n bytes is exceeds IOBuffer maxsize $(io.maxsize)"))
    n = Int(n)::Int
    offset = get_offset(io)
    current_size = io.size - offset
    if io.reinit
        io.data = fill!(_similar_data(io, n), 0x00)
        io.reinit = false
        io.size = n
    elseif n < current_size
        if translate_seek_position(io, io.mark) > n + offset
            io.mark = -1
        end
        io.size = n + offset
        io.ptr = min(io.ptr, n + offset + 1)
    elseif n > current_size
        if n + offset > io.maxsize
            compact!(io)
        end
        _resize!(io, n + get_offset(io), false)
        fill!(view(io.data, io.size + 1:min(length(io.data), n + get_offset(io))), 0x00)
        io.size = min(length(io.data), n + get_offset(io))
    end
    return io
end
```
-/
def truncate {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data NewData N : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage m Ref Data NewData)
    (negative : N → m Bool) (exceeds : N → I → m Bool) (toInt : N → m I)
    (showN : N → String) (ref : Ref) (requested : N) : m Ref := do
  let io ← access.get ref
  if !io.writable then
    throw (.jl (.argumentError "truncate failed, IOBuffer is not writeable"))
  let io ← access.get ref
  if !io.seekable then
    throw (.jl (.argumentError "truncate failed, IOBuffer is not seekable"))
  if ← negative requested then
    throw (.jl (.argumentError ("truncate failed, n bytes must be ≥ 0, got " ++ showN requested)))
  let io ← access.get ref
  if ← exceeds requested io.maxsize then
    throw (.jl (.argumentError ("truncate failed, " ++ showN requested ++
      " bytes is exceeds IOBuffer maxsize " ++ toString io.maxsize.val)))
  let n ← toInt requested
  let io ← access.get ref
  let offset := JuliaLean.base.iobuffer.fieldsOffset io
  let currentSize := JuliaLean.base.int.sub io.size offset
  if io.reinit then
    let newData ← storage.similar ref n
    storage.fillNew newData (JuliaLean.base.int.lit .u8 0)
    let data ← storage.convertData newData
    let current ← access.get ref
    access.set ref { current with data }
    let current ← access.get ref
    access.set ref { current with reinit := false }
    let current ← access.get ref
    access.set ref { current with size := n }
  else if JuliaLean.base.int.lt n currentSize then
    if JuliaLean.base.int.lt (JuliaLean.base.int.add n offset)
        (← JuliaLean.base.iobuffer.liftIO
          (JuliaLean.base.iobuffer.source_translate_seek_position io io.mark)) then
      let current ← access.get ref
      access.set ref { current with mark := JuliaLean.base.int.lit .i64 (-1) }
    let current ← access.get ref
    access.set ref { current with size := JuliaLean.base.int.add n offset }
    let current ← access.get ref
    access.set ref { current with
      ptr := JuliaLean.base.int.jmin current.ptr
        (JuliaLean.base.int.add (JuliaLean.base.int.add n offset) JuliaLean.base.iobuffer.one) }
  else if JuliaLean.base.int.lt currentSize n then
    if JuliaLean.base.int.lt io.maxsize (JuliaLean.base.int.add n offset) then
      let _ ← JuliaLean.base.iobuffer.source_compact access storage ref
      pure ()
    let current ← access.get ref
    let _ ← JuliaLean.base.iobuffer.source_resize access storage ref
      (JuliaLean.base.int.add n (JuliaLean.base.iobuffer.fieldsOffset current)) false
    let current ← access.get ref
    let data := current.data
    let first := JuliaLean.base.int.add current.size JuliaLean.base.iobuffer.one
    let current ← access.get ref
    let length ← storage.length current.data
    let current ← access.get ref
    let last ← storage.minimumLength length
      (JuliaLean.base.int.add n (JuliaLean.base.iobuffer.fieldsOffset current))
    storage.fillView data first last (JuliaLean.base.int.lit .u8 0)
    let current ← access.get ref
    let length ← storage.length current.data
    let current ← access.get ref
    let last ← storage.minimumLength length
      (JuliaLean.base.int.add n (JuliaLean.base.iobuffer.fieldsOffset current))
    let size ← storage.boundToInt last
    let current ← access.get ref
    access.set ref { current with size }
  pure ref

export JuliaLean.base.iobuffer (DenseByteVector ArrayWorld)

/-- Installed SubArray indices over an installed dense byte-vector representation. -/
structure SubArrayByteVector where
  view : JuliaLean.base.subarray.SubArray DenseByteVector Byte
  deriving DecidableEq
/-- `to_index(::Integer)` converts the UInt loop index before a SubArray Int setter call. -/
def unsafeWriteIndex {E World : Type} (index : U) : RuntimeM E World I :=
  match JuliaLean.base.indices.to_index_Integer
    (fun value : U => JuliaLean.base.int.convert .i64 value)
    (fun value : I => pure value)
    index with
  | .ok value => pure value
  | .error error => throwThe JuliaLean.base.iobuffer.IOErr (.jl error)

/-- Lift the installed mutable Array heap into the shared IOBuffer world, retaining partial writes
when an Array operation throws. -/
private def liftArrayMutation {E Ref Data A : Type}
    (action : JuliaLean.base.array.MutationM Byte A) :
    RuntimeM E (ArrayWorld Ref Data) A := fun world =>
  let (result, memory) := action.run world.other
  match result with
  | .ok value => some (.ok (value, { world with other := memory }))
  | .error error => some (.error (.array error, { world with other := memory }))

private def memoryByteInBounds {E Ref Data : Type} (memory : Nat) (index : I) :
    RuntimeM E (ArrayWorld Ref Data) Bool := do
  let contents ← liftArrayMutation (JuliaLean.base.array.memoryRead memory)
  pure (decide (1 ≤ index.val ∧ index.val ≤ (contents.length : Int)))

private def readMemoryByte {E Ref Data : Type} (memory : Nat) (index : I) :
    RuntimeM E (ArrayWorld Ref Data) Byte := do
  let contents ← liftArrayMutation (JuliaLean.base.array.memoryRead memory)
  if !(1 ≤ index.val) then
    throwThe (Error E) (.array .bounds)
  match contents[(index.val - 1).toNat]? with
  | some (some value) => pure value
  | some none => throwThe (Error E) (.array .undefinedReference)
  | none => throwThe (Error E) (.array .bounds)

private def mutableByteMemoryOps {E Ref Data : Type} :
    JuliaLean.base.genericmemory.MemoryAccessOps
      (RuntimeM E (ArrayWorld Ref Data)) Nat I Byte Byte :=
  JuliaLean.base.iobuffer.mutableByteMemoryOpsWith liftArrayMutation

export JuliaLean.base.iobuffer (denseBytePointer pointerAtDenseByte
  ByteMemory byteMemoryLength byteMemoryPointer byteMemoryCheckBounds byteMemoryGetindex
  byteMemoryAccessOps byteMemorySetindex byteMemoryCopyOps byteMemoryCopyto
  byteMemoryFillNew byteMemoryFill byteMemoryStorage byteMemoryEnsureRoom
  byteMemoryEnsureRoomInt byteMemoryEmptyIOBuffer byteMemoryTakeString)
private def writePointerByte {E Ref Data : Type}
    (pointer : JuliaLean.base.pointer.Ptr Byte) (value : Byte) :
    RuntimeM E (ArrayWorld Ref Data) Unit := do
  let world ← getWorld
  setWorld { world with bytes :=
    world.bytes.writeByte pointer.address.val.toNat value }

/-- Runtime representation factory for a `Vector{UInt8}`. It allocates through the installed
`JuliaLean.base.array.mutableAllocate` and uses its typed setter model
(`boot.jl:821-824`, `array.jl:1031-1041`); `baseAddress` is the runtime `pointer(data)` value. -/
def vectorUInt8Factory {E Ref : Type}
    (baseAddress : JuliaLean.base.pointer.U64) (length : I) (bytes : List Byte) :
    RuntimeM E (ArrayWorld Ref DenseByteVector) DenseByteVector := do
  let handle ← liftArrayMutation (JuliaLean.base.array.mutableAllocate
    (some ⟨1, false, false⟩) 0 length)
  let vector := JuliaLean.base.iobuffer.DenseByteVector.array handle baseAddress
  for (byte, offset) in bytes.zipIdx do
    let index := JuliaLean.base.iobuffer.i (offset + 1)
    let _ ← liftArrayMutation (JuliaLean.base.array.mutableSet handle byte index)
    writePointerByte (pointerAtDenseByte vector index) byte
  pure vector

/-- Store through the installed Array and GenericMemory setters with the bounds check suppressed
by Julia's enclosing `@inbounds` (`array.jl:1036-1041`, `genericmemory.jl:326-331`). An index
outside the represented vector's logical length has undefined behavior. -/
private def setDenseByteBacking {E Ref Data : Type}
    (data : DenseByteVector) (value : Byte) (index : I) :
    RuntimeM E (ArrayWorld Ref Data) Unit := do
  match data with
  | .array handle _ => do
    if !(← liftArrayMutation (JuliaLean.base.array.mutableInBounds handle index)) then
      throwThe (Error E) (.undefinedBehavior "Array @inbounds write outside vector")
    let _ ← liftArrayMutation (JuliaLean.base.array.setindexTyped
      (fun _ _ => pure ())
      (fun arrayIndex item _ => JuliaLean.base.array.mutableMemoryref arrayIndex item)
      (fun reference byte _ => JuliaLean.base.array.memoryWrite reference.1 reference.2
        (some byte))
      handle value index)
    pure ()
  | .memory handle _ => do
    if !(← memoryByteInBounds handle index) then
      throwThe (Error E) (.undefinedBehavior "Memory @inbounds write outside memory")
    let _ ← JuliaLean.base.genericmemory.setindexMemoryRaw
      mutableByteMemoryOps false handle value index
    pure ()

private def setDenseByteInbounds {E Ref Data : Type}
    (data : DenseByteVector) (value : Byte) (index : I) :
    RuntimeM E (ArrayWorld Ref Data) Unit := do
  setDenseByteBacking data value index
  writePointerByte (pointerAtDenseByte data index) value


/-- A dense pointer copy reads the source span before writing, as `memmove` does. The installed
`unsafeCopyPtr` body still chooses this typed byte-move operation for the dense specialization. -/
private def copyDenseByteVector {E Ref : Type}
    (heap : JuliaLean.base.iobuffer.HeapAccess
      (RuntimeM E (ArrayWorld Ref DenseByteVector)))
    (data : DenseByteVector) (start : I)
    (_destination source : JuliaLean.base.pointer.Ptr Byte) (count : U) :
    RuntimeM E (ArrayWorld Ref DenseByteVector) Unit := do
  let bytes ← (List.range count.val.toNat).mapM fun offset =>
    loadBytePointer heap source (JInt.wrap .u64 (Int.ofNat (offset + 1)))
  for (byte, offset) in bytes.zipIdx do
    setDenseByteInbounds data byte (start + JInt.wrap .i64 (Int.ofNat offset))

private def subArrayVectorLength
    (view : JuliaLean.base.subarray.SubArray DenseByteVector Byte) : I :=
  let axisLength (axis : JuliaLean.base.subarray.Axis) : I :=
    if axis.last.val < axis.first.val then JuliaLean.base.subarray.int64 0
    else JuliaLean.base.subarray.iadd
      (JuliaLean.base.subarray.isub axis.last axis.first)
      (JuliaLean.base.subarray.int64 1)
  (JuliaLean.base.subarray.sizeSubArray view
    JuliaLean.base.subarray.axesSubArrayModel axisLength).headD
    (JuliaLean.base.subarray.int64 0)

/-- `checkbounds(::Bool, V::AbstractArray, i)` checks the view's linear OneTo axis. -/
private def checkSubArrayVectorBounds {E Ref Data : Type}
    (view : JuliaLean.base.subarray.SubArray DenseByteVector Byte) (index : I) :
    RuntimeM E (ArrayWorld Ref Data) Unit := do
  if !(JuliaLean.base.abstractarray.checkindexOneTo (subArrayVectorLength view) index) then
    throwThe (Error E) (.buffer (.jl .boundsError))

/-- Worldful lift of `setindex!(V::FastSubArray{<:Any,1}, x, i::Int)`:
check the view, reindex, then write the selected parent through its installed Array/Memory setter
(`subarray.jl:398-403`). -/
private def setindexFastVectorSubArrayRuntime {E Ref Data : Type}
    (view : JuliaLean.base.subarray.SubArray DenseByteVector Byte)
    (value : Byte) (index : I) : RuntimeM E (ArrayWorld Ref Data) Unit := do
  checkSubArrayVectorBounds view index
  setDenseByteInbounds view.parent value
    (JuliaLean.base.subarray.reindexLinearDispatch view index)

/-- Each concrete representation selects its source `_unsafe_write` method by type. -/
class UnsafeWriteDispatch (Data : Type) where
  unsafeWriteBody {E Ref : Type}
    (heap : JuliaLean.base.iobuffer.HeapAccess
      (RuntimeM E (ArrayWorld Ref Data)))
    (data : Data) (source : JuliaLean.base.pointer.Ptr Byte) (start : I) (count : U) :
    RuntimeM E (ArrayWorld Ref Data) (Unit ⊕ JuliaLean.base.pointer.Ptr Byte)



/-- Source body for `_unsafe_write(::AbstractVector{UInt8}, ...)` (`iobuffer.jl:923-928`).
Unmodeled user-defined non-dense vectors remain a named gap because their dispatch instances are
not installed. -/
def unsafeWriteVector {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {Data : Type}
    (setindex : Data → Byte → U → m Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (data : Data) (pointer : JuliaLean.base.pointer.Ptr Byte) (start : I) (count : U) : m Unit :=
  JuliaLean.base.iobuffer.source_unsafe_write_vector setindex
    (fun source => loadBytePointer heap source (JInt.wrap .u64 1))
    (fun source => pure
      (JuliaLean.base.pointer.ptrAddI64 source JuliaLean.base.iobuffer.one))
    data pointer start count

/-- Exact dense `_unsafe_write` body (`iobuffer.jl:930-946`). Pointer loads and copy use installed
models; `pointerForData` is the selected `pointer(data, start)` method, still required for dense
storage. -/
def unsafeWriteDense {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {Data : Type}
    (setindex : Data → Byte → I → m Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (pointerForData : Data → I → m (JuliaLean.base.pointer.Ptr Byte))
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (data : Data) (source : JuliaLean.base.pointer.Ptr Byte) (start : I) (count : U) :
    m (Unit ⊕ JuliaLean.base.pointer.Ptr Byte) :=
  JuliaLean.base.iobuffer.source_unsafe_write_dense setindex
    (fun pointer index => loadBytePointer heap pointer index)
    pointerForData (copyBytePointer memmove) data source start count
/-- `Array{UInt8,1}` and `Memory{UInt8}` share the dense method
(`iobuffer.jl:930-946`); their handles and data live in the installed mutable Array heap. -/
instance denseByteVectorUnsafeWriteDispatch : UnsafeWriteDispatch DenseByteVector where
  unsafeWriteBody heap data source start count :=
    unsafeWriteDense (fun _ byte index => setDenseByteInbounds data byte index)
      heap (fun _ index => pure (pointerAtDenseByte data index))
      (copyDenseByteVector heap data start) data source start count

/-- A SubArray of a represented dense byte vector selects the AbstractVector fallback
(`iobuffer.jl:923-928`). Other user-defined vector representations remain unmodeled. -/
instance subArrayByteVectorUnsafeWriteDispatch : UnsafeWriteDispatch SubArrayByteVector where
  unsafeWriteBody heap data source start count := do
    unsafeWriteVector
      (fun _ byte rawIndex => do
        let index ← unsafeWriteIndex rawIndex
        setindexFastVectorSubArrayRuntime data.view byte index)
      heap data source start count
    pure (.inl ())

/- BLOCKED-MODEL: User-defined non-dense `AbstractVector{UInt8}` data, and SubArrays whose parent
is not a represented dense Array/Memory byte vector, remain gaps. Their pinned fallback is
`base/iobuffer.jl:923-928`. The concrete dense dispatch is the `Array`/`Memory` alias at
`base/iobuffer.jl:930-946`. -/

/-- Exact generic `unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)` body
(`iobuffer.jl:902-921`). The data type's dispatch instance selects one of the two installed
`_unsafe_write` methods above. -/
def unsafeWrite {E Ref Data NewData Source Task Scope : Type}
    [dispatch : UnsafeWriteDispatch Data]
    (access : JuliaLean.base.iobuffer.Access
      (RuntimeM E (ArrayWorld Ref Data)) Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage
      (RuntimeM E (ArrayWorld Ref Data)) Ref Data NewData)
    (scopeOps : JuliaLean.base.cancellation.ScopeOps (ArrayWorld Ref Data) Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps (ArrayWorld Ref Data) Source)
    (slow : Task → JuliaLean.base.cancellation.M (ArrayWorld Ref Data)
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M (ArrayWorld Ref Data) Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess
      (RuntimeM E (ArrayWorld Ref Data)))
    (ref : Ref) (pointer : JuliaLean.base.pointer.Ptr Byte) (count : U)
    (cancel : JuliaLean.base.cancellation.CancelTokenArg Source) :
    RuntimeM E (ArrayWorld Ref Data) I :=
  JuliaLean.base.iobuffer.source_unsafe_write access storage
    (precheckCancelArg scopeOps tokenOps slow handleCancellation)
    (dispatch.unsafeWriteBody heap) ref pointer count cancel
/-- Exact `write(::GenericIOBuffer, ::UInt8)` method (`iobuffer.jl:948-963`). -/
def writeUInt8 {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data NewData : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage m Ref Data NewData)
    (setindex : Data → I → Byte → m Unit) (ref : Ref) (byte : Byte) : m I :=
  JuliaLean.base.iobuffer.source_write_uint8 access storage setindex ref byte

/-- `take!(::IOBuffer)` uses installed Array and GenericMemory allocation, wrap, and copy bodies
(`iobuffer.jl:758-786`). String allocation and Array object creation remain runtime calls. -/
def takeIOBuffer {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Ref Memory Vector P Pointer Token StringRef : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Memory)
    (arrayOps : JuliaLean.base.array.Storage m Vector Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I)
    (copyOps : JuliaLean.base.genericmemory.MemoryCopyOps m Memory P I I I I Pointer Token)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (checkedDims : List I → m I)
    (newArray : JuliaLean.base.genericmemory.GenericMemoryRef Memory P → List I → m Vector)
    (ref : Ref) : m Vector :=
  JuliaLean.base.iobuffer.source_take_IOBuffer access
    (allocateStringVector memoryOps memoryLength allocateString stringToMemory newArray)
    (wrapMemoryVector arrayOps memoryOps memoryLength checkedDims newArray)
    (copyMemoryToVector arrayOps memoryOps copyOps) ref

export JuliaLean.base.iobuffer (takeStringIOBuffer)
/-- Exact generic `copyuntil(::IO, ::GenericIOBuffer, ::UInt8)` source body (`iobuffer.jl:993-1008`).
`writeDefault`/`writeToken` are the installed IO array-write dispatch, with user IO methods typed
at the selected-call boundary. -/
def copyuntil {m : Type → Type} [Monad m] {Ref Data Out View Cancel : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (view : Data → I → I → m View) (findFirst : Byte → View → m (Option I))
    (length : View → m I) (getByte : View → I → m Byte)
    (isDefault : Cancel → m Bool) (writeDefault : Out → View → m Unit)
    (writeToken : Out → View → Cancel → m Unit) (out : Out) (ref : Ref)
    (delimiter : Byte) (keep : Bool) (cancel : Cancel) : m Out :=
  JuliaLean.base.iobuffer.source_copyuntil access view findFirst length getByte isDefault
    writeDefault writeToken out ref delimiter keep cancel

/-- Exact generic `copyline(::GenericIOBuffer, ::IO)` source body (`iobuffer.jl:1010-1055`). -/
def copylineBuffer {m : Type → Type} [Monad m] {Ref Data Stream Cancel Vector : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (isDefault : Cancel → m Bool) (checkCancel : Cancel → m Cancel)
    (newBuffer : m Ref) (copyDefault : Ref → Stream → Byte → Bool → m Unit)
    (copyToken : Ref → Stream → Byte → Bool → Cancel → m Unit)
    (take : Ref → m Vector) (length : Vector → m I) (last : Vector → m Byte)
    (pop : Vector → m Unit) (write : Ref → Vector → Cancel → m Unit)
    (getByte : Data → I → m Byte) (out : Ref) (stream : Stream)
    (keep : Bool) (cancel : Cancel) : m Ref :=
  JuliaLean.base.iobuffer.source_copyline_buffer access isDefault checkCancel newBuffer
    copyDefault copyToken take length last pop write getByte out stream keep cancel

/--
Julia source: base/iobuffer.jl:886-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(to::IO, from::GenericIOBuffer)
    if to === from
        throw(ArgumentError("Writing all content fron an IOBuffer into itself in invalid"))
    else
        from.readable || _throw_not_readable()
        written = write(to, view(from.data, from.ptr:from.size))
        from.ptr = from.size + 1
    end
    return written
end
```
-/
def writeFromIOBuffer {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Ref Data Out View : Type} (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (identical : Out → Ref → m Bool) (view : Data → I → I → m View)
    (writeView : Out → View → m I) (out : Out) (input : Ref) : m I := do
  if ← identical out input then
    throw (.jl (.argumentError "Writing all content fron an IOBuffer into itself in invalid"))
  let io ← access.get input
  if !io.readable then
    JuliaLean.base.iobuffer.liftIO JuliaLean.base.iobuffer.source_throw_not_readable
  let written ← writeView out (← view io.data io.ptr io.size)
  let current ← access.get input
  access.set input { current with ptr := JuliaLean.base.int.add current.size JuliaLean.base.iobuffer.one }
  pure written

/-- Exact `copyline(::IO, ::GenericIOBuffer)` body (`iobuffer.jl:1079`). -/
def copylineIO {m : Type → Type} [Monad m] {Ref Data View Out Cancel : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (view : Data → I → I → m View) (findFirst : Byte → View → m (Option I))
    (length : View → m I) (getByte : View → I → m Byte)
    (isDefault : Cancel → Bool) (writeDefault : Out → View → m Unit)
    (writeToken : Out → View → Cancel → m Unit) (out : Out) (ref : Ref)
    (keep : Bool) (cancel : Cancel) : m Out :=
  JuliaLean.base.iobuffer.source_copyline_IO access view findFirst length getByte isDefault
    writeDefault writeToken out ref keep cancel

/-- Exact `copyline(::GenericIOBuffer, ::GenericIOBuffer)` dispatch (`iobuffer.jl:1080`). -/
def copylineBufferBuffer {m : Type → Type} [Monad m] {Ref Data View Out Cancel : Type}
    (access : JuliaLean.base.iobuffer.Access m Ref Data)
    (view : Data → I → I → m View) (findFirst : Byte → View → m (Option I))
    (length : View → m I) (getByte : View → I → m Byte)
    (isDefault : Cancel → Bool) (writeDefault : Out → View → m Unit)
    (writeToken : Out → View → Cancel → m Unit) (out : Out) (ref : Ref)
    (keep : Bool) (cancel : Cancel) : m Out :=
  JuliaLean.base.iobuffer.source_copyline_buffer_buffer access view findFirst length getByte
    isDefault writeDefault writeToken out ref keep cancel

/-- Installed `readuntil(::IO, ::UInt8)` body (`io.jl:624-626`), lifted once into the shared
runtime error sum. Its callbacks retain the selected `copyuntil` and `take!` methods. -/
def readuntilByte {E World Stream Buffer Token Kw A : Type}
    (newBuffer : I → JuliaLean.base.io.M World Buffer)
    (plain : Buffer → Stream → Byte → Kw → JuliaLean.base.io.M World Buffer)
    (explicit : Buffer → Stream → Byte → Option Token → Kw → JuliaLean.base.io.M World Buffer)
    (take : Buffer → JuliaLean.base.io.M World A) (stream : Stream) (delimiter : Byte)
    (cancel : JuliaLean.base.io.CancelArg Token) (keywords : Kw) : RuntimeM E World A :=
  liftIOModel (JuliaLean.base.io.readuntilByte newBuffer plain explicit take stream delimiter cancel keywords)

/-- Installed `readuntil(::IO, ::AbstractChar/AbstractString)` body (`io.jl:627-629`). -/
def readuntilText {E World Stream Buffer Token Delimiter Kw Text : Type}
    (newBuffer : I → JuliaLean.base.io.M World Buffer)
    (plain : Buffer → Stream → Delimiter → Kw → JuliaLean.base.io.M World Buffer)
    (explicit : Buffer → Stream → Delimiter → Option Token → Kw → JuliaLean.base.io.M World Buffer)
    (takestring : Buffer → JuliaLean.base.io.M World Text) (stream : Stream)
    (delimiter : Delimiter) (cancel : JuliaLean.base.io.CancelArg Token)
    (keywords : Kw) : RuntimeM E World Text :=
  liftIOModel (JuliaLean.base.io.readuntilText newBuffer plain explicit takestring
    stream delimiter cancel keywords)

end JuliaLean.Bindings.base.iobuffer
