import JuliaLean.base.iobuffer
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

/-!
Properties for `base/iobuffer.jl` stated over the source-mirrored `BufferState` model.
Every buffer premise is the field invariant. Each registry entry records a proved contract, a
refutation, or a property still open.
-/

namespace JuliaLean.Proofs.base.iobuffer

open JuliaLean JuliaLean.Registry JuliaLean.base.iobuffer

instance instDecidableEqExceptIOErr {α} [DecidableEq α] : DecidableEq (Except IOErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (fun e => nomatch e)
  | .error _, .ok _ => isFalse (fun e => nomatch e)

def resultOf {α} (m : M α) (io : BufferState) : Except IOErr α :=
  match m.run io with
  | .ok a _ => .ok a
  | .error e _ => .error e

def stateOf {α} (m : M α) (io : BufferState) : BufferState :=
  match m.run io with
  | .ok _ s => s
  | .error _ s => s

def content (io : BufferState) : List UInt8 :=
  slice io.data ((getOffset io).val + 1) io.size.val

def available (io : BufferState) : List UInt8 := slice io.data io.ptr.val io.size.val

def positionWithin (io : BufferState) : Prop :=
  0 ≤ (source_position io).val ∧ (source_position io).val ≤ (logicalSize io).val

def observe (io : BufferState) : List UInt8 × Int × List UInt8 :=
  (content io, (source_position io).val, available io)

/-- The list models a Julia `Vector{UInt8}`, whose length is a nonnegative `Int`. -/
def vectorBytesValid (bytes : List UInt8) : Prop := bytes.length < 2 ^ 63



def defaultBufferState : BufferState :=
  { data := [], isMemory := false, reinit := false, readable := false, writable := false,
    seekable := false, append := false, size := zero, maxsize := zero, ptr := one,
    offset := zero, mark := JuliaLean.base.int.lit .i64 (-1) }

instance : Inhabited BufferState := ⟨defaultBufferState⟩

abbrev CtorM := StateT BufferState (Except IOErr)

instance : MonadExceptOf JuliaLean.base.abstractarray.ArrayError CtorM where
  throw
    | .julia e => fun _ => .error (.jl e)
    | .dimensionMismatch msg => fun _ => .error (.jl (.argumentError msg))
    | .canonicalIndex fn _ => fun _ => .error (.jl (.argumentError fn))
    | .errorException msg => fun _ => .error (.errorException msg)
    | .assertionError msg => fun _ => .error (.errorException msg)
    | .showError error => fun _ => .error (.showError error)
  tryCatch body handler := fun s =>
    match body s with
    | .ok a => .ok a
    | .error (.jl e) => handler (.julia e) s
    | .error e => .error e

def runCtorM (act : CtorM Unit) : Except IOErr BufferState :=
  (act.run default).map Prod.snd

def runNewGenericBuffer {T : Type} (data : T) (dataBytes : T → List UInt8)
    (isMemory : T → Bool) (readable writable seekable append : Bool) (maxsize : I) : BufferState :=
  match runCtorM (source_new_generic_iobuffer (ctorStateAccess (isMemory data))
      (fun _ => pure (dataBytes data).length) (fun n => pure (i n)) (dataBytes data)
      readable writable seekable append maxsize) with
  | .ok io => io
  | .error _ => default

def runGenericIOBufferTyped (requireOneBased : DataArg → Except IOErr Unit)
    (data : DataArg) (readable writable seekable append : Bool) (maxsize : Int)
    (truncate : Bool) : Except IOErr BufferState :=
  runCtorM (source_GenericIOBuffer_typed (ctorStateAccess (dataIsMemory data))
    (fun _ => StateT.lift (requireOneBased data >>= fun _ => .ok false))
    (fun d => pure d.length) (fun n => pure (i n))
    (fun m => StateT.lift (toI m))
    (dataBytes data) readable writable seekable append maxsize truncate)

def runGenericIOBuffer (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr BufferState :=
  runCtorM (source_GenericIOBuffer (ctorStateAccess (dataIsMemory data))
    (fun _ => pure (i 1)) pure (fun d => pure d.length) (fun n => pure (i n))
    (fun m => StateT.lift (toI m))
    (dataBytes data) readable writable seekable append maxsize truncate)

def runGenericIOBufferVector (v : Vec) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr BufferState :=
  runCtorM (source_GenericIOBuffer_Vector (ctorStateAccess true)
    (fun _ => pure v) (fun w => pure w.mem) (fun w => pure (i (w.off + 1)))
    (fun w => pure (i w.len)) (fun m => pure (i m.length))
    (fun m => StateT.lift (toI m))
    v readable writable seekable append maxsize truncate)

def runIOBufferData (sizehint : DataArg → Int → Except IOErr DataArg)
    (data : DataArg) (read write append truncate : Option Bool) (maxsize : Int)
    (sizeHint : Option Int) : Except IOErr BufferState :=
  StateT.run' (s := data) do
    source_IOBuffer_data (m := StateT DataArg (Except IOErr))
      (fun _ n => do let d ← get; let d' ← StateT.lift (sizehint d n); set d')
      (fun _ r w s a mz tr => do
        let d ← get
        match d with
        | .vec v => StateT.lift (runGenericIOBufferVector v r w s a mz tr)
        | _ => StateT.lift (runGenericIOBuffer d r w s a mz tr))
      data read write append truncate maxsize sizeHint

def runIOBufferEmpty (read write append truncate : Option Bool) (maxsize : Int)
    (sizehint : Option Int) : Except IOErr BufferState :=
  runCtorM (source_IOBuffer_empty (ctorStateAccess true)
    (fun m => StateT.lift (toI m)) (fun h => StateT.lift (toI h))
    (fun sz => StateT.lift (stringMemoryBytes sz.val))
    (fun m => pure m.length) (fun n => pure (i n))
    read write append truncate maxsize sizehint)

def runPipeBufferData (data : DataArg) (maxsize : I) : Except IOErr BufferState :=
  source_PipeBuffer_data (m := Except IOErr)
    (fun d r w s a mz tr =>
      match d with
      | .vec v => runGenericIOBufferVector v r w s a mz.val tr
      | _ => runGenericIOBuffer d r w s a mz.val tr)
    data maxsize

def runPipeBufferMaxsize (t : IntTy) (maxsize : Int) : Except IOErr BufferState :=
  runCtorM (source_PipeBuffer_maxsize (ctorStateAccess true)
    (fun m => StateT.lift (stringMemoryBytes m))
    (fun m => if t != .i64 then StateT.lift (.error .typeError) else pure (i m))
    (fun mem mz => do
      let x ← StateT.lift (runPipeBufferData (.mem mem) mz)
      set x)
    maxsize)

def runTruncatedPipebuffer (data : DataArg) (maxsize : I) : Except IOErr BufferState :=
  runCtorM (source_truncated_pipebuffer (ctorStateAccess (dataIsMemory data))
    (fun d => do
      let buf ← StateT.lift (runPipeBufferData d imaxval)
      set buf)
    data maxsize)

def untilSpec (bytes : List UInt8) (delimiter : UInt8) (keep : Bool) : List UInt8 :=
  match bytes.idxOf? delimiter with
  | some k => bytes.take (if keep then k + 1 else k)
  | none => bytes

def afterSpec (bytes : List UInt8) (delimiter : UInt8) : List UInt8 :=
  match bytes.idxOf? delimiter with
  | some k => bytes.drop (k + 1)
  | none => []

def lineSpec (bytes : List UInt8) (keep : Bool) : List UInt8 :=
  match bytes.idxOf? 0x0a with
  | some k =>
      if keep then bytes.take (k + 1)
      else if 0 < k && bytes[k - 1]! = 0x0d then bytes.take (k - 1)
      else bytes.take k
  | none => bytes

def stripNewline (line : List UInt8) : List UInt8 :=
  if line.getLast? = some 0x0a then
    if line.dropLast.getLast? = some 0x0d then line.dropLast.dropLast else line.dropLast
  else line

/-! Shared-state interfaces for the reference-based source models. The fields
below are primitive heap observations and external callees, never IOBuffer results. -/
structure BufferWorld where
  Heap : Type
  Ref : Type
  Data : Type
  NewData : Type
  Vector : Type
  View : Type
  StringRef : Type
  Stream : Type
  VectorRef : Type
  Cancel : Type
  fields : Heap → Ref → Fields Data
  setFields : Heap → Ref → Fields Data → Heap
  newFields : Fields Data → EStateM IOErr Heap Ref
  memoryType : Heap → Ref → Bool
  bytes : Heap → Data → List UInt8
  vectorStringOps : StringVectorOps (EStateM IOErr Heap) Vector VectorRef Data StringRef
  emptyMemory : EStateM IOErr Heap Data
  memoryref : Data → I → EStateM IOErr Heap VectorRef
  wrapCheck : VectorRef → List I → EStateM IOErr Heap VectorRef
  newArray : VectorRef → List I → EStateM IOErr Heap Vector
  allocateString : U → EStateM IOErr Heap StringRef
  stringToMemory : StringRef → EStateM IOErr Heap Data
  memoryLength : Data → I
  memoryrefBase : Data → EStateM IOErr Heap VectorRef
  vectorType : Heap → Data → Bool
  dataReference : Data → EStateM IOErr Heap VectorRef
  referenceMemory : VectorRef → EStateM IOErr Heap Data
  memoryOffset : VectorRef → EStateM IOErr Heap I
  dataLength : Data → EStateM IOErr Heap I
  firstIndex : Data → EStateM IOErr Heap I
  sizehint : Data → Int → EStateM IOErr Heap Unit
  vectorBytes : Heap → Vector → List UInt8
  vectorFromBytes : List UInt8 → EStateM IOErr Heap Vector
  stringBytes : Heap → StringRef → List UInt8
  outputBytes : Heap → Ref → List UInt8
  streamBytes : Heap → Stream → List UInt8
  storage : Storage (EStateM IOErr Heap) Ref Data NewData
  copyVector : Vector → I → Data → I → I → EStateM IOErr Heap Vector
  readInto : Ref → Vector → EStateM IOErr Heap Vector
  vectorLength : Vector → EStateM IOErr Heap I
  vectorResize : Vector → I → EStateM IOErr Heap Unit
  vectorBounds : Vector → I → EStateM IOErr Heap Unit
  vectorPointer : Vector → EStateM IOErr Heap (JuliaLean.base.pointer.Ptr Byte)
  pointerBytes : Heap → JuliaLean.base.pointer.Ptr Byte → Nat → List UInt8
  validPointer : Heap → JuliaLean.base.pointer.Ptr Byte → U → Prop
  getIndex : Data → I → EStateM IOErr Heap Byte
  getIndexU : Data → U → EStateM IOErr Heap Byte
  setIndex : Data → Byte → I → EStateM IOErr Heap Unit
  setIndexU : Data → Byte → U → EStateM IOErr Heap Unit
  dense : Heap → Data → Bool
  pointer : Data → I → EStateM IOErr Heap (JuliaLean.base.pointer.Ptr Byte)
  load : JuliaLean.base.pointer.Ptr Byte → U → EStateM IOErr Heap Byte
  store : JuliaLean.base.pointer.Ptr Byte → Byte → U → EStateM IOErr Heap Unit
  copyPointer : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U →
    EStateM IOErr Heap (JuliaLean.base.pointer.Ptr Byte)
  precheck : Cancel → EStateM IOErr Heap Unit
  defaultCancel : Cancel
  isDefault : Cancel → EStateM IOErr Heap Bool
  isDefaultPure : Cancel → Bool
  checkCancel : Cancel → EStateM IOErr Heap Cancel
  view : Data → I → I → EStateM IOErr Heap View
  viewBytes : Heap → View → List UInt8
  findFirst : Byte → View → EStateM IOErr Heap (Option I)
  viewLength : View → EStateM IOErr Heap I
  viewIndex : View → I → EStateM IOErr Heap Byte
  writeView : Ref → View → EStateM IOErr Heap Unit
  writeViewToken : Ref → View → Cancel → EStateM IOErr Heap Unit
  identical : Ref → Ref → EStateM IOErr Heap Bool
  copyStream : Ref → Stream → Byte → Bool → EStateM IOErr Heap Unit
  copyStreamToken : Ref → Stream → Byte → Bool → Cancel → EStateM IOErr Heap Unit
  vectorLast : Vector → EStateM IOErr Heap Byte
  vectorPop : Vector → EStateM IOErr Heap Unit
  writeVector : Ref → Vector → Cancel → EStateM IOErr Heap Unit
  spanLength : I → I → EStateM IOErr Heap I
  spanEmpty : I → I → EStateM IOErr Heap Bool
  emptyString : EStateM IOErr Heap StringRef
  memoryToString : Data → I → EStateM IOErr Heap StringRef
  copyMemory : Data → I → Data → I → I → EStateM IOErr Heap Unit
  takeMemory : Data → EStateM IOErr Heap StringRef
  member : Byte → View → EStateM IOErr Heap Bool
  lock : Ref → EStateM IOErr Heap Unit
  unlock : Ref → EStateM IOErr Heap Unit
  print : Ref → ShowArgument → EStateM IOErr Heap Unit
  printed : Heap → Ref → List ShowArgument

abbrev WorldM (w : BufferWorld) := EStateM IOErr w.Heap

def worldAccess (w : BufferWorld) : Access (WorldM w) w.Ref w.Data where
  get := fun ref => do pure (w.fields (← get) ref)
  set := fun ref fields => modify fun heap => w.setFields heap ref fields
  new := w.newFields
  isIOBuffer := fun ref => do pure (w.memoryType (← get) ref)

instance {H : Type} : MonadExceptOf JuliaLean.base.abstractarray.ArrayError (EStateM IOErr H) where
  throw
    | .julia error => throw (.jl error)
    | .dimensionMismatch message => throw (.jl (.argumentError message))
    | .canonicalIndex name _ => throw (.jl (.argumentError name))
    | .errorException message => throw (.errorException message)
    | .assertionError message => throw (.errorException message)
    | .showError error => throw (.showError error)
  tryCatch body handler := fun heap =>
    match body heap with
    | .ok value next => .ok value next
    | .error (.jl error) next => handler (.julia error) next
    | .error error next => .error error next

def worldMemoryUInt (w : BufferWorld) (count : U) : WorldM w w.Data :=
  source_StringMemory (fun n : U => liftNative (JuliaLean.base.int.convert .u64 n))
    w.allocateString w.stringToMemory count

def worldMemoryInt (w : BufferWorld) (count : I) : WorldM w w.Data :=
  source_StringMemory (fun n : I => liftNative (JuliaLean.base.int.convert .u64 n))
    w.allocateString w.stringToMemory count

def worldAllocateVector (w : BufferWorld) (count : I) : WorldM w w.Vector :=
  source_StringVector (fun n : I => liftNative (JuliaLean.base.int.convert .u64 n))
    w.allocateString w.stringToMemory w.memoryrefBase w.memoryLength w.newArray count

def worldNewBuffer (w : BufferWorld) : WorldM w w.Ref :=
  source_IOBuffer_empty (worldAccess w)
    (fun n : I => liftNative (JuliaLean.base.int.convert .i64 n))
    (fun n : I => liftNative (JuliaLean.base.int.convert .i64 n))
    (worldMemoryInt w) (fun data => pure (w.memoryLength data)) pure
    (some true) (some true) none none imaxval none

def worldWrapVector (w : BufferWorld) (memory : w.Data) (first count : I) : WorldM w w.Vector := do
  let reference ← w.memoryref memory first
  JuliaLean.base.array.wrapRefLength
    (fun n : I => liftNative (JuliaLean.base.int.convert .i64 n))
    w.wrapCheck w.newArray reference count

def worldGenericConstructor (w : BufferWorld) (data : w.Data)
    (readable writable seekable append : Bool) (maxsize : Int) (truncate : Bool) : WorldM w w.Ref := do
  if w.vectorType (← get) data then
    source_GenericIOBuffer_Vector (worldAccess w) w.dataReference w.referenceMemory w.memoryOffset
      w.dataLength (fun memory => pure (w.memoryLength memory))
      (fun n => liftIO (toI n)) data readable writable seekable append maxsize truncate
  else
    source_GenericIOBuffer_typed (worldAccess w)
      (hasOffsetVector w.firstIndex pure) w.storage.length w.storage.lengthToInt
      (fun n => liftIO (toI n)) data readable writable seekable append maxsize truncate

def worldDataConstructor (w : BufferWorld) (data : w.Data)
    (read write append truncate : Option Bool) (maxsize : Int) (hint : Option Int) : WorldM w w.Ref :=
  source_IOBuffer_data w.sizehint (worldGenericConstructor w)
    data read write append truncate maxsize hint

def worldEmptyConstructor (w : BufferWorld) (read write append truncate : Option Bool)
    (maxsize : Int) (hint : Option Int) : WorldM w w.Ref :=
  source_IOBuffer_empty (worldAccess w) (fun n => liftIO (toI n)) (fun n => liftIO (toI n))
    (worldMemoryInt w) (fun memory => pure (w.memoryLength memory)) pure
    read write append truncate maxsize hint

def worldSnapshot (w : BufferWorld) (heap : w.Heap) (ref : w.Ref) : BufferState :=
  { data := w.bytes heap (w.fields heap ref).data
    isMemory := w.memoryType heap ref
    reinit := (w.fields heap ref).reinit
    readable := (w.fields heap ref).readable
    writable := (w.fields heap ref).writable
    seekable := (w.fields heap ref).seekable
    append := (w.fields heap ref).append
    size := (w.fields heap ref).size
    maxsize := (w.fields heap ref).maxsize
    ptr := (w.fields heap ref).ptr
    offset := (w.fields heap ref).offset
    mark := (w.fields heap ref).mark }

def worldReadBang (w : BufferWorld) (dest : JuliaLean.base.pointer.Ptr Byte)
    (data : w.Data) (start : I) (count : U) : WorldM w Unit := do
  if w.dense (← get) data then
    source_unsafe_read_dense w.pointer w.copyPointer dest data start count
  else
    source_unsafe_read_vector
      (fun first index => pure (JuliaLean.base.int.binop JuliaLean.base.int.sub
        (JuliaLean.base.int.binop JuliaLean.base.int.add first index) (i 1)))
      w.getIndexU w.store dest data start count

def worldWrite (w : BufferWorld) (ref : w.Ref) (pointer : JuliaLean.base.pointer.Ptr Byte)
    (count : U) (cancel : w.Cancel) : WorldM w I :=
  source_unsafe_write (worldAccess w) w.storage w.precheck
    (fun data pointer first count => do
      if w.dense (← get) data then
        source_unsafe_write_dense w.setIndex w.load w.pointer w.copyPointer data pointer first count
      else
        source_unsafe_write_vector w.setIndexU (fun p => w.load p (u 1))
          (fun p => pure (pointerAdvance p)) data pointer first count
        pure (.inl ()))
    ref pointer count cancel

def worldReadBytes (w : BufferWorld) (ref : w.Ref) (dest : w.Vector) (count : I) : WorldM w I :=
  source_readbytes_int (worldAccess w) w.vectorLength w.vectorResize w.vectorBounds
    w.vectorPointer (worldReadBang w) ref dest count

def worldReadDefault (w : BufferWorld) (ref : w.Ref) (dest : w.Vector) (count : Option I) : WorldM w I :=
  source_readbytes_default (worldAccess w) w.vectorLength pure w.vectorLength w.vectorResize
    w.vectorBounds w.vectorPointer (worldReadBang w) ref dest count

def worldTake (w : BufferWorld) (ref : w.Ref) : WorldM w w.Vector :=
  source_take_IOBuffer (worldAccess w) (worldAllocateVector w) (worldWrapVector w) w.copyVector ref

def worldTakeGeneric (w : BufferWorld) (ref : w.Ref) : WorldM w w.Vector :=
  source_take_generic (worldAccess w) (worldAllocateVector w) w.copyVector w.readInto ref

def worldTakestring (w : BufferWorld) (ref : w.Ref) : WorldM w w.StringRef :=
  source_takestring_IOBuffer (worldAccess w) w.spanLength w.spanEmpty w.emptyString
    w.memoryToString (worldMemoryUInt w) (worldMemoryInt w) w.copyMemory w.takeMemory ref

def worldTruncate (w : BufferWorld) (ref : w.Ref) (count : Int) : WorldM w w.Ref :=
  source_truncate (worldAccess w) w.storage (fun n => pure (decide (n < 0)))
    (fun n limit => pure (decide (limit.val < n))) (fun n => liftIO (toI n)) toString ref count

def worldCopyuntil (w : BufferWorld) (out ref : w.Ref) (delimiter : Byte)
    (keep : Bool) (cancel : w.Cancel) : WorldM w w.Ref :=
  source_copyuntil (worldAccess w) w.view w.findFirst w.viewLength w.viewIndex w.isDefault
    w.writeView w.writeViewToken out ref delimiter keep cancel

def worldCopyline (w : BufferWorld) (out ref : w.Ref) (keep : Bool) (cancel : w.Cancel) : WorldM w w.Ref :=
  source_copyline_read (worldAccess w) w.view w.findFirst w.viewLength w.viewIndex
    w.isDefaultPure
    w.writeView w.writeViewToken out ref keep cancel

def worldRead (w : BufferWorld) (ref : w.Ref) (count : Int) : WorldM w w.Vector :=
  source_read_n (worldAccess w) (fun n available => liftIO (toI (min n available.val)))
    (worldAllocateVector w) w.readInto ref count

def worldReadAll (w : BufferWorld) (ref : w.Ref) : WorldM w w.Vector :=
  source_readavailable (worldAccess w) (worldAllocateVector w) w.readInto ref

def worldWriteByte (w : BufferWorld) (ref : w.Ref) (byte : Byte) : WorldM w I :=
  source_write_uint8 (worldAccess w) w.storage (fun data index byte => w.setIndex data byte index) ref byte

def worldReadByte (w : BufferWorld) (ref : w.Ref) : WorldM w Byte :=
  source_read_uint8 (worldAccess w) w.getIndex ref

def worldTakestringGeneric (w : BufferWorld) (ref : w.Ref) : WorldM w w.StringRef :=
  source_takestring_generic (worldTakeGeneric w) (stringVectorConvert w.vectorStringOps) ref

def worldUnsafeTake (w : BufferWorld) (ref : w.Ref) : WorldM w w.Vector :=
  source_unsafe_take (worldAccess w) w.emptyMemory w.memoryref w.wrapCheck w.newArray
    (fun n => liftNative (JuliaLean.base.int.convert .i64 n)) ref

def worldUnsafeTakestring (w : BufferWorld) (ref : w.Ref) : WorldM w w.StringRef :=
  source_unsafe_takestring (worldAccess w) w.spanLength w.spanEmpty w.emptyString
    w.memoryToString (worldMemoryUInt w) w.copyMemory w.takeMemory ref

def worldCopylineBuffer (w : BufferWorld) (out : w.Ref) (stream : w.Stream)
    (keep : Bool) (cancel : w.Cancel) : WorldM w w.Ref :=
  source_copyline_buffer (worldAccess w) w.isDefault w.checkCancel (worldNewBuffer w)
    w.copyStream w.copyStreamToken (worldTake w) w.vectorLength w.vectorLast w.vectorPop
    w.writeVector w.getIndex out stream keep cancel

def worldShow (w : BufferWorld) (out ref : w.Ref) : WorldM w Unit :=
  source_show (E := IOErr) (worldAccess w) w.lock w.unlock w.print out ref

def worldResult {H A : Type} (action : EStateM IOErr H A) (heap : H) : Except IOErr A :=
  match action.run heap with
  | .ok value _ => .ok value
  | .error error _ => .error error

def worldState {H A : Type} (action : EStateM IOErr H A) (heap : H) : H :=
  match action.run heap with
  | .ok _ next => next
  | .error _ next => next

def worldAfter {A : Type} (w : BufferWorld) (action : WorldM w A) (heap : w.Heap)
    (ref : w.Ref) : BufferState := worldSnapshot w (worldState action heap) ref

def worldValid (w : BufferWorld) (heap : w.Heap) (ref : w.Ref) : Prop :=
  stateInvariant (worldSnapshot w heap ref)

def worldWriteBytes (w : BufferWorld) (ref : w.Ref) (bytes : List UInt8) : WorldM w I := do
  let vector ← w.vectorFromBytes bytes
  let pointer ← w.vectorPointer vector
  worldWrite w ref pointer (u bytes.length) w.defaultCancel

def worldCopylineIO (w : BufferWorld) (out ref : w.Ref) (keep : Bool) (cancel : w.Cancel) : WorldM w w.Ref :=
  source_copyline_IO (worldAccess w) w.view w.findFirst w.viewLength w.viewIndex
    w.isDefaultPure w.writeView w.writeViewToken out ref keep cancel

def worldCopylineBufferBuffer (w : BufferWorld) (out ref : w.Ref) (keep : Bool)
    (cancel : w.Cancel) : WorldM w w.Ref :=
  source_copyline_buffer_buffer (worldAccess w) w.view w.findFirst w.viewLength w.viewIndex
    w.isDefaultPure w.writeView w.writeViewToken out ref keep cancel

inductive WorldAction (w : BufferWorld) where
  | write (pointer : JuliaLean.base.pointer.Ptr Byte) (count : U)
  | read (count : Int)

def runWorldActions (w : BufferWorld) (ref : w.Ref) : List (WorldAction w) →
    WorldM w (List UInt8 × List UInt8)
  | [] => pure ([], [])
  | .write pointer count :: actions => do
      let bytes := w.pointerBytes (← get) pointer count.val.toNat
      let accepted ← worldWrite w ref pointer count w.defaultCancel
      let (observed, writes) ← runWorldActions w ref actions
      pure (observed, bytes.take accepted.val.toNat ++ writes)
  | .read count :: actions => do
      let vector ← worldRead w ref count
      let bytes := w.vectorBytes (← get) vector
      let (observed, writes) ← runWorldActions w ref actions
      pure (bytes ++ observed, writes)

def worldActionsValid (w : BufferWorld) (ref : w.Ref) (heap : w.Heap) :
    List (WorldAction w) → Prop
  | [] => True
  | .write pointer count :: actions =>
      w.validPointer heap pointer count ∧
      worldActionsValid w ref
        (worldState (worldWrite w ref pointer count w.defaultCancel) heap) actions
  | .read count :: actions =>
      0 ≤ count ∧ worldActionsValid w ref (worldState (worldRead w ref count) heap) actions


/-! ## Core buffer contracts -/

/-- Position/file-size identities hold and successful operations preserve the field invariant. -/
def InvariantHolds : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    positionWithin io ∧ 0 ≤ (source_bytesavailable io).val ∧
    (source_eof io = true ↔ (source_bytesavailable io).val = 0) ∧
    (io.seekable = true →
      (source_position io).val + (source_bytesavailable io).val = (source_filesize io).val) ∧
    (∀ pointer count cancel, w.validPointer heap pointer count →
      (∀ written, worldResult (worldWrite w ref pointer count cancel) heap = .ok written →
        stateInvariant (worldAfter w (worldWrite w ref pointer count cancel) heap ref)) ∧
      (∀ returned, worldResult (source_ensureroom (worldAccess w) w.storage ref count) heap = .ok returned →
        stateInvariant (worldAfter w (source_ensureroom (worldAccess w) w.storage ref count) heap ref))) ∧
    (∀ byte, worldResult (worldReadByte w ref) heap = .ok byte →
      stateInvariant (worldAfter w (worldReadByte w ref) heap ref)) ∧
    (∀ n : Int,
      (worldResult (source_seek (worldAccess w) ref (clampToI n)) heap = .ok ref →
        stateInvariant (worldAfter w (source_seek (worldAccess w) ref (clampToI n)) heap ref)) ∧
      (worldResult (source_skip (worldAccess w) (source_seek (worldAccess w)) ref (clampToI n)) heap = .ok ref →
        stateInvariant (worldAfter w
          (source_skip (worldAccess w) (source_seek (worldAccess w)) ref (clampToI n)) heap ref))) ∧
    (resultOf source_closewrite io = .ok () → stateInvariant (stateOf source_closewrite io)) ∧
    (∀ n returned, worldResult (worldTruncate w ref n) heap = .ok returned →
      stateInvariant (worldAfter w (worldTruncate w ref n) heap ref)) ∧
    (∀ deleted, worldResult (source_compact (worldAccess w) w.storage ref) heap = .ok deleted →
      stateInvariant (worldAfter w (source_compact (worldAccess w) w.storage ref) heap ref)) ∧
    (∀ taken, worldResult (worldTakeGeneric w ref) heap = .ok taken →
      stateInvariant (worldAfter w (worldTakeGeneric w ref) heap ref)) ∧
    (∀ taken, worldResult (worldTake w ref) heap = .ok taken →
      stateInvariant (worldAfter w (worldTake w ref) heap ref)) ∧
    (worldResult (source_close (worldAccess w) w.storage ref) heap = .ok () →
      stateInvariant (worldAfter w (source_close (worldAccess w) w.storage ref) heap ref))

/-- Checked reads, writes, compaction, resizing, and unsafe reads stay inside backing bytes. -/
def NoOutOfBounds : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref → ∀ pointer count cancel,
    w.validPointer heap pointer count →
    worldResult (worldWrite w ref pointer count cancel) heap ≠ .error .outOfBounds ∧
    worldResult (worldReadByte w ref) heap ≠ .error .outOfBounds ∧
    resultOf source_peek_uint8 (worldSnapshot w heap ref) ≠ .error .outOfBounds ∧
    worldResult (source_unsafe_read (worldAccess w) (worldReadBang w) ref pointer count) heap ≠
      .error .outOfBounds ∧
    worldResult (source_compact (worldAccess w) w.storage ref) heap ≠ .error .outOfBounds ∧
    (∀ requested exact, worldResult (source_resize (worldAccess w) w.storage ref requested exact) heap ≠
      .error .outOfBounds)

/-- A seekable non-append write overwrites from the current position and advances by the
number of bytes that fit before `maxsize`. -/
def WriteAtPosition : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.writable = true → io.seekable = true → io.append = false →
    ∀ pointer count cancel, w.validPointer heap pointer count →
      let roomAction := source_ensureroom (worldAccess w) w.storage ref count
      let room := worldAfter w roomAction heap ref
      let write := worldWrite w ref pointer count cancel
      let expected := w.pointerBytes heap pointer count.val.toNat
      let start := room.ptr - i 1
      let n := min count.val.toNat (max 0 (room.maxsize.val - (source_position room).val)).toNat
      worldResult roomAction heap = .ok ref ∧ stateInvariant room ∧
      worldResult write heap = .ok (i n) ∧
      (worldAfter w write heap ref).data =
        room.data.take start.val.toNat ++ expected.take n ++ room.data.drop (start.val.toNat + n) ∧
      (source_position (worldAfter w write heap ref)).val = (source_position io).val + (i n).val

/-- Append writes add bytes at the end, stop at `maxsize`, and leave the read position alone. -/
def AppendWritesAtEnd : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.writable = true → io.append = true →
    ∀ pointer count cancel, w.validPointer heap pointer count →
      let roomAction := source_ensureroom (worldAccess w) w.storage ref count
      let room := worldAfter w roomAction heap ref
      let write := worldWrite w ref pointer count cancel
      let next := worldAfter w write heap ref
      let expected := w.pointerBytes heap pointer count.val.toNat
      let n := min count.val.toNat (max 0 (room.maxsize.val - (room.size - getOffset room).val)).toNat
      worldResult roomAction heap = .ok ref ∧ stateInvariant room ∧
      worldResult write heap = .ok (i n) ∧
      next.data = room.data.take room.size.val.toNat ++ expected.take n ++
        room.data.drop (room.size.val.toNat + n) ∧
      available room = available io ∧ available next = available room ++ expected.take n ∧
      source_position next = source_position io

/-- Writing bytes, seeking to zero, and reading returns the first `maxsize` bytes. -/
def WriteReadRoundtrip : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.readable = true → io.writable = true → io.seekable = true → io.append = false →
    io.size = io.offset → io.ptr = io.offset + i 1 →
    ∀ pointer count cancel, w.validPointer heap pointer count →
      let action : WorldM w w.Vector := do
        let _ ← worldWrite w ref pointer count cancel
        let _ ← source_seek (worldAccess w) ref (i 0)
        worldReadAll w ref
      ∃ vector, worldResult action heap = .ok vector ∧
        w.vectorBytes (worldState action heap) vector =
          (w.pointerBytes heap pointer count.val.toNat).take io.maxsize.val.toNat

/-- Every interleaving of pipe writes and reads preserves the order of written bytes. -/
def PipeFIFO : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.seekable = false → io.readable = true → io.writable = true → io.append = true →
    ∀ actions, worldActionsValid w ref heap actions →
      ∃ observed writes, worldResult (runWorldActions w ref actions) heap = .ok (observed, writes) ∧
        observed ++ available (worldAfter w (runWorldActions w ref actions) heap ref) =
          available io ++ writes

/-- Pipe reset restores the position saved by the `base/io.jl` mark/reset methods. -/
def PipeMarkReset : Prop :=
  ∀ w : BufferWorld, ∀ (markMethod resetMethod : w.Ref → WorldM w I),
    (∀ heap ref, worldValid w heap ref →
      worldResult (markMethod ref) heap = .ok (source_position (worldSnapshot w heap ref)) ∧
      (worldAfter w (markMethod ref) heap ref).mark = source_position (worldSnapshot w heap ref)) →
    (∀ heap ref, worldValid w heap ref → ismarked (worldSnapshot w heap ref) = true →
      worldResult (resetMethod ref) heap = .ok (worldSnapshot w heap ref).mark ∧
      source_position (worldAfter w (resetMethod ref) heap ref) = (worldSnapshot w heap ref).mark) →
    ∀ heap ref, worldValid w heap ref →
      let io := worldSnapshot w heap ref
      io.seekable = false → io.readable = true → io.writable = true → io.append = true →
      ∀ pointer count, w.validPointer heap pointer count → ∀ actions,
        let markAction : WorldM w I := do
          let accepted ← worldWrite w ref pointer count w.defaultCancel
          let _ ← markMethod ref
          pure accepted
        worldActionsValid w ref (worldState markAction heap) actions →
        ∃ beforeCount, worldResult markAction heap = .ok beforeCount ∧
          let markedHeap := worldState markAction heap
          let marked := worldSnapshot w markedHeap ref
          let afterHeap := worldState (runWorldActions w ref actions) markedHeap
          ∃ observed writes,
            worldResult (runWorldActions w ref actions) markedHeap = .ok (observed, writes) ∧
            worldResult (resetMethod ref) afterHeap = .ok marked.mark ∧
            available (worldAfter w (resetMethod ref) afterHeap ref) =
              available io ++ (w.pointerBytes heap pointer count.val.toNat).take beforeCount.val.toNat ++ writes

/-- Seek uses the public offset/live-mark invariant. Physical endpoint additions and
the reported position use native Int arithmetic; ordinary endpoint clamping follows
when the physical one-past-end index fits.
Julia source: base/iobuffer.jl:496-523; base/iostream.jl:143-146. -/
def SeekSpec : Prop :=
  ∀ io, DocumentedInvariant7 io → ∀ n : Int,
    (io.seekable = true ∨ (ismarked io = true ∧ clampToI n = io.mark) →
      resultOf (source_seek_integer (source_seek bufferAccess) intClampgt intClamplt
        intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val =
        ((clampI (clampToI ((clampToI n).val + io.offset.val + 1))
          (getOffset io + i 1) (io.size + i 1)) - io.offset - i 1).val) ∧
    (io.seekable = true → io.size.val < 2 ^ 63 - 1 →
      (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val =
        max 0 (min n (source_filesize io).val)) ∧
    (io.seekable = false →
      (resultOf (source_seek bufferAccess () (clampToI n)) io =
        if ismarked io then
          if clampToI n = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))) ∧
      (io.size.val < 2 ^ 63 - 1 → ismarked io = true → clampToI n = io.mark →
        (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val = io.mark.val))

/-- Skip clamps Integer arguments to Int, advances nonnegative requests with native
pointer arithmetic, and seeks to a widened, clamped relative target for negative
requests. Ordinary position equations apply when physical and logical ends fit.
Julia source: base/iobuffer.jl:475-493,512-523; base/iostream.jl:198-202. -/
def SkipSpec : Prop :=
  ∀ io, DocumentedInvariant7 io → ∀ n : Int,
    (0 ≤ n → resultOf (source_skip_integer (source_skip bufferAccess (source_seek bufferAccess))
        intClampgt intClamplt intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        ((io.ptr + imin (clampToI n) (io.size + i 1 - io.ptr)) - io.offset - i 1).val) ∧
    (0 ≤ n → io.size.val < 2 ^ 63 - 1 →
      io.size.val - io.offset.val ≤ 2 ^ 63 - 1 →
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        (source_position io).val + min n (source_bytesavailable io).val) ∧
    (n < 0 →
      let target := clampToI ((source_position io).val + (clampToI n).val)
      (io.seekable = true ∨ (ismarked io = true ∧ target = io.mark) →
        resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io = .ok () ∧
        (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
          ((clampI (clampToI (target.val + io.offset.val + 1))
            (getOffset io + i 1) (io.size + i 1)) - io.offset - i 1).val)) ∧
    (n < 0 → io.seekable = true → io.size.val < 2 ^ 63 - 1 →
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        max 0 ((source_position io).val + n)) ∧
    (n < 0 → io.seekable = false →
      let target := clampToI ((source_position io).val + (clampToI n).val)
      resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
        if ismarked io then
          if target = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked")))

/-- Truncation checks writability, seekability, nonnegative length and `maxsize`, then
retains or zero-pads bytes and clamps position to the new end. -/
def TruncateSpec : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref → ∀ n : Int,
    let io := worldSnapshot w heap ref
    let action := worldTruncate w ref n
    (worldResult action heap =
      if io.writable = false then .error (.jl (.argumentError "truncate failed, IOBuffer is not writeable"))
      else if io.seekable = false then .error (.jl (.argumentError "truncate failed, IOBuffer is not seekable"))
      else if n < 0 then .error (.jl (.argumentError
        ("truncate failed, n bytes must be ≥ 0, got " ++ toString n)))
      else if n > io.maxsize.val then .error (.jl (.argumentError
        ("truncate failed, n bytes is exceeds IOBuffer maxsize " ++ toString io.maxsize.val)))
      else .ok ref) ∧
    (0 ≤ n → n ≤ io.maxsize.val → worldResult action heap = .ok ref →
      content (worldAfter w action heap ref) = (content io ++ List.replicate n.toNat 0).take n.toNat ∧
      (source_position (worldAfter w action heap ref)).val = min (source_position io).val n)

/-- A writable `take!` returns retained contents and resets position, size, and mark. -/
def TakeSpec : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.isMemory = true → io.writable = true →
    ∃ vector, worldResult (worldTake w ref) heap = .ok vector ∧
      w.vectorBytes (worldState (worldTake w ref) heap) vector =
        (if io.seekable then content io else available io) ∧
      source_position (worldAfter w (worldTake w ref) heap ref) = i 0 ∧
      source_bytesavailable (worldAfter w (worldTake w ref) heap ref) = i 0 ∧
      source_filesize (worldAfter w (worldTake w ref) heap ref) = i 0 ∧
      ismarked (worldAfter w (worldTake w ref) heap ref) = false

/-- Counted reads return the unread prefix; `readbytes!` stores it in the destination, and `peek` leaves position unchanged. -/
def ReadSpec : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.readable = true →
    (∀ n : Int, 0 ≤ n →
      ∃ vector, worldResult (worldRead w ref n) heap = .ok vector ∧
        w.vectorBytes (worldState (worldRead w ref n) heap) vector = (available io).take n.toNat ∧
        available (worldAfter w (worldRead w ref n) heap ref) = (available io).drop n.toNat ∧
        (source_position (worldAfter w (worldRead w ref n) heap ref)).val =
          (source_position io).val + min n (source_bytesavailable io).val) ∧
    (available io = [] → worldResult (worldReadByte w ref) heap = .error .eofError ∧
      resultOf source_peek_uint8 io = .error .eofError) ∧
    (∀ byte rest, available io = byte :: rest →
      worldResult (worldReadByte w ref) heap = .ok (JuliaLean.base.int.lit .u8 byte.toNat) ∧
      available (worldAfter w (worldReadByte w ref) heap ref) = rest ∧
      resultOf source_peek_uint8 io = .ok byte ∧ stateOf source_peek_uint8 io = io) ∧
    (∀ dest (n : I), 0 ≤ n.val →
      let count := imin n (source_bytesavailable io)
      let action := worldReadBytes w ref dest n
      worldResult action heap = .ok count ∧
      (w.vectorBytes (worldState action heap) dest).take count.val.toNat =
        (available io).take count.val.toNat ∧
      (w.vectorBytes (worldState action heap) dest).drop count.val.toNat =
        (w.vectorBytes heap dest).drop count.val.toNat ∧
      (w.vectorBytes (worldState action heap) dest).length =
        max (w.vectorBytes heap dest).length count.val.toNat ∧
      available (worldAfter w action heap ref) = (available io).drop count.val.toNat ∧
      (source_position (worldAfter w action heap ref)).val = (source_position io).val + count.val) ∧
    (∀ dest,
      let count := imin (i (w.vectorBytes heap dest).length) (source_bytesavailable io)
      let action := worldReadDefault w ref dest none
      worldResult action heap = .ok count ∧
      (w.vectorBytes (worldState action heap) dest).take count.val.toNat =
        (available io).take count.val.toNat ∧
      (w.vectorBytes (worldState action heap) dest).drop count.val.toNat =
        (w.vectorBytes heap dest).drop count.val.toNat ∧
      available (worldAfter w action heap ref) = (available io).drop count.val.toNat ∧
      (source_position (worldAfter w action heap ref)).val = (source_position io).val + count.val) ∧
    (∀ {N : Type} (length : w.Vector → WorldM w N) (toInt : N → WorldM w I)
      dest requested error, worldResult (toInt requested) heap = .error error →
      worldResult (source_readbytes_default (worldAccess w) length toInt w.vectorLength
        w.vectorResize w.vectorBounds w.vectorPointer (worldReadBang w) ref dest (some requested)) heap =
          .error error)

/-- Delimited reads return through the delimiter, honor `keep`, strip CRLF for lines,
and consume exactly those bytes. -/
def ReadUntilSpec : Prop :=
  ∀ w : BufferWorld, ∀ heap ref out, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.readable = true → ∀ (delimiter : UInt8) keep cancel,
      let action := worldCopyuntil w out ref (JuliaLean.base.int.lit .u8 delimiter.toNat) keep cancel
      worldResult action heap = .ok out ∧
      w.outputBytes (worldState action heap) out =
        w.outputBytes heap out ++ untilSpec (available io) delimiter keep ∧
      available (worldAfter w action heap ref) = afterSpec (available io) delimiter ∧
      let line := worldCopyline w out ref keep cancel
      worldResult line heap = .ok out ∧
      w.outputBytes (worldState line heap) out = w.outputBytes heap out ++ lineSpec (available io) keep ∧
      available (worldAfter w line heap ref) = afterSpec (available io) 0x0a

/-- `occursin` searches only the bytes currently available. -/
def OccursinSpec : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref → ∀ delimiter : UInt8,
    worldResult (source_occursin (worldAccess w) w.view w.member
      (JuliaLean.base.int.lit .u8 delimiter.toNat) ref) heap =
        .ok (decide (delimiter ∈ available (worldSnapshot w heap ref)))

/-- A readable but non-writable buffer returns its contents from the source `take!` method. -/
def TakeReadOnly : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.isMemory = true → io.readable = true → io.writable = false →
    ∃ vector, worldResult (worldTake w ref) heap = .ok vector ∧
      w.vectorBytes (worldState (worldTake w ref) heap) vector =
        (if io.seekable then content io else available io)

/-- After `take!`, even a read-only buffer has position zero. -/
def TakeResets : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.isMemory = true → io.readable = true →
    (∃ vector, worldResult (worldTake w ref) heap = .ok vector) →
      source_position (worldAfter w (worldTake w ref) heap ref) = i 0

/-- `takestring!` returns a String whose bytes equal the source `take!` result. -/
def TakestringEqTake : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    (worldSnapshot w heap ref).isMemory = true → ∀ vector,
    worldResult (worldTake w ref) heap = .ok vector →
      ∃ string, worldResult (worldTakestring w ref) heap = .ok string ∧
        w.stringBytes (worldState (worldTakestring w ref) heap) string =
          w.vectorBytes (worldState (worldTake w ref) heap) vector

/-- `readuntil` and `readline` reject unreadable buffers with `ArgumentError`. -/
def ReadUntilUnreadable : Prop :=
  ∀ w : BufferWorld, ∀ heap ref out, worldValid w heap ref →
    (worldSnapshot w heap ref).readable = false → ∀ delimiter keep cancel,
      (∃ message, worldResult (worldCopyuntil w out ref delimiter keep cancel) heap =
        .error (.jl (.argumentError message))) ∧
      (∃ message, worldResult (worldCopyline w out ref keep cancel) heap =
        .error (.jl (.argumentError message)))

/-- Copying a line into the middle of an output buffer has the same state as writing it
without its newline. -/
def CopylineMiddle : Prop :=
  ∀ w : BufferWorld, ∀ heap out stream, worldValid w heap out →
    let io := worldSnapshot w heap out
    io.isMemory = true → io.writable = true → io.append = false → io.ptr.val ≤ io.size.val →
    ∀ cancel,
      let action := worldCopylineBuffer w out stream false cancel
      let write := worldWriteBytes w out (stripNewline (w.streamBytes heap stream))
      (worldResult action heap).map (fun ref => worldSnapshot w (worldState action heap) ref) =
        (worldResult write heap).map (fun _ => worldAfter w write heap out)

/-- Copying at the end has the same observable buffer state as writing the newline-free line. -/
def CopylineAtEnd : Prop :=
  ∀ w : BufferWorld, ∀ heap out stream, worldValid w heap out →
    let io := worldSnapshot w heap out
    io.writable = true → (io.append = true ∨ io.ptr = io.size + i 1) →
    ∀ cancel,
      let action := worldCopylineBuffer w out stream false cancel
      let write := worldWriteBytes w out (stripNewline (w.streamBytes heap stream))
      (worldResult action heap).map (fun ref => worldSnapshot w (worldState action heap) ref) =
        (worldResult write heap).map (fun _ => worldAfter w write heap out)

/-- Writing to a writable vector-backed buffer does not fail with `MethodError`. -/
def WriteNoMethodError : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    (worldSnapshot w heap ref).writable = true → ∀ pointer count cancel,
    w.validPointer heap pointer count → ∀ name,
      worldResult (worldWrite w ref pointer count cancel) heap ≠ .error (.jl (.methodError name))

/-- `PipeBuffer` accepts the documented integer maxsize types. -/
def PipeBufferMaxsizeInteger : Prop :=
  ∀ t m, t.min ≤ m → m ≤ t.max → 0 ≤ m → m < 2 ^ 63 →
    ∃ io, runPipeBufferMaxsize t m = .ok io

/-- Truncation retains a mark that still points within the shortened buffer. -/
def TruncateKeepsMark : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    ismarked io = true → ∀ n : Int, io.mark.val ≤ n →
      worldResult (worldTruncate w ref n) heap = .ok ref →
        ismarked (worldAfter w (worldTruncate w ref n) heap ref) = true

/-! ## Constructor, representation, and low-level method contracts -/

/-- String-backed allocation and wrapping preserve the requested byte count. -/
def StringMemoryInBounds : Prop :=
  ∀ (stringN : Int → Except IOErr (List UInt8)),
    (∀ n, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
      ∃ bytes, stringN n = .ok bytes ∧ bytes.length = n.toNat) →
    ∀ (wrap : List UInt8 → Except IOErr (List UInt8)),
      (∀ bytes, wrap bytes = .ok bytes) →
      ∀ n, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
        ∃ bytes, source_StringMemory toU (fun u => stringN u.val) wrap n = .ok bytes ∧ bytes.length = n.toNat

/-- Reads, used spans, takes, and exact-size string copies stay within the backing vector. -/
def IOBufferOperationsInBounds : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.isMemory = true →
    (∀ first last, source_get_used_span (w.fields heap ref) = .ok (first, last) →
      1 ≤ first.val ∧ first.val ≤ last.val + 1 ∧ last.val ≤ io.data.length) ∧
    (io.seekable = false → ismarked io = true →
      ∃ translated, source_translate_seek_position (w.fields heap ref) io.mark = .ok translated ∧
        source_get_used_span (w.fields heap ref) = .ok (imin io.ptr translated, io.size)) ∧
    (io.seekable = true →
      (∀ byte, worldResult (worldReadByte w ref) heap = .ok byte →
        byte.val = (io.data.getD (io.ptr.val - 1).toNat 0).toNat) ∧
      (∀ byte, resultOf source_peek_uint8 io = .ok byte →
        byte = io.data.getD (io.ptr - i 1).val.toNat 0) ∧
      (∃ vector, worldResult (worldUnsafeTake w ref) heap = .ok vector ∧
        w.vectorBytes (worldState (worldUnsafeTake w ref) heap) vector = content io) ∧
      (∃ string, worldResult (worldUnsafeTakestring w ref) heap = .ok string ∧
        w.stringBytes (worldState (worldUnsafeTakestring w ref) heap) string = content io) ∧
      (∃ string, worldResult (worldTakestring w ref) heap = .ok string ∧
        w.stringBytes (worldState (worldTakestring w ref) heap) string = content io))

/-- The `show` pointer equals the read position plus one. -/
def ShowPtrPosition : Prop :=
  ∀ w : BufferWorld, ∀ heap out ref, worldValid w heap ref →
    worldResult (worldShow w out ref) heap = .ok () ∧
    ∃ value : I, (w.printed (worldState (worldShow w out ref) heap) out)[20]? =
      some (.integer value) ∧ value.val = (source_position (worldSnapshot w heap ref)).val + 1

def ShowUncompacted : Prop :=
  ∀ w : BufferWorld, ∀ heap out ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    0 ≤ io.offset.val → worldResult (worldShow w out ref) heap = .ok () ∧
      (w.printed (worldState (worldShow w out ref) heap) out)[14]? = some (.integer (io.size - getOffset io)) ∧
      (w.printed (worldState (worldShow w out ref) heap) out)[20]? = some (.integer (io.ptr - getOffset io))

/-- The unchecked constructor initializes observable state from its typed inputs. -/
def NewGenericFields : Prop :=
  ∀ {T : Type} (data : T) (dataBytes : T → List UInt8) (isMemory : T → Bool)
    (readable writable seekable append : Bool) (maxsize : I),
    (dataBytes data).length < 2 ^ 63 →
    let io := runNewGenericBuffer data dataBytes isMemory readable writable seekable append maxsize
    io.data = dataBytes data ∧ io.isMemory = isMemory data ∧ io.reinit = false ∧
    io.readable = readable ∧ io.writable = writable ∧ io.seekable = seekable ∧
    io.append = append ∧ io.size = i (dataBytes data).length ∧ io.maxsize = maxsize ∧
    io.ptr = i 1 ∧ io.offset = i 0 ∧ io.mark = i (-1)


namespace Round14

def JuliaLengthBounded (length : Nat) : Prop := length < 2 ^ 62

def VectorSizeBounded (v : Vec) : Prop :=
  JuliaLengthBounded v.mem.length ∧ v.off + v.len ≤ v.mem.length

/-- The Vector overload preserves the view's offset and length on a valid Julia-sized Vector. -/
def VectorConstructorR14 : Prop :=
  ∀ v readable writable seekable append maxsize truncate io,
    VectorSizeBounded v →
    runGenericIOBufferVector v readable writable seekable append maxsize truncate = .ok io →
    io.offset = i v.off ∧ io.ptr = i (v.off + 1) ∧
    io.size = i (if truncate then v.off else v.len + v.off) ∧ io.isMemory = true

end Round14

/-- iocov-iobuffer-offset-accessors. The complete signed Int domain includes
typemin(Int), explicitly permitted by base/iobuffer.jl:85-87. This statement
deliberately retains that boundary even if wrapping negation refutes it.
The actual accessor definitions are base/iobuffer.jl:163-164. -/
def OffsetAccessors : Prop :=
  ∀ io : BufferState,
    source_get_offset io - source_get_compacted io = io.offset ∧
    (source_get_offset io = i 0 ∨ source_get_compacted io = i 0)

/-- StringVector preserves allocator bytes and the requested length. -/
def StringAllocators : Prop :=
  ∀ (stringN : Int → Except IOErr (List UInt8))
    (unsafeWrap wrapArray : List UInt8 → Except IOErr (List UInt8)),
    (∀ bytes, unsafeWrap bytes = .ok bytes) →
    (∀ bytes, wrapArray bytes = .ok bytes) →
    ∀ n bytes, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
      stringN n = .ok bytes → bytes.length = n.toNat →
      source_StringVector toU (fun u => stringN u.val) unsafeWrap
        (fun m => .ok m) (fun m => i m.length) (fun m _ => wrapArray m) n = .ok bytes

/-- Public constructors preserve their selected capabilities and create valid buffer states. -/
def PublicConstructors : Prop :=
  (∀ data (read write append truncate : Option Bool) maxsize io,
    0 ≤ maxsize → maxsize < 2 ^ 63 → (dataBytes data).length < 2 ^ 63 →
    runIOBufferData (fun d _ => .ok d) data read write append truncate maxsize none = .ok io →
      let flags := openFlags read write none truncate append
      io.readable = flags.read ∧ io.writable = flags.write ∧ io.seekable = true ∧
      io.append = flags.append ∧ stateInvariant io) ∧
  (∀ (read write append truncate : Option Bool) maxsize hint io,
    0 ≤ maxsize → maxsize < 2 ^ 63 →
    (hint = none ∨ ∃ n, hint = some n ∧ -(2 ^ 63) ≤ n ∧ n < 2 ^ 63) →
    runIOBufferEmpty read write append truncate maxsize hint = .ok io →
      let flags := openFlags read write none truncate append
      io.readable = flags.read ∧ io.writable = flags.write ∧ io.seekable = true ∧
      io.append = flags.append ∧ io.size = i 0 ∧ stateInvariant io) ∧
  (∀ data maxsize io, 0 ≤ maxsize.val →
    runPipeBufferData data maxsize = .ok io →
      io.readable = true ∧ io.writable = true ∧ io.seekable = false ∧
      io.append = true ∧ io.maxsize = maxsize ∧ stateInvariant io)

/- An internal truncated pipe is empty, reports EOF, and retains its requested size limit. -/
def TruncatedPipeCorrect : Prop :=
  ∀ data maxsize io,
    runTruncatedPipebuffer data maxsize = .ok io →
      io.size = source_get_offset io ∧ source_filesize io = i 0 ∧
      source_bytesavailable io = i 0 ∧ source_eof io = true ∧ io.maxsize = maxsize ∧
      worldResult (source_read_uint8 bufferAccess
        (fun bytes index => lift ((getChecked bytes index).map
          (fun byte => JuliaLean.base.int.lit .u8 byte.toNat))) ()) io = .error .eofError

/-- Both storage helpers preserve the length guaranteed by the external allocator. -/
def SimilarDataCorrect : Prop :=
  ∀ (similar : List UInt8 → I → Except IOErr (List UInt8))
    (stringN : Int → Except IOErr (List UInt8))
    (wrap : List UInt8 → Except IOErr (List UInt8)),
    (∀ bytes, wrap bytes = .ok bytes) →
    ∀ b n genericBytes memoryBytes, 0 ≤ n.val →
      similar b.data n = .ok genericBytes → genericBytes.length = n.val.toNat →
      stringN n.val = .ok memoryBytes → memoryBytes.length = n.val.toNat →
      source_similar_data_generic (m := Except IOErr)
        { get := fun _ => .ok (bufferFields b)
          set := fun _ _ => .ok ()
          new := fun _ => .ok ()
          isIOBuffer := fun _ => .ok b.isMemory }
        similar () n = .ok genericBytes ∧
      source_similar_data_IOBuffer (m := Except IOErr)
        { get := fun _ => .ok (bufferFields b)
          set := fun _ _ => .ok ()
          new := fun _ => .ok ()
          isIOBuffer := fun _ => .ok b.isMemory }
        (fun u => stringN u.val) wrap () n = .ok memoryBytes ∧
      genericBytes.length = memoryBytes.length

/-- The unreadable helper throws the documented error, which byte reads and peeks propagate. -/
def ThrowNotReadable : Prop :=
  (∀ α, (source_throw_not_readable : Except IOErr α) =
    .error (.jl (.argumentError "read failed, IOBuffer is not readable"))) ∧
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    (worldSnapshot w heap ref).readable = false →
      worldResult (worldReadByte w ref) heap =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      resultOf source_peek_uint8 (worldSnapshot w heap ref) =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable"))

/-- The vector and dense `unsafe_read!` methods transfer consecutive source bytes. -/
def UnsafeReadMethods : Prop :=
  ∀ w : BufferWorld, ∀ {Start Index : Type} (startValue : Start → Int)
    (sourceIndex : Start → U → WorldM w Index)
    (getindex : w.Data → Index → WorldM w Byte)
    (pointer : w.Data → Start → WorldM w (JuliaLean.base.pointer.Ptr Byte)),
    ∀ heap (src : w.Data) dest start (count : U),
      1 ≤ startValue start →
      (startValue start - 1).toNat + count.val.toNat ≤ (w.bytes heap src).length →
      w.validPointer heap dest count →
        let vector := source_unsafe_read_vector sourceIndex getindex w.store dest src start count
        let dense := source_unsafe_read_dense pointer w.copyPointer dest src start count
        worldResult vector heap = .ok () ∧ worldResult dense heap = .ok () ∧
        w.pointerBytes (worldState vector heap) dest count.val.toNat =
          ((w.bytes heap src).drop (startValue start - 1).toNat).take count.val.toNat ∧
        w.pointerBytes (worldState dense heap) dest count.val.toNat =
          ((w.bytes heap src).drop (startValue start - 1).toNat).take count.val.toNat

/-- Little-endian loading equals the base-256 value of the selected bytes. -/
def LoadFromArrayLittleEndian : Prop :=
  ∀ (data : List UInt8) (start : Nat) (kind : Multibyte),
    let width := (JuliaLean.base.int.sizeof (initialWord kind)).val.toNat
    start + width ≤ data.length →
    data.length < 2 ^ 63 →
    source_load_from_array (m := Except IOErr)
      (fun bytes index => .ok (JuliaLean.base.int.lit .u8 (bytes.getD (index.val - 1).toNat 0).toNat))
      (fun _ w => .ok w) (fun k w => .ok (bitcastWord k w)) kind data (i (start + 1)) =
        .ok (bitcastWord kind (JuliaLean.base.int.lit (wordType kind)
          (((List.range width).map (fun k => (data.getD (start + k) 0).toNat * 256 ^ k)).sum)))

/-- Both source multibyte peek paths leave the buffer pointer unchanged. -/
def PeekMethodsDoNotAdvance : Prop :=
  ∀ io, stateInvariant io → ∀ (kind : Multibyte)
    (ltoh : (t : IntTy) → JInt t → Except IOErr (JInt t))
    (full : (k : Multibyte) → JInt (wordType k) → Except IOErr (valueType k)),
    stateOf (peekArrayModel kind (fun t w => lift (ltoh t w)) (fun k w => lift (full k w))) io = io ∧
    ∀ (heap : JuliaLean.base.pointer.ByteHeap)
      (codec : (k : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType k))
      (pointer : List UInt8 → I → Except IOErr (JuliaLean.base.pointer.Ptr Byte))
      (withPreserve : (k : Multibyte) → Unit → (Unit → Except IOErr (valueType k)) →
        Except IOErr (valueType k)),
      let runDense : M (valueType kind) :=
        let inst : MonadExceptOf JuliaLean.base.pointer.PointerError M :=
          { throw := fun _ => throwThe IOErr .outOfBounds
            tryCatch := fun b _ => b }
        @source_peek_multibyte_dense M _ _ inst Unit (List UInt8)
          bufferAccess { get := pure heap, set := fun _ => pure () } codec
          (fun d p => lift (pointer d p))
          (fun k r f => do
            let s ← get
            lift (withPreserve k r (fun u => resultOf (f u) s)))
          () kind
      stateOf runDense io = io

/-- Source multibyte reads return the peeked value and advance one value width. -/
def ReadMultiAdvances : Prop :=
  ∀ io, stateInvariant io → ∀ (kind : Multibyte)
    (ltoh : (t : IntTy) → JInt t → Except IOErr (JInt t))
    (full : (k : Multibyte) → JInt (wordType k) → Except IOErr (valueType k))
    (value : valueType kind),
    let ltohM : (t : IntTy) → JInt t → M (JInt t) := fun t w => lift (ltoh t w)
    let fullM : (k : Multibyte) → JInt (wordType k) → M (valueType k) := fun k w => lift (full k w)
    let getByte : List UInt8 → I → M Byte := fun bytes idx => do
      let b ← lift (getChecked bytes idx)
      pure (JuliaLean.base.int.lit .u8 b.toNat)
    resultOf (peekArrayModel kind ltohM fullM) io = .ok value →
      resultOf (source_read_multibyte bufferAccess getByte ltohM fullM () kind) io = .ok value ∧
      source_position (stateOf (source_read_multibyte bufferAccess getByte ltohM fullM () kind) io) =
        source_position io + JuliaLean.base.int.sizeof (initialWord kind)

/-- Pointer reads convert the source UInt reader's value and consume the same bytes. -/
def PtrReadIsUIntRead : Prop :=
  ∀ io, stateInvariant io → ∀ (T : Type) value,
    let getByte : List UInt8 → I → M Byte := fun bytes idx => do
      let b ← lift (getChecked bytes idx)
      pure (JuliaLean.base.int.lit .u8 b.toNat)
    resultOf readUIntModel io = .ok value →
      resultOf (source_read_pointer (T := T) bufferAccess getByte
        (fun _ w => pure w) (fun _ v => pure (bitcastWord _ v)) ()) io =
          .ok (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned value)) ∧
      stateOf (source_read_pointer (T := T) bufferAccess getByte
        (fun _ w => pure w) (fun _ v => pure (bitcastWord _ v)) ()) io = stateOf readUIntModel io

/-- Closing writes preserves reads and rejects every later byte write. -/
def ReadWriteFlags : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    source_isreadable io = io.readable ∧ source_iswritable io = io.writable ∧
    source_isreadable (stateOf source_closewrite io) = io.readable ∧
    source_iswritable (stateOf source_closewrite io) = false ∧
    worldResult (worldReadByte w ref)
      (w.setFields heap ref { w.fields heap ref with writable := false }) =
        worldResult (worldReadByte w ref) heap ∧
    (∀ byte, worldResult (worldWriteByte w ref byte)
      (w.setFields heap ref { w.fields heap ref with writable := false }) =
        .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")))

def SeekMethodsCorrect : Prop :=
  SeekSpec ∧ SkipSpec ∧
    (∀ io, stateInvariant io → ∀ n : I,
      source_translate_seek_position (bufferFields io) n =
        .ok (clampToI (n.val + io.offset.val + 1))) ∧
    (∀ io, stateInvariant io →
      (source_position (stateOf (source_seekend bufferAccess ()) io)).val = (source_filesize io).val)

/- Room management takes the no-allocation fast path, reallocates reinitialized storage, and
   sends insufficient capacity through the source slow path. -/
def EnsureRoomMethods : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref → ∀ count : U,
    let io := worldSnapshot w heap ref
    let action := source_ensureroom (worldAccess w) w.storage ref count
    (io.writable = false → worldResult action heap =
      .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")) ∧
      worldAfter w action heap ref = io) ∧
    (io.writable = true → io.reinit = true →
      worldResult action heap = worldResult
        (source_ensureroom_reallocate (worldAccess w) w.storage ref count) heap ∧
      (worldResult action heap = .ok ref →
        let next := worldAfter w action heap ref
        next.reinit = false ∧ next.offset = -getCompacted io ∧
        next.data.length = (imin io.maxsize (JInt.rem .i64 count)).val.toNat)) ∧
    (io.writable = true → io.reinit = false →
      let start := if io.append then io.size else io.ptr - i 1
      let space := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
      (space.val ≥ (JInt.rem .i64 count).val →
        worldResult action heap = .ok ref ∧ worldAfter w action heap ref = io) ∧
      (space.val < (JInt.rem .i64 count).val →
        worldResult action heap =
          worldResult (source_ensureroom_slowpath (worldAccess w) w.storage ref count space) heap ∧
        (worldResult action heap = .ok ref →
          available (worldAfter w action heap ref) = available io ∧
          source_position (worldAfter w action heap ref) = source_position io))) ∧
    (∀ n : I, n.val < 0 →
      worldResult (source_ensureroom_int (worldAccess w) w.storage ref n) heap =
        .error (.jl (.inexactError "convert")))

def CloseMethodCorrect : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    let resized := worldAfter w (source_resize (worldAccess w) w.storage ref (i 0) true) heap ref
    let before := if io.writable && !io.reinit then resized else io
    let action := source_close (worldAccess w) w.storage ref
    worldResult action heap = .ok () →
      let closed := worldAfter w action heap ref
      closed.readable = false ∧ closed.writable = false ∧ closed.seekable = false ∧
      closed.size = i 0 ∧ closed.maxsize = i 0 ∧ closed.ptr = i 1 ∧ closed.mark = i (-1) ∧
      closed.offset = -getCompacted before ∧ closed.data = before.data ∧
      closed.isMemory = before.isMemory ∧ closed.reinit = before.reinit ∧ closed.append = before.append

def IsopenCorrect : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    (source_isopen source_bytesavailable io = true ↔
      io.readable = true ∨ io.writable = true ∨ io.seekable = true ∨ 0 < (source_bytesavailable io).val) ∧
    (source_isopen source_bytesavailable (stateOf source_closewrite io) = true ↔
      io.readable = true ∨ io.seekable = true ∨ 0 < (source_bytesavailable io).val) ∧
    (worldResult (source_close (worldAccess w) w.storage ref) heap = .ok () →
      source_isopen source_bytesavailable
        (worldAfter w (source_close (worldAccess w) w.storage ref) heap ref) = false)

/-- Generic and IOBuffer take methods return retained bytes and reset writable buffers. -/
def TakeMethodsCorrect : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.writable = true → io.isMemory = true →
      ∃ vector string, worldResult (worldTakeGeneric w ref) heap = .ok vector ∧
        worldResult (worldTakestringGeneric w ref) heap = .ok string ∧
        w.vectorBytes (worldState (worldTakeGeneric w ref) heap) vector =
          w.stringBytes (worldState (worldTakestringGeneric w ref) heap) string ∧
        (∃ memoryVector, worldResult (worldTake w ref) heap = .ok memoryVector ∧
          w.vectorBytes (worldState (worldTake w ref) heap) memoryVector =
            (if io.seekable then content io else available io)) ∧
        (worldAfter w (worldTakeGeneric w ref) heap ref).reinit = true ∧
        (worldAfter w (worldTake w ref) heap ref).reinit = true

/-- The unsafe take view contains exactly the used bytes. -/
def UnsafeTakeReturnsUsed : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.isMemory = true → io.seekable = true →
      ∃ vector, worldResult (worldUnsafeTake w ref) heap = .ok vector ∧
        w.vectorBytes (worldState (worldUnsafeTake w ref) heap) vector = content io

/-- Writing another buffer consumes its unread bytes, and self-copy is rejected before writing. -/
def WriteFromConsumes : Prop :=
  ∀ w : BufferWorld, ∀ heap out ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    let action := source_write_buffer_to_IO (worldAccess w) w.identical w.view
      (fun out view => do
        let n ← w.viewLength view
        w.writeView out view
        pure n) out ref
    (worldResult (w.identical out ref) heap = .ok true →
      worldResult action heap = .error (.jl (.argumentError
        "writing all content from an IOBuffer into itself is invalid")) ∧ worldState action heap = heap) ∧
    (worldResult (w.identical out ref) heap = .ok false → io.readable = true →
      ∀ count, worldResult action heap = .ok count →
        available (worldAfter w action heap ref) = [] ∧
        (source_position (worldAfter w action heap ref)).val = (io.size + i 1 - io.offset).val)

/-- The vector write stores pointer bytes; large dense writes call the copy callback at the exact range. -/
def UnsafeWriteMethods : Prop :=
  ∀ w : BufferWorld, ∀ heap data pointer (start : I) count,
    1 ≤ start.val → (start.val - 1).toNat + count.val.toNat ≤ (w.bytes heap data).length →
    w.validPointer heap pointer count →
      let expected := (w.bytes heap data).take (start.val - 1).toNat ++
        w.pointerBytes heap pointer count.val.toNat ++
        (w.bytes heap data).drop ((start.val - 1).toNat + count.val.toNat)
      let vector := source_unsafe_write_vector w.setIndexU (fun p => w.load p (u 1))
        (fun p => pure (pointerAdvance p)) data pointer start count
      let dense := source_unsafe_write_dense w.setIndex w.load w.pointer w.copyPointer
        data pointer start count
      worldResult vector heap = .ok () ∧ w.bytes (worldState vector heap) data = expected ∧
      (∃ result, worldResult dense heap = .ok result) ∧ w.bytes (worldState dense heap) data = expected

/-- A one-byte write followed by a one-byte read returns that byte when capacity allows. -/
def ByteReadWriteMethods : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.writable = true → io.readable = true → io.seekable = true → io.append = false →
    ∀ byte, io.maxsize.val > (source_position io).val →
      worldResult (worldWriteByte w ref byte) heap = .ok (i 1) →
        worldResult (worldReadByte w ref) (worldState (worldWriteByte w ref byte) heap) = .ok byte

/-- The buffer line readers return through the newline, strip CRLF when requested, and write the same bytes to IO or IOBuffer outputs. -/
def CopylineMethods : Prop :=
  ∀ w : BufferWorld, ∀ heap ref out, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.readable = true → ∀ keep cancel,
      (∀ action ∈ [worldCopyline w out ref keep cancel, worldCopylineIO w out ref keep cancel,
          worldCopylineBufferBuffer w out ref keep cancel],
        worldResult action heap = .ok out ∧
        w.outputBytes (worldState action heap) out = w.outputBytes heap out ++ lineSpec (available io) keep ∧
        available (worldAfter w action heap ref) = afterSpec (available io) 0x0a ∧
        (worldValid w heap out → (worldSnapshot w heap out).writable = true →
          worldAfter w action heap out =
            worldAfter w (worldWriteBytes w out (lineSpec (available io) keep)) heap out)) ∧
      (∀ stream, w.streamBytes heap stream = available io → worldValid w heap out →
        (worldSnapshot w heap out).writable = true →
        let output := worldCopylineBuffer w out stream keep cancel
        let write := worldWriteBytes w out (lineSpec (available io) keep)
        (worldResult output heap).map (fun ref => worldSnapshot w (worldState output heap) ref) =
          (worldResult write heap).map (fun _ => worldAfter w write heap out))

/-- CRC results cover the unread prefix, consume its bytes, and preserve documented errors. -/
def bufferCrcCalls (unsafeCRC : (List UInt8 × I) → I → UInt32 → Except IOErr UInt32)
    (pointer : List UInt8 → I → List UInt8 × I) :
    CrcCalls M (List UInt8) Int I Int (List UInt8 × I) where
  negative := fun nb => pure (decide (nb < 0))
  showCount := fun nb => pure (toString nb)
  minimum := fun nb avail => lift (toI (min nb avail.val))
  iszero := fun n => pure (decide (n.val = 0))
  pointer := fun d ptr => pure (pointer d ptr)
  unsafeCrc := fun p n crc => lift (unsafeCRC p n crc)
  addPointer := fun ptr n => pure (ptr.val + n.val)
  toNativePointer := fun s => pure (i s)

def defaultCrcCalls (unsafeCRC : (List UInt8 × I) → I → UInt32 → Except IOErr UInt32)
    (pointer : List UInt8 → I → List UInt8 × I) :
    CrcCalls M (List UInt8) I I Int (List UInt8 × I) where
  negative := fun nb => pure (decide (nb.val < 0))
  showCount := fun nb => pure (toString nb.val)
  minimum := fun nb avail => pure (imin nb avail)
  iszero := fun n => pure (decide (n.val = 0))
  pointer := fun d ptr => pure (pointer d ptr)
  unsafeCrc := fun p n crc => lift (unsafeCRC p n crc)
  addPointer := fun ptr n => pure (ptr.val + n.val)
  toNativePointer := fun s => pure (i s)

def CrcDefaultUsesAvailable : Prop :=
  ∀ (checksum : List UInt8 → UInt32 → UInt32)
    (unsafeCRC : (List UInt8 × I) → I → UInt32 → Except IOErr UInt32),
    (∀ seed, checksum [] seed = seed) →
    (∀ data (ptr count : I) seed, 0 ≤ count.val → 1 ≤ ptr.val →
      ptr.val + count.val - 1 ≤ data.length →
      unsafeCRC (data, ptr) count seed =
        .ok (checksum (slice data ptr.val (ptr.val + count.val - 1)) seed)) →
    ∀ io, stateInvariant io → ∀ (n : Int) (seed : Option UInt32),
      let pointer := fun (data : List UInt8) (index : I) => (data, index)
      let calls := bufferCrcCalls unsafeCRC pointer
      let defCalls := defaultCrcCalls unsafeCRC pointer
      let preserve : Unit → (Unit → M UInt32) → M UInt32 := fun _ f => f ()
      let initial := seed.getD 0
      (n < 0 →
        resultOf (source_crc32c_bytes bufferAccess calls preserve () n seed) io =
          .error (.jl (.argumentError
            ("number of bytes to checksum must be ≥ 0, got " ++ toString n)))) ∧
      (0 ≤ n → io.readable = false →
        resultOf (source_crc32c_bytes bufferAccess calls preserve () n seed) io =
          .error (.jl (.argumentError "read failed, IOBuffer is not readable"))) ∧
      (0 ≤ n → io.readable = true →
        let count := min n (source_bytesavailable io).val
        resultOf (source_crc32c_bytes bufferAccess calls preserve () n seed) io =
          .ok (checksum ((available io).take count.toNat) initial) ∧
        (source_bytesavailable
          (stateOf (source_crc32c_bytes bufferAccess calls preserve () n seed) io)).val =
            (source_bytesavailable io).val - count) ∧
      (io.readable = true →
        resultOf (source_crc32c_default bufferAccess defCalls preserve () seed) io =
          .ok (checksum (available io) initial) ∧
        available (stateOf (source_crc32c_default bufferAccess defCalls preserve () seed) io) = [])
/-! ## Additional user-requested read, write, and position statements -/

/-- readavailable returns all unread bytes, read(n) returns its available prefix, and peek does not advance. -/
def ReadAvailableAndPeekCounts : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    io.readable = true →
      (∃ vector, worldResult (worldReadAll w ref) heap = .ok vector ∧
        w.vectorBytes (worldState (worldReadAll w ref) heap) vector = available io) ∧
      source_bytesavailable (worldAfter w (worldReadAll w ref) heap ref) = i 0 ∧
      (source_position (worldAfter w (worldReadAll w ref) heap ref)).val =
        (source_position io).val + (source_bytesavailable io).val ∧
      (∀ n : Int, 0 ≤ n → ∃ vector, worldResult (worldRead w ref n) heap = .ok vector ∧
        w.vectorBytes (worldState (worldRead w ref n) heap) vector = (available io).take n.toNat) ∧
      (∀ byte, available io = byte :: (available io).drop 1 →
        resultOf source_peek_uint8 io = .ok byte ∧ stateOf source_peek_uint8 io = io)

/-- Writes on non-writable buffers and reads on non-readable buffers raise their documented ArgumentErrors. -/
def ReadWritePermissionErrors : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    let io := worldSnapshot w heap ref
    (io.writable = false →
      (∀ pointer count cancel, worldResult (worldWrite w ref pointer count cancel) heap =
        .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")) ∧
        worldAfter w (worldWrite w ref pointer count cancel) heap ref = io) ∧
      (∀ byte, worldResult (worldWriteByte w ref byte) heap =
        .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")) ∧
        worldAfter w (worldWriteByte w ref byte) heap ref = io)) ∧
    (io.readable = false →
      worldResult (worldReadByte w ref) heap =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      worldAfter w (worldReadByte w ref) heap ref = io ∧
      resultOf source_peek_uint8 io = .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      stateOf source_peek_uint8 io = io ∧
      (∀ n : Int, 0 ≤ n → worldResult (worldRead w ref n) heap =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
        worldAfter w (worldRead w ref n) heap ref = io) ∧
      worldResult (worldReadAll w ref) heap =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      worldAfter w (worldReadAll w ref) heap ref = io ∧
      (∀ dest, worldResult (worldReadDefault w ref dest none) heap =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
        worldAfter w (worldReadDefault w ref dest none) heap ref = io))

/-- A successful source write never advances beyond the configured `maxsize` boundary. -/
def MaxsizeCapsWrites : Prop :=
  ∀ w : BufferWorld, ∀ heap ref, worldValid w heap ref →
    (worldSnapshot w heap ref).writable = true → ∀ pointer count cancel,
    w.validPointer heap pointer count →
      let roomAction := source_ensureroom (worldAccess w) w.storage ref count
      let room := worldAfter w roomAction heap ref
      let start := if room.append then room.size else room.ptr - i 1
      ∃ written, worldResult roomAction heap = .ok ref ∧ stateInvariant room ∧
        worldResult (worldWrite w ref pointer count cancel) heap = .ok written ∧
        written.val ≤ count.val ∧
        written.val ≤ max 0 (room.maxsize.val - (start - getOffset room).val)

/-- Position, invalid seek/truncate errors, and typed mark/reset follow the IO contracts. -/
def PositionBoundsAfterOperations : Prop :=
  SeekSpec ∧ SkipSpec ∧ TruncateSpec ∧
  ∀ w : BufferWorld, ∀ (markMethod resetMethod : w.Ref → WorldM w I),
    (∀ heap ref, worldValid w heap ref →
      worldResult (markMethod ref) heap = .ok (source_position (worldSnapshot w heap ref)) ∧
      (worldAfter w (markMethod ref) heap ref).mark = source_position (worldSnapshot w heap ref)) →
    (∀ heap ref, worldValid w heap ref → ismarked (worldSnapshot w heap ref) = true →
      worldResult (resetMethod ref) heap = .ok (worldSnapshot w heap ref).mark ∧
      source_position (worldAfter w (resetMethod ref) heap ref) = (worldSnapshot w heap ref).mark) →
    (∀ heap ref, worldValid w heap ref → ismarked (worldSnapshot w heap ref) = false →
      worldResult (resetMethod ref) heap = .error (.jl (.argumentError "IOBuffer not marked"))) →
    ∀ heap ref, worldValid w heap ref → ∀ n : Int,
      let io := worldSnapshot w heap ref
      (ismarked io = false → worldResult (resetMethod ref) heap =
        .error (.jl (.argumentError "IOBuffer not marked"))) ∧
      (worldResult (source_seek (worldAccess w) ref (clampToI n)) heap = .ok ref →
        positionWithin (worldAfter w (source_seek (worldAccess w) ref (clampToI n)) heap ref)) ∧
      (worldResult (source_skip (worldAccess w) (source_seek (worldAccess w)) ref (clampToI n)) heap = .ok ref →
        positionWithin (worldAfter w
          (source_skip (worldAccess w) (source_seek (worldAccess w)) ref (clampToI n)) heap ref)) ∧
      (worldResult (markMethod ref) heap = .ok (source_position io) →
        positionWithin (worldAfter w (markMethod ref) heap ref)) ∧
      (worldResult (worldTruncate w ref n) heap = .ok ref →
        positionWithin (worldAfter w (worldTruncate w ref n) heap ref)) ∧
      (worldResult (resetMethod ref) heap = .ok io.mark →
        positionWithin (worldAfter w (resetMethod ref) heap ref))

theorem newGenericFields_proven : NewGenericFields := by
  intro T data dataBytes isMemory readable writable seekable append maxsize hlen
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem resultAndStateDetermineRun {α : Type} (m : M α) (io : BufferState) (value : α)
    (next : BufferState) (hresult : resultOf m io = .ok value)
    (hstate : stateOf m io = next) : m.run io = .ok value next := by
  cases hrun : m.run io with
  | ok actual state =>
      have hactual : actual = value := by simpa [resultOf, hrun] using hresult
      have hnext : state = next := by simpa [stateOf, hrun] using hstate
      simp [hrun, hactual, hnext]
  | error error state =>
      simp [resultOf, hrun] at hresult

theorem sourcePositionAfterPtrAdd (io : BufferState) (n : I) :
    source_position { io with ptr := io.ptr + n } = source_position io + n := by
  apply Subtype.ext
  change
    wrapInt .i64 (wrapInt .i64 (wrapInt .i64 (io.ptr.val + n.val) - io.offset.val) - 1) =
      wrapInt .i64 (wrapInt .i64 (wrapInt .i64 (io.ptr.val - io.offset.val) - 1) + n.val)
  simp only [JuliaLean.Proofs.base.int.wrapInt_sub_left,
    JuliaLean.Proofs.base.int.wrapInt_add_left]
  congr 1
  omega


theorem toIOfRange (x : Int) (h0 : -2 ^ 63 ≤ x) (h1 : x < 2 ^ 63) : ∃ v, toI x = .ok v := by
  have hr : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    simp
    omega
  exact ⟨⟨x, hr⟩, by simp [toI, JInt.convert, hr]⟩

theorem toUOfRange (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : ∃ v, toU x = .ok v := by
  have hr : IntTy.u64.min ≤ x ∧ x ≤ IntTy.u64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    simp
    omega
  exact ⟨⟨x, hr⟩, by simp [toU, JInt.convert, hr]⟩

theorem resultStateOfRunError {α : Type} (m : M α) (io : BufferState) (e : IOErr)
    (h : m.run io = .error e io) : resultOf m io = .error e ∧ stateOf m io = io := by
  simp [resultOf, stateOf, h]

theorem stringVectorOfRange (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 63) :
    stringVectorBytes n = .ok (List.replicate n.toNat 0) := by
  have hr : IntTy.u64.min ≤ n ∧ n ≤ IntTy.u64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
  have hv : toU n = .ok ⟨n, hr⟩ := by simp [toU, JInt.convert, hr]
  have hneg : ¬(n < 0) := by omega
  have hhi : ¬(n > 2 ^ 64 - 1) := by omega
  simp [stringVectorBytes, source_StringVector, source_StringMemory, stringN,
    unsafeWrapMemory, unsafeWrapModel, wrapArrayModel, JuliaLean.base.array.wrapMemory,
    hv, stringNModel, hneg, hhi, Bind.bind, Except.bind]

/-! ## Registry entries -/

/-! Nothing to promise:
`GenericIOBuffer@134` forwards the same arguments to `GenericIOBuffer{T}@110`.
`readavailable@980` forwards to `read@977`; its documented byte behavior is stated by
`ReadAvailableAndPeekCounts`.
`copyline@1079` and `copyline@1080` forward unchanged to `_copyline@1057`; their
documented byte behavior is stated by `CopylineMethods`.
-/

def counterexampleByte (byte : UInt8) : Byte :=
  JuliaLean.base.int.lit .u8 byte.toNat

def counterexampleUInt8 (byte : Byte) : UInt8 :=
  UInt8.ofNat byte.val.toNat


def counterexampleWorld : BufferWorld where
  Heap := (BufferState × BufferState) × List UInt8
  Ref := Bool
  Data := List UInt8
  NewData := List UInt8
  Vector := List UInt8
  View := List UInt8
  StringRef := List UInt8
  Stream := List UInt8
  VectorRef := List UInt8
  Cancel := Unit
  fields := fun heap ref => bufferFields (if ref then heap.1.2 else heap.1.1)
  setFields := fun heap ref fields =>
    if ref then
      ((heap.1.1, updateBufferFields heap.1.2 fields), heap.2)
    else
      ((updateBufferFields heap.1.1 fields, heap.1.2), heap.2)
  newFields := fun fields => fun heap =>
    .ok true ((heap.1.1, updateBufferFields heap.1.2 fields), heap.2)
  memoryType := fun heap ref => (if ref then heap.1.2 else heap.1.1).isMemory
  bytes := fun _ data => data
  vectorStringOps := {
    length := fun vector => pure (i vector.length)
    reference := fun vector => pure vector
    ptrOrOffset := fun _ => pure (u 0)
    memory := fun reference => pure reference
    memoryPointer := fun _ => pure (u 0)
    memoryToString := fun memory count => pure (memory.take count.val.toNat)
    pointerToString := fun reference count => pure (reference.take count.val.toNat)
    emptyString := pure []
    emptyMemory := pure []
    memoryref := fun memory => pure memory
    setSize := fun _ _ => pure ()
    setReference := fun _ _ => pure ()
  }
  emptyMemory := pure []
  memoryref := fun memory first => pure (memory.drop (first.val.toNat - 1))
  wrapCheck := fun memory dimensions => pure (memory.take (dimensions.getD 0 (i 0)).val.toNat)
  newArray := fun memory _ => pure memory
  allocateString := fun count => pure (List.replicate count.val.toNat 0)
  stringToMemory := fun memory => pure memory
  memoryLength := fun memory => i memory.length
  memoryrefBase := fun memory => pure memory
  vectorType := fun _ _ => true
  dataReference := fun data => pure data
  referenceMemory := fun reference => pure reference
  memoryOffset := fun _ => pure (i 0)
  dataLength := fun data => pure (i data.length)
  firstIndex := fun _ => pure (i 1)
  sizehint := fun _ _ => pure ()
  vectorBytes := fun _ vector => vector
  vectorFromBytes := fun bytes => pure bytes
  stringBytes := fun _ string => string
  outputBytes := fun heap ref => if ref then heap.1.2.data else []
  streamBytes := fun _ stream => stream
  storage := {
    Length := I
    LastIndex := I
    IndexDifference := I
    SpaceOther := Unit
    ShiftedLength := Unit
    AddedLength := Unit
    DesiredOther := Unit
    Bound := I
    length := fun data => pure (i data.length)
    lastIndex := fun data => pure (i data.length)
    subtractIndex := fun last start => pure (last - start)
    minimumSpace := fun difference capacity => pure (.inl (imin difference capacity))
    spaceLess := fun existing requested => pure (match existing with
      | .inl available => decide (available.val < requested.val)
      | .inr _ => false)
    shiftLength := fun _ => pure ()
    reclaimEnough := fun _ _ => pure false
    addLength := fun _ _ => pure ()
    subtractAvailable := fun _ _ => pure (.inl (i 0))
    desiredGreater := fun desired limit => pure (match desired with
      | .inl value => decide (limit.val < value.val)
      | .inr _ => false)
    lengthLess := fun length limit => pure (decide (length.val < limit.val))
    lengthToInt := fun length => pure length
    minimumLength := fun length limit => pure (imin length limit)
    boundToInt := fun bound => pure bound
    applicableResize := fun _ _ => pure false
    resize := fun _ _ => pure ()
    similar := fun _ count => pure (List.replicate count.val.toNat 0)
    convertData := fun data => pure data
    copyIntoNew := fun _ _ _ _ _ => pure ()
    copyWithin := fun _ _ _ _ _ => pure ()
    spanLength := fun first last => pure (rangeLength first last)
    fillNew := fun _ _ => pure ()
    fillView := fun _ _ _ _ => pure ()
  }
  copyVector := fun _ _ memory first count =>
    pure (slice memory first.val (first + count - i 1).val)
  readInto := fun _ vector => pure vector
  vectorLength := fun vector => pure (i vector.length)
  vectorResize := fun _ _ => pure ()
  vectorBounds := fun _ _ => pure ()
  vectorPointer := fun _ => pure ⟨JuliaLean.base.pointer.u64 0⟩
  pointerBytes := fun heap pointer count =>
    (heap.2.drop pointer.address.val.toNat).take count
  validPointer := fun heap pointer count =>
    pointer.address.val.toNat + count.val.toNat ≤ heap.2.length
  getIndex := fun data index =>
    pure (counterexampleByte (data.getD (index.val.toNat - 1) 0))
  getIndexU := fun data index =>
    pure (counterexampleByte (data.getD (index.val.toNat - 1) 0))
  setIndex := fun _ _ _ => pure ()
  setIndexU := fun _ _ _ => pure ()
  dense := fun _ _ => false
  pointer := fun _ _ => pure ⟨JuliaLean.base.pointer.u64 0⟩
  load := fun pointer index => do
    let heap ← get
    pure (counterexampleByte
      ((heap.2.drop pointer.address.val.toNat).getD (index.val.toNat - 1) 0))
  store := fun _ _ _ => pure ()
  copyPointer := fun destination _ _ => pure destination
  precheck := fun _ => pure ()
  defaultCancel := ()
  isDefault := fun _ => pure true
  isDefaultPure := fun _ => true
  checkCancel := fun cancel => pure cancel
  view := fun data first last => pure (slice data first.val last.val)
  viewBytes := fun _ view => view
  findFirst := fun byte view => pure
    (if byte = JuliaLean.base.int.lit .u8 10 ∧
        view = [0x61, 0x62, 0x0a, 0x63, 0x64] then
      some (i 3)
    else (view.idxOf? (counterexampleUInt8 byte)).map fun index => i (Int.ofNat (index + 1)))
  viewLength := fun view => pure (i view.length)
  viewIndex := fun view index =>
    pure (counterexampleByte (view.getD (index.val.toNat - 1) 0))
  writeView := fun _ _ => pure ()
  writeViewToken := fun _ _ _ => pure ()
  identical := fun left right => pure (left == right)
  copyStream := fun _ _ _ _ => pure ()
  copyStreamToken := fun _ _ _ _ _ => pure ()
  vectorLast := fun vector =>
    pure (counterexampleByte (vector.getD (vector.length - 1) 0))
  vectorPop := fun _ => pure ()
  writeVector := fun _ _ _ => pure ()
  spanLength := fun first last => pure (rangeLength first last)
  spanEmpty := fun first last => pure (decide (last.val < first.val))
  emptyString := pure []
  memoryToString := fun memory count => pure (memory.take count.val.toNat)
  copyMemory := fun _ _ _ _ _ => pure ()
  takeMemory := fun memory => pure memory
  member := fun byte view => pure (view.contains (counterexampleUInt8 byte))
  lock := fun _ => pure ()
  unlock := fun _ => pure ()
  print := fun _ _ => pure ()
  printed := fun _ _ => []

instance : DecidableEq counterexampleWorld.Vector := by
  change DecidableEq (List UInt8)
  infer_instance

instance : DecidableEq counterexampleWorld.StringRef := by
  change DecidableEq (List UInt8)
  infer_instance

instance : DecidableEq counterexampleWorld.Ref := by
  change DecidableEq Bool
  infer_instance

set_option maxRecDepth 10000 in
theorem takeReadOnly_refuted : ¬ TakeReadOnly := by
  intro h
  let io : BufferState :=
    { data := [0x41, 0x42, 0x43], isMemory := true, reinit := false, readable := true,
      writable := false, seekable := false, append := true, size := i 3,
      maxsize := i 10, ptr := i 1, offset := i 0, mark := i (-1) }
  let heap : ((BufferState × BufferState) × List UInt8) := ((io, defaultBufferState), [])
  have hinv : worldValid counterexampleWorld heap false := by
    change stateInvariant io
    unfold stateInvariant
    decide
  have htake := h counterexampleWorld heap false hinv rfl rfl rfl
  rcases htake with ⟨vector, htake, _⟩
  have hfail : worldResult (worldTake counterexampleWorld false) heap =
      .error (.errorException "Unreachable IOBuffer state") := by
    decide
  rw [hfail] at htake
  cases htake

set_option maxRecDepth 10000 in
theorem takeResets_refuted : ¬ TakeResets := by
  intro h
  let io : BufferState :=
    { data := [0x41, 0x42, 0x43], isMemory := true, reinit := false, readable := true,
      writable := false, seekable := true, append := false, size := i 3,
      maxsize := i 3, ptr := i 2, offset := i 0, mark := i (-1) }
  let heap : ((BufferState × BufferState) × List UInt8) := ((io, defaultBufferState), [])
  have hinv : worldValid counterexampleWorld heap false := by
    change stateInvariant io
    unfold stateInvariant
    decide
  have htake :
      ∃ vector, worldResult (worldTake counterexampleWorld false) heap = .ok vector := by
    refine ⟨[0x41, 0x42, 0x43], ?_⟩
    decide
  have hreset := h counterexampleWorld heap false hinv rfl rfl htake
  have hposition :
      source_position (worldAfter counterexampleWorld (worldTake counterexampleWorld false)
        heap false) = i 1 := by
    decide
  rw [hposition] at hreset
  have hone : i 1 ≠ i 0 := by decide
  exact hone hreset

namespace JuliaLean.ChatGPT.Batch3.Group5
open JuliaLean JuliaLean.base.iobuffer JuliaLean.Proofs.base.iobuffer

/-- An unreadable byte reader stops before the supplied indexing operation. -/
theorem iobufferWorldReadByteNotReadable (w : BufferWorld) (heap : w.Heap) (ref : w.Ref)
    (hr : (w.fields heap ref).readable = false) :
    (worldReadByte w ref).run heap =
      .error (.jl (.argumentError "read failed, IOBuffer is not readable")) heap := by
  dsimp [worldReadByte, source_read_uint8, worldAccess, EStateM.run]
  simp only [hr, Bool.not_false, ite_true]
  rfl

/-- The byte peek rejects unreadable buffers without changing their state. -/
theorem iobufferPeekNotReadable (io : BufferState) (hr : io.readable = false) :
    source_peek_uint8.run io =
      .error (.jl (.argumentError "read failed, IOBuffer is not readable")) io := by
  dsimp [source_peek_uint8, EStateM.run]
  simp only [hr, Bool.not_false, ite_true]
  rfl

/-- iocov-iobuffer-not-readable: reads and peeks propagate the same documented error. -/
theorem IocovIobufferNotReadable_proven :
    JuliaLean.Proofs.base.iobuffer.ThrowNotReadable := by
  refine ⟨fun _ => rfl, ?_⟩
  intro w heap ref _ hr
  have hw := iobufferWorldReadByteNotReadable w heap ref hr
  have hp := iobufferPeekNotReadable (worldSnapshot w heap ref) hr
  constructor
  · simp only [worldResult, hw]
  · simp only [resultOf, hp]

/-- State reached by reading one byte from a two-byte PipeBuffer. -/
def iobufferSeekendPipe : BufferState :=
  { data := [0x41, 0x42], isMemory := true, reinit := false,
    readable := true, writable := true, seekable := false, append := true,
    size := i 2, maxsize := imaxval, ptr := i 2, offset := i 0, mark := i (-1) }

theorem iobufferSeekendPipeInvariant : stateInvariant iobufferSeekendPipe := by
  unfold stateInvariant
  decide

theorem iobufferSeekendPipePosition :
    (source_position (stateOf (source_seekend bufferAccess ()) iobufferSeekendPipe)).val = 2 := by
  decide

theorem iobufferSeekendPipeFilesize : (source_filesize iobufferSeekendPipe).val = 1 := by
  decide

/-- iocov-iobuffer-seek-methods: seekend uses the absolute end, while a pipe's filesize is unread bytes. -/
theorem IocovIobufferSeekMethods_refuted :
    ¬ JuliaLean.Proofs.base.iobuffer.SeekMethodsCorrect := by
  intro h
  have he := h.2.2.2 iobufferSeekendPipe iobufferSeekendPipeInvariant
  rw [iobufferSeekendPipePosition, iobufferSeekendPipeFilesize] at he
  omega


/-! Diagnostics for missing reachability clauses; these are not public Julia refutations. -/

/-- A field-invariant witness, excluded by the public seekable-buffer construction discipline. -/
def iobufferNegativeSeekableOffset : BufferState :=
  { data := [], isMemory := true, reinit := false, readable := true, writable := true,
    seekable := true, append := false, size := i 0, maxsize := imaxval,
    ptr := i 1, offset := i (-1), mark := i (-1) }

theorem iobufferNegativeSeekableOffsetInvariant :
    stateInvariant iobufferNegativeSeekableOffset := by
  unfold stateInvariant
  decide

/-- The frozen field invariant alone does not guarantee clamping to position zero. -/
theorem iobufferNegativeOffsetSeekPosition :
    (source_position (stateOf (source_seek bufferAccess () (clampToI 0))
      iobufferNegativeSeekableOffset)).val = 1 := by
  decide

theorem iobufferNegativeOffsetSeekExpected :
    max 0 (min (0 : Int) (source_filesize iobufferNegativeSeekableOffset).val) = 0 := by
  decide

/-- The same unreachable state obstructs the negative-skip clause. -/
theorem iobufferNegativeOffsetSkipPosition :
    (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) ()
      (clampToI (-1))) iobufferNegativeSeekableOffset)).val = 1 := by
  decide

theorem iobufferNegativeOffsetSkipExpected :
    max 0 ((source_position iobufferNegativeSeekableOffset).val + (-1)) = 0 := by
  decide

/-- This mark is already in the discarded prefix, which public pipe operations do not allow. -/
def iobufferStalePipeMark : BufferState :=
  { data := [], isMemory := true, reinit := false, readable := true, writable := true,
    seekable := false, append := true, size := i 0, maxsize := imaxval,
    ptr := i 1, offset := i (-1), mark := i 0 }

theorem iobufferStalePipeMarkInvariant : stateInvariant iobufferStalePipeMark := by
  unfold stateInvariant
  decide

theorem iobufferStalePipeMarkPosition :
    (source_position (stateOf (source_seek bufferAccess () (clampToI 0))
      iobufferStalePipeMark)).val = 1 ∧ iobufferStalePipeMark.mark.val = 0 := by
  decide


/-! General source-operation lemmas and corrected consequences of DocumentedInvariant7. -/

open JuliaLean.Proofs.base.int

theorem iobufferI64Bounds (x : I) : -2 ^ 63 ≤ x.val ∧ x.val ≤ 2 ^ 63 - 1 := by
  have h := x.property
  simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using h

theorem iobufferClampBits {t : IntTy} (n : JInt t) :
    clampBits n = .ok (clampToI n.val) := by
  unfold clampBits clampInteger JuliaLean.base.intfuncs.clamp_Type
  simp only [lt_eq, decide_eq_true_eq]
  have hlo : (JInt.typemin .i64).val = -2 ^ 63 := rfl
  have hhi : (JInt.typemax .i64).val = 2 ^ 63 - 1 := rfl
  rw [hlo, hhi]
  by_cases hh : 2 ^ 63 - 1 < n.val
  · simp only [hh, ite_true, clampToI]
    rfl
  · by_cases hl : n.val < -2 ^ 63
    · simp only [hh, hl, ite_false, ite_true, clampToI]
      rfl
    · have hb : IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max := by
        change -2 ^ 63 ≤ n.val ∧ n.val ≤ 2 ^ 63 - 1
        omega
      simp only [hh, hl, ite_false, clampToI, JuliaLean.base.int.convert,
        JInt.convert, dite_eq_left hb, Except.mapError]
      congr 1
      apply Subtype.ext
      exact (wrapInt_of_inRange .i64 n.val hb).symm

theorem iobufferWidenI128Value (n : I) :
    (JuliaLean.base.int.widenTo .i128 n).val = n.val := by
  rw [widenTo_val]
  apply wrapInt_of_inRange
  have hn := iobufferI64Bounds n
  change -(2 : Int) ^ 127 ≤ n.val ∧ n.val ≤ 2 ^ 127 - 1
  omega

theorem iobufferTranslateSeekPosition {D : Type} (io : Fields D) (n : I) :
    source_translate_seek_position io n = .ok (clampToI (n.val + io.offset.val + 1)) := by
  unfold source_translate_seek_position
  rw [iobufferClampBits]
  apply congrArg (fun z => Except.ok (clampToI z))
  simp only [JuliaLean.base.int.add, add_int_val, iobufferWidenI128Value]
  have hn := iobufferI64Bounds n
  have ho := iobufferI64Bounds io.offset
  change wrapInt .i128 (wrapInt .i128 (n.val + io.offset.val) + 1) =
    n.val + io.offset.val + 1
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem iobufferCoreAdd (x y : I) : JuliaLean.base.int.add x y = x + y := by
  apply Subtype.ext
  exact add_int_val x y

theorem iobufferCoreSub (x y : I) : JuliaLean.base.int.sub x y = x - y := by
  apply Subtype.ext
  exact sub_int_val x y

theorem iobufferCoreMax (x y : I) : JuliaLean.base.int.jmax x y = imax x y := by
  apply Subtype.ext
  rw [jmax_val]
  unfold imax
  split <;> omega

theorem iobufferCoreMin (x y : I) : JuliaLean.base.int.jmin x y = imin x y := by
  apply Subtype.ext
  rw [jmin_val]
  unfold imin
  split <;> omega

theorem iobufferConvertI64 (x : I) : JuliaLean.base.int.convert .i64 x = .ok x := by
  unfold JuliaLean.base.int.convert JInt.convert
  rw [dite_eq_left x.property]

theorem iobufferCoreClamp (x lo hi : I) :
    JuliaLean.base.intfuncs.clamp (fun x hi => JuliaLean.base.int.lt hi x)
      JuliaLean.base.int.lt (JuliaLean.base.int.convert .i64)
      (JuliaLean.base.int.convert .i64) (JuliaLean.base.int.convert .i64) x lo hi =
      .ok (clampI x lo hi) := by
  simp only [JuliaLean.base.intfuncs.clamp, lt_eq, iobufferConvertI64,
    decide_eq_true_eq, clampI]
  split
  · rfl
  · split <;> rfl

theorem iobufferValueEq (x y : I) : (x.val = y.val) ↔ x = y :=
  ⟨Subtype.ext, congrArg Subtype.val⟩

theorem iobufferSourceSeekEq (n : I) : source_seek bufferAccess () n = seek n := by
  funext io
  dsimp [source_seek, seek, bufferAccess]
  simp only [bufferFields, fieldsIsmarked, fieldsOffset, iobufferCoreMax,
    iobufferCoreAdd, eq_int_eq, iobufferTranslateSeekPosition,
    iobufferCoreClamp, ismarked, not_decide_eq_true, iobufferValueEq]
  dsimp [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.instMonadStateOf, EStateM.get,
    pure, EStateM.pure]
  cases hs : io.seekable <;> by_cases hm : 0 ≤ io.mark.val <;>
    by_cases hn : n = io.mark <;>
    (try simp only [hm, hn, Bool.not_false, Bool.not_true, ite_true, ite_false,
      not_true_eq_false, not_false_eq_true]) <;> rfl

theorem iobufferIntClamp (n : Int) :
    clampInteger intClampgt intClamplt intClampConvert n = .ok (clampToI n) := by
  unfold clampInteger JuliaLean.base.intfuncs.clamp_Type intClampgt intClamplt
  simp only [decide_eq_true_eq]
  have hlo : (JInt.typemin .i64).val = -2 ^ 63 := rfl
  have hhi : (JInt.typemax .i64).val = 2 ^ 63 - 1 := rfl
  rw [hlo, hhi]
  by_cases hh : 2 ^ 63 - 1 < n
  · simp only [hh, ite_true, clampToI]
    rfl
  · by_cases hl : n < -2 ^ 63
    · simp only [hh, hl, ite_false, ite_true, clampToI]
      rfl
    · have hb : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
        change -2 ^ 63 ≤ n ∧ n ≤ 2 ^ 63 - 1
        omega
      simp only [hh, hl, ite_false, clampToI, intClampConvert,
        JInt.convert, dite_eq_left hb, Except.mapError]
      congr 1
      apply Subtype.ext
      exact (wrapInt_of_inRange .i64 n hb).symm

theorem iobufferSourceSeekIntegerEq (n : Int) :
    source_seek_integer (source_seek bufferAccess) intClampgt intClamplt
      intClampConvert () n = source_seek bufferAccess () (clampToI n) := by
  unfold source_seek_integer
  rw [iobufferIntClamp]
  rfl

theorem iobufferIValue (x : Int) (hlo : -2 ^ 63 ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (i x).val = x := by
  change wrapInt .i64 x = x
  apply wrapInt_of_inRange
  change -2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1
  exact ⟨hlo, hhi⟩

theorem iobufferClampToIValue (x : Int) :
    (clampToI x).val = max (-2 ^ 63) (min x (2 ^ 63 - 1)) := by
  unfold clampToI imaxval
  split
  · rw [iobufferIValue _ (by decide) (by decide)]
    omega
  · split
    · rw [iobufferIValue _ (by decide) (by decide)]
      omega
    · rw [iobufferIValue _ (by omega) (by omega)]
      omega

theorem iobufferClampIValue (x lo hi : I) (h : lo.val ≤ hi.val) :
    (clampI x lo hi).val = max lo.val (min x.val hi.val) := by
  unfold clampI
  split
  · omega
  · split <;> omega

theorem iobufferAddOneValue (x : I) (hx : x.val < 2 ^ 63 - 1) :
    (x + i 1).val = x.val + 1 := by
  change wrapInt .i64 (x.val + 1) = x.val + 1
  apply wrapInt_of_inRange
  have hb := iobufferI64Bounds x
  change -2 ^ 63 ≤ x.val + 1 ∧ x.val + 1 ≤ 2 ^ 63 - 1
  omega

theorem iobufferPositionAt (io : BufferState) (ptr : I)
    (hlo : -2 ^ 63 ≤ ptr.val - io.offset.val - 1)
    (hhi : ptr.val - io.offset.val - 1 ≤ 2 ^ 63 - 1) :
    (source_position { io with ptr }).val = ptr.val - io.offset.val - 1 := by
  change wrapInt .i64 (wrapInt .i64 (ptr.val - io.offset.val) - 1) = _
  rw [wrapInt_sub_left]
  apply wrapInt_of_inRange
  change -2 ^ 63 ≤ ptr.val - io.offset.val - 1 ∧
    ptr.val - io.offset.val - 1 ≤ 2 ^ 63 - 1
  exact ⟨hlo, hhi⟩

theorem iobufferSeekRunSuccess (io : BufferState) (n : I)
    (hc : io.seekable = true ∨ (ismarked io = true ∧ n = io.mark)) :
    (source_seek bufferAccess () n).run io = .ok ()
      { io with ptr := clampI (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1) } := by
  rw [iobufferSourceSeekEq]
  dsimp [seek, EStateM.run]
  rcases hc with hs | ⟨hm, hn⟩
  · simp only [hs, Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  · cases hs : io.seekable <;>
      simp only [hm, hn, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ite_false, ite_true, not_true_eq_false] <;> rfl

theorem iobufferMaxValue (a b : I) : (imax a b).val = max a.val b.val := by
  unfold imax
  split <;> omega

theorem iobufferMinValue (a b : I) : (imin a b).val = min a.val b.val := by
  unfold imin
  split <;> omega

theorem iobufferOffsetValue (io : BufferState) :
    (getOffset io).val = max 0 io.offset.val := by
  rw [getOffset, iobufferMaxValue]
  rfl

theorem iobufferSeekPointerValue (io : BufferState) (n : I)
    (hos : (getOffset io).val ≤ io.size.val) (hsize : io.size.val < 2 ^ 63 - 1) :
    (clampI (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1)).val =
      max ((getOffset io).val + 1)
        (min (max (-2 ^ 63) (min (n.val + io.offset.val + 1) (2 ^ 63 - 1)))
          (io.size.val + 1)) := by
  have hlo := iobufferAddOneValue (getOffset io) (by omega)
  have hhi := iobufferAddOneValue io.size hsize
  rw [iobufferClampIValue _ _ _ (by rw [hlo, hhi]; omega), hlo, hhi,
    translateSeekPosition, iobufferClampToIValue]

/-- The seekable part of the frozen seek claim follows from the documented offset clause. -/
theorem iobufferSeekableDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1) (hs : io.seekable = true) (n : Int) :
    resultOf (source_seek_integer (source_seek bufferAccess) intClampgt intClamplt
      intClampConvert () n) io = .ok () ∧
    (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val =
      max 0 (min n (source_filesize io).val) := by
  rcases hd with ⟨_, hs0, _, _, ho0, hos, _, _, _, hseek, _, _, _, _⟩
  have hoff := hseek hs
  have hoffval : (getOffset io).val = io.offset.val := by
    rw [iobufferOffsetValue]
    omega
  have hfs : (source_filesize io).val = io.size.val - io.offset.val := by
    simp only [source_filesize, hs, ite_true]
    change wrapInt .i64 (io.size.val - (getOffset io).val) = _
    rw [hoffval]
    apply wrapInt_of_inRange
    change -2 ^ 63 ≤ io.size.val - io.offset.val ∧
      io.size.val - io.offset.val ≤ 2 ^ 63 - 1
    omega
  let ptr := clampI (translateSeekPosition io (clampToI n))
    (getOffset io + i 1) (io.size + i 1)
  have hp : ptr.val = max (io.offset.val + 1)
      (min (max (-2 ^ 63) (min ((clampToI n).val + io.offset.val + 1) (2 ^ 63 - 1)))
        (io.size.val + 1)) := by
    rw [iobufferSeekPointerValue io (clampToI n) hos hsize, hoffval]
  have hrun := iobufferSeekRunSuccess io (clampToI n) (Or.inl hs)
  have hn := iobufferClampToIValue n
  constructor
  · rw [iobufferSourceSeekIntegerEq]
    simp only [resultOf, hrun]
  · have hst : stateOf (source_seek bufferAccess () (clampToI n)) io = { io with ptr } := by
      simp only [stateOf, hrun]
      rfl
    rw [hst, iobufferPositionAt io ptr (by omega) (by omega), hfs]
    omega

/-- The documented live-mark interval makes an allowed pipe seek restore the exact mark. -/
theorem iobufferMarkedSeekDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1) (hm : ismarked io = true) :
    resultOf (source_seek bufferAccess () io.mark) io = .ok () ∧
    (source_position (stateOf (source_seek bufferAccess () io.mark) io)).val = io.mark.val := by
  rcases hd with ⟨_, _, _, _, ho0, hos, _, _, _, _, _, hlive, _, _⟩
  have hm0 : 0 ≤ io.mark.val := by simpa only [ismarked, decide_eq_true_eq] using hm
  have hmark := hlive hm0
  have hmb := iobufferI64Bounds io.mark
  let ptr := clampI (translateSeekPosition io io.mark)
    (getOffset io + i 1) (io.size + i 1)
  have hp : ptr.val = io.mark.val + io.offset.val + 1 := by
    have hx := iobufferSeekPointerValue io io.mark hos hsize
    change ptr.val = _ at hx
    omega
  have hrun := iobufferSeekRunSuccess io io.mark (Or.inr ⟨hm, rfl⟩)
  constructor
  · simp only [resultOf, hrun]
  · have hst : stateOf (source_seek bufferAccess () io.mark) io = { io with ptr } := by
      simp only [stateOf, hrun]
      rfl
    rw [hst, iobufferPositionAt io ptr (by omega) (by omega), hp]
    omega

theorem iobufferClampValueIdentity (n : I) : clampToI n.val = n := by
  apply Subtype.ext
  rw [iobufferClampToIValue]
  have hn := iobufferI64Bounds n
  omega

theorem iobufferWidenAdd (x y : I) :
    (JuliaLean.base.int.add (JuliaLean.base.int.widenTo .i128 x)
      (JuliaLean.base.int.widenTo .i128 y)).val = x.val + y.val := by
  rw [JuliaLean.base.int.add, add_int_val, iobufferWidenI128Value, iobufferWidenI128Value]
  apply wrapInt_of_inRange
  have hx := iobufferI64Bounds x
  have hy := iobufferI64Bounds y
  change -(2 : Int) ^ 127 ≤ x.val + y.val ∧ x.val + y.val ≤ 2 ^ 127 - 1
  omega

theorem iobufferSignbitI64 (n : I) : JuliaLean.base.int.signbit n = decide (n.val < 0) := by
  change JuliaLean.base.int.signbit_Integer n = decide (n.val < 0)
  unfold JuliaLean.base.int.signbit_Integer JuliaLean.base.int.Generic.signbit_Integer
  change JuliaLean.base.int.lt n (JuliaLean.base.int.lit .i64 0) = decide (n.val < 0)
  rw [lt_eq]
  rfl

/-- Source skip has the same complete state/error behavior as the concrete skip model. -/
theorem iobufferSourceSkipEq (n : I) :
    source_skip bufferAccess (source_seek bufferAccess) () n = skip n.val := by
  funext io
  unfold source_skip skip
  rw [iobufferClampValueIdentity]
  simp only [iobufferSignbitI64, decide_eq_true_eq, iobufferClampBits,
    iobufferWidenAdd, iobufferSourceSeekEq]
  dsimp [bufferAccess, fieldsPosition]
  simp only [iobufferCoreAdd, iobufferCoreSub, iobufferCoreMin, bufferFields]
  dsimp [bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.instMonadStateOf, EStateM.get, pure, EStateM.pure]
  by_cases hn : n.val < 0 <;> simp only [hn, ite_true, ite_false] <;> rfl

/-- Arbitrary integer skip arguments are clamped before the Int method is called. -/
theorem iobufferSourceSkipIntegerEq (n : Int) :
    source_skip_integer (source_skip bufferAccess (source_seek bufferAccess))
      intClampgt intClamplt intClampConvert () n =
    source_skip bufferAccess (source_seek bufferAccess) () (clampToI n) := by
  unfold source_skip_integer
  rw [iobufferIntClamp]
  rfl

theorem iobufferSkipRunNonneg (io : BufferState) (n : I) (hn : 0 ≤ n.val) :
    (source_skip bufferAccess (source_seek bufferAccess) () n).run io =
      .ok () { io with ptr := io.ptr + imin n (io.size + i 1 - io.ptr) } := by
  rw [iobufferSourceSkipEq]
  unfold skip
  rw [iobufferClampValueIdentity]
  dsimp [EStateM.run]
  simp only [ite_eq_right (Int.not_lt.mpr hn)]
  rfl

theorem iobufferSkipRunNegative (io : BufferState) (n : I) (hn : n.val < 0) :
    (source_skip bufferAccess (source_seek bufferAccess) () n).run io =
      (source_seek bufferAccess () (clampToI ((source_position io).val + n.val))).run io := by
  rw [iobufferSourceSkipEq, iobufferSourceSeekEq]
  unfold skip
  rw [iobufferClampValueIdentity]
  dsimp [EStateM.run]
  simp only [ite_eq_left hn]
  rfl

/-- The documented pointer interval gives the exact mathematical position when its logical end fits. -/
theorem iobufferDocumentedPosition (io : BufferState) (hd : DocumentedInvariant7 io)
    (hlogical : io.size.val - io.offset.val ≤ 2 ^ 63 - 1) :
    (source_position io).val = io.ptr.val - io.offset.val - 1 ∧
      0 ≤ (source_position io).val ∧
      (source_position io).val ≤ io.size.val - io.offset.val := by
  rcases hd with ⟨_, _, _, _, ho0, hos, hplo, hphi, _, _, _, _, _, _⟩
  have hoff := iobufferOffsetValue io
  have hp := iobufferPositionAt io io.ptr (by omega) (by omega)
  change (source_position io).val = io.ptr.val - io.offset.val - 1 at hp
  exact ⟨hp, by omega, by omega⟩

/-- Remaining bytes are the unwrapped distance from the pointer through the stored end. -/
theorem iobufferDocumentedAvailable (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1) :
    (source_bytesavailable io).val = io.size.val - io.ptr.val + 1 := by
  rcases hd with ⟨_, _, _, _, ho0, _, hplo, hphi, _, _, _, _, _, _⟩
  change wrapInt .i64 (wrapInt .i64 (io.size.val - io.ptr.val) + 1) = _
  rw [wrapInt_add_left]
  apply wrapInt_of_inRange
  change -2 ^ 63 ≤ io.size.val - io.ptr.val + 1 ∧
    io.size.val - io.ptr.val + 1 ≤ 2 ^ 63 - 1
  omega

/-- Nonnegative source skip obeys the frozen position formula under the documented pointer bounds. -/
theorem iobufferSkipNonnegDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1)
    (hlogical : io.size.val - io.offset.val ≤ 2 ^ 63 - 1) (n : Int) (hn : 0 ≤ n) :
    resultOf (source_skip_integer (source_skip bufferAccess (source_seek bufferAccess))
      intClampgt intClamplt intClampConvert () n) io = .ok () ∧
    (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) ()
      (clampToI n)) io)).val =
      (source_position io).val + min n (source_bytesavailable io).val := by
  have hp := iobufferDocumentedPosition io hd hlogical
  have ha := iobufferDocumentedAvailable io hd hsize
  rcases hd with ⟨_, _, _, _, ho0, hos, hplo, hphi, _, _, _, _, _, _⟩
  have hoff := iobufferOffsetValue io
  have hnval := iobufferClampToIValue n
  have hnn : 0 ≤ (clampToI n).val := by omega
  have hnmax : (io.size + i 1 - io.ptr).val = io.size.val + 1 - io.ptr.val := by
    change wrapInt .i64 ((io.size + i 1).val - io.ptr.val) = _
    rw [iobufferAddOneValue io.size hsize]
    apply wrapInt_of_inRange
    change -2 ^ 63 ≤ io.size.val + 1 - io.ptr.val ∧
      io.size.val + 1 - io.ptr.val ≤ 2 ^ 63 - 1
    omega
  have hmin : (imin (clampToI n) (io.size + i 1 - io.ptr)).val =
      min n (source_bytesavailable io).val := by
    rw [iobufferMinValue, hnmax, ha]
    omega
  let ptr := io.ptr + imin (clampToI n) (io.size + i 1 - io.ptr)
  have hptr : ptr.val = io.ptr.val + min n (source_bytesavailable io).val := by
    change wrapInt .i64 (io.ptr.val + (imin (clampToI n) (io.size + i 1 - io.ptr)).val) = _
    rw [hmin]
    apply wrapInt_of_inRange
    change -2 ^ 63 ≤ io.ptr.val + min n (source_bytesavailable io).val ∧
      io.ptr.val + min n (source_bytesavailable io).val ≤ 2 ^ 63 - 1
    omega
  have hrun := iobufferSkipRunNonneg io (clampToI n) hnn
  constructor
  · rw [iobufferSourceSkipIntegerEq]
    simp only [resultOf, hrun]
  · have hst : stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
        { io with ptr } := by
      simp only [stateOf, hrun]
      rfl
    rw [hst, iobufferPositionAt io ptr (by omega) (by omega), hptr]
    omega

/-- A negative seekable skip has the documented backward-clamping behavior. -/
theorem iobufferSkipNegativeDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1) (hs : io.seekable = true)
    (n : Int) (hn : n < 0) :
    resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io = .ok () ∧
    (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) ()
      (clampToI n)) io)).val = max 0 ((source_position io).val + n) := by
  have hd' := hd
  rcases hd' with ⟨_, hs0, _, _, _, hos, _, _, _, hseek, _, _, _, _⟩
  have hoff := hseek hs
  have hoffval : (getOffset io).val = io.offset.val := by
    rw [iobufferOffsetValue]
    omega
  have hp := iobufferDocumentedPosition io hd (by omega)
  have hfs : (source_filesize io).val = io.size.val - io.offset.val := by
    simp only [source_filesize, hs, ite_true]
    change wrapInt .i64 (io.size.val - (getOffset io).val) = _
    rw [hoffval]
    apply wrapInt_of_inRange
    change -2 ^ 63 ≤ io.size.val - io.offset.val ∧
      io.size.val - io.offset.val ≤ 2 ^ 63 - 1
    omega
  have hnval := iobufferClampToIValue n
  have hneg : (clampToI n).val < 0 := by omega
  have hrun := iobufferSkipRunNegative io (clampToI n) hneg
  have hseeked := iobufferSeekableDocumented io hd hsize hs
    ((source_position io).val + (clampToI n).val)
  rw [iobufferSourceSeekIntegerEq] at hseeked
  constructor
  · simpa only [resultOf, hrun] using hseeked.1
  · have hsame : stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
        stateOf (source_seek bufferAccess ()
          (clampToI ((source_position io).val + (clampToI n).val))) io := by
      simp only [stateOf, hrun]
    rw [hsame, hseeked.2, hfs]
    omega

/-- The pipe seek error cases hold for every state, without extra invariant hypotheses. -/
theorem iobufferSeekPipeResult (io : BufferState) (hs : io.seekable = false) (n : I) :
    resultOf (source_seek bufferAccess () n) io =
      if ismarked io then
        if n = io.mark then .ok ()
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
      else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked")) := by
  rw [iobufferSourceSeekEq]
  dsimp [resultOf, seek, EStateM.run, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.instMonadStateOf, EStateM.get]
  cases hm : ismarked io <;> by_cases he : n = io.mark <;>
    simp only [hs, he, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_true, ite_false, not_true_eq_false, not_false_eq_true] <;> rfl

/-- The negative pipe-skip error clause is independent of the physical-position invariants. -/
theorem iobufferSkipNegativePipeResult (io : BufferState) (hs : io.seekable = false)
    (n : Int) (hn : n < 0) :
    let target := clampToI ((source_position io).val + (clampToI n).val)
    resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
      if ismarked io then
        if target = io.mark then .ok ()
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
      else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked")) := by
  have hc := iobufferClampToIValue n
  have hneg : (clampToI n).val < 0 := by omega
  have hrun := iobufferSkipRunNegative io (clampToI n) hneg
  simpa only [resultOf, hrun] using
    iobufferSeekPipeResult io hs (clampToI ((source_position io).val + (clampToI n).val))

/-- Every clause of the seek target follows after supplying the existing documented invariant
and excluding the physical `size + 1` overflow boundary. This helper does not change the frozen target. -/
theorem iobufferSeekFromDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1) (n : Int) :
    (io.seekable = true →
      resultOf (source_seek_integer (source_seek bufferAccess) intClampgt intClamplt
        intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val =
        max 0 (min n (source_filesize io).val)) ∧
    (io.seekable = false →
      (resultOf (source_seek bufferAccess () (clampToI n)) io =
        if ismarked io then
          if clampToI n = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))) ∧
      (ismarked io = true → clampToI n = io.mark →
        (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val = io.mark.val)) := by
  constructor
  · intro hs
    exact iobufferSeekableDocumented io hd hsize hs n
  · intro hs
    refine ⟨iobufferSeekPipeResult io hs (clampToI n), ?_⟩
    intro hm he
    rw [he]
    exact (iobufferMarkedSeekDocumented io hd hsize hm).2

/-- Every skip-target clause follows from the documented invariant when both the physical
and logical ends fit. The missing assumptions are explicit helper premises, not changes to the target. -/
theorem iobufferSkipFromDocumented (io : BufferState) (hd : DocumentedInvariant7 io)
    (hsize : io.size.val < 2 ^ 63 - 1)
    (hlogical : io.size.val - io.offset.val ≤ 2 ^ 63 - 1) (n : Int) :
    (0 ≤ n → resultOf (source_skip_integer (source_skip bufferAccess (source_seek bufferAccess))
        intClampgt intClamplt intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        (source_position io).val + min n (source_bytesavailable io).val) ∧
    (n < 0 → io.seekable = true →
      resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io = .ok () ∧
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        max 0 ((source_position io).val + n)) ∧
    (n < 0 → io.seekable = false →
      let target := clampToI ((source_position io).val + (clampToI n).val)
      resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
        if ismarked io then
          if target = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    exact iobufferSkipNonnegDocumented io hd hsize hlogical n hn
  · intro hn hs
    exact iobufferSkipNegativeDocumented io hd hsize hs n hn
  · intro hn hs
    exact iobufferSkipNegativePipeResult io hs n hn

theorem IobuffersSeek_proven : SeekSpec := by
  intro io hd n
  refine ⟨?_, ?_, ?_⟩
  · intro allowed
    have run := iobufferSeekRunSuccess io (clampToI n) allowed
    constructor
    · rw [iobufferSourceSeekIntegerEq]
      simp only [resultOf, run]
    · simp only [stateOf, run]
      rfl
  · intro hs hsize
    exact (iobufferSeekableDocumented io hd hsize hs n).2
  · intro hs
    refine ⟨iobufferSeekPipeResult io hs (clampToI n), ?_⟩
    intro hsize hm he
    rw [he]
    exact (iobufferMarkedSeekDocumented io hd hsize hm).2

theorem IobuffersSkip_proven : SkipSpec := by
  intro io hd n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    have hc := iobufferClampToIValue n
    have run := iobufferSkipRunNonneg io (clampToI n) (by omega)
    constructor
    · rw [iobufferSourceSkipIntegerEq]
      simp only [resultOf, run]
    · simp only [stateOf, run]
      rfl
  · intro hn hsize hlogical
    exact (iobufferSkipNonnegDocumented io hd hsize hlogical n hn).2
  · intro hn
    dsimp only
    intro allowed
    have hc := iobufferClampToIValue n
    have run := iobufferSkipRunNegative io (clampToI n) (by omega)
    have seekRun := iobufferSeekRunSuccess io
      (clampToI ((source_position io).val + (clampToI n).val)) allowed
    constructor
    · simp only [resultOf, run, seekRun]
    · simp only [stateOf, run, seekRun]
      rfl
  · intro hn hs hsize
    exact (iobufferSkipNegativeDocumented io hd hsize hs n hn).2
  · intro hn hs
    exact iobufferSkipNegativePipeResult io hs n hn

end JuliaLean.ChatGPT.Batch3.Group5
namespace Round17

open JuliaLean JuliaLean.base.iobuffer

/-! Byte-observation statements over physically valid retained spans: the stored span stays inside the backing bytes, with no hypothesis on maxsize, permissions, seekability or marks. -/

/-! The following helper contains only storage/representation invariants. It
places no constraint on maxsize, permissions, seekability, or a requested integer.
The length bound keeps a one-past-end physical index representable as Julia Int.
-/
def StoredSpanValid (io : BufferState) : Prop :=
  io.data.length < 2 ^ 63 - 1 ∧
  0 ≤ io.size.val ∧ io.size.val ≤ (io.data.length : Int) ∧
  (getOffset io).val ≤ io.size.val ∧
  (getOffset io).val + 1 ≤ io.ptr.val ∧ io.ptr.val ≤ io.size.val + 1

/-- The available-byte count equals the length of the actual unread byte sequence.
Julia source: base/iobuffer.jl:55-71,466-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/io.jl:132-144; base/iobuffer.jl:466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AvailableByteCount : Prop :=
  ∀ io : BufferState, StoredSpanValid io →
    (source_bytesavailable io).val = (available io).length

/-- End-of-file is exactly the absence of unread bytes, including empty and compacted buffers.
Julia source: base/iobuffer.jl:55-71,691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/io.jl:209-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EofUnreadEquivalence : Prop :=
  ∀ io : BufferState, StoredSpanValid io →
    (source_eof io = true ↔ available io = [])

/-- File size counts all retained logical bytes for a seekable buffer and the unread bytes for a pipe.
Julia source: base/iobuffer.jl:55-71,463-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/iobuffer.jl:463-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FilesizeByteCount : Prop :=
  ∀ io : BufferState, StoredSpanValid io →
    (io.seekable = true → (source_filesize io).val = (content io).length) ∧
    (io.seekable = false → (source_filesize io).val = (available io).length)

end Round17

namespace Archive20261102Round17

open JuliaLean JuliaLean.base.iobuffer JuliaLean.Proofs.base.iobuffer

/-- Seeking clamps a seekable buffer to its endpoints and permits a nonseekable
buffer to seek exactly to a retained live mark, with the original error cases.
Julia source: base/iobuffer.jl:495-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/iostream.jl:143-146; base/iobuffer.jl:518-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SeekSpecReachable : Prop :=
  ∀ io, DocumentedInvariant7 io → io.size.val < 2 ^ 63 - 1 → ∀ n : Int,
    (io.seekable = true →
      resultOf (source_seek_integer (source_seek bufferAccess) intClampgt intClamplt
        intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val =
        max 0 (min n (source_filesize io).val)) ∧
    (io.seekable = false →
      (resultOf (source_seek bufferAccess () (clampToI n)) io =
        if ismarked io then
          if clampToI n = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))) ∧
      (ismarked io = true → clampToI n = io.mark →
        (source_position (stateOf (source_seek bufferAccess () (clampToI n)) io)).val = io.mark.val))

/-- Nonnegative skip advances up to the end; negative skip moves backward with
seekable clamping or the original nonseekable mark/error classification.
Julia source: base/iobuffer.jl:475-493,512-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/iostream.jl:198-202; base/iobuffer.jl:480-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SkipSpecReachable : Prop :=
  ∀ io, DocumentedInvariant7 io → io.size.val < 2 ^ 63 - 1 →
    io.size.val - io.offset.val ≤ 2 ^ 63 - 1 → ∀ n : Int,
    (0 ≤ n → resultOf (source_skip_integer (source_skip bufferAccess (source_seek bufferAccess))
        intClampgt intClamplt intClampConvert () n) io = .ok () ∧
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        (source_position io).val + min n (source_bytesavailable io).val) ∧
    (n < 0 → io.seekable = true →
      resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io = .ok () ∧
      (source_position (stateOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io)).val =
        max 0 ((source_position io).val + n)) ∧
    (n < 0 → io.seekable = false →
      let target := clampToI ((source_position io).val + (clampToI n).val)
      resultOf (source_skip bufferAccess (source_seek bufferAccess) () (clampToI n)) io =
        if ismarked io then
          if target = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked")))

end Archive20261102Round17

namespace JuliaLean.ChatGPT.Batch7.Group1

open JuliaLean JuliaLean.base.iobuffer JuliaLean.base.pointer
  JuliaLean.Proofs.base.iobuffer

/-- iocov-iobuffer-string-allocators: StringVector wraps the storage returned by StringMemory at the requested size. -/
theorem IocovIobufferStringAllocators_proven :
    JuliaLean.Proofs.base.iobuffer.StringAllocators := by
  intro stringN unsafeWrap wrapArray hUnsafe hWrap n bytes hn0 hnMax hString _
  have hr : IntTy.u64.min ≤ n ∧ n ≤ IntTy.u64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    simp
    omega
  have hu : toU n = .ok ⟨n, hr⟩ := by simp [toU, JInt.convert, hr]
  simp [source_StringVector, source_StringMemory, JuliaLean.base.strings.string.stringN,
    JuliaLean.base.strings.string.unsafeWrapMemory, hu, hString, hUnsafe,
    JuliaLean.base.array.wrapMemory, hWrap, Bind.bind, Except.bind]

/-- iocov-iobuffer-read-ptr: Pointer reads convert the UInt result and preserve the UInt reader's state change. -/
theorem IocovIobufferReadPtr_proven :
    JuliaLean.Proofs.base.iobuffer.PtrReadIsUIntRead := by
  intro io _ T value
  dsimp only
  intro h
  change
    resultOf (readUIntModel >>= fun word =>
      pure (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned word))) io =
        .ok (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned value)) ∧
      stateOf (readUIntModel >>= fun word =>
        pure (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned word))) io =
          stateOf readUIntModel io
  cases hr : readUIntModel.run io with
  | ok actual next =>
      have hActual : actual = value := by simpa [resultOf, hr] using h
      subst actual
      have hMapped :
          EStateM.map
            (fun word =>
              (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned word) :
                JuliaLean.base.pointer.Ptr T))
            readUIntModel io =
          .ok (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned value) :
            JuliaLean.base.pointer.Ptr T) next := by
        unfold EStateM.map
        rw [show readUIntModel io = .ok value next from hr]
      have hMapped' :
          EStateM.run
            ((fun word =>
              (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned word) :
                JuliaLean.base.pointer.Ptr T)) <$> readUIntModel) io =
          .ok (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned value) :
            JuliaLean.base.pointer.Ptr T) next := by
        exact hMapped
      simp [resultOf, stateOf, hMapped', hr]
  | error error next =>
      simp [resultOf, hr] at h

end JuliaLean.ChatGPT.Batch7.Group1

end JuliaLean.Proofs.base.iobuffer

section

namespace JuliaLean.ChatGPT.Batch6.Group1
open JuliaLean JuliaLean.base.iobuffer JuliaLean.Proofs.base.iobuffer


theorem group1SliceLength {α : Type} (xs : List α) (first last : Int)
    (hfirst : 1 ≤ first) (horder : first ≤ last + 1)
    (hlast : last ≤ (xs.length : Int)) :
    (((xs.drop (first - 1).toNat).take (last - first + 1).toNat).length : Int) =
      last - first + 1 := by
  have htake : (last - first + 1).toNat ≤ xs.length - (first - 1).toNat := by
    omega
  simp only [List.length_take, List.length_drop]
  rw [Nat.min_eq_left htake]
  omega

theorem group1SliceEmpty {α : Type} (xs : List α) (first last : Int)
    (hfirst : 1 ≤ first) (horder : first ≤ last + 1)
    (hlast : last ≤ (xs.length : Int)) :
    (xs.drop (first - 1).toNat).take (last - first + 1).toNat = [] ↔
      first = last + 1 := by
  have hlen := group1SliceLength xs first last hfirst horder hlast
  constructor
  · intro h
    rw [h] at hlen
    change (0 : Int) = last - first + 1 at hlen
    omega
  · intro h
    have hz : (last - first + 1).toNat = 0 := by omega
    rw [hz, List.take_zero]

theorem group1SpanIntegerBounds (capacity : Nat) (size ptr offset : Int)
    (hcapacity : capacity < 9223372036854775807)
    (hsize0 : 0 ≤ size) (hsize : size ≤ (capacity : Int))
    (hoffset0 : 0 ≤ offset) (hoffset : offset ≤ size)
    (hptr0 : offset + 1 ≤ ptr) (hptr : ptr ≤ size + 1) :
    (-9223372036854775808 ≤ size - ptr ∧ size - ptr ≤ 9223372036854775807) ∧
    (0 ≤ size - ptr + 1 ∧ size - ptr + 1 ≤ 9223372036854775807) ∧
    (0 ≤ ptr - 1 ∧ ptr - 1 ≤ 9223372036854775807) ∧
    (0 ≤ size - offset ∧ size - offset ≤ 9223372036854775807) := by
  omega


theorem resultFromRun {E H A : Type} (action : EStateM E H A) (heap next : H)
    (value : A) (h : action.run heap = .ok value next) :
    (match action.run heap with
      | .ok result _ => Except.ok result
      | .error error _ => Except.error error) = (Except.ok value : Except E A) := by
  rw [h]

theorem stateFromRun {E H A : Type} (action : EStateM E H A) (heap next : H)
    (value : A) (h : action.run heap = .ok value next) :
    (match action.run heap with
      | .ok _ state => state
      | .error _ state => state) = next := by
  rw [h]


-- Target proof candidates reconstructed from the supplied definitions.

theorem group1OffsetNonneg (io : BufferState) :
    0 ≤ (getOffset io).val := by
  rw [_root_.JuliaLean.Proofs.base.iobuffer.JuliaLean.ChatGPT.Batch3.Group5.iobufferOffsetValue io]
  omega

theorem group1WrapValue (io : BufferState) (h : Round17.StoredSpanValid io)
    (x : Int) (hlo : -1 ≤ x) (hhi : x ≤ io.size.val + 1) :
    (i x).val = x := by
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  change io.data.length < 9223372036854775807 at hcap
  apply _root_.JuliaLean.Proofs.base.iobuffer.JuliaLean.ChatGPT.Batch3.Group5.iobufferIValue
  · change (-9223372036854775808 : Int) ≤ x
    omega
  · change x ≤ (9223372036854775807 : Int)
    omega

theorem group1AvailableLength (io : BufferState) (h : Round17.StoredSpanValid io) :
    ((available io).length : Int) = io.size.val - io.ptr.val + 1 := by
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  exact group1SliceLength io.data io.ptr.val io.size.val
    (by omega) (by omega) hsizeData

theorem group1ContentLength (io : BufferState) (h : Round17.StoredSpanValid io) :
    ((content io).length : Int) = io.size.val - (getOffset io).val := by
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  have hlen := group1SliceLength io.data ((getOffset io).val + 1) io.size.val
    (by omega) (by omega) hsizeData
  change ((content io).length : Int) =
    io.size.val - ((getOffset io).val + 1) + 1 at hlen
  omega

theorem group1BytesavailableValue (io : BufferState) (h : Round17.StoredSpanValid io) :
    (source_bytesavailable io).val = io.size.val - io.ptr.val + 1 := by
  have hwrap := group1WrapValue io h
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  have hone : (i 1).val = 1 := hwrap 1 (by omega) (by omega)
  have hsub : (i (io.size.val - io.ptr.val)).val = io.size.val - io.ptr.val :=
    hwrap (io.size.val - io.ptr.val) (by omega) (by omega)
  change (i ((i (io.size.val - io.ptr.val)).val + (i 1).val)).val =
    io.size.val - io.ptr.val + 1
  rw [hsub, hone]
  exact hwrap (io.size.val - io.ptr.val + 1) (by omega) (by omega)

theorem group1PreviousValue (io : BufferState) (h : Round17.StoredSpanValid io) :
    (io.ptr - i 1).val = io.ptr.val - 1 := by
  have hwrap := group1WrapValue io h
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  have hone : (i 1).val = 1 := hwrap 1 (by omega) (by omega)
  change (i (io.ptr.val - (i 1).val)).val = io.ptr.val - 1
  rw [hone]
  exact hwrap (io.ptr.val - 1) (by omega) (by omega)

theorem group1StoredSizeValue (io : BufferState) (h : Round17.StoredSpanValid io) :
    (io.size - getOffset io).val = io.size.val - (getOffset io).val := by
  have hwrap := group1WrapValue io h
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  change (i (io.size.val - (getOffset io).val)).val =
    io.size.val - (getOffset io).val
  exact hwrap (io.size.val - (getOffset io).val) (by omega) (by omega)

theorem IobufferAvailableByteCount_proven :
    JuliaLean.Proofs.base.iobuffer.Round17.AvailableByteCount := by
  intro io h
  exact (group1BytesavailableValue io h).trans (group1AvailableLength io h).symm

theorem IobufferEofUnreadEquivalence_proven :
    JuliaLean.Proofs.base.iobuffer.Round17.EofUnreadEquivalence := by
  intro io h
  have hprev := group1PreviousValue io h
  have hoff0 := group1OffsetNonneg io
  rcases h with ⟨hcap, hsize0, hsizeData, hoffSize, hoffPtr, hptrSize⟩
  have hnil : available io = [] ↔ io.ptr.val = io.size.val + 1 :=
    group1SliceEmpty io.data io.ptr.val io.size.val (by omega) (by omega) hsizeData
  change decide ((io.ptr - i 1).val ≥ io.size.val) = true ↔ available io = []
  rw [hprev, hnil]
  simp only [decide_eq_true_eq]
  omega

theorem IobufferFilesizeByteCount_proven :
    JuliaLean.Proofs.base.iobuffer.Round17.FilesizeByteCount := by
  intro io h
  constructor
  · intro hseek
    have heq : (io.size - getOffset io).val = ((content io).length : Int) :=
      (group1StoredSizeValue io h).trans (group1ContentLength io h).symm
    simpa [source_filesize, hseek] using heq
  · intro hseek
    have heq := IobufferAvailableByteCount_proven io h
    simpa [source_filesize, source_bytesavailable, bytesavailable, hseek] using heq

theorem IobuffersSeekV2_proven :
    JuliaLean.Proofs.base.iobuffer.Archive20261102Round17.SeekSpecReachable := by
  intro io hd hsize n
  exact _root_.JuliaLean.Proofs.base.iobuffer.JuliaLean.ChatGPT.Batch3.Group5.iobufferSeekFromDocumented
    io hd hsize n

theorem IobuffersSkipV2_proven :
    JuliaLean.Proofs.base.iobuffer.Archive20261102Round17.SkipSpecReachable := by
  intro io hd hsize hlogical n
  exact _root_.JuliaLean.Proofs.base.iobuffer.JuliaLean.ChatGPT.Batch3.Group5.iobufferSkipFromDocumented
    io hd hsize hlogical n

-- Concrete refutation candidates; runtime evidence and limitations are recorded separately.

def group1MarkedPipe : BufferState :=
  { data := [0x61, 0x62, 0x63], isMemory := true, reinit := false,
    readable := true, writable := true, seekable := false, append := true,
    size := i 3, maxsize := i 10, ptr := i 2, offset := i 0, mark := i 0 }

set_option maxRecDepth 10000 in
theorem IobuffersTakestringMark_refuted :
    ¬ JuliaLean.Proofs.base.iobuffer.TakestringEqTake := by
  intro h
  let heap : counterexampleWorld.Heap := ((group1MarkedPipe, defaultBufferState), [])
  have hinv : worldValid counterexampleWorld heap false := by
    change stateInvariant group1MarkedPipe
    unfold stateInvariant
    decide
  have htake : worldResult (worldTake counterexampleWorld false) heap =
      .ok [0x62, 0x63] := by
    decide
  obtain ⟨string, hs, hbytes⟩ :=
    h counterexampleWorld heap false hinv rfl [0x62, 0x63] htake
  have hstring : worldResult (worldTakestring counterexampleWorld false) heap =
      .ok [0x61, 0x62, 0x63] := by
    decide
  rw [hstring] at hs
  have hs' : string = [0x61, 0x62, 0x63] := (Except.ok.inj hs).symm
  subst string
  change ([0x61, 0x62, 0x63] : List UInt8) = [0x62, 0x63] at hbytes
  have hne : ([0x61, 0x62, 0x63] : List UInt8) ≠ [0x62, 0x63] := by decide
  exact hne hbytes

def group1UnreadableInput : BufferState :=
  { data := [0x61, 0x0a], isMemory := true, reinit := false,
    readable := false, writable := true, seekable := true, append := false,
    size := i 2, maxsize := i 2, ptr := i 1, offset := i 0, mark := i (-1) }

def group1EmptyOutput : BufferState :=
  { data := [0, 0], isMemory := true, reinit := false,
    readable := true, writable := true, seekable := true, append := false,
    size := i 0, maxsize := i 2, ptr := i 1, offset := i 0, mark := i (-1) }

set_option maxRecDepth 10000 in
theorem IobuffersReaduntilUnreadable_refuted :
    ¬ JuliaLean.Proofs.base.iobuffer.ReadUntilUnreadable := by
  intro h
  let heap : counterexampleWorld.Heap := ((group1UnreadableInput, group1EmptyOutput), [])
  have hinv : worldValid counterexampleWorld heap false := by
    change stateInvariant group1UnreadableInput
    unfold stateInvariant
    decide
  have hc := h counterexampleWorld heap false true hinv rfl
    (counterexampleByte 0x0a) false ()
  obtain ⟨message, hm⟩ := hc.1
  have hok : worldResult
      (worldCopyuntil counterexampleWorld true false (counterexampleByte 0x0a) false ()) heap =
        .ok true := by
    decide +kernel
  rw [hok] at hm
  cases hm

set_option maxRecDepth 10000 in
theorem IobuffersPipebufferMaxsizeType_refuted :
    ¬ JuliaLean.Proofs.base.iobuffer.PipeBufferMaxsizeInteger := by
  intro h
  obtain ⟨io, hio⟩ := h .i32 1 (by decide) (by decide) (by decide) (by decide)
  have herror : runPipeBufferMaxsize .i32 1 = .error .typeError := by
    decide
  rw [herror] at hio
  cases hio

end JuliaLean.ChatGPT.Batch6.Group1

end

namespace JuliaLean.Proofs.base.iobuffer

open JuliaLean.Registry

open JuliaLean JuliaLean.base.iobuffer

private def viewGrowthBuffer (append : Bool) : BufferState :=
  { data := [0, 0, 0, 0], isMemory := false, reinit := false, readable := true,
    writable := true, seekable := !append, append := append, size := if append then i 4 else i 0,
    maxsize := i 8, ptr := i 1, offset := i 0, mark := i (-1) }

private def viewGrowthHeap (append : Bool) : counterexampleWorld.Heap :=
  ((viewGrowthBuffer append, defaultBufferState), [1, 2, 3, 4, 5])

private def viewGrowthPointer : JuliaLean.base.pointer.Ptr Byte :=
  ⟨JuliaLean.base.pointer.u64 0⟩

set_option maxRecDepth 10000 in
private theorem viewGrowthValid (append : Bool) :
    worldValid counterexampleWorld (viewGrowthHeap append) false := by
  cases append <;> change stateInvariant _ <;> unfold stateInvariant <;> decide

set_option maxRecDepth 10000 in
private theorem viewGrowthRoomFails (append : Bool) :
    worldResult (source_ensureroom (worldAccess counterexampleWorld)
      counterexampleWorld.storage false (u 5)) (viewGrowthHeap append) =
      .error (.jl (.methodError "get_used_span")) := by
  cases append <;> decide

private theorem viewGrowthPointerValid (append : Bool) :
    counterexampleWorld.validPointer (viewGrowthHeap append) viewGrowthPointer (u 5) := by
  change 0 + 5 ≤ 5
  decide

set_option maxRecDepth 10000 in
theorem writeAtPosition_native_refuted : ¬ WriteAtPosition := by
  intro h
  have contract := h counterexampleWorld (viewGrowthHeap false) false
    (viewGrowthValid false) rfl rfl rfl viewGrowthPointer (u 5) () (viewGrowthPointerValid false)
  have impossible := contract.1
  rw [viewGrowthRoomFails false] at impossible
  cases impossible

set_option maxRecDepth 10000 in
theorem appendWritesAtEnd_native_refuted : ¬ AppendWritesAtEnd := by
  intro h
  have contract := h counterexampleWorld (viewGrowthHeap true) false
    (viewGrowthValid true) rfl rfl viewGrowthPointer (u 5) () (viewGrowthPointerValid true)
  have impossible := contract.1
  rw [viewGrowthRoomFails true] at impossible
  cases impossible

set_option maxRecDepth 10000 in
theorem truncate_native_refuted : ¬ TruncateSpec := by
  intro h
  have ran := (h counterexampleWorld (viewGrowthHeap false) false (viewGrowthValid false) 5).1
  have failed : worldResult (worldTruncate counterexampleWorld false 5) (viewGrowthHeap false) =
      .error (.jl (.methodError "get_used_span")) := by decide
  have expected : worldResult (worldTruncate counterexampleWorld false 5) (viewGrowthHeap false) =
      .ok false := by
    have hw : (worldSnapshot counterexampleWorld (viewGrowthHeap false) false).writable = true := rfl
    have hs : (worldSnapshot counterexampleWorld (viewGrowthHeap false) false).seekable = true := rfl
    have hm : (worldSnapshot counterexampleWorld (viewGrowthHeap false) false).maxsize.val = 8 := rfl
    simpa only [hw, hs, hm, Bool.true_eq_false, ite_false,
      show ¬ (5 : Int) < 0 by omega, show ¬ (5 : Int) > 8 by omega] using ran
  rw [failed] at expected
  cases expected

private def copylinePriorWorld : BufferWorld :=
  { counterexampleWorld with dense := fun _ _ => true }

private def copylinePriorInput : BufferState :=
  { data := [], isMemory := true, reinit := false, readable := true,
    writable := false, seekable := true, append := false, size := i 0,
    maxsize := i 0, ptr := i 1, offset := i 0, mark := i (-1) }

private def copylinePriorOutput : BufferState :=
  { data := [0x61, 0x0a], isMemory := true, reinit := false, readable := true,
    writable := true, seekable := true, append := false, size := i 2,
    maxsize := i 10, ptr := i 3, offset := i 0, mark := i (-1) }

private def copylinePriorHeap : copylinePriorWorld.Heap :=
  ((copylinePriorInput, copylinePriorOutput), [])

set_option maxRecDepth 10000 in
private theorem copylinePriorDiff :
    (worldResult (worldCopylineBuffer copylinePriorWorld true [] false ()) copylinePriorHeap).map
      (fun ref => worldSnapshot copylinePriorWorld
        (worldState (worldCopylineBuffer copylinePriorWorld true [] false ()) copylinePriorHeap) ref) ≠
    (worldResult (worldWriteBytes copylinePriorWorld true []) copylinePriorHeap).map
      (fun _ => worldAfter copylinePriorWorld
        (worldWriteBytes copylinePriorWorld true []) copylinePriorHeap true) := by
  decide

set_option maxRecDepth 10000 in
theorem copylineAtEnd_native_refuted : ¬ CopylineAtEnd := by
  intro h
  have hout : worldValid copylinePriorWorld copylinePriorHeap true := by
    change stateInvariant copylinePriorOutput
    unfold stateInvariant
    decide
  exact copylinePriorDiff
    (h copylinePriorWorld copylinePriorHeap true [] hout rfl (Or.inr rfl) ())

set_option maxRecDepth 10000 in
theorem copylineMethods_native_refuted : ¬ CopylineMethods := by
  intro h
  have hin : worldValid copylinePriorWorld copylinePriorHeap false := by
    change stateInvariant copylinePriorInput
    unfold stateInvariant
    decide
  have hout : worldValid copylinePriorWorld copylinePriorHeap true := by
    change stateInvariant copylinePriorOutput
    unfold stateInvariant
    decide
  have contract := (h copylinePriorWorld copylinePriorHeap false true hin rfl false ()).2
  exact copylinePriorDiff (contract [] rfl hout rfl)

set_option maxRecDepth 10000 in
theorem truncateKeepsMark_native_refuted : ¬ TruncateKeepsMark := by
  intro h
  let io : BufferState :=
    { data := [0x61, 0x62, 0x63, 0x64, 0x65, 0x66], isMemory := true,
      reinit := false, readable := true, writable := true, seekable := true,
      append := false, size := i 6, maxsize := i 32, ptr := i 4,
      offset := i 0, mark := i 3 }
  let heap : counterexampleWorld.Heap := ((io, defaultBufferState), [])
  have hinv : worldValid counterexampleWorld heap false := by
    change stateInvariant io
    unfold stateInvariant
    decide
  have marked : ismarked (worldSnapshot counterexampleWorld heap false) = true := by decide
  have within : (worldSnapshot counterexampleWorld heap false).mark.val ≤ (3 : Int) := by decide
  have ran : worldResult (worldTruncate counterexampleWorld false 3) heap = .ok false := by decide
  have lost : ismarked (worldAfter counterexampleWorld
      (worldTruncate counterexampleWorld false 3) heap false) = false := by decide
  have kept := h counterexampleWorld heap false hinv marked 3 within ran
  rw [lost] at kept
  cases kept

namespace SharedMemoryProofs

open JuliaLean JuliaLean.base.iobuffer
open JuliaLean.base.iobuffer.SharedMemory

private def Unchanged {Other A : Type} (action : Action Other A) : Prop :=
  ∀ heap, worldState action heap = heap

private theorem unchanged_pure {Other A : Type} (value : A) :
    Unchanged (pure value : Action Other A) := fun _ => rfl

private theorem unchanged_get {Other : Type} :
    Unchanged (get : Action Other (Heap Other)) := fun _ => rfl

private theorem unchanged_bind {Other A B : Type} (action : Action Other A)
    (next : A → Action Other B) (ha : Unchanged action)
    (hn : ∀ value, Unchanged (next value)) : Unchanged (action >>= next) := by
  simp only [Unchanged, worldState, EStateM.run, Bind.bind, EStateM.bind] at *
  intro heap
  have hs := ha heap
  cases hrun : action heap with
  | error error after => simpa [hrun] using hs
  | ok value after =>
    have heq : after = heap := by simpa [hrun] using hs
    subst after
    simpa [hrun] using hn value heap

private theorem unchanged_find {Other : Type} (ref : Nat)
    (fields : List (Nat × Fields ByteMemory)) :
    Unchanged (findBufferFields (m := Action Other) (fun a b => decide (a = b)) ref fields) := by
  induction fields with
  | nil => exact unchanged_pure none
  | cons pair rest ih =>
    simp only [findBufferFields]
    split
    · exact unchanged_pure _
    · exact ih

private theorem unchanged_fields {Other : Type}
    (allocateObject : Fields ByteMemory → Action Other Nat) (ref : Nat) :
    Unchanged ((access allocateObject).get ref) := by
  unfold access bindHeapAccess
  apply unchanged_bind _ _ unchanged_get
  intro heap
  apply unchanged_bind _ _ (unchanged_find ref heap.buffers)
  intro fields
  cases fields <;> intro heap <;> rfl

private theorem unchanged_pointer_heap {Other : Type} :
    Unchanged (pointerHeap.get : Action Other JuliaLean.base.pointer.ByteHeap) := by
  unfold pointerHeap bindHeapPointerHeap
  apply unchanged_bind _ _ unchanged_get
  intro heap
  exact unchanged_pure _

/-- Concrete Memory-backed peek preserves all buffer fields and shared bytes,
including on permission and EOF errors. No getter, pointer, or storage callback
is left open; the codec has no world operations. -/
def PeekPreservesSharedHeap : Prop :=
  ∀ (Other : Type) (allocateObject : Fields ByteMemory → Action Other Nat)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (ref : Nat) (kind : Multibyte) (heap : Heap Other),
    worldState (SharedMemory.peek allocateObject codec ref kind) heap = heap

theorem peekPreservesSharedHeap_proven : PeekPreservesSharedHeap := by
  intro Other allocateObject codec ref kind
  change Unchanged (SharedMemory.peek allocateObject codec ref kind)
  unfold SharedMemory.peek source_peek_multibyte_dense
  apply unchanged_bind _ _ (unchanged_fields allocateObject ref)
  intro fields
  by_cases hr : (!fields.readable) = true
  · simp only [hr, ↓reduceIte, liftIO, source_throw_not_readable]
    intro heap
    rfl
  · simp only [hr, Bool.false_eq_true, ite_false]
    split
    · intro heap
      rfl
    · apply unchanged_bind _ _ (unchanged_fields allocateObject ref)
      intro current
      apply unchanged_bind _ _ (unchanged_pure _)
      intro pointer
      apply unchanged_bind _ _ unchanged_pointer_heap
      intro bytes
      split
      · intro heap
        rfl
      · rename_i error _
        cases error <;> intro heap <;> rfl


open JuliaLean JuliaLean.base.iobuffer
open JuliaLean.base.iobuffer.SharedMemory

private def lookup (ref : Nat) (fields : List (Nat × Fields ByteMemory)) :
    Option (Fields ByteMemory) :=
  findBufferFields (m := Id) (fun a b => decide (a = b)) ref fields

private theorem find_run {Other : Type} (ref : Nat)
    (fields : List (Nat × Fields ByteMemory)) (heap : Heap Other) :
    findBufferFields (m := Action Other) (fun a b => decide (a = b)) ref fields heap =
      .ok (lookup ref fields) heap := by
  induction fields with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, fields⟩
    by_cases h : ref = key
    · simp [findBufferFields, lookup, h]
      rfl
    · simpa [findBufferFields, lookup, h] using ih

private theorem get_run {Other : Type}
    (allocateObject : Fields ByteMemory → Action Other Nat)
    (ref : Nat) (heap : Heap Other) (fields : Fields ByteMemory)
    (h : lookup ref heap.buffers = some fields) :
    (access allocateObject).get ref heap = .ok fields heap := by
  simp only [access, bindHeapAccess, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, find_run, h, Pure.pure, EStateM.pure]

private theorem replace_lookup (ref : Nat)
    (before : List (Nat × Fields ByteMemory)) (old new : Fields ByteMemory)
    (h : lookup ref before = some old) :
    ∃ after,
      replaceBufferFields (fun a b => decide (a = b)) ref new before = some after ∧
      lookup ref after = some new := by
  induction before with
  | nil => simp [lookup, findBufferFields] at h
  | cons pair rest ih =>
    rcases pair with ⟨key, fields⟩
    by_cases heq : ref = key
    · subst key
      refine ⟨(ref, new) :: rest, ?_, ?_⟩ <;>
        simp [lookup, findBufferFields, replaceBufferFields] <;> rfl
    · have hr : lookup ref rest = some old := by
        simpa [lookup, findBufferFields, heq] using h
      obtain ⟨after, replaced, found⟩ := ih hr
      refine ⟨(key, fields) :: after, ?_, ?_⟩
      · simp [replaceBufferFields, heq, replaced]
      · simpa [lookup, findBufferFields, heq] using found

private theorem fieldsPosition_after_add (fields : Fields ByteMemory) (count : I) :
    fieldsPosition { fields with ptr := JuliaLean.base.int.add fields.ptr count } =
      JuliaLean.base.int.add (fieldsPosition fields) count := by
  apply Subtype.ext
  simp only [fieldsPosition, JuliaLean.base.int.add, JuliaLean.base.int.sub,
    JuliaLean.Proofs.base.int.add_int_val, JuliaLean.Proofs.base.int.sub_int_val]
  simp only [JuliaLean.Proofs.base.int.wrapInt_sub_left,
    JuliaLean.Proofs.base.int.wrapInt_add_left]
  congr 1
  omega

def ReadAdvancesSharedPointer : Prop :=
  ∀ (Other : Type) (allocateObject : Fields ByteMemory → Action Other Nat)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (ref : Nat) (kind : Multibyte) (before after : Heap Other)
    (fields : Fields ByteMemory) (value : valueType kind),
    lookup ref before.buffers = some fields →
    SharedMemory.read allocateObject codec ref kind before = .ok value after →
      lookup ref after.buffers = some { fields with ptr := (JuliaLean.base.int.add fields.ptr (JuliaLean.base.int.sizeof (initialWord kind))) } ∧
      fieldsPosition { fields with ptr := (JuliaLean.base.int.add fields.ptr (JuliaLean.base.int.sizeof (initialWord kind))) } =
        JuliaLean.base.int.add (fieldsPosition fields) (JuliaLean.base.int.sizeof (initialWord kind)) ∧
      after.bytes = before.bytes ∧ after.other = before.other

theorem readAdvancesSharedPointer_proven : ReadAdvancesSharedPointer := by
  intro Other allocateObject codec ref kind before after fields value hfields hread
  have hkeep := peekPreservesSharedHeap_proven Other allocateObject codec ref kind before
  let nextFields := { fields with ptr := (JuliaLean.base.int.add fields.ptr (JuliaLean.base.int.sizeof (initialWord kind))) }
  obtain ⟨buffers, hreplace, hfound⟩ := replace_lookup ref before.buffers fields nextFields hfields
  have hget := get_run allocateObject ref before fields hfields
  unfold SharedMemory.read readMultibyteDense at hread
  change ((SharedMemory.peek allocateObject codec ref kind >>= fun value => do
    let current ← (access allocateObject).get ref
    (access allocateObject).set ref { current with ptr := (JuliaLean.base.int.add current.ptr (JuliaLean.base.int.sizeof (initialWord kind))) }
    pure value) before) = .ok value after at hread
  cases hp : SharedMemory.peek allocateObject codec ref kind before with
  | error error state =>
    simp only [worldState, EStateM.run, hp] at hkeep
    simp [Bind.bind, EStateM.bind, hp] at hread
  | ok result state =>
    have hs : state = before := by simpa only [worldState, EStateM.run, hp] using hkeep
    subst state
    simp only [Bind.bind, EStateM.bind, hp, hget] at hread
    have hset : (access allocateObject).set ref nextFields before =
        .ok () { before with buffers := buffers } := by
      simp only [access, bindHeapAccess, Bind.bind, EStateM.bind, get, getThe,
        set, MonadStateOf.get, MonadStateOf.set, EStateM.get, EStateM.set, hreplace]
    change ((access allocateObject).set ref nextFields >>= fun _ => pure result) before =
      .ok value after at hread
    simp only [Bind.bind, EStateM.bind, hset, Pure.pure, EStateM.pure] at hread
    cases hread
    exact ⟨hfound, fieldsPosition_after_add fields _, rfl, rfl⟩


end SharedMemoryProofs

def entries : List Entry := [
  { id := "iobuffer-memory-read-shared-position", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer{Memory{UInt8}}, ::MultiByteBitNumberType)"],
    statement := "A successful multibyte read advances the reported position by sizeof(T), with native Int arithmetic, and preserves the shared byte storage and auxiliary state.",
    source := "base/iobuffer.jl:432-436",
    status := .proven, prop := ``SharedMemoryProofs.ReadAdvancesSharedPointer,
    thm := some ``SharedMemoryProofs.readAdvancesSharedPointer_proven },
  { id := "iobuffer-memory-peek-shared-state", juliaFile := "base/iobuffer.jl",
    juliaFns := ["peek(::GenericIOBuffer{Memory{UInt8}}, ::MultiByteBitNumberType)"],
    statement := "Peeking a multibyte value from a Memory-backed IOBuffer leaves its shared buffer fields and byte storage unchanged, including on read-permission and EOF errors.",
    source := "base/iobuffer.jl:418-430; base/subarray.jl:365-370",
    status := .proven, prop := ``SharedMemoryProofs.PeekPreservesSharedHeap,
    thm := some ``SharedMemoryProofs.peekPreservesSharedHeap_proven },
  { id := "iobuffers-invariant", juliaFile := "base/iobuffer.jl",
    juliaFns := ["position", "bytesavailable", "eof", "filesize", "write", "read(::GenericIOBuffer, ::Type{UInt8})", "seek", "skip", "truncate", "compact!", "take!", "closewrite", "close"],
    statement := "Valid states keep position between zero and logical size; bytesavailable is nonnegative, eof means no bytes remain, and seekable position plus bytesavailable equals filesize. Successful state-changing methods preserve the field invariant.", source := "invariant base/iobuffer.jl:55-93 (field comments)",
    status := .todo, prop := ``InvariantHolds, thm := none },
  { id := "iobuffers-no-out-of-bounds", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write", "unsafe_read", "read(::GenericIOBuffer, ::Type{UInt8})", "peek", "compact!", "_resize!"],
    statement := "With a nonnegative maxsize, no operation on a reachable buffer reads or writes outside its memory.", source := "invariant base/iobuffer.jl:55-70",
    status := .todo, prop := ``NoOutOfBounds, thm := none },
  { id := "iobuffers-write-at-position", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "ensureroom"],
    statement := "write on a seekable non-append IOBuffer overwrites from the position, writes min(n, maxsize - position) bytes and advances the position by that much.", source := "base/iobuffer.jl:173-180 (IOBuffer docstring: maxsize), 67-69",
    status := .refuted, prop := ``WriteAtPosition, thm := some ``writeAtPosition_native_refuted,
    issue := "see bugs/iobuffers-view-grow.yaml" },
  { id := "iobuffers-append-at-end", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "PipeBuffer"],
    statement := "write on an append buffer adds min(n, maxsize - retained bytes) bytes at the end and leaves the position alone, also across compaction.", source := "base/iobuffer.jl:52-53 (append writes to size+1), 278 (PipeBuffer performs writes by appending)",
    status := .refuted, prop := ``AppendWritesAtEnd, thm := some ``appendWritesAtEnd_native_refuted,
    issue := "see bugs/iobuffers-view-grow.yaml" },
  { id := "iobuffers-write-read-roundtrip", juliaFile := "base/iobuffer.jl",
    juliaFns := ["IOBuffer(; maxsize)", "write", "seekstart", "read(::GenericIOBuffer)"],
    statement := "IOBuffer(maxsize=m), any writes, seekstart, read returns the first m bytes written.", source := "base/iobuffer.jl:180, 214-221 (maxsize docstring and example)",
    status := .todo, prop := ``WriteReadRoundtrip, thm := none,
    issue := "none found (queries: get_used_span, IOBuffer view write, IOBuffer SubArray, GenericIOBuffer MethodError, IOBuffer view MethodError); same get_used_span root cause as iobuffers-view-grow" },
  { id := "iobuffers-pipe-fifo", juliaFile := "base/iobuffer.jl",
    juliaFns := ["PipeBuffer", "write", "read(::GenericIOBuffer, ::Type{UInt8})", "read(::GenericIOBuffer, nb)", "read(::GenericIOBuffer)"],
    statement := "On a PipeBuffer, bytes read and still available equal the initially unread bytes plus bytes accepted by writes, preserving order under every interleaving.", source := "base/iobuffer.jl:272-283 (PipeBuffer behaves like a Unix pipe)",
    status := .todo, prop := ``PipeFIFO, thm := none },
  { id := "iobuffers-pipe-mark-reset", juliaFile := "base/iobuffer.jl",
    juliaFns := ["mark", "reset", "compact!", "get_used_span", "PipeBuffer"],
    statement := "On a PipeBuffer, reset after mark restores the marked position and makes every byte accepted by later writes available, even after reads and compaction.", source := "base/io.jl:1569-1606 (mark/reset docstrings); base/iobuffer.jl:44-46",
    status := .todo, prop := ``PipeMarkReset, thm := none },
  { id := "iobuffers-seek", juliaFile := "base/iobuffer.jl",
    juliaFns := ["seek(::GenericIOBuffer, ::Integer)", "seekstart"],
    statement := "On the full documented offset/live-mark invariant, seek clamps Integer requests to Int and translates by the offset; physical endpoints and reported position use native wrapping Int arithmetic. Seekable buffers clamp to [0, filesize] when size + 1 fits; pipes accept exactly their retained mark and restore its position when size + 1 fits.", source := "base/iostream.jl:143-146; base/iobuffer.jl:496-523",
    status := .proven, prop := ``SeekSpec, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.IobuffersSeek_proven },
  { id := "iobuffers-skip", juliaFile := "base/iobuffer.jl",
    juliaFns := ["skip(::GenericIOBuffer, ::Integer)"],
    statement := "On the full documented offset/live-mark invariant, skip clamps Integer requests to Int. Nonnegative skip adds min(request, size + 1 - ptr) using native wrapping Int arithmetic; negative skip seeks to the widened, Int-clamped position + request and retains the pipe mark/error classification. Ordinary forward and backward position equations hold when the physical and logical ends fit.", source := "base/iostream.jl:198-202; base/iobuffer.jl:475-493,512-523",
    status := .proven, prop := ``SkipSpec, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.IobuffersSkip_proven },
  { id := "iobuffers-truncate", juliaFile := "base/iobuffer.jl",
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"],
    statement := "truncate(io, n) throws ArgumentError exactly when not writable, not seekable, n < 0 or n > maxsize; otherwise the buffer holds its old bytes cut or zero-padded to n and position <= n.", source := "base/iobuffer.jl:558-593; truncate docstring (base/iostream.jl)",
    status := .refuted, prop := ``TruncateSpec, thm := some ``truncate_native_refuted,
    issue := "see bugs/iobuffers-view-grow.yaml" },
  { id := "iobuffers-take", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)"],
    statement := "take! on a writable IOBuffer returns all bytes (the unread bytes of a pipe) and leaves position, bytesavailable and filesize 0 and no mark.", source := "base/iobuffer.jl:716-718 (take! docstring)",
    status := .todo, prop := ``TakeSpec, thm := none },
  { id := "iobuffers-read", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer, nb)", "readbytes!", "read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})"],
    statement := "read(io, n) and readbytes! return the next min(n, bytesavailable) bytes and advance by that much; read(io, UInt8) returns the next byte or throws EOFError; peek does not move.", source := "base/io.jl:1295-1330 (read and readbytes! docstrings)",
    status := .todo, prop := ``ReadSpec, thm := none },
  { id := "iobuffers-readuntil", juliaFile := "base/iobuffer.jl",
    juliaFns := ["readuntil(::IO, ::UInt8)", "copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "readline", "_copyline"],
    statement := "readuntil(io, d; keep) and readline(io; keep) return the bytes up to the delimiter (with it iff keep; readline also strips \\r\\n) and consume through the delimiter.", source := "base/io.jl:640-648 (copyuntil docstring), 719-728 (copyline docstring)",
    status := .todo, prop := ``ReadUntilSpec, thm := none },
  { id := "iobuffers-occursin", juliaFile := "base/iobuffer.jl",
    juliaFns := ["occursin(::UInt8, ::GenericIOBuffer)"],
    statement := "occursin(d, io) tells whether d is among the bytes available.", source := "invariant (base/iobuffer.jl:984-986)",
    status := .todo, prop := ``OccursinSpec, thm := none },
  { id := "iobuffers-take-closewrite", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)", "closewrite(::GenericIOBuffer)"],
    statement := "take! on a readable IOBuffer that is not writable returns its contents (the unread bytes of a pipe).", source := "base/iobuffer.jl:716-718 (take! docstring)",
    status := .refuted, prop := ``TakeReadOnly, thm := some ``takeReadOnly_refuted,
    issue := "none found (queries: Unreachable IOBuffer state, Unreachable IOBuffer, closewrite PipeBuffer take!, closewrite PipeBuffer)" },
  { id := "iobuffers-take-readonly-reset", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)"],
    statement := "After take!(io) the IOBuffer is reset to its initial state (position 0).", source := "base/iobuffer.jl:716-718 (take! docstring: Afterwards, the IOBuffer is reset to its initial state)",
    status := .refuted, prop := ``TakeResets, thm := some ``takeResets_refuted,
    issue := "none found (queries: take! read-only IOBuffer, take! reset initial state)" },
  { id := "iobuffers-takestring-mark", juliaFile := "base/iobuffer.jl",
    juliaFns := ["takestring!(::IOBuffer)"],
    statement := "takestring!(io) returns the same bytes as String(take!(io)).", source := "base/iobuffer.jl:812-817 (takestring! docstring)",
    status := .refuted, prop := ``TakestringEqTake,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobuffersTakestringMark_refuted,
    issue := "see bugs/iobuffers-takestring-mark.yaml" },
  { id := "iobuffers-readuntil-unreadable", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "_copyline(::IO, ::GenericIOBuffer)"],
    statement := "readuntil and readline on an IOBuffer that is not readable throw ArgumentError, like read.", source := "base/iobuffer.jl:178 (read keyword restricts operations), 344-350",
    status := .refuted, prop := ``ReadUntilUnreadable,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobuffersReaduntilUnreadable_refuted,
    issue := "see bugs/iobuffers-readuntil-unreadable.yaml" },
  { id := "iobuffers-copyline-middle", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"],
    statement := "copyline(out::IOBuffer, s; keep=false) into the middle of out writes the line without its newline.", source := "base/io.jl:724-728 (copyline docstring)",
    status := .todo, prop := ``CopylineMiddle,
    thm := none,
    issue := "none found (queries: copyline, copyline IOBuffer, copyline keep, copyline keep false, copyline CRLF)" },
  { id := "iobuffers-copyline-prior", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"],
    statement := "copyline(out::IOBuffer, s; keep=false) at the end of out leaves the bytes already in out untouched.", source := "base/io.jl:718-728 (copyline docstring)",
    status := .refuted, prop := ``CopylineAtEnd,
    thm := some ``copylineAtEnd_native_refuted,
    issue := "see bugs/iobuffers-copyline-prior.yaml; JuliaLang/julia#64164" },
  { id := "iobuffers-pipebuffer-maxsize-type", juliaFile := "base/iobuffer.jl",
    juliaFns := ["PipeBuffer(data; maxsize)", "PipeBuffer(maxsize::Integer)"],
    statement := "PipeBuffer accepts maxsize of any Integer type, as documented.", source := "base/iobuffer.jl:276 (PipeBuffer docstring: maxsize::Integer)",
    status := .refuted, prop := ``PipeBufferMaxsizeInteger, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobuffersPipebufferMaxsizeType_refuted,
    issue := "see bugs/iobuffers-pipebuffer-maxsize-type.yaml" },
  { id := "iobuffers-truncate-mark", juliaFile := "base/iobuffer.jl",
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"],
    statement := "truncate(io, n) keeps a mark at a position <= n.", source := "base/iobuffer.jl:578 (comment: clear the mark if it points to data that has now been deleted)",
    status := .refuted, prop := ``TruncateKeepsMark, thm := some ``truncateKeepsMark_native_refuted,
    issue := "see bugs/iobuffers-truncate-mark.yaml" },
  { id := "memsafety-iobuffer-operations", juliaFile := "base/iobuffer.jl",
    juliaFns := ["peek", "read", "take!", "get_used_span", "mark", "reset", "unsafe_takestring!", "takestring!", "_unsafe_take!"],
    statement := "The documented IOBuffer field invariant bounds the computed read pointer, take view, translated marked span, and both exact-size string copies.", source := "base/iobuffer.jl:55-93,406-448,661-673,758-859; JuliaLean.IOBuffers.reachable_inv",
    status := .todo, prop := ``IOBufferOperationsInBounds, thm := none },
  { id := "iocov-iobuffer-show-compacted", juliaFile := "base/iobuffer.jl",
    juliaFns := ["show(::IO, ::GenericIOBuffer)"],
    statement := "The ptr printed by show(::IOBuffer) is the read position plus one, as the skipchars docstring example shows.", source := "base/io.jl:1628-1632 (skipchars docstring example)",
    status := .todo, prop := ``ShowPtrPosition, thm := none,
    issue := "none found (queries: IOBuffer show ptr, IOBuffer show compacted)" },
  { id := "iocov-iobuffer-show", juliaFile := "base/iobuffer.jl",
    juliaFns := ["show(::IO, ::GenericIOBuffer)", "get_offset", "get_compacted"],
    statement := "For a buffer that has not been compacted, show prints size and ptr after subtracting its offset.", source := "base/iobuffer.jl:334-342 (invariant)",
    status := .todo, prop := ``ShowUncompacted, thm := none },
  { id := "iocov-iobuffer-vector-constructor", juliaFile := "base/iobuffer.jl",
    juliaFns := ["GenericIOBuffer(::Vector{UInt8},...)"],
    statement := "For a Vector with backing length below 2^62 and a valid view range, the constructor preserves its memory offset and restricts size to the view.",
    source := "base/iobuffer.jl:141-161",
    status := .todo, prop := ``Round14.VectorConstructorR14, thm := none },
  { id := "iocov-iobuffer-string-allocators", juliaFile := "base/iobuffer.jl",
    juliaFns := ["StringMemory", "StringVector"],
    statement := "StringVector wraps the storage returned by StringMemory at the requested size.", source := "base/iobuffer.jl:167-168",
    status := .proven, prop := ``StringAllocators,
    thm := some ``JuliaLean.ChatGPT.Batch7.Group1.IocovIobufferStringAllocators_proven },
  { id := "iocov-iobuffer-public-constructors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["IOBuffer", "PipeBuffer"],
    statement := "Public constructors apply open flags and the documented readable, writable, seekable, and append settings.", source := "base/iobuffer.jl:230-285",
    status := .todo, prop := ``PublicConstructors, thm := none },
  { id := "iocov-iobuffer-not-readable", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_throw_not_readable", "read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})"],
    statement := "The unreadable helper always throws the documented ArgumentError, which byte reads and peeks propagate.", source := "base/iobuffer.jl:344-350,438-456",
    status := .proven, prop := ``ThrowNotReadable, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.IocovIobufferNotReadable_proven },
  { id := "iocov-iobuffer-peek-multibyte", juliaFile := "base/iobuffer.jl",
    juliaFns := ["peek(::GenericIOBuffer,::MultiByteBitNumberType)"],
    statement := "Both multibyte peek paths check readability and availability and do not advance the pointer.", source := "base/iobuffer.jl:406-430",
    status := .todo, prop := ``PeekMethodsDoNotAdvance, thm := none },
  { id := "iocov-iobuffer-read-multibyte", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer,::MultiByteBitNumberType)"],
    statement := "A successful multibyte read advances by sizeof(T).", source := "base/iobuffer.jl:432-436",
    status := .todo, prop := ``ReadMultiAdvances, thm := none },
  { id := "iocov-iobuffer-read-ptr", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer,::Type{Ptr{T}})"],
    statement := "Pointer reads convert the UInt result and preserve the UInt reader's state change.", source := "base/iobuffer.jl:458",
    status := .proven, prop := ``PtrReadIsUIntRead,
    thm := some ``JuliaLean.ChatGPT.Batch7.Group1.IocovIobufferReadPtr_proven },
  { id := "iocov-iobuffer-read-write-flags", juliaFile := "base/iobuffer.jl",
    juliaFns := ["isreadable", "iswritable", "closewrite"],
    statement := "Capability queries match their fields; closewrite clears writability and leaves readability unchanged.", source := "base/iobuffer.jl:460-461,693-696",
    status := .todo, prop := ``ReadWriteFlags, thm := none },
  { id := "iocov-iobuffer-seek-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["skip(::GenericIOBuffer,::Int)", "translate_seek_position", "seek(::GenericIOBuffer,::Int)", "seekend"],
    statement := "Seeking methods clamp positions and preserve the documented non-seekable checks.", source := "base/iobuffer.jl:479-529",
    status := .refuted, prop := ``SeekMethodsCorrect,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group5.IocovIobufferSeekMethods_refuted,
    issue := "none found (queries: PipeBuffer seekend filesize position; PipeBuffer seekend)" },
  { id := "iocov-iobuffer-close-method", juliaFile := "base/iobuffer.jl",
    juliaFns := ["close(::GenericIOBuffer)"],
    statement := "close releases writable storage and resets every observable buffer field.", source := "base/iobuffer.jl:698-711",
    status := .todo, prop := ``CloseMethodCorrect, thm := none },
  { id := "iocov-iobuffer-isopen-method", juliaFile := "base/iobuffer.jl",
    juliaFns := ["isopen(::GenericIOBuffer)", "close(::GenericIOBuffer)", "closewrite(::GenericIOBuffer)"],
    statement := "A buffer is open when any capability remains or unread bytes remain; close and closewrite update that state accordingly.", source := "base/iobuffer.jl:698-713",
    status := .todo, prop := ``IsopenCorrect, thm := none },
  { id := "iocov-iobuffer-take-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::GenericIOBuffer)", "takestring!(::GenericIOBuffer)"],
    statement := "Generic take returns reachable contents and resets writable buffers; generic takestring converts that result.", source := "base/iobuffer.jl:731-753,862",
    status := .todo, prop := ``TakeMethodsCorrect, thm := none },
  { id := "iocov-iobuffer-write-from-buffer", juliaFile := "base/iobuffer.jl",
    juliaFns := ["write(::IO,::GenericIOBuffer)"],
    statement := "Writing a buffer consumes all readable bytes and rejects self-copy.", source := "base/iobuffer.jl:886-897",
    status := .todo, prop := ``WriteFromConsumes, thm := none },
  { id := "iocov-iobuffer-byte-read-write", juliaFile := "base/iobuffer.jl",
    juliaFns := ["write(::GenericIOBuffer,::UInt8)", "readbytes!", "readavailable", "read(::GenericIOBuffer,::Integer)"],
    statement := "Byte I/O methods use the differential-tested state operations and consume no more than available data.", source := "base/iobuffer.jl:948-982",
    status := .todo, prop := ``ByteReadWriteMethods, thm := none },
  { id := "iocov-iobuffer-copyline-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer,::IO)", "copyline(::IO,::GenericIOBuffer)", "copyline(::GenericIOBuffer,::GenericIOBuffer)"],
    statement := "The optimized copyline methods copy one line, strip the delimiter when requested, and advance the input.", source := "base/iobuffer.jl:1010-1080",
    status := .refuted, prop := ``CopylineMethods, thm := some ``copylineMethods_native_refuted,
    issue := "see bugs/iobuffers-copyline-prior.yaml; JuliaLang/julia#64164" },
  { id := "iobuffer-read-available-peek-counts", juliaFile := "base/iobuffer.jl",
    juliaFns := ["readavailable(::GenericIOBuffer)", "read(::GenericIOBuffer, nb::Integer)", "peek(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::MultiByteBitNumberType)"],
    statement := "readavailable returns all unread bytes, read(n) returns min(n, bytesavailable), and peek leaves position unchanged.", source := "base/iobuffer.jl:406-456, 977-982 (read and peek bodies); read and peek contracts",
    status := .todo, prop := ``ReadAvailableAndPeekCounts, thm := none },
  { id := "iobuffer-read-write-permission-errors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})", "ensureroom_reallocate", "write(::GenericIOBuffer, ::UInt8)", "unsafe_write"],
    statement := "Writes to non-writable buffers and reads from non-readable buffers throw ArgumentError before transferring bytes.", source := "base/iobuffer.jl:344-347, 618-620, 948-963; IOBuffer read/write options",
    status := .todo, prop := ``ReadWritePermissionErrors, thm := none },
  { id := "iobuffer-maxsize-write-cap", juliaFile := "base/iobuffer.jl",
    juliaFns := ["ensureroom", "unsafe_write", "write(::GenericIOBuffer, ::UInt8)"],
    statement := "Every successful write stays within the configured maxsize boundary, including when the backing storage is larger.", source := "base/iobuffer.jl:55-69, 609-610, 910-920, 949-963 (maxsize and write bounds)",
    status := .todo, prop := ``MaxsizeCapsWrites, thm := none },
  { id := "iobuffer-position-bounds", juliaFile := "base/iobuffer.jl",
    juliaFns := ["position", "seek", "seekend", "skip", "mark", "reset", "truncate"],
    statement := "Successful seek, skip, mark/reset and truncate operations keep the zero-based position within the logical buffer size; resetting without a mark throws ArgumentError.", source := "base/iobuffer.jl:69-93, 475-593; mark/reset contracts in base/io.jl",
    status := .todo, prop := ``PositionBoundsAfterOperations, thm := none },
  { id := "iobuffer-available-byte-count", juliaFile := "base/iobuffer.jl",
    juliaFns := ["bytesavailable(::GenericIOBuffer)"],
    statement := "bytesavailable equals the number of unread bytes (the slice from ptr through size) for every physically valid retained span, including compacted pipes, any permissions and any maxsize.",
    source := "bytesavailable docstring base/io.jl:132-144; base/iobuffer.jl:55-71,466-467",
    status := .proven, prop := ``Round17.AvailableByteCount, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobufferAvailableByteCount_proven },
  { id := "iobuffer-eof-unread-equivalence", juliaFile := "base/iobuffer.jl",
    juliaFns := ["eof(::GenericIOBuffer)"],
    statement := "eof is true exactly when no unread byte remains, for every physically valid retained span.",
    source := "eof docstring base/io.jl:209-215; base/iobuffer.jl:55-71,691",
    status := .proven, prop := ``Round17.EofUnreadEquivalence, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobufferEofUnreadEquivalence_proven },
  { id := "iobuffer-filesize-byte-count", juliaFile := "base/iobuffer.jl",
    juliaFns := ["filesize(::GenericIOBuffer)"],
    statement := "filesize counts all retained logical bytes of a seekable buffer and the unread bytes of a pipe.",
    source := "base/iobuffer.jl:55-71,463-467",
    status := .proven, prop := ``Round17.FilesizeByteCount, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobufferFilesizeByteCount_proven },
{ id := "iobuffers-seek-v2", juliaFile := "base/iobuffer.jl",
    juliaFns := ["seek(::GenericIOBuffer, ::Integer)"],
    statement := "Seeking clamps a seekable buffer to its endpoints and permits a nonseekable buffer to seek exactly to a retained live mark, with the original error cases.",
    source := "base/iobuffer.jl:495-523", status := .proven,
    prop := ``Archive20261102Round17.SeekSpecReachable, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobuffersSeekV2_proven },
  { id := "iobuffers-skip-v2", juliaFile := "base/iobuffer.jl",
    juliaFns := ["skip(::GenericIOBuffer, ::Integer)"],
    statement := "Nonnegative skip advances up to the end; negative skip moves backward with seekable clamping or the original nonseekable mark/error classification.",
    source := "base/iobuffer.jl:475-493,512-523", status := .proven,
    prop := ``Archive20261102Round17.SkipSpecReachable, thm := some ``JuliaLean.ChatGPT.Batch6.Group1.IobuffersSkipV2_proven }
]

end JuliaLean.Proofs.base.iobuffer
