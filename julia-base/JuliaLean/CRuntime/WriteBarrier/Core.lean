import JuliaLean.Registry.Types
import JuliaLean.CRuntime.Memory
import JuliaLean.CRuntime.Types

/-!
Julia stock GC, pinned at `bbfa0ce4150ea33f2532198cabcf319a49399360`.
Identifiers parameterize arbitrary finite object graphs, threads, slots and
pages. The source programs expose loads, RMWs, array writes, locks, stores and
queue calls separately. `JL_NOTSAFEPOINT` permits a thread to stop only at
its caller boundary.

Scalar callers must use a valid owner/slot and a null or heap pointer, with the
barrier immediately before the store (`src/gc-interface.h:323-327`). Immutable
payload callers must use a boxed immutable source and the same destination
layout (`src/gc-interface.h:340-345`). Genericmemory callers must provide spans
of the same element type (`src/gc-interface.h:355-366`). Source observations
are explicit and are checked against a C11 memory candidate.

Datatype and layout tables are immutable `Config` inputs; their metadata
lookups are outside the emitted memory events. Arraylist growth exposes
both malloc/realloc outcomes and each capacity, length and item store.
Allocation identity and byte addressing remain external primitives.
-/

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.Registry
open JuliaLean.CRuntime.Memory

/-- `bbfa0ce4150 src/julia_internal.h:422-429`: the four GC-bit states. -/
inductive GCBits where
  | clean | marked | old | oldMarked
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/julia_internal.h:422-428`: bit zero. -/
def GCBits.markedBit : GCBits → Bool
  | .marked | .oldMarked => true
  | _ => false

/-- `bbfa0ce4150 src/julia_internal.h:424,428`: bit one. -/
def GCBits.oldBit : GCBits → Bool
  | .old | .oldMarked => true
  | _ => false

/-- `bbfa0ce4150 src/gc-stock.c:1679`: `header & ~GC_OLD`. -/
def GCBits.clearOld : GCBits → GCBits
  | .old => .clean
  | .oldMarked => .marked
  | bits => bits

/-- `bbfa0ce4150 src/gc-stock.c:245-263`: mark without resetting age. -/
def GCBits.setMark : GCBits → GCBits
  | .old | .oldMarked => .oldMarked
  | _ => .marked

/-- `bbfa0ce4150 src/julia.h:171-187`,
`src/julia_internal.h:422-429`: one complete header RMW location. -/
structure Header where
  gc : GCBits
  inImage : Bool := false
  imageRemset : Bool := false
  tag : Nat := 0
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-wb-stock.h:55,86,114`: `bits.in_image == 1`. -/
def Header.imageNotRemset (h : Header) : Bool := h.inImage && !h.imageRemset

/-- `bbfa0ce4150 src/gc-stock.c:1679`: preserve the tag and image bits. -/
def Header.clearOld (h : Header) : Header := { h with gc := h.gc.clearOld }

/-- `bbfa0ce4150 src/gc-stock.c:1686`: set the permanent-remset bit. -/
def Header.setImageRemset (h : Header) : Header := { h with imageRemset := true }

/-- `bbfa0ce4150 src/gc-stock.c:248-263`: reset-age and ordinary marks. -/
def Header.setMark (h : Header) (resetAge : Bool) : Header :=
  { h with gc := if resetAge then .marked else h.gc.setMark }

/-- `bbfa0ce4150 src/gc-stock.c:1726-1740,2753-2800`: descriptors. -/
inductive Descriptor where
  | bits8 | bits16 | bits32 | foreign
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:2506-2517,2661-2800`: scan dispatch. -/
inductive LayoutKind where
  | object | simpleVector | boxedMemory | inlineMemory | stringOwnedMemory
  | weakReference | foreign
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1716-1742,2694-2737,2746-2800`:
offsets/strides use pointer-sized words. Foreign layouts supply their strong
offsets through the mark callback; weak references have no strong offsets. -/
structure Layout where
  kind : LayoutKind := .object
  descriptor : Descriptor := .bits8
  sizeWords : Nat
  npointers : Nat := 0
  pointerOffsets : List Nat
  length : Nat := 1
  firstPtr : Option Nat := none
  symbolElements : Bool := false
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:2694-2737,2746-2800`: strong slots. -/
def Layout.traceOffsets (l : Layout) : List Nat :=
  match l.kind with
  | .weakReference => []
  | .boxedMemory | .simpleVector => List.range l.length
  | .inlineMemory => (List.range l.length).flatMap fun i =>
      l.pointerOffsets.map fun offset => i * l.sizeWords + offset
  | .stringOwnedMemory => [0]
  | _ => l.pointerOffsets

/-- `bbfa0ce4150 src/julia.h:171-189`, `src/gc-stock.h:99-144`,
`src/gc-stock.c:1716-1742,2661-2800`: finite graph parameters. -/
structure Config extends JuliaLean.CRuntime.Config where
  slots : Nat
  datatypes : Nat
  genericMemories : Nat
  layout : Fin objects → Layout
  datatypeLayout : Fin datatypes → Layout
  memoryDatatype : Fin genericMemories → Fin datatypes
  memoryObject : Fin genericMemories → Fin objects
  memoryOwner : Fin genericMemories → Fin objects
  memoryDataAddress : Fin genericMemories → Nat
  memoryLength : Fin genericMemories → Nat
  field : Fin objects → Nat → Option (Fin slots)
  owner : Fin slots → Fin objects
  slotAtomic : Fin slots → Bool
  page : Fin objects → Option (Fin pages)
  immutable : Fin objects → Bool
  slotAtWord : Nat → Option (Fin slots) := fun _ => none

abbrev ObjectId (c : Config) := Fin c.objects
abbrev ThreadId (c : Config) := Fin c.threads
abbrev SlotId (c : Config) := Fin c.slots
abbrev PageId (c : Config) := Fin c.pages
abbrev AllocationId (c : Config) := Fin c.arrays
abbrev DatatypeId (c : Config) := Fin c.datatypes
abbrev GenericMemoryId (c : Config) := Fin c.genericMemories

/-- `bbfa0ce4150 src/support/arraylist.h:16-21`: inline `_space`
and allocator-returned backing pointers. -/
inductive ArrayStorage (c : Config) where
  | inline | heap (allocation : AllocationId c)
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.h:105-135`,
`src/gc-stock.c:297-308,1065-1080`: relevant page age metadata. -/
structure PageAge where
  hasMarked : Bool := false
  hasYoung : Bool := true
  nold : BitVec 16 := 0
  prevNold : BitVec 16 := 0
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/support/arraylist.c:40-70`,
`src/gc-stock.c:1681-1682`: array storage, active length, capacity, counter. -/
structure Remset (c : Config) where
  items : Nat → Option (ObjectId c)
  len : Nat := 0
  capacity : Nat := 29
  nptr : BitVec 32 := 0
  storage : ArrayStorage c := .inline

/-- `bbfa0ce4150 src/support/arraylist.c:40-70`: grow and push PCs. -/
inductive ArrayListPC where
  | loadLength | newLength | loadMax | testMax | loadStorage
  | inlineAllocate | inlineResult | copyInline
  | heapInitialize | heapZero | heapTest | heapDouble | heapAllocate | heapResult
  | storeStorage | storeMax | storeLength | pushLength | pushStorage | pushItem
  | finished | undefinedAccess
  deriving Repr, DecidableEq

inductive ArrayTarget where
  | tls | image
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/support/arraylist.c:42-70`: C local registers.
`newlen` and doubling use explicit unsigned target-word wrapping. -/
structure ArrayListState (c : Config) where
  target : ArrayTarget := .tls
  pc : ArrayListPC := .loadLength
  n : Nat := 1
  len : Nat := 0
  newlen : Nat := 0
  max : Nat := 0
  nm : Nat := 0
  storage : ArrayStorage c := .inline
  result : Option (AllocationId c) := none
  pushLen : Nat := 0
  pushBacking : ArrayStorage c := .inline

def wordWrap (c : Config) (n : Nat) : Nat := n % (2 ^ c.wordBits)

/-- `bbfa0ce4150 src/gc-stock.h:97`, `src/gc-stock.c:2475-2485`:
the remset tag suppresses page-metadata updates during scanning. -/
structure MarkWork (c : Config) where
  object : ObjectId c
  remset : Bool := false
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:2055-2057,2073-2075,2130-2132,
2207-2209`: chunk queue payload. -/
structure MarkChunk (c : Config) where
  object : ObjectId c
  «begin» : Nat
  end_ : Nat
  stride : Nat
  offsets : List Nat
  nptr : Nat
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:3383-3407,3458,3685-3700`: phases. -/
inductive Phase where
  | mutating | stopping | drain | roots | marking | beforeSweep | sweeping | reset | resume
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1671-1702,1812-1826,3092-3115,
3685-3700`, `src/gc-stock.h:99-144`: boundary-state heap projection.
`previousFull` controls permanent image-remset scanning independently of
the kind of the current collection. -/
structure Heap (c : Config) where
  header : ObjectId c → Header
  pointers : SlotId c → Option (ObjectId c)
  allocated : ObjectId c → Bool
  roots : List (ObjectId c)
  remset : ThreadId c → Remset c
  imageRemset : Remset c
  markerQueue : ThreadId c → List (MarkWork c)
  chunkQueue : ThreadId c → List (MarkChunk c)
  pageAge : PageId c → PageAge
  phase : Phase := .mutating
  full : Bool := false
  previousFull : Bool := false
  resetAge : Bool := false

/-- `bbfa0ce4150 src/gc-stock.c:1679-1694,1816-1824,3094-3104`,
`src/julia.h:1426-1437`: source memory locations. -/
inductive Location (c : Config) where
  | header (object : ObjectId c)
  | pointer (slot : SlotId c)
  | remsetLen (thread : ThreadId c)
  | remsetCapacity (thread : ThreadId c)
  | remsetItem (thread : ThreadId c) (index : Nat)
  | remsetNptr (thread : ThreadId c)
  | remsetStorage (thread : ThreadId c)
  | imageLen | imageCapacity | imageItem (index : Nat) | imageStorage | imageLock
  | pageNold (page : PageId c)
  | pageHasMarked (page : PageId c)
  | pageHasYoung (page : PageId c)
  deriving Repr, DecidableEq

def declaredAccessClass (c : Config) : Location c → AccessClass
  | .header _ => .ordinary
  | .pointer slot => if c.slotAtomic slot then .atomic else .ordinary
  | _ => .ordinary

/-- `bbfa0ce4150 src/julia.h:171-189`,
`src/gc-stock.c:1679-1694,1816-1824,3094-3104`: typed memory values. -/
inductive Value (c : Config) where
  | header (value : Header)
  | pointer (value : Option (ObjectId c))
  | number (value : Nat)
  | counter (value : BitVec 32)
  | flag (value : Bool)
  | storage (value : ArrayStorage c)
  deriving Repr, DecidableEq

abbrev MemoryAction (c : Config) := Action (Location c) (Value c)

/-- `bbfa0ce4150 src/gc-interface.h:323-345,355-366`: caller kinds. -/
inductive CallerKind where
  | scalar | object | multi | copyBoxed | copyInline | moduleUsings
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/julia.h:1426-1469`,
`src/genericmemory.c:222-250`, `src/gc-wb-stock.h:48-130`:
caller arguments before address, layout and span derivation. -/
structure Call (c : Config) where
  kind : CallerKind
  parent : ObjectId c
  source : Option (ObjectId c) := none
  scalarSlot : Option (SlotId c) := none
  scalarValue : Option (ObjectId c) := none
  storeOrder : Order := .release
  scalarAtomic : Bool := true
  multiCopyPairs : List (SlotId c × SlotId c) := []
  multiScanSlots : List (SlotId c) := []
  sourceAddress : Nat := 0
  destinationAddress : Nat := 0
  elementCount : Nat := 0
  sourceMemory : Option (GenericMemoryId c) := none
  destinationMemory : Option (GenericMemoryId c) := none

/-- `bbfa0ce4150 src/julia.h:1429-1437`: overlapping-copy direction. -/
def memmoveOrder {α : Type} (source destination : Nat) (pairs : List α) : List α :=
  if destination < source ∨ destination > source + pairs.length then pairs else pairs.reverse

/-- `bbfa0ce4150 src/genericmemory.c:226-246`,
`src/gc-wb-stock.h:78-130`: boxed copies have one pointer word per element;
inline layout comes from the destination genericmemory datatype. -/
def Call.copyLayout {c : Config} (call : Call c) : Layout :=
  match call.kind with
  | .copyBoxed => { kind := .boxedMemory, sizeWords := 1, npointers := 1, pointerOffsets := [0] }
  | .copyInline =>
      match call.destinationMemory with
      | some memory => c.datatypeLayout (c.memoryDatatype memory)
      | none => { sizeWords := 0, pointerOffsets := [] }
  | _ => { sizeWords := 0, pointerOffsets := [] }

def Config.datatypeLayoutsValid (c : Config) : Prop :=
  ∀ datatype, (c.datatypeLayout datatype).pointerOffsets.length =
    (c.datatypeLayout datatype).npointers

/-- `bbfa0ce4150 src/genericmemory.c:222-250`: successful C entry into
the boxed or inline barrier after the source/destination datatype identity
check. Every modeled call field is fixed by the C arguments and destination
metadata. -/
inductive GenericMemoryEntry (c : Config) : Call c → Prop where
  | boxed (source destination : GenericMemoryId c) (sourceAddress destinationAddress n : Nat)
      (sameType : c.memoryDatatype source = c.memoryDatatype destination)
      (boxed : (c.datatypeLayout (c.memoryDatatype destination)).kind = .boxedMemory) :
      GenericMemoryEntry c
        { kind := .copyBoxed
          parent := c.memoryOwner destination
          source := some (c.memoryObject source)
          sourceAddress := sourceAddress
          destinationAddress := destinationAddress
          elementCount := n
          sourceMemory := some source
          destinationMemory := some destination }
  | inline (source destination : GenericMemoryId c) (sourceAddress destinationAddress n : Nat)
      (sameType : c.memoryDatatype source = c.memoryDatatype destination)
      (inline : (c.datatypeLayout (c.memoryDatatype destination)).kind = .inlineMemory)
      (pointers : (c.datatypeLayout (c.memoryDatatype destination)).firstPtr.isSome = true) :
      GenericMemoryEntry c
        { kind := .copyInline
          parent := c.memoryOwner destination
          source := some (c.memoryObject source)
          sourceAddress := sourceAddress
          destinationAddress := destinationAddress
          elementCount := n
          sourceMemory := some source
          destinationMemory := some destination }

def Call.copyStride {c : Config} (call : Call c) : Nat :=
  call.copyLayout.sizeWords

def Call.copyPointerOffsets {c : Config} (call : Call c) : List Nat :=
  call.copyLayout.pointerOffsets

/-- `bbfa0ce4150 src/gc-wb-stock.h:82,110`: the `size_t` word count
passed to `memmove_refs`, including target-width multiplication wrapping. -/
def Call.copyWordCount {c : Config} (call : Call c) : Nat :=
  wordWrap c (call.elementCount * call.copyStride)

def Call.copyWordIndices {c : Config} (call : Call c) : List Nat :=
  memmoveOrder call.sourceAddress call.destinationAddress (List.range call.copyWordCount)

/-- `bbfa0ce4150 src/julia.h:1426-1437`: source and destination slots in
the exact forward or reverse `memmove_refs` loop order. -/
def Call.bulkCopyPairs {c : Config} (call : Call c) : List (SlotId c × SlotId c) :=
  call.copyWordIndices.filterMap fun index =>
    match c.slotAtWord (call.sourceAddress + index),
        c.slotAtWord (call.destinationAddress + index) with
    | some source, some destination => some (source, destination)
    | _, _ => none

/-- `bbfa0ce4150 src/gc-wb-stock.h:90-96,118-127`: destination pointer
fields in the nested source-loop order. -/
def Call.bulkScanSlots {c : Config} (call : Call c) : List (SlotId c) :=
  (List.range call.elementCount).flatMap fun element =>
    call.copyPointerOffsets.filterMap fun offset =>
      c.slotAtWord (call.destinationAddress + element * call.copyStride + offset)

def Call.copyPairs {c : Config} (call : Call c) : List (SlotId c × SlotId c) :=
  match call.kind with
  | .multi => call.multiCopyPairs
  | .copyBoxed | .copyInline => call.bulkCopyPairs
  | _ => []

def Call.scanSlots {c : Config} (call : Call c) : List (SlotId c) :=
  match call.kind with
  | .multi => call.multiScanSlots
  | .copyBoxed | .copyInline => call.bulkScanSlots
  | _ => []

/-- `bbfa0ce4150 src/gc-wb-stock.h:85,113`: the target-width value used
by the four-pointer branch. -/
def Call.scanPointerCount {c : Config} (call : Call c) : Nat :=
  match call.kind with
  | .copyBoxed => call.elementCount
  | .copyInline => wordWrap c (call.elementCount * call.copyPointerOffsets.length)
  | _ => 0

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1671-1748`, `src/julia.h:1426-1469`: source-order PCs. -/
inductive MutatorPC where
  | outside | parentGC | scalarNull | scalarImage | scalarChildGC
  | objectGC | multiImage | multiSourceGC | multiLayout | multiSlot | multiChildGC
  | moduleImage | moduleChildGC
  | copyLoad | copyStore | copyEmpty | copyParentGC | copySmall | copyImage
  | copyScanSlot | copyScanChildGC
  | rootFetchAnd | rootOldBranch | rootLengthLoad | rootCapacity
  | rootGrow | rootLengthStore | rootItemStore | rootNptrLoad | rootNptrStore
  | rootImageBranch | rootImageFetchOr | rootImageOldBranch
  | imageLock | imageLengthLoad | imageCapacity | imageGrow
  | imageLengthStore | imageItemStore | imageUnlock
  | returnBarrier | scalarStore | payloadLoad | payloadStore
  | undefinedArithmetic | undefinedAccess
  | arrayList
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1673-1748`,
`src/gc-wb-stock.h:48-130`: local registers. -/
structure Mutator (c : Config) where
  call : Call c
  pc : MutatorPC := .outside
  returnPC : MutatorPC := .returnBarrier
  readHeader : Header := { gc := .clean }
  oldHeader : Header := { gc := .clean }
  pointer : Option (ObjectId c) := none
  copyIndex : Nat := 0
  scanIndex : Nat := 0
  arrayIndex : Nat := 0
  count : BitVec 32 := 0
  capacity : Nat := 0
  support : List Nat := []
  arrayCall : ArrayListState c := {}

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1679-1694`: one interleavable source instruction. Allocation
calls retain a separate control step before length and element writes. -/
structure Instruction (c : Config) where
  next : Mutator c
  action : Option (MemoryAction c) := none
  growArray : Bool := false

/-- `bbfa0ce4150 src/gc-stock.c:1679,1686`,
`src/gc-wb-stock.h:91,122`: candidate load/RMW observations. -/
structure Observation (c : Config) where
  header : Header := { gc := .clean }
  pointer : Option (ObjectId c) := none
  number : Nat := 0
  counter : BitVec 32 := 0
  storage : ArrayStorage c := .inline
  allocation : Option (AllocationId c) := none

def ArrayTarget.lengthLocation {c : Config} (target : ArrayTarget) (tid : ThreadId c) : Location c :=
  match target with | .tls => .remsetLen tid | .image => .imageLen
def ArrayTarget.maxLocation {c : Config} (target : ArrayTarget) (tid : ThreadId c) : Location c :=
  match target with | .tls => .remsetCapacity tid | .image => .imageCapacity
def ArrayTarget.storageLocation {c : Config} (target : ArrayTarget) (tid : ThreadId c) : Location c :=
  match target with | .tls => .remsetStorage tid | .image => .imageStorage
def ArrayTarget.itemLocation {c : Config} (target : ArrayTarget) (tid : ThreadId c) (index : Nat) : Location c :=
  match target with | .tls => .remsetItem tid index | .image => .imageItem index

structure ArrayListInstruction (c : Config) where
  next : ArrayListState c
  action : Option (MemoryAction c) := none
  allocate : Bool := false
  copyLength : Option Nat := none

/-- `bbfa0ce4150 src/support/arraylist.c:40-70`: each source statement.
NULL returns without changing the array. `push` still reloads len/items
and writes items[len-1]. The memcpy preserves exactly the old len logical
entries; allocation and byte addressing remain external primitives. -/
def arrayListInstruction (c : Config) (tid : ThreadId c) (parent : ObjectId c)
    (s : ArrayListState c) (obs : Observation c) : ArrayListInstruction c :=
  let advance pc := { next := { s with pc := pc } : ArrayListInstruction c }
  match s.pc with
  | .loadLength =>
      { next := { s with pc := .newLength, len := obs.number }
        action := some (.plainLoad (s.target.lengthLocation tid) (.number obs.number)) }
  | .newLength => { next := { s with pc := .loadMax, newlen := wordWrap c (s.len + s.n) } }
  | .loadMax =>
      { next := { s with pc := .testMax, max := obs.number }
        action := some (.plainLoad (s.target.maxLocation tid) (.number obs.number)) }
  | .testMax => advance (if s.newlen > s.max then .loadStorage else .storeLength)
  | .loadStorage =>
      { next := { s with
          storage := obs.storage
          pc := if obs.storage = .inline then .inlineAllocate else .heapInitialize }
        action := some (.plainLoad (s.target.storageLocation tid) (.storage obs.storage)) }
  | .inlineAllocate =>
      { next := { s with pc := .inlineResult, result := obs.allocation }, allocate := true }
  | .inlineResult => advance (if s.result.isNone then .pushLength else .copyInline)
  | .copyInline => { next := { s with pc := .storeStorage }, copyLength := some s.len }
  | .heapInitialize => { next := { s with pc := .heapZero, nm := wordWrap c (s.max * 2) } }
  | .heapZero => { next := { s with pc := .heapTest, nm := if s.nm = 0 then 1 else s.nm } }
  | .heapTest => advance (if s.newlen > s.nm then .heapDouble else .heapAllocate)
  | .heapDouble => { next := { s with pc := .heapTest, nm := wordWrap c (s.nm * 2) } }
  | .heapAllocate =>
      { next := { s with pc := .heapResult, result := obs.allocation }, allocate := true }
  | .heapResult => advance (if s.result.isNone then .pushLength else .storeStorage)
  | .storeStorage =>
      match s.result with
      | none => advance .undefinedAccess
      | some allocation =>
          { next := { s with pc := .storeMax }
            action := some (.plainStore (s.target.storageLocation tid) (.storage (.heap allocation))) }
  | .storeMax =>
      { next := { s with pc := .storeLength }
        action := some (.plainStore (s.target.maxLocation tid)
          (.number (if s.storage = .inline then s.newlen else s.nm))) }
  | .storeLength =>
      { next := { s with pc := .pushLength }
        action := some (.plainStore (s.target.lengthLocation tid) (.number s.newlen)) }
  | .pushLength =>
      { next := { s with
          pushLen := obs.number
          pc := if obs.number = 0 then .undefinedAccess else .pushStorage }
        action := some (.plainLoad (s.target.lengthLocation tid) (.number obs.number)) }
  | .pushStorage =>
      { next := { s with pc := .pushItem, pushBacking := obs.storage }
        action := some (.plainLoad (s.target.storageLocation tid) (.storage obs.storage)) }
  | .pushItem =>
      if s.pushLen = 0 then advance .undefinedAccess else
      { next := { s with pc := .finished }
        action := some (.plainStore (s.target.itemLocation tid (s.pushLen - 1)) (.pointer (some parent))) }
  | .finished => advance .finished
  | .undefinedAccess => advance .undefinedAccess

/-- Logical effects of the stores in `src/support/arraylist.c:50-70`.
The external memcpy retains old entries at their logical indices. -/
def arrayListEffect {c : Config} (array : Remset c) (s : ArrayListState c)
    (parent : ObjectId c) : Remset c :=
  match s.pc with
  | .storeStorage =>
      match s.result with
      | none => array
      | some allocation => { array with storage := .heap allocation }
  | .storeMax => { array with capacity := if s.storage = .inline then s.newlen else s.nm }
  | .storeLength => { array with len := s.newlen }
  | .pushItem =>
      if s.pushLen = 0 then array else
      { array with items := fun index =>
          if index = s.pushLen - 1 then some parent else array.items index }
  | _ => array

structure ArrayExecutionState (c : Config) where
  frame : ArrayListState c
  array : Remset c

def arrayObservation {c : Config} (s : ArrayExecutionState c) (obs : Observation c) : Prop :=
  match s.frame.pc with
  | .loadLength | .pushLength => obs.number = s.array.len
  | .loadMax => obs.number = s.array.capacity
  | .loadStorage | .pushStorage => obs.storage = s.array.storage
  | _ => True

def arrayStep (c : Config) (tid : ThreadId c) (parent : ObjectId c)
    (s : ArrayExecutionState c) (obs : Observation c) : ArrayExecutionState c :=
  { frame := (arrayListInstruction c tid parent s.frame obs).next
    array := arrayListEffect s.array s.frame parent }

def replayArray (c : Config) (tid : ThreadId c) (parent : ObjectId c) :
    List (Observation c) → ArrayExecutionState c → ArrayExecutionState c
  | [], s => s
  | obs :: rest, s => replayArray c tid parent rest (arrayStep c tid parent s obs)

def arrayTraceObserves (c : Config) (tid : ThreadId c) (parent : ObjectId c) :
    List (Observation c) → ArrayExecutionState c → Prop
  | [], _ => True
  | obs :: rest, s => arrayObservation s obs ∧
      arrayTraceObserves c tid parent rest (arrayStep c tid parent s obs)

def arrayTraceActions (c : Config) (tid : ThreadId c) (parent : ObjectId c) :
    List (Observation c) → ArrayExecutionState c → List (MemoryAction c)
  | [], _ => []
  | obs :: rest, s => (arrayListInstruction c tid parent s.frame obs).action.toList ++
      arrayTraceActions c tid parent rest (arrayStep c tid parent s obs)

inductive ArrayRun (c : Config) (tid : ThreadId c) (parent : ObjectId c)
    (initial : ArrayExecutionState c) : ArrayExecutionState c → Prop where
  | initial : ArrayRun c tid parent initial initial
  | next {s} : ArrayRun c tid parent initial s → (obs : Observation c) → arrayObservation s obs →
      ArrayRun c tid parent initial (arrayStep c tid parent s obs)

/-- Allocation outcomes and representable size arithmetic, separately
from caller validity. The source transition relation retains NULL paths. -/
def AllocationStepSuccess {c : Config} (s : ArrayListState c) (obs : Observation c) : Prop :=
  (s.pc ∈ [.inlineAllocate, .heapAllocate] → obs.allocation.isSome = true) ∧
  (s.pc = .newLength → s.len + s.n < 2 ^ c.wordBits)

def arrayTraceSuccess (c : Config) (tid : ThreadId c) (parent : ObjectId c) :
    List (Observation c) → ArrayExecutionState c → Prop
  | [], _ => True
  | obs :: rest, s => AllocationStepSuccess s.frame obs ∧
      arrayTraceSuccess c tid parent rest (arrayStep c tid parent s obs)

def ArrayCursor {c : Config} (s : ArrayExecutionState c) (published : Nat) : Prop :=
  s.frame.n = 1 ∧
  match s.frame.pc with
  | .loadLength => s.array.len = published
  | .newLength => s.array.len = published ∧ s.frame.len = published
  | .inlineResult | .copyInline | .heapResult | .storeStorage | .storeMax =>
      s.array.len = published ∧ s.frame.len = published ∧ s.frame.newlen = published + 1 ∧
      s.frame.result.isSome = true
  | .pushLength =>
      s.array.len = published + 1 ∧ s.frame.len = published ∧ s.frame.newlen = published + 1
  | .pushStorage | .pushItem =>
      s.array.len = published + 1 ∧ s.frame.len = published ∧ s.frame.newlen = published + 1 ∧
      s.frame.pushLen = published + 1
  | .finished => s.array.len = published
  | .undefinedAccess => False
  | _ => s.array.len = published ∧ s.frame.len = published ∧ s.frame.newlen = published + 1

def arrayPublished {c : Config} (s : ArrayListState c) (published : Nat) : Nat :=
  if s.pc = .pushItem then s.pushLen else published

theorem arrayCursor_step {c : Config} (tid : ThreadId c) (parent : ObjectId c)
    (s : ArrayExecutionState c) (obs : Observation c) (published : Nat)
    (cursor : ArrayCursor s published) (observed : arrayObservation s obs)
    (successful : AllocationStepSuccess s.frame obs) :
    ArrayCursor (arrayStep c tid parent s obs) (arrayPublished s.frame published) := by
  have wrap : s.frame.pc = .newLength → wordWrap c (s.frame.len + s.frame.n) = s.frame.len + s.frame.n := by
    intro pc
    exact Nat.mod_eq_of_lt (successful.2 pc)
  cases pc : s.frame.pc <;> cases result : s.frame.result <;>
    simp_all [ArrayCursor, arrayStep, arrayPublished, arrayObservation, arrayListEffect,
      arrayListInstruction, AllocationStepSuccess]
  all_goals repeat' (split at * <;> try simp_all)
  all_goals omega

def arrayMutatorPC (target : ArrayTarget) (pc : ArrayListPC) : MutatorPC :=
  match pc, target with
  | .loadLength, .tls => .rootLengthLoad
  | .loadMax, .tls => .rootCapacity
  | .loadStorage, .tls => .rootGrow
  | .storeLength, .tls => .rootLengthStore
  | .pushItem, .tls => .rootItemStore
  | .finished, .tls => .rootNptrLoad
  | .loadLength, .image => .imageLengthLoad
  | .loadMax, .image => .imageCapacity
  | .loadStorage, .image => .imageGrow
  | .storeLength, .image => .imageLengthStore
  | .pushItem, .image => .imageItemStore
  | .finished, .image => .imageUnlock
  | .undefinedAccess, _ => .undefinedAccess
  | _, _ => .arrayList

def arrayMutatorInstruction (c : Config) (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) : Instruction c :=
  let instruction := arrayListInstruction c tid m.call.parent m.arrayCall obs
  { next := { m with
      arrayCall := instruction.next
      pc := arrayMutatorPC instruction.next.target instruction.next.pc
      arrayIndex := if m.arrayCall.pc = .pushLength then obs.number - 1 else m.arrayIndex }
    action := instruction.action
    growArray := instruction.allocate }

def inArrayCode : MutatorPC → Bool
  | .rootLengthLoad | .rootCapacity | .rootGrow | .rootLengthStore | .rootItemStore
  | .imageLengthLoad | .imageCapacity | .imageGrow | .imageLengthStore | .imageItemStore
  | .arrayList => true
  | _ => false

def Mutator.allocationSuccess {c : Config} (m : Mutator c) (obs : Observation c) : Prop :=
  inArrayCode m.pc = true → AllocationStepSuccess m.arrayCall obs

theorem arrayList_target {c : Config} (tid : ThreadId c) (parent : ObjectId c)
    (s : ArrayListState c) (obs : Observation c) :
    (arrayListInstruction c tid parent s obs).next.target = s.target := by
  cases pc : s.pc <;> simp [arrayListInstruction, pc]
  all_goals repeat' (split <;> try simp_all)

theorem arrayItem_pc (target : ArrayTarget) (pc : ArrayListPC) :
    arrayMutatorPC target pc = .rootItemStore ↔ target = .tls ∧ pc = .pushItem := by
  cases target <;> cases pc <;> simp [arrayMutatorPC]

def advance {c : Config} (m : Mutator c) (pc : MutatorPC) : Instruction c :=
  ⟨{ m with pc := pc }, none, false⟩

def emit {c : Config} (m : Mutator c) (pc : MutatorPC)
    (a : MemoryAction c) : Instruction c := ⟨{ m with pc := pc }, some a, false⟩

def readHeader {c : Config} (m : Mutator c) (pc : MutatorPC)
    (obj : ObjectId c) (obs : Observation c) : Instruction c :=
  ⟨{ m with pc := pc, readHeader := obs.header },
   some (.plainLoad (.header obj) (.header obs.header)), false⟩

def readPointer {c : Config} (m : Mutator c) (pc : MutatorPC)
    (slot : SlotId c) (obs : Observation c) (atomic : Bool) : Instruction c :=
  ⟨{ m with pc := pc, pointer := obs.pointer },
   some (if atomic then .load (.pointer slot) .relaxed (.pointer obs.pointer)
         else .plainLoad (.pointer slot) (.pointer obs.pointer)), false⟩

def rootCall {c : Config} (m : Mutator c) (returnPC : MutatorPC) : Instruction c :=
  advance { m with returnPC := returnPC } .rootFetchAnd

def afterBarrier {c : Config} (m : Mutator c) : MutatorPC :=
  match m.call.kind with
  | .scalar => .scalarStore
  | .multi | .object => .payloadLoad
  | _ => .outside

def afterParentGC (kind : CallerKind) : MutatorPC :=
  match kind with
  | .multi => .multiImage
  | .moduleUsings => .moduleImage
  | _ => .scalarNull

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1671-1748`, `src/support/arraylist.c:40-70`,
`src/julia.h:1426-1437,1458-1469`, `src/genericmemory.c:222-250`:
one scalar, immutable-payload or fused-copy source instruction. Header
bitfield reads remain plain reads; relaxed RMWs and release pointer stores
retain their exact memory orders. Arraylist growth is an external allocation
call, followed by distinct active-length and item writes. -/
def mutatorInstruction (c : Config) (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) : Instruction c :=
  let parent := m.call.parent
  match m.pc with
  | .outside => advance m .outside
  | .parentGC =>
      let i := readHeader m .returnBarrier parent obs
      { i with next := { i.next with pc :=
          if obs.header.gc = .oldMarked then afterParentGC m.call.kind else .returnBarrier } }
  | .scalarNull => advance m (if m.call.scalarValue.isNone then .returnBarrier else .scalarImage)
  | .scalarImage =>
      let i := readHeader m .scalarChildGC parent obs
      { i with next := { i.next with
          pc := (if obs.header.imageNotRemset then .rootFetchAnd else .scalarChildGC)
          returnPC := .returnBarrier } }
  | .scalarChildGC =>
      match m.call.scalarValue with
      | none => advance m .returnBarrier
      | some child =>
          let i := readHeader m .returnBarrier child obs
          { i with next := { i.next with
              pc := (if obs.header.gc.markedBit then .returnBarrier else .rootFetchAnd)
              returnPC := .returnBarrier } }
  | .objectGC =>
      let i := readHeader m .returnBarrier parent obs
      { i with next := { i.next with
          pc := (if obs.header.gc = .oldMarked then .rootFetchAnd else .returnBarrier)
          returnPC := .returnBarrier } }
  | .multiImage =>
      let i := readHeader m .multiSourceGC parent obs
      { i with next := { i.next with
          pc := (if obs.header.imageNotRemset then .rootFetchAnd else .multiSourceGC)
          returnPC := .returnBarrier } }
  | .multiSourceGC =>
      match m.call.source with
      | none => advance m .undefinedAccess
      | some source =>
          let i := readHeader m .multiLayout source obs
          { i with next := { i.next with pc := if obs.header.gc = .oldMarked then .returnBarrier else .multiLayout } }
  | .multiLayout => advance { m with scanIndex := 0 }
      (if m.call.scanSlots.isEmpty then .returnBarrier else .multiSlot)
  | .multiSlot =>
      match m.call.scanSlots[m.scanIndex]? with
      | none => advance m .returnBarrier
      | some slot => readPointer m .multiChildGC slot obs false
  | .multiChildGC =>
      match m.pointer with
      | none => advance { m with scanIndex := m.scanIndex + 1 } .multiSlot
      | some child =>
          let i := readHeader m .multiSlot child obs
          { i with next := { i.next with
              scanIndex := m.scanIndex + 1
              pc := if obs.header.gc.markedBit then .multiSlot else .objectGC } }
  | .moduleImage =>
      let i := readHeader m .moduleChildGC parent obs
      { i with next := { i.next with
          pc := (if obs.header.imageNotRemset then .rootFetchAnd else .moduleChildGC)
          returnPC := .outside } }
  | .moduleChildGC =>
      match m.call.source with
      | none => advance m .undefinedAccess
      | some source =>
          let i := readHeader m .outside source obs
          { i with next := { i.next with
              pc := (if obs.header.gc.markedBit then .outside else .rootFetchAnd)
              returnPC := .outside } }
  | .copyLoad =>
      match m.call.copyPairs[m.copyIndex]? with
      | none => advance m .copyEmpty
      | some pair => readPointer m .copyStore pair.1 obs true
  | .copyStore =>
      match m.call.copyPairs[m.copyIndex]? with
      | none => advance m .copyEmpty
      | some pair => emit { m with copyIndex := m.copyIndex + 1 } .copyLoad
          (.store (.pointer pair.2) .release (.pointer m.pointer))
  | .copyEmpty => advance m (if m.call.elementCount = 0 then .outside else .copyParentGC)
  | .copyParentGC =>
      let i := readHeader m .copySmall parent obs
      { i with next := { i.next with pc := if obs.header.gc = .oldMarked then .copySmall else .outside } }
  | .copySmall =>
      if m.call.scanPointerCount ≤ 4 then advance m .copyImage else rootCall m .outside
  | .copyImage =>
      let i := readHeader m .copyScanSlot parent obs
      { i with next := { i.next with
          pc := (if obs.header.imageNotRemset then .rootFetchAnd else .copyScanSlot)
          returnPC := .outside, scanIndex := 0 } }
  | .copyScanSlot =>
      match m.call.scanSlots[m.scanIndex]? with
      | none => advance m .outside
      | some slot => readPointer m .copyScanChildGC slot obs true
  | .copyScanChildGC =>
      match m.pointer with
      | none => advance { m with scanIndex := m.scanIndex + 1 } .copyScanSlot
      | some child =>
          let i := readHeader m .copyScanSlot child obs
          { i with next := { i.next with
              scanIndex := m.scanIndex + 1
              pc := (if obs.header.gc.markedBit then .copyScanSlot else .rootFetchAnd)
              returnPC := .outside } }
  | .rootFetchAnd =>
      ⟨{ m with pc := .rootOldBranch, oldHeader := obs.header },
       some (.rmw (.header parent) .relaxed (.header obs.header) (.header obs.header.clearOld)), false⟩
  | .rootOldBranch => advance { m with arrayCall := {} }
      (if m.oldHeader.gc.oldBit then .rootLengthLoad else m.returnPC)
  | .rootLengthLoad | .rootCapacity | .rootGrow | .rootLengthStore | .rootItemStore | .arrayList =>
      arrayMutatorInstruction c tid m obs
  | .rootNptrLoad =>
      ⟨{ m with pc := .rootNptrStore, count := obs.counter },
       some (.plainLoad (.remsetNptr tid) (.counter obs.counter)), false⟩
  | .rootNptrStore =>
      if m.count = 0x7fffffff then advance m .undefinedArithmetic else
      emit m .rootImageBranch (.plainStore (.remsetNptr tid) (.counter (m.count + 1)))
  | .rootImageBranch => advance m
      (if m.oldHeader.inImage && !m.oldHeader.imageRemset then .rootImageFetchOr else m.returnPC)
  | .rootImageFetchOr =>
      ⟨{ m with pc := .rootImageOldBranch, oldHeader := obs.header },
       some (.rmw (.header parent) .relaxed (.header obs.header) (.header obs.header.setImageRemset)), false⟩
  | .rootImageOldBranch => advance m (if m.oldHeader.imageRemset then m.returnPC else .imageLock)
  | .imageLock => emit { m with arrayCall := { target := .image } } .imageLengthLoad (.lock 0)
  | .imageLengthLoad | .imageCapacity | .imageGrow | .imageLengthStore | .imageItemStore =>
      arrayMutatorInstruction c tid m obs
  | .imageUnlock => emit m m.returnPC (.unlock 0)
  | .returnBarrier => advance { m with copyIndex := 0 } (afterBarrier m)
  | .scalarStore =>
      match m.call.scalarSlot with
      | none => advance m .undefinedAccess
      | some slot => emit m .outside
          (if m.call.scalarAtomic then .store (.pointer slot) m.call.storeOrder (.pointer m.call.scalarValue)
           else .plainStore (.pointer slot) (.pointer m.call.scalarValue))
  | .payloadLoad =>
      match m.call.copyPairs[m.copyIndex]? with
      | none => advance m .outside
      | some pair => readPointer m .payloadStore pair.1 obs true
  | .payloadStore =>
      match m.call.copyPairs[m.copyIndex]? with
      | none => advance m .outside
      | some pair => emit { m with copyIndex := m.copyIndex + 1 } .payloadLoad
          (.store (.pointer pair.2) .release (.pointer m.pointer))
  | .undefinedArithmetic => advance m .undefinedArithmetic
  | .undefinedAccess => advance m .undefinedAccess

theorem mutator_arrayInstruction {c : Config} (tid : ThreadId c)
    (m : Mutator c) (obs : Observation c) (code : inArrayCode m.pc = true) :
    mutatorInstruction c tid m obs = arrayMutatorInstruction c tid m obs := by
  cases pc : m.pc <;> simp [pc, inArrayCode] at code
  all_goals simp [mutatorInstruction, pc]

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: actual function entries. -/
def entryPC : CallerKind → MutatorPC
  | .scalar | .multi | .moduleUsings => .parentGC
  | .object => .objectGC
  | .copyBoxed | .copyInline => .copyLoad

/-- `bbfa0ce4150 src/gc-interface.h:315,327,344-366`,
`src/gc-wb-stock.h:19-130`: the no-safepoint boundary. -/
def canSafepoint (pc : MutatorPC) : Bool := if pc = .outside then true else false

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: one source instruction
extends the event array only when it performs an actual memory access.
`dependsOn` records the branch/value reads used to reach this instruction. -/
def appendInstruction {c : Config} (candidate : Candidate (Location c) (Value c))
    (thread : ThreadId c) (instruction : Instruction c) (choice : Choice)
    (dependsOn : List Nat) : Candidate (Location c) (Value c) :=
  match instruction.action with
  | none => candidate
  | some action => candidate.append
      { thread := thread.val + 1, action := action, readFrom := choice.readFrom,
        mo := choice.mo, sc := choice.sc, dependsOn := dependsOn }

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1679-1748`: a source read remains a dependency of later
instructions through its value, address, or the decision to continue this
invocation. The scheduler cannot omit those dependencies. -/
def instructionThread {c : Config} (candidate : Candidate (Location c) (Value c))
    (m : Mutator c) (instruction : Instruction c) : Mutator c :=
  { instruction.next with support :=
      if instruction.action.any (fun action => action.readValue.isSome) then
        candidate.events.size :: m.support else m.support }

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1671-1748`, `src/julia.h:1426-1469`: all finite
instruction interleavings, with arbitrary load/RMW read choices. Prefixes
may end in the middle of a no-safepoint region; collection entry may not. -/
inductive MutatorPrefix (c : Config)
    (initialCandidate : Candidate (Location c) (Value c))
    (initialThreads : ThreadId c → Mutator c) :
    Candidate (Location c) (Value c) → (ThreadId c → Mutator c) → Prop where
  | initial : MutatorPrefix c initialCandidate initialThreads initialCandidate initialThreads
  | beginCall {candidate threads} : MutatorPrefix c initialCandidate initialThreads candidate threads →
      (tid : ThreadId c) → (call : Call c) → (threads tid).pc = .outside →
      MutatorPrefix c initialCandidate initialThreads candidate
        (fun other => if other = tid then { call := call, pc := entryPC call.kind } else threads other)
  | next {candidate threads} : MutatorPrefix c initialCandidate initialThreads candidate threads →
      (tid : ThreadId c) → (obs : Observation c) → (choice : Choice) →
      MutatorPrefix c initialCandidate initialThreads
        (appendInstruction candidate tid (mutatorInstruction c tid (threads tid) obs) choice (threads tid).support)
        (fun other => if other = tid then
          instructionThread candidate (threads tid) (mutatorInstruction c tid (threads tid) obs) else threads other)

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: a scheduler selection and
its unconstrained memory observation; acceptance checks the final candidate. -/
structure MutatorSelection (c : Config) where
  tid : ThreadId c
  observation : Observation c
  choice : Choice := {}
  beginCall : Option (Call c) := none

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1671-1748`: executable source-schedule replay. -/
def replayMutators (c : Config) : List (MutatorSelection c) →
    Candidate (Location c) (Value c) × (ThreadId c → Mutator c) →
    Candidate (Location c) (Value c) × (ThreadId c → Mutator c)
  | [], state => state
  | selection :: rest, (candidate, threads) =>
      match selection.beginCall with
      | some call =>
          if (threads selection.tid).pc = .outside then replayMutators c rest
            (candidate, fun other => if other = selection.tid then { call := call, pc := entryPC call.kind }
              else threads other)
          else replayMutators c rest (candidate, threads)
      | none =>
          let instruction := mutatorInstruction c selection.tid (threads selection.tid) selection.observation
          replayMutators c rest
            (appendInstruction candidate selection.tid instruction selection.choice (threads selection.tid).support,
             fun other => if other = selection.tid then instructionThread candidate (threads selection.tid) instruction
               else threads other)

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: every replay is a source
history, for all schedule lengths, thread choices, and observed values. -/
theorem replayMutators_prefix (c : Config) (schedule : List (MutatorSelection c))
    (initialCandidate : Candidate (Location c) (Value c))
    (initialThreads : ThreadId c → Mutator c) :
    MutatorPrefix c initialCandidate initialThreads
      (replayMutators c schedule (initialCandidate, initialThreads)).1
      (replayMutators c schedule (initialCandidate, initialThreads)).2 := by
  have go : ∀ schedule candidate threads,
      MutatorPrefix c initialCandidate initialThreads candidate threads →
      MutatorPrefix c initialCandidate initialThreads
        (replayMutators c schedule (candidate, threads)).1
        (replayMutators c schedule (candidate, threads)).2 := by
    intro schedule
    induction schedule with
    | nil => intro candidate threads history; exact history
    | cons selection rest ih =>
        intro candidate threads history
        cases startCase : selection.beginCall with
        | none =>
            simpa [replayMutators, startCase] using
              ih _ _ (MutatorPrefix.next history selection.tid selection.observation selection.choice)
        | some call =>
            by_cases outside : (threads selection.tid).pc = .outside
            · simpa [replayMutators, startCase, outside] using
                ih _ _ (MutatorPrefix.beginCall history selection.tid call outside)
            · simpa [replayMutators, startCase, outside] using ih candidate threads history
  exact go schedule initialCandidate initialThreads MutatorPrefix.initial

/-- `bbfa0ce4150 src/genericmemory.c:222-250`,
`src/gc-wb-stock.h:78-130`: the C entry derives layout and owner from the
destination genericmemory, rejects unequal source types, and passes the caller
addresses and element count to the barrier. -/
def GenericMemoryCallConstruction (c : Config) (call : Call c) : Prop :=
  c.datatypeLayoutsValid ∧ GenericMemoryEntry c call ∧
    ∃ source destination,
      call.sourceMemory = some source ∧ call.destinationMemory = some destination ∧
      call.elementCount ≤ c.memoryLength source ∧
      call.elementCount ≤ c.memoryLength destination ∧
      c.memoryDataAddress source ≤ call.sourceAddress ∧
      call.sourceAddress + call.copyWordCount ≤
        c.memoryDataAddress source + c.memoryLength source * call.copyStride ∧
      c.memoryDataAddress destination ≤ call.destinationAddress ∧
      call.destinationAddress + call.copyWordCount ≤
        c.memoryDataAddress destination + c.memoryLength destination * call.copyStride

/-- `bbfa0ce4150 src/gc-wb-stock.h:78-130`, `src/julia.h:1426-1437`:
the caller's target-width spans and address-to-slot mapping are complete for
every copied word and every pointer field scanned by the source loops. -/
def BulkCopyConstruction (c : Config) (call : Call c) : Prop :=
  call.elementCount < 2 ^ c.wordBits ∧
  call.sourceAddress < 2 ^ c.wordBits ∧
  call.destinationAddress < 2 ^ c.wordBits ∧
  call.sourceAddress + call.copyWordCount ≤ 2 ^ c.wordBits ∧
  call.destinationAddress + call.copyWordCount ≤ 2 ^ c.wordBits ∧
  GenericMemoryCallConstruction c call ∧
  call.copyPointerOffsets.length = call.copyLayout.npointers ∧
  (∀ offset ∈ call.copyPointerOffsets, offset < call.copyStride) ∧
  (∀ index, index < call.copyWordCount →
    ∃ source destination,
      c.slotAtWord (call.sourceAddress + index) = some source ∧
      c.slotAtWord (call.destinationAddress + index) = some destination ∧
      c.owner destination = call.parent) ∧
  (∀ element, element < call.elementCount →
    ∀ offset ∈ call.copyPointerOffsets,
      call.destinationAddress + element * call.copyStride + offset < 2 ^ c.wordBits ∧
      ∃ destination,
        c.slotAtWord (call.destinationAddress + element * call.copyStride + offset) =
          some destination ∧
        c.owner destination = call.parent)

/-- `bbfa0ce4150 src/gc-interface.h:323-345`: immutable payload-copy
construction and its complete source-layout pointer list. -/
def MultiCallConstruction (c : Config) (call : Call c) : Prop :=
  ∃ source, call.source = some source ∧ c.immutable source = true ∧
    call.multiScanSlots = (c.layout source).pointerOffsets.filterMap (c.field source) ∧
    ∀ pair ∈ call.multiCopyPairs, c.owner pair.2 = call.parent

def CallPointerActionsTyped (c : Config) (call : Call c) : Prop :=
  (∀ slot, call.scalarSlot = some slot → c.slotAtomic slot = call.scalarAtomic) ∧
  (∀ pair ∈ call.copyPairs,
    c.slotAtomic pair.1 = true ∧ c.slotAtomic pair.2 = true) ∧
  (∀ slot ∈ call.scanSlots,
    c.slotAtomic slot = (call.kind != .multi))

/-- `bbfa0ce4150 src/gc-interface.h:323-345,355-366`: the documented
ownership, source immutability, target-width span, actual layout, address
mapping and complete-pointer-scan requirements. -/
def CallValid (c : Config) (call : Call c) : Prop :=
  (∀ slot, call.scalarSlot = some slot → c.owner slot = call.parent) ∧
  ((call.kind = .copyBoxed ∨ call.kind = .copyInline) → BulkCopyConstruction c call) ∧
  (call.kind = .multi → MultiCallConstruction c call) ∧
  (call.kind = .scalar → call.scalarSlot.isSome = true) ∧
  CallPointerActionsTyped c call

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`: select one unmarked
reference and its destination slot. The index selects a source field for
immutable payload copies and a destination field for bulk-copy scans. -/
structure BarrierTarget (c : Config) where
  child : ObjectId c
  slot : SlotId c
  index : Nat := 0

/-- `bbfa0ce4150 src/gc-interface.h:323-345,355-366`: the selected
reference is present in a nonempty valid write/copy operation. -/
def TargetsCall {c : Config} (call : Call c) (target : BarrierTarget c) : Prop :=
  match call.kind with
  | .scalar => call.scalarSlot = some target.slot ∧ call.scalarValue = some target.child
  | .object => True
  | .multi => target.index < call.scanSlots.length ∧
      ∃ sourceSlot, call.scanSlots[target.index]? = some sourceSlot ∧
        (sourceSlot, target.slot) ∈ call.copyPairs
  | .copyBoxed | .copyInline =>
      call.elementCount ≠ 0 ∧ target.index < call.scanSlots.length ∧
      call.scanSlots[target.index]? = some target.slot ∧
      ∃ sourceSlot, (sourceSlot, target.slot) ∈ call.copyPairs
  | .moduleUsings => call.source = some target.child ∧ call.scalarSlot = some target.slot

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1706-1748`: the path that still owes a barrier for a
selected unmarked reference, before the first queue-root RMW. This is a
PC assertion, without a remembered-set or reachability conclusion. -/
def BarrierPending {c : Config} (m : Mutator c) (target : BarrierTarget c) : Prop :=
  match m.call.kind with
  | .scalar => m.pc ∈ [.parentGC, .scalarNull, .scalarImage, .scalarChildGC, .rootFetchAnd]
  | .object => m.pc ∈ [.objectGC, .rootFetchAnd]
  | .multi =>
      m.pc ∈ [.parentGC, .multiImage, .multiSourceGC, .multiLayout, .objectGC, .rootFetchAnd] ∨
      (m.pc = .multiSlot ∧ m.scanIndex ≤ target.index) ∨
      (m.pc = .multiChildGC ∧ m.scanIndex ≤ target.index ∧
        (m.scanIndex = target.index → m.pointer = some target.child))
  | .copyBoxed | .copyInline =>
      m.pc ∈ [.copyLoad, .copyStore, .copyEmpty, .copyParentGC, .copySmall, .copyImage, .rootFetchAnd] ∨
      (m.pc = .copyScanSlot ∧ m.scanIndex ≤ target.index) ∨
      (m.pc = .copyScanChildGC ∧ m.scanIndex ≤ target.index ∧
        (m.scanIndex = target.index → m.pointer = some target.child))
  | .moduleUsings => m.pc ∈ [.parentGC, .moduleImage, .moduleChildGC, .rootFetchAnd]

/-- `bbfa0ce4150 src/gc-wb-stock.h:19-130`,
`src/gc-stock.c:1679,1708-1745`: observations before any owner has
claimed queueing. The owner's unchanged header is OLD_MARKED. Mark bits
are stable within a mutator epoch. An immutable source containing the
selected unmarked field cannot be OLD_MARKED outside the remset. For a
bulk copy's last-written field, write/read coherence makes its later scan
observe that value. These are explicit implementation/caller contracts. -/
def BarrierObservation {c : Config} (m : Mutator c) (obs : Observation c)
    (target : BarrierTarget c) : Prop :=
  (m.pc ∈ [.parentGC, .objectGC, .copyParentGC] → obs.header.gc = .oldMarked) ∧
  (m.pc = .multiSourceGC → obs.header.gc ≠ .oldMarked) ∧
  (m.pc ∈ [.scalarChildGC, .moduleChildGC] → obs.header.gc.markedBit = false) ∧
  (m.pc ∈ [.multiSlot, .copyScanSlot] → m.scanIndex = target.index →
    obs.pointer = some target.child) ∧
  (m.pc ∈ [.multiChildGC, .copyScanChildGC] → m.pointer = some target.child →
    obs.header.gc.markedBit = false) ∧
  (m.pc = .rootFetchAnd → obs.header.gc.oldBit = true)

/-- `bbfa0ce4150 src/gc-stock.c:1679-1682`: the emitted instruction
acquires the actual remset-append duty. -/
def InstructionClaims {c : Config} (m : Mutator c) (i : Instruction c) : Prop :=
  ∃ header, i.action = some
    (.rmw (.header m.call.parent) .relaxed (.header header) (.header header.clearOld)) ∧
    header.gc.oldBit = true

end JuliaLean.CRuntime.WriteBarrier
