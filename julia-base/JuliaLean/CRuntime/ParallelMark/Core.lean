import JuliaLean.Registry.Types
import JuliaLean.CRuntime.Memory
import JuliaLean.CRuntime.Types

/-!
Parallel marking at Julia `bbfa0ce4150ea33f2532198cabcf319a49399360`.

The queue machine follows `src/work-stealing-queue.h:24-105`, including
individual memory operations, resize allocation/copying, both strong-CAS
outcomes, and `src/gc-stock.c:1830-1903`. The mark machine follows
`src/gc-stock.c:2817-3032,3409-3444,4019-4031,4055-4062`. Numeric PCs name source lines; extensions split
one C statement's memory accesses. Scanner calls are explicit protocol
boundaries which may make owner pushes before returning. Object headers and
scanner correctness are outside this module.

Read values, read-from edges, modification ranks and SC ranks are explicit
inputs. The completed `Memory.Candidate` checks their consistency. Ordinary
slot accesses remain ordinary accesses, with a separate C11 data-race check.
Single-owner access, fresh/live allocation, representable signed arithmetic,
power-of-two capacities and valid collector IDs are explicit conditions.
An access outside a live allocation or an overflowing signed C expression
records a fault.

Capacities, payload occurrences, allocation IDs and thread IDs are finite
parameters. Pointer and chunk queues have separate locations. Julia's initial
capacities are 2^18 and 2^14 (`src/gc-stock.h:94-95`).
-/

namespace JuliaLean.CRuntime.ParallelMark

open Memory

/-- `bbfa0ce4150`, `src/gc-tls-stock.h:37-41`. -/
inductive QueueKind where
  | pointer | chunk
  deriving DecidableEq, Repr, Inhabited

/-- Complete shared C chunk with its finite representation parameters,
`bbfa0ce4150`, `src/gc-stock.h:72-89`. -/
structure Chunk where
  config : JuliaLean.CRuntime.Config
  value : jl_gc_chunk_t config
  deriving DecidableEq, Repr

/-- Complete memcpy records in `bbfa0ce4150`, `src/gc-stock.c:1830-1903`.
Occurrence IDs distinguish separate publications with identical C values. -/
inductive Payload where
  | zero
  | pointer (occurrence address : Nat)
  | chunk (occurrence : Nat) (value : Chunk)
  deriving DecidableEq, Repr, Inhabited

/-- The chunk sentinel test in `bbfa0ce4150`,
`src/gc-stock.c:2833,2857,2868,2875`. -/
def Payload.emptyChunk : Payload → Bool
  | .zero => true
  | .chunk _ entry => entry.value.cid == .GC_empty_chunk
  | .pointer .. => false

/-- Scanner work consumed by `gc_mark_and_steal`, `bbfa0ce4150`,
`src/gc-stock.c:1909-1922,1984-2013,2828-2840,2857-2875`.
The pointer constructor represents a nonnull pointer; `.zero` is NULL. -/
def Payload.ValidWork : QueueKind → Payload → Prop
  | .pointer, .pointer .. => True
  | .chunk, .chunk _ entry => entry.value.cid ≠ .GC_empty_chunk
  | _, _ => False

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:24-50`,
`src/gc-stock.c:38-50`. -/
inductive Location where
  | top (owner : Nat) (kind : QueueKind)
  | bottom (owner : Nat) (kind : QueueKind)
  | array (owner : Nat) (kind : QueueKind)
  | capacity (array : Nat)
  | mask (array : Nat)
  | buffer (array : Nat)
  | slot (buffer index : Nat)
  | nMarking
  | initiator
  | sweepRequests (thread : Nat)
  | stackSweepRequests (thread : Nat)
  | gcState (thread : Nat)
  deriving DecidableEq, Repr

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:24-50`;
`src/gc-stock.c:38-50,2905-2914,2941-3004,4019-4063`. -/
def declaredAccessClass : Location → Memory.AccessClass
  | .top .. | .bottom .. | .array .. | .nMarking | .initiator
  | .sweepRequests .. | .stackSweepRequests .. | .gcState .. => .atomic
  | .capacity .. | .mask .. | .buffer .. | .slot .. => .ordinary

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:24-50`,
`src/gc-stock.h:80-89`. -/
inductive Value where
  | i64 (value : Int64)
  | i32 (value : Int32)
  | i8 (value : Int8)
  | usize (value : UInt64)
  | address (value : Nat)
  | payload (value : Payload)
  deriving DecidableEq, Repr

abbrev Execution := Memory.Candidate Location Value

/-- Finite inputs of `bbfa0ce4150`, `src/gc-stock.c:2848-2901,2954-2959`,
and allocation in `src/work-stealing-queue.h:30-36`. -/
structure Config where
  threads : Nat
  arrays : Nat
  items : Nat
  initiator : Nat
  firstCollector : Nat
  markThreads : Nat
  pointerBytes : Nat := 8
  chunkBytes : Nat := 64
  previousSweepFull : Bool := false
  rootScanner : Bool := false
  singleThreadedMark : Bool := false
  present : Nat → Bool
  initialPower : Nat → QueueKind → Nat

def Config.lastCollector (c : Config) : Nat := c.firstCollector + c.markThreads - 1

/-- Shared finite C layout parameters, `bbfa0ce4150`,
`src/gc-stock.h:80-89`, `src/gc-tls-stock.h:37-41`. This module targets
the 64-bit Julia build; every modeled address has a finite word-sized ID. -/
def Config.storage (c : Config) : JuliaLean.CRuntime.Config :=
  { objects := c.items, pages := 0, arrays := c.arrays, threads := c.threads,
    addresses := 2^64, wordBits := 64 }

/-- The shared source queue fields, `bbfa0ce4150`,
`src/work-stealing-queue.h:45-50`. -/
def queueLayout (c : Config) (owner : Nat) (kind : QueueKind) :
    ws_queue_t Location c.storage :=
  { top := ⟨.top owner kind⟩, bottom := ⟨.bottom owner kind⟩,
    array := ⟨.array owner kind⟩ }

/-- The shared mark-queue struct, `bbfa0ce4150`,
`src/gc-tls-stock.h:37-41`. Reclaim-list contents use the shared arraylist
layout; list ownership and push/pop control are modeled separately below. -/
def markQueueLayout (c : Config) (owner : Nat)
    (reclaim : arraylist_t c.storage (ArrayId c.storage)) :
    jl_gc_markqueue_t Location c.storage :=
  { chunk_queue := queueLayout c owner .chunk,
    ptr_queue := queueLayout c owner .pointer, reclaim_set := reclaim }

/-- Initialized TLS, power-of-two capacity and ownership preconditions,
`bbfa0ce4150`, `src/gc-stock.c:1830-1903,2819-2824,3967-3979`,
`src/work-stealing-queue.h:24-50`, `src/julia_threads.h:179`,
`src/threading.c:802`. Arithmetic bounds are checked per step. -/
def Config.WellFormed (c : Config) : Prop :=
  0 < c.threads ∧ c.threads ≤ 2^15 ∧ 0 < c.arrays ∧ c.initiator < c.threads ∧
  c.present c.initiator = true ∧ 0 < c.markThreads ∧ c.markThreads < 2^15 ∧
  c.firstCollector + c.markThreads ≤ c.threads ∧
  c.initiator < c.firstCollector ∧
  c.pointerBytes = 8 ∧ c.chunkBytes = 64 ∧
  0 < c.pointerBytes ∧ c.pointerBytes < 2^31 ∧
  0 < c.chunkBytes ∧ c.chunkBytes < 2^31 ∧
  ∀ tid kind, tid < c.threads → c.present tid = true → c.initialPower tid kind ≤ 30

/-- GC initialization sizes and storage for separate pointer/chunk queues,
`bbfa0ce4150`, `src/gc-stock.h:94-95`, `src/gc-stock.c:3967-3979`. -/
def Config.SourceInitial (c : Config) : Prop :=
  c.WellFormed ∧ 2 * c.threads ≤ c.arrays ∧
    ∀ tid, tid < c.threads → c.present tid = true →
      c.initialPower tid .pointer = 18 ∧ c.initialPower tid .chunk = 14

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:24-36`. `power` records
the initialized equality capacity=2^power, mask=capacity-1. -/
structure WsArray where
  contents : ws_array_t Payload
  power : Nat
  headerLive : Bool
  deriving Repr

def WsArray.mask (a : WsArray) : Int32 := Int32.ofBitVec a.contents.mask

/-- A separate malloc allocation for `ws_array_t.buffer`,
`bbfa0ce4150`, `src/work-stealing-queue.h:33,41`. -/
structure BufferAllocation where
  bytes : Nat
  live : Bool
  deriving Repr

/-- Low bits of the signed two's-complement counter, exactly the mask index
in `bbfa0ce4150`, `src/work-stealing-queue.h:61,67,81,101`. -/
def circularIndex (power : Nat) (index : Int64) : Nat :=
  (index.toBitVec.extractLsb' 0 power).toNat

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:61,67,81,101`. -/
def byteOffset (power : Nat) (index : Int64) (elementBytes byte : Nat) : Nat :=
  circularIndex power index * elementBytes + byte

/-- Signed promotion of `int32_t mask` before the C bitwise operation,
`bbfa0ce4150`, `src/work-stealing-queue.h:61,67,81,101`. -/
def maskedIndex (index : Int64) (mask : Int32) : Int64 :=
  Int64.ofBitVec (index.toBitVec &&& (Int64.ofInt mask.toInt).toBitVec)

def fits64 (n : Int) : Bool := decide (-(2^63 : Int) ≤ n ∧ n < 2^63)
def fits32 (n : Int) : Bool := decide (-(2^31 : Int) ≤ n ∧ n < 2^31)

/-- Signed C locals plus address/value dependencies,
`bbfa0ce4150`, `src/work-stealing-queue.h:54-105`. -/
structure Registers where
  b : Int64 := 0
  t : Int64 := 0
  ary : Nat := 0
  oldAry : Option Nat := none
  newAry : Nat := 0
  copyIndex : Int32 := 0
  power : Nat := 0
  newPower : Nat := 0
  capacity : Int32 := 0
  newCapacity : Int32 := 0
  mask : Int32 := 0
  newMask : Int32 := 0
  buffer : Nat := 0
  newBuffer : Nat := 0
  value : Payload := .zero
  pushed : Payload := .zero
  bDeps : List Nat := []
  tDeps : List Nat := []
  aryDeps : List Nat := []
  capacityDeps : List Nat := []
  maskDeps : List Nat := []
  newMaskDeps : List Nat := []
  bufferDeps : List Nat := []
  newBufferDeps : List Nat := []
  valueDeps : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- `bbfa0ce4150`, `src/work-stealing-queue.h:52-105`. -/
inductive QueueOperation where
  | push | pop | steal
  deriving DecidableEq, Repr, Inhabited

/-- Calls in `bbfa0ce4150`, `src/gc-stock.c:2828-2901`.
The queue owner and scheduled caller are separate concrete thread IDs. -/
structure QueueCall where
  operation : QueueOperation
  owner : Nat
  kind : QueueKind
  pc : Nat
  returnPC : Nat
  registers : Registers := {}
  addressDeps : List Nat := []
  controlDeps : List Nat := []
  deriving DecidableEq, Repr

/-- C locals and PCs in `bbfa0ce4150`,
`src/gc-stock.c:2817-3032,4019-4031,4055-4062`.
`scanPC` splits all four relaxed queue loads in `gc_count_work_in_queue`;
`work` is the source's unsigned size_t. -/
structure Thread where
  pc : Nat := 2943
  call : Option QueueCall := none
  result : Payload := .zero
  resultDeps : List Nat := []
  controlDeps : List Nat := []
  initiator : Int32 := -1
  initiatorDeps : List Nat := []
  nMarking : Int32 := 0
  counterDeps : List Nat := []
  work : UInt64 := 0
  scanThread : Nat := 0
  scanPC : Nat := 0
  chunkBottom : Int64 := 0
  chunkTop : Int64 := 0
  pointerBottom : Int64 := 0
  pointerTop : Int64 := 0
  scanDeps : List Nat := []
  index : Nat := 0
  victim : Nat := 0
  shouldMark : Bool := false
  processing : Bool := false
  cleanupArray : Option Nat := none
  cleanupBuffer : Option Nat := none
  markReturnPC : Nat := 2996
  markLoopInitiator : Bool := false
  markLoopReturnPC : Nat := 0
  waiting : Bool := false
  notified : Bool := false
  requests : UInt64 := 0
  requestDeps : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- The per-thread queues/reclaim lists of `bbfa0ce4150`,
`src/gc-tls-stock.h:37-41`, represented by memory locations and allocation
state. Only `gc-stock.c:3017-3018` frees arrays. -/
structure State where
  threads : Nat → Thread
  arrays : Nat → WsArray
  buffers : Nat → BufferAllocation
  reclaimSet : Nat → List Nat
  observer : Option Nat := none
  wakeLock : Option Nat := none
  barrierPassed : Bool := false
  freedBuffers : List Nat := []
  freedHeaders : List Nat := []
  fault : Bool := false
  execution : Execution := ⟨#[]⟩

/-- Explicit observations/annotations for `bbfa0ce4150`,
`src/julia_atomics.h:93-98,199-259`. -/
structure Choice where
  memory : Memory.Choice := {}
  i64 : Int64 := 0
  i32 : Int32 := 0
  i8 : Int8 := 0
  usize : UInt64 := 0
  address : Nat := 0
  payload : Payload := .zero
  randomCollector : Nat := 0
  scannerReturns : Bool := true
  scannerPush : Option (QueueKind × Payload) := none
  resumeWait : Bool := false
  deriving DecidableEq, Repr

/-- Source call sites whose scanner may publish owner work,
`bbfa0ce4150`, `src/gc-stock.c:2834,2840,3394,3396,3429,3431,3442`. -/
def scannerPC (pc : Nat) : Prop :=
  pc ∈ [2834, 2840, 3394, 3396, 3429, 3431, 3442]

/-- The external scanners publish nonnull pointers or nonempty chunks at
their literal call sites, `bbfa0ce4150`,
`src/gc-stock.c:1909-1922,1984-2013,2834,2840,3394-3396,3429-3442`. -/
def Choice.ValidScannerOutput (thread : Thread) (choice : Choice) : Prop :=
  thread.call = none → scannerPC thread.pc →
    ∀ kind value, choice.scannerPush = some (kind, value) → Payload.ValidWork kind value

def noChoice : Choice := { i64 := 0 }

def updateThread (s : State) (tid : Nat) (t : Thread) : State :=
  { s with
    threads := fun i => if i = tid then t else s.threads i }

def updateArray (s : State) (id : Nat) (a : WsArray) : State :=
  { s with
    arrays := fun i => if i = id then a else s.arrays i }

def updateBuffer (s : State) (id : Nat) (buffer : BufferAllocation) : State :=
  { s with buffers := fun i => if i = id then buffer else s.buffers i }

def advance (s : State) (tid pc : Nat) : State :=
  updateThread s tid { s.threads tid with
    pc }

def setCall (s : State) (tid : Nat) (q : QueueCall) : State :=
  updateThread s tid { s.threads tid with
    call := some q }

def emit (s : State) (tid : Nat) (a : Action Location Value)
    (ch : Choice) (deps : List Nat := []) : State :=
  { s with
    execution := s.execution.append
      { (Event.emit tid a ch.memory) with
        dependsOn :=
          ((s.threads tid).controlDeps ++ deps).eraseDups } }

def elementBytes (c : Config) : QueueKind → Nat
  | .pointer => c.pointerBytes
  | .chunk => c.chunkBytes

def validSlot (c : Config) (s : State) (kind : QueueKind)
    (buffer : Nat) (index : Int64) : Bool :=
  let bytes := elementBytes c kind
  let offset := index.toInt * bytes
  decide (buffer < c.arrays) && (s.buffers buffer).live &&
    decide (0 < bytes) && fits32 bytes && fits64 offset &&
    decide (0 ≤ offset ∧ offset + bytes ≤ (s.buffers buffer).bytes)

def checked (s : State) (valid : Bool) : State :=
  { s with
    fault := s.fault || !valid }

def returnQueue (s : State) (tid : Nat) (q : QueueCall) : State :=
  match q.operation with
  | .push => updateThread s tid { s.threads tid with pc := q.returnPC, call := none }
  | .pop | .steal =>
    updateThread s tid { s.threads tid with
      pc := q.returnPC, call := none, result := q.registers.value,
      resultDeps := q.registers.valueDeps ++ q.controlDeps }

def beginQueue (s : State) (tid owner : Nat) (kind : QueueKind)
    (operation : QueueOperation) (returnPC : Nat) (value : Payload := .zero)
    (deps : List Nat := []) : State :=
  setCall s tid {
    owner := owner, kind := kind, operation := operation, pc := 0, returnPC := returnPC,
    registers := { value, pushed := value }, addressDeps := deps,
    controlDeps := (s.threads tid).controlDeps }

def queueControl (s : State) (tid : Nat) (deps : List Nat) : State :=
  match (s.threads tid).call with
  | none => { s with
    fault := true }
  | some q => setCall s tid { q with
    controlDeps := q.controlDeps ++ deps }

def threadControl (s : State) (tid : Nat) (deps : List Nat) : State :=
  updateThread s tid { s.threads tid with
    controlDeps := (s.threads tid).controlDeps ++ deps }

/-- Queue C statements, `bbfa0ce4150`,
`src/work-stealing-queue.h:30-36,54-105`; GC wrapper statements in
`src/gc-stock.c:1836-1839,1845-1847,1853-1855,1861-1872,1901-1903`.
Each ordinary header-field read is separate from the buffer access it
controls. PCs 32/33 allocate header/buffer, 34/35 initialize capacity/mask,
36 initializes the copy loop. CAS failure updates local `t`. -/
def queueStep (c : Config) (s : State) (tid : Nat) (q : QueueCall)
    (ch : Choice) : State := Id.run do
  let r := q.registers
  let go (pc : Nat) (r' : Registers := r) :=
    setCall s tid { q with
      pc, registers := r' }
  let access (a : Action Location Value) (pc : Nat) (r' : Registers := r)
      (deps : List Nat := []) :=
    emit (go pc r') tid a ch (q.addressDeps ++ q.controlDeps ++ deps)
  let id := s.execution.events.size
  let layout := queueLayout c q.owner q.kind
  let headerLive (ary : Nat) := decide (ary < c.arrays) && (s.arrays ary).headerLive
  match q.operation, q.pc with
  | .push, 0 =>
    return go 54 { r with
    oldAry := none }
  | .push, 54 =>
    return access (.load layout.bottom.location .relaxed (.i64 ch.i64)) 55
      { r with
        b := ch.i64, bDeps := [id] }
  | .push, 55 =>
    return access (.load layout.top.location .acquire (.i64 ch.i64)) 56
      { r with
        t := ch.i64, tDeps := [id] }
  | .push, 56 =>
    return access (.load layout.array.location .relaxed (.address ch.address)) 57
      { r with
        ary := ch.address, aryDeps := [id] }
  | .push, 57 =>
    return go 58 { r with
    oldAry := none }
  | .push, 58 =>
    return checked
      (access (.plainLoad (.capacity r.ary) (.i32 ch.i32)) 581
        { r with capacity := ch.i32, capacityDeps := [id], power := (s.arrays r.ary).power }
        r.aryDeps) (headerLive r.ary)
  | .push, 581 =>
    return checked
      (queueControl
        (go (if r.b.toInt - r.t.toInt > r.capacity.toInt - 1 then 59 else 67))
        tid (r.capacityDeps ++ r.bDeps ++ r.tDeps))
      (fits64 (r.b.toInt - r.t.toInt) && fits32 (r.capacity.toInt - 1))
  | .push, 59 =>
    return checked
      (access (.plainLoad (.capacity r.ary) (.i32 ch.i32)) 591
        { r with capacity := ch.i32, capacityDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .push, 591 =>
    return checked (go 32 { r with
      newPower := r.power + 1,
      newCapacity := Int32.ofInt (2 * r.capacity.toInt) })
      (fits32 (2 * r.capacity.toInt))
  | .push, 32 =>
    return checked
      (updateArray (go 33 { r with newAry := ch.address }) ch.address
        { s.arrays ch.address with headerLive := true })
      (decide (ch.address < c.arrays) && !(s.arrays ch.address).headerLive)
  | .push, 33 =>
    let bytes := (UInt64.ofInt r.newCapacity.toInt * UInt64.ofNat (elementBytes c q.kind)).toNat
    return checked
      (updateBuffer
        (access (.plainStore (.buffer r.newAry) (.address ch.address)) 34 r r.capacityDeps)
        ch.address { bytes, live := true })
      (headerLive r.newAry && decide (ch.address < c.arrays) && !(s.buffers ch.address).live)
  | .push, 34 =>
    return updateArray
      (access (.plainStore (.capacity r.newAry) (.i32 r.newCapacity)) 35 r r.capacityDeps)
      r.newAry { s.arrays r.newAry with
        contents := { (s.arrays r.newAry).contents with
          capacity := r.newCapacity.toBitVec },
        power := r.newPower }
  | .push, 35 =>
    let mask := r.newCapacity - 1
    return updateArray (access (.plainStore (.mask r.newAry) (.i32 mask)) 36 r r.capacityDeps)
      r.newAry { s.arrays r.newAry with
        contents := { (s.arrays r.newAry).contents with
          mask := mask.toBitVec } }
  | .push, 36 =>
    return go 60 { r with
    copyIndex := 0 }
  | .push, 60 =>
    return checked
      (access (.plainLoad (.capacity r.ary) (.i32 ch.i32)) 601
        { r with capacity := ch.i32, capacityDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .push, 601 =>
    return queueControl (go (if r.copyIndex < r.capacity then 611 else 63))
      tid r.capacityDeps
  | .push, 611 =>
    return checked
      (access (.plainLoad (.mask r.ary) (.i32 ch.i32)) 612
        { r with mask := ch.i32, maskDeps := [id] } r.aryDeps) (headerLive r.ary)
  | .push, 612 =>
    return checked
      (access (.plainLoad (.buffer r.ary) (.address ch.address)) 613
        { r with buffer := ch.address, bufferDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .push, 613 =>
    return checked
      (access (.plainLoad (.mask r.newAry) (.i32 ch.i32)) 614
        { r with newMask := ch.i32, newMaskDeps := [id] } r.capacityDeps)
      (headerLive r.newAry)
  | .push, 614 =>
    return checked
      (access (.plainLoad (.buffer r.newAry) (.address ch.address)) 615
        { r with newBuffer := ch.address, newBufferDeps := [id] } r.capacityDeps)
      (headerLive r.newAry)
  | .push, 615 =>
    let i := maskedIndex (r.t + Int64.ofInt r.copyIndex.toInt) r.mask
    return checked
      (access (.plainLoad (.slot r.buffer i.toInt.toNat) (.payload ch.payload)) 616
        { r with value := ch.payload, valueDeps := [id] }
        (r.tDeps ++ r.maskDeps ++ r.bufferDeps))
      (fits64 (r.t.toInt + r.copyIndex.toInt) && validSlot c s q.kind r.buffer i)
  | .push, 616 =>
    let i := maskedIndex (r.t + Int64.ofInt r.copyIndex.toInt) r.newMask
    return checked
      (access (.plainStore (.slot r.newBuffer i.toInt.toNat) (.payload r.value)) 617 r
        (r.tDeps ++ r.newMaskDeps ++ r.newBufferDeps ++ r.valueDeps))
      (fits64 (r.t.toInt + r.copyIndex.toInt) && validSlot c s q.kind r.newBuffer i)
  | .push, 617 =>
    return checked (go 60 { r with
    copyIndex := r.copyIndex + 1 })
      (fits32 (r.copyIndex.toInt + 1))
  | .push, 63 =>
    return access (.store layout.array.location .release (.address r.newAry))
      64 r r.capacityDeps
  | .push, 64 =>
    return go 65 { r with
    oldAry := some r.ary }
  | .push, 65 =>
    return go 67 { r with
    ary := r.newAry, power := r.newPower }
  | .push, 67 =>
    return checked
      (access (.plainLoad (.mask r.ary) (.i32 ch.i32)) 671
        { r with mask := ch.i32, maskDeps := [id] } r.aryDeps) (headerLive r.ary)
  | .push, 671 =>
    return checked
      (access (.plainLoad (.buffer r.ary) (.address ch.address)) 672
        { r with buffer := ch.address, bufferDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .push, 672 =>
    let i := maskedIndex r.b r.mask
    return checked
      (access (.plainStore (.slot r.buffer i.toInt.toNat) (.payload r.pushed)) 68
        r (r.bDeps ++ r.maskDeps ++ r.bufferDeps)) (validSlot c s q.kind r.buffer i)
  | .push, 68 =>
    return access (.fence .release) 69
  | .push, 69 =>
    return checked
      (access (.store layout.bottom.location .relaxed (.i64 (r.b + 1))) 70 r r.bDeps)
      (fits64 (r.b.toInt + 1))
  | .push, 70 =>
    return go 1838
  | .push, 1838 =>
    return go (if r.oldAry.isSome then 1839 else 1840)
  | .push, 1839 =>
    match r.oldAry with
    | none =>
      return { s with
      fault := true }
    | some a =>
      return { go 1840 with
      reclaimSet := fun i =>
        if i = q.owner then a :: s.reclaimSet i else s.reclaimSet i }
  | .push, 1840 =>
    return returnQueue s tid q
  | .pop, 0 =>
    return go 75 { r with
    value := .zero }
  | .pop, 75 =>
    return checked
      (access (.load layout.bottom.location .relaxed (.i64 ch.i64)) 76
        { r with
          b := ch.i64 - 1, bDeps := [id] }) (fits64 (ch.i64.toInt - 1))
  | .pop, 76 =>
    return access (.load layout.array.location .relaxed (.address ch.address))
      77 { r with
        ary := ch.address, aryDeps := [id] }
  | .pop, 77 =>
    return access (.store layout.bottom.location .relaxed (.i64 r.b)) 78 r r.bDeps
  | .pop, 78 =>
    return access (.fence .seqCst) 79
  | .pop, 79 =>
    return access (.load layout.top.location .relaxed (.i64 ch.i64)) 80
      { r with
        t := ch.i64, tDeps := [id] }
  | .pop, 80 =>
    return queueControl (go (if r.t ≤ r.b then 81 else 89))
      tid (r.tDeps ++ r.bDeps)
  | .pop, 81 =>
    return checked
      (access (.plainLoad (.mask r.ary) (.i32 ch.i32)) 811
        { r with mask := ch.i32, maskDeps := [id] } r.aryDeps) (headerLive r.ary)
  | .pop, 811 =>
    return checked
      (access (.plainLoad (.buffer r.ary) (.address ch.address)) 812
        { r with buffer := ch.address, bufferDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .pop, 812 =>
    let i := maskedIndex r.b r.mask
    return checked
      (access (.plainLoad (.slot r.buffer i.toInt.toNat) (.payload ch.payload)) 82
        { r with
          value := ch.payload, valueDeps := [id] }
        (r.bDeps ++ r.maskDeps ++ r.bufferDeps)) (validSlot c s q.kind r.buffer i)
  | .pop, 82 =>
    return queueControl (go (if r.t = r.b then 83 else 92))
      tid (r.tDeps ++ r.bDeps)
  | .pop, 83 =>
    return checked
      (queueControl (access (.cas layout.top.location .seqCst .seqCst
        (.i64 r.t) (.i64 (r.t + 1)) (.i64 ch.i64))
        (if ch.i64 = r.t then 85 else 84) { r with
          t := ch.i64, tDeps := [id] } r.tDeps)
        tid [id])
      (fits64 (r.t.toInt + 1))
  | .pop, 84 =>
    return go 85 { r with
    value := .zero, valueDeps := [] }
  | .pop, 85 =>
    return access (.store layout.bottom.location .relaxed (.i64 (r.b + 1)))
      92 r r.bDeps
  | .pop, 89 =>
    return go 90 { r with
    value := .zero, valueDeps := [] }
  | .pop, 90 =>
    return access (.store layout.bottom.location .relaxed (.i64 (r.b + 1)))
      92 r r.bDeps
  | .pop, 92 =>
    return returnQueue s tid q
  | .steal, 0 =>
    return go 96 { r with
    value := .zero }
  | .steal, 96 =>
    return access (.load layout.top.location .acquire (.i64 ch.i64)) 97
      { r with
        t := ch.i64, tDeps := [id] }
  | .steal, 97 =>
    return access (.fence .seqCst) 98
  | .steal, 98 =>
    return access (.load layout.bottom.location .acquire (.i64 ch.i64)) 99
      { r with
        b := ch.i64, bDeps := [id] }
  | .steal, 99 =>
    return queueControl (go (if r.t < r.b then 100 else 105))
      tid (r.tDeps ++ r.bDeps)
  | .steal, 100 =>
    return access (.load layout.array.location .relaxed (.address ch.address))
      101 { r with
        ary := ch.address, aryDeps := [id] }
  | .steal, 101 =>
    return checked
      (access (.plainLoad (.mask r.ary) (.i32 ch.i32)) 1011
        { r with mask := ch.i32, maskDeps := [id] } r.aryDeps) (headerLive r.ary)
  | .steal, 1011 =>
    return checked
      (access (.plainLoad (.buffer r.ary) (.address ch.address)) 1012
        { r with buffer := ch.address, bufferDeps := [id] } r.aryDeps)
      (headerLive r.ary)
  | .steal, 1012 =>
    let i := maskedIndex r.t r.mask
    return checked
      (access (.plainLoad (.slot r.buffer i.toInt.toNat) (.payload ch.payload)) 102
        { r with
          value := ch.payload, valueDeps := [id] }
        (r.tDeps ++ r.maskDeps ++ r.bufferDeps)) (validSlot c s q.kind r.buffer i)
  | .steal, 102 =>
    return checked
      (queueControl (access (.cas layout.top.location .seqCst .seqCst
        (.i64 r.t) (.i64 (r.t + 1)) (.i64 ch.i64))
        (if ch.i64 = r.t then 105 else 103) { r with
          t := ch.i64, tDeps := [id] } r.tDeps)
        tid [id])
      (fits64 (r.t.toInt + 1))
  | .steal, 103 =>
    return go 105 { r with
    value := .zero, valueDeps := [] }
  | .steal, 105 =>
    return returnQueue s tid q
  | _, _ =>
    return { s with
    fault := true }

/-- Four separate relaxed loads in `bbfa0ce4150`,
`src/gc-stock.c:2905-2914`. Signed subtraction precedes conversion to
unsigned size_t. The factor 256 is multiplied in signed int64 arithmetic. -/
def countStep (c : Config) (s : State) (tid : Nat) (ch : Choice) : State :=
  let t := s.threads tid
  let chunk := queueLayout c t.scanThread .chunk
  let pointer := queueLayout c t.scanThread .pointer
  let id := s.execution.events.size
  let put (t' : Thread) := updateThread s tid t'
  let load (loc : Location) (t' : Thread) :=
    emit (put t') tid (.load loc .relaxed (.i64 ch.i64)) ch t.initiatorDeps
  match t.scanPC with
  | 0 => load chunk.bottom.location
      { t with
        scanPC := 1, chunkBottom := ch.i64, scanDeps := id :: t.scanDeps }
  | 1 => load chunk.top.location
      { t with
        scanPC := 2, chunkTop := ch.i64, scanDeps := id :: t.scanDeps }
  | 2 => load pointer.bottom.location
      { t with
        scanPC := 3, pointerBottom := ch.i64, scanDeps := id :: t.scanDeps }
  | 3 => load pointer.top.location
      { t with
        scanPC := 4, pointerTop := ch.i64, scanDeps := id :: t.scanDeps }
  | 4 =>
    let chunks := t.chunkBottom.toInt - t.chunkTop.toInt
    let pointers := t.pointerBottom.toInt - t.pointerTop.toInt
    checked (put { t with
      scanPC := 5,
      work := t.work + UInt64.ofInt (256 * chunks) + UInt64.ofInt pointers })
      (fits64 chunks && fits64 pointers && fits64 (256 * chunks))
  | _ => s

/-- Source PCs for `bbfa0ce4150`, `src/gc-stock.c:2817-3032,3409-3444`.
Owner scanner and finalizer-list pushes use `queueStep`.
The threshold is exactly 16*n (2962).
Random victims must be actual collectors. Cleanup frees buffer and header
separately before separately resetting all four queue indices. Wakeup uses
mutex 1; the observer uses mutex 0. The worker prefix follows
`src/gc-stock.c:4019-4031,4055-4062`, ending at the sweep boundary 4063.
Condition waits release the mutex while blocked and reacquire it on a
notification or an explicit spurious wake choice. -/
def markStep (c : Config) (s : State) (tid : Nat) (ch : Choice) : State := Id.run do
  let t := s.threads tid
  let go (pc : Nat) := advance s tid pc
  let put (t' : Thread) := updateThread s tid t'
  let id := s.execution.events.size
  let own (kind : QueueKind) (ret : Nat) := beginQueue s tid tid kind .pop ret
  let steal (owner : Nat) (kind : QueueKind) (ret : Nat) :=
    beginQueue s tid owner kind .steal ret .zero
      (if owner = t.initiator.toInt.toNat then t.initiatorDeps else [])
  match t.pc with
  | 3394 | 3396 =>
    match ch.scannerPush with
    | some (kind, value) =>
      return checked (beginQueue s tid tid kind .push t.pc value)
        (decide (tid = c.initiator))
    | none =>
      return go (if !ch.scannerReturns then t.pc else if t.pc = 3394 then 3395 else 3397)
  | 3395 =>
    return go (if c.rootScanner then 3396 else 3400)
  | 3397 =>
    return go 3400
  | 3400 =>
    return go (if c.singleThreadedMark then 3401 else 3404)
  | 3401 =>
    return checked (put { t with pc := 2821, markReturnPC := 3406 })
      (decide (tid = c.initiator))
  | 3404 =>
    return checked (put { t with
      pc := 2983, markLoopInitiator := true, markLoopReturnPC := 3406 })
      (decide (tid = c.initiator))
  | 3406 =>
    return checked (go 3002) (decide (tid = c.initiator))
  | 2983 =>
    return go (if t.markLoopInitiator then 2984 else 2991)
  | 2984 =>
    return emit (go 2985) tid
      (.store .initiator .seqCst (.i32 (Int32.ofNat tid))) ch
  | 2985 =>
    return emit (go 2986) tid (.rmw .nMarking .seqCst (.i32 ch.i32) (.i32 (ch.i32 + 1))) ch
  | 2986 =>
    return put { t with pc := 2974, markReturnPC := 2988 }
  | 2974 =>
    return go 2976
  | 2976 =>
    if s.wakeLock.isSome then return s
    else return emit { go 2977 with wakeLock := some tid } tid (.lock 1) ch
  | 2977 =>
    return checked
      { go 2978 with threads := fun i =>
          let current := (go 2978).threads i
          if current.waiting then { current with notified := true } else current }
      (decide (s.wakeLock = some tid))
  | 2978 =>
    return checked
      (emit { go 2987 with wakeLock := none } tid (.unlock 1) ch)
      (decide (s.wakeLock = some tid))
  | 2987 =>
    return go 2821
  | 2821 =>
    return emit (put { t with
    pc := 2822, initiator := ch.i32,
      initiatorDeps := [id] }) tid (.load .initiator .seqCst (.i32 ch.i32)) ch
  | 2822 =>
    return checked (threadControl (go 2828) tid t.initiatorDeps)
      (if t.initiator = -1 then true else
        decide (0 ≤ t.initiator.toInt ∧ t.initiator.toInt.toNat < c.threads) &&
          c.present t.initiator.toInt.toNat)
  | 2828 =>
    return own .pointer 2829
  | 2829 =>
    return threadControl (go (if t.result = .zero then 2832 else 2840))
      tid t.resultDeps
  | 2832 =>
    return own .chunk 2833
  | 2833 =>
    return threadControl (go (if t.result.emptyChunk then 2848 else 2834))
      tid t.resultDeps
  | 2834 | 2840 =>
    match ch.scannerPush with
    | some (kind, value) =>
      return beginQueue (put { t with
      processing := true })
        tid tid kind .push t.pc value
    | none =>
      return put { t with
      pc := if ch.scannerReturns then 2828 else t.pc,
        processing := !ch.scannerReturns }
  | 2848 =>
    return go 2849
  | 2849 =>
    return put { t with
    pc := 2851, index := 0 }
  | 2851 =>
    return go (if t.index < 4 * c.markThreads then 2852 else 2863)
  | 2852 =>
    return checked (put { t with
    pc := 2853, victim := ch.randomCollector })
      (decide (c.firstCollector ≤ ch.randomCollector ∧ ch.randomCollector ≤ c.lastCollector))
  | 2853 =>
    return go 2854
  | 2854 =>
    return checked (go 2855) (c.present t.victim)
  | 2855 =>
    return go 2856
  | 2856 =>
    return steal t.victim .chunk 2857
  | 2857 =>
    return threadControl (go (if t.result.emptyChunk then 2861 else 2834))
      tid t.resultDeps
  | 2861 =>
    return put { t with
    pc := 2851, index := t.index + 1 }
  | 2863 =>
    return put { t with
    pc := 28631, index := c.firstCollector }
  | 28631 =>
    return go (if t.index ≤ c.lastCollector then 2864 else 2874)
  | 2864 =>
    return go 2865
  | 2865 =>
    return checked (go 2866) (c.present t.index)
  | 2866 =>
    return go 2867
  | 2867 =>
    return steal t.index .chunk 2868
  | 2868 =>
    return threadControl (go (if t.result.emptyChunk then 2872 else 2834))
      tid t.resultDeps
  | 2872 =>
    return put { t with
    pc := 28631, index := t.index + 1 }
  | 2874 =>
    return steal (if t.initiator = -1 then tid else t.initiator.toInt.toNat) .chunk 2875
  | 2875 =>
    return threadControl (go (if t.result.emptyChunk then 2880 else 2834))
      tid t.resultDeps
  | 2880 =>
    return put { t with
    pc := 28801, index := 0 }
  | 28801 =>
    return go (if t.index < 4 * c.markThreads then 2881 else 2890)
  | 2881 =>
    return checked (put { t with
    pc := 2882, victim := ch.randomCollector })
      (decide (c.firstCollector ≤ ch.randomCollector ∧ ch.randomCollector ≤ c.lastCollector))
  | 2882 =>
    return go 2883
  | 2883 =>
    return checked (go 2884) (c.present t.victim)
  | 2884 =>
    return go 2885
  | 2885 =>
    return steal t.victim .pointer 2886
  | 2886 =>
    return threadControl (go (if t.result = .zero then 2888 else 2840))
      tid t.resultDeps
  | 2888 =>
    return put { t with
    pc := 28801, index := t.index + 1 }
  | 2890 =>
    return put { t with
    pc := 28901, index := c.firstCollector }
  | 28901 =>
    return go (if t.index ≤ c.lastCollector then 2891 else 2899)
  | 2891 =>
    return go 2892
  | 2892 =>
    return checked (go 2893) (c.present t.index)
  | 2893 =>
    return go 2894
  | 2894 =>
    return steal t.index .pointer 2895
  | 2895 =>
    return threadControl (go (if t.result = .zero then 2897 else 2840))
      tid t.resultDeps
  | 2897 =>
    return put { t with
    pc := 28901, index := t.index + 1 }
  | 2899 =>
    return steal (if t.initiator = -1 then tid else t.initiator.toInt.toNat) .pointer 2900
  | 2900 =>
    return threadControl (go (if t.result = .zero then t.markReturnPC else 2840))
      tid t.resultDeps
  | 2988 | 2996 =>
    return emit (go 2991) tid (.rmw .nMarking .seqCst (.i32 ch.i32) (.i32 (ch.i32 - 1))) ch
  | 2991 =>
    return go 2943
  | 2943 =>
    return put { t with pc := 2944, shouldMark := false }
  | 2944 =>
    if s.observer.isSome then return s
    else return emit { go 2946 with
      observer := some tid } tid (.lock 0) ch
  | 2946 =>
    return emit (put { t with
    pc := 2947, nMarking := ch.i32,
      counterDeps := [id] }) tid (.load .nMarking .seqCst (.i32 ch.i32)) ch
  | 2947 =>
    return threadControl (go (if t.nMarking = 0 then 2970 else 2950))
      tid t.counterDeps
  | 2950 =>
    return emit (put { t with
    pc := 2951, initiator := ch.i32,
      initiatorDeps := [id] }) tid (.load .initiator .relaxed (.i32 ch.i32)) ch
  | 2951 =>
    return checked (threadControl (go 2952) tid t.initiatorDeps)
      (decide (t.initiator ≠ -1))
  | 2952 =>
    return checked (put { t with
    pc := 2953, work := 0,
      scanThread := t.initiator.toInt.toNat, scanPC := 0, scanDeps := [] })
      (decide (0 ≤ t.initiator.toInt ∧ t.initiator.toInt.toNat < c.threads) &&
        c.present t.initiator.toInt.toNat)
  | 2953 =>
    if t.scanPC = 5 then return go 2954
    else return countStep c s tid ch
  | 2954 =>
    return go 2955
  | 2955 =>
    return put { t with
    pc := 2956, index := c.firstCollector }
  | 2956 =>
    return go (if t.index ≤ c.lastCollector then 2957 else 2962)
  | 2957 =>
    return go 2958
  | 2958 =>
    return checked (put { t with
    pc := 2959, scanThread := t.index,
      scanPC := 0 }) (c.present t.index)
  | 2959 =>
    if t.scanPC = 5 then return put { t with
      pc := 2956, index := t.index + 1 }
    else return countStep c s tid ch
  | 2962 =>
    return checked
      (threadControl
        (go (if t.work ≥ UInt64.ofInt (16 * t.nMarking.toInt) then 2963 else 2968))
        tid (t.counterDeps ++ t.scanDeps))
      (fits32 (16 * t.nMarking.toInt))
  | 2963 =>
    return emit (go 2965) tid (.rmw .nMarking .seqCst (.i32 ch.i32) (.i32 (ch.i32 + 1)))
      ch t.counterDeps
  | 2965 =>
    return put { t with
    pc := 2970, shouldMark := true }
  | 2968 =>
    return go 2946
  | 2970 =>
    return checked
      (emit { go 2971 with
        observer := none } tid (.unlock 0) ch)
      (decide (s.observer = some tid))
  | 2971 =>
    return go 2992
  | 2992 =>
    return go (if t.shouldMark then 2995 else 2998)
  | 2995 =>
    return put { t with pc := 2821, markReturnPC := 2996 }
  | 2998 =>
    return go t.markLoopReturnPC
  | 3002 =>
    return checked
      (emit (go 3003) tid (.load .nMarking .relaxed (.i32 ch.i32)) ch)
      (decide (ch.i32 = 0))
  | 3003 =>
    return emit { go 3009 with
    barrierPassed := true } tid
      (.store .initiator .relaxed (.i32 (-1))) ch
  | 3009 =>
    return put { t with
    pc := 30091, index := 0 }
  | 30091 =>
    return go (if t.index < c.threads then 3010 else 3022)
  | 3010 =>
    return go 3011
  | 3011 =>
    return go (if c.present t.index then 3014 else 3020)
  | 3014 =>
    return go 3015
  | 3015 =>
    return put { t with
    pc := 3016, cleanupArray := none, cleanupBuffer := none }
  | 3016 =>
    match s.reclaimSet t.index with
    | [] =>
      return go 3020
    | a :: rest =>
      return { put { t with
      pc := 3017, cleanupArray := some a, cleanupBuffer := none } with
        reclaimSet := fun i => if i = t.index then rest else s.reclaimSet i }
  | 3017 =>
    match t.cleanupArray with
    | none =>
      return { s with
      fault := true }
    | some a =>
      return checked
        (emit (put { t with pc := 30171, cleanupBuffer := some ch.address }) tid
          (.plainLoad (.buffer a) (.address ch.address)) ch)
        (decide (a < c.arrays) && (s.arrays a).headerLive)
  | 30171 =>
    match t.cleanupBuffer with
    | none => return { s with fault := true }
    | some buffer =>
      return checked
        (updateBuffer { go 3018 with freedBuffers := buffer :: s.freedBuffers }
          buffer { s.buffers buffer with live := false })
        (decide (buffer < c.arrays) && (s.buffers buffer).live)
  | 3018 =>
    match t.cleanupArray with
    | none =>
      return { s with
      fault := true }
    | some a =>
      return checked (updateArray { go 3016 with
      freedHeaders := a :: s.freedHeaders }
        a { s.arrays a with
          headerLive := false }) (decide (a < c.arrays) && (s.arrays a).headerLive)
  | 3020 =>
    return put { t with
    pc := 30091, index := t.index + 1 }
  | 3022 =>
    return put { t with
    pc := 30221, index := 0 }
  | 30221 =>
    return go (if t.index < c.threads then 3023 else 3032)
  | 3023 =>
    return go 3024
  | 3024 =>
    return go (if c.present t.index then 3027 else 3031)
  | 3027 =>
    return emit (go 3028) tid
      (.store (queueLayout c t.index .pointer).bottom.location .relaxed (.i64 0)) ch
  | 3028 =>
    return emit (go 3029) tid
      (.store (queueLayout c t.index .pointer).top.location .relaxed (.i64 0)) ch
  | 3029 =>
    return emit (go 3030) tid
      (.store (queueLayout c t.index .chunk).bottom.location .relaxed (.i64 0)) ch
  | 3030 =>
    return emit (go 3031) tid
      (.store (queueLayout c t.index .chunk).top.location .relaxed (.i64 0)) ch
  | 3031 =>
    return put { t with
    pc := 30221, index := t.index + 1 }
  | 3032 =>
    return checked (go 3409) (decide (tid = c.initiator))
  | 3409 =>
    return go 3414
  | 3414 =>
    return put { t with pc := 3416, index := 0 }
  | 3416 =>
    return go (if t.index < c.threads then 3417 else 3421)
  | 3417 =>
    return go 3418
  | 3418 =>
    return go (if c.present t.index then 3419 else 3420)
  | 3419 =>
    return go 3420
  | 3420 =>
    return put { t with pc := 3416, index := t.index + 1 }
  | 3421 =>
    return go (if c.previousSweepFull then 3422 else 3425)
  | 3422 =>
    return go 3423
  | 3423 =>
    return go 3425
  | 3425 =>
    return put { t with pc := 3426, index := 0 }
  | 3426 =>
    return go (if t.index < c.threads then 3427 else 3431)
  | 3427 =>
    return go 3428
  | 3428 =>
    return go (if c.present t.index then 3429 else 3430)
  | 3429 | 3431 | 3442 =>
    match ch.scannerPush with
    | some (kind, value) =>
      return checked (beginQueue s tid tid kind .push t.pc value)
        (decide (tid = c.initiator))
    | none =>
      return go (if !ch.scannerReturns then t.pc else
        if t.pc = 3429 then 3430 else if t.pc = 3431 then 3434 else 3443)
  | 3430 =>
    return put { t with pc := 3426, index := t.index + 1 }
  | 3434 =>
    return checked (put { t with pc := 2821, markReturnPC := 3437 })
      (decide (tid = c.initiator))
  | 3437 =>
    return go 3442
  | 3443 =>
    return checked (put { t with pc := 2821, markReturnPC := 3444 })
      (decide (tid = c.initiator))
  | 3444 =>
    return go 3445
  | 4055 =>
    return go 4056
  | 4056 =>
    if s.wakeLock.isSome then return s
    else return emit { go 4057 with wakeLock := some tid } tid (.lock 1) ch
  | 4057 =>
    return go 4021
  | 4021 =>
    return emit (put { t with pc := 40211, nMarking := ch.i32, counterDeps := [id] })
      tid (.load .nMarking .seqCst (.i32 ch.i32)) ch
  | 40211 =>
    return threadControl (go (if t.nMarking > 0 then 4060 else 4024)) tid t.counterDeps
  | 4024 =>
    return go 4026
  | 4026 =>
    return emit (put { t with pc := 40261, requests := ch.usize, requestDeps := [id] })
      tid (.load (.sweepRequests tid) .seqCst (.usize ch.usize)) ch
  | 40261 =>
    return threadControl (go (if t.requests > 0 then 4060 else 4029)) tid t.requestDeps
  | 4029 =>
    return go 4031
  | 4031 =>
    return emit (put { t with pc := 40311, requests := ch.usize, requestDeps := [id] })
      tid (.load (.stackSweepRequests tid) .seqCst (.usize ch.usize)) ch
  | 40311 =>
    return threadControl (go (if t.requests > 0 then 4060 else 4058)) tid t.requestDeps
  | 4058 =>
    return checked
      (emit { put { t with pc := 40581, waiting := true, notified := false } with
        wakeLock := none } tid (.unlock 1) ch)
      (decide (s.wakeLock = some tid))
  | 40581 =>
    if !(t.notified || ch.resumeWait) || s.wakeLock.isSome then return s
    else return (emit
      { put { t with pc := 4057, waiting := false, notified := false } with
        wakeLock := some tid } tid (.lock 1) ch)
  | 4060 =>
    return checked
      (emit { go 4061 with wakeLock := none } tid (.unlock 1) ch)
      (decide (s.wakeLock = some tid))
  | 4061 =>
    return checked
      (threadControl (emit (go 4062) tid (.load (.gcState tid) .relaxed (.i8 ch.i8)) ch)
        tid [id]) (decide (ch.i8 = 3))
  | 4062 =>
    return put { t with pc := 2983, markLoopInitiator := false, markLoopReturnPC := 4063 }
  | 0 | 3445 | 4063 =>
    return s
  | _ =>
    return { s with
    fault := true }

/-- One scheduled statement/atomic operation, `bbfa0ce4150`,
`src/work-stealing-queue.h:54-105`, `src/gc-stock.c:2817-3032`.
Push/pop require the unique owner; stealing does not. -/
def step (c : Config) (tid : Nat) (ch : Choice) (s : State) : State :=
  if s.fault then s
  else if tid < c.threads then
    match (s.threads tid).call with
    | none => markStep c s tid ch
    | some q =>
      if q.operation ≠ .steal ∧ q.owner ≠ tid then { s with
        fault := true }
      else queueStep c s tid q ch
  else { s with
    fault := true }

/-- Arbitrary finite schedules/read choices, `bbfa0ce4150`,
`src/work-stealing-queue.h:54-105`, `src/gc-stock.c:2817-3032`. -/
def run (c : Config) : List (Nat × Choice) → State → State
  | [], s => s
  | (tid, ch) :: rest, s => run c rest (step c tid ch s)

/-- Scanner-output validity at each actual scheduled source call.
`bbfa0ce4150`, `src/gc-stock.c:2834,2840,3394-3396,3429-3442`. -/
def ScannerOutputsValid (c : Config) : List (Nat × Choice) → State → Prop
  | [], _ => True
  | (tid, choice) :: rest, state =>
    Choice.ValidScannerOutput (state.threads tid) choice ∧
      ScannerOutputsValid c rest (step c tid choice state)

theorem run_append (c : Config) (left right : List (Nat × Choice)) (state : State) :
    run c (left ++ right) state = run c right (run c left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons scheduled rest ih => exact ih (step c scheduled.1 scheduled.2 state)

theorem scannerOutputsValid_append (c : Config) (left right : List (Nat × Choice))
    (state : State) :
    ScannerOutputsValid c (left ++ right) state ↔
      ScannerOutputsValid c left state ∧ ScannerOutputsValid c right (run c left state) := by
  induction left generalizing state with
  | nil => simp [ScannerOutputsValid, run]
  | cons scheduled rest ih =>
    simp only [List.cons_append, ScannerOutputsValid, run, ih, and_assoc]

/-- Initial queue allocation identities, `bbfa0ce4150`,
`src/gc-stock.c:3967-3979`. -/
def initialQueueId (tid : Nat) (kind : QueueKind) : Nat :=
  2 * tid + match kind with | .chunk => 0 | .pointer => 1

/-- Queue fields initialized before the marking round. Malloc-created slots
receive their first value from a push. `bbfa0ce4150`,
`src/work-stealing-queue.h:30-36`, `src/gc-stock.c:3967-3979`. -/
def initialQueueEvents (c : Config) (tid : Nat) (kind : QueueKind) :
    List (Event Location Value) :=
  let array := initialQueueId tid kind
  let capacity := 2 ^ c.initialPower tid kind
  [ { thread := tid, action := .init (.top tid kind) (.i64 0) },
    { thread := tid, action := .init (.bottom tid kind) (.i64 0) },
    { thread := tid, action := .init (.array tid kind) (.address array) },
    { thread := tid, action := .init (.capacity array) (.i32 (Int32.ofNat capacity)) },
    { thread := tid, action := .init (.mask array) (.i32 (Int32.ofNat (capacity - 1))) },
    { thread := tid, action := .init (.buffer array) (.address array) } ]

/-- Initialized GC fields before root publication, `bbfa0ce4150`,
`src/gc-stock.c:38-50,3394,3837-3838,3967-3979,4049,4055`. -/
def initialEvents (c : Config) : List (Event Location Value) :=
  [ { thread := c.initiator, action := .init .nMarking (.i32 0) },
    { thread := c.initiator, action := .init .initiator (.i32 (-1)) } ] ++
  (List.range c.threads).flatMap (fun tid =>
    if c.present tid then
      initialQueueEvents c tid .chunk ++ initialQueueEvents c tid .pointer ++
        [ { thread := tid, action := .init (.sweepRequests tid) (.usize 0) },
          { thread := tid, action := .init (.stackSweepRequests tid) (.usize 0) },
          { thread := tid, action := .init (.gcState tid)
              (.i8 (if c.firstCollector ≤ tid ∧ tid < c.firstCollector + c.markThreads
                then 3 else 1)) } ]
    else [])

/-- Empty initialized queues, distinct allocations and fresh source calls,
`bbfa0ce4150`, `src/gc-stock.c:3394,3967-3979,4055`.
Slot contents are represented by memory events. -/
def canonicalInitial (c : Config) : State :=
  let kind (id : Nat) : QueueKind := if id % 2 = 0 then .chunk else .pointer
  let live (id : Nat) : Bool := decide (id / 2 < c.threads) && c.present (id / 2)
  let power (id : Nat) := if live id then c.initialPower (id / 2) (kind id) else 0
  { threads := fun tid =>
      if tid < c.threads ∧ c.present tid = true then
        if tid = c.initiator then { pc := 3394, markLoopReturnPC := 3406 }
        else if c.firstCollector ≤ tid ∧ tid < c.firstCollector + c.markThreads then
          { pc := 4055, markLoopReturnPC := 4063 }
        else { pc := 0 }
      else { pc := 0 },
    arrays := fun id =>
      { contents :=
          { buffer := #[],
            capacity := BitVec.ofNat 32 (2 ^ power id),
            mask := BitVec.ofNat 32 (2 ^ power id - 1) },
        power := power id,
        headerLive := live id },
    buffers := fun id =>
      { bytes := if live id then 2 ^ power id * elementBytes c (kind id) else 0,
        live := live id },
    reclaimSet := fun _ => [], execution := ⟨(initialEvents c).toArray⟩ }

end JuliaLean.CRuntime.ParallelMark
