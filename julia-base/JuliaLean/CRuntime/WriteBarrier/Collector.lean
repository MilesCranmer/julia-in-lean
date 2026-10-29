import JuliaLean.CRuntime.WriteBarrier.Barrier

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.CRuntime.Memory

/-- `bbfa0ce4150 src/gc-stock.c:1810-1826,1906-1917`: `nptr` count/flags. -/
structure ScanCount where
  pointers : Nat
  old : Bool
  refyoung : Bool := false
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1815-1816,1906-1917`: packed `nptr`. -/
def ScanCount.packed (n : ScanCount) : Nat :=
  4 * n.pointers + (if n.old then 2 else 0) + (if n.refyoung then 1 else 0)

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826,1906-1917,2475-2803,
3092-3115,3685-3700`: collector source PCs. -/
inductive CollectorPC where
  | drainStorage | drainLength | drainItem | drainHeaderLoad | drainHeader | drainQueue | drainClearLength | drainClearNptr
  | imageLength | imageStorage | imageItem | imageQueue
  | scanHeader | scanMetadata | scanPageOldCount | scanPageMarked | scanLayout
  | scanPointer | scanChildAge | claimHeader | claimExchange | claimQueue
  | arrayPreTest | arrayPreSlot | arrayPreAge | arrayPreMarked | arrayPreAdvance
  | arrayPartition | arrayEarlyChunk | arrayScanTest | arrayScanSlot | arrayScanAdvance
  | arrayFinish | arrayLateChunk | returnTail | aborted
  | scanRemsetTest | scanRemsetNptrLoad | scanRemsetNptrStore
  | scanRemsetLength | scanRemsetCapacity | scanRemsetGrow
  | scanRemsetLengthStore | scanRemsetStorage | scanRemsetItemStore
  | resetMode | resetLength | resetItem | resetHeaderLoad | resetHeader | fullClearLength | finished
  | arrayList
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826,2477-2489,3092-3115,
3688-3700`: local collector registers. -/
structure Collector (c : Config) where
  pc : CollectorPC
  target : ThreadId c
  work : MarkWork c
  index : Nat := 0
  length : Nat := 0
  arrayIndex : Nat := 0
  count : BitVec 32 := 0
  capacity : Nat := 0
  backing : ArrayStorage c := .inline
  offsets : List Nat := []
  child : Option (ObjectId c) := none
  oldHeader : Header := { gc := .clean }
  bits : GCBits := .marked
  nptr : ScanCount := ⟨0, false, false⟩
  full : Bool := false
  resetAge : Bool := false
  returnPC : CollectorPC := .scanPointer
  tail : Option (ObjectId c) := none
  arrayBegin : Nat := 0
  arrayEnd : Nat := 0
  scanEnd : Nat := 0
  stride : Nat := 1
  fieldIndex : Nat := 0
  tooBig : Bool := false
  pushedChunk : Bool := false
  support : List Nat := []
  arrayCall : ArrayListState c := {}

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826`, `src/gc-tls-stock.h:27-30`:
the current `int` counter and the `uintptr_t` addition result are representable
as a nonnegative 32-bit C `int`. -/
def RemsetCounterTargetContract {c : Config} (k : Collector c) : Prop :=
  k.nptr.packed < 2 ^ c.wordBits ∧
    k.count.toNat ≤ 2147483647 ∧
    k.count.toNat + k.nptr.pointers ≤ 2147483647

/-- The value assigned back to C `int remset_nptr` after the usual unsigned
conversion for `remset_nptr += nptr >> 2`. -/
def remsetCounterResult {c : Config} (k : Collector c) : BitVec 32 :=
  BitVec.ofNat 32 (k.count.toNat + k.nptr.pointers)

theorem remsetCounterResult_exact {c : Config} (k : Collector c)
    (contract : RemsetCounterTargetContract k) :
    (remsetCounterResult k).toNat = k.count.toNat + k.nptr.pointers := by
  rcases contract with ⟨_, _, sum⟩
  have bound : k.count.toNat + k.nptr.pointers < 2 ^ 32 := by
    omega
  simp [remsetCounterResult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

/-- `bbfa0ce4150 src/gc-stock.c:1830-1903,2056-2057,2074-2075,
2131-2132,2210-2211`: calls distinguish pointer and chunk queues. -/
inductive QueueRequest (c : Config) where
  | pointer (work : MarkWork c)
  | chunk (work : MarkChunk c)
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826,1906-1917,2475-2803,
3092-3115,3685-3700`: one collector instruction. `enqueue` is a call
to the GC queue protocol, preserving the remset pointer tag. -/
structure CollectorInstruction (c : Config) where
  next : Collector c
  action : Option (MemoryAction c) := none
  enqueue : Option (QueueRequest c) := none
  growArray : Bool := false

def cadvance {c : Config} (k : Collector c) (pc : CollectorPC) : CollectorInstruction c :=
  ⟨{ k with pc := pc }, none, none, false⟩

def cemit {c : Config} (k : Collector c) (pc : CollectorPC)
    (a : MemoryAction c) : CollectorInstruction c := ⟨{ k with pc := pc }, some a, none, false⟩

def arrayCollectorInstruction (c : Config) (tid : ThreadId c)
    (k : Collector c) (obs : Observation c) : CollectorInstruction c :=
  let instruction := arrayListInstruction c tid k.work.object k.arrayCall obs
  { next := { k with
      arrayCall := instruction.next
      pc := if instruction.next.pc = .finished then .returnTail
        else if instruction.next.pc = .undefinedAccess then .aborted else .arrayList }
    action := instruction.action
    growArray := instruction.allocate }

/-- `bbfa0ce4150 src/gc-stock.c:1812-1826,1906-1917,2475-2803,
3092-3115,3685-3700`: source-order drain, scan, claim, rebuild and
post-sweep reset. `Layout.traceOffsets` supplies the strong slot stream.
`gc_try_setmark_tag` uses relaxed exchange with its computed desired header. -/
def collectorInstruction (c : Config) (tid : ThreadId c)
    (k : Collector c) (obs : Observation c) : CollectorInstruction c :=
  let obj := k.work.object
  match k.pc with
  | .drainStorage =>
      ⟨{ k with pc := .drainLength, backing := obs.storage },
       some (.plainLoad (.remsetStorage k.target) (.storage obs.storage)), none, false⟩
  | .drainLength =>
      ⟨{ k with pc := .drainItem, index := 0, length := obs.number },
       some (.plainLoad (.remsetLen k.target) (.number obs.number)), none, false⟩
  | .drainItem =>
      if k.index < k.length then
        ⟨{ k with pc := .drainHeaderLoad, child := obs.pointer },
         some (.plainLoad (.remsetItem k.target k.index) (.pointer obs.pointer)), none, false⟩
      else cadvance k .drainClearLength
  | .drainHeaderLoad =>
      match k.child with
      | none => cadvance k .aborted
      | some parent =>
          ⟨{ k with pc := .drainHeader, oldHeader := obs.header },
           some (.plainLoad (.header parent) (.header obs.header)), none, false⟩
  | .drainHeader =>
      match k.child with
      | none => cadvance k .drainQueue
      | some parent => cemit k .drainQueue
          (.plainStore (.header parent) (.header { k.oldHeader with gc := .oldMarked }))
  | .drainQueue =>
      match k.child with
      | none => cadvance { k with index := k.index + 1 } .drainItem
      | some parent =>
          ⟨{ k with pc := .drainItem, index := k.index + 1 }, none, some (.pointer ⟨parent, true⟩), false⟩
  | .drainClearLength => cemit k .drainClearNptr (.plainStore (.remsetLen k.target) (.number 0))
  | .drainClearNptr => cemit k .finished (.plainStore (.remsetNptr k.target) (.counter 0))
  | .imageLength =>
      ⟨{ k with pc := .imageStorage, index := 0, length := obs.number },
       some (.plainLoad (.imageLen) (.number obs.number)), none, false⟩
  | .imageStorage =>
      ⟨{ k with pc := .imageItem, backing := obs.storage },
       some (.plainLoad .imageStorage (.storage obs.storage)), none, false⟩
  | .imageItem =>
      if k.index < k.length then
        ⟨{ k with pc := .imageQueue, child := obs.pointer },
         some (.plainLoad (.imageItem k.index) (.pointer obs.pointer)), none, false⟩
      else cadvance k .finished
  | .imageQueue =>
      match k.child with
      | none => cadvance { k with index := k.index + 1 } .imageItem
      | some parent =>
          ⟨{ k with pc := .imageItem, index := k.index + 1 }, none, some (.pointer ⟨parent, true⟩), false⟩
  | .scanHeader =>
      ⟨{ k with
          pc := .scanMetadata, oldHeader := obs.header
          bits := (if obs.header.gc.oldBit && !k.resetAge then .oldMarked else .marked) },
       some (.plainLoad (.header obj) (.header obs.header)), none, false⟩
  | .scanMetadata =>
      cadvance k (if k.work.remset || k.oldHeader.inImage then .scanLayout else .scanPageOldCount)
  | .scanPageOldCount =>
      match c.page obj with
      | none => cadvance k .scanPageMarked
      | some page =>
          if k.bits = .oldMarked then cemit k .scanPageMarked
            (.rmw (.pageNold page) .relaxed (.number obs.number) (.number ((obs.number + 1) % 65536)))
          else if k.resetAge then cemit k .scanPageMarked (.plainStore (.pageHasYoung page) (.flag true))
          else cadvance k .scanPageMarked
  | .scanPageMarked =>
      match c.page obj with
      | none => cadvance k .scanLayout
      | some page => cemit k .scanLayout (.plainStore (.pageHasMarked page) (.flag true))
  | .scanLayout =>
      let layout := c.layout obj
      match layout.kind with
      | .weakReference => cadvance k .finished
      | .simpleVector =>
          if layout.length = 0 then cadvance k .finished else
          cadvance { k with
            offsets := [0], arrayBegin := 0, arrayEnd := layout.length
            stride := 1, fieldIndex := 0
            nptr := ⟨layout.length, k.bits.oldBit, false⟩ }
            (if k.bits.oldBit then .arrayPreTest else .arrayPartition)
      | .boxedMemory =>
          if layout.length = 0 then cadvance k .finished else
          if layout.symbolElements then cadvance k .finished else
          cadvance { k with
            offsets := [0], arrayBegin := 0, arrayEnd := layout.length
            stride := 1, fieldIndex := 0
            nptr := ⟨layout.length, k.bits.oldBit, false⟩ }
            (if k.bits.oldBit then .arrayPreTest else .arrayPartition)
      | .inlineMemory =>
          if layout.length = 0 then cadvance k .finished else
          match layout.firstPtr with
          | none => cadvance k .finished
          | some first =>
              let next := { k with
                offsets := layout.pointerOffsets, arrayBegin := 0
                arrayEnd := layout.length * layout.sizeWords, stride := layout.sizeWords, fieldIndex := 0
                nptr := ⟨layout.length * layout.pointerOffsets.length, k.bits.oldBit, false⟩ }
              if layout.pointerOffsets.length = 1 then
                cadvance { next with offsets := [0], arrayBegin := first }
                  (if k.bits.oldBit then .arrayPreTest else .arrayPartition)
              else if layout.descriptor = .bits8 ∨ layout.descriptor = .bits16 then
                cadvance next (if k.bits.oldBit then .arrayPreTest else .arrayPartition)
              else cadvance k .aborted
      | _ =>
          let offsets := layout.traceOffsets
          cadvance { k with
            offsets := offsets, index := 0, tail := none
            returnPC := .scanPointer, nptr := ⟨offsets.length, k.bits.oldBit, false⟩ } .scanPointer
  | .scanPointer =>
      match k.offsets[k.index]? with
      | none => cadvance k .scanRemsetTest
      | some offset =>
          match c.field obj offset with
          | none => cadvance k .aborted
          | some slot =>
              ⟨{ k with pc := .scanChildAge, child := obs.pointer, returnPC := .scanPointer },
               some (.plainLoad (.pointer slot) (.pointer obs.pointer)), none, false⟩
  | .scanChildAge =>
      match k.child with
      | none => cadvance
          (if k.returnPC = .scanPointer then { k with index := k.index + 1 } else k) k.returnPC
      | some child =>
          ⟨{ k with
              pc := .claimHeader
              nptr := { k.nptr with refyoung := k.nptr.refyoung || !obs.header.gc.oldBit } },
           some (.plainLoad (.header child) (.header obs.header)), none, false⟩
  | .claimHeader =>
      match k.child with
      | none => cadvance
          (if k.returnPC = .scanPointer then { k with index := k.index + 1 } else k) k.returnPC
      | some child =>
          ⟨{ k with
              oldHeader := obs.header
              pc := (if obs.header.gc.markedBit then k.returnPC else .claimExchange)
              index := (if obs.header.gc.markedBit && decide (k.returnPC = .scanPointer) then k.index + 1 else k.index) },
           some (.plainLoad (.header child) (.header obs.header)), none, false⟩
  | .claimExchange =>
      match k.child with
      | none => cadvance
          (if k.returnPC = .scanPointer then { k with index := k.index + 1 } else k) k.returnPC
      | some child =>
          ⟨{ k with oldHeader := obs.header, pc := .claimQueue },
           some (.rmw (.header child) .relaxed (.header obs.header)
             (.header (k.oldHeader.setMark k.resetAge))), none, false⟩
  | .claimQueue =>
      match k.child with
      | none => cadvance
          (if k.returnPC = .scanPointer then { k with index := k.index + 1 } else k) k.returnPC
      | some child =>
          let next := if k.returnPC = .scanPointer then { k with index := k.index + 1 } else k
          if (c.layout obj).kind = .object ∧ k.returnPC = .scanPointer ∧
              k.index + 1 = k.offsets.length then
            cadvance { next with tail := if k.oldHeader.gc.markedBit then none else some child } k.returnPC
          else
            ⟨{ next with pc := k.returnPC }, none,
             if k.oldHeader.gc.markedBit then none else some (.pointer ⟨child, false⟩), false⟩
  | .arrayPreTest => cadvance k (if k.arrayBegin < k.arrayEnd then .arrayPreSlot else .arrayPartition)
  | .arrayPreSlot =>
      match k.offsets[k.fieldIndex]? with
      | none => cadvance k .arrayPreAdvance
      | some offset =>
          match c.field obj (k.arrayBegin + offset) with
          | none => cadvance k .aborted
          | some slot =>
              ⟨{ k with
                  pc := (if obs.pointer.isSome then .arrayPreAge else .arrayPreAdvance)
                  child := obs.pointer },
               some (.plainLoad (.pointer slot) (.pointer obs.pointer)), none, false⟩
  | .arrayPreAge =>
      match k.child with
      | none => cadvance k .arrayPreAdvance
      | some child =>
          ⟨{ k with
              pc := .arrayPreMarked
              nptr := { k.nptr with refyoung := k.nptr.refyoung || !obs.header.gc.oldBit } },
           some (.plainLoad (.header child) (.header obs.header)), none, false⟩
  | .arrayPreMarked =>
      match k.child with
      | none => cadvance k .arrayPreAdvance
      | some child =>
          ⟨{ k with pc := (if obs.header.gc.markedBit then .arrayPreAdvance else .arrayPartition) },
           some (.plainLoad (.header child) (.header obs.header)), none, false⟩
  | .arrayPreAdvance =>
      if k.fieldIndex + 1 < k.offsets.length then
        cadvance { k with fieldIndex := k.fieldIndex + 1 } .arrayPreSlot
      else cadvance { k with arrayBegin := k.arrayBegin + k.stride, fieldIndex := 0 } .arrayPreTest
  | .arrayPartition =>
      let tooBig := decide ((k.arrayEnd - k.arrayBegin) / 65536 > k.stride)
      let next := { k with
        tooBig := tooBig, pushedChunk := false, fieldIndex := 0
        scanEnd := if tooBig then k.arrayBegin + k.stride * 65536 else k.arrayEnd }
      cadvance next (if tooBig && (!k.nptr.old || k.nptr.refyoung) then .arrayEarlyChunk else .arrayScanTest)
  | .arrayEarlyChunk =>
      ⟨{ k with pc := .arrayScanTest, pushedChunk := true }, none,
       some (.chunk ⟨obj, k.scanEnd, k.arrayEnd, k.stride, k.offsets, k.nptr.packed⟩), false⟩
  | .arrayScanTest => cadvance k (if k.arrayBegin < k.scanEnd then .arrayScanSlot else .arrayFinish)
  | .arrayScanSlot =>
      match k.offsets[k.fieldIndex]? with
      | none => cadvance k .arrayScanAdvance
      | some offset =>
          match c.field obj (k.arrayBegin + offset) with
          | none => cadvance k .aborted
          | some slot =>
              ⟨{ k with pc := .scanChildAge, child := obs.pointer, returnPC := .arrayScanAdvance },
               some (.plainLoad (.pointer slot) (.pointer obs.pointer)), none, false⟩
  | .arrayScanAdvance =>
      if k.fieldIndex + 1 < k.offsets.length then
        cadvance { k with fieldIndex := k.fieldIndex + 1 } .arrayScanSlot
      else cadvance { k with arrayBegin := k.arrayBegin + k.stride, fieldIndex := 0 } .arrayScanTest
  | .arrayFinish =>
      cadvance k (if k.tooBig then (if k.pushedChunk then .finished else .arrayLateChunk) else .scanRemsetTest)
  | .arrayLateChunk =>
      ⟨{ k with pc := .finished }, none,
       some (.chunk ⟨obj, k.scanEnd, k.arrayEnd, k.stride, k.offsets, k.nptr.packed⟩), false⟩
  | .returnTail =>
      match k.tail with
      | none => cadvance k .finished
      | some child =>
          if k.work.remset then
            ⟨{ k with pc := .finished }, none, some (.pointer ⟨child, false⟩), false⟩
          else cadvance { k with work := ⟨child, false⟩, tail := none } .scanHeader
  | .aborted => cadvance k .aborted
  | .scanRemsetTest => cadvance k
      (if k.nptr.old && k.nptr.refyoung then .scanRemsetNptrLoad else .returnTail)
  | .scanRemsetNptrLoad =>
      ⟨{ k with pc := .scanRemsetNptrStore, count := obs.counter },
       some (.plainLoad (.remsetNptr tid) (.counter obs.counter)), none, false⟩
  | .scanRemsetNptrStore => cemit k .scanRemsetLength
      (.plainStore (.remsetNptr tid) (.counter (remsetCounterResult k)))
  | .scanRemsetLength =>
      ⟨{ k with pc := .scanRemsetCapacity, arrayIndex := obs.number },
       some (.plainLoad (.remsetLen tid) (.number obs.number)), none, false⟩
  | .scanRemsetCapacity =>
      ⟨{ k with
          pc := (if k.arrayIndex < obs.number then .scanRemsetLengthStore else .scanRemsetGrow)
          capacity := obs.number, arrayCall := {} },
       some (.plainLoad (.remsetCapacity tid) (.number obs.number)), none, false⟩
  | .scanRemsetGrow | .arrayList => arrayCollectorInstruction c tid k obs
  | .scanRemsetLengthStore => cemit k .scanRemsetStorage
      (.plainStore (.remsetLen tid) (.number (k.arrayIndex + 1)))
  | .scanRemsetStorage =>
      ⟨{ k with pc := .scanRemsetItemStore, backing := obs.storage },
       some (.plainLoad (.remsetStorage tid) (.storage obs.storage)), none, false⟩
  | .scanRemsetItemStore => cemit k .returnTail
      (.plainStore (.remsetItem tid k.arrayIndex) (.pointer (some obj)))
  | .resetMode => cadvance k (if k.full then .fullClearLength else .resetLength)
  | .resetLength =>
      ⟨{ k with pc := .resetItem, index := 0, length := obs.number },
       some (.plainLoad (.remsetLen k.target) (.number obs.number)), none, false⟩
  | .resetItem =>
      if k.index < k.length then
        ⟨{ k with pc := .resetHeaderLoad, child := obs.pointer },
         some (.plainLoad (.remsetItem k.target k.index) (.pointer obs.pointer)), none, false⟩
      else cadvance k .finished
  | .resetHeaderLoad =>
      match k.child with
      | none => cadvance k .aborted
      | some parent =>
          ⟨{ k with pc := .resetHeader, oldHeader := obs.header },
           some (.plainLoad (.header parent) (.header obs.header)), none, false⟩
  | .resetHeader =>
      match k.child with
      | none => cadvance { k with index := k.index + 1 } .resetItem
      | some parent => cemit { k with index := k.index + 1 } .resetItem
          (.plainStore (.header parent) (.header { k.oldHeader with gc := .marked }))
  | .fullClearLength => cemit k .finished (.plainStore (.remsetLen k.target) (.number 0))
  | .finished => cadvance k .finished

/-- `bbfa0ce4150 src/gc-stock.c:2017-2235`: source array-scan partition,
including the old-owner marked-prefix pass and chunk publication flags. -/
structure ScanPartition where
  first : Nat
  end_ : Nat
  stride : Nat
  prefixEnd : Nat
  scanEnd : Nat
  old : Bool
  refyoungAfterPrefix : Bool
  deriving Repr, DecidableEq

/-- `bbfa0ce4150 src/gc-stock.c:2044,2119,2196`: division/check order. -/
def ScanPartition.tooBig (p : ScanPartition) : Bool :=
  decide ((p.end_ - p.prefixEnd) / 65536 > p.stride)

/-- `bbfa0ce4150 src/gc-stock.c:2055,2130,2207`: publish a suffix
chunk early only when subsequent scans cannot change the remset decision. -/
def ScanPartition.publishBefore (p : ScanPartition) : Bool :=
  p.tooBig && (!p.old || p.refyoungAfterPrefix)

end JuliaLean.CRuntime.WriteBarrier
