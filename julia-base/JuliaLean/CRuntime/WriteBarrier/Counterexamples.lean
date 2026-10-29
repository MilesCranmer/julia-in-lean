import JuliaLean.CRuntime.WriteBarrier.Coverage

namespace JuliaLean.CRuntime.WriteBarrier

open JuliaLean.CRuntime.Memory

/-- A sequential heap projection for an actual scalar-barrier invocation.
Every read is checked against the preceding source writes. Allocation
outcomes remain arbitrary; no successful-allocation premise is present. -/
structure SerialHeap (c : Config) where
  array : Remset c
  header : ObjectId c → Header
  pointers : SlotId c → Option (ObjectId c)
  roots : List (ObjectId c) := []
  pageAge : PageId c → PageAge := fun _ => {}

structure SerialState (c : Config) where
  heap : SerialHeap c
  frame : Mutator c

private def serialStore {c : Config} (heap : SerialHeap c)
    (action : Option (MemoryAction c)) : SerialHeap c :=
  match action with
  | some (.rmw (.header object) _ _ (.header value))
  | some (.plainStore (.header object) (.header value)) =>
      { heap with header := fun other => if other = object then value else heap.header other }
  | some (.store (.pointer slot) _ (.pointer value))
  | some (.plainStore (.pointer slot) (.pointer value)) =>
      { heap with pointers := fun other => if other = slot then value else heap.pointers other }
  | _ => heap

def serialStep {c : Config} (tid : ThreadId c) (s : SerialState c)
    (obs : Observation c) : SerialState c :=
  let instruction := mutatorInstruction c tid s.frame obs
  let localState := (PrivateArray.mk s.frame s.heap.array s.heap.array.len).step tid obs
  { frame := instruction.next
    heap := { serialStore s.heap instruction.action with array := localState.array } }

def serialObservation {c : Config} (tid : ThreadId c) (s : SerialState c)
    (obs : Observation c) : Prop :=
  let action := (mutatorInstruction c tid s.frame obs).action
  match action with
  | some (.plainLoad (.header object) (.header value))
  | some (.rmw (.header object) _ (.header value) _) => value = s.heap.header object
  | some (.load (.pointer slot) _ (.pointer value))
  | some (.plainLoad (.pointer slot) (.pointer value)) => value = s.heap.pointers slot
  | some (.plainLoad (.remsetLen thread) (.number value)) => thread = tid ∧ value = s.heap.array.len
  | some (.plainLoad (.remsetCapacity thread) (.number value)) => thread = tid ∧ value = s.heap.array.capacity
  | some (.plainLoad (.remsetStorage thread) (.storage value)) => thread = tid ∧ value = s.heap.array.storage
  | some (.plainLoad (.remsetNptr thread) (.counter value)) => thread = tid ∧ value = s.heap.array.nptr
  | none => True
  | some action => action.readValue = none

def replaySerial {c : Config} (tid : ThreadId c) :
    List (Observation c) → SerialState c → SerialState c
  | [], s => s
  | obs :: rest, s => replaySerial tid rest (serialStep tid s obs)

def serialTraceObserves {c : Config} (tid : ThreadId c) :
    List (Observation c) → SerialState c → Prop
  | [], _ => True
  | obs :: rest, s => serialObservation tid s obs ∧ serialTraceObserves tid rest (serialStep tid s obs)

/-- `bbfa0ce4150 src/julia.h:1372-1383`: `jl_svecset`'s relaxed scalar store. -/
private def scalarCall {c : Config} (parent : ObjectId c) (slot : SlotId c)
    (child : ObjectId c) : Call c :=
  { kind := .scalar, parent := parent, scalarSlot := some slot, scalarValue := some child
    storeOrder := .relaxed }

def scalarStart {c : Config} (heap : SerialHeap c) (call : Call c) : SerialState c :=
  ⟨heap, { call := call, pc := entryPC call.kind }⟩

private theorem replaySerial_append {c : Config} (tid : ThreadId c)
    (first second : List (Observation c)) (s : SerialState c) :
    replaySerial tid (first ++ second) s =
      replaySerial tid second (replaySerial tid first s) := by
  induction first generalizing s with
  | nil => rfl
  | cons obs rest ih => exact ih (serialStep tid s obs)

private theorem serialTraceObserves_append {c : Config} (tid : ThreadId c)
    (first second : List (Observation c)) (s : SerialState c) :
    serialTraceObserves tid (first ++ second) s ↔
      serialTraceObserves tid first s ∧
        serialTraceObserves tid second (replaySerial tid first s) := by
  induction first generalizing s with
  | nil => simp [serialTraceObserves, replaySerial]
  | cons obs rest ih => simp [serialTraceObserves, replaySerial, ih, and_assoc]

/-- `bbfa0ce4150 src/julia.h:1372-1383,1458-1469`, `src/gc-stock.c:1671-1702`: finite
histories of complete valid scalar write invocations, each executed through
the source PCs. Each load and RMW reads the preceding sequential state. -/
inductive ScalarSourceHistory (c : Config) (tid : ThreadId c) (initial : SerialHeap c) :
    SerialHeap c → Prop where
  | initial : ScalarSourceHistory c tid initial initial
  | invoke {before} : ScalarSourceHistory c tid initial before →
      (call : Call c) → call.kind = .scalar → CallValid c call →
      (observations : List (Observation c)) →
      serialTraceObserves tid observations (scalarStart before call) →
      (replaySerial tid observations (scalarStart before call)).frame.pc = .outside →
      ScalarSourceHistory c tid initial
        (replaySerial tid observations (scalarStart before call)).heap

def SerialHeap.toHeap {c : Config} (tid : ThreadId c) (heap : SerialHeap c) : Heap c :=
  { header := heap.header, pointers := heap.pointers, roots := heap.roots
    allocated := fun _ => true
    remset := fun other => if other = tid then heap.array else { items := fun _ => none }
    imageRemset := { items := fun _ => none }
    markerQueue := fun _ => [], chunkQueue := fun _ => []
    pageAge := heap.pageAge }

/-- Quick-start coverage over sequential scalar histories with arbitrary
allocator outcomes. -/
def QuickStartCoverage : Prop :=
  ∀ (c : Config) (tid : ThreadId c) (initial after : SerialHeap c),
    InitialGenerationInvariant c (initial.toHeap tid) →
    ScalarSourceHistory c tid initial after → QuickStartCovered c (after.toHeap tid)

private def oldHeader : Header := { gc := .oldMarked, tag := 20 }
private def youngHeader : Header := { gc := .clean, tag := 20 }

private def scalarPrefixTrace {c : Config} : List (Observation c) :=
  [{ header := oldHeader }, {}, { header := oldHeader }, { header := youngHeader },
   { header := oldHeader }, {}]

private def noGrowArrayTrace {c : Config} (len : Nat) : List (Observation c) :=
  [{ number := len }, {}, { number := 29 }, {}, {}, { number := len + 1 },
   { storage := .inline }, {}]

private def scalarSuffixTrace {c : Config} (count : BitVec 32) : List (Observation c) :=
  [{ counter := count }, {}, {}, {}, {}]

private def noGrowTrace {c : Config} (len : Nat) (count : BitVec 32) : List (Observation c) :=
  scalarPrefixTrace ++ (noGrowArrayTrace len ++ scalarSuffixTrace count)

private def failedGrowArrayTrace {c : Config} : List (Observation c) :=
  [{ number := 29 }, {}, { number := 29 }, {}, { storage := .inline },
   { allocation := none }, {}, { number := 29 }, { storage := .inline }, {}]

private def failedGrowTrace {c : Config} (count : BitVec 32) : List (Observation c) :=
  scalarPrefixTrace ++ (failedGrowArrayTrace ++ scalarSuffixTrace count)

private def scalarEnd {c : Config} (before : SerialHeap c) (parent : ObjectId c)
    (slot : SlotId c) (child : ObjectId c) (len index : Nat) : SerialHeap c :=
  { before with
    array := { before.array with
      len := len
      nptr := before.array.nptr + 1
      items := fun other => if other = index then some parent else before.array.items other }
    header := fun other => if other = parent then oldHeader.clearOld else before.header other
    pointers := fun other => if other = slot then some child else before.pointers other }

private def scalarClaimedHeap {c : Config} (before : SerialHeap c) (parent : ObjectId c) :
    SerialHeap c :=
  { before with
    header := fun other => if other = parent then oldHeader.clearOld else before.header other }

private def scalarArrayStart {c : Config} (before : SerialHeap c) (parent : ObjectId c)
    (slot : SlotId c) (child : ObjectId c) : SerialState c :=
  { heap := scalarClaimedHeap before parent
    frame :=
      { call := scalarCall parent slot child
        pc := .rootLengthLoad
        readHeader := youngHeader
        oldHeader := oldHeader } }

private def scalarArrayEnd {c : Config} (before : SerialHeap c) (parent : ObjectId c)
    (slot : SlotId c) (child : ObjectId c) (len : Nat) : SerialState c :=
  { heap :=
      { scalarClaimedHeap before parent with
        array :=
          { before.array with
            len := len + 1
            items := fun other => if other = len then some parent else before.array.items other } }
    frame :=
      { call := scalarCall parent slot child
        pc := .rootNptrLoad
        readHeader := youngHeader
        oldHeader := oldHeader
        arrayIndex := len
        arrayCall :=
          { pc := .finished
            len := len
            newlen := len + 1
            max := 29
            pushLen := len + 1
            pushBacking := .inline } } }

private def scalarFailedArrayEnd {c : Config} (before : SerialHeap c)
    (parent : ObjectId c) (slot : SlotId c) (child : ObjectId c) : SerialState c :=
  { heap :=
      { scalarClaimedHeap before parent with
        array :=
          { before.array with
            items := fun other => if other = 28 then some parent else before.array.items other } }
    frame :=
      { call := scalarCall parent slot child
        pc := .rootNptrLoad
        readHeader := youngHeader
        oldHeader := oldHeader
        arrayIndex := 28
        arrayCall :=
          { pc := .finished
            len := 29
            newlen := 30
            max := 29
            pushLen := 29
            pushBacking := .inline } } }

private theorem scalarPrefix {c : Config} (tid : ThreadId c) (before : SerialHeap c)
    (parent : ObjectId c) (slot : SlotId c) (child : ObjectId c)
    (owner : before.header parent = oldHeader) (young : before.header child = youngHeader) :
    serialTraceObserves tid scalarPrefixTrace
        (scalarStart before (scalarCall parent slot child)) ∧
      replaySerial tid scalarPrefixTrace
        (scalarStart before (scalarCall parent slot child)) =
          scalarArrayStart before parent slot child := by
  simp [scalarPrefixTrace, scalarStart, scalarCall, entryPC, serialTraceObserves,
    replaySerial, serialObservation, serialStep, serialStore, PrivateArray.step,
    mutatorInstruction, advance, readHeader, afterParentGC, inArrayCode,
    scalarClaimedHeap, scalarArrayStart, oldHeader, youngHeader,
    Header.imageNotRemset, Header.clearOld, GCBits.clearOld, GCBits.markedBit,
    GCBits.oldBit, owner, young]

private theorem scalarArray_noGrow {c : Config} (tid : ThreadId c)
    (before : SerialHeap c) (parent : ObjectId c) (slot : SlotId c)
    (child : ObjectId c) (len : Nat)
    (length : before.array.len = len) (capacity : before.array.capacity = 29)
    (storage : before.array.storage = .inline) (fits : len < 29)
    (word : len + 1 < 2 ^ c.wordBits) :
    serialTraceObserves tid (noGrowArrayTrace len)
        (scalarArrayStart before parent slot child) ∧
      replaySerial tid (noGrowArrayTrace len)
        (scalarArrayStart before parent slot child) =
          scalarArrayEnd before parent slot child len := by
  have noGrowth : ¬ len + 1 > 29 := by omega
  have wrap : wordWrap c (len + 1) = len + 1 := Nat.mod_eq_of_lt word
  rcases before with ⟨array, headers, pointers, roots, pages⟩
  rcases array with ⟨items, actualLength, actualCapacity, count, actualStorage⟩
  dsimp only at length capacity storage
  subst actualLength
  subst actualCapacity
  subst actualStorage
  simp [noGrowArrayTrace, scalarArrayStart, scalarArrayEnd, scalarClaimedHeap,
    scalarCall, serialTraceObserves, replaySerial, serialObservation, serialStep,
    serialStore, PrivateArray.step, mutatorInstruction, arrayMutatorInstruction,
    arrayListInstruction, arrayListEffect, inArrayCode, arrayMutatorPC,
    ArrayTarget.lengthLocation, ArrayTarget.maxLocation, ArrayTarget.storageLocation,
    ArrayTarget.itemLocation, Action.readValue, noGrowth, wrap]

private theorem scalarSuffix_noGrow {c : Config} (tid : ThreadId c)
    (before : SerialHeap c) (parent : ObjectId c) (slot : SlotId c)
    (child : ObjectId c) (len : Nat) (counter : before.array.nptr ≠ 0x7fffffff) :
    serialTraceObserves tid (scalarSuffixTrace before.array.nptr)
        (scalarArrayEnd before parent slot child len) ∧
      (replaySerial tid (scalarSuffixTrace before.array.nptr)
        (scalarArrayEnd before parent slot child len)).frame.pc = .outside ∧
      (replaySerial tid (scalarSuffixTrace before.array.nptr)
        (scalarArrayEnd before parent slot child len)).heap =
          scalarEnd before parent slot child (len + 1) len := by
  rcases before with ⟨array, headers, pointers, roots, pages⟩
  rcases array with ⟨items, actualLength, actualCapacity, count, actualStorage⟩
  dsimp only at counter
  have safe : count ≠ 2147483647#32 := by simpa using counter
  simp [scalarSuffixTrace, scalarArrayEnd, scalarClaimedHeap, scalarEnd, scalarCall,
    serialTraceObserves, replaySerial, serialObservation, serialStep, serialStore,
    PrivateArray.step, mutatorInstruction, advance, emit, afterBarrier,
    inArrayCode, Action.readValue,
    oldHeader, Header.clearOld, GCBits.clearOld, safe]

private theorem scalarArray_failedGrow {c : Config} (tid : ThreadId c)
    (before : SerialHeap c) (parent : ObjectId c) (slot : SlotId c)
    (child : ObjectId c)
    (length : before.array.len = 29) (capacity : before.array.capacity = 29)
    (storage : before.array.storage = .inline) (word : 30 < 2 ^ c.wordBits) :
    serialTraceObserves tid failedGrowArrayTrace
        (scalarArrayStart before parent slot child) ∧
      replaySerial tid failedGrowArrayTrace
        (scalarArrayStart before parent slot child) =
          scalarFailedArrayEnd before parent slot child := by
  have wrap : wordWrap c 30 = 30 := Nat.mod_eq_of_lt word
  rcases before with ⟨array, headers, pointers, roots, pages⟩
  rcases array with ⟨items, actualLength, actualCapacity, count, actualStorage⟩
  dsimp only at length capacity storage
  subst actualLength
  subst actualCapacity
  subst actualStorage
  simp [failedGrowArrayTrace, scalarArrayStart, scalarFailedArrayEnd,
    scalarClaimedHeap, scalarCall, serialTraceObserves, replaySerial,
    serialObservation, serialStep, serialStore, PrivateArray.step,
    mutatorInstruction, arrayMutatorInstruction, arrayListInstruction,
    arrayListEffect, inArrayCode, arrayMutatorPC,
    ArrayTarget.lengthLocation, ArrayTarget.maxLocation, ArrayTarget.storageLocation,
    ArrayTarget.itemLocation, Action.readValue, wrap]

private theorem scalarSuffix_failedGrow {c : Config} (tid : ThreadId c)
    (before : SerialHeap c) (parent : ObjectId c) (slot : SlotId c)
    (child : ObjectId c) (length : before.array.len = 29)
    (counter : before.array.nptr ≠ 0x7fffffff) :
    serialTraceObserves tid (scalarSuffixTrace before.array.nptr)
        (scalarFailedArrayEnd before parent slot child) ∧
      (replaySerial tid (scalarSuffixTrace before.array.nptr)
        (scalarFailedArrayEnd before parent slot child)).frame.pc = .outside ∧
      (replaySerial tid (scalarSuffixTrace before.array.nptr)
        (scalarFailedArrayEnd before parent slot child)).heap =
          scalarEnd before parent slot child 29 28 := by
  rcases before with ⟨array, headers, pointers, roots, pages⟩
  rcases array with ⟨items, actualLength, actualCapacity, count, actualStorage⟩
  dsimp only at length counter
  subst actualLength
  have safe : count ≠ 2147483647#32 := by simpa using counter
  simp [scalarSuffixTrace, scalarFailedArrayEnd, scalarClaimedHeap, scalarEnd,
    scalarCall, serialTraceObserves, replaySerial, serialObservation, serialStep,
    serialStore, PrivateArray.step, mutatorInstruction, advance, emit,
    afterBarrier, inArrayCode, Action.readValue,
    oldHeader, Header.clearOld, GCBits.clearOld, safe]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
private theorem scalar_noGrow {c : Config} (tid : ThreadId c) (before : SerialHeap c)
    (parent : ObjectId c) (slot : SlotId c) (child : ObjectId c) (len : Nat)
    (length : before.array.len = len) (capacity : before.array.capacity = 29)
    (storage : before.array.storage = .inline)
    (owner : before.header parent = oldHeader) (young : before.header child = youngHeader)
    (fits : len < 29) (word : len + 1 < 2 ^ c.wordBits)
    (counter : before.array.nptr ≠ 0x7fffffff) :
    serialTraceObserves (c := c) tid (noGrowTrace (c := c) len before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child)) ∧
    (replaySerial (c := c) tid (noGrowTrace (c := c) len before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child))).frame.pc = .outside ∧
    (replaySerial (c := c) tid (noGrowTrace (c := c) len before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child))).heap =
        scalarEnd before parent slot child (len + 1) len := by
  have prefixRun := scalarPrefix tid before parent slot child owner young
  have arrayRun := scalarArray_noGrow tid before parent slot child len
    length capacity storage fits word
  have suffixRun := scalarSuffix_noGrow tid before parent slot child len counter
  rw [noGrowTrace, serialTraceObserves_append]
  refine ⟨⟨prefixRun.1, ?_⟩, ?_, ?_⟩
  · rw [prefixRun.2, serialTraceObserves_append]
    exact ⟨arrayRun.1, by rw [arrayRun.2]; exact suffixRun.1⟩
  · rw [replaySerial_append, prefixRun.2, replaySerial_append, arrayRun.2]
    exact suffixRun.2.1
  · rw [replaySerial_append, prefixRun.2, replaySerial_append, arrayRun.2]
    exact suffixRun.2.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
private theorem scalar_failedGrow {c : Config} (tid : ThreadId c) (before : SerialHeap c)
    (parent : ObjectId c) (slot : SlotId c) (child : ObjectId c)
    (length : before.array.len = 29) (capacity : before.array.capacity = 29)
    (storage : before.array.storage = .inline)
    (owner : before.header parent = oldHeader) (young : before.header child = youngHeader)
    (word : 30 < 2 ^ c.wordBits) (counter : before.array.nptr ≠ 0x7fffffff) :
    serialTraceObserves (c := c) tid (failedGrowTrace (c := c) before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child)) ∧
    (replaySerial (c := c) tid (failedGrowTrace (c := c) before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child))).frame.pc = .outside ∧
    (replaySerial (c := c) tid (failedGrowTrace (c := c) before.array.nptr)
      (scalarStart before (scalarCall (c := c) parent slot child))).heap =
        scalarEnd before parent slot child 29 28 := by
  have prefixRun := scalarPrefix tid before parent slot child owner young
  have arrayRun := scalarArray_failedGrow tid before parent slot child
    length capacity storage word
  have suffixRun := scalarSuffix_failedGrow tid before parent slot child length counter
  rw [failedGrowTrace, serialTraceObserves_append]
  refine ⟨⟨prefixRun.1, ?_⟩, ?_, ?_⟩
  · rw [prefixRun.2, serialTraceObserves_append]
    exact ⟨arrayRun.1, by rw [arrayRun.2]; exact suffixRun.1⟩
  · rw [replaySerial_append, prefixRun.2, replaySerial_append, arrayRun.2]
    exact suffixRun.2.1
  · rw [replaySerial_append, prefixRun.2, replaySerial_append, arrayRun.2]
    exact suffixRun.2.2

/-- `bbfa0ce4150 src/simplevector.c:81-100`, `src/support/arraylist.h:6`:
sixty one-slot SimpleVectors, thirty owners and thirty young children;
the inline remembered-set capacity is 29. -/
abbrev allocationConfig : Config :=
  { objects := 60, threads := 1, slots := 60, pages := 1, arrays := 1, addresses := 0
    datatypes := 1, genericMemories := 1
    layout := fun _ => { kind := .simpleVector, sizeWords := 1, pointerOffsets := [], length := 1 }
    datatypeLayout := fun _ =>
      { kind := .inlineMemory, sizeWords := 1, pointerOffsets := [], length := 1 }
    memoryDatatype := fun _ => 0, memoryObject := fun _ => 0
    memoryOwner := fun _ => 0, memoryDataAddress := fun _ => 0, memoryLength := fun _ => 1
    field := fun object offset => if offset = 0 then some ⟨object.val, object.isLt⟩ else none
    owner := fun slot => ⟨slot.val, slot.isLt⟩
    slotAtomic := fun _ => true
    page := fun _ => some 0, immutable := fun _ => false }

private def allocationOwner (index : Nat) : ObjectId allocationConfig :=
  ⟨index % 30, by
    change index % 30 < 60
    have := Nat.mod_lt index (by decide : 0 < 30)
    omega⟩
private def allocationSlot (index : Nat) : SlotId allocationConfig :=
  ⟨index % 30, by
    change index % 30 < 60
    have := Nat.mod_lt index (by decide : 0 < 30)
    omega⟩
private def allocationChild (index : Nat) : ObjectId allocationConfig :=
  ⟨30 + index % 30, by
    change 30 + index % 30 < 60
    have := Nat.mod_lt index (by decide : 0 < 30)
    omega⟩

private def allocationCheckpoint (count : Nat) : SerialHeap allocationConfig :=
  { array := {
      len := count
      capacity := 29
      storage := .inline
      nptr := BitVec.ofNat 32 count
      items := fun index => if index < count then some (allocationOwner index) else none }
    header := fun object => if object.val < 30 then
      if object.val < count then oldHeader.clearOld else oldHeader else youngHeader
    pointers := fun slot => if slot.val < count then some (allocationChild slot.val) else none
    roots := [allocationOwner 28]
    pageAge := fun _ => { hasMarked := true, hasYoung := true, nold := 30, prevNold := 30 } }

private theorem allocationCall_valid (index : Nat) :
    CallValid allocationConfig
      (scalarCall (allocationOwner index) (allocationSlot index) (allocationChild index)) := by
  simp [CallValid, CallPointerActionsTyped, Call.scanSlots, Call.copyPairs,
    scalarCall, allocationConfig, allocationOwner, allocationSlot]

private theorem allocationCheckpoint_successor (count : Nat) (fits : count < 29) :
    scalarEnd (allocationCheckpoint count) (allocationOwner count) (allocationSlot count)
      (allocationChild count) (count + 1) count = allocationCheckpoint (count + 1) := by
  have small : count < 30 := by omega
  have modCount : count % 30 = count := Nat.mod_eq_of_lt small
  simp only [scalarEnd, allocationCheckpoint, SerialHeap.mk.injEq, Remset.mk.injEq]
  refine ⟨?_, ?_, ?_, by trivial, by trivial⟩
  · refine ⟨?_, by trivial, by trivial, ?_, by trivial⟩
    · funext index
      by_cases equal : index = count
      · subst index; simp
      · by_cases less : index < count
        · have next : index < count + 1 := by omega
          simp [equal, less, next]
        · have next : ¬ index < count + 1 := by omega
          simp [equal, less, next]
    · simp [BitVec.ofNat_add]
  · funext object
    by_cases equal : object = allocationOwner count
    · subst object; simp [allocationOwner, modCount, small]
    · have unequal : object.val ≠ count := by
        intro value
        apply equal
        apply Fin.ext
        simpa [allocationOwner, modCount] using value
      by_cases parent : object.val < 30
      · by_cases earlier : object.val < count <;>
          simp_all [show object.val < count + 1 ↔ object.val < count by omega]
      · simp [parent, equal]
  · funext slot
    by_cases equal : slot = allocationSlot count
    · subst slot; simp [allocationSlot, modCount]
    · have unequal : slot.val ≠ count := by
        intro value
        apply equal
        apply Fin.ext
        simpa [allocationSlot, modCount] using value
      by_cases earlier : slot.val < count <;>
        simp_all [show slot.val < count + 1 ↔ slot.val < count by omega]

/-- The full 29-entry checkpoint is reached from the empty initialized TLS
array by 29 complete successful source invocations. -/
theorem allocationCheckpoint_reachable (count : Nat) (bound : count ≤ 29) :
    ScalarSourceHistory allocationConfig 0 (allocationCheckpoint 0) (allocationCheckpoint count) := by
  induction count with
  | zero => exact .initial
  | succ count ih =>
      have fits : count < 29 := by omega
      have small : count < 30 := by omega
      have modCount : count % 30 = count := Nat.mod_eq_of_lt small
      have prior := ih (by omega)
      have run := scalar_noGrow (c := allocationConfig) 0 (allocationCheckpoint count)
        (allocationOwner count) (allocationSlot count) (allocationChild count) count
        rfl rfl rfl (by simp [allocationCheckpoint, allocationOwner, modCount, small])
        (by simp [allocationCheckpoint, allocationChild]; omega) fits
        (by change count + 1 < 18446744073709551616; omega)
        (by
          intro equal
          have value := congrArg BitVec.toNat equal
          have smallCount : count < 4294967296 := by omega
          simp [allocationCheckpoint, BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallCount] at value
          omega)
      have next := ScalarSourceHistory.invoke prior _ rfl (allocationCall_valid count)
        (noGrowTrace count (allocationCheckpoint count).array.nptr) run.1 run.2.1
      rw [run.2.2, allocationCheckpoint_successor count fits] at next
      exact next

private def allocationFailureHeap : SerialHeap allocationConfig :=
  scalarEnd (allocationCheckpoint 29) (allocationOwner 29) (allocationSlot 29)
    (allocationChild 29) 29 28

theorem allocationFailure_reachable :
    ScalarSourceHistory allocationConfig 0 (allocationCheckpoint 0) allocationFailureHeap := by
  have run := scalar_failedGrow (c := allocationConfig) 0 (allocationCheckpoint 29)
    (allocationOwner 29) (allocationSlot 29) (allocationChild 29) rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide)
  have next := ScalarSourceHistory.invoke (allocationCheckpoint_reachable 29 (by decide))
    _ rfl (allocationCall_valid 29) (failedGrowTrace (allocationCheckpoint 29).array.nptr) run.1 run.2.1
  simpa [run.2.2, allocationFailureHeap] using next

theorem allocationFailure_loses_owner :
    (allocationFailureHeap.toHeap 0).header (allocationOwner 28) = oldHeader.clearOld ∧
    Edge allocationConfig (allocationFailureHeap.toHeap 0) (allocationOwner 28) (allocationChild 28) ∧
    ¬ RememberedForQuick allocationConfig (allocationFailureHeap.toHeap 0) (allocationOwner 28) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact ⟨0, by decide, allocationSlot 28, by decide, by decide⟩
  · rintro (⟨thread, index, bound, item⟩ | ⟨full, image⟩)
    · have threadZero : thread = 0 := Fin.ext (Fin.val_eq_zero thread)
      subst thread
      have small : index < 30 := by
        simpa [allocationFailureHeap, scalarEnd, SerialHeap.toHeap] using Nat.lt_succ_of_lt bound
      have modIndex := Nat.mod_eq_of_lt small
      by_cases last : index = 28
      · subst index
        have impossible : (allocationOwner 29 : ObjectId allocationConfig) ≠ allocationOwner 28 := by decide
        exact impossible (Option.some.inj (by simpa [SerialHeap.toHeap, allocationFailureHeap, scalarEnd] using item))
      · have less : index < 29 := by simpa [allocationFailureHeap, scalarEnd, SerialHeap.toHeap] using bound
        simp [SerialHeap.toHeap, allocationFailureHeap, scalarEnd, allocationCheckpoint,
          last, less, allocationOwner, modIndex, Fin.ext_iff] at item
        omega
    · simp [SerialHeap.toHeap] at full

theorem allocationFailure_child_reachable :
    Reachable allocationConfig (allocationFailureHeap.toHeap 0) (allocationChild 28) := by
  exact .edge (.root (by decide)) allocationFailure_loses_owner.2.1

theorem quickStartCoverage_refuted : ¬ QuickStartCoverage := by
  intro coverage
  have initial : InitialGenerationInvariant allocationConfig ((allocationCheckpoint 0).toHeap 0) := by
    intro parent child edge
    obtain ⟨offset, traced, slot, field, pointer⟩ := edge
    simp [SerialHeap.toHeap, allocationCheckpoint] at pointer
  have covered := coverage allocationConfig 0 (allocationCheckpoint 0) allocationFailureHeap
    initial allocationFailure_reachable
  obtain ⟨header, edge, lost⟩ := allocationFailure_loses_owner
  exact lost (covered (allocationOwner 28) (allocationChild 28) edge
    (by rw [header]; decide) (by decide))

/-- Both allocator outcomes flow through the shared TLS/image mutator and
marker-rebuild callers. A NULL result resumes `push` at its length reload;
a non-NULL result reaches the source copy/storage-publication path. -/
def ArrayListAllocationOutcomes : Prop :=
  ∀ (c : Config) (tid : ThreadId c) (parent : ObjectId c) (target : ArrayTarget)
      (pc : ArrayListPC) (result : Option (AllocationId c)),
    pc ∈ [.inlineAllocate, .heapAllocate] →
    let initial : ArrayListState c := { target := target, pc := pc }
    let obs : Observation c := { allocation := result }
    let allocated := (arrayListInstruction c tid parent initial obs).next
    let mutator : Mutator c :=
      { call := { kind := .object, parent := parent }
        pc := .arrayList, arrayCall := initial }
    let collector : Collector c :=
      { pc := .arrayList, target := tid
        work := ⟨parent, false⟩, arrayCall := initial }
    allocated.result = result ∧ allocated.target = target ∧
    (arrayListInstruction c tid parent allocated {}).next.pc =
      (if result.isNone then .pushLength
       else if pc = .inlineAllocate then .copyInline else .storeStorage) ∧
    (mutatorInstruction c tid mutator obs).next.arrayCall = allocated ∧
    (collectorInstruction c tid collector obs).next.arrayCall = allocated

theorem arrayListAllocationOutcomes_proven : ArrayListAllocationOutcomes := by
  intro c tid parent target pc result allocationPC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allocationPC
  rcases allocationPC with rfl | rfl <;> cases result <;>
    simp [arrayListInstruction, mutatorInstruction, arrayMutatorInstruction,
      collectorInstruction, arrayCollectorInstruction]

/-- `bbfa0ce4150 src/gc-wb-stock.h:26-29`,
`src/gc-stock.c:1671-1682`, `src/julia.h:1110-1171`: two valid
whole-object barriers on one old simple vector, using distinct mutator
threads. Tag 20 is SimpleVector, with one nullable slot and one pool page. -/
abbrev raceConfig : Config :=
  { objects := 1, threads := 2, slots := 1, pages := 1, arrays := 0, addresses := 0
    datatypes := 1, genericMemories := 1
    layout := fun _ =>
      { kind := .simpleVector, sizeWords := 1, npointers := 1, pointerOffsets := [0], length := 1 }
    datatypeLayout := fun _ =>
      { kind := .inlineMemory, sizeWords := 1, npointers := 1, pointerOffsets := [0], length := 1 }
    memoryDatatype := fun _ => 0, memoryObject := fun _ => 0
    memoryOwner := fun _ => 0, memoryDataAddress := fun _ => 0, memoryLength := fun _ => 1
    field := fun _ offset => if offset = 0 then some 0 else none
    owner := fun _ => 0
    slotAtomic := fun _ => false
    page := fun _ => some 0
    immutable := fun _ => false }

private def raceCall : Call raceConfig := { kind := .object, parent := 0 }
private def raceMutator : Mutator raceConfig := { call := raceCall, pc := .objectGC }
private def raceOld : Observation raceConfig := { header := { gc := .oldMarked, tag := 20 } }
private def raceRemembered : Observation raceConfig := { header := { gc := .marked, tag := 20 } }

private def raceInitialCandidate : Candidate (Location raceConfig) (Value raceConfig) :=
  ⟨#[{ thread := 0, action := .init (.header 0) (.header { gc := .oldMarked, tag := 20 }) }]⟩

private def raceSchedule : List (MutatorSelection raceConfig) :=
  [ { tid := 0, observation := raceOld, choice := { readFrom := some 0 } },
    { tid := 1, observation := raceOld, choice := { readFrom := some 0 } },
    { tid := 0, observation := raceOld, choice := { readFrom := some 0, mo := 1 } },
    { tid := 1, observation := raceRemembered, choice := { readFrom := some 3, mo := 2 } } ]

/-- `bbfa0ce4150 src/gc-wb-stock.h:28`,
`src/gc-stock.c:1679`: both fast checks read the old parent; the first
relaxed fetch-and claims queueing, and the second loses the claim. Each
RMW reads its immediate modification-order predecessor. -/
abbrev headerRaceCandidate : Candidate (Location raceConfig) (Value raceConfig) :=
  ⟨#[
    { thread := 0, action := .init (.header 0) (.header { gc := .oldMarked, tag := 20 }) },
    { thread := 1, action := .plainLoad (.header 0) (.header { gc := .oldMarked, tag := 20 }), readFrom := some 0 },
    { thread := 2, action := .plainLoad (.header 0) (.header { gc := .oldMarked, tag := 20 }), readFrom := some 0 },
    { thread := 1, action := .rmw (.header 0) .relaxed (.header { gc := .oldMarked, tag := 20 }) (.header { gc := .marked, tag := 20 }),
      readFrom := some 0, mo := 1, dependsOn := [1] },
    { thread := 2, action := .rmw (.header 0) .relaxed (.header { gc := .marked, tag := 20 }) (.header { gc := .marked, tag := 20 }),
      readFrom := some 3, mo := 2, dependsOn := [2] } ]⟩

/-- `bbfa0ce4150 src/gc-wb-stock.h:26-29`,
`src/gc-stock.c:1679`: the race witness follows actual source PCs, including
the atomic loser. The history ends before the winner's remset append. -/
theorem headerRace_follows_source :
    (mutatorInstruction raceConfig 0 raceMutator raceOld).next.pc = .rootFetchAnd ∧
    (mutatorInstruction raceConfig 1 raceMutator raceOld).next.pc = .rootFetchAnd ∧
    (mutatorInstruction raceConfig 0
      (mutatorInstruction raceConfig 0 raceMutator raceOld).next raceOld).action =
        some (headerRaceCandidate.event 3).action ∧
    (mutatorInstruction raceConfig 1
      (mutatorInstruction raceConfig 1 raceMutator raceOld).next raceRemembered).action =
        some (headerRaceCandidate.event 4).action := by decide

/-- `bbfa0ce4150 src/gc-wb-stock.h:26-29`, `src/gc-stock.c:1679`:
the candidate is the replay of its actual source instruction schedule. -/
theorem headerRace_replay :
    (replayMutators raceConfig raceSchedule
      (raceInitialCandidate, fun _ => raceMutator)).1 = headerRaceCandidate := by rfl

/-- `bbfa0ce4150 src/gc-wb-stock.h:28`, `src/gc-stock.c:1679`: read-from
sources match each read class, including neutral initialization seeds. -/
theorem headerRace_consistent : headerRaceCandidate.consistent = true := by decide

theorem headerRace_not_declaredAccessTyped :
    ¬ headerRaceCandidate.DeclaredAccessTyped (declaredAccessClass raceConfig) := by
  unfold Candidate.DeclaredAccessTyped
  decide

theorem headerRace_not_raceFree : headerRaceCandidate.dataRaceFree = false := by decide

/-- `bbfa0ce4150 src/julia.h:171-187`, `src/gc-wb-stock.h:19-29`,
`src/gc-stock.c:1675-1679`: consistent pre-undefined concurrent
whole-object barrier source replays must be free of C11 data races. -/
def HeaderAccessDataRaceFreedom : Prop :=
  ∀ (c : Config) (initial : Candidate (Location c) (Value c))
      (threads : ThreadId c → Mutator c) (schedule : List (MutatorSelection c)),
    (∀ event ∈ initial.events.toList, event.action.isInit = true) →
    (∀ tid, (threads tid).pc = entryPC (threads tid).call.kind ∧ CallValid c (threads tid).call) →
    (∀ selection ∈ schedule, ∀ call, selection.beginCall = some call → CallValid c call) →
    let candidate := (replayMutators c schedule (initial, threads)).1
    candidate.consistent = true → candidate.dataRaceFree = true

theorem headerAccessDataRaceFreedom_refuted : ¬ HeaderAccessDataRaceFreedom := by
  intro all
  have initOnly : ∀ event ∈ raceInitialCandidate.events.toList, event.action.isInit = true := by
    simp [raceInitialCandidate, Action.isInit]
  have sourceValid : ∀ tid : ThreadId raceConfig,
      raceMutator.pc = entryPC raceMutator.call.kind ∧ CallValid raceConfig raceMutator.call := by
    intro tid
    exact ⟨rfl, by simp [CallValid, CallPointerActionsTyped, Call.scanSlots,
      Call.copyPairs, raceMutator, raceCall]⟩
  have validStarts : ∀ selection ∈ raceSchedule, ∀ call,
      selection.beginCall = some call → CallValid raceConfig call := by
    simp [raceSchedule, CallValid, CallPointerActionsTyped, Call.scanSlots, Call.copyPairs]
  have bad := all raceConfig raceInitialCandidate (fun _ => raceMutator) raceSchedule
    initOnly sourceValid validStarts
  rw [headerRace_replay] at bad
  have bad := bad headerRace_consistent
  rw [headerRace_not_raceFree] at bad
  contradiction


end JuliaLean.CRuntime.WriteBarrier
