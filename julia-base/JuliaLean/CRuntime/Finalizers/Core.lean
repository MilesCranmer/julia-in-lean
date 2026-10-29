import JuliaLean.Registry.Types

/-!
Finalizer protocol at Julia `bbfa0ce4150`:
`gc-common.c:155-167,191-340,409-526`, `gc-common.h:183-215`,
`gc-stock.c:2362-2404,3182-3232,3409-3444`, and
`support/arraylist.c:16-78`. Published per-thread lengths use acquire/release;
cross-thread compaction publishes by compare-exchange; the pending flag is
relaxed. Lists retain zeroed holes when a stale owner append follows compaction.
Copied arrays record inline or heap backing identity and the two GC-frame
header cells installed by `jl_gc_push_arraylist`.
`PairSlot` represents two raw pointer cells, so length events use twice the
logical pair count. `GCFrameHeader` abstracts the encoded frame tag and any
non-finalizer frames elsewhere on the task GC stack.
-/

namespace JuliaLean.CRuntime.Finalizers

inductive Color where
  | white | youngMarked | oldMarked
  deriving BEq, DecidableEq, Repr

structure Entry where
  serial : Nat
  object : Nat
  function : Nat
  tagBits : BitVec 2 := 0
  deriving BEq, DecidableEq, Repr

structure TaggedObject where
  serial : Nat
  object : Nat
  tagBits : BitVec 2
  deriving DecidableEq, Repr

structure TaggedFunction where
  serial : Nat
  function : Nat
  deriving DecidableEq, Repr

inductive ArrayBacking where
  | inline (buffer : Nat)
  | heap (allocation : Nat)
  deriving DecidableEq, Repr

def ArrayBacking.identity : ArrayBacking → Nat
  | .inline buffer => buffer
  | .heap allocation => allocation

structure GCFrameHeader where
  encodedSlots : Nat
  previousFrame : Option Nat
  deriving DecidableEq, Repr

structure PairSlot where
  objectCell : Option TaggedObject := none
  functionCell : Option TaggedFunction := none
  deriving Inhabited, DecidableEq, Repr

def Entry.validTag (entry : Entry) : Prop :=
  entry.tagBits = 0 ∨ entry.tagBits = 1 ∨ entry.tagBits = 2

def Entry.isCFunction (entry : Entry) : Bool := entry.tagBits == 1

def Entry.isCObject (entry : Entry) : Bool := entry.tagBits == 2

def Entry.pair (entry : Entry) : PairSlot :=
  ⟨some ⟨entry.serial, entry.object, entry.tagBits⟩,
    some ⟨entry.serial, entry.function⟩⟩

def PairSlot.entry? (slot : PairSlot) : Option Entry :=
  match slot.objectCell, slot.functionCell with
  | some object, some function =>
      if object.serial = function.serial then
        some ⟨object.serial, object.object, function.function, object.tagBits⟩
      else none
  | _, _ => none

inductive Actor where
  | mutator (tid : Nat)
  | collector
  deriving DecidableEq, Repr

inductive Lifecycle where
  | absent | registering | owner (tid : Nat) | marked | pending
  | finalizeEscrow (tid : Nat) | runEscrow (tid : Nat)
  | finalizeCompactEscrow (tid : Nat) | collectorCompactEscrow
  | pendingEscrow | markedEscrow
  | frame (tid : Nat) | running (tid : Nat) | completed
  deriving DecidableEq, Repr

inductive ListId where
  | thread (tid : Nat)
  | marked
  deriving BEq, DecidableEq, Repr

def ListId.lifecycle : ListId → Lifecycle
  | .thread tid => .owner tid
  | .marked => .marked

inductive QueueId where
  | list (list : ListId)
  | toFinalize
  | copied
  deriving DecidableEq, Repr

inductive Order where
  | relaxed | acquire | release | seqCst
  deriving DecidableEq, Repr

inductive Event where
  | lengthLoad (actor : Actor) (list : ListId) (order : Order) (value : Nat)
  | lengthStore (actor : Actor) (list : ListId) (order : Order) (value : Nat)
  | lengthCAS (actor : Actor) (list : ListId) (order : Order)
      (expected desired observed : Nat) (success : Bool)
  | objectLoad (actor : Actor) (queue : QueueId) (index : Nat)
      (object : Option TaggedObject)
  | functionLoad (actor : Actor) (queue : QueueId) (index : Nat)
      (function : Option TaggedFunction)
  | objectStore (actor : Actor) (queue : QueueId) (index : Nat) (object : TaggedObject)
  | functionStore (actor : Actor) (queue : QueueId) (index : Nat)
      (function : TaggedFunction)
  | zeroRange (actor : Actor) (list : ListId) (first count : Nat)
  | pendingLoad (actor : Actor) (value : Bool)
  | pendingStore (actor : Actor) (value : Bool)
  | lock (actor : Actor)
  | unlock (actor : Actor)
  | queueBarrier (actor : Actor)
  | rootQueue (actor : Actor) (backing : ArrayBacking)
      (header : GCFrameHeader) (cells : List PairSlot)
  | callbackStart (actor : Actor) (entry : Entry)
  | callbackFinish (actor : Actor) (entry : Entry)
  | markRoot (object : Nat)
  deriving DecidableEq, Repr

structure RunFrame where
  copied : List Entry
  cells : List PairSlot
  queue : List Entry
  running : Option Entry
  restoreInFinalizer : Option Bool
  backing : ArrayBacking
  header : Option GCFrameHeader
  deriving DecidableEq, Repr

def RunFrame.WellFormed (frame : RunFrame) : Prop :=
  frame.cells = frame.copied.map Entry.pair ∧
    ∀ header, frame.header = some header →
      header.encodedSlots = frame.cells.length * 2

def rootedFrameChain : List RunFrame → Option Nat → Prop
  | [], _ => True
  | frame :: rest, head =>
      frame.WellFormed ∧
        match frame.header with
        | none => rootedFrameChain rest head
        | some header =>
            head = some frame.backing.identity ∧
              rootedFrameChain rest header.previousFrame

inductive PC where
  | idle
  | pendingLoad
  | pendingGuard
  | addAcquire (entry : Entry)
  | addLock (entry : Entry) (observed : Nat)
  | addReload (entry : Entry)
  | addGrow (entry : Entry) (observed : Nat)
  | addUnlock (entry : Entry) (observed : Nat)
  | addWriteObject (entry : Entry) (observed : Nat)
  | addWriteFunction (entry : Entry) (observed : Nat)
  | addRelease (entry : Entry) (observed : Nat)
  | finalizeLock (target caller : Nat)
  | finalizeNext (target caller : Nat) (remaining : List ListId) (copied : List Entry)
  | finalizeAcquire (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied : List Entry) (needSync : Bool)
  | finalizeScan (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat)
  | finalizeReadFunction (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (object : TaggedObject)
  | finalizeInspect (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (entry : Entry) (isMatch : Bool)
  | finalizeCopyObject (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (entry : Entry)
  | finalizeCopyFunction (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (entry : Entry)
  | finalizeKeepObject (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (entry : Entry)
  | finalizeKeepFunction (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength index : Nat) (entry : Entry)
  | finalizeZero (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength zeroIndex : Nat)
  | finalizePublish (target caller : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry)
      (needSync : Bool) (oldLength : Nat)
  | runFast (finalizersThread : Bool)
  | runLock (finalizersThread : Bool)
  | runRecheck (finalizersThread : Bool)
  | runCopy (finalizersThread : Bool) (queue : List Entry)
  | runClearHint (finalizersThread : Bool) (queue : List Entry)
  | runBarrier (finalizersThread : Bool) (queue : List Entry)
  | runReset (finalizersThread : Bool) (queue : List Entry)
  | runSave (finalizersThread : Bool) (queue : List Entry)
  | rootFrame
  | unlockFrame
  | callbacks
  | callbackReturn
  | collectWait (resume : PC)
  | collectResume (resume : PC)
  | restoreFrame
  | collectBegin (full : Bool)
  | collectNext (full : Bool) (origMarked : Nat) (remaining : List ListId)
  | collectScan (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
  | collectReadFunction (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (object : TaggedObject)
  | collectClassify (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (entry : Entry) (freed old : Bool)
  | collectKeepObject (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (entry : Entry)
  | collectKeepFunction (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (entry : Entry)
  | collectScheduleObject (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (entry : Entry)
  | collectScheduleFunction (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index position : Nat)
      (entry : Entry)
  | collectPending (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
  | collectMarkedObject (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index : Nat)
      (entry : Entry)
  | collectMarkedFunction (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength index position : Nat)
      (entry : Entry)
  | collectPublish (full : Bool) (origMarked : Nat) (list : ListId)
      (remaining : List ListId) (kept : List Entry) (oldLength : Nat)
  | collectMark (origMarked : Nat)
  | collectPostRun (tid : Nat) (resume : PC)
  deriving DecidableEq, Repr

structure State where
  nThreads : Nat
  pc : Actor → PC
  returns : Actor → List PC
  threadFinalizers : Nat → List PairSlot
  publishedLength : Nat → Nat
  capacity : Nat → Nat
  markedFinalizers : List PairSlot
  markedLength : Nat
  toFinalize : List PairSlot
  pendingHint : Bool
  finalizersLock : Option Actor
  frames : Nat → List RunFrame
  gcStackHead : Nat → Option Nat
  nextBufferId : Nat
  inFinalizer : Nat → Bool
  finalizersInhibited : Nat → Nat
  heldLocks : Nat → Nat
  engineQueued : Nat → Nat
  worldStopped : Bool
  colors : Nat → Color
  markedRoots : Nat → Bool
  resetAgeRoots : List Nat
  collectorCaller : Option (Nat × PC)
  lifecycle : Nat → Lifecycle
  created : List Entry
  started : List Entry
  completed : List Entry
  events : List Event

def FrameStackWF (s : State) (tid : Nat) : Prop :=
  rootedFrameChain (s.frames tid) (s.gcStackHead tid)

def replace [DecidableEq α] (f : α → β) (key : α) (value : β) : α → β :=
  fun other => if other = key then value else f other

def State.setPC (s : State) (actor : Actor) (pc : PC) : State :=
  { s with pc := replace s.pc actor pc }

def State.setReturns (s : State) (actor : Actor) (returns : List PC) : State :=
  { s with returns := replace s.returns actor returns }

def State.enter (s : State) (actor : Actor) (pc : PC) : State :=
  (s.setReturns actor (s.pc actor :: s.returns actor)).setPC actor pc

def State.leave (s : State) (actor : Actor) : State :=
  match s.returns actor with
  | [] => s.setPC actor .idle
  | returnPC :: rest => (s.setReturns actor rest).setPC actor returnPC

def State.record (s : State) (event : Event) : State :=
  { s with events := s.events ++ [event] }

def State.setThreadFinalizers (s : State) (tid : Nat) (entries : List PairSlot) : State :=
  { s with threadFinalizers := replace s.threadFinalizers tid entries }

def State.setPublishedLength (s : State) (tid length : Nat) : State :=
  { s with publishedLength := replace s.publishedLength tid length }

def State.setCapacity (s : State) (tid capacity : Nat) : State :=
  { s with capacity := replace s.capacity tid capacity }

def State.setInFinalizer (s : State) (tid : Nat) (value : Bool) : State :=
  { s with inFinalizer := replace s.inFinalizer tid value }

def State.setFrames (s : State) (tid : Nat) (frames : List RunFrame) : State :=
  { s with frames := replace s.frames tid frames }

def State.setGCStackHead (s : State) (tid : Nat) (head : Option Nat) : State :=
  { s with gcStackHead := replace s.gcStackHead tid head }

def State.setMarkedRoot (s : State) (object : Nat) : State :=
  { s with markedRoots := replace s.markedRoots object true }

def State.setLifecycle (s : State) (serial : Nat) (stage : Lifecycle) : State :=
  { s with lifecycle := replace s.lifecycle serial stage }

def State.setLifecycleEntries (s : State) (entries : List Entry)
    (stage : Lifecycle) : State :=
  entries.foldl (fun state entry => state.setLifecycle entry.serial stage) s

def State.list (s : State) : ListId → List PairSlot
  | .thread tid => s.threadFinalizers tid
  | .marked => s.markedFinalizers

def State.setListContents (s : State) : ListId → List PairSlot → State
  | .thread tid, entries => s.setThreadFinalizers tid entries
  | .marked, entries => { s with markedFinalizers := entries }

def State.setList (s : State) : ListId → List PairSlot → State
  | .thread tid, entries => (s.setThreadFinalizers tid entries).setPublishedLength tid entries.length
  | .marked, entries => { s with markedFinalizers := entries, markedLength := entries.length }

def State.setListLength (s : State) : ListId → Nat → State
  | .thread tid, length => s.setPublishedLength tid length
  | .marked, length => { s with markedLength := length }

def listLength (s : State) : ListId → Nat
  | .thread tid => s.publishedLength tid
  | .marked => s.markedLength

def rawPairLength (pairs : Nat) : Nat := 2 * pairs

def rawListLength (s : State) (list : ListId) : Nat :=
  rawPairLength (listLength s list)

def needsSync (caller : Nat) : ListId → Bool
  | .thread owner => decide (caller ≠ owner)
  | .marked => false

def callable : PC → Bool
  | .idle | .callbacks | .callbackReturn => true
  | _ => false

def gcCallable : PC → Bool
  | .idle | .callbackReturn => true
  | _ => false

def ListId.InRange (s : State) : ListId → Prop
  | .thread tid => tid < s.nThreads
  | .marked => True

/-- The PC resumed by `State.leave` is a point where the caller may start new work. -/
def ReturnCallable (s : State) (actor : Actor) : Prop :=
  match s.returns actor with
  | [] => True
  | returnPC :: _ => callable returnPC = true

/-- Slot `index` holds exactly `entry`'s complete pair. -/
def SlotHolds (entries : List PairSlot) (index : Nat) (entry : Entry) : Prop :=
  entries[index]? = some entry.pair

/-- Slot `index` holds `entry`'s object half; its function half is not constrained. -/
def ObjectHalfAt (entries : List PairSlot) (index : Nat) (entry : Entry) : Prop :=
  ∃ slot, entries[index]? = some slot ∧
    slot.objectCell = some (TaggedObject.mk entry.serial entry.object entry.tagBits)

def PairSlot.SerialsSatisfy (slot : PairSlot) (allowed : Nat → Prop) : Prop :=
  (∀ object, slot.objectCell = some object → allowed object.serial) ∧
    ∀ function, slot.functionCell = some function → allowed function.serial

/-- Every cell present in slot `index` carries an `allowed` serial. -/
def GarbageAt (entries : List PairSlot) (index : Nat) (allowed : Nat → Prop) : Prop :=
  ∀ slot, entries[index]? = some slot → slot.SerialsSatisfy allowed

def GarbageBetween (entries : List PairSlot) (first last : Nat)
    (allowed : Nat → Prop) : Prop :=
  ∀ index, first ≤ index → index < last → GarbageAt entries index allowed

/-- Serials whose list cells a finalize scan has already copied or moved away. -/
def FinalizeGarbage (s : State) (caller serial : Nat) : Prop :=
  s.lifecycle serial = .finalizeEscrow caller ∨
    s.lifecycle serial = .finalizeCompactEscrow caller

/-- Serials whose cells in `list` a collector sweep has already moved, scheduled, or promoted. -/
def CollectGarbage (s : State) (list : ListId) (serial : Nat) : Prop :=
  s.lifecycle serial = .collectorCompactEscrow ∨ s.lifecycle serial = .pending ∨
    (s.lifecycle serial = .marked ∧ list ≠ ListId.marked)

def CompactedPrefix (entries : List PairSlot) (kept : List Entry) : Prop :=
  entries.take kept.length = kept.map Entry.pair

def NoCompletePairBetween (entries : List PairSlot) (first last : Nat) : Prop :=
  ∀ index, first ≤ index → index < last → ∀ slot, entries[index]? = some slot →
    slot.entry? = none

def NoKeptPairBetween (entries : List PairSlot) (kept : List Entry) (first last : Nat) : Prop :=
  ∀ index, first ≤ index → index < last → ∀ slot, entries[index]? = some slot →
    ∀ found, slot.entry? = some found → ∀ entry ∈ kept, found.serial ≠ entry.serial

def NoCompleteCopy (entries : List PairSlot) (serial : Nat) : Prop :=
  ∀ slot ∈ entries, ∀ found, slot.entry? = some found → found.serial ≠ serial

def SerialFresh (entries : List Entry) (serial : Nat) : Prop :=
  ∀ entry ∈ entries, entry.serial ≠ serial

def Entry.matchesObject (entry : Entry) (object : Nat) : Bool :=
  (entry.tagBits == 0 || entry.tagBits == 1) && entry.object == object

def Entry.roots (entry : Entry) : List Nat :=
  if entry.isCObject then [entry.function]
  else if entry.isCFunction then [entry.object]
  else [entry.object, entry.function]

def Color.marked : Color → Bool
  | .white => false
  | .youngMarked | .oldMarked => true

def Entry.freed (s : State) (entry : Entry) : Bool :=
  entry.isCObject || !(s.colors entry.object).marked

def Entry.oldForFinalizers (s : State) (list : ListId) (entry : Entry) : Bool :=
  !entry.isCObject && list != .marked && s.colors entry.object == .oldMarked &&
    (entry.isCFunction || s.colors entry.function == .oldMarked)

def sweepTargets (s : State) (full : Bool) : List ListId :=
  (List.range s.nThreads).map .thread ++ if full then [.marked] else []

def finalizeTargets (s : State) : List ListId :=
  (List.range s.nThreads).map .thread ++ [.marked]

def present (entries : List PairSlot) : List Entry :=
  entries.filterMap PairSlot.entry?

def publishedPresent (s : State) (list : ListId) : List Entry :=
  present ((s.list list).take (listLength s list))

def finalizePartition (target : Nat) : List PairSlot → List Entry × List Entry
  | [] => ([], [])
  | slot :: rest =>
      let tail := finalizePartition target rest
      match slot.entry? with
      | none => tail
      | some entry =>
          if entry.matchesObject target then (tail.1, entry :: tail.2)
          else (entry :: tail.1, tail.2)

def compactPublished (current : List PairSlot) (kept : List Entry)
    (oldLength : Nat) : List PairSlot :=
  kept.map Entry.pair ++ List.replicate (oldLength - kept.length) default ++
    current.drop oldLength

def writeSlot (current : List PairSlot) (index : Nat) (slot : PairSlot) : List PairSlot :=
  if index < current.length then
    current.take index ++ [slot] ++ current.drop (index + 1)
  else
    current ++ List.replicate (index - current.length) default ++ [slot]

def writeObjectCell (current : List PairSlot) (index : Nat) (entry : Entry) : List PairSlot :=
  let slot := (current[index]?).getD default
  writeSlot current index
    { slot with objectCell := some ⟨entry.serial, entry.object, entry.tagBits⟩ }

def writeFunctionCell (current : List PairSlot) (index : Nat) (entry : Entry) : List PairSlot :=
  let slot := (current[index]?).getD default
  writeSlot current index
    { slot with functionCell := some ⟨entry.serial, entry.function⟩ }

def popLast? (entries : List α) : Option (List α × α) :=
  match entries.reverse with
  | [] => none
  | last :: reverseFront => some (reverseFront.reverse, last)

def topFrame? (s : State) (tid : Nat) : Option RunFrame :=
  (s.frames tid).head?

def State.replaceTopFrame (s : State) (tid : Nat) (frame : RunFrame) : State :=
  match s.frames tid with
  | [] => s.setFrames tid [frame]
  | _ :: rest => s.setFrames tid (frame :: rest)

def State.pushFrame (s : State) (tid : Nat) (frame : RunFrame) : State :=
  s.setFrames tid (frame :: s.frames tid)

def frameBacking (identity entries : Nat) : ArrayBacking :=
  if entries * 2 + 2 ≤ 29 then .inline identity else .heap identity

def State.pushNewFrame (s : State) (tid : Nat) (copied : List Entry)
    (restoreInFinalizer : Option Bool) : State :=
  let frame : RunFrame :=
    { copied := copied
      cells := copied.map Entry.pair
      queue := copied
      running := none
      restoreInFinalizer := restoreInFinalizer
      backing := frameBacking s.nextBufferId copied.length
      header := none }
  { s.pushFrame tid frame with nextBufferId := s.nextBufferId + 1 }

def State.popFrame (s : State) (tid : Nat) : State :=
  match s.frames tid with
  | [] => s
  | frame :: rest =>
      let popped := s.setFrames tid rest
      match frame.header with
      | none => popped
      | some header => popped.setGCStackHead tid header.previousFrame

def markObjects (s : State) : List Nat → Bool → State
  | [], _ => s
  | object :: rest, resetAge =>
      let marked := (s.setMarkedRoot object).record (.markRoot object)
      let marked := if resetAge then
        { marked with resetAgeRoots := marked.resetAgeRoots ++ [object] }
      else marked
      markObjects marked rest resetAge

def markEntries (s : State) : List Entry → Bool → State
  | [], _ => s
  | entry :: rest, resetAge =>
      markEntries (markObjects s entry.roots resetAge) rest resetAge

def RunFrame.collectorEntries (frame : RunFrame) : List Entry :=
  if frame.header.isSome then present frame.cells else []

def callbackCollectorRoots (s : State) : List Entry :=
  (List.range s.nThreads).flatMap fun tid =>
    (s.frames tid).flatMap RunFrame.collectorEntries

def collectorRoots (s : State) (origMarked : Nat) : List Entry :=
  (List.range s.nThreads).flatMap (fun tid => publishedPresent s (.thread tid)) ++
    (publishedPresent s .marked).drop origMarked ++ present s.toFinalize ++
    callbackCollectorRoots s

def markCollectorFinalizers (s : State) (origMarked : Nat) : State :=
  let regular := (List.range s.nThreads).flatMap
    (fun tid => publishedPresent s (.thread tid)) ++
    (publishedPresent s .marked).drop origMarked ++ callbackCollectorRoots s
  markEntries (markEntries s regular false) (present s.toFinalize) true

inductive Step : State → Actor → State → Prop where
  | beginAdd (s : State) (tid : Nat) (entry : Entry)
      (tidBound : tid < s.nThreads)
      (callablePC : callable (s.pc (.mutator tid)) = true)
      (running : s.worldStopped = false)
      (validTag : entry.validTag)
      (absent : s.lifecycle entry.serial = .absent)
      (freshSerial : ∀ existing ∈ s.created, existing.serial ≠ entry.serial) :
      Step s (.mutator tid)
        { (s.setLifecycle entry.serial .registering).enter (.mutator tid) (.addAcquire entry) with
          created := s.created ++ [entry] }
  | addAcquireNoGrow (s : State) (tid : Nat) (entry : Entry)
      (pc : s.pc (.mutator tid) = .addAcquire entry)
      (space : s.publishedLength tid + 1 ≤ s.capacity tid) :
      Step s (.mutator tid)
        (((s.setPC (.mutator tid) (.addWriteObject entry (s.publishedLength tid))).record
          (.lengthLoad (.mutator tid) (.thread tid) .acquire
            (rawPairLength (s.publishedLength tid)))))
  | addAcquireGrow (s : State) (tid : Nat) (entry : Entry)
      (pc : s.pc (.mutator tid) = .addAcquire entry)
      (full : s.capacity tid < s.publishedLength tid + 1) :
      Step s (.mutator tid)
        ((s.setPC (.mutator tid) (.addLock entry (s.publishedLength tid))).record
          (.lengthLoad (.mutator tid) (.thread tid) .acquire
            (rawPairLength (s.publishedLength tid))))
  | addLock (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addLock entry observed)
      (free : s.finalizersLock = none) :
      Step s (.mutator tid)
        (({ s.setPC (.mutator tid) (.addReload entry) with
          finalizersLock := some (.mutator tid) }).record (.lock (.mutator tid)))
  | addReload (s : State) (tid : Nat) (entry : Entry)
      (pc : s.pc (.mutator tid) = .addReload entry) :
      Step s (.mutator tid)
        ((s.setPC (.mutator tid) (.addGrow entry (s.publishedLength tid))).record
          (.lengthLoad (.mutator tid) (.thread tid) .relaxed
            (rawPairLength (s.publishedLength tid))))
  | addGrow (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addGrow entry observed) :
      Step s (.mutator tid)
        ((s.setCapacity tid (Nat.max (s.capacity tid * 2) (observed + 1))).setPC
          (.mutator tid) (.addUnlock entry observed))
  | addUnlock (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addUnlock entry observed)
      (owns : s.finalizersLock = some (.mutator tid)) :
      Step s (.mutator tid)
        (({ s.setPC (.mutator tid) (.addWriteObject entry observed) with
          finalizersLock := none }).record (.unlock (.mutator tid)))
  | addWriteObject (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addWriteObject entry observed)
      (stage : s.lifecycle entry.serial = .registering)
      (published : s.publishedLength tid ≤ observed) :
      Step s (.mutator tid)
        (((s.setThreadFinalizers tid (writeObjectCell (s.threadFinalizers tid) observed entry)).setPC
          (.mutator tid) (.addWriteFunction entry observed)).record
          (.objectStore (.mutator tid) (.list (.thread tid)) observed
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | addWriteFunction (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addWriteFunction entry observed)
      (stage : s.lifecycle entry.serial = .registering)
      (published : s.publishedLength tid ≤ observed)
      (objectHalf : ObjectHalfAt (s.threadFinalizers tid) observed entry) :
      Step s (.mutator tid)
        (((s.setThreadFinalizers tid (writeFunctionCell (s.threadFinalizers tid) observed entry)).setPC
          (.mutator tid) (.addRelease entry observed)).record
          (.functionStore (.mutator tid) (.list (.thread tid)) observed
            ⟨entry.serial, entry.function⟩))
  | addRelease (s : State) (tid : Nat) (entry : Entry) (observed : Nat)
      (pc : s.pc (.mutator tid) = .addRelease entry observed)
      (stage : s.lifecycle entry.serial = .registering)
      (tidBound : tid < s.nThreads)
      (published : s.publishedLength tid ≤ observed)
      (written : SlotHolds (s.threadFinalizers tid) observed entry)
      (holes : NoCompletePairBetween (s.threadFinalizers tid) (s.publishedLength tid) observed)
      (returnCallable : ReturnCallable s (.mutator tid)) :
      Step s (.mutator tid)
        ((((s.setPublishedLength tid (observed + 1)).setLifecycle entry.serial
          (.owner tid)).leave (.mutator tid)).record
          (.lengthStore (.mutator tid) (.thread tid) .release
            (rawPairLength (observed + 1))))
  | beginFinalize (s : State) (caller target : Nat)
      (callerBound : caller < s.nThreads)
      (callablePC : callable (s.pc (.mutator caller)) = true)
      (running : s.worldStopped = false) :
      Step s (.mutator caller)
        (s.enter (.mutator caller) (.finalizeLock target caller))
  | finalizeLock (s : State) (caller target : Nat)
      (pc : s.pc (.mutator caller) = .finalizeLock target caller)
      (free : s.finalizersLock = none) :
      Step s (.mutator caller)
        (({ s.setPC (.mutator caller)
            (.finalizeNext target caller (finalizeTargets s) []) with
          finalizersLock := some (.mutator caller) }).record (.lock (.mutator caller)))
  | finalizeNextDoneEmpty (s : State) (caller target : Nat)
      (pc : s.pc (.mutator caller) = .finalizeNext target caller [] [])
      (owns : s.finalizersLock = some (.mutator caller))
      (returnCallable : ReturnCallable s (.mutator caller)) :
      Step s (.mutator caller)
        (({ s.leave (.mutator caller) with finalizersLock := none }).record
          (.unlock (.mutator caller)))
  | finalizeNextDoneCopied (s : State) (caller target : Nat) (copied : List Entry)
      (pc : s.pc (.mutator caller) = .finalizeNext target caller [] copied)
      (nonempty : copied ≠ [])
      (sourceStage : ∀ entry ∈ copied,
        s.lifecycle entry.serial = .finalizeEscrow caller)
      (callerBound : caller < s.nThreads) :
      Step s (.mutator caller)
        (((s.setLifecycleEntries copied (.frame caller)).pushNewFrame caller copied none).setPC
          (.mutator caller) .rootFrame)
  | finalizeAcquire (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied : List Entry)
      (pc : s.pc (.mutator caller) = .finalizeNext target caller (list :: remaining) copied) :
      Step s (.mutator caller)
        ((s.setPC (.mutator caller)
          (.finalizeScan target caller list remaining copied [] (needsSync caller list)
            (listLength s list) 0)).record
          (.lengthLoad (.mutator caller) list
            (if needsSync caller list then .acquire else .relaxed)
            (rawListLength s list)))
  | finalizeScanObject (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (slot : PairSlot) (object : TaggedObject)
      (pc : s.pc (.mutator caller) =
        .finalizeScan target caller list remaining copied kept needSync oldLength index)
      (inside : index < oldLength) (item : (s.list list)[index]? = some slot)
      (loaded : slot.objectCell = some object)
      (listBound : list.InRange s) :
      Step s (.mutator caller)
        ((s.setPC (.mutator caller)
          (.finalizeReadFunction target caller list remaining copied kept needSync oldLength index
            object)).record
          (.objectLoad (.mutator caller) (.list list) index (some object)))
  | finalizeReadFunctionStep (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (object : TaggedObject) (slot : PairSlot)
      (function : TaggedFunction) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeReadFunction target caller list remaining copied kept needSync oldLength index object)
      (item : (s.list list)[index]? = some slot)
      (loaded : slot.functionCell = some function)
      (serial : object.serial = function.serial)
      (decoded : entry = ⟨object.serial, object.object, function.function, object.tagBits⟩) :
      Step s (.mutator caller)
        ((s.setPC (.mutator caller)
          (.finalizeInspect target caller list remaining copied kept needSync oldLength index
            entry (entry.matchesObject target))).record
          (.functionLoad (.mutator caller) (.list list) index (some function)))
  | finalizeInspectMatched (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeInspect target caller list remaining copied kept needSync oldLength index entry true) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizeCopyObject target caller list remaining copied kept needSync oldLength index entry))
  | finalizeInspectKept (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeInspect target caller list remaining copied kept needSync oldLength index entry false) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizeKeepObject target caller list remaining copied kept needSync oldLength index entry))
  | finalizeCopyObject (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeCopyObject target caller list remaining copied kept needSync oldLength index entry)
      (stage : s.lifecycle entry.serial = list.lifecycle) :
      Step s (.mutator caller)
        ((s.setPC (.mutator caller)
          (.finalizeCopyFunction target caller list remaining copied kept needSync oldLength index entry)).record
          (.objectStore (.mutator caller) .copied copied.length
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | finalizeCopyFunction (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeCopyFunction target caller list remaining copied kept needSync oldLength index entry)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (callerBound : caller < s.nThreads)
      (source : SlotHolds (s.list list) index entry) :
      Step s (.mutator caller)
        (((s.setLifecycle entry.serial (.finalizeEscrow caller)).setPC (.mutator caller)
          (.finalizeScan target caller list remaining (copied ++ [entry]) kept
            needSync oldLength (index + 1))).record
          (.functionStore (.mutator caller) .copied copied.length
            ⟨entry.serial, entry.function⟩))
  | finalizeKeepObjectMoved (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeKeepObject target caller list remaining copied kept needSync oldLength index entry)
      (moved : kept.length < index)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (destination : GarbageAt (s.list list) kept.length (FinalizeGarbage s caller)) :
      Step s (.mutator caller)
        (((s.setListContents list (writeObjectCell (s.list list) kept.length entry)).setPC
          (.mutator caller)
          (.finalizeKeepFunction target caller list remaining copied kept needSync oldLength index entry)).record
          (.objectStore (.mutator caller) (.list list) kept.length
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | finalizeKeepObjectSame (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeKeepObject target caller list remaining copied kept needSync oldLength index entry)
      (same : kept.length = index) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizeKeepFunction target caller list remaining copied kept needSync oldLength index entry))
  | finalizeKeepFunctionMoved (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeKeepFunction target caller list remaining copied kept needSync oldLength index entry)
      (moved : kept.length < index)
      (owns : s.finalizersLock = some (.mutator caller))
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (partialDestination : ObjectHalfAt (s.list list) kept.length entry)
      (destinationBound : kept.length < listLength s list)
      (fresh : SerialFresh kept entry.serial) :
      Step s (.mutator caller)
        ((((s.setListContents list (writeFunctionCell (s.list list) kept.length entry)).setLifecycle
          entry.serial (.finalizeCompactEscrow caller)).setPC
          (.mutator caller)
          (.finalizeScan target caller list remaining copied (kept ++ [entry])
            needSync oldLength (index + 1))).record
          (.functionStore (.mutator caller) (.list list) kept.length
            ⟨entry.serial, entry.function⟩))
  | finalizeKeepFunctionSame (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc (.mutator caller) =
        .finalizeKeepFunction target caller list remaining copied kept needSync oldLength index entry)
      (same : kept.length = index)
      (stage : s.lifecycle entry.serial = list.lifecycle) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizeScan target caller list remaining copied (kept ++ [entry])
            needSync oldLength (index + 1)))
  | finalizeScanEmpty (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength index : Nat) (slot : PairSlot)
      (pc : s.pc (.mutator caller) =
        .finalizeScan target caller list remaining copied kept needSync oldLength index)
      (inside : index < oldLength) (item : (s.list list)[index]? = some slot)
      (empty : slot.objectCell = none) :
      Step s (.mutator caller)
        ((s.setPC (.mutator caller)
          (.finalizeScan target caller list remaining copied kept
            needSync oldLength (index + 1))).record
          (.objectLoad (.mutator caller) (.list list) index none))
  | finalizeScanDone (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizeScan target caller list remaining copied kept needSync oldLength oldLength) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizeZero target caller list remaining copied kept needSync oldLength kept.length))
  | finalizeZeroSlot (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength zeroIndex : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizeZero target caller list remaining copied kept needSync oldLength zeroIndex)
      (inside : zeroIndex < oldLength)
      (garbage : GarbageAt (s.list list) zeroIndex (FinalizeGarbage s caller))
      (afterKept : kept.length ≤ zeroIndex) :
      Step s (.mutator caller)
        (((s.setListContents list (writeSlot (s.list list) zeroIndex default)).setPC
          (.mutator caller)
          (.finalizeZero target caller list remaining copied kept needSync oldLength
            (zeroIndex + 1))).record
          (.zeroRange (.mutator caller) list zeroIndex 1))
  | finalizeZeroDone (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (needSync : Bool)
      (oldLength : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizeZero target caller list remaining copied kept needSync oldLength oldLength) :
      Step s (.mutator caller)
        (s.setPC (.mutator caller)
          (.finalizePublish target caller list remaining copied kept needSync oldLength))
  | finalizePublishCASSuccess (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (oldLength : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizePublish target caller list remaining copied kept true oldLength)
      (observed : listLength s list = oldLength)
      (keptStage : ∀ entry ∈ kept, s.lifecycle entry.serial = list.lifecycle ∨
        s.lifecycle entry.serial = .finalizeCompactEscrow caller)
      (owns : s.finalizersLock = some (.mutator caller))
      (keptBound : kept.length ≤ oldLength)
      (compacted : CompactedPrefix (s.list list) kept)
      (tail : GarbageBetween (s.list list) kept.length oldLength fun _ => False) :
      Step s (.mutator caller)
        ((((s.setLifecycleEntries kept list.lifecycle).setListLength list kept.length).setPC
          (.mutator caller)
          (.finalizeNext target caller remaining copied)).record
          (.lengthCAS (.mutator caller) list .seqCst
            (rawPairLength oldLength) (rawPairLength kept.length)
            (rawPairLength oldLength) true))
  | finalizePublishCASFailure (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (oldLength actual : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizePublish target caller list remaining copied kept true oldLength)
      (observed : listLength s list = actual) (failed : actual ≠ oldLength)
      (keptStage : ∀ entry ∈ kept, s.lifecycle entry.serial = list.lifecycle ∨
        s.lifecycle entry.serial = .finalizeCompactEscrow caller)
      (owns : s.finalizersLock = some (.mutator caller))
      (keptBound : kept.length ≤ oldLength)
      (compacted : CompactedPrefix (s.list list) kept)
      (tail : GarbageBetween (s.list list) kept.length oldLength fun _ => False)
      (appended : NoKeptPairBetween (s.list list) kept oldLength actual) :
      Step s (.mutator caller)
        (((s.setLifecycleEntries kept list.lifecycle).setPC (.mutator caller)
          (.finalizeNext target caller remaining copied)).record
          (.lengthCAS (.mutator caller) list .seqCst
            (rawPairLength oldLength) (rawPairLength kept.length)
            (rawPairLength actual) false))
  | finalizePublishPlain (s : State) (caller target : Nat) (list : ListId)
      (remaining : List ListId) (copied kept : List Entry) (oldLength : Nat)
      (pc : s.pc (.mutator caller) =
        .finalizePublish target caller list remaining copied kept false oldLength)
      (keptStage : ∀ entry ∈ kept, s.lifecycle entry.serial = list.lifecycle ∨
        s.lifecycle entry.serial = .finalizeCompactEscrow caller)
      (owns : s.finalizersLock = some (.mutator caller))
      (observed : listLength s list = oldLength)
      (keptBound : kept.length ≤ oldLength)
      (compacted : CompactedPrefix (s.list list) kept)
      (tail : GarbageBetween (s.list list) kept.length oldLength fun _ => False) :
      Step s (.mutator caller)
        ((((s.setLifecycleEntries kept list.lifecycle).setListLength list kept.length).setPC
          (.mutator caller)
          (.finalizeNext target caller remaining copied)).record
          (.lengthStore (.mutator caller) list .relaxed (rawPairLength kept.length)))
  | beginRun (s : State) (tid : Nat) (finalizersThread : Bool)
      (tidBound : tid < s.nThreads)
      (callablePC : callable (s.pc (.mutator tid)) = true)
      (running : s.worldStopped = false) :
      Step s (.mutator tid) (s.enter (.mutator tid) (.runFast finalizersThread))
  | beginPendingCheck (s : State) (tid : Nat)
      (tidBound : tid < s.nThreads)
      (callablePC : callable (s.pc (.mutator tid)) = true)
      (running : s.worldStopped = false) :
      Step s (.mutator tid) (s.enter (.mutator tid) .pendingLoad)
  | pendingLoadEmpty (s : State) (tid : Nat)
      (pc : s.pc (.mutator tid) = .pendingLoad) (empty : s.pendingHint = false)
      (returnCallable : ReturnCallable s (.mutator tid)) :
      Step s (.mutator tid)
        ((s.leave (.mutator tid)).record (.pendingLoad (.mutator tid) false))
  | pendingLoadWork (s : State) (tid : Nat)
      (pc : s.pc (.mutator tid) = .pendingLoad) (work : s.pendingHint = true) :
      Step s (.mutator tid)
        ((s.setPC (.mutator tid) .pendingGuard).record (.pendingLoad (.mutator tid) true))
  | pendingGuardRun (s : State) (tid : Nat)
      (pc : s.pc (.mutator tid) = .pendingGuard)
      (outside : s.inFinalizer tid = false) (unlocked : s.heldLocks tid = 0)
      (enabled : s.finalizersInhibited tid = 0) (queueEmpty : s.engineQueued tid = 0) :
      Step s (.mutator tid) (s.setPC (.mutator tid) (.runFast false))
  | pendingGuardSkip (s : State) (tid : Nat)
      (pc : s.pc (.mutator tid) = .pendingGuard)
      (blocked : s.inFinalizer tid = true ∨ s.heldLocks tid ≠ 0 ∨
        s.finalizersInhibited tid ≠ 0 ∨ s.engineQueued tid ≠ 0)
      (returnCallable : ReturnCallable s (.mutator tid)) :
      Step s (.mutator tid) (s.leave (.mutator tid))
  | runFastEmpty (s : State) (tid : Nat) (finalizersThread : Bool)
      (pc : s.pc (.mutator tid) = .runFast finalizersThread)
      (empty : s.toFinalize = [])
      (returnCallable : ReturnCallable s (.mutator tid)) :
      Step s (.mutator tid) (s.leave (.mutator tid))
  | runFastWork (s : State) (tid : Nat) (finalizersThread : Bool)
      (pc : s.pc (.mutator tid) = .runFast finalizersThread)
      (work : s.toFinalize ≠ []) :
      Step s (.mutator tid) (s.setPC (.mutator tid) (.runLock finalizersThread))
  | runLock (s : State) (tid : Nat) (finalizersThread : Bool)
      (pc : s.pc (.mutator tid) = .runLock finalizersThread)
      (free : s.finalizersLock = none) :
      Step s (.mutator tid)
        (({ s.setPC (.mutator tid) (.runRecheck finalizersThread) with
          finalizersLock := some (.mutator tid) }).record (.lock (.mutator tid)))
  | runRecheckEmpty (s : State) (tid : Nat) (finalizersThread : Bool)
      (pc : s.pc (.mutator tid) = .runRecheck finalizersThread)
      (empty : s.toFinalize = []) (owns : s.finalizersLock = some (.mutator tid))
      (returnCallable : ReturnCallable s (.mutator tid)) :
      Step s (.mutator tid)
        (({ s.leave (.mutator tid) with finalizersLock := none }).record
          (.unlock (.mutator tid)))
  | runRecheckWork (s : State) (tid : Nat) (finalizersThread : Bool)
      (pc : s.pc (.mutator tid) = .runRecheck finalizersThread)
      (work : s.toFinalize ≠ []) (owns : s.finalizersLock = some (.mutator tid)) :
      Step s (.mutator tid)
        (s.setPC (.mutator tid) (.runCopy finalizersThread (present s.toFinalize)))
  | runCopy (s : State) (tid : Nat) (finalizersThread : Bool) (queue : List Entry)
      (pc : s.pc (.mutator tid) = .runCopy finalizersThread queue) :
      Step s (.mutator tid) (s.setPC (.mutator tid) (.runClearHint finalizersThread queue))
  | runClearHint (s : State) (tid : Nat) (finalizersThread : Bool) (queue : List Entry)
      (pc : s.pc (.mutator tid) = .runClearHint finalizersThread queue) :
      Step s (.mutator tid)
        (({ s.setPC (.mutator tid) (.runBarrier finalizersThread queue) with
          pendingHint := false }).record (.pendingStore (.mutator tid) false))
  | runBarrier (s : State) (tid : Nat) (finalizersThread : Bool) (queue : List Entry)
      (pc : s.pc (.mutator tid) = .runBarrier finalizersThread queue) :
      Step s (.mutator tid)
        ((s.setPC (.mutator tid) (.runReset finalizersThread queue)).record
          (.queueBarrier (.mutator tid)))
  | runReset (s : State) (tid : Nat) (finalizersThread : Bool) (queue : List Entry)
      (pc : s.pc (.mutator tid) = .runReset finalizersThread queue)
      (pending : ∀ entry ∈ queue, s.lifecycle entry.serial = .pending)
      (tidBound : tid < s.nThreads)
      (queueSource : queue = present s.toFinalize) :
      Step s (.mutator tid)
        ({ (s.setLifecycleEntries queue (.runEscrow tid)).setPC (.mutator tid)
          (.runSave finalizersThread queue) with toFinalize := [] })
  | runSave (s : State) (tid : Nat) (finalizersThread : Bool) (queue : List Entry)
      (pc : s.pc (.mutator tid) = .runSave finalizersThread queue)
      (escrow : ∀ entry ∈ queue, s.lifecycle entry.serial = .runEscrow tid)
      (tidBound : tid < s.nThreads) :
      Step s (.mutator tid)
        ((((s.setLifecycleEntries queue (.frame tid)).pushNewFrame tid queue
          (some (s.inFinalizer tid))).setInFinalizer
          tid (!finalizersThread)).setPC (.mutator tid) .rootFrame)
  | rootFrame (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .rootFrame) (top : topFrame? s tid = some frame)
      (frameWF : frame.WellFormed) :
      Step s actor
        (let header : GCFrameHeader :=
          ⟨frame.cells.length * 2, s.gcStackHead tid⟩
        ((((s.replaceTopFrame tid { frame with header := some header }).setGCStackHead tid
          (some frame.backing.identity)).setPC actor .unlockFrame).record
          (.rootQueue actor frame.backing header frame.cells)))
  | unlockFrame (s : State) (actor : Actor) (tid : Nat)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .unlockFrame) (owns : s.finalizersLock = some actor) :
      Step s actor
        (({ s.setPC actor .callbacks with finalizersLock := none }).record (.unlock actor))
  | callbackStart (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame)
      (front : List Entry) (entry : Entry)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .callbacks) (top : topFrame? s tid = some frame)
      (rooted : frame.header.isSome = true)
      (frameWF : frame.WellFormed)
      (queueCopied : ∀ item ∈ frame.queue, item ∈ frame.copied)
      (stage : s.lifecycle entry.serial = .frame tid)
      (pop : popLast? frame.queue = some (front, entry))
      (idle : frame.running = none) :
      Step s actor
        ({ ((((s.replaceTopFrame tid { frame with queue := front, running := some entry }).setLifecycle
          entry.serial (.running tid)).setPC
          actor .callbackReturn).record (.callbackStart actor entry)) with
          started := s.started ++ [entry] })
  | callbackFinish (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame) (entry : Entry)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .callbackReturn) (top : topFrame? s tid = some frame)
      (running : frame.running = some entry)
      (rooted : frame.header.isSome = true) (frameWF : frame.WellFormed)
      (runningCopied : entry ∈ frame.copied)
      (stage : s.lifecycle entry.serial = .running tid)
      (tidBound : tid < s.nThreads) :
      Step s actor
        ({ (((s.replaceTopFrame tid { frame with running := none }).setLifecycle
          entry.serial .completed).setPC actor .callbacks).record
          (.callbackFinish actor entry) with completed := s.completed ++ [entry] })
  | callbacksDone (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .callbacks) (top : topFrame? s tid = some frame)
      (empty : frame.queue = []) (idle : frame.running = none) :
      Step s actor (s.setPC actor .restoreFrame)
  | restoreFrameSaved (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame) (saved : Bool)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .restoreFrame) (top : topFrame? s tid = some frame)
      (restore : frame.restoreInFinalizer = some saved)
      (empty : frame.queue = []) (idle : frame.running = none)
      (returnCallable : ReturnCallable s actor) :
      Step s actor (((s.popFrame tid).setInFinalizer tid saved).leave actor)
  | restoreFramePlain (s : State) (actor : Actor) (tid : Nat) (frame : RunFrame)
      (actorThread : actor = .mutator tid)
      (pc : s.pc actor = .restoreFrame) (top : topFrame? s tid = some frame)
      (restore : frame.restoreInFinalizer = none)
      (empty : frame.queue = []) (idle : frame.running = none)
      (returnCallable : ReturnCallable s actor) :
      Step s actor ((s.popFrame tid).leave actor)
  | enterCollectWait (s : State) (tid : Nat) (resume : PC)
      (tidBound : tid < s.nThreads)
      (pc : s.pc (.mutator tid) = resume)
      (safe : gcCallable resume = true) (running : s.worldStopped = false) :
      Step s (.mutator tid) (s.setPC (.mutator tid) (.collectWait resume))
  | beginCollection (s : State) (tid : Nat) (resume : PC) (full : Bool)
      (pc : s.pc .collector = .idle) (free : s.finalizersLock = none)
      (caller : s.pc (.mutator tid) = .collectWait resume)
      (tidBound : tid < s.nThreads)
      (quiescent : ∀ other, other < s.nThreads → other ≠ tid →
        s.pc (.mutator other) = .idle) :
      Step s .collector
        (({ s.setPC .collector (.collectBegin full) with
          finalizersLock := some .collector, worldStopped := true,
          collectorCaller := some (tid, resume) }).record
          (.lock .collector))
  | collectBegin (s : State) (full : Bool)
      (pc : s.pc .collector = .collectBegin full) :
      Step s .collector
        (s.setPC .collector
          (.collectNext full (if full then 0 else s.markedLength)
            (sweepTargets s full)))
  | collectNextList (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId)
      (pc : s.pc .collector = .collectNext full origMarked (list :: remaining)) :
      Step s .collector
        (s.setPC .collector
          (.collectScan full origMarked list remaining [] (listLength s list) 0))
  | collectScanObject (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (slot : PairSlot) (object : TaggedObject)
      (pc : s.pc .collector =
        .collectScan full origMarked list remaining kept oldLength index)
      (inside : index < oldLength) (item : (s.list list)[index]? = some slot)
      (loaded : slot.objectCell = some object)
      (listBound : list.InRange s) :
      Step s .collector
        ((s.setPC .collector
          (.collectReadFunction full origMarked list remaining kept oldLength index object)).record
          (.objectLoad .collector (.list list) index (some object)))
  | collectReadFunctionStep (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (object : TaggedObject) (slot : PairSlot)
      (function : TaggedFunction) (entry : Entry)
      (pc : s.pc .collector =
        .collectReadFunction full origMarked list remaining kept oldLength index object)
      (item : (s.list list)[index]? = some slot)
      (loaded : slot.functionCell = some function)
      (serial : object.serial = function.serial)
      (decoded : entry = ⟨object.serial, object.object, function.function, object.tagBits⟩) :
      Step s .collector
        ((s.setPC .collector
          (.collectClassify full origMarked list remaining kept oldLength index entry
            (entry.freed s) (entry.oldForFinalizers s list))).record
          (.functionLoad .collector (.list list) index (some function)))
  | collectClassifyFreed (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry) (old : Bool)
      (pc : s.pc .collector =
        .collectClassify full origMarked list remaining kept oldLength index entry true old) :
      Step s .collector
        (s.setPC .collector
          (.collectScheduleObject full origMarked list remaining kept oldLength index entry))
  | collectClassifyOld (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectClassify full origMarked list remaining kept oldLength index entry false true) :
      Step s .collector
        (s.setPC .collector
          (.collectMarkedObject full origMarked list remaining kept oldLength index entry))
  | collectClassifyKept (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectClassify full origMarked list remaining kept oldLength index entry false false) :
      Step s .collector
        (s.setPC .collector
          (.collectKeepObject full origMarked list remaining kept oldLength index entry))
  | collectKeepObjectMoved (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectKeepObject full origMarked list remaining kept oldLength index entry)
      (moved : kept.length < index)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (destination : GarbageAt (s.list list) kept.length (CollectGarbage s list)) :
      Step s .collector
        (((s.setListContents list (writeObjectCell (s.list list) kept.length entry)).setPC
          .collector (.collectKeepFunction full origMarked list remaining kept oldLength index entry)).record
          (.objectStore .collector (.list list) kept.length
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | collectKeepObjectSame (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectKeepObject full origMarked list remaining kept oldLength index entry)
      (same : kept.length = index) :
      Step s .collector
        (s.setPC .collector
          (.collectKeepFunction full origMarked list remaining kept oldLength index entry))
  | collectKeepFunctionMoved (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectKeepFunction full origMarked list remaining kept oldLength index entry)
      (moved : kept.length < index)
      (owns : s.finalizersLock = some .collector)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (partialDestination : ObjectHalfAt (s.list list) kept.length entry)
      (destinationBound : kept.length < listLength s list)
      (fresh : SerialFresh kept entry.serial) :
      Step s .collector
        ((((s.setListContents list (writeFunctionCell (s.list list) kept.length entry)).setLifecycle
          entry.serial .collectorCompactEscrow).setPC
          .collector (.collectScan full origMarked list remaining (kept ++ [entry])
            oldLength (index + 1))).record
          (.functionStore .collector (.list list) kept.length
            ⟨entry.serial, entry.function⟩))
  | collectKeepFunctionSame (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectKeepFunction full origMarked list remaining kept oldLength index entry)
      (same : kept.length = index)
      (stage : s.lifecycle entry.serial = list.lifecycle) :
      Step s .collector
        (s.setPC .collector
          (.collectScan full origMarked list remaining (kept ++ [entry])
            oldLength (index + 1)))
  | collectScheduleObject (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectScheduleObject full origMarked list remaining kept oldLength index entry)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry) :
      Step s .collector
        (({ s with toFinalize := writeObjectCell s.toFinalize s.toFinalize.length entry }.setPC
          .collector (.collectScheduleFunction full origMarked list remaining kept oldLength index
            s.toFinalize.length entry)).record
          (.objectStore .collector .toFinalize s.toFinalize.length
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | collectScheduleFunction (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index position : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectScheduleFunction full origMarked list remaining kept oldLength index position entry)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (partialDestination : ObjectHalfAt s.toFinalize position entry) :
      Step s .collector
        ((({ s with toFinalize := writeFunctionCell s.toFinalize position entry }.setLifecycle
          entry.serial .pending).setPC
          .collector (.collectPending full origMarked list remaining kept oldLength index)).record
          (.functionStore .collector .toFinalize position
            ⟨entry.serial, entry.function⟩))
  | collectPending (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat)
      (pc : s.pc .collector =
        .collectPending full origMarked list remaining kept oldLength index) :
      Step s .collector
        (({ s.setPC .collector
          (.collectScan full origMarked list remaining kept oldLength (index + 1)) with
          pendingHint := true }).record (.pendingStore .collector true))
  | collectMarkedObject (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectMarkedObject full origMarked list remaining kept oldLength index entry)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (destination : GarbageAt s.markedFinalizers s.markedLength
        (fun serial => s.lifecycle serial ≠ .markedEscrow)) :
      Step s .collector
        (({ s with markedFinalizers :=
          writeObjectCell s.markedFinalizers s.markedLength entry }.setPC
          .collector (.collectMarkedFunction full origMarked list remaining kept oldLength index
            s.markedLength entry)).record
          (.objectStore .collector (.list .marked) s.markedLength
            ⟨entry.serial, entry.object, entry.tagBits⟩))
  | collectMarkedFunction (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index position : Nat) (entry : Entry)
      (pc : s.pc .collector =
        .collectMarkedFunction full origMarked list remaining kept oldLength index position entry)
      (stage : s.lifecycle entry.serial = list.lifecycle)
      (source : SlotHolds (s.list list) index entry)
      (partialDestination : ObjectHalfAt s.markedFinalizers position entry)
      (atEnd : position = s.markedLength)
      (unique : NoCompleteCopy (s.markedFinalizers.take s.markedLength) entry.serial) :
      Step s .collector
        ((((({ s with markedFinalizers :=
          writeFunctionCell s.markedFinalizers position entry }.setListLength .marked
          (position + 1)).setLifecycle entry.serial .marked).setPC .collector
          (.collectScan full origMarked list remaining kept oldLength (index + 1))).record
          (.functionStore .collector (.list .marked) position
            ⟨entry.serial, entry.function⟩)).record
          (.lengthStore .collector .marked .relaxed (rawPairLength (position + 1))))
  | collectScanEmpty (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry)
      (oldLength index : Nat) (slot : PairSlot)
      (pc : s.pc .collector =
        .collectScan full origMarked list remaining kept oldLength index)
      (inside : index < oldLength) (item : (s.list list)[index]? = some slot)
      (empty : slot.objectCell = none) :
      Step s .collector
        ((s.setPC .collector
          (.collectScan full origMarked list remaining kept oldLength (index + 1))).record
          (.objectLoad .collector (.list list) index none))
  | collectScanDone (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry) (oldLength : Nat)
      (pc : s.pc .collector =
        .collectScan full origMarked list remaining kept oldLength oldLength) :
      Step s .collector
        (s.setPC .collector
          (.collectPublish full origMarked list remaining kept oldLength))
  | collectPublish (s : State) (full : Bool) (origMarked : Nat)
      (list : ListId) (remaining : List ListId) (kept : List Entry) (oldLength : Nat)
      (pc : s.pc .collector =
        .collectPublish full origMarked list remaining kept oldLength)
      (keptStage : ∀ entry ∈ kept, s.lifecycle entry.serial = list.lifecycle ∨
        s.lifecycle entry.serial = .collectorCompactEscrow)
      (owns : s.finalizersLock = some .collector)
      (observed : listLength s list = oldLength)
      (keptBound : kept.length ≤ oldLength)
      (compacted : CompactedPrefix (s.list list) kept)
      (tail : GarbageBetween (s.list list) kept.length oldLength (CollectGarbage s list)) :
      Step s .collector
        ((((s.setLifecycleEntries kept list.lifecycle).setListLength list kept.length).setPC .collector
          (.collectNext full origMarked remaining)).record
          (.lengthStore .collector list .relaxed (rawPairLength kept.length)))
  | collectNextDone (s : State) (full : Bool) (origMarked : Nat)
      (pc : s.pc .collector = .collectNext full origMarked []) :
      Step s .collector (s.setPC .collector (.collectMark origMarked))
  | collectMark (s : State) (origMarked tid : Nat) (resume : PC)
      (pc : s.pc .collector = .collectMark origMarked)
      (caller : s.collectorCaller = some (tid, resume))
      (waiting : s.pc (.mutator tid) = .collectWait resume)
      (owns : s.finalizersLock = some .collector) :
      Step s .collector
        (({ ((markCollectorFinalizers s origMarked).setPC (.mutator tid)
          (.collectResume resume)).setPC .collector (.collectPostRun tid resume) with
          finalizersLock := none, worldStopped := false }).record (.unlock .collector))
  | collectPostRunRun (s : State) (tid : Nat) (resume : PC)
      (pc : s.pc .collector = .collectPostRun tid resume)
      (caller : s.collectorCaller = some (tid, resume))
      (resuming : s.pc (.mutator tid) = .collectResume resume)
      (tidBound : tid < s.nThreads)
      (enabled : s.finalizersInhibited tid = 0)
      (unlocked : s.heldLocks tid = 0) (queueEmpty : s.engineQueued tid = 0) :
      Step s .collector
        (let restored :=
          { (s.setPC (.mutator tid) resume).setPC .collector .idle with
            collectorCaller := none }
        restored.enter (.mutator tid) (.runFast false))
  | collectPostRunSkip (s : State) (tid : Nat) (resume : PC)
      (pc : s.pc .collector = .collectPostRun tid resume)
      (caller : s.collectorCaller = some (tid, resume))
      (resuming : s.pc (.mutator tid) = .collectResume resume)
      (blocked : s.nThreads ≤ tid ∨ s.finalizersInhibited tid ≠ 0 ∨
        s.heldLocks tid ≠ 0 ∨ s.engineQueued tid ≠ 0)
      (resumeCallable : gcCallable resume = true) :
      Step s .collector
        { (s.setPC (.mutator tid) resume).setPC .collector .idle with
          collectorCaller := none }

inductive Steps : State → List Actor → State → Prop where
  | nil (s : State) : Steps s [] s
  | cons {s middle out : State} {actor : Actor} {actors : List Actor} :
      Step s actor middle → Steps middle actors out → Steps s (actor :: actors) out

end JuliaLean.CRuntime.Finalizers
