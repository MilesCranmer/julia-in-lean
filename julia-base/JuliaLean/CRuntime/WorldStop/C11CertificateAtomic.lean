import JuliaLean.CRuntime.WorldStop.C11CertificateBase
import JuliaLean.CRuntime.WorldStop.C11CertificateData

namespace JuliaLean.CRuntime.WorldStop

open Memory

set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 65536
set_option linter.constructorNameAsVariable false

namespace D
abbrev initializerIds := C11CertificateData.initializerIds
abbrev allEventIds := C11CertificateData.allEventIds
abbrev atomicReadIds := C11CertificateData.atomicReadIds
abbrev atomicWriteIds := C11CertificateData.atomicWriteIds
abbrev plainReadIds := C11CertificateData.plainReadIds
abbrev plainWriteIds := C11CertificateData.plainWriteIds
abbrev readIds := C11CertificateData.readIds
abbrev plainAccessIds := C11CertificateData.plainAccessIds
abbrev writeIds := C11CertificateData.writeIds
abbrev accessIds := C11CertificateData.accessIds
abbrev nonInitAtomicWriteIds := C11CertificateData.nonInitAtomicWriteIds
abbrev readFromPairs := C11CertificateData.readFromPairs
abbrev atomicInitializerPairs := C11CertificateData.atomicInitializerPairs
abbrev scIds := C11CertificateData.scIds
abbrev scFenceIds := C11CertificateData.scFenceIds
abbrev successfulRMWIds := C11CertificateData.successfulRMWIds
abbrev lockIds := C11CertificateData.lockIds
abbrev unlockIds := C11CertificateData.unlockIds
abbrev scRank := C11CertificateData.scRank
abbrev gcRunningAccessIds := C11CertificateData.gcRunningAccessIds
abbrev eventLocation := C11CertificateData.eventLocation
abbrev eventMO := C11CertificateData.eventMO
abbrev eventThread := C11CertificateData.eventThread
abbrev lockMutex := C11CertificateData.lockMutex
abbrev unlockMutex := C11CertificateData.unlockMutex
theorem canonicalCandidate_eventCount : canonicalCandidate.events.size = 88 :=
  C11CertificateData.canonicalCandidate_eventCount
theorem initializerIds_exact (id : Nat) : id ∈ initializerIds ↔ id < 20 :=
  C11CertificateData.initializerIds_exact id
end D

def certificateId (n : Nat) (h : n < 88) : canonicalCandidate.Id :=
  ⟨n, Nat.lt_of_lt_of_le h (Nat.le_of_eq D.canonicalCandidate_eventCount.symm)⟩

theorem certificateId_bound (i : canonicalCandidate.Id) : i.val < 88 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq D.canonicalCandidate_eventCount)

def pairProduct (first second : List Nat) : List (Nat × Nat) :=
  first.flatMap fun left => second.map fun right => (left, right)

def listedEventCheck (ids : List Nat)
    (predicate : canonicalCandidate.Id → Bool) : Bool :=
  ids.all fun n =>
    if h : n < 88 then predicate (certificateId n h) else false

theorem listedEvent_of_check (ids : List Nat)
    (predicate : canonicalCandidate.Id → Bool)
    (check : listedEventCheck ids predicate = true) {n : Nat}
    (member : n ∈ ids) (bound : n < 88) :
    predicate (certificateId n bound) = true := by
  unfold listedEventCheck at check
  have row := (List.all_eq_true.mp check) n member
  simpa [bound] using row

def idRange (start count : Nat) : List Nat :=
  (List.range count).map fun offset => start + offset

theorem mem_idRange (start count id : Nat) (lower : start ≤ id)
    (upper : id < start + count) : id ∈ idRange start count := by
  apply List.mem_map.mpr
  refine ⟨id - start, List.mem_range.mpr ?_, ?_⟩
  · omega
  · omega

def eventChunkStarts : List Nat :=
  (List.range 22).map fun chunk => chunk * 4

theorem allEvent_of_chunks (predicate : canonicalCandidate.Id → Bool)
    (checks : ∀ start, start ∈ eventChunkStarts →
      listedEventCheck (idRange start 4) predicate = true)
    (i : canonicalCandidate.Id) : predicate i = true := by
  let start := (i.val / 4) * 4
  have lower : start ≤ i.val := Nat.div_mul_le_self i.val 4
  have quotientBound : i.val / 4 < 22 := by
    have bound := certificateId_bound i
    omega
  have startMember : start ∈ eventChunkStarts := by
    apply List.mem_map.mpr
    exact ⟨i.val / 4, List.mem_range.mpr quotientBound, rfl⟩
  have remainder := Nat.mod_lt i.val (by decide : 0 < 4)
  have decomposition := Nat.div_add_mod i.val 4
  have upper : i.val < start + 4 := by omega
  exact listedEvent_of_check _ _ (checks start startMember)
    (mem_idRange start 4 i.val lower upper) (certificateId_bound i)

theorem listedEventProp_of_check (ids : List Nat)
    (property : canonicalCandidate.Id → Prop) [DecidablePred property]
    (check : listedEventCheck ids (fun i => decide (property i)) = true)
    (i : canonicalCandidate.Id) (member : i.val ∈ ids) : property i := by
  have bound : i.val < 88 := certificateId_bound i
  have row := listedEvent_of_check ids (fun i => decide (property i))
    check member bound
  have same : certificateId i.val bound = i := by apply Fin.ext; rfl
  exact of_decide_eq_true (by simpa [same] using row)

def listedPairCheck (pairs : List (Nat × Nat))
    (predicate : canonicalCandidate.Id → canonicalCandidate.Id → Bool) : Bool :=
  pairs.all fun pair =>
    if hread : pair.1 < 88 then
      if hsource : pair.2 < 88 then
        predicate (certificateId pair.1 hread) (certificateId pair.2 hsource)
      else false
    else false

def pairBoundsCheck (pairs : List (Nat × Nat)) : Bool :=
  pairs.all fun pair => decide (pair.1 < 88 ∧ pair.2 < 88)

theorem pairBounds_of_check (pairs : List (Nat × Nat))
    (check : pairBoundsCheck pairs = true) {pair : Nat × Nat}
    (member : pair ∈ pairs) : pair.1 < 88 ∧ pair.2 < 88 := by
  unfold pairBoundsCheck at check
  exact of_decide_eq_true ((List.all_eq_true.mp check) pair member)

theorem listedPair_of_check (pairs : List (Nat × Nat))
    (predicate : canonicalCandidate.Id → canonicalCandidate.Id → Bool)
    (check : listedPairCheck pairs predicate = true) {pair : Nat × Nat}
    (member : pair ∈ pairs) (bounds : pair.1 < 88 ∧ pair.2 < 88) :
    predicate (certificateId pair.1 bounds.1) (certificateId pair.2 bounds.2) = true := by
  unfold listedPairCheck at check
  have row := (List.all_eq_true.mp check) pair member
  simpa [bounds.1, bounds.2] using row

def CanonicalEventCore (i : canonicalCandidate.Id) : Prop :=
  (canonicalCandidate.isAtomicRead i = true ↔ i.val ∈ D.atomicReadIds) ∧
  (canonicalCandidate.isAtomicWrite i = true ↔ i.val ∈ D.atomicWriteIds) ∧
  (canonicalCandidate.isRead i = true ∧
    (canonicalCandidate.event i).action.isPlain = true ↔ i.val ∈ D.plainReadIds) ∧
  (canonicalCandidate.isWrite i = true ∧
    (canonicalCandidate.event i).action.isPlain = true ↔ i.val ∈ D.plainWriteIds) ∧
  (canonicalCandidate.isRead i = true ↔ i.val ∈ D.readIds) ∧
  ((canonicalCandidate.event i).action.isInit = true ↔ i.val ∈ D.initializerIds) ∧
  ((canonicalCandidate.event i).action.isSC = true ↔ i.val ∈ D.scIds) ∧
  ((canonicalCandidate.event i).action.isFence = true ↔ i.val ∈ D.scFenceIds) ∧
  ((canonicalCandidate.event i).action.isRMW = true ↔ i.val ∈ D.successfulRMWIds) ∧
  ((match (canonicalCandidate.event i).action with | .lock _ => true | _ => false) = true ↔
    i.val ∈ D.lockIds) ∧
  ((match (canonicalCandidate.event i).action with | .unlock _ => true | _ => false) = true ↔
    i.val ∈ D.unlockIds) ∧
  (i.val ∈ D.scIds → (canonicalCandidate.event i).sc = D.scRank i.val) ∧
  ((canonicalCandidate.event i).action.location = some .gcRunning ↔
    i.val ∈ D.gcRunningAccessIds) ∧
  (canonicalCandidate.event i).action.location = D.eventLocation i.val ∧
  (canonicalCandidate.event i).mo = D.eventMO i.val ∧
  (canonicalCandidate.event i).thread = D.eventThread i.val ∧
  (i.val ∈ D.lockIds →
    (canonicalCandidate.event i).action = .lock (D.lockMutex i.val)) ∧
  (i.val ∈ D.unlockIds →
    (canonicalCandidate.event i).action = .unlock (D.unlockMutex i.val)) ∧
  (canonicalCandidate.event i).action.validOrders = true ∧
  (match (canonicalCandidate.event i).readFrom with
    | none => true
    | some source => decide ((i.val, source) ∈ D.readFromPairs)) = true ∧
  (canonicalCandidate.isRead i = true →
    (canonicalCandidate.event i).readFrom.isSome = true) ∧
  ((canonicalCandidate.event i).dependsOn.all fun dependency =>
    decide (dependency < canonicalCandidate.events.size)) = true ∧
  ((canonicalCandidate.event i).dependsOn.all fun dependency =>
    decide (dependency < i.val)) = true ∧
  (match (canonicalCandidate.event i).action.location with
    | none => true
    | some location => (canonicalCandidate.event i).action.isInit ||
      decide ((canonicalCandidate.event i).action.accessClass =
        some (declaredAccessClass location))) = true ∧
  ((canonicalCandidate.event i).action.isPlain = true ↔
    i.val ∈ D.plainAccessIds) ∧
  (canonicalCandidate.isWrite i = true ↔ i.val ∈ D.writeIds) ∧
  ((canonicalCandidate.event i).action.location.isSome = true ↔
    i.val ∈ D.accessIds)

def canonicalEventCoreCheck (i : canonicalCandidate.Id) : Bool :=
  decide (canonicalCandidate.isAtomicRead i = true ↔ i.val ∈ D.atomicReadIds) &&
  decide (canonicalCandidate.isAtomicWrite i = true ↔ i.val ∈ D.atomicWriteIds) &&
  decide (canonicalCandidate.isRead i = true ∧
    (canonicalCandidate.event i).action.isPlain = true ↔ i.val ∈ D.plainReadIds) &&
  decide (canonicalCandidate.isWrite i = true ∧
    (canonicalCandidate.event i).action.isPlain = true ↔ i.val ∈ D.plainWriteIds) &&
  decide (canonicalCandidate.isRead i = true ↔ i.val ∈ D.readIds) &&
  decide ((canonicalCandidate.event i).action.isInit = true ↔ i.val ∈ D.initializerIds) &&
  decide ((canonicalCandidate.event i).action.isSC = true ↔ i.val ∈ D.scIds) &&
  decide ((canonicalCandidate.event i).action.isFence = true ↔ i.val ∈ D.scFenceIds) &&
  decide ((canonicalCandidate.event i).action.isRMW = true ↔ i.val ∈ D.successfulRMWIds) &&
  decide ((match (canonicalCandidate.event i).action with | .lock _ => true | _ => false) = true ↔
    i.val ∈ D.lockIds) &&
  decide ((match (canonicalCandidate.event i).action with | .unlock _ => true | _ => false) = true ↔
    i.val ∈ D.unlockIds) &&
  decide (i.val ∈ D.scIds → (canonicalCandidate.event i).sc = D.scRank i.val) &&
  decide ((canonicalCandidate.event i).action.location = some .gcRunning ↔
    i.val ∈ D.gcRunningAccessIds) &&
  decide ((canonicalCandidate.event i).action.location = D.eventLocation i.val) &&
  decide ((canonicalCandidate.event i).mo = D.eventMO i.val) &&
  decide ((canonicalCandidate.event i).thread = D.eventThread i.val) &&
  decide (i.val ∈ D.lockIds →
    (canonicalCandidate.event i).action = .lock (D.lockMutex i.val)) &&
  decide (i.val ∈ D.unlockIds →
    (canonicalCandidate.event i).action = .unlock (D.unlockMutex i.val)) &&
  (canonicalCandidate.event i).action.validOrders &&
  (match (canonicalCandidate.event i).readFrom with
    | none => true
    | some source => decide ((i.val, source) ∈ D.readFromPairs)) &&
  decide (canonicalCandidate.isRead i = true →
    (canonicalCandidate.event i).readFrom.isSome = true) &&
  ((canonicalCandidate.event i).dependsOn.all fun dependency =>
    decide (dependency < canonicalCandidate.events.size)) &&
  ((canonicalCandidate.event i).dependsOn.all fun dependency =>
    decide (dependency < i.val)) &&
  (match (canonicalCandidate.event i).action.location with
    | none => true
    | some location => (canonicalCandidate.event i).action.isInit ||
      decide ((canonicalCandidate.event i).action.accessClass =
        some (declaredAccessClass location))) &&
  decide ((canonicalCandidate.event i).action.isPlain = true ↔
    i.val ∈ D.plainAccessIds) &&
  decide (canonicalCandidate.isWrite i = true ↔ i.val ∈ D.writeIds) &&
  decide ((canonicalCandidate.event i).action.location.isSome = true ↔
    i.val ∈ D.accessIds)

theorem canonicalEventCoreChunk (start : Nat) (member : start ∈ eventChunkStarts) :
    listedEventCheck (idRange start 4) canonicalEventCoreCheck = true := by
  rcases List.mem_map.mp member with ⟨chunk, chunkMember, rfl⟩
  have chunkBound := List.mem_range.mp chunkMember
  have possibilities :
      chunk = 0 ∨ chunk = 1 ∨ chunk = 2 ∨ chunk = 3 ∨ chunk = 4 ∨
      chunk = 5 ∨ chunk = 6 ∨ chunk = 7 ∨ chunk = 8 ∨ chunk = 9 ∨
      chunk = 10 ∨ chunk = 11 ∨ chunk = 12 ∨ chunk = 13 ∨
      chunk = 14 ∨ chunk = 15 ∨ chunk = 16 ∨ chunk = 17 ∨
      chunk = 18 ∨ chunk = 19 ∨ chunk = 20 ∨ chunk = 21 := by omega
  rcases possibilities with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem canonicalEventCore (i : canonicalCandidate.Id) : CanonicalEventCore i := by
  have row := allEvent_of_chunks canonicalEventCoreCheck canonicalEventCoreChunk i
  unfold canonicalEventCoreCheck at row
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  simpa [CanonicalEventCore, and_assoc] using row

theorem isAtomicRead_iff_mem (i : canonicalCandidate.Id) :
    canonicalCandidate.isAtomicRead i = true ↔ i.val ∈ D.atomicReadIds :=
  (canonicalEventCore i).1

theorem isAtomicWrite_iff_mem (i : canonicalCandidate.Id) :
    canonicalCandidate.isAtomicWrite i = true ↔ i.val ∈ D.atomicWriteIds :=
  (canonicalEventCore i).2.1

theorem isPlainRead_iff_mem (i : canonicalCandidate.Id) :
    canonicalCandidate.isRead i = true ∧
      (canonicalCandidate.event i).action.isPlain = true ↔
      i.val ∈ D.plainReadIds := by
  exact (canonicalEventCore i).2.2.1

theorem isPlainWrite_iff_mem (i : canonicalCandidate.Id) :
    canonicalCandidate.isWrite i = true ∧
      (canonicalCandidate.event i).action.isPlain = true ↔
      i.val ∈ D.plainWriteIds := by
  exact (canonicalEventCore i).2.2.2.1

theorem isRead_iff_mem (i : canonicalCandidate.Id) :
    canonicalCandidate.isRead i = true ↔ i.val ∈ D.readIds :=
  (canonicalEventCore i).2.2.2.2.1

theorem isInit_iff_mem (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.isInit = true ↔
      i.val ∈ D.initializerIds :=
  (canonicalEventCore i).2.2.2.2.2.1

theorem isSC_iff_mem (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.isSC = true ↔ i.val ∈ D.scIds :=
  (canonicalEventCore i).2.2.2.2.2.2.1

theorem isFence_iff_mem (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.isFence = true ↔
      i.val ∈ D.scFenceIds := by
  rcases canonicalEventCore i with ⟨_, _, _, _, _, _, _, fence, _⟩
  exact fence

theorem isRMW_iff_mem (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.isRMW = true ↔
      i.val ∈ D.successfulRMWIds := by
  rcases canonicalEventCore i with ⟨_, _, _, _, _, _, _, _, rmw, _⟩
  exact rmw

theorem isLock_iff_mem (i : canonicalCandidate.Id) :
    (match (canonicalCandidate.event i).action with | .lock _ => true | _ => false) = true ↔
      i.val ∈ D.lockIds := by
  rcases canonicalEventCore i with ⟨_, _, _, _, _, _, _, _, _, lock, _⟩
  exact lock

theorem isUnlock_iff_mem (i : canonicalCandidate.Id) :
    (match (canonicalCandidate.event i).action with | .unlock _ => true | _ => false) = true ↔
      i.val ∈ D.unlockIds := by
  rcases canonicalEventCore i with ⟨_, _, _, _, _, _, _, _, _, _, unlock, _⟩
  exact unlock

theorem scRank_of_sc (i : canonicalCandidate.Id)
    (sc : (canonicalCandidate.event i).action.isSC = true) :
    (canonicalCandidate.event i).sc = D.scRank i.val := by
  have member := (isSC_iff_mem i).mp sc
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, rank, _⟩
  exact rank member

theorem gcRunningLocation_iff (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.location = some .gcRunning ↔
      i.val ∈ D.gcRunningAccessIds := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, location, _⟩
  exact location

theorem eventLocation_eq (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).action.location = D.eventLocation i.val := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, location, _⟩
  exact location

theorem eventMO_eq (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).mo = D.eventMO i.val := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, modificationOrder, _⟩
  exact modificationOrder

theorem eventThread_eq (i : canonicalCandidate.Id) :
    (canonicalCandidate.event i).thread = D.eventThread i.val := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, thread, _⟩
  exact thread

theorem lockAction_eq (i : canonicalCandidate.Id) (member : i.val ∈ D.lockIds) :
    (canonicalCandidate.event i).action = .lock (D.lockMutex i.val) := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, action, _⟩
  exact action member

theorem unlockAction_eq (i : canonicalCandidate.Id) (member : i.val ∈ D.unlockIds) :
    (canonicalCandidate.event i).action = .unlock (D.unlockMutex i.val) := by
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, action, _⟩
  exact action member

def readFromPairBoundsCheck : Bool := pairBoundsCheck D.readFromPairs

def ReadFromPairCore (read source : canonicalCandidate.Id) : Prop :=
  canonicalCandidate.readSource read source = true ∧
  canonicalCandidate.isRead read = true ∧
  canonicalCandidate.isWrite source = true ∧
  canonicalCandidate.sameLocation read source = true ∧
  (canonicalCandidate.event read).action.readValue =
    (canonicalCandidate.event source).action.writeValue ∧
  ((canonicalCandidate.event source).action.isInit = true ∨
    (canonicalCandidate.event source).action.accessClass =
      (canonicalCandidate.event read).action.accessClass)

def readFromPairCorePredicate (read source : canonicalCandidate.Id) : Bool :=
  canonicalCandidate.readSource read source &&
  canonicalCandidate.isRead read &&
  canonicalCandidate.isWrite source &&
  canonicalCandidate.sameLocation read source &&
  decide ((canonicalCandidate.event read).action.readValue =
    (canonicalCandidate.event source).action.writeValue) &&
  ((canonicalCandidate.event source).action.isInit ||
    decide ((canonicalCandidate.event source).action.accessClass =
      (canonicalCandidate.event read).action.accessClass))

def readFromPairCoreCheck : Bool :=
  listedPairCheck D.readFromPairs readFromPairCorePredicate

theorem readFromPairBoundsCheck_true : readFromPairBoundsCheck = true := by decide
theorem readFromPairCoreCheck_true : readFromPairCoreCheck = true := by decide

theorem readFromPairCore_of_mem {pair : Nat × Nat}
    (member : pair ∈ D.readFromPairs) (bounds : pair.1 < 88 ∧ pair.2 < 88) :
    ReadFromPairCore (certificateId pair.1 bounds.1)
      (certificateId pair.2 bounds.2) := by
  have row := listedPair_of_check D.readFromPairs
    readFromPairCorePredicate
    readFromPairCoreCheck_true member bounds
  unfold readFromPairCorePredicate at row
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at row
  simpa [ReadFromPairCore, and_assoc] using row

theorem readFromCovered (read : canonicalCandidate.Id) :
    match (canonicalCandidate.event read).readFrom with
    | none => True
    | some source => (read.val, source) ∈ D.readFromPairs := by
  rcases canonicalEventCore read with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, covered, _, _, _⟩
  cases sourceEq : (canonicalCandidate.event read).readFrom with
  | none => trivial
  | some source =>
    rw [sourceEq] at covered
    exact of_decide_eq_true covered

theorem readSource_iff_mem (read source : canonicalCandidate.Id) :
    canonicalCandidate.readSource read source = true ↔
      (read.val, source.val) ∈ D.readFromPairs := by
  constructor
  · intro hsource
    have sourceEq : (canonicalCandidate.event read).readFrom = some source.val := by
      simpa only [Memory.Candidate.readSource, beq_iff_eq] using hsource
    have row := readFromCovered read
    rw [sourceEq] at row
    exact row
  · intro member
    have readBound : read.val < 88 := certificateId_bound read
    have sourceBound : source.val < 88 := certificateId_bound source
    have row := readFromPairCore_of_mem member ⟨readBound, sourceBound⟩
    have readId : certificateId read.val readBound = read := by apply Fin.ext; rfl
    have sourceId : certificateId source.val sourceBound = source := by apply Fin.ext; rfl
    simpa [readId, sourceId] using row.1

theorem canonicalCandidate_validOrders :
    ∀ i : canonicalCandidate.Id,
      (canonicalCandidate.event i).action.validOrders = true := by
  intro i
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, valid, _, _, _, _⟩
  exact valid

def readFromPairFirstCheck : Bool :=
  D.readFromPairs.all fun pair => decide (pair.1 ∈ D.readIds)

theorem readFromPairFirstCheck_true : readFromPairFirstCheck = true := by decide

theorem canonicalCandidate_readsWitnessed :
    ∀ i : canonicalCandidate.Id, canonicalCandidate.isRead i = true →
      ∃ source : canonicalCandidate.Id,
        canonicalCandidate.readSource i source = true ∧
        canonicalCandidate.isWrite source = true ∧
        canonicalCandidate.sameLocation i source = true ∧
        (canonicalCandidate.event i).action.readValue =
          (canonicalCandidate.event source).action.writeValue := by
  intro i reading
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hasSource, _, _⟩
  have hasSource := hasSource reading
  cases sourceEq : (canonicalCandidate.event i).readFrom with
  | none => simp [sourceEq] at hasSource
  | some sourceNat =>
    have pairRow := readFromCovered i
    rw [sourceEq] at pairRow
    have pairMember : (i.val, sourceNat) ∈ D.readFromPairs := pairRow
    have pairBounds := pairBounds_of_check D.readFromPairs
      readFromPairBoundsCheck_true pairMember
    let source := certificateId sourceNat pairBounds.2
    refine ⟨source, ?_⟩
    have witness := readFromPairCore_of_mem pairMember pairBounds
    have same : certificateId i.val pairBounds.1 = i := by apply Fin.ext; rfl
    have converted : ReadFromPairCore i source := by
      simpa [source, same] using witness
    exact ⟨converted.1, converted.2.2.1, converted.2.2.2.1,
      converted.2.2.2.2.1⟩

theorem canonicalCandidate_nonReadsHaveNoSource :
    ∀ i : canonicalCandidate.Id, canonicalCandidate.isRead i = false →
      (canonicalCandidate.event i).readFrom = none := by
  intro i notReading
  have notMember : i.val ∉ D.readIds := by
    intro member
    have reading := (isRead_iff_mem i).mpr member
    rw [notReading] at reading
    contradiction
  cases sourceEq : (canonicalCandidate.event i).readFrom with
  | none => rfl
  | some sourceNat =>
    have pairRow := readFromCovered i
    rw [sourceEq] at pairRow
    have pairMember : (i.val, sourceNat) ∈ D.readFromPairs := pairRow
    have firstCheck := readFromPairFirstCheck_true
    unfold readFromPairFirstCheck at firstCheck
    have firstRow := (List.all_eq_true.mp firstCheck) (i.val, sourceNat) pairMember
    exact (notMember (of_decide_eq_true firstRow)).elim

def initializerMOCheck : Bool :=
  listedEventCheck D.initializerIds fun i =>
    decide ((canonicalCandidate.event i).mo = 0)

def nonInitAtomicWriteMOCheck : Bool :=
  listedEventCheck D.nonInitAtomicWriteIds fun i =>
    decide (0 < (canonicalCandidate.event i).mo)

def atomicWriteSplitCheck : Bool :=
  D.atomicWriteIds.all fun id =>
    decide (id ∈ D.initializerIds ∨ id ∈ D.nonInitAtomicWriteIds)

theorem initializerMOCheck_true : initializerMOCheck = true := by decide
theorem nonInitAtomicWriteMOCheck_true : nonInitAtomicWriteMOCheck = true := by decide
theorem atomicWriteSplitCheck_true : atomicWriteSplitCheck = true := by decide

theorem atomicWrite_mem_split {id : Nat} (member : id ∈ D.atomicWriteIds) :
    id ∈ D.initializerIds ∨ id ∈ D.nonInitAtomicWriteIds := by
  have check := atomicWriteSplitCheck_true
  unfold atomicWriteSplitCheck at check
  exact of_decide_eq_true
    ((List.all_eq_true.mp check) id member)

theorem initializer_mo_zero (i : canonicalCandidate.Id)
    (member : i.val ∈ D.initializerIds) : (canonicalCandidate.event i).mo = 0 :=
  listedEventProp_of_check D.initializerIds _ initializerMOCheck_true i member

theorem nonInitAtomicWrite_mo_positive (i : canonicalCandidate.Id)
    (member : i.val ∈ D.nonInitAtomicWriteIds) :
    0 < (canonicalCandidate.event i).mo :=
  listedEventProp_of_check D.nonInitAtomicWriteIds _
    nonInitAtomicWriteMOCheck_true i member

theorem canonicalCandidate_initialMO :
    ∀ i : canonicalCandidate.Id, canonicalCandidate.isAtomicWrite i = true →
      ((canonicalCandidate.event i).action.isInit = true ↔
        (canonicalCandidate.event i).mo = 0) := by
  intro i writing
  have writeMember := (isAtomicWrite_iff_mem i).mp writing
  constructor
  · intro initializing
    exact initializer_mo_zero i ((isInit_iff_mem i).mp initializing)
  · intro zero
    rcases atomicWrite_mem_split writeMember with initializing | nonInit
    · exact (isInit_iff_mem i).mpr initializing
    · have positive := nonInitAtomicWrite_mo_positive i nonInit
      omega

def uniqueMOPredicate (first second : canonicalCandidate.Id) : Bool :=
  decide (canonicalCandidate.sameLocation first second = true →
    (canonicalCandidate.event first).mo = (canonicalCandidate.event second).mo →
    first.val = second.val)

def initializerUniqueBlockCheck (start : Nat) : Bool :=
  listedPairCheck (pairProduct (idRange start 4) D.initializerIds)
    uniqueMOPredicate

def nonInitUniqueMOCheck : Bool :=
  listedPairCheck
    (pairProduct D.nonInitAtomicWriteIds D.nonInitAtomicWriteIds)
    uniqueMOPredicate

theorem ium0 : initializerUniqueBlockCheck 0 = true := by decide
theorem ium1 : initializerUniqueBlockCheck 4 = true := by decide
theorem ium2 : initializerUniqueBlockCheck 8 = true := by decide
theorem ium3 : initializerUniqueBlockCheck 12 = true := by decide
theorem ium4 : initializerUniqueBlockCheck 16 = true := by decide
theorem nonInitUniqueMOCheck_true : nonInitUniqueMOCheck = true := by decide

theorem initializerUniqueMO (i j : canonicalCandidate.Id)
    (initI : i.val ∈ D.initializerIds) (initJ : j.val ∈ D.initializerIds)
    (same : canonicalCandidate.sameLocation i j = true)
    (rank : (canonicalCandidate.event i).mo = (canonicalCandidate.event j).mo) :
    i = j := by
  have bounds : (i.val, j.val).1 < 88 ∧ (i.val, j.val).2 < 88 :=
    ⟨certificateId_bound i, certificateId_bound j⟩
  have secondMember : j.val ∈ D.initializerIds := initJ
  have finish (start : Nat) (check : initializerUniqueBlockCheck start = true)
      (firstMember : i.val ∈ idRange start 4) : i = j := by
    have pairMember : (i.val, j.val) ∈
        pairProduct (idRange start 4) D.initializerIds := by
      simp [pairProduct, firstMember, secondMember]
    have row := listedPair_of_check
      (pairProduct (idRange start 4) D.initializerIds) uniqueMOPredicate
      check pairMember bounds
    have equality := of_decide_eq_true row same rank
    exact Fin.ext equality
  by_cases first : i.val < 4
  · exact finish 0 ium0 (mem_idRange 0 4 i.val (by omega) first)
  by_cases second : i.val < 8
  · exact finish 4 ium1 (mem_idRange 4 4 i.val (by omega) (by omega))
  by_cases third : i.val < 12
  · exact finish 8 ium2 (mem_idRange 8 4 i.val (by omega) (by omega))
  by_cases fourth : i.val < 16
  · exact finish 12 ium3 (mem_idRange 12 4 i.val (by omega) (by omega))
  · have underTwenty : i.val < 20 := (D.initializerIds_exact i.val).mp initI
    exact finish 16 ium4 (mem_idRange 16 4 i.val (by omega) (by omega))

theorem canonicalCandidate_uniqueMO :
    ∀ i j : canonicalCandidate.Id,
      canonicalCandidate.isAtomicWrite i = true →
      canonicalCandidate.isAtomicWrite j = true →
      canonicalCandidate.sameLocation i j = true →
      (canonicalCandidate.event i).mo = (canonicalCandidate.event j).mo → i = j := by
  intro i j writeI writeJ same rank
  have memberI := (isAtomicWrite_iff_mem i).mp writeI
  have memberJ := (isAtomicWrite_iff_mem j).mp writeJ
  rcases atomicWrite_mem_split memberI with initI | nonInitI <;>
    rcases atomicWrite_mem_split memberJ with initJ | nonInitJ
  · exact initializerUniqueMO i j initI initJ same rank
  · have zero := initializer_mo_zero i initI
    have positive := nonInitAtomicWrite_mo_positive j nonInitJ
    omega
  · have positive := nonInitAtomicWrite_mo_positive i nonInitI
    have zero := initializer_mo_zero j initJ
    omega
  · have bounds : (i.val, j.val).1 < 88 ∧ (i.val, j.val).2 < 88 := by
      constructor
      · exact certificateId_bound i
      · exact certificateId_bound j
    have row := listedPair_of_check
      (pairProduct D.nonInitAtomicWriteIds D.nonInitAtomicWriteIds) _
      nonInitUniqueMOCheck_true (by simp [pairProduct, nonInitI, nonInitJ]) bounds
    have equality := of_decide_eq_true row same rank
    exact Fin.ext equality

def atomicAccessIds : List Nat := D.atomicReadIds ++ D.atomicWriteIds

def atomicInitializerCoverageCheck : Bool :=
  atomicAccessIds.all fun access =>
    D.atomicInitializerPairs.any fun pair => pair.1 == access

def atomicInitializerBoundsCheck : Bool := pairBoundsCheck D.atomicInitializerPairs

def atomicInitializerWitnessCheck : Bool :=
  listedPairCheck D.atomicInitializerPairs fun access initializer => decide (
    (canonicalCandidate.event initializer).action.isInit = true ∧
    canonicalCandidate.sameLocation access initializer = true)

theorem atomicInitializerCoverageCheck_true :
    atomicInitializerCoverageCheck = true := by decide

theorem atomicInitializerBoundsCheck_true :
    atomicInitializerBoundsCheck = true := by decide

theorem atomicInitializerWitnessCheck_true :
    atomicInitializerWitnessCheck = true := by decide

theorem atomicAccess_has_initializer_pair (i : canonicalCandidate.Id)
    (accessing : canonicalCandidate.isAtomicRead i = true ∨
      canonicalCandidate.isAtomicWrite i = true) :
    ∃ initializer, (i.val, initializer) ∈ D.atomicInitializerPairs := by
  have member : i.val ∈ atomicAccessIds := by
    simp only [atomicAccessIds, List.mem_append]
    rcases accessing with reading | writing
    · exact Or.inl ((isAtomicRead_iff_mem i).mp reading)
    · exact Or.inr ((isAtomicWrite_iff_mem i).mp writing)
  have coverage := atomicInitializerCoverageCheck_true
  unfold atomicInitializerCoverageCheck at coverage
  have row := (List.all_eq_true.mp coverage) i.val member
  rcases List.any_eq_true.mp row with ⟨pair, pairMember, first⟩
  have firstEq : pair.1 = i.val := beq_iff_eq.mp first
  rcases pair with ⟨firstId, initializerId⟩
  dsimp at firstEq ⊢
  subst firstId
  exact ⟨initializerId, pairMember⟩

theorem canonicalCandidate_atomicInitialized :
    ∀ i : canonicalCandidate.Id,
      (canonicalCandidate.isAtomicRead i = true ∨
        canonicalCandidate.isAtomicWrite i = true) →
      ∃ init : canonicalCandidate.Id,
        (canonicalCandidate.event init).action.isInit = true ∧
        canonicalCandidate.sameLocation i init = true := by
  intro i accessing
  rcases atomicAccess_has_initializer_pair i accessing with
    ⟨initializerNat, pairMember⟩
  have bounds := pairBounds_of_check D.atomicInitializerPairs
    atomicInitializerBoundsCheck_true pairMember
  let initializer := certificateId initializerNat bounds.2
  refine ⟨initializer, ?_⟩
  have row := listedPair_of_check D.atomicInitializerPairs
    (fun access initializer => decide (
      (canonicalCandidate.event initializer).action.isInit = true ∧
      canonicalCandidate.sameLocation access initializer = true))
    atomicInitializerWitnessCheck_true pairMember bounds
  have witness := of_decide_eq_true row
  have same : certificateId i.val bounds.1 = i := by apply Fin.ext; rfl
  simpa [initializer, same] using witness

theorem canonicalCandidate_dependenciesInBounds :
    ∀ i : canonicalCandidate.Id,
      ∀ dependency ∈ (canonicalCandidate.event i).dependsOn,
        dependency < canonicalCandidate.events.size := by
  intro i dependency member
  rcases canonicalEventCore i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, _⟩
  exact of_decide_eq_true ((List.all_eq_true.mp bounds) dependency member)

theorem canonicalCandidate_depsForward :
    ∀ event : canonicalCandidate.Id,
      ∀ dependency ∈ (canonicalCandidate.event event).dependsOn,
        dependency < event.val := by
  intro event dependency member
  rcases canonicalEventCore event with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, forward, _⟩
  exact of_decide_eq_true ((List.all_eq_true.mp forward) dependency member)

theorem canonicalCandidate_declaredAccessTyped :
    canonicalCandidate.DeclaredAccessTyped declaredAccessClass := by
  unfold Memory.Candidate.DeclaredAccessTyped
  intro event location atLocation nonInit
  rcases canonicalEventCore event with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, typed, _, _, _⟩
  rw [atLocation] at typed
  simp only [nonInit, Bool.false_or, decide_eq_true_eq] at typed
  exact typed

theorem eventSupport (event : canonicalCandidate.Id) :
    ((canonicalCandidate.event event).action.isPlain = true ↔
      event.val ∈ D.plainAccessIds) ∧
    (canonicalCandidate.isWrite event = true ↔ event.val ∈ D.writeIds) ∧
    ((canonicalCandidate.event event).action.location.isSome = true ↔
      event.val ∈ D.accessIds) := by
  rcases canonicalEventCore event with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      plain, write, access⟩
  exact ⟨plain, write, access⟩

theorem isPlain_iff_mem (event : canonicalCandidate.Id) :
    (canonicalCandidate.event event).action.isPlain = true ↔
      event.val ∈ D.plainAccessIds := (eventSupport event).1

theorem isWrite_iff_mem (event : canonicalCandidate.Id) :
    canonicalCandidate.isWrite event = true ↔ event.val ∈ D.writeIds :=
  (eventSupport event).2.1

theorem hasLocation_iff_mem (event : canonicalCandidate.Id) :
    (canonicalCandidate.event event).action.location.isSome = true ↔
      event.val ∈ D.accessIds := (eventSupport event).2.2

theorem canonicalCandidate_readFromTyped : canonicalCandidate.ReadFromTyped := by
  unfold Memory.Candidate.ReadFromTyped
  intro read source _ sourceEdge
  have pairMember := (readSource_iff_mem read source).mp sourceEdge
  have readBound : read.val < 88 := certificateId_bound read
  have sourceBound : source.val < 88 := certificateId_bound source
  have witness := readFromPairCore_of_mem pairMember ⟨readBound, sourceBound⟩
  have sameRead : certificateId read.val readBound = read := by apply Fin.ext; rfl
  have sameSource : certificateId source.val sourceBound = source := by apply Fin.ext; rfl
  simpa [sameRead, sameSource] using witness.2.2.2.2.2

end JuliaLean.CRuntime.WorldStop
