import JuliaLean.CRuntime.WorldStop.C11CertificateSC

namespace JuliaLean.CRuntime.WorldStop

open Memory
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def syncPairBoundsCheck : Bool :=
  pairBoundsCheck C11CertificateData.synchronizesWithPairs

theorem syncPairBoundsCheck_true : syncPairBoundsCheck = true := by decide

theorem listed_sync_pair {pair : Nat × Nat}
    (member : pair ∈ C11CertificateData.synchronizesWithPairs) :
    canonicalCandidate.synchronizesWith
      (certificateId pair.1
        (pairBounds_of_check _ syncPairBoundsCheck_true member).1)
      (certificateId pair.2
        (pairBounds_of_check _ syncPairBoundsCheck_true member).2) = true := by
  have bounds := pairBounds_of_check C11CertificateData.synchronizesWithPairs
    syncPairBoundsCheck_true member
  simp [C11CertificateData.synchronizesWithPairs] at member
  rcases member with first | second | third | fourth | fifth
  · rcases first with ⟨rfl, rfl⟩
    change canonicalCandidate.synchronizesWith
      (certificateId 33 (by decide)) (certificateId 75 (by decide)) = true
    apply Bool.or_eq_true_iff.mpr
    apply Or.inr
    rw [unlockAction_eq _ (by decide), lockAction_eq _ (by decide)]
    decide
  · rcases second with ⟨rfl, rfl⟩
    change canonicalCandidate.synchronizesWith
      (certificateId 36 (by decide)) (certificateId 46 (by decide)) = true
    apply Bool.or_eq_true_iff.mpr
    apply Or.inr
    rw [unlockAction_eq _ (by decide), lockAction_eq _ (by decide)]
    decide
  · rcases third with ⟨rfl, rfl⟩
    change canonicalCandidate.synchronizesWith
      (certificateId 38 (by decide)) (certificateId 68 (by decide)) = true
    exact Memory.Candidate.release_store_acquire_load_sync
      (loc := .gcState 3) (stored := 2) (observed := 2)
      rfl rfl rfl
  · rcases fourth with ⟨rfl, rfl⟩
    change canonicalCandidate.synchronizesWith
      (certificateId 44 (by decide)) (certificateId 62 (by decide)) = true
    exact Memory.Candidate.release_store_acquire_load_sync
      (loc := .gcState 1) (stored := 1) (observed := 1)
      rfl rfl rfl
  · rcases fifth with ⟨rfl, rfl⟩
    change canonicalCandidate.synchronizesWith
      (certificateId 54 (by decide)) (certificateId 74 (by decide)) = true
    apply Bool.or_eq_true_iff.mpr
    apply Or.inr
    rw [unlockAction_eq _ (by decide), lockAction_eq _ (by decide)]
    decide

def conflictPairBoundsCheck : Bool :=
  pairBoundsCheck C11CertificateData.ordinaryConflictPairs

theorem conflictPairBoundsCheck_true : conflictPairBoundsCheck = true := by decide

def conflictPairOrderCheck : Bool :=
  C11CertificateData.ordinaryConflictPairs.all fun pair => decide (
    (pair.1 < 20 ∧ 20 ≤ pair.2) ∨
    (20 ≤ pair.1 ∧ C11CertificateData.eventThread pair.1 =
      C11CertificateData.eventThread pair.2 ∧ pair.1 < pair.2))

theorem conflictPairOrderCheck_true : conflictPairOrderCheck = true := by decide

theorem listed_conflict_has_hbEdge {pair : Nat × Nat}
    (member : pair ∈ C11CertificateData.ordinaryConflictPairs) :
    canonicalCandidate.hbEdge
      (certificateId pair.1
        (pairBounds_of_check _ conflictPairBoundsCheck_true member).1)
      (certificateId pair.2
        (pairBounds_of_check _ conflictPairBoundsCheck_true member).2) = true := by
  have bounds := pairBounds_of_check C11CertificateData.ordinaryConflictPairs
    conflictPairBoundsCheck_true member
  have check := conflictPairOrderCheck_true
  unfold conflictPairOrderCheck at check
  have order := of_decide_eq_true
    ((List.all_eq_true.mp check) pair member)
  let first := certificateId pair.1 bounds.1
  let second := certificateId pair.2 bounds.2
  rcases order with initialized | sequenced
  · have firstInit : (canonicalCandidate.event first).action.isInit = true :=
      (isInit_iff_mem first).mpr
        ((C11CertificateData.initializerIds_exact pair.1).mpr initialized.1)
    have secondInit : (canonicalCandidate.event second).action.isInit = false := by
      cases init : (canonicalCandidate.event second).action.isInit with
      | false => rfl
      | true =>
        have member := (isInit_iff_mem second).mp init
        have below := (C11CertificateData.initializerIds_exact pair.2).mp member
        omega
    have edge : canonicalCandidate.hbEdge first second = true := by
      simp [Memory.Candidate.hbEdge, firstInit, secondInit]
    simpa [first, second] using edge
  · have firstInit : (canonicalCandidate.event first).action.isInit = false := by
      cases init : (canonicalCandidate.event first).action.isInit with
      | false => rfl
      | true =>
        have member := (isInit_iff_mem first).mp init
        have below := (C11CertificateData.initializerIds_exact pair.1).mp member
        omega
    have secondInit : (canonicalCandidate.event second).action.isInit = false := by
      cases init : (canonicalCandidate.event second).action.isInit with
      | false => rfl
      | true =>
        have member := (isInit_iff_mem second).mp init
        have below := (C11CertificateData.initializerIds_exact pair.2).mp member
        omega
    have threads : (canonicalCandidate.event first).thread =
        (canonicalCandidate.event second).thread := by
      rw [eventThread_eq first, eventThread_eq second]
      exact sequenced.2.1
    have idOrder : first.val < second.val := by
      change pair.1 < pair.2
      exact sequenced.2.2
    have edge : canonicalCandidate.sequencedBefore first second = true := by
      simp [Memory.Candidate.sequencedBefore, firstInit, secondInit,
        threads, idOrder]
    have hb : canonicalCandidate.hbEdge first second = true := by
      simp [Memory.Candidate.hbEdge, edge]
    simpa [first, second] using hb

def readFromForwardCheck : Bool :=
  C11CertificateData.readFromPairs.all fun pair =>
    decide (pair.2 < pair.1)

theorem readFromForwardCheck_true : readFromForwardCheck = true := by decide

theorem canonicalCandidate_rfForward :
    ∀ read source : canonicalCandidate.Id,
      canonicalCandidate.readSource read source = true → source.val < read.val := by
  intro read source edge
  have member := (readSource_iff_mem read source).mp edge
  have check := readFromForwardCheck_true
  unfold readFromForwardCheck at check
  exact of_decide_eq_true
    ((List.all_eq_true.mp check) (read.val, source.val) member)

theorem eventEarlier_true_iff (first second : canonicalCandidate.Id) :
    eventEarlier canonicalCandidate first second = true ↔ first.val < second.val := by
  simp [eventEarlier]

theorem canonicalCandidate_sequencedBefore_forward
    (first second : canonicalCandidate.Id)
    (edge : canonicalCandidate.sequencedBefore first second = true) :
    first.val < second.val := by
  simp only [Memory.Candidate.sequencedBefore, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at edge
  exact edge.2

theorem canonicalCandidate_init_forward
    (first second : canonicalCandidate.Id)
    (initializer : (canonicalCandidate.event first).action.isInit = true)
    (concurrent : (canonicalCandidate.event second).action.isInit = false) :
    first.val < second.val := by
  have firstMember := (isInit_iff_mem first).mp initializer
  have firstBound := (C11CertificateData.initializerIds_exact first.val).mp firstMember
  have secondNotMember : second.val ∉ C11CertificateData.initializerIds := by
    intro member
    have initialized := (isInit_iff_mem second).mpr member
    rw [concurrent] at initialized
    cases initialized
  have secondLower : 20 ≤ second.val := by
    by_cases below : second.val < 20
    · exact (secondNotMember
        ((C11CertificateData.initializerIds_exact second.val).mpr below)).elim
    · omega
  omega

theorem expectedLocation_eq_of_same (first second : canonicalCandidate.Id)
    (same : canonicalCandidate.sameLocation first second = true) :
    C11CertificateData.eventLocation first.val =
      C11CertificateData.eventLocation second.val := by
  simp only [Memory.Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same
  rw [eventLocation_eq first, eventLocation_eq second] at same
  exact same.2

def atomicWriteBlocks : List (List Nat) :=
  [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15],
   [16, 17, 18, 19], [27, 30, 38, 44], [48, 78, 81, 82]]

def atomicWriteBlockCoverageCheck : Bool :=
  C11CertificateData.atomicWriteIds.all fun id =>
    atomicWriteBlocks.any fun block => decide (id ∈ block)

theorem atomicWriteBlockCoverageCheck_true :
    atomicWriteBlockCoverageCheck = true := by decide

theorem atomicWrite_has_block {id : Nat}
    (member : id ∈ C11CertificateData.atomicWriteIds) :
    ∃ block, block ∈ atomicWriteBlocks ∧ id ∈ block := by
  have check := atomicWriteBlockCoverageCheck_true
  unfold atomicWriteBlockCoverageCheck at check
  have row := (List.all_eq_true.mp check) id member
  rcases List.any_eq_true.mp row with ⟨block, blockMember, idMember⟩
  exact ⟨block, blockMember, of_decide_eq_true idMember⟩

def AtomicWriteOrderCore (first second : canonicalCandidate.Id) : Prop :=
  (canonicalCandidate.sameLocation first second = true → first.val < second.val →
    (canonicalCandidate.event first).mo < (canonicalCandidate.event second).mo) ∧
  (canonicalCandidate.sameLocation first second = true →
    (canonicalCandidate.event first).mo < (canonicalCandidate.event second).mo →
    first.val < second.val)

def atomicWriteOrderPredicate (first second : Nat) : Bool :=
  decide (C11CertificateData.eventLocation first = C11CertificateData.eventLocation second →
    first < second → C11CertificateData.eventMO first < C11CertificateData.eventMO second) &&
  decide (C11CertificateData.eventLocation first = C11CertificateData.eventLocation second →
    C11CertificateData.eventMO first < C11CertificateData.eventMO second → first < second)

def atomicWriteOrderBlockCheck (first second : List Nat) : Bool :=
  (pairProduct first second).all fun pair =>
    atomicWriteOrderPredicate pair.1 pair.2

theorem atomicWriteOrderBlockCheck_true (first second : List Nat)
    (firstMember : first ∈ atomicWriteBlocks)
    (secondMember : second ∈ atomicWriteBlocks) :
    atomicWriteOrderBlockCheck first second = true := by
  simp [atomicWriteBlocks] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem atomicWriteOrderCore (first second : canonicalCandidate.Id)
    (firstWriting : canonicalCandidate.isAtomicWrite first = true)
    (secondWriting : canonicalCandidate.isAtomicWrite second = true) :
    AtomicWriteOrderCore first second := by
  have firstIdMember := (isAtomicWrite_iff_mem first).mp firstWriting
  have secondIdMember := (isAtomicWrite_iff_mem second).mp secondWriting
  rcases atomicWrite_has_block firstIdMember with
    ⟨firstBlock, firstBlockMember, firstMember⟩
  rcases atomicWrite_has_block secondIdMember with
    ⟨secondBlock, secondBlockMember, secondMember⟩
  have pairMember : (first.val, second.val) ∈
      pairProduct firstBlock secondBlock := by
    simp [pairProduct, firstMember, secondMember]
  have check := atomicWriteOrderBlockCheck_true firstBlock secondBlock
    firstBlockMember secondBlockMember
  unfold atomicWriteOrderBlockCheck at check
  have row := (List.all_eq_true.mp check) (first.val, second.val) pairMember
  unfold atomicWriteOrderPredicate at row
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  constructor
  · intro same order
    have locationEq := expectedLocation_eq_of_same first second same
    have result := row.1 locationEq order
    rw [eventMO_eq first, eventMO_eq second]
    exact result
  · intro same order
    have locationEq := expectedLocation_eq_of_same first second same
    have result := row.2 locationEq
    rw [eventMO_eq first, eventMO_eq second] at order
    exact result order

theorem canonicalCandidate_sameLocWrites_moForward
    (first second : canonicalCandidate.Id)
    (firstWriting : canonicalCandidate.isAtomicWrite first = true)
    (secondWriting : canonicalCandidate.isAtomicWrite second = true)
    (same : canonicalCandidate.sameLocation first second = true)
    (order : first.val < second.val) :
    (canonicalCandidate.event first).mo < (canonicalCandidate.event second).mo :=
  (atomicWriteOrderCore first second firstWriting secondWriting).1 same order

theorem canonicalCandidate_sameLocWrites_idForward
    (first second : canonicalCandidate.Id)
    (firstWriting : canonicalCandidate.isAtomicWrite first = true)
    (secondWriting : canonicalCandidate.isAtomicWrite second = true)
    (same : canonicalCandidate.sameLocation first second = true)
    (order : (canonicalCandidate.event first).mo <
      (canonicalCandidate.event second).mo) : first.val < second.val :=
  (atomicWriteOrderCore first second firstWriting secondWriting).2 same order

theorem canonicalCandidate_releaseSequence_forward
    (head last : canonicalCandidate.Id)
    (sequence : canonicalCandidate.releaseSequence head last = true) :
    head.val ≤ last.val := by
  simp only [Memory.Candidate.releaseSequence, Bool.and_eq_true,
    decide_eq_true_eq] at sequence
  have headWrite := sequence.1.1.1.1
  have lastWrite := sequence.1.1.1.2
  have same := sequence.1.1.2
  have ranks := sequence.1.2
  rcases Nat.lt_or_eq_of_le ranks with lower | equal
  · exact Nat.le_of_lt
      (canonicalCandidate_sameLocWrites_idForward head last
        headWrite lastWrite same lower)
  · have sameEvent := canonicalCandidate_uniqueMO head last
      headWrite lastWrite same equal
    subst last
    exact Nat.le_refl _

theorem canonicalCandidate_releaseEndpoint_forward
    (event head : canonicalCandidate.Id)
    (endpoint : canonicalCandidate.releaseEndpoint event head = true) :
    event.val ≤ head.val := by
  simp only [Memory.Candidate.releaseEndpoint, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at endpoint
  rcases endpoint with direct | fenced
  · exact Nat.le_of_eq (congrArg Fin.val direct.1)
  · exact Nat.le_of_lt
      (canonicalCandidate_sequencedBefore_forward event head fenced.2)

theorem canonicalCandidate_acquireEndpoint_forward
    (read event : canonicalCandidate.Id)
    (endpoint : canonicalCandidate.acquireEndpoint read event = true) :
    read.val ≤ event.val := by
  simp only [Memory.Candidate.acquireEndpoint, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at endpoint
  rcases endpoint with direct | fenced
  · exact Nat.le_of_eq (congrArg Fin.val direct.1)
  · exact Nat.le_of_lt
      (canonicalCandidate_sequencedBefore_forward read event fenced.2)

theorem readsSequence_forward_of {Loc : Type} [DecidableEq Loc]
    (candidate : Memory.Candidate Loc Nat)
    (releaseForward : ∀ head source : candidate.Id,
      candidate.releaseSequence head source = true → head.val ≤ source.val)
    (rfForward : ∀ read source : candidate.Id,
      candidate.readSource read source = true → source.val < read.val)
    (head read : candidate.Id) (sequence : candidate.readsSequence head read = true) :
    head.val < read.val := by
  simp only [Memory.Candidate.readsSequence, Bool.and_eq_true,
    Bool.not_eq_true'] at sequence
  have sourceExists := sequence.2
  rw [List.any_eq_true] at sourceExists
  rcases sourceExists with ⟨source, _, sourceData⟩
  simp only [Bool.and_eq_true] at sourceData
  have headBeforeSource := releaseForward head source sourceData.2
  have sourceBeforeRead := rfForward read source sourceData.1
  omega

theorem canonicalCandidate_readsSequence_forward
    (head read : canonicalCandidate.Id)
    (sequence : canonicalCandidate.readsSequence head read = true) :
    head.val < read.val := by
  exact readsSequence_forward_of canonicalCandidate
    canonicalCandidate_releaseSequence_forward canonicalCandidate_rfForward
    head read sequence

def mutexSyncBranch {Loc : Type} [DecidableEq Loc]
    (candidate : Memory.Candidate Loc Nat) (first second : candidate.Id) : Bool :=
  match (candidate.event first).action, (candidate.event second).action with
  | .unlock firstMutex, .lock secondMutex =>
      firstMutex == secondMutex && decide (first.val < second.val)
  | _, _ => false

theorem mutexSync_forward_of {Loc : Type} [DecidableEq Loc]
    (candidate : Memory.Candidate Loc Nat)
    (first second : candidate.Id)
    (edge : mutexSyncBranch candidate first second = true) : first.val < second.val := by
  unfold mutexSyncBranch at edge
  generalize firstActionEq : (candidate.event first).action = firstAction at edge
  generalize secondActionEq : (candidate.event second).action = secondAction at edge
  cases firstAction <;> cases secondAction <;>
    simp_all only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.false_eq_true]

theorem canonicalCandidate_mutexSync_forward
    (first second : canonicalCandidate.Id)
    (edge : mutexSyncBranch canonicalCandidate first second = true) : first.val < second.val :=
  mutexSync_forward_of canonicalCandidate first second edge

theorem synchronizesWith_forward_of {Loc : Type} [DecidableEq Loc]
    (candidate : Memory.Candidate Loc Nat)
    (releaseForward : ∀ first head : candidate.Id,
      candidate.releaseEndpoint first head = true → first.val ≤ head.val)
    (readsForward : ∀ head read : candidate.Id,
      candidate.readsSequence head read = true → head.val < read.val)
    (acquireForward : ∀ read second : candidate.Id,
      candidate.acquireEndpoint read second = true → read.val ≤ second.val)
    (first second : candidate.Id) (edge : candidate.synchronizesWith first second = true) :
    first.val < second.val := by
  simp only [Memory.Candidate.synchronizesWith, Bool.or_eq_true] at edge
  rcases edge with atomic | mutex
  · rw [List.any_eq_true] at atomic
    rcases atomic with ⟨head, _, headData⟩
    simp only [Bool.and_eq_true] at headData
    have readExists := headData.2
    rw [List.any_eq_true] at readExists
    rcases readExists with ⟨read, _, readData⟩
    simp only [Bool.and_eq_true] at readData
    have firstToHead := releaseForward first head headData.1
    have headToRead := readsForward head read readData.1
    have readToSecond := acquireForward read second readData.2
    omega
  · generalize firstActionEq : (candidate.event first).action = firstAction at mutex
    generalize secondActionEq : (candidate.event second).action = secondAction at mutex
    cases firstAction <;> cases secondAction <;>
      simp_all only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.false_eq_true]

theorem canonicalCandidate_sync_forward
    (first second : canonicalCandidate.Id)
    (edge : canonicalCandidate.synchronizesWith first second = true) :
    first.val < second.val := by
  exact synchronizesWith_forward_of canonicalCandidate
    canonicalCandidate_releaseEndpoint_forward
    canonicalCandidate_readsSequence_forward
    canonicalCandidate_acquireEndpoint_forward
    first second edge

theorem hbEdge_forward_of {Loc : Type} [DecidableEq Loc]
    (candidate : Memory.Candidate Loc Nat)
    (sequencedForward : ∀ first second : candidate.Id,
      candidate.sequencedBefore first second = true → first.val < second.val)
    (syncForward : ∀ first second : candidate.Id,
      candidate.synchronizesWith first second = true → first.val < second.val)
    (initForward : ∀ first second : candidate.Id,
      (candidate.event first).action.isInit = true →
      (candidate.event second).action.isInit = false → first.val < second.val)
    (first second : candidate.Id) (edge : candidate.hbEdge first second = true) :
    first.val < second.val := by
  unfold Memory.Candidate.hbEdge at edge
  rcases Bool.or_eq_true_iff.mp edge with concurrent | initialized
  · rcases Bool.or_eq_true_iff.mp concurrent with sequenced | synchronized
    · exact sequencedForward first second sequenced
    · exact syncForward first second synchronized
  · have fields := Bool.and_eq_true_iff.mp initialized
    have nonInit : (candidate.event second).action.isInit = false := by
      simpa only [Bool.not_eq_true'] using fields.2
    exact initForward first second fields.1 nonInit

theorem canonicalCandidate_hbForward :
    ∀ first second : canonicalCandidate.Id,
      canonicalCandidate.hbEdge first second = true → first.val < second.val := by
  intro first second edge
  exact hbEdge_forward_of canonicalCandidate
    canonicalCandidate_sequencedBefore_forward canonicalCandidate_sync_forward
    canonicalCandidate_init_forward first second edge

theorem canonicalCandidate_happensBeforeForward
    (first second : canonicalCandidate.Id)
    (edge : canonicalCandidate.happensBefore first second = true) :
    first.val < second.val :=
  Memory.Candidate.closure_rank (fun event : canonicalCandidate.Id => event.val)
    canonicalCandidate_hbForward edge

def writeReadLocalCheck (pair : Nat × Nat) : Bool :=
  C11CertificateData.atomicWriteIds.all fun write => decide (
    C11CertificateData.eventLocation write = C11CertificateData.eventLocation pair.1 →
    write < pair.1 →
    C11CertificateData.eventMO write ≤ C11CertificateData.eventMO pair.2)

def readWriteLocalCheck (pair : Nat × Nat) : Bool :=
  C11CertificateData.atomicWriteIds.all fun write => decide (
    C11CertificateData.eventLocation pair.1 = C11CertificateData.eventLocation write →
    pair.1 < write →
    C11CertificateData.eventMO pair.2 < C11CertificateData.eventMO write)

def readReadLocalCheck (pair : Nat × Nat) : Bool :=
  C11CertificateData.readFromPairs.all fun second => decide (
    C11CertificateData.eventLocation pair.1 = C11CertificateData.eventLocation second.1 →
    pair.1 < second.1 →
    C11CertificateData.eventMO pair.2 ≤ C11CertificateData.eventMO second.2)

def readCoherencePredicate (pair : Nat × Nat) : Bool :=
  writeReadLocalCheck pair && readWriteLocalCheck pair && readReadLocalCheck pair

def readCoherenceBlockCheck (block : List (Nat × Nat)) : Bool :=
  block.all readCoherencePredicate

def readFromBlockCoverageCheck : Bool :=
  C11CertificateData.readFromPairs.all fun pair =>
    C11CertificateData.readFromPairBlocks.any fun block => decide (pair ∈ block)

theorem readFromBlockCoverageCheck_true : readFromBlockCoverageCheck = true := by decide

theorem readFromPair_has_block {pair : Nat × Nat}
    (member : pair ∈ C11CertificateData.readFromPairs) :
    ∃ block, block ∈ C11CertificateData.readFromPairBlocks ∧ pair ∈ block := by
  have check := readFromBlockCoverageCheck_true
  unfold readFromBlockCoverageCheck at check
  have row := (List.all_eq_true.mp check) pair member
  rcases List.any_eq_true.mp row with ⟨block, blockMember, pairMember⟩
  exact ⟨block, blockMember, of_decide_eq_true pairMember⟩

theorem readCoherenceBlockCheck_true (block : List (Nat × Nat))
    (member : block ∈ C11CertificateData.readFromPairBlocks) :
    readCoherenceBlockCheck block = true := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  have indexBound := List.mem_range.mp indexMember
  have possibilities : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨
      index = 8 ∨ index = 9 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem readCoherence_of_mem {pair : Nat × Nat}
    (member : pair ∈ C11CertificateData.readFromPairs) :
    writeReadLocalCheck pair = true ∧ readWriteLocalCheck pair = true ∧
      readReadLocalCheck pair = true := by
  rcases readFromPair_has_block member with ⟨block, blockMember, pairMember⟩
  have check := readCoherenceBlockCheck_true block blockMember
  unfold readCoherenceBlockCheck at check
  have row := (List.all_eq_true.mp check) pair pairMember
  simpa [readCoherencePredicate, Bool.and_eq_true, and_assoc] using row

theorem canonicalCandidate_coherent :
    coherentAgainst canonicalCandidate (eventEarlier canonicalCandidate) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro event
    simp [eventEarlier]
  · intro first firstWrite second secondWrite same notBefore
    cases earlier : eventEarlier canonicalCandidate first second with
    | false => rfl
    | true =>
      have idOrder : first.val < second.val := by
        simpa [eventEarlier] using earlier
      have moOrder := canonicalCandidate_sameLocWrites_moForward
        first second firstWrite secondWrite same idOrder
      unfold Memory.Candidate.modificationBefore at notBefore
      simp [firstWrite, secondWrite, same, moOrder] at notBefore
  · intro write writing read reading same earlier source rf
    have writeMember := (isAtomicWrite_iff_mem write).mp writing
    have pairMember := (readSource_iff_mem read source).mp rf
    have locationEq := expectedLocation_eq_of_same write read same
    have idOrder : write.val < read.val := by
      simpa [eventEarlier] using earlier
    have core := readCoherence_of_mem pairMember
    unfold writeReadLocalCheck at core
    have writeRow := (List.all_eq_true.mp core.1) write.val writeMember
    have result := of_decide_eq_true writeRow locationEq idOrder
    rw [eventMO_eq write, eventMO_eq source]
    exact result
  · intro read reading write writing same earlier source rf
    have pairMember := (readSource_iff_mem read source).mp rf
    have writeMember := (isAtomicWrite_iff_mem write).mp writing
    have locationEq := expectedLocation_eq_of_same read write same
    have idOrder : read.val < write.val := by
      simpa [eventEarlier] using earlier
    have core := readCoherence_of_mem pairMember
    unfold readWriteLocalCheck at core
    have writeRow := (List.all_eq_true.mp core.2.1) write.val writeMember
    have result := of_decide_eq_true writeRow locationEq idOrder
    rw [eventMO_eq source, eventMO_eq write]
    exact result
  · intro first firstRead second secondRead same earlier
      firstSource firstRF secondSource secondRF
    have firstPair := (readSource_iff_mem first firstSource).mp firstRF
    have secondPair := (readSource_iff_mem second secondSource).mp secondRF
    have locationEq := expectedLocation_eq_of_same first second same
    have idOrder : first.val < second.val := by
      simpa [eventEarlier] using earlier
    have core := readCoherence_of_mem firstPair
    unfold readReadLocalCheck at core
    have secondRow := (List.all_eq_true.mp core.2.2)
      (second.val, secondSource.val) secondPair
    have result := of_decide_eq_true secondRow locationEq idOrder
    rw [eventMO_eq firstSource, eventMO_eq secondSource]
    exact result
  · intro read reading source rf
    have sourceBefore := canonicalCandidate_rfForward read source rf
    simp [eventEarlier]
    omega

def lockValidityCheck : Bool :=
  C11CertificateData.lockIds.all fun current =>
    C11CertificateData.lockIds.all fun prior => decide (
      prior < current →
      C11CertificateData.lockMutex prior = C11CertificateData.lockMutex current →
      prior < C11CertificateData.unlockForLock prior ∧
      C11CertificateData.unlockForLock prior < current ∧
      C11CertificateData.unlockForLock prior ∈ C11CertificateData.unlockIds ∧
      C11CertificateData.unlockMutex (C11CertificateData.unlockForLock prior) =
        C11CertificateData.lockMutex prior ∧
      C11CertificateData.eventThread (C11CertificateData.unlockForLock prior) =
        C11CertificateData.eventThread prior)

def unlockValidityCheck : Bool :=
  C11CertificateData.unlockIds.all fun current =>
    decide (C11CertificateData.lockForUnlock current ∈ C11CertificateData.lockIds ∧
      C11CertificateData.lockForUnlock current < current ∧
      C11CertificateData.lockMutex (C11CertificateData.lockForUnlock current) =
        C11CertificateData.unlockMutex current ∧
      C11CertificateData.eventThread (C11CertificateData.lockForUnlock current) =
        C11CertificateData.eventThread current) &&
    C11CertificateData.unlockIds.all fun other => decide (
      C11CertificateData.lockForUnlock current < other → other < current →
      C11CertificateData.unlockMutex other ≠ C11CertificateData.unlockMutex current)

def lockIdsBoundCheck : Bool :=
  C11CertificateData.lockIds.all fun id => decide (id < 88)

def unlockIdsBoundCheck : Bool :=
  C11CertificateData.unlockIds.all fun id => decide (id < 88)

theorem lockValidityCheck_true : lockValidityCheck = true := by decide
theorem unlockValidityCheck_true : unlockValidityCheck = true := by decide
theorem lockIdsBoundCheck_true : lockIdsBoundCheck = true := by decide
theorem unlockIdsBoundCheck_true : unlockIdsBoundCheck = true := by decide

theorem lockId_bound {id : Nat} (member : id ∈ C11CertificateData.lockIds) : id < 88 := by
  have check := lockIdsBoundCheck_true
  unfold lockIdsBoundCheck at check
  exact of_decide_eq_true ((List.all_eq_true.mp check) id member)

theorem unlockId_bound {id : Nat} (member : id ∈ C11CertificateData.unlockIds) : id < 88 := by
  have check := unlockIdsBoundCheck_true
  unfold unlockIdsBoundCheck at check
  exact of_decide_eq_true ((List.all_eq_true.mp check) id member)

theorem canonicalCandidate_mutex : canonicalCandidate.MutexValid := by
  intro event
  unfold Memory.Candidate.MutexEventValid
  generalize actionEq : (canonicalCandidate.event event).action = action
  cases action with
  | lock mutex =>
    have eventLockShape :
        (match (canonicalCandidate.event event).action with
          | .lock _ => true | _ => false) = true := by simp [actionEq]
    have eventMember := (isLock_iff_mem event).mp eventLockShape
    have eventAction := lockAction_eq event eventMember
    rw [actionEq] at eventAction
    have eventMutex : mutex = C11CertificateData.lockMutex event.val := by
      cases eventAction
      rfl
    intro prior priorBefore priorAction
    have priorLockShape :
        (match (canonicalCandidate.event prior).action with
          | .lock _ => true | _ => false) = true := by simp [priorAction]
    have priorMember := (isLock_iff_mem prior).mp priorLockShape
    have mappedPrior := lockAction_eq prior priorMember
    rw [priorAction] at mappedPrior
    have priorMutex : mutex = C11CertificateData.lockMutex prior.val := by
      cases mappedPrior
      rfl
    have check := lockValidityCheck_true
    unfold lockValidityCheck at check
    have eventRow := (List.all_eq_true.mp check) event.val eventMember
    have priorRow := (List.all_eq_true.mp eventRow) prior.val priorMember
    have mutexEq : C11CertificateData.lockMutex prior.val =
        C11CertificateData.lockMutex event.val := by omega
    have data := of_decide_eq_true priorRow priorBefore mutexEq
    let unlockNat := C11CertificateData.unlockForLock prior.val
    have unlockMember : unlockNat ∈ C11CertificateData.unlockIds := data.2.2.1
    let unlockEvent := certificateId unlockNat (unlockId_bound unlockMember)
    refine ⟨unlockEvent, data.1, data.2.1, ?_, ?_⟩
    · have mappedUnlock := unlockAction_eq unlockEvent unlockMember
      rw [mappedUnlock]
      congr 1
      change C11CertificateData.unlockMutex
        (C11CertificateData.unlockForLock prior.val)
        = mutex
      exact data.2.2.2.1.trans priorMutex.symm
    · rw [eventThread_eq unlockEvent, eventThread_eq prior]
      change C11CertificateData.eventThread
        (C11CertificateData.unlockForLock prior.val) =
        C11CertificateData.eventThread prior.val
      exact data.2.2.2.2
  | unlock mutex =>
    have eventUnlockShape :
        (match (canonicalCandidate.event event).action with
          | .unlock _ => true | _ => false) = true := by simp [actionEq]
    have eventMember := (isUnlock_iff_mem event).mp eventUnlockShape
    have eventAction := unlockAction_eq event eventMember
    rw [actionEq] at eventAction
    have eventMutex : mutex = C11CertificateData.unlockMutex event.val := by
      cases eventAction
      rfl
    have check := unlockValidityCheck_true
    unfold unlockValidityCheck at check
    have row := (List.all_eq_true.mp check) event.val eventMember
    simp only [Bool.and_eq_true] at row
    have partnerData := of_decide_eq_true row.1
    let lockNat := C11CertificateData.lockForUnlock event.val
    have lockMember : lockNat ∈ C11CertificateData.lockIds := partnerData.1
    let lockEvent := certificateId lockNat (lockId_bound lockMember)
    refine ⟨lockEvent, partnerData.2.1, ?_, ?_, ?_⟩
    · have mappedLock := lockAction_eq lockEvent lockMember
      rw [mappedLock]
      congr 1
      change C11CertificateData.lockMutex
        (C11CertificateData.lockForUnlock event.val)
        = mutex
      exact partnerData.2.2.1.trans eventMutex.symm
    · rw [eventThread_eq lockEvent, eventThread_eq event]
      change C11CertificateData.eventThread
        (C11CertificateData.lockForUnlock event.val) =
        C11CertificateData.eventThread event.val
      exact partnerData.2.2.2
    · intro other lockBefore otherBefore otherAction
      have otherShape :
          (match (canonicalCandidate.event other).action with
            | .unlock _ => true | _ => false) = true := by simp [otherAction]
      have otherMember := (isUnlock_iff_mem other).mp otherShape
      have otherMapped := unlockAction_eq other otherMember
      rw [otherAction] at otherMapped
      have otherMutex : mutex = C11CertificateData.unlockMutex other.val := by
        cases otherMapped
        rfl
      have noBetween := (List.all_eq_true.mp row.2) other.val otherMember
      have distinct := of_decide_eq_true noBetween lockBefore otherBefore
      apply distinct
      exact otherMutex.symm.trans eventMutex
  | _ => trivial

theorem canonicalCandidate_justificationForward
    (first second : canonicalCandidate.Id)
    (edge : canonicalCandidate.justificationEdge first second = true) :
    first.val < second.val := by
  simp only [Memory.Candidate.justificationEdge, Bool.or_eq_true, or_assoc] at edge
  rcases edge with rf | dependency | writes
  · exact canonicalCandidate_rfForward second first rf
  · exact canonicalCandidate_depsForward second first.val
      (of_decide_eq_true dependency)
  · simp only [Bool.and_eq_true, and_assoc] at writes
    exact canonicalCandidate_happensBeforeForward first second writes.2.2.2

theorem canonicalCandidate_justified : canonicalCandidate.Justified := by
  apply Memory.Candidate.justified_of_forward
  exact canonicalCandidate_justificationForward

def ordinaryConflictCoveragePredicate (first second : Nat) : Bool :=
  decide ((first ∈ C11CertificateData.plainAccessIds ∨
      second ∈ C11CertificateData.plainAccessIds) →
    (first ∈ C11CertificateData.writeIds ∨
      second ∈ C11CertificateData.writeIds) →
    C11CertificateData.eventLocation first = C11CertificateData.eventLocation second →
    first < second →
    (first, second) ∈ C11CertificateData.ordinaryConflictPairs)

def ordinaryConflictBlockCheck (block : List Nat) : Bool :=
  block.all fun first =>
    C11CertificateData.accessIds.all fun second =>
      ordinaryConflictCoveragePredicate first second

def accessBlockCoverageCheck : Bool :=
  C11CertificateData.accessIds.all fun event =>
    C11CertificateData.accessIdBlocks.any fun block => decide (event ∈ block)

theorem accessBlockCoverageCheck_true : accessBlockCoverageCheck = true := by decide

theorem accessId_has_block {event : Nat}
    (member : event ∈ C11CertificateData.accessIds) :
    ∃ block, block ∈ C11CertificateData.accessIdBlocks ∧ event ∈ block := by
  have check := accessBlockCoverageCheck_true
  unfold accessBlockCoverageCheck at check
  have row := (List.all_eq_true.mp check) event member
  rcases List.any_eq_true.mp row with ⟨block, blockMember, eventMember⟩
  exact ⟨block, blockMember, of_decide_eq_true eventMember⟩

theorem ordinaryConflictBlockCheck_true (block : List Nat)
    (member : block ∈ C11CertificateData.accessIdBlocks) :
    ordinaryConflictBlockCheck block = true := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  have indexBound := List.mem_range.mp indexMember
  have possibilities :
      index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨
      index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨
      index = 14 ∨ index = 15 ∨ index = 16 ∨ index = 17 ∨
      index = 18 := by omega
  rcases possibilities with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ordinaryConflictPairs_exact (first second : canonicalCandidate.Id)
    (order : first.val < second.val)
    (writing : canonicalCandidate.isWrite first = true ∨
      canonicalCandidate.isWrite second = true)
    (plain : (canonicalCandidate.event first).action.isPlain = true ∨
      (canonicalCandidate.event second).action.isPlain = true)
    (same : canonicalCandidate.sameLocation first second = true) :
    (first.val, second.val) ∈ C11CertificateData.ordinaryConflictPairs := by
  have sameOriginal := same
  simp only [Memory.Candidate.sameLocation, Bool.and_eq_true] at same
  have firstAccess := (hasLocation_iff_mem first).mp same.1
  have secondAccess : second.val ∈ C11CertificateData.accessIds := by
    apply (hasLocation_iff_mem second).mp
    rw [beq_iff_eq] at same
    rw [← same.2]
    exact same.1
  have plainMember : first.val ∈ C11CertificateData.plainAccessIds ∨
      second.val ∈ C11CertificateData.plainAccessIds := by
    rcases plain with firstPlain | secondPlain
    · exact Or.inl ((isPlain_iff_mem first).mp firstPlain)
    · exact Or.inr ((isPlain_iff_mem second).mp secondPlain)
  have writeMember : first.val ∈ C11CertificateData.writeIds ∨
      second.val ∈ C11CertificateData.writeIds := by
    rcases writing with firstWrite | secondWrite
    · exact Or.inl ((isWrite_iff_mem first).mp firstWrite)
    · exact Or.inr ((isWrite_iff_mem second).mp secondWrite)
  have locationEq := expectedLocation_eq_of_same first second sameOriginal
  rcases accessId_has_block firstAccess with ⟨block, blockMember, eventMember⟩
  have check := ordinaryConflictBlockCheck_true block blockMember
  unfold ordinaryConflictBlockCheck at check
  have firstRow := (List.all_eq_true.mp check) first.val eventMember
  have secondRow := (List.all_eq_true.mp firstRow) second.val secondAccess
  unfold ordinaryConflictCoveragePredicate at secondRow
  exact of_decide_eq_true secondRow plainMember writeMember locationEq order

theorem sameLocation_symm (first second : canonicalCandidate.Id)
    (same : canonicalCandidate.sameLocation first second = true) :
    canonicalCandidate.sameLocation second first = true := by
  simp only [Memory.Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same ⊢
  exact ⟨by rw [← same.2]; exact same.1, same.2.symm⟩

theorem canonicalCandidate_raceAgainst :
    raceAgainst canonicalCandidate canonicalCandidate.hbEdge := by
  intro first second distinct same plain writing
  by_cases ordered : first.val < second.val
  · have member := ordinaryConflictPairs_exact first second ordered writing plain same
    have bounds := pairBounds_of_check C11CertificateData.ordinaryConflictPairs
      conflictPairBoundsCheck_true member
    have edge := listed_conflict_has_hbEdge member
    have firstId : certificateId first.val bounds.1 = first := by apply Fin.ext; rfl
    have secondId : certificateId second.val bounds.2 = second := by apply Fin.ext; rfl
    have edge : canonicalCandidate.hbEdge first second = true := by
      simpa [firstId, secondId] using edge
    exact Or.inl edge
  · have valuesDistinct : first.val ≠ second.val := by
      intro equal
      exact distinct (Fin.ext equal)
    have reverseOrder : second.val < first.val := by omega
    have member := ordinaryConflictPairs_exact second first reverseOrder
      (Or.symm writing) (Or.symm plain) (sameLocation_symm first second same)
    have bounds := pairBounds_of_check C11CertificateData.ordinaryConflictPairs
      conflictPairBoundsCheck_true member
    have edge := listed_conflict_has_hbEdge member
    have secondId : certificateId second.val bounds.1 = second := by apply Fin.ext; rfl
    have firstId : certificateId first.val bounds.2 = first := by apply Fin.ext; rfl
    have edge : canonicalCandidate.hbEdge second first = true := by
      simpa [secondId, firstId] using edge
    exact Or.inr edge

theorem canonicalCandidate_raceFree : canonicalCandidate.RaceFree := by
  intro first second distinct same plain writing
  rcases canonicalCandidate_raceAgainst first second distinct same plain writing with
    forward | reverse
  · exact Or.inl (Memory.Candidate.happensBefore_of_hbEdge forward)
  · exact Or.inr (Memory.Candidate.happensBefore_of_hbEdge reverse)

def plainRFDirectCheck : Bool :=
  C11CertificateData.readFromPairs.all fun pair => decide (
    pair.1 ∈ C11CertificateData.plainReadIds →
    (pair.2 < 20 ∨ C11CertificateData.eventThread pair.2 =
      C11CertificateData.eventThread pair.1))

def ordinaryNoInterveningCheck : Bool :=
  C11CertificateData.readFromPairs.all fun pair =>
    C11CertificateData.ordinaryConflictPairs.all fun conflict => decide (
      pair.1 ∈ C11CertificateData.plainReadIds →
      conflict.2 = pair.1 → pair.2 < conflict.1 → False)

theorem plainRFDirectCheck_true : plainRFDirectCheck = true := by decide
theorem ordinaryNoInterveningCheck_true : ordinaryNoInterveningCheck = true := by decide

theorem plainRF_has_direct_edge (read source : canonicalCandidate.Id)
    (plainRead : read.val ∈ C11CertificateData.plainReadIds)
    (rf : canonicalCandidate.readSource read source = true) :
    canonicalCandidate.hbEdge source read = true := by
  have pairMember := (readSource_iff_mem read source).mp rf
  have check := plainRFDirectCheck_true
  unfold plainRFDirectCheck at check
  have row := (List.all_eq_true.mp check) (read.val, source.val) pairMember
  have sourceData := of_decide_eq_true row plainRead
  by_cases sourceInit : source.val < 20
  · have initSource : (canonicalCandidate.event source).action.isInit = true :=
      (isInit_iff_mem source).mpr
        ((C11CertificateData.initializerIds_exact source.val).mpr sourceInit)
    have nonInitRead : (canonicalCandidate.event read).action.isInit = false := by
      cases initialized : (canonicalCandidate.event read).action.isInit with
      | false => rfl
      | true =>
        have initMember := (isInit_iff_mem read).mp initialized
        have bound := (C11CertificateData.initializerIds_exact read.val).mp initMember
        simp [C11CertificateData.plainReadIds] at plainRead
        omega
    simp [Memory.Candidate.hbEdge, initSource, nonInitRead]
  · have sameThread : C11CertificateData.eventThread source.val =
        C11CertificateData.eventThread read.val := by
      rcases sourceData with initialized | sameThread
      · exact (sourceInit initialized).elim
      · exact sameThread
    have nonInitSource : (canonicalCandidate.event source).action.isInit = false := by
      cases initialized : (canonicalCandidate.event source).action.isInit with
      | false => rfl
      | true =>
        have initMember := (isInit_iff_mem source).mp initialized
        have bound := (C11CertificateData.initializerIds_exact source.val).mp initMember
        exact (sourceInit bound).elim
    have nonInitRead : (canonicalCandidate.event read).action.isInit = false := by
      cases initialized : (canonicalCandidate.event read).action.isInit with
      | false => rfl
      | true =>
        have initMember := (isInit_iff_mem read).mp initialized
        have bound := (C11CertificateData.initializerIds_exact read.val).mp initMember
        simp [C11CertificateData.plainReadIds] at plainRead
        omega
    have order := canonicalCandidate_rfForward read source rf
    have threadEq : (canonicalCandidate.event source).thread =
        (canonicalCandidate.event read).thread := by
      rw [eventThread_eq source, eventThread_eq read]
      exact sameThread
    have sequenced : canonicalCandidate.sequencedBefore source read = true := by
      simp [Memory.Candidate.sequencedBefore, nonInitSource, nonInitRead,
        threadEq, order]
    simp [Memory.Candidate.hbEdge, sequenced]

theorem canonicalCandidate_ordinary :
    ∀ read source : canonicalCandidate.Id,
      (canonicalCandidate.event read).action.isPlain = true →
      canonicalCandidate.isRead read = true →
      canonicalCandidate.readSource read source = true →
      canonicalCandidate.hbEdge source read = true ∧
        ∀ other : canonicalCandidate.Id,
          canonicalCandidate.isWrite other = true →
          canonicalCandidate.sameLocation read other = true →
          ¬(eventEarlier canonicalCandidate source other = true ∧
            eventEarlier canonicalCandidate other read = true) := by
  intro read source plain reading rf
  have plainRead := (isPlainRead_iff_mem read).mp ⟨reading, plain⟩
  refine ⟨plainRF_has_direct_edge read source plainRead rf, ?_⟩
  intro other writing same between
  have sourceBefore : source.val < other.val := by
    simpa [eventEarlier] using between.1
  have otherBefore : other.val < read.val := by
    simpa [eventEarlier] using between.2
  have conflictMember := ordinaryConflictPairs_exact other read otherBefore
    (Or.inl writing) (Or.inr plain) (sameLocation_symm read other same)
  have pairMember := (readSource_iff_mem read source).mp rf
  have check := ordinaryNoInterveningCheck_true
  unfold ordinaryNoInterveningCheck at check
  have pairRow := (List.all_eq_true.mp check) (read.val, source.val) pairMember
  have conflictRow := (List.all_eq_true.mp pairRow)
    (other.val, read.val) conflictMember
  exact of_decide_eq_true conflictRow plainRead rfl sourceBefore

def atomicInit0 : canonicalCandidate.Id := certificateId 0 (by decide)

theorem successfulRMW_eq_48 (event : canonicalCandidate.Id)
    (rmw : (canonicalCandidate.event event).action.isRMW = true) :
    event = scWrite48 := by
  have member := (isRMW_iff_mem event).mp rmw
  have value : event.val = 48 := by
    simpa [C11CertificateData.successfulRMWIds] using member
  apply Fin.ext
  exact value

theorem cas48_source_eq_0 (source : canonicalCandidate.Id)
    (edge : canonicalCandidate.readSource scWrite48 source = true) :
    source = atomicInit0 := by
  have member := (readSource_iff_mem scWrite48 source).mp edge
  have value : source.val = 0 := by
    change (48, source.val) ∈ C11CertificateData.readFromPairs at member
    simpa [C11CertificateData.readFromPairs] using member
  apply Fin.ext
  exact value

def rmwPredecessorDataCheck : Bool :=
  C11CertificateData.atomicWriteIds.all fun other => decide (
    C11CertificateData.eventLocation 48 = C11CertificateData.eventLocation other →
    C11CertificateData.eventMO other < C11CertificateData.eventMO 48 →
    C11CertificateData.eventMO other ≤ C11CertificateData.eventMO 0)

theorem rmwPredecessorDataCheck_true : rmwPredecessorDataCheck = true := by decide

theorem canonicalCandidate_rmw : canonicalCandidate.RMWAtomicity := by
  unfold Memory.Candidate.RMWAtomicity
  intro event rmw source edge
  have eventEq := successfulRMW_eq_48 event rmw
  subst event
  have sourceEq := cas48_source_eq_0 source edge
  subst source
  refine ⟨by decide, ?_⟩
  intro other writing same lower
  have member := (isAtomicWrite_iff_mem other).mp writing
  have locationEq := expectedLocation_eq_of_same scWrite48 other same
  have check := rmwPredecessorDataCheck_true
  unfold rmwPredecessorDataCheck at check
  have row := (List.all_eq_true.mp check) other.val member
  have result := of_decide_eq_true row locationEq
  rw [eventMO_eq other, eventMO_eq scWrite48] at lower
  rw [eventMO_eq other, eventMO_eq atomicInit0]
  exact result lower

theorem canonicalCandidate_wellFormed : canonicalCandidate.WellFormed :=
  ⟨canonicalCandidate_validOrders, canonicalCandidate_readsWitnessed,
    canonicalCandidate_nonReadsHaveNoSource, canonicalCandidate_initialMO,
    canonicalCandidate_uniqueMO, canonicalCandidate_atomicInitialized,
    canonicalCandidate_uniqueSC, canonicalCandidate_dependenciesInBounds,
    canonicalCandidate_readFromTyped⟩

theorem canonicalCandidate_certificate : ChronologicalCertificate canonicalCandidate :=
  ⟨canonicalCandidate_wellFormed, canonicalCandidate_hbForward,
    canonicalCandidate_coherent, canonicalCandidate_rmw, canonicalCandidate_sc,
    canonicalCandidate_mutex, canonicalCandidate_rfForward,
    canonicalCandidate_depsForward, canonicalCandidate_raceAgainst,
    canonicalCandidate_ordinary⟩

end JuliaLean.CRuntime.WorldStop
