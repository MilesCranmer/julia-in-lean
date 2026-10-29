import JuliaLean.CRuntime.ParallelMark.Bounds

namespace JuliaLean.CRuntime.ParallelMark

open Memory

namespace DequeRefinement

/-- Source writes to a fixed top field during one parallel marking round,
`bbfa0ce4150`, `src/work-stealing-queue.h:83,102`. Reset stores at
`src/gc-stock.c:3028,3030` belong to the following cleanup phase. -/
def TopWriteShape (location : Location) (action : Action Location Value) : Prop :=
  action.location = some location → action.writeValue.isSome = true →
    action = .init location (.i64 0) ∨
      ∃ expected desired : Int64,
        action = .cas location .seqCst .seqCst
          (.i64 expected) (.i64 desired) (.i64 expected) ∧
        desired.toInt = expected.toInt + 1

private def topValue (action : Action Location Value) : Int :=
  match action.writeValue with
  | some (.i64 value) => value.toInt
  | _ => 0

private theorem topWrite_atomic {action : Action Location Value} {location : Location}
    (shape : TopWriteShape location action) (hl : action.location = some location)
    (hw : action.writeValue.isSome = true) : action.isPlain = false := by
  rcases shape hl hw with h | ⟨expected, desired, h, _⟩ <;>
    simp [h, Action.isPlain]

private theorem topWrite_value {action : Action Location Value} {location : Location}
    (shape : TopWriteShape location action) (hl : action.location = some location)
    (hw : action.writeValue.isSome = true) :
    ∃ value : Int64, action.writeValue = some (.i64 value) := by
  rcases shape hl hw with h | ⟨expected, desired, h, _⟩
  · exact ⟨0, by simp [h, Action.writeValue]⟩
  · exact ⟨desired, by simp [h, Action.writeValue]⟩

/-- Source top values strictly increase in C11 modification order. -/
private theorem topWrite_values_strict {execution : Execution}
    (consistent : execution.consistent = true) (location : Location)
    (shape : ∀ event : execution.Id,
      TopWriteShape location (execution.event event).action)
    (left right : execution.Id)
    (leftLocation : (execution.event left).action.location = some location)
    (rightLocation : (execution.event right).action.location = some location)
    (leftWrite : execution.isWrite left = true)
    (rightWrite : execution.isWrite right = true)
    (ordered : (execution.event left).mo < (execution.event right).mo) :
    topValue (execution.event left).action < topValue (execution.event right).action := by
  have wellFormed := (of_decide_eq_true consistent : execution.Consistent).1
  have atomic (event : execution.Id)
      (hl : (execution.event event).action.location = some location)
      (hw : execution.isWrite event = true) : execution.isAtomicWrite event = true := by
    have hp := topWrite_atomic (shape event) hl hw
    simp [Candidate.isAtomicWrite, hw, hp]
  have same (a b : execution.Id)
      (ha : (execution.event a).action.location = some location)
      (hb : (execution.event b).action.location = some location) :
      execution.sameLocation a b = true := by
    simp [Candidate.sameLocation, ha, hb]
  generalize rankEq : (execution.event right).mo = rank at ordered
  induction rank using Nat.strongRecOn generalizing right left with
  | ind rank ih =>
    rcases shape right rightLocation rightWrite with initial | ⟨expected, desired, claim, increment⟩
    · have zeroRank := (wellFormed.2.2.2.1 right (atomic right rightLocation rightWrite)).mp
        (by simp [initial, Action.isInit])
      omega
    · have read : execution.isRead right = true := by
        simp [Candidate.isRead, claim, Action.readValue]
      rcases wellFormed.2.1 right read with ⟨source, rf, sourceWrite, sameSource, sourceValue⟩
      have sourceLocation : (execution.event source).action.location = some location := by
        have locations := Bool.and_eq_true_iff.mp sameSource
        have equal := beq_iff_eq.mp locations.2
        exact equal.symm.trans rightLocation
      have sourceWritten : (execution.event source).action.writeValue = some (.i64 expected) := by
        simpa [claim, Action.readValue] using sourceValue.symm
      have sourceRMW : (execution.event right).action.isRMW = true := by
        simp [claim, Action.isRMW]
      have immediate := Candidate.rmw_reads_immediate consistent right source sourceRMW rf
      have earlier : (execution.event source).mo < rank := by omega
      have beforeSource : (execution.event left).mo ≤ (execution.event source).mo :=
        immediate.2 left (atomic left leftLocation leftWrite)
          (same right left rightLocation leftLocation) (by omega)
      have sourceTop : topValue (execution.event source).action = expected.toInt := by
        simp [topValue, sourceWritten]
      have rightTop : topValue (execution.event right).action = desired.toInt := by
        simp [topValue, claim, Action.writeValue]
      rw [rightTop, increment]
      rcases Nat.lt_or_eq_of_le beforeSource with less | equal
      · have smaller := ih (execution.event source).mo earlier left source
          leftLocation sourceLocation leftWrite sourceWrite rfl less
        rw [sourceTop] at smaller
        omega
      · have sameEvent := wellFormed.2.2.2.2.1 left source
          (atomic left leftLocation leftWrite) (atomic source sourceLocation sourceWrite)
          (same left source leftLocation sourceLocation) equal
        subst source
        rw [sourceTop]
        omega

/-- Two successful source top-CAS operations cannot claim the same top value. -/
private theorem topClaims_unique {execution : Execution}
    (consistent : execution.consistent = true) (location : Location)
    (shape : ∀ event : execution.Id,
      TopWriteShape location (execution.event event).action)
    (left right : execution.Id) (expected : Int64)
    (leftClaim : (execution.event left).action =
      .cas location .seqCst .seqCst (.i64 expected) (.i64 (expected + 1)) (.i64 expected))
    (rightClaim : (execution.event right).action =
      .cas location .seqCst .seqCst (.i64 expected) (.i64 (expected + 1)) (.i64 expected)) :
    left = right := by
  have leftLocation : (execution.event left).action.location = some location := by
    simp [leftClaim, Action.location]
  have rightLocation : (execution.event right).action.location = some location := by
    simp [rightClaim, Action.location]
  have leftWrite : execution.isWrite left = true := by
    simp [Candidate.isWrite, leftClaim, Action.writeValue]
  have rightWrite : execution.isWrite right = true := by
    simp [Candidate.isWrite, rightClaim, Action.writeValue]
  have leftPlain := topWrite_atomic (shape left) leftLocation leftWrite
  have rightPlain := topWrite_atomic (shape right) rightLocation rightWrite
  have wellFormed := (of_decide_eq_true consistent : execution.Consistent).1
  rcases Nat.lt_trichotomy (execution.event left).mo (execution.event right).mo with h | h | h
  · have impossible := topWrite_values_strict consistent location shape left right
      leftLocation rightLocation leftWrite rightWrite h
    simp [topValue, leftClaim, rightClaim, Action.writeValue] at impossible
  · exact wellFormed.2.2.2.2.1 left right
      (by simp [Candidate.isAtomicWrite, leftWrite, leftPlain])
      (by simp [Candidate.isAtomicWrite, rightWrite, rightPlain])
      (by simp [Candidate.sameLocation, leftLocation, rightLocation]) h
  · have impossible := topWrite_values_strict consistent location shape right left
      rightLocation leftLocation rightWrite leftWrite h
    simp [topValue, leftClaim, rightClaim, Action.writeValue] at impossible

private theorem increment_toInt (value : Int64)
    (representable : fits64 (value.toInt + 1) = true) :
    (value + 1).toInt = value.toInt + 1 := by
  have bounds : -(2 ^ 63 : Int) ≤ value.toInt + 1 ∧ value.toInt + 1 < 2 ^ 63 :=
    of_decide_eq_true representable
  rw [Int64.toInt_add]
  change (value.toInt + 1).bmod (2 ^ 64) = value.toInt + 1
  exact Int.bmod_eq_of_le bounds.1 bounds.2

private theorem topClaim_shape (owner targetOwner : Nat) (kind targetKind : QueueKind)
    (expected observed : Int64) (representable : fits64 (expected.toInt + 1) = true) :
    TopWriteShape (.top targetOwner targetKind)
      (.cas (.top owner kind) .seqCst .seqCst
        (.i64 expected) (.i64 (expected + 1)) (.i64 observed)) := by
  intro location written
  have success : observed = expected := by
    by_cases success : observed = expected
    · exact success
    · simp [Action.writeValue, success] at written
  subst observed
  have fields := Option.some.inj location
  cases fields
  exact Or.inr ⟨expected, expected + 1, rfl, increment_toInt expected representable⟩

private def TopCensus (location : Location) (execution : Execution) : Prop :=
  ∀ event ∈ execution.events.toList, TopWriteShape location event.action

private theorem topCensus_event {location : Location} {execution : Execution}
    (census : TopCensus location execution) (event : execution.Id) :
    TopWriteShape location (execution.event event).action := by
  apply census (execution.event event)
  simp [Candidate.event, Array.getElem_mem]

@[simp] private theorem topCensus_append (location : Location)
    (execution : Execution) (event : Event Location Value) :
    TopCensus location (execution.append event) ↔
      TopCensus location execution ∧ TopWriteShape location event.action := by
  constructor
  · intro appended
    constructor
    · intro prior member
      exact appended prior (by simp [Candidate.append, member])
    · exact appended event (by simp [Candidate.append])
  · rintro ⟨prior, latest⟩ current member
    have cases : current ∈ execution.events.toList ∨ current = event := by
      simpa [Candidate.append] using member
    rcases cases with old | rfl
    · exact prior current old
    · exact latest

@[simp] private theorem updateThread_execution (s : State) (tid : Nat) (t : Thread) :
    (updateThread s tid t).execution = s.execution := rfl

@[simp] private theorem updateArray_execution (s : State) (id : Nat) (array : WsArray) :
    (updateArray s id array).execution = s.execution := rfl

@[simp] private theorem updateBuffer_execution (s : State) (id : Nat) (buffer : BufferAllocation) :
    (updateBuffer s id buffer).execution = s.execution := rfl

@[simp] private theorem checked_execution (s : State) (valid : Bool) :
    (checked s valid).execution = s.execution := rfl

@[simp] private theorem setCall_execution (s : State) (tid : Nat) (call : QueueCall) :
    (setCall s tid call).execution = s.execution := rfl

@[simp] private theorem advance_execution (s : State) (tid pc : Nat) :
    (advance s tid pc).execution = s.execution := rfl

@[simp] private theorem returnQueue_execution (s : State) (tid : Nat) (call : QueueCall) :
    (returnQueue s tid call).execution = s.execution := by
  unfold returnQueue
  cases call.operation <;> rfl

@[simp] private theorem queueControl_execution (s : State) (tid : Nat) (deps : List Nat) :
    (queueControl s tid deps).execution = s.execution := by
  unfold queueControl
  split <;> rfl

@[simp] private theorem threadControl_execution (s : State) (tid : Nat) (deps : List Nat) :
    (threadControl s tid deps).execution = s.execution := rfl

@[simp] private theorem emit_execution (s : State) (tid : Nat)
    (action : Action Location Value) (choice : Choice) (deps : List Nat) :
    (emit s tid action choice deps).execution =
      s.execution.append
        { (Event.emit tid action choice.memory) with
          dependsOn := ((s.threads tid).controlDeps ++ deps).eraseDups } := rfl

set_option maxHeartbeats 2000000 in
private theorem queueStep_census (c : Config) (s : State)
    (tid : Nat) (call : QueueCall) (ch : Choice) (owner : Nat) (kind : QueueKind)
    (census : TopCensus (.top owner kind) s.execution)
    (defined : (queueStep c s tid call ch).fault = false) :
    TopCensus (.top owner kind) (queueStep c s tid call ch).execution := by
  unfold queueStep at defined ⊢
  dsimp at defined ⊢
  all_goals repeat' (split at * <;> try simp_all [checked, emit, Event.emit,
    setCall, updateThread, updateArray, updateBuffer, queueControl, returnQueue,
    TopWriteShape, Action.location, Action.writeValue])
  all_goals try dsimp
  all_goals try exact census
  all_goals try exact topClaim_shape call.owner owner call.kind kind call.registers.t ch.i64 defined.2
  all_goals try simp_all [queueLayout, TopWriteShape, Action.location,
    Action.writeValue, increment_toInt]
  all_goals
    intro _ _ _
    exact ⟨call.registers.t, call.registers.t + 1, ⟨rfl, rfl, rfl⟩,
      increment_toInt call.registers.t defined.2⟩

private theorem countStep_census (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (owner : Nat) (kind : QueueKind)
    (census : TopCensus (.top owner kind) s.execution) :
    TopCensus (.top owner kind) (countStep c s tid ch).execution := by
  unfold countStep
  dsimp
  split <;> simp_all [checked, emit, Event.emit, updateThread, TopWriteShape,
    Action.location, Action.writeValue]

set_option maxHeartbeats 20000000 in
private theorem markStep_census (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (_after : (markStep c s tid ch).barrierPassed = false)
    (owner : Nat) (kind : QueueKind)
    (census : TopCensus (.top owner kind) s.execution) :
    TopCensus (.top owner kind) (markStep c s tid ch).execution := by
  have selectedPC := (control tid).1
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_census c s tid ch owner kind census
    | (simp_all [roundPC, checked, emit, Event.emit, advance,
        beginQueue, setCall, threadControl, updateThread, updateArray, updateBuffer,
        TopWriteShape, Action.location, Action.writeValue] <;> done)
    | split)

private theorem step_census (c : Config) (s : State) (tid : Nat) (ch : Choice)
    (control : RoundControl s) (after : (step c tid ch s).barrierPassed = false)
    (defined : (step c tid ch s).fault = false)
    (owner : Nat) (kind : QueueKind)
    (census : TopCensus (.top owner kind) s.execution) :
    TopCensus (.top owner kind) (step c tid ch s).execution := by
  have before : s.barrierPassed = false := by
    cases hb : s.barrierPassed with
    | false => rfl
    | true => have h := step_barrier c s tid ch hb; simp [after] at h
  have initial := control before
  cases fault : s.fault with
  | true => simpa [step, fault] using census
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none =>
        have markAfter : (markStep c s tid ch).barrierPassed = false := by
          simpa [step, fault, valid, call] using after
        simpa [step, fault, valid, call] using
          markStep_census c s tid ch initial before markAfter owner kind census
      | some q =>
        by_cases ownerFault : q.operation ≠ .steal ∧ q.owner ≠ tid
        · simpa [step, fault, valid, call, ownerFault] using census
        · have queueDefined : (queueStep c s tid q ch).fault = false := by
            simpa [step, fault, valid, call, ownerFault] using defined
          simpa [step, fault, valid, call, ownerFault] using
            queueStep_census c s tid q ch owner kind census queueDefined
    · simpa [step, fault, valid] using census

private theorem run_fault (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (fault : s.fault = true) : (run c schedule s).fault = true := by
  induction schedule generalizing s with
  | nil => exact fault
  | cons scheduled rest ih =>
    apply ih
    simp [step, fault]

private theorem run_census (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (control : RoundControl s) (after : (run c schedule s).barrierPassed = false)
    (defined : (run c schedule s).fault = false)
    (owner : Nat) (kind : QueueKind)
    (census : TopCensus (.top owner kind) s.execution) :
    TopCensus (.top owner kind) (run c schedule s).execution := by
  induction schedule generalizing s with
  | nil => exact census
  | cons scheduled rest ih =>
    have beforeBarrier : (step c scheduled.1 scheduled.2 s).barrierPassed = false := by
      cases hb : (step c scheduled.1 scheduled.2 s).barrierPassed with
      | false => rfl
      | true =>
        have h := run_barrier c rest (step c scheduled.1 scheduled.2 s) hb
        change (run c rest (step c scheduled.1 scheduled.2 s)).barrierPassed = false at after
        simp [after] at h
    have beforeFault : (step c scheduled.1 scheduled.2 s).fault = false := by
      cases hf : (step c scheduled.1 scheduled.2 s).fault with
      | false => rfl
      | true =>
        have h := run_fault c rest (step c scheduled.1 scheduled.2 s) hf
        change (run c rest (step c scheduled.1 scheduled.2 s)).fault = false at defined
        simp [defined] at h
    exact ih _ (step_control c s scheduled.1 scheduled.2 control) after defined
      (step_census c s scheduled.1 scheduled.2 control beforeBarrier beforeFault owner kind census)

/-- Successful source top-CAS operations claim distinct top values.
`bbfa0ce4150`, `src/work-stealing-queue.h:83,102` and
`src/gc-stock.c:2817-3004,4055-4062`. -/
private def sourceTopClaimsUnique : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)) (s : State),
    RoundControl s → ∀ owner kind,
    TopCensus (.top owner kind) s.execution →
    (run c schedule s).barrierPassed = false → (run c schedule s).fault = false →
    (run c schedule s).execution.consistent = true →
    ∀ (left right : (run c schedule s).execution.Id) (expected : Int64),
      ((run c schedule s).execution.event left).action =
        .cas (.top owner kind) .seqCst .seqCst
          (.i64 expected) (.i64 (expected + 1)) (.i64 expected) →
      ((run c schedule s).execution.event right).action =
        .cas (.top owner kind) .seqCst .seqCst
          (.i64 expected) (.i64 (expected + 1)) (.i64 expected) →
      left = right

private theorem sourceTopClaimsUnique_proven : sourceTopClaimsUnique := by
  intro c schedule s control owner kind initial before defined consistent left right expected
    leftClaim rightClaim
  have census := run_census c schedule s control before defined owner kind initial
  exact topClaims_unique consistent (.top owner kind) (topCensus_event census)
    left right expected leftClaim rightClaim

private def countTrue (predicate : α → Bool) : List α → Nat
  | [] => 0
  | value :: rest => (if predicate value then 1 else 0) + countTrue predicate rest

private theorem countTrue_le (left right : α → Bool) : ∀ values : List α,
    (∀ value ∈ values, left value = true → right value = true) →
    countTrue left values ≤ countTrue right values := by
  intro values
  induction values with
  | nil => simp [countTrue]
  | cons value rest ih =>
    intro included
    have tail := ih (fun item member => included item (by simp [member]))
    have head := included value (by simp)
    cases hl : left value <;> cases hr : right value <;>
      simp_all [countTrue]
    all_goals omega

private theorem countTrue_lt (left right : α → Bool) : ∀ values : List α,
    (∀ value ∈ values, left value = true → right value = true) →
    (∃ value ∈ values, left value = false ∧ right value = true) →
    countTrue left values < countTrue right values := by
  intro values
  induction values with
  | nil => simp
  | cons value rest ih =>
    intro included witness
    have tailIncluded : ∀ item ∈ rest, left item = true → right item = true :=
      fun item member => included item (by simp [member])
    have tailLe := countTrue_le left right rest tailIncluded
    have head := included value (by simp)
    rcases witness with ⟨item, member, hl, hr⟩
    rcases List.mem_cons.mp member with same | member
    · subst item
      simp [countTrue, hl, hr]
      omega
    · have tailLt := ih tailIncluded ⟨item, member, hl, hr⟩
      cases hv : left value <;> cases hw : right value <;>
        simp_all [countTrue]
      all_goals omega

/-- The number of happens-before predecessors of each ordinary read-from
and source-copy occurrence.
`bbfa0ce4150`, `src/work-stealing-queue.h:61,67,81,101`. -/
def predecessorRank (execution : Execution) (event : execution.Id) : Nat :=
  countTrue (fun before => execution.happensBefore before event) execution.ids

theorem predecessorRank_strict {execution : Execution}
    (defined : execution.Defined) {before after : execution.Id}
    (ordered : execution.happensBefore before after = true) :
    predecessorRank execution before < predecessorRank execution after := by
  apply countTrue_lt
  · intro event _ prior
    exact Candidate.happensBefore_trans prior ordered
  · refine ⟨before, ?_, defined.1.2.1.1 before, ordered⟩
    simp [Candidate.ids]

/-- Ordinary reads and their source-copy stores strictly advance the rank.
`bbfa0ce4150`, `src/work-stealing-queue.h:61`; the two memcpy accesses are
separate source events in the queue machine. -/
theorem copySource_rank_lt {execution : Execution}
    (defined : execution.Defined) (source read write : execution.Id)
    (ordinary : (execution.event read).action.isPlain = true)
    (reading : execution.isRead read = true)
    (readFrom : execution.readSource read source = true)
    (copied : execution.sequencedBefore read write = true) :
    predecessorRank execution source < predecessorRank execution write := by
  have sourceBefore := (defined.2.2 read source ordinary reading readFrom).1
  exact predecessorRank_strict defined
    (Candidate.happensBefore_trans sourceBefore
      (Candidate.happensBefore_of_sequencedBefore copied))

/-- The memory action at each queue source PC. Control, allocation and return
PCs emit no memory action. `bbfa0ce4150`, `src/work-stealing-queue.h:30-105`.
The resize memcpy has a read PC615 and a write PC616. -/
def queueAction (call : QueueCall) (choice : Choice) : Option (Action Location Value) :=
  let r := call.registers
  let top := Location.top call.owner call.kind
  let bottom := Location.bottom call.owner call.kind
  let array := Location.array call.owner call.kind
  match call.operation, call.pc with
  | .push, 54 => some (.load bottom .relaxed (.i64 choice.i64))
  | .push, 55 => some (.load top .acquire (.i64 choice.i64))
  | .push, 56 => some (.load array .relaxed (.address choice.address))
  | .push, 58 | .push, 59 | .push, 60 =>
    some (.plainLoad (.capacity r.ary) (.i32 choice.i32))
  | .push, 33 => some (.plainStore (.buffer r.newAry) (.address choice.address))
  | .push, 34 => some (.plainStore (.capacity r.newAry) (.i32 r.newCapacity))
  | .push, 35 => some (.plainStore (.mask r.newAry) (.i32 (r.newCapacity - 1)))
  | .push, 611 => some (.plainLoad (.mask r.ary) (.i32 choice.i32))
  | .push, 612 => some (.plainLoad (.buffer r.ary) (.address choice.address))
  | .push, 613 => some (.plainLoad (.mask r.newAry) (.i32 choice.i32))
  | .push, 614 => some (.plainLoad (.buffer r.newAry) (.address choice.address))
  | .push, 615 => some (.plainLoad
      (.slot r.buffer (maskedIndex (r.t + Int64.ofInt r.copyIndex.toInt) r.mask).toInt.toNat)
      (.payload choice.payload))
  | .push, 616 => some (.plainStore
      (.slot r.newBuffer (maskedIndex (r.t + Int64.ofInt r.copyIndex.toInt) r.newMask).toInt.toNat)
      (.payload r.value))
  | .push, 63 => some (.store array .release (.address r.newAry))
  | .push, 67 => some (.plainLoad (.mask r.ary) (.i32 choice.i32))
  | .push, 671 => some (.plainLoad (.buffer r.ary) (.address choice.address))
  | .push, 672 => some (.plainStore
      (.slot r.buffer (maskedIndex r.b r.mask).toInt.toNat) (.payload r.pushed))
  | .push, 68 => some (.fence .release)
  | .push, 69 => some (.store bottom .relaxed (.i64 (r.b + 1)))
  | .pop, 75 => some (.load bottom .relaxed (.i64 choice.i64))
  | .pop, 76 => some (.load array .relaxed (.address choice.address))
  | .pop, 77 => some (.store bottom .relaxed (.i64 r.b))
  | .pop, 78 => some (.fence .seqCst)
  | .pop, 79 => some (.load top .relaxed (.i64 choice.i64))
  | .pop, 81 => some (.plainLoad (.mask r.ary) (.i32 choice.i32))
  | .pop, 811 => some (.plainLoad (.buffer r.ary) (.address choice.address))
  | .pop, 812 => some (.plainLoad
      (.slot r.buffer (maskedIndex r.b r.mask).toInt.toNat) (.payload choice.payload))
  | .pop, 83 => some (.cas top .seqCst .seqCst
      (.i64 r.t) (.i64 (r.t + 1)) (.i64 choice.i64))
  | .pop, 85 | .pop, 90 => some (.store bottom .relaxed (.i64 (r.b + 1)))
  | .steal, 96 => some (.load top .acquire (.i64 choice.i64))
  | .steal, 97 => some (.fence .seqCst)
  | .steal, 98 => some (.load bottom .acquire (.i64 choice.i64))
  | .steal, 100 => some (.load array .relaxed (.address choice.address))
  | .steal, 101 => some (.plainLoad (.mask r.ary) (.i32 choice.i32))
  | .steal, 1011 => some (.plainLoad (.buffer r.ary) (.address choice.address))
  | .steal, 1012 => some (.plainLoad
      (.slot r.buffer (maskedIndex r.t r.mask).toInt.toNat) (.payload choice.payload))
  | .steal, 102 => some (.cas top .seqCst .seqCst
      (.i64 r.t) (.i64 (r.t + 1)) (.i64 choice.i64))
  | _, _ => none

def AppendsAction (before after : Execution) (thread : Nat) :
    Option (Action Location Value) → Prop
  | none => after = before
  | some action => ∃ event, event.thread = thread ∧
      event.action = action ∧ after = before.append event

set_option maxHeartbeats 2000000
/-- The action census is derived from `queueStep`, including every branch
of resize, failed CAS and queue return. -/
theorem queueStep_appendsAction (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) :
    AppendsAction s.execution (queueStep c s tid call choice).execution tid
      (queueAction call choice) := by
  unfold queueStep queueAction
  dsimp
  all_goals repeat' (split at * <;> try simp_all only [checked_execution,
    updateArray_execution, updateBuffer_execution, setCall_execution,
    queueControl_execution, returnQueue_execution, emit_execution])
  all_goals try dsimp
  all_goals try simp only [checked_execution, updateArray_execution, updateBuffer_execution,
    setCall_execution, queueControl_execution, returnQueue_execution, emit_execution]
  all_goals first
    | rfl
    | exact ⟨_, rfl, rfl, rfl⟩
set_option maxHeartbeats 200000

/-- The owner's bottom reservation and a thief's top observation cannot
both be hidden across the two source SC fences. This is the memory-order
part of the owner-pop/thief exclusion argument, `bbfa0ce4150`,
`src/work-stealing-queue.h:77-79,96-98`. -/
theorem scFences_exclude_crossedSources {execution : Execution}
    (defined : execution.Defined)
    (bottomWrite ownerFence topRead topSource
      topPredecessor thiefFence bottomRead bottomSource : execution.Id)
    (bottomWriting : execution.isAtomicWrite bottomWrite = true)
    (predecessorWriting : execution.isAtomicWrite topPredecessor = true)
    (predecessorSC : (execution.event topPredecessor).action.isSC = true)
    (topReading : execution.isAtomicRead topRead = true)
    (bottomReading : execution.isAtomicRead bottomRead = true)
    (sameTop : execution.sameLocation topPredecessor topRead = true)
    (sameBottom : execution.sameLocation bottomWrite bottomRead = true)
    (topReadFrom : execution.readSource topRead topSource = true)
    (bottomReadFrom : execution.readSource bottomRead bottomSource = true)
    (ownerShape : (execution.event ownerFence).action = .fence .seqCst)
    (thiefShape : (execution.event thiefFence).action = .fence .seqCst)
    (distinct : ownerFence ≠ thiefFence)
    (ownerBefore : execution.sequencedBefore bottomWrite ownerFence = true)
    (ownerAfter : execution.sequencedBefore ownerFence topRead = true)
    (thiefBefore : execution.happensBefore topPredecessor thiefFence = true)
    (thiefAfter : execution.sequencedBefore thiefFence bottomRead = true)
    (oldTop : (execution.event topSource).mo < (execution.event topPredecessor).mo)
    (oldBottom : (execution.event bottomSource).mo < (execution.event bottomWrite).mo) :
    False := by
  have wellFormed := defined.1.1
  have sc := defined.1.2.2.2.1
  have ownerSC : (execution.event ownerFence).action.isSC = true := by
    simp [ownerShape, Action.isSC, Action.order]
  have thiefSC : (execution.event thiefFence).action.isSC = true := by
    simp [thiefShape, Action.isSC, Action.order]
  have ownerIsFence : (execution.event ownerFence).action.isFence = true := by
    simp [ownerShape, Action.isFence]
  have thiefIsFence : (execution.event thiefFence).action.isFence = true := by
    simp [thiefShape, Action.isFence]
  have unequal : (execution.event ownerFence).sc ≠ (execution.event thiefFence).sc := by
    intro equal
    exact distinct (wellFormed.2.2.2.2.2.2.1 ownerFence thiefFence ownerSC thiefSC equal)
  rcases Nat.lt_trichotomy (execution.event ownerFence).sc
    (execution.event thiefFence).sc with ownerFirst | equal | thiefFirst
  · have visible := sc.2.2.2.2 bottomWrite bottomWriting bottomRead bottomReading
      sameBottom bottomSource bottomReadFrom ownerFence ownerIsFence ownerSC ownerBefore
      thiefFence thiefIsFence thiefSC thiefAfter ownerFirst
    omega
  · exact unequal equal
  · have predecessorFirst := sc.1 topPredecessor predecessorSC thiefFence thiefSC
      (Or.inl thiefBefore)
    have visible := sc.2.2.1 topPredecessor predecessorWriting predecessorSC
      topRead topReading sameTop topSource topReadFrom ownerFence ownerIsFence ownerSC
      (Nat.lt_trans predecessorFirst thiefFirst) ownerAfter
    omega

/-- Replay records the concrete pre-state of every scheduled C statement. -/
structure SourceFrame where
  state : State
  thread : Nat
  choice : Choice

def sourceLog (c : Config) : List (Nat × Choice) → State → List SourceFrame
  | [], _ => []
  | (thread, choice) :: rest, state =>
    ⟨state, thread, choice⟩ :: sourceLog c rest (step c thread choice state)

theorem sourceLog_append (c : Config) (left right : List (Nat × Choice)) (state : State) :
    sourceLog c (left ++ right) state =
      sourceLog c left state ++ sourceLog c right (run c left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons scheduled rest ih => simp only [List.cons_append, sourceLog, run, ih]

def isSlotAction (action : Action Location Value) : Bool :=
  match action.location with
  | some (.slot _ _) => true
  | _ => false

def NoNewSlots (before after : Execution) : Prop :=
  ∀ event ∈ after.events.toList, isSlotAction event.action = true →
    event ∈ before.events.toList

private theorem noNewSlots_refl (execution : Execution) :
    NoNewSlots execution execution := by
  intro event member _
  exact member

private theorem noNewSlots_append (execution : Execution) (event : Event Location Value)
    (nonSlot : isSlotAction event.action = false) :
    NoNewSlots execution (execution.append event) := by
  intro current member slot
  have cases : current ∈ execution.events.toList ∨ current = event := by
    simpa [Candidate.append] using member
  rcases cases with old | rfl
  · exact old
  · simp [nonSlot] at slot

private theorem countStep_noNewSlots (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : NoNewSlots s.execution (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> try dsimp <;> try simp only [checked_execution, updateThread_execution]
  all_goals first
    | exact noNewSlots_refl _
    | (apply noNewSlots_append; simp [Event.emit, queueLayout, isSlotAction, Action.location])

set_option maxHeartbeats 2000000 in
private theorem markStep_noNewSlots (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : NoNewSlots s.execution (markStep c s tid choice).execution := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_noNewSlots c s tid choice
    | exact noNewSlots_refl _
    | (apply noNewSlots_append; simp [Event.emit, queueLayout, isSlotAction, Action.location])
    | (simp_all [NoNewSlots, checked, emit, advance, beginQueue, setCall,
        threadControl, updateThread, updateArray, updateBuffer,
        Candidate.append, isSlotAction, Action.location] <;> done)
    | split)
  all_goals dsimp
  all_goals first
    | exact noNewSlots_refl _
    | (apply noNewSlots_append; simp [Event.emit, queueLayout, isSlotAction, Action.location])

private theorem queueStep_event_source (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (event : Event Location Value)
    (member : event ∈ (queueStep c s tid call choice).execution.events.toList) :
    event ∈ s.execution.events.toList ∨
      (queueAction call choice = some event.action ∧
        (queueStep c s tid call choice).execution = s.execution.append event) := by
  have appended := queueStep_appendsAction c s tid call choice
  cases actionChoice : queueAction call choice with
  | none =>
    have unchanged : (queueStep c s tid call choice).execution = s.execution := by
      simpa [actionChoice, AppendsAction] using appended
    exact Or.inl (by simpa [unchanged] using member)
  | some action =>
    obtain ⟨emitted, _, shape, result⟩ :
        ∃ emitted, emitted.thread = tid ∧ emitted.action = action ∧
          (queueStep c s tid call choice).execution = s.execution.append emitted := by
      simpa [actionChoice, AppendsAction] using appended
    have membership : event ∈ s.execution.events.toList ∨ event = emitted := by
      simpa [result, Candidate.append] using member
    rcases membership with prior | same
    · exact Or.inl prior
    · subst event
      exact Or.inr ⟨by simpa [shape] using actionChoice, result⟩

/-- A concrete queue call and PC, together with its emitted action. -/
def QueueSource (c : Config) (frame : SourceFrame)
    (event : Event Location Value) : Prop :=
  ∃ call, (frame.state.threads frame.thread).call = some call ∧
    queueAction call frame.choice = some event.action ∧
    (step c frame.thread frame.choice frame.state).execution =
      frame.state.execution.append event

private theorem step_slot_source (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (event : Event Location Value)
    (member : event ∈ (step c tid choice s).execution.events.toList)
    (slot : isSlotAction event.action = true) :
    event ∈ s.execution.events.toList ∨ QueueSource c ⟨s, tid, choice⟩ event := by
  change event ∈ s.execution.events.toList ∨
    ∃ call, (s.threads tid).call = some call ∧
      queueAction call choice = some event.action ∧
      (step c tid choice s).execution = s.execution.append event
  cases fault : s.fault with
  | true => exact Or.inl (by simpa [step, fault] using member)
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none =>
        have markMember : event ∈ (markStep c s tid choice).execution.events.toList := by
          simpa [step, fault, valid, call] using member
        exact Or.inl (markStep_noNewSlots c s tid choice event markMember slot)
      | some q =>
        by_cases ownerFault : q.operation ≠ .steal ∧ q.owner ≠ tid
        · exact Or.inl (by simpa [step, fault, valid, call, ownerFault] using member)
        · have queueMember : event ∈
              (queueStep c s tid q choice).execution.events.toList := by
            simpa [step, fault, valid, call, ownerFault] using member
          rcases queueStep_event_source c s tid q choice event queueMember with prior | source
          · exact Or.inl prior
          · exact Or.inr ⟨q, rfl, source.1, by
              simpa [step, fault, valid, call, ownerFault] using source.2⟩
    · exact Or.inl (by simpa [step, fault, valid] using member)

/-- Every slot access in a source run comes from an actual scheduled queue
PC, or from the supplied initial execution. No memory-consistency assumption
is needed for this census. -/
theorem run_slot_source (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (event : Event Location Value)
    (member : event ∈ (run c schedule s).execution.events.toList)
    (slot : isSlotAction event.action = true) :
    event ∈ s.execution.events.toList ∨
      ∃ frame ∈ sourceLog c schedule s, QueueSource c frame event := by
  induction schedule generalizing s with
  | nil => exact Or.inl member
  | cons scheduled rest ih =>
    rcases ih (step c scheduled.1 scheduled.2 s) member with prior | later
    · rcases step_slot_source c s scheduled.1 scheduled.2 event prior slot with initial | source
      · exact Or.inl initial
      · exact Or.inr ⟨⟨s, scheduled.1, scheduled.2⟩, by simp [sourceLog], source⟩
    · obtain ⟨frame, included, source⟩ := later
      exact Or.inr ⟨frame, by simp [sourceLog, included], source⟩

private theorem initialQueueEvents_not_slot (c : Config) (tid : Nat) (kind : QueueKind)
    (event : Event Location Value) (member : event ∈ initialQueueEvents c tid kind) :
    isSlotAction event.action = false := by
  simp [initialQueueEvents] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem initialEvents_not_slot (c : Config) (event : Event Location Value)
    (member : event ∈ initialEvents c) : isSlotAction event.action = false := by
  unfold initialEvents at member
  rcases List.mem_append.mp member with global | thread
  · simp at global
    rcases global with rfl | rfl <;> rfl
  · obtain ⟨tid, _, member⟩ := List.mem_flatMap.mp thread
    split at member
    · rcases List.mem_append.mp member with queues | requests
      · rcases List.mem_append.mp queues with chunk | pointer
        · exact initialQueueEvents_not_slot c tid .chunk event chunk
        · exact initialQueueEvents_not_slot c tid .pointer event pointer
      · simp at requests
        rcases requests with rfl | rfl | rfl <;> rfl
    · simp at member

theorem initialEvents_init (c : Config) (event : Event Location Value)
    (member : event ∈ initialEvents c) : event.action.isInit = true := by
  unfold initialEvents at member
  rcases List.mem_append.mp member with global | thread
  · simp at global
    rcases global with rfl | rfl <;> rfl
  · obtain ⟨tid, _, member⟩ := List.mem_flatMap.mp thread
    split at member
    · rcases List.mem_append.mp member with queues | requests
      · rcases List.mem_append.mp queues with chunk | pointer
        · simp [initialQueueEvents] at chunk
          rcases chunk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · simp [initialQueueEvents] at pointer
          rcases pointer with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · simp at requests
        rcases requests with rfl | rfl | rfl <;> rfl
    · simp at member

/-- Empty canonical source queues have no initialized slot payloads. Every
slot event in their actual run is therefore emitted by a concrete queue PC.
`bbfa0ce4150`, `src/gc-stock.c:3967-3979`. -/
theorem canonical_run_slot_source (c : Config) (schedule : List (Nat × Choice))
    (event : Event Location Value)
    (member : event ∈ (run c schedule (canonicalInitial c)).execution.events.toList)
    (slot : isSlotAction event.action = true) :
    ∃ frame ∈ sourceLog c schedule (canonicalInitial c), QueueSource c frame event := by
  rcases run_slot_source c schedule (canonicalInitial c) event member slot with initial | source
  · have unused := initialEvents_not_slot c event (by simpa [canonicalInitial] using initial)
    simp [unused] at slot
  · exact source

def PushSlot (call : QueueCall) (action : Action Location Value) : Prop :=
  call.operation = .push ∧ call.pc = 672 ∧
    action = .plainStore
      (.slot call.registers.buffer
        (maskedIndex call.registers.b call.registers.mask).toInt.toNat)
      (.payload call.registers.pushed)

def CopySlot (call : QueueCall) (action : Action Location Value) : Prop :=
  call.operation = .push ∧ call.pc = 616 ∧
    action = .plainStore
      (.slot call.registers.newBuffer
        (maskedIndex (call.registers.t + Int64.ofInt call.registers.copyIndex.toInt)
          call.registers.newMask).toInt.toNat)
      (.payload call.registers.value)

/-- Source writes of payloads are either the input publication memcpy or
the write half of a resize memcpy. -/
theorem queueAction_slot_write (call : QueueCall) (choice : Choice)
    (action : Action Location Value) (emitted : queueAction call choice = some action)
    (slot : isSlotAction action = true) (writing : action.writeValue.isSome = true) :
    PushSlot call action ∨ CopySlot call action := by
  unfold queueAction at emitted
  dsimp at emitted
  all_goals repeat' (split at * <;> try simp_all [PushSlot, CopySlot,
    isSlotAction, Action.location, Action.writeValue])

/-- Every slot write in the actual initialized source run is accounted for
by its concrete push PC672 or resize PC616. -/
theorem canonical_slotWrite_source (c : Config) (schedule : List (Nat × Choice))
    (event : Event Location Value)
    (member : event ∈ (run c schedule (canonicalInitial c)).execution.events.toList)
    (slot : isSlotAction event.action = true)
    (writing : event.action.writeValue.isSome = true) :
    ∃ frame ∈ sourceLog c schedule (canonicalInitial c),
      ∃ call, (frame.state.threads frame.thread).call = some call ∧
        (PushSlot call event.action ∨ CopySlot call event.action) ∧
        (step c frame.thread frame.choice frame.state).execution =
          frame.state.execution.append event := by
  obtain ⟨frame, included, call, selected, action, appended⟩ :=
    canonical_run_slot_source c schedule event member slot
  exact ⟨frame, included, call, selected,
    queueAction_slot_write call frame.choice event.action action slot writing, appended⟩

private theorem initialQueueEvents_topShape (c : Config) (tid : Nat) (kind : QueueKind)
    (owner : Nat) (targetKind : QueueKind) (event : Event Location Value)
    (member : event ∈ initialQueueEvents c tid kind) :
    TopWriteShape (.top owner targetKind) event.action := by
  simp [initialQueueEvents] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TopWriteShape, Action.location, Action.writeValue]

private theorem initialEvents_topShape (c : Config) (owner : Nat) (kind : QueueKind)
    (event : Event Location Value) (member : event ∈ initialEvents c) :
    TopWriteShape (.top owner kind) event.action := by
  unfold initialEvents at member
  rcases List.mem_append.mp member with global | thread
  · simp at global
    rcases global with rfl | rfl <;>
      simp [TopWriteShape, Action.location, Action.writeValue]
  · obtain ⟨tid, _, member⟩ := List.mem_flatMap.mp thread
    split at member
    · rcases List.mem_append.mp member with queues | requests
      · rcases List.mem_append.mp queues with chunk | pointer
        · exact initialQueueEvents_topShape c tid .chunk owner kind event chunk
        · exact initialQueueEvents_topShape c tid .pointer owner kind event pointer
      · simp at requests
        rcases requests with rfl | rfl | rfl <;>
          simp [TopWriteShape, Action.location, Action.writeValue]
    · simp at member

/-- The top-claim result instantiated at actual empty GC source queues.
Initialization and the source census are proved from `canonicalInitial`.
`bbfa0ce4150`, `src/gc-stock.c:3967-3979`. -/
theorem canonicalSourceTopClaimsUnique (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (faultFree : (run c schedule (canonicalInitial c)).fault = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (owner : Nat) (kind : QueueKind)
    (left right : (run c schedule (canonicalInitial c)).execution.Id) (expected : Int64)
    (leftClaim : ((run c schedule (canonicalInitial c)).execution.event left).action =
      .cas (.top owner kind) .seqCst .seqCst
        (.i64 expected) (.i64 (expected + 1)) (.i64 expected))
    (rightClaim : ((run c schedule (canonicalInitial c)).execution.event right).action =
      .cas (.top owner kind) .seqCst .seqCst
        (.i64 expected) (.i64 (expected + 1)) (.i64 expected)) : left = right := by
  apply sourceTopClaimsUnique_proven c schedule (canonicalInitial c)
    (canonicalInitial_control c) owner kind _ before faultFree _ left right expected
    leftClaim rightClaim
  · intro event member
    exact initialEvents_topShape c owner kind event (by simpa [canonicalInitial] using member)
  · exact decide_eq_true defined.1

def canonicalSourceTopClaimsAtMostOnce : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)),
    let state := run c schedule (canonicalInitial c)
    state.barrierPassed = false → state.fault = false → state.execution.Defined →
    ∀ (owner : Nat) (kind : QueueKind) (left right : state.execution.Id) (expected : Int64),
      (state.execution.event left).action =
        .cas (.top owner kind) .seqCst .seqCst
          (.i64 expected) (.i64 (expected + 1)) (.i64 expected) →
      (state.execution.event right).action =
        .cas (.top owner kind) .seqCst .seqCst
          (.i64 expected) (.i64 (expected + 1)) (.i64 expected) →
      left = right

theorem canonicalSourceTopClaimsAtMostOnce_proven : canonicalSourceTopClaimsAtMostOnce := by
  unfold canonicalSourceTopClaimsAtMostOnce
  intro c schedule
  dsimp
  intro before faultFree defined owner kind left right expected leftClaim rightClaim
  exact canonicalSourceTopClaimsUnique c schedule before faultFree defined
    owner kind left right expected leftClaim rightClaim

/-- A payload value obtained by a concrete earlier ordinary slot read. -/
def SlotObservation (execution : Execution) (thread : Nat) (value : Payload) : Prop :=
  ∃ event ∈ execution.events.toList, event.thread = thread ∧
    ∃ buffer index, event.action = .plainLoad (.slot buffer index) (.payload value)

@[simp] theorem slotObservation_append (execution : Execution)
    (event : Event Location Value) (thread : Nat) (value : Payload) :
    SlotObservation (execution.append event) thread value ↔
      SlotObservation execution thread value ∨
        (event.thread = thread ∧
          ∃ buffer index, event.action = .plainLoad (.slot buffer index) (.payload value)) := by
  constructor
  · rintro ⟨read, member, sameThread, buffer, index, action⟩
    have membership : read ∈ execution.events.toList ∨ read = event := by
      simpa [Candidate.append] using member
    rcases membership with prior | same
    · exact Or.inl ⟨read, prior, sameThread, buffer, index, action⟩
    · subst read
      exact Or.inr ⟨sameThread, buffer, index, action⟩
  · rintro (⟨read, member, sameThread, buffer, index, action⟩ |
      ⟨sameThread, buffer, index, action⟩)
    · exact ⟨read, by simp [Candidate.append, member], sameThread, buffer, index, action⟩
    · exact ⟨event, by simp [Candidate.append], sameThread, buffer, index, action⟩

def CallValueSources (execution : Execution) (thread : Nat) (call : QueueCall) : Prop :=
  (call.pc = 0 → call.registers.valueDeps = []) ∧
  (call.registers.valueDeps ≠ [] → SlotObservation execution thread call.registers.value) ∧
  (call.operation = .push → call.pc = 616 → call.registers.valueDeps ≠ []) ∧
  (call.operation ≠ .push → call.registers.value ≠ .zero → call.registers.valueDeps ≠ [])

def ThreadValueSources (execution : Execution) (thread : Nat) (state : Thread) : Prop :=
  (state.result ≠ .zero → SlotObservation execution thread state.result) ∧
    ∀ call, state.call = some call → CallValueSources execution thread call

def ValueSources (state : State) : Prop :=
  ∀ thread, ThreadValueSources state.execution thread (state.threads thread)

theorem canonicalInitial_valueSources (c : Config) : ValueSources (canonicalInitial c) := by
  intro thread
  unfold canonicalInitial
  dsimp
  split
  · split
    · simp [ThreadValueSources]
    · split <;> simp [ThreadValueSources]
  · simp [ThreadValueSources]

set_option maxHeartbeats 2000000 in
private theorem queueStep_valueSources (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (sources : ValueSources s)
    (selected : (s.threads tid).call = some call) :
    ValueSources (queueStep c s tid call choice) := by
  intro thread
  have old := sources thread
  have current := sources tid
  have ready := current.2 call selected
  unfold queueStep
  dsimp
  all_goals repeat' (split at * <;> try simp_all [ThreadValueSources,
    CallValueSources, checked, emit, Event.emit, queueLayout, setCall,
    queueControl, returnQueue, updateThread, updateArray, updateBuffer])

set_option maxHeartbeats 2000000 in
private theorem countStep_valueSources (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (sources : ValueSources s) : ValueSources (countStep c s tid choice) := by
  intro thread
  have old := sources thread
  have current := sources tid
  unfold countStep
  dsimp
  all_goals repeat' (split at * <;> try simp_all [ThreadValueSources,
    CallValueSources, checked, emit, Event.emit, queueLayout, updateThread])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem markStep_valueSources (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (sources : ValueSources s) : ValueSources (markStep c s tid choice) := by
  intro thread
  have old := sources thread
  have current := sources tid
  by_cases same : thread = tid <;>
  unfold markStep <;>
  dsimp <;>
  split <;> (repeat' first
    | exact countStep_valueSources c s tid choice sources thread
    | (simp_all [ThreadValueSources, CallValueSources, checked, emit, Event.emit,
        advance, beginQueue, setCall, threadControl, updateThread, updateArray,
        updateBuffer] <;> done)
    | split)
  all_goals try dsimp
  all_goals try simp_all [ThreadValueSources, CallValueSources, checked, emit,
    Event.emit, advance, beginQueue, setCall, threadControl, updateThread,
    updateArray, updateBuffer]
  all_goals cases waiting : (s.threads thread).waiting <;>
    simp_all [ThreadValueSources, CallValueSources]

theorem step_valueSources (c : Config) (s : State) (tid : Nat) (choice : Choice)
    (sources : ValueSources s) : ValueSources (step c tid choice s) := by
  unfold step
  split
  · exact sources
  · split
    · split
      · exact markStep_valueSources c s tid choice sources
      · rename_i call selected
        split
        · exact sources
        · exact queueStep_valueSources c s tid call choice sources selected
    · exact sources

theorem run_valueSources (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (sources : ValueSources s) : ValueSources (run c schedule s) := by
  induction schedule generalizing s with
  | nil => exact sources
  | cons scheduled rest ih =>
    exact ih _ (step_valueSources c s scheduled.1 scheduled.2 sources)

theorem sourceLog_valueSources (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (sources : ValueSources s) : ∀ frame ∈ sourceLog c schedule s, ValueSources frame.state := by
  induction schedule generalizing s with
  | nil => simp [sourceLog]
  | cons scheduled rest ih =>
    intro frame member
    rcases List.mem_cons.mp member with first | later
    · subst frame
      exact sources
    · exact ih _ (step_valueSources c s scheduled.1 scheduled.2 sources) frame later

/-- The value written by a source resize memcpy came from an actual earlier
slot read by the same thread. `bbfa0ce4150`,
`src/work-stealing-queue.h:61`. -/
theorem canonical_copy_valueSource (c : Config) (schedule : List (Nat × Choice))
    (frame : SourceFrame) (included : frame ∈ sourceLog c schedule (canonicalInitial c))
    (call : QueueCall) (selected : (frame.state.threads frame.thread).call = some call)
    (push : call.operation = .push) (copy : call.pc = 616) :
    SlotObservation frame.state.execution frame.thread call.registers.value := by
  have sources := sourceLog_valueSources c schedule (canonicalInitial c)
    (canonicalInitial_valueSources c) frame included
  have ready := (sources frame.thread).2 call selected
  exact ready.2.1 (ready.2.2.1 push copy)

def ExecutionPrefix (before after : Execution) : Prop :=
  ∃ suffix, after.events.toList = before.events.toList ++ suffix

@[simp] theorem executionPrefix_refl (execution : Execution) :
    ExecutionPrefix execution execution := ⟨[], by simp⟩

@[simp] theorem executionPrefix_append (execution : Execution) (event : Event Location Value) :
    ExecutionPrefix execution (execution.append event) :=
  ⟨[event], by simp [Candidate.append]⟩

theorem executionPrefix_trans {first second third : Execution}
    (left : ExecutionPrefix first second) (right : ExecutionPrefix second third) :
    ExecutionPrefix first third := by
  obtain ⟨middle, hm⟩ := left
  obtain ⟨last, hl⟩ := right
  exact ⟨middle ++ last, by rw [hl, hm, List.append_assoc]⟩

private theorem queueStep_executionPrefix (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) :
    ExecutionPrefix s.execution (queueStep c s tid call choice).execution := by
  have appended := queueStep_appendsAction c s tid call choice
  cases actionChoice : queueAction call choice with
  | none =>
    have unchanged : (queueStep c s tid call choice).execution = s.execution := by
      simpa [AppendsAction, actionChoice] using appended
    rw [unchanged]
    exact executionPrefix_refl _
  | some action =>
    obtain ⟨event, _, _, result⟩ : ∃ event, event.thread = tid ∧ event.action = action ∧
        (queueStep c s tid call choice).execution = s.execution.append event := by
      simpa [AppendsAction, actionChoice] using appended
    rw [result]
    exact executionPrefix_append _ _

private theorem countStep_executionPrefix (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : ExecutionPrefix s.execution (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> try dsimp
  all_goals first
    | exact executionPrefix_refl _
    | exact executionPrefix_append _ _

set_option maxHeartbeats 2000000 in
private theorem markStep_executionPrefix (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : ExecutionPrefix s.execution (markStep c s tid choice).execution := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_executionPrefix c s tid choice
    | (simp_all [checked, emit, advance, beginQueue, setCall,
        threadControl, updateThread, updateArray, updateBuffer] <;> done)
    | split)

theorem step_executionPrefix (c : Config) (s : State) (tid : Nat) (choice : Choice) :
    ExecutionPrefix s.execution (step c tid choice s).execution := by
  unfold step
  split
  · exact executionPrefix_refl _
  · split
    · split
      · exact markStep_executionPrefix c s tid choice
      · split
        · exact executionPrefix_refl _
        · exact queueStep_executionPrefix c s tid _ choice
    · exact executionPrefix_refl _

theorem run_executionPrefix (c : Config) (schedule : List (Nat × Choice)) (s : State) :
    ExecutionPrefix s.execution (run c schedule s).execution := by
  induction schedule generalizing s with
  | nil => exact executionPrefix_refl _
  | cons scheduled rest ih =>
    exact executionPrefix_trans (step_executionPrefix c s scheduled.1 scheduled.2)
      (ih (step c scheduled.1 scheduled.2 s))

theorem sourceLog_executionPrefix (c : Config) (schedule : List (Nat × Choice)) (s : State) :
    ∀ frame ∈ sourceLog c schedule s,
      ExecutionPrefix frame.state.execution (run c schedule s).execution ∧
      ExecutionPrefix (step c frame.thread frame.choice frame.state).execution
        (run c schedule s).execution := by
  induction schedule generalizing s with
  | nil => simp [sourceLog]
  | cons scheduled rest ih =>
    intro frame member
    rcases List.mem_cons.mp member with first | later
    · subst frame
      exact ⟨run_executionPrefix c (scheduled :: rest) s,
        run_executionPrefix c rest (step c scheduled.1 scheduled.2 s)⟩
    · exact ih _ frame later

theorem executionPrefix_get {before after : Execution}
    (extension : ExecutionPrefix before after) (index : Nat) (event : Event Location Value)
    (read : before.events[index]? = some event) :
    after.events[index]? = some event := by
  obtain ⟨suffix, equal⟩ := extension
  rw [← Array.getElem?_toList] at read ⊢
  have inside : index < before.events.toList.length := by
    by_cases inside : index < before.events.toList.length
    · exact inside
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt inside)] at read
      cases read
  rw [equal, List.getElem?_append_left inside, read]

theorem executionPrefix_size {before after : Execution}
    (extension : ExecutionPrefix before after) : before.events.size ≤ after.events.size := by
  obtain ⟨suffix, equal⟩ := extension
  have lengths := congrArg List.length equal
  simp only [List.length_append, Array.length_toList] at lengths
  omega

theorem executionPrefix_event {before after : Execution}
    (extension : ExecutionPrefix before after) (event : before.Id) :
    after.event ⟨event.val, Nat.lt_of_lt_of_le event.isLt (executionPrefix_size extension)⟩ =
      before.event event := by
  have lookup := executionPrefix_get extension event.val (before.event event)
    (Array.getElem?_eq_getElem event.isLt)
  rw [Array.getElem?_eq_getElem
    (Nat.lt_of_lt_of_le event.isLt (executionPrefix_size extension))] at lookup
  exact Option.some.inj lookup

def OneEmission (before after : Execution) : Prop :=
  after = before ∨ ∃ event, after = before.append event

private theorem queueStep_oneEmission (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) :
    OneEmission s.execution (queueStep c s tid call choice).execution := by
  have appended := queueStep_appendsAction c s tid call choice
  cases selectedAction : queueAction call choice with
  | none => exact Or.inl (by simpa [AppendsAction, selectedAction] using appended)
  | some action =>
    obtain ⟨event, _, _, equal⟩ : ∃ event, event.thread = tid ∧ event.action = action ∧
        (queueStep c s tid call choice).execution = s.execution.append event := by
      simpa [AppendsAction, selectedAction] using appended
    exact Or.inr ⟨event, equal⟩

private theorem countStep_oneEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : OneEmission s.execution (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩

private theorem markStep_oneEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : OneEmission s.execution (markStep c s tid choice).execution := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_oneEmission c s tid choice
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩
    | split)

theorem step_oneEmission (c : Config) (s : State) (tid : Nat) (choice : Choice) :
    OneEmission s.execution (step c tid choice s).execution := by
  unfold step
  split
  · exact Or.inl rfl
  · split
    · split
      · exact markStep_oneEmission c s tid choice
      · split
        · exact Or.inl rfl
        · exact queueStep_oneEmission c s tid _ choice
    · exact Or.inl rfl

def NonInitEmission (before after : Execution) : Prop :=
  before = after ∨ ∃ event, event.action.isInit = false ∧ after = before.append event

private theorem queueStep_nonInitEmission (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) :
    NonInitEmission s.execution (queueStep c s tid call choice).execution := by
  have appended := queueStep_appendsAction c s tid call choice
  cases actionChoice : queueAction call choice with
  | none =>
      left
      have unchanged : (queueStep c s tid call choice).execution = s.execution := by
        simpa [AppendsAction, actionChoice] using appended
      exact unchanged.symm
  | some action =>
      obtain ⟨event, _, shape, result⟩ : ∃ event,
          event.thread = tid ∧ event.action = action ∧
            (queueStep c s tid call choice).execution = s.execution.append event := by
        simpa [AppendsAction, actionChoice] using appended
      right
      refine ⟨event, ?_, result⟩
      unfold queueAction at actionChoice
      dsimp at actionChoice
      all_goals repeat' (split at * <;> try simp_all [shape, Action.isInit])

private theorem countStep_nonInitEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : NonInitEmission s.execution (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> first | exact Or.inl rfl | exact Or.inr ⟨_, by rfl, rfl⟩

private theorem markStep_nonInitEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) : NonInitEmission s.execution (markStep c s tid choice).execution := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_nonInitEmission c s tid choice
    | exact Or.inl rfl
    | exact Or.inr ⟨_, by rfl, rfl⟩
    | split)

theorem step_nonInitEmission (c : Config) (s : State) (tid : Nat) (choice : Choice) :
    NonInitEmission s.execution (step c tid choice s).execution := by
  unfold step
  split
  · exact Or.inl rfl
  · split
    · split
      · exact markStep_nonInitEmission c s tid choice
      · split
        · exact Or.inl rfl
        · exact queueStep_nonInitEmission c s tid _ choice
    · exact Or.inl rfl

/-- Each new memory occurrence is indexed by the pre-state of its actual
source instruction. Equal event records keep distinct occurrence indices. -/
theorem run_indexedEmission (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (event : (run c schedule s).execution.Id) :
    event.val < s.execution.events.size ∨
      ∃ frame ∈ sourceLog c schedule s,
        frame.state.execution.events.size = event.val ∧
        (step c frame.thread frame.choice frame.state).execution =
          frame.state.execution.append ((run c schedule s).execution.event event) := by
  induction schedule generalizing s with
  | nil => exact Or.inl event.isLt
  | cons scheduled rest ih =>
    rcases ih (step c scheduled.1 scheduled.2 s) event with prior | later
    · rcases step_oneEmission c s scheduled.1 scheduled.2 with same | ⟨emitted, appended⟩
      · exact Or.inl (by simpa [same] using prior)
      · by_cases initial : event.val < s.execution.events.size
        · exact Or.inl initial
        · have position : event.val = s.execution.events.size := by
            simp only [appended, Candidate.append, Array.size_push] at prior
            omega
          have lookup :
              (step c scheduled.1 scheduled.2 s).execution.events[event.val]? = some emitted := by
            simp [appended, Candidate.append, position]
          have finalLookup := executionPrefix_get
            (run_executionPrefix c rest (step c scheduled.1 scheduled.2 s))
            event.val emitted lookup
          have indexed : (run c (scheduled :: rest) s).execution.events[event.val]? =
              some ((run c (scheduled :: rest) s).execution.event event) := by
            simp [Candidate.event, event.isLt]
          have sameEvent : (run c (scheduled :: rest) s).execution.event event = emitted :=
            Option.some.inj (indexed.symm.trans finalLookup)
          exact Or.inr ⟨⟨s, scheduled.1, scheduled.2⟩, by simp [sourceLog],
            position.symm, by simpa [sameEvent] using appended⟩
    · obtain ⟨frame, member, position, appended⟩ := later
      exact Or.inr ⟨frame, by simp [sourceLog, member], position, appended⟩

/-- A resize write carries the exact ordinary-read occurrence stored in
the source register `valueDeps`. `bbfa0ce4150`,
`src/work-stealing-queue.h:61`. -/
def CopyRead (execution : Execution) (tid : Nat) (call : QueueCall) : Prop :=
  ∃ index event, call.registers.valueDeps = [index] ∧
    execution.events[index]? = some event ∧ event.thread = tid ∧
    event.action = .plainLoad
      (.slot call.registers.buffer
        (maskedIndex (call.registers.t + Int64.ofInt call.registers.copyIndex.toInt)
          call.registers.mask).toInt.toNat)
      (.payload call.registers.value)

def CopyReady (execution : Execution) (tid : Nat) (call : QueueCall) : Prop :=
  call.operation = .push → call.pc = 616 → CopyRead execution tid call

def CopyRegisters (state : State) : Prop :=
  ∀ tid call, (state.threads tid).call = some call → CopyReady state.execution tid call

theorem copyRead_prefix {before after : Execution} (extension : ExecutionPrefix before after)
    (tid : Nat) (call : QueueCall) (read : CopyRead before tid call) :
    CopyRead after tid call := by
  obtain ⟨index, event, deps, lookup, thread, action⟩ := read
  exact ⟨index, event, deps, executionPrefix_get extension index event lookup, thread, action⟩

theorem canonicalInitial_copyRegisters (c : Config) : CopyRegisters (canonicalInitial c) := by
  intro tid call selected
  unfold canonicalInitial at selected
  dsimp at selected
  all_goals repeat' (split at selected <;> try simp_all)

private theorem queueStep_selected_copyReady (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (next : QueueCall)
    (current : (s.threads tid).call = some call)
    (selected : ((queueStep c s tid call choice).threads tid).call = some next) :
    CopyReady (queueStep c s tid call choice).execution tid next := by
  intro push copy
  unfold queueStep at selected ⊢
  dsimp at selected ⊢
  all_goals repeat' (split at * <;> try simp_all [checked, emit, Event.emit,
    setCall, queueControl, returnQueue, updateThread, updateArray, updateBuffer,
    CopyRead, Candidate.append])
  all_goals subst next <;> simp_all [CopyReady, CopyRead, Candidate.append]

private theorem queueStep_copyRegisters (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (registers : CopyRegisters s)
    (current : (s.threads tid).call = some call) :
    CopyRegisters (queueStep c s tid call choice) := by
  intro thread next selected
  by_cases same : thread = tid
  · subst thread
    exact queueStep_selected_copyReady c s tid call choice next current selected
  · have unchanged : (queueStep c s tid call choice).threads thread = s.threads thread := by
      unfold queueStep
      dsimp
      split <;> (repeat' first
        | (simp_all [checked, emit, setCall, updateThread, updateArray,
            updateBuffer, queueControl, returnQueue] <;> done)
        | split)
    have old := registers thread next (by simpa [unchanged] using selected)
    intro push copy
    exact copyRead_prefix (queueStep_executionPrefix c s tid call choice)
      thread next (old push copy)

@[simp] private theorem updateThread_call (s : State) (target : Nat)
    (updated : Thread) (thread : Nat) :
    ((updateThread s target updated).threads thread).call =
      if thread = target then updated.call else (s.threads thread).call := by
  by_cases same : thread = target <;> simp [updateThread, same]

@[simp] private theorem checked_call (s : State) (valid : Bool) (thread : Nat) :
    ((checked s valid).threads thread).call = (s.threads thread).call := rfl

@[simp] private theorem emit_call (s : State) (target : Nat)
    (action : Action Location Value) (choice : Choice) (deps : List Nat)
    (thread : Nat) :
    ((emit s target action choice deps).threads thread).call =
      (s.threads thread).call := rfl

@[simp] private theorem updateArray_call (s : State) (array : Nat)
    (value : WsArray) (thread : Nat) :
    ((updateArray s array value).threads thread).call = (s.threads thread).call := rfl

@[simp] private theorem updateBuffer_call (s : State) (buffer : Nat)
    (value : BufferAllocation) (thread : Nat) :
    ((updateBuffer s buffer value).threads thread).call = (s.threads thread).call := rfl

@[simp] private theorem advance_call (s : State) (target pc thread : Nat) :
    ((advance s target pc).threads thread).call = (s.threads thread).call := by
  by_cases same : thread = target <;> simp [advance, updateThread_call, same]

@[simp] private theorem threadControl_call (s : State) (target : Nat)
    (deps : List Nat) (thread : Nat) :
    ((threadControl s target deps).threads thread).call = (s.threads thread).call := by
  by_cases same : thread = target <;> simp [threadControl, updateThread_call, same]

@[simp] private theorem beginQueue_call (s : State) (target owner : Nat)
    (kind : QueueKind) (operation : QueueOperation) (returnPC : Nat)
    (value : Payload) (deps : List Nat) (thread : Nat) :
    ((beginQueue s target owner kind operation returnPC value deps).threads thread).call =
      if thread = target then some
        { owner := owner, kind := kind, operation := operation, pc := 0,
          returnPC := returnPC,
          registers := { value, pushed := value }, addressDeps := deps,
          controlDeps := (s.threads target).controlDeps }
      else (s.threads thread).call := by
  simp [beginQueue, setCall, updateThread_call]

@[simp] private theorem notifyWaiting_call (s : State) (target thread : Nat) :
    (({ advance s target 2978 with threads := fun i =>
        let current := (advance s target 2978).threads i
        if current.waiting then { current with notified := true } else current }).threads
      thread).call = (s.threads thread).call := by
  by_cases waiting : ((advance s target 2978).threads thread).waiting <;>
    simp [waiting, advance_call]

private theorem countStep_call (c : Config) (s : State) (tid thread : Nat)
    (choice : Choice) :
    ((countStep c s tid choice).threads thread).call = (s.threads thread).call := by
  unfold countStep
  dsimp
  by_cases same : thread = tid <;>
    split <;> simp_all [checked, emit, updateThread]

set_option maxHeartbeats 2000000 in
private theorem queueStep_other_call (c : Config) (s : State) (tid thread : Nat)
    (call : QueueCall) (choice : Choice) (different : thread ≠ tid) :
    ((queueStep c s tid call choice).threads thread).call =
      (s.threads thread).call := by
  unfold queueStep
  dsimp
  all_goals repeat' (split <;> try simp_all [checked_call, emit_call, advance_call,
    setCall, updateThread_call, updateArray_call, updateBuffer_call,
    threadControl_call, returnQueue, queueControl])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem markStep_other_call (c : Config) (s : State) (tid thread : Nat)
    (choice : Choice) (different : thread ≠ tid) :
    ((markStep c s tid choice).threads thread).call =
      (s.threads thread).call := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_call c s tid thread choice
    | (simp_all [checked_call, emit_call, advance_call, beginQueue_call,
        threadControl_call, updateThread_call, updateArray_call, updateBuffer_call,
        notifyWaiting_call] <;> done)
    | split)
  all_goals try simpa only [checked_call] using notifyWaiting_call s tid thread
  all_goals simp [checked, advance, updateThread, different]
  all_goals split <;> rfl

theorem step_other_call (c : Config) (s : State) (tid thread : Nat)
    (choice : Choice) (different : thread ≠ tid) :
    ((step c tid choice s).threads thread).call = (s.threads thread).call := by
  unfold step
  split
  · rfl
  · split
    · split
      · exact markStep_other_call c s tid thread choice different
      · split
        · rfl
        · exact queueStep_other_call c s tid thread _ choice different
    · rfl

private theorem callCleared_hasScheduledFrame (c : Config) :
    ∀ (schedule : List (Nat × Choice)) (state : State) (thread : Nat)
      (call : QueueCall),
      (state.threads thread).call = some call →
      ((run c schedule state).threads thread).call = none →
      ∃ left choice right,
        schedule = left ++ (thread, choice) :: right ∧
        ((run c left state).threads thread).call = some call := by
  intro schedule
  induction schedule with
  | nil =>
      intro state thread call selected cleared
      simp [run, selected] at cleared
  | cons scheduled rest ih =>
      intro state thread call selected cleared
      by_cases same : scheduled.1 = thread
      · subst thread
        exact ⟨[], scheduled.2, rest, rfl, selected⟩
      · have preserved :
          (((step c scheduled.1 scheduled.2 state).threads thread).call) = some call := by
          rw [step_other_call c state scheduled.1 thread scheduled.2 (Ne.symm same)]
          exact selected
        obtain ⟨left, choice, right, split, active⟩ :=
          ih (step c scheduled.1 scheduled.2 state) thread call preserved (by
            simpa [run] using cleared)
        refine ⟨scheduled :: left, choice, right, ?_, ?_⟩
        · simp [split]
        · simpa [run] using active

theorem markStep_call (c : Config) (s : State) (tid thread : Nat)
    (choice : Choice) (call : QueueCall)
    (selected : ((markStep c s tid choice).threads thread).call = some call) :
    (s.threads thread).call = some call ∨ call.pc = 0 := by
  by_cases same : thread = tid <;>
  unfold markStep at selected <;>
  dsimp at selected
  all_goals repeat' (split at selected)
  all_goals try dsimp at selected
  all_goals try (apply Or.inl; simpa only [advance_call] using selected)
  all_goals try
    (apply Or.inl
     split at selected <;> simp_all only [advance_call])
  all_goals first
    | exact Or.inl selected
    | (apply Or.inl
       simpa only [checked_call, emit_call, advance_call, beginQueue_call,
         threadControl_call, updateThread_call, updateArray_call, updateBuffer_call,
         notifyWaiting_call, countStep_call, same, ite_true, ite_false] using selected)
    | (apply Or.inl
       simp only [checked_call, emit_call, advance_call, beginQueue_call,
         threadControl_call, updateThread_call, updateArray_call, updateBuffer_call,
         notifyWaiting_call, countStep_call, same, ite_true, ite_false] at selected
       split at selected <;> simp_all only)
    | (apply Or.inr
       simp only [checked_call, emit_call, advance_call, beginQueue_call,
         threadControl_call, updateThread_call, updateArray_call, updateBuffer_call,
         notifyWaiting_call, countStep_call, same, ite_true, ite_false] at selected
       have pcEq : 0 = call.pc := by
         simpa only using congrArg QueueCall.pc (Option.some.inj selected)
       exact pcEq.symm)

private theorem markStep_copyRegisters (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (registers : CopyRegisters s) :
    CopyRegisters (markStep c s tid choice) := by
  intro thread call selected push copy
  rcases markStep_call c s tid thread choice call selected with old | fresh
  · exact copyRead_prefix (markStep_executionPrefix c s tid choice)
      thread call (registers thread call old push copy)
  · omega

theorem step_copyRegisters (c : Config) (s : State) (tid : Nat) (choice : Choice)
    (registers : CopyRegisters s) : CopyRegisters (step c tid choice s) := by
  unfold step
  split
  · exact registers
  · split
    · split
      · exact markStep_copyRegisters c s tid choice registers
      · rename_i call current
        split
        · exact registers
        · exact queueStep_copyRegisters c s tid call choice registers current
    · exact registers

theorem run_copyRegisters (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (registers : CopyRegisters s) : CopyRegisters (run c schedule s) := by
  induction schedule generalizing s with
  | nil => exact registers
  | cons scheduled rest ih =>
    exact ih _ (step_copyRegisters c s scheduled.1 scheduled.2 registers)

theorem sourceLog_copyRegisters (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (registers : CopyRegisters s) :
    ∀ frame ∈ sourceLog c schedule s, CopyRegisters frame.state := by
  induction schedule generalizing s with
  | nil => simp [sourceLog]
  | cons scheduled rest ih =>
    intro frame member
    rcases List.mem_cons.mp member with first | later
    · subst frame
      exact registers
    · exact ih _ (step_copyRegisters c s scheduled.1 scheduled.2 registers) frame later

/-- Canonical source execution determines the exact resize-read occurrence
retained at PC616.
`bbfa0ce4150`, `src/work-stealing-queue.h:61`. -/
theorem canonical_copyRead (c : Config) (schedule : List (Nat × Choice))
    (frame : SourceFrame) (included : frame ∈ sourceLog c schedule (canonicalInitial c))
    (call : QueueCall) (selected : (frame.state.threads frame.thread).call = some call)
    (push : call.operation = .push) (copy : call.pc = 616) :
    CopyRead frame.state.execution frame.thread call := by
  have registers := sourceLog_copyRegisters c schedule (canonicalInitial c)
    (canonicalInitial_copyRegisters c) frame included
  exact registers frame.thread call selected push copy

def RemovalRead (execution : Execution) (thread : Nat) (call : QueueCall) : Prop :=
  ∃ read : execution.Id,
    call.registers.valueDeps = [read.val] ∧
    (execution.event read).thread = thread ∧
    ∃ buffer index, (execution.event read).action =
      .plainLoad (.slot buffer index) (.payload call.registers.value)

def CallRemovalRead (execution : Execution) (thread : Nat) (call : QueueCall) : Prop :=
  call.operation ≠ .push → call.registers.valueDeps ≠ [] →
    RemovalRead execution thread call

def RemovalRegisters (state : State) : Prop :=
  ValueSources state ∧
    ∀ thread call, (state.threads thread).call = some call →
      CallRemovalRead state.execution thread call

theorem removalRead_prefix {before after : Execution}
    (extension : ExecutionPrefix before after) (thread : Nat) (call : QueueCall)
    (ready : RemovalRead before thread call) : RemovalRead after thread call := by
  obtain ⟨read, deps, sameThread, buffer, index, action⟩ := ready
  let lifted : after.Id :=
    ⟨read.val, Nat.lt_of_lt_of_le read.isLt (executionPrefix_size extension)⟩
  refine ⟨lifted, by simpa [lifted] using deps, ?_, buffer, index, ?_⟩
  · have preserved := congrArg Event.thread (executionPrefix_event extension read)
    exact preserved.trans sameThread
  · have preserved := congrArg Event.action (executionPrefix_event extension read)
    exact preserved.trans action

theorem removalRead_fields {before after : Execution}
    (extension : ExecutionPrefix before after) (thread : Nat)
    (call next : QueueCall) (ready : RemovalRead before thread call)
    (deps : next.registers.valueDeps = call.registers.valueDeps)
    (value : next.registers.value = call.registers.value) :
    RemovalRead after thread next := by
  obtain ⟨read, oldDeps, sameThread, buffer, index, action⟩ :=
    removalRead_prefix extension thread call ready
  exact ⟨read, deps.trans oldDeps, sameThread, buffer, index, by
    simpa only [value] using action⟩

theorem callRemovalRead_fields {before after : Execution}
    (extension : ExecutionPrefix before after) (thread : Nat)
    (call next : QueueCall) (ready : CallRemovalRead before thread call)
    (operation : next.operation = call.operation)
    (deps : next.registers.valueDeps = call.registers.valueDeps)
    (value : next.registers.value = call.registers.value) :
    CallRemovalRead after thread next := by
  intro notPush nonempty
  apply removalRead_fields extension thread call next
  · apply ready
    · intro push
      exact notPush (operation.trans push)
    · intro empty
      exact nonempty (deps.trans empty)
  · exact deps
  · exact value

theorem removalRead_append (execution : Execution) (event : Event Location Value)
    (thread : Nat) (call : QueueCall) (buffer index : Nat)
    (sameThread : event.thread = thread)
    (action : event.action =
      .plainLoad (.slot buffer index) (.payload call.registers.value))
    (deps : call.registers.valueDeps = [execution.events.size]) :
    RemovalRead (execution.append event) thread call := by
  let read : (execution.append event).Id :=
    ⟨execution.events.size, by simp [Candidate.append]⟩
  refine ⟨read, by simpa [read] using deps, ?_, buffer, index, ?_⟩
  · simp [read, Candidate.event, Candidate.append, sameThread]
  · simp [read, Candidate.event, Candidate.append, action]

private theorem queueStep_slotRead_removalRead (c : Config) (s : State)
    (thread : Nat) (call next : QueueCall) (choice : Choice)
    (buffer index : Nat)
    (emitted : queueAction call choice = some
      (.plainLoad (.slot buffer index) (.payload choice.payload)))
    (deps : next.registers.valueDeps = [s.execution.events.size])
    (value : next.registers.value = choice.payload) :
    RemovalRead (queueStep c s thread call choice).execution thread next := by
  have source := queueStep_appendsAction c s thread call choice
  rw [emitted] at source
  obtain ⟨event, sameThread, action, result⟩ := source
  rw [result]
  exact removalRead_append s.execution event thread next buffer index sameThread
    (by simpa only [value] using action) deps

private theorem queueStep_slotRead_callRemovalRead (c : Config) (s : State)
    (thread : Nat) (call next : QueueCall) (choice : Choice)
    (buffer index : Nat)
    (emitted : queueAction call choice = some
      (.plainLoad (.slot buffer index) (.payload choice.payload)))
    (deps : next.registers.valueDeps = [s.execution.events.size])
    (value : next.registers.value = choice.payload) :
    CallRemovalRead (queueStep c s thread call choice).execution thread next := by
  intro _ _
  exact queueStep_slotRead_removalRead c s thread call next choice buffer index
    emitted deps value

theorem canonicalInitial_removalRegisters (c : Config) :
    RemovalRegisters (canonicalInitial c) := by
  refine ⟨canonicalInitial_valueSources c, ?_⟩
  intro thread call selected
  rw [canonicalInitial_call] at selected
  cases selected

set_option maxHeartbeats 2000000 in
private theorem queueStep_selected_removalRead (c : Config) (s : State)
    (thread : Nat) (call : QueueCall) (choice : Choice) (next : QueueCall)
    (current : (s.threads thread).call = some call)
    (sources : CallValueSources s.execution thread call)
    (ready : CallRemovalRead s.execution thread call)
    (selected : ((queueStep c s thread call choice).threads thread).call = some next) :
    CallRemovalRead (queueStep c s thread call choice).execution thread next := by
  by_cases popRead : call.operation = .pop ∧ call.pc = 812
  · have chosen := selected
    simp [queueStep, popRead.1, popRead.2, checked, emit, setCall,
      updateThread, queueControl] at chosen
    subst next
    exact queueStep_slotRead_callRemovalRead c s thread call _ choice
      call.registers.buffer
      (maskedIndex call.registers.b call.registers.mask).toInt.toNat
      (by simp [queueAction, popRead.1, popRead.2]) rfl rfl
  by_cases stealRead : call.operation = .steal ∧ call.pc = 1012
  · have chosen := selected
    simp [queueStep, stealRead.1, stealRead.2, checked, emit, setCall,
      updateThread, queueControl] at chosen
    subst next
    exact queueStep_slotRead_callRemovalRead c s thread call _ choice
      call.registers.buffer
      (maskedIndex call.registers.t call.registers.mask).toInt.toNat
      (by simp [queueAction, stealRead.1, stealRead.2]) rfl rfl
  let after := (queueStep c s thread call choice).execution
  change CallRemovalRead after thread next
  have extension : ExecutionPrefix s.execution after :=
    queueStep_executionPrefix c s thread call choice
  have preserve (updated : QueueCall)
      (operation : updated.operation = call.operation)
      (deps : updated.registers.valueDeps = call.registers.valueDeps)
      (value : updated.registers.value = call.registers.value) :
      CallRemovalRead after thread updated :=
    callRemovalRead_fields extension thread call updated ready operation deps value
  unfold queueStep at selected
  dsimp at selected
  all_goals repeat' (split at selected)
  all_goals try dsimp at selected
  all_goals try simp only [checked_call, emit_call, setCall, updateThread_call,
    updateArray_call, updateBuffer_call, threadControl_call, returnQueue,
    queueControl, ite_true] at selected
  all_goals try
    have sameCall : call = next := Option.some.inj (current.symm.trans selected)
    subst next
  all_goals try cases selected
  all_goals try exact preserve _ rfl rfl rfl
  all_goals dsimp [after]
  all_goals simp_all [CallRemovalRead, CallValueSources, RemovalRead, queueStep,
    checked, emit, Event.emit,
    setCall, queueControl, returnQueue, updateThread, updateArray, updateBuffer,
    Candidate.append]

private theorem queueStep_removalRegisters (c : Config) (s : State)
    (thread : Nat) (call : QueueCall) (choice : Choice)
    (current : (s.threads thread).call = some call)
    (registers : RemovalRegisters s) :
    RemovalRegisters (queueStep c s thread call choice) := by
  constructor
  · exact queueStep_valueSources c s thread call choice registers.1 current
  intro target next selected
  by_cases same : target = thread
  · subst target
    exact queueStep_selected_removalRead c s thread call choice next current
      ((registers.1 thread).2 call current) (registers.2 thread call current) selected
  · have oldSelected : (s.threads target).call = some next := by
      rw [← queueStep_other_call c s thread target call choice same]
      exact selected
    intro notPush deps
    exact removalRead_prefix (queueStep_executionPrefix c s thread call choice)
      target next (registers.2 target next oldSelected notPush deps)

private theorem countStep_removalRegisters (c : Config) (s : State)
    (thread : Nat) (choice : Choice) (registers : RemovalRegisters s) :
    RemovalRegisters (countStep c s thread choice) := by
  constructor
  · exact countStep_valueSources c s thread choice registers.1
  intro target call selected notPush deps
  have oldSelected : (s.threads target).call = some call := by
    simpa only [countStep_call] using selected
  exact removalRead_prefix (countStep_executionPrefix c s thread choice)
    target call (registers.2 target call oldSelected notPush deps)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem markStep_removalRegisters (c : Config) (s : State)
    (thread : Nat) (choice : Choice) (registers : RemovalRegisters s)
    (current : (s.threads thread).call = none) :
    RemovalRegisters (markStep c s thread choice) := by
  have values := markStep_valueSources c s thread choice registers.1
  constructor
  · exact values
  intro target call selected notPush deps
  rcases markStep_call c s thread target choice call selected with old | fresh
  · exact removalRead_prefix (markStep_executionPrefix c s thread choice)
      target call (registers.2 target call old notPush deps)
  · have ready := (values target).2 call selected
    exact False.elim (deps (ready.1 fresh))

theorem step_removalRegisters (c : Config) (s : State) (thread : Nat)
    (choice : Choice) (registers : RemovalRegisters s) :
    RemovalRegisters (step c thread choice s) := by
  unfold step
  split
  · exact registers
  · split
    · split
      · exact markStep_removalRegisters c s thread choice registers (by assumption)
      · rename_i call current
        split
        · exact registers
        · exact queueStep_removalRegisters c s thread call choice current registers
    · exact registers

theorem run_removalRegisters (c : Config) (schedule : List (Nat × Choice))
    (s : State) (registers : RemovalRegisters s) :
    RemovalRegisters (run c schedule s) := by
  induction schedule generalizing s with
  | nil => exact registers
  | cons scheduled rest ih =>
      exact ih _ (step_removalRegisters c s scheduled.1 scheduled.2 registers)

theorem sourceLog_removalRegisters (c : Config)
    (schedule : List (Nat × Choice)) (s : State)
    (registers : RemovalRegisters s) :
    ∀ frame ∈ sourceLog c schedule s, RemovalRegisters frame.state := by
  induction schedule generalizing s with
  | nil => simp [sourceLog]
  | cons scheduled rest ih =>
      intro frame member
      rcases List.mem_cons.mp member with first | later
      · subst frame
        exact registers
      · exact ih _ (step_removalRegisters c s scheduled.1 scheduled.2 registers)
          frame later

theorem canonical_removalRead (c : Config) (schedule : List (Nat × Choice))
    (frame : SourceFrame)
    (included : frame ∈ sourceLog c schedule (canonicalInitial c))
    (call : QueueCall)
    (selected : (frame.state.threads frame.thread).call = some call)
    (notPush : call.operation ≠ .push) (deps : call.registers.valueDeps ≠ []) :
    RemovalRead frame.state.execution frame.thread call := by
  have registers := sourceLog_removalRegisters c schedule (canonicalInitial c)
    (canonicalInitial_removalRegisters c) frame included
  exact registers.2 frame.thread call selected notPush deps

private theorem append_event_eq (before : Execution) (left right : Event Location Value)
    (equal : before.append left = before.append right) : left = right := by
  have lookup := congrArg (fun execution : Execution =>
    execution.events[before.events.size]?) equal
  simpa [Candidate.append] using lookup

private theorem self_ne_append (before : Execution) (event : Event Location Value) :
    before ≠ before.append event := by
  intro equal
  have size := congrArg (fun execution : Execution => execution.events.size) equal
  simp [Candidate.append] at size

def NonSlotEmission (before after : Execution) : Prop :=
  after = before ∨ ∃ event, isSlotAction event.action = false ∧ after = before.append event

private theorem countStep_nonSlotEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) :
    NonSlotEmission s.execution (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl, rfl⟩

private theorem markStep_nonSlotEmission (c : Config) (s : State) (tid : Nat)
    (choice : Choice) :
    NonSlotEmission s.execution (markStep c s tid choice).execution := by
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_nonSlotEmission c s tid choice
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl, rfl⟩
    | split)

private theorem slotEmission_not_nonSlotEmission {before after : Execution}
    (event : Event Location Value) (slot : isSlotAction event.action = true)
    (appended : after = before.append event) (nonSlot : NonSlotEmission before after) :
    False := by
  rcases nonSlot with same | ⟨other, ordinary, equal⟩
  · exact self_ne_append before event (same.symm.trans appended)
  · have events := append_event_eq before event other (appended.symm.trans equal)
    rw [events, ordinary] at slot
    cases slot

theorem sourceStepEmission_not_init (c : Config) (state : State) (thread : Nat)
    (choice : Choice) (event : Event Location Value)
    (appended : (step c thread choice state).execution = state.execution.append event) :
    event.action.isInit = false := by
  rcases step_nonInitEmission c state thread choice with same | ⟨emitted, nonInit, equal⟩
  · exact False.elim (self_ne_append state.execution event (same.trans appended))
  · have eventEq := append_event_eq state.execution emitted event (equal.symm.trans appended)
    simpa only [eventEq] using nonInit

/-- A slot occurrence emitted at one source step has the call selected at
that step, including its concrete source PC. -/
theorem step_slotEmission_source (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (event : Event Location Value)
    (slot : isSlotAction event.action = true)
    (appended : (step c tid choice s).execution = s.execution.append event) :
    QueueSource c ⟨s, tid, choice⟩ event := by
  change ∃ call, (s.threads tid).call = some call ∧
    queueAction call choice = some event.action ∧
    (step c tid choice s).execution = s.execution.append event
  cases fault : s.fault with
  | true =>
      exact False.elim (self_ne_append s.execution event (by
        simpa [step, fault] using appended))
  | false =>
    by_cases valid : tid < c.threads
    · cases selected : (s.threads tid).call with
      | none =>
        have markAppended : (markStep c s tid choice).execution =
            s.execution.append event := by simpa [step, fault, valid, selected] using appended
        exact False.elim (slotEmission_not_nonSlotEmission event slot markAppended
          (markStep_nonSlotEmission c s tid choice))
      | some call =>
        by_cases ownerFault : call.operation ≠ .steal ∧ call.owner ≠ tid
        · exact False.elim (self_ne_append s.execution event (by
            simpa [step, fault, valid, selected, ownerFault] using appended))
        · have queueAppended : (queueStep c s tid call choice).execution =
              s.execution.append event := by
            simpa [step, fault, valid, selected, ownerFault] using appended
          have census := queueStep_appendsAction c s tid call choice
          cases observed : queueAction call choice with
          | none =>
              have unchanged : (queueStep c s tid call choice).execution = s.execution := by
                simpa [AppendsAction, observed] using census
              exact False.elim (self_ne_append s.execution event
                (unchanged.symm.trans queueAppended))
          | some action =>
              obtain ⟨emitted, _, shape, result⟩ : ∃ emitted,
                  emitted.thread = tid ∧ emitted.action = action ∧
                  (queueStep c s tid call choice).execution = s.execution.append emitted := by
                simpa [AppendsAction, observed] using census
              have eventEq := append_event_eq s.execution emitted event
                (result.symm.trans queueAppended)
              subst emitted
              exact ⟨call, rfl, by simpa [shape] using observed, appended⟩
    · exact False.elim (self_ne_append s.execution event (by
        simpa [step, fault, valid] using appended))

/-- Every canonical slot occurrence has its actual source emission index.
The initialized queue headers contain no slot occurrences.
`bbfa0ce4150`, `src/gc-stock.c:3967-3979`. -/
theorem canonical_indexedSlot_source (c : Config) (schedule : List (Nat × Choice))
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    (slot : isSlotAction ((run c schedule (canonicalInitial c)).execution.event event).action =
      true) :
    ∃ frame ∈ sourceLog c schedule (canonicalInitial c),
      frame.state.execution.events.size = event.val ∧
      QueueSource c frame ((run c schedule (canonicalInitial c)).execution.event event) := by
  rcases run_indexedEmission c schedule (canonicalInitial c) event with initial | emitted
  · let first : (canonicalInitial c).execution.Id := ⟨event.val, initial⟩
    have equal := executionPrefix_event
      (run_executionPrefix c schedule (canonicalInitial c)) first
    have same : (run c schedule (canonicalInitial c)).execution.event event =
        (canonicalInitial c).execution.event first := by
      simpa only [first] using equal
    have unused := initialEvents_not_slot c ((canonicalInitial c).execution.event first)
      (by
        have bound : first.val < (initialEvents c).length := by
          simpa [canonicalInitial] using first.isLt
        change (initialEvents c)[first.val]'bound ∈ initialEvents c
        exact List.getElem_mem bound)
    rw [same, unused] at slot
    cases slot
  · obtain ⟨frame, included, position, appended⟩ := emitted
    exact ⟨frame, included, position, step_slotEmission_source c frame.state frame.thread
      frame.choice _ slot appended⟩

theorem canonicalEvent_not_init_of_initial_le (c : Config)
    (schedule : List (Nat × Choice))
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    (concurrent : (canonicalInitial c).execution.events.size ≤ event.val) :
    ((run c schedule (canonicalInitial c)).execution.event event).action.isInit = false := by
  rcases run_indexedEmission c schedule (canonicalInitial c) event with initial | emitted
  · omega
  · obtain ⟨frame, _, _, appended⟩ := emitted
    exact sourceStepEmission_not_init c frame.state frame.thread frame.choice _ appended

theorem canonical_indexedSlotWrite_source (c : Config) (schedule : List (Nat × Choice))
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    (slot : isSlotAction ((run c schedule (canonicalInitial c)).execution.event event).action =
      true)
    (writing : (run c schedule (canonicalInitial c)).execution.isWrite event = true) :
    ∃ frame ∈ sourceLog c schedule (canonicalInitial c),
      ∃ call, frame.state.execution.events.size = event.val ∧
        (frame.state.threads frame.thread).call = some call ∧
        (PushSlot call ((run c schedule (canonicalInitial c)).execution.event event).action ∨
          CopySlot call ((run c schedule (canonicalInitial c)).execution.event event).action) ∧
        (step c frame.thread frame.choice frame.state).execution =
          frame.state.execution.append
            ((run c schedule (canonicalInitial c)).execution.event event) := by
  obtain ⟨frame, included, position, call, selected, action, appended⟩ :=
    canonical_indexedSlot_source c schedule event slot
  exact ⟨frame, included, call, position, selected,
    queueAction_slot_write call frame.choice _ action slot writing, appended⟩

theorem eventIndex_lt {execution : Execution} {index : Nat}
    {event : Event Location Value} (lookup : execution.events[index]? = some event) :
    index < execution.events.size := by
  by_cases inside : index < execution.events.size
  · exact inside
  · rw [← Array.getElem?_toList,
      List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt inside))] at lookup
    cases lookup

private theorem queueStep_appended_thread (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (event : Event Location Value)
    (appended : (queueStep c s tid call choice).execution = s.execution.append event) :
    event.thread = tid := by
  have census := queueStep_appendsAction c s tid call choice
  cases action : queueAction call choice with
  | none =>
      have unchanged : (queueStep c s tid call choice).execution = s.execution := by
        simpa [AppendsAction, action] using census
      exact False.elim (self_ne_append s.execution event (unchanged.symm.trans appended))
  | some operation =>
      obtain ⟨emitted, emittedThread, _, result⟩ :
          ∃ emitted, emitted.thread = tid ∧ emitted.action = operation ∧
            (queueStep c s tid call choice).execution = s.execution.append emitted := by
        simpa [AppendsAction, action] using census
      have sameEvent := append_event_eq s.execution emitted event (result.symm.trans appended)
      rw [← sameEvent]
      exact emittedThread

theorem queueSource_thread (c : Config) (frame : SourceFrame)
    (event : Event Location Value) (source : QueueSource c frame event) :
    event.thread = frame.thread := by
  obtain ⟨call, selected, _, appended⟩ := source
  unfold step at appended
  split at appended
  · exact False.elim (self_ne_append frame.state.execution event appended)
  · split at appended
    · simp only [selected] at appended
      split at appended
      · exact False.elim (self_ne_append frame.state.execution event appended)
      · exact queueStep_appended_thread c frame.state frame.thread call frame.choice event appended
    · exact False.elim (self_ne_append frame.state.execution event appended)

private theorem sameLocation_slot {execution : Execution} {left right : execution.Id}
    (same : execution.sameLocation left right = true)
    (slot : isSlotAction (execution.event left).action = true) :
    isSlotAction (execution.event right).action = true := by
  simp only [Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same
  unfold isSlotAction at slot ⊢
  rw [← same.2]
  exact slot

/-- An input memcpy at the concrete source frame and event index.
`bbfa0ce4150`, `src/work-stealing-queue.h:67`. -/
def InputPublication (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (event : execution.Id) : Prop :=
  ∃ frame ∈ sourceLog c schedule (canonicalInitial c),
    ∃ call, frame.state.execution.events.size = event.val ∧
      (frame.state.threads frame.thread).call = some call ∧
      PushSlot call (execution.event event).action ∧
      (step c frame.thread frame.choice frame.state).execution =
        frame.state.execution.append (execution.event event)

/-- The write half of one source resize memcpy and its exact read half.
`bbfa0ce4150`, `src/work-stealing-queue.h:61`. -/
def ResizeCopy (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (write read : execution.Id) : Prop :=
  ∃ frame ∈ sourceLog c schedule (canonicalInitial c),
    ∃ call, frame.state.execution.events.size = write.val ∧
      (frame.state.threads frame.thread).call = some call ∧
      CopySlot call (execution.event write).action ∧
      call.registers.valueDeps = [read.val] ∧ read.val < write.val ∧
      (execution.event read).thread = frame.thread ∧
      (execution.event read).action = .plainLoad
        (.slot call.registers.buffer
          (maskedIndex (call.registers.t + Int64.ofInt call.registers.copyIndex.toInt)
            call.registers.mask).toInt.toNat)
        (.payload call.registers.value) ∧
      (step c frame.thread frame.choice frame.state).execution =
        frame.state.execution.append (execution.event write)

/-- Source input publications and the read-from/copy ancestry of slot
writes. Publication occurrence IDs are source event indices. -/
inductive SlotOrigin (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) : execution.Id → execution.Id → Prop where
  | input {event} : InputPublication c schedule execution event →
      SlotOrigin c schedule execution event event
  | copy {write read source origin} : ResizeCopy c schedule execution write read →
      execution.readSource read source = true →
      SlotOrigin c schedule execution source origin → SlotOrigin c schedule execution write origin

inductive IndexedSlotOrigin (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) : execution.Id → execution.Id →
      Nat → QueueKind → Int64 → Prop where
  | input {event frame call} :
      frame ∈ sourceLog c schedule (canonicalInitial c) →
      frame.state.execution.events.size = event.val →
      (frame.state.threads frame.thread).call = some call →
      PushSlot call (execution.event event).action →
      (step c frame.thread frame.choice frame.state).execution =
        frame.state.execution.append (execution.event event) →
      IndexedSlotOrigin c schedule execution event event
        call.owner call.kind call.registers.b
  | copy {write read source origin frame call owner kind index} :
      frame ∈ sourceLog c schedule (canonicalInitial c) →
      frame.state.execution.events.size = write.val →
      (frame.state.threads frame.thread).call = some call →
      CopySlot call (execution.event write).action →
      call.registers.valueDeps = [read.val] → read.val < write.val →
      (execution.event read).thread = frame.thread →
      (execution.event read).action = .plainLoad
        (.slot call.registers.buffer
          (maskedIndex (call.registers.t + Int64.ofInt call.registers.copyIndex.toInt)
            call.registers.mask).toInt.toNat)
        (.payload call.registers.value) →
      (step c frame.thread frame.choice frame.state).execution =
        frame.state.execution.append (execution.event write) →
      call.owner = owner → call.kind = kind →
      call.registers.t + Int64.ofInt call.registers.copyIndex.toInt = index →
      execution.readSource read source = true →
      IndexedSlotOrigin c schedule execution source origin owner kind index →
      IndexedSlotOrigin c schedule execution write origin owner kind index

theorem indexedSlotOrigin_origin {c : Config} {schedule : List (Nat × Choice)}
    {execution : Execution} {write origin : execution.Id} {owner : Nat}
    {kind : QueueKind} {index : Int64}
    (indexed : IndexedSlotOrigin c schedule execution write origin owner kind index) :
    SlotOrigin c schedule execution write origin := by
  induction indexed with
  | input included position selected push appended =>
      exact SlotOrigin.input ⟨_, included, _, position, selected, push, appended⟩
  | @copy write read source origin frame call owner kind index included position selected
      copy deps readBefore readThread readAction appended _ _ _ readFrom _ ih =>
      exact SlotOrigin.copy
        ⟨frame, included, call, position, selected, copy, deps, readBefore,
          readThread, readAction, appended⟩ readFrom ih

theorem slotOrigin_input {c : Config} {schedule : List (Nat × Choice)}
    {execution : Execution} {write origin : execution.Id}
    (ancestry : SlotOrigin c schedule execution write origin) :
    InputPublication c schedule execution origin := by
  induction ancestry with
  | input publication => exact publication
  | copy _ _ _ ih => exact ih

theorem indexedSlotOrigin_input {c : Config} {schedule : List (Nat × Choice)}
    {execution : Execution} {write origin : execution.Id} {owner : Nat}
    {kind : QueueKind} {index : Int64}
    (ancestry : IndexedSlotOrigin c schedule execution write origin owner kind index) :
    InputPublication c schedule execution origin :=
  slotOrigin_input (indexedSlotOrigin_origin ancestry)

/-- Every ordinary slot write in a defined canonical source execution
comes from an input publication, through zero or more actual resize copies.
`bbfa0ce4150`, `src/work-stealing-queue.h:61,67`. -/
def sourceSlotWritesHaveInputOrigins : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)),
    let execution := (run c schedule (canonicalInitial c)).execution
    execution.Defined → ∀ write : execution.Id,
      execution.isWrite write = true → isSlotAction (execution.event write).action = true →
      ∃ origin : execution.Id, InputPublication c schedule execution origin ∧
        SlotOrigin c schedule execution write origin ∧
        (execution.event write).action.writeValue = (execution.event origin).action.writeValue

theorem sourceSlotWritesHaveInputOrigins_proven : sourceSlotWritesHaveInputOrigins := by
  unfold sourceSlotWritesHaveInputOrigins
  intro c schedule
  dsimp
  intro defined write writing slot
  let execution := (run c schedule (canonicalInitial c)).execution
  generalize rankEq : predecessorRank execution write = rank
  induction rank using Nat.strongRecOn generalizing write with
  | ind rank ih =>
    obtain ⟨frame, included, call, position, selected, source, appended⟩ :=
      canonical_indexedSlotWrite_source c schedule write slot writing
    rcases source with push | copy
    · let input : InputPublication c schedule execution write :=
        ⟨frame, included, call, position, selected, push, appended⟩
      exact ⟨write, input, SlotOrigin.input input, rfl⟩
    · have copyOperation : call.operation = .push := copy.1
      have copyPC : call.pc = 616 := copy.2.1
      obtain ⟨index, observed, deps, lookup, readThread, readAction⟩ :=
        canonical_copyRead c schedule frame included call selected copyOperation copyPC
      have prior := eventIndex_lt lookup
      have extension := (sourceLog_executionPrefix c schedule (canonicalInitial c)
        frame included).1
      let read : execution.Id :=
        ⟨index, Nat.lt_of_lt_of_le prior (executionPrefix_size extension)⟩
      have finalLookup := executionPrefix_get extension index observed lookup
      rw [Array.getElem?_eq_getElem read.isLt] at finalLookup
      have observedEq : execution.event read = observed := Option.some.inj finalLookup
      have readShape : (execution.event read).action = .plainLoad
          (.slot call.registers.buffer
            (maskedIndex (call.registers.t + Int64.ofInt call.registers.copyIndex.toInt)
              call.registers.mask).toInt.toNat)
          (.payload call.registers.value) := by
        simpa only [observedEq] using readAction
      have readSameThread : (execution.event read).thread = frame.thread := by
        simpa only [observedEq] using readThread
      have readBefore : read.val < write.val := by
        change index < write.val
        omega
      have writeSameThread : (execution.event write).thread = frame.thread := by
        apply queueSource_thread c frame
        refine ⟨call, selected, ?_, appended⟩
        rw [copy.2.2]
        simp [queueAction, copyOperation, copyPC]
      have writeShape := copy.2.2
      have writeNonInit : (execution.event write).action.isInit = false := by
        rw [writeShape]
        rfl
      have readNonInit : (execution.event read).action.isInit = false := by
        rw [readShape]
        rfl
      have sequenced : execution.sequencedBefore read write = true := by
        simp [Candidate.sequencedBefore, readNonInit, writeNonInit,
          readSameThread, writeSameThread, readBefore]
      have reading : execution.isRead read = true := by
        simp [Candidate.isRead, readShape, Action.readValue]
      have ordinary : (execution.event read).action.isPlain = true := by
        simp [readShape, Action.isPlain]
      obtain ⟨source, readFrom, sourceWrites, same, value⟩ := defined.1.1.2.1 read reading
      have sourceSlot : isSlotAction (execution.event source).action = true :=
        sameLocation_slot same (by simp [isSlotAction, readShape, Action.location])
      have lower := copySource_rank_lt defined source read write ordinary reading readFrom sequenced
      have sourceRank : predecessorRank execution source < rank := by
        rw [← rankEq]
        simpa [execution] using lower
      obtain ⟨origin, input, ancestry, equal⟩ :=
        ih (predecessorRank execution source) sourceRank source sourceWrites sourceSlot rfl
      have link : ResizeCopy c schedule execution write read :=
        ⟨frame, included, call, position, selected, copy, deps, readBefore,
          readSameThread, readShape, appended⟩
      refine ⟨origin, input, SlotOrigin.copy link readFrom ancestry, ?_⟩
      have copiedValue : (execution.event write).action.writeValue =
          (execution.event read).action.readValue := by
        rw [writeShape, readShape]
        rfl
      exact copiedValue.trans (value.trans equal)

/-- Before cleanup, the owner is the only thread storing its queue's
bottom field. `bbfa0ce4150`, `src/work-stealing-queue.h:69,77,85,90`. -/
def BottomWriteShape (owner : Nat) (kind : QueueKind) (event : Event Location Value) : Prop :=
  event.action.location = some (.bottom owner kind) →
    event.action.writeValue.isSome = true →
    event.action = .init (.bottom owner kind) (.i64 0) ∨
      ∃ value : Int64,
        event.action = .store (.bottom owner kind) .relaxed (.i64 value) ∧
        event.thread = owner

private def BottomCensus (owner : Nat) (kind : QueueKind) (execution : Execution) : Prop :=
  ∀ event ∈ execution.events.toList, BottomWriteShape owner kind event

@[simp] private theorem bottomCensus_append (owner : Nat) (kind : QueueKind)
    (execution : Execution) (event : Event Location Value) :
    BottomCensus owner kind (execution.append event) ↔
      BottomCensus owner kind execution ∧ BottomWriteShape owner kind event := by
  constructor
  · intro appended
    constructor
    · intro prior member
      exact appended prior (by simp [Candidate.append, member])
    · exact appended event (by simp [Candidate.append])
  · rintro ⟨prior, latest⟩ current member
    have cases : current ∈ execution.events.toList ∨ current = event := by
      simpa [Candidate.append] using member
    rcases cases with old | rfl
    · exact prior current old
    · exact latest

private theorem initialQueueEvents_bottomShape (c : Config) (tid : Nat) (kind : QueueKind)
    (owner : Nat) (targetKind : QueueKind) (event : Event Location Value)
    (member : event ∈ initialQueueEvents c tid kind) :
    BottomWriteShape owner targetKind event := by
  simp [initialQueueEvents] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BottomWriteShape, Action.location, Action.writeValue]

private theorem canonicalInitial_bottomCensus (c : Config) (owner : Nat) (kind : QueueKind) :
    BottomCensus owner kind (canonicalInitial c).execution := by
  intro event member
  have initialized : event ∈ initialEvents c := by simpa [canonicalInitial] using member
  unfold initialEvents at initialized
  rcases List.mem_append.mp initialized with shared | perThread
  · simp at shared
    rcases shared with rfl | rfl <;>
      simp [BottomWriteShape, Action.location, Action.writeValue]
  · obtain ⟨tid, _, initialized⟩ := List.mem_flatMap.mp perThread
    split at initialized
    · rcases List.mem_append.mp initialized with queues | fields
      · rcases List.mem_append.mp queues with chunk | pointer
        · exact initialQueueEvents_bottomShape c tid .chunk owner kind event chunk
        · exact initialQueueEvents_bottomShape c tid .pointer owner kind event pointer
      · simp at fields
        rcases fields with rfl | rfl | rfl <;>
          simp [BottomWriteShape, Action.location, Action.writeValue]
    · simp at initialized

set_option maxHeartbeats 2000000 in
private theorem queueStep_bottomCensus (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (owner : Nat) (kind : QueueKind)
    (owned : call.operation ≠ .steal → call.owner = tid)
    (census : BottomCensus owner kind s.execution) :
    BottomCensus owner kind (queueStep c s tid call choice).execution := by
  unfold queueStep
  dsimp
  all_goals repeat' (split at * <;> try simp_all [checked, emit, Event.emit,
    setCall, updateThread, updateArray, updateBuffer, queueControl, returnQueue,
    queueLayout, BottomWriteShape, Action.location, Action.writeValue])

private theorem countStep_bottomCensus (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (owner : Nat) (kind : QueueKind)
    (census : BottomCensus owner kind s.execution) :
    BottomCensus owner kind (countStep c s tid choice).execution := by
  unfold countStep
  dsimp
  split <;> simp_all [checked, emit, Event.emit, updateThread,
    BottomWriteShape, Action.location, Action.writeValue]

set_option maxHeartbeats 20000000 in
private theorem markStep_bottomCensus (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (owner : Nat) (kind : QueueKind)
    (control : ∀ thread, threadInRound (s.threads thread))
    (before : s.barrierPassed = false)
    (_after : (markStep c s tid choice).barrierPassed = false)
    (census : BottomCensus owner kind s.execution) :
    BottomCensus owner kind (markStep c s tid choice).execution := by
  have selectedPC := (control tid).1
  unfold markStep
  dsimp
  split <;> (repeat' first
    | exact countStep_bottomCensus c s tid choice owner kind census
    | (simp_all [roundPC, checked, emit, Event.emit, advance,
        beginQueue, setCall, threadControl, updateThread, updateArray, updateBuffer,
        BottomWriteShape, Action.location, Action.writeValue] <;> done)
    | split)

private theorem step_bottomCensus (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (owner : Nat) (kind : QueueKind)
    (control : RoundControl s) (after : (step c tid choice s).barrierPassed = false)
    (census : BottomCensus owner kind s.execution) :
    BottomCensus owner kind (step c tid choice s).execution := by
  have before : s.barrierPassed = false := by
    cases initial : s.barrierPassed with
    | false => rfl
    | true =>
      have persistent := step_barrier c s tid choice initial
      simp [after] at persistent
  have initial := control before
  cases fault : s.fault with
  | true => simpa [step, fault] using census
  | false =>
    by_cases valid : tid < c.threads
    · cases call : (s.threads tid).call with
      | none =>
        have markAfter : (markStep c s tid choice).barrierPassed = false := by
          simpa [step, fault, valid, call] using after
        simpa [step, fault, valid, call] using
          markStep_bottomCensus c s tid choice owner kind initial before markAfter census
      | some q =>
        by_cases ownerFault : q.operation ≠ .steal ∧ q.owner ≠ tid
        · simpa [step, fault, valid, call, ownerFault] using census
        · have owned : q.operation ≠ .steal → q.owner = tid := by
            intro operation
            by_cases same : q.owner = tid
            · exact same
            · exact False.elim (ownerFault ⟨operation, same⟩)
          simpa [step, fault, valid, call, ownerFault] using
            queueStep_bottomCensus c s tid q choice owner kind owned census
    · simpa [step, fault, valid] using census

private theorem run_bottomCensus (c : Config) (schedule : List (Nat × Choice)) (s : State)
    (owner : Nat) (kind : QueueKind) (control : RoundControl s)
    (after : (run c schedule s).barrierPassed = false)
    (census : BottomCensus owner kind s.execution) :
    BottomCensus owner kind (run c schedule s).execution := by
  induction schedule generalizing s with
  | nil => exact census
  | cons scheduled rest ih =>
    have first : (step c scheduled.1 scheduled.2 s).barrierPassed = false := by
      cases initial : (step c scheduled.1 scheduled.2 s).barrierPassed with
      | false => rfl
      | true =>
        have persistent := run_barrier c rest (step c scheduled.1 scheduled.2 s) initial
        change (run c rest (step c scheduled.1 scheduled.2 s)).barrierPassed = false at after
        simp [after] at persistent
    exact ih _ (step_control c s scheduled.1 scheduled.2 control) after
      (step_bottomCensus c s scheduled.1 scheduled.2 owner kind control first census)

theorem sourceBottomWrite_shape (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (owner : Nat) (kind : QueueKind)
    (event : (run c schedule (canonicalInitial c)).execution.Id) :
    BottomWriteShape owner kind
      ((run c schedule (canonicalInitial c)).execution.event event) := by
  have census := run_bottomCensus c schedule (canonicalInitial c) owner kind
    (canonicalInitial_control c) before (canonicalInitial_bottomCensus c owner kind)
  apply census
  simp [Candidate.event, Array.getElem_mem]

/-- Owner bottom stores follow their source order in C11 modification
order. `bbfa0ce4150`, `src/work-stealing-queue.h:69,77,85,90`. -/
theorem sourceBottom_modificationOrder (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (owner : Nat) (kind : QueueKind)
    (left right : (run c schedule (canonicalInitial c)).execution.Id)
    (leftLocation : ((run c schedule (canonicalInitial c)).execution.event left).action.location =
      some (.bottom owner kind))
    (rightLocation : ((run c schedule (canonicalInitial c)).execution.event right).action.location =
      some (.bottom owner kind))
    (leftWrite : (run c schedule (canonicalInitial c)).execution.isWrite left = true)
    (rightWrite : (run c schedule (canonicalInitial c)).execution.isWrite right = true)
    (leftConcurrent : ((run c schedule (canonicalInitial c)).execution.event left).action.isInit =
      false)
    (rightConcurrent : ((run c schedule (canonicalInitial c)).execution.event right).action.isInit =
      false)
    (ordered : left.val < right.val) :
    ((run c schedule (canonicalInitial c)).execution.event left).mo <
      ((run c schedule (canonicalInitial c)).execution.event right).mo := by
  let execution := (run c schedule (canonicalInitial c)).execution
  have leftShape := sourceBottomWrite_shape c schedule before owner kind left leftLocation leftWrite
  have rightShape := sourceBottomWrite_shape c schedule before owner kind right rightLocation rightWrite
  rcases leftShape with initial | ⟨leftValue, leftAction, leftThread⟩
  · simp [initial, Action.isInit] at leftConcurrent
  rcases rightShape with initial | ⟨rightValue, rightAction, rightThread⟩
  · simp [initial, Action.isInit] at rightConcurrent
  have atomicLeft : execution.isAtomicWrite left = true := by
    simp [execution, Candidate.isAtomicWrite, leftWrite, leftAction, Action.isPlain]
  have atomicRight : execution.isAtomicWrite right = true := by
    simp [execution, Candidate.isAtomicWrite, rightWrite, rightAction, Action.isPlain]
  have same : execution.sameLocation left right = true := by
    simp [execution, Candidate.sameLocation, leftLocation, rightLocation]
  have sequenced : execution.sequencedBefore left right = true := by
    simp [execution, Candidate.sequencedBefore, leftConcurrent, rightConcurrent,
      leftThread, rightThread, ordered]
  have happens := Candidate.happensBefore_of_sequencedBefore sequenced
  have modification : execution.modificationBefore left right = true := by
    cases result : execution.modificationBefore left right with
    | true => rfl
    | false =>
      have excluded := defined.1.2.1.2.1 left atomicLeft right atomicRight same result
      rw [happens] at excluded
      contradiction
  simpa [execution, Candidate.modificationBefore, atomicLeft, atomicRight, same] using modification

private theorem readSource_values {execution : Execution} (wellFormed : execution.WellFormed)
    (read source : execution.Id) (reading : execution.isRead read = true)
    (readFrom : execution.readSource read source = true) :
    execution.isWrite source = true ∧ execution.sameLocation read source = true ∧
      (execution.event read).action.readValue = (execution.event source).action.writeValue := by
  obtain ⟨found, foundFrom, written, same, value⟩ := wellFormed.2.1 read reading
  have equal : found = source := by
    have first : (execution.event read).readFrom = some found.val := by
      simpa only [Candidate.readSource, beq_iff_eq] using foundFrom
    have second : (execution.event read).readFrom = some source.val := by
      simpa only [Candidate.readSource, beq_iff_eq] using readFrom
    exact Fin.ext (Option.some.inj (first.symm.trans second))
  subst found
  exact ⟨written, same, value⟩

/-- The owner's bottom load includes every earlier source bottom store in
its visible modification prefix. Its source is initialized zero or an
earlier owner store. `bbfa0ce4150`, `src/work-stealing-queue.h:54,75`. -/
theorem sourceOwnerBottom_lastWrite (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (owner : Nat) (kind : QueueKind)
    (read source : (run c schedule (canonicalInitial c)).execution.Id)
    (order : Order) (observed : Int64)
    (load : ((run c schedule (canonicalInitial c)).execution.event read).action =
      .load (.bottom owner kind) order (.i64 observed))
    (thread : ((run c schedule (canonicalInitial c)).execution.event read).thread = owner)
    (readFrom : (run c schedule (canonicalInitial c)).execution.readSource read source = true) :
    (((run c schedule (canonicalInitial c)).execution.event source).action.isInit = true ∨
      source.val < read.val) ∧
    ∀ write : (run c schedule (canonicalInitial c)).execution.Id,
      (run c schedule (canonicalInitial c)).execution.isWrite write = true →
      ((run c schedule (canonicalInitial c)).execution.event write).action.location =
        some (.bottom owner kind) → write.val < read.val →
      ((run c schedule (canonicalInitial c)).execution.event write).mo ≤
        ((run c schedule (canonicalInitial c)).execution.event source).mo := by
  let execution := (run c schedule (canonicalInitial c)).execution
  have reading : execution.isRead read = true := by
    simp [execution, Candidate.isRead, load, Action.readValue]
  have atomicRead : execution.isAtomicRead read = true := by
    simp [execution, Candidate.isAtomicRead, reading, load, Action.isPlain]
  have sourceData := readSource_values defined.1.1 read source reading readFrom
  have sourceLocation : (execution.event source).action.location = some (.bottom owner kind) := by
    have same := sourceData.2.1
    simp only [Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same
    simpa only [load, Action.location] using same.2.symm
  constructor
  · rcases sourceBottomWrite_shape c schedule before owner kind source sourceLocation sourceData.1
      with initial | ⟨value, store, sourceThread⟩
    · exact Or.inl (by simp [initial, Action.isInit])
    · right
      by_cases earlier : source.val < read.val
      · exact earlier
      · have different : source ≠ read := by
          intro equal
          subst source
          simp [execution, Candidate.isWrite, load, Action.writeValue] at sourceData
        have ordered : read.val < source.val := by
          have distinct : read.val ≠ source.val := by
            intro equal
            exact different (Fin.ext equal.symm)
          omega
        have sequenced : execution.sequencedBefore read source = true := by
          simp [execution, Candidate.sequencedBefore, load, store, Action.isInit,
            thread, sourceThread, ordered]
        have happens := Candidate.happensBefore_of_sequencedBefore sequenced
        have excluded := defined.1.2.1.2.2.2.2.2 read atomicRead source readFrom
        simp [execution, happens] at excluded
  · intro write writing location ordered
    rcases sourceBottomWrite_shape c schedule before owner kind write location writing
      with initial | ⟨value, store, writeThread⟩
    · have atomicWrite : execution.isAtomicWrite write = true := by
        simp [execution, Candidate.isAtomicWrite, writing, initial, Action.isPlain]
      have happens : execution.happensBefore write read = true := by
        apply Candidate.happensBefore_of_hbEdge
        simp [execution, Candidate.hbEdge, initial, load, Action.isInit]
      have same : execution.sameLocation write read = true := by
        simp [execution, Candidate.sameLocation, initial, load, Action.location]
      exact Candidate.write_read_coherent (decide_eq_true defined.1) write read source
        atomicWrite atomicRead same happens readFrom
    · have atomicWrite : execution.isAtomicWrite write = true := by
        simp [execution, Candidate.isAtomicWrite, writing, store, Action.isPlain]
      have sequenced : execution.sequencedBefore write read = true := by
        simp [execution, Candidate.sequencedBefore, store, load, Action.isInit,
          writeThread, thread, ordered]
      have same : execution.sameLocation write read = true := by
        simp [execution, Candidate.sameLocation, store, load, Action.location]
      exact Candidate.write_read_coherent (decide_eq_true defined.1) write read source
        atomicWrite atomicRead same
        (Candidate.happensBefore_of_sequencedBefore sequenced) readFrom

def ValidPushCalls (state : State) : Prop :=
  ∀ tid call, (state.threads tid).call = some call → call.operation = .push →
    Payload.ValidWork call.kind call.registers.pushed

theorem canonicalInitial_validPushCalls (c : Config) :
    ValidPushCalls (canonicalInitial c) := by
  intro tid call selected _
  unfold canonicalInitial at selected
  dsimp at selected
  all_goals repeat' (split at selected <;> try simp_all)

private theorem queueStep_validPushCalls (c : Config) (s : State) (tid : Nat)
    (call : QueueCall) (choice : Choice) (valid : ValidPushCalls s)
    (current : (s.threads tid).call = some call) :
    ValidPushCalls (queueStep c s tid call choice) := by
  intro thread next selected operation
  have old := valid thread
  have ready := valid tid call current
  unfold queueStep at selected
  dsimp at selected
  all_goals repeat' (split at * <;> try simp_all [checked, emit, setCall,
    queueControl, returnQueue, updateThread, updateArray, updateBuffer])
  all_goals try cases selected <;> simp_all

private theorem countStep_validPushCalls (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (valid : ValidPushCalls s) :
    ValidPushCalls (countStep c s tid choice) := by
  intro thread call selected operation
  exact valid thread call (by simpa only [countStep_call] using selected) operation

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem markStep_validPushCalls (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (valid : ValidPushCalls s)
    (scanner : Choice.ValidScannerOutput (s.threads tid) choice)
    (current : (s.threads tid).call = none) :
    ValidPushCalls (markStep c s tid choice) := by
  intro thread call selected operation
  have old := valid thread
  unfold markStep at selected
  dsimp at selected
  all_goals repeat' (split at * <;> try simp_all [Choice.ValidScannerOutput,
    scannerPC, checked, emit, advance, beginQueue, setCall, threadControl,
    updateThread, updateArray, updateBuffer, countStep_validPushCalls])
  all_goals try exact countStep_validPushCalls c s tid choice valid thread call selected operation
  all_goals try cases selected <;> simp_all

theorem step_validPushCalls (c : Config) (s : State) (tid : Nat)
    (choice : Choice) (valid : ValidPushCalls s)
    (scanner : Choice.ValidScannerOutput (s.threads tid) choice) :
    ValidPushCalls (step c tid choice s) := by
  unfold step
  split
  · exact valid
  · split
    · split
      · exact markStep_validPushCalls c s tid choice valid scanner (by assumption)
      · rename_i call current
        split
        · exact valid
        · exact queueStep_validPushCalls c s tid call choice valid current
    · exact valid

theorem run_validPushCalls (c : Config) (schedule : List (Nat × Choice))
    (s : State) (valid : ValidPushCalls s)
    (scanner : ScannerOutputsValid c schedule s) :
    ValidPushCalls (run c schedule s) := by
  induction schedule generalizing s with
  | nil => exact valid
  | cons scheduled rest ih =>
      exact ih _ (step_validPushCalls c s scheduled.1 scheduled.2 valid scanner.1)
        scanner.2

theorem sourceLog_validPushCalls (c : Config) (schedule : List (Nat × Choice))
    (s : State) (valid : ValidPushCalls s)
    (scanner : ScannerOutputsValid c schedule s) :
    ∀ frame ∈ sourceLog c schedule s, ValidPushCalls frame.state := by
  induction schedule generalizing s with
  | nil => simp [sourceLog]
  | cons scheduled rest ih =>
      intro frame member
      rcases List.mem_cons.mp member with first | later
      · subst frame
        exact valid
      · exact ih _ (step_validPushCalls c s scheduled.1 scheduled.2 valid scanner.1)
          scanner.2 frame later

private theorem validWork_nonempty (kind : QueueKind) (value : Payload)
    (valid : Payload.ValidWork kind value) :
    value ≠ .zero ∧ value.emptyChunk = false := by
  cases kind <;> cases value <;> simp_all [Payload.ValidWork, Payload.emptyChunk]

theorem sourceSlotWrite_validWork (c : Config) (schedule : List (Nat × Choice))
    (scanner : ScannerOutputsValid c schedule (canonicalInitial c))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (write : (run c schedule (canonicalInitial c)).execution.Id)
    (writing : (run c schedule (canonicalInitial c)).execution.isWrite write = true)
    (slot : isSlotAction
      ((run c schedule (canonicalInitial c)).execution.event write).action = true)
    (value : Payload)
    (stored : ((run c schedule (canonicalInitial c)).execution.event write).action.writeValue =
      some (.payload value)) :
    ∃ kind, Payload.ValidWork kind value := by
  obtain ⟨origin, input, _, same⟩ :=
    sourceSlotWritesHaveInputOrigins_proven c schedule defined write writing slot
  obtain ⟨frame, included, call, _, selected, push, _⟩ := input
  have valid := sourceLog_validPushCalls c schedule (canonicalInitial c)
    (canonicalInitial_validPushCalls c) scanner frame included
  have payload := valid frame.thread call selected push.1
  have originStored :
      ((run c schedule (canonicalInitial c)).execution.event origin).action.writeValue =
        some (.payload call.registers.pushed) := by
    simp [push.2.2, Action.writeValue]
  have equal : value = call.registers.pushed := by
    have values := Option.some.inj (stored.symm.trans (same.trans originStored))
    exact Value.payload.inj values
  exact ⟨call.kind, by simpa only [equal] using payload⟩

theorem sourceSlotRead_validWork (c : Config) (schedule : List (Nat × Choice))
    (scanner : ScannerOutputsValid c schedule (canonicalInitial c))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (read : (run c schedule (canonicalInitial c)).execution.Id)
    (buffer index : Nat) (value : Payload)
    (load : ((run c schedule (canonicalInitial c)).execution.event read).action =
      .plainLoad (.slot buffer index) (.payload value)) :
    ∃ kind, Payload.ValidWork kind value := by
  let execution := (run c schedule (canonicalInitial c)).execution
  have reading : execution.isRead read = true := by
    dsimp [execution]
    simp [Candidate.isRead, load, Action.readValue]
  obtain ⟨source, readFrom, writing, same, observed⟩ :=
    defined.1.1.2.1 read reading
  apply sourceSlotWrite_validWork c schedule scanner defined source writing
    (sameLocation_slot same (by simp [isSlotAction, load, Action.location])) value
  simpa only [load, Action.readValue] using observed.symm

def CompletedRemoval (call : QueueCall) : Prop :=
  ((call.operation = .pop ∧ call.pc = 92) ∨
    (call.operation = .steal ∧ call.pc = 105)) ∧ call.registers.value ≠ .zero

def RemovalOrigin (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (frame : SourceFrame) (call : QueueCall)
    (origin : execution.Id) : Prop :=
  frame ∈ sourceLog c schedule (canonicalInitial c) ∧
    (frame.state.threads frame.thread).call = some call ∧
    CompletedRemoval call ∧ InputPublication c schedule execution origin ∧
    (execution.event origin).action.writeValue = some (.payload call.registers.value)

@[simp] theorem sourceLog_length (c : Config) (schedule : List (Nat × Choice))
    (state : State) : (sourceLog c schedule state).length = schedule.length := by
  induction schedule generalizing state with
  | nil => rfl
  | cons scheduled rest ih => simp [sourceLog, ih]

def sourceFrameAt (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) : SourceFrame :=
  (sourceLog c schedule (canonicalInitial c))[stepIndex.val]'(by
    simpa only [sourceLog_length] using stepIndex.isLt)

@[simp] theorem sourceFrameAt_split (c : Config) (left right : List (Nat × Choice))
    (thread : Nat) (choice : Choice) :
    sourceFrameAt c (left ++ (thread, choice) :: right)
      ⟨left.length, by simp⟩ =
      { state := run c left (canonicalInitial c), thread, choice } := by
  unfold sourceFrameAt
  simp [sourceLog_append, sourceLog_length, sourceLog]

private theorem sourceLog_get_eq_take (c : Config) :
    ∀ (schedule : List (Nat × Choice)) (state : State)
      (stepIndex : Fin schedule.length),
      (sourceLog c schedule state)[stepIndex.val] =
        { state := run c (schedule.take stepIndex.val) state,
          thread := schedule[stepIndex.val].1,
          choice := schedule[stepIndex.val].2 } := by
  intro schedule
  induction schedule with
  | nil => intro state stepIndex; exact Fin.elim0 stepIndex
  | cons scheduled rest ih =>
      intro state stepIndex
      obtain ⟨index, bound⟩ := stepIndex
      cases index with
      | zero => rfl
      | succ index =>
          let tailIndex : Fin rest.length := ⟨index, by simpa using bound⟩
          simpa [sourceLog, run, List.take_succ_cons, tailIndex] using
            ih (step c scheduled.1 scheduled.2 state) tailIndex

theorem sourceFrameAt_eq_take (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) :
    sourceFrameAt c schedule stepIndex =
      { state := run c (schedule.take stepIndex.val) (canonicalInitial c),
        thread := schedule[stepIndex.val].1,
        choice := schedule[stepIndex.val].2 } := by
  unfold sourceFrameAt
  exact sourceLog_get_eq_take c schedule (canonicalInitial c) stepIndex

theorem sourceFrameAt_executionSize_mono (c : Config)
    (schedule : List (Nat × Choice)) (left right : Fin schedule.length)
    (ordered : left.val ≤ right.val) :
    (sourceFrameAt c schedule left).state.execution.events.size ≤
      (sourceFrameAt c schedule right).state.execution.events.size := by
  have takeEq : schedule.take right.val = schedule.take left.val ++
      (schedule.drop left.val).take (right.val - left.val) := by
    have split := (List.take_add : schedule.take (left.val + (right.val - left.val)) =
      schedule.take left.val ++ (schedule.drop left.val).take (right.val - left.val))
    simpa [Nat.add_sub_of_le ordered] using split
  rw [sourceFrameAt_eq_take, sourceFrameAt_eq_take, takeEq, run_append]
  exact executionPrefix_size
    (run_executionPrefix c ((schedule.drop left.val).take (right.val - left.val))
      (run c (schedule.take left.val) (canonicalInitial c)))

theorem sourceFrameAt_step (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) :
    step c (sourceFrameAt c schedule stepIndex).thread
      (sourceFrameAt c schedule stepIndex).choice
      (sourceFrameAt c schedule stepIndex).state =
        run c (schedule.take (stepIndex.val + 1)) (canonicalInitial c) := by
  rw [sourceFrameAt_eq_take]
  rw [List.take_succ, List.getElem?_eq_getElem stepIndex.isLt,
    Option.toList_some, run_append]
  rfl

def SourceEmissionAt (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length)
    (event : (run c schedule (canonicalInitial c)).execution.Id) : Prop :=
  let frame := sourceFrameAt c schedule stepIndex
  frame.state.execution.events.size = event.val ∧
    (step c frame.thread frame.choice frame.state).execution =
      frame.state.execution.append
        ((run c schedule (canonicalInitial c)).execution.event event)

theorem sourceEmissionAt_step_unique (c : Config)
    (schedule : List (Nat × Choice))
    (left right : Fin schedule.length)
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    (leftEmits : SourceEmissionAt c schedule left event)
    (rightEmits : SourceEmissionAt c schedule right event) : left = right := by
  apply Fin.ext
  rcases Nat.lt_trichotomy left.val right.val with before | equal | after
  · let next : Fin schedule.length :=
      ⟨left.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt before) right.isLt⟩
    have afterEq := congrArg (fun state : State => state.execution.events.size)
      (sourceFrameAt_step c schedule left)
    have appendSize := congrArg (fun execution : Execution => execution.events.size)
      leftEmits.2
    have nextSize :
        (sourceFrameAt c schedule next).state.execution.events.size = event.val + 1 := by
      rw [sourceFrameAt_eq_take]
      rw [← afterEq]
      simpa [Candidate.append, leftEmits.1] using appendSize
    have mono := sourceFrameAt_executionSize_mono c schedule next right (by
      simpa [next] using Nat.succ_le_of_lt before)
    rw [nextSize, rightEmits.1] at mono
    omega
  · exact equal
  · let next : Fin schedule.length :=
      ⟨right.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt after) left.isLt⟩
    have afterEq := congrArg (fun state : State => state.execution.events.size)
      (sourceFrameAt_step c schedule right)
    have appendSize := congrArg (fun execution : Execution => execution.events.size)
      rightEmits.2
    have nextSize :
        (sourceFrameAt c schedule next).state.execution.events.size = event.val + 1 := by
      rw [sourceFrameAt_eq_take]
      rw [← afterEq]
      simpa [Candidate.append, rightEmits.1] using appendSize
    have mono := sourceFrameAt_executionSize_mono c schedule next left (by
      simpa [next] using Nat.succ_le_of_lt after)
    rw [nextSize, leftEmits.1] at mono
    omega

private theorem sourceFrame_member_index_from_mem (c : Config)
    (schedule : List (Nat × Choice)) (frame : SourceFrame)
    (included : frame ∈ sourceLog c schedule (canonicalInitial c)) :
    ∃ stepIndex : Fin schedule.length, frame = sourceFrameAt c schedule stepIndex := by
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp included
  let stepIndex : Fin schedule.length :=
    ⟨index, by simpa only [sourceLog_length] using bound⟩
  exact ⟨stepIndex, by
    unfold sourceFrameAt
    simpa [stepIndex] using equal.symm⟩

def InputDescriptor (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (origin : execution.Id)
    (owner : Nat) (kind : QueueKind) (index : Int64) : Prop :=
  ∃ frame ∈ sourceLog c schedule (canonicalInitial c), ∃ call,
    frame.state.execution.events.size = origin.val ∧
    (frame.state.threads frame.thread).call = some call ∧
    PushSlot call (execution.event origin).action ∧
    (step c frame.thread frame.choice frame.state).execution =
      frame.state.execution.append (execution.event origin) ∧
    call.owner = owner ∧ call.kind = kind ∧ call.registers.b = index

theorem indexedSlotOrigin_descriptor {c : Config}
    {schedule : List (Nat × Choice)} {execution : Execution}
    {write origin : execution.Id} {owner : Nat} {kind : QueueKind} {index : Int64}
    (ancestry : IndexedSlotOrigin c schedule execution write origin owner kind index) :
    InputDescriptor c schedule execution origin owner kind index := by
  induction ancestry with
  | input included position selected push appended =>
      exact ⟨_, included, _, position, selected, push, appended, rfl, rfl, rfl⟩
  | copy _ _ _ _ _ _ _ _ _ _ _ _ _ prior ih => exact ih

theorem inputDescriptor_functional (c : Config) (schedule : List (Nat × Choice))
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    {leftOwner rightOwner : Nat} {leftKind rightKind : QueueKind}
    {leftIndex rightIndex : Int64}
    (left : InputDescriptor c schedule (run c schedule (canonicalInitial c)).execution
      origin leftOwner leftKind leftIndex)
    (right : InputDescriptor c schedule (run c schedule (canonicalInitial c)).execution
      origin rightOwner rightKind rightIndex) :
    leftOwner = rightOwner ∧ leftKind = rightKind ∧ leftIndex = rightIndex := by
  obtain ⟨leftFrame, leftMember, leftCall, leftPosition, leftSelected,
    leftPush, leftAppended, leftOwnerEq, leftKindEq, leftIndexEq⟩ := left
  obtain ⟨rightFrame, rightMember, rightCall, rightPosition, rightSelected,
    rightPush, rightAppended, rightOwnerEq, rightKindEq, rightIndexEq⟩ := right
  obtain ⟨leftStep, leftFrameEq⟩ :=
    sourceFrame_member_index_from_mem c schedule leftFrame leftMember
  obtain ⟨rightStep, rightFrameEq⟩ :=
    sourceFrame_member_index_from_mem c schedule rightFrame rightMember
  subst leftFrame
  subst rightFrame
  have leftEmits : SourceEmissionAt c schedule leftStep origin := by
    exact ⟨leftPosition, leftAppended⟩
  have rightEmits : SourceEmissionAt c schedule rightStep origin := by
    exact ⟨rightPosition, rightAppended⟩
  have stepEq := sourceEmissionAt_step_unique c schedule leftStep rightStep origin
    leftEmits rightEmits
  subst rightStep
  have callEq : leftCall = rightCall := Option.some.inj (leftSelected.symm.trans rightSelected)
  subst rightCall
  exact ⟨leftOwnerEq.symm.trans rightOwnerEq,
    leftKindEq.symm.trans rightKindEq, leftIndexEq.symm.trans rightIndexEq⟩

theorem indexedSlotOrigin_metadata_functional (c : Config)
    (schedule : List (Nat × Choice))
    (leftWrite rightWrite origin :
      (run c schedule (canonicalInitial c)).execution.Id)
    {leftOwner rightOwner : Nat} {leftKind rightKind : QueueKind}
    {leftIndex rightIndex : Int64}
    (left : IndexedSlotOrigin c schedule
      (run c schedule (canonicalInitial c)).execution leftWrite origin
        leftOwner leftKind leftIndex)
    (right : IndexedSlotOrigin c schedule
      (run c schedule (canonicalInitial c)).execution rightWrite origin
        rightOwner rightKind rightIndex) :
    leftOwner = rightOwner ∧ leftKind = rightKind ∧ leftIndex = rightIndex :=
  inputDescriptor_functional c schedule origin
    (indexedSlotOrigin_descriptor left) (indexedSlotOrigin_descriptor right)

private theorem sourceEmission_call_functional (c : Config)
    (schedule : List (Nat × Choice))
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    {leftFrame rightFrame : SourceFrame} {leftCall rightCall : QueueCall}
    (leftMember : leftFrame ∈ sourceLog c schedule (canonicalInitial c))
    (leftPosition : leftFrame.state.execution.events.size = event.val)
    (leftSelected : (leftFrame.state.threads leftFrame.thread).call = some leftCall)
    (leftAppended : (step c leftFrame.thread leftFrame.choice leftFrame.state).execution =
      leftFrame.state.execution.append
        ((run c schedule (canonicalInitial c)).execution.event event))
    (rightMember : rightFrame ∈ sourceLog c schedule (canonicalInitial c))
    (rightPosition : rightFrame.state.execution.events.size = event.val)
    (rightSelected : (rightFrame.state.threads rightFrame.thread).call = some rightCall)
    (rightAppended : (step c rightFrame.thread rightFrame.choice rightFrame.state).execution =
      rightFrame.state.execution.append
        ((run c schedule (canonicalInitial c)).execution.event event)) :
    leftFrame = rightFrame ∧ leftCall = rightCall := by
  obtain ⟨leftStep, leftFrameEq⟩ :=
    sourceFrame_member_index_from_mem c schedule leftFrame leftMember
  obtain ⟨rightStep, rightFrameEq⟩ :=
    sourceFrame_member_index_from_mem c schedule rightFrame rightMember
  subst leftFrame
  subst rightFrame
  have stepEq := sourceEmissionAt_step_unique c schedule leftStep rightStep event
    ⟨leftPosition, leftAppended⟩ ⟨rightPosition, rightAppended⟩
  subst rightStep
  exact ⟨rfl, Option.some.inj (leftSelected.symm.trans rightSelected)⟩

private theorem readSource_functional {execution : Execution}
    {read left right : execution.Id}
    (leftSource : execution.readSource read left = true)
    (rightSource : execution.readSource read right = true) : left = right := by
  apply Fin.ext
  simp only [Candidate.readSource, beq_iff_eq] at leftSource rightSource
  exact Option.some.inj (leftSource.symm.trans rightSource)

theorem indexedSlotOrigin_origin_functional (c : Config)
    (schedule : List (Nat × Choice))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    {write leftOrigin rightOrigin :
      (run c schedule (canonicalInitial c)).execution.Id}
    {leftOwner rightOwner : Nat} {leftKind rightKind : QueueKind}
    {leftIndex rightIndex : Int64}
    (left : IndexedSlotOrigin c schedule
      (run c schedule (canonicalInitial c)).execution write leftOrigin
        leftOwner leftKind leftIndex)
    (right : IndexedSlotOrigin c schedule
      (run c schedule (canonicalInitial c)).execution write rightOrigin
        rightOwner rightKind rightIndex) :
    leftOrigin = rightOrigin := by
  induction left generalizing rightOwner rightKind rightIndex with
  | @input event leftFrame leftCall leftMember leftPosition leftSelected
      leftPush leftAppended =>
      cases right with
      | input rightMember rightPosition rightSelected rightPush rightAppended => rfl
      | @copy rightWrite rightRead rightSource rightOrigin rightFrame rightCall _ _ _
          rightMember rightPosition rightSelected rightCopy rightDeps rightBefore
          rightThread rightAction rightAppended rightOwnerEq rightKindEq rightIndexEq
          rightReadFrom rightPrior =>
          obtain ⟨frameEq, callEq⟩ := sourceEmission_call_functional c schedule event
            leftMember leftPosition leftSelected leftAppended
            rightMember rightPosition rightSelected rightAppended
          subst rightFrame
          subst rightCall
          exact False.elim (by
            have leftPC : leftCall.pc = 672 := leftPush.2.1
            have rightPC : leftCall.pc = 616 := rightCopy.2.1
            omega)
  | @copy write leftRead leftSource leftOrigin leftFrame leftCall leftOwner leftKind
      leftIndex leftMember leftPosition leftSelected leftCopy leftDeps leftBefore
      leftThread leftAction leftAppended leftOwnerEq leftKindEq leftIndexEq
      leftReadFrom leftPrior ih =>
      cases right with
      | @input rightEvent rightFrame rightCall rightMember rightPosition rightSelected
          rightPush rightAppended =>
          obtain ⟨frameEq, callEq⟩ := sourceEmission_call_functional c schedule rightOrigin
            leftMember leftPosition leftSelected leftAppended
            rightMember rightPosition rightSelected rightAppended
          subst rightFrame
          subst rightCall
          exact False.elim (by
            have leftPC : leftCall.pc = 616 := leftCopy.2.1
            have rightPC : leftCall.pc = 672 := rightPush.2.1
            omega)
      | @copy rightWrite rightRead rightSource rightOrigin rightFrame rightCall _ _ _
          rightMember rightPosition rightSelected rightCopy rightDeps rightBefore
          rightThread rightAction rightAppended rightOwnerEq rightKindEq rightIndexEq
          rightReadFrom rightPrior =>
          obtain ⟨frameEq, callEq⟩ := sourceEmission_call_functional c schedule write
            leftMember leftPosition leftSelected leftAppended
            rightMember rightPosition rightSelected rightAppended
          subst rightFrame
          subst rightCall
          have readEq : leftRead = rightRead := by
            apply Fin.ext
            have equalDeps := leftDeps.symm.trans rightDeps
            exact (List.cons.inj equalDeps).1
          subst rightRead
          have sourceEq := readSource_functional leftReadFrom rightReadFrom
          subst rightSource
          exact ih rightPrior

theorem sourceLog_member_split (c : Config) (schedule : List (Nat × Choice))
    (state : State) (frame : SourceFrame)
    (included : frame ∈ sourceLog c schedule state) :
    ∃ left thread choice right,
      schedule = left ++ (thread, choice) :: right ∧
      frame = { state := run c left state, thread, choice } := by
  induction schedule generalizing state with
  | nil => simp [sourceLog] at included
  | cons scheduled rest ih =>
    simp only [sourceLog, List.mem_cons] at included
    rcases included with first | later
    · subst frame
      exact ⟨[], scheduled.1, scheduled.2, rest, rfl, rfl⟩
    · obtain ⟨left, thread, choice, right, scheduleEq, frameEq⟩ :=
        ih (step c scheduled.1 scheduled.2 state) later
      refine ⟨scheduled :: left, thread, choice, right, ?_, ?_⟩
      · simp [scheduleEq]
      · simpa [run] using frameEq

theorem sourceFrame_member_index (c : Config) (schedule : List (Nat × Choice))
    (frame : SourceFrame)
    (included : frame ∈ sourceLog c schedule (canonicalInitial c)) :
    ∃ stepIndex : Fin schedule.length, frame = sourceFrameAt c schedule stepIndex := by
  obtain ⟨left, thread, choice, right, scheduleEq, frameEq⟩ :=
    sourceLog_member_split c schedule (canonicalInitial c) frame included
  subst frame
  subst schedule
  exact ⟨⟨left.length, by simp⟩, by simp⟩

theorem sourceFrame_initialSize_le (c : Config) (schedule : List (Nat × Choice))
    (frame : SourceFrame) (included : frame ∈ sourceLog c schedule (canonicalInitial c)) :
    (canonicalInitial c).execution.events.size ≤ frame.state.execution.events.size := by
  obtain ⟨left, thread, choice, right, _, frameEq⟩ :=
    sourceLog_member_split c schedule (canonicalInitial c) frame included
  subst frame
  exact executionPrefix_size (run_executionPrefix c left (canonicalInitial c))

theorem canonicalNonInit_initialSize_le (c : Config) (schedule : List (Nat × Choice))
    (event : (run c schedule (canonicalInitial c)).execution.Id)
    (nonInit : ((run c schedule (canonicalInitial c)).execution.event event).action.isInit =
      false) :
    (canonicalInitial c).execution.events.size ≤ event.val := by
  rcases run_indexedEmission c schedule (canonicalInitial c) event with initial | emitted
  · let source : (canonicalInitial c).execution.Id := ⟨event.val, initial⟩
    have eventEq := executionPrefix_event
      (run_executionPrefix c schedule (canonicalInitial c)) source
    have sourceInit : ((canonicalInitial c).execution.event source).action.isInit = true := by
      apply initialEvents_init c
      change (initialEvents c)[source.val]'(by
        simpa [canonicalInitial] using source.isLt) ∈ initialEvents c
      exact List.getElem_mem _
    have finalInit :
        ((run c schedule (canonicalInitial c)).execution.event event).action.isInit = true := by
      let lifted : (run c schedule (canonicalInitial c)).execution.Id :=
        ⟨source.val, Nat.lt_of_lt_of_le source.isLt
          (executionPrefix_size (run_executionPrefix c schedule (canonicalInitial c)))⟩
      have same : event = lifted := Fin.ext rfl
      rw [same]
      rw [show (run c schedule (canonicalInitial c)).execution.event lifted =
          (canonicalInitial c).execution.event source by simpa [lifted] using eventEq]
      exact sourceInit
    rw [finalInit] at nonInit
    cases nonInit
  · obtain ⟨frame, included, position, _⟩ := emitted
    rw [← position]
    exact sourceFrame_initialSize_le c schedule frame included

def RemovalAt (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (stepIndex : Fin schedule.length)
    (origin : execution.Id) : Prop :=
  ∃ call, ((sourceFrameAt c schedule stepIndex).state.threads
      (sourceFrameAt c schedule stepIndex).thread).call = some call ∧
    RemovalOrigin c schedule execution (sourceFrameAt c schedule stepIndex) call origin

theorem slotObservation_prefix {before after : Execution} (extension : ExecutionPrefix before after)
    (tid : Nat) (value : Payload) (observed : SlotObservation before tid value) :
    SlotObservation after tid value := by
  obtain ⟨event, member, thread, buffer, index, action⟩ := observed
  obtain ⟨suffix, equal⟩ := extension
  exact ⟨event, by rw [equal]; exact List.mem_append_left suffix member,
    thread, buffer, index, action⟩

private def sourceReturnedWorkHasInputOrigin : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)), c.SourceInitial →
    ScannerOutputsValid c schedule (canonicalInitial c) →
    let execution := (run c schedule (canonicalInitial c)).execution
    execution.Defined →
    ∀ frame ∈ sourceLog c schedule (canonicalInitial c),
      ∀ call, (frame.state.threads frame.thread).call = some call →
        CompletedRemoval call →
        ∃ origin : execution.Id,
          InputPublication c schedule execution origin ∧
          (execution.event origin).action.writeValue =
            some (.payload call.registers.value)

private theorem sourceReturnedWorkHasInputOrigin_proven : sourceReturnedWorkHasInputOrigin := by
  unfold sourceReturnedWorkHasInputOrigin
  intro c schedule _ scanner
  dsimp
  intro defined frame included call selected completed
  have values := sourceLog_valueSources c schedule (canonicalInitial c)
    (canonicalInitial_valueSources c) frame included
  have ready := (values frame.thread).2 call selected
  have notPush : call.operation ≠ .push := by
    rcases completed.1 with ⟨operation, _⟩ | ⟨operation, _⟩ <;> simp [operation]
  have deps : call.registers.valueDeps ≠ [] := ready.2.2.2 notPush completed.2
  have observed := ready.2.1 deps
  have extension := (sourceLog_executionPrefix c schedule (canonicalInitial c) frame included).1
  have finalObserved := slotObservation_prefix extension frame.thread call.registers.value observed
  obtain ⟨event, member, _, buffer, index, action⟩ := finalObserved
  obtain ⟨position, bound, equal⟩ := List.mem_iff_getElem.mp member
  let read : (run c schedule (canonicalInitial c)).execution.Id :=
    ⟨position, by simpa only [Array.length_toList] using bound⟩
  have eventEq : (run c schedule (canonicalInitial c)).execution.event read = event := by
    simpa [Candidate.event, read] using equal
  have load : ((run c schedule (canonicalInitial c)).execution.event read).action =
      .plainLoad (.slot buffer index) (.payload call.registers.value) := by
    simpa only [eventEq] using action
  have reading : (run c schedule (canonicalInitial c)).execution.isRead read = true := by
    simp [Candidate.isRead, load, Action.readValue]
  obtain ⟨source, _, writing, same, observedValue⟩ := defined.1.1.2.1 read reading
  have sourceSlot :
      isSlotAction ((run c schedule (canonicalInitial c)).execution.event source).action = true :=
    sameLocation_slot same (by simp [isSlotAction, load, Action.location])
  obtain ⟨origin, input, _, originValue⟩ :=
    sourceSlotWritesHaveInputOrigins_proven c schedule defined source writing sourceSlot
  refine ⟨origin, input, ?_⟩
  have readValue :
      ((run c schedule (canonicalInitial c)).execution.event read).action.readValue =
        some (.payload call.registers.value) := by simp [load, Action.readValue]
  exact originValue.symm.trans (observedValue.symm.trans readValue)

def RemovalReadOrigin (c : Config) (schedule : List (Nat × Choice))
    (execution : Execution) (frame : SourceFrame) (call : QueueCall)
    (read source origin : execution.Id) : Prop :=
  frame ∈ sourceLog c schedule (canonicalInitial c) ∧
    (frame.state.threads frame.thread).call = some call ∧
    CompletedRemoval call ∧
    InputPublication c schedule execution origin ∧
    SlotOrigin c schedule execution source origin ∧
    execution.readSource read source = true ∧
    ∃ buffer index,
      (execution.event read).action =
        .plainLoad (.slot buffer index) (.payload call.registers.value)

theorem sourceRemoval_hasReadOrigin (c : Config) (schedule : List (Nat × Choice))
    (initial : c.SourceInitial)
    (scanner : ScannerOutputsValid c schedule (canonicalInitial c))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (frame : SourceFrame) (included : frame ∈ sourceLog c schedule (canonicalInitial c))
    (call : QueueCall) (selected : (frame.state.threads frame.thread).call = some call)
    (completed : CompletedRemoval call) :
    ∃ read source origin, RemovalReadOrigin c schedule
      (run c schedule (canonicalInitial c)).execution frame call read source origin := by
  have values := sourceLog_valueSources c schedule (canonicalInitial c)
    (canonicalInitial_valueSources c) frame included
  have ready := (values frame.thread).2 call selected
  have notPush : call.operation ≠ .push := by
    rcases completed.1 with ⟨operation, _⟩ | ⟨operation, _⟩ <;> simp [operation]
  have deps : call.registers.valueDeps ≠ [] := ready.2.2.2 notPush completed.2
  have observed := ready.2.1 deps
  have extension := (sourceLog_executionPrefix c schedule (canonicalInitial c) frame included).1
  have finalObserved := slotObservation_prefix extension frame.thread call.registers.value observed
  obtain ⟨event, member, _, buffer, index, action⟩ := finalObserved
  obtain ⟨position, bound, equal⟩ := List.mem_iff_getElem.mp member
  let execution := (run c schedule (canonicalInitial c)).execution
  let read : execution.Id := ⟨position, by simpa only [Array.length_toList] using bound⟩
  have eventEq : execution.event read = event := by
    simpa [Candidate.event, read] using equal
  have load : (execution.event read).action =
      .plainLoad (.slot buffer index) (.payload call.registers.value) := by
    simpa only [eventEq] using action
  have reading : execution.isRead read = true := by
    simp [Candidate.isRead, load, Action.readValue]
  obtain ⟨source, readFrom, writing, same, observedValue⟩ :=
    defined.1.1.2.1 read reading
  have sourceSlot : isSlotAction (execution.event source).action = true :=
    sameLocation_slot same (by simp [isSlotAction, load, Action.location])
  obtain ⟨origin, input, ancestry, originValue⟩ :=
    sourceSlotWritesHaveInputOrigins_proven c schedule defined source writing sourceSlot
  exact ⟨read, source, origin, included, selected, completed, input, ancestry,
    readFrom, buffer, index, load⟩

theorem sourceRemoval_hasOrigin (c : Config) (schedule : List (Nat × Choice))
    (initial : c.SourceInitial)
    (scanner : ScannerOutputsValid c schedule (canonicalInitial c))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (frame : SourceFrame) (included : frame ∈ sourceLog c schedule (canonicalInitial c))
    (call : QueueCall) (selected : (frame.state.threads frame.thread).call = some call)
    (completed : CompletedRemoval call) :
    ∃ origin, RemovalOrigin c schedule
      (run c schedule (canonicalInitial c)).execution frame call origin := by
  obtain ⟨origin, input, value⟩ := sourceReturnedWorkHasInputOrigin_proven
    c schedule initial scanner defined frame included call selected completed
  exact ⟨origin, included, selected, completed, input, value⟩

def LatestQueueWrite (execution : Execution) (location : Location)
    (write : execution.Id) (value : Int64) : Prop :=
  execution.isAtomicWrite write = true ∧
    (execution.event write).action.location = some location ∧
    (execution.event write).action.writeValue = some (.i64 value) ∧
    ∀ other : execution.Id, execution.isAtomicWrite other = true →
      (execution.event other).action.location = some location →
      (execution.event other).mo ≤ (execution.event write).mo

def QueueIntervalEmpty (execution : Execution) (owner : Nat) (kind : QueueKind) : Prop :=
  ∃ bottom top b t,
    LatestQueueWrite execution (.bottom owner kind) bottom b ∧
      LatestQueueWrite execution (.top owner kind) top t ∧ b.toInt ≤ t.toInt

def QuiescentQueues (c : Config) (state : State) : Prop :=
  state.barrierPassed = false ∧
  (∀ tid, tid < c.threads → c.present tid = true →
    (state.threads tid).call = none ∧ (state.threads tid).processing = false) ∧
  ∀ owner, owner < c.threads → c.present owner = true →
    ∀ kind, QueueIntervalEmpty state.execution owner kind

def TopClaimStep (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) (owner : Nat) (kind : QueueKind)
    (index : Int64) : Prop :=
  let frame := sourceFrameAt c schedule stepIndex
  ∃ call, (frame.state.threads frame.thread).call = some call ∧
    call.owner = owner ∧ call.kind = kind ∧ call.registers.t = index ∧
    frame.choice.i64 = index ∧
    ((call.operation = .pop ∧ call.pc = 83) ∨
      (call.operation = .steal ∧ call.pc = 102))

def TopClaimEvent (execution : Execution) (owner : Nat) (kind : QueueKind)
    (index : Int64) (event : execution.Id) : Prop :=
  (execution.event event).action =
    .cas (.top owner kind) .seqCst .seqCst
      (.i64 index) (.i64 (index + 1)) (.i64 index)

theorem sourceTopClaimEvent_unique (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (faultFree : (run c schedule (canonicalInitial c)).fault = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (owner : Nat) (kind : QueueKind) (index : Int64)
    (left right : (run c schedule (canonicalInitial c)).execution.Id)
    (leftClaim : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      owner kind index left)
    (rightClaim : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      owner kind index right) : left = right :=
  canonicalSourceTopClaimsUnique c schedule before faultFree defined
    owner kind left right index leftClaim rightClaim

theorem topRemovalStep_unique (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (faultFree : (run c schedule (canonicalInitial c)).fault = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (left right : Fin schedule.length) (owner : Nat) (kind : QueueKind)
    (index : Int64)
    (leftClaim rightClaim : (run c schedule (canonicalInitial c)).execution.Id)
    (leftEmits : SourceEmissionAt c schedule left leftClaim)
    (rightEmits : SourceEmissionAt c schedule right rightClaim)
    (leftEvent : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      owner kind index leftClaim)
    (rightEvent : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      owner kind index rightClaim) : left = right := by
  have claimEq := sourceTopClaimEvent_unique c schedule before faultFree defined
    owner kind index leftClaim rightClaim leftEvent rightEvent
  subst rightClaim
  exact sourceEmissionAt_step_unique c schedule left right leftClaim leftEmits rightEmits

def TopClaimValue (execution : Execution) (location : Location) (index : Int)
    (event : execution.Id) : Prop :=
  ∃ expected desired : Int64,
    (execution.event event).action =
      .cas location .seqCst .seqCst
        (.i64 expected) (.i64 desired) (.i64 expected) ∧
    expected.toInt = index ∧ desired.toInt = index + 1

private theorem topClaimsBelow {execution : Execution}
    (consistent : execution.consistent = true) (location : Location)
    (shape : ∀ event : execution.Id,
      TopWriteShape location (execution.event event).action)
    (last : execution.Id)
    (lastLocation : (execution.event last).action.location = some location)
    (lastWrite : execution.isWrite last = true) :
    ∀ index : Int, 0 ≤ index → index < topValue (execution.event last).action →
      ∃ event : execution.Id, TopClaimValue execution location index event ∧
        (execution.event event).mo ≤ (execution.event last).mo := by
  generalize rankEq : (execution.event last).mo = rank
  induction rank using Nat.strongRecOn generalizing last with
  | ind rank ih =>
    intro index nonnegative below
    have wellFormed := (of_decide_eq_true consistent : execution.Consistent).1
    have atomic (event : execution.Id)
        (eventLocation : (execution.event event).action.location = some location)
        (eventWrite : execution.isWrite event = true) :
        execution.isAtomicWrite event = true := by
      have plain := topWrite_atomic (shape event) eventLocation eventWrite
      simp [Candidate.isAtomicWrite, eventWrite, plain]
    rcases shape last lastLocation lastWrite with initial |
      ⟨expected, desired, claim, increment⟩
    · simp [topValue, initial, Action.writeValue] at below
      omega
    · have lastTop : topValue (execution.event last).action = desired.toInt := by
        simp [topValue, claim, Action.writeValue]
      by_cases current : index = expected.toInt
      · exact ⟨last, ⟨expected, desired, claim, current.symm, by omega⟩, by omega⟩
      · have earlierIndex : index < expected.toInt := by
          rw [lastTop, increment] at below
          omega
        have reading : execution.isRead last = true := by
          simp [Candidate.isRead, claim, Action.readValue]
        obtain ⟨source, readFrom, sourceWrite, same, value⟩ :=
          wellFormed.2.1 last reading
        have sourceLocation : (execution.event source).action.location = some location := by
          simp only [Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same
          exact same.2.symm.trans lastLocation
        have sourceValue : (execution.event source).action.writeValue = some (.i64 expected) := by
          simpa [claim, Action.readValue] using value.symm
        have sourceTop : topValue (execution.event source).action = expected.toInt := by
          simp [topValue, sourceValue]
        have rmw : (execution.event last).action.isRMW = true := by
          simp [claim, Action.isRMW]
        have immediate := Candidate.rmw_reads_immediate consistent last source rmw readFrom
        have lowerRank : (execution.event source).mo < rank := by omega
        obtain ⟨event, eventClaim, eventBefore⟩ :=
          ih (execution.event source).mo lowerRank source sourceLocation sourceWrite rfl
            index nonnegative (by simpa [sourceTop] using earlierIndex)
        exact ⟨event, eventClaim, Nat.le_trans eventBefore (Nat.le_of_lt lowerRank)⟩

private theorem topClaimValue_unique {execution : Execution}
    (consistent : execution.consistent = true) (location : Location)
    (shape : ∀ event : execution.Id,
      TopWriteShape location (execution.event event).action)
    (index : Int) (left right : execution.Id)
    (leftClaim : TopClaimValue execution location index left)
    (rightClaim : TopClaimValue execution location index right) : left = right := by
  obtain ⟨leftExpected, leftDesired, leftAction, _, leftValue⟩ := leftClaim
  obtain ⟨rightExpected, rightDesired, rightAction, _, rightValue⟩ := rightClaim
  have leftLocation : (execution.event left).action.location = some location := by
    simp [leftAction, Action.location]
  have rightLocation : (execution.event right).action.location = some location := by
    simp [rightAction, Action.location]
  have leftWrite : execution.isWrite left = true := by
    simp [Candidate.isWrite, leftAction, Action.writeValue]
  have rightWrite : execution.isWrite right = true := by
    simp [Candidate.isWrite, rightAction, Action.writeValue]
  have leftTop : topValue (execution.event left).action = index + 1 := by
    simp [topValue, leftAction, Action.writeValue, leftValue]
  have rightTop : topValue (execution.event right).action = index + 1 := by
    simp [topValue, rightAction, Action.writeValue, rightValue]
  rcases Nat.lt_trichotomy (execution.event left).mo (execution.event right).mo with
    before | equal | after
  · have strict := topWrite_values_strict consistent location shape left right
      leftLocation rightLocation leftWrite rightWrite before
    rw [leftTop, rightTop] at strict
    omega
  · have wellFormed := (of_decide_eq_true consistent : execution.Consistent).1
    have leftAtomic : execution.isAtomicWrite left = true := by
      simp [Candidate.isAtomicWrite, leftWrite, leftAction, Action.isPlain]
    have rightAtomic : execution.isAtomicWrite right = true := by
      simp [Candidate.isAtomicWrite, rightWrite, rightAction, Action.isPlain]
    exact wellFormed.2.2.2.2.1 left right leftAtomic rightAtomic
      (by simp [Candidate.sameLocation, leftLocation, rightLocation]) equal
  · have strict := topWrite_values_strict consistent location shape right left
      rightLocation leftLocation rightWrite leftWrite after
    rw [leftTop, rightTop] at strict
    omega

private theorem topClaimValue_below_latest {execution : Execution}
    (consistent : execution.consistent = true) (location : Location)
    (shape : ∀ event : execution.Id,
      TopWriteShape location (execution.event event).action)
    (latest : execution.Id) (latestValue : Int64)
    (latestWrite : LatestQueueWrite execution location latest latestValue)
    (index : Int) (claim : execution.Id)
    (claimed : TopClaimValue execution location index claim) :
    index < latestValue.toInt := by
  obtain ⟨expected, desired, action, _, desiredValue⟩ := claimed
  have claimLocation : (execution.event claim).action.location = some location := by
    simp [action, Action.location]
  have claimWrite : execution.isAtomicWrite claim = true := by
    simp [Candidate.isAtomicWrite, Candidate.isWrite, action,
      Action.writeValue, Action.isPlain]
  have claimLe := latestWrite.2.2.2 claim claimWrite claimLocation
  have latestTop : topValue (execution.event latest).action = latestValue.toInt := by
    simp [topValue, latestWrite.2.2]
  have claimTop : topValue (execution.event claim).action = index + 1 := by
    simp [topValue, action, Action.writeValue, desiredValue]
  rcases Nat.lt_or_eq_of_le claimLe with before | equal
  · have strict := topWrite_values_strict consistent location shape claim latest
      claimLocation latestWrite.2.1 (by
        simp [Candidate.isWrite, action, Action.writeValue])
      (Bool.and_eq_true_iff.mp latestWrite.1).1 before
    rw [claimTop, latestTop] at strict
    omega
  · have wellFormed := (of_decide_eq_true consistent : execution.Consistent).1
    have same : execution.sameLocation claim latest = true := by
      simp [Candidate.sameLocation, claimLocation, latestWrite.2.1]
    have equalEvent := wellFormed.2.2.2.2.1 claim latest claimWrite latestWrite.1 same equal
    subst claim
    rw [claimTop] at latestTop
    omega

theorem canonicalTopIndexPartition (c : Config) (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (faultFree : (run c schedule (canonicalInitial c)).fault = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (owner : Nat) (kind : QueueKind)
    (top : (run c schedule (canonicalInitial c)).execution.Id) (value : Int64)
    (latest : LatestQueueWrite (run c schedule (canonicalInitial c)).execution
      (.top owner kind) top value) (index : Int) (nonnegative : 0 ≤ index) :
    index < value.toInt ↔
      ∃ event : (run c schedule (canonicalInitial c)).execution.Id,
        TopClaimValue (run c schedule (canonicalInitial c)).execution
          (.top owner kind) index event ∧
        ∀ other, TopClaimValue (run c schedule (canonicalInitial c)).execution
          (.top owner kind) index other → other = event := by
  let execution := (run c schedule (canonicalInitial c)).execution
  have census := run_census c schedule (canonicalInitial c)
    (canonicalInitial_control c) before faultFree owner kind
    (fun event member => initialEvents_topShape c owner kind event
      (by simpa [canonicalInitial] using member))
  have shape (event : execution.Id) :
      TopWriteShape (.top owner kind) (execution.event event).action :=
    topCensus_event census event
  constructor
  · intro below
    have topValueEq : topValue (execution.event top).action = value.toInt := by
      unfold topValue
      rw [latest.2.2.1]
    have belowTop : index < topValue (execution.event top).action := by
      rw [topValueEq]
      exact below
    have topWriting : execution.isWrite top = true :=
      (Bool.and_eq_true_iff.mp latest.1).1
    obtain ⟨event, claim, _⟩ := topClaimsBelow (decide_eq_true defined.1)
      (.top owner kind) shape top latest.2.1 topWriting index nonnegative belowTop
    refine ⟨event, claim, ?_⟩
    intro other otherClaim
    exact topClaimValue_unique (decide_eq_true defined.1)
      (.top owner kind) shape index other event otherClaim claim
  · rintro ⟨event, claim, _⟩
    exact topClaimValue_below_latest (decide_eq_true defined.1)
      (.top owner kind) shape top value latest index event claim

def OwnerTailRemovalStep (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) (owner : Nat) (kind : QueueKind)
    (index : Int64) : Prop :=
  let frame := sourceFrameAt c schedule stepIndex
  ∃ call, (frame.state.threads frame.thread).call = some call ∧
    call.owner = owner ∧ call.kind = kind ∧ call.registers.b = index ∧
    call.operation = .pop ∧ call.pc = 82 ∧
    call.registers.t < call.registers.b

def InputStepFor (owner : Nat) (kind : QueueKind) (frame : SourceFrame) : Bool :=
  match (frame.state.threads frame.thread).call with
  | some call => decide (call.operation = .push) && decide (call.pc = 672) &&
      decide (call.owner = owner) && decide (call.kind = kind)
  | none => false

def PushCommitStepFor (owner : Nat) (kind : QueueKind) (frame : SourceFrame) : Bool :=
  match (frame.state.threads frame.thread).call with
  | some call => decide (call.operation = .push) && decide (call.pc = 69) &&
      decide (call.owner = owner) && decide (call.kind = kind)
  | none => false

def OwnerRemovalStepFor (owner : Nat) (kind : QueueKind) (frame : SourceFrame) : Bool :=
  match (frame.state.threads frame.thread).call with
  | some call => decide (call.operation = .pop) && decide (call.pc = 82) &&
      decide (call.owner = owner) && decide (call.kind = kind) &&
      decide (call.registers.t < call.registers.b)
  | none => false

def TopRemovalStepFor (owner : Nat) (kind : QueueKind) (frame : SourceFrame) : Bool :=
  match (frame.state.threads frame.thread).call with
  | some call =>
      decide (call.owner = owner) && decide (call.kind = kind) &&
      decide (frame.choice.i64 = call.registers.t) &&
      decide ((call.operation = .pop ∧ call.pc = 83) ∨
        (call.operation = .steal ∧ call.pc = 102))
  | none => false

def ReturnStepFor (owner : Nat) (kind : QueueKind) (frame : SourceFrame) : Bool :=
  match (frame.state.threads frame.thread).call with
  | some call => decide (call.owner = owner) && decide (call.kind = kind) &&
      decide (call.registers.value ≠ .zero) &&
      decide ((call.operation = .pop ∧ call.pc = 92) ∨
        (call.operation = .steal ∧ call.pc = 105))
  | none => false

structure QueueWorkCounts where
  inputs : Nat
  commits : Nat
  ownerRemovals : Nat
  topRemovals : Nat
  returns : Nat
  deriving DecidableEq, Repr

def queueWorkCounts (c : Config) (schedule : List (Nat × Choice))
    (owner : Nat) (kind : QueueKind) : QueueWorkCounts :=
  let frames := sourceLog c schedule (canonicalInitial c)
  { inputs := countTrue (InputStepFor owner kind) frames
    commits := countTrue (PushCommitStepFor owner kind) frames
    ownerRemovals := countTrue (OwnerRemovalStepFor owner kind) frames
    topRemovals := countTrue (TopRemovalStepFor owner kind) frames
    returns := countTrue (ReturnStepFor owner kind) frames }

def IndexedRemovalAt (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length)
    (read source origin : (run c schedule (canonicalInitial c)).execution.Id) : Prop :=
  ∃ call,
    ((sourceFrameAt c schedule stepIndex).state.threads
      (sourceFrameAt c schedule stepIndex).thread).call = some call ∧
    RemovalReadOrigin c schedule (run c schedule (canonicalInitial c)).execution
      (sourceFrameAt c schedule stepIndex) call read source origin

def CompletedRemovalAt (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) : Prop :=
  ∃ call, ((sourceFrameAt c schedule stepIndex).state.threads
      (sourceFrameAt c schedule stepIndex).thread).call = some call ∧
    CompletedRemoval call

theorem sourceFrameAt_mem (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length) :
    sourceFrameAt c schedule stepIndex ∈ sourceLog c schedule (canonicalInitial c) := by
  unfold sourceFrameAt
  exact List.getElem_mem _

theorem completedRemoval_hasIndexedOrigin (c : Config)
    (schedule : List (Nat × Choice)) (initial : c.SourceInitial)
    (scanner : ScannerOutputsValid c schedule (canonicalInitial c))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (stepIndex : Fin schedule.length)
    (completed : CompletedRemovalAt c schedule stepIndex) :
    ∃ read source origin, IndexedRemovalAt c schedule stepIndex read source origin := by
  obtain ⟨call, selected, removal⟩ := completed
  have included := sourceFrameAt_mem c schedule stepIndex
  obtain ⟨read, source, origin, relation⟩ := sourceRemoval_hasReadOrigin
    c schedule initial scanner defined (sourceFrameAt c schedule stepIndex)
      included call selected removal
  exact ⟨read, source, origin, call, selected, relation⟩

def ClosedEventCut (execution : Execution) (cut : execution.Id → Prop) : Prop :=
  ∀ before after, cut after → execution.happensBefore before after = true → cut before

def InputInCut (c : Config) (schedule : List (Nat × Choice))
    (cut : (run c schedule (canonicalInitial c)).execution.Id → Prop)
    (origin : (run c schedule (canonicalInitial c)).execution.Id) : Prop :=
  InputPublication c schedule (run c schedule (canonicalInitial c)).execution origin ∧
    cut origin

def RemovalReadInCut (c : Config) (schedule : List (Nat × Choice))
    (cut : (run c schedule (canonicalInitial c)).execution.Id → Prop)
    (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id) : Prop :=
  ∃ read source, IndexedRemovalAt c schedule stepIndex read source origin ∧ cut read

theorem slotOrigin_happensBeforeOrEq {c : Config}
    {schedule : List (Nat × Choice)} {execution : Execution}
    (defined : execution.Defined) {write origin : execution.Id}
    (ancestry : SlotOrigin c schedule execution write origin) :
    origin = write ∨ execution.happensBefore origin write = true := by
  induction ancestry with
  | input _ => exact Or.inl rfl
  | @copy write read source origin resize readFrom prior ih =>
      obtain ⟨frame, included, call, _, selected, copy, _, readBefore,
        readThread, readShape, appended⟩ := resize
      have reading : execution.isRead read = true := by
        simp [Candidate.isRead, readShape, Action.readValue]
      have ordinary : (execution.event read).action.isPlain = true := by
        simp [readShape, Action.isPlain]
      have sourceBeforeRead := (defined.2.2 read source ordinary reading readFrom).1
      have operation : call.operation = .push := copy.1
      have pc : call.pc = 616 := copy.2.1
      have writeThread : (execution.event write).thread = frame.thread := by
        apply queueSource_thread c frame
        refine ⟨call, selected, ?_, appended⟩
        rw [copy.2.2]
        simp [queueAction, operation, pc]
      have writeNonInit : (execution.event write).action.isInit = false := by
        rw [copy.2.2]
        rfl
      have readNonInit : (execution.event read).action.isInit = false := by
        rw [readShape]
        rfl
      have readBeforeWrite : execution.sequencedBefore read write = true := by
        simp [Candidate.sequencedBefore, readNonInit, writeNonInit,
          readThread, writeThread, readBefore]
      have sourceBeforeWrite := Candidate.happensBefore_trans sourceBeforeRead
        (Candidate.happensBefore_of_sequencedBefore readBeforeWrite)
      rcases ih with equal | originBefore
      · exact Or.inr (by simpa [equal] using sourceBeforeWrite)
      · exact Or.inr (Candidate.happensBefore_trans originBefore sourceBeforeWrite)

theorem removalInClosedCut_hasInput (c : Config)
    (schedule : List (Nat × Choice))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (cut : (run c schedule (canonicalInitial c)).execution.Id → Prop)
    (closed : ClosedEventCut (run c schedule (canonicalInitial c)).execution cut)
    (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (removed : RemovalReadInCut c schedule cut stepIndex origin) :
    InputInCut c schedule cut origin := by
  obtain ⟨read, source, indexed, readCut⟩ := removed
  obtain ⟨call, selected, relation⟩ := indexed
  obtain ⟨_, _, _, input, ancestry, readFrom, _, _, load⟩ := relation
  have reading : (run c schedule (canonicalInitial c)).execution.isRead read = true := by
    simp [Candidate.isRead, load, Action.readValue]
  have ordinary :
      ((run c schedule (canonicalInitial c)).execution.event read).action.isPlain = true := by
    simp [load, Action.isPlain]
  have sourceBefore := (defined.2.2 read source ordinary reading readFrom).1
  have sourceCut := closed source read readCut sourceBefore
  refine ⟨input, ?_⟩
  rcases slotOrigin_happensBeforeOrEq defined ancestry with equal | originBefore
  · simpa [equal] using sourceCut
  · exact closed origin source sourceCut originBefore

def completedRemovalOriginsRespectClosedCuts : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)), c.SourceInitial →
    ScannerOutputsValid c schedule (canonicalInitial c) →
    let execution := (run c schedule (canonicalInitial c)).execution
    execution.Defined → ∀ cut : execution.Id → Prop, ClosedEventCut execution cut →
    ∀ stepIndex origin, RemovalReadInCut c schedule cut stepIndex origin →
      InputInCut c schedule cut origin

theorem completedRemovalOriginsRespectClosedCuts_proven :
    completedRemovalOriginsRespectClosedCuts := by
  intro c schedule _ _
  dsimp
  intro defined cut closed stepIndex origin removed
  exact removalInClosedCut_hasInput c schedule defined cut closed stepIndex origin removed

inductive RemovalClass where
  | ownerTail | topClaim
  deriving DecidableEq, Repr

def LinearizedRemovalAt (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (removalClass : RemovalClass) : Prop :=
  let frame := sourceFrameAt c schedule stepIndex
  let execution := (run c schedule (canonicalInitial c)).execution
  ∃ call read source owner kind index,
    (frame.state.threads frame.thread).call = some call ∧
    call.owner = owner ∧ call.kind = kind ∧
    call.registers.valueDeps = [read.val] ∧
    execution.readSource read source = true ∧
    IndexedSlotOrigin c schedule execution source origin owner kind index ∧
    match removalClass with
    | .ownerTail => call.operation = .pop ∧ call.pc = 82 ∧
        call.registers.t < call.registers.b ∧ index = call.registers.b
    | .topClaim => ((call.operation = .pop ∧ call.pc = 83) ∨
          (call.operation = .steal ∧ call.pc = 102)) ∧
        frame.choice.i64 = call.registers.t ∧ index = call.registers.t ∧
        ∃ claim : execution.Id,
          SourceEmissionAt c schedule stepIndex claim ∧
          TopClaimEvent execution owner kind index claim

theorem linearizedRemoval_readShape (c : Config)
    (schedule : List (Nat × Choice)) (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (removalClass : RemovalClass)
    (removal : LinearizedRemovalAt c schedule stepIndex origin removalClass) :
    ∃ call read source owner kind index buffer slot,
      ((sourceFrameAt c schedule stepIndex).state.threads
        (sourceFrameAt c schedule stepIndex).thread).call = some call ∧
      call.owner = owner ∧ call.kind = kind ∧
      call.registers.valueDeps = [read.val] ∧
      (run c schedule (canonicalInitial c)).execution.readSource read source = true ∧
      IndexedSlotOrigin c schedule
        (run c schedule (canonicalInitial c)).execution source origin owner kind index ∧
      ((run c schedule (canonicalInitial c)).execution.event read).action =
        .plainLoad (.slot buffer slot) (.payload call.registers.value) := by
  obtain ⟨call, read, source, owner, kind, index, selected, ownerEq, kindEq,
    deps, readFrom, ancestry, linearization⟩ := removal
  have notPush : call.operation ≠ .push := by
    cases removalClass with
    | ownerTail => simp_all
    | topClaim => rcases linearization.1 with operation | operation <;> simp_all
  have nonempty : call.registers.valueDeps ≠ [] := by simp [deps]
  have included := sourceFrameAt_mem c schedule stepIndex
  obtain ⟨localRead, localDeps, localThread, buffer, slot, localAction⟩ :=
    canonical_removalRead c schedule (sourceFrameAt c schedule stepIndex)
      included call selected notPush nonempty
  have indexEq : localRead.val = read.val := by
    exact (List.cons.inj (localDeps.symm.trans deps)).1
  have extension := (sourceLog_executionPrefix c schedule (canonicalInitial c)
    (sourceFrameAt c schedule stepIndex) included).1
  let lifted : (run c schedule (canonicalInitial c)).execution.Id :=
    ⟨localRead.val,
      Nat.lt_of_lt_of_le localRead.isLt (executionPrefix_size extension)⟩
  have readEq : read = lifted := Fin.ext indexEq.symm
  have action :
      ((run c schedule (canonicalInitial c)).execution.event read).action =
        .plainLoad (.slot buffer slot) (.payload call.registers.value) := by
    rw [readEq, executionPrefix_event extension localRead, localAction]
  exact ⟨call, read, source, owner, kind, index, buffer, slot, selected,
    ownerEq, kindEq, deps, readFrom, ancestry, action⟩

theorem linearizedRemoval_hasInput (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (removalClass : RemovalClass)
    (removal : LinearizedRemovalAt c schedule stepIndex origin removalClass) :
    InputPublication c schedule (run c schedule (canonicalInitial c)).execution origin := by
  obtain ⟨call, read, source, owner, kind, index, selected, ownerEq, kindEq,
    deps, readFrom, ancestry, linearization⟩ := removal
  exact indexedSlotOrigin_input ancestry

theorem linearizedRemoval_origin_functional (c : Config)
    (schedule : List (Nat × Choice))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (stepIndex : Fin schedule.length)
    (leftOrigin rightOrigin :
      (run c schedule (canonicalInitial c)).execution.Id)
    (leftClass rightClass : RemovalClass)
    (left : LinearizedRemovalAt c schedule stepIndex leftOrigin leftClass)
    (right : LinearizedRemovalAt c schedule stepIndex rightOrigin rightClass) :
    leftOrigin = rightOrigin := by
  obtain ⟨leftCall, leftRead, leftSource, leftOwner, leftKind, leftIndex,
    leftSelected, leftOwnerEq, leftKindEq, leftDeps, leftReadFrom,
    leftAncestry, leftLinearization⟩ := left
  obtain ⟨rightCall, rightRead, rightSource, rightOwner, rightKind, rightIndex,
    rightSelected, rightOwnerEq, rightKindEq, rightDeps, rightReadFrom,
    rightAncestry, rightLinearization⟩ := right
  have callEq : leftCall = rightCall :=
    Option.some.inj (leftSelected.symm.trans rightSelected)
  subst rightCall
  have readEq : leftRead = rightRead := by
    apply Fin.ext
    have equalDeps := leftDeps.symm.trans rightDeps
    exact (List.cons.inj equalDeps).1
  subst rightRead
  have sourceEq := readSource_functional leftReadFrom rightReadFrom
  subst rightSource
  exact indexedSlotOrigin_origin_functional c schedule defined leftAncestry rightAncestry

theorem linearizedTopRemoval_origin_injective (c : Config)
    (schedule : List (Nat × Choice))
    (before : (run c schedule (canonicalInitial c)).barrierPassed = false)
    (faultFree : (run c schedule (canonicalInitial c)).fault = false)
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (leftStep rightStep : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (left : LinearizedRemovalAt c schedule leftStep origin .topClaim)
    (right : LinearizedRemovalAt c schedule rightStep origin .topClaim) :
    leftStep = rightStep := by
  obtain ⟨leftCall, leftRead, leftSource, leftOwner, leftKind, leftIndex,
    leftSelected, leftOwnerEq, leftKindEq, leftDeps, leftReadFrom, leftAncestry,
    leftOperation, leftChoice, leftIndexEq, leftClaim, leftEmits, leftEvent⟩ := left
  obtain ⟨rightCall, rightRead, rightSource, rightOwner, rightKind, rightIndex,
    rightSelected, rightOwnerEq, rightKindEq, rightDeps, rightReadFrom, rightAncestry,
    rightOperation, rightChoice, rightIndexEq, rightClaim, rightEmits, rightEvent⟩ := right
  obtain ⟨ownerEq, kindEq, indexEq⟩ := indexedSlotOrigin_metadata_functional
    c schedule leftSource rightSource origin leftAncestry rightAncestry
  have leftLogical : leftCall.registers.t = leftIndex := leftIndexEq.symm
  have leftEvent' : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      leftOwner leftKind leftIndex leftClaim := by
    simpa only [leftOwnerEq, leftKindEq, leftLogical] using leftEvent
  have rightEvent' : TopClaimEvent (run c schedule (canonicalInitial c)).execution
      leftOwner leftKind leftIndex rightClaim := by
    have rightOwnerToLeft' : rightOwner = leftOwner := ownerEq.symm
    have rightKindToLeft' : rightKind = leftKind := kindEq.symm
    have rightIndexToLeft' : rightIndex = leftIndex := indexEq.symm
    simpa only [rightOwnerToLeft', rightKindToLeft', rightIndexToLeft'] using rightEvent
  exact topRemovalStep_unique c schedule before faultFree defined leftStep rightStep
    leftOwner leftKind leftIndex leftClaim rightClaim leftEmits rightEmits leftEvent' rightEvent'

structure EventFrameCut (c : Config) (schedule : List (Nat × Choice)) where
  events : (run c schedule (canonicalInitial c)).execution.Id → Prop
  frames : Fin schedule.length → Prop
  eventsClosed : ClosedEventCut (run c schedule (canonicalInitial c)).execution events

def LinearizedRemovalInCut (c : Config) (schedule : List (Nat × Choice))
    (cut : EventFrameCut c schedule) (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id) : Prop :=
  ∃ removalClass, LinearizedRemovalAt c schedule stepIndex origin removalClass ∧
    cut.frames stepIndex

def ExactWorkPartitionAtCut (c : Config) (schedule : List (Nat × Choice))
    (cut : EventFrameCut c schedule) : Prop :=
  (∀ stepIndex origin, LinearizedRemovalInCut c schedule cut stepIndex origin →
    InputInCut c schedule cut.events origin) ∧
  (∀ stepIndex left right,
    LinearizedRemovalInCut c schedule cut stepIndex left →
    LinearizedRemovalInCut c schedule cut stepIndex right → left = right) ∧
  (∀ left right origin,
    LinearizedRemovalInCut c schedule cut left origin →
    LinearizedRemovalInCut c schedule cut right origin → left = right) ∧
  ∀ origin, InputInCut c schedule cut.events origin →
    ∃ stepIndex, LinearizedRemovalInCut c schedule cut stepIndex origin

def fullEventFrameCut (c : Config) (schedule : List (Nat × Choice)) :
    EventFrameCut c schedule :=
  { events := fun _ => True
    frames := fun _ => True
    eventsClosed := by simp [ClosedEventCut] }

theorem fullCutLinearized_hasInput (c : Config) (schedule : List (Nat × Choice))
    (stepIndex : Fin schedule.length)
    (origin : (run c schedule (canonicalInitial c)).execution.Id)
    (removal : LinearizedRemovalInCut c schedule
      (fullEventFrameCut c schedule) stepIndex origin) :
    InputInCut c schedule (fullEventFrameCut c schedule).events origin := by
  obtain ⟨removalClass, relation, _⟩ := removal
  exact ⟨linearizedRemoval_hasInput c schedule stepIndex origin removalClass relation, trivial⟩

theorem fullCutLinearized_origin_functional (c : Config)
    (schedule : List (Nat × Choice))
    (defined : (run c schedule (canonicalInitial c)).execution.Defined)
    (stepIndex : Fin schedule.length)
    (left right : (run c schedule (canonicalInitial c)).execution.Id)
    (leftRemoval : LinearizedRemovalInCut c schedule
      (fullEventFrameCut c schedule) stepIndex left)
    (rightRemoval : LinearizedRemovalInCut c schedule
      (fullEventFrameCut c schedule) stepIndex right) : left = right := by
  obtain ⟨leftClass, leftRelation, _⟩ := leftRemoval
  obtain ⟨rightClass, rightRelation, _⟩ := rightRemoval
  exact linearizedRemoval_origin_functional c schedule defined stepIndex
    left right leftClass rightClass leftRelation rightRelation

def canonicalWorkConservation : Prop :=
  ∀ (c : Config) (schedule : List (Nat × Choice)), c.SourceInitial →
    ScannerOutputsValid c schedule (canonicalInitial c) →
    let final := run c schedule (canonicalInitial c)
    final.fault = false → final.execution.Defined → QuiescentQueues c final →
    ExactWorkPartitionAtCut c schedule (fullEventFrameCut c schedule)


end DequeRefinement

end JuliaLean.CRuntime.ParallelMark
