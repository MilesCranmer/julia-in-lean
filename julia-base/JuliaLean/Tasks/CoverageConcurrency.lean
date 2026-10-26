import JuliaLean.Tasks.TaskModel
import JuliaLean.Tasks.Condition

/-! Source-body models for `base/lock.jl` and `base/partr.jl`. -/

namespace JuliaLean.Tasks

/-! ## base/lock.jl:10-458, ReentrantLock and higher-order wrappers -/

structure CoverageReentrantLock where
  owner : Option Nat := none
  count : Nat := 0
  locked : Bool := false
  deriving Repr, DecidableEq

def newReentrantLock : CoverageReentrantLock := {}

def reentrantTryLock (lock : CoverageReentrantLock) (task : Nat) :
    Bool × CoverageReentrantLock :=
  if lock.owner == some task then
    (true, { lock with count := (lock.count + 1) % 2^32 })
  else if lock.locked then (false, lock)
  else (true, ⟨some task, 1, true⟩)

def reentrantUnlock (lock : CoverageReentrantLock) (task : Nat) :
    Except String CoverageReentrantLock :=
  if lock.owner != some task then .error "unlock owner"
  else
    let count := (lock.count + 2^32 - 1) % 2^32
    if count == 0 then .ok {} else .ok { lock with count := count }

def unlockAll (lock : CoverageReentrantLock) (task : Nat) :
    Except String (Nat × CoverageReentrantLock) :=
  if lock.owner == some task then .ok (lock.count, {}) else .error "unlock owner"

def relockAll (lock : CoverageReentrantLock) (task count : Nat) : CoverageReentrantLock :=
  if count == 0 then lock else ⟨some task, count % 2^32, true⟩

def LockReentrantBodies : Prop := ∀ (lock : CoverageReentrantLock) (task count : Nat),
  newReentrantLock = {} ∧
  (reentrantTryLock lock task).1 = (lock.owner == some task || !lock.locked) ∧
  relockAll {} task count = (if count == 0 then {} else ⟨some task, count % 2^32, true⟩)

theorem lockReentrantBodies_proven : LockReentrantBodies := by
  intro lock task count
  constructor
  · rfl
  constructor
  · simp [reentrantTryLock]
    split <;> rename_i howner
    · simp [howner]
    · split <;> rename_i hlocked <;> simp_all
  · rfl

inductive WrappedCall (α : Type) where | returned (value : α) | threw
  deriving Repr, DecidableEq

def withLock (lockSucceeded bodySucceeded : Bool) (value : Nat) : WrappedCall Nat :=
  if !lockSucceeded then .threw else if bodySucceeded then .returned value else .threw

def lockableGet (holdsLock : Bool) (value : Nat) : WrappedCall Nat :=
  if holdsLock then .returned value else .threw

def LockWrapperBodies : Prop := ∀ (lockSucceeded bodySucceeded holdsLock : Bool) (value : Nat),
  withLock lockSucceeded bodySucceeded value =
    (if !lockSucceeded then .threw else if bodySucceeded then .returned value else .threw) ∧
  lockableGet holdsLock value = (if holdsLock then .returned value else .threw)

theorem lockWrapperBodies_proven : LockWrapperBodies := by
  unfold LockWrapperBodies
  intros
  exact ⟨rfl, rfl⟩

/-! ## base/lock.jl:565-679, Semaphore -/

structure CoverageSemaphore where
  size : Nat
  current : Nat := 0
  waiting : Nat := 0
  deriving Repr, DecidableEq

inductive SemaphoreResult where | acquired | parked | released | error
  deriving Repr, DecidableEq

def semaphoreAcquire (semaphore : CoverageSemaphore) : SemaphoreResult × CoverageSemaphore :=
  if semaphore.current < semaphore.size then
    (.acquired, { semaphore with current := semaphore.current + 1 })
  else (.parked, { semaphore with waiting := semaphore.waiting + 1 })

def semaphoreRelease (semaphore : CoverageSemaphore) : SemaphoreResult × CoverageSemaphore :=
  if semaphore.current == 0 then (.error, semaphore)
  else if 0 < semaphore.waiting then
    (.released, ⟨semaphore.size, semaphore.current - 1, semaphore.waiting - 1⟩)
  else (.released, { semaphore with current := semaphore.current - 1 })

def LockSemaphoreBodies : Prop := ∀ (semaphore : CoverageSemaphore),
  (semaphoreAcquire semaphore).1 =
    (if semaphore.current < semaphore.size then .acquired else .parked) ∧
  ((semaphoreRelease semaphore).1 = .error ↔ semaphore.current = 0)

theorem lockSemaphoreBodies_proven : LockSemaphoreBodies := by
  intro semaphore
  constructor
  · simp [semaphoreAcquire]
    split <;> rfl
  · by_cases zero : semaphore.current = 0
    · simp [semaphoreRelease, zero]
    · simp [semaphoreRelease, zero]
      split <;> simp

/-! ## base/lock.jl:701-758, Event -/

structure CoverageEvent where
  autoreset : Bool
  set : Bool := false
  deriving Repr, DecidableEq

def eventWait (event : CoverageEvent) : Bool × CoverageEvent :=
  if event.set then (true, if event.autoreset then { event with set := false } else event)
  else (false, event)

def eventNotify (event : CoverageEvent) : CoverageEvent := { event with set := true }
def eventReset (event : CoverageEvent) : CoverageEvent := { event with set := false }

def LockEventBodies : Prop := ∀ (event : CoverageEvent),
  (eventNotify event).set = true ∧ (eventReset event).set = false ∧
  (event.autoreset → event.set → (eventWait event).2.set = false)

theorem lockEventBodies_proven : LockEventBodies := by
  intro event
  constructor
  · rfl
  constructor
  · rfl
  · intro autoreset set
    simp [eventWait, autoreset, set]

/-! ## base/lock.jl:801-868, OncePerProcess and AtomicMemory helpers -/

inductive OnceState where | initial | running | hasRun | failed
  deriving Repr, DecidableEq

structure OnceCell where
  state : OnceState := .initial
  value : Option Nat := none
  deriving Repr, DecidableEq

def oncePerProcess (cell : OnceCell) (initializer : Except Nat Nat) : OnceCell :=
  match cell.state with
  | .hasRun | .failed => cell
  | .running => cell
  | .initial =>
      match initializer with
      | .ok value => ⟨.hasRun, some value⟩
      | .error error => ⟨.failed, some error⟩

def copyMonotonic (source : List Nat) : List Nat := source
def fillMonotonic (length value : Nat) : List Nat := List.replicate length value

def LockOnceProcessBodies : Prop := ∀ (cell : OnceCell) (result : Except Nat Nat)
    (source : List Nat) (length value : Nat),
  copyMonotonic source = source ∧
  (fillMonotonic length value).length = length ∧
  (oncePerProcess cell result).state =
    (match cell.state with
     | .initial => match result with | .ok _ => .hasRun | .error _ => .failed
     | state => state)

theorem lockOnceProcessBodies_proven : LockOnceProcessBodies := by
  unfold LockOnceProcessBodies
  intro cell result source length value
  constructor
  · rfl
  constructor
  · simp [fillMonotonic]
  · rcases cell with ⟨state, stored⟩
    cases state <;> cases result <;> rfl

/-! ## base/lock.jl:914-1019, OncePerThread -/

def oncePerThreadGet (cells : List OnceCell) (thread : Nat) (initializer : Except Nat Nat) :
    List OnceCell :=
  match cells[thread]? with
  | none => cells
  | some cell => cells.set thread (oncePerProcess cell initializer)

def LockOnceThreadBodies : Prop := ∀ (cells : List OnceCell) (thread : Nat)
    (initializer : Except Nat Nat),
  (oncePerThreadGet cells thread initializer).length = cells.length

theorem lockOnceThreadBodies_proven : LockOnceThreadBodies := by
  intro cells thread initializer
  simp [oncePerThreadGet]
  split <;> simp

/-! ## base/lock.jl:1052-1063, OncePerTask -/

def oncePerTaskGet (hasValue : Bool) (value initialized : Nat) : Nat :=
  if hasValue then value else initialized

def LockOnceTaskBodies : Prop := ∀ (hasValue : Bool) (value initialized : Nat),
  oncePerTaskGet hasValue value initialized = if hasValue then value else initialized

theorem lockOnceTaskBodies_proven : LockOnceTaskBodies := by
  unfold LockOnceTaskBodies
  intros
  rfl

/-! ## base/partr.jl:28-75, task-local RNG -/

def partrCong (maximum draw : Nat) : Nat := if maximum == 0 then 0 else draw % maximum + 1

def partrNextSeed (seed : Nat) : Nat :=
  (69069 * seed + 362437) % 2^64

def partrRandom (maximum seed : Nat) : Nat × Nat :=
  if maximum == 1 then (0, seed)
  else
    let next := partrNextSeed seed
    (((maximum * (next % 2^32)) / 2^32) % 2^32, next)

def PartrRngBodies : Prop := ∀ (maximum seed draw : Nat),
  partrCong 0 draw = 0 ∧
  (0 < maximum → 1 ≤ partrCong maximum draw ∧ partrCong maximum draw ≤ maximum) ∧
  (partrRandom 1 seed = (0, seed))

theorem partrRngBodies_proven : PartrRngBodies := by
  intro maximum seed draw
  constructor
  · rfl
  constructor
  · intro positive
    simp [partrCong, Nat.ne_of_gt positive]
    exact Nat.mod_lt draw positive
  · rfl

/-! ## base/partr.jl:8-269, heap and multiqueue branches -/

structure CoverageTaskHeap where
  tasks : List Nat := []
  priorities : List Nat := []
  advertised : Nat := 65535
  deriving Repr, DecidableEq

def taskHeap : CoverageTaskHeap := {}

def heapInsert (heap : CoverageTaskHeap) (task priority : Nat) : CoverageTaskHeap :=
  { tasks := heap.tasks ++ [task]
    priorities := heap.priorities ++ [priority]
    advertised := min heap.advertised priority }

def heapDeleteFirst (heap : CoverageTaskHeap) : Option Nat × CoverageTaskHeap :=
  match heap.tasks, heap.priorities with
  | [], _ => (none, heap)
  | task :: tasks, _ :: priorities =>
      (some task, ⟨tasks, priorities, priorities.foldl min 65535⟩)
  | _, [] => (none, heap)

def siftUpDecision (index child parent : Nat) : Bool × Nat :=
  if 1 < index && child < parent then (true, (index - 2) / 8 + 1) else (false, index)

def siftDownDecision (index child childPriority parentPriority : Nat) : Bool × Nat :=
  if child ≤ 8 * index + 1 && childPriority < parentPriority then (true, child)
  else (false, index)

def PartrHeapBodies : Prop := ∀ (heap : CoverageTaskHeap) (task priority index child parent : Nat),
  (heapInsert heap task priority).tasks.length = heap.tasks.length + 1 ∧
  (heapInsert heap task priority).advertised = min heap.advertised priority ∧
  siftUpDecision index child parent =
    (if 1 < index && child < parent then (true, (index - 2) / 8 + 1) else (false, index))

theorem partrHeapBodies_proven : PartrHeapBodies := by
  unfold PartrHeapBodies
  intros
  exact ⟨by simp [heapInsert], rfl, rfl⟩

end JuliaLean.Tasks
