import JuliaLean.base.lock
import JuliaLean.Proofs.base.task.interleavings
import JuliaLean.Proofs.base.condition.task_properties

namespace JuliaLean.Tasks



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

def LockWrapperBodies : Prop := ∀ (lockSucceeded bodySucceeded holdsLock : Bool) (value : Nat),
  withLock lockSucceeded bodySucceeded value =
    (if !lockSucceeded then .threw else if bodySucceeded then .returned value else .threw) ∧
  lockableGet holdsLock value = (if holdsLock then .returned value else .threw)

theorem lockWrapperBodies_proven : LockWrapperBodies := by
  unfold LockWrapperBodies
  intros
  exact ⟨rfl, rfl⟩

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

def LockOnceThreadBodies : Prop := ∀ (cells : List OnceCell) (thread : Nat)
    (initializer : Except Nat Nat),
  (oncePerThreadGet cells thread initializer).length = cells.length

theorem lockOnceThreadBodies_proven : LockOnceThreadBodies := by
  intro cells thread initializer
  simp [oncePerThreadGet]
  split <;> simp

def LockOnceTaskBodies : Prop := ∀ (hasValue : Bool) (value initialized : Nat),
  oncePerTaskGet hasValue value initialized = if hasValue then value else initialized

theorem lockOnceTaskBodies_proven : LockOnceTaskBodies := by
  unfold LockOnceTaskBodies
  intros
  rfl

end JuliaLean.Tasks
