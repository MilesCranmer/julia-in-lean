import JuliaLean.ConcurrencyCov.Locks

/-! Per-method source-body models for `base/lock.jl`. -/

namespace JuliaLean.ConcurrencyCov.FaithfulLock

open JuliaLean.ConcurrencyCov

def currentTaskM := Locks.currentTask
def CurrentTaskProp : Prop := ∀ current, currentTaskM current = current
theorem currentTask_proven : CurrentTaskProp := by
  unfold CurrentTaskProp
  intros
  rfl
def reentrantCtor := Locks.reentrantLock
def ReentrantCtorProp : Prop := ∀ _u : Unit, reentrantCtor = {}
theorem reentrantCtor_proven : ReentrantCtorProp := by
  unfold ReentrantCtorProp
  intros
  rfl
def assertHavelockM := Locks.assertHavelock
def AssertHavelockProp : Prop := ∀ task lock, assertHavelockM task lock = Locks.assertHavelock task lock
theorem assertHavelock_proven : AssertHavelockProp := by
  unfold AssertHavelockProp
  intros
  rfl
def showLockM := Locks.showLock
def ShowLockProp : Prop := ∀ _lock : Locks.RLock, showLockM = "ReentrantLock()"
theorem showLock_proven : ShowLockProp := by
  unfold ShowLockProp
  intros
  rfl
def showPlainM := Locks.showPlain
def ShowPlainProp : Prop := ∀ compact current lock,
  showPlainM compact current lock = Locks.showPlain compact current lock
theorem showPlain_proven : ShowPlainProp := by
  unfold ShowPlainProp
  intros
  rfl
def islockedM := Locks.islocked
def IslockedProp : Prop := ∀ lock, islockedM lock = decide (lock.havelock % 2 = 1)
theorem islocked_proven : IslockedProp := by
  unfold IslockedProp
  intros
  rfl
def trylockM := Locks.trylock
def TrylockProp : Prop := ∀ task state, trylockM task state = Locks.trylock task state
theorem trylock_proven : TrylockProp := by
  unfold TrylockProp
  intros
  rfl
def trylockSlowM := Locks.trylockSlow
def TrylockSlowProp : Prop := ∀ task state, trylockSlowM task state = Locks.trylockSlow task state
theorem trylockSlow_proven : TrylockSlowProp := by
  unfold TrylockSlowProp
  intros
  rfl
def lockM := Locks.lock
def LockProp : Prop := ∀ task token state, lockM task token state = Locks.lock task token state
theorem lock_proven : LockProp := by
  unfold LockProp
  intros
  rfl
def slowlockM := Locks.slowlock
def SlowlockProp : Prop := ∀ task token state, slowlockM task token state = Locks.slowlock task token state
theorem slowlock_proven : SlowlockProp := by
  unfold SlowlockProp
  intros
  rfl
def conditionLockM := Locks.lockCond
def ConditionLockProp : Prop := ∀ task token state,
  conditionLockM task token state = Locks.lock task token state
theorem conditionLock_proven : ConditionLockProp := by
  unfold ConditionLockProp
  intros
  rfl
def waitNoRelockM := Locks.waitNoRelock
def WaitNoRelockProp : Prop := ∀ token, waitNoRelockM token = Locks.waitNoRelock token
theorem waitNoRelock_proven : WaitNoRelockProp := by
  unfold WaitNoRelockProp
  intros
  rfl
def uncancellableM := Locks.uncancellableLock
def UncancellableProp : Prop := ∀ task state, uncancellableM task state = Locks.lock task none state
theorem uncancellable_proven : UncancellableProp := by
  unfold UncancellableProp
  intros
  rfl
def relockallButOneM := Locks.relockallButOne
def RelockallButOneProp : Prop := ∀ state, relockallButOneM state =
  if state.val = 1 then none else some (state - u32 1)
theorem relockallButOne_proven : RelockallButOneProp := by
  unfold RelockallButOneProp
  intros
  rfl
def unlockM := Locks.unlock
def UnlockProp : Prop := ∀ task state, unlockM task state = Locks.unlock task state
theorem unlock_proven : UnlockProp := by
  unfold UnlockProp
  intros
  rfl
def unlockInnerM := Locks.unlockInner
def UnlockInnerProp : Prop := ∀ state, unlockInnerM state = Locks.unlockInner state
theorem unlockInner_proven : UnlockInnerProp := by
  unfold UnlockInnerProp
  intros
  rfl
def notifywaitersM := Locks.notifywaiters
def NotifywaitersProp : Prop := ∀ state, notifywaitersM state = Locks.notifywaiters state
theorem notifywaiters_proven : NotifywaitersProp := by
  unfold NotifywaitersProp
  intros
  rfl
def unlockallM := Locks.unlockall
def UnlockallProp : Prop := ∀ task state, unlockallM task state = Locks.unlockall task state
theorem unlockall_proven : UnlockallProp := by
  unfold UnlockallProp
  intros
  rfl
def relockallM := Locks.relockall
def RelockallProp : Prop := ∀ count state, relockallM count state = Locks.relockall count state
theorem relockall_proven : RelockallProp := by
  unfold RelockallProp
  intros
  rfl

def genericLockDo (acquire : Nat → R Unit) (release : Nat → R Unit) (body : Outcome) (lock : Nat) : R Nat := do
  acquire lock
  match body with
  | .ok value => let _ ← release lock; return value
  | .error e => let _ ← release lock; .error e
def GenericLockDoProp : Prop := ∀ acquire release body lock,
  genericLockDo acquire release body lock = do
    acquire lock
    match body with
    | .ok value => let _ ← release lock; return value
    | .error e => let _ ← release lock; .error e
theorem genericLockDo_proven : GenericLockDoProp := by
  unfold GenericLockDoProp
  intros
  rfl
def reentrantLockDoM := Locks.lockDo
def ReentrantLockDoProp : Prop := ∀ task body state,
  reentrantLockDoM task body state = Locks.lockDo task body state
theorem reentrantLockDo_proven : ReentrantLockDoProp := by
  unfold ReentrantLockDoProp
  intros
  rfl
def genericTrylockDoM := Locks.trylockDo
def GenericTrylockDoProp : Prop := ∀ task body state,
  genericTrylockDoM task body state = Locks.trylockDo task body state
theorem genericTrylockDo_proven : GenericTrylockDoProp := by
  unfold GenericTrylockDoProp
  intros
  rfl
def lockMacroM := Locks.lockMacro
def LockMacroProp : Prop := ∀ task body state, lockMacroM task body state = Locks.lockDo task body state
theorem lockMacro_proven : LockMacroProp := by
  unfold LockMacroProp
  intros
  rfl
def lockNofailM := Locks.lockNofail
def LockNofailProp : Prop := ∀ task body state, lockNofailM task body state = Locks.lockNofail task body state
theorem lockNofail_proven : LockNofailProp := by
  unfold LockNofailProp
  intros
  rfl

def lockableCtor := Locks.lockable
def LockableCtorProp : Prop := ∀ value, (lockableCtor value).value = value
theorem lockableCtor_proven : LockableCtorProp := by
  unfold LockableCtorProp
  intros
  rfl
def lockableGetM := Locks.lockableGet
def LockableGetProp : Prop := ∀ task lockable, lockableGetM task lockable = Locks.lockableGet task lockable
theorem lockableGet_proven : LockableGetProp := by
  unfold LockableGetProp
  intros
  rfl
def lockableDoM := Locks.lockableDo
def LockableDoProp : Prop := ∀ task body lockable,
  lockableDoM task body lockable = Locks.lockableDo task body lockable
theorem lockableDo_proven : LockableDoProp := by
  unfold LockableDoProp
  intros
  rfl
def lockableLockM := Locks.lockableLock
def LockableLockProp : Prop := ∀ task lockable, lockableLockM task lockable = Locks.lockableLock task lockable
theorem lockableLock_proven : LockableLockProp := by
  unfold LockableLockProp
  intros
  rfl
def lockableTrylockM := Locks.lockableTrylock
def LockableTrylockProp : Prop := ∀ task lockable,
  lockableTrylockM task lockable = Locks.lockableTrylock task lockable
theorem lockableTrylock_proven : LockableTrylockProp := by
  unfold LockableTrylockProp
  intros
  rfl
def lockableUnlockM := Locks.lockableUnlock
def LockableUnlockProp : Prop := ∀ task lockable,
  lockableUnlockM task lockable = Locks.lockableUnlock task lockable
theorem lockableUnlock_proven : LockableUnlockProp := by
  unfold LockableUnlockProp
  intros
  rfl

def semaphoreCtor := Locks.semaphore
def SemaphoreCtorProp : Prop := ∀ size, semaphoreCtor size = Locks.semaphore size
theorem semaphoreCtor_proven : SemaphoreCtorProp := by
  unfold SemaphoreCtorProp
  intros
  rfl
def semaphoreAcquire := Locks.acquire
def SemaphoreAcquireProp : Prop := ∀ sem, semaphoreAcquire sem = Locks.acquire sem
theorem semaphoreAcquire_proven : SemaphoreAcquireProp := by
  unfold SemaphoreAcquireProp
  intros
  rfl
def semaphoreAcquireDo := Locks.acquireDo
def SemaphoreAcquireDoProp : Prop := ∀ body sem,
  semaphoreAcquireDo body sem = Locks.acquireDo body sem
theorem semaphoreAcquireDo_proven : SemaphoreAcquireDoProp := by
  unfold SemaphoreAcquireDoProp
  intros
  rfl
def semaphoreMacro := Locks.acquireMacro
def SemaphoreMacroProp : Prop := ∀ body sem, semaphoreMacro body sem = Locks.acquireDo body sem
theorem semaphoreMacro_proven : SemaphoreMacroProp := by
  unfold SemaphoreMacroProp
  intros
  rfl
def semaphoreRelease := Locks.release
def SemaphoreReleaseProp : Prop := ∀ sem, semaphoreRelease sem = Locks.release sem
theorem semaphoreRelease_proven : SemaphoreReleaseProp := by
  unfold SemaphoreReleaseProp
  intros
  rfl

def eventCtor (autoreset : Bool) := Locks.event autoreset
def EventCtorProp : Prop := ∀ autoreset, eventCtor autoreset = ⟨autoreset, false⟩
theorem eventCtor_proven : EventCtorProp := by
  unfold EventCtorProp
  intros
  rfl
def eventWait (event : Locks.Event) : Bool × Locks.Event :=
  if event.set then (true, if event.autoreset then { event with set := false } else event)
  else (false, event)
def EventWaitProp : Prop := ∀ event, eventWait event =
  if event.set then (true, if event.autoreset then { event with set := false } else event) else (false, event)
theorem eventWait_proven : EventWaitProp := by
  unfold EventWaitProp
  intros
  rfl
def eventNotify (event : Locks.Event) := { event with set := true }
def EventNotifyProp : Prop := ∀ event, (eventNotify event).set = true
theorem eventNotify_proven : EventNotifyProp := by
  unfold EventNotifyProp
  intros
  rfl
def eventResetM := Locks.reset
def EventResetProp : Prop := ∀ event, (eventResetM event).set = false
theorem eventReset_proven : EventResetProp := by
  unfold EventResetProp
  intros
  rfl

structure ProcCtor where
  initializer : Nat
  cell : Locks.OnceProc
def procCtor (initializer : Nat) : ProcCtor := ⟨initializer, Locks.oncePerProcess⟩
def ProcCtorTFProp : Prop := ∀ init, (procCtor init).initializer = init
theorem procCtorTF_proven : ProcCtorTFProp := by
  unfold ProcCtorTFProp
  intros
  rfl
def ProcCtorTypeProp : Prop := ∀ init, (procCtor init).initializer = init
theorem procCtorType_proven : ProcCtorTypeProp := by
  unfold ProcCtorTypeProp
  intros
  rfl
def ProcCtorTProp : Prop := ∀ init, (procCtor init).initializer = init
theorem procCtorT_proven : ProcCtorTProp := by
  unfold ProcCtorTProp
  intros
  rfl
def ProcCtorAnyTypeProp : Prop := ∀ init, (procCtor init).initializer = init
theorem procCtorAnyType_proven : ProcCtorAnyTypeProp := by
  unfold ProcCtorAnyTypeProp
  intros
  rfl
def ProcCtorAnyProp : Prop := ∀ init, (procCtor init).initializer = init
theorem procCtorAny_proven : ProcCtorAnyProp := by
  unfold ProcCtorAnyProp
  intros
  rfl
def callProcM := Locks.callOnceProc
def CallProcProp : Prop := ∀ init cell, callProcM init cell = Locks.callOnceProc init cell
theorem callProc_proven : CallProcProp := by
  unfold CallProcProp
  intros
  rfl
def initProcM := Locks.initPerprocess
def InitProcProp : Prop := ∀ init state cell, initProcM init state cell = Locks.initPerprocess init state cell
theorem initProc_proven : InitProcProp := by
  unfold InitProcProp
  intros
  rfl
def copyMonotonicM := @Locks.copytoMonotonic
def CopyMonotonicProp : Prop := ∀ (α : Type) dest src,
  copyMonotonicM (α := α) dest src = Locks.copytoMonotonic dest src
theorem copyMonotonic_proven : CopyMonotonicProp := by
  unfold CopyMonotonicProp
  intros
  rfl
def fillMonotonicM := @Locks.fillMonotonic
def FillMonotonicProp : Prop := ∀ (α : Type) dest x,
  fillMonotonicM (α := α) dest x = Locks.fillMonotonic dest x
theorem fillMonotonic_proven : FillMonotonicProp := by
  unfold FillMonotonicProp
  intros
  rfl

structure ThreadCtor where
  initializer : Nat
  cell : Locks.OnceThread
def threadCtor (initializer : Nat) : ThreadCtor := ⟨initializer, Locks.oncePerThread⟩
def ThreadCtorTFProp : Prop := ∀ init, (threadCtor init).initializer = init
theorem threadCtorTF_proven : ThreadCtorTFProp := by
  unfold ThreadCtorTFProp
  intros
  rfl
def ThreadCtorTypeProp : Prop := ∀ init, (threadCtor init).initializer = init
theorem threadCtorType_proven : ThreadCtorTypeProp := by
  unfold ThreadCtorTypeProp
  intros
  rfl
def ThreadCtorTProp : Prop := ∀ init, (threadCtor init).initializer = init
theorem threadCtorT_proven : ThreadCtorTProp := by
  unfold ThreadCtorTProp
  intros
  rfl
def ThreadCtorAnyTypeProp : Prop := ∀ init, (threadCtor init).initializer = init
theorem threadCtorAnyType_proven : ThreadCtorAnyTypeProp := by
  unfold ThreadCtorAnyTypeProp
  intros
  rfl
def ThreadCtorAnyProp : Prop := ∀ init, (threadCtor init).initializer = init
theorem threadCtorAny_proven : ThreadCtorAnyProp := by
  unfold ThreadCtorAnyProp
  intros
  rfl
def callThreadM := Locks.callOnceThread
def CallThreadProp : Prop := ∀ init count tid cell,
  callThreadM init count tid cell = Locks.callOnceThread init count tid cell
theorem callThread_proven : CallThreadProp := by
  unfold CallThreadProp
  intros
  rfl
def threadGetM := Locks.onceThreadGet
def ThreadGetProp : Prop := ∀ init count tid cell,
  threadGetM init count tid cell = Locks.onceThreadGet init count tid cell
theorem threadGet_proven : ThreadGetProp := by
  unfold ThreadGetProp
  intros
  rfl
def initThreadM := Locks.onceThreadGet
def InitThreadProp : Prop := ∀ init count tid cell,
  initThreadM init count tid cell = Locks.onceThreadGet init count tid cell
theorem initThread_proven : InitThreadProp := by
  unfold InitThreadProp
  intros
  rfl

structure TaskCtor where
  initializer : Nat
  cell : Locks.OnceTask
def taskCtor (initializer : Nat) : TaskCtor := ⟨initializer, Locks.oncePerTask⟩
def TaskCtorTypeProp : Prop := ∀ init, (taskCtor init).initializer = init
theorem taskCtorType_proven : TaskCtorTypeProp := by
  unfold TaskCtorTypeProp
  intros
  rfl
def TaskCtorTProp : Prop := ∀ init, (taskCtor init).initializer = init
theorem taskCtorT_proven : TaskCtorTProp := by
  unfold TaskCtorTProp
  intros
  rfl
def TaskCtorTFProp : Prop := ∀ init, (taskCtor init).initializer = init
theorem taskCtorTF_proven : TaskCtorTFProp := by
  unfold TaskCtorTFProp
  intros
  rfl
def TaskCtorAnyTypeProp : Prop := ∀ init, (taskCtor init).initializer = init
theorem taskCtorAnyType_proven : TaskCtorAnyTypeProp := by
  unfold TaskCtorAnyTypeProp
  intros
  rfl
def TaskCtorAnyProp : Prop := ∀ init, (taskCtor init).initializer = init
theorem taskCtorAny_proven : TaskCtorAnyProp := by
  unfold TaskCtorAnyProp
  intros
  rfl
def callTaskM := Locks.callOnceTask
def CallTaskProp : Prop := ∀ init task cell, callTaskM init task cell = Locks.callOnceTask init task cell
theorem callTask_proven : CallTaskProp := by
  unfold CallTaskProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulLock
