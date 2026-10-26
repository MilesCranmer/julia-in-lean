import JuliaLean.ConcurrencyCov.ParkProps

/-! Per-method source-body models for `base/park.jl`. -/

namespace JuliaLean.ConcurrencyCov.FaithfulPark

open JuliaLean.ConcurrencyCov

def waitRecheckDefault (object entry : Nat) (s : Park.St) := Park.waitRecheck (.obj object false) entry s
def WaitRecheckDefaultProp : Prop := ∀ object entry s, waitRecheckDefault object entry s = false
theorem waitRecheckDefault_proven : WaitRecheckDefaultProp := by
  unfold WaitRecheckDefaultProp
  intros
  rfl

def uncancellableLock (lock : Nat → Nat) (l : Nat) := Park.uncancellableLock lock l
def UncancellableLockProp : Prop := ∀ lock l, uncancellableLock lock l = lock l
theorem uncancellableLock_proven : UncancellableLockProp := by
  unfold UncancellableLockProp
  intros
  rfl

def acquireTupleOne (x : Park.Waitable) := match x with
  | .watcher _ _ => Park.newEntry 1 | _ => Park.cachedWaitEntry
def AcquireTupleOneProp : Prop := ∀ x, acquireTupleOne x = Park.acquireWaitEntry [x] true
theorem acquireTupleOne_proven : AcquireTupleOneProp := by intro x; cases x <;> rfl

def acquireTupleSource (x : Park.Waitable) (src floor : Nat) := match x with
  | .watcher _ _ => Park.newEntry 2 | _ => Park.cancelWaitEntry src floor
def AcquireTupleSourceProp : Prop := ∀ x src floor,
  acquireTupleSource x src floor = Park.acquireWaitEntry [x, .source src floor] true
theorem acquireTupleSource_proven : AcquireTupleSourceProp := by
  intro x src floor
  cases x <;> rfl

def acquireGeneric (ws : List Park.Waitable) := Park.newEntry ws.length
def AcquireGenericProp : Prop := ∀ ws, acquireGeneric ws = Park.acquireWaitEntry ws false
theorem acquireGeneric_proven : AcquireGenericProp := by intro ws; cases ws <;> rfl

def releaseWaitEntryM := Park.releaseWaitEntry
def ReleaseWaitEntryProp : Prop := ∀ w s, releaseWaitEntryM w s = Park.releaseWaitEntry w s
theorem releaseWaitEntry_proven : ReleaseWaitEntryProp := by
  unfold ReleaseWaitEntryProp
  intros
  rfl

def disarmM := Park.disarm
def DisarmProp : Prop := ∀ w s, disarmM w s =
  if s.waitingOn = some w then (true, { s with waitingOn := none }) else (false, s)
theorem disarm_proven : DisarmProp := by
  unfold DisarmProp
  intros
  rfl

def parkM := Park.park
def ParkProp : Prop := ∀ ws w first claimed, parkM ws w first claimed = Park.park ws w first claimed
theorem park_proven : ParkProp := by
  unfold ParkProp
  intros
  rfl

def enqueueEmpty (w : Nat) (first : Bool) := Park.enqueueUntilFired [] w first
def EnqueueEmptyProp : Prop := ∀ w first, enqueueEmpty w first = pure none
theorem enqueueEmpty_proven : EnqueueEmptyProp := by
  unfold EnqueueEmptyProp
  intros
  rfl

def enqueueTuple (ws : List Park.Waitable) (w : Nat) (first : Bool) := Park.enqueueUntilFired ws w first
def EnqueueTupleProp : Prop := ∀ ws w first, enqueueTuple ws w first = Park.enqueueUntilFired ws w first
theorem enqueueTuple_proven : EnqueueTupleProp := by
  unfold EnqueueTupleProp
  intros
  rfl

def enqueueGeneric (ws : List Park.Waitable) (w : Nat) (first : Bool) := Park.enqueueUntilFired ws w first
def EnqueueGenericProp : Prop := ∀ ws w first, enqueueGeneric ws w first = Park.enqueueUntilFired ws w first
theorem enqueueGeneric_proven : EnqueueGenericProp := by
  unfold EnqueueGenericProp
  intros
  rfl

def recheckEmpty (w : Nat) (s : Park.St) := Park.recheckUntilFired [] w s
def RecheckEmptyProp : Prop := ∀ w s, recheckEmpty w s = none
theorem recheckEmpty_proven : RecheckEmptyProp := by
  unfold RecheckEmptyProp
  intros
  rfl

def recheckTuple (ws : List Park.Waitable) (w : Nat) (s : Park.St) := Park.recheckUntilFired ws w s
def RecheckTupleProp : Prop := ∀ ws w s, recheckTuple ws w s = Park.recheckUntilFired ws w s
theorem recheckTuple_proven : RecheckTupleProp := by
  unfold RecheckTupleProp
  intros
  rfl

def recheckGeneric (ws : List Park.Waitable) (w : Nat) (s : Park.St) := Park.recheckUntilFired ws w s
def RecheckGenericProp : Prop := ∀ ws w s, recheckGeneric ws w s = Park.recheckUntilFired ws w s
theorem recheckGeneric_proven : RecheckGenericProp := by
  unfold RecheckGenericProp
  intros
  rfl

def dequeueEmpty (w why : Nat) (s : Park.St) := Park.dequeueEach [] w why s
def DequeueEmptyProp : Prop := ∀ w why s, dequeueEmpty w why s = s
theorem dequeueEmpty_proven : DequeueEmptyProp := by
  unfold DequeueEmptyProp
  intros
  rfl

def dequeueTuple (ws : List Park.Waitable) (w why : Nat) (s : Park.St) := Park.dequeueEach ws w why s
def DequeueTupleProp : Prop := ∀ ws w why s, dequeueTuple ws w why s = Park.dequeueEach ws w why s
theorem dequeueTuple_proven : DequeueTupleProp := by
  unfold DequeueTupleProp
  intros
  rfl

def dequeueGeneric (ws : List Park.Waitable) (w why : Nat) (s : Park.St) := Park.dequeueEach ws w why s
def DequeueGenericProp : Prop := ∀ ws w why s, dequeueGeneric ws w why s = Park.dequeueEach ws w why s
theorem dequeueGeneric_proven : DequeueGenericProp := by
  unfold DequeueGenericProp
  intros
  rfl

def reparkM := Park.repark
def ReparkProp : Prop := ∀ ws w claimed, reparkM ws w claimed = Park.repark ws w claimed
theorem repark_proven : ReparkProp := by
  unfold ReparkProp
  intros
  rfl

def waitSafeInterruptM := Park.waitSafeInterrupt
def WaitSafeInterruptProp : Prop := ∀ ws w wake nested,
  waitSafeInterruptM ws w wake nested = Park.waitSafeInterrupt ws w wake nested
theorem waitSafeInterrupt_proven : WaitSafeInterruptProp := by
  unfold WaitSafeInterruptProp
  intros
  rfl

def withdrawM := Park.withdraw
def WithdrawProp : Prop := ∀ ws w why s, withdrawM ws w why s = Park.releaseWaitEntry w (Park.dequeueEach ws w why s)
theorem withdraw_proven : WithdrawProp := by
  unfold WithdrawProp
  intros
  rfl

def interruptedCleanupM := Park.interruptedParkCleanup
def InterruptedCleanupProp : Prop := ∀ ws w nested s,
  interruptedCleanupM ws w nested s = Park.interruptedParkCleanup ws w nested s
theorem interruptedCleanup_proven : InterruptedCleanupProp := by
  unfold InterruptedCleanupProp
  intros
  rfl

def sourceWaitEnqueueM := Park.sourceWaitEnqueue
def SourceWaitEnqueueProp : Prop := ∀ src w aux,
  sourceWaitEnqueueM src w aux = Park.sourceWaitEnqueue src w aux
theorem sourceWaitEnqueue_proven : SourceWaitEnqueueProp := by
  unfold SourceWaitEnqueueProp
  intros
  rfl

def sourceWaitEnqueue (src floor w : Nat) (first : Bool) := Park.waitEnqueue (.source src floor) w first
def SourceWaitEnqueueMethodProp : Prop := ∀ src floor w first,
  sourceWaitEnqueue src floor w first = Park.sourceWaitEnqueue src w floor
theorem sourceWaitEnqueueMethod_proven : SourceWaitEnqueueMethodProp := by
  unfold SourceWaitEnqueueMethodProp
  intros
  rfl

def sourceWaitRecheck (src floor w : Nat) (s : Park.St) := Park.waitRecheck (.source src floor) w s
def SourceWaitRecheckProp : Prop := ∀ src floor w s,
  sourceWaitRecheck src floor w s = (s.srcState src ≠ 0 && s.srcState src ≥ floor)
theorem sourceWaitRecheck_proven : SourceWaitRecheckProp := by
  unfold SourceWaitRecheckProp
  intros
  rfl

def sourceWaitDequeue (src floor w why : Nat) (s : Park.St) := Park.waitDequeue (.source src floor) w why s
def SourceWaitDequeueProp : Prop := ∀ src floor w why s, sourceWaitDequeue src floor w why s = s
theorem sourceWaitDequeue_proven : SourceWaitDequeueProp := by
  unfold SourceWaitDequeueProp
  intros
  rfl

def watcherWaitM := Park.watcherWait
def WatcherWaitProp : Prop := ∀ src, watcherWaitM src = .watcher src Park.SAFE
theorem watcherWait_proven : WatcherWaitProp := by
  unfold WatcherWaitProp
  intros
  rfl

def acquireWatcherOne (src floor : Nat) := Park.newEntry 1
def AcquireWatcherOneProp : Prop := ∀ src floor,
  acquireWatcherOne src floor = Park.acquireWaitEntry [.watcher src floor] true
theorem acquireWatcherOne_proven : AcquireWatcherOneProp := by
  unfold AcquireWatcherOneProp
  intros
  rfl

def acquireWatcherSource (src floor gov minSev : Nat) := Park.newEntry 2
def AcquireWatcherSourceProp : Prop := ∀ src floor gov minSev,
  acquireWatcherSource src floor gov minSev =
    Park.acquireWaitEntry [.watcher src floor, .source gov minSev] true
theorem acquireWatcherSource_proven : AcquireWatcherSourceProp := by
  unfold AcquireWatcherSourceProp
  intros
  rfl

def watcherEnqueue (src floor w : Nat) (first : Bool) := Park.waitEnqueue (.watcher src floor) w first
def WatcherEnqueueProp : Prop := ∀ src floor w first,
  watcherEnqueue src floor w first = Park.sourceWaitEnqueue src w (Park.WATCHER_BIT ||| max floor Park.SAFE)
theorem watcherEnqueue_proven : WatcherEnqueueProp := by
  unfold WatcherEnqueueProp
  intros
  rfl

def watcherRecheck (src floor w : Nat) (s : Park.St) := Park.waitRecheck (.watcher src floor) w s
def WatcherRecheckProp : Prop := ∀ src floor w s,
  watcherRecheck src floor w s = decide (s.srcState src ≥ max floor Park.SAFE)
theorem watcherRecheck_proven : WatcherRecheckProp := by
  unfold WatcherRecheckProp
  intros
  rfl

def watcherDequeue (src floor w why : Nat) (s : Park.St) := Park.waitDequeue (.watcher src floor) w why s
def WatcherDequeueProp : Prop := ∀ src floor w why s, watcherDequeue src floor w why s = s
theorem watcherDequeue_proven : WatcherDequeueProp := by
  unfold WatcherDequeueProp
  intros
  rfl

def waitTokenM := Park.waitToken
def WaitTokenProp : Prop := ∀ src gov claimed wake nested,
  waitTokenM src gov claimed wake nested = Park.waitToken src gov claimed wake nested
theorem waitToken_proven : WaitTokenProp := by
  unfold WaitTokenProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulPark
