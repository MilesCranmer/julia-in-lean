import JuliaLean.base.park
import JuliaLean.Proofs.base.park.properties

/-! Per-method source-body models for `base/park.jl`. -/

namespace JuliaLean.ConcurrencyCov.FaithfulPark

open JuliaLean.ConcurrencyCov

def WaitRecheckDefaultProp : Prop := ∀ object entry s, waitRecheckDefault object entry s = false
theorem waitRecheckDefault_proven : WaitRecheckDefaultProp := by
  unfold WaitRecheckDefaultProp
  intros
  rfl

def UncancellableLockProp : Prop := ∀ lock l, uncancellableLock lock l = lock l
theorem uncancellableLock_proven : UncancellableLockProp := by
  unfold UncancellableLockProp
  intros
  rfl

def AcquireTupleOneProp : Prop := ∀ x, acquireTupleOne x = Park.acquireWaitEntry [x] true
theorem acquireTupleOne_proven : AcquireTupleOneProp := by intro x; cases x <;> rfl

def AcquireTupleSourceProp : Prop := ∀ x src floor,
  acquireTupleSource x src floor = Park.acquireWaitEntry [x, .source src floor] true
theorem acquireTupleSource_proven : AcquireTupleSourceProp := by
  intro x src floor
  cases x <;> rfl

def AcquireGenericProp : Prop := ∀ ws, acquireGeneric ws = Park.acquireWaitEntry ws false
theorem acquireGeneric_proven : AcquireGenericProp := by intro ws; cases ws <;> rfl

def ReleaseWaitEntryProp : Prop := ∀ w s, releaseWaitEntryM w s = Park.releaseWaitEntry w s
theorem releaseWaitEntry_proven : ReleaseWaitEntryProp := by
  unfold ReleaseWaitEntryProp
  intros
  rfl

def DisarmProp : Prop := ∀ w s, disarmM w s =
  if s.waitingOn = some w then (true, { s with waitingOn := none }) else (false, s)
theorem disarm_proven : DisarmProp := by
  unfold DisarmProp
  intros
  rfl

def ParkProp : Prop := ∀ ws w first claimed, parkM ws w first claimed = Park.park ws w first claimed
theorem park_proven : ParkProp := by
  unfold ParkProp
  intros
  rfl

def EnqueueEmptyProp : Prop := ∀ w first, enqueueEmpty w first = pure none
theorem enqueueEmpty_proven : EnqueueEmptyProp := by
  unfold EnqueueEmptyProp
  intros
  rfl

def EnqueueTupleProp : Prop := ∀ ws w first, enqueueTuple ws w first = Park.enqueueUntilFired ws w first
theorem enqueueTuple_proven : EnqueueTupleProp := by
  unfold EnqueueTupleProp
  intros
  rfl

def EnqueueGenericProp : Prop := ∀ ws w first, enqueueGeneric ws w first = Park.enqueueUntilFired ws w first
theorem enqueueGeneric_proven : EnqueueGenericProp := by
  unfold EnqueueGenericProp
  intros
  rfl

def RecheckEmptyProp : Prop := ∀ w s, recheckEmpty w s = none
theorem recheckEmpty_proven : RecheckEmptyProp := by
  unfold RecheckEmptyProp
  intros
  rfl

def RecheckTupleProp : Prop := ∀ ws w s, recheckTuple ws w s = Park.recheckUntilFired ws w s
theorem recheckTuple_proven : RecheckTupleProp := by
  unfold RecheckTupleProp
  intros
  rfl

def RecheckGenericProp : Prop := ∀ ws w s, recheckGeneric ws w s = Park.recheckUntilFired ws w s
theorem recheckGeneric_proven : RecheckGenericProp := by
  unfold RecheckGenericProp
  intros
  rfl

def DequeueEmptyProp : Prop := ∀ w why s, dequeueEmpty w why s = s
theorem dequeueEmpty_proven : DequeueEmptyProp := by
  unfold DequeueEmptyProp
  intros
  rfl

def DequeueTupleProp : Prop := ∀ ws w why s, dequeueTuple ws w why s = Park.dequeueEach ws w why s
theorem dequeueTuple_proven : DequeueTupleProp := by
  unfold DequeueTupleProp
  intros
  rfl

def DequeueGenericProp : Prop := ∀ ws w why s, dequeueGeneric ws w why s = Park.dequeueEach ws w why s
theorem dequeueGeneric_proven : DequeueGenericProp := by
  unfold DequeueGenericProp
  intros
  rfl

def ReparkProp : Prop := ∀ ws w claimed, reparkM ws w claimed = Park.repark ws w claimed
theorem repark_proven : ReparkProp := by
  unfold ReparkProp
  intros
  rfl

def WaitSafeInterruptProp : Prop := ∀ ws w wake nested,
  waitSafeInterruptM ws w wake nested = Park.waitSafeInterrupt ws w wake nested
theorem waitSafeInterrupt_proven : WaitSafeInterruptProp := by
  unfold WaitSafeInterruptProp
  intros
  rfl

def WithdrawProp : Prop := ∀ ws w why s, withdrawM ws w why s = Park.releaseWaitEntry w (Park.dequeueEach ws w why s)
theorem withdraw_proven : WithdrawProp := by
  unfold WithdrawProp
  intros
  rfl

def InterruptedCleanupProp : Prop := ∀ ws w nested s,
  interruptedCleanupM ws w nested s = Park.interruptedParkCleanup ws w nested s
theorem interruptedCleanup_proven : InterruptedCleanupProp := by
  unfold InterruptedCleanupProp
  intros
  rfl

def SourceWaitEnqueueProp : Prop := ∀ src w aux,
  sourceWaitEnqueueM src w aux = Park.sourceWaitEnqueue src w aux
theorem sourceWaitEnqueue_proven : SourceWaitEnqueueProp := by
  unfold SourceWaitEnqueueProp
  intros
  rfl

def SourceWaitEnqueueMethodProp : Prop := ∀ src floor w first,
  sourceWaitEnqueue src floor w first = Park.sourceWaitEnqueue src w floor
theorem sourceWaitEnqueueMethod_proven : SourceWaitEnqueueMethodProp := by
  unfold SourceWaitEnqueueMethodProp
  intros
  rfl

def SourceWaitRecheckProp : Prop := ∀ src floor w s,
  sourceWaitRecheck src floor w s = (s.srcState src ≠ 0 && s.srcState src ≥ floor)
theorem sourceWaitRecheck_proven : SourceWaitRecheckProp := by
  unfold SourceWaitRecheckProp
  intros
  rfl

def SourceWaitDequeueProp : Prop := ∀ src floor w why s, sourceWaitDequeue src floor w why s = s
theorem sourceWaitDequeue_proven : SourceWaitDequeueProp := by
  unfold SourceWaitDequeueProp
  intros
  rfl

def WatcherWaitProp : Prop := ∀ src, watcherWaitM src = .watcher src Park.SAFE
theorem watcherWait_proven : WatcherWaitProp := by
  unfold WatcherWaitProp
  intros
  rfl

def AcquireWatcherOneProp : Prop := ∀ src floor,
  acquireWatcherOne src floor = Park.acquireWaitEntry [.watcher src floor] true
theorem acquireWatcherOne_proven : AcquireWatcherOneProp := by
  unfold AcquireWatcherOneProp
  intros
  rfl

def AcquireWatcherSourceProp : Prop := ∀ src floor gov minSev,
  acquireWatcherSource src floor gov minSev =
    Park.acquireWaitEntry [.watcher src floor, .source gov minSev] true
theorem acquireWatcherSource_proven : AcquireWatcherSourceProp := by
  unfold AcquireWatcherSourceProp
  intros
  rfl

def WatcherEnqueueProp : Prop := ∀ src floor w first,
  watcherEnqueue src floor w first = Park.sourceWaitEnqueue src w (Park.WATCHER_BIT ||| max floor Park.SAFE)
theorem watcherEnqueue_proven : WatcherEnqueueProp := by
  unfold WatcherEnqueueProp
  intros
  rfl

def WatcherRecheckProp : Prop := ∀ src floor w s,
  watcherRecheck src floor w s = decide (s.srcState src ≥ max floor Park.SAFE)
theorem watcherRecheck_proven : WatcherRecheckProp := by
  unfold WatcherRecheckProp
  intros
  rfl

def WatcherDequeueProp : Prop := ∀ src floor w why s, watcherDequeue src floor w why s = s
theorem watcherDequeue_proven : WatcherDequeueProp := by
  unfold WatcherDequeueProp
  intros
  rfl

def WaitTokenProp : Prop := ∀ src gov claimed wake nested,
  waitTokenM src gov claimed wake nested = Park.waitToken src gov claimed wake nested
theorem waitToken_proven : WaitTokenProp := by
  unfold WaitTokenProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulPark
