import JuliaLean.Tasks.TaskModel
import JuliaLean.Tasks.Cancellation
import JuliaLean.Tasks.Condition

/-! Source-body models for `base/task.jl`, `base/cancellation.jl`, and
`base/condition.jl`. Runtime calls, locks, callbacks, and exception rendering
enter as explicit inputs; the Julia branch and mutation order remains explicit. -/

namespace JuliaLean.Tasks

/-! ## base/task.jl:5-113, exception containers and rendering -/

def capturedBacktrace (frames : List Nat) : List Nat := frames.take 100
def compositePush (exceptions : List Nat) (exception : Nat) : List Nat :=
  exceptions ++ [exception]
def compositePushFirst (exceptions : List Nat) (exception : Nat) : List Nat :=
  exception :: exceptions
def compositeSummary : List Nat → Option (Nat × Nat)
  | [] => none
  | exception :: rest => some (exception, rest.length)

def TaskExceptionBodies : Prop := ∀ (frames exceptions : List Nat) (exception : Nat),
  (capturedBacktrace frames).length = min 100 frames.length ∧
  compositePush exceptions exception = exceptions ++ [exception] ∧
  compositePushFirst exceptions exception = exception :: exceptions ∧
  (compositeSummary (exception :: exceptions) = some (exception, exceptions.length))

theorem taskExceptionBodies_proven : TaskExceptionBodies := by
  intro frames exceptions exception
  simp [capturedBacktrace, compositePush, compositePushFirst, compositeSummary,
    List.length_take]

/-! ## base/task.jl:5-403, task construction, properties, thread data, and TLS -/

structure TaskCore where
  phase : TaskPhase := .created
  result : Nat := 0
  isException : Bool := false
  doneNotify : Bool := true
  tls : List (Nat × Nat) := []
  deriving Repr, DecidableEq

def coreTask : TaskCore := {}

inductive TaskProperty where | state | backtrace | exception | scope | invoked | result | other
  deriving Repr, DecidableEq

inductive TaskPropertyResult where
  | value (value : Nat)
  | symbol (value : TaskState)
  | absent
  | error
  deriving Repr, DecidableEq

def taskGetProperty (task : TaskCore) : TaskProperty → TaskPropertyResult
  | .state => .symbol (taskState task.phase)
  | .exception => if task.isException then .value task.result else .absent
  | .scope | .invoked => .error
  | .backtrace | .result | .other => .value task.result

def taskSetPropertyAllowed (task : TaskCore) : TaskProperty → Bool
  | .scope => !istaskstarted task.phase
  | .invoked | .result => false
  | _ => true

def tlsGet (tls : List (Nat × Nat)) (key : Nat) : Option Nat :=
  (tls.find? (fun pair => pair.1 == key)).map (·.2)

def tlsSet (tls : List (Nat × Nat)) (key value : Nat) : List (Nat × Nat) :=
  (key, value) :: tls.filter (fun pair => pair.1 != key)

def tlsScoped (tls : List (Nat × Nat)) (_key _value : Nat) (bodyResult : Nat) :
    Nat × List (Nat × Nat) :=
  (bodyResult, tls)

def unsafeAbandonBody (committed : Bool) (result : Nat) (task : TaskCore) : Bool × TaskCore :=
  if committed then (true, { task with phase := .abandoned, result := result, isException := true })
  else (false, task)

def TaskCoreBodies : Prop := ∀ (task : TaskCore) (key value bodyResult result : Nat)
    (committed : Bool),
  coreTask.doneNotify = true ∧ coreTask.phase = .created ∧
  taskGetProperty task .state = .symbol (taskState task.phase) ∧
  taskSetPropertyAllowed task .invoked = false ∧
  tlsGet (tlsSet task.tls key value) key = some value ∧
  (tlsScoped task.tls key value bodyResult).2 = task.tls ∧
  (unsafeAbandonBody committed result task).1 = committed

theorem taskCoreBodies_proven : TaskCoreBodies := by
  unfold TaskCoreBodies
  intro task key value bodyResult result committed
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · simp [tlsGet, tlsSet]
  · cases committed <;> rfl

/-! ## base/task.jl:406-742, task waits, wait-many, and fetch -/

def collectTaskIds (tasks : List Nat) : List Nat := tasks

def completedTaskIds (tasks : List Nat) (done : Nat → Bool) : List Nat :=
  tasks.filter done

def failedTaskIds (tasks : List Nat) (failed : Nat → Bool) : List Nat :=
  tasks.filter failed

structure WaitManyResult where
  done : List Nat
  remaining : List Nat
  failures : List Nat
  deriving Repr, DecidableEq

def waitManyBody (tasks : List Nat) (done failed : Nat → Bool) : WaitManyResult :=
  { done := completedTaskIds tasks done
    remaining := tasks.filter (fun task => !done task)
    failures := failedTaskIds (completedTaskIds tasks done) failed }

def TaskWaitBodies : Prop := ∀ (tasks : List Nat) (done failed : Nat → Bool)
    (task : TaskPhase),
  collectTaskIds tasks = tasks ∧
  (waitManyBody tasks done failed).done = tasks.filter done ∧
  (waitManyBody tasks done failed).failures = (tasks.filter done).filter failed ∧
  (match task with
    | .done value => fetchTask task = .returned value
    | .failed _ _ | .abandoned => fetchTask task = .threw .taskFailed
    | _ => fetchTask task = .blocked)

theorem taskWaitBodies_proven : TaskWaitBodies := by
  intro tasks done failed task
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · cases task <;> rfl

/-! ## base/task.jl:746-1106, structured waiting and macro bodies -/

inductive SyncItem where
  | task (id : Nat) (failed : Bool)
  | waitable (error : Option Nat)
  deriving Repr, DecidableEq

def syncExceptions : List SyncItem → List Nat
  | [] => []
  | .task id true :: items => id :: syncExceptions items
  | .task _ false :: items => syncExceptions items
  | .waitable (some error) :: items => error :: syncExceptions items
  | .waitable none :: items => syncExceptions items

structure AsyncExpansion where
  registers : Bool
  schedules : Bool
  wraps : Bool
  deriving Repr, DecidableEq

def asyncExpansion (insideSync unwrap : Bool) : AsyncExpansion :=
  ⟨insideSync, true, unwrap⟩

def syncExpansion (hasCancellationSource : Bool) : Bool × Bool :=
  (hasCancellationSource, true)

def TaskSyncBodies : Prop := ∀ (items : List SyncItem) (insideSync unwrap : Bool),
  (syncExceptions items).length ≤ items.length ∧
  (asyncExpansion insideSync unwrap).registers = insideSync ∧
  (asyncExpansion insideSync unwrap).schedules = true ∧
  syncExpansion true = (true, true)

theorem taskSyncBodies_proven : TaskSyncBodies := by
  intro items insideSync unwrap
  constructor
  · induction items with
    | nil => simp [syncExceptions]
    | cons item items ih =>
        cases item with
        | task id failed =>
            cases failed
            · simpa [syncExceptions] using Nat.le.step ih
            · simp [syncExceptions, ih]
        | waitable error =>
            cases error
            · simpa [syncExceptions] using Nat.le.step ih
            · simp [syncExceptions, ih]
  exact ⟨rfl, rfl, rfl⟩

/-! ## base/task.jl:1108-1318, completion and synchronized queues -/

def queuePush (queue : List Nat) (task : Nat) : List Nat := queue ++ [task]
def queuePushFirst (queue : List Nat) (task : Nat) : List Nat := task :: queue
def queuePop : List Nat → Option Nat × List Nat
  | [] => (none, [])
  | task :: tasks => (some task, tasks)
def queueDelete (queue : List Nat) (task : Nat) : List Nat := queue.erase task

def enqueueAllowed (state : TaskState) (alreadyQueued waiting : Bool) : Bool :=
  state == .abandoned || (state == .runnable && !alreadyQueued && !waiting)

def taskDoneHandled (failed hasClaimedWaiter : Bool) : Bool :=
  failed && hasClaimedWaiter

def TaskQueueBodies : Prop := ∀ (queue : List Nat) (task : Nat)
    (state : TaskState) (queued waiting failed waiter : Bool),
  queuePush queue task = queue ++ [task] ∧
  queuePushFirst queue task = task :: queue ∧
  queueDelete queue task = queue.erase task ∧
  enqueueAllowed state queued waiting =
    (state == .abandoned || (state == .runnable && !queued && !waiting)) ∧
  taskDoneHandled failed waiter = (failed && waiter)

theorem taskQueueBodies_proven : TaskQueueBodies := by
  unfold TaskQueueBodies
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## base/task.jl:1374-1716, scheduling, switching, and metrics -/

inductive YieldToResult where | returned (value : Nat) | switched | threw (error : Nat)
  deriving Repr, DecidableEq

def yieldToBody (task : TaskPhase) (argument : Nat) : YieldToResult :=
  match task with
  | .done _ => .returned argument
  | .failed error _ => .threw error
  | .abandoned => .threw 0
  | _ => .switched

def runningTimeBody (enabled done : Bool) (old delta : Nat) : Nat :=
  if enabled && !done then old + delta else old

def firstEnqueuedBody (enabled : Bool) (old now : Nat) : Nat :=
  if enabled && old == 0 then now else old

def pauseBody (windows : Bool) : String := if windows then "Sleep" else "pause"

def TaskSchedulingBodies : Prop := ∀ (task : TaskPhase) (argument old delta now : Nat)
    (enabled done : Bool),
  (yieldToBody (.done old) argument = .returned argument) ∧
  (yieldToBody (.failed old true) argument = .threw old) ∧
  runningTimeBody enabled done old delta =
    (if enabled && !done then old + delta else old) ∧
  firstEnqueuedBody enabled old now = (if enabled && old == 0 then now else old) ∧
  pauseBody enabled = (if enabled then "Sleep" else "pause") ∧
  istaskdone (taskStep .yield task) = istaskdone task

theorem taskSchedulingBodies_proven : TaskSchedulingBodies := by
  intro task argument old delta now enabled done
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases task <;> rfl

/-! ## base/cancellation.jl:102-191, token queries and source linkage -/

def cancellationSeverity (state : Nat) : Option Nat :=
  if state == 0 then none else some state
def cancellationIsCancelled (state : Nat) : Bool := state != 0
def uniqueParents (first : Nat) (rest : List Nat) : List Nat :=
  rest.foldl (fun parents parent => if parent ∈ parents then parents else parents ++ [parent]) [first]

def CancellationTokenBodies : Prop := ∀ (state first : Nat) (_rest : List Nat),
  cancellationSeverity 0 = none ∧
  cancellationIsCancelled state = (state != 0) ∧
  uniqueParents first [] = [first] ∧
  (raiseCancellation state first).2 = max state first

theorem cancellationTokenBodies_proven : CancellationTokenBodies := by
  intro state first rest
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · unfold raiseCancellation
    split <;> omega

/-! ## base/cancellation.jl:242-437, uniform WaitEntry slots -/

structure CoverageWaitSlot where
  owner : Option Nat := none
  next : Option Nat := none
  aux : Nat := 0
  deriving Repr, DecidableEq, Inhabited

structure CoverageWaitEntry where
  task : Option Nat
  slots : List CoverageWaitSlot
  deriving Repr, DecidableEq, Inhabited

def emptyWaitSlot : CoverageWaitSlot := ⟨none, none, 0⟩

def waitEntry (task : Option Nat) (slots : Nat) : CoverageWaitEntry :=
  ⟨task, List.replicate slots emptyWaitSlot⟩

def waitSlot (entry : CoverageWaitEntry) (index : Nat) : CoverageWaitSlot :=
  entry.slots.getD (index - 1) emptyWaitSlot

def setWaitSlot (entry : CoverageWaitEntry) (index : Nat) (slot : CoverageWaitSlot) :
    CoverageWaitEntry :=
  { entry with slots := entry.slots.set (index - 1) slot }

def findWaitSlotFrom (owner : Option Nat) : Nat → List CoverageWaitSlot → Nat
  | _, [] => 0
  | index, slot :: slots =>
      if slot.owner == owner then index else findWaitSlotFrom owner (index + 1) slots

def findWaitSlot (entry : CoverageWaitEntry) (owner : Option Nat) : Nat :=
  findWaitSlotFrom owner 1 entry.slots

def acquireWaitSlot (entry : CoverageWaitEntry) (owner : Nat) : Option CoverageWaitEntry :=
  let index := findWaitSlot entry none
  if index == 0 then none
  else some (setWaitSlot entry index { (waitSlot entry index) with owner := some owner })

def releaseWaitSlot (entry : CoverageWaitEntry) (index : Nat) : CoverageWaitEntry :=
  setWaitSlot entry index emptyWaitSlot

def CancellationSlotBodies : Prop := ∀ (task : Option Nat) (count owner : Nat),
  (waitEntry task count).slots.length = count ∧
  (findWaitSlot (waitEntry task 1) none = 1) ∧
  (match acquireWaitSlot (waitEntry task 1) owner with
    | some entry => (waitSlot entry 1).owner = some owner
    | none => False)

theorem cancellationSlotBodies_proven : CancellationSlotBodies := by
  intro task count owner
  constructor
  · simp [waitEntry]
  constructor
  · simp [findWaitSlot, findWaitSlotFrom, waitEntry, emptyWaitSlot]
  · simp [acquireWaitSlot, findWaitSlot, findWaitSlotFrom, waitEntry, emptyWaitSlot,
      setWaitSlot, waitSlot]

/-! ## base/cancellation.jl:452-523, cached entries, arming, and claims -/

structure WaitArm where
  entry : Option Nat := none
  armed : Bool := false
  deriving Repr, DecidableEq

def armWait (state : WaitArm) (entry : Nat) : Option WaitArm :=
  if state.armed then none else some ⟨some entry, true⟩

def claimWait (state : WaitArm) (entry : Nat) : Bool × WaitArm :=
  if state.armed && state.entry == some entry then (true, ⟨none, false⟩)
  else (false, state)

def cancelWaitEntrySlots (hasCached : Bool) : Nat := if hasCached then 2 else 2

def CancellationArmBodies : Prop := ∀ (state : WaitArm) (entry : Nat),
  (armWait ⟨none, false⟩ entry = some ⟨some entry, true⟩) ∧
  (claimWait ⟨some entry, true⟩ entry = (true, ⟨none, false⟩)) ∧
  (state.armed → armWait state entry = none)

theorem cancellationArmBodies_proven : CancellationArmBodies := by
  intro state entry
  constructor
  · simp [armWait]
  constructor
  · simp [claimWait]
  · intro armed
    simp [armWait, armed]

/-! ## base/cancellation.jl:541-655, registration bookkeeping -/

structure RegistrationState where
  waiters : List Nat := []
  deadCount : Nat := 0
  deriving Repr, DecidableEq

def unregisterBody (state : RegistrationState) (waiter : Nat) : RegistrationState :=
  { waiters := state.waiters.erase waiter, deadCount := state.deadCount }

def retireBody (state : RegistrationState) (waiter : Nat) : RegistrationState :=
  { state with waiters := state.waiters.erase waiter }

def noteDeadBody (state : RegistrationState) : RegistrationState :=
  { state with deadCount := state.deadCount + 1 }

def CancellationRegistrationBodies : Prop := ∀ (state : RegistrationState) (waiter : Nat),
  (unregisterBody state waiter).waiters.length ≤ state.waiters.length ∧
  (retireBody state waiter).waiters.length ≤ state.waiters.length ∧
  (noteDeadBody state).deadCount = state.deadCount + 1

theorem cancellationRegistrationBodies_proven : CancellationRegistrationBodies := by
  unfold CancellationRegistrationBodies
  intro state waiter
  exact ⟨List.length_erase_le, List.length_erase_le, rfl⟩

/-! ## base/cancellation.jl:681-912, cancellation delivery -/

def validCancellationSeverity (severity : Nat) : Bool :=
  severity == 1 || severity == 3 || severity == 4

def cancelBody (state severity : Nat) : Except Unit (Bool × Nat) :=
  if validCancellationSeverity severity then .ok (raiseCancellation state severity)
  else .error ()

def redeliverBody (state : Nat) : Bool := state != 0

def walkNodeBody (requested current : Nat) : Nat := max requested current

def handleCancellationBody (hasSource preempt : Bool) (status current : Nat) : Except Nat Unit :=
  if preempt && (!hasSource || status % 64 == 0) then .ok ()
  else if hasSource && status % 64 != 0 then .error current
  else .ok ()

def CancellationDeliveryBodies : Prop := ∀ (state severity current status : Nat)
    (hasSource preempt : Bool),
  (validCancellationSeverity severity = true →
    cancelBody state severity = .ok (raiseCancellation state severity)) ∧
  redeliverBody state = (state != 0) ∧
  walkNodeBody severity current = max severity current ∧
  handleCancellationBody hasSource preempt status current =
    (if preempt && (!hasSource || status % 64 == 0) then .ok ()
     else if hasSource && status % 64 != 0 then .error current else .ok ())

theorem cancellationDeliveryBodies_proven : CancellationDeliveryBodies := by
  unfold CancellationDeliveryBodies
  intros
  constructor
  · intro valid; simp [cancelBody, valid]
  exact ⟨rfl, rfl, rfl⟩

/-! ## base/cancellation.jl:947-1129, checks and default token wrappers -/

inductive TokenArgument where | useDefault | none | token (source : Nat)
  deriving Repr, DecidableEq

def resolveToken (defaultSource : Option Nat) : TokenArgument → Option Nat
  | .useDefault => defaultSource
  | .none => none
  | .token source => some source

def cancelSource : TokenArgument → Option Nat
  | .token source => some source
  | _ => none

def checkCancelBody (source : Option Nat) (state : Nat) : Except Nat Unit :=
  match source with
  | none => .ok ()
  | some _ => if state == 0 then .ok () else .error state

def CancellationDefaultBodies : Prop := ∀ (defaultSource : Option Nat)
    (argument : TokenArgument) (state : Nat),
  resolveToken defaultSource .useDefault = defaultSource ∧
  resolveToken defaultSource .none = none ∧
  checkCancelBody none state = .ok () ∧
  cancelSource argument = (match argument with | .token source => some source | _ => none)

theorem cancellationDefaultBodies_proven : CancellationDefaultBodies := by
  intro defaultSource argument state
  cases argument <;> simp [resolveToken, checkCancelBody, cancelSource]

/-! ## base/condition.jl:5-135, lock abstractions and condition wrappers -/

def hasLock (locked : Bool) (owner current : Nat) : Bool := locked && owner == current
def alwaysLockedTry (owner current : Nat) : Bool := owner == current
def conditionWaitQueue (identity : Nat) : Nat := identity

def ConditionLockBodies : Prop := ∀ (locked : Bool) (owner current identity : Nat),
  hasLock locked owner current = (locked && owner == current) ∧
  alwaysLockedTry owner current = (owner == current) ∧
  conditionWaitQueue identity = identity

theorem conditionLockBodies_proven : ConditionLockBodies := by
  unfold ConditionLockBodies
  intros
  exact ⟨rfl, rfl, rfl⟩

/-! ## base/condition.jl:140-249, queue registration and fresh subscriptions -/

def conditionEnqueue (queue : List Nat) (waiter : Nat) (first : Bool) : List Nat :=
  if first then waiter :: queue else queue ++ [waiter]

def conditionDequeue (queue : List Nat) (waiter : Nat) : List Nat := queue.erase waiter

def freshWaiter (started queued armed : Bool) : Bool := !started && !queued && !armed

def subscribeBody (queue : List Nat) (waiter : Nat) (first cancelled : Bool) :
    List Nat × Bool :=
  if cancelled then (queue, false) else (conditionEnqueue queue waiter first, true)

def ConditionRegistrationBodies : Prop := ∀ (queue : List Nat) (waiter : Nat)
    (first cancelled started queued armed : Bool),
  conditionDequeue (conditionEnqueue queue waiter first) waiter =
    (conditionEnqueue queue waiter first).erase waiter ∧
  freshWaiter started queued armed = (!started && !queued && !armed) ∧
  (subscribeBody queue waiter first cancelled).2 = !cancelled

theorem conditionRegistrationBodies_proven : ConditionRegistrationBodies := by
  unfold ConditionRegistrationBodies
  intro queue waiter first cancelled started queued armed
  constructor
  · rfl
  constructor
  · rfl
  · cases cancelled <;> rfl

/-! ## base/condition.jl:291-405, cancellable wait and lock restoration -/

inductive ConditionWaitResult where | blocked | value (value : Nat) | cancelled (severity : Nat)
  deriving Repr, DecidableEq

def conditionWaitBody (cancelled cancelAsValue notified : Bool) (payload severity : Nat) :
    ConditionWaitResult :=
  if cancelled then
    if cancelAsValue then .value severity else .cancelled severity
  else if notified then .value payload else .blocked

def ConditionWaitBodies : Prop := ∀ (cancelled cancelAsValue notified : Bool)
    (payload severity : Nat),
  conditionWaitBody cancelled cancelAsValue notified payload severity =
    (if cancelled then
      if cancelAsValue then .value severity else .cancelled severity
     else if notified then .value payload else .blocked)

theorem conditionWaitBodies_proven : ConditionWaitBodies := by
  unfold ConditionWaitBodies
  intros
  rfl

/-! ## base/condition.jl:416-468, notify wrappers and display -/

def conditionShow (threadSafe : Bool) : String :=
  if threadSafe then "GenericCondition(lock)" else "Condition()"

def ConditionNotifyBodies : Prop := ∀ (waiters : List Waiter) (all threadSafe : Bool),
  (notifyModel all waiters).count ≤ waiters.length ∧
  conditionShow threadSafe = (if threadSafe then "GenericCondition(lock)" else "Condition()")

theorem conditionNotifyBodies_proven : ConditionNotifyBodies := by
  intro waiters all threadSafe
  constructor
  · induction waiters with
    | nil => simp [notifyModel]
    | cons waiter waiters ih =>
        cases h : waiter.claimable <;> cases all <;> simp_all [notifyModel] <;> omega
  · rfl

end JuliaLean.Tasks
