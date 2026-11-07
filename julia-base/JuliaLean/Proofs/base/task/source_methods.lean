import JuliaLean.base.task
import JuliaLean.Proofs.base.task.interleavings
import JuliaLean.Proofs.base.cancellation.task_properties
import JuliaLean.Proofs.base.condition.task_properties

namespace JuliaLean.Tasks



def TaskExceptionBodies : Prop := ∀ (frames exceptions : List Nat) (exception : Nat),
  (capturedBacktrace frames).length = min 100 frames.length ∧
  compositePush exceptions exception = exceptions ++ [exception] ∧
  compositePushFirst exceptions exception = exception :: exceptions ∧
  (compositeSummary (exception :: exceptions) = some (exception, exceptions.length))

theorem taskExceptionBodies_proven : TaskExceptionBodies := by
  intro frames exceptions exception
  simp [capturedBacktrace, compositePush, compositePushFirst, compositeSummary,
    List.length_take]

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

end JuliaLean.Tasks
