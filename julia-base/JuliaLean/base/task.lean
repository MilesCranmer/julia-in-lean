import JuliaLean.base.condition
import JuliaLean.base.threadingconstructs
import JuliaLean.base.locks_mt
import JuliaLean.base.pointer
import JuliaLean.base.expr

/-!
# Typed model of `base/task.jl`

Task identities, results, wait entries, cancellation sources, and work queues
have separate types. Runtime context switches and atomic field operations are
world-passing primitives; blocked computations retain nontermination. Queueing,
sticky propagation, wake delivery, and exception cleanup follow the Julia
branches. The scheduler primitives may interleave with other tasks at each call.
-/
namespace JuliaLean.base.task
open JuliaLean
open JuliaLean.base.locks_mt (M MemoryOrder loop finallyDo liftFrame runFrame getFrame setFrame)
open JuliaLean.base.condition (CancelArg GenericCondition WakeValue)
abbrev I := JInt .i64
abbrev I16 := JInt .i16
abbrev U64 := JInt .u64
def int (n : Int) : I := JInt.wrap .i64 n

inductive StateSymbol where
  | runnable | done | failed | abandoned
  deriving DecidableEq, Repr

structure SynchronizedQueue (Queue Lock : Type) where
  identity : Nat
  queue : Queue
  lock : Lock

structure WorkqueueRef (Queue Lock : Type) where
  queue : Queue
  owner : SynchronizedQueue Queue Lock

inductive DoneNotify (Queue Lock Value : Type) where
  | nothing | condition (condition : GenericCondition Queue Lock) | other (value : Value)

structure Runtime (E W Task Queue Lock Entry Slot Source Token LockState Value : Type) where
  condition : JuliaLean.base.condition.Runtime E W Queue Lock Task Entry Slot Source Token LockState Value
  sameTask : Task → Task → Bool
  newCoreTask : M E W (WakeValue Value) → I → M E W Task
  doneNotify : Task → M E W (DoneNotify Queue Lock Value)
  setDoneNotify : Task → GenericCondition Queue Lock → M E W Unit
  loadState : MemoryOrder → Task → M E W UInt8
  storeState : MemoryOrder → Task → UInt8 → M E W Unit
  isTaskStarted : Task → M E W Bool
  result : Task → M E W (WakeValue Value)
  setResult : Task → WakeValue Value → M E W Unit
  isException : Task → M E W Bool
  setException : Task → Bool → M E W Unit
  payloadError : WakeValue Value → E
  errorPayload : E → WakeValue Value
  assertionError : String → E
  taskFailedException : Task → E
  failedTaskOfError : E → Option Task
  compositeException : List E → E
  taskQueue : Task → M E W (Option (SynchronizedQueue Queue Lock))
  swapWaitingOn : Task → Option Entry → M E W (Option Entry)
  metricsEnabled : Task → M E W Bool
  runningTimeAdd : MemoryOrder → Task → U64 → M E W Unit
  taskThreadIdRaw : Task → M E W I16
  doneNotifyTypeError : E
  lastStarted : Task → M E W U64
  setLastStarted : MemoryOrder → Task → U64 → M E W Unit
  firstEnqueued : Task → M E W U64
  setFirstEnqueued : MemoryOrder → Task → U64 → M E W Unit
  timeNs : M E W U64
  newWorkList : M E W Queue
  newSpinLock : M E W Lock
  newQueueIdentity : M E W Nat
  rawEmpty : Queue → M E W Bool
  rawLength : Queue → M E W I
  rawPushLast : WorkqueueRef Queue Lock → Task → M E W Unit
  rawPushFirst : WorkqueueRef Queue Lock → Task → M E W Unit
  rawPopLast : WorkqueueRef Queue Lock → M E W Task
  rawPopFirst : WorkqueueRef Queue Lock → M E W Task
  rawDeleteFirst : WorkqueueRef Queue Lock → Task → M E W Unit
  workqueueFor : I → M E W (SynchronizedQueue Queue Lock)
  multiqInsert : Task → UInt16 → M E W Unit
  multiqDeleteMin : M E W (Option Task)
  taskPriority : Task → M E W UInt16
  wakeThread : I16 → M E W (JInt .i32)
  wakeThreadPool : JInt .i8 → M E W Unit
  setTaskThreadId : Task → I → M E W Unit
  getTaskPoolId : Task → M E W (JInt .i8)
  setNextTask : Task → M E W Unit
  nextTask : M E W Task
  switch : M E W Unit
  multiqCheckEmpty : M E W Bool
  getNextTask : (SynchronizedQueue Queue Lock → M E W (Option Task)) →
    SynchronizedQueue Queue Lock → M E W Bool → M E W Task
  getSchedulerTask : M E W Task
  newSchedulerTask : M E W Task
  gcSafepoint : M E W Unit
  processEvents : M E W Unit
  safeWorkqueueWarning : M E W Unit
  precheckCancelArg : CancelArg Token → M E W (CancelArg Token)
  resolveCancelToken : CancelArg Token → M E W (Option Token)
  findWaitSlot : Entry → GenericCondition Queue Lock → M E W I
  acquireWaitEntry : Task → List Task → Option Source → M E W Entry
  parkDoneTasks : List Task → Option Source → Entry → M E W Bool
  withdrawDoneTasks : List Task → Option Source → Entry → UInt8 → M E W Unit
  waitDoneTasks : List Task → Option Source → Entry → M E W (WakeValue Value)
  cachedCancelEntry2 : Task → M E W (Option Entry)
  cancelEntryOwner2 : MemoryOrder → Entry → M E W (Option Source)
  noteDeadRegistration : Source → M E W Unit
  sigatomicEnd : M E W Unit
  resultIsInterrupt : WakeValue Value → Bool
  errorIsInterrupt : E → Bool
  globalWorkqueue : M E W (SynchronizedQueue Queue Lock)
  rootTask : M E W Task
  rngState : Task → Fin 5 → M E W U64
  setRngState : Task → Fin 5 → U64 → M E W Unit

structure TLSRuntime (E W Task Store Key Value : Type) where
  currentTask : M E W Task
  storage : Task → M E W (Option Store)
  setStorage : Task → Store → M E W Unit
  newIdDict : M E W Store
  storageAsIdDict : Task → M E W Store
  nothingValue : Value
  hasKey : Store → Key → M E W Bool
  getDefault : Store → Key → Value → M E W Value
  get : Store → Key → M E W Value
  set : Store → Key → Value → M E W Value
  delete : Store → Key → M E W Unit

inductive PrintPart (Value : Type) where
  | text (text : String) | value (value : Value)
  | integer (value : I)

structure Diagnostic (E W Task Value IO Stack : Type) where
  withShieldedToken : M E W Task → M E W Task
  stderr : M E W IO
  coreStderr : M E W IO
  newPipeBuffer : M E W IO
  context : IO → IO → M E W IO
  emphasize : IO → String → M E W Unit
  displayError : IO → Stack → M E W Unit
  currentTaskExceptions : Task → M E W Stack
  currentExceptions : M E W Stack
  scrubBacktrace : Stack → M E W Stack
  write : IO → IO → M E W Unit
  print : IO → String → M E W Unit
  flush : IO → M E W Unit
  corePrint : IO → List (PrintPart Value) → M E W Unit
  corePrintln : IO → Value → M E W Unit
  lastException : Stack → M E W Value
  exceptionTypeName : E → String

inductive PropertyValue (V Backtrace Other : Type) where
  | state (value : StateSymbol)
  | backtrace (value : Backtrace)
  | exception (value : Option (WakeValue V))
  | other (value : Other)

structure PropertyRuntime (E W Task V Backtrace Other : Type) where
  currentExceptions : Task → M E W (List (V × Backtrace))
  lastException : List (V × Backtrace) → M E W (V × Backtrace)
  getField : Task → String → M E W (PropertyValue V Backtrace Other)
  setPropertyAny : Task → String → V → M E W V

/-- The native abandonment request owns a wake handle until its terminal poll is consumed. -/
structure AbandonRuntime (E W Task Async V : Type) where
  newAsyncCondition : M E W Async
  request : Task → Task → WakeValue V → Async → M E W (JInt .i32)
  poll : I16 → M E W (JInt .i32)
  close : Async → M E W Unit
  waitShielded : Async → M E W Unit
  cpuPause : M E W Unit

structure CapturedException (V Backtrace : Type) where
  exception : V
  processedBacktrace : List Backtrace

structure CompositeException (Exceptions : Type) where
  exceptions : Exceptions

/-- Vector operations retain the underlying exception-vector reference in the caller's world. -/
structure ExceptionVectorOps (E W V Exceptions State : Type) where
  newEmpty : M E W Exceptions
  length : Exceptions → M E W I
  push : Exceptions → V → M E W Exceptions
  pushFirst : Exceptions → V → M E W Exceptions
  isEmpty : Exceptions → M E W Bool
  iterate : Exceptions → Option State → M E W (Option (V × State))

structure BackendRuntime (E W Task Backend : Type) where
  activeIsDefined : M E W Bool
  active : M E W Backend
  hasBackendTask : Backend → M E W Bool
  backendTask : Backend → M E W Task
  inEval : Backend → M E W Bool
  isNothing : Backend → Bool

structure DiagnosticRuntime (E W IO Buffer Context Stack : Type) where
  stderr : M E W IO
  pipeBuffer : M E W Buffer
  ioContext : Buffer → IO → M E W Context
  emphasize : Context → String → M E W Unit
  currentExceptions : M E W Stack
  displayError : Context → Stack → M E W Unit
  write : IO → Context → M E W I

structure DisplayRuntime (E W IO Buffer Context Task V Backtrace Color : Type) where
  print : IO → List (PrintPart V) → M E W Unit
  println : IO → M E W Unit
  showError : IO → V → M E W Unit
  showValue : IO → V → M E W Unit
  typeName : V → M E W String
  showBacktrace : IO → Backtrace → M E W Unit
  errorColor : M E W Color
  printStyled : IO → String → Color → M E W Unit
  currentExceptions : Task → M E W (List (V × Backtrace))
  newBuffer : M E W Buffer
  ioContext : Buffer → IO → M E W Context
  showContextError : Context → WakeValue V → M E W Unit
  showExceptionStack : Context → List (V × Backtrace) → M E W Unit
  takeString : Buffer → M E W String
  pointerFromObject : Task → M E W (JuliaLean.base.pointer.Ptr Unit)
  pointerToUnsigned : JuliaLean.base.pointer.Ptr Unit → M E W U64
  stringUnsigned : U64 → I → I → M E W String
  formatRequest : UInt8 → M E W String

structure SyncRuntime (E W Channel Task Other Failures Waitees Iter Token Source : Type) where
  tokenOf : Source → Token
  requireToken : Option Token → M E W Token
  isReady : Channel → M E W Bool
  take : Channel → M E W (Sum Task Other)
  close : Channel → M E W Unit
  channelNext : Channel → Option Iter → M E W (Option (Sum Task Other × Iter))
  singletonWaitees : Task → M E W Waitees
  emptyWaitees : M E W Waitees
  pushWaitee : Waitees → Sum Task Other → M E W Unit
  waiteesNext : Waitees → Option Iter → M E W (Option (Sum Task Other × Iter))
  waitOther : Other → M E W Unit
  newFailures : M E W Failures
  pushFailure : Failures → E → M E W Unit
  pushFirstFailure : Failures → E → M E W Unit
  failuresEmpty : Failures → M E W Bool
  failureError : Failures → E
  scheduledAfterError : Waitees → M E W E
  cancellationError : UInt8 → E

section
variable {E W Task Queue Lock Entry Slot Source Token LockState Value : Type}
variable (r : Runtime E W Task Queue Lock Entry Slot Source Token LockState Value)

/-- The source's `::ThreadSynchronizer` assertion, including a malformed task field. -/
def requireDoneCondition (t : Task) : M E W (GenericCondition Queue Lock) := do
  match ← r.doneNotify t with
  | .condition condition => pure condition
  | _ => throw r.doneNotifyTypeError

-- Source: base/task.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## basic task functions and TLS
-- 
-- /Source

-- Source: base/task.jl:10-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Container for a captured exception and its backtrace. Can be serialized.
-- struct CapturedException <: Exception
--     ex::Any
--     processed_bt::Vector{Any}
-- 
-- /Source

-- Source: base/task.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:26-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

-- Source: base/task.jl:31-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     capture_exception(ex, bt)::Exception
-- 
-- Return an exception, possibly incorporating information from a backtrace `bt`. Defaults to returning [`CapturedException(ex, bt)`](@ref).
-- 
-- Used in [`asyncmap`](@ref) and [`asyncmap!`](@ref) to capture exceptions thrown during
-- the user-supplied function call.
-- """
-- /Source

-- Source: base/task.jl:41-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     CompositeException
-- 
-- Wrap a `Vector` of exceptions thrown by a [`Task`](@ref) (e.g. generated from a remote worker over a channel
-- or an asynchronously executing local I/O write or a remote worker under `pmap`) with information about the series of exceptions.
-- For example, if a group of workers are executing several tasks, and multiple workers fail, the resulting `CompositeException` will
-- contain a "bundle" of information from each worker indicating where and why the exception(s) occurred.
-- """
-- struct CompositeException <: Exception
--     exceptions::Vector{Any}
-- /Source

-- Source: base/task.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/task.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:72-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     TaskFailedException
-- 
-- This exception is thrown by a [`wait(t)`](@ref) call when task `t` fails.
-- `TaskFailedException` wraps the failed task `t`.
-- """
-- struct TaskFailedException <: Exception
--     task::Task
-- end
-- 
-- /Source

-- Source: base/task.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:114-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @task
-- 
-- Wrap an expression in a [`Task`](@ref) without executing it, and return the [`Task`](@ref). This only
-- creates a task, and does not run it.
-- 
-- !!! warning
--     By default tasks will have the sticky bit set to true `t.sticky`. This models the
--     historic default for [`@async`](@ref). Sticky tasks can only be run on the worker thread
--     they are first scheduled on, and when scheduled will make the task that they were scheduled
--     from sticky. To obtain the behavior of [`Threads.@spawn`](@ref) set the sticky
--     bit manually to `false`.
-- 
-- # Examples
-- ```jldoctest
-- julia> a1() = sum(i for i in 1:1000);
-- 
-- julia> b = @task a1();
-- 
-- julia> istaskstarted(b)
-- false
-- 
-- julia> schedule(b);
-- 
-- julia> yield();
-- 
-- julia> istaskdone(b)
-- true
-- ```
-- """
-- /Source

-- Source: base/task.jl:149-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # task states
-- 
-- const task_state_runnable  = UInt8(0)
-- const task_state_done      = UInt8(1)
-- const task_state_failed    = UInt8(2)
-- # like _failed, but the task was forcibly abandoned and may have leaked resources
-- const task_state_abandoned = UInt8(3)
-- 
-- /Source

-- Source: base/task.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:200-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     istaskdone(t::Task)::Bool
-- 
-- Determine whether a task has exited.
-- 
-- # Examples
-- ```jldoctest
-- julia> a2() = sum(i for i in 1:1000);
-- 
-- julia> b = Task(a2);
-- 
-- julia> istaskdone(b)
-- false
-- 
-- julia> schedule(b);
-- 
-- julia> yield();
-- 
-- julia> istaskdone(b)
-- true
-- ```
-- """
-- /Source

-- Source: base/task.jl:224-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     istaskstarted(t::Task)::Bool
-- 
-- Determine whether a task has started executing.
-- 
-- # Examples
-- ```jldoctest
-- julia> a3() = sum(i for i in 1:1000);
-- 
-- julia> b = Task(a3);
-- 
-- julia> istaskstarted(b)
-- false
-- ```
-- """
-- /Source

-- Source: base/task.jl:241-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     istaskfailed(t::Task)::Bool
-- 
-- Determine whether a task has exited because an exception was thrown.
-- 
-- # Examples
-- ```jldoctest
-- julia> a4() = error("task failed");
-- 
-- julia> b = Task(a4);
-- 
-- julia> istaskfailed(b)
-- false
-- 
-- julia> schedule(b);
-- 
-- julia> yield();
-- 
-- julia> istaskfailed(b)
-- true
-- ```
-- 
-- !!! compat "Julia 1.3"
--     This function requires at least Julia 1.3.
-- """
-- /Source

-- Source: base/task.jl:271-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unsafe_abandon!(t::Task, next_task::Task) -> Bool
-- 
-- Forcibly abandon task `t` and switch its thread to `next_task`, discarding
-- `t`'s execution. Returns `true` if the abandonment committed: `t`'s state is
-- `:abandoned` and it will never run another instruction.
-- 
-- Returns `false` - with `t` untouched and still running - when the abandonment
-- could not be performed safely: `t` was not (or no longer) running on a
-- thread, was found holding runtime state that must not be discarded (runtime
-- locks, an in-flight finalizer or GC transition, a signal-deferral region),
-- or another abandonment was already in flight for that thread. Blocks (in a
-- scheduler-friendly wait) until the delivery settles the request one way or
-- the other; a victim thread that never services signals blocks the call
-- indefinitely.
-- 
-- `next_task` must be a fresh, never-scheduled task; it takes over the
-- victim's thread.
-- 
-- !!! warning
--     Abandonment discards the victim's execution wherever it stands. Any
--     non-runtime resource it holds (locks, buffers, connections) is leaked.
--     This is a last-resort recovery primitive.
-- 
-- !!! note
--     The task must be currently running on a thread for this to have effect;
--     use [`cancel!`](@ref) with `CANCEL_REQUEST_ABANDON_ALL` to also stop
--     parked or queued tasks.
-- """
-- /Source

-- Source: base/task.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:371-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     task_local_storage(key)
-- 
-- Look up the value of a key in the current task's task-local storage.
-- """
-- /Source

-- Source: base/task.jl:378-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     task_local_storage(key, value)
-- 
-- Assign a value to a key in the current task's task-local storage.
-- """
-- /Source

-- Source: base/task.jl:385-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     task_local_storage(body, key, value)
-- 
-- Call the function `body` with a modified task-local storage, in which `value` is assigned to
-- `key`; the previous value of `key`, or lack thereof, is restored afterwards. Useful
-- for emulating dynamic scoping.
-- """
-- /Source

-- Source: base/task.jl:404-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # just wait for a task to be done, no error propagation
-- /Source

-- Source: base/task.jl:408-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # With `cancel_value`, a cancellation of the governing token (at or above
-- # `min_severity`) is returned as the `CancellationRequest` instead of being
-- # thrown; `nothing` means the task completed.
-- /Source

-- Source: base/task.jl:434-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:436-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Subscribe the not-yet-started `waiter` to `t`'s completion (see the
-- # GenericCondition method's contract in condition.jl: a start trigger
-- # governed by the waiter's birth cancellation source, not a park)
-- /Source

-- Source: base/task.jl:477-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     wait(t::Task; throw=true, cancel=Base.DEFAULT_CANCEL)
-- 
-- Wait for a `Task` to finish.
-- 
-- The keyword `throw` (defaults to `true`) controls whether a failed task results
-- in an error, thrown as a [`TaskFailedException`](@ref) which wraps the failed task.
-- 
-- The `cancel` keyword argument controls which cancellation token may interrupt
-- the wait (see [`CancellationToken`](@ref)); by default the scoped token. A
-- cancelled wait throws the [`CancellationRequest`](@ref) and leaves `t`
-- unaffected: cancellation reaches `t` only through its own governing token
-- (e.g. when both waiter and waitee run under the same cancelled scope).
-- 
-- Throws a `ConcurrencyViolationError` if `t` is the currently running task, to prevent deadlocks.
-- """
-- /Source

-- Source: base/task.jl:511-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Wait multiple tasks
-- 
-- """
--     waitany(tasks; throw=true) -> (done_tasks, remaining_tasks)
-- 
-- Wait until at least one of the given tasks have been completed.
-- 
-- If `throw` is `true`, throw `CompositeException` when one of the
-- completed tasks completes with an exception.
-- 
-- The return value consists of two task vectors. The first one consists of
-- completed tasks, and the other consists of uncompleted tasks.
-- 
-- !!! warning
--     This may scale poorly compared to writing code that uses multiple individual tasks that
--     each runs serially, since this needs to scan the list of `tasks` each time and
--     synchronize with each one every time this is called. Or consider using
--     [`waitall(tasks; failfast=true)`](@ref waitall) instead.
-- 
-- !!! compat "Julia 1.12"
--     This function requires at least Julia 1.12.
-- """
-- /Source

-- Source: base/task.jl:536-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     waitall(tasks; failfast=true, throw=true) -> (done_tasks, remaining_tasks)
-- 
-- Wait until all the given tasks have been completed.
-- 
-- If `failfast` is `true`, the function will return when at least one of the
-- given tasks is finished by exception. If `throw` is `true`, throw
-- `CompositeException` when one of the completed tasks has failed.
-- 
-- `failfast` and `throw` keyword arguments work independently; when only
-- `throw=true` is specified, this function waits for all the tasks to complete.
-- 
-- The return value consists of two task vectors. The first one consists of
-- completed tasks, and the other consists of uncompleted tasks.
-- 
-- !!! compat "Julia 1.12"
--     This function requires at least Julia 1.12.
-- """
-- /Source

-- Source: base/task.jl:557-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:566-576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Task completion as a waitable (see base/park.jl): a one-shot predicate
-- ## kind - enqueue declines when the task is already done (its only notify
-- ## has fired), and the recheck is membership-qualified: the slot witness,
-- ## cleared when the completion notify pops the entry, is the
-- ## already-delivered bit (without it a repark! would re-fire forever on
-- ## consumed completions).
-- struct DoneWait
--     t::Task
-- end
-- 
-- /Source

-- Source: base/task.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:611-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:718-723 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fetch(x::Any)
-- 
-- Return `x`.
-- """
-- /Source

-- Source: base/task.jl:725-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fetch(t::Task)
-- 
-- Wait for a [`Task`](@ref) to finish, then return its result value.
-- If the task fails with an exception, a [`TaskFailedException`](@ref) (which wraps the failed task)
-- is thrown.
-- """
-- /Source

-- Source: base/task.jl:743-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## lexically-scoped waiting for multiple items
-- 
-- struct ScheduledAfterSyncException <: Exception
--     values::Vector{Any}
-- end
-- 
-- /Source

-- Source: base/task.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:781-781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:840-847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const sync_varname = gensym(:sync)
-- 
-- # Teardown of a `@sync` block whose own scope was cancelled: the scope's
-- # token subtree (covering every child) is already cancelled; await the
-- # children's unwind per the severity policy. Our own acknowledgement of the
-- # request lets these teardown waits park; they are only re-woken by a
-- # severity escalation (`min_severity`).
-- /Source

-- Source: base/task.jl:893-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @sync
-- 
-- Wait until all lexically-enclosed uses of [`@async`](@ref), [`@spawn`](@ref Threads.@spawn),
-- `Distributed.@spawnat` and `Distributed.@distributed`
-- are complete. All exceptions thrown by enclosed async operations are collected and thrown as
-- a [`CompositeException`](@ref).
-- 
-- # Examples
-- ```julia-repl
-- julia> Threads.nthreads()
-- 4
-- 
-- julia> @sync begin
--            Threads.@spawn println("Thread-id \$(Threads.threadid()), task 1")
--            Threads.@spawn println("Thread-id \$(Threads.threadid()), task 2")
--        end;
-- Thread-id 3, task 1
-- Thread-id 1, task 2
-- ```
-- """
-- /Source

-- Source: base/task.jl:936-958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # schedule an expression to run asynchronously
-- 
-- """
--     @async
-- 
-- Wrap an expression in a [`Task`](@ref) and add it to the local machine's scheduler queue.
-- 
-- Values can be interpolated into `@async` via `\$`, which copies the value directly into the
-- constructed underlying closure. This allows you to insert the _value_ of a variable,
-- isolating the asynchronous code from changes to the variable's value in the current task.
-- 
-- !!! warning
--     It is strongly encouraged to favor `Threads.@spawn` over `@async` always **even when no
--     parallelism is required** especially in publicly distributed libraries.  This is
--     because a use of `@async` disables the migration of the *parent* task across worker
--     threads in the current implementation of Julia.  Thus, seemingly innocent use of
--     `@async` in a library function can have a large impact on the performance of very
--     different parts of user applications.
-- 
-- !!! compat "Julia 1.4"
--     Interpolating values via `\$` is available as of Julia 1.4.
-- """
-- /Source

-- Source: base/task.jl:962-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # generate the code for @async, possibly wrapping the task in something before
-- # pushing it to the wait queue.
-- /Source

-- Source: base/task.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # task wrapper that doesn't create exceptions wrapped in TaskFailedException
-- struct UnwrapTaskFailedException <: Exception
--     task::Task
-- end
-- 
-- # common code for wait&fetch for UnwrapTaskFailedException
-- /Source

-- Source: base/task.jl:999-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # the unwrapping for above task wrapper (gets triggered in sync_end())
-- /Source

-- Source: base/task.jl:1002-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # same for fetching the tasks, for convenience
-- /Source

-- Source: base/task.jl:1005-1006 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # macro for running async code that doesn't throw wrapped exceptions
-- /Source

-- Source: base/task.jl:1010-1023 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     errormonitor(t::Task)
-- 
-- Print an error log to `stderr` if task `t` fails.
-- 
-- # Examples
-- ```julia-repl
-- julia> wait(errormonitor(Threads.@spawn error("task failed")); throw = false)
-- Unhandled Task ERROR: task failed
-- Stacktrace:
-- [...]
-- ```
-- """
-- /Source

-- Source: base/task.jl:1060-1061 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Capture interpolated variables in $() and move them to let-block
-- /Source

-- Source: base/task.jl:1096-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # add a wait-able object to the sync pool
-- /Source

-- Source: base/task.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1118-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # runtime system hook called when a task finishes
-- /Source

-- Source: base/task.jl:1167-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1173-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## scheduler and work queue
-- 
-- mutable struct IntrusiveLinkedListSynchronized{T}
--     queue::IntrusiveLinkedList{T}
--     lock::Threads.SpinLock
-- /Source

-- Source: base/task.jl:1180-1180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/task.jl:1227-1231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const StickyWorkqueue = IntrusiveLinkedListSynchronized{Task}
-- const Workqueues = OncePerThread{StickyWorkqueue}(StickyWorkqueue)
-- const Workqueue = Workqueues[1] # default work queue is thread 1 // TODO: deprecate this variable
-- 
-- /Source

-- Source: base/task.jl:1233-1233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1313-1313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1319-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     schedule(t::Task, [val]; error=false)
-- 
-- Add a [`Task`](@ref) to the scheduler's queue. This causes the task to run constantly when the system
-- is otherwise idle, unless the task performs a blocking operation such as [`wait`](@ref).
-- 
-- If a second argument `val` is provided, it will be passed to the task (via the return value of
-- [`yieldto`](@ref)) when it runs again. If `error` is `true`, the value is raised as an exception in
-- the woken task.
-- 
-- !!! warning
--     It is incorrect to use `schedule` on an arbitrary `Task` that has already been started.
--     See [the API reference](@ref low-level-schedule-wait) for more information.
-- 
-- !!! warning
--     By default tasks will have the sticky bit set to true `t.sticky`. This models the
--     historic default for [`@async`](@ref). Sticky tasks can only be run on the worker thread
--     they are first scheduled on, and when scheduled will make the task that they were scheduled
--     from sticky. To obtain the behavior of [`Threads.@spawn`](@ref) set the sticky
--     bit manually to `false`.
-- 
-- # Examples
-- ```jldoctest
-- julia> a5() = sum(i for i in 1:1000);
-- 
-- julia> b = Task(a5);
-- 
-- julia> istaskstarted(b)
-- false
-- 
-- julia> schedule(b);
-- 
-- julia> yield();
-- 
-- julia> istaskstarted(b)
-- true
-- 
-- julia> istaskdone(b)
-- true
-- ```
-- 
-- A task that is blocked in [`wait`](@ref) can be woken with a value, which is then returned
-- by `wait` in that task:
-- ```jldoctest
-- julia> t = Task(() -> 2 * wait());
-- 
-- julia> schedule(t); yield(); # `t` starts and blocks in `wait()`
-- 
-- julia> schedule(t, 21);
-- 
-- julia> fetch(t)
-- 42
-- ```
-- """
-- /Source

-- Source: base/task.jl:1395-1404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Deliver `exc` into the parked wait whose wake the caller already claimed
-- # by CASing `t.waiting_on` from `w` to nothing (the cancellation walk).
-- # Unlike `schedule(t, exc, error=true)` - whose unconditional swap *takes*
-- # a claim - this must not re-claim: the claim was the wake ticket. If a
-- # claim-less wake (a raw interrupter, `throwto`) resumed the task first and
-- # it has since registered a new wait, the claimed park no longer exists and
-- # the delivery is dropped - a task still eligibly parked under the
-- # cancelled source is impossible (its registration recheck refuses), and
-- # anything else must not observe this request.
-- /Source

-- Source: base/task.jl:1421-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The value-mode variant of `deliver_claimed_wake!`, with the same claim
-- # contract: the parked wait *completes*, returning `val` (the cancellation
-- # walk's delivery to a watcher - `wait(::CancellationToken)` - whose wait
-- # the cancellation is the event for).
-- /Source

-- Source: base/task.jl:1437-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     yield()
-- 
-- Switch to the scheduler to allow another scheduled task to run. A task that calls this
-- function is still runnable, and will be restarted immediately if there are no other runnable
-- tasks.
-- """
-- /Source

-- Source: base/task.jl:1455-1455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1457-1465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     yield(t::Task, arg = nothing)
-- 
-- A fast, unfair-scheduling version of `schedule(t, arg); yield()` which
-- immediately yields to `t` before calling the scheduler.
-- 
-- Throws a `ConcurrencyViolationError` if `t` is the currently running task.
-- """
-- /Source

-- Source: base/task.jl:1480-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     yieldto(t::Task, arg = nothing)
-- 
-- Switch to the given task. The first time a task is switched to, the task's function is
-- called with no arguments. On subsequent switches, `arg` is returned from the task's last
-- call to `yieldto`. This is a low-level call that only switches tasks, not considering states
-- or scheduling in any way. Its use is discouraged.
-- """
-- /Source

-- Source: base/task.jl:1506-1506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1529-1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # yield to a task, throwing an exception in it
-- /Source

-- Source: base/task.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1587-1587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1603-1605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const get_sched_task = OncePerThread{Task}(_new_sched_task)
-- 
-- /Source

-- Source: base/task.jl:1622-1622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1638-1638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/task.jl:1658-1660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- checktaskempty = Partr.multiq_check_empty
-- 
-- /Source

-- Source: base/task.jl:1693-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Sys.iswindows()
-- /Source

-- Source: base/task.jl:1696-1696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source

-- Source: base/task.jl:1698-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # update the `running_time_ns` field of `t` to include the time since it last started running.
-- /Source

-- Source: base/task.jl:1707-1710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # if this is the first time `t` has been added to the run queue
-- # (or the first time it has been unfairly yielded to without being added to the run queue)
-- # then set the `first_enqueued_at` field to the current time.
-- /Source

/--
Julia source: base/task.jl:5-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.Task(@nospecialize(f), reserved_stack::Int=0)
    task = Core._task(f, reserved_stack)
    task.donenotify = ThreadSynchronizer()
    return task
end
```
-/
def newTask (body : M E W (WakeValue Value)) (reservedStack : I := int 0) : M E W Task := do
  let t ← r.newCoreTask body reservedStack
  let condition ← JuliaLean.base.condition.newGenericCondition r.condition
  r.setDoneNotify t condition
  pure t

/--
Julia source: base/task.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
istaskdone(t::Task) = (@atomic :acquire t._state) !== task_state_runnable
```
-/
def istaskdone (t : Task) : M E W Bool := do
  pure ((← r.loadState .acquire t) != 0)

/--
Julia source: base/task.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
istaskstarted(t::Task) = ccall(:jl_is_task_started, Cint, (Any,), t) != 0
```
-/
def istaskstarted (t : Task) : M E W Bool := r.isTaskStarted t

/--
Julia source: base/task.jl:267-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function istaskfailed(t::Task)
    st = @atomic :acquire t._state
    return st === task_state_failed || st === task_state_abandoned
end
```
-/
def istaskfailed (t : Task) : M E W Bool := do
  let state ← r.loadState .acquire t
  pure (state == 2 || state == 3)

/--
Julia source: base/task.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Threads.threadid(t::Task) = Int(ccall(:jl_get_task_tid, Int16, (Any,), t)+1)
```
-/
def threadid (t : Task) : M E W I := do
  pure (int ((← r.taskThreadIdRaw t).val + 1))

/--
Julia source: base/task.jl:357-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Threads.threadpool(t::Task)
    tpid = ccall(:jl_get_task_threadpoolid, Int8, (Any,), t)
    return Threads._tpid_to_sym(tpid)
end
```
-/
def threadpool (t : Task) : M E W JuliaLean.base.threadingconstructs.Pool := do
  let poolId ← r.getTaskPoolId t
  JuliaLean.base.threadingconstructs.liftResult
    (JuliaLean.base.threadingconstructs.tpidToSym r.condition.argumentError poolId)

/--
Julia source: base/task.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
task_result(t::Task) = t.result
```
-/
def taskResult (t : Task) : M E W (WakeValue Value) := r.result t

/--
Julia source: base/task.jl:158-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getproperty(t::Task, field::Symbol)
    if field === :state
        # TODO: this field name should be deprecated in 2.0
        st = @atomic :acquire t._state
        if st === task_state_runnable
            return :runnable
        elseif st === task_state_done
            return :done
        elseif st === task_state_failed
            return :failed
        elseif st === task_state_abandoned
            return :abandoned
        else
            @assert false "unexpected state"
        end
    elseif field === :backtrace
        # TODO: this field name should be deprecated in 2.0
        return current_exceptions(t)[end][2]
    elseif field === :exception
        # TODO: this field name should be deprecated in 2.0
        return t._isexception ? t.result : nothing
    elseif field === :scope
        error("""
            Querying a Task's `scope` field is disallowed.
            The private `Core.current_scope()` function is better, though still an implementation detail.""")
    elseif field === :invoked
        error("Querying a Task's `invoked` field is disallowed because it is an implementation detail.")
    else
        return getfield(t, field)
    end
end
```
-/
def getproperty {Backtrace Other : Type} (p : PropertyRuntime E W Task Value Backtrace Other)
    (t : Task) (field : String) : M E W (PropertyValue Value Backtrace Other) := do
  if field == "state" then
    let state ← r.loadState .acquire t
    if state == 0 then return .state .runnable
    if state == 1 then return .state .done
    if state == 2 then return .state .failed
    if state == 3 then return .state .abandoned
    throw (r.assertionError "unexpected state")
  else if field == "backtrace" then
    pure (.backtrace (← p.lastException (← p.currentExceptions t)).2)
  else if field == "exception" then
    if ← r.isException t then pure (.exception (some (← r.result t))) else pure (.exception none)
  else if field == "scope" then
    throw (r.condition.error "Querying a Task's `scope` field is disallowed.\nThe private `Core.current_scope()` function is better, though still an implementation detail.\n")
  else if field == "invoked" then
    throw (r.condition.error "Querying a Task's `invoked` field is disallowed because it is an implementation detail.")
  else p.getField t field

/--
Julia source: base/task.jl:190-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setproperty!(t::Task, field::Symbol, @nospecialize(v))
    if field === :scope
        istaskstarted(t) && error("Setting scope on a started task directly is disallowed.")
    elseif field === :invoked
        error("Setting a Task's `invoked` field directly is disallowed because it is an implementation detail.")
    elseif field === :result
        error("Setting a Task's `result` field directly is disallowed. The result of a task is determined by the return value of its code; to pass a value to a suspended task, use `schedule(t, val)` or `yieldto(t, val)` instead.")
    end
    return @invoke setproperty!(t::Any, field::Symbol, v::Any)
end
```
-/
def setproperty {Backtrace Other : Type} (p : PropertyRuntime E W Task Value Backtrace Other)
    (t : Task) (field : String) (value : Value) : M E W Value := do
  if field == "scope" then
    if ← istaskstarted r t then throw (r.condition.error "Setting scope on a started task directly is disallowed.")
  else if field == "invoked" then
    throw (r.condition.error "Setting a Task's `invoked` field directly is disallowed because it is an implementation detail.")
  else if field == "result" then
    throw (r.condition.error "Setting a Task's `result` field directly is disallowed. The result of a task is determined by the return value of its code; to pass a value to a suspended task, use `schedule(t, val)` or `yieldto(t, val)` instead.")
  p.setPropertyAny t field value

/--
Julia source: base/task.jl:1701-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function record_running_time!(t::Task)
    if t.metrics_enabled && !istaskdone(t)
        @atomic :monotonic t.running_time_ns +%= time_ns() -% t.last_started_running_at
    end
    return t
end
```
-/
def recordRunningTime (t : Task) : M E W Task := do
  if ← r.metricsEnabled t then
    if !(← istaskdone r t) then
      let now ← r.timeNs
      let previous ← r.lastStarted t
      r.runningTimeAdd .monotonic t (now - previous)
  pure t

/--
Julia source: base/task.jl:1711-1716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function maybe_record_enqueued!(t::Task)
    if t.metrics_enabled && t.first_enqueued_at == 0
        @atomic :monotonic t.first_enqueued_at = time_ns()
    end
    return t
end
```
-/
def maybeRecordEnqueued (t : Task) : M E W Task := do
  if ← r.metricsEnabled t then
    if (← r.firstEnqueued t).val == 0 then
      r.setFirstEnqueued .monotonic t (← r.timeNs)
  pure t

/--
Julia source: base/task.jl:1179-1179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IntrusiveLinkedListSynchronized{T}() where {T} = new(IntrusiveLinkedList{T}(), Threads.SpinLock())
```
-/
def newSynchronizedQueue : M E W (SynchronizedQueue Queue Lock) := do
  let queue ← r.newWorkList
  let lock ← r.newSpinLock
  let identity ← r.newQueueIdentity
  pure ⟨identity, queue, lock⟩

/--
Julia source: base/task.jl:1181-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitqueue(W::IntrusiveLinkedListSynchronized) = ILLRef(W.queue, W)
```
-/
def workqueueRef (queue : SynchronizedQueue Queue Lock) : WorkqueueRef Queue Lock := ⟨queue.queue, queue⟩

/--
Julia source: base/task.jl:1182-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(W::IntrusiveLinkedListSynchronized) = isempty(W.queue)
```
-/
def workqueueEmpty (queue : SynchronizedQueue Queue Lock) : M E W Bool := r.rawEmpty queue.queue

/--
Julia source: base/task.jl:1183-1183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(W::IntrusiveLinkedListSynchronized) = length(W.queue)
```
-/
def workqueueLength (queue : SynchronizedQueue Queue Lock) : M E W I := r.rawLength queue.queue

/--
Julia source: base/task.jl:1184-1192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(W::IntrusiveLinkedListSynchronized{T}, t::T) where T
    lock(W.lock)
    try
        push!(waitqueue(W), t)
    finally
        unlock(W.lock)
    end
    return W
end
```
-/
def pushWork (queue : SynchronizedQueue Queue Lock) (t : Task) : M E W (SynchronizedQueue Queue Lock) := do
  r.condition.lock queue.lock
  finallyDo (r.rawPushLast (workqueueRef queue) t) (r.condition.unlock queue.lock)
  pure queue

/--
Julia source: base/task.jl:1193-1201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(W::IntrusiveLinkedListSynchronized{T}, t::T) where T
    lock(W.lock)
    try
        pushfirst!(waitqueue(W), t)
    finally
        unlock(W.lock)
    end
    return W
end
```
-/
def pushFirstWork (queue : SynchronizedQueue Queue Lock) (t : Task) : M E W (SynchronizedQueue Queue Lock) := do
  r.condition.lock queue.lock
  finallyDo (r.rawPushFirst (workqueueRef queue) t) (r.condition.unlock queue.lock)
  pure queue

/--
Julia source: base/task.jl:1202-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(W::IntrusiveLinkedListSynchronized)
    lock(W.lock)
    try
        return pop!(waitqueue(W))
    finally
        unlock(W.lock)
    end
end
```
-/
def popWork (queue : SynchronizedQueue Queue Lock) : M E W Task := do
  r.condition.lock queue.lock
  finallyDo (r.rawPopLast (workqueueRef queue)) (r.condition.unlock queue.lock)

/--
Julia source: base/task.jl:1210-1217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst!(W::IntrusiveLinkedListSynchronized)
    lock(W.lock)
    try
        return popfirst!(waitqueue(W))
    finally
        unlock(W.lock)
    end
end
```
-/
def popFirstWork (queue : SynchronizedQueue Queue Lock) : M E W Task := do
  r.condition.lock queue.lock
  finallyDo (r.rawPopFirst (workqueueRef queue)) (r.condition.unlock queue.lock)

/--
Julia source: base/task.jl:1218-1226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function list_deletefirst!(W::IntrusiveLinkedListSynchronized{T}, t::T) where T
    lock(W.lock)
    try
        list_deletefirst!(waitqueue(W), t)
    finally
        unlock(W.lock)
    end
    return W
end
```
-/
def deleteFirstWork (queue : SynchronizedQueue Queue Lock) (t : Task) : M E W (SynchronizedQueue Queue Lock) := do
  r.condition.lock queue.lock
  finallyDo (r.rawDeleteFirst (workqueueRef queue) t) (r.condition.unlock queue.lock)
  pure queue

/--
Julia source: base/task.jl:1232-1232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
workqueue_for(tid::Int) = Workqueues[tid]
```
-/
def workqueueFor (tid : I) : M E W (SynchronizedQueue Queue Lock) := r.workqueueFor tid

/--
Julia source: base/task.jl:1234-1312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function enq_work(t::Task)
    state = t._state
    if state === task_state_abandoned
        # A task frozen by forcible abandonment leaves its waitqueue
        # registrations behind by design; a later notify of such a stale
        # entry lands here. The wakeup is consumed by the abandoned task -
        # drop it silently.
        return t
    end
    (state === task_state_runnable && t.queue === nothing) || error("schedule: Task not runnable")
    (@atomic :monotonic t.waiting_on) === nothing ||
        throw(ConcurrencyViolationError("schedule: Task is registered on a wait queue"))

    # Sticky tasks go into their thread's work queue.
    if t.sticky
        tid = Threads.threadid(t)
        if tid == 0
            # The task is not yet stuck to a thread. Stick it to the current
            # thread and do the same to the parent task (the current task) so
            # that the tasks are correctly co-scheduled (issue #41324).
            # XXX: Ideally we would be able to unset this.
            if GC.in_finalizer()
                # The task was launched in a finalizer. There is no thread to sticky it
                # to, so just allow it to run anywhere as if it had been non-sticky.
                t.sticky = false
                @goto not_sticky
            else
                tid = Threads.threadid()
                ccall(:jl_set_task_tid, Cint, (Any, Cint), t, tid-1)
                current_task().sticky = true
            end
        end
        push!(workqueue_for(tid), t)
    else
        @label not_sticky
        tp = Threads.threadpool(t)
        if tp !== :foreign && Threads.threadpoolsize(tp) == 0
            # The task's threadpool has no threads, so it can never run;
            # fail it with a ConcurrencyViolationError rather than queueing
            # it (the multiqueue heaps are unsized for empty pools, and a
            # task queued during sysimage bootstrap would be serialized
            # into the system image).
            setfield!(t, :result, ConcurrencyViolationError("deadlock detected: cannot schedule task"))
            t._isexception = true
            @atomic :release t._state = task_state_failed
            return t
        end
        if tp === :foreign || Threads.threadpoolsize(tp) == 1
            # There's only one thread in the task's assigned thread pool;
            # use its work queue.
            tid = (tp === :interactive) ? 1 : Threads.threadpoolsize(:interactive)+1
            ccall(:jl_set_task_tid, Cint, (Any, Cint), t, tid-1)
            push!(workqueue_for(tid), t)
        else
            # Otherwise, put the task in the multiqueue.
            Partr.multiq_insert(t, t.priority)
            tid = Threads.threadid(t)
            if tid != 0 && tid != Threads.threadid()
                # The task's tid is pinned to another thread: typically it is that
                # thread's current task, parked hosting its thread-sleep logic in
                # wait(), and only that thread can resume it, so wake it directly
                # (#58689). If that thread was already awake (busy with other work),
                # this wake added no running thread; wake a pool thread too so the
                # number of running threads still scales with enqueued work — the
                # task is not sticky, so its tid may be cleared later, making it
                # runnable by any pool thread.
                if ccall(:jl_wakeup_thread, Cint, (Int16,), (tid - 1) % Int16) == 0
                    ccall(:jl_wakeup_threadpool, Cvoid, (Int8,), Threads._sym_to_tpid(tp))
                end
            else
                # Wake one sleeping thread in the task's pool rather than all of them. See #61820, #50425.
                ccall(:jl_wakeup_threadpool, Cvoid, (Int8,), Threads._sym_to_tpid(tp))
            end
            return t
        end
    end
    ccall(:jl_wakeup_thread, Cint, (Int16,), (tid - 1) % Int16)
    return t
end
```
-/
def enqWork (t : Task) : M E W Task := do
  let state ← r.loadState .plain t
  if state == 3 then return t
  if state != 0 then throw (r.condition.error "schedule: Task not runnable")
  if (← r.taskQueue t).isSome then throw (r.condition.error "schedule: Task not runnable")
  if (← r.condition.waitingOn .monotonic t).isSome then
    throw (r.condition.concurrencyError "schedule: Task is registered on a wait queue")
  let mut sticky ← r.condition.sticky t
  let mut tid := int 0
  if sticky then
    tid ← threadid r t
    if tid.val == 0 then
      if ← r.condition.inFinalizer then
        r.condition.setSticky t false
        sticky := false
      else
        tid ← JuliaLean.base.threadingconstructs.threadid r.condition.queries
        r.setTaskThreadId t (tid - int 1)
        r.condition.setSticky (← r.condition.currentTask) true
  if sticky then
    let _ ← pushWork r (← workqueueFor r tid) t
  else
    let pool ← threadpool r t
    if pool != .foreign then
      if (← JuliaLean.base.threadingconstructs.threadpoolsize r.condition.queries pool).val == 0 then
        r.setResult t (r.errorPayload (r.condition.concurrencyError "deadlock detected: cannot schedule task"))
        r.setException t true
        r.storeState .release t 2
        return t
    let single ← if pool == .foreign then pure true else do
      pure ((← JuliaLean.base.threadingconstructs.threadpoolsize r.condition.queries pool).val == 1)
    if single then
      tid ← if pool == .interactive then pure (int 1) else do
        pure ((← JuliaLean.base.threadingconstructs.threadpoolsize r.condition.queries .interactive) + int 1)
      r.setTaskThreadId t (tid - int 1)
      let _ ← pushWork r (← workqueueFor r tid) t
    else
      r.multiqInsert t (← r.taskPriority t)
      tid ← threadid r t
      if tid.val != 0 then
        if tid.val != (← JuliaLean.base.threadingconstructs.threadid r.condition.queries).val then
          let woken ← r.wakeThread (JInt.wrap .i16 (tid - int 1).val)
          if woken.val == 0 then
            let poolId ← JuliaLean.base.threadingconstructs.liftResult
              (JuliaLean.base.threadingconstructs.symToTpid r.condition.argumentError pool)
            r.wakeThreadPool poolId
        else
          let poolId ← JuliaLean.base.threadingconstructs.liftResult
            (JuliaLean.base.threadingconstructs.symToTpid r.condition.argumentError pool)
          r.wakeThreadPool poolId
      else
        let poolId ← JuliaLean.base.threadingconstructs.liftResult
          (JuliaLean.base.threadingconstructs.symToTpid r.condition.argumentError pool)
        r.wakeThreadPool poolId
      return t
  let _ ← r.wakeThread (JInt.wrap .i16 (tid - int 1).val)
  pure t

/--
Julia source: base/task.jl:1314-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function schedule(t::Task)
    # [task] created -scheduled-> wait_time
    maybe_record_enqueued!(t)
    enq_work(t)
end
```
-/
def schedule (t : Task) : M E W Task := do
  let _ ← maybeRecordEnqueued r t
  enqWork r t

/--
Julia source: base/task.jl:1374-1394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function schedule(t::Task, @nospecialize(arg); error=false)
    # schedule a task to be (re)started with the given value or exception
    t._state === task_state_runnable || Base.error("schedule: Task not runnable")
    if error
        # Interrupt path: Unconditionally remove the wait (if any)
        # TODO: This should use the proper cancellation system instead
        w = @atomicswap t.waiting_on = nothing
        w isa WaitEntry && try_unlink_claimed!(w)
        q = t.queue
        q === nothing || list_deletefirst!(q::StickyWorkqueue, t)
        setfield!(t, :result, arg)
        setfield!(t, :_isexception, true)
    else
        t.queue === nothing || Base.error("schedule: Task not runnable")
        setfield!(t, :result, arg)
    end
    # [task] created -scheduled-> wait_time
    maybe_record_enqueued!(t)
    enq_work(t)
    return t
end
```
-/
def scheduleValue (t : Task) (arg : WakeValue Value) (error : Bool := false) : M E W Task := do
  if (← r.loadState .plain t) != 0 then throw (r.condition.error "schedule: Task not runnable")
  if error then
    match ← r.swapWaitingOn t none with
    | some w => let _ ← JuliaLean.base.condition.tryUnlinkClaimed r.condition w; pure ()
    | none => pure ()
    match ← r.taskQueue t with
    | some queue => let _ ← deleteFirstWork r queue t; pure ()
    | none => pure ()
    r.setResult t arg
    r.setException t true
  else
    if (← r.taskQueue t).isSome then throw (r.condition.error "schedule: Task not runnable")
    r.setResult t arg
  let _ ← maybeRecordEnqueued r t
  let _ ← enqWork r t
  pure t

/--
Julia source: base/task.jl:1405-1420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deliver_claimed_wake!(t::Task, w::WaitEntry, @nospecialize(exc))
    (@atomic :monotonic t.waiting_on) === nothing || return nothing
    # the claimed waitee-queue entry stays linked (the walk does not take
    # waitee locks); collect it opportunistically like an interrupter would
    try_unlink_claimed!(w)
    # a pending wake somebody enqueued claim-lessly is superseded by the
    # cancellation delivery, like an interrupt overriding a claimed value
    q = t.queue
    q === nothing || list_deletefirst!(q::StickyWorkqueue, t)
    t._state === task_state_runnable || return nothing
    setfield!(t, :result, exc)
    setfield!(t, :_isexception, true)
    maybe_record_enqueued!(t)
    enq_work(t)
    return nothing
end
```
-/
def deliverClaimedWake (t : Task) (w : Entry) (exception : WakeValue Value) : M E W Unit := do
  if (← r.condition.waitingOn .monotonic t).isSome then return ()
  let _ ← JuliaLean.base.condition.tryUnlinkClaimed r.condition w
  match ← r.taskQueue t with
  | some queue => let _ ← deleteFirstWork r queue t; pure ()
  | none => pure ()
  if (← r.loadState .plain t) != 0 then return ()
  r.setResult t exception
  r.setException t true
  let _ ← maybeRecordEnqueued r t
  let _ ← enqWork r t
  pure ()

/--
Julia source: base/task.jl:1426-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deliver_claimed_value_wake!(t::Task, w::WaitEntry, @nospecialize(val))
    (@atomic :monotonic t.waiting_on) === nothing || return nothing
    try_unlink_claimed!(w)
    q = t.queue
    q === nothing || list_deletefirst!(q::StickyWorkqueue, t)
    t._state === task_state_runnable || return nothing
    setfield!(t, :result, val)
    maybe_record_enqueued!(t)
    enq_work(t)
    return nothing
end
```
-/
def deliverClaimedValueWake (t : Task) (w : Entry) (value : WakeValue Value) : M E W Unit := do
  if (← r.condition.waitingOn .monotonic t).isSome then return ()
  let _ ← JuliaLean.base.condition.tryUnlinkClaimed r.condition w
  match ← r.taskQueue t with
  | some queue => let _ ← deleteFirstWork r queue t; pure ()
  | none => pure ()
  if (← r.loadState .plain t) != 0 then return ()
  r.setResult t value
  let _ ← maybeRecordEnqueued r t
  let _ ← enqWork r t
  pure ()

/--
Julia source: base/task.jl:1606-1621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ensure_rescheduled(othertask::Task)
    ct = current_task()
    W = workqueue_for(Threads.threadid())
    if ct !== othertask && othertask._state === task_state_runnable
        # we failed to yield to othertask
        # return it to the head of a queue to be retried later
        tid = Threads.threadid(othertask)
        Wother = tid == 0 ? W : workqueue_for(tid)
        pushfirst!(Wother, othertask)
    end
    # if the current task was queued,
    # also need to return it to the runnable state
    # before throwing an error
    list_deletefirst!(W, ct)
    nothing
end
```
-/
def ensureRescheduled (other : Task) : M E W Unit := do
  let current ← r.condition.currentTask
  let queue ← workqueueFor r (← JuliaLean.base.threadingconstructs.threadid r.condition.queries)
  if !(r.sameTask current other) then
    if (← r.loadState .plain other) == 0 then
      let tid ← threadid r other
      let otherQueue ← if tid.val == 0 then pure queue else workqueueFor r tid
      let _ ← pushFirstWork r otherQueue other
  let _ ← deleteFirstWork r queue current
  pure ()

/--
Julia source: base/task.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline set_next_task(t::Task) = ccall(:jl_set_next_task, Cvoid, (Any,), t)
```
-/
def setNextTask (t : Task) : M E W Unit := r.setNextTask t

/--
Julia source: base/task.jl:1507-1528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_yieldto(undo)
    try
        ccall(:jl_switch, Cvoid, ())
    catch
        undo(ccall(:jl_get_next_task, Ref{Task}, ()))
        rethrow()
    end
    ct = current_task()
    # [task] wait_time -(re)started-> user_time
    if ct.metrics_enabled
        @atomic :monotonic ct.last_started_running_at = time_ns()
    end
    if ct._isexception
        exc = ct.result
        setfield!(ct, :result, nothing)
        ct._isexception = false
        throw(exc)
    end
    result = ct.result
    setfield!(ct, :result, nothing)
    return result
end
```
-/
def tryYieldTo (undo : Task → M E W Unit) : M E W (WakeValue Value) := do
  tryCatch r.switch (fun error => do undo (← r.nextTask); throw error)
  let current ← r.condition.currentTask
  if ← r.metricsEnabled current then r.setLastStarted .monotonic current (← r.timeNs)
  if ← r.isException current then
    let error ← r.result current
    r.setResult current .nothing
    r.setException current false
    throw (r.payloadError error)
  let result ← r.result current
  r.setResult current .nothing
  pure result

/--
Julia source: base/task.jl:1489-1505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function yieldto(t::Task, @nospecialize(x=nothing))
    ct = current_task()
    # TODO: these are legacy behaviors; these should perhaps be a scheduler
    # state error instead.
    if t._state === task_state_done
        return x
    elseif t._state === task_state_failed || t._state === task_state_abandoned
        throw(t.result)
    end
    # [task] user_time -yield-> wait_time
    record_running_time!(ct)
    # [task] created -scheduled-unfairly-> wait_time
    maybe_record_enqueued!(t)
    setfield!(t, :result, x)
    set_next_task(t)
    return try_yieldto(identity)
end
```
-/
def yieldto (t : Task) (arg : WakeValue Value := .nothing) : M E W (WakeValue Value) := do
  let current ← r.condition.currentTask
  if (← r.loadState .plain t) == 1 then return arg
  if (← r.loadState .plain t) == 2 then throw (r.payloadError (← r.result t))
  if (← r.loadState .plain t) == 3 then throw (r.payloadError (← r.result t))
  let _ ← recordRunningTime r current
  let _ ← maybeRecordEnqueued r t
  r.setResult t arg
  setNextTask r t
  tryYieldTo r (fun _ => pure ())

/--
Julia source: base/task.jl:1531-1541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function throwto(t::Task, @nospecialize exc)
    ct = current_task()
    # [task] user_time -yield-> wait_time
    record_running_time!(ct)
    # [task] created -scheduled-unfairly-> wait_time
    maybe_record_enqueued!(t)
    setfield!(t, :result, exc)
    t._isexception = true
    set_next_task(t)
    return try_yieldto(identity)
end
```
-/
def throwto (t : Task) (exception : WakeValue Value) : M E W (WakeValue Value) := do
  let current ← r.condition.currentTask
  let _ ← recordRunningTime r current
  let _ ← maybeRecordEnqueued r t
  r.setResult t exception
  r.setException t true
  setNextTask r t
  tryYieldTo r (fun _ => pure ())

/--
Julia source: base/task.jl:1623-1637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function discard_stale_workqueue_task(t::Task)
    # A task frozen in place by forcible abandonment is completed without
    # ever leaving the queues it was registered with (a workqueue, or a
    # waitqueue whose later notify re-enqueues it here); discard it. Any
    # other non-runnable state means the task somehow got queued twice -
    # probably broken now, but try discarding this switch and keep going.
    # We can't throw here, because it's probably not the fault of the caller
    # to wait, and don't want to use print() here, because that may try to
    # incur a task switch.
    if t._state !== task_state_abandoned
        ccall(:jl_safe_printf, Cvoid, (Ptr{UInt8}, Int32...),
            "\nWARNING: Workqueue inconsistency detected: popfirst!(Workqueue).state !== :runnable\n")
    end
    nothing
end
```
-/
def discardStaleWorkqueueTask (t : Task) : M E W Unit := do
  if (← r.loadState .plain t) != 3 then r.safeWorkqueueWarning

/--
Julia source: base/task.jl:1639-1657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trypoptask(W::StickyWorkqueue)
    while !isempty(W)
        t = popfirst!(W)
        if t._state !== task_state_runnable
            discard_stale_workqueue_task(t)
            continue
        end
        return t
    end
    while true
        t = Partr.multiq_deletemin()
        t === nothing && return nothing
        if t._state !== task_state_runnable
            discard_stale_workqueue_task(t)
            continue
        end
        return t
    end
end
```
-/
def trypoptask (queue : SynchronizedQueue Queue Lock) : M E W (Option Task) := do
  let localTask ← loop (fun (_ : Unit) => do
    if ← workqueueEmpty r queue then return .inl none
    let task ← popFirstWork r queue
    if (← r.loadState .plain task) != 0 then
      discardStaleWorkqueueTask r task
      return .inr ()
    pure (.inl (some task))) ()
  match localTask with
  | some task => pure (some task)
  | none => loop (fun (_ : Unit) => do
      match ← r.multiqDeleteMin with
      | none => pure (.inl none)
      | some task =>
        if (← r.loadState .plain task) != 0 then
          discardStaleWorkqueueTask r task
          return .inr ()
        pure (.inl (some task))) ()

/--
Julia source: base/task.jl:1661-1692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait()
    ct = current_task()
    # [task] user_time -yield-or-done-> wait_time
    record_running_time!(ct)
    # let GC run
    GC.safepoint()
    # check for libuv events, but not on a completed task (#63048)
    ct_done = istaskdone(ct)
    ct_done || process_events()

    # get the next task to run
    W = workqueue_for(Threads.threadid())
    task = trypoptask(W)
    if task === nothing
        # No tasks to run. If the current task is done, switch to the scheduler task
        # to run the thread sleep logic, so that this task's stack can be freed
        # promptly (#57544). Otherwise run the thread sleep logic in the context of
        # the current task, so that an asynchronously thrown InterruptException
        # is delivered to a task that can observe it, rather than swallowed by
        # the internal scheduler task (#58689).
        if ct_done
            sched_task = get_sched_task()
            if ct !== sched_task
                istaskdone(sched_task) && (sched_task = _new_sched_task())
                return yieldto(sched_task)
            end
        end
        task = ccall(:jl_task_get_next, Ref{Task}, (Any, Any, Any), trypoptask, W, checktaskempty)
    end
    set_next_task(task)
    return try_yieldto(ensure_rescheduled)
end
```
-/
def waitScheduler : M E W (WakeValue Value) := do
  let current ← r.condition.currentTask
  let _ ← recordRunningTime r current
  r.gcSafepoint
  let done ← istaskdone r current
  if !done then r.processEvents
  let queue ← workqueueFor r (← JuliaLean.base.threadingconstructs.threadid r.condition.queries)
  let task ← trypoptask r queue
  let task ← match task with
    | some task => pure (Sum.inr task)
    | none => (fun (_ : Unit) => do
      if done then
        let scheduler ← r.getSchedulerTask
        if !(r.sameTask current scheduler) then
          let scheduler ← if ← istaskdone r scheduler then r.newSchedulerTask else pure scheduler
          return ← do
            let value ← yieldto r scheduler
            pure (Sum.inl value)
      pure (Sum.inr (← r.getNextTask (trypoptask r) queue r.multiqCheckEmpty))) ()
  match task with
  | .inl value => pure value
  | .inr task => setNextTask r task; tryYieldTo r (ensureRescheduled r)

/--
Julia source: base/task.jl:1445-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function yield()
    ct = current_task()
    enq_work(ct)
    try
        wait()
    catch
        q = ct.queue; q === nothing || list_deletefirst!(q::StickyWorkqueue, ct)
        rethrow()
    end
end
```
-/
def yield : M E W (WakeValue Value) := do
  let current ← r.condition.currentTask
  let _ ← enqWork r current
  tryCatch (waitScheduler r) (fun error => do
    match ← r.taskQueue current with
    | some queue => let _ ← deleteFirstWork r queue current; pure ()
    | none => pure ()
    throw error)

/--
Julia source: base/task.jl:1466-1479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function yield(t::Task, @nospecialize(x=nothing))
    ct = current_task()
    t === ct && throw(ConcurrencyViolationError("Cannot yield to currently running task!"))
    (t._state === task_state_runnable && t.queue === nothing &&
     (@atomic :monotonic t.waiting_on) === nothing) || throw(ConcurrencyViolationError("yield: Task not runnable"))
    # [task] user_time -yield-> wait_time
    record_running_time!(ct)
    # [task] created -scheduled-> wait_time
    maybe_record_enqueued!(t)
    setfield!(t, :result, x)
    enq_work(ct)
    set_next_task(t)
    return try_yieldto(ensure_rescheduled)
end
```
-/
def yieldTask (t : Task) (arg : WakeValue Value := .nothing) : M E W (WakeValue Value) := do
  let current ← r.condition.currentTask
  if r.sameTask t current then
    throw (r.condition.concurrencyError "Cannot yield to currently running task!")
  if (← r.loadState .plain t) != 0 then throw (r.condition.concurrencyError "yield: Task not runnable")
  if (← r.taskQueue t).isSome then throw (r.condition.concurrencyError "yield: Task not runnable")
  if (← r.condition.waitingOn .monotonic t).isSome then
    throw (r.condition.concurrencyError "yield: Task not runnable")
  let _ ← recordRunningTime r current
  let _ ← maybeRecordEnqueued r t
  r.setResult t arg
  let _ ← enqWork r current
  setNextTask r t
  tryYieldTo r (ensureRescheduled r)

/--
Julia source: base/task.jl:1168-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_task_lock(t::Task) # Function only called from jl_adopt_thread so foreign tasks have a lock.
    if t.donenotify === nothing
        t.donenotify = ThreadSynchronizer()
    end
end
```
-/
def initTaskLock (t : Task) : M E W Unit := do
  match ← r.doneNotify t with
  | .nothing => r.setDoneNotify t (← JuliaLean.base.condition.newGenericCondition r.condition)
  | _ => pure ()

/--
Julia source: base/task.jl:411-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _wait(t::Task, tok::MaybeToken; min_severity::UInt8=0x00,
               cancel_value::Bool=false)
    t === current_task() && throw(ConcurrencyViolationError("deadlock detected: cannot wait on current task"))
    if !istaskdone(t)
        donenotify = t.donenotify::ThreadSynchronizer
        lock(donenotify)
        locked = true
        try
            while !istaskdone(t)
                locked = false
                r = wait(donenotify, tok; min_severity=min_severity,
                         cancel_value=cancel_value)
                locked = true
                if cancel_value && r isa CancellationRequest
                    return r
                end
            end
        finally
            locked && unlock(donenotify)
        end
    end
    nothing
end
```
-/
def waitToken (t : Task) (token : Option Token) (minSeverity : UInt8 := 0)
    (cancelValue : Bool := false) : M E W (WakeValue Value) := do
  if r.sameTask t (← r.condition.currentTask) then
    throw (r.condition.concurrencyError "deadlock detected: cannot wait on current task")
  if !(← istaskdone r t) then
    let condition ← requireDoneCondition r t
    JuliaLean.base.condition.lockCondition r.condition condition
    let result ← runFrame true do
      finallyDo (loop (fun (_ : Unit) => do
        if ← liftFrame (istaskdone r t) then return .inl WakeValue.nothing
        setFrame false
        let value ← liftFrame (JuliaLean.base.condition.waitToken r.condition condition token false minSeverity cancelValue)
        setFrame true
        if cancelValue then
          match value with
          | .cancellation _ => return .inl value
          | _ => pure ()
        pure (.inr ())) ()) (do
          if ← getFrame then liftFrame (JuliaLean.base.condition.unlockCondition r.condition condition))
    return result
  pure .nothing

/--
Julia source: base/task.jl:406-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_wait(t::Task; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    _wait(t, resolve_cancel_token(cancel))
```
-/
def waitInternal (t : Task) (cancel : CancelArg Token := .default) : M E W (WakeValue Value) := do
  waitToken r t (← r.resolveCancelToken cancel)

/--
Julia source: base/task.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitqueue(t::Task) = waitqueue(t.donenotify::ThreadSynchronizer)
```
-/
def waitqueue (t : Task) : M E W (JuliaLean.base.condition.QueueRef Queue Lock) := do
  pure (JuliaLean.base.condition.waitqueue (← requireDoneCondition r t))

/--
Julia source: base/task.jl:440-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function schedule_on_notify!(t::Task, waiter::Task)
    _assert_fresh_waiter(waiter)
    if !istaskdone(t)
        # since this is similar to schedule, we should observe the sticky
        # bit, even if we don't call `schedule` with early-return below
        if waiter.sticky && Threads.threadid(waiter) == 0 && !GC.in_finalizer()
            # Issue #41324
            # t.sticky && tid == 0 is a task that needs to be co-scheduled with
            # the parent task. If the parent (current_task) is not sticky we must
            # set it to be sticky.
            # XXX: Ideally we would be able to unset this
            current_task().sticky = true
            tid = Threads.threadid()
            ccall(:jl_set_task_tid, Cint, (Any, Cint), waiter, tid-1)
        end
        donenotify = t.donenotify::ThreadSynchronizer
        lock(donenotify)
        try
            if !istaskdone(t)
                schedule_on_notify!(donenotify, waiter)
                return nothing
            end
        finally
            unlock(donenotify)
        end
    end
    # `t` already done: start (or, under a cancelled birth source, kill)
    # the waiter now
    _assert_fresh_waiter(waiter)
    src = _birth_cancel_source(waiter)
    if src !== nothing && iscancelled(src)
        _schedule_subscription_cancelled(waiter, src)
    else
        schedule(waiter)
    end
    nothing
end
```
-/
def scheduleOnNotify (t waiter : Task) : M E W Unit := do
  JuliaLean.base.condition.assertFreshWaiter r.condition waiter
  if !(← istaskdone r t) then
    if ← r.condition.sticky waiter then
      if (← threadid r waiter).val == 0 then
        if !(← r.condition.inFinalizer) then
          r.condition.setSticky (← r.condition.currentTask) true
          let tid ← JuliaLean.base.threadingconstructs.threadid r.condition.queries
          r.setTaskThreadId waiter (tid - int 1)
    let condition ← requireDoneCondition r t
    JuliaLean.base.condition.lockCondition r.condition condition
    let subscribed ← finallyDo (do
      if !(← istaskdone r t) then
        let _ ← JuliaLean.base.condition.scheduleOnNotify r.condition condition waiter
        pure true
      else pure false) (JuliaLean.base.condition.unlockCondition r.condition condition)
    if subscribed then return ()
  JuliaLean.base.condition.assertFreshWaiter r.condition waiter
  let source ← r.condition.birthCancelSource waiter
  match source with
  | some source =>
    if ← r.condition.sourceCancelled source then
      JuliaLean.base.condition.scheduleSubscriptionCancelled r.condition waiter source
    else let _ ← schedule r waiter; pure ()
  | none => let _ ← schedule r waiter; pure ()

/--
Julia source: base/task.jl:503-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function wait(t::Task, tok::MaybeToken; throw=true)
    # Inlining a blocking call buys nothing; this also keeps the inlineable `fetch(::Task)` small.
    _wait(t, tok)
    if throw && istaskfailed(t)
        Core.throw(TaskFailedException(t))
    end
    nothing
end
```
-/
def waitTaskToken (t : Task) (token : Option Token) (throwFailure : Bool := true) : M E W Unit := do
  let _ ← waitToken r t token
  if throwFailure then
    if ← istaskfailed r t then throw (r.taskFailedException t)

/--
Julia source: base/task.jl:494-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait(t::Task; throw=true, cancel::CancelTokenArg=DEFAULT_CANCEL)
    # An explicit token is checked here, the scoped one only if the wait blocks.
    cancel = precheck_cancel_arg(cancel)
    istaskdone(t) || return wait(t, resolve_cancel_token(cancel); throw)
    if throw && istaskfailed(t)
        Core.throw(TaskFailedException(t))
    end
    nothing
end
```
-/
def wait (t : Task) (throwFailure : Bool := true) (cancel : CancelArg Token := .default) : M E W Unit := do
  let cancel ← r.precheckCancelArg cancel
  if !(← istaskdone r t) then return ← waitTaskToken r t (← r.resolveCancelToken cancel) throwFailure
  if throwFailure then
    if ← istaskfailed r t then throw (r.taskFailedException t)

/--
Julia source: base/task.jl:724-724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fetch(@nospecialize x) = x
```
-/
def fetchValue {A : Type} (value : A) : A := value

/--
Julia source: base/task.jl:733-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function fetch(t::Task; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # `cancel` governs the *wait* for the task: a cancellation unwinds this
    # fetch, the fetched task keeps running.
    wait(t; cancel)
    # This typeassert looks redundant, but is required for soundness and must not be
    # removed: `Task.code`/`Task.result` are mutable, so the precise type inference
    # may derive here (via `PartialTask`) is a claim that must be re-checked at
    # runtime, not a proven fact.
    return task_result(t)::Core.task_result_type(t)
end
```
-/
def fetch (t : Task) (cancel : CancelArg Token := .default) : M E W (WakeValue Value) := do
  let cancel ← r.precheckCancelArg cancel
  if !(← istaskdone r t) then
    let _ ← waitToken r t (← r.resolveCancelToken cancel)
  if ← istaskfailed r t then throw (r.taskFailedException t)
  taskResult r t

/--
Julia source: base/task.jl:577-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_enqueue!(x::DoneWait, w::WaitEntry, first::Bool)
    t = x.t
    donenotify = t.donenotify::ThreadSynchronizer
    lock(donenotify)
    if istaskdone(t)
        unlock(donenotify)
        return false
    end
    # a duplicate of an already-registered task shares its slot
    if _find_slot(w, donenotify) == 0
        push!(waitqueue(t), w)
    end
    unlock(donenotify)
    return true
end
```
-/
def doneWaitEnqueue (t : Task) (w : Entry) (_first : Bool) : M E W Bool := do
  let condition ← requireDoneCondition r t
  JuliaLean.base.condition.lockCondition r.condition condition
  if ← istaskdone r t then
    JuliaLean.base.condition.unlockCondition r.condition condition
    return false
  if (← r.findWaitSlot w condition).val == 0 then
    r.condition.pushLast (← waitqueue r t) w
  JuliaLean.base.condition.unlockCondition r.condition condition
  pure true

/--
Julia source: base/task.jl:593-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_recheck(x::DoneWait, w::WaitEntry)
    t = x.t
    istaskdone(t) || return false
    return _find_slot(w, t.donenotify::ThreadSynchronizer) != 0
end
```
-/
def doneWaitRecheck (t : Task) (w : Entry) : M E W Bool := do
  if !(← istaskdone r t) then return false
  pure ((← r.findWaitSlot w (← requireDoneCondition r t)).val != 0)

/--
Julia source: base/task.jl:599-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_dequeue!(x::DoneWait, w::WaitEntry, why::UInt8)
    # lazy on a normal wake: the claiming completion notify popped its own
    # registration; eager everywhere else (fired slots must not re-fire,
    # withdrawal and cleanup must not leave the entry reachable)
    why == WAKE_VALUE && return nothing
    t = x.t
    donenotify = t.donenotify::ThreadSynchronizer
    lock(donenotify)
    list_deletefirst!(waitqueue(t), w)
    unlock(donenotify)
    return nothing
end
```
-/
def doneWaitDequeue (t : Task) (w : Entry) (why : UInt8) : M E W Unit := do
  if why == r.condition.wakeValue then return ()
  let condition ← requireDoneCondition r t
  JuliaLean.base.condition.lockCondition r.condition condition
  r.condition.deleteFirst (← waitqueue r t) w
  JuliaLean.base.condition.unlockCondition r.condition condition

/--
Julia source: base/task.jl:365-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_task_tls(t::Task)
    if t.storage === nothing
        t.storage = IdDict()
    end
    return (t.storage)::IdDict{Any,Any}
end
```
-/
def getTaskTLS {Store Key V : Type} (tls : TLSRuntime E W Task Store Key V) (t : Task) : M E W Store := do
  if (← tls.storage t).isNone then tls.setStorage t (← tls.newIdDict)
  tls.storageAsIdDict t

/--
Julia source: base/task.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
task_local_storage() = get_task_tls(current_task())
```
-/
def taskLocalStorage {Store Key V : Type} (tls : TLSRuntime E W Task Store Key V) : M E W Store := do
  getTaskTLS tls (← tls.currentTask)

/--
Julia source: base/task.jl:377-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
task_local_storage(key) = task_local_storage()[key]
```
-/
def taskLocalStorageGet {Store Key V : Type} (tls : TLSRuntime E W Task Store Key V) (key : Key) : M E W V := do
  tls.get (← taskLocalStorage tls) key

/--
Julia source: base/task.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
task_local_storage(key, val) = (task_local_storage()[key] = val)
```
-/
def taskLocalStorageSet {Store Key V : Type} (tls : TLSRuntime E W Task Store Key V)
    (key : Key) (value : V) : M E W V := do
  tls.set (← taskLocalStorage tls) key value

/--
Julia source: base/task.jl:393-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function task_local_storage(body::Function, key, val)
    tls = task_local_storage()
    hadkey = haskey(tls, key)
    old = get(tls, key, nothing)
    tls[key] = val
    try
        return body()
    finally
        hadkey ? (tls[key] = old) : delete!(tls, key)
    end
end
```
-/
def taskLocalStorageBody {Store Key V A : Type} (tls : TLSRuntime E W Task Store Key V)
    (body : M E W A) (key : Key) (value : V) : M E W A := do
  let store ← taskLocalStorage tls
  let hadKey ← tls.hasKey store key
  let old ← tls.getDefault store key tls.nothingValue
  let _ ← tls.set store key value
  finallyDo body (if hadKey then do let _ ← tls.set store key old; pure () else tls.delete store key)

/--
Julia source: base/task.jl:1024-1059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function errormonitor(t::Task)
    # the monitor is diagnostic cleanup: shield it from the constructing
    # scope's cancellation so a cancelled scope still gets its report
    t2 = ScopedValues.with(CANCEL_TOKEN => nothing) do
        Task() do
        if istaskfailed(t)
            local errs = stderr
            try # try to display the failure atomically
                errio = IOContext(PipeBuffer(), errs::IO)
                emphasize(errio, "Unhandled Task ")
                display_error(errio, scrub_repl_backtrace(current_exceptions(t)))
                write(errs, errio)
            catch
                try # try to display the secondary error atomically
                    errio = IOContext(PipeBuffer(), errs::IO)
                    print(errio, "\nSYSTEM: caught exception while trying to print a failed Task notice: ")
                    display_error(errio, scrub_repl_backtrace(current_exceptions()))
                    write(errs, errio)
                    flush(errs)
                    # and then the actual error, as best we can
                    Core.print(Core.stderr, "while handling: ")
                    Core.println(Core.stderr, current_exceptions(t)[end][1])
                catch e
                    # give up
                    Core.print(Core.stderr, "\nSYSTEM: caught exception of type ", typeof(e).name.name,
                            " while trying to print a failed Task notice; giving up\n")
                end
            end
        end
        nothing
    end
    end
    t2.sticky = false
    schedule_on_notify!(t, t2)
    return t
end
```
-/
def errormonitor {IO Stack : Type} (d : Diagnostic E W Task Value IO Stack) (t : Task) : M E W Task := do
  let monitor ← d.withShieldedToken (newTask r (do
    if ← istaskfailed r t then
      let errors ← d.stderr
      tryCatch (do
        let context ← d.context (← d.newPipeBuffer) errors
        d.emphasize context "Unhandled Task "
        d.displayError context (← d.scrubBacktrace (← d.currentTaskExceptions t))
        d.write errors context) (fun _ => do
        tryCatch (do
          let context ← d.context (← d.newPipeBuffer) errors
          d.print context "\nSYSTEM: caught exception while trying to print a failed Task notice: "
          d.displayError context (← d.scrubBacktrace (← d.currentExceptions))
          d.write errors context
          d.flush errors
          d.corePrint (← d.coreStderr) [.text "while handling: "]
          d.corePrintln (← d.coreStderr) (← d.lastException (← d.currentTaskExceptions t))) (fun error => do
          d.corePrint (← d.coreStderr) [.text "\nSYSTEM: caught exception of type ",
            .text (d.exceptionTypeName error),
            .text " while trying to print a failed Task notice; giving up\n"]))
    pure .nothing))
  r.condition.setSticky monitor false
  scheduleOnNotify r t monitor
  pure t

/--
Julia source: base/task.jl:558-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function collect_tasks(waiting_tasks)
    tasks = Task[]
    for t in waiting_tasks
        t isa Task || error("Expected an iterator of `Task` object")
        push!(tasks, t)
    end
    return tasks
end
```
-/
def collectTasks {Input State Other : Type}
    (iterate : Input → Option State → M E W (Option (Sum Task Other × State)))
    (input : Input) : M E W (List Task) :=
  loop (fun (state : Option State × List Task) => do
    match ← iterate input state.1 with
    | none => pure (.inl state.2.reverse)
    | some (.inl task, next) => pure (.inr (some next, task :: state.2))
    | some (.inr _, _) => throw (r.condition.error "Expected an iterator of `Task` object")) (none, [])

/--
Julia source: base/task.jl:612-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _wait_multiple(tasks::Vector{Task}, throwexc::Bool=false, all::Bool=false, failfast::Bool=false,
                        tok::MaybeToken=default_cancel_token())
    if (all && !failfast) || length(tasks) <= 1
        exception = false
        # Force everything to finish synchronously for the case of waitall
        # with failfast=false
        for t in tasks
            _wait(t, tok)
            exception |= istaskfailed(t)
        end
        if exception && throwexc
            exceptions = [TaskFailedException(t) for t in tasks if istaskfailed(t)]
            throw(CompositeException(exceptions))
        else
            return tasks, Task[]
        end
    end

    exception = false
    nremaining::Int = length(tasks)
    done_mask = falses(nremaining)
    for (i, t) in enumerate(tasks)
        if istaskdone(t)
            done_mask[i] = true
            exception |= istaskfailed(t)
            nremaining -= 1
        end
    end

    # We can return early if all tasks are done, or if any is done and we only
    # needed to wait for one, or if any task failed and we have failfast
    if nremaining == 0 || (any(done_mask) && (!all || (failfast && exception)))
        if throwexc && (!all || failfast) && exception
            exceptions = [TaskFailedException(t) for t in tasks[done_mask] if istaskfailed(t)]
            throw(CompositeException(exceptions))
        else
            if nremaining == 0
                return tasks, Task[]
            else
                return tasks[done_mask], tasks[.~done_mask]
            end
        end
    end

    # Re-run `park!` for pending tasks after each wake: the previous park
    # may have stopped at a completed task, and notifications while unarmed
    # can consume registrations. Keep registrations for pending tasks, but
    # synchronize with completed tasks' notifiers before reusing their slots.
    ct = current_task()
    src = cancel_source(tok)
    src === nothing || checkcancel(src)
    ws = Vector{Union{DoneWait, SourceWait}}()
    for (i, done) in enumerate(done_mask)
        done || push!(ws, DoneWait(tasks[i]))
    end
    src === nothing || push!(ws, SourceWait(src, 0x00))
    w = acquire_wait_entry!(ct, ws)
    while true
        # suspend only when the park armed (a `false` park means a waitable
        # fired - a completion, or the source - and the self-claim won)
        park!(ws, w, false) && wait_safe_interrupt(ws, w)
        # the fired-source outcome (and, level-triggered, any cancelled
        # state) delivers here: withdraw and throw
        if src !== nothing && iscancelled(src)
            withdraw!(ws, w)
            checkcancel(src)
        end
        # collect completions (a wake happens-after its completing notify,
        # so the istaskdone reads below observe it)
        for (i, done) in enumerate(done_mask)
            done && continue
            t = tasks[i]
            if istaskdone(t)
                wait_dequeue!(DoneWait(t), w, WAKE_WITHDRAWN)
                done_mask[i] = true
                exception |= istaskfailed(t)
                nremaining -= 1
            end
        end
        if nremaining == 0 || (!all && any(done_mask)) || (exception && failfast)
            break
        end
        empty!(ws)
        for (i, done) in enumerate(done_mask)
            done || push!(ws, DoneWait(tasks[i]))
        end
        src === nothing || push!(ws, SourceWait(src, 0x00))
    end
    withdraw!(ws, w)

    if nremaining == 0
        if throwexc && exception
            exceptions = [TaskFailedException(t) for t in tasks if istaskfailed(t)]
            throw(CompositeException(exceptions))
        end
        return tasks, Task[]
    else
        done_tasks = tasks[done_mask]
        if throwexc && exception
            exceptions = [TaskFailedException(t) for t in done_tasks if istaskfailed(t)]
            throw(CompositeException(exceptions))
        else
            return done_tasks, tasks[.~done_mask]
        end
    end
end
```
-/
def failedExceptions (tasks : List Task) : M E W (List E) := do
  let mut errors := []
  for task in tasks do
    if ← istaskfailed r task then errors := r.taskFailedException task :: errors
  pure errors.reverse

def partitionTasks (tasks : List Task) (mask : List Bool) : List Task × List Task :=
  (tasks.zip mask).foldr (fun (task, done) (finished, remaining) =>
    if done then (task :: finished, remaining) else (finished, task :: remaining)) ([], [])

def scanTasks (tasks : List Task) (mask : List Bool) (entry : Option Entry)
    (exception : Bool) (remaining : I) : M E W (List Bool × Bool × I) := do
  let mut next := []
  let mut exception := exception
  let mut remaining := remaining
  for (task, done) in tasks.zip mask do
    if done then next := true :: next
    else if ← istaskdone r task then
      match entry with
      | some entry => doneWaitDequeue r task entry r.condition.wakeWithdrawn
      | none => pure ()
      next := true :: next
      let failed ← istaskfailed r task
      exception := exception || failed
      remaining := remaining - int 1
    else next := false :: next
  pure (next.reverse, exception, remaining)

def waitMultiple (tasks : List Task) (throwException : Bool := false) (all : Bool := false)
    (failfast : Bool := false) (token : Option Token := none) : M E W (List Task × List Task) := do
  if (all && !failfast) || tasks.length ≤ 1 then
    let mut exception := false
    for task in tasks do
      let _ ← waitToken r task token
      let failed ← istaskfailed r task
      exception := exception || failed
    if exception && throwException then throw (r.compositeException (← failedExceptions r tasks))
    return (tasks, [])
  let (mask, exception, remaining) ← scanTasks r tasks (List.replicate tasks.length false) none false (int tasks.length)
  if remaining.val == 0 || (mask.any id && (!all || (failfast && exception))) then
    if throwException && (!all || failfast) && exception then
      throw (r.compositeException (← failedExceptions r (partitionTasks tasks mask).1))
    if remaining.val == 0 then return (tasks, [])
    return partitionTasks tasks mask
  let current ← r.condition.currentTask
  let source := r.condition.cancelSource token
  if source.isSome then r.condition.checkCancel source
  let pending := (partitionTasks tasks mask).2
  let entry ← r.acquireWaitEntry current pending source
  let (mask, exception, remaining, pending) ← loop (fun (state : List Bool × Bool × I × List Task) => do
    if ← r.parkDoneTasks state.2.2.2 source entry then
      let _ ← r.waitDoneTasks state.2.2.2 source entry
    match source with
    | some sourceValue =>
      if ← r.condition.sourceCancelled sourceValue then
        r.withdrawDoneTasks state.2.2.2 source entry r.condition.wakeWithdrawn
        r.condition.checkCancel source
    | none => pure ()
    let (mask, exception, remaining) ← scanTasks r tasks state.1 (some entry) state.2.1 state.2.2.1
    if remaining.val == 0 || (!all && mask.any id) || (exception && failfast) then
      return .inl (mask, exception, remaining, state.2.2.2)
    pure (.inr (mask, exception, remaining, (partitionTasks tasks mask).2))) (mask, exception, remaining, pending)
  r.withdrawDoneTasks pending source entry r.condition.wakeWithdrawn
  if remaining.val == 0 then
    if throwException && exception then throw (r.compositeException (← failedExceptions r tasks))
    pure (tasks, [])
  else
    let doneTasks := (partitionTasks tasks mask).1
    if throwException && exception then throw (r.compositeException (← failedExceptions r doneTasks))
    pure (doneTasks, (partitionTasks tasks mask).2)

/--
Julia source: base/task.jl:534-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitany(tasks; throw=true, cancel::CancelTokenArg=DEFAULT_CANCEL) =
    _wait_multiple(collect_tasks(tasks), throw, false, false, check_cancel_arg(cancel))
```
-/
def waitany {Input State Other : Type}
    (iterate : Input → Option State → M E W (Option (Sum Task Other × State)))
    (input : Input) (throwFailure : Bool := true)
    (cancel : CancelArg Token := .default) : M E W (List Task × List Task) := do
  let tasks ← collectTasks r iterate input
  let token ← r.condition.checkCancelArg cancel
  waitMultiple r tasks throwFailure false false token

/--
Julia source: base/task.jl:555-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
waitall(tasks; failfast=true, throw=true, cancel::CancelTokenArg=DEFAULT_CANCEL) =
    _wait_multiple(collect_tasks(tasks), throw, true, failfast, check_cancel_arg(cancel))
```
-/
def waitall {Input State Other : Type}
    (iterate : Input → Option State → M E W (Option (Sum Task Other × State)))
    (input : Input) (failfast : Bool := true)
    (throwFailure : Bool := true) (cancel : CancelArg Token := .default) : M E W (List Task × List Task) := do
  let tasks ← collectTasks r iterate input
  let token ← r.condition.checkCancelArg cancel
  waitMultiple r tasks throwFailure true failfast token

/--
Julia source: base/task.jl:304-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_abandon!(t::Task, next_task::Task, @nospecialize(result))
    # The requester's own wakeup handle, staged with the request in the
    # victim thread's abandon slot: the delivery paths ping it (from signal
    # context, where uv_async_send is the one legal wakeup) when the
    # request settles. One requester per slot means one consumer per
    # handle, which is exactly the AsyncCondition trigger's latched,
    # consume-once semantics - a settle that lands inside the check/park
    # window below is caught by the latch.
    async = AsyncCondition()
    tid = ccall(:jl_abandon_task_request, Cint, (Any, Any, Any, Ptr{Cvoid}),
                t, next_task, result, async.handle)
    if tid < 0
        close(async)
        return false
    end
    tid = tid % Int16
    ok = false
    try
        while true
            verdict = ccall(:jl_abandon_task_poll, Cint, (Int16,), tid)
            if verdict == 1 || verdict == -1
                ok = verdict == 1
                break
            elseif verdict == 2
                # mid-settle: the ping was already sent (pre-terminal, so it
                # can never race this handle's close below); the verdict is
                # microseconds away
                ccall(:jl_cpu_pause, Cvoid, ())
            else
                wait(async; cancel=nothing)
            end
        end
    finally
        # Safe only after the terminal consume: pings happen strictly
        # before the terminal state becomes visible.
        close(async)
    end
    if ok
        # A forcibly abandoned task never goes through the regular task
        # completion path, so wake up anyone waiting on it. (The waiters
        # observe the already-stored abandoned state; they do not touch the
        # task's stack. The root task's donenotify may be `nothing`.)
        donenotify = t.donenotify
        if donenotify isa ThreadSynchronizer
            lock(donenotify)
            notify(donenotify)
            unlock(donenotify)
        end
    end
    return ok
end
```
-/
def unsafeAbandon {Async : Type} (a : AbandonRuntime E W Task Async Value)
    (task next : Task) (result : WakeValue Value) : M E W Bool := do
  let async ← a.newAsyncCondition
  let tid ← a.request task next result async
  if tid.val < 0 then
    a.close async
    return false
  let tid := JInt.wrap .i16 tid.val
  let ok ← finallyDo (loop (fun (_ : Unit) => do
    let verdict ← a.poll tid
    if verdict.val == 1 || verdict.val == -1 then return .inl (verdict.val == 1)
    if verdict.val == 2 then a.cpuPause else a.waitShielded async
    pure (.inr ())) ()) (a.close async)
  if ok then
    match ← r.doneNotify task with
    | .condition condition =>
      JuliaLean.base.condition.lockCondition r.condition condition
      let _ ← JuliaLean.base.condition.notifyKw r.condition condition
      JuliaLean.base.condition.unlockCondition r.condition condition
    | _ => pure ()
  pure ok

/--
Julia source: base/task.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_abandon!(t::Task, next_task::Task) =
    unsafe_abandon!(t, next_task, CancellationRequest(0x4)) # CANCEL_REQUEST_ABANDON_ALL
```
-/
def unsafeAbandonDefault {Async : Type} (a : AbandonRuntime E W Task Async Value)
    (task next : Task) : M E W Bool := unsafeAbandon r a task next (.cancellation 4)

/--
Julia source: base/task.jl:988-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrap_task_failed(f::Function, t::UnwrapTaskFailedException)
    try
        f(t.task)
    catch ex
        if ex isa TaskFailedException
            throw(ex.task.exception)
        else
            rethrow()
        end
    end
end
```
-/
def unwrapTaskFailed {A : Type} (body : Task → M E W A) (task : Task) : M E W A :=
  tryCatch (body task) (fun error => do
    match r.failedTaskOfError error with
    | none => throw error
    | some failed =>
      if ← r.isException failed then throw (r.payloadError (← r.result failed))
      throw (r.payloadError .nothing))

/--
Julia source: base/task.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait(t::UnwrapTaskFailedException) = unwrap_task_failed(wait, t)
```
-/
def waitUnwrap (task : Task) : M E W Unit :=
  unwrapTaskFailed r (fun task => wait r task) task

/--
Julia source: base/task.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fetch(t::UnwrapTaskFailedException) = unwrap_task_failed(fetch, t)
```
-/
def fetchUnwrap (task : Task) : M E W (WakeValue Value) :=
  unwrapTaskFailed r (fun task => fetch r task) task

/--
Julia source: base/task.jl:16-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function CapturedException(ex, bt_raw::Vector)
        # bt_raw MUST be a vector that can be processed by StackTraces.stacktrace
        # Typically the result of a catch_backtrace()

        # Process bt_raw so that it can be safely serialized
        bt_lines = process_backtrace(stacktrace(bt_raw))[1:min(100, end)] # Limiting this to 100 lines.
        CapturedException(ex, bt_lines)
    end
```
-/
def capturedExceptionRaw {V Raw Trace Frame : Type}
    (stacktrace : List Raw → M E W Trace) (processBacktrace : Trace → M E W (List Frame))
    (exception : V) (raw : List Raw) : M E W (CapturedException V Frame) := do
  let lines ← processBacktrace (← stacktrace raw)
  pure ⟨exception, lines.take (min 100 lines.length)⟩

/--
Julia source: base/task.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CapturedException(ex, processed_bt::Vector{Any}) = new(ex, processed_bt)
```
-/
def capturedExceptionProcessed {V Frame : Type} (exception : V) (processed : List Frame) : CapturedException V Frame :=
  ⟨exception, processed⟩

/--
Julia source: base/task.jl:28-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ce::CapturedException)
    showerror(io, ce.ex, ce.processed_bt, backtrace=true)
end
```
-/
def showCapturedException {IO V Frame : Type}
    (showError : IO → V → List Frame → Bool → M E W Unit)
    (io : IO) (exception : CapturedException V Frame) : M E W Unit :=
  showError io exception.exception exception.processedBacktrace true

/--
Julia source: base/task.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
capture_exception(ex, bt) = CapturedException(ex, bt)
```
-/
def captureException {V Raw Frame : Type} (capture : V → Raw → M E W (CapturedException V Frame))
    (exception : V) (backtrace : Raw) : M E W (CapturedException V Frame) := capture exception backtrace

/--
Julia source: base/task.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CompositeException() = new(Any[])
```
-/
def compositeExceptionEmpty {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State) :
    M E W (CompositeException Exceptions) := do
  pure ⟨← ops.newEmpty⟩

/--
Julia source: base/task.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CompositeException(exceptions) = new(exceptions)
```
-/
def compositeException {Input Exceptions : Type} (convert : Input → M E W Exceptions)
    (exceptions : Input) : M E W (CompositeException Exceptions) := do
  pure ⟨← convert exceptions⟩

/--
Julia source: base/task.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(c::CompositeException) = length(c.exceptions)
```
-/
def compositeExceptionLength {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State)
    (exception : CompositeException Exceptions) : M E W I := ops.length exception.exceptions

/--
Julia source: base/task.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(c::CompositeException, ex) = push!(c.exceptions, ex)
```
-/
def compositeExceptionPush {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State)
    (exception : CompositeException Exceptions) (value : V) : M E W Exceptions := ops.push exception.exceptions value

/--
Julia source: base/task.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pushfirst!(c::CompositeException, ex) = pushfirst!(c.exceptions, ex)
```
-/
def compositeExceptionPushFirst {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State)
    (exception : CompositeException Exceptions) (value : V) : M E W Exceptions := ops.pushFirst exception.exceptions value

/--
Julia source: base/task.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(c::CompositeException) = isempty(c.exceptions)
```
-/
def compositeExceptionIsEmpty {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State)
    (exception : CompositeException Exceptions) : M E W Bool := ops.isEmpty exception.exceptions

/--
Julia source: base/task.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(c::CompositeException, state...) = iterate(c.exceptions, state...)
```
-/
def compositeExceptionIterate {V Exceptions State : Type} (ops : ExceptionVectorOps E W V Exceptions State)
    (exception : CompositeException Exceptions) (state : Option State := none) : M E W (Option (V × State)) :=
  ops.iterate exception.exceptions state

/--
Julia source: base/task.jl:1695-1695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    pause() = ccall(:Sleep, stdcall, Cvoid, (UInt32,), 0xffffffff)
```
-/
def pauseWindows (sleep : UInt32 → M E W Unit) : M E W Unit := sleep 0xffffffff

/--
Julia source: base/task.jl:1697-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    pause() = ccall(:pause, Cvoid, ())
```
-/
def pausePosix (pause : M E W Unit) : M E W Unit := pause

/--
Julia source: base/task.jl:1108-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repl_backend_task()
    @isdefined(active_repl_backend) || return
    backend = active_repl_backend
    isdefined(backend, :backend_task) || return
    backend_task = getfield(active_repl_backend, :backend_task)::Task
    if backend_task._state === task_state_runnable && getfield(backend, :in_eval)
        return backend_task
    end
    return
end
```
-/
def replBackendTask {Backend : Type} (b : BackendRuntime E W Task Backend) : M E W (Option Task) := do
  if !(← b.activeIsDefined) then return none
  let backend ← b.active
  if !(← b.hasBackendTask backend) then return none
  let task ← b.backendTask (← b.active)
  if (← r.loadState .plain task) == 0 then
    if ← b.inEval backend then return some task
  pure none

/--
Julia source: base/task.jl:1120-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function task_done_hook(t::Task)
    # a sticky cancellation-source registration of this task is garbage now
    w = t.cached_cancel_entry
    if w isa WaitEntry2
        o = @atomic :monotonic w.owner2
        o isa CancellationTokenSource && _note_dead_registration!(o)
    end
    # `finish_task` sets `sigatomic` before entering this function
    err = istaskfailed(t)
    result = task_result(t)
    handled = false

    donenotify = t.donenotify
    if isa(donenotify, ThreadSynchronizer)
        lock(donenotify)
        try
            if !isempty(donenotify.waitq)
                # only wakes whose claim was won count as having consumed the
                # result (a stale, already-claimed registration does not)
                handled = notify(donenotify) > 0
            end
        finally
            unlock(donenotify)
        end
    end

    if err && !handled && Threads.threadid() == 1
        if isa(result, InterruptException) && isempty(Workqueue)
            backend = repl_backend_task()
            backend isa Task && throwto(backend, result)
        end
    end
    # Clear sigatomic before waiting
    sigatomic_end()
    try
        wait() # this will not return
    catch e
        # If an InterruptException happens while blocked in the event loop, try handing
        # the exception to the REPL task since the current task is done.
        # issue #19467
        if Threads.threadid() == 1 && isa(e, InterruptException) && isempty(Workqueue)
            backend = repl_backend_task()
            backend isa Task && throwto(backend, e)
        end
        rethrow() # this will terminate the program
    end
end
```
-/
def taskDoneHook {Backend : Type} (b : BackendRuntime E W Task Backend) (task : Task) : M E W (WakeValue Value) := do
  match ← r.cachedCancelEntry2 task with
  | some entry =>
    match ← r.cancelEntryOwner2 .monotonic entry with
    | some source => r.noteDeadRegistration source
    | none => pure ()
  | none => pure ()
  let err ← istaskfailed r task
  let result ← taskResult r task
  let mut handled := false
  match ← r.doneNotify task with
  | .condition condition =>
    JuliaLean.base.condition.lockCondition r.condition condition
    handled ← finallyDo (do
      if !(← JuliaLean.base.condition.isempty r.condition condition) then
        return (← JuliaLean.base.condition.notifyKw r.condition condition).val > 0
      pure false) (JuliaLean.base.condition.unlockCondition r.condition condition)
  | _ => pure ()
  if err && !handled then
    if (← JuliaLean.base.threadingconstructs.threadid r.condition.queries).val == 1 then
      if r.resultIsInterrupt result then
        if ← workqueueEmpty r (← r.globalWorkqueue) then
          match ← replBackendTask r b with
          | some backend => let _ ← throwto r backend result; pure ()
          | none => pure ()
  r.sigatomicEnd
  tryCatch (waitScheduler r) (fun error => do
    if (← JuliaLean.base.threadingconstructs.threadid r.condition.queries).val == 1 then
      if r.errorIsInterrupt error then
        if ← workqueueEmpty r (← r.globalWorkqueue) then
          match ← replBackendTask r b with
          | some backend => let _ ← throwto r backend (r.errorPayload error); pure ()
          | none => pure ()
    throw error)

/--
Julia source: base/task.jl:1543-1586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_forever()
    while true
        try
            while true
                wait()
            end
        catch e
            if Threads.threadid() == 1 && isa(e, InterruptException) && isempty(Workqueue)
                # An InterruptException landed on this internal scheduler task while
                # the thread was idle (it parked here after running a completed task).
                # N.B.: SIGINT no longer force-throws InterruptException on any
                # platform (it cancels the ^C episode source instead), so this
                # branch is reachable only via an explicit user/library throw
                # (`throwto`, `schedule(..., error=...)`) into a scheduler
                # task; kept as defense in depth.
                # Forward it to a task that can observe it: the REPL backend if it is
                # evaluating user code; nothing at an idle REPL prompt (drop it); the
                # root task otherwise, e.g. a non-interactive script blocked in wait
                # (#58689).
                victim = repl_backend_task()
                if !(victim isa Task)
                    at_repl_prompt = @isdefined(active_repl_backend) && active_repl_backend !== nothing
                    victim = (at_repl_prompt || istaskdone(roottask)) ? nothing : roottask
                end
                if victim isa Task
                    try
                        throwto(victim, e)
                    catch
                        # delivery is best-effort: the victim may have been
                        # rescheduled concurrently, or a second interrupt may arrive
                        # while this task is suspended in the switch
                    end
                end
            else
                local errs = stderr
                # try to display the failure atomically
                errio = IOContext(PipeBuffer(), errs::IO)
                emphasize(errio, "Internal Task ")
                display_error(errio, current_exceptions())
                write(errs, errio)
            end
        end
    end
end
```
-/
def waitForever {Backend IO Buffer Context Stack : Type} (b : BackendRuntime E W Task Backend)
    (d : DiagnosticRuntime E W IO Buffer Context Stack) : M E W (WakeValue Value) :=
  loop (fun (_ : Unit) => do
    tryCatch (loop (fun (_ : Unit) => do
      let _ ← waitScheduler r
      pure (.inr ())) ()) (fun error => do
      let mut idleInterrupt := false
      if (← JuliaLean.base.threadingconstructs.threadid r.condition.queries).val == 1 then
        if r.errorIsInterrupt error then idleInterrupt ← workqueueEmpty r (← r.globalWorkqueue)
      if idleInterrupt then
        let mut victim ← replBackendTask r b
        if victim.isNone then
          let mut atPrompt := false
          if ← b.activeIsDefined then atPrompt := !(b.isNothing (← b.active))
          let root ← r.rootTask
          victim ← if atPrompt then pure none else if ← istaskdone r root then pure none else pure (some root)
        match victim with
        | some task =>
          tryCatch (do let _ ← throwto r task (r.errorPayload error); pure ()) (fun _ => pure ())
        | none => pure ()
      else
        let errors ← d.stderr
        let io ← d.ioContext (← d.pipeBuffer) errors
        d.emphasize io "Internal Task "
        d.displayError io (← d.currentExceptions)
        let _ ← d.write errors io
        pure ())
    pure (.inr ())) ()

/--
Julia source: base/task.jl:1588-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _new_sched_task()
    ct = current_task()
    rngState0 = ct.rngState0
    rngState1 = ct.rngState1
    rngState2 = ct.rngState2
    rngState3 = ct.rngState3
    rngState4 = ct.rngState4
    t = Task(wait_forever)
    ct.rngState0 = rngState0
    ct.rngState1 = rngState1
    ct.rngState2 = rngState2
    ct.rngState3 = rngState3
    ct.rngState4 = rngState4
    return t
end
```
-/
def newSchedulerTask (waitForever : M E W (WakeValue Value)) : M E W Task := do
  let current ← r.condition.currentTask
  let state0 ← r.rngState current 0
  let state1 ← r.rngState current 1
  let state2 ← r.rngState current 2
  let state3 ← r.rngState current 3
  let state4 ← r.rngState current 4
  let task ← newTask r waitForever
  r.setRngState current 0 state0
  r.setRngState current 1 state1
  r.setRngState current 2 state2
  r.setRngState current 3 state3
  r.setRngState current 4 state4
  pure task

/--
Julia source: base/task.jl:61-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::CompositeException)
    if !isempty(ex)
        showerror(io, ex.exceptions[1])
        remaining = length(ex) - 1
        if remaining > 0
            print(io, "\n\n...and ", remaining, " more exception", remaining > 1 ? "s" : "", ".\n")
        end
    else
        print(io, "CompositeException()\n")
    end
end
```
-/
def showCompositeException {IO Buffer Context Backtrace Color Exceptions State : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color)
    (v : ExceptionVectorOps E W Value Exceptions State) (get : Exceptions → I → M E W Value)
    (io : IO) (exception : CompositeException Exceptions) : M E W Unit := do
  if !(← v.isEmpty exception.exceptions) then
    d.showError io (← get exception.exceptions (int 1))
    let remaining := (← v.length exception.exceptions) - int 1
    if remaining.val > 0 then
      d.print io [.text "\n\n...and ", .integer remaining, .text " more exception",
        .text (if remaining.val > 1 then "s" else ""), .text ".\n"]
  else d.print io [.text "CompositeException()"]

/--
Julia source: base/task.jl:93-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_task_exception(io::IO, t::Task; indent = true)
    stack = current_exceptions(t)
    b = IOBuffer()
    if isempty(stack)
        # exception stack buffer not available; probably a serialized task
        showerror(IOContext(b, io), t.result)
    else
        show_exception_stack(IOContext(b, io), stack)
    end
    str = takestring!(b)
    if indent
        str = replace(str, "\n" => "\n    ")
    end
    print(io, str)
end
```
-/
def showTaskException {IO Buffer Context Backtrace Color : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color)
    (io : IO) (task : Task) (indent : Bool := true) : M E W Unit := do
  let stack ← d.currentExceptions task
  let buffer ← d.newBuffer
  if stack.isEmpty then d.showContextError (← d.ioContext buffer io) (← r.result task)
  else d.showExceptionStack (← d.ioContext buffer io) stack
  let text ← d.takeString buffer
  let text := if indent then text.replace "\n" "\n    " else text
  d.print io [.text text]

/--
Julia source: base/task.jl:83-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::TaskFailedException, bt = nothing; backtrace=true)
    print(io, "TaskFailedException")
    if bt !== nothing && backtrace
        show_backtrace(io, bt)
    end
    println(io)
    printstyled(io, "\n    nested task error: ", color=error_color())
    show_task_exception(io, ex.task)
end
```
-/
def showTaskFailedException {IO Buffer Context Backtrace Color : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color)
    (io : IO) (task : Task) (backtrace : Option Backtrace := none)
    (includeBacktrace : Bool := true) : M E W Unit := do
  d.print io [.text "TaskFailedException"]
  match backtrace with
  | some backtrace => if includeBacktrace then d.showBacktrace io backtrace
  | none => pure ()
  d.println io
  d.printStyled io "\n    nested task error: " (← d.errorColor)
  showTaskException r d io task

/--
Julia source: base/task.jl:109-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, t::Task)
    state = t.state
    state_str = "$state" * ((state == :runnable && istaskstarted(t)) ? ", started" : "")
    print(io, "Task ($state_str) @0x$(string(convert(UInt, pointer_from_objref(t)), base = 16, pad = Sys.WORD_SIZE>>2))")
end
```
-/
def showTask {IO Buffer Context Backtrace Color : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color) (io : IO) (task : Task) : M E W Unit := do
  let state ← r.loadState .acquire task
  let text ← if state == 0 then pure "runnable"
    else if state == 1 then pure "done"
    else if state == 2 then pure "failed"
    else if state == 3 then pure "abandoned"
    else throw (r.assertionError "unexpected state")
  let mut started := false
  if state == 0 then started ← istaskstarted r task
  let text := text ++ (if started then ", started" else "")
  let pointer ← d.pointerToUnsigned (← d.pointerFromObject task)
  let address ← d.stringUnsigned pointer (int 16) (int 16)
  d.print io [.text ("Task (" ++ text ++ ") @0x" ++ address)]

/--
Julia source: base/task.jl:750-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, cr::CancellationRequest)
    print(io, "CancellationRequest: ")
    if cr === CANCEL_REQUEST_SAFE
        print(io, "Safe Cancellation (CANCEL_REQUEST_SAFE)")
    elseif cr === CANCEL_REQUEST_ABANDON_EXTERNAL
        print(io, "Abandonment of External Resources (CANCEL_REQUEST_ABANDON_EXTERNAL)")
    elseif cr === CANCEL_REQUEST_ABANDON_ALL
        print(io, "Task Abandonment (CANCEL_REQUEST_ABANDON_ALL)")
    else
        print(io, "Unknown ($(cr.request))")
    end
end
```
-/
def showCancellationRequest {IO Buffer Context Backtrace Color : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color) (io : IO) (request : UInt8) : M E W Unit := do
  d.print io [.text "CancellationRequest: "]
  if request == 1 then d.print io [.text "Safe Cancellation (CANCEL_REQUEST_SAFE)"]
  else if request == 3 then d.print io [.text "Abandonment of External Resources (CANCEL_REQUEST_ABANDON_EXTERNAL)"]
  else if request == 4 then d.print io [.text "Task Abandonment (CANCEL_REQUEST_ABANDON_ALL)"]
  else d.print io [.text ("Unknown (" ++ (← d.formatRequest request) ++ ")")]

/--
Julia source: base/task.jl:763-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::ScheduledAfterSyncException)
    print(io, "ScheduledAfterSyncException: ")
    if isempty(ex.values)
        print(io, "(no values)")
        return
    end
    show(io, ex.values[1])
    if length(ex.values) == 1
        print(io, " is")
    elseif length(ex.values) == 2
        print(io, " and one more ")
        print(io, nameof(typeof(ex.values[2])))
        print(io, " are")
    else
        print(io, " and ", length(ex.values) - 1, " more objects are")
    end
    print(io, " registered after the end of a `@sync` block")
end
```
-/
def showScheduledAfterSyncException {IO Buffer Context Backtrace Color Exceptions State : Type}
    (d : DisplayRuntime E W IO Buffer Context Task Value Backtrace Color)
    (v : ExceptionVectorOps E W Value Exceptions State) (get : Exceptions → I → M E W Value)
    (io : IO) (values : Exceptions) : M E W Unit := do
  d.print io [.text "ScheduledAfterSyncException: "]
  if ← v.isEmpty values then
    d.print io [.text "(no values)"]
    return ()
  d.showValue io (← get values (int 1))
  if (← v.length values).val == 1 then d.print io [.text " is"]
  else if (← v.length values).val == 2 then
    d.print io [.text " and one more "]
    d.print io [.text (← d.typeName (← get values (int 2)))]
    d.print io [.text " are"]
  else d.print io [.text " and ", .integer ((← v.length values) - int 1), .text " more objects are"]
  d.print io [.text " registered after the end of a `@sync` block"]

/--
Julia source: base/task.jl:848-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function sync_cancel!(c::Channel{Any}, t::Task, cr::CancellationRequest,
                                tok::CancellationToken, c_ex::CompositeException)
    waitees = Any[t]
    while isready(c)
        push!(waitees, take!(c))
    end
    close(c)
    sev = severity(cr)
    for r in waitees
        if isa(r, Task)
            while sev < CANCEL_REQUEST_ABANDON_ALL.request
                # Tasks are internal: their cancellation is awaited (for
                # ABANDON_ALL they were frozen; there is nothing to wait
                # for). A severity escalation completes the teardown wait
                # (value-mode; only severities above the acknowledged one
                # are admitted) - adopt the stronger request and keep
                # awaiting internal tasks per its policy rather than
                # unwinding out of the `@sync` while children are still
                # running.
                r2 = _wait(r, tok; min_severity=sev + 0x01, cancel_value=true)
                r2 isa CancellationRequest || break
                cr = r2
                sev = severity(r2)
            end
            if istaskfailed(r)
                push!(c_ex, TaskFailedException(r))
            end
        else
            # Non-task waitees are external - the ABANDON_* severities cease
            # waiting for external resources.
            sev == CANCEL_REQUEST_SAFE.request || continue
            try
                wait(r)
            catch e
                push!(c_ex, e)
            end
        end
    end
    # Reporting the composite outcome constitutes delivery of the request;
    # include the request itself if no child failure already records it.
    if isempty(c_ex)
        throw(cr)
    end
    throw(c_ex)
end
```
-/
def syncCancel {Channel Other Failures Waitees Iter : Type}
    (p : SyncRuntime E W Channel Task Other Failures Waitees Iter Token Source)
    (channel : Channel) (task : Task) (request : UInt8) (token : Token) (failures : Failures) : M E W Unit := do
  let waitees ← p.singletonWaitees task
  loop (fun (_ : Unit) => do
    if !(← p.isReady channel) then return .inl ()
    p.pushWaitee waitees (← p.take channel)
    pure (.inr ())) ()
  p.close channel
  let request ← loop (fun (state : Option Iter × UInt8) => do
    match ← p.waiteesNext waitees state.1 with
    | none => pure (.inl state.2)
    | some (waitee, next) =>
      let request ← match waitee with
        | .inl task => do
          let request ← loop (fun (severity : UInt8) => do
            if severity ≥ 4 then return .inl severity
            let result ← waitToken r task (some token) (severity + 1) true
            match result with
            | .cancellation next => pure (.inr next)
            | _ => pure (.inl severity)) state.2
          if ← istaskfailed r task then p.pushFailure failures (r.taskFailedException task)
          pure request
        | .inr other => do
          if state.2 == 1 then
            tryCatch (p.waitOther other) (fun error => p.pushFailure failures error)
          pure state.2
      pure (.inr (some next, request))) (none, request)
  if ← p.failuresEmpty failures then throw (p.cancellationError request)
  throw (p.failureError failures)

/--
Julia source: base/task.jl:782-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sync_end(c::Channel{Any}, src::Union{Nothing, CancellationTokenSource}=nothing)
    local c_ex
    tok = src === nothing ? nothing : CancellationToken(src)
    while isready(c)
        r = take!(c)
        if isa(r, Task)
            cancelled = _wait(r, tok; cancel_value=tok !== nothing)
            if cancelled isa CancellationRequest
                # Our own scope (or an ancestor) was cancelled. The children
                # run under the same scope's token, so the tree walk already
                # cancelled them all; await their teardown per severity.
                return sync_cancel!(c, r, cancelled, tok,
                                    @isdefined(c_ex) ? c_ex : CompositeException())
            end
            if istaskfailed(r)
                if !@isdefined(c_ex)
                    c_ex = CompositeException()
                end
                push!(c_ex, TaskFailedException(r))
            end
        else
            try
                wait(r)
            catch e
                if !@isdefined(c_ex)
                    c_ex = CompositeException()
                end
                push!(c_ex, e)
            end
        end
    end
    close(c)

    # Capture all waitable objects scheduled after the end of `@sync` and
    # include them in the exception. This way, the user can check what was
    # scheduled by examining at the exception object.
    if isready(c)
        local racy
        for r in c
            if !@isdefined(racy)
                racy = []
            end
            push!(racy, r)
        end
        if @isdefined(racy)
            if !@isdefined(c_ex)
                c_ex = CompositeException()
            end
            # Since this is a clear programming error, show this exception first:
            pushfirst!(c_ex, ScheduledAfterSyncException(racy))
        end
    end

    if @isdefined(c_ex)
        throw(c_ex)
    end
    nothing
end
```
-/
def ensureSyncFailures {Channel Other Failures Waitees Iter : Type}
    (p : SyncRuntime E W Channel Task Other Failures Waitees Iter Token Source) : M E (Option Failures × W) Failures := do
  match ← getFrame with
  | some failures => pure failures
  | none =>
    let failures ← liftFrame p.newFailures
    setFrame (some failures)
    pure failures

def syncEnd {Channel Other Failures Waitees Iter : Type}
    (p : SyncRuntime E W Channel Task Other Failures Waitees Iter Token Source)
    (channel : Channel) (source : Option Source := none) : M E W Unit := do
  let token := source.map p.tokenOf
  runFrame (none : Option Failures) (do
    let cancelled ← loop (fun (_ : Unit) => do
      if !(← liftFrame (p.isReady channel)) then return .inl none
      match ← liftFrame (p.take channel) with
      | .inl task =>
        let result ← liftFrame (waitToken r task token 0 token.isSome)
        match result with
        | .cancellation severity => return .inl (some (task, severity))
        | _ => pure ()
        if ← liftFrame (istaskfailed r task) then
          let failures ← ensureSyncFailures p
          liftFrame (p.pushFailure failures (r.taskFailedException task))
      | .inr other =>
        tryCatch (liftFrame (p.waitOther other)) (fun error => do
          let failures ← ensureSyncFailures p
          liftFrame (p.pushFailure failures error))
      pure (.inr ())) ()
    match cancelled with
    | some (task, severity) =>
      let failures ← ensureSyncFailures p
      let concreteToken ← liftFrame (p.requireToken token)
      return ← liftFrame (syncCancel r p channel task severity concreteToken failures)
    | none => pure ()
    liftFrame (p.close channel)
    if ← liftFrame (p.isReady channel) then
      let racy ← loop (fun (state : Option Iter × Option Waitees) => do
        match ← liftFrame (p.channelNext channel state.1) with
        | none => pure (.inl state.2)
        | some (waitee, next) =>
          let racy ← match state.2 with
            | some racy => pure racy
            | none => liftFrame p.emptyWaitees
          liftFrame (p.pushWaitee racy waitee)
          pure (.inr (some next, some racy))) (none, none)
      match racy with
      | some racy =>
        let failures ← ensureSyncFailures p
        let error ← liftFrame (p.scheduledAfterError racy)
        liftFrame (p.pushFirstFailure failures error)
      | none => pure ()
    match ← getFrame with
    | some failures => throw (p.failureError failures)
    | none => pure ())

-- UNTRANSLATED
-- Source: base/task.jl:145-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro task(ex)
--     thunk = replace_linenums!(:(()->$(esc(ex))), __source__)
--     :(Task($thunk))
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime task/synchronization functions are modelled.

-- UNTRANSLATED
-- Source: base/task.jl:915-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro sync(block)
--     var = esc(sync_varname)
--     # The block runs in a new dynamic scope carrying the token of a fresh
--     # cancellation source linked under the enclosing scope's token, so that
--     # cancellation of the enclosing scope reaches every (transitively
--     # spawned) child through the token tree. This expands the equivalent of
--     # `@with CANCEL_TOKEN => token ...` manually: the ScopedValues macro API
--     # is not loaded yet when Base code containing `@sync` is compiled during
--     # bootstrap.
--     scoped_block = Expr(:tryfinally, esc(block), nothing,
--         :(Scope(Core.current_scope()::Union{Nothing, Scope},
--                 CANCEL_TOKEN => CancellationToken(var"#sync_src#"))))
--     quote
--         let var"#sync_src#" = CancellationTokenSource(default_cancel_token()),
--             $var = Channel(Inf)
--             v = $scoped_block
--             sync_end($var, var"#sync_src#")
--             v
--         end
--     end
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime task/synchronization functions are modelled.

-- UNTRANSLATED
-- Source: base/task.jl:959-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro async(expr)
--     do_async_macro(expr, __source__, identity)
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime task/synchronization functions are modelled.

/--
Julia source: base/task.jl:965-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function do_async_macro(expr, linenums, wrap)
    letargs = _lift_one_interp!(expr)

    thunk = replace_linenums!(:(()->($(esc(expr)))), linenums)
    var = esc(sync_varname)
    quote
        let $(letargs...)
            local task = Task($thunk)
            if $(Expr(:islocal, var))
                put!($var, $(wrap(:task)))
            end
            schedule(task)
            task
        end
    end
end
```
-/
def do_async_macro {L S : Type} (lo : JuliaLean.base.expr.LeafOps L)
    (sync_varname : String) (expr linenums : JuliaLean.base.expr.Value L)
    (wrap : JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L)
    (_lift_one_interp! : JuliaLean.base.expr.Value L → S → ExceptT JuliaLean.base.expr.ExprError Option
      (List (JuliaLean.base.expr.Value L) × JuliaLean.base.expr.Value L × S)) (state : S) :
    ExceptT JuliaLean.base.expr.ExprError Option (JuliaLean.base.expr.Value L × S) := do
  let (letargs, expr, state) ← _lift_one_interp! expr state
  let ln ← match linenums with
    | .lineNumberNode line file => pure (line, file)
    | _ => throw (.jl (.methodError "replace_linenums!"))
  let thunk ← ExceptT.lift (JuliaLean.base.expr.replace_linenums! lo ln
    (.expr "->" [.expr "tuple" [], .expr "block" [taskLine 968, JuliaLean.base.expr.esc expr]]))
  let var := JuliaLean.base.expr.esc (.symbol sync_varname)
  pure (.expr "block" [taskLine 971,
    .expr "let" [.expr "block" letargs, .expr "block" [
      taskLine 972,
      .expr "local" [.expr "=" [.symbol "task", .expr "call" [.symbol "Task", thunk]]],
      taskLine 973,
      .expr "if" [.expr "islocal" [var], .expr "block" [
        taskLine 974,
        .expr "call" [.symbol "put!", var, wrap (.symbol "task")]]],
      taskLine 976,
      .expr "call" [.symbol "schedule", .symbol "task"],
      taskLine 977,
      .symbol "task"]]], state)
where
  /-- The line-number node `#= task.jl:line =#` of the quoted code. -/
  taskLine (line : Int) : JuliaLean.base.expr.Value L :=
    .lineNumberNode (JInt.wrap .i64 line) (.symbol "task.jl")

/-- The state of `_lift_one_interp_helper`: the `letargs` vector and the `gensym` counter. -/
abbrev LiftM (L S : Type) :=
  StateT (List (JuliaLean.base.expr.Value L) × S) (ExceptT JuliaLean.base.expr.ExprError Option)

/-- An `ExprResult` computation of `base/expr.jl` in `LiftM`. -/
def liftExprResult {L S α : Type} (r : JuliaLean.base.expr.ExprResult α) : LiftM L S α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

-- UNTRANSLATED
-- Source: base/task.jl:1007-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro async_unwrap(expr)
--     do_async_macro(expr, __source__, taskvar->:(UnwrapTaskFailedException($taskvar)))
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime task/synchronization functions are modelled.

/--
Julia source: base/task.jl:1062-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _lift_one_interp!(@nospecialize e)
    letargs = Any[]  # store the new gensymed arguments
    _lift_one_interp_helper(e, false, 0, letargs) # Start out _not_ in a quote context (false) and not needing escapes
    return letargs
end
```
-/
def _lift_one_interp! {L S : Type}
    (_lift_one_interp_helper : JuliaLean.base.expr.Value L → Bool → JInt64 → LiftM L S (JuliaLean.base.expr.Value L))
    (e : JuliaLean.base.expr.Value L) (state : S) :
    ExceptT JuliaLean.base.expr.ExprError Option
      (List (JuliaLean.base.expr.Value L) × JuliaLean.base.expr.Value L × S) := do
  -- `e` after its mutation is returned with the new arguments
  let (e, letargs, state) ← (_lift_one_interp_helper e false (JInt.wrap .i64 0)).run ([], state)
  pure (letargs, e, state)

/--
Julia source: base/task.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_lift_one_interp_helper(@nospecialize(v), _::Bool, _::Int, _::Vector{Any}) = v
```
-/
def _lift_one_interp_helper_Any {L S : Type} (v : JuliaLean.base.expr.Value L) :
    LiftM L S (JuliaLean.base.expr.Value L) := pure v

mutual
/--
Julia source: base/task.jl:1068-1095 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _lift_one_interp_helper(expr::Expr, in_quote_context::Bool, escs::Int, letargs::Vector{Any})
    if expr.head === :$
        if in_quote_context  # This $ is simply interpolating out of the quote
            # Now, we're out of the quote, so any _further_ $ is ours.
            in_quote_context = false
        elseif escs == 0
            # if escs is non-zero, then we cannot hoist expr.args without violating hygiene rules
            newarg = gensym()
            push!(letargs, :($(esc(newarg)) = $(esc(expr.args[1]))))
            return newarg  # Don't recurse into the lifted $() exprs
        end
    elseif expr.head === :meta || expr.head === :inert
        return expr
    elseif expr.head === :quote
        in_quote_context = true   # Don't try to lift $ directly out of quotes
    elseif expr.head === :macrocall
        return expr  # Don't recur into macro calls, since some other macros use $
    elseif expr.head === :var"hygienic-scope"
        escs += 1
    elseif expr.head === :escape
        escs == 0 && return expr
        escs -= 1
    end
    for (i,e) in enumerate(expr.args)
        expr.args[i] = _lift_one_interp_helper(e, in_quote_context, escs, letargs)
    end
    expr
end
```
-/
-- `_lift_one_interp_helper(v, in_quote_context, escs, letargs)`; a non-`Expr` `v` is returned.
def _lift_one_interp_helper {L S : Type} (go : JuliaLean.base.expr.GensymOps S)
    (expr : JuliaLean.base.expr.Value L) (in_quote_context : Bool) (escs : JInt64) :
    LiftM L S (JuliaLean.base.expr.Value L) := do
  match expr with
  | .expr head args =>
    let mut in_quote_context := in_quote_context
    let mut escs := escs
    if head == "$" then
      if in_quote_context then
        in_quote_context := false
      else if escs.val == 0 then
        let (letargs, state) ← get
        let (newarg, state) := go.untagged state
        set (letargs, state)
        let arg ← liftExprResult (JuliaLean.base.expr.argAt args 1)
        set (letargs ++ [.expr "=" [JuliaLean.base.expr.esc (.symbol newarg), JuliaLean.base.expr.esc arg]],
          state)
        return .symbol newarg
    else if head == "meta" || head == "inert" then
      return expr
    else if head == "quote" then
      in_quote_context := true
    else if head == "macrocall" then
      return expr
    else if head == "hygienic-scope" then
      escs := escs + JInt.wrap .i64 1
    else if head == "escape" then
      if escs.val == 0 then return expr
      escs := escs - JInt.wrap .i64 1
    return .expr head (← _lift_one_interp_args go args in_quote_context escs)
  | _ => _lift_one_interp_helper_Any expr
partial_fixpoint

-- The `for (i,e) in enumerate(expr.args)` loop: the arguments after their replacement.
def _lift_one_interp_args {L S : Type} (go : JuliaLean.base.expr.GensymOps S)
    (args : List (JuliaLean.base.expr.Value L)) (in_quote_context : Bool) (escs : JInt64) :
    LiftM L S (List (JuliaLean.base.expr.Value L)) := do
  match args with
  | [] => return []
  | e :: rest =>
    let e ← _lift_one_interp_helper go e in_quote_context escs
    return e :: (← _lift_one_interp_args go rest in_quote_context escs)
partial_fixpoint
end

-- UNTRANSLATED
-- Source: base/task.jl:1099-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro sync_add(expr)
--     var = esc(sync_varname)
--     quote
--         local ref = $(esc(expr))
--         put!($var, ref)
--         ref
--     end
-- end
-- /Source
-- Reason: Compile-time Julia AST quotation, escaping, and macro expansion are untranslated; the corresponding runtime task/synchronization functions are modelled.


end

end JuliaLean.base.task

namespace JuliaLean.Tasks



inductive TaskState where
  | runnable
  | done
  | failed
  | abandoned
  deriving Repr, DecidableEq

/-- The observable task phases behind `base/task.jl:150-269,1234-1490`.
The Boolean on `queued` and `failed` records the runtime's independent
"has started" bit. An empty thread pool can fail a queued task before start. -/
inductive TaskPhase where
  | created
  | queued (started : Bool)
  | running
  | waiting
  | done (value : Nat)
  | failed (error : Nat) (started : Bool)
  | abandoned
  deriving Repr, DecidableEq

def taskState : TaskPhase → TaskState
  | .created | .queued _ | .running | .waiting => .runnable
  | .done _ => .done
  | .failed _ _ => .failed
  | .abandoned => .abandoned

/-- `istaskdone`, `base/task.jl:223`: every state other than runnable is done. -/
def istaskdone (t : TaskPhase) : Bool := taskState t != .runnable

/-- `istaskstarted`, `base/task.jl:240`: queued fresh tasks have not run yet. -/
def istaskstarted : TaskPhase → Bool
  | .created => false
  | .queued started => started
  | .failed _ started => started
  | .running | .waiting | .done _ | .abandoned => true

/-- `istaskfailed`, `base/task.jl:267-270`: abandoned tasks count as failed. -/
def istaskfailed (t : TaskPhase) : Bool :=
  taskState t == .failed || taskState t == .abandoned

inductive TaskAction where
  | schedule
  | start
  | yield
  | wait
  | wake
  | finish (value : Nat)
  | fail (error : Nat)
  | failEmptyPool (error : Nat)
  | abandon
  deriving Repr, DecidableEq

/-- Relevant branches of `schedule`, `yield`, `wait`, task completion, and
abandonment (`base/task.jl:1234-1490,1661-1691`). Invalid scheduler actions
leave the task unchanged, matching the model's restriction to legal steps. -/
def taskStep (action : TaskAction) (t : TaskPhase) : TaskPhase :=
  match action, t with
  | .schedule, .created => .queued false
  | .schedule, .waiting => .queued true
  | .start, .queued _ => .running
  | .yield, .running => .queued true
  | .wait, .running => .waiting
  | .wake, .waiting => .queued true
  | .finish value, .running => .done value
  | .fail error, .running => .failed error true
  | .failEmptyPool error, .queued started => .failed error started
  | .abandon, .running => .abandoned
  | _, _ => t

structure ScheduledAction where
  task : Nat
  action : TaskAction
  deriving Repr, DecidableEq

abbrev Scheduler := Nat → TaskPhase

def schedulerStep (event : ScheduledAction) (s : Scheduler) : Scheduler :=
  fun i => if i = event.task then taskStep event.action (s event.task) else s i

def schedulerRun : List ScheduledAction → Scheduler → Scheduler
  | [], s => s
  | event :: events, s => schedulerRun events (schedulerStep event s)

inductive TaskError where
  | taskFailed
  deriving Repr, DecidableEq

inductive Await (α : Type) where
  | blocked
  | returned (value : α)
  | threw (error : TaskError)
  deriving Repr, DecidableEq

/-- `wait(t; throw=true)`, `base/task.jl:494-509`. -/
def waitTask : TaskPhase → Await Unit
  | .done _ => .returned ()
  | .failed _ _ | .abandoned => .threw .taskFailed
  | _ => .blocked

/-- `fetch(t)`, `base/task.jl:727-741`. -/
def fetchTask : TaskPhase → Await Nat
  | .done value => .returned value
  | .failed _ _ | .abandoned => .threw .taskFailed
  | _ => .blocked

inductive ChildResult where
  | success
  | failure (error : Nat)
  deriving Repr, DecidableEq

def childFailed : ChildResult → Bool
  | .success => false
  | .failure _ => true

/-- The task branch of `sync_end`, `base/task.jl:782-837`: wait for each
registered child and append one `TaskFailedException` when it failed. -/
def syncEnd : List Nat → (Nat → ChildResult) → List Nat
  | [], _ => []
  | child :: children, result =>
      if childFailed (result child) then child :: syncEnd children result
      else syncEnd children result

end JuliaLean.Tasks

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

end JuliaLean.Tasks
