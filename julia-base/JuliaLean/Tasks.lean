import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Tasks.TaskModel
import JuliaLean.Tasks.Cancellation
import JuliaLean.Tasks.Condition
import JuliaLean.Tasks.AsyncMap
import JuliaLean.Tasks.LinkedList
import JuliaLean.Tasks.ScopedValues
import JuliaLean.Tasks.Atomics
import JuliaLean.Tasks.CoverageEntries

namespace JuliaLean.Tasks

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "tasks-asyncmap-negative-ntasks-function", juliaFile := "base/asyncmap.jl"
    juliaFns := ["asyncmap", "AsyncCollector", "verify_ntasks", "setup_chnl_and_tasks"]
    statement := "Every integer returned initially by the documented zero-argument ntasks form either starts at least one worker or is rejected, so nonempty asyncmap input cannot block forever on its first dispatch."
    source := "base/asyncmap.jl:18-21,116-150"
    status := .refuted, prop := ``AsyncMapDynamicNTasksTerminates, thm := some ``asyncMapDynamicNTasksTerminates_refuted
    issue := "none found (queries: asyncmap ntasks function negative; asyncmap hang ntasks; asyncmap dynamic ntasks)"
    notes := "ntasks=() -> -1 starts no workers; the first put! on the unbuffered channel blocks forever. Confirmed on 1.13.2 and nightly bbfa0ce4150. P2 because the negative dynamic count is an edge input." },
  { id := "tasks-state-monotone", juliaFile := "base/task.jl"
    juliaFns := ["istaskstarted(::Task)", "istaskdone(::Task)", "istaskfailed(::Task)", "schedule(::Task)", "yield()", "yield(::Task)", "wait()"]
    statement := "Under every interleaving of schedule, start, yield, wait, wake, completion, failure, and abandonment steps, a terminal task never becomes runnable again and a started task never becomes unstarted."
    source := "base/task.jl:150-269,1234-1490,1661-1691; task-state invariant"
    status := .proven, prop := ``TaskStateMonotone, thm := some ``taskStateMonotone_proven
    notes := "The phase model preserves the independent started bit, including failure before start when a thread pool is empty. Differential test covered created, queued, done, and failed observations on release and nightly." },
  { id := "tasks-cancellation-severity-monotone", juliaFile := "base/cancellation.jl"
    juliaFns := ["_raise_state!", "cancel!", "cancel_severity", "iscancelled"]
    statement := "Under every sequence of cancellation requests, a source's severity is monotonically nondecreasing; repeated requests can only preserve or raise it."
    source := "base/cancellation.jl:3-12,104-127,177-191,662-700"
    status := .proven, prop := ``CancellationSeverityMonotone, thm := some ``cancellationSeverityMonotone_proven
    notes := "The cancellation subsystem is present on master bbfa0ce4150 and absent from the 1.13.2 runtime." },
  { id := "tasks-wait-fetch-contract", juliaFile := "base/task.jl"
    juliaFns := ["wait(::Task; throw=true)", "fetch(::Task)", "TaskFailedException"]
    statement := "Waiting on a successful task returns nothing and fetching it returns its value; both block while it is runnable and throw TaskFailedException wrapping the task after failure or abandonment."
    source := "base/task.jl:73-81,478-509,727-741"
    status := .proven, prop := ``TaskWaitFetchContract, thm := some ``taskWaitFetchContract_proven },
  { id := "tasks-sync-failures-once", juliaFile := "base/task.jl"
    juliaFns := ["@sync", "@async", "sync_end", "CompositeException"]
    statement := "For every child-task completion interleaving, @sync reports every failed lexical @async child exactly once in its CompositeException."
    source := "base/task.jl:43-59,782-837,894-979"
    status := .proven, prop := ``SyncReportsEachFailureOnce, thm := some ``syncReportsEachFailureOnce_proven
    notes := "The contract assumes the one registration emitted by each lexical @async. Explicitly registering the same object more than once with internal @sync_add is outside that contract." },
  { id := "tasks-condition-notify-one", juliaFile := "base/condition.jl"
    juliaFns := ["notify(::GenericCondition; all=false)", "notify(::Threads.Condition; all=false)"]
    statement := "For every condition queue, notify(c; all=false) wakes exactly one still-claimable waiter when one exists, skipping stale claimed entries, and otherwise returns zero."
    source := "base/condition.jl:407-434 (notify docstring and implementation)"
    status := .proven, prop := ``ConditionNotifyOne, thm := some ``conditionNotifyOne_proven },
  { id := "tasks-asyncmap-order", juliaFile := "base/asyncmap.jl"
    juliaFns := ["asyncmap", "asyncmap!", "AsyncCollector", "verify_ntasks", "verify_batch_size"]
    statement := "For every nonnegative integer ntasks, valid batch_size, and complete worker interleaving, every asyncmap result slot contains the mapped value for the input at the same index."
    source := "base/asyncmap.jl:5-25,76-129,238-290"
    status := .proven, prop := ``AsyncMapOrdered, thm := some ``asyncMapOrdered_proven
    notes := "The model permits every completion order and indexes each write by the input enumeration index. Differential checks covered ntasks 0, 1, 2, 4, a dynamic worker function, and batch_size 2." },
  { id := "tasks-scopedvalues-restore", juliaFile := "base/scopedvalues.jl"
    juliaFns := ["ScopedValues.with", "ScopedValues.@with"]
    statement := "For every outer scope, set of bindings, and normal or exceptional body outcome, with restores every scoped value to the outer scope on exit."
    source := "base/scopedvalues.jl:203-288 (@with uses tryfinally and a child Scope)"
    status := .proven, prop := ``ScopedValuesRestore, thm := some ``scopedValuesRestore_proven },
  { id := "tasks-scopedvalues-child-inheritance", juliaFile := "base/scopedvalues.jl"
    juliaFns := ["ScopedValue", "ScopedValues.with", "Task"]
    statement := "A child task sees every scoped value from the dynamic scope in which the task was created, even if it runs after that scope exits."
    source := "base/scopedvalues.jl:45-55 (dynamic scopes propagate across tasks); base/task.jl:5-8"
    status := .proven, prop := ``ScopedValuesChildInheritance, thm := some ``scopedValuesChildInheritance_proven },
  { id := "tasks-atomics-rmw", juliaFile := "base/atomics.jl"
    juliaFns := ["atomic_cas!", "atomic_xchg!", "atomic_add!", "atomic_sub!", "atomic_and!", "atomic_nand!", "atomic_or!", "atomic_xor!", "atomic_min!", "atomic_max!"]
    statement := "Every Threads.Atomic{Int64} read-modify-write operation returns the old bit pattern and stores exactly its documented wrapping, bitwise, exchange, compare-and-set, minimum, or maximum update."
    source := "base/atomics.jl:81-324,326-361"
    status := .proven, prop := ``AtomicOperationsCorrect, thm := some ``atomicOperationsCorrect_proven }
] ++ coverageEntries

end JuliaLean.Tasks
