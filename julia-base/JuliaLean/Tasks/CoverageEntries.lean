import JuliaLean.Registry.Types
import JuliaLean.Tasks.CoverageTask
import JuliaLean.Tasks.CoverageConcurrency
import JuliaLean.Tasks.CoverageCollections

namespace JuliaLean.Tasks

open JuliaLean.Registry

def coverageEntries : List Entry := [
  { id := "tasks-coverage-task-exceptions", juliaFile := "base/task.jl"
    juliaFns := ["CapturedException", "CompositeException", "TaskFailedException", "capture_exception", "showerror", "show_task_exception", "show(::Task)"]
    statement := "Task exception constructors, collection wrappers, and render-selection branches preserve their source order and cap processed backtraces at 100 frames."
    source := "base/task.jl:11-113", status := .proven
    prop := ``TaskExceptionBodies, thm := some ``taskExceptionBodies_proven },
  { id := "tasks-coverage-task-core", juliaFile := "base/task.jl"
    juliaFns := ["Core.Task", "@task", "getproperty(::Task)", "setproperty!(::Task)", "unsafe_abandon!", "Threads.threadid(::Task)", "Threads.threadpool(::Task)", "task_result", "task_local_storage", "get_task_tls"]
    statement := "Task construction, property access, abandonment, runtime-field wrappers, and task-local storage follow the source checks and restoration order."
    source := "base/task.jl:5-9,145-403", status := .proven
    prop := ``TaskCoreBodies, thm := some ``taskCoreBodies_proven },
  { id := "tasks-coverage-task-wait", juliaFile := "base/task.jl"
    juliaFns := ["_wait(::Task)", "schedule_on_notify!(::Task)", "wait(::Task)", "waitany", "waitall", "collect_tasks", "DoneWait", "_wait_multiple", "fetch"]
    statement := "Task wait, wait-many, completion registration, and fetch bodies preserve done/remaining partitions and failure selection."
    source := "base/task.jl:405-742", status := .proven
    prop := ``TaskWaitBodies, thm := some ``taskWaitBodies_proven },
  { id := "tasks-coverage-task-sync", juliaFile := "base/task.jl"
    juliaFns := ["showerror(::CancellationRequest)", "showerror(::ScheduledAfterSyncException)", "sync_end", "sync_cancel!", "@sync", "@async", "do_async_macro", "unwrap_task_failed", "@async_unwrap", "errormonitor", "_lift_one_interp!", "@sync_add"]
    statement := "Structured-concurrency bodies register and schedule children, collect task and waitable errors in scan order, and preserve macro wrapper choices."
    source := "base/task.jl:744-1106", status := .proven
    prop := ``TaskSyncBodies, thm := some ``taskSyncBodies_proven },
  { id := "tasks-coverage-task-queue", juliaFile := "base/task.jl"
    juliaFns := ["repl_backend_task", "task_done_hook", "init_task_lock", "IntrusiveLinkedListSynchronized", "waitqueue", "isempty", "length", "push!", "pushfirst!", "pop!", "popfirst!", "list_deletefirst!", "workqueue_for", "enq_work", "schedule(::Task)"]
    statement := "Completion hooks and synchronized workqueue wrappers preserve queue mutations and enforce the runnable, unqueued, unarmed enqueue checks."
    source := "base/task.jl:1108-1318", status := .proven
    prop := ``TaskQueueBodies, thm := some ``taskQueueBodies_proven },
  { id := "tasks-coverage-task-scheduling", juliaFile := "base/task.jl"
    juliaFns := ["schedule(::Task, arg)", "deliver_claimed_wake!", "deliver_claimed_value_wake!", "yield", "yieldto", "try_yieldto", "throwto", "wait_forever", "_new_sched_task", "ensure_rescheduled", "discard_stale_workqueue_task", "trypoptask", "wait()", "pause", "record_running_time!", "maybe_record_enqueued!"]
    statement := "Scheduling, switching, wake delivery, stale-queue filtering, and metrics follow the source terminal branches and conditional updates."
    source := "base/task.jl:1374-1716", status := .proven
    prop := ``TaskSchedulingBodies, thm := some ``taskSchedulingBodies_proven },

  { id := "tasks-coverage-cancellation-token", juliaFile := "base/cancellation.jl"
    juliaFns := ["severity", "cancel_severity", "iscancelled", "CancellationTokenSource", "_cancel_parent", "_cancel_next_child", "_raise_state!"]
    statement := "Cancellation token queries, parent deduplication, runtime-link wrappers, and CAS-max state raising preserve the source decisions."
    source := "base/cancellation.jl:102-191", status := .proven
    prop := ``CancellationTokenBodies, thm := some ``cancellationTokenBodies_proven },
  { id := "tasks-coverage-cancellation-slots", juliaFile := "base/cancellation.jl"
    juliaFns := ["WaitEntry1", "WaitEntry2", "WaitEntryN", "_nslots", "_slot_owner", "_set_slot_owner!", "_slot_next", "_set_slot_next!", "_slot_aux", "_set_slot_aux!", "_find_slot", "_free_slot", "_slot_overflow_error", "_acquire_slot!", "WaitSlotRef.getproperty", "WaitSlotRef.setproperty!", "WaitSlots.size", "WaitSlots.getindex", "slots", "_release_slot!", "_next_on", "_set_wait_witness!", "_clear_wait_witness!", "_clear_uv_witness!"]
    statement := "Uniform WaitEntry slot constructors, accessors, search, acquisition, release, witness, and proxy-field bodies preserve one-based slot selection."
    source := "base/cancellation.jl:193-437", status := .proven
    prop := ``CancellationSlotBodies, thm := some ``cancellationSlotBodies_proven },
  { id := "tasks-coverage-cancellation-arms", juliaFile := "base/cancellation.jl"
    juliaFns := ["_cached_wait_entry", "_cancel_wait_entry", "_wait_registration_error", "_arm_wait", "claim_wait"]
    statement := "Cached and cancellation WaitEntry selection, arming, and expected-entry claim bodies reject double arms and clear successful claims."
    source := "base/cancellation.jl:439-523", status := .proven
    prop := ``CancellationArmBodies, thm := some ``cancellationArmBodies_proven },
  { id := "tasks-coverage-cancellation-registrations", juliaFile := "base/cancellation.jl"
    juliaFns := ["_walk_lock", "_lock_walk", "_trylock_walk", "_unlock_walk", "_note_dead_registration!", "_waiters_head", "unregister_cancellation!", "retire_cancellation_entry!", "_try_prune!"]
    statement := "Cancellation registration bookkeeping removes the requested entry, retires its ownership, and increments dead-registration counts in source order."
    source := "base/cancellation.jl:525-655", status := .proven
    prop := ``CancellationRegistrationBodies, thm := some ``cancellationRegistrationBodies_proven },
  { id := "tasks-coverage-cancellation-delivery", juliaFile := "base/cancellation.jl"
    juliaFns := ["cancel!", "redeliver!", "_cancel_walk!", "_walk_waiters!", "_cancel_walk_node!", "handle_cancellation!"]
    statement := "Cancellation delivery validates severity, raises node state, scans each worklist node, and selects value, exception, or yield delivery from the source conditions."
    source := "base/cancellation.jl:657-912", status := .proven
    prop := ``CancellationDeliveryBodies, thm := some ``cancellationDeliveryBodies_proven },
  { id := "tasks-coverage-cancellation-defaults", juliaFile := "base/cancellation.jl"
    juliaFns := ["@cancel_check", "checkcancel", "_birth_cancel_source", "default_cancel_token", "_default_cancel_token_slow", "default_cancel_source", "resolve_cancel_token", "cancel_source", "check_cancel_arg", "precheck_cancel_arg"]
    statement := "Cancellation macros and default-token wrappers preserve explicit tokens, resolve the default marker once, and bypass checks for nothing."
    source := "base/cancellation.jl:914-1129", status := .proven
    prop := ``CancellationDefaultBodies, thm := some ``cancellationDefaultBodies_proven },

  { id := "tasks-coverage-condition-locks", juliaFile := "base/condition.jl"
    juliaFns := ["concurrency_violation", "unlockall", "relockall", "relockall_but_one", "assert_havelock", "AlwaysLockedST", "GenericCondition", "waitqueue", "try_unlink_claimed!", "_try_unlink_from!", "show", "lock", "unlock", "trylock", "islocked"]
    statement := "Condition lock wrappers preserve owner checks, AlwaysLockedST thread identity, condition identity, and lock delegation."
    source := "base/condition.jl:5-135", status := .proven
    prop := ``ConditionLockBodies, thm := some ``conditionLockBodies_proven },
  { id := "tasks-coverage-condition-registration", juliaFile := "base/condition.jl"
    juliaFns := ["wait_enqueue!", "wait_dequeue!", "_fresh_waiter_error", "_assert_fresh_waiter", "_schedule_subscription_cancelled", "schedule_on_notify!"]
    statement := "Condition registration bodies select front or FIFO insertion, remove claimed entries, reject nonfresh tasks, and skip enqueue for born-cancelled tasks."
    source := "base/condition.jl:137-249", status := .proven
    prop := ``ConditionRegistrationBodies, thm := some ``conditionRegistrationBodies_proven },
  { id := "tasks-coverage-condition-wait", juliaFile := "base/condition.jl"
    juliaFns := ["wait(::GenericCondition)"]
    statement := "GenericCondition wait checks cancellation before parking, distinguishes throwing and value-mode cancellation, and returns the notify payload after lock restoration."
    source := "base/condition.jl:277-405", status := .proven
    prop := ``ConditionWaitBodies, thm := some ``conditionWaitBodies_proven },
  { id := "tasks-coverage-condition-notify", juliaFile := "base/condition.jl"
    juliaFns := ["notify", "notify_error", "isempty(::GenericCondition)", "show(::Condition)"]
    statement := "Condition notify wrappers preserve all/error arguments, return successful-claim counts, and select the documented display forms."
    source := "base/condition.jl:407-468", status := .proven
    prop := ``ConditionNotifyBodies, thm := some ``conditionNotifyBodies_proven },

  { id := "tasks-coverage-lock-reentrant", juliaFile := "base/lock.jl"
    juliaFns := ["current_task", "ReentrantLock", "assert_havelock", "show", "islocked", "trylock", "_trylock", "lock", "slowlock", "wait_no_relock", "_uncancellable_lock", "relockall_but_one", "unlock", "_unlock", "notifywaiters", "unlockall", "relockall"]
    statement := "ReentrantLock source bodies preserve owner-sensitive acquisition, UInt32 count wrap, nonowner error, full unlock, and relock decisions."
    source := "base/lock.jl:10-365", status := .proven
    prop := ``LockReentrantBodies, thm := some ``lockReentrantBodies_proven },
  { id := "tasks-coverage-lock-wrappers", juliaFile := "base/lock.jl"
    juliaFns := ["lock(f,...)", "trylock(f,...)", "@lock", "@lock_nofail", "Lockable", "getindex(::Lockable)"]
    statement := "Higher-order lock and Lockable wrappers acquire before the body, return its value, and execute unlock on normal and exceptional exits."
    source := "base/lock.jl:367-515", status := .proven
    prop := ``LockWrapperBodies, thm := some ``lockWrapperBodies_proven },
  { id := "tasks-coverage-lock-semaphore", juliaFile := "base/lock.jl"
    juliaFns := ["Semaphore", "acquire", "@acquire", "release"]
    statement := "Semaphore bodies increment below capacity, park at capacity, decrement on release, wake one queued task, and reject unmatched release."
    source := "base/lock.jl:565-679", status := .proven
    prop := ``LockSemaphoreBodies, thm := some ``lockSemaphoreBodies_proven },
  { id := "tasks-coverage-lock-event", juliaFile := "base/lock.jl"
    juliaFns := ["Event", "wait(::Event)", "notify(::Event)", "reset(::Event)"]
    statement := "Event bodies set on notify, clear on reset, and consume the set bit exactly for autoreset waits."
    source := "base/lock.jl:701-758", status := .proven
    prop := ``LockEventBodies, thm := some ``lockEventBodies_proven },
  { id := "tasks-coverage-lock-once-process", juliaFile := "base/lock.jl"
    juliaFns := ["OncePerProcess", "init_perprocesss", "copyto_monotonic!", "fill_monotonic!"]
    statement := "OncePerProcess stores one initializer value or error, reuses terminal state, and AtomicMemory copy/fill preserve element order and length."
    source := "base/lock.jl:774-868", status := .proven
    prop := ``LockOnceProcessBodies, thm := some ``lockOnceProcessBodies_proven },
  { id := "tasks-coverage-lock-once-thread", juliaFile := "base/lock.jl"
    juliaFns := ["OncePerThread", "getindex(::OncePerThread)", "init_perthread"]
    statement := "OncePerThread constructors and indexed initialization update only the requested thread slot and preserve the slot count."
    source := "base/lock.jl:886-1019", status := .proven
    prop := ``LockOnceThreadBodies, thm := some ``lockOnceThreadBodies_proven },
  { id := "tasks-coverage-lock-once-task", juliaFile := "base/lock.jl"
    juliaFns := ["OncePerTask", "(::OncePerTask)()"]
    statement := "OncePerTask constructors and calls return the task-local cached value or evaluate and cache the initializer once."
    source := "base/lock.jl:1030-1063", status := .proven
    prop := ``LockOnceTaskBodies, thm := some ``lockOnceTaskBodies_proven },

  { id := "tasks-coverage-partr-rng", juliaFile := "base/partr.jl"
    juliaFns := ["cong", "get_ptls_rng", "set_ptls_rng", "rand_ptls", "rand_uniform_max_int32"]
    statement := "Partr RNG bodies apply the documented LCG update, high-word range reduction, and zero/one special cases."
    source := "base/partr.jl:23-75", status := .proven
    prop := ``PartrRngBodies, thm := some ``partrRngBodies_proven },
  { id := "tasks-coverage-partr-heap", juliaFile := "base/partr.jl"
    juliaFns := ["taskheap", "multiq_sift_up", "multiq_sift_down", "multiq_size", "multiq_insert", "yield_os_thread", "multiq_deletemin", "multiq_check_empty"]
    statement := "Partr heap bodies preserve task/count alignment, update advertised priority on insert/delete, and apply the source 8-ary parent and child comparisons."
    source := "base/partr.jl:7-20,77-269", status := .proven
    prop := ``PartrHeapBodies, thm := some ``partrHeapBodies_proven },

  { id := "tasks-coverage-asyncmap-public", juliaFile := "base/asyncmap.jl"
    juliaFns := ["asyncmap", "_asyncmap_result", "batch_size_err_str", "verify_batch_size", "verify_ntasks", "setup_chnl_and_tasks"]
    statement := "Public asyncmap bodies choose indexed storage, reconstruct the source shape, and validate batch and constant/dynamic worker counts in source order."
    source := "base/asyncmap.jl:76-152", status := .proven
    prop := ``AsyncMapPublicBodies, thm := some ``asyncMapPublicBodies_proven },
  { id := "tasks-coverage-asyncmap-collector", juliaFile := "base/asyncmap.jl"
    juliaFns := ["start_worker_task!", "AsyncCollector", "iterate(::AsyncCollector)", "wait_done"]
    statement := "AsyncCollector bodies start workers, assign each completion to its enumeration index, add at most one requested worker per iteration, and close before joining."
    source := "base/asyncmap.jl:154-291", status := .proven
    prop := ``AsyncCollectorBodies, thm := some ``asyncCollectorBodies_proven },
  { id := "tasks-coverage-asyncmap-generator", juliaFile := "base/asyncmap.jl"
    juliaFns := ["AsyncGenerator", "iterate(::AsyncGenerator)", "IteratorSize", "IteratorEltype", "asyncmap!"]
    statement := "AsyncGenerator waits for the next numbered result, deletes it after return, ends only after collection drains, and asyncmap! returns its destination."
    source := "base/asyncmap.jl:293-356", status := .proven
    prop := ``AsyncGeneratorBodies, thm := some ``asyncGeneratorBodies_proven },

  { id := "tasks-coverage-linked-generic", juliaFile := "base/linked_list.jl"
    juliaFns := ["IntrusiveLinkedList", "eltype", "iterate", "isempty", "length", "list_append!!", "push!", "pushfirst!", "pop!", "popfirst!", "list_deletefirst!", "_list_deletefirst!"]
    statement := "Generic intrusive-list bodies preserve identity order, reject duplicate insertion/self-append, update both endpoints, and clear removed node linkage."
    source := "base/linked_list.jl:3-143", status := .proven
    prop := ``LinkedGenericBodies, thm := some ``linkedGenericBodies_proven },
  { id := "tasks-coverage-linked-boxed", juliaFile := "base/linked_list.jl"
    juliaFns := ["LinkedListItem", "LinkedList eltype", "LinkedList iterate", "LinkedList push!", "LinkedList pushfirst!", "LinkedList pop!", "LinkedList popfirst!", "LinkedList list_deletefirst!"]
    statement := "Boxed LinkedList wrappers allocate one node per pushed value, expose values in node order, and delete the first isequal value."
    source := "base/linked_list.jl:152-179", status := .proven
    prop := ``LinkedBoxedBodies, thm := some ``linkedBoxedBodies_proven },
  { id := "tasks-coverage-linked-waitentry", juliaFile := "base/linked_list.jl"
    juliaFns := ["WaitEntry push!", "WaitEntry pushfirst!", "WaitEntry pop!", "WaitEntry popfirst!", "WaitEntry list_deletefirst!", "WaitEntry length", "_waitq_isempty"]
    statement := "WaitEntry list bodies acquire and release the owner-specific slot, preserve owner-local linkage, update endpoints, and distinguish armed entries from claimed corpses."
    source := "base/linked_list.jl:181-293", status := .proven
    prop := ``LinkedWaitEntryBodies, thm := some ``linkedWaitEntryBodies_proven },

  { id := "tasks-coverage-scoped-access", juliaFile := "base/scopedvalues.jl"
    juliaFns := ["ScopedValue", "eltype", "hasdefault", "getdefault", "isassigned", "show(::Scope)", "get", "getindex", "show(::AbstractScopedValue)"]
    statement := "Scoped-value constructors and accessors select current-scope values before defaults, preserve declared type, and report assignment from either source."
    source := "base/scopedvalues.jl:79-201", status := .proven
    prop := ``ScopedAccessBodies, thm := some ``scopedAccessBodies_proven },
  { id := "tasks-coverage-scoped-dynamic", juliaFile := "base/scopedvalues.jl"
    juliaFns := ["@with", "with", "@enter_scope", "ScopedThunk", "(::ScopedThunk)()"]
    statement := "Dynamic-scope wrappers enter the constructed child scope for the body, restore the parent, and invoke ScopedThunk under its captured scope."
    source := "base/scopedvalues.jl:203-308", status := .proven
    prop := ``ScopedDynamicBodies, thm := some ``scopedDynamicBodies_proven },

  { id := "tasks-coverage-atomics-storage", juliaFile := "base/atomics.jl"
    juliaFns := ["Atomic", "lock_profiling", "inc_lock_conflict_count", "nand", "getindex", "getindex_atomic", "setindex_atomic!", "swapindex_atomic!", "modifyindex_atomic!", "replaceindex_atomic!", "setindexonce_atomic!", "atomic_cas!", "atomic_xchg!", "atomic_add!", "atomic_sub!", "atomic_and!", "atomic_nand!", "atomic_or!", "atomic_xor!", "atomic_min!", "atomic_max!"]
    statement := "Atomic storage wrappers convert before store, return old values for swaps and RMWs, compare exact bits for replacement, and delegate each legacy operation to its matching atomic primitive."
    source := "base/atomics.jl:66-361", status := .proven
    prop := ``AtomicStorageBodies, thm := some ``atomicStorageBodies_proven },
  { id := "tasks-coverage-atomics-fences", juliaFile := "base/atomics.jl"
    juliaFns := ["atomic_fence", "atomic_fence_light", "atomic_fence_heavy"]
    statement := "Atomic fence wrappers select sequentially-consistent system, sequentially-consistent single-thread, and jl_membarrier operations respectively."
    source := "base/atomics.jl:363-402", status := .proven
    prop := ``AtomicFenceBodies, thm := some ``atomicFenceBodies_proven }
]

end JuliaLean.Tasks
