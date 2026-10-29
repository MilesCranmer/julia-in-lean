import JuliaLean.Registry.Types
import JuliaLean.ConcurrencyCov.FaithfulSmall
import JuliaLean.ConcurrencyCov.FaithfulTiming
import JuliaLean.ConcurrencyCov.FaithfulPark
import JuliaLean.ConcurrencyCov.FaithfulChannels
import JuliaLean.ConcurrencyCov.FaithfulLogging
import JuliaLean.ConcurrencyCov.FaithfulThreads
import JuliaLean.ConcurrencyCov.FaithfulLock

namespace JuliaLean.ConcurrencyCov

open JuliaLean.Registry
open JuliaLean.ConcurrencyCov.FaithfulSmall

def faithfulSmallEntries : List Entry := [
  { id := "concurrencycov-atomic-constructors", juliaFile := "base/atomics.jl"
    juliaFns := ["Atomic{T}()", "Atomic{T}(value)"]
    statement := "Atomic construction initializes its field to the converted input or zero, and propagates zero and conversion failures."
    source := "base/atomics.jl:68-69", status := .proven
    prop := ``AtomicCtorContract, thm := some ``atomicCtorContract_proven },
  { id := "concurrencycov-atomic-default", juliaFile := "base/atomics.jl"
    juliaFns := ["Atomic()"]
    statement := "The default Atomic constructor creates an Int cell initialized to zero."
    source := "base/atomics.jl:72", status := .proven
    prop := ``AtomicDefaultContract, thm := some ``atomicDefaultContract_proven },
  { id := "concurrencycov-locks-mt-SpinLock", juliaFile := "base/locks-mt.jl", juliaFns := ["SpinLock()"]
    statement := "SpinLock starts with owned equal to zero for every construction."
    source := "base/locks-mt.jl:46", status := .proven, prop := ``SpinLockCtorProp, thm := some ``spinLockCtor_proven },
  { id := "concurrencycov-locks-mt-PaddedSpinLock", juliaFile := "base/locks-mt.jl", juliaFns := ["PaddedSpinLock()"]
    statement := "PaddedSpinLock initializes its atomic owned field to zero."
    source := "base/locks-mt.jl:70-74", status := .proven, prop := ``PaddedSpinLockCtorProp, thm := some ``paddedSpinLockCtor_proven },
  { id := "concurrencycov-locks-mt-assert-havelock", juliaFile := "base/locks-mt.jl", juliaFns := ["Base.assert_havelock(::AbstractSpinLock)"]
    statement := "assert_havelock returns normally exactly when islocked holds, otherwise reporting a concurrency violation."
    source := "base/locks-mt.jl:79", status := .proven, prop := ``SpinAssertHavelockProp, thm := some ``spinAssertHavelock_proven },
  { id := "concurrencycov-locks-mt-lock", juliaFile := "base/locks-mt.jl", juliaFns := ["lock(::AbstractSpinLock)"]
    statement := "lock retries trylock and performs a CPU suspend and GC safepoint after every failed iteration."
    source := "base/locks-mt.jl:81-90", status := .proven, prop := ``SpinLockLoopProp, thm := some ``spinLockLoop_proven },
  { id := "concurrencycov-locks-mt-trylock", juliaFile := "base/locks-mt.jl", juliaFns := ["trylock(::AbstractSpinLock)"]
    statement := "trylock disables finalizers before its acquire swap, succeeds only from zero, and restores finalizers after a failed swap."
    source := "base/locks-mt.jl:92-102", status := .proven, prop := ``SpinTrylockProp, thm := some ``spinTrylock_proven },
  { id := "concurrencycov-locks-mt-unlock", juliaFile := "base/locks-mt.jl", juliaFns := ["unlock(::AbstractSpinLock)"]
    statement := "unlock release-swaps to zero, rejects a zero previous value, enables finalizers, wakes a CPU, and returns."
    source := "base/locks-mt.jl:104-111", status := .proven, prop := ``SpinUnlockProp, thm := some ``spinUnlock_proven },
  { id := "concurrencycov-locks-mt-islocked", juliaFile := "base/locks-mt.jl", juliaFns := ["islocked(::AbstractSpinLock)"]
    statement := "islocked is true exactly when the monotonic atomic load of owned is nonzero."
    source := "base/locks-mt.jl:113-115", status := .proven, prop := ``SpinIslockedProp, thm := some ``spinIslocked_proven },

  { id := "concurrencycov-threadcall-macro", juliaFile := "base/threadcall.jl", juliaFns := ["@threadcall"]
    statement := "The macro validates tuple syntax and arity before constructing ordered cconvert, unsafe_convert, preserve, callback, and result bindings for every argument list."
    source := "base/threadcall.jl:18-59", status := .proven, prop := ``ThreadcallMacroProp, thm := some ``threadcallMacro_proven },
  { id := "concurrencycov-threadcall-run", juliaFile := "base/threadcall.jl", juliaFns := ["threadcall_run"]
    statement := "threadcall_run invokes its concrete wrapper and returns, propagating the wrapper outcome."
    source := "base/threadcall.jl:64-67", status := .proven, prop := ``ThreadcallRunProp, thm := some ``threadcallRun_proven },
  { id := "concurrencycov-threadcall-notify", juliaFile := "base/threadcall.jl", juliaFns := ["threadcall_notify"]
    statement := "threadcall_notify schedules the waiting task, then unpreserves the task and context in source order."
    source := "base/threadcall.jl:71-76", status := .proven, prop := ``ThreadcallNotifyProp, thm := some ``threadcallNotify_proven },
  { id := "concurrencycov-threadcall-do", juliaFile := "base/threadcall.jl", juliaFns := ["do_threadcall"]
    statement := "do_threadcall creates callbacks and context, acquires, preserves, queues, waits, releases in finally, then reads the result."
    source := "base/threadcall.jl:78-109", status := .proven, prop := ``DoThreadcallProp, thm := some ``doThreadcall_proven },

  { id := "concurrencycov-threads-overloads-foreach", juliaFile := "base/threads_overloads.jl", juliaFns := ["Threads.foreach"]
    statement := "Threads.foreach gives each spawned worker its channel items, applies the selected schedule wrapper before testing stop, and records failure through the shared stop path."
    source := "base/threads_overloads.jl:41-63", status := .proven, prop := ``ThreadsForeachProp, thm := some ``threadsForeach_proven },
  { id := "concurrencycov-threads-overloads-static", juliaFile := "base/threads_overloads.jl", juliaFns := ["_apply_for_schedule(::StaticSchedule)"]
    statement := "The static schedule wrapper calls f(x) directly."
    source := "base/threads_overloads.jl:65", status := .proven, prop := ``ApplyStaticProp, thm := some ``applyStatic_proven },
  { id := "concurrencycov-threads-overloads-fair", juliaFile := "base/threads_overloads.jl", juliaFns := ["_apply_for_schedule(::FairSchedule)"]
    statement := "The fair schedule wrapper spawns f(x) and waits for that task."
    source := "base/threads_overloads.jl:66", status := .proven, prop := ``ApplyFairProp, thm := some ``applyFair_proven },

  { id := "concurrencycov-gcutils-weak-weak-eq", juliaFile := "base/gcutils.jl", juliaFns := ["==(::WeakRef,::WeakRef)"]
    statement := "WeakRef equality delegates to isequal on both current values."
    source := "base/gcutils.jl:37", status := .proven, prop := ``WeakWeakEqProp, thm := some ``weakWeakEq_proven },
  { id := "concurrencycov-gcutils-weak-value-eq", juliaFile := "base/gcutils.jl", juliaFns := ["==(::WeakRef,v)"]
    statement := "WeakRef-to-value equality delegates to isequal on the current weak value and the argument."
    source := "base/gcutils.jl:38", status := .proven, prop := ``WeakValueEqProp, thm := some ``weakValueEq_proven },
  { id := "concurrencycov-gcutils-value-weak-eq", juliaFile := "base/gcutils.jl", juliaFns := ["==(v,::WeakRef)"]
    statement := "Value-to-WeakRef equality delegates to isequal on the argument and current weak value."
    source := "base/gcutils.jl:39", status := .proven, prop := ``ValueWeakEqProp, thm := some ``valueWeakEq_proven },
  { id := "concurrencycov-gcutils-check-mutable", juliaFile := "base/gcutils.jl", juliaFns := ["_check_mutable"]
    statement := "_check_mutable returns for mutable objects and otherwise throws the type-specific finalizer error."
    source := "base/gcutils.jl:42-46", status := .proven, prop := ``CheckMutableProp, thm := some ``checkMutable_proven },
  { id := "concurrencycov-gcutils-finalizer", juliaFile := "base/gcutils.jl", juliaFns := ["finalizer(f,o)"]
    statement := "finalizer checks mutability, registers the Julia callback, and returns the object."
    source := "base/gcutils.jl:87-91", status := .proven, prop := ``FinalizerProp, thm := some ``finalizer_proven },
  { id := "concurrencycov-gcutils-pointer-finalizer", juliaFile := "base/gcutils.jl", juliaFns := ["finalizer(::Ptr,o)"]
    statement := "The pointer finalizer checks mutability, registers through jl_gc_add_ptr_finalizer, and returns the object."
    source := "base/gcutils.jl:93-98", status := .proven, prop := ``PointerFinalizerProp, thm := some ``pointerFinalizer_proven },
  { id := "concurrencycov-gcutils-finalize", juliaFile := "base/gcutils.jl", juliaFns := ["finalize"]
    statement := "finalize invokes jl_finalize_th with the current task and object."
    source := "base/gcutils.jl:105-106", status := .proven, prop := ``FinalizeProp, thm := some ``finalize_proven },
  { id := "concurrencycov-gcutils-gc", juliaFile := "base/gcutils.jl", juliaFns := ["GC.gc"]
    statement := "GC.gc calls jl_gc_collect with full or incremental mode according to its Boolean argument."
    source := "base/gcutils.jl:136-137", status := .proven, prop := ``GcProp, thm := some ``gc_proven },
  { id := "concurrencycov-gcutils-enable", juliaFile := "base/gcutils.jl", juliaFns := ["GC.enable"]
    statement := "GC.enable passes its Boolean to jl_gc_enable and returns the previous state."
    source := "base/gcutils.jl:149", status := .proven, prop := ``GcEnableProp, thm := some ``gcEnable_proven },
  { id := "concurrencycov-gcutils-set-finalizers", juliaFile := "base/gcutils.jl", juliaFns := ["GC.enable_finalizers(::Bool)"]
    statement := "The Boolean finalizer wrapper dispatches true to enable_finalizers() and false to disable_finalizers()."
    source := "base/gcutils.jl:159", status := .proven, prop := ``SetFinalizersProp, thm := some ``setFinalizers_proven },
  { id := "concurrencycov-gcutils-enable-finalizers", juliaFile := "base/gcutils.jl", juliaFns := ["GC.enable_finalizers()"]
    statement := "enable_finalizers decrements the runtime counter and runs pending finalizers exactly when the atomic flag is nonzero."
    source := "base/gcutils.jl:161-166", status := .proven, prop := ``EnableFinalizersProp, thm := some ``enableFinalizers_proven },
  { id := "concurrencycov-gcutils-disable-finalizers", juliaFile := "base/gcutils.jl", juliaFns := ["GC.disable_finalizers()"]
    statement := "disable_finalizers calls jl_gc_disable_finalizers_internal once."
    source := "base/gcutils.jl:168-170", status := .proven, prop := ``DisableFinalizersProp, thm := some ``disableFinalizers_proven },
  { id := "concurrencycov-gcutils-in-finalizer", juliaFile := "base/gcutils.jl", juliaFns := ["GC.in_finalizer"]
    statement := "in_finalizer is true exactly when jl_gc_is_in_finalizer returns a positive Int8."
    source := "base/gcutils.jl:185-187", status := .proven, prop := ``InFinalizerProp, thm := some ``inFinalizer_proven },
  { id := "concurrencycov-gcutils-preserve", juliaFile := "base/gcutils.jl", juliaFns := ["GC.@preserve"]
    statement := "@preserve rejects every nonsymbol protected argument, then emits gc_preserve with the final expression and symbols in order."
    source := "base/gcutils.jl:237-243", status := .proven, prop := ``PreserveProp, thm := some ``preserve_proven },
  { id := "concurrencycov-gcutils-safepoint", juliaFile := "base/gcutils.jl", juliaFns := ["GC.safepoint"]
    statement := "safepoint calls jl_gc_safepoint once."
    source := "base/gcutils.jl:267", status := .proven, prop := ``SafepointProp, thm := some ``safepoint_proven },
  { id := "concurrencycov-gcutils-enable-logging", juliaFile := "base/gcutils.jl", juliaFns := ["GC.enable_logging"]
    statement := "enable_logging passes its Boolean argument to jl_enable_gc_logging."
    source := "base/gcutils.jl:274-276", status := .proven, prop := ``EnableLoggingProp, thm := some ``enableLogging_proven },
  { id := "concurrencycov-gcutils-logging-enabled", juliaFile := "base/gcutils.jl", juliaFns := ["GC.logging_enabled"]
    statement := "logging_enabled is true exactly when jl_is_gc_logging_enabled returns nonzero."
    source := "base/gcutils.jl:283-285", status := .proven, prop := ``LoggingEnabledProp, thm := some ``loggingEnabled_proven },
  { id := "concurrencycov-gcutils-active-impl", juliaFile := "base/gcutils.jl", juliaFns := ["GC.gc_active_impl"]
    statement := "gc_active_impl converts the pointer returned by jl_gc_active_impl to a String."
    source := "base/gcutils.jl:293-295", status := .proven, prop := ``GcActiveImplProp, thm := some ``gcActiveImpl_proven }
]

private def timingEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/timing.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }

def faithfulTimingEntries : List Entry := [
  timingEntry "concurrencycov-timing-gc-num" "gc_num" "gc_num returns the runtime GC counter snapshot." "base/timing.jl:79" ``FaithfulTiming.GcNumProp ``FaithfulTiming.gcNum_proven,
  timingEntry "concurrencycov-timing-gc-total-bytes" "gc_total_bytes" "gc_total_bytes sums allocated, deferred, and cumulative allocation counters in source order." "base/timing.jl:94-95" ``FaithfulTiming.GcTotalBytesProp ``FaithfulTiming.gcTotalBytes_proven,
  timingEntry "concurrencycov-timing-gc-diff" "GC_Diff" "GC_Diff subtracts every new and old counter, with allocd derived from gc_total_bytes." "base/timing.jl:97-110" ``FaithfulTiming.GcDiffProp ``FaithfulTiming.gcDiff_proven,
  timingEntry "concurrencycov-timing-gc-alloc-count" "gc_alloc_count" "gc_alloc_count sums malloc, realloc, poolalloc, and bigalloc." "base/timing.jl:112-114" ``FaithfulTiming.GcAllocCountProp ``FaithfulTiming.gcAllocCount_proven,
  timingEntry "concurrencycov-timing-compile-time" "cumulative_compile_time_ns" "cumulative_compile_time_ns returns compile and recompile counters in order." "base/timing.jl:117-121" ``FaithfulTiming.CumulativeCompileTimeNsProp ``FaithfulTiming.cumulativeCompileTimeNs_proven,
  timingEntry "concurrencycov-timing-compile-toggle" "cumulative_compile_timing" "cumulative_compile_timing increments on enable and decrements on disable." "base/timing.jl:123-130" ``FaithfulTiming.CumulativeCompileTimingProp ``FaithfulTiming.cumulativeCompileTiming_proven,
  timingEntry "concurrencycov-timing-gc-time" "gc_time_ns" "gc_time_ns returns the GC high-resolution time counter." "base/timing.jl:133" ``FaithfulTiming.GcTimeNsProp ``FaithfulTiming.gcTimeNs_proven,
  timingEntry "concurrencycov-timing-live-bytes" "gc_live_bytes" "gc_live_bytes adds live, allocated, and deferred bytes." "base/timing.jl:143-146" ``FaithfulTiming.GcLiveBytesProp ``FaithfulTiming.gcLiveBytes_proven,
  timingEntry "concurrencycov-timing-page-util" "gc_page_utilization_data" "gc_page_utilization_data reads exactly the configured pool prefix." "base/timing.jl:150-153" ``FaithfulTiming.GcPageUtilizationDataProp ``FaithfulTiming.gcPageUtilizationData_proven,
  timingEntry "concurrencycov-timing-sweep-reasons" "full_sweep_reasons" "full_sweep_reasons reads, converts, and labels the five runtime counters in source order." "base/timing.jl:175-187" ``FaithfulTiming.FullSweepReasonsProp ``FaithfulTiming.fullSweepReasons_proven,
  timingEntry "concurrencycov-timing-jit-bytes" "jit_total_bytes" "jit_total_bytes returns the runtime JIT byte counter." "base/timing.jl:195-197" ``FaithfulTiming.JitTotalBytesProp ``FaithfulTiming.jitTotalBytes_proven,
  timingEntry "concurrencycov-timing-pretty-units" "prettyprint_getunits" "prettyprint_getunits handles zero and one, computes logarithmic units, clamps the unit, and scales in source order." "base/timing.jl:202-210" ``FaithfulTiming.PrettyprintGetunitsProp ``FaithfulTiming.prettyprintGetunits_proven,
  timingEntry "concurrencycov-timing-padded-method" "padded_nonzero_print" "padded_nonzero_print applies the force or nonzero test before padding and returning its line." "base/timing.jl:212-217" ``FaithfulTiming.PaddedNonzeroPrintProp ``FaithfulTiming.paddedNonzeroPrint_proven,
  timingEntry "concurrencycov-timing-format-bytes-method" "format_bytes" "format_bytes selects binary or decimal factors and units, formats the scaled value, and pluralizes bytes." "base/timing.jl:243-252" ``FaithfulTiming.FormatBytesProp ``FaithfulTiming.formatBytes_proven,
  timingEntry "concurrencycov-timing-time-print-method" "time_print" "time_print builds the elapsed, allocation, GC, lock, compile, message, and newline clauses in source order." "base/timing.jl:254-305" ``FaithfulTiming.TimePrintProp ``FaithfulTiming.timePrint_proven,
  timingEntry "concurrencycov-timing-timev-print-method" "timev_print" "timev_print calls time_print then emits each verbose counter in source order." "base/timing.jl:307-324" ``FaithfulTiming.TimevPrintProp ``FaithfulTiming.timevPrint_proven,
  timingEntry "concurrencycov-timing-tryfinally" "__tryfinally" "__tryfinally evaluates the expression outcome and then applies the finalizer state transformation." "base/timing.jl:329-334" ``FaithfulTiming.TryfinallyProp ``FaithfulTiming.tryfinally_proven,
  timingEntry "concurrencycov-timing-time" "@time" "The no-message @time wrapper times, prints, and returns the expression outcome." "base/timing.jl:395-399" ``FaithfulTiming.TimeNoMsgProp ``FaithfulTiming.timeNoMsg_proven,
  timingEntry "concurrencycov-timing-time-msg" "@time(msg,ex)" "The message @time wrapper evaluates the message, times, prints, and returns the expression outcome." "base/timing.jl:400-408" ``FaithfulTiming.TimeMsgProp ``FaithfulTiming.timeMsg_proven,
  timingEntry "concurrencycov-timing-showtime" "@showtime" "@showtime quotes the expression as its message and delegates to the message timing body." "base/timing.jl:425-429" ``FaithfulTiming.ShowtimeProp ``FaithfulTiming.showtime_proven,
  timingEntry "concurrencycov-timing-timev" "@timev" "The no-message @timev wrapper times, prints verbose counters, and returns the expression outcome." "base/timing.jl:468-472" ``FaithfulTiming.TimevNoMsgProp ``FaithfulTiming.timevNoMsg_proven,
  timingEntry "concurrencycov-timing-timev-msg" "@timev(msg,ex)" "The message @timev wrapper evaluates the message, times, prints verbose counters, and returns the expression outcome." "base/timing.jl:473-481" ``FaithfulTiming.TimevMsgProp ``FaithfulTiming.timevMsg_proven,
  timingEntry "concurrencycov-timing-elapsed" "@elapsed" "@elapsed snapshots the clock around the expression and returns the wrapped difference in seconds." "base/timing.jl:501-508" ``FaithfulTiming.ElapsedProp ``FaithfulTiming.elapsed_proven,
  timingEntry "concurrencycov-timing-gc-bytes-ref" "gc_bytes(::Ref)" "gc_bytes writes the current runtime total-byte counter into the reference model." "base/timing.jl:511" ``FaithfulTiming.GcBytesRefProp ``FaithfulTiming.gcBytesRef_proven,
  timingEntry "concurrencycov-timing-gc-bytes" "gc_bytes()" "gc_bytes allocates a reference, fills it through gc_bytes(ref), and returns its value." "base/timing.jl:513-517" ``FaithfulTiming.GcBytesProp ``FaithfulTiming.gcBytes_proven,
  timingEntry "concurrencycov-timing-allocated" "allocated" "allocated snapshots total bytes, runs f(args...), snapshots again, and returns the wrapped difference." "base/timing.jl:519-526" ``FaithfulTiming.AllocatedProp ``FaithfulTiming.allocated_proven,
  timingEntry "concurrencycov-timing-allocations" "allocations" "allocations snapshots GC counters, runs f(args...), and returns the allocation-count difference." "base/timing.jl:529-534" ``FaithfulTiming.AllocationsProp ``FaithfulTiming.allocations_proven,
  timingEntry "concurrencycov-timing-is-simply-call" "is_simply_call" "is_simply_call checks call shape, simple arguments, and dotted operator exclusions in source order." "base/timing.jl:537-554" ``FaithfulTiming.IsSimplyCallProp ``FaithfulTiming.isSimplyCall_proven,
  timingEntry "concurrencycov-timing-is-simple-atom" "is_simple_atom" "is_simple_atom accepts symbols, global references, quote nodes, and nonexpression literals." "base/timing.jl:538" ``FaithfulTiming.IsSimpleAtomProp ``FaithfulTiming.isSimpleAtom_proven,
  timingEntry "concurrencycov-timing-gen-measurer" "_gen_allocation_measurer" "The allocation measurer validates arguments and selects direct, wrapped-call, or in-place expansion in source order." "base/timing.jl:556-592" ``FaithfulTiming.GenAllocationMeasurerProp ``FaithfulTiming.genAllocationMeasurer_proven,
  timingEntry "concurrencycov-timing-allocated-macro" "@allocated" "@allocated delegates its expression to the allocation measurer with the allocated function." "base/timing.jl:622-624" ``FaithfulTiming.AllocatedMacroProp ``FaithfulTiming.allocatedMacro_proven,
  timingEntry "concurrencycov-timing-allocations-macro" "@allocations" "@allocations delegates its expression to the allocation measurer with the allocations function." "base/timing.jl:643-645" ``FaithfulTiming.AllocationsMacroProp ``FaithfulTiming.allocationsMacro_proven,
  timingEntry "concurrencycov-timing-lock-conflicts" "@lock_conflicts" "@lock_conflicts enables profiling, snapshots conflicts, runs the expression, and restores profiling in finally." "base/timing.jl:672-683" ``FaithfulTiming.LockConflictsProp ``FaithfulTiming.lockConflicts_proven,
  timingEntry "concurrencycov-timing-timed" "@timed" "@timed snapshots clock, GC, lock, and compile counters, runs the expression, restores toggles, and returns the named tuple." "base/timing.jl:732-760" ``FaithfulTiming.TimedProp ``FaithfulTiming.timed_proven,
  timingEntry "concurrencycov-timing-time-imports" "@time_imports" "@time_imports increments the imports counter around the expression and restores it in finally." "base/timing.jl:764-774" ``FaithfulTiming.TimeImportsProp ``FaithfulTiming.timeImports_proven,
  timingEntry "concurrencycov-timing-trace-compile" "@trace_compile" "@trace_compile increments the compile-trace counter around the expression and restores it in finally." "base/timing.jl:776-786" ``FaithfulTiming.TraceCompileProp ``FaithfulTiming.traceCompile_proven,
  timingEntry "concurrencycov-timing-trace-dispatch" "@trace_dispatch" "@trace_dispatch increments the dispatch-trace counter around the expression and restores it in finally." "base/timing.jl:788-798" ``FaithfulTiming.TraceDispatchProp ``FaithfulTiming.traceDispatch_proven
]

private def parkEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/park.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }

def faithfulParkEntries : List Entry := [
  parkEntry "concurrencycov-park-wait-recheck-default" "wait_recheck" "The default wait_recheck method returns false for every object and entry." "base/park.jl:61" ``FaithfulPark.WaitRecheckDefaultProp ``FaithfulPark.waitRecheckDefault_proven,
  parkEntry "concurrencycov-park-uncancellable-lock" "_uncancellable_lock" "_uncancellable_lock calls lock without passing a cancellation token." "base/park.jl:67" ``FaithfulPark.UncancellableLockProp ``FaithfulPark.uncancellableLock_proven,
  parkEntry "concurrencycov-park-acquire-one" "acquire_wait_entry!(::Tuple{Any})" "The canonical one-waitable tuple uses the task cache, except the watcher-specialized tuple uses one fresh slot." "base/park.jl:90" ``FaithfulPark.AcquireTupleOneProp ``FaithfulPark.acquireTupleOne_proven,
  parkEntry "concurrencycov-park-acquire-cancel" "acquire_wait_entry!(::Tuple{Any,SourceWait})" "The canonical cancellable tuple uses the cancellation cache, except the watcher specialization uses two fresh slots." "base/park.jl:91-92" ``FaithfulPark.AcquireTupleSourceProp ``FaithfulPark.acquireTupleSource_proven,
  parkEntry "concurrencycov-park-acquire-generic" "acquire_wait_entry!(ws)" "Every other iterable allocates a fresh WaitEntryN with length(ws) slots." "base/park.jl:93" ``FaithfulPark.AcquireGenericProp ``FaithfulPark.acquireGeneric_proven,
  parkEntry "concurrencycov-park-release-entry" "release_wait_entry!" "release_wait_entry! preserves cached entries, ignores retired entries, and retires every other live entry in source order." "base/park.jl:97-103" ``FaithfulPark.ReleaseWaitEntryProp ``FaithfulPark.releaseWaitEntry_proven,
  parkEntry "concurrencycov-park-disarm" "disarm!" "disarm! atomically replaces this armed entry by nothing and returns the replacement success bit." "base/park.jl:106" ``FaithfulPark.DisarmProp ``FaithfulPark.disarm_proven,
  parkEntry "concurrencycov-park-park" "park!" "park! arms, enqueues, rechecks, self-claims, dequeues a self-fired wait, and returns the parked decision in source order." "base/park.jl:132-142" ``FaithfulPark.ParkProp ``FaithfulPark.park_proven,
  parkEntry "concurrencycov-park-enqueue-empty" "_enqueue_until_fired(::Tuple{})" "The empty tuple enqueue helper returns nothing without touching state." "base/park.jl:146" ``FaithfulPark.EnqueueEmptyProp ``FaithfulPark.enqueueEmpty_proven,
  parkEntry "concurrencycov-park-enqueue-tuple" "_enqueue_until_fired(::Tuple)" "The tuple enqueue helper calls wait_enqueue! from first to last and stops at the first false result." "base/park.jl:147-151" ``FaithfulPark.EnqueueTupleProp ``FaithfulPark.enqueueTuple_proven,
  parkEntry "concurrencycov-park-enqueue-generic" "_enqueue_until_fired(ws)" "The generic enqueue helper iterates in order and returns the first waitable whose enqueue reports false." "base/park.jl:152-157" ``FaithfulPark.EnqueueGenericProp ``FaithfulPark.enqueueGeneric_proven,
  parkEntry "concurrencycov-park-recheck-empty" "_recheck_until_fired(::Tuple{})" "The empty tuple recheck helper returns nothing." "base/park.jl:158" ``FaithfulPark.RecheckEmptyProp ``FaithfulPark.recheckEmpty_proven,
  parkEntry "concurrencycov-park-recheck-tuple" "_recheck_until_fired(::Tuple)" "The tuple recheck helper calls wait_recheck from first to last and returns the first fired waitable." "base/park.jl:159-163" ``FaithfulPark.RecheckTupleProp ``FaithfulPark.recheckTuple_proven,
  parkEntry "concurrencycov-park-recheck-generic" "_recheck_until_fired(ws)" "The generic recheck helper iterates in order and returns the first fired waitable." "base/park.jl:164-169" ``FaithfulPark.RecheckGenericProp ``FaithfulPark.recheckGeneric_proven,
  parkEntry "concurrencycov-park-dequeue-empty" "_dequeue_each!(::Tuple{})" "The empty tuple dequeue helper leaves state unchanged." "base/park.jl:170" ``FaithfulPark.DequeueEmptyProp ``FaithfulPark.dequeueEmpty_proven,
  parkEntry "concurrencycov-park-dequeue-tuple" "_dequeue_each!(::Tuple)" "The tuple dequeue helper calls wait_dequeue! for every waitable in order." "base/park.jl:171-174" ``FaithfulPark.DequeueTupleProp ``FaithfulPark.dequeueTuple_proven,
  parkEntry "concurrencycov-park-dequeue-generic" "_dequeue_each!(ws)" "The generic dequeue helper calls wait_dequeue! for every waitable in iteration order." "base/park.jl:175-180" ``FaithfulPark.DequeueGenericProp ``FaithfulPark.dequeueGeneric_proven,
  parkEntry "concurrencycov-park-repark" "repark!" "repark! arms, rechecks, self-claims, conditionally dequeues the fired waitable, and returns the parked decision." "base/park.jl:191-200" ``FaithfulPark.ReparkProp ``FaithfulPark.repark_proven,
  parkEntry "concurrencycov-park-wait-safe-interrupt" "wait_safe_interrupt" "wait_safe_interrupt returns normal wakes and runs interrupted cleanup before propagating every exceptional wake." "base/park.jl:227-237" ``FaithfulPark.WaitSafeInterruptProp ``FaithfulPark.waitSafeInterrupt_proven,
  parkEntry "concurrencycov-park-withdraw" "withdraw!" "withdraw! dequeues each waitable with the supplied reason before releasing the wait entry." "base/park.jl:248-252" ``FaithfulPark.WithdrawProp ``FaithfulPark.withdraw_proven,
  parkEntry "concurrencycov-park-interrupted-cleanup" "interrupted_park_cleanup!" "Interrupted cleanup disarms, protects caches from nested parks, dequeues registrations, clears queue state, and restores or retires the entry." "base/park.jl:276-301" ``FaithfulPark.InterruptedCleanupProp ``FaithfulPark.interruptedCleanup_proven,
  parkEntry "concurrencycov-park-source-enqueue-internal" "_source_wait_enqueue!" "The source enqueue helper reuses an existing slot or acquires one, stores aux, links the registration, increments its count, and returns true." "base/park.jl:306-337" ``FaithfulPark.SourceWaitEnqueueProp ``FaithfulPark.sourceWaitEnqueue_proven,
  parkEntry "concurrencycov-park-source-enqueue" "wait_enqueue!(::SourceWait)" "SourceWait enqueue delegates to the sticky source helper with its source and floor." "base/park.jl:339-340" ``FaithfulPark.SourceWaitEnqueueMethodProp ``FaithfulPark.sourceWaitEnqueueMethod_proven,
  parkEntry "concurrencycov-park-source-recheck" "wait_recheck(::SourceWait)" "SourceWait recheck performs the state reads and requires a nonzero severity at least its floor." "base/park.jl:342-347" ``FaithfulPark.SourceWaitRecheckProp ``FaithfulPark.sourceWaitRecheck_proven,
  parkEntry "concurrencycov-park-source-dequeue" "wait_dequeue!(::SourceWait)" "SourceWait dequeue is intentionally sticky and returns without mutation." "base/park.jl:349" ``FaithfulPark.SourceWaitDequeueProp ``FaithfulPark.sourceWaitDequeue_proven,
  parkEntry "concurrencycov-park-watcher-ctor" "WatcherWait" "WatcherWait stores the source and the safe cancellation severity." "base/park.jl:370" ``FaithfulPark.WatcherWaitProp ``FaithfulPark.watcherWait_proven,
  parkEntry "concurrencycov-park-acquire-watcher-one" "acquire_wait_entry!(::Tuple{WatcherWait})" "A watcher-only tuple allocates a fresh one-slot entry." "base/park.jl:372" ``FaithfulPark.AcquireWatcherOneProp ``FaithfulPark.acquireWatcherOne_proven,
  parkEntry "concurrencycov-park-acquire-watcher-source" "acquire_wait_entry!(::Tuple{WatcherWait,SourceWait})" "A watcher plus source tuple allocates a fresh two-slot entry." "base/park.jl:373" ``FaithfulPark.AcquireWatcherSourceProp ``FaithfulPark.acquireWatcherSource_proven,
  parkEntry "concurrencycov-park-watcher-enqueue" "wait_enqueue!(::WatcherWait)" "Watcher enqueue sets the watcher bit, raises the floor to safe, and delegates to source enqueue." "base/park.jl:375-377" ``FaithfulPark.WatcherEnqueueProp ``FaithfulPark.watcherEnqueue_proven,
  parkEntry "concurrencycov-park-watcher-recheck" "wait_recheck(::WatcherWait)" "Watcher recheck reads source state and compares it with the maximum of its floor and safe severity." "base/park.jl:379-380" ``FaithfulPark.WatcherRecheckProp ``FaithfulPark.watcherRecheck_proven,
  parkEntry "concurrencycov-park-watcher-dequeue" "wait_dequeue!(::WatcherWait)" "Watcher dequeue is intentionally sticky and returns without mutation." "base/park.jl:382" ``FaithfulPark.WatcherDequeueProp ``FaithfulPark.watcherDequeue_proven,
  parkEntry "concurrencycov-park-wait-token-method" "wait(::CancellationToken)" "Token wait rejects self-governance, checks cancellation, fast-returns existing state, parks on the correct tuple, withdraws, and returns or throws the wake." "base/park.jl:400-429" ``FaithfulPark.WaitTokenProp ``FaithfulPark.waitToken_proven
]

private def channelEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/channels.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }

def faithfulChannelEntries : List Entry := [
  channelEntry "concurrencycov-channels-push-abstract" "push!(::AbstractChannel)" "push! calls put! for the value and returns the channel." "base/channels.jl:10" ``FaithfulChannels.PushAbstractProp ``FaithfulChannels.pushAbstract_proven,
  channelEntry "concurrencycov-channels-popfirst-abstract" "popfirst!(::AbstractChannel)" "popfirst! delegates directly to take!." "base/channels.jl:11" ``FaithfulChannels.PopfirstAbstractProp ``FaithfulChannels.popfirstAbstract_proven,
  channelEntry "concurrencycov-channels-constructor-integer" "Channel{T}(::Integer)" "The integer constructor rejects negative sizes, constructs shared conditions, selects cond_wait, and initializes every field in order." "base/channels.jl:43-51" ``FaithfulChannels.ChannelIntegerProp ``FaithfulChannels.channelInteger_proven,
  channelEntry "concurrencycov-channels-constructor-float" "Channel{T}(::Float64)" "The Float64 constructor maps positive infinity to typemax(Int), otherwise converts to Int, then delegates to the integer constructor." "base/channels.jl:54-57" ``FaithfulChannels.ChannelFloatProp ``FaithfulChannels.channelFloat_proven,
  channelEntry "concurrencycov-channels-constructor-default" "Channel(sz)" "The untyped Channel constructor preserves its size argument and delegates to Channel{Any}." "base/channels.jl:58" ``FaithfulChannels.ChannelDefaultProp ``FaithfulChannels.channelDefault_proven,
  channelEntry "concurrencycov-channels-constructor-function" "Channel{T}(func,size)" "The function constructor creates the channel and task, resolves the pool and spawn flag, binds, starts, writes taskref when applicable, and returns the channel." "base/channels.jl:139-157" ``FaithfulChannels.ChannelFunctionProp ``FaithfulChannels.channelFunction_proven,
  channelEntry "concurrencycov-channels-constructor-function-any" "Channel(func,args...)" "The untyped function constructor forwards every positional and keyword argument to Channel{Any}." "base/channels.jl:158" ``FaithfulChannels.ChannelFunctionAnyProp ``FaithfulChannels.channelFunctionAny_proven,
  channelEntry "concurrencycov-channels-closed-exception" "closed_exception" "closed_exception constructs the documented InvalidStateException and closed state." "base/channels.jl:178" ``FaithfulChannels.ClosedExceptionProp ``FaithfulChannels.closedException_proven,
  channelEntry "concurrencycov-channels-isbuffered" "isbuffered" "isbuffered is false exactly for size zero." "base/channels.jl:180" ``FaithfulChannels.IsbufferedProp ``FaithfulChannels.isbuffered_proven,
  channelEntry "concurrencycov-channels-check-state" "check_channel_state" "check_channel_state performs the open load, acquire fence, stored-exception check, and default closed exception in order." "base/channels.jl:182-190" ``FaithfulChannels.CheckChannelStateProp ``FaithfulChannels.checkChannelState_proven,
  channelEntry "concurrencycov-channels-close-default" "close(::Channel)" "The one-argument close method constructs the default closed exception and delegates to close(c,excp)." "base/channels.jl:199" ``FaithfulChannels.CloseDefaultProp ``FaithfulChannels.closeDefault_proven,
  channelEntry "concurrencycov-channels-close" "close(::Channel,::Exception)" "close locks, stores the exception, release-stores closed, notifies all three conditions, unlocks in finally, and returns nothing." "base/channels.jl:200-212" ``FaithfulChannels.CloseProp ``FaithfulChannels.close_proven,
  channelEntry "concurrencycov-channels-isopen" "isopen" "isopen performs the acquire state load and compares it with open." "base/channels.jl:253-259" ``FaithfulChannels.IsopenProp ``FaithfulChannels.isopen_proven,
  channelEntry "concurrencycov-channels-empty" "empty!" "empty! locks, records buffer length, empties data, decrements availability, notifies putters, and returns the channel." "base/channels.jl:267-275" ``FaithfulChannels.EmptyProp ``FaithfulChannels.empty_proven,
  channelEntry "concurrencycov-channels-bind" "bind" "bind creates an uncancellable close hook, makes it non-sticky, registers it on task completion, and returns the channel." "base/channels.jl:329-339" ``FaithfulChannels.BindProp ``FaithfulChannels.bind_proven,
  channelEntry "concurrencycov-channels-channeled-tasks" "channeled_tasks" "channeled_tasks validates type and size lengths, creates channels and tasks, binds every pair, schedules tasks, yields, and returns both arrays." "base/channels.jl:352-365" ``FaithfulChannels.ChanneledTasksProp ``FaithfulChannels.channeledTasks_proven,
  channelEntry "concurrencycov-channels-close-on-done" "close_chnl_on_taskdone" "The completion hook double-checks openness under lock, closes with TaskFailedException on failure or normally otherwise, and unlocks in finally." "base/channels.jl:367-381" ``FaithfulChannels.CloseOnTaskDoneProp ``FaithfulChannels.closeOnTaskDone_proven,
  channelEntry "concurrencycov-channels-showerror" "showerror(::InvalidStateException)" "showerror prints the exception type prefix followed by its message." "base/channels.jl:387" ``FaithfulChannels.ShowInvalidStateProp ``FaithfulChannels.showInvalidState_proven,
  channelEntry "concurrencycov-channels-put" "put!" "put! checks channel state, converts the value, prechecks cancellation, and dispatches by buffer size." "base/channels.jl:400-405" ``FaithfulChannels.PutProp ``FaithfulChannels.put_proven,
  channelEntry "concurrencycov-channels-increment-available" "_increment_n_avail" "_increment_n_avail adds under the lock and stores the new value monotonically." "base/channels.jl:408-415" ``FaithfulChannels.IncrementAvailableProp ``FaithfulChannels.incrementAvailable_proven,
  channelEntry "concurrencycov-channels-put-buffered" "put_buffered" "put_buffered eagerly increments availability, waits while full, pushes, notifies takers, fixes availability on failure, and unlocks in finally." "base/channels.jl:417-449" ``FaithfulChannels.PutBufferedProp ``FaithfulChannels.putBuffered_proven,
  channelEntry "concurrencycov-channels-put-unbuffered" "put_unbuffered" "put_unbuffered increments availability, waits for and claims a taker, decrements in finally, schedules the taker, yields, and returns the value." "base/channels.jl:451-487" ``FaithfulChannels.PutUnbufferedProp ``FaithfulChannels.putUnbuffered_proven,
  channelEntry "concurrencycov-channels-fetch" "fetch" "fetch prechecks cancellation and dispatches to buffered fetch or the unsupported unbuffered path." "base/channels.jl:513-516" ``FaithfulChannels.FetchProp ``FaithfulChannels.fetch_proven,
  channelEntry "concurrencycov-channels-fetch-buffered" "fetch_buffered" "fetch_buffered locks, waits while empty with state checks, returns data[1], and unlocks in finally." "base/channels.jl:517-534" ``FaithfulChannels.FetchBufferedProp ``FaithfulChannels.fetchBuffered_proven,
  channelEntry "concurrencycov-channels-fetch-unbuffered" "fetch_unbuffered" "fetch_unbuffered always throws the documented unsupported error." "base/channels.jl:535" ``FaithfulChannels.FetchUnbufferedProp ``FaithfulChannels.fetchUnbuffered_proven,
  channelEntry "concurrencycov-channels-take" "take!" "take! prechecks cancellation and dispatches by buffer size." "base/channels.jl:567-570" ``FaithfulChannels.TakeProp ``FaithfulChannels.take_proven,
  channelEntry "concurrencycov-channels-take-buffered" "take_buffered" "take_buffered locks, waits while empty, removes the first value, decrements availability, wakes one putter, and unlocks in finally." "base/channels.jl:571-591" ``FaithfulChannels.TakeBufferedProp ``FaithfulChannels.takeBuffered_proven,
  channelEntry "concurrencycov-channels-take-unbuffered" "take_unbuffered" "take_unbuffered locks, checks state, wakes one putter, waits for a typed value, and unlocks in finally." "base/channels.jl:594-607" ``FaithfulChannels.TakeUnbufferedProp ``FaithfulChannels.takeUnbuffered_proven,
  channelEntry "concurrencycov-channels-isready" "isready" "isready is true exactly when n_avail is positive." "base/channels.jl:647" ``FaithfulChannels.IsreadyProp ``FaithfulChannels.isready_proven,
  channelEntry "concurrencycov-channels-isempty" "isempty" "isempty is true exactly when n_avail is zero." "base/channels.jl:648" ``FaithfulChannels.IsemptyProp ``FaithfulChannels.isempty_proven,
  channelEntry "concurrencycov-channels-n-avail" "n_avail" "n_avail returns the monotonic atomic availability load." "base/channels.jl:649-652" ``FaithfulChannels.NAvailProp ``FaithfulChannels.nAvail_proven,
  channelEntry "concurrencycov-channels-isfull" "isfull" "isfull compares n_avail with sz_max." "base/channels.jl:693" ``FaithfulChannels.IsfullProp ``FaithfulChannels.isfull_proven,
  channelEntry "concurrencycov-channels-lock" "lock(::Channel)" "Channel lock forwards the cancellation argument to cond_take lock." "base/channels.jl:698" ``FaithfulChannels.LockProp ``FaithfulChannels.lock_proven,
  channelEntry "concurrencycov-channels-lock-do" "lock(f,::Channel)" "The higher-order Channel lock delegates f and the shared condition to lock." "base/channels.jl:699" ``FaithfulChannels.LockDoProp ``FaithfulChannels.lockDo_proven,
  channelEntry "concurrencycov-channels-unlock" "unlock(::Channel)" "Channel unlock delegates to cond_take unlock." "base/channels.jl:700" ``FaithfulChannels.UnlockProp ``FaithfulChannels.unlock_proven,
  channelEntry "concurrencycov-channels-trylock" "trylock(::Channel)" "Channel trylock delegates to cond_take trylock." "base/channels.jl:701" ``FaithfulChannels.TrylockProp ``FaithfulChannels.trylock_proven,
  channelEntry "concurrencycov-channels-wait" "wait(::Channel)" "wait prechecks cancellation, fast-returns when ready, otherwise locks and waits with state checks until ready, then unlocks in finally." "base/channels.jl:727-746" ``FaithfulChannels.WaitProp ``FaithfulChannels.wait_proven,
  channelEntry "concurrencycov-channels-eltype" "eltype(::Type{Channel{T}})" "Channel eltype returns its type parameter." "base/channels.jl:748" ``FaithfulChannels.EltypeProp ``FaithfulChannels.eltype_proven,
  channelEntry "concurrencycov-channels-show-short" "show(::IO,::Channel)" "Short show prints the channel type and maximum size in parentheses." "base/channels.jl:750" ``FaithfulChannels.ShowShortProp ``FaithfulChannels.showShort_proven,
  channelEntry "concurrencycov-channels-show-plain" "show(::IO,::MIME,::Channel)" "Plain show first prints short form, then when noncompact prints closed, empty, or available-item metadata with pluralization." "base/channels.jl:752-767" ``FaithfulChannels.ShowPlainProp ``FaithfulChannels.showPlain_proven,
  channelEntry "concurrencycov-channels-iterate" "iterate(::Channel)" "iterate tests open or ready, takes one value, maps the normal closed exception to end, rethrows others, and checks stored close exceptions on the terminal path." "base/channels.jl:769-792" ``FaithfulChannels.IterateProp ``FaithfulChannels.iterate_proven,
  channelEntry "concurrencycov-channels-iterator-size" "IteratorSize(::Type{<:Channel})" "Channel iteration reports SizeUnknown." "base/channels.jl:794" ``FaithfulChannels.IteratorSizeProp ``FaithfulChannels.iteratorSize_proven
]

private def loggingEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/logging/logging.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }
private def consoleEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/logging/ConsoleLogger.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }

def faithfulLoggingEntries : List Entry := [
  loggingEntry "concurrencycov-logging-catch-default" "catch_exceptions" "The default logger exception policy returns true." "base/logging/logging.jl:72" ``FaithfulLogging.CatchExceptionsProp ``FaithfulLogging.catchExceptions_proven,
  loggingEntry "concurrencycov-logging-invoked-shouldlog" "_invoked_shouldlog" "The invalidation barrier invokes shouldlog at the exact concrete argument tuple and asserts Bool." "base/logging/logging.jl:77-84" ``FaithfulLogging.InvokedShouldlogProp ``FaithfulLogging.invokedShouldlog_proven,
  loggingEntry "concurrencycov-logging-invoked-min" "_invoked_min_enabled_level" "The invalidation barrier invokes min_enabled_level for the logger type and asserts LogLevel." "base/logging/logging.jl:86-88" ``FaithfulLogging.InvokedMinLevelProp ``FaithfulLogging.invokedMinLevel_proven,
  loggingEntry "concurrencycov-logging-invoked-catch" "_invoked_catch_exceptions" "The invalidation barrier invokes catch_exceptions for the logger type and asserts Bool." "base/logging/logging.jl:90-92" ``FaithfulLogging.InvokedCatchProp ``FaithfulLogging.invokedCatch_proven,
  loggingEntry "concurrencycov-logging-null-min" "min_enabled_level(::NullLogger)" "NullLogger reports AboveMaxLevel." "base/logging/logging.jl:102" ``FaithfulLogging.NullMinLevelProp ``FaithfulLogging.nullMinLevel_proven,
  loggingEntry "concurrencycov-logging-null-should" "shouldlog(::NullLogger)" "NullLogger rejects every message." "base/logging/logging.jl:103" ``FaithfulLogging.NullShouldlogProp ``FaithfulLogging.nullShouldlog_proven,
  loggingEntry "concurrencycov-logging-null-handle" "handle_message(::NullLogger)" "NullLogger handle_message throws because filtering should prevent the call." "base/logging/logging.jl:104-105" ``FaithfulLogging.NullHandleMessageProp ``FaithfulLogging.nullHandleMessage_proven,
  loggingEntry "concurrencycov-logging-level-copy" "LogLevel(::LogLevel)" "Constructing a LogLevel from a LogLevel returns the same value." "base/logging/logging.jl:129" ``FaithfulLogging.LogLevelCopyProp ``FaithfulLogging.logLevelCopy_proven,
  loggingEntry "concurrencycov-logging-less-level-level" "isless(::LogLevel,::LogLevel)" "LogLevel comparison delegates to Int32 comparison of both fields." "base/logging/logging.jl:131" ``FaithfulLogging.LessLevelLevelProp ``FaithfulLogging.lessLevelLevel_proven,
  loggingEntry "concurrencycov-logging-less-level-int" "isless(::LogLevel,::Integer)" "LogLevel-to-integer comparison delegates to comparison of the level field and integer." "base/logging/logging.jl:132" ``FaithfulLogging.LessLevelIntegerProp ``FaithfulLogging.lessLevelInteger_proven,
  loggingEntry "concurrencycov-logging-less-int-level" "isless(::Integer,::LogLevel)" "Integer-to-LogLevel comparison delegates to comparison of the integer and level field." "base/logging/logging.jl:133" ``FaithfulLogging.LessIntegerLevelProp ``FaithfulLogging.lessIntegerLevel_proven,
  loggingEntry "concurrencycov-logging-add-level" "+(::LogLevel,::Integer)" "LogLevel addition adds to the Int32 field and reconstructs LogLevel with exact conversion." "base/logging/logging.jl:134" ``FaithfulLogging.AddLevelProp ``FaithfulLogging.addLevel_proven,
  loggingEntry "concurrencycov-logging-sub-level" "-(::LogLevel,::Integer)" "LogLevel subtraction subtracts from the Int32 field and reconstructs LogLevel with exact conversion." "base/logging/logging.jl:135" ``FaithfulLogging.SubLevelProp ``FaithfulLogging.subLevel_proven,
  loggingEntry "concurrencycov-logging-convert-level" "convert(::Type{LogLevel},::Integer)" "Integer conversion constructs LogLevel and enforces the Int32 range." "base/logging/logging.jl:136" ``FaithfulLogging.ConvertLevelProp ``FaithfulLogging.convertLevel_proven,
  loggingEntry "concurrencycov-logging-convert-int32" "convert(::Type{Int32},::LogLevel)" "Converting LogLevel to Int32 returns its field." "base/logging/logging.jl:137" ``FaithfulLogging.ConvertInt32Prop ``FaithfulLogging.convertInt32_proven,
  loggingEntry "concurrencycov-logging-show-level" "show(::LogLevel)" "LogLevel show selects each standard name before the generic LogLevel(n) form." "base/logging/logging.jl:180-189" ``FaithfulLogging.ShowLevelProp ``FaithfulLogging.showLevel_proven,
  loggingEntry "concurrencycov-logging-sourceinfo" "@_sourceinfo" "_sourceinfo returns the caller module, question mark for no file or the String file, and source line." "base/logging/logging.jl:266-272" ``FaithfulLogging.SourceInfoProp ``FaithfulLogging.sourceInfo_proven,
  loggingEntry "concurrencycov-logging-logmsg-macro" "@logmsg" "@logmsg passes source information, escaped level, and arguments to logmsg_code." "base/logging/logging.jl:274" ``FaithfulLogging.LogmsgMacroProp ``FaithfulLogging.logmsgMacro_proven,
  loggingEntry "concurrencycov-logging-debug-macro" "@debug" "@debug passes source information, Debug, and arguments to logmsg_code." "base/logging/logging.jl:275" ``FaithfulLogging.DebugMacroProp ``FaithfulLogging.debugMacro_proven,
  loggingEntry "concurrencycov-logging-info-macro" "@info" "@info passes source information, Info, and arguments to logmsg_code." "base/logging/logging.jl:276" ``FaithfulLogging.InfoMacroProp ``FaithfulLogging.infoMacro_proven,
  loggingEntry "concurrencycov-logging-warn-macro" "@warn" "@warn passes source information, Warn, and arguments to logmsg_code." "base/logging/logging.jl:277" ``FaithfulLogging.WarnMacroProp ``FaithfulLogging.warnMacro_proven,
  loggingEntry "concurrencycov-logging-error-macro" "@error" "@error passes source information, Error, and arguments to logmsg_code." "base/logging/logging.jl:278" ``FaithfulLogging.ErrorMacroProp ``FaithfulLogging.errorMacro_proven,
  loggingEntry "concurrencycov-logging-record-id" "log_record_id" "log_record_id hashes the full record identity, forms the padded symbol, and increments with wrapping until it is unique." "base/logging/logging.jl:294-312" ``FaithfulLogging.LogRecordIdProp ``FaithfulLogging.logRecordId_proven,
  loggingEntry "concurrencycov-logging-default-group" "default_group" "default_group takes the basename, removes its extension, and converts the stem to Symbol." "base/logging/logging.jl:314" ``FaithfulLogging.DefaultGroupProp ``FaithfulLogging.defaultGroup_proven,
  loggingEntry "concurrencycov-logging-issimple" "issimple" "issimple accepts the five literal classes, quoted simple values and inert expressions, and rejects every other form in source order." "base/logging/logging.jl:316-327" ``FaithfulLogging.IsSimpleProp ``FaithfulLogging.isSimple_proven,
  loggingEntry "concurrencycov-logging-issimplekw" "issimplekw" "issimplekw accepts exactly keyword expressions whose escaped value is simple." "base/logging/logging.jl:328-338" ``FaithfulLogging.IsSimpleKwProp ``FaithfulLogging.isSimpleKw_proven,
  loggingEntry "concurrencycov-logging-current-env" "current_logger_for_env" "current_logger_for_env reads logstate and returns its logger exactly when the standard threshold or environment override enables it." "base/logging/logging.jl:341-347" ``FaithfulLogging.CurrentLoggerForEnvProp ``FaithfulLogging.currentLoggerForEnv_proven,
  loggingEntry "concurrencycov-logging-logmsg-code" "logmsg_code" "logmsg_code processes metadata, selects constant, definedness-check, or protected record construction, then emits the two filtering stages and handler call." "base/logging/logging.jl:350-429" ``FaithfulLogging.LogmsgCodeProp ``FaithfulLogging.logmsgCode_proven,
  loggingEntry "concurrencycov-logging-handle-nothrow" "handle_message_nothrow" "handle_message_nothrow invokes handle_message and reports any thrown exception through logging_error." "base/logging/logging.jl:431-441" ``FaithfulLogging.HandleMessageNothrowProp ``FaithfulLogging.handleMessageNothrow_proven,
  loggingEntry "concurrencycov-logging-process-exs" "process_logmsg_exs" "process_logmsg_exs scans arguments in order, handles direct special assignments, retains splats, derives positional keys, and fills default group and id." "base/logging/logging.jl:443-484" ``FaithfulLogging.ProcessLogmsgExsProp ``FaithfulLogging.processLogmsgExs_proven,
  loggingEntry "concurrencycov-logging-default-group-code" "default_group_code" "default_group_code precomputes literal groups when Base.basename is available, otherwise emits memoized runtime code." "base/logging/logging.jl:486-494" ``FaithfulLogging.DefaultGroupCodeProp ``FaithfulLogging.defaultGroupCode_proven,
  loggingEntry "concurrencycov-logging-logging-error" "logging_error" "logging_error rethrows when exception catching is disabled, otherwise constructs the protected message and scrubbed backtrace before logging it." "base/logging/logging.jl:498-519" ``FaithfulLogging.LoggingErrorProp ``FaithfulLogging.loggingError_proven,
  loggingEntry "concurrencycov-logging-shim" "logmsg_shim" "logmsg_shim pairs alternating keyword elements, converts the level and file, supplies special metadata directly, splats real keywords, and returns nothing." "base/logging/logging.jl:523-530" ``FaithfulLogging.LogmsgShimProp ``FaithfulLogging.logmsgShim_proven,
  loggingEntry "concurrencycov-logging-logstate" "LogState" "LogState invokes the logger minimum-level method, converts it to LogLevel, and stores it with the logger." "base/logging/logging.jl:538" ``FaithfulLogging.LogStateCtorProp ``FaithfulLogging.logStateCtor_proven,
  loggingEntry "concurrencycov-logging-current-logstate" "current_logstate" "current_logstate reads the scoped state and falls back to the global state with a LogState assertion." "base/logging/logging.jl:542-545" ``FaithfulLogging.CurrentLogstateProp ``FaithfulLogging.currentLogstate_proven,
  loggingEntry "concurrencycov-logging-with-logstate" "with_logstate" "with_logstate installs CURRENT_LOGSTATE for the dynamic call to f." "base/logging/logging.jl:547" ``FaithfulLogging.WithLogstateProp ``FaithfulLogging.withLogstate_proven,
  loggingEntry "concurrencycov-logging-disable" "disable_logging" "disable_logging adds one to the level, stores the Int32 threshold sequentially consistently, and returns nothing." "base/logging/logging.jl:565-567" ``FaithfulLogging.DisableLoggingProp ``FaithfulLogging.disableLogging_proven,
  loggingEntry "concurrencycov-logging-env-override" "env_override_minlevel" "env_override_minlevel parses JULIA_DEBUG tokens in order and matches group, module, or root according to include and exclusion state." "base/logging/logging.jl:572-615" ``FaithfulLogging.EnvOverrideProp ``FaithfulLogging.envOverride_proven,
  loggingEntry "concurrencycov-logging-global-get" "global_logger()" "global_logger returns the logger stored in the global LogState." "base/logging/logging.jl:631" ``FaithfulLogging.GlobalLoggerProp ``FaithfulLogging.globalLogger_proven,
  loggingEntry "concurrencycov-logging-global-set" "global_logger(logger)" "The global logger setter saves the previous logger, constructs and installs a new LogState, and returns the previous logger." "base/logging/logging.jl:633-637" ``FaithfulLogging.SetGlobalLoggerProp ``FaithfulLogging.setGlobalLogger_proven,
  loggingEntry "concurrencycov-logging-with-logger" "with_logger" "with_logger constructs LogState(logger) and delegates the dynamic call to with_logstate." "base/logging/logging.jl:657-659" ``FaithfulLogging.WithLoggerProp ``FaithfulLogging.withLogger_proven,
  loggingEntry "concurrencycov-logging-current-logger" "current_logger" "current_logger returns the logger from current_logstate." "base/logging/logging.jl:667" ``FaithfulLogging.CurrentLoggerProp ``FaithfulLogging.currentLogger_proven,
  loggingEntry "concurrencycov-logging-simple-stream" "SimpleLogger(stream,level)" "The stream SimpleLogger constructor allocates a ReentrantLock and empty message-limit dictionary and stores stream and minimum." "base/logging/logging.jl:690" ``FaithfulLogging.SimpleLoggerStreamProp ``FaithfulLogging.simpleLoggerStream_proven,
  loggingEntry "concurrencycov-logging-simple-default" "SimpleLogger(level)" "The default SimpleLogger constructor delegates with the closed stream and supplied level." "base/logging/logging.jl:691" ``FaithfulLogging.SimpleLoggerDefaultProp ``FaithfulLogging.simpleLoggerDefault_proven,
  loggingEntry "concurrencycov-logging-simple-should" "shouldlog(::SimpleLogger)" "SimpleLogger shouldlog locks and tests whether the id limit, defaulting to one, is positive." "base/logging/logging.jl:693-694" ``FaithfulLogging.SimpleShouldlogProp ``FaithfulLogging.simpleShouldlog_proven,
  loggingEntry "concurrencycov-logging-simple-min" "min_enabled_level(::SimpleLogger)" "SimpleLogger minimum-level query returns its stored minimum." "base/logging/logging.jl:696" ``FaithfulLogging.SimpleMinLevelProp ``FaithfulLogging.simpleMinLevel_proven,
  loggingEntry "concurrencycov-logging-simple-catch" "catch_exceptions(::SimpleLogger)" "SimpleLogger disables logging exception catching." "base/logging/logging.jl:698" ``FaithfulLogging.SimpleCatchProp ``FaithfulLogging.simpleCatch_proven,
  loggingEntry "concurrencycov-logging-simple-handle" "handle_message(::SimpleLogger)" "SimpleLogger enforces built-in maxlog under lock, formats every message and metadata line, chooses a fallback stream, writes under lock, and returns nothing." "base/logging/logging.jl:700-734" ``FaithfulLogging.SimpleHandleProp ``FaithfulLogging.simpleHandle_proven
]

def faithfulConsoleEntries : List Entry := [
  consoleEntry "concurrencycov-console-stream" "ConsoleLogger(stream,level)" "The stream ConsoleLogger constructor allocates a lock and empty limits dictionary and stores every option." "base/logging/ConsoleLogger.jl:37-42" ``FaithfulLogging.ConsoleLoggerStreamProp ``FaithfulLogging.consoleLoggerStream_proven,
  consoleEntry "concurrencycov-console-default" "ConsoleLogger(level)" "The default ConsoleLogger constructor uses the closed stream and stores every supplied option." "base/logging/ConsoleLogger.jl:43-48" ``FaithfulLogging.ConsoleLoggerDefaultProp ``FaithfulLogging.consoleLoggerDefault_proven,
  consoleEntry "concurrencycov-console-should" "shouldlog(::ConsoleLogger)" "ConsoleLogger shouldlog locks and tests whether the id limit, defaulting to one, is positive." "base/logging/ConsoleLogger.jl:51-52" ``FaithfulLogging.ConsoleShouldlogProp ``FaithfulLogging.consoleShouldlog_proven,
  consoleEntry "concurrencycov-console-min" "min_enabled_level(::ConsoleLogger)" "ConsoleLogger minimum-level query returns its stored minimum." "base/logging/ConsoleLogger.jl:54" ``FaithfulLogging.ConsoleMinLevelProp ``FaithfulLogging.consoleMinLevel_proven,
  consoleEntry "concurrencycov-console-showvalue-plain" "showvalue(io,msg)" "Plain showvalue delegates to text/plain show." "base/logging/ConsoleLogger.jl:57" ``FaithfulLogging.ShowValuePlainProp ``FaithfulLogging.showValuePlain_proven,
  consoleEntry "concurrencycov-console-showvalue-tuple" "showvalue(io,(ex,bt))" "Tuple showvalue scrubs the backtrace and calls showerror with the backtrace flag exactly when nonnothing." "base/logging/ConsoleLogger.jl:58-62" ``FaithfulLogging.ShowValueTupleProp ``FaithfulLogging.showValueTuple_proven,
  consoleEntry "concurrencycov-console-showvalue-exception" "showvalue(io,ex)" "Exception showvalue delegates directly to showerror." "base/logging/ConsoleLogger.jl:63" ``FaithfulLogging.ShowValueExceptionProp ``FaithfulLogging.showValueException_proven,
  consoleEntry "concurrencycov-console-color" "default_logcolor" "default_logcolor selects debug, info, warning, or error color by the three standard thresholds." "base/logging/ConsoleLogger.jl:65-70" ``FaithfulLogging.DefaultLogcolorProp ``FaithfulLogging.defaultLogcolor_proven,
  consoleEntry "concurrencycov-console-metafmt" "default_metafmt" "default_metafmt selects color and prefix, omits Info metadata, otherwise builds module, contracted file, optional line range, and @ suffix in source order." "base/logging/ConsoleLogger.jl:72-88" ``FaithfulLogging.DefaultMetafmtProp ``FaithfulLogging.defaultMetafmt_proven,
  consoleEntry "concurrencycov-console-termlength" "termlength" "termlength scans characters, ignores ANSI escape runs through m, and counts every other character." "base/logging/ConsoleLogger.jl:92-109" ``FaithfulLogging.TermlengthProp ``FaithfulLogging.termlength_proven,
  consoleEntry "concurrencycov-console-handle" "handle_message(::ConsoleLogger)" "ConsoleLogger enforces maxlog, formats message and values with box decoration, computes right justification, chooses fallback stream, writes under lock, and returns nothing." "base/logging/ConsoleLogger.jl:111-199" ``FaithfulLogging.ConsoleHandleProp ``FaithfulLogging.consoleHandle_proven
]

private def threadsEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/threadingconstructs.jl", juliaFns := [fn], statement, source
    status := .proven, prop, thm := some thm }

def faithfulThreadsEntries : List Entry := [
  threadsEntry "concurrencycov-threading-threadid" "threadid" "threadid reads the zero-based runtime id, adds one in Int16, and converts to Int." "base/threadingconstructs.jl:36" ``FaithfulThreads.ThreadidProp ``FaithfulThreads.threadid_proven,
  threadsEntry "concurrencycov-threading-maxthreadid" "maxthreadid" "maxthreadid returns jl_n_threads as Int." "base/threadingconstructs.jl:47" ``FaithfulThreads.MaxthreadidProp ``FaithfulThreads.maxthreadid_proven,
  threadsEntry "concurrencycov-threading-nthreads" "nthreads" "nthreads delegates its pool symbol to threadpoolsize." "base/threadingconstructs.jl:60" ``FaithfulThreads.NthreadsProp ``FaithfulThreads.nthreads_proven,
  threadsEntry "concurrencycov-threading-nthreads-pool" "_nthreads_in_pool" "_nthreads_in_pool performs the pointer load at tpid plus one and converts the result to Int." "base/threadingconstructs.jl:62-65" ``FaithfulThreads.NthreadsInPoolProp ``FaithfulThreads.nthreadsInPool_proven,
  threadsEntry "concurrencycov-threading-tpid-symbol" "_tpid_to_sym" "_tpid_to_sym checks interactive, default, and foreign ids in order and rejects every other id." "base/threadingconstructs.jl:67-77" ``FaithfulThreads.TpidToSymProp ``FaithfulThreads.tpidToSym_proven,
  threadsEntry "concurrencycov-threading-symbol-tpid" "_sym_to_tpid" "_sym_to_tpid checks interactive, default, and foreign names in order and rejects every other symbol." "base/threadingconstructs.jl:79-89" ``FaithfulThreads.SymToTpidProp ``FaithfulThreads.symToTpid_proven,
  threadsEntry "concurrencycov-threading-threadpool" "threadpool" "threadpool subtracts one, converts to Int16, calls jl_threadpoolid, and converts the returned id to a symbol." "base/threadingconstructs.jl:96-99" ``FaithfulThreads.ThreadpoolProp ``FaithfulThreads.threadpool_proven,
  threadsEntry "concurrencycov-threading-threadpool-description" "threadpooldescription" "threadpooldescription delegates to threadpool and labels the configured leading foreign ids as GC threads." "base/threadingconstructs.jl:106-117" ``FaithfulThreads.ThreadpoolDescriptionProp ``FaithfulThreads.threadpoolDescription_proven,
  threadsEntry "concurrencycov-threading-nthreadpools" "nthreadpools" "nthreadpools reads jl_n_threadpools and converts it to Int." "base/threadingconstructs.jl:124" ``FaithfulThreads.NthreadpoolsProp ``FaithfulThreads.nthreadpools_proven,
  threadsEntry "concurrencycov-threading-pool-size" "threadpoolsize" "threadpoolsize handles interactive and default through id conversion and runtime load, rejects foreign size, and rejects unknown pools." "base/threadingconstructs.jl:136-145" ``FaithfulThreads.ThreadpoolsizeProp ``FaithfulThreads.threadpoolsize_proven,
  threadsEntry "concurrencycov-threading-pool-tids" "threadpooltids" "threadpooltids computes interactive and default UnitRanges from the two runtime pool counts and rejects other names." "base/threadingconstructs.jl:152-161" ``FaithfulThreads.ThreadpooltidsProp ``FaithfulThreads.threadpooltids_proven,
  threadsEntry "concurrencycov-threading-ngcthreads" "ngcthreads" "ngcthreads reads jl_n_gcthreads, adds one, and converts to Int." "base/threadingconstructs.jl:169" ``FaithfulThreads.NgcthreadsProp ``FaithfulThreads.ngcthreads_proven,
  threadsEntry "concurrencycov-threading-threads-call" "_threads_call" "_threads_call invokes the stored function on the supplied task id." "base/threadingconstructs.jl:182" ``FaithfulThreads.ThreadsCallProp ``FaithfulThreads.threadsCall_proven,
  threadsEntry "concurrencycov-threading-run" "threading_run" "threading_run validates static nesting, enters the region, constructs and schedules every worker, waits with cancellation escalation, exits in finally, then reports failures or cancellation." "base/threadingconstructs.jl:184-251" ``FaithfulThreads.ThreadingRunProp ``FaithfulThreads.threadingRun_proven,
  threadsEntry "concurrencycov-threading-run-expr" "_threading_run_expr" "_threading_run_expr emits the call with the static identity test and no foreigncall in the thunk." "base/threadingconstructs.jl:257-259" ``FaithfulThreads.ThreadingRunExprProp ``FaithfulThreads.threadingRunExpr_proven,
  threadsEntry "concurrencycov-threading-threadsfor" "_threadsfor" "_threadsfor extracts index and range, escapes the range, selects greedy or default function generation, and emits the runner returning nothing." "base/threadingconstructs.jl:261-276" ``FaithfulThreads.ThreadsforProp ``FaithfulThreads.threadsfor_proven,
  threadsEntry "concurrencycov-threading-multi" "_threadsfor_multi_iterator" "The multi-iterator helper extracts variables and ranges, constructs ordered let assignments and product, then delegates to the single-iterator generator." "base/threadingconstructs.jl:278-299" ``FaithfulThreads.MultiIteratorProp ``FaithfulThreads.multiIterator_proven,
  threadsEntry "concurrencycov-threading-comprehension" "_threadsfor_comprehension" "The comprehension helper unwraps flattening, validates generator form, extracts filter and iterators, and selects single or product generation." "base/threadingconstructs.jl:301-326" ``FaithfulThreads.ComprehensionProp ``FaithfulThreads.comprehension_proven,
  threadsEntry "concurrencycov-threading-body-func" "_comprehension_body_func" "The body helper constructs an escaped one-argument lambda with tuple destructuring." "base/threadingconstructs.jl:331" ``FaithfulThreads.BodyFuncProp ``FaithfulThreads.bodyFunc_proven,
  threadsEntry "concurrencycov-threading-eltype-expr" "_comprehension_eltype_expr" "The eltype helper constructs filtered generator and optional flatten syntax before the iterator upper-bound return-type query." "base/threadingconstructs.jl:337-342" ``FaithfulThreads.ComprehensionEltypeProp ``FaithfulThreads.comprehensionEltype_proven,
  threadsEntry "concurrencycov-threading-pred-expr" "_comprehension_pred_expr" "The predicate helper emits nothing without a condition and otherwise a local predicate lambda." "base/threadingconstructs.jl:346-347" ``FaithfulThreads.PredExprProp ``FaithfulThreads.predExpr_proven,
  threadsEntry "concurrencycov-threading-test-expr" "_comprehension_test_expr" "The test helper emits true without a condition and pred(item) otherwise." "base/threadingconstructs.jl:348" ``FaithfulThreads.TestExprProp ``FaithfulThreads.testExpr_proven,
  threadsEntry "concurrencycov-threading-add-expr" "_comprehension_add_expr" "The add helper emits a loop over flattened values or one add call for an unflattened body." "base/threadingconstructs.jl:351-352" ``FaithfulThreads.AddExprProp ``FaithfulThreads.addExpr_proven,
  threadsEntry "concurrencycov-threading-result" "_comprehension_result" "The result helper handles empty union widening, preserves concrete inferred types, otherwise scans and copies only when the element type changes." "base/threadingconstructs.jl:356-364" ``FaithfulThreads.ResultProp ``FaithfulThreads.result_proven,
  threadsEntry "concurrencycov-threading-widened" "_comprehension_widened_eltype" "The widening helper scans from i, recursing at the first value outside T with promote_typejoin and the next index." "base/threadingconstructs.jl:368-374" ``FaithfulThreads.WidenedProp ``FaithfulThreads.widened_proven,
  threadsEntry "concurrencycov-threading-single" "_threadsfor_single_iterator" "The single-iterator generator extracts and escapes range, then selects greedy, fast, or default path in source order." "base/threadingconstructs.jl:376-389" ``FaithfulThreads.SingleIteratorProp ``FaithfulThreads.singleIterator_proven,
  threadsEntry "concurrencycov-threading-fast" "_threadsfor_comprehension_fast" "The fast generator builds items, inferred type, shaped result, worker function, runner call, and final type correction in source order." "base/threadingconstructs.jl:395-424" ``FaithfulThreads.FastComprehensionProp ``FaithfulThreads.fastComprehension_proven,
  threadsEntry "concurrencycov-threading-fast-worker" "threadsfor_fun(fast)" "The fast worker computes its contiguous range and writes body(r[i]) into the matching result slot." "base/threadingconstructs.jl:410-417" ``FaithfulThreads.FastWorkerProp ``FaithfulThreads.fastWorker_proven,
  threadsEntry "concurrencycov-threading-greedy-func" "greedy_func" "greedy_func creates a spawned producer channel and a worker that iterates the channel and executes the escaped body." "base/threadingconstructs.jl:427-442" ``FaithfulThreads.GreedyFuncProp ``FaithfulThreads.greedyFunc_proven,
  threadsEntry "concurrencycov-threading-greedy-worker" "threadsfor_fun(greedy)" "The greedy loop worker takes channel items, binds the escaped index, and executes the escaped body." "base/threadingconstructs.jl:434-439" ``FaithfulThreads.GreedyWorkerProp ``FaithfulThreads.greedyWorker_proven,
  threadsEntry "concurrencycov-threading-greedy-comprehension" "greedy_comprehension_expr" "The greedy comprehension generator builds predicate, inferred type, producer and result channels, workers, runner, close, type correction, and optional reshape in order." "base/threadingconstructs.jl:444-481" ``FaithfulThreads.GreedyComprehensionProp ``FaithfulThreads.greedyComprehension_proven,
  threadsEntry "concurrencycov-threading-greedy-comprehension-worker" "threadsfor_fun(greedy-comprehension)" "The greedy comprehension worker takes each channel item, tests the predicate, binds the index, and adds the body result with the selected flattening." "base/threadingconstructs.jl:467-474" ``FaithfulThreads.GreedyComprehensionWorkerProp ``FaithfulThreads.greedyComprehensionWorker_proven,
  threadsEntry "concurrencycov-threading-work-distribution" "_work_distribution_code" "Work distribution computes divrem, handles fewer iterations than threads, derives first and last, and apportions the remainder in source order." "base/threadingconstructs.jl:484-511" ``FaithfulThreads.WorkDistributionProp ``FaithfulThreads.workDistribution_proven,
  threadsEntry "concurrencycov-threading-default-func" "default_func" "default_func captures items and emits a worker using the shared distribution code and escaped loop body." "base/threadingconstructs.jl:513-527" ``FaithfulThreads.DefaultFuncProp ``FaithfulThreads.defaultFunc_proven,
  threadsEntry "concurrencycov-threading-default-func-worker" "threadsfor_fun(default)" "The default loop worker computes its contiguous range, binds each indexed item, and executes the escaped body." "base/threadingconstructs.jl:517-524" ``FaithfulThreads.DefaultFuncWorkerProp ``FaithfulThreads.defaultFuncWorker_proven,
  threadsEntry "concurrencycov-threading-default-comprehension" "default_comprehension_expr" "The default comprehension generator builds items, predicate, inferred type, per-task buffers, workers, runner, concatenation, and final type correction in order." "base/threadingconstructs.jl:529-565" ``FaithfulThreads.DefaultComprehensionProp ``FaithfulThreads.defaultComprehension_proven,
  threadsEntry "concurrencycov-threading-default-comprehension-worker" "threadsfor_fun(default-comprehension)" "The default comprehension worker computes its range, selects its task buffer, tests each item, binds the index, and appends the body result." "base/threadingconstructs.jl:547-558" ``FaithfulThreads.DefaultComprehensionWorkerProp ``FaithfulThreads.defaultComprehensionWorker_proven,
  threadsEntry "concurrencycov-threading-macro" "@threads" "@threads validates argument count and quoted schedule, then selects comprehension, typed comprehension, simple for loop, or the documented error." "base/threadingconstructs.jl:789-824" ``FaithfulThreads.ThreadsMacroProp ``FaithfulThreads.threadsMacro_proven,
  threadsEntry "concurrencycov-threading-spawn-set-pool" "_spawn_set_thrpool" "_spawn_set_thrpool converts the pool, falls back to default for foreign or empty pools, calls the runtime setter, asserts success, and returns nothing." "base/threadingconstructs.jl:826-834" ``FaithfulThreads.SpawnSetPoolProp ``FaithfulThreads.spawnSetPool_proven,
  threadsEntry "concurrencycov-threading-spawn" "@spawn" "@spawn validates optional pool syntax, lifts interpolation, constructs a nonsticky task, resolves samepool, sets pool, registers with sync, schedules, and returns the task." "base/threadingconstructs.jl:880-920" ``FaithfulThreads.SpawnMacroProp ``FaithfulThreads.spawnMacro_proven
]

private def lockEntry (id fn source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/lock.jl", juliaFns := [fn]
    statement := s!"{fn} follows its source branches, checks, calls, mutations, and return order for every allowed input."
    source, status := .proven, prop, thm := some thm }

def faithfulLockEntries : List Entry := [
  lockEntry "concurrencycov-lock-current-task" "current_task" "base/lock.jl:10" ``FaithfulLock.CurrentTaskProp ``FaithfulLock.currentTask_proven,
  lockEntry "concurrencycov-lock-reentrant-ctor" "ReentrantLock" "base/lock.jl:85" ``FaithfulLock.ReentrantCtorProp ``FaithfulLock.reentrantCtor_proven,
  lockEntry "concurrencycov-lock-assert" "assert_havelock" "base/lock.jl:88" ``FaithfulLock.AssertHavelockProp ``FaithfulLock.assertHavelock_proven,
  lockEntry "concurrencycov-lock-show-short" "show(::ReentrantLock)" "base/lock.jl:90" ``FaithfulLock.ShowLockProp ``FaithfulLock.showLock_proven,
  lockEntry "concurrencycov-lock-show-plain" "show(::MIME,::ReentrantLock)" "base/lock.jl:92-102" ``FaithfulLock.ShowPlainProp ``FaithfulLock.showPlain_proven,
  lockEntry "concurrencycov-lock-islocked" "islocked(::ReentrantLock)" "base/lock.jl:143-145" ``FaithfulLock.IslockedProp ``FaithfulLock.islocked_proven,
  lockEntry "concurrencycov-lock-trylock" "trylock(::ReentrantLock)" "base/lock.jl:165-172" ``FaithfulLock.TrylockProp ``FaithfulLock.trylock_proven,
  lockEntry "concurrencycov-lock-trylock-internal" "_trylock" "base/lock.jl:173-183" ``FaithfulLock.TrylockSlowProp ``FaithfulLock.trylockSlow_proven,
  lockEntry "concurrencycov-lock-lock" "lock(::ReentrantLock)" "base/lock.jl:194-257" ``FaithfulLock.LockProp ``FaithfulLock.lock_proven,
  lockEntry "concurrencycov-lock-slowlock" "slowlock" "base/lock.jl:196-255" ``FaithfulLock.SlowlockProp ``FaithfulLock.slowlock_proven,
  lockEntry "concurrencycov-lock-condition-lock" "lock(::GenericCondition{ReentrantLock})" "base/lock.jl:263-264" ``FaithfulLock.ConditionLockProp ``FaithfulLock.conditionLock_proven,
  lockEntry "concurrencycov-lock-wait-no-relock" "wait_no_relock" "base/lock.jl:266-296" ``FaithfulLock.WaitNoRelockProp ``FaithfulLock.waitNoRelock_proven,
  lockEntry "concurrencycov-lock-uncancellable" "_uncancellable_lock(::ReentrantLock)" "base/lock.jl:299" ``FaithfulLock.UncancellableProp ``FaithfulLock.uncancellable_proven,
  lockEntry "concurrencycov-lock-relockall-one" "relockall_but_one" "base/lock.jl:301-305" ``FaithfulLock.RelockallButOneProp ``FaithfulLock.relockallButOne_proven,
  lockEntry "concurrencycov-lock-unlock" "unlock(::ReentrantLock)" "base/lock.jl:315-348" ``FaithfulLock.UnlockProp ``FaithfulLock.unlock_proven,
  lockEntry "concurrencycov-lock-unlock-internal" "_unlock" "base/lock.jl:318-346" ``FaithfulLock.UnlockInnerProp ``FaithfulLock.unlockInner_proven,
  lockEntry "concurrencycov-lock-notifywaiters" "notifywaiters" "base/lock.jl:327-341" ``FaithfulLock.NotifywaitersProp ``FaithfulLock.notifywaiters_proven,
  lockEntry "concurrencycov-lock-unlockall" "unlockall" "base/lock.jl:350-354" ``FaithfulLock.UnlockallProp ``FaithfulLock.unlockall_proven,
  lockEntry "concurrencycov-lock-relockall" "relockall" "base/lock.jl:356-365" ``FaithfulLock.RelockallProp ``FaithfulLock.relockall_proven,
  lockEntry "concurrencycov-lock-generic-do" "lock(f,::AbstractLock)" "base/lock.jl:382-389" ``FaithfulLock.GenericLockDoProp ``FaithfulLock.genericLockDo_proven,
  lockEntry "concurrencycov-lock-reentrant-do" "lock(f,::ReentrantLock)" "base/lock.jl:392-399" ``FaithfulLock.ReentrantLockDoProp ``FaithfulLock.reentrantLockDo_proven,
  lockEntry "concurrencycov-lock-generic-try-do" "trylock(f,::AbstractLock)" "base/lock.jl:401-410" ``FaithfulLock.GenericTrylockDoProp ``FaithfulLock.genericTrylockDo_proven,
  lockEntry "concurrencycov-lock-macro" "@lock" "base/lock.jl:431-441" ``FaithfulLock.LockMacroProp ``FaithfulLock.lockMacro_proven,
  lockEntry "concurrencycov-lock-nofail" "@lock_nofail" "base/lock.jl:450-458" ``FaithfulLock.LockNofailProp ``FaithfulLock.lockNofail_proven,
  lockEntry "concurrencycov-lock-lockable-ctor" "Lockable" "base/lock.jl:490" ``FaithfulLock.LockableCtorProp ``FaithfulLock.lockableCtor_proven,
  lockEntry "concurrencycov-lock-lockable-get" "getindex(::Lockable)" "base/lock.jl:491" ``FaithfulLock.LockableGetProp ``FaithfulLock.lockableGet_proven,
  lockEntry "concurrencycov-lock-lockable-do" "lock(f,::Lockable)" "base/lock.jl:506-510" ``FaithfulLock.LockableDoProp ``FaithfulLock.lockableDo_proven,
  lockEntry "concurrencycov-lock-lockable-lock" "lock(::Lockable)" "base/lock.jl:513" ``FaithfulLock.LockableLockProp ``FaithfulLock.lockableLock_proven,
  lockEntry "concurrencycov-lock-lockable-try" "trylock(::Lockable)" "base/lock.jl:514" ``FaithfulLock.LockableTrylockProp ``FaithfulLock.lockableTrylock_proven,
  lockEntry "concurrencycov-lock-lockable-unlock" "unlock(::Lockable)" "base/lock.jl:515" ``FaithfulLock.LockableUnlockProp ``FaithfulLock.lockableUnlock_proven,
  lockEntry "concurrencycov-lock-semaphore-ctor" "Semaphore" "base/lock.jl:569" ``FaithfulLock.SemaphoreCtorProp ``FaithfulLock.semaphoreCtor_proven,
  lockEntry "concurrencycov-lock-semaphore-acquire" "acquire(::Semaphore)" "base/lock.jl:578-597" ``FaithfulLock.SemaphoreAcquireProp ``FaithfulLock.semaphoreAcquire_proven,
  lockEntry "concurrencycov-lock-semaphore-do" "acquire(f,::Semaphore)" "base/lock.jl:623-630" ``FaithfulLock.SemaphoreAcquireDoProp ``FaithfulLock.semaphoreAcquireDo_proven,
  lockEntry "concurrencycov-lock-semaphore-macro" "@acquire" "base/lock.jl:650-660" ``FaithfulLock.SemaphoreMacroProp ``FaithfulLock.semaphoreMacro_proven,
  lockEntry "concurrencycov-lock-semaphore-release" "release(::Semaphore)" "base/lock.jl:669-679" ``FaithfulLock.SemaphoreReleaseProp ``FaithfulLock.semaphoreRelease_proven,
  lockEntry "concurrencycov-lock-event-ctor" "Event" "base/lock.jl:705" ``FaithfulLock.EventCtorProp ``FaithfulLock.eventCtor_proven,
  lockEntry "concurrencycov-lock-event-wait" "wait(::Event)" "base/lock.jl:708-730" ``FaithfulLock.EventWaitProp ``FaithfulLock.eventWait_proven,
  lockEntry "concurrencycov-lock-event-notify" "notify(::Event)" "base/lock.jl:732-747" ``FaithfulLock.EventNotifyProp ``FaithfulLock.eventNotify_proven,
  lockEntry "concurrencycov-lock-event-reset" "reset(::Event)" "base/lock.jl:755-758" ``FaithfulLock.EventResetProp ``FaithfulLock.eventReset_proven,
  lockEntry "concurrencycov-lock-proc-ctor-tf" "OncePerProcess{T,F}" "base/lock.jl:808-811" ``FaithfulLock.ProcCtorTFProp ``FaithfulLock.procCtorTF_proven,
  lockEntry "concurrencycov-lock-proc-ctor-type" "OncePerProcess{T}(::Type)" "base/lock.jl:813" ``FaithfulLock.ProcCtorTypeProp ``FaithfulLock.procCtorType_proven,
  lockEntry "concurrencycov-lock-proc-ctor-t" "OncePerProcess{T}" "base/lock.jl:814" ``FaithfulLock.ProcCtorTProp ``FaithfulLock.procCtorT_proven,
  lockEntry "concurrencycov-lock-proc-ctor-any-type" "OncePerProcess(::Type)" "base/lock.jl:815" ``FaithfulLock.ProcCtorAnyTypeProp ``FaithfulLock.procCtorAnyType_proven,
  lockEntry "concurrencycov-lock-proc-ctor-any" "OncePerProcess" "base/lock.jl:816" ``FaithfulLock.ProcCtorAnyProp ``FaithfulLock.procCtorAny_proven,
  lockEntry "concurrencycov-lock-proc-call" "(::OncePerProcess)()" "base/lock.jl:817-848" ``FaithfulLock.CallProcProp ``FaithfulLock.callProc_proven,
  lockEntry "concurrencycov-lock-proc-init" "init_perprocesss" "base/lock.jl:820-845" ``FaithfulLock.InitProcProp ``FaithfulLock.initProc_proven,
  lockEntry "concurrencycov-lock-copy-monotonic" "copyto_monotonic!" "base/lock.jl:850-861" ``FaithfulLock.CopyMonotonicProp ``FaithfulLock.copyMonotonic_proven,
  lockEntry "concurrencycov-lock-fill-monotonic" "fill_monotonic!" "base/lock.jl:863-868" ``FaithfulLock.FillMonotonicProp ``FaithfulLock.fillMonotonic_proven,
  lockEntry "concurrencycov-lock-thread-ctor-tf" "OncePerThread{T,F}" "base/lock.jl:919-923" ``FaithfulLock.ThreadCtorTFProp ``FaithfulLock.threadCtorTF_proven,
  lockEntry "concurrencycov-lock-thread-ctor-type" "OncePerThread{T}(::Type)" "base/lock.jl:925" ``FaithfulLock.ThreadCtorTypeProp ``FaithfulLock.threadCtorType_proven,
  lockEntry "concurrencycov-lock-thread-ctor-t" "OncePerThread{T}" "base/lock.jl:926" ``FaithfulLock.ThreadCtorTProp ``FaithfulLock.threadCtorT_proven,
  lockEntry "concurrencycov-lock-thread-ctor-any-type" "OncePerThread(::Type)" "base/lock.jl:927" ``FaithfulLock.ThreadCtorAnyTypeProp ``FaithfulLock.threadCtorAnyType_proven,
  lockEntry "concurrencycov-lock-thread-ctor-any" "OncePerThread" "base/lock.jl:928" ``FaithfulLock.ThreadCtorAnyProp ``FaithfulLock.threadCtorAny_proven,
  lockEntry "concurrencycov-lock-thread-call" "(::OncePerThread)()" "base/lock.jl:929" ``FaithfulLock.CallThreadProp ``FaithfulLock.callThread_proven,
  lockEntry "concurrencycov-lock-thread-get" "getindex(::OncePerThread)" "base/lock.jl:930-1019" ``FaithfulLock.ThreadGetProp ``FaithfulLock.threadGet_proven,
  lockEntry "concurrencycov-lock-thread-init" "init_perthread" "base/lock.jl:936-1015" ``FaithfulLock.InitThreadProp ``FaithfulLock.initThread_proven,
  lockEntry "concurrencycov-lock-task-ctor-type" "OncePerTask{T}(::Type)" "base/lock.jl:1055" ``FaithfulLock.TaskCtorTypeProp ``FaithfulLock.taskCtorType_proven,
  lockEntry "concurrencycov-lock-task-ctor-t" "OncePerTask{T}" "base/lock.jl:1056" ``FaithfulLock.TaskCtorTProp ``FaithfulLock.taskCtorT_proven,
  lockEntry "concurrencycov-lock-task-ctor-tf" "OncePerTask{T,F}" "base/lock.jl:1057" ``FaithfulLock.TaskCtorTFProp ``FaithfulLock.taskCtorTF_proven,
  lockEntry "concurrencycov-lock-task-ctor-any-type" "OncePerTask(::Type)" "base/lock.jl:1058" ``FaithfulLock.TaskCtorAnyTypeProp ``FaithfulLock.taskCtorAnyType_proven,
  lockEntry "concurrencycov-lock-task-ctor-any" "OncePerTask" "base/lock.jl:1059" ``FaithfulLock.TaskCtorAnyProp ``FaithfulLock.taskCtorAny_proven,
  lockEntry "concurrencycov-lock-task-call" "(::OncePerTask)()" "base/lock.jl:1061-1063" ``FaithfulLock.CallTaskProp ``FaithfulLock.callTask_proven
]

end JuliaLean.ConcurrencyCov
