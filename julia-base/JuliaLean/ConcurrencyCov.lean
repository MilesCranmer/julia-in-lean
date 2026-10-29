import JuliaLean.Registry.Types
import JuliaLean.ConcurrencyCov.ThreadsProps
import JuliaLean.ConcurrencyCov.LocksProps
import JuliaLean.ConcurrencyCov.ParkProps
import JuliaLean.ConcurrencyCov.ChannelsCov
import JuliaLean.ConcurrencyCov.GcUtils
import JuliaLean.ConcurrencyCov.Threadcall
import JuliaLean.ConcurrencyCov.ThreadsOverloads
import JuliaLean.ConcurrencyCov.TimingProps
import JuliaLean.ConcurrencyCov.LoggingCov
import JuliaLean.ConcurrencyCov.FaithfulEntries

namespace JuliaLean.ConcurrencyCov

open JuliaLean.Registry

/-- Registry entries for concurrency, GC wrappers, timing, and logging coverage. -/
def entries : List Entry := [
  { id := "concurrencycov-thread-queries", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["threadid", "maxthreadid", "nthreads", "_nthreads_in_pool", "_tpid_to_sym",
      "_sym_to_tpid", "threadpool", "nthreadpools", "threadpoolsize", "threadpooltids", "ngcthreads"]
    statement := "Thread and pool query wrappers preserve the runtime values, conversions, validation, and source branch order."
    source := "base/threadingconstructs.jl:36-169", status := .proven
    prop := ``Threads.ThreadQueriesSpec, thm := some ``Threads.threadQueriesSpec_proven },
  { id := "concurrencycov-threadpooldescription-gc-range", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["threadpooldescription", "ngcthreads"]
    statement := "threadpooldescription labels exactly the GC-thread ids in the foreign pool as foreign: gc."
    source := "base/threadingconstructs.jl:106-117,169", status := .refuted
    prop := ``Threads.ThreadpoolDescriptionGc, thm := some ``Threads.threadpoolDescriptionGc_refuted
    issue := "none found (queries: threadpooldescription; ngcthreads foreign)"
    notes := "ngcthreads includes the mutator thread, so the first adopted foreign thread is mislabeled. P3." },
  { id := "concurrencycov-threads-macros", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["_threads_call", "_threading_run_expr", "_threadsfor", "_threadsfor_multi_iterator",
      "_threadsfor_comprehension", "_threadsfor_single_iterator", "@threads"]
    statement := "The threaded-loop macro validates arguments and selects the same loop or comprehension expansion as the source."
    source := "base/threadingconstructs.jl:182,257-389,789-824", status := .proven
    prop := ``Threads.ThreadsMacroSpec, thm := some ``Threads.threadsMacroSpec_proven },
  { id := "concurrencycov-threads-comprehensions", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["_comprehension_body_func", "_comprehension_eltype_expr", "_comprehension_pred_expr",
      "_comprehension_test_expr", "_comprehension_add_expr", "_comprehension_result",
      "_comprehension_widened_eltype", "_threadsfor_comprehension_fast", "greedy_func",
      "greedy_comprehension_expr", "default_comprehension_expr", "threadsfor_fun"]
    statement := "Generated comprehension helpers preserve body order, filtering, flattening, result shape, and element-type branch selection."
    source := "base/threadingconstructs.jl:331-565", status := .proven
    prop := ``Threads.ComprehensionSpec, thm := some ``Threads.comprehensionSpec_proven },
  { id := "concurrencycov-spawn", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["_spawn_set_thrpool", "@spawn"]
    statement := "Spawn validates its pool, resolves samepool, falls back from unavailable pools, registers with sync, and creates a non-sticky task."
    source := "base/threadingconstructs.jl:826-920", status := .proven
    prop := ``Threads.SpawnSpec, thm := some ``Threads.spawnSpec_proven },

  { id := "concurrencycov-park-protocol", juliaFile := "base/park.jl"
    juliaFns := ["wait_enqueue!", "wait_dequeue!", "wait_recheck", "_uncancellable_lock",
      "_source_wait_enqueue!", "WatcherWait"]
    statement := "Waitable protocol dispatch preserves source registrations, watcher severity floors, object slots, and sticky source dequeues."
    source := "base/park.jl:59-67,306-382", status := .proven
    prop := ``Park.WaitableProtocolSpec, thm := some ``Park.waitableProtocolSpec_proven },
  { id := "concurrencycov-park-entries", juliaFile := "base/park.jl"
    juliaFns := ["acquire_wait_entry!", "release_wait_entry!", "disarm!"]
    statement := "Wait-entry selection uses the specialized cache paths and disarms only the currently armed entry."
    source := "base/park.jl:90-106,370-373", status := .proven
    prop := ``Park.WaitEntrySpec, thm := some ``Park.waitEntrySpec_proven },
  { id := "concurrencycov-park-loops", juliaFile := "base/park.jl"
    juliaFns := ["_enqueue_until_fired", "_recheck_until_fired", "_dequeue_each!"]
    statement := "Park iterator helpers stop at the first fired waitable and dequeue all registrations in source order."
    source := "base/park.jl:146-180", status := .proven
    prop := ``Park.WaitLoopSpec, thm := some ``Park.waitLoopSpec_proven },
  { id := "concurrencycov-park-driver", juliaFile := "base/park.jl"
    juliaFns := ["park!", "repark!", "wait_safe_interrupt", "withdraw!", "interrupted_park_cleanup!"]
    statement := "Parking arms before registration, claims after recheck, and interrupt cleanup clears queue state before returning or rethrowing."
    source := "base/park.jl:132-142,191-301", status := .proven
    prop := ``Park.ParkDriverSpec, thm := some ``Park.parkDriverSpec_proven },
  { id := "concurrencycov-park-wait-token", juliaFile := "base/park.jl"
    juliaFns := ["wait(::CancellationToken)"]
    statement := "Token wait rejects its own governing token and returns an already-observed cancellation before parking."
    source := "base/park.jl:400-429", status := .proven
    prop := ``Park.WaitTokenSpec, thm := some ``Park.waitTokenSpec_proven },

  { id := "concurrencycov-channel-bodies", juliaFile := "base/channels.jl"
    juliaFns := ["push!(::AbstractChannel)", "popfirst!(::AbstractChannel)", "Channel{T}(::Integer)",
      "Channel", "close", "isopen", "isbuffered", "bind", "channeled_tasks",
      "showerror", "_increment_n_avail", "fetch_unbuffered", "isempty", "isfull",
      "lock", "unlock", "trylock", "eltype", "show", "IteratorSize"]
    statement := "Channel constructors, state wrappers, lock delegation, availability queries, display, and traits preserve source results and mutations."
    source := "base/channels.jl:10-158,178-381,387,408-415,535,648-794", status := .proven
    prop := ``ChannelsCov.ChannelBodies, thm := some ``ChannelsCov.channelBodies_proven },
  { id := "concurrencycov-channel-float-size-error", juliaFile := "base/channels.jl"
    juliaFns := ["Channel{T}(::Float64)", "Channel"]
    statement := "Every Float64 size outside 0, positive integers, and positive infinity throws the constructor size ArgumentError."
    source := "base/channels.jl:13-27,43-57", status := .refuted
    prop := ``ChannelsCov.FloatSizeArgumentError, thm := some ``ChannelsCov.floatSizeArgumentError_refuted
    issue := "none found (queries: Channel InexactError size; Channel Inf size float; Channel size NaN)"
    notes := "Negative infinity, NaN, and fractional values reach convert(Int, sz) first and throw InexactError. P3." },
  { id := "concurrencycov-channel-wrappers", juliaFile := "base/channels.jl"
    juliaFns := ["Channel{T}(func)", "Channel(func)", "close_chnl_on_taskdone", "lock(f, ::Channel)",
      "show(::MIME, ::Channel)"]
    statement := "Function constructors bind and start with the selected pool, task termination closes once, and higher-order lock and plain display wrappers preserve delegation."
    source := "base/channels.jl:139-158,367-381,699,752-767", status := .proven
    prop := ``ChannelsCov.ChannelWrapperSpec, thm := some ``ChannelsCov.channelWrapperSpec_proven },

  { id := "concurrencycov-spin-lock", juliaFile := "base/locks-mt.jl"
    juliaFns := ["SpinLock", "PaddedSpinLock", "assert_havelock", "lock", "trylock", "unlock", "islocked"]
    statement := "Spin locks start unlocked, acquire with the atomic swap, balance finalizer disabling, retry while owned, and reject unmatched unlock."
    source := "base/locks-mt.jl:46-115", status := .proven
    prop := ``Locks.SpinLockSpec, thm := some ``Locks.spinLockSpec_proven },

  { id := "concurrencycov-threadcall-bodies", juliaFile := "base/threadcall.jl"
    juliaFns := ["@threadcall", "threadcall_run", "threadcall_notify", "do_threadcall"]
    statement := "Threadcall validates tuple arity before conversion, invokes the callback, schedules and unpreserves on notification, and balances the limiter around queue and wait."
    source := "base/threadcall.jl:18-109", status := .proven
    prop := ``Threadcall.ThreadcallBodies, thm := some ``Threadcall.threadcallBodies_proven },
  { id := "concurrencycov-threadcall-pool-size", juliaFile := "base/threadcall.jl"
    juliaFns := ["@threadcall", "do_threadcall"]
    statement := "After restart, the threadcall concurrency limiter equals the process UV_THREADPOOL_SIZE as documented."
    source := "base/threadcall.jl:7-15,18-109", status := .refuted
    prop := ``Threadcall.ThreadcallPoolFollowsEnvironment,
    thm := some ``Threadcall.threadcallPoolFollowsEnvironment_refuted
    issue := "none found (queries: UV_THREADPOOL_SIZE threadcall; threadcall thread pool size; max_ccall_threads sysimage)"
    notes := "The constant is serialized into the system image at 4; a process restarted with UV_THREADPOOL_SIZE=8 still admits four calls. P3." },

  { id := "concurrencycov-threads-foreach", juliaFile := "base/threads_overloads.jl"
    juliaFns := ["Threads.foreach", "_apply_for_schedule"]
    statement := "Threaded foreach waits for the requested workers and applies each worker's channel items once; schedule traits select direct or spawn-and-wait application."
    source := "base/threads_overloads.jl:41-66", status := .proven
    prop := ``ThreadsOverloads.ThreadsForeachSpec, thm := some ``ThreadsOverloads.threadsForeachSpec_proven },

  { id := "concurrencycov-gc-finalizers", juliaFile := "base/gcutils.jl"
    juliaFns := ["==(::WeakRef)", "_check_mutable", "finalizer", "finalize"]
    statement := "WeakRef comparison delegates to isequal, and finalizer registration checks mutability before registering and returning its object."
    source := "base/gcutils.jl:37-106", status := .proven
    prop := ``GcUtils.FinalizerSpec, thm := some ``GcUtils.finalizerSpec_proven },
  { id := "concurrencycov-gc-wrappers", juliaFile := "base/gcutils.jl"
    juliaFns := ["GC.gc", "GC.enable", "GC.enable_finalizers", "GC.disable_finalizers",
      "GC.in_finalizer", "GC.@preserve", "GC.safepoint", "GC.enable_logging",
      "GC.logging_enabled", "GC.gc_active_impl"]
    statement := "GC wrappers select collection mode, balance task-local finalizer state, preserve expression results, and expose runtime logging and implementation values."
    source := "base/gcutils.jl:136-295", status := .proven
    prop := ``GcUtils.GcWrapperSpec, thm := some ``GcUtils.gcWrapperSpec_proven },

  { id := "concurrencycov-timing-counters", juliaFile := "base/timing.jl"
    juliaFns := ["gc_num", "gc_total_bytes", "GC_Diff", "gc_alloc_count", "cumulative_compile_time_ns",
      "cumulative_compile_timing", "gc_time_ns", "gc_live_bytes", "gc_page_utilization_data",
      "full_sweep_reasons", "jit_total_bytes", "gc_bytes"]
    statement := "Timing runtime queries and GC counter differences preserve fields, sums, wrapping subtraction, and compile-timing restoration."
    source := "base/timing.jl:79-197,511-517", status := .proven
    prop := ``Timing.GcCountersSpec, thm := some ``Timing.gcCountersSpec_proven },
  { id := "concurrencycov-timing-format", juliaFile := "base/timing.jl"
    juliaFns := ["prettyprint_getunits", "format_bytes"]
    statement := "Unit selection stays within its table and format_bytes preserves singular and documented binary or decimal examples."
    source := "base/timing.jl:202-252", status := .proven
    prop := ``Timing.FormatBytesSpec, thm := some ``Timing.formatBytesSpec_proven },
  { id := "concurrencycov-timing-print", juliaFile := "base/timing.jl"
    juliaFns := ["time_print"]
    statement := "The time printer applies source pluralization, counter conditions, message prefixes, and newline selection."
    source := "base/timing.jl:254-305", status := .proven
    prop := ``Timing.TimePrintSpec, thm := some ``Timing.timePrintSpec_proven },
  { id := "concurrencycov-timing-padded", juliaFile := "base/timing.jl"
    juliaFns := ["padded_nonzero_print"]
    statement := "The verbose counter printer pads labels to column 20 and suppresses zero values when requested."
    source := "base/timing.jl:212-217", status := .proven
    prop := ``Timing.PaddedPrintSpec, thm := some ``Timing.paddedPrintSpec_proven },
  { id := "concurrencycov-timev-elapsed-float", juliaFile := "base/timing.jl"
    juliaFns := ["@timev", "timev_print", "padded_nonzero_print"]
    statement := "The timev elapsed-time counter is printed as an integer nanosecond count."
    source := "base/timing.jl:307-324,435-481", status := .refuted
    prop := ``Timing.TimevElapsedInteger, thm := some ``Timing.timevElapsedInteger_refuted
    issue := "none found (queries: timev elapsed time; timev output; padded_nonzero_print)"
    notes := "timev multiplies seconds by 1e9 and prints a Float64. P3." },
  { id := "concurrencycov-timev-zero-counters", juliaFile := "base/timing.jl"
    juliaFns := ["@timev", "timev_print", "padded_nonzero_print"]
    statement := "Every counter line printed after the elapsed time by timev has a nonzero value."
    source := "base/timing.jl:307-324,435-481", status := .refuted
    prop := ``Timing.TimevNonzeroCounters, thm := some ``Timing.timevNonzeroCounters_refuted
    issue := "none found (queries: timev output; padded_nonzero_print; timev elapsed time)"
    notes := "timev_print forces seven zero-valued counters despite the docstring. P3." },
  { id := "concurrencycov-timing-measure", juliaFile := "base/timing.jl"
    juliaFns := ["__tryfinally", "@time", "@showtime", "@timev", "@elapsed", "@timed"]
    statement := "Timing macros restore instrumentation state, propagate exceptions, and return the expression value or elapsed counters from the same snapshots."
    source := "base/timing.jl:329-334,395-508,732-760", status := .proven
    prop := ``Timing.TimedSpec, thm := some ``Timing.timedSpec_proven },
  { id := "concurrencycov-timing-allocation", juliaFile := "base/timing.jl"
    juliaFns := ["allocated", "allocations", "@lock_conflicts", "@time_imports", "@trace_compile", "@trace_dispatch"]
    statement := "Allocation and bracket macros return source counter differences and restore profiling counters on every outcome."
    source := "base/timing.jl:519-534,672-683,764-798", status := .proven
    prop := ``Timing.CountersMacroSpec, thm := some ``Timing.countersMacroSpec_proven },
  { id := "concurrencycov-timing-measurer", juliaFile := "base/timing.jl"
    juliaFns := ["is_simply_call", "is_simple_atom", "_gen_allocation_measurer", "@allocated", "@allocations"]
    statement := "Allocation measurer generation selects direct calls only for simple atoms and non-dotted callees, otherwise using the source wrapper path."
    source := "base/timing.jl:537-645", status := .proven
    prop := ``Timing.MeasurerSpec, thm := some ``Timing.measurerSpec_proven },

  { id := "concurrencycov-logging-interface", juliaFile := "base/logging/logging.jl"
    juliaFns := ["catch_exceptions", "_invoked_shouldlog", "_invoked_min_enabled_level",
      "_invoked_catch_exceptions", "NullLogger", "LogLevel", "isless", "convert", "show"]
    statement := "Logger interface defaults, NullLogger, invocation barriers, and LogLevel conversion and display preserve source results."
    source := "base/logging/logging.jl:72-189", status := .proven
    prop := ``LoggingCov.LoggingInterfaceSpec, thm := some ``LoggingCov.loggingInterfaceSpec_proven },
  { id := "concurrencycov-logging-macros", juliaFile := "base/logging/logging.jl"
    juliaFns := ["@_sourceinfo", "@logmsg", "@debug", "@info", "@warn", "@error", "log_record_id",
      "default_group", "issimple", "issimplekw", "logmsg_code", "handle_message_nothrow",
      "default_group_code", "logging_error", "logmsg_shim", "LogState", "current_logstate"]
    statement := "Logging macros select source metadata, stable identifiers, record construction paths, exception handling, keyword pairing, and scoped-state fallback in source order."
    source := "base/logging/logging.jl:266-545", status := .proven
    prop := ``LoggingCov.LoggingMacroSpec, thm := some ``LoggingCov.loggingMacroSpec_proven },
  { id := "concurrencycov-simple-logger", juliaFile := "base/logging/logging.jl"
    juliaFns := ["global_logger", "SimpleLogger", "min_enabled_level(::SimpleLogger)",
      "catch_exceptions(::SimpleLogger)", "handle_message(::SimpleLogger)"]
    statement := "Global and SimpleLogger wrappers preserve the previous logger, minimum level, exception policy, per-id limit, and formatting decision order."
    source := "base/logging/logging.jl:631-734", status := .proven
    prop := ``LoggingCov.SimpleLoggerSpec, thm := some ``LoggingCov.simpleLoggerSpec_proven },
  { id := "concurrencycov-console-logger", juliaFile := "base/logging/ConsoleLogger.jl"
    juliaFns := ["ConsoleLogger", "shouldlog", "min_enabled_level", "showvalue", "default_logcolor", "default_metafmt"]
    statement := "ConsoleLogger constructors, limit filtering, value dispatch, color thresholds, and metadata formatting preserve source decisions."
    source := "base/logging/ConsoleLogger.jl:37-88", status := .proven
    prop := ``LoggingCov.ConsoleLoggerSpec, thm := some ``LoggingCov.consoleLoggerSpec_proven }
] ++ faithfulSmallEntries ++ faithfulTimingEntries ++ faithfulParkEntries ++ faithfulChannelEntries
  ++ faithfulLoggingEntries ++ faithfulConsoleEntries
  ++ faithfulThreadsEntries
  ++ faithfulLockEntries

end JuliaLean.ConcurrencyCov
