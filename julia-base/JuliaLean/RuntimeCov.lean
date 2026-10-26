import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RuntimeCov.OsInfo
import JuliaLean.RuntimeCov.Options
import JuliaLean.RuntimeCov.CpuId
import JuliaLean.RuntimeCov.SysInfo
import JuliaLean.RuntimeCov.InitDefs
import JuliaLean.RuntimeCov.Client
import JuliaLean.RuntimeCov.BaseCompiler
import JuliaLean.RuntimeCov.Layout
import JuliaLean.RuntimeCov.Fields
import JuliaLean.RuntimeCov.Modules
import JuliaLean.RuntimeCov.TypePreds
import JuliaLean.RuntimeCov.Methods
import JuliaLean.RuntimeCov.Precompilation
import JuliaLean.RuntimeCov.PrecompilationMore
import JuliaLean.RuntimeCov.InitDefsCoverage
import JuliaLean.RuntimeCov.RuntimeInternalsCoverage
namespace JuliaLean.RuntimeCov
open JuliaLean.Registry
open OsInfo Options CpuId SysInfo InitDefs Client BaseCompiler Layout Fields Modules TypePreds Methods Precompilation
open PrecompilationMore
open InitDefsCoverage
open RuntimeInternalsCoverage

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "runtimecov-isconst-globals", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["isconst(::Module, ::Symbol)", "isconst(::GlobalRef)"]
    statement := "Both global-constant queries return true exactly when their corresponding libjulia runtime query returns a nonzero C integer."
    source := "base/runtime_internals.jl:522-527; runtime-query wrapper invariant", status := .proven
    prop := ``IsconstGlobalBodies, thm := some ``isconstGlobalBodies_proven },
  { id := "runtimecov-initdefs-core", juliaFile := "base/initdefs.jl"
    juliaFns := ["exit(::Any)", "exit()", "foreground_task", "as_foreground_task", "isinteractive"]
    statement := "Exit converts only Int32-range codes, the zero-argument method uses zero, foreground-task replacement restores the prior task, and interactivity returns the runtime flag."
    source := "base/initdefs.jl:28-75; process and foreground-task invariants", status := .proven
    prop := ``CoreBodies, thm := some ``coreBodies_proven },
  { id := "runtimecov-initdefs-depot-append", juliaFile := "base/initdefs.jl"
    juliaFns := ["append_bundled_depot_path!"]
    statement := "Appending bundled depots preserves the old path as a prefix and leaves both bundled depots present."
    source := "base/initdefs.jl:132-138; path-update invariant", status := .proven
    prop := ``DepotAppendBodies, thm := some ``depotAppendBodies_proven },
  { id := "runtimecov-initdefs-current-project", juliaFile := "base/initdefs.jl"
    juliaFns := ["current_project(::AbstractString)", "current_project()"]
    statement := "Directory search returns only a project file accepted by the file predicate, and the zero-argument wrapper delegates the current directory or returns nothing on its caught error."
    source := "base/initdefs.jl:237-259; project-search invariant", status := .proven
    prop := ``CurrentProjectBodies, thm := some ``currentProjectBodies_proven },
  { id := "runtimecov-initdefs-active-init", juliaFile := "base/initdefs.jl"
    juliaFns := ["init_active_project", "init_named_env!", "cmd_suppresses_program"]
    statement := "Active-project initialization respects missing and empty settings, named-environment creation reports write success, and only -e/-E suppress a program."
    source := "base/initdefs.jl:297-325; initialization invariants", status := .proven
    prop := ``ActiveInitBodies, thm := some ``activeInitBodies_proven },
  { id := "runtimecov-initdefs-expand-special", juliaFile := "base/initdefs.jl"
    juliaFns := ["load_path_expand(::AbstractString)", "load_path_expand(::Nothing)"]
    statement := "LOAD_PATH expansion handles @, @., @temp, @stdlib, @script and nothing through their documented branches."
    source := "base/initdefs.jl:327-375; LOAD_PATH special-form documentation", status := .proven
    prop := ``ExpandSpecialBodies, thm := some ``expandSpecialBodies_proven },
  { id := "runtimecov-initdefs-active-paths", juliaFile := "base/initdefs.jl"
    juliaFns := ["active_project", "set_active_project", "active_manifest", "load_path"]
    statement := "Active project and manifest selection preserve their precedence, callbacks receive the stored project, and expanded load paths contain no duplicate resolved path."
    source := "base/initdefs.jl:382-469; active-path invariants", status := .proven
    prop := ``ActivePathBodies, thm := some ``activePathBodies_proven },
  { id := "runtimecov-initdefs-hooks", juliaFile := "base/initdefs.jl"
    juliaFns := ["atexit", "_atexit", "_run_atexit_hooks", "postoutput", "_postoutput",
      "at_disable_library_threading", "disable_library_threading"]
    statement := "Hook registration prepends callbacks until shutdown, atexit and postoutput run their recorded order and clear state, and library-threading hooks run in reverse registration order."
    source := "base/initdefs.jl:502-617; hook ordering and finalization invariants", status := .proven
    prop := ``HookBodies, thm := some ``hookBodies_proven },
  { id := "runtimecov-precomp-formatting-more", juliaFile := "base/precompilation.jl"
    juliaFns := ["format_verbose_timing", "dim", "col", "show_progress"]
    statement := "Verbose-timing parsing requires an include marker, its nested formatters preserve the requested dimming, and progress rendering either throttles without state change or records the new display time."
    source := "base/precompilation.jl:390-438,488-536; display-state invariants", status := .proven
    prop := ``FormattingMoreBodies, thm := some ``formattingMoreBodies_proven },
  { id := "runtimecov-precomp-environment", juliaFile := "base/precompilation.jl"
    juliaFns := ["ExplicitEnv", "collect_workspace_deps", "collect_workspace_deps!", "fixup_stdlib_deps!"]
    statement := "Explicit environments take the empty branch for missing projects, workspace traversal stops on zero fuel or seen projects, and stdlib fixups update only supplied dependency records."
    source := "base/precompilation.jl:567-911; environment and traversal invariants", status := .proven
    prop := ``EnvironmentBodies, thm := some ``environmentBodies_proven },
  { id := "runtimecov-precomp-graph", juliaFile := "base/precompilation.jl"
    juliaFns := ["full_name", "excluded_circular_deps_explanation", "collect_all_deps",
      "visit_indirect_deps!", "build_dep_graph", "detect_circular_deps!", "filter_dep_graph!",
      "preresolved_snapshot", "checked_now!"]
    statement := "Dependency-graph helpers name extensions, separate cycle members, traverse edges, filter only existing vertices, keep ready cache paths, and reject unchecked paths whose current checksum fails."
    source := "base/precompilation.jl:916-1204; dependency-graph and cache-trust invariants", status := .proven
    prop := ``GraphBodies, thm := some ``graphBodies_proven },
  { id := "runtimecov-precomp-public-background", juliaFile := "base/precompilation.jl"
    juliaFns := ["precompilepkgs", "is_precompiling_in_background", "is_package_pending",
      "mark_completed_pkgid!", "stop_background_precompile", "launch_background_precompile", "_precompilepkgs"]
    statement := "The public wrapper normalizes verbose and force options; background queries, completion, stop, reset, injection and launch decisions follow the recorded task state."
    source := "base/precompilation.jl:1337-1368,1459-1517,1860-2063; lifecycle invariants", status := .proven
    prop := ``PublicBackgroundBodies, thm := some ``publicBackgroundBodies_proven },
  { id := "runtimecov-precomp-loading-background", juliaFile := "base/precompilation.jl"
    juliaFns := ["precompile_for_loading", "_precompile_for_loading", "available", "label",
      "wait_for_pending_package", "broadcast_signal", "keyboard_tip", "monitor_background_precompile",
      "_monitor_background_precompile", "stop_monitoring_unless_waited_on", "_collect_reachable!"]
    statement := "Loading look-ahead obeys its three gates, selects available stale packages, and background monitoring follows pending, signal, keyboard, detach, cancel, interrupt and reachability state."
    source := "base/precompilation.jl:1384-1455,1476-1491,1535-1858,1965-1971; lifecycle invariants", status := .proven
    prop := ``LoadingBackgroundBodies, thm := some ``loadingBackgroundBodies_proven },
  { id := "runtimecov-precomp-process-display", juliaFile := "base/precompilation.jl"
    juliaFns := ["process_stats", "sample_peak_rss!", "should_stop", "make_signal_channel",
      "format_names_list", "resolved_version", "unverified_set"]
    statement := "Process probes return zeros on unsupported/error paths, peak RSS is monotone, stop flags accumulate, and the short name, version and unverified-cache helpers follow their branches."
    source := "base/precompilation.jl:2079-2122,2159-2200,2220-2225,2284-2289,2676; state invariants", status := .proven
    prop := ``ProcessDisplayBodies, thm := some ``processDisplayBodies_proven },
  { id := "runtimecov-precomp-messages", juliaFile := "base/precompilation.jl"
    juliaFns := ["poll_process_stats!", "describe_pkg", "print_header", "explain_reasons!",
      "loaded_version_differs", "loaded_version_conflicts", "stacked_version_conflicts",
      "env_display_name", "stacked_conflicts_message", "only_flags_mismatch",
      "loaded_conflicts_message", "spawn_print_loop!", "precompilepkgs_monitor_std",
      "precompile_pkgs_maybe_cachefile_lock", "precompile_cost_estimate"]
    statement := "Polling, package descriptions, headers, conflict explanations, print-loop decisions, pipe monitoring, cache locking and cost estimates preserve their documented values and accumulated state."
    source := "base/precompilation.jl:2126-2154,2202-2364,2366-2613; display and process-state invariants", status := .proven
    prop := ``MessageBodies, thm := some ``messageBodies_proven },
  { id := "runtimecov-precomp-scheduling", juliaFile := "base/precompilation.jl"
    juliaFns := ["SchedulePriorities", "schedule_priority", "schedule_height!", "is_stdlib_source",
      "failed_dependency", "spawn_precompile_tasks!", "drain_work_channel!",
      "report_precompile_results!", "do_precompile"]
    statement := "Scheduling computes dependency height and cost, classifies failures without losing packages, merges injected work, prioritizes final errors, and normalizes the main driver's task count."
    source := "base/precompilation.jl:2630-3481; scheduling and final-result invariants", status := .proven
    prop := ``SchedulingBodies, thm := some ``schedulingBodies_proven },
  { id := "runtimecov-precomp-jobserver", juliaFile := "base/precompilation.jl"
    juliaFns := ["setup_precompile_jobserver!", "teardown_precompile_jobserver!", "WorkerLimiter",
      "_jobserver_acquire_baseline", "_jobserver_release_baseline"]
    statement := "Jobserver setup records only a created pool, teardown removes it, the limiter starts empty, and baseline acquire/release never move the held-token count in the wrong direction."
    source := "base/precompilation.jl:20-108; jobserver and nonnegative-token invariants", status := .proven
    prop := ``JobserverBodies, thm := some ``jobserverBodies_proven },
  { id := "runtimecov-precomp-worker-limiter", juliaFile := "base/precompilation.jl"
    juliaFns := ["_acquire_slot", "_release_slot", "Base.acquire(::WorkerLimiter)",
      "Base.release(::WorkerLimiter)", "Base.acquire(::Any, ::WorkerLimiter)"]
    statement := "Worker acquire adds one active slot, failures release it, release removes one slot, and the callback form always releases after the callback."
    source := "base/precompilation.jl:110-158; worker-count invariant", status := .proven
    prop := ``WorkerBodies, thm := some ``workerBodies_proven },
  { id := "runtimecov-precomp-job-state", juliaFile := "base/precompilation.jl"
    juliaFns := ["PrecompileJob", "is_pending", "is_started", "is_recompiled", "is_soft_error",
      "is_failed", "is_dep_failed", "has_pid", "had_pid", "is_locked", "is_waiting"]
    statement := "A new precompile job is pending with no process, and each query reads exactly its corresponding status or state field."
    source := "base/precompilation.jl:183-195; record accessor invariant", status := .proven
    prop := ``JobQueriesBodies, thm := some ``jobQueriesBodies_proven },
  { id := "runtimecov-precomp-job-updates", juliaFile := "base/precompilation.jl"
    juliaFns := ["mark_started!", "mark_recompiled!", "mark_soft_error!", "mark_failed!",
      "mark_dep_failed!", "set_pid!", "clear_pid!", "clear_failure!"]
    statement := "Each job-state mutator changes the named fields, and clearing a failure restores pending status and empties the stored error and output."
    source := "base/precompilation.jl:197-210; record-update invariant", status := .proven
    prop := ``JobUpdatesBodies, thm := some ``jobUpdatesBodies_proven },
  { id := "runtimecov-precomp-background-lock", juliaFile := "base/precompilation.jl"
    juliaFns := ["Base.lock(::Any, ::BackgroundPrecompileState)",
      "Base.lock(::BackgroundPrecompileState)", "Base.unlock(::BackgroundPrecompileState)"]
    statement := "Background-state lock methods delegate to the contained lock with the same callback or unit argument."
    source := "base/precompilation.jl:336-338; delegation invariant", status := .proven
    prop := ``LockDelegateBodies, thm := some ``lockDelegateBodies_proven },
  { id := "runtimecov-precomp-formatting", juliaFile := "base/precompilation.jl"
    juliaFns := ["ansi_moveup", "Base.showerror", "Base.show", "can_fancyprint", "unstable_iocontext",
      "printpkgstyle", "timing_string", "format_verbose_timing_header", "color_string"]
    statement := "The short precompilation formatting helpers emit their documented prefixes, suffixes, context conversion, color wrappers and fixed timing header."
    source := "base/precompilation.jl:354-382,442,458-466; display invariant", status := .proven
    prop := ``FormattingBodies, thm := some ``formattingBodies_proven },
  { id := "runtimecov-precomp-cache-bytes", juliaFile := "base/precompilation.jl"
    juliaFns := ["_precompile_cache_bytes"]
    statement := "Cache byte counting sums the existing cache files and preserves sizes accumulated before a caught file-system error."
    source := "base/precompilation.jl:446-454; accumulator invariant", status := .proven
    prop := ``CacheBytesBody, thm := some ``cacheBytesBody_proven },
  { id := "runtimecov-precomp-progress-boundaries", juliaFile := "base/precompilation.jl"
    juliaFns := ["start_progress", "end_progress", "print_progress_bottom"]
    statement := "Progress start, end and bottom helpers emit their fixed ANSI control sequences."
    source := "base/precompilation.jl:486,538-540; display invariant", status := .proven
    prop := ``ProgressBoundaryBodies, thm := some ``progressBoundaryBodies_proven },
  { id := "runtimecov-scan-deps-unreported-cycle", juliaFile := "base/precompilation.jl"
    juliaFns := ["scan_pkg!", "scan_deps!"]
    statement := "Every reachable two-node dependency cycle is included in the cycle list used by the precompilation diagnostic."
    source := "base/precompilation.jl:924-992; diagnostic distinguishes cycle members from dependants", status := .refuted
    prop := ``AllCyclesReported, thm := some ``allCyclesReported_refuted
    issue := "none found (queries: precompilation circular dependency omitted cycle; scan_deps cycle precompile; excluded_circular_deps_explanation)"
    notes := "Counterexample: X and Y form one cycle, Z and W form another, and X also depends on Z; only the Z-W cycle is reported." },
  { id := "runtimecov-osinfo", juliaFile := "base/osinfo.jl"
    juliaFns := ["KERNEL", "isunix", "islinux", "isbsd", "isfreebsd", "isopenbsd", "isnetbsd",
      "isdragonfly", "iswindows", "isapple", "isjsvm", "detectwsl", "$f()"]
    statement := "OS predicates match exactly their kernel symbols, isunix throws on unknown systems, detectwsl needs Linux plus a WSL marker, and the generated zero-argument predicates apply their predicate to KERNEL."
    source := "base/osinfo.jl:1-172", status := .proven
    prop := ``OsPredicates, thm := some ``osPredicates_proven },
  { id := "runtimecov-options", juliaFile := "base/options.jl"
    juliaFns := ["JLOptions", "colored_text", "show(::IO, ::JLOptions)", "unsafe_load_commands", "is_file_tracked"]
    statement := "JLOptions loads the runtime record, colored_text honours the color option then FORCE_COLOR over NO_COLOR, show prints every field with separators between them, the command table stops at the first null, and is_file_tracked is the runtime answer."
    source := "base/options.jl:80-137", status := .proven
    prop := ``OptionsBodies, thm := some ``optionsBodies_proven },
  { id := "runtimecov-cpuid", juliaFile := "base/cpuid.jl"
    juliaFns := ["<=(::ISA, ::ISA)", "<(::ISA, ::ISA)", "_featurebytes_to_isa", "_cross_lookup_cpu", "_build_bit_to_name",
      "feature_names", "feature_name", "normalize_arch", "ISAs_by_family", "cpu_isa", "test_cpu_feature", "@cpu_supports"]
    statement := "ISA comparisons are feature-set inclusion, the byte decoder collects set bits, lookups and feature listings follow the runtime tables, and arch names normalize to their families."
    source := "base/cpuid.jl:4-312", status := .proven
    prop := ``CpuIdBodies, thm := some ``cpuIdBodies_proven },
  { id := "runtimecov-isa-isless-order", juliaFile := "base/cpuid.jl"
    juliaFns := ["isless(::ISA, ::ISA)"]
    statement := "isless on ISA values is a strict weak order (incomparability is transitive)."
    source := "invariant; sort and other ordered algorithms require it of isless", status := .refuted
    prop := ``IsaIslessStrictWeak, thm := some ``isaIslessStrictWeak_refuted
    issue := "none found (queries: CPUID ISA isless; ISA partial order isless)" },
  { id := "runtimecov-sysinfo", juliaFile := "base/sysinfo.jl"
    juliaFns := ["__init__", "__init_build", "CPUinfo", "show(::IO, ::CPUinfo)", "_cpu_summary", "cpu_summary", "cpu_info",
      "sysimage_target", "matched_sysimage_target", "uptime", "loadavg", "free_memory", "total_memory",
      "free_physical_memory", "total_physical_memory", "get_process_title", "set_process_title", "maxrss",
      "windows_version", "isexecutable", "isreadable", "iswritable", "which", "username"]
    statement := "Sys initialisation parses JULIA_CPU_THREADS with a positive fallback, CPU summaries group equal models, libuv queries throw exactly on negative status, memory totals respect the constrained limit, and which returns the first executable candidate."
    source := "base/sysinfo.jl:140-585", status := .proven
    prop := ``SysInfoBodies, thm := some ``sysInfoBodies_proven },
  { id := "runtimecov-initdefs-bodies", juliaFile := "base/initdefs.jl"
    juliaFns := ["exit", "foreground_task", "set_foreground_task!", "init_depot_path", "init_load_path", "load_path_expand",
      "active_project", "set_active_project", "active_manifest", "load_path", "atexit", "_atexit", "postoutput",
      "at_disable_library_threading", "disable_library_threading"]
    statement := "Startup definitions: exit codes, the foreground task, depot and load path initialisation, environment expansion, the active project and manifest, and the atexit, postoutput and library-threading hook lists run in their documented orders."
    source := "base/initdefs.jl:1-617", status := .proven
    prop := ``InitDefsBodies, thm := some ``initDefsBodies_proven },
  { id := "runtimecov-depot-path-documented", juliaFile := "base/initdefs.jl"
    juliaFns := ["init_depot_path", "append_bundled_depot_path!"]
    statement := "DEPOT_PATH follows the JULIA_DEPOT_PATH rules of the manual: empty entries expand to the default user depot or the bundled depots."
    source := "doc/src/manual/environment-variables.md (JULIA_DEPOT_PATH)", status := .proven
    prop := ``DepotPathDocumented, thm := some ``depotPathDocumented_proven },
  { id := "runtimecov-init-depot-path-duplicate", juliaFile := "base/initdefs.jl"
    juliaFns := ["init_depot_path"]
    statement := "init_depot_path produces a DEPOT_PATH without duplicate entries."
    source := "base/initdefs.jl (append_bundled_depot_path! deduplicates)", status := .refuted
    prop := ``DepotPathNoDuplicates, thm := some ``depotPathNoDuplicates_refuted
    issue := "none found (queries: JULIA_DEPOT_PATH duplicate; DEPOT_PATH duplicate entries)" },
  { id := "runtimecov-load-path-documented", juliaFile := "base/initdefs.jl"
    juliaFns := ["init_load_path", "parse_load_path"]
    statement := "LOAD_PATH follows the JULIA_LOAD_PATH rules: empty entries expand to the default load path."
    source := "doc/src/manual/environment-variables.md (JULIA_LOAD_PATH)", status := .proven
    prop := ``LoadPathDocumented, thm := some ``loadPathDocumented_proven },
  { id := "runtimecov-load-path-expand-script-prefix", juliaFile := "base/initdefs.jl"
    juliaFns := ["load_path_expand(::AbstractString)"]
    statement := "Named environments other than @script itself, such as @scripts, are looked up as named environments."
    source := "base/initdefs.jl LOAD_PATH docstring (@name entries)", status := .refuted
    prop := ``LoadPathNamedEnv, thm := some ``loadPathNamedEnv_refuted
    issue := "none found (queries: @script load path named environment; load_path_expand @script; related issue #55069)" },
  { id := "runtimecov-client", juliaFile := "base/client.jl"
    juliaFns := ["repl_color", "error_color", "warn_color", "info_color", "debug_color", "input_color", "answer_color",
      "stackframe_lineinfo_color", "stackframe_function_color", "repl_cmd", "shell_escape", "display_error",
      "scrub_repl_backtrace", "istrivialerror", "eval_user_input", "parse_input_line", "incomplete_tag", "exec_options",
      "load_julia_startup", "atreplinit", "__atreplinit", "run_main_repl", "run_std_repl", "_start", "repl_main", "@main"]
    statement := "REPL colors fall back to defaults, shell-mode cd and commands follow their documented cases, input parsing accumulates incomplete lines, option processing runs the command list in order, and the banner choice follows the banner option."
    source := "base/client.jl:1-802", status := .proven
    prop := ``ClientBodies, thm := some ``clientBodies_proven },
  { id := "runtimecov-base-compiler", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["include", "IncludeInto", "@inline", "@noinline", "@_boundscheck", "getproperty", "setproperty!",
      "dotgetproperty", "convert", "eval", "strcat", "time_ns", "process_sysimg_args!", "=="]
    statement := "Bootstrap definitions forward include, expand the meta macros, implement the property protocol with field conversion, and parse sysimage arguments in flag/value pairs."
    source := "base/Base_compiler.jl:1-434", status := .proven
    prop := ``BaseCompilerBodies, thm := some ``baseCompilerBodies_proven },
  { id := "runtimecov-layout", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["DataTypeLayout", "datatype_alignment", "uniontype_layout", "LLT_ALIGN", "aligned_sizeof", "gc_alignment",
      "datatype_haspadding", "datatype_isbitsegal", "datatype_nfields", "datatype_npointers", "datatype_pointerfree",
      "datatype_fielddesc_type", "datatype_arrayelem", "datatype_layoutsize", "FieldDesc", "DataTypeFieldDesc",
      "getindex(::DataTypeFieldDesc, ::Int)", "is_datatype_layoutopaque", "is_valid_intrinsic_elptr", "issingletontype"]
    statement := "Layout accessors read their flag bits and fields, alignment rounds up to a multiple of the power-of-two alignment, and field descriptors are bounds-checked."
    source := "base/runtime_internals.jl:620-813, 1194-1212", status := .proven
    prop := ``LayoutBodies, thm := some ``layoutBodies_proven },
  { id := "runtimecov-datatype-haspadding-doc", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["datatype_haspadding(::DataType)"]
    statement := "datatype_haspadding returns what its docstring says."
    source := "base/runtime_internals.jl docstring of datatype_haspadding", status := .refuted
    prop := ``HaspaddingDoc, thm := some ``haspaddingDoc_refuted
    issue := "#49318 (related; queries: datatype_haspadding)" },
  { id := "runtimecov-datatype-fielddesc-type-doc", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["datatype_fielddesc_type(::DataType)"]
    statement := "datatype_fielddesc_type returns the field-descriptor entry size its docstring describes."
    source := "base/runtime_internals.jl docstring of datatype_fielddesc_type", status := .refuted
    prop := ``FielddescTypeDoc, thm := some ``fielddescTypeDoc_refuted
    issue := "none found (queries: datatype_fielddesc_type)" },
  { id := "runtimecov-datatype-npointers-return-type", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["datatype_npointers(::DataType)"]
    statement := "datatype_npointers returns an Int, as its docstring signature declares."
    source := "base/runtime_internals.jl:725-729", status := .refuted
    prop := ``NpointersReturnType, thm := some ``npointersReturnType_refuted
    issue := "none found (queries: datatype_npointers)" },
  { id := "runtimecov-fields", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["_fieldnames", "fieldname", "fieldnames", "hasfield", "nameof", "parentmodule", "isconst",
      "isfieldatomic", "fieldoffset", "fieldindex", "_fieldindex_maythrow", "_fieldindex_nothrow", "_fieldindex",
      "argument_datatype", "argument_datatypename", "datatype_fieldcount", "_typename_noerror",
      "_fieldindex_error_type", "_fieldindex_noerror", "_fieldcount_noerror", "fieldcount", "fieldcount_noerror",
      "fieldtypes", "propertynames", "hasproperty"]
    statement := "Field reflection returns names and 1-based indices of a type's own fields, rejects out-of-range indices, treats out-of-bounds fields as const, and reports properties of modules, arrays and other values."
    source := "base/runtime_internals.jl:237-579, 1273-1514, 1679-1694", status := .proven
    prop := ``FieldsBodies, thm := some ``fieldsBodies_proven },
  { id := "runtimecov-hasfield-kind-types", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["hasfield(::Type, ::Symbol)", "fieldindex"]
    statement := "hasfield(T, name) returns a Bool for every type T."
    source := "base/runtime_internals.jl hasfield docstring", status := .refuted
    prop := ``HasfieldTotal, thm := some ``hasfieldTotal_refuted
    issue := "none found (queries: hasfield Union{}; hasfield MethodError; fieldindex TypeEq)" },
  { id := "runtimecov-modules", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["parentmodule", "is_root_module", "moduleroot", "@__MODULE__", "fullname", "moduleloc", "names",
      "unsorted_names", "isexported", "ispublic", "@__FUNCTION__", "isdeprecated", "binding_module",
      "is_defined_const_binding", "is_some_const_binding", "is_some_imported", "is_some_implicit",
      "is_some_explicit_imported", "is_some_binding_imported", "is_some_guard", "is_some_global",
      "lookup_binding_partition", "convert(::Type{Core.Binding}, ::GlobalRef)", "partition_restriction",
      "partition_owner", "binding_kind", "delete_binding", "set_binding_visibility!", "@locals",
      "min_world", "max_world", "get_world_counter", "tls_world_age", "get_require_world"]
    statement := "moduleroot is the first registered or self-parented module of the parent chain, fullname ends in the module's name, names is sorted, the partition-kind predicates respect their class inclusions, and set_binding_visibility! accepts exactly :none, :public and :export."
    source := "base/runtime_internals.jl:1-370, 580-618, 1636-1662", status := .proven
    prop := ``ModulesBodies, thm := some ``modulesBodies_proven },
  { id := "runtimecov-typepreds", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["datatype_fieldtypes", "ismutable", "ismutabletype", "ismutabletypename", "isstructtype",
      "isprimitivetype", "isbitstype", "isbits", "objectid", "isdispatchtuple", "datatype_ismutationfree",
      "ismutationfree", "datatype_isidentityfree", "isidentityfree", "iskindtype", "isconcretedispatch",
      "isdispatchelem", "isType", "isTypeEq", "isTypeEgal", "type_parameter", "isconcretetype", "isabstracttype",
      "typeintersect", "morespecific", "to_tuple_type", "signature_type", "get_methodtable",
      "has_bottom_parameter", "find_free_typevars", "rewrap_free_typevars", "typeintersect_env", "unionlen",
      "_uniontypes", "uniontypes", "hasintersect"]
    statement := "Type predicates read their flag bits, return false for non-types, see through UnionAll; struct types are neither primitive nor abstract; uniontypes lists exactly unionlen non-union members; to_tuple_type and signature_type build the documented tuple types."
    source := "base/runtime_internals.jl:620-623, 815-1226, 1532-1634, 1778-1789, 1999", status := .proven
    prop := ``TypePredsBodies, thm := some ``typePredsBodies_proven },
  { id := "runtimecov-iskindtype-abstract-kind", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["iskindtype"]
    statement := "Every type iskindtype accepts is concrete, as its docstring states."
    source := "base/runtime_internals.jl:1041-1048 (iskindtype docstring)", status := .refuted
    prop := ``KindsConcrete, thm := some ``kindsConcrete_refuted
    issue := "none found (queries: iskindtype; AnyType abstract kind; related PRs #61915 and #58774)" },
  { id := "runtimecov-methods", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["delete_method", "MethodList", "size(::MethodList)", "getindex(::MethodList, ::Integer)",
      "matches_to_methods", "methods", "methods_including_ambiguous", "_methods", "_methods_by_ftype",
      "hasgenerator", "_uncompressed_ir", "get_ci_mi", "generating_output", "ast_slotflag", "may_invoke_generator",
      "subst_trivial_bounds", "normalize_typevars", "get_nospecializeinfer_sig", "is_nospecialized",
      "is_nospecializeinfer", "specialize_method", "visit", "avisit", "specializations", "iterate",
      "length", "isempty", "uncompressed_ir", "has_image_globalref"]
    statement := "methods keeps exactly the runtime's matches defined in the requested modules, IR access reports generated and missing code, may_invoke_generator only accepts generators that do not read non-dispatch arguments, the method-table walk reads only in-bounds value slots, and the specializations iterator yields exactly the non-empty slots."
    source := "base/runtime_internals.jl:1701-2093", status := .proven
    prop := ``MethodsBodies, thm := some ``methodsBodies_proven }
]

end JuliaLean.RuntimeCov
