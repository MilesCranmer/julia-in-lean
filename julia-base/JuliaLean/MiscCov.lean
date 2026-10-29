import JuliaLean.Registry.Types
import JuliaLean.MiscCov.Deprecated
import JuliaLean.MiscCov.Experimental
import JuliaLean.MiscCov.Experimental2
import JuliaLean.MiscCov.Shell
import JuliaLean.MiscCov.CInterface
import JuliaLean.MiscCov.Module
import JuliaLean.MiscCov.RefScope
import JuliaLean.MiscCov.CRuntime
import JuliaLean.MiscCov.BaseJl
import JuliaLean.MiscCov.ParserInts
import JuliaLean.MiscCov.RyuProofs
import JuliaLean.MiscCov.RyuArith
import JuliaLean.MiscCov.RyuWrap

namespace JuliaLean.MiscCov

open JuliaLean.Registry Lean

private def proven (id file : String) (fns : List String) (statement source : String)
    (prop thm : Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .proven,
    prop, thm := some thm }

private def refuted (id file : String) (fns : List String) (statement source issue : String)
    (prop thm : Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue }

def ExperimentalConstIndexingClosed : Prop := @Experimental.ConstIndexing Unit
theorem experimentalConstIndexingClosed_proven : ExperimentalConstIndexingClosed :=
  Experimental.constIndexing_proven

def BaseExtContractClosed : Prop := @BaseExt.Contract Unit
theorem baseExtContractClosed_proven : BaseExtContractClosed := BaseExt.contract_proven

def RefValueContractClosed : Prop := @RefValue.Contract Unit
theorem refValueContractClosed_proven : RefValueContractClosed := RefValue.contract_proven

def ScopeContractClosed : Prop := @Scope.Contract Unit
theorem scopeContractClosed_proven : ScopeContractClosed := Scope.contract_proven

def PairContractClosed : Prop := @BaseJl.PairContract Unit Unit
theorem pairContractClosed_proven : PairContractClosed := BaseJl.pairContract_proven

/-- Registry entries of this area. -/
def entries : List Entry := [
  proven "misccov-deprecated-internal-change" "base/deprecated.jl" ["__has_internal_change"]
    "The cutoff and named-change branches return their documented Boolean result." "base/deprecated.jl:110-113"
    ``Deprecated.HasInternalChange ``Deprecated.hasInternalChange_proven,
  proven "misccov-deprecated-macro" "base/deprecated.jl" ["@deprecate", "cannot_export_nonsymbol"]
    "@deprecate validates signatures and emits the documented forwarding method and export." "base/deprecated.jl:179-231"
    ``Deprecated.DeprecateContract ``Deprecated.deprecateContract_proven,
  proven "misccov-depwarn" "base/deprecated.jl" ["depwarn", "_depwarn", "firstcaller"]
    "Deprecation levels and caller discovery produce the documented error or warning record." "base/deprecated.jl:253-317"
    ``Deprecated.DepwarnContract ``Deprecated.depwarnContract_proven,
  proven "misccov-deprecated-bindings" "base/deprecated.jl" ["deprecate", "@deprecate_binding", "@deprecate_stdlib", "@deprecate_moved"]
    "Binding deprecations emit the documented aliases, messages, exports and flags." "base/deprecated.jl:319-376"
    ``Deprecated.BindingContract ``Deprecated.bindingContract_proven,

  proven "misccov-experimental-const" "base/experimental.jl" ["IndexStyle", "size", "axes", "getindex"]
    "Const arrays preserve dimensions and return the stored value at every in-bounds index." "base/experimental.jl:19-39"
    ``ExperimentalConstIndexingClosed ``experimentalConstIndexingClosed_proven,
  refuted "misccov-max-methods-default" "base/experimental.jl" ["@max_methods"]
    "Every documented @max_methods setting expands successfully." "base/experimental.jl:55-66"
    "none found (queries: @max_methods default, max_methods default MethodError)"
    ``Experimental.MaxMethodsDoc ``Experimental.maxMethodsDoc_refuted,
  proven "misccov-experimental-options" "base/experimental.jl" ["@aliasscope", "@optlevel", "@max_methods", "@compiler_options", "@force_compile"]
    "Compiler-option macros validate inputs and emit the corresponding meta expressions." "base/experimental.jl:42-139"
    ``Experimental.OptionMacros ``Experimental.optionMacros_proven,
  proven "misccov-experimental-checked" "base/experimental.jl" ["make_all_arithmetic_checked", "+", "-", "*"]
    "Generated checked arithmetic methods return exact results or overflow errors." "base/experimental.jl:142-172"
    ``Experimental.CheckedArithmetic ``Experimental.checkedArithmetic_proven,
  proven "misccov-experimental-sync" "base/experimental.jl" ["sync_end"]
    "sync_end waits for every task and forwards every completion." "base/experimental.jl:180-198"
    ``Experimental.SyncContract ``Experimental.syncContract_proven,
  proven "misccov-experimental-sync-macro" "base/experimental.jl" ["@sync"]
    "@sync creates the channel, rewrites async calls and invokes sync_end." "base/experimental.jl:200-207"
    ``Experimental.SyncMacroShape ``Experimental.syncMacroShape_proven,
  proven "misccov-experimental-hints" "base/experimental.jl" ["register_error_hint", "show_error_hints"]
    "Error-hint handlers retain registration order and run for the exception type chain." "base/experimental.jl:214-257"
    ``Experimental.HintsContract ``Experimental.hintsContract_proven,
  proven "misccov-experimental-overlay" "base/experimental.jl" ["overlay_def!", "overlay", "consistent_overlay"]
    "Overlay helpers accept documented definitions and emit their matching metadata." "base/experimental.jl:265-355"
    ``Experimental.OverlayContract ``Experimental.overlayContract_proven,
  proven "misccov-experimental-methodtable" "base/experimental.jl" ["new_mt", "@MethodTable"]
    "MethodTable construction checks top-level use and preserves its name and module." "base/experimental.jl:363-379"
    ``Experimental.MethodTableContract ``Experimental.methodTableContract_proven,
  proven "misccov-experimental-runtime" "base/experimental.jl" ["make_io_thread", "entrypoint", "disable_new_worlds", "task_metrics", "task_running_time_ns", "task_wall_time_ns"]
    "Runtime helpers propagate errors, set flags and compute wrapped task times." "base/experimental.jl:387-471"
    ``Experimental.RuntimeContract ``Experimental.runtimeContract_proven,
  proven "misccov-experimental-wait" "base/experimental.jl" ["wait_with_timeout"]
    "Timed waits return the waiter, timeout or cancellation result from the first event." "base/experimental.jl:479-525"
    ``Experimental.WaitContract ``Experimental.waitContract_proven,
  proven "misccov-experimental-syntax" "base/experimental.jl" ["set_syntax_version", "@VERSION", "reexport"]
    "Syntax-version and reexport helpers validate and emit the documented module operations." "base/experimental.jl:533-598"
    ``Experimental.SyntaxContract ``Experimental.syntaxContract_proven,
  proven "misccov-experimental-prune-objcache" "base/experimental.jl" ["prune_objcache"]
    "A disabled cache is neither pruned nor copied, a failed prune skips compaction, and successful compaction returns the number removed."
    "base/experimental.jl:853-861" ``Experimental.PruneObjcacheContract ``Experimental.pruneObjcacheContract_proven,

  refuted "misccov-shell-fd-overflow" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "Every unsupported redirect descriptor produces the parser's unsupported-fd error." "base/shell.jl:195-201"
    "none found (queries: shell_parse fd overflow, unsupported fd redirect OverflowError)"
    ``Shell.FdErrorType ``Shell.fdErrorType_refuted,
  refuted "misccov-shell-redirect-before-pipe" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "A redirect operator immediately before a pipe is rejected for lacking a filename." "base/shell.jl:302-303"
    "none found (queries: shell_parse redirect before pipe)"
    ``Shell.RedirectNeedsFilename ``Shell.redirectNeedsFilename_refuted,
  refuted "misccov-shell-empty-word-redirect" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "A quoted empty argument immediately before a redirect remains an argument." "base/shell.jl:129,307"
    "none found (queries: shell_parse empty quoted argument redirect)"
    ``Shell.EmptyWordBeforeRedirect ``Shell.emptyWordBeforeRedirect_refuted,
  proven "misccov-shell-word-helpers" "base/shell.jl" ["push_nonempty!", "consume_upto!", "append_2to1!"]
    "Word helpers preserve nonempty spans and represent a quoted empty word." "base/shell.jl:63-77"
    ``Shell.WordHelpers ``Shell.wordHelpers_proven,
  proven "misccov-shell-dollar" "base/shell.jl" ["parse_dollar_interp"]
    "Dollar interpolation parses the next atom and rejects a terminal dollar sign." "base/shell.jl:86-103"
    ``Shell.DollarInterp ``Shell.dollarInterp_proven,
  proven "misccov-shell-redirect-word" "base/shell.jl" ["redirect_word_expr"]
    "Redirect words remain strings or become interpolation expressions according to their parts." "base/shell.jl:106-114"
    ``Shell.RedirectWord ``Shell.redirectWord_proven,
  proven "misccov-shell-build-segment" "base/shell.jl" ["build_seg_expr"]
    "Command segments and redirect flags produce the corresponding command or pipeline syntax." "base/shell.jl:328-343"
    ``Shell.BuildSegShape ``Shell.buildSegShape_proven,

  proven "misccov-baseext" "base/baseext.jl" ["VecElement", "convert", "Array", "Vector", "Matrix"]
    "VecElement and Array convenience methods preserve conversions, rank, dimensions and fill values." "base/baseext.jl:17-45"
    ``BaseExtContractClosed ``baseExtContractClosed_proven,
  proven "misccov-scope" "base/scope.jl" ["Scope"]
    "Scope constructors preserve existing scopes and extend a parent once per pair." "base/scope.jl:24-47"
    ``ScopeContractClosed ``scopeContractClosed_proven,

  proven "misccov-cfunction" "base/c.jl" ["unsafe_convert", "cfunction"]
    "CFunction conversion and syntax construction preserve pointer and signature arguments." "base/c.jl:32-52"
    ``CInterface.CfunctionContract ``CInterface.cfunctionContract_proven,
  proven "misccov-c-sigint" "base/c.jl" ["sigatomic_begin", "sigatomic_end", "disable_sigint", "reenable_sigint", "exit_on_sigint"]
    "Signal helpers balance the runtime counter and propagate results, errors and mode updates." "base/c.jl:55-107"
    ``CInterface.SigintContract ``CInterface.sigintContract_proven,
  refuted "misccov-ccallable-forward-decl" "base/c.jl" ["@ccallable", "expand_ccallable"]
    "Every non-method definition produces @ccallable's expected-method error." "base/c.jl:119-180"
    "none found (queries: @ccallable forward declaration FieldError)"
    ``CInterface.CcallableErrors ``CInterface.ccallableErrors_refuted,
  proven "misccov-ccallable-expand" "base/c.jl" ["_ccallable", "expand_ccallable", "@ccallable"]
    "@ccallable extracts and emits the registration and escaped definition." "base/c.jl:109-180"
    ``CInterface.CcallableExpand ``CInterface.ccallableExpand_proven,
  refuted "misccov-ccall-macro-parse-doc" "base/c.jl" ["ccall_macro_parse"]
    "ccall_macro_parse returns the four values and bare function described by its docstring." "base/c.jl:185-193"
    "none found (queries: ccall_macro_parse docstring tuple)"
    ``CInterface.CcallMacroParseDoc ``CInterface.ccallMacroParseDoc_refuted,
  proven "misccov-ccall-parse" "base/c.jl" ["pusharg!", "ccall_macro_parse"]
    "ccall parsing separates typed arguments and every call option." "base/c.jl:195-350"
    ``CInterface.CcallMacroParse ``CInterface.ccallMacroParse_proven,
  proven "misccov-ccall-lower" "base/c.jl" ["ccall_macro_lower", "@ccall", "ccall_effects"]
    "ccall lowering emits conversions and the requested convention, effects and safety flags." "base/c.jl:352-424"
    ``CInterface.CcallLower ``CInterface.ccallLower_proven,

  proven "misccov-module-import-path" "base/module.jl" ["check_macro_rename", "eval_import_path", "eval_import_path_all", "_eval_using"]
    "Import-path evaluation validates renames and preserves every path effect." "base/module.jl:3-154"
    ``Module.ImportPathContract ``Module.importPathContract_proven,
  proven "misccov-module-import" "base/module.jl" ["_eval_import"]
    "_eval_import processes paths in order and propagates the first error." "base/module.jl:156-236"
    ``Module.ImportContract ``Module.importContract_proven,

  proven "misccov-osutils-static" "base/osutils.jl" ["@static"]
    "@static evaluates conditional syntax recursively and preserves other expressions." "base/osutils.jl:24-48"
    ``Static.Contract ``Static.contract_proven,
  proven "misccov-flfrontend" "base/flfrontend.jl" ["fl_parse", "fl_lower"]
    "Frontend wrappers normalize inputs and preserve every parse and lowering option." "base/flfrontend.jl:5-29"
    ``FlFrontend.Contract ``FlFrontend.contract_proven,
  proven "misccov-coreir" "base/coreir.jl" ["PhiNode", "PartialStruct", "partialstruct_init_undefs", "==", "getproperty"]
    "Core IR constructors validate fields and expose structural equality and properties." "base/coreir.jl:3-67"
    ``CoreIR.Contract ``CoreIR.contract_proven,
  proven "misccov-opaque-closure" "base/opaque_closure.jl" ["@opaque", "generate_opaque_closure", "OpaqueClosure"]
    "Opaque-closure helpers preserve signature, bounds, arity, environment and options." "base/opaque_closure.jl:3-92"
    ``OpaqueClosure.Contract ``OpaqueClosure.contract_proven,

  proven "misccov-base-pair" "base/Base.jl" ["Pair"]
    "The typed Pair constructor converts each mismatched component exactly once." "base/Base.jl:10-13"
    ``PairContractClosed ``pairContractClosed_proven,
  proven "misccov-base-small" "base/Base.jl" ["array_new_memory", "sizeof", "isdebugbuild", "a_method_to_overwrite_in_test", "include", "IncludeInto", "in_sysimage"]
    "Small Base wrappers preserve ownership, byte size, flags, include arguments and membership." "base/Base.jl:46-57,87,135-137,350-363"
    ``BaseJl.SmallContract ``BaseJl.smallContract_proven,
  proven "misccov-base-sigint" "base/Base.jl" ["sigint_new_episode!", "sigint_close_episode!", "sigint_active_severity", "_sigint_dispatch_pass", "maybe_dispatch_sigint", "sigint_listener"]
    "Interrupt episodes preserve generation matching, monotone cancellation and dispatch claims." "base/Base.jl:445-553"
    ``BaseJl.SigintContract ``BaseJl.sigintContract_proven,
  proven "misccov-base-listeners" "base/Base.jl" ["profile_printing_listener", "start_profile_listener", "start_sigint_listener"]
    "Listener setup creates the required tasks, callbacks and finalizers." "base/Base.jl:370-407,563-589"
    ``BaseJl.ListenerContract ``BaseJl.listenerContract_proven,
  proven "misccov-base-init" "base/Base.jl" ["__init__"]
    "Base initialization performs each state reset and startup action in source order." "base/Base.jl:591-623"
    ``BaseJl.InitContract ``BaseJl.initContract_proven,
  proven "misccov-download" "base/download.jl" ["Downloads", "download", "do_download"]
    "Download wrappers load Downloads, select the path, transfer and return the path." "base/download.jl:3-25"
    ``BaseJl.DownloadContract ``BaseJl.downloadContract_proven,

  proven "misccov-parsers-helpers" "base/parsers/ints.jl" ["load8", "isdigits8", "digits8", "bytesin", "ishexdigits8", "hexdigits8", "digitvalue", "overflowfailure"]
    "Parser byte helpers load, classify and convert digits and distinguish invalid tails." "base/parsers/ints.jl:10-78"
    ``Parsers.HelperContract ``Parsers.helperContract_proven,
  proven "misccov-parsers-parse" "base/parsers/ints.jl" ["parseint", "parsevalue"]
    "Integer parsing follows each source branch and returns values or structured failures." "base/parsers/ints.jl:86-190"
    ``Parsers.ParseContract ``Parsers.parseContract_proven,
  proven "misccov-parsers-show" "base/parsers/Parsers.jl" ["show(::ParseFailure)"]
    "Each ParseFailure prints its qualified constant name." "base/parsers/Parsers.jl:52-53"
    ``Parsers.HelperContract ``Parsers.helperContract_proven,
  refuted "misccov-parsers-parsevalue-bool" "base/parsers/ints.jl" ["parseint", "parsevalue"]
    "parsevalue for every integer type returns a value or ParseFailure without throwing." "base/parsers/Parsers.jl:58-63; base/parsers/ints.jl:161-190"
    "PR #63971 (open, same Bool failure)"
    ``Parsers.ParsevalueNoThrow ``Parsers.parsevalueNoThrow_refuted,

  proven "misccov-ryu-log-range" "base/ryu/utils.jl" ["log10pow2", "log10pow5", "pow5bits"]
    "Fixed-point logarithm helpers are exact on Ryu's algorithmic ranges." "base/ryu/utils.jl:23-43"
    ``RyuUtils.LogApproxRange ``RyuUtils.logApproxRange_proven,
  refuted "misccov-ryu-log10pow-negative" "base/ryu/utils.jl" ["log10pow2", "log10pow5"]
    "The documented bounds make the logarithm helpers valid for negative exponents." "base/ryu/utils.jl:23-35"
    "none found (queries: Ryu log10pow2 negative, log10pow5 negative)"
    ``RyuUtils.LogApproxDoc ``RyuUtils.logApproxDoc_refuted,
  proven "misccov-ryu-mulshift" "base/ryu/utils.jl" ["mulshift", "mulshiftinvsplit", "mulshiftsplit"]
    "Split multiplication returns the exact requested high shifted product." "base/ryu/utils.jl:49-53,132-146"
    ``RyuUtils.MulshiftExact ``RyuUtils.mulshiftExact_proven,
  proven "misccov-ryu-index" "base/ryu/utils.jl" ["indexforexp", "pow10bitsforindex", "lengthforindex"]
    "Ryu index helpers implement their integer formulas." "base/ryu/utils.jl:55-57"
    ``RyuUtils.IndexHelpers ``RyuUtils.indexHelpers_proven,
  proven "misccov-ryu-powers" "base/ryu/utils.jl" ["pow5", "pow2"]
    "Power helpers recognize divisibility by their requested powers." "base/ryu/utils.jl:64-87"
    ``RyuUtils.Pow5Pow2Exact ``RyuUtils.pow5Pow2Exact_proven,
  refuted "misccov-ryu-decimallength-doc" "base/ryu/utils.jl" ["decimallength"]
    "decimallength returns the decimal digit count for every accepted integer." "base/ryu/utils.jl:91-130"
    "none found (queries: Ryu decimallength 18 digits, decimallength UInt32)"
    ``RyuUtils.DecimallengthDoc ``RyuUtils.decimallengthDoc_refuted,
  proven "misccov-ryu-decimallength-range" "base/ryu/utils.jl" ["decimallength"]
    "Each decimallength overload is exact throughout Ryu's used range." "base/ryu/utils.jl:94-130"
    ``RyuUtils.DecimallengthRange ``RyuUtils.decimallengthRange_proven,
  proven "misccov-ryu-umul256" "base/ryu/utils.jl" ["umul256", "umul256_hi"]
    "umul256 returns the exact low and high halves of the 256-bit product." "base/ryu/utils.jl:153-183"
    ``RyuUtils.Umul256Exact ``RyuUtils.umul256Exact_proven,
  proven "misccov-ryu-mod1e9" "base/ryu/utils.jl" ["mod1e9", "mulshiftmod1e9"]
    "Remainder helpers equal the mathematical result modulo one billion." "base/ryu/utils.jl:185-206"
    ``RyuUtils.Mod1e9Exact ``RyuUtils.mod1e9Exact_proven,
  proven "misccov-ryu-output-helpers" "base/ryu/utils.jl" ["append_sign", "append_d_digits"]
    "Output helpers write the requested sign and decimal separator." "base/ryu/utils.jl:208-230"
    ``RyuUtils.AppendSignDigits ``RyuUtils.appendSignDigits_proven,
  proven "misccov-ryu-table-formulas" "base/ryu/utils.jl" ["pow5split", "pow5invsplit"]
    "Power-of-five split values equal their integer formulas." "base/ryu/utils.jl:279-312"
    ``RyuUtils.Pow5SplitFormulas ``RyuUtils.pow5SplitFormulas_proven,
  refuted "misccov-ryu-pow5invsplit-bitcount" "base/ryu/utils.jl" ["pow5invsplit", "pow5_inv_bitcount"]
    "pow5invsplit has exactly the documented significant-bit count." "base/ryu/utils.jl:271-284"
    "none found (queries: Ryu pow5invsplit bitcount)"
    ``RyuUtils.Pow5InvsplitBitcount ``RyuUtils.pow5InvsplitBitcount_refuted,
  proven "misccov-ryu-lookups" "base/ryu/utils.jl" ["pow5invsplit_lookup", "pow5split_lookup"]
    "Generated lookup methods return their matching table entries." "base/ryu/utils.jl:286-325"
    ``RyuUtils.LookupTables ``RyuUtils.lookupTables_proven,
  proven "misccov-ryu-inverse-tables" "base/ryu/utils.jl" ["generateinversetables"]
    "Generated inverse tables preserve limb bounds, growth and entry counts." "base/ryu/utils.jl:242-268"
    ``RyuUtils.InverseTablesShape ``RyuUtils.inverseTablesShape_proven,

  proven "misccov-ryu-digit-counts" "base/ryu/Ryu.jl" ["neededdigits", "neededfloatdigits"]
    "Ryu buffer-size helpers return the source constants for every float width." "base/ryu/Ryu.jl:16-27"
    ``RyuWrap.DigitCounts ``RyuWrap.digitCounts_proven,
  proven "misccov-ryu-wrappers" "base/ryu/Ryu.jl" ["writeshortest", "writefixed", "writeexp", "show", "string", "print"]
    "Allocating format wrappers validate precision, size buffers and forward options." "base/ryu/Ryu.jl:48-145"
    ``RyuWrap.WrapperContract ``RyuWrap.wrapperContract_proven
]

end JuliaLean.MiscCov
