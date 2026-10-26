import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ErrorShow.Model
import JuliaLean.ErrorShow.Props
import JuliaLean.ErrorShow.Proofs
import JuliaLean.ErrorShow.Validation
import JuliaLean.ErrorShow.Coverage
import JuliaLean.ErrorShow.ErrorFaithful
import JuliaLean.ErrorShow.MultimediaEntries
import JuliaLean.ErrorShow.StacktracesEntries
import JuliaLean.ErrorShow.MethodshowEntries
import JuliaLean.ErrorShow.ArrayshowEntries
import JuliaLean.ErrorShow.ErrorshowEntries

namespace JuliaLean.ErrorShow

open JuliaLean.Registry
open JuliaLean.ErrorShow.Coverage
open JuliaLean.ErrorShow.ErrorFaithful

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "errorshow-base-exception-payloads", juliaFile := "base/errorshow.jl"
    juliaFns := ["showerror(::IO, ::Meta.ParseError)", "showerror(::IO, ::Core.TypeNameError)",
      "showerror(::IO, ::TypeError)", "showerror(::IO, ::LoadError)",
      "showerror(::IO, ::InitError)", "showerror(::IO, ::DomainError)",
      "showerror(::IO, ::SystemError)", "showerror(::IO, ::DivideError)",
      "showerror(::IO, ::StackOverflowError)", "showerror(::IO, ::UndefRefError)",
      "showerror(::IO, ::EOFError)", "showerror(::IO, ::ErrorException)",
      "showerror(::IO, ::KeyError)", "showerror(::IO, ::InterruptException)",
      "showerror(::IO, ::ArgumentError)", "showerror(::IO, ::AssertionError)",
      "showerror(::IO, ::OverflowError)", "showerror(::IO, ::UndefKeywordError)",
      "showerror(::IO, ::UndefVarError)", "showerror(::IO, ::InexactError)",
      "showerror(::IO, ::CanonicalIndexError)", "showerror(::IO, ::MethodError)",
      "showerror(::IO, ::FieldError)"]
    statement := "Every Base exception renderer in errorshow.jl emits all of the value, type, name, location, hint, and candidate payloads selected by its source branches, and the renderer returns a string for every well-formed modelled exception."
    source := "base/errorshow.jl:38-443", status := .proven
    prop := ``BaseExceptionRendering, thm := some ``baseExceptionRendering_proven
    notes := "Values rendered by other show methods enter as text. Valid InexactError values have the documented (name, T, val...) shape." },
  { id := "errorshow-fallback-show", juliaFile := "base/errorshow.jl"
    juliaFns := ["showerror(::IO, ::Any)", "show(::IO, ::Any)"]
    statement := "For a type without a specialized showerror method, showerror emits exactly the same representation as two-argument show."
    source := "base/errorshow.jl:4-30 (showerror docstring and fallback)", status := .proven
    prop := ``FallbackShowAgreement, thm := some ``fallbackShowAgreement_proven },
  { id := "errorshow-bounds-dimension", juliaFile := "base/errorshow.jl"
    juliaFns := ["showerror(::IO, ::BoundsError)", "showerror(::IO, ::DimensionMismatch)", "show_index"]
    statement := "BoundsError output contains the collection summary and every rendered index in order; DimensionMismatch output contains its message after the documented exception name."
    source := "base/errorshow.jl:32-76,170", status := .proven
    prop := ``BoundsAndDimensionMessages, thm := some ``boundsAndDimensionMessages_proven },
  { id := "errorshow-method-candidates", juliaFile := "base/errorshow.jl"
    juliaFns := ["showerror(::IO, ::MethodError)", "show_method_candidates"]
    statement := "MethodError candidate listing sorts by the source match score, emits at most three candidates, and records truncation exactly when more candidates exist."
    source := "base/errorshow.jl:260-408,656-865", status := .proven
    prop := ``MethodCandidateListing, thm := some ``methodCandidateListing_proven },
  { id := "errorshow-show-method-modes", juliaFile := "base/methodshow.jl"
    juliaFns := ["show(::IO, ::Method)", "show(::IO, ::MIME\"text/plain\", ::Method)", "show_method"]
    statement := "Method display always emits its signature; compact display keeps the location on one line, plain-text display puts it on the next line, and signature-only display omits it."
    source := "base/methodshow.jl:235-284", status := .proven
    prop := ``MethodDisplayModes, thm := some ``methodDisplayModes_proven },
  { id := "errorshow-matrix-alignment", juliaFile := "base/arrayshow.jl"
    juliaFns := ["alignment", "print_matrix_row", "print_matrix"]
    statement := "When a cell's left and right widths are bounded by its column alignment, print_matrix_row padding gives every cell that column's common total width."
    source := "base/arrayshow.jl:49-124", status := .proven
    prop := ``MatrixColumnAlignment, thm := some ``matrixColumnAlignment_proven },
  { id := "errorshow-matrix-corners", juliaFile := "base/arrayshow.jl"
    juliaFns := ["print_matrix", "_print_matrix", "alignment"]
    statement := "Limited matrix output selects the source-defined first and last row corners and splits the visible columns between the left and right corners, giving the odd extra item to the first corner."
    source := "base/arrayshow.jl:150-273", status := .proven
    prop := ``MatrixCornerTruncation, thm := some ``matrixCornerTruncation_proven },
  { id := "errorshow-print-array-routes", juliaFile := "base/arrayshow.jl"
    juliaFns := ["print_array", "show(::IO, ::MIME\"text/plain\", ::AbstractArray)", "show_zero_dim", "_show_empty"]
    statement := "Non-limited 0-dimensional arrays use the scalar route, empty vectors or compact empty arrays use two-argument show, and other empty arrays stop after their summary."
    source := "base/arrayshow.jl:359-414,497-533", status := .proven
    prop := ``PrintArrayRoutes, thm := some ``printArrayRoutes_proven },
  { id := "errorshow-stacktrace-lookup-remove", juliaFile := "base/stacktraces.jl"
    juliaFns := ["StackTraces.lookup", "StackTraces.remove_frames!"]
    statement := "StackTraces.lookup preserves raw frame order and reverses outermost-first DebugInfo traversal to innermost-first order; remove_frames! retains exactly the frames after the last matching frame."
    source := "base/stacktraces.jl:148-230,262-287", status := .proven
    prop := ``StackLookupAndRemoval, thm := some ``stackLookupAndRemoval_proven },
  { id := "errorshow-current-exceptions-order", juliaFile := "base/error.jl"
    juliaFns := ["current_exceptions", "rethrow", "throw"]
    statement := "current_exceptions reverses the runtime's newest-first exception stack so the root cause is first and the most recent exception is last; rethrow keeps the stack and throwing a new exception appends it."
    source := "base/error.jl:59-74,157-188", status := .proven
    prop := ``CurrentExceptionStackExact, thm := some ``currentExceptionStackExact_proven },
  { id := "errorshow-assert-message", juliaFile := "base/error.jl"
    juliaFns := ["@assert", "_assert_tostring", "__assert_tostring"]
    statement := "A failed assertion uses the condition text by default or the string-converted supplied message, while a true assertion returns without an error."
    source := "base/error.jl:223-268 (@assert docstring and expansion)", status := .proven
    prop := ``AssertMessageConstruction, thm := some ``assertMessageConstruction_proven },
  { id := "errorshow-mime-construction", juliaFile := "base/multimedia.jl"
    juliaFns := ["MIME", "@MIME_str", "print(::IO, ::MIME)", "show(::IO, ::MIME)"]
    statement := "MIME construction preserves the supplied media-type text, print emits that text, and show prefixes it with `MIME type `."
    source := "base/multimedia.jl:12-82", status := .proven
    prop := ``MimeConstructionAndPrinting, thm := some ``mimeConstructionAndPrinting_proven },
  { id := "errorshow-showable-displayable", juliaFile := "base/multimedia.jl"
    juliaFns := ["showable", "displayable", "display", "xdisplayable"]
    statement := "Default showable agrees with availability of the MIME show method; displayable is true exactly when a backend supports the MIME; display selects the last such backend in the display stack."
    source := "base/multimedia.jl:88-108,262-271,300-403", status := .proven
    prop := ``ShowableAndDisplayable, thm := some ``showableAndDisplayable_proven },
  { id := "errorshow-type-diff-methods", juliaFile := "base/errorshow.jl"
    juliaFns := ["typesof", "print_with_compare", "show_convert_error", "striptype",
      "show_type_diff", "show_separator", "show_type_match", "show_namedtuple_diff",
      "descend_params", "show_type_mismatch", "_resolves_to_self", "show_shadowed_type_hint"]
    statement := "Type comparison and mismatch helpers preserve the source recursion, separators, matched parameters, and color or !Matched annotations."
    source := "base/errorshow.jl:213-258,466-654", status := .proven
    prop := ``ErrorShowTypeDiffExact, thm := some ``errorShowTypeDiffExact },
  { id := "errorshow-backtrace-methods", juliaFile := "base/errorshow.jl"
    juliaFns := ["stacktrace_expand_basepaths", "stacktrace_contract_userdir", "stacktrace_linebreaks",
      "stacktrace_full_loading", "get_stacktrace_color", "_backtrace_find_and_remove_cycles",
      "showerror_nostdio",
      "_backtrace_print_repetition_closings!", "show_processed_backtrace", "print_stackframe",
      "parentmodule_before_main", "print_module_path_file", "show_backtrace",
      "_backtrace_collapse_and_count_repeated_frames", "_backtrace_remove_kwcall_frames!",
      "_backtrace_simplify_include_frames!", "_is_loading_frame", "_is_loading_anchor",
      "_backtrace_simplify_loading_frames!", "_backtrace_collapse_repeated_locations!",
      "process_backtrace", "show_exception_stack", "show(::IO, ::InterpreterIP)"]
    statement := "Backtrace environment, coloring, frame filtering, location collapsing, repetition counting, exception-stack ordering, and output routing follow the source sequence."
    source := "base/errorshow.jl:458-461,887-1446", status := .proven
    prop := ``ErrorShowBacktraceExact, thm := some ``errorShowBacktraceExact },
  { id := "errorshow-hint-methods", juliaFile := "base/errorshow.jl"
    juliaFns := ["noncallable_number_hint_handler", "nonsetable_type_hint_handler",
      "string_concatenation_hint_handler", "string_replace_hint_handler", "methods_on_iterable",
      "fielderror_dict_hint_handler", "fielderror_listfields_hint_handler", "_propertynames_bytype",
      "apply_type_unionall_hint_handler", "UndefVarError_hint", "_UndefVarError_warnfor",
      "size(::ExceptionStack)", "getindex(::ExceptionStack)", "show(::ExceptionStack)", "incomplete_tag"]
    statement := "Built-in error hints emit only under their source predicates, property-name collection removes duplicates, ExceptionStack delegates to its backing vector, and incomplete tags follow the parsed expression."
    source := "base/errorshow.jl:1451-1734", status := .proven
    prop := ``ErrorShowHintsExact, thm := some ``errorShowHintsExact },
  { id := "errorshow-method-signature-coverage", juliaFile := "base/methodshow.jl"
    juliaFns := ["strip_gensym", "argtype_decl", "method_argnames", "arg_decl_parts",
      "kwarg_decl", "show_method_params", "sym_to_string"]
    statement := "Method signature helpers strip generated names, render ordinary and Vararg declarations, filter keyword slots, move splats last, and render where parameters in source order."
    source := "base/methodshow.jl:5-143,223-233", status := .proven
    prop := ``MethodSignatureHelpersExact, thm := some ``methodSignatureHelpersExact },
  { id := "errorshow-method-location-coverage", juliaFile := "base/methodshow.jl"
    juliaFns := ["fixup_stdlib_path", "updated_methodloc", "functionloc", "show_method_list_header",
      "_modulecolor", "show_method_table", "show(::MethodList)", "show(::Core.MethodTable)",
      "inbase", "fileurl", "url(::Method)", "show(::MIME\"text/html\", ::Method)",
      "show(::MIME, ::MethodList)", "show(::MIME, ::AbstractVector{Method})"]
    statement := "Method locations, single-method selection, list headers and limits, Base source URLs, and plain or HTML method containers follow the source branches."
    source := "base/methodshow.jl:145-221,287-525", status := .proven
    prop := ``MethodLocationDisplayExact, thm := some ``methodLocationDisplayExact },
  { id := "errorshow-array-helper-coverage", juliaFile := "base/arrayshow.jl"
    juliaFns := ["replace_with_centered_mark", "print_matrix_vdots", "show_nd", "_show_nd",
      "_show_nd_label", "_show_oneline_truncated", "_show_nonempty", "show_vector"]
    statement := "Array helper models preserve centered markers, vertical-dot placement, limited higher-dimensional slice selection, literal corner selection, and delegation between display helpers."
    source := "base/arrayshow.jl:36-45,127-148,275-357,416-497,535-558", status := .proven
    prop := ``ArrayHelpersExact, thm := some ``arrayHelpersExact },
  { id := "errorshow-array-typeinfo-coverage", juliaFile := "base/arrayshow.jl"
    juliaFns := ["typeinfo_eltype", "_typeinfo_implicit", "typeinfo_implicit", "typeinfo_prefix"]
    statement := "Array type-info helpers return the element or Pair type when known, classify implicit types by the source predicates, and select the same explicit prefix branch."
    source := "base/arrayshow.jl:561-626", status := .proven
    prop := ``ArrayTypeInfoExact, thm := some ``arrayTypeInfoExact },
  { id := "errorshow-stackframe-core-coverage", juliaFile := "base/stacktraces.jl"
    juliaFns := ["StackFrame", "==(::StackFrame,::StackFrame)", "hash(::StackFrame)",
      "_add_linetable_frames!", "_add_di_frames!", "stacktrace", "remove_frames!(::Module)",
      "is_top_level_frame", "frame_method_or_module", "frame_mi", "frame_location"]
    statement := "StackFrame constructors, equality and hash fields, DebugInfo flattening, C-frame filtering, module removal, and metadata lookup follow the source fields and order."
    source := "base/stacktraces.jl:59-146,233-328", status := .proven
    prop := ``StackFrameMethodsExact, thm := some ``stackFrameMethodsExact },
  { id := "errorshow-stackframe-display-coverage", juliaFile := "base/stacktraces.jl"
    juliaFns := ["show_spec_linfo", "show_custom_spec_sig", "show_spec_sig", "show(::StackFrame)",
      "Base.parentmodule(::StackFrame)", "from(::StackFrame,::Module)"]
    statement := "Stack-frame signature, source location, inline annotation, parent module, and module-origin selection use the source fallbacks."
    source := "base/stacktraces.jl:330-455", status := .proven
    prop := ``StackFrameDisplayExact, thm := some ``stackFrameDisplayExact },
  { id := "errorshow-error-runtime-coverage", juliaFile := "base/error.jl"
    juliaFns := ["error(::Vararg)", "_reformat_bt", "backtrace", "catch_backtrace", "kwerr",
      "systemerror"]
    statement := "Error construction concatenates arguments, raw backtraces preserve native and interpreter entry order and reject unknown tags, and system errors obey their Boolean guard."
    source := "base/error.jl:47-57,82-220", status := .proven
    prop := ``ErrorRuntimeExact, thm := some ``errorRuntimeExact },
  { id := "errorshow-retry-coverage", juliaFile := "base/error.jl"
    juliaFns := ["ExponentialBackOff", "iterate(::ExponentialBackOff)", "length(::ExponentialBackOff)",
      "eltype(::Type{ExponentialBackOff})", "retry"]
    statement := "ExponentialBackOff validates nonnegative fields, clamps the sampled next delay, decrements its count, and retry sleeps only after an accepted failed attempt before its final unguarded call."
    source := "base/error.jl:270-342", status := .proven
    prop := ``JuliaLean.ErrorShow.Coverage.RetryExact,
    thm := some ``JuliaLean.ErrorShow.Coverage.retryExact },
  { id := "errorshow-multimedia-representation-coverage", juliaFile := "base/multimedia.jl"
    juliaFns := ["show(::IO,::MIME\"text/plain\",x)", "show(::IO,::AbstractString,x)",
      "repr", "_textrepr", "__binrepr", "_binrepr", "istextmime"]
    statement := "MIME representation chooses text or bytes by the exact text-MIME table, preserves raw strings and byte vectors in their special cases, and otherwise returns the selected show bytes."
    source := "base/multimedia.jl:77-78,110-236", status := .proven
    prop := ``MultimediaRepresentationExact, thm := some ``multimediaRepresentationExact },
  { id := "errorshow-multimedia-display-coverage", juliaFile := "base/multimedia.jl"
    juliaFns := ["display(::TextDisplay)", "displayable(::TextDisplay)", "xdisplayable", "display",
      "displayable", "redisplay"]
    statement := "Display and redisplay inspect backends from stack top to bottom, skip inapplicable backends, catch only the source-listed MethodErrors, and otherwise return or rethrow the first outcome."
    source := "base/multimedia.jl:258-293,338-456", status := .proven
    prop := ``MultimediaDisplayExact, thm := some ``multimediaDisplayExact },
  { id := "errorshow-multimedia-stack-coverage", juliaFile := "base/multimedia.jl"
    juliaFns := ["flush(::TextDisplay)", "close(::TextDisplay)", "pushdisplay", "popdisplay", "reinit_displays"]
    statement := "Display stack mutation appends, pops the top, removes the last matching backend, raises KeyError when absent, and reinitializes to stdout."
    source := "base/multimedia.jl:295-336", status := .proven
    prop := ``MultimediaStackExact, thm := some ``multimediaStackExact },
  { id := "errorshow-error-l47", juliaFile := "base/error.jl"
    juliaFns := ["error(s::Vararg{Any,N}) where N"]
    statement := "For every argument list, error constructs the same empty, single-string, invalid-singleton, or concatenated ErrorException selected by the source arity branches."
    source := "base/error.jl:47-57", status := .proven
    prop := ``ErrorVarargExact, thm := some ``errorVarargExact },
  { id := "errorshow-error-l73", juliaFile := "base/error.jl"
    juliaFns := ["rethrow()"]
    statement := "The zero-argument rethrow method invokes the current-exception rethrow operation for every call."
    source := "base/error.jl:73", status := .proven
    prop := ``RethrowCurrentExact, thm := some ``rethrowCurrentExact },
  { id := "errorshow-error-l74", juliaFile := "base/error.jl"
    juliaFns := ["rethrow(e)"]
    statement := "The one-argument rethrow method invokes the replacement-exception rethrow operation with that same exception."
    source := "base/error.jl:74", status := .proven
    prop := ``RethrowReplacementExact, thm := some ``rethrowReplacementExact },
  { id := "errorshow-error-l84", juliaFile := "base/error.jl"
    juliaFns := ["_reformat_bt"]
    statement := "Backtrace reformatting preserves native entries, decodes interpreter entries with the runtime metadata counts in order, and rejects every unknown tag."
    source := "base/error.jl:84-114", status := .proven
    prop := ``ReformatBacktraceExact, thm := some ``reformatBacktraceExact },
  { id := "errorshow-error-l121", juliaFile := "base/error.jl"
    juliaFns := ["backtrace()"]
    statement := "backtrace reformats exactly the runtime entries returned after skipping its own frame."
    source := "base/error.jl:121-128", status := .proven
    prop := ``BacktraceExact, thm := some ``backtraceExact },
  { id := "errorshow-error-l152", juliaFile := "base/error.jl"
    juliaFns := ["catch_backtrace()"]
    statement := "catch_backtrace reformats exactly the current exception's runtime backtrace entries."
    source := "base/error.jl:152-155", status := .proven
    prop := ``CatchBacktraceExact, thm := some ``catchBacktraceExact },
  { id := "errorshow-error-l179", juliaFile := "base/error.jl"
    juliaFns := ["current_exceptions"]
    statement := "For every runtime exception stack and backtrace option, current_exceptions reverses newest-first records and reformats or omits each backtrace in source order."
    source := "base/error.jl:179-189", status := .proven
    prop := ``CurrentExceptionsExact, thm := some ``currentExceptionsExact },
  { id := "errorshow-error-l192", juliaFile := "base/error.jl"
    juliaFns := ["kwerr"]
    statement := "kwerr constructs the Core.kwcall MethodError from the keyword tuple, positional arguments, and current world for every input."
    source := "base/error.jl:192-195", status := .proven
    prop := ``KeywordErrorExact, thm := some ``keywordErrorExact },
  { id := "errorshow-error-l204", juliaFile := "base/error.jl"
    juliaFns := ["systemerror(p, b::Bool)"]
    statement := "The Boolean systemerror overload throws with the current errno exactly when its condition is true."
    source := "base/error.jl:204", status := .proven
    prop := ``SystemErrorIfExact, thm := some ``systemErrorIfExact },
  { id := "errorshow-error-l205", juliaFile := "base/error.jl"
    juliaFns := ["systemerror(p, errno::Cint)"]
    statement := "The errno systemerror overload always constructs and throws the corresponding SystemError."
    source := "base/error.jl:205", status := .proven
    prop := ``SystemErrorNowExact, thm := some ``systemErrorNowExact },
  { id := "errorshow-error-l249", juliaFile := "base/error.jl"
    juliaFns := ["@assert"]
    statement := "For every condition and allowed message form, @assert returns nothing on true and throws AssertionError with the selected source message on false."
    source := "base/error.jl:249-263", status := .proven
    prop := ``AssertExpansionExact, thm := some ``assertExpansionExact },
  { id := "errorshow-error-l266", juliaFile := "base/error.jl"
    juliaFns := ["_assert_tostring"]
    statement := "_assert_tostring returns exactly the compiler-barrier call's string result for every message."
    source := "base/error.jl:266", status := .proven
    prop := ``AssertToStringExact, thm := some ``assertToStringExact },
  { id := "errorshow-error-l267", juliaFile := "base/error.jl"
    juliaFns := ["__assert_tostring"]
    statement := "__assert_tostring calls Base.string when available and otherwise prints the bootstrap value and returns the fixed bootstrap message."
    source := "base/error.jl:267-268", status := .proven
    prop := ``BootstrapAssertToStringExact, thm := some ``bootstrapAssertToStringExact },
  { id := "errorshow-error-l277", juliaFile := "base/error.jl"
    juliaFns := ["ExponentialBackOff(n, first_delay, max_delay, factor, jitter)"]
    statement := "The inner ExponentialBackOff constructor accepts exactly nonnegative fields and rejects every negative field."
    source := "base/error.jl:277-280", status := .proven
    prop := ``BackoffConstructorExact, thm := some ``backoffConstructorExact },
  { id := "errorshow-error-l290", juliaFile := "base/error.jl"
    juliaFns := ["ExponentialBackOff(; kwargs...)"]
    statement := "The keyword ExponentialBackOff constructor forwards every selected field to the validating inner constructor in source order."
    source := "base/error.jl:290-291", status := .proven
    prop := ``DefaultBackoffExact, thm := some ``defaultBackoffExact },
  { id := "errorshow-error-l292", juliaFile := "base/error.jl"
    juliaFns := ["iterate(::ExponentialBackOff)"]
    statement := "For every Backoff state and sampled jitter factor, iterate stops below one or returns the current delay, decremented count, and clamped next delay."
    source := "base/error.jl:292-298", status := .proven
    prop := ``IterateBackoffExact, thm := some ``iterateBackoffExact },
  { id := "errorshow-error-l299", juliaFile := "base/error.jl"
    juliaFns := ["length(::ExponentialBackOff)"]
    statement := "ExponentialBackOff length returns its n field for every instance."
    source := "base/error.jl:299", status := .proven
    prop := ``BackoffLengthExact, thm := some ``backoffLengthExact },
  { id := "errorshow-error-l300", juliaFile := "base/error.jl"
    juliaFns := ["eltype(::Type{ExponentialBackOff})"]
    statement := "ExponentialBackOff's element type is Float64 for every instance type."
    source := "base/error.jl:300", status := .proven
    prop := ``BackoffElementTypeExact, thm := some ``backoffElementTypeExact },
  { id := "errorshow-error-l322", juliaFile := "base/error.jl"
    juliaFns := ["retry"]
    statement := "For every delay and attempt sequence, retry returns on success, rethrows when check rejects, sleeps once per accepted failure, and makes the final call outside the catch."
    source := "base/error.jl:322-342", status := .proven
    prop := ``JuliaLean.ErrorShow.ErrorFaithful.RetryExact,
    thm := some ``JuliaLean.ErrorShow.ErrorFaithful.retryExact }
] ++ JuliaLean.ErrorShow.MultimediaEntries.entries
  ++ JuliaLean.ErrorShow.StacktracesEntries.entries
  ++ JuliaLean.ErrorShow.MethodshowEntries.entries
  ++ JuliaLean.ErrorShow.ArrayshowEntries.entries
  ++ JuliaLean.ErrorShow.ErrorshowEntries.entries

end JuliaLean.ErrorShow
