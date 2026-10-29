import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.StringsCovB.AnnProps
import JuliaLean.StringsCovB.AIOProps
import JuliaLean.StringsCovB.AIORProps
import JuliaLean.StringsCovB.RxProps
import JuliaLean.StringsCovB.UniProps

namespace JuliaLean.StringsCovB

open JuliaLean.Registry

private def proven (id file : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := file, juliaFns := fns, statement := statement, source := source,
    status := .proven, prop := prop, thm := some thm }

private def refuted (id file : String) (fns : List String) (statement source issue notes : String)
    (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := file, juliaFns := fns, statement := statement, source := source,
    status := .refuted, prop := prop, thm := some thm, issue := issue, notes := notes }

/-- Registry entries of this area. -/
def entries : List Entry := [
  proven "stringscovb-ann-constructors" "base/strings/annotated.jl"
    ["AnnotatedString", "AnnotatedChar", "convert", "String"]
    "Annotated string and character constructors preserve the represented text and annotation data."
    "base/strings/annotated.jl:64-144" ``Ann.CtorContract ``Ann.ctorContract,
  proven "stringscovb-ann-interface" "base/strings/annotated.jl"
    ["ncodeunits", "codeunit", "codeunits", "firstindex", "lastindex", "isvalid", "iterate", "getindex", "unannotate"]
    "The AbstractString interface forwards to the stored string and indexing selects the covering annotations."
    "base/strings/annotated.jl:146-199" ``Ann.InterfaceContract ``Ann.interfaceContract,
  proven "stringscovb-ann-show" "base/strings/annotated.jl" ["show", "AnnotatedChar"]
    "Display delegates to the underlying text while retaining the documented annotated wrappers."
    "base/strings/annotated.jl:204-224" ``Ann.ShowContract ``Ann.showContract,
  proven "stringscovb-ann-equality" "base/strings/annotated.jl" ["==", "cmp", "promote_rule"]
    "Annotated equality compares text and annotations, and mixed equality follows the underlying text."
    "base/strings/annotated.jl:227-269" ``Ann.EqContract ``Ann.eqContract,
  refuted "stringscovb-annotatedstring-char-region" "base/strings/annotated.jl" ["annotatedstring"]
    "Converting an AnnotatedChar to an AnnotatedString must cover all code units of the character."
    "base/strings/annotated.jl:272-306; annotation-region invariant"
    "none found (queries: annotatedstring AnnotatedChar multibyte region)"
    "A multibyte character receives region 1:1." ``Ann.AnnotatedstringCharRegion ``Ann.annotatedstringCharRegion_refuted,
  proven "stringscovb-ann-annotatedstring-forms" "base/strings/annotated.jl" ["annotatedstring", "AnnotatedString"]
    "Identity, plain-string, and SubString forms preserve text and shift annotations as their bodies specify."
    "base/strings/annotated.jl:272-312" ``Ann.AnnotatedstringForms ``Ann.annotatedstringForms,
  proven "stringscovb-ann-repeat-string" "base/strings/annotated.jl" ["repeat(::AnnotatedString, ::Integer)"]
    "Repeating an AnnotatedString repeats its bytes and shifts each annotation into every copy."
    "base/strings/annotated.jl:314-335" ``Ann.RepeatString ``Ann.repeatString,
  refuted "stringscovb-repeat-char-zero" "base/strings/annotated.jl" ["repeat(::AnnotatedChar, ::Integer)"]
    "Repeating an AnnotatedChar agrees with repeating its equivalent one-character AnnotatedString."
    "base/strings/annotated.jl:314-344; consistency invariant"
    "none found (queries: repeat AnnotatedChar zero)" "repeat(c, 0) keeps an empty annotation region."
    ``Ann.RepeatCharAsString ``Ann.repeatCharAsString_refuted,
  proven "stringscovb-ann-reverse-sub" "base/strings/annotated.jl" ["reverse(::SubString{<:AnnotatedString})"]
    "The SubString reverse method delegates through the converted AnnotatedString."
    "base/strings/annotated.jl:356-358" ``Ann.ReverseSub ``Ann.reverseSub_proven,
  proven "stringscovb-ann-annotate" "base/strings/annotated.jl" ["_annotate!", "annotate!"]
    "Annotation insertion mutates the stated target and preserves the underlying text."
    "base/strings/annotated.jl:364-400" ``Ann.AnnotateContract ``Ann.annotateContract,
  refuted "stringscovb-annotate-nothing-partial" "base/strings/annotated.jl" ["_annotate!", "annotate!"]
    "Annotating with nothing removes every matching annotation over the requested region."
    "base/strings/annotated.jl:364-383; annotate! removal contract"
    "none found (queries: annotate nothing partial overlap)" "Partially overlapping annotations remain."
    ``Ann.AnnotateNothingRemoves ``Ann.annotateNothingRemoves_refuted,
  proven "stringscovb-ann-annotations" "base/strings/annotated.jl" ["annotations"]
    "Annotation queries return exactly the annotations intersecting their requested region."
    "base/strings/annotated.jl:418-458" ``Ann.AnnotationsContract ``Ann.annotationsContract,
  refuted "stringscovb-chartransform-ascii-grow" "base/strings/annotated.jl" ["annotated_chartransform"]
    "Character transforms keep an annotation aligned with the transformed character's code units."
    "base/strings/annotated.jl:477-502; documented annotation-conservation invariant"
    "none found (queries: annotated_chartransform annotation offset)" "A one-byte character growing to two bytes shifts the start incorrectly."
    ``Ann.ChartransformAligned ``Ann.chartransformAligned_refuted,
  proven "stringscovb-ann-region-iterator" "base/strings/annotated.jl" ["Base.length", "Base.iterate", "Base.eltype", "eachregion"]
    "RegionIterator length, iteration bounds, and element type agree with its parallel region vectors."
    "base/strings/annotated.jl:504-609" ``Ann.RegionIterContract ``Ann.regionIterContract,
  proven "stringscovb-ann-events-sorted" "base/strings/annotated.jl" ["annotation_events"]
    "Annotation events are returned in nondecreasing byte position."
    "base/strings/annotated.jl:595-609" ``Ann.EventsSorted ``Ann.eventsSorted,
  proven "stringscovb-ann-events-forward" "base/strings/annotated.jl" ["annotation_events", "eachregion"]
    "The public annotation_events and eachregion forms forward their exact source arguments."
    "base/strings/annotated.jl:595-609" ``Ann.EventsForward ``Ann.eventsForward,

  proven "stringscovb-aio-forward" "base/strings/annotated_io.jl"
    ["AnnotatedIOBuffer", "copy", "pipe_reader", "pipe_writer", "position", "seek", "seekend", "skip", "annotations", "annotate!"]
    "Construction and forwarding methods preserve annotations and delegate IO state changes to the wrapped buffer."
    "base/strings/annotated_io.jl:5-33" ``AIO.ForwardContract ``AIO.forwardContract,
  proven "stringscovb-aio-clear-region" "base/strings/annotated_io.jl" ["_clear_annotations_in_region!"]
    "Clearing a region drops, truncates, or splits every overlapping annotation exactly once."
    "base/strings/annotated_io.jl:111-149" ``AIO.ClearRegionContract ``AIO.clearRegionContract,
  refuted "stringscovb-aio-empty-write-splits" "base/strings/annotated_io.jl" ["write(::AnnotatedIOBuffer, ::AnnotatedString)"]
    "Writing zero bytes leaves destination annotations unchanged."
    "base/strings/annotated_io.jl:35-41; write invariant"
    "none found (queries: AnnotatedIOBuffer empty write annotations)" "An empty middle write splits an annotation."
    ``AIO.WriteEmptyKeeps ``AIO.writeEmptyKeeps_refuted,
  refuted "stringscovb-aio-write-aio-clears-before" "base/strings/annotated_io.jl" ["write(::AnnotatedIOBuffer, ::AnnotatedIOBuffer)"]
    "Writing at a non-final position preserves annotations before the overwritten bytes."
    "base/strings/annotated_io.jl:50-60; write invariant"
    "none found (queries: AnnotatedIOBuffer write clears annotation)" "The byte before the write loses its annotation."
    ``AIO.WriteAioKeepsBefore ``AIO.writeAioKeepsBefore_refuted,
  refuted "stringscovb-aio-write-aio-drops-spanning" "base/strings/annotated_io.jl" ["write(::AnnotatedIOBuffer, ::AnnotatedIOBuffer)"]
    "Writing an AnnotatedIOBuffer carries every source annotation intersecting the readable bytes."
    "base/strings/annotated_io.jl:50-60"
    "none found (queries: AnnotatedIOBuffer write spanning annotation)" "Annotations starting before the source position are dropped."
    ``AIO.WriteAioCarries ``AIO.writeAioCarries_refuted,
  proven "stringscovb-aio-buffer" "base/strings/annotated_io.jl" ["write", "read", "truncate"]
    "Buffer writes update the wrapped bytes and annotation list according to the write span."
    "base/strings/annotated_io.jl:35-109" ``AIO.BufferContract ``AIO.bufferContract,
  proven "stringscovb-aio-read-truncate" "base/strings/annotated_io.jl" ["read", "truncate"]
    "Reads shift selected annotations to the returned value and truncate removes annotations beyond the new end."
    "base/strings/annotated_io.jl:81-109" ``AIO.ReadTruncateContract ``AIO.readTruncateContract,
  proven "stringscovb-aio-insert" "base/strings/annotated_io.jl" ["_insert_annotations!"]
    "Annotation insertion shifts new regions by the byte offset and updates the buffer annotation state."
    "base/strings/annotated_io.jl:168-232" ``AIO.InsertContract ``AIO.insertContract,
  proven "stringscovb-aio-display" "base/strings/annotated_io.jl"
    ["ansi_write", "ansi_write_", "Base.write", "Base.print", "Base.printstyled", "styled_print", "styled_print_", "Base.escape_string", "show", "show_annot", "show_annot_", "Base.show"]
    "Plain IO display methods emit the unannotated bytes, while AnnotatedIOBuffer display delegates to annotated writes."
    "base/strings/annotated_io.jl:340-425" ``AIO.DisplayContract ``AIO.displayContract,
  proven "stringscovb-replace-trivial" "base/strings/annotated_io.jl" ["replace"]
    "Annotated replacement preserves the source on an empty replacement list or zero count and forwards the plain-text pass."
    "base/strings/annotated_io.jl:240-338" ``AIOR.ReplaceTrivialContract ``AIOR.replaceTrivialContract,
  refuted "stringscovb-replace-clears-before" "base/strings/annotated_io.jl" ["replace"]
    "Replacement into a buffer preserves annotations strictly before the output span."
    "base/strings/annotated_io.jl:240-338; replacement invariant"
    "none found (queries: replace AnnotatedIOBuffer annotation before)" "The annotation on the preceding byte is cleared."
    ``AIOR.ReplaceKeepsBefore ``AIOR.replaceKeepsBefore_refuted,
  refuted "stringscovb-replace-end-empty-match" "base/strings/annotated_io.jl" ["replace"]
    "An annotated replacement inserted by an empty end match retains its annotations."
    "base/strings/annotated_io.jl:240-338; annotation-conservation invariant"
    "none found (queries: replace AnnotatedString empty end match annotation)" "The replacement text is written without its annotation."
    ``AIOR.ReplaceEndAnnotated ``AIOR.replaceEndAnnotated_refuted,
  refuted "stringscovb-replace-skipped-empty-annotation" "base/strings/annotated_io.jl" ["replace"]
    "Annotations from a skipped empty replacement do not attach to unrelated source text."
    "base/strings/annotated_io.jl:240-338; annotation-conservation invariant"
    "none found (queries: replace AnnotatedString skipped empty annotation)" "A skipped replacement annotates following original text."
    ``AIOR.ReplaceAnnotsInside ``AIOR.replaceAnnotsInside_refuted,

  proven "stringscovb-regex-show-flags" "base/regex.jl" ["Regex", "r_str", "show"]
    "Documented regex flags round-trip through the literal printer."
    "base/regex.jl:48-67,123-159" ``Rx.ShowFlagsRoundTrip ``Rx.showFlagsRoundTrip,
  proven "stringscovb-regex-unknown-flag" "base/regex.jl" ["Regex"]
    "An unknown regex flag throws instead of being ignored."
    "base/regex.jl:48-67" ``Rx.UnknownFlagThrows ``Rx.unknownFlagThrows,
  proven "stringscovb-regex-opts-str" "base/regex.jl" ["regex_opts_str", "wrap_string"]
    "Every documented imsx option subset maps to its ordered flag letters."
    "base/regex.jl:856-909" ``Rx.OptsStrContract ``Rx.optsStrContract,
  proven "stringscovb-regex-eq-hash" "base/regex.jl" ["==", "hash"]
    "Equal Regex values hash equally because both operations use the same three fields."
    "base/regex.jl:814-825" ``Rx.RegexEqHash ``Rx.regexEqHash,
  proven "stringscovb-regex-multiply" "base/regex.jl" ["*"]
    "Regex concatenation retains common match options and the unary form is identity."
    "base/regex.jl:856-877" ``Rx.MulContract ``Rx.mulContract,
  refuted "stringscovb-regex-execute-mask" "base/regex.jl" ["Regex"]
    "Every match option accepted by the Regex constructor is usable by PCRE matching."
    "base/regex.jl:29-45; base/pcre.jl:119-130"
    "none found (queries: EXECUTE_MASK NO_START_OPTIMIZE bad option value)" "NO_START_OPTIMIZE is accepted and every match rejects it."
    ``Rx.MatchOptionsUsable ``Rx.matchOptionsUsable_refuted,
  proven "stringscovb-regex-exec-free" "base/regex.jl" ["occursin", "startswith", "endswith"]
    "Successful regex predicate calls free their temporary PCRE match data."
    "base/regex.jl:306-378; base/pcre.jl:219-224" ``Rx.ExecRFrees ``Rx.execRFrees,
  refuted "stringscovb-match-data-leak" "base/regex.jl" ["match", "findnext", "occursin"]
    "Regex operations free PCRE match data on both return and exception paths."
    "base/regex.jl:430-512; base/pcre.jl:219-230; resource-lifetime invariant"
    "none found (queries: regex match_data leak free_match_data)" "Throwing calls leak one PCRE match-data block per call."
    ``Rx.MatchDataFreed ``Rx.matchDataFreed_refuted,
  refuted "stringscovb-haskey-nul" "base/regex.jl" ["haskey(::RegexMatch, name)"]
    "haskey returns a Boolean for every capture-group name."
    "base/regex.jl:293-297; haskey contract"
    "none found (queries: RegexMatch haskey NUL)" "A NUL byte raises ArgumentError."
    ``Rx.HaskeyNameTotal ``Rx.haskeyNameTotal_refuted,
  proven "stringscovb-regex-match" "base/regex.jl"
    ["RegexMatch", "keys", "getindex", "haskey", "iterate", "length", "eltype", "NamedTuple", "Dict"]
    "RegexMatch indexing, membership, iteration, keys, and conversions agree with its capture vector."
    "base/regex.jl:234-304" ``Rx.RegexMatchContract ``Rx.regexMatchContract,
  proven "stringscovb-regex-constructor" "base/regex.jl" ["Regex", "compile", "r_str", "show"]
    "Regex construction validates integer options, compiles once, and preserves pattern and option fields."
    "base/regex.jl:29-89,123-159" ``Rx.RegexCtorContract ``Rx.regexCtorContract,
  proven "stringscovb-regex-chop" "base/regex.jl" ["chopprefix", "chopsuffix"]
    "Regex prefix and suffix chopping follow the match and SubString branches in the source."
    "base/regex.jl:380-391" ``Rx.ChopContract ``Rx.chopContract,
  proven "stringscovb-regex-misc" "base/regex.jl"
    ["_annotatedmatch", "match", "ncodeunits", "codeunit", "isvalid", "iterate", "show", "s_str", "_write_capture", "replace_err", "RegexMatchIterator", "compile", "eltype", "IteratorSize", "wrap_string"]
    "Annotated matches, substitution strings, capture writes, and iterator wrappers preserve their source fields and bytes."
    "base/regex.jl:456-478,606-747,879-882" ``Rx.MiscContract ``Rx.miscContract,
  proven "stringscovb-regex-pat-replacer" "base/regex.jl"
    ["RegexAndMatchData", "_findnext_re", "findnext", "_pat_replacer", "_free_pat_replacer"]
    "Pattern replacement allocation and findnext wrappers follow their checked source bodies."
    "base/regex.jl:640-650,485-512" ``Rx.PatReplacerContract ``Rx.patReplacerContract,
  proven "stringscovb-pcre-capture-names" "base/pcre.jl" ["capture_names"]
    "capture_names decodes fixed-size PCRE name-table entries into their capture slots."
    "base/pcre.jl:265-282" ``Rx.CaptureNamesDecode ``Rx.captureNamesDecode,
  proven "stringscovb-pcre-local-context" "base/pcre.jl" ["create_match_context", "_tid", "_mth", "get_local_match_context"]
    "The thread-local match context grows its table, stores a non-null context, and reuses it."
    "base/pcre.jl:20-63" ``Rx.LocalMatchContext ``Rx.localMatchContext,
  proven "stringscovb-pcre-helpers" "base/pcre.jl"
    ["info", "ovec_length", "ovec_ptr", "err_message", "compile", "jit_compile", "substring_number_from_name", "substring_length_bynumber", "substring_copy_bynumber", "create_match_data", "free_re", "free_jit_stack", "free_match_context", "free_match_data"]
    "PCRE wrappers translate return codes, lengths, copied bytes, and object lifetimes as their source bodies specify."
    "base/pcre.jl:135-203,232-263" ``Rx.PcreHelpersContract ``Rx.pcreHelpersContract,
  proven "stringscovb-pcre-exec" "base/pcre.jl" ["_exec", "exec", "exec_r", "exec_r_data"]
    "Successful exec_r calls free their allocated match data and preserve the Boolean match result."
    "base/pcre.jl:210-230" ``Rx.ExecRFrees ``Rx.execRFrees

]

end JuliaLean.StringsCovB
