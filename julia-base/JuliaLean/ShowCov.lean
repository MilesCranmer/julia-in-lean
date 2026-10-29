import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ShowCov.Terminals
import JuliaLean.ShowCov.TermInfo
import JuliaLean.ShowCov.Truncate
import JuliaLean.ShowCov.StringsIO
import JuliaLean.ShowCov.IOContext
import JuliaLean.ShowCov.Values
import JuliaLean.ShowCov.Containers
import JuliaLean.ShowCov.PropsTerm
import JuliaLean.ShowCov.PropsStr
import JuliaLean.ShowCov.PropsShow
import JuliaLean.ShowCov.Remaining
import JuliaLean.ShowCov.RemainingProps
import JuliaLean.ShowCov.Methods

namespace JuliaLean.ShowCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := Methods.entries ++ [
  { id := "showcov-truncate-width-overflow", juliaFile := "base/show.jl"
    juliaFns := ["_truncate_at_width_or_chars(::Bool, ::AbstractString, ::Int, ::Bool, ::AbstractString, ::AbstractString)"]
    statement := "The truncation helper always returns text whose display width is at most the requested positive width."
    source := "base/show.jl:104-135; display-width invariant for limited Dict and Set output"
    status := .refuted, prop := ``TruncateFitsWidth, thm := some ``truncateFitsWidth_refuted
    issue := "none found (queries: _truncate_at_width_or_chars, truncate_at_width, truncate width wide character Dict display)"
    notes := "A final double-width character can take the result past the requested width." },
  { id := "showcov-truncate-ansi-reset", juliaFile := "base/show.jl"
    juliaFns := ["_truncate_at_width_or_chars(::Bool, ::AbstractString, ::Int, ::Bool, ::AbstractString, ::AbstractString)"]
    statement := "ANSI-aware truncation does not append a second reset after the last retained delimiter is already a reset."
    source := "base/show.jl:110,114,127"
    status := .refuted, prop := ``TruncateResetOnlyWhenNeeded,
    thm := some ``truncateResetOnlyWhenNeeded_refuted
    issue := "none found (queries: ANSIDelimiter, needANSIend, ANSI reset truncate, _truncate_at_width_or_chars)"
    notes := "ANSIDelimiter is compared with a String, so an existing reset is never recognized." },
  { id := "showcov-truncate-degenerate", juliaFile := "base/show.jl"
    juliaFns := ["_truncate_at_width_or_chars(::Bool, ::AbstractString, ::Int, ::Bool, ::AbstractString, ::AbstractString)"]
    statement := "Nonpositive and mark-too-narrow widths return an empty string, and empty input is padded exactly when requested."
    source := "base/show.jl:104-135"
    status := .proven, prop := ``TruncateDegenerate, thm := some ``truncateDegenerate_proven },
  { id := "showcov-ansi-iterator", juliaFile := "base/show.jl"
    juliaFns := ["ncodeunits(::ANSIDelimiter)", "textwidth(::ANSIDelimiter)",
      "ANSIIterator(::AbstractString)", "IteratorSize(::Type{<:ANSIIterator})",
      "eltype(::Type{<:ANSIIterator})", "iterate(::ANSIIterator)",
      "textwidth(::ANSIIterator)"]
    statement := "ANSIIterator preserves visible characters, groups ANSI delimiters, assigns them zero width, and exposes the declared iterator traits."
    source := "base/show.jl:79-102"
    status := .proven, prop := ``AnsiIteratorSpec, thm := some ``ansiIteratorSpec_proven },
  { id := "showcov-type-depth-limit-backslash", juliaFile := "base/show.jl"
    juliaFns := ["type_depth_limit(::String, ::Int)"]
    statement := "Type-depth limiting ignores braces inside every printable ASCII character literal."
    source := "base/show.jl:2726-2816"
    status := .refuted, prop := ``TypeDepthLimitCharParam,
    thm := some ``typeDepthLimitCharParam_refuted
    issue := "none found (queries: type_depth_limit, stacktrace type limit backslash, type depth limit stacktrace quote)"
    notes := "An escaped backslash leaves the scanner in its backslash state and hides the rest of the signature." },
  { id := "showcov-type-depth-limit-char", juliaFile := "base/show.jl"
    juliaFns := ["type_depth_limit(::String, ::Int)"]
    statement := "Type-depth limiting handles every printable ASCII character literal except backslash."
    source := "base/show.jl:2726-2816"
    status := .proven, prop := ``TypeDepthLimitCharParamNoBackslash,
    thm := some ``typeDepthLimitCharParamNoBackslash_proven },
  { id := "showcov-type-depth-limit-wide", juliaFile := "base/show.jl"
    juliaFns := ["type_depth_limit(::String, ::Int)", "stateis", "quoted", "enter", "leave"]
    statement := "A depth limit above the nesting of an unquoted escape-free type string preserves the string."
    source := "base/show.jl:2726-2816"
    status := .proven, prop := ``TypeDepthLimitWide, thm := some ``typeDepthLimitWide_proven },


  { id := "showcov-terminals-move-fallbacks", juliaFile := "base/Terminals.jl"
    juliaFns := ["cmove_up(::TextTerminal, n)", "cmove_down(::TextTerminal, n)",
      "cmove_left(::TextTerminal, n)", "cmove_right(::TextTerminal, n)"]
    statement := "Relative TextTerminal cursor movement delegates to cmove with the terminal and clamps down and right coordinates to the terminal bounds."
    source := "base/Terminals.jl:52-62"
    status := .refuted, prop := ``TextMoveFallbacks, thm := some ``textMoveFallbacks_refuted
    issue := "related #50109 and #59813; none found for the fallback defects"
    notes := "The fallbacks omit the terminal argument, and down and right use max where min is required." },
  { id := "showcov-terminals-interface", juliaFile := "base/Terminals.jl"
    juliaFns := ["pipe_reader(::TextTerminal)", "pipe_writer(::TextTerminal)",
      "displaysize(::TextTerminal)", "cmove(::TextTerminal, x, y)", "getX(::TextTerminal)",
      "getY(::TextTerminal)", "pos(::TextTerminal)", "cmove_up(::TextTerminal, n)",
      "cmove_up(t)", "cmove_down(::TextTerminal, n)", "cmove_down(t)",
      "cmove_left(::TextTerminal, n)", "cmove_left(t)", "cmove_right(::TextTerminal, n)",
      "cmove_right(t)", "cmove_line_up(::TextTerminal, n)", "cmove_line_up(t)",
      "cmove_line_down(::TextTerminal, n)", "cmove_line_down(t)", "cmove_col(::TextTerminal, c)",
      "hascolor(::TextTerminal)", "width(::TextTerminal)", "height(::TextTerminal)",
      "flush(::TextTerminal)", "clear(::TextTerminal)", "clear_line(::TextTerminal, row)",
      "clear_line(::TextTerminal)", "raw!(::TextTerminal, ::Bool)", "beep(::TextTerminal)",
      "enable_bracketed_paste(::TextTerminal)", "disable_bracketed_paste(::TextTerminal)"]
    statement := "The TextTerminal interface forwards stream queries, position queries, one-step wrappers, and default operations exactly as its method bodies specify."
    source := "base/Terminals.jl:43-91"
    status := .proven, prop := ``TextTerminalInterface, thm := some ``textTerminalInterface_proven },
  { id := "showcov-terminals-unix-escapes", juliaFile := "base/Terminals.jl"
    juliaFns := ["cmove_up(::UnixTerminal, n)", "cmove_down(::UnixTerminal, n)",
      "cmove_right(::UnixTerminal, n)", "cmove_left(::UnixTerminal, n)",
      "cmove_line_up(::UnixTerminal, n)", "cmove_line_down(::UnixTerminal, n)",
      "cmove_col(::UnixTerminal, n)", "enable_bracketed_paste(::UnixTerminal)",
      "disable_bracketed_paste(::UnixTerminal)", "end_keypad_transmit_mode(::UnixTerminal)",
      "clear(::UnixTerminal)", "clear_line(::UnixTerminal)", "beep(::UnixTerminal)"]
    statement := "UnixTerminal cursor and mode operations emit the exact CSI escape sequences and bell byte."
    source := "base/Terminals.jl:115-121,149-156"
    status := .proven, prop := ``UnixEscapes, thm := some ``unixEscapes_proven },
  { id := "showcov-terminals-tty", juliaFile := "base/Terminals.jl"
    juliaFns := ["pipe_reader(::UnixTerminal)", "pipe_writer(::UnixTerminal)",
      "raw!(::TTYTerminal, ::Bool)", "Base.displaysize(::UnixTerminal)", "hascolor(::TTYTerminal)",
      "Base.in(::Pair, ::TTYTerminal)", "Base.haskey(::TTYTerminal, key)",
      "Base.getindex(::TTYTerminal, key)", "Base.get(::TTYTerminal, key, default)",
      "Base.peek(::TTYTerminal, ::Type)"]
    statement := "TTY terminal wrappers forward to their streams and properties, and raw mode returns the recorded libuv result."
    source := "base/Terminals.jl:97-168"
    status := .proven, prop := ``TTYForwarding, thm := some ``ttyForwarding_proven },
  { id := "showcov-coreio", juliaFile := "base/coreio.jl"
    juliaFns := ["print", "print(x)", "print(x1, x2)", "println(x)", "println(x1, x2)",
      "print(xs...)", "println(xs...)", "println(::IO)", "show", "repr", "DevNull()",
      "write(::DevNull, ::UInt8)", "unsafe_write(::DevNull, ::Ptr{UInt8}, ::UInt)",
      "closewrite(::DevNull)", "close(::DevNull)", "wait_close(::DevNull)",
      "bytesavailable(::DevNull)", "write(::CoreIO, ::UInt8)",
      "unsafe_write(::CoreIO, ::Ptr{UInt8}, ::UInt)", "read(::CoreIO, ::Type{UInt8})",
      "isopen(::CoreIO)", "isreadable(::CoreIO)", "iswritable(::CoreIO)",
      "flush(::CoreIO)", "eof(::CoreIO)", "wait_readnb(::CoreIO, ::Int)"]
    statement := "Core output wrappers target standard output, DevNull reports its fixed behavior, and CoreIO has the documented bootstrap read and write behavior."
    source := "base/coreio.jl:3-40"
    status := .proven, prop := ``CoreIOBehaviour, thm := some ``coreIOBehaviour_proven },

  { id := "showcov-terminfo-extended-labels", juliaFile := "base/terminfo.jl"
    juliaFns := ["extendedterminfo(::IO, ::Union{Type{Int16},Type{Int32}})"]
    statement := "A flag-only extended section assigns its flag to the label stored in the names table."
    source := "base/terminfo.jl:117-154"
    status := .proven, prop := ``ExtendedLabels, thm := some ``extendedLabels_proven
    issue := "related #51110 and #51190; none found for these offsets"
    notes := "The previous nightly refutation is retained as extendedLabels_refuted for ExtendedLabelsHistorical." },
  { id := "showcov-terminfo-strings", juliaFile := "base/terminfo.jl"
    juliaFns := ["read(::IO, ::Type{TermInfoRaw})", "_terminfo_read_strings(::Vector{UInt8}, ::Vector{Int16})"]
    statement := "The terminfo reader decodes little-endian fields and resolves present string offsets to NUL-terminated byte sequences."
    source := "base/terminfo.jl:71-162"
    status := .proven, prop := ``TermInfoStrings, thm := some ``termInfoStrings_proven },
  { id := "showcov-terminfo-lookup", juliaFile := "base/terminfo.jl"
    juliaFns := ["get(::TermInfo, ::Symbol, ::Bool)", "get(::TermInfo, ::Symbol, ::Int)",
      "get(::TermInfo, ::Symbol, ::String)", "haskey(::TermInfo, ::Symbol)",
      "getindex(::TermInfo, ::Symbol)", "keys(::TermInfo)",
      "show(::IO, ::MIME\"text/plain\", ::TermInfo)"]
    statement := "TermInfo lookup selects the dictionary matching the requested default type, reports membership across dictionaries, and lists each key once."
    source := "base/terminfo.jl:214-237"
    status := .proven, prop := ``TermInfoLookup, thm := some ``termInfoLookup_proven },
  { id := "showcov-terminfo-build", juliaFile := "base/terminfo.jl"
    juliaFns := ["TermInfo()", "TermInfo(::TermInfoRaw)", "longalias(key, value)"]
    statement := "TermInfo construction combines the declared standard and extended capabilities and applies long aliases."
    source := "base/terminfo.jl:69,170-212"
    status := .proven, prop := ``TermInfoBuild, thm := some ``termInfoBuild_proven },
  { id := "showcov-terminfo-loading", juliaFile := "base/terminfo.jl"
    juliaFns := ["find_terminfo_file(::String)", "load_terminfo(::String)"]
    statement := "Terminfo search checks the environment and standard candidate paths in order, and loading returns empty state when no readable file exists."
    source := "base/terminfo.jl:248-298"
    status := .proven, prop := ``TerminfoLoading, thm := some ``terminfoLoading_proven },
  { id := "showcov-terminfo-color", juliaFile := "base/terminfo.jl"
    juliaFns := ["ttyhascolor()", "ttyhastruecolor()", "get_have_color()", "get_have_truecolor()",
      "Base.in(::Pair{Symbol,Bool}, ::TTY)", "Base.haskey(::TTY, ::Symbol)",
      "Base.getindex(::TTY, ::Symbol)", "Base.get(::TTY, ::Symbol, default)"]
    statement := "Terminal color detection follows the environment and capability rules, caches results, and exposes the TTY color property."
    source := "base/terminfo.jl:317-391"
    status := .proven, prop := ``ColorDetection, thm := some ``colorDetection_proven },

  { id := "showcov-iocontext-bindings", juliaFile := "base/show.jl"
    juliaFns := ["IOContext{IO_t}(::IO_t, ::ImmutableDict{Symbol,Any})", "ioproperties(::IO)",
      "ioproperties(::IOContext)", "unwrapcontext(::IO)", "unwrapcontext(::IOContext)",
      "IOContext(::IO, ::ImmutableDict{Symbol,Any})", "IOContext(::IOContext, ::ImmutableDict{Symbol,Any})",
      "convert(::Type{IOContext}, ::IOContext)", "convert(::Type{IOContext}, ::IO)",
      "convert(::Type{IOContext{IO_t}}, ::IOContext{IO_t})", "convert(::Type{IOContext{IO_t}}, ::IO)",
      "IOContext(::IO)", "IOContext{IO_t}(::IO)", "IOContext(::IO, ::Pair)",
      "IOContext(::IO, ::IO)", "IOContext(::IO, ::Pair, ::Pair...)", "show(::IO, ::IOContext)",
      "pipe_reader(::IOContext)", "pipe_writer(::IOContext)", "lock(::IOContext)", "unlock(::IOContext)"]
    statement := "IOContext constructors preserve the wrapped stream, add bindings in argument order, and wrappers delegate to the unwrapped stream."
    source := "base/show.jl:336-463"
    status := .proven, prop := ``IOContextBindings, thm := some ``ioContextBindings_proven },
  { id := "showcov-iocontext-lookup", juliaFile := "base/show.jl"
    juliaFns := ["Base.in(::Pair, ::IOContext)", "Base.in(::Pair, ::IO)",
      "haskey(::IOContext, key)", "haskey(::IO, key)", "getindex(::IOContext, key)",
      "getindex(::IO, key)", "get(::IOContext, key, default)", "get(::IO, key, default)",
      "keys(::IOContext)", "keys(::IO)"]
    statement := "IOContext lookup uses the newest matching binding, while a plain IO has no context keys."
    source := "base/show.jl:465-474"
    status := .proven, prop := ``IOContextLookup, thm := some ``ioContextLookup_proven },
  { id := "showcov-iocontext-displaysize", juliaFile := "base/show.jl"
    juliaFns := ["displaysize(::IOContext)"]
    statement := "IOContext displaysize uses a valid context override and otherwise delegates to the wrapped stream."
    source := "base/show.jl:476"
    status := .proven, prop := ``DisplaysizeCtx, thm := some ``displaysizeCtx_proven },
  { id := "showcov-show-circular", juliaFile := "base/show.jl"
    juliaFns := ["show_circular(::IO, x)", "show_circular(::IOContext, x)"]
    statement := "Circular display detects the nearest identical object in the context chain and prints the correct circular-reference marker."
    source := "base/show.jl:478-491"
    status := .proven, prop := ``ShowCircularSpec, thm := some ``showCircularSpec_proven },
  { id := "showcov-scalars", juliaFile := "base/show.jl"
    juliaFns := ["nonnothing_nonmissing_typeinfo(::IO)", "show(::IO, ::Bool)",
      "show(::IO, ::Nothing)", "show(::IO, ::Signed)"]
    statement := "Scalar display uses numeric Bool spelling only under Bool type information, and prints Nothing and signed integers directly."
    source := "base/show.jl:1422-1425"
    status := .proven, prop := ``ShowScalars, thm := some ``showScalars_proven },
  { id := "showcov-unsigned-hex", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::Unsigned)"]
    statement := "Hexadecimal unsigned display has the type-width padding and evaluates to the original value."
    source := "base/show.jl:1426-1436"
    status := .proven, prop := ``UnsignedHexLiteral, thm := some ``unsignedHexLiteral_proven },
  { id := "showcov-unsigned-decimal", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::Unsigned)", "print(::IO, ::Unsigned)"]
    statement := "Decimal unsigned display prints its decimal digits and includes the type suffix only when type information differs."
    source := "base/show.jl:1426-1437"
    status := .proven, prop := ``UnsignedDecimal, thm := some ``unsignedDecimal_proven },
  { id := "showcov-pair", juliaFile := "base/show.jl"
    juliaFns := ["has_tight_type(::Pair)", "isdelimited(::IO, x)", "isdelimited(::IO, ::Function)",
      "isdelimited(::IO, ::Pair)", "gettypeinfos(::IO, ::Pair)", "show(::IO, ::Pair)",
      "show_pairtyped(::IO, ::Pair)"]
    statement := "Pair display chooses typed and arrow forms from type tightness, delimiters, compactness, and type information."
    source := "base/show.jl:1439-1472"
    status := .proven, prop := ``ShowPairSpec, thm := some ``showPairSpec_proven },
  { id := "showcov-module", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::Module)", "print_fullname(::IO, ::Module)"]
    statement := "Module display prints a root name or the complete dotted parent path."
    source := "base/show.jl:1474-1493"
    status := .proven, prop := ``ShowModuleSpec, thm := some ``showModuleSpec_proven },
  { id := "showcov-wrappers", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::UndefInitializer)",
      "show(::IO, ::MIME\"text/plain\", ::AbstractRange)",
      "show(::IO, ::MIME\"text/plain\", ::UnitRange)",
      "show(::IO, ::MIME\"text/plain\", ::LinRange)",
      "show(::IO, ::MIME\"text/plain\", ::LogRange)",
      "show(::IO, ::MIME\"text/plain\", ::ComposedFunction)",
      "show(::IO, ::MIME\"text/plain\", ::Returns)", "show(::IO, ::MIME\"text/plain\", ::Splat)",
      "summary(::IO, ::AbstractSet)", "show(::IO, ::MIME\"text/plain\", ::JLOptions)",
      "show(::IO, ::MIME\"text/plain\", ::Task)", "show(::IO, ::Core.CancellationTokenSource)",
      "print(::IO, ::Symbol)", "show(::IO, x)", "show(x)", "show_default(::IO, x)",
      "show(::IO, ::MIME\"text/plain\", ::Core.TypeofBottom)", "show(::IO, ::UndefInitializer)",
      "show(::IO, ::IncludeInto)", "show(::IO, ::Core.EvalInto)"]
    statement := "The small display wrappers forward, decorate, summarize, or fall back exactly as their method bodies specify."
    source := "base/show.jl:6-39,75-77,235-239,278-322,520-525,615,3228,3539-3555"
    status := .proven, prop := ``ShowWrappers, thm := some ``showWrappers_proven },
  { id := "showcov-show-default", juliaFile := "base/show.jl"
    juliaFns := ["_show_default(::IO, x)"]
    statement := "Default display prints circular markers, assigned and unassigned fields, and raw bits in the specified order."
    source := "base/show.jl:527-568"
    status := .proven, prop := ``ShowDefaultSpec, thm := some ``showDefaultSpec_proven },
  { id := "showcov-delimited", juliaFile := "base/show.jl"
    juliaFns := ["show_delim_array(::IO, ::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one)",
      "show_delim_array(::IO, itr, op, delim, cl, delim_one)", "show(::IO, ::Tuple)",
      "show(::IO, ::SimpleVector)", "show(::IO, ::Iterators.Enumerate)", "show(::IO, ::Iterators.Zip)"]
    statement := "Delimited display preserves order, separators, singleton tuple commas, circular markers, and unassigned array slots."
    source := "base/show.jl:1562-1626,3391-3396"
    status := .proven, prop := ``DelimSpec, thm := some ``delimSpec_proven },
  { id := "showcov-summary", juliaFile := "base/show.jl"
    juliaFns := ["summary(::IO, x)", "summary(x)", "dims2string(d)", "inds2string(inds)",
      "_indsstring(i)", "_indsstring(::Union{IdentityUnitRange,Slice})", "summary(::IO, ::AbstractArray)",
      "array_summary(::IO, a, ::Tuple{Vararg{OneTo}})", "array_summary(::IO, a, inds)",
      "summary(::IO, ::GenericMemoryRef)", "summary(::IO, ::Function)", "showarg(::IO, x, toplevel)",
      "showarg(::IO, ::Type, toplevel)", "showarg(::IO, ::Array{Union{}}, toplevel)",
      "showarg(::IO, ::SubArray, toplevel)", "showindices(::IO, ::Slice, inds...)",
      "showindices(::IO, ind1, inds...)", "showindices(::IO)", "showarg(::IO, ::ReshapedArray, toplevel)",
      "showarg(::IO, ::NonReshapedReinterpretArray, toplevel)",
      "showarg(::IO, ::ReshapedReinterpretArray, toplevel)",
      "Base.showarg(::IO, ::Iterators.Pairs{<:Integer,<:Any,<:Any,<:AbstractArray}, toplevel)",
      "Base.showarg(::IO, ::Iterators.Pairs{Symbol,<:Any,Nothing,<:NamedTuple}, toplevel)",
      "Base.showarg(::IO, ::Iterators.Pairs, toplevel)"]
    statement := "Summary and showarg methods print dimensions, indices, parent arrays, element types, and iterator wrappers according to their specializations."
    source := "base/show.jl:3249-3409"
    status := .proven, prop := ``SummarySpec, thm := some ``summarySpec_proven },
  { id := "showcov-bit-chunks", juliaFile := "base/show.jl"
    juliaFns := ["print_bit_chunk(::IO, ::UInt64, ::Integer)", "print_bit_chunk(::UInt64, ::Integer)",
      "print_bit_chunk(::UInt64)", "bitshow(::IO, ::BitArray)", "bitshow(::BitArray)",
      "bitstring(::BitArray)"]
    statement := "Bit display emits each stored bit in index order and inserts only the specified spacing."
    source := "base/show.jl:3415-3440"
    status := .proven, prop := ``BitChunkSpec, thm := some ``bitChunkSpec_proven },
  { id := "showcov-dump", juliaFile := "base/show.jl"
    juliaFns := ["dump(::IOContext, ::SimpleVector, ::Int, indent)", "dump(::IOContext, x, ::Int, indent)",
      "dump(::IOContext, ::Module, ::Int, indent)", "dump(::IOContext, ::String, ::Int, indent)",
      "dump(::IOContext, ::Symbol, ::Int, indent)", "dump(::IOContext, ::Union, ::Int, indent)",
      "dump(::IOContext, ::Ptr, ::Int, indent)", "dump_elts(::IOContext, ::Array, ::Int, indent, i0, i1)",
      "dump(::IOContext, ::Array, ::Int, indent)", "dump(::IOContext, ::DataType, ::Int, indent)",
      "dump(::IO, x)", "dump(arg)"]
    statement := "dump respects maximum depth, limited array windows, one-line specializations, and datatype headers."
    source := "base/show.jl:2990-3167"
    status := .proven, prop := ``DumpSpec, thm := some ``dumpSpec_proven },
  { id := "showcov-alignment-decimal", juliaFile := "base/show.jl"
    juliaFns := ["alignment(::IO, ::Real)"]
    statement := "Real display aligns immediately before its decimal point or exponent."
    source := "base/show.jl:3194-3199"
    status := .proven, prop := ``AlignmentDecimal, thm := some ``alignmentDecimal_proven },
  { id := "showcov-alignment-inf", juliaFile := "base/show.jl"
    juliaFns := ["alignment(::IO, ::Real)"]
    statement := "A real value without a decimal point or exponent places its full width left of the alignment point."
    source := "base/show.jl:3194-3199; alignment docstring"
    status := .refuted, prop := ``AlignmentInf, thm := some ``alignmentInf_refuted
    issue := "none found (queries: alignment Inf, Inf alignment vector display, alignment Float Inf column)"
    notes := "The scan treats the final f in Inf as an exponent marker." },
  { id := "showcov-alignment-parts", juliaFile := "base/show.jl"
    juliaFns := ["nocolor(::IO)", "alignment_from_show(::IO, x)",
      "alignment_from_show(::IO, ::AbstractString)", "alignment(::IO, x)",
      "alignment(::IO, ::Number)", "alignment(::IO, ::Integer)", "alignment(::IO, ::Complex)",
      "alignment(::IO, ::Rational)", "alignment(::IO, ::Pair)"]
    statement := "Alignment wrappers split rational and complex components, preserve total pair width, and suppress color during measurement."
    source := "base/show.jl:3169-3224"
    status := .proven, prop := ``AlignmentParts, thm := some ``alignmentParts_proven },
  { id := "showcov-function-display", juliaFile := "base/show.jl"
    juliaFns := ["_isself(::DataType)", "show(::IO, ::MIME\"text/plain\", ::Function)",
      "active_module()", "show_function(::IO, ::Function, ::Bool, ::Function)",
      "show(::IO, ::Function)", "print(::IO, ::Function)",
      "show(::IO, ::Core.IntrinsicFunction)", "print(::IO, ::Core.IntrinsicFunction)"]
    statement := "Function display distinguishes intrinsic, built-in, generic, global, compact, and fallback cases, and active_module selects Main or the active REPL module."
    source := "base/show.jl:41-73,570-613"
    status := .proven, prop := ``FunctionDisplaySpec, thm := some ``functionDisplaySpec_proven },
  { id := "showcov-container-display", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::Union{KeySet,ValueIterator})",
      "show(::IO, ::MIME\"text/plain\", ::AbstractDict)",
      "show(::IO, ::MIME\"text/plain\", ::AbstractSet)"]
    statement := "Key, value, and dictionary text display handles empty, circular, limited, truncated, aligned, and ellipsis cases in source order."
    source := "base/show.jl:137-233"
    status := .proven, prop := ``ContainerDisplaySpec, thm := some ``containerDisplaySpec_proven },
  { id := "showcov-type-analysis", juliaFile := "base/show.jl"
    juliaFns := ["print_without_params(x)", "io_has_tvar_name(::IOContext, ::Symbol, x)",
      "io_has_tvar_name(::IO, ::Symbol, x)", "modulesof!(::Set{Module}, ::TypeVar)",
      "modulesof!(::Set{Module}, ::TypeEq)", "modulesof!(::Set{Module}, ::Core.TypeEgal)",
      "modulesof!(::Set{Module}, ::Type)", "has_other_free_typevars(x, free_before)",
      "unbounded_typealias(alias)", "reapply_unionall_env(::Union{IO,Nothing}, x)",
      "make_typealias(::Type, ::Union{IO,Nothing})"]
    statement := "Type-alias analysis collects referenced modules and free variables, removes binder bounds for matching, reapplies context binders, and returns one most-specific valid alias."
    source := "base/show.jl:617-767"
    status := .proven, prop := ``TypeAnalysisSpec, thm := some ``typeAnalysisSpec_proven },
  { id := "showcov-type-params", juliaFile := "base/show.jl"
    juliaFns := ["isgensym(::Symbol)", "show_can_elide(::TypeVar, ::Vector, ::Int, ::SimpleVector, ::Int)",
      "egal_var(::TypeVar, x)", "show_typeparams(::IO, ::SimpleVector, ::SimpleVector, ::Vector)"]
    statement := "Type-parameter display identifies generated names, elides only unreferenced binders, renders bounds, and resizes the where list to the retained binders."
    source := "base/show.jl:769-830"
    status := .proven, prop := ``TypeParamsSpec, thm := some ``typeParamsSpec_proven },
  { id := "showcov-type-alias-print", juliaFile := "base/show.jl"
    juliaFns := ["show_typealias_name(::IO, ::GlobalRef)",
      "show_typealias(::IO, ::GlobalRef, ::SimpleVector, ::Vector)",
      "make_wheres(::IO, ::SimpleVector, ::Type)", "show_wheres(::IO, ::Vector{TypeVar})",
      "show_typealias(::IO, ::Type)", "make_typealiases(::Type)",
      "show_unionaliases(::IO, ::Union)", "show(::IO, ::MIME\"text/plain\", ::Type)"]
    statement := "Type-alias printing qualifies invisible names, builds binder order, renders where clauses, selects union aliases, and annotates noncompact aliases."
    source := "base/show.jl:832-1069"
    status := .proven, prop := ``TypeAliasPrintSpec, thm := some ``typeAliasPrintSpec_proven },
  { id := "showcov-type-dispatch", juliaFile := "base/show.jl"
    juliaFns := ["show_typeegal(::IO, ::Core.TypeEgal)", "show(::IO, ::Core.AnyType)",
      "show_typeeq(::IO, ::TypeEq)", "_show_type(::IO, ::Type)"]
    statement := "Core type display dispatches in source order among bottom, TypeEgal, TypeEq, aliases, datatypes, unions, and UnionAll binders."
    source := "base/show.jl:1071-1152"
    status := .proven, prop := ``TypeDispatchSpec, thm := some ``typeDispatchSpec_proven },
  { id := "showcov-type-names", juliaFile := "base/show.jl"
    juliaFns := ["isvisible(::Symbol, ::Module, ::Module)",
      "is_global_function(::Core.TypeName, ::Union{Symbol,Nothing})", "check_world_bounded(::Core.TypeName)",
      "show_type_name(::IO, ::Core.TypeName)", "maybe_kws_nt(::DataType)",
      "show_datatype(::IO, ::DataType, ::Vector{TypeVar})", "show_supertypes(::IO, ::DataType)",
      "show_supertypes(::DataType)", "@show(exs...)", "show(::IO, ::Core.TypeName)"]
    statement := "Type-name and datatype display follows visibility and world bounds, recognizes keyword and tuple forms, expands @show, and prints complete supertype chains."
    source := "base/show.jl:1159-1420"
    status := .proven, prop := ``TypeNamesSpec, thm := some ``typeNamesSpec_proven },
  { id := "showcov-source-info", juliaFile := "base/show.jl"
    juliaFns := ["sourceinfo_slotnames(::CodeInfo)", "sourceinfo_slotnames(::Vector{Symbol})",
      "show(::IO, ::Core.MethodInstance)", "show(::IO, ::Core.CodeInstance)",
      "show_mi(::IO, ::Core.MethodInstance, ::Bool)"]
    statement := "Source slot names disambiguate duplicates and unused slots, while method and code instances print generator, method, thunk, ABI, and owner details."
    source := "base/show.jl:1495-1560"
    status := .proven, prop := ``SourceInfoSpec, thm := some ``sourceInfoSpec_proven },
  { id := "showcov-expr-wrappers", juliaFile := "base/show.jl"
    juliaFns := ["print(::IO, ::ExprNode)", "show(::IO, ::ExprNode)", "show_unquoted(::IO, ex)",
      "show_unquoted(::IO, ex, ::Int)", "show_unquoted(::IO, ex, ::Int, ::Int)",
      "show_unquoted(::IO, ex, ::Int, ::Int, ::Int)", "operator_precedence(::Symbol)",
      "operator_precedence(x)", "is_quoted(x)", "is_quoted(::QuoteNode)", "is_quoted(::Expr)",
      "unquoted(::QuoteNode)", "unquoted(::Expr)"]
    statement := "Expression wrappers choose lawful print or quoted contexts, precedence uses the runtime value with a zero fallback, and quote helpers recognize and unwrap their nodes."
    source := "base/show.jl:1666-1755"
    status := .proven, prop := ``ExprWrappersSpec, thm := some ``exprWrappersSpec_proven },
  { id := "showcov-ast-formatting", juliaFile := "base/show.jl"
    juliaFns := ["operator_associativity(::Symbol)", "emphasize(::IO, ::AbstractString)",
      "show_linenumber(::IO, line)", "show_linenumber(::IO, line, file)",
      "show_linenumber(::IO, line, ::Nothing)", "show_block(::IO, head, ::Vector, body, ::Int, ::Int)",
      "show_block(::IO, head, block, ::Int, ::Int)", "show_block(::IO, head, arg, block, ::Int, ::Int)",
      "show_enclosed_list(::IO, op, items, sep, cl, indent, prec, quote_level, encl_ops, ::Bool)"]
    statement := "AST formatting applies the documented associativity, emphasis, source-location, block indentation, and enclosed-list rules."
    source := "base/show.jl:1739-1832"
    status := .proven, prop := ``AstFormattingSpec, thm := some ``astFormattingSpec_proven },
  { id := "showcov-ir-nodes", juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::SSAValue, ::Int, ::Int)",
      "show_unquoted(::IO, ::Symbol, ::Int, ::Int)", "show_unquoted(::IO, ::LineNumberNode, ::Int, ::Int)",
      "show_unquoted(::IO, ::GotoNode, ::Int, ::Int)", "show_unquoted(::IO, ::GlobalRef, ::Int, ::Int)",
      "show_unquoted(::IO, ::Core.BindingPartition, ::Int, ::Int)", "show_globalref(::IO, ::GlobalRef)",
      "show_unquoted(::IO, ::SlotNumber, ::Int, ::Int)", "show_unquoted(::IO, ::QuoteNode, ::Int, ::Int)",
      "show_generator(::IO, ::Expr, indent, quote_level)", "valid_import_path(ex)",
      "show_import_path(::IO, ex, quote_level)", "allow_macroname(ex)",
      "is_core_macro(::GlobalRef, ::AbstractString)", "is_core_macro(::GlobalRef, ::Symbol)",
      "is_core_macro(arg, ::AbstractString)", "is_core_macro(arg, ::Symbol)",
      "show_unquoted_expr_fallback(::IO, ::Expr)"]
    statement := "IR and import-path helpers print identifiers, slots, references, generators, macro names, and fallback Expr constructors according to their node forms."
    source := "base/show.jl:1880-2051"
    status := .proven, prop := ``IrNodeSpec, thm := some ``irNodeSpec_proven },
  { id := "showcov-stacktrace-format", juliaFile := "base/show.jl"
    juliaFns := ["demangle_function_name(::Symbol)", "demangle_function_name(::AbstractString)",
      "show_signature_function(::IO, ft)", "print_within_stacktrace(::IO, s...)",
      "show_tuple_as_call(::IO, ::Symbol, ::Type)", "type_limited_string_from_context(::IO, ::String)"]
    statement := "Stacktrace formatting demangles names, renders callable and argument types, switches styled output, and records when type text was shortened."
    source := "base/show.jl:2608-2723"
    status := .proven, prop := ``StacktraceSpec, thm := some ``stacktraceSpec_proven },
  { id := "showcov-type-binding", juliaFile := "base/show.jl"
    juliaFns := ["print_type_bicolor(::IO, type)", "print_type_bicolor(::IO, ::String)",
      "resolvebinding(ex)", "resolvebinding(::QuoteNode)", "resolvebinding(::Symbol)",
      "resolvebinding(::Expr)", "resolvebinding(::GlobalRef)", "ismodulecall(::Expr)",
      "show(::IO, ::TypeVar)", "show_bound(::IO, b)", "show(::IO, ::Core.TypeofVararg)"]
    statement := "Type coloring splits outer and parameter text, binding resolution follows constant modules, and TypeVar and Vararg display prints the applicable bounds."
    source := "base/show.jl:2818-2912"
    status := .proven, prop := ``TypeBindingSpec, thm := some ``typeBindingSpec_proven },
  { id := "showcov-code-ir", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::CodeInfo)", "show_unquoted(::IO, ::Argument, ::Int, ::Int)",
      "show_unquoted(::IO, ::PhiNode, ::Int, ::Int)", "show_unquoted_phinode(::IO, ::PhiNode, ::Int, ::String)",
      "show_unquoted(::IO, ::PhiCNode, ::Int, ::Int)", "show_unquoted(::IO, ::PiNode, ::Int, ::Int)",
      "show_unquoted(::IO, ::UpsilonNode, ::Int, ::Int)", "show_unquoted(::IO, ::ReturnNode, ::Int, ::Int)",
      "show_unquoted(::IO, ::GotoIfNot, ::Int, ::Int)",
      "show_unquoted_gotoifnot(::IO, ::GotoIfNot, ::Int, ::String)"]
    statement := "CodeInfo and compiler IR nodes print their delimiters, assigned and undefined values, types, control-flow targets, and conditions exactly."
    source := "base/show.jl:2916-2988"
    status := .proven, prop := ``CodeIrSpec, thm := some ``codeIrSpec_proven },
  { id := "showcov-opaque-bindings", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::Core.OpaqueClosure)",
      "show(::IO, ::MIME\"text/plain\", ::Core.OpaqueClosure)",
      "print_partition(::IO, ::Core.BindingPartition)", "show(::IO, ::Core.BindingPartition)",
      "show(::IO, ::MIME\"text/plain\", ::Core.BindingPartition)",
      "show(::IO, ::MIME\"text/plain\", ::Core.Binding)"]
    statement := "Opaque closures print their call type and result, while bindings and partitions print world ranges, flags, kinds, owners, and linked partitions."
    source := "base/show.jl:3443-3536"
    status := .proven, prop := ``OpaqueBindingSpec, thm := some ``opaqueBindingSpec_proven }
]

end JuliaLean.ShowCov
