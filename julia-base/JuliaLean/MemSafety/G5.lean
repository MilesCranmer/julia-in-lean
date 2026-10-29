import JuliaLean.MemSafety.G5.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MemSafety.G5

open JuliaLean.Registry

/-- Registry entries for the proved and refuted sites in `memsafety/sites-5.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-accumulate-indexing", juliaFile := "base/accumulate.jl"
    juliaFns := ["_accumulate_pairwise!", "accumulate_pairwise!", "_accumulate1!"]
    statement := "Every unchecked input and output access computed by the pairwise recursion and LinearIndices iterator is within both arrays after their equality checks."
    source := "array-axis invariant; base/accumulate.jl:7-35,436-451"
    status := .proven, prop := ``AccumulateAccessesInBounds
    thm := some ``accumulateAccessesInBounds },
  { id := "memsafety-accumulate-offset-axis-overflow", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate!", "_accumulate!", "_accumulaten!"]
    statement := "Every unchecked access computed after the dimensional axis checks remains on the common input and output axis."
    source := "AbstractArray axis invariant; base/accumulate.jl:337-355,374-434"
    status := .refuted, prop := ``AccumulateDimsAccessesInBounds
    thm := some ``accumulateDimsAccessesInBounds_refuted
    issue := "none found (queries: accumulate offset axis overflow; accumulate typemax firstindex; accumulate custom axes bounds; PRs same)"
    notes := "For a singleton axis typemax(Int):typemax(Int), first(axis)+1 wraps to typemin(Int), so the loop at lines 391-393 reads outside the axis. Both Julia 1.13.2 and master reproduce under forced bounds checks." },
  { id := "memsafety-accumulate-dimensional-initial", juliaFile := "base/accumulate.jl"
    juliaFns := ["_accumulate!", "_accumulaten!"]
    statement := "After the matching-axis and nonempty checks, each dimensional scan's initial unchecked read and write use the first index of the common axis."
    source := "array-axis invariant; base/accumulate.jl:374-390,404-425"
    status := .proven, prop := ``AccumulateDimsInitialAccessesInBounds
    thm := some ``accumulateDimsInitialAccessesInBounds },
  { id := "memsafety-options-commands", juliaFile := "base/options.jl"
    juliaFns := ["JLOptions", "unsafe_load_commands", "show(::IO, ::JLOptions)", "exec_options"]
    statement := "JLOptions loads one runtime object, and every command-table and first-byte load follows the runtime table's terminating null pointer."
    source := "runtime JLOptions layout invariant; base/options.jl:79-85,105-133; base/client.jl:268; base/show.jl:287"
    status := .proven, prop := ``OptionsCommandsAccessesInBounds
    thm := some ``optionsCommandsAccessesInBounds },
  { id := "memsafety-rawbigfloats-get-elem", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["get_elem(::BigFloatData, ::Int, ::Val{:words}, ::Val{:ascending})", "get_elem(::BigFloatData, ::Int, ::Val{:descending})", "truncated", "BigFloatDataRoundingIncrementHelper", "tail_is_nonzero"]
    statement := "Every unchecked BigFloatData word load computed by truncation, descending indexing, final and round bits, and sticky-bit scanning is within the limb vector."
    source := "base/rawbigfloats.jl:5-142; public BigFloat-to-Float callers at base/mpfr.jl:494-552"
    status := .proven, prop := ``RawBigFloatAccessesInBounds
    thm := some ``rawBigFloatAccessesInBounds },
  { id := "memsafety-show-bits", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, x)"]
    statement := "The raw-bits display branch reads exactly the descending byte offsets below cld(bitsizeof(typeof(x)), 8)."
    source := "bits object storage invariant; base/show.jl:530-565"
    status := .proven, prop := ``ShowBitsAccessesInBounds
    thm := some ``showBitsAccessesInBounds },
  { id := "memsafety-stream-redirect-global", juliaFile := "base/stream.jl"
    juliaFns := ["_redirect_io_cglobal", "RedirectStdStream"]
    statement := "The redirect helper's nested descriptor branch either performs no store or stores at the implicit first element of one scalar runtime global."
    source := "runtime scalar-global invariant; base/stream.jl:1928-1978"
    status := .proven, prop := ``StreamRedirectAccessesInBounds
    thm := some ``streamRedirectAccessesInBounds },
  { id := "memsafety-thread-runtime-globals", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["maxthreadid", "_nthreads_in_pool", "nthreadpools", "ngcthreads", "threadpoolsize", "threadpooltids", "multiq_size", "@spawn"]
    statement := "Scalar thread globals use their only cell, and every public caller maps to one of the two entries in jl_n_threads_per_pool."
    source := "runtime thread-pool layout invariant; base/threadingconstructs.jl:38-169,828; base/partr.jl:111,132"
    status := .proven, prop := ``ThreadRuntimeAccessesInBounds
    thm := some ``threadRuntimeAccessesInBounds },
  { id := "memsafety-toml-take-chunks", juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse_string_continue", "take_chunks", "TOML.parse", "TOML.tryparse"]
    statement := "Every take_chunks source span recorded by the parser cursor lies in l.str, and every destination span lies in the string allocated from the sum of chunk lengths."
    source := "Parser cursor and chunk representation invariant; base/toml/parser.jl:75-149,1360-1462"
    status := .proven, prop := ``TomlTakeChunksAccessesInBounds
    thm := some ``tomlTakeChunksAccessesInBounds },
  { id := "memsafety-version-matches", juliaFile := "base/version.jl"
    juliaFns := ["matches_spec_range!"]
    statement := "The exact lower-search and upper-marking loops read versions and write dest only after their i <= n check and the two length assertions."
    source := "base/version.jl:530-560"
    status := .proven, prop := ``VersionMatchesAccessesInBounds
    thm := some ``versionMatchesAccessesInBounds },
  { id := "memsafety-version-intersect", juliaFile := "base/version.jl"
    juliaFns := ["intersect(::VersionSpec, ::VersionSpec)"]
    statement := "The nested range product loop writes one one-based slot for each pair into the allocation with that product length."
    source := "base/version.jl:570-579"
    status := .proven, prop := ``VersionIntersectAccessesInBounds
    thm := some ``versionIntersectAccessesInBounds },
  { id := "memsafety-threads-comprehension-firstindex-overflow"
    juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["Threads.@threads comprehension", "_comprehension_result", "_comprehension_widened_eltype"]
    statement := "The threaded-comprehension widening scan reads only an index of its result array."
    source := "AbstractArray index invariant; base/threadingconstructs.jl:356-370,391-421"
    status := .refuted, prop := ``ComprehensionWidenAccessesInBounds
    thm := some ``comprehensionWidenAccessesInBounds_refuted
    issue := "none found (queries: threaded comprehension firstindex overflow; _comprehension_widened_eltype; typemax firstindex @threads; PRs same)"
    notes := "On master, a one-element result whose sole index is typemax(Int) wraps firstindex(result)+1 to typemin(Int), then line 370 reads that index under @inbounds. Julia 1.13.2 does not support threaded comprehensions." }
]

end JuliaLean.MemSafety.G5
