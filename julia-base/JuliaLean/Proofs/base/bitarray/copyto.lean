import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.count
import JuliaLean.Proofs.base.bitarray.copyto_append



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesCopyto1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-append-prepend", juliaFile := "base/bitarray.jl", juliaFns := ["append!(::BitVector, ::BitVector)", "prepend!(::BitVector, ::BitVector)", "copy_chunks!", "copy_chunks_rtol!"],
    statement := "append!(B, C) and prepend!(B, C) compute [B; C] and [C; B] and keep the chunk invariant, also when C === B.", source := "append!/prepend! docstrings (base/array.jl); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``AppendPrependAgrees, thm := none, notes := "No complete exact proof returned. the remaining exact target is blocked by the old model treating readable primitive allocation as unassigned references." }
]
def entriesCopyto2 : List JuliaLean.Registry.Entry := [
  { id := "memsafety-bitarray-copy-chunks", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!", "fill_chunks!", "copy_to_bitarray_chunks!", "copyto!"],
    statement := "Every bit position reached after copyto!'s public range checks maps to an in-bounds source and destination chunk.", source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; copyto! checks at base/bitarray.jl:454-469",
    status := .todo, prop := ``BitArrayCopyChunksInBounds, thm := none }
]
def entriesCopyto3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-abstract-array-copy-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "copyto!@429", "copyto!@454", "copyto!@466"],
    statement := "Copying Boolean elements from an abstract array stores them in order and leaves the unused destination suffix unchanged.", source := "obvious invariant; base/bitarray.jl:429",
    status := .todo, prop := ``AbstractArrayCopyAgrees, thm := none },
  { id := "bitarray-array-conversions-keep-bits", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!@135", "copy_chunks_rtol!@189", "copy_to_bitarray_chunks!@261", "fill!@368", "_insert_int!@885", "unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "gen_bitarray@573", "gen_bitarray@594", "gen_bitarrayN@596", "gen_bitarrayN@597", "copyto!@429", "copyto!@454", "copyto!@466", "::Type{T}@535", "BitArray@536", "BitArray@566", "convert@569", "$f@1194", "/@1197", "/@1198"],
    statement := "Converting between BitArray and Boolean arrays preserves every logical element.", source := "obvious invariant; base/bitarray.jl:135",
    status := .todo, prop := ``ArrayConversionsKeepBits, thm := none }
]
def entriesCopyto4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-concatenation", juliaFile := "base/bitarray.jl", juliaFns := ["hcat@1847", "vcat@1860", "hcat@1874", "_cat@1924"],
    statement := "Variadic BitVector vcat flattens inputs in order; hcat preserves dimensions and column-major order for equal-length inputs. Both results preserve packed padding.", source := "base/bitarray.jl:1847-1875; unused bits are zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``Round5.BitArrayConcatenation, thm := none, notes := "No complete exact proof returned. Julia's primitive words are readable, so this is an old allocator-model blocker rather than a Julia refutation." }
]
def entriesCopyto5 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-copyto-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!@135", "copy_chunks_rtol!@189", "copy_to_bitarray_chunks!@261", "unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "copyto!@429", "copyto!@454", "copyto!@466", "::Type{T}@535"],
    statement := "copyto! copies the source bits and preserves any untouched destination suffix.", source := "obvious invariant; base/bitarray.jl:135",
    status := .todo, prop := ``BitArrayCopytoAgrees, thm := none }
]
def entriesCopyto6 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-matrix-hcat-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["hcat@1847", "vcat@1860", "hcat@1874", "_cat@1924"],
    statement := "Horizontal concatenation of BitMatrices joins columns and preserves their row order.", source := "obvious invariant; base/bitarray.jl:1847",
    status := .todo, prop := ``MatrixHcatAgrees, thm := none, notes := "No complete exact proof returned. the statement also permits impossible shapes such as rows=2 and left=right=[true], and the multiword copy model still needs correction." },
  { id := "bitarray-matrix-vcat-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["vcat@1898"],
    statement := "Variadic BitMatrix vcat joins each input's rows independently in every column, preserves column-major order and dimensions, and keeps packed padding zero.", source := "base/bitarray.jl:1898-1922; unused bits are zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``Round5.MatrixVcatAgrees, thm := none, notes := "No complete exact proof returned. existing matrixVcat_model_error proves undefinedReference for one 65-by-1 input, so completion needs the old primitive-allocation model corrected." }
]
def entriesCopyto7 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bool-copy-frame",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)"],
    statement := "Every instrumented signed-input execution preserves validity metadata, its prior access log, and every byte outside actual destination stores; only the source AssertionError is reported. Unchecked access failures remain explicit obligations.",
    source := "base/bitarray.jl:274-337,454-470; base/pointer.jl:92-104,131-151; doc/src/devdocs/ub.md:39-64",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BoolCopyAllInputsFrame,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-bool-copy-transfer",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)"],
    statement := "For every safe native positive-count call, the destination interval equals the original Bool sequence, other bits and bytes remain unchanged, access obligations hold, and the exact UInt64-or-nothing return follows independent interval geometry.",
    source := "base/bitarray.jl:274-337,454-470; base/pointer.jl:92-104,131-151; doc/src/devdocs/ub.md:39-64",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BoolCopySafeBitTransfer,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-bool-copy-return",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)"],
    statement := "For all signed positions/counts and shared byte heaps, any returned UInt64 equals the actual last stored destination word, observed independently as a base-256 byte sum.",
    source := "base/bitarray.jl:274-337,454-470; base/pointer.jl:92-104,131-151; doc/src/devdocs/ub.md:39-64",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BoolCopyReturnedWordStored,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-bool-copy-zero",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)"],
    statement := "At every positive word-aligned destination, zero bits returns nothing without reading any header, source element, or destination element and leaves all state unchanged, regardless of source rank or offset.",
    source := "base/bitarray.jl:274-337,454-470; base/pointer.jl:92-104,131-151; doc/src/devdocs/ub.md:39-64",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.BoolCopyZeroAlignedNoAccess,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.BoolCopyZeroAlignedNoAccess_proven },
  { id := "bitarray-dump-cache-frame",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool})"],
    statement := "For every signed bind and raw heap, only bytes named by actual chunk stores may change; validity and prior access events are preserved, and only the delegated source assertion may report an error.",
    source := "base/bitarray.jl:342-348,274-337; base/essentials.jl:1296; base/promotion.jl:677",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DumpBoolCacheAllInputsFrame,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-dump-cache-transfer",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool})"],
    statement := "Whenever the interval selected by native wrapping is a safe positive copy, exactly the cache prefix is copied into it, other bits and bytes are preserved, and the wrapper returns nothing. Capacity is counted in bits.",
    source := "base/bitarray.jl:342-348,274-337; base/essentials.jl:1296; base/promotion.jl:677",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DumpBoolCacheSafeBitTransfer,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-dump-cache-return",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool})"],
    statement := "Every successful cache dump returns nothing for all native bind values, including wrapping and negative capacities; the source-mirrored model retains the delegated UInt64-or-nothing type and assertion paths.",
    source := "base/bitarray.jl:342-348,274-337; base/essentials.jl:1296; base/promotion.jl:677",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DumpBoolCacheSuccessfulReturn,
    thm := none,
    notes := "Independent statement; intentionally unproved." },
  { id := "bitarray-dump-cache-zero",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool})"],
    statement := "A selected zero count with a positive wrapped destination position returns nothing with the entire state unchanged and without source or destination accesses.",
    source := "base/bitarray.jl:342-348,274-337; base/essentials.jl:1296; base/promotion.jl:677",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models2Group11.DumpBoolCacheZeroNoAccess,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models2Group11.DumpBoolCacheZeroNoAccess_proven }
]
def entriesCopyto8 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-copyto-frame", juliaFile := "base/bitarray.jl",
    juliaFns := ["copyto!(dest::BitArray, src::BitArray)"],
    statement := "For every heap and pair of BitArrays, a too-long source raises BoundsError before heap access, successful return preserves the destination header, and every run preserves heap metadata and cells outside the valid physical destination chunk window, including failures and overlapping aliases.",
    source := "base/bitarray.jl:429-447; base/abstractarray.jl:1043-1051 (error-order and mutation-frame invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.CopytoBoundsAndGlobalFrame, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15CopytoFrame_proven,
    notes := "No exact chunk-count, padding, source-validity or nonaliasing premise is imposed on this global contract. The physical frame only needs the destination vector's actual valid-window invariant." },
  { id := "bitarray-copyto-same-chunks", juliaFile := "base/bitarray.jl",
    juliaFns := ["copyto!(dest::BitArray, src::BitArray)"],
    statement := "When source and destination use the same valid chunk vector, copyto! leaves the entire heap unchanged even if logical lengths or ranks differ; readable storage ensures successful return when the source-length check passes.",
    source := "base/bitarray.jl:429-447 (same-chunk alias invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.CopytoSameChunksUnchanged, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15CopytoSameChunks_proven,
    notes := "Allows alias-resized logical/physical length mismatches and unassigned cells; the latter may stop reading but cannot induce a mutation. Does not generalize to distinct overlapping array headers." },
  { id := "bitarray-copyto-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["copyto!(dest::BitArray, src::BitArray)"],
    statement := "For self-consistent machine-sized packed arrays with disjoint physical windows, copyto! copies the complete source into the destination prefix, preserves remaining destination values, source storage and padding, and returns the destination; a too-long source errors before mutation.",
    source := "base/bitarray.jl:429-447; base/abstractarray.jl:1043-1051; base/Base_compiler.jl:222-225 (documented alias warning)", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.CopytoNonoverlappingValues, thm := none,
    notes := "No complete exact proof returned. Disjoint-window snapshots, prefix values and padding remain open." },
  { id := "bitarray-copy-offset-preflight", juliaFile := "base/bitarray.jl",
    juliaFns := ["copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer) (native Int packed-source specialization)"],
    statement := "Native-offset packed copying returns immediately for zero count, rejects negative count before offsets, and rejects nonpositive offsets before heap access; each such outcome preserves the heap. Later successes or failures preserve the physical destination frame.",
    source := "base/bitarray.jl:454-464; base/array.jl:282-287 (ordered error and zero-count invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.PackedOffsetsEarlyErrors, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15CopyOffsetPreflight_proven,
    notes := "Useful partial result only; covers all heaps and native offset values, including invalid chunk handles. Generic Integer conversions and Array sources remain blocked." },
  { id := "bitarray-copy-offset-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["unsafe_copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer) (native Int packed-source specialization)", "_copyto_int! (packed-source specialization)", "copyto! with native offsets and packed source"],
    statement := "Native-offset packed copies use the requested mathematical intervals, copy snapshot values into the destination slice and preserve all other destination bits and padding, for disjoint windows and same-chunk overlap. Invalid checked intervals error without mutation; unsafe copying is specified on the valid-interval domain.",
    source := "base/bitarray.jl:135-141,189-233,449-464; base/array.jl:265-287", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.PackedOffsetsValues, thm := none,
    notes := "Useful partial result only. Lengths are machine-sized and chunk windows are concrete; same-vector overlap is included, distinct overlapping headers are not assigned undocumented snapshot semantics. Generic Integer conversions and Array sources remain blocked." }
]
def entriesCopyto9 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-append-prepend-frame", juliaFile := "base/bitarray.jl",
    juliaFns := ["append!(B::BitVector, items::BitVector)", "prepend!(B::BitVector, items::BitVector)"],
    statement := "Empty items return the identical target before any chunk access, and checked native length overflow raises OverflowError before mutation. Every execution preserves other object headers, other chunk-array headers, old memory sizes and unrelated backing memories; target metadata can only change its length, including when a later copy fails.",
    source := "base/bitarray.jl:757-772,777-793; base/array.jl:1384-1420,1449-1478", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.AppendPrependEarlyErrorsAndFrame, thm := none,
    notes := "All typed header aliases, arbitrary chunk states, overlapping windows and partial-write errors are included. No successful-callee or nonaliasing premise is supplied." },
  { id := "bitarray-append-prepend-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["append!(B::BitVector, items::BitVector)", "prepend!(B::BitVector, items::BitVector)"],
    statement := "For full-size native readable packed extents, append and prepend return the exact corresponding concatenation and the original target identity, including self-concatenation and different object headers sharing one chunk vector. Checked length overflow and too-large native growth allocation are classified explicitly and leave the state unchanged.",
    source := "base/bitarray.jl:757-772,777-793; base/array.jl:1102-1112,1171-1223,1384-1420,1449-1478; src/genericmemory.c:55-73; base/Base_compiler.jl:222-225", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.AppendPrependConcatenationAndNativeLimits, thm := none,
    notes := "All native capacities and offsets are quantified with the exact raw-memory byte bound. Source snapshots are promised for identical chunk handles or separate backing memory objects; different shared-memory windows retain the unrestricted frame, since growth can change their overlap. No convenience bound such as 2^31 is imposed." },
  { id := "bitarray-append-prepend-error-length", juliaFile := "base/bitarray.jl",
    juliaFns := ["append!(B::BitVector, items::BitVector)", "prepend!(B::BitVector, items::BitVector)"],
    statement := "When alias shrinkage leaves the source underbacked and the destination already has enough capacity, copying raises BoundsError after the summed target length has been committed. The real mutable target header retains that length, and preceding shifts/writes are not rolled back.",
    source := "base/bitarray.jl:768-770,789-792; base/Base_compiler.jl:222-225", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.AppendPrependUnderbackedSourceKeepsLength, thm := none,
    notes := "No complete exact proof returned. Append/prepend length tracing and forced BoundsError remain open." }
]
def entriesCopyto10 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-pack8bools-bit-incidence",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["pack8bools(z::UInt64)"],
    statement := "For every UInt64 word, the result is a byte whose bit j is the disjunction of original input bits j+7k for k from zero through seven.",
    source := "base/bitarray.jl:266-272",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.Pack8BoolsBitIncidence,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15Pack8boolsBitIncidence_proven,
    notes := "Independent mathematical bit observations cover every UInt64 input, including noncanonical Boolean-byte encodings." }
]
end JuliaLean.Proofs.base.bitarray

