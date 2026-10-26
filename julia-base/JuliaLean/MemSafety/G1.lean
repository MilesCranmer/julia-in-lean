import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.MemSafety.G1.Faithful

namespace JuliaLean.MemSafety.G1

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-1.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-base-compiler-bootstrap", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["include(::Module, ::String)", "strcat(::String, ::String)"]
    statement := "Bootstrap include either grows its valid offset-one vector through _growend! or advances its size before writing len+1; strcat partitions the exact x+y allocation."
    source := "base/Base_compiler.jl:13-25,194-205; base/array.jl:1171-1227"
    status := .proven, prop := ``BootstrapInBounds, thm := some ``bootstrapInBounds_proven },
  { id := "memsafety-array-checked-scalar", juliaFile := "base/array.jl"
    juliaFns := ["unsetindex!", "isassigned(::Vector)", "_setindex!(::Array, ::Any, ::Int)"]
    statement := "Each scalar Array access is executed only on the successful checkbounds branch, and its computed zero-based storage ordinal is below length(A)."
    source := "base/array.jl:208-243,1031-1041"
    status := .proven, prop := ``CheckedScalarInBounds, thm := some ``checkedScalarInBounds_proven },
  { id := "memsafety-array-checked-cartesian", juliaFile := "base/array.jl"
    juliaFns := ["isassigned(::Array, ::Int...)", "getindex(::Array, ::Int, ::Int, ::Int...)", "_setindex!(::Array, ::Any, ::Int, ::Int, ::Int...)"]
    statement := "After checkbounds normalizes missing and extra singleton dimensions, _sub2ind computes a one-based linear index inside the product storage length."
    source := "base/array.jl:231-236,974-977,1042-1051; base/abstractarray.jl:682-728,3165-3208"
    status := .proven, prop := ``CheckedCartesianInBounds,
    thm := some ``checkedCartesianInBounds_proven },
  { id := "memsafety-array-checked-copies", juliaFile := "base/array.jl"
    juliaFns := ["_copyto_impl!", "copy(::Array)", "getindex(::Array, ::Colon)", "setindex!(::Array, ::Array, ::AbstractUnitRange)", "setindex!(::Array, ::Array, ::Colon)"]
    statement := "Checked copy paths derive both spans from their bounds checks; exact-copy paths allocate or require exactly the copied element count."
    source := "base/array.jl:299-315,391-399,995-1001,1078-1095"
    status := .proven, prop := ``ArrayCheckedCopiesInBounds,
    thm := some ``arrayCheckedCopiesInBounds_proven },
  { id := "memsafety-array-vcat", juliaFile := "base/array.jl"
    juliaFns := ["vcat(::Vector...)"]
    statement := "The first loop computes the representable total allocation and the second advances the destination by each source length, so every copied prefix ends at the total."
    source := "base/array.jl:2351-2364"
    status := .proven, prop := ``VcatInBounds, thm := some ``vcatInBounds_proven },
  { id := "memsafety-array-literal", juliaFile := "base/array.jl"
    juliaFns := ["getindex(::Type, vals...)"]
    statement := "The non-tuple array-literal fold starts at index one, writes once for each vararg value, and allocates length(vals) slots."
    source := "base/array.jl:445-460"
    status := .proven, prop := ``LiteralInBounds, thm := some ``literalInBounds_proven },
  { id := "memsafety-array-allocated-callers", juliaFile := "base/array.jl"
    juliaFns := ["setindex_widen_up_to", "collect_to!", "__safe_setindex!", "setindex!(::Array, ::AbstractArray, ::AbstractVector{Int})"]
    statement := "Sized collection uses the iterator length contract, every __safe_setindex! caller derives its index from the exact newly grown range, and vector-indexed assignment checks shape and every destination index first."
    source := "base/array.jl:124-162,445-466,875-911,1055-1074,1358-1386,1776-1801; IteratorSize HasLength and HasShape contracts"
    status := .proven, prop := ``ArrayAllocatedCallersInBounds,
    thm := some ``arrayAllocatedCallersInBounds_proven },
  { id := "memsafety-array-insert", juliaFile := "base/array.jl"
    juliaFns := ["_insert!"]
    statement := "Insertion writes the slot created by _growat! after that function checks the insertion index against old length plus one."
    source := "base/array.jl:1871-1877"
    status := .proven, prop := ``InsertInBounds, thm := some ``insertInBounds_proven },
  { id := "memsafety-array-delete-indices", juliaFile := "base/array.jl"
    juliaFns := ["_deleteat!(::Vector, inds)", "deleteat!(::Vector, ::AbstractVector{Bool})"]
    statement := "Every deleted, copied source, and compacted destination index is computed from the checked monotone p/q cursors inside the original vector length."
    source := "base/array.jl:1952-2014"
    status := .proven, prop := ``DeleteIndicesInBounds,
    thm := some ``deleteIndicesInBounds_proven },
  { id := "memsafety-array-filter-loops", juliaFile := "base/array.jl"
    juliaFns := ["filter(::Function, ::Array)", "filter(::Function, ::AbstractArray)", "filter!(::Function, ::AbstractVector)"]
    statement := "Filter loops allocate one slot per input index and advance the compacted destination only after keeping an element."
    source := "base/array.jl:3020-3079"
    status := .proven, prop := ``FilterLoopsInBounds, thm := some ``filterLoopsInBounds_proven },
  { id := "memsafety-array-iterator-access", juliaFile := "base/array.jl"
    juliaFns := ["reverse!", "_findin", "_sortedfindin"]
    statement := "reverse! derives both swap indices from checked endpoints, while the find loops advance only iterators created from the arrays they access."
    source := "base/array.jl:2317-2333,2903-2955"
    status := .proven, prop := ``ArrayIteratorLoopsInBounds,
    thm := some ``arrayIteratorLoopsInBounds_proven },
  { id := "memsafety-array-wrap-memory", juliaFile := "base/array.jl"
    juliaFns := ["wrap(::Type{Array}, ::Memory, dims)", "wrap(::Type{Array}, ::Memory, length)", "wrap(::Type{Array}, ::Memory)"]
    statement := "The Memory overloads start at the first cell and expose only the checked dimension product after _wrap compares it with length(memory)."
    source := "base/array.jl:3240-3278"
    status := .proven, prop := ``WrapMemoryInBounds, thm := some ``wrapMemoryInBounds_proven },
  { id := "memsafety-array-simple-vector-moves", juliaFile := "base/array.jl"
    juliaFns := ["_growbeg!", "_growat!", "_deletebeg!", "_deleteend!", "_deleteat!", "sizehint!"]
    statement := "Valid Vector storage bounds every in-place front or tail shift, edge deletion, checked tail deletion, and sizehint copy at the indices computed by its source branch."
    source := "base/array.jl:1151-1168,1230-1326,1617-1647; Vector representation checks at lines 1120-1125 and 1173-1179"
    status := .proven, prop := ``SimpleVectorMovesInBounds,
    thm := some ``simpleVectorMovesInBounds_proven },
  { id := "memsafety-array-allocating-growth", juliaFile := "base/array.jl"
    juliaFns := ["_growbeg_internal!", "_growend_internal!", "_growat!"]
    statement := "The allocating growth branches compute overallocation, checked minimum capacity, centered offsets, copy spans, and new references from a valid Vector state; the end-growth queue branch also bounds its in-memory move and cleanup loop."
    source := "base/array.jl:1102-1148,1171-1208,1263-1274; Vector representation checks at lines 1120-1125 and 1173-1179"
    status := .proven, prop := ``AllocatingGrowthInBounds,
    thm := some ``allocatingGrowthInBounds_proven },
  { id := "memsafety-abstractarraymath-repeat-vector-matrix", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat_outer(::AbstractVector)", "repeat_outer(::AbstractMatrix)"]
    statement := "Each vector or matrix repeat tile is computed from the source dimensions and loop ordinals and lies inside the checked product allocation."
    source := "base/abstractarraymath.jl:559-581"
    status := .proven, prop := ``RepeatVectorMatrixInBounds,
    thm := some ``repeatVectorMatrixInBounds_proven },
  { id := "memsafety-abstractarraymath-broadcast-repeat", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!"]
    statement := "conj! broadcasts over identical source and destination axes, so broadcast's checked common iterator supplies every source and destination ordinal."
    source := "base/abstractarraymath.jl:194; broadcast axis contract"
    status := .proven, prop := ``BroadcastConjInBounds,
    thm := some ``broadcastConjInBounds_proven },
  { id := "memsafety-abstractarraymath-generic-repeat", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat_outer(::AbstractArray)", "repeat_inner"]
    statement := "The generic repeat trace executes both Cartesian loops, the componentwise TIJ formula, and the column-major source and output index computations."
    source := "base/abstractarraymath.jl:583-611"
    status := .proven, prop := ``GenericRepeatInBounds,
    thm := some ``genericRepeatInBounds_proven },
  { id := "memsafety-combinatorics-swap-invperm", juliaFile := "base/combinatorics.jl"
    juliaFns := ["swapcols!", "swaprows!", "invperm"]
    statement := "Swaps check both scalar indices before traversing the other matrix axis, and invperm range-checks every value before indexing its length-sized result."
    source := "base/combinatorics.jl:103-123,286-296"
    status := .proven, prop := ``CombinatoricsAccessesInBounds,
    thm := some ``combinatoricsAccessesInBounds_proven },
  { id := "memsafety-set-pop", juliaFile := "base/set.jl"
    juliaFns := ["pop!(::Set, key)"]
    statement := "The Dict slot returned by lookup is computed by searching the slot vector and is accessed only when a live slot was found."
    source := "base/set.jl:139-157; Dict table representation invariant"
    status := .proven, prop := ``SetPopInBounds, thm := some ``setPopInBounds_proven },
  { id := "memsafety-set-unique", juliaFile := "base/set.jl"
    juliaFns := ["unique!", "_unique!", "_indexed_allunique"]
    statement := "The unique compaction destination never passes the current input position, and _indexed_allunique compares only later indices from the same eachindex iterator."
    source := "base/set.jl:373-405,579-592"
    status := .proven, prop := ``SetUniqueInBounds, thm := some ``setUniqueInBounds_proven },
  { id := "memsafety-set-replace", juliaFile := "base/set.jl"
    juliaFns := ["replace", "replace!", "_replace!(::Callable, ::AbstractArray, ::AbstractArray)", "_replace!(::Callable, ::Dict, ::AbstractDict)"]
    statement := "Array replacement uses the equal axes supplied by its public wrappers, and Dict replacement obtains every slot from skip_deleted's live-slot search."
    source := "base/set.jl:804-896,947-1009"
    status := .proven, prop := ``SetReplaceInBounds, thm := some ``setReplaceInBounds_proven },
  { id := "memsafety-libdl-global", juliaFile := "base/libdl.jl"
    juliaFns := ["Libdl.__init__"]
    statement := "cglobal(:jl_libdl_dlopen_func, Any) computes offset zero in the runtime's one-Any global object."
    source := "base/libdl.jl:515-517; runtime global declaration"
    status := .proven, prop := ``RuntimeCellInBounds, thm := some ``runtimeCellInBounds_proven },
  { id := "memsafety-libc-os-buffers", juliaFile := "base/libc.jl"
    juliaFns := ["Libc.FormatMessage", "Libc.getgrgid"]
    statement := "FormatMessageW's returned count sizes both copy spans, and getgrgid walks the null-terminated member-pointer array returned by libuv."
    source := "base/libc.jl:395-410,581-603; Win32 FormatMessageW and libuv uv_os_get_group contracts"
    status := .proven, prop := ``LibcBuffersInBounds, thm := some ``libcBuffersInBounds_proven },
  { id := "memsafety-iobuffer-string-memory", juliaFile := "base/iobuffer.jl"
    juliaFns := ["StringMemory"]
    statement := "On successful Csize_t conversion, _string_n allocates exactly n bytes and unsafe_wrap exposes those same n bytes as Memory."
    source := "base/iobuffer.jl:166-168; base/strings/string.jl:184-185"
    status := .proven, prop := ``StringMemoryInBounds, thm := some ``stringMemoryInBounds_proven },
  { id := "memsafety-iobuffer-operations", juliaFile := "base/iobuffer.jl"
    juliaFns := ["peek", "read", "take!", "unsafe_takestring!", "takestring!"]
    statement := "The documented IOBuffer field invariant bounds the computed read pointer, take view, translated marked span, and both exact-size string copies."
    source := "base/iobuffer.jl:55-93,406-448,661-673,758-859; JuliaLean.IOBuffers.reachable_inv"
    status := .proven, prop := ``IOBufferOperationsInBounds,
    thm := some ``ioBufferOperationsInBounds_proven },
  { id := "memsafety-strings-io-wrap", juliaFile := "base/strings/io.jl"
    juliaFns := ["IOBuffer(::String)", "IOBuffer(::SubString{String})"]
    statement := "String IOBuffer wraps all parent bytes, while the SubString method uses its stored offset and byte count inside the parent."
    source := "base/strings/io.jl:288-307; SubString representation invariant at base/strings/substring.jl:142-143"
    status := .proven, prop := ``StringIOInBounds, thm := some ``stringIOInBounds_proven },
  { id := "memsafety-strings-substring-index", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString", "codeunit(::SubString)", "getindex(::SubString)", "isvalid(::SubString)"]
    statement := "Constructors check the parent endpoints, and every SubString operation checks its local index before adding the stored in-parent offset."
    source := "base/strings/substring.jl:71-171; base/strings/string.jl:252-271"
    status := .proven, prop := ``SubstringIndexInBounds,
    thm := some ``substringIndexInBounds_proven },
  { id := "memsafety-strings-repeat", juliaFile := "base/strings/substring.jl"
    juliaFns := ["repeat(::Union{String,SubString{String}}, ::Integer)"]
    statement := "After the multiplication overflow check, repeat fills or copies exactly r consecutive source-width blocks in its n*r byte allocation."
    source := "base/strings/substring.jl:289-306"
    status := .proven, prop := ``RepeatStringInBounds, thm := some ``repeatStringInBounds_proven },
  { id := "memsafety-strings-build", juliaFile := "base/strings/substring.jl"
    juliaFns := ["_string", "__unsafe_string!"]
    statement := "The sizing and writing loops use the same per-value byte width; every unsafe store or copy begins at the prefix sum and ends inside the successful total-size allocation."
    source := "base/strings/substring.jl:215-283; successful jl_alloc_string length is Int-representable"
    status := .proven, prop := ``StringBuildInBounds, thm := some ``stringBuildInBounds_proven },
  { id := "memsafety-deprecated-substring-negative-count", juliaFile := "base/deprecated.jl"
    juliaFns := ["SubString{T}(s, i, j, Val(:noshift))"]
    statement := "Every successful deprecated no-shift constructor call returns a SubString with a nonnegative code-unit count and a span inside its parent."
    source := "base/deprecated.jl:704-724; SubString representation invariant"
    status := .refuted, prop := ``DeprecatedSubstringValid,
    thm := some ``deprecatedSubstringValid_refuted
    issue := "none found (queries: SubString negative ncodeunits, Val noshift negative SubString, raw_substring negative)"
    notes := "With s=\"abc\", i=2, and j=-1, both validated endpoints are valid before the unchecked raw_substring call stores ncodeunits=-1." },
  { id := "memsafety-reducedim-accesses", juliaFile := "base/reducedim.jl"
    juliaFns := ["_mapreducedim!", "findminmax!"]
    statement := "For every rank, check_reducedims selects singleton or unchanged result axes; the slow Cartesian path maps each coordinate accordingly, while the fast path partitions linear input storage by its computed leading block."
    source := "base/reducedim.jl:205-293,1032-1080"
    status := .proven, prop := ``ReductionNDAccessesInBounds,
    thm := some ``reductionNDAccessesInBounds_proven }
]

end JuliaLean.MemSafety.G1
