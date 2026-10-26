import JuliaLean.Registry.Types
import JuliaLean.MemSafety.G4.Proofs
import JuliaLean.BitArrays
import JuliaLean.ReinterpretArrays
import JuliaLean.Sort

namespace JuliaLean.MemSafety.G4

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-4.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-bitarray-copy-chunks", juliaFile := "base/bitarray.jl"
    juliaFns := ["copy_chunks!", "fill_chunks!", "copy_to_bitarray_chunks!", "copyto!"]
    statement := "Every bit position reached after copyto!'s public range checks maps to an in-bounds source and destination chunk."
    source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; copyto! checks at base/bitarray.jl:454-469"
    status := .proven, prop := ``BitArrayCopyChunksInBounds, thm := some ``bitArrayCopyChunksInBounds },
  { id := "memsafety-bitarray-builder-cache", juliaFile := "base/bitarray.jl"
    juliaFns := ["gen_bitarray_from_itr", "fill_bitarray_from_itr!"]
    statement := "The builder cache index starts at one and resets after every 4096 stores, so every cache access is in bounds."
    source := "base/bitarray.jl:607-655; invariant: the cache is allocated with bitcache_size elements"
    status := .proven, prop := ``BitCacheInBounds, thm := some ``bitCacheInBounds },
  { id := "memsafety-bitarray-valid-chunk-index", juliaFile := "base/bitarray.jl"
    juliaFns := ["unsafe_bitgetindex", "unsafe_bitsetindex!", "findnext", "findprev", "findnextnot", "findprevnot"]
    statement := "After the public scalar/start check, get_chunks_id computes an in-bounds chunk for every valid BitArray."
    source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; checks at base/bitarray.jl:668-690,1469-1481,1553-1564"
    status := .proven, prop := ``BitArrayChunkInBounds, thm := some ``bitArrayChunkInBounds },
  { id := "memsafety-bitarray-vector-loops", juliaFile := "base/bitarray.jl"
    juliaFns := ["bitcount", "findall", "all", "any", "reverse!", "map!"]
    statement := "Loops derived from a chunk vector's own length access only indices one through that length."
    source := "invariant: each loop is over 1:length(B.chunks), base/bitarray.jl:1263-1305,1439-1444,1611-1735"
    status := .proven, prop := ``BitVectorLoopInBounds, thm := some ``bitVectorLoopInBounds },
  { id := "memsafety-bitarray-find-extrema", juliaFile := "base/bitarray.jl"
    juliaFns := ["findmin(::BitArray)", "findmax(::BitArray)"]
    statement := "After rejecting an empty array, the chunk scan returns the first matching logical key or key one, all within the BitArray axes."
    source := "base/bitarray.jl:1611-1638; BitArray chunk and zero-padding invariants"
    status := .proven, prop := ``BitFindKeyInBounds, thm := some ``bitFindKeyInBounds },
  { id := "memsafety-bitarray-findall-output", juliaFile := "base/bitarray.jl"
    juliaFns := ["findall(::BitArray)"]
    statement := "findall allocates count(B) output slots and writes one slot for each true bit, so its output counter stays in bounds."
    source := "base/bitarray.jl:1679-1705; count and BitArray zero-padding invariants"
    status := .proven, prop := ``BitFindAllInBounds, thm := some ``bitFindAllInBounds },
  { id := "memsafety-bitarray-mask-chunks", juliaFile := "base/bitarray.jl"
    juliaFns := ["_unsafe_setindex!(::BitArray, ::AbstractArray, ::BitArray)"]
    statement := "The explicit equal-chunk-count check makes every mask and destination chunk access use the same in-bounds index."
    source := "base/bitarray.jl:707-733; invariant: line 710 rejects unequal chunk-vector lengths"
    status := .proven, prop := ``BitMaskChunksInBounds, thm := some ``bitMaskChunksInBounds },
  { id := "memsafety-bitarray-mask-source", juliaFile := "base/bitarray.jl"
    juliaFns := ["_unsafe_setindex!(::BitArray, ::AbstractArray, ::BitArray)"]
    statement := "Logical mask assignment checks source exhaustion before each X[Xi] access and advances Xi once per selected bit."
    source := "base/bitarray.jl:714-733"
    status := .proven, prop := ``BitMaskSourceInBounds, thm := some ``bitMaskSourceInBounds },
  { id := "memsafety-boot-array-getindex", juliaFile := "base/boot.jl"
    juliaFns := ["getindex(::Array, ::Int) during bootstrap"]
    statement := "The bootstrap unsigned range check permits memoryrefget only at an index in 1:length(A)."
    source := "base/boot.jl:879-883"
    status := .proven, prop := ``BootArrayRefInBounds, thm := some ``bootArrayRefInBounds },
  { id := "memsafety-broadcast-eachindex", juliaFile := "base/broadcast.jl"
    juliaFns := ["getindex(::Broadcasted)", "copy", "copyto!", "copyto_nonleaf!", "copy(::Broadcasted{Style{Tuple}})"]
    statement := "Broadcast checks equal axes and then uses only indices yielded by those axes for source and destination accesses."
    source := "base/broadcast.jl:615-629,948-974,1015-1029,1145-1172"
    status := .proven, prop := ``BroadcastEachindexInBounds, thm := some ``broadcastEachindexInBounds },
  { id := "memsafety-broadcast-bitarray-chunks", juliaFile := "base/broadcast.jl"
    juliaFns := ["copyto!(::BitArray, ::Broadcasted)", "chunkedcopyto!"]
    statement := "BitArray broadcast writes sequential chunks allocated from the destination length and masks the existing final chunk."
    source := "BitArray chunk-count invariant; base/broadcast.jl:1035-1072,1120-1129"
    status := .proven, prop := ``BroadcastChunkInBounds, thm := some ``broadcastChunkInBounds },
  { id := "memsafety-hamt-entry-index", juliaFile := "base/hamt.jl"
    juliaFns := ["path", "insert!", "entry_index"]
    statement := "For a present HAMT bitmap bit, one plus the set-bit count before it is an in-bounds data slot."
    source := "HAMT bitmap/data-length invariant at base/hamt.jl:127-140"
    status := .proven, prop := ``HamtSlotInBounds, thm := some ``hamtSlotInBounds },
  { id := "memsafety-precompilation-process-stats", juliaFile := "base/precompilation.jl"
    juliaFns := ["_get_process_stats"]
    statement := "The UInt64 reads at byte offsets 8, 16 and 24 fit in the allocated 96-byte proc_taskinfo buffer."
    source := "base/precompilation.jl:2102-2111"
    status := .proven, prop := ``ProcessStatsReadsInBounds, thm := some ``processStatsReadsInBounds },
  { id := "memsafety-rational-parse-split", juliaFile := "base/rational.jl"
    juliaFns := ["parse(::Type{Rational{T}}, ::AbstractString)"]
    statement := "split with limit two returns two parts on the branch that reads ss[1] and ss[2]."
    source := "base/rational.jl:175-186; split contract with limit=2"
    status := .proven, prop := ``RationalSplitInBounds, thm := some ``rationalSplitInBounds },
  { id := "memsafety-reinterpretarray-getindex", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["getindex(::ReinterpretArray)", "_getindex_ptr", "_getindex_ra"]
    statement := "Every pointer and parent-element read used to assemble a checked ReinterpretArray element stays in its parent byte image."
    source := "reinterpret docstring at base/reinterpretarray.jl:35-39; checks and branches at lines 433-567"
    status := .proven, prop := ``JuliaLean.ReinterpretArrays.RaGetCorrect
    thm := some ``JuliaLean.ReinterpretArrays.raGetCorrect },
  { id := "memsafety-reinterpretarray-setindex", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["setindex!(::ReinterpretArray)", "_setindex_ptr!", "_setindex_ra!"]
    statement := "Every pointer and parent-element write used for a checked ReinterpretArray element stays in its parent byte image."
    source := "reinterpret and shared-data docstrings; base/reinterpretarray.jl:579-730"
    status := .proven, prop := ``JuliaLean.ReinterpretArrays.RaSetCorrect
    thm := some ``JuliaLean.ReinterpretArrays.raSetCorrect },
  { id := "memsafety-reinterpretarray-mapreduce", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_mapreduce", "mapreduce_impl(::SCartesianIndex2)"]
    statement := "The sequential and pairwise branches visit only the K by n indices returned by eachindex."
    source := "base/reinterpretarray.jl:943-978"
    status := .proven, prop := ``ReinterpretMapreduceInBounds, thm := some ``reinterpretMapreduceInBounds },
  { id := "memsafety-reinterpretarray-totuple", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_totuple(::Type{All32}, ::Union{Array,Memory})"]
    statement := "After the length check, the N+32 element view reinterprets to one tuple and index one is valid."
    source := "base/reinterpretarray.jl:984-995"
    status := .proven, prop := ``ReinterpretTupleInBounds, thm := some ``reinterpretTupleInBounds },
  { id := "memsafety-runtime-fieldname", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldname", "getindex(::DataTypeFieldDesc)"]
    statement := "Both field accessors reject indices outside 1:nfields before their unchecked read."
    source := "base/runtime_internals.jl:391-405,797-812"
    status := .proven, prop := ``RuntimeFieldInBounds, thm := some ``runtimeFieldInBounds },
  { id := "memsafety-runtime-field-bitmaps", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["isconst(::Type, ::Int)", "isfieldatomic(::Type, ::Int)"]
    statement := "A checked field number maps to a word within the runtime field bitmap."
    source := "base/runtime_internals.jl:544-578; DataType field-bitmap representation invariant"
    status := .proven, prop := ``RuntimeBitfieldInBounds, thm := some ``runtimeBitfieldInBounds },
  { id := "memsafety-runtime-metadata", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["DataTypeLayout", "getindex(::DataTypeFieldDesc)", "get_require_world"]
    statement := "Runtime-owned metadata pointers are read only as their complete represented object after null and field checks."
    source := "runtime object representation; base/runtime_internals.jl:625-645,789-812,1662"
    status := .proven, prop := ``RuntimeMetadataAccessesInBounds, thm := some ``runtimeMetadataAccessesInBounds },
  { id := "memsafety-ryu-lookup-index", juliaFile := "base/ryu/utils.jl"
    juliaFns := ["pow5invsplit_lookup", "pow5split_lookup"]
    statement := "Every index accepted by the documented Ryu lookup helpers selects an element of the generated tuple."
    source := "base/ryu/utils.jl:286-325 (lookup docstrings state no index precondition)"
    status := .refuted, prop := ``RyuLookupInBounds, thm := some ``ryuLookupInBounds_refuted
    issue := "none found (queries: pow5invsplit_lookup bounds; Ryu lookup negative index; PRs same)"
    notes := "i=-1 computes tuple index zero in both helpers; forced bounds checks reproduce on release and nightly." },
  { id := "memsafety-simdloop-index", juliaFile := "base/simdloop.jl"
    juliaFns := ["@simd", "simd_index"]
    statement := "The generated zero-based counter selects exactly one member of the iterator's one-dimensional index range."
    source := "@simd contract and generated loop at base/simdloop.jl:39-85,90-120"
    status := .proven, prop := ``SimdIndexInBounds, thm := some ``simdIndexInBounds },
  { id := "memsafety-sort-send-to-end-window", juliaFile := "base/sort.jl"
    juliaFns := ["send_to_end!(f, v; lo, hi)"]
    statement := "Every lo and hi accepted by send_to_end! keep both unchecked loops within v."
    source := "base/sort.jl:610-633 (docstring promises equivalence to a checked view)"
    status := .refuted, prop := ``SendToEndInBounds, thm := some ``sendToEndInBounds_refuted
    issue := "none found (queries: send_to_end bounds; send_to_end out of bounds; PRs same)"
    notes := "lo=0, hi=2 reads v[0]; forced bounds checks reproduce on release and nightly." },
  { id := "memsafety-sort-checked-windows", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!", "_issorted", "uint_map!", "uint_unmap!", "legacy sort! kernels"]
    statement := "After the public checkbounds call, every direct lo:hi loop index is within the vector."
    source := "base/sort.jl:835-900,1020-1045,1445-1451,2294-2309,2454-2580"
    status := .proven, prop := ``CheckedIntervalInBounds, thm := some ``checkedIntervalInBounds },
  { id := "memsafety-sort-bool-fill", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(::AbstractVector{Bool}, ::BoolOptimization)"]
    statement := "The input scan, counted prefix fill, and remaining suffix fill all stay within the checked Boolean vector window."
    source := "base/sort.jl:746-757"
    status := .proven, prop := ``BoolSortInBounds, thm := some ``boolSortInBounds },
  { id := "memsafety-sort-vector-search-first", juliaFile := "base/sort.jl"
    juliaFns := ["searchsortedfirst(::AbstractVector)"]
    statement := "For the documented sorted-vector input and public 1:length window, searchsortedfirst never reads outside the vector."
    source := "searchsortedfirst docstring and base/sort.jl:182-199,304-311"
    status := .proven, prop := ``VectorSearchFirstInBounds, thm := some ``vectorSearchFirstInBounds },
  { id := "memsafety-sort-perm-data-indices", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(::IEEEFloatOptimization, ::Perm)"]
    statement := "The Perm optimization executes only after verifying that its index vector equals eachindex(o.data), so each o.data[i] access uses one of those indices."
    source := "base/sort.jl:656-658,718-727"
    status := .proven, prop := ``SortPermDataInBounds, thm := some ``sortPermDataInBounds },
  { id := "memsafety-sort-count-buckets", juliaFile := "base/sort.jl"
    juliaFns := ["_sort!(::CountingSort)", "sortperm_int_range"]
    statement := "Normalizing a value by the computed minimum selects one of the range+1 count buckets."
    source := "base/sort.jl:923-966,2057-2078"
    status := .proven, prop := ``SortCountBucketInBounds, thm := some ``sortCountBucketInBounds },
  { id := "memsafety-sort-partition-indices", juliaFile := "base/sort.jl"
    juliaFns := ["partition!", "bracket_kernel!", "_quicksort!", "_mergesort!", "_partialquicksort!"]
    statement := "After normalizing a checked lo:hi window, each current-position or end-position branch index stays in the one-based source or scratch span."
    source := "base/sort.jl:1084-1118,1226-1245,2401-2565"
    status := .proven, prop := ``SortPartitionInBounds, thm := some ``sortPartitionInBounds },
  { id := "memsafety-sort-radix-buckets", juliaFile := "base/sort.jl"
    juliaFns := ["radix_sort!", "radix_sort_pass!"]
    statement := "Masking a radix digit to chunk bits selects only the allocated counter slots."
    source := "base/sort.jl:1384-1428"
    status := .proven, prop := ``SortRadixBucketInBounds, thm := some ``sortRadixBucketInBounds },
  { id := "memsafety-strings-search-loops", juliaFile := "base/strings/search.jl"
    juliaFns := ["findnext", "findprev", "findall"]
    statement := "After start validation, nextind and prevind move only through the string's valid character positions."
    source := "findnext/findprev contracts and base/strings/search.jl:342-353,651-678"
    status := .proven, prop := ``StringSearchInBounds, thm := some ``stringSearchInBounds },
  { id := "memsafety-sysinfo-cpu-info", juliaFile := "base/sysinfo.jl"
    juliaFns := ["Sys.cpu_info"]
    statement := "cpu_info reads exactly the count records returned and initialized by libuv."
    source := "libuv uv_cpu_info contract; base/sysinfo.jl:309-323"
    status := .proven, prop := ``CpuInfoInBounds, thm := some ``cpuInfoInBounds }
]

end JuliaLean.MemSafety.G4
