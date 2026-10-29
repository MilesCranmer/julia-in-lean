import JuliaLean.Registry.Types
import JuliaLean.MemSafety.G4.Proofs
import JuliaLean.BitArrays
import JuliaLean.ReinterpretArrays
import JuliaLean.Sort

namespace JuliaLean.MemSafety.G4

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-4.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-boot-array-getindex", juliaFile := "base/boot.jl"
    juliaFns := ["getindex(::Array, ::Int) during bootstrap"]
    statement := "The bootstrap unsigned range check permits memoryrefget only at an index in 1:length(A)."
    source := "base/boot.jl:879-883"
    status := .proven, prop := ``BootArrayRefInBounds, thm := some ``bootArrayRefInBounds },
  { id := "memsafety-precompilation-process-stats", juliaFile := "base/precompilation.jl"
    juliaFns := ["_get_process_stats"]
    statement := "The UInt64 reads at byte offsets 8, 16 and 24 fit in the allocated 96-byte proc_taskinfo buffer."
    source := "base/precompilation.jl:2102-2111"
    status := .proven, prop := ``ProcessStatsReadsInBounds, thm := some ``processStatsReadsInBounds },
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
  { id := "memsafety-sysinfo-cpu-info", juliaFile := "base/sysinfo.jl"
    juliaFns := ["Sys.cpu_info"]
    statement := "cpu_info reads exactly the count records returned and initialized by libuv."
    source := "libuv uv_cpu_info contract; base/sysinfo.jl:309-323"
    status := .proven, prop := ``CpuInfoInBounds, thm := some ``cpuInfoInBounds }
]

end JuliaLean.MemSafety.G4
