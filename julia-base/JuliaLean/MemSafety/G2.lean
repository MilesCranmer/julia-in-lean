import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.MemSafety.G2.Proofs

namespace JuliaLean.MemSafety.G2

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-2.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-arraymath-reverse", juliaFile := "base/arraymath.jl"
    juliaFns := ["_reverse!(::AbstractArray, ::NTuple)"]
    statement := "Every swap coordinate computed by reverse!, including recursive odd middle slices, is inside the selected array view."
    source := "memory-safety invariant; base/arraymath.jl:107-130"
    status := .proven, prop := ``ReverseInBounds, thm := some ``reverseInBounds },
  { id := "memsafety-experimental-const-getindex", juliaFile := "base/experimental.jl"
    juliaFns := ["getindex(::Experimental.Const, ::Int)", "getindex(::Experimental.Const, ::Int...)"]
    statement := "Const's completed scalar or Cartesian bounds check makes its computed memory or linear index valid for the wrapped Array."
    source := "Array representation invariant; base/experimental.jl:25-40"
    status := .proven, prop := ``ConstGetindexInBounds, thm := some ``constGetindexInBounds },
  { id := "memsafety-expr-copy", juliaFile := "base/expr.jl"
    juliaFns := ["copy(::PhiNode)", "copy(::PhiCNode)", "copy_exprargs"]
    statement := "The expression-copy loops read and write only the slots computed from length(values) or eachindex(x)."
    source := "Array iteration invariant; base/expr.jl:45-79"
    status := .proven, prop := ``ExprCopyInBounds, thm := some ``exprCopyInBounds },
  { id := "memsafety-gmp-zero-bool-rem-null", juliaFile := "base/gmp.jl"
    juliaFns := ["rem(::BigInt, ::Type{Bool})"]
    statement := "The eager Boolean remainder method reads a valid first limb for every live BigInt storage representation."
    source := "memory-safety invariant; base/gmp.jl:129,294,367"
    status := .refuted, prop := ``GmpBoolRemInBounds, thm := some ``gmpBoolRemInBounds_refuted
    issue := "none found (queries: BigInt ZERO rem Bool segfault; GMP ZERO unsafe_load rem)"
    notes := "Base.GMP.ZERO has a null limb pointer; rem(Base.GMP.ZERO, Bool) terminates both tested Julia child processes with signal 11." },
  { id := "memsafety-gmp-limb-convert", juliaFile := "base/gmp.jl"
    juliaFns := ["BigInt(::Integer)", "rem(::BigInt, ::Type)", "(::Type{<:IEEEFloat})(::BigInt, ::RoundingMode)"]
    statement := "BigInt construction, fixed-width remainder, and floating conversion derive every limb index from the input value's normalized limb count."
    source := "GMP normalized-limb representation; base/gmp.jl:347-465"
    status := .proven, prop := ``GmpLimbAccessesInBounds, thm := some ``gmpLimbAccessesInBounds },
  { id := "memsafety-gmp-bit-magnitude", juliaFile := "base/gmp.jl"
    juliaFns := ["exponent(::BigInt)", "top_set_bit(::BigInt)", "_bit_magnitude"]
    statement := "The public callers reject zero before _bit_magnitude reads the most-significant normalized limb."
    source := "base/gmp.jl:608-623"
    status := .proven, prop := ``GmpBitMagnitudeInBounds, thm := some ``gmpBitMagnitudeInBounds },
  { id := "memsafety-gmp-string", juliaFile := "base/gmp.jl"
    juliaFns := ["string(::BigInt)"]
    statement := "string allocates the digit and sign count computed from n, base, and pad before writing a negative sign at byte one."
    source := "base/gmp.jl:765-781"
    status := .proven, prop := ``GmpStringSignInBounds, thm := some ``gmpStringSignInBounds },
  { id := "memsafety-gmp-hash", juliaFile := "base/gmp.jl"
    juliaFns := ["UnsafeLimbView.getindex", "iterate(::UnsafeLimbView)", "hash_integer(::BigInt)", "hash(::BigInt)"]
    statement := "The BigInt hash branches and each byte index requested from their computed UnsafeLimbViews select an allocated limb."
    source := "GMP normalized-limb representation; base/gmp.jl:873-955"
    status := .proven, prop := ``GmpHashInBounds, thm := some ``gmpHashInBounds },
  { id := "memsafety-hashing-hash-bytes", juliaFile := "base/hashing.jl"
    juliaFns := ["load_le_array", "hash_bytes(::AbstractArray{UInt8}, ...)"]
    statement := "Every byte offset computed by the small, 48-byte-loop, remaining, and final hash branches is below length(arr)."
    source := "base/hashing.jl:378-466"
    status := .proven, prop := ``HashArrayInBounds, thm := some ``hashArrayInBounds },
  { id := "memsafety-loading-isfile-casesensitive", juliaFile := "base/loading.jl"
    juliaFns := ["isfile_casesensitive"]
    statement := "Every loop iteration reads the four-byte filename-length field from a buffer allocated or resized to include its 12-byte header."
    source := "getattrlist buffer layout; base/loading.jl:33-65"
    status := .proven, prop := ``LoadingHeaderInBounds, thm := some ``loadingHeaderInBounds },
  { id := "memsafety-missing-skipmissing-eachindex", juliaFile := "base/missing.jl"
    juliaFns := ["eachindex(::SkipMissing)"]
    statement := "SkipMissing evaluates its filter only at indices computed by the wrapped IndexLinear array's eachindex."
    source := "array iteration invariant; base/missing.jl:252-254"
    status := .proven, prop := ``SkipMissingEachindexInBounds, thm := some ``skipMissingEachindexInBounds },
  { id := "memsafety-missing-skipmissing-keys", juliaFile := "base/missing.jl"
    juliaFns := ["keys(::SkipMissing)"]
    statement := "SkipMissing evaluates its keys filter only at Cartesian keys computed from the wrapped array's axes."
    source := "array keys invariant; base/missing.jl:255-256"
    status := .proven, prop := ``SkipMissingKeysInBounds, thm := some ``skipMissingKeysInBounds },
  { id := "memsafety-missing-mapreduce", juliaFile := "base/missing.jl"
    juliaFns := ["_mapreduce(::IndexLinear, ::SkipMissing)", "_mapreduce_impl_skipmissing"]
    statement := "Both preliminary scans and every sequential or pairwise mapreduce block compute indices within LinearIndices(A), including typemax guards."
    source := "base/missing.jl:269-351"
    status := .proven, prop := ``MissingMapreduceInBounds, thm := some ``missingMapreduceInBounds },
  { id := "memsafety-multidimensional-cartesian-collect", juliaFile := "base/multidimensional.jl"
    juliaFns := ["collect(::CartesianIndices)"]
    statement := "CartesianIndices iteration performs exactly product(size(inds)) writes into a destination of that length."
    source := "CartesianIndices iteration invariant; base/multidimensional.jl:631-640"
    status := .proven, prop := ``CartesianCollectInBounds, thm := some ``cartesianCollectInBounds },
  { id := "memsafety-multidimensional-logicalindex", juliaFile := "base/multidimensional.jl"
    juliaFns := ["iterate(::LogicalIndex{<:Any,<:BitArray})"]
    statement := "The nonzero-sum guard supplies the first BitArray chunk, and the zero-chunk loop checks the chunk count before each incremented read."
    source := "BitArray storage invariant; base/multidimensional.jl:834-895"
    status := .proven, prop := ``LogicalIndexInBounds, thm := some ``logicalIndexInBounds },
  { id := "memsafety-multidimensional-unsafe-indexing", juliaFile := "base/multidimensional.jl"
    juliaFns := ["_unsafe_getindex!", "_unsafe_setindex!"]
    statement := "After public bounds and shape checks, the Cartesian index product computes valid source/destination coordinates and exact destination/source iteration counts."
    source := "base/multidimensional.jl:995-1079"
    status := .proven, prop := ``GenericIndexingInBounds, thm := some ``genericIndexingInBounds },
  { id := "memsafety-multidimensional-cartesian-copyto", juliaFile := "base/multidimensional.jl"
    juliaFns := ["copyto!(::AbstractArray, ::CartesianIndices, ::AbstractArray, ::CartesianIndices)"]
    statement := "Equal-size source and destination regions whose endpoints pass checkbounds map every computed Cartesian coordinate inside both parents."
    source := "copyto! region contract; base/multidimensional.jl:1190-1222"
    status := .proven, prop := ``CartesianCopyInBounds, thm := some ``cartesianCopyInBounds },
  { id := "memsafety-multidimensional-bitarray-source-scan", juliaFile := "base/multidimensional.jl"
    juliaFns := ["copy_to_bitarray_chunks!(::Vector{UInt64}, ::Int, ::StridedArray{<:Real}, ::Int, ::Int)"]
    statement := "The Real-source conversion pre-scan reads exactly the shape-checked source interval."
    source := "base/multidimensional.jl:1459-1462,1516-1562"
    status := .proven, prop := ``BitSourceScanInBounds, thm := some ``bitSourceScanInBounds },
  { id := "memsafety-multidimensional-isassigned", juliaFile := "base/multidimensional.jl"
    juliaFns := ["isassigned(::AbstractArray, ::Integer...)"]
    statement := "After to_indices and checkbounds, both IndexLinear and IndexCartesian conversion branches address the same array."
    source := "base/multidimensional.jl:1637-1660"
    status := .proven, prop := ``IsassignedInBounds, thm := some ``isassignedInBounds },
  { id := "memsafety-reshapedarray-ind2sub", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["isassigned(::ReshapedArray, ::Int...)", "_unsafe_getindex(::ReshapedArray, ::Int...)", "_unsafe_setindex!(::ReshapedArray, ..., ::Int...)"]
    statement := "The checked Cartesian path computes its linear index, uses the constructor-supplied multiplicative inverses, and produces in-bounds parent subscripts."
    source := "reshape length and SignedMultiplicativeInverse representation invariants; base/reshapedarray.jl:235-241,270-276,285-291,308-317,324-338"
    status := .proven, prop := ``JuliaLean.ReinterpretArrays.Ind2subCorrect
    thm := some ``JuliaLean.ReinterpretArrays.ind2subCorrect },
  { id := "memsafety-reshapedarray-indexing", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["isassigned(::ReshapedArrayLF, ::Int)", "getindex(::ReshapedArrayLF, ::Int)", "setindex!(::ReshapedArrayLF, ..., ::Int)", "getindex(::ReshapedArray, ::ReshapedIndex)", "setindex!(::ReshapedArray, ..., ::ReshapedIndex)"]
    statement := "The checked linear fast path translates through the equal-length offset parent axis, and ReshapedIndex forwards only a parent index already checked against that parent."
    source := "reshape length invariant and explicit parent check; base/reshapedarray.jl:278-306,320-331"
    status := .proven, prop := ``ReshapedIndexingInBounds, thm := some ``reshapedIndexingInBounds },
  { id := "memsafety-ryu-exponent-table", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.writeshortest(::Float16)", "Ryu.writeshortest(::Float32)", "Ryu.writeshortest(::Float64)"]
    statement := "For every IEEE input type accepted by writeshortest, the exponent computed by reduce_shortest selects one of the 100 DIGIT_TABLE16 entries."
    source := "base/ryu/shortest.jl:7-226,319-447"
    status := .proven, prop := ``RyuExponentTableInBounds, thm := some ``ryuExponentTableInBounds },
  { id := "memsafety-rem-pio2-paynehanek-callers", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["rem_pio2_kernel(::Float64)", "rem_pio2_kernel(::Float32)", "paynehanek(::Float64)"]
    statement := "Every public Float64 and Float32 reduction path that reaches paynehanek computes INV_2PI positions 1 through 19."
    source := "base/special/rem_pio2.jl:130-178,222-293"
    status := .proven, prop := ``PayneHanekCallerInBounds, thm := some ``payneHanekCallerInBounds },
  { id := "memsafety-stringview-indexing", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["getindex(::StringView, ::UnitRange{Int})", "chomp(::StringViewAndSub)"]
    statement := "StringView range checks protect both UTF-8 validity probes, and chomp computes a substring length no greater than its code-unit length."
    source := "base/strings/stringview.jl:122-150"
    status := .proven, prop := ``StringViewInBounds, thm := some ``stringViewInBounds },
  { id := "memsafety-summarysize-memory", juliaFile := "base/summarysize.jl"
    juliaFns := ["summarysize"]
    statement := "The frontier transition enumerates length*np inline pointer fields and length direct elements, mapping every field ordinal to an existing GenericMemory element."
    source := "GenericMemory traversal invariant; base/summarysize.jl:45-116,171-190"
    status := .proven, prop := ``SummarySizeInBounds, thm := some ``summarySizeInBounds }
]

end JuliaLean.MemSafety.G2
