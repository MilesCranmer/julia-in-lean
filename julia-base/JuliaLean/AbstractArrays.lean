import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.AbstractArrays.Model
import JuliaLean.AbstractArrays.Props
import JuliaLean.AbstractArrays.Refutations
import JuliaLean.AbstractArrays.Proofs

namespace JuliaLean.AbstractArrays

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "abstractarrays-size-axes-dim", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size(::AbstractArray, d)", "axes(::AbstractArray, d)"]
    statement := "For d::Int, size(A,d) and axes(A,d) return the stored dimension for 1 <= d <= ndims(A), a singleton dimension for d > ndims(A), and BoundsError for d < 1."
    source := "base/abstractarray.jl:20-82 (docstrings; axes example states every dimension past ndims has size 1)"
    status := .proven, prop := ``SizeAxesDim, thm := some ``sizeAxesDim_proven },
  { id := "abstractarrays-size-large-dim", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size(::AbstractArray, dim)", "axes(::AbstractArray, d)"]
    statement := "size(A,d) returns 1 for every positive Integer d greater than ndims(A), as axes(A,d) does."
    source := "base/abstractarray.jl:21-24 (size docstring), 63-64 (all dimensions past ndims have size 1)"
    status := .refuted, prop := ``SizeAllIntegerDims, thm := some ``sizeAllIntegerDims_refuted
    issue := "none found (queries: size dimension InexactError; size UInt dimension; size typemax dimension axes; size(A,d) Int(dim); matching PR searches)"
    notes := "UInt64(2)^63, Int128(typemax(Int))+1 and BigInt(typemax(Int))+1 all throw InexactError in size(A,d), while axes(A,d) returns OneTo(1), on release and nightly." },
  { id := "abstractarrays-checkindex-forms", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex(::Type{Bool}, ::AbstractUnitRange, ::Real)", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::Colon)", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::AbstractRange)"]
    statement := "Integer scalars are checked against both axis endpoints, Colon is always accepted, and a range is accepted exactly when it is empty or both endpoints are in bounds."
    source := "base/abstractarray.jl:730-760 (checkindex docstring and methods)"
    status := .proven, prop := ``CheckIndexForms, thm := some ``checkIndexForms_proven },
  { id := "abstractarrays-checkbounds-cartesian", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds_indices", "checkbounds(::Type{Bool}, ::AbstractArray, I...)"]
    statement := "CartesianIndex components and ordinary Cartesian scalar indices consume axes in order; missing or extra coordinates are accepted exactly for trailing singleton dimensions."
    source := "base/abstractarray.jl:682-728 (checkbounds_indices documentation and recursion)"
    status := .proven, prop := ``CheckboundsCartesian, thm := some ``checkboundsCartesian_proven },
  { id := "abstractarrays-checkbounds-logical", juliaFile := "base/multidimensional.jl"
    juliaFns := ["checkbounds(::Type{Bool}, ::AbstractArray, ::AbstractArray{Bool})", "checkindex(::Type{Bool}, inds, ::AbstractArray{Bool})"]
    statement := "A logical mask is in bounds exactly when its axes equal the array axes it consumes; a vector mask uses the linear index axis."
    source := "base/multidimensional.jl:898-920 (logical-index bounds methods)"
    status := .proven, prop := ``CheckboundsLogical, thm := some ``checkboundsLogical_proven },
  { id := "abstractarrays-checkbounds-linear", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds(::Type{Bool}, ::AbstractArray, i)", "eachindex(::IndexLinear, ::AbstractArray)"]
    statement := "One scalar integer index uses the offset axis for a vector and 1:length(A) for every other AbstractArray."
    source := "base/abstractarray.jl:384-403,687-693"
    status := .proven, prop := ``CheckboundsLinear, thm := some ``checkboundsLinear_proven },
  { id := "abstractarrays-checkbounds-real-index", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds(::Type{Bool}, ::AbstractArray, i)", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::Real)", "to_index(::Bool)", "to_index(i)"]
    statement := "checkbounds(Bool,A,i) is true exactly when i is a supported scalar array index whose value is in bounds."
    source := "base/abstractarray.jl:655-692 (checkbounds docstring); base/indices.jl:230-266 (to_index supported forms)"
    status := .refuted, prop := ``CheckboundsAgreesGetindex, thm := some ``checkboundsAgreesGetindex_refuted
    issue := "none found (queries: checkbounds Bool index; checkbounds Float64 invalid index; checkindex Real; invalid index true checkbounds; PRs for checkbounds Bool and checkindex Real)"
    notes := "On release and nightly, checkbounds(Bool,A,true) and checkbounds(Bool,A,2.5) return true for a three-element generic AbstractVector, while A[true] and A[2.5] throw ArgumentError. The Real method tests only numeric endpoints." },
  { id := "abstractarrays-to-indices-cartesian", juliaFile := "base/indices.jl"
    juliaFns := ["to_indices", "to_index", "to_indices(::Tuple{CartesianIndex,Vararg})"]
    statement := "to_indices flattens CartesianIndex components into canonical integer indices and converts every scalar through to_index."
    source := "base/indices.jl:230-323; base/multidimensional.jl:926-939"
    status := .proven, prop := ``ToIndicesCartesian, thm := some ``toIndicesCartesian_proven },
  { id := "abstractarrays-copyto-generic", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(::AbstractArray, ::AbstractArray)", "copyto_unaliased!"]
    statement := "Generic copyto! copies source elements in iteration order into the first source-length slots of any longer offset destination, preserves remaining slots, and throws BoundsError before mutation when the destination is shorter."
    source := "base/abstractarray.jl:1042-1123 (copyto! docstring and generic implementation)"
    status := .proven, prop := ``CopytoGeneric, thm := some ``copytoGeneric_proven },
  { id := "abstractarrays-copyto-overlap", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(::AbstractArray, dstart, ::AbstractArray, sstart, n)", "unalias"]
    statement := "Overlapping copyto! on one array equals copying from a snapshot for every valid source and destination block, in either overlap direction."
    source := "base/abstractarray.jl:1072-1151 (unalias before generic copies); copyto! aliasing contract"
    status := .proven, prop := ``CopytoOverlap, thm := some ``copytoOverlap_proven },
  { id := "abstractarrays-similar-fallback", juliaFile := "base/abstractarray.jl"
    juliaFns := ["similar(::AbstractArray, ::Type, dims)"]
    statement := "The generic one-based similar fallback returns an unassigned array with the requested length and element positions."
    source := "base/abstractarray.jl:775-873 (similar docstring and fallbacks)"
    status := .proven, prop := ``SimilarFallback, thm := some ``similarFallback_proven },
  { id := "abstractarrays-index-iteration", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eachindex(::AbstractVector)", "firstindex(::AbstractArray)", "lastindex(::AbstractArray)"]
    statement := "For every offset AbstractVector, eachindex enumerates its axis in order and firstindex and lastindex are the endpoints of that axis."
    source := "base/abstractarray.jl:321-453 (eachindex, firstindex and lastindex docstrings and methods)"
    status := .proven, prop := ``IndexIteration, thm := some ``indexIteration_proven },
  { id := "abstractarrays-isassigned", juliaFile := "base/multidimensional.jl"
    juliaFns := ["isassigned(::AbstractArray, ::Integer...)"]
    statement := "isassigned is true exactly for a supported in-bounds integer index whose slot is assigned, and false for bounds and undefined-reference failures."
    source := "base/multidimensional.jl:1619-1660"
    status := .proven, prop := ``IsassignedSpec, thm := some ``isassignedSpec_proven },
  { id := "abstractarrays-concat-vectors", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat(::AbstractVector...)", "hcat(::AbstractVecOrMat...)", "promote_eltype"]
    statement := "vcat of mixed-element-type AbstractVectors concatenates promoted values in order; hcat makes one column per vector and rejects unequal row counts."
    source := "base/abstractarray.jl:1680-1825"
    status := .proven, prop := ``ConcatVectors, thm := some ``concatVectors_proven },
  { id := "abstractarrays-basic-ops", juliaFile := "base/abstractarray.jl"
    juliaFns := ["reverse(::AbstractVector)", "fill!(::AbstractArray, x)", "isempty(::AbstractArray)"]
    statement := "reverse preserves an offset vector's axis and reverses its values, fill! assigns the converted value everywhere, and isempty is true exactly at length zero."
    source := "base/array.jl:336-378,2212-2265; base/abstractarray.jl:1262"
    status := .proven, prop := ``BasicArrayOps, thm := some ``basicArrayOps_proven },
  { id := "abstractarrays-require-one-based", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes", "require_one_based_indexing"]
    statement := "For Int-valued axes, require_one_based_indexing succeeds exactly when every axis begins at one and otherwise throws ArgumentError."
    source := "base/abstractarray.jl:105-135 (docstrings and methods)"
    status := .proven, prop := ``RequireOneBased, thm := some ``requireOneBased_proven },
  { id := "abstractarrays-require-one-based-large-axis", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes(::AbstractVector)", "has_offset_axes(A)", "require_one_based_indexing"]
    statement := "For every integer-valued axis that does not start at one, has_offset_axes returns true and require_one_based_indexing throws ArgumentError."
    source := "base/abstractarray.jl:105-135 (docstrings); axes accepts AbstractUnitRange{<:Integer} at lines 69-70"
    status := .refuted, prop := ``RequireOneBasedAllIntegerAxes, thm := some ``requireOneBasedAllIntegerAxes_refuted
    issue := "none found (queries: require_one_based_indexing InexactError; has_offset_axes UInt; offset axes typemax UInt; require one based indexing ArgumentError; matching PR searches)"
    notes := "An IdentityUnitRange(typemax(UInt):typemax(UInt)) axis makes both functions throw InexactError because lines 115-116 convert first(axis) to Int. Reproduced on release and nightly." },
  { id := "abstractarrays-linear-cartesian-roundtrip", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_to_linear_index", "_to_subscript_indices", "_sub2ind", "_ind2sub"]
    statement := "For every nonnegative shape whose element count fits Int, converting any in-bounds linear index to column-major Cartesian subscripts and back returns the original index."
    source := "base/abstractarray.jl:1392-1436,3165-3232"
    status := .proven, prop := ``LinearCartesianRoundTrip, thm := some ``linearCartesianRoundTrip_proven }
]

end JuliaLean.AbstractArrays
