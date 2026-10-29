import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.AbstractArraySpecs.Model
import JuliaLean.AbstractArraySpecs.Cat
import JuliaLean.AbstractArraySpecs.Props
import JuliaLean.AbstractArraySpecs.Refutations
import JuliaLean.AbstractArraySpecs.IndexOrdinary
import JuliaLean.AbstractArraySpecs.Indexing
import JuliaLean.AbstractArraySpecs.CopyProofs
import JuliaLean.AbstractArraySpecs.CopyRowsProofs
import JuliaLean.AbstractArraySpecs.CircshiftProofs
import JuliaLean.AbstractArraySpecs.MapNProofs
import JuliaLean.AbstractArraySpecs.CatEntries

namespace JuliaLean.AbstractArraySpecs

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "abstractarrayspecs-zero-index-offset", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex(A::AbstractArray, I...)", "setindex!(A::AbstractArray, v, I...)",
      "_getindex(::IndexCartesian, A, I::Vararg{Int,M})", "_setindex!(::IndexCartesian, A, v, I::Vararg{Int,M})",
      "_to_subscript_indices(A::AbstractArray{T,N}) where {T,N}", "get(A::AbstractArray, I::Tuple{}, default)"]
    statement := "For any array and any number of Int indices (including none), getindex and setindex! act on the element selected by the manual's linear, Cartesian, omitted and extra index rules and throw BoundsError when none is selected; get returns that element or the default."
    source := "doc/src/manual/arrays.md (Linear indexing; Omitted and extra indices, including the A[] idiom); base/abstractarray.jl:1305-1318, 1441-1447, 1632-1642"
    status := .todo, prop := ``IndexingAgreesWithReference
    notes := "The current theorem is restricted to the Arr model with Int64 axes and mutable storage; it does not establish the generic AbstractArray interface." },
  { id := "abstractarrayspecs-linear-zero-unitrange", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_to_linear_index(A::AbstractArray)", "_getindex(::IndexLinear, A, I::Vararg{Int,M})",
      "_setindex!(::IndexLinear, A, v, I::Vararg{Int,M})", "get(A::AbstractArray, I::Tuple{}, default)"]
    statement := "A zero-index read, defaulted read, and supported write select the sole element of a lawful IndexLinear array."
    source := "doc/src/manual/arrays.md (Omitted and extra indices); doc/src/devdocs/offset-arrays.md (Custom AbstractUnitRange types); base/abstractarray.jl:1392-1401, 1487-1491, 1638; base/indices.jl:482-487, 525-527"
    status := .refuted, prop := ``GenericLinearZeroPromise, thm := some ``genericLinearZeroPromise_refuted
    issue := "none found (queries: LinearIndices UnitRange offset; LinearIndices axes offset)"
    notes := "A singleton linear vector with the permitted UnitRange axis 3:3 uses index 1 for A[], get(A, (), d), and setindex! on release and target." },
  { id := "abstractarrayspecs-cartesian-zero-generic", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_getindex(::IndexCartesian, A, I::Vararg{Int,M})",
      "_setindex!(::IndexCartesian, A, v, I::Vararg{Int,M})", "get(A::AbstractArray, I::Tuple{}, default)"]
    statement := "The generic zero-index Cartesian fallback selects the only element when every axis is singleton and its starts convert to Int; conversion errors propagate, non-singleton arrays produce BoundsError or the default, and a supported setter writes the element."
    source := "base/abstractarray.jl:1404-1416, 1495-1503, 1638; base/indices.jl:243, 258-259"
    status := .proven, prop := ``GenericZeroContract, thm := some ``genericZeroContract_proven
    notes := "Generic scalar-integer conversion and canonical methods are modelled; custom array-specific index conversion and bounds-check overrides are not." },
  { id := "abstractarrayspecs-linear-indexing", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex(A::AbstractArray, I...)", "setindex!(A::AbstractArray, v, I...)",
      "_getindex(::IndexCartesian, A, I::Vararg{Int,M})", "_setindex!(::IndexCartesian, A, v, I::Vararg{Int,M})",
      "_to_subscript_indices(A::AbstractArray, i::Integer)", "_unsafe_ind2sub", "_ind2sub", "_ind2sub_recurse",
      "checkbounds(::Type{Bool}, A::AbstractArray, i)", "eachindex(::IndexLinear, A::AbstractArray)",
      "get(A::AbstractArray, i::Integer, default)"]
    statement := "With one Int index k, getindex, setindex! and get act on the k-th element in column-major order (k ranges over the axis of a vector and over 1:length(A) otherwise) for both IndexStyles and any axes, and throw BoundsError (get: return the default) for any other k."
    source := "doc/src/manual/arrays.md (Linear indexing); base/abstractarray.jl:337-346 (eachindex docstring), 1305-1318, 1441-1447, 1632-1642"
    status := .todo, prop := ``LinearIndexingAgrees
    notes := "The Arr proof assumes Int64 axes and does not model conversion of LinearIndices axis ranges." },
  { id := "abstractarrayspecs-cartesian-indexing", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex(A::AbstractArray, I...)", "setindex!(A::AbstractArray, v, I...)",
      "_getindex(::IndexLinear, A, I::Vararg{Int,M})", "_setindex!(::IndexLinear, A, v, I::Vararg{Int,M})",
      "_to_linear_index", "_sub2ind", "_sub2ind_recurse", "_to_subscript_indices(A, J::Tuple, Jrem::Tuple)",
      "checkbounds_indices", "get(A::AbstractArray, I::Dims, default)"]
    statement := "With ndims(A) or more Int indices, getindex, setindex! and get act on the element at those Cartesian coordinates when every coordinate is within its axis and every extra index is 1, for both IndexStyles and any axes, and throw BoundsError (get: return the default) otherwise."
    source := "doc/src/manual/arrays.md (Cartesian indexing; Omitted and extra indices: more than N indices); base/abstractarray.jl:1305-1318, 1441-1447, 1632-1642"
    status := .proven, prop := ``CartesianIndexingAgrees, thm := some ``cartesianIndexingAgrees_proven },
  { id := "abstractarrayspecs-checkbounds", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds(::Type{Bool}, A::AbstractArray, I...)", "checkbounds(::Type{Bool}, A::AbstractArray, i)",
      "checkbounds(A::AbstractArray, I...)", "checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})",
      "checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{})", "checkindex(::Type{Bool}, inds::AbstractUnitRange, i::Real)",
      "checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger}", "checkindex(::Type{Bool}, inds::IdentityUnitRange, i::Real)"]
    statement := "checkbounds(Bool, A, I...) with Int indices is true exactly when the indices select an element under the manual's linear, Cartesian, omitted and extra index rules, for any axes (including OneTo and offset axes), and checkbounds(A, I...) throws BoundsError exactly when it is false."
    source := "base/abstractarray.jl:655-700 (checkbounds docstrings), 702-748 (checkbounds_indices, checkindex docstrings); doc/src/manual/arrays.md (Omitted and extra indices)"
    status := .proven, prop := ``CheckboundsAgreesWithReference, thm := some ``checkboundsAgreesWithReference_proven },
  { id := "abstractarrayspecs-iterate", juliaFile := "base/abstractarray.jl"
    juliaFns := ["iterate(A::AbstractArray, state = iterate_starting_state(A))", "iterate_starting_state(A)",
      "_iterate_abstractarray(A::AbstractArray, state::Tuple)", "_iterate_abstractarray(A::AbstractArray, state::Integer)"]
    statement := "Iterating any array (either IndexStyle, any axes including offset and empty ones, any number of dimensions including 0) yields exactly its elements in column-major order and then stops."
    source := "doc/src/manual/arrays.md (Iteration); doc/src/manual/interfaces.md (Abstract arrays: iteration over eachindex); base/abstractarray.jl:1239-1260"
    status := .proven, prop := ``IterateColumnMajor, thm := some ``iterateColumnMajor_proven },
  { id := "abstractarrayspecs-eachindex", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eachindex(A::AbstractVector)", "eachindex(A::AbstractArray)", "eachindex(::IndexLinear, A::AbstractArray)",
      "eachindex(::IndexLinear, A::AbstractVector)", "axes1(A::AbstractArray)", "keys(a::AbstractVector)"]
    statement := "Iterating eachindex(A) yields length(A) indices, and its k-th index selects the k-th element in column-major order under the manual's indexing rules, so it visits every valid index exactly once, for either IndexStyle, any axes and any number of dimensions."
    source := "base/abstractarray.jl:337-360 (eachindex docstring), 145-170 (keys docstring); doc/src/manual/arrays.md (Iteration)"
    status := .proven, prop := ``EachindexEnumerates, thm := some ``eachindexEnumerates_proven },
  { id := "abstractarrayspecs-copyto", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(dest::AbstractArray, src::AbstractArray)",
      "copyto_unaliased!(deststyle::IndexStyle, dest::AbstractArray, srcstyle::IndexStyle, src::AbstractArray)",
      "unalias(dest, A::AbstractArray)"]
    statement := "copyto!(dest, src) with length(dest) >= length(src) overwrites the first length(src) elements of dest (in iteration order) with the elements of src and leaves the rest unchanged, and throws when dest is shorter, for every combination of IndexStyles and any axes (including offset axes at typemin/typemax), for a BitArray dest, and whatever mightalias reports."
    source := "base/abstractarray.jl:1042-1071 (copyto! docstring)"
    status := .proven, prop := ``CopytoPrefix, thm := some ``copytoPrefix_proven
    notes := "The BitArray branch follows _copyto_bitarray! (base/bitarray.jl:507-532) at the element level. Arrays are values, so unalias's copy has src's contents; the bounds check uses wrapping Int arithmetic for Δi and the proof shows it accepts exactly length(src) <= length(dest)." },
  { id := "abstractarrayspecs-copyto-styles", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(deststyle::IndexStyle, dest::AbstractArray, srcstyle::IndexStyle, src::AbstractArray)"]
    statement := "copyto!(deststyle, dest, srcstyle, src) satisfies the copyto!(dest, src) contract for every pair of IndexStyle arguments, whether or not they are the arrays' own styles."
    source := "base/abstractarray.jl:1042-1071 (copyto! docstring)"
    status := .proven, prop := ``CopytoStylesPrefix, thm := some ``copytoStylesPrefix_proven },
  { id := "abstractarrayspecs-copyto-iter-at", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(dest::AbstractArray, dstart::Integer, src)"]
    statement := "copyto!(dest, dstart, src) with an iterable src writes its elements to dest at consecutive linear indices from dstart, does nothing for an empty src, and throws BoundsError when they do not all lie in dest, whether or not src has a length."
    source := "base/array.jl:282-287 (copyto!(dest, doffs, src, soffs, n) docstring); base/abstractarray.jl:1042-1071"
    status := .proven, prop := ``CopytoIterAtSpec, thm := some ``copytoIterAt_spec
    notes := "Int dstart. 1.13.2 checks i:(i + length(src) - 1), which wraps for dstart near typemax(Int), and then writes out of bounds under @inbounds; master replaced it with n <= lastindex(dest) - i + 1 (#62797), so this is fixed upstream." },
  { id := "abstractarrayspecs-copyto-n", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer, n::Integer)"]
    statement := "copyto!(dest, dstart, src, sstart, n) for arrays copies n elements of src from linear index sstart on to dest from linear index dstart on; n == 0 does nothing, a negative n throws, and a range outside either array throws BoundsError; for either IndexStyle, any axes and any mightalias outcome."
    source := "base/array.jl:282-287 (copyto!(dest, doffs, src, soffs, n) docstring)"
    status := .proven, prop := ``CopytoNSpec, thm := some ``copytoN_spec
    notes := "Int arguments. 1.13.2 checks dstart+n-1 with wrapping arithmetic (master: n <= last(destinds) - dstart + 1, #62797); on 1.13.2 the Array methods of array.jl also read and write out of bounds for n or dstart near typemax(Int), which master fixed." },
  { id := "abstractarrayspecs-copyto-at", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray)"]
    statement := "copyto!(dest, dstart, src) for arrays copies all of src to dest from linear index dstart on, does nothing for an empty src, and throws BoundsError when src does not fit."
    source := "base/array.jl:282-287; base/abstractarray.jl:1042-1071 (copyto! docstrings)"
    status := .proven, prop := ``CopytoAtSpec, thm := some ``copytoAt_spec },
  { id := "abstractarrayspecs-copyto-from", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer)"]
    statement := "copyto!(dest, dstart, src, sstart) for arrays copies the elements of src from linear index sstart to the end to dest from linear index dstart on, and throws BoundsError when sstart is not a linear index of src or the elements do not fit."
    source := "base/array.jl:282-287 (copyto!(dest, doffs, src, soffs, n) docstring)"
    status := .proven, prop := ``CopytoFromSpec, thm := some ``copytoFrom_spec },
  { id := "abstractarrayspecs-copyto-block", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(B::AbstractVecOrMat{R}, ir_dest::AbstractRange{Int}, jr_dest::AbstractRange{Int}, A::AbstractVecOrMat{S}, ir_src::AbstractRange{Int}, jr_src::AbstractRange{Int}) where {R,S}"]
    statement := "copyto!(B, ir_dest, jr_dest, A, ir_src, jr_src) throws ArgumentError when the range lengths differ, BoundsError when a range leaves its axis, and otherwise performs B[ir_dest[p], jr_dest[q]] = A[ir_src[p], jr_src[q]] for all pairs in column order, for vectors and matrices of either style with any axes."
    source := "base/abstractarray.jl:1159-1181; obvious meaning of B[ir_dest, jr_dest] = A[ir_src, jr_src]"
    status := .proven, prop := ``CopytoBlockSpec, thm := some ``copytoBlock_spec
    notes := "Ranges are those whose elements are first + k*step (UnitRange, StepRange, OneTo, StepRangeLen with an Int step)." },
  { id := "abstractarrayspecs-copyto-axcheck", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto_axcheck!(dest, src)"]
    statement := "copyto_axcheck!(dest, src) makes dest hold exactly src's elements when their axes agree and throws DimensionMismatch otherwise."
    source := "base/abstractarray.jl:1184-1189"
    status := .proven, prop := ``CopytoAxcheckSpec, thm := some ``copytoAxcheck_spec },
  { id := "abstractarrayspecs-copy-bang-array", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copy!(dst::AbstractArray, src::AbstractArray)"]
    statement := "copy!(dst, src) for arrays throws ArgumentError unless dst and src have equal axes, and then makes dst hold exactly src's elements."
    source := "base/abstractarray.jl:898-918 (copy! docstring: 'dst == src should hold after the call'; 'multidimensional arrays ... must have equal axes')"
    status := .proven, prop := ``CopyBangArraySpec, thm := some ``copyBangArray_spec },
  { id := "abstractarrayspecs-copy-bang-vector", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copy!(dst::AbstractVector, src::AbstractVector)"]
    statement := "copy!(dst, src) for vectors throws unless they have the same first index, and otherwise resizes dst to length(src) if needed and makes it hold exactly src's elements, for any dst whose resize! meets the resize! contract."
    source := "base/abstractarray.jl:898-918 (copy! docstring: 'they must have equal offset'; 'dst is resized to length(src)'); base/array.jl resize! docstring"
    status := .proven, prop := ``CopyBangVectorSpec, thm := some ``copyBangVector_spec },
  { id := "abstractarrayspecs-copy", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copy(a::AbstractArray)", "copymutable(a::AbstractArray)", "similar(a::AbstractArray{T}) where {T}",
      "similar(a::AbstractArray, ::Type{T}) where {T}",
      "similar(a::AbstractArray, ::Type{T}, dims::Tuple{Union{Integer, AbstractOneTo}, Vararg{Union{Integer, AbstractOneTo}}}) where {T}",
      "similar(a::AbstractArray, ::Type{T}, dims::Dims{N}) where {T,N}", "to_shape"]
    statement := "copy(A) of an array whose axes are Base.OneTo ranges returns an Array with the same axes and the same elements in the same order, regardless of the uninitialized contents of similar(A), for either IndexStyle."
    source := "base/abstractarray.jl:1191-1209 (copymutable docstring), 772-818 (similar docstring); doc/src/manual/interfaces.md (Abstract arrays: similar)"
    status := .proven, prop := ``CopyEqual, thm := some ``copyEqual_proven
    notes := "Arrays with other axes have no Base similar method; their types must define one (interfaces.md), so they are outside this contract." },
  { id := "abstractarrayspecs-map-n", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map_n!(f::F, dest::AbstractArray, As) where F"]
    statement := "map_n!(f, dest, As) with one or more sources stores f of the k-th elements of the sources in position k of dest for every k that dest and all sources have, and leaves the rest of dest unchanged, whether or not the sources' LinearIndices equal dest's, for either IndexStyle and any axes."
    source := "base/abstractarray.jl:3562-3592 (map! docstring: 'Like map, but stores the result in destination'; example map!(+, zeros(Int, 5), 100:999, 1:3))"
    status := .proven, prop := ``MapNPrefix, thm := some ``mapNPrefix_proven },
  { id := "abstractarrayspecs-map-bang-n", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map!(f::F, dest::AbstractArray, As::AbstractArray...) where {F}"]
    statement := "map!(f, dest, As...) with one or more source arrays stores f of the k-th elements of the sources in position k of dest for every k that dest and all sources have, and leaves the rest of dest unchanged."
    source := "base/abstractarray.jl:3562-3592 (map! docstring and example)"
    status := .proven, prop := ``MapBangNPrefix, thm := some ``mapBangNPrefix_proven }
] ++ catEntries

end JuliaLean.AbstractArraySpecs
