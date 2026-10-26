import JuliaLean.Registry.Types
import JuliaLean.ArrayCov.Model
import JuliaLean.ArrayCov.Simple
import JuliaLean.ArrayCov.Construct
import JuliaLean.ArrayCov.ReshapedSimple
import JuliaLean.ArrayCov.ReinterpretSimple
import JuliaLean.ArrayCov.ReshapedShape
import JuliaLean.ArrayCov.ReinterpretCartesian
import JuliaLean.ArrayCov.ReshapeCore
import JuliaLean.ArrayCov.ReshapedIndex
import JuliaLean.ArrayCov.ReshapedPointers
import JuliaLean.ArrayCov.ReinterpretConstruct
import JuliaLean.ArrayCov.ReinterpretShape
import JuliaLean.ArrayCov.ReinterpretAccess
import JuliaLean.ArrayCov.ReinterpretPadding
import JuliaLean.ArrayCov.ArrayCore
import JuliaLean.ArrayCov.ArrayWrap
import JuliaLean.ArrayCov.ArrayFind
import JuliaLean.ArrayCov.ArrayMisc
import JuliaLean.ArrayCov.ArrayIndex
import JuliaLean.ArrayCov.ArrayPush
import JuliaLean.ArrayCov.ArrayDeleteRoutes
import JuliaLean.ArrayCov.ArrayFilterSet
import JuliaLean.ArrayCov.ArrayIndcopy
import JuliaLean.ArrayCov.ArrayCollect
import JuliaLean.ArrayCov.ArrayGrowth
import JuliaLean.MemSafety.G4.Proofs

namespace JuliaLean.ArrayCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "arraycov-array-basics", juliaFile := "base/array.jl"
    juliaFns := ["DimensionMismatch()", "vect()", "asize_from(::Array, n)",
      "allocatedinline(::Type)", "isbitsunion(::Type)", "elsize(::Type{<:Array})",
      "elsize(::Type{Union{}})", "elsize(::Type{Union{}}, args...)",
      "sizeof(::Array)", "_throw_argerror(s)"]
    statement := "The default exception and empty vector constructors return their documented empty values; array size metadata and the outlined ArgumentError helper follow their source expressions for every input."
    source := "base/array.jl:14,158,188-229,321"
    status := .proven, prop := ``ArrayBasicsCorrect, thm := some ``arrayBasicsCorrect },
  { id := "arraycov-array-copy-routes", juliaFile := "base/array.jl"
    juliaFns := ["unsetindex!(::Array, ::Integer)", "_copyto2arg!(dest, src)",
      "copyto!(::Array, ::Array)", "copyto!(::Array, ::Memory)",
      "copyto!(::Memory, ::Array)", "copyto!(::Array{T}, ::Array{T})",
      "copyto!(::Array{T}, ::Memory{T})", "copyto!(::Memory{T}, ::Array{T})"]
    statement := "The integer unset wrapper converts its index before delegation, and every two-argument copy overload delegates with the source and destination unchanged; _copyto2arg! supplies both first indices and the source length in source order."
    source := "base/array.jl:208,323-332"
    status := .proven, prop := ``ArrayCopyRoutesCorrect, thm := some ``arrayCopyRoutesCorrect },
  { id := "arraycov-array-similar", juliaFile := "base/array.jl"
    juliaFns := ["similar(::Vector)", "similar(::Matrix)", "similar(::Vector, ::Type)",
      "similar(::Matrix, ::Type)", "similar(::Array, ::Int)",
      "similar(::Array, ::Type, ::Dims)", "similar(::Array, ::Dims)",
      "similar(::Type{<:Array}, ::Dims)"]
    statement := "Each Array similar overload allocates with exactly the source element type or requested type and exactly the source or requested dimensions named by that overload."
    source := "base/array.jl:414-421"
    status := .proven, prop := ``ArraySimilarCorrect, thm := some ``arraySimilarCorrect },
  { id := "arraycov-array-fill-constructors", juliaFile := "base/array.jl"
    juliaFns := ["to_dim(::Integer)", "to_dim(::OneTo)", "fill(v, dims...)",
      "fill(v, ::Tuple)", "zeros(dims...)", "zeros(::Type, dims...)",
      "ones(dims...)", "ones(::Type, dims...)"]
    statement := "Every fill, zeros and ones overload preserves the source routing order: normalize dimensions where required, allocate or call similar, evaluate the requested zero or one value once, fill the result, and return it."
    source := "base/array.jl:482-483,583-587,631-651"
    status := .proven, prop := ``ArrayFillConstructorsCorrect,
    thm := some ``arrayFillConstructorsCorrect },
  { id := "arraycov-array-conversion-constructors", juliaFile := "base/array.jl"
    juliaFns := ["convert(::Type{<:Array}, ::AbstractArray)",
      "promote_rule(::Type{<:Array}, ::Type{<:Array})",
      "Array{T,N}(::AbstractArray{S,N})", "AbstractArray{T,N}(::AbstractArray{S,N})"]
    statement := "Array conversion returns an already matching array or invokes the requested constructor; promotion calls promote_type before el_same; conversion constructors allocate or call similar before the checked copy."
    source := "base/array.jl:657-665"
    status := .proven, prop := ``ArrayConversionConstructorsCorrect,
    thm := some ``arrayConversionConstructorsCorrect },
  { id := "arraycov-array-typed-collect", juliaFile := "base/array.jl"
    juliaFns := ["collect(::Type, itr)", "_collect(::Type, itr, ::HasLength)",
      "_collect(::Type, itr, ::HasShape)", "_collect(::Type, itr, ::SizeUnknown)",
      "_similar_for", "_similar_shape", "_array_for_inner", "_array_for"]
    statement := "Typed collection dispatches on IteratorSize, allocates from the matching length or axes path, copies sized iterators, and pushes unknown-size elements in iteration order with error propagation."
    source := "base/array.jl:684-716"
    status := .proven, prop := ``ArrayTypedCollectCorrect,
    thm := some ``arrayTypedCollectCorrect },
  { id := "arraycov-array-syntax-vect", juliaFile := "base/array.jl"
    juliaFns := ["@_safeindex", "_safeindex(ex)", "vect(X::T...)", "vect(X...)"]
    statement := "Safe-index rewriting preserves assignment, reference and recursive expression branches in source order; typed vect allocates then assigns each argument once; promoted vect computes the promoted type before constructing its typed literal."
    source := "base/array.jl:132-166,183-186"
    status := .proven, prop := ``ArraySyntaxAndVectCorrect,
    thm := some ``arraySyntaxAndVectCorrect },
  { id := "arraycov-array-storage-routes", juliaFile := "base/array.jl"
    juliaFns := ["unsetindex!(::Array, ::Int)", "elsize(::Type{Ptr})", "isassigned(::Array)",
      "unsafe_copyto!", "copyto!(dest, doffs, src, soffs, n)"]
    statement := "Scalar storage methods check bounds before touching memory; Ptr elsize follows its Any, invalid type and aligned-size branches; unsafe copies preserve byte-count multiplication and mutation; typed copy overloads delegate unchanged to _copyto_impl!."
    source := "base/array.jl:209-297"
    status := .proven, prop := ``ArrayStorageRoutesCorrect,
    thm := some ``arrayStorageRoutesCorrect },
  { id := "arraycov-array-fill-copy-literal", juliaFile := "base/array.jl"
    juliaFns := ["fill!(::AbstractArray)", "_fill!", "copy(::Array)", "_take!",
      "getindex(::Type, vals...)", "getindex(::Type{Any}, vals...)",
      "getindex(::Type{Any})", "fill!(::Union{Array{UInt8},Array{Int8}}, ::Integer)"]
    statement := "Fill converts once before traversing each index, copy allocates and copies the complete storage before restoring dimensions, _take! updates only unequal fields, typed literals allocate then assign every value through the tuple or fold path, and byte fill converts before memset."
    source := "base/array.jl:368-480"
    status := .proven, prop := ``ArrayFillCopyLiteralCorrect,
    thm := some ``arrayFillCopyLiteralCorrect },
  { id := "arraycov-array-wrap", juliaFile := "base/array.jl"
    juliaFns := ["_wrap", "invalid_wrap_err", "wrap(::Type{Array}, ::MemoryRef, dims)",
      "wrap(::Type{Array}, ::Memory, dims)", "wrap(::Type{Array}, ::MemoryRef, length)",
      "wrap(::Type{Array}, ::Memory)"]
    statement := "Safe Array wrapping converts dimensions before checking their product against the remaining MemoryRef span, constructs the array from the checked reference and normalized dimensions, and reports DimensionMismatch when storage is too short."
    source := "base/array.jl:3241-3269,3275-3279"
    status := .proven, prop := ``ArrayWrapCorrect, thm := some ``arrayWrapCorrect },
  { id := "arraycov-array-find-routing", juliaFile := "base/array.jl"
    juliaFns := ["findnext(A, start)", "findfirst(A)", "findfirst(predicate, A)",
      "findprev(A, start)", "findlast(A)", "findlast(predicate, A)"]
    statement := "Boolean find wrappers insert identity and boundary keys before delegation; pair scans test values in iteration or reverse order and return the associated first matching key; indexed wrappers call findnext or findprev with the exact first or last key."
    source := "base/array.jl:2404-2444,2523-2532,2591-2632,2716-2736"
    status := .proven, prop := ``ArrayFindRoutingCorrect,
    thm := some ``arrayFindRoutingCorrect },
  { id := "arraycov-array-range-find", juliaFile := "base/array.jl"
    juliaFns := ["findfirst(::Fix2, ::OneTo)", "findfirst(iszero, ::OneTo)",
      "findfirst(isone, ::OneTo)", "findfirst(::Fix2, ::AbstractUnitRange)",
      "findfirst(iszero, ::AbstractRange)", "findfirst(isone, ::AbstractRange)"]
    statement := "Specialized range findfirst methods check the documented bounds before key conversion, compute unit-range offsets from the first key, and construct zero or one predicates from the range element type before delegation."
    source := "base/array.jl:2534-2544,2554-2555"
    status := .proven, prop := ``ArrayRangeFindCorrect,
    thm := some ``arrayRangeFindCorrect },
  { id := "arraycov-array-findall", juliaFile := "base/array.jl"
    juliaFns := ["findall(predicate, A)", "findall(A)", "findall(::AbstractArray{Bool})",
      "findall(::Bool)", "findall(predicate, ::Number)", "findall(in, ::Number)"]
    statement := "findall filters pair values before collecting their keys, selects typed collection only for unknown generator eltype, broadcasts the specialized array predicate before finding true indices, and writes Boolean-array or scalar matches in source order."
    source := "base/array.jl:2789-2858"
    status := .proven, prop := ``ArrayFindAllCorrect,
    thm := some ``arrayFindAllCorrect },
  { id := "arraycov-array-comparison", juliaFile := "base/array.jl"
    juliaFns := ["empty!(::Vector)", "cmp(::Array{UInt8,1}, ::Array{UInt8,1})",
      "==(::BitIntegerArray, ::BitIntegerArray)"]
    statement := "empty! deletes the current length; byte comparison calls memcmp over the shorter byte length before comparing lengths; bit-integer equality rejects unequal shapes or lengths before comparing the exact storage byte count."
    source := "base/array.jl:2155-2210"
    status := .proven, prop := ``ArrayComparisonCorrect,
    thm := some ``arrayComparisonCorrect },
  { id := "arraycov-array-reverse-routes", juliaFile := "base/array.jl"
    juliaFns := ["reverse(::AbstractVector; dims)", "_reverse", "reverse!(::AbstractVector; dims)",
      "_reverse!", "reverseind", "midpoint"]
    statement := "One-dimensional reverse routes colon and integer dimensions through the source helpers and error check; reverseind uses linear-index endpoints; midpoint performs wrapping subtraction, logical shift and wrapping addition before the promoted overload delegates."
    source := "base/array.jl:2271-2289"
    status := .proven, prop := ``ArrayReverseRoutesCorrect,
    thm := some ``arrayReverseRoutesCorrect },
  { id := "arraycov-array-concat", juliaFile := "base/array.jl"
    juliaFns := ["vcat()", "hcat()", "hcat(::Vector...)", "vcat(::Vector...)", "_cat"]
    statement := "Empty concatenations return empty vectors; homogeneous hcat rejects unequal heights before row-major construction; homogeneous vcat accumulates the wrapping total before allocation and checked sequential copies; generic wrappers select dimensions one or two; _cat constructs singleton leading dimensions before reshape."
    source := "base/array.jl:2337-2368"
    status := .proven, prop := ``ArrayConcatCorrect,
    thm := some ``arrayConcatCorrect },
  { id := "arraycov-array-getindex", juliaFile := "base/array.jl"
    juliaFns := ["getindex(::Array, ::Int, ::Int, ::Int...)",
      "getindex(::Array, ::AbstractUnitRange)", "getindex(::Array, ::AbstractUnitRange{Bool})",
      "getindex(::Array, ::Colon)", "getindex(::Array, ::AbstractRange{Int})"]
    statement := "Array getindex methods check bounds before linearization or range copies, allocate outputs from source axes or length, avoid copies for empty ranges, normalize Boolean ranges before recursion, and evaluate range comprehensions in source order."
    source := "base/array.jl:974-1007"
    status := .proven, prop := ``ArrayGetindexCorrect,
    thm := some ``arrayGetindexCorrect },
  { id := "arraycov-array-setindex", juliaFile := "base/array.jl"
    juliaFns := ["setindex!(::Array, value, indices...)", "_setindex!",
      "__safe_setindex!", "setindex!(::Array, ::AbstractArray, ::AbstractVector{Int})",
      "setindex!(::Array, ::Array, ::AbstractUnitRange{Int})", "setindex!(::Array, ::Array, ::Colon)"]
    statement := "Array setindex converts before dispatch, checks bounds before memory writes, preserves the unsafe fast paths, validates shapes and unaliases both sources before scatter, and performs contiguous range or colon copies only after validation."
    source := "base/array.jl:1031-1096"
    status := .proven, prop := ``ArraySetindexCorrect,
    thm := some ``arraySetindexCorrect },
  { id := "arraycov-array-push", juliaFile := "base/array.jl"
    juliaFns := ["array_new_memory", "push!(::Vector, item)", "_push!",
      "push!(::Vector{Any}, items...)"]
    statement := "Push converts before growth for typed vectors, grows once before the safe final write, and the Any vararg specialization records the old length before one growth and sequential writes."
    source := "base/array.jl:1114,1358-1387"
    status := .proven, prop := ``ArrayPushCorrect, thm := some ``arrayPushCorrect },
  { id := "arraycov-array-append", juliaFile := "base/array.jl"
    juliaFns := ["append!(::Vector, items)", "append!(::AbstractVector, iter)",
      "push!(::AbstractVector, iter...)", "append!(::AbstractVector, iter...)", "_append!"]
    statement := "Append converts tuples before mutation, records the original count, grows before alias-aware copying, dispatches on IteratorSize, applies sizehint only for sized iterators, and pushes or appends collections in source order."
    source := "base/array.jl:1427-1452"
    status := .proven, prop := ``ArrayAppendCorrect, thm := some ``arrayAppendCorrect },
  { id := "arraycov-array-prepend", juliaFile := "base/array.jl"
    juliaFns := ["prepend!(::Vector, items)", "prepend!(::AbstractVector, iter)",
      "pushfirst!(::AbstractVector, iter...)", "prepend!(::AbstractVector, iter...)", "_prepend!"]
    statement := "Prepend converts tuples or unaliases non-self inputs before growth, reads self aliases after growth, processes multiple collections in reverse call order, and for generic iterators counts pushfirst calls before reversing only the inserted prefix."
    source := "base/array.jl:1485-1525"
    status := .proven, prop := ``ArrayPrependCorrect, thm := some ``arrayPrependCorrect },
  { id := "arraycov-array-pushfirst-insert", juliaFile := "base/array.jl"
    juliaFns := ["pushfirst!(::Vector, item)", "_pushfirst!",
      "pushfirst!(::Vector{Any}, items...)", "insert!(::Vector, index, item)", "_insert!"]
    statement := "Pushfirst and insert convert before mutation, grow the front or insertion point once, then write exactly the newly created positions in source order; Any varargs grow once and fill from index one."
    source := "base/array.jl:1777-1802,1866-1878"
    status := .proven, prop := ``ArrayPushFirstInsertCorrect,
    thm := some ``arrayPushFirstInsertCorrect },
  { id := "arraycov-array-pop-routes", juliaFile := "base/array.jl"
    juliaFns := ["pop!(::Vector)", "popat!(::Vector, index)",
      "popat!(::Vector, index, default)", "popfirst!(::Vector)"]
    statement := "Pop and popfirst reject empty vectors before reading and deleting one endpoint; popat reads before deletion and its default overload mutates only for an in-bounds index."
    source := "base/array.jl:1700-1756,1836-1843"
    status := .proven, prop := ``ArrayPopRoutesCorrect,
    thm := some ``arrayPopRoutesCorrect },
  { id := "arraycov-array-delete-routes", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds)", "push!(::Nowhere, x)",
      "_growend!(::Nowhere, n)", "_push_deleted!", "_copy_item!", "splice!(::Vector, inds)"]
    statement := "Delete wrappers normalize vector indices before delegation; the Nowhere sink ignores pushes and growth; deleted-item and compaction helpers preserve assignedness; general splice constructs its deleted accumulator before the deleting call."
    source := "base/array.jl:1945-1968,2153"
    status := .proven, prop := ``ArrayDeleteRoutesCorrect,
    thm := some ``arrayDeleteRoutesCorrect },
  { id := "arraycov-array-findin", juliaFile := "base/array.jl"
    juliaFns := ["_findin", "_sortedfindin", "findall(in, ::Array{<:Real})"]
    statement := "Hash-based findin scans pairs and appends matching keys, the generic wrapper constructs its Set before delegation, sorted findin advances exactly one source iterator according to isless or records a match, and the specialization selects that merge only after both sortedness checks."
    source := "base/array.jl:2903-2963"
    status := .proven, prop := ``ArrayFindInCorrect,
    thm := some ``arrayFindInCorrect },
  { id := "arraycov-array-filter", juliaFile := "base/array.jl"
    juliaFns := ["filter(::Function, ::Array)", "filter(::Function, ::AbstractArray)",
      "filter(f)"]
    statement := "Array filtering allocates one scratch slot per input, stores before evaluating the predicate, advances only for kept values, resizes and hints the compact result; non-linear arrays use logical indexing, and the curried overload preserves its predicate."
    source := "base/array.jl:3020-3047,3105-3107"
    status := .proven, prop := ``ArrayFilterCorrect,
    thm := some ``arrayFilterCorrect },
  { id := "arraycov-array-setlike", juliaFile := "base/array.jl"
    juliaFns := ["keepat!(::Vector, inds)", "keepat!(::Vector, mask)",
      "_unique_filter!", "_grow_filter!", "_shrink_filter!", "_grow!", "union!",
      "symdiff!", "_shrink!", "intersect!", "setdiff!", "vectorfilter",
      "intersect", "setdiff"]
    statement := "Vector set-like methods construct their stateful uniqueness predicates from the named membership and update functions, preserve filtering and iterator order, route union and symmetric difference through growth, route intersection and set difference through shrinkage, and preserve the range/vector argument order."
    source := "base/array.jl:3134-3221"
    status := .proven, prop := ``ArraySetLikeCorrect,
    thm := some ``arraySetLikeCorrect },
  { id := "arraycov-array-indcopy-range", juliaFile := "base/array.jl"
    juliaFns := ["indcopy(::Dims, ::Vector)", "indcopy(::Dims, ::Tuple)",
      "getindex(::AbstractRange, ::Integer)"]
    statement := "indcopy rejects an empty index collection, forms the wrapping product of dimensions from the final copied dimension onward, computes destination membership before source lookup for each index collection, and range scalar indexing rejects Bool before delegation."
    source := "base/array.jl:2970-2991,3224-3230"
    status := .proven, prop := ``ArrayIndcopyRangeCorrect,
    thm := some ``arrayIndcopyRangeCorrect },
  { id := "arraycov-array-collect-routes", juliaFile := "base/array.jl"
    juliaFns := ["collect(itr)", "collect(::AbstractArray)", "collect_similar",
      "_collect(::HasEltype, ...)", "_collect_indices"]
    statement := "Untyped collect obtains iterator traits before dispatch, sized collection computes shape and destination before copying, unknown-size collection pushes in iteration order, and array collection allocates from exact axes before its empty or copy branch."
    source := "base/array.jl:771-801"
    status := .proven, prop := ``ArrayCollectRoutesCorrect,
    thm := some ``arrayCollectRoutesCorrect },
  { id := "arraycov-array-iterator-type", juliaFile := "base/array.jl"
    juliaFns := ["_iterator_upper_bound", "@default_eltype"]
    statement := "Iterator upper-bound inference advances the first and subsequent states until the barrier returns a value or exhaustion throws the Nothing sentinel; default_eltype selects a Generator type function before compiler return-type inference and then promotes union components."
    source := "base/array.jl:805-831"
    status := .proven, prop := ``ArrayIteratorTypeCorrect,
    thm := some ``arrayIteratorTypeCorrect },
  { id := "arraycov-array-generator-collect", juliaFile := "base/array.jl"
    juliaFns := ["collect(::Generator)", "_collect(::EltypeUnknown, ::SizeUnknown)",
      "_collect(::EltypeUnknown, ::Union{HasLength,HasShape})"]
    statement := "Generator collection computes size and default element type first, grows unknown-size iterators, otherwise computes shape and inspects the first iteration result before empty allocation or first-value collection; unknown-eltype overloads follow the same order."
    source := "base/array.jl:833-873"
    status := .proven, prop := ``ArrayGeneratorCollectCorrect,
    thm := some ``arrayGeneratorCollectCorrect },
  { id := "arraycov-array-collect-first-widen", juliaFile := "base/array.jl"
    juliaFns := ["collect_to_with_first!", "setindex_widen_up_to"]
    statement := "First-value collection stores at the first linear index before continuing or pushes before generic growth; widening allocates at the promoted element type, copies the prefix ending before the new index, stores the widening value, and returns the new destination."
    source := "base/array.jl:875-893"
    status := .proven, prop := ``ArrayCollectFirstWidenCorrect,
    thm := some ``arrayCollectFirstWidenCorrect },
  { id := "arraycov-array-collect-loops", juliaFile := "base/array.jl"
    juliaFns := ["collect_to!", "grow_to!", "push_widen"]
    statement := "Collection loops advance iterator state once per element, store matching values and increment the index, widen and redispatch at the first mismatch, preserve empty iteration, and rebuild widened set or vector destinations before pushing the mismatching value."
    source := "base/array.jl:895-949"
    status := .proven, prop := ``ArrayCollectLoopsCorrect,
    thm := some ``arrayCollectLoopsCorrect },
  { id := "arraycov-array-growth", juliaFile := "base/array.jl"
    juliaFns := ["overallocation", "_growbeg_internal!", "_growbeg!",
      "_growend_internal!", "_growend!", "_growat!"]
    statement := "Vector growth uses wrapping overallocation arithmetic, checked length arithmetic and representation validation before choosing in-memory, centered-allocation, front, back or insertion moves; public wrappers convert and validate deltas before updating the logical length."
    source := "base/array.jl:1102-1112,1116-1275"
    status := .proven, prop := ``ArrayGrowthCorrect,
    thm := some ``arrayGrowthCorrect },
  { id := "arraycov-array-delete-resize", juliaFile := "base/array.jl"
    juliaFns := ["_deletebeg!", "_deleteend!", "_deleteat!(::Vector, index, delta)",
      "resize!(::Vector, length; first)"]
    statement := "Vector deletion converts and validates counts before unsetting storage and changing length or reference, middle deletion checks its complete interval before choosing front or tail compaction, and resize selects growth or deletion only after converted-length comparisons."
    source := "base/array.jl:1278-1327,1564-1579"
    status := .proven, prop := ``ArrayDeleteResizeCorrect,
    thm := some ``arrayDeleteResizeCorrect },
  { id := "arraycov-array-sizehint", juliaFile := "base/array.jl"
    juliaFns := ["sizehint!(::Vector, size; first, shrink)", "Core.kwcall(::typeof(sizehint!), ...)"]
    statement := "Vector sizehint converts and clamps the request before its shrink, front-growth or end-growth branch and restores logical length after reserving capacity; the keyword fallback validates both Boolean keywords and rejects extras before delegation."
    source := "base/array.jl:1617-1657"
    status := .proven, prop := ``ArraySizehintCorrect,
    thm := some ``arraySizehintCorrect },
  { id := "arraycov-reshaped-construction", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["ReshapedArray(parent, dims, mi)", "ReshapedArrayIterator(A)",
      "_rs_iterator(P, mi)", "length(::ReshapedArrayIterator)",
      "eltype(::Type{<:ReshapedArrayIterator})", "throw_dmrsa(dims, len)"]
    statement := "ReshapedArray and its iterator store the source fields in order; iterator metadata forwards to the parent iterator; the dimension-mismatch helper always throws."
    source := "base/reshapedarray.jl:10,20-24,35-39"
    status := .proven, prop := ``ReshapedConstructionCorrect,
    thm := some ``reshapedConstructionCorrect },
  { id := "arraycov-reshaped-metadata", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["size(::ReshapedArray)", "length(::ReshapedArray)",
      "similar(::ReshapedArray, ::Type, ::Dims)", "similar(::Type{<:ReshapedArray}, ::Dims)",
      "IndexStyle(::Type{<:ReshapedArrayLF})", "parent(::ReshapedArray)",
      "parentindices(::ReshapedArray)", "elsize(::Type{<:ReshapedArray})",
      "unaliascopy(::ReshapedArray)", "dataids(::ReshapedArray)", "mightalias"]
    statement := "ReshapedArray metadata returns its stored dimensions or parent metadata, similar delegates to the parent, unaliascopy copies only the parent, and alias tests forward the correct parent arguments."
    source := "base/reshapedarray.jl:253-268"
    status := .proven, prop := ``ReshapedMetadataCorrect,
    thm := some ``reshapedMetadataCorrect },
  { id := "arraycov-reshaped-simple-routes", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["setindex!(::ReshapedRange, ...)", "_rs_setindex!_err()",
      "cconvert(::Type{Ptr}, ::ReshapedArray)", "unsafe_convert(::Type{Ptr}, ::ReshapedArray)",
      "viewindexing", "compute_stride1", "_checkcontiguous",
      "merge_adjacent_dim(::Dims{0}, ::Dims{0})", "merge_adjacent_dim(::Dims{1}, ::Dims{1})"]
    statement := "Reshaped-range writes route to the dedicated error; pointer conversions route to the parent; view and contiguity specializations return their source constants or parent result; one-axis merge returns the source size and stride."
    source := "base/reshapedarray.jl:344-357,417-422,448-449"
    status := .proven, prop := ``ReshapedSimpleRoutesCorrect,
    thm := some ``reshapedSimpleRoutesCorrect },
  { id := "arraycov-reshaped-shape-wrappers", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::AbstractArray, dims...)", "reshape(::AbstractArray, ::Tuple)",
      "reshape(::AbstractVector, ::Colon)", "_any_colon", "_before_colon", "_after_colon"]
    statement := "The reshape overloads preserve tuple construction, dimension conversion and to_shape order; vector-colon overloads return the parent; colon scanners stop or recurse at the same argument and propagate missing-colon errors."
    source := "base/reshapedarray.jl:122-136,178-184"
    status := .proven, prop := ``ReshapedShapeWrappersCorrect,
    thm := some ``reshapedShapeWrappersCorrect },
  { id := "arraycov-reshaped-rank-routes", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::AbstractArray, ::Val)", "rdims_trailing", "rdims", "_reshape"]
    statement := "Val reshape preserves an equal-rank parent; rdims uses wrapping products and the exact empty, singleton, equal-rank or recursive tuple branch; simple _reshape overloads preserve or unwrap the source parent before delegation."
    source := "base/reshapedarray.jl:186-211,232-233"
    status := .proven, prop := ``ReshapedRankRoutesCorrect,
    thm := some ``reshapedRankRoutesCorrect },
  { id := "arraycov-reshape-core", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["reshape(::Array, ::Dims)", "reshape!(::Array, ::Dims)",
      "_reshape_uncolon", "_reshape_uncolon_computesize",
      "_reshape_uncolon_computesize_nonempty", "reshape(::AbstractArray, ::Val)",
      "_reshape(::AbstractVector, ::Dims{1})", "_reshape(::AbstractArray, ::Dims)",
      "_throw_dmrs", "__reshape"]
    statement := "Core reshape methods run checked dimension products before comparison or mutation, colon inference checks zero products and remainders in source order, generic reshape enforces length equality before construction, and each __reshape specialization stores the source parent and requested dimensions with the source multiplier tuple."
    source := "base/reshapedarray.jl:43-62,138-177,187-189,214-251"
    status := .proven, prop := ``ReshapeCoreCorrect, thm := some ``reshapeCoreCorrect },
  { id := "arraycov-reshaped-index-math", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["ind2sub_rs", "_ind2sub_rs", "offset_if_vec"]
    statement := "Reshaped index conversion subtracts one before recursive division, performs each quotient and remainder before recurring on the tails, restores axis starts, and applies the one-axis offset with wrapping Int arithmetic."
    source := "base/reshapedarray.jl:270-278"
    status := .proven, prop := ``ReshapedIndexMathCorrect,
    thm := some ``reshapedIndexMathCorrect },
  { id := "arraycov-reshaped-access", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["isassigned(::ReshapedArray, ...)", "getindex(::ReshapedArray, ...)",
      "_unsafe_getindex", "_unsafe_getindex_rs", "setindex!(::ReshapedArray, ...)",
      "_unsafe_setindex!"]
    statement := "Every reshaped access checks bounds before use, computes parent axes and the source linear index in source order, converts that index to parent subscripts, and reads or writes exactly those parent positions; linear methods translate first indices directly."
    source := "base/reshapedarray.jl:280-340"
    status := .proven, prop := ``ReshapedAccessCorrect,
    thm := some ``reshapedAccessCorrect },
  { id := "arraycov-reshaped-pointer-routes", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["compute_offset1", "substrides", "unsafe_convert(::Type{Ptr}, ::SubArray)",
      "_offset_cconvert", "unsafe_convert(::Type{Ptr}, ::OffsetCConvert)",
      "cconvert(::Type{Ptr}, ::SubArray)"]
    statement := "Reshaped pointer routes compute wrapping byte offsets after the same contiguity branch, preserve nested offsets, convert the parent before adding its offset, and prepend the reshaped first stride before recurring on trailing indices."
    source := "base/reshapedarray.jl:358-415"
    status := .proven, prop := ``ReshapedPointerRoutesCorrect,
    thm := some ``reshapedPointerRoutesCorrect },
  { id := "arraycov-reshaped-strides", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["strides(::ReshapedArray)", "_reshaped_strides", "merge_adjacent_dim"]
    statement := "Reshaped stride calculation takes the contiguous fast path first, merges adjacent parent dimensions with wrapping products, checks the terminal merged size, and recursively emits each reshaped stride in source order or throws for a non-strided input."
    source := "base/reshapedarray.jl:424-464"
    status := .proven, prop := ``ReshapedStridesCorrect,
    thm := some ``reshapedStridesCorrect },
  { id := "arraycov-reshaped-delegates", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["map(f, ::ReshapedArray)", "iterate(::ReshapedArray)",
      "iterate(::ReshapedArray, state)", "mapfoldl_impl", "mapfoldr_impl", "in"]
    statement := "Map reshapes the mapped parent to the stored dimensions, while iteration, folds and membership delegate to the parent with every argument preserved."
    source := "base/reshapedarray.jl:466-474"
    status := .proven, prop := ``ReshapedDelegatesCorrect,
    thm := some ``reshapedDelegatesCorrect },
  { id := "arraycov-reinterpret-simple-construction", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["reinterpret(::Type{T}, ::AbstractArray{T})",
      "reinterpret(reshape, ::Type{T}, ::AbstractArray{T})",
      "reinterpret(::Type, ::NonReshapedReinterpretArray)",
      "reinterpret(reshape, ::Type, ::ReshapedReinterpretArray)", "strides", "_checkcontiguous", "similar"]
    statement := "Same-type reinterpret returns its input, nested reinterpret delegates to the parent with the reshape mode preserved, and the simple strides, contiguity and similar methods call their source helpers with the original arguments."
    source := "base/reinterpretarray.jl:104,145,190-204,229-232"
    status := .proven, prop := ``ReinterpretSimpleConstructionCorrect,
    thm := some ``reinterpretSimpleConstructionCorrect },
  { id := "arraycov-reinterpret-error-helpers", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["throwbits", "throwsize0", "throwsingleton", "throwbitpadding",
      "thrownonint", "throwaxes1", "throwintmult", "throwsize1", "throwfromsingleton"]
    statement := "Every outlined reinterpret validation helper throws the ArgumentError category belonging to the exact failed bits, padding, dimensionality, multiplicity, singleton or first-axis check."
    source := "base/reinterpretarray.jl:14-31,74-84,108-123"
    status := .proven, prop := ``ReinterpretErrorHelpersCorrect,
    thm := some ``reinterpretErrorHelpersCorrect },
  { id := "arraycov-reinterpret-constructors", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["reinterpret(::Type, ::AbstractArray)",
      "reinterpret(reshape, ::Type, ::AbstractArray)"]
    statement := "Both reinterpret constructors perform bits and bit-padding checks first, then the exact size, singleton, divisibility and first-axis branches, compute readable and writable in opposite subpadding directions, and construct a view over the original parent with the selected rank and reshape flag."
    source := "base/reinterpretarray.jl:73-103,107-144"
    status := .proven, prop := ``ReinterpretConstructorsCorrect,
    thm := some ``reinterpretConstructorsCorrect },
  { id := "arraycov-reinterpret-stride-checks", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["stride", "check_readable", "check_writable",
      "IndexStyle(::Type{<:NonReshapedReinterpretArray})"]
    statement := "Stride chooses the stored stride or length after the dimension comparison; readability and writability short-circuit their cached flag before recomputing subpadding; non-reshaped IndexStyle preserves only a linear parent style."
    source := "base/reinterpretarray.jl:205-206,234-261"
    status := .proven, prop := ``ReinterpretStridesAndChecksCorrect,
    thm := some ``reinterpretStridesAndChecksCorrect },
  { id := "arraycov-reinterpret-stride-calculation", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["strides(::ReinterpretArray)", "_checked_strides",
      "IndexStyle(::Type{<:ReshapedReinterpretArray})"]
    statement := "Reinterpret strides take the contiguous and equal-size fast paths first, convert parent strides to bytes before exact division, reject nonintegral divisions or a noncontiguous first dimension, and choose static Cartesian style only for a smaller target over a linear parent."
    source := "base/reinterpretarray.jl:208-227,263-269"
    status := .proven, prop := ``ReinterpretStrideCalculationCorrect,
    thm := some ``reinterpretStrideCalculationCorrect },
  { id := "arraycov-reinterpret-shape", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["size(::ReinterpretArray)", "axes(::ReinterpretArray)", "elsize",
      "getindex(::NonReshapedReinterpretArray{T,0})", "check_ptr_indexable(::ReinterpretArray)"]
    statement := "Reinterpret size and axes scale, add or remove the first dimension with wrapping Int arithmetic while preserving trailing dimensions; elsize selects parent or target size; scalar zero-dimensional access and pointer-indexability take their exact source branches."
    source := "base/reinterpretarray.jl:371-421"
    status := .proven, prop := ``ReinterpretShapeCorrect,
    thm := some ``reinterpretShapeCorrect },
  { id := "arraycov-reinterpret-get-routes", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["getindex(::ReinterpretArray, ...)", "_getindex_ptr",
      "_is_scalar_reinterpret_applicable", "_getindex_ra(::ReshapedReinterpretArray)"]
    statement := "Reinterpret reads check readability first, select pointer or array assembly in source order, preserve linear and Cartesian index conversion, compute pointer offsets with wrapping Int arithmetic, and take singleton, scalar, larger, equal or smaller element-size branches after the documented bounds check."
    source := "base/reinterpretarray.jl:433-468,524-567"
    status := .proven, prop := ``ReinterpretGetRoutesCorrect,
    thm := some ``reinterpretGetRoutesCorrect },
  { id := "arraycov-reinterpret-set-routes", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["setindex!(::ReinterpretArray, ...)", "_setindex_ptr!",
      "_setindex_ra!(::ReshapedReinterpretArray)"]
    statement := "Reinterpret writes convert values and check writability in source order, select pointer or array mutation after index conversion, preserve parent bytes through the selected write callback, and return the original view after successful pointer or singleton writes."
    source := "base/reinterpretarray.jl:569-614,685-731"
    status := .proven, prop := ``ReinterpretSetRoutesCorrect,
    thm := some ``reinterpretSetRoutesCorrect },
  { id := "arraycov-reinterpret-padding-map", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["showerror(::PaddingError)", "non_padding_bytes",
      "fill_nonpadding_bytes!", "array_subpadding", "struct_subpadding",
      "packedsize", "ispacked", "has_bit_padding"]
    statement := "Padding maps reject bit padding, mark primitive value bytes or recurse through fields at their offsets, cycle source and target byte maps until both wrap, and derive structural compatibility and packed sizes from those exact maps."
    source := "base/reinterpretarray.jl:738-837"
    status := .proven, prop := ``ReinterpretPaddingMapCorrect,
    thm := some ``reinterpretPaddingMapCorrect },
  { id := "arraycov-reinterpret-packed-copies", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_copytopacked!", "_copyfrompacked!"]
    statement := "Packed copies handle primitive bytes directly and otherwise traverse fields in order, using field offsets and packed sizes while recursively packing or unpacking nested padded fields."
    source := "base/reinterpretarray.jl:839-877"
    status := .proven, prop := ``ReinterpretPackedCopiesCorrect,
    thm := some ``reinterpretPackedCopiesCorrect },
  { id := "arraycov-reinterpret-scalar-padding", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_reinterpret", "_reinterpret_padding", "String(::ReinterpretArray{UInt8})"]
    statement := "Scalar reinterpret checks bits, bit padding and packed-size equality before copying or padding conversion; padding conversion selects pack, unpack or intermediate packed storage in source order; String returns empty before readability checking and otherwise copies the bytes."
    source := "base/reinterpretarray.jl:879-939"
    status := .proven, prop := ``ReinterpretScalarPaddingCorrect,
    thm := some ``reinterpretScalarPaddingCorrect },
  { id := "arraycov-reinterpret-mapreduce-bounds", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_mapreduce(::IndexSCartesian2)", "mapreduce_impl(::SCartesianIndex2)"]
    statement := "The sequential and pairwise mapreduce branches visit only the K by n indices returned by eachindex."
    source := "base/reinterpretarray.jl:943-982"
    status := .proven, prop := ``JuliaLean.MemSafety.G4.ReinterpretMapreduceInBounds,
    thm := some ``JuliaLean.MemSafety.G4.reinterpretMapreduceInBounds },
  { id := "arraycov-reinterpret-totuple-bounds", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["_totuple(::Type{All32}, ::Union{Array,Memory})"]
    statement := "After the length check, the N+32 element view reinterprets to one tuple and index one is valid."
    source := "base/reinterpretarray.jl:987-996"
    status := .proven, prop := ``JuliaLean.MemSafety.G4.ReinterpretTupleInBounds,
    thm := some ``JuliaLean.MemSafety.G4.reinterpretTupleInBounds },
  { id := "arraycov-reinterpret-cartesian-basics", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["IndexStyle(::IndexSCartesian2, ::IndexSCartesian2)",
      "to_index(::SCartesianIndex2)", "nextind", "prevind", "SCartesianIndices2",
      "eachindex(::IndexSCartesian2, ::ReshapedReinterpretArray)", "size(::SCartesianIndices2)",
      "axes(::SCartesianIndices2)", "first(::SCartesianIndices2)", "last(::SCartesianIndices2)",
      "SimdLoop.simd_outer_range", "SimdLoop.simd_inner_length", "SimdLoop.simd_index",
      "_maybe_reshape", "eachindex(::IndexSCartesian2, ::AbstractArray)"]
    statement := "The static Cartesian helpers preserve their K parameter, perform the source wrapping index arithmetic and assertion, construct size and axes from the stored range, and forward reshape or eachindex calls with the source style."
    source := "base/reinterpretarray.jl:270-299,324-331,362"
    status := .proven, prop := ``ReinterpretCartesianBasicsCorrect,
    thm := some ``reinterpretCartesianBasicsCorrect },
  { id := "arraycov-reinterpret-cartesian-iteration", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["eachindex(::IndexSCartesian2, arrays...)",
      "getindex(::SCartesianIndices2, i, j)", "iterate(::SCartesianIndices2)",
      "iterate(::SCartesianIndices2, state)", "_getindex(::IndexSCartesian2, ...)",
      "_setindex!(::IndexSCartesian2, ...)", "_scartesian2_trailing"]
    statement := "Static Cartesian eachindex checks every companion iterator before returning; indexing checks bounds before range access; iteration follows the inner-index then parent-range state machine; fallbacks and trailing-index conversion preserve source argument order and wrapping arithmetic."
    source := "base/reinterpretarray.jl:288-360"
    status := .proven, prop := ``ReinterpretCartesianIterationCorrect,
    thm := some ``reinterpretCartesianIterationCorrect },
  { id := "arraycov-reinterpret-metadata-routes", juliaFile := "base/reinterpretarray.jl"
    juliaFns := ["parent(::ReinterpretArray)", "dataids(::ReinterpretArray)", "unaliascopy",
      "size(::NonReshapedReinterpretArray{T,0})", "axes(::NonReshapedReinterpretArray{T,0})",
      "has_offset_axes", "cconvert", "unsafe_convert", "check_ptr_indexable",
      "getindex(::ReshapedReinterpretArray{T,0})", "isassigned", "_isassigned_ra",
      "setindex!(::ReshapedReinterpretArray{T,0}, v)"]
    statement := "Metadata and conversion wrappers forward to the parent in source order; zero-dimensional size and axes are empty; pointer-indexability constants and isassigned short-circuit branches match the source; zero-dimensional get and set use firstindex."
    source := "base/reinterpretarray.jl:366-369,382,396-398,407-408,422-431,577"
    status := .proven, prop := ``ReinterpretMetadataRoutesCorrect,
    thm := some ``reinterpretMetadataRoutesCorrect },
  { id := "arraycov-wrap-memory-unsigned", juliaFile := "base/array.jl"
    juliaFns := ["wrap(::Type{Array}, m::Memory{T}, l::Integer) where {T}"]
    statement := "wrap(Array, memory, n) accepts every Int-representable Integer length that fits in the supplied Memory, as its adjacent MemoryRef overload does."
    source := "wrap docstring at base/array.jl:3232-3237 and Integer method signature at lines 3270-3273"
    status := .refuted, prop := ``WrapMemoryIntegerSpec, thm := some ``wrapMemoryIntegerSpec_refuted
    issue := "none found (queries: wrap Memory UInt MethodError; _wrap MemoryRef Tuple UInt; Base.wrap unsigned length)"
    notes := "For Memory{Int}(undef, 3), UInt(2) is converted into dims but the source passes (l,) to the Int-tuple-only _wrap method. Release and nightly throw MethodError; the MemoryRef overload returns a size-(2,) Array." },
  { id := "arraycov-reshaped-iterator-exhaustion", juliaFile := "base/reshapedarray.jl"
    juliaFns := ["iterate(::ReshapedArrayIterator, i...)"]
    statement := "A finite ReshapedArrayIterator returns nothing at normal exhaustion, as required by the iteration protocol."
    source := "iteration protocol invariant; fast iterator implementation at base/reshapedarray.jl:15-36"
    status := .refuted, prop := ``ReshapedIteratorProtocol, thm := some ``reshapedIteratorProtocol_refuted
    issue := "none found (queries: ReshapedArrayIterator iterate Nothing; ReshapedArrayIterator collect MethodError; reshape iterator exhaustion)"
    notes := "The method destructures iterate(R.iter, i...) before testing for nothing. collect of a two-element iterator throws MethodError at exhaustion on release and nightly." },
  { id := "arraycov-indexin-isequal", juliaFile := "base/array.jl"
    juliaFns := ["indexin(a, b::AbstractArray)"]
    statement := "indexin returns a first index exactly when each value from a is a member of b under collection-membership equality."
    source := "indexin docstring at base/array.jl:2861-2868: first index in b for each value in a that is a member of b"
    status := .refuted, prop := ``IndexinMembershipSpec, thm := some ``indexinMembershipSpec_refuted
    issue := "none found (queries: indexin isequal; indexin NaN signed zero; indexin -0.0; indexin equality Dict; indexin membership)"
    notes := "The Dict at lines 2892-2900 uses isequal. Thus indexin([-0.0], [0.0]) returns [nothing] while membership is true, and indexin([NaN], [NaN]) returns [1] while membership is false, on release and nightly." }
]

end JuliaLean.ArrayCov
