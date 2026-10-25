import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Multidim.Model
import JuliaLean.Multidim.Props
import JuliaLean.Multidim.Refutations
import JuliaLean.Multidim.ProofsIter
import JuliaLean.Multidim.ProofsCirc
import JuliaLean.Multidim.ProofsCirccopy
import JuliaLean.Multidim.ProofsSmall

namespace JuliaLean.Multidim

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "multidim-cartesian-iterate", juliaFile := "base/multidimensional.jl"
    juliaFns := ["iterate(iter::CartesianIndices)", "iterate(iter::CartesianIndices, state)", "__inc"]
    statement := "Iterating CartesianIndices of any representable OrdinalRange{Int,Int} components (including empty, negative-step and typemin/typemax-adjacent ranges) visits the column-major product of the ranges once each, in order, then stops."
    source := "base/multidimensional.jl:212-226 (CartesianIndices docstring: equivalent to the nested loops, first index fastest)"
    status := .proven, prop := ``CartesianIterOrder, thm := some ``cartesianIterOrder },
  { id := "multidim-cartesian-reverse-iterate", juliaFile := "base/multidimensional.jl"
    juliaFns := ["iterate(r::Reverse{<:CartesianIndices})", "iterate(r::Reverse{<:CartesianIndices}, state)", "__dec"]
    statement := "Iterators.reverse of CartesianIndices visits exactly the reverse of the forward order, for every representable component ranges."
    source := "invariant: Iterators.reverse(itr) iterates itr backwards (base/iterators.jl, Iterators.reverse docstring)"
    status := .proven, prop := ``CartesianRevOrder, thm := some ``cartesianRevOrder },
  { id := "multidim-findfirst-nonempty", juliaFile := "base/array.jl"
    juliaFns := ["findfirst(testf::Function, A::AbstractArray)", "findnext(testf::Function, A, start)", "nextind(::AbstractArray, ::CartesianIndex)"]
    statement := "For an array with no empty dimension, findfirst(f, A) returns the first CartesianIndex in column-major order where f holds, or nothing."
    source := "base/array.jl:2488-2492 (findfirst docstring)"
    status := .proven, prop := ``FindfirstNonempty, thm := some ``findfirstNonempty },
  { id := "multidim-cartesian-isless", juliaFile := "base/multidimensional.jl"
    juliaFns := ["isless(::CartesianIndex, ::CartesianIndex)"]
    statement := "isless on CartesianIndex{N} is a strict total order (irreflexive, transitive, trichotomous with ==), comparing the last coordinate first."
    source := "base/multidimensional.jl:142; invariant: isless is a total order (isless docstring, base/operators.jl)"
    status := .proven, prop := ``CartesianIslessOrder, thm := some ``cartesianIslessOrder },
  { id := "multidim-reverse-dims-check", juliaFile := "base/multidimensional.jl"
    juliaFns := ["_reverse(iter::CartesianIndices, dims::Tuple{Vararg{Integer}})"]
    statement := "reverse(R::CartesianIndices; dims) accepts exactly the dims tuples whose entries are distinct dimensions in 1:ndims(R), and throws ArgumentError otherwise."
    source := "invariant: same dims rule as reverse(A::AbstractArray; dims) (base/arraymath.jl); multidimensional.jl:558-562"
    status := .proven, prop := ``ReverseDimsCheck, thm := some ``reverseDimsCheck },
  { id := "multidim-circshift-formula", juliaFile := "base/multidimensional.jl"
    juliaFns := ["circshift(a::AbstractArray, shiftamt)", "circshift!(dest, src, shiftamt)", "_circshift!", "copyto!(dest, Rdest::CartesianIndices, src, Rsrc::CartesianIndices)"]
    statement := "For an Array of any size and integer shifts (of any Integer type, any magnitude, at most ndims(A) of them), circshift(A, s)[J] == A[mod.(J .- 1 .- s, size(A)) .+ 1], with missing shifts zero."
    source := "base/abstractarraymath.jl:339-345 (circshift docstring: rotate the data in each dimension)"
    status := .proven, prop := ``CircshiftFormula, thm := some ``circshiftFormula },
  { id := "multidim-circcopy-nonempty", juliaFile := "base/multidimensional.jl"
    juliaFns := ["circcopy!(dest, src)", "_circcopy!"]
    statement := "For nonempty arrays of the same size with arbitrary axes, circcopy!(dest, src) sets dest[J] = src[K] where K is congruent to J modulo the size and lies in the axes of src."
    source := "base/multidimensional.jl:1302-1309 (circcopy! docstring: indexing each dimension modulo its length)"
    status := .proven, prop := ``CirccopyNonempty, thm := some ``circcopyNonempty },
  { id := "multidim-cat-same-ndims", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size_shape", "_cshp", "cat(A...; dims)"]
    statement := "For arrays with the same number of dimensions M >= max(dims), the cat result shape sums the sizes along the concatenated dimensions and is the common size elsewhere; any disagreement along another dimension is a DimensionMismatch."
    source := "base/abstractarray.jl:2061-2066 (cat docstring)"
    status := .proven, prop := ``CatSameNdims, thm := some ``catSameNdims },
  { id := "multidim-repeat-size", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "repeat(A::AbstractArray, counts...)", "_RepeatInnerOuter.check", "_RepeatInnerOuter.resolve", "repeat_inner", "repeat_outer"]
    statement := "size(repeat(A; inner, outer)) == size(A) .* inner .* outer after padding all three with ones to a common length; negative counts, fewer inner counts than ndims(A), or fewer outer counts when inner is given, throw ArgumentError."
    source := "base/abstractarraymath.jl:449-456 (repeat docstring) and the checks at lines 526-552"
    status := .proven, prop := ``RepeatShape, thm := some ``repeatShape },
  { id := "multidim-diff-size", juliaFile := "base/multidimensional.jl"
    juliaFns := ["diff(a::AbstractArray; dims::Integer)"]
    statement := "diff(A; dims) has the size of A with size(A, dims) reduced by one (not below zero), and throws ArgumentError for dims outside 1:ndims(A)."
    source := "base/multidimensional.jl:1083-1090 (diff docstring: finite difference along dims)"
    status := .proven, prop := ``DiffSize, thm := some ``diffSize_spec },
  { id := "multidim-selectdim-in-range", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)"]
    statement := "For 1 <= d <= ndims(A) and a one-dimensional index i, selectdim(A, d, i) has the size of view(A, :, ..., i, ..., :) or throws the same exception."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring)"
    status := .proven, prop := ``SelectdimInRange, thm := some ``selectdimInRange },
  { id := "multidim-findfirst-empty-matrix", juliaFile := "base/array.jl"
    juliaFns := ["findfirst(A::AbstractArray)", "findfirst(testf::Function, A::AbstractArray)", "findlast(A::AbstractArray)", "findnext(testf::Function, A, start)", "findprev(testf::Function, A, start)"]
    statement := "findfirst(f, A) on a multidimensional array returns the first CartesianIndex (column-major) where f holds, or nothing; it never throws."
    source := "base/array.jl:2488-2492 (findfirst docstring: \"Return nothing if there is no such element\")"
    status := .refuted, prop := ``FindfirstCartesian, thm := some ``findfirstCartesian_refuted
    issue := "#36938 (open, findnext on degenerate arrays; related: #40120)"
    notes := "For a 0x3 array, first(keys(A)) = CartesianIndex(1, 1) and last(keys(A)) = CartesianIndex(0, 3); the generic findnext (array.jl:2475-2486) returns early only if i > l, but CartesianIndex isless compares the last coordinate first, so it reads A[1, 1] and throws BoundsError. findlast/findprev mirror it (A[0, 3]). Arrays whose empty dimension is the last one are fine. Same on 1.13.2." },
  { id := "multidim-selectdim-cartesian-oob", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "Every position addressed by the view selectdim(A, d, i) lies inside A."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring: a view equivalent to view(A, :, ..., i, ...)); invariant: views are bounds-checked"
    status := .refuted, prop := ``SelectdimInBounds, thm := some ``selectdimInBounds_refuted
    issue := "#64175 (opened 2026-10-25 from this write-up)"
    notes := "selectdim builds _setindex(i, d, map(Slice, axes(A))...) (abstractarraymath.jl:327), keeping ndims(A) entries. A CartesianIndex{K} with K > 1 consumes K dimensions, so the remaining Slices land on dimensions past ndims(A); checkindex accepts any Slice unchecked (abstractarray.jl:755). selectdim(B, 1, CartesianIndex(2, 2)) for a 2x2 B is view(B, CartesianIndex(2, 2), Slice(OneTo(2))), whose second element is B[2, 2, 2]; reading returns garbage. Same on 1.13.2." },
  { id := "multidim-selectdim-trailing", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "selectdim(A, d, i) equals view(A, :, ..., :, i, :, ..., :) with i in position d (same size or same exception) for every d >= 1 and one-dimensional index i."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring: \"Equivalent to view(A,:,:,...,i,:,:,...) where i is in position d\")"
    status := .refuted, prop := ``SelectdimViewAgrees, thm := some ``selectdimViewAgrees_refuted
    issue := "none found (related: #51692; queries: selectdim, selectdim dimension, selectdim BoundsError, selectdim view, prs: selectdim)"
    notes := "For d > ndims(A), _selectdim (abstractarraymath.jl:331) admits only i == 1 and then views all of A without the trailing singleton dimensions: selectdim(A, 3, 1:1) throws BoundsError while view(A, :, :, 1:1) is 2x3x1; selectdim(A, 4, 1) is 2x3 while view(A, :, :, :, 1) is 2x3x1; selectdim(A, 5, true) succeeds while view rejects Bool. For 1 <= d <= ndims(A) the equivalence holds (entry multidim-selectdim-in-range). Same on 1.13.2." },
  { id := "multidim-cat-scalar-shape", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat(A...; dims)", "vcat", "hcat", "cat_size_shape", "_cshp", "__cat_offset1!"]
    statement := "Along every dimension not in dims, every argument of a successful cat has the size of the result (a scalar counts as size 1)."
    source := "base/abstractarray.jl:2061-2066 (cat docstring: \"Along other dimensions, all input arrays should have the same size\")"
    status := .refuted, prop := ``CatShapeChecked, thm := some ``catShapeChecked_refuted
    issue := "#38019 (open; also #48468, closed as duplicate)"
    notes := "_cshp (abstractarray.jl:1873, 1875-1876) does not check the extra dimensions of a later argument, nor a dimension that a later argument lacks, so a scalar is broadcast by fill! (line 1941): vcat(1, [2 3]) == [1 1; 2 3], cat([1 2], 3; dims=3) == [1 2;;; 3 3], and cat(Int[], [1 2; 3 4]; dims=1) == [1 2; 3 4], while the same arguments as arrays or in the other order throw DimensionMismatch. Same on 1.13.2." },
  { id := "multidim-hvcat-row-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvcat(rows::Tuple{Vararg{Int}}, xs::T...) where T<:Number", "typed_hvcat(::Type{T}, rows, xs::Number...)"]
    statement := "hvcat(rows, xs...) with numbers of a single type throws the same exception type as typed_hvcat for numbers of mixed types."
    source := "invariant: the specialised method (abstractarray.jl:2253-2272) agrees with typed_hvcat (abstractarray.jl:2279-2290)"
    status := .refuted, prop := ``HvcatNumbersAgree, thm := some ``hvcatNumbersAgree_refuted
    issue := "none found (queries: hvcat ArgumentError DimensionMismatch, hvcat argument count, prs: hvcat)"
    notes := "hvcat((2, 1), 1, 2, 3) throws ArgumentError (count check against rows[1] columns first, line 2258) while hvcat((2, 1), 1, 2.0, 3) and 1x1 matrices throw DimensionMismatch (row lengths first). Same on 1.13.2." },
  { id := "multidim-hvcat-zero-columns", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvcat(nbc::Int, as...)"]
    statement := "hvcat(nbc, values...) with nbc <= 0 and at least one value throws ArgumentError."
    source := "invariant: invalid arguments raise ArgumentError, as abstractarray.jl:2200-2201 does for counts that do not divide the number of values"
    status := .refuted, prop := ``HvcatColumnsError, thm := some ``hvcatColumnsError_refuted
    issue := "none found (queries: hvcat DivideError, hvcat zero, prs: hvcat)"
    notes := "mod(n, nbc) with nbc == 0 throws DivideError (abstractarray.jl:2200); negative nbc gives ArgumentError. Same on 1.13.2." },
  { id := "multidim-circcopy-empty", juliaFile := "base/multidimensional.jl"
    juliaFns := ["circcopy!(dest, src)", "_circcopy!"]
    statement := "circcopy!(dest, src) succeeds whenever src and dest have the same size."
    source := "base/multidimensional.jl:1302-1309 (circcopy! docstring: same size, possibly offset indices)"
    status := .refuted, prop := ``CirccopyCorrect, thm := some ``circcopyCorrect_refuted
    issue := "none found (related: #41402; queries: circcopy!, circcopy empty, circcopy DivideError, prs: circcopy)"
    notes := "With a zero-length dimension and a nonzero axis offset in some dimension, _circcopy! computes mod(first(inds1) - first(indd1), 0) (multidimensional.jl:1353) and throws DivideError; circshift! returns early for empty arrays (line 1261). Same on 1.13.2." },
  { id := "multidim-copyto-empty-size", juliaFile := "base/multidimensional.jl"
    juliaFns := ["copyto!(dest::AbstractArray, Rdest::CartesianIndices, src::AbstractArray, Rsrc::CartesianIndices)"]
    statement := "copyto!(dest, Rdest, src, Rsrc) throws ArgumentError whenever size(Rdest) != size(Rsrc)."
    source := "base/multidimensional.jl:1218-1222 (docstring: \"The sizes of the two regions must match\")"
    status := .refuted, prop := ``CopytoSizeChecked, thm := some ``copytoSizeChecked_refuted
    issue := "none found (related: #45430; queries: copyto! CartesianIndices, copyto! CartesianIndices empty, copyto CartesianIndices size, CartesianIndices ==, prs: copyto CartesianIndices)"
    notes := "isempty(Rdest) && return dest (multidimensional.jl:1192) precedes the size check (1193-1195). Same on 1.13.2." },
  { id := "multidim-cartesianindices-length-overflow", juliaFile := "base/essentials.jl"
    juliaFns := ["length(t::AbstractArray)", "isempty(a::AbstractArray)", "size(iter::CartesianIndices)", "getindex(::CartesianIndices, ::Int)"]
    statement := "isempty(R) for a CartesianIndices is true exactly when one of its component ranges is empty."
    source := "isempty docstring (base/essentials.jl: \"Determine whether a collection is empty (has no elements)\"); length docstring (base/abstractarray.jl:305-308: the number of elements)"
    status := .refuted, prop := ``CartesianIsEmpty, thm := some ``cartesianIsEmpty_refuted
    issue := "none found (queries: CartesianIndices (titles scanned), CartesianIndices length overflow, CartesianIndices overflow, isempty CartesianIndices, length overflow prod size, length of array overflows)"
    notes := "length(t::AbstractArray) = prod(size(t)) (essentials.jl:13) multiplies in wrapping Int: length(CartesianIndices((2^32, 2^32))) == 0, so isempty is true while iterate returns CartesianIndex(1, 1), and linear indexing R[2] throws BoundsError (checked against 1:length) although R[2, 1] works; length(CartesianIndices((typemax(Int), 2))) == -2. Same on 1.13.2." },
  { id := "multidim-cartesianindices-empty-eq", juliaFile := "base/multidimensional.jl"
    juliaFns := ["==(a::CartesianIndices{N}, b::CartesianIndices{N})"]
    statement := "a == b for CartesianIndices agrees with == on the arrays they represent (equal size and equal elements)."
    source := "invariant: == on AbstractArrays compares axes and elements; isequal and == agree for integer elements"
    status := .refuted, prop := ``CartesianEqArrays, thm := some ``cartesianEqArrays_refuted
    issue := "none found (queries: CartesianIndices equality, CartesianIndices ==, CartesianIndices empty equal, CartesianIndices isequal, prs: CartesianIndices ==)"
    notes := "== compares the component ranges (multidimensional.jl:382-383): CartesianIndices((1:0, 1:2)) == CartesianIndices((1:0, 3:4)) is false although both are empty 0x2 arrays and isequal is true. Same on 1.13.2." }
]

end JuliaLean.Multidim
