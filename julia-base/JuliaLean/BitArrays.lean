import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.BitArrays.Chunks
import JuliaLean.BitArrays.Vector
import JuliaLean.BitArrays.Reference
import JuliaLean.BitArrays.BitSet
import JuliaLean.BitArrays.Properties
import JuliaLean.BitArrays.Refutations
import JuliaLean.BitArrays.ScalarProof
import JuliaLean.BitArrays.BitSetProof
import JuliaLean.BitArrays.MapProof
import JuliaLean.BitArrays.ReverseProof
import JuliaLean.BitArrays.FindProof
import JuliaLean.BitArrays.CopyProof
import JuliaLean.BitArrays.RangeProof

namespace JuliaLean.BitArrays

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "bitarrays-scalar-index", juliaFile := "base/bitarray.jl"
    juliaFns := ["getindex(::BitArray, ::Int)", "setindex!(::BitArray, x, ::Int)"]
    statement := "B[i] and B[i] = x agree with Vector{Bool} for every Int i (BoundsError outside 1:length(B)) and keep the zero padding of the last chunk."
    source := "invariant: BitVector behaves as Vector{Bool} (BitArray docstring, base/bitarray.jl:7-23); unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``ScalarIndexAgrees, thm := some ``scalarIndexAgrees },
  { id := "bitarrays-deque", juliaFile := "base/bitarray.jl"
    juliaFns := ["push!(::BitVector, x)", "pop!(::BitVector)", "pushfirst!(::BitVector, x)", "popfirst!(::BitVector)"]
    statement := "push!, pop!, pushfirst! and popfirst! agree with Vector{Bool} (ArgumentError when popping an empty vector) and keep the chunk invariant, whatever the contents of newly allocated chunks."
    source := "invariant: BitVector behaves as Vector{Bool}; unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``DequeAgrees, thm := some ``dequeAgrees },
  { id := "bitarrays-insert-deleteat", juliaFile := "base/bitarray.jl"
    juliaFns := ["insert!(::BitVector, i, x)", "deleteat!(::BitVector, i::Integer)"]
    statement := "insert!(B, i, x) and deleteat!(B, i) agree with Vector{Bool} for every Int i and keep the chunk invariant."
    source := "invariant: BitVector behaves as Vector{Bool}; insert!/deleteat! docstrings (base/array.jl)", status := .proven
    prop := ``InsertDeleteAgrees, thm := some ``insertDeleteAgrees },
  { id := "bitarrays-deleteat-empty-range", juliaFile := "base/bitarray.jl"
    juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "splice!(::BitVector, ::AbstractUnitRange{Int}, ins)"]
    statement := "deleteat!(B, r) agrees with deleteat!(v, r) on Vector{Bool} for every UnitRange{Int} r, including empty ranges."
    source := "deleteat! docstring (base/array.jl:1916-1944: remove the items at the indices given by inds); invariant: BitVector behaves as Vector{Bool}", status := .refuted
    prop := ``DeleteatRangeAgrees, thm := some ``deleteatRangeAgrees_refuted
    issue := "none found (queries: deleteat! empty range BoundsError, deleteat! range empty, splice! empty, deleteat! BitVector; PRs: deleteat! BitVector, bitarray deleteat)" },
  { id := "bitarrays-deleteat-range-inside", juliaFile := "base/bitarray.jl"
    juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "copy_chunks!"]
    statement := "deleteat!(B, r) agrees with Vector{Bool} and keeps the chunk invariant for every UnitRange{Int} r that is nonempty or starts in 1:length(B)+1."
    source := "invariant: BitVector behaves as Vector{Bool}; unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``DeleteatRangeInsideAgrees, thm := some ``deleteatRangeInsideAgrees },
  { id := "bitarrays-append-prepend", juliaFile := "base/bitarray.jl"
    juliaFns := ["append!(::BitVector, ::BitVector)", "prepend!(::BitVector, ::BitVector)", "copy_chunks!", "copy_chunks_rtol!"]
    statement := "append!(B, C) and prepend!(B, C) compute [B; C] and [C; B] and keep the chunk invariant, also when C === B."
    source := "append!/prepend! docstrings (base/array.jl); unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``AppendPrependAgrees, thm := some ``appendPrependAgrees },
  { id := "bitarrays-resize-negative", juliaFile := "base/bitarray.jl"
    juliaFns := ["resize!(::BitVector, n)"]
    statement := "resize!(B, n; first) throws the same exception type as resize!(v, n) on Vector{Bool} (ArgumentError for n < 0) and otherwise keeps the old elements and the invariant."
    source := "invariant: BitVector behaves as Vector{Bool}; resize!(::Vector) throws ArgumentError(\"new length must be ≥ 0\") (base/array.jl:1575-1576)", status := .refuted
    prop := ``ResizeAgrees, thm := some ``resizeAgrees_refuted
    issue := "none found (queries: resize! negative, resize! BoundsError, BitArray resize!, resize! negative BitVector)" },
  { id := "bitarrays-resize-nonneg", juliaFile := "base/bitarray.jl"
    juliaFns := ["resize!(::BitVector, n; first)"]
    statement := "For every n >= 0, resize!(B, n; first) returns a valid BitVector of length n keeping the old elements (at the end when first=true)."
    source := "resize! docstring (base/array.jl); unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``ResizeNonnegAgrees, thm := some ``resizeNonnegAgrees },
  { id := "bitarrays-fill", juliaFile := "base/bitarray.jl"
    juliaFns := ["fill!(::BitArray, x)"]
    statement := "fill!(B, x) sets every element to x and keeps the chunk invariant."
    source := "fill! docstring; unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``FillAgrees, thm := some ``fillAgrees },
  { id := "bitarrays-shift", juliaFile := "base/bitarray.jl"
    juliaFns := ["<<(::BitVector, ::Int)", ">>(::BitVector, ::Int)", ">>>(::BitVector, ::Int)", "<<(::BitVector, ::UInt)", ">>>(::BitVector, ::UInt)"]
    statement := "B << k and B >> k (= B >>> k) shift the elements k positions backwards resp. forwards for every k::Int, filling with false, and return valid BitVectors."
    source := "<< and >> docstrings (base/bitarray.jl:1333-1414)", status := .proven
    prop := ``ShiftAgrees, thm := some ``shiftAgrees },
  { id := "bitarrays-circshift-empty", juliaFile := "base/bitarray.jl"
    juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"]
    statement := "circshift!(B, k) and circshift!(dest, B, k) agree with circshift! on Vector{Bool} for every k::Int, including empty vectors."
    source := "invariant: BitVector behaves as Vector{Bool}; circshift!(::AbstractVector) returns empty vectors unchanged (base/abstractarray.jl:3756-3758)", status := .refuted
    prop := ``CircshiftAgrees, thm := some ``circshiftAgrees_refuted
    issue := "none found (related: #41402 fixed the same DivideError for Vector, #54294 the same for tuples; queries: circshift, circshift DivideError, circshift BitVector, circshift! BitVector; PRs: BitVector circshift, circshift empty)" },
  { id := "bitarrays-circshift-nonempty", juliaFile := "base/bitarray.jl"
    juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"]
    statement := "For nonempty vectors, circshift!(B, k) and circshift!(dest, B, k) rotate exactly like circshift! on Vector{Bool} for every k::Int and keep the invariant."
    source := "circshift! docstring (base/abstractarraymath.jl); unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``CircshiftNonemptyAgrees, thm := some ``circshiftNonemptyAgrees },
  { id := "bitarrays-reverse-dims-empty", juliaFile := "base/bitarray.jl"
    juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)"]
    statement := "reverse(A; dims=d) on a BitArray of any size agrees with Array{Bool}, including empty arrays."
    source := "reverse docstring (base/arraymath.jl: reverse A along dimension dims); invariant: BitArray behaves as Array{Bool}", status := .refuted
    prop := ``ReverseDimsAgrees, thm := some ``reverseDimsAgrees_refuted
    issue := "none found (related: #58085 zero-dimensional reverse; queries: reverse BitArray, reverse dims empty, step cannot be zero reverse, BitMatrix reverse; PRs: reverse BitArray)" },
  { id := "bitarrays-reverse-dims", juliaFile := "base/bitarray.jl"
    juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)", "copy_chunks!"]
    statement := "For BitArrays without an empty dimension, reverse(A; dims=d) agrees with Array{Bool} and returns a valid BitArray."
    source := "reverse docstring; unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``ReverseDimsNonemptyAgrees, thm := some ``reverseDimsNonemptyAgrees },
  { id := "bitarrays-reverse", juliaFile := "base/bitarray.jl"
    juliaFns := ["reverse!(::BitVector)", "_reverse!(::BitVector, ::Colon)"]
    statement := "reverse!(B) reverses the elements and keeps the chunk invariant."
    source := "reverse! docstring; unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``ReverseAgrees, thm := some ``reverseAgrees },
  { id := "bitarrays-count-init-wrap", juliaFile := "base/bitarray.jl"
    juliaFns := ["count(::BitArray; init)", "bitcount"]
    statement := "count(B; init) returns the same value as count(v; init) on Vector{Bool}, init plus the number of true elements, for every BitInteger type of init."
    source := "count docstring (base/reduce.jl:1067-1090); invariant: BitArray behaves as Array{Bool}", status := .refuted
    prop := ``CountAgrees, thm := some ``countAgrees_refuted
    issue := "none found (related: #59869 open, count(; init) return type differs between master and 1.12; queries: count init, count init BitArray, bitcount init overflow, count init UInt8; PRs: bitcount, count init)" },
  { id := "bitarrays-count-any-all", juliaFile := "base/bitarray.jl"
    juliaFns := ["count(::BitArray)", "any(::BitArray)", "all(::BitArray)"]
    statement := "count(B), any(B) and all(B) agree with Vector{Bool}."
    source := "count/any/all docstrings; they read whole chunks and rely on the zero padding (base/bitarray.jl:1439-1447, 1715-1736)", status := .proven
    prop := ``CountAnyAllAgrees, thm := some ``countAnyAllAgrees },
  { id := "bitarrays-find", juliaFile := "base/bitarray.jl"
    juliaFns := ["findnext(::BitArray, ::Integer)", "findprev(::BitArray, ::Integer)", "findnextnot", "findprevnot", "findnext(!, ::BitArray, i)", "findprev(!, ::BitArray, i)"]
    statement := "findnext and findprev (for true, and through findnextnot/findprevnot for false) agree with the generic methods on Vector{Bool} for every Int start, including the BoundsError cases."
    source := "findnext/findprev docstrings (base/array.jl); invariant: BitVector behaves as Vector{Bool}", status := .proven
    prop := ``FindAgrees, thm := some ``findAgrees },
  { id := "bitarrays-map", juliaFile := "base/bitarray.jl"
    juliaFns := ["map!(!, dest::BitArray, A::BitArray)", "map!(f, dest::BitArray, A::BitArray, B::BitArray)", "bit_map!"]
    statement := "The chunkwise map! specializations agree with elementwise map! over the shortest input, leave the rest of dest unchanged and keep the invariant, also when A === dest."
    source := "map! docstring (destination at least as large as the smallest collection); unused bits zero (base/bitarray.jl:5-6)", status := .proven
    prop := ``MapAgrees, thm := some ``mapAgrees },
  { id := "bitarrays-setindex-mask-partial", juliaFile := "base/bitarray.jl"
    juliaFns := ["setindex!(::BitArray, X::AbstractArray, I::BitArray)", "_unsafe_setindex!(::BitArray, X, ::BitArray)"]
    statement := "B[I] = X with a logical BitVector mask agrees with v[I] = X on Vector{Bool}, including leaving the array unchanged when it throws DimensionMismatch for length(X) != count(I)."
    source := "invariant: BitVector behaves as Vector{Bool}; Array setindex! checks the shape before writing (setindex_shape_check, base/indices.jl)", status := .refuted
    prop := ``SetindexMaskAgrees, thm := some ``setindexMaskAgrees_refuted
    issue := "none found (queries: BitArray setindex! DimensionMismatch mask, logical indexing setindex, BitArray DimensionMismatch, setindex! partial mutation, BitArray setindex)" },
  { id := "bitarrays-vec-resize-alias", juliaFile := "base/bitarray.jl"
    juliaFns := ["reshape(::BitArray, dims)", "vec(::BitArray)", "push!(::BitVector, x)", "pop!(::BitVector)"]
    statement := "push!/pop! on v = vec(M) leave M a valid BitArray (num_bit_chunks(length(M)) chunks, unused bits zero)."
    source := "invariant: unused bits zero (base/bitarray.jl:5-6), relied on by ==, count, hash; reshape shares data (reshape docstring)", status := .refuted
    prop := ``VecAliasKeepsParentValid, thm := some ``vecAliasKeepsParentValid_refuted
    issue := "none found (queries: reshape BitArray, BitArray resize!, BitVector reshape, vec push! shared, reshape push!, BitArray shared chunks; PRs: BitArray reshape)" },
  { id := "bitarrays-bitset-push-delete", juliaFile := "base/bitset.jl"
    juliaFns := ["push!(::BitSet, ::Integer)", "delete!(::BitSet, ::Integer)", "in(::Int, ::BitSet)", "_setint!"]
    statement := "After any sequence of push! and delete! on a BitSet, n in s agrees with Set{Int} for every Int n, including negative values and typemin/typemax."
    source := "BitSet docstring (base/bitset.jl:25-32): a set of Ints; invariant: BitSet behaves as Set{Int}", status := .proven
    prop := ``BitSetPushDeleteAgrees, thm := some ``bitSetPushDeleteAgrees },
  { id := "bitarrays-bitset-symdiff-duplicates", juliaFile := "base/bitset.jl"
    juliaFns := ["symdiff!(::BitSet, itr)", "int_symdiff!", "symdiff(::BitSet, itr)"]
    statement := "symdiff!(s::BitSet, itr) agrees with symdiff!(Set{Int}(s), itr): the result holds exactly the elements in exactly one of s and itr."
    source := "symdiff! docstring (base/abstractset.jl:282-289) and symdiff!(::AbstractSet, itr) = symdiff!(s, Set(itr)) (base/abstractset.jl:297, #46397)", status := .refuted
    prop := ``BitSetSymdiffAgrees, thm := some ``bitSetSymdiffAgrees_refuted
    issue := "none found (related: #34686 and #44591 on symdiff multiplicity, fixed for AbstractSet/Vector by #46397, which left the BitSet method toggling; queries: symdiff, BitSet, symdiff multiplicity, symdiff! BitSet duplicates; PRs: symdiff, BitSet symdiff)" }
]

end JuliaLean.BitArrays
