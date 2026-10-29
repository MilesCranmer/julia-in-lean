import JuliaLean.MultidimCov.ArrayV2LiteralsProps
import JuliaLean.MultidimCov.ArrayV2Wrap
import JuliaLean.MultidimCov.ArrayV2Types
import JuliaLean.MultidimCov.ArrayV2CatProps
import JuliaLean.MultidimCov.ArrayV2Range
import JuliaLean.MultidimCov.ArrayV2SetsProps
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean.Registry

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := s!"multidimcov-array-v2-{id}", juliaFile := "base/array.jl", juliaFns := fns,
    statement, source, status := .proven, prop, thm := some thm, notes }

private def refuted (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (issue notes : String) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue, notes }

def entries3 : List Entry := [
  entry "cat-integers" ["_cat(n::Integer, x::Integer...)"]
    "cat(x::Integer...; dims=n) for n >= 1 is an array of size (1,...,1,length(x)) holding x promoted; n < 1 throws ArgumentError."
    "docstring of cat (base/abstractarray.jl)" ``P2368 ``p2368,
  entry "collect" ["collect(itr)", "collect_similar(cont, itr)", "_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape})",
      "_collect(cont, itr, ::HasEltype, isz::SizeUnknown)", "_collect(c, itr, ::EltypeUnknown, isz::SizeUnknown)",
      "_collect(c, itr, ::EltypeUnknown, isz::Union{HasLength,HasShape})", "collect_to_with_first!(dest::AbstractArray, v1, itr, st)",
      "setindex_widen_up_to(dest::AbstractArray{T}, el, i)", "collect_to!(dest::AbstractArray{T}, itr, offs, st)",
      "grow_to!(dest, itr)", "push_widen(dest, el)", "grow_to!(dest, itr, st)", "@default_eltype(itr)"]
    "collect(itr) holds the items in order, shaped like a HasShape iterator and a vector otherwise; with a declared eltype T the element type is T, otherwise it is the promote_typejoin of the value types, or the inferred type for an empty iterator."
    "docstring base/array.jl:719-770" ``P771 ``p771
    (notes := "Type universe Int, Float64, String, Union{Int,Float64}, Real, Any; inference assumed sound for the iterator."),
  entry "collect-to-with-first-push" ["collect_to_with_first!(dest, v1, itr, st)"]
    "collect_to_with_first! into a vector-like destination pushes v1 and grows with the rest: all values in order, element type from the values."
    "comment base/array.jl:881-884" ``P881 ``p881,
  refuted "multidimcov-hcat-vector-eltype" ["hcat(V::Vector{T}...) where T"]
    "hcat of Vector{T}s of equal length h is an h x n Matrix{T} holding the vectors as columns (equivalent to cat(A...; dims=2)); unequal lengths throw DimensionMismatch."
    "docstring of hcat (base/abstractarray.jl)" ``P2340 ``p2340_refuted
    "https://github.com/JuliaLang/julia/issues/26004"
    "Counterexample: hcat(Any[1], Any[2]) has element type Int.",
  entry "vcat-same" ["vcat(arrays::Vector{T}...) where T"]
    "vcat of Vector{T}s is a Vector{T} of the total length holding their slots one after another."
    "docstring of vcat (base/abstractarray.jl)" ``P2351 ``p2351,
  entry "hcat-mixed" ["hcat(A::Vector...)"]
    "hcat of vectors of equal length is an h x n matrix with element type promote_type of the element types, holding the converted elements column by column; unequal lengths throw DimensionMismatch."
    "docstrings of hcat/cat (base/abstractarray.jl)" ``P2349 ``p2349,
  entry "vcat-mixed" ["vcat(A::Vector...)"]
    "vcat of vectors is a vector with element type promote_type of the element types holding all elements converted, one vector after another."
    "docstrings of vcat/cat (base/abstractarray.jl)" ``P2366 ``p2366,
  entry "getindex-unitrange" ["getindex(A::Array, I::AbstractUnitRange{<:Integer})"]
    "A[lo:hi] is a vector of A's slots lo..hi; an empty range gives an empty vector even out of bounds; any other range reaching outside 1:length(A) throws BoundsError."
    "manual Indexing" ``P981 ``p981,
  entry "getindex-steprange" ["getindex(A::Array{S}, I::AbstractRange{Int}) where S"]
    "A[r] for a non-unit Int range holds A[i] for i in r in order; an index outside 1:length(A) throws BoundsError."
    "manual Indexing" ``P1005 ``p1005,
  entry "setindex-vector" ["setindex!(A::Array, X::AbstractArray, I::AbstractVector{Int})"]
    "A[I] = X throws DimensionMismatch unless length(X) == length(I), then BoundsError outside 1:length(A); otherwise each A[I[k]] receives X[k] converted in order (a repeated index keeps its last value) and other slots keep their values."
    "manual Indexed assignment" ``P1063 ``p1063,
  entry "setindex-range-colon" ["setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int})", "setindex!(A::Array{T}, X::Array{T}, c::Colon)"]
    "A[lo:hi] = X throws BoundsError for a nonempty range outside A, then DimensionMismatch unless length(X) matches; otherwise slot lo+k-1 receives X's slot k and other slots keep their values; A[:] = X likewise for the whole array."
    "manual Indexed assignment" ``P1078 ``p1078
]

end JuliaLean.MultidimCov.ArrayV2
