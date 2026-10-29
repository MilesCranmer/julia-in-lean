import JuliaLean.MultidimCov.ArrayV2DeleteProps
import JuliaLean.MultidimCov.ArrayV2AccessProps
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

def entries4 : List Entry := [
  entry "getindex-boolrange" ["getindex(a::Array, r::AbstractUnitRange{Bool})"]
    "A[r] for a Bool unit range is logical indexing with collect(r): BoundsError unless length(r) == length(A); otherwise the elements where the mask is true, in order, and UndefRefError for an #undef selected element."
    "comment base/array.jl:992; manual Logical indexing" ``P993 ``p993,
  entry "pushfirst-convert" ["pushfirst!(a::Vector{T}, item) where T"]
    "pushfirst!(a, item) puts item converted to eltype(a) before the old elements; a failing conversion throws that error."
    "docstring base/array.jl:1757-1776" ``P1777 ``p1777,
  entry "deleteat-internal" ["_deleteat!(a::Vector, inds, dltd=Nowhere())", "_push_deleted!(dltd, a::Vector, ind)"]
    "_deleteat!(a, inds, dltd) for sorted unique in-range indices keeps the other slots in order and appends the removed slots (assigned or #undef) in order to a vector dltd, nothing to Nowhere(); otherwise it throws ArgumentError (unsorted) or BoundsError (out of range)."
    "docstring of deleteat! and splice! (base/array.jl:1916-1944, 2054-2056)" ``P1970 ``p1970,
  entry "deleteat-mask" ["deleteat!(a::Vector, inds::AbstractVector{Bool})", "_copy_item!(a::Vector, p, q)"]
    "deleteat!(a, mask) with length(mask) == length(a) leaves the slots where mask is false, in order, #undef slots included; another length throws BoundsError."
    "docstring base/array.jl:1922-1923" ``P2005 ``p2005,
  entry "splice-index" ["splice!(a::Vector, i::Integer, ins=_default_splice)"]
    "splice!(a, i, ins) throws BoundsError outside 1:n and UndefRefError for an #undef item; otherwise it returns a[i] and leaves a[1:i-1], the replacements converted to eltype(a), then a[i+1:n]; a failing conversion throws that error."
    "docstring base/array.jl:2018-2025" ``P2070 ``p2070
    (notes := "The state of a after a failing conversion is the refuted entry arrayops-splice-convert-undef."),
  entry "splice-range" ["splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins=_default_splice)"]
    "splice!(a, f:l, ins) throws BoundsError for a nonempty range outside 1:n and for an insertion point f:f-1 outside 1:n+1 with replacements; otherwise it returns a[f:l] and leaves a[1:f-1], the converted replacements, then a[l+1:n]; a failing conversion throws that error."
    "docstring base/array.jl:2073-2084" ``P2125 ``p2125
    (notes := "Range ends within 2^60 of zero and lengths up to 2^58. The state of a after a failing conversion is the refuted entry arrayops-splice-convert-undef."),
  entry "splice-inds" ["splice!(a::Vector, inds)", "_push_deleted!(dltd, a::Vector, ind)"]
    "splice!(a, inds) for sorted unique in-range indices returns the removed slots (assigned or #undef) in order and leaves the other slots; otherwise it throws ArgumentError (unsorted) or BoundsError (out of range)."
    "docstring base/array.jl:2054-2056" ``P2153 ``p2153
    (notes := "The state of a after a thrown error is the refuted entry arrayops-deleteat-error-partial."),
  entry "keepat-indices" ["keepat!(a::Vector, inds)"]
    "keepat!(a, inds) with assigned kept slots: sorted unique in-range indices leave a[inds]; in-range unsorted indices throw ArgumentError; sorted indices outside 1:n throw BoundsError."
    "docstring base/array.jl:3110-3121" ``P3134 ``p3134
    (notes := "Kept #undef slots are the refuted entry multidimcov-keepat-undef; the state after an error is arrayops-deleteat-error-partial."),
  entry "keepat-mask" ["keepat!(a::Vector, m::AbstractVector{Bool})"]
    "keepat!(a, m) with length(m) == length(a) and assigned kept slots leaves the slots where m is true, in order; another length throws BoundsError."
    "docstring base/array.jl:3137-3142" ``P3159 ``p3159
    (notes := "Kept #undef slots are the refuted entry multidimcov-keepat-undef.")
]

end JuliaLean.MultidimCov.ArrayV2
