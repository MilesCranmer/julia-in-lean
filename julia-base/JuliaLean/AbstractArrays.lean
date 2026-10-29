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
  { id := "abstractarrays-index-iteration", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eachindex(::AbstractVector)", "firstindex(::AbstractArray)", "lastindex(::AbstractArray)"]
    statement := "For every offset AbstractVector, eachindex enumerates its axis in order and firstindex and lastindex are the endpoints of that axis."
    source := "base/abstractarray.jl:321-453 (eachindex, firstindex and lastindex docstrings and methods)"
    status := .proven, prop := ``IndexIteration, thm := some ``indexIteration_proven },
  { id := "abstractarrays-basic-ops", juliaFile := "base/abstractarray.jl"
    juliaFns := ["reverse(::AbstractVector)", "fill!(::AbstractArray, x)", "isempty(::AbstractArray)"]
    statement := "reverse preserves an offset vector's axis and reverses its values, fill! assigns the converted value everywhere, and isempty is true exactly at length zero."
    source := "base/array.jl:336-378,2212-2265; base/abstractarray.jl:1262"
    status := .proven, prop := ``BasicArrayOps, thm := some ``basicArrayOps_proven },
  { id := "abstractarrays-linear-cartesian-roundtrip", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_to_linear_index", "_to_subscript_indices", "_sub2ind", "_ind2sub"]
    statement := "For every nonnegative shape whose element count fits Int, converting any in-bounds linear index to column-major Cartesian subscripts and back returns the original index."
    source := "base/abstractarray.jl:1392-1436,3165-3232"
    status := .proven, prop := ``LinearCartesianRoundTrip, thm := some ``linearCartesianRoundTrip_proven }
]

end JuliaLean.AbstractArrays
