import JuliaLean.MultidimCov.ArrayV2RangeFind
import JuliaLean.MultidimCov.ArrayV2IterProps
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

def entries2 : List Entry := [
  entry "range-find-oneto" ["findfirst(p::Fix2{==/isequal}, r::OneTo)", "findfirst(::typeof(iszero), ::OneTo)",
      "findfirst(::typeof(isone), r::OneTo)"]
    "For OneTo(n) with n <= typemax(Int), findfirst(==(x)), findfirst(isequal(x)) for any integer x, findfirst(iszero) and findfirst(isone) agree with the scan of collect(OneTo(n))."
    "findfirst docstring base/array.jl:2489" ``P2534 ``p2534,
  entry "range-find-bounds" ["findfirst(p::Fix2{==/isequal}, r::AbstractUnitRange{<:Integer})",
      "findfirst(p::Fix2{==/isequal}, r::StepRange{T,S})", "findfirst(::typeof(iszero), r::AbstractRange)",
      "findfirst(::typeof(isone), r::AbstractRange)", "findlast(p, r::AbstractUnitRange{<:Integer})",
      "findlast(p, r::StepRange{T,S})"]
    "On unit and step ranges, findfirst/findlast with ==(x), isequal(x), iszero or isone return nothing for an empty range and for x outside [minimum(r), maximum(r)], never report a value between the endpoints of a unit range as missing, findlast equals findfirst, and iszero/isone search for zero/one of the element type."
    "findfirst docstring base/array.jl:2489; comment base/array.jl:2727"
    ``PRangeFindBounds ``pRangeFindBounds
    (notes := "The scan contract itself is the refuted entry ranges-operations-findfirst-overflow. StepRange modelled with step type equal to the element type."),
  entry "append-iter" ["append!(a::AbstractVector, iter)", "_append!(a::AbstractVector, ::Union{HasLength,HasShape}, iter)",
      "_append!(a::AbstractVector, ::IteratorSize, iter)"]
    "append!(a, iter) on a Vector is a's old elements followed by the items of iter converted in order, with or without a known length; a failing conversion propagates."
    "append! docstring base/array.jl:1383" ``P1435 ``p1435
    (notes := "Inputs: memory length plus the number of items at most 2^59."),
  entry "prepend-iter" ["prepend!(a::AbstractVector, iter)", "_prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)",
      "_prepend!(a::Vector, ::IteratorSize, iter)"]
    "prepend!(a, iter) on a Vector is the items of iter converted in order followed by a's old elements, with or without a known length; a failing conversion propagates."
    "prepend! docstring base/array.jl:1455" ``P1500 ``p1500
    (notes := "Inputs: length plus the number of items below 2^59.")
]

end JuliaLean.MultidimCov.ArrayV2
