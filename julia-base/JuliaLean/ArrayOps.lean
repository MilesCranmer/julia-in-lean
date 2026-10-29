import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ArrayOps.Vec
import JuliaLean.ArrayOps.Pure
import JuliaLean.ArrayOps.VecProps
import JuliaLean.ArrayOps.PureProps
import JuliaLean.ArrayOps.VecProofs
import JuliaLean.ArrayOps.PureProofs
import JuliaLean.ArrayOps.PureProofs2
import JuliaLean.ArrayOps.Unique
import JuliaLean.ArrayOps.UniqueProofs

namespace JuliaLean.ArrayOps

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "arrayops-dequeue", juliaFile := "base/array.jl"
    juliaFns := ["push!(::Vector, x)", "pushfirst!(::Vector, x)", "pop!(::Vector)", "popfirst!(::Vector)"]
    statement := "push!/pushfirst! add at the ends; pop!/popfirst! remove and return the last/first element, and throw ArgumentError on an empty vector."
    source := "base/array.jl:1330-1355, 1659-1699, 1758-1776, 1804-1835 (docstrings)", status := .proven
    prop := ``DequeueSpec, thm := some ``dequeueSpec },
  { id := "arrayops-insert", juliaFile := "base/array.jl"
    juliaFns := ["insert!(::Vector, i::Integer, x)", "_growat!"]
    statement := "insert!(a, i, x) for an index of any integer type puts x at index i for 1 <= i <= length(a)+1, and otherwise throws BoundsError (InexactError when Int(i) fails) leaving a unchanged."
    source := "base/array.jl:1845-1865 (docstring: index is the index of item in the resulting a)", status := .proven
    prop := ``InsertSpec, thm := some ``insertSpec },
  { id := "arrayops-deleteat-index", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, i::Integer)", "_deleteat!(a, i, delta)"]
    statement := "deleteat!(a, i) for an index of any integer type removes a[i] when 1 <= i <= length(a), and otherwise throws BoundsError (InexactError when Int(i) fails) leaving a unchanged."
    source := "base/array.jl:1880-1898 (docstring)", status := .proven
    prop := ``DeleteatIndexSpec, thm := some ``deleteatIndexSpec },
  { id := "arrayops-deleteat-range-inbounds", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, r::AbstractUnitRange{<:Integer})", "_deleteat!(a, i, delta)"]
    statement := "deleteat!(a, lo:hi) does nothing for an empty range and removes exactly a[lo:hi] for 1 <= lo <= hi <= length(a), for unit ranges of every integer type."
    source := "base/array.jl:1916-1944 (docstring)", status := .proven
    prop := ``DeleteatRangeInBounds, thm := some ``deleteatRangeInBounds },
  { id := "arrayops-deleteat-sorted", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector)", "_deleteat!(a, inds)"]
    statement := "deleteat!(a, inds) for sorted, unique, in-bounds inds::Vector{Int} removes exactly the elements at those positions."
    source := "base/array.jl:1916-1944 (docstring: inds is a collection of sorted and unique integer indices)", status := .proven
    prop := ``DeleteatSortedSpec, thm := some ``deleteatSortedSpec },
  { id := "arrayops-deleteat-mask", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector{Bool})"]
    statement := "deleteat!(a, mask) with a Bool vector of length(a) removes the entries marked true; another length throws BoundsError leaving a unchanged."
    source := "base/array.jl:1916-1944 (docstring: a boolean vector of the same length as a)", status := .proven
    prop := ``DeleteatMaskSpec, thm := some ``deleteatMaskSpec },
  { id := "arrayops-filter-bang", juliaFile := "base/array.jl"
    juliaFns := ["filter!(f, a::AbstractVector)"]
    statement := "filter!(f, a) keeps exactly the elements for which f is true, in order."
    source := "base/array.jl:3049-3065 (docstring)", status := .proven
    prop := ``FilterBangSpec, thm := some ``filterBangSpec },
  { id := "arrayops-splice-range", juliaFile := "base/array.jl"
    juliaFns := ["splice!(::Vector, r::AbstractUnitRange{<:Integer}, ins)"]
    statement := "splice!(a, f:l, ins) for 1 <= f <= l+1 <= length(a)+1 (including the empty range f:f-1) returns a[f:l] and replaces it by ins."
    source := "base/array.jl:2088-2124 (docstring: splice!(collection, n:n-1, replacement) inserts before n)", status := .proven
    prop := ``SpliceRangeSpec, thm := some ``spliceRangeSpec },
  { id := "arrayops-resize", juliaFile := "base/array.jl"
    juliaFns := ["resize!(::Vector, n::Integer; first)"]
    statement := "resize!(a, n; first) for n of any integer type throws ArgumentError for n < 0 and otherwise yields length n, keeping the first (first=false) or last (first=true) min(n, length(a)) elements, with new slots unassigned."
    source := "base/array.jl:1527-1563 (docstring)", status := .proven
    prop := ``ResizeSpec, thm := some ``resizeSpec
    notes := "The first keyword is new in 1.14 (absent in 1.13.2)." },
  { id := "arrayops-reverse-window", juliaFile := "base/array.jl"
    juliaFns := ["reverse!(v::AbstractVector, start::Integer, stop::Integer)"]
    statement := "reverse!(v, start, stop) for indices of any integer type reverses exactly v[start:stop] when 1 <= start <= stop <= length(v), and leaves v unchanged when stop <= start."
    source := "base/array.jl:2291-2316 (docstring), 2212-2252 (reverse(v, start, stop) docstring)", status := .proven
    prop := ``ReverseBangSpec, thm := some ``reverseBangSpec },
  { id := "arrayops-find-inrange", juliaFile := "base/array.jl"
    juliaFns := ["findnext(testf::Function, A, start)", "findprev(testf::Function, A, start)"]
    statement := "findnext(f, v, i) for i >= 1 and findprev(f, v, i) for i <= length(v), of any integer type, return the next (previous) matching index after (before) or including i, or nothing."
    source := "base/array.jl:2446-2474, 2634-2670 (docstrings)", status := .proven
    prop := ``FindInRange, thm := some ``findInRange },
  { id := "arrayops-accumulate", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; init)", "cumsum(::AbstractVector)"]
    statement := "accumulate(op, v; init) is [op(init, v1), op(op(init, v1), v2), ...] and cumsum of a BitInteger vector is the running sum wrapped into the widened type."
    source := "base/accumulate.jl:69-115, 234-280 (cumsum and accumulate docstrings; accumulate(+, [1,2,3]; init=100) == [101, 103, 106]; cumsum widens narrow integers)", status := .proven
    prop := ``AccumulateSpec, thm := some ``accumulateSpec }
]

end JuliaLean.ArrayOps
