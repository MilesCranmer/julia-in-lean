import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.array.mutation_properties
import JuliaLean.Proofs.base.array.vector_properties
import JuliaLean.Proofs.base.array.mutation_proofs
import JuliaLean.Proofs.base.array.vector_proofs
import JuliaLean.Proofs.base.array.vector_folds
import JuliaLean.Proofs.base.set.unique

namespace JuliaLean.ArrayOps

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "arrayops-insert", juliaFile := "base/array.jl"
    juliaFns := ["insert!(::Vector, i::Integer, x)", "_growat!"]
    statement := "insert!(a, i, x) for an index of any integer type puts x at index i for 1 <= i <= length(a)+1, and otherwise throws BoundsError (InexactError when Int(i) fails) leaving a unchanged."
    source := "base/array.jl:1845-1865 (docstring: index is the index of item in the resulting a)", status := .proven
    prop := ``InsertSpec, thm := some ``insertSpec },
  { id := "arrayops-deleteat-sorted", juliaFile := "base/array.jl"
    juliaFns := ["deleteat!(::Vector, inds::AbstractVector)", "_deleteat!(a, inds)"]
    statement := "deleteat!(a, inds) for sorted, unique, in-bounds inds::Vector{Int} removes exactly the elements at those positions."
    source := "base/array.jl:1916-1944 (docstring: inds is a collection of sorted and unique integer indices)", status := .proven
    prop := ``DeleteatSortedSpec, thm := some ``deleteatSortedSpec },
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
  { id := "arrayops-reverse-window", juliaFile := "base/array.jl"
    juliaFns := ["reverse!(v::AbstractVector, start::Integer, stop::Integer)"]
    statement := "reverse!(v, start, stop) for indices of any integer type reverses exactly v[start:stop] when 1 <= start <= stop <= length(v), and leaves v unchanged when stop <= start."
    source := "base/array.jl:2291-2316 (docstring), 2212-2252 (reverse(v, start, stop) docstring)", status := .proven
    prop := ``ReverseBangSpec, thm := some ``reverseBangSpec },
  { id := "arrayops-accumulate", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate(op, A; init)", "cumsum(::AbstractVector)"]
    statement := "accumulate(op, v; init) is [op(init, v1), op(op(init, v1), v2), ...] and cumsum of a BitInteger vector is the running sum wrapped into the widened type."
    source := "base/accumulate.jl:69-115, 234-280 (cumsum and accumulate docstrings; accumulate(+, [1,2,3]; init=100) == [101, 103, 106]; cumsum widens narrow integers)", status := .proven
    prop := ``AccumulateSpec, thm := some ``accumulateSpec }
]

end JuliaLean.ArrayOps
