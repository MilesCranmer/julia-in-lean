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
  { id := "multidim-findfirst-nonempty", juliaFile := "base/array.jl"
    juliaFns := ["findfirst(testf::Function, A::AbstractArray)", "findnext(testf::Function, A, start)", "nextind(::AbstractArray, ::CartesianIndex)"]
    statement := "For an array with no empty dimension, findfirst(f, A) returns the first CartesianIndex in column-major order where f holds, or nothing."
    source := "base/array.jl:2488-2492 (findfirst docstring)"
    status := .proven, prop := ``FindfirstNonempty, thm := some ``findfirstNonempty },
  { id := "multidim-cat-same-ndims", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size_shape", "_cshp", "cat(A...; dims)"]
    statement := "For arrays with the same number of dimensions M >= max(dims), the cat result shape sums the sizes along the concatenated dimensions and is the common size elsewhere; any disagreement along another dimension is a DimensionMismatch."
    source := "base/abstractarray.jl:2061-2066 (cat docstring)"
    status := .proven, prop := ``CatSameNdims, thm := some ``catSameNdims }
]

end JuliaLean.Multidim
