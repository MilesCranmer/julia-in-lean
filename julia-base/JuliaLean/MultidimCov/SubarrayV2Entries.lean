import JuliaLean.MultidimCov.SubarrayV2Misc
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.Registry

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := s!"multidimcov-subarray-v2-{id}", juliaFile := "base/subarray.jl", juliaFns := fns,
    statement, source, status := .proven, prop, thm := some thm, notes }

private def incomplete (id : String) (fns : List String) (statement source : String)
    (prop _thm : Lean.Name) (notes : String := "") : Entry :=
  { id := s!"multidimcov-subarray-v2-{id}", juliaFile := "base/subarray.jl", juliaFns := fns,
    statement, source, status := .todo, prop, notes }

private def refuted (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (issue notes : String) : Entry :=
  { id := s!"multidimcov-subarray-v2-{id}", juliaFile := "base/subarray.jl", juliaFns := fns,
    statement, source, status := .refuted, prop, thm := some thm, issue, notes }

def entries : List Entry := [
  entry "construct-linear-whole-axis" ["SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}"]
    "When every Slice spans its parent axis, the fast constructor's offset and stride map each view element to its parent position."
    "invariant: linear indexing of a FastSubArray, base/subarray.jl:17-18, 323-344" ``P34 ``p34,
  entry "getindex-fast-whole-axis" ["getindex(V::FastSubArray, i::Int)"]
    "When every Slice spans its parent axis, fast-view reads agree with their parent positions and out-of-bounds indices throw."
    "view docstring; linear indexing manual" ``P330 ``p330,
  entry "getindex-fast-vector-whole-axis" ["getindex(V::FastSubArray{<:Any, 1}, i::Int)"]
    "When every Slice spans its parent axis, one-dimensional fast-view reads agree with their parent positions and out-of-bounds indices throw."
    "view docstring; linear indexing manual" ``P339 ``p339,
  entry "setindex-fast-vector-whole-axis" ["setindex!(V::FastSubArray{<:Any, 1}, x, i::Int)"]
    "When every Slice spans its parent axis, fast-vector writes modify exactly the selected element."
    "view docstring (writes through views modify the parent)" ``P398 ``p398,
  entry "isassigned-fast-vector-whole-axis" ["isassigned(V::FastSubArray{<:Any, 1}, i::Int)"]
    "When every Slice spans its parent axis, isassigned checks the selected parent element."
    "isassigned docstring base/multidimensional.jl" ``P426 ``p426,
  entry "pointer-fast-whole-axis" ["pointer(V::FastSubArray, i::Int)"]
    "When every Slice spans its parent axis, a non-contiguous fast-view pointer selects the corresponding parent element."
    "pointer docstring; linear indexing invariant" ``P510 ``p510,
  entry "pointer-contiguous-whole-axis" ["pointer(V::FastContiguousSubArray, i::Int)"]
    "When every Slice spans its parent axis, a contiguous fast-view pointer selects the corresponding parent element."
    "pointer docstring; linear indexing invariant" ``P511 ``p511
]

end JuliaLean.MultidimCov.SubarrayV2
