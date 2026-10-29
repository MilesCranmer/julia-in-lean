import JuliaLean.Registry.Types
import JuliaLean.IteratorsCov.Count
import JuliaLean.IteratorsCov.Wrappers
import JuliaLean.IteratorsCov.Reverse
import JuliaLean.IteratorsCov.Product
import JuliaLean.IteratorsCov.Metadata
import JuliaLean.IteratorsCov.AnyAll
import JuliaLean.IteratorsCov.SimdLoop

namespace JuliaLean.IteratorsCov

open JuliaLean.Registry

/-- Registry entries for the four iterator implementation files. -/
def entries : List Entry := [
  { id := "iteratorscov-simdloop-semantics", juliaFile := "base/simdloop.jl"
    juliaFns := ["parse_iteration_space", "check_body!", "simd_outer_range", "simd_inner_length",
      "simd_index", "compile", "@simd"]
    statement := "The SIMD parser validates the loop shape, rejects nested forbidden control flow, constructs the documented indexed loop expansion, and accepts only the ivdep option."
    source := "@simd docstring and invariant; base/simdloop.jl:17-137"
    status := .proven, prop := ``SimdLoopSemantics, thm := some ``simdLoopSemantics }

]

end JuliaLean.IteratorsCov
