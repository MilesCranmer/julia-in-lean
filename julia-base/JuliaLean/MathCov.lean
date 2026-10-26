import JuliaLean.MathCov.Methods
import JuliaLean.Registry.Types

namespace JuliaLean.MathCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := Methods.entries ++ [
  { id := "mathcov-cosc-large-argument", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::Union{Float32, Float64})"]
    statement := "For every finite nonzero Float32 or Float64, cosc returns its documented formula."
    source := "base/special/trig.jl:1244-1250 (cosc docstring)"
    status := .refuted, prop := ``CoscLargeArgument, thm := some ``coscLargeArgument_refuted
    issue := "none found (queries: cosc; cosc NaN; cosc overflow large; cosc floatmax; related issues #59064 and #59065)"
    notes := "floatmax(Float64) is finite, but cosc returns NaN instead of inv(floatmax(Float64)); release 1.13.2 and nightly reproduce." }
]

end JuliaLean.MathCov
