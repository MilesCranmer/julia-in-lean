import JuliaLean.Registry.Types
import JuliaLean.HashOps.Validation

namespace JuliaLean.HashOps

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "hashops-annotated-isless"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["isequal(::AnnotatedString, ::AnnotatedString)", "cmp(::AnnotatedString, ::AnnotatedString)", "isless(::AbstractString, ::AbstractString)"]
    statement := "For any two AnnotatedStrings, exactly one of isless(a,b), isless(b,a), and isequal(a,b) is true."
    source := "isless docstring base/operators.jl:208-214; cmp docstring base/operators.jl:508-511"
    status := .refuted
    prop := ``AnnotatedStringOrder
    thm := some ``annotatedStringOrder_refuted
    issue := "none found (queries: AnnotatedString cmp; AnnotatedString isless; AnnotatedString equality ordering; annotations cmp isless)"
    notes := "Same text with :red versus :blue annotations: isequal and both isless calls are false, while cmp is 0, on both versions." }
]

end JuliaLean.HashOps
