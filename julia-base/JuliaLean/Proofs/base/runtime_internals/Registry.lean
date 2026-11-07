import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.runtime_internals.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesRuntime_internals : List Entry := [
  { id := "exprreflect-fieldnames-count", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldnames", "fieldcount"]
    statement := "Whenever fieldnames and fieldcount return normally for a layout, the number of names equals the field count."
    source := "base/runtime_internals.jl:413-442,1456-1487", status := .proven
    prop := ``FieldNamesCount, thm := some ``fieldNamesCount_proven },
  { id := "exprreflect-fieldoffset-bounds", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldoffset"]
    statement := "Every successful one-based fieldoffset lookup uses an index within fieldnames(type)."
    source := "base/runtime_internals.jl:1228-1275; field-layout invariant", status := .proven
    prop := ``FieldOffsetInBounds, thm := some ``fieldOffsetInBounds_proven },
  { id := "exprreflect-methods-filter", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["methods", "matches_to_methods"]
    statement := "Every method returned by methods matches the requested signature and, when supplied, the module filter."
    source := "base/runtime_internals.jl:1706-1758", status := .proven
    prop := ``MethodFiltering, thm := some ``methodFiltering_proven },
]

end JuliaLean.ExprReflect
