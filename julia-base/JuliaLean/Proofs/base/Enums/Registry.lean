import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.Enums.LegacyProofs
import JuliaLean.Proofs.base.Enums.Refutations
import JuliaLean.Proofs.base.Enums.RowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesEnums : List Entry := [
  { id := "exprreflect-enum-assignment", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "instances"]
    statement := "For every in-range Int8 starting value below typemax, an explicit member followed by an implicit member receives values x and x+1 in declaration order."
    source := "base/Enums.jl:95-135,144-217,235-237", status := .proven
    prop := ``EnumAssignsDocumentedValues, thm := some ``enumAssignsDocumentedValues_proven },
  { id := "exprreflect-enum-duplicate-values", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every pair of distinct member names assigned the same in-range Int8 value."
    source := "base/Enums.jl:199-200", status := .proven
    prop := ``EnumRejectsDuplicateValues, thm := some ``enumRejectsDuplicateValues_proven },
  { id := "exprreflect-enum-duplicate-names", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every repeated member name even when its two assigned Int8 values differ."
    source := "base/Enums.jl:204-207", status := .proven
    prop := ``EnumRejectsDuplicateNames, thm := some ``enumRejectsDuplicateNames_proven },
  { id := "exprreflect-enum-out-of-range", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "@enum rejects every explicit value outside the chosen Int8 base type's range."
    source := "base/Enums.jl:185-190", status := .proven
    prop := ``EnumRejectsOutOfRange, thm := some ``enumRejectsOutOfRange_proven },
  { id := "exprreflect-enum-overflow", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum"]
    statement := "After an Int8 member assigned typemax, @enum rejects every following implicit member instead of wrapping to typemin."
    source := "base/Enums.jl:178-181,216", status := .proven
    prop := ``EnumRejectsOverflow, thm := some ``enumRejectsOverflow_proven },
  { id := "exprreflect-enum-instances-order", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "instances"]
    statement := "For every three distinct in-range explicit Int8 values, instances lists each value once in declaration order."
    source := "base/Enums.jl:199-207,235-237", status := .proven
    prop := ``EnumInstancesOrder, thm := some ``enumInstancesOrder_proven },
  { id := "exprreflect-enum-typemin-order", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "typemin(::Type{<:Enum})", "typemax(::Type{<:Enum})"]
    statement := "For every successfully constructed enum, typemin and typemax are the minimum and maximum represented instance values."
    source := "base/int.jl:827-831; base/Enums.jl:208-227", status := .refuted
    prop := ``EnumExtremaCorrect, thm := some ``enumExtremaCorrect_refuted
    issue := "none found (queries: enum typemin order OR out of order OR minimum)"
    notes := "@enum E::Int8 high=5 low=-2 top=9 makes Int(typemin(E)) == 5 instead of -2 because lo is never updated after the first member." },
  { id := "exprreflect-enum-runtime-bodies", juliaFile := "base/Enums.jl"
    juliaFns := ["basetype", "convert enum to integer", "cconvert", "write", "read", "_enum_hash", "hash", "isless", "Symbol", "_symbol", "print", "show", "membershiptest", "broadcastable", "enum_argument_error"]
    statement := "Enum runtime methods bitcast through the base type, delegate IO and hashing, order by integer value, map values to names or invalid fallbacks, choose membership strategy, and broadcast as scalars."
    source := "base/Enums.jl:10-93", status := .proven
    prop := ``EnumRuntimeBodies, thm := some ``enumRuntimeBodies_proven },
  { id := "exprreflect-enum-macro-bodies", juliaFile := "base/Enums.jl"
    juliaFns := ["@enum", "generated enum constructor", "Enums.namemap", "typemin", "typemax", "generated _enum_hash", "instances"]
    statement := "@enum validates base types and members in source order, assigns and increments base values, rejects duplicate or invalid declarations, and generates constructor, name, extrema, hash, instances, and constants."
    source := "base/Enums.jl:95-252", status := .proven
    prop := ``EnumMacroBodies, thm := some ``enumMacroBodies_proven },
] ++ enumRowEntries

end JuliaLean.ExprReflect
