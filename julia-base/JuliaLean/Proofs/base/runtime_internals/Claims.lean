import JuliaLean.base.runtime_internals

namespace JuliaLean.ExprReflect

open JuliaLean

def FieldNamesCount : Prop := ∀ layout names count,
  fieldNames layout = .ok names → fieldCount layout = .ok count →
  names.length = count

def FieldOffsetInBounds : Prop := ∀ layout index offset,
  fieldOffset layout index = .ok offset →
  1 ≤ index ∧ index ≤ (layout.names.length : Int)

def MethodFiltering : Prop := ∀ table modules method,
  method ∈ methods table modules →
  method.signatureMatches = true ∧ modules.all (·.contains method.moduleName) = true

end JuliaLean.ExprReflect
