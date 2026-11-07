import JuliaLean.base.ntuple

namespace JuliaLean.Tuples

/-- Same value, or exceptions of the same type. -/
def SameOutcome {α : Type} : R α → R α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error f => e.kind = f.kind
  | _, _ => False

end JuliaLean.Tuples
