import JuliaLean.base.cartesian

namespace JuliaLean.ExprReflect

open JuliaLean

def NrefExact : Prop := ∀ dimensions array stem,
  nref dimensions array stem = .expr "escape" [.expr "ref" (.atom array ::
    (List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def NtupleExact : Prop := ∀ dimensions stem,
  ntuple dimensions stem = .expr "escape" [.expr "tuple"
    ((List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def CartesianLoopsTotal : Prop := ∀ dimensions iterator array body,
  nloops dimensions iterator array body =
    .ok (documentedLoops dimensions iterator array body)

def CartesianLoopsCompoundExact : Prop := ∀ dimensions iterator array head args,
  nloops dimensions iterator array (.expr head args) =
    .ok (documentedLoops dimensions iterator array (.expr head args))

end JuliaLean.ExprReflect
