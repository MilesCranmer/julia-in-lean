import JuliaLean.Proofs.base.reflection.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem whichHasMethod_proven : WhichHasMethod := by
  unfold WhichHasMethod
  intro table modules method h
  cases filtered : methods table modules with
  | nil => simp [whichMethod, filtered] at h
  | cons first rest => simp [hasMethod, filtered]

theorem nameofContract_proven : NameofContract := by
  unfold NameofContract
  intro
  rfl

end JuliaLean.ExprReflect
