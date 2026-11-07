import JuliaLean.Proofs.base.cartesian.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem nrefExact_proven : NrefExact := by
  unfold NrefExact
  intros
  rfl

theorem ntupleExact_proven : NtupleExact := by
  unfold NtupleExact
  intros
  rfl

theorem cartesianLoopsCompoundExact_proven : CartesianLoopsCompoundExact := by
  unfold CartesianLoopsCompoundExact
  intros
  rfl

end JuliaLean.ExprReflect
