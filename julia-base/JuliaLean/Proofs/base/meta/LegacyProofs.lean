import JuliaLean.Proofs.base.meta.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem quotContract_proven : QuotContract := by
  unfold QuotContract
  intro
  rfl

theorem showSexprContract_proven : ShowSexprContract := by
  unfold ShowSexprContract
  intros
  simp [toSExpr]

end JuliaLean.ExprReflect
