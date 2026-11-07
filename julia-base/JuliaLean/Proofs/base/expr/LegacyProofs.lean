import JuliaLean.Proofs.base.expr.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem copyEqual_proven : CopyEqual := by
  unfold CopyEqual
  intro value fresh
  induction value with
  | nil => rfl
  | atom => rfl
  | args first rest ihFirst ihRest => simp [copyExprs, eraseCopyIds, ihFirst, ihRest]
  | quoteNode => rfl
  | expr id head args ih => simp [copyExprs, eraseCopyIds, ih]

theorem isExprContract_proven : IsExprContract := by
  unfold IsExprContract
  intros
  rfl


theorem inlineContract_proven : InlineContract := by
  unfold InlineContract
  intro
  rfl

theorem generatedContract_proven : GeneratedContract := by
  unfold GeneratedContract
  intros
  rfl

end JuliaLean.ExprReflect
