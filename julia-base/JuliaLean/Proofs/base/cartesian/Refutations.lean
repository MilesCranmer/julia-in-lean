import JuliaLean.Proofs.base.cartesian.Claims

namespace JuliaLean.ExprReflect

open JuliaLean

theorem cartesianLoopsTotal_refuted : ¬ CartesianLoopsTotal := by
  unfold CartesianLoopsTotal
  intro h
  have wrong := h 2 "i" "A" (.atom "body")
  simp [nloops, isCompound] at wrong

end JuliaLean.ExprReflect
