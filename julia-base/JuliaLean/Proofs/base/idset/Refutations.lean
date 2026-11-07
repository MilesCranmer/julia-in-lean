import JuliaLean.Proofs.base.idset.Contracts

namespace JuliaLean.IdDicts

/-- `s = IdSet{Int}(); push!(s, "a string")` -/
theorem idSetElemsHaveEltype_refuted : ¬ IdSetElemsHaveEltype := by
  intro h
  obtain ⟨xs, hx⟩ := h .int [.push (.str "a string")]
  have e : (runS .int [.push (.str "a string")]).iterate = .error .typeError := by decide
  rw [e] at hx
  cases hx

end JuliaLean.IdDicts
