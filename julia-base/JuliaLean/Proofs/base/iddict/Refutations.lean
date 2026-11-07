import JuliaLean.Proofs.base.iddict.Contracts

/-!
# Refutations: concrete counterexamples mirroring the reproducers
-/

namespace JuliaLean.IdDicts

/-- `d = IdDict{Any,Any}(); d["k"] = Base.secret_table_token` -/
def tokenOps : List DOp := [.set (.str "k") token]

theorem tokenDict_iterate :
    (runD .any .any tokenOps).iterate = .ok [(.str "k", token)] := by decide

theorem lookupFindsPresent_refuted : ¬ LookupFindsPresent := by
  intro h
  have := h .any .any tokenOps (.str "k") token ⟨_, tokenDict_iterate, by decide⟩
  revert this
  decide

theorem popReturnsPresent_refuted : ¬ PopReturnsPresent := by
  intro h
  have := h .any .any tokenOps (.str "k") token ⟨_, tokenDict_iterate, by decide⟩
  revert this
  decide

theorem getBangKeepsPresent_refuted : ¬ GetBangKeepsPresent := by
  intro h
  have := h .any .any tokenOps (.str "k") token (.str "DEFAULT") ⟨_, tokenDict_iterate, by decide⟩
  dsimp only at this
  revert this
  decide

end JuliaLean.IdDicts
