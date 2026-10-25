import JuliaLean.IdDicts.Props

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

/-- `s = IdSet{Int}(); push!(s, "a string")` -/
theorem idSetElemsHaveEltype_refuted : ¬ IdSetElemsHaveEltype := by
  intro h
  obtain ⟨xs, hx⟩ := h .int [.push (.str "a string")]
  have e : (runS .int [.push (.str "a string")]).iterate = .error .typeError := by decide
  rw [e] at hx
  cases hx

/-- `a = [1]; b = [1]; symdiff!(IdSet{Any}(), [a, b])` loses `a`. -/
theorem idSetSymdiffIdentity_refuted : ¬ IdSetSymdiffIdentity := by
  intro h
  have := h [] [.vec 0 1, .vec 1 1] (.vec 0 1)
  revert this
  decide

/-- `issetequal(IdSet{Any}(Any[1, 1.0]), Any[1, 1.0])` -/
theorem idSetIssetequalSubsets_refuted : ¬ IdSetIssetequalSubsets := by
  intro h
  have := (h [.push (.int 1), .push (.flt 1)] [.int 1, .flt 1]).1
  revert this
  decide

/-- `IdSet{Any}(Any[1, 1.0]) ⊆ Set([1])` -/
theorem idSetIssubsetIn_refuted : ¬ IdSetIssubsetIn := by
  intro h
  have := (h [.push (.int 1), .push (.flt 1)] [.int 1]).1
  revert this
  decide

/-- `wk[k1] = :first; wk[k2] = :second` with `k1 = [1]`, `k2 = [1]`, then a
collection frees `k2`. -/
def wkOps : List WOp :=
  [.set (.vec 0 1) (.sym "first"), .set (.vec 1 1) (.sym "second"), .gc [.vec 1 1]]

theorem weakKeyLengthLive_refuted : ¬ WeakKeyLengthLive := by
  intro h
  have real : Realistic wkOps := by
    refine ⟨?_, ?_, trivial⟩
    · intro x hx; simp at hx; subst hx; rfl
    · intro x _ op hop; simp at hop
  have nofree : NoValueFreed wkOps := by
    intro op hop dead hd op' hop' k v hkv
    simp [wkOps] at hop hop'
    rcases hop with rfl | rfl | rfl <;> cases hd
    rcases hop' with rfl | rfl | rfl <;> cases hkv <;> simp
  have := h .any wkOps real nofree
  dsimp only at this
  revert this
  decide

/-- `w = WeakValueIdDict{Any,Vector{Int}}(); w[:k] = [1.0]; w[:k]` -/
theorem weakValueReadsTyped_refuted : ¬ WeakValueReadsTyped := by
  intro h
  have := h .any .vec (.sym "k") (.fvec 0 1) (.vec 1 0) (by decide)
  exact this.1 (by decide)

end JuliaLean.IdDicts
