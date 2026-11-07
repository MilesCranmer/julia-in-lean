import JuliaLean.Proofs.base.weakdict.Contracts

namespace JuliaLean.IdDicts

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
