import JuliaLean.Proofs.Compiler.src.typelattice.Common
import JuliaLean.Compiler.src.typeutils.lattice

/-!
Lemmas about `for` loops over lists in `CM` and about the argument accessors of
`Compiler/src/typeutils.jl`, shared by the proofs of the union-splitting functions.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

theorem forIn_cons_run {α β : Type} {a : α} {as : List α} {b : β}
    {f : α → β → CM (ForInStep β)} {s r s'}
    (h : (forIn (a :: as) b f).run s = .ok (r, s')) :
    ∃ st s₁, (f a b).run s = .ok (st, s₁) ∧
      match st with
      | .done b' => r = b' ∧ s' = s₁
      | .yield b' => (forIn as b' f).run s₁ = .ok (r, s') := by
  rw [List.forIn_cons] at h
  obtain ⟨st, s₁, h1, h2⟩ := run_bind_inv h
  refine ⟨st, s₁, h1, ?_⟩
  cases st with
  | done b' => cases h2; exact ⟨rfl, rfl⟩
  | yield b' => exact h2

/-- A loop whose body never stops early from a state `(none, b)` ends in a state `(none, b')`. -/
theorem forIn_yield_none {γ β : Type} (l : List Nat)
    (f : Nat → Option γ × β → CM (ForInStep (Option γ × β)))
    (hf : ∀ i ∈ l, ∀ b s r s', (f i (none, b)).run s = .ok (r, s') → ∃ b', r = .yield (none, b')) :
    ∀ b s r s', (forIn l (none, b) f).run s = .ok (r, s') → r.1 = none := by
  induction l with
  | nil => intro b s r s' h; cases h; rfl
  | cons i l ih =>
    intro b s r s' h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨b', rfl⟩ := hf i (List.mem_cons_self ..) b s st s₁ h1
    exact ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)) b' s₁ r s' h2

/-- `argtypes[i]` within bounds. -/
theorem eltAt_run (argtypes : List LElt) (j : Nat) (hj : j < argtypes.length) (s : Nat) :
    (eltAt argtypes (j + 1)).run s = .ok (argtypes[j], s) := by
  simp only [eltAt, Nat.add_sub_cancel, List.getElem?_eq_getElem hj]; rfl

theorem mem_range'_one {i na : Nat} (h : i ∈ List.range' 1 na) : ∃ j, j < na ∧ i = j + 1 := by
  rw [List.mem_range'_1] at h
  exact ⟨i - 1, by omega, by omega⟩

/-- No `MustAlias` among the arguments. -/
def NoMustAlias (argtypes : List LElt) : Prop := ∀ a ∈ argtypes, a.isMustAlias = false

/-- Without `fargs` and with fewer than two `MustAlias` arguments there is no aliasing, so
`compute_alias_groups` returns `nothing` (the identity grouping). -/
theorem computeAliasGroups_none (argtypes : List LElt) (ats : Option (List LElt))
    (hats : ats = none ∨ ats = some argtypes) (h : NoMustAlias argtypes) :
    Returns (computeAliasGroups argtypes.length none ats) (· = none) := by
  intro s r s' hr
  simp only [computeAliasGroups] at hr
  obtain ⟨c, s₁, hc, hr⟩ := run_bind_inv hr
  have hc' : c = false := by
    simp only [anyAliasCandidate] at hc
    rcases hats with rfl | rfl
    · cases hc; rfl
    · obtain ⟨st, s₂, hst, hc⟩ := run_bind_inv hc
      have := forIn_yield_none (List.range' 1 argtypes.length) _ ?_ 0 s st s₂ hst
      · rw [this] at hc; cases hc; rfl
      · intro i hi b s₃ r₃ s₃' h3
        obtain ⟨j, hj, rfl⟩ := mem_range'_one hi
        obtain ⟨e, s₄, he, h3⟩ := run_bind_inv h3
        rw [eltAt_run argtypes j hj] at he
        cases he
        have hm := h _ (List.getElem_mem hj)
        simp only [hm, Bool.false_eq_true, if_false] at h3
        cases h3
        exact ⟨_, rfl⟩
  subst hc'
  cases hr; rfl

end JuliaLean.Proofs.Compiler.src.typeutils
