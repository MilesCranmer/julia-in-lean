import JuliaLean.Proofs.Compiler.src.typeutils.Split

/-!
`argtypes_to_type(argtypes)` (`Compiler/src/typeutils.jl:40-45`) on arguments that are native
types.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

theorem mapM_ty_run (f : LElt → CM Val) (ts : List Val)
    (hf : ∀ t ∈ ts, ∀ s, (f (.ty t)).run s = .ok (t, s)) :
    ∀ s, (List.mapM f (ts.map .ty)).run s = .ok (ts, s) := by
  induction ts with
  | nil => intro s; rfl
  | cons t ts ih =>
    intro s
    rw [List.map_cons, List.mapM_cons, StateT.run_bind, hf t (List.mem_cons_self ..) s]
    show (List.mapM f (ts.map .ty) >>= fun l => pure (t :: l)).run s = _
    rw [StateT.run_bind, ih (fun t' ht' => hf t' (List.mem_cons_of_mem _ ht')) s]
    rfl

theorem filterAuxM_true_run {α : Type} (p : α → CM Bool) (l : List α)
    (hp : ∀ x ∈ l, ∀ s, (p x).run s = .ok (true, s)) :
    ∀ acc s, (List.filterAuxM p l acc).run s = .ok (l.reverse ++ acc, s) := by
  induction l with
  | nil => intro acc s; rfl
  | cons x l ih =>
    intro acc s
    simp only [List.filterAuxM]
    rw [StateT.run_bind, hp x (List.mem_cons_self ..) s]
    show (List.filterAuxM p l (x :: acc)).run s = _
    rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]
    simp

theorem filterM_true_run {α : Type} (p : α → CM Bool) (l : List α)
    (hp : ∀ x ∈ l, ∀ s, (p x).run s = .ok (true, s)) :
    ∀ s, (List.filterM p l).run s = .ok (l, s) := by
  intro s
  simp only [List.filterM]
  rw [StateT.run_bind, filterAuxM_true_run p l hp [] s]
  show (pure (l.reverse ++ []).reverse : CM _).run s = _
  simp; rfl

theorem mapM_ty_inv {f : LElt → CM Val} {ts : List Val} {s ws s'}
    (h : (List.mapM f (ts.map .ty)).run s = .ok (ws, s'))
    (hf : ∀ t ∈ ts, ∀ s, (f (.ty t)).run s = .ok (t, s)) : ws = ts ∧ s' = s := by
  rw [mapM_ty_run f ts hf s] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem filterM_true_inv {α : Type} {p : α → CM Bool} {l : List α} {s r s'}
    (h : (List.filterM p l).run s = .ok (r, s'))
    (hp : ∀ x ∈ l, ∀ s, (p x).run s = .ok (true, s)) : r = l ∧ s' = s := by
  rw [filterM_true_run p l hp s] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- A search loop that stops with `some v` exactly when its test answers `false`. -/
theorem forIn_test {γ : Type} (l : List Val) (test : Val → CM Bool) (v : γ)
    (f : Val → Option γ × Unit → CM (ForInStep (Option γ × Unit)))
    (hf : ∀ x ∈ l, ∀ s st s', (f x (none, ())).run s = .ok (st, s') →
      ∃ b, (test x).run s = .ok (b, s') ∧ st = if b then .yield (none, ()) else .done (some v, ())) :
    ∀ s r s', (forIn l (none, ()) f).run s = .ok (r, s') →
      (r.1 = none ∧ ∀ x ∈ l, ∃ s₁ s₂, (test x).run s₁ = .ok (true, s₂)) ∨
      (r.1 = some v ∧ ∃ x ∈ l, ∃ s₁ s₂, (test x).run s₁ = .ok (false, s₂)) := by
  induction l with
  | nil => intro s r s' h; cases h; exact .inl ⟨rfl, fun x hx => absurd hx List.not_mem_nil⟩
  | cons x l ih =>
    intro s r s' h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨b, hb, rfl⟩ := hf x (List.mem_cons_self ..) s st s₁ h1
    cases b
    · obtain ⟨rfl, -⟩ := h2
      exact .inr ⟨rfl, x, List.mem_cons_self .., _, _, hb⟩
    · rcases ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) s₁ r s' h2 with ⟨h3, h4⟩ | ⟨h3, y, hy, h4⟩
      · refine .inl ⟨h3, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨_, _, hb⟩
        · exact h4 y hy
      · exact .inr ⟨h3, y, List.mem_cons_of_mem _ hy, h4⟩

/-- On native types (not `Vararg`s), `argtypes_to_type` is `Tuple{argtypes...}` when every
argument is a valid type tag (`valid_as_lattice(x, true)`), and `Union{}` only when one of them is
not, that is, when no tuple of values has those types. -/
def ArgtypesToTypeSpec : Prop :=
  ∀ n E (ts : List Val), (∀ t ∈ ts, t.isType = true ∧ t.isVararg = false) →
    Returns (argtypesToType n E (ts.map .ty)) (fun r =>
      ((∀ t ∈ ts, ∃ s₁ s₂, (validAsLattice n E t true).run s₁ = .ok (true, s₂)) ∧
        ∃ s₁ s₂, (jlTuple n E ts).run s₁ = .ok (r, s₂)) ∨
      (r = .bottom ∧ ∃ t ∈ ts, ∃ s₁ s₂, (validAsLattice n E t true).run s₁ = .ok (false, s₂)))

theorem argtypesToTypeSpec_proven : ArgtypesToTypeSpec := by
  intro n E ts hts s r s' h
  simp only [argtypesToType] at h
  obtain ⟨ws, s₁, hws, h1⟩ := run_bind_inv h
  obtain ⟨hw1, hw2⟩ := mapM_ty_inv hws (by
    intro t ht s₀
    have hv : isvarargtype t = false := (hts t ht).2
    simp only [hv, Bool.false_eq_true, if_false]
    exact widenconstSplit_ty_run n E t (hts t ht).1 s₀)
  subst ws s₁
  obtain ⟨fs, s₂, hfs, h2⟩ := run_bind_inv h1
  obtain ⟨hf1, hf2⟩ := filterM_true_inv hfs (by
    intro t ht s₀
    have hv : isvarargtype t = false := (hts t ht).2
    simp only [hv, Bool.not_false, if_true]; rfl)
  subst fs s₂
  obtain ⟨st, s₃, hst, h3⟩ := run_bind_inv h2
  have key := forIn_test ts (fun x => validAsLattice n E x true) Val.bottom _ (by
    intro x hxm s₀ st₀ s₀' hx
    obtain ⟨b, s₄, hb, hx⟩ := run_bind_inv hx
    have hv : isvarargtype x = false := (hts x hxm).2
    cases b
    · simp only [hv, Bool.false_or, Bool.not_false, if_true] at hx
      cases hx; exact ⟨false, hb, rfl⟩
    · simp only [hv, Bool.false_or, Bool.not_true, Bool.false_eq_true, if_false] at hx
      cases hx; exact ⟨true, hb, rfl⟩) s st s₃ hst
  rcases key with ⟨h5, h4⟩ | ⟨h5, y, hy, h4⟩
  · simp only [h5] at h3
    exact .inl ⟨h4, _, _, h3⟩
  · simp only [h5] at h3
    cases h3
    exact .inr ⟨rfl, y, hy, h4⟩

end JuliaLean.Proofs.Compiler.src.typeutils
