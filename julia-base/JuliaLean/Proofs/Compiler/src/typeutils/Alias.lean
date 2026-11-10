import JuliaLean.Proofs.Compiler.src.typeutils.Loops

/-!
`any_alias_candidate` and `compute_alias_groups` (`Compiler/src/typeutils.jl:187-241`) on every
input: when aliasing is possible at all.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- A loop that stops with `some v` at the first element satisfying `Q`, and otherwise ends with
`none`. -/
theorem forIn_exists {α σ γ : Type} (l : List α) (u : σ) (v : γ) (Q : α → Prop)
    (F : α → Option γ × σ → CM (ForInStep (Option γ × σ)))
    (hF : ∀ x ∈ l, ∀ s st s', (F x (none, u)).run s = .ok (st, s') →
      (st = .yield (none, u) ∧ ¬ Q x) ∨ (st = .done (some v, u) ∧ Q x)) :
    ∀ s r s', (forIn l (none, u) F).run s = .ok (r, s') →
      (r.1 = none ∧ ∀ x ∈ l, ¬ Q x) ∨ (r.1 = some v ∧ ∃ x ∈ l, Q x) := by
  induction l with
  | nil => intro s r s' h; cases h; exact .inl ⟨rfl, fun x hx => absurd hx List.not_mem_nil⟩
  | cons x l ih =>
    intro s r s' h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    rcases hF x (List.mem_cons_self ..) s st s₁ h1 with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
    · rcases ih (fun y hy => hF y (List.mem_cons_of_mem _ hy)) s₁ r s' h2 with ⟨h3, h4⟩ | ⟨h3, y, hy, h4⟩
      · refine .inl ⟨h3, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hq
        · exact h4 y hy
      · exact .inr ⟨h3, y, List.mem_cons_of_mem _ hy, h4⟩
    · obtain ⟨rfl, -⟩ := h2
      exact .inr ⟨rfl, x, List.mem_cons_self .., hq⟩

theorem fargAt_run_inv {fa : List FArg} {i : Nat} {s x s'}
    (h : (fargAt fa i).run s = .ok (x, s')) : fa[i - 1]? = some x ∧ s' = s := by
  simp only [fargAt] at h
  cases h' : fa[i - 1]? with
  | none => rw [h'] at h; cases h
  | some a => rw [h'] at h; cases h; exact ⟨rfl, rfl⟩

theorem eltAt_run_inv {ats : List LElt} {i : Nat} {s x s'}
    (h : (eltAt ats i).run s = .ok (x, s')) : ats[i - 1]? = some x ∧ s' = s := by
  simp only [eltAt] at h
  cases h' : ats[i - 1]? with
  | none => rw [h'] at h; cases h
  | some a => rw [h'] at h; cases h; exact ⟨rfl, rfl⟩

/-- Position `i` (1-based) holds a `SlotNumber` or `SSAValue` that also sits at an earlier
position (`fargs[j] === fargs[i]`). -/
def FargAliased (fa : List FArg) (i : Nat) : Prop :=
  ∃ a, fa[i - 1]? = some a ∧ a.isSlotOrSSA = true ∧
    ∃ j ∈ List.range' 1 (i - 1), ∃ b, fa[j - 1]? = some b ∧ (b == a) = true

/-- Whether position `i` (1-based) holds a `MustAlias`. -/
def mustAliasAt (ats : List LElt) (i : Nat) : Bool :=
  (ats[i - 1]?.map LElt.isMustAlias).getD false

/-- The number of `MustAlias` among the first positions in `l`. -/
def mustAliasCount (ats : List LElt) (l : List Nat) : Nat := (l.filter (mustAliasAt ats)).length

theorem forIn_count (ats : List LElt) (F : Nat → Option Bool × Nat → CM (ForInStep (Option Bool × Nat)))
    (hF : ∀ i c s st s', (F i (none, c)).run s = .ok (st, s') → ∃ e, ats[i - 1]? = some e ∧
      st = (if e.isMustAlias = true then
        (if (c + 1 == 2) = true then .done (some true, c + 1) else .yield (none, c + 1))
        else .yield (none, c))) :
    ∀ (l : List Nat) c, c ≤ 1 → ∀ s r s', (forIn l (none, c) F).run s = .ok (r, s') →
      (r.1 = some true ∧ 2 ≤ c + mustAliasCount ats l) ∨
      (r.1 = none ∧ c + mustAliasCount ats l < 2) := by
  intro l
  induction l with
  | nil => intro c hc s r s' h; cases h; exact .inr ⟨rfl, by simp [mustAliasCount]; omega⟩
  | cons i l ih =>
    intro c hc s r s' h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨e, he, rfl⟩ := hF i c s st s₁ h1
    have hma : mustAliasAt ats i = e.isMustAlias := by simp [mustAliasAt, he]
    have hcnt : mustAliasCount ats (i :: l) =
        (if e.isMustAlias = true then 1 else 0) + mustAliasCount ats l := by
      simp only [mustAliasCount, List.filter_cons, hma]
      split <;> simp; omega
    rw [hcnt]
    cases hm : e.isMustAlias
    · simp only [hm, Bool.false_eq_true, if_false] at h2 ⊢
      rcases ih c hc s₁ r s' h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact .inl ⟨h3, by omega⟩
      · exact .inr ⟨h3, by omega⟩
    · simp only [hm, if_true] at h2 ⊢
      by_cases h12 : (c + 1 == 2) = true
      · simp only [h12, if_true] at h2
        obtain ⟨rfl, -⟩ := h2
        have : c = 1 := by simp at h12; omega
        exact .inl ⟨rfl, by omega⟩
      · simp only [h12, Bool.false_eq_true, if_false] at h2
        have hc0 : c = 0 := by simp at h12; omega
        subst hc0
        rcases ih 1 (Nat.le_refl 1) s₁ r s' h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact .inl ⟨h3, by omega⟩
        · exact .inr ⟨h3, by omega⟩

/-- When `any_alias_candidate(na, fargs, argtypes)` holds (`Compiler/src/typeutils.jl:213-241`):
exactly when some position among the first `na` repeats an earlier `SlotNumber`/`SSAValue` of
`fargs`, or at least two of the first `na` arguments are `MustAlias`. -/
def AliasCandidate (na : Nat) (fargs : Option (List FArg)) (ats : Option (List LElt)) : Prop :=
  (∃ fa, fargs = some fa ∧ ∃ i ∈ List.range' 1 na, FargAliased fa i) ∨
  (∃ a, ats = some a ∧ 2 ≤ mustAliasCount a (List.range' 1 na))

-- The `MustAlias` part of `any_alias_candidate`: from `h`, the run of the counting loop and the
-- `match` after it, derive `hma : r = true ↔ 2 ≤ mustAliasCount a (List.range' 1 na)`.
set_option hygiene false in
macro "mustalias_tac" : tactic => `(tactic| (
  obtain ⟨st, s₁, hst, h⟩ := run_bind_inv h
  have key := forIn_count a _ ?hF (List.range' 1 na) 0 (Nat.zero_le 1) _ st s₁ hst
  case hF =>
    intro i c s₀ st₀ s₀' h₀
    obtain ⟨e, s₂, he, h₀⟩ := run_bind_inv h₀
    obtain ⟨he', -⟩ := eltAt_run_inv he
    refine ⟨e, he', ?_⟩
    cases hm : e.isMustAlias
    · simp only [hm, Bool.false_eq_true, if_false] at h₀ ⊢; cases h₀; rfl
    · simp only [hm, if_true] at h₀ ⊢
      split at h₀ <;> cases h₀ <;> simp_all
  have hma : r = true ↔ 2 ≤ mustAliasCount a (List.range' 1 na) := by
    rcases key with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · simp only [h3] at h; cases h; simp only [true_iff]; omega
    · simp only [h3] at h; cases h; simp only [Bool.false_eq_true, false_iff]; omega))

/-- `any_alias_candidate(na, fargs, argtypes)` (`Compiler/src/typeutils.jl:213-241`) is true exactly
when `AliasCandidate` holds: a repeated `SlotNumber`/`SSAValue` among the first `na` `fargs`, or
two `MustAlias` among the first `na` arguments. -/
def AnyAliasCandidateSpec : Prop :=
  ∀ na fargs ats, Returns (anyAliasCandidate na fargs ats) (fun r => r = true ↔ AliasCandidate na fargs ats)

theorem anyAliasCandidateSpec_proven : AnyAliasCandidateSpec := by
  intro na fargs ats s r s' h
  cases fargs with
  | none =>
    cases ats with
    | none =>
      simp only [anyAliasCandidate] at h; cases h
      simp [AliasCandidate]
    | some a =>
      simp only [anyAliasCandidate] at h
      mustalias_tac
      rw [hma]
      simp [AliasCandidate]
  | some fa =>
    simp only [anyAliasCandidate] at h
    obtain ⟨st, s₁, hst, h⟩ := run_bind_inv h
    have key := forIn_exists _ () true (FargAliased fa) _ ?hF s st s₁ hst
    case hF =>
      intro i _ s₀ st₀ s₀' hi
      obtain ⟨argI, s₂, ha, hi⟩ := run_bind_inv hi
      obtain ⟨ha', -⟩ := fargAt_run_inv ha
      cases hs : argI.isSlotOrSSA
      · simp only [hs, Bool.false_eq_true, if_false] at hi
        cases hi
        refine .inl ⟨rfl, fun ⟨a, h1, h2, _⟩ => ?_⟩
        rw [ha'] at h1; cases h1; rw [hs] at h2; cases h2
      · simp only [hs, if_true] at hi
        obtain ⟨st₁, s₃, hst₁, hi⟩ := run_bind_inv hi
        have inner := forIn_exists _ () true
          (fun j => ∃ b, fa[j - 1]? = some b ∧ (b == argI) = true) _ ?hG _ st₁ s₃ hst₁
        case hG =>
          intro j _ s₄ st₄ s₄' hj
          obtain ⟨b, s₅, hb, hj⟩ := run_bind_inv hj
          obtain ⟨hb', -⟩ := fargAt_run_inv hb
          cases he : (b == argI)
          · simp only [he, Bool.false_eq_true, if_false] at hj
            cases hj
            refine .inl ⟨rfl, fun ⟨b', h1, h2⟩ => ?_⟩
            rw [hb'] at h1; cases h1; rw [he] at h2; cases h2
          · simp only [he, if_true] at hj
            cases hj
            exact .inr ⟨rfl, b, hb', he⟩
        rcases inner with ⟨h1, h2⟩ | ⟨h1, j, hj, h2⟩
        · simp only [h1] at hi; cases hi
          refine .inl ⟨rfl, fun ⟨a, ha2, _, j, hj, b, hb, hba⟩ => ?_⟩
          rw [ha'] at ha2; cases ha2
          exact h2 j hj ⟨b, hb, hba⟩
        · simp only [h1] at hi; cases hi
          exact .inr ⟨rfl, argI, ha', hs, j, hj, h2⟩
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1] at h
      have hnf : ¬ ∃ i ∈ List.range' 1 na, FargAliased fa i := fun ⟨i, hi, hf⟩ => h2 i hi hf
      cases ats with
      | none =>
        cases h
        simp only [AliasCandidate, Bool.false_eq_true, false_iff, not_or]
        exact ⟨fun ⟨fa', hfa, hx⟩ => by cases hfa; exact hnf hx, fun ⟨_, h, _⟩ => by cases h⟩
      | some a =>
        mustalias_tac
        rw [hma]
        simp only [AliasCandidate]
        constructor
        · intro hc; exact .inr ⟨a, rfl, hc⟩
        · rintro (⟨fa', hfa, hx⟩ | ⟨a', ha, hc⟩)
          · cases hfa; exact absurd hx hnf
          · cases ha; exact hc
    · simp only [h1] at h; cases h
      simp only [AliasCandidate, true_iff]
      exact .inl ⟨fa, rfl, h2⟩

/-- `compute_alias_groups(na, fargs, argtypes)` "returns `nothing` when no aliasing is possible"
(`Compiler/src/typeutils.jl:187-191`): it returns `nothing` exactly when `AliasCandidate` fails,
and a grouping otherwise. -/
def ComputeAliasGroupsSpec : Prop :=
  ∀ na fargs ats, Returns (computeAliasGroups na fargs ats)
    (fun r => r = none ↔ ¬ AliasCandidate na fargs ats)

theorem computeAliasGroupsSpec_proven : ComputeAliasGroupsSpec := by
  intro na fargs ats s r s' h
  simp only [computeAliasGroups] at h
  obtain ⟨c, s₁, hc, h⟩ := run_bind_inv h
  have hiff := anyAliasCandidateSpec_proven na fargs ats s c s₁ hc
  cases c
  · simp only [Bool.not_false, if_true] at h; cases h
    simp only [true_iff]
    exact fun hx => by have := hiff.mpr hx; cases this
  · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    have hsome : r.isSome = true := by
      cases fargs <;> cases ats <;> simp only at h <;>
        first
        | (obtain ⟨g1, s₂, _, h⟩ := run_bind_inv h
           obtain ⟨g2, s₃, _, h⟩ := run_bind_inv h
           cases h; rfl)
        | (obtain ⟨g1, s₂, _, h⟩ := run_bind_inv h
           cases h; rfl)
        | (cases h; rfl)
    have hne : r ≠ none := by intro hr; rw [hr] at hsome; cases hsome
    simp only [hne, false_iff]
    exact fun hn => hn (hiff.mp rfl)

end JuliaLean.Proofs.Compiler.src.typeutils
