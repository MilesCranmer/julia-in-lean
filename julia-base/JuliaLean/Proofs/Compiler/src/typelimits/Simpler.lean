import JuliaLean.Proofs.Compiler.src.typelimits.Limits

/-!
`issimplertype` (`Compiler/src/typelimits.jl:340-411`) and `tmerge(::ConstsLattice)`
(`Compiler/src/typelimits.jl:763-773`).
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- `x === x` on lattice elements, from `x === x` on Julia objects. -/
theorem eltEgal_refl (hr : EgalReflexive) :
    ∀ n E (a : LElt) s r s', (eltEgal n E a a).run s = .ok (r, s') → r = true := by
  intro n
  induction n with
  | zero => intro E a s r s' h; cases h
  | succ n ih =>
    intro E a s r s' h
    cases a with
    | ty x => exact hr n E x s r s' h
    | const x => exact hr n E x s r s' h
    | partialStruct t u f ui fi =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false] at h
      exact hr n E t s r s' h
    | conditional sl d a b i =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      rw [ih E a s e s₁ he] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      exact ih E b _ r s' h
    | interConditional sl a b =>
      simp only [eltEgal, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      rw [ih E a s e s₁ he] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      exact ih E b _ r s' h
    | mustAlias sl d v i f =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      rw [ih E v s e s₁ he] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      exact ih E f _ r s' h
    | interMustAlias sl v i f =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      rw [ih E v s e s₁ he] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      exact ih E f _ r s' h
    | partialTypeVar tv l u =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self] at h
      exact (pure_ok_inv h).1.symm ▸ rfl
    | limitedAccuracy t c ci =>
      simp only [eltEgal, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      exact ih E t s r s' h
    | partialOpaque t e p sr =>
      simp only [eltEgal, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true,
        if_false] at h
      obtain ⟨b, s₁, hb, h⟩ := bind_ok_inv h
      rw [hr n E t s b s₁ hb] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      exact ih E e _ r s' h
    | partialTask f => exact ih E f s r s' (by simpa only [eltEgal] using h)

/-- `issimplertype(𝕃, a, b)` (assumes `b ⊑ a`):
* every element that is not `LimitedAccuracy` is simpler than itself;
* a native type `T` is simpler than `b` exactly when `T === b` or `issimpleenoughtype(T)`;
* a `PartialStruct` is simpler than `b` only when `b` is egal to it, a `Const`, or a
  `PartialStruct` (`Compiler/src/typelimits.jl:342-411`, the branch at lines 345-355).
Assumes `===` is reflexive on Julia objects. -/
def IssimplertypeSpec : Prop :=
  EgalReflexive →
  (∀ n E L (a : LElt) s r s', a.isLimited = false →
    (issimplertype n E L a a).run s = .ok (r, s') → r = true) ∧
  (∀ n E L (t : Val) (b : LElt) s r s', t.isType = true → b.isLimited = false →
    (issimplertype (n + 1) E L (.ty t) b).run s = .ok (r, s') →
    (∃ s₁ s₂, (eltEgal n E (.ty t) b).run s₁ = .ok (true, s₂)) ∨
    ∃ s₁ s₂, (issimpleenoughtype n E t).run s₁ = .ok (r, s₂)) ∧
  (∀ n E L atyp us fs ui fi (b : LElt) s s', b.isLimited = false →
    (issimplertype (n + 1) E L (.partialStruct atyp us fs ui fi) b).run s = .ok (true, s') →
    (∃ s₁ s₂, (eltEgal n E (.partialStruct atyp us fs ui fi) b).run s₁ = .ok (true, s₂)) ∨
    b.isConst = true ∨ b.isPartialStruct = true)

theorem issimplertypeSpec_proven : IssimplertypeSpec := by
  intro hr
  refine ⟨fun n E L a s r s' ha h => ?_, fun n E L t b s r s' ht hb h => ?_,
    fun n E L atyp us fs ui fi b s s' hb h => ?_⟩
  · cases n with
    | zero => cases h
    | succ n =>
      unfold issimplertype at h
      simp only [ha, Bool.or_self, Bool.false_eq_true, if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      rw [eltEgal_refl hr n E a s e s₁ he] at h
      simp only [if_true] at h
      exact (pure_ok_inv h).1
  · unfold issimplertype at h
    have ha : (LElt.ty t).isLimited = false := rfl
    simp only [ha, hb, Bool.or_false, Bool.false_eq_true, if_false] at h
    obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
    cases e
    · simp only [Bool.false_eq_true, if_false, ht, if_true] at h
      exact .inr ⟨s₁, s', h⟩
    · exact .inl ⟨s, s₁, he⟩
  · unfold issimplertype at h
    have ha : (LElt.partialStruct atyp us fs ui fi).isLimited = false := rfl
    simp only [ha, hb, Bool.or_false, Bool.false_eq_true, if_false] at h
    obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
    cases e
    · simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨w, _, _, h⟩ := bind_ok_inv h
      obtain ⟨q, _, _, h⟩ := bind_ok_inv h
      cases q
      · simp only [Bool.not_false, if_true] at h
        exact absurd (pure_ok_inv h).1 (by decide)
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        by_cases hcp : (b.isConst || b.isPartialStruct) = true
        · simp only [Bool.or_eq_true] at hcp
          exact .inr hcp
        · rw [if_neg hcp] at h
          exact absurd (pure_ok_inv h).1 (by decide)
    · exact .inl ⟨s, s₁, he⟩

/-! ## `tmerge(::ConstsLattice)` -/

/-- `tmerge(::ConstsLattice, a, b)`: a `Const` or `PartialTypeVar` merged with itself is returned
unchanged, and two elements that are neither are handed to `JLTypeLattice` unchanged
(`Compiler/src/typelimits.jl:763-773`). Assumes `===` is reflexive on Julia objects. -/
def TmergeConstsSpec : Prop :=
  EgalReflexive →
  (∀ n E (a : LElt) s r s', (a.isConst || a.isPartialTypeVar) = true →
    (tmerge (n + 1) E .consts a a).run s = .ok (r, s') → r = a) ∧
  (∀ n E (a b : LElt) s, (a.isConst || a.isPartialTypeVar) = false →
    (b.isConst || b.isPartialTypeVar) = false →
    (tmerge (n + 1) E .consts a b).run s = (tmerge n E .jlType a b).run s)

theorem tmergeConstsSpec_proven : TmergeConstsSpec := by
  intro hr
  refine ⟨fun n E a s r s' ha h => ?_, fun n E a b s ha hb => ?_⟩
  · simp only [tmerge, ha, Bool.and_self, if_true] at h
    obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
    rw [eltEgal_refl hr n E a s e s₁ he] at h
    simp only [if_true] at h
    exact (pure_ok_inv h).1
  · simp only [tmerge, ha, hb, Bool.and_self, Bool.false_eq_true, if_false]

end JuliaLean.Proofs.Compiler.src.typelimits
