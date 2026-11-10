import JuliaLean.Proofs.Compiler.src.typelimits.Bottom

/-!
`tmerge_fast_path` (`Compiler/src/typelimits.jl:413-425`) and the `LimitedAccuracy` cause sets
(`union_causes`, `Compiler/src/typelimits.jl:427-435`).
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

theorem bind_ok_inv {α β : Type} {m : CM α} {f : α → CM β} {s s' : Nat} {r : β}
    (h : (m >>= f).run s = .ok (r, s')) :
    ∃ v s₁, m.run s = .ok (v, s₁) ∧ (f v).run s₁ = .ok (r, s') := by
  rw [StateT.run_bind] at h
  cases hm : m.run s with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem pure_ok_inv {α : Type} {x r : α} {s s' : Nat}
    (h : (pure x : CM α).run s = .ok (r, s')) : r = x ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

/-- The fast path only answers with one of its arguments, and only when the other argument is
`Union{}`, egal to it, or `⊑` it (as `⊑` answered during the call). So, wherever `⊑` is
reflexive and has `Union{}` as least element, its answer is an upper bound of both arguments, the
property `tmerge` needs from it. With `Union{}` on either side it answers with the other
argument, without querying `⊑`. -/
def TmergeFastPathSound : Prop :=
  (∀ n E L (x : LElt) s, (tmergeFastPath n E L bot x).run s = .ok (some x, s) ∧
    (tmergeFastPath n E L x bot).run s = .ok (some x, s)) ∧
  ∀ n E L (a b r : LElt) s s', (tmergeFastPath n E L a b).run s = .ok (some r, s') →
    (r = b ∧ (a.isBottom = true ∨ ∃ s₁ s₂, (sqsub n E L a b).run s₁ = .ok (true, s₂))) ∨
    (r = a ∧ (b.isBottom = true ∨ (∃ s₁ s₂, (eltEgal n E a b).run s₁ = .ok (true, s₂)) ∨
      ∃ s₁ s₂, (sqsub n E L b a).run s₁ = .ok (true, s₂)))

theorem tmergeFastPathSound_proven : TmergeFastPathSound := by
  refine ⟨fun n E L x s => ⟨fastPath_bot_left n E L x s, fastPath_bot_right n E L x s⟩, ?_⟩
  intro n E L a b r s s' h
  unfold tmergeFastPath at h
  by_cases ha : a.isBottom = true
  · simp only [ha, if_true] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h
    cases h1; exact .inl ⟨rfl, .inl ha⟩
  simp only [ha, Bool.false_eq_true, if_false] at h
  by_cases hb : b.isBottom = true
  · simp only [hb, if_true] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h
    cases h1; exact .inr ⟨rfl, .inl hb⟩
  simp only [hb, Bool.false_eq_true, if_false] at h
  obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
  cases e
  · simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨suba, s₂, hsa, h⟩ := bind_ok_inv h
    cases suba
    · simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨subb, s₃, hsb, h⟩ := bind_ok_inv h
      cases subb
      · simp only [Bool.and_false, Bool.false_eq_true, if_false] at h
        cases h
      · simp only [Bool.false_and, Bool.false_eq_true, if_false, if_true] at h
        obtain ⟨si, s₄, -, h⟩ := bind_ok_inv h
        cases si
        · cases h
        · obtain ⟨h1, -⟩ := pure_ok_inv h
          cases h1; exact .inr ⟨rfl, .inr (.inr ⟨s₂, s₃, hsb⟩)⟩
    · simp only [if_true] at h
      obtain ⟨si, s₃, -, h⟩ := bind_ok_inv h
      cases si
      · simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨subb, s₄, hsb, h⟩ := bind_ok_inv h
        cases subb
        · simp only [Bool.and_false, Bool.false_eq_true, if_false] at h
          cases h
        · simp only [Bool.and_self, if_true] at h
          obtain ⟨h1, -⟩ := pure_ok_inv h
          cases h1; exact .inr ⟨rfl, .inr (.inr ⟨s₃, s₄, hsb⟩)⟩
      · simp only [if_true] at h
        obtain ⟨h1, -⟩ := pure_ok_inv h
        cases h1; exact .inl ⟨rfl, .inr ⟨s₁, s₂, hsa⟩⟩
  · simp only [if_true] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h
    cases h1; exact .inr ⟨rfl, .inr (.inl ⟨s, s₁, he⟩)⟩

end JuliaLean.Proofs.Compiler.src.typelimits
