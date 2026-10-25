import JuliaLean.Platforms.MatchProofs

/-!
# Proofs about `select_platform`, `add_tag!` and the constructor defaults
-/

namespace JuliaLean.Platforms

open JuliaLean

/-! ## `isless` on strings is a strict total order -/

theorem char_lt_iff (a b : Char) : a < b ↔ a.toNat < b.toNat := Iff.rfl

theorem strLt_cons (x y : Char) (xs ys : Str) :
    strLt (x :: xs) (y :: ys) = true ↔ x.toNat < y.toNat ∨ (x = y ∧ strLt xs ys = true) := by
  show (if x < y then true else if y < x then false else strLt xs ys) = true ↔ _
  by_cases h1 : x < y
  · rw [if_pos h1]
    have h1' : x.toNat < y.toNat := h1
    simp [h1']
  · rw [if_neg h1]
    have h1' : ¬ x.toNat < y.toNat := h1
    by_cases h2 : y < x
    · rw [if_pos h2]
      have h2' : y.toNat < x.toNat := h2
      constructor
      · intro h; cases h
      · intro h
        rcases h with h | ⟨e, _⟩
        · exact absurd h h1'
        · subst e; omega
    · rw [if_neg h2]
      have h2' : ¬ y.toNat < x.toNat := h2
      have : x = y := Char.toNat_inj.1 (by omega)
      subst this
      simp

theorem strLt_irrefl : ∀ s : Str, strLt s s = false
  | [] => rfl
  | a :: as => by
    cases h : strLt (a :: as) (a :: as)
    · rfl
    · rw [strLt_cons] at h
      rcases h with h | ⟨_, h⟩
      · omega
      · rw [strLt_irrefl as] at h; cases h

theorem strLt_trans : ∀ a b c : Str, strLt a b = true → strLt b c = true → strLt a c = true
  | [], [], _, h, _ => by simp [strLt] at h
  | [], _ :: _, [], _, h => by simp [strLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [strLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [strLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    rw [strLt_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; omega
    · left; exact h1
    · left; exact h2
    · right; exact ⟨rfl, strLt_trans xs ys zs h1 h2⟩

theorem strLt_total : ∀ a b : Str, a ≠ b → strLt a b = true ∨ strLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | x :: xs, y :: ys, h => by
    rw [strLt_cons, strLt_cons]
    by_cases hxy : x = y
    · subst hxy
      have : xs ≠ ys := fun e => h (by rw [e])
      rcases strLt_total xs ys this with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · have : x.toNat ≠ y.toNat := fun e => hxy (Char.toNat_inj.1 e)
      by_cases hl : x.toNat < y.toNat
      · exact Or.inl (Or.inl hl)
      · exact Or.inr (Or.inl (by omega))

theorem strLt_asymm (a b : Str) (h : strLt a b = true) : strLt b a = false := by
  cases h' : strLt b a
  · rfl
  · have := strLt_trans a b a h h'
    rw [strLt_irrefl] at this; cases this

/-! ## The sort order of `select_platform` -/

theorem selLt_false_iff (x y : Nat × Str) :
    selLt x y = false ↔ (y.1 < x.1 ∨ (x.1 = y.1 ∧ strLt y.2 x.2 = false)) := by
  unfold selLt
  by_cases h : x.1 = y.1
  · simp [h]
  · have hne : (x.1 != y.1) = true := by simp [h]
    rw [if_pos hne]
    simp only [decide_eq_false_iff_not, h, false_and, or_false]
    constructor <;> intro <;> omega

theorem selLt_irrefl (x : Nat × Str) : selLt x x = false := by
  rw [selLt_false_iff]; exact Or.inr ⟨rfl, strLt_irrefl _⟩

theorem selLt_asymm (x y : Nat × Str) (h : selLt x y = true) : selLt y x = false := by
  rw [selLt_false_iff]
  have h' : ¬ selLt x y = false := by simp [h]
  rw [selLt_false_iff] at h'
  by_cases e : x.1 = y.1
  · have hs : strLt y.2 x.2 = true := by
      cases hs : strLt y.2 x.2
      · exact absurd (Or.inr ⟨e, hs⟩) h'
      · rfl
    exact Or.inr ⟨e.symm, strLt_asymm _ _ hs⟩
  · left; omega

theorem selLt_negtrans (x y z : Nat × Str) (h1 : selLt z y = false) (h2 : selLt y x = false) :
    selLt z x = false := by
  rw [selLt_false_iff] at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · left; omega
  · left; omega
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    cases h : strLt x.2 z.2
    · rfl
    · exfalso
      by_cases hyz : y.2 = z.2
      · rw [hyz] at h2; rw [h] at h2; cases h2
      · rcases strLt_total y.2 z.2 hyz with h3 | h3
        · rw [h1] at h3; cases h3
        · rw [strLt_trans _ _ _ h h3] at h2; cases h2

theorem firstMin_cons_some {α : Type} (lt : α → α → Bool) (x : α) (xs : List α) :
    ∃ y, firstMin lt (x :: xs) = some y := by
  unfold firstMin
  cases firstMin lt xs with
  | none => exact ⟨x, rfl⟩
  | some m =>
    dsimp only
    by_cases h : lt m x = true
    · exact ⟨m, by rw [if_pos h]⟩
    · exact ⟨x, by rw [if_neg h]⟩

theorem firstMin_spec {α : Type} (lt : α → α → Bool) (irr : ∀ x, lt x x = false)
    (asym : ∀ x y, lt x y = true → lt y x = false)
    (ntr : ∀ x y z, lt z y = false → lt y x = false → lt z x = false) :
    ∀ (xs : List α) (y : α), firstMin lt xs = some y → y ∈ xs ∧ ∀ z ∈ xs, lt z y = false
  | [], _, h => by simp [firstMin] at h
  | x :: xs, y, h => by
    unfold firstMin at h
    cases hm : firstMin lt xs with
    | none =>
      rw [hm] at h
      dsimp only at h
      cases h
      refine ⟨List.mem_cons_self, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact irr _
      · cases xs with
        | nil => cases hz
        | cons w ws =>
          obtain ⟨y', hy'⟩ := firstMin_cons_some lt w ws
          rw [hy'] at hm; cases hm
    | some m =>
      rw [hm] at h
      dsimp only at h
      have ⟨hmem, hmin⟩ := firstMin_spec lt irr asym ntr xs m hm
      by_cases hl : lt m x = true
      · rw [if_pos hl] at h; cases h
        refine ⟨List.mem_cons_of_mem _ hmem, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact asym _ _ hl
        · exact hmin z hz
      · rw [if_neg hl] at h; cases h
        refine ⟨List.mem_cons_self, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact irr _
        · exact ntr _ _ _ (hmin z hz) (by simpa using hl)

/-! ## `filterJ` and `mapJ` -/

theorem filterJ_spec {β : Type} (f : β → Jl Bool) :
    ∀ (xs ps : List β), filterJ f xs = .ok ps →
      (∀ x ∈ xs, f x = .ok true ∨ f x = .ok false) ∧ (∀ x, x ∈ ps ↔ x ∈ xs ∧ f x = .ok true)
  | [], ps, h => by
    simp only [filterJ, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | x :: xs, ps, h => by
    simp only [filterJ] at h
    obtain ⟨keep, hk, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have ⟨htot, hmem⟩ := filterJ_spec f xs rest hr
    refine ⟨fun y hy => ?_, fun y => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · cases keep <;> simp [hk]
      · exact htot y hy
    · cases keep
      · simp only [Bool.false_eq_true, if_false, hmem, List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · rw [hk] at h2; cases h2
          · exact ⟨h1, h2⟩
      · simp only [if_true, List.mem_cons, hmem]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, hk⟩
          · exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h2⟩

theorem mapJ_spec {β γ : Type} (f : β → Jl γ) :
    ∀ (xs : List β) (ys : List γ), mapJ f xs = .ok ys →
      (∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y) ∧ (∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y)
  | [], ys, h => by
    simp only [mapJ, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [mapJ] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have ⟨h1, h2⟩ := mapJ_spec f xs rest hr
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨x, List.mem_cons_self, hy⟩
      · obtain ⟨w, hw, hw'⟩ := h1 z hz; exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨y, List.mem_cons_self, hy⟩
      · obtain ⟨w, hw, hw'⟩ := h2 z hz; exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩

/-! ## `select_platform` -/

theorem selectKey_ok {host : Platform} {e : Platform × Str} {y : (Nat × Str) × (Platform × Str)}
    (h : (do return ((matchLoss e.1 host, ← triplet e.1), e) : Jl _) = .ok y) :
    ∃ t, triplet e.1 = .ok t ∧ y = ((matchLoss e.1 host, t), e) := by
  obtain ⟨t, ht, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨t, ht, h.symm⟩

theorem selectBest_proven : SelectBest := by
  intro usem order es host r h
  unfold selectPlatform at h
  obtain ⟨ps, hps, h⟩ := bind_ok h
  have ⟨htot, hmem⟩ := filterJ_spec _ es ps hps
  rcases ps with _ | ⟨e, _ | ⟨e2, rest⟩⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    intro x hx
    rcases htot x hx with h1 | h1
    · have := (hmem x).2 ⟨hx, h1⟩; simp at this
    · exact h1
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have he := (hmem e).1 List.mem_cons_self
    refine ⟨e.1, he.1, he.2, fun q hq hqm => ?_⟩
    have hq' := (hmem q).2 ⟨hq, hqm⟩
    simp only [List.mem_singleton] at hq'; subst hq'
    refine ⟨Nat.le_refl _, fun _ tp tq h1 h2 => ?_⟩
    rw [h1] at h2; cases h2; exact strLt_irrefl _
  · obtain ⟨keyed, hk, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have ⟨hk1, hk2⟩ := mapJ_spec _ _ keyed hk
    obtain ⟨y0, hy0, _⟩ := hk2 e List.mem_cons_self
    obtain ⟨w, ws, rfl⟩ : ∃ w ws, keyed = w :: ws := by
      cases keyed with
      | nil => cases hy0
      | cons w ws => exact ⟨w, ws, rfl⟩
    obtain ⟨y, hy⟩ := firstMin_cons_some (fun x y => selLt x.1 y.1) w ws
    rw [hy]
    have ⟨hymem, hymin⟩ := firstMin_spec (fun x y => selLt x.1 y.1) (fun x => selLt_irrefl _)
      (fun x y h => selLt_asymm _ _ h) (fun x y z h1 h2 => selLt_negtrans x.1 y.1 z.1 h1 h2) _ y hy
    obtain ⟨e', he', hge'⟩ := hk1 y hymem
    obtain ⟨t, ht, rfl⟩ := selectKey_ok hge'
    have hm' := (hmem e').1 he'
    refine ⟨e'.1, hm'.1, hm'.2, fun q hq hqm => ?_⟩
    obtain ⟨z, hz, hgz⟩ := hk2 q ((hmem q).2 ⟨hq, hqm⟩)
    obtain ⟨tq', htq', rfl⟩ := selectKey_ok hgz
    have hmn := hymin _ hz
    simp only at hmn
    rw [selLt_false_iff] at hmn
    refine ⟨by omega, fun hl tp tq h1 h2 => ?_⟩
    rw [h1] at ht; cases ht
    rw [h2] at htq'; cases htq'
    rcases hmn with hmn | ⟨_, hmn⟩
    · omega
    · exact hmn

/-! ## `add_tag!` -/

theorem all_not_isNono (l : Str) : l.all (fun c => !isNono c) = !(l.any isNono) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [List.all_cons, List.any_cons, ih]

theorem addTagRejectsNonos_proven : AddTagRejectsNonos := by
  intro lc hlc tags tag value
  have hv : (lower lc value).any isNono = value.any isNono := by
    simp only [lower, List.any_map]
    congr 1
    funext c
    exact isNono_lc hlc c
  rw [all_not_isNono, all_not_isNono]
  unfold addTag
  dsimp only
  rw [hv]
  cases h1 : tag.any isNono <;> cases h2 : value.any isNono <;>
    simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end JuliaLean.Platforms
