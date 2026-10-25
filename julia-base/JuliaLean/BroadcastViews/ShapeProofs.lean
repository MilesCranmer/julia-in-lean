import JuliaLean.BroadcastViews.Shape

/-! Properties of broadcast shape combination and their proofs or refutations. -/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `Broadcast.broadcast_shape(s, ss...)` on integer size tuples returns the documented
combination: as many dimensions as the longest tuple, and in each dimension every input extent
is 1 or equal to the result extent, which is one of the input extents. It throws only
`DimensionMismatch`, and only when two input extents of one dimension differ and neither is 1. -/
def ShapeCombination : Prop :=
  ∀ (s : List I64) (ss : List (List I64)),
    (∀ out, broadcastShape s ss = .ok out →
      out.length = maxLen (s :: ss) ∧
      (∀ d, ∀ t ∈ s :: ss, ext t d = 1 ∨ ext t d = ext out d) ∧
      (∀ d, ∃ t ∈ s :: ss, ext t d = ext out d)) ∧
    (∀ e, broadcastShape s ss = .error e →
      e = .dimensionMismatch ∧
      ∃ d, ∃ t ∈ s :: ss, ∃ t' ∈ s :: ss, ext t d ≠ 1 ∧ ext t' d ≠ 1 ∧ ext t d ≠ ext t' d)

/-- `_bcs1` on a size and an axis (in either order) agrees with integer sizes: it throws exactly
when both lengths differ from 1 and from each other, and otherwise returns an entry whose length
is the non-singleton one. -/
def ShapeMixedSingleton : Prop :=
  ∀ x y : Dim,
    (bcs1Mixed x y = .error .dimensionMismatch ↔ (x.len ≠ 1 ∧ y.len ≠ 1 ∧ x.len ≠ y.len)) ∧
    ∀ z, bcs1Mixed x y = .ok z → z.len = (if x.len = 1 then y.len else x.len)

private theorem ext_nil (d : Nat) : ext [] d = 1 := by simp [ext]
private theorem ext_cons_zero (x : I64) (s : List I64) : ext (x :: s) 0 = x.val := by simp [ext]
private theorem ext_cons_succ (x : I64) (s : List I64) (d : Nat) : ext (x :: s) (d + 1) = ext s d := by
  simp [ext]

private theorem bcs1_ok {a b x : I64} (h : bcs1 a b = .ok x) :
    (a.val = 1 ∨ a.val = x.val) ∧ (b.val = 1 ∨ b.val = x.val) ∧ (x.val = a.val ∨ x.val = b.val) := by
  unfold bcs1 at h
  by_cases h1 : a.val = 1
  · simp [h1] at h; subst h; simp [h1]
  · by_cases h2 : b.val = 1
    · simp [h1, h2] at h; subst h; simp [h2]
    · by_cases h3 : a.val = b.val
      · simp [h2, h3] at h; subst h; simp [h3]
      · simp [h1, h2, h3] at h

private theorem bcs1_err {a b : I64} {e : Err} (h : bcs1 a b = .error e) :
    e = .dimensionMismatch ∧ a.val ≠ 1 ∧ b.val ≠ 1 ∧ a.val ≠ b.val := by
  unfold bcs1 at h
  by_cases h1 : a.val = 1
  · simp [h1] at h
  · by_cases h2 : b.val = 1
    · simp [h1, h2] at h
    · by_cases h3 : a.val = b.val
      · simp [h2, h3] at h
      · simp [h1, h2, h3] at h; exact ⟨h.symm, h1, h2, h3⟩

/-- Per-dimension facts about a successful `_bcs`. -/
private def BcsOk (a b u : List I64) : Prop :=
  u.length = max a.length b.length ∧
    ∀ d, (ext a d = 1 ∨ ext a d = ext u d) ∧ (ext b d = 1 ∨ ext b d = ext u d) ∧
      (ext u d = ext a d ∨ ext u d = ext b d)

private theorem bcs_ok : ∀ (a b u : List I64), bcs a b = .ok u → BcsOk a b u
  | [], [], u, h => by
    simp [bcs] at h; subst h
    exact ⟨rfl, fun d => by simp [ext_nil]⟩
  | [], b :: bs, u, h => by
    simp only [bcs] at h
    cases hr : bcs [] bs with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hl, hd⟩ := bcs_ok [] bs r hr
      refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
      cases d with
      | zero => simp [ext_nil, ext_cons_zero]
      | succ d =>
        have := hd d
        simp only [ext_nil, ext_cons_succ] at this ⊢
        exact this
  | a :: as, [], u, h => by
    simp only [bcs] at h
    cases hr : bcs as [] with
    | error e => rw [hr] at h; cases h
    | ok r =>
      rw [hr] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hl, hd⟩ := bcs_ok as [] r hr
      refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
      cases d with
      | zero => simp [ext_nil, ext_cons_zero]
      | succ d =>
        have := hd d
        simp only [ext_nil, ext_cons_succ] at this ⊢
        exact this
  | a :: as, b :: bs, u, h => by
    simp only [bcs] at h
    cases hx : bcs1 a b with
    | error e => rw [hx] at h; cases h
    | ok x =>
      rw [hx] at h
      cases hr : bcs as bs with
      | error e => simp only [bind, Except.bind, hr] at h; cases h
      | ok r =>
        simp only [bind, Except.bind, hr, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hd⟩ := bcs_ok as bs r hr
        refine ⟨by simp at hl ⊢; omega, fun d => ?_⟩
        cases d with
        | zero =>
          simp only [ext_cons_zero]
          exact bcs1_ok hx
        | succ d =>
          simp only [ext_cons_succ]
          exact hd d

private theorem bcs_err : ∀ (a b : List I64) (e : Err), bcs a b = .error e →
    e = .dimensionMismatch ∧ ∃ d, ext a d ≠ 1 ∧ ext b d ≠ 1 ∧ ext a d ≠ ext b d
  | [], [], e, h => by simp [bcs] at h
  | [], b :: bs, e, h => by
    simp only [bcs] at h
    cases hr : bcs [] bs with
    | error e' =>
      rw [hr] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨_, d, h1, _, _⟩ := bcs_err [] bs e' hr
      exact absurd (ext_nil d) h1
    | ok r => rw [hr] at h; cases h
  | a :: as, [], e, h => by
    simp only [bcs] at h
    cases hr : bcs as [] with
    | error e' =>
      rw [hr] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨_, d, _, h2, _⟩ := bcs_err as [] e' hr
      exact absurd (ext_nil d) h2
    | ok r => rw [hr] at h; cases h
  | a :: as, b :: bs, e, h => by
    simp only [bcs] at h
    cases hx : bcs1 a b with
    | error e' =>
      rw [hx] at h
      simp only [bind, Except.bind, Except.error.injEq] at h
      subst h
      obtain ⟨he, h1, h2, h3⟩ := bcs1_err hx
      exact ⟨he, 0, by simpa [ext_cons_zero] using h1, by simpa [ext_cons_zero] using h2,
        by simpa [ext_cons_zero] using h3⟩
    | ok x =>
      rw [hx] at h
      cases hr : bcs as bs with
      | error e' =>
        simp only [bind, Except.bind, hr, Except.error.injEq] at h
        subst h
        obtain ⟨he, d, h1, h2, h3⟩ := bcs_err as bs e' hr
        exact ⟨he, d + 1, by simpa [ext_cons_succ] using h1, by simpa [ext_cons_succ] using h2,
          by simpa [ext_cons_succ] using h3⟩
      | ok r => simp only [bind, Except.bind, hr, pure, Except.pure] at h; cases h

private theorem maxLen_cons (s : List I64) (ss : List (List I64)) :
    maxLen (s :: ss) = max s.length (maxLen ss) := rfl

theorem shapeCombination : ShapeCombination := by
  intro s ss
  induction ss generalizing s with
  | nil =>
    refine ⟨fun out h => ?_, fun e h => ?_⟩
    · simp [broadcastShape] at h; subst h
      refine ⟨by simp [maxLen], fun d t ht => ?_, fun d => ⟨s, by simp, rfl⟩⟩
      simp at ht; subst ht; exact Or.inr rfl
    · simp [broadcastShape] at h
  | cons t ts ih =>
    refine ⟨fun out h => ?_, fun e h => ?_⟩
    · simp only [broadcastShape] at h
      cases hu : bcs s t with
      | error e => rw [hu] at h; cases h
      | ok u =>
        simp only [bind, Except.bind, hu] at h
        obtain ⟨hl, hd⟩ := bcs_ok s t u hu
        obtain ⟨hl', hall, hex⟩ := (ih u).1 out h
        refine ⟨?_, fun d x hx => ?_, fun d => ?_⟩
        · rw [hl', maxLen_cons, maxLen_cons, maxLen_cons, hl]; omega
        · have hud := hall d u (by simp)
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · rcases (hd d).1 with h1 | h1
            · exact Or.inl h1
            · rcases hud with h2 | h2
              · exact Or.inl (h1.trans h2)
              · exact Or.inr (h1.trans h2)
          · rcases (hd d).2.1 with h1 | h1
            · exact Or.inl h1
            · rcases hud with h2 | h2
              · exact Or.inl (h1.trans h2)
              · exact Or.inr (h1.trans h2)
          · exact hall d x (by simp [hx])
        · obtain ⟨y, hy, hye⟩ := hex d
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rcases (hd d).2.2 with h1 | h1
            · exact ⟨s, by simp, h1.symm.trans hye⟩
            · exact ⟨t, by simp, h1.symm.trans hye⟩
          · exact ⟨y, by simp [hy], hye⟩
    · simp only [broadcastShape] at h
      cases hu : bcs s t with
      | error e' =>
        simp only [bind, Except.bind, hu, Except.error.injEq] at h
        subst h
        obtain ⟨he, d, h1, h2, h3⟩ := bcs_err s t e' hu
        exact ⟨he, d, s, by simp, t, by simp, h1, h2, h3⟩
      | ok u =>
        simp only [bind, Except.bind, hu] at h
        obtain ⟨he, d, x, hx, x', hx', h1, h2, h3⟩ := (ih u).2 e h
        refine ⟨he, d, ?_⟩
        have hpick : ∀ y ∈ u :: ts, ∃ z ∈ s :: t :: ts, ext z d = ext y d := by
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rcases ((bcs_ok s t y hu).2 d).2.2 with h4 | h4
            · exact ⟨s, by simp, h4.symm⟩
            · exact ⟨t, by simp, h4.symm⟩
          · exact ⟨y, by simp [hy], rfl⟩
        obtain ⟨z, hz, hze⟩ := hpick x hx
        obtain ⟨z', hz', hze'⟩ := hpick x' hx'
        exact ⟨z, hz, z', hz', by rw [hze]; exact h1, by rw [hze']; exact h2, by rw [hze, hze']; exact h3⟩

/-- `broadcast_shape((3,), (OneTo(1),))` throws `DimensionMismatch` although `OneTo(1)` is a
singleton. -/
theorem bcs1Mixed_3_oneTo1 : bcs1Mixed (.size (i64 3)) (.axis ⟨i64 1⟩) = .error .dimensionMismatch := by
  decide

theorem shapeMixedSingleton_refuted : ¬ ShapeMixedSingleton := by
  intro h
  have := ((h (.size (i64 3)) (.axis ⟨i64 1⟩)).1.mp bcs1Mixed_3_oneTo1).2.1
  exact this (by decide)

end JuliaLean.BroadcastViews
