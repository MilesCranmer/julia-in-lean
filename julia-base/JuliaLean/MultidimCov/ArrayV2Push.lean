import JuliaLean.MultidimCov.ArrayV2VectorProps

/-!
Repeated `push!`/`pushfirst!` on `Vector`: the growth primitives keep the
memory below `2^60` slots as long as the data window plus the pushed items stay
below `2^59` slots (`_growend!` reallocates only when the memory is full, to at
most `overallocation(memlen)` slots; `_growbeg!` to at most
`overallocation(len)`). These bounds let the loops of `_append!`, `_prepend!`,
`_collect`, `_deleteat!` and friends be proven for every length.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-! ### Size bounds of the growth primitives -/

theorem m1171_bnd {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) (a' : Arr α) (h : m1171 a delta n = .ok a') :
    a'.off ≤ a.off ∧ (a'.mem.len = a.mem.len ∨ a'.mem.len = max (m1102 a.mem.len) (a.off - 1 + (n + delta))) := by
  obtain ⟨_, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1171 at h
  rw [checkedAdd_ok (by omega) (by omega), bind_ok] at h
  simp only [] at h
  rw [if_neg (by omega), checkedAdd_ok (by omega) (by omega), bind_ok] at h
  have hq4 : Int.tdiv (n + delta) 4 = (n + delta) / 4 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hq8 : Int.tdiv (n + delta) 8 = (n + delta) / 8 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [hq4, hq8] at h
  split at h
  · rename_i hc
    rw [refCopy_ok (by omega) (by omega) (by omega), bind_ok, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨by simp only []; omega, Or.inl (by simp)⟩
  · rw [refCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok, pure_ok,
      Except.ok.injEq] at h
    subst h
    exact ⟨Int.le_refl _, Or.inr (by simp [m1114])⟩

theorem m1212_bnd {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) (a' : Arr α) (h : m1212 a delta = .ok a') :
    a'.off ≤ a.off ∧ (a'.mem.len = a.mem.len ∨
      (a.mem.len < a.off - 1 + (n + delta) ∧ a'.mem.len = max (m1102 a.mem.len) (a.off - 1 + (n + delta)))) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1212 at h
  rw [toInt_ok (by omega) (by omega), bind_ok, if_neg (by omega)] at h
  simp only [hn] at h
  rw [wrap64_id (x := a.off - 1) (by omega) (by omega),
    wrap64_id (x := a.mem.len - (a.off - 1)) (by omega) (by omega),
    wrap64_id (x := a.mem.len - (a.off - 1) - n) (by omega) (by omega),
    wrap64_id (x := n + delta) (by omega) (by omega)] at h
  split at h
  · rename_i hc
    revert h
    cases e : m1171 a delta n with
    | error err => intro h; cases h
    | ok a1 =>
      intro h
      rw [bind_ok, pure_ok, Except.ok.injEq] at h
      subst h
      obtain ⟨b1, b2⟩ := m1171_bnd ha hd0 hd1 a1 e
      refine ⟨b1, ?_⟩
      rcases b2 with b2 | b2
      · exact Or.inl b2
      · exact Or.inr ⟨by omega, b2⟩
  · rw [pure_ok, bind_ok, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨Int.le_refl _, Or.inl rfl⟩

theorem m1116_bnd {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) (a' : Arr α) (h : m1116 a delta n = .ok a') :
    (a'.mem.len = a.mem.len ∨ a'.mem.len = max (m1102 n) (n + 2 * delta + 1)) ∧
    (1 ≤ delta → a.mem.len < n + delta → a'.off + delta ≤ a'.mem.len) := by
  obtain ⟨_, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1116 at h
  rw [checkedAdd_ok (by omega) (by omega), bind_ok] at h
  simp only [] at h
  rw [if_neg (by omega), checkedMul_ok (by omega) (by omega), bind_ok,
    checkedAdd_ok (by omega) (by omega), bind_ok, checkedAdd_ok (by omega) (by omega), bind_ok] at h
  have hm := m1102_bounds (n := n) hn0 (by omega)
  split at h
  · rename_i hc
    have hq : Int.tdiv (a.mem.len - (n + delta)) 2 = (a.mem.len - (n + delta)) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by omega)
    rw [hq, memCopy_ok (by omega) (by omega) (by omega), bind_ok, pure_ok, Except.ok.injEq] at h
    subst h
    exact ⟨Or.inl (by simp), fun _ h2 => by omega⟩
  · have hq : Int.tdiv (max (m1102 n) (n + 2 * delta + 1) - (n + delta)) 2 =
        (max (m1102 n) (n + 2 * delta + 1) - (n + delta)) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by rw [Int.max_def]; split <;> omega)
    rw [hq, memCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok, pure_ok,
      Except.ok.injEq] at h
    subst h
    refine ⟨Or.inr (by simp [m1114]), fun h1 _ => ?_⟩
    simp only [Mem.copy_len, m1114, Mem.undef_len, Int.max_def]
    split <;> omega

theorem m1151_bnd {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) (a' : Arr α) (h : m1151 a delta = .ok a') :
    (a'.mem.len = a.mem.len ∨ a'.mem.len = max (m1102 n) (n + 2 * delta + 1)) ∧
    (1 ≤ delta → a.mem.len < n + delta → a'.off + delta ≤ a'.mem.len) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1151 at h
  rw [toInt_ok (by omega) (by omega), bind_ok] at h
  by_cases hz : delta = 0
  · subst hz
    rw [if_pos rfl, Except.ok.injEq] at h
    subst h
    exact ⟨Or.inl rfl, fun h1 => by omega⟩
  · rw [if_neg hz, if_neg (by omega)] at h
    simp only [hn] at h
    rw [checkedAdd_ok (by omega) (by omega), bind_ok] at h
    split at h
    · rw [pure_ok, Except.ok.injEq] at h
      subst h
      exact ⟨Or.inl rfl, fun _ h2 => by omega⟩
    · revert h
      cases e : m1116 a delta n with
      | error err => intro h; cases h
      | ok a1 =>
        intro h
        rw [bind_ok, pure_ok, Except.ok.injEq] at h
        subst h
        exact m1116_bnd ha hd0 hd1 a1 e

/-! ### One push -/

theorem small_after {m m' w : Int} (hm0 : 0 ≤ m) (hw : w ≤ 576460752303423488)
    (h : m' = m ∨ (m < w ∧ m' = max (m1102 m) w)) (hs : m ≤ 1152921504606846976) : m' ≤ 1152921504606846976 := by
  rcases h with h | ⟨h1, h2⟩
  · omega
  · have := m1102_bounds (n := m) hm0 (by omega)
    rw [h2, Int.max_def]; split <;> omega

theorem m1212_vec {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hb : a.off - 1 + n + delta ≤ 576460752303423488) :
    ∃ a', m1212 a delta = .ok a' ∧ VecOK a' (n + delta) ∧ a'.off ≤ a.off ∧
      (∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  obtain ⟨a', e, hv', hval, hp⟩ := m1212_spec ha hd0 (by omega)
  obtain ⟨b1, b2⟩ := m1212_bnd ha hd0 (by omega) a' e
  refine ⟨a', e, ⟨hv', hval, ?_⟩, b1, hp⟩
  unfold Small
  exact small_after (by omega) (w := a.off - 1 + (n + delta)) (by omega) b2 hs

theorem m1366_vec {a : Arr α} {n : Int} (ha : VecOK a n) (hb : a.off - 1 + n + 1 ≤ 576460752303423488) (x : α) :
    ∃ a', m1366 a x = .ok a' ∧ VecOK a' (n + 1) ∧ a'.off ≤ a.off ∧ contents a' = contents a ++ [some x] := by
  obtain ⟨a', e, _, _, hc⟩ := m1366_spec ha x
  obtain ⟨a1, e1, ⟨hv1, hval1, hs1⟩, ho1, _⟩ := m1212_vec ha (delta := 1) (by omega) hb
  have : a' = m1057 a1 x (length a1) := by
    unfold m1366 at e; rw [e1, bind_ok, pure_ok, Except.ok.injEq] at e; exact e.symm
  subst this
  refine ⟨_, e, ⟨by unfold IsVec at hv1 ⊢; simpa [m1057] using hv1, by simpa [m1057, Valid, length] using hval1,
    by simpa [m1057, Small] using hs1⟩, by simpa [m1057] using ho1, hc⟩

theorem m1782_vec {a : Arr α} {n : Int} (ha : VecOK a n) (hb : n + 1 ≤ 576460752303423488) (x : α) :
    ∃ a', m1782 a x = .ok a' ∧ VecOK a' (n + 1) ∧ contents a' = some x :: contents a := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  obtain ⟨a', e, _, _, hc⟩ := m1782_spec ha x
  obtain ⟨a1, e1, hv1, hval1, _⟩ := m1151_spec ha (delta := 1) (by omega) (by omega)
  obtain ⟨b1, _⟩ := m1151_bnd ha (delta := 1) (by omega) (by omega) a1 e1
  have : a' = m1057 a1 x 1 := by
    unfold m1782 at e; rw [e1, bind_ok, pure_ok, Except.ok.injEq] at e; exact e.symm
  subst this
  have hm := m1102_bounds (n := n) hn0 (by omega)
  refine ⟨_, e, ⟨by unfold IsVec at hv1 ⊢; simpa [m1057] using hv1, by simpa [m1057, Valid, length] using hval1, ?_⟩, hc⟩
  simp only [Small, m1057, setU_mem_len]
  rcases b1 with b1 | b1
  · omega
  · rw [b1, Int.max_def]; split <;> omega

/-! ### Push loops -/

theorem pushEach_spec (conv : β → R α) : ∀ (xs : List β) (a : Arr α) (n : Int), VecOK a n →
    a.off - 1 + n + xs.length ≤ 576460752303423488 →
    (∀ e, convList conv xs = .error e → pushEach conv a xs = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a', pushEach conv a xs = .ok a' ∧ VecOK a' (n + xs.length) ∧
      a'.off ≤ a.off ∧ contents a' = contents a ++ ys.map some)
  | [], a, n, ha, _ => ⟨fun e h => by simp [convList] at h, fun ys h => by
      simp only [convList, Except.ok.injEq] at h; subst h
      exact ⟨a, rfl, by simpa using ha, Int.le_refl _, by simp⟩⟩
  | x :: xs, a, n, ha, hb => by
    simp only [List.length_cons] at hb
    refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · unfold convList at h
      cases hx : conv x with
      | error e' =>
        rw [hx, bind_error] at h; cases h
        simp only [pushEach, m1358, hx, bind_error]
      | ok y =>
        rw [hx, bind_ok] at h
        obtain ⟨a1, e1, ha1, ho1, _⟩ := m1366_vec ha (by omega) y
        have ih := (pushEach_spec conv xs a1 (n + 1) ha1 (by omega)).1
        cases hxs : convList conv xs with
        | error e'' =>
          rw [hxs, bind_error] at h; cases h
          simp only [pushEach, m1358, hx, bind_ok, e1]
          exact ih _ hxs
        | ok zs => rw [hxs, bind_ok] at h; cases h
    · unfold convList at h
      cases hx : conv x with
      | error e' => rw [hx, bind_error] at h; cases h
      | ok y =>
        rw [hx, bind_ok] at h
        cases hxs : convList conv xs with
        | error e'' => rw [hxs, bind_error] at h; cases h
        | ok zs =>
          rw [hxs, bind_ok, pure_ok, Except.ok.injEq] at h
          subst h
          obtain ⟨a1, e1, ha1, ho1, hc1⟩ := m1366_vec ha (by omega) y
          obtain ⟨a2, e2, ha2, ho2, hc2⟩ := (pushEach_spec conv xs a1 (n + 1) ha1 (by omega)).2 zs hxs
          refine ⟨a2, ?_, by simpa [Int.add_assoc, Int.add_comm 1] using ha2, by omega, ?_⟩
          · simp only [pushEach, m1358, hx, bind_ok, e1]; exact e2
          · rw [hc2, hc1]; simp

theorem pushfirstEach_spec (conv : β → R α) : ∀ (xs : List β) (a : Arr α) (n c : Int), VecOK a n →
    n + xs.length ≤ 576460752303423488 →
    (∀ e, convList conv xs = .error e → pushfirstEach conv a c xs = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a', pushfirstEach conv a c xs = .ok (a', c + xs.length) ∧
      VecOK a' (n + xs.length) ∧ contents a' = (ys.map some).reverse ++ contents a)
  | [], a, n, c, ha, _ => ⟨fun e h => by simp [convList] at h, fun ys h => by
      simp only [convList, Except.ok.injEq] at h; subst h
      exact ⟨a, by simp [pushfirstEach], by simpa using ha, by simp⟩⟩
  | x :: xs, a, n, c, ha, hb => by
    simp only [List.length_cons] at hb
    refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · unfold convList at h
      cases hx : conv x with
      | error e' =>
        rw [hx, bind_error] at h; cases h
        simp only [pushfirstEach, pushfirstConv, hx, bind_error]
      | ok y =>
        rw [hx, bind_ok] at h
        obtain ⟨a1, e1, ha1, _⟩ := m1782_vec ha (by omega) y
        have ih := (pushfirstEach_spec conv xs a1 (n + 1) (c + 1) ha1 (by omega)).1
        cases hxs : convList conv xs with
        | error e'' =>
          rw [hxs, bind_error] at h; cases h
          simp only [pushfirstEach, pushfirstConv, hx, bind_ok, e1]
          exact ih _ hxs
        | ok zs => rw [hxs, bind_ok] at h; cases h
    · unfold convList at h
      cases hx : conv x with
      | error e' => rw [hx, bind_error] at h; cases h
      | ok y =>
        rw [hx, bind_ok] at h
        cases hxs : convList conv xs with
        | error e'' => rw [hxs, bind_error] at h; cases h
        | ok zs =>
          rw [hxs, bind_ok, pure_ok, Except.ok.injEq] at h
          subst h
          obtain ⟨a1, e1, ha1, hc1⟩ := m1782_vec ha (by omega) y
          obtain ⟨a2, e2, ha2, hc2⟩ := (pushfirstEach_spec conv xs a1 (n + 1) (c + 1) ha1 (by omega)).2 zs hxs
          refine ⟨a2, ?_, by simpa [Int.add_assoc, Int.add_comm 1] using ha2, ?_⟩
          · simp only [pushfirstEach, pushfirstConv, hx, bind_ok, e1]
            rw [e2]; congr 2; simp only [List.length_cons]; omega
          · rw [hc2, hc1]; simp

/-! ### `sizehint!(a, sz; shrink=false)` -/

theorem m1617_end {a : Arr α} {n sz : Int} (ha : VecOK a n) (h0 : 0 ≤ sz)
    (hb : a.off - 1 + max sz n ≤ 576460752303423488) :
    ∃ a', m1617 a sz false false = .ok a' ∧ VecOK a' n ∧ a'.off ≤ a.off ∧ contents a' = contents a := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1617
  simp only [hn]
  rw [toInt_ok (by omega) (by omega), bind_ok]
  split
  · exact ⟨a, by simp, ha, Int.le_refl _, rfl⟩
  · rename_i hc
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨a1, e1, ⟨hv1, ⟨h1, h2, h3⟩, hs1⟩, ho1, hp⟩ := m1212_vec ha (delta := max sz n - n) (by omega) (by omega)
    rw [e1, bind_ok, pure_ok]
    refine ⟨_, rfl, ⟨rfl, ⟨h1, by simp [length]; omega, ?_⟩, hs1⟩, ho1, ?_⟩
    · have := length_vec a1 _ hv1; simp [length]; omega
    · apply contents_ext (by simp [length, hv])
      intro k hk; simp only [contents_length, hn] at hk
      rw [getElem_contents]
      exact hp _ (by omega) (by omega)

theorem m1617_beg {a : Arr α} {n sz : Int} (ha : VecOK a n) (h0 : 0 ≤ sz)
    (hb : max sz n < 576460752303423488) :
    ∃ a', m1617 a sz true false = .ok a' ∧ VecOK a' n ∧ contents a' = contents a := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1617
  simp only [hn]
  rw [toInt_ok (by omega) (by omega), bind_ok]
  have hMn : n ≤ max sz n := Int.le_max_right _ _
  generalize max sz n = M at *
  split
  · exact ⟨a, by simp, ha, rfl⟩
  · rename_i hc
    simp only [if_true]
    obtain ⟨a1, e1, hv1, ⟨h1, h2, h3⟩, hp⟩ := m1151_spec ha (delta := M - n) (by omega) (by omega)
    obtain ⟨b1, b2⟩ := m1151_bnd ha (delta := M - n) (by omega) (by omega) a1 e1
    have hl1 := length_vec a1 _ hv1
    rw [hl1] at h3
    rw [e1, bind_ok]
    have hin : 1 ≤ a1.off + (M - n + 1) - 1 ∧ a1.off + (M - n + 1) - 1 ≤ a1.mem.len := by
      by_cases hn1 : 1 ≤ n
      · omega
      · have := b2 (by omega) (by omega); omega
    unfold refIndex; rw [if_pos hin, bind_ok, pure_ok]
    have hm := m1102_bounds (n := n) hn0 (by omega)
    refine ⟨_, rfl, ⟨rfl, ⟨by dsimp only; omega, by simp [length]; omega, by simp [length]; omega⟩, ?_⟩, ?_⟩
    · simp only [Small]
      rcases b1 with b1 | b1
      · omega
      · rw [b1, Int.max_def]; split <;> omega
    · apply contents_ext (by simp [length, hv])
      intro k hk; simp only [contents_length, hn] at hk
      rw [getElem_contents, ← hp ((k : Int) + 1) (by omega) (by omega)]
      simp only [Arr.at]; congr 1; omega

end JuliaLean.MultidimCov.ArrayV2
