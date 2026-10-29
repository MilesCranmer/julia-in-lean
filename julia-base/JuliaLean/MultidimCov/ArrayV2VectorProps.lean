import JuliaLean.MultidimCov.ArrayV2Vector

/-! Contracts of the `Vector` mutation methods in `ArrayV2Vector`. -/

namespace JuliaLean.MultidimCov.ArrayV2

theorem getElem?_contents (a : Arr α) (k : Nat) :
    (contents a)[k]? = if (k : Int) < length a then some (a.at ((k : Int) + 1)) else none := by
  unfold contents
  by_cases h : k < (length a).toNat
  · rw [List.getElem?_map, List.getElem?_range h, if_pos (by omega)]; rfl
  · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega), if_neg (by omega)]; rfl

/-- Close a list equation between `contents` terms slot by slot. -/
macro "contents_ext" : tactic => `(tactic| (
  apply List.ext_getElem?
  intro k
  simp only [getElem?_contents, List.getElem?_append, List.getElem?_map, List.getElem?_take,
    List.getElem?_drop, List.getElem?_cons, List.getElem?_nil, List.length_append, List.length_map,
    List.length_take, List.length_drop, List.length_cons, List.length_nil, contents_length,
    List.getElem?_replicate, List.length_replicate]
  repeat' split
  all_goals first | rfl | omega | (simp_all; done) | (congr 1; omega) | skip))

theorem safeWrites_spec : ∀ (xs : List α) (a : Arr α) (start : Int),
    (safeWrites a start xs).dims = a.dims ∧ (safeWrites a start xs).off = a.off ∧
    (safeWrites a start xs).mem.len = a.mem.len ∧
    ∀ t, (safeWrites a start xs).at t = if start ≤ t ∧ t < start + xs.length then xs[(t - start).toNat]? else a.at t
  | [], a, start => ⟨rfl, rfl, rfl, fun t => (if_neg (by simp only [List.length_nil]; omega)).symm⟩
  | x :: xs, a, start => by
    obtain ⟨h1, h2, h3, h4⟩ := safeWrites_spec xs (m1055 a x start) (start + 1)
    simp only [safeWrites]
    refine ⟨by simpa [m1055] using h1, by simpa [m1055] using h2, by simpa [m1055] using h3, fun t => ?_⟩
    rw [h4 t]
    simp only [m1055, setU_at, List.getElem?_cons, List.length_cons]
    by_cases h : t = start
    · subst h; split <;> simp_all <;> omega
    · rw [if_neg h]
      by_cases h' : start + 1 ≤ t ∧ t < start + 1 + xs.length
      · rw [if_pos h', if_pos (by omega), if_neg (by omega)]
        congr 1; omega
      · rw [if_neg h', if_neg (by omega)]

/-- A vector whose slots are `a[1:s]`, then `ys`, then `a[s+1:n]` has those contents. -/
theorem contents_splice {a a' : Arr α} {n s : Int} (ys : List (Option α)) (hn : length a = n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ n) (hl : length a' = n + ys.length)
    (hA : ∀ k, 1 ≤ k → k ≤ s → a'.at k = a.at k)
    (hB : ∀ j : Nat, (hj : j < ys.length) → a'.at (s + j + 1) = ys[j])
    (hC : ∀ k, s < k → k ≤ n → a'.at (k + ys.length) = a.at k) :
    contents a' = (contents a).take s.toNat ++ ys ++ (contents a).drop s.toNat := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [contents_length] at h1
    rw [getElem_contents]
    by_cases ja : j < s.toNat
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_take, getElem_contents]
      exact hA _ (by omega) (by omega)
    · by_cases jb : j < s.toNat + ys.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        have hj : j - (List.take s.toNat (contents a)).length < ys.length := by simp; omega
        have := hB (j - (List.take s.toNat (contents a)).length) hj
        rw [show s + ((j - (List.take s.toNat (contents a)).length : Nat) : Int) + 1 = (j : Int) + 1 by
          simp; omega] at this
        exact this
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_drop, getElem_contents, List.length_append, List.length_take,
          contents_length]
        have := hC ((s.toNat + (j - (min s.toNat (length a).toNat + ys.length)) : Nat) + 1)
          (by omega) (by omega)
        rw [← this]; congr 1; omega

/-! ### push! and pushfirst! -/

theorem m1366_spec {a : Arr α} {n : Int} (ha : VecOK a n) (x : α) :
    ∃ a', m1366 a x = .ok a' ∧ IsVec a' (n + 1) ∧ Valid a' ∧ contents a' = contents a ++ [some x] := by
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  obtain ⟨a1, e, hv1, hval1, hp⟩ := m1212_spec (delta := 1) ha (by omega) (by omega)
  have hl1 := length_vec a1 _ hv1
  unfold m1366; rw [e, bind_ok, pure_ok]
  refine ⟨_, rfl, show (setU _ _ _).dims = _ by rw [setU_dims]; exact hv1,
    by simpa [m1057, Valid, length] using hval1, ?_⟩
  have := contents_splice (a := a) (a' := m1057 a1 x (length a1)) (n := n) (s := n) [some x] hn hn0
    (Int.le_refl n) (by simp [m1057, hl1])
    (fun k k1 k2 => by simp only [m1057, setU_at, hl1]; rw [if_neg (by omega), hp k k1 k2])
    (fun j hj => by simp at hj; subst hj; simp [m1057, hl1])
    (fun k k1 k2 => by omega)
  rw [this, List.take_of_length_le (by simp; omega), List.drop_of_length_le (by simp; omega),
    List.append_nil]

theorem splice_end {a a' : Arr α} {n : Int} (ys : List (Option α)) (hn : length a = n) (hn0 : 0 ≤ n)
    (hl : length a' = n + ys.length) (hA : ∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k)
    (hB : ∀ j : Nat, (hj : j < ys.length) → a'.at (n + j + 1) = ys[j]) : contents a' = contents a ++ ys := by
  rw [contents_splice ys hn hn0 (Int.le_refl n) hl hA hB (fun k k1 k2 => by omega),
    List.take_of_length_le (by simp; omega), List.drop_of_length_le (by simp; omega), List.append_nil]

theorem splice_front {a a' : Arr α} {n : Int} (ys : List (Option α)) (hn : length a = n) (hn0 : 0 ≤ n)
    (hl : length a' = n + ys.length)
    (hB : ∀ j : Nat, (hj : j < ys.length) → a'.at (j + 1) = ys[j])
    (hC : ∀ k, 0 < k → k ≤ n → a'.at (k + ys.length) = a.at k) : contents a' = ys ++ contents a := by
  rw [contents_splice (s := 0) ys hn (Int.le_refl 0) hn0 hl (fun k k1 k2 => by omega)
    (fun j hj => by simpa using hB j hj) hC]
  all_goals simp

theorem safeWrites_at {xs : List α} {a : Arr α} {start : Int} (j : Nat) (hj : j < xs.length) :
    (safeWrites a start xs).at (start + j) = some xs[j] := by
  rw [(safeWrites_spec xs a start).2.2.2, if_pos (by omega)]
  rw [show (start + (j : Int) - start).toNat = j by omega]
  exact List.getElem?_eq_getElem hj

theorem safeWrites_out {xs : List α} {a : Arr α} {start t : Int} (h : t < start ∨ start + xs.length ≤ t) :
    (safeWrites a start xs).at t = a.at t := by
  rw [(safeWrites_spec xs a start).2.2.2, if_neg (by omega)]

theorem length_safeWrites (xs : List α) (a : Arr α) (start : Int) :
    length (safeWrites a start xs) = length a := by
  simp [length, (safeWrites_spec xs a start).1]

theorem valid_safeWrites {xs : List α} {a : Arr α} {start : Int} (h : Valid a) :
    Valid (safeWrites a start xs) := by
  obtain ⟨d, o, m, _⟩ := safeWrites_spec xs a start
  unfold Valid at *; rw [o, m, length_safeWrites]; exact h

theorem m1373_spec {a : Arr α} {n : Int} (ha : VecOK a n) (x : α) :
    ∃ a', m1373 a x = .ok a' ∧ IsVec a' (n + 1) ∧ Valid a' ∧ contents a' = contents a ++ [some x] := by
  have h := m1366_spec ha x
  unfold m1366 at h; unfold m1373; simpa [m1057, m1055] using h

theorem m1378_spec {a : Arr α} {n : Int} (ha : VecOK a n) (xs : List α) (hx : xs.length ≤ 2 ^ 60) :
    ∃ a', m1378 a xs = .ok a' ∧ IsVec a' (n + xs.length) ∧ Valid a' ∧
      contents a' = contents a ++ xs.map some := by
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  obtain ⟨a1, e, hv1, hval1, hp⟩ := m1212_spec (delta := xs.length) ha (by omega) (by omega)
  have hl1 := length_vec a1 _ hv1
  unfold m1378; simp only [hn]; rw [e, bind_ok, pure_ok]
  refine ⟨_, rfl, by unfold IsVec; rw [(safeWrites_spec xs a1 _).1]; exact hv1, valid_safeWrites hval1, ?_⟩
  apply splice_end _ hn hn0 (by rw [length_safeWrites, hl1]; simp)
  · intro k k1 k2; rw [safeWrites_out (by omega), hp k k1 k2]
  · intro j hj; simp only [List.length_map] at hj
    rw [show n + (j : Int) + 1 = n + 1 + j by omega, safeWrites_at j hj]; simp

theorem m1782_spec {a : Arr α} {n : Int} (ha : VecOK a n) (x : α) :
    ∃ a', m1782 a x = .ok a' ∧ IsVec a' (n + 1) ∧ Valid a' ∧ contents a' = some x :: contents a := by
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  obtain ⟨a1, e, hv1, hval1, hp⟩ := m1151_spec (delta := 1) ha (by omega) (by omega)
  have hl1 := length_vec a1 _ hv1
  unfold m1782; rw [e, bind_ok, pure_ok]
  refine ⟨_, rfl, show (setU _ _ _).dims = _ by rw [setU_dims]; exact hv1,
    by simpa [m1057, Valid, length] using hval1, ?_⟩
  have := splice_front (a := a) (a' := m1057 a1 x 1) [some x] hn hn0 (by simp [m1057, hl1])
    (fun j hj => by simp at hj; subst hj; simp [m1057])
    (fun k k1 k2 => by simp only [m1057, setU_at, List.length_singleton]; rw [if_neg (by omega),
      show k + ((1 : Nat) : Int) = 1 + k by omega, hp k (by omega) k2])
  simpa using this

theorem m1789_spec {a : Arr α} {n : Int} (ha : VecOK a n) (x : α) :
    ∃ a', m1789 a x = .ok a' ∧ IsVec a' (n + 1) ∧ Valid a' ∧ contents a' = some x :: contents a := by
  have h := m1782_spec ha x
  unfold m1782 at h; unfold m1789; simpa [m1057, m1055] using h

theorem m1794_spec {a : Arr α} {n : Int} (ha : VecOK a n) (xs : List α) (hx : xs.length ≤ 2 ^ 60) :
    ∃ a', m1794 a xs = .ok a' ∧ IsVec a' (n + xs.length) ∧ Valid a' ∧
      contents a' = xs.map some ++ contents a := by
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  obtain ⟨a1, e, hv1, hval1, hp⟩ := m1151_spec (delta := xs.length) ha (by omega) (by omega)
  have hl1 := length_vec a1 _ hv1
  unfold m1794; (try dsimp only); rw [e, bind_ok, pure_ok]
  refine ⟨_, rfl, by unfold IsVec; rw [(safeWrites_spec xs a1 _).1]; exact hv1, valid_safeWrites hval1, ?_⟩
  apply splice_front _ hn hn0 (by rw [length_safeWrites, hl1]; simp)
  · intro j hj; simp only [List.length_map] at hj
    rw [show (j : Int) + 1 = 1 + j by omega, safeWrites_at j hj]; simp
  · intro k k1 k2; simp only [List.length_map]
    rw [safeWrites_out (by omega), show k + (xs.length : Int) = xs.length + k by omega, hp k k1 k2]

/-- `push!`/`pushfirst!` contract (docstrings `base/array.jl:1330`, `1757`): the
items, converted to the element type in order, end up after (`push!`) or before
(`pushfirst!`) every old element, which keep their order; a failing conversion
propagates. Covers the typed, `Vector{Any}` and variadic methods. -/
def PPush : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int), VecOK a n →
    (∀ x : β, (∀ e, conv x = .error e → m1358 conv a x = .error e) ∧
      (∀ y, conv x = .ok y → ∃ a', m1358 conv a x = .ok a' ∧ IsVec a' (n + 1) ∧ Valid a' ∧
        contents a' = contents a ++ [some y])) ∧
    (∀ x : α, ∃ a', m1366 a x = .ok a' ∧ IsVec a' (n + 1) ∧ contents a' = contents a ++ [some x]) ∧
    (∀ x : α, ∃ a', m1373 a x = .ok a' ∧ IsVec a' (n + 1) ∧ contents a' = contents a ++ [some x]) ∧
    (∀ xs : List α, xs.length ≤ 2 ^ 60 → ∃ a', m1378 a xs = .ok a' ∧
      IsVec a' (n + xs.length) ∧ contents a' = contents a ++ xs.map some) ∧
    (∀ x : α, ∃ a', m1782 a x = .ok a' ∧ IsVec a' (n + 1) ∧ contents a' = some x :: contents a) ∧
    (∀ x : α, ∃ a', m1789 a x = .ok a' ∧ IsVec a' (n + 1) ∧ contents a' = some x :: contents a) ∧
    (∀ xs : List α, xs.length ≤ 2 ^ 60 → ∃ a', m1794 a xs = .ok a' ∧
      IsVec a' (n + xs.length) ∧ contents a' = xs.map some ++ contents a)

theorem pPush : PPush := by
  intro α β conv a n ha
  refine ⟨fun x => ⟨fun e he => by unfold m1358; rw [he, bind_error], fun y hy => ?_⟩,
    fun x => ?_, fun x => ?_, fun xs hx => ?_, fun x => ?_, fun x => ?_, fun xs hx => ?_⟩
  · unfold m1358; rw [hy, bind_ok]; exact m1366_spec ha y
  · obtain ⟨a', e, h1, _, h3⟩ := m1366_spec ha x; exact ⟨a', e, h1, h3⟩
  · obtain ⟨a', e, h1, _, h3⟩ := m1373_spec ha x; exact ⟨a', e, h1, h3⟩
  · obtain ⟨a', e, h1, _, h3⟩ := m1378_spec ha xs hx; exact ⟨a', e, h1, h3⟩
  · obtain ⟨a', e, h1, _, h3⟩ := m1782_spec ha x; exact ⟨a', e, h1, h3⟩
  · obtain ⟨a', e, h1, _, h3⟩ := m1789_spec ha x; exact ⟨a', e, h1, h3⟩
  · obtain ⟨a', e, h1, _, h3⟩ := m1794_spec ha xs hx; exact ⟨a', e, h1, h3⟩

/-! ### append! and prepend! -/

theorem copyIter_ok {dest : Arr α} {dstart : Int} {ys : List α} (h0 : 0 < ys.length) (h1 : 1 ≤ dstart)
    (h2 : dstart + ys.length - 1 ≤ length dest) :
    copyIter dest dstart ys 1 ys.length = .ok (safeWrites dest dstart ys) := by
  unfold copyIter
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by simp only [inBounds, Bool.and_eq_true, decide_eq_true_eq]; omega)]
  cases ys with
  | nil => simp at h0
  | cons x xs =>
    simp only [show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero, Int.toNat_natCast,
      List.take_length]
    rw [if_neg (by omega)]

theorem m299_vec {d s : Arr α} (hd : Valid d) (hs : Valid s) (hdl : length d ≤ 2 ^ 60)
    (hsl : length s ≤ 2 ^ 60) {doffs soffs c : Int} (h0 : 0 ≤ c) (h1 : 1 ≤ doffs)
    (h2 : doffs + c - 1 ≤ length d) (h3 : 1 ≤ soffs) (h4 : soffs + c - 1 ≤ length s) :
    ∃ d', m299 d doffs s soffs c = .ok d' ∧ d'.dims = d.dims ∧ Valid d' ∧
      ∀ k, 1 ≤ k → k ≤ length d → d'.at k = if doffs ≤ k ∧ k < doffs + c then s.at (k - doffs + soffs) else d.at k := by
  obtain ⟨z, _, _, ok⟩ := m299_contract d s doffs soffs c hd hs hdl hsl
  by_cases hc : c = 0
  · exact ⟨d, z hc, rfl, hd, fun k _ _ => by rw [if_neg (by omega)]⟩
  · obtain ⟨d', e, hdd, hl, hp⟩ := ok (by omega) h1 h2 h3 h4
    refine ⟨d', e, hdd, ?_, hp⟩
    have hmem : d'.off = d.off ∧ d'.mem.len = d.mem.len := by
      unfold m299 at e
      simp only [hc, if_false] at e
      rw [if_neg (by omega)] at e
      simp only [inBounds, Bool.and_eq_true, decide_eq_true_eq] at e
      obtain ⟨o1, o2, o3⟩ := hd; obtain ⟨t1, t2, t3⟩ := hs
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok,
        toInt_ok (by omega) (by omega), bind_ok, refCopy_ok (by omega) (by omega) (by omega), bind_ok] at e
      cases e; exact ⟨rfl, rfl⟩
    unfold Valid at *; rw [hmem.1, hmem.2, hl]; exact hd

/-- `append!(a::Vector{T}, items)` and `push!(a, items...)` (docstring
`base/array.jl:1383`): the result is `a`'s old elements followed by every element
of `items` in order (converted, for a `Tuple`); appending a vector to itself
doubles it. A failing tuple conversion propagates before `a` grows. -/
def P1427 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int), VecOK a n →
    (∀ xs : List β, (∀ e, convList conv xs = .error e → m1427 conv a (.tuple xs) = .error e ∧
        m1436 conv a xs = .error e) ∧
      (∀ ys, convList conv xs = .ok ys → ys.length ≤ 2 ^ 60 →
        ∃ a', m1427 conv a (.tuple xs) = .ok a' ∧ m1436 conv a xs = .ok a' ∧
          IsVec a' (n + ys.length) ∧ contents a' = contents a ++ ys.map some)) ∧
    (∀ b : Arr α, Valid b → n + length b ≤ 2 ^ 60 →
      ∃ a', m1427 conv a (.vec b) = .ok a' ∧ IsVec a' (n + length b) ∧ contents a' = contents a ++ contents b) ∧
    (n + n ≤ 2 ^ 60 → ∃ a', m1427 conv a .self = .ok a' ∧ IsVec a' (n + n) ∧
      contents a' = contents a ++ contents a)

theorem p1427 : P1427 := by
  intro α β conv a n ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun xs => ⟨fun e he => ?_, fun ys hys hyl => ?_⟩, fun b hb hbl => ?_, fun hl => ?_⟩
  · simp only [m1436, m1427]; rw [he, bind_error]; exact ⟨rfl, rfl⟩
  · suffices h : ∃ a', m1427 conv a (.tuple xs) = .ok a' ∧ IsVec a' (n + ys.length) ∧
        contents a' = contents a ++ ys.map some by
      obtain ⟨a', e, h1, h2⟩ := h; exact ⟨a', e, e, h1, h2⟩
    obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1212_spec (delta := ys.length) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1427]; rw [hys, bind_ok, toInt_ok (by omega) (by omega), bind_ok, e1, bind_ok, hl1]
    by_cases h0 : ys.length = 0
    · have : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      refine ⟨a1, by unfold copyIter; simp, hv1, ?_⟩
      simp only [List.map_nil, List.append_nil]
      apply contents_ext (by rw [hl1]; simp; omega)
      intro k hk; simp at hk; rw [getElem_contents, hp _ (by omega) (by omega)]
    · rw [show n + (ys.length : Int) - ys.length + 1 = n + 1 by omega, copyIter_ok (by omega) (by omega)
        (by omega)]
      refine ⟨_, rfl, by unfold IsVec; rw [(safeWrites_spec ys a1 _).1]; exact hv1, ?_⟩
      apply splice_end _ hn hn0 (by rw [length_safeWrites, hl1]; simp)
      · intro k k1 k2; rw [safeWrites_out (by omega), hp k k1 k2]
      · intro j hj; simp only [List.length_map] at hj
        rw [show n + (j : Int) + 1 = n + 1 + j by omega, safeWrites_at j hj]; simp
  · obtain ⟨b1, b2, b3⟩ := hb
    obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1212_spec (delta := length b) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1427]; rw [toInt_ok (by omega) (by omega), bind_ok, e1, bind_ok, hl1]
    unfold m288
    obtain ⟨a2, e2, hd2, _, hp2⟩ := m299_vec (c := length b) hval1 ⟨b1, b2, b3⟩ (by omega) (by omega)
      (doffs := n + length b - length b + 1) (soffs := 1) b2 (by omega) (by omega) (by omega) (by omega)
    refine ⟨a2, e2, by unfold IsVec; rw [hd2]; exact hv1, ?_⟩
    apply splice_end _ hn hn0 (by rw [show length a2 = length a1 by simp [length, hd2], hl1]; simp; omega)
    · intro k k1 k2; rw [hp2 k k1 (by omega), if_neg (by omega), hp k k1 k2]
    · intro j hj; simp only [contents_length] at hj
      rw [hp2 _ (by omega) (by omega), if_pos (by omega), getElem_contents]; congr 1; omega
  · obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1212_spec (delta := n) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1427]; rw [hn, toInt_ok (by omega) (by omega), bind_ok, e1, bind_ok, hl1]
    unfold m288
    obtain ⟨a2, e2, hd2, _, hp2⟩ := m299_vec (c := n) hval1 hval1 (by omega) (by omega)
      (doffs := n + n - n + 1) (soffs := 1) hn0 (by omega) (by omega) (by omega) (by omega)
    refine ⟨a2, e2, by unfold IsVec; rw [hd2]; exact hv1, ?_⟩
    apply splice_end _ hn hn0 (by rw [show length a2 = length a1 by simp [length, hd2], hl1]; simp; omega)
    · intro k k1 k2; rw [hp2 k k1 (by omega), if_neg (by omega), hp k k1 k2]
    · intro j hj; simp only [contents_length] at hj
      rw [hp2 _ (by omega) (by omega), if_pos (by omega), getElem_contents, hp _ (by omega) (by omega)]
      congr 1; omega

/-- `prepend!(a::Vector{T}, items)` and `pushfirst!(a, items...)` (docstring
`base/array.jl:1455`): every element of `items` in order (converted, for a
`Tuple`), then `a`'s old elements; prepending a vector to itself doubles it. -/
def P1485 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int), VecOK a n →
    (∀ xs : List β, (∀ e, convList conv xs = .error e → m1485 conv a (.tuple xs) = .error e ∧
        m1501 conv a xs = .error e) ∧
      (∀ ys, convList conv xs = .ok ys → ys.length ≤ 2 ^ 60 →
        ∃ a', m1485 conv a (.tuple xs) = .ok a' ∧ m1501 conv a xs = .ok a' ∧
          IsVec a' (n + ys.length) ∧ contents a' = ys.map some ++ contents a)) ∧
    (∀ b : Arr α, Valid b → n + length b ≤ 2 ^ 60 →
      ∃ a', m1485 conv a (.vec b) = .ok a' ∧ IsVec a' (n + length b) ∧ contents a' = contents b ++ contents a) ∧
    (n + n ≤ 2 ^ 60 → ∃ a', m1485 conv a .self = .ok a' ∧ IsVec a' (n + n) ∧
      contents a' = contents a ++ contents a)

theorem p1485 : P1485 := by
  intro α β conv a n ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun xs => ⟨fun e he => ?_, fun ys hys hyl => ?_⟩, fun b hb hbl => ?_, fun hl => ?_⟩
  · simp only [m1501, m1485]; rw [he, bind_error]; exact ⟨rfl, rfl⟩
  · suffices h : ∃ a', m1485 conv a (.tuple xs) = .ok a' ∧ IsVec a' (n + ys.length) ∧
        contents a' = ys.map some ++ contents a by
      obtain ⟨a', e, h1, h2⟩ := h; exact ⟨a', e, e, h1, h2⟩
    obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1151_spec (delta := ys.length) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1485]; rw [hys, bind_ok]; (try dsimp only); rw [e1, bind_ok]
    by_cases h0 : ys.length = 0
    · have : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      refine ⟨a1, by unfold copyIter; simp, hv1, ?_⟩
      simp only [List.map_nil, List.nil_append]
      apply contents_ext (by rw [hl1]; simp; omega)
      intro k hk; simp at hk; rw [getElem_contents]
      have := hp (k + 1) (by omega) (by omega); simp at this; rw [this]
    · rw [show (ys.length : Int) - ys.length + 1 = 1 by omega, copyIter_ok (by omega) (by omega)
        (by omega)]
      refine ⟨_, rfl, by unfold IsVec; rw [(safeWrites_spec ys a1 _).1]; exact hv1, ?_⟩
      apply splice_front _ hn hn0 (by rw [length_safeWrites, hl1]; simp)
      · intro j hj; simp only [List.length_map] at hj
        rw [show (j : Int) + 1 = 1 + j by omega, safeWrites_at j hj]; simp
      · intro k k1 k2; simp only [List.length_map]
        rw [safeWrites_out (by omega), show k + (ys.length : Int) = ys.length + k by omega, hp k k1 k2]
  · obtain ⟨b1, b2, b3⟩ := hb
    obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1151_spec (delta := length b) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1485]; (try dsimp only); rw [e1, bind_ok]
    unfold m288
    obtain ⟨a2, e2, hd2, _, hp2⟩ := m299_vec (c := length b) hval1 ⟨b1, b2, b3⟩ (by omega) (by omega)
      (doffs := 1) (soffs := length b - length b + 1) b2 (by omega) (by omega) (by omega) (by omega)
    refine ⟨a2, e2, by unfold IsVec; rw [hd2]; exact hv1, ?_⟩
    apply splice_front _ hn hn0 (by rw [show length a2 = length a1 by simp [length, hd2], hl1]; simp; omega)
    · intro j hj; simp only [contents_length] at hj
      rw [hp2 _ (by omega) (by omega), if_pos (by omega), getElem_contents]; congr 1; omega
    · intro k k1 k2; simp only [contents_length]
      rw [hp2 _ (by omega) (by omega), if_neg (by omega), show k + ((length b).toNat : Int) = length b + k by
        omega, hp k k1 k2]
  · obtain ⟨a1, e1, hv1, hval1, hp⟩ := m1151_spec (delta := n) ha (by omega) (by omega)
    have hl1 := length_vec a1 _ hv1
    simp only [m1485]; (try dsimp only); rw [hn, e1, bind_ok, hl1]
    unfold m288
    obtain ⟨a2, e2, hd2, _, hp2⟩ := m299_vec (c := n) hval1 hval1 (by omega) (by omega)
      (doffs := 1) (soffs := n + n - n + 1) hn0 (by omega) (by omega) (by omega) (by omega)
    refine ⟨a2, e2, by unfold IsVec; rw [hd2]; exact hv1, ?_⟩
    apply splice_front _ hn hn0 (by rw [show length a2 = length a1 by simp [length, hd2], hl1]; simp; omega)
    · intro j hj; simp only [contents_length] at hj
      rw [hp2 _ (by omega) (by omega), if_pos (by omega), getElem_contents,
        show (j : Int) + 1 - 1 + (n + n - n + 1) = n + (j + 1) by omega, hp _ (by omega) (by omega)]
    · intro k k1 k2; simp only [contents_length]
      rw [hp2 _ (by omega) (by omega), if_neg (by omega), show k + ((length a).toNat : Int) = n + k by
        omega, hp k k1 k2]

/-! ### resize!, sizehint!, pop!, popfirst!, popat!, insert!, deleteat!, empty! -/

theorem take_contents_full (a : Arr α) (n : Int) (hn : length a = n) :
    (contents a).take n.toNat = contents a := List.take_of_length_le (by simp [hn])

/-- `resize!(a, n; first)` (docstring `base/array.jl:1527`): a negative length is an
`ArgumentError`; shrinking keeps the first `n` elements (the last `n` with
`first=true`); growing keeps every old element, after the new slots with
`first=true` and before them otherwise. -/
def P1564 : Prop := ∀ {α : Type} (a : Arr α) (n nl : Int) (first : Bool), VecOK a n →
    (typeminInt ≤ nl → nl < 0 → m1564 a nl first = .error .argument) ∧
    (0 ≤ nl → nl ≤ n → ∃ a', m1564 a nl first = .ok a' ∧ IsVec a' nl ∧ Valid a' ∧
      contents a' = if first then (contents a).drop (n - nl).toNat else (contents a).take nl.toNat) ∧
    (n < nl → nl ≤ 2 ^ 60 → ∃ a', m1564 a nl first = .ok a' ∧ IsVec a' nl ∧ Valid a' ∧
      (if first then (contents a').drop (nl - n).toNat = contents a else (contents a').take n.toNat = contents a))

theorem p1564 : P1564 := by
  intro α a n nl first ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · unfold typeminInt at h0
    unfold m1564; rw [toInt_ok' h0 (by omega), bind_ok]; simp only [hn]
    rw [if_neg (by omega), if_pos (by omega), if_pos h1]; rfl
  · unfold m1564; rw [toInt_ok (by omega) (by omega), bind_ok]; simp only [hn]
    rw [if_neg (by omega)]
    by_cases he : nl = n
    · subst he; rw [if_neg (by simp)]
      refine ⟨a, rfl, (vecOK_unpack ha).2.2.2.2.2, ha.2.1, ?_⟩
      cases first
      · simp [take_contents_full a nl hn]
      · simp
    · rw [if_pos he, if_neg (show ¬ nl < 0 by omega)]
      cases first
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨_, ok⟩ := p1296 a n (n - nl) ha
        obtain ⟨a', e, hv, hvl, hc⟩ := ok (by omega) (by omega)
        refine ⟨a', e, by rw [show nl = n - (n - nl) by omega]; exact hvl, hv, ?_⟩
        rw [hc, show n - (n - nl) = nl by omega]
      · simp only [if_true]
        obtain ⟨_, ok⟩ := p1278 a n (n - nl) ha
        obtain ⟨a', e, hv, hvl, hc⟩ := ok (by omega) (by omega)
        exact ⟨a', e, by rw [show nl = n - (n - nl) by omega]; exact hvl, hv, hc⟩
  · unfold m1564; rw [toInt_ok (by omega) (by omega), bind_ok]; simp only [hn]
    have h63 : (2 : Int) ^ 63 = 9223372036854775808 := by rfl
    rw [if_pos (show nl > n from h0), h63, Int.emod_eq_of_lt (by omega) (by omega)]
    cases first
    · simp only [Bool.false_eq_true, if_false]
      obtain ⟨_, ok⟩ := p1212 a n (nl - n) ha
      obtain ⟨a', e, hv, hvl, hc⟩ := ok (by omega) (by omega)
      exact ⟨a', e, by rw [show nl = n + (nl - n) by omega]; exact hvl, hv, hc⟩
    · simp only [if_true]
      obtain ⟨_, ok⟩ := p1151 a n (nl - n) ha
      obtain ⟨a', e, hv, hvl, hc⟩ := ok (by omega) (by omega)
      exact ⟨a', e, by rw [show nl = n + (nl - n) by omega]; exact hvl, hv, hc⟩

/-- `pop!`/`popfirst!` (docstrings `base/array.jl:1660`, `1802`): an empty vector is
an `ArgumentError`; otherwise the last (first) element is returned and removed,
keeping the others in order. -/
def P1700 : Prop := ∀ {α : Type} (a : Arr α) (n : Int), VecOK a n →
    (n = 0 → m1700 a = .error .argument ∧ m1836 a = .error .argument) ∧
    (0 < n → a.at n = none → m1700 a = .error .undefRef) ∧
    (0 < n → ∀ x, a.at n = some x → ∃ a', m1700 a = .ok (x, a') ∧ IsVec a' (n - 1) ∧
      contents a' = (contents a).take (n - 1).toNat) ∧
    (0 < n → a.at 1 = none → m1836 a = .error .undefRef) ∧
    (0 < n → ∀ x, a.at 1 = some x → ∃ a', m1836 a = .ok (x, a') ∧ IsVec a' (n - 1) ∧
      contents a' = (contents a).drop 1)

theorem p1700 : P1700 := by
  intro α a n ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun h => ⟨?_, ?_⟩, fun h hx => ?_, fun h x hx => ?_, fun h hx => ?_, fun h x hx => ?_⟩
  · unfold m1700; rw [if_pos (by omega)]; rfl
  · unfold m1836; rw [if_pos (by omega)]; rfl
  · unfold m1700; rw [if_neg (by omega), getL_def, if_pos (by rw [inBounds_iff]; omega), hn, hx]; rfl
  · unfold m1700; rw [if_neg (by omega), getL_def, if_pos (by rw [inBounds_iff]; omega), hn, hx]
    simp only [bind_ok]
    obtain ⟨_, ok⟩ := p1296 a n 1 ha
    obtain ⟨a', e, _, hvl, hc⟩ := ok (by omega) (by omega)
    rw [e]; exact ⟨a', rfl, hvl, hc⟩
  · unfold m1836; rw [if_neg (by omega), getL_def, if_pos (by rw [inBounds_iff]; omega), hx]; rfl
  · unfold m1836; rw [if_neg (by omega), getL_def, if_pos (by rw [inBounds_iff]; omega), hx]
    simp only [bind_ok]
    obtain ⟨_, ok⟩ := p1278 a n 1 ha
    obtain ⟨a', e, _, hvl, hc⟩ := ok (by omega) (by omega)
    rw [e]; exact ⟨a', rfl, hvl, hc⟩

/-- `popat!(a, i)` / `popat!(a, i, default)` (docstring `base/array.jl:1716`): an
out-of-range `i` is a `BoundsError` (or returns `default`, leaving `a` unchanged);
otherwise `a[i]` is returned and removed, keeping the rest in order. -/
def P1741 : Prop := ∀ {α γ : Type} (a : Arr α) (n i : Int) (d : γ), VecOK a n →
    ((i < 1 ∨ n < i) → m1741 a i = .error .bounds ∧ m1748 a i d = .ok (.inr d, a)) ∧
    (1 ≤ i → i ≤ n → a.at i = none → m1741 a i = .error .undefRef ∧ m1748 a i d = .error .undefRef) ∧
    (1 ≤ i → i ≤ n → ∀ x, a.at i = some x → ∃ a', m1741 a i = .ok (x, a') ∧ m1748 a i d = .ok (.inl x, a') ∧
      IsVec a' (n - 1) ∧ contents a' = (contents a).take (i - 1).toNat ++ (contents a).drop i.toNat)

theorem p1741 : P1741 := by
  intro α γ a n i d ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun h => ⟨?_, ?_⟩, fun h1 h2 hx => ⟨?_, ?_⟩, fun h1 h2 x hx => ?_⟩
  · unfold m1741; rw [getL_def, if_neg (by rw [inBounds_iff]; omega)]; rfl
  · unfold m1748; rw [if_neg (by omega)]
  · unfold m1741; rw [getL_def, if_pos (by rw [inBounds_iff]; omega), hx]; rfl
  · unfold m1748; rw [if_pos (by omega)]; simp [getU, hx]
  · obtain ⟨_, _, ok⟩ := p1312 a n i 1 ha
    obtain ⟨a', e, _, hvl, hc⟩ := ok h1 h2 (by omega) (by omega)
    refine ⟨a', ?_, ?_, hvl, by rw [hc, show i - 1 + 1 = i by omega]⟩
    · unfold m1741; rw [getL_def, if_pos (by rw [inBounds_iff]; omega), hx]; simp only [bind_ok]; rw [e]; rfl
    · unfold m1748; rw [if_pos (by omega)]; simp only [getU, hx, bind_ok]; rw [e]; rfl

/-- `insert!(a, i, item)` (docstring `base/array.jl:1847`): the item is converted
first (a failing conversion propagates whatever `i` is); an index outside
`1:length(a)+1` is a `BoundsError`; otherwise the item sits at index `i` with the
old elements around it in order. -/
def P1866 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n i : Int) (x : β), VecOK a n →
    (∀ e, conv x = .error e → m1866 conv a i x = .error e) ∧
    (∀ y, conv x = .ok y →
      (typeminInt ≤ i → i ≤ typemaxInt → (i < 1 ∨ n + 1 < i) → m1866 conv a i x = .error .bounds) ∧
      (1 ≤ i → i ≤ n + 1 → ∃ a', m1866 conv a i x = .ok a' ∧ m1871 a i y = .ok a' ∧ IsVec a' (n + 1) ∧
        contents a' = (contents a).take (i - 1).toNat ++ [some y] ++ (contents a).drop (i - 1).toNat))

theorem p1866 : P1866 := by
  intro α β conv a n i x ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun e he => by unfold m1866; rw [he, bind_error], fun y hy => ⟨fun h0 h1 h2 => ?_, fun h1 h2 => ?_⟩⟩
  · obtain ⟨_, hb, _⟩ := p1230 a n i 1 ha
    unfold m1866; rw [hy, bind_ok]; unfold m1871
    rw [hb (by omega) (by omega) h0 h1 h2, bind_error]
  · obtain ⟨a1, e1, hv1, hval1, hp1, hp2⟩ := m1230_spec (delta := 1) ha (by omega) (by omega) h1 h2
    have hl1 := length_vec a1 _ hv1
    have e : m1871 a i y = .ok (setU a1 i (some y)) := by unfold m1871; rw [e1, bind_ok]; rfl
    refine ⟨_, by unfold m1866; rw [hy, bind_ok]; exact e, e,
      show (setU _ _ _).dims = _ by rw [setU_dims]; exact hv1, ?_⟩
    apply contents_splice (s := i - 1) [some y] hn (by omega) (by omega) (by simp [hl1])
    · intro k k1 k2; rw [setU_at, if_neg (by omega), hp1 k k1 k2]
    · intro j hj; simp at hj; subst hj; simp
    · intro k k1 k2
      rw [setU_at, if_neg (by simp; omega)]
      have := hp2 (k - (i - 1)) (by omega) (by omega)
      rw [show i - 1 + 1 + (k - (i - 1)) = k + (([some y] : List (Option α)).length : Int) by simp; omega,
        show i - 1 + (k - (i - 1)) = k by omega] at this
      exact this

/-- `deleteat!(a, i)` and `deleteat!(a, r::UnitRange)` (docstring `base/array.jl:1884`):
a valid index or a non-empty range inside `1:length(a)` removes exactly those
elements, keeping the rest in order; an empty range changes nothing; an index
outside `1:length(a)` is a `BoundsError`. `empty!(a)` removes everything. -/
def PDeleteat : Prop := ∀ {α : Type} (mask : Arr α → R (Arr α)) (a : Arr α) (n : Int), VecOK a n →
    (∀ i b, typeminInt ≤ i → i ≤ typemaxInt → (i < 1 ∨ n < i) → m1899 a i b = .error .bounds) ∧
    (∀ i b, 1 ≤ i → i ≤ n → ∃ a', m1899 a i b = .ok a' ∧ IsVec a' (n - 1) ∧
      contents a' = (contents a).take (i - 1).toNat ++ (contents a).drop i.toNat) ∧
    (∀ lo hi, hi < lo → m1905 mask a lo hi false = .ok a) ∧
    (∀ lo hi, 1 ≤ lo → lo ≤ hi → hi ≤ n → ∃ a', m1905 mask a lo hi false = .ok a' ∧ IsVec a' (n - (hi - lo + 1)) ∧
      contents a' = (contents a).take (lo - 1).toNat ++ (contents a).drop hi.toNat) ∧
    (∀ lo hi, m1905 mask a lo hi true = mask a) ∧
    (∃ a', m2155 a = .ok a' ∧ IsVec a' 0 ∧ contents a' = [])

theorem pDeleteat : PDeleteat := by
  intro α mask a n ha
  obtain ⟨hn, _, hn0, _, hs, _⟩ := vecOK_unpack ha
  refine ⟨fun i b h0 h1 h2 => ?_, fun i b h1 h2 => ?_, fun lo hi h => ?_, fun lo hi h1 h2 h3 => ?_,
    fun lo hi => rfl, ?_⟩
  · exact (p1312 a n i 1 ha).2.1 h0 h1 (by omega) h2
  · obtain ⟨a', e, _, hvl, hc⟩ := (p1312 a n i 1 ha).2.2 h1 h2 (by omega) (by omega)
    exact ⟨a', e, hvl, by rw [hc, show i - 1 + 1 = i by omega]⟩
  · unfold m1905; simp only [Bool.false_eq_true, if_false]; rw [if_pos h]
  · unfold m1905; simp only [Bool.false_eq_true, if_false]; rw [if_neg (by omega),
      wrap64_id (by omega) (by omega)]
    obtain ⟨a', e, _, hvl, hc⟩ := (p1312 a n lo (1 + (hi - lo)) ha).2.2 h1 (by omega) (by omega) (by omega)
    exact ⟨a', e, by rw [show n - (hi - lo + 1) = n - (1 + (hi - lo)) by omega]; exact hvl,
      by rw [hc, show lo - 1 + (1 + (hi - lo)) = hi by omega]⟩
  · obtain ⟨_, ok⟩ := p1296 a n n ha
    obtain ⟨a', e, _, hvl, hc⟩ := ok hn0 (Int.le_refl n)
    refine ⟨a', by unfold m2155; rw [hn]; exact e, by simpa using hvl, ?_⟩
    rw [hc]; simp

/-- `sizehint!(a, sz; first, shrink)` (docstring `base/array.jl:1581`) returns `a`
with its contents unchanged, for every request `0 ≤ sz` that memory can hold. -/
def P1617 : Prop := ∀ {α : Type} (a : Arr α) (n sz : Int) (first shrink : Bool), VecOK a n →
    0 ≤ sz → sz ≤ 2 ^ 60 → ∃ a', m1617 a sz first shrink = .ok a' ∧ IsVec a' n ∧ contents a' = contents a

/-- The emptied 100-slot vector of `repro/multidimcov-sizehint-first-empty.jl`. -/
def emptiedVec : Arr Unit := ⟨Mem.undef 100, 1, [0]⟩

theorem sizehint_first_empty :
    ∃ a', m1617 emptiedVec 10 true true = .ok a' ∧ contents a' = contents emptiedVec := by
  exact ⟨_, rfl, rfl⟩

theorem sizehint_growbeg_empty {a : Arr α} {delta : Int} (ha : VecOK a 0)
    (hd : 0 < delta) (hdmax : delta ≤ 2 ^ 60) (hg : a.mem.len < delta) :
    ∃ b, m1151 a delta = .ok b ∧ 1 ≤ b.off ∧ b.off + delta ≤ b.mem.len := by
  obtain ⟨hn, ho, _, hw, hs, _⟩ := vecOK_unpack ha
  unfold m1151
  rw [toInt_ok (by omega) (by omega), bind_ok, if_neg (by omega), if_neg (by omega), hn]
  dsimp only
  rw [checkedAdd_ok (by omega) (by omega), bind_ok, if_neg (by omega)]
  unfold m1116
  rw [checkedAdd_ok (by omega) (by omega), bind_ok]
  simp only []
  rw [if_neg (by omega), checkedMul_ok (by omega) (by omega), bind_ok,
    checkedAdd_ok (by omega) (by omega), bind_ok, checkedAdd_ok (by omega) (by omega), bind_ok]
  simp only [Int.zero_add]
  have hm := m1102_bounds (n := 0) (by omega) (by omega)
  split
  · rename_i hc
    have hq : Int.tdiv (a.mem.len - delta) 2 = (a.mem.len - delta) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by omega)
    rw [hq, memCopy_ok (by omega) (by omega) (by omega), bind_ok, pure_ok, bind_ok, pure_ok]
    refine ⟨_, rfl, by simp; omega, by simp; omega⟩
  · have hq : Int.tdiv (max (m1102 0) (2 * delta + 1) - delta) 2 =
        (max (m1102 0) (2 * delta + 1) - delta) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by rw [Int.max_def]; split <;> omega)
    rw [hq, memCopy_ok (by omega) (by simp [m1114, Int.max_def])
      (by omega), bind_ok, pure_ok, bind_ok, pure_ok]
    refine ⟨_, rfl, by simp [Int.max_def]; split <;> omega,
      by simp [m1114, Int.max_def]; split <;> omega⟩

theorem p1617 : P1617 := by
  intro α a n sz first shrink ha hsz hszmax
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  have hmax0 : 0 ≤ max sz n := by omega
  have hmax1 : max sz n ≤ 2 ^ 60 := by omega
  unfold m1617
  rw [hn, toInt_ok (by omega) (by omega), bind_ok]
  by_cases hfit : max sz n ≤ a.mem.len
  · rw [if_pos hfit]
    split
    · exact ⟨a, rfl, hv, rfl⟩
    · let off : Int := if first && n != 0 then max sz n - n + 1 else 1
      have hoff : 1 ≤ off := by dsimp [off]; split <;> omega
      have hend : n = 0 ∨ off + n - 1 ≤ max sz n := by
        dsimp [off]; split <;> simp_all <;> omega
      have href : (if first && n != 0 then memref (m1114 a.mem (max sz n)) (max sz n - n + 1)
          else .ok 1) = .ok off := by
        dsimp [off]; split
        · unfold memref; rw [if_pos (by simp [m1114]; simp_all; omega)]
        · rfl
      split <;> rename_i hg <;> simp only [hg, Bool.false_eq_true, ↓reduceIte] at href ⊢
      all_goals rw [href, bind_ok, refCopy_ok (by omega) (by simp [m1114]; omega) (by omega),
        bind_ok, pure_ok]
      all_goals refine ⟨_, rfl, hv, ?_⟩
      all_goals
        apply List.ext_getElem?
        intro k
        rw [getElem?_contents, getElem?_contents]
        simp only [length, hv, List.foldr_cons, List.foldr_nil, Int.mul_one, hn]
        split
        · simp only [Arr.at, Mem.copy_get]
          rw [if_pos (by omega)]
          rw [show off + ((k : Int) + 1) - 1 - off + a.off =
            a.off + ((k : Int) + 1) - 1 by omega]
        · rfl
  · rw [if_neg hfit]
    cases first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨b, hb, hvb, _, hp⟩ := m1212_spec (delta := max sz n - n) ha (by omega) (by omega)
      rw [hb, bind_ok, pure_ok]
      refine ⟨_, rfl, rfl, ?_⟩
      apply List.ext_getElem?
      intro k
      rw [getElem?_contents, getElem?_contents]
      simp only [length, hv, List.foldr_cons, List.foldr_nil, Int.mul_one]
      split
      · exact congrArg some (hp _ (by omega) (by omega))
      · rfl
    · simp only [↓reduceIte]
      by_cases hz : n = 0
      · have ha0 : VecOK a 0 := by simpa [hz] using ha
        obtain ⟨b, hb, hb1, hb2⟩ :=
          sizehint_growbeg_empty (delta := max sz n - n) ha0 (by omega) (by omega) (by omega)
        rw [hb, bind_ok]
        unfold refIndex
        rw [if_pos (by omega), bind_ok, pure_ok]
        refine ⟨_, rfl, rfl, ?_⟩
        simp [contents, length, hv, hz]
      · obtain ⟨b, hb, hvb, hvalid, hp⟩ := m1151_spec (delta := max sz n - n) ha (by omega) (by omega)
        have hlb := length_vec b _ hvb
        obtain ⟨hb1, _, hb2⟩ := hvalid
        rw [hlb] at hb2
        rw [hb, bind_ok]
        unfold refIndex
        rw [if_pos (by omega), bind_ok, pure_ok]
        refine ⟨_, rfl, rfl, ?_⟩
        apply List.ext_getElem?
        intro k
        rw [getElem?_contents, getElem?_contents]
        simp only [length, hv, List.foldr_cons, List.foldr_nil, Int.mul_one]
        split
        · have h := hp ((k : Int) + 1) (by omega) (by omega)
          simp only [Arr.at] at h ⊢
          rw [show b.off + (max sz n - n + 1) - 1 + ((k : Int) + 1) - 1 =
            b.off + (max sz n - n + ((k : Int) + 1)) - 1 by omega]
          exact congrArg some h
        · rfl

theorem sizehint_inexact (a : Arr α) (sz : Int) (first shrink : Bool)
    (h : sz < typeminInt ∨ typemaxInt < sz) :
    m1617 a sz first shrink = .error .inexact := by
  unfold m1617 toInt
  rw [if_neg (by omega), bind_error]

/-- A keyword value seen by `Core.kwcall(kwargs, sizehint!, a, sz)`. -/
inductive KwVal where
  | bool (b : Bool)
  | other

/-- `get(kwargs, name, default)::Bool`. -/
def kwBool (kw : List (String × KwVal)) (name : String) (dflt : Bool) : R Bool :=
  match kw.lookup name with
  | none => .ok dflt
  | some (.bool b) => .ok b
  | some .other => .error .typeError

/-- base/array.jl:1652 `Core.kwcall(kwargs, ::typeof(sizehint!), a, sz)` for collections
whose `sizehint!` takes no keywords: type-check `first`/`shrink`, reject any other
keyword with `kwerr` (a `MethodError`), then call the positional `sizehint!(a, sz)`. -/
def m1652 (kw : List (String × KwVal)) (f : A → Int → R A) (a : A) (sz : Int) : R A := do
  let _ ← kwBool kw "first" false
  let _ ← kwBool kw "shrink" true
  if (kw.map Prod.fst).all (fun s => s == "first" || s == "shrink") then f a sz else .error .method

/-- The generic keyword `sizehint!` accepts `first`/`shrink` only as `Bool`s
(`TypeError` otherwise), rejects every other keyword with `MethodError`, and then
behaves exactly as the positional `sizehint!(a, sz)`, ignoring the keywords. -/
def P1652 : Prop := ∀ {A : Type} (kw : List (String × KwVal)) (f : A → Int → R A) (a : A) (sz : Int),
    (kw.lookup "first" = some .other → m1652 kw f a sz = .error .typeError) ∧
    ((∀ v, kw.lookup "first" ≠ some v ∨ v ≠ .other) → kw.lookup "shrink" = some .other →
      m1652 kw f a sz = .error .typeError) ∧
    ((∀ v, kw.lookup "first" = some v → ∃ b, v = .bool b) → (∀ v, kw.lookup "shrink" = some v → ∃ b, v = .bool b) →
      ((∀ p ∈ kw, p.1 = "first" ∨ p.1 = "shrink") → m1652 kw f a sz = f a sz) ∧
      ((∃ p ∈ kw, p.1 ≠ "first" ∧ p.1 ≠ "shrink") → m1652 kw f a sz = .error .method))

theorem kwBool_ok {kw : List (String × KwVal)} {name : String} {d : Bool}
    (h : ∀ v, kw.lookup name = some v → ∃ b, v = .bool b) : ∃ b, kwBool kw name d = .ok b := by
  unfold kwBool
  cases hl : kw.lookup name with
  | none => exact ⟨d, rfl⟩
  | some v => obtain ⟨b, rfl⟩ := h v hl; exact ⟨b, rfl⟩

theorem p1652 : P1652 := by
  intro A kw f a sz
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨fun h3 => ?_, fun h3 => ?_⟩⟩
  · unfold m1652 kwBool; rw [h]; rfl
  · unfold m1652
    have : ∃ b, kwBool kw "first" false = .ok b := by
      unfold kwBool
      cases hl : kw.lookup "first" with
      | none => exact ⟨false, rfl⟩
      | some v =>
        cases v with
        | bool b => exact ⟨b, rfl⟩
        | other => rcases h1 .other with h | h <;> simp_all
    obtain ⟨b, hb⟩ := this
    rw [hb, bind_ok]; unfold kwBool; rw [h2]; rfl
  · obtain ⟨b1, e1⟩ := kwBool_ok (d := false) h1
    obtain ⟨b2, e2⟩ := kwBool_ok (d := true) h2
    unfold m1652; rw [e1, bind_ok, e2, bind_ok, if_pos]
    simp only [List.all_map, List.all_eq_true, Function.comp, Bool.or_eq_true, beq_iff_eq]
    exact h3
  · obtain ⟨b1, e1⟩ := kwBool_ok (d := false) h1
    obtain ⟨b2, e2⟩ := kwBool_ok (d := true) h2
    unfold m1652; rw [e1, bind_ok, e2, bind_ok, if_neg]
    intro hall
    simp only [List.all_map, List.all_eq_true, Function.comp, Bool.or_eq_true, beq_iff_eq] at hall
    obtain ⟨p, hp, h4, h5⟩ := h3
    rcases hall p hp with h | h <;> contradiction

end JuliaLean.MultidimCov.ArrayV2
