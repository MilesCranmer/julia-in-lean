import JuliaLean.MultidimCov.ArrayV2Push

/-!
Contracts of `append!`/`prepend!` with general iterators (master
`base/array.jl:1435-1525`), modelled in `ArrayV2Vector`.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `append!(a, iter)` for an iterator (docstring `base/array.jl:1383`): the
result is `a`'s old elements followed by the items of `iter`, each converted to
the element type in order, whether or not `iter` has a length; a failing
conversion propagates. The memory plus the new items stay below `2^59` slots. -/
def P1435 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int) (xs : List β), VecOK a n →
    a.mem.len + xs.length ≤ 2 ^ 59 → ∀ sized : Bool,
    (∀ e, convList conv xs = .error e → m1435 conv a xs sized = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a', m1435 conv a xs sized = .ok a' ∧ IsVec a' (n + xs.length) ∧
      contents a' = contents a ++ ys.map some)

theorem p1435 : P1435 := by
  intro α β conv a n xs ha hb sized
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  cases sized
  · refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · exact (pushEach_spec conv xs a n ha (by omega)).1 e h
    · obtain ⟨a', e, ha', _, hc⟩ := (pushEach_spec conv xs a n ha (by omega)).2 ys h
      exact ⟨a', e, ha'.1, hc⟩
  · obtain ⟨a1, e1, ha1, ho1, hc1⟩ := m1617_end (sz := n + xs.length) ha (by omega)
      (by rw [Int.max_def]; split <;> omega)
    have hk : toInt (xs.length : Int) = .ok (xs.length : Int) := toInt_ok (by omega) (by omega)
    refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · simp only [m1435, if_true, m1439, hk, bind_ok, hn, e1]
      exact (pushEach_spec conv xs a1 n ha1 (by omega)).1 e h
    · obtain ⟨a', e, ha', _, hc⟩ := (pushEach_spec conv xs a1 n ha1 (by omega)).2 ys h
      refine ⟨a', ?_, ha'.1, by rw [hc, hc1]⟩
      simp only [m1435, if_true, m1439, hk, bind_ok, hn, e1]; exact e

/-- `prepend!(a, iter)` for an iterator (docstring `base/array.jl:1455`): the
items of `iter`, converted in order, followed by `a`'s old elements, whether or
not `iter` has a length; a failing conversion propagates. -/
def P1500 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int) (xs : List β), VecOK a n →
    n + xs.length < 2 ^ 59 → ∀ sized : Bool,
    (∀ e, convList conv xs = .error e → m1500 conv a xs sized = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a', m1500 conv a xs sized = .ok a' ∧ IsVec a' (n + xs.length) ∧
      contents a' = ys.map some ++ contents a)

theorem rev_after_pushfirst {a : Arr α} {n : Int} {ys : List α} (ha : VecOK a (n + ys.length))
    (hc : contents a = (ys.map some).reverse ++ c) (hlc : c.length = n.toNat) (hn0 : 0 ≤ n) :
    ∃ a', m2317 a 1 ys.length = .ok a' ∧ IsVec a' (n + ys.length) ∧ contents a' = ys.map some ++ c := by
  obtain ⟨hn, ho, _, hw, hs, hv⟩ := vecOK_unpack ha
  by_cases h2 : 2 ≤ ys.length
  · have hassigned : ∀ t, 1 ≤ t → t ≤ (ys.length : Int) → (a.at t).isSome := by
      intro t t1 t2
      have hk : (t - 1).toNat < (contents a).length := by simp [hn]; omega
      have := getElem_contents a (t - 1).toNat hk
      rw [show ((t - 1).toNat : Int) + 1 = t by omega] at this
      rw [← this]
      simp only [hc]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    obtain ⟨a', e, hv', hc'⟩ := (p2317 a (n + ys.length) 1 ys.length ha).2.2 (by omega) (by omega) (by omega)
      hassigned
    refine ⟨a', e, hv', ?_⟩
    rw [hc', hc]
    simp only [show ((1 : Int) - 1).toNat = 0 by rfl, List.take_zero, List.drop_zero, List.nil_append]
    rw [show (ys.length : Int) - 1 + 1 = ys.length by omega, Int.toNat_natCast,
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
      List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]
    simp
  · refine ⟨a, ?_, ha.1, ?_⟩
    · exact (p2317 a (n + ys.length) 1 ys.length ha).1 (by unfold typeminInt; omega) (by unfold typemaxInt; omega)
        (by unfold typeminInt; omega) (by unfold typemaxInt; omega) (by omega)
    · rw [hc]
      match ys, h2 with
      | [], _ => simp
      | [y], _ => simp
      | _ :: _ :: _, h => simp at h

theorem convList_length (conv : β → R α) : ∀ (xs : List β) (ys : List α),
    convList conv xs = .ok ys → ys.length = xs.length
  | [], ys, h => by simp [convList] at h; subst h; rfl
  | x :: xs, ys, h => by
    unfold convList at h
    cases hx : conv x with
    | error e => rw [hx, bind_error] at h; cases h
    | ok y =>
      rw [hx, bind_ok] at h
      cases hxs : convList conv xs with
      | error e => rw [hxs, bind_error] at h; cases h
      | ok zs =>
        rw [hxs, bind_ok, pure_ok, Except.ok.injEq] at h; subst h
        simp [convList_length conv xs zs hxs]

theorem p1500 : P1500 := by
  intro α β conv a n xs ha hb sized
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  have hlen := convList_length conv xs
  have tail : ∀ a1 : Arr α, VecOK a1 n → contents a1 = contents a →
      (∀ e, convList conv xs = .error e → (do let (a, n) ← pushfirstEach conv a1 0 xs; m2317 a 1 n) = .error e) ∧
      (∀ ys, convList conv xs = .ok ys → ∃ a', (do let (a, n) ← pushfirstEach conv a1 0 xs; m2317 a 1 n) = .ok a' ∧
        IsVec a' (n + xs.length) ∧ contents a' = ys.map some ++ contents a) := by
    intro a1 ha1 hc1
    refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · rw [(pushfirstEach_spec conv xs a1 n 0 ha1 (by omega)).1 e h, bind_error]
    · obtain ⟨a2, e2, ha2, hc2⟩ := (pushfirstEach_spec conv xs a1 n 0 ha1 (by omega)).2 ys h
      have hl := hlen ys h
      rw [e2, bind_ok]
      simp only [Int.zero_add]
      rw [← hl] at ha2
      obtain ⟨a3, e3, hv3, hc3⟩ := rev_after_pushfirst ha2 (c := contents a1) hc2
        (by simp [length_vec a1 n ha1.1]) hn0
      rw [hl] at hv3 e3
      exact ⟨a3, e3, hv3, by rw [hc3, hc1]⟩
  cases sized
  · exact tail a ha rfl
  · obtain ⟨a1, e1, ha1, hc1⟩ := m1617_beg (sz := n + xs.length) ha (by omega)
      (by rw [Int.max_def]; split <;> omega)
    have hk : toInt (xs.length : Int) = .ok (xs.length : Int) := toInt_ok (by omega) (by omega)
    have := tail a1 ha1 hc1
    simp only [m1500, if_true, m1504, hk, bind_ok, hn, e1]
    exact this

/-- Several collections (base/array.jl:1437, 1502) agree with the one-collection
methods applied in turn: `append!(a, v₁, …, vₖ)` is `append!(append!(a, v₁), v₂, …)`
and `prepend!(a, v₁, …, vₖ)` is `prepend!(prepend!(a, vₖ), v₁, …, vₖ₋₁)`, so
`v₁` ends up leftmost. (Each collection is read after the earlier ones were
added; with `a` itself among them that breaks the documented result: refuted
entry `arrayops-append-many-self`.) -/
def P1437 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (v : Src α β) (vs : List (Src α β)),
    m1437 conv a [] = .ok a ∧ m1437 conv a (v :: vs) = (appendOne conv a v >>= fun a => m1437 conv a vs) ∧
    m1502 conv a [] = .ok a ∧ m1502 conv a (vs ++ [v]) = (prependOne conv a v >>= fun a => m1502 conv a vs)

theorem p1437 : P1437 := by
  intro α β conv a v vs
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold m1502
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldlM_cons]

end JuliaLean.MultidimCov.ArrayV2
