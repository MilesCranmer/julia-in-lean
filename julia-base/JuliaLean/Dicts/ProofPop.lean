import JuliaLean.Dicts.ProofDelete

/-!
# `pop!(h::Dict)`

The scan from `popcursor` either finds a filled slot, or the scan from
`idxfloor` does: every filled slot lies at or after `idxfloor`, so a non-empty
table always yields a stored pair, which is then deleted.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

theorem popAny_empty {o : KeyOps K} {t : Table K V} (h : Rep o t []) :
    popAny t = .error .argumentError := by
  have hc0 : t.count = 0 := by rw [h.1.count, h.2.length_eq] <;> rfl
  have hc : (t.count == 0) = true := by simp [hc0]
  unfold popAny
  simp only [hc, ite_true]
  rfl

theorem popAny_at {t : Table K V} {j : Nat} (hc : (t.count == 0) = false)
    (hj : skipDeleted t t.popcursor = j) (hj0 : (j == 0) = false) :
    popAny t = (entryAt { t with popcursor := j + 1 } j >>= fun e =>
      pure (e, deleteAt { t with popcursor := j + 1 } j)) := by
  unfold popAny
  simp only [hc, hj, hj0, Bool.false_eq_true, ite_false]

theorem popAny_floor {t : Table K V} {i : Nat} (hc : (t.count == 0) = false)
    (hj : skipDeleted t t.popcursor = 0) (hi : skipDeleted t t.idxfloor = i) (hi0 : (i != 0) = true) :
    popAny t = (entryAt { t with popcursor := i + 1, idxfloor := i } i >>= fun e =>
      pure (e, deleteAt { t with popcursor := i + 1, idxfloor := i } i)) := by
  unfold popAny
  simp only [hc, hj, hi, hi0, Bool.false_eq_true, ite_false, ite_true, beq_self_eq_true]

theorem Rep.popAny {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    (hne : m ≠ []) :
    ∃ k v t', popAny t = .ok ((k, v), t') ∧ (k, v) ∈ m ∧ Rep o t' (rdel o m k) ∧ AgeStep t t' 1 := by
  have hi := h.1
  have hc0 : t.count ≠ 0 := by
    rw [hi.count, h.2.length_eq]
    intro h0
    exact hne (List.length_eq_zero_iff.1 h0)
  have hc : (t.count == 0) = false := by simp [hc0]
  -- deleting a filled slot `j` of a table that differs from `t` only in its cursors
  have fin : ∀ (t2 : Table K V) (j : Nat), Inv o t2 → t2.size = t.size → t2.age = t.age →
      t2.slots = t.slots → t2.keys = t.keys → t2.vals = t.vals → 1 ≤ j → j ≤ t.size →
      isFilledB (t.slots j) = true →
      ∃ k v, entryAt t2 j = .ok (k, v) ∧ (k, v) ∈ m ∧
        Rep o (JuliaLean.Dicts.deleteAt t2 j) (rdel o m k) ∧
        AgeStep t (JuliaLean.Dicts.deleteAt t2 j) 1 := by
    intro t2 j hI2 hs2 ha2 hsl hk hv hj1 hj2 hf
    obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled hj1 hj2 hf
    have he2 : ent t2 j = some (k, v) := by
      rw [ent_congr (t := t) (by rw [hsl]) (by rw [hk]) (by rw [hv])]
      exact he
    have htl : tlist t2 = tlist t := tlist_congr hs2 (fun p _ _ =>
      ent_congr (by rw [hsl]) (by rw [hk]) (by rw [hv]))
    obtain ⟨hr, ha⟩ := Rep.deleteAt (m := m) hl ⟨hI2, by rw [htl]; exact h.2⟩ hj1
      (by rw [hs2]; exact hj2)
      he2 (hl.refl k)
    exact ⟨k, v, entryAt_of_ent he2, h.2.mem_iff.1 (mem_tlist.2 ⟨j, hj1, hj2, he⟩), hr,
      ⟨by rw [ha.1, ha2], fun h0 => absurd h0 (by omega)⟩⟩
  rcases skipDeletedLoop_spec t (t.size + 1 - t.popcursor) t.popcursor hi.popcursor with
    ⟨h0, -⟩ | ⟨hj1, hj2, hjf, -⟩
  · -- nothing filled from `popcursor` on: rescan from `idxfloor`
    have hj : skipDeleted t t.popcursor = 0 := h0
    obtain ⟨e, hem⟩ : ∃ e, e ∈ tlist t := by
      cases hm : tlist t with
      | nil =>
        have := hi.count
        rw [hm] at this
        exact absurd this hc0
      | cons e _ => exact ⟨e, List.mem_cons_self⟩
    obtain ⟨p, hp1, hp2, hpe⟩ := mem_tlist.1 hem
    have hpf := (ent_some hpe).1
    have hfl := hi.floorLe p hp1 hp2 hpf
    rcases skipDeletedLoop_spec t (t.size + 1 - t.idxfloor) t.idxfloor hi.idxfloor with
      ⟨-, hnone⟩ | ⟨hi1, hi2, hif, hbefore⟩
    · exact absurd hpf (by rw [hnone p hfl (by omega)]; decide)
    · have hii : skipDeleted t t.idxfloor = skipDeletedLoop t (t.size + 1 - t.idxfloor) t.idxfloor :=
        rfl
      generalize skipDeletedLoop t (t.size + 1 - t.idxfloor) t.idxfloor = i at hii hi1 hi2 hif hbefore
      have hi0 : (i != 0) = true := by
        have := hi.idxfloor
        simp only [bne_iff_ne, ne_eq]
        omega
      rw [popAny_floor hc hj hii hi0]
      have hfl2 : ∀ q, 1 ≤ q → q ≤ t.size → isFilledB (t.slots q) = true → i ≤ q := by
        intro q hq1 hq2 hqf
        have hq := hi.floorLe q hq1 hq2 hqf
        by_cases hlt : q < i
        · rw [hbefore q hq hlt] at hqf
          cases hqf
        · omega
      have hI2 : Inv o { t with popcursor := i + 1, idxfloor := i } :=
        ⟨hi.size, hi.sizeLe, hi.slot, hi.distinct, hi.count, hi.maxprobe,
          show 1 ≤ i by have := hi.idxfloor; omega, hfl2, show 1 ≤ i + 1 by omega⟩
      obtain ⟨k, v, hent, hmem, hr, ha⟩ := fin _ i hI2 rfl rfl rfl rfl rfl
        (by have := hi.idxfloor; omega) (by omega) hif
      rw [hent]
      exact ⟨k, v, _, rfl, hmem, hr, ha⟩
  · have hj : skipDeleted t t.popcursor = skipDeletedLoop t (t.size + 1 - t.popcursor) t.popcursor :=
      rfl
    generalize skipDeletedLoop t (t.size + 1 - t.popcursor) t.popcursor = j at hj hj1 hj2 hjf
    have hj0 : (j == 0) = false := by
      have := hi.popcursor
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    rw [popAny_at hc hj hj0]
    have hI2 : Inv o { t with popcursor := j + 1 } :=
      ⟨hi.size, hi.sizeLe, hi.slot, hi.distinct, hi.count, hi.maxprobe, hi.idxfloor, hi.floorLe,
        show 1 ≤ j + 1 by omega⟩
    obtain ⟨k, v, hent, hmem, hr, ha⟩ := fin _ j hI2 rfl rfl rfl rfl rfl
      (by have := hi.popcursor; omega) (by omega) hjf
    rw [hent]
    exact ⟨k, v, _, rfl, hmem, hr, ha⟩

end JuliaLean.Dicts
