import JuliaLean.Dicts.ProofDelete

/-!
# The `filter!` loop of `Set`

`filterLoop` iterates over a set by slot index and deletes the current key
when the predicate fails. `_delete!` at slot `j` changes only slot `j` and
tombstones, so every filled slot after `j` keeps its pair: the loop visits
exactly the pairs present initially and keeps those satisfying the predicate.
-/

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

theorem ent_eq_fill {V : Type} {t t' : Table K V} {q : Nat}
    (hf : isFilledB (t'.slots q) = isFilledB (t.slots q)) (hk : t'.keys q = t.keys q)
    (hv : t'.vals q = t.vals q) : ent t' q = ent t q := by
  unfold ent
  rw [hf, hk, hv]

/-- The loop at iteration state `i`: the slots before `i` are filtered, the
others are as in the initial set `s`. -/
structure SInv (o : KeyOps K) (p : K → Bool) (s : SetT K) (i : Nat) (T : SetT K) : Prop where
  inv : Inv o T
  size : T.size = s.size
  ents : ∀ q, 1 ≤ q → q ≤ s.size →
    ent T q = if q < i then (ent s q).filter (fun e => p e.1) else ent s q
  fill : ∀ q, i ≤ q → q ≤ s.size → isFilledB (T.slots q) = isFilledB (s.slots q)

theorem SInv.init {o : KeyOps K} {p : K → Bool} {s : SetT K} (hi : Inv o s) :
    SInv o p s s.idxfloor s := by
  refine ⟨hi, rfl, fun q hq1 hq2 => ?_, fun _ _ _ => rfl⟩
  by_cases hq : q < s.idxfloor
  · rw [if_pos hq]
    have hf : isFilledB (s.slots q) = false := by
      cases hfq : isFilledB (s.slots q)
      · rfl
      · have := hi.floorLe q hq1 hq2 hfq
        omega
    rw [ent_of_not_filled hf] <;> rfl
  · rw [if_neg hq]

/-- Moving past slots that are not filled. -/
theorem SInv.advance {o : KeyOps K} {p : K → Bool} {s T : SetT K} {i j : Nat} (h : SInv o p s i T)
    (hij : i ≤ j) (hnf : ∀ q, i ≤ q → q < j → isFilledB (T.slots q) = false) :
    SInv o p s j T := by
  refine ⟨h.inv, h.size, fun q hq1 hq2 => ?_, fun q hq1 hq2 => h.fill q (by omega) hq2⟩
  rw [h.ents q hq1 hq2]
  by_cases hqi : q < i
  · rw [if_pos hqi, if_pos (by omega)]
  · rw [if_neg hqi]
    by_cases hqj : q < j
    · rw [if_pos hqj]
      have hf : isFilledB (s.slots q) = false := by
        rw [← h.fill q (by omega) hq2]
        exact hnf q (by omega) hqj
      rw [ent_of_not_filled hf] <;> rfl
    · rw [if_neg hqj]

theorem SInv.top {o : KeyOps K} {p : K → Bool} {s T : SetT K} {i : Nat} (h : SInv o p s i T)
    (hi : s.size + 1 ≤ i) : SInv o p s (s.size + 1) T :=
  ⟨h.inv, h.size, fun q hq1 hq2 => by rw [h.ents q hq1 hq2, if_pos (by omega), if_pos (by omega)],
   fun q hq1 hq2 => absurd hq2 (by omega)⟩

/-- Keeping the pair at slot `j`. -/
theorem SInv.stay {o : KeyOps K} {p : K → Bool} {s T : SetT K} {j : Nat} (h : SInv o p s j T)
    {e : K × Unit} (he : ent T j = some e) (hp : p e.1 = true) : SInv o p s (j + 1) T := by
  refine ⟨h.inv, h.size, fun q hq1 hq2 => ?_, fun q hq1 hq2 => h.fill q (by omega) hq2⟩
  rw [h.ents q hq1 hq2]
  by_cases hqj : q = j
  · rw [hqj, if_neg (by omega), if_pos (by omega)]
    have hs : ent s j = some e := by
      rw [← he, h.ents j (by omega) (by omega), if_neg (by omega)]
    rw [hs]
    show some e = (if p e.1 = true then some e else none)
    rw [if_pos hp]
  · by_cases hlt : q < j
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- Deleting the pair at slot `j`. -/
theorem SInv.drop {o : KeyOps K} (hl : o.Lawful) {p : K → Bool} {s T : SetT K} {j : Nat}
    (h : SInv o p s j T) (hj1 : 1 ≤ j) (hj2 : j ≤ s.size) {e : K × Unit} (he : ent T j = some e)
    (hp : p e.1 = false) : SInv o p s (j + 1) (deleteAt T j) := by
  have hj2' : j ≤ T.size := by rw [h.size]; exact hj2
  obtain ⟨hI, -, -, -, hsz, hk, hv, -, -, -, hnf, hfil⟩ := deleteAt_spec hl h.inv hj1 hj2' he
  have hs : ent s j = some e := by rw [← he, h.ents j hj1 hj2, if_neg (by omega)]
  refine ⟨hI, by rw [hsz, h.size], fun q hq1 hq2 => ?_, fun q hq1 hq2 => ?_⟩
  · by_cases hqj : q = j
    · rw [hqj, ent_of_not_filled hnf, if_pos (by omega), hs]
      show none = (if p e.1 = true then some e else none)
      rw [hp] <;> rfl
    · rw [ent_eq_fill (hfil q hqj) (by rw [hk, upd_ne _ _ hqj]) (by rw [hv, upd_ne _ _ hqj]),
        h.ents q hq1 hq2]
      by_cases hlt : q < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  · rw [hfil q (by omega)]
    exact h.fill q (by omega) hq2

theorem SInv.tlist_eq {o : KeyOps K} {p : K → Bool} {s T : SetT K} (h : SInv o p s (s.size + 1) T) :
    tlist T = (tlist s).filter (fun e => p e.1) := by
  unfold tlist
  rw [h.size, List.filter_filterMap]
  apply filterMap_congr_mem
  intro q hq
  rw [List.mem_range'_1] at hq
  rw [h.ents q hq.1 (by omega), if_pos (by omega)]

/-- An iteration that finds no filled slot ends the loop. -/
theorem filterLoop_none {o : KeyOps K} {keep : K → DR Bool} {left : Nat} {T : SetT K} {i : Nat}
    (hj : skipDeleted T i = 0) : filterLoop o keep (left + 1) T i = .ok T := by
  rw [filterLoop.eq_2]
  simp only [hj] <;> rfl

/-- An iteration at the filled slot `j` holding `x`, kept by the predicate. -/
theorem filterLoop_keep {o : KeyOps K} {keep : K → DR Bool} {left : Nat} {T : SetT K}
    {i j : Nat} {x : K} (hj : skipDeleted T i = j) (hj0 : j ≠ 0)
    (hx : T.keys j = some x) (hb : keep x = .ok true) :
    filterLoop o keep (left + 1) T i = filterLoop o keep left T (j + 1) := by
  have hj0' : (j == 0) = false := by rw [beq_eq_false_iff_ne]; exact hj0
  rw [filterLoop.eq_2]
  simp only [hj, hj0', hx, hb, except_ok_bind] <;> rfl

/-- An iteration at the filled slot `j` holding `x`, deleted by the predicate. -/
theorem filterLoop_drop {o : KeyOps K} {keep : K → DR Bool} {left : Nat} {T T' : SetT K}
    {i j : Nat} {x : K} (hj : skipDeleted T i = j) (hj0 : j ≠ 0)
    (hx : T.keys j = some x) (hb : keep x = .ok false) (hd : setDelete o T x = .ok T') :
    filterLoop o keep (left + 1) T i = filterLoop o keep left T' (j + 1) := by
  have hj0' : (j == 0) = false := by rw [beq_eq_false_iff_ne]; exact hj0
  rw [filterLoop.eq_2]
  simp only [hj, hj0', hx, hb, hd, except_ok_bind] <;> rfl

/-- The loop from state `i` filters the remaining slots. -/
theorem filterLoop_spec {o : KeyOps K} (hl : o.Lawful) {keep : K → DR Bool} {p : K → Bool}
    (hk : ∀ x, keep x = .ok (p x)) (s : SetT K) :
    ∀ fuel i T, 1 ≤ i → s.size + 1 - i ≤ fuel → SInv o p s i T →
      ∃ T', filterLoop o keep fuel T i = .ok T' ∧ SInv o p s (s.size + 1) T'
  | 0, i, T, _, hf, hS => ⟨T, rfl, hS.top (by omega)⟩
  | left + 1, i, T, hi1, hf, hS => by
    have hTs := hS.size
    have hjd : skipDeleted T i = skipDeletedLoop T (T.size + 1 - i) i := rfl
    rcases skipDeletedLoop_spec T (T.size + 1 - i) i hi1 with ⟨h0, hall⟩ | ⟨ha, hb, hc, hd⟩
    · refine ⟨T, ?_, ?_⟩
      · exact filterLoop_none (hjd.trans h0)
      · rw [hTs] at hall
        by_cases hle : i ≤ s.size + 1
        · exact hS.advance hle (fun q hq1 hq2 => hall q hq1 (by omega))
        · exact hS.top (by omega)
    · generalize hJ : skipDeletedLoop T (T.size + 1 - i) i = j at ha hb hc hd
      have hj : skipDeleted T i = j := hjd.trans hJ
      rw [hTs] at hb
      have hj1 : 1 ≤ j := by omega
      have hj2 : j ≤ s.size := by omega
      have hS' := hS.advance ha hd
      obtain ⟨x, u, hkx, -, hent, -, -⟩ := hS'.inv.filled hj1 (by rw [hTs]; exact hj2) hc
      cases hpx : p x with
      | true =>
        have e : filterLoop o keep (left + 1) T i = filterLoop o keep left T (j + 1) :=
          filterLoop_keep hj (by omega) hkx (by rw [hk x, hpx])
        rw [e]
        exact filterLoop_spec hl hk s left (j + 1) T (by omega) (by omega) (hS'.stay hent hpx)
      | false =>
        have hdel : setDelete o T x = .ok (deleteAt T j) := by
          show dictDelete o T x = _
          rw [dictDelete_of (htKeyindex_found hl hS'.inv hj1 (by rw [hTs]; exact hj2) hent
            (hl.refl x)), if_pos (by omega), Int.toNat_natCast] <;> rfl
        have e : filterLoop o keep (left + 1) T i =
            filterLoop o keep left (deleteAt T j) (j + 1) :=
          filterLoop_drop hj (by omega) hkx (by rw [hk x, hpx]) hdel
        rw [e]
        exact filterLoop_spec hl hk s left (j + 1) _ (by omega) (by omega)
          (hS'.drop hl hj1 hj2 hent hpx)

/-- `filter!(keep, s)` on a set: the pairs whose key satisfies `p`. -/
theorem setFilterBang_spec {o : KeyOps K} (hl : o.Lawful) {keep : K → DR Bool} {p : K → Bool}
    (hk : ∀ x, keep x = .ok (p x)) {s : SetT K} (hi : Inv o s) :
    ∃ s', setFilterBang o keep s = .ok s' ∧ Inv o s' ∧
      tlist s' = (tlist s).filter (fun e => p e.1) := by
  obtain ⟨T, h1, hS⟩ := filterLoop_spec hl hk s (s.size + 1) s.idxfloor s hi.idxfloor (by omega)
    (SInv.init hi)
  exact ⟨T, h1, hS.inv, hS.tlist_eq⟩

theorem setFilterBang_rep {o : KeyOps K} (hl : o.Lawful) {keep : K → DR Bool} {p : K → Bool}
    (hk : ∀ x, keep x = .ok (p x)) {s : SetT K} {m : RMap K Unit} (h : Rep o s m) :
    ∃ s', setFilterBang o keep s = .ok s' ∧ Rep o s' (m.filter (fun e => p e.1)) := by
  obtain ⟨s', h1, hi, ht⟩ := setFilterBang_spec hl hk h.1
  exact ⟨s', h1, hi, by rw [ht]; exact h.2.filter _⟩

end JuliaLean.Dicts.SetProofs
