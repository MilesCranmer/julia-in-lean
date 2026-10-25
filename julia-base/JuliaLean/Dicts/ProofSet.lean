import JuliaLean.Dicts.ProofInsert

/-!
# `_setindex!`, overwrite and `setindex!`

On an invariant table, `setindex!` stores the pair: the result represents
`rset m k v`, and its `age` advanced by between `1` and `2 count + 21`.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-! ## Reference lookups after `rset` and `rdel` -/

theorem find_filter_of {α : Type} {p f : α → Bool} (h : ∀ x, p x = true → f x = true) :
    ∀ l : List α, (l.filter f).find? p = l.find? p
  | [] => rfl
  | a :: l => by
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos (h a hp), List.find?_cons_of_pos hp, List.find?_cons_of_pos hp]
    · cases hf : f a
      · rw [List.filter_cons_of_neg (by simp [hf]), List.find?_cons_of_neg hp, find_filter_of h l]
      · rw [List.filter_cons_of_pos hf, List.find?_cons_of_neg hp, List.find?_cons_of_neg hp,
          find_filter_of h l]

theorem find_filter_none {α : Type} {p f : α → Bool} (h : ∀ x, p x = true → f x = false) :
    ∀ l : List α, (l.filter f).find? p = none
  | [] => rfl
  | a :: l => by
    cases hf : f a
    · rw [List.filter_cons_of_neg (by simp [hf]), find_filter_none h l]
    · have hp : ¬ p a = true := fun hp => by rw [h a hp] at hf; cases hf
      rw [List.filter_cons_of_pos hf, List.find?_cons_of_neg hp, find_filter_none h l]

theorem eq_congr_left {o : KeyOps K} (hl : o.Lawful) {k k' : K} (h : o.eq k k' = true) (b : K) :
    o.eq k b = o.eq k' b := by
  cases hb : o.eq k' b
  · cases hk : o.eq k b
    · rfl
    · exact absurd (eq_trans' hl h hk) (by rw [hb]; decide)
  · exact hl.trans k k' b h hb

theorem rfind_rdel_ne {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) {k q : K}
    (hqk : o.eq q k = false) : rfind o (rdel o m k) q = rfind o m q := by
  unfold rfind rdel
  apply find_filter_of
  intro x hx
  show (!o.eq k x.1) = true
  cases hkx : o.eq k x.1
  · rfl
  · rw [hl.trans q x.1 k hx (hl.symm k x.1 hkx)] at hqk
    cases hqk

theorem rfind_rdel_eq {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) {k q : K}
    (hqk : o.eq q k = true) : rfind o (rdel o m k) q = none := by
  unfold rfind rdel
  apply find_filter_none
  intro x hx
  show (!o.eq k x.1) = false
  rw [eq_trans' hl hqk hx] <;> rfl

theorem rfind_rset {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (k q : K) (v : V) :
    rfind o (rset o m k v) q = if o.eq q k then some (k, v) else rfind o m q := by
  unfold rset
  by_cases hqk : o.eq q k = true
  · rw [if_pos hqk]
    exact List.find?_cons_of_pos (p := fun e : K × V => o.eq q e.1) (a := (k, v)) hqk
  · rw [if_neg hqk]
    unfold rfind
    rw [List.find?_cons_of_neg (p := fun e : K × V => o.eq q e.1) (a := (k, v)) hqk]
    exact rfind_rdel_ne hl m (Bool.eq_false_iff.2 hqk)

theorem rlookup_rset {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (k q : K) (v : V) :
    rlookup o (rset o m k v) q = if o.eq q k then some v else rlookup o m q := by
  unfold rlookup
  rw [rfind_rset hl]
  by_cases hqk : o.eq q k = true
  · rw [if_pos hqk, if_pos hqk] <;> rfl
  · rw [if_neg hqk, if_neg hqk]

theorem rlookup_rdel {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (k q : K) :
    rlookup o (rdel o m k) q = if o.eq q k then none else rlookup o m q := by
  unfold rlookup
  by_cases hqk : o.eq q k = true
  · rw [if_pos hqk, rfind_rdel_eq hl m hqk] <;> rfl
  · rw [if_neg hqk, rfind_rdel_ne hl m (Bool.eq_false_iff.2 hqk)]

/-- Deleting an absent key changes nothing. -/
theorem rdel_of_absent {o : KeyOps K} {m : RMap K V} {k : K} (h : ∀ e ∈ m, o.eq k e.1 = false) :
    rdel o m k = m := by
  unfold rdel
  rw [List.filter_eq_self]
  intro e he
  simp [h e he]

/-! ## `_setindex!` -/

/-- The table `_setindex!` builds before its idxfloor update. -/
def storeT0 (t : Table K V) (v : V) (key : K) (index sh : Nat) : Table K V :=
  { t with ndel := t.ndel - (if isMissingB (t.slots index) then 1 else 0),
           slots := upd t.slots index sh, keys := upd t.keys index (some key),
           vals := upd t.vals index (some v), count := t.count + 1, age := bump t.age }

/-- The table `_setindex!` builds before its load-factor check. -/
def storeT (t : Table K V) (v : V) (key : K) (index sh : Nat) : Table K V :=
  { storeT0 t v key index sh with idxfloor := if index < t.idxfloor then index else t.idxfloor }

/-- The load-factor check of `_setindex!`. -/
def loadFix (o : KeyOps K) (t : Table K V) : DR (Table K V) :=
  if (t.count + t.ndel) * 3 > t.size * 2 then
    rehash o t (if t.count > 64000 then t.count * 2 else max (t.count * 4) 4)
  else pure t

theorem ite_idxfloor (t : Table K V) (index : Nat) :
    (if index < t.idxfloor then { t with idxfloor := index } else t) =
      { t with idxfloor := if index < t.idxfloor then index else t.idxfloor } := by
  by_cases h : index < t.idxfloor
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem setindexAt_eq (o : KeyOps K) (t : Table K V) (v : V) (key : K) (index sh : Nat) :
    setindexAt o t v key index sh = loadFix o (storeT t v key index sh) := by
  have e : setindexAt o t v key index sh =
      loadFix o (if index < (storeT0 t v key index sh).idxfloor then
        { storeT0 t v key index sh with idxfloor := index } else storeT0 t v key index sh) := rfl
  rw [e, ite_idxfloor] <;> rfl

theorem setindexAt_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {j : Nat}
    {k : K} (v : V) (hj : InsertSlot o t k j) (habs : Absent o t k) (hc : t.count < 2 ^ 33) :
    ∃ t', setindexAt o t v k j (shorthash7 (o.hash k)) = .ok t' ∧ Inv o t' ∧
      List.Perm (tlist t') ((k, v) :: tlist t) ∧ t'.count = t.count + 1 ∧
      ∃ n, 1 ≤ n ∧ n ≤ 3 ∧ AgeStep t t' n := by
  have hfl := hi.idxfloor
  have hj1 := hj.1
  have hst := Inv.store hl hi hj habs (t' := storeT t v k j (shorthash7 (o.hash k))) rfl rfl rfl rfl
    rfl rfl
    (by show 1 ≤ (if j < t.idxfloor then j else t.idxfloor); split <;> omega)
    (by show (if j < t.idxfloor then j else t.idxfloor) ≤ t.idxfloor; split <;> omega)
    (by show (if j < t.idxfloor then j else t.idxfloor) ≤ j; split <;> omega)
    hi.popcursor
  have hcT : (storeT t v k j (shorthash7 (o.hash k))).count = t.count + 1 := rfl
  have haT : (storeT t v k j (shorthash7 (o.hash k))).age = bump t.age := rfl
  rw [setindexAt_eq]
  unfold loadFix
  generalize storeT t v k j (shorthash7 (o.hash k)) = T at hst hcT haT ⊢
  by_cases hload : (T.count + T.ndel) * 3 > T.size * 2
  · rw [if_pos hload]
    have hn1 : T.count < (if T.count > 64000 then T.count * 2 else max (T.count * 4) 4) := by
      split <;> omega
    have hn2 : (if T.count > 64000 then T.count * 2 else max (T.count * 4) 4) ≤ 2 ^ 40 := by
      split <;> omega
    have hle := tableszNat_le (if T.count > 64000 then T.count * 2 else max (T.count * 4) 4)
    obtain ⟨t', h1, hi', hp', -, hc', ha'⟩ := rehash_spec hst.1 _
      (Nat.lt_of_lt_of_le hn1 (tableszNat_ge _)) (by omega)
    refine ⟨t', h1, hi', hp'.trans hst.2, by rw [hc', hcT], 1 + 2, by omega, by omega,
      AgeStep.of_pos ?_ (by omega)⟩
    rw [ha', if_neg (show ¬ T.count = 0 by omega), bump_bump, haT, bump_eq, ageAdd_add]
  · rw [if_neg hload]
    exact ⟨T, rfl, hst.1, hst.2, hcT, 1, Nat.le_refl _, by omega,
      AgeStep.of_pos (by rw [haT, bump_eq]) (by omega)⟩

/-! ## Overwriting an existing key -/

theorem overwrite_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {i : Nat}
    {e : K × V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some e) {k : K}
    (hq : o.eq k e.1 = true) (v : V) :
    Inv o (overwriteAt t v k i) ∧
      List.Perm (tlist (overwriteAt t v k i)) ((k, v) :: (tlist t).filter (fun b => !o.eq k b.1)) ∧
      (overwriteAt t v k i).count = t.count := by
  have hfi := (ent_some he).1
  have hent : ∀ p, ent (overwriteAt t v k i) p = if p = i then some (k, v) else ent t p :=
    ent_store_eq hfi (upd_self t.slots i).symm rfl rfl
  have hdis : ∀ p b, 1 ≤ p → p ≤ t.size → p ≠ i → ent t p = some b → o.eq k b.1 = false := by
    intro p b hp1 hp2 hpi hb
    have hd := hi.distinct i p e b h1 h2 hp1 hp2 (Ne.symm hpi) he hb
    rw [eq_congr_left hl hq]
    exact hd
  have hperm := tlist_store (o := o) (t := t) (t' := overwriteAt t v k i) (e := (k, v)) rfl h1 h2
    (fun p _ _ => hent p) hdis (fun b hb => by rw [he] at hb; cases hb; exact hq)
  have hself := tlist_store (o := o) (t := t) (t' := t) (e := e) rfl h1 h2
    (fun p _ _ => by
      by_cases hp : p = i
      · rw [if_pos hp, hp, he]
      · rw [if_neg hp])
    (fun p b hp1 hp2 hpi hb => hi.distinct i p e b h1 h2 hp1 hp2 (Ne.symm hpi) he hb)
    (fun b hb => by rw [he] at hb; cases hb; exact hl.refl _)
  have hfilt : (tlist t).filter (fun b => !o.eq k b.1) = (tlist t).filter (fun b => !o.eq e.1 b.1) :=
    List.filter_congr (fun b _ => by
      show (!o.eq k b.1) = (!o.eq e.1 b.1)
      rw [eq_congr_left hl hq])
  have hlen : (tlist (overwriteAt t v k i)).length = (tlist t).length := by
    rw [hperm.length_eq, hself.length_eq, hfilt, List.length_cons, List.length_cons]
  obtain ⟨k0, v0, hk0, -, he0, hs0, hc0⟩ := hi.filled h1 h2 hfi
  rw [he] at he0
  cases he0
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hmp : t.maxprobe < t.size := by
    rcases hi.maxprobe with h | h
    · omega
    · exact h
  refine ⟨⟨hi.size, hi.sizeLe, fun p hp1 hp2 => ?_, ?_, ?_, hi.maxprobe, hi.idxfloor, hi.floorLe,
    hi.popcursor⟩, hperm, rfl⟩
  · by_cases hpi : p = i
    · rw [hpi]
      refine Or.inr (Or.inr ⟨k, v, upd_same _ _ _, upd_same _ _ _, ?_, ?_⟩)
      · show t.slots i = shorthash7 (o.hash k)
        rw [hs0, hl.hash_eq k k0 hq]
      · obtain ⟨d, hd, hid, hall⟩ := hc0
        refine ⟨d, hd, ?_, ?_⟩
        · show i = pr t.size (home o t.size k) d
          rw [home_eq_of_eq hl hq]; exact hid
        · show ∀ e, e < d → t.slots (pr t.size (home o t.size k) e) ≠ 0
          rw [home_eq_of_eq hl hq]; exact hall
    · exact SlotOK.transfer (hi.slot p hp1 hp2) rfl (upd_ne _ _ hpi) (upd_ne _ _ hpi)
        (fun k' hc => Chain.mono (t := t) hpow hmp rfl (Nat.le_refl _) (fun _ _ _ h => h) hc)
  · intro a b a' b' ha1 ha2 hb1 hb2 hab hea heb
    show o.eq a'.1 b'.1 = false
    rw [hent] at hea heb
    by_cases hai : a = i
    · rw [if_pos hai] at hea
      cases hea
      have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
      rw [if_neg hbi] at heb
      exact hdis b b' hb1 hb2 hbi heb
    · rw [if_neg hai] at hea
      by_cases hbi : b = i
      · rw [if_pos hbi] at heb
        cases heb
        exact eq_false_symm hl (hdis a a' ha1 ha2 hai hea)
      · rw [if_neg hbi] at heb
        exact hi.distinct a b a' b' ha1 ha2 hb1 hb2 hab hea heb
  · show t.count = (tlist (overwriteAt t v k i)).length
    rw [hlen, hi.count]

/-! ## `setindex!` -/

theorem setindex_of_k2 {o : KeyOps K} {t t1 : Table K V} {v : V} {key : K} {idx : Int} {sh : Nat}
    (h : keyindex2 o t (o.hash key) (o.eq key) = .ok (idx, sh, t1)) :
    setindex o t v key = if idx > 0 then pure (overwriteAt t1 v key idx.toNat)
      else setindexAt o t1 v key (-idx).toNat sh := by
  unfold setindex
  rw [h]
  rfl

/-- Either some stored key is `isequal` to `k`, or `k` is absent. -/
theorem present_or_absent (o : KeyOps K) (t : Table K V) (k : K) :
    (∃ i e, 1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e ∧ o.eq k e.1 = true) ∨ Absent o t k := by
  by_cases hex : ∃ i e, 1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e ∧ o.eq k e.1 = true
  · exact Or.inl hex
  · refine Or.inr fun e he => ?_
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 he
    cases hq : o.eq k e.1
    · rfl
    · exact absurd ⟨i, e, h1, h2, hei, hq⟩ hex

theorem Rep.setindex {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    (hc : t.count < 2 ^ 33) (k : K) (v : V) :
    ∃ t', setindex o t v k = .ok t' ∧ Rep o t' (rset o m k v) ∧
      ∃ n, 1 ≤ n ∧ n ≤ 2 * t.count + 21 ∧ AgeStep t t' n := by
  obtain ⟨idx, t1, n1, hk2, hn1, hout⟩ := keyindex2_spec hl h.1 hc k
  rw [setindex_of_k2 hk2]
  rcases present_or_absent o t k with ⟨i, e, h1, h2, he, hq⟩ | habs
  · obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 he hq
    rw [hidx, ht1, if_pos (by omega), Int.toNat_natCast]
    obtain ⟨hI, hP, -⟩ := overwrite_spec hl h.1 h1 h2 he hq v
    exact ⟨_, rfl, ⟨hI, hP.trans (List.Perm.cons _ (h.2.filter _))⟩, 1, Nat.le_refl _, by omega,
      AgeStep.of_pos (bump_eq _) (by omega)⟩
  · obtain ⟨hneg, hslot⟩ := hout.absent habs
    rw [if_neg (by omega)]
    have habs1 : Absent o t1 k := fun b hb => habs b (hout.perm.mem_iff.1 hb)
    obtain ⟨t', h1', hi', hp', -, n2, hn2a, hn2b, hage⟩ :=
      setindexAt_spec hl hout.inv v hslot habs1 (by rw [hout.count]; exact hc)
    have hm : rdel o m k = m :=
      rdel_of_absent fun b hb => habs b (h.2.mem_iff.2 hb)
    refine ⟨t', h1', ⟨hi', hp'.trans (List.Perm.cons _ ?_)⟩, n1 + n2, by omega, by omega,
      hout.age.trans hage⟩
    rw [hm]
    exact hout.perm.trans h.2

end JuliaLean.Dicts
