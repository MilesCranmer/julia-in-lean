import JuliaLean.Dicts.ProofReach

/-!
# `ht_keyindex` with a key of any type

`ht_keyindex(h, key)` (`base/dict.jl:241-263`) accepts a `key` of any type: it
hashes `key` and compares it with `key === k || isequal(key, k)`. A key of a
type `Q` other than the key type `K` is described by a `Conv Q K`
(`JuliaLean.Dicts.Conv`). These lemmas generalise the `K`-key lookup lemmas of
`JuliaLean.Dicts` to such keys.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V Q : Type}

/-- A foreign key type consistent with `hash`/`isequal` (`base/hashing.jl:12-16`):
a key `isequal` to a stored key has its hash, the match respects `isequal`
among stored keys, and two stored keys matching the same lookup key are
`isequal` (transitivity of `isequal`). -/
structure QLawful (o : KeyOps K) (c : Conv Q K) : Prop where
  hash_eq : ∀ q k, c.iseq q k = true → c.hash q = o.hash k
  iseq_eq : ∀ q k k', c.iseq q k = true → o.eq k k' = true → c.iseq q k' = true
  iseq_uniq : ∀ q k k', c.iseq q k = true → c.iseq q k' = true → o.eq k k' = true

/-- Keys of the key type form a lawful foreign key type. -/
theorem qlawful_self {o : KeyOps K} (hl : o.Lawful) : QLawful o (Conv.self o) where
  hash_eq q k h := hl.hash_eq q k h
  iseq_eq q k k' h1 h2 := hl.trans q k k' h1 h2
  iseq_uniq q k k' h1 h2 := hl.trans k q k' (hl.symm q k h1) h2

/-- The stored pair matching a lookup key `q`. -/
def rfindQ (c : Conv Q K) (m : RMap K V) (q : Q) : Option (K × V) := m.find? (fun e => c.iseq q e.1)

theorem htKeyindexQ_absent {o : KeyOps K} {t : Table K V} (hi : Inv o t) (hq : JInt .u64)
    {mt : K → Bool} (habs : ∀ e ∈ tlist t, mt e.1 = false) : htKeyindex t hq mt = .ok (-1) := by
  by_cases hc : t.count = 0
  · unfold htKeyindex
    rw [hc] <;> rfl
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  congr 1
  have hr := hashindex_range hp.1 hq
  rcases keyindexLoop_cases t (shorthash7 hq) mt (fun j => 1 ≤ j ∧ j ≤ t.size)
      (fun j hj => nextIdx_range hp.1 hj.1 hj.2) (t.maxprobe + 1) _ hr with h | ⟨j, hj, hhit, _⟩
  · exact h
  · exfalso
    obtain ⟨hs, k2, hk2, hm2⟩ := hitAt_true hhit
    have hf2 : isFilledB (t.slots j) = true := by rw [hs]; exact shorthash7_filled _
    obtain ⟨k3, v3, hk3, -, he3, -, -⟩ := hi.filled hj.1 hj.2 hf2
    rw [hk2] at hk3
    cases hk3
    have := habs _ (mem_tlist.2 ⟨j, hj.1, hj.2, he3⟩)
    rw [hm2] at this
    cases this

theorem htKeyindexQ_found {o : KeyOps K} {c : Conv Q K} (hq : QLawful o c) {t : Table K V}
    (hi : Inv o t) {q : Q} {i : Nat} {k : K} {v : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size)
    (he : ent t i = some (k, v)) (hm : c.iseq q k = true) :
    htKeyindex t (c.hash q) (c.iseq q) = .ok (i : Int) := by
  have hc := hi.count_pos h1 h2 he
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  have hfill := (ent_some he).1
  obtain ⟨k', v', hk, hv, -, hs, hch⟩ := hi.filled h1 h2 hfill
  have hkk : k' = k := by rw [(ent_some he).2.1] at hk; cases hk; rfl
  subst hkk
  obtain ⟨d, hd, hid, hall⟩ := hch
  have hh : home o t.size k' = (hashindex (c.hash q) t.size).1 := by
    unfold home; rw [hq.hash_eq q k' hm]
  have hhr := home_range hp.1 k' (o := o)
  rw [← hh]
  have hsh : shorthash7 (c.hash q) = shorthash7 (o.hash k') := by rw [hq.hash_eq q k' hm]
  congr 1
  rw [hid]
  apply keyindexLoop_found t (shorthash7 (c.hash q)) (c.iseq q) (home o t.size k') d
    (t.maxprobe + 1) 0 (Nat.zero_le _) (by omega)
  · intro e _ hed
    refine ⟨hall e hed, ?_⟩
    cases hhit : hitAt t (shorthash7 (c.hash q)) (c.iseq q) (pr t.size (home o t.size k') e)
    · rfl
    · exfalso
      obtain ⟨hs', k2, hk2, hm2⟩ := hitAt_true hhit
      have hr := pr_range hp.1 hhr.1 hhr.2 (show e < t.size by omega)
      have hf2 : isFilledB (t.slots (pr t.size (home o t.size k') e)) = true := by
        rw [hs']; exact shorthash7_filled _
      obtain ⟨k3, v3, hk3, -, he3, -, -⟩ := hi.filled hr.1 hr.2 hf2
      rw [hk2] at hk3
      cases hk3
      have hne : pr t.size (home o t.size k') e ≠ i := by
        intro heq
        rw [hid] at heq
        have := pr_inj hp.1 hhr.1 hhr.2 (show e < t.size by omega) (show d < t.size by omega) heq
        omega
      have hdis := hi.distinct _ i _ _ hr.1 hr.2 h1 h2 hne he3 he
      dsimp only at hdis
      rw [hq.iseq_uniq q k2 k' hm2 hm] at hdis
      cases hdis
  · exact hitAt_of (by rw [← hid, hs, hsh]) (by rw [← hid]; exact hk) hm
  · rw [← hid, hs]; exact shorthash7_ne0 _

theorem find_unique {o : KeyOps K} {c : Conv Q K} (hq : QLawful o c) {q : Q} :
    ∀ {m : RMap K V} {e : K × V}, Distinct o m → e ∈ m → c.iseq q e.1 = true →
      m.find? (fun e => c.iseq q e.1) = some e
  | [], _, _, he, _ => absurd he List.not_mem_nil
  | a :: rest, e, hd, he, heq => by
    have hpa := List.pairwise_cons.1 hd
    rcases List.mem_cons.1 he with rfl | hr
    · exact List.find?_cons_of_pos heq
    · cases ha : c.iseq q a.1
      · rw [List.find?_cons_of_neg (by simp [ha])]
        exact find_unique hq hpa.2 hr heq
      · exfalso
        have := hpa.1 e hr
        rw [hq.iseq_uniq q a.1 e.1 ha heq] at this
        cases this

/-- `ht_keyindex` with a foreign key on a table representing `m`: the index
of the stored pair `rfindQ` finds, or `-1`. -/
theorem Rep.keyindexQ {o : KeyOps K} (hl : o.Lawful) {c : Conv Q K} (hq : QLawful o c)
    {t : Table K V} {m : RMap K V} (h : Rep o t m) (q : Q) :
    match rfindQ c m q with
    | some e => ∃ i : Nat, htKeyindex t (c.hash q) (c.iseq q) = .ok (i : Int) ∧ 1 ≤ i ∧
        i ≤ t.size ∧ ent t i = some e
    | none => htKeyindex t (c.hash q) (c.iseq q) = .ok (-1) := by
  have hd : Distinct o (tlist t) := tlist_pairwise h.1
  by_cases hex : ∃ e ∈ tlist t, c.iseq q e.1 = true
  · obtain ⟨e, hem, heq⟩ := hex
    have hdm : Distinct o m := Distinct.perm hl hd h.2
    have hfind : rfindQ c m q = some e := find_unique hq hdm (h.2.mem_iff.1 hem) heq
    rw [hfind]
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    obtain ⟨k, v⟩ := e
    exact ⟨i, htKeyindexQ_found hq h.1 h1 h2 hei heq, h1, h2, hei⟩
  · have habs : ∀ e ∈ tlist t, c.iseq q e.1 = false := by
      intro e he
      cases hq' : c.iseq q e.1
      · rfl
      · exact absurd ⟨e, he, hq'⟩ hex
    have hfind : rfindQ c m q = none := by
      unfold rfindQ
      rw [List.find?_eq_none]
      intro e hem
      have := habs e (h.2.mem_iff.2 hem)
      simp [this]
    rw [hfind]
    exact htKeyindexQ_absent h.1 _ habs

end JuliaLean.DictsCov
