import JuliaLean.Dicts.ProofLookup

/-!
# `rehash!`

With more slots than keys, `rehash!` copies every pair into a fresh table
that satisfies the invariant: the probe loop always finds an empty slot
because fewer than `newsz` slots are filled.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- Updating slot `j` with a filled byte stores `(k, v)` there. -/
theorem ent_store_eq {t t' : Table K V} {j : Nat} {k : K} {v : V} {b : Nat}
    (hb : isFilledB b = true) (hs : t'.slots = upd t.slots j b) (hk : t'.keys = upd t.keys j (some k))
    (hv : t'.vals = upd t.vals j (some v)) (i : Nat) :
    ent t' i = if i = j then some (k, v) else ent t i := by
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl]
    apply ent_of_filled
    · rw [hs, upd_same]; exact hb
    · rw [hk, upd_same]
    · rw [hv, upd_same]
  · rw [ite_eq_right h]
    unfold ent
    rw [hs, hk, hv, upd_ne _ _ h, upd_ne _ _ h, upd_ne _ _ h]

theorem length_filterMap_ent_all {t : Table K V} :
    ∀ n s, (∀ p, s ≤ p → p < s + n → ent t p ≠ none) → ((List.range' s n).filterMap (ent t)).length = n
  | 0, _, _ => rfl
  | n + 1, s, h => by
    rw [List.range'_succ]
    cases he : ent t s with
    | none => exact absurd he (h s (Nat.le_refl _) (by omega))
    | some e =>
      rw [List.filterMap_cons_some he, List.length_cons,
        length_filterMap_ent_all n (s + 1) (fun p h1 h2 => h p (by omega) (by omega))]

/-- A table with fewer stored pairs than slots has a slot without a pair. -/
theorem exists_not_ent {t : Table K V} (h : (tlist t).length < t.size) :
    ∃ j, 1 ≤ j ∧ j ≤ t.size ∧ ent t j = none := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ p, 1 ≤ p → p < 1 + t.size → ent t p ≠ none := by
    intro p h1 h2 he
    exact hne ⟨p, h1, by omega, he⟩
  have := length_filterMap_ent_all t.size 1 hall
  unfold tlist at h
  omega

/-- The probe loop of `rehash!` stops at the first empty slot. -/
theorem rehashProbe_spec (slots : Nat → Nat) (sz hm : Nat) :
    ∀ left a, (∃ d, a ≤ d ∧ d < a + left ∧ slots (pr sz hm d) = 0) →
      ∃ d, a ≤ d ∧ d < a + left ∧ slots (pr sz hm d) = 0 ∧
        (∀ e, a ≤ e → e < d → slots (pr sz hm e) ≠ 0) ∧
        rehashProbe slots sz left (pr sz hm a) = some (pr sz hm d)
  | 0, a, ⟨d, h1, h2, _⟩ => absurd h2 (by omega)
  | left + 1, a, ⟨d, h1, h2, h3⟩ => by
    have e : rehashProbe slots sz (left + 1) (pr sz hm a) =
        if slots (pr sz hm a) != 0 then rehashProbe slots sz left (pr sz hm (a + 1))
        else some (pr sz hm a) := rfl
    by_cases ha : slots (pr sz hm a) = 0
    · refine ⟨a, Nat.le_refl _, by omega, ha, fun e he1 he2 => absurd he2 (by omega), ?_⟩
      rw [e, ha] <;> rfl
    · have hd : a < d := by
        rcases Nat.lt_or_ge a d with h | h
        · exact h
        · have : d = a := by omega
          subst this
          exact absurd h3 ha
      obtain ⟨d', h1', h2', h3', h4', h5'⟩ :=
        rehashProbe_spec slots sz hm left (a + 1) ⟨d, by omega, by omega, h3⟩
      refine ⟨d', by omega, by omega, h3', fun e he1 he2 => ?_, ?_⟩
      · by_cases hea : e = a
        · rw [hea]; exact ha
        · exact h4' e (by omega) he2
      · rw [e, ite_cond_eq_true _ _ (by simp [ha])]
        exact h5'

/-- The table of the copy-loop locals of `rehash!`. -/
def accT (newsz : Nat) (acc : RehashAcc K V) : Table K V :=
  ⟨newsz, acc.slots, acc.keys, acc.vals, 0, acc.count, JInt.lit .u64 0, 1, acc.maxprobe, 1⟩

/-- The copy loop after the old slots `1:n`. -/
def AccOK (o : KeyOps K) (t : Table K V) (newsz n : Nat) (acc : RehashAcc K V) : Prop :=
  Inv o (accT newsz acc) ∧ (∀ j, acc.slots j ≠ 127) ∧
  List.Perm (tlist (accT newsz acc)) ((List.range' 1 n).filterMap (ent t))

abbrev acc0 : RehashAcc K V :=
  { slots := fun _ => 0, keys := fun _ => none, vals := fun _ => none, count := 0, maxprobe := 0 }

theorem accOK_zero {o : KeyOps K} {t : Table K V} {newsz : Nat} (hp : IsPow newsz)
    (hle : newsz ≤ 2 ^ 62) : AccOK o t newsz 0 acc0 := by
  have hnil : tlist (accT newsz (acc0 : RehashAcc K V)) = [] :=
    filterMap_ent_nil (t := accT newsz acc0) newsz 1 (fun _ _ _ => isFilledB_zero)
  refine ⟨⟨Or.inr hp, hle, fun i _ _ => Or.inl rfl, ?_, ?_, Or.inr ?_, Nat.le_refl _, ?_,
    Nat.le_refl _⟩, fun _ => by show (0 : Nat) ≠ 127; decide, ?_⟩
  · intro i j a b _ _ _ _ _ ha
    have : ent (accT newsz (acc0 : RehashAcc K V)) i = none := ent_of_not_filled isFilledB_zero
    rw [this] at ha
    cases ha
  · rw [hnil] <;> rfl
  · have := hp.ge
    show 0 < newsz
    omega
  · intro i _ _ hf
    exact absurd hf (by show ¬ (isFilledB 0 = true); decide)
  · rw [hnil]
    exact List.Perm.nil

/-- The prefix lists of a table. -/
theorem prefix_succ (t : Table K V) (n : Nat) :
    (List.range' 1 (n + 1)).filterMap (ent t) =
      (List.range' 1 n).filterMap (ent t) ++ (ent t (n + 1)).toList := by
  rw [List.range'_concat, List.filterMap_append]
  congr 1
  rw [show 1 + 1 * n = n + 1 by omega]
  cases h : ent t (n + 1)
  · rw [List.filterMap_cons_none h] <;> rfl
  · rw [List.filterMap_cons_some h] <;> rfl

theorem prefix_length_le (t : Table K V) {n : Nat} (hn : n ≤ t.size) :
    ((List.range' 1 n).filterMap (ent t)).length ≤ (tlist t).length := by
  unfold tlist
  have h := List.range'_append_1 (s := 1) (m := n) (n := t.size - n)
  rw [show n + (t.size - n) = t.size by omega] at h
  rw [← h, List.filterMap_append, List.length_append]
  omega

theorem prefix_mem {t : Table K V} {n : Nat} {e : K × V}
    (h : e ∈ (List.range' 1 n).filterMap (ent t)) : ∃ p, 1 ≤ p ∧ p ≤ n ∧ ent t p = some e := by
  rw [List.mem_filterMap] at h
  obtain ⟨p, hp, he⟩ := h
  rw [List.mem_range'_1] at hp
  exact ⟨p, hp.1, by omega, he⟩

/-- The copy-loop locals after storing `(k, v)` with byte `b` at `index`, probe length `d`. -/
def accStore (acc : RehashAcc K V) (index b : Nat) (k : K) (v : V) (d : Nat) : RehashAcc K V :=
  ⟨upd acc.slots index b, upd acc.keys index (some k), upd acc.vals index (some v), acc.count + 1,
   if d > acc.maxprobe then d else acc.maxprobe⟩

/-- The result of `rehash!` on a table without pairs. -/
def rehashEmpty (t : Table K V) (newsz : Nat) : Table K V :=
  ⟨newsz, fun _ => 0, fun _ => none, fun _ => none, 0, t.count, bump t.age, 1, 0, 1⟩

/-- The result of `rehash!` after the copy loop. -/
def rehashFull (t : Table K V) (newsz : Nat) (acc : RehashAcc K V) : Table K V :=
  ⟨newsz, acc.slots, acc.keys, acc.vals, 0, acc.count, bump (bump t.age), 1, acc.maxprobe, 1⟩

theorem rehashStep_skip {o : KeyOps K} {newsz : Nat} {olds : Nat → Nat} {oldk : Nat → Option K}
    {oldv : Nat → Option V} {acc : RehashAcc K V} {i : Nat} (hf : isFilledB (olds i) = false) :
    rehashStep o newsz olds oldk oldv acc i = .ok acc := by
  unfold rehashStep
  rw [hf] <;> rfl

theorem rehashStep_store {o : KeyOps K} {newsz : Nat} {olds : Nat → Nat} {oldk : Nat → Option K}
    {oldv : Nat → Option V} {acc : RehashAcc K V} {i : Nat} {k : K} {v : V} {index : Nat}
    (hf : isFilledB (olds i) = true) (hk : oldk i = some k) (hv : oldv i = some v)
    (hp : rehashProbe acc.slots newsz newsz (home o newsz k) = some index) :
    rehashStep o newsz olds oldk oldv acc i =
      .ok (accStore acc index (olds i) k v (probeDist newsz index (home o newsz k))) := by
  unfold rehashStep
  rw [ite_eq_left hf, hk, hv]
  show (match rehashProbe acc.slots newsz newsz (home o newsz k) with
    | none => (throw DErr.diverges : DR (RehashAcc K V))
    | some index => pure (accStore acc index (olds i) k v (probeDist newsz index (home o newsz k))))
      = _
  rw [hp] <;> rfl

/-- One step of the copy loop. -/
theorem rehashStep_ok {o : KeyOps K} {t : Table K V} (hi : Inv o t) {newsz : Nat} (hp : IsPow newsz)
    (hle : newsz ≤ 2 ^ 62) (hgt : t.count < newsz) {n : Nat} (hn : n < t.size)
    {acc : RehashAcc K V} (ha : AccOK o t newsz n acc) :
    ∃ acc', rehashStep o newsz t.slots t.keys t.vals acc (n + 1) = .ok acc' ∧
      AccOK o t newsz (n + 1) acc' := by
  obtain ⟨hai, ha127, hap⟩ := ha
  cases hf : isFilledB (t.slots (n + 1)) with
  | false =>
    refine ⟨acc, rehashStep_skip hf, hai, ha127, ?_⟩
    rw [prefix_succ, ent_of_not_filled hf]
    simpa using hap
  | true =>
    obtain ⟨k, v, hk, hv, hent, hs, -⟩ := hi.filled (by omega) (by omega) hf
    -- the accumulator has fewer pairs than slots
    have hlen : (tlist (accT newsz acc)).length + 1 ≤ t.count := by
      rw [hap.length_eq, hi.count]
      have h1 := prefix_length_le t (n := n + 1) (by omega)
      rw [prefix_succ, hent, List.length_append] at h1
      simpa using h1
    obtain ⟨j, hj1, hj2, hjn⟩ := exists_not_ent (t := accT newsz acc) (by show _ < newsz; omega)
    have hj0 : acc.slots j = 0 := by
      rcases hai.slot j hj1 hj2 with h | h | ⟨k', v', hk', hv', hs', -⟩
      · exact h
      · exact absurd h (ha127 j)
      · have hf' : isFilledB ((accT newsz acc).slots j) = true := by
          rw [hs']; exact shorthash7_filled _
        rw [ent_of_filled hf' hk' hv'] at hjn
        cases hjn
    have hhr := home_range hp k (o := o)
    obtain ⟨d0, hd0, hd0e⟩ := pr_surj hp hhr.1 hhr.2 hj1 hj2
    obtain ⟨d, -, hd, hdz, hdbefore, hprobe⟩ := rehashProbe_spec acc.slots newsz (home o newsz k)
      newsz 0 ⟨d0, Nat.zero_le _, by omega, by rw [hd0e]; exact hj0⟩
    have hprobe' : rehashProbe acc.slots newsz newsz (home o newsz k) =
        some (pr newsz (home o newsz k) d) := hprobe
    have hdist := probeDist_pr hp (by omega) hhr.1 hhr.2 (show d < newsz by omega)
    refine ⟨_, rehashStep_store hf hk hv hprobe', ?_⟩
    rw [hdist]
    have hir := pr_range hp hhr.1 hhr.2 (show d < newsz by omega)
    have hent' := ent_store_eq (t := accT newsz acc)
      (t' := accT newsz (accStore acc (pr newsz (home o newsz k) d) (t.slots (n + 1)) k v d))
      hf rfl rfl rfl
    -- keys already copied come from earlier old slots
    have hold : ∀ i b, 1 ≤ i → i ≤ newsz → ent (accT newsz acc) i = some b →
        o.eq k b.1 = false ∧ o.eq b.1 k = false := by
      intro i b h1 h2 hb
      obtain ⟨p, hp1, hp2, hpe⟩ := prefix_mem (hap.mem_iff.1 (mem_tlist.2 ⟨i, h1, h2, hb⟩))
      exact ⟨hi.distinct (n + 1) p (k, v) b (by omega) (by omega) hp1 (by omega) (by omega) hent hpe,
        hi.distinct p (n + 1) b (k, v) hp1 (by omega) (by omega) (by omega) (by omega) hpe hent⟩
    have hmpacc : acc.maxprobe < newsz := by
      rcases hai.maxprobe with h | h
      · exact absurd h (by have := hp.ge; show newsz ≠ 0; omega)
      · exact h
    have hnf : ent (accT newsz acc) (pr newsz (home o newsz k) d) = none :=
      ent_of_not_filled (by
        show isFilledB (acc.slots (pr newsz (home o newsz k) d)) = false
        rw [hdz]; exact isFilledB_zero)
    have hstore := tlist_store (o := o) (t := accT newsz acc)
      (t' := accT newsz (accStore acc (pr newsz (home o newsz k) d) (t.slots (n + 1)) k v d))
      (j := pr newsz (home o newsz k) d) (e := (k, v)) rfl hir.1 hir.2 (fun i _ _ => hent' i)
      (fun i b h1 h2 _ hb => (hold i b h1 h2 hb).1)
      (fun b hb => by rw [hnf] at hb; cases hb)
    have hfilt : (tlist (accT newsz acc)).filter (fun b => !o.eq (k, v).1 b.1) =
        tlist (accT newsz acc) := by
      rw [List.filter_eq_self]
      intro b hb
      obtain ⟨i, h1, h2, hbi⟩ := mem_tlist.1 hb
      simp [(hold i b h1 h2 hbi).1]
    rw [hfilt] at hstore
    refine ⟨⟨Or.inr hp, hle, ?_, ?_, ?_, Or.inr ?_, Nat.le_refl _, fun _ h _ _ => h, Nat.le_refl _⟩,
      ?_, ?_⟩
    · -- slots
      intro i h1 h2
      by_cases hi' : i = pr newsz (home o newsz k) d
      · subst hi'
        refine Or.inr (Or.inr ⟨k, v, upd_same _ _ _, upd_same _ _ _, (upd_same _ _ _).trans hs,
          d, ?_, rfl, ?_⟩)
        · show d ≤ (if d > acc.maxprobe then d else acc.maxprobe)
          split <;> omega
        · intro e he
          have hne : pr newsz (home o newsz k) e ≠ pr newsz (home o newsz k) d := by
            intro heq
            have := pr_inj hp hhr.1 hhr.2 (show e < newsz by omega) (show d < newsz by omega) heq
            omega
          show upd acc.slots (pr newsz (home o newsz k) d) (t.slots (n + 1))
            (pr newsz (home o newsz k) e) ≠ 0
          rw [upd_ne _ _ hne]
          exact hdbefore e (Nat.zero_le _) he
      · rcases hai.slot i h1 h2 with h | h | ⟨k', v', hk', hv', hs', hc'⟩
        · exact Or.inl ((upd_ne _ _ hi').trans h)
        · exact Or.inr (Or.inl ((upd_ne _ _ hi').trans h))
        · refine Or.inr (Or.inr ⟨k', v', (upd_ne _ _ hi').trans hk', (upd_ne _ _ hi').trans hv',
            (upd_ne _ _ hi').trans hs', ?_⟩)
          refine Chain.mono (t := accT newsz acc) hp hmpacc rfl ?_ ?_ hc'
          · show acc.maxprobe ≤ (if d > acc.maxprobe then d else acc.maxprobe)
            split <;> omega
          · intro p _ _ hne
            show upd acc.slots (pr newsz (home o newsz k) d) (t.slots (n + 1)) p ≠ 0
            by_cases hp' : p = pr newsz (home o newsz k) d
            · rw [hp', upd_same, hs]; exact shorthash7_ne0 _
            · rw [upd_ne _ _ hp']; exact hne
    · -- distinct
      intro i i' a b h1 h2 h1' h2' hne ha hb
      rw [hent'] at ha hb
      by_cases hi1 : i = pr newsz (home o newsz k) d
      · rw [ite_eq_left hi1] at ha
        cases ha
        have hi2 : i' ≠ pr newsz (home o newsz k) d := fun h => hne (hi1.trans h.symm)
        rw [ite_eq_right hi2] at hb
        exact (hold i' b h1' h2' hb).1
      · rw [ite_eq_right hi1] at ha
        by_cases hi2 : i' = pr newsz (home o newsz k) d
        · rw [ite_eq_left hi2] at hb
          cases hb
          exact (hold i a h1 h2 ha).2
        · rw [ite_eq_right hi2] at hb
          exact hai.distinct i i' a b h1 h2 h1' h2' hne ha hb
    · -- count
      show acc.count + 1 = _
      rw [hstore.length_eq, List.length_cons,
        ← show acc.count = (tlist (accT newsz acc)).length from hai.count]
    · -- maxprobe
      show (if d > acc.maxprobe then d else acc.maxprobe) < newsz
      split <;> omega
    · -- no deleted bytes
      intro p
      show upd acc.slots (pr newsz (home o newsz k) d) (t.slots (n + 1)) p ≠ 127
      by_cases hp' : p = pr newsz (home o newsz k) d
      · rw [hp', upd_same, hs]; exact shorthash7_ne127 _
      · rw [upd_ne _ _ hp']; exact ha127 p
    · -- contents
      rw [prefix_succ, hent]
      exact hstore.trans ((List.Perm.cons _ hap).trans (List.perm_append_singleton _ _).symm)

/-- The whole copy loop. -/
theorem rehash_fold {o : KeyOps K} {t : Table K V} (hi : Inv o t) {newsz : Nat} (hp : IsPow newsz)
    (hle : newsz ≤ 2 ^ 62) (hgt : t.count < newsz) :
    ∀ n, n ≤ t.size → ∃ acc,
      (List.range n).foldlM (fun acc i => rehashStep o newsz t.slots t.keys t.vals acc (i + 1))
        (acc0 : RehashAcc K V) = .ok acc ∧ AccOK o t newsz n acc
  | 0, _ => ⟨acc0, rfl, accOK_zero hp hle⟩
  | n + 1, hn => by
    obtain ⟨acc, h1, h2⟩ := rehash_fold hi hp hle hgt n (by omega)
    obtain ⟨acc', h3, h4⟩ := rehashStep_ok hi hp hle hgt (by omega) h2
    refine ⟨acc', ?_, h4⟩
    rw [List.range_succ, List.foldlM_append, h1]
    simp only [except_ok_bind, List.foldlM_cons, List.foldlM_nil]
    rw [h3] <;> rfl

/-- `rehash!(h, newsz0)` keeps the pairs when the new size exceeds the count. -/
theorem rehash_spec {o : KeyOps K} {t : Table K V} (hi : Inv o t) (newsz0 : Nat)
    (hgt : t.count < tableszNat newsz0) (hle : tableszNat newsz0 ≤ 2 ^ 62) :
    ∃ t', rehash o t newsz0 = .ok t' ∧ Inv o t' ∧ List.Perm (tlist t') (tlist t) ∧
      t'.size = tableszNat newsz0 ∧ t'.count = t.count ∧
      t'.age = (if t.count = 0 then bump t.age else bump (bump t.age)) := by
  have hp := tableszNat_pow newsz0
  by_cases hc : t.count = 0
  · have hnil : tlist (rehashEmpty t (tableszNat newsz0)) = [] :=
      filterMap_ent_nil (tableszNat newsz0) 1 (fun _ _ _ => isFilledB_zero)
    refine ⟨rehashEmpty t (tableszNat newsz0), ?_, ?_, ?_, rfl, rfl, by simp [hc, rehashEmpty]⟩
    · unfold rehash
      have h0 : (t.count == 0) = true := by simp [hc]
      simp only [h0, eq_self_iff_true, ite_true]
      rfl
    · have h := accOK_zero (o := o) (t := t) hp hle
      exact ⟨h.1.size, h.1.sizeLe, h.1.slot, h.1.distinct, by rw [hnil]; exact hc,
        h.1.maxprobe, h.1.idxfloor, h.1.floorLe, h.1.popcursor⟩
    · have ht : tlist t = [] := by
        rw [hi.count] at hc
        exact List.length_eq_zero_iff.1 hc
      rw [hnil, ht]
  · obtain ⟨acc, hfold, hacc, -, hperm⟩ := rehash_fold hi hp hle hgt t.size (Nat.le_refl _)
    have htl : (List.range' 1 t.size).filterMap (ent t) = tlist t := rfl
    rw [htl] at hperm
    refine ⟨rehashFull t (tableszNat newsz0) acc, ?_,
      ⟨hacc.size, hacc.sizeLe, hacc.slot, hacc.distinct, hacc.count, hacc.maxprobe, hacc.idxfloor,
        hacc.floorLe, hacc.popcursor⟩, hperm, rfl, ?_, by simp [hc, rehashFull]⟩
    · unfold rehash
      have h0 : (t.count == 0) = false := by simp [hc]
      simp only [h0, Bool.false_eq_true, ite_false]
      rw [bind_of_ok hfold]
      rfl
    · show acc.count = t.count
      rw [show acc.count = (tlist (accT (tableszNat newsz0) acc)).length from hacc.count,
        hperm.length_eq, hi.count]

end JuliaLean.Dicts
