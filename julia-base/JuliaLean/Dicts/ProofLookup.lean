import JuliaLean.Dicts.InvTable
import JuliaLean.Dicts.InvRef

/-!
# Lookup and iteration on invariant tables

`ht_keyindex` finds exactly the slot of an `isequal` key, and iteration from
`idxfloor` lists the stored pairs in slot order. Together they give `Agrees`
for every table that represents a reference map.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- The key test of the probe loops at slot `j`. -/
def keyMatch (t : Table K V) (m : K → Bool) (j : Nat) : Bool :=
  match t.keys j with
  | some k => m k
  | none => false

theorem keyMatch_some {t : Table K V} {m : K → Bool} {j : Nat} {k : K} (hk : t.keys j = some k) :
    keyMatch t m j = m k := by
  unfold keyMatch
  rw [hk]

theorem keyMatch_true {t : Table K V} {m : K → Bool} {j : Nat} (h : keyMatch t m j = true) :
    ∃ k, t.keys j = some k ∧ m k = true := by
  cases hk : t.keys j with
  | none => unfold keyMatch at h; rw [hk] at h; cases h
  | some k => exact ⟨k, rfl, by rw [keyMatch_some hk] at h; exact h⟩

/-- The tag and key test of the probe loops at slot `j`. -/
def hitAt (t : Table K V) (sh : Nat) (m : K → Bool) (j : Nat) : Bool :=
  sh == t.slots j && keyMatch t m j

theorem hitAt_true {t : Table K V} {sh : Nat} {m : K → Bool} {j : Nat} (h : hitAt t sh m j = true) :
    t.slots j = sh ∧ ∃ k, t.keys j = some k ∧ m k = true := by
  unfold hitAt at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.symm, keyMatch_true h.2⟩

theorem hitAt_of {t : Table K V} {sh : Nat} {m : K → Bool} {j : Nat} {k : K} (hs : t.slots j = sh)
    (hk : t.keys j = some k) (hm : m k = true) : hitAt t sh m j = true := by
  unfold hitAt
  rw [keyMatch_some hk, hs, hm]
  simp

theorem isEmptyB_iff (b : Nat) : isEmptyB b = true ↔ b = 0 := by
  unfold isEmptyB
  simp

theorem keyindexLoop_succ (t : Table K V) (sh : Nat) (m : K → Bool) (left index : Nat) :
    keyindexLoop t sh m (left + 1) index =
      if isEmptyB (t.slots index) then -1
      else if hitAt t sh m index then (index : Int)
      else keyindexLoop t sh m left (nextIdx t.size index) := rfl

/-- The loop returns `-1` or a hit on a slot satisfying any predicate stable under the step. -/
theorem keyindexLoop_cases (t : Table K V) (sh : Nat) (m : K → Bool) (P : Nat → Prop)
    (hP : ∀ j, P j → P (nextIdx t.size j)) :
    ∀ left index, P index →
      keyindexLoop t sh m left index = -1 ∨
      ∃ j, P j ∧ hitAt t sh m j = true ∧ keyindexLoop t sh m left index = (j : Int)
  | 0, _, _ => Or.inl rfl
  | left + 1, index, hp => by
    rw [keyindexLoop_succ]
    split
    · exact Or.inl rfl
    · split
      · next hh => exact Or.inr ⟨index, hp, hh, rfl⟩
      · exact keyindexLoop_cases t sh m P hP left _ (hP _ hp)

/-- The loop stops at the first hit on a probe sequence over non-empty slots. -/
theorem keyindexLoop_found (t : Table K V) (sh : Nat) (m : K → Bool) (h d : Nat) :
    ∀ left a, a ≤ d → d < a + left →
      (∀ e, a ≤ e → e < d → t.slots (pr t.size h e) ≠ 0 ∧ hitAt t sh m (pr t.size h e) = false) →
      hitAt t sh m (pr t.size h d) = true → t.slots (pr t.size h d) ≠ 0 →
      keyindexLoop t sh m left (pr t.size h a) = (pr t.size h d : Int)
  | 0, _, h1, h2, _, _, _ => absurd h2 (by omega)
  | left + 1, a, h1, h2, hbefore, hhit, hne => by
    rw [keyindexLoop_succ]
    by_cases had : a = d
    · subst had
      rw [ite_eq_right (fun he => hne ((isEmptyB_iff _).1 he)), ite_eq_left hhit]
    · have hb := hbefore a (Nat.le_refl _) (by omega)
      rw [ite_eq_right (fun he => hb.1 ((isEmptyB_iff _).1 he)),
        ite_eq_right (fun hh => by rw [hb.2] at hh; cases hh)]
      exact keyindexLoop_found t sh m h d left (a + 1) (by omega) (by omega)
        (fun e he1 he2 => hbefore e (by omega) he2) hhit hne

/-- A non-empty invariant table has a power-of-two size and `maxprobe < size`. -/
theorem Inv.pow_of_count {o : KeyOps K} {t : Table K V} (hi : Inv o t) (hc : t.count ≠ 0) :
    IsPow t.size ∧ t.maxprobe < t.size := by
  have hs : t.size ≠ 0 := by
    intro h0
    apply hc
    rw [hi.count]
    unfold tlist
    rw [h0]
    rfl
  rcases hi.size with h | h
  · exact absurd h hs
  · rcases hi.maxprobe with h' | h'
    · exact absurd h' hs
    · exact ⟨h, h'⟩

theorem Inv.count_pos {o : KeyOps K} {t : Table K V} (hi : Inv o t) {i : Nat} {e : K × V}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some e) : t.count ≠ 0 := by
  rw [hi.count]
  have : e ∈ tlist t := mem_tlist.2 ⟨i, h1, h2, he⟩
  intro h0
  rw [List.length_eq_zero_iff] at h0
  rw [h0] at this
  cases this

/-- `ht_keyindex` on an invariant table from its definition, when non-empty. -/
theorem htKeyindex_unfold {o : KeyOps K} {t : Table K V} (hi : Inv o t) (hc : t.count ≠ 0)
    (hq : JInt .u64) (m : K → Bool) :
    htKeyindex t hq m =
      .ok (keyindexLoop t (shorthash7 hq) m (t.maxprobe + 1) (hashindex hq t.size).1) := by
  have hp := hi.pow_of_count hc
  have h0 : (t.count == 0) = false := by simp [hc]
  have e : htKeyindex t hq m = if ¬ t.maxprobe < t.size then throw .thrownDict else
      pure (keyindexLoop t (shorthash7 hq) m (t.maxprobe + 1) (hashindex hq t.size).1) := by
    unfold htKeyindex
    rw [h0] <;> rfl
  rw [e, ite_eq_right (fun h => h hp.2)] <;> rfl

theorem htKeyindex_found {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {q : K}
    {i : Nat} {k : K} {v : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some (k, v))
    (hq : o.eq q k = true) : htKeyindex t (o.hash q) (o.eq q) = .ok (i : Int) := by
  have hc := hi.count_pos h1 h2 he
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  have hfill := (ent_some he).1
  obtain ⟨k', v', hk, hv, -, hs, hch⟩ := hi.filled h1 h2 hfill
  have hkk : k' = k := by rw [(ent_some he).2.1] at hk; cases hk; rfl
  subst hkk
  obtain ⟨d, hd, hid, hall⟩ := hch
  have hh : home o t.size k' = (hashindex (o.hash q) t.size).1 := by
    unfold home; rw [hl.hash_eq q k' hq]
  have hhr := home_range hp.1 k' (o := o)
  rw [← hh]
  have hsh : shorthash7 (o.hash q) = shorthash7 (o.hash k') := by rw [hl.hash_eq q k' hq]
  congr 1
  rw [hid]
  apply keyindexLoop_found t (shorthash7 (o.hash q)) (o.eq q) (home o t.size k') d
    (t.maxprobe + 1) 0 (Nat.zero_le _) (by omega)
  · intro e _ hed
    refine ⟨hall e hed, ?_⟩
    cases hhit : hitAt t (shorthash7 (o.hash q)) (o.eq q) (pr t.size (home o t.size k') e)
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
      rw [eq_trans' hl hm2 hq] at hdis
      cases hdis
  · exact hitAt_of (by rw [← hid, hs, hsh]) (by rw [← hid]; exact hk) hq
  · rw [← hid, hs]; exact shorthash7_ne0 _

theorem htKeyindex_absent {o : KeyOps K} {t : Table K V} (hi : Inv o t) {q : K}
    (habs : ∀ e ∈ tlist t, o.eq q e.1 = false) : htKeyindex t (o.hash q) (o.eq q) = .ok (-1) := by
  by_cases hc : t.count = 0
  · unfold htKeyindex
    rw [hc] <;> rfl
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  congr 1
  have hr := hashindex_range hp.1 (o.hash q)
  rcases keyindexLoop_cases t (shorthash7 (o.hash q)) (o.eq q) (fun j => 1 ≤ j ∧ j ≤ t.size)
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

theorem valAt_of_ent {t : Table K V} {i : Nat} {k : K} {v : V} (he : ent t i = some (k, v)) :
    valAt t i = .ok v := by
  unfold valAt
  rw [(ent_some he).2.2] <;> rfl

theorem entryAt_of_ent {t : Table K V} {i : Nat} {e : K × V} (he : ent t i = some e) :
    entryAt t i = .ok e := by
  unfold entryAt
  rw [(ent_some he).2.1, (ent_some he).2.2] <;> rfl

theorem lookup_found {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {q : K}
    {i : Nat} {k : K} {v : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some (k, v))
    (hq : o.eq q k = true) : dictGet o t q = .ok (some v) := by
  unfold dictGet lookup
  rw [htKeyindex_found hl hi h1 h2 he hq]
  show (if (i : Int) < 0 then pure none else some <$> valAt t (i : Int).toNat) = _
  rw [ite_eq_right (by omega), Int.toNat_natCast, valAt_of_ent he] <;> rfl

theorem lookup_absent {o : KeyOps K} {t : Table K V} (hi : Inv o t) {q : K}
    (habs : ∀ e ∈ tlist t, o.eq q e.1 = false) : dictGet o t q = .ok none := by
  unfold dictGet lookup
  rw [htKeyindex_absent hi habs] <;> rfl

/-- Lookups in a table that represents `m`. -/
theorem Rep.dictGet {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    (q : K) : dictGet o t q = .ok (rlookup o m q) := by
  have hd : Distinct o (tlist t) := tlist_pairwise h.1
  unfold rlookup
  rw [← rfind_perm hl hd h.2]
  by_cases hex : ∃ e ∈ tlist t, o.eq q e.1 = true
  · obtain ⟨e, hem, heq⟩ := hex
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    rw [rfind_of_mem hl hd hem heq]
    exact lookup_found hl h.1 h1 h2 hei heq
  · have habs : ∀ e ∈ tlist t, o.eq q e.1 = false := by
      intro e he
      cases hq : o.eq q e.1
      · rfl
      · exact absurd ⟨e, he, hq⟩ hex
    rw [rfind_none habs]
    exact lookup_absent h.1 habs

theorem Rep.haskey_eq {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    (q : K) : haskey o t q = .ok (rfind o m q).isSome := by
  have hd : Distinct o (tlist t) := tlist_pairwise h.1
  unfold haskey
  rw [← rfind_perm hl hd h.2]
  by_cases hex : ∃ e ∈ tlist t, o.eq q e.1 = true
  · obtain ⟨e, hem, heq⟩ := hex
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    rw [rfind_of_mem hl hd hem heq, htKeyindex_found hl h.1 h1 h2 hei heq]
    show Except.ok (decide ((i : Int) ≥ 0)) = Except.ok true
    simp
  · have habs : ∀ e ∈ tlist t, o.eq q e.1 = false := by
      intro e he
      cases hq : o.eq q e.1
      · rfl
      · exact absurd ⟨e, he, hq⟩ hex
    rw [rfind_none habs, htKeyindex_absent h.1 habs]
    rfl

/-! ## Iteration -/

theorem skipDeletedLoop_spec (t : Table K V) :
    ∀ left i, 1 ≤ i →
      (skipDeletedLoop t left i = 0 ∧ ∀ p, i ≤ p → p < i + left → isFilledB (t.slots p) = false) ∨
      (i ≤ skipDeletedLoop t left i ∧ skipDeletedLoop t left i < i + left ∧
        isFilledB (t.slots (skipDeletedLoop t left i)) = true ∧
        ∀ p, i ≤ p → p < skipDeletedLoop t left i → isFilledB (t.slots p) = false)
  | 0, i, _ => Or.inl ⟨rfl, fun p h1 h2 => absurd h2 (by omega)⟩
  | left + 1, i, hi => by
    cases hf : isFilledB (t.slots i)
    · have e : skipDeletedLoop t (left + 1) i = skipDeletedLoop t left (i + 1) := by
        show (if isFilledB (t.slots i) then i else skipDeletedLoop t left (i + 1)) = _
        rw [hf] <;> rfl
      rw [e]
      rcases skipDeletedLoop_spec t left (i + 1) (by omega) with ⟨h0, hall⟩ | ⟨ha, hb, hc, hd⟩
      · refine Or.inl ⟨h0, fun p h1 h2 => ?_⟩
        by_cases hp : p = i
        · rw [hp]; exact hf
        · exact hall p (by omega) (by omega)
      · refine Or.inr ⟨by omega, by omega, hc, fun p h1 h2 => ?_⟩
        by_cases hp : p = i
        · rw [hp]; exact hf
        · exact hd p (by omega) h2
    · have e : skipDeletedLoop t (left + 1) i = i := by
        show (if isFilledB (t.slots i) then i else skipDeletedLoop t left (i + 1)) = _
        rw [hf] <;> rfl
      rw [e]
      exact Or.inr ⟨Nat.le_refl _, by omega, hf, fun p h1 h2 => absurd h2 (by omega)⟩

theorem filterMap_ent_nil {t : Table K V} :
    ∀ n s, (∀ p, s ≤ p → p < s + n → isFilledB (t.slots p) = false) →
      (List.range' s n).filterMap (ent t) = []
  | 0, _, _ => rfl
  | n + 1, s, h => by
    rw [List.range'_succ, List.filterMap_cons_none (ent_of_not_filled (h s (Nat.le_refl _) (by omega)))]
    exact filterMap_ent_nil n (s + 1) (fun p h1 h2 => h p (by omega) (by omega))

/-- Iteration from state `i` lists the stored pairs of `i:size`. -/
theorem iterFrom_eq {o : KeyOps K} {t : Table K V} (hi : Inv o t) :
    ∀ fuel i, 1 ≤ i → t.size + 1 - i ≤ fuel →
      iterFrom t fuel i = .ok ((List.range' i (t.size + 1 - i)).filterMap (ent t))
  | 0, i, _, hf => by
    rw [show t.size + 1 - i = 0 by omega] <;> rfl
  | fuel + 1, i, h1, hf => by
    have hspec := skipDeletedLoop_spec t (t.size + 1 - i) i h1
    have e : iterFrom t (fuel + 1) i =
        if (skipDeletedLoop t (t.size + 1 - i) i == 0) = true then pure [] else
          entryAt t (skipDeletedLoop t (t.size + 1 - i) i) >>= fun e =>
            iterFrom t fuel (skipDeletedLoop t (t.size + 1 - i) i + 1) >>= fun rest =>
              pure (e :: rest) := rfl
    rw [e]
    generalize skipDeletedLoop t (t.size + 1 - i) i = j at hspec ⊢
    rcases hspec with ⟨h0, hall⟩ | ⟨ha, hb, hc, hd⟩
    · subst h0
      rw [filterMap_ent_nil _ _ hall] <;> rfl
    · have hj0 : (j == 0) = false := by
        rw [beq_eq_false_iff_ne]; omega
      obtain ⟨k, v, -, -, hent, -, -⟩ := hi.filled (by omega) (by omega) hc
      rw [hj0, ite_eq_right (by decide), entryAt_of_ent hent,
        iterFrom_eq hi fuel (j + 1) (by omega) (by omega)]
      show Except.ok ((k, v) :: _) = _
      congr 1
      have hsplit : List.range' i (t.size + 1 - i) =
          List.range' i (j - i) ++ (j :: List.range' (j + 1) (t.size + 1 - (j + 1))) := by
        have h2 := List.range'_append_1 (s := i) (m := j - i) (n := t.size + 1 - j)
        rw [show i + (j - i) = j by omega,
          show j - i + (t.size + 1 - j) = t.size + 1 - i by omega] at h2
        rw [← h2, show t.size + 1 - j = (t.size + 1 - (j + 1)) + 1 by omega, List.range'_succ]
      rw [hsplit, List.filterMap_append, filterMap_ent_nil _ _ (fun p h1 h2 => hd p h1 (by omega)),
        List.filterMap_cons_some hent] <;> rfl

theorem iterList_eq {o : KeyOps K} {t : Table K V} (hi : Inv o t) : iterList t = .ok (tlist t) := by
  unfold iterList
  rw [iterFrom_eq hi (t.size + 1) t.idxfloor hi.idxfloor (by omega)]
  congr 1
  unfold tlist
  have hf1 := hi.idxfloor
  have hnone : ∀ p, 1 ≤ p → p < t.idxfloor → p ≤ t.size → isFilledB (t.slots p) = false := by
    intro p h1 h2 h3
    cases hfp : isFilledB (t.slots p)
    · rfl
    · have := hi.floorLe p h1 h3 hfp
      omega
  by_cases hf : t.idxfloor ≤ t.size + 1
  · have h1 := List.range'_append_1 (s := 1) (m := t.idxfloor - 1) (n := t.size + 1 - t.idxfloor)
    rw [show 1 + (t.idxfloor - 1) = t.idxfloor by omega,
      show t.idxfloor - 1 + (t.size + 1 - t.idxfloor) = t.size by omega] at h1
    rw [← h1, List.filterMap_append,
      filterMap_ent_nil (t := t) (t.idxfloor - 1) 1 (fun p h2 h3 => hnone p h2 (by omega) (by omega))]
      <;> rfl
  · rw [show t.size + 1 - t.idxfloor = 0 by omega,
      filterMap_ent_nil (t := t) t.size 1 (fun p h2 h3 => hnone p h2 (by omega) (by omega))] <;> rfl

/-- A table representing `m` agrees with it. -/
theorem Rep.agrees {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m) :
    Agrees o t m :=
  ⟨(tlist_pairwise h.1).perm h.2 (fun h => eq_false_symm hl h),
   fun q => h.dictGet hl q,
   ⟨tlist t, iterList_eq h.1, fun _ => h.2.mem_iff, h.2.length_eq⟩,
   by unfold dictLength; rw [h.1.count, h.2.length_eq]⟩

end JuliaLean.Dicts
