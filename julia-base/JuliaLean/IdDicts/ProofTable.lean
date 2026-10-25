import JuliaLean.IdDicts.Props

/-!
# Lemmas on the eqtable primitive and the reference map
-/

namespace JuliaLean.IdDicts

@[simp] theorem egal_eq (a b : JVal) : egal a b = decide (a = b) := rfl

theorem eqtableGet_eq (t : Tab) (k d : JVal) : eqtableGet t k d = (rLookup t k).getD d := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k = k' <;> simp [eqtableGet, rLookup, h, ih]

theorem rLookup_none_iff (t : Tab) (k : JVal) : rLookup t k = none ↔ k ∉ t.map Prod.fst := by
  induction t with
  | nil => simp [rLookup]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k = k' <;> simp [rLookup, h, ih]

theorem rLookup_mem {t : Tab} {k v : JVal} (h : rLookup t k = some v) : (k, v) ∈ t := by
  induction t with
  | nil => simp [rLookup] at h
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k = k'
    · subst hk; simp [rLookup] at h; subst h; simp
    · simp [rLookup, hk] at h; exact List.mem_cons_of_mem _ (ih h)

theorem put_lookup (t : Tab) (k v q : JVal) :
    rLookup (eqtablePut t k v).1 q = if q = k then some v else rLookup t q := by
  induction t with
  | nil => by_cases h : q = k <;> simp [eqtablePut, rLookup, h]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k = k'
    · subst hk; by_cases hq : q = k <;> simp [eqtablePut, rLookup, hq]
    · have hk' : ¬ k' = k := fun e => hk e.symm
      by_cases hq : q = k
      · subst hq; simp [eqtablePut, rLookup, hk, ih]
      · by_cases hq' : q = k'
        · subst hq'; simp [eqtablePut, rLookup, hk, hk']
        · simp [eqtablePut, rLookup, hk, hq, hq', ih]

theorem put_ins (t : Tab) (k v : JVal) :
    (eqtablePut t k v).2 = if (rLookup t k).isSome then 0 else 1 := by
  induction t with
  | nil => simp [eqtablePut, rLookup]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k = k'
    · subst hk; simp [eqtablePut, rLookup]
    · simp [eqtablePut, rLookup, hk, ih]

theorem put_length (t : Tab) (k v : JVal) :
    (eqtablePut t k v).1.length = t.length + (eqtablePut t k v).2 := by
  induction t with
  | nil => simp [eqtablePut]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k = k'
    · subst hk; simp [eqtablePut]
    · simp [eqtablePut, hk, ih]; omega

theorem put_mem {t : Tab} {k v : JVal} {p : JVal × JVal} (h : p ∈ (eqtablePut t k v).1) :
    p ∈ t ∨ p = (k, v) := by
  induction t with
  | nil => simp [eqtablePut] at h; exact Or.inr h
  | cons q t ih =>
    obtain ⟨k', v'⟩ := q
    by_cases hk : k = k'
    · subst hk
      simp [eqtablePut] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · simp [eqtablePut, hk] at h
      rcases h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · rcases ih h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

theorem put_keys (t : Tab) (k v : JVal) :
    (eqtablePut t k v).1.map Prod.fst =
      if (rLookup t k).isSome then t.map Prod.fst else t.map Prod.fst ++ [k] := by
  induction t with
  | nil => simp [eqtablePut, rLookup]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k = k'
    · subst hk; simp [eqtablePut, rLookup]
    · by_cases hm : (rLookup t k).isSome
      · simp [eqtablePut, rLookup, hk, ih, hm]
      · simp [eqtablePut, rLookup, hk, ih, hm]

theorem put_distinct {t : Tab} (h : keysDistinct t) (k v : JVal) :
    keysDistinct (eqtablePut t k v).1 := by
  unfold keysDistinct at *
  rw [put_keys]
  by_cases hm : (rLookup t k).isSome
  · simp [hm, h]
  · have hn : k ∉ t.map Prod.fst := (rLookup_none_iff t k).1 (by simpa using hm)
    simp only [hm]
    refine List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp at hb; subst hb
    exact fun e => hn (e ▸ ha)

/-! ## `rDel` and `rSet` -/

theorem rDel_lookup (t : Tab) (k q : JVal) :
    rLookup (rDel t k) q = if q = k then none else rLookup t q := by
  induction t with
  | nil => simp [rDel, rLookup]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    simp only [rDel, egal_eq] at ih ⊢
    by_cases hk : k' = k
    · subst hk
      by_cases hq : q = k'
      · subst hq; simp [List.filter, ih]
      · simp [List.filter, rLookup, hq, ih]
    · by_cases hq : q = k'
      · subst hq; simp [List.filter, rLookup, hk]
      · simp [List.filter, rLookup, hk, hq, ih]

theorem rDel_of_none {t : Tab} {k : JVal} (h : rLookup t k = none) : rDel t k = t := by
  have h := (rLookup_none_iff t k).1 h
  unfold rDel
  apply List.filter_eq_self.2
  intro p hp
  have : p.1 ≠ k := fun e => h (e ▸ List.mem_map_of_mem hp)
  simp [this]

theorem rDel_distinct {t : Tab} (h : keysDistinct t) (k : JVal) : keysDistinct (rDel t k) :=
  List.Pairwise.sublist ((List.filter_sublist).map Prod.fst) h

theorem rDel_mem {t : Tab} {k : JVal} {p : JVal × JVal} (h : p ∈ rDel t k) : p ∈ t :=
  (List.mem_filter.1 h).1

theorem rDel_length {t : Tab} (h : keysDistinct t) (k : JVal) :
    (rDel t k).length + (if (rLookup t k).isSome then 1 else 0) = t.length := by
  induction t with
  | nil => simp [rDel, rLookup]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    unfold keysDistinct at h
    simp only [List.map_cons, List.nodup_cons] at h
    have ih := ih h.2
    by_cases hk : k' = k
    · subst hk
      have hn : rLookup t k' = none := (rLookup_none_iff t k').2 h.1
      have : rDel t k' = t := rDel_of_none hn
      simp only [rDel, egal_eq] at this
      simp [rDel, rLookup, List.filter, this]
    · have hk' : ¬ k = k' := fun e => hk e.symm
      simp only [rDel, egal_eq] at ih
      simp [rDel, List.filter, rLookup, hk, hk']
      omega

theorem rSet_lookup (t : Tab) (k v q : JVal) :
    rLookup (rSet t k v) q = if q = k then some v else rLookup t q := by
  by_cases hq : q = k
  · subst hq; simp [rSet, rLookup]
  · have := rDel_lookup t k q
    simp only [rDel, egal_eq] at this
    simp [rSet, rLookup, hq, this]

theorem rSet_distinct {t : Tab} (h : keysDistinct t) (k v : JVal) : keysDistinct (rSet t k v) := by
  have hd := rDel_distinct h k
  have hn : k ∉ (rDel t k).map Prod.fst := by
    rw [← rLookup_none_iff, rDel_lookup]; simp
  unfold keysDistinct rDel at *
  simp only [rSet, List.map_cons]
  exact List.nodup_cons.2 ⟨hn, hd⟩

theorem rSet_length {t : Tab} (h : keysDistinct t) (k v : JVal) :
    (rSet t k v).length = t.length + (if (rLookup t k).isSome then 0 else 1) := by
  have := rDel_length h k
  simp only [rDel] at this
  simp only [rSet, List.length_cons]
  by_cases hm : (rLookup t k).isSome <;> simp [hm] at this ⊢ <;> omega

/-! ## Agreement of two tables -/

/-- Two `===` maps with distinct keys, the same lookups and the same size. -/
def Agree (t m : Tab) : Prop :=
  keysDistinct t ∧ keysDistinct m ∧ (∀ q, rLookup t q = rLookup m q) ∧ t.length = m.length

theorem Agree.put {t m : Tab} (h : Agree t m) (k v : JVal) :
    Agree (eqtablePut t k v).1 (rSet m k v) := by
  refine ⟨put_distinct h.1 k v, rSet_distinct h.2.1 k v, ?_, ?_⟩
  · intro q; rw [put_lookup, rSet_lookup, h.2.2.1]
  · rw [put_length, put_ins, rSet_length h.2.1, h.2.2.2, h.2.2.1]

theorem Agree.del {t m : Tab} (h : Agree t m) (k : JVal) : Agree (rDel t k) (rDel m k) := by
  refine ⟨rDel_distinct h.1 k, rDel_distinct h.2.1 k, ?_, ?_⟩
  · intro q; rw [rDel_lookup, rDel_lookup, h.2.2.1]
  · have h1 := rDel_length h.1 k
    have h2 := rDel_length h.2.1 k
    rw [h.2.2.1] at h1
    have h3 := h.2.2.2
    omega

theorem pop_eq {t : Tab} (hd : keysDistinct t) (k d : JVal) :
    eqtablePop t k d = ((rLookup t k).getD d, (rLookup t k).isSome, rDel t k) := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    unfold keysDistinct at hd
    simp only [List.map_cons, List.nodup_cons] at hd
    by_cases hk : k = k'
    · subst hk
      have : rDel t k = t := rDel_of_none ((rLookup_none_iff t k).2 hd.1)
      simp only [rDel, egal_eq] at this
      simp [eqtablePop, rLookup, rDel, List.filter, this]
    · have hk' : ¬ k' = k := fun e => hk e.symm
      have := ih hd.2
      simp only [rDel, egal_eq] at this ⊢
      simp [eqtablePop, rLookup, List.filter, hk, hk', this]

end JuliaLean.IdDicts
