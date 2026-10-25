import JuliaLean.Tuples.Lemmas

/-! Proofs of the `NamedTuple` properties. -/

namespace JuliaLean.Tuples

variable {α : Type}

@[simp] theorem lookup_nil (k : String) : lookup ([] : NT α) k = none := rfl

@[simp] theorem lookup_cons (n : String) (v : α) (r : NT α) (k : String) :
    lookup ((n, v) :: r) k = if n = k then some v else lookup r k := by
  unfold lookup
  by_cases h : n = k <;> simp [List.find?_cons, h]

theorem symIn_iff (x : String) (l : List String) : symIn x l = true ↔ x ∈ l := by
  unfold symIn; simp

theorem lookup_isSome (nt : NT α) (k : String) : (lookup nt k).isSome ↔ k ∈ ntNames nt := by
  induction nt with
  | nil => simp [ntNames]
  | cons p r ih =>
    obtain ⟨n, v⟩ := p
    by_cases h : n = k
    · subst h; simp [ntNames]
    · simp [h, ih, ntNames, Ne.symm h]

theorem lookup_none (nt : NT α) (k : String) (h : k ∉ ntNames nt) : lookup nt k = none := by
  cases hl : lookup nt k with
  | none => rfl
  | some _ => exact absurd ((lookup_isSome nt k).mp (by simp [hl])) h

/-- Looking up a name in a list built by `filterMap` over names. -/
theorem lookup_filterMap (names : List String) (g : String → Option α) (k : String) :
    lookup (names.filterMap fun n => (g n).map (n, ·)) k = if k ∈ names then g k else none := by
  induction names with
  | nil => simp
  | cons n r ih =>
    simp only [List.filterMap_cons]
    cases hg : g n with
    | none =>
      simp only [Option.map_none, ih]
      by_cases h : n = k
      · subst h; simp [hg]
      · simp [Ne.symm h]
    | some v =>
      simp only [Option.map_some, lookup_cons, ih]
      by_cases h : n = k
      · subst h; simp [hg]
      · simp [h, Ne.symm h]

theorem names_filterMap (names : List String) (g : String → Option α)
    (h : ∀ n ∈ names, (g n).isSome) :
    ntNames (names.filterMap fun n => (g n).map (n, ·)) = names := by
  induction names with
  | nil => rfl
  | cons n r ih =>
    simp only [List.filterMap_cons]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h n (by simp))
    rw [hv]
    simp only [Option.map_some]
    simp only [ntNames, List.map_cons] at ih ⊢
    rw [ih (fun m hm => h m (by simp [hm]))]

theorem mem_mergeNames (an bn : List String) (k : String) :
    k ∈ mergeNames an bn ↔ k ∈ an ∨ k ∈ bn := by
  unfold mergeNames
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases ha : k ∈ an
      · exact Or.inl ha
      · right; refine ⟨h, ?_⟩
        cases hs : symIn k an
        · rfl
        · exact absurd ((symIn_iff k an).mp hs) ha

theorem merge_names (a b : NT α) : ntNames (merge a b) = mergeNames (ntNames a) (ntNames b) := by
  unfold merge
  split
  · rename_i hb; subst hb; simp [mergeNames, ntNames]
  · split
    · rename_i _ ha; subst ha
      simp only [mergeNames, ntNames, List.map_nil, List.nil_append]
      symm; apply List.filter_eq_self.mpr
      intro n _; simp [symIn]
    · apply names_filterMap
      intro n hn
      split
      · rename_i hs; exact (lookup_isSome b n).mpr ((symIn_iff n _).mp hs)
      · rename_i hs
        apply (lookup_isSome a n).mpr
        rcases (mem_mergeNames _ _ n).mp hn with h | h
        · exact h
        · exact absurd ((symIn_iff n _).mpr h) (by simpa using hs)

theorem merge_lookup (a b : NT α) (k : String) :
    lookup (merge a b) k = (lookup b k).or (lookup a k) := by
  unfold merge
  split
  · rename_i hb; subst hb; simp
  · split
    · rename_i _ ha; subst ha; simp
    · rw [lookup_filterMap]
      by_cases hkb : k ∈ ntNames b
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((lookup_isSome b k).mpr hkb)
        rw [if_pos ((mem_mergeNames _ _ k).mpr (Or.inr hkb)), if_pos ((symIn_iff k _).mpr hkb), hv]
        rfl
      · rw [lookup_none b k hkb, Option.none_or]
        have hs : symIn k (ntNames b) = false := by
          cases h : symIn k (ntNames b)
          · rfl
          · exact absurd ((symIn_iff k _).mp h) hkb
        by_cases hka : k ∈ ntNames a
        · rw [if_pos ((mem_mergeNames _ _ k).mpr (Or.inl hka)), hs]; rfl
        · rw [if_neg (fun hm => ((mem_mergeNames _ _ k).mp hm).elim hka hkb), lookup_none a k hka]

theorem structdiff_names (a : NT α) (bn : List String) :
    ntNames (structdiff a bn) = (ntNames a).filter (fun n => !bn.contains n) := by
  unfold structdiff
  split
  · rename_i h
    rw [h]; symm
    apply List.filter_eq_nil_iff.mpr
    intro n hn; simp [hn]
  · rw [names_filterMap]
    · unfold diffNames
      have e : ∀ n, symIn n bn = bn.contains n := fun n => by
        rw [Bool.eq_iff_iff, symIn_iff]; simp
      simp only [e]
    · intro n hn
      unfold diffNames at hn
      exact (lookup_isSome a n).mpr (List.mem_filter.mp hn).1

theorem structdiff_lookup (a : NT α) (bn : List String) (k : String) :
    lookup (structdiff a bn) k = if bn.contains k then none else lookup a k := by
  unfold structdiff
  split
  · rename_i h
    simp only [lookup_nil]
    split
    · rfl
    · rename_i hk
      symm; apply lookup_none
      rw [h]; simpa using hk
  · rw [lookup_filterMap]
    unfold diffNames
    by_cases hk : bn.contains k = true
    · rw [if_pos hk, if_neg]
      simp only [List.mem_filter, Bool.not_eq_true']
      rintro ⟨_, hs⟩
      have : k ∈ bn := by simpa using hk
      rw [(symIn_iff k bn).mpr this] at hs
      exact absurd hs (by decide)
    · rw [if_neg hk]
      by_cases ha : k ∈ ntNames a
      · rw [if_pos]
        simp only [List.mem_filter, Bool.not_eq_true']
        refine ⟨ha, ?_⟩
        cases hs : symIn k bn
        · rfl
        · exact absurd (by simpa using (symIn_iff k bn).mp hs) hk
      · rw [if_neg (by simp [List.mem_filter, ha]), lookup_none a k ha]

theorem selectNames_ok (a : NT α) (idxs : List String) (hn : idxs.Nodup)
    (h : ∀ k ∈ idxs, (lookup a k).isSome) :
    ∃ r, selectNames a idxs = .ok r ∧ ntNames r = idxs ∧ ∀ k ∈ idxs, lookup r k = lookup a k := by
  have key : ∀ l : List String, (∀ k ∈ l, (lookup a k).isSome) →
      ∃ r, l.mapM (fun k => (lookup a k).map (k, ·)) = some r ∧ ntNames r = l ∧
        ∀ k ∈ l, lookup r k = lookup a k := by
    intro l hl
    induction l with
    | nil => exact ⟨[], rfl, rfl, by simp⟩
    | cons k l ih =>
      obtain ⟨r, hr, hnr, hlr⟩ := ih (fun x hx => hl x (by simp [hx]))
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hl k (by simp))
      refine ⟨(k, v) :: r, ?_, ?_, ?_⟩
      · simp [List.mapM_cons, hv, hr]
      · simp [ntNames] at hnr ⊢; exact hnr
      · intro x hx
        by_cases e : k = x
        · subst e; simp [hv]
        · simp only [lookup_cons, e, if_false]
          exact hlr x (by simpa [Ne.symm e] using hx)
  obtain ⟨r, hr, hnr, hlr⟩ := key idxs h
  refine ⟨r, ?_, hnr, hlr⟩
  unfold selectNames
  rw [hr]
  simp [hn]

theorem namedTupleCorrect : NamedTupleCorrect := by
  intro α a b _ _
  refine ⟨merge_names a b, merge_lookup a b, ?_, ?_, ?_⟩
  · intro bn; exact ⟨structdiff_names a bn, structdiff_lookup a bn⟩
  · intro v k k'
    unfold setindexNT
    rw [merge_lookup]
    by_cases h : k' = k
    · subst h; simp
    · simp [Ne.symm h, h]
  · intro idxs hn h
    exact selectNames_ok a idxs hn h

end JuliaLean.Tuples
