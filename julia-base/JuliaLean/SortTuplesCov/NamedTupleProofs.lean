import JuliaLean.SortTuplesCov.NamedTuple
import JuliaLean.Tuples.ProofsNT

/-! Proofs of the named-tuple properties of `NamedTuple.lean`. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds argErr NT ntNames ntValues lookup selectNames symIn
  diffNames Ops getfield_ok getfield_bounds)
open NTup

variable {α T : Type}

theorem bind_pure_map {β γ : Type} (x : R β) (f : β → γ) :
    (x >>= fun v => pure (f v)) = x.map f := by
  cases x <;> rfl

theorem lookup_cons (k : String) (v : α) (nt : NT α) (k' : String) :
    lookup ((k, v) :: nt) k' = if k = k' then some v else lookup nt k' := by
  by_cases h : k = k' <;> simp [lookup, List.find?_cons, h]

theorem lookup_of_mem : ∀ (nt : NT α), (ntNames nt).Nodup → ∀ k v, (k, v) ∈ nt → lookup nt k = some v
  | [], _, _, _, h => by simp at h
  | (k0, v0) :: nt, hn, k, v, h => by
    simp only [ntNames, List.map_cons, List.nodup_cons] at hn
    rw [lookup_cons]
    rcases List.mem_cons.1 h with e | h
    · cases e; simp
    · have hk : k0 ≠ k := by
        intro e; subst e; exact hn.1 (List.mem_map.2 ⟨(k0, v), h, rfl⟩)
      rw [if_neg hk]; exact lookup_of_mem nt hn.2 k v h

theorem mapM_lookup_sub (nt : NT α) (hn : (ntNames nt).Nodup) :
    ∀ l : NT α, (∀ p ∈ l, p ∈ nt) →
      (l.map Prod.fst).mapM (fun k => (lookup nt k).map (k, ·)) = some l
  | [], _ => rfl
  | (k, v) :: l, h => by
    rw [List.map_cons, List.mapM_cons, lookup_of_mem nt hn k v (h _ (by simp)),
      mapM_lookup_sub nt hn l (fun p hp => h p (by simp [hp]))]
    rfl

theorem selectNames_sub (nt l : NT α) (hn : (ntNames nt).Nodup) (hs : l.Sublist nt) :
    selectNames nt (ntNames l) = .ok l := by
  have e := mapM_lookup_sub nt hn l (fun p hp => hs.subset hp)
  unfold selectNames
  simp only [ntNames] at e ⊢
  rw [e]
  exact if_pos ((hs.map Prod.fst).nodup hn)

theorem zip_fst_snd : ∀ l : NT α, (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | (a, b) :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_fst_snd l]

/-! ### Construction and conversion -/

theorem ofNT_none (conv : T → α → R α) (nt : NT α) :
    ∀ (names : List String) (tys : List T), tys.length = names.length →
      names.mapM (lookup nt) = none → ∃ e, (names.zip tys).mapM (ofNTField conv nt) = .error e
  | [], _, _, h => by simp at h
  | _ :: _, [], hl, _ => by simp at hl
  | n :: ns, ty :: ts, hl, h => by
    rw [List.zip_cons_cons, List.mapM_cons]
    cases hn : lookup nt n with
    | none => exact ⟨.fieldError, by simp [ofNTField, hn]⟩
    | some x =>
      have hns : ns.mapM (lookup nt) = none := by
        rw [List.mapM_cons, hn] at h
        cases hm : ns.mapM (lookup nt) with
        | none => rfl
        | some _ => rw [hm] at h; cases h
      obtain ⟨e, he⟩ := ofNT_none conv nt ns ts (by simpa using hl) hns
      cases hc : conv ty x with
      | error e' => exact ⟨e', by simp [ofNTField, hn, hc]⟩
      | ok y => exact ⟨e, by simp [ofNTField, hn, hc, he]⟩

theorem ofNT_some (conv : T → α → R α) (nt : NT α) :
    ∀ (names : List String) (tys : List T) (xs : List α), tys.length = names.length →
      names.mapM (lookup nt) = some xs →
      (names.zip tys).mapM (ofNTField conv nt) = (tys.zip xs).mapM fun p => conv p.1 p.2
  | [], _, xs, _, h => by simp at h; subst h; simp
  | _ :: _, [], _, hl, _ => by simp at hl
  | n :: ns, ty :: ts, xs, hl, h => by
    rw [List.mapM_cons] at h
    cases hn : lookup nt n with
    | none => rw [hn] at h; cases h
    | some x =>
      cases hm : ns.mapM (lookup nt) with
      | none => rw [hn, hm] at h; cases h
      | some xs' =>
        rw [hn, hm] at h
        cases h
        rw [List.zip_cons_cons, List.zip_cons_cons, List.mapM_cons, List.mapM_cons,
          ofNT_some conv nt ns ts xs' (by simpa using hl) hm]
        simp [ofNTField, hn]

theorem totupleFixed_short (conv : T → α → R α) (hc : ∀ ty x, ∃ y, conv ty x = .ok y) :
    ∀ (tys : List T) (itr : List α), itr.length < tys.length →
      ∃ msg, totupleFixed conv tys itr = argErr msg
  | [], _, h => by simp at h
  | _ :: _, [], _ => ⟨_, rfl⟩
  | ty :: tys, x :: xs, h => by
    obtain ⟨y, hy⟩ := hc ty x
    obtain ⟨msg, hm⟩ := totupleFixed_short conv hc tys xs (by simp at h; omega)
    exact ⟨msg, by simp only [totupleFixed, hy, hm]; rfl⟩

theorem totupleFixed_long (conv : T → α → R α) :
    ∀ (tys : List T) (itr : List α), tys.length ≤ itr.length →
      totupleFixed conv tys itr = (tys.zip itr).mapM fun p => conv p.1 p.2
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | ty :: tys, x :: xs, h => by
    rw [List.zip_cons_cons, List.mapM_cons, ← totupleFixed_long conv tys xs (by simp at h; omega)]
    rfl

theorem ntConstructCorrect : NTConstructCorrect := by
  intro α T conv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, ?_⟩
  · intro names tys args _
    unfold ofTuple
    split
    · rfl
    · exact bind_pure_map _ _
  · intro names tys nt hl
    refine ⟨fun h => ?_, fun xs h => ?_⟩
    · obtain ⟨e, he⟩ := ofNT_none conv nt names tys hl h
      exact ⟨e, by unfold ofNT; rw [he]; rfl⟩
    · unfold ofNT
      rw [ofNT_some conv nt names tys xs hl h]
      exact bind_pure_map _ _
  · intro names vals hn hl
    unfold ofNamesItr ofNamesTuple
    rw [if_neg (by omega), if_pos hn]
  · intro names vals h
    unfold ofNamesItr ofNamesTuple
    by_cases hl : names.length ≠ vals.length
    · rw [if_pos hl]
    · rw [if_neg hl, if_neg (h.resolve_right hl)]
  · intro tys itr hl hc
    exact totupleFixed_short conv hc tys itr hl
  · intro tys itr hl
    exact totupleFixed_long conv tys itr hl
  · intro tys nt h
    unfold toTupleType
    rw [if_pos h]

/-! ### Access -/

theorem ntAccessCorrect : NTAccessCorrect := by
  intro α t hn
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, fun _ => rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro i h1 h2
    obtain ⟨x, hx, hg⟩ := getfield_some (d := ntValues t) h1 (by simpa [ntValues] using h2)
    refine ⟨x, hx, ?_, hg, ?_⟩
    · unfold NTup.iterate
      rw [if_neg (by omega), hg]
      rfl
    · unfold NTup.indexedIterate
      rw [hg]
      rfl
  · intro i h
    unfold NTup.iterate
    rw [if_pos h]
  · intro i h
    exact getfield_none (d := ntValues t) (by simpa [ntValues] using h)
  · cases t <;> rfl
  · cases t with
    | nil => rfl
    | cons p r =>
      rw [if_neg (List.cons_ne_nil _ _)]
      exact selectNames_sub (p :: r) r hn (by simp)
  · unfold NTup.front
    rw [JuliaLean.Tuples.front_spec]
    by_cases h : t = []
    · subst h; rfl
    · have h' : ntNames t ≠ [] := by simpa [ntNames] using h
      rw [if_neg h', if_neg h]
      have e : (ntNames t).dropLast = ntNames t.dropLast := by simp [ntNames, List.map_dropLast]
      show selectNames t (ntNames t).dropLast = _
      rw [e]
      exact selectNames_sub t _ hn (List.dropLast_sublist t)
  · unfold NTup.reverse ofNamesTuple
    rw [JuliaLean.Tuples.revargs_eq, JuliaLean.Tuples.revargs_eq,
      if_neg (by simp [ntNames, ntValues]), if_pos ((List.reverse_perm _).nodup_iff.2 hn)]
    have := zip_fst_snd t.reverse
    simp only [List.map_reverse] at this
    simp only [ntNames, ntValues]
    rw [this]

/-! ### Comparison -/

theorem ntCompareCorrect : NTCompareCorrect := by
  intro α o a b
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun _ => rfl, rfl⟩
  · unfold NTup.isequal
    by_cases h : ntNames a = ntNames b <;> simp [h]
  · unfold NTup.isequal JuliaLean.Tuples.isequalNT
    by_cases h : ntNames a = ntNames b <;> simp [h]
  · intro h
    exact ⟨by unfold NTup.lt; rw [if_neg h], by unfold NTup.isless; rw [if_neg h]⟩
  · intro h
    unfold NTup.isless
    rw [if_pos h]

/-! ### `map` and `filter` -/

theorem filter_names (g : α → Bool) : ∀ (xs : NT α), (ntNames xs).Nodup →
    (ntNames xs).filter (fun k => (lookup xs k).any g) = ntNames (xs.filter fun p => g p.2)
  | [], _ => rfl
  | (k, v) :: xs, hn => by
    simp only [ntNames, List.map_cons, List.nodup_cons] at hn
    have ih := filter_names g xs hn.2
    have hc : ∀ k' ∈ ntNames xs,
        (lookup ((k, v) :: xs) k').any g = (lookup xs k').any g := by
      intro k' hk'
      rw [lookup_cons, if_neg (fun e : k = k' => hn.1 (e ▸ hk'))]
    have e1 : ntNames ((k, v) :: xs) = k :: ntNames xs := rfl
    rw [e1, List.filter_cons, lookup_cons, if_pos rfl, List.filter_congr hc, ih]
    by_cases hg : g v <;> simp [hg, ntNames]

theorem ntMapFilterCorrect : NTMapFilterCorrect := by
  intro α β f g nt nts hn
  refine ⟨fun h => ⟨"Named tuple names do not match.", ?_⟩, fun h => ?_, ?_⟩
  · unfold NTup.map; rw [h]; rfl
  · unfold NTup.map; rw [h]; rfl
  · unfold NTup.filter
    rw [filter_names g nt hn]
    exact selectNames_sub nt _ hn (by simp)

/-! ### `merge` with iterators, `delete` -/

theorem mergeMany_eq : ∀ (a : NT α) (bs : List (NT α)),
    mergeMany a bs = bs.foldl JuliaLean.Tuples.merge a
  | _, [] => rfl
  | a, b :: cs => mergeMany_eq (JuliaLean.Tuples.merge a b) cs

theorem foldl_keyStep_nodup : ∀ (itr : List (KV α)) (ks : List String), ks.Nodup →
    (itr.foldl keyStep ks).Nodup
  | [], _, h => h
  | kv :: rest, ks, h => by
    rw [List.foldl_cons]
    apply foldl_keyStep_nodup rest
    unfold keyStep
    split
    · exact h
    · rename_i hk
      exact (List.perm_append_singleton _ _).nodup_iff.2 (List.nodup_cons.2 ⟨hk, h⟩)

theorem lookup_append (l1 l2 : NT α) (k : String) :
    lookup (l1 ++ l2) k = (lookup l1 k).or (lookup l2 k) := by
  unfold lookup
  rw [List.find?_append]
  cases l1.find? (·.1 == k) <;> rfl

theorem lookup_upd (key : String) (v : α) :
    ∀ (acc : NT α) (k : String),
      lookup (acc.map fun p => if p.1 == key then (p.1, v) else p) k =
        if key = k ∧ (lookup acc k).isSome then some v else lookup acc k
  | [], _ => by simp [lookup]
  | (k0, v0) :: acc, k => by
    rw [List.map_cons]
    have ih := lookup_upd key v acc k
    by_cases h0 : k0 = key
    · subst h0
      simp only [beq_self_eq_true, if_true, lookup_cons]
      by_cases hk : k0 = k
      · simp [hk]
      · simpa [hk] using ih
    · have h0' : (k0 == key) = false := by simp [h0]
      simp only [h0', Bool.false_eq_true, if_false, lookup_cons]
      by_cases hk : k0 = k
      · subst hk
        simp [h0, Ne.symm h0]
      · simpa [hk] using ih

theorem loop_spec : ∀ (itr : List (KV α)) (acc : NT α), (∀ kv ∈ itr, kv.isSym = true) →
    ∃ acc', mergeItrLoop acc itr = .ok acc' ∧
      acc'.map Prod.fst = itr.foldl keyStep (acc.map Prod.fst) ∧
      ∀ k, lookup acc' k = ((itr.reverse.find? (·.key == k)).map KV.val).or (lookup acc k)
  | [], acc, _ => ⟨acc, rfl, rfl, fun k => by simp⟩
  | kv :: rest, acc, h => by
    have hs : kv.isSym = true := h kv (by simp)
    have hr : ∀ x ∈ rest, x.isSym = true := fun x hx => h x (by simp [hx])
    have hrev : ∀ k, ((kv :: rest).reverse.find? (·.key == k)).map KV.val =
        ((rest.reverse.find? (·.key == k)).map KV.val).or (if kv.key = k then some kv.val else none) := by
      intro k
      rw [List.reverse_cons, List.find?_append]
      cases rest.reverse.find? (·.key == k) with
      | some x => rfl
      | none => by_cases hk : kv.key = k <;> simp [hk]
    by_cases hm : acc.any (·.1 == kv.key) = true
    · have hmem : kv.key ∈ acc.map Prod.fst := by
        obtain ⟨p, hp, hpk⟩ := List.any_eq_true.1 hm
        exact List.mem_map.2 ⟨p, hp, by simpa using hpk⟩
      obtain ⟨acc', e, en, el⟩ :=
        loop_spec rest (acc.map fun p => if p.1 == kv.key then (p.1, kv.val) else p) hr
      refine ⟨acc', ?_, ?_, ?_⟩
      · simp only [mergeItrLoop, hs, Bool.not_true, Bool.false_eq_true, if_false, hm, if_true]
        exact e
      · rw [en, List.foldl_cons]
        have e1 : (acc.map fun p => if p.1 == kv.key then (p.1, kv.val) else p).map Prod.fst =
            acc.map Prod.fst := by
          rw [List.map_map]
          apply List.map_congr_left
          intro p _
          simp only [Function.comp]
          split <;> rfl
        rw [e1]
        unfold keyStep
        rw [if_pos hmem]
      · intro k
        rw [el k, lookup_upd, hrev k]
        cases rest.reverse.find? (·.key == k) with
        | some x => rfl
        | none =>
          by_cases hk : kv.key = k
          · subst hk
            have : (lookup acc kv.key).isSome := by
              rw [JuliaLean.Tuples.lookup_isSome]; exact hmem
            simp [this]
          · simp [hk]
    · obtain ⟨acc', e, en, el⟩ := loop_spec rest (acc ++ [(kv.key, kv.val)]) hr
      have hmem : kv.key ∉ acc.map Prod.fst := by
        intro hk
        obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk
        exact hm (List.any_eq_true.2 ⟨p, hp, by simp [hpk]⟩)
      refine ⟨acc', ?_, ?_, ?_⟩
      · have hm' : acc.any (·.1 == kv.key) = false := Bool.eq_false_iff.2 hm
        simp only [mergeItrLoop, hs, Bool.not_true, Bool.false_eq_true, if_false, hm']
        exact e
      · rw [en, List.foldl_cons, List.map_append]
        unfold keyStep
        rw [if_neg hmem]
        rfl
      · intro k
        rw [el k, lookup_append, hrev k]
        cases rest.reverse.find? (·.key == k) with
        | some x => rfl
        | none =>
          by_cases hk : kv.key = k
          · subst hk
            rw [JuliaLean.Tuples.lookup_none acc kv.key hmem]
            simp [lookup_cons]
          · simp [hk, lookup_cons, lookup]

theorem loop_err : ∀ (itr : List (KV α)) (acc : NT α), (∃ kv ∈ itr, kv.isSym = false) →
    mergeItrLoop acc itr = .error .typeError
  | [], _, h => by simp at h
  | kv :: rest, acc, h => by
    by_cases hs : kv.isSym = true
    · have h' : ∃ x ∈ rest, x.isSym = false := by
        obtain ⟨x, hx, hxs⟩ := h
        rcases List.mem_cons.1 hx with e | hx
        · subst e; simp [hs] at hxs
        · exact ⟨x, hx, hxs⟩
      simp only [mergeItrLoop, hs, Bool.not_true, Bool.false_eq_true, if_false]
      split
      · exact loop_err rest _ h'
      · exact loop_err rest _ h'
    · have hs' : kv.isSym = false := by simpa using hs
      simp [mergeItrLoop, hs']

theorem ntMergeItrCorrect : NTMergeItrCorrect := by
  intro α a data itr bs _
  refine ⟨rfl, rfl, mergeMany_eq a bs, fun h => ?_, fun h => ?_, fun k => ?_⟩
  · obtain ⟨acc, e, en, el⟩ := loop_spec itr [] h
    have hnd : (acc.map Prod.fst).Nodup := by
      rw [en]; exact foldl_keyStep_nodup itr [] List.nodup_nil
    refine ⟨acc, e, en, fun k => by rw [el k]; simp [lookup, lastVal], ?_⟩
    unfold mergeItr ofNamesTuple
    rw [e]
    simp only [JuliaLean.Tuples.R.bind_ok]
    rw [if_neg (by simp), if_pos hnd, zip_fst_snd]
    rfl
  · unfold mergeItr
    rw [loop_err itr [] h]
    rfl
  · unfold NTup.delete
    have e : diffNames (ntNames a) [k] = ntNames (a.filter fun p => p.1 != k) := by
      simp only [diffNames, symIn, ntNames, List.filter_map]
      congr 1
      apply List.filter_congr
      intro p _
      show (!([k].any fun x => x == p.1)) = !(p.1 == k)
      rw [List.any_cons, List.any_nil, Bool.or_false]
      by_cases h : p.1 = k
      · rw [h]
      · rw [beq_eq_false_iff_ne.2 (fun e => h e.symm), beq_eq_false_iff_ne.2 h]
    rw [e]
    exact selectNames_sub a _ (by assumption) (by simp)

/-! ### Refutation: `merge(a, zip(ks, vs))` -/

theorem mergeZip_dup : mergeZip ([] : NT Nat) ["a", "a"] [1, 2] = .error .errorException := by
  rfl

theorem mergeZipAgrees_refuted : ¬ MergeZipAgrees := by
  intro h
  have e : (Except.error Err.errorException : R (NT Nat)) = .ok [("a", 2)] :=
    mergeZip_dup.symm.trans ((h Nat [] ["a", "a"] [1, 2]).trans (by rfl))
  cases e

end JuliaLean.SortTuplesCov
