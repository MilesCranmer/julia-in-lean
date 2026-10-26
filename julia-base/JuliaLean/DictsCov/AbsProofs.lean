import JuliaLean.DictsCov.AbsProps
import JuliaLean.DictsCov.LookupQ

/-! Proofs of the generic `AbstractDict` properties of `AbsProps.lean`. -/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {T D E K V X : Type}

/-- A monadic fold whose every step succeeds and tracks a reference fold. -/
theorem foldlM_ok {σ α β ε : Type} (step : σ → α → Except ε σ) (P : σ → β → Prop) (ref : β → α → β)
    (h : ∀ s b a, P s b → ∃ s', step s a = .ok s' ∧ P s' (ref b a)) :
    ∀ (l : List α) (s : σ) (b : β), P s b → ∃ s', l.foldlM step s = .ok s' ∧ P s' (l.foldl ref b)
  | [], s, _, hp => ⟨s, rfl, hp⟩
  | a :: l, s, b, hp => by
    obtain ⟨s1, h1, hp1⟩ := h s b a hp
    obtain ⟨s', h2, hp2⟩ := foldlM_ok step P ref h l s1 (ref b a) hp1
    refine ⟨s', ?_, hp2⟩
    rw [List.foldlM_cons, h1]
    exact h2

/-- The pair stored for a key. -/
def findE (o : KeyOps K) (ps : List (K × V)) (q : K) : Option (K × V) := ps.find? (fun e => o.eq q e.1)

theorem gOf_eq (o : KeyOps K) (ps : List (K × V)) (q : K) : gOf o ps q = (findE o ps q).map Prod.snd := rfl

theorem findE_none_of {o : KeyOps K} (hl : o.Lawful) {e : K × V} {rest : List (K × V)} {q : K}
    (hq : o.eq q e.1 = true) (hd : ∀ e' ∈ rest, o.eq e.1 e'.1 = false) : findE o rest q = none := by
  unfold findE
  rw [List.find?_eq_none]
  intro x hx hqx
  have := hd x hx
  rw [hl.trans e.1 q x.1 (hl.symm q e.1 hq) hqx] at this
  cases this

theorem findE_cons (o : KeyOps K) (e : K × V) (rest : List (K × V)) (q : K) :
    findE o (e :: rest) q = if o.eq q e.1 then some e else findE o rest q := by
  unfold findE
  cases h : o.eq q e.1
  · rw [List.find?_cons_of_neg (by simp [h])]; rfl
  · rw [List.find?_cons_of_pos (p := fun e => o.eq q e.1) h]; rfl

/-- Storing distinct pairs in order: each key gets its own value. -/
theorem gfold_distinct {o : KeyOps K} (hl : o.Lawful) :
    ∀ (ps : List (K × V)), ps.Pairwise (fun a b => o.eq a.1 b.1 = false) → ∀ g0 : K → Option V,
      ps.foldl (fun g kv => gset o g kv.1 kv.2) g0 =
        fun q => match findE o ps q with | some e => some e.2 | none => g0 q
  | [], _, g0 => by funext q; rfl
  | e :: rest, hd, g0 => by
    have hp := List.pairwise_cons.1 hd
    rw [List.foldl_cons, gfold_distinct hl rest hp.2]
    funext q
    rw [findE_cons]
    cases hq : o.eq q e.1
    · simp only [Bool.false_eq_true, if_false]
      cases findE o rest q <;> simp [gset, hq]
    · simp only [if_true]
      rw [findE_none_of hl hq hp.1]
      simp [gset, hq]

theorem gfold_gOf {o : KeyOps K} (hl : o.Lawful) (ps : List (K × V))
    (hd : ps.Pairwise (fun a b => o.eq a.1 b.1 = false)) :
    ps.foldl (fun g kv => gset o g kv.1 kv.2) (fun _ => none) = gOf o ps := by
  rw [gfold_distinct hl ps hd]
  funext q
  rw [gOf_eq]
  cases findE o ps q <;> rfl

theorem foldl_ite_filter {α β : Type} (p : α → Bool) (F : β → α → β) :
    ∀ (l : List α) (b : β), l.foldl (fun b a => if p a then F b a else b) b = (l.filter p).foldl F b
  | [], _ => rfl
  | a :: l, b => by
    cases h : p a
    · simp only [List.foldl_cons, h, Bool.false_eq_true, if_false, List.filter_cons]
      exact foldl_ite_filter p F l b
    · simp only [List.foldl_cons, h, if_true, List.filter_cons]
      exact foldl_ite_filter p F l (F b a)

theorem filter_findE {o : KeyOps K} (hl : o.Lawful) (f : K × V → Bool) (q : K) :
    ∀ ps : List (K × V), ps.Pairwise (fun a b => o.eq a.1 b.1 = false) →
      findE o (ps.filter f) q = (findE o ps q).filter f
  | [], _ => rfl
  | e :: rest, hd => by
    have hp := List.pairwise_cons.1 hd
    rw [findE_cons]
    cases hf : f e
    · rw [List.filter_cons_of_neg (by simp [hf]), filter_findE hl f q rest hp.2]
      cases hq : o.eq q e.1
      · rfl
      · simp only [if_true]
        rw [findE_none_of hl hq hp.1]
        simp [Option.filter, hf]
    · rw [List.filter_cons_of_pos hf, findE_cons]
      cases hq : o.eq q e.1
      · simp only [Bool.false_eq_true, if_false]
        exact filter_findE hl f q rest hp.2
      · simp [Option.filter, hf]

theorem bad_any {o : KeyOps K} (hl : o.Lawful) (f : K × V → Bool) (q : K) :
    ∀ ps : List (K × V), ps.Pairwise (fun a b => o.eq a.1 b.1 = false) →
      ((ps.filter (fun p => !f p)).map Prod.fst).any (o.eq q) =
        match findE o ps q with | some e => !f e | none => false
  | [], _ => rfl
  | e :: rest, hd => by
    have hp := List.pairwise_cons.1 hd
    rw [findE_cons]
    cases hf : f e
    · rw [List.filter_cons_of_pos (by simp [hf]), List.map_cons, List.any_cons,
        bad_any hl f q rest hp.2]
      cases hq : o.eq q e.1
      · rfl
      · simp [hf]
    · rw [List.filter_cons_of_neg (by simp [hf]), bad_any hl f q rest hp.2]
      cases hq : o.eq q e.1
      · rfl
      · simp only [if_true]
        rw [findE_none_of hl hq hp.1]
        simp [hf]

theorem gdel_fold (o : KeyOps K) :
    ∀ (bad : List K) (g : K → Option V),
      bad.foldl (gdel o) g = fun q => if bad.any (o.eq q) then none else g q
  | [], g => by funext q; rfl
  | k :: bad, g => by
    rw [List.foldl_cons, gdel_fold o bad]
    funext q
    simp only [List.any_cons, gdel]
    by_cases h1 : o.eq q k = true <;> by_cases h2 : bad.any (o.eq q) = true <;> simp [h1, h2]

theorem badkeys_eq (f : K × V → Bool) :
    ∀ (ps : List (K × V)) (acc : List K),
      ps.foldl (fun bk pair => if f pair then bk else bk ++ [pair.1]) acc =
        acc ++ (ps.filter (fun p => !f p)).map Prod.fst
  | [], acc => by simp
  | e :: rest, acc => by
    rw [List.foldl_cons, badkeys_eq f rest]
    cases hf : f e
    · simp [hf, List.filter_cons]
    · simp [hf, List.filter_cons]

/-- Deleting the keys of the rejected pairs keeps the accepted ones. -/
theorem del_bad_eq {o : KeyOps K} (hl : o.Lawful) (f : K × V → Bool) (ps : List (K × V))
    (hd : ps.Pairwise (fun a b => o.eq a.1 b.1 = false)) :
    ((ps.filter (fun p => !f p)).map Prod.fst).foldl (gdel o) (gOf o ps) = gOf o (ps.filter f) := by
  rw [gdel_fold]
  funext q
  rw [bad_any hl f q ps hd, gOf_eq, gOf_eq, filter_findE hl f q ps hd]
  cases findE o ps q with
  | none => rfl
  | some e => cases hf : f e <;> simp [Option.filter, hf]

section Lawful

variable {o : KeyOps K} {ops : DictOps T D K V}

theorem setFold_spec (hops : ops.Lawful o) (l : List (K × V)) (s : D) :
    ∃ s', l.foldlM (fun d kv => ops.setindex d kv.2 kv.1) s = .ok s' ∧
      ops.get s' = l.foldl (fun g kv => gset o g kv.1 kv.2) (ops.get s) ∧ ops.typeOf s' = ops.typeOf s := by
  obtain ⟨s', h1, h2, h3⟩ := foldlM_ok (fun d (kv : K × V) => ops.setindex d kv.2 kv.1)
    (fun (s' : D) (g : K → Option V) => ops.get s' = g ∧ ops.typeOf s' = ops.typeOf s)
    (fun g kv => gset o g kv.1 kv.2)
    (fun s1 g kv hp => by
      obtain ⟨d', e1, e2, e3⟩ := hops.set s1 kv.2 kv.1
      exact ⟨d', e1, by rw [e2, hp.1], by rw [e3, hp.2]⟩) l s (ops.get s) ⟨rfl, rfl⟩
  exact ⟨s', h1, h2, h3⟩

theorem mergeBang_spec (hops : ops.Lawful o) (others : List (Other K V)) (d : D) :
    ∃ d', mergeBang ops d others = .ok d' ∧ ops.get d' = gmerge o (ops.get d) others ∧
      ops.typeOf d' = ops.typeOf d := by
  obtain ⟨s', h1, h2, h3⟩ := foldlM_ok (σ := D) (mergeStep ops)
    (fun (s' : D) (g : K → Option V) => ops.get s' = g ∧ ops.typeOf s' = ops.typeOf d)
    (fun g oth => oth.pairs.foldl (fun g kv => gset o g kv.1 kv.2) g)
    (fun s1 g oth hp => by
      have hs : ops.get (if ops.hasLength s1 && oth.hasLength then
          ops.sizehint s1 (ops.length s1 + oth.pairs.length) else s1) = ops.get s1 ∧
          ops.typeOf (if ops.hasLength s1 && oth.hasLength then
          ops.sizehint s1 (ops.length s1 + oth.pairs.length) else s1) = ops.typeOf s1 := by
        split
        · exact hops.sizehint _ _
        · exact ⟨rfl, rfl⟩
      obtain ⟨d', e1, e2, e3⟩ := setFold_spec hops oth.pairs (if ops.hasLength s1 && oth.hasLength then
          ops.sizehint s1 (ops.length s1 + oth.pairs.length) else s1)
      exact ⟨d', e1, by rw [e2, hs.1, hp.1], by rw [e3, hs.2, hp.2]⟩) others d (ops.get d) ⟨rfl, rfl⟩
  exact ⟨s', h1, h2, h3⟩

theorem mergewithStep_eq (ops : DictOps T D K V) (combine : V → V → V) (s : D) (kv : K × V) :
    mergewithStep ops combine s kv =
      ops.setindex s (match ops.get s kv.1 with | some w => combine w kv.2 | none => kv.2) kv.1 := by
  unfold mergewithStep haskeyAD inKeySet getindexAD
  cases ops.get s kv.1 <;> rfl

theorem mergewith2_spec (hops : ops.Lawful o) (combine : V → V → V) (d2 : Other K V) (s : D) :
    ∃ s', mergewithBang2 ops combine s d2 = .ok s' ∧
      ops.get s' = d2.pairs.foldl (fun g kv =>
        gset o g kv.1 (match g kv.1 with | some w => combine w kv.2 | none => kv.2)) (ops.get s) ∧
      ops.typeOf s' = ops.typeOf s := by
  obtain ⟨s', h1, h2, h3⟩ := foldlM_ok (σ := D) (mergewithStep ops combine)
    (fun (s' : D) (g : K → Option V) => ops.get s' = g ∧ ops.typeOf s' = ops.typeOf s)
    (fun g kv => gset o g kv.1 (match g kv.1 with | some w => combine w kv.2 | none => kv.2))
    (fun s1 g kv hp => by
      obtain ⟨d', e1, e2, e3⟩ := hops.set s1
        (match ops.get s1 kv.1 with | some w => combine w kv.2 | none => kv.2) kv.1
      exact ⟨d', by rw [mergewithStep_eq]; exact e1, by rw [e2, hp.1], by rw [e3, hp.2]⟩)
    d2.pairs s (ops.get s) ⟨rfl, rfl⟩
  exact ⟨s', h1, h2, h3⟩

theorem mergewith_spec (hops : ops.Lawful o) (combine : V → V → V) (others : List (Other K V)) (d : D) :
    ∃ d', mergewithBang ops combine d others = .ok d' ∧
      ops.get d' = gmergewith o combine (ops.get d) others ∧ ops.typeOf d' = ops.typeOf d := by
  obtain ⟨s', h1, h2, h3⟩ := foldlM_ok (σ := D) (mergewithBang2 ops combine)
    (fun (s' : D) (g : K → Option V) => ops.get s' = g ∧ ops.typeOf s' = ops.typeOf d)
    (fun g oth => oth.pairs.foldl (fun g kv =>
      gset o g kv.1 (match g kv.1 with | some w => combine w kv.2 | none => kv.2)) g)
    (fun s1 g oth hp => by
      obtain ⟨d', e1, e2, e3⟩ := mergewith2_spec hops combine oth s1
      exact ⟨d', e1, by rw [e2, hp.1], by rw [e3, hp.2]⟩) others d (ops.get d) ⟨rfl, rfl⟩
  exact ⟨s', h1, h2, h3⟩

theorem copy_spec (hl : o.Lawful) (hops : ops.Lawful o) (e src : D) (he : ops.get e = fun _ => none) :
    ∃ d', mergeBang ops e [ops.other src] = .ok d' ∧ ops.get d' = ops.get src ∧
      ops.typeOf d' = ops.typeOf e := by
  obtain ⟨d', h1, h2, h3⟩ := mergeBang_spec hops [ops.other src] e
  refine ⟨d', h1, ?_, h3⟩
  rw [h2, gmerge, he, List.foldl_cons, List.foldl_nil]
  show List.foldl _ _ (ops.pairs src) = _
  rw [gfold_gOf hl _ (hops.distinct src), hops.get_pairs]

end Lawful

theorem zip_fst_snd {A B : Type} : ∀ l : List (A × B), List.zip (l.map Prod.fst) (l.map Prod.snd) = l
  | [] => rfl
  | a :: l => by simp [zip_fst_snd l]

theorem copyKeySet_fold {o : KeyOps K} (hl : o.Lawful) :
    ∀ (ps : List (K × V)) (acc : List K), ps.Pairwise (fun a b => o.eq a.1 b.1 = false) →
      (∀ a ∈ acc, ∀ e ∈ ps, o.eq e.1 a = false) →
      (ps.map Prod.fst).foldl (fun s k => if s.any (o.eq k) then s else s ++ [k]) acc =
        acc ++ ps.map Prod.fst
  | [], acc, _, _ => by simp
  | e :: rest, acc, hd, ha => by
    have hp := List.pairwise_cons.1 hd
    have hnot : acc.any (o.eq e.1) = false := by
      rw [List.any_eq_false]
      intro a hacc h
      rw [ha a hacc e List.mem_cons_self] at h
      cases h
    rw [List.map_cons, List.foldl_cons, hnot]
    simp only [Bool.false_eq_true, if_false]
    rw [copyKeySet_fold hl rest (acc ++ [e.1]) hp.2]
    · simp
    · intro a hacc e' he'
      rcases List.mem_append.1 hacc with h | h
      · exact ha a h e' (List.mem_cons_of_mem _ he')
      · rw [List.mem_singleton.1 h]
        cases h2 : o.eq e'.1 e.1
        · rfl
        · have := hp.1 e' he'
          rw [hl.symm _ _ h2] at this
          cases this

theorem iterPartAll_keys {ops : DictOps T D K V} (d : D) :
    iterPartAll ops .keys d = (ops.pairs d).map Prod.fst := by
  unfold iterPartAll
  induction ops.pairs d with
  | nil => rfl
  | cons a l ih => simp only [List.filterMap_cons]; rw [ih]; rfl

theorem iterPartAll_vals {ops : DictOps T D K V} (d : D) :
    iterPartAll ops .vals d = (ops.pairs d).map Prod.snd := by
  unfold iterPartAll
  induction ops.pairs d with
  | nil => rfl
  | cons a l ih => simp only [List.filterMap_cons]; rw [ih]; rfl

theorem absLookupSpec_proven : AbsLookupSpec := by
  intro T D K V o ops hops d k
  have hg := hops.get_pairs d
  refine ⟨by simp [haskeyAD, inKeySet, hg], by simp [inKeySet, hg], fun valcmp v => ?_, rfl, ?_,
    fun A tuple k1 k2 ks => ⟨rfl, fun v => rfl⟩, fun t A key => rfl⟩
  · unfold inPairAD; rw [hg]; rfl
  · unfold getindexAD; rw [hg]; cases gOf o (ops.pairs d) k <;> rfl

theorem absIterSpec_proven : AbsIterSpec := by
  intro T D K V o ops hl hops d
  refine ⟨iterPartAll_keys d, iterPartAll_vals d, fun S p kv s => ⟨rfl, rfl⟩, fun p => hops.length d,
    fun isempty p => rfl, ?_, rfl, ?_, fun showVector p => rfl, fun showarg => ?_, fun showarg name => rfl⟩
  · rw [iterPartAll_keys, iterPartAll_vals]; exact zip_fst_snd _
  · unfold copyKeySet
    rw [iterPartAll_keys, copyKeySet_fold hl _ [] (hops.distinct d) (by simp)]
    simp
  · unfold summaryAD
    rw [hops.length]

theorem absTypeSpec_proven : AbsTypeSpec := by
  intro T D K V ops k v d
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun K' V' h => ?_, rfl, rfl⟩
  rcases h with rfl | rfl
  · cases V' <;> rfl
  · cases K' <;> rfl

theorem absCopyMergeSpec_proven : AbsCopyMergeSpec := by
  intro T D K V o ops hl hops d
  have he := hops.emptyT d (keytypeAD ops d) (valtypeAD ops d)
  refine ⟨⟨he.1, he.2.1, he.2.2⟩, fun V' => hops.emptyT d _ V', ?_, fun src => ⟨rfl, ?_⟩,
    fun others => mergeBang_spec hops others d, fun combine others => ?_, fun p => rfl,
    fun n => rfl, rfl, fun E dops mk h hmk => ?_⟩
  · obtain ⟨d', h1, h2, -⟩ := copy_spec hl hops (emptyAD ops d) d he.1
    exact ⟨d', h1, h2⟩
  · obtain ⟨e, h1, h2⟩ := hops.emptyBang d
    obtain ⟨d', h3, h4, -⟩ := copy_spec hl hops e src h2
    refine ⟨d', ?_, h4⟩
    show (if false = true then _ else _) = _
    simp only [Bool.false_eq_true, if_false]
    rw [h1]
    exact h3
  · obtain ⟨d', h1, h2, -⟩ := mergewith_spec hops combine others d
    exact ⟨d', h1, h2, rfl, rfl⟩
  · unfold convertAD
    rw [hmk]
    show (if (dops.length h != ops.length d) = true then _ else _) = _
    by_cases hlen : dops.length h = ops.length d
    · simp [hlen]
    · simp [hlen]; try rfl

theorem promoteK_foldl (promote : T → T → T) :
    ∀ (K0 : T) (ds : List (DictTy T)), promoteK promote K0 ds = ds.foldl (fun K t => promote K t.K) K0
  | _, [] => rfl
  | K0, d :: ds => promoteK_foldl promote (promote K0 d.K) ds

theorem promoteV_foldl (promote : T → T → T) :
    ∀ (V0 : T) (ds : List (DictTy T)), promoteV promote V0 ds = ds.foldl (fun V t => promote V t.V) V0
  | _, [] => rfl
  | V0, d :: ds => promoteV_foldl promote (promote V0 d.V) ds

theorem absMergeSpec_proven : AbsMergeSpec := by
  intro T D E K V o ops dops hl hops hdops promote dictOf hdict d others combine
  obtain ⟨t, ht, htg⟩ := hdict (promoteK promote (keytypeAD ops d) (others.map Prod.fst))
    (promoteV promote (valtypeAD ops d) (others.map Prod.fst)) (ops.pairs d) (hops.distinct d)
  have htd : typeddict ops promote dictOf d (others.map Prod.fst) = .ok t := ht
  refine ⟨?_, ?_, rfl, fun K0 ds => ⟨promoteK_foldl promote K0 ds, promoteV_foldl promote K0 ds⟩⟩
  · obtain ⟨t', h1, h2, -⟩ := mergeBang_spec hdops (others.map Prod.snd) t
    refine ⟨t', ?_, by rw [h2, htg, hops.get_pairs]⟩
    unfold mergeAD
    rw [htd]
    exact h1
  · obtain ⟨t', h1, h2, -⟩ := mergewith_spec hdops combine (others.map Prod.snd) t
    refine ⟨t', ?_, by rw [h2, htg, hops.get_pairs]⟩
    unfold mergewithAD
    rw [htd]
    exact h1

theorem absFilterMapSpec_proven : AbsFilterMapSpec := by
  intro T D K V o ops hl hops d f
  have hdist := hops.distinct d
  refine ⟨?_, ?_, ?_, fun g => ?_⟩
  · -- filter!
    unfold filterBangAD
    rw [badkeys_eq f (ops.pairs d) [], List.nil_append]
    obtain ⟨d', h1, h2⟩ := foldlM_ok (fun d k => ops.delete d k)
      (fun (s : D) (g : K → Option V) => ops.get s = g) (gdel o)
      (fun s g k hp => by
        obtain ⟨d', e1, e2⟩ := hops.del s k
        exact ⟨d', e1, by rw [e2, hp]⟩) ((ops.pairs d |>.filter fun p => !f p).map Prod.fst) d
      (ops.get d) rfl
    refine ⟨d', h1, ?_⟩
    rw [h2, hops.get_pairs d, del_bad_eq hl f _ hdist]
  · -- filter_in_one_pass!
    unfold filterInOnePass
    obtain ⟨d', h1, h2⟩ := foldlM_ok (fun d' (pair : K × V) => if !f pair then ops.delete d' pair.1 else pure d')
      (fun (s : D) (g : K → Option V) => ops.get s = g)
      (fun g pair => if !f pair then gdel o g pair.1 else g)
      (fun s g pair hp => by
        cases hf : f pair
        · obtain ⟨d', e1, e2⟩ := hops.del s pair.1
          refine ⟨d', ?_, ?_⟩
          · simp only [hf, Bool.not_false, if_true]; exact e1
          · simp only [hf, Bool.not_false, if_true]; rw [e2, hp]
        · refine ⟨s, ?_, ?_⟩
          · simp only [hf, Bool.not_true, Bool.false_eq_true, if_false]; rfl
          · simp only [hf, Bool.not_true, Bool.false_eq_true, if_false]; exact hp)
      (ops.pairs d) d (ops.get d) rfl
    refine ⟨d', h1, ?_⟩
    rw [h2, foldl_ite_filter (fun p => !f p) (fun g pair => gdel o g pair.1), ← List.foldl_map,
      hops.get_pairs d, del_bad_eq hl f _ hdist]
  · -- filter
    unfold filterAD
    have he := hops.emptyT d (keytypeAD ops d) (valtypeAD ops d)
    obtain ⟨d', h1, h2, h3⟩ := foldlM_ok
      (fun df (pair : K × V) => if f pair then ops.setindex df pair.2 pair.1 else pure df)
      (fun (s : D) (g : K → Option V) => ops.get s = g ∧ ops.typeOf s = ops.typeOf (emptyAD ops d))
      (fun g pair => if f pair then gset o g pair.1 pair.2 else g)
      (fun s g pair hp => by
        cases hf : f pair
        · refine ⟨s, ?_, ?_⟩
          · simp only [hf, Bool.false_eq_true, if_false]; rfl
          · simp only [hf, Bool.false_eq_true, if_false]; exact hp
        · obtain ⟨d', e1, e2, e3⟩ := hops.set s pair.2 pair.1
          refine ⟨d', ?_, ?_⟩
          · simp only [hf, if_true]; exact e1
          · simp only [hf, if_true]; exact ⟨by rw [e2, hp.1], by rw [e3, hp.2]⟩)
      (ops.pairs d) (emptyAD ops d) (ops.get (emptyAD ops d)) ⟨rfl, rfl⟩
    refine ⟨d', h1, ?_, by rw [h3]; exact he.2.1, by rw [h3]; exact he.2.2⟩
    rw [h2, foldl_ite_filter f (fun g pair => gset o g pair.1 pair.2)]
    have he1 : ops.get (emptyAD ops d) = fun _ => none := he.1
    rw [he1, gfold_gOf hl _ (hdist.filter f)]
  · -- map!
    unfold mapValuesAD pairsAD
    obtain ⟨d', h1, h2, -⟩ := setFold_spec hops ((ops.pairs d).map fun kv => (kv.1, g kv.2)) d
    refine ⟨d', ?_, ?_⟩
    · rw [← h1, List.foldlM_map]
    · rw [h2]
      have hdm : ((ops.pairs d).map fun kv => (kv.1, g kv.2)).Pairwise
          (fun a b => o.eq a.1 b.1 = false) := by
        rw [List.pairwise_map]; exact hdist
      rw [gfold_distinct hl _ hdm]
      funext q
      have hfm : findE o ((ops.pairs d).map fun kv => (kv.1, g kv.2)) q =
          (findE o (ops.pairs d) q).map fun kv => (kv.1, g kv.2) := by
        unfold findE; rw [List.find?_map]; rfl
      rw [hfm, hops.get_pairs d, gOf_eq]
      cases findE o (ops.pairs d) q <;> rfl

theorem absGetBangSpec_proven : AbsGetBangSpec := by
  intro T D K V Q W o ops c cv hl hops d key0 default
  refine ⟨?_, fun w => rfl⟩
  cases hc : c.convert key0 with
  | error e =>
    show getBangFAD ops c cv default d key0 = .error (.dict e)
    unfold getBangFAD
    rw [hc]
    rfl
  | ok key =>
    show (match ops.get d key with
      | some v => getBangFAD ops c cv default d key0 = .ok (v, d)
      | none => _)
    cases hg : ops.get d key with
    | some v =>
      show getBangFAD ops c cv default d key0 = .ok (v, d)
      unfold getBangFAD
      rw [hc]
      show (if haskeyAD ops d key then _ else _) = _
      simp only [haskeyAD, inKeySet, hg, Option.isSome_some, if_true]
      show (getindexAD ops d key >>= _) = _
      simp only [getindexAD, hg]
      rfl
    | none =>
      show (match default () with
        | .error e => getBangFAD ops c cv default d key0 = .error e
        | .ok w => _)
      have hpre : getBangFAD ops c cv default d key0 = (do
          let w ← default ()
          let v ← liftD (cv.convert w)
          let t ← ops.setindex d v key
          pure (v, t)) := by
        unfold getBangFAD
        rw [hc]
        show (if haskeyAD ops d key then _ else _) = _
        simp only [haskeyAD, inKeySet, hg, Option.isSome_none, Bool.false_eq_true, if_false]
      cases hd : default () with
      | error e => show getBangFAD ops c cv default d key0 = .error e; rw [hpre, hd]; rfl
      | ok w =>
        show (match cv.convert w with
          | .error e => getBangFAD ops c cv default d key0 = .error (.dict e)
          | .ok v => _)
        cases hv : cv.convert w with
        | error e =>
          show getBangFAD ops c cv default d key0 = .error (.dict e)
          rw [hpre, hd]
          show (liftD (cv.convert w) >>= _) = _
          rw [hv]
          rfl
        | ok v =>
          obtain ⟨d', e1, e2, -⟩ := hops.set d v key
          refine ⟨d', ?_, e2⟩
          rw [hpre, hd]
          show (liftD (cv.convert w) >>= _) = _
          rw [hv]
          show (ops.setindex d v key >>= _) = _
          rw [e1]
          rfl

theorem kvPair_bad {bad : Option (List X)} (h : ∀ k v, bad ≠ some [k, v]) :
    kvPair bad = .error (.argumentError dictKVMsg) := by
  match bad, h with
  | none, _ => rfl
  | some [], _ => rfl
  | some [_], _ => rfl
  | some [k, v], h => exact absurd rfl (h k v)
  | some (_ :: _ :: _ :: _), _ => rfl

section Grow

variable {o : KeyOps X} {ty : TyOps T X} {ops : DictOps T D X X}

theorem growStep_spec (hl : o.Lawful) (hops : ops.Lawful o) (dest : D) (k v : X) :
    let K := keytypeAD ops dest
    let V := valtypeAD ops dest
    ∃ d', (if ty.isa k K && ty.isa v V then ops.setindex dest v k else do
        let new := ops.emptyT dest (ty.join K (ty.typeOf k)) (ty.join V (ty.typeOf v))
        let new ← mergeBang ops new [ops.other dest]
        ops.setindex new v k) = .ok d' ∧ ops.get d' = gset o (ops.get dest) k v := by
  intro K V
  split
  · obtain ⟨d', e1, e2, -⟩ := hops.set dest v k
    exact ⟨d', e1, e2⟩
  · have he := hops.emptyT dest (ty.join K (ty.typeOf k)) (ty.join V (ty.typeOf v))
    obtain ⟨n, h1, h2, -⟩ := copy_spec hl hops _ dest he.1
    obtain ⟨d', e1, e2, -⟩ := hops.set n v k
    refine ⟨d', ?_, by rw [e2, h2]⟩
    show (mergeBang ops _ [ops.other dest] >>= _) = _
    rw [h1]
    exact e1

theorem growLoop_spec (hl : o.Lawful) (hops : ops.Lawful o) :
    ∀ (kvs : List (X × X)) (dest : D), ∃ d',
      growToLoop ty ops (kvs.map fun p => some [p.1, p.2]) dest = .ok d' ∧
      ops.get d' = kvs.foldl (fun g p => gset o g p.1 p.2) (ops.get dest)
  | [], dest => ⟨dest, rfl, rfl⟩
  | p :: kvs, dest => by
    obtain ⟨d1, h1, h2⟩ := growStep_spec (ty := ty) hl hops dest p.1 p.2
    obtain ⟨d', h3, h4⟩ := growLoop_spec hl hops kvs d1
    refine ⟨d', ?_, by rw [h4, h2]; rfl⟩
    simp only [List.map_cons, growToLoop]
    show (kvPair (some [p.1, p.2]) >>= _) = _
    show (if ty.isa p.1 (keytypeAD ops dest) && ty.isa p.2 (valtypeAD ops dest) then _ else _) = _
    split
    · rename_i hc
      have h1' := h1
      rw [if_pos hc] at h1'
      rw [h1']
      exact h3
    · rename_i hc
      have h1' := h1
      rw [if_neg hc] at h1'
      show (mergeBang ops _ [ops.other dest] >>= _) = _
      revert h1'
      show (mergeBang ops _ [ops.other dest] >>= _) = _ → _
      cases hm : mergeBang ops (ops.emptyT dest (ty.join (keytypeAD ops dest) (ty.typeOf p.1))
          (ty.join (valtypeAD ops dest) (ty.typeOf p.2))) [ops.other dest] with
      | error e => intro h; cases h
      | ok n =>
        intro h
        show (ops.setindex n p.2 p.1 >>= _) = _
        have h' : ops.setindex n p.2 p.1 = .ok d1 := h
        rw [h']
        exact h3

theorem growLoop_bad (bad : Option (List X)) (hb : ∀ k v, bad ≠ some [k, v])
    (post : List (Option (List X))) (hl : o.Lawful) (hops : ops.Lawful o) :
    ∀ (pre : List (X × X)) (dest : D),
      growToLoop ty ops (pre.map (fun p => some [p.1, p.2]) ++ bad :: post) dest =
        .error (.argumentError dictKVMsg)
  | [], dest => by
    simp only [List.map_nil, List.nil_append, growToLoop]
    show (kvPair bad >>= _) = _
    rw [kvPair_bad hb]
    rfl
  | p :: pre, dest => by
    obtain ⟨d1, h1, -⟩ := growStep_spec (ty := ty) hl hops dest p.1 p.2
    simp only [List.map_cons, List.cons_append, growToLoop]
    show (kvPair (some [p.1, p.2]) >>= _) = _
    show (if ty.isa p.1 (keytypeAD ops dest) && ty.isa p.2 (valtypeAD ops dest) then _ else _) = _
    have ih := growLoop_bad bad hb post hl hops pre d1
    split
    · rename_i hc
      rw [if_pos hc] at h1
      rw [h1]
      exact ih
    · rename_i hc
      rw [if_neg hc] at h1
      revert h1
      show (mergeBang ops _ [ops.other dest] >>= _) = _ → _
      cases hm : mergeBang ops (ops.emptyT dest (ty.join (keytypeAD ops dest) (ty.typeOf p.1))
          (ty.join (valtypeAD ops dest) (ty.typeOf p.2))) [ops.other dest] with
      | error e => intro h; cases h
      | ok n =>
        intro h
        show (ops.setindex n p.2 p.1 >>= _) = _
        have h' : ops.setindex n p.2 p.1 = .ok d1 := h
        rw [h']
        exact ih

end Grow

theorem absGrowSpec_proven : AbsGrowSpec := by
  intro T D X o ty ops hl hops dest hdest
  have hfirst : ∀ k v : X, ∃ d1, (do
      let dest := if ty.isaDict (ops.typeOf dest) (ty.typeOf k) (ty.typeOf v) then dest
        else ops.emptyT dest (ty.typeOf k) (ty.typeOf v)
      ops.setindex dest v k) = .ok d1 ∧ ops.get d1 = gset o (fun _ => none) k v := by
    intro k v
    split
    · obtain ⟨d1, e1, e2, -⟩ := hops.set dest v k
      exact ⟨d1, e1, by rw [e2, hdest]⟩
    · obtain ⟨d1, e1, e2, -⟩ := hops.set (ops.emptyT dest (ty.typeOf k) (ty.typeOf v)) v k
      exact ⟨d1, e1, by rw [e2, (hops.emptyT _ _ _).1]⟩
  refine ⟨fun kvs => ?_, rfl, fun pre bad post hb => ?_, fun DT DT0 anyT isPair pairLike et K V kv =>
    ⟨rfl, rfl, rfl, rfl⟩⟩
  · cases kvs with
    | nil => exact ⟨dest, rfl, hdest⟩
    | cons p kvs =>
      obtain ⟨d1, h1, h2⟩ := hfirst p.1 p.2
      obtain ⟨d', h3, h4⟩ := growLoop_spec (ty := ty) hl hops kvs d1
      refine ⟨d', ?_, by rw [h4, h2]; rfl⟩
      show (kvPair (some [p.1, p.2]) >>= _) = _
      show (do
        let dest := if ty.isaDict (ops.typeOf dest) (ty.typeOf p.1) (ty.typeOf p.2) then dest
          else ops.emptyT dest (ty.typeOf p.1) (ty.typeOf p.2)
        let dest ← ops.setindex dest p.2 p.1
        growToLoop ty ops (kvs.map fun (p : X × X) => some [p.1, p.2]) dest) = _
      revert h1
      split
      · intro h1; rw [h1]; exact h3
      · intro h1; rw [h1]; exact h3
  · cases pre with
    | nil =>
      show (kvPair bad >>= _) = _
      rw [kvPair_bad hb]
      rfl
    | cons p pre =>
      obtain ⟨d1, h1, -⟩ := hfirst p.1 p.2
      show (kvPair (some [p.1, p.2]) >>= _) = _
      show (do
        let dest := if ty.isaDict (ops.typeOf dest) (ty.typeOf p.1) (ty.typeOf p.2) then dest
          else ops.emptyT dest (ty.typeOf p.1) (ty.typeOf p.2)
        let dest ← ops.setindex dest p.2 p.1
        growToLoop ty ops (pre.map (fun (p : X × X) => some [p.1, p.2]) ++ bad :: post) dest) = _
      have ih := growLoop_bad (ty := ty) bad hb post hl hops pre d1
      revert h1
      split
      · intro h1; rw [h1]; exact ih
      · intro h1; rw [h1]; exact ih

end JuliaLean.DictsCov
