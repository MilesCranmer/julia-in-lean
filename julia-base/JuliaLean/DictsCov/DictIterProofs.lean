import JuliaLean.DictsCov.DictProofs

/-! Proofs of the iteration, `map!` and `reduce(merge, ...)` properties of `DictProps.lean`. -/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V : Type}

/-! ## `skip_deleted` -/

theorem skipDeleted_spec (t : Table K V) (i : Nat) (h1 : 1 ≤ i) :
    (skipDeleted t i = 0 ∧ ∀ p, i ≤ p → p ≤ t.size → isFilledB (t.slots p) = false) ∨
    (i ≤ skipDeleted t i ∧ skipDeleted t i ≤ t.size ∧ isFilledB (t.slots (skipDeleted t i)) = true ∧
      ∀ p, i ≤ p → p < skipDeleted t i → isFilledB (t.slots p) = false) := by
  unfold skipDeleted
  rcases skipDeletedLoop_spec t (t.size + 1 - i) i h1 with ⟨h0, hall⟩ | ⟨ha, hb, hc, hd⟩
  · exact Or.inl ⟨h0, fun p hp1 hp2 => hall p hp1 (by omega)⟩
  · exact Or.inr ⟨ha, by omega, hc, hd⟩

theorem skipDeletedFloor_rep {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) :
    Rep o (skipDeletedFloor t).2 m := by
  have hi := h.1
  unfold skipDeletedFloor
  dsimp only
  cases hj : (skipDeleted t t.idxfloor != 0) with
  | false => exact h
  | true =>
    rw [if_pos rfl]
    have hj0 : skipDeleted t t.idxfloor ≠ 0 := by simpa using hj
    rcases skipDeleted_spec t t.idxfloor hi.idxfloor with ⟨h0, -⟩ | ⟨ha, hb, hc, hd⟩
    · exact absurd h0 hj0
    · refine ⟨⟨hi.size, hi.sizeLe, hi.slot, hi.distinct, hi.count, hi.maxprobe,
        Nat.le_trans hi.idxfloor ha, fun p hp1 hp2 hf => ?_, hi.popcursor⟩, h.2⟩
      have := hi.floorLe p hp1 hp2 hf
      by_cases hlt : p < skipDeleted t t.idxfloor
      · rw [hd p this hlt] at hf
        cases hf
      · show skipDeleted t t.idxfloor ≤ p
        omega

/-! ## The iteration protocol -/

theorem iterLoop_eq (t : Table K V) : ∀ left i, iterLoop t left i = iterFrom t left i
  | 0, _ => rfl
  | left + 1, i => by
    have hA : iterLoop t (left + 1) i = (iterateNext t i >>= fun y => match y with
        | none => pure []
        | some (e, st) => iterLoop t left st >>= fun rest => pure (e :: rest)) := rfl
    have hB : iterateNext t i = if (skipDeleted t i == 0) = true then pure none else
        (entryAt t (skipDeleted t i) >>= fun e => pure (some (e, skipDeleted t i + 1))) := rfl
    have hC : iterFrom t (left + 1) i = if (skipDeleted t i == 0) = true then pure [] else
        (entryAt t (skipDeleted t i) >>= fun e =>
          iterFrom t left (skipDeleted t i + 1) >>= fun rest => pure (e :: rest)) := rfl
    rw [hA, hB, hC]
    cases hj : (skipDeleted t i == 0) with
    | true => rfl
    | false =>
      cases he : entryAt t (skipDeleted t i) with
      | error err => rfl
      | ok e =>
        exact congrArg (fun x => x >>= fun rest => pure (e :: rest)) (iterLoop_eq t left _)

theorem collectDict_eq (t : Table K V) : collectDict t = iterList t :=
  iterLoop_eq t _ _

/-- The element of `keys(d)` / `values(d)` of a pair. -/
def proj : (p : Part) → K × V → p.Elem K V
  | .keys => Prod.fst
  | .vals => Prod.snd

theorem partAt_of_ent {t : Table K V} {i : Nat} {e : K × V} (he : ent t i = some e) (p : Part) :
    partAt t p i = .ok (proj p e) := by
  obtain ⟨k, v⟩ := e
  cases p with
  | keys => show (match t.keys i with | some k => (pure k : DR K) | none => throw DErr.undefRef) = _
            rw [(ent_some he).2.1]; rfl
  | vals => show (match t.vals i with | some v => (pure v : DR V) | none => throw DErr.undefRef) = _
            rw [(ent_some he).2.2]; rfl

theorem partRun_eq {o : KeyOps K} {t : Table K V} (hi : Inv o t) (p : Part) :
    ∀ fuel i, 1 ≤ i → 1 ≤ fuel → t.size + 2 ≤ fuel + i →
      partRun t p fuel i = .ok (((List.range' i (t.size + 1 - i)).filterMap (ent t)).map (proj p))
  | 0, i, _, h0, _ => absurd h0 (by omega)
  | fuel + 1, i, h1, _, hf => by
    have hspec := skipDeletedLoop_spec t (t.size + 1 - i) i h1
    have hi0 : (i == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    have e0 : partRun t p (fuel + 1) i = (iteratePart t p i >>= fun r => match r with
        | none => pure []
        | some (x, j) => partRun t p fuel j >>= fun rest => pure (x :: rest)) := rfl
    have e1 : iteratePart t p i =
        if (skipDeletedLoop t (t.size + 1 - i) i == 0) = true then pure none else
          (partAt t p (skipDeletedLoop t (t.size + 1 - i) i) >>= fun x =>
            pure (some (x, skipDeletedLoop t (t.size + 1 - i) i + 1))) := by
      unfold iteratePart
      rw [hi0]
      rfl
    rw [e0, e1]
    generalize skipDeletedLoop t (t.size + 1 - i) i = j at hspec ⊢
    rcases hspec with ⟨h0, hall⟩ | ⟨ha, hb, hc, hd⟩
    · subst h0
      rw [filterMap_ent_nil _ _ hall]
      rfl
    · have hj0 : (j == 0) = false := by rw [beq_eq_false_iff_ne]; omega
      obtain ⟨k, v, -, -, hent, -, -⟩ := hi.filled (by omega) (by omega) hc
      rw [hj0, ite_eq_right (by decide), partAt_of_ent hent p]
      show (partRun t p fuel (j + 1) >>= fun rest => pure (proj p (k, v) :: rest)) = _
      rw [partRun_eq hi p fuel (j + 1) (by omega) (by omega) (by omega)]
      show Except.ok (proj p (k, v) :: _) = _
      congr 1
      have hsplit : List.range' i (t.size + 1 - i) =
          List.range' i (j - i) ++ (j :: List.range' (j + 1) (t.size + 1 - (j + 1))) := by
        have h2 := List.range'_append_1 (s := i) (m := j - i) (n := t.size + 1 - j)
        rw [show i + (j - i) = j by omega,
          show j - i + (t.size + 1 - j) = t.size + 1 - i by omega] at h2
        rw [← h2, show t.size + 1 - j = (t.size + 1 - (j + 1)) + 1 by omega, List.range'_succ]
      rw [hsplit, List.filterMap_append, filterMap_ent_nil _ _ (fun p h1 h2 => hd p h1 (by omega)),
        List.filterMap_cons_some hent]
      rfl

theorem iterFrom_floor {o : KeyOps K} {t : Table K V} (hi : Inv o t) :
    ((List.range' t.idxfloor (t.size + 1 - t.idxfloor)).filterMap (ent t)) = tlist t := by
  have h1 := iterFrom_eq hi (t.size + 1) t.idxfloor hi.idxfloor (by omega)
  have h2 := iterList_eq hi
  unfold iterList at h2
  rw [h1] at h2
  exact Except.ok.inj h2

theorem collectPart_eq {o : KeyOps K} {t : Table K V} (hi : Inv o t) (p : Part) :
    collectPart t p = .ok ((tlist t).map (proj p)) := by
  unfold collectPart
  rw [partRun_eq hi p (t.size + 2) t.idxfloor hi.idxfloor (by omega) (by omega), iterFrom_floor hi]

/-! ## `only` -/

theorem collect_cons {t : Table K V} {e : K × V} (hc : collectDict t = .ok [e]) :
    ∃ st, iterateFirst t = .ok (some (e, st)) := by
  have e0 : collectDict t = (iterateNext t t.idxfloor >>= fun y => match y with
      | none => pure []
      | some (e, st) => iterLoop t t.size st >>= fun rest => pure (e :: rest)) := rfl
  rw [e0] at hc
  have hf : iterateFirst t = iterateNext t t.idxfloor := rfl
  rw [hf]
  cases hn : iterateNext t t.idxfloor with
  | error err => rw [hn] at hc; cases hc
  | ok y =>
    rw [hn] at hc
    cases y with
    | none => cases hc
    | some p =>
      obtain ⟨e', st⟩ := p
      change (iterLoop t t.size st >>= fun rest => pure (e' :: rest)) = .ok [e] at hc
      cases hr : iterLoop t t.size st with
      | error err => rw [hr] at hc; cases hc
      | ok rest =>
        rw [hr] at hc
        have := Except.ok.inj hc
        cases this
        exact ⟨st, rfl⟩

theorem onlyDict_spec {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) :
    match (generalizing := false) m with
    | [e] => onlyDict t = .ok e
    | _ => onlyDict t = .error .argumentError := by
  have hcount : dictLength t = m.length := by unfold dictLength; rw [h.1.count, h.2.length_eq]
  have hne : ∀ n, m.length = n → n ≠ 1 → onlyDict t = .error .argumentError := by
    intro n hn h1
    unfold onlyDict
    rw [hcount, hn]
    have : (n != 1) = true := by simpa using h1
    rw [this]
    rfl
  match m, h, hcount, hne with
  | [], _, _, hne => exact hne 0 rfl (by decide)
  | a :: b :: rest, _, _, hne => exact hne (rest.length + 2) (by simp) (by omega)
  | [e], h, hcount, _ =>
    have ht : tlist t = [e] := List.perm_singleton.1 h.2
    have hc : collectDict t = .ok [e] := by rw [collectDict_eq, iterList_eq h.1, ht]
    obtain ⟨st, hst⟩ := collect_cons hc
    unfold onlyDict
    rw [hcount]
    show (do match ← iterateFirst t with
      | some (e, _) => pure e
      | none => throw DErr.argumentError) = _
    rw [hst]
    rfl

/-! ## The iteration property -/

theorem dictIterSpec_proven : DictIterSpec := by
  intro K V o hl hmv t m hR
  obtain ⟨h, -⟩ := hR.rep hl hmv
  have hi := h.1
  refine ⟨fun i h1 => skipDeleted_spec t i h1, ⟨rfl, Rep.agrees hl (skipDeletedFloor_rep h)⟩,
    ⟨tlist t, by rw [collectDict_eq, iterList_eq hi], iterList_eq hi, h.2⟩,
    ⟨tlist t, by rw [collectDict_eq, iterList_eq hi], collectPart_eq hi .keys,
      collectPart_eq hi .vals⟩, ?_, onlyDict_spec h⟩
  unfold isemptyDict
  rw [hi.count, h.2.length_eq]
  cases m <;> simp

/-! ## `map!` -/

/-- The step of `map!`'s loop. -/
def mstepV (f : V → V) (t : Table K V) (i : Nat) : Table K V :=
  if isFilledB (t.slots i) then { t with vals := upd t.vals i ((t.vals i).map f) } else t

theorem mapValues_eq (t : Table K V) (f : V → V) :
    mapValues t f = (List.range' t.idxfloor (t.size + 1 - t.idxfloor)).foldl (mstepV f) t := rfl

/-- The values after `map!` has visited the slots of `l`. -/
def mvals (f : V → V) (l : List Nat) (t : Table K V) (i : Nat) : Option V :=
  if i ∈ l ∧ isFilledB (t.slots i) = true then (t.vals i).map f else t.vals i

theorem mstep_fold (f : V → V) :
    ∀ (l : List Nat), l.Nodup → ∀ t : Table K V,
      l.foldl (mstepV f) t = { t with vals := mvals f l t }
  | [], _, t => by
    cases t
    simp only [List.foldl_nil]
    congr 1
  | a :: l, hnd, t => by
    have hnd' := List.nodup_cons.1 hnd
    rw [List.foldl_cons, mstep_fold f l hnd'.2]
    unfold mstepV
    cases hfa : isFilledB (t.slots a) with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      congr 1
      funext i
      by_cases hia : i = a
      · subst hia; simp [mvals, hfa]
      · simp [mvals, hia]
    | true =>
      simp only [if_true]
      congr 1
      funext i
      by_cases hia : i = a
      · subst hia; simp [mvals, upd, hfa, hnd'.1]
      · simp [mvals, upd, hia]

theorem mapValues_ent {o : KeyOps K} {t : Table K V} (hi : Inv o t) (f : V → V) (i : Nat)
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) :
    ent (mapValues t f) i = (ent t i).map fun e => (e.1, f e.2) := by
  rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  unfold ent
  dsimp only [mvals]
  cases hf : isFilledB (t.slots i) with
  | false => simp
  | true =>
    have hfl := hi.floorLe i h1 h2 hf
    have hmem : i ∈ List.range' t.idxfloor (t.size + 1 - t.idxfloor) := by
      rw [List.mem_range'_1]; omega
    simp only [hmem, true_and, if_true]
    cases t.keys i <;> cases t.vals i <;> rfl

theorem mapValues_rep {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) (f : V → V) :
    Rep o (mapValues t f) (m.map fun e => (e.1, f e.2)) := by
  have hi := h.1
  have hs : (mapValues t f).size = t.size := by rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hsl : (mapValues t f).slots = t.slots := by rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hk : (mapValues t f).keys = t.keys := by rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hmp : (mapValues t f).maxprobe = t.maxprobe := by
    rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hfl : (mapValues t f).idxfloor = t.idxfloor := by
    rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hpc : (mapValues t f).popcursor = t.popcursor := by
    rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have hcnt : (mapValues t f).count = t.count := by
    rw [mapValues_eq, mstep_fold f _ List.nodup_range' t]
  have htl : tlist (mapValues t f) = (tlist t).map fun e => (e.1, f e.2) := by
    unfold tlist
    rw [hs, List.map_filterMap]
    exact filterMap_congr_mem fun i hmem => by
      rw [List.mem_range'_1] at hmem
      exact mapValues_ent hi f i hmem.1 (by omega)
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, fun i h1 h2 => ?_,
    fun i j a b h1 h2 h3 h4 hij ha hb => ?_, by rw [hcnt, htl, List.length_map]; exact hi.count,
    by rw [hs, hmp]; exact hi.maxprobe, by rw [hfl]; exact hi.idxfloor,
    fun i h1 h2 hf => by rw [hfl]; rw [hs] at h2; rw [hsl] at hf; exact hi.floorLe i h1 h2 hf,
    by rw [hpc]; exact hi.popcursor⟩, ?_⟩
  · rw [hs] at h2
    rcases hi.slot i h1 h2 with h0 | h0 | ⟨k, v, hk1, hv1, hs1, hc1⟩
    · exact Or.inl (by rw [hsl]; exact h0)
    · exact Or.inr (Or.inl (by rw [hsl]; exact h0))
    · have hf : isFilledB (t.slots i) = true := by rw [hs1]; exact shorthash7_filled _
      have he := mapValues_ent hi f i h1 h2
      rw [ent_of_filled hf hk1 hv1] at he
      refine Or.inr (Or.inr ⟨k, f v, by rw [hk]; exact hk1, (ent_some he).2.2, by rw [hsl]; exact hs1, ?_⟩)
      obtain ⟨d, hd, hid, hall⟩ := hc1
      exact ⟨d, by rw [hmp]; exact hd, by rw [hs]; exact hid, fun e he' => by rw [hsl, hs]; exact hall e he'⟩
  · rw [hs] at h2 h4
    rw [mapValues_ent hi f i h1 h2] at ha
    rw [mapValues_ent hi f j h3 h4] at hb
    cases hea : ent t i with
    | none => rw [hea] at ha; cases ha
    | some a' =>
      cases heb : ent t j with
      | none => rw [heb] at hb; cases hb
      | some b' =>
        rw [hea] at ha; rw [heb] at hb
        cases ha; cases hb
        exact hi.distinct i j a' b' h1 h2 h3 h4 hij hea heb
  · rw [htl]
    exact h.2.map _

/-! ## `reduce(merge, items)` -/

theorem foldl_rset_length (o : KeyOps K) :
    ∀ (l : List (K × V)) (M : RMap K V), (l.foldl (fun M kv => rset o M kv.1 kv.2) M).length ≤
      M.length + l.length
  | [], M => by simp
  | kv :: l, M => by
    rw [List.foldl_cons]
    have h1 := foldl_rset_length o l (rset o M kv.1 kv.2)
    have h2 := rset_length_le o M kv.1 kv.2
    simp only [List.length_cons]
    omega

theorem reduce_fold {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) :
    ∀ (items : List (Table K V × RMap K V)) (acc : Table K V) (M : RMap K V), Rep o acc M →
      (∀ x ∈ items, Rep o x.1 x.2) → M.length + (items.map fun x => x.2.length).sum ≤ 2 ^ 30 →
      ∃ t, (items.map Prod.fst).foldlM (fun acc d => dictMerge o acc d) acc = .ok t ∧
        Rep o t (items.foldl (fun M x => x.2.foldl (fun M kv => rset o M kv.1 kv.2) M) M)
  | [], acc, M, h, _, _ => ⟨acc, rfl, h⟩
  | x :: rest, acc, M, h, hall, hc => by
    have hx := hall x List.mem_cons_self
    have hc' : acc.count + x.1.count ≤ 2 ^ 32 := by
      rw [h.count_eq, hx.count_eq]
      simp only [List.map_cons, List.sum_cons] at hc
      omega
    obtain ⟨t1, h1, hr1, -⟩ := Rep.dictMerge hl hmv h hx hc'
    have hlen := foldl_rset_length o x.2 M
    obtain ⟨t, ht, hr⟩ := reduce_fold hl hmv rest t1 _ hr1
      (fun y hy => hall y (List.mem_cons_of_mem _ hy))
      (by simp only [List.map_cons, List.sum_cons] at hc; omega)
    refine ⟨t, ?_, hr⟩
    rw [List.map_cons, List.foldlM_cons, h1]
    exact ht

theorem dictMapReduceSpec_proven : DictMapReduceSpec := by
  intro K V o hl hmv
  refine ⟨fun t m hR f => Rep.agrees hl (mapValues_rep (hR.rep hl hmv).1 f), fun items hall hc => ?_⟩
  have hall' : ∀ x ∈ items, Rep o x.1 x.2 := fun x hx => ((hall x hx).rep hl hmv).1
  match items, hall', hc with
  | [], _, _ => rfl
  | x :: rest, hall', hc =>
    obtain ⟨t, ht, hr⟩ := reduce_fold hl hmv (x :: rest) Table.empty [] (empty_rep o) hall'
      (by simpa using hc)
    exact ⟨t, ht, Rep.agrees hl hr⟩

end JuliaLean.DictsCov
