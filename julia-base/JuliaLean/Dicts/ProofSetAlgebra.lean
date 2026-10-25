import JuliaLean.Dicts.ProofReach
import JuliaLean.Dicts.ProofSetRef

/-!
# The `Set` properties

`union!` pushes the elements of `t` in slot order; `intersect!` and the
small branch of `setdiff!` delete while iterating, which never changes the
filled slots after the current one; the other `setdiff!` branch and
`symdiff!` fold deletions and insertions over the elements of `t`;
`issubset` and `==` return early on lengths, which is correct because a set
of distinct keys contained in another is no larger than it.
-/

namespace JuliaLean.Dicts

variable {K Q : Type}

/-! ## Elements and membership -/

theorem elems_eq {o : KeyOps K} {s : SetT K} (hi : Inv o s) :
    elems s = .ok ((tlist s).map (·.1)) := by
  unfold elems
  rw [iterList_eq hi] <;> rfl

theorem setIn_of_rep {o : KeyOps K} (hl : o.Lawful) {s : SetT K} {m : RMap K Unit} (h : Rep o s m)
    (x : K) : setIn o s x = .ok (rmem o m x) :=
  h.haskey_eq hl x

/-! ## `union!` -/

theorem pushConv_self (o : KeyOps K) (s : SetT K) (x : K) :
    pushConv o (Conv.self o) s x = setindex o s () x := rfl

theorem unionLoop_spec {o : KeyOps K} (hl : o.Lawful) (hg : GenericMax o) :
    ∀ (L : RMap K Unit) (s : SetT K) (m : RMap K Unit), Rep o s m → s.count + L.length ≤ 2 ^ 31 →
      ∃ s', unionLoop o (Conv.self o) s (L.map (·.1)) = .ok s' ∧
        Rep o s' (L.foldl (fun m e => rset o m e.1 ()) m)
  | [], s, _, h, _ => ⟨s, rfl, h⟩
  | e :: L, s, m, h, hc => by
    rw [List.length_cons] at hc
    obtain ⟨s1, h1, hr1, -⟩ := h.setindex hl (by omega) e.1 ()
    have hc1 : s1.count ≤ s.count + 1 := by
      rw [hr1.count_eq, h.count_eq]
      exact rset_length_le _ _ _ _
    have hne : ((s1.count : Int) == o.maxValues.val) = false := by
      have hg' : o.maxValues = JInt.typemax .i64 := hg
      rw [hg', typemax_i64_val]
      exact beq_eq_false_iff_ne.2 (by omega)
    obtain ⟨s', h2, hr2⟩ := unionLoop_spec hl hg L s1 _ hr1 (by omega)
    refine ⟨s', ?_, hr2⟩
    simp only [List.map_cons, unionLoop.eq_2, pushConv_self, h1, except_ok_bind, hne,
      Bool.false_eq_true, ite_false]
    exact h2

theorem unionBang_eq (o : KeyOps K) (c : Conv Q K) (s : SetT K) (itr : List Q) :
    unionBang o c s itr = (sizehint o s (JInt.lit .i64 ((s.count + itr.length : Nat) : Int)) false >>=
      fun s => unionLoop o c s itr) := rfl

theorem unionSet_eq (o : KeyOps K) (s t : SetT K) :
    unionSet o s t = (elems t >>= fun xs => unionBang o (Conv.self o) s xs) := rfl

theorem setUnionAgrees_thm : SetUnionAgrees := by
  intro K o hl hg s t ms mt hRs hRt
  have hmv := GenericMax.maxValuesOK hg
  obtain ⟨hs, hcs⟩ := hRs.rep hl hmv
  obtain ⟨ht, hct⟩ := hRt.rep hl hmv
  have hlen : ((tlist t).map (·.1)).length = t.count := by rw [List.length_map, ht.1.count]
  obtain ⟨s1, h1, hr1, hc1, -⟩ := merge_hint hmv hs ((tlist t).map (·.1)).length (by omega)
  obtain ⟨s', h2, hr2⟩ := unionLoop_spec hl hg (tlist t) s1 ms hr1
    (by rw [hc1, ← ht.1.count]; omega)
  have hp : List.Perm ((tlist t).foldl (fun m e => rset o m e.1 ()) ms)
      (mt.foldl (fun m e => rset o m e.1 ()) ms) :=
    foldl_rset_perm hl ht.2 (tlist_pairwise ht.1) ms
  have hr := hr2.perm hp
  refine ⟨s', ?_, Rep.agrees hl hr, fun x => ?_⟩
  · rw [unionSet_eq, elems_eq ht.1, except_ok_bind, unionBang_eq, h1, except_ok_bind]
    exact h2
  · rw [setIn_of_rep hl hr x]
    show Except.ok (rfind o (mt.foldl (fun m e => rset o m e.1 ()) ms) x).isSome = _
    rw [isSome_rfind_foldl_rset hl x mt ms] <;> rfl

/-! ## Deleting while iterating -/

/-- The state of the set `filter!` loop at index `i`: entries below `i` are
filtered, slots from `i` on are those of the original set `s`. -/
structure SFInv (o : KeyOps K) (kb : K → Bool) (s S : SetT K) (i : Nat) : Prop where
  inv : Inv o S
  size : S.size = s.size
  ent : ∀ p, 1 ≤ p → p ≤ s.size →
    ent S p = if p < i then (ent s p).filter (fun e => kb e.1) else ent s p
  filled : ∀ p, i ≤ p → p ≤ s.size → isFilledB (S.slots p) = isFilledB (s.slots p)

theorem filterLoop_done {o : KeyOps K} {keep : K → DR Bool} {S : SetT K} {i : Nat} (left : Nat)
    (hjd : skipDeleted S i = 0) : filterLoop o keep (left + 1) S i = pure S := by
  rw [filterLoop.eq_2]
  try dsimp only
  rw [hjd, if_pos (by decide)]

theorem filterLoop_step {o : KeyOps K} {keep : K → DR Bool} {S : SetT K} {i j : Nat} (left : Nat)
    {x : K} (hjd : skipDeleted S i = j) (hj : j ≠ 0) (hx : S.keys j = some x) :
    filterLoop o keep (left + 1) S i = (keep x >>= fun b =>
      if (!b) = true then (setDelete o S x >>= fun S' => filterLoop o keep left S' (j + 1))
      else (pure S >>= fun S' => filterLoop o keep left S' (j + 1))) := by
  rw [filterLoop.eq_2]
  try dsimp only
  rw [hjd, if_neg (by simpa using hj), hx] <;> rfl

theorem filterLoop_spec {o : KeyOps K} (hl : o.Lawful) {s : SetT K} (keep : K → DR Bool)
    (kb : K → Bool) (hk : ∀ x, keep x = .ok (kb x)) :
    ∀ left (S : SetT K) i, SFInv o kb s S i → 1 ≤ i → s.size + 2 ≤ i + left →
      ∃ S', filterLoop o keep left S i = .ok S' ∧ Inv o S' ∧ S'.size = s.size ∧
        ∀ p, 1 ≤ p → p ≤ s.size → ent S' p = (ent s p).filter (fun e => kb e.1)
  | 0, S, i, hF, _, hli => ⟨S, rfl, hF.inv, hF.size, fun p h1 h2 => by
      rw [hF.ent p h1 h2, if_pos (by omega)]⟩
  | left + 1, S, i, hF, hi1, hli => by
    have hspec := skipDeletedLoop_spec S (S.size + 1 - i) i hi1
    have hsd : skipDeleted S i = skipDeletedLoop S (S.size + 1 - i) i := rfl
    rw [← hsd, hF.size] at hspec
    obtain ⟨j, hjd⟩ : ∃ j, skipDeleted S i = j := ⟨_, rfl⟩
    rw [hjd] at hspec
    rcases hspec with ⟨h0, hnone⟩ | ⟨hj1, hj2, hjf, hbefore⟩
    · rw [h0] at hjd
      refine ⟨S, filterLoop_done left hjd, hF.inv, hF.size, fun p h1 h2 => ?_⟩
      rw [hF.ent p h1 h2]
      by_cases hpi : p < i
      · rw [if_pos hpi]
      · have hf : isFilledB (s.slots p) = false := by
          rw [← hF.filled p (by omega) h2]
          exact hnone p (by omega) (by omega)
        rw [if_neg hpi, ent_of_not_filled hf] <;> rfl
    · have hjS : j ≤ s.size := by omega
      have hj0 : j ≠ 0 := by omega
      have hj1' : 1 ≤ j := by omega
      have hjS' : j ≤ S.size := by rw [hF.size]; exact hjS
      obtain ⟨k, v, hkj, -, hentS, -, -⟩ := hF.inv.filled hj1' hjS' hjf
      have hents : ent s j = some (k, v) := by
        rw [← hentS, hF.ent j hj1' hjS, if_neg (by omega)]
      have hgap : ∀ p, i ≤ p → p < j → ent s p = none := fun p h1 h2 =>
        ent_of_not_filled (by rw [← hF.filled p h1 (by omega)]; exact hbefore p h1 h2)
      have hlow : ∀ T : SetT K, (∀ p, p ≠ j → ent T p = ent S p) →
          ent T j = (ent s j).filter (fun e => kb e.1) →
          ∀ p, 1 ≤ p → p ≤ s.size →
            ent T p = if p < j + 1 then (ent s p).filter (fun e => kb e.1) else ent s p := by
        intro T hT hTj p hp1 hp2
        by_cases hpj : p = j
        · rw [hpj, if_pos (by omega)]
          exact hTj
        · rw [hT p hpj, hF.ent p hp1 hp2]
          by_cases hpi : p < i
          · rw [if_pos hpi, if_pos (by omega)]
          · rw [if_neg hpi]
            by_cases hpj' : p < j
            · rw [if_pos (by omega), hgap p (by omega) hpj'] <;> rfl
            · rw [if_neg (by omega)]
      rw [filterLoop_step left hjd hj0 hkj, hk k, except_ok_bind]
      cases hkb : kb k with
      | true =>
        rw [if_neg (by decide), dr_pure_bind]
        have hF' : SFInv o kb s S (j + 1) := by
          refine ⟨hF.inv, hF.size, hlow S (fun _ _ => rfl) ?_,
            fun p hp1 hp2 => hF.filled p (by omega) hp2⟩
          rw [hentS, hents]
          show some (k, v) = (if kb k = true then some (k, v) else none)
          rw [hkb] <;> rfl
        exact filterLoop_spec hl keep kb hk left S (j + 1) hF' (by omega) (by omega)
      | false =>
        rw [if_pos (by decide)]
        have hdel : setDelete o S k = .ok (deleteAt S j) := by
          show dictDelete o S k = _
          rw [dictDelete_of (htKeyindex_found hl hF.inv hj1' hjS' hentS (hl.refl k)),
            if_pos (by omega), Int.toNat_natCast] <;> rfl
        rw [hdel, except_ok_bind]
        obtain ⟨hI, -, -, -, hs', hkk, hvv, -, -, -, hnf, hfil⟩ :=
          deleteAt_spec hl hF.inv hj1' hjS' hentS
        have hF' : SFInv o kb s (deleteAt S j) (j + 1) := by
          refine ⟨hI, hs'.trans hF.size, hlow _ (fun p hpn => ent_eq_of (hfil p hpn)
            (by rw [hkk, upd_ne _ _ hpn]) (by rw [hvv, upd_ne _ _ hpn])) ?_,
            fun p hp1 hp2 => by rw [hfil p (by omega)]; exact hF.filled p (by omega) hp2⟩
          rw [ent_of_not_filled hnf, hents]
          show none = (if kb k = true then some (k, v) else none)
          rw [hkb] <;> rfl
        exact filterLoop_spec hl keep kb hk left _ (j + 1) hF' (by omega) (by omega)

theorem setFilterBang_spec {o : KeyOps K} (hl : o.Lawful) {s : SetT K} {m : RMap K Unit}
    (h : Rep o s m) (keep : K → DR Bool) (kb : K → Bool) (hk : ∀ x, keep x = .ok (kb x)) :
    ∃ s', setFilterBang o keep s = .ok s' ∧ Rep o s' (m.filter fun e => kb e.1) := by
  have hF : SFInv o kb s s s.idxfloor := by
    refine ⟨h.1, rfl, fun p h1 h2 => ?_, fun _ _ _ => rfl⟩
    by_cases hp : p < s.idxfloor
    · have hf : isFilledB (s.slots p) = false := by
        cases hfp : isFilledB (s.slots p)
        · rfl
        · exact absurd (h.1.floorLe p h1 h2 hfp) (by omega)
      rw [if_pos hp, ent_of_not_filled hf] <;> rfl
    · rw [if_neg hp]
  have hfl := h.1.idxfloor
  obtain ⟨S', h1, hI, hsz, hent⟩ :=
    filterLoop_spec hl keep kb hk (s.size + 1) s s.idxfloor hF hfl (by omega)
  refine ⟨S', h1, hI, ?_⟩
  have htl : tlist S' = (tlist s).filter (fun e => kb e.1) := by
    unfold tlist
    rw [hsz, List.filter_filterMap]
    apply filterMap_congr_mem
    intro p hp
    rw [List.mem_range'_1] at hp
    exact hent p hp.1 (by omega)
  rw [htl]
  exact h.2.filter _

/-! ## `intersect!` and `setdiff!` -/

theorem setIntersectAgrees_thm : SetIntersectAgrees := by
  intro K o hl hg s t ms mt hRs hRt
  have hmv := GenericMax.maxValuesOK hg
  obtain ⟨hs, -⟩ := hRs.rep hl hmv
  obtain ⟨ht, -⟩ := hRt.rep hl hmv
  obtain ⟨s', h1, hr⟩ := setFilterBang_spec hl hs (fun x => setIn o t x) (fun x => rmem o mt x)
    (fun x => setIn_of_rep hl ht x)
  refine ⟨s', h1, Rep.agrees hl hr, fun x => ?_⟩
  rw [setIn_of_rep hl hr x]
  show Except.ok (rfind o (ms.filter fun e => rmem o mt e.1) x).isSome = _
  rw [isSome_rfind_filter ms (x := x) (p := fun e => rmem o mt e.1) (c := rmem o mt x)
    (fun e he => isSome_rfind_congr hl mt (hl.symm _ _ he))] <;> rfl

theorem delFold_spec {o : KeyOps K} (hl : o.Lawful) :
    ∀ (L : RMap K Unit) (s : SetT K) (m : RMap K Unit), Rep o s m →
      ∃ s', (L.map (·.1)).foldlM (fun s x => setDelete o s x) s = .ok s' ∧
        Rep o s' (L.foldl (fun m e => rdel o m e.1) m)
  | [], s, _, h => ⟨s, rfl, h⟩
  | e :: L, s, m, h => by
    obtain ⟨s1, h1, hr1, -⟩ := h.dictDelete hl e.1
    obtain ⟨s', h2, hr2⟩ := delFold_spec hl L s1 _ hr1
    refine ⟨s', ?_, hr2⟩
    rw [List.map_cons, List.foldlM_cons]
    show (dictDelete o s e.1 >>= fun s => (L.map (·.1)).foldlM (fun s x => setDelete o s x) s) = _
    rw [h1, except_ok_bind]
    exact h2

theorem setSetdiffAgrees_thm : SetSetdiffAgrees := by
  intro K o hl hg s t ms mt hRs hRt
  have hmv := GenericMax.maxValuesOK hg
  obtain ⟨hs, -⟩ := hRs.rep hl hmv
  obtain ⟨ht, -⟩ := hRt.rep hl hmv
  have hmem : ∀ x, rmem o (ms.filter fun e => !rmem o mt e.1) x = (rmem o ms x && !rmem o mt x) :=
    fun x => isSome_rfind_filter ms (x := x) (p := fun e => !rmem o mt e.1) (c := !rmem o mt x)
      (fun e he => by
        show (!(rfind o mt e.1).isSome) = !(rfind o mt x).isSome
        rw [isSome_rfind_congr hl mt (hl.symm _ _ he)])
  have hfin : ∀ s', Rep o s' (ms.filter fun e => !rmem o mt e.1) →
      Agrees o s' (ms.filter fun e => !rmem o mt e.1) ∧
        ∀ x, setIn o s' x = .ok (rmem o ms x && !rmem o mt x) :=
    fun s' hr => ⟨Rep.agrees hl hr, fun x => by rw [setIn_of_rep hl hr x, hmem x]⟩
  unfold setdiffBang
  by_cases hsmall : 2 * s.count < t.count
  · rw [if_pos hsmall]
    obtain ⟨s', h1, hr⟩ := setFilterBang_spec hl hs (fun x => do pure (!(← setIn o t x)))
      (fun x => !rmem o mt x) (fun x => by
        show (setIn o t x >>= fun b => pure (!b)) = _
        rw [setIn_of_rep hl ht x] <;> rfl)
    exact ⟨s', h1, hfin s' hr⟩
  · rw [if_neg hsmall, elems_eq ht.1, except_ok_bind]
    obtain ⟨s', h1, hr⟩ := delFold_spec hl (tlist t) s ms hs
    have heq : (tlist t).foldl (fun m e => rdel o m e.1) ms = ms.filter fun e => !rmem o mt e.1 := by
      rw [foldl_rdel_eq]
      apply List.filter_congr
      intro e _
      exact all_not_eq hl ht.2 e.1
    rw [heq] at hr
    exact ⟨s', h1, hfin s' hr⟩

/-! ## `symdiff!` -/

/-- One step of `symdiff!`: `x in s ? delete!(s, x) : push!(s, x)`. -/
def symT (o : KeyOps K) (s : SetT K) (x : K) : DR (SetT K) := do
  if ← setIn o s x then setDelete o s x else push o s x

theorem symdiffBang_eq (o : KeyOps K) (s t : SetT K) :
    symdiffBang o s t = (elems t >>= fun xs => xs.foldlM (symT o) s) := rfl

theorem symT_of_rep {o : KeyOps K} (hl : o.Lawful) {s : SetT K} {m : RMap K Unit} (h : Rep o s m)
    (hc : s.count < 2 ^ 33) (x : K) :
    ∃ s1, symT o s x = .ok s1 ∧ Rep o s1 (symStep o m (x, ())) ∧ s1.count ≤ s.count + 1 := by
  have e1 : symT o s x = (if rmem o m x = true then setDelete o s x else push o s x) := by
    show (setIn o s x >>= fun c => if c = true then setDelete o s x else push o s x) = _
    rw [setIn_of_rep hl h x] <;> rfl
  rw [e1]
  cases hm : rmem o m x
  · rw [if_neg (by decide)]
    obtain ⟨s1, h1, hr1, -⟩ := h.setindex hl hc x ()
    refine ⟨s1, h1, ?_, ?_⟩
    · show Rep o s1 (if rmem o m x = true then rdel o m x else rset o m x ())
      rw [hm, if_neg (by decide)]
      exact hr1
    · rw [hr1.count_eq, h.count_eq]
      exact rset_length_le _ _ _ _
  · rw [if_pos rfl]
    obtain ⟨s1, h1, hr1, -⟩ := h.dictDelete hl x
    refine ⟨s1, h1, ?_, ?_⟩
    · show Rep o s1 (if rmem o m x = true then rdel o m x else rset o m x ())
      rw [hm, if_pos rfl]
      exact hr1
    · rw [hr1.count_eq, h.count_eq]
      have := rdel_length_le o m x
      omega

theorem symFold_spec {o : KeyOps K} (hl : o.Lawful) :
    ∀ (L : RMap K Unit) (s : SetT K) (m : RMap K Unit), Rep o s m → s.count + L.length ≤ 2 ^ 31 →
      ∃ s', (L.map (·.1)).foldlM (symT o) s = .ok s' ∧ Rep o s' (L.foldl (symStep o) m)
  | [], s, _, h, _ => ⟨s, rfl, h⟩
  | (k, ()) :: L, s, m, h, hc => by
    rw [List.length_cons] at hc
    obtain ⟨s1, h1, hr1, hc1⟩ := symT_of_rep hl h (by omega) k
    obtain ⟨s', h2, hr2⟩ := symFold_spec hl L s1 _ hr1 (by omega)
    refine ⟨s', ?_, hr2⟩
    simp only [List.map_cons, List.foldlM_cons, h1, except_ok_bind]
    exact h2

theorem setSymdiffAgrees_thm : SetSymdiffAgrees := by
  intro K o hl hg s t ms mt hRs hRt
  have hmv := GenericMax.maxValuesOK hg
  obtain ⟨hs, hcs⟩ := hRs.rep hl hmv
  obtain ⟨ht, hct⟩ := hRt.rep hl hmv
  have hlen : (tlist t).length = t.count := ht.1.count.symm
  obtain ⟨s', h1, hr⟩ := symFold_spec hl (tlist t) s ms hs (by omega)
  have hp : List.Perm ((tlist t).foldl (symStep o) ms) (mt.foldl (symStep o) ms) :=
    foldl_symStep_perm hl ht.2 (tlist_pairwise ht.1) ms (hs.distinct hl)
  have hr' := hr.perm hp
  refine ⟨s', ?_, Rep.agrees hl hr', fun x => ?_⟩
  · rw [symdiffBang_eq, elems_eq ht.1, except_ok_bind]
    exact h1
  · rw [setIn_of_rep hl hr' x]
    show Except.ok (rfind o (mt.foldl (symStep o) ms) x).isSome = _
    rw [isSome_rfind_foldl_symStep hl x mt ms (ht.distinct hl)] <;> rfl

/-! ## `issubset` and `==` -/

theorem allIn_spec {o : KeyOps K} (hl : o.Lawful) {b : SetT K} {mb : RMap K Unit} (h : Rep o b mb) :
    ∀ xs : List K, allIn o b xs = .ok (xs.all fun x => rmem o mb x)
  | [] => rfl
  | x :: xs => by
    show (setIn o b x >>= fun c => if c = true then allIn o b xs else pure false) = _
    rw [setIn_of_rep hl h x, except_ok_bind, List.all_cons]
    cases rmem o mb x
    · rfl
    · rw [if_pos rfl, allIn_spec hl h xs] <;> rfl

theorem issubsetSet_eq (o : KeyOps K) (a b : SetT K) :
    issubsetSet o a b =
      if a.count > b.count then pure false else (elems a >>= fun xs => allIn o b xs) := by
  unfold issubsetSet
  rfl

theorem setCompareAgrees_thm : SetCompareAgrees := by
  intro K o hl hg s t ms mt hRs hRt
  have hmv := GenericMax.maxValuesOK hg
  obtain ⟨hs, -⟩ := hRs.rep hl hmv
  obtain ⟨ht, -⟩ := hRt.rep hl hmv
  have hdm := hs.distinct hl
  have hdt := ht.distinct hl
  have hcs := hs.count_eq
  have hct := ht.count_eq
  have hsub : issubsetSet o s t = .ok (ms.all fun e => rmem o mt e.1) := by
    rw [issubsetSet_eq]
    by_cases hgt : s.count > t.count
    · rw [if_pos hgt]
      cases hall : List.all ms (fun e => rmem o mt e.1)
      · rfl
      · exfalso
        have := pigeon hl ms mt hdm (fun e he => List.all_eq_true.1 hall e he)
        omega
    · rw [if_neg hgt, elems_eq hs.1, except_ok_bind, allIn_spec hl ht, List.all_map, hs.2.all_eq]
        <;> rfl
  refine ⟨hsub, ?_⟩
  unfold setEq
  by_cases heq : s.count = t.count
  · rw [if_pos (by simp [heq]), hsub]
    cases hall : List.all ms (fun e => rmem o mt e.1)
    · rfl
    · have hback := pigeon_all hl hdm (fun e he => List.all_eq_true.1 hall e he) (by omega)
      have h2 : (mt.all fun e => rmem o ms e.1) = true := List.all_eq_true.2 hback
      rw [h2] <;> rfl
  · rw [if_neg (by simp [heq])]
    cases hall : List.all ms (fun e => rmem o mt e.1)
    · rfl
    · cases hall2 : List.all mt (fun e => rmem o ms e.1)
      · rfl
      · exfalso
        have h1 := pigeon hl ms mt hdm (fun e he => List.all_eq_true.1 hall e he)
        have h2 := pigeon hl mt ms hdt (fun e he => List.all_eq_true.1 hall2 e he)
        omega

end JuliaLean.Dicts
