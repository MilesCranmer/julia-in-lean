import JuliaLean.Proofs.base.dict.ProofReach
import JuliaLean.Proofs.base.abstractset.ProofSetRef

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

/-- A reference set at the finite keyspace bound contains every key. -/
theorem full_reference_contains {o : KeyOps K} {m : RMap K Unit}
    (hmax : ∀ xs : List K, xs.Pairwise (fun a b => o.eq a b = false) →
      (xs.length : Int) ≤ o.maxValues.val)
    (hd : Distinct o m) (hcount : (m.length : Int) = o.maxValues.val) (x : K) :
    (rfind o m x).isSome = true := by
  cases hf : rfind o m x with
  | some e => rfl
  | none =>
    have hn := rfind_eq_none_iff.mp hf
    have hp : (x :: m.map Prod.fst).Pairwise (fun a b => o.eq a b = false) := by
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        exact hn e he
      · simpa only [List.pairwise_map] using hd
    have bound := hmax (x :: m.map Prod.fst) hp
    simp only [List.length_cons, List.length_map] at bound
    omega

/-- Reference insertion applies the same key conversion as `push!`. -/
def unionRefPush (o : KeyOps K) (c : Conv Q K) (m : RMap K Unit) (q : Q) : DR (RMap K Unit) :=
  match c.isa q with
  | some k => pure (rset o m k ())
  | none => do
    let k ← c.convert q
    if !(c.iseq q k) then throw .keyTypeError
    pure (rset o m k ())

theorem unionRefPush_spec {o : KeyOps K} (hl : o.Lawful) (c : Conv Q K)
    {s : SetT K} {m : RMap K Unit} (h : Rep o s m) (hc : s.count + 1 ≤ 2 ^ 32) (q : Q) :
    SameOutcome (pushConv o c s q) (unionRefPush o c m q)
      (fun s' m' => Rep o s' m' ∧ s'.count ≤ s.count + 1) := by
  have step (k : K) :
      SameOutcome (setindex o s () k) (.ok (rset o m k ()))
        (fun s' m' => Rep o s' m' ∧ s'.count ≤ s.count + 1) := by
    obtain ⟨s', hs, hr, -⟩ := h.setindex hl (by omega) k ()
    rw [hs]
    exact ⟨hr, by rw [hr.count_eq, h.count_eq]; exact rset_length_le o m k ()⟩
  cases hi : c.isa q with
  | some k =>
    simpa [pushConv, setindexConv, unionRefPush, hi] using step k
  | none =>
    cases he : c.convert q with
    | error e => simp [pushConv, setindexConv, unionRefPush, hi, he, SameOutcome]
    | ok k =>
      cases hq : c.iseq q k with
      | false =>
        simp only [pushConv, setindexConv, unionRefPush, hi, he, except_ok_bind, hq]
        rfl
      | true => simpa [pushConv, setindexConv, unionRefPush, hi, he, hq] using step k

theorem unionFold_spec {o : KeyOps K} (hl : o.Lawful) (c : Conv Q K) :
    ∀ (xs : List Q) (s : SetT K) (m : RMap K Unit), Rep o s m →
      s.count + xs.length ≤ 2 ^ 32 →
      SameOutcome (xs.foldlM (pushConv o c) s) (xs.foldlM (unionRefPush o c) m)
        (fun s' m' => Rep o s' m' ∧ s'.count ≤ s.count + xs.length)
  | [], s, m, hr, _ => ⟨hr, by simp⟩
  | q :: qs, s, m, hr, hc => by
    have hs := unionRefPush_spec hl c hr (by simp only [List.length_cons] at hc; omega) q
    cases hp : pushConv o c s q with
    | error e =>
      cases hq : unionRefPush o c m q with
      | error e' =>
        simp only [hp, hq, SameOutcome] at hs
        simp [List.foldlM_cons, hp, hq, SameOutcome, hs]
      | ok m' => simp [hp, hq, SameOutcome] at hs
    | ok s' =>
      cases hq : unionRefPush o c m q with
      | error e => simp [hp, hq, SameOutcome] at hs
      | ok m' =>
        simp only [hp, hq, SameOutcome] at hs
        have ih := unionFold_spec hl c qs s' m' hs.1 (by simp only [List.length_cons] at hc; omega)
        apply SameOutcome.mono (R := fun t r => Rep o t r ∧ t.count ≤ s'.count + qs.length)
          (by simpa [List.foldlM_cons, hp, hq] using ih)
        intro t r ht
        exact ⟨ht.1, by simp only [List.length_cons]; omega⟩

theorem unionRefFold_full {o : KeyOps K} (hl : o.Lawful) (c : Conv Q K)
    (cl : ConvLawful o c) (hsub : c.eltypeSubtype = true) :
    ∀ (xs : List Q) (m : RMap K Unit), (∀ x, (rfind o m x).isSome = true) →
      ∃ m', xs.foldlM (unionRefPush o c) m = .ok m' ∧
        ∀ x, (rfind o m' x).isSome = true
  | [], m, hm => ⟨m, rfl, hm⟩
  | q :: qs, m, hm => by
    obtain ⟨k, hk⟩ := cl.subtype_isa hsub q
    have hm' : ∀ x, (rfind o (rset o m k ()) x).isSome = true := by
      intro x
      rw [isSome_rfind_rset hl, hm x, Bool.or_true]
    obtain ⟨m', hf, hfull⟩ := unionRefFold_full hl c cl hsub qs (rset o m k ()) hm'
    refine ⟨m', ?_, hfull⟩
    simpa [List.foldlM_cons, unionRefPush, hk] using hf

theorem unionLoop_reference {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o)
    (c : Conv Q K) (cl : ConvLawful o c) :
    ∀ (xs : List Q) (s : SetT K) (m : RMap K Unit), Rep o s m →
      s.count + xs.length ≤ 2 ^ 32 →
      SameOutcome (unionLoop o c s xs) (xs.foldlM (unionRefPush o c) m)
        (fun s' m' => (∀ x, setIn o s' x = .ok (rfind o m' x).isSome) ∧
          s'.count ≤ s.count + xs.length)
  | [], s, m, hr, _ => ⟨fun x => setIn_of_rep hl hr x, by simp⟩
  | q :: qs, s, m, hr, hc => by
    have hs := unionRefPush_spec hl c hr (by simp only [List.length_cons] at hc; omega) q
    cases hp : pushConv o c s q with
    | error e =>
      cases hq : unionRefPush o c m q with
      | error e' =>
        simp only [hp, hq, SameOutcome] at hs
        simp [unionLoop, List.foldlM_cons, hp, hq, SameOutcome, hs]
      | ok m' => simp [hp, hq, SameOutcome] at hs
    | ok s' =>
      cases hq : unionRefPush o c m q with
      | error e => simp [hp, hq, SameOutcome] at hs
      | ok m' =>
        simp only [hp, hq, SameOutcome] at hs
        by_cases hexit : c.eltypeSubtype && ((s'.count : Int) == o.maxValues.val)
        · have hexit' : c.eltypeSubtype = true ∧ (s'.count : Int) = o.maxValues.val := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using hexit
          have hsub := hexit'.1
          have hcount := hexit'.2
          have hfull : ∀ x, (rfind o m' x).isSome = true := by
            cases hmv with
            | inl big => have := hs.2; simp only [List.length_cons] at hc; omega
            | inr finite =>
              apply full_reference_contains finite (hs.1.distinct hl)
              rw [← hs.1.count_eq]
              exact hcount
          obtain ⟨m'', hf, hfull'⟩ := unionRefFold_full hl c cl hsub qs m' hfull
          simp only [unionLoop, hp, except_ok_bind, hexit, ite_true,
            List.foldlM_cons, hq, hf, SameOutcome]
          refine ⟨?_, by simp only [List.length_cons]; omega⟩
          intro x
          rw [setIn_of_rep hl hs.1 x]
          change (Except.ok (rfind o m' x).isSome : DR Bool) = .ok (rfind o m'' x).isSome
          rw [hfull x, hfull' x]
        · have hcond : ¬ (c.eltypeSubtype = true ∧ (s'.count : Int) = o.maxValues.val) := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using hexit
          have ih := unionLoop_reference hl hmv c cl qs s' m' hs.1
            (by simp only [List.length_cons] at hc; omega)
          apply SameOutcome.mono (R := fun t r =>
            (∀ x, setIn o t x = .ok (rfind o r x).isSome) ∧ t.count ≤ s'.count + qs.length)
            (by simpa [unionLoop, hp, hcond, List.foldlM_cons, hq] using ih)
          intro t r ht
          exact ⟨ht.1, by simp only [List.length_cons]; omega⟩

set_option maxRecDepth 4096 in
theorem unionPushEquiv_thm : UnionPushEquiv := by
  intro K Q o c hl cl hmv s ms reach itr hlen
  have hreach := Reach.rep hl hmv reach
  have hr := hreach.1
  have hc := hreach.2
  have hhint := merge_hint hmv hr itr.length (by omega)
  let s1 := Classical.choose hhint
  have hhint' := Classical.choose_spec hhint
  have hh := hhint'.1
  have hr1 := hhint'.2.1
  have hc1 := hhint'.2.2.1
  change s1.count = s.count at hc1
  change sizehint o s (JInt.lit .i64 ((s.count : Int) + (itr.length : Int))) false = .ok s1 at hh
  have hu := unionLoop_reference hl hmv c cl itr s1 ms hr1 (by omega)
  have hf := unionFold_spec hl c itr s ms hr (by omega)
  unfold unionBang
  rw [hh, except_ok_bind]
  cases href : itr.foldlM (unionRefPush o c) ms with
  | error e =>
    cases hleft : unionLoop o c s1 itr <;> cases hright : itr.foldlM (pushConv o c) s <;>
      simp only [hleft, hright, href, SameOutcome] at hu hf ⊢ <;>
      first | exact False.elim hu | exact False.elim hf | exact hu.trans hf.symm
  | ok m =>
    cases hleft : unionLoop o c s1 itr <;> cases hright : itr.foldlM (pushConv o c) s <;>
      simp only [hleft, hright, href, SameOutcome] at hu hf ⊢ <;>
      first | exact False.elim hu | exact False.elim hf | skip
    intro x
    rw [hu.1 x, setIn_of_rep hl hf.1 x]
    rfl

/-- Without the subtype shortcut, union performs every insertion in order. -/
theorem unionLoop_nonSubtype (o : KeyOps K) (c : Conv Q K)
    (h : c.eltypeSubtype = false) :
    ∀ (xs : List Q) (s : SetT K),
      unionLoop o c s xs = xs.foldlM (pushConv o c) s := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    simp [unionLoop, h, List.foldlM_cons, ih]

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
    unionSet unionBang o s t = (elems t >>= fun xs => unionBang o (Conv.self o) s xs) := rfl

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

end JuliaLean.Dicts