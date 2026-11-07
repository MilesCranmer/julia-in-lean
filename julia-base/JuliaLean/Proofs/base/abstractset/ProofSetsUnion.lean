import JuliaLean.Proofs.base.abstractset.ProofSetsRef
import JuliaLean.Proofs.base.set.FilterProofs
import JuliaLean.Proofs.base.dict.ProofBulk

/-!
# `union!`, `intersect!`, `setdiff!`, `symdiff!`, `issubset` and `==` on sets

Each operation on tables representing reference sets `ms` and `mt` (with
small counts where the operation inserts) returns a table representing the
reference result, and the membership tests agree with it.
-/

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

/-! ## Common facts -/

theorem typemax_i64_val : (JInt.typemax .i64).val = 2 ^ 63 - 1 := by
  have h := i64_max
  have e : (JInt.typemax .i64).val = IntTy.max .i64 :=
    wrap_i64_val (by rw [h]; omega) (by rw [h]; omega)
  rw [e, h]

theorem genericMax_ok {o : KeyOps K} (h : GenericMax o) : MaxValuesOK o := by
  refine Or.inl ?_
  have e : o.maxValues = JInt.typemax .i64 := h
  rw [e, typemax_i64_val]
  omega

theorem rep_count {o : KeyOps K} {t : SetT K} {m : RMap K Unit} (h : Rep o t m) :
    t.count = m.length := by
  rw [h.1.count, h.2.length_eq]

theorem rep_distinct {o : KeyOps K} (hl : o.Lawful) {t : SetT K} {m : RMap K Unit}
    (h : Rep o t m) : Distinct o m :=
  Distinct.perm hl (tlist_pairwise h.1) h.2

theorem rep_setIn {o : KeyOps K} (hl : o.Lawful) {t : SetT K} {m : RMap K Unit} (h : Rep o t m)
    (x : K) : setIn o t x = .ok (rmem o m x) :=
  h.haskey_eq hl x

theorem rep_perm {o : KeyOps K} {t : SetT K} {m m' : RMap K Unit} (h : Rep o t m)
    (hp : List.Perm m m') : Rep o t m' :=
  ⟨h.1, h.2.trans hp⟩

theorem elems_eq {o : KeyOps K} {t : SetT K} (hi : Inv o t) :
    elems t = .ok ((tlist t).map (·.1)) := by
  unfold elems
  rw [iterList_eq hi] <;> rfl

theorem bind_ite_true {α : Type} (a b : DR α) :
    ((Except.ok true : DR Bool) >>= fun c => if c = true then a else b) = a := rfl

theorem bind_ite_false {α : Type} (a b : DR α) :
    ((Except.ok false : DR Bool) >>= fun c => if c = true then a else b) = b := rfl

/-- The key filter of a reference set only depends on its members. -/
theorem filter_notin_perm {o : KeyOps K} {L L' : RMap K Unit} (h : List.Perm L L')
    (m : RMap K Unit) :
    m.filter (fun b => !rmem o L b.1) = m.filter (fun b => !rmem o L' b.1) :=
  List.filter_congr (fun b _ => by
    show (!rmem o L b.1) = !rmem o L' b.1
    rw [rmem_perm h b.1])

/-! ## `union!` -/

theorem unionLoop_spec {o : KeyOps K} (hl : o.Lawful) (hgm : GenericMax o) :
    ∀ (xs : List K) (s : SetT K) (m : RMap K Unit), Rep o s m → m.length + xs.length ≤ 2 ^ 32 →
      ∃ s', unionLoop o (Conv.self o) s xs = .ok s' ∧
        Rep o s' (xs.foldl (fun m x => rset o m x ()) m)
  | [], s, _, h, _ => ⟨s, rfl, h⟩
  | x :: xs, s, m, h, hb => by
    have hlen : m.length + 1 + xs.length ≤ 2 ^ 32 := by
      rw [List.length_cons] at hb
      omega
    have hc : s.count < 2 ^ 33 := by rw [rep_count h]; omega
    obtain ⟨s1, h1, hr1, -⟩ := h.setindex hl hc x ()
    have hl1 := rset_length_le o m x
    have hmax : o.maxValues = JInt.typemax .i64 := hgm
    have hne : ((s1.count : Int) == o.maxValues.val) = false := by
      rw [beq_eq_false_iff_ne, hmax, typemax_i64_val, rep_count hr1]
      omega
    have e : unionLoop o (Conv.self o) s (x :: xs) = unionLoop o (Conv.self o) s1 xs := by
      show (setindex o s () x >>= fun s => if ((s.count : Int) == o.maxValues.val) = true then pure s
        else unionLoop o (Conv.self o) s xs) = _
      rw [h1]
      show (if ((s1.count : Int) == o.maxValues.val) = true then pure s1
        else unionLoop o (Conv.self o) s1 xs) = _
      rw [hne] <;> rfl
    rw [e]
    exact unionLoop_spec hl hgm xs s1 (rset o m x ()) hr1 (by omega)

theorem unionSet_rep {o : KeyOps K} (hl : o.Lawful) (hgm : GenericMax o) {s t : SetT K}
    {ms mt : RMap K Unit} (hs : Rep o s ms) (ht : Rep o t mt) (hcs : s.count ≤ 2 ^ 30)
    (hct : t.count ≤ 2 ^ 30) :
    ∃ s', unionSet unionBang o s t = .ok s' ∧
      Rep o s' ((tlist t).foldl (fun m e => rset o m e.1 ()) ms) := by
  obtain ⟨xs, hel, hxs⟩ : ∃ xs, elems t = .ok xs ∧ xs = (tlist t).map (·.1) :=
    ⟨_, elems_eq ht.1, rfl⟩
  have hxl : xs.length = t.count := by rw [hxs, List.length_map, ht.1.count]
  have hn : (JInt.lit .i64 (s.count + xs.length)).val ≤ 2 ^ 61 := by
    rw [lit_i64_val (by omega) (by omega)]
    omega
  obtain ⟨s1, h1, hi1, hp1, -, -⟩ :=
    sizehint_spec (genericMax_ok hgm) hs.1 (by omega) (JInt.lit .i64 (s.count + xs.length)) hn false
  obtain ⟨s', h2, hr'⟩ := unionLoop_spec hl hgm xs s1 ms ⟨hi1, hp1.trans hs.2⟩
    (by rw [← rep_count hs]; omega)
  refine ⟨s', ?_, ?_⟩
  · unfold unionSet
    rw [hel, except_ok_bind]
    unfold unionBang
    rw [h1, except_ok_bind]
    exact h2
  · rw [hxs, foldl_map_fst] at hr'
    exact hr'

theorem setUnion_main {o : KeyOps K} (hl : o.Lawful) (hgm : GenericMax o) {s t : SetT K}
    {ms mt : RMap K Unit} (hs : Rep o s ms) (ht : Rep o t mt) (hcs : s.count ≤ 2 ^ 30)
    (hct : t.count ≤ 2 ^ 30) :
    ∃ s', unionSet unionBang o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x || rmem o mt x) := by
  obtain ⟨s', h1, hr⟩ := unionSet_rep hl hgm hs ht hcs hct
  have hdm := rep_distinct hl ht
  have hp : List.Perm ((tlist t).foldl (fun m e => rset o m e.1 ()) ms)
      (mt.foldl (fun m e => rset o m e.1 ()) ms) := by
    refine (union_fold hl _ ms (tlist_pairwise ht.1)).trans
      (List.Perm.trans ?_ (union_fold hl _ ms hdm).symm)
    rw [filter_notin_perm ht.2 ms]
    exact List.Perm.append ht.2 (List.Perm.refl _)
  have hr' := rep_perm hr hp
  refine ⟨s', h1, hr'.agrees hl, fun x => ?_⟩
  rw [rep_setIn hl hr' x, rmem_perm (union_fold hl mt ms hdm) x, rmem_union hl ms mt x]

/-! ## `intersect!` -/

theorem setIntersect_main {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) :
    ∃ s', intersectBang o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && rmem o mt x) := by
  obtain ⟨s', h1, hr⟩ := setFilterBang_rep hl (keep := fun x => setIn o t x) (p := rmem o mt)
    (fun x => rep_setIn hl ht x) hs
  refine ⟨s', h1, hr.agrees hl, fun x => ?_⟩
  rw [rep_setIn hl hr x, rmem_inter hl ms mt x]

end JuliaLean.Dicts.SetProofs