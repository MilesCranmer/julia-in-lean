import JuliaLean.Dicts.ProofSetsRef
import JuliaLean.Dicts.ProofSetsLoop
import JuliaLean.Dicts.ProofBulk

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
    ∃ s', unionSet o s t = .ok s' ∧
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
    ∃ s', unionSet o s t = .ok s' ∧
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

/-! ## `setdiff!` -/

theorem deleteFold_spec {o : KeyOps K} (hl : o.Lawful) :
    ∀ (xs : List K) (s : SetT K) (m : RMap K Unit), Rep o s m →
      ∃ s', xs.foldlM (fun s x => setDelete o s x) s = .ok s' ∧
        Rep o s' (xs.foldl (fun m x => rdel o m x) m)
  | [], s, _, h => ⟨s, rfl, h⟩
  | x :: xs, s, m, h => by
    obtain ⟨s1, h1, hr1, -⟩ := h.dictDelete hl x
    obtain ⟨s', h2, hr'⟩ := deleteFold_spec hl xs s1 _ hr1
    refine ⟨s', ?_, hr'⟩
    show (setDelete o s x >>= fun s => xs.foldlM (fun s x => setDelete o s x) s) = _
    rw [show setDelete o s x = .ok s1 from h1]
    exact h2

theorem setdiff_rep {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) :
    ∃ s', setdiffBang o s t = .ok s' ∧ Rep o s' (ms.filter fun e => !rmem o mt e.1) := by
  unfold setdiffBang
  by_cases hb : 2 * s.count < t.count
  · rw [if_pos hb]
    exact setFilterBang_rep hl (p := fun x => !rmem o mt x) (fun x => by
      show (setIn o t x >>= fun b => pure (!b)) = _
      rw [rep_setIn hl ht x] <;> rfl) hs
  · rw [if_neg hb, elems_eq ht.1]
    obtain ⟨s', h1, hr⟩ := deleteFold_spec hl ((tlist t).map (·.1)) s ms hs
    refine ⟨s', h1, ?_⟩
    rw [foldl_map_fst, rdel_fold hl, filter_notin_perm ht.2 ms] at hr
    exact hr

theorem setSetdiff_main {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) :
    ∃ s', setdiffBang o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => !rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && !rmem o mt x) := by
  obtain ⟨s', h1, hr⟩ := setdiff_rep hl hs ht
  exact ⟨s', h1, hr.agrees hl, fun x => by rw [rep_setIn hl hr x, rmem_diff hl ms mt x]⟩

/-! ## `symdiff!` -/

/-- The loop body of `symdiff!`, `base/abstractset.jl:301-303`. -/
def symStep (o : KeyOps K) (s : SetT K) (x : K) : DR (SetT K) := do
  if ← setIn o s x then setDelete o s x else push o s x

theorem symFold_spec {o : KeyOps K} (hl : o.Lawful) :
    ∀ (xs : List K) (s : SetT K) (m : RMap K Unit), Rep o s m → m.length + xs.length ≤ 2 ^ 32 →
      ∃ s', xs.foldlM (symStep o) s = .ok s' ∧ Rep o s' (xs.foldl (fun m x => rsym o m x) m)
  | [], s, _, h, _ => ⟨s, rfl, h⟩
  | x :: xs, s, m, h, hb => by
    have hlen : m.length + 1 + xs.length ≤ 2 ^ 32 := by
      rw [List.length_cons] at hb
      omega
    have hc : s.count < 2 ^ 33 := by rw [rep_count h]; omega
    have hstep : ∃ s1, symStep o s x = .ok s1 ∧ Rep o s1 (rsym o m x) ∧
        (rsym o m x).length ≤ m.length + 1 := by
      cases hm : rmem o m x with
      | true =>
        obtain ⟨s1, h1, hr1, -⟩ := h.dictDelete hl x
        refine ⟨s1, ?_, by rw [rsym_of_mem hm]; exact hr1, ?_⟩
        · show (setIn o s x >>= fun c => if c = true then setDelete o s x else push o s x) = _
          rw [rep_setIn hl h x, hm, bind_ite_true]
          exact h1
        · rw [rsym_of_mem hm]
          have := rdel_length_le o m x
          omega
      | false =>
        obtain ⟨s1, h1, hr1, -⟩ := h.setindex hl hc x ()
        refine ⟨s1, ?_, by rw [rsym_of_not_mem hm]; exact hr1, ?_⟩
        · show (setIn o s x >>= fun c => if c = true then setDelete o s x else push o s x) = _
          rw [rep_setIn hl h x, hm, bind_ite_false]
          exact h1
        · rw [rsym_of_not_mem hm]
          exact rset_length_le o m x
    obtain ⟨s1, h1, hr1, hl1⟩ := hstep
    obtain ⟨s', h2, hr'⟩ := symFold_spec hl xs s1 _ hr1 (by omega)
    refine ⟨s', ?_, hr'⟩
    show (symStep o s x >>= fun s => xs.foldlM (symStep o) s) = _
    rw [h1]
    exact h2

theorem setSymdiff_main {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) (hcs : s.count ≤ 2 ^ 30) (hct : t.count ≤ 2 ^ 30) :
    ∃ s', symdiffBang o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => if rmem o m e.1 then rdel o m e.1 else rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x != rmem o mt x) := by
  obtain ⟨s', h1, hr⟩ := symFold_spec hl ((tlist t).map (·.1)) s ms hs
    (by rw [List.length_map, ← ht.1.count, ← rep_count hs]; omega)
  rw [foldl_map_fst] at hr
  have hdm := rep_distinct hl ht
  have hp : List.Perm ((tlist t).foldl (fun m e => rsym o m e.1) ms)
      (mt.foldl (fun m e => rsym o m e.1) ms) := by
    refine (symdiff_fold hl _ ms (tlist_pairwise ht.1)).trans
      (List.Perm.trans ?_ (symdiff_fold hl _ ms hdm).symm)
    rw [filter_notin_perm ht.2 ms]
    exact List.Perm.append (List.Perm.refl _) (ht.2.filter _)
  have hr' := rep_perm hr hp
  refine ⟨s', ?_, hr'.agrees hl, fun x => ?_⟩
  · unfold symdiffBang
    rw [elems_eq ht.1]
    exact h1
  · rw [rep_setIn hl hr' x, rmem_perm (symdiff_fold hl mt ms hdm) x, rmem_symdiff hl ms mt x]

/-! ## `issubset` and `==` -/

theorem allIn_eq {o : KeyOps K} (hl : o.Lawful) {t : SetT K} {mt : RMap K Unit} (ht : Rep o t mt) :
    ∀ xs : List K, allIn o t xs = .ok (xs.all (fun x => rmem o mt x))
  | [] => rfl
  | x :: xs => by
    show (setIn o t x >>= fun c => if c = true then allIn o t xs else pure false) = _
    rw [rep_setIn hl ht x, List.all_cons]
    cases rmem o mt x
    · rw [bind_ite_false, Bool.false_and] <;> rfl
    · rw [bind_ite_true, Bool.true_and]
      exact allIn_eq hl ht xs

theorem issubsetSet_eq (o : KeyOps K) (a b : SetT K) :
    issubsetSet o a b =
      if a.count > b.count then pure false else (elems a >>= fun xs => allIn o b xs) := rfl

theorem setEq_eq (o : KeyOps K) (a b : SetT K) :
    setEq o a b = if (a.count == b.count) = true then issubsetSet o a b else pure false := rfl

theorem issubset_main {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) :
    issubsetSet o s t = .ok (ms.all fun e => rmem o mt e.1) := by
  rw [issubsetSet_eq]
  by_cases hgt : s.count > t.count
  · rw [if_pos hgt]
    cases hall : ms.all (fun e => rmem o mt e.1)
    · rfl
    · exfalso
      have := pigeon hl ms mt (rep_distinct hl hs) (fun a ha => List.all_eq_true.1 hall a ha)
      rw [rep_count hs, rep_count ht] at hgt
      omega
  · rw [if_neg hgt, elems_eq hs.1]
    show allIn o t ((tlist s).map (·.1)) = _
    rw [allIn_eq hl ht, all_map_fst, perm_all hs.2]

theorem setEq_main {o : KeyOps K} (hl : o.Lawful) {s t : SetT K} {ms mt : RMap K Unit}
    (hs : Rep o s ms) (ht : Rep o t mt) :
    setEq o s t = .ok ((ms.all fun e => rmem o mt e.1) && (mt.all fun e => rmem o ms e.1)) := by
  rw [setEq_eq]
  by_cases hc : s.count = t.count
  · rw [if_pos (beq_iff_eq.2 hc), issubset_main hl hs ht]
    cases hall : ms.all (fun e => rmem o mt e.1)
    · rfl
    · rw [all_rev hl (rep_distinct hl hs) (by rw [← rep_count hs, ← rep_count ht]; exact hc) hall]
        <;> rfl
  · rw [if_neg (by rw [beq_iff_eq]; exact hc)]
    cases h1 : ms.all (fun e => rmem o mt e.1)
    · rfl
    · cases h2 : mt.all (fun e => rmem o ms e.1)
      · rfl
      · exfalso
        have l1 := pigeon hl ms mt (rep_distinct hl hs) (fun a ha => List.all_eq_true.1 h1 a ha)
        have l2 := pigeon hl mt ms (rep_distinct hl ht) (fun a ha => List.all_eq_true.1 h2 a ha)
        rw [rep_count hs, rep_count ht] at hc
        omega

end JuliaLean.Dicts.SetProofs
