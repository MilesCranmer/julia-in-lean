import JuliaLean.Proofs.base.set.Algebra

namespace JuliaLean.Dicts

variable {K Q : Type}

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
