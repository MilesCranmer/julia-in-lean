import JuliaLean.Proofs.base.abstractset.SetLoops

namespace JuliaLean.Dicts

variable {K Q : Type}

theorem setFilterBang_spec {o : KeyOps K} (hl : o.Lawful) {s : SetT K} {m : RMap K Unit}
    (h : Rep o s m) (keep : K → DR Bool) (kb : K → Bool) (hk : ∀ x, keep x = .ok (kb x)) :
    ∃ s', setFilterBang filterLoop o keep s = .ok s' ∧ Rep o s' (m.filter fun e => kb e.1) := by
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

end JuliaLean.Dicts
