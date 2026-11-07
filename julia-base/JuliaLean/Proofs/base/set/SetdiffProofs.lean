import JuliaLean.Proofs.base.abstractset.ProofSetsUnion
import JuliaLean.Proofs.base.set.FilterProofs

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

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
    ∃ s', setdiffBang filterLoop o s t = .ok s' ∧ Rep o s' (ms.filter fun e => !rmem o mt e.1) := by
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
    ∃ s', setdiffBang filterLoop o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => !rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && !rmem o mt x) := by
  obtain ⟨s', h1, hr⟩ := setdiff_rep hl hs ht
  exact ⟨s', h1, hr.agrees hl, fun x => by rw [rep_setIn hl hr x, rmem_diff hl ms mt x]⟩

end JuliaLean.Dicts.SetProofs
