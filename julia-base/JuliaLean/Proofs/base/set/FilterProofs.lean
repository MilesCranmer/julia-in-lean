import JuliaLean.Proofs.base.abstractset.ProofSetsLoop

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

/-- `filter!(keep, s)` on a set: the pairs whose key satisfies `p`. -/
theorem setFilterBang_spec {o : KeyOps K} (hl : o.Lawful) {keep : K → DR Bool} {p : K → Bool}
    (hk : ∀ x, keep x = .ok (p x)) {s : SetT K} (hi : Inv o s) :
    ∃ s', setFilterBang filterLoop o keep s = .ok s' ∧ Inv o s' ∧
      tlist s' = (tlist s).filter (fun e => p e.1) := by
  obtain ⟨T, h1, hS⟩ := filterLoop_spec hl hk s (s.size + 1) s.idxfloor s hi.idxfloor (by omega)
    (SInv.init hi)
  exact ⟨T, h1, hS.inv, hS.tlist_eq⟩

theorem setFilterBang_rep {o : KeyOps K} (hl : o.Lawful) {keep : K → DR Bool} {p : K → Bool}
    (hk : ∀ x, keep x = .ok (p x)) {s : SetT K} {m : RMap K Unit} (h : Rep o s m) :
    ∃ s', setFilterBang filterLoop o keep s = .ok s' ∧ Rep o s' (m.filter (fun e => p e.1)) := by
  obtain ⟨s', h1, hi, ht⟩ := setFilterBang_spec hl hk h.1
  exact ⟨s', h1, hi, by rw [ht]; exact h.2.filter _⟩

end JuliaLean.Dicts.SetProofs
