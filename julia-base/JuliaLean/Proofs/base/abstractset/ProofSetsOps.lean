import JuliaLean.Proofs.base.set.SetdiffProofs

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

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
