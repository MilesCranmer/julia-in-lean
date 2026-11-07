import JuliaLean.Proofs.base.multidimensional.cartesian_contracts
import JuliaLean.Proofs.base.tuple.cartesian_order
import JuliaLean.Proofs.base.abstractarray.cartesian_shapes

namespace JuliaLean.Multidim

namespace SmallAux

/-! ## `reverse(::CartesianIndices; dims)` -/

theorem nodup_iff_count (l : List Int) : l.Nodup ↔ ∀ a, l.count a ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.nodup_cons, ih]
    constructor
    · rintro ⟨hb, h⟩ a
      rw [List.count_cons]
      by_cases hab : b = a
      · subst hab; rw [List.count_eq_zero_of_not_mem hb]; simp
      · have := h a
        rw [if_neg (by simpa using hab)]; omega
    · intro h
      refine ⟨fun hb => ?_, fun a => ?_⟩
      · have h1 := h b
        have h2 := List.count_pos_iff.mpr hb
        rw [List.count_cons, if_pos (beq_self_eq_true b)] at h1
        omega
      · have h1 := h a
        rw [List.count_cons] at h1
        split at h1 <;> omega

theorem filter_len_succ (l : List Int) (N : Nat) :
    (l.filter fun d => decide (1 ≤ d ∧ d ≤ ((N + 1 : Nat) : Int))).length =
      (l.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length + l.count ((N : Int) + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.count_cons, decide_eq_true_eq, beq_iff_eq]
    split <;> split <;> split <;> (try simp only [List.length_cons]) <;> omega

theorem filter_length_eq_iff {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length ≤ l.length ∧ ((l.filter p).length = l.length ↔ ∀ x ∈ l, p x = true)
  | [] => by simp
  | a :: l => by
    obtain ⟨h1, h2⟩ := filter_length_eq_iff p l
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.forall_mem_cons]
      simp only [List.length_cons, ha, true_and]
      refine ⟨by omega, ?_⟩
      rw [← h2]
      constructor <;> intro h <;> omega
    · rw [List.filter_cons_of_neg ha, List.forall_mem_cons]
      simp only [List.length_cons]
      exact ⟨by omega, fun h => by omega, fun h => absurd h.1 ha⟩

theorem once_le (dims : List Int) : ∀ N : Nat,
    ((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true ≤
      (dims.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length ∧
    (((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true =
      (dims.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length ↔
      ∀ i < N, dims.count ((i : Int) + 1) ≤ 1)
  | 0 => by
    have h0 : (dims.filter fun d => decide (1 ≤ d ∧ d ≤ ((0 : Nat) : Int))) = [] :=
      List.filter_eq_nil_iff.mpr fun a _ => by simp only [decide_eq_true_eq]; omega
    rw [h0]; simp
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := once_le dims N
    have hA : ((List.range (N + 1)).map fun (i : Nat) =>
          decide (dims.count ((i : Int) + 1) = 1)).count true =
        ((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true +
          (if dims.count ((N : Int) + 1) = 1 then 1 else 0) := by
      by_cases hc : dims.count ((N : Int) + 1) = 1 <;>
        simp [List.range_succ, List.count_append, hc]
    rw [hA, filter_len_succ]
    refine ⟨by split <;> omega, ⟨fun h i hi => ?_, fun h => ?_⟩⟩
    · rcases Nat.lt_or_ge i N with hi' | hi'
      · exact ih2.mp (by split at h <;> omega) i hi'
      · have : i = N := by omega
        subst this
        split at h <;> omega
    · have e1 := ih2.mpr (fun i hi => h i (by omega))
      have e2 := h N (by omega)
      split <;> omega

end SmallAux

open SmallAux

theorem cartesianIslessOrder : CartesianIslessOrder := by
  intro a b c hab hbc
  unfold ciLess
  refine ⟨tupleLess_irrefl _, tupleLess_trans _ _ _, ?_⟩
  rcases tupleLess_total a.reverse b.reverse (by simp [hab]) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (List.reverse_inj.mp h))
  · exact Or.inr (Or.inr h)

theorem reverseDimsCheck : ReverseDimsCheck := by
  intro N dims
  obtain ⟨hle, heq⟩ := once_le dims N
  obtain ⟨fle, feq⟩ := filter_length_eq_iff (fun d => decide (1 ≤ d ∧ d ≤ (N : Int))) dims
  simp only [reverseDimsOk, beq_iff_eq]
  constructor
  · intro h
    have hA := heq.mp (by omega)
    have hF := feq.mp (by omega)
    have hR : ∀ d ∈ dims, 1 ≤ d ∧ d ≤ (N : Int) := fun d hd => by simpa using hF d hd
    refine ⟨(nodup_iff_count dims).mpr fun a => ?_, hR⟩
    by_cases ha : a ∈ dims
    · have h1 := hR a ha
      have h2 := hA (a.toNat - 1) (by omega)
      have e : ((a.toNat - 1 : Nat) : Int) + 1 = a := by omega
      rwa [e] at h2
    · rw [List.count_eq_zero_of_not_mem ha]; omega
  · rintro ⟨hnd, hR⟩
    have hF := feq.mpr (fun d hd => by simpa using hR d hd)
    have hA := heq.mpr (fun i _ => (nodup_iff_count dims).mp hnd _)
    omega

theorem diffSize_spec : DiffSize := by
  intro sz dims
  by_cases h1 : 1 ≤ dims
  · by_cases h2 : dims ≤ (sz.length : Int)
    · rw [if_pos ⟨h1, h2⟩]
      have hr : ((List.range sz.length).map fun (i : Nat) =>
          if (i : Int) + 1 = dims then ((sz.getD i 0 : Int) - 1 - 1 + 1).toNat else sz.getD i 0) =
          ((List.range sz.length).map fun (i : Nat) =>
          if (i : Int) + 1 = dims then ((sz.getD i 0 : Int) - 2 + 1).toNat else sz.getD i 0) := by
        congr 1; funext i; split <;> omega
      have hs : ((List.range sz.length).map fun (i : Nat) =>
          if (i : Int) + 1 = dims then ((sz.getD i 0 : Int) - 2 + 1).toNat else sz.getD i 0) =
          sz.set (dims.toNat - 1) (sz.getD (dims.toNat - 1) 0 - 1) := by
        apply List.ext_getElem
        · simp
        · intro n hn1 hn2
          have hn : n < sz.length := by simpa using hn1
          simp only [List.getElem_map, List.getElem_range, List.getElem_set]
          by_cases hk : (n : Int) + 1 = dims
          · have hk' : dims.toNat - 1 = n := by omega
            simp [hk, hk', List.getD_eq_getElem?_getD, hn] <;> omega
          · have hk' : ¬ dims.toNat - 1 = n := by omega
            simp [hk, hk', List.getD_eq_getElem?_getD, hn]
      unfold diffSize
      rw [hr, hs]
      simp [h1, h2, pure, Except.pure]
    · rw [if_neg (fun h => h2 h.2)]
      simp [diffSize, h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · rw [if_neg (fun h => h1 h.1)]
    simp [diffSize, h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

end JuliaLean.Multidim
