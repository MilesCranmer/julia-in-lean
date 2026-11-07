import JuliaLean.base.permuteddimsarray

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `PermutedDimsArray(A, perm)` is constructed exactly when `perm` is a permutation of `1:N`, and then
`B[I...]` reads `A[J...]` with `J[perm[d]] == I[d]`, in bounds whenever `I` is in bounds of
`size(B) = genperm(size(A), perm)`. -/
def PermutedCorrect : Prop :=
  ∀ (perm : List Int) (dims : List Int), perm.length = dims.length →
    (isperm perm = false → ∃ e, pdaNew perm dims.length = .error e) ∧
    (isperm perm = true → ∃ iperm, pdaNew perm dims.length = .ok iperm ∧
      ∀ I : List Int, I.length = dims.length →
        (∀ p ∈ I.zip (genperm dims perm), 1 ≤ p.1 ∧ p.1 ≤ p.2) →
        let J := genperm I iperm
        J.length = dims.length ∧ (∀ p ∈ J.zip dims, 1 ≤ p.1 ∧ p.1 ≤ p.2) ∧
        ∀ d < dims.length, J.getD ((perm.getD d 0) - 1).toNat 0 = I.getD d 0)
/-! ### `PermutedDimsArray` -/

/-- The loop body of `invperm`, `base/combinatorics.jl:286-296`. -/
private def invStep (n : Nat) (b : List Int) (p : Int × Nat) : Jl (List Int) :=
  let (j, i) := p
  if 1 ≤ j ∧ j ≤ n ∧ b.getD (j - 1).toNat 0 = 0 then .ok (b.set (j - 1).toNat i)
  else .error (.argumentError "argument is not a permutation")

private theorem invperm_eq (a : List Int) :
    invperm a = (a.zipIdx 1).foldlM (invStep a.length) (List.replicate a.length 0) := rfl

private theorem getD_replicate_zero (n j : Nat) : (List.replicate n (0 : Int)).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

private theorem invFold (n : Nat) : ∀ (xs : List Int) (k : Nat) (b : List Int), b.length = n →
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ n) → xs.Nodup → (∀ x ∈ xs, b.getD (x - 1).toNat 0 = 0) →
    ∃ b', (xs.zipIdx k).foldlM (invStep n) b = .ok b' ∧ b'.length = n ∧
      (∀ j, (∀ y ∈ xs, (y - 1).toNat ≠ j) → b'.getD j 0 = b.getD j 0) ∧
      ∀ i < xs.length, b'.getD ((xs.getD i 0) - 1).toNat 0 = ((k + i : Nat) : Int)
  | [], _, b, hb, _, _, _ => ⟨b, rfl, hb, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | x :: xs, k, b, hb, hr, hnd, hz => by
    have hx := hr x List.mem_cons_self
    have hbx := hz x List.mem_cons_self
    obtain ⟨hxn, hnd⟩ := List.nodup_cons.mp hnd
    have hstep : invStep n b (x, k) = .ok (b.set (x - 1).toNat (k : Int)) := by
      have e : invStep n b (x, k) = if 1 ≤ x ∧ x ≤ n ∧ b.getD (x - 1).toNat 0 = 0 then
          .ok (b.set (x - 1).toNat (k : Int)) else .error (.argumentError "argument is not a permutation") :=
        rfl
      rw [e, ite_eq_left ⟨hx.1, hx.2, hbx⟩]
    have hb1 : (b.set (x - 1).toNat (k : Int)).length = n := by rw [List.length_set, hb]
    have hne : ∀ y ∈ xs, (y - 1).toNat ≠ (x - 1).toNat := fun y hy h0 => by
      have hy1 := (hr y (List.mem_cons_of_mem _ hy)).1
      have hyx : y = x := by omega
      exact hxn (hyx ▸ hy)
    have hb1get : ∀ j, j ≠ (x - 1).toNat → (b.set (x - 1).toNat (k : Int)).getD j 0 = b.getD j 0 := by
      intro j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
    have hz1 : ∀ y ∈ xs, (b.set (x - 1).toNat (k : Int)).getD (y - 1).toNat 0 = 0 := fun y hy => by
      rw [hb1get _ (hne y hy)]
      exact hz y (List.mem_cons_of_mem _ hy)
    obtain ⟨b', hf, hl, hag, hval⟩ := invFold n xs (k + 1) _ hb1
      (fun y hy => hr y (List.mem_cons_of_mem _ hy)) hnd hz1
    refine ⟨b', ?_, hl, ?_, ?_⟩
    · show (invStep n b (x, k) >>= fun b'' => (xs.zipIdx (k + 1)).foldlM (invStep n) b'') = .ok b'
      rw [hstep]
      exact hf
    · intro j hj
      rw [hag j (fun y hy => hj y (List.mem_cons_of_mem _ hy)),
        hb1get j (fun h0 => hj x List.mem_cons_self h0.symm)]
    · intro i hi
      cases i with
      | zero =>
        show b'.getD (x - 1).toNat 0 = ((k + 0 : Nat) : Int)
        rw [hag _ (fun y hy => hne y hy)]
        have hlt : (x - 1).toNat < b.length := by rw [hb]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt]
        rfl
      | succ i =>
        show b'.getD ((xs.getD i 0) - 1).toNat 0 = ((k + (i + 1) : Nat) : Int)
        rw [hval i (by simpa using hi)]
        omega

/-- The list `[1, 2, ..., n]`. -/
private def iota1 (n : Nat) : List Int := (List.range n).map (fun k : Nat => (k : Int) + 1)

private theorem mem_iota1 {n : Nat} {y : Int} (h : y ∈ iota1 n) : 1 ≤ y ∧ y ≤ n := by
  unfold iota1 at h
  rw [List.mem_map] at h
  obtain ⟨k, hk, hky⟩ := h
  rw [List.mem_range] at hk
  omega

private theorem iota1_nodup (n : Nat) : (iota1 n).Nodup := by
  unfold iota1 List.Nodup
  exact List.Pairwise.map _ (fun a b hab heq => hab (by
    have h' : (a : Int) + 1 = (b : Int) + 1 := heq
    omega)) List.nodup_range

private theorem isperm_mem {p : List Int} (h : isperm p = true) : ∀ k < p.length, ((k : Int) + 1) ∈ p := by
  intro k hk
  unfold isperm at h
  have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have hc : p.count ((k : Int) + 1) = 1 := of_decide_eq_true h1
  exact List.count_pos_iff.mp (by omega)

private theorem isperm_range {p : List Int} (h : isperm p = true) : ∀ x ∈ p, 1 ≤ x ∧ x ≤ p.length := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  have hxL : x ∉ iota1 p.length := fun hm => hn (mem_iota1 hm)
  have hsub : (x :: iota1 p.length) ⊆ p := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · unfold iota1 at hy
      rw [List.mem_map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact isperm_mem h k (List.mem_range.mp hk)
  have hle := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hxL, iota1_nodup _⟩) hsub
  have hl : (x :: iota1 p.length).length = p.length + 1 := by simp [iota1]
  omega

private theorem isperm_nodup {p : List Int} (h : isperm p = true) : p.Nodup := by
  rw [List.nodup_iff_count]
  intro a
  by_cases ha : a ∈ p
  · have hr := isperm_range h a ha
    have h' := h
    unfold isperm at h'
    have h1 := List.all_eq_true.mp h' (a - 1).toNat (List.mem_range.mpr (by omega))
    have hc : p.count (((a - 1).toNat : Int) + 1) = 1 := of_decide_eq_true h1
    have he : (((a - 1).toNat : Int) + 1) = a := by omega
    rw [he] at hc
    omega
  · rw [List.count_eq_zero_of_not_mem ha]
    omega

private theorem mem_getD {l : List Int} {x : Int} (h : x ∈ l) : ∃ d < l.length, l.getD d 0 = x := by
  obtain ⟨d, hd, hx⟩ := List.mem_iff_getElem.mp h
  refine ⟨d, hd, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]
  exact hx

private theorem getD_mem {l : List Int} {d : Nat} (h : d < l.length) : l.getD d 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

private theorem genperm_length (I perm : List Int) : (genperm I perm).length = perm.length := by
  simp [genperm]

private theorem genperm_getD (I perm : List Int) (k : Nat) (hk : k < perm.length) :
    (genperm I perm).getD k 0 = I.getD ((perm.getD k 0) - 1).toNat 0 := by
  simp [genperm, List.getElem?_eq_getElem hk] <;> rfl

private theorem forall_zip_getD : ∀ (l₁ l₂ : List Int), l₁.length = l₂.length →
    ((∀ p ∈ l₁.zip l₂, 1 ≤ p.1 ∧ p.1 ≤ p.2) ↔
      ∀ k < l₁.length, 1 ≤ l₁.getD k 0 ∧ l₁.getD k 0 ≤ l₂.getD k 0)
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    have ih := forall_zip_getD l₁ l₂ (by simpa using h)
    constructor
    · intro hz k hk
      cases k with
      | zero => exact hz (a, b) List.mem_cons_self
      | succ k =>
        exact (ih.mp (fun p hp => hz p (List.mem_cons_of_mem _ hp))) k (by simpa using hk)
    · intro hk p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hk 0 (by simp)
      · exact ih.mpr (fun k hk' => hk (k + 1) (by simpa using hk')) p hp

theorem permutedCorrect : PermutedCorrect := by
  intro perm dims hlen
  refine ⟨fun hf => ?_, fun hp => ?_⟩
  · cases hi : invperm perm with
    | error e =>
      refine ⟨e, ?_⟩
      simp only [pdaNew, hlen, ne_eq, not_true_eq_false, reduceIte, hi, bind, Except.bind]
    | ok ip =>
      refine ⟨.argumentError "not a valid permutation", ?_⟩
      simp only [pdaNew, hlen, ne_eq, not_true_eq_false, reduceIte, hi, hf, Bool.not_false, bind,
        Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have hrange := isperm_range hp
    have hnd := isperm_nodup hp
    obtain ⟨ip, hfold, hiplen, -, hval⟩ := invFold perm.length perm 1 (List.replicate perm.length 0)
      List.length_replicate hrange hnd (fun _ _ => getD_replicate_zero _ _)
    have hinv : invperm perm = .ok ip := by rw [invperm_eq]; exact hfold
    have hval' : ∀ d < perm.length, ip.getD ((perm.getD d 0) - 1).toNat 0 = (d : Int) + 1 := by
      intro d hd
      rw [hval d hd]
      omega
    have hc : (List.range perm.length).all
        (fun d => decide (ip.getD ((perm.getD d 0) - 1).toNat 0 = (d : Int) + 1)) = true :=
      List.all_eq_true.mpr (fun d hd => decide_eq_true (hval' d (List.mem_range.mp hd)))
    refine ⟨ip, ?_, ?_⟩
    · rw [← hlen]
      simp only [pdaNew, ne_eq, not_true_eq_false, reduceIte, Bool.false_eq_true, hinv, hp, hc, Bool.not_true, bind,
        Except.bind, pure, Except.pure]
    · intro I hIlen hIb
      dsimp only
      refine ⟨by rw [genperm_length, hiplen, hlen], ?_, ?_⟩
      · refine (forall_zip_getD (genperm I ip) dims (by rw [genperm_length, hiplen, hlen])).mpr ?_
        intro k hk
        rw [genperm_length, hiplen] at hk
        obtain ⟨d, hd, hpd⟩ := mem_getD (isperm_mem hp k hk)
        have hipk : ip.getD k 0 = (d : Int) + 1 := by
          have h1 := hval' d hd
          rwa [hpd, (by omega : (((k : Int) + 1) - 1).toNat = k)] at h1
        have hb := (forall_zip_getD I (genperm dims perm)
          (by rw [genperm_length, hIlen, hlen])).mp hIb d (by omega)
        rw [genperm_getD dims perm d hd, hpd, (by omega : (((k : Int) + 1) - 1).toNat = k)] at hb
        rw [genperm_getD I ip k (by omega), hipk, (by omega : (((d : Int) + 1) - 1).toNat = d)]
        exact hb
      · intro d hd
        rw [← hlen] at hd
        have hk2 : ((perm.getD d 0) - 1).toNat < ip.length := by
          have := hrange _ (getD_mem hd)
          omega
        rw [genperm_getD I ip _ hk2, hval' d hd, (by omega : (((d : Int) + 1) - 1).toNat = d)]

end JuliaLean.ReinterpretArrays
