import JuliaLean.MissingChar.Skip

/-!
# Proofs of the `skipmissing` properties of `JuliaLean.MissingChar.Skip`

Every loop of the model is related to `SkipPf.vals x n k`, the non-missing values at
0-based positions `k, …, k + n - 1` of `x`.
-/

namespace JuliaLean.MissingChar

namespace SkipPf

variable {α β : Type}

/-- The non-missing values at 0-based positions `k, k+1, …, k+n-1` of `x`. -/
def vals (x : List (Option α)) : Nat → Nat → List α
  | 0, _ => []
  | n + 1, k => (x.getD k none).toList ++ vals x n (k + 1)

theorem vals_zero (x : List (Option α)) (k : Nat) : vals x 0 k = [] := rfl

theorem vals_succ (x : List (Option α)) (n k : Nat) :
    vals x (n + 1) k = (x.getD k none).toList ++ vals x n (k + 1) := rfl

theorem vals_add (x : List (Option α)) (m n k : Nat) :
    vals x (m + n) k = vals x m k ++ vals x n (k + m) := by
  induction m generalizing k with
  | zero => simp [vals_zero]
  | succ m ih =>
    rw [Nat.add_right_comm, vals_succ, vals_succ, ih, List.append_assoc,
      show k + 1 + m = k + (m + 1) by omega]

theorem vals_cons (o : Option α) (x : List (Option α)) (n k : Nat) :
    vals (o :: x) n (k + 1) = vals x n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [vals_succ, vals_succ, ih]; rfl

theorem vals_full (x : List (Option α)) : vals x x.length 0 = x.filterMap id := by
  induction x with
  | nil => rfl
  | cons o x ih =>
    rw [List.length_cons, vals_succ, vals_cons o x x.length 0, ih]
    cases o <;> rfl

/-! ## `firstNonMissing` and `simdLoop` -/

theorem fnm_spec (x : List (Option α)) (ilast : Nat) : ∀ fuel k, ilast - k ≤ fuel →
    (firstNonMissing x fuel (k + 1) ilast = none ∧ vals x (ilast - k) k = []) ∨
    ∃ a i, firstNonMissing x fuel (k + 1) ilast = some (a, i) ∧ k < i ∧ i ≤ ilast ∧
      vals x (ilast - k) k = a :: vals x (ilast - i) i := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h
    left
    rw [show ilast - k = 0 by omega]
    exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    intro k h
    by_cases hk : k + 1 > ilast
    · left
      rw [show ilast - k = 0 by omega]
      refine ⟨?_, rfl⟩
      simp only [firstNonMissing, hk, ↓reduceIte]
    · rw [show ilast - k = ilast - (k + 1) + 1 by omega, vals_succ]
      cases hx : x.getD k none with
      | some a =>
        right
        refine ⟨a, k + 1, ?_, by omega, by omega, rfl⟩
        simp only [firstNonMissing, hk, ↓reduceIte, Nat.add_sub_cancel, hx]
      | none =>
        rcases ih (k + 1) (by omega) with ⟨h1, h2⟩ | ⟨a, i, h1, h2, h3, h4⟩
        · left
          refine ⟨?_, by simp [h2]⟩
          simp only [firstNonMissing, hk, ↓reduceIte, Nat.add_sub_cancel, hx, h1]
        · right
          refine ⟨a, i, ?_, by omega, h3, by simp [h4]⟩
          simp only [firstNonMissing, hk, ↓reduceIte, Nat.add_sub_cancel, hx, h1]

theorem simd_spec (f : α → β) (op : β → β → β) (x : List (Option α)) (ilast : Nat) :
    ∀ fuel k v, ilast - k ≤ fuel →
      simdLoop f op x fuel (k + 1) ilast v =
        (vals x (ilast - k) k).foldl (fun acc b => op acc (f b)) v := by
  intro fuel
  induction fuel with
  | zero =>
    intro k v h
    rw [show ilast - k = 0 by omega]
    rfl
  | succ fuel ih =>
    intro k v h
    by_cases hk : k + 1 > ilast
    · rw [show ilast - k = 0 by omega]
      simp only [simdLoop, hk, ↓reduceIte]
      rfl
    · rw [show ilast - k = ilast - (k + 1) + 1 by omega, vals_succ, List.foldl_append]
      simp only [simdLoop, hk, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (k + 1) _ (by omega)]
      cases x.getD k none <;> rfl

/-! ## The pairwise reduction `mrImpl` -/

/-- The value `mrImpl` computes for the non-missing values `l` of its range. -/
def F (f : α → β) (op : β → β → β) : List α → Option β
  | [] => none
  | a :: rest => some (rest.foldl (fun acc b => op acc (f b)) (f a))

theorem foldl_op (f : α → β) (op : β → β → β)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (A : β) :
    ∀ (r : List α) (c : β),
      r.foldl (fun acc b => op acc (f b)) (op A c) =
        op A (r.foldl (fun acc b => op acc (f b)) c) := by
  intro r
  induction r with
  | nil => intro c; rfl
  | cons b r ih =>
    intro c
    simp only [List.foldl_cons]
    rw [hassoc, ih]

theorem mr_spec (f : α → β) (op : β → β → β) (x : List (Option α)) (blk : Nat)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) :
    ∀ N k ilast, ilast - k ≤ N →
      mrImpl f op x blk (k + 1) ilast = F f op (vals x (ilast - k) k) := by
  intro N
  induction N with
  | zero =>
    intro k ilast h
    rw [mrImpl, if_pos (show k + 1 > ilast by omega), show ilast - k = 0 by omega]
    rfl
  | succ N ih =>
    intro k ilast h
    rw [mrImpl]
    by_cases h1 : k + 1 > ilast
    · rw [if_pos h1, show ilast - k = 0 by omega]
      rfl
    rw [if_neg h1]
    by_cases h2 : k + 1 = ilast
    · rw [if_pos h2, show ilast - k = 0 + 1 by omega, vals_succ, Nat.add_sub_cancel]
      cases x.getD k none <;> rfl
    rw [if_neg h2]
    by_cases h3 : ilast - (k + 1) < blk
    · rw [if_pos h3, show ilast + 1 - (k + 1) = ilast - k by omega]
      rcases fnm_spec x ilast (ilast - k) k (Nat.le_refl _) with
        ⟨e1, e2⟩ | ⟨a1, i, e1, hi1, hi2, e2⟩
      · rw [e1, e2]
        rfl
      · rw [e1, e2]
        rcases fnm_spec x ilast (ilast - i) i (Nat.le_refl _) with
          ⟨e3, e4⟩ | ⟨a2, j, e3, hj1, hj2, e4⟩
        · simp [e3, e4, F]
        · simp [e3, e4, F, simd_spec f op x ilast (ilast - j) j _ (Nat.le_refl _)]
    · rw [if_neg h3]
      generalize hm : (ilast - (k + 1)) / 2 = m
      dsimp only
      rw [ih k (k + 1 + m) (by omega), ih (k + 1 + m) ilast (by omega),
        show ilast - k = (k + 1 + m - k) + (ilast - (k + 1 + m)) by omega, vals_add,
        show k + (k + 1 + m - k) = k + 1 + m by omega]
      generalize vals x (k + 1 + m - k) k = l1
      generalize vals x (ilast - (k + 1 + m)) (k + 1 + m) = l2
      cases l1 with
      | nil => cases l2 <;> rfl
      | cons a r1 =>
        cases l2 with
        | nil => simp [F]
        | cons b r2 =>
          simp only [F, List.cons_append, List.foldl_cons, List.foldl_append]
          rw [foldl_op f op hassoc]

/-! ## Iteration -/

theorem while_spec (x : List (Option α)) : ∀ fuel k, x.length - k ≤ fuel →
    (smWhile x fuel none (k + 1) = none ∧ vals x (x.length - k) k = []) ∨
    ∃ a j, smWhile x fuel none (k + 1) = some (a, j + 1) ∧ k < j ∧ j ≤ x.length ∧
      vals x (x.length - k) k = a :: vals x (x.length - j) j := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h
    left
    rw [show x.length - k = 0 by omega]
    exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    intro k h
    by_cases hk : k + 1 ≤ x.length
    · have hv : vecIterate x (k + 1) = some (x.getD k none, k + 1 + 1) := by
        simp only [vecIterate, Nat.add_sub_cancel,
          if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ x.length from ⟨Nat.le_add_left 1 k, hk⟩)]
      rw [show x.length - k = x.length - (k + 1) + 1 by omega, vals_succ]
      cases hx : x.getD k none with
      | some a =>
        right
        refine ⟨a, k + 1, ?_, by omega, hk, rfl⟩
        simp only [smWhile, hv, hx]
      | none =>
        rcases ih (k + 1) (by omega) with ⟨h1, h2⟩ | ⟨a, j, h1, h2, h3, h4⟩
        · left
          exact ⟨by simp only [smWhile, hv, hx, h1], by simp [h2]⟩
        · right
          exact ⟨a, j, by simp only [smWhile, hv, hx, h1], by omega, h3, by simp [h4]⟩
    · left
      have hv : vecIterate x (k + 1) = none := by
        simp only [vecIterate,
          if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ x.length) by omega)]
      rw [show x.length - k = 0 by omega]
      exact ⟨by simp only [smWhile, hv], rfl⟩

theorem iterate_eq (x : List (Option α)) (k : Nat) :
    smIterate x (k + 1) = smWhile x (x.length - k) none (k + 1) := by
  by_cases hk : k + 1 ≤ x.length
  · rw [show x.length - k = x.length - (k + 1) + 1 by omega]
    simp only [smIterate, smWhile, vecIterate, Nat.add_sub_cancel,
      if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ x.length from ⟨Nat.le_add_left 1 k, hk⟩)]
    rw [show x.length + 1 - (k + 1 + 1) = x.length - (k + 1) by omega]
  · rw [show x.length - k = 0 by omega]
    simp only [smIterate, smWhile, vecIterate,
      if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ x.length) by omega)]

theorem collect_spec (x : List (Option α)) : ∀ fuel k, x.length - k + 1 ≤ fuel →
    smCollectFrom x fuel (k + 1) = vals x (x.length - k) k := by
  intro fuel
  induction fuel with
  | zero => intro k h; omega
  | succ fuel ih =>
    intro k h
    rcases while_spec x (x.length - k) k (Nat.le_refl _) with
      ⟨e1, e2⟩ | ⟨a, j, e1, h1, h2, e2⟩
    · simp only [smCollectFrom, iterate_eq, e1, e2]
    · simp only [smCollectFrom, iterate_eq, e1, e2, ih j (by omega)]

theorem collect_eq (x : List (Option α)) : smCollect x = vals x x.length 0 := by
  have h := collect_spec x (x.length + 1) 0 (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at h
  exact h

/-! ## Keys -/

theorem map_range' (s n : Nat) :
    (List.range' s n).map (· + 1) = List.range' (s + 1) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.range'_succ, List.map_cons, ih]

theorem keys_eq (x : List (Option α)) :
    smKeys x = (List.range' 1 x.length).filter (fun i => (x.getD (i - 1) none).isSome) := by
  unfold smKeys
  rw [List.range_eq_range', map_range']

theorem getindex_nat (x : List (Option α)) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ x.length) :
    smGetindex x (n : Int) = (match x.getD (n - 1) none with
      | some a => .ok a
      | none => .error .missingException) := by
  unfold smGetindex vecGet
  rw [if_pos (show (1 : Int) ≤ (n : Int) ∧ (n : Int) ≤ (x.length : Int) by omega),
    Int.toNat_natCast]
  cases x.getD (n - 1) none <;> rfl

theorem keys_mapM (x : List (Option α)) : ∀ n k, k + n ≤ x.length →
    ((List.range' (k + 1) n).filter (fun i => (x.getD (i - 1) none).isSome)).mapM
      (fun (i : Nat) => smGetindex x (i : Int)) = .ok (vals x n k) := by
  intro n
  induction n with
  | zero => intro k h; rfl
  | succ n ih =>
    intro k h
    have hg := getindex_nat x (k + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hg
    rw [List.range'_succ, vals_succ, List.filter_cons]
    cases hx : x.getD k none with
    | some a =>
      rw [hx] at hg
      simp only [Nat.add_sub_cancel, hx, Option.isSome_some, ↓reduceIte, List.mapM_cons, hg,
        ih (k + 1) (by omega)]
      rfl
    | none =>
      simp only [Nat.add_sub_cancel, hx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1) (by omega)

theorem mem_keys (x : List (Option α)) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ x.length) :
    n ∈ smKeys x ↔ (x.getD (n - 1) none).isSome := by
  rw [keys_eq, List.mem_filter, List.mem_range'_1]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h1, by omega⟩, h⟩

/-! ## `findfirst` -/

theorem findfirst_spec (f : α → Bool) (x : List (Option α)) : ∀ n k,
    ((((List.range' (k + 1) n).filter (fun i => (x.getD (i - 1) none).isSome)).zip
        (vals x n k)).find? (fun p => f p.2)).map (·.1) =
      ((List.range' (k + 1) n).filter (fun i => (x.getD (i - 1) none).isSome)).find?
        (fun i => match x.getD (i - 1) none with
          | some a => f a
          | none => false) := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    rw [List.range'_succ, vals_succ, List.filter_cons]
    cases hx : x.getD k none with
    | some a =>
      simp only [Nat.add_sub_cancel, hx, Option.isSome_some, ↓reduceIte, Option.toList_some,
        List.singleton_append, List.zip_cons_cons, List.find?_cons]
      cases hf : f a
      · simpa [hf] using ih (k + 1)
      · simp
    | none =>
      simp only [Nat.add_sub_cancel, hx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Option.toList_none, List.nil_append]
      exact ih (k + 1)

/-! ## `filter` -/

theorem foldl_filter (f : α → Bool) (step : List α → Option α → List α)
    (hs : ∀ y o, step y o = y ++ o.toList.filter f) :
    ∀ (x : List (Option α)) (y : List α), x.foldl step y = y ++ (x.filterMap id).filter f := by
  intro x
  induction x with
  | nil => intro y; simp
  | cons o x ih =>
    intro y
    rw [List.foldl_cons, ih, hs]
    cases o with
    | none => simp
    | some a => cases hf : f a <;> simp [hf]

end SkipPf

open SkipPf

theorem skipMissingIterate_proven : SkipMissingIterate := by
  intro α x
  rw [collect_eq, vals_full]

theorem skipMissingKeys_proven : SkipMissingKeys := by
  intro α x
  refine ⟨?_, ?_⟩
  · have h := keys_mapM x x.length 0 (by omega)
    rw [Nat.zero_add] at h
    rw [keys_eq, collect_eq]
    exact h
  · intro i hi1 hi2
    obtain ⟨n, rfl⟩ : ∃ n : Nat, i = (n : Int) := ⟨i.toNat, by omega⟩
    have h1 : 1 ≤ n := by omega
    have h2 : n ≤ x.length := by omega
    rw [Int.toNat_natCast, mem_keys x n h1 h2, getindex_nat x n h1 h2]
    cases x.getD (n - 1) none <;> simp

theorem skipMissingFilter_proven : SkipMissingFilter := by
  intro α f x
  unfold smFilter
  rw [collect_eq, vals_full, foldl_filter f _ ?_ x [], List.nil_append]
  intro y o
  cases o with
  | none => simp
  | some a => cases hf : f a <;> simp [hf]

theorem skipMissingFindFirst_proven : SkipMissingFindFirst := by
  intro α f x
  have h := findfirst_spec f x x.length 0
  rw [Nat.zero_add] at h
  unfold smFindfirst
  rw [keys_eq, collect_eq]
  exact h

theorem skipMissingMapreduce_proven : SkipMissingMapreduce := by
  intro α β f op empty blk x hassoc
  rw [← vals_full x]
  unfold mrSkip
  dsimp only
  have e := fnm_spec x x.length x.length 0 (by omega)
  simp only [Nat.zero_add, Nat.sub_zero] at e
  rcases e with ⟨e1, e2⟩ | ⟨a1, i, e1, hi1, hi2, e2⟩
  · rw [e1, e2]
  · rw [e1, e2]
    rcases fnm_spec x x.length (x.length - i) i (Nat.le_refl _) with
      ⟨e3, e4⟩ | ⟨a2, j, e3, _, _, e4⟩
    · simp [e3, e4]
    · have e5 := mr_spec f op x blk hassoc _ 0 x.length (Nat.le_refl _)
      simp only [Nat.zero_add, Nat.sub_zero, e2, e4] at e5
      simp [e3, e4, e5, F]

end JuliaLean.MissingChar
