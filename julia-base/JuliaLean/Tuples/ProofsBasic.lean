import JuliaLean.Tuples.Lemmas

/-! Proofs of the construction, indexing, mapping and search properties. -/

namespace JuliaLean.Tuples

variable {α β γ δ : Type}

theorem ntupleCorrect : NtupleCorrect := by
  refine ⟨?_, ?_⟩
  · intro α _ f t n
    simp only [ntuple, JInt.convert]
    split
    · rename_i h
      simp only [liftJ_ok', R.bind_ok]
      have h1 : ¬ (n.val < IntTy.i64.min ∨ n.val > IntTy.i64.max) := by omega
      rw [if_neg h1]
      unfold ntupleInt
      by_cases h2 : n.val < 0
      · rw [if_pos h2, if_neg (by omega), if_neg (by omega)]
        simp [SameOutcome, argErr, Err.kind]
      · rw [if_neg h2]
        by_cases h3 : n.val ≤ 10
        · rw [if_pos ⟨by omega, h3⟩]; exact sameOutcome_refl _
        · rw [if_neg (by omega), if_pos (by omega)]; exact sameOutcome_refl _
    · rename_i h
      have h1 : n.val < IntTy.i64.min ∨ n.val > IntTy.i64.max := by omega
      rw [if_pos h1]
      simp [SameOutcome, Err.kind]
  · intro α _ f N
    unfold ntupleVal
    split
    · rw [if_neg (by omega)]; exact sameOutcome_refl _
    · rw [if_pos (by omega)]; simp [SameOutcome, argErr, Err.kind]

theorem fillToLengthCorrect : FillToLengthCorrect := by
  intro α _ t v N
  unfold fillToLength
  by_cases h0 : (t.length : Int) = N.val
  · rw [if_pos h0, if_neg (by omega)]
    have : (N.val - t.length).toNat = 0 := by omega
    simp [this, SameOutcome]
  rw [if_neg h0]
  by_cases h1 : t.length = 0 ∧ N.val = 1
  · rw [if_pos h1, if_neg (by omega)]
    have ht : t = [] := List.length_eq_zero_iff.mp h1.1
    subst ht
    simp [h1.2, SameOutcome]
  rw [if_neg h1]
  by_cases h2 : t.length = 1 ∧ N.val = 2
  · rw [if_pos h2, if_neg (by omega)]
    have : (N.val - t.length).toNat = 1 := by omega
    simp [this, SameOutcome]
  rw [if_neg h2]
  by_cases h3 : t.length = 0 ∧ N.val = 2
  · rw [if_pos h3, if_neg (by omega)]
    have ht : t = [] := List.length_eq_zero_iff.mp h3.1
    subst ht
    simp [h3.2, SameOutcome]
  rw [if_neg h3]
  split
  · simp [SameOutcome, argErr, Err.kind]
  · exact sameOutcome_refl _

theorem revargs_eq (t : List α) : revargs t = t.reverse := by
  induction t with
  | nil => rfl
  | cons x r ih => simp [revargs, ih]

theorem reverseCorrect : ReverseCorrect := by
  intro α t
  refine ⟨revargs_eq t, ?_⟩
  unfold reverseNTuple
  apply mapM_range_ok
  · simp
  · intro k hk
    simp at hk
    have e : (t.length : Int) + 1 - ((k : Int) + 1) = (((t.length - 1 - k : Nat) : Int)) + 1 := by
      omega
    rw [e, getfield_ok t _ (by omega)]
    simp [List.getElem_reverse]

theorem frontTailCorrect : FrontTailCorrect := by
  intro α _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [front_spec]; split <;> simp [SameOutcome, argErr, Err.kind]
  · cases t <;> simp [tail, SameOutcome, argErr, Err.kind]
  · cases t with
    | nil => simp [first, SameOutcome, argErr, Err.kind]
    | cons a r =>
      have := getfield_ok (a :: r) 0 (by simp)
      simp at this
      simp [first, this, SameOutcome]
  · unfold last
    cases h : t.getLast? with
    | none =>
      have : t = [] := by simpa using h
      subst this; simp [getfield, SameOutcome, bounds]
    | some a =>
      have hne : t ≠ [] := by intro e; subst e; simp at h
      have hl : 0 < t.length := List.length_pos_iff.mpr hne
      have := getfield_ok t (t.length - 1) (by omega)
      have e : (((t.length - 1 : Nat)) : Int) + 1 = t.length := by omega
      rw [e] at this
      rw [this]
      rw [List.getLast?_eq_getElem?] at h
      simp [List.getElem?_eq_getElem (show t.length - 1 < t.length by omega)] at h
      simp [SameOutcome, h]

theorem getindex_int (t : List α) (ty : IntTy) (i : JInt ty) :
    getindex t (.int ty i) =
      if i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max then .error (.jl (.inexactError IntTy.i64.name))
      else getfield t i.val := by
  show (if ty = .i64 then getfield t i.val
    else do let j ← liftJ (JInt.convert .i64 i.val); getfield t j.val) = _
  have hb := i.property
  by_cases hty : ty = .i64
  · subst hty
    have h1 : ¬ (i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max) := by omega
    rw [if_pos rfl, if_neg h1]
  · rw [if_neg hty]
    simp only [JInt.convert]
    by_cases h : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max
    · have h1 : ¬ (i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max) := by omega
      rw [dif_pos h, if_neg h1]; rfl
    · have h1 : i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max := by omega
      rw [dif_neg h, if_pos h1]; rfl

theorem integerIndexCorrect : IntegerIndexCorrect := by
  intro α _ t ty i v d hlen
  simp only
  have elt_eq : (1 ≤ i.val ∧ i.val ≤ t.length) →
      getfield t i.val = (match t[(i.val - 1).toNat]? with | some a => .ok a | none => bounds) := by
    intro h
    unfold getfield
    rw [if_pos h.1]
    cases t[(i.val - 1).toNat]? <;> rfl
  have gi : SameOutcome (getindex t (.int ty i))
      (if 1 ≤ i.val ∧ i.val ≤ t.length then
        (match t[(i.val - 1).toNat]? with | some a => .ok a | none => bounds)
       else if i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max then .error (.jl (.inexactError ""))
       else bounds) := by
    rw [getindex_int]
    by_cases hin : 1 ≤ i.val ∧ i.val ≤ t.length
    · have hmin : IntTy.i64.min ≤ 0 := by decide
      rw [if_neg (by omega), if_pos hin, elt_eq hin]
      exact sameOutcome_refl _
    · rw [if_neg hin]
      split
      · simp [SameOutcome, Err.kind]
      · rw [getfield_bounds t _ hin]; exact sameOutcome_refl _
  refine ⟨gi, ?_, ?_, ?_⟩
  · unfold setindex
    by_cases h : 1 ≤ i.val ∧ i.val ≤ t.length
    · have h' : 1 ≤ (Idx.int ty i).val ∧ (Idx.int ty i).val ≤ t.length := h
      rw [if_pos h', if_pos h]
      apply sameOutcome_of_eq
      congr 1
      apply List.ext_getElem
      · simp
      · intro k h1 h2
        have hv : (Idx.int ty i).val = i.val := rfl
        simp only [List.getElem_zipWith, List.getElem_range, List.getElem_set]
        by_cases hk : ((k : Int) + 1) = (Idx.int ty i).val
        · have hk' : (i.val - 1).toNat = k := by omega
          rw [if_pos hk, if_pos hk']
        · have hk' : ¬ (i.val - 1).toNat = k := by omega
          rw [if_neg hk, if_neg hk']
    · have h' : ¬ (1 ≤ (Idx.int ty i).val ∧ (Idx.int ty i).val ≤ t.length) := h
      rw [if_neg h', if_neg h]; exact sameOutcome_refl _
  · unfold get
    by_cases h : 1 ≤ i.val ∧ i.val ≤ t.length
    · have h' : 1 ≤ (Idx.int ty i).val ∧ (Idx.int ty i).val ≤ t.length := h
      have := gi
      rw [if_pos h] at this
      rw [if_pos h', if_pos h]
      exact this
    · have h' : ¬ (1 ≤ (Idx.int ty i).val ∧ (Idx.int ty i).val ≤ t.length) := h
      rw [if_neg h', if_neg h]; exact sameOutcome_refl _
  · rfl

theorem unitRange_spec (t : List α) (a : Int) (len : Nat) :
    getindexUnitRange t a len =
      if len = 0 then .ok []
      else if 1 ≤ a ∧ a + len - 1 ≤ t.length then .ok ((t.drop (a - 1).toNat).take len)
      else bounds := by
  have generic := mapM_slice t a len (fun k => a + k) (fun _ => rfl)
  unfold getindexUnitRange
  split
  · exact mapM_slice t a len _ (fun k => by omega)
  · rename_i hlen
    have hlen0 : len ≠ 0 := by omega
    rw [if_neg hlen0]
    split
    · rename_i ha
      subst ha
      split
      · rename_i he
        rw [if_pos (by omega)]
        have : len = t.length := by omega
        subst this
        simp
      · split
        · rename_i _ he
          have hl : 0 < t.length := by omega
          have hin : 1 ≤ (1 : Int) ∧ 1 + (len : Int) - 1 ≤ t.length := by omega
          have hl' : len = t.length - 1 := by omega
          rw [front_spec, if_neg (List.length_pos_iff.mp hl), if_pos hin, List.dropLast_eq_take, hl']
          simp
        · split
          · rename_i _ _ he
            rw [front_spec, if_neg (by intro e; subst e; simp at he; omega)]
            simp only [R.bind_ok]
            rw [front_spec, if_neg (by
              intro e
              have := congrArg List.length e
              simp at this; omega)]
            rw [if_pos (by omega)]
            simp [List.dropLast_eq_take, List.take_take]
            congr 1; omega
          · rw [generic, if_neg hlen0]
    · split
      · rename_i ha he
        split
        · rename_i h2
          subst h2
          rw [if_pos (by omega)]
          cases t with
          | nil => simp at he; omega
          | cons x r =>
            simp [tail]
            simp at he
            rw [List.take_of_length_le (by omega)]
        · split
          · rename_i _ h3
            subst h3
            rw [if_pos (by omega)]
            match t, he with
            | x :: y :: r, he =>
              simp [tail]
              simp at he
              rw [List.take_of_length_le (by omega)]
            | [x], he => simp at he; omega
            | [], he => simp at he; omega
          · rw [generic, if_neg hlen0]
      · rw [generic, if_neg hlen0]

theorem unitRangeIndexCorrect : UnitRangeIndexCorrect := by
  intro α _ t a b hab
  unfold getindexColon unitRange
  simp only
  rw [unitRange_spec]
  by_cases hba : b.val < a.val
  · have hn : ¬ b.val ≥ a.val := by omega
    rw [if_neg hn, if_pos rfl, if_pos hba]
    exact sameOutcome_refl _
  · have hge : b.val ≥ a.val := by omega
    have hne : (b.val - a.val + 1).toNat ≠ 0 := by omega
    rw [if_pos hge, if_neg hne, if_neg hba]
    by_cases hin : 1 ≤ a.val ∧ b.val ≤ t.length
    · have hin' : 1 ≤ a.val ∧ a.val + (((b.val - a.val + 1).toNat : Nat) : Int) - 1 ≤ t.length := by
        omega
      rw [if_pos hin', if_pos hin]; exact sameOutcome_refl _
    · have hin' : ¬ (1 ≤ a.val ∧ a.val + (((b.val - a.val + 1).toNat : Nat) : Int) - 1 ≤ t.length) := by
        omega
      rw [if_neg hin', if_neg hin]; exact sameOutcome_refl _

private theorem map1Rec_cons (f : α → β) (a : α) (r : List α) :
    map1Rec f (a :: r) = f a :: map1Rec f r := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rfl

theorem map1Rec_eq (f : α → β) (t : List α) : map1Rec f t = t.map f := by
  induction t with
  | nil => rfl
  | cons a r ih => rw [map1Rec_cons, ih]; rfl

theorem map1Loop_eq (f : α → β) (t : List α) (i k : Nat) (h : i + k = t.length) :
    map1Loop f t i k = (t.drop i).map f := by
  induction k generalizing i with
  | zero =>
    have h0 : t.length ≤ i := by omega
    simp [map1Loop, drop_nil_of_le h0]
  | succ k ih =>
    have hi : i < t.length := by omega
    rw [map1Loop, getElem?_of_lt hi, ih (i + 1) (by omega), drop_cons_of_lt hi]
    rfl

private theorem map2Rec_cons (f : α → β → γ) (a : α) (b : β) (r : List α) (s : List β) :
    map2Rec f (a :: r) (b :: s) = f a b :: map2Rec f r s := by
  rcases r with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> rcases s with _ | ⟨x', _ | ⟨y', s⟩⟩ <;> rfl

theorem map2Rec_eq (f : α → β → γ) (t : List α) (s : List β) :
    map2Rec f t s = List.zipWith f t s := by
  induction t generalizing s with
  | nil => cases s <;> rfl
  | cons a r ih =>
    cases s with
    | nil => rfl
    | cons b s => rw [map2Rec_cons, ih]; rfl

theorem map2Loop_eq (f : α → β → γ) (t : List α) (s : List β) (i k : Nat)
    (h : i + k = min t.length s.length) :
    map2Loop f t s i k = List.zipWith f (t.drop i) (s.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [map2Loop]
    rcases Nat.le_total t.length s.length with h' | h'
    · have h0 : t.length ≤ i := by omega
      rw [drop_nil_of_le h0]; simp
    · have h0 : s.length ≤ i := by omega
      rw [drop_nil_of_le h0]; simp
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [map2Loop, getElem?_of_lt hi, getElem?_of_lt hj, ih (i + 1) (by omega),
      drop_cons_of_lt hi, drop_cons_of_lt hj]
    rfl

theorem map3Rec_eq (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) :
    map3Rec f t s u = zip3With f t s u := by
  induction t generalizing s u with
  | nil => cases s <;> cases u <;> rfl
  | cons a r ih =>
    cases s with
    | nil => cases u <;> rfl
    | cons b s =>
      cases u with
      | nil => rfl
      | cons c u => exact congrArg (f a b c :: ·) (ih s u)

theorem zip3With_drop_nil (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) :
    (t = [] ∨ s = [] ∨ u = []) → zip3With f t s u = [] := by
  intro h
  cases t <;> cases s <;> cases u <;> first | rfl | simp at h

theorem map3Loop_eq (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) (i k : Nat)
    (h : i + k = min t.length (min s.length u.length)) :
    map3Loop f t s u i k = zip3With f (t.drop i) (s.drop i) (u.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [map3Loop]
    symm
    apply zip3With_drop_nil
    by_cases h1 : t.length ≤ i
    · exact Or.inl (drop_nil_of_le h1)
    · by_cases h2 : s.length ≤ i
      · exact Or.inr (Or.inl (drop_nil_of_le h2))
      · have h3 : u.length ≤ i := by omega
        exact Or.inr (Or.inr (drop_nil_of_le h3))
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    have hl : i < u.length := by omega
    rw [map3Loop, getElem?_of_lt hi, getElem?_of_lt hj, getElem?_of_lt hl, ih (i + 1) (by omega),
      drop_cons_of_lt hi, drop_cons_of_lt hj, drop_cons_of_lt hl]
    simp [zip3With]

theorem mapCorrect : MapCorrect := by
  intro α β γ δ f1 f2 f3 t s u
  refine ⟨?_, ?_, ?_⟩
  · unfold map1; split
    · rw [map1Loop_eq f1 t 0 _ (by omega)]; simp
    · exact map1Rec_eq f1 t
  · unfold map2; split
    · rw [map2Loop_eq f2 t s 0 _ (by omega)]; simp
    · exact map2Rec_eq f2 t s
  · unfold map3; split
    · rw [map3Loop_eq f3 t s u 0 _ (by omega)]; simp
    · exact map3Rec_eq f3 t s u

theorem findfirstRec_eq (f : α → Bool) (t : List α) (i : Nat) :
    findfirstRec f i t = (t.findIdx? f).map (· + i) := by
  induction t generalizing i with
  | nil => rfl
  | cons a r ih =>
    simp only [findfirstRec, List.findIdx?_cons]
    split
    · simp_all
    · rename_i hf
      simp [hf, ih, Option.map_map]
      congr 1; funext x; simp only [Function.comp_apply]; omega

theorem findfirstLoop_eq (f : α → Bool) (t : List α) (i k : Nat) (h : i + k = t.length) :
    findfirstLoop f t i k = ((t.drop i).findIdx? f).map (· + i + 1) := by
  induction k generalizing i with
  | zero =>
    have h0 : t.length ≤ i := by omega
    simp [findfirstLoop, drop_nil_of_le h0]
  | succ k ih =>
    have hi : i < t.length := by omega
    rw [findfirstLoop, getElem?_of_lt hi, ih (i + 1) (by omega), drop_cons_of_lt hi,
      List.findIdx?_cons]
    simp only
    split
    · simp_all
    · rename_i hf
      simp [hf, Option.map_map]
      congr 1; funext x; simp only [Function.comp_apply]; omega

theorem findfirst_eq (f : α → Bool) (t : List α) : findfirst f t = (t.findIdx? f).map (· + 1) := by
  unfold findfirst
  split
  · exact findfirstRec_eq f t 1
  · rw [findfirstLoop_eq f t 0 _ (by omega)]; simp

theorem lastIndex_append (f : α → Bool) (t : List α) (a : α) :
    lastIndex f (t ++ [a]) = if f a then some (t.length + 1) else lastIndex f t := by
  induction t with
  | nil => simp [lastIndex]
  | cons x r ih =>
    show (match lastIndex f (r ++ [a]) with
      | some k => some (k + 1)
      | none => if f x then some 1 else none) = _
    rw [ih]
    by_cases hfa : f a = true
    · simp [hfa]
    · rw [if_neg hfa, if_neg hfa] <;> rfl

theorem lastIndex_eq (f : α → Bool) (t : List α) :
    lastIndex f t = (t.reverse.findIdx? f).map (fun r => t.length - r) := by
  induction t with
  | nil => rfl
  | cons x r ih =>
    show (match lastIndex f r with
      | some k => some (k + 1)
      | none => if f x then some 1 else none) = _
    rw [ih, List.reverse_cons, List.findIdx?_append, List.findIdx?_cons]
    cases hr : r.reverse.findIdx? f with
    | some j =>
      have hj : j < r.length := by
        have := (List.findIdx?_eq_some_iff_getElem.mp hr).1
        simpa using this
      simp <;> omega
    | none =>
      by_cases hx : f x = true <;> simp [hx] <;> omega

theorem findlastLoop_eq (f : α → Bool) (t : List α) (k : Nat) (h : k ≤ t.length) :
    findlastLoop f t k = lastIndex f (t.take k) := by
  induction k with
  | zero => simp [findlastLoop, lastIndex]
  | succ k ih =>
    have hk : k < t.length := by omega
    rw [findlastLoop, List.take_succ, getElem?_of_lt hk, Option.toList_some, lastIndex_append,
      ih (by omega), List.length_take, Nat.min_eq_left (show k ≤ t.length by omega)]
    all_goals rfl

theorem findlast_eq (f : α → Bool) (t : List α) : findlast f t = lastIndex f t := by
  unfold findlast
  split
  · rename_i h
    rw [findfirst_eq, revargs_eq, lastIndex_eq]
    cases hr : t.reverse.findIdx? f with
    | none => rfl
    | some r =>
      have := List.findIdx?_eq_some_iff_getElem.mp hr
      obtain ⟨hlt, _, _⟩ := this
      simp at hlt
      simp; omega
  · rw [findlastLoop_eq f t _ (Nat.le_refl _), List.take_length]

theorem filterRec_eq (f : α → Bool) (t : List α) : filterRec f t = t.filter f := by
  unfold filterRec
  suffices ∀ acc, t.foldl (fun ys x => if f x then ys ++ [x] else ys) acc = acc ++ t.filter f by
    simpa using this []
  induction t with
  | nil => simp
  | cons a r ih =>
    intro acc
    simp only [List.foldl_cons, List.filter_cons]
    split <;> simp [ih]

theorem findFilterCorrect : FindFilterCorrect := by
  intro α f t
  refine ⟨findfirst_eq f t, findlast_eq f t, ?_⟩
  unfold filter; split
  · exact filterRec_eq f t
  · rfl

theorem inTupleRec_eq (eq : α → α → Option Bool) (x : α) (t : List α) (b : Bool) :
    inTupleRec eq x t (if b then none else some false) = anyGo (fun y => eq y x) t b := by
  induction t generalizing b with
  | nil => cases b <;> rfl
  | cons a r ih =>
    simp only [inTupleRec, anyGo]
    cases h : eq a x with
    | none =>
      simp only
      have : or3 (if b then none else some false) none = if true then none else some false := by
        cases b <;> rfl
      rw [this, ih]
      simp
    | some c =>
      cases c with
      | true => simp
      | false =>
        simp only
        have : or3 (if b then none else some false) (some false) = if b then none else some false := by
          cases b <;> rfl
        rw [this, ih]
        simp

theorem inCorrect : InCorrect := by
  intro α eq x t
  unfold inTuple
  split
  · rfl
  · simpa using inTupleRec_eq eq x t false

end JuliaLean.Tuples
