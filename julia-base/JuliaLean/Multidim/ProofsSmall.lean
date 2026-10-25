import JuliaLean.Multidim.Props

/-! Proofs of `CartesianIslessOrder`, `ReverseDimsCheck`, `DiffSize`, `CatSameNdims`,
`RepeatShape` and `SelectdimInRange`. -/

namespace JuliaLean.Multidim

namespace SmallAux

/-! ## `isless` on `CartesianIndex` -/

theorem tupleLess_irrefl : ∀ a : List I64, tupleLess a a = false
  | [] => rfl
  | x :: xs => by simp [tupleLess, tupleLess_irrefl xs]

theorem tupleLess_trans : ∀ a b c : List I64,
    tupleLess a b = true → tupleLess b c = true → tupleLess a c = true
  | [], [], _, h, _ => by simp [tupleLess] at h
  | [], _ :: _, [], _, h => by simp [tupleLess] at h
  | [], _ :: _, _ :: _, _, _ => by simp [tupleLess]
  | _ :: _, [], _, h, _ => by simp [tupleLess] at h
  | _ :: _, _ :: _, [], _, h => by simp [tupleLess] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [tupleLess, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨by omega, tupleLess_trans xs ys zs h1' h2'⟩

theorem tupleLess_total : ∀ a b : List I64, a.length = b.length →
    tupleLess a b = true ∨ a = b ∨ tupleLess b a = true
  | [], [], _ => Or.inr (Or.inl rfl)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    have hl : xs.length = ys.length := by simpa using h
    simp only [tupleLess, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.cons.injEq]
    rcases Int.lt_trichotomy x.val y.val with hxy | hxy | hxy
    · exact Or.inl (Or.inl hxy)
    · have hxy' : x = y := Subtype.ext hxy
      rcases tupleLess_total xs ys hl with h' | h' | h'
      · exact Or.inl (Or.inr ⟨hxy, h'⟩)
      · exact Or.inr (Or.inl ⟨hxy', h'⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hxy.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl hxy))

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

/-! ## `diff` -/

/-! ## `cat` -/

theorem range_map_getD (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

theorem getD_range_map (M : Nat) (F : Nat → Nat) (i : Nat) (hi : i < M) :
    ((List.range M).map F).getD i 0 = F i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem catArg_size_array (y : List Nat) : (CatArg.array y).size = y := rfl

theorem cshp_nil : ∀ (dims : List Bool) (x : List Nat), dims.length ≤ x.length →
    cshp dims [] x = .ok x
  | [], x, _ => by cases x <;> simp [cshp, cshpNoDims]
  | _ :: _, [], h => by simp at h
  | d :: ds, b :: bs, h => by
    have := cshp_nil ds bs (by simp at h; omega)
    simp [cshp, this, bind, Except.bind, pure, Except.pure]

theorem cshp_eq (dims : List Bool) (s y : List Nat) (h1 : dims.length ≤ s.length)
    (h2 : s.length = y.length) :
    cshp dims s y =
      if ∀ i < s.length, dims.getD i false = false → y.getD i 0 = s.getD i 0 then
        .ok ((List.range s.length).map fun i =>
          if dims.getD i false then s.getD i 0 + y.getD i 0 else s.getD i 0)
      else .error .dimensionMismatch := by
  induction s generalizing dims y with
  | nil =>
    cases y with
    | cons => simp at h2
    | nil =>
      cases dims with
      | nil => simp [cshp, cshpNoDims]
      | cons => simp at h1
  | cons a as ih =>
    cases y with
    | nil => simp at h2
    | cons b bs =>
      have hunf : cshp dims (a :: as) (b :: bs) =
          (do let next ← (if dims.headD false then pure (a + b) else cs a b)
              let rest ← cshp dims.tail as bs
              pure (next :: rest)) := by
        cases dims with
        | nil => simp [cshp, cshpNoDims]
        | cons d ds => cases d <;> simp [cshp]
      rw [hunf, ih dims.tail bs (by cases dims <;> simp at h1 ⊢ <;> omega) (by simpa using h2)]
      have hcond : (∀ i < (a :: as).length, dims.getD i false = false →
            (b :: bs).getD i 0 = (a :: as).getD i 0) ↔
          ((dims.headD false = false → b = a) ∧
            ∀ i < as.length, dims.tail.getD i false = false → bs.getD i 0 = as.getD i 0) := by
        constructor
        · intro H
          refine ⟨fun hd => ?_, fun i hi hc => ?_⟩
          · have := H 0 (by simp) (by cases dims <;> simpa using hd)
            simpa using this
          · have := H (i + 1) (by simp; omega) (by cases dims <;> simpa using hc)
            simpa using this
        · rintro ⟨H0, H⟩ i hi hc
          cases i with
          | zero => simpa using H0 (by cases dims <;> simpa using hc)
          | succ i => simpa using H i (by simp at hi; omega) (by cases dims <;> simpa using hc)
      have hlist : (List.range (a :: as).length).map (fun i =>
            if dims.getD i false then (a :: as).getD i 0 + (b :: bs).getD i 0 else (a :: as).getD i 0) =
          (if dims.headD false then a + b else a) :: (List.range as.length).map (fun i =>
            if dims.tail.getD i false then as.getD i 0 + bs.getD i 0 else as.getD i 0) := by
        rw [List.length_cons, List.range_succ_eq_map]
        cases dims <;> simp [Function.comp_def]
      generalize dims.headD false = d at hcond hlist ⊢
      generalize dims.tail = ds at hcond hlist ⊢
      by_cases hC : ∀ i < as.length, ds.getD i false = false → bs.getD i 0 = as.getD i 0
      · rw [if_pos hC]
        by_cases hd : d = true
        · rw [if_pos (hcond.mpr ⟨fun h => by simp [hd] at h, hC⟩), hlist]
          simp [hd, bind, Except.bind, pure, Except.pure]
        · by_cases hab : b = a
          · rw [if_pos (hcond.mpr ⟨fun _ => hab, hC⟩), hlist]
            simp [hd, hab, cs, bind, Except.bind, pure, Except.pure]
          · rw [if_neg (fun h => hab ((hcond.mp h).1 (by simpa using hd)))]
            have hab' : ¬ a = b := fun e => hab e.symm
            simp [hd, cs, hab', bind, Except.bind]
      · rw [if_neg hC, if_neg (fun h => hC (hcond.mp h).2)]
        by_cases hd : d = true
        · simp [hd, bind, Except.bind, pure, Except.pure]
        · by_cases hab : a = b
          · simp [hd, hab, cs, bind, Except.bind]
          · simp [hd, hab, cs, bind, Except.bind]

theorem fold_eq (catdims : List Bool) (M : Nat) (hM : catdims.length ≤ M) :
    ∀ (xs : List (List Nat)) (s : List Nat), s.length = M → (∀ y ∈ xs, y.length = M) →
    (xs.map CatArg.array).foldlM (fun s y => cshp catdims s y.size) s =
      if ∀ i < M, catdims.getD i false = false → ∀ y ∈ xs, y.getD i 0 = s.getD i 0 then
        .ok ((List.range M).map fun i =>
          if catdims.getD i false then s.getD i 0 + (xs.map (·.getD i 0)).sum else s.getD i 0)
      else .error .dimensionMismatch
  | [], s, hs, _ => by
    rw [if_pos (fun i _ _ z hz => by simp at hz)]
    simp only [List.map_nil, List.foldlM_nil, List.sum_nil, Nat.add_zero, ite_self]
    rw [← hs, range_map_getD]
    rfl
  | y :: ys, s, hs, hys => by
    have hy : y.length = M := hys y (by simp)
    have hys' : ∀ z ∈ ys, z.length = M := fun z hz => hys z (by simp [hz])
    simp only [List.map_cons, List.foldlM_cons, catArg_size_array]
    rw [cshp_eq catdims s y (by omega) (by omega), hs]
    by_cases h1 : ∀ i < M, catdims.getD i false = false → y.getD i 0 = s.getD i 0
    · rw [if_pos h1]
      have hget : ∀ i < M, ((List.range M).map fun i =>
          if catdims.getD i false then s.getD i 0 + y.getD i 0 else s.getD i 0).getD i 0 =
          if catdims.getD i false then s.getD i 0 + y.getD i 0 else s.getD i 0 :=
        fun i hi => getD_range_map M _ i hi
      have hlen : ((List.range M).map fun i =>
          if catdims.getD i false then s.getD i 0 + y.getD i 0 else s.getD i 0).length = M := by
        simp
      generalize ((List.range M).map fun i =>
          if catdims.getD i false then s.getD i 0 + y.getD i 0 else s.getD i 0) = s' at hget hlen ⊢
      simp only [bind, Except.bind]
      rw [fold_eq catdims M hM ys s' hlen hys']
      by_cases h2 : ∀ i < M, catdims.getD i false = false → ∀ z ∈ ys, z.getD i 0 = s'.getD i 0
      · have h3 : ∀ i < M, catdims.getD i false = false →
            ∀ z ∈ y :: ys, z.getD i 0 = s.getD i 0 := by
          intro i hi hc z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h1 i hi hc
          · rw [h2 i hi hc z hz, hget i hi, if_neg (by rw [hc]; decide)]
        rw [if_pos h2, if_pos h3]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [hget i hi]
        cases hc : catdims.getD i false <;>
          simp only [Bool.false_eq_true, eq_self, ↓reduceIte, List.sum_cons] <;> omega
      · have h3 : ¬ ∀ i < M, catdims.getD i false = false →
            ∀ z ∈ y :: ys, z.getD i 0 = s.getD i 0 := by
          intro H; apply h2; intro i hi hc z hz
          rw [hget i hi, if_neg (by rw [hc]; decide)]
          exact H i hi hc z (List.mem_cons_of_mem _ hz)
        rw [if_neg h2, if_neg h3]
    · have h3 : ¬ ∀ i < M, catdims.getD i false = false →
          ∀ z ∈ y :: ys, z.getD i 0 = s.getD i 0 :=
        fun H => h1 fun i hi hc => H i hi hc y (by simp)
      rw [if_neg h1, if_neg h3]
      rfl

/-! ## `repeat` -/

theorem i64_max : IntTy.max .i64 = 2 ^ 63 - 1 := rfl
theorem i64_min : IntTy.min .i64 = -2 ^ 63 := rfl

theorem padOnes_length (a : List Int) (N : Nat) (h : a.length ≤ N) : (padOnes a N).length = N := by
  simp only [padOnes, List.length_append, List.length_replicate]; omega

theorem padOnes_bound {a : List Int} {N : Nat} {B : Int} (h : ∀ x ∈ a, 0 ≤ x ∧ x ≤ B)
    (hB : 1 ≤ B) : ∀ x ∈ padOnes a N, 0 ≤ x ∧ x ≤ B := by
  intro x hx
  simp only [padOnes, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h x hx
  · rw [List.eq_of_mem_replicate hx]; omega

theorem zipWith_bound (B1 B2 : Int) (hB1 : 0 ≤ B1) : ∀ (l1 l2 : List Int),
    (∀ x ∈ l1, 0 ≤ x ∧ x ≤ B1) → (∀ x ∈ l2, 0 ≤ x ∧ x ≤ B2) →
    ∀ x ∈ List.zipWith (· * ·) l1 l2, 0 ≤ x ∧ x ≤ B1 * B2
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: l1, b :: l2, h1, h2 => by
    intro x hx
    simp only [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · obtain ⟨ha0, ha⟩ := h1 a (by simp)
      obtain ⟨hb0, hb⟩ := h2 b (by simp)
      exact ⟨Int.mul_nonneg ha0 hb0, Int.mul_le_mul ha hb hb0 hB1⟩
    · exact zipWith_bound B1 B2 hB1 l1 l2 (fun x hx => h1 x (by simp [hx]))
        (fun x hx => h2 x (by simp [hx])) x hx

theorem mapM_checkedMul (B1 B2 : Int) (hB1 : 0 ≤ B1) (hB : B1 * B2 ≤ 2 ^ 63 - 1) :
    ∀ (l1 l2 : List Int), (∀ x ∈ l1, 0 ≤ x ∧ x ≤ B1) → (∀ x ∈ l2, 0 ≤ x ∧ x ≤ B2) →
    ∀ {f : Int × Int → R Int}, (∀ a b, f (a, b) = checkedMul a b) →
    (l1.zip l2).mapM f = .ok (List.zipWith (· * ·) l1 l2)
  | [], l2, _, _, _, _ => by cases l2 <;> rfl
  | _ :: _, [], _, _, _, _ => rfl
  | a :: l1, b :: l2, h1, h2, f, hf => by
    obtain ⟨ha0, ha⟩ := h1 a (by simp)
    obtain ⟨hb0, hb⟩ := h2 b (by simp)
    have hab : IntTy.min .i64 ≤ a * b ∧ a * b ≤ IntTy.max .i64 := by
      have e1 := Int.mul_nonneg ha0 hb0
      have e2 := Int.mul_le_mul ha hb hb0 hB1
      rw [i64_min, i64_max]
      omega
    have ih := mapM_checkedMul B1 B2 hB1 hB l1 l2 (fun x hx => h1 x (by simp [hx]))
      (fun x hx => h2 x (by simp [hx])) hf
    simp [List.zip_cons_cons, List.mapM_cons, hf, checkedMul, hab, ih, bind, Except.bind, pure,
      Except.pure]

theorem getD_zipWith_mul (l1 l2 : List Int) (d : Nat) (h1 : d < l1.length) (h2 : d < l2.length) :
    (List.zipWith (· * ·) l1 l2).getD d 1 = l1.getD d 1 * l2.getD d 1 := by
  have h : d < (List.zipWith (· * ·) l1 l2).length := by simp; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

theorem getD_replicate_one (N d : Nat) : (List.replicate N (1 : Int)).getD d 1 = 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem eq_range_map (l : List Int) (N : Nat) (g : Nat → Int) (hl : l.length = N)
    (h : ∀ d < N, l.getD d 1 = g d) : l = (List.range N).map g := by
  apply List.ext_getElem
  · simp [hl]
  · intro d h1 h2
    have := h d (by omega)
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp [this]

theorem any_neg_false_iff : ∀ i : List Int, i.any (fun x => decide (x < 0)) = false ↔ ∀ x ∈ i, 0 ≤ x
  | [] => by simp
  | a :: l => by
    simp only [List.any_cons, Bool.or_eq_false_iff, any_neg_false_iff l, List.forall_mem_cons,
      decide_eq_false_iff_not, Int.not_lt]

theorem repeatCheck_ok (n : Nat) (inner outer : Option (List Int))
    (h1 : ∀ i, inner = some i → (∀ x ∈ i, 0 ≤ x) ∧ n ≤ i.length)
    (h2 : ∀ o, outer = some o → (∀ x ∈ o, 0 ≤ x) ∧ (n ≤ o.length ∨ inner = none)) :
    repeatCheck n inner outer = .ok () := by
  cases inner with
  | none =>
    cases outer with
    | none => rfl
    | some o =>
      have ho := (any_neg_false_iff o).mpr (h2 o rfl).1
      simp [repeatCheck, ho, pure, Except.pure]
  | some i =>
    have hi := (any_neg_false_iff i).mpr (h1 i rfl).1
    have hil : ¬ i.length < n := by have := (h1 i rfl).2; omega
    cases outer with
    | none => simp [repeatCheck, hi, hil, pure, Except.pure]
    | some o =>
      have ho := (any_neg_false_iff o).mpr (h2 o rfl).1
      have hol : ¬ o.length < n := by
        rcases (h2 o rfl).2 with h | h
        · omega
        · cases h
      simp [repeatCheck, hi, hil, ho, hol, pure, Except.pure]

theorem repeatCheck_err (n : Nat) (inner outer : Option (List Int))
    (h : ¬ ((∀ i, inner = some i → (∀ x ∈ i, 0 ≤ x) ∧ n ≤ i.length) ∧
      (∀ o, outer = some o → (∀ x ∈ o, 0 ≤ x) ∧ (n ≤ o.length ∨ inner = none)))) :
    repeatCheck n inner outer = .error .argumentError := by
  have hany : ∀ l : List Int, ¬ (∀ x ∈ l, 0 ≤ x) → l.any (fun x => decide (x < 0)) = true := by
    intro l hl
    cases hb : l.any (fun x => decide (x < 0))
    · exact absurd ((any_neg_false_iff l).mp hb) hl
    · rfl
  cases inner with
  | none =>
    cases outer with
    | none => exact absurd ⟨fun _ e => (nomatch e), fun _ e => (nomatch e)⟩ h
    | some o =>
      have ho : ¬ ∀ x ∈ o, 0 ≤ x := fun ho =>
        h ⟨fun _ e => (nomatch e), fun o' e => by cases e; exact ⟨ho, Or.inr rfl⟩⟩
      simp [repeatCheck, hany o ho, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  | some i =>
    by_cases hi : ∀ x ∈ i, 0 ≤ x
    · have hi' := (any_neg_false_iff i).mpr hi
      by_cases hil : n ≤ i.length
      · have hil' : ¬ i.length < n := by omega
        cases outer with
        | none => exact absurd ⟨fun i' e => by cases e; exact ⟨hi, hil⟩, fun _ e => (nomatch e)⟩ h
        | some o =>
          by_cases ho : ∀ x ∈ o, 0 ≤ x
          · have ho' := (any_neg_false_iff o).mpr ho
            have hol : o.length < n := Nat.lt_of_not_le fun hle =>
              h ⟨fun i' e => by cases e; exact ⟨hi, hil⟩, fun o' e => by cases e; exact ⟨ho, Or.inl hle⟩⟩
            simp [repeatCheck, hi', hil', ho', hol, throw, throwThe, MonadExceptOf.throw]
          · simp [repeatCheck, hi', hil', hany o ho, throw, throwThe, MonadExceptOf.throw, bind,
              Except.bind]
      · have hil' : i.length < n := by omega
        simp [repeatCheck, hi', hil', throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · simp [repeatCheck, hany i hi, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem le_max3 (a b c : Nat) : a ≤ max a (max b c) ∧ b ≤ max a (max b c) ∧ c ≤ max a (max b c) :=
  ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
   Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩

/-! ## `selectdim` -/

theorem foldl_ndims (f : Nat → Idx) (hf : ∀ j, (f j).ndims = 1) :
    ∀ (L : List Nat) (k : Nat), (L.map f).foldl (fun k i => k + i.ndims) k = k + L.length
  | [], k => by simp
  | j :: L, k => by
    simp only [List.map_cons, List.foldl_cons, hf, List.length_cons]
    rw [foldl_ndims f hf L (k + 1)]; omega

theorem splitAxes_map (f : Nat → Idx) (h : Nat → Nat) (hf : ∀ j, (f j).ndims = 1) :
    ∀ L : List Nat, splitAxes (L.map f) (L.map h) = L.map fun j => (f j, [h j])
  | [] => rfl
  | j :: L => by
    simp [splitAxes, hf, splitAxes_map f h hf L]

theorem any_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (P : Idx → Bool) (hP : ∀ m, P (.slice m) = P .colon) :
    (L.map f).any P = (L.map g).any P := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.any_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hP]

theorem all_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (Q : Idx × List Nat → Bool) (hQ : ∀ m, Q (.slice m, [m]) = Q (.colon, [m])) :
    (L.map fun j => (f j, [h j])).all Q = (L.map fun j => (g j, [h j])).all Q := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hQ]

theorem filterMap_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (Q : Idx × List Nat → Option Nat)
    (hQ : ∀ m, Q (.slice m, [m]) = Q (.colon, [m])) :
    (L.map fun j => (f j, [h j])).filterMap Q = (L.map fun j => (g j, [h j])).filterMap Q := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.filterMap_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hQ]

theorem view_congr (sz : List Nat) (f g : Nat → Idx) (hf : ∀ j, (f j).ndims = 1)
    (hg : ∀ j, (g j).ndims = 1)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (sz.getD j 0) ∧ g j = .colon)) :
    view sz ((List.range sz.length).map f) = view sz ((List.range sz.length).map g) := by
  have hax : axesFor sz sz.length = (List.range sz.length).map (fun j => sz.getD j 0) := by
    rw [range_map_getD]; simp [axesFor]
  simp only [view, foldl_ndims f hf, foldl_ndims g hg, List.length_range,
    Nat.zero_add, hax, splitAxes_map f (fun j => sz.getD j 0) hf,
    splitAxes_map g (fun j => sz.getD j 0) hg]
  rw [any_sel f g _ hb, all_sel f g _ hb, filterMap_sel f g _ hb]
  all_goals first | rfl | (intro m; rfl) | (intro m; simp [idxLen])

theorem rep_split (x y : Idx) (a b : Nat) : List.replicate a x ++ [y] ++ List.replicate b x =
    (List.range (a + 1 + b)).map fun j => if j = a then y else x := by
  apply List.ext_getElem
  · simp; omega
  · intro m h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rcases Nat.lt_trichotomy m a with hm | hm | hm
    · simp [hm, Nat.ne_of_lt hm]
    · subst hm
      simp [List.getElem_cons]
    · have hm1 : ¬ m < a := by omega
      have hm2 : m - a ≠ 0 := by omega
      simp [List.getElem_append, List.getElem_cons, hm1, hm2, Nat.ne_of_gt hm]

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

theorem catSameNdims : CatSameNdims := by
  intro catdims M x xs hM hx hxs
  simp only [List.map_cons, catSizeShape, catArg_size_array]
  rw [cshp_nil catdims x (by omega)]
  exact fold_eq catdims M hM xs x hx hxs

theorem repeatShape : RepeatShape := by
  intro sz inner outer hsz hin hout
  dsimp only
  by_cases hC : (∀ i, inner = some i → (∀ x ∈ i, 0 ≤ x) ∧ sz.length ≤ i.length) ∧
      (∀ o, outer = some o → (∀ x ∈ o, 0 ≤ x) ∧ (sz.length ≤ o.length ∨ inner = none))
  · rw [if_pos hC]
    unfold repeatSize
    rw [repeatCheck_ok _ _ _ hC.1 hC.2]
    simp only [bind, Except.bind]
    obtain ⟨hN1, hN2, hN3⟩ := le_max3 sz.length ((inner.map List.length).getD 0)
      ((outer.map List.length).getD 0)
    generalize max sz.length (max ((inner.map List.length).getD 0)
      ((outer.map List.length).getD 0)) = N at hN1 hN2 hN3 ⊢
    have hP : ∀ x ∈ padOnes sz N, 0 ≤ x ∧ x ≤ 2 ^ 20 :=
      padOnes_bound (fun x hx => ⟨(hsz x hx).1, Int.le_of_lt (hsz x hx).2⟩) (by simp)
    have hPl : (padOnes sz N).length = N := padOnes_length _ _ hN1
    cases inner with
    | none =>
      cases outer with
      | none =>
        simp only [Option.map, Option.getD, pure, Except.pure]
        congr 1
        apply eq_range_map _ _ _ hPl
        intro d _
        rw [getD_replicate_one, Int.mul_one, Int.mul_one]
      | some o =>
        simp only [Option.map, Option.getD] at hN3 ⊢
        have hO : ∀ x ∈ padOnes o N, 0 ≤ x ∧ x ≤ 2 ^ 20 :=
          padOnes_bound (fun x hx => ⟨(hC.2 o rfl).1 x hx, Int.le_of_lt (hout o rfl x hx).1⟩)
            (by simp)
        have hOl : (padOnes o N).length = N := padOnes_length _ _ hN3
        simp only [pure, Except.pure]
        rw [mapM_checkedMul (2 ^ 20) (2 ^ 20) (by simp) (by simp) _ _ hP hO]
        · congr 1
          apply eq_range_map _ _ _ (by simp [hPl, hOl])
          intro d hd
          rw [getD_zipWith_mul _ _ _ (by omega) (by omega), getD_replicate_one, Int.mul_one]
        · intro a b; rfl
    | some i =>
      simp only [Option.map, Option.getD] at hN2 ⊢
      have hI : ∀ x ∈ padOnes i N, 0 ≤ x ∧ x ≤ 2 ^ 20 :=
        padOnes_bound (fun x hx => ⟨(hC.1 i rfl).1 x hx, Int.le_of_lt (hin i rfl x hx).1⟩)
          (by simp)
      have hIl : (padOnes i N).length = N := padOnes_length _ _ hN2
      rw [mapM_checkedMul (2 ^ 20) (2 ^ 20) (by simp) (by simp) _ _ hP hI]
      · dsimp only
        cases outer with
        | none =>
          simp only [pure, Except.pure]
          congr 1
          apply eq_range_map _ _ _ (by simp [hPl, hIl])
          intro d hd
          rw [getD_zipWith_mul _ _ _ (by omega) (by omega), getD_replicate_one, Int.mul_one]
        | some o =>
          simp only [Option.map, Option.getD] at hN3 ⊢
          have hO : ∀ x ∈ padOnes o N, 0 ≤ x ∧ x ≤ 2 ^ 20 :=
            padOnes_bound (fun x hx => ⟨(hC.2 o rfl).1 x hx, Int.le_of_lt (hout o rfl x hx).1⟩)
              (by simp)
          have hOl : (padOnes o N).length = N := padOnes_length _ _ hN3
          have hPI := zipWith_bound (2 ^ 20) (2 ^ 20) (by simp) _ _ hP hI
          have hPIl : (List.zipWith (· * ·) (padOnes sz N) (padOnes i N)).length = N := by
            simp [hPl, hIl]
          rw [mapM_checkedMul (2 ^ 20 * 2 ^ 20) (2 ^ 20) (by simp) (by simp) _ _ hPI hO]
          · congr 1
            apply eq_range_map _ _ _ (by simp [hPIl, hOl])
            intro d hd
            rw [getD_zipWith_mul _ _ _ (by omega) (by omega),
              getD_zipWith_mul _ _ _ (by omega) (by omega)]
          · intro a b; rfl
      · intro a b; rfl
  · rw [if_neg hC]
    unfold repeatSize
    rw [repeatCheck_err _ _ _ hC]
    rfl

theorem selectdimInRange : SelectdimInRange := by
  intro sz d i hd1 hd2 hi _
  have key : view sz (selectdimIdxs sz d i) =
      view sz (List.replicate (d - 1) .colon ++ [i] ++ List.replicate (sz.length - d) .colon) := by
    have hJ : List.replicate (d - 1) Idx.colon ++ [i] ++ List.replicate (sz.length - d) .colon =
        (List.range sz.length).map fun j => if j + 1 = d then i else .colon := by
      rw [rep_split]
      have e : d - 1 + 1 + (sz.length - d) = sz.length := by omega
      rw [e]
      congr 1; funext j
      by_cases hj : j + 1 = d
      · rw [if_pos hj, if_pos (by omega)]
      · rw [if_neg hj, if_neg (by omega)]
    rw [hJ]
    unfold selectdimIdxs
    apply view_congr
    · intro j; by_cases hj : j + 1 = d
      · rw [if_pos hj]; exact hi
      · rw [if_neg hj]; rfl
    · intro j; by_cases hj : j + 1 = d
      · rw [if_pos hj]; exact hi
      · rw [if_neg hj]; rfl
    · intro j; by_cases hj : j + 1 = d <;> simp [hj]
  have hsel : selectdim sz d i =
      (view sz (selectdimIdxs sz d i) >>= fun _ => pure (selectdimIdxs sz d i)) := by
    have a1 : (1 : Int) ≤ d := by omega
    have a2 : ¬ ((sz.length : Int) < d) := by omega
    simp [selectdim, a1, a2]
  rw [hsel, ← key]
  cases hv : view sz (selectdimIdxs sz d i) with
  | error e => rfl
  | ok v => exact hv

end JuliaLean.Multidim
