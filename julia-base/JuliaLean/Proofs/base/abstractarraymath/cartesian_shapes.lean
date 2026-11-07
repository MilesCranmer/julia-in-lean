import JuliaLean.Proofs.base.abstractarraymath.cartesian_contracts
import JuliaLean.Proofs.base.abstractarray.cartesian_shapes

namespace JuliaLean.Multidim

namespace SmallAux

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

end SmallAux

open SmallAux

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
