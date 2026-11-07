import JuliaLean.Proofs.base.abstractarray.cartesian_contracts

namespace JuliaLean.Multidim

namespace SmallAux

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

end SmallAux

open SmallAux

theorem catSameNdims : CatSameNdims := by
  intro catdims M x xs hM hx hxs
  simp only [List.map_cons, catSizeShape, catArg_size_array]
  rw [cshp_nil catdims x (by omega)]
  exact fold_eq catdims M hM xs x hx hxs

end JuliaLean.Multidim
