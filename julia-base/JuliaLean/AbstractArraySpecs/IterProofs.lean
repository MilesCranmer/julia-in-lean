import JuliaLean.AbstractArraySpecs.IndexingProofs

/-! Proofs of the iteration, `isequal`, `==` and `map!` contracts. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

/-! ## Element access at a known reference position -/

theorem refPos_full {α : Type} (A : Arr α) (J : List I64) (hJ : J.length = A.axes.length) :
    refPos A J = refCartPos A.axes (J.map (·.val)) := by
  by_cases h1 : J.length = 1
  · obtain ⟨k, rfl⟩ := exists_single h1
    obtain ⟨r, hax⟩ := exists_single (show A.axes.length = 1 by simpa using hJ.symm)
    simp only [refPos, refLinPos, hax, refCartPos_single, List.map_cons, List.map_nil]
  · exact refPos_cart A J h1

theorem getindex_at {α : Type} (A : Arr α) (hA : A.WF) (J : List I64) (p : Nat)
    (hle : A.axes.length ≤ J.length ∨ J.length = 1) (hp : refPos A J = some p) :
    getindex A J = .ok (A.data[p]'(refPos_lt A hA J p hp)) := by
  have hg : getindex A J = refGet A J := by
    rcases hle with h | h
    · exact (indexing_extra A hA J h).1
    · obtain ⟨k, rfl⟩ := exists_single h; exact (indexing_linear A hA k).1
  rw [hg, refGet_eq, hp]
  simp [elemAt, List.getElem?_eq_getElem (refPos_lt A hA J p hp)]

theorem setindex_at {α : Type} (A : Arr α) (hA : A.WF) (J : List I64) (p : Nat) (v : α)
    (hle : A.axes.length ≤ J.length ∨ J.length = 1) (hp : refPos A J = some p) :
    setindex A v J = .ok { A with data := A.data.set p v } := by
  have hs : setindex A v J = refSet A v J := by
    rcases hle with h | h
    · exact (indexing_extra A hA J h).2 v
    · obtain ⟨k, rfl⟩ := exists_single h; exact (indexing_linear A hA k).2 v
  rw [hs, refSet_eq, hp]
  simp [storeAt, refPos_lt A hA J p hp]

/-! ## Linear stepping -/

theorem linAx_len {α : Type} (A : Arr α) (hA : A.WF) :
    (linearAxis A).hi.val = (linearAxis A).lo.val + A.data.length - 1 := by
  have hd := hA.2.1
  have hlen := lengthA_val A hA
  unfold linearAxis
  rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · simp only [onetoLen, oneTo, one_val, hlen]; omega
  · rw [hax] at hd; simp only [totalLen, Int.mul_one, len_def] at hd
    simp only [axes1, hax]; omega
  · simp only [onetoLen, oneTo, one_val, hlen]; omega

/-- Linear indices `lo + j` (wrapped as Julia's `state + 1` wraps) select element `j`
for `j < length(A)` and nothing for `j = length(A)`. -/
theorem refLin_step {α : Type} (A : Arr α) (hA : A.WF) (j : Nat) (hj : j ≤ A.data.length) :
    refLinPos A (wrapInt .i64 ((linearAxis A).lo.val + j)) =
      if j < A.data.length then some j else none := by
  have hd := hA.2.1
  have hb := hA.2.2
  rw [tmax_eq] at hb
  have hlen := lengthA_val A hA
  have hhi := linAx_len A hA
  have hlo := bnd (linearAxis A).lo
  have hhb := bnd (linearAxis A).hi
  by_cases h : j < A.data.length
  · rw [if_pos h, wrap_id _ (by omega) (by omega)]
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · have hns : ∀ r', A.axes ≠ [r'] := by intro r' h'; rw [hax] at h'; simp at h'
      rw [refLinPos_ns A hns]
      simp only [linearAxis, hax, onetoLen, oneTo, one_val] at hhi ⊢
      rw [hax] at hd; rw [← hd]; simp; omega
    · simp only [refLinPos, linearAxis, axes1, hax] at hhi ⊢
      simp; omega
    · have hns : ∀ r', A.axes ≠ [r'] := by intro r' h'; rw [hax] at h'; simp at h'
      rw [refLinPos_ns A hns]
      simp only [linearAxis, hax, onetoLen, oneTo, one_val] at hhi ⊢
      rw [hax] at hd; rw [← hd]; simp; omega
  · rw [if_neg h]
    have hjl : j = A.data.length := by omega
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · have hns : ∀ r', A.axes ≠ [r'] := by intro r' h'; rw [hax] at h'; simp at h'
      rw [refLinPos_ns A hns]
      simp only [linearAxis, hax, onetoLen, oneTo, one_val] at hhi ⊢
      rw [hax] at hd hb; have : totalLen ([] : List Ax) = 1 := rfl; rw [← hd, wi]; simp; omega
    · simp only [refLinPos, linearAxis, axes1, hax] at hhi ⊢
      rw [wi]; simp; omega
    · have hns : ∀ r', A.axes ≠ [r'] := by intro r' h'; rw [hax] at h'; simp at h'
      rw [refLinPos_ns A hns]
      simp only [linearAxis, hax, onetoLen, oneTo, one_val] at hhi ⊢
      rw [hax] at hd hb; have : totalLen ([] : List Ax) = 1 := rfl; rw [← hd, wi]; simp; omega

/-! ## `CartesianIndices` stepping -/

theorem refCartPos_cons (r : Ax) (rs : List Ax) (i : Int) (is : List Int) :
    refCartPos (r :: rs) (i :: is) = if r.lo.val ≤ i ∧ i ≤ r.hi.val then
      (refCartPos rs is).map (fun p => (i - r.lo.val).toNat + r.len.toNat * p) else none := rfl

theorem ciInc_spec (axs : List Ax) : ∀ (hwf : ∀ r ∈ axs, r.WF) (hne : axs ≠ []) (I : List I64)
    (p : Nat) (hl : I.length = axs.length) (hp : refCartPos axs (I.map (·.val)) = some p),
    (ciInc I axs).1 = decide ((p : Int) + 1 < totalLen axs) ∧
    ((ciInc I axs).1 = true → (ciInc I axs).2.length = axs.length ∧
      refCartPos axs ((ciInc I axs).2.map (·.val)) = some (p + 1)) := by
  induction axs with
  | nil => intro _ hne; exact absurd rfl hne
  | cons r rs ih =>
    intro hwf _ I p hl hp
    have hr := hwf r (by simp)
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    have hld := len_def r
    have hlt := hr.2.2
    rw [tmax_eq] at hlt
    have := bnd r.lo; have := bnd r.hi
    rcases I with _ | ⟨s, ss⟩
    · simp at hl
    have hbs := bnd s
    simp only [List.map_cons, refCartPos] at hp
    split at hp
    · rename_i hin
      obtain ⟨p', hp', hpd⟩ := Option.map_eq_some_iff.mp hp
      have hT := refCartPos_lt rs hrs _ p' hp'
      have hT0 := totalLen_nonneg rs hrs
      rcases rs with _ | ⟨r2, rs'⟩
      · -- one axis
        rcases ss with _ | ⟨s2, ss'⟩
        · have hp'0 := refCartPos_nil_axes_val [] p' hp'
          subst hp'0
          simp only [ciInc, bne, beq64, totalLen, Int.mul_one, Bool.not_eq_true']
          have hpv : (p : Int) = s.val - r.lo.val := by
            rw [← hpd]; simp only [Nat.mul_zero, Nat.add_zero]; rw [cast_toNat (by omega)]
          refine ⟨?_, ?_⟩
          · by_cases h : s.val = r.hi.val <;> simp [h] <;> omega
          · intro hv
            have hne : s.val ≠ r.hi.val := by simpa using hv
            refine ⟨rfl, ?_⟩
            have e : (s + i64 1).val = s.val + 1 := by
              rw [vadd, one_val, wrap_id _ (by omega) (by omega)]
            simp only [List.map_cons, List.map_nil, refCartPos, e]
            rw [if_pos (by omega)]
            simp only [List.all_nil, if_true, Option.map_some, Nat.mul_zero, Nat.add_zero,
              Option.some.injEq]
            omega
        · simp at hl
      · -- two or more axes
        rcases ss with _ | ⟨s2, ss'⟩
        · simp at hl
        have hl' : (s2 :: ss').length = (r2 :: rs').length := by simpa using hl
        have hl1 : 1 ≤ r.len := by omega
        have hpv : (p : Int) = (s.val - r.lo.val) + r.len * p' := by
          rw [← hpd]; push_cast
          rw [cast_toNat (show 0 ≤ s.val - r.lo.val by omega), cast_toNat (show 0 ≤ r.len by omega)]
        have m1 := mul_le_mul_l (show 0 ≤ r.len by omega) (show (p' : Int) + 1 ≤ totalLen (r2 :: rs') by omega)
        have m2 : r.len * ((p' : Int) + 1) = r.len * p' + r.len := by rw [Int.mul_add, Int.mul_one]
        by_cases hs : s.val = r.hi.val
        · have hsr : s = r.hi := ext64 hs
          have hc : (s != r.hi) = false := by simp [hsr]
          obtain ⟨ih1, ih2⟩ := ih hrs (by simp) (s2 :: ss') p' hl' hp'
          simp only [ciInc, hc, Bool.false_eq_true, if_false]
          refine ⟨?_, ?_⟩
          · rw [ih1, totalLen_cons r]
            have e : r.len * (totalLen (r2 :: rs') - ((p' : Int) + 2)) =
                r.len * totalLen (r2 :: rs') - (r.len * p' + r.len * 2) := by
              rw [Int.mul_sub, Int.mul_add]
            simp only [decide_eq_decide]
            constructor
            · intro h
              have := Int.mul_nonneg (show 0 ≤ r.len by omega)
                (show 0 ≤ totalLen (r2 :: rs') - ((p' : Int) + 2) by omega)
              omega
            · intro h
              refine Classical.byContradiction (fun hc => ?_)
              have hT' : (p' : Int) + 1 = totalLen (r2 :: rs') := by omega
              have : r.len * totalLen (r2 :: rs') = r.len * p' + r.len := by
                rw [← hT', Int.mul_add, Int.mul_one]
              omega
          · intro hv
            obtain ⟨hl2, hp2⟩ := ih2 hv
            refine ⟨by simp [hl2], ?_⟩
            simp only [List.map_cons, refCartPos]
            rw [if_pos (by omega), hp2]
            simp only [Option.map_some, Option.some.injEq]
            apply Int.ofNat.inj
            simp only [Int.ofNat_eq_coe]
            push_cast
            rw [cast_toNat (by omega), cast_toNat (show 0 ≤ r.len by omega)]
            omega
        · have hc : (s != r.hi) = true := by
            have : s ≠ r.hi := fun e => hs (congrArg Subtype.val e)
            simp [this]
          simp only [ciInc, hc, if_true]
          refine ⟨?_, ?_⟩
          · rw [totalLen_cons r]; exact (decide_eq_true (by omega)).symm
          · intro _
            refine ⟨by simp [hl'], ?_⟩
            have e : (s + i64 1).val = s.val + 1 := by
              rw [vadd, one_val, wrap_id _ (by omega) (by omega)]
            rw [List.map_cons, refCartPos_cons, e]
            rw [if_pos (by omega)]
            rw [hp']
            simp only [Option.map_some, Option.some.injEq]
            apply Int.ofNat.inj
            simp only [Int.ofNat_eq_coe]
            push_cast
            rw [cast_toNat (by omega), cast_toNat (show 0 ≤ r.len by omega)]
            omega
    · simp at hp

theorem inAx_lo (r : Ax) : inAx r.lo r = decide (r.lo.val ≤ r.hi.val) := by
  simp [inAx, decide_le64]

theorem allIn_los (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) :
    ((axs.map (·.lo)).zip axs).all (fun p => inAx p.1 p.2) = decide (∀ r ∈ axs, 1 ≤ r.len) := by
  induction axs with
  | nil => simp
  | cons r rs ih =>
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih hrs, inAx_lo,
      List.mem_cons, forall_eq_or_imp]
    have := len_def r
    by_cases h : 1 ≤ r.len
    · have : r.lo.val ≤ r.hi.val := by omega
      simp [h, this]
    · have : ¬ r.lo.val ≤ r.hi.val := by omega
      simp [h, this]

/-! ## The iteration invariant -/

/-- State of the `CartesianIndices` iteration before element `j`. -/
def GoodC {α : Type} (A : Arr α) (j : Nat) (st : IterState) : Prop :=
  (j = 0 ∧ st = .cartStart) ∨ (A.axes = [] ∧ j = 1 ∧ st = .cart0 true) ∨
    (A.axes ≠ [] ∧ 1 ≤ j ∧ ∃ I, st = .cart I ∧ I.length = A.axes.length ∧
      refCartPos A.axes (I.map (·.val)) = some (j - 1))

/-- State of `iterate(A)` before element `j`. -/
def Good {α : Type} (A : Arr α) (j : Nat) (st : IterState) : Prop :=
  match A.style with
  | .linear => ∃ k : I64, st = .lin k ∧ k.val = wrapInt .i64 ((linearAxis A).lo.val + j)
  | .cartesian => GoodC A j st

/-- State of the iteration of `eachindex(A)` before index `j`. -/
def GoodE {α : Type} (A : Arr α) (j : Nat) (st : IterState) : Prop :=
  if eachRange A then (j = 0 ∧ st = .rngStart) ∨
      (1 ≤ j ∧ ∃ i : I64, st = .rng i ∧ i.val = (linearAxis A).lo.val + (j - 1))
  else GoodC A j st

theorem data_len_nil {α : Type} (A : Arr α) (hA : A.WF) (hax : A.axes = []) : A.data.length = 1 := by
  have hd := hA.2.1; rw [hax] at hd; simp only [totalLen] at hd; omega

/-- One step of the `CartesianIndices` iteration, shared by `iterate(A)` and
`eachindex(A)`: the yielded index list selects element `j`. -/
theorem cart_step {α : Type} (A : Arr α) (hA : A.WF) (j : Nat) (st : IterState)
    (hg : GoodC A j st) (hj : j ≤ A.data.length) :
    (j < A.data.length → ∃ I st', A.axes.length ≤ I.length ∧ refPos A I = some j ∧ GoodC A (j + 1) st' ∧
      (st = .cartStart ∧ ((A.axes = [] ∧ I = [] ∧ st' = .cart0 true) ∨
          (A.axes ≠ [] ∧ I = A.axes.map (·.lo) ∧
            ((A.axes.map (·.lo)).zip A.axes).all (fun p => inAx p.1 p.2) = true ∧ st' = .cart I)) ∨
        ∃ I0, st = .cart I0 ∧ (ciInc I0 A.axes).1 = true ∧ (ciInc I0 A.axes).2 = I ∧ st' = .cart I)) ∧
    (j = A.data.length →
      (st = .cartStart ∧ A.axes ≠ [] ∧
          ((A.axes.map (·.lo)).zip A.axes).all (fun p => inAx p.1 p.2) = false) ∨
        (st = .cart0 true) ∨ ∃ I0, st = .cart I0 ∧ (ciInc I0 A.axes).1 = false) := by
  have hT0 := totalLen_nonneg _ hA.1
  have hd := hA.2.1
  rcases hg with ⟨rfl, rfl⟩ | ⟨hax, rfl, rfl⟩ | ⟨hne, hj1, I, rfl, hIl, hIp⟩
  · by_cases hax : A.axes = []
    · have h1 := data_len_nil A hA hax
      refine ⟨fun _ => ⟨[], .cart0 true, by simp [hax], ?_, Or.inr (Or.inl ⟨hax, rfl, rfl⟩),
        Or.inl ⟨rfl, Or.inl ⟨hax, rfl, rfl⟩⟩⟩, fun h => by omega⟩
      show refCartPos A.axes [] = some 0
      simp [refCartPos, hax]
    · have hall := allIn_los A.axes hA.1
      have hpos := totalLen_pos_iff A.axes hA.1
      have hlos := refCartPos_los A.axes hA.1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hin : ∀ r ∈ A.axes, 1 ≤ r.len := hpos.mp (by omega)
        refine ⟨A.axes.map (·.lo), .cart (A.axes.map (·.lo)), by simp, ?_, ?_, Or.inl ⟨rfl,
          Or.inr ⟨hax, rfl, by rw [hall]; simpa using hin, rfl⟩⟩⟩
        · rw [refPos_full A _ (by simp), List.map_map]
          rw [show ((·.val) ∘ (·.lo) : Ax → Int) = (fun r => r.lo.val) from rfl, hlos, if_pos hin]
        · refine Or.inr (Or.inr ⟨hax, Nat.le_refl _, _, rfl, by simp, ?_⟩)
          rw [List.map_map, show ((·.val) ∘ (·.lo) : Ax → Int) = (fun r => r.lo.val) from rfl,
            hlos, if_pos hin]
      · left
        refine ⟨rfl, hax, ?_⟩
        rw [hall]
        simp only [decide_eq_false_iff_not]
        intro hin; have := hpos.mpr hin; omega
  · have h1 := data_len_nil A hA hax
    exact ⟨fun h => by omega, fun _ => Or.inr (Or.inl rfl)⟩
  · have hc := ciInc_spec A.axes hA.1 hne I (j - 1) hIl hIp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hv : (ciInc I A.axes).1 = true := by rw [hc.1]; simp only [decide_eq_true_eq]; omega
      obtain ⟨hl2, hp2⟩ := hc.2 hv
      refine ⟨(ciInc I A.axes).2, .cart (ciInc I A.axes).2, by omega, ?_, ?_, Or.inr ⟨I, rfl, hv, rfl, rfl⟩⟩
      · rw [refPos_full A _ hl2, hp2]; congr 1; omega
      · refine Or.inr (Or.inr ⟨hne, by omega, _, rfl, hl2, ?_⟩)
        rw [hp2]; congr 1; omega
    · right; right
      refine ⟨I, rfl, ?_⟩
      rw [hc.1]; simp only [decide_eq_false_iff_not]; omega

theorem iter_step {α : Type} (A : Arr α) (hA : A.WF) (j : Nat) (st : IterState)
    (hg : Good A j st) (hj : j ≤ A.data.length) :
    (∀ h : j < A.data.length, ∃ st', iterateA A st = .ok (some (A.data[j]'h, st')) ∧ Good A (j + 1) st') ∧
    (j = A.data.length → iterateA A st = .ok none) := by
  unfold Good at hg ⊢
  rcases hst : A.style with _ | _ <;> rw [hst] at hg <;> simp only []
  · obtain ⟨k, rfl, hk⟩ := hg
    have hcb := checkboundsBool_eq A hA [k]
    have hstep := refLin_step A hA j hj
    rw [← hk] at hstep
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [if_pos h] at hstep
      have hp : refPos A [k] = some j := hstep
      have hlo := bnd (linearAxis A).lo
      have hhi := linAx_len A hA
      have := bnd (linearAxis A).hi
      have hkv : k.val = (linearAxis A).lo.val + j := by rw [hk, wrap_id _ (by omega) (by omega)]
      refine ⟨.lin (k + i64 1), ?_, k + i64 1, rfl, ?_⟩
      · simp only [iterateA, hcb, hp, Option.isSome_some, if_true,
          getindex_at A hA [k] j (Or.inr rfl) hp, bind_ok]
      · rw [vadd, one_val, hkv]; push_cast; rw [Int.add_assoc]
    · rw [if_neg (by omega)] at hstep
      have hp : refPos A [k] = none := hstep
      simp only [iterateA, hcb, hp, Option.isSome_none, Bool.false_eq_true, if_false]
  · obtain ⟨h1, h2⟩ := cart_step A hA j st hg hj
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨I, st', hle, hp, hg', hcase⟩ := h1 h
      refine ⟨st', ?_, hg'⟩
      rcases hcase with ⟨rfl, ⟨hax, rfl, rfl⟩ | ⟨hax, rfl, hall, rfl⟩⟩ | ⟨I0, rfl, hv, rfl, rfl⟩
      · simp only [iterateA, hax, getindex_at A hA [] j (Or.inl (by simp [hax])) hp, bind_ok]
      · have hga := getindex_at A hA _ j (Or.inl hle) hp
        rcases hax2 : A.axes with _ | ⟨r, rs⟩
        · exact absurd hax2 hax
        · simp only [iterateA, hax2]
          rw [← hax2]
          simp only [hall, if_true, hga, bind_ok]
      · simp only [iterateA, hv, if_true, getindex_at A hA _ j (Or.inl hle) hp, bind_ok]
    · rcases h2 h with ⟨rfl, hax, hall⟩ | rfl | ⟨I0, rfl, hv⟩
      · rcases hax2 : A.axes with _ | ⟨r, rs⟩
        · exact absurd hax2 hax
        · simp only [iterateA, hax2]
          rw [← hax2]
          simp only [hall, Bool.false_eq_true, if_false]
      · rfl
      · simp only [iterateA, hv, Bool.false_eq_true, if_false]

theorem good_start {α : Type} (A : Arr α) : Good A 0 (iterStart A) := by
  unfold Good iterStart
  rcases A.style
  · refine ⟨_, rfl, ?_⟩
    have := bnd (linearAxis A).lo
    rw [show (((0 : Nat)) : Int) = 0 from rfl, Int.add_zero, wrap_id _ (by omega) (by omega)]
  · exact Or.inl ⟨rfl, rfl⟩

theorem iterAll_from {α : Type} (A : Arr α) (hA : A.WF) : ∀ (n j : Nat) (st : IterState),
    Good A j st → j ≤ A.data.length → A.data.length - j < n → iterAll A n st = .ok (A.data.drop j) := by
  intro n
  induction n with
  | zero => intro j st _ _ h; omega
  | succ n ih =>
    intro j st hg hj hn
    obtain ⟨hs1, hs2⟩ := iter_step A hA j st hg hj
    by_cases h : j < A.data.length
    · obtain ⟨st', hst, hg'⟩ := hs1 h
      rw [iterAll, hst, bind_ok]
      simp only []
      rw [ih (j + 1) st' hg' (by omega) (by omega), bind_ok, ← List.drop_eq_getElem_cons h]
    · rw [iterAll, hs2 (by omega), bind_ok]
      simp only []
      rw [List.drop_of_length_le (by omega)]

theorem iterateColumnMajor_proven : IterateColumnMajor := by
  intro α A hA
  rw [iterAll_from A hA (fuelOf A) 0 (iterStart A) (good_start A) (by omega) (by simp [fuelOf]),
    List.drop_zero]

/-! ## isequal and == -/

theorem axEq_len {r s : Ax} (hr : r.WF) (hs : s.WF) (h : axEq r s = true) : r.len = s.len := by
  have := len_def r; have := len_def s
  have hr0 := hr.2.1; have hs0 := hs.2.1
  have lr := axLength_val hr; have ls := axLength_val hs
  unfold axEq axIsEmpty at h
  simp only [decide_lt64, beq64, one_val] at h
  split at h
  · rename_i he; simp only [decide_eq_true_eq] at he h; omega
  · split at h
    · rename_i h1; simp only [decide_eq_true_eq] at h1; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem axesEq_total (axs bxs : List Ax) (ha : ∀ r ∈ axs, r.WF) (hb : ∀ r ∈ bxs, r.WF)
    (h : axesEq axs bxs = true) : totalLen axs = totalLen bxs := by
  induction axs generalizing bxs with
  | nil => cases bxs with
    | nil => rfl
    | cons _ _ => simp [axesEq] at h
  | cons r rs ih =>
    cases bxs with
    | nil => simp [axesEq] at h
    | cons s ss =>
      simp only [axesEq, Bool.and_eq_true] at h
      simp only [totalLen_cons]
      rw [axEq_len (ha r (by simp)) (hb s (by simp)) h.1,
        ih ss (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) h.2]

theorem allPairs_cons {α : Type} (p : α → α → Bool) (x y : α) (xs ys : List α) :
    allPairs p (x :: xs) (y :: ys) = (p x y && allPairs p xs ys) := by
  simp [allPairs]

theorem zip_isequal {α : Type} (iseq : α → α → Bool) (A B : Arr α) (hA : A.WF) (hB : B.WF)
    (hl : A.data.length = B.data.length) : ∀ (n j : Nat) (sa sb : IterState),
    Good A j sa → Good B j sb → j ≤ A.data.length → A.data.length - j < n →
    zipLoop A B (fun a b => if !iseq a b then some false else none) true n sa sb =
      .ok (allPairs iseq (A.data.drop j) (B.data.drop j)) := by
  intro n
  induction n with
  | zero => intro j _ _ _ _ _ h; omega
  | succ n ih =>
    intro j sa sb ga gb hj hn
    obtain ⟨a1, a2⟩ := iter_step A hA j sa ga hj
    obtain ⟨b1, b2⟩ := iter_step B hB j sb gb (by omega)
    by_cases h : j < A.data.length
    · obtain ⟨sa', hsa, ga'⟩ := a1 h
      obtain ⟨sb', hsb, gb'⟩ := b1 (by omega)
      rw [zipLoop, hsa, bind_ok]; simp only []
      rw [hsb, bind_ok]; simp only []
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons (show j < B.data.length by omega),
        allPairs_cons]
      by_cases he : iseq (A.data[j]'h) (B.data[j]'(by omega)) = true
      · simp only [he, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
        exact ih (j + 1) sa' sb' ga' gb' (by omega) (by omega)
      · simp only [Bool.not_eq_true] at he
        simp [he]
    · rw [zipLoop, a2 (by omega), bind_ok]; simp only []
      rw [List.drop_of_length_le (by omega), List.drop_of_length_le (show B.data.length ≤ j by omega)]
      rfl

theorem isequalElementwise_proven : IsequalElementwise := by
  intro α iseq A B hA hB
  unfold isequalA
  by_cases hax : axesEq A.axes B.axes = true
  · have hl : A.data.length = B.data.length := by
      have := axesEq_total _ _ hA.1 hB.1 hax
      have := hA.2.1; have := hB.2.1; omega
    simp only [hax, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
    rw [zip_isequal iseq A B hA hB hl (fuelOf A) 0 _ _ (good_start A) (good_start B) (by omega)
      (by simp [fuelOf]), List.drop_zero, List.drop_zero]
  · simp only [Bool.not_eq_true] at hax
    simp [hax]

theorem eq_loop {α : Type} (eq : Eq3 α) (A B : Arr α) (hA : A.WF) (hB : B.WF)
    (hl : A.data.length = B.data.length) : ∀ (n j : Nat) (m : Bool) (sa sb : IterState),
    Good A j sa → Good B j sb → j ≤ A.data.length → A.data.length - j < n →
    eqLoop A B eq n m sa sb =
      .ok (if ((A.data.drop j).zip (B.data.drop j)).any (fun q => eq q.1 q.2 == some false) then some false
        else if m || ((A.data.drop j).zip (B.data.drop j)).any (fun q => eq q.1 q.2 == none) then none
        else some true) := by
  intro n
  induction n with
  | zero => intro j _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro j m sa sb ga gb hj hn
    obtain ⟨a1, a2⟩ := iter_step A hA j sa ga hj
    obtain ⟨b1, b2⟩ := iter_step B hB j sb gb (by omega)
    by_cases h : j < A.data.length
    · obtain ⟨sa', hsa, ga'⟩ := a1 h
      obtain ⟨sb', hsb, gb'⟩ := b1 (by omega)
      rw [eqLoop, hsa, bind_ok]; simp only []
      rw [hsb, bind_ok]; simp only []
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons (show j < B.data.length by omega)]
      simp only [List.zip_cons_cons, List.any_cons]
      have e1 : ((none : Option Bool) == some false) = false := rfl
      have e2 : ((none : Option Bool) == none) = true := rfl
      have e3 : ((some true : Option Bool) == some false) = false := rfl
      have e4 : ((some true : Option Bool) == none) = false := rfl
      have e5 : ((some false : Option Bool) == some false) = true := rfl
      split
      · rename_i heq
        rw [ih (j + 1) true sa' sb' ga' gb' (by omega) (by omega)]
        simp only [heq, e1, e2, Bool.false_or, Bool.true_or, Bool.or_true]
      · rename_i heq
        simp only [heq, e5, Bool.true_or, if_true]
      · rename_i heq
        rw [ih (j + 1) m sa' sb' ga' gb' (by omega) (by omega)]
        simp only [heq, e3, e4, Bool.false_or]
    · rw [eqLoop, a2 (by omega), bind_ok]; simp only []
      rw [List.drop_of_length_le (by omega), List.drop_of_length_le (show B.data.length ≤ j by omega)]
      cases m <;> simp

theorem eqElementwise_proven : EqElementwise := by
  intro α eq A B hA hB
  unfold eqA
  by_cases hax : axesEq A.axes B.axes = true
  · have hl : A.data.length = B.data.length := by
      have := axesEq_total _ _ hA.1 hB.1 hax
      have := hA.2.1; have := hB.2.1; omega
    simp only [hax, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rw [eq_loop eq A B hA hB hl (fuelOf A) 0 false _ _ (good_start A) (good_start B) (by omega)
      (by simp [fuelOf]), List.drop_zero, List.drop_zero]
    simp only [eq3List, Bool.false_or]
  · simp only [Bool.not_eq_true] at hax
    simp [hax]

/-! ## `eachindex` stepping and `map!` -/

theorem eachindexStep_data {α : Type} (A : Arr α) (d : List α) (st : IterState) :
    eachindexStep { A with data := d } st = eachindexStep A st := by
  cases st <;> rfl

theorem refPos_data {α : Type} (A : Arr α) (d : List α) (I : List I64) :
    refPos { A with data := d } I = refPos A I := rfl

theorem goodE_start {α : Type} (A : Arr α) : GoodE A 0 (eachStart A) := by
  unfold GoodE eachStart
  by_cases h : eachRange A = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false]; exact Or.inl ⟨rfl, rfl⟩

theorem each_step {α : Type} (A : Arr α) (hA : A.WF) (j : Nat) (st : IterState)
    (hg : GoodE A j st) (hj : j ≤ A.data.length) :
    (j < A.data.length → ∃ I st', eachindexStep A st = some (I, st') ∧
      (A.axes.length ≤ I.length ∨ I.length = 1) ∧ refPos A I = some j ∧ GoodE A (j + 1) st') ∧
    (j = A.data.length → eachindexStep A st = none) := by
  unfold GoodE at hg ⊢
  by_cases hst : eachRange A = true
  · simp only [hst, if_true] at hg ⊢
    have hhi := linAx_len A hA
    have hlo := bnd (linearAxis A).lo
    have hhb := bnd (linearAxis A).hi
    have hstep := refLin_step A hA j hj
    rcases hg with ⟨rfl, rfl⟩ | ⟨hj1, i, rfl, hi⟩
    · have hw : wrapInt .i64 ((linearAxis A).lo.val + ((0 : Nat) : Int)) = (linearAxis A).lo.val := by
        rw [show (((0 : Nat)) : Int) = 0 from rfl, Int.add_zero, wrap_id _ (by omega) (by omega)]
      rw [hw] at hstep
      refine ⟨fun h => ⟨[(linearAxis A).lo], .rng (linearAxis A).lo, ?_, Or.inr rfl, ?_, ?_⟩, fun h => ?_⟩
      · have : axIsEmpty (linearAxis A) = false := by
          simp only [axIsEmpty, decide_eq_false_iff_not]
          show ¬ (linearAxis A).hi.val < (linearAxis A).lo.val
          omega
        simp only [eachindexStep, this]; rfl
      · show refLinPos A (linearAxis A).lo.val = some 0
        rw [hstep, if_pos h]
      · exact Or.inr ⟨Nat.le_refl _, _, rfl, by simp⟩
      · have : axIsEmpty (linearAxis A) = true := by
          simp only [axIsEmpty, decide_eq_true_eq]
          show (linearAxis A).hi.val < (linearAxis A).lo.val
          omega
        simp only [eachindexStep, this]; rfl
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hne : i ≠ (linearAxis A).hi := by
          intro e; have := congrArg Subtype.val e; omega
        have hv : (i + i64 1).val = (linearAxis A).lo.val + j := by
          rw [vadd, one_val, hi, wrap_id _ (by omega) (by omega)]; omega
        refine ⟨[i + i64 1], .rng (i + i64 1), ?_, Or.inr rfl, ?_, Or.inr ⟨by omega, _, rfl, by rw [hv]; push_cast; omega⟩⟩
        · simp only [eachindexStep, hne, if_false]
        · show refLinPos A (i + i64 1).val = some j
          rw [hv, ← wrap_id ((linearAxis A).lo.val + j) (by omega) (by omega), hstep, if_pos h]
      · have he : i = (linearAxis A).hi := Subtype.ext (by omega)
        simp only [eachindexStep, he, if_true]
  · simp only [hst, Bool.false_eq_true, if_false] at hg ⊢
    obtain ⟨h1, h2⟩ := cart_step A hA j st hg hj
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨I, st', hle, hp, hg', hcase⟩ := h1 h
      refine ⟨I, st', ?_, Or.inl hle, hp, hg'⟩
      rcases hcase with ⟨rfl, ⟨hax, rfl, rfl⟩ | ⟨hax, rfl, hall, rfl⟩⟩ | ⟨I0, rfl, hv, rfl, rfl⟩
      · simp only [eachindexStep, hax]
      · rcases hax2 : A.axes with _ | ⟨r, rs⟩
        · exact absurd hax2 hax
        · simp only [eachindexStep, hax2]
          rw [← hax2]
          simp only [hall, if_true]
      · simp only [eachindexStep, hv, if_true]
    · rcases h2 h with ⟨rfl, hax, hall⟩ | rfl | ⟨I0, rfl, hv⟩
      · rcases hax2 : A.axes with _ | ⟨r, rs⟩
        · exact absurd hax2 hax
        · simp only [eachindexStep, hax2]
          rw [← hax2]
          simp only [hall, Bool.false_eq_true, if_false]
      · rfl
      · simp only [eachindexStep, hv, Bool.false_eq_true, if_false]

theorem prefix_len {α : Type} (f : α → α) (xs ys : List α) (j : Nat) (hx : j ≤ xs.length)
    (hy : j ≤ ys.length) : ((xs.take j).map f ++ ys.drop j).length = ys.length := by
  simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

theorem set_prefix {α : Type} (f : α → α) (xs ys : List α) (j : Nat) (hx : j < xs.length)
    (hy : j < ys.length) :
    ((xs.take j).map f ++ ys.drop j).set j (f (xs[j]'hx)) = (xs.take (j + 1)).map f ++ ys.drop (j + 1) := by
  have hl : ((xs.take j).map f).length = j := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, List.drop_eq_getElem_cons hy,
    List.set_cons_zero, List.take_succ, List.getElem?_eq_getElem hx, List.map_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]

theorem mapLoop_from {α : Type} (f : α → α) (dest A : Arr α) (hd : dest.WF) (hA : A.WF) :
    ∀ (n j : Nat) (sd sa : IterState), GoodE dest j sd → GoodE A j sa →
      j ≤ dest.data.length → j ≤ A.data.length → dest.data.length - j < n →
      mapLoop f A n { dest with data := (A.data.take j).map f ++ dest.data.drop j } sd sa =
        .ok { dest with data := (A.data.take dest.data.length).map f ++ dest.data.drop A.data.length } := by
  intro n
  induction n with
  | zero => intro j sd sa _ _ _ _ h; omega
  | succ n ih =>
    intro j sd sa gd ga hjd hja hn
    by_cases h1 : j < dest.data.length
    · by_cases h2 : j < A.data.length
      · have hn1 : dest.data.length - (j + 1) < n := by omega
        have hj1 : j + 1 ≤ dest.data.length := h1
        have hj2 : j + 1 ≤ A.data.length := h2
        have hlen := prefix_len f A.data dest.data j hja hjd
        have hD : ({ dest with data := (A.data.take j).map f ++ dest.data.drop j } : Arr α).WF :=
          ⟨hd.1, by rw [← hd.2.1]; exact congrArg _ hlen, hd.2.2⟩
        obtain ⟨d1, -⟩ := each_step dest hd j sd gd hjd
        obtain ⟨a1, -⟩ := each_step A hA j sa ga hja
        rw [mapLoop, eachindexStep_data]
        obtain ⟨I, sd', hsd, hIl, hIp, gd'⟩ := d1 h1
        rw [hsd]
        simp only []
        obtain ⟨J, sa', hsa, hJl, hJp, ga'⟩ := a1 h2
        rw [hsa]
        simp only []
        rw [getindex_at A hA J j hJl hJp, bind_ok,
          setindex_at _ hD I j _ hIl (by rw [refPos_data]; exact hIp), bind_ok]
        simp only []
        rw [set_prefix f A.data dest.data j h2 h1]
        exact ih (j + 1) sd' sa' gd' ga' hj1 hj2 hn1
      · have e3 : j = A.data.length := by omega
        have e1 : A.data.take j = A.data := List.take_of_length_le (by omega)
        have e2 : A.data.take dest.data.length = A.data := List.take_of_length_le (by omega)
        obtain ⟨d1, -⟩ := each_step dest hd j sd gd hjd
        obtain ⟨-, a2⟩ := each_step A hA j sa ga hja
        rw [mapLoop, eachindexStep_data]
        obtain ⟨I, sd', hsd, -, -, -⟩ := d1 h1
        rw [hsd]
        simp only []
        rw [a2 e3]
        simp only []
        rw [e1, e2, e3]
    · have e3 : j = dest.data.length := by omega
      have e4 : dest.data.drop A.data.length = [] := List.drop_of_length_le (by omega)
      obtain ⟨-, d2⟩ := each_step dest hd j sd gd hjd
      rw [mapLoop, eachindexStep_data, d2 e3]
      simp only []
      rw [e3, e4, List.drop_length]

theorem mapBangPrefix_proven : MapBangPrefix := by
  intro α f dest A hd hA
  have h := mapLoop_from f dest A hd hA (fuelOf dest) 0 _ _ (goodE_start dest) (goodE_start A)
    (by omega) (by omega) (by simp [fuelOf])
  have e : ({ dest with data := (A.data.take 0).map f ++ dest.data.drop 0 } : Arr α) = dest := by
    cases dest; simp
  rw [e] at h
  exact h

theorem eachAll_from {α : Type} (A : Arr α) (hA : A.WF) : ∀ (n j : Nat) (st : IterState),
    GoodE A j st → j ≤ A.data.length → A.data.length - j < n →
    (eachAll A n st).length = A.data.length - j ∧
    ∀ (k : Nat) (h : k < (eachAll A n st).length), refPos A ((eachAll A n st)[k]'h) = some (j + k) := by
  intro n
  induction n with
  | zero => intro j st _ _ h; omega
  | succ n ih =>
    intro j st hg hj hn
    by_cases h1 : j < A.data.length
    · have hj1 : j + 1 ≤ A.data.length := h1
      have hn1 : A.data.length - (j + 1) < n := by omega
      have hlen : A.data.length - (j + 1) + 1 = A.data.length - j := by omega
      obtain ⟨s1, -⟩ := each_step A hA j st hg hj
      obtain ⟨I, st', hs, -, hp, hg'⟩ := s1 h1
      obtain ⟨ihl, ihp⟩ := ih (j + 1) st' hg' hj1 hn1
      have e : eachAll A (n + 1) st = I :: eachAll A n st' := by
        rw [eachAll, hs]
      rw [e]
      refine ⟨by rw [List.length_cons, ihl, hlen], fun k hk => ?_⟩
      rcases k with _ | k
      · simpa using hp
      · rw [List.getElem_cons_succ, ihp k (by simpa using hk)]
        congr 1; omega
    · have e3 : j = A.data.length := by omega
      obtain ⟨-, s2⟩ := each_step A hA j st hg hj
      have e : eachAll A (n + 1) st = [] := by rw [eachAll, s2 e3]
      rw [e]
      exact ⟨by simp; omega, fun k hk => absurd hk (by simp)⟩

theorem eachindexEnumerates_proven : EachindexEnumerates := by
  intro α A hA
  obtain ⟨hl, hp⟩ := eachAll_from A hA (fuelOf A) 0 (eachStart A) (goodE_start A)
    (Nat.zero_le _) (by simp [fuelOf])
  exact ⟨by rw [hl]; rfl, fun k h => by rw [hp k h, Nat.zero_add]⟩

/-! ## `cmp` and `isless` of vectors -/

/-- Reference semantics of a `zip` loop over two element lists. -/
def zipRef {α β γ : Type} (step : α → β → Option γ) (done : γ) : List α → List β → γ
  | x :: xs, y :: ys => match step x y with
    | some r => r
    | none => zipRef step done xs ys
  | _, _ => done

theorem zipLoop_spec {α β γ : Type} (A : Arr α) (B : Arr β) (hA : A.WF) (hB : B.WF)
    (step : α → β → Option γ) (done : γ) : ∀ (n j : Nat) (sa sb : IterState),
    Good A j sa → Good B j sb → j ≤ A.data.length → j ≤ B.data.length → A.data.length - j < n →
    zipLoop A B step done n sa sb = .ok (zipRef step done (A.data.drop j) (B.data.drop j)) := by
  intro n
  induction n with
  | zero => intro j _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro j sa sb ga gb hja hjb hn
    obtain ⟨a1, a2⟩ := iter_step A hA j sa ga hja
    obtain ⟨b1, b2⟩ := iter_step B hB j sb gb hjb
    by_cases h : j < A.data.length
    · obtain ⟨sa', hsa, ga'⟩ := a1 h
      rw [zipLoop, hsa, bind_ok]; simp only []
      rw [List.drop_eq_getElem_cons h]
      by_cases h2 : j < B.data.length
      · obtain ⟨sb', hsb, gb'⟩ := b1 h2
        rw [hsb, bind_ok]; simp only []
        rw [List.drop_eq_getElem_cons h2, zipRef]
        have hj1 : j + 1 ≤ A.data.length := h
        have hj2 : j + 1 ≤ B.data.length := h2
        have hn1 : A.data.length - (j + 1) < n := by omega
        rcases hst : step (A.data[j]'h) (B.data[j]'h2) with _ | r
        · exact ih (j + 1) sa' sb' ga' gb' hj1 hj2 hn1
        · rfl
      · rw [b2 (by omega), bind_ok]; simp only []
        rw [List.drop_of_length_le (show B.data.length ≤ j by omega)]
        rfl
    · rw [zipLoop, a2 (by omega), bind_ok]; simp only []
      rw [List.drop_of_length_le (show A.data.length ≤ j by omega)]
      cases B.data.drop j <;> rfl

theorem zipRef_lex {α : Type} (iseq lt : α → α → Bool) : ∀ (xs ys : List α) (d : Int),
    d = (if xs.length < ys.length then -1 else if ys.length < xs.length then 1 else 0) →
    zipRef (fun a b => if !iseq a b then some (if lt a b then -1 else 1) else none) d xs ys =
      lexCmp iseq lt xs ys := by
  intro xs
  induction xs with
  | nil => intro ys d hd; cases ys <;> simp_all [zipRef, lexCmp]
  | cons x xs ih =>
    intro ys d hd
    cases ys with
    | nil => simp_all [zipRef, lexCmp]
    | cons y ys =>
      simp only [zipRef, lexCmp]
      by_cases he : iseq x y = true
      · simp only [he, Bool.not_true, Bool.false_eq_true, if_false]
        apply ih ys d
        simp only [List.length_cons] at hd
        rw [hd]
        repeat' split
        all_goals omega
      · simp only [Bool.not_eq_true] at he
        simp only [he, Bool.not_false, if_true]

theorem cmpI_val (x y : I64) : cmpI x y = if x.val < y.val then -1 else if y.val < x.val then 1 else 0 := rfl

theorem cmpVectorOrder_proven : CmpVectorOrder := by
  intro α iseq lt A B hA hB _ _
  have hc : cmpV iseq lt A B = .ok (if (linearAxis A).lo.val < (linearAxis B).lo.val then -1
      else if (linearAxis B).lo.val < (linearAxis A).lo.val then 1
      else lexCmp iseq lt A.data B.data) := by
    unfold cmpV
    by_cases he : (linearAxis A).lo.val = (linearAxis B).lo.val
    · have hb : ((linearAxis A).lo == (linearAxis B).lo) = true := by rw [beq64]; simp [he]
      simp only [hb, Bool.not_true, Bool.false_eq_true, if_false]
      rw [if_neg (by omega), if_neg (by omega)]
      rw [zipLoop_spec A B hA hB _ _ (fuelOf A) 0 (iterStart A) (iterStart B) (good_start A)
        (good_start B) (Nat.zero_le _) (Nat.zero_le _) (by simp [fuelOf]), List.drop_zero, List.drop_zero]
      congr 1
      apply zipRef_lex
      rw [cmpI_val, lengthA_val A hA, lengthA_val B hB]
      repeat' split
      all_goals omega
    · have hb : ((linearAxis A).lo == (linearAxis B).lo) = false := by rw [beq64]; simp [he]
      simp only [hb, Bool.not_false, if_true, cmpI_val]
      congr 1
      repeat' split
      all_goals omega
  refine ⟨hc, ?_⟩
  simp only [islessV, hc, bind_ok]

end JuliaLean.AbstractArraySpecs
