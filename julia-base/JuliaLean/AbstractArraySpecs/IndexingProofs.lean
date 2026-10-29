import JuliaLean.AbstractArraySpecs.IndexProofs

/-! Proofs of the indexing, `first`/`last` and `length`/`isempty` contracts. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

theorem exists_single {β : Type} {l : List β} (h : l.length = 1) : ∃ r, l = [r] := by
  rcases l with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · simp at h
  · exact ⟨r, rfl⟩
  · simp at h

theorem refGet_eq {α : Type} (A : Arr α) (I : List I64) : refGet A I = elemAt A (refPos A I) := by
  unfold refGet elemAt; rcases refPos A I with _ | p <;> rfl

theorem refSet_eq {α : Type} (A : Arr α) (v : α) (I : List I64) :
    refSet A v I = storeAt A (refPos A I) v := by
  unfold refSet storeAt; rcases refPos A I with _ | p <;> rfl

theorem checkbounds_eq {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) :
    checkbounds A I = (if (refPos A I).isSome then .ok () else .error .boundsError) :=
  (checkboundsAgreesWithReference_proven A I hA).2

/-! ## Index conversion in the fallbacks -/

theorem refLinPos_ns {α : Type} (A : Arr α) (h : ∀ r, A.axes ≠ [r]) (k : Int) :
    refLinPos A k = if 1 ≤ k ∧ k ≤ totalLen A.axes then some (k - 1).toNat else none := by
  unfold refLinPos
  split
  · rename_i r hr; exact absurd hr (h r)
  · rfl

theorem toLinearIndex_ok {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) (h1 : I.length ≠ 1)
    (p : Nat) (hp : refCartPos A.axes (I.map (·.val)) = some p) :
    ∃ k, toLinearIndex A I = .ok k ∧ refLinPos A k.val = some p := by
  have hd := hA.2.1
  have hb := hA.2.2
  rw [tmax_eq] at hb
  match I, h1 with
  | [], _ =>
    obtain ⟨hp0, hall⟩ := refCartPos_nil (by simpa using hp)
    subst hp0
    have hT := totalLen_of_all1 _ hall
    refine ⟨firstLinear A, rfl, ?_⟩
    unfold firstLinear linearAxis refLinPos
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · simp [onetoLen, oneTo, one_val, totalLen]
    · rw [hax] at hT
      simp only [totalLen_cons, totalLen, Int.mul_one] at hT
      have := len_def r
      simp only [axes1, hax]
      rw [if_pos (by omega)]; simp
    · rw [hax] at hT
      simp only [onetoLen, oneTo, one_val]
      rw [if_pos (by omega)]; simp
  | [_], h => exact absurd rfl h
  | i :: i2 :: I', _ =>
    by_cases hN : A.axes.length = 1
    · obtain ⟨r, hax⟩ : ∃ r, A.axes = [r] := exists_single hN
      refine ⟨i, by simp [toLinearIndex, hN], ?_⟩
      rw [hax] at hp
      simp only [List.map_cons, refCartPos] at hp
      split at hp
      · rename_i hin
        obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        have := refCartPos_nil_axes_val ((i2 :: I').map (fun x : I64 => x.val)) p' hp'
        subst this
        simp only [refLinPos, hax, if_pos hin]
        simp
      · simp at hp
    · have hlt := refCartPos_lt _ hA.1 _ p hp
      have h0 := Int.natCast_nonneg p
      have hv := sub2indRecurse_val (i :: i2 :: I') A.axes hA.1 p hp (i64 1) (i64 1)
        (by rw [one_val]; omega) (by rw [one_val]; omega)
        (by rw [one_val, tmax_eq]; omega) (by rw [one_val, tmax_eq]; omega)
      rw [one_val] at hv
      refine ⟨sub2indRecurse A.axes (i64 1) (i64 1) (i :: i2 :: I'), ?_, ?_⟩
      · simp only [toLinearIndex, if_neg hN, sub2ind]
        rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
        · rfl
        · rw [hax] at hN; simp at hN
        · rfl
      · unfold refLinPos
        rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
        · rw [hax] at hlt hv
          simp only [hv]; rw [if_pos (by omega)]; simp <;> omega
        · rw [hax] at hN; simp at hN
        · rw [hax] at hlt hv
          simp only [hv]; rw [if_pos (by omega)]; simp <;> omega

theorem toSubscript_extra {α : Type} (A : Arr α) (I : List I64)
    (hlen : A.axes.length < I.length) (h1 : I.length ≠ 1)
    (p : Nat) (hp : refCartPos A.axes (I.map (·.val)) = some p) :
    ∃ J, toSubscriptIndices A I = .ok J ∧ J.length = A.axes.length ∧
      refCartPos A.axes (J.map (·.val)) = some p := by
  rcases hax : A.axes with _ | ⟨r, rs⟩
  · refine ⟨[], by simp [toSubscriptIndices, hax], rfl, ?_⟩
    rw [hax] at hp
    have := refCartPos_nil_axes_val _ p hp
    subst this; rfl
  · rw [hax] at hlen hp
    match I, h1, hlen with
    | i :: i2 :: I', _, hlen =>
      refine ⟨(i :: i2 :: I').take (r :: rs).length, ?_, ?_, ?_⟩
      · simp only [toSubscriptIndices, hax]
        rw [if_neg (by omega)]
      · simp only [List.length_take]; omega
      · rw [List.map_take]
        exact refCartPos_take (r :: rs) _ p hp (by simp only [List.length_map]; omega)

theorem toSubscript_linear {α : Type} (A : Arr α) (hA : A.WF) (k : I64)
    (hax2 : 2 ≤ A.axes.length) (p : Nat) (hp : refLinPos A k.val = some p) :
    ∃ J, toSubscriptIndices A [k] = .ok J ∧ J.length = A.axes.length ∧
      refCartPos A.axes (J.map (·.val)) = some p := by
  have hb := hA.2.2
  have hbk := bnd k
  rw [tmax_eq] at hb
  rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · rw [hax] at hax2; simp at hax2
  · rw [hax] at hax2; simp at hax2
  · have hns : ∀ r', A.axes ≠ [r'] := by intro r' h'; rw [hax] at h'; simp at h'
    rw [refLinPos_ns A hns k.val, hax] at hp
    rw [hax] at hb
    split at hp
    · rename_i hin
      simp only [Option.some.injEq] at hp
      subst hp
      have hk1 : (k - i64 1).val = k.val - 1 := by
        rw [vsub, one_val, wrap_id _ (by omega) (by omega)]
      obtain ⟨J, hJ, hl, hpos⟩ := ind2subRecurse_ok (r :: r2 :: rs) (by simp) (hax ▸ hA.1)
        (k - i64 1) (by omega) (by omega) (by rw [tmax_eq]; omega)
      refine ⟨J, ?_, hl, ?_⟩
      · simp only [toSubscriptIndices, hax, ind2sub]; exact hJ
      · rw [hpos, hk1]
    · simp at hp

/-! ## getindex, setindex!, get -/

theorem elemAt_some_ok {α : Type} (A : Arr α) (p : Nat) (hp : p < A.data.length) :
    ∃ x, elemAt A (some p) = .ok x := ⟨A.data[p], by simp [elemAt, List.getElem?_eq_getElem hp]⟩

theorem getDefault_of {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) (d : α)
    (hg : getindex A I = refGet A I) : getDefault A I d = refGetDefault A I d := by
  unfold getDefault refGetDefault
  rw [checkboundsBool_eq A hA I, hg, refGet_eq]
  rcases hq : refPos A I with _ | p
  · rfl
  · obtain ⟨x, hx⟩ := elemAt_some_ok A p (refPos_lt A hA I p hq)
    simp [hx]

theorem indexing_linear {α : Type} (A : Arr α) (hA : A.WF) (k : I64) :
    getindex A [k] = refGet A [k] ∧ ∀ v, setindex A v [k] = refSet A v [k] := by
  simp only [refGet_eq, refSet_eq]
  rcases hst : A.style with _ | _
  · simp [getindex, setindex, hst, canonGetL, canonSetL, refPos]
  · by_cases hN : A.axes.length = 1
    · obtain ⟨r, hax⟩ : ∃ r, A.axes = [r] := exists_single hN
      have e : refCartPos A.axes [k.val] = refLinPos A k.val := by
        simp only [refLinPos, hax, refCartPos_single]
      simp only [getindex, setindex, hst, List.length_singleton, hN, if_true, canonGetC, canonSetC,
        List.map_cons, List.map_nil, e, refPos]
      exact ⟨trivial, fun _ => trivial⟩
    · have hN' : ¬ (1 = A.axes.length) := fun h => hN h.symm
      have hcb := checkbounds_eq A hA [k]
      rcases hq : refPos A [k] with _ | p
      · rw [hq] at hcb
        simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hcb
        simp only [getindex, setindex, hst, List.length_singleton, if_neg hN', hcb, bind_err,
          elemAt, storeAt, hq]
        refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
      · rw [hq] at hcb
        simp only [Option.isSome_some, if_true] at hcb
        have hlin : refLinPos A k.val = some p := hq
        have hlt := refPos_lt A hA [k] p hq
        by_cases h0 : A.axes.length = 0
        · have hax : A.axes = [] := List.length_eq_zero_iff.mp h0
          have hp0 : p = 0 := by
            have hd := hA.2.1
            rw [hax] at hd
            simp only [totalLen] at hd
            omega
          subst hp0
          have ht : toSubscriptIndices A [k] = .ok [] := by simp [toSubscriptIndices, hax]
          simp only [getindex, setindex, hst, List.length_singleton, if_neg hN', hcb, bind_ok, ht,
            canonGetC, canonSetC, List.length_nil, hax, List.map_nil, hq]
          refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
        · obtain ⟨J, hJ, hl, hpos⟩ := toSubscript_linear A hA k (by omega) p hlin
          simp only [getindex, setindex, hst, List.length_singleton, if_neg hN', hcb, bind_ok, hJ,
            canonGetC, canonSetC, hl, if_true, hpos, hq]
          refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl

theorem indexing_extra {α : Type} (A : Arr α) (hA : A.WF) (I : List I64)
    (hlen : A.axes.length ≤ I.length) :
    getindex A I = refGet A I ∧ ∀ v, setindex A v I = refSet A v I := by
  by_cases h1 : I.length = 1
  · obtain ⟨k, rfl⟩ := exists_single h1
    exact indexing_linear A hA k
  simp only [refGet_eq, refSet_eq, refPos_cart A I h1]
  have hcb := checkbounds_eq A hA I
  rw [refPos_cart A I h1] at hcb
  rcases hst : A.style with _ | _
  · rcases hq : refCartPos A.axes (I.map (·.val)) with _ | p
    · rw [hq] at hcb
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hcb
      simp only [getindex, setindex, hst, if_neg h1, hcb, bind_err, elemAt, storeAt, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
    · rw [hq] at hcb
      simp only [Option.isSome_some, if_true] at hcb
      obtain ⟨k, hk, hlin⟩ := toLinearIndex_ok A hA I h1 p hq
      simp only [getindex, setindex, hst, if_neg h1, hcb, bind_ok, hk, canonGetL, canonSetL, hlin, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
  · by_cases hN : I.length = A.axes.length
    · simp only [getindex, setindex, hst, if_pos hN, canonGetC, canonSetC]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
    · rcases hq : refCartPos A.axes (I.map (·.val)) with _ | p
      · rw [hq] at hcb
        simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hcb
        simp only [getindex, setindex, hst, if_neg hN, hcb, bind_err, elemAt, storeAt, hq]
        refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
      · rw [hq] at hcb
        simp only [Option.isSome_some, if_true] at hcb
        obtain ⟨J, hJ, hl, hpos⟩ := toSubscript_extra A I (by omega) h1 p hq
        simp only [getindex, setindex, hst, if_neg hN, hcb, bind_ok, hJ, canonGetC, canonSetC,
          hl, if_true, hpos, hq]
        refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl

theorem linearIndexingAgrees_proven : LinearIndexingAgrees := by
  intro α A k v d hA
  obtain ⟨hg, hs⟩ := indexing_linear A hA k
  exact ⟨hg, hs v, getDefault_of A hA [k] d hg⟩

theorem cartesianIndexingAgrees_proven : CartesianIndexingAgrees := by
  intro α A I v d hA hlen
  obtain ⟨hg, hs⟩ := indexing_extra A hA I hlen
  exact ⟨hg, hs v, getDefault_of A hA I d hg⟩

/-! ## first, last -/

theorem data_nil_iff {α : Type} (A : Arr α) (hA : A.WF) : A.data = [] ↔ totalLen A.axes = 0 := by
  have hd := hA.2.1
  constructor
  · intro h; rw [h] at hd; simp at hd; omega
  · intro h; rw [h] at hd; exact List.length_eq_zero_iff.mp (by omega)

theorem refLin_first {α : Type} (A : Arr α) (hA : A.WF) :
    refLinPos A (linearAxis A).lo.val = if A.data = [] then none else some 0 := by
  have hT0 := totalLen_nonneg _ hA.1
  have hd := hA.2.1
  unfold linearAxis refLinPos
  by_cases h : A.data = []
  · have h0 : A.data.length = 0 := by simp [h]
    rw [if_pos h]
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · rw [hax] at hd; simp only [totalLen] at hd; omega
    · rw [hax] at hd; simp only [totalLen_cons, totalLen, Int.mul_one, len_def] at hd
      simp only [axes1, hax]; rw [if_neg (by omega)]
    · rw [hax] at hd
      simp only [onetoLen, oneTo, one_val]; rw [if_neg (by omega)]
  · have h0 : A.data.length ≠ 0 := fun e => h (List.length_eq_zero_iff.mp e)
    rw [if_neg h]
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · rw [hax] at hd; simp only [totalLen] at hd
      simp only [onetoLen, oneTo, one_val]; rw [if_pos (by simp only [totalLen]; omega)]; simp
    · rw [hax] at hd; simp only [totalLen_cons, totalLen, Int.mul_one, len_def] at hd
      simp only [axes1, hax]; rw [if_pos (by omega)]; simp
    · rw [hax] at hd
      simp only [onetoLen, oneTo, one_val]; rw [if_pos (by omega)]; simp

theorem refLin_last {α : Type} (A : Arr α) (hA : A.WF) :
    refLinPos A (linearAxis A).hi.val = if A.data = [] then none else some (A.data.length - 1) := by
  have hT0 := totalLen_nonneg _ hA.1
  have hd := hA.2.1
  have hlen := lengthA_val A hA
  unfold linearAxis refLinPos
  by_cases h : A.data = []
  · have h0 : A.data.length = 0 := by simp [h]
    rw [if_pos h]
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · rw [hax] at hd; simp only [totalLen] at hd; omega
    · rw [hax] at hd; simp only [totalLen_cons, totalLen, Int.mul_one, len_def] at hd
      simp only [axes1, hax]; rw [if_neg (by omega)]
    · rw [hax] at hd
      simp only [onetoLen, oneTo, hlen]; rw [if_neg (by omega)]
  · have h0 : A.data.length ≠ 0 := fun e => h (List.length_eq_zero_iff.mp e)
    rw [if_neg h]
    rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · rw [hax] at hd; simp only [totalLen] at hd
      simp only [onetoLen, oneTo, hlen]; rw [if_pos (by simp only [totalLen]; omega)]; simp <;> omega
    · rw [hax] at hd; simp only [totalLen_cons, totalLen, Int.mul_one, len_def] at hd
      simp only [axes1, hax]; rw [if_pos (by omega)]; simp <;> omega
    · rw [hax] at hd
      simp only [onetoLen, oneTo, hlen]; rw [if_pos (by omega)]; simp <;> omega

theorem refPos_first {α : Type} (A : Arr α) (hA : A.WF) :
    refPos A (A.axes.map (·.lo)) = if A.data = [] then none else some 0 := by
  have hnil := data_nil_iff A hA
  have hT0 := totalLen_nonneg _ hA.1
  by_cases hN : A.axes.length = 1
  · obtain ⟨r, hax⟩ : ∃ r, A.axes = [r] := exists_single hN
    have := refLin_first A hA
    simp only [linearAxis, axes1, hax] at this
    simp only [hax, List.map_cons, List.map_nil, refPos]
    exact this
  · rw [refPos_cart A _ (by simpa using hN), List.map_map]
    have hl := refCartPos_los A.axes hA.1
    have hp := totalLen_pos_iff A.axes hA.1
    rw [show ((·.val) ∘ (·.lo) : Ax → Int) = (fun r => r.lo.val) from rfl, hl]
    by_cases h : A.data = []
    · have h0 := hnil.mp h
      rw [if_pos h, if_neg (fun hh => by have := hp.mpr hh; omega)]
    · have h0 : totalLen A.axes ≠ 0 := fun e => h (hnil.mpr e)
      rw [if_neg h, if_pos (hp.mp (by omega))]

theorem firstLastElements_proven : FirstLastElements := by
  intro α A hA
  constructor
  · have hres : ∀ I, getindex A I = refGet A I →
        refPos A I = (if A.data = [] then none else some 0) →
        getindex A I = (match A.data.head? with | some x => .ok x | none => .error .boundsError) := by
      intro I hg hp
      rw [hg, refGet_eq, hp, List.head?_eq_getElem?]
      by_cases h : A.data = []
      · rw [if_pos h]; simp [elemAt, h]
      · rw [if_neg h]; simp only [elemAt]; rcases A.data[0]? <;> rfl
    rcases hst : A.style with _ | _
    · simp only [firstA, hst]
      exact hres _ (indexing_linear A hA _).1 (refLin_first A hA)
    · simp only [firstA, hst]
      exact hres _ (indexing_extra A hA _ (by simp)).1 (refPos_first A hA)
  · simp only [lastA]
    rw [(indexing_linear A hA _).1, refGet_eq]
    show elemAt A (refLinPos A (linearAxis A).hi.val) = _
    rw [refLin_last A hA, List.getLast?_eq_getElem?]
    by_cases h : A.data = []
    · rw [if_pos h]; simp [elemAt, h]
    · rw [if_neg h]; simp only [elemAt]; rcases A.data[A.data.length - 1]? <;> rfl

theorem lengthIsemptyCount_proven : LengthIsemptyCount := by
  intro α A hA
  have hl := lengthA_val A hA
  refine ⟨hl, ?_⟩
  simp only [isemptyA, beq64, zero_val, hl]
  rcases A.data with _ | ⟨x, xs⟩
  · simp
  · simp only [List.isEmpty_cons, List.length_cons, decide_eq_false_iff_not]
    omega

end JuliaLean.AbstractArraySpecs
