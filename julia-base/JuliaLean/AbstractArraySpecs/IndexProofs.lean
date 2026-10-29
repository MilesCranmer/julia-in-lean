import JuliaLean.AbstractArraySpecs.Basic

/-! Correctness of Base's index conversion (`_sub2ind`, `_ind2sub`,
`_to_linear_index`, `_to_subscript_indices`) and of `checkbounds`. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

theorem bind_ok {α β : Type} (a : α) (f : α → R β) : ((Except.ok a : R α) >>= f) = f a := rfl
theorem bind_err {α β : Type} (e : Err) (f : α → R β) : ((Except.error e : R α) >>= f) = .error e := rfl

theorem cast_toNat {x : Int} (h : 0 ≤ x) : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg h

/-! ## `_sub2ind` -/

theorem sub2indRecurse_val (I : List I64) : ∀ (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) (p : Nat)
    (hp : refCartPos axs (I.map (·.val)) = some p) (L ind : I64)
    (hL : 1 ≤ L.val) (hind : 0 ≤ ind.val)
    (hb : ind.val + L.val * (totalLen axs - 1) ≤ tmax) (hLb : L.val * totalLen axs ≤ tmax),
    (sub2indRecurse axs L ind I).val = ind.val + L.val * p := by
  induction I with
  | nil =>
    intro axs hwf p hp L ind _ _ _ _
    have := (refCartPos_nil (by simpa using hp)).1
    subst this
    simp [sub2indRecurse]
  | cons i I ih =>
    intro axs hwf p hp L ind hL hind hb hLb
    have hbL := bnd L; have hbi := bnd ind; have hbii := bnd i
    rw [tmax_eq] at hb hLb
    cases axs with
    | nil =>
      simp only [List.map_cons, refCartPos] at hp
      split at hp
      · rename_i hi1
        simp only [sub2indRecurse]
        have e : (ind + (i - i64 1) * L).val = ind.val := by
          rw [vadd, vmul, vsub, one_val, hi1, show (1 : Int) - 1 = 0 by rfl,
            show wrapInt .i64 0 = 0 by decide, Int.zero_mul,
            show wrapInt .i64 0 = 0 by decide, Int.add_zero, wrap_id _ (by omega) (by omega)]
        rw [ih [] (by simp) p hp L _ hL (by omega) (by rw [e, tmax_eq]; simp [totalLen]; omega)
          (by rw [tmax_eq]; simpa [totalLen] using hLb), e]
      · simp at hp
    | cons r rs =>
      have hr := hwf r (by simp)
      have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
      simp only [List.map_cons, refCartPos] at hp
      split at hp
      · rename_i hin
        obtain ⟨p', hp', hpd⟩ := Option.map_eq_some_iff.mp hp
        have hT := refCartPos_lt rs hrs _ p' hp'
        have hT0 := totalLen_nonneg rs hrs
        have hlen := axLength_val hr
        rw [totalLen_cons] at hb hLb
        simp only [sub2indRecurse]
        have hld := len_def r
        have hlt := hr.2.2
        rw [tmax_eq] at hlt
        have hl1 : 1 ≤ r.len := by omega
        have hbl := bnd r.lo
        -- products as atoms
        have f1 := mul_le_mul_l (show 0 ≤ L.val by omega) (show i.val - r.lo.val ≤ r.len - 1 by
          omega)
        have f2 := Int.mul_nonneg (show 0 ≤ L.val by omega) (show 0 ≤ i.val - r.lo.val by omega)
        have f3 : L.val * (r.len - 1) = L.val * r.len - L.val := by rw [Int.mul_sub, Int.mul_one]
        have f4 := Int.mul_nonneg (show 0 ≤ L.val * r.len by
          exact Int.mul_nonneg (by omega) (by omega)) (show 0 ≤ totalLen rs - 1 by omega)
        have f4' : L.val * r.len * (totalLen rs - 1) = L.val * r.len * totalLen rs - L.val * r.len := by
          rw [Int.mul_sub, Int.mul_one]
        have f5 : L.val * (r.len * totalLen rs) = L.val * r.len * totalLen rs := by rw [Int.mul_assoc]
        have f5' : L.val * (r.len * totalLen rs - 1) = L.val * (r.len * totalLen rs) - L.val := by
          rw [Int.mul_sub, Int.mul_one]
        have f6 := one_le_mul hL hl1
        have fc : (i.val - r.lo.val) * L.val = L.val * (i.val - r.lo.val) := Int.mul_comm _ _
        have eL : (L * axLength r).val = L.val * r.len := by
          rw [vmul, hlen, wrap_id _ (by omega) (by omega)]
        have eI : (ind + (i - r.lo) * L).val = ind.val + L.val * (i.val - r.lo.val) := by
          rw [vadd, vmul, vsub, wrap_id (i.val - r.lo.val) (by omega) (by omega),
            wrap_id ((i.val - r.lo.val) * L.val) (by omega) (by omega),
            wrap_id (ind.val + (i.val - r.lo.val) * L.val) (by omega) (by omega), fc]
        rw [ih rs hrs p' hp' _ _ (by rw [eL]; omega) (by rw [eI]; omega)
          (by rw [eI, eL, tmax_eq]; omega) (by rw [eL, tmax_eq]; omega), eI, eL, ← hpd]
        push_cast
        rw [cast_toNat (show 0 ≤ i.val - r.lo.val by omega),
          cast_toNat (show 0 ≤ r.len by omega)]
        rw [Int.mul_add, Int.mul_assoc]
        omega
      · simp at hp

/-! ## `_ind2sub` -/

theorem divrem_ok (k n : I64) (hk : 0 ≤ k.val) (hn : 0 < n.val) :
    divrem k n = .ok (i64 (k.val / n.val), i64 (k.val % n.val)) := by
  have h1 : n.val ≠ 0 := by omega
  have h2 : ¬ (k.val = tmin ∧ n.val = -1) := by rw [tmin_eq]; omega
  simp only [divrem, h1, h2, if_false, Int.tdiv_eq_ediv_of_nonneg hk, Int.tmod_eq_emod_of_nonneg hk]

theorem ind2subRecurse_ok (axs : List Ax) : ∀ (hne : axs ≠ []) (hwf : ∀ r ∈ axs, r.WF) (k : I64)
    (hk0 : 0 ≤ k.val) (hk : k.val < totalLen axs) (hb : totalLen axs ≤ tmax),
    ∃ J, ind2subRecurse axs k = .ok J ∧ J.length = axs.length ∧
      refCartPos axs (J.map (·.val)) = some k.val.toNat := by
  induction axs with
  | nil => intro hne; exact absurd rfl hne
  | cons r rs ih =>
    intro _ hwf k hk0 hk hb
    have hr := hwf r (by simp)
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    have hbk := bnd k; have hbl := bnd r.lo; have hbh := bnd r.hi
    have hl0 := hr.2.1
    cases rs with
    | nil =>
      have hld := len_def r
      simp only [totalLen, Int.mul_one] at hk hb
      refine ⟨[k + r.lo], rfl, rfl, ?_⟩
      have e : (k + r.lo).val = k.val + r.lo.val := by
        rw [vadd, wrap_id _ (by omega) (by omega)]
      simp only [List.map_cons, List.map_nil, refCartPos, e]
      have : r.lo.val ≤ k.val + r.lo.val ∧ k.val + r.lo.val ≤ r.hi.val := by
        omega
      rw [if_pos this]
      simp [List.all_nil]
    | cons r2 rs' =>
      have hT0 := totalLen_nonneg (r2 :: rs') hrs
      have hlen := axLength_val hr
      have hld := len_def r
      have hlt := hr.2.2
      rw [tmax_eq] at hlt hb
      rw [totalLen_cons] at hk hb
      have hl1 : 1 ≤ r.len := by
        by_cases h : r.len = 0
        · rw [h, Int.zero_mul] at hk; omega
        · omega
      have hT1 : 1 ≤ totalLen (r2 :: rs') := by
        by_cases h : totalLen (r2 :: rs') = 0
        · rw [h, Int.mul_zero] at hk; omega
        · omega
      have hpos : 0 < r.len := by omega
      have hq0 : 0 ≤ k.val / r.len := Int.ediv_nonneg hk0 (by omega)
      have hqT : k.val / r.len < totalLen (r2 :: rs') := by
        rw [Int.ediv_lt_iff_lt_mul hpos, Int.mul_comm]; exact hk
      have hm0 : 0 ≤ k.val % r.len := Int.emod_nonneg _ (by omega)
      have hmL : k.val % r.len < r.len := Int.emod_lt_of_pos _ hpos
      have hdm : k.val % r.len = k.val - r.len * (k.val / r.len) := Int.emod_def _ _
      have hqle : k.val / r.len ≤ k.val := by
        have := mul_le_mul_l (show 0 ≤ k.val / r.len by omega) (show 1 ≤ r.len from hl1)
        rw [Int.mul_one, Int.mul_comm] at this; omega
      have hTle : totalLen (r2 :: rs') ≤ tmax := by
        have := mul_le_mul_l (show 0 ≤ totalLen (r2 :: rs') by omega) (show 1 ≤ r.len from hl1)
        rw [Int.mul_one, Int.mul_comm] at this; rw [tmax_eq]; omega
      obtain ⟨J', hJ', hlen', hpos'⟩ := ih (by simp) hrs (i64 (k.val / r.len))
        (by rw [vlit, wrap_id _ (by omega) (by omega)]; omega)
        (by rw [vlit, wrap_id _ (by omega) (by omega)]; exact hqT) hTle
      have eq : (i64 (k.val / r.len)).val = k.val / r.len := by rw [vlit, wrap_id _ (by omega) (by omega)]
      have em : (i64 (k.val % r.len) + r.lo).val = k.val % r.len + r.lo.val := by
        rw [vadd, vlit, wrap_id (k.val % r.len) (by omega) (by omega),
          wrap_id _ (by omega) (by omega)]
      refine ⟨(i64 (k.val % r.len) + r.lo) :: J', ?_, by simp [hlen'], ?_⟩
      · simp only [ind2subRecurse]
        rw [divrem_ok k (axLength r) hk0 (by rw [hlen]; omega), hlen, bind_ok]
        simp only [hJ', bind_ok]
      · simp only [List.map_cons, refCartPos, em]
        have : r.lo.val ≤ k.val % r.len + r.lo.val ∧ k.val % r.len + r.lo.val ≤ r.hi.val := by
          omega
        rw [if_pos this]
        rw [show List.map (fun x => x.val) J' = List.map (·.val) J' from rfl, hpos', eq]
        simp only [Option.map_some, Option.some.injEq]
        apply Int.ofNat.inj
        simp only [Int.ofNat_eq_coe]
        push_cast
        rw [cast_toNat (show 0 ≤ k.val % r.len + r.lo.val - r.lo.val by omega),
          cast_toNat (show 0 ≤ r.len by omega), cast_toNat hq0, cast_toNat hk0]
        omega

/-! ## Reference-position facts -/

theorem refCartPos_take (axs : List Ax) : ∀ (is : List Int) (p : Nat),
    refCartPos axs is = some p → axs.length ≤ is.length →
    refCartPos axs (is.take axs.length) = some p := by
  induction axs with
  | nil =>
    intro is p h _
    have := refCartPos_nil_axes_val is p h
    subst this; simp [refCartPos]
  | cons r rs ih =>
    intro is p h hl
    cases is with
    | nil => simp at hl
    | cons i is =>
      simp only [List.length_cons, List.take_succ_cons, refCartPos] at h hl ⊢
      split at h
      · rename_i hin
        obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [if_pos hin, ih is p' hp' (by omega)]
        rfl
      · simp at h

theorem refCartPos_single (r : Ax) (k : Int) :
    refCartPos [r] [k] = if r.lo.val ≤ k ∧ k ≤ r.hi.val then some (k - r.lo.val).toNat else none := by
  simp only [refCartPos]
  split <;> simp

theorem refPos_cart {α : Type} (A : Arr α) (I : List I64) (h : I.length ≠ 1) :
    refPos A I = refCartPos A.axes (I.map (·.val)) := by
  match I, h with
  | [], _ => rfl
  | [_], h => exact absurd rfl h
  | _ :: _ :: _, _ => rfl

theorem refPos_lt {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) (p : Nat)
    (h : refPos A I = some p) : p < A.data.length := by
  have hlen := hA.2.1
  suffices hs : (p : Int) < totalLen A.axes by omega
  match I with
  | [k] =>
    simp only [refPos, refLinPos] at h
    split at h
    · rename_i r hax
      split at h
      · rename_i hin
        simp only [Option.some.injEq] at h
        subst h
        rw [hax, totalLen_cons, len_def]; simp only [totalLen, Int.mul_one]
        rw [cast_toNat (by omega)]; omega
      · simp at h
    · split at h
      · rename_i hin; simp only [Option.some.injEq] at h; subst h
        rw [cast_toNat (by omega)]; omega
      · simp at h
  | [] => exact refCartPos_lt _ hA.1 _ p h
  | a :: b :: c => exact refCartPos_lt _ hA.1 _ p h

/-! ## `checkbounds` -/

theorem checkboundsIndices_eq (I : List I64) : ∀ (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF),
    checkboundsIndices axs I = (refCartPos axs (I.map (·.val))).isSome := by
  induction I with
  | nil =>
    intro axs hwf
    simp only [checkboundsIndices, List.map_nil, refCartPos, all_len1 axs hwf]
    split <;> simp_all
  | cons i I ih =>
    intro axs hwf
    cases axs with
    | nil =>
      have hw1 : (oneTo (i64 1)).WF := oneTo_wf (by rw [one_val]; omega)
      simp only [checkboundsIndices, List.headD_nil, List.tail_nil, checkindex_eq hw1,
        List.map_cons, refCartPos, ih [] (by simp)]
      simp only [oneTo, one_val]
      by_cases h : i.val = 1
      · simp [h]
      · have : ¬ (1 ≤ i.val ∧ i.val ≤ 1) := by omega
        simp [h, this]
    | cons r rs =>
      have hr := hwf r (by simp)
      have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
      simp only [checkboundsIndices, List.headD_cons, List.tail_cons, checkindex_eq hr,
        List.map_cons, refCartPos, ih rs hrs]
      by_cases h : r.lo.val ≤ i.val ∧ i.val ≤ r.hi.val
      · simp [h]
      · simp [h]

theorem checkindex_linear {α : Type} (A : Arr α) (hA : A.WF) (k : I64) :
    checkindex (linearAxis A) k = (refLinPos A k.val).isSome := by
  rw [checkindex_eq (linearAxis_wf A hA)]
  have hlen := lengthA_val A hA
  have hd := hA.2.1
  unfold linearAxis refLinPos
  rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · simp only [hax] at hd
    simp only [onetoLen, oneTo, one_val, hlen, hd]
    split <;> simp_all
  · simp only [axes1, hax]
    split <;> simp_all
  · simp only [hax] at hd
    simp only [onetoLen, oneTo, one_val, hlen, hd]
    split <;> simp_all

theorem checkboundsBool_eq {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) :
    checkboundsBool A I = (refPos A I).isSome := by
  match I with
  | [k] => exact checkindex_linear A hA k
  | [] => exact checkboundsIndices_eq [] A.axes hA.1
  | a :: b :: c => exact checkboundsIndices_eq (a :: b :: c) A.axes hA.1

theorem checkboundsAgreesWithReference_proven : CheckboundsAgreesWithReference := by
  intro α A I hA
  refine ⟨checkboundsBool_eq A hA I, ?_⟩
  simp only [checkbounds, checkboundsBool_eq A hA I]

end JuliaLean.AbstractArraySpecs
