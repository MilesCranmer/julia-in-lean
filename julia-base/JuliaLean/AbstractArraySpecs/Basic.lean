import JuliaLean.AbstractArraySpecs.Props

/-! Arithmetic and reference-semantics lemmas for the proofs of this area. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

theorem wi (x : Int) :
    wrapInt .i64 x = (x + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]
theorem wu (x : Int) : wrapInt .u64 x = x % 18446744073709551616 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]
theorem bnd (x : I64) : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 := by
  have := x.property; simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using this
theorem vadd (a b : I64) : (a + b).val = wrapInt .i64 (a.val + b.val) := rfl
theorem vsub (a b : I64) : (a - b).val = wrapInt .i64 (a.val - b.val) := rfl
theorem vmul (a b : I64) : (a * b).val = wrapInt .i64 (a.val * b.val) := rfl
theorem vlit (x : Int) : (i64 x).val = wrapInt .i64 x := rfl
theorem tmax_eq : tmax = 9223372036854775807 := by decide
theorem tmin_eq : tmin = -9223372036854775808 := by decide
theorem one_val : (i64 1).val = 1 := by decide
theorem zero_val : (i64 0).val = 0 := by decide

/-- A value in `Int` range is unchanged by wrapping. -/
theorem wrap_id (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    wrapInt .i64 x = x := by rw [wi]; omega

theorem ext64 {a b : I64} (h : a.val = b.val) : a = b := Subtype.ext h

theorem decide_le64 (a b : I64) : decide (a ≤ b) = decide (a.val ≤ b.val) := rfl
theorem decide_lt64 (a b : I64) : decide (a < b) = decide (a.val < b.val) := rfl

theorem beq64 (a b : I64) : (a == b) = decide (a.val = b.val) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : a.val ≠ b.val := fun e => h (ext64 e)
    simp [h, h']

theorem mul_le_mul_l {a b c : Int} (ha : 0 ≤ a) (h : b ≤ c) : a * b ≤ a * c :=
  Int.mul_le_mul_of_nonneg_left h ha

theorem one_le_mul {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have := Int.mul_le_mul ha hb (by omega) (by omega)
  simpa using this

/-! ## Axes -/

theorem len_def (r : Ax) : r.len = r.hi.val - r.lo.val + 1 := rfl
theorem totalLen_cons (r : Ax) (rs : List Ax) : totalLen (r :: rs) = r.len * totalLen rs := rfl

theorem axLength_val {r : Ax} (h : r.WF) : (axLength r).val = r.len := by
  obtain ⟨k, lo, hi⟩ := r
  obtain ⟨hk, h0, h1⟩ := h
  have := bnd lo; have := bnd hi
  simp only [Ax.len] at h0 h1 ⊢
  rw [tmax_eq] at h1
  cases k with
  | oneTo =>
    have hlo : lo.val = 1 := hk rfl
    simp only [axLength]; omega
  | unit =>
    simp only [axLength, vadd, vsub, one_val]
    rw [wrap_id (hi.val - lo.val) (by omega) (by omega), wrap_id _ (by omega) (by omega)]
    omega

theorem checkindex_eq {r : Ax} (h : r.WF) (i : I64) :
    checkindex r i = decide (r.lo.val ≤ i.val ∧ i.val ≤ r.hi.val) := by
  obtain ⟨k, lo, hi⟩ := r
  obtain ⟨hk, h0, h1⟩ := h
  have := bnd lo; have := bnd hi; have := bnd i
  simp only [Ax.len] at h0 h1
  cases k with
  | oneTo =>
    have hlo : lo.val = 1 := hk rfl
    simp only [checkindex, unsignedVal, vsub, one_val, wi, wu, decide_eq_decide]
    omega
  | unit =>
    simp only [checkindex, decide_le64, Bool.decide_and]

theorem oneTo_wf {n : I64} (h : 0 ≤ n.val) : (oneTo n).WF := by
  have := bnd n
  refine ⟨fun _ => one_val, ?_, ?_⟩ <;> simp only [oneTo, Ax.len, one_val, tmax_eq] <;> omega

theorem totalLen_nonneg (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) : 0 ≤ totalLen axs := by
  induction axs with
  | nil => simp [totalLen]
  | cons r rs ih =>
    simp only [totalLen]
    exact Int.mul_nonneg (hwf r (by simp)).2.1 (ih (fun x hx => hwf x (by simp [hx])))

theorem prodI_val (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) (hb : totalLen axs ≤ tmax) :
    (prodI (axs.map axLength)).val = totalLen axs := by
  induction axs with
  | nil => simp [prodI, totalLen, one_val]
  | cons r rs ih =>
    have hr := hwf r (by simp)
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    have hT := totalLen_nonneg rs hrs
    have hlen := axLength_val hr
    simp only [List.map_cons, prodI, vmul, hlen, totalLen] at hb ⊢
    rw [tmax_eq] at hb
    by_cases h0 : r.len = 0
    · rw [h0, Int.zero_mul, Int.zero_mul, wi]; omega
    · have h1 : 1 ≤ r.len := by have := hr.2.1; omega
      have e : (r.len - 1) * totalLen rs = r.len * totalLen rs - totalLen rs := by
        rw [Int.sub_mul, Int.one_mul]
      have := Int.mul_nonneg (show 0 ≤ r.len - 1 by omega) hT
      rw [ih hrs (by rw [tmax_eq]; omega), wrap_id _ (by omega) (by omega)]

theorem lengthA_val {α : Type} (A : Arr α) (h : A.WF) : (lengthA A).val = A.data.length := by
  rw [h.2.1]; exact prodI_val A.axes h.1 h.2.2

theorem linearAxis_wf {α : Type} (A : Arr α) (h : A.WF) : (linearAxis A).WF := by
  unfold linearAxis
  split
  · rename_i r hA; simp only [axes1, hA]; exact h.1 r (by simp [hA])
  · exact oneTo_wf (by rw [lengthA_val A h]; omega)

/-! ## Reference positions -/

theorem all_len1 (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) :
    axs.all (fun x => axLength x == i64 1) = axs.all (fun r => decide (r.len = 1)) := by
  induction axs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons]
    rw [ih (fun x hx => hwf x (by simp [hx])), beq64, axLength_val (hwf r (by simp)), one_val]

theorem totalLen_of_all1 (axs : List Ax) (h : axs.all (fun r => decide (r.len = 1)) = true) :
    totalLen axs = 1 := by
  induction axs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [totalLen, h.1, ih h.2, Int.one_mul]

theorem refCartPos_nil {axs : List Ax} {p : Nat} (h : refCartPos axs [] = some p) :
    p = 0 ∧ axs.all (fun r => decide (r.len = 1)) = true := by
  unfold refCartPos at h
  split at h
  · rename_i ha; simp at h; exact ⟨h.symm, ha⟩
  · simp at h

theorem refCartPos_lt (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) (is : List Int) (p : Nat)
    (h : refCartPos axs is = some p) : (p : Int) < totalLen axs := by
  induction is generalizing axs p with
  | nil =>
    obtain ⟨hp, ha⟩ := refCartPos_nil h
    rw [totalLen_of_all1 axs ha, hp]; decide
  | cons i is ih =>
    cases axs with
    | nil =>
      simp only [refCartPos] at h
      split at h
      · exact ih [] (by simp) p h
      · simp at h
    | cons r rs =>
      have hr := hwf r (by simp)
      have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
      simp only [refCartPos] at h
      split at h
      · rename_i hin
        obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp h
        have hlt := ih rs hrs p' hp'
        have hl0 := hr.2.1
        simp only [totalLen]
        simp only [Ax.len] at hl0 ⊢
        have e1 : (((i - r.lo.val).toNat : Nat) : Int) = i - r.lo.val := Int.toNat_of_nonneg (by omega)
        have e2 : (((r.hi.val - r.lo.val + 1).toNat : Nat) : Int) = r.hi.val - r.lo.val + 1 :=
          Int.toNat_of_nonneg (by omega)
        push_cast
        rw [e1, e2]
        have := mul_le_mul_l (show 0 ≤ r.hi.val - r.lo.val + 1 by omega)
          (show (p' : Int) ≤ totalLen rs - 1 by omega)
        have e3 : (r.hi.val - r.lo.val + 1) * (totalLen rs - 1) =
            (r.hi.val - r.lo.val + 1) * totalLen rs - (r.hi.val - r.lo.val + 1) := by
          rw [Int.mul_sub, Int.mul_one]
        omega
      · simp at h

theorem refCartPos_nil_axes_val (is : List Int) (p : Nat) (h : refCartPos [] is = some p) : p = 0 := by
  induction is with
  | nil => exact (refCartPos_nil h).1
  | cons i is ih =>
    simp only [refCartPos] at h
    split at h
    · exact ih h
    · simp at h

/-- The axis starts select position 0 exactly when every axis is nonempty. -/
theorem refCartPos_los (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) :
    refCartPos axs (axs.map (fun r => r.lo.val)) =
      if ∀ r ∈ axs, 1 ≤ r.len then some 0 else none := by
  induction axs with
  | nil => simp [refCartPos]
  | cons r rs ih =>
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    simp only [List.map_cons, refCartPos, ih hrs]
    by_cases h1 : 1 ≤ r.len
    · have : r.lo.val ≤ r.lo.val ∧ r.lo.val ≤ r.hi.val := by simp only [Ax.len] at h1; omega
      rw [if_pos this]
      by_cases h2 : ∀ x ∈ rs, 1 ≤ x.len
      · rw [if_pos h2, if_pos (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h1
          · exact h2 x hx)]
        simp
      · rw [if_neg h2, if_neg (fun h => h2 (fun x hx => h x (List.mem_cons_of_mem _ hx)))]
        rfl
    · have hn : ¬ (r.lo.val ≤ r.lo.val ∧ r.lo.val ≤ r.hi.val) := by simp only [Ax.len] at h1; omega
      rw [if_neg hn, if_neg (fun h => h1 (h r (List.mem_cons_self ..)))]

theorem totalLen_pos_iff (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) :
    1 ≤ totalLen axs ↔ ∀ r ∈ axs, 1 ≤ r.len := by
  induction axs with
  | nil => simp [totalLen]
  | cons r rs ih =>
    have hrs : ∀ x ∈ rs, x.WF := fun x hx => hwf x (by simp [hx])
    have hT := totalLen_nonneg rs hrs
    have hl := (hwf r (by simp)).2.1
    simp only [totalLen, List.mem_cons, forall_eq_or_imp]
    rw [← ih hrs]
    constructor
    · intro h
      by_cases a : r.len = 0
      · rw [a, Int.zero_mul] at h; omega
      by_cases b : totalLen rs = 0
      · rw [b, Int.mul_zero] at h; omega
      omega
    · intro ⟨a, b⟩; exact one_le_mul a b

end JuliaLean.AbstractArraySpecs
