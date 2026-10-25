import JuliaLean.Sort.RangeSearch

/-! Proof that the integer-range search methods are correct when `x - first(a)`
does not overflow (`RangeSearchNoOverflowCorrect`). -/

namespace JuliaLean.Sort

open JuliaLean

private theorem tmin_nonpos (t : IntTy) : t.min ≤ 0 := by
  cases t <;> decide

private theorem tmax_pos (t : IntTy) : 1 ≤ t.max := by
  cases t <;> decide

private theorem unsigned_min (t : IntTy) (h : t.signed = false) : t.min = 0 := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem signed_max (t : IntTy) (h : t.signed = true) : t.max = -t.min - 1 := by
  cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max]

private theorem wrap_val {t : IntTy} (z : Int) (h : t.min ≤ z ∧ z ≤ t.max) :
    (JInt.wrap t z).val = z := wrapInt_of_inRange t z h

private theorem sub_val {t : IntTy} (a b : JInt t)
    (h : t.min ≤ a.val - b.val ∧ a.val - b.val ≤ t.max) :
    (a - b).val = a.val - b.val := wrapInt_of_inRange t _ h

/-- Quotient facts for `0 ≤ D`, `0 < H`. -/
private theorem qfacts (D H : Int) (hD : 0 ≤ D) (hH : 0 < H) :
    0 ≤ D / H ∧ D / H * H ≤ D ∧ D < (D / H + 1) * H ∧ D / H ≤ D := by
  have e := Int.mul_ediv_add_emod D H
  have m0 := Int.emod_nonneg D (show H ≠ 0 by omega)
  have m1 := Int.emod_lt_of_pos D hH
  have q0 : 0 ≤ D / H := Int.ediv_nonneg hD (by omega)
  have hc : H * (D / H) = D / H * H := Int.mul_comm _ _
  have hs : (D / H + 1) * H = D / H * H + H := by rw [Int.add_mul, Int.one_mul]
  have hq : D / H * 1 ≤ D / H * H := Int.mul_le_mul_of_nonneg_left (show 1 ≤ H by omega) q0
  rw [Int.mul_one] at hq
  refine ⟨q0, ?_, ?_, ?_⟩ <;> omega

private theorem floor_char {D H : Int} (hH : 0 < H) (k : Int) : k ≤ D / H ↔ k * H ≤ D :=
  Int.le_ediv_iff_mul_le hH

/-- `cld` is `D / H` plus the correction of `base/div.jl`: `k < c ↔ k * H < D`. -/
private theorem ceil_char {D H : Int} (hD : 0 ≤ D) (hH : 0 < H) (k : Int) :
    k < D / H + (if D / H * H ≠ D then 1 else 0) ↔ k * H < D := by
  obtain ⟨q0, qle, qlt, -⟩ := qfacts D H hD hH
  have hs : (D / H + 1) * H = D / H * H + H := by rw [Int.add_mul, Int.one_mul]
  by_cases hne : D / H * H ≠ D
  · rw [if_pos hne]
    constructor
    · intro hk
      have : k * H ≤ D / H * H := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · intro hk
      have := Int.lt_of_mul_lt_mul_right (show k * H < (D / H + 1) * H by omega) (by omega)
      omega
  · rw [if_neg hne]
    have heq : D / H * H = D := by omega
    constructor
    · intro hk
      have := Int.mul_lt_mul_of_pos_right (show k < D / H by omega) hH
      omega
    · intro hk
      have := Int.lt_of_mul_lt_mul_right (show k * H < D / H * H by omega) (by omega)
      omega

private theorem div_ok {t : IntTy} (a b : JInt t) (hb : b.val ≠ 0)
    (hn : ¬ (t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
  unfold JInt.div
  rw [if_neg hb, if_neg hn]

/-- `x + lit 0` and `x - lit 0` are `x`; `x + lit 1` is `x + 1` when it fits. -/
private theorem add_lit {t : IntTy} (d : JInt t) (c : Int) (hc : c = 0 ∨ c = 1)
    (h : d.val + c ≤ t.max) : (d + JInt.lit t c).val = d.val + c := by
  have hm := tmin_nonpos t
  have h1 := tmax_pos t
  show wrapInt t (d.val + wrapInt t c) = _
  rw [wrapInt_of_inRange t c ⟨by omega, by omega⟩]
  exact wrapInt_of_inRange t _ ⟨by have := d.property.1; omega, h⟩

private theorem sub_lit0 {t : IntTy} (d : JInt t) : (d - JInt.lit t 0).val = d.val := by
  have hm := tmin_nonpos t
  have h1 := tmax_pos t
  show wrapInt t (d.val - wrapInt t 0) = _
  rw [wrapInt_of_inRange t 0 ⟨by omega, by omega⟩, Int.sub_zero]
  exact wrapInt_of_inRange t _ d.property

/-- `fld`/`cld` for `0 ≤ a`, `0 < b`. -/
private theorem fldcld_pos {t : IntTy} (a b : JInt t) (ha : 0 ≤ a.val) (hb : 0 < b.val) :
    (∃ r, JInt.fld a b = .ok r ∧ r.val = a.val / b.val) ∧
    (∃ r, JInt.cld a b = .ok r ∧
      r.val = a.val / b.val + (if a.val / b.val * b.val ≠ a.val then 1 else 0)) := by
  obtain ⟨q0, qle, qlt, qa⟩ := qfacts a.val b.val ha hb
  have hmin := tmin_nonpos t
  have hamax := a.property.2
  have ht : a.val.tdiv b.val = a.val / b.val := Int.tdiv_eq_ediv_of_nonneg ha
  have hd := div_ok a b (by omega) (fun ⟨_, _, h⟩ => by omega)
  rw [ht] at hd
  generalize hq : a.val / b.val = q at *
  have wq : (JInt.wrap t q).val = q := wrap_val _ ⟨by omega, by omega⟩
  have hqb := Int.mul_nonneg q0 (show 0 ≤ b.val by omega)
  have wprod : (JInt.wrap t q * b).val = q * b.val := by
    show wrapInt t ((JInt.wrap t q).val * b.val) = _
    rw [wq]
    exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  constructor
  · unfold JInt.fld
    rw [hd]
    simp only [bind, Except.bind]
    cases hs : t.signed
    · exact ⟨JInt.wrap t q, rfl, wq⟩
    · have hc : ¬ (((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := fun ⟨h1, _⟩ => by omega
      refine ⟨JInt.wrap t q - JInt.lit t 0, ?_, by rw [sub_lit0, wq]⟩
      rw [if_pos rfl, if_neg hc]
      rfl
  · unfold JInt.cld
    rw [hd]
    simp only [bind, Except.bind]
    by_cases hc : q * b.val ≠ a.val
    · have hpos : 0 < a.val := by
        rcases Int.lt_or_le 0 a.val with h' | h'
        · exact h'
        · exfalso
          have ha0 : a.val = 0 := by omega
          rw [ha0, Int.zero_ediv] at hq
          subst hq
          rw [Int.zero_mul] at hc
          exact hc ha0.symm
      have hcond : (¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val :=
        ⟨Or.inr ⟨fun _ => hb, fun _ => hpos⟩, by rw [wprod]; exact hc⟩
      refine ⟨JInt.wrap t q + JInt.lit t 1, ?_, ?_⟩
      · rw [if_pos hcond]
        rfl
      · have hqqb : q * 1 ≤ q * b.val := Int.mul_le_mul_of_nonneg_left (by omega) q0
        rw [Int.mul_one] at hqqb
        rw [if_pos hc, add_lit _ 1 (Or.inr rfl) (by rw [wq]; omega), wq]
    · have hcond : ¬ ((¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := by rw [wprod]; exact fun h => hc h.2
      refine ⟨JInt.wrap t q + JInt.lit t 0, ?_, ?_⟩
      · rw [if_neg hcond]
        rfl
      · rw [if_neg hc, add_lit _ 0 (Or.inl rfl) (by rw [wq]; have := wq; omega), wq]

/-- `fld`/`cld` for `typemin(T) < a ≤ 0`, `b < 0`, in terms of `-a` and `-b`. -/
private theorem fldcld_neg {t : IntTy} (a b : JInt t) (ha : a.val ≤ 0) (hb : b.val < 0)
    (hmin' : t.min < a.val) :
    (∃ r, JInt.fld a b = .ok r ∧ r.val = (-a.val) / (-b.val)) ∧
    (∃ r, JInt.cld a b = .ok r ∧
      r.val = (-a.val) / (-b.val) +
        (if (-a.val) / (-b.val) * (-b.val) ≠ -a.val then 1 else 0)) := by
  have hsg : t.signed = true := by
    cases hs : t.signed
    · have := unsigned_min t hs; have := b.property.1; omega
    · rfl
  obtain ⟨q0, qle, qlt, qa⟩ := qfacts (-a.val) (-b.val) (by omega) (by omega)
  have hmin := tmin_nonpos t
  have hbmin := b.property.1
  have hmx := signed_max t hsg
  have ht : a.val.tdiv b.val = (-a.val) / (-b.val) := by
    rw [← Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have hd := div_ok a b (by omega) (fun ⟨_, h, _⟩ => by omega)
  rw [ht] at hd
  generalize hq : (-a.val) / (-b.val) = q at *
  have wq : (JInt.wrap t q).val = q := wrap_val _ ⟨by omega, by omega⟩
  have hprod : q * b.val = -(q * (-b.val)) := by rw [Int.mul_neg, Int.neg_neg]
  have hqb0 : 0 ≤ q * (-b.val) := Int.mul_nonneg q0 (by omega)
  have wprod : (JInt.wrap t q * b).val = q * b.val := by
    show wrapInt t ((JInt.wrap t q).val * b.val) = _
    rw [wq]
    exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  constructor
  · unfold JInt.fld
    rw [hd]
    simp only [bind, Except.bind]
    have hc : ¬ (((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
        (JInt.wrap t q * b).val ≠ a.val) := by
      rw [wprod]
      intro ⟨h1, h2⟩
      rcases h1 with h1 | h1
      · omega
      · have ha0 : a.val = 0 := by omega
        rw [ha0, Int.neg_zero, Int.zero_ediv] at hq
        subst hq
        rw [Int.zero_mul] at h2
        exact h2 ha0.symm
    refine ⟨JInt.wrap t q - JInt.lit t 0, ?_, by rw [sub_lit0, wq]⟩
    rw [if_pos hsg, if_neg hc]
    rfl
  · unfold JInt.cld
    rw [hd]
    simp only [bind, Except.bind]
    by_cases hc : q * (-b.val) ≠ -a.val
    · have hcond : (¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val :=
        ⟨Or.inr ⟨fun h' => by omega, fun h' => by omega⟩, by rw [wprod]; omega⟩
      refine ⟨JInt.wrap t q + JInt.lit t 1, ?_, ?_⟩
      · rw [if_pos hcond]
        rfl
      · have hqqb : q * 1 ≤ q * (-b.val) := Int.mul_le_mul_of_nonneg_left (by omega) q0
        rw [Int.mul_one] at hqqb
        rw [if_pos hc, add_lit _ 1 (Or.inr rfl) (by rw [wq]; omega), wq]
    · have hcond : ¬ ((¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := by rw [wprod]; intro h; omega
      refine ⟨JInt.wrap t q + JInt.lit t 0, ?_, ?_⟩
      · rw [if_neg hcond]
        rfl
      · rw [if_neg hc, add_lit _ 0 (Or.inl rfl) (by rw [wq]; omega), wq]

private theorem elemLt_false (a b : Int) : elemLt false a b = decide (a < b) := rfl
private theorem elemLt_true (a b : Int) : elemLt true a b = decide (b < a) := rfl

private theorem iff_not' {A B : Prop} (h : A ↔ B) : ¬A ↔ ¬B :=
  ⟨fun na b => na (h.mpr b), fun nb a => nb (h.mp a)⟩

/-- Closes `elemLt`/`rangeElem` goals by linear arithmetic over the atoms `(i - 1) * h`. -/
macro "elem_tac" : tactic => `(tactic| (
  simp only [elemLt_false, elemLt_true, rangeElem, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, Int.not_lt]
  omega))

/-- `q + 1` computed in `promote_type(T, Int)` and converted to `Int`. -/
private theorem addOne_key {t : IntTy} (q : JInt t) (h0 : 0 ≤ q.val)
    (h1 : q.val + 1 < IntTy.max .i64) :
    ∃ r, toKeytype (addOneInt q) = .ok r ∧ r.val = q.val + 1 := by
  have hw : addOneInt q = q.val + 1 := by
    unfold addOneInt
    apply wrapInt_of_inRange
    cases t <;> simp [IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] at h1 ⊢ <;> omega
  unfold toKeytype JInt.convert
  rw [hw, dif_pos ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega, by omega⟩]
  exact ⟨_, rfl, rfl⟩

private theorem lit_one : (JInt.lit .i64 1).val = 1 := by decide
private theorem lit_zero : (JInt.lit .i64 0).val = 0 := by decide

private theorem len_add_one (len : JInt64) (h0 : 0 ≤ len.val) (h : len.val < IntTy.max .i64) :
    (len + JInt.lit .i64 1).val = len.val + 1 := by
  show wrapInt .i64 (len.val + wrapInt .i64 1) = _
  rw [wrapInt_of_inRange .i64 1 (by decide)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega, by omega⟩

theorem rangeSearchNoOverflowCorrect : RangeSearchNoOverflowCorrect := by
  intro t f h l len x rev hv hs hne hdlo hdhi
  obtain ⟨hn0, hnmax, hh0, hl⟩ := hv
  rw [if_neg (by omega)] at hl
  unfold rangeElem at hl
  have hmin := tmin_nonpos t
  have hsmin : t.min ≤ x.val - f.val := by split at hdlo <;> omega
  have hd : (x - f).val = x.val - f.val := sub_val x f ⟨hsmin, hdhi⟩
  have hv1 := len_add_one len hn0 hnmax
  unfold RangeSorted at hs
  unfold RangeAnswers FirstContract LastContract
  generalize hN : len.val = n at *
  cases rev
  · -- Forward: `lt(a, b) = a < b`, increasing elements.
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hmono : ∀ i, 1 ≤ i → i ≤ n →
        0 ≤ (i - 1) * h.val ∧ (i - 1) * h.val ≤ (n - 1) * h.val := by
      intro i hi1 hin
      by_cases h2 : 2 ≤ n
      · have hp := hs h2
        exact ⟨Int.mul_nonneg (by omega) (by omega),
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)⟩
      · have e1 : i - 1 = 0 := by omega
        have e2 : n - 1 = 0 := by omega
        rw [e1, e2, Int.zero_mul]
        exact ⟨Int.le_refl 0, Int.le_refl 0⟩
    constructor
    · -- searchsortedfirst
      unfold rangeSearchFirst rangeLt
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases b1 : f.val < x.val
      · rw [if_neg (by simpa using b1)]
        by_cases b2 : l.val < x.val
        · rw [if_pos (by simp [b2])]
          refine ⟨_, rfl, ?_⟩
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := hmono i hi1 (by omega)
            elem_tac
          · intro i hir hin; omega
        · have hn2 : 2 ≤ n := by
            refine Classical.byContradiction fun hc => ?_
            have e2 : n - 1 = 0 := by omega
            rw [e2, Int.zero_mul] at hl; omega
          have hp := hs hn2
          rw [if_neg (by simp [b2]; omega)]
          obtain ⟨-, r, hr, hrv⟩ := fldcld_pos (x - f) h (by omega) hp
          rw [hr]
          simp only [bind, Except.bind]
          rw [hd] at hrv
          have hceil := ceil_char (D := x.val - f.val) (by omega) hp
          have hq0 := (qfacts (x.val - f.val) h.val (by omega) hp).1
          have hc0 : 0 ≤ r.val := by rw [hrv]; split <;> omega
          have hcn : r.val ≤ n - 1 := by
            have := (iff_not' (hceil (n - 1))).mpr (by omega)
            rw [← hrv] at this; omega
          obtain ⟨k, hk, hkv⟩ := addOne_key r hc0 (by omega)
          rw [hk]
          refine ⟨k, rfl, ?_⟩
          rw [hkv]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := (hceil (i - 1)).mp (by rw [← hrv]; omega)
            elem_tac
          · intro i hir hin
            have := (iff_not' (hceil (i - 1))).mp (by rw [← hrv]; omega)
            elem_tac
      · rw [if_pos (by simpa using b1)]
        refine ⟨_, rfl, ?_⟩
        rw [lit_one]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro i hi1 hir; omega
        · intro i hir hin
          have := hmono i hir hin
          elem_tac
    · -- searchsortedlast
      unfold rangeSearchLast rangeLt
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases b1 : x.val < f.val
      · rw [if_pos (by simpa using b1)]
        refine ⟨_, rfl, ?_⟩
        rw [lit_zero]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro i hi1 hir; omega
        · intro i hir hin
          have := hmono i (by omega) hin
          elem_tac
      · rw [if_neg (by simpa using b1)]
        by_cases b2 : x.val < l.val
        · have hn2 : 2 ≤ n := by
            refine Classical.byContradiction fun hc => ?_
            have e2 : n - 1 = 0 := by omega
            rw [e2, Int.zero_mul] at hl; omega
          have hp := hs hn2
          rw [if_neg (by simp [b2]; omega)]
          obtain ⟨⟨r, hr, hrv⟩, -⟩ := fldcld_pos (x - f) h (by omega) hp
          rw [hr]
          simp only [bind, Except.bind]
          rw [hd] at hrv
          have hq0 := (qfacts (x.val - f.val) h.val (by omega) hp).1
          have hlt : (x.val - f.val) / h.val < n - 1 :=
            (Int.ediv_lt_iff_lt_mul hp).mpr (by omega)
          obtain ⟨k, hk, hkv⟩ := addOne_key r (by omega) (by omega)
          rw [hk]
          refine ⟨k, rfl, ?_⟩
          rw [hkv]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := (floor_char (D := x.val - f.val) hp (i - 1)).mp (by omega)
            elem_tac
          · intro i hir hin
            have := (iff_not' (floor_char (D := x.val - f.val) hp (i - 1))).mp (by omega)
            elem_tac
        · rw [if_pos (by simp [b2])]
          refine ⟨_, rfl, ?_⟩
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := hmono i hi1 (by omega)
            elem_tac
          · intro i hir hin; omega
  · -- Reverse: `lt(a, b) = b < a`, decreasing elements; write `H = -h`.
    simp only [↓reduceIte] at hs
    have hmono : ∀ i, 1 ≤ i → i ≤ n →
        0 ≤ (i - 1) * (-h.val) ∧ (i - 1) * (-h.val) ≤ (n - 1) * (-h.val) := by
      intro i hi1 hin
      by_cases h2 : 2 ≤ n
      · have hp := hs h2
        exact ⟨Int.mul_nonneg (by omega) (by omega),
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)⟩
      · have e1 : i - 1 = 0 := by omega
        have e2 : n - 1 = 0 := by omega
        rw [e1, e2, Int.zero_mul]
        exact ⟨Int.le_refl 0, Int.le_refl 0⟩
    have neg_mul : ∀ k : Int, k * h.val = -(k * (-h.val)) := fun k => by
      rw [Int.mul_neg, Int.neg_neg]
    have hl' : l.val = f.val - (n - 1) * (-h.val) := by rw [hl, neg_mul]; omega
    have hsg : ∀ _ : h.val < 0, t.min < (x - f).val := by
      intro hp
      have hs' : t.signed = true := by
        cases hs' : t.signed
        · have := unsigned_min t hs'; have := h.property.1; omega
        · rfl
      rw [hs'] at hdlo; simp at hdlo; omega
    constructor
    · -- searchsortedfirst
      unfold rangeSearchFirst rangeLt
      simp only [↓reduceIte]
      by_cases b1 : x.val < f.val
      · rw [if_neg (by simpa using b1)]
        by_cases b2 : x.val < l.val
        · rw [if_pos (by simp [b2])]
          refine ⟨_, rfl, ?_⟩
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := hmono i hi1 (by omega)
            have := neg_mul (i - 1)
            elem_tac
          · intro i hir hin; omega
        · have hn2 : 2 ≤ n := by
            refine Classical.byContradiction fun hc => ?_
            have e2 : n - 1 = 0 := by omega
            rw [e2, Int.zero_mul] at hl'; omega
          have hp := hs hn2
          rw [if_neg (by simp [b2]; omega)]
          obtain ⟨-, r, hr, hrv⟩ := fldcld_neg (x - f) h (by omega) hp (hsg hp)
          rw [hr]
          simp only [bind, Except.bind]
          rw [hd] at hrv
          have hceil := ceil_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (by omega)
          have hq0 := (qfacts (-(x.val - f.val)) (-h.val) (by omega) (by omega)).1
          have hc0 : 0 ≤ r.val := by rw [hrv]; split <;> omega
          have hcn : r.val ≤ n - 1 := by
            have := (iff_not' (hceil (n - 1))).mpr (by omega)
            rw [← hrv] at this; omega
          obtain ⟨k, hk, hkv⟩ := addOne_key r hc0 (by omega)
          rw [hk]
          refine ⟨k, rfl, ?_⟩
          rw [hkv]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := (hceil (i - 1)).mp (by rw [← hrv]; omega)
            have := neg_mul (i - 1)
            elem_tac
          · intro i hir hin
            have := (iff_not' (hceil (i - 1))).mp (by rw [← hrv]; omega)
            have := neg_mul (i - 1)
            elem_tac
      · rw [if_pos (by simpa using b1)]
        refine ⟨_, rfl, ?_⟩
        rw [lit_one]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro i hi1 hir; omega
        · intro i hir hin
          have := hmono i hir hin
          have := neg_mul (i - 1)
          elem_tac
    · -- searchsortedlast
      unfold rangeSearchLast rangeLt
      simp only [↓reduceIte]
      by_cases b1 : f.val < x.val
      · rw [if_pos (by simpa using b1)]
        refine ⟨_, rfl, ?_⟩
        rw [lit_zero]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro i hi1 hir; omega
        · intro i hir hin
          have := hmono i (by omega) hin
          have := neg_mul (i - 1)
          elem_tac
      · rw [if_neg (by simpa using b1)]
        by_cases b2 : l.val < x.val
        · have hn2 : 2 ≤ n := by
            refine Classical.byContradiction fun hc => ?_
            have e2 : n - 1 = 0 := by omega
            rw [e2, Int.zero_mul] at hl'; omega
          have hp := hs hn2
          rw [if_neg (by simp [b2]; omega)]
          obtain ⟨⟨r, hr, hrv⟩, -⟩ := fldcld_neg (x - f) h (by omega) hp (hsg hp)
          rw [hr]
          simp only [bind, Except.bind]
          rw [hd] at hrv
          have hq0 := (qfacts (-(x.val - f.val)) (-h.val) (by omega) (by omega)).1
          have hlt : (-(x.val - f.val)) / (-h.val) < n - 1 :=
            (Int.ediv_lt_iff_lt_mul (by omega)).mpr (by omega)
          obtain ⟨k, hk, hkv⟩ := addOne_key r (by omega) (by omega)
          rw [hk]
          refine ⟨k, rfl, ?_⟩
          rw [hkv]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := (floor_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (i - 1)).mp
              (by omega)
            have := neg_mul (i - 1)
            elem_tac
          · intro i hir hin
            have := (iff_not' (floor_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (i - 1))).mp
              (by omega)
            have := neg_mul (i - 1)
            elem_tac
        · rw [if_pos (by simp [b2])]
          refine ⟨_, rfl, ?_⟩
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro i hi1 hir
            have := hmono i hi1 (by omega)
            have := neg_mul (i - 1)
            elem_tac
          · intro i hir hin; omega

end JuliaLean.Sort
