import JuliaLean.MiscCov.RyuProps

/-!
Proofs and refutations of the `base/ryu/utils.jl` properties.
-/

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean JuliaLean.ParsePrint

theorem lit_self (e : JInt t) : JInt.lit t e.val = e :=
  Subtype.ext (wrapInt_of_inRange t e.val e.property)

theorem lit_toNat (e : JInt t) (h : 0 ≤ e.val) : JInt.lit t (e.val.toNat : Int) = e := by
  rw [Int.toNat_of_nonneg h]; exact lit_self e

/-! ### Logarithm approximations -/

/-- Check a decidable property on `0, 1, ..., n-1` by one Boolean scan, so that the
kernel evaluates a flat `List.all` instead of nested `Decidable` instances. -/
theorem forall_lt_of_all (n : Nat) (p : Nat → Prop) [DecidablePred p]
    (h : (List.range n).all (fun k => decide (p k)) = true) : ∀ k, k < n → p k := by
  intro k hk
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using this

theorem log10pow2_table : ∀ n : Nat, n < 1651 → FloorLog10 2 n (log10pow2 (JInt.lit .i64 n)).val :=
  forall_lt_of_all 1651 _ (by decide +kernel)

theorem log10pow5_table : ∀ n : Nat, n < 2621 → FloorLog10 5 n (log10pow5 (JInt.lit .i64 n)).val :=
  forall_lt_of_all 2621 _ (by decide +kernel)

theorem pow5bits_table : ∀ n : Nat, n < 3529 → CeilLog2Pow5 n (pow5bits (JInt.lit .i64 n)).val :=
  forall_lt_of_all 3529 _ (by decide +kernel)

theorem logApproxRange_proven : LogApproxRange := by
  refine ⟨?_, ?_, ?_⟩
  · intro e h0 h1
    have h := log10pow2_table e.val.toNat (by omega)
    rwa [lit_toNat e h0, Int.toNat_of_nonneg h0] at h
  · intro e h0 h1
    have h := log10pow5_table e.val.toNat (by omega)
    rwa [lit_toNat e h0, Int.toNat_of_nonneg h0] at h
  · intro e h0 h1
    have h := pow5bits_table e.val.toNat (by omega)
    rwa [lit_toNat e h0] at h

theorem logApproxDoc_refuted : ¬ LogApproxDoc := by
  intro h
  have := h.1 (JInt.lit .i64 (-1651)) (by decide)
  exact absurd this (by decide +kernel)

/-! ### `decimallength` -/

theorem decimallengthDoc_refuted : ¬ DecimallengthDoc := by
  intro h
  have := h.1 (JInt.lit .u64 (10 ^ 17))
  exact absurd this (by decide +kernel)

/-- Prove `P (if c then a else b)` from both branches. -/
theorem ite_prop {c : Prop} [Decidable c] {a b : Nat} (P : Nat → Prop) (h1 : c → P a) (h2 : ¬ c → P b) :
    P (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem decimallength_digits (x : Int) (h0 : 0 ≤ x) (h1 : x < 10 ^ 17) :
    IsNDigits x (decimallength x) := by
  simp only [decimallength, ge_iff_le]
  repeat' (refine ite_prop (IsNDigits x) (fun hc => ?_) (fun hc => ?_))
  all_goals
    refine ⟨by decide, by simp only [Int.reducePow]; omega, ?_⟩
    first | exact Or.inl rfl | (right; simp only [Nat.reduceSub, Int.reducePow]; omega)

theorem decimallength32_digits (v : JInt .u32) (h1 : v.val < 10 ^ 9) :
    IsNDigits v.val (decimallength32 v) := by
  have h0 : 0 ≤ v.val := (uval_bounds (t := .u32) rfl v).1
  simp only [decimallength32, ge_iff_le]
  repeat' (refine ite_prop (IsNDigits v.val) (fun hc => ?_) (fun hc => ?_))
  all_goals
    refine ⟨by decide, by simp only [Int.reducePow]; omega, ?_⟩
    first | exact Or.inl rfl | (right; simp only [Nat.reduceSub, Int.reducePow]; omega)

theorem decimallength16_digits (v : JInt .u16) : IsNDigits v.val (decimallength16 v) := by
  have h0 : 0 ≤ v.val := (uval_bounds (t := .u16) rfl v).1
  have h1 : v.val < 65536 := (uval_bounds (t := .u16) rfl v).2
  simp only [decimallength16, ge_iff_le]
  repeat' (refine ite_prop (IsNDigits v.val) (fun hc => ?_) (fun hc => ?_))
  all_goals
    refine ⟨by decide, by simp only [Int.reducePow]; omega, ?_⟩
    first | exact Or.inl rfl | (right; simp only [Nat.reduceSub, Int.reducePow]; omega)

theorem decimallengthRange_proven : DecimallengthRange :=
  ⟨fun v hv => decimallength_digits v.val (uval_bounds (t := .u64) rfl v).1 hv,
   fun v hv => decimallength32_digits v hv, decimallength16_digits⟩

/-! ### `pow5invsplit` bit count -/

theorem pow5InvsplitBitcount_refuted : ¬ Pow5InvsplitBitcount := by
  intro h
  obtain ⟨v, hv, _, hlt⟩ := h .f64 0 (by decide +kernel)
  have : pow5invsplit .f64 0 = .ok (JInt.lit .u128 (2 ^ 122 + 1)) := by decide +kernel
  rw [this] at hv
  cases hv
  exact absurd hlt (by decide +kernel)

/-! ### Lookup tables -/

theorem lookupTables_proven : LookupTables := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel⟩
  · intro T i h0 h1
    simp only [pow5invsplitLookup, invTable, h0, ↓reduceIte]
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · intro T i h0 h1
    simp only [pow5splitLookup, splitTable, h0, ↓reduceIte]
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    rfl

/-! ### Index helpers -/

theorem lengthforindex_table : ∀ idx : Nat, idx < 64 →
    (lengthforindex (JInt.lit .i64 idx)).toOption.map (·.val) =
      some (((log10pow2 (JInt.lit .i64 (16 * idx))).val + 25) / 9) ∧
    IndexHelpers.pow10Offset.getD idx 0 =
      ((List.range idx).map (fun (k : Nat) => ((lengthforindex (JInt.lit .i64 k)).toOption.map (·.val)).getD 0)).sum := by
  decide +kernel

theorem indexHelpers_proven : IndexHelpers := by
  refine ⟨?_, ?_, lengthforindex_table, by decide +kernel⟩
  · intro e h0 h1
    refine ⟨JInt.wrap .i64 ((e.val + 15).tdiv 16), ?_, ?_⟩
    · have hb := e.property
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb
      simp only [indexforexp, JInt.div]
      have h15 : (e + JInt.lit .i64 15).val = e.val + 15 := by
        rw [add_val, lit_val]
        rw [wrapInt_of_inRange .i64 15 (by decide)]
        exact wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)
      simp only [lit_val, wrapInt_of_inRange .i64 16 (by decide), h15]
      simp
    · have h15 : (e.val + 15).tdiv 16 = (e.val + 15) / 16 := Int.tdiv_eq_ediv_of_nonneg (by omega)
      rw [wrap_val_of_range _ (by
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, h15]; omega), h15]
      omega
  · intro idx h0 h1
    simp only [pow10bitsforindex, add_val, mul_val, lit_val]
    rw [wrapInt_of_inRange .i64 16 (by decide), wrapInt_of_inRange .i64 120 (by decide)]
    rw [wrapInt_of_inRange .i64 (16 * idx.val) (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
    exact wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

/-! ### Output helpers -/

theorem appendSignDigits_proven : AppendSignDigits := by
  refine ⟨?_, ?_⟩
  · intro x plus space pos
    cases x with
    | mk s n => cases s <;> cases n <;> cases plus <;> cases space <;> simp [appendSign]
  · intro olength digits buf pos decchar h1
    simp only [appendDDigits, appendCDigits, Buf.set]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (show ¬ pos = pos + 1 by omega)]
      simp only [↓reduceIte]
      rw [if_pos (by omega)]
      simp
    · simp
    · intro k hk1 hk2
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have hk : (pos + 1 + (k : Int) - (pos + 1)).toNat = k := by omega
      rw [hk]
    · intro i hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end JuliaLean.MiscCov.RyuUtils
