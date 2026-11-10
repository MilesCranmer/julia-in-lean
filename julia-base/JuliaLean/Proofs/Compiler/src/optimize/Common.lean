import JuliaLean.Compiler.src.optimize

/-!
Shared lemmas for the inlining proofs: `Int` (`JInt64`) arithmetic of the cost model and bit facts
about `UInt32` statement flags.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-! ## `Int` arithmetic -/

theorem ji_bounds (x : JI) : -(2 ^ 63 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 63 - 1 := by
  have := x.property
  simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using this

theorem wrap64_of (x : Int) (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

theorem wrap64_big (x : Int) (h1 : 2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 64 - 2) :
    wrapInt .i64 x = x - 2 ^ 64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem ji_val (x : Int) (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x ≤ 2 ^ 63 - 1) : (ji x).val = x := by
  show wrapInt .i64 x = x
  exact wrap64_of x h1 h2

theorem add_val (a b : JI) : (a + b).val = wrapInt .i64 (a.val + b.val) := rfl

theorem add_val_of (a b : JI) (h1 : -(2 ^ 63 : Int) ≤ a.val + b.val) (h2 : a.val + b.val ≤ 2 ^ 63 - 1) :
    (a + b).val = a.val + b.val := by
  rw [add_val]; exact wrap64_of _ h1 h2

theorem wrap_self (b : JI) : JInt.wrap .i64 b.val = b := by
  apply Subtype.ext
  have := ji_bounds b
  show wrapInt .i64 b.val = b.val
  exact wrap64_of _ this.1 this.2

theorem jmax_val (x y : JI) : (jmax x y).val = max x.val y.val := by
  unfold jmax
  by_cases h : y.val < x.val
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- `plus_saturate(b, c) ≥ b`, whatever the signs. -/
theorem ps_ge_left (b c : JI) : b.val ≤ (plusSaturate b c).val := by
  unfold plusSaturate; rw [jmax_val, jmax_val]; omega

theorem ps_ge_right (b c : JI) : c.val ≤ (plusSaturate b c).val := by
  unfold plusSaturate; rw [jmax_val, jmax_val]; omega

/-- On non-negative inputs without overflow, `plus_saturate` is the sum. -/
theorem ps_val_small (b c : JI) (hb : 0 ≤ b.val) (hc : 0 ≤ c.val) (h : b.val + c.val ≤ 2 ^ 63 - 1) :
    (plusSaturate b c).val = b.val + c.val := by
  unfold plusSaturate; rw [jmax_val, jmax_val, add_val_of b c (by omega) h]; omega

/-- On non-negative inputs with overflow, `plus_saturate` is the larger input. -/
theorem ps_val_big (b c : JI) (hb : 0 ≤ b.val) (hc : 0 ≤ c.val) (h : 2 ^ 63 - 1 < b.val + c.val) :
    (plusSaturate b c).val = max b.val c.val := by
  have hb' := ji_bounds b; have hc' := ji_bounds c
  unfold plusSaturate; rw [jmax_val, jmax_val, add_val, wrap64_big _ (by omega) (by omega)]; omega

/-- Below a threshold `t < 2^62`, `plus_saturate(b, c) > t` exactly when `b + c > t`. -/
theorem ps_gt_iff (b c t : JI) (hb : 0 ≤ b.val) (hc : 0 ≤ c.val) (hbt : b.val ≤ t.val)
    (ht : t.val < 2 ^ 62) : t.val < (plusSaturate b c).val ↔ t.val < b.val + c.val := by
  by_cases h : b.val + c.val ≤ 2 ^ 63 - 1
  · rw [ps_val_small b c hb hc h]
  · rw [ps_val_big b c hb hc (by omega)]; omega

/-! ## Statement-flag bits -/

theorem hasFlag_iff (c f : UInt32) :
    hasFlag c f = true ↔ ∀ i, f.toBitVec.getLsbD i = true → c.toBitVec.getLsbD i = true := by
  simp only [hasFlag, beq_iff_eq, ← UInt32.toBitVec_inj, UInt32.toBitVec_and]
  constructor
  · intro h i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp [BitVec.getLsbD_and, hi] at this
    exact this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and]
    cases hf : f.toBitVec.getLsbD i
    · simp
    · simp [h i hf]

theorem hasFlag_or (c f g : UInt32) : hasFlag c (f ||| g) = (hasFlag c f && hasFlag c g) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, hasFlag_iff, UInt32.toBitVec_or, BitVec.getLsbD_or, Bool.or_eq_true]
  constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · intro ⟨h1, h2⟩ i hi; rcases hi with hi | hi; exact h1 i hi; exact h2 i hi

theorem hasFlag_zero (c : UInt32) : hasFlag c 0 = true := by
  rw [hasFlag_iff]; intro i hi; simp at hi

theorem hasFlag_self_or (c f : UInt32) : hasFlag (c ||| f) f = true := by
  rw [hasFlag_iff]; intro i hi; simp [UInt32.toBitVec_or, BitVec.getLsbD_or, hi]

theorem hasFlag_or_right (c d f : UInt32) (h : hasFlag c f = true) : hasFlag (c ||| d) f = true := by
  rw [hasFlag_iff] at *; intro i hi; simp [UInt32.toBitVec_or, BitVec.getLsbD_or, h i hi]

/-- Bits disjoint from `f` do not change `has_flag(_, f)`. -/
theorem hasFlag_or_disjoint (c x f : UInt32) (hx : x &&& f = 0) : hasFlag (c ||| x) f = hasFlag c f := by
  apply Bool.eq_iff_iff.mpr
  rw [hasFlag_iff, hasFlag_iff]
  have hb : ∀ i, x.toBitVec.getLsbD i = true → f.toBitVec.getLsbD i = true → False := by
    intro i h1 h2
    have := congrArg (fun v : UInt32 => v.toBitVec.getLsbD i) hx
    simp [UInt32.toBitVec_and, BitVec.getLsbD_and, h1, h2] at this
  constructor
  · intro h i hi
    have := h i hi
    simp only [UInt32.toBitVec_or, BitVec.getLsbD_or, Bool.or_eq_true] at this
    rcases this with h' | h'
    · exact h'
    · exact absurd (hb i h' hi) id
  · intro h i hi; simp [UInt32.toBitVec_or, BitVec.getLsbD_or, h i hi]

end JuliaLean.Proofs.Compiler.src.optimize
