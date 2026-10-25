import JuliaLean.BigNums.Int

/-!
`ToIntExact`: `T(x::BigInt)` agrees with exact conversion for every `BitInteger` type. The limb
count bounds `abs(x)`, the limb fold in `rem(x, T)` is two's-complement reduction, and the
sign test of the signed constructors rejects exactly the out-of-range values.
-/

namespace JuliaLean.BigNums.ConvProofs

open JuliaLean JuliaLean.Promotion

/-- Unfold `wrapInt`/`limb` on a concrete type and evaluate the literal arithmetic. -/
local macro "wsimp" : tactic => `(tactic| simp only [limb, wrapInt, IntTy.signed, IntTy.bits,
  IntTy.min, IntTy.max, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, Nat.reducePow,
  Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Int.reducePow, Nat.pow_zero,
  Nat.div_one, Nat.mul_zero, Nat.mul_one, Int.reduceAdd, Int.reduceMod, Int.reduceSub,
  Int.reduceNeg, Int.reduceMul] at *)

theorem jint_neg_val {t : IntTy} (u : JInt t) : (-u).val = wrapInt t (-u.val) := rfl
theorem jint_add_val {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem jint_mul_val {t : IntTy} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
theorem jint_wrap_val (t : IntTy) (v : Int) : (JInt.wrap t v).val = wrapInt t v := rfl
theorem jint_lit_val (t : IntTy) (v : Int) : (JInt.lit t v).val = wrapInt t v := rfl

theorem nlimbs_le_iff (x : Int) (k : Nat) : nlimbs x ≤ k ↔ x.natAbs < 2 ^ (64 * k) := by
  unfold nlimbs
  split
  · rename_i hx; subst hx; simp [Nat.two_pow_pos]
  · rename_i hx
    have hn : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx
    rw [← Nat.log2_lt hn]
    omega

theorem nlimbs_pos (x : Int) (hx : x ≠ 0) : 0 < nlimbs x := by
  unfold nlimbs; rw [if_neg hx]; omega

theorem remTy_i64_val (x : Int) : (remTy .i64 x).val = wrapInt .i64 x := by
  have ha := Int.natAbs_eq x
  unfold remTy flipsignTy
  rw [if_pos (by decide)]
  split
  · rename_i hx; subst hx; rfl
  · split
    · rw [jint_neg_val, jint_wrap_val]
      wsimp
      generalize x.natAbs = n at *
      omega
    · rw [jint_wrap_val]
      wsimp
      generalize x.natAbs = n at *
      omega

theorem remTy_u64_val (x : Int) : (remTy .u64 x).val = wrapInt .u64 x := by
  have ha := Int.natAbs_eq x
  unfold remTy flipsignTy
  rw [if_pos (by decide)]
  split
  · rename_i hx; subst hx; rfl
  · split
    · rw [jint_neg_val, jint_wrap_val]
      wsimp
      generalize x.natAbs = n at *
      omega
    · rw [jint_wrap_val]
      wsimp
      generalize x.natAbs = n at *
      omega

theorem wrap_zero (t : IntTy) : wrapInt t 0 = 0 := by cases t <;> decide
theorem wrap_add_l (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a + b) = wrapInt t (a + b) := by
  cases t <;> wsimp <;> omega
theorem wrap_add_r (t : IntTy) (a b : Int) : wrapInt t (a + wrapInt t b) = wrapInt t (a + b) := by
  cases t <;> wsimp <;> omega
theorem wrap_neg (t : IntTy) (a : Int) : wrapInt t (-wrapInt t a) = wrapInt t (-a) := by
  cases t <;> wsimp <;> omega
theorem wrap_mul_one (t : IntTy) (a : Int) : wrapInt t (wrapInt t a * wrapInt t 1) = wrapInt t a := by
  cases t <;> wsimp <;> omega
theorem wrap_mul_2_64 (t : IntTy) (a : Int) :
    wrapInt t (wrapInt t a * wrapInt t 18446744073709551616) =
      wrapInt t (a * 18446744073709551616) := by
  cases t <;> wsimp <;> omega

theorem remTy_128_val (t : IntTy) (ht : t = .u128 ∨ t = .i128) (x : Int)
    (hx : x.natAbs < 2 ^ 128) : (remTy t x).val = wrapInt t x := by
  have ha := Int.natAbs_eq x
  have hk : nlimbs x ≤ 2 := (nlimbs_le_iff x 2).2 hx
  have h1 : nlimbs x ≤ 1 → x.natAbs < 2 ^ 64 := (nlimbs_le_iff x 1).1
  have h0 : nlimbs x = 0 → x = 0 := fun h => by
    by_cases hne : x = 0
    · exact hne
    · have := nlimbs_pos x hne; omega
  rcases ht with rfl | rfl <;>
  · unfold remTy flipsignTy
    rw [if_neg (by decide)]
    rw [show min (nlimbs x) ((IntTy.bits _ / 8 + 7) / 8) = nlimbs x by simp only [IntTy.bits]; omega]
    rcases (by omega : nlimbs x = 0 ∨ nlimbs x = 1 ∨ nlimbs x = 2) with h | h | h
    · have := h0 h; subst this; decide
    · have hx1 := h1 (by omega)
      rw [h]; dsimp only; rw [show List.range 1 = [0] from rfl]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hneg : x < 0 <;> simp only [hneg, ↓reduceIte, jint_neg_val, jint_add_val,
        jint_mul_val, jint_wrap_val, jint_lit_val, Nat.mul_zero, Int.reducePow,
        wrap_zero, wrap_add_r, wrap_neg, wrap_mul_one] <;>
        congr 1 <;> simp only [limb] <;> wsimp <;> generalize x.natAbs = n at * <;> omega
    · rw [h]; dsimp only; rw [show List.range 2 = [0, 1] from rfl]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hneg : x < 0 <;> simp only [hneg, ↓reduceIte, jint_neg_val, jint_add_val,
        jint_mul_val, jint_wrap_val, jint_lit_val, Nat.mul_zero, Nat.mul_one, Int.reducePow,
        wrap_zero, wrap_add_l, wrap_add_r, wrap_neg, wrap_mul_one, wrap_mul_2_64] <;>
        congr 1 <;> simp only [limb] <;> wsimp <;> generalize x.natAbs = n at * <;> omega

theorem toSignedWide_eq (t : IntTy) (ht : t = .i64 ∨ t = .i128) (x : Int) :
    toSignedWide t x = JInt.convert t x := by
  have ha := Int.natAbs_eq x
  obtain ⟨k, hk, hiff, hv⟩ : ∃ k, (t.bits / 8 + 7) / 8 = k ∧
      (nlimbs x ≤ k ↔ x.natAbs < 2 ^ t.bits) ∧
      (x.natAbs < 2 ^ t.bits → (remTy t x).val = wrapInt t x) := by
    rcases ht with rfl | rfl
    · exact ⟨1, rfl, nlimbs_le_iff x 1, fun _ => remTy_i64_val x⟩
    · exact ⟨2, rfl, nlimbs_le_iff x 2, remTy_128_val .i128 (.inr rfl) x⟩
  unfold toSignedWide JInt.convert
  dsimp only
  rw [hk]
  by_cases hr : t.min ≤ x ∧ x ≤ t.max
  · rw [dif_pos hr]
    have hx : x.natAbs < 2 ^ t.bits := by
      rcases ht with rfl | rfl <;> wsimp <;> generalize x.natAbs = n at * <;> omega
    have hy : (remTy t x).val = x := by
      rw [hv hx]; rcases ht with rfl | rfl <;> wsimp <;> generalize x.natAbs = n at * <;> omega
    have hc : ¬ ((decide (0 < x) != decide (0 < (remTy t x).val)) = true) := by rw [hy]; simp
    rw [if_pos (hiff.2 hx), if_neg hc]
    exact congrArg Except.ok (Subtype.ext hy)
  · rw [dif_neg hr]
    by_cases hn : nlimbs x ≤ k
    · have hx := hiff.1 hn
      have hc : (decide (0 < x) != decide (0 < (remTy t x).val)) = true := by
        rw [hv hx]
        simp only [bne_iff_ne, ne_eq, decide_eq_decide]
        rcases ht with rfl | rfl <;> wsimp <;> generalize x.natAbs = n at * <;> omega
      rw [if_pos hn, if_pos hc]
    · rw [if_neg hn]

theorem toUnsignedWide_eq (t : IntTy) (ht : t = .u64 ∨ t = .u128) (x : Int) :
    toUnsignedWide t x = JInt.convert t x := by
  have ha := Int.natAbs_eq x
  have hp := nlimbs_pos x
  obtain ⟨k, hk, hiff, hv⟩ : ∃ k, (t.bits / 8 + 7) / 8 = k ∧
      (nlimbs x ≤ k ↔ x.natAbs < 2 ^ t.bits) ∧
      (x.natAbs < 2 ^ t.bits → (remTy t x).val = wrapInt t x) := by
    rcases ht with rfl | rfl
    · exact ⟨1, rfl, nlimbs_le_iff x 1, fun _ => remTy_u64_val x⟩
    · exact ⟨2, rfl, nlimbs_le_iff x 2, remTy_128_val .u128 (.inl rfl) x⟩
  have hsz : size x = if x < 0 then -(nlimbs x : Int) else nlimbs x := rfl
  unfold toUnsignedWide JInt.convert
  rw [hk]
  by_cases hr : t.min ≤ x ∧ x ≤ t.max
  · rw [dif_pos hr]
    have hx : x.natAbs < 2 ^ t.bits := by
      rcases ht with rfl | rfl <;> wsimp <;> generalize x.natAbs = n at * <;> omega
    have hx0 : 0 ≤ x := by rcases ht with rfl | rfl <;> wsimp <;> omega
    have hs : size x = nlimbs x := by rw [hsz, if_neg (by omega)]
    have hc : 0 ≤ size x ∧ size x ≤ (k : Int) := by
      rw [hs]; have := hiff.2 hx; omega
    rw [if_pos hc]
    exact congrArg Except.ok (Subtype.ext (by
      rw [hv hx]; rcases ht with rfl | rfl <;> wsimp <;> omega))
  · rw [dif_neg hr]
    have hc : ¬ (0 ≤ size x ∧ size x ≤ (k : Int)) := by
      intro ⟨c1, c2⟩
      by_cases hneg : x < 0
      · rw [hsz, if_pos hneg] at c1; have := hp (by omega); omega
      · rw [hsz, if_neg hneg] at c2
        have hn : nlimbs x ≤ k := by omega
        have hx := hiff.1 hn
        rcases ht with rfl | rfl <;> wsimp <;> generalize x.natAbs = n at * <;> omega
    rw [if_neg hc]

theorem sameJl_self {t : IntTy} (r : Jl (JInt t)) :
    sameJl Subtype.val r (r.map Subtype.val) = true := by
  cases r <;> simp [sameJl, Except.map]

theorem narrow_via (s t : IntTy) (x : Int) (hmin : s.min ≤ t.min) (hmax : t.max ≤ s.max) :
    sameJl Subtype.val (JInt.convert s x >>= fun y => JInt.convert t y.val)
      ((JInt.convert t x).map Subtype.val) = true := by
  by_cases hr : s.min ≤ x ∧ x ≤ s.max
  · have e : JInt.convert s x = .ok ⟨x, hr⟩ := dif_pos hr
    rw [e]
    exact sameJl_self _
  · have e1 : JInt.convert s x = .error (.inexactError s.name) := dif_neg hr
    have e2 : JInt.convert t x = .error (.inexactError t.name) := dif_neg (by omega)
    rw [e1, e2]
    rfl

end JuliaLean.BigNums.ConvProofs

namespace JuliaLean.BigNums

open JuliaLean ConvProofs

theorem toIntExact_proven : ToIntExact := by
  intro t x
  cases t
  all_goals simp only [toIntTy, IntTy.signed, IntTy.bits, ↓reduceIte, Bool.false_eq_true,
    Nat.reduceLT]
  · rw [toSignedWide_eq .i64 (.inl rfl)]; exact narrow_via .i64 .i8 x (by decide) (by decide)
  · rw [toSignedWide_eq .i64 (.inl rfl)]; exact narrow_via .i64 .i16 x (by decide) (by decide)
  · rw [toSignedWide_eq .i64 (.inl rfl)]; exact narrow_via .i64 .i32 x (by decide) (by decide)
  · rw [toSignedWide_eq .i64 (.inl rfl)]; exact sameJl_self _
  · rw [toSignedWide_eq .i128 (.inr rfl)]; exact sameJl_self _
  · rw [toUnsignedWide_eq .u64 (.inl rfl)]; exact narrow_via .u64 .u8 x (by decide) (by decide)
  · rw [toUnsignedWide_eq .u64 (.inl rfl)]; exact narrow_via .u64 .u16 x (by decide) (by decide)
  · rw [toUnsignedWide_eq .u64 (.inl rfl)]; exact narrow_via .u64 .u32 x (by decide) (by decide)
  · rw [toUnsignedWide_eq .u64 (.inl rfl)]; exact sameJl_self _
  · rw [toUnsignedWide_eq .u128 (.inr rfl)]; exact sameJl_self _

end JuliaLean.BigNums
