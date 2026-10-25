import Lean
import JuliaLean.RandomSampling.Props

/-! Proof that the generic `rand(rng, Float64)` lies in `[0, 1)`. -/

set_option maxHeartbeats 4000000

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

open private JuliaLean.Float.F64.floorLog2Rat JuliaLean.Float.F64.roundQuotient
  JuliaLean.Float.F64.packRounded from JuliaLean.Float.Basic

theorem log2_eq_of {n k : Nat} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : n.log2 = k := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hn : n ≠ 0 := by omega
  apply Nat.le_antisymm
  · have := (Nat.log2_lt hn).2 h2; omega
  · apply Classical.byContradiction; intro hc
    have := (Nat.log2_lt hn).1 (show n.log2 < k by omega)
    omega

theorem toBits_ofBits_lt (n : Nat) (h : n < 2 ^ 64) : F64.toBits (F64.ofBits n) = n := by
  unfold F64.toBits F64.ofBits; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- A float whose bits are below those of `1.0` lies in `[0, 1)`. -/
theorem closeOpen_of_bits (r : F64) (h : F64.toBits r < 1023 * 2 ^ 52) :
    F64.le F64.zero r = true ∧ F64.lt r F64.one = true := by
  have h' : F64.toBits r < 4607182418800017408 := by
    simp only [Nat.reducePow, Nat.reduceMul] at h; exact h
  have hnan : F64.isnan r = false := by
    unfold F64.isnan F64.exponentField
    have : F64.toBits r / 2 ^ 52 % 2048 ≠ 2047 := by
      simp only [Nat.reducePow]; omega
    simp [this]
  have hsign : F64.signbit r = false := by
    unfold F64.signbit
    simp only [Nat.reducePow, decide_eq_false_iff_not]; omega
  have hzero : F64.iszero r = decide (F64.toBits r = 0) := by
    unfold F64.iszero F64.abs
    rw [toBits_ofBits_lt _ (by
      have := Nat.mod_lt (F64.toBits r) (show 0 < 2 ^ 63 from Nat.two_pow_pos _)
      have : 2 ^ 63 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)
      omega)]
    rw [Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
    simp
  have hz : F64.toBits F64.zero = 0 := by decide
  have ho : F64.toBits F64.one = 4607182418800017408 := by decide
  have hnz : F64.isnan F64.zero = false := by decide
  have hno : F64.isnan F64.one = false := by decide
  have hsz : F64.signbit F64.zero = false := by decide
  have hso : F64.signbit F64.one = false := by decide
  have hzz : F64.iszero F64.zero = true := by decide
  have hzo : F64.iszero F64.one = false := by decide
  unfold F64.le F64.lt F64.eq
  rw [hnan, hsign, hzero, hz, ho, hnz, hno, hsz, hso, hzz, hzo]
  by_cases h0 : F64.toBits r = 0
  · simp [h0]
  · simp [h0]; omega

theorem toRat_x (f : Nat) (hf : f < 2 ^ 52) :
    F64.toRat (F64.ofBits (2 ^ 52 * 1023 + f)) = (((2 ^ 52 + f : Nat) : Int), 2 ^ 52) := by
  have hb : F64.toBits (F64.ofBits (2 ^ 52 * 1023 + f)) = 2 ^ 52 * 1023 + f :=
    toBits_ofBits_lt _ (by omega)
  unfold F64.toRat F64.isfinite F64.exponentField F64.fraction F64.signbit
  rw [hb]
  simp only [Nat.reducePow, Nat.reduceMul] at hf ⊢
  have e1 : (4607182418800017408 + f) / 4503599627370496 % 2048 = 1023 := by omega
  have e2 : (4607182418800017408 + f) % 4503599627370496 = f := by omega
  have e3 : ¬ (4607182418800017408 + f ≥ 9223372036854775808) := by omega
  simp only [e1, e2, e3, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp
  omega

theorem sub_one_eq (f : Nat) (hf : f < 2 ^ 52) :
    F64.sub (F64.ofBits (2 ^ 52 * 1023 + f)) F64.one =
      F64.roundRat ((f * 2 ^ 52 : Nat) : Int) (2 ^ 104) false := by
  have hb : F64.toBits (F64.ofBits (2 ^ 52 * 1023 + f)) = 2 ^ 52 * 1023 + f :=
    toBits_ofBits_lt _ (by omega)
  have hnx : F64.isnan (F64.ofBits (2 ^ 52 * 1023 + f)) = false := by
    unfold F64.isnan F64.exponentField; rw [hb]
    simp only [Nat.reducePow, Nat.reduceMul] at hf ⊢
    have : (4607182418800017408 + f) / 4503599627370496 % 2048 = 1023 := by omega
    simp [this]
  have hix : F64.isinf (F64.ofBits (2 ^ 52 * 1023 + f)) = false := by
    unfold F64.isinf F64.abs; rw [hb]
    simp only [Nat.reducePow, Nat.reduceMul] at hf ⊢
    rw [toBits_ofBits_lt _ (by omega)]
    simp; omega
  have hsx : F64.signbit (F64.ofBits (2 ^ 52 * 1023 + f)) = false := by
    unfold F64.signbit; rw [hb]; simp only [Nat.reducePow, Nat.reduceMul] at hf ⊢; simp; omega
  have hy : F64.neg F64.one = F64.ofBits 0xbff0000000000000 := by decide
  have hno : F64.isnan F64.one = false := by decide
  have hny : F64.isnan (F64.ofBits 0xbff0000000000000) = false := by decide
  have hiy : F64.isinf (F64.ofBits 0xbff0000000000000) = false := by decide
  have hsy : F64.signbit (F64.ofBits 0xbff0000000000000) = true := by decide
  have hry : F64.toRat (F64.ofBits 0xbff0000000000000) =
      (-4503599627370496, 4503599627370496) := by decide
  unfold F64.sub F64.add
  rw [hy, hnx, hno, hny, hix, hiy, hsx, toRat_x f hf, hry]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  congr 1
  · simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, Int.reducePow]
    omega

/-- `1 + f/2^52 - 1` is `f/2^52`, whose bits are below those of `1.0`. -/
theorem roundRat_bits (f : Nat) (hf0 : 0 < f) (hf : f < 2 ^ 52) :
    F64.toBits (F64.roundRat ((f * 2 ^ 52 : Nat) : Int) (2 ^ 104) false) < 1023 * 2 ^ 52 := by
  have hfne : f ≠ 0 := by omega
  generalize hL : f.log2 = L
  have hL1 : 2 ^ L ≤ f := hL ▸ Nat.log2_self_le hfne
  have hL2 : f < 2 ^ (L + 1) := hL ▸ Nat.lt_log2_self
  have hL52 : L < 52 := by rw [← hL]; exact (Nat.log2_lt hfne).2 hf
  -- the significand `Q = f * 2^(52-L)` has exactly 53 bits
  have hP : 2 ^ (52 - L) * 2 ^ L = 2 ^ 52 := by rw [← Nat.pow_add]; congr 1; omega
  have hQ1 : 2 ^ 52 ≤ f * 2 ^ (52 - L) := by
    rw [← hP, Nat.mul_comm (2 ^ (52 - L))]; exact Nat.mul_le_mul_right _ hL1
  have hQ2 : f * 2 ^ (52 - L) < 2 ^ 53 := by
    have : 2 ^ (52 - L) * 2 ^ (L + 1) = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
    rw [← this, Nat.mul_comm (2 ^ (52 - L))]
    exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
  have hlog : (f * 2 ^ 52).log2 = L + 52 := by
    apply log2_eq_of
    · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ hL1
    · rw [show L + 52 + 1 = (L + 1) + 52 by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
  have hbig : 2 ^ 104 ≤ f * 2 ^ 52 * 2 ^ (52 - L) := by
    rw [Nat.mul_right_comm, show 104 = 52 + 52 by rfl, Nat.pow_add]
    exact Nat.mul_le_mul_right _ hQ1
  have hfl : F64.floorLog2Rat (f * 2 ^ 52) (2 ^ 104) = (L : Int) - 52 := by
    unfold F64.floorLog2Rat
    rw [hlog, Nat.log2_two_pow]
    have h1 : ¬ (((L + 52 : Nat) : Int) - ((104 : Nat) : Int) ≥ 0) := by omega
    have h2 : (-(((L + 52 : Nat) : Int) - ((104 : Nat) : Int))).toNat = 52 - L := by omega
    simp only [h1, ↓reduceIte, h2]
    rw [if_neg (by omega)]
    omega
  have hscaled : f * 2 ^ 52 * 2 ^ (104 - L) = f * 2 ^ (52 - L) * 2 ^ 104 := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  have hrq : F64.roundQuotient (f * 2 ^ 52 * 2 ^ (104 - L)) (2 ^ 104) = f * 2 ^ (52 - L) := by
    unfold F64.roundQuotient
    rw [hscaled, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_mod_left]
    simp
  unfold F64.roundRat
  have hne : ((f * 2 ^ 52 : Nat) : Int) ≠ 0 := by
    have : 0 < f * 2 ^ 52 := Nat.mul_pos hf0 (Nat.two_pow_pos _)
    omega
  simp only [Nat.reducePow, Nat.reduceMul] at hfl hrq hQ1 hQ2 hf ⊢
  simp only [show (20282409603651670423947251286016 == 0) = false by decide, Bool.false_eq_true,
    ↓reduceIte, hne, beq_iff_eq, Int.natAbs_natCast]
  rw [show (decide (((f * 4503599627370496 : Nat) : Int) < 0)) = false by simp, hfl]
  rw [if_neg (by omega), if_neg (by omega)]
  have hk : max ((L : Int) - 52 - 52) (-1074) = (L : Int) - 104 := by omega
  have hk2 : (-((L : Int) - 104)).toNat = 104 - L := by omega
  simp only [hk, hk2, show ¬ ((L : Int) - 104 ≥ 0) by omega, ↓reduceIte]
  simp only [Nat.reducePow, Nat.reduceMul] at hrq
  rw [hrq]
  unfold F64.packRounded
  generalize hQ : f * 2 ^ (52 - L) = Q at hQ1 hQ2
  simp only [Nat.reducePow] at hQ1 hQ2
  have hQ0 : (Q == 0) = false := by simp; omega
  rw [hQ0]
  simp only [Bool.false_eq_true, ↓reduceIte, show ¬ (Q ≥ 9007199254740992) by omega,
    show ¬ ((L : Int) - 104 + 1075 ≥ 2047) by omega, show ¬ (Q < 4503599627370496) by omega]
  have he : ((L : Int) - 104 + 1075).toNat = L + 971 := by omega
  rw [he, toBits_ofBits_lt _ (by omega)]
  omega

theorem randFloat64CloseOpen_proven : RandFloat64CloseOpen := by
  intro σ g st
  apply closeOpen_of_bits
  unfold randFloat64
  simp only
  generalize ((g.next st .raw52).1 : JInt .u64).val.toNat = w
  have hf : w &&& 0x000fffffffffffff = w % 2 ^ 52 := by
    rw [show (0x000fffffffffffff : Nat) = 2 ^ 52 - 1 by decide]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have hlt : w % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hor : 0x3ff0000000000000 ||| w % 2 ^ 52 = 2 ^ 52 * 1023 + w % 2 ^ 52 := by
    rw [show (0x3ff0000000000000 : Nat) = 2 ^ 52 * 1023 by decide]
    exact (Nat.two_pow_add_eq_or_of_lt hlt 1023).symm
  rw [hf, hor, sub_one_eq _ hlt]
  generalize w % 2 ^ 52 = f at hlt
  by_cases hf0 : f = 0
  · subst hf0
    have : F64.roundRat (((0 * 2 ^ 52 : Nat)) : Int) (2 ^ 104) false = F64.zero := by decide
    rw [this]; decide
  · exact roundRat_bits f (by omega) hlt

end JuliaLean.RandomSampling
