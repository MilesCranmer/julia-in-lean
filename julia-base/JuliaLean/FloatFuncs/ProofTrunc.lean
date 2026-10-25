import JuliaLean.FloatFuncs.Props
import JuliaLean.MathFuncs.ProofsBits

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs.ProofsBits

namespace ProofTrunc

def mantissa (x : F64) : Nat :=
  F64.fraction x + if F64.exponentField x = 0 then 0 else 2^52

def numerator (x : F64) : Nat := mantissa x * 2^(F64.exponentField x - 1075)

def denominator (x : F64) : Nat :=
  2^(if F64.exponentField x = 0 then 1074 else 1075 - F64.exponentField x)

def quotient (x : F64) : Nat := numerator x / denominator x

theorem rat_parts (x : F64) (hfin : F64.isfinite x = true) :
    F64.toRat x =
      (if F64.signbit x then -(numerator x : Int) else (numerator x : Int), denominator x) := by
  have he : F64.exponentField x < 2047 := by
    have := Nat.mod_lt (F64.toBits x / 2^52) (by decide : 0 < 2048)
    simp only [F64.isfinite, bne_iff_ne] at hfin
    unfold F64.exponentField at *
    omega
  by_cases hz : F64.exponentField x = 0
  · rw [toRat_subn x hz]
    simp [numerator, mantissa, denominator, hz, F64.fraction, Nat.mul_one]
  · by_cases hs : F64.exponentField x ≤ 1074
    · rw [toRat_norm x (by exact Nat.one_le_iff_ne_zero.mpr hz) hs]
      change (if F64.signbit x then -((F64.fraction x + 2^52 : Nat) : Int)
        else ((F64.fraction x + 2^52 : Nat) : Int), 2^(1075 - F64.exponentField x)) = _
      simp only [numerator, mantissa, denominator, hz, ↓reduceIte,
        Nat.sub_eq_zero_of_le (by omega : F64.exponentField x ≤ 1075),
        Nat.pow_zero, Nat.mul_one]
    · rw [toRat_big x (by change 1075 ≤ F64.exponentField x; omega)
        (by change F64.exponentField x ≤ 2046; omega)]
      change ((if F64.signbit x then -((F64.fraction x + 2^52 : Nat) : Int)
        else ((F64.fraction x + 2^52 : Nat) : Int)) *
          ((2^(F64.exponentField x - 1075) : Nat) : Int), 1) = _
      simp only [numerator, mantissa, denominator, hz, ↓reduceIte,
        Nat.sub_eq_zero_of_le (by omega : 1075 ≤ F64.exponentField x), Nat.pow_zero,
        Int.natCast_mul]
      split <;> simp [Int.neg_mul]

theorem tdiv_parts (x : F64) (hfin : F64.isfinite x = true) :
    (F64.toRat x).1.tdiv (F64.toRat x).2 =
      if F64.signbit x then -(quotient x : Int) else (quotient x : Int) := by
  rw [rat_parts x hfin]
  cases F64.signbit x <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_tdiv, ← Int.ofNat_tdiv, quotient]

theorem quotient_small (x : F64) (he : F64.exponentField x < 1023) :
    quotient x = 0 := by
  have hf : F64.fraction x < 2^52 := Nat.mod_lt _ (by decide)
  have hshift : F64.exponentField x - 1075 = 0 := by omega
  have hm : mantissa x < 2^53 := by
    unfold mantissa
    split <;> omega
  have hd : 2^53 ≤ denominator x := by
    unfold denominator
    apply Nat.pow_le_pow_right (by decide)
    split <;> omega
  unfold quotient numerator
  rw [hshift]
  simp only [Nat.pow_zero, Nat.mul_one]
  exact Nat.div_eq_of_lt (by omega)

theorem quotient_binade (x : F64) (he : 1023 ≤ F64.exponentField x) :
    2^(F64.exponentField x - 1023) ≤ quotient x ∧
      quotient x < 2^(F64.exponentField x - 1022) := by
  have hf : F64.fraction x < 2^52 := Nat.mod_lt _ (by decide)
  have hz : F64.exponentField x ≠ 0 := by omega
  have hm1 : 2^52 ≤ mantissa x := by simp [mantissa, hz]
  have hm2 : mantissa x < 2^53 := by simp only [mantissa, hz, ↓reduceIte]; omega
  by_cases hs : F64.exponentField x ≤ 1074
  · have hd : 0 < 2^(1075 - F64.exponentField x) := Nat.two_pow_pos _
    have h1 : 2^(F64.exponentField x - 1023) * 2^(1075 - F64.exponentField x) = 2^52 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h2 : 2^(F64.exponentField x - 1022) * 2^(1075 - F64.exponentField x) = 2^53 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    simp only [quotient, numerator, denominator, hz, ↓reduceIte,
      Nat.sub_eq_zero_of_le (by omega : F64.exponentField x ≤ 1075),
      Nat.pow_zero, Nat.mul_one]
    constructor
    · exact (Nat.le_div_iff_mul_le hd).mpr (by rw [h1]; exact hm1)
    · exact (Nat.div_lt_iff_lt_mul hd).mpr (by rw [h2]; exact hm2)
  · have h1 : 2^52 * 2^(F64.exponentField x - 1075) = 2^(F64.exponentField x - 1023) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h2 : 2^53 * 2^(F64.exponentField x - 1075) = 2^(F64.exponentField x - 1022) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    simp only [quotient, numerator, denominator, hz, ↓reduceIte,
      Nat.sub_eq_zero_of_le (by omega : 1075 ≤ F64.exponentField x),
      Nat.pow_zero, Nat.div_one]
    constructor
    · rw [← h1]
      exact Nat.mul_le_mul_right _ hm1
    · rw [← h2]
      exact Nat.mul_lt_mul_of_pos_right hm2 (Nat.two_pow_pos _)

theorem quotient_lt_pow (x : F64) (b : Nat) :
    quotient x < 2^b ↔ F64.exponentField x < 1023 + b := by
  by_cases he : F64.exponentField x < 1023
  · rw [quotient_small x he]
    exact iff_of_true (Nat.two_pow_pos _) (by omega)
  · obtain ⟨h1, h2⟩ := quotient_binade x (by omega)
    constructor
    · intro h
      have hp : 2^(F64.exponentField x - 1023) < 2^b := by omega
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
      omega
    · intro h
      have hp : 2^(F64.exponentField x - 1022) ≤ 2^b :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega

theorem quotient_le_pow_small (x : F64) (b : Nat) (hb : b ≤ 51) :
    quotient x ≤ 2^b ↔
      F64.toBits x % 2^63 < (1023 + b) * 2^52 + 2^(52 - b) := by
  have ht := tb_lt x
  have hf : F64.fraction x < 2^52 := Nat.mod_lt _ (by decide)
  have he : F64.exponentField x < 2048 := Nat.mod_lt _ (by decide)
  by_cases hc : F64.exponentField x = 1023 + b
  · have hz : F64.exponentField x ≠ 0 := by omega
    have hs : F64.exponentField x - 1075 = 0 := by omega
    have hd : 1075 - F64.exponentField x = 52 - b := by omega
    have hp : 2^b * 2^(52 - b) = 2^52 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hd0 := Nat.two_pow_pos (52 - b)
    have hn : quotient x ≤ 2^b ↔ F64.fraction x < 2^(52 - b) := by
      simp only [quotient, numerator, denominator, mantissa, hz, ↓reduceIte,
        hs, hd, Nat.pow_zero, Nat.mul_one]
      rw [Nat.lt_succ_iff.symm, Nat.div_lt_iff_lt_mul hd0, Nat.succ_mul, hp]
      omega
    rw [hn]
    unfold F64.fraction F64.exponentField at *
    omega
  · have hl := quotient_lt_pow x b
    by_cases hlow : F64.exponentField x < 1023 + b
    · have hq := hl.mpr hlow
      have hr : F64.toBits x % 2^63 < (1023 + b) * 2^52 := by
        unfold F64.exponentField at hlow
        omega
      exact iff_of_true (Nat.le_of_lt hq) (Nat.lt_of_lt_of_le hr (Nat.le_add_right _ _))
    · obtain ⟨h1, -⟩ := quotient_binade x (by omega)
      have hp : 2^b < 2^(F64.exponentField x - 1023) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      have hd : 2^(52 - b) ≤ 2^52 := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : (1023 + b + 1) * 2^52 ≤ F64.toBits x % 2^63 := by
        unfold F64.exponentField at hlow hc
        omega
      exact iff_of_false (by omega) (by omega)

theorem quotient_le_pow_big (x : F64) (b : Nat) (hb : 52 ≤ b) (hb' : b < 1024) :
    quotient x ≤ 2^b ↔ F64.toBits x % 2^63 ≤ (1023 + b) * 2^52 := by
  have ht := tb_lt x
  have hf : F64.fraction x < 2^52 := Nat.mod_lt _ (by decide)
  by_cases hc : F64.exponentField x = 1023 + b
  · have hz : F64.exponentField x ≠ 0 := by omega
    have hs : 1075 - F64.exponentField x = 0 := by omega
    have hd : F64.exponentField x - 1075 = b - 52 := by omega
    have hp : 2^52 * 2^(b - 52) = 2^b := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hd0 := Nat.two_pow_pos (b - 52)
    have hn : quotient x ≤ 2^b ↔ F64.fraction x = 0 := by
      simp only [quotient, numerator, denominator, mantissa, hz, ↓reduceIte,
        hs, hd, Nat.pow_zero, Nat.div_one, Nat.add_mul, hp]
      constructor
      · intro h
        have hmul : F64.fraction x * 2^(b - 52) = 0 := by omega
        exact (Nat.mul_eq_zero.mp hmul).resolve_right (by omega)
      · intro h
        simp [h]
    rw [hn]
    unfold F64.fraction F64.exponentField at *
    omega
  · have hl := quotient_lt_pow x b
    by_cases hlow : F64.exponentField x < 1023 + b
    · have hq := hl.mpr hlow
      have hr : F64.toBits x % 2^63 < (1023 + b) * 2^52 := by
        unfold F64.exponentField at hlow
        omega
      exact iff_of_true (by omega) (by omega)
    · obtain ⟨h1, -⟩ := quotient_binade x (by omega)
      have hp : 2^b < 2^(F64.exponentField x - 1023) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      have hr : (1023 + b + 1) * 2^52 ≤ F64.toBits x % 2^63 := by
        unfold F64.exponentField at hlow hc
        omega
      exact iff_of_false (by omega) (by omega)

theorem quotient_lt_pow_bits (x : F64) (b : Nat) :
    quotient x < 2^b ↔ F64.toBits x % 2^63 < (1023 + b) * 2^52 := by
  rw [quotient_lt_pow]
  have ht := tb_lt x
  unfold F64.exponentField
  omega

theorem quotient_zero_bits (x : F64) :
    quotient x = 0 ↔ F64.toBits x % 2^63 < 1023 * 2^52 := by
  have h := quotient_lt_pow_bits x 0
  simp only [Nat.pow_zero, Nat.add_zero] at h
  omega

def width (t : IntTy) : Nat := if t.signed then t.bits - 1 else t.bits

def upperBits (t : IntTy) : Nat := (1023 + width t) * 2^52

def lowerBits (t : IntTy) : Nat :=
  if t.signed then
    2^63 + upperBits t + if t.bits < 64 then 2^(52 - width t) else 0
  else 2^63 + 1023 * 2^52

def bitTruncValid (t : IntTy) (x : F64) : Prop :=
  if F64.signbit x then
    if t.signed then
      if t.bits < 64 then F64.toBits x % 2^63 < upperBits t + 2^(52 - width t)
      else F64.toBits x % 2^63 ≤ upperBits t
    else F64.toBits x % 2^63 < 1023 * 2^52
  else F64.toBits x % 2^63 < upperBits t

theorem min_eq (t : IntTy) :
    t.min = if t.signed then -((2^(width t) : Nat) : Int) else 0 := by
  cases t <;> decide

theorem max_eq (t : IntTy) : t.max = ((2^(width t) : Nat) : Int) - 1 := by
  cases t <;> decide

theorem width_bounds (t : IntTy) :
    0 < width t ∧ width t < 1024 ∧ (t.bits < 64 ↔ width t ≤ 51) := by
  cases t <;> decide

theorem finite_range (t : IntTy) (x : F64) (hfin : F64.isfinite x = true) :
    bitTruncValid t x ↔
      t.min ≤ (F64.toRat x).1.tdiv (F64.toRat x).2 ∧
      (F64.toRat x).1.tdiv (F64.toRat x).2 ≤ t.max := by
  obtain ⟨hw0, hw1, hws⟩ := width_bounds t
  have hu := quotient_lt_pow_bits x (width t)
  have hz := quotient_zero_bits x
  have hp := Nat.two_pow_pos (width t)
  have hl :
      (if t.bits < 64 then F64.toBits x % 2^63 < upperBits t + 2^(52 - width t)
       else F64.toBits x % 2^63 ≤ upperBits t) ↔ quotient x ≤ 2^(width t) := by
    by_cases hs : t.bits < 64
    · simpa only [hs, ↓reduceIte, upperBits] using
        (quotient_le_pow_small x (width t) (hws.mp hs)).symm
    · simpa only [hs, ↓reduceIte, upperBits] using
        (quotient_le_pow_big x (width t) (by omega) hw1).symm
  rw [tdiv_parts x hfin, min_eq, max_eq]
  unfold bitTruncValid
  cases hs : F64.signbit x <;> cases ht : t.signed <;>
    simp only [hs, ht, Bool.false_eq_true, ↓reduceIte] <;>
    simp only [upperBits] at hl ⊢ <;> first | omega | (rw [hl]; omega)

theorem valid_finite (t : IntTy) (x : F64) (h : bitTruncValid t x) :
    F64.isfinite x = true := by
  have ht := tb_lt x
  have hm : F64.toBits x % 2^63 < 2047 * 2^52 := by
    cases t <;> cases hs : F64.signbit x <;>
      simp only [bitTruncValid, hs, width, upperBits, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceMul, Nat.reduceLT] at h <;> omega
  simp only [F64.isfinite, F64.exponentField, bne_iff_ne]
  omega

theorem trunc_range (t : IntTy) (x : F64) :
    bitTruncValid t x ↔
      F64.isfinite x = true ∧
      t.min ≤ (F64.toRat x).1.tdiv (F64.toRat x).2 ∧
      (F64.toRat x).1.tdiv (F64.toRat x).2 ≤ t.max := by
  constructor
  · intro h
    have hf := valid_finite t x h
    exact ⟨hf, (finite_range t x hf).mp h⟩
  · rintro ⟨hf, h⟩
    exact (finite_range t x hf).mpr h

theorem lower_constant (t : IntTy) :
    (if !t.signed || t.bits < 64 then F64.sub (F64.ofJInt (JInt.typemin t)) F64.one
     else F64.ofJInt (JInt.typemin t)) = F64.ofBits (lowerBits t) := by
  cases t <;> decide

theorem upper_constant (t : IntTy) :
    (if !t.signed || t.bits < 64 then F64.add (F64.ofJInt (JInt.typemax t)) F64.one
     else F64.ofJInt (JInt.typemax t)) = F64.ofBits (upperBits t) := by
  cases t <;> decide

theorem trunc_checks (t : IntTy) (x : F64) :
    (if !t.signed || t.bits < 64 then
      F64.lt (F64.sub (F64.ofJInt (JInt.typemin t)) F64.one) x &&
        F64.lt x (F64.add (F64.ofJInt (JInt.typemax t)) F64.one)
     else F64.le (F64.ofJInt (JInt.typemin t)) x &&
        F64.lt x (F64.ofJInt (JInt.typemax t))) = true ↔ bitTruncValid t x := by
  have hl := lower_constant t
  have hu := upper_constant t
  have ht := tb_lt x
  have hn := isnan_iff x
  have hz := iszero_iff x
  have hs := signbit_iff x
  by_cases hc : (!t.signed || t.bits < 64) = true
  · simp only [hc, ↓reduceIte] at hl hu ⊢
    rw [hl, hu, Bool.and_eq_true, lt_iff, lt_iff]
    cases t <;> cases sx : F64.signbit x <;>
      simp only [bitTruncValid, sx, width, lowerBits, upperBits, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_or,
        Bool.true_or, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul,
        Nat.reduceLT, decide_true, decide_false, tb_ofBits] at hc ⊢ <;>
      simp only [signbit_iff, signbit_f] at sx <;> simp_all <;> omega
  · have hc' : (!t.signed || t.bits < 64) = false := by
      cases h : (!t.signed || t.bits < 64) <;> simp_all
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at hl hu ⊢
    rw [hl, hu, Bool.and_eq_true, F64.le, Bool.or_eq_true, lt_iff, eq_iff, lt_iff]
    cases t <;> cases sx : F64.signbit x <;>
      simp only [bitTruncValid, sx, width, lowerBits, upperBits, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_or,
        Bool.true_or, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul,
        Nat.reduceLT, decide_true, decide_false, tb_ofBits] at hc ⊢ <;>
      simp only [signbit_iff, signbit_f] at sx <;> simp_all <;> omega

theorem signed_mod_zero (a d : Nat) (s : Bool) (hd : 0 < d) :
    ((if s then -(a : Int) else (a : Int)) % (d : Int) == 0) = (a % d == 0) := by
  have hr := Nat.mod_lt a hd
  apply Bool.eq_iff_iff.mpr
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, ← Int.natCast_emod,
      Int.natCast_eq_zero]
  · simp only [↓reduceIte, beq_iff_eq, Int.neg_emod, ← Int.natCast_emod]
    omega

theorem integral_parts (x : F64) (hfin : F64.isfinite x = true) :
    (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0 ↔
      numerator x % denominator x = 0 := by
  rw [rat_parts x hfin]
  have h := Bool.eq_iff_iff.mp
    (signed_mod_zero (numerator x) (denominator x) (F64.signbit x) (Nat.two_pow_pos _))
  simpa only [beq_iff_eq] using h

theorem numerator_exact (x : F64) (hi : numerator x % denominator x = 0) :
    numerator x = quotient x * denominator x := by
  have h := Nat.mod_add_div (numerator x) (denominator x)
  rw [hi, Nat.zero_add] at h
  simpa only [quotient, Nat.mul_comm] using h.symm

theorem quotient_zero_integral (x : F64) (hi : numerator x % denominator x = 0) :
    quotient x = 0 ↔ F64.toBits x % 2^63 = 0 := by
  have ht := tb_lt x
  constructor
  · intro hq
    have hn := numerator_exact x hi
    rw [hq, Nat.zero_mul] at hn
    have hm : mantissa x = 0 := by
      exact (Nat.mul_eq_zero.mp hn).resolve_right (Nat.ne_of_gt (Nat.two_pow_pos _))
    unfold mantissa at hm
    have he : F64.exponentField x = 0 := by
      by_cases h : F64.exponentField x = 0
      · exact h
      · simp only [h, ↓reduceIte] at hm
        omega
    simp only [he, ↓reduceIte, Nat.add_zero] at hm
    unfold F64.fraction at hm
    unfold F64.exponentField at he
    omega
  · intro h
    exact (quotient_zero_bits x).mpr (by omega)

theorem quotient_le_pow_integral (x : F64) (b : Nat) (hb : b < 1024)
    (hi : numerator x % denominator x = 0) :
    quotient x ≤ 2^b ↔ F64.toBits x % 2^63 ≤ (1023 + b) * 2^52 := by
  have ht := tb_lt x
  have hf : F64.fraction x < 2^52 := Nat.mod_lt _ (by decide)
  have hlt := quotient_lt_pow_bits x b
  constructor
  · intro hq
    by_cases hstrict : quotient x < 2^b
    · have := hlt.mp hstrict
      omega
    have hqe : quotient x = 2^b := by omega
    have hnext := quotient_lt_pow x (b + 1)
    have hprev := quotient_lt_pow x b
    have hp : 2^b < 2^(b + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have he : F64.exponentField x = 1023 + b := by
      have := hnext.mp (by omega)
      omega
    have hz : F64.exponentField x ≠ 0 := by omega
    have hn := numerator_exact x hi
    have hfrac : F64.fraction x = 0 := by
      by_cases hs : b ≤ 51
      · have hp : 2^b * 2^(52 - b) = 2^52 := by
          rw [← Nat.pow_add]
          congr 1
          omega
        simp only [numerator, mantissa, denominator, hz, ↓reduceIte,
          Nat.sub_eq_zero_of_le (by omega : F64.exponentField x ≤ 1075),
          Nat.pow_zero, Nat.mul_one, hqe,
          show 1075 - F64.exponentField x = 52 - b by omega, hp] at hn
        omega
      · have hp : 2^52 * 2^(b - 52) = 2^b := by
          rw [← Nat.pow_add]
          congr 1
          omega
        simp only [numerator, mantissa, denominator, hz, ↓reduceIte,
          Nat.sub_eq_zero_of_le (by omega : 1075 ≤ F64.exponentField x),
          Nat.pow_zero, Nat.mul_one, hqe,
          show F64.exponentField x - 1075 = b - 52 by omega, Nat.add_mul, hp] at hn
        have hmul : F64.fraction x * 2^(b - 52) = 0 := by omega
        exact (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt (Nat.two_pow_pos _))
    unfold F64.fraction at hfrac
    unfold F64.exponentField at he
    omega
  · intro h
    by_cases hs : b ≤ 51
    · apply (quotient_le_pow_small x b hs).mpr
      have := Nat.two_pow_pos (52 - b)
      omega
    · exact (quotient_le_pow_big x b (by omega) hb).mpr h

def bitIntValid (t : IntTy) (x : F64) : Prop :=
  if F64.signbit x then
    if t.signed then F64.toBits x % 2^63 ≤ upperBits t
    else F64.toBits x % 2^63 = 0
  else F64.toBits x % 2^63 < upperBits t

theorem min_constant (t : IntTy) :
    F64.ofJInt (JInt.typemin t) =
      F64.ofBits (if t.signed then 2^63 + upperBits t else 0) := by
  cases t <;> decide

theorem int_checks (t : IntTy) (x : F64) :
    (F64.le (F64.ofJInt (JInt.typemin t)) x &&
      F64.lt x (if !t.signed || t.bits < 64 then
        F64.add (F64.ofJInt (JInt.typemax t)) F64.one
        else F64.ofJInt (JInt.typemax t))) = true ↔ bitIntValid t x := by
  rw [min_constant, upper_constant, Bool.and_eq_true, F64.le, Bool.or_eq_true,
    lt_iff, eq_iff, lt_iff]
  have ht := tb_lt x
  cases t <;> cases sx : F64.signbit x <;>
    simp only [bitIntValid, sx, width, upperBits, IntTy.signed, IntTy.bits,
      Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceMul, tb_ofBits] <;>
    simp only [signbit_iff, signbit_f] at sx <;> simp_all <;> omega

theorem int_valid_finite (t : IntTy) (x : F64) (h : bitIntValid t x) :
    F64.isfinite x = true := by
  have ht := tb_lt x
  have hm : F64.toBits x % 2^63 < 2047 * 2^52 := by
    cases t <;> cases hs : F64.signbit x <;>
      simp only [bitIntValid, hs, width, upperBits, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceMul] at h <;> omega
  simp only [F64.isfinite, F64.exponentField, bne_iff_ne]
  omega

theorem finite_int_range (t : IntTy) (x : F64) (hfin : F64.isfinite x = true)
    (hi : (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0) :
    bitIntValid t x ↔
      t.min ≤ (F64.toRat x).1 / ((F64.toRat x).2 : Int) ∧
      (F64.toRat x).1 / ((F64.toRat x).2 : Int) ≤ t.max := by
  have hdiv := Int.tdiv_eq_ediv_of_dvd (Int.dvd_iff_emod_eq_zero.mpr hi)
  rw [← hdiv, tdiv_parts x hfin, min_eq, max_eq]
  have hir := (integral_parts x hfin).mp hi
  have hu := quotient_lt_pow_bits x (width t)
  have hl := quotient_le_pow_integral x (width t) (width_bounds t).2.1 hir
  have hz := quotient_zero_integral x hir
  have hp := Nat.two_pow_pos (width t)
  unfold bitIntValid upperBits
  cases hs : F64.signbit x <;> cases ht : t.signed <;>
    simp only [hs, ht, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem neg_fields (x : F64) :
    F64.exponentField (F64.neg x) = F64.exponentField x ∧
    F64.fraction (F64.neg x) = F64.fraction x := by
  have h := tb_lt x
  simp only [F64.exponentField, F64.fraction, tb_neg]
  split <;> constructor <;> omega

theorem neg_isfinite (x : F64) : F64.isfinite (F64.neg x) = F64.isfinite x := by
  simp only [F64.isfinite, (neg_fields x).1]

theorem neg_isnan (x : F64) : F64.isnan (F64.neg x) = F64.isnan x := by
  simp only [F64.isnan, (neg_fields x).1, (neg_fields x).2]

theorem neg_isinf (x : F64) : F64.isinf (F64.neg x) = F64.isinf x := by
  simp only [F64.isinf, abs_neg]

theorem toRat_neg (x : F64) :
    F64.toRat (F64.neg x) = (-(F64.toRat x).1, (F64.toRat x).2) := by
  simp only [F64.toRat, neg_isfinite, (neg_fields x).1, (neg_fields x).2, signbit_neg]
  cases hf : F64.isfinite x <;> cases hs : F64.signbit x <;>
    simp only [hf, hs, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte, Int.neg_neg, Int.neg_mul, Int.neg_zero]
  all_goals split <;> simp_all [Int.neg_mul]
  all_goals split <;> simp_all [Int.neg_mul]

theorem finite_not_nan (x : F64) (h : F64.isfinite x = true) : F64.isnan x = false := by
  have hE : F64.exponentField x ≠ 2047 := by simpa [F64.isfinite] using h
  simp [F64.isnan, hE]

theorem finite_not_inf (x : F64) (h : F64.isfinite x = true) : F64.isinf x = false := by
  have hE : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
    simpa [F64.isfinite, F64.exponentField] using h
  have ht := tb_lt x
  rw [Bool.eq_false_iff, ne_eq, isinf_iff]
  omega


theorem sub_finite (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.sub x y = F64.roundRat
      ((F64.toRat x).1 * (F64.toRat y).2 - (F64.toRat y).1 * (F64.toRat x).2)
      ((F64.toRat x).2 * (F64.toRat y).2) (F64.signbit x && !F64.signbit y) := by
  simp only [F64.sub, F64.add, finite_not_nan x hx, finite_not_nan y hy,
    neg_isnan, neg_isinf, finite_not_inf x hx, finite_not_inf y hy,
    Bool.false_eq_true, ↓reduceIte, toRat_neg, Prod.fst, Prod.snd,
    signbit_neg, Int.neg_mul, Int.sub_eq_add_neg]


theorem norm_fields (s : Bool) (E M : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046)
    (hM1 : 2^52 ≤ M) (hM2 : M < 2^53) :
    let y := F64.ofBits ((if s then 2^63 else 0) + E * 2^52 + (M - 2^52))
    F64.toBits y / 2^52 % 2048 = E ∧ F64.toBits y % 2^52 = M - 2^52 ∧
      F64.signbit y = s ∧ F64.isfinite y = true := by
  dsimp only
  simp only [F64.signbit, F64.isfinite, F64.exponentField, tb_ofBits]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;>
    constructor <;> try omega
  all_goals constructor <;> try omega
  all_goals constructor <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not,
    bne_iff_ne] <;> omega

theorem small_ofInt_bits (k : Nat) (s : Bool) (h0 : 0 < k) (hk : k < 2^52) :
    F64.ofInt (if s then -(k : Int) else (k : Int)) =
      F64.ofBits ((if s then 2^63 else 0) + (k.log2 + 1023) * 2^52 +
        (k * 2^(52 - k.log2) - 2^52)) := by
  obtain ⟨hL, -, -⟩ := log2_facts (by omega) hk
  obtain ⟨hM1, hM2, -⟩ := sub_mant (by omega) hk
  have hn : (if s then -(k : Int) else (k : Int)) ≠ 0 := by cases s <;> simp <;> omega
  have ha : (if s then -(k : Int) else (k : Int)).natAbs = k := by
    cases s <;> simp
  have hs : decide ((if s then -(k : Int) else (k : Int)) < 0) = s := by
    cases s <;> simp <;> omega
  have hf : fl2 k 1 = (k.log2 : Int) := by
    simpa using fl2_pow k 0 0 h0
  have hK : max ((k.log2 : Int) - 52) (-1074) = (k.log2 : Int) - 52 := by omega
  have hKt : (-((k.log2 : Int) - 52)).toNat = 52 - k.log2 := toNat_eq (by omega)
  have hEt : ((k.log2 : Int) - 52 + 1075).toNat = k.log2 + 1023 := toNat_eq (by omega)
  unfold F64.ofInt
  rw [roundRat_eq]
  simp only [show (1 == 0) = false by decide, show ((if s then -(k : Int) else (k : Int)) == 0) = false by simp [hn],
    Bool.false_eq_true, ↓reduceIte, ha, hs, hf]
  rw [ite_f (by omega), ite_f (by omega), hK, ite_f (by omega), hKt]
  simp only [Prod.fst, Prod.snd]
  rw [rq_exact _ 1 (by decide) (Nat.mod_one _), Nat.div_one,
    pk_norm s _ ((k.log2 : Int) - 52) hM1 hM2 (by omega) (by omega), hEt]
  simp only [Nat.add_assoc]

set_option simprocs false in
theorem ofInt_small (k : Nat) (s : Bool) (hk : k ≤ 2^53) :
    let y := F64.ofInt (if s then -(k : Int) else (k : Int))
    F64.isfinite y = true ∧ F64.signbit y = (s && (k != 0)) ∧
      (F64.toRat y).1 = (if s then -(k : Int) else (k : Int)) * (F64.toRat y).2 := by
  by_cases h0 : k = 0
  · subst k
    cases s <;> decide
  by_cases htop : k = 2^53
  · subst k
    cases s <;> decide
  have hk' : k < 2^53 := by omega
  by_cases hsmall : k < 2^52
  · rw [small_ofInt_bits k s (by omega) hsmall]
    obtain ⟨hL, -, -⟩ := log2_facts h0 hsmall
    obtain ⟨hM1, hM2, -⟩ := sub_mant h0 hsmall
    obtain ⟨hE, hF, hS, hfin⟩ := norm_fields s (k.log2 + 1023)
      (k * 2^(52 - k.log2)) (by omega) (by omega) hM1 hM2
    refine ⟨hfin, ?_, ?_⟩
    · simp only [hS, show (k != 0) = true by simp [h0], Bool.and_true]
    · rw [toRat_norm _ (by omega) (by omega)]
      simp only [Prod.fst, Prod.snd, hF, hS]
      have hM : k * 2^(52 - k.log2) - 2^52 + 2^52 = k * 2^(52 - k.log2) := by omega
      have hD : 1075 - (k.log2 + 1023) = 52 - k.log2 := by omega
      rw [hM, hE, hD]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, ite_false, ite_true,
        Int.natCast_mul, Int.neg_mul]
  · have hM1 : 2^52 ≤ k := by omega
    have hr := roundRat_norm k 0 0 s false hM1 hk' (by omega) (by omega)
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.sub_zero, ← Nat.add_assoc] at hr
    simp only [F64.ofInt, hr]
    obtain ⟨hE, hF, hS, hfin⟩ := norm_fields s 1075 k (by decide) (by decide) hM1 hk'
    refine ⟨hfin, ?_, ?_⟩
    · simp only [hS, show (k != 0) = true by simp [h0], Bool.and_true]
    · rw [toRat_big _ (by omega) (by omega)]
      simp only [Prod.fst, Prod.snd, hS, hE, hF, Nat.sub_self, Nat.pow_zero,
        Int.natCast_one, Int.mul_one]
      rw [show k - 2^52 + 2^52 = k by omega]

theorem iszero_signed_bits (s : Bool) (b : Nat) (h0 : 0 < b) (hb : b < 2^63) :
    F64.iszero (F64.ofBits ((if s then 2^63 else 0) + b)) = false := by
  rw [Bool.eq_false_iff, ne_eq, iszero_iff, tb_ofBits]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

theorem dyadic_iszero (a i j : Nat) (s zs : Bool) (ha : a < 2^53) (hi : i ≤ 1074) :
    F64.iszero (F64.roundRat
      (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int))
      (2^(i+j)) zs) = (a == 0) := by
  by_cases h0 : a = 0
  · subst a
    have hd : (2^(i+j) == 0) = false := by simp [Nat.ne_of_gt (Nat.two_pow_pos _)]
    simp only [Nat.zero_mul, Int.natCast_zero, Int.neg_zero, ite_self, roundRat_eq,
      hd, Bool.false_eq_true, BEq.rfl, ↓reduceIte]
    cases zs <;> decide
  have hpos : 0 < a := by omega
  have hL : a.log2 ≤ 52 := by have := (Nat.log2_lt h0).mpr ha; omega
  have hlow : 2^a.log2 ≤ a := Nat.log2_self_le h0
  have hupp : a < 2^(a.log2 + 1) := Nat.lt_log2_self
  have hscale : 0 < 2^(52 - a.log2) := Nat.two_pow_pos _
  have hp1 : 2^a.log2 * 2^(52 - a.log2) = 2^52 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hp2 : 2^(a.log2 + 1) * 2^(52 - a.log2) = 2^53 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hM1 : 2^52 ≤ a * 2^(52 - a.log2) := by
    rw [← hp1]; exact Nat.mul_le_mul_right _ hlow
  have hM2 : a * 2^(52 - a.log2) < 2^53 := by
    rw [← hp2]; exact Nat.mul_lt_mul_of_pos_right hupp hscale
  have hprod : 0 < a * 2^j := Nat.mul_pos hpos (Nat.two_pow_pos j)
  have hn : (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have habs : (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)).natAbs =
      a * 2^j := by
    cases s
    · rfl
    · change (-((a * 2^j : Nat) : Int)).natAbs = a * 2^j
      rw [Int.natAbs_neg]; rfl
  have hsign : decide ((if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)) < 0) = s := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
      decide_eq_false_iff_not, decide_eq_true_eq] <;> omega
  have hd : (2^(i+j) == 0) = false := by simp [Nat.ne_of_gt (Nat.two_pow_pos _)]
  have hfl : fl2 (a * 2^j) (2^(i+j)) = (a.log2 : Int) - (i : Int) := by
    rw [fl2_pow a j (i+j) hpos]
    omega
  have hn0 : ¬((if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)) == 0) = true := by
    simpa only [beq_iff_eq] using hn
  have hd0 : ¬(2^(i+j) == 0) = true := by rw [hd]; decide
  rw [roundRat_eq, ite_f hd0, ite_f hn0, habs, hsign, hfl,
    ite_f (by omega : ¬((a.log2 : Int) - (i : Int) ≥ 1024)),
    ite_f (by omega : ¬((a.log2 : Int) - (i : Int) < -1075))]
  rw [show (a == 0) = false by simp only [beq_eq_false_iff_ne]; exact h0]
  by_cases hnormal : (a.log2 : Int) - (i : Int) ≥ -1022
  · have hK : max ((a.log2 : Int) - (i : Int) - 52) (-1074) =
        (a.log2 : Int) - (i : Int) - 52 := by omega
    rw [hK]
    by_cases hK0 : (a.log2 : Int) - (i : Int) - 52 ≥ 0
    · have hi0 : i = 0 := by omega
      have hL52 : a.log2 = 52 := by omega
      subst i
      rw [hL52]
      simp only [Nat.zero_add, Int.natCast_zero]
      rw [show ((52 : Nat) : Int) - 0 - 52 = 0 by decide,
        ite_t (by decide : (0 : Int) ≥ 0)]
      simp only [Int.toNat_zero, Nat.pow_zero, Nat.mul_one, Prod.fst, Prod.snd]
      change F64.iszero (pk s (rq (a * 2^j) (2^j)) 0) = false
      rw [rq_exact _ _ (Nat.two_pow_pos j) (Nat.mul_mod_left _ _),
        Nat.mul_div_cancel _ (Nat.two_pow_pos j),
        pk_norm s a 0 (by simpa only [hL52, Nat.sub_self, Nat.pow_zero, Nat.mul_one] using hM1) ha
          (by decide) (by decide)]
      apply iszero_signed_bits
      · omega
      · omega
    · have hKt : (-((a.log2 : Int) - (i : Int) - 52)).toNat = i + 52 - a.log2 :=
        toNat_eq (by omega)
      rw [ite_f hK0, hKt]
      simp only [Prod.fst, Prod.snd]
      have hnum : a * 2^j * 2^(i + 52 - a.log2) =
          (a * 2^(52 - a.log2)) * 2^(i+j) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
        congr 2
        omega
      rw [hnum, rq_exact _ _ (Nat.two_pow_pos _) (Nat.mul_mod_left _ _),
        Nat.mul_div_cancel _ (Nat.two_pow_pos _),
        pk_norm s _ ((a.log2 : Int) - (i : Int) - 52) hM1 hM2 (by omega) (by omega)]
      have hEt : ((a.log2 : Int) - (i : Int) - 52 + 1075).toNat =
          a.log2 + 1023 - i := toNat_eq (by omega)
      rw [hEt]
      apply iszero_signed_bits <;> omega
  · have hK : max ((a.log2 : Int) - (i : Int) - 52) (-1074) = -1074 := by omega
    rw [hK, ite_f (by decide : ¬((-1074 : Int) ≥ 0))]
    simp only [Prod.fst, Prod.snd]
    change F64.iszero (pk s (rq (a * 2^j * 2^1074) (2^(i+j))) (-1074)) = false
    have hnum : a * 2^j * 2^1074 = (a * 2^(1074-i)) * 2^(i+j) := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    have hQ0 : 0 < a * 2^(1074-i) := Nat.mul_pos hpos (Nat.two_pow_pos _)
    have hQ : a * 2^(1074-i) < 2^52 := by
      calc
        a * 2^(1074-i) < 2^(a.log2+1) * 2^(1074-i) :=
          Nat.mul_lt_mul_of_pos_right hupp (Nat.two_pow_pos _)
        _ = 2^(a.log2+1+(1074-i)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2^52 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hnum, rq_exact _ _ (Nat.two_pow_pos _) (Nat.mul_mod_left _ _),
      Nat.mul_div_cancel _ (Nat.two_pow_pos _), pk_sub s _ hQ0 hQ]
    apply iszero_signed_bits <;> omega

theorem trunc_formula (x : F64) : F64.trunc x =
    if F64.isnan x then F64.ofBits (Nat.lor (F64.toBits x) 0x0008000000000000)
    else if F64.isinf x then x
    else
      let q := (F64.toRat x).1.natAbs / (F64.toRat x).2
      if q == 0 then F64.zero (F64.signbit x)
      else F64.ofInt (if F64.signbit x then -(q : Int) else (q : Int)) := by
  rfl

theorem finite_den_pow (x : F64) (hx : F64.isfinite x = true) :
    ∃ j : Nat, j ≤ 1074 ∧ (F64.toRat x).2 = 2^j := by
  have ht := tb_lt x
  have he : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hx
  by_cases h0 : F64.toBits x / 2^52 % 2048 = 0
  · exact ⟨1074, by decide, by rw [toRat_subn x h0]⟩
  by_cases hsmall : F64.toBits x / 2^52 % 2048 ≤ 1074
  · exact ⟨1075 - F64.toBits x / 2^52 % 2048, by omega,
      by rw [toRat_norm x (by omega) hsmall]⟩
  · exact ⟨0, by decide, by rw [toRat_big x (by omega) (by omega)]⟩

theorem trunc_small_value (x : F64) (a i : Nat) (hx : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (ha : a < 2^53) :
    F64.isfinite (F64.trunc x) = true ∧
      (F64.toRat (F64.trunc x)).1 =
        (if F64.signbit x then -((a / 2^i : Nat) : Int) else ((a / 2^i : Nat) : Int)) *
          (F64.toRat (F64.trunc x)).2 := by
  have habs : (if F64.signbit x then -(a : Int) else (a : Int)).natAbs = a := by
    cases F64.signbit x
    · rfl
    · change (-(a : Int)).natAbs = a
      rw [Int.natAbs_neg]; rfl
  rw [trunc_formula, finite_not_nan x hx, finite_not_inf x hx]
  simp only [Bool.false_eq_true, ↓reduceIte, hr, Prod.fst, Prod.snd, habs]
  by_cases hq : a / 2^i = 0
  · simp only [hq, BEq.rfl, ↓reduceIte, Int.natCast_zero, Int.neg_zero, ite_self,
      Int.zero_mul, toRat_zero, Prod.fst]
    cases F64.signbit x <;> decide
  · rw [ite_f (by simpa only [beq_iff_eq] using hq)]
    have hqbound : a / 2^i ≤ 2^53 := by have := Nat.div_le_self a (2^i); omega
    exact ⟨(ofInt_small _ _ hqbound).1, (ofInt_small _ _ hqbound).2.2⟩


theorem isinteger_small (x : F64) (a i : Nat) (hx : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (ha : a < 2^53) (hi : i ≤ 1074) :
    F64.isinteger x = ((F64.toRat x).1 % ((F64.toRat x).2 : Int) == 0) := by
  obtain ⟨hfin, hval⟩ := trunc_small_value x a i hx hr ha
  obtain ⟨j, -, hden⟩ := finite_den_pow (F64.trunc x) hfin
  have hdecomp : (a : Int) - ((a / 2^i : Nat) : Int) * ((2^i : Nat) : Int) =
      ((a % 2^i : Nat) : Int) := by
    have h := Nat.mod_add_div a (2^i)
    rw [Int.mul_comm ((a / 2^i : Nat) : Int)]
    omega
  have hnum :
      (if F64.signbit x then -(a : Int) else (a : Int)) * ((2^j : Nat) : Int) -
        ((if F64.signbit x then -((a / 2^i : Nat) : Int) else ((a / 2^i : Nat) : Int)) *
          ((2^j : Nat) : Int)) * ((2^i : Nat) : Int) =
      (if F64.signbit x then -(((a % 2^i) * 2^j : Nat) : Int)
        else (((a % 2^i) * 2^j : Nat) : Int)) := by
    have heq : (a : Int) * ((2^j : Nat) : Int) -
        (((a / 2^i : Nat) : Int) * ((2^j : Nat) : Int)) * ((2^i : Nat) : Int) =
        ((a % 2^i : Nat) : Int) * ((2^j : Nat) : Int) := by
      rw [Int.mul_right_comm ((a / 2^i : Nat) : Int), ← Int.sub_mul, hdecomp]
    cases hs : F64.signbit x <;>
      simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul]
    · exact heq
    · omega
  unfold F64.isinteger
  rw [sub_finite x (F64.trunc x) hx hfin]
  simp only [hr, Prod.fst, Prod.snd, hval, hden]
  rw [hnum, ← Nat.pow_add]
  rw [dyadic_iszero _ i j _ _ (by have := Nat.mod_le a (2^i); omega) hi]
  exact (signed_mod_zero a (2^i) (F64.signbit x) (Nat.two_pow_pos _)).symm

theorem fields_bits (x : F64) :
    (if F64.signbit x then 2^63 else 0) +
      (F64.toBits x / 2^52 % 2048) * 2^52 + F64.toBits x % 2^52 = F64.toBits x := by
  have ht := tb_lt x
  cases hs : F64.signbit x
  · rw [signbit_f] at hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · rw [signbit_iff] at hs
    simp only [↓reduceIte]
    omega

theorem trunc_big (x : F64) (hx : F64.isfinite x = true)
    (he : 1075 ≤ F64.toBits x / 2^52 % 2048) : F64.trunc x = x := by
  have ht := tb_lt x
  have he2 : F64.toBits x / 2^52 % 2048 ≤ 2046 := by
    have : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hx
    omega
  have hM0 : 0 < F64.toBits x % 2^52 + 2^52 := by omega
  have hprod : 0 < (F64.toBits x % 2^52 + 2^52) *
      2^(F64.toBits x / 2^52 % 2048 - 1075) :=
    Nat.mul_pos hM0 (Nat.two_pow_pos _)
  have habs :
      ((if F64.signbit x then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
        else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int)) *
          ((2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int)).natAbs =
      (F64.toBits x % 2^52 + 2^52) * 2^(F64.toBits x / 2^52 % 2048 - 1075) := by
    cases hs : F64.signbit x <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.neg_mul]
    · rw [← Int.natCast_mul]; rfl
    · rw [Int.natAbs_neg, ← Int.natCast_mul]; rfl
  rw [trunc_formula, finite_not_nan x hx, finite_not_inf x hx]
  simp only [Bool.false_eq_true, ↓reduceIte, toRat_big x he he2, Prod.fst, Prod.snd,
    habs, Nat.div_one]
  rw [ite_f (by simp only [beq_iff_eq]; omega)]
  unfold F64.ofInt
  rw [show (1 : Nat) = 2^0 by rfl,
    roundRat_norm (F64.toBits x % 2^52 + 2^52)
      (F64.toBits x / 2^52 % 2048 - 1075) 0 (F64.signbit x) false
      (by omega) (by omega) (by omega) (by omega)]
  apply f64_ext
  rw [tb_ofBits]
  have hf := fields_bits x
  have heq : F64.toBits x / 2^52 % 2048 - 1075 + 1075 - 0 =
      F64.toBits x / 2^52 % 2048 := by omega
  rw [heq]
  omega

theorem sub_self_iszero (x : F64) (hx : F64.isfinite x = true) :
    F64.iszero (F64.sub x x) = true := by
  have hd := toRat_den_pos x hx
  have hprod : 0 < (F64.toRat x).2 * (F64.toRat x).2 := Nat.mul_pos hd hd
  rw [sub_finite x x hx hx]
  simp only [Int.sub_self, roundRat_eq,
    show (((F64.toRat x).2 * (F64.toRat x).2) == 0) = false by
      simp only [beq_eq_false_iff_ne]; omega,
    Bool.false_eq_true, BEq.rfl, ↓reduceIte]
  cases F64.signbit x <;> decide

theorem nan_sub_not_zero (x y : F64) (hx : F64.isnan x = true) :
    F64.iszero (F64.sub x y) = false := by
  rw [F64.sub, ite_t hx]
  change F64.iszero (if F64.fraction x < 2^51 then
    F64.ofBits (F64.toBits x + 2^51) else x) = false
  have ht := tb_lt x
  have hn := (isnan_iff x).mp hx
  split
  · rw [Bool.eq_false_iff, ne_eq, iszero_iff, tb_ofBits]
    simp only [F64.fraction] at *
    omega
  · rw [Bool.eq_false_iff, ne_eq, iszero_iff]
    omega


theorem isinteger_exact : IsintegerExact := by
  intro x
  cases hx : F64.isfinite x
  · simp only [hx, Bool.false_and]
    cases hn : F64.isnan x
    · have ht := tb_lt x
      have he : F64.toBits x / 2^52 % 2048 = 2047 := by
        simpa [F64.isfinite, F64.exponentField] using hx
      have hnf := (isnan_f x).mp hn
      have hinf : F64.isinf x = true := by rw [isinf_iff]; omega
      obtain ⟨s, rfl⟩ := inf_of_isinf x hinf
      cases s <;> decide
    · exact nan_sub_not_zero x (F64.trunc x) hn
  · simp only [hx, Bool.true_and]
    have ht := tb_lt x
    have he : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hx
    by_cases hE0 : F64.toBits x / 2^52 % 2048 = 0
    · exact isinteger_small x (F64.toBits x % 2^52) 1074 hx (toRat_subn x hE0)
        (by omega) (by decide)
    by_cases hE : F64.toBits x / 2^52 % 2048 ≤ 1074
    · exact isinteger_small x (F64.toBits x % 2^52 + 2^52)
        (1075 - F64.toBits x / 2^52 % 2048) hx (toRat_norm x (by omega) hE)
        (by omega) (by omega)
    · have hE1 : 1075 ≤ F64.toBits x / 2^52 % 2048 := by omega
      rw [F64.isinteger, trunc_big x hx hE1, sub_self_iszero x hx,
        toRat_big x hE1 (by omega)]
      simp
theorem integer_condition (t : IntTy) (x : F64) (his : IsintegerExact) :
    bitIntValid t x ∧ F64.isinteger x = true ↔
      F64.isfinite x = true ∧ (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0 ∧
      t.min ≤ (F64.toRat x).1 / ((F64.toRat x).2 : Int) ∧
      (F64.toRat x).1 / ((F64.toRat x).2 : Int) ≤ t.max := by
  constructor
  · rintro ⟨hv, hi⟩
    have hf := int_valid_finite t x hv
    have hm : (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0 := by
      simpa only [his x, hf, Bool.true_and, beq_iff_eq] using hi
    exact ⟨hf, hm, (finite_int_range t x hf hm).mp hv⟩
  · rintro ⟨hf, hm, hr⟩
    refine ⟨(finite_int_range t x hf hm).mpr hr, ?_⟩
    simp only [his x, hf, Bool.true_and, beq_iff_eq, hm]

theorem intConvert_of_isinteger (his : IsintegerExact) : IntConvertExact := by
  intro t x
  change (if (F64.le (F64.ofJInt (JInt.typemin t)) x &&
      F64.lt x (if !t.signed || t.bits < 64 then
        F64.add (F64.ofJInt (JInt.typemax t)) F64.one
        else F64.ofJInt (JInt.typemax t)) && F64.isinteger x) = true
    then Except.ok (JInt.wrap t ((F64.toRat x).1.tdiv (F64.toRat x).2))
    else Except.error (JlError.inexactError t.name)) = _
  have hchecks :
      (F64.le (F64.ofJInt (JInt.typemin t)) x &&
        F64.lt x (if !t.signed || t.bits < 64 then
          F64.add (F64.ofJInt (JInt.typemax t)) F64.one
          else F64.ofJInt (JInt.typemax t)) && F64.isinteger x) = true ↔
        bitIntValid t x ∧ F64.isinteger x = true := by
    rw [Bool.and_eq_true, int_checks]
  simp only [hchecks, integer_condition t x his]
  split
  · rename_i h
    rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_iff_emod_eq_zero.mpr h.2.1)]
  · rfl

end ProofTrunc

theorem truncIntExact_proven : TruncIntExact := by
  intro t x
  change (if (if !t.signed || t.bits < 64 then
      F64.lt (F64.sub (F64.ofJInt (JInt.typemin t)) F64.one) x &&
        F64.lt x (F64.add (F64.ofJInt (JInt.typemax t)) F64.one)
     else F64.le (F64.ofJInt (JInt.typemin t)) x &&
        F64.lt x (F64.ofJInt (JInt.typemax t))) = true
    then Except.ok (JInt.wrap t ((F64.toRat x).1.tdiv (F64.toRat x).2))
    else Except.error (JlError.inexactError "round")) = _
  simp only [ProofTrunc.trunc_checks, ProofTrunc.trunc_range]

theorem intConvertExact_proven : IntConvertExact :=
  ProofTrunc.intConvert_of_isinteger ProofTrunc.isinteger_exact

end JuliaLean.FloatFuncs
