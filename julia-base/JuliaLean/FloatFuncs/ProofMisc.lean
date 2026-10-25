import JuliaLean.FloatFuncs.Props
import JuliaLean.MathFuncs.ProofsBits

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 10000

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs
open JuliaLean.MathFuncs.ProofsBits

namespace ProofMisc

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

theorem abs_zero (s : Bool) : F64.abs (F64.zero s) = F64.zero false := by
  cases s <;> decide

theorem abs_inf (s : Bool) : F64.abs (F64.inf s) = F64.inf false := by
  cases s <;> decide

theorem abs_pack (s t : Bool) (q : Nat) (k : Int) :
    F64.abs (pk s q k) = F64.abs (pk t q k) := by
  have hb (b : Nat) : F64.abs (F64.ofBits ((if s then 2^63 else 0) + b)) =
      F64.abs (F64.ofBits ((if t then 2^63 else 0) + b)) := by
    apply f64_ext
    simp only [tb_abs, tb_ofBits]
    cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega
  unfold pk
  split
  · simp only [abs_zero]
  · dsimp only
    by_cases hc : q ≥ 2^53 <;> simp only [hc, ↓reduceIte]
    all_goals split <;> first | simp only [abs_inf] | exact hb _

theorem abs_roundRat_neg (n : Int) (d : Nat) (s t : Bool) :
    F64.abs (F64.roundRat n d s) = F64.abs (F64.roundRat (-n) d t) := by
  have hz : (-n == 0) = (n == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Int.neg_eq_zero]
  rw [roundRat_eq, roundRat_eq, hz]
  simp only [Int.natAbs_neg]
  by_cases hd : d = 0
  · simp only [hd, BEq.rfl, ↓reduceIte]
    by_cases hn : n = 0
    · simp only [hn, BEq.rfl, ↓reduceIte, Int.neg_zero]
    · simp only [show (n == 0) = false by simp [hn], Bool.false_eq_true, ↓reduceIte, abs_inf]
  · simp only [show (d == 0) = false by simp [hd], Bool.false_eq_true, ↓reduceIte]
    by_cases hn : n = 0
    · simp only [hn, BEq.rfl, ↓reduceIte, abs_zero]
    · simp only [show (n == 0) = false by simp [hn], Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [abs_inf]
      · split
        · simp only [abs_zero]
        · exact abs_pack _ _ _ _

theorem sub_finite (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.sub x y = F64.roundRat
      ((F64.toRat x).1 * (F64.toRat y).2 - (F64.toRat y).1 * (F64.toRat x).2)
      ((F64.toRat x).2 * (F64.toRat y).2) (F64.signbit x && !F64.signbit y) := by
  simp only [F64.sub, F64.add, finite_not_nan x hx, finite_not_nan y hy,
    neg_isnan, neg_isinf, finite_not_inf x hx, finite_not_inf y hy,
    Bool.false_eq_true, ↓reduceIte, toRat_neg, Prod.fst, Prod.snd,
    signbit_neg, Int.neg_mul, Int.sub_eq_add_neg]

theorem abs_sub_comm (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.abs (F64.sub x y) = F64.abs (F64.sub y x) := by
  rw [sub_finite x y hx hy, sub_finite y x hy hx, Nat.mul_comm (F64.toRat y).2]
  rw [show (F64.toRat y).1 * ((F64.toRat x).2 : Int) -
      (F64.toRat x).1 * ((F64.toRat y).2 : Int) =
      -((F64.toRat x).1 * ((F64.toRat y).2 : Int) -
        (F64.toRat y).1 * ((F64.toRat x).2 : Int)) by omega]
  exact abs_roundRat_neg _ _ _ _

theorem eq_comm (x y : F64) : F64.eq x y = F64.eq y x := by
  apply Bool.eq_iff_iff.mpr
  simp only [eq_iff]
  omega

theorem abs_not_nan (x : F64) (hx : F64.isfinite x = true) : F64.isnan (F64.abs x) = false := by
  have ht := tb_lt x
  have hn := (isnan_f x).mp (finite_not_nan x hx)
  rw [isnan_f]
  simp only [tb_abs]
  omega

theorem abs_signbit (x : F64) : F64.signbit (F64.abs x) = false := by
  rw [signbit_f, tb_abs]
  omega

theorem fmax_abs_comm (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    fmax (F64.abs x) (F64.abs y) = fmax (F64.abs y) (F64.abs x) := by
  have hnx := (isnan_f (F64.abs x)).mp (abs_not_nan x hx)
  have hny := (isnan_f (F64.abs y)).mp (abs_not_nan y hy)
  simp only [tb_abs] at hnx hny
  simp only [fmax, abs_not_nan x hx, abs_not_nan y hy, abs_signbit,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.or_false]
  split <;> rename_i h1 <;> split <;> rename_i h2 <;>
    first
    | rfl
    | (apply f64_ext
       simp only [lt_iff, tb_abs] at h1 h2 ⊢
       omega)

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

theorem signed_mod_zero (a d : Nat) (s : Bool) (hd : 0 < d) :
    ((if s then -(a : Int) else (a : Int)) % (d : Int) == 0) = (a % d == 0) := by
  have hr := Nat.mod_lt a hd
  have hsign : (d : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  apply Bool.eq_iff_iff.mpr
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, ← Int.natCast_emod,
      Int.natCast_eq_zero]
  · simp only [↓reduceIte, beq_iff_eq, Int.neg_emod, ← Int.natCast_emod, hsign]
    omega

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

end ProofMisc

open ProofMisc

theorem isapproxSymmetric_proven : IsapproxSymmetric := by
  intro x y atol rtol nans
  unfold isapproxF
  rw [eq_comm x y]
  cases hx : F64.isfinite x <;> cases hy : F64.isfinite y <;>
    simp only [hx, hy, Bool.false_and, Bool.true_and, Bool.and_false, Bool.or_false]
  all_goals try (cases nans <;> cases F64.isnan x <;> cases F64.isnan y <;> rfl)
  rw [abs_sub_comm x y hx hy, fmax_abs_comm x y hx hy]
  cases nans <;> cases F64.isnan x <;> cases F64.isnan y <;> rfl

theorem maxintfloatSpec_proven : MaxintfloatSpec := by
  refine ⟨by decide, ?_, ?_⟩
  · intro k hk
    refine ⟨F64.ofInt k, ?_, ?_⟩
    · exact (ofInt_small k false hk).1
    · exact (ofInt_small k false hk).2.2
  · intro y hy h
    have ht := tb_lt y
    have hf : F64.toBits y / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hy
    have hM : F64.toBits y % 2^52 < 2^52 := Nat.mod_lt _ (by decide)
    have hd := toRat_den_pos y hy
    by_cases hE0 : F64.toBits y / 2^52 % 2048 = 0
    · rw [toRat_subn y hE0] at h
      simp only [Prod.fst, Prod.snd] at h
      cases hs : F64.signbit y <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h <;> omega
    by_cases hE : F64.toBits y / 2^52 % 2048 ≤ 1074
    · rw [toRat_norm y (by omega) hE] at h hd
      simp only [Prod.fst, Prod.snd] at h hd
      have hdp : 1 ≤ ((2^(1075 - F64.toBits y / 2^52 % 2048) : Nat) : Int) := by omega
      cases hs : F64.signbit y <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.natCast_add] at h <;> omega
    · have hE1 : 1075 ≤ F64.toBits y / 2^52 % 2048 := by omega
      rw [toRat_big y hE1 (by omega)] at h
      simp only [Prod.fst, Prod.snd, Int.natCast_one, Int.mul_one] at h
      by_cases hEq : F64.toBits y / 2^52 % 2048 = 1075
      · rw [hEq] at h
        simp only [Nat.sub_self, Nat.pow_zero, Int.natCast_one, Int.mul_one] at h
        cases hs : F64.signbit y <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.natCast_add] at h <;> omega
      · have hp : F64.toBits y / 2^52 % 2048 - 1075 =
            (F64.toBits y / 2^52 % 2048 - 1076) + 1 := by omega
        have hpow : (2^(F64.toBits y / 2^52 % 2048 - 1075) : Nat) =
            2^(F64.toBits y / 2^52 % 2048 - 1076) * 2 := by
          rw [hp]
          exact Nat.pow_succ _ _
        rw [hpow, Int.natCast_mul] at h
        rw [← Int.mul_assoc] at h
        omega

theorem isintegerExact_proven : IsintegerExact := by
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

end JuliaLean.FloatFuncs
