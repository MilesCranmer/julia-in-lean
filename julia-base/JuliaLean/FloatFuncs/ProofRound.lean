import JuliaLean.FloatFuncs.Props
import JuliaLean.MathFuncs.ProofsBits
import JuliaLean.FloatFuncs.ProofMisc
import JuliaLean.Promotion.CompareProofs

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs
open JuliaLean.MathFuncs.ProofsBits

namespace ProofRound

theorem finite_not_nan {x : F64} (h : F64.isfinite x = true) :
    F64.isnan x = false := by
  simp_all [F64.isfinite, F64.isnan]

theorem finite_not_inf {x : F64} (h : F64.isfinite x = true) :
    F64.isinf x = false := by
  have ht := tb_lt x
  have he : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
    simpa [F64.isfinite, F64.exponentField] using h
  rw [Bool.eq_false_iff, ne_eq, isinf_iff]
  omega

theorem fields (x : F64) :
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

theorem roundRat_toRat (x : F64) (h : F64.isfinite x = true) :
    F64.roundRat (F64.toRat x).1 (F64.toRat x).2 (F64.signbit x) = x := by
  have ht := tb_lt x
  have he : F64.toBits x / 2^52 % 2048 ≤ 2046 := by
    have : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using h
    omega
  by_cases he0 : F64.toBits x / 2^52 % 2048 = 0
  · rw [toRat_subn x he0]
    simp only []
    by_cases hf0 : F64.toBits x % 2^52 = 0
    · have hx : x = F64.zero (F64.signbit x) := by
        apply f64_ext
        unfold F64.zero
        rw [tb_ofBits]
        have hf := fields x
        rw [he0, hf0] at hf
        cases hs : F64.signbit x <;> simp_all <;> omega
      rw [hf0]
      simp only [Int.natCast_zero, Int.neg_zero, ite_self]
      change F64.zero (F64.signbit x) = x
      exact hx.symm
    · have hr := roundRat_sub (F64.toBits x % 2^52) 0 1074
        (F64.signbit x) (F64.signbit x) (by omega) (by omega) (by decide)
      simp only [Nat.pow_zero, Nat.mul_one] at hr
      rw [hr]
      apply f64_ext
      rw [tb_ofBits]
      have hf := fields x
      rw [he0] at hf
      omega
  · by_cases he1 : F64.toBits x / 2^52 % 2048 ≤ 1074
    · rw [toRat_norm x (by omega) he1]
      simp only []
      have hr := roundRat_norm (F64.toBits x % 2^52 + 2^52) 0
        (1075 - F64.toBits x / 2^52 % 2048) (F64.signbit x) (F64.signbit x)
        (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.pow_zero, Nat.mul_one] at hr
      rw [hr]
      apply f64_ext
      rw [tb_ofBits]
      have hf := fields x
      have hx : 0 + 1075 - (1075 - F64.toBits x / 2^52 % 2048) =
          F64.toBits x / 2^52 % 2048 := by omega
      rw [hx]
      omega
    · rw [toRat_big x (by omega) he]
      simp only []
      have hn : (if F64.signbit x then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
          else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int)) *
            ((2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int) =
          if F64.signbit x then
            -(((F64.toBits x % 2^52 + 2^52) * 2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int)
          else (((F64.toBits x % 2^52 + 2^52) * 2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int) := by
        split <;> simp [Int.natCast_mul, Int.neg_mul]
      rw [hn]
      have hr := roundRat_norm (F64.toBits x % 2^52 + 2^52)
        (F64.toBits x / 2^52 % 2048 - 1075) 0 (F64.signbit x) (F64.signbit x)
        (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.pow_zero] at hr
      rw [hr]
      apply f64_ext
      rw [tb_ofBits]
      have hf := fields x
      have hx : F64.toBits x / 2^52 % 2048 - 1075 + 1075 - 0 =
          F64.toBits x / 2^52 % 2048 := by omega
      rw [hx]
      omega

def magnitude (a d : Nat) (s : Bool) (m : Mode) : Nat :=
  a / d + if (match m with
    | .Nearest => decide (2 * (a % d) > d) || (2 * (a % d) == d && a / d % 2 == 1)
    | .NearestTiesAway => decide (2 * (a % d) ≥ d)
    | .NearestTiesUp => if s then decide (2 * (a % d) > d) else decide (2 * (a % d) ≥ d)
    | .ToZero => false
    | .FromZero => a % d != 0
    | .Up => !s && a % d != 0
    | .Down => s && a % d != 0) then 1 else 0

theorem exactRound_signed (a d : Nat) (s : Bool) (m : Mode) (hd : 0 < d) :
    exactRound (if s then -(a : Int) else (a : Int)) d m =
      if s then -(magnitude a d s m : Int) else (magnitude a d s m : Int) := by
  have hr := Nat.mod_lt a hd
  have hsign : (d : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  have ha0 : a = 0 → a % d = 0 := by intro h; simp [h]
  cases s <;> cases m <;>
    simp only [exactRound, magnitude, Int.neg_ediv, Int.neg_emod,
      Int.dvd_iff_emod_eq_zero, ← Int.natCast_ediv, ← Int.natCast_emod,
      Int.natAbs_natCast, hsign, Bool.false_eq_true,
      Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      bne_iff_ne, Int.natCast_add, ↓reduceIte]
  all_goals repeat' (first | omega | split)

def intrinsic (x : F64) (m : Mode) : F64 :=
  let k := magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m
  if k == 0 then F64.zero (F64.signbit x)
  else F64.ofInt (if F64.signbit x then -(k : Int) else (k : Int))

theorem roundF_intrinsic (x : F64) (m : Mode)
    (hm : m ≠ .NearestTiesAway ∧ m ≠ .NearestTiesUp)
    (h : F64.isfinite x = true) : roundF x m = intrinsic x m := by
  have hn := finite_not_nan h
  have hi := finite_not_inf h
  cases m with
  | Nearest =>
    change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
    rw [hn, hi]
    rfl
  | NearestTiesAway => exact False.elim (hm.1 rfl)
  | NearestTiesUp => exact False.elim (hm.2 rfl)
  | ToZero =>
    change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
    rw [hn, hi]
    rfl
  | FromZero =>
    cases hs : F64.signbit x
    · simp only [roundF, hs, Bool.false_eq_true, ↓reduceIte]
      change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
      rw [hn, hi]
      simp [intrinsic, magnitude, hs]
    · simp only [roundF, hs, ↓reduceIte]
      change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
      rw [hn, hi]
      simp [intrinsic, magnitude, hs]
  | Up =>
    change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
    rw [hn, hi]
    rfl
  | Down =>
    change (if F64.isnan x then _ else if F64.isinf x then _ else _) = _
    rw [hn, hi]
    rfl

theorem toRat_signed (x : F64) (h : F64.isfinite x = true) :
    (F64.toRat x).1 =
      if F64.signbit x then -((F64.toRat x).1.natAbs : Int)
      else ((F64.toRat x).1.natAbs : Int) := by
  have he : F64.toBits x / 2^52 % 2048 ≤ 2046 := by
    have : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using h
    omega
  by_cases h0 : F64.toBits x / 2^52 % 2048 = 0
  · rw [toRat_subn x h0]
    cases hs : F64.signbit x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  · by_cases h1 : F64.toBits x / 2^52 % 2048 ≤ 1074
    · rw [toRat_norm x (by omega) h1]
      cases hs : F64.signbit x <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    · rw [toRat_big x (by omega) he]
      cases hs : F64.signbit x <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_mul,
          Int.natAbs_neg, Int.natAbs_natCast, Int.natCast_mul, Int.neg_mul]

theorem magnitude_one (a : Nat) (s : Bool) (m : Mode) :
    magnitude a 1 s m = a := by
  cases s <;> cases m <;> simp [magnitude, Nat.mod_one]

theorem intrinsic_den_one (x : F64) (m : Mode) (h : F64.isfinite x = true)
    (hd : (F64.toRat x).2 = 1) : intrinsic x m = x := by
  have hs := toRat_signed x h
  have hr := roundRat_toRat x h
  unfold intrinsic
  rw [hd, magnitude_one]
  dsimp only
  by_cases hz : (F64.toRat x).1.natAbs = 0
  · have hn : (F64.toRat x).1 = 0 := Int.natAbs_eq_zero.mp hz
    rw [hz]
    simp only [BEq.rfl, ↓reduceIte]
    rw [hn, hd] at hr
    exact hr
  · have hzb : ((F64.toRat x).1.natAbs == 0) = false := by
      simpa only [beq_eq_false_iff_ne] using hz
    rw [hzb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hs]
    unfold F64.ofInt
    rw [hd] at hr
    have hn : (F64.toRat x).1 ≠ 0 := by omega
    simpa only [roundRat_eq, beq_eq_false_iff_ne.mpr hn, Bool.false_eq_true,
      ↓reduceIte] using hr

theorem magnitude_le (a d : Nat) (s : Bool) (m : Mode) :
    magnitude a d s m ≤ a / d + 1 := by
  unfold magnitude
  have bit_le (b : Bool) : (if b then 1 else 0 : Nat) ≤ 1 := by cases b <;> decide
  exact Nat.add_le_add_left (bit_le _) _

theorem numerator_lt (x : F64) (h : F64.isfinite x = true)
    (hd : (F64.toRat x).2 ≠ 1) : (F64.toRat x).1.natAbs < 2^53 := by
  have he : F64.toBits x / 2^52 % 2048 ≤ 2046 := by
    have : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using h
    omega
  by_cases h0 : F64.toBits x / 2^52 % 2048 = 0
  · rw [toRat_subn x h0]
    cases hs : F64.signbit x <;> simp <;> omega
  · by_cases h1 : F64.toBits x / 2^52 % 2048 ≤ 1074
    · rw [toRat_norm x (by omega) h1]
      cases hs : F64.signbit x <;> simp <;> omega
    · rw [toRat_big x (by omega) he] at hd
      exact False.elim (hd rfl)

theorem finite_zero (s : Bool) : F64.isfinite (F64.zero s) = true := by
  cases s <;> decide

theorem signbit_zero (s : Bool) : F64.signbit (F64.zero s) = s := by
  cases s <;> decide

theorem small_integer_exact (n : Int) (hn : n.natAbs ≤ 2^53) (h0 : n ≠ 0) :
    F64.isfinite (F64.ofInt n) = true ∧
      F64.signbit (F64.ofInt n) = decide (n < 0) ∧
      (F64.toRat (F64.ofInt n)).1 = n * ((F64.toRat (F64.ofInt n)).2 : Int) := by
  have hs : (if decide (n < 0) then -(n.natAbs : Int) else (n.natAbs : Int)) = n := by
    split <;> simp_all <;> omega
  have ha : (n.natAbs != 0) = true := by
    simp only [bne_iff_ne]
    omega
  have hh := ProofMisc.ofInt_small n.natAbs (decide (n < 0)) hn
  dsimp only at hh
  rw [hs] at hh
  exact ⟨hh.1, by simpa only [ha, Bool.and_true] using hh.2.1, hh.2.2⟩

theorem intrinsic_exact
    (x : F64) (m : Mode) (h : F64.isfinite x = true) :
    F64.isfinite (intrinsic x m) = true ∧
      F64.signbit (intrinsic x m) = F64.signbit x ∧
      (F64.toRat (intrinsic x m)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 m *
          ((F64.toRat (intrinsic x m)).2 : Int) := by
  by_cases hd : (F64.toRat x).2 = 1
  · rw [intrinsic_den_one x m h hd]
    exact ⟨h, rfl, by simp [hd, exactRound]⟩
  · have hn := numerator_lt x h hd
    have hp := toRat_den_pos x h
    have hm := magnitude_le (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m
    have hdiv := Nat.div_le_self (F64.toRat x).1.natAbs (F64.toRat x).2
    have hk : magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m ≤ 2^53 := by
      omega
    have hv : exactRound (F64.toRat x).1 (F64.toRat x).2 m =
        if F64.signbit x then
          -(magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int)
        else (magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int) := by
      calc
        _ = exactRound
            (if F64.signbit x then -((F64.toRat x).1.natAbs : Int)
              else ((F64.toRat x).1.natAbs : Int)) (F64.toRat x).2 m :=
          congrArg (fun n => exactRound n (F64.toRat x).2 m) (toRat_signed x h)
        _ = _ := exactRound_signed _ _ _ _ hp
    unfold intrinsic
    dsimp only
    by_cases hz : magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m = 0
    · rw [hz]
      simp only [BEq.rfl, ↓reduceIte]
      rw [hz] at hv
      simp only [Int.natCast_zero, Int.neg_zero, ite_self] at hv
      exact ⟨finite_zero _, signbit_zero _, by simp [toRat_zero, hv]⟩
    · have hzb : (magnitude (F64.toRat x).1.natAbs (F64.toRat x).2
          (F64.signbit x) m == 0) = false := by
        simpa only [beq_eq_false_iff_ne] using hz
      rw [hzb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have habs : (if F64.signbit x then
          -(magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int)
        else (magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int)).natAbs ≤ 2^53 := by
        cases hs : F64.signbit x <;> simpa [hs] using hk
      have hne : (if F64.signbit x then
          -(magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int)
        else (magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) m : Int)) ≠ 0 := by
        cases hs : F64.signbit x <;> simp_all
      obtain ⟨hfin, hsign, hrat⟩ := small_integer_exact _ habs hne
      refine ⟨hfin, ?_, ?_⟩
      · rw [hsign]
        cases hs : F64.signbit x <;> simp_all <;> omega
      · rw [hv]
        exact hrat

theorem exactRound_toZero (n : Int) (d : Nat) (hd : 0 < d) :
    exactRound n d .ToZero = n.tdiv (d : Int) := by
  have hs : (d : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  simp only [exactRound, Int.tdiv_eq_ediv, Int.dvd_iff_emod_eq_zero, hs]
  split <;> simp_all <;> omega

theorem roundF_exact (x : F64) (m : Mode)
    (hm : m ≠ .NearestTiesAway ∧ m ≠ .NearestTiesUp) (h : F64.isfinite x = true) :
    F64.isfinite (roundF x m) = true ∧
      F64.signbit (roundF x m) = F64.signbit x ∧
      (F64.toRat (roundF x m)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 m *
          ((F64.toRat (roundF x m)).2 : Int) := by
  rw [roundF_intrinsic x m hm h]
  exact intrinsic_exact x m h

theorem trunc_exact (x : F64) (h : F64.isfinite x = true) :
    F64.isfinite (F64.trunc x) = true ∧
      F64.signbit (F64.trunc x) = F64.signbit x ∧
      (F64.toRat (F64.trunc x)).1 =
        (F64.toRat x).1.tdiv ((F64.toRat x).2 : Int) *
          ((F64.toRat (F64.trunc x)).2 : Int) := by
  simpa only [roundF, F64.trunc, exactRound_toZero _ _ (toRat_den_pos x h)]
    using roundF_exact x .ToZero (by decide) h

theorem roundF_den_one (x : F64) (m : Mode)
    (hm : m ≠ .NearestTiesAway ∧ m ≠ .NearestTiesUp)
    (h : F64.isfinite x = true) (hd : (F64.toRat x).2 = 1) :
    roundF x m = x := by
  rw [roundF_intrinsic x m hm h]
  exact intrinsic_den_one x m h hd

theorem eq_self_finite (x : F64) (h : F64.isfinite x = true) :
    F64.eq x x = true := by
  simp [F64.eq, finite_not_nan h]

theorem tiesAway_den_one (x : F64) (h : F64.isfinite x = true)
    (hd : (F64.toRat x).2 = 1) : roundF x .NearestTiesAway = x := by
  have ht := roundF_den_one x .ToZero (by decide) h hd
  change (let y := roundF x .ToZero; if F64.eq x y then y else _) = x
  rw [ht]
  simp only [eq_self_finite x h, ↓reduceIte]

theorem natAbs_mod_zero (n : Int) (d : Nat) (h : n % (d : Int) = 0) :
    n.natAbs % d = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  have hdvd : (d : Int) ∣ n := Int.dvd_iff_emod_eq_zero.mpr h
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdvd

theorem trunc_zero (s : Bool) : F64.trunc (F64.zero s) = F64.zero s := by
  cases s <;> decide

theorem trunc_integral (x : F64) (h : F64.isfinite x = true)
    (hint : (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0) :
    F64.trunc x = x := by
  have hrem := natAbs_mod_zero _ _ hint
  by_cases hbig : 1075 ≤ F64.toBits x / 2^52 % 2048
  · exact ProofMisc.trunc_big x h hbig
  by_cases hsub : F64.toBits x / 2^52 % 2048 = 0
  · have hr := toRat_subn x hsub
    have habs : (F64.toRat x).1.natAbs = F64.toBits x % 2^52 := by
      rw [hr]
      cases hs : F64.signbit x <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    rw [habs, show (F64.toRat x).2 = 2^1074 by rw [hr]] at hrem
    have hlt : F64.toBits x % 2^52 < 2^1074 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hrem
    have hx : x = F64.zero (F64.signbit x) := by
      apply f64_ext
      unfold F64.zero
      rw [tb_ofBits]
      have hf := fields x
      rw [hsub, hrem] at hf
      cases hs : F64.signbit x <;> simp_all <;> omega
    calc
      F64.trunc x = F64.trunc (F64.zero (F64.signbit x)) := congrArg F64.trunc hx
      _ = F64.zero (F64.signbit x) := trunc_zero _
      _ = x := hx.symm
  · let M := F64.toBits x % 2^52 + 2^52
    let i := 1075 - F64.toBits x / 2^52 % 2048
    let q := M / 2^i
    have hM1 : 2^52 ≤ M := by dsimp only [M]; omega
    have hM2 : M < 2^53 := by dsimp only [M]; omega
    have hi : 1 ≤ i := by dsimp only [i]; omega
    have hr := toRat_norm x (by omega) (by omega)
    have habs : (F64.toRat x).1.natAbs = M := by
      rw [hr]
      cases hs : F64.signbit x <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast, M]
    have hden : (F64.toRat x).2 = 2^i := by rw [hr]
    rw [habs, hden] at hrem
    have hmul : q * 2^i = M := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hrem)
    have hq0 : 0 < q := by
      by_cases hq : q = 0
      · rw [hq, Nat.zero_mul] at hmul
        omega
      · exact Nat.pos_iff_ne_zero.mpr hq
    have hd2 : 2 ≤ 2^i := by
      have hip : i = (i - 1) + 1 := by omega
      rw [hip, Nat.pow_succ]
      have hp := Nat.two_pow_pos (i - 1)
      omega
    have hq2 : q < 2^52 := by
      have hqm := Nat.mul_le_mul_left q hd2
      rw [hmul] at hqm
      omega
    have hlogM : M.log2 = 52 := by
      have ha := (Nat.log2_lt (by omega : M ≠ 0)).mpr hM2
      have hb : ¬ M.log2 < 52 := fun hl =>
        absurd hM1 (Nat.not_le.mpr ((Nat.log2_lt (by omega : M ≠ 0)).mp hl))
      omega
    have hlog := log2_mul_pow i hq0
    rw [hmul, hlogM] at hlog
    have hE : q.log2 + 1023 = F64.toBits x / 2^52 % 2048 := by
      dsimp only [i] at hlog
      omega
    have hscale : q * 2^(52 - q.log2) = M := by
      rw [show 52 - q.log2 = i by omega]
      exact hmul
    rw [ProofMisc.trunc_formula, finite_not_nan h, finite_not_inf h]
    simp only [Bool.false_eq_true, ↓reduceIte, habs, hden]
    change (if q == 0 then _ else _) = x
    rw [ite_f (by simp only [beq_iff_eq]; omega)]
    rw [ProofMisc.small_ofInt_bits q (F64.signbit x) hq0 hq2, hE, hscale]
    apply f64_ext
    rw [tb_ofBits]
    rw [show M - 2^52 = F64.toBits x % 2^52 by dsimp only [M]; omega,
      fields x, Nat.mod_eq_of_lt (tb_lt x)]

theorem tiesAway_integral (x : F64) (h : F64.isfinite x = true)
    (hint : (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0) :
    roundF x .NearestTiesAway = x := by
  change (let y := F64.trunc x; if F64.eq x y then y else _) = x
  rw [trunc_integral x h hint]
  simp only [eq_self_finite x h, ↓reduceIte]

theorem signed_natAbs (a : Nat) (s : Bool) :
    (if s then -(a : Int) else (a : Int)).natAbs = a := by
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]

theorem signed_negative (a : Nat) (s : Bool) (ha : 0 < a) :
    decide ((if s then -(a : Int) else (a : Int)) < 0) = s := by
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
    decide_eq_false_iff_not, decide_eq_true_eq] <;> omega

theorem dyadic_normal_bits (a i j : Nat) (s zs : Bool)
    (h0 : 0 < a) (ha : a < 2^53) (hi : i ≤ a.log2 + 1022) :
    F64.roundRat (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int))
      (2^(i+j)) zs =
      F64.ofBits ((if s then 2^63 else 0) +
        (a.log2 + 1023 - i) * 2^52 + (a * 2^(52-a.log2) - 2^52)) := by
  let n : Int := if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)
  have hprod := Nat.mul_pos h0 (Nat.two_pow_pos j)
  have habs : n.natAbs = a * 2^j := signed_natAbs _ _
  have hn : n ≠ 0 := by intro hz; rw [hz] at habs; simp only [Int.natAbs_zero] at habs; omega
  have hs : decide (n < 0) = s := signed_negative _ _ hprod
  have hL : a.log2 ≤ 52 := by have := (Nat.log2_lt (by omega : a ≠ 0)).mpr ha; omega
  have he : -1075 ≤ Promotion.Fl.floorLog2Rat n.natAbs (2^(i+j)) := by
    change -1075 ≤ fl2 n.natAbs (2^(i+j))
    rw [habs, fl2_pow a j (i+j) h0]
    omega
  rw [Promotion.f64_roundRat_bridge n _ zs (Nat.ne_of_gt (Nat.two_pow_pos _)) hn he]
  have hr := Promotion.Fl.roundRat_normal (f := Promotion.double) Promotion.good_double
    n a j (i+j) zs habs (by omega) (by exact ha)
    (by change i + j + 1 ≤ a.log2 + j + 1023; omega)
    (by change a.log2 + j + 1023 < i + j + 2047; omega)
  rw [hr]
  rw [Promotion.Fl.pack, Promotion.Fl.toBits_ofBits, Promotion.f64_ofBits_mod, hs]
  change F64.ofBits ((if s then 2^63 else 0) +
    ((a.log2 + j + 1023 - (i+j)) * 2^52 + (a * 2^(52-a.log2) - 2^52))) = _
  rw [show a.log2 + j + 1023 - (i+j) = a.log2 + 1023 - i by omega]
  simp only [Nat.add_assoc]

theorem dyadic_sub_bits (a i j : Nat) (s zs : Bool)
    (h0 : 0 < a) (ha : a < 2^53) (hi : i ≤ 1074) (he : a.log2 + 1022 < i) :
    F64.roundRat (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int))
      (2^(i+j)) zs =
      F64.ofBits ((if s then 2^63 else 0) + a * 2^(1074-i)) := by
  have hp := Nat.mul_pos h0 (Nat.two_pow_pos j)
  have habs := signed_natAbs (a * 2^j) s
  have hs := signed_negative (a * 2^j) s hp
  have hn : ¬((if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int)) == 0) = true := by
    simp only [beq_iff_eq]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hd : ¬(2^(i+j) == 0) = true := by
    simp only [beq_iff_eq]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  have hL : a.log2 ≤ 52 := by have := (Nat.log2_lt (by omega : a ≠ 0)).mpr ha; omega
  rw [roundRat_eq, ite_f hd, ite_f hn, habs, hs, fl2_pow a j (i+j) h0,
    ite_f (by omega), ite_f (by omega)]
  have hK : max (((a.log2 + j : Nat) : Int) - (i+j : Nat) - 52) (-1074) = -1074 := by omega
  rw [hK, ite_f (by decide : ¬((-1074 : Int) ≥ 0))]
  change pk s (rq (a * 2^j * 2^1074) (2^(i+j))) (-1074) = _
  have hnum : a * 2^j * 2^1074 = (a * 2^(1074-i)) * 2^(i+j) := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    congr 2
    omega
  have hQ0 := Nat.mul_pos h0 (Nat.two_pow_pos (1074-i))
  have hQ : a * 2^(1074-i) < 2^52 := by
    calc
      a * 2^(1074-i) < 2^(a.log2+1) * 2^(1074-i) :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
      _ = 2^(a.log2+1+(1074-i)) := (Nat.pow_add _ _ _).symm
      _ ≤ 2^52 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hnum, rq_exact _ _ (Nat.two_pow_pos _) (Nat.mul_mod_left _ _),
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), pk_sub s _ hQ0 hQ]

theorem dyadic_value (a i j : Nat) (s zs : Bool)
    (h0 : 0 < a) (ha : a < 2^53) (hi : i ≤ 1074) :
    let y := F64.roundRat
      (if s then -((a * 2^j : Nat) : Int) else ((a * 2^j : Nat) : Int))
      (2^(i+j)) zs
    ∃ k : Nat, i ≤ k ∧ k ≤ 1074 ∧ F64.isfinite y = true ∧ F64.signbit y = s ∧
      F64.toRat y =
        (if s then -((a * 2^(k-i) : Nat) : Int) else ((a * 2^(k-i) : Nat) : Int), 2^k) := by
  dsimp only
  obtain ⟨hL, hM1, hM2⟩ :=
    Promotion.Fl.sig_bounds (f := Promotion.double) a (by omega) ha
  change a.log2 ≤ 52 at hL
  change 2^52 ≤ a * 2^(52-a.log2) at hM1
  change a * 2^(52-a.log2) < 2^53 at hM2
  by_cases hn : i ≤ a.log2 + 1022
  · rw [dyadic_normal_bits a i j s zs h0 ha hn]
    let E := a.log2 + 1023 - i
    let M := a * 2^(52-a.log2)
    let k := i + 52 - a.log2
    have hE1 : 1 ≤ E := by dsimp only [E]; omega
    have hE2 : E ≤ 1075 := by dsimp only [E]; omega
    have hEk : E + k = 1075 := by dsimp only [E, k]; omega
    have hk1 : i ≤ k := by dsimp only [k]; omega
    have hk2 : k ≤ 1074 := by dsimp only [k]; omega
    have hM : M - 2^52 + 2^52 = a * 2^(k-i) := by
      rw [Nat.sub_add_cancel hM1]
      congr 2
      dsimp only [k]
      omega
    obtain ⟨hE, hF, hS, hfin⟩ := ProofMisc.norm_fields s E M hE1 (by omega) hM1 hM2
    refine ⟨k, hk1, hk2, hfin, hS, ?_⟩
    by_cases hk0 : k = 0
    · have he : E = 1075 := by omega
      rw [toRat_big _ (by rw [hE]; omega) (by rw [hE]; omega)]
      rw [hS, hE, hF, hM, he]
      simp only [Nat.sub_self, Nat.pow_zero, Int.natCast_one, Int.mul_one, hk0]
    · rw [toRat_norm _ (by rw [hE]; omega) (by rw [hE]; omega)]
      rw [hS, hE, hF, hM, show 1075 - E = k by omega]
  · rw [dyadic_sub_bits a i j s zs h0 ha hi (by omega)]
    let Q := a * 2^(1074-i)
    have hQ0 : 0 < Q := Nat.mul_pos h0 (Nat.two_pow_pos _)
    have hQ : Q < 2^52 := by
      calc
        Q < 2^(a.log2+1) * 2^(1074-i) :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
        _ = 2^(a.log2+1+(1074-i)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2^52 := Nat.pow_le_pow_right (by decide) (by omega)
    have hE : F64.toBits (F64.ofBits ((if s then 2^63 else 0) + Q)) / 2^52 % 2048 = 0 := by
      rw [tb_ofBits]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hF : F64.toBits (F64.ofBits ((if s then 2^63 else 0) + Q)) % 2^52 = Q := by
      rw [tb_ofBits]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hS : F64.signbit (F64.ofBits ((if s then 2^63 else 0) + Q)) = s := by
      simp only [F64.signbit, tb_ofBits]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
        decide_eq_false_iff_not] <;> omega
    have hfin : F64.isfinite (F64.ofBits ((if s then 2^63 else 0) + Q)) = true := by
      simp only [F64.isfinite, F64.exponentField, hE]
      decide
    refine ⟨1074, hi, Nat.le_refl _, hfin, hS, ?_⟩
    rw [toRat_subn _ hE, hF, hS]

theorem scaled_quotient (a i k : Nat) (hik : i ≤ k) :
    a * 2^(k-i) / 2^k = a / 2^i := by
  have hp : 2^k = 2^i * 2^(k-i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hp]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)

theorem away_quotient (a i : Nat) (s : Bool) (hi : 0 < i) :
    (a - a / 2^i * 2^(i-1)) / 2^(i-1) = magnitude a (2^i) s .NearestTiesAway := by
  let H := 2^(i-1)
  let q := a / 2^i
  let r := a % 2^i
  have hp : 2^i = 2 * H := by
    dsimp only [H]
    calc
      2^i = 2^((i-1)+1) := congrArg (fun n : Nat => 2^n) (by omega)
      _ = 2 * 2^(i-1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hHp : 0 < H := Nat.two_pow_pos _
  have hr : r < 2 * H := by
    have ht := Nat.mod_lt a (Nat.two_pow_pos i)
    change r < 2^i at ht
    rwa [hp] at ht
  have hmul : 2^i * q = 2 * (q * H) := by
    rw [hp, Nat.mul_assoc, Nat.mul_comm H q]
  have hsum : a = 2 * (q * H) + r := by
    have ht := Nat.div_add_mod a (2^i)
    change 2^i * q + r = a at ht
    rw [hmul] at ht
    exact ht.symm
  change (a - q * H) / H = q + if decide (2*r ≥ 2^i) then 1 else 0
  by_cases hc : r < H
  · have hinc : decide (2*r ≥ 2^i) = false := by
      simp only [decide_eq_false_iff_not]
      rw [hp]
      omega
    rw [hinc]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  · have hinc : decide (2*r ≥ 2^i) = true := by
      simp only [decide_eq_true_eq]
      rw [hp]
      omega
    rw [hinc]
    simp only [↓reduceIte]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      omega

theorem double_small_value (x : F64) (a i : Nat) (h : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (h0 : 0 < a) (ha : a < 2^53) (hi0 : 0 < i) (hi : i ≤ 1074) :
    ∃ k : Nat, i-1 ≤ k ∧ k ≤ 1074 ∧
      F64.isfinite (F64.mul (F64.ofInt 2) x) = true ∧
      F64.signbit (F64.mul (F64.ofInt 2) x) = F64.signbit x ∧
      F64.toRat (F64.mul (F64.ofInt 2) x) =
        (if F64.signbit x then -((a * 2^(k-(i-1)) : Nat) : Int)
          else ((a * 2^(k-(i-1)) : Nat) : Int), 2^k) := by
  have htwo : F64.toRat (F64.ofInt 2) = ((2^52 : Int), 2^51) := by decide
  have hnum : (2^52 : Int) * (if F64.signbit x then -(a : Int) else (a : Int)) =
      if F64.signbit x then -((a * 2^52 : Nat) : Int) else ((a * 2^52 : Nat) : Int) := by
    cases hs : F64.signbit x <;> simp [Int.natCast_mul, Int.mul_comm, Int.neg_mul]
  have hden : 2^51 * 2^i = 2^((i-1)+52) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [mul_fin _ _ (by decide) (finite_not_nan h) (by decide) (finite_not_inf h),
    htwo, hr]
  rw [hnum, hden]
  exact dyadic_value a (i-1) 52 _ _ h0 ha (by omega)

theorem dyadic_sub_value (x y : F64) (a q i u v : Nat) (s : Bool)
    (hx : F64.isfinite x = true) (hy : F64.isfinite y = true)
    (hrx : F64.toRat x =
      (if s then -((a * 2^(u-i) : Nat) : Int) else ((a * 2^(u-i) : Nat) : Int), 2^u))
    (hry : F64.toRat y =
      (if s then -((q * 2^v : Nat) : Int) else ((q * 2^v : Nat) : Int), 2^v))
    (hu : i ≤ u) (hi : i ≤ 1074) (ha : a < 2^53) (hq : q * 2^i < a) :
    ∃ k : Nat, i ≤ k ∧ k ≤ 1074 ∧ F64.isfinite (F64.sub x y) = true ∧
      F64.signbit (F64.sub x y) = s ∧ F64.toRat (F64.sub x y) =
        (if s then -(((a - q * 2^i) * 2^(k-i) : Nat) : Int)
          else (((a - q * 2^i) * 2^(k-i) : Nat) : Int), 2^k) := by
  let j := u + v - i
  have hji : i+j = u+v := by dsimp only [j]; omega
  have h1 : a * 2^(u-i) * 2^v = a * 2^j := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    dsimp only [j]
    omega
  have h2 : q * 2^v * 2^u = (q * 2^i) * 2^j := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    congr 2
    omega
  have hdiff : (((a - q * 2^i) * 2^j : Nat) : Int) =
      ((a * 2^j : Nat) : Int) - (((q * 2^i) * 2^j : Nat) : Int) := by
    rw [Nat.sub_mul, Int.natCast_sub (Nat.mul_le_mul_right _ (Nat.le_of_lt hq))]
  have hnum :
      (if s then -((a * 2^(u-i) : Nat) : Int) else ((a * 2^(u-i) : Nat) : Int)) * (2^v : Nat) -
        (if s then -((q * 2^v : Nat) : Int) else ((q * 2^v : Nat) : Int)) * (2^u : Nat) =
      if s then -(((a - q * 2^i) * 2^j : Nat) : Int)
        else (((a - q * 2^i) * 2^j : Nat) : Int) := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul,
      ← Int.natCast_mul, h1, h2, hdiff] <;> omega
  rw [ProofMisc.sub_finite x y hx hy, hrx, hry]
  rw [hnum, ← Nat.pow_add, ← hji]
  exact dyadic_value (a - q * 2^i) i j s _ (by omega) (by omega) hi

theorem signed_tdiv (a d : Nat) (s : Bool) :
    (if s then -(a : Int) else (a : Int)).tdiv (d : Int) =
      if s then -((a / d : Nat) : Int) else ((a / d : Nat) : Int) := by
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_tdiv,
    Int.natCast_tdiv_eq_ediv, ← Int.natCast_ediv]

theorem eq_of_eq_sign (x y : F64) (heq : F64.eq x y = true)
    (hs : F64.signbit x = F64.signbit y) : x = y := by
  have hx := tb_lt x
  have hy := tb_lt y
  rw [eq_iff] at heq
  apply f64_ext
  rcases heq.2.2 with hb | ⟨hx0, hy0⟩
  · exact hb
  · cases hxs : F64.signbit x
    · have hys : F64.signbit y = false := hs.symm.trans hxs
      rw [signbit_f] at hxs hys
      omega
    · have hys : F64.signbit y = true := hs.symm.trans hxs
      rw [signbit_iff] at hxs hys
      omega

theorem integral_of_trunc_eq (x : F64) (h : F64.isfinite x = true)
    (heq : F64.eq x (F64.trunc x) = true) :
    (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0 := by
  have ht := trunc_exact x h
  have he := eq_of_eq_sign x (F64.trunc x) heq ht.2.1.symm
  have hrat := ht.2.2
  rw [← he] at hrat
  apply Int.dvd_iff_emod_eq_zero.mp
  exact ⟨_, hrat.trans (Int.mul_comm _ _)⟩

theorem tiesAway_exact (x : F64) (h : F64.isfinite x = true) :
    F64.isfinite (roundF x .NearestTiesAway) = true ∧
      F64.signbit (roundF x .NearestTiesAway) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesAway)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesAway *
          ((F64.toRat (roundF x .NearestTiesAway)).2 : Int) := by
  by_cases hint : (F64.toRat x).1 % ((F64.toRat x).2 : Int) = 0
  · rw [tiesAway_integral x h hint]
    refine ⟨h, rfl, ?_⟩
    simp only [exactRound, hint, ↓reduceIte]
    exact (Int.ediv_mul_cancel_of_emod_eq_zero hint).symm
  · have hxy : ¬ F64.eq x (F64.trunc x) = true := fun he =>
      hint (integral_of_trunc_eq x h he)
    have hd1 : (F64.toRat x).2 ≠ 1 := by
      intro hd
      apply hint
      rw [hd]
      exact Int.emod_one _
    let a := (F64.toRat x).1.natAbs
    have ha : a < 2^53 := numerator_lt x h hd1
    have ha0 : 0 < a := by
      apply Nat.pos_iff_ne_zero.mpr
      intro hz
      have hn : (F64.toRat x).1 = 0 := Int.natAbs_eq_zero.mp hz
      apply hint
      rw [hn, Int.zero_emod]
    obtain ⟨i, hi, hden⟩ := ProofMisc.finite_den_pow x h
    have hi0 : 0 < i := by
      by_cases hz : i = 0
      · rw [hz, Nat.pow_zero] at hden
        exact False.elim (hd1 hden)
      · exact Nat.pos_iff_ne_zero.mpr hz
    have hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i) :=
      Prod.ext (toRat_signed x h) hden
    let q := a / 2^i
    have hp : 2^i = 2 * 2^(i-1) := by
      calc
        2^i = 2^((i-1)+1) := congrArg (fun n : Nat => 2^n) (by omega)
        _ = 2 * 2^(i-1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hqmul : q * 2^i = 2 * (q * 2^(i-1)) := by
      rw [hp, ← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]
    have hq : q * 2^(i-1) < a := by
      have hdiv := Nat.div_mul_le_self a (2^i)
      change q * 2^i ≤ a at hdiv
      rw [hqmul] at hdiv
      omega
    obtain ⟨u, hu, hu1, h2fin, h2s, h2r⟩ :=
      double_small_value x a i h hr ha0 ha hi0 hi
    have hyt := trunc_exact x h
    obtain ⟨v, hv, hvden⟩ := ProofMisc.finite_den_pow (F64.trunc x) hyt.1
    have hyr : F64.toRat (F64.trunc x) =
        (if F64.signbit x then -((q * 2^v : Nat) : Int)
          else ((q * 2^v : Nat) : Int), 2^v) := by
      apply Prod.ext
      · have hh := (ProofMisc.trunc_small_value x a i h hr ha).2
        rw [hvden] at hh
        rw [hh]
        cases hs : F64.signbit x <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul, q]
      · exact hvden
    obtain ⟨k, hk, hk1, hzfin, hzs, hzr⟩ :=
      dyadic_sub_value (F64.mul (F64.ofInt 2) x) (F64.trunc x) a q (i-1) u v
        (F64.signbit x) h2fin hyt.1 h2r hyr hu (by omega) ha hq
    let z := F64.sub (F64.mul (F64.ofInt 2) x) (F64.trunc x)
    have hz := trunc_exact z hzfin
    have hv : (F64.toRat z).1.tdiv ((F64.toRat z).2 : Int) =
        if F64.signbit x then -(magnitude a (2^i) (F64.signbit x) .NearestTiesAway : Int)
        else (magnitude a (2^i) (F64.signbit x) .NearestTiesAway : Int) := by
      rw [hzr]
      rw [signed_tdiv, scaled_quotient _ (i-1) k hk,
        away_quotient a i (F64.signbit x) hi0]
    have hex : exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesAway =
        if F64.signbit x then -(magnitude a (2^i) (F64.signbit x) .NearestTiesAway : Int)
        else (magnitude a (2^i) (F64.signbit x) .NearestTiesAway : Int) := by
      rw [hr]
      exact exactRound_signed a (2^i) _ _ (Nat.two_pow_pos _)
    have hform : roundF x .NearestTiesAway = F64.trunc z := by
      change (if F64.eq x (F64.trunc x) then _ else _) = _
      rw [ite_f hxy]
      rfl
    rw [hform]
    refine ⟨hz.1, hz.2.1.trans hzs, ?_⟩
    calc
      _ = (F64.toRat z).1.tdiv ((F64.toRat z).2 : Int) *
          ((F64.toRat (F64.trunc z)).2 : Int) := hz.2.2
      _ = _ := by rw [hv, hex]

theorem roundF_exact_except_tiesUp (x : F64) (m : Mode)
    (hm : m ≠ .NearestTiesUp) (h : F64.isfinite x = true) :
    F64.isfinite (roundF x m) = true ∧
      F64.signbit (roundF x m) = F64.signbit x ∧
      (F64.toRat (roundF x m)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 m *
          ((F64.toRat (roundF x m)).2 : Int) := by
  by_cases ha : m = .NearestTiesAway
  · subst m
    exact tiesAway_exact x h
  · exact roundF_exact x m ⟨ha, hm⟩ h

theorem tiesUp_boundary_value :
    F64.toRat (F64.ofBits 0xc330000000000000) = (-(2^52 : Int), 1) := by decide

theorem tiesUp_boundary_add :
    F64.add
      (F64.add (F64.ofBits 0xc330000000000000)
        (F64.sub (F64.ofBits 0x3fd0000000000000) (F64.eps (F64.ofBits 0x3fe0000000000000))))
      (F64.add (F64.ofBits 0x3fd0000000000000) (F64.eps (F64.ofBits 0x3fe0000000000000))) =
      F64.ofBits 0xc32fffffffffffff := by decide

theorem tiesUp_boundary_round :
    roundF (F64.ofBits 0xc330000000000000) .NearestTiesUp =
      F64.ofBits 0xc330000000000000 := by decide

theorem exactRound_tiesUp_floor (n : Int) (d : Nat) (hd : 0 < d) :
    exactRound n d .NearestTiesUp = (2*n + (d : Int)) / (2*(d : Int)) := by
  have hrem0 := Int.emod_nonneg n (by omega : (d : Int) ≠ 0)
  have hrem1 := Int.emod_lt_of_pos n (by omega : (0 : Int) < d)
  have hdiv := Int.mul_ediv_add_emod n (d : Int)
  rw [Int.mul_comm (d : Int) (n / (d : Int))] at hdiv
  have hscale : (n / (d : Int)) * (2*(d : Int)) =
      2 * ((n / (d : Int)) * (d : Int)) := by
    rw [← Int.mul_assoc, Int.mul_comm (n / (d : Int)) 2, Int.mul_assoc]
  by_cases hr : n % (d : Int) = 0
  · simp only [exactRound, hr, ↓reduceIte]
    symm
    apply (Int.ediv_eq_iff_of_pos (by omega : (0 : Int) < 2*(d : Int))).mpr
    simp only [hscale]
    omega
  · simp only [exactRound, hr, ↓reduceIte]
    split
    all_goals
      symm
      apply (Int.ediv_eq_iff_of_pos (by omega : (0 : Int) < 2*(d : Int))).mpr
      simp only [Int.add_mul, Int.one_mul, hscale]
      omega

theorem copysign_fields (x y : F64) :
    F64.exponentField (copysign x y) = F64.exponentField x ∧
      F64.fraction (copysign x y) = F64.fraction x := by
  have hx := tb_lt x
  have hy := tb_lt y
  simp only [copysign, F64.exponentField, F64.fraction, tb_ofBits]
  cases hs : F64.signbit y <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> omega

theorem copysign_finite (x y : F64) :
    F64.isfinite (copysign x y) = F64.isfinite x := by
  simp only [F64.isfinite, (copysign_fields x y).1]

theorem toRat_copysign (x y : F64) :
    F64.toRat (copysign x y) =
      (if F64.signbit y then -((F64.toRat x).1.natAbs : Int)
        else ((F64.toRat x).1.natAbs : Int), (F64.toRat x).2) := by
  simp only [F64.toRat, copysign_finite, (copysign_fields x y).1,
    (copysign_fields x y).2, (copysignFloatSpec_proven x y).1]
  cases hf : F64.isfinite x <;> cases hx : F64.signbit x <;> cases hy : F64.signbit y <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Int.natAbs_zero, Int.natCast_zero, Int.neg_zero]
  all_goals repeat' split
  all_goals simp_all only [Int.natAbs_neg, Int.natAbs_natCast,
    Int.natAbs_mul, Int.natCast_mul, Int.neg_mul]

theorem tiesUp_c1 :
    F64.sub (F64.ofBits 0x3fd0000000000000) (F64.eps (F64.ofBits 0x3fe0000000000000)) =
      F64.ofBits 0x3fcffffffffffffc := by decide

theorem tiesUp_c2 :
    F64.add (F64.ofBits 0x3fd0000000000000) (F64.eps (F64.ofBits 0x3fe0000000000000)) =
      F64.ofBits 0x3fd0000000000002 := by decide

def tiesUpSum (x : F64) : F64 :=
  F64.add (F64.add x (F64.ofBits 0x3fcffffffffffffc)) (F64.ofBits 0x3fd0000000000002)

theorem roundF_tiesUp_form (x : F64) :
    roundF x .NearestTiesUp = copysign (F64.floor (tiesUpSum x)) x := by
  simp only [roundF, tiesUp_c1, tiesUp_c2, tiesUpSum]

theorem tiesUp_exact_of_sum_floor (x : F64) (hx : F64.isfinite x = true)
    (hb : F64.isfinite (tiesUpSum x) = true)
    (hfloor : (F64.toRat (tiesUpSum x)).1 / ((F64.toRat (tiesUpSum x)).2 : Int) =
      exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  have hy := roundF_exact (tiesUpSum x) .Down (by decide) hb
  have hdown : exactRound (F64.toRat (tiesUpSum x)).1
      (F64.toRat (tiesUpSum x)).2 .Down =
        (F64.toRat (tiesUpSum x)).1 / ((F64.toRat (tiesUpSum x)).2 : Int) := by
    simp only [exactRound]
    split <;> rfl
  have hyr : (F64.toRat (F64.floor (tiesUpSum x))).1 =
      exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
        ((F64.toRat (F64.floor (tiesUpSum x))).2 : Int) := by
    simpa only [roundF, F64.floor, hdown, hfloor] using hy.2.2
  have hm : exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp =
      if F64.signbit x then
        -(magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) .NearestTiesUp : Int)
      else (magnitude (F64.toRat x).1.natAbs (F64.toRat x).2 (F64.signbit x) .NearestTiesUp : Int) := by
    calc
      _ = exactRound
          (if F64.signbit x then -((F64.toRat x).1.natAbs : Int)
            else ((F64.toRat x).1.natAbs : Int)) (F64.toRat x).2 .NearestTiesUp :=
        congrArg (fun n => exactRound n (F64.toRat x).2 .NearestTiesUp) (toRat_signed x hx)
      _ = _ := exactRound_signed _ _ _ _ (toRat_den_pos x hx)
  rw [roundF_tiesUp_form]
  refine ⟨?_, (copysignFloatSpec_proven _ _).1, ?_⟩
  · rw [copysign_finite]
    exact hy.1
  · rw [toRat_copysign]
    rw [hyr, hm]
    cases hs : F64.signbit x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_mul, Int.natAbs_neg,
        Int.natAbs_natCast, Int.natCast_mul, Int.neg_mul]

theorem rq_near_upper (q d r : Nat) (hd : 0 < d) (hr : 2*r < d) :
    rq (q*d+r) d = q := by
  have hr0 : r < d := by omega
  have hq : (q*d+r) / d = q :=
    Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have hm : (q*d+r) % d = r := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr0]
  simp [rq, hq, hm, show ¬(2*r > d) by omega, show 2*r ≠ d by omega]

theorem rq_near_lower (q d r : Nat) (hq : 0 < q) (hd : 0 < d) (hr : 2*r < d) :
    rq (q*d-r) d = q := by
  by_cases hr0 : r = 0
  · rw [hr0, Nat.sub_zero, rq_exact _ _ hd (Nat.mul_mod_left _ _),
      Nat.mul_div_cancel _ hd]
  · have hr1 : r < d := by omega
    have hqd : d ≤ q*d := by
      have hh := Nat.mul_le_mul_right d (by omega : 1 ≤ q)
      simpa only [Nat.one_mul] using hh
    have hn : q*d-r = (q-1)*d + (d-r) := by
      rw [Nat.sub_mul, Nat.one_mul]
      omega
    have hdiv : ((q-1)*d + (d-r)) / d = q-1 :=
      Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hmod : ((q-1)*d + (d-r)) % d = d-r := by
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hn]
    have hinc : d < 2*(d-r) := by omega
    simp [rq, hdiv, hmod, hinc]
    omega

theorem add_finite (x y : F64) (hx : F64.isfinite x = true)
    (hy : F64.isfinite y = true) :
    F64.add x y = F64.roundRat
      ((F64.toRat x).1 * ((F64.toRat y).2 : Int) +
        (F64.toRat y).1 * ((F64.toRat x).2 : Int))
      ((F64.toRat x).2 * (F64.toRat y).2) (F64.signbit x && F64.signbit y) := by
  simp only [F64.add, finite_not_nan hx, finite_not_nan hy,
    finite_not_inf hx, finite_not_inf hy, Bool.false_eq_true, ↓reduceIte]

theorem roundRat_quarter_grid (n : Int) (d : Nat) (zs : Bool)
    (hn : n ≠ 0) (hd : 3 ≤ d) (hlog : n.natAbs.log2 = d-3) :
    F64.roundRat n (2^d) zs =
      pk (decide (n < 0)) (rq (n.natAbs*2^55) (2^d)) (-55) := by
  have hp : 0 < n.natAbs := by omega
  have hfl : fl2 n.natAbs (2^d) = -3 := by
    calc
      _ = fl2 (n.natAbs*2^0) (2^d) := by rw [Nat.pow_zero, Nat.mul_one]
      _ = (((n.natAbs.log2+0 : Nat) : Int)-(d : Int)) := fl2_pow n.natAbs 0 d hp
      _ = _ := by rw [hlog]; omega
  have hd0 : ¬(2^d == 0) = true := by
    simp only [beq_iff_eq]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  have hn0 : ¬(n == 0) = true := by simpa only [beq_iff_eq] using hn
  rw [roundRat_eq, ite_f hd0, ite_f hn0, hfl,
    ite_f (by decide : ¬((-3 : Int) ≥ 1024)),
    ite_f (by decide : ¬((-3 : Int) < -1075)),
    show max ((-3 : Int)-52) (-1074) = -55 by decide,
    ite_f (by decide : ¬((-55 : Int) ≥ 0))]
  rfl

theorem quarter_add_grid (a i : Nat) (s zs : Bool)
    (ha : a < 2^53) (hi : 106 ≤ i) :
    F64.roundRat
      ((if s then -(a : Int) else (a : Int)) * ((2^55 : Nat) : Int) +
        ((2^53-4 : Nat) : Int) * ((2^i : Nat) : Int)) (2^(i+55)) zs =
      pk false (if s then
        rq ((2^53-4)*2^(i+55)-a*2^110) (2^(i+55))
      else rq ((2^53-4)*2^(i+55)+a*2^110) (2^(i+55))) (-55) := by
  let M := 2^53-4
  have hMdef : M = 2^53-4 := rfl
  rw [← hMdef]
  clear_value M
  let P := 2^(i-55)
  let N := if s then M*P-a else M*P+a
  have hP : 2^51 ≤ P := Nat.pow_le_pow_right (by decide) (by omega)
  have haP : a < 4*P := by omega
  have hML : 2^52*P+4*P ≤ M*P := by
    have hh := Nat.mul_le_mul_right P (by omega : 2^52+4 ≤ M)
    simpa only [Nat.add_mul] using hh
  have hMU : M*P+4*P = 2^53*P := by rw [← Nat.add_mul, show M+4 = 2^53 by omega]
  have hMP : a ≤ M*P := by omega
  have hlow : 2^(i-3) ≤ N := by
    have hp : 2^(i-3) = 2^52 * P := by
      dsimp only [P]
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hp]
    dsimp only [N]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hupp : N < 2^((i-3)+1) := by
    have hp : 2^((i-3)+1) = 2^53 * P := by
      dsimp only [P]
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hp]
    dsimp only [N]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hN0 : 0 < N := by have := Nat.two_pow_pos (i-3); omega
  have hlog : N.log2 = i-3 := by
    have hne : N ≠ 0 := by omega
    have h1 := (Nat.log2_lt hne).mpr hupp
    have h2 : ¬ N.log2 < i-3 := fun hh =>
      absurd hlow (Nat.not_le.mpr ((Nat.log2_lt hne).mp hh))
    omega
  have hpi : 2^i = P * 2^55 := by
    dsimp only [P]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hnum :
      (if s then -(a : Int) else (a : Int)) * ((2^55 : Nat) : Int) +
        (M : Int) * ((2^i : Nat) : Int) = ((N * 2^55 : Nat) : Int) := by
    rw [hpi]
    cases s <;>
      simp only [N, Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.natCast_add,
        Int.natCast_sub hMP, Int.add_mul, Int.neg_mul,
        Int.mul_assoc, Int.sub_eq_add_neg, Int.add_comm]
  let D := 2^(i+55)
  let R := a * 2^110
  have hPD : P * 2^110 = D := by
    dsimp only [P, D]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hscaled : N * 2^55 * 2^55 = if s then M*D-R else M*D+R := by
    rw [Nat.mul_assoc, show (2^55 : Nat) * 2^55 = 2^110 by decide]
    cases s <;>
      simp only [N, Bool.false_eq_true, ↓reduceIte, Nat.add_mul, Nat.sub_mul,
        Nat.mul_assoc, hPD, R]
  have hn : ((N*2^55 : Nat) : Int) ≠ 0 := by
    have hh := Nat.mul_pos hN0 (Nat.two_pow_pos 55)
    omega
  have hs : decide (((N*2^55 : Nat) : Int) < 0) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  have hlogI : (((N*2^55 : Nat) : Int).natAbs).log2 = (i+55)-3 := by
    rw [Int.natAbs_natCast, log2_mul_pow 55 hN0, hlog]
    omega
  have hq : rq (((N*2^55 : Nat) : Int).natAbs*2^55) (2^(i+55)) =
      if s then rq (M*2^(i+55)-a*2^110) (2^(i+55))
        else rq (M*2^(i+55)+a*2^110) (2^(i+55)) := by
    rw [Int.natAbs_natCast, hscaled]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, D, R]
  calc
    _ = F64.roundRat ((N*2^55 : Nat) : Int) (2^(i+55)) zs := by rw [hnum]
    _ = pk (decide (((N*2^55 : Nat) : Int) < 0))
        (rq (((N*2^55 : Nat) : Int).natAbs*2^55) (2^(i+55))) (-55) :=
      roundRat_quarter_grid _ _ zs hn (by omega) hlogI
    _ = _ := by rw [hs, hq]

theorem roundRat_tiny_add_c1 (a i : Nat) (s zs : Bool)
    (ha : a < 2^53) (hi : 109 ≤ i) :
    F64.roundRat
      ((if s then -(a : Int) else (a : Int)) * ((2^55 : Nat) : Int) +
        ((2^53-4 : Nat) : Int) * ((2^i : Nat) : Int)) (2^(i+55)) zs =
      F64.ofBits 0x3fcffffffffffffc := by
  let M := 2^53-4
  let D := 2^(i+55)
  let R := a*2^110
  have hR : 2*R < D := by
    have hh := Nat.mul_lt_mul_of_pos_right (by omega : 2*a < 2^54) (Nat.two_pow_pos 110)
    rw [Nat.mul_assoc, ← Nat.pow_add] at hh
    have hd : 2^164 ≤ 2^(i+55) := Nat.pow_le_pow_right (by decide) (by omega)
    dsimp only [R, D]
    omega
  rw [quarter_add_grid a i s zs ha (by omega)]
  change pk false (if s then rq (M*D-R) D else rq (M*D+R) D) (-55) = _
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rq_near_upper M D R (Nat.two_pow_pos _) hR]
    decide
  · simp only [↓reduceIte]
    rw [rq_near_lower M D R (by decide) (Nat.two_pow_pos _) hR]
    decide

theorem tiny_add_c1 (x : F64) (a i : Nat) (hx : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (ha : a < 2^53) (hi : 109 ≤ i) :
    F64.add x (F64.ofBits 0x3fcffffffffffffc) = F64.ofBits 0x3fcffffffffffffc := by
  have hc : F64.toRat (F64.ofBits 0x3fcffffffffffffc) =
      (((2^53-4 : Nat) : Int), 2^55) := by decide
  rw [add_finite x _ hx (by decide), hr, hc, ← Nat.pow_add]
  exact roundRat_tiny_add_c1 a i _ _ ha hi

theorem tiesUp_tiny_value (x : F64) (a i : Nat) (hx : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (ha : a < 2^53) (hi : 109 ≤ i) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  have hs : tiesUpSum x = F64.ofBits 0x3fe0000000000000 := by
    unfold tiesUpSum
    rw [tiny_add_c1 x a i hx hr ha hi]
    decide
  have hpow : 2^54 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
  have hhalf : 2*a < 2^i := by omega
  have he : exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp = 0 := by
    rw [hr, exactRound_tiesUp_floor _ _ (Nat.two_pow_pos _)]
    cases hsign : F64.signbit x <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      apply (Int.ediv_eq_iff_of_pos (by have := Nat.two_pow_pos i; omega)).mpr
      simp only [Int.zero_mul]
      omega
  apply tiesUp_exact_of_sum_floor x hx
  · rw [hs]
    decide
  · rw [hs, he]
    decide

theorem tiesUp_tiny_exact (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 ≤ 966) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases h0 : F64.toBits x / 2^52 % 2048 = 0
  · exact tiesUp_tiny_value x (F64.toBits x % 2^52) 1074 hx
      (toRat_subn x h0) (by omega) (by decide)
  · exact tiesUp_tiny_value x (F64.toBits x % 2^52 + 2^52)
      (1075 - F64.toBits x / 2^52 % 2048) hx
      (toRat_norm x (by omega) (by omega)) (by omega) (by omega)

theorem log2_of_interval (N L : Nat) (hlo : 2^L ≤ N) (hhi : N < 2^(L+1)) :
    N.log2 = L := by
  have hn : N ≠ 0 := by have := Nat.two_pow_pos L; omega
  have h1 := (Nat.log2_lt hn).mpr hhi
  have h2 : ¬ N.log2 < L := fun hh =>
    absurd hlo (Nat.not_le.mpr ((Nat.log2_lt hn).mp hh))
  omega

theorem roundRat_integral_grid (n : Int) (d e : Nat) (zs : Bool)
    (hn : n ≠ 0) (hlog : n.natAbs.log2 = e+d) (he0 : 52 ≤ e) (he1 : e ≤ 1023) :
    F64.roundRat n (2^d) zs =
      pk (decide (n < 0)) (rq n.natAbs (2^(d+(e-52)))) ((e-52 : Nat) : Int) := by
  have hpos : 0 < n.natAbs := by omega
  have hfl : fl2 n.natAbs (2^d) = (e : Int) := by
    calc
      _ = fl2 (n.natAbs * 2^0) (2^d) := by rw [Nat.pow_zero, Nat.mul_one]
      _ = (((n.natAbs.log2+0 : Nat) : Int) - (d : Int)) :=
        fl2_pow n.natAbs 0 d hpos
      _ = _ := by rw [hlog]; omega
  have hd0 : ¬(2^d == 0) = true := by
    simp only [beq_iff_eq]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  have hn0 : ¬(n == 0) = true := by simpa only [beq_iff_eq] using hn
  rw [roundRat_eq, ite_f hd0, ite_f hn0, hfl,
    ite_f (by omega), ite_f (by omega)]
  have hk : max ((e : Int)-52) (-1074) = ((e-52 : Nat) : Int) := by omega
  rw [hk, ite_t (Int.natCast_nonneg _)]
  change pk (decide (n < 0)) (rq n.natAbs (2^d * 2^(e-52))) ((e-52 : Nat) : Int) = _
  rw [← Nat.pow_add]

theorem pk_large_norm (s : Bool) (M j : Nat) (hM0 : 2^52 ≤ M)
    (hM1 : M < 2^53) (hj : j ≤ 971) :
    pk s M (j : Int) =
      F64.ofBits ((if s then 2^63 else 0) + (j+1075)*2^52 + (M-2^52)) := by
  rw [pk_norm s M (j : Int) hM0 hM1 (by omega) (by omega)]
  rw [show ((j : Int)+1075).toNat = j+1075 by omega]
  simp only [Nat.add_assoc]

theorem pk_large_carry (s : Bool) (j : Nat) (hj0 : 1 ≤ j) (hj1 : j ≤ 971) :
    pk s (2^53) ((j : Int)-1) =
      F64.ofBits ((if s then 2^63 else 0) + (j+1075)*2^52) := by
  unfold pk
  rw [ite_f (by decide : ¬((2^53 : Nat) == 0) = true)]
  simp only [show (2^53 : Nat) ≥ 2^53 by decide, ↓reduceIte,
    show (2^53 : Nat) / 2 = 2^52 by decide]
  have he : (j : Int)-1+1+1075 = j+1075 := by omega
  rw [he, ite_f (by omega : ¬((j : Int)+1075 ≥ 2047)),
    ite_f (by decide : ¬((2^52 : Nat) < 2^52))]
  simp only [Nat.sub_self, Nat.add_zero]
  rw [show ((j : Int)+1075).toNat = j+1075 by omega]

theorem roundRat_large_add_pos (M j d A : Nat) (zs : Bool)
    (hM0 : 2^52 ≤ M) (hM1 : M < 2^53) (hj : j ≤ 971)
    (hA : 2*A < 2^d) :
    F64.roundRat (((M * 2^(j+d) + A : Nat) : Int)) (2^d) zs =
      F64.ofBits ((j+1075)*2^52 + (M-2^52)) := by
  let D := 2^(j+d)
  let N := M*D+A
  have hD0 : 0 < D := Nat.two_pow_pos _
  have hD1 : 2^d ≤ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hA1 : 2*A < D := by omega
  have hp0 : 2^(52+j+d) = 2^52 * D := by
    dsimp only [D]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hp1 : 2^(52+j+d+1) = 2^53 * D := by
    dsimp only [D]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hlow : 2^(52+j+d) ≤ N := by
    rw [hp0]
    have hh := Nat.mul_le_mul_right D hM0
    dsimp only [N]
    omega
  have hupp : N < 2^(52+j+d+1) := by
    rw [hp1]
    have hh := Nat.mul_le_mul_right D (by omega : M+1 ≤ 2^53)
    rw [Nat.add_mul, Nat.one_mul] at hh
    dsimp only [N]
    omega
  have hlog : N.log2 = 52+j+d := log2_of_interval N _ hlow hupp
  have hN0 : N ≠ 0 := by have := Nat.two_pow_pos (52+j+d); omega
  have hs : decide ((N : Int) < 0) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  have hlogI : ((N : Int).natAbs).log2 = (52+j)+d := by
    simpa only [Int.natAbs_natCast] using hlog
  rw [roundRat_integral_grid (N : Int) d (52+j) zs (by omega) hlogI (by omega) (by omega)]
  rw [Int.natAbs_natCast, hs, show 52+j-52 = j by omega,
    show d+j = j+d by omega]
  rw [rq_near_upper M D A hD0 hA1, pk_large_norm false M j hM0 hM1 hj]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]

theorem roundRat_negative_grid (N e d Q : Nat) (zs : Bool) (hN : 0 < N)
    (he0 : 52 ≤ e) (he1 : e ≤ 1023) (hlog : N.log2 = e+d)
    (hq : rq N (2^(d+(e-52))) = Q) :
    F64.roundRat (-(N : Int)) (2^d) zs = pk true Q ((e-52 : Nat) : Int) := by
  have hn : -(N : Int) ≠ 0 := by omega
  have hlogI : (-(N : Int)).natAbs.log2 = e+d := by
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hlog
  have hs : decide (-(N : Int) < 0) = true := by
    simp only [decide_eq_true_eq]
    omega
  calc
    _ = pk (decide (-(N : Int) < 0))
        (rq (-(N : Int)).natAbs (2^(d+(e-52)))) ((e-52 : Nat) : Int) :=
      roundRat_integral_grid (-(N : Int)) d e zs hn hlogI he0 he1
    _ = _ := by rw [hs, Int.natAbs_neg, Int.natAbs_natCast, hq]

theorem negative_boundary_pack (N j d : Nat) (zs : Bool)
    (hj0 : 1 ≤ j) (hj1 : j ≤ 971) (hN0 : 0 < N)
    (hlog : N.log2 = (51+j)+d) (hq : rq N (2^(d+(51+j-52))) = 2^53) :
    F64.roundRat (-(N : Int)) (2^d) zs =
      F64.ofBits (2^63+(j+1075)*2^52) := by
  calc
    _ = pk true (2^53) ((51+j-52 : Nat) : Int) :=
      roundRat_negative_grid N (51+j) d (2^53) zs hN0 (by omega) (by omega) hlog hq
    _ = _ := by
      rw [show ((51+j-52 : Nat) : Int) = (j : Int)-1 by omega]
      exact pk_large_carry true j hj0 hj1

theorem neg_large_boundary (M j d A D N : Nat) (zs : Bool) (hMb : M = 2^52)
    (hj0 : 1 ≤ j) (hj1 : j ≤ 971) (hA0 : 0 < A) (hA1 : 2*A < 2^d)
    (hDdef : D = 2^(j+d)) (hNdef : N = M*D-A) (hN0 : 0 < N) :
    F64.roundRat (-(N : Int)) (2^d) zs =
      F64.ofBits (2^63+(j+1075)*2^52+(M-2^52)) := by
  have hD1 : 2^d ≤ D := by
    rw [hDdef]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hp0 : 2^(51+j+d) = 2^51 * D := by
    rw [hDdef, ← Nat.pow_add]
    congr 1
    omega
  have hp1 : 2^(51+j+d+1) = 2^52 * D := by
    rw [hDdef, ← Nat.pow_add]
    congr 1
    omega
  have hlow : 2^(51+j+d) ≤ N := by
    rw [hp0]
    have hh := Nat.mul_le_mul_right D (by omega : 2^51+1 ≤ M)
    rw [Nat.add_mul, Nat.one_mul] at hh
    rw [hNdef]
    omega
  have hupp : N < 2^(51+j+d+1) := by
    rw [hp1]
    have hh := Nat.mul_le_mul_right D (by omega : M ≤ 2^52)
    rw [hNdef]
    omega
  have hlog : N.log2 = (51+j)+d := log2_of_interval N _ hlow hupp
  have hDH : D = 2 * 2^(d+(j-1)) := by
    rw [hDdef]
    calc
      2^(j+d) = 2^(d+(j-1)+1) := congrArg (fun n : Nat => 2^n) (by omega)
      _ = 2 * 2^(d+(j-1)) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hN : N = 2^53 * 2^(d+(j-1)) - A := by
    rw [hNdef, hDH, ← Nat.mul_assoc, show M * 2 = 2^53 by omega]
  have hAH : 2*A < 2^(d+(j-1)) := by
    have hh : 2^d ≤ 2^(d+(j-1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hq : rq N (2^(d+(51+j-52))) = 2^53 := by
    rw [show 51+j-52 = j-1 by omega, hN]
    exact rq_near_lower _ _ A (by decide) (Nat.two_pow_pos _) hAH
  rw [show M-2^52 = 0 by omega, Nat.add_zero]
  exact negative_boundary_pack N j d zs hj0 hj1 hN0 hlog hq

theorem neg_large_interior (M j d A D N : Nat) (zs : Bool)
    (hM0 : 2^52 < M) (hM1 : M < 2^53) (hj1 : j ≤ 971)
    (hDdef : D = 2^(j+d)) (hNdef : N = M*D-A)
    (hA2 : 2*A < D) (hD0 : 0 < D) (hN0 : 0 < N) :
    F64.roundRat (-(N : Int)) (2^d) zs =
      F64.ofBits (2^63+(j+1075)*2^52+(M-2^52)) := by
  have hp0 : 2^(52+j+d) = 2^52 * D := by
    rw [hDdef, ← Nat.pow_add]
    congr 1
    omega
  have hp1 : 2^(52+j+d+1) = 2^53 * D := by
    rw [hDdef, ← Nat.pow_add]
    congr 1
    omega
  have hlow : 2^(52+j+d) ≤ N := by
    rw [hp0]
    have hh := Nat.mul_le_mul_right D (by omega : 2^52 ≤ M-1)
    rw [Nat.sub_mul, Nat.one_mul] at hh
    rw [hNdef]
    omega
  have hupp : N < 2^(52+j+d+1) := by
    rw [hp1]
    have hh := Nat.mul_lt_mul_of_pos_right hM1 hD0
    rw [hNdef]
    omega
  have hlog : N.log2 = (52+j)+d := log2_of_interval N _ hlow hupp
  have hq : rq N (2^(d+(52+j-52))) = M := by
    rw [show 52+j-52 = j by omega, show d+j = j+d by omega, hNdef, ← hDdef]
    exact rq_near_lower M D A (by omega) hD0 hA2
  calc
    _ = pk true M ((52+j-52 : Nat) : Int) :=
      roundRat_negative_grid N (52+j) d M zs hN0 (by omega) (by omega) hlog hq
    _ = _ := by
      rw [show 52+j-52 = j by omega]
      exact pk_large_norm true M j (by omega) hM1 hj1

theorem roundRat_large_add_neg (M j d A : Nat) (zs : Bool)
    (hM0 : 2^52 ≤ M) (hM1 : M < 2^53) (hj0 : 1 ≤ j) (hj1 : j ≤ 971)
    (hA0 : 0 < A) (hA1 : 2*A < 2^d) :
    F64.roundRat (-((M * 2^(j+d) : Nat) : Int) + (A : Int)) (2^d) zs =
      F64.ofBits (2^63 + (j+1075)*2^52 + (M-2^52)) := by
  let D := 2^(j+d)
  let N := M*D-A
  have hD0 : 0 < D := Nat.two_pow_pos _
  have hD1 : 2^d ≤ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hA2 : 2*A < D := by omega
  have hMD : D ≤ M*D := by
    have hh := Nat.mul_le_mul_right D (by omega : 1 ≤ M)
    simpa only [Nat.one_mul] using hh
  have hMA : A ≤ M*D := by omega
  have hN0 : 0 < N := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by omega : A < D) hMD)
  have hn : -((M * 2^(j+d) : Nat) : Int) + (A : Int) = -(N : Int) := by
    change -((M*D : Nat) : Int) + (A : Int) = -((M*D-A : Nat) : Int)
    rw [Int.natCast_sub hMA, Int.neg_sub, Int.sub_eq_add_neg, Int.add_comm]
  rw [hn]
  have hDdef : D = 2^(j+d) := rfl
  have hNdef : N = M*D-A := rfl
  clear_value N D
  by_cases hMb : M = 2^52
  · exact neg_large_boundary M j d A D N zs hMb hj0 hj1 hA0 hA1 hDdef hNdef hN0
  · exact neg_large_interior M j d A D N zs (by omega) hM1 hj1 hDdef hNdef hA2 hD0 hN0

theorem add_large_small (x c : F64) (A d : Nat)
    (hx : F64.isfinite x = true) (hc : F64.isfinite c = true)
    (hrc : F64.toRat c = ((A : Int), 2^d))
    (he : 1076 ≤ F64.toBits x / 2^52 % 2048)
    (hA0 : 0 < A) (hA1 : 2*A < 2^d) : F64.add x c = x := by
  have he1 : F64.toBits x / 2^52 % 2048 ≤ 2046 := by
    have hh : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hx
    omega
  let M := F64.toBits x % 2^52 + 2^52
  let j := F64.toBits x / 2^52 % 2048 - 1075
  have hM0 : 2^52 ≤ M := by dsimp only [M]; omega
  have hM1 : M < 2^53 := by dsimp only [M]; omega
  have hj0 : 1 ≤ j := by dsimp only [j]; omega
  have hj1 : j ≤ 971 := by dsimp only [j]; omega
  have hrx : F64.toRat x =
      ((if F64.signbit x then -(M : Int) else (M : Int)) * ((2^j : Nat) : Int), 1) :=
    toRat_big x (by omega) he1
  have hprod : (M : Int) * ((2^j : Nat) : Int) * ((2^d : Nat) : Int) =
      ((M * 2^(j+d) : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul, Nat.mul_assoc, ← Nat.pow_add]
  have hnum :
      (if F64.signbit x then -(M : Int) else (M : Int)) *
          ((2^j : Nat) : Int) * ((2^d : Nat) : Int) + (A : Int) =
      if F64.signbit x then -((M * 2^(j+d) : Nat) : Int) + (A : Int)
        else ((M * 2^(j+d) : Nat) : Int) + (A : Int) := by
    cases hs : F64.signbit x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, hprod]
  rw [add_finite x c hx hc, hrx, hrc]
  simp only [Int.natCast_one, Int.mul_one, Nat.one_mul]
  rw [hnum]
  cases hs : F64.signbit x <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | (rw [← Int.natCast_add]; rw [roundRat_large_add_pos M j d A _ hM0 hM1 hj1 hA1])
    | rw [roundRat_large_add_neg M j d A _ hM0 hM1 hj0 hj1 hA0 hA1]
  all_goals
    rw [show M-2^52 = F64.toBits x % 2^52 by dsimp only [M]; omega,
      show j+1075 = F64.toBits x / 2^52 % 2048 by dsimp only [j]; omega]
    apply f64_ext
    rw [tb_ofBits]
    have hf := fields x
    rw [hs] at hf
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hf
    rw [hf, Nat.mod_eq_of_lt (tb_lt x)]

theorem tiesUp_large_exact (x : F64) (hx : F64.isfinite x = true)
    (he : 1076 ≤ F64.toBits x / 2^52 % 2048) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  have hc1 : F64.toRat (F64.ofBits 0x3fcffffffffffffc) =
      (((2^53-4 : Nat) : Int), 2^55) := by decide
  have hc2 : F64.toRat (F64.ofBits 0x3fd0000000000002) =
      (((2^52+2 : Nat) : Int), 2^54) := by decide
  have hb : tiesUpSum x = x := by
    unfold tiesUpSum
    rw [add_large_small x _ (2^53-4) 55 hx (by decide) hc1 he (by decide) (by decide),
      add_large_small x _ (2^52+2) 54 hx (by decide) hc2 he (by decide) (by decide)]
  have hd : (F64.toRat x).2 = 1 := by
    rw [toRat_big x (by omega) (by
      have hh : F64.toBits x / 2^52 % 2048 ≠ 2047 := by
        simpa [F64.isfinite, F64.exponentField] using hx
      omega)]
  apply tiesUp_exact_of_sum_floor x hx
  · rwa [hb]
  · rw [hb]
    simp [hd, exactRound]

theorem add_unit_binade_small (x c : F64) (A d : Nat)
    (hx : F64.isfinite x = true) (hc : F64.isfinite c = true)
    (hrc : F64.toRat c = ((A : Int), 2^d))
    (he : F64.toBits x / 2^52 % 2048 = 1075)
    (hsafe : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0)
    (hA0 : 0 < A) (hA1 : 2*A < 2^d) : F64.add x c = x := by
  let M := F64.toBits x % 2^52 + 2^52
  have hM0 : 2^52 ≤ M := by dsimp only [M]; omega
  have hM1 : M < 2^53 := by dsimp only [M]; omega
  have hfrac : M-2^52 = F64.toBits x % 2^52 := by dsimp only [M]; omega
  have hrx : F64.toRat x = (if F64.signbit x then -(M : Int) else (M : Int), 1) := by
    rw [toRat_big x (by omega) (by omega), he]
    simp only [Nat.sub_self, Nat.pow_zero, Int.natCast_one, Int.mul_one]
    rfl
  have hreconstruct (s : Bool) (hs : F64.signbit x = s) :
      F64.ofBits ((if s then 2^63 else 0)+1075*2^52+(M-2^52)) = x := by
    rw [← hs]
    apply f64_ext
    rw [tb_ofBits, hfrac, ← he, fields x, Nat.mod_eq_of_lt (tb_lt x)]
  rw [add_finite x c hx hc, hrx, hrc]
  simp only [Int.natCast_one, Int.mul_one, Nat.one_mul]
  cases hs : F64.signbit x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Int.natCast_mul, ← Int.natCast_add]
    have hh := roundRat_large_add_pos M 0 d A (false && F64.signbit c) hM0 hM1 (by decide) hA1
    simp only [Nat.zero_add] at hh
    rw [hh]
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using hreconstruct false hs
  · simp only [↓reduceIte]
    have hMstrict : 2^52 < M := by
      rcases hsafe with hh | hh
      · rw [hs] at hh
        cases hh
      · dsimp only [M]
        omega
    let D := 2^d
    let N := M*D-A
    have hD0 : 0 < D := Nat.two_pow_pos _
    have hMD : D ≤ M*D := by
      have hh := Nat.mul_le_mul_right D (by omega : 1 ≤ M)
      simpa only [Nat.one_mul] using hh
    have hMA : A ≤ M*D := by omega
    have hN0 : 0 < N := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by omega : A < D) hMD)
    have hn : -(M : Int) * ((2^d : Nat) : Int) + (A : Int) = -(N : Int) := by
      rw [Int.neg_mul, ← Int.natCast_mul]
      change -((M*D : Nat) : Int)+(A : Int) = -((M*D-A : Nat) : Int)
      rw [Int.natCast_sub hMA, Int.neg_sub, Int.sub_eq_add_neg, Int.add_comm]
    rw [hn]
    have hh := neg_large_interior M 0 d A D N (true && F64.signbit c)
      hMstrict hM1 (by decide) (by simp only [Nat.zero_add]; rfl) rfl hA1 hD0 hN0
    simp only [Nat.zero_add] at hh
    rw [hh]
    simpa only [↓reduceIte] using hreconstruct true hs

theorem tiesUp_unit_exact (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 = 1075) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases hs : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0
  · have hc1 : F64.toRat (F64.ofBits 0x3fcffffffffffffc) =
        (((2^53-4 : Nat) : Int), 2^55) := by decide
    have hc2 : F64.toRat (F64.ofBits 0x3fd0000000000002) =
        (((2^52+2 : Nat) : Int), 2^54) := by decide
    have hb : tiesUpSum x = x := by
      unfold tiesUpSum
      rw [add_unit_binade_small x _ (2^53-4) 55 hx (by decide) hc1 he hs (by decide) (by decide),
        add_unit_binade_small x _ (2^52+2) 54 hx (by decide) hc2 he hs (by decide) (by decide)]
    have hd : (F64.toRat x).2 = 1 := by rw [toRat_big x (by omega) (by omega)]
    apply tiesUp_exact_of_sum_floor x hx
    · rwa [hb]
    · rw [hb]
      simp [hd, exactRound]
  · have hsign : F64.signbit x = true := by
      cases hh : F64.signbit x
      · exact False.elim (hs (Or.inl hh))
      · rfl
    have hfrac : F64.toBits x % 2^52 = 0 := by
      by_cases hh : F64.toBits x % 2^52 = 0
      · exact hh
      · exact False.elim (hs (Or.inr hh))
    have hbits : x = F64.ofBits 0xc330000000000000 := by
      apply f64_ext
      rw [tb_ofBits]
      have hf := fields x
      rw [he, hfrac, hsign] at hf
      simp only [↓reduceIte] at hf
      omega
    subst x
    decide

theorem tiesUp_high_exact (x : F64) (hx : F64.isfinite x = true)
    (he : 1075 ≤ F64.toBits x / 2^52 % 2048) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases hh : F64.toBits x / 2^52 % 2048 = 1075
  · exact tiesUp_unit_exact x hx hh
  · exact tiesUp_large_exact x hx (by omega)

theorem log2_center_upper (M d r : Nat) (hM0 : 2^52 ≤ M) (hM1 : M < 2^53)
    (hr : r < 2^d) : (M*2^d+r).log2 = 52+d := by
  apply log2_of_interval
  · rw [Nat.pow_add]
    have hh := Nat.mul_le_mul_right (2^d) hM0
    omega
  · rw [show 52+d+1 = 53+d by omega, Nat.pow_add]
    have hh := Nat.mul_le_mul_right (2^d) (by omega : M+1 ≤ 2^53)
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega

theorem log2_center_lower (M d r : Nat) (hM0 : 2^52 < M) (hM1 : M < 2^53)
    (hr : r < 2^d) : (M*2^d-r).log2 = 52+d := by
  apply log2_of_interval
  · rw [Nat.pow_add]
    have hh := Nat.mul_le_mul_right (2^d) (by omega : 2^52 ≤ M-1)
    rw [Nat.sub_mul, Nat.one_mul] at hh
    omega
  · rw [show 52+d+1 = 53+d by omega, Nat.pow_add]
    have hh := Nat.mul_lt_mul_of_pos_right hM1 (Nat.two_pow_pos d)
    omega

theorem roundRat_half_grid (n : Int) (d : Nat) (zs : Bool)
    (hn : n ≠ 0) (hlog : n.natAbs.log2 = 51+d) :
    F64.roundRat n (2^d) zs =
      pk (decide (n < 0)) (rq (n.natAbs*2) (2^d)) (-1) := by
  have hp : 0 < n.natAbs := by omega
  have hfl : fl2 n.natAbs (2^d) = 51 := by
    calc
      _ = fl2 (n.natAbs*2^0) (2^d) := by rw [Nat.pow_zero, Nat.mul_one]
      _ = (((n.natAbs.log2+0 : Nat) : Int)-(d : Int)) := fl2_pow n.natAbs 0 d hp
      _ = _ := by rw [hlog]; omega
  have hd0 : ¬(2^d == 0) = true := by
    simp only [beq_iff_eq]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  have hn0 : ¬(n == 0) = true := by simpa only [beq_iff_eq] using hn
  rw [roundRat_eq, ite_f hd0, ite_f hn0, hfl,
    ite_f (by decide : ¬((51 : Int) ≥ 1024)),
    ite_f (by decide : ¬((51 : Int) < -1075)),
    show max ((51 : Int)-52) (-1074) = -1 by decide,
    ite_f (by decide : ¬((-1 : Int) ≥ 0))]
  rfl

theorem roundRat_half_add_grid (M d A : Nat) (s zs : Bool)
    (hM0 : 2^52 ≤ M) (hM1 : M < 2^53)
    (hs : s = true → 2^52 < M) (hA : 2*A < 2^d) :
    F64.roundRat ((if s then -(M : Int) else (M : Int)) * ((2^d : Nat) : Int) + (2*A : Nat))
      (2^(d+1)) zs =
      pk s (if s then rq (M*2^(d+1)-4*A) (2^(d+1))
        else rq (M*2^(d+1)+4*A) (2^(d+1))) (-1) := by
  let N := if s then M*2^d-2*A else M*2^d+2*A
  have hMD : 2^d ≤ M*2^d := by
    have hh := Nat.mul_le_mul_right (2^d) (by omega : 1 ≤ M)
    simpa only [Nat.one_mul] using hh
  have hMA : 2*A ≤ M*2^d := by omega
  have hlog : N.log2 = 52+d := by
    cases hh : s
    · simpa only [N, hh, Bool.false_eq_true, ↓reduceIte] using
        log2_center_upper M d (2*A) hM0 hM1 hA
    · simpa only [N, hh, ↓reduceIte] using
        log2_center_lower M d (2*A) (hs hh) hM1 hA
  have hN0 : 0 < N := by
    cases hh : s
    · dsimp only [N]
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := Nat.two_pow_pos d
      omega
    · dsimp only [N]
      rw [hh]
      simp only [↓reduceIte]
      exact Nat.sub_pos_of_lt (by omega)
  have hnum :
      (if s then -(M : Int) else (M : Int)) * ((2^d : Nat) : Int) + ((2*A : Nat) : Int) =
        if s then -(N : Int) else (N : Int) := by
    cases hh : s <;>
      simp only [N, hh, Bool.false_eq_true, ↓reduceIte, Int.neg_mul,
        Int.natCast_add, Int.natCast_sub hMA, Int.natCast_mul,
        Int.neg_add, Int.neg_neg, Int.sub_eq_add_neg, Int.add_comm]
  have hn : (if s then -(N : Int) else (N : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hsign := signed_negative N s hN0
  have hlogI : (if s then -(N : Int) else (N : Int)).natAbs.log2 = 51+(d+1) := by
    rw [signed_natAbs, hlog]
    omega
  rw [hnum, roundRat_half_grid _ (d+1) zs hn hlogI, signed_natAbs, hsign]
  have hN2 : N*2 = if s then M*2^(d+1)-4*A else M*2^(d+1)+4*A := by
    cases hh : s <;>
      simp only [N, hh, Bool.false_eq_true, ↓reduceIte, Nat.sub_mul, Nat.add_mul,
        Nat.mul_assoc, ← Nat.pow_succ, show 2*(A*2) = 4*A by omega]
  rw [hN2]
  cases s <;> rfl

theorem rq_above_upper (q d r : Nat) (hr : r < d) (hh : d < 2*r) :
    rq (q*d+r) d = q+1 := by
  have hdiv : (q*d+r)/d = q :=
    Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have hmod : (q*d+r)%d = r := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]
  simp [rq, hdiv, hmod, hh]

theorem rq_above_lower (q d r : Nat) (hq : 0 < q) (hd : 0 < d)
    (hr : r < d) (hh : d < 2*r) : rq (q*d-r) d = q-1 := by
  have hqd : d ≤ q*d := by
    have ht := Nat.mul_le_mul_right d (by omega : 1 ≤ q)
    simpa only [Nat.one_mul] using ht
  have he : q*d-r = (q-1)*d+(d-r) := by rw [Nat.sub_mul, Nat.one_mul]; omega
  rw [he]
  exact rq_near_upper _ d (d-r) hd (by omega)

theorem pk_half_floor (Q : Nat) (s : Bool) (hQ0 : 2^52 ≤ Q) (hQ1 : Q ≤ 2^53) :
    F64.isfinite (pk s Q (-1)) = true ∧
      (F64.toRat (pk s Q (-1))).1 / ((F64.toRat (pk s Q (-1))).2 : Int) =
        (if s then -(Q : Int) else (Q : Int)) / 2 := by
  by_cases ht : Q = 2^53
  · subst Q
    cases s <;> decide
  · rw [pk_norm s Q (-1) hQ0 (by omega) (by decide) (by decide)]
    rw [show ((-1 : Int)+1075).toNat = 1074 by decide]
    simp only [← Nat.add_assoc]
    obtain ⟨hE, hF, hS, hfin⟩ := ProofMisc.norm_fields s 1074 Q (by decide) (by decide) hQ0 (by omega)
    refine ⟨hfin, ?_⟩
    rw [toRat_norm _ (by rw [hE]; decide) (by rw [hE]; decide)]
    rw [hS, hF, hE, Nat.sub_add_cancel hQ0]
    rfl

theorem add_half_binade_grid (x c : F64) (A d : Nat)
    (hx : F64.isfinite x = true) (hc : F64.isfinite c = true)
    (hrc : F64.toRat c = ((A : Int), 2^d))
    (he : F64.toBits x / 2^52 % 2048 = 1074)
    (hsafe : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0)
    (hA : 2*A < 2^d) :
    F64.add x c = pk (F64.signbit x)
      (if F64.signbit x then
        rq ((F64.toBits x % 2^52+2^52)*2^(d+1)-4*A) (2^(d+1))
      else rq ((F64.toBits x % 2^52+2^52)*2^(d+1)+4*A) (2^(d+1))) (-1) := by
  let M := F64.toBits x % 2^52+2^52
  have hrx : F64.toRat x = (if F64.signbit x then -(M : Int) else (M : Int), 2) := by
    have hh := toRat_norm x (by omega) (by omega)
    simpa only [he, Nat.reduceSub, Nat.pow_one] using hh
  have hs : F64.signbit x = true → 2^52 < M := by
    intro ht
    rcases hsafe with hh | hh
    · rw [ht] at hh
      cases hh
    · dsimp only [M]
      omega
  have hnum : (A : Int) * ((2 : Nat) : Int) = ((2*A : Nat) : Int) := by
    rw [Int.natCast_mul]
    omega
  have hden : (2 : Nat)*2^d = 2^(d+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [add_finite x c hx hc, hrx, hrc, hnum, hden]
  exact roundRat_half_add_grid M d A _ _ (by dsimp only [M]; omega)
    (by dsimp only [M]; omega) hs hA

theorem half_add_c1 (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 = 1074)
    (hsafe : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0) :
    F64.add x (F64.ofBits 0x3fcffffffffffffc) = x := by
  let M := F64.toBits x % 2^52+2^52
  have hM0 : 2^52 ≤ M := by dsimp only [M]; omega
  have hM1 : M < 2^53 := by dsimp only [M]; omega
  have hc : F64.toRat (F64.ofBits 0x3fcffffffffffffc) =
      (((2^53-4 : Nat) : Int), 2^55) := by decide
  rw [add_half_binade_grid x _ (2^53-4) 55 hx (by decide) hc he hsafe (by decide)]
  have hq :
      (if F64.signbit x then rq (M*2^56-4*(2^53-4)) (2^56)
        else rq (M*2^56+4*(2^53-4)) (2^56)) = M := by
    cases hs : F64.signbit x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact rq_near_upper M (2^56) (4*(2^53-4)) (by decide) (by decide)
    · simp only [↓reduceIte]
      exact rq_near_lower M (2^56) (4*(2^53-4)) (by omega) (by decide) (by decide)
  rw [hq, pk_norm _ M (-1) hM0 hM1 (by decide) (by decide),
    show ((-1 : Int)+1075).toNat = 1074 by decide]
  simp only [← Nat.add_assoc]
  apply f64_ext
  rw [tb_ofBits, show M-2^52 = F64.toBits x % 2^52 by dsimp only [M]; omega,
    ← he, fields x, Nat.mod_eq_of_lt (tb_lt x)]

theorem half_add_c2 (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 = 1074)
    (hsafe : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0) :
    F64.add x (F64.ofBits 0x3fd0000000000002) =
      pk (F64.signbit x)
        (if F64.signbit x then F64.toBits x % 2^52+2^52-1
          else F64.toBits x % 2^52+2^52+1) (-1) := by
  let M := F64.toBits x % 2^52+2^52
  have hc : F64.toRat (F64.ofBits 0x3fd0000000000002) =
      (((2^52+2 : Nat) : Int), 2^54) := by decide
  rw [add_half_binade_grid x _ (2^52+2) 54 hx (by decide) hc he hsafe (by decide)]
  have hq :
      (if F64.signbit x then rq (M*2^55-4*(2^52+2)) (2^55)
        else rq (M*2^55+4*(2^52+2)) (2^55)) =
        if F64.signbit x then M-1 else M+1 := by
    cases hs : F64.signbit x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact rq_above_upper M (2^55) (4*(2^52+2)) (by decide) (by decide)
    · simp only [↓reduceIte]
      exact rq_above_lower M (2^55) (4*(2^52+2)) (by dsimp only [M]; omega)
        (by decide) (by decide) (by decide)
  rw [hq]

theorem exactRound_half_tiesUp (n : Int) :
    exactRound n 2 .NearestTiesUp = (n+1)/2 := by
  rw [exactRound_tiesUp_floor n 2 (by decide)]
  omega

theorem tiesUp_half_exact (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 = 1074) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases hsafe : F64.signbit x = false ∨ F64.toBits x % 2^52 ≠ 0
  · let M := F64.toBits x % 2^52+2^52
    let Q := if F64.signbit x then M-1 else M+1
    have hM0 : 2^52 ≤ M := by dsimp only [M]; omega
    have hM1 : M < 2^53 := by dsimp only [M]; omega
    have hMstrict : F64.signbit x = true → 2^52 < M := by
      intro hs
      rcases hsafe with hh | hh
      · rw [hs] at hh
        cases hh
      · dsimp only [M]
        omega
    have hQ0 : 2^52 ≤ Q := by
      cases hs : F64.signbit x
      · simp only [Q, hs, Bool.false_eq_true, ↓reduceIte]
        omega
      · have hh := hMstrict hs
        simp only [Q, hs, ↓reduceIte]
        omega
    have hQ1 : Q ≤ 2^53 := by
      cases hs : F64.signbit x <;>
        simp only [Q, hs, Bool.false_eq_true, ↓reduceIte] <;> omega
    have hsum : tiesUpSum x = pk (F64.signbit x) Q (-1) := by
      unfold tiesUpSum
      rw [half_add_c1 x hx he hsafe]
      exact half_add_c2 x hx he hsafe
    have hpk := pk_half_floor Q (F64.signbit x) hQ0 hQ1
    have hrx : F64.toRat x = (if F64.signbit x then -(M : Int) else (M : Int), 2) := by
      have hh := toRat_norm x (by omega) (by omega)
      simpa only [he, Nat.reduceSub, Nat.pow_one] using hh
    apply tiesUp_exact_of_sum_floor x hx
    · rw [hsum]
      exact hpk.1
    · rw [hsum, hpk.2, hrx, exactRound_half_tiesUp]
      cases hs : F64.signbit x <;>
        simp only [Q, hs, Bool.false_eq_true, ↓reduceIte, Int.natCast_add,
          Int.natCast_sub (by omega : 1 ≤ M), Int.natCast_one] <;> omega
  · have hsign : F64.signbit x = true := by
      cases hh : F64.signbit x
      · exact False.elim (hsafe (Or.inl hh))
      · rfl
    have hfrac : F64.toBits x % 2^52 = 0 := by
      by_cases hh : F64.toBits x % 2^52 = 0
      · exact hh
      · exact False.elim (hsafe (Or.inr hh))
    have hbits : x = F64.ofBits 0xc320000000000000 := by
      apply f64_ext
      rw [tb_ofBits]
      have hf := fields x
      rw [he, hfrac, hsign] at hf
      simp only [↓reduceIte] at hf
      omega
    subst x
    decide

theorem tiesUp_top_exact (x : F64) (hx : F64.isfinite x = true)
    (he : 1074 ≤ F64.toBits x / 2^52 % 2048) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases hh : F64.toBits x / 2^52 % 2048 = 1074
  · exact tiesUp_half_exact x hx hh
  · exact tiesUp_high_exact x hx (by omega)

theorem rq_upper_range4 (q d r : Nat) (hd : 0 < d) (hr : r < 4*d) :
    q ≤ rq (q*d+r) d ∧ rq (q*d+r) d ≤ q+4 := by
  have hlo : q ≤ (q*d+r)/d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hhi : (q*d+r)/d < q+4 := (Nat.div_lt_iff_lt_mul hd).mpr (by
    rw [Nat.add_mul]
    omega)
  unfold rq
  dsimp only
  split <;> omega

theorem rq_lower_range4 (q d r : Nat) (hq : 4 ≤ q) (hd : 0 < d) (hr : r < 4*d) :
    q-4 ≤ rq (q*d-r) d ∧ rq (q*d-r) d ≤ q := by
  by_cases hz : r = 0
  · rw [hz, Nat.sub_zero, rq_exact _ _ hd (Nat.mul_mod_left _ _),
      Nat.mul_div_cancel _ hd]
    omega
  · have hqd : 4*d ≤ q*d := Nat.mul_le_mul_right d hq
    have hlo : q-4 ≤ (q*d-r)/d := (Nat.le_div_iff_mul_le hd).mpr (by
      rw [Nat.sub_mul]
      omega)
    have hhi : (q*d-r)/d < q := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
    unfold rq
    dsimp only
    split <;> omega

theorem quarter_neighbor_sum (Q : Nat) (hlo : 2^53-8 ≤ Q) (hhi : Q ≤ 2^53) :
    let y := F64.add (pk false Q (-55)) (F64.ofBits 0x3fd0000000000002)
    F64.isfinite y = true ∧ (F64.toRat y).1 / ((F64.toRat y).2 : Int) = 0 := by
  have hc : Q = 2^53-8 ∨ Q = 2^53-7 ∨ Q = 2^53-6 ∨ Q = 2^53-5 ∨
      Q = 2^53-4 ∨ Q = 2^53-3 ∨ Q = 2^53-2 ∨ Q = 2^53-1 ∨ Q = 2^53 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem tiesUp_neighbor_value (x : F64) (a i : Nat) (hx : F64.isfinite x = true)
    (hr : F64.toRat x = (if F64.signbit x then -(a : Int) else (a : Int), 2^i))
    (ha : a < 2^53) (hi : 106 ≤ i) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  let M := 2^53-4
  have hMdef : M = 2^53-4 := rfl
  let D := 2^(i+55)
  let R := a*2^110
  let Q := if F64.signbit x then rq (M*D-R) D else rq (M*D+R) D
  have hD0 : 0 < D := Nat.two_pow_pos _
  have hR0 : R < 2^163 := by
    have hh := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos 110)
    rw [← Nat.pow_add] at hh
    exact hh
  have hD1 : 2^161 ≤ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hR4 : R < 4*D := by
    have hh := Nat.mul_le_mul_left 4 hD1
    rw [show (4 : Nat)*2^161 = 2^163 by decide] at hh
    omega
  have hQ : 2^53-8 ≤ Q ∧ Q ≤ 2^53 := by
    cases hs : F64.signbit x <;> simp only [Q, hs, Bool.false_eq_true, ↓reduceIte]
    · have hh := rq_upper_range4 M D R hD0 hR4
      omega
    · have hh := rq_lower_range4 M D R (by decide) hD0 hR4
      omega
  have hc : F64.toRat (F64.ofBits 0x3fcffffffffffffc) =
      (((2^53-4 : Nat) : Int), 2^55) := by decide
  have hfirst : F64.add x (F64.ofBits 0x3fcffffffffffffc) = pk false Q (-55) := by
    rw [add_finite x _ hx (by decide), hr, hc, ← Nat.pow_add]
    exact quarter_add_grid a i _ _ ha hi
  have hsum : tiesUpSum x =
      F64.add (pk false Q (-55)) (F64.ofBits 0x3fd0000000000002) := by
    unfold tiesUpSum
    rw [hfirst]
  have hys := quarter_neighbor_sum Q hQ.1 hQ.2
  have hpow : 2^54 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
  have hhalf : 2*a < 2^i := by omega
  have hround : exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp = 0 := by
    rw [hr, exactRound_tiesUp_floor _ _ (Nat.two_pow_pos _)]
    cases hs : F64.signbit x <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      apply (Int.ediv_eq_iff_of_pos (by have := Nat.two_pow_pos i; omega)).mpr
      simp only [Int.zero_mul]
      omega
  apply tiesUp_exact_of_sum_floor x hx
  · rw [hsum]
    exact hys.1
  · rw [hsum, hys.2, hround]

theorem tiesUp_low_exact (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 ≤ 969) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
      (F64.toRat (roundF x .NearestTiesUp)).1 =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
          ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  by_cases h0 : F64.toBits x / 2^52 % 2048 = 0
  · exact tiesUp_neighbor_value x (F64.toBits x % 2^52) 1074 hx
      (toRat_subn x h0) (by omega) (by decide)
  · exact tiesUp_neighbor_value x (F64.toBits x % 2^52+2^52)
      (1075-F64.toBits x / 2^52 % 2048) hx
      (toRat_norm x (by omega) (by omega)) (by omega) (by omega)

theorem rq_gt_iff (n d k : Nat) (hd : 0 < d) :
    k < rq n d ↔
      (2*k+1)*d < 2*n ∨ (2*n = (2*k+1)*d ∧ k%2 = 1) := by
  have hr := Nat.mod_lt n hd
  have hn := Nat.div_add_mod n d
  rw [Nat.mul_comm d (n/d)] at hn
  have ht : (2*k+1)*d = 2*(k*d)+d := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [ht]
  rcases Nat.lt_trichotomy (n/d) k with hlt | heq | hgt
  · have hp := Nat.mul_le_mul_right d (by omega : n/d+1 ≤ k)
    rw [Nat.add_mul, Nat.one_mul] at hp
    have hl : 2*n < 2*(k*d)+d := by omega
    unfold rq
    dsimp only
    split <;> omega
  · rw [heq] at hn
    unfold rq
    rw [heq]
    dsimp only
    split
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      omega
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      omega
  · have hp := Nat.mul_le_mul_right d (by omega : k+1 ≤ n/d)
    rw [Nat.add_mul, Nat.one_mul] at hp
    have hl : 2*(k*d)+d < 2*n := by omega
    unfold rq
    dsimp only
    split <;> omega

theorem cross_threshold_le (a b c d t : Nat) (hc : 0 < c)
    (hab : a*d ≤ b*c) (ha : t*c ≤ a) : t*d ≤ b := by
  by_cases hb : t*d ≤ b
  · exact hb
  · have hh := Nat.mul_lt_mul_of_pos_right (by omega : b < t*d) hc
    have hl := Nat.mul_le_mul_right d ha
    have he : (t*d)*c = (t*c)*d := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    rw [he] at hh
    have hbad := Nat.lt_of_lt_of_le hh (Nat.le_trans hl hab)
    exact False.elim (Nat.lt_irrefl _ hbad)

theorem cross_threshold_lt (a b c d t : Nat) (hc : 0 < c) (hd : 0 < d)
    (hab : a*d ≤ b*c) (ha : t*c < a) : t*d < b := by
  have hh := Nat.mul_lt_mul_of_pos_right ha hd
  have he : (t*d)*c = (t*c)*d := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have ht : (t*d)*c < b*c := by
    rw [he]
    exact Nat.lt_of_lt_of_le hh hab
  exact (Nat.mul_lt_mul_right hc).mp ht

theorem rq_rational_monotone (n₁ d₁ n₂ d₂ : Nat) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hn : n₁*d₂ ≤ n₂*d₁) : rq n₁ d₁ ≤ rq n₂ d₂ := by
  by_cases hq : rq n₁ d₁ ≤ rq n₂ d₂
  · exact hq
  · let k := rq n₂ d₂
    have hq₁ : k < rq n₁ d₁ := by omega
    have hq₂ : ¬ k < rq n₂ d₂ := Nat.lt_irrefl _
    rw [rq_gt_iff _ _ _ hd₁] at hq₁
    rw [rq_gt_iff _ _ _ hd₂] at hq₂
    have hn₂ : (2*n₁)*d₂ ≤ (2*n₂)*d₁ := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hn
    rcases hq₁ with hs | ⟨he, hk⟩
    · have ht := cross_threshold_lt (2*n₁) (2*n₂) d₁ d₂ (2*k+1) hd₁ hd₂ hn₂ hs
      exact False.elim (hq₂ (Or.inl ht))
    · have ht := cross_threshold_le (2*n₁) (2*n₂) d₁ d₂ (2*k+1) hd₁ hn₂ (by omega)
      by_cases hl : (2*k+1)*d₂ < 2*n₂
      · exact False.elim (hq₂ (Or.inl hl))
      · have hEq : 2*n₂ = (2*k+1)*d₂ := by omega
        exact False.elim (hq₂ (Or.inr ⟨hEq, hk⟩))

theorem rq_monotone (n m d : Nat) (hd : 0 < d) (hnm : n ≤ m) :
    rq n d ≤ rq m d :=
  rq_rational_monotone n d m d hd hd (Nat.mul_le_mul_right d hnm)

theorem rq_scale (n d c : Nat) (hd : 0 < d) (hc : 0 < c) :
    rq (n*c) (d*c) = rq n d := by
  apply Nat.le_antisymm
  · apply rq_rational_monotone _ _ _ _ (Nat.mul_pos hd hc) hd
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    exact Nat.le_refl _
  · apply rq_rational_monotone _ _ _ _ hd (Nat.mul_pos hd hc)
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    exact Nat.le_refl _

theorem rq_upper_bound (n d q : Nat) (hd : 0 < d) (hn : n < q*d) :
    rq n d ≤ q := by
  have hh : n/d < q := (Nat.div_lt_iff_lt_mul hd).mpr hn
  unfold rq
  dsimp only
  split <;> omega

theorem rq_lower_bound (n d q : Nat) (hd : 0 < d) (hn : q*d ≤ n) :
    q ≤ rq n d := by
  have hh : q ≤ n/d := (Nat.le_div_iff_mul_le hd).mpr hn
  unfold rq
  dsimp only
  split <;> omega

def quantizeKey (n d k : Nat) : Nat := rq n (d*2^k)*2^k

theorem dyadic_grid_gap (k l : Nat) (hkl : k < l) : 2*2^k ≤ 2^l := by
  calc
    2*2^k = 2^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 2^l := Nat.pow_le_pow_right (by decide) (by omega)

theorem quantize_normalized_monotone (n₁ d₁ k₁ n₂ d₂ k₂ : Nat)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hn : n₁*d₂ ≤ n₂*d₁)
    (hu₁ : n₁ < (2^53*2^k₁)*d₁) (hu₂ : n₂ < (2^53*2^k₂)*d₂)
    (hl₁ : 0 < k₁ → (2^52*2^k₁)*d₁ ≤ n₁)
    (hl₂ : 0 < k₂ → (2^52*2^k₂)*d₂ ≤ n₂) :
    quantizeKey n₁ d₁ k₁ ≤ quantizeKey n₂ d₂ k₂ := by
  have hdu₁ := Nat.mul_pos hd₁ (Nat.two_pow_pos k₁)
  have hdu₂ := Nat.mul_pos hd₂ (Nat.two_pow_pos k₂)
  have hq₁ : rq n₁ (d₁*2^k₁) ≤ 2^53 := by
    apply rq_upper_bound _ _ _ hdu₁
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hu₁
  rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · have hq₂ : 2^52 ≤ rq n₂ (d₂*2^k₂) := by
      apply rq_lower_bound _ _ _ hdu₂
      have hh := hl₂ (by omega)
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
    unfold quantizeKey
    calc
      _ ≤ 2^53*2^k₁ := Nat.mul_le_mul_right _ hq₁
      _ = 2^52*(2*2^k₁) := by rw [← Nat.mul_assoc]
      _ ≤ 2^52*2^k₂ := Nat.mul_le_mul_left _ (dyadic_grid_gap _ _ hlt)
      _ ≤ _ := Nat.mul_le_mul_right _ hq₂
  · subst k₂
    have hc : n₁*(d₂*2^k₁) ≤ n₂*(d₁*2^k₁) := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (2^k₁) hn
    exact Nat.mul_le_mul_right _ (rq_rational_monotone _ _ _ _ hdu₁ hdu₂ hc)
  · have hgap : 2^53*2^k₂ ≤ 2^52*2^k₁ := by
      calc
        _ = 2^52*(2*2^k₂) := by rw [← Nat.mul_assoc]
        _ ≤ _ := Nat.mul_le_mul_left _ (dyadic_grid_gap _ _ hgt)
    have hbound := Nat.mul_le_mul_right d₂ hgap
    have htransfer := cross_threshold_le n₁ n₂ d₁ d₂ (2^52*2^k₁) hd₁ hn (hl₁ (by omega))
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans hbound htransfer)) hu₂)

def quantizeNat (n : Nat) : Nat := quantizeKey n 1 (n.log2-52)

theorem quantize_nat_bounds (n : Nat) :
    n < 2^53*2^(n.log2-52) ∧
    (0 < n.log2-52 → 2^52*2^(n.log2-52) ≤ n) := by
  by_cases hn : n = 0
  · subst n
    decide
  by_cases hl : 52 ≤ n.log2
  · have hu : 2^53*2^(n.log2-52) = 2^(n.log2+1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hd : 2^52*2^(n.log2-52) = 2^n.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    exact ⟨by rw [hu]; exact Nat.lt_log2_self,
      fun _ => by rw [hd]; exact Nat.log2_self_le hn⟩
  · have hk : n.log2-52 = 0 := by omega
    have hs : n < 2^52 := (Nat.log2_lt hn).mp (by omega)
    rw [hk]
    simp only [Nat.pow_zero, Nat.mul_one]
    constructor <;> omega

theorem quantize_nat_monotone (n m : Nat) (hnm : n ≤ m) :
    quantizeNat n ≤ quantizeNat m := by
  obtain ⟨hu₁, hl₁⟩ := quantize_nat_bounds n
  obtain ⟨hu₂, hl₂⟩ := quantize_nat_bounds m
  apply quantize_normalized_monotone n 1 (n.log2-52) m 1 (m.log2-52)
    (by decide) (by decide)
  · simpa only [Nat.mul_one] using hnm
  · simpa only [Nat.mul_one] using hu₁
  · simpa only [Nat.mul_one] using hu₂
  · simpa only [Nat.mul_one] using hl₁
  · simpa only [Nat.mul_one] using hl₂

def magKey64 (x : F64) : Nat :=
  (F64.fraction x + if F64.exponentField x == 0 then 0 else 2^52) *
    2^(F64.exponentField x-1)

def key64 (x : F64) : Int :=
  if F64.signbit x then -(magKey64 x : Int) else (magKey64 x : Int)

theorem key64_rat (x : F64) (hx : F64.isfinite x = true) :
    (F64.toRat x).1 * ((2^1074 : Nat) : Int) =
      key64 x * ((F64.toRat x).2 : Int) := by
  let E := F64.toBits x / 2^52 % 2048
  let M := F64.toBits x % 2^52 + 2^52
  have he : E ≤ 2046 := by
    have ht := tb_lt x
    have hh : E ≠ 2047 := by
      simpa only [F64.isfinite, F64.exponentField, bne_iff_ne] using hx
    dsimp only [E] at *
    omega
  by_cases hz : E = 0
  · rw [toRat_subn x hz]
    change F64.toBits x / 2^52 % 2048 = 0 at hz
    simp only [key64, magKey64, F64.fraction, F64.exponentField, hz,
      beq_iff_eq, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero]
  have hb : (F64.exponentField x == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    exact hz
  have hk : key64 x =
      if F64.signbit x then -((M*2^(E-1) : Nat) : Int)
      else ((M*2^(E-1) : Nat) : Int) := by
    simp only [key64, magKey64, hb, Bool.false_eq_true, ↓reduceIte]
    rfl
  by_cases hs : E ≤ 1074
  · have hp : 2^(E-1)*2^(1075-E) = (2^1074 : Nat) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp' : ((2^(E-1) : Nat) : Int) * ((2^(1075-E) : Nat) : Int) =
        ((2^1074 : Nat) : Int) := by rw [← Int.natCast_mul, hp]
    rw [toRat_norm x (by omega) hs, hk]
    change (if F64.signbit x then -(M : Int) else (M : Int)) * ((2^1074 : Nat) : Int) =
      (if F64.signbit x then -((M*2^(E-1) : Nat) : Int)
        else ((M*2^(E-1) : Nat) : Int)) * ((2^(1075-E) : Nat) : Int)
    cases F64.signbit x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul,
        Int.mul_assoc, hp']
  · have hp : 2^(E-1075)*2^1074 = (2^(E-1) : Nat) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp' : ((2^(E-1075) : Nat) : Int) * ((2^1074 : Nat) : Int) =
        ((2^(E-1) : Nat) : Int) := by rw [← Int.natCast_mul, hp]
    rw [toRat_big x (by omega) he, hk]
    change ((if F64.signbit x then -(M : Int) else (M : Int)) *
        ((2^(E-1075) : Nat) : Int)) * ((2^1074 : Nat) : Int) =
      (if F64.signbit x then -((M*2^(E-1) : Nat) : Int)
        else ((M*2^(E-1) : Nat) : Int)) * 1
    cases F64.signbit x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul,
        Int.mul_one, Int.mul_assoc, hp']

theorem int_le_cancel_positive {a b c : Int} (hc : 0 < c) :
    a*c ≤ b*c ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact hab
    have hh := Int.mul_le_mul_of_nonneg_right (show b+1 ≤ a by omega) (Int.le_of_lt hc)
    rw [Int.add_mul, Int.one_mul] at hh
    omega
  · intro h
    exact Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hc)

theorem key64_order (x y : F64)
    (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    (F64.toRat x).1 * ((F64.toRat y).2 : Int) ≤
      (F64.toRat y).1 * ((F64.toRat x).2 : Int) ↔ key64 x ≤ key64 y := by
  have hG : (0 : Int) < ((2^1074 : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hd : (0 : Int) <
      ((F64.toRat x).2 : Int) * ((F64.toRat y).2 : Int) :=
    Int.mul_pos (Int.natCast_pos.mpr (toRat_den_pos x hx))
      (Int.natCast_pos.mpr (toRat_den_pos y hy))
  have he₁ : ((F64.toRat x).1 * ((F64.toRat y).2 : Int)) *
      ((2^1074 : Nat) : Int) =
      key64 x * (((F64.toRat x).2 : Int) * ((F64.toRat y).2 : Int)) := by
    rw [Int.mul_right_comm, key64_rat x hx, Int.mul_assoc]
  have he₂ : ((F64.toRat y).1 * ((F64.toRat x).2 : Int)) *
      ((2^1074 : Nat) : Int) =
      key64 y * (((F64.toRat x).2 : Int) * ((F64.toRat y).2 : Int)) := by
    rw [Int.mul_right_comm, key64_rat y hy]
    simp only [Int.mul_assoc, Int.mul_comm]
  calc
    _ ↔ ((F64.toRat x).1 * ((F64.toRat y).2 : Int)) *
          ((2^1074 : Nat) : Int) ≤
        ((F64.toRat y).1 * ((F64.toRat x).2 : Int)) *
          ((2^1074 : Nat) : Int) := (int_le_cancel_positive hG).symm
    _ ↔ key64 x * (((F64.toRat x).2 : Int) * ((F64.toRat y).2 : Int)) ≤
        key64 y * (((F64.toRat x).2 : Int) * ((F64.toRat y).2 : Int)) := by rw [he₁, he₂]
    _ ↔ key64 x ≤ key64 y := int_le_cancel_positive hd

theorem quantize_nat_pow (j : Nat) : quantizeNat (2^j) = 2^j := by
  have hd : 2^(j-52) ∣ (2^j : Nat) := Nat.pow_dvd_pow 2 (by omega)
  unfold quantizeNat quantizeKey
  rw [Nat.log2_two_pow, Nat.one_mul,
    rq_exact _ _ (Nat.two_pow_pos _) (Nat.mod_eq_zero_of_dvd hd)]
  exact Nat.div_mul_cancel hd

def quantizeSigned (t : Int) : Int :=
  if t < 0 then -(quantizeNat t.natAbs : Int) else (quantizeNat t.natAbs : Int)

theorem quantize_signed_monotone (t u : Int) (htu : t ≤ u) :
    quantizeSigned t ≤ quantizeSigned u := by
  cases t with
  | ofNat a =>
    cases u with
    | ofNat b =>
      change (a : Int) ≤ (b : Int) at htu
      have hh := quantize_nat_monotone a b (by omega)
      have hc : (quantizeNat a : Int) ≤ (quantizeNat b : Int) := by omega
      simpa only [quantizeSigned, Int.ofNat_eq_natCast, Int.natAbs_natCast,
        show ¬(a : Int) < 0 by omega, show ¬(b : Int) < 0 by omega, ↓reduceIte] using hc
    | negSucc b =>
      change (a : Int) ≤ Int.negSucc b at htu
      omega
  | negSucc a =>
    cases u with
    | ofNat b => simp [quantizeSigned] <;> omega
    | negSucc b =>
      have hh := quantize_nat_monotone (b+1) (a+1) (by omega)
      have hc : -(quantizeNat (a+1) : Int) ≤ -(quantizeNat (b+1) : Int) := by omega
      simpa [quantizeSigned] using hc

theorem key64_sub (s : Bool) (q : Nat) (hq : q < 2^52) :
    let y := F64.ofBits ((if s then 2^63 else 0)+q)
    F64.isfinite y = true ∧
      key64 y = if s then -(q : Int) else (q : Int) := by
  dsimp only
  have hf :
      F64.toBits (F64.ofBits ((if s then 2^63 else 0)+q)) / 2^52 % 2048 = 0 ∧
      F64.toBits (F64.ofBits ((if s then 2^63 else 0)+q)) % 2^52 = q ∧
      F64.signbit (F64.ofBits ((if s then 2^63 else 0)+q)) = s := by
    simp only [F64.signbit, tb_ofBits]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;>
      constructor <;> try omega
    all_goals constructor <;> try omega
    all_goals simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  constructor
  · simp only [F64.isfinite, F64.exponentField, hf.1]
    decide
  · simp only [key64, magKey64, F64.exponentField, F64.fraction,
      hf.1, hf.2.1, hf.2.2, beq_iff_eq, ↓reduceIte, Nat.zero_sub, Nat.pow_zero,
      Nat.mul_one, Nat.add_zero]

theorem key64_norm (s : Bool) (E M : Nat) (he₀ : 1 ≤ E) (he₁ : E ≤ 2046)
    (hm₀ : 2^52 ≤ M) (hm₁ : M < 2^53) :
    let y := F64.ofBits ((if s then 2^63 else 0)+E*2^52+(M-2^52))
    F64.isfinite y = true ∧
      key64 y = if s then -((M*2^(E-1) : Nat) : Int)
        else ((M*2^(E-1) : Nat) : Int) := by
  obtain ⟨hE, hF, hS, hfin⟩ := ProofMisc.norm_fields s E M he₀ he₁ hm₀ hm₁
  dsimp only
  refine ⟨hfin, ?_⟩
  have hz : ¬E = 0 := by omega
  have hM : M-2^52+2^52 = M := Nat.sub_add_cancel hm₀
  simp only [key64, magKey64, F64.exponentField, F64.fraction, hE, hF, hS,
    beq_iff_eq, hz, ↓reduceIte, hM]

theorem pk_key64 (s : Bool) (q K : Nat) (hq : q ≤ 2^53) (hK : K ≤ 1073)
    (hlo : 0 < K → 2^52 ≤ q) :
    F64.isfinite (pk s q ((K : Int)-1074)) = true ∧
      key64 (pk s q ((K : Int)-1074)) =
        if s then -((q*2^K : Nat) : Int) else ((q*2^K : Nat) : Int) := by
  by_cases hz : q = 0
  · subst q
    simpa only [pk, beq_iff_eq, ↓reduceIte, Nat.zero_mul, Nat.add_zero, F64.zero]
      using key64_sub s 0 (by decide)
  by_cases ht : q = 2^53
  · subst q
    have hp : pk s (2^53) ((K : Int)-1074) =
        F64.ofBits ((if s then 2^63 else 0)+(K+2)*2^52+((2^52 : Nat)-2^52)) := by
      unfold pk
      rw [ite_f (by decide : ¬((2^53 : Nat) == 0) = true)]
      simp only [show (2^53 : Nat) ≥ 2^53 by decide, ↓reduceIte,
        show (2^53 : Nat) / 2 = 2^52 by decide]
      have he : (K : Int)-1074+1+1075 = (K : Int)+2 := by omega
      rw [he, ite_f (by omega : ¬((K : Int)+2 ≥ 2047)),
        ite_f (by decide : ¬((2^52 : Nat) < 2^52)),
        show ((K : Int)+2).toNat = K+2 by omega, ← Nat.add_assoc]
    rw [hp]
    have hk := key64_norm s (K+2) (2^52) (by omega) (by omega) (by decide) (by decide)
    have hh : 2^52*2^(K+2-1) = (2^53 : Nat)*2^K := by
      rw [show K+2-1 = K+1 by omega, Nat.pow_succ 2 K, ← Nat.mul_assoc,
        Nat.mul_right_comm (2^52) (2^K) 2, show (2^52 : Nat)*2 = 2^53 by decide]
    simpa only [hh] using hk
  by_cases hl : 2^52 ≤ q
  · rw [pk_norm s q ((K : Int)-1074) hl (by omega) (by omega) (by omega),
      show ((K : Int)-1074+1075).toNat = K+1 by omega]
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using
      key64_norm s (K+1) q (by omega) (by omega) hl (by omega)
  · have hzero : K = 0 := by
      by_cases hh : 0 < K
      · have hb := hlo hh
        omega
      · omega
    subst K
    rw [show ((0 : Nat) : Int)-1074 = -1074 by decide, pk_sub s q (by omega) (by omega)]
    simpa only [Nat.pow_zero, Nat.mul_one] using key64_sub s q (by omega)

theorem rq_cross_eq (a b c d : Nat) (hb : 0 < b) (hd : 0 < d)
    (h : a*d = c*b) : rq a b = rq c d := by
  apply Nat.le_antisymm
  · exact rq_rational_monotone _ _ _ _ hb hd (Nat.le_of_eq h)
  · exact rq_rational_monotone _ _ _ _ hd hb (Nat.le_of_eq h.symm)

theorem roundRat_small_key (n t : Int) (j : Nat) (zs : Bool)
    (hc : n*((2^1074 : Nat) : Int) = t*((2^j : Nat) : Int))
    (ht : t.natAbs < 2^1126) :
    F64.isfinite (F64.roundRat n (2^j) zs) = true ∧
      key64 (F64.roundRat n (2^j) zs) = quantizeSigned t := by
  have hG : (0 : Int) < ((2^1074 : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hD : (0 : Int) < ((2^j : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hd₀ : ¬(2^j == 0) = true := by
    simp only [beq_iff_eq]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  by_cases ht₀ : t = 0
  · have hn : n = 0 :=
      (Int.mul_eq_zero.mp (by simpa only [ht₀, Int.zero_mul] using hc)).resolve_right
        (by omega)
    rw [hn, ht₀, roundRat_eq, ite_f hd₀]
    change F64.isfinite (F64.zero zs) = true ∧ key64 (F64.zero zs) = quantizeSigned 0
    refine ⟨finite_zero zs, ?_⟩
    have hz : key64 (F64.zero zs) = 0 := by cases zs <;> decide
    rw [hz]
    rfl
  have hn : n ≠ 0 := by
    intro hz
    rw [hz, Int.zero_mul] at hc
    have hz' : t = 0 := (Int.mul_eq_zero.mp hc.symm).resolve_right (by omega)
    exact ht₀ hz'
  have hn₀ : ¬(n == 0) = true := by simpa only [beq_iff_eq] using hn
  have hnAbs : 0 < n.natAbs := by omega
  have htAbs : 0 < t.natAbs := by omega
  have ha : n.natAbs*2^1074 = t.natAbs*2^j := by
    have hh := congrArg Int.natAbs hc
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
  have hlogs := congrArg Nat.log2 ha
  rw [log2_mul_pow 1074 hnAbs, log2_mul_pow j htAbs] at hlogs
  have hL : t.natAbs.log2 ≤ 1125 := by
    have hh := (Nat.log2_lt (by omega : t.natAbs ≠ 0)).mpr ht
    omega
  let K := t.natAbs.log2-52
  have hK : K ≤ 1073 := by dsimp only [K]; omega
  have hfl : fl2 n.natAbs (2^j) = (t.natAbs.log2 : Int)-1074 := by
    have hh := fl2_pow n.natAbs 0 j hnAbs
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hh
    rw [hh]
    omega
  have hk : max (((t.natAbs.log2 : Int)-1074)-52) (-1074) = (K : Int)-1074 := by
    dsimp only [K]
    omega
  have hround : F64.roundRat n (2^j) zs =
      pk (decide (n < 0)) (rq (n.natAbs*2^(1074-K)) (2^j)) ((K : Int)-1074) := by
    rw [roundRat_eq, ite_f hd₀, ite_f hn₀, hfl, ite_f (by omega), ite_f (by omega),
      hk, ite_f (by omega),
      show (-((K : Int)-1074)).toNat = 1074-K by omega]
  have hscale : (n.natAbs*2^(1074-K))*2^K = t.natAbs*2^j := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show 1074-K+K = 1074 by omega]
    exact ha
  have hq := rq_cross_eq (n.natAbs*2^(1074-K)) (2^j) t.natAbs (2^K)
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) hscale
  have hs : decide (n < 0) = decide (t < 0) := by
    apply decide_eq_decide.mpr
    constructor
    · intro hh
      have hp : t*((2^j : Nat) : Int) < 0*((2^j : Nat) : Int) := by
        rw [Int.zero_mul, ← hc]
        exact Int.mul_neg_of_neg_of_pos hh hG
      exact Int.lt_of_mul_lt_mul_right hp (Int.le_of_lt hD)
    · intro hh
      have hp : n*((2^1074 : Nat) : Int) < 0*((2^1074 : Nat) : Int) := by
        rw [Int.zero_mul, hc]
        exact Int.mul_neg_of_neg_of_pos hh hD
      exact Int.lt_of_mul_lt_mul_right hp (Int.le_of_lt hG)
  have hu : rq t.natAbs (2^K) ≤ 2^53 :=
    rq_upper_bound _ _ _ (Nat.two_pow_pos _) (quantize_nat_bounds _).1
  have hl : 0 < K → 2^52 ≤ rq t.natAbs (2^K) := by
    intro hh
    exact rq_lower_bound _ _ _ (Nat.two_pow_pos _) ((quantize_nat_bounds _).2 hh)
  rw [hround, hq, hs]
  obtain ⟨hfin, hkey⟩ := pk_key64 (decide (t < 0)) (rq t.natAbs (2^K)) K hu hK hl
  refine ⟨hfin, ?_⟩
  simpa only [quantizeSigned, quantizeNat, quantizeKey, Nat.one_mul,
    decide_eq_true_eq, K] using hkey

theorem quantize_signed_abs (t : Int) :
    (quantizeSigned t).natAbs = quantizeNat t.natAbs := by
  unfold quantizeSigned
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

theorem quantize_nat_dyadic (a j : Nat) (ha : a < 2^53) :
    quantizeNat (a*2^j) = a*2^j := by
  by_cases hz : a = 0
  · subst a
    rw [Nat.zero_mul]
    rfl
  have hL : a.log2 ≤ 52 := by
    have hh := (Nat.log2_lt hz).mpr ha
    omega
  let K := (a*2^j).log2-52
  have hK : K ≤ j := by
    dsimp only [K]
    rw [log2_mul_pow j (by omega)]
    omega
  have hp : 2^j = (2^K : Nat)*2^(j-K) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hd : 2^K ∣ a*2^j :=
    ⟨a*2^(j-K), by rw [hp]; simp only [Nat.mul_left_comm]⟩
  change rq (a*2^j) (1*2^K)*2^K = a*2^j
  rw [Nat.one_mul, rq_exact _ _ (Nat.two_pow_pos _) (Nat.mod_eq_zero_of_dvd hd)]
  exact Nat.div_mul_cancel hd

theorem quantize_signed_bound (t : Int) (j : Nat) (ht : t.natAbs ≤ 2^j) :
    (quantizeSigned t).natAbs ≤ 2^j := by
  rw [quantize_signed_abs]
  calc
    _ ≤ quantizeNat (2^j) := quantize_nat_monotone _ _ ht
    _ = _ := quantize_nat_pow j

theorem add_small_key (x y : F64) (hx : F64.isfinite x = true)
    (hy : F64.isfinite y = true) (hs : (key64 x+key64 y).natAbs < 2^1126) :
    F64.isfinite (F64.add x y) = true ∧
      key64 (F64.add x y) = quantizeSigned (key64 x+key64 y) := by
  obtain ⟨u, _, hdx⟩ := ProofMisc.finite_den_pow x hx
  obtain ⟨v, _, hdy⟩ := ProofMisc.finite_den_pow y hy
  have hcross :
      ((F64.toRat x).1*((F64.toRat y).2 : Int) +
        (F64.toRat y).1*((F64.toRat x).2 : Int)) * ((2^1074 : Nat) : Int) =
      (key64 x+key64 y) * (((F64.toRat x).2*(F64.toRat y).2 : Nat) : Int) := by
    rw [Int.add_mul]
    rw [Int.mul_right_comm (F64.toRat x).1, Int.mul_right_comm (F64.toRat y).1,
      key64_rat x hx, key64_rat y hy, Int.natCast_mul, Int.add_mul]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hdx, hdy, ← Nat.pow_add] at hcross
  rw [add_finite x y hx hy, hdx, hdy, ← Nat.pow_add]
  exact roundRat_small_key _ _ _ _ hcross hs

def quarterDownKey : Int := ((2^1072 : Nat) : Int)-((2^1021 : Nat) : Int)
def quarterUpKey : Int := ((2^1072 : Nat) : Int)+((2^1021 : Nat) : Int)

def tiesUpKey (t : Int) : Int :=
  quantizeSigned (quantizeSigned (t+quarterDownKey)+quarterUpKey)

theorem tiesUp_key_monotone (t u : Int) (htu : t ≤ u) :
    tiesUpKey t ≤ tiesUpKey u := by
  unfold tiesUpKey
  apply quantize_signed_monotone
  have hh := quantize_signed_monotone (t+quarterDownKey) (u+quarterDownKey) (by omega)
  omega

theorem tiesUp_key_small (x : F64) (hx : F64.isfinite x = true)
    (hs : (key64 x).natAbs ≤ 2^1125) :
    F64.isfinite (tiesUpSum x) = true ∧ key64 (tiesUpSum x) = tiesUpKey (key64 x) := by
  let c₁ := F64.ofBits 0x3fcffffffffffffc
  let c₂ := F64.ofBits 0x3fd0000000000002
  have hc₁ : F64.isfinite c₁ = true := by decide
  have hc₂ : F64.isfinite c₂ = true := by decide
  have hk₁ : key64 c₁ = quarterDownKey := by decide
  have hk₂ : key64 c₂ = quarterUpKey := by decide
  have hs₁ : (key64 x+key64 c₁).natAbs ≤ 3*2^1124 := by
    rw [hk₁]
    dsimp only [quarterDownKey]
    omega
  have hlt₁ : (key64 x+key64 c₁).natAbs < 2^1126 := by omega
  obtain ⟨hfin₁, hkey₁⟩ := add_small_key x c₁ hx hc₁ hlt₁
  have hb₁ : (key64 (F64.add x c₁)).natAbs ≤ 3*2^1124 := by
    rw [hkey₁, quantize_signed_abs]
    calc
      _ ≤ quantizeNat (3*2^1124) := quantize_nat_monotone _ _ hs₁
      _ = _ := quantize_nat_dyadic 3 1124 (by decide)
  have hs₂ : (key64 (F64.add x c₁)+key64 c₂).natAbs < 2^1126 := by
    rw [hk₂]
    dsimp only [quarterUpKey]
    omega
  obtain ⟨hfin₂, hkey₂⟩ := add_small_key (F64.add x c₁) c₂ hfin₁ hc₂ hs₂
  change F64.isfinite (F64.add (F64.add x c₁) c₂) = true ∧
    key64 (F64.add (F64.add x c₁) c₂) = tiesUpKey (key64 x)
  refine ⟨hfin₂, ?_⟩
  rw [hkey₂, hkey₁, hk₁, hk₂]
  rfl

theorem int_cross_div (n t d G : Int) (hd : 0 < d) (hG : 0 < G)
    (h : n*G = t*d) : n/d = t/G := by
  calc
    _ = (n*G)/(d*G) := (Int.mul_ediv_mul_of_pos_left n d hG).symm
    _ = (t*d)/(G*d) := by rw [h, Int.mul_comm d G]
    _ = _ := Int.mul_ediv_mul_of_pos_left t G hd

theorem key64_floor (x : F64) (hx : F64.isfinite x = true) :
    (F64.toRat x).1 / ((F64.toRat x).2 : Int) =
      key64 x / ((2^1074 : Nat) : Int) :=
  int_cross_div _ _ _ _ (Int.natCast_pos.mpr (toRat_den_pos x hx))
    (Int.natCast_pos.mpr (Nat.two_pow_pos _)) (key64_rat x hx)

theorem exactRound_tiesUp_key (x : F64) (hx : F64.isfinite x = true) :
    exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp =
      (2*key64 x+((2^1074 : Nat) : Int))/(2*((2^1074 : Nat) : Int)) := by
  have hd : (0 : Int) < ((F64.toRat x).2 : Int) :=
    Int.natCast_pos.mpr (toRat_den_pos x hx)
  have hG : (0 : Int) < ((2^1074 : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hh :
      (2*(F64.toRat x).1+((F64.toRat x).2 : Int))*((2^1074 : Nat) : Int) =
      (2*key64 x+((2^1074 : Nat) : Int))*((F64.toRat x).2 : Int) := by
    rw [Int.add_mul, Int.mul_assoc, key64_rat x hx, Int.add_mul]
    simp only [Int.mul_comm, Int.mul_left_comm]
  have hc :
      (2*(F64.toRat x).1+((F64.toRat x).2 : Int))*(2*((2^1074 : Nat) : Int)) =
      (2*key64 x+((2^1074 : Nat) : Int))*(2*((F64.toRat x).2 : Int)) := by
    have hm := congrArg (fun z : Int => z*2) hh
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hm
  rw [exactRound_tiesUp_floor _ _ (toRat_den_pos x hx)]
  exact int_cross_div _ _ _ _ (by omega) (by omega) hc

theorem key64_abs (x : F64) : (key64 x).natAbs = magKey64 x := by
  unfold key64
  cases F64.signbit x <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Int.natAbs_neg, Int.natAbs_natCast]

theorem magKey64_small_bound (x : F64)
    (he : F64.toBits x / 2^52 % 2048 ≤ 1021) :
    magKey64 x ≤ (2^53-1)*2^1020 := by
  have hf : F64.toBits x % 2^52 < 2^52 := Nat.mod_lt _ (by decide)
  unfold magKey64
  by_cases hz : F64.exponentField x = 0
  · simp only [hz, beq_iff_eq, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero, F64.fraction]
    omega
  · have hp : 2^(F64.exponentField x-1) ≤ (2^1020 : Nat) :=
      Nat.pow_le_pow_right (by decide) (by change F64.toBits x / 2^52 % 2048-1 ≤ 1020; omega)
    simp only [beq_iff_eq, hz, ↓reduceIte, F64.fraction]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ hp)

theorem tiesUp_key_under_half :
    tiesUpKey (-((2^1073 : Nat) : Int)) = 0 ∧
      tiesUpKey (((2^53-1)*2^1020 : Nat) : Int) =
        ((2^1074 : Nat) : Int)-((2^1021 : Nat) : Int) := by decide

theorem tiesUp_below_half_exact (x : F64) (hx : F64.isfinite x = true)
    (he : F64.toBits x / 2^52 % 2048 ≤ 1021) :
    F64.isfinite (roundF x .NearestTiesUp) = true ∧
      F64.signbit (roundF x .NearestTiesUp) = F64.signbit x ∧
        (F64.toRat (roundF x .NearestTiesUp)).1 =
          exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp *
            ((F64.toRat (roundF x .NearestTiesUp)).2 : Int) := by
  have hm := magKey64_small_bound x he
  have ha : (key64 x).natAbs ≤ (2^53-1)*2^1020 := by rwa [key64_abs]
  obtain ⟨hfin, hkey⟩ := tiesUp_key_small x hx (by omega)
  have hlo := tiesUp_key_monotone (-((2^1073 : Nat) : Int)) (key64 x) (by omega)
  have hhi := tiesUp_key_monotone (key64 x) (((2^53-1)*2^1020 : Nat) : Int) (by omega)
  rw [tiesUp_key_under_half.1] at hlo
  rw [tiesUp_key_under_half.2] at hhi
  have hfloor : (F64.toRat (tiesUpSum x)).1 /
      ((F64.toRat (tiesUpSum x)).2 : Int) = 0 := by
    rw [key64_floor _ hfin, hkey]
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have hexact : exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp = 0 := by
    rw [exactRound_tiesUp_key x hx]
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  exact tiesUp_exact_of_sum_floor x hx hfin (by rw [hfloor, hexact])

theorem magKey64_eq (x : F64) :
    magKey64 x = Promotion.magKey Promotion.double (F64.toBits x % 2^63) := by
  have hf : (F64.toBits x % 2^63) % 2^52 = F64.toBits x % 2^52 := by omega
  have he : (F64.toBits x % 2^63) / 2^52 = F64.toBits x / 2^52 % 2048 := by omega
  change (F64.toBits x % 2^52 +
      if F64.toBits x / 2^52 % 2048 == 0 then 0 else 2^52) *
      2^(F64.toBits x / 2^52 % 2048-1) =
    ((F64.toBits x % 2^63) % 2^52 +
      if (F64.toBits x % 2^63) / 2^52 = 0 then 0 else 2^52) *
      2^((F64.toBits x % 2^63) / 2^52-1)
  rw [hf, he]
  simp only [beq_iff_eq]

def code64 (x : F64) : Int :=
  if F64.signbit x then -((F64.toBits x % 2^63 : Nat) : Int)
  else ((F64.toBits x % 2^63 : Nat) : Int)

theorem key64_code_order (x y : F64) : key64 x ≤ key64 y ↔ code64 x ≤ code64 y := by
  unfold key64 code64
  rw [magKey64_eq x, magKey64_eq y]
  generalize F64.toBits x % 2^63 = a
  generalize F64.toBits y % 2^63 = b
  generalize F64.signbit x = s
  generalize F64.signbit y = t
  have pa := Promotion.magKey_cases Promotion.double a
  have pb := Promotion.magKey_cases Promotion.double b
  rcases Nat.lt_trichotomy a b with h | h | h
  · have hh := Promotion.magKey_strictMono Promotion.double h
    cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · subst b
    cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · have hh := Promotion.magKey_strictMono Promotion.double h
    cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem key64_gap_of_code (H P x : F64) (hp : code64 P = code64 H-1)
    (hx : key64 x < key64 H) : key64 x ≤ key64 P := by
  have hh : code64 x < code64 H := by
    by_cases hc : code64 H ≤ code64 x
    · have hb := (key64_code_order H x).mpr hc
      omega
    · omega
  exact (key64_code_order x P).mpr (by omega)

theorem code64_norm (s : Bool) (E M : Nat) (he₀ : 1 ≤ E) (he₁ : E ≤ 2046)
    (hm₀ : 2^52 ≤ M) (hm₁ : M < 2^53) :
    code64 (F64.ofBits ((if s then 2^63 else 0)+E*2^52+(M-2^52))) =
      if s then -((E*2^52+(M-2^52) : Nat) : Int)
        else ((E*2^52+(M-2^52) : Nat) : Int) := by
  have hS := (ProofMisc.norm_fields s E M he₀ he₁ hm₀ hm₁).2.2.1
  have hbits :
      F64.toBits (F64.ofBits ((if s then 2^63 else 0)+E*2^52+(M-2^52))) % 2^63 =
        E*2^52+(M-2^52) := by
    rw [tb_ofBits]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  simp only [code64, hS, hbits]

theorem normal_key_gap (s : Bool) (E M : Nat) (he₀ : 1 ≤ E) (he₁ : E ≤ 2046)
    (hm₀ : 2^52 < M) (hm₁ : M+1 < 2^53) (x : F64)
    (hx : key64 x <
      (if s then -((M*2^(E-1) : Nat) : Int) else ((M*2^(E-1) : Nat) : Int))) :
    key64 x ≤
      (if s then -((M*2^(E-1) : Nat) : Int) else ((M*2^(E-1) : Nat) : Int)) -
        ((2^(E-1) : Nat) : Int) := by
  let N := if s then M+1 else M-1
  let H := F64.ofBits ((if s then 2^63 else 0)+E*2^52+(M-2^52))
  let P := F64.ofBits ((if s then 2^63 else 0)+E*2^52+(N-2^52))
  have hn₀ : 2^52 ≤ N := by cases s <;> simp only [N, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hn₁ : N < 2^53 := by cases s <;> simp only [N, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hH := (key64_norm s E M he₀ he₁ (by omega) (by omega)).2
  have hP := (key64_norm s E N he₀ he₁ hn₀ hn₁).2
  have hCH := code64_norm s E M he₀ he₁ (by omega) (by omega)
  have hCP := code64_norm s E N he₀ he₁ hn₀ hn₁
  have hc : code64 P = code64 H-1 := by
    rw [hCP, hCH]
    cases s <;> simp only [N, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hpkey : key64 P =
      (if s then -((M*2^(E-1) : Nat) : Int) else ((M*2^(E-1) : Nat) : Int)) -
        ((2^(E-1) : Nat) : Int) := by
    rw [hP]
    cases s <;> simp only [N, Bool.false_eq_true, ↓reduceIte, Int.natCast_mul,
      Int.natCast_add, Int.natCast_sub (by omega : 1 ≤ M), Int.add_mul, Int.sub_mul,
      Int.neg_add]
    all_goals omega
  have hh : key64 x < key64 H := by rw [hH]; exact hx
  have hg := key64_gap_of_code H P x hc hh
  rwa [hpkey] at hg

theorem quantize_signed_ofNat (n : Nat) :
    quantizeSigned (n : Int) = (quantizeNat n : Int) := by
  unfold quantizeSigned
  rw [ite_f (by omega : ¬(n : Int) < 0), Int.natAbs_natCast]

theorem quantize_signed_neg (t : Int) :
    quantizeSigned (-t) = -quantizeSigned t := by
  by_cases hz : t = 0
  · subst t
    rfl
  by_cases hn : t < 0
  · simp only [quantizeSigned, hn, show ¬ -t < 0 by omega, ↓reduceIte,
      Int.natAbs_neg, Int.neg_neg]
  · simp only [quantizeSigned, hn, show -t < 0 by omega, ↓reduceIte,
      Int.natAbs_neg]

theorem quantize_signed_int_dyadic (z : Int) (j : Nat) (hz : z.natAbs < 2^53) :
    quantizeSigned (z*((2^j : Nat) : Int)) = z*((2^j : Nat) : Int) := by
  cases z with
  | ofNat a =>
    change a < 2^53 at hz
    change quantizeSigned ((a : Int)*((2^j : Nat) : Int)) = (a : Int)*((2^j : Nat) : Int)
    rw [← Int.natCast_mul, quantize_signed_ofNat, quantize_nat_dyadic a j hz]
  | negSucc a =>
    have he : Int.negSucc a = -((a+1 : Nat) : Int) := by omega
    rw [he] at hz ⊢
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hz
    rw [Int.neg_mul, quantize_signed_neg, ← Int.natCast_mul, quantize_signed_ofNat,
      quantize_nat_dyadic (a+1) j hz]

theorem quantize_nat_near_plus (q K r : Nat) (hq₀ : 2^52 ≤ q) (hq₁ : q < 2^53)
    (hr : 2*r < 2^K) : quantizeNat (q*2^K+r) = q*2^K := by
  have hp₀ : (2^52 : Nat)*2^K = 2^(K+52) := by
    rw [← Nat.pow_add, Nat.add_comm]
  have hp₁ : (2^53 : Nat)*2^K = 2^(K+52+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hl := Nat.mul_le_mul_right (2^K) hq₀
  have hu := Nat.mul_le_mul_right (2^K) (show q+1 ≤ 2^53 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hu
  have hlog : (q*2^K+r).log2 = K+52 := log2_of_interval _ _
    (by rw [← hp₀]; omega) (by rw [← hp₁]; omega)
  unfold quantizeNat quantizeKey
  rw [hlog, show K+52-52 = K by omega, Nat.one_mul,
    rq_near_upper q (2^K) r (Nat.two_pow_pos _) hr]

theorem quantize_nat_near_minus (q K r : Nat) (hq₀ : 2^52 < q) (hq₁ : q ≤ 2^53)
    (hr₀ : 0 < r) (hr : 2*r < 2^K) : quantizeNat (q*2^K-r) = q*2^K := by
  have hp₀ : (2^52 : Nat)*2^K = 2^(K+52) := by
    rw [← Nat.pow_add, Nat.add_comm]
  have hp₁ : (2^53 : Nat)*2^K = 2^(K+52+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hl := Nat.mul_le_mul_right (2^K) (show 2^52+1 ≤ q by omega)
  rw [Nat.add_mul, Nat.one_mul] at hl
  have hu := Nat.mul_le_mul_right (2^K) hq₁
  have hlog : (q*2^K-r).log2 = K+52 := log2_of_interval _ _
    (by rw [← hp₀]; omega) (by rw [← hp₁]; omega)
  unfold quantizeNat quantizeKey
  rw [hlog, show K+52-52 = K by omega, Nat.one_mul,
    rq_near_lower q (2^K) r (by omega) (Nat.two_pow_pos _) hr]

theorem quantize_epsilon_plus (q K : Nat) (hq₀ : 2^52 ≤ q) (hq₁ : q < 2^53)
    (hr : 2*(2^1021 : Nat) < 2^K) :
    quantizeSigned (((q*2^K : Nat) : Int)+((2^1021 : Nat) : Int)) =
      ((q*2^K : Nat) : Int) := by
  rw [← Int.natCast_add, quantize_signed_ofNat, quantize_nat_near_plus q K _ hq₀ hq₁ hr]

theorem quantize_epsilon_minus (q K : Nat) (hq₀ : 2^52 < q) (hq₁ : q ≤ 2^53)
    (hr : 2*(2^1021 : Nat) < 2^K) :
    quantizeSigned (((q*2^K : Nat) : Int)-((2^1021 : Nat) : Int)) =
      ((q*2^K : Nat) : Int) := by
  have hh := Nat.mul_le_mul_right (2^K) (show 1 ≤ q by omega)
  simp only [Nat.one_mul] at hh
  have hb : 2^1021 ≤ q*2^K := by omega
  rw [← Int.natCast_sub hb, quantize_signed_ofNat,
    quantize_nat_near_minus q K _ hq₀ hq₁ (Nat.two_pow_pos _) hr]

def HalfBoundary (h : Int) : Prop :=
  ∃ g : Nat, 0 < g ∧
    (∀ x : F64, key64 x < h → key64 x ≤ h-(g : Int)) ∧
    h+((2^1073 : Nat) : Int) ≤ tiesUpKey h ∧
    tiesUpKey (h-(g : Int)) < h+((2^1073 : Nat) : Int)

theorem half_boundary_bits (h : Int) (g b p : Nat) (hg : 0 < g)
    (hH : key64 (F64.ofBits b) = h) (hP : key64 (F64.ofBits p) = h-(g : Int))
    (hc : code64 (F64.ofBits p) = code64 (F64.ofBits b)-1)
    (hlo : h+((2^1073 : Nat) : Int) ≤ tiesUpKey h)
    (hhi : tiesUpKey (h-(g : Int)) < h+((2^1073 : Nat) : Int)) :
    HalfBoundary h := by
  refine ⟨g, hg, ?_, hlo, hhi⟩
  intro x hx
  have hh : key64 x < key64 (F64.ofBits b) := by rwa [hH]
  have hp := key64_gap_of_code (F64.ofBits b) (F64.ofBits p) x hc hh
  rwa [hP] at hp

theorem half_boundary_small (s : Bool) (q : Nat)
    (hq : q = 1 ∨ q = 3 ∨ q = 2^52+1) :
    HalfBoundary (if s then -((q*2^1073 : Nat) : Int) else ((q*2^1073 : Nat) : Int)) := by
  rcases hq with h | h | h <;> subst q <;> cases s
  · apply half_boundary_bits _ (2^1020) 0x3fe0000000000000 0x3fdfffffffffffff <;> decide
  · apply half_boundary_bits _ (2^1021) 0xbfe0000000000000 0xbfe0000000000001 <;> decide
  · apply half_boundary_bits _ (2^1022) 0x3ff8000000000000 0x3ff7ffffffffffff <;> decide
  · apply half_boundary_bits _ (2^1022) 0xbff8000000000000 0xbff8000000000001 <;> decide
  · apply half_boundary_bits _ (2^1073) 0x4320000000000001 0x4320000000000000 <;> decide
  · apply half_boundary_bits _ (2^1073) 0xc320000000000001 0xc320000000000002 <;> decide

theorem quantize_epsilon_near (z : Int) (K : Nat) (hz₀ : 2^52 < z.natAbs)
    (hz₁ : z.natAbs < 2^53) (hr : 2*(2^1021 : Nat) < 2^K) :
    quantizeSigned (z*((2^K : Nat) : Int)+((2^1021 : Nat) : Int)) =
      z*((2^K : Nat) : Int) ∧
    quantizeSigned (z*((2^K : Nat) : Int)-((2^1021 : Nat) : Int)) =
      z*((2^K : Nat) : Int) := by
  cases z with
  | ofNat a =>
    change 2^52 < a at hz₀
    change a < 2^53 at hz₁
    constructor
    · simpa only [Int.ofNat_eq_natCast, Int.natCast_mul] using
        quantize_epsilon_plus a K (by omega) hz₁ hr
    · simpa only [Int.ofNat_eq_natCast, Int.natCast_mul] using
        quantize_epsilon_minus a K hz₀ (by omega) hr
  | negSucc a =>
    have he : Int.negSucc a = -((a+1 : Nat) : Int) := by omega
    rw [he] at hz₀ hz₁ ⊢
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hz₀ hz₁
    constructor
    · calc
        _ = quantizeSigned (-(((a+1)*2^K : Nat) : Int)+((2^1021 : Nat) : Int)) := by
          rw [Int.natCast_mul, Int.neg_mul]
        _ = quantizeSigned (-((((a+1)*2^K : Nat) : Int)-((2^1021 : Nat) : Int))) := by
          congr 1
          omega
        _ = -quantizeSigned ((((a+1)*2^K : Nat) : Int)-((2^1021 : Nat) : Int)) :=
          quantize_signed_neg _
        _ = -(((a+1)*2^K : Nat) : Int) := by
          rw [quantize_epsilon_minus _ _ hz₀ (by omega) hr]
        _ = _ := by rw [Int.natCast_mul, Int.neg_mul]
    · calc
        _ = quantizeSigned (-(((a+1)*2^K : Nat) : Int)-((2^1021 : Nat) : Int)) := by
          rw [Int.natCast_mul, Int.neg_mul]
        _ = quantizeSigned (-((((a+1)*2^K : Nat) : Int)+((2^1021 : Nat) : Int))) := by
          congr 1
          omega
        _ = -quantizeSigned ((((a+1)*2^K : Nat) : Int)+((2^1021 : Nat) : Int)) :=
          quantize_signed_neg _
        _ = -(((a+1)*2^K : Nat) : Int) := by
          rw [quantize_epsilon_plus _ _ (by omega) hz₁ hr]
        _ = _ := by rw [Int.natCast_mul, Int.neg_mul]

theorem tiesUp_grid_boundary (z : Int) (a K : Nat)
    (hC : a*2^K = 2^1072) (hr : 2*(2^1021 : Nat) < 2^K)
    (h₁ : 2^52 < (z+(a : Int)).natAbs ∧ (z+(a : Int)).natAbs < 2^53)
    (h₂ : 2^52 < (z+(a : Int)-1).natAbs ∧ (z+(a : Int)-1).natAbs < 2^53)
    (h₃ : 2^52 < (z+2*(a : Int)-1).natAbs ∧ (z+2*(a : Int)-1).natAbs < 2^53)
    (hf : quantizeSigned (z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int)) =
      z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int)) :
    z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int) ≤
        tiesUpKey (z*((2^K : Nat) : Int)) ∧
      tiesUpKey (z*((2^K : Nat) : Int)-((2^K : Nat) : Int)) =
        z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int)-((2^K : Nat) : Int) := by
  let g := ((2^K : Nat) : Int)
  let ε := ((2^1021 : Nat) : Int)
  have hc : (a : Int)*g = ((2^1072 : Nat) : Int) := by
    dsimp only [g]
    rw [← Int.natCast_mul, hC]
  have harg₁ : z*g+quarterDownKey = (z+(a : Int))*g-ε := by
    simp only [quarterDownKey, Int.add_mul, hc]
    omega
  have harg₂ : z*g-g+quarterDownKey = (z+(a : Int)-1)*g-ε := by
    simp only [quarterDownKey, Int.sub_mul, Int.add_mul, Int.one_mul, hc]
    omega
  have harg₃ : (z+(a : Int))*g+quarterUpKey =
      z*g+((2^1073 : Nat) : Int)+ε := by
    simp only [quarterUpKey, Int.add_mul, hc]
    omega
  have harg₄ : (z+(a : Int)-1)*g+quarterUpKey = (z+2*(a : Int)-1)*g+ε := by
    simp only [quarterUpKey, Int.sub_mul, Int.add_mul, Int.one_mul, Int.mul_assoc, hc]
    omega
  have hvalue : (z+2*(a : Int)-1)*g =
      z*g+((2^1073 : Nat) : Int)-g := by
    simp only [Int.sub_mul, Int.add_mul, Int.one_mul, Int.mul_assoc, hc]
    omega
  constructor
  · change z*g+((2^1073 : Nat) : Int) ≤ tiesUpKey (z*g)
    unfold tiesUpKey
    rw [harg₁, (quantize_epsilon_near _ _ h₁.1 h₁.2 hr).2, harg₃]
    have hh := quantize_signed_monotone (z*g+((2^1073 : Nat) : Int))
      (z*g+((2^1073 : Nat) : Int)+ε) (by dsimp only [ε]; omega)
    rwa [hf] at hh
  · change tiesUpKey (z*g-g) = z*g+((2^1073 : Nat) : Int)-g
    unfold tiesUpKey
    rw [harg₂, (quantize_epsilon_near _ _ h₂.1 h₂.2 hr).2, harg₄,
      (quantize_epsilon_near _ _ h₃.1 h₃.2 hr).1, hvalue]

theorem half_boundary_normal (s : Bool) (q : Nat) (hq₀ : 5 ≤ q) (hq₁ : q < 2^52)
    (hqOdd : q%2 = 1) :
    HalfBoundary (if s then -((q*2^1073 : Nat) : Int) else ((q*2^1073 : Nat) : Int)) := by
  let L := q.log2
  have hL₀ : 2 ≤ L := by
    by_cases hh : q.log2 < 2
    · have hb := (Nat.log2_lt (by omega : q ≠ 0)).mp hh
      omega
    · exact Nat.le_of_not_gt hh
  have hL₁ : L ≤ 51 := by
    have hh := (Nat.log2_lt (by omega : q ≠ 0)).mpr hq₁
    omega
  let P := 2^L
  let a := 2^(51-L)
  let K := L+1021
  let M := q*(2*a)
  let z := if s then -(M : Int) else (M : Int)
  let H := if s then -((q*2^1073 : Nat) : Int) else ((q*2^1073 : Nat) : Int)
  have ha : 0 < a := Nat.two_pow_pos _
  have hK : 1023 ≤ K ∧ K ≤ 1072 := by dsimp only [K]; omega
  have hP₀ : P ≤ q := Nat.log2_self_le (by omega)
  have hP₁ : q < P*2 := by
    have hh : q < 2^(L+1) := Nat.lt_log2_self
    rwa [Nat.pow_succ 2 L] at hh
  have hPtwo : P = 2^(L-1)*2 := by
    dsimp only [P]
    rw [← Nat.pow_succ 2 (L-1)]
    congr 1
    omega
  have hPparity : P%2 = 0 := by rw [hPtwo]; omega
  have hqLow : P+1 ≤ q := by omega
  have hqHigh : q+1 ≤ 2*P := by omega
  have haPow : 2*a = 2^(52-L) := by
    dsimp only [a]
    rw [show 52-L = (51-L)+1 by omega, Nat.pow_succ 2 (51-L),
      Nat.mul_comm 2 (2^(51-L))]
  have hPscale : P*(2*a) = 2^52 := by
    dsimp only [P]
    rw [haPow, ← Nat.pow_add]
    congr 1
    omega
  have hPscale₂ : (2*P)*(2*a) = 2^53 := by
    rw [Nat.mul_assoc, hPscale] <;> decide
  have hM₀ : 2^52+2*a ≤ M := by
    have hh := Nat.mul_le_mul_right (2*a) hqLow
    rwa [Nat.add_mul, Nat.one_mul, hPscale] at hh
  have hM₁ : M+2*a ≤ 2^53 := by
    have hh := Nat.mul_le_mul_right (2*a) hqHigh
    rwa [Nat.add_mul, Nat.one_mul, hPscale₂] at hh
  have hC : a*2^K = 2^1072 := by
    dsimp only [a, K]
    rw [← Nat.pow_add]
    congr 1
    omega
  have htwoC : (2*a)*2^K = 2^1073 := by
    rw [Nat.mul_assoc, hC] <;> decide
  have hMg : M*2^K = q*2^1073 := by
    dsimp only [M]
    rw [Nat.mul_assoc, htwoC]
  have hr : 2*(2^1021 : Nat) < 2^K := by
    have hh : (2^1023 : Nat) ≤ 2^K := Nat.pow_le_pow_right (by decide) hK.1
    omega
  have hz : z*((2^K : Nat) : Int) = H := by
    cases s <;> simp only [z, H, Bool.false_eq_true, ↓reduceIte, Int.neg_mul,
      ← Int.natCast_mul, hMg]
  let n : Int := if s then -((q/2 : Nat) : Int) else ((q/2+1 : Nat) : Int)
  have hqDiv := Nat.div_add_mod q 2
  have hn : n.natAbs < 2^53 := by
    cases s <;> simp only [n, Bool.false_eq_true, ↓reduceIte,
      Int.natAbs_neg, Int.natAbs_natCast] <;> omega
  have hN : H+((2^1073 : Nat) : Int) = n*((2^1074 : Nat) : Int) := by
    cases s <;> simp only [H, n, Bool.false_eq_true, ↓reduceIte,
      Int.natCast_mul, Int.natCast_add] <;> omega
  have hf : quantizeSigned (z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int)) =
      z*((2^K : Nat) : Int)+((2^1073 : Nat) : Int) := by
    rw [hz, hN]
    exact quantize_signed_int_dyadic n 1074 hn
  have h₁ : 2^52 < (z+(a : Int)).natAbs ∧ (z+(a : Int)).natAbs < 2^53 := by
    cases s <;> simp only [z, Bool.false_eq_true, ↓reduceIte] <;> omega
  have h₂ : 2^52 < (z+(a : Int)-1).natAbs ∧ (z+(a : Int)-1).natAbs < 2^53 := by
    cases s <;> simp only [z, Bool.false_eq_true, ↓reduceIte] <;> omega
  have h₃ : 2^52 < (z+2*(a : Int)-1).natAbs ∧ (z+2*(a : Int)-1).natAbs < 2^53 := by
    cases s <;> simp only [z, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hb := tiesUp_grid_boundary z a K hC hr h₁ h₂ h₃ hf
  rw [hz] at hb
  refine ⟨2^K, Nat.two_pow_pos _, ?_, hb.1, ?_⟩
  · intro x hx
    have heq :
        (if s then -((M*2^(K+1-1) : Nat) : Int) else ((M*2^(K+1-1) : Nat) : Int)) = H := by
      rw [Nat.add_sub_cancel]
      cases s <;> simp only [H, Bool.false_eq_true, ↓reduceIte, hMg]
    have hh := normal_key_gap s (K+1) M (by omega) (by omega) (by omega) (by omega)
      x (by rwa [heq])
    rwa [heq, Nat.add_sub_cancel] at hh
  · rw [hb.2]
    have hh : (0 : Int) < ((2^K : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos _)
    omega

theorem half_boundary_all (s : Bool) (q : Nat) (hq₀ : 0 < q) (hq₁ : q ≤ 2^52+1)
    (hqOdd : q%2 = 1) :
    HalfBoundary (if s then -((q*2^1073 : Nat) : Int) else ((q*2^1073 : Nat) : Int)) := by
  by_cases hs : q = 1 ∨ q = 3 ∨ q = 2^52+1
  · exact half_boundary_small s q hs
  · exact half_boundary_normal s q (by omega) (by omega) hqOdd

theorem half_boundary_odd (k : Int) (hk : k.natAbs ≤ 2^52+1) (ho : k%2 = 1) :
    HalfBoundary (k*((2^1073 : Nat) : Int)) := by
  cases k with
  | ofNat a =>
    change a ≤ 2^52+1 at hk
    change (a : Int)%2 = 1 at ho
    have hh := half_boundary_all false a (by omega) hk (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.ofNat_eq_natCast] using hh
  | negSucc a =>
    have he : Int.negSucc a = -((a+1 : Nat) : Int) := by omega
    rw [he] at hk ho ⊢
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hk
    have hh := half_boundary_all true (a+1) (by omega) hk (by omega)
    simpa only [↓reduceIte, Int.natCast_mul, Int.neg_mul] using hh

theorem tiesUp_small_floor (x : F64) (hx : F64.isfinite x = true)
    (hs : (key64 x).natAbs < 2^1125) :
    F64.isfinite (tiesUpSum x) = true ∧
      (F64.toRat (tiesUpSum x)).1 / ((F64.toRat (tiesUpSum x)).2 : Int) =
        exactRound (F64.toRat x).1 (F64.toRat x).2 .NearestTiesUp := by
  obtain ⟨hfin, hkey⟩ := tiesUp_key_small x hx (Nat.le_of_lt hs)
  refine ⟨hfin, ?_⟩
  rw [key64_floor _ hfin, hkey, exactRound_tiesUp_key x hx]
  let t := key64 x
  let G := ((2^1074 : Nat) : Int)
  let R := ((2^1073 : Nat) : Int)
  let N := (2*t+G)/(2*G)
  have hG : 0 < G := Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hN : N*(2*G) ≤ 2*t+G ∧ 2*t+G < N*(2*G)+2*G :=
    (Int.ediv_eq_iff_of_pos (by omega : 0 < 2*G)).mp rfl
  have hnb : -((2^51 : Nat) : Int) ≤ N ∧ N ≤ ((2^51 : Nat) : Int) := by
    dsimp only [t, G] at *
    omega
  have hl : (2*N-1)*R ≤ t := by dsimp only [G, R] at *; omega
  have hu : t < (2*N+1)*R := by dsimp only [G, R] at *; omega
  have hbl := half_boundary_odd (2*N-1) (by omega) (by omega)
  have hbu := half_boundary_odd (2*N+1) (by omega) (by omega)
  obtain ⟨_, _, _, hlow, _⟩ := hbl
  obtain ⟨g, hg, hgap, _, hhigh⟩ := hbu
  have hlow' := tiesUp_key_monotone ((2*N-1)*R) t hl
  have hgap' : t ≤ (2*N+1)*R-(g : Int) := hgap x hu
  have hhigh' := tiesUp_key_monotone t ((2*N+1)*R-(g : Int)) hgap'
  change tiesUpKey t/G = N
  apply (Int.ediv_eq_iff_of_pos hG).mpr
  dsimp only [G, R] at *
  constructor <;> omega

theorem key64_under_2pow51 (x : F64) (he : F64.toBits x / 2^52 % 2048 ≤ 1073) :
    (key64 x).natAbs < 2^1125 := by
  rw [key64_abs]
  have hf : F64.toBits x % 2^52 < 2^52 := Nat.mod_lt _ (by decide)
  unfold magKey64
  by_cases hz : F64.exponentField x = 0
  · simp only [hz, beq_iff_eq, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero, F64.fraction]
    omega
  · have hp : 2^(F64.exponentField x-1) ≤ (2^1072 : Nat) :=
      Nat.pow_le_pow_right (by decide) (by change F64.toBits x / 2^52 % 2048-1 ≤ 1072; omega)
    simp only [beq_iff_eq, hz, ↓reduceIte, F64.fraction]
    calc
      _ < (2^53 : Nat)*2^(F64.exponentField x-1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ ≤ 2^53*2^1072 := Nat.mul_le_mul_left _ hp
      _ = _ := by rw [← Nat.pow_add]

end ProofRound

theorem roundModesExact_proven : RoundModesExact := by
  intro x m hx
  by_cases hm : m = .NearestTiesUp
  · subst m
    by_cases he : 1074 ≤ F64.toBits x / 2^52 % 2048
    · exact ProofRound.tiesUp_top_exact x hx he
    · obtain ⟨hfin, hfloor⟩ := ProofRound.tiesUp_small_floor x hx
        (ProofRound.key64_under_2pow51 x (by omega))
      exact ProofRound.tiesUp_exact_of_sum_floor x hx hfin hfloor
  · exact ProofRound.roundF_exact_except_tiesUp x m hm hx


end JuliaLean.FloatFuncs
