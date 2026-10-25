import JuliaLean.FloatFuncs.Props
import JuliaLean.FloatFuncs.ProofTrunc

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs JuliaLean.MathFuncs.ProofsBits

namespace ProofRoundInt

def quiet (x : F64) : F64 :=
  if F64.fraction x < 2^51 then F64.ofBits (F64.toBits x + 2^51) else x

theorem quiet_nan (x : F64) (hx : F64.isnan x = true) : F64.isnan (quiet x) = true := by
  have ht := tb_lt x
  have hn := (isnan_iff x).mp hx
  unfold quiet
  split
  · rw [isnan_iff, tb_ofBits]
    simp only [F64.fraction] at *
    omega
  · exact hx

theorem nan_add_left (x y : F64) (hx : F64.isnan x = true) :
    F64.isnan (F64.add x y) = true := by
  change F64.isnan (if F64.isnan x then quiet x else _) = true
  simp only [hx, ↓reduceIte]
  exact quiet_nan x hx

theorem nan_sub_left (x y : F64) (hx : F64.isnan x = true) :
    F64.isnan (F64.sub x y) = true := by
  change F64.isnan (if F64.isnan x then quiet x else _) = true
  simp only [hx, ↓reduceIte]
  exact quiet_nan x hx

theorem nan_mul_right (x y : F64) (hy : F64.isnan y = true) :
    F64.isnan (F64.mul x y) = true := by
  change F64.isnan (if F64.isnan x then quiet x else if F64.isnan y then quiet y else _) = true
  cases hx : F64.isnan x
  · simp only [hy, Bool.false_eq_true, ↓reduceIte]
    exact quiet_nan y hy
  · simp only [↓reduceIte]
    exact quiet_nan x hx

theorem quiet_or_nan (x : F64) (hx : F64.isnan x = true) :
    F64.isnan (F64.ofBits (Nat.lor (F64.toBits x) 0x0008000000000000)) = true := by
  have ht := tb_lt x
  have hn := (isnan_iff x).mp hx
  have hf : F64.toBits x % 2^52 < 2^52 := Nat.mod_lt _ (by decide)
  have hb : 0x0008000000000000 < 2^52 := by decide
  have hf' : Nat.lor (F64.toBits x % 2^52) 0x0008000000000000 < 2^52 :=
    Nat.or_lt_two_pow hf hb
  have hne : Nat.lor (F64.toBits x % 2^52) 0x0008000000000000 ≠ 0 := by
    simp
  have hor : Nat.lor (F64.toBits x) 0x0008000000000000 =
      2^52 * (F64.toBits x / 2^52) + Nat.lor (F64.toBits x % 2^52) 0x0008000000000000 := by
    change (F64.toBits x ||| 0x0008000000000000) =
      2^52 * (F64.toBits x / 2^52) + (F64.toBits x % 2^52 ||| 0x0008000000000000)
    have h := or_split (a := F64.toBits x / 2^52) (c := 0) hf hb
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.or_zero,
      Nat.div_add_mod] using h
  rw [isnan_iff, tb_ofBits, hor]
  omega

theorem round_simple_nan (x : F64) (m : Rounding) (hm : m ≠ .RoundNearestTiesAway)
    (hx : F64.isnan x = true) : F64.isnan (F64.round x m) = true := by
  cases m <;> first
  | exact False.elim (hm rfl)
  | (change F64.isnan
      (if F64.isnan x then F64.ofBits (Nat.lor (F64.toBits x) 0x0008000000000000) else _) = true
     simp only [hx, ↓reduceIte]
     exact quiet_or_nan x hx)

theorem trunc_nan (x : F64) (hx : F64.isnan x = true) :
    F64.isnan (F64.trunc x) = true :=
  round_simple_nan x .RoundToZero (by decide) hx

theorem copysign_nan (x y : F64) (hx : F64.isnan x = true) :
    F64.isnan (copysign x y) = true := by
  have ht := tb_lt x
  have ht' := tb_lt (copysign x y)
  have hn := (isnan_iff x).mp hx
  have ha := congrArg F64.toBits (copysignFloatSpec_proven x y).2
  simp only [tb_abs] at ha
  rw [isnan_iff]
  omega

theorem roundF_nan (x : F64) (m : Mode) (hx : F64.isnan x = true) :
    F64.isnan (roundF x m) = true := by
  cases m with
  | Nearest => exact round_simple_nan x .RoundNearest (by decide) hx
  | ToZero => exact round_simple_nan x .RoundToZero (by decide) hx
  | Up => exact round_simple_nan x .RoundUp (by decide) hx
  | Down => exact round_simple_nan x .RoundDown (by decide) hx
  | FromZero =>
    simp only [roundF]
    split
    · exact round_simple_nan x .RoundDown (by decide) hx
    · exact round_simple_nan x .RoundUp (by decide) hx
  | NearestTiesAway =>
    change F64.isnan (if F64.eq x (F64.trunc x) then F64.trunc x
      else F64.trunc (F64.sub (F64.mul (F64.ofInt 2) x) (F64.trunc x))) = true
    have heq : F64.eq x (F64.trunc x) = false := by simp [F64.eq, hx]
    simp only [heq, Bool.false_eq_true, ↓reduceIte]
    apply trunc_nan
    exact nan_sub_left _ _ (nan_mul_right _ x hx)
  | NearestTiesUp =>
    simp only [roundF]
    apply copysign_nan
    apply round_simple_nan _ .RoundDown (by decide)
    apply nan_add_left
    exact nan_add_left x _ hx

theorem roundF_inf (s : Bool) (m : Mode) : roundF (F64.inf s) m = F64.inf s := by
  cases s <;> cases m <;> decide

theorem roundF_nonfinite (x : F64) (m : Mode) (hx : F64.isfinite x = false) :
    F64.isfinite (roundF x m) = false := by
  cases hn : F64.isnan x
  · have ht := tb_lt x
    have he : F64.toBits x / 2^52 % 2048 = 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hx
    have hnf := (isnan_f x).mp hn
    have hi : F64.isinf x = true := by rw [isinf_iff]; omega
    obtain ⟨s, rfl⟩ := inf_of_isinf x hi
    rw [roundF_inf]
    cases s <;> decide
  · have hr := (isnan_iff (roundF x m)).mp (roundF_nan x m hn)
    simp only [F64.isfinite, F64.exponentField, hr.1]
    decide

theorem roundIntM_eq (t : IntTy) (x : F64) (m : Mode) (hm : m ≠ .ToZero) :
    roundIntM t x m = F64.int t (roundF x m) := by
  cases m <;> first | exact False.elim (hm rfl) | rfl

end ProofRoundInt

theorem roundIntExact_of (h : RoundModesExact) : RoundIntExact := by
  intro t x m hm
  rw [ProofRoundInt.roundIntM_eq t x m hm, intConvertExact_proven t (roundF x m)]
  cases hx : F64.isfinite x
  · have hr := ProofRoundInt.roundF_nonfinite x m hx
    simp only [hr, Bool.false_eq_true, false_and, ↓reduceIte]
  · obtain ⟨hr, _, hv⟩ := h x m hx
    have hd : ((F64.toRat (roundF x m)).2 : Int) ≠ 0 := by
      have := toRat_den_pos (roundF x m) hr
      omega
    have hmod : (F64.toRat (roundF x m)).1 % ((F64.toRat (roundF x m)).2 : Int) = 0 := by
      rw [hv, Int.mul_emod_left]
    have hdiv : (F64.toRat (roundF x m)).1 / ((F64.toRat (roundF x m)).2 : Int) =
        exactRound (F64.toRat x).1 (F64.toRat x).2 m := by
      rw [hv, Int.mul_ediv_cancel _ hd]
    simp only [hr, hmod, hdiv, true_and]

end JuliaLean.FloatFuncs
