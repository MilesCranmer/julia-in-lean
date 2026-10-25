import JuliaLean.BigNums.Int

/-!
Proofs that BigInt `div`/`rem`/`mod`/`fld`/`cld` agree with the machine-integer functions
on every `BitInteger` type, and that negative-exponent `^` agrees with Int64
`power_by_squaring` up to the exception type.

The arithmetic is done on plain integers: the GMP results are expressed through the
truncated quotient `q` and remainder `r`, whose magnitudes are bounded by the operands.
-/

namespace JuliaLean.BigNums

open JuliaLean

/-! ## Wrapping and type ranges -/

private theorem wrapInt_sub_wrap (t : IntTy) (x y : Int) :
    wrapInt t (x - wrapInt t y) = wrapInt t (x - y) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem wrapInt_add_wrap (t : IntTy) (x y : Int) :
    wrapInt t (x + wrapInt t y) = wrapInt t (x + y) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem ty_range (t : IntTy) :
    (t.min = -(t.max + 1) ∧ 127 ≤ t.max) ∨ (t.min = 0 ∧ 255 ≤ t.max) := by
  cases t <;> simp [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits]

private theorem signed_of_min_neg (t : IntTy) (h : t.min < 0) : t.signed = true := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem unsigned_nonneg {t : IntTy} (x : JInt t) (h : t.signed = false) :
    0 ≤ x.val := by
  have hx := x.property.1
  cases t <;> simp_all [IntTy.signed, IntTy.min]

/-! ## Quotients and remainders of integers -/

/-- Floored quotient and remainder in terms of the truncated ones. -/
private theorem fdiv_fmod_tdiv (a b : Int) (hb : b ≠ 0) :
    a.fdiv b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b - 1 else a.tdiv b) ∧
    a.fmod b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tmod b + b else a.tmod b) := by
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  have h4 : a = 0 → a % b = 0 := by intro h; subst h; simp
  have htm0 : (a.tmod b = 0) = (a % b = 0) := by
    rw [Int.tmod_eq_emod]
    simp only [Int.dvd_iff_emod_eq_zero]
    apply propext
    split <;> omega
  simp only [ne_eq, htm0]
  rw [Int.fdiv_eq_ediv, Int.fmod_eq_emod, Int.tdiv_eq_ediv, Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  generalize a / b = e
  generalize a % b = m at h0 h1 h4 ⊢
  rcases Int.lt_or_gt_of_ne hb with hs | hs
  · rw [Int.sign_eq_neg_one_of_neg hs]
    constructor <;> (repeat' split) <;> omega
  · rw [Int.sign_eq_one_of_pos hs]
    constructor <;> (repeat' split) <;> omega

/-- Ceiled quotient in terms of the truncated one. -/
private theorem cdiv_tdiv (a b : Int) (hb : b ≠ 0) :
    -((-a).fdiv b) = (if ((0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b + 1 else a.tdiv b) := by
  rw [(fdiv_fmod_tdiv (-a) b hb).1, Int.neg_tdiv, Int.neg_tmod]
  split <;> split <;> omega

private theorem fdiv_mul_add_fmod (a b : Int) (hb : b ≠ 0) :
    a.fdiv b * b + a.fmod b = a := by
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a b hb
  have := Int.tdiv_mul_add_tmod a b
  rw [hfd, hfm]
  split
  · rw [Int.sub_mul, Int.one_mul]
    omega
  · omega

private theorem fmod_neg_one (a : Int) : a.fmod (-1) = 0 := by
  rw [(fdiv_fmod_tdiv a (-1) (by decide)).2, Int.tmod_neg, Int.tmod_one]
  simp

private theorem quot_facts (a b : Int) (hb : b ≠ 0) :
    a.tdiv b * b + a.tmod b = a ∧
    (0 ≤ a → 0 ≤ a.tmod b ∧ a.tmod b ≤ a) ∧ (a < 0 → a ≤ a.tmod b ∧ a.tmod b ≤ 0) ∧
    (0 < b → -b < a.tmod b ∧ a.tmod b < b) ∧ (b < 0 → b < a.tmod b ∧ a.tmod b < -b) ∧
    (0 ≤ a → (2 ≤ b ∨ b ≤ -2) → -a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ a) ∧
    (a < 0 → (2 ≤ b ∨ b ≤ -2) → a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ -a) ∧
    (b = 1 → a.tdiv b = a) ∧ (b = -1 → a.tdiv b = -a) ∧
    (0 ≤ a → 0 < b → 0 ≤ a.tdiv b) := by
  have hra : (a.tmod b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
  have hq2 : 2 ≤ b.natAbs → 2 * (a.tdiv b).natAbs ≤ a.natAbs := by
    intro h2
    rw [Int.natAbs_tdiv]
    have := @Nat.div_le_div_left 2 b.natAbs a.natAbs h2 (by omega)
    show 2 * (a.natAbs / b.natAbs) ≤ a.natAbs
    omega
  refine ⟨Int.tdiv_mul_add_tmod a b, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h h2 => ?_, fun h h2 => ?_, fun h => by subst h; exact Int.tdiv_one a,
    fun h => by subst h; rw [Int.tdiv_neg, Int.tdiv_one], fun ha hb' => ?_⟩
  · have := Int.tmod_nonneg b h
    omega
  · have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
    rw [Int.neg_tmod] at this
    omega
  · exact ⟨Int.lt_tmod_of_pos a h, Int.tmod_lt_of_pos a h⟩
  · have h1 := Int.lt_tmod_of_pos a (show 0 < -b by omega)
    have h2 := Int.tmod_lt_of_pos a (show 0 < -b by omega)
    rw [Int.tmod_neg] at h1 h2
    omega
  · have := hq2 (by omega)
    omega
  · have := hq2 (by omega)
    omega
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]; exact Int.ediv_nonneg ha (by omega)

/-- Every exact result lies in `[lo, hi]`, except the quotients of `lo ÷ -1` for signed
ranges. -/
private theorem ranges_int (x y q r lo hi : Int) (hy : y ≠ 0)
    (hx : lo ≤ x ∧ x ≤ hi) (hyr : lo ≤ y ∧ y ≤ hi)
    (hty : (lo = -(hi + 1) ∧ 127 ≤ hi) ∨ (lo = 0 ∧ 255 ≤ hi))
    (hqr : q * y + r = x)
    (hra0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hra1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hrb0 : 0 < y → -y < r ∧ r < y) (hrb1 : y < 0 → y < r ∧ r < -y)
    (hq20 : 0 ≤ x → (2 ≤ y ∨ y ≤ -2) → -x ≤ 2 * q ∧ 2 * q ≤ x)
    (hq21 : x < 0 → (2 ≤ y ∨ y ≤ -2) → x ≤ 2 * q ∧ 2 * q ≤ -x)
    (hq1 : y = 1 → q = x) (hqm1 : y = -1 → q = -x) (hqpos : 0 ≤ x → 0 < y → 0 ≤ q) :
    (lo ≤ r ∧ r ≤ hi) ∧
    (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ∧
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ≤ hi) ∧
    (lo ≤ q * y ∧ q * y ≤ hi) ∧
    (¬(lo < 0 ∧ x = lo ∧ y = -1) →
      (lo ≤ q ∧ q ≤ hi) ∧
      (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ∧
        (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ≤ hi) ∧
      (lo ≤ (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ∧
        (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ≤ hi)) := by
  rcases hty with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;>
  by_cases hx0 : 0 ≤ x <;>
  rcases Int.lt_or_gt_of_ne hy with hy0 | hy0 <;>
  refine ⟨by omega, by split <;> omega, by omega,
    fun hn => ⟨by omega, by split <;> omega, by split <;> omega⟩⟩

/-! ## Machine results -/

private theorem ranges {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0) :
    (t.min ≤ a.val.tmod b.val ∧ a.val.tmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.fmod b.val ∧ a.val.fmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.tdiv b.val * b.val ∧ a.val.tdiv b.val * b.val ≤ t.max) ∧
    (¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) →
      (t.min ≤ a.val.tdiv b.val ∧ a.val.tdiv b.val ≤ t.max) ∧
      (t.min ≤ a.val.fdiv b.val ∧ a.val.fdiv b.val ≤ t.max) ∧
      (t.min ≤ -((-a.val).fdiv b.val) ∧ -((-a.val).fdiv b.val) ≤ t.max)) := by
  obtain ⟨hqr, hr0, hr1, hrb, hra, hqa, hq2, hq1, hqm1, hqpos⟩ := quot_facts a.val b.val hb0
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a.val b.val hb0
  have key := ranges_int a.val b.val _ _ t.min t.max hb0 a.property b.property (ty_range t)
    hqr hr0 hr1 hrb hra hqa hq2 hq1 hqm1 hqpos
  rw [hfd, hfm, cdiv_tdiv a.val b.val hb0]
  exact ⟨key.1, key.2.1, key.2.2.1,
    fun hn => key.2.2.2 fun h => hn ⟨signed_of_min_neg t h.1, h.2⟩⟩

private theorem div_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
  unfold JInt.div
  rw [ite_eq_right hb0, ite_eq_right hn]

private theorem mul_wrap_val {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    (JInt.wrap t (a.val.tdiv b.val) * b).val = a.val.tdiv b.val * b.val := by
  obtain ⟨-, -, hqbR, hrng⟩ := ranges a b hb0
  show wrapInt t (wrapInt t _ * b.val) = _
  rw [wrapInt_of_inRange t _ (hrng hn).1, wrapInt_of_inRange t _ hqbR]

private theorem pos_of_unsigned {t : IntTy} (x : JInt t) (h : t.signed = false)
    (hx : x.val ≠ 0) : 0 < x.val := by
  have := unsigned_nonneg x h
  omega

private theorem sub_of_add (p m x : Int) (h : p + m = x) : x - p = m := by
  omega

private theorem fld_cond (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0) :
    q - (if ((x < 0 ∧ 0 ≤ y) ∨ (0 ≤ x ∧ y < 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) := by
  split <;> split <;> omega

private theorem cld_cond (s : Bool) (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hs : s = false → 0 ≤ x ∧ 0 < y) :
    q + (if (¬ s = true ∨ (x > 0 ↔ y > 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) := by
  cases s
  · have := hs rfl
    simp only [Bool.false_eq_true, not_false_eq_true, true_or, true_and]
    split <;> split <;> omega
  · simp only [not_true_eq_false, false_or]
    split <;> split <;> omega

private theorem fld_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.fld a b = .ok (JInt.wrap t (a.val.fdiv b.val)) := by
  obtain ⟨hqr, hr0, hr1, -⟩ := quot_facts a.val b.val hb0
  obtain ⟨-, -, -, hrng⟩ := ranges a b hb0
  obtain ⟨hfd, -⟩ := fdiv_fmod_tdiv a.val b.val hb0
  unfold JInt.fld
  rw [div_mach a b hb0 hn]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [mul_wrap_val a b hb0 hn]
  cases hs : t.signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ha0 := unsigned_nonneg a hs
    have hb1 := pos_of_unsigned b hs hb0
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hb1), Int.tdiv_eq_ediv_of_nonneg ha0]
  · simp only [↓reduceIte]
    congr 1
    apply Subtype.ext
    show wrapInt t (wrapInt t (a.val.tdiv b.val) - wrapInt t _) = wrapInt t (a.val.fdiv b.val)
    rw [wrapInt_of_inRange t (a.val.tdiv b.val) (hrng hn).1, wrapInt_sub_wrap, hfd,
      fld_cond a.val b.val _ _ hb0 hqr hr0 hr1]

private theorem cld_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.cld a b = .ok (JInt.wrap t (-((-a.val).fdiv b.val))) := by
  obtain ⟨hqr, hr0, hr1, -⟩ := quot_facts a.val b.val hb0
  obtain ⟨-, -, -, hrng⟩ := ranges a b hb0
  have hsu : t.signed = false → 0 ≤ a.val ∧ 0 < b.val := fun hs =>
    ⟨unsigned_nonneg a hs, pos_of_unsigned b hs hb0⟩
  unfold JInt.cld
  rw [div_mach a b hb0 hn]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [mul_wrap_val a b hb0 hn]
  congr 1
  apply Subtype.ext
  show wrapInt t (wrapInt t (a.val.tdiv b.val) + wrapInt t _) =
    wrapInt t (-((-a.val).fdiv b.val))
  rw [wrapInt_of_inRange t (a.val.tdiv b.val) (hrng hn).1, wrapInt_add_wrap,
    cdiv_tdiv a.val b.val hb0, cld_cond t.signed a.val b.val _ _ hb0 hqr hr0 hr1 hsu]

private theorem mod_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0) :
    JInt.mod a b = .ok (JInt.wrap t (a.val.fmod b.val)) := by
  obtain ⟨-, -, -, hrng⟩ := ranges a b hb0
  unfold JInt.mod
  cases hs : t.signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ha0 := unsigned_nonneg a hs
    have hb1 := pos_of_unsigned b hs hb0
    unfold JInt.remInt
    rw [ite_eq_right hb0, Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt hb1),
      Int.tmod_eq_emod_of_nonneg ha0]
  · simp only [↓reduceIte]
    by_cases hbm : b.val = -1
    · rw [ite_eq_left hbm, hbm, fmod_neg_one]
      rfl
    · have hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) := fun h => hbm h.2.2
      rw [ite_eq_right hbm, fld_mach a b hb0 hn]
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      congr 1
      apply Subtype.ext
      show wrapInt t (a.val - wrapInt t (wrapInt t (a.val.fdiv b.val) * b.val)) =
        wrapInt t (a.val.fmod b.val)
      rw [wrapInt_of_inRange t (a.val.fdiv b.val) (hrng hn).2.1, wrapInt_sub_wrap]
      rw [sub_of_add _ _ _ (fdiv_mul_add_fmod a.val b.val hb0)]

private theorem ok_map_val {t : IntTy} (x : Int) (h : t.min ≤ x ∧ x ≤ t.max) :
    (Except.ok (JInt.wrap t x) : Jl (JInt t)).map Subtype.val = .ok x := by
  show Except.ok (wrapInt t x) = Except.ok x
  rw [wrapInt_of_inRange t x h]

/-! ## The properties -/

theorem divisionMatchesInt_proven : DivisionMatchesInt := by
  intro t a b
  by_cases hb0 : b.val = 0
  · have hd : JInt.div a b = .error .divideError := by simp [JInt.div, hb0]
    have hf : JInt.fld a b = .error .divideError := by
      simp only [JInt.fld, hd, Bind.bind, Except.bind]
    have hc : JInt.cld a b = .error .divideError := by
      simp only [JInt.cld, hd, Bind.bind, Except.bind]
    have hm : JInt.mod a b = .error .divideError := by
      unfold JInt.mod
      rw [ite_eq_right (show ¬ b.val = -1 by rw [hb0]; decide), hf]
      simp [JInt.remInt, hb0, Bind.bind, Except.bind]
    refine ⟨?_, ?_, fun _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp [rem, tdivR, JInt.remInt, mod, fdivR, hm, div, tdivQ, hd, fld, fdivQ, hf, cld,
        cdivQ, hc, hb0, Except.map]
  · obtain ⟨hrR, hfmR, -, hrng⟩ := ranges a b hb0
    have hrem : JInt.remInt a b = .ok (JInt.wrap t (a.val.tmod b.val)) := by
      unfold JInt.remInt
      rw [ite_eq_right hb0]
    refine ⟨?_, ?_, fun hn => ?_⟩
    · rw [hrem, ok_map_val _ hrR]
      simp only [rem, tdivR, hb0, ↓reduceIte]
    · rw [mod_mach a b hb0, ok_map_val _ hfmR]
      simp only [mod, fdivR, hb0, ↓reduceIte]
    · obtain ⟨hqR, hfR, hcR⟩ := hrng hn
      refine ⟨?_, ?_, ?_⟩
      · rw [div_mach a b hb0 hn, ok_map_val _ hqR]
        simp only [div, tdivQ, hb0, ↓reduceIte]
      · rw [fld_mach a b hb0 hn, ok_map_val _ hfR]
        simp only [fld, fdivQ, hb0, ↓reduceIte]
      · rw [cld_mach a b hb0 hn, ok_map_val _ hcR]
        simp only [cld, cdivQ, hb0, ↓reduceIte]

theorem powNegativeMatchesInt_proven : PowNegativeMatchesInt := by
  intro x p hp
  have hx := x.property
  have hneg : ((-x).val = 1) = (x.val = -1) := by
    apply propext
    show wrapInt .i64 (-x.val) = 1 ↔ x.val = -1
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx
    simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
    omega
  have hp1 : ¬ p.val = 1 := by omega
  have hp0 : ¬ p.val = 0 := by omega
  have hp2 : ¬ p.val = 2 := by omega
  simp only [bigintPow, IntArith.PowersDigits.powerBySquaring, hp1, hp0, hp2, hp, hneg,
    ↓reduceIte]
  by_cases h1 : x.val = 1
  · simp [h1, sameOutcome, sameJl, Except.map]
  · by_cases h2 : x.val = -1
    · by_cases hpe : p.val % 2 = 0
      · simp [h2, hpe, sameOutcome, sameJl, Except.map, JInt.lit, JInt.wrap, wrapInt,
          IntTy.signed, IntTy.bits]
      · simp [h2, hpe, sameOutcome, sameJl, Except.map]
    · simp [h1, h2, sameOutcome, sameJl, Except.map, errKind]

end JuliaLean.BigNums
