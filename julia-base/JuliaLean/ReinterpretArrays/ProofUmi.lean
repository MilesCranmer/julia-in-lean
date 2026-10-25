import JuliaLean.ReinterpretArrays.MultInvProps
import JuliaLean.ReinterpretArrays.Wrap

/-!
Proof of `UmiDivCorrect`: for every unsigned integer type, `UnsignedMultiplicativeInverse(d)`
(`base/multinverses.jl:98-133`) returns, and `div`/`rem` by it (`base/multinverses.jl:142-149`) agree
with `div`/`rem` by `d`.

With `n = bits(T)` and `W = 2^n`, the constructor loop keeps `q1, r1 = divrem(2^p, nc)` and
`q2, r2 = divrem(2^p - 1, d)`. While the loop runs, `2^p < nc * d`, so neither quotient wraps and
`add` stays false. It stops at the first `p` with `nc * e < 2^p`, where `m = q2 + 1 = ⌈2^p / d⌉` and
`e = m * d - 2^p`; then `m < 2 W`, `add` records `W ≤ m`, and `⌊a m / 2^p⌋ = ⌊a / d⌋` for `0 ≤ a < W`.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean IntArith.NumberTheory

namespace Umi

/-! ### Integer arithmetic -/

/-- Quotient and remainder of an explicit Euclidean decomposition. -/
theorem divmod_of_eq {x c q r : Int} (hc : 0 < c) (h : x = c * q + r) (h0 : 0 ≤ r) (h1 : r < c) :
    x / c = q ∧ x % c = r := by
  have hq : x / c = q := by
    subst h
    rw [Int.add_comm, Int.mul_comm, Int.add_mul_ediv_right _ _ (by omega : c ≠ 0),
      Int.ediv_eq_zero_of_lt h0 h1, Int.zero_add]
  refine ⟨hq, ?_⟩
  rw [Int.emod_def, hq]
  omega

/-- Floor division from bounds on the dividend. -/
theorem ediv_eq_of_bounds {x c q : Int} (hc : 0 < c) (h1 : c * q ≤ x) (h2 : x < c * q + c) :
    x / c = q :=
  (divmod_of_eq hc (show x = c * q + (x - c * q) by omega) (by omega) (by omega)).1

theorem le_of_mul_le {D b c : Int} (hD : 0 < D) (h : D * b ≤ D * c) : b ≤ c := by
  rcases (show b ≤ c ∨ c + 1 ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    rw [Int.mul_add, Int.mul_one] at this
    omega

theorem lt_of_mul_lt {D b c : Int} (hD : 0 < D) (h : D * b < D * c) : b < c := by
  rcases (show b < c ∨ c ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    omega

theorem lt_of_mul_lt_right {c a b : Int} (hc : 0 < c) (h : a * c < b * c) : a < b := by
  rw [Int.mul_comm a, Int.mul_comm b] at h
  exact lt_of_mul_lt hc h

theorem mul_nonneg' {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at this

theorem ediv_ediv {x y z : Int} (hy : 0 < y) : x / y / z = x / (y * z) :=
  Int.ediv_ediv_of_nonneg (Int.le_of_lt hy)

theorem two_pow_pos (k : Nat) : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)

theorem two_pow_succ (k : Nat) : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by
  rw [Int.pow_succ, Int.mul_comm]

theorem two_pow_mono {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Int.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · have := ih (by omega)
      have := two_pow_pos b
      rw [two_pow_succ]
      omega
    · have : a = b + 1 := by omega
      subst this
      exact Int.le_refl _

/-! ### Unsigned types -/

theorem bits_ge (t : IntTy) : 8 ≤ t.bits := by cases t <;> decide

theorem bits_le (t : IntTy) : t.bits ≤ 128 := by cases t <;> decide

theorem two_pow_half (t : IntTy) : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := by
  have h := two_pow_succ (t.bits - 1)
  rwa [Nat.sub_add_cancel (by have := bits_ge t; omega : 1 ≤ t.bits)] at h

theorem two_pow_half_ge (t : IntTy) : (128 : Int) ≤ 2 ^ (t.bits - 1) := by
  have h := two_pow_mono (show 7 ≤ t.bits - 1 by have := bits_ge t; omega)
  have h7 : (2 : Int) ^ 7 = 128 := by decide
  omega

theorem wrap_u {t : IntTy} (ht : t.signed = false) (x : Int) : wrapInt t x = x % 2 ^ t.bits := by
  simp [wrapInt, ht]

theorem val_bounds_u {t : IntTy} (ht : t.signed = false) (a : JInt t) :
    0 ≤ a.val ∧ a.val < 2 ^ t.bits := by
  have h := a.property
  simp [IntTy.min, IntTy.max, ht] at h
  omega

theorem wrap_id {t : IntTy} (ht : t.signed = false) {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ t.bits) :
    wrapInt t x = x := by
  rw [wrap_u ht, Int.emod_eq_of_lt h0 h1]

theorem wrap_sub_W {t : IntTy} (ht : t.signed = false) (x : Int) :
    wrapInt t (x - 2 ^ t.bits) = wrapInt t x := by
  rw [← wrapInt_sub, wrap_u ht (2 ^ t.bits), Int.emod_self, Int.sub_zero, wrapInt_wrapInt]

theorem wrap_add_l (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a + b) = wrapInt t (a + b) := by
  rw [← wrapInt_add t (wrapInt t a) b, wrapInt_wrapInt, wrapInt_add]

theorem wrap_add_r (t : IntTy) (a b : Int) : wrapInt t (a + wrapInt t b) = wrapInt t (a + b) := by
  rw [← wrapInt_add t a (wrapInt t b), wrapInt_wrapInt, wrapInt_add]

theorem wrap_sub_l (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a - b) = wrapInt t (a - b) := by
  rw [← wrapInt_sub t (wrapInt t a) b, wrapInt_wrapInt, wrapInt_sub]

theorem wrap_sub_r (t : IntTy) (a b : Int) : wrapInt t (a - wrapInt t b) = wrapInt t (a - b) := by
  rw [← wrapInt_sub t a (wrapInt t b), wrapInt_wrapInt, wrapInt_sub]

theorem val_wrap (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl

theorem jle {t : IntTy} (a b : JInt t) : (a ≤ b) = (a.val ≤ b.val) := rfl

theorem u8_in (k : Nat) (hk : k ≤ 255) : IntTy.min .u8 ≤ (k : Int) ∧ (k : Int) ≤ IntTy.max .u8 := by
  have h : IntTy.min .u8 = 0 ∧ IntTy.max .u8 = 255 := by decide
  omega

theorem remInt_ok {t : IntTy} (a b : JInt t) (hb : b.val ≠ 0) :
    JInt.remInt a b = .ok (JInt.wrap t (a.val.tmod b.val)) := by
  unfold JInt.remInt
  rw [ite_eq_right hb]

theorem div_ok {t : IntTy} (ht : t.signed = false) (a b : JInt t) (hb : b.val ≠ 0) :
    JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
  unfold JInt.div
  rw [ite_eq_right hb, ite_eq_right (by simp [ht])]

theorem bind_ok {α β : Type} (x : α) (f : α → Jl β) : (Except.ok x >>= f : Jl β) = f x := rfl

/-! ### The magic-number constructor -/

/-- What the constructor loop returns for divisor `d` and `nc`: the final exponent `p + 1`, the
multiplier `⌈2^(p+1) / d⌉` wrapped to `T`, the `add` flag recording that it needs `bits + 1` bits,
the stopping inequality `e * nc < 2^(p+1)`, and the shift. -/
def Good (t : IntTy) (d : JInt t) (nc : Int) (mi : UnsignedMI t) : Prop :=
  mi.divisor = d ∧ ∃ p : Nat, t.bits ≤ p + 1 ∧ p + 1 ≤ 2 * t.bits ∧
    (p + 1 = t.bits ∨ (2 : Int) ^ p < nc * d.val) ∧
    mi.multiplier.val = wrapInt t (((2 : Int) ^ (p + 1) - 1) / d.val + 1) ∧
    mi.add = decide ((2 : Int) ^ t.bits ≤ ((2 : Int) ^ (p + 1) - 1) / d.val + 1) ∧
    (d.val - 1 - ((2 : Int) ^ (p + 1) - 1) % d.val) * nc < 2 ^ (p + 1) ∧
    mi.shift =
      (wrapInt .u8 (((p + 1 : Nat) : Int) - (t.bits : Int) - (if mi.add then 1 else 0))).toNat

theorem good_ite {t : IntTy} {d : JInt t} {nc : Int} {c : Prop} [Decidable c]
    {A B : UnsignedMI t} (h1 : c → Good t d nc A) (h2 : ¬ c → Good t d nc B) :
    Good t d nc (if c then A else B) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact h1 h
  · rw [ite_eq_right h]; exact h2 h

/-- One pass of the loop body from a state with exact quotients and remainders at exponent `p`:
the next state holds the (wrapped) quotients and remainders at exponent `p + 1`, and `add` records
whether `⌈2^(p+1) / d⌉` reaches `W`. -/
theorem magicLoop_step {t : IntTy} (ht : t.signed = false) (d nc : JInt t) (p : Nat)
    (q1 r1 q2 r2 : JInt t) (hD : 1 ≤ d.val) (hN : 1 ≤ nc.val)
    (hq1 : q1.val = 2 ^ p / nc.val) (hr1 : r1.val = 2 ^ p % nc.val)
    (hq2 : q2.val = (2 ^ p - 1) / d.val) (hr2 : r2.val = (2 ^ p - 1) % d.val)
    (G : UnsignedMI t → Prop)
    (hG : ∀ (q1' r1' q2' r2' : JInt t) (add' : Bool),
      q1'.val = wrapInt t (2 ^ (p + 1) / nc.val) → r1'.val = 2 ^ (p + 1) % nc.val →
      q2'.val = wrapInt t ((2 ^ (p + 1) - 1) / d.val) → r2'.val = (2 ^ (p + 1) - 1) % d.val →
      add' = decide ((2 : Int) ^ t.bits ≤ (2 ^ (p + 1) - 1) / d.val + 1) →
      G (if p + 1 < 2 * t.bits ∧
          (q1' < d - JInt.lit t 1 - r2' ∨ (q1' = d - JInt.lit t 1 - r2' ∧ r1'.val = 0))
        then magicLoop t d nc (p + 1) q1' r1' q2' r2' add'
        else ⟨d, q2' + JInt.lit t 1, add',
          (JInt.wrap .u8 (((p + 1 : Nat) : Int) - (t.bits : Int) - (if add' then 1 else 0))).val.toNat⟩)) :
    G (magicLoop t d nc p q1 r1 q2 r2 false) := by
  obtain ⟨hD0, hDW⟩ := val_bounds_u ht d
  obtain ⟨hN0, hNW⟩ := val_bounds_u ht nc
  have hWH := two_pow_half t
  have hH := two_pow_half_ge t
  have hX := two_pow_pos p
  have hX2 := two_pow_succ p
  have e1 := Int.mul_ediv_add_emod ((2 : Int) ^ p) nc.val
  have e1a := Int.emod_nonneg ((2 : Int) ^ p) (by omega : nc.val ≠ 0)
  have e1b := Int.emod_lt_of_pos ((2 : Int) ^ p) (by omega : 0 < nc.val)
  have e2 := Int.mul_ediv_add_emod ((2 : Int) ^ p - 1) d.val
  have e2a := Int.emod_nonneg ((2 : Int) ^ p - 1) (by omega : d.val ≠ 0)
  have e2b := Int.emod_lt_of_pos ((2 : Int) ^ p - 1) (by omega : 0 < d.val)
  have cond1 : r1 ≥ nc - r1 ↔ nc.val ≤ 2 * (2 ^ p % nc.val) := by
    rw [ge_iff_le, jle, val_sub, hr1,
      wrap_id ht (x := nc.val - 2 ^ p % nc.val) (by omega) (by omega)]
    constructor <;> intro h <;> omega
  have cond2 : r2 + JInt.lit t 1 ≥ d - r2 ↔ d.val ≤ 2 * ((2 ^ p - 1) % d.val) + 1 := by
    rw [ge_iff_le, jle, val_sub, val_add, val_lit, wrap_add_r, hr2,
      wrap_id ht (x := d.val - (2 ^ p - 1) % d.val) (by omega) (by omega),
      wrap_id ht (x := (2 ^ p - 1) % d.val + 1) (by omega) (by omega)]
    constructor <;> intro h <;> omega
  rw [magicLoop]
  dsimp only
  by_cases c1 : nc.val ≤ 2 * (2 ^ p % nc.val) <;>
    by_cases c2 : d.val ≤ 2 * ((2 ^ p - 1) % d.val) + 1
  · rw [ite_eq_left (cond1.mpr c1), ite_eq_left (cond2.mpr c2)]
    dsimp only
    have s1 := divmod_of_eq (x := (2 : Int) ^ (p + 1)) (c := nc.val)
      (q := 2 ^ p / nc.val + 2 ^ p / nc.val + 1) (r := 2 ^ p % nc.val + 2 ^ p % nc.val - nc.val)
      (by omega) (by rw [hX2, Int.mul_add, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)
    have s2 := divmod_of_eq (x := (2 : Int) ^ (p + 1) - 1) (c := d.val)
      (q := (2 ^ p - 1) / d.val + (2 ^ p - 1) / d.val + 1)
      (r := (2 ^ p - 1) % d.val + (2 ^ p - 1) % d.val + 1 - d.val)
      (by omega) (by rw [hX2, Int.mul_add, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)
    apply hG
    · rw [s1.1]; simp only [val_add, val_lit, hq1, wrap_add_l, wrap_add_r]
    · rw [s1.2]; simp only [val_add, val_sub, hr1, wrap_sub_l]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]; simp only [val_add, val_lit, hq2, wrap_add_l, wrap_add_r]
    · rw [s2.2]; simp only [val_add, val_sub, val_lit, hr2, wrap_add_l, wrap_add_r, wrap_sub_l]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]
      simp only [Bool.false_or, ge_iff_le, jle, val_sub, val_wrap, val_lit, wrap_sub_l, wrap_sub_r,
        hq2, decide_eq_decide]
      rw [wrap_id ht (x := 2 ^ (t.bits - 1) - 1) (by omega) (by omega)]
      constructor <;> intro h <;> omega
  · rw [ite_eq_left (cond1.mpr c1), ite_eq_right (fun h => c2 (cond2.mp h))]
    dsimp only
    have s1 := divmod_of_eq (x := (2 : Int) ^ (p + 1)) (c := nc.val)
      (q := 2 ^ p / nc.val + 2 ^ p / nc.val + 1) (r := 2 ^ p % nc.val + 2 ^ p % nc.val - nc.val)
      (by omega) (by rw [hX2, Int.mul_add, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)
    have s2 := divmod_of_eq (x := (2 : Int) ^ (p + 1) - 1) (c := d.val)
      (q := (2 ^ p - 1) / d.val + (2 ^ p - 1) / d.val)
      (r := (2 ^ p - 1) % d.val + (2 ^ p - 1) % d.val + 1)
      (by omega) (by rw [hX2, Int.mul_add]; omega) (by omega) (by omega)
    apply hG
    · rw [s1.1]; simp only [val_add, val_lit, hq1, wrap_add_l, wrap_add_r]
    · rw [s1.2]; simp only [val_add, val_sub, hr1, wrap_sub_l]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]; simp only [val_add, hq2]
    · rw [s2.2]; simp only [val_add, val_lit, hr2, wrap_add_l, wrap_add_r]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]
      simp only [Bool.false_or, ge_iff_le, jle, val_wrap, hq2, decide_eq_decide]
      rw [wrap_id ht (x := 2 ^ (t.bits - 1)) (by omega) (by omega)]
      constructor <;> intro h <;> omega
  · rw [ite_eq_right (fun h => c1 (cond1.mp h)), ite_eq_left (cond2.mpr c2)]
    dsimp only
    have s1 := divmod_of_eq (x := (2 : Int) ^ (p + 1)) (c := nc.val)
      (q := 2 ^ p / nc.val + 2 ^ p / nc.val) (r := 2 ^ p % nc.val + 2 ^ p % nc.val)
      (by omega) (by rw [hX2, Int.mul_add]; omega) (by omega) (by omega)
    have s2 := divmod_of_eq (x := (2 : Int) ^ (p + 1) - 1) (c := d.val)
      (q := (2 ^ p - 1) / d.val + (2 ^ p - 1) / d.val + 1)
      (r := (2 ^ p - 1) % d.val + (2 ^ p - 1) % d.val + 1 - d.val)
      (by omega) (by rw [hX2, Int.mul_add, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)
    apply hG
    · rw [s1.1]; simp only [val_add, hq1]
    · rw [s1.2]; simp only [val_add, hr1]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]; simp only [val_add, val_lit, hq2, wrap_add_l, wrap_add_r]
    · rw [s2.2]; simp only [val_add, val_sub, val_lit, hr2, wrap_add_l, wrap_add_r, wrap_sub_l]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]
      simp only [Bool.false_or, ge_iff_le, jle, val_sub, val_wrap, val_lit, wrap_sub_l, wrap_sub_r,
        hq2, decide_eq_decide]
      rw [wrap_id ht (x := 2 ^ (t.bits - 1) - 1) (by omega) (by omega)]
      constructor <;> intro h <;> omega
  · rw [ite_eq_right (fun h => c1 (cond1.mp h)), ite_eq_right (fun h => c2 (cond2.mp h))]
    dsimp only
    have s1 := divmod_of_eq (x := (2 : Int) ^ (p + 1)) (c := nc.val)
      (q := 2 ^ p / nc.val + 2 ^ p / nc.val) (r := 2 ^ p % nc.val + 2 ^ p % nc.val)
      (by omega) (by rw [hX2, Int.mul_add]; omega) (by omega) (by omega)
    have s2 := divmod_of_eq (x := (2 : Int) ^ (p + 1) - 1) (c := d.val)
      (q := (2 ^ p - 1) / d.val + (2 ^ p - 1) / d.val)
      (r := (2 ^ p - 1) % d.val + (2 ^ p - 1) % d.val + 1)
      (by omega) (by rw [hX2, Int.mul_add]; omega) (by omega) (by omega)
    apply hG
    · rw [s1.1]; simp only [val_add, hq1]
    · rw [s1.2]; simp only [val_add, hr1]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]; simp only [val_add, hq2]
    · rw [s2.2]; simp only [val_add, val_lit, hr2, wrap_add_l, wrap_add_r]
      exact wrap_id ht (by omega) (by omega)
    · rw [s2.1]
      simp only [Bool.false_or, ge_iff_le, jle, val_wrap, hq2, decide_eq_decide]
      rw [wrap_id ht (x := 2 ^ (t.bits - 1)) (by omega) (by omega)]
      constructor <;> intro h <;> omega

/-- The loop invariant, by induction on the number `k = 2 * bits - p` of passes left: from exact
quotients and remainders at exponent `p` with `2^p < nc * d` (or `p = bits - 1`), the loop returns a
`Good` result. -/
theorem magicLoop_good {t : IntTy} (ht : t.signed = false) (d nc : JInt t) (K ρ : Int)
    (hD : 1 ≤ d.val) (hK : 1 ≤ K) (hnc : nc.val = K * d.val) (hρ1 : ρ < d.val)
    (hW : 2 ^ t.bits - 1 = nc.val + ρ) :
    ∀ (k p : Nat) (q1 r1 q2 r2 : JInt t), 2 * t.bits - p = k → t.bits ≤ p + 1 → p < 2 * t.bits →
      (p + 1 = t.bits ∨ (2 : Int) ^ p < nc.val * d.val) →
      q1.val = 2 ^ p / nc.val → r1.val = 2 ^ p % nc.val →
      q2.val = (2 ^ p - 1) / d.val → r2.val = (2 ^ p - 1) % d.val →
      Good t d nc.val (magicLoop t d nc p q1 r1 q2 r2 false) := by
  have hbits := bits_ge t
  obtain ⟨hD0, hDW⟩ := val_bounds_u ht d
  obtain ⟨hN0, hNW⟩ := val_bounds_u ht nc
  have hWH := two_pow_half t
  have hH := two_pow_half_ge t
  have hW0 := two_pow_pos t.bits
  have hND : d.val ≤ nc.val := by
    have := Int.mul_le_mul_of_nonneg_right hK hD0
    rw [Int.one_mul] at this
    omega
  intro k
  induction k with
  | zero => intro p q1 r1 q2 r2 hk _ hp1; omega
  | succ k ih =>
    intro p q1 r1 q2 r2 hk hp0 hp1 hpre hq1 hr1 hq2 hr2
    have hX := two_pow_pos p
    have hX2 := two_pow_succ p
    refine magicLoop_step ht d nc p q1 r1 q2 r2 hD (by omega) hq1 hr1 hq2 hr2
      (Good t d nc.val) ?_
    intro q1' r1' q2' r2' add' hq1' hr1' hq2' hr2' hadd'
    have f1 := Int.mul_ediv_add_emod ((2 : Int) ^ (p + 1)) nc.val
    have f1a := Int.emod_nonneg ((2 : Int) ^ (p + 1)) (by omega : nc.val ≠ 0)
    have f1b := Int.emod_lt_of_pos ((2 : Int) ^ (p + 1)) (by omega : 0 < nc.val)
    have f1c := Int.ediv_nonneg (Int.le_of_lt (two_pow_pos (p + 1))) hN0
    have f2a := Int.emod_nonneg ((2 : Int) ^ (p + 1) - 1) (by omega : d.val ≠ 0)
    have f2b := Int.emod_lt_of_pos ((2 : Int) ^ (p + 1) - 1) (by omega : 0 < d.val)
    have f2c := Int.ediv_nonneg (by omega : (0 : Int) ≤ 2 ^ (p + 1) - 1) hD0
    obtain ⟨e, he⟩ : ∃ e : Int, e = d.val - 1 - (2 ^ (p + 1) - 1) % d.val := ⟨_, rfl⟩
    have he0 : 0 ≤ e := by omega
    have he1 : e < d.val := by omega
    have hdv : (d - JInt.lit t 1 - r2').val = e := by
      simp only [val_sub, val_lit, wrap_sub_l, wrap_sub_r, hr2']
      rw [← he]
      exact wrap_id ht he0 (by omega)
    have hQ1 : p + 1 < 2 * t.bits → (2 : Int) ^ (p + 1) / nc.val < 2 ^ t.bits := by
      intro hp2
      apply (Int.ediv_lt_iff_lt_mul (by omega)).mpr
      rcases hpre with h | h
      · rw [h]
        have := Int.mul_le_mul_of_nonneg_left (show (2 : Int) ≤ nc.val by omega) (Int.le_of_lt hW0)
        omega
      · have hmax : (2 : Int) ^ (p + 1) ≤ 2 ^ t.bits * 2 ^ (t.bits - 1) := by
          rw [← Int.pow_add]
          exact two_pow_mono (by omega)
        rcases (show (2 : Int) ^ (p + 1) < 2 ^ t.bits * nc.val ∨
            2 ^ t.bits * nc.val ≤ 2 ^ (p + 1) by omega) with hlt | hcon
        · exact hlt
        · exfalso
          have h1 : 2 ^ t.bits * nc.val < (2 * d.val) * nc.val := by
            have e' : (2 * d.val) * nc.val = 2 * (nc.val * d.val) := by
              rw [Int.mul_assoc, Int.mul_comm d.val]
            rw [e']
            omega
          have h2 : 2 ^ t.bits < 2 * d.val := lt_of_mul_lt_right (by omega) h1
          have hK1 : K = 1 := by
            have h3 : K * d.val < 2 * d.val := by omega
            have := lt_of_mul_lt_right (by omega) h3
            omega
          rw [hK1, Int.one_mul] at hnc
          have h4 := Int.mul_le_mul_of_nonneg_left
            (show 2 ^ (t.bits - 1) + 1 ≤ d.val by omega) (Int.le_of_lt hW0)
          rw [Int.mul_add, Int.mul_one] at h4
          rw [hnc] at hcon
          omega
    apply good_ite
    · rintro ⟨hp2, hc⟩
      have hq1v : q1'.val = 2 ^ (p + 1) / nc.val := by rw [hq1', wrap_id ht f1c (hQ1 hp2)]
      have hc' : 2 ^ (p + 1) / nc.val < e ∨ (2 ^ (p + 1) / nc.val = e ∧ 2 ^ (p + 1) % nc.val = 0) := by
        rw [← hq1v, ← hdv, ← hr1']
        rcases hc with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨congrArg Subtype.val h1, h2⟩
      have hcont : (2 : Int) ^ (p + 1) < nc.val * d.val := by
        have hed := Int.mul_le_mul_of_nonneg_left (show e + 1 ≤ d.val by omega) hN0
        rw [Int.mul_add, Int.mul_one] at hed
        rcases hc' with h | ⟨h1, h2⟩
        · have := Int.mul_le_mul_of_nonneg_left (show 2 ^ (p + 1) / nc.val + 1 ≤ e by omega) hN0
          rw [Int.mul_add, Int.mul_one] at this
          omega
        · rw [h1] at f1
          omega
      have hQ2 : (2 ^ (p + 1) - 1) / d.val < nc.val :=
        (Int.ediv_lt_iff_lt_mul (by omega)).mpr (by omega)
      have hq2v : q2'.val = (2 ^ (p + 1) - 1) / d.val := by
        rw [hq2', wrap_id ht f2c (by omega)]
      have hadd0 : add' = false := by
        rw [hadd']
        exact decide_eq_false (by omega)
      subst hadd0
      exact ih (p + 1) q1' r1' q2' r2' (by omega) (by omega) hp2 (Or.inr hcont) hq1v hr1' hq2v hr2'
    · intro hc
      refine ⟨rfl, p, by omega, by omega, hpre, ?_, hadd', ?_, rfl⟩
      · show (q2' + JInt.lit t 1).val = _
        simp only [val_add, val_lit, hq2', wrap_add_l, wrap_add_r]
      · rw [← he]
        rcases Nat.lt_or_ge (p + 1) (2 * t.bits) with hp2 | hp2
        · have hq1v : q1'.val = 2 ^ (p + 1) / nc.val := by rw [hq1', wrap_id ht f1c (hQ1 hp2)]
          have hc' : ¬ (2 ^ (p + 1) / nc.val < e ∨
              (2 ^ (p + 1) / nc.val = e ∧ 2 ^ (p + 1) % nc.val = 0)) := by
            rw [← hq1v, ← hdv, ← hr1']
            rintro (h | ⟨h1, h2⟩)
            · exact hc ⟨hp2, Or.inl h⟩
            · exact hc ⟨hp2, Or.inr ⟨Subtype.ext h1, h2⟩⟩
          rw [Int.mul_comm]
          rcases (show e + 1 ≤ 2 ^ (p + 1) / nc.val ∨
              (2 ^ (p + 1) / nc.val = e ∧ 0 < 2 ^ (p + 1) % nc.val) by omega) with h | ⟨h1, h2⟩
          · have := Int.mul_le_mul_of_nonneg_left h hN0
            rw [Int.mul_add, Int.mul_one] at this
            omega
          · rw [h1] at f1
            omega
        · have hWW : (2 : Int) ^ (p + 1) = 2 ^ t.bits * 2 ^ t.bits := by
            rw [show p + 1 = t.bits + t.bits by omega, Int.pow_add]
          rw [hWW]
          have h1 := Int.mul_le_mul_of_nonneg_right (show e ≤ 2 ^ t.bits by omega) hN0
          have h2 := Int.mul_le_mul_of_nonneg_left (show nc.val + 1 ≤ 2 ^ t.bits by omega)
            (Int.le_of_lt hW0)
          rw [Int.mul_add, Int.mul_one] at h2
          omega

/-- `UnsignedMultiplicativeInverse(d)` returns a `Good` result for every nonzero `d`, where
`nc = K * d` is the largest multiple of `d` below `W` and `ρ = (W - 1) mod d`. -/
theorem unsignedMI_good {t : IntTy} (ht : t.signed = false) (d : JInt t) (hd : d.val ≠ 0) :
    ∃ (mi : UnsignedMI t) (K ρ nc : Int), unsignedMI d = .ok mi ∧ 1 ≤ K ∧ nc = K * d.val ∧
      0 ≤ ρ ∧ ρ < d.val ∧ 2 ^ t.bits - 1 = nc + ρ ∧ Good t d nc mi := by
  have hbits := bits_ge t
  obtain ⟨hD0, hDW⟩ := val_bounds_u ht d
  have hWH := two_pow_half t
  have hH := two_pow_half_ge t
  have hD : 1 ≤ d.val := by omega
  have hall : (JInt.lit t 0 - JInt.lit t 1).val = 2 ^ t.bits - 1 := by
    rw [val_sub, val_lit, val_lit, wrapInt_sub,
      show (0 : Int) - 1 = (2 ^ t.bits - 1) - 2 ^ t.bits by omega, wrap_sub_W ht,
      wrap_id ht (x := 2 ^ t.bits - 1) (by omega) (by omega)]
  have hamd : (JInt.lit t 0 - JInt.lit t 1 - d).val = 2 ^ t.bits - 1 - d.val := by
    rw [val_sub, hall, wrap_id ht (x := 2 ^ t.bits - 1 - d.val) (by omega) (by omega)]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Int, ρ = (2 ^ t.bits - 1 - d.val) % d.val := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact Int.emod_nonneg _ (by omega)
  have hρ1 : ρ < d.val := by rw [hρ]; exact Int.emod_lt_of_pos _ (by omega)
  have hK := Int.mul_ediv_add_emod (2 ^ t.bits - 1 - d.val) d.val
  have hK0 := Int.ediv_nonneg (show (0 : Int) ≤ 2 ^ t.bits - 1 - d.val by omega) hD0
  have hrem : (JInt.wrap t ((JInt.lit t 0 - JInt.lit t 1 - d).val.tmod d.val)).val = ρ := by
    rw [val_wrap, hamd, Int.tmod_eq_emod_of_nonneg (show (0 : Int) ≤ 2 ^ t.bits - 1 - d.val by omega),
      ← hρ, wrap_id ht hρ0 (by omega)]
  have hnc : (JInt.lit t 0 - JInt.lit t 1 -
      JInt.wrap t ((JInt.lit t 0 - JInt.lit t 1 - d).val.tmod d.val)).val = 2 ^ t.bits - 1 - ρ := by
    rw [val_sub, hall, hrem, wrap_id ht (x := 2 ^ t.bits - 1 - ρ) (by omega) (by omega)]
  have hnc0 : (JInt.lit t 0 - JInt.lit t 1 -
      JInt.wrap t ((JInt.lit t 0 - JInt.lit t 1 - d).val.tmod d.val)).val ≠ 0 := by
    rw [hnc]; omega
  have hsmin : (JInt.wrap t (2 ^ (t.bits - 1))).val = 2 ^ (t.bits - 1) := by
    rw [val_wrap, wrap_id ht (x := 2 ^ (t.bits - 1)) (by omega) (by omega)]
  have hsmax : (JInt.wrap t (2 ^ (t.bits - 1)) - JInt.lit t 1).val = 2 ^ (t.bits - 1) - 1 := by
    rw [val_sub, hsmin, val_lit, wrap_sub_r, wrap_id ht (x := 2 ^ (t.bits - 1) - 1) (by omega) (by omega)]
  have hncK : 2 ^ t.bits - 1 - ρ = ((2 ^ t.bits - 1 - d.val) / d.val + 1) * d.val := by
    rw [Int.add_mul, Int.one_mul, Int.mul_comm]
    omega
  unfold unsignedMI
  rw [ite_eq_right hd]
  dsimp only
  rw [remInt_ok _ _ hd]
  simp only [bind_ok]
  rw [div_ok ht _ _ hnc0]
  simp only [bind_ok]
  rw [remInt_ok _ _ hnc0]
  simp only [bind_ok]
  rw [div_ok ht _ _ hd]
  simp only [bind_ok]
  rw [remInt_ok _ _ hd]
  simp only [bind_ok]
  refine ⟨_, (2 ^ t.bits - 1 - d.val) / d.val + 1, ρ, 2 ^ t.bits - 1 - ρ, rfl, by omega, hncK, hρ0,
    hρ1, by omega, ?_⟩
  rw [← hnc]
  refine magicLoop_good ht d _ ((2 ^ t.bits - 1 - d.val) / d.val + 1) ρ hD (by omega)
    (by rw [hnc]; exact hncK) hρ1 (by rw [hnc]; omega) _ (t.bits - 1) _ _ _ _ rfl (by omega)
    (by omega) (Or.inl (by omega)) ?_ ?_ ?_ ?_
  · rw [val_wrap, hsmin, hnc, Int.tdiv_eq_ediv_of_nonneg (show (0 : Int) ≤ 2 ^ (t.bits - 1) by omega)]
    exact wrap_id ht (Int.ediv_nonneg (by omega) (by omega))
      (by have := Int.ediv_le_self (2 ^ t.bits - 1 - ρ) (show (0 : Int) ≤ 2 ^ (t.bits - 1) by omega)
          omega)
  · rw [val_wrap, hsmin, hnc, Int.tmod_eq_emod_of_nonneg (show (0 : Int) ≤ 2 ^ (t.bits - 1) by omega)]
    exact wrap_id ht (Int.emod_nonneg _ (by omega))
      (by have := Int.emod_lt_of_pos (2 ^ (t.bits - 1)) (show (0 : Int) < 2 ^ t.bits - 1 - ρ by omega)
          omega)
  · rw [val_wrap, hsmax,
      Int.tdiv_eq_ediv_of_nonneg (show (0 : Int) ≤ 2 ^ (t.bits - 1) - 1 by omega)]
    exact wrap_id ht (Int.ediv_nonneg (by omega) hD0)
      (by have := Int.ediv_le_self d.val (show (0 : Int) ≤ 2 ^ (t.bits - 1) - 1 by omega)
          omega)
  · rw [val_wrap, hsmax,
      Int.tmod_eq_emod_of_nonneg (show (0 : Int) ≤ 2 ^ (t.bits - 1) - 1 by omega)]
    exact wrap_id ht (Int.emod_nonneg _ (by omega))
      (by have := Int.emod_lt_of_pos (2 ^ (t.bits - 1) - 1) (show (0 : Int) < d.val by omega)
          omega)

/-! ### Division by the magic number -/

/-- `⌊A m / X⌋ = ⌊A / D⌋` for `0 ≤ A < W`, when `D m = X + e` with `0 ≤ e < D`, `W ∣ X`, and
`e * nc < X` for `nc = K D`, the largest multiple of `D` below `W`. -/
theorem magic_div {W D nc K ρ X m e A : Int} (hD : 0 < D) (hK : 1 ≤ K) (hnc : nc = K * D)
    (hρ1 : ρ < D) (hW : W - 1 = nc + ρ) (hX : 0 < X) (hWX : ∃ j, X = W * j)
    (hm : D * m = X + e) (he0 : 0 ≤ e) (he1 : e < D) (hen : e * nc < X) (hA0 : 0 ≤ A)
    (hA1 : A < W) : A * m / X = A / D := by
  have hq := Int.mul_ediv_add_emod A D
  have hr0 := Int.emod_nonneg A (by omega : D ≠ 0)
  have hr1 := Int.emod_lt_of_pos A hD
  obtain ⟨q, hqd⟩ : ∃ q, q = A / D := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = A % D := ⟨_, rfl⟩
  rw [← hqd, ← hrd] at hq
  rw [← hrd] at hr0 hr1
  rw [← hqd]
  have hDX : X ≤ (D - r) * X := by
    have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ D - r by omega) (Int.le_of_lt hX)
    rwa [Int.one_mul] at this
  have hND : D ≤ nc := by
    have := Int.mul_le_mul_of_nonneg_right hK (Int.le_of_lt hD)
    rw [Int.one_mul] at this
    omega
  have hen' : nc * e < X := by rw [Int.mul_comm]; exact hen
  have hqK : q ≤ K := by
    have h1 : D * q < D * (K + 1) := by
      rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
      omega
    have := lt_of_mul_lt hD h1
    omega
  have hkey : A * e < (D - r) * X := by
    rcases (show q < K ∨ q = K by omega) with hlt | heq
    · have h1 := Int.mul_le_mul_of_nonneg_left (show q ≤ K - 1 by omega) (Int.le_of_lt hD)
      rw [Int.mul_sub, Int.mul_one, Int.mul_comm D K] at h1
      have h2 := Int.mul_le_mul_of_nonneg_right (show A ≤ nc by omega) he0
      omega
    · rw [heq, Int.mul_comm] at hq
      rcases (show r = D - 1 ∨ r ≤ D - 2 by omega) with hr | hr
      · obtain ⟨j, hj⟩ := hWX
        have hWK : W = D * (K + 1) := by
          rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
          omega
        have h1 : D * (m - (K + 1) * j) = e := by
          rw [Int.mul_sub, ← Int.mul_assoc, ← hWK]
          omega
        have he : e = 0 := by
          rcases (show m - (K + 1) * j ≤ -1 ∨ m - (K + 1) * j = 0 ∨ 1 ≤ m - (K + 1) * j by omega)
            with h | h | h
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
          · rw [h, Int.mul_zero] at h1
            omega
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
        rw [he, Int.mul_zero]
        omega
      · have h1 := Int.mul_le_mul_of_nonneg_right (show r ≤ nc by omega) he0
        have h2 : A * e = nc * e + r * e := by
          rw [← hq, ← hnc, Int.add_mul]
        have h3 := Int.mul_le_mul_of_nonneg_right (show 2 ≤ D - r by omega) (Int.le_of_lt hX)
        omega
  have h1 : D * (A * m) = A * X + A * e := by rw [Int.mul_left_comm, hm, Int.mul_add]
  have h2 : A * X = D * (X * q) + r * X := by
    rw [← hq, Int.add_mul, Int.mul_assoc, Int.mul_comm q X]
  have h3 : (D - r) * X = D * X - r * X := Int.sub_mul _ _ _
  have h4 : D * (X * q + X) = D * (X * q) + D * X := Int.mul_add _ _ _
  have h5 := mul_nonneg' hr0 (Int.le_of_lt hX)
  have h6 := mul_nonneg' hA0 he0
  apply ediv_eq_of_bounds hX
  · apply le_of_mul_le hD
    omega
  · apply lt_of_mul_lt hD
    omega

/-- `div(a, mi)` for a `Good` unsigned inverse is `⌊a / d⌋`. -/
theorem umiDiv_val {t : IntTy} (ht : t.signed = false) (a d : JInt t) (mi : UnsignedMI t)
    (K ρ nc : Int) (hd : d.val ≠ 0) (hK : 1 ≤ K) (hnc : nc = K * d.val) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < d.val) (hW : 2 ^ t.bits - 1 = nc + ρ) (hgood : Good t d nc mi) :
    (umiDiv a mi).val = a.val / d.val := by
  obtain ⟨hdiv, p, hp0, hp1, hpre, hmult, hadd, hstop, hshift⟩ := hgood
  have hbits := bits_ge t
  have hbits' := bits_le t
  obtain ⟨hA0, hAW⟩ := val_bounds_u ht a
  obtain ⟨hD0, hDW⟩ := val_bounds_u ht d
  have hWH := two_pow_half t
  have hH := two_pow_half_ge t
  have hW0 := two_pow_pos t.bits
  have hX2 := two_pow_succ p
  have hXp := two_pow_pos (p + 1)
  unfold umiDiv
  dsimp only
  rw [hdiv]
  by_cases hD1 : d.val = 1
  · rw [ite_eq_left hD1, hD1, Int.ediv_one]
  rw [ite_eq_right hD1]
  have f2 := Int.mul_ediv_add_emod ((2 : Int) ^ (p + 1) - 1) d.val
  have f2a := Int.emod_nonneg ((2 : Int) ^ (p + 1) - 1) (by omega : d.val ≠ 0)
  have f2b := Int.emod_lt_of_pos ((2 : Int) ^ (p + 1) - 1) (by omega : 0 < d.val)
  have f2c := Int.ediv_nonneg (show (0 : Int) ≤ 2 ^ (p + 1) - 1 by omega) hD0
  obtain ⟨m, hm⟩ : ∃ m : Int, m = ((2 : Int) ^ (p + 1) - 1) / d.val + 1 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Int, e = d.val - 1 - ((2 : Int) ^ (p + 1) - 1) % d.val := ⟨_, rfl⟩
  rw [← hm] at hmult hadd
  rw [← he] at hstop
  have hDm : d.val * m = 2 ^ (p + 1) + e := by
    rw [hm, Int.mul_add, Int.mul_one]
    omega
  have hXs : (2 : Int) ^ (p + 1) = 2 ^ t.bits * 2 ^ (p + 1 - t.bits) := by
    rw [← Int.pow_add, show t.bits + (p + 1 - t.bits) = p + 1 by omega]
  have hmW : p + 1 = t.bits → m < 2 ^ t.bits := by
    intro h
    rw [h] at hDm
    rcases (show m < 2 ^ t.bits ∨ 2 ^ t.bits ≤ m by omega) with h' | h'
    · exact h'
    · have := Int.mul_le_mul_of_nonneg_left h' hD0
      have := Int.mul_le_mul_of_nonneg_right (show 2 ≤ d.val by omega) (Int.le_of_lt hW0)
      omega
  have hm2 : m < 2 * 2 ^ t.bits := by
    rcases hpre with h | h
    · have := hmW h
      omega
    · have h1 : d.val * m < d.val * (2 * nc + 1) := by
        rw [Int.mul_add, Int.mul_one, Int.mul_left_comm, Int.mul_comm d.val nc]
        omega
      have := lt_of_mul_lt (by omega) h1
      omega
  have hAm : 0 ≤ a.val * m := mul_nonneg' hA0 (by omega)
  obtain ⟨Y, hY⟩ : ∃ Y : Int, Y = a.val * m / 2 ^ t.bits := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact Int.ediv_nonneg hAm (Int.le_of_lt hW0)
  have hfin : Y / 2 ^ (p + 1 - t.bits) = a.val / d.val := by
    rw [hY, ediv_ediv hW0, ← hXs]
    exact magic_div (by omega) hK hnc hρ1 hW hXp ⟨_, hXs⟩ hDm (by omega) (by omega) hstop hA0 hAW
  have hqW : a.val / d.val < 2 ^ t.bits := by
    have := Int.ediv_le_self d.val hA0
    omega
  have hq0 := Int.ediv_nonneg hA0 hD0
  rcases (show 2 ^ t.bits ≤ m ∨ m < 2 ^ t.bits by omega) with hWm | hWm
  · have hb : mi.add = true := by rw [hadd]; exact decide_eq_true hWm
    have hp2 : t.bits ≤ p := by
      rcases Nat.lt_or_ge p t.bits with h | h
      · have := hmW (by omega)
        omega
      · exact h
    have hs : mi.shift = p - t.bits := by
      rw [hshift, hb, ite_eq_left rfl,
        show ((p + 1 : Nat) : Int) - (t.bits : Int) - 1 = ((p - t.bits : Nat) : Int) by omega,
        wrapInt_of_inRange .u8 _ (u8_in _ (by omega))]
      simp
    have hmv : mi.multiplier.val = m - 2 ^ t.bits := by
      rw [hmult, ← wrap_sub_W ht m]
      exact wrap_id ht (by omega) (by omega)
    have hsplit : a.val * (m - 2 ^ t.bits) = a.val * m + (-a.val) * 2 ^ t.bits := by
      rw [Int.mul_sub, Int.neg_mul]
      omega
    have hYA : a.val ≤ Y := by
      rw [hY]
      apply (Int.le_ediv_iff_mul_le hW0).mpr
      exact Int.mul_le_mul_of_nonneg_left hWm hA0
    have hY2 : Y ≤ 2 * a.val := by
      have : Y < 2 * a.val + 1 := by
        rw [hY]
        apply (Int.ediv_lt_iff_lt_mul hW0).mpr
        have h1 := Int.mul_le_mul_of_nonneg_left (show m ≤ 2 * 2 ^ t.bits by omega) hA0
        rw [Int.mul_left_comm] at h1
        rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
        omega
      omega
    have hhi : (mulHi a mi.multiplier).val = Y - a.val := by
      show wrapInt t (a.val * mi.multiplier.val / 2 ^ t.bits) = _
      rw [hmv, hsplit, Int.add_mul_ediv_right _ _ (by omega : (2 : Int) ^ t.bits ≠ 0), ← hY,
        show Y + -a.val = Y - a.val by omega]
      exact wrap_id ht (by omega) (by omega)
    have hsub : (a - mulHi a mi.multiplier).val = 2 * a.val - Y := by
      rw [val_sub, hhi, show a.val - (Y - a.val) = 2 * a.val - Y by omega]
      exact wrap_id ht (by omega) (by omega)
    have hsh : (shr (a - mulHi a mi.multiplier) 1).val = (2 * a.val - Y) / 2 := by
      show wrapInt t ((a - mulHi a mi.multiplier).val / 2 ^ 1) = _
      rw [hsub, Int.pow_one]
      exact wrap_id ht (by omega) (by omega)
    have hx : (shr (a - mulHi a mi.multiplier) 1 + mulHi a mi.multiplier).val = Y / 2 := by
      rw [val_add, hsh, hhi, show (2 * a.val - Y) / 2 + (Y - a.val) = Y / 2 by omega]
      exact wrap_id ht (by omega) (by omega)
    rw [ite_eq_left hb]
    show wrapInt t ((shr (a - mulHi a mi.multiplier) 1 + mulHi a mi.multiplier).val /
      2 ^ mi.shift) = _
    rw [hx, hs, ediv_ediv (by decide), ← two_pow_succ, show p - t.bits + 1 = p + 1 - t.bits by omega,
      hfin]
    exact wrap_id ht hq0 hqW
  · have hb : mi.add = false := by rw [hadd]; exact decide_eq_false (by omega)
    have hs : mi.shift = p + 1 - t.bits := by
      rw [hshift, hb, ite_eq_right (by decide),
        show ((p + 1 : Nat) : Int) - (t.bits : Int) - 0 = ((p + 1 - t.bits : Nat) : Int) by omega,
        wrapInt_of_inRange .u8 _ (u8_in _ (by omega))]
      simp
    have hmv : mi.multiplier.val = m := by
      rw [hmult]
      exact wrap_id ht (by omega) hWm
    have hYW : Y < 2 ^ t.bits := by
      rw [hY]
      apply (Int.ediv_lt_iff_lt_mul hW0).mpr
      have h1 := Int.mul_le_mul_of_nonneg_left (show m ≤ 2 ^ t.bits by omega) hA0
      have h2 := Int.mul_le_mul_of_nonneg_right (show a.val + 1 ≤ 2 ^ t.bits by omega)
        (Int.le_of_lt hW0)
      rw [Int.add_mul, Int.one_mul] at h2
      omega
    have hhi : (mulHi a mi.multiplier).val = Y := by
      show wrapInt t (a.val * mi.multiplier.val / 2 ^ t.bits) = _
      rw [hmv, ← hY]
      exact wrap_id ht hY0 hYW
    rw [ite_eq_right (show ¬ (mi.add = true) by rw [hb]; decide)]
    show wrapInt t ((mulHi a mi.multiplier).val / 2 ^ mi.shift) = _
    rw [hhi, hs, hfin]
    exact wrap_id ht hq0 hqW

end Umi

open Umi

/-- `UnsignedMultiplicativeInverse(d)` returns for every nonzero `d`, and `div(a, mi)` and
`rem(a, mi)` equal `div(a, d)` and `rem(a, d)` for every dividend `a`. -/
theorem umiDivCorrect : UmiDivCorrect := by
  intro t ht a d hd
  obtain ⟨mi, K, ρ, nc, hmi, hK, hnc, hρ0, hρ1, hW, hgood⟩ := unsignedMI_good ht d hd
  have hq := umiDiv_val ht a d mi K ρ nc hd hK hnc hρ0 hρ1 hW hgood
  obtain ⟨hA0, hAW⟩ := val_bounds_u ht a
  obtain ⟨hD0, hDW⟩ := val_bounds_u ht d
  have hqW : a.val / d.val < 2 ^ t.bits := by
    have := Int.ediv_le_self d.val hA0
    omega
  have hq0 := Int.ediv_nonneg hA0 hD0
  refine ⟨mi, hmi, ?_, ?_⟩
  · rw [div_ok ht _ _ hd]
    congr 1
    apply Subtype.ext
    rw [hq, val_wrap, Int.tdiv_eq_ediv_of_nonneg hA0, wrap_id ht hq0 hqW]
  · rw [remInt_ok _ _ hd]
    congr 1
    apply Subtype.ext
    unfold umiRem
    rw [val_sub, val_mul, hq, hgood.1, wrap_sub_r, val_wrap, Int.tmod_eq_emod_of_nonneg hA0,
      Int.emod_def, Int.mul_comm]

end JuliaLean.ReinterpretArrays
