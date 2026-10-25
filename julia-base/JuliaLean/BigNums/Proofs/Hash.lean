import JuliaLean.BigNums.Proofs.Convert

/-!
`hash(big(x)) == hash(x)` for `Int64`/`UInt64` (`HashBigMatchesSmall`) and `Int128`/`UInt128`
(`HashBigMatches128`). The single-limb branches of `hashBig` are the integer hashes; on the
general branch the trailing-zero count, digit count and limb window coincide with
`decompose`-based `hashReal`, and the byte-hash tail is `hashReal`'s `num << (pow % 8)` term.
-/

namespace JuliaLean.BigNums.HashProofs

open JuliaLean JuliaLean.Promotion JuliaLean.BigNums.ConvProofs

/-- Unfold `wrapInt`/`limb` on a concrete type and evaluate the literal arithmetic. -/
local macro "wsimp" : tactic => `(tactic| simp only [limb, wrapInt, IntTy.signed, IntTy.bits,
  IntTy.min, IntTy.max, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, Nat.reducePow,
  Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Int.reducePow, Nat.pow_zero,
  Nat.div_one, Nat.mul_zero, Nat.mul_one, Int.reduceAdd, Int.reduceMod, Int.reduceSub,
  Int.reduceNeg, Int.reduceMul] at *)

/-! ## Closed float facts -/

theorem hashF64_zero (h : HTerm) : hashF64 (Fl.zero false : Fl double) h = hashI64 0 h := by
  simp only [hashF64]
  split
  next h1 =>
    split
    next h2 => exact congrArg (fun v => hashI64 v h) (by decide +kernel)
    next h2 => exact absurd h2 (by decide +kernel)
  next h1 => exact absurd h1 (by decide +kernel)

theorem hashF64_min (h : HTerm) :
    hashF64 (Fl.roundRat (-9223372036854775808) 1 false : Fl double) h =
      hashI64 (-9223372036854775808) h := by
  simp only [hashF64]
  split
  next h1 =>
    split
    next h2 => exact congrArg (fun v => hashI64 v h) (by decide +kernel)
    next h2 => exact absurd h2 (by decide +kernel)
  next h1 => exact absurd h1 (by decide +kernel)

/-! ## Trailing zeros -/

theorem tzgo_eq (m k : Nat) : trailingZerosBig.go m k = trailingZeros.go m k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp only [trailingZerosBig.go, trailingZeros.go, ih]

theorem tz_stable : ∀ (k m : Nat), m < 2 ^ k → ∀ j,
    trailingZeros.go m (k + j) = trailingZeros.go m k
  | 0, m, hm, j => by
    have : m = 0 := by simp at hm; omega
    subst this
    cases j <;> simp [trailingZeros.go]
  | k + 1, m, hm, j => by
    have hm2 : m / 2 < 2 ^ k := by rw [Nat.pow_succ] at hm; omega
    rw [show k + 1 + j = (k + j) + 1 by omega]
    simp only [trailingZeros.go, tz_stable k (m / 2) hm2 j]

theorem tz_dvd : ∀ (k m : Nat), m ≠ 0 → m < 2 ^ k → 2 ^ trailingZeros.go m k ∣ m
  | 0, m, h0, hm => by simp at hm; omega
  | k + 1, m, h0, hm => by
    have hm2 : m / 2 < 2 ^ k := by rw [Nat.pow_succ] at hm; omega
    simp only [trailingZeros.go]
    split
    · simp
    · rename_i hc
      have he : m % 2 = 0 := by simp at hc; omega
      have ih := tz_dvd k (m / 2) (by omega) hm2
      rw [Nat.pow_add, Nat.pow_one]
      exact Nat.dvd_trans (Nat.mul_dvd_mul_left 2 ih) ⟨1, by omega⟩

theorem tzBig_dvd (x : Int) (hx0 : x ≠ 0) : 2 ^ trailingZerosBig x ∣ x.natAbs := by
  unfold trailingZerosBig
  rw [tzgo_eq]
  exact tz_dvd _ _ (Int.natAbs_ne_zero.mpr hx0) Nat.lt_log2_self

theorem tz_spec (x : Int) (hx0 : x ≠ 0) (hx : x.natAbs < 2 ^ 128) :
    trailingZerosBig x = trailingZeros x ∧ 2 ^ trailingZeros x ∣ x.natAbs := by
  have hm0 : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
  have hl : x.natAbs.log2 < 128 := (Nat.log2_lt hm0).2 hx
  have hst := tz_stable (x.natAbs.log2 + 1) x.natAbs Nat.lt_log2_self
    (200 - (x.natAbs.log2 + 1))
  rw [show x.natAbs.log2 + 1 + (200 - (x.natAbs.log2 + 1)) = 200 by omega] at hst
  unfold trailingZerosBig trailingZeros
  rw [tzgo_eq, hst]
  exact ⟨rfl, tz_dvd _ _ hm0 Nat.lt_log2_self⟩

theorem log2_mul_pow {M : Nat} (j : Nat) (hM : 0 < M) : (M * 2^j).log2 = M.log2 + j := by
  have h1 : 2^M.log2 ≤ M := Nat.log2_self_le (by omega)
  have h2 : M < 2^(M.log2+1) := Nat.lt_log2_self
  have hne : M * 2^j ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos hM (Nat.two_pow_pos j))
  have a1 : M * 2^j < 2^(M.log2 + j + 1) := by
    rw [show M.log2 + j + 1 = (M.log2 + 1) + j by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos j)
  have a2 : 2^(M.log2 + j) ≤ M * 2^j := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ h1
  have b1 := (Nat.log2_lt hne).mpr a1
  have b2 : ¬ (M * 2^j).log2 < M.log2 + j := fun h =>
    absurd a2 (Nat.not_le.mpr ((Nat.log2_lt hne).mp h))
  omega

/-! ## The limb window -/

theorem mulmod (A c M : Nat) : (A % M * c) % M = (A * c) % M := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem shift_div (A B s : Nat) (hs : s ≤ 64) :
    (B + A * 2 ^ 64) / 2 ^ s = A * 2 ^ (64 - s) + B / 2 ^ s := by
  rw [show A * 2 ^ 64 = A * 2 ^ (64 - s) * 2 ^ s by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hs]]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos s)]
  exact Nat.add_comm _ _

theorem lw_eq (m p : Nat) :
    (if p % 64 = 0 then m / 2 ^ (64 * (p / 64)) % 2 ^ 64
     else (m / 2 ^ (64 * (p / 64 + 1)) % 2 ^ 64 * 2 ^ (64 - p % 64) % 2 ^ 64 +
       m / 2 ^ (64 * (p / 64)) % 2 ^ 64 / 2 ^ (p % 64)) % 2 ^ 64) = m / 2 ^ p % 2 ^ 64 := by
  have hp : p = 64 * (p / 64) + p % 64 := (Nat.div_add_mod p 64).symm
  have hmp : m / 2 ^ p = m / 2 ^ (64 * (p / 64)) / 2 ^ (p % 64) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← hp]
  have hm1 : m / 2 ^ (64 * (p / 64 + 1)) = m / 2 ^ (64 * (p / 64)) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * (p / 64 + 1) = 64 * (p / 64) + 64 by omega]
  rw [hmp, hm1]
  generalize m / 2 ^ (64 * (p / 64)) = N
  split
  · rename_i h0; rw [h0, Nat.pow_zero, Nat.div_one]
  · have hs : p % 64 ≤ 64 := by omega
    rw [Nat.add_mod (N / 2 ^ 64 % 2 ^ 64 * 2 ^ (64 - p % 64) % 2 ^ 64), Nat.mod_mod, mulmod,
      ← Nat.add_mod, ← shift_div (N / 2 ^ 64) (N % 2 ^ 64) (p % 64) hs]
    congr 2
    rw [Nat.mul_comm]
    exact Nat.mod_add_div N _

/-! ## hashBig on its branches -/

theorem hashBig_zero (h : HTerm) : hashBig 0 h = hashI64 0 h := by
  unfold hashBig; simp [size, nlimbs]

theorem hashBig_pos (x : Int) (h : HTerm) (h0 : 0 < x) (h1 : x < 2 ^ 64) :
    hashBig x h = .u64 x.toNat h := by
  have ha := Int.natAbs_eq x
  have hiff : nlimbs x ≤ 1 ↔ x.natAbs < 2 ^ 64 := nlimbs_le_iff x 1
  have hn : nlimbs x = 1 := by
    have h2 := nlimbs_pos x (by omega)
    have h3 := hiff.2 (by generalize x.natAbs = n at *; omega)
    omega
  have hs : size x = 1 := by unfold size; rw [if_neg (by omega), hn]; rfl
  have hl : limb x 0 = x.toNat := by
    simp only [limb, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    generalize x.natAbs = n at *; omega
  unfold hashBig; dsimp only
  rw [hs, if_neg (by decide), if_pos rfl, hl]

theorem hashBig_neg (x : Int) (h : HTerm) (h0 : x < 0) (h1 : -2 ^ 63 ≤ x) :
    hashBig x h = hashI64 x h := by
  have ha := Int.natAbs_eq x
  have hiff : nlimbs x ≤ 1 ↔ x.natAbs < 2 ^ 64 := nlimbs_le_iff x 1
  have hn : nlimbs x = 1 := by
    have h2 := nlimbs_pos x (by omega)
    have h3 := hiff.2 (by generalize x.natAbs = n at *; omega)
    omega
  have hs : size x = -1 := by unfold size; rw [if_pos h0, hn]; rfl
  have hl : limb x 0 = x.natAbs := by
    simp only [limb, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    generalize x.natAbs = n at *; omega
  have hl2 : limb x 0 ≤ 2 ^ 63 := by rw [hl]; generalize x.natAbs = n at *; omega
  unfold hashBig; dsimp only
  rw [hs, if_neg (by decide), if_neg (by decide), if_pos ⟨rfl, hl2⟩, hl]
  congr 1
  generalize x.natAbs = n at *; omega

theorem hashBig_big (x : Int) (h : HTerm) (hbig : 2 ^ 64 ≤ x ∨ x < -2 ^ 63) :
    hashBig x h =
      if x.natAbs.log2 + 1 ≤ 1024 ∧ x.natAbs.log2 + 1 - trailingZerosBig x ≤ 53 then
        hashF64 (Fl.roundRat x 1 false) h
      else HTerm.int ((if x < 0 then -1 else 1) *
          ((x.natAbs / 2 ^ (8 * (trailingZerosBig x / 8)) : Nat) : Int))
        (HTerm.int (trailingZerosBig x) h) := by
  have hx0 : x ≠ 0 := by omega
  have ha := Int.natAbs_eq x
  have hp := nlimbs_pos x hx0
  have hiff : nlimbs x ≤ 1 ↔ x.natAbs < 2 ^ 64 := nlimbs_le_iff x 1
  have hsz : size x = if x < 0 then -(nlimbs x : Int) else nlimbs x := rfl
  have hlimb : limb x 0 = x.natAbs % 2 ^ 64 := by simp [limb]
  have hs0 : ¬ size x = 0 := by rw [hsz]; split <;> omega
  have hs1 : ¬ size x = 1 := by
    rw [hsz]; split
    · omega
    · have : ¬ nlimbs x ≤ 1 := fun hn => by
        have := hiff.1 hn; generalize x.natAbs = n at *; omega
      omega
  have hs2 : ¬ (size x = -1 ∧ limb x 0 ≤ 2 ^ 63) := by
    rintro ⟨c1, c2⟩
    rw [hsz] at c1
    split at c1
    · have hn : nlimbs x ≤ 1 := by omega
      have := hiff.1 hn
      rw [hlimb] at c2
      generalize x.natAbs = n at *; omega
    · omega
  have hdvd := tzBig_dvd x hx0
  unfold hashBig; dsimp only
  rw [if_neg hs0, if_neg hs1, if_neg hs2]
  split
  · congr 2
    simp only [limb]
    rw [lw_eq]
    generalize trailingZerosBig x = P at *
    have hlt : x.natAbs / 2 ^ P < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      calc x.natAbs < 2 ^ (x.natAbs.log2 + 1) := Nat.lt_log2_self
        _ ≤ 2 ^ (P + 64) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ P * 2 ^ 64 := Nat.pow_add _ _ _
    rw [Nat.mod_eq_of_lt hlt]
    have hc : ((x.natAbs / 2 ^ P : Nat) : Int) * 2 ^ P = (x.natAbs : Int) := by
      have := Nat.div_mul_cancel hdvd
      exact_mod_cast this
    split
    · rw [Int.neg_mul, hc]; omega
    · rw [hc]; omega
  · rfl

/-! ## hashReal on integers -/

theorem num_eq (x : Int) (P q : Nat) (hx0 : x ≠ 0) (hq : x.natAbs = 2 ^ P * q) :
    x / 2 ^ P = if x < 0 then -(q : Int) else q := by
  have hpow : (2 : Int) ^ P ≠ 0 := by
    have : (0 : Int) < 2 ^ P := by have := Nat.two_pow_pos P; exact_mod_cast this
    omega
  have hm0 : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
  rcases Int.natAbs_eq x with hx | hx
  · have hpos : ¬ x < 0 := by
      rw [hx]; generalize x.natAbs = n; omega
    rw [if_neg hpos, hx, hq]; push_cast; exact Int.mul_ediv_cancel_left _ hpow
  · have hneg : x < 0 := by generalize x.natAbs = n at hx hm0; omega
    rw [if_pos hneg, hx, hq]; push_cast; rw [← Int.mul_neg]
    exact Int.mul_ediv_cancel_left _ hpow

theorem hashReal_nf (t : IntTy) (x : Int) (h : HTerm) (hx0 : x ≠ 0)
    (hm : x.natAbs < 2 ^ 128) :
    hashReal t (x, 0, 1) h =
      if x.natAbs.log2 + 1 ≤ 63 then hashI64 x h
      else if x.natAbs.log2 + 1 ≤ 64 ∧ 0 ≤ x then HTerm.u64 x.toNat h
      else if x.natAbs.log2 + 1 ≤ 1024 ∧ x.natAbs.log2 + 1 - trailingZeros x ≤ 53 then
        hashF64 (Fl.roundRat x 1 false) h
      else HTerm.int (if 0 < trailingZeros x then
          wrapInt t (x / 2 ^ trailingZeros x * 2 ^ (trailingZeros x % 8))
          else x / 2 ^ trailingZeros x)
        (HTerm.int (trailingZeros x) h) := by
  have ha := Int.natAbs_eq x
  obtain ⟨-, hdvd⟩ := tz_spec x hx0 hm
  have t1 : trailingZeros 1 = 0 := by decide
  have hm0 : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, Nat.mul_zero] at hq; exact absurd hq hm0
    · exact h0
  have hlog : x.natAbs.log2 = q.log2 + trailingZeros x := by
    rw [hq, Nat.mul_comm]; exact log2_mul_pow _ hq0
  have hnum := num_eq x (trailingZeros x) q hx0 hq
  have hnd : ndigits2 (x / 2 ^ trailingZeros x) = ((q.log2 + 1 : Nat) : Int) := by
    rw [hnum]; unfold ndigits2; split <;> simp [show q ≠ 0 by omega]
  have hFa : x / 2 ^ trailingZeros x * 2 ^ trailingZeros x = x := by
    have hdz : (2 : Int) ^ trailingZeros x ∣ x := Int.natAbs_dvd_natAbs.mp (by
      rw [Int.natAbs_pow]; exact ⟨q, hq⟩)
    exact Int.ediv_mul_cancel hdz
  have hsgn : 0 ≤ x / 2 ^ trailingZeros x ↔ 0 ≤ x := by
    rw [hnum]; split <;> omega
  simp [hashReal, hx0, t1, hashExactF64, hFa, hnd, hsgn]
  have hk8 : ((trailingZeros x : Int) % 8).toNat = trailingZeros x % 8 := by omega
  rw [hk8, hlog]
  generalize trailingZeros x = p at *
  refine ite_congr (propext ⟨fun _ => by omega, fun _ => by omega⟩) (fun _ => rfl) (fun _ => ?_)
  refine ite_congr (propext ⟨fun _ => by omega, fun _ => by omega⟩) (fun _ => rfl) (fun _ => ?_)
  exact ite_congr (propext ⟨fun _ => by omega, fun _ => by omega⟩) (fun _ => rfl) (fun _ => rfl)

theorem hashI64_nonneg (x : Int) (h : HTerm) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) :
    hashI64 x h = .u64 x.toNat h := by
  unfold hashI64; congr 1; wsimp; omega

theorem log2_lt_iff (x : Int) (hx0 : x ≠ 0) (k : Nat) :
    x.natAbs.log2 + 1 ≤ k ↔ x.natAbs < 2 ^ k := by
  rw [← Nat.log2_lt (Int.natAbs_ne_zero.mpr hx0)]; omega

theorem tail_eq (t : IntTy) (ht : t = .i128 ∨ t = .u128) (x : Int)
    (hxr : t.min ≤ x ∧ x ≤ t.max) (hx0 : x ≠ 0) (P : Nat) (hdvd : 2 ^ P ∣ x.natAbs) :
    (if x < 0 then -1 else 1) * ((x.natAbs / 2 ^ (8 * (P / 8)) : Nat) : Int) =
      if 0 < P then wrapInt t (x / 2 ^ P * 2 ^ (P % 8)) else x / 2 ^ P := by
  have ha := Int.natAbs_eq x
  obtain ⟨q, hq⟩ := hdvd
  have hnum := num_eq x P q hx0 hq
  have hsplit : 2 ^ P = 2 ^ (8 * (P / 8)) * 2 ^ (P % 8) := by
    rw [← Nat.pow_add, Nat.div_add_mod]
  have hdiv8 : x.natAbs / 2 ^ (8 * (P / 8)) = q * 2 ^ (P % 8) := by
    rw [hq, hsplit, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_comm]
  have hr : q * 2 ^ (P % 8) ≤ x.natAbs := by rw [← hdiv8]; exact Nat.div_le_self _ _
  have hcast : (q : Int) * 2 ^ (P % 8) ≤ (x.natAbs : Int) := by exact_mod_cast hr
  have hR0 : (0 : Int) ≤ (q : Int) * 2 ^ (P % 8) := by
    exact_mod_cast Nat.zero_le (q * 2 ^ (P % 8))
  rw [hdiv8, hnum]
  push_cast
  by_cases hneg : x < 0
  · simp only [hneg, ↓reduceIte, Int.neg_mul, Int.one_mul]
    split
    · have hin : t.min ≤ -((q : Int) * 2 ^ (P % 8)) ∧ -((q : Int) * 2 ^ (P % 8)) ≤ t.max := by
        generalize (q : Int) * 2 ^ (P % 8) = R at *
        generalize x.natAbs = n at *
        rcases ht with rfl | rfl <;> wsimp <;> omega
      rw [wrapInt_of_inRange t _ hin]
    · have : P = 0 := by omega
      subst this; simp
  · simp only [hneg, ↓reduceIte, Int.one_mul]
    split
    · have hin : t.min ≤ (q : Int) * 2 ^ (P % 8) ∧ (q : Int) * 2 ^ (P % 8) ≤ t.max := by
        generalize (q : Int) * 2 ^ (P % 8) = R at *
        generalize x.natAbs = n at *
        rcases ht with rfl | rfl <;> wsimp <;> omega
      rw [wrapInt_of_inRange t _ hin]
    · have : P = 0 := by omega
      subst this; simp

theorem hash128 (t : IntTy) (ht : t = .i128 ∨ t = .u128) (x : Int)
    (hxr : t.min ≤ x ∧ x ≤ t.max) (h : HTerm) : hashBig x h = hashReal t (x, 0, 1) h := by
  have hr' : -2 ^ 127 ≤ x ∧ x < 2 ^ 128 := by
    have := hxr; rcases ht with rfl | rfl <;> wsimp <;> omega
  by_cases hx0 : x = 0
  · subst hx0
    rw [hashBig_zero, show hashReal t (0, 0, 1) h = hashF64 (Fl.zero false) h by simp [hashReal]]
    exact (hashF64_zero h).symm
  have ha := Int.natAbs_eq x
  have hm : x.natAbs < 2 ^ 128 := by generalize x.natAbs = n at *; omega
  obtain ⟨hpz, hdvd⟩ := tz_spec x hx0 hm
  rw [hashReal_nf t x h hx0 hm]
  have l63 := log2_lt_iff x hx0 63
  have l64 := log2_lt_iff x hx0 64
  by_cases c1 : 0 < x ∧ x < 2 ^ 64
  · rw [hashBig_pos x h c1.1 c1.2]
    by_cases c2 : x < 2 ^ 63
    · rw [if_pos (l63.2 (by generalize x.natAbs = n at *; omega))]
      exact (hashI64_nonneg x h (by omega) (by omega)).symm
    · rw [if_neg (fun hc => by have := l63.1 hc; generalize x.natAbs = n at *; omega),
        if_pos ⟨l64.2 (by generalize x.natAbs = n at *; omega), by omega⟩]
  by_cases c3 : x < 0 ∧ -2 ^ 63 < x
  · rw [hashBig_neg x h c3.1 (by omega), if_pos (l63.2 (by generalize x.natAbs = n at *; omega))]
  by_cases c4 : x = -9223372036854775808
  · subst c4
    rw [hashBig_neg _ h (by decide) (by decide)]
    have e1 : (-9223372036854775808 : Int).natAbs.log2 = 63 := by
      rw [show (-9223372036854775808 : Int).natAbs = 2 ^ 63 from rfl]; exact Nat.log2_two_pow
    have e2 : trailingZeros (-9223372036854775808) = 63 := by decide +kernel
    rw [e1, e2, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    exact (hashF64_min h).symm
  have hbig : 2 ^ 64 ≤ x ∨ x < -2 ^ 63 := by omega
  have n63 : ¬ (x.natAbs.log2 + 1 ≤ 63) := fun hc => by
    have := l63.1 hc; generalize x.natAbs = n at *; omega
  have n64 : ¬ (x.natAbs.log2 + 1 ≤ 64 ∧ 0 ≤ x) := fun hc => by
    have := l64.1 hc.1; generalize x.natAbs = n at *; omega
  rw [hashBig_big x h hbig, hpz, if_neg n63, if_neg n64]
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  congr 1
  exact tail_eq t ht x hxr hx0 _ hdvd

theorem i64_range (x : Int) (hx : IntTy.min .i64 ≤ x ∧ x ≤ IntTy.max .i64) :
    -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  wsimp; omega

theorem u64_range (x : Int) (hx : IntTy.min .u64 ≤ x ∧ x ≤ IntTy.max .u64) :
    0 ≤ x ∧ x < 2 ^ 64 := by
  wsimp; omega

end JuliaLean.BigNums.HashProofs

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion HashProofs

theorem hashBigMatchesSmall_proven : HashBigMatchesSmall := by
  intro h
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ => ?_⟩
  · show hashBig x h = hashI64 x h
    have hx' := i64_range x hx
    rcases (by omega : x = 0 ∨ 0 < x ∨ x < 0) with h0 | h0 | h0
    · subst h0; exact hashBig_zero h
    · rw [hashBig_pos x h h0 (by omega), hashI64_nonneg x h (by omega) (by omega)]
    · exact hashBig_neg x h h0 (by omega)
  · show hashBig x h = HTerm.u64 x.toNat h
    have hx' := u64_range x hx
    rcases (by omega : x = 0 ∨ 0 < x) with h0 | h0
    · subst h0; rw [hashBig_zero, hashI64_nonneg 0 h (by decide) (by decide)]
    · exact hashBig_pos x h h0 (by omega)

theorem hashBigMatches128_proven : HashBigMatches128 := by
  intro h
  exact ⟨fun ⟨x, hx⟩ => hash128 .i128 (.inl rfl) x hx h,
    fun ⟨x, hx⟩ => hash128 .u128 (.inr rfl) x hx h⟩

end JuliaLean.BigNums
