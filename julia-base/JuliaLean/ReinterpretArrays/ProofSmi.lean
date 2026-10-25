import JuliaLean.ReinterpretArrays.MultInvProps
import JuliaLean.ReinterpretArrays.ProofIndex
import JuliaLean.ReinterpretArrays.Wrap

/-!
Proofs of `SmiDivCorrect` and `SmiRemModCorrect`: the constructor of
`SignedMultiplicativeInverse` (`base/multinverses.jl:53-88`) terminates for every nonzero divisor,
and `div`, `rem`, `mod` through the inverse agree with the truncating intrinsics.

The proof works in the bit width `n = t.bits` with `H = 2^(n-1)`. The loop keeps
`q1 = 2^p / anc`, `r1 = 2^p % anc`, `q2 = (2^p / ad) mod 2^n`, `r2 = 2^p % ad`; it continues exactly
while `2^p ≤ anc * (ad - 2^p % ad)` and stops with `p ≤ 2n - 1`. The magic number
`M = 2^p / ad + 1` then satisfies `floor(b * M / 2^p) = floor(b / ad)` on the admissible dividends.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

namespace SmiProof

/-! ### Integer arithmetic -/

theorem dm_ex (x : Int) {b : Int} (hb : 0 < b) :
    ∃ q r, x / b = q ∧ x % b = r ∧ r + b * q = x ∧ 0 ≤ r ∧ r < b :=
  ⟨_, _, rfl, rfl, Int.emod_add_mul_ediv x b, Int.emod_nonneg x (by omega), Int.emod_lt_of_pos x hb⟩

theorem divmod_of {a b q : Int} (hb : 0 < b) (h1 : b * q ≤ a) (h2 : a < b * q + b) :
    a / b = q ∧ a % b = a - b * q := by
  obtain ⟨q', r', hq', hr', e, r0, r1⟩ := dm_ex a hb
  have hq : q' = q := by
    rcases Int.lt_trichotomy q' q with h | h | h
    · have m := Int.mul_le_mul_of_nonneg_left (show q' + 1 ≤ q by omega) (Int.le_of_lt hb)
      rw [Int.mul_add, Int.mul_one] at m
      omega
    · exact h
    · have m := Int.mul_le_mul_of_nonneg_left (show q + 1 ≤ q' by omega) (Int.le_of_lt hb)
      rw [Int.mul_add, Int.mul_one] at m
      omega
  subst hq
  exact ⟨hq', by omega⟩

theorem dbl_hi {X B : Int} (hB : 0 < B) (h : B ≤ X % B * 2) :
    X * 2 / B = X / B * 2 + 1 ∧ X * 2 % B = X % B * 2 - B := by
  obtain ⟨q, r, hq, hr, e, r0, r1⟩ := dm_ex X hB
  rw [hr] at h
  rw [hq, hr]
  have m : B * (q * 2 + 1) = B * q * 2 + B := by grind
  obtain ⟨h1, h2⟩ := divmod_of (a := X * 2) (q := q * 2 + 1) hB (by omega) (by omega)
  exact ⟨h1, by rw [h2]; omega⟩

theorem dbl_lo {X B : Int} (hB : 0 < B) (h : X % B * 2 < B) :
    X * 2 / B = X / B * 2 ∧ X * 2 % B = X % B * 2 := by
  obtain ⟨q, r, hq, hr, e, r0, r1⟩ := dm_ex X hB
  rw [hr] at h
  rw [hq, hr]
  have m : B * (q * 2) = B * q * 2 := by grind
  obtain ⟨h1, h2⟩ := divmod_of (a := X * 2) (q := q * 2) hB (by omega) (by omega)
  exact ⟨h1, by rw [h2]; omega⟩

theorem emod_mul2_add (y W c : Int) : (y % W * 2 + c) % W = (y * 2 + c) % W := by
  have e := Int.emod_add_mul_ediv y W
  have h : y % W * 2 + c = (y * 2 + c) + W * (-(y / W) * 2) := by grind
  rw [h, Int.add_mul_emod_self_left]

theorem emod_mul2 (y W : Int) : (y % W * 2) % W = (y * 2) % W := by
  have h := emod_mul2_add y W 0
  rw [Int.add_zero, Int.add_zero] at h
  exact h

theorem emod_add1 (y W : Int) : (y % W + 1) % W = (y + 1) % W := by
  have e := Int.emod_add_mul_ediv y W
  have h : y % W + 1 = (y + 1) + W * (-(y / W)) := by grind
  rw [h, Int.add_mul_emod_self_left]

theorem ediv_range {x W H : Int} (hW : 0 < W) (h1 : -(W * H) ≤ x) (h2 : x < W * H) :
    -H ≤ x / W ∧ x / W < H := by
  obtain ⟨q, r, hq, -, e, r0, r1⟩ := dm_ex x hW
  rw [hq]
  constructor
  · refine Classical.byContradiction fun hc => ?_
    have m := Int.mul_le_mul_of_nonneg_left (show q ≤ -H - 1 by omega) (Int.le_of_lt hW)
    have i : W * (-H - 1) = -(W * H) - W := by grind
    omega
  · refine Classical.byContradiction fun hc => ?_
    have m := Int.mul_le_mul_of_nonneg_left (show H ≤ q by omega) (Int.le_of_lt hW)
    omega

theorem ediv_neg_iff {x W : Int} (hW : 0 < W) : x / W < 0 ↔ x < 0 := by
  obtain ⟨q, r, hq, -, e, r0, r1⟩ := dm_ex x hW
  rw [hq]
  constructor
  · intro h
    have m := Int.mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (Int.le_of_lt hW)
    omega
  · intro h
    refine Classical.byContradiction fun hc => ?_
    have m := Int.mul_nonneg (Int.le_of_lt hW) (show 0 ≤ q by omega)
    omega

theorem ediv_ediv {x W K : Int} (hW : 0 < W) (hK : 0 < K) : x / W / K = x / (W * K) := by
  obtain ⟨q1, r1, hq1, -, e1, a0, a1⟩ := dm_ex x hW
  obtain ⟨q2, r2, hq2, -, e2, b0, b1⟩ := dm_ex q1 hK
  rw [hq1, hq2]
  have hWK : 0 < W * K := Int.mul_pos hW hK
  have m := Int.mul_le_mul_of_nonneg_left (show r2 ≤ K - 1 by omega) (Int.le_of_lt hW)
  have hWr2 : 0 ≤ W * r2 := Int.mul_nonneg (Int.le_of_lt hW) b0
  have i1 : x = W * K * q2 + (W * r2 + r1) := by grind
  have i2 : W * (K - 1) = W * K - W := by grind
  exact ((divmod_of (a := x) (q := q2) hWK (by omega) (by omega)).1).symm

theorem prod_range {H b M : Int} (hH : 0 < H) (hb0 : -H ≤ b) (hb1 : b ≤ H) (hM0 : 0 ≤ M)
    (hM1 : M < 2 * H) : -(2 * H * H) ≤ b * M ∧ b * M < 2 * H * H := by
  have m1 := Int.mul_lt_mul_of_pos_left hM1 hH
  have e1 : H * (2 * H) = 2 * H * H := by grind
  by_cases hb : 0 ≤ b
  · have m2 := Int.mul_le_mul_of_nonneg_right hb1 hM0
    have m3 := Int.mul_nonneg hb hM0
    omega
  · have m2 := Int.mul_le_mul_of_nonneg_right (show -b ≤ H by omega) hM0
    have m3 := Int.mul_nonneg (show 0 ≤ -b by omega) hM0
    have e2 : -b * M = -(b * M) := Int.neg_mul b M
    omega

theorem pow2_pos (k : Nat) : (0 : Int) < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

theorem pow2_succ (k : Nat) : (2 : Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k

theorem pow2_add (a b : Nat) : (2 : Int) ^ (a + b) = 2 ^ a * 2 ^ b := by
  induction b with
  | zero => rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | succ b ih => rw [← Nat.add_assoc, pow2_succ, pow2_succ, ih, Int.mul_assoc]

theorem pow2_mono {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow2_add]
  have h1 := pow2_pos a
  have h2 := pow2_pos c
  have m := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 2 ^ c by omega) (Int.le_of_lt h1)
  rw [Int.mul_one] at m
  exact m

theorem odd_of {H D Q : Int} (hH2 : H % 2 = 0) (h : H + 1 = D * Q) : D % 2 = 1 := by
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨k, hk⟩ : ∃ k, D = 2 * k := ⟨D / 2, by omega⟩
  subst hk
  rw [Int.mul_assoc] at h
  omega

theorem pow2_emod_ne {D : Int} (hD : 2 ≤ D) (hodd : D % 2 = 1) (k : Nat) : (2 : Int) ^ k % D ≠ 0 := by
  induction k with
  | zero => rw [Int.pow_zero, Int.emod_eq_of_lt (by omega) (by omega)]; omega
  | succ k ih =>
    rw [pow2_succ]
    have r0 := Int.emod_nonneg ((2 : Int) ^ k) (show D ≠ 0 by omega)
    have r1 := Int.emod_lt_of_pos ((2 : Int) ^ k) (show 0 < D by omega)
    by_cases h : D ≤ (2 : Int) ^ k % D * 2
    · rw [(dbl_hi (show 0 < D by omega) h).2]; omega
    · rw [(dbl_lo (show 0 < D by omega) (by omega)).2]; omega

/-- Remainder facts for truncated division by a divisor of absolute value `D`. -/
theorem tmod_facts (a d : Int) {D : Int} (hD : D = d ∨ D = -d) (hD0 : 0 < D) :
    -D < a.tmod d ∧ a.tmod d < D ∧ (0 ≤ a → 0 ≤ a.tmod d ∧ a.tmod d ≤ a) ∧
      (a < 0 → a ≤ a.tmod d ∧ a.tmod d ≤ 0) := by
  have e : a.tmod d = a.tmod D := by
    rcases hD with h | h
    · rw [h]
    · rw [h, Int.tmod_neg]
  rw [e]
  by_cases ha : 0 ≤ a
  · rw [Int.tmod_eq_emod_of_nonneg ha]
    obtain ⟨q, r, hq, hr, eq, r0, r1⟩ := dm_ex a hD0
    have q0 : 0 ≤ q := by rw [← hq]; exact Int.ediv_nonneg ha (by omega)
    have m := Int.mul_nonneg (Int.le_of_lt hD0) q0
    rw [hr]
    exact ⟨by omega, by omega, fun _ => ⟨by omega, by omega⟩, fun h => absurd h (by omega)⟩
  · have hna : 0 ≤ -a := by omega
    have e2 : a.tmod D = -((-a).tmod D) := by rw [Int.neg_tmod, Int.neg_neg]
    rw [e2, Int.tmod_eq_emod_of_nonneg hna]
    obtain ⟨q, r, hq, hr, eq, r0, r1⟩ := dm_ex (-a) hD0
    have q0 : 0 ≤ q := by rw [← hq]; exact Int.ediv_nonneg hna (by omega)
    have m := Int.mul_nonneg (Int.le_of_lt hD0) q0
    rw [hr]
    exact ⟨by omega, by omega, fun h => absurd h ha, fun _ => ⟨by omega, by omega⟩⟩

/-! ### Floor and ceiling of `b * M / 2^p` -/

theorem floor_lem {b D T e M : Int} (hD : 0 < D) (hT : 0 < T) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hMD : M * D = T + e) (h : b * e < (D - b % D) * T) : b * M / T = b / D := by
  obtain ⟨q, r, hq, hr, eb, r0, r1⟩ := dm_ex b hD
  rw [hq]
  rw [hr] at h
  have key : D * (b * M) = D * (T * q) + r * T + b * e := by grind
  have k2 : (D - r) * T = D * T - r * T := by grind
  have k3 : D * (T * q + T) = D * (T * q) + D * T := by grind
  have hrT : 0 ≤ r * T := Int.mul_nonneg r0 (Int.le_of_lt hT)
  have hbe : 0 ≤ b * e := Int.mul_nonneg hb he
  have lo : T * q ≤ b * M := Int.le_of_mul_le_mul_left (by omega) hD
  have hi : b * M < T * q + T := Int.lt_of_mul_lt_mul_left (by omega) (Int.le_of_lt hD)
  exact (divmod_of hT lo hi).1

theorem ceil_lem {c D T e M : Int} (hD : 0 < D) (hT : 0 < T) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hMD : M * D = T + e) (h : c * e ≤ (D - c % D) * T) : -(c * M) / T = -(c / D) - 1 := by
  obtain ⟨q, r, hq, hr, eb, r0, r1⟩ := dm_ex c hD
  rw [hq]
  rw [hr] at h
  have key : D * (c * M) = D * (T * q) + r * T + c * e := by grind
  have k2 : (D - r) * T = D * T - r * T := by grind
  have k3 : D * (T * q + T) = D * (T * q) + D * T := by grind
  have hrT : 0 ≤ r * T := Int.mul_nonneg r0 (Int.le_of_lt hT)
  have hce : c ≤ c * e := by
    have m := Int.mul_le_mul_of_nonneg_left he (show (0 : Int) ≤ c by omega)
    rw [Int.mul_one] at m
    exact m
  have lo : T * q < c * M := Int.lt_of_mul_lt_mul_left (by omega) (Int.le_of_lt hD)
  have hi : c * M ≤ T * q + T := Int.le_of_mul_le_mul_left (by omega) hD
  have k4 : T * (-q - 1) = -(T * q) - T := by grind
  exact (divmod_of (a := -(c * M)) (q := -q - 1) hT (by omega) (by omega)).1

/-! ### Constructor parameters -/

/-- Facts about `anc` and `ad` computed before the loop (`base/multinverses.jl:58-61`), in terms of
`H = 2^(n-1)`, `c = signbit(d)`, `A = anc`, `D = ad`. -/
structure Params (H A D c : Int) (n : Nat) : Prop where
  hH : H = (2 : Int) ^ (n - 1)
  hn : 8 ≤ n
  hn' : n ≤ 128
  hc : c = 0 ∨ c = 1
  hD1 : 1 ≤ D
  hDH : D ≤ H
  hDc : D = H → c = 1
  hA : A = H + c - 1 - (H + c) % D

theorem Params.facts {H A D c : Int} {n : Nat} (P : Params H A D c n) :
    128 ≤ H ∧ H % 2 = 0 ∧ A ≤ H ∧ D - 1 ≤ A ∧ 2 ≤ A ∧ (D = H → A = H - 1) ∧
      ∃ Q ρ, H + c = D * Q + ρ ∧ 0 ≤ ρ ∧ ρ < D ∧ 1 ≤ Q ∧ A = H + c - 1 - ρ ∧ D ≤ D * Q := by
  have hn := P.hn
  have hH : 128 ≤ H := by
    rw [P.hH]
    have m := pow2_mono (show 7 ≤ n - 1 by omega)
    have h7 : (2 : Int) ^ 7 = 128 := by decide
    omega
  have hH2 : H % 2 = 0 := by
    rw [P.hH, show n - 1 = (n - 2) + 1 by omega, pow2_succ]
    omega
  have hD1 := P.hD1
  have hDH := P.hDH
  have hc := P.hc
  obtain ⟨Q, ρ, -, hρ, e, r0, r1⟩ := dm_ex (H + c) (show 0 < D by omega)
  have hA : A = H + c - 1 - ρ := by rw [P.hA, hρ]
  have hQ : 1 ≤ Q := by
    refine Classical.byContradiction fun hq => ?_
    have m := Int.mul_le_mul_of_nonneg_left (show Q ≤ 0 by omega) (show 0 ≤ D by omega)
    rw [Int.mul_zero] at m
    omega
  have hDQ : D ≤ D * Q := by
    have m := Int.mul_le_mul_of_nonneg_left hQ (show 0 ≤ D by omega)
    rw [Int.mul_one] at m
    exact m
  refine ⟨hH, hH2, by omega, by omega, by omega, ?_, Q, ρ, by omega, r0, r1, hQ, hA, hDQ⟩
  intro hDHe
  have hc1 := P.hDc hDHe
  have h1 := (divmod_of (a := H + c) (b := D) (q := 1) (by omega) (by omega) (by omega)).2
  rw [hρ] at h1
  omega

/-! ### Magic number bound -/

theorem magic_lt {H A D c : Int} {n : Nat} (P : Params H A D c n) (hD2 : 2 ≤ D) {p : Nat}
    (hp : n ≤ p) (hprev : p = n ∨ (2 : Int) ^ (p - 1) ≤ A * (D - (2 : Int) ^ (p - 1) % D)) :
    (2 : Int) ^ p / D + 1 < 2 * H := by
  obtain ⟨hH, hH2, hAH, hDA, hA2, -, Q, ρ, e1, r0, r1, hQ, hA, hDQ⟩ := P.facts
  have hn := P.hn
  have hDH := P.hDH
  have hD0 : 0 < D := by omega
  suffices hlt : (2 : Int) ^ p < (2 * H - 1) * D by
    obtain ⟨q, r, hq, -, e, r0', r1'⟩ := dm_ex ((2 : Int) ^ p) hD0
    rw [hq]
    refine Classical.byContradiction fun hc => ?_
    have m := Int.mul_le_mul_of_nonneg_left (show 2 * H - 1 ≤ q by omega) (show 0 ≤ D by omega)
    have i : D * (2 * H - 1) = (2 * H - 1) * D := Int.mul_comm _ _
    omega
  have hpp : (2 : Int) ^ p = (2 : Int) ^ (p - 1) * 2 := by
    rw [← pow2_succ]; congr 1; omega
  rcases hprev with h | h
  · have hn2 : (2 : Int) ^ n = (2 : Int) ^ (n - 1) * 2 := by
      rw [← pow2_succ]; congr 1; omega
    rw [h, hn2, ← P.hH]
    have m := Int.mul_le_mul_of_nonneg_left hD2 (show 0 ≤ 2 * H - 1 by omega)
    omega
  · obtain ⟨q', r', -, hr', e', r0', r1'⟩ := dm_ex ((2 : Int) ^ (p - 1)) hD0
    rw [hr'] at h
    rw [hpp]
    by_cases hA' : A ≤ H - 1
    · have m1 := Int.mul_le_mul_of_nonneg_right hA' (show 0 ≤ D - r' by omega)
      have m2 := Int.mul_le_mul_of_nonneg_left (show D - r' ≤ D by omega) (show 0 ≤ H - 1 by omega)
      have i : (2 * H - 1) * D = 2 * ((H - 1) * D) + D := by grind
      omega
    · have hAeq : A = H := by omega
      have hodd : D % 2 = 1 := odd_of hH2 (show H + 1 = D * Q by omega)
      have hr'0 : r' ≠ 0 := by rw [← hr']; exact pow2_emod_ne hD2 hodd _
      have m1 := Int.mul_le_mul_of_nonneg_left (show D - r' ≤ D - 1 by omega) (show 0 ≤ H by omega)
      rw [hAeq] at h
      have i : (2 * H - 1) * D = 2 * (H * (D - 1)) + 2 * H - D := by grind
      omega

/-! ### Admissible dividends -/

theorem adm_nonneg {H A D c : Int} {n : Nat} (P : Params H A D c n) (hD2 : 2 ≤ D) {T e b : Int}
    (hT : 0 < T) (he : 0 ≤ e) (hAe : A * e < T) (hb1 : b ≤ H + c - 1) :
    b * e < (D - b % D) * T := by
  obtain ⟨hH, -, hAH, hDA, hA2, -, Q, ρ, e1, r0, r1, hQ, hA, hDQ⟩ := P.facts
  obtain ⟨qb, rb, -, hrb, eb, rb0, rb1⟩ := dm_ex b (show 0 < D by omega)
  rw [hrb]
  by_cases hbA : b ≤ A
  · have m1 := Int.mul_le_mul_of_nonneg_right hbA he
    have m2 := Int.mul_le_mul_of_nonneg_right (show 1 ≤ D - rb by omega) (Int.le_of_lt hT)
    rw [Int.one_mul] at m2
    omega
  · have hrb' := (divmod_of (a := b) (b := D) (q := Q) (by omega) (by omega) (by omega)).2
    rw [hrb] at hrb'
    have m1 := Int.mul_le_mul_of_nonneg_right (show b ≤ 2 * A by omega) he
    have m2 := Int.mul_le_mul_of_nonneg_right (show 2 ≤ D - rb by omega) (Int.le_of_lt hT)
    have e2 : 2 * A * e = 2 * (A * e) := Int.mul_assoc 2 A e
    omega

theorem adm_neg {H A D c : Int} {n : Nat} (P : Params H A D c n) (hD2 : 2 ≤ D) {T rT b K : Int}
    (hT : 0 < T) (hrT : T % D = rT) (hAe : A * (D - rT) < T) (hTK : T = H * K) (hK : 2 ≤ K)
    (hb1 : b ≤ H - c) :
    b * (D - rT) ≤ (D - b % D) * T := by
  obtain ⟨hH, -, hAH, hDA, hA2, -, Q, ρ, e1, r0, r1, hQ, hA, hDQ⟩ := P.facts
  have hc := P.hc
  have rT0 := Int.emod_nonneg T (show D ≠ 0 by omega)
  have rT1 := Int.emod_lt_of_pos T (show 0 < D by omega)
  rw [hrT] at rT0 rT1
  obtain ⟨qb, rb, -, hrb, eb, rb0, rb1⟩ := dm_ex b (show 0 < D by omega)
  rw [hrb]
  have he0 : 0 ≤ D - rT := by omega
  by_cases hbA : b ≤ A
  · have m1 := Int.mul_le_mul_of_nonneg_right hbA he0
    have m2 := Int.mul_le_mul_of_nonneg_right (show 1 ≤ D - rb by omega) (Int.le_of_lt hT)
    rw [Int.one_mul] at m2
    omega
  · by_cases hbA1 : b = A + 1
    · have h0 := (divmod_of (a := b) (b := D) (q := Q) (by omega) (by omega) (by omega)).2
      rw [hrb] at h0
      have hrb0 : rb = 0 := by omega
      rw [hrb0, Int.sub_zero]
      have m0 := Int.mul_le_mul_of_nonneg_right hD2 (show 0 ≤ Q by omega)
      have hQA : Q ≤ A := by omega
      have m1 := Int.mul_le_mul_of_nonneg_right hQA he0
      have m2 := Int.mul_le_mul_of_nonneg_left (show Q * (D - rT) ≤ T by omega)
        (show 0 ≤ D by omega)
      have e3 : b * (D - rT) = D * (Q * (D - rT)) := by
        rw [show b = D * Q by omega, Int.mul_assoc]
      omega
    · have h0 := (divmod_of (a := b) (b := D) (q := Q) (by omega) (by omega) (by omega)).2
      rw [hrb] at h0
      by_cases hr2 : rb ≤ D - 2
      · have m1 := Int.mul_le_mul_of_nonneg_right (show b ≤ 2 * A by omega) he0
        have m2 := Int.mul_le_mul_of_nonneg_right (show 2 ≤ D - rb by omega) (Int.le_of_lt hT)
        have e2 : 2 * A * (D - rT) = 2 * (A * (D - rT)) := Int.mul_assoc 2 A (D - rT)
        omega
      · have hbH : b = H := by omega
        have hD1 : D - rb = 1 := by omega
        rw [hD1, Int.one_mul, hbH]
        by_cases hKD : D ≤ K
        · have m := Int.mul_le_mul_of_nonneg_left (show D - rT ≤ K by omega) (show 0 ≤ H by omega)
          omega
        · have hHQ : H = D * Q + (D - 1) := by omega
          have hid : T = D * (Q * K + K - 1) + (D - K) := by rw [hTK, hHQ]; grind
          have h2 := (divmod_of (a := T) (b := D) (q := Q * K + K - 1) (by omega) (by omega)
            (by omega)).2
          rw [hrT] at h2
          have heK : D - rT = K := by omega
          rw [heK]
          omega

theorem core_tdiv {H A D c : Int} {n : Nat} (P : Params H A D c n) (hD2 : 2 ≤ D) {p : Nat}
    (hp : n ≤ p) {T M : Int} (hTp : (2 : Int) ^ p = T) (hM : M = T / D + 1)
    (hexit : A * (D - T % D) < T) {b : Int} (hb0 : -(H - c) ≤ b) (hb1 : b ≤ H + c - 1) :
    b * M / T + (if b * M < 0 then 1 else 0) = b.tdiv D := by
  have hn := P.hn
  have hc := P.hc
  have hT : 0 < T := by rw [← hTp]; exact pow2_pos p
  have hD0 : 0 < D := by omega
  obtain ⟨qT, rT, hqT, hrT, eT, rT0, rT1⟩ := dm_ex T hD0
  rw [hqT] at hM
  rw [hrT] at hexit
  have hMD : M * D = T + (D - rT) := by rw [hM]; grind
  have hq0 : 0 ≤ qT := by rw [← hqT]; exact Int.ediv_nonneg (by omega) (by omega)
  obtain ⟨K, hTK, hK⟩ : ∃ K, T = H * K ∧ 2 ≤ K := by
    refine ⟨(2 : Int) ^ (p - (n - 1)), ?_, ?_⟩
    · rw [← hTp, P.hH, ← pow2_add]; congr 1; omega
    · have m := pow2_mono (show 1 ≤ p - (n - 1) by omega)
      have h1 : (2 : Int) ^ 1 = 2 := by decide
      omega
  by_cases hb : 0 ≤ b
  · have hbM : 0 ≤ b * M := Int.mul_nonneg hb (by omega)
    rw [ite_eq_right (by omega), Int.add_zero, Int.tdiv_eq_ediv_of_nonneg hb]
    exact floor_lem hD0 hT hb (by omega) hMD (adm_nonneg P hD2 hT (by omega) hexit hb1)
  · have hc1 : 1 ≤ -b := by omega
    have hneg : b * M < 0 := by
      have m := Int.mul_le_mul_of_nonneg_right hc1 (show 0 ≤ M by omega)
      rw [Int.one_mul, Int.neg_mul] at m
      omega
    have hbM : b * M = -((-b) * M) := by rw [Int.neg_mul, Int.neg_neg]
    rw [ite_eq_left hneg, hbM,
      ceil_lem hD0 hT hc1 (by omega) hMD (adm_neg P hD2 hT hrT hexit hTK hK (by omega))]
    have e : b.tdiv D = -((-b).tdiv D) := by rw [Int.neg_tdiv, Int.neg_neg]
    rw [e, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega

/-! ### Machine integers -/

theorem tfacts {t : IntTy} (ht : t.signed = true) :
    t.toUnsigned.signed = false ∧ t.toUnsigned.bits = t.bits ∧
      t.min = -((2 : Int) ^ (t.bits - 1)) ∧ t.max = (2 : Int) ^ (t.bits - 1) - 1 ∧
      (2 : Int) ^ t.bits = 2 * (2 : Int) ^ (t.bits - 1) ∧ 8 ≤ t.bits ∧ t.bits ≤ 128 := by
  cases t <;> simp [IntTy.signed] at ht <;> decide

theorem H_ge {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H) :
    128 ≤ H := by
  obtain ⟨-, -, -, -, -, h8, -⟩ := tfacts ht
  rw [← hH]
  have m := pow2_mono (show 7 ≤ t.bits - 1 by omega)
  have h7 : (2 : Int) ^ 7 = 128 := by decide
  omega

theorem wrapS_eq {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    (x : Int) : wrapInt t x = (x + H) % (2 * H) - H := by
  obtain ⟨-, -, -, -, hW, -⟩ := tfacts ht
  rw [wrapInt, ite_eq_left ht, hW, hH]

theorem wrapU_eq {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    (x : Int) : wrapInt t.toUnsigned x = x % (2 * H) := by
  obtain ⟨hu, hb, -, -, hW, -⟩ := tfacts ht
  rw [wrapInt, ite_eq_right (by rw [hu]; decide), hb, hW, hH]

theorem wrapS_id {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {x : Int} (h1 : -H ≤ x) (h2 : x < H) : wrapInt t x = x := by
  have hb := H_ge ht hH
  rw [wrapS_eq ht hH,
    (divmod_of (a := x + H) (b := 2 * H) (q := 0) (by omega) (by omega) (by omega)).2]
  omega

theorem wrapS_hi {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {x : Int} (h1 : H ≤ x) (h2 : x < 3 * H) : wrapInt t x = x - 2 * H := by
  have hb := H_ge ht hH
  rw [wrapS_eq ht hH,
    (divmod_of (a := x + H) (b := 2 * H) (q := 1) (by omega) (by omega) (by omega)).2]
  omega

theorem wrapU_id {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {x : Int} (h1 : 0 ≤ x) (h2 : x < 2 * H) : wrapInt t.toUnsigned x = x := by
  have hb := H_ge ht hH
  rw [wrapU_eq ht hH,
    (divmod_of (a := x) (b := 2 * H) (q := 0) (by omega) (by omega) (by omega)).2]
  omega

theorem wrapU_neg {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {x : Int} (h1 : -(2 * H) ≤ x) (h2 : x < 0) : wrapInt t.toUnsigned x = x + 2 * H := by
  have hb := H_ge ht hH
  rw [wrapU_eq ht hH,
    (divmod_of (a := x) (b := 2 * H) (q := -1) (by omega) (by omega) (by omega)).2]
  omega

theorem val_bounds {t : IntTy} (ht : t.signed = true) {H : Int}
    (hH : (2 : Int) ^ (t.bits - 1) = H) (x : JInt t) : -H ≤ x.val ∧ x.val ≤ H - 1 := by
  obtain ⟨-, -, hmin, hmax, -⟩ := tfacts ht
  obtain ⟨h1, h2⟩ := x.property
  exact ⟨by omega, by omega⟩

theorem wrap64 (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ 100000) : wrapInt .i64 x = x := by
  have hmin : IntTy.i64.min = -9223372036854775808 := by decide
  have hmax : IntTy.i64.max = 9223372036854775807 := by decide
  exact wrapInt_of_inRange _ _ ⟨by rw [hmin]; omega, by rw [hmax]; omega⟩

theorem wrap_mul_l (t : IntTy) (x : Int) (y : JInt t) :
    wrapInt t (wrapInt t x * y.val) = wrapInt t (x * y.val) := by
  have h := wrapInt_mul t x y.val
  rw [← val_eq_wrap y] at h
  exact h

theorem wrap_sub_r (t : IntTy) (x : JInt t) (y : Int) :
    wrapInt t (x.val - wrapInt t y) = wrapInt t (x.val - y) := by
  have h := wrapInt_sub t x.val y
  rw [← val_eq_wrap x] at h
  exact h

theorem shl1_val {t : IntTy} (x : JInt t) : (shl1 x).val = wrapInt t (x.val * 2) := rfl
theorem shr_val {t : IntTy} (x : JInt t) (k : Nat) : (shr x k).val = wrapInt t (x.val / 2 ^ k) := rfl
theorem mulHi_val {t : IntTy} (a b : JInt t) :
    (mulHi a b).val = wrapInt t (a.val * b.val / 2 ^ t.bits) := rfl
theorem rem_val {t t' : IntTy} (a : JInt t) : (JInt.rem t' a).val = wrapInt t' a.val := rfl
theorem wrap_val (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl

theorem bind_ok {α β : Type} (x : α) (f : α → Jl β) : ((Except.ok x : Jl α) >>= f) = f x := rfl
theorem bind_err {α β : Type} (e : JlError) (f : α → Jl β) :
    ((Except.error e : Jl α) >>= f) = .error e := rfl
theorem pure_ok {α : Type} (x : α) : (pure x : Jl α) = .ok x := rfl

theorem remInt_ok {u : IntTy} {a b : JInt u} (hb : b.val ≠ 0) :
    JInt.remInt a b = .ok (JInt.wrap u (a.val.tmod b.val)) := by
  rw [JInt.remInt, ite_eq_right hb]

theorem divU_ok {u : IntTy} (hu : u.signed = false) {a b : JInt u} (hb : b.val ≠ 0) :
    JInt.div a b = .ok (JInt.wrap u (a.val.tdiv b.val)) := by
  rw [JInt.div, ite_eq_right hb, ite_eq_right (by rw [hu]; simp)]

theorem jabs_val {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    (d : JInt t) :
    (jabs d).val = if d.val < 0 then (if d.val = -H then -H else -d.val) else d.val := by
  have hb := H_ge ht hH
  have hdb := val_bounds ht hH d
  unfold jabs
  by_cases hneg : d.val < 0
  · rw [ite_eq_left hneg, ite_eq_left hneg, val_neg]
    by_cases hm : d.val = -H
    · rw [ite_eq_left hm, hm, wrapS_hi ht hH (by omega) (by omega)]
      omega
    · rw [ite_eq_right hm, wrapS_id ht hH (by omega) (by omega)]
  · rw [ite_eq_right hneg, ite_eq_right hneg]

/-! ### The loop -/

/-- Loop invariant at exponent `k`: `q1, r1 = divrem(2^k, A)`, `q2 = div(2^k, D) mod 2^n`,
`r2 = rem(2^k, D)`. -/
def Inv {t : IntTy} (H A D : Int) (k : Nat) (s : SmiState t) : Prop :=
  s.p.val = (k : Int) ∧ s.q1.val = (2 : Int) ^ k / A ∧ s.r1.val = (2 : Int) ^ k % A ∧
    s.q2.val = (2 : Int) ^ k / D % (2 * H) ∧ s.r2.val = (2 : Int) ^ k % D

/-- A state from which one more loop pass computes the next quotients without overflow. -/
def Good {t : IntTy} (H A D : Int) (n k : Nat) (s : SmiState t) : Prop :=
  Inv H A D k s ∧ (2 : Int) ^ k < A * H ∧ n - 1 ≤ k ∧ k + 2 ≤ 2 * n ∧
    (k = n - 1 ∨ (2 : Int) ^ k ≤ A * (D - (2 : Int) ^ k % D))

/-- The state in which the loop stops, at exponent `P`. -/
def Final {t : IntTy} (H A D : Int) (n : Nat) (s : SmiState t) : Prop :=
  ∃ P : Nat, Inv H A D P s ∧ n ≤ P ∧ P + 1 ≤ 2 * n ∧ A * (D - (2 : Int) ^ P % D) < (2 : Int) ^ P ∧
    (P = n ∨ (2 : Int) ^ (P - 1) ≤ A * (D - (2 : Int) ^ (P - 1) % D))

theorem step_fields {t : IntTy} (anc ad : JInt t.toUnsigned) (s : SmiState t) :
    (smiStep anc ad s).p = s.p + JInt.lit .i64 1 ∧
    (smiStep anc ad s).q1 =
      (if anc ≤ shl1 s.r1 then shl1 s.q1 + JInt.lit t.toUnsigned 1 else shl1 s.q1) ∧
    (smiStep anc ad s).r1 = (if anc ≤ shl1 s.r1 then shl1 s.r1 - anc else shl1 s.r1) ∧
    (smiStep anc ad s).q2 =
      (if ad ≤ shl1 s.r2 then shl1 s.q2 + JInt.lit t.toUnsigned 1 else shl1 s.q2) ∧
    (smiStep anc ad s).r2 = (if ad ≤ shl1 s.r2 then shl1 s.r2 - ad else shl1 s.r2) := by
  by_cases h1 : anc ≤ shl1 s.r1 <;> by_cases h2 : ad ≤ shl1 s.r2 <;> simp [smiStep, h1, h2]

theorem step_inv {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {anc ad : JInt t.toUnsigned} {A D : Int} (hA : anc.val = A) (hD : ad.val = D)
    (hA0 : 0 < A) (hAH : A ≤ H) (hD0 : 0 < D) (hDH : D ≤ H) {s : SmiState t} {k : Nat}
    (hinv : Inv H A D k s) (hsmall : (2 : Int) ^ k < A * H) (hk : k ≤ 1000) :
    Inv H A D (k + 1) (smiStep anc ad s) := by
  obtain ⟨hp, hq1, hr1, hq2, hr2⟩ := hinv
  obtain ⟨ep, eq1, er1, eq2, er2⟩ := step_fields anc ad s
  have hb := H_ge ht hH
  obtain ⟨X, hX⟩ : ∃ X, (2 : Int) ^ k = X := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [← hX]; exact pow2_pos k
  rw [hX] at hq1 hr1 hq2 hr2 hsmall
  unfold Inv
  rw [pow2_succ, hX]
  obtain ⟨qa, ra, hqa, hra, ea, ra0, ra1⟩ := dm_ex X hA0
  obtain ⟨qd, rd, hqd, hrd, ed, rd0, rd1⟩ := dm_ex X hD0
  rw [hqa] at hq1
  rw [hra] at hr1
  rw [hqd] at hq2
  rw [hrd] at hr2
  have hqa0 : 0 ≤ qa := by rw [← hqa]; exact Int.ediv_nonneg (by omega) (by omega)
  have hqaH : qa < H := by
    refine Classical.byContradiction fun hc => ?_
    have m := Int.mul_le_mul_of_nonneg_left (show H ≤ qa by omega) (Int.le_of_lt hA0)
    omega
  have one : (JInt.lit t.toUnsigned 1).val = 1 := by
    rw [val_lit, wrapU_id ht hH (by omega) (by omega)]
  have sq1 : (shl1 s.q1).val = qa * 2 := by
    rw [shl1_val, hq1, wrapU_id ht hH (by omega) (by omega)]
  have sr1 : (shl1 s.r1).val = ra * 2 := by
    rw [shl1_val, hr1, wrapU_id ht hH (by omega) (by omega)]
  have sr2 : (shl1 s.r2).val = rd * 2 := by
    rw [shl1_val, hr2, wrapU_id ht hH (by omega) (by omega)]
  have sq2 : (shl1 s.q2).val = qd % (2 * H) * 2 % (2 * H) := by
    rw [shl1_val, hq2, wrapU_eq ht hH]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ep, val_add, hp, val_lit, wrap64 1 (by omega) (by omega), wrap64 _ (by omega) (by omega)]
    omega
  · rw [eq1]
    by_cases hc : anc ≤ shl1 s.r1
    · have hc' : A ≤ X % A * 2 := by
        have h' : anc.val ≤ (shl1 s.r1).val := hc
        rw [hA, sr1] at h'
        rw [hra]
        exact h'
      rw [ite_eq_left hc, val_add, sq1, one, wrapU_id ht hH (by omega) (by omega),
        (dbl_hi hA0 hc').1, hqa]
    · have hc' : X % A * 2 < A := by
        have h' : ¬ anc.val ≤ (shl1 s.r1).val := hc
        rw [hA, sr1] at h'
        rw [hra]
        omega
      rw [ite_eq_right hc, sq1, (dbl_lo hA0 hc').1, hqa]
  · rw [er1]
    by_cases hc : anc ≤ shl1 s.r1
    · have hc' : A ≤ X % A * 2 := by
        have h' : anc.val ≤ (shl1 s.r1).val := hc
        rw [hA, sr1] at h'
        rw [hra]
        exact h'
      rw [ite_eq_left hc, val_sub, sr1, hA, wrapU_id ht hH (by omega) (by omega),
        (dbl_hi hA0 hc').2, hra]
    · have hc' : X % A * 2 < A := by
        have h' : ¬ anc.val ≤ (shl1 s.r1).val := hc
        rw [hA, sr1] at h'
        rw [hra]
        omega
      rw [ite_eq_right hc, sr1, (dbl_lo hA0 hc').2, hra]
  · rw [eq2]
    by_cases hc : ad ≤ shl1 s.r2
    · have hc' : D ≤ X % D * 2 := by
        have h' : ad.val ≤ (shl1 s.r2).val := hc
        rw [hD, sr2] at h'
        rw [hrd]
        exact h'
      rw [ite_eq_left hc, val_add, sq2, one, wrapU_eq ht hH, (dbl_hi hD0 hc').1, hqd, emod_add1,
        emod_mul2_add]
    · have hc' : X % D * 2 < D := by
        have h' : ¬ ad.val ≤ (shl1 s.r2).val := hc
        rw [hD, sr2] at h'
        rw [hrd]
        omega
      rw [ite_eq_right hc, sq2, (dbl_lo hD0 hc').1, hqd, emod_mul2]
  · rw [er2]
    by_cases hc : ad ≤ shl1 s.r2
    · have hc' : D ≤ X % D * 2 := by
        have h' : ad.val ≤ (shl1 s.r2).val := hc
        rw [hD, sr2] at h'
        rw [hrd]
        exact h'
      rw [ite_eq_left hc, val_sub, sr2, hD, wrapU_id ht hH (by omega) (by omega),
        (dbl_hi hD0 hc').2, hrd]
    · have hc' : X % D * 2 < D := by
        have h' : ¬ ad.val ≤ (shl1 s.r2).val := hc
        rw [hD, sr2] at h'
        rw [hrd]
        omega
      rw [ite_eq_right hc, sr2, (dbl_lo hD0 hc').2, hrd]

theorem cont_iff {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {ad : JInt t.toUnsigned} {A D : Int} (hD : ad.val = D) (hA0 : 0 < A) (hD0 : 0 < D)
    (hDH : D ≤ H) {s : SmiState t} {k : Nat} (hinv : Inv H A D k s) :
    smiContinue ad s ↔ (2 : Int) ^ k ≤ A * (D - (2 : Int) ^ k % D) := by
  obtain ⟨-, hq1, hr1, -, hr2⟩ := hinv
  have hb := H_ge ht hH
  obtain ⟨qa, ra, hqa, hra, ea, ra0, ra1⟩ := dm_ex ((2 : Int) ^ k) hA0
  obtain ⟨qd, rd, -, hrd, ed, rd0, rd1⟩ := dm_ex ((2 : Int) ^ k) hD0
  rw [hqa] at hq1
  rw [hra] at hr1
  rw [hrd] at hr2 ⊢
  have hdelta : (ad - s.r2).val = D - rd := by
    rw [val_sub, hD, hr2, wrapU_id ht hH (by omega) (by omega)]
  have hq : s.q1 = ad - s.r2 ↔ s.q1.val = (ad - s.r2).val :=
    ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
  unfold smiContinue
  show (s.q1.val < (ad - s.r2).val ∨ (s.q1 = ad - s.r2 ∧ s.r1.val = 0)) ↔ _
  rw [hq, hdelta, hq1, hr1]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · have m := Int.mul_le_mul_of_nonneg_left (show qa + 1 ≤ D - rd by omega) (Int.le_of_lt hA0)
      rw [Int.mul_add, Int.mul_one] at m
      omega
    · rw [h1] at ea
      omega
  · intro h
    by_cases h1 : qa < D - rd
    · exact Or.inl h1
    · right
      by_cases h2 : qa = D - rd
      · rw [h2] at ea
        exact ⟨h2, by omega⟩
      · have m := Int.mul_le_mul_of_nonneg_left (show D - rd + 1 ≤ qa by omega) (Int.le_of_lt hA0)
        rw [Int.mul_add, Int.mul_one] at m
        omega

theorem init_good {t : IntTy} {H A D c : Int} {n : Nat} (P : Params H A D c n) {s : SmiState t}
    (h : Inv H A D (n - 1) s) : Good H A D n (n - 1) s := by
  obtain ⟨hH, -, -, -, hA2, -⟩ := P.facts
  have hn := P.hn
  refine ⟨h, ?_, Nat.le_refl _, by omega, Or.inl rfl⟩
  rw [← P.hH]
  have m := Int.mul_le_mul_of_nonneg_right (show 2 ≤ A by omega) (show 0 ≤ H by omega)
  omega

theorem good_next {t : IntTy} {H A D c : Int} {n : Nat} (P : Params H A D c n) {s : SmiState t}
    {k : Nat} (hinv : Inv H A D (k + 1) s) (hk : n - 1 ≤ k)
    (hcont : (2 : Int) ^ (k + 1) ≤ A * (D - (2 : Int) ^ (k + 1) % D)) :
    Good H A D n (k + 1) s := by
  obtain ⟨hH, -, hAH, hDA, hA2, hDHA, -⟩ := P.facts
  have hn := P.hn
  have hDH := P.hDH
  have hD0 : 0 < D := by have := P.hD1; omega
  obtain ⟨X, hX⟩ : ∃ X, (2 : Int) ^ (k + 1) = X := ⟨_, rfl⟩
  rw [hX] at hcont
  obtain ⟨-, r, -, hr, -, r0, r1⟩ := dm_ex X hD0
  rw [hr] at hcont
  have m1 := Int.mul_le_mul_of_nonneg_left (show D - r ≤ D by omega) (show 0 ≤ A by omega)
  have m2 := Int.mul_le_mul_of_nonneg_right hAH (show 0 ≤ D by omega)
  have m3 := Int.mul_le_mul_of_nonneg_left hDH (show 0 ≤ H by omega)
  have hHH : H * H = (2 : Int) ^ (2 * n - 2) := by
    rw [P.hH, ← pow2_add]; congr 1; omega
  have hHH0 : 0 < H * H := Int.mul_pos (by omega) (by omega)
  have hlt : k + 1 + 2 ≤ 2 * n := by
    refine Classical.byContradiction fun hc => ?_
    have m := pow2_mono (show (2 * n - 2) + 1 ≤ k + 1 by omega)
    rw [pow2_succ, ← hHH, hX] at m
    omega
  refine ⟨hinv, ?_, by omega, hlt, Or.inr (by rw [hX, hr]; exact hcont)⟩
  rw [hX]
  by_cases he : D - r ≤ H - 1
  · have m4 := Int.mul_le_mul_of_nonneg_left he (show 0 ≤ A by omega)
    have i : A * (H - 1) = A * H - A := by grind
    omega
  · have hDH' : D = H := by omega
    have hA' := hDHA hDH'
    rw [hA'] at hcont ⊢
    have m5 := Int.mul_le_mul_of_nonneg_left (show D - r ≤ H by omega) (show 0 ≤ H - 1 by omega)
    have i : (H - 1) * H = H * H - H := by grind
    have hk3 : k + 1 + 3 ≤ 2 * n := by
      refine Classical.byContradiction fun hc => ?_
      have hx : X = H * H := by rw [← hX, hHH]; congr 1; omega
      omega
    have m6 := pow2_mono (show k + 1 + 1 ≤ 2 * n - 2 by omega)
    rw [pow2_succ, ← hHH, hX] at m6
    have m7 := Int.mul_le_mul_of_nonneg_right hH (show 0 ≤ H by omega)
    omega

theorem loop_final {t : IntTy} (ht : t.signed = true) {H A D c : Int} (P : Params H A D c t.bits)
    {anc ad : JInt t.toUnsigned} (hA : anc.val = A) (hD : ad.val = D) {s r : SmiState t}
    (hl : SmiLoop anc ad s r) : ∀ k, Good H A D t.bits k s → Final H A D t.bits r := by
  obtain ⟨hH, -, hAH, hDA, hA2, -⟩ := P.facts
  have hD0 : 0 < D := by have := P.hD1; omega
  have hHp := P.hH.symm
  induction hl with
  | stop s hnc =>
    intro k hg
    obtain ⟨hinv, hsm, hk1, hk2, hprev⟩ := hg
    have hi := step_inv ht hHp hA hD (by omega) hAH hD0 P.hDH hinv hsm (by have := P.hn'; omega)
    have hnc' : ¬ ((2 : Int) ^ (k + 1) ≤ A * (D - (2 : Int) ^ (k + 1) % D)) :=
      fun h => hnc ((cont_iff ht hHp hD (by omega) hD0 P.hDH hi).2 h)
    refine ⟨k + 1, hi, by omega, by omega, by omega, ?_⟩
    rcases hprev with h | h
    · left; omega
    · right; rw [Nat.add_sub_cancel]; exact h
  | next s r hc hl ih =>
    intro k hg
    obtain ⟨hinv, hsm, hk1, hk2, hprev⟩ := hg
    have hi := step_inv ht hHp hA hD (by omega) hAH hD0 P.hDH hinv hsm (by have := P.hn'; omega)
    exact ih (k + 1) (good_next P hi hk1 ((cont_iff ht hHp hD (by omega) hD0 P.hDH hi).1 hc))

theorem loop_exists {t : IntTy} (ht : t.signed = true) {H A D c : Int} (P : Params H A D c t.bits)
    {anc ad : JInt t.toUnsigned} (hA : anc.val = A) (hD : ad.val = D) :
    ∀ (f : Nat) (s : SmiState t) (k : Nat), k + f = 2 * t.bits → Good H A D t.bits k s →
      ∃ r, SmiLoop anc ad s r := by
  obtain ⟨hH, -, hAH, hDA, hA2, -⟩ := P.facts
  have hD0 : 0 < D := by have := P.hD1; omega
  have hHp := P.hH.symm
  intro f
  induction f with
  | zero =>
    intro s k hf hg
    obtain ⟨-, -, -, hk2, -⟩ := hg
    omega
  | succ f ih =>
    intro s k hf hg
    obtain ⟨hinv, hsm, hk1, hk2, hprev⟩ := hg
    have hi := step_inv ht hHp hA hD (by omega) hAH hD0 P.hDH hinv hsm (by have := P.hn'; omega)
    by_cases hc : smiContinue ad (smiStep anc ad s)
    · obtain ⟨r, hr⟩ := ih (smiStep anc ad s) (k + 1) (by omega)
        (good_next P hi hk1 ((cont_iff ht hHp hD (by omega) hD0 P.hDH hi).1 hc))
      exact ⟨r, .next _ _ hc hr⟩
    · exact ⟨_, .stop _ hc⟩

/-! ### Before the loop -/

theorem pre_spec {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {d : JInt t} (hd : d.val ≠ 0) :
    ∃ anc ad s0, smiPre d = .ok (anc, ad, s0) ∧ ∃ c, Params H anc.val ad.val c t.bits ∧
      (d.val < 0 → c = 1 ∧ ad.val = -d.val) ∧ (0 < d.val → c = 0 ∧ ad.val = d.val) ∧
      Inv H anc.val ad.val (t.bits - 1) s0 := by
  obtain ⟨hu, hub, hmin, hmax, hW, hn8, hn128⟩ := tfacts ht
  have hb := H_ge ht hH
  have hdb := val_bounds ht hH d
  obtain ⟨c, hcdef⟩ : ∃ c : Int, (if d.val < 0 then (1 : Int) else 0) = c := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Int, (if d.val < 0 then -d.val else d.val) = D := ⟨_, rfl⟩
  have hcD : (d.val < 0 ∧ c = 1 ∧ D = -d.val) ∨ (0 < d.val ∧ c = 0 ∧ D = d.val) := by
    by_cases hneg : d.val < 0
    · rw [ite_eq_left hneg] at hcdef hDdef
      left; omega
    · rw [ite_eq_right hneg] at hcdef hDdef
      right; omega
  have hsm : (JInt.rem t.toUnsigned (JInt.typemin t)).val = H := by
    rw [rem_val]
    show wrapInt t.toUnsigned (wrapInt t t.min) = H
    rw [hmin, hH, wrapS_id ht hH (by omega) (by omega), wrapU_neg ht hH (by omega) (by omega)]
    omega
  have hadv : (JInt.rem t.toUnsigned (jabs d)).val = D := by
    rw [rem_val, jabs_val ht hH]
    rcases hcD with ⟨hneg, -, hD⟩ | ⟨hpos, -, hD⟩
    · rw [ite_eq_left hneg]
      by_cases hm : d.val = -H
      · rw [ite_eq_left hm, wrapU_neg ht hH (by omega) (by omega)]
        omega
      · rw [ite_eq_right hm, wrapU_id ht hH (by omega) (by omega)]
        omega
    · rw [ite_eq_right (by omega), wrapU_id ht hH (by omega) (by omega)]
      omega
  have htt : (JInt.rem t.toUnsigned (JInt.typemin t) +
      JInt.lit t.toUnsigned (if d.val < 0 then 1 else 0)).val = H + c := by
    rw [val_add, hsm, val_lit, hcdef, wrapU_id ht hH (show 0 ≤ c by omega) (by omega),
      wrapU_id ht hH (by omega) (by omega)]
  simp only [smiPre, hd, ↓reduceIte]
  generalize hTT : JInt.rem t.toUnsigned (JInt.typemin t) +
    JInt.lit t.toUnsigned (if d.val < 0 then 1 else 0) = tt
  generalize hSM : JInt.rem t.toUnsigned (JInt.typemin t) = sm
  generalize hAD : JInt.rem t.toUnsigned (jabs d) = ad
  rw [hTT] at htt
  rw [hSM] at hsm
  rw [hAD] at hadv
  have hD0 : ad.val ≠ 0 := by omega
  simp only [remInt_ok hD0, bind_ok]
  have hrr : (JInt.wrap t.toUnsigned (tt.val.tmod ad.val)).val = (H + c) % D := by
    rw [wrap_val, htt, hadv, Int.tmod_eq_emod_of_nonneg (by omega)]
    have r0 := Int.emod_nonneg (H + c) (show D ≠ 0 by omega)
    have r1 := Int.emod_lt_of_pos (H + c) (show 0 < D by omega)
    exact wrapU_id ht hH r0 (by omega)
  generalize hRR : JInt.wrap t.toUnsigned (tt.val.tmod ad.val) = rr
  rw [hRR] at hrr
  have r0 := Int.emod_nonneg (H + c) (show D ≠ 0 by omega)
  have r1 := Int.emod_lt_of_pos (H + c) (show 0 < D by omega)
  have hancv : (tt - JInt.lit t.toUnsigned 1 - rr).val = H + c - 1 - (H + c) % D := by
    rw [val_sub, val_sub, htt, val_lit, hrr, wrapU_id ht hH (show (0 : Int) ≤ 1 by omega) (by omega),
      wrapU_id ht hH (x := H + c - 1) (by omega) (by omega),
      wrapU_id ht hH (x := H + c - 1 - (H + c) % D) (by omega) (by omega)]
  generalize hANC : tt - JInt.lit t.toUnsigned 1 - rr = anc
  rw [hANC] at hancv
  have hA0 : anc.val ≠ 0 := by omega
  simp only [divU_ok hu hA0, remInt_ok hA0, divU_ok hu hD0, bind_ok, pure_ok]
  refine ⟨anc, ad, _, rfl, c, ?_, ?_, ?_, ?_⟩
  · refine ⟨hH.symm, hn8, hn128, by omega, by omega, by omega, ?_, by rw [hancv, hadv]⟩
    intro h
    omega
  · intro h; omega
  · intro h; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (JInt.lit .i64 ((t.bits : Int) - 1)).val = ((t.bits - 1 : Nat) : Int)
      rw [val_lit, wrap64 _ (by omega) (by omega)]
      omega
    · show (JInt.wrap t.toUnsigned (sm.val.tdiv anc.val)).val = (2 : Int) ^ (t.bits - 1) / anc.val
      have hq := Int.ediv_le_self (b := anc.val) (show 0 ≤ H by omega)
      have hq0 := Int.ediv_nonneg (show 0 ≤ H by omega) (show 0 ≤ anc.val by omega)
      rw [wrap_val, hsm, hH, Int.tdiv_eq_ediv_of_nonneg (by omega), wrapU_id ht hH hq0 (by omega)]
    · show (JInt.wrap t.toUnsigned (sm.val.tmod anc.val)).val = (2 : Int) ^ (t.bits - 1) % anc.val
      have q0 := Int.emod_nonneg H (show anc.val ≠ 0 by omega)
      have q1 := Int.emod_lt_of_pos H (show 0 < anc.val by omega)
      rw [wrap_val, hsm, hH, Int.tmod_eq_emod_of_nonneg (by omega), wrapU_id ht hH q0 (by omega)]
    · show (JInt.wrap t.toUnsigned (sm.val.tdiv ad.val)).val =
        (2 : Int) ^ (t.bits - 1) / ad.val % (2 * H)
      rw [wrap_val, hsm, hH, Int.tdiv_eq_ediv_of_nonneg (by omega), wrapU_eq ht hH]
    · show (JInt.wrap t.toUnsigned (sm.val.tmod ad.val)).val = (2 : Int) ^ (t.bits - 1) % ad.val
      have q0 := Int.emod_nonneg H (show ad.val ≠ 0 by omega)
      have q1 := Int.emod_lt_of_pos H (show 0 < ad.val by omega)
      rw [wrap_val, hsm, hH, Int.tmod_eq_emod_of_nonneg (by omega), wrapU_id ht hH q0 (by omega)]

theorem pre_facts {t : IntTy} (ht : t.signed = true) {H : Int} (hH : (2 : Int) ^ (t.bits - 1) = H)
    {d : JInt t} (hd : d.val ≠ 0) {anc ad : JInt t.toUnsigned} {s0 : SmiState t}
    (h : smiPre d = .ok (anc, ad, s0)) :
    ∃ c, Params H anc.val ad.val c t.bits ∧
      (d.val < 0 → c = 1 ∧ ad.val = -d.val) ∧ (0 < d.val → c = 0 ∧ ad.val = d.val) ∧
      Inv H anc.val ad.val (t.bits - 1) s0 := by
  obtain ⟨anc', ad', s0', h', hrest⟩ := pre_spec ht hH hd
  rw [h'] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact hrest

/-! ### After the loop -/

theorem convert_val {u : IntTy} {x : Int} {sh : JInt u} (h : JInt.convert u x = .ok sh) :
    sh.val = x := by
  unfold JInt.convert at h
  split at h
  · cases h; rfl
  · cases h

theorem convert_u8 {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 255) :
    ∃ sh : JInt .u8, JInt.convert .u8 x = .ok sh := by
  have hmin : IntTy.u8.min = 0 := by decide
  have hmax : IntTy.u8.max = 255 := by decide
  unfold JInt.convert
  rw [dite_eq_left (show IntTy.u8.min ≤ x ∧ x ≤ IntTy.u8.max by rw [hmin, hmax]; exact ⟨h0, h1⟩)]
  exact ⟨_, rfl⟩

theorem finish_fields {t : IntTy} {d : JInt t} {s : SmiState t} {mi : SignedMI t}
    (h : smiFinish d s = .ok mi) :
    mi.divisor = d ∧ mi.multiplier = flipsign (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)) d ∧
    mi.addmul = (if d.val > 0 ∧ (flipsign (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)) d).val < 0
        then JInt.lit .i8 1
      else if d.val < 0 ∧ (flipsign (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)) d).val > 0
        then JInt.lit .i8 (-1) else JInt.lit .i8 0) ∧
    mi.shift.val = (s.p - JInt.lit .i64 (t.bits : Int)).val := by
  simp only [smiFinish] at h
  cases hc : JInt.convert IntTy.u8 (s.p - JInt.lit .i64 (t.bits : Int)).val with
  | error e =>
    rw [hc, bind_err] at h
    cases h
  | ok sh =>
    rw [hc, bind_ok, pure_ok] at h
    cases h
    exact ⟨rfl, rfl, rfl, convert_val hc⟩

theorem finish_ok {t : IntTy} {d : JInt t} {s : SmiState t}
    (h0 : 0 ≤ (s.p - JInt.lit .i64 (t.bits : Int)).val)
    (h1 : (s.p - JInt.lit .i64 (t.bits : Int)).val ≤ 255) :
    ∃ mi, smiFinish d s = .ok mi := by
  obtain ⟨sh, hc⟩ := convert_u8 h0 h1
  simp only [smiFinish]
  rw [hc, bind_ok, pure_ok]
  exact ⟨_, rfl⟩

theorem flipsign_val {t : IntTy} (x d : JInt t) :
    (flipsign x d).val = if d.val < 0 then (-x).val else x.val := by
  unfold flipsign
  split <;> rfl

theorem magic_split {t : IntTy} (ht : t.signed = true) {H : Int}
    (hH : (2 : Int) ^ (t.bits - 1) = H) {d : JInt t} (hd : d.val ≠ 0) {M : Int} (hM1 : 1 ≤ M)
    (hM2 : M < 2 * H) {mr : JInt t} (hmr : mr.val = wrapInt t M) :
    (flipsign mr d).val + 2 * H * (if d.val > 0 ∧ (flipsign mr d).val < 0 then JInt.lit .i8 1
      else if d.val < 0 ∧ (flipsign mr d).val > 0 then JInt.lit .i8 (-1)
      else JInt.lit .i8 0).val = (if d.val < 0 then -M else M) ∧
    -1 ≤ (if d.val > 0 ∧ (flipsign mr d).val < 0 then JInt.lit .i8 1
      else if d.val < 0 ∧ (flipsign mr d).val > 0 then JInt.lit .i8 (-1)
      else JInt.lit .i8 0).val ∧
    (if d.val > 0 ∧ (flipsign mr d).val < 0 then JInt.lit .i8 1
      else if d.val < 0 ∧ (flipsign mr d).val > 0 then JInt.lit .i8 (-1)
      else JInt.lit .i8 0).val ≤ 1 := by
  have hb := H_ge ht hH
  have l1 : (JInt.lit .i8 1).val = 1 := by decide
  have l0 : (JInt.lit .i8 0).val = 0 := by decide
  have lm : (JInt.lit .i8 (-1)).val = -1 := by decide
  obtain ⟨v, hv⟩ : ∃ v, (flipsign mr d).val = v := ⟨_, rfl⟩
  have hfv := hv
  rw [flipsign_val, val_neg, hmr] at hfv
  rw [hv]
  by_cases hneg : d.val < 0
  · rw [ite_eq_left hneg] at hfv ⊢
    by_cases hMH : M < H
    · rw [wrapS_id ht hH (x := M) (by omega) hMH, wrapS_id ht hH (x := -M) (by omega) (by omega)]
        at hfv
      rw [ite_eq_right (show ¬(d.val > 0 ∧ v < 0) by omega),
        ite_eq_right (show ¬(d.val < 0 ∧ v > 0) by omega),
        l0]
      omega
    · by_cases hMe : M = H
      · rw [wrapS_hi ht hH (x := M) (by omega) (by omega),
          wrapS_hi ht hH (x := -(M - 2 * H)) (by omega) (by omega)] at hfv
        rw [ite_eq_right (show ¬(d.val > 0 ∧ v < 0) by omega),
          ite_eq_right (show ¬(d.val < 0 ∧ v > 0) by omega), l0]
        omega
      · rw [wrapS_hi ht hH (x := M) (by omega) (by omega),
          wrapS_id ht hH (x := -(M - 2 * H)) (by omega) (by omega)] at hfv
        rw [ite_eq_right (show ¬(d.val > 0 ∧ v < 0) by omega),
          ite_eq_left (show d.val < 0 ∧ v > 0 by omega), lm]
        omega
  · rw [ite_eq_right hneg] at hfv ⊢
    by_cases hMH : M < H
    · rw [wrapS_id ht hH (x := M) (by omega) hMH] at hfv
      rw [ite_eq_right (show ¬(d.val > 0 ∧ v < 0) by omega),
        ite_eq_right (show ¬(d.val < 0 ∧ v > 0) by omega),
        l0]
      omega
    · rw [wrapS_hi ht hH (x := M) (by omega) (by omega)] at hfv
      rw [ite_eq_left (show d.val > 0 ∧ v < 0 by omega), l1]
      omega

/-! ### Evaluating `div(a, mi)` -/

theorem smiDiv_formula {t : IntTy} (ht : t.signed = true) {H : Int}
    (hH : (2 : Int) ^ (t.bits - 1) = H) (a : JInt t) (mi : SignedMI t)
    (hj : (jabs mi.divisor).val ≠ 1) (ham : -1 ≤ mi.addmul.val ∧ mi.addmul.val ≤ 1) {S : Int}
    (hS : mi.multiplier.val + 2 * H * mi.addmul.val = S)
    (hr1 : -(2 * H * H) ≤ a.val * S) (hr2 : a.val * S < 2 * H * H) :
    (smiDiv a mi).val = wrapInt t ((if a.val * S < 0 then 1 else 0) +
      a.val * S / (2 * H * 2 ^ mi.shift.val.toNat)) := by
  have hb := H_ge ht hH
  obtain ⟨-, -, -, -, hW, -⟩ := tfacts ht
  rw [hH] at hW
  have h2H : (0 : Int) < 2 * H := by omega
  have hy : (mulHi a mi.multiplier + JInt.rem t (a * JInt.rem t mi.addmul)).val =
      a.val * S / (2 * H) := by
    rw [val_add, mulHi_val, rem_val, val_mul, rem_val,
      wrapS_id ht hH (show -H ≤ mi.addmul.val by omega) (by omega), wrapInt_wrapInt, wrapInt_add, hW]
    have e : a.val * mi.multiplier.val / (2 * H) + a.val * mi.addmul.val = a.val * S / (2 * H) := by
      rw [← hS, show a.val * (mi.multiplier.val + 2 * H * mi.addmul.val) =
          a.val * mi.multiplier.val + 2 * H * (a.val * mi.addmul.val) by grind,
        Int.add_mul_ediv_left _ _ (by omega)]
    rw [e]
    obtain ⟨l1, l2⟩ := ediv_range h2H hr1 hr2
    exact wrapS_id ht hH l1 l2
  simp only [smiDiv]
  rw [ite_eq_right hj, rem_val, hy, val_add, shr_val, hy, val_lit, wrapInt_wrapInt, wrapInt_add,
    ediv_ediv h2H (pow2_pos _)]
  by_cases hneg : a.val * S < 0
  · rw [ite_eq_left ((ediv_neg_iff h2H).2 hneg), ite_eq_left hneg]
  · rw [ite_eq_right (fun h => hneg ((ediv_neg_iff h2H).1 h)), ite_eq_right hneg]

theorem smiNew_divisor {t : IntTy} {d : JInt t} {mi : SignedMI t} (hmi : SmiNew d mi) :
    mi.divisor = d := by
  obtain ⟨_, _, _, _, _, _, hfin⟩ := hmi
  exact (finish_fields hfin).1

theorem smiNew_exists {t : IntTy} (ht : t.signed = true) {d : JInt t} (hd : d.val ≠ 0) :
    ∃ mi, SmiNew d mi := by
  obtain ⟨H, hH⟩ : ∃ H, (2 : Int) ^ (t.bits - 1) = H := ⟨_, rfl⟩
  obtain ⟨anc, ad, s0, hpre, c, Pm, -, -, hinv0⟩ := pre_spec ht hH hd
  have hg0 := init_good Pm hinv0
  have hn := Pm.hn
  have hn' := Pm.hn'
  obtain ⟨s, hl⟩ := loop_exists ht Pm rfl rfl (t.bits + 1) s0 (t.bits - 1) (by omega) hg0
  obtain ⟨p, hinvp, hp1, hp2, -, -⟩ := loop_final ht Pm rfl rfl hl _ hg0
  have hsh : (s.p - JInt.lit .i64 (t.bits : Int)).val = (p : Int) - t.bits := by
    rw [val_sub, hinvp.1, val_lit, wrap64 (t.bits : Int) (by omega) (by omega),
      wrap64 _ (by omega) (by omega)]
  obtain ⟨mi, hmi⟩ := finish_ok (d := d) (s := s) (by rw [hsh]; omega) (by rw [hsh]; omega)
  exact ⟨mi, anc, ad, s0, s, hpre, hl, hmi⟩

theorem smiDiv_val {t : IntTy} (ht : t.signed = true) {d : JInt t} (hd : d.val ≠ 0)
    {mi : SignedMI t} (hmi : SmiNew d mi) (a : JInt t) :
    (smiDiv a mi).val = wrapInt t (a.val.tdiv d.val) := by
  obtain ⟨anc, ad, s0, s, hpre, hloop, hfin⟩ := hmi
  obtain ⟨H, hH⟩ : ∃ H, (2 : Int) ^ (t.bits - 1) = H := ⟨_, rfl⟩
  obtain ⟨c, Pm, hDneg, hDpos, hinv0⟩ := pre_facts ht hH hd hpre
  obtain ⟨hHb, -, hAH, hDA, hA2, -⟩ := Pm.facts
  have hc := Pm.hc
  have hD1 := Pm.hD1
  have hDH := Pm.hDH
  obtain ⟨p, hinvp, hp1, hp2, hexit, hprev⟩ := loop_final ht Pm rfl rfl hloop _ (init_good Pm hinv0)
  obtain ⟨hdv, hmul, hadd, hsh⟩ := finish_fields hfin
  have hab := val_bounds ht hH a
  have hdb := val_bounds ht hH d
  obtain ⟨-, -, -, -, hW, hn8, hn128⟩ := tfacts ht
  rw [hH] at hW
  by_cases hD1' : ad.val = 1
  · have hd1 : d.val = 1 ∨ d.val = -1 := by
      by_cases hneg : d.val < 0
      · have := (hDneg hneg).2; omega
      · have := (hDpos (by omega)).2; omega
    have hj : (jabs d).val = 1 := by
      rw [jabs_val ht hH]
      rcases hd1 with h | h
      · rw [ite_eq_right (by omega), h]
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), h]; rfl
    simp only [smiDiv]
    rw [hdv, ite_eq_left hj, val_mul]
    rcases hd1 with h | h
    · rw [h, Int.tdiv_one, Int.mul_one]
    · rw [h, Int.tdiv_neg, Int.tdiv_one]
      congr 1
      omega
  · have hD2 : 2 ≤ ad.val := by omega
    have hj : (jabs d).val ≠ 1 := by
      rw [jabs_val ht hH]
      by_cases hneg : d.val < 0
      · have := (hDneg hneg).2
        rw [ite_eq_left hneg]
        by_cases hm : d.val = -H
        · rw [ite_eq_left hm]; omega
        · rw [ite_eq_right hm]; omega
      · have := (hDpos (by omega)).2
        rw [ite_eq_right hneg]; omega
    have hshv : mi.shift.val = (p : Int) - t.bits := by
      rw [hsh, val_sub, hinvp.1, val_lit, wrap64 (t.bits : Int) (by omega) (by omega),
        wrap64 _ (by omega) (by omega)]
    have hshn : mi.shift.val.toNat = p - t.bits := by
      rw [hshv, show (p : Int) - t.bits = ((p - t.bits : Nat) : Int) by omega, Int.toNat_natCast]
    have hTp : 2 * H * 2 ^ (p - t.bits) = (2 : Int) ^ p := by
      rw [← hW, ← pow2_add]; congr 1; omega
    obtain ⟨M, hMdef⟩ : ∃ M, (2 : Int) ^ p / ad.val + 1 = M := ⟨_, rfl⟩
    have hMlt : M < 2 * H := by rw [← hMdef]; exact magic_lt Pm hD2 hp1 hprev
    have hM1 : 1 ≤ M := by
      rw [← hMdef]
      have := Int.ediv_nonneg (Int.le_of_lt (pow2_pos p)) (show 0 ≤ ad.val by omega)
      omega
    have one : (JInt.lit t.toUnsigned 1).val = 1 := by
      rw [val_lit, wrapU_id ht hH (by omega) (by omega)]
    have hmr : (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)).val = wrapInt t M := by
      rw [rem_val, val_add, hinvp.2.2.2.1, one, wrapU_eq ht hH, emod_add1, hMdef,
        Int.emod_eq_of_lt (by omega) hMlt]
    obtain ⟨hms, ham1, ham2⟩ := magic_split ht hH hd hM1 hMlt hmr
    have hS : mi.multiplier.val + 2 * H * mi.addmul.val = if d.val < 0 then -M else M := by
      rw [hmul, hadd]; exact hms
    have ham : -1 ≤ mi.addmul.val ∧ mi.addmul.val ≤ 1 := by
      rw [hadd]; exact ⟨ham1, ham2⟩
    obtain ⟨b, hbS, hb0, hb1, hbt⟩ : ∃ b, a.val * (if d.val < 0 then -M else M) = b * M ∧
        -(H - c) ≤ b ∧ b ≤ H + c - 1 ∧ b.tdiv ad.val = a.val.tdiv d.val := by
      by_cases hneg : d.val < 0
      · obtain ⟨hc1, hadn⟩ := hDneg hneg
        refine ⟨-a.val, by rw [ite_eq_left hneg, Int.mul_neg, Int.neg_mul], by omega, by omega, ?_⟩
        rw [hadn, Int.neg_tdiv_neg]
      · obtain ⟨hc0, hadp⟩ := hDpos (by omega)
        exact ⟨a.val, by rw [ite_eq_right hneg], by omega, by omega, by rw [hadp]⟩
    have pr := prod_range (show 0 < H by omega) (show -H ≤ b by omega) (show b ≤ H by omega)
      (show 0 ≤ M by omega) hMlt
    rw [smiDiv_formula ht hH a mi (by rw [hdv]; exact hj) ham hS (by rw [hbS]; exact pr.1)
      (by rw [hbS]; exact pr.2), hbS, hshn, hTp, Int.add_comm,
      core_tdiv Pm hD2 hp1 rfl hMdef.symm hexit hb0 hb1, hbt]

theorem mod_ok {t : IntTy} (ht : t.signed = true) {a b : JInt t} (hb : b.val ≠ 0)
    (hb1 : b.val ≠ -1) :
    JInt.mod a b = .ok (a - (JInt.wrap t (a.val.tdiv b.val) - JInt.lit t
      (if ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap t (a.val.tdiv b.val) * b).val ≠ a.val then 1 else 0)) * b) := by
  have hdiv : JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
    rw [JInt.div, ite_eq_right hb,
      ite_eq_right (show ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) from fun h => hb1 h.2.2)]
  rw [JInt.mod, ite_eq_left ht, ite_eq_right hb1, JInt.fld, hdiv]
  simp only [bind_ok]
  rw [ite_eq_left ht]
  simp only [pure_ok, bind_ok]

end SmiProof

open SmiProof in
/-- The signed constructor terminates for every nonzero divisor, and `div(a, mi)` equals the
truncating `div(a, d)` whenever the latter does not throw. -/
theorem smiDivCorrect : SmiDivCorrect := by
  intro t ht a d hd hnot
  refine ⟨smiNew_exists ht hd, fun mi hmi => ?_⟩
  have hv := smiDiv_val ht hd hmi a
  rw [JInt.div, ite_eq_right hd,
    ite_eq_right (show ¬(t.signed = true ∧ a.val = t.min ∧ d.val = -1) from
      fun h => hnot ⟨h.2.1, h.2.2⟩)]
  exact congrArg Except.ok (Subtype.ext hv)

open SmiProof in
/-- `rem(a, mi)` and `mod(a, mi)` agree with `rem(a, d)` and `mod(a, d)` for every dividend,
including `typemin` with divisor `-1`. -/
theorem smiRemModCorrect : SmiRemModCorrect := by
  intro t ht a d hd mi hmi
  have hv := smiDiv_val ht hd hmi a
  have hdv := smiNew_divisor hmi
  obtain ⟨H, hH⟩ : ∃ H, (2 : Int) ^ (t.bits - 1) = H := ⟨_, rfl⟩
  have hb := H_ge ht hH
  have hab := val_bounds ht hH a
  have hdb := val_bounds ht hH d
  have hR : (smiRem a mi).val = wrapInt t (a.val.tmod d.val) := by
    show (a - smiDiv a mi * mi.divisor).val = _
    rw [val_sub, val_mul, hv, hdv, wrap_mul_l, wrap_sub_r]
    congr 1
    have e := Int.tmod_add_mul_tdiv a.val d.val
    have i : a.val.tdiv d.val * d.val = d.val * a.val.tdiv d.val := Int.mul_comm _ _
    omega
  obtain ⟨D, hD, hD0, hDH⟩ : ∃ D, (D = d.val ∨ D = -d.val) ∧ 0 < D ∧ D ≤ H := by
    by_cases hneg : d.val < 0
    · exact ⟨-d.val, Or.inr rfl, by omega, by omega⟩
    · exact ⟨d.val, Or.inl rfl, by omega, by omega⟩
  obtain ⟨tm1, tm2, tm3, tm4⟩ := tmod_facts a.val d.val hD hD0
  have hRw : wrapInt t (a.val.tmod d.val) = a.val.tmod d.val := wrapS_id ht hH (by omega) (by omega)
  rw [hRw] at hR
  refine ⟨?_, ?_⟩
  · rw [JInt.remInt, ite_eq_right hd]
    exact congrArg Except.ok (Subtype.ext (by rw [hR]; exact hRw.symm))
  · obtain ⟨R, hRdef⟩ : ∃ R, a.val.tmod d.val = R := ⟨_, rfl⟩
    rw [hRdef] at hR hRw tm1 tm2 tm3 tm4
    dsimp only [smiMod]
    rw [hdv]
    by_cases hm1 : d.val = -1
    · have hR0 : R = 0 := by rw [← hRdef, hm1, Int.tmod_neg, Int.tmod_one]
      rw [JInt.mod, ite_eq_left ht, ite_eq_left hm1, ite_eq_left (Or.inl (by rw [hR, hR0]))]
      exact congrArg Except.ok (Subtype.ext (by rw [hR, hR0, val_lit, wrapInt_zero]))
    · rw [mod_ok ht hd hm1]
      have hQd : (JInt.wrap t (a.val.tdiv d.val) * d).val = a.val - R := by
        rw [val_mul, wrap_val, wrap_mul_l]
        have e := Int.tmod_add_mul_tdiv a.val d.val
        have i : a.val.tdiv d.val * d.val = d.val * a.val.tdiv d.val := Int.mul_comm _ _
        rw [show a.val.tdiv d.val * d.val = a.val - R by omega]
        exact wrapS_id ht hH (by omega) (by omega)
      have hRHS : ∀ ci : Int, (a - (JInt.wrap t (a.val.tdiv d.val) - JInt.lit t ci) * d).val =
          wrapInt t (R + ci * d.val) := by
        intro ci
        rw [val_sub, val_mul, val_sub, wrap_val, val_lit, wrapInt_sub, wrap_mul_l, wrap_sub_r]
        congr 1
        have e := Int.tmod_add_mul_tdiv a.val d.val
        rw [hRdef] at e
        have i : (a.val.tdiv d.val - ci) * d.val = d.val * a.val.tdiv d.val - ci * d.val := by grind
        omega
      have hsgn : R ≠ 0 → (R < 0 ↔ a.val < 0) := by
        intro h0
        constructor
        · intro h
          refine Classical.byContradiction fun h' => ?_
          have := (tm3 (by omega)).1
          omega
        · intro h; have := (tm4 h).2; omega
      by_cases hs : R = 0 ∨ decide (R < 0) = decide (d.val < 0)
      · rw [ite_eq_left (by rw [hR]; exact hs), ite_eq_right]
        · exact congrArg Except.ok
            (Subtype.ext (by rw [hRHS, hR, Int.zero_mul, Int.add_zero, hRw]))
        · intro hci
          obtain ⟨hci1, hci2⟩ := hci
          rw [hQd] at hci2
          by_cases hR0 : R = 0
          · exact hci2 (by omega)
          · have h : decide (R < 0) = decide (d.val < 0) := by
              rcases hs with h | h
              · exact absurd h hR0
              · exact h
            rw [decide_eq_decide] at h
            have hiff := (hsgn hR0).symm.trans h
            rcases hci1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have := hiff.1 h1; omega
            · have := hiff.2 h2; omega
      · have hR0 : R ≠ 0 := fun h => hs (Or.inl h)
        have hnd : ¬ (R < 0 ↔ d.val < 0) := fun h => hs (Or.inr (decide_eq_decide.2 h))
        rw [ite_eq_right (by rw [hR]; exact hs), ite_eq_left]
        · exact congrArg Except.ok (Subtype.ext (by rw [val_add, hR, hRHS, Int.one_mul]))
        · refine ⟨?_, by rw [hQd]; omega⟩
          by_cases ha : a.val < 0
          · left
            refine ⟨ha, ?_⟩
            refine Classical.byContradiction fun hdn => ?_
            exact hnd ⟨fun _ => by omega, fun _ => (hsgn hR0).2 ha⟩
          · right
            refine ⟨by omega, ?_⟩
            refine Classical.byContradiction fun hdn => ?_
            exact hnd ⟨fun h => absurd ((hsgn hR0).1 h) ha, fun h => absurd h hdn⟩

end JuliaLean.ReinterpretArrays

namespace JuliaLean.ReinterpretArrays

/-- `ReshapedArray` index conversion with `SignedMultiplicativeInverse` division is correct. -/
theorem ind2subCorrect : Ind2subCorrect := ind2subCorrect_of smiDivCorrect

end JuliaLean.ReinterpretArrays
