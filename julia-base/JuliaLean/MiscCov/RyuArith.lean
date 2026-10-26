import JuliaLean.MiscCov.RyuProofs
import JuliaLean.MiscCov.UNat

/-!
Proofs of the wide-arithmetic properties of `base/ryu/utils.jl`: `mulshift`,
`umul256`, `mod1e9`, `mulshiftmod1e9`, `pow5`, `pow2`, the table formulas and the
shape of `generateinversetables()`.
-/

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean JuliaLean.ParsePrint JuliaLean.MiscCov

/-- Close an equation between casts of natural-number expressions. -/
macro "castEq" : tactic => `(tactic| first | (push_cast; done) | (push_cast; rfl))

/-! ### Product bounds -/

theorem mul_lt_sq {x y P : Nat} (hx : x < P) (hy : y < P) : x * y + 2 * P ≤ P * P + 1 := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  have h : x * y ≤ Q * Q := Nat.mul_le_mul (by omega) (by omega)
  have e : (Q + 1) * (Q + 1) = Q * Q + 2 * Q + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  omega

theorem mul_lt_mul_both {x y X Y : Nat} (hx : x < X) (hy : y < Y) : x * y < X * Y :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hx) (Nat.le_refl y))
    (Nat.mul_lt_mul_of_pos_left hy (by omega))

theorem expand4 (x y z w c : Nat) :
    (x + c * y) * (z + c * w) = x * z + c * (x * w) + c * (y * z) + c * (c * (y * w)) := by
  simp only [Nat.add_mul, Nat.mul_add]; ac_rfl

theorem expand3 (m a b c P Q : Nat) : m * (a + P * b + Q * c) = m * a + P * (m * b) + Q * (m * c) := by
  simp only [Nat.mul_add]; ac_rfl

theorem or_disjoint (a y k : Nat) (hy : y < 2 ^ k) : a * 2 ^ k ||| y = a * 2 ^ k + y := by
  rw [← Nat.shiftLeft_eq]; exact (Nat.shiftLeft_add_eq_or_of_lt hy a).symm

/-! ### `mulshift` -/

theorem mulshift_nat (n a mul j : Nat) (ha : a < 2 ^ n) (hm : mul < 2 ^ n * 2 ^ n) (hj : n ≤ j) :
    a * (mul % 2 ^ n) < 2 ^ n * 2 ^ n ∧ a * (mul / 2 ^ n) < 2 ^ n * 2 ^ n ∧
    a * (mul % 2 ^ n) / 2 ^ n + a * (mul / 2 ^ n) < 2 ^ n * 2 ^ n ∧
    (a * (mul % 2 ^ n) / 2 ^ n + a * (mul / 2 ^ n)) / 2 ^ (j - n) = a * mul / 2 ^ j := by
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlo : mul % 2 ^ n < 2 ^ n := Nat.mod_lt _ hP
  have hhi : mul / 2 ^ n < 2 ^ n := Nat.div_lt_of_lt_mul hm
  have b1 := mul_lt_sq ha hlo
  have b2 := mul_lt_sq ha hhi
  have hq : a * (mul % 2 ^ n) / 2 ^ n < 2 ^ n := Nat.div_lt_of_lt_mul (by omega)
  refine ⟨by omega, by omega, by omega, ?_⟩
  have e1 : a * mul = a * (mul % 2 ^ n) + 2 ^ n * (a * (mul / 2 ^ n)) := by
    conv => lhs; rw [← Nat.mod_add_div mul (2 ^ n)]
    rw [Nat.mul_add, Nat.mul_left_comm]
  have e2 : a * mul / 2 ^ n = a * (mul % 2 ^ n) / 2 ^ n + a * (mul / 2 ^ n) := by
    rw [e1, Nat.add_mul_div_left _ _ hP]
  rw [← e2, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' hj]

theorem mulshift_val (u : IntTy) (hu : u ∈ [IntTy.u16, .u32, .u64]) (m : JInt u)
    (mul : JInt (widenTy u)) (j : Int) (hj : (u.bits : Int) ≤ j) :
    (mulshift u m mul j).val = (m.val * mul.val / 2 ^ j.toNat) % 2 ^ (promU32 u).bits := by
  have hf : u.signed = false ∧ (widenTy u).signed = false ∧ (promU32 u).signed = false ∧
      2 ^ (widenTy u).bits = 2 ^ u.bits * 2 ^ u.bits := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> decide
  obtain ⟨hs, hws, hps, hwb⟩ := hf
  have ha := nv_lt hs m
  have hm := nv_lt hws mul
  rw [hwb] at hm
  have hjn : 0 ≤ j - u.bits := by omega
  obtain ⟨b1, b2, b3, e⟩ := mulshift_nat u.bits (nv m) (nv mul) j.toNat ha hm (by omega)
  have hk : (j - (u.bits : Int)).toNat = j.toNat - u.bits := by omega
  simp only [mulshift, shrI, hjn, ge_iff_le, ↓reduceIte]
  rw [val_nv hps, val_nv hs m, val_nv hws mul]
  rw [nv_rem hws hps, nv_shr hws, nv_add hws, nv_shr hws, nv_mul hws, nv_mul hws, nv_shr hws,
    nv_rem hs hws, nv_rem hs hws, nv_rem hws hs]
  rw [hwb]
  have hm1 : nv m % (2 ^ u.bits * 2 ^ u.bits) = nv m :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  have hlo : nv mul % 2 ^ u.bits % (2 ^ u.bits * 2 ^ u.bits) = nv mul % 2 ^ u.bits :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  rw [hm1, hlo, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3, hk, e]
  castEq

theorem mulshiftExact_proven : MulshiftExact := by
  intro u hu m mul j hj
  exact ⟨mulshift_val u hu m mul j hj, rfl, rfl⟩

/-! ### `umul256` -/

theorem nv_r64 (x : JInt .u128) : nv (JInt.rem .u64 x) = nv x % 2 ^ 64 := nv_rem rfl rfl x

theorem nv_r128 (x : JInt .u64) : nv (JInt.rem .u128 x) = nv x % 2 ^ 128 := nv_rem rfl rfl x

theorem nv_shr128 (x : JInt .u128) (k : Nat) : nv (shr x k) = nv x / 2 ^ k := nv_shr rfl x k

theorem nv_add128 (a b : JInt .u128) : nv (a + b) = (nv a + nv b) % 2 ^ 128 := nv_add rfl a b

theorem nv_lt64 (x : JInt .u64) : nv x < 2 ^ 64 := nv_lt rfl x

theorem nv_lt128 (x : JInt .u128) : nv x < 2 ^ 128 := nv_lt rfl x

theorem nv_prod64 (x y : JInt .u64) : nv (JInt.rem .u128 x * JInt.rem .u128 y) = nv x * nv y := by
  have hx := nv_lt64 x
  have hy := nv_lt64 y
  have hxy := mul_lt_mul_both hx hy
  rw [nv_mul (t := .u128) rfl, nv_r128, nv_r128]
  simp only [IntTy.bits]
  rw [Nat.mod_eq_of_lt (by omega : nv x < 2 ^ 128), Nat.mod_eq_of_lt (by omega : nv y < 2 ^ 128)]
  exact Nat.mod_eq_of_lt (by omega)

/-- `pLo` of `umul256`: `(mid2Lo << 64) | b00Lo` with both halves below `2^64`. -/
theorem or_halves (m y : Nat) (hm : m < 2 ^ 64) (hy : y < 2 ^ 64) :
    m % 2 ^ 128 * 2 ^ 64 % 2 ^ 128 ||| y % 2 ^ 128 = m * 2 ^ 64 + y := by
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y < 2 ^ 128),
    Nat.mod_eq_of_lt (by omega : m * 2 ^ 64 < 2 ^ 128)]
  exact or_disjoint m y 64 hy

theorem umul256_nat (a : JInt .u128) (bHi bLo : JInt .u64) :
    nv (umul256 a bHi bLo).1 + 2 ^ 128 * nv (umul256 a bHi bLo).2 = nv a * (nv bLo + 2 ^ 64 * nv bHi) := by
  have hA := nv_lt128 a
  have hH := nv_lt64 bHi
  have hL := nv_lt64 bLo
  simp only [umul256]
  generalize e1 : JInt.rem .u64 a = aLo
  generalize e2 : JInt.rem .u64 (shr a 64) = aHi
  have f1 : nv aLo = nv a % 2 ^ 64 := by rw [← e1, nv_r64]
  have f2 : nv aHi = nv a / 2 ^ 64 := by rw [← e2, nv_r64, nv_shr128]; omega
  have hal := nv_lt64 aLo
  have hah := nv_lt64 aHi
  have g00 := nv_prod64 aLo bLo
  have g01 := nv_prod64 aLo bHi
  have g10 := nv_prod64 aHi bLo
  have g11 := nv_prod64 aHi bHi
  have s00 := mul_lt_sq hal hL
  have s01 := mul_lt_sq hal hH
  have s10 := mul_lt_sq hah hL
  have s11 := mul_lt_sq hah hH
  rw [← g00] at s00
  rw [← g01] at s01
  rw [← g10] at s10
  rw [← g11] at s11
  generalize JInt.rem .u128 aLo * JInt.rem .u128 bLo = b00 at g00 s00 ⊢
  generalize JInt.rem .u128 aLo * JInt.rem .u128 bHi = b01 at g01 s01 ⊢
  generalize JInt.rem .u128 aHi * JInt.rem .u128 bLo = b10 at g10 s10 ⊢
  generalize JInt.rem .u128 aHi * JInt.rem .u128 bHi = b11 at g11 s11 ⊢
  generalize e7 : JInt.rem .u64 b00 = b00Lo
  generalize e8 : JInt.rem .u64 (shr b00 64) = b00Hi
  have f7 : nv b00Lo = nv b00 % 2 ^ 64 := by rw [← e7, nv_r64]
  have f8 : nv b00Hi = nv b00 / 2 ^ 64 := by rw [← e8, nv_r64, nv_shr128]; omega
  generalize e9 : b10 + JInt.rem .u128 b00Hi = mid1
  have f9 : nv mid1 = nv b10 + nv b00Hi := by
    rw [← e9, nv_add128, nv_r128]; have := nv_lt64 b00Hi; omega
  generalize e10 : JInt.rem .u64 mid1 = mid1Lo
  generalize e11 : JInt.rem .u64 (shr mid1 64) = mid1Hi
  have f10 : nv mid1Lo = nv mid1 % 2 ^ 64 := by rw [← e10, nv_r64]
  have f11 : nv mid1Hi = nv mid1 / 2 ^ 64 := by
    rw [← e11, nv_r64, nv_shr128]; have := nv_lt64 b00Hi; omega
  generalize e12 : b01 + JInt.rem .u128 mid1Lo = mid2
  have f12 : nv mid2 = nv b01 + nv mid1Lo := by
    rw [← e12, nv_add128, nv_r128]; have := nv_lt64 mid1Lo; omega
  generalize e13 : JInt.rem .u64 mid2 = mid2Lo
  generalize e14 : JInt.rem .u64 (shr mid2 64) = mid2Hi
  have f13 : nv mid2Lo = nv mid2 % 2 ^ 64 := by rw [← e13, nv_r64]
  have f14 : nv mid2Hi = nv mid2 / 2 ^ 64 := by
    rw [← e14, nv_r64, nv_shr128]; have := nv_lt64 mid1Lo; omega
  have h1 := nv_lt64 mid1Hi
  have h2 := nv_lt64 mid2Hi
  have hpHi : nv (b11 + JInt.rem .u128 mid1Hi + JInt.rem .u128 mid2Hi) = nv b11 + nv mid1Hi + nv mid2Hi := by
    rw [nv_add128, nv_add128, nv_r128, nv_r128]; omega
  rw [hpHi, nv_bor (t := .u128) rfl, nv_shl (t := .u128) rfl, nv_r128, nv_r128]
  simp only [IntTy.bits]
  rw [or_halves _ _ (nv_lt64 mid2Lo) (nv_lt64 b00Lo)]
  have hAe : nv a = nv a % 2 ^ 64 + 2 ^ 64 * (nv a / 2 ^ 64) := (Nat.mod_add_div _ _).symm
  rw [hAe, expand4, ← f1, ← f2, ← g00, ← g01, ← g10, ← g11]
  omega

theorem umul256Exact_proven : Umul256Exact := by
  intro a bHi bLo
  have E := umul256_nat a bHi bLo
  have hLo := nv_lt128 (umul256 a bHi bLo).1
  refine ⟨E, ?_⟩
  unfold umul256Hi
  omega

/-! ### `mod1e9` and `mulshiftmod1e9` -/

/-- The Granlund-Montgomery reciprocal of `mod1e9`: `floor(v * M / 2^157) == div(v, 10^9)`
for every `v < 2^128`. -/
theorem gm1e9 (v : Nat) (hv : v < 2 ^ 128) :
    v * 0x89705F4136B4A59731680A88F8953031 / 2 ^ 157 = v / 1000000000 := by
  omega

theorem mod1e9_nat (v : JInt .u128) : nv (mod1e9 v) = nv v % 10 ^ 9 := by
  have hv := nv_lt128 v
  have E := umul256_nat v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031)
  have c1 : nv (JInt.lit .u64 0x89705F4136B4A597) = 0x89705F4136B4A597 := by decide
  have c2 : nv (JInt.lit .u64 0x31680A88F8953031) = 0x31680A88F8953031 := by decide
  have c3 : nv (JInt.lit .u32 1000000000) = 1000000000 := by decide
  rw [c1, c2] at E
  have hLo := nv_lt128
    (umul256 v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031)).1
  have hgm := gm1e9 (nv v) hv
  simp only [mod1e9, umul256Hi]
  generalize umul256 v (JInt.lit .u64 0x89705F4136B4A597) (JInt.lit .u64 0x31680A88F8953031) = p at E hLo
  rw [nv_sub32, nv_mul (t := .u32) rfl, c3, nv_rem (t := .u128) rfl rfl, nv_rem (t := .u128) rfl rfl,
    nv_shr128]
  simp only [IntTy.bits]
  have h1 : nv p.2 = nv v * (0x31680A88F8953031 + 2 ^ 64 * 0x89705F4136B4A597) / 2 ^ 128 := by omega
  have hq : nv p.2 / 2 ^ 29 = nv v / 1000000000 := by
    rw [h1, Nat.div_div_eq_div_mul]
    omega
  rw [hq]
  omega

theorem mulshiftmod1e9_nat (m mula mulb mulc : JInt .u64) (j : Int) (hj : 128 ≤ j) :
    nv (mulshiftmod1e9 m mula mulb mulc j) =
      nv m * (nv mula + 2 ^ 64 * nv mulb + 2 ^ 128 * nv mulc) / 2 ^ j.toNat % 10 ^ 9 := by
  have hm := nv_lt64 m
  have ha := nv_lt64 mula
  have hb := nv_lt64 mulb
  have hc := nv_lt64 mulc
  have g0 := nv_prod64 m mula
  have g1 := nv_prod64 m mulb
  have g2 := nv_prod64 m mulc
  have s0 := mul_lt_sq hm ha
  have s1 := mul_lt_sq hm hb
  have s2 := mul_lt_sq hm hc
  rw [← g0] at s0
  rw [← g1] at s1
  rw [← g2] at s2
  have hjn : 0 ≤ j - 128 := by omega
  simp only [mulshiftmod1e9, shrI, hjn, ge_iff_le, ↓reduceIte]
  rw [mod1e9_nat, nv_shr128]
  generalize JInt.rem .u128 m * JInt.rem .u128 mula = b0 at g0 s0 ⊢
  generalize JInt.rem .u128 m * JInt.rem .u128 mulb = b1 at g1 s1 ⊢
  generalize JInt.rem .u128 m * JInt.rem .u128 mulc = b2 at g2 s2 ⊢
  generalize e1 : b1 + JInt.rem .u128 (JInt.rem .u64 (shr b0 64)) = mid
  have f1 : nv mid = nv b1 + nv b0 / 2 ^ 64 := by
    rw [← e1, nv_add128, nv_r128, nv_r64, nv_shr128]; omega
  generalize e2 : b2 + JInt.rem .u128 (JInt.rem .u64 (shr mid 64)) = s
  have f2 : nv s = nv b2 + nv mid / 2 ^ 64 := by
    rw [← e2, nv_add128, nv_r128, nv_r64, nv_shr128]; omega
  have hs : nv s = nv m * (nv mula + 2 ^ 64 * nv mulb + 2 ^ 128 * nv mulc) / 2 ^ 128 := by
    rw [expand3, ← g0, ← g1, ← g2]; omega
  have hk : 128 + (j - 128).toNat = j.toNat := by omega
  rw [hs, Nat.div_div_eq_div_mul, ← Nat.pow_add, hk]

theorem mod1e9Exact_proven : Mod1e9Exact :=
  ⟨mod1e9_nat, mulshiftmod1e9_nat⟩

/-! ### `pow5` and `pow2` -/

theorem wrappedPow5_small (p : JInt .i64) (h0 : 0 ≤ p.val) (h1 : p.val ≤ 27) :
    (wrappedPow5 p).val = 5 ^ p.val.toNat := by
  have hp : p.val.toNat ≤ 27 := by omega
  have hlt : 5 ^ p.val.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hp) (by decide)
  have hlt' : (5 : Int) ^ p.val.toNat < 2 ^ 64 := by exact_mod_cast hlt
  have h0' : (0 : Int) ≤ 5 ^ p.val.toNat := by exact_mod_cast Nat.zero_le (5 ^ p.val.toNat)
  simp only [wrappedPow5]
  have hr : IntTy.u64.min ≤ (5 : Int) ^ p.val.toNat ∧ (5 : Int) ^ p.val.toNat ≤ IntTy.u64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte]; omega
  rw [wrap_val_of_range (t := .u64) _ hr]

/-- For `28 ≤ p ≤ 308`, `5^p mod 2^64` exceeds `2^53`. -/
theorem wrappedPow5_large_table : ∀ k : Nat, k < 281 → 2 ^ 53 < 5 ^ (k + 28) % 2 ^ 64 :=
  forall_lt_of_all 281 _ (by decide +kernel)

theorem wrappedPow5_large (p : JInt .i64) (h0 : 28 ≤ p.val) (h1 : p.val ≤ 308) :
    2 ^ 53 < (wrappedPow5 p).val := by
  have h := wrappedPow5_large_table (p.val.toNat - 28) (by omega)
  rw [show p.val.toNat - 28 + 28 = p.val.toNat by omega] at h
  simp only [wrappedPow5]
  rw [wrap_val_u (t := .u64) rfl]
  simp only [IntTy.bits]
  exact_mod_cast h

theorem pow5_dvd_small (x : JInt .u64) (p : JInt .i64) (h0 : 0 ≤ p.val) (h1 : p.val ≤ 27) :
    pow5 x p = true ↔ (5 ^ p.val.toNat : Int) ∣ x.val := by
  simp only [pow5, wrappedPow5_small p h0 h1, beq_iff_eq]
  exact Int.dvd_iff_emod_eq_zero.symm

theorem mask_table : ∀ p : Nat, p < 64 → ((shlOne64 p - JInt.lit .i64 1).val % 2 ^ 64).toNat = 2 ^ p - 1 :=
  forall_lt_of_all 64 _ (by decide +kernel)

theorem pow2_nat {u : IntTy} (hu : u.signed = false) (hb : u.bits ≤ 64) (x : JInt u) (p : Nat) :
    pow2 x p = true ↔ (2 ^ p : Int) ∣ x.val := by
  have hx := nv_lt hu x
  have hx64 : nv x < 2 ^ 64 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hb)
  have hmask : ((shlOne64 p - JInt.lit .i64 1).val % 2 ^ 64).toNat = 2 ^ (min p 64) - 1 := by
    by_cases hp : p < 64
    · rw [Nat.min_eq_left (by omega)]; exact mask_table p hp
    · rw [Nat.min_eq_right (by omega)]
      have : shlOne64 p = shlOne64 64 := by simp [shlOne64, hp]
      rw [this]; decide
  simp only [pow2, hmask, beq_iff_eq]
  show nv x &&& (2 ^ min p 64 - 1) = 0 ↔ _
  rw [Nat.and_two_pow_sub_one_eq_mod, val_nv hu x,
    show (2 : Int) ^ p = ((2 ^ p : Nat) : Int) by castEq, Int.natCast_dvd_natCast,
    Nat.dvd_iff_mod_eq_zero]
  by_cases hp : p ≤ 64
  · rw [Nat.min_eq_left hp]
  · rw [Nat.min_eq_right (by omega), Nat.mod_eq_of_lt hx64,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx64 (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem pow5Pow2Exact_proven : Pow5Pow2Exact := by
  refine ⟨?_, ?_, fun x p => pow2_nat rfl (by decide) x p, fun x p => pow2_nat rfl (by decide) x p,
    fun T => by cases T <;> decide⟩
  · intro x p hx0 hx1 h0 h1
    by_cases hp : p.val ≤ 27
    · exact pow5_dvd_small x p h0 hp
    · have hw := wrappedPow5_large p (by omega) h1
      have hxv : (x.val % (wrappedPow5 p).val) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [pow5, hxv, beq_iff_eq]
      constructor
      · intro h; omega
      · intro hd
        exfalso
        have e : ((5 ^ p.val.toNat : Nat) : Int) = (5 : Int) ^ p.val.toNat := by rw [Int.natCast_pow]; rfl
        rw [← e, val_nv (t := .u64) rfl x, Int.natCast_dvd_natCast] at hd
        have hxn : 0 < nv x := by have := val_nv (t := .u64) rfl x; omega
        have hle := Nat.le_of_dvd hxn hd
        have h5 : 5 ^ 28 ≤ 5 ^ p.val.toNat := Nat.pow_le_pow_right (by decide) (by omega)
        have hx53 : nv x < 2 ^ 53 := by have := val_nv (t := .u64) rfl x; omega
        omega
  · intro T x p h0 h1
    have : qinvbound T ≤ 27 := by cases T <;> decide
    exact pow5_dvd_small x p h0 (by omega)

/-! ### `pow5invsplit` and `pow5split` formulas -/

theorem nbits_spec (n : Nat) (h : 0 < n) : 2 ^ (nbits n - 1) ≤ n ∧ n < 2 ^ nbits n := by
  unfold nbits
  rw [Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem nbits_eq (n m : Nat) (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1)) : nbits n = m + 1 := by
  have hn : n ≠ 0 := by have := Nat.two_pow_pos m; omega
  unfold nbits
  congr 1
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn).mpr h2)
  · exact (Nat.le_log2 hn).mpr h1

theorem nbits_pow5 (i : Nat) (hi : i < 3529) : (nbits (5 ^ i) : Int) = (pow5bits (JInt.lit .i64 i)).val := by
  have h := pow5bits_table i hi
  generalize (pow5bits (JInt.lit .i64 i)).val = k at h ⊢
  unfold CeilLog2Pow5 at h
  rcases h with ⟨rfl, rfl⟩ | ⟨_, hk1, hlo, hhi⟩
  · have := nbits_eq 1 0 (by decide) (by decide)
    simp only [Nat.pow_zero]
    omega
  · have hodd : 5 ^ i % 2 = 1 := by rw [Nat.pow_mod]; simp
    have hev : 2 ^ k.toNat % 2 = 0 := by
      obtain ⟨q, hq⟩ : ∃ q, k.toNat = q + 1 := ⟨k.toNat - 1, by omega⟩
      rw [hq, Nat.pow_succ, Nat.mul_mod_left]
    have hne : 5 ^ i ≠ 2 ^ k.toNat := fun e => by rw [e] at hodd; omega
    have := nbits_eq (5 ^ i) (k.toNat - 1) (Nat.le_of_lt hlo)
      (by rw [show k.toNat - 1 + 1 = k.toNat by omega]; omega)
    omega

/-- Unsigned `T.wide` bounds as numbers. -/
theorem wide_range (T : FT) (x : Nat) (hx : x < 2 ^ T.wide.bits) :
    T.wide.min ≤ (x : Int) ∧ (x : Int) ≤ T.wide.max := by
  cases T <;> simp only [FT.wide, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true,
    ↓reduceIte] at hx ⊢ <;> omega

theorem convert_ok (T : FT) (x : Nat) (hx : x < 2 ^ T.wide.bits) :
    ∃ v, JInt.convert T.wide (x : Int) = .ok v ∧ v.val = x := by
  refine ⟨⟨x, wide_range T x hx⟩, ?_, rfl⟩
  simp only [JInt.convert, dif_pos (wide_range T x hx)]

theorem pow5SplitFormulas_proven : Pow5SplitFormulas := by
  intro T i hi
  have hnb := nbits_pow5 i hi
  have hpos : 0 < 5 ^ i := Nat.pow_pos (by decide)
  obtain ⟨hlo, hhi⟩ := nbits_spec (5 ^ i) hpos
  have hN1 : 1 ≤ nbits (5 ^ i) := by unfold nbits; omega
  generalize hN : nbits (5 ^ i) = N at hlo hhi hnb hN1
  have hbits : pow5InvBitcount T + 2 ≤ T.wide.bits ∧ pow5Bitcount T ≤ T.wide.bits ∧ 1 ≤ pow5Bitcount T := by
    cases T <;> decide
  refine ⟨?_, ?_⟩
  · have hdiv : 2 ^ (N - 1 + pow5InvBitcount T) / 5 ^ i ≤ 2 ^ pow5InvBitcount T := by
      apply Nat.div_le_of_le_mul
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ hlo
    have hfit : 2 ^ (N - 1 + pow5InvBitcount T) / 5 ^ i + 1 < 2 ^ T.wide.bits := by
      have h1 : 2 ^ (pow5InvBitcount T + 2) ≤ 2 ^ T.wide.bits := Nat.pow_le_pow_right (by decide) hbits.1
      have h2 : 2 ^ (pow5InvBitcount T + 2) = 4 * 2 ^ pow5InvBitcount T := by
        rw [Nat.pow_add]; omega
      have := Nat.one_le_two_pow (n := pow5InvBitcount T)
      omega
    obtain ⟨v, hv, hvv⟩ := convert_ok T _ hfit
    refine ⟨v, ?_, ?_⟩
    · simp only [pow5invsplit]
      rw [show nbits (5 ^ i) = N from hN]
      exact_mod_cast hv
    · rw [hvv, ← hnb, show ((N : Int) - 1 + (pow5InvBitcount T : Int)).toNat = N - 1 + pow5InvBitcount T by omega]
      castEq
  · have hbc := hbits.2.2
    have hsplit : ∃ w : Nat, (pow5split T i = JInt.convert T.wide (w : Int)) ∧
        ((w : Int) = if (N : Int) - pow5Bitcount T ≥ 0 then 5 ^ i / 2 ^ ((N : Int) - pow5Bitcount T).toNat
          else 5 ^ i * 2 ^ (-((N : Int) - pow5Bitcount T)).toNat) ∧
        2 ^ (pow5Bitcount T - 1) ≤ w ∧ w < 2 ^ pow5Bitcount T := by
      by_cases hs : (N : Int) - pow5Bitcount T ≥ 0
      · have hsN : ((N : Int) - pow5Bitcount T).toNat + pow5Bitcount T = N := by omega
        generalize hS : ((N : Int) - pow5Bitcount T).toNat = s at hsN
        refine ⟨5 ^ i / 2 ^ s, ?_, ?_, ?_, ?_⟩
        · simp only [pow5split, hN, hs, ↓reduceIte]
          rw [hS]; castEq
        · rw [if_pos hs]; castEq
        · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
          exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hlo
        · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm, hsN]
          exact hhi
      · have hsN : N + ((-((N : Int) - pow5Bitcount T)).toNat) = pow5Bitcount T := by omega
        generalize hS : (-((N : Int) - pow5Bitcount T)).toNat = s at hsN
        refine ⟨5 ^ i * 2 ^ s, ?_, ?_, ?_, ?_⟩
        · simp only [pow5split, hN, hs, ↓reduceIte]
          rw [hS]; castEq
        · rw [if_neg hs]; castEq
        · rw [show pow5Bitcount T - 1 = (N - 1) + s by omega, Nat.pow_add]
          exact Nat.mul_le_mul_right _ hlo
        · rw [← hsN, Nat.pow_add]
          exact Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
    obtain ⟨w, hw, hwv, hw1, hw2⟩ := hsplit
    have hfit : w < 2 ^ T.wide.bits :=
      Nat.lt_of_lt_of_le hw2 (Nat.pow_le_pow_right (by decide) hbits.2.1)
    obtain ⟨v, hv, hvv⟩ := convert_ok T w hfit
    refine ⟨v, by rw [hw, hv], ?_, ?_, ?_⟩
    · dsimp only
      rw [hvv, hwv, ← hnb]
    · rw [hvv]; exact_mod_cast hw1
    · rw [hvv]; exact_mod_cast hw2

/-! ### `generateinversetables()` -/

/-- The bound every stored limb satisfies. -/
def LimbOk (t : Nat × Nat × Nat) : Prop := t.1 < 2 ^ 64 ∧ t.2.1 < 2 ^ 64 ∧ t.2.2 < 2 ^ 64

/-- `s'` extends the table of `s`, keeping every limb below `2^64`. -/
def Grows (s s' : InvState) : Prop :=
  s.split.length ≤ s'.split.length ∧ ((∀ t ∈ s.split, LimbOk t) → ∀ t ∈ s'.split, LimbOk t)

theorem grows_trans {a b c : InvState} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩

theorem invLoop_spec (idx : Nat) : ∀ (fuel i : Nat) (s : InvState), Grows s (invLoop idx fuel i s) := by
  intro fuel
  induction fuel with
  | zero => intro i s; exact ⟨Nat.le_refl _, fun h => h⟩
  | succ f ih =>
    intro i s
    have hs : ∀ c : Bool, (if c = true then { s with minBlock := some i } else s).split = s.split := by
      intro c; cases c <;> rfl
    simp only [invLoop]
    split
    · exact ih (i + 1) s
    · split
      · exact ⟨by rw [hs]; exact Nat.le_refl _, fun h => by rw [hs]; exact h⟩
      · apply grows_trans _ (ih (i + 1) _)
        refine ⟨?_, fun h t ht => ?_⟩
        · simp only [hs, List.length_append, List.length_singleton]; omega
        · simp only [hs, List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact h t ht
          · exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-- The loop invariant of `generateinversetables()` after `k` iterations. -/
def TabInv (k : Nat) (r : List Nat × List Nat × List (Nat × Nat × Nat)) : Prop :=
  r.1.length = k ∧ r.2.1.length = k ∧ r.1.Pairwise (· ≤ ·) ∧ (∀ o ∈ r.1, o ≤ r.2.2.length) ∧
  ((r.1 = [] ∧ r.2.2 = []) ∨ r.1.head? = some 0) ∧ (∀ t ∈ r.2.2, LimbOk t)

theorem genStep_inv (fuel k idx : Nat) (r : List Nat × List Nat × List (Nat × Nat × Nat))
    (h : TabInv k r) : TabInv (k + 1) (genStep fuel r idx) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨l1, l2⟩ := invLoop_spec idx fuel 0 ⟨r.2.2, none⟩
  simp only at l1 l2
  refine ⟨by simp [genStep, h1], by simp [genStep, h2], ?_, ?_, ?_, ?_⟩
  · simp only [genStep]
    rw [List.pairwise_append]
    refine ⟨h3, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]; exact h4 a ha
  · simp only [genStep]
    intro o ho
    simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact Nat.le_trans (h4 o ho) l1
    · exact l1
  · right
    simp only [genStep]
    rcases h5 with ⟨e1, e2⟩ | e
    · rw [e1, e2]; rfl
    · rw [List.head?_append, e]; rfl
  · exact l2 h6

theorem foldl_inv (fuel : Nat) : ∀ (l : List Nat) (k : Nat) (r : List Nat × List Nat × List (Nat × Nat × Nat)),
    TabInv k r → TabInv (k + l.length) (l.foldl (genStep fuel) r) := by
  intro l
  induction l with
  | nil => intro k r h; simpa using h
  | cons x xs ih =>
    intro k r h
    have := ih (k + 1) _ (genStep_inv fuel k x r h)
    simp only [List.foldl_cons, List.length_cons]
    rw [show k + (xs.length + 1) = k + 1 + xs.length by omega]
    exact this

theorem inverseTablesShape_proven : InverseTablesShape := by
  intro n fuel
  simp only [generateinversetables]
  have h := foldl_inv fuel (List.range n) 0 ([], [], []) ⟨rfl, rfl, List.Pairwise.nil, by simp, Or.inl ⟨rfl, rfl⟩, by simp⟩
  generalize (List.range n).foldl (genStep fuel) ([], [], []) = r at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [List.length_range, Nat.zero_add] at h1 h2
  refine ⟨by simp [h1], by simp [h2], by simp, ?_, by simp, ?_, h6⟩
  · rcases h5 with ⟨e1, e2⟩ | e
    · rw [e1, e2]; rfl
    · rw [List.head?_append, e]; rfl
  · rw [List.pairwise_append]
    refine ⟨h3, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]; exact h4 a ha

end JuliaLean.MiscCov.RyuUtils
