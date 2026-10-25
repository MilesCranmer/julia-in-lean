import JuliaLean.MathFuncs.PropsBasic
import JuliaLean.MathFuncs.PropsUniversal

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
Proofs of the bit-level properties of `PropsBasic` and `PropsUniversal`: `min`/`max`/`clamp`,
`copysign`/`flipsign`, `hypot`, `evalpoly`, the `log`/`log1p` domain errors, `pow` with a zero
or unit exponent or a unit base, and `exponent`/`significand`/`frexp`. The helper lemmas restate
`roundRat` (`fl2`, `rq`, `pk` mirror its private helpers) and the bit manipulations of
`ldexp`/`significand`/`frexp` in closed form.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

namespace ProofsBits

theorem tb_ofBits (n : Nat) : F64.toBits (F64.ofBits n) = n % 2^64 := by
  simp [F64.toBits, F64.ofBits]

theorem tb_lt (x : F64) : F64.toBits x < 2^64 := x.isLt

theorem f64_ext {x y : F64} (h : F64.toBits x = F64.toBits y) : x = y := BitVec.eq_of_toNat_eq h

theorem tb_abs (x : F64) : F64.toBits (F64.abs x) = F64.toBits x % 2^63 := by
  have := tb_lt x
  unfold F64.abs
  rw [tb_ofBits]
  omega

theorem tb_neg (x : F64) : F64.toBits (F64.neg x) =
    if F64.toBits x ≥ 2^63 then F64.toBits x - 2^63 else F64.toBits x + 2^63 := by
  have := tb_lt x
  unfold F64.neg
  by_cases h : F64.toBits x ≥ 2^63
  · have hs : F64.signbit x = true := by simp [F64.signbit, h]
    simp only [hs, h, ↓reduceIte, tb_ofBits]
    omega
  · have hs : F64.signbit x = false := by simp [F64.signbit]; omega
    simp only [hs, h, ↓reduceIte, tb_ofBits, Bool.false_eq_true]
    omega

theorem isnan_iff (x : F64) : F64.isnan x = true ↔
    (F64.toBits x / 2^52 % 2048 = 2047 ∧ F64.toBits x % 2^52 ≠ 0) := by
  simp [F64.isnan, F64.exponentField, F64.fraction]

theorem isnan_f (x : F64) : F64.isnan x = false ↔
    ¬(F64.toBits x / 2^52 % 2048 = 2047 ∧ F64.toBits x % 2^52 ≠ 0) := by
  rw [Bool.eq_false_iff, ne_eq, isnan_iff]

theorem iszero_iff (x : F64) : F64.iszero x = true ↔ F64.toBits x % 2^63 = 0 := by
  simp [F64.iszero, tb_abs]

theorem iszero_f (x : F64) : F64.iszero x = false ↔ ¬ F64.toBits x % 2^63 = 0 := by
  rw [Bool.eq_false_iff, ne_eq, iszero_iff]

theorem signbit_iff (x : F64) : F64.signbit x = true ↔ F64.toBits x ≥ 2^63 := by
  simp [F64.signbit]

theorem signbit_f (x : F64) : F64.signbit x = false ↔ F64.toBits x < 2^63 := by
  rw [Bool.eq_false_iff, ne_eq, signbit_iff]; omega

theorem isinf_iff (x : F64) : F64.isinf x = true ↔ F64.toBits x % 2^63 = 2047 * 2^52 := by
  simp [F64.isinf, tb_abs]

theorem lt_iff (x y : F64) : F64.lt x y = true ↔
    ¬(F64.toBits x / 2^52 % 2048 = 2047 ∧ F64.toBits x % 2^52 ≠ 0) ∧
    ¬(F64.toBits y / 2^52 % 2048 = 2047 ∧ F64.toBits y % 2^52 ≠ 0) ∧
    ¬(F64.toBits x % 2^63 = 0 ∧ F64.toBits y % 2^63 = 0) ∧
    ((F64.toBits x ≥ 2^63 ∧ F64.toBits y < 2^63) ∨
     (F64.toBits x ≥ 2^63 ∧ F64.toBits y ≥ 2^63 ∧ F64.toBits y < F64.toBits x) ∨
     (F64.toBits x < 2^63 ∧ F64.toBits y < 2^63 ∧ F64.toBits x < F64.toBits y)) := by
  unfold F64.lt
  cases nx : F64.isnan x <;> cases ny : F64.isnan y <;> cases zx : F64.iszero x <;>
    cases zy : F64.iszero y <;> cases sx : F64.signbit x <;> cases sy : F64.signbit y <;>
    simp only [isnan_iff, isnan_f, iszero_iff, iszero_f, signbit_iff, signbit_f]
      at nx ny zx zy sx sy <;>
    simp_all <;> omega

theorem eq_iff (x y : F64) : F64.eq x y = true ↔
    ¬(F64.toBits x / 2^52 % 2048 = 2047 ∧ F64.toBits x % 2^52 ≠ 0) ∧
    ¬(F64.toBits y / 2^52 % 2048 = 2047 ∧ F64.toBits y % 2^52 ≠ 0) ∧
    (F64.toBits x = F64.toBits y ∨ (F64.toBits x % 2^63 = 0 ∧ F64.toBits y % 2^63 = 0)) := by
  unfold F64.eq
  cases nx : F64.isnan x <;> cases ny : F64.isnan y <;> cases zx : F64.iszero x <;>
    cases zy : F64.iszero y <;>
    simp only [isnan_iff, isnan_f, iszero_iff, iszero_f] at nx ny zx zy <;>
    simp_all <;> omega

theorem isless_iff {x y : F64} (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    F64.isless x y = true ↔
    ((F64.toBits x ≥ 2^63 ∧ F64.toBits y < 2^63) ∨
     (F64.toBits x ≥ 2^63 ∧ F64.toBits y ≥ 2^63 ∧ F64.toBits y < F64.toBits x) ∨
     (F64.toBits x < 2^63 ∧ F64.toBits y < 2^63 ∧ F64.toBits x < F64.toBits y)) := by
  unfold F64.isless
  cases sx : F64.signbit x <;> cases sy : F64.signbit y <;>
    simp only [signbit_iff, signbit_f] at sx sy <;>
    simp_all <;> omega

theorem lt_asymm {x y : F64} (h : F64.lt x y = true) : F64.lt y x = false := by
  rw [Bool.eq_false_iff, ne_eq, lt_iff]
  rw [lt_iff] at h
  omega

theorem lt_nan_l {x y : F64} (h : F64.lt x y = true) : F64.isnan x = false := by
  rw [isnan_f]
  rw [lt_iff] at h
  omega

theorem lt_eq {x y : F64} (h : F64.lt x y = true) : F64.eq x y = false := by
  rw [Bool.eq_false_iff, ne_eq, eq_iff]
  rw [lt_iff] at h
  omega

theorem abs_neg (x : F64) : F64.abs (F64.neg x) = F64.abs x := by
  apply f64_ext
  have := tb_lt x
  rw [tb_abs, tb_abs, tb_neg]
  split <;> omega

theorem signbit_neg (x : F64) : F64.signbit (F64.neg x) = !F64.signbit x := by
  have := tb_lt x
  cases h1 : F64.signbit x
  · rw [signbit_f] at h1
    have h2 : ¬ F64.toBits x ≥ 2^63 := by omega
    show F64.signbit (F64.neg x) = true
    rw [signbit_iff, tb_neg]
    simp only [h2, ↓reduceIte]
    omega
  · rw [signbit_iff] at h1
    show F64.signbit (F64.neg x) = false
    rw [signbit_f, tb_neg]
    simp only [h1, ↓reduceIte]
    omega

theorem abs_of_isinf {x : F64} (h : F64.isinf x = true) : F64.abs x = F64.inf := by
  apply f64_ext
  rw [tb_abs]
  have h' := (isinf_iff x).mp h
  have : F64.toBits F64.inf = 2047 * 2^52 := by decide
  rw [this]
  exact h'

theorem div_inf_one : F64.div F64.inf F64.one = F64.inf := by decide

theorem isinf_inf : F64.isinf F64.inf = true := by decide

theorem toRat_zero (s : Bool) : F64.toRat (F64.zero s) = (0, 2^1074) := by
  cases s <;> decide

theorem powFFClamped_zero (x : F64) (s : Bool) : powFFClamped x (F64.zero s) = .ok F64.one := by
  unfold powFFClamped
  rw [toRat_zero]
  rfl

theorem ldexp_one_bits : ∀ i : Fin 2099,
    F64.toBits (F64.ldexp F64.one ((i : Int) - 1074)) =
      (if (i : Nat) < 52 then 2^(i : Nat) else ((i : Nat) - 51) * 2^52) := by
  decide +kernel

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]


theorem and_split {i a b c d : Nat} (hb : b < 2^i) (hd : d < 2^i) :
    (2^i*a + b) &&& (2^i*c + d) = 2^i*(a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow b hd)]
  split <;> simp [Nat.testBit_and]

theorem or_split {i a b c d : Nat} (hb : b < 2^i) (hd : d < 2^i) :
    (2^i*a + b) ||| (2^i*c + d) = 2^i*(a ||| c) + (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.or_lt_two_pow hb hd)]
  split <;> simp [Nat.testBit_or]

theorem or_split0 {i b c d : Nat} (hb : b < 2^i) (hd : d < 2^i) :
    b ||| (2^i*c + d) = 2^i*c + (b ||| d) := by
  have h := or_split (a := 0) (c := c) hb hd
  simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_or] at h
  exact h

theorem pack_bits {u K : Nat} (hu : u < 2^64) (hK : K < 2048) :
    Nat.lor (Nat.land u 0x800fffffffffffff) (K * 2^52) = u / 2^63 * 2^63 + K * 2^52 + u % 2^52 := by
  obtain ⟨s, E, f, hs, hE, hf, rfl⟩ : ∃ s E f, s < 2 ∧ E < 2^11 ∧ f < 2^52 ∧
      u = 2^52*(2^11*s + E) + f :=
    ⟨u/2^63, u/2^52%2048, u%2^52, by omega, by omega, by omega, by omega⟩
  have m1 : (0x800fffffffffffff : Nat) = 2^52*(2^11*1 + 0) + (2^52-1) := by decide
  have m2 : K * 2^52 = 2^52*(2^11*0 + K) + 0 := by omega
  show ((2^52*(2^11*s + E) + f) &&& 0x800fffffffffffff) ||| (K * 2^52) = _
  rw [m1, m2, and_split hf (by decide : 2^52 - 1 < 2^52),
    and_split hE (by decide : (0:Nat) < 2^11),
    or_split (Nat.and_lt_two_pow f (by decide : 2^52 - 1 < 2^52)) (by decide : (0:Nat) < 2^52),
    or_split (Nat.and_lt_two_pow E (by decide : (0:Nat) < 2^11)) hK]
  simp only [Nat.and_zero, Nat.zero_or, Nat.or_zero, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hf, Nat.and_one_is_mod]
  omega

theorem sign_or {u F : Nat} (hu : u < 2^64) (hF : F < 2^63) :
    Nat.lor F (Nat.land u 0x8000000000000000) = u / 2^63 * 2^63 + F := by
  obtain ⟨s, r, hs, hr, rfl⟩ : ∃ s r, s < 2 ∧ r < 2^63 ∧ u = 2^63*s + r :=
    ⟨u/2^63, u%2^63, by omega, by omega, by omega⟩
  have m1 : (0x8000000000000000 : Nat) = 2^63*1 + 0 := by decide
  show F ||| ((2^63*s + r) &&& 0x8000000000000000) = _
  rw [m1, and_split hr (by decide : (0:Nat) < 2^63), Nat.and_zero, Nat.and_one_is_mod,
    or_split0 hF (by decide : (0:Nat) < 2^63), Nat.or_zero]
  omega

theorem wrapU (n : Nat) (h : n < 2^64) : (JInt.wrap .u64 (Int.ofNat n)).val.toNat = n := by
  show ((n : Int) % 2^64).toNat = n
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem wrapI (a : Int) (h1 : -2^63 ≤ a) (h2 : a < 2^63) : (JInt.wrap .i64 a).val = a := by
  show (a + 2^63) % 2^64 - 2^63 = a
  omega

theorem toNat_eq {a : Int} {n : Nat} (h : a = n) : a.toNat = n := by
  subst h
  simp

theorem log2_facts {f : Nat} (h0 : f ≠ 0) (hf : f < 2^52) :
    f.log2 < 52 ∧ 2^f.log2 ≤ f ∧ f < 2^(f.log2+1) :=
  ⟨(Nat.log2_lt h0).mpr hf, Nat.log2_self_le h0, Nat.lt_log2_self⟩

theorem sub_mant {f : Nat} (h0 : f ≠ 0) (hf : f < 2^52) :
    2^52 ≤ f * 2^(52 - f.log2) ∧ f * 2^(52 - f.log2) < 2^53 ∧
      2^52 * (f * 2^(52 - f.log2)) = f * 2^(104 - f.log2) := by
  obtain ⟨h1, h2, h3⟩ := log2_facts h0 hf
  have e1 : 2^f.log2 * 2^(52 - f.log2) = 2^52 := by
    rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2^(f.log2+1) * 2^(52 - f.log2) = 2^53 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hp : 0 < 2^(52 - f.log2) := Nat.two_pow_pos _
  refine ⟨?_, ?_, ?_⟩
  · calc 2^52 = 2^f.log2 * 2^(52 - f.log2) := e1.symm
      _ ≤ f * 2^(52 - f.log2) := Nat.mul_le_mul_right _ h2
  · calc f * 2^(52 - f.log2) < 2^(f.log2+1) * 2^(52 - f.log2) :=
          Nat.mul_lt_mul_of_pos_right h3 hp
      _ = 2^53 := e2
  · rw [Nat.mul_left_comm, ← Nat.pow_add]
    congr 2
    omega

theorem exponent_eq (x : F64) : F64.exponent x =
    if F64.toBits (F64.abs x) ≥ 0x7ff0000000000000 then .error (.domainError "Cannot be NaN or Inf.")
    else if (Int.ofNat (F64.toBits (F64.abs x) >>> 52) == 0) = true then
      (if (F64.toBits (F64.abs x) == 0) = true then .error (.domainError "Cannot be ±0.0.")
       else .ok (1 - Int.ofNat ((if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true
          then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11) - 1023))
    else .ok (Int.ofNat (F64.toBits (F64.abs x) >>> 52) - 1023) := rfl

theorem exponent_ok (x : F64) (hfin : F64.isfinite x = true) (hz : F64.iszero x = false) :
    F64.exponent x = .ok (if F64.toBits x / 2^52 % 2048 = 0
      then ((F64.toBits x % 2^52).log2 : Int) - 1074
      else ((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1023) := by
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  have c1 : ¬ (F64.toBits x % 2^63 ≥ 0x7ff0000000000000) := by omega
  rw [exponent_eq, tb_abs, Nat.shiftRight_eq_div_pow, ite_f c1]
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · have c2 : (Int.ofNat (F64.toBits x % 2^63 / 2^52) == 0) = true := by
      simp only [beq_iff_eq, Int.ofNat_eq_natCast]; omega
    have c3 : ¬ ((F64.toBits x % 2^63 == 0) = true) := by
      simp only [beq_iff_eq]; omega
    have e1 : F64.toBits x % 2^63 = F64.toBits x % 2^52 := by omega
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    obtain ⟨h1, -, -⟩ := log2_facts hne (by omega)
    have c4 : ¬ ((F64.toBits x % 2^52 == 0) = true) := by simp only [beq_iff_eq]; omega
    rw [ite_t c2, ite_f c3, wrapU (F64.toBits x % 2^63) (by omega), e1, ite_f c4, ite_t hE,
      Except.ok.injEq, Int.ofNat_eq_natCast]
    omega
  · have c2 : ¬ ((Int.ofNat (F64.toBits x % 2^63 / 2^52) == 0) = true) := by
      simp only [beq_iff_eq, Int.ofNat_eq_natCast]; omega
    rw [ite_f c2, ite_f hE, Except.ok.injEq, Int.ofNat_eq_natCast]
    simp only [Nat.reducePow] at *
    omega

theorem significand_eq (x : F64) : F64.significand x =
    if F64.toBits (F64.abs x) ≥ 0x7ff0000000000000 then x
    else if F64.toBits (F64.abs x) ≤ 0xfffffffffffff then
      (if (F64.toBits (F64.abs x) == 0) = true then x
       else F64.ofBits (Nat.lor (Nat.land (Nat.lor
          (if (if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11 ≥ 64 then JInt.wrap .u64 (Int.ofNat 0)
          else JInt.wrap .u64 (Int.ofNat ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat <<< ((if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11)))).val.toNat
          (Nat.land (F64.toBits x) 0x8000000000000000)) 0x800fffffffffffff) 0x3ff0000000000000))
    else F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff) 0x3ff0000000000000) := rfl

theorem frexp_eq (x : F64) : F64.frexp x =
    if F64.toBits (F64.abs x) ≥ 0x7ff0000000000000 then (x, 0)
    else if (Int.ofNat (F64.toBits (F64.abs x) >>> 52) == 0) = true then
      (if (F64.toBits (F64.abs x) == 0) = true then (x, 0)
       else (F64.ofBits (Nat.lor (Nat.land (Nat.lor
          (if (if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11 ≥ 64 then JInt.wrap .u64 (Int.ofNat 0)
          else JInt.wrap .u64 (Int.ofNat ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat <<< ((if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11)))).val.toNat
          (Nat.land (F64.toBits x) 0x8000000000000000)) 0x800fffffffffffff) 0x3fe0000000000000),
          1 - Int.ofNat ((if ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat == 0) = true then 64 else 63 - ((JInt.wrap .u64 (Int.ofNat (F64.toBits (F64.abs x)))).val.toNat).log2) - 11) - 1022))
    else (F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff) 0x3fe0000000000000),
      Int.ofNat (F64.toBits (F64.abs x) >>> 52) - 1022) := rfl

theorem lz_val {f : Nat} (h0 : f ≠ 0) (hf : f < 2^52) :
    (if ((JInt.wrap .u64 (Int.ofNat f)).val.toNat == 0) = true then 64
      else 63 - ((JInt.wrap .u64 (Int.ofNat f)).val.toNat).log2) - 11 = 52 - f.log2 := by
  rw [wrapU f (by omega)]
  have c : ¬ ((f == 0) = true) := by simp only [beq_iff_eq]; omega
  rw [ite_f c]
  obtain ⟨h1, -, -⟩ := log2_facts h0 hf
  omega

theorem shl_val {f : Nat} (h0 : f ≠ 0) (hf : f < 2^52) :
    (if 52 - f.log2 ≥ 64 then JInt.wrap .u64 (Int.ofNat 0)
      else JInt.wrap .u64 (Int.ofNat ((JInt.wrap .u64 (Int.ofNat f)).val.toNat <<< (52 - f.log2)))).val.toNat
      = f * 2^(52 - f.log2) := by
  have c : ¬ (52 - f.log2 ≥ 64) := by omega
  rw [ite_f c, wrapU f (by omega), Nat.shiftLeft_eq]
  obtain ⟨-, h2, -⟩ := sub_mant h0 hf
  exact wrapU _ (by omega)

theorem sig_bits (x : F64) (hfin : F64.isfinite x = true) (hz : F64.iszero x = false) :
    F64.toBits (F64.significand x) = F64.toBits x / 2^63 * 2^63 + 1023 * 2^52 +
      (if F64.toBits x / 2^52 % 2048 = 0
        then F64.toBits x % 2^52 * 2^(52 - (F64.toBits x % 2^52).log2) - 2^52
        else F64.toBits x % 2^52) := by
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  have h3ff : (0x3ff0000000000000 : Nat) = 1023 * 2^52 := by decide
  rw [significand_eq, tb_abs]
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · have e1 : F64.toBits x % 2^63 = F64.toBits x % 2^52 := by omega
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    have hf' : F64.toBits x % 2^52 < 2^52 := by omega
    obtain ⟨m1, m2, -⟩ := sub_mant hne hf'
    have c1 : ¬ (F64.toBits x % 2^52 ≥ 0x7ff0000000000000) := by omega
    have c2 : F64.toBits x % 2^52 ≤ 0xfffffffffffff := by omega
    have c3 : ¬ ((F64.toBits x % 2^52 == 0) = true) := by simp only [beq_iff_eq]; omega
    rw [e1, lz_val hne hf', shl_val hne hf', ite_f c1, ite_t c2, ite_f c3,
      sign_or ht, h3ff, pack_bits, tb_ofBits, ite_t hE]
    all_goals omega
  · have c1 : ¬ (F64.toBits x % 2^63 ≥ 0x7ff0000000000000) := by omega
    have c2 : ¬ (F64.toBits x % 2^63 ≤ 0xfffffffffffff) := by omega
    rw [ite_f c1, ite_f c2, h3ff, pack_bits ht (by decide : 1023 < 2048), tb_ofBits, ite_f hE]
    omega

theorem frexp_val (x : F64) (hfin : F64.isfinite x = true) (hz : F64.iszero x = false) :
    F64.frexp x = (F64.ofBits (F64.toBits x / 2^63 * 2^63 + 1022 * 2^52 +
      (if F64.toBits x / 2^52 % 2048 = 0
        then F64.toBits x % 2^52 * 2^(52 - (F64.toBits x % 2^52).log2) - 2^52
        else F64.toBits x % 2^52)),
      if F64.toBits x / 2^52 % 2048 = 0 then ((F64.toBits x % 2^52).log2 : Int) - 1073
      else ((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1022) := by
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  have h3fe : (0x3fe0000000000000 : Nat) = 1022 * 2^52 := by decide
  rw [frexp_eq, tb_abs, Nat.shiftRight_eq_div_pow]
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · have e1 : F64.toBits x % 2^63 = F64.toBits x % 2^52 := by omega
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    have hf' : F64.toBits x % 2^52 < 2^52 := by omega
    obtain ⟨h1, -, -⟩ := log2_facts hne hf'
    obtain ⟨m1, m2, -⟩ := sub_mant hne hf'
    have c1 : ¬ (F64.toBits x % 2^52 ≥ 0x7ff0000000000000) := by omega
    have c2 : (Int.ofNat (F64.toBits x % 2^52 / 2^52) == 0) = true := by
      simp only [beq_iff_eq, Int.ofNat_eq_natCast]; omega
    have c3 : ¬ ((F64.toBits x % 2^52 == 0) = true) := by simp only [beq_iff_eq]; omega
    rw [e1, lz_val hne hf', shl_val hne hf', ite_f c1, ite_t c2, ite_f c3,
      sign_or ht, h3fe, pack_bits, ite_t hE, ite_t hE, Prod.mk.injEq]
    · refine ⟨congrArg F64.ofBits (by omega), ?_⟩
      simp only [Int.ofNat_eq_natCast, Nat.reducePow] at *
      omega
    all_goals omega
  · have c1 : ¬ (F64.toBits x % 2^63 ≥ 0x7ff0000000000000) := by omega
    have c2 : ¬ ((Int.ofNat (F64.toBits x % 2^63 / 2^52) == 0) = true) := by
      simp only [beq_iff_eq, Int.ofNat_eq_natCast]; omega
    rw [ite_f c1, ite_f c2, h3fe, pack_bits ht (by decide : 1022 < 2048), ite_f hE, ite_f hE,
      Prod.mk.injEq]
    refine ⟨congrArg F64.ofBits (by omega), ?_⟩
    simp only [Int.ofNat_eq_natCast, Nat.reducePow] at *
    omega

theorem ldexp_norm (x : F64) (e : Int) (h1 : 2^52 ≤ F64.toBits x % 2^63)
    (h2 : F64.toBits x % 2^63 < 0x7ff0000000000000) (he1 : -1100 ≤ e) (he2 : e ≤ 1100) :
    F64.ldexp x e =
      if (((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) ≥ 2047 then F64.inf (F64.signbit x)
      else if (((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) > 0 then
        F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff) ((((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e).toNat * 2^52))
      else if (((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) ≤ -53 then F64.zero (F64.signbit x)
      else F64.mul (F64.ofBits (970 * 2^52))
        (F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff) (((((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) + 53).toNat * 2^52))) := by
  have hk0 : (JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52))).val =
      ((F64.toBits x % 2^63 / 2^52 : Nat) : Int) := by
    rw [tb_abs, Nat.shiftRight_eq_div_pow, Int.ofNat_eq_natCast]
    exact wrapI _ (by omega) (by omega)
  have hk : (JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val = (((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) := by
    show (JInt.wrap .i64 ((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52))).val +
      (JInt.wrap .i64 e).val)).val = _
    rw [hk0, wrapI e (by omega) (by omega)]
    exact wrapI _ (by omega) (by omega)
  have hk53 : ((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e) + JInt.wrap .i64 53).val = (((F64.toBits x % 2^63 / 2^52 : Nat) : Int) + e) + 53 := by
    show (JInt.wrap .i64 ((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val + (JInt.wrap .i64 53).val)).val = _
    rw [hk, wrapI 53 (by omega) (by omega)]
    exact wrapI _ (by omega) (by omega)
  have hmax : IntTy.i64.max = 2^63 - 1 := by decide
  have hmin : IntTy.i64.min = -2^63 := by decide
  have c1 : ¬ (F64.toBits (F64.abs x) ≥ 0x7ff0000000000000) := by rw [tb_abs]; omega
  have c2 : ¬ (((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52))).val == 0) = true) := by
    rw [hk0]; simp only [beq_iff_eq]; omega
  have c3 : ¬ (e > IntTy.i64.max) := by rw [hmax]; omega
  have c4 : ¬ (e < IntTy.i64.min) := by rw [hmin]; omega
  have c5 : ¬ (e > 50000) := by omega
  show (if F64.toBits (F64.abs x) ≥ 0x7ff0000000000000 then x
    else if ((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52))).val == 0) = true then _
    else if e > IntTy.i64.max then F64.inf (F64.signbit x)
    else if e < IntTy.i64.min then F64.zero (F64.signbit x)
    else if (JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val ≥ 2047 then F64.inf (F64.signbit x)
    else if (JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val > 0 then
      F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff) ((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val.toNat <<< 52))
    else if (JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e).val ≤ -53 then
      (if e > 50000 then F64.inf (F64.signbit x) else F64.zero (F64.signbit x))
    else F64.mul (F64.ofBits (970 <<< 52)) (F64.ofBits (Nat.lor (Nat.land (F64.toBits x) 0x800fffffffffffff)
      (((JInt.wrap .i64 (Int.ofNat (F64.toBits (F64.abs x) >>> 52)) + JInt.wrap .i64 e) + JInt.wrap .i64 53).val.toNat <<< 52)))) = _
  rw [ite_f c1, ite_f c2, ite_f c3, ite_f c4, hk53, hk, ite_f c5, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]

def fl2 (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2^e.toNat else n * 2^(-e).toNat < d
  if below then e - 1 else e

def rq (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

def pk (negative : Bool) (q : Nat) (k : Int) : F64 :=
  if q == 0 then F64.zero negative
  else
    let carry := q ≥ 2^53
    let m := if carry then q / 2 else q
    let p := if carry then k + 1 else k
    let exponent := p + 1075
    if exponent ≥ 2047 then F64.inf negative
    else
      let magnitude :=
        if m < 2^52 then m
        else exponent.toNat * 2^52 + (m - 2^52)
      F64.ofBits ((if negative then 2^63 else 0) + magnitude)

theorem roundRat_eq (n : Int) (d : Nat) (zs : Bool) : F64.roundRat n d zs =
    if d == 0 then (if n == 0 then F64.nan else F64.inf (decide (n < 0)))
    else if n == 0 then F64.zero zs
    else
      if fl2 n.natAbs d ≥ 1024 then F64.inf (decide (n < 0))
      else if fl2 n.natAbs d < -1075 then F64.zero (decide (n < 0))
      else
        pk (decide (n < 0))
          (rq (if (max (fl2 n.natAbs d - 52) (-1074)) ≥ 0 then (n.natAbs, d * 2^(max (fl2 n.natAbs d - 52) (-1074)).toNat)
               else (n.natAbs * 2^(-(max (fl2 n.natAbs d - 52) (-1074))).toNat, d)).1
              (if (max (fl2 n.natAbs d - 52) (-1074)) ≥ 0 then (n.natAbs, d * 2^(max (fl2 n.natAbs d - 52) (-1074)).toNat)
               else (n.natAbs * 2^(-(max (fl2 n.natAbs d - 52) (-1074))).toNat, d)).2)
          (max (fl2 n.natAbs d - 52) (-1074)) := rfl

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

theorem fl2_pow (M j i : Nat) (hM : 0 < M) :
    fl2 (M * 2^j) (2^i) = ((M.log2 + j : Nat) : Int) - (i : Int) := by
  have h1 : 2^M.log2 ≤ M := Nat.log2_self_le (by omega)
  unfold fl2
  rw [log2_mul_pow j hM, Nat.log2_two_pow]
  by_cases hc : ((M.log2 + j : Nat) : Int) - (i : Int) ≥ 0
  · have ht : (((M.log2 + j : Nat) : Int) - (i : Int)).toNat = M.log2 + j - i := toNat_eq (by omega)
    have hP : ¬ (M * 2^j < 2^i * 2^(((M.log2 + j : Nat) : Int) - (i : Int)).toNat) := by
      rw [ht, ← Nat.pow_add, show i + (M.log2 + j - i) = M.log2 + j by omega, Nat.pow_add]
      have := Nat.mul_le_mul_right (2^j) h1
      omega
    simp only [hc, hP, ↓reduceIte]
  · have ht : (-(((M.log2 + j : Nat) : Int) - (i : Int))).toNat = i - (M.log2 + j) :=
      toNat_eq (by omega)
    have hP : ¬ (M * 2^j * 2^(-(((M.log2 + j : Nat) : Int) - (i : Int))).toNat < 2^i) := by
      rw [ht]
      have e : 2^i = 2^M.log2 * 2^j * 2^(i - (M.log2 + j)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      have := Nat.mul_le_mul_right (2^(i - (M.log2 + j))) (Nat.mul_le_mul_right (2^j) h1)
      omega
    simp only [hc, hP, ↓reduceIte]

theorem rq_exact (a b : Nat) (hb : 0 < b) (h : a % b = 0) : rq a b = a / b := by
  unfold rq
  rw [h]
  have c : ¬ ((decide (2 * 0 > b) || (2 * 0 == b && a / b % 2 == 1)) = true) := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  exact ite_f c

theorem pk_sub (neg : Bool) (q : Nat) (h0 : 0 < q) (h : q < 2^52) :
    pk neg q (-1074) = F64.ofBits ((if neg then 2^63 else 0) + q) := by
  unfold pk
  have c1 : ¬ ((q == 0) = true) := by simp only [beq_iff_eq]; omega
  have c2 : ¬ (q ≥ 2^53) := by omega
  have c3 : ¬ ((-1074 : Int) + 1075 ≥ 2047) := by decide
  rw [ite_f c1]
  simp only [ite_f c2, ite_f c3, ite_t h]

theorem roundRat_sub (M j i : Nat) (neg zs : Bool) (hM0 : 0 < M) (hM : M < 2^52)
    (hji : j + 1074 = i) :
    F64.roundRat (if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) (2^i) zs =
      F64.ofBits ((if neg then 2^63 else 0) + M) := by
  have hp : 0 < M * 2^j := Nat.mul_pos hM0 (Nat.two_pow_pos j)
  have habs : (if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)).natAbs = M * 2^j := by
    cases neg
    · rfl
    · show (-((M * 2^j : Nat) : Int)).natAbs = M * 2^j
      rw [Int.natAbs_neg]
      rfl
  have hneg : decide ((if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) < 0) = neg := by
    cases neg
    · show decide (((M * 2^j : Nat) : Int) < 0) = false
      simp only [decide_eq_false_iff_not]
      omega
    · show decide (-((M * 2^j : Nat) : Int) < 0) = true
      simp only [decide_eq_true_eq]
      omega
  have hn0 : ¬ (((if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) == 0) = true) := by
    cases neg
    · show ¬ ((((M * 2^j : Nat) : Int) == 0) = true)
      simp only [beq_iff_eq]
      omega
    · show ¬ ((-((M * 2^j : Nat) : Int) == 0) = true)
      simp only [beq_iff_eq]
      omega
  have hd0 : ¬ ((2^i == 0) = true) := by
    simp only [beq_iff_eq]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos i)
  obtain ⟨hL, -, -⟩ := log2_facts (by omega) hM
  rw [roundRat_eq, ite_f hd0, ite_f hn0, habs, hneg, fl2_pow M j i hM0]
  have c1 : ¬ (((M.log2 + j : Nat) : Int) - (i : Int) ≥ 1024) := by omega
  have c2 : ¬ (((M.log2 + j : Nat) : Int) - (i : Int) < -1075) := by omega
  have c3 : max (((M.log2 + j : Nat) : Int) - (i : Int) - 52) (-1074) = -1074 := by omega
  have c4 : ¬ ((-1074 : Int) ≥ 0) := by decide
  have c5 : (-(-1074 : Int)).toNat = 1074 := by decide
  have e1 : M * 2^j * 2^1074 = M * 2^i := by rw [Nat.mul_assoc, ← Nat.pow_add, hji]
  rw [ite_f c1, ite_f c2, c3, ite_f c4, c5, e1,
    rq_exact _ _ (Nat.two_pow_pos i) (Nat.mul_mod_left M (2^i)),
    Nat.mul_div_cancel _ (Nat.two_pow_pos i)]
  exact pk_sub neg M hM0 hM

set_option simprocs false in
theorem toRat_norm (x : F64) (h1 : 1 ≤ F64.toBits x / 2^52 % 2048)
    (h2 : F64.toBits x / 2^52 % 2048 ≤ 1074) :
    F64.toRat x = (if F64.signbit x then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
      else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int), 2^(1075 - F64.toBits x / 2^52 % 2048)) := by
  have hfin : (!F64.isfinite x) = false := by
    simp only [F64.isfinite, F64.exponentField, bne_iff_ne, ne_eq, Bool.not_eq_false']; omega
  have hE0 : ¬ ((F64.exponentField x == 0) = true) := by
    simp only [F64.exponentField, beq_iff_eq]; omega
  have hp : ¬ (((F64.exponentField x : Nat) : Int) - 1075 ≥ 0) := by
    simp only [F64.exponentField]; omega
  have hq : (-(((F64.exponentField x : Nat) : Int) - 1075)).toNat =
      1075 - F64.toBits x / 2^52 % 2048 := toNat_eq (by simp only [F64.exponentField]; omega)
  unfold F64.toRat
  rw [hfin]
  simp only []
  rw [ite_f hE0, ite_f hE0, ite_f hp, hq]
  rfl

theorem mul_fin (x y : F64) (h1 : F64.isnan x = false) (h2 : F64.isnan y = false)
    (h3 : F64.isinf x = false) (h4 : F64.isinf y = false) :
    F64.mul x y = F64.roundRat ((F64.toRat x).1 * (F64.toRat y).1) ((F64.toRat x).2 * (F64.toRat y).2)
      (F64.signbit x != F64.signbit y) := by
  show (if F64.isnan x then _ else if F64.isnan y then _
    else if (F64.isinf x && F64.iszero y) || (F64.iszero x && F64.isinf y) then _
    else if F64.isinf x || F64.isinf y then F64.inf (F64.signbit x != F64.signbit y)
    else F64.roundRat ((F64.toRat x).1 * (F64.toRat y).1) ((F64.toRat x).2 * (F64.toRat y).2)
      (F64.signbit x != F64.signbit y)) = _
  rw [h1, h2, h3, h4]
  simp only [Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

theorem mul_sub (s f L F' : Nat) (y : F64) (hs : s < 2) (hL : L ≤ 51) (hf0 : 0 < f)
    (hf : f < 2^52) (hF1 : 2^52 ≤ F') (hF2 : F' < 2^53) (hrel : 2^52 * F' = f * 2^(104 - L))
    (hY : F64.toBits y = s * 2^63 + (L + 2) * 2^52 + (F' - 2^52)) :
    F64.mul (F64.ofBits (970 * 2^52)) y = F64.ofBits (s * 2^63 + f) := by
  have hny : F64.isnan y = false := by rw [isnan_f, hY]; omega
  have hiy : F64.isinf y = false := by rw [Bool.eq_false_iff, ne_eq, isinf_iff, hY]; omega
  have hz1 : F64.isnan (F64.ofBits (970 * 2^52)) = false := by decide
  have hz2 : F64.isinf (F64.ofBits (970 * 2^52)) = false := by decide
  have hz4 : F64.signbit (F64.ofBits (970 * 2^52)) = false := by decide
  have hz5 : F64.toRat (F64.ofBits (970 * 2^52)) =
      ((4503599627370496 : Int), (40564819207303340847894502572032 : Nat)) := by decide
  have hry : F64.toRat y = (if F64.signbit y then -((F' : Nat) : Int) else ((F' : Nat) : Int),
      2^(1073 - L)) := by
    rw [toRat_norm y (by rw [hY]; omega) (by rw [hY]; omega), hY]
    have a1 : (s * 2^63 + (L + 2) * 2^52 + (F' - 2^52)) % 2^52 + 2^52 = F' := by omega
    have a2 : 1075 - (s * 2^63 + (L + 2) * 2^52 + (F' - 2^52)) / 2^52 % 2048 = 1073 - L := by omega
    rw [a1, a2]
  have hsy : F64.signbit y = decide (s = 1) := by
    simp only [F64.signbit, hY, decide_eq_decide]; omega
  have hn : (4503599627370496 : Int) *
      (if decide (s = 1) = true then -((F' : Nat) : Int) else ((F' : Nat) : Int)) =
      if decide (s = 1) = true then -((f * 2^(104 - L) : Nat) : Int)
      else ((f * 2^(104 - L) : Nat) : Int) := by
    have h : ((f * 2^(104 - L) : Nat) : Int) = (4503599627370496 : Int) * ((F' : Nat) : Int) := by
      rw [← hrel]; omega
    rw [h]
    split <;> omega
  have hd : (40564819207303340847894502572032 : Nat) * 2^(1073 - L) = 2^(1178 - L) := by
    rw [show (40564819207303340847894502572032 : Nat) = 2^105 by decide, ← Nat.pow_add]
    congr 1
    omega
  have hneg : (false != decide (s = 1)) = decide (s = 1) := by cases decide (s = 1) <;> rfl
  rw [mul_fin _ _ hz1 hny hz2 hiy, hz5, hry, hz4, hsy, hn, hd, hneg, roundRat_sub f (104 - L) (1178 - L) (decide (s = 1)) _ hf0 hf (by omega)]
  apply congrArg F64.ofBits
  by_cases h : s = 1 <;> simp [h] <;> omega

theorem pk_norm (neg : Bool) (q : Nat) (k : Int) (h1 : 2^52 ≤ q) (h2 : q < 2^53) (hk1 : -1074 ≤ k)
    (hk2 : k ≤ 971) :
    pk neg q k = F64.ofBits ((if neg then 2^63 else 0) + ((k + 1075).toNat * 2^52 + (q - 2^52))) := by
  unfold pk
  have c1 : ¬ ((q == 0) = true) := by simp only [beq_iff_eq]; omega
  have c2 : ¬ (q ≥ 2^53) := by omega
  have c3 : ¬ (k + 1075 ≥ 2047) := by omega
  have c4 : ¬ (q < 2^52) := by omega
  rw [ite_f c1]
  simp only [ite_f c2, ite_f c3, ite_f c4]

theorem roundRat_norm (M j i : Nat) (neg zs : Bool) (hM1 : 2^52 ≤ M) (hM2 : M < 2^53)
    (h1 : i ≤ j + 1074) (h2 : j + 1074 ≤ i + 2045) :
    F64.roundRat (if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) (2^i) zs =
      F64.ofBits ((if neg then 2^63 else 0) + ((j + 1075 - i) * 2^52 + (M - 2^52))) := by
  have hM0 : 0 < M := by omega
  have hp : 0 < M * 2^j := Nat.mul_pos hM0 (Nat.two_pow_pos j)
  have habs : (if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)).natAbs = M * 2^j := by
    cases neg
    · rfl
    · show (-((M * 2^j : Nat) : Int)).natAbs = M * 2^j
      rw [Int.natAbs_neg]
      rfl
  have hneg : decide ((if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) < 0) = neg := by
    cases neg
    · show decide (((M * 2^j : Nat) : Int) < 0) = false
      simp only [decide_eq_false_iff_not]
      omega
    · show decide (-((M * 2^j : Nat) : Int) < 0) = true
      simp only [decide_eq_true_eq]
      omega
  have hn0 : ¬ (((if neg then -((M * 2^j : Nat) : Int) else ((M * 2^j : Nat) : Int)) == 0) = true) := by
    cases neg
    · show ¬ ((((M * 2^j : Nat) : Int) == 0) = true)
      simp only [beq_iff_eq]
      omega
    · show ¬ ((-((M * 2^j : Nat) : Int) == 0) = true)
      simp only [beq_iff_eq]
      omega
  have hd0 : ¬ ((2^i == 0) = true) := by
    simp only [beq_iff_eq]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos i)
  have hne : M ≠ 0 := by omega
  have hL : M.log2 = 52 := by
    have a := (Nat.log2_lt hne).mpr hM2
    have b : ¬ M.log2 < 52 := fun h => absurd hM1 (Nat.not_le.mpr ((Nat.log2_lt hne).mp h))
    omega
  rw [roundRat_eq, ite_f hd0, ite_f hn0, habs, hneg, fl2_pow M j i hM0, hL]
  have c1 : ¬ (((52 + j : Nat) : Int) - (i : Int) ≥ 1024) := by omega
  have c2 : ¬ (((52 + j : Nat) : Int) - (i : Int) < -1075) := by omega
  have c3 : max (((52 + j : Nat) : Int) - (i : Int) - 52) (-1074) = (j : Int) - (i : Int) := by omega
  rw [ite_f c1, ite_f c2, c3]
  by_cases hD : (j : Int) - (i : Int) ≥ 0
  · have hDt : ((j : Int) - (i : Int)).toNat = j - i := toNat_eq (by omega)
    have e1 : 2^i * 2^(j - i) = 2^j := by rw [← Nat.pow_add]; congr 1; omega
    rw [ite_t hD, hDt, e1, rq_exact _ _ (Nat.two_pow_pos j) (Nat.mul_mod_left M (2^j)),
      Nat.mul_div_cancel _ (Nat.two_pow_pos j),
      pk_norm neg M ((j : Int) - (i : Int)) hM1 hM2 (by omega) (by omega)]
    have e2 : ((j : Int) - (i : Int) + 1075).toNat = j + 1075 - i := toNat_eq (by omega)
    rw [e2]
  · have hDt : (-((j : Int) - (i : Int))).toNat = i - j := toNat_eq (by omega)
    have e1 : M * 2^j * 2^(i - j) = M * 2^i := by
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [ite_f hD, hDt, e1, rq_exact _ _ (Nat.two_pow_pos i) (Nat.mul_mod_left M (2^i)),
      Nat.mul_div_cancel _ (Nat.two_pow_pos i),
      pk_norm neg M ((j : Int) - (i : Int)) hM1 hM2 (by omega) (by omega)]
    have e2 : ((j : Int) - (i : Int) + 1075).toNat = j + 1075 - i := toNat_eq (by omega)
    rw [e2]

set_option simprocs false in
theorem toRat_subn (x : F64) (hE : F64.toBits x / 2^52 % 2048 = 0) :
    F64.toRat x = (if F64.signbit x then -((F64.toBits x % 2^52 : Nat) : Int)
      else ((F64.toBits x % 2^52 : Nat) : Int), 2^1074) := by
  have hfin : (!F64.isfinite x) = false := by
    simp only [F64.isfinite, F64.exponentField, bne_iff_ne, ne_eq, Bool.not_eq_false']; omega
  have hE0 : (F64.exponentField x == 0) = true := by
    simp only [F64.exponentField, beq_iff_eq]; omega
  have hp : ¬ ((-1074 : Int) ≥ 0) := by decide
  have hq : (-(-1074 : Int)).toNat = 1074 := by decide
  unfold F64.toRat
  rw [hfin]
  simp only []
  rw [ite_t hE0, ite_t hE0, ite_f hp, hq, Nat.add_zero]
  rfl

set_option simprocs false in
theorem toRat_big (x : F64) (h1 : 1075 ≤ F64.toBits x / 2^52 % 2048)
    (h2 : F64.toBits x / 2^52 % 2048 ≤ 2046) :
    F64.toRat x = ((if F64.signbit x then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
      else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int)) *
        ((2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int), 1) := by
  have hfin : (!F64.isfinite x) = false := by
    simp only [F64.isfinite, F64.exponentField, bne_iff_ne, ne_eq, Bool.not_eq_false']; omega
  have hE0 : ¬ ((F64.exponentField x == 0) = true) := by
    simp only [F64.exponentField, beq_iff_eq]; omega
  have hp : ((F64.exponentField x : Nat) : Int) - 1075 ≥ 0 := by
    simp only [F64.exponentField]; omega
  have hq : (((F64.exponentField x : Nat) : Int) - 1075).toNat =
      F64.toBits x / 2^52 % 2048 - 1075 := toNat_eq (by simp only [F64.exponentField]; omega)
  unfold F64.toRat
  rw [hfin]
  simp only []
  rw [ite_f hE0, ite_f hE0, ite_t hp, hq]
  rfl

theorem toRat_den_pos (x : F64) (h : F64.isfinite x = true) : 0 < (F64.toRat x).2 := by
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using h
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · rw [toRat_subn x hE]
    exact Nat.two_pow_pos _
  · by_cases hE2 : F64.toBits x / 2^52 % 2048 ≤ 1074
    · rw [toRat_norm x (by omega) hE2]
      exact Nat.two_pow_pos _
    · rw [toRat_big x (by omega) (by omega)]
      exact Nat.one_pos

theorem zero_of_iszero (x : F64) (h : F64.iszero x = true) : ∃ s, x = F64.zero s := by
  have ht := tb_lt x
  have h' := (iszero_iff x).mp h
  refine ⟨F64.signbit x, f64_ext ?_⟩
  unfold F64.zero
  rw [tb_ofBits]
  cases hs : F64.signbit x
  · rw [signbit_f] at hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · rw [signbit_iff] at hs
    simp only [↓reduceIte]
    omega

theorem inf_of_isinf (x : F64) (h : F64.isinf x = true) : ∃ s, x = F64.inf s := by
  have ht := tb_lt x
  have h' := (isinf_iff x).mp h
  refine ⟨F64.signbit x, f64_ext ?_⟩
  unfold F64.inf
  rw [tb_ofBits]
  cases hs : F64.signbit x
  · rw [signbit_f] at hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · rw [signbit_iff] at hs
    simp only [↓reduceIte]
    omega

theorem sign_bits (x : F64) (b : Nat) (hb : b < 2^63) (h : F64.toBits x % 2^63 = b) :
    ((if F64.signbit x then 2^63 else 0) + b) % 2^64 = F64.toBits x := by
  have ht := tb_lt x
  cases hs : F64.signbit x
  · rw [signbit_f] at hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · rw [signbit_iff] at hs
    simp only [↓reduceIte]
    omega

theorem mul_one_eq (x : F64) (hn : F64.isnan x = false) : F64.mul x F64.one = x := by
  have ht := tb_lt x
  have hn' := (isnan_f x).mp hn
  have o1 : F64.isnan F64.one = false := by decide
  have o2 : F64.isinf F64.one = false := by decide
  have o4 : F64.signbit F64.one = false := by decide
  have o5 : F64.toRat F64.one = ((4503599627370496 : Int), (4503599627370496 : Nat)) := by decide
  cases hi : F64.isinf x
  · cases hz : F64.iszero x
    · have hi' : ¬ (F64.toBits x % 2^63 = 2047 * 2^52) := by
        rw [← isinf_iff, hi]; decide
      have hz' := (iszero_f x).mp hz
      have hb2 : (F64.signbit x != false) = F64.signbit x := by cases F64.signbit x <;> rfl
      rw [mul_fin x F64.one hn o1 hi o2, o5, o4]
      by_cases hE : F64.toBits x / 2^52 % 2048 = 0
      · have hn2 : (if F64.signbit x = true then -((F64.toBits x % 2^52 : Nat) : Int)
            else ((F64.toBits x % 2^52 : Nat) : Int)) * 4503599627370496 =
            if F64.signbit x = true then -((F64.toBits x % 2^52 * 2^52 : Nat) : Int)
            else ((F64.toBits x % 2^52 * 2^52 : Nat) : Int) := by split <;> omega
        have hd2 : (2^1074 * 4503599627370496 : Nat) = 2^1126 := by decide
        rw [toRat_subn x hE, hn2, hd2, hb2,
          roundRat_sub (F64.toBits x % 2^52) 52 1126 _ _ (by omega) (by omega) (by omega)]
        apply f64_ext
        rw [tb_ofBits]
        exact sign_bits x _ (by omega) (by omega)
      · by_cases hE2 : F64.toBits x / 2^52 % 2048 ≤ 1074
        · have hn2 : (if F64.signbit x = true then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
              else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int)) * 4503599627370496 =
              if F64.signbit x = true then -(((F64.toBits x % 2^52 + 2^52) * 2^52 : Nat) : Int)
              else (((F64.toBits x % 2^52 + 2^52) * 2^52 : Nat) : Int) := by split <;> omega
          have hd2 : 2^(1075 - F64.toBits x / 2^52 % 2048) * 4503599627370496 =
              2^(1127 - F64.toBits x / 2^52 % 2048) := by
            rw [show (4503599627370496 : Nat) = 2^52 by decide, ← Nat.pow_add]; congr 1; omega
          rw [toRat_norm x (by omega) hE2, hn2, hd2, hb2,
            roundRat_norm (F64.toBits x % 2^52 + 2^52) 52 (1127 - F64.toBits x / 2^52 % 2048) _ _ (by omega) (by omega) (by omega)
              (by omega)]
          apply f64_ext
          rw [tb_ofBits]
          exact sign_bits x _ (by omega) (by omega)
        · have hk : 2^(F64.toBits x / 2^52 % 2048 - 1023) =
              2^(F64.toBits x / 2^52 % 2048 - 1075) * 2^52 := by
            rw [← Nat.pow_add]; congr 1; omega
          have hn2 : (if F64.signbit x = true then -((F64.toBits x % 2^52 + 2^52 : Nat) : Int)
              else ((F64.toBits x % 2^52 + 2^52 : Nat) : Int)) *
              ((2^(F64.toBits x / 2^52 % 2048 - 1075) : Nat) : Int) * 4503599627370496 =
              if F64.signbit x = true then
                -(((F64.toBits x % 2^52 + 2^52) * 2^(F64.toBits x / 2^52 % 2048 - 1023) : Nat) : Int)
              else (((F64.toBits x % 2^52 + 2^52) * 2^(F64.toBits x / 2^52 % 2048 - 1023) : Nat) : Int) := by
            rw [hk]
            split <;> simp [Int.natCast_mul, Int.mul_assoc, Int.neg_mul]
          have hd2 : (1 * 4503599627370496 : Nat) = 2^52 := by decide
          rw [toRat_big x (by omega) (by omega), hn2, hd2, hb2,
            roundRat_norm (F64.toBits x % 2^52 + 2^52) (F64.toBits x / 2^52 % 2048 - 1023) 52 _ _ (by omega) (by omega) (by omega)
              (by omega)]
          apply f64_ext
          rw [tb_ofBits]
          exact sign_bits x _ (by omega) (by omega)
    · obtain ⟨s, rfl⟩ := zero_of_iszero x hz
      cases s <;> decide
  · obtain ⟨s, rfl⟩ := inf_of_isinf x hi
    cases s <;> decide

theorem mul_zero_fin (x : F64) (hn : F64.isnan x = false) (hf : F64.isfinite x = true) :
    F64.mul x F64.zero = F64.zero (F64.signbit x != false) := by
  have hi : F64.isinf x = false := by
    rw [Bool.eq_false_iff, ne_eq, isinf_iff]
    have := tb_lt x
    have hf' : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
      simpa [F64.isfinite, F64.exponentField] using hf
    omega
  have hd := toRat_den_pos x hf
  have c1 : ¬ (((F64.toRat x).2 * 2^1074 == 0) = true) := by
    simp only [beq_iff_eq]
    exact Nat.pos_iff_ne_zero.mp (Nat.mul_pos hd (Nat.two_pow_pos 1074))
  rw [mul_fin x F64.zero hn (by decide) hi (by decide), toRat_zero,
    (by decide : F64.signbit (F64.zero false) = false), Int.mul_zero, roundRat_eq, ite_f c1, ite_t (by decide : ((0 : Int) == 0) = true)]

theorem powBodyLoop_one (x a y b : F64) : powBodyLoop 64 x a y b 1 = (x, a, y, b) := rfl

theorem powBodyI_one (x : F64) : powBodyI x 1 =
    if F64.isfinite x && F64.isfinite (F64.muladd F64.one (F64.zero true) (F64.mul x F64.zero)) &&
        !F64.iszero (F64.muladd F64.one (F64.zero true) (F64.mul x F64.zero))
    then F64.add (F64.mul x F64.one) (F64.muladd F64.one (F64.zero true) (F64.mul x F64.zero))
    else F64.mul x F64.one := by
  unfold powBodyI
  rw [ite_f (by decide : ¬ (((1 : Int) == 3) = true)), ite_f (by decide : ¬ ((1 : Int) < 0))]
  unfold powBodyIFinish
  rw [powBodyLoop_one]

theorem fma_zero_iszero (s : Bool) :
    F64.iszero (F64.muladd F64.one (F64.zero true) (F64.zero s)) = true := by
  cases s <;> decide

theorem powFI_one (x : F64) : powFI x 1 = powBodyI x 1 := by
  have h : (if (1 : Int) > 2^63 - 1 then 2^63 - 1 else if (1 : Int) < -2^63 then -2^63 else 1) = 1 := by
    decide
  unfold powFI
  rw [h]
  show (if ((1 : Int) == 0) = true then F64.one
    else if usePowerBySquaring 1 = true then powBodyI x 1 else _) = _
  rw [ite_f (by decide : ¬ (((1 : Int) == 0) = true)), ite_t (by decide : usePowerBySquaring 1 = true)]

theorem lt_abs_one : (!F64.lt (F64.abs F64.one) (lit 0x43d8000000000000)) = false := by decide

theorem one_bits : F64.toBits F64.one = 0x3ff0000000000000 := by decide

theorem toRat_one : F64.toRat F64.one = ((4503599627370496 : Int), (4503599627370496 : Nat)) := by
  decide

theorem powFFClamped_one (x : F64) : powFFClamped x F64.one = .ok (powBodyI x 1) := by
  unfold powFFClamped
  rw [toRat_one]
  rfl

end ProofsBits

open ProofsBits

theorem evalpolyOne_proven : evalpolyOne := by
  intro x c
  rfl

theorem copysignFloatSpec_proven : copysignFloatSpec := by
  intro x y
  have hx := tb_lt x
  constructor
  · unfold copysign
    cases sy : F64.signbit y <;> simp [F64.signbit, tb_ofBits] <;> omega
  · apply f64_ext
    rw [tb_abs, tb_abs]
    unfold copysign
    rw [tb_ofBits]
    split <;> omega

theorem flipsignFloatSpec_proven : flipsignFloatSpec := by
  intro x y
  unfold flipsign
  cases sy : F64.signbit y
  · simp
  · simp [abs_neg, signbit_neg]

theorem hypotInf_proven : hypotInf := by
  constructor
  · intro x y h
    unfold hypot
    cases hx : F64.isinf x
    · have hy : F64.isinf y = true := by simpa [hx] using h
      simp only [abs_of_isinf hy, div_inf_one, isinf_inf, Bool.or_true, ↓reduceIte]
    · simp only [abs_of_isinf hx, div_inf_one, isinf_inf, Bool.true_or, ↓reduceIte]
  · intro xs h
    have hany : (xs.map F64.abs).any (fun z => F64.eq z F64.inf) = true := by
      rw [List.any_eq_true] at h ⊢
      obtain ⟨x, hx, hi⟩ := h
      refine ⟨F64.abs x, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      show F64.eq (F64.abs x) F64.inf = true
      rw [abs_of_isinf hi]
      decide
    unfold hypotN
    simp only [hany, ↓reduceIte]

theorem hypotSignInvariant_proven : hypotSignInvariant := by
  intro x y
  constructor <;> simp only [hypot, abs_neg]

theorem minMaxNaN_proven : minMaxNaN := by
  intro x y h
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> simp_all [fmin, fmax, fminmax]

theorem minMaxIsless_proven : minMaxIsless := by
  intro x y hx hy
  have hx' := (isnan_f x).mp hx
  have hy' := (isnan_f y).mp hy
  have bx := tb_lt x
  have by' := tb_lt y
  have hl := isless_iff hy hx
  constructor
  · simp only [fmin, hx, hy, Bool.false_eq_true, ↓reduceIte]
    split <;> rename_i h1 <;> split <;> rename_i h2 <;>
      first
      | rfl
      | (apply f64_ext
         simp only [Bool.or_eq_true, Bool.and_eq_true, lt_iff, iszero_iff, signbit_iff, hl]
           at h1 h2
         omega)
  · simp only [fmax, hx, hy, Bool.false_eq_true, ↓reduceIte]
    split <;> rename_i h1 <;> split <;> rename_i h2 <;>
      first
      | rfl
      | (apply f64_ext
         simp only [Bool.or_eq_true, Bool.and_eq_true, lt_iff, iszero_iff, signbit_iff, hl]
           at h1 h2
         omega)

theorem clampSpec_proven : clampSpec := by
  intro x lo hi hx hl hh
  have hx' := (isnan_f x).mp hx
  have hl' := (isnan_f lo).mp hl
  have hh' := (isnan_f hi).mp hh
  have bx := tb_lt x
  have bl := tb_lt lo
  have bh := tb_lt hi
  refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · unfold clamp
    split
    next h3 =>
      exfalso
      simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff] at h1 h2 h3
      omega
    next =>
      split
      next h4 =>
        exfalso
        simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff] at h1 h2 h4
        omega
      next => rfl
  · unfold clamp
    simp only [h, ↓reduceIte]
  · unfold clamp
    split
    next h3 =>
      exfalso
      simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff] at h1 h2 h3
      omega
    next => rfl

theorem logNegDomain_proven : logNegDomain := by
  intro x b h
  refine ⟨b.funcName, ?_⟩
  unfold logImpl
  simp only [lt_asymm h, lt_eq h, lt_nan_l h, Bool.false_eq_true, ↓reduceIte]

theorem log1pDomain_proven : log1pDomain := by
  intro x h
  have hc : F64.neg F64.one = lit 0xbff0000000000000 := by decide
  rw [hc] at h
  refine ⟨"log1p", ?_⟩
  unfold log1p
  simp only [lt_asymm h, lt_eq h, lt_nan_l h, Bool.false_eq_true, ↓reduceIte]

theorem powOneBase_proven : powOneBase := by
  intro y
  unfold powFF
  simp only [(by decide : (bitsOf F64.one == 0x3ff0000000000000) = true), ↓reduceIte]

theorem powZeroExponent_proven : powZeroExponent := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · unfold powFF
    split
    · rfl
    · simp only [(by decide :
        (!F64.lt (F64.abs (F64.zero false)) (lit 0x43d8000000000000)) = false), ↓reduceIte,
        Bool.false_eq_true]
      exact powFFClamped_zero x false
  · unfold powFF
    split
    · rfl
    · simp only [(by decide :
        (!F64.lt (F64.abs (F64.zero true)) (lit 0x43d8000000000000)) = false), ↓reduceIte,
        Bool.false_eq_true]
      exact powFFClamped_zero x true
  · rfl


theorem exponentFloatDefinition_proven : exponentFloatDefinition := by
  intro x hfin hz
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  refine ⟨_, exponent_ok x hfin hz, ?_⟩
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · rw [ite_t hE]
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    obtain ⟨h1, h2, h3⟩ := log2_facts hne (by omega)
    have b1 : F64.toBits (F64.ldexp F64.one ((((F64.toBits x % 2^52).log2 : Nat) : Int) - 1074)) =
        if (F64.toBits x % 2^52).log2 < 52 then 2^(F64.toBits x % 2^52).log2 else ((F64.toBits x % 2^52).log2 - 51) * 2^52 := ldexp_one_bits ⟨(F64.toBits x % 2^52).log2, by omega⟩
    rw [ite_t h1] at b1
    have e2 : ((((F64.toBits x % 2^52).log2 + 1 : Nat)) : Int) - 1074 = (((F64.toBits x % 2^52).log2 : Nat) : Int) - 1074 + 1 := by omega
    have b2 : F64.toBits (F64.ldexp F64.one ((((F64.toBits x % 2^52).log2 : Nat) : Int) - 1074 + 1)) =
        if (F64.toBits x % 2^52).log2 + 1 < 52 then 2^((F64.toBits x % 2^52).log2 + 1) else ((F64.toBits x % 2^52).log2 + 1 - 51) * 2^52 := by
      rw [← e2]
      exact ldexp_one_bits ⟨(F64.toBits x % 2^52).log2 + 1, by omega⟩
    have b2' : F64.toBits (F64.ldexp F64.one ((((F64.toBits x % 2^52).log2 : Nat) : Int) - 1074 + 1)) = 2^((F64.toBits x % 2^52).log2 + 1) ∨
        ((F64.toBits x % 2^52).log2 = 51 ∧ F64.toBits (F64.ldexp F64.one ((((F64.toBits x % 2^52).log2 : Nat) : Int) - 1074 + 1)) = 2^52) := by
      rw [b2]; split <;> omega
    generalize hLv : (F64.toBits x % 2^52).log2 = L at h1 h2 h3 b1 b2' ⊢
    constructor
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, b1]
      omega
    · rcases b2' with b2' | ⟨-, b2'⟩ <;> simp only [lt_iff, tb_abs, b2'] <;> omega
  · simp only [hE, ↓reduceIte]
    have b1 := ldexp_one_bits ⟨F64.toBits x / 2^52 % 2048 + 51, by omega⟩
    have b2 := ldexp_one_bits ⟨F64.toBits x / 2^52 % 2048 + 52, by omega⟩
    have c1 : ¬ (F64.toBits x / 2^52 % 2048 + 51 < 52) := by omega
    have c2 : ¬ (F64.toBits x / 2^52 % 2048 + 52 < 52) := by omega
    simp only [c1, c2, ↓reduceIte] at b1 b2
    have e1 : ((F64.toBits x / 2^52 % 2048 + 51 : Nat) : Int) - 1074 =
        ((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1023 := by omega
    have e2 : ((F64.toBits x / 2^52 % 2048 + 52 : Nat) : Int) - 1074 =
        ((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1023 + 1 := by omega
    rw [e1] at b1
    rw [e2] at b2
    constructor
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, b1]
      omega
    · simp only [lt_iff, tb_abs, b2]
      omega

theorem significandRange_proven : significandRange := by
  intro x hfin hz
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  have hb := sig_bits x hfin hz
  have h1 : F64.toBits F64.one = 0x3ff0000000000000 := by decide
  have h2 : F64.toBits (F64.ofInt 2) = 0x4000000000000000 := by decide
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · rw [ite_t hE] at hb
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    have hf' : F64.toBits x % 2^52 < 2^52 := by omega
    obtain ⟨hL, -, -⟩ := log2_facts hne hf'
    obtain ⟨m1, m2, m3⟩ := sub_mant hne hf'
    generalize hFv : F64.toBits x % 2^52 * 2^(52 - (Nat.log2 (F64.toBits x % 2^52))) = F' at hb m1 m2 m3
    refine ⟨?_, ?_, ?_, ⟨_, exponent_ok x hfin hz, ?_⟩⟩
    · simp only [F64.signbit, hb, decide_eq_decide]; omega
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, hb, h1]; omega
    · simp only [lt_iff, tb_abs, hb, h2]; omega
    · rw [ite_t hE]
      have hK : ((F64.toBits (F64.significand x) % 2^63 / 2^52 : Nat) : Int) +
          ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 1074) = ((Nat.log2 (F64.toBits x % 2^52)) : Int) - 51 := by rw [hb]; omega
      rw [ldexp_norm (F64.significand x) ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 1074) (by rw [hb]; omega)
        (by rw [hb]; omega) (by omega) (by omega), hK]
      have c1 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 ≥ 2047) := by omega
      have c2 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 > 0) := by omega
      have c3 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 ≤ -53) := by omega
      have c4 : ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 + 53).toNat = (Nat.log2 (F64.toBits x % 2^52)) + 2 := toNat_eq (by omega)
      rw [ite_f c1, ite_f c2, ite_f c3, c4, hb,
        mul_sub (F64.toBits x / 2^63) (F64.toBits x % 2^52) (Nat.log2 (F64.toBits x % 2^52)) F'
          (F64.ofBits (Nat.lor (Nat.land (F64.toBits x / 2^63 * 2^63 + 1023 * 2^52 + (F' - 2^52))
            0x800fffffffffffff) (((Nat.log2 (F64.toBits x % 2^52)) + 2) * 2^52)))
          (by omega) (by omega) (by omega) hf' m1 m2 m3 (by rw [tb_ofBits, pack_bits] <;> omega)]
      apply f64_ext
      rw [tb_ofBits]
      omega
  · rw [ite_f hE] at hb
    refine ⟨?_, ?_, ?_, ⟨_, exponent_ok x hfin hz, ?_⟩⟩
    · simp only [F64.signbit, hb, decide_eq_decide]; omega
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, hb, h1]; omega
    · simp only [lt_iff, tb_abs, hb, h2]; omega
    · rw [ite_f hE]
      have hK : ((F64.toBits (F64.significand x) % 2^63 / 2^52 : Nat) : Int) +
          (((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1023) = ((F64.toBits x / 2^52 % 2048 : Nat) : Int) := by rw [hb]; omega
      rw [ldexp_norm (F64.significand x) (((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1023) (by rw [hb]; omega)
        (by rw [hb]; omega) (by omega) (by omega), hK]
      have c1 : ¬ (((F64.toBits x / 2^52 % 2048 : Nat) : Int) ≥ 2047) := by omega
      have c2 : ((F64.toBits x / 2^52 % 2048 : Nat) : Int) > 0 := by omega
      have c4 : ((F64.toBits x / 2^52 % 2048 : Nat) : Int).toNat = F64.toBits x / 2^52 % 2048 := toNat_eq rfl
      rw [ite_f c1, ite_t c2, c4, hb, pack_bits]
      · apply f64_ext
        rw [tb_ofBits]
        omega
      all_goals omega

theorem frexpRange_proven : frexpRange := by
  intro x hfin hz
  have ht := tb_lt x
  have hf : ¬ F64.toBits x / 2^52 % 2048 = 2047 := by
    simpa [F64.isfinite, F64.exponentField] using hfin
  have hz' := (iszero_f x).mp hz
  have hv := frexp_val x hfin hz
  have h1 : F64.toBits F64.one = 0x3ff0000000000000 := by decide
  by_cases hE : F64.toBits x / 2^52 % 2048 = 0
  · rw [ite_t hE, ite_t hE] at hv
    have hne : F64.toBits x % 2^52 ≠ 0 := by omega
    have hf' : F64.toBits x % 2^52 < 2^52 := by omega
    obtain ⟨hL, -, -⟩ := log2_facts hne hf'
    obtain ⟨m1, m2, m3⟩ := sub_mant hne hf'
    generalize hFv : F64.toBits x % 2^52 * 2^(52 - (Nat.log2 (F64.toBits x % 2^52))) = F' at hv m1 m2 m3
    have hb : F64.toBits (F64.frexp x).1 = F64.toBits x / 2^63 * 2^63 + 1022 * 2^52 + (F' - 2^52) := by
      rw [hv, tb_ofBits]; omega
    have he : (F64.frexp x).2 = ((Nat.log2 (F64.toBits x % 2^52)) : Int) - 1073 := by rw [hv]
    generalize (F64.frexp x).1 = fr at hb ⊢
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, hb, tb_ofBits]; omega
    · simp only [lt_iff, tb_abs, hb, h1]; omega
    · have hK : ((F64.toBits fr % 2^63 / 2^52 : Nat) : Int) + ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 1073) =
          ((Nat.log2 (F64.toBits x % 2^52)) : Int) - 51 := by rw [hb]; omega
      rw [ldexp_norm fr ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 1073) (by rw [hb]; omega) (by rw [hb]; omega) (by omega)
        (by omega), hK]
      have c1 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 ≥ 2047) := by omega
      have c2 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 > 0) := by omega
      have c3 : ¬ ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 ≤ -53) := by omega
      have c4 : ((((Nat.log2 (F64.toBits x % 2^52)) : Nat) : Int) - 51 + 53).toNat = (Nat.log2 (F64.toBits x % 2^52)) + 2 := toNat_eq (by omega)
      rw [ite_f c1, ite_f c2, ite_f c3, c4, hb,
        mul_sub (F64.toBits x / 2^63) (F64.toBits x % 2^52) (Nat.log2 (F64.toBits x % 2^52)) F'
          (F64.ofBits (Nat.lor (Nat.land (F64.toBits x / 2^63 * 2^63 + 1022 * 2^52 + (F' - 2^52))
            0x800fffffffffffff) (((Nat.log2 (F64.toBits x % 2^52)) + 2) * 2^52)))
          (by omega) (by omega) (by omega) hf' m1 m2 m3 (by rw [tb_ofBits, pack_bits] <;> omega)]
      apply f64_ext
      rw [tb_ofBits]
      omega
  · rw [ite_f hE, ite_f hE] at hv
    have hb : F64.toBits (F64.frexp x).1 =
        F64.toBits x / 2^63 * 2^63 + 1022 * 2^52 + F64.toBits x % 2^52 := by
      rw [hv, tb_ofBits]; omega
    have he : (F64.frexp x).2 = ((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1022 := by rw [hv]
    generalize (F64.frexp x).1 = fr at hb ⊢
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · simp only [F64.le, Bool.or_eq_true, lt_iff, eq_iff, tb_abs, hb, tb_ofBits]; omega
    · simp only [lt_iff, tb_abs, hb, h1]; omega
    · have hK : ((F64.toBits fr % 2^63 / 2^52 : Nat) : Int) + (((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1022) =
          ((F64.toBits x / 2^52 % 2048 : Nat) : Int) := by rw [hb]; omega
      rw [ldexp_norm fr (((F64.toBits x / 2^52 % 2048 : Nat) : Int) - 1022) (by rw [hb]; omega) (by rw [hb]; omega) (by omega)
        (by omega), hK]
      have c1 : ¬ (((F64.toBits x / 2^52 % 2048 : Nat) : Int) ≥ 2047) := by omega
      have c2 : ((F64.toBits x / 2^52 % 2048 : Nat) : Int) > 0 := by omega
      have c4 : ((F64.toBits x / 2^52 % 2048 : Nat) : Int).toNat = F64.toBits x / 2^52 % 2048 := toNat_eq rfl
      rw [ite_f c1, ite_t c2, c4, hb, pack_bits]
      · apply f64_ext
        rw [tb_ofBits]
        omega
      all_goals omega

theorem powOneExponent_proven : powOneExponent := by
  intro x hn
  have hp : powBodyI x 1 = x := by
    rw [powBodyI_one]
    cases hf : F64.isfinite x
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact mul_one_eq x hn
    · rw [mul_zero_fin x hn hf, fma_zero_iszero]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact mul_one_eq x hn
  constructor
  · unfold powFF
    by_cases hb : (bitsOf x == 0x3ff0000000000000) = true
    · rw [ite_t hb]
      have hb' : F64.toBits x = 0x3ff0000000000000 := by simpa [bitsOf] using hb
      rw [show x = F64.one from f64_ext (by rw [hb', one_bits])]
    · rw [ite_f hb, lt_abs_one, ite_f (by decide : ¬ (false = true)), powFFClamped_one, hp]
  · rw [powFI_one, hp]

end JuliaLean.MathFuncs
