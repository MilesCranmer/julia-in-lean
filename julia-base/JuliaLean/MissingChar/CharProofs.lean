import JuliaLean.MissingChar.Char

/-!
# Proofs of the `Char` encoding properties

Every `UInt32` operation of the model is turned into `Nat` arithmetic on four bytes
(`b4`); bitwise `&&&`, `|||`, `^^^` act byte by byte (`and_b4`, `or_b4`, `xor_b4`).
`enc n` is the closed form of `Char(n)` per UTF-8 length class; `codepoint`,
`ismalformed` and `isoverlong` are then evaluated on `enc n` class by class
(`dec1` to `dec4`), and order, validity and arithmetic follow from `enc` being
strictly increasing.
-/

namespace JuliaLean.MissingChar

open JuliaLean.Strings

namespace CharPf

theorem iteT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

theorem iteF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-! ## Bitwise arithmetic on `Nat` -/

theorem tb_split (a b k j : Nat) (hb : b < 2 ^ k) :
    (2 ^ k * a + b).testBit j = if j < k then b.testBit j else a.testBit (j - k) := by
  have hm : (2 ^ k * a + b) % 2 ^ k = b := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hb
  have hd : (2 ^ k * a + b) / 2 ^ k = a := by
    rw [Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hb, Nat.add_zero]
  split
  · next h =>
    have := Nat.testBit_mod_two_pow (2 ^ k * a + b) k j
    rw [hm] at this; rw [this]; simp [h]
  · next h =>
    conv => lhs; rw [show j = k + (j - k) by omega]
    rw [← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow, hd]

theorem and_split (a b c e k : Nat) (hb : b < 2 ^ k) (he : e < 2 ^ k) :
    (2 ^ k * a + b) &&& (2 ^ k * c + e) = 2 ^ k * (a &&& c) + (b &&& e) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, tb_split _ _ _ _ hb, tb_split _ _ _ _ he,
    tb_split _ _ _ _ (Nat.and_lt_two_pow _ he), Nat.testBit_and, Nat.testBit_and]
  split <;> rfl

theorem or_split (a b c e k : Nat) (hb : b < 2 ^ k) (he : e < 2 ^ k) :
    (2 ^ k * a + b) ||| (2 ^ k * c + e) = 2 ^ k * (a ||| c) + (b ||| e) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, tb_split _ _ _ _ hb, tb_split _ _ _ _ he,
    tb_split _ _ _ _ (Nat.or_lt_two_pow hb he), Nat.testBit_or, Nat.testBit_or]
  split <;> rfl

theorem xor_split (a b c e k : Nat) (hb : b < 2 ^ k) (he : e < 2 ^ k) :
    (2 ^ k * a + b) ^^^ (2 ^ k * c + e) = 2 ^ k * (a ^^^ c) + (b ^^^ e) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, tb_split _ _ _ _ hb, tb_split _ _ _ _ he,
    tb_split _ _ _ _ (Nat.xor_lt_two_pow hb he), Nat.testBit_xor, Nat.testBit_xor]
  split <;> rfl

theorem and8 (a b c e : Nat) (hb : b < 256) (he : e < 256) :
    (256 * a + b) &&& (256 * c + e) = 256 * (a &&& c) + (b &&& e) := and_split a b c e 8 hb he

theorem or8 (a b c e : Nat) (hb : b < 256) (he : e < 256) :
    (256 * a + b) ||| (256 * c + e) = 256 * (a ||| c) + (b ||| e) := or_split a b c e 8 hb he

theorem xor8 (a b c e : Nat) (hb : b < 256) (he : e < 256) :
    (256 * a + b) ^^^ (256 * c + e) = 256 * (a ^^^ c) + (b ^^^ e) := xor_split a b c e 8 hb he

/-- Four bytes, most significant first. -/
def b4 (a b c d : Nat) : Nat := 256 * (256 * (256 * a + b) + c) + d

theorem and_b4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d &&& b4 a' b' c' d' = b4 (a &&& a') (b &&& b') (c &&& c') (d &&& d') := by
  unfold b4; rw [and8 _ _ _ _ hd hd', and8 _ _ _ _ hc hc', and8 _ _ _ _ hb hb']

theorem or_b4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d ||| b4 a' b' c' d' = b4 (a ||| a') (b ||| b') (c ||| c') (d ||| d') := by
  unfold b4; rw [or8 _ _ _ _ hd hd', or8 _ _ _ _ hc hc', or8 _ _ _ _ hb hb']

theorem xor_b4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d ^^^ b4 a' b' c' d' = b4 (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  unfold b4; rw [xor8 _ _ _ _ hd hd', xor8 _ _ _ _ hc hc', xor8 _ _ _ _ hb hb']

theorem and15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4
theorem and31 (x : Nat) : x &&& 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5
theorem and63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6
theorem and127 (x : Nat) : x &&& 127 = x % 128 := Nat.and_two_pow_sub_one_eq_mod x 7
theorem and255 (x : Nat) (h : x < 256) : x &&& 255 = x := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem and_mask (x k : Nat) : x &&& 63 * 2 ^ k = x / 2 ^ k % 64 * 2 ^ k := by
  have h := and_split (x / 2 ^ k) (x % 2 ^ k) 63 0 k (Nat.mod_lt _ (Nat.two_pow_pos k))
    (Nat.two_pow_pos k)
  rw [Nat.div_add_mod, Nat.add_zero, Nat.and_zero, Nat.add_zero, and63] at h
  rw [Nat.mul_comm 63, h, Nat.mul_comm]

theorem and_m8 (x : Nat) : x &&& 16128 = x / 256 % 64 * 256 := and_mask x 8
theorem and_m16 (x : Nat) : x &&& 4128768 = x / 65536 % 64 * 65536 := and_mask x 16
theorem and_m24 (x : Nat) : x &&& 1056964608 = x / 16777216 % 64 * 16777216 := and_mask x 24

theorem or_add (x y k : Nat) (h : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]

theorem or_add6 (x y : Nat) (h : x < 64) : x ||| y * 64 = x + y * 64 := or_add x y 6 h
theorem or_add12 (x y : Nat) (h : x < 4096) : x ||| y * 4096 = x + y * 4096 := or_add x y 12 h
theorem or_add18 (x y : Nat) (h : x < 262144) : x ||| y * 262144 = x + y * 262144 :=
  or_add x y 18 h

theorem cont192 (q : Nat) (h : q < 64) : (128 + q) &&& 192 = 128 :=
  (by decide : ∀ q, q < 64 → (128 + q) &&& 192 = 128) q h
theorem lead63 (p : Nat) (h : p < 64) : (192 + p) &&& 63 = p := by rw [and63]; omega
theorem lead31 (p : Nat) (h : p < 32) : (224 + p) &&& 31 = p := by rw [and31]; omega
theorem lead15 (p : Nat) (h : p < 16) : (240 + p) &&& 15 = p := by rw [and15]; omega
theorem or192 (x : Nat) (h : x < 64) : x ||| 192 = 192 + x :=
  (by decide : ∀ x, x < 64 → x ||| 192 = 192 + x) x h
theorem or224 (x : Nat) (h : x < 32) : x ||| 224 = 224 + x :=
  (by decide : ∀ x, x < 32 → x ||| 224 = 224 + x) x h
theorem or240 (x : Nat) (h : x < 16) : x ||| 240 = 240 + x :=
  (by decide : ∀ x, x < 16 → x ||| 240 = 240 + x) x h
theorem or128 (x : Nat) (h : x < 128) : x ||| 128 = 128 + x :=
  (by decide : ∀ x, x < 128 → x ||| 128 = 128 + x) x h

theorem b4_000 (d : Nat) : b4 0 0 0 d = d := by unfold b4; omega
theorem b4_div4 (c : Nat) : b4 0 0 c 0 / 4 = c * 64 := by unfold b4; omega
theorem b4_div16 (b : Nat) : b4 0 b 0 0 / 16 = b * 4096 := by unfold b4; omega
theorem b4_div64 (a : Nat) : b4 a 0 0 0 / 64 = a * 262144 := by unfold b4; omega

theorem or4hi {P0 P1 P2 P3 a b c d : Nat} (h0 : P0 = b4 a 0 0 0) (h1 : P1 = b4 0 b 0 0)
    (h2 : P2 = b4 0 0 c 0) (h3 : P3 = b4 0 0 0 d) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    P0 ||| P1 ||| P2 ||| P3 = b4 a b c d := by
  subst h0 h1 h2 h3
  simp (disch := omega) only [or_b4, Nat.or_zero, Nat.zero_or]

theorem or4lo {P0 P1 P2 P3 a b c d : Nat} (h0 : P0 = b4 0 0 0 d) (h1 : P1 = b4 0 0 c 0)
    (h2 : P2 = b4 0 b 0 0) (h3 : P3 = b4 a 0 0 0) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    P0 ||| P1 ||| P2 ||| P3 = b4 a b c d := by
  subst h0 h1 h2 h3
  simp (disch := omega) only [or_b4, Nat.or_zero, Nat.zero_or]

/-! ## `UInt32` operations as `Nat` operations -/

theorem eq_ofNat {x : UInt32} {m : Nat} (h : x.toNat = m) : x = UInt32.ofNat m := by
  rw [← h, UInt32.ofNat_toNat]

theorem shr_toNat (x k : UInt32) (h : k.toNat < 32) : (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h]

theorem shl_toNat (x k : UInt32) (h : k.toNat < 32) :
    (x <<< k).toNat = x.toNat * 2 ^ k.toNat % 4294967296 := by
  rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem shr0 (x : UInt32) : (x >>> (0 : UInt32)).toNat = x.toNat := by
  rw [shr_toNat x _ (by decide)]; exact Nat.div_one _
theorem shr2 (x : UInt32) : (x >>> (2 : UInt32)).toNat = x.toNat / 4 := shr_toNat x _ (by decide)
theorem shr4 (x : UInt32) : (x >>> (4 : UInt32)).toNat = x.toNat / 16 := shr_toNat x _ (by decide)
theorem shr6 (x : UInt32) : (x >>> (6 : UInt32)).toNat = x.toNat / 64 := shr_toNat x _ (by decide)
theorem shr8 (x : UInt32) : (x >>> (8 : UInt32)).toNat = x.toNat / 256 := shr_toNat x _ (by decide)
theorem shr16 (x : UInt32) : (x >>> (16 : UInt32)).toNat = x.toNat / 65536 :=
  shr_toNat x _ (by decide)
theorem shr20 (x : UInt32) : (x >>> (20 : UInt32)).toNat = x.toNat / 1048576 :=
  shr_toNat x _ (by decide)
theorem shr21 (x : UInt32) : (x >>> (21 : UInt32)).toNat = x.toNat / 2097152 :=
  shr_toNat x _ (by decide)
theorem shr24 (x : UInt32) : (x >>> (24 : UInt32)).toNat = x.toNat / 16777216 :=
  shr_toNat x _ (by decide)
theorem shr25 (x : UInt32) : (x >>> (25 : UInt32)).toNat = x.toNat / 33554432 :=
  shr_toNat x _ (by decide)

theorem shl0 (x : UInt32) : (x <<< (0 : UInt32)).toNat = x.toNat * 1 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl2 (x : UInt32) : (x <<< (2 : UInt32)).toNat = x.toNat * 4 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl4 (x : UInt32) : (x <<< (4 : UInt32)).toNat = x.toNat * 16 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl6 (x : UInt32) : (x <<< (6 : UInt32)).toNat = x.toNat * 64 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl8 (x : UInt32) : (x <<< (8 : UInt32)).toNat = x.toNat * 256 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl16 (x : UInt32) : (x <<< (16 : UInt32)).toNat = x.toNat * 65536 % 4294967296 :=
  shl_toNat x _ (by decide)
theorem shl24 (x : UInt32) : (x <<< (24 : UInt32)).toNat = x.toNat * 16777216 % 4294967296 :=
  shl_toNat x _ (by decide)

theorem ushr32_toNat (x : UInt32) (k : Nat) (hk : k < 32) :
    (ushr32 x k).toNat = x.toNat / 2 ^ k := by
  unfold ushr32
  rw [iteT hk, shr_toNat]
  · congr 2
    show (UInt32.ofNat k).toNat = k
    rw [UInt32.toNat_ofNat']; omega
  · show (UInt32.ofNat k).toNat < 32
    rw [UInt32.toNat_ofNat']; omega

theorem k3f : (0x0000003f : UInt32).toNat = 63 := rfl
theorem k3f00 : (0x00003f00 : UInt32).toNat = 16128 := rfl
theorem k3f0000 : (0x003f0000 : UInt32).toNat = 4128768 := rfl
theorem k3f000000 : (0x3f000000 : UInt32).toNat = 1056964608 := rfl
theorem kc0800000 : (0xc0800000 : UInt32).toNat = b4 192 128 0 0 := rfl
theorem ke0808000 : (0xe0808000 : UInt32).toNat = b4 224 128 128 0 := rfl
theorem kf0808080 : (0xf0808080 : UInt32).toNat = b4 240 128 128 128 := rfl
theorem kc0c0c0 : (0x00c0c0c0 : UInt32).toNat = b4 0 192 192 192 := rfl
theorem k808080 : (0x00808080 : UInt32).toNat = b4 0 128 128 128 := rfl
theorem k7f : (0x0000007f : UInt32).toNat = b4 0 0 0 127 := rfl
theorem k7f00 : (0x00007f00 : UInt32).toNat = b4 0 0 127 0 := rfl
theorem k7f0000 : (0x007f0000 : UInt32).toNat = b4 0 127 0 0 := rfl
theorem k7f000000 : (0x7f000000 : UInt32).toNat = b4 127 0 0 0 := rfl
theorem kff : (0xff : UInt32).toNat = 255 := rfl
theorem k80000000 : (0x80000000 : UInt32).toNat = 2147483648 := rfl
theorem kmask2 : (ushr32 0xffffffff 2).toNat = b4 63 255 255 255 := by decide
theorem kmask3 : (ushr32 0xffffffff 3).toNat = b4 31 255 255 255 := by decide
theorem kmask4 : (ushr32 0xffffffff 4).toNat = b4 15 255 255 255 := by decide

theorem and255' (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

/-! ## `leading_ones` and `trailing_zeros` -/

theorem clo32_eq (c : UInt32) (k : Nat) (hk : k < 32)
    (h1 : 4294967296 - 2 ^ (32 - k) ≤ c.toNat) (h2 : c.toNat < 4294967296 - 2 ^ (31 - k)) :
    clo32 c = k := by
  have hn : (~~~c).toNat = 4294967295 - c.toNat := UInt32.toNat_not c
  have hp : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hpos := Nat.two_pow_pos (31 - k)
  unfold clo32 clz32
  have hne : ~~~c ≠ 0 := by
    intro h; rw [h, UInt32.toNat_zero] at hn; omega
  rw [iteF hne, hn]
  have hlog : Nat.log2 (4294967295 - c.toNat) = 31 - k := by
    rw [Nat.log2_eq_iff (by omega), show 31 - k + 1 = 32 - k by omega]
    constructor <;> omega
  omega

theorem clo32_0 (c : UInt32) (h : c.toNat < 2147483648) : clo32 c = 0 :=
  clo32_eq c 0 (by decide) (Nat.zero_le _) h
theorem clo32_2 (c : UInt32) (h1 : 3221225472 ≤ c.toNat) (h2 : c.toNat < 3758096384) :
    clo32 c = 2 := clo32_eq c 2 (by decide) h1 h2
theorem clo32_3 (c : UInt32) (h1 : 3758096384 ≤ c.toNat) (h2 : c.toNat < 4026531840) :
    clo32 c = 3 := clo32_eq c 3 (by decide) h1 h2
theorem clo32_4 (c : UInt32) (h1 : 4026531840 ≤ c.toNat) (h2 : c.toNat < 4160749568) :
    clo32 c = 4 := clo32_eq c 4 (by decide) h1 h2

theorem ctzAux_le : ∀ (n x : Nat), ctzAux x n ≤ n
  | 0, _ => by simp [ctzAux]
  | n + 1, x => by
    have := ctzAux_le n (x / 2)
    simp only [ctzAux]; split <;> omega

theorem ctzAux_mul (y n : Nat) : ∀ k, ctzAux (2 ^ k * y) (k + n) = k + ctzAux y n
  | 0 => by simp
  | k + 1 => by
    have ih := ctzAux_mul y n k
    have h2 : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [ctzAux]
    rw [h2, iteF (show ¬ (2 * (2 ^ k * y) % 2 = 1) by omega),
      Nat.mul_div_cancel_left _ (by decide : 0 < 2), ih]
    omega

theorem ctzAux_lt8 (y m : Nat) (hy : y % 256 ≠ 0) : ctzAux y (m + 8) < 8 := by
  simp only [ctzAux]
  repeat' split
  all_goals omega

theorem ctz32_range (c : UInt32) (k y : Nat) (hk : k ≤ 24) (hc : c.toNat = 2 ^ k * y)
    (hy : y % 256 ≠ 0) : k ≤ ctz32 c ∧ ctz32 c < k + 8 := by
  have hne : c ≠ 0 := by
    intro h; rw [h, UInt32.toNat_zero] at hc
    rcases Nat.mul_eq_zero.mp hc.symm with h' | h'
    · exact absurd h' (by have := Nat.two_pow_pos k; omega)
    · rw [h'] at hy; exact hy rfl
  unfold ctz32
  rw [iteF hne, hc, show (32 : Nat) = k + (24 - k + 8) by omega, ctzAux_mul]
  have := ctzAux_lt8 y (24 - k) hy
  omega

theorem ctz32_ge (c : UInt32) (k y : Nat) (hk : k ≤ 32) (hc : c.toNat = 2 ^ k * y) :
    k ≤ ctz32 c ∧ ctz32 c ≤ 32 := by
  unfold ctz32
  split
  · omega
  · rw [hc, show (32 : Nat) = k + (32 - k) by omega, ctzAux_mul]
    have := ctzAux_le (32 - k) y
    omega

theorem land56_eq : ∀ t, t < 33 → land56 t = t / 8 * 8 := by decide

/-! ## The decoding steps of `codepoint` and `ismalformed` -/

theorem codepoint_of (c : UInt32) (l t : Nat) (hlt : ¬ c < 0x80000000) (hl : clo32 c = l)
    (ht : land56 (ctz32 c) = t) (hX : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) t = 0)
    (hchk : (decide (l = 1) || decide ((ix (8 * Int.ofNat l) + ix t).val > 32)) = false) :
    codepoint c = .ok (((ushr32 (c &&& ushr32 0xffffffff l) t &&& 0x0000007f) >>> 0) |||
      ((ushr32 (c &&& ushr32 0xffffffff l) t &&& 0x00007f00) >>> 2) |||
      ((ushr32 (c &&& ushr32 0xffffffff l) t &&& 0x007f0000) >>> 4) |||
      ((ushr32 (c &&& ushr32 0xffffffff l) t &&& 0x7f000000) >>> 6)) := by
  unfold codepoint
  dsimp only
  rw [iteF hlt, hl, ht, hX, hchk]
  rfl

theorem ismal_of (c : UInt32) (l t : Nat) (hl : clo32 c = l) (ht : land56 (ctz32 c) = t)
    (hX : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) t = 0)
    (h8 : (decide ((ix (Int.ofNat l * 8)).val = 8) ||
      decide ((ix (Int.ofNat l * 8) + ix t).val > 32)) = false) :
    ismalformed c = false := by
  unfold ismalformed
  dsimp only
  rw [hl, ht, hX, h8]
  decide

theorem decN_toNat (u : UInt32) (a b c d : Nat) (h : u.toNat = b4 a b c d)
    (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b % 128 < 64) (hc' : c % 128 < 64) (hd' : d % 128 < 64) :
    (((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)).toNat =
    a % 128 * 262144 + b % 128 * 4096 + c % 128 * 64 + d % 128 := by
  simp only [UInt32.toNat_or, UInt32.toNat_and, shr0, shr2, shr4, shr6, h, k7f, k7f00, k7f0000,
    k7f000000]
  simp (disch := omega) only [and_b4, Nat.and_zero, and127]
  simp only [b4_000, b4_div4, b4_div16, b4_div64]
  simp (disch := omega) only [or_add6, or_add12, or_add18]
  omega

theorem beq_shr (c k m : UInt32) (hk : k.toNat < 32) :
    (c >>> k == m) = decide (c.toNat / 2 ^ k.toNat = m.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt32.toNat_inj, shr_toNat c k hk]

theorem isoverlong_nat (c : UInt32) : isoverlong c =
    (decide (c.toNat / 33554432 = 96) || decide (c.toNat / 2097152 = 1796) ||
      decide (c.toNat / 1048576 = 3848)) := by
  unfold isoverlong isOverlongEnc
  rw [beq_shr c 25 0x60 (by decide), beq_shr c 21 0x0704 (by decide),
    beq_shr c 20 0x0f08 (by decide)]
  rfl

theorem over_false (x : Nat) (h1 : x / 33554432 ≠ 96) (h2 : x / 2097152 ≠ 1796)
    (h3 : x / 1048576 ≠ 3848) :
    (decide (x / 33554432 = 96) || decide (x / 2097152 = 1796) ||
      decide (x / 1048576 = 3848)) = false := by
  simp [h1, h2, h3]

/-! ## The four length classes -/

/-- `Char(u)` as a number, for `u < 0x200000`. -/
def enc (n : Nat) : Nat :=
  if n < 128 then b4 n 0 0 0
  else if n < 2048 then b4 (192 + n / 64) (128 + n % 64) 0 0
  else if n < 65536 then b4 (224 + n / 4096) (128 + n / 64 % 64) (128 + n % 64) 0
  else b4 (240 + n / 262144) (128 + n / 4096 % 64) (128 + n / 64 % 64) (128 + n % 64)

theorem enc_lt {n : Nat} (h : n < 2097152) : enc n < 4294967296 := by
  unfold enc b4
  repeat' split
  all_goals omega

theorem enc_mono {n m : Nat} (h : n < m) (hm : m < 2097152) : enc n < enc m := by
  unfold enc b4
  repeat' split
  all_goals omega

theorem enc_lt_iff {n m : Nat} (hn : n < 2097152) (hm : m < 2097152) :
    enc n < enc m ↔ n < m := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy n m with h' | h' | h'
    · exact h'
    · subst h'; omega
    · have := enc_mono h' hn; omega
  · exact fun h => enc_mono h hm

theorem enc_le_iff {n m : Nat} (hn : n < 2097152) (hm : m < 2097152) :
    enc n ≤ enc m ↔ n ≤ m := by
  rw [← Nat.not_lt, ← Nat.not_lt, enc_lt_iff hm hn]

theorem enc_eq_iff {n m : Nat} (hn : n < 2097152) (hm : m < 2097152) :
    enc n = enc m ↔ n = m := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy n m with h' | h' | h'
    · have := enc_mono h' hm; omega
    · exact h'
    · have := enc_mono h' hn; omega
  · intro h; rw [h]

theorem toNat_enc {n : Nat} (hn : n < 2097152) : (UInt32.ofNat (enc n)).toNat = enc n := by
  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (enc_lt hn)

theorem cexp_toNat (u : UInt32) (h : u.toNat < 2097152) :
    (((u <<< (0 : UInt32)) &&& (0x0000003f : UInt32)) |||
      ((u <<< (2 : UInt32)) &&& (0x00003f00 : UInt32)) |||
      ((u <<< (4 : UInt32)) &&& (0x003f0000 : UInt32)) |||
      ((u <<< (6 : UInt32)) &&& (0x3f000000 : UInt32))).toNat =
    b4 (u.toNat / 262144) (u.toNat / 4096 % 64) (u.toNat / 64 % 64) (u.toNat % 64) := by
  simp only [UInt32.toNat_or, UInt32.toNat_and, shl0, shl2, shl4, shl6, k3f, k3f00, k3f0000,
    k3f000000, and63, and_m8, and_m16, and_m24]
  generalize u.toNat = n at h ⊢
  refine or4lo ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (try unfold b4) <;> omega

theorem charOfU32_big (u : UInt32) (h : 2097152 ≤ u.toNat) :
    charOfU32 u = .error (.codePointError u) := by
  have h1 : ¬ u < 0x80 := fun h' => by
    have : u.toNat < 128 := UInt32.lt_iff_toNat_lt.mp h'
    omega
  have h2 : ¬ u < 0x00200000 := fun h' => by
    have : u.toNat < 2097152 := UInt32.lt_iff_toNat_lt.mp h'
    omega
  unfold charOfU32
  rw [iteF h1, iteT (show (!decide (u < 0x00200000)) = true by simp [h2])]

theorem charOfU32_ok (u : UInt32) (h : u.toNat < 2097152) :
    charOfU32 u = .ok (UInt32.ofNat (enc u.toNat)) := by
  have hc := cexp_toNat u h
  unfold charOfU32
  by_cases h1 : u.toNat < 128
  · rw [iteT (show u < 0x80 from UInt32.lt_iff_toNat_lt.mpr h1)]
    refine congrArg Except.ok (eq_ofNat ?_)
    rw [shl24]; unfold enc; rw [iteT h1]; unfold b4; omega
  rw [iteF (show ¬ u < 0x80 from fun h' => h1 (UInt32.lt_iff_toNat_lt.mp h')),
    iteF (show ¬ (!decide (u < 0x00200000)) = true by
      simp [show u < 0x00200000 from UInt32.lt_iff_toNat_lt.mpr h])]
  dsimp only
  refine congrArg Except.ok (eq_ofNat ?_)
  by_cases h2 : u.toNat < 2048
  · rw [iteT (show u < 0x00000800 from UInt32.lt_iff_toNat_lt.mpr h2), UInt32.toNat_or, shl16,
      hc, kc0800000]
    unfold enc; rw [iteF h1, iteT h2]
    generalize u.toNat = n at *
    rw [show b4 (n / 262144) (n / 4096 % 64) (n / 64 % 64) (n % 64) * 65536 % 4294967296 =
      b4 (n / 64 % 64) (n % 64) 0 0 by unfold b4; omega]
    simp (disch := omega) only [or_b4, or192, or128, Nat.or_zero]
    unfold b4; omega
  rw [iteF (show ¬ u < 0x00000800 from fun h' => h2 (UInt32.lt_iff_toNat_lt.mp h'))]
  by_cases h3 : u.toNat < 65536
  · rw [iteT (show u < 0x00010000 from UInt32.lt_iff_toNat_lt.mpr h3), UInt32.toNat_or, shl8,
      hc, ke0808000]
    unfold enc; rw [iteF h1, iteF h2, iteT h3]
    generalize u.toNat = n at *
    rw [show b4 (n / 262144) (n / 4096 % 64) (n / 64 % 64) (n % 64) * 256 % 4294967296 =
      b4 (n / 4096 % 64) (n / 64 % 64) (n % 64) 0 by unfold b4; omega]
    simp (disch := omega) only [or_b4, or224, or128, Nat.or_zero]
    unfold b4; omega
  rw [iteF (show ¬ u < 0x00010000 from fun h' => h3 (UInt32.lt_iff_toNat_lt.mp h')),
    UInt32.toNat_or, hc, kf0808080]
  unfold enc; rw [iteF h1, iteF h2, iteF h3]
  generalize u.toNat = n at *
  simp (disch := omega) only [or_b4, or240, or128]

theorem small_of_ok {u c : UInt32} (h : charOfU32 u = .ok c) : u.toNat < 2097152 := by
  apply Classical.byContradiction
  intro h'
  rw [charOfU32_big u (by omega)] at h
  cases h

theorem dec1 (c : UInt32) (n : Nat) (h1 : n < 128) (hc : c.toNat = b4 n 0 0 0) :
    codepoint c = .ok (UInt32.ofNat n) ∧ ismalformed c = false ∧ isoverlong c = false := by
  have hlt : c < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, hc, k80000000]; unfold b4; omega
  have hl : clo32 c = 0 := clo32_0 c (by rw [hc]; unfold b4; omega)
  have ht : land56 (ctz32 c) = 24 ∨ land56 (ctz32 c) = 32 := by
    have := ctz32_ge c 24 n (by omega) (by rw [hc]; unfold b4; omega)
    rw [land56_eq _ (by omega)]; omega
  have hA : ((c &&& 0x00c0c0c0) ^^^ 0x00808080).toNat = b4 0 128 128 128 := by
    rw [UInt32.toNat_xor, UInt32.toNat_and, hc, kc0c0c0, k808080]
    simp (disch := omega) only [and_b4, xor_b4, Nat.and_zero, Nat.zero_and]
    decide
  have hX : ∀ t, (t = 24 ∨ t = 32) → ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) t = 0 := by
    intro t ht
    rcases ht with rfl | rfl
    · apply UInt32.toNat_inj.mp
      rw [ushr32_toNat _ _ (by decide), hA]
      decide
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold codepoint
    dsimp only
    rw [iteT hlt]
    refine congrArg Except.ok (eq_ofNat ?_)
    rw [shr24, hc]; unfold b4; omega
  · rcases ht with ht | ht
    · exact ismal_of c 0 24 hl ht (hX 24 (Or.inl rfl)) (by decide)
    · exact ismal_of c 0 32 hl ht (hX 32 (Or.inr rfl)) (by decide)
  · rw [isoverlong_nat, hc]
    exact over_false _ (by unfold b4; omega) (by unfold b4; omega) (by unfold b4; omega)

theorem dec2 (c : UInt32) (n : Nat) (h1 : 128 ≤ n) (h2 : n < 2048)
    (hc : c.toNat = b4 (192 + n / 64) (128 + n % 64) 0 0) :
    codepoint c = .ok (UInt32.ofNat n) ∧ ismalformed c = false ∧ isoverlong c = false := by
  have hlt : ¬ c < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, hc, k80000000]; unfold b4; omega
  have hl : clo32 c = 2 :=
    clo32_2 c (by rw [hc]; unfold b4; omega) (by rw [hc]; unfold b4; omega)
  have ht : land56 (ctz32 c) = 16 := by
    have := ctz32_range c 16 (256 * (192 + n / 64) + (128 + n % 64)) (by omega)
      (by rw [hc]; unfold b4; omega) (by omega)
    rw [land56_eq _ (by omega)]; omega
  have hX : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 16 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), UInt32.toNat_xor, UInt32.toNat_and, hc, kc0c0c0, k808080]
    simp (disch := omega) only [and_b4, cont192, Nat.and_zero]
    decide
  refine ⟨?_, ismal_of c 2 16 hl ht hX (by decide), ?_⟩
  · rw [codepoint_of c 2 16 hlt hl ht hX (by decide)]
    refine congrArg Except.ok (eq_ofNat ?_)
    have hu : (ushr32 (c &&& ushr32 0xffffffff 2) 16).toNat = b4 0 0 (n / 64) (128 + n % 64) := by
      rw [ushr32_toNat _ _ (by decide), UInt32.toNat_and, hc, kmask2]
      simp (disch := omega) only [and_b4, lead63, and255]
      unfold b4; omega
    rw [decN_toNat _ 0 0 (n / 64) (128 + n % 64) hu (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    omega
  · rw [isoverlong_nat, hc]
    exact over_false _ (by unfold b4; omega) (by unfold b4; omega) (by unfold b4; omega)

theorem over3 (p q r : Nat) (hp : p < 16) (hq : q < 64) (hr : r < 64)
    (hn : 2048 ≤ 4096 * p + 64 * q + r) :
    (decide (b4 (224 + p) (128 + q) (128 + r) 0 / 33554432 = 96) ||
      decide (b4 (224 + p) (128 + q) (128 + r) 0 / 2097152 = 1796) ||
      decide (b4 (224 + p) (128 + q) (128 + r) 0 / 1048576 = 3848)) = false :=
  over_false _ (by unfold b4; omega) (by unfold b4; omega) (by unfold b4; omega)

theorem over4 (p q r s : Nat) (hq : q < 64) (hr : r < 64) (hs : s < 64)
    (hn : 65536 ≤ 262144 * p + 4096 * q + 64 * r + s) :
    (decide (b4 (240 + p) (128 + q) (128 + r) (128 + s) / 33554432 = 96) ||
      decide (b4 (240 + p) (128 + q) (128 + r) (128 + s) / 2097152 = 1796) ||
      decide (b4 (240 + p) (128 + q) (128 + r) (128 + s) / 1048576 = 3848)) = false :=
  over_false _ (by unfold b4; omega) (by unfold b4; omega) (by unfold b4; omega)

theorem dec3 (c : UInt32) (n : Nat) (h1 : 2048 ≤ n) (h2 : n < 65536)
    (hc : c.toNat = b4 (224 + n / 4096) (128 + n / 64 % 64) (128 + n % 64) 0) :
    codepoint c = .ok (UInt32.ofNat n) ∧ ismalformed c = false ∧ isoverlong c = false := by
  have hlt : ¬ c < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, hc, k80000000]; unfold b4; omega
  have hl : clo32 c = 3 :=
    clo32_3 c (by rw [hc]; unfold b4; omega) (by rw [hc]; unfold b4; omega)
  have ht : land56 (ctz32 c) = 8 := by
    have := ctz32_range c 8
      (65536 * (224 + n / 4096) + 256 * (128 + n / 64 % 64) + (128 + n % 64)) (by omega)
      (by rw [hc]; unfold b4; omega) (by omega)
    rw [land56_eq _ (by omega)]; omega
  have hX : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 8 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), UInt32.toNat_xor, UInt32.toNat_and, hc, kc0c0c0, k808080]
    simp (disch := omega) only [and_b4, cont192, Nat.and_zero]
    decide
  refine ⟨?_, ismal_of c 3 8 hl ht hX (by decide), ?_⟩
  · rw [codepoint_of c 3 8 hlt hl ht hX (by decide)]
    refine congrArg Except.ok (eq_ofNat ?_)
    have hu : (ushr32 (c &&& ushr32 0xffffffff 3) 8).toNat =
        b4 0 (n / 4096) (128 + n / 64 % 64) (128 + n % 64) := by
      rw [ushr32_toNat _ _ (by decide), UInt32.toNat_and, hc, kmask3]
      simp (disch := omega) only [and_b4, lead31, and255]
      unfold b4; omega
    rw [decN_toNat _ 0 (n / 4096) (128 + n / 64 % 64) (128 + n % 64) hu (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    omega
  · rw [isoverlong_nat, hc]
    exact over3 (n / 4096) (n / 64 % 64) (n % 64) (by omega) (by omega) (by omega) (by omega)

theorem dec4 (c : UInt32) (n : Nat) (h1 : 65536 ≤ n) (h2 : n < 2097152)
    (hc : c.toNat = b4 (240 + n / 262144) (128 + n / 4096 % 64) (128 + n / 64 % 64)
      (128 + n % 64)) :
    codepoint c = .ok (UInt32.ofNat n) ∧ ismalformed c = false ∧ isoverlong c = false := by
  have hlt : ¬ c < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, hc, k80000000]; unfold b4; omega
  have hl : clo32 c = 4 :=
    clo32_4 c (by rw [hc]; unfold b4; omega) (by rw [hc]; unfold b4; omega)
  have ht : land56 (ctz32 c) = 0 := by
    have := ctz32_range c 0 c.toNat (by omega) (by omega) (by rw [hc]; unfold b4; omega)
    rw [land56_eq _ (by omega)]; omega
  have hX : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 0 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), UInt32.toNat_xor, UInt32.toNat_and, hc, kc0c0c0, k808080]
    simp (disch := omega) only [and_b4, xor_b4, cont192, Nat.and_zero]
    decide
  refine ⟨?_, ismal_of c 4 0 hl ht hX (by decide), ?_⟩
  · rw [codepoint_of c 4 0 hlt hl ht hX (by decide)]
    refine congrArg Except.ok (eq_ofNat ?_)
    have hu : (ushr32 (c &&& ushr32 0xffffffff 4) 0).toNat =
        b4 (n / 262144) (128 + n / 4096 % 64) (128 + n / 64 % 64) (128 + n % 64) := by
      rw [ushr32_toNat _ _ (by decide), UInt32.toNat_and, hc, kmask4]
      simp (disch := omega) only [and_b4, lead15, and255]
      unfold b4; omega
    rw [decN_toNat _ (n / 262144) (128 + n / 4096 % 64) (128 + n / 64 % 64) (128 + n % 64) hu
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    omega
  · rw [isoverlong_nat, hc]
    exact over4 (n / 262144) (n / 4096 % 64) (n / 64 % 64) (n % 64) (by omega) (by omega)
      (by omega) (by omega)

theorem dec_all (c : UInt32) (n : Nat) (hn : n < 2097152) (hc : c.toNat = enc n) :
    codepoint c = .ok (UInt32.ofNat n) ∧ ismalformed c = false ∧ isoverlong c = false := by
  unfold enc at hc
  by_cases h1 : n < 128
  · rw [iteT h1] at hc; exact dec1 c n h1 hc
  rw [iteF h1] at hc
  by_cases h2 : n < 2048
  · rw [iteT h2] at hc; exact dec2 c n (by omega) h2 hc
  rw [iteF h2] at hc
  by_cases h3 : n < 65536
  · rw [iteT h3] at hc; exact dec3 c n (by omega) h3 hc
  rw [iteF h3] at hc
  exact dec4 c n (by omega) hn hc

/-! ## `Char` arithmetic and `write` -/

set_option maxRecDepth 100000 in
theorem i8_toInt (b : UInt8) :
    b.toInt8.toInt = if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256 := by
  have h := (by decide : ∀ i, i < 256 → (UInt8.ofNat i).toInt8.toInt =
    if (UInt8.ofNat i).toNat < 128 then ((UInt8.ofNat i).toNat : Int)
    else ((UInt8.ofNat i).toNat : Int) - 256) b.toNat (UInt8.toNat_lt b)
  rwa [UInt8.ofNat_toNat] at h

theorem wrap_i32 (x : Int) (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) :
    wrapInt .i32 x = x := by
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem wrap_i64 (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    wrapInt .i64 x = x := by
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem bswap_toNat (c : UInt32) : (bswap32 c).toNat =
    b4 (c.toNat % 256) (c.toNat / 256 % 256) (c.toNat / 65536 % 256) (c.toNat / 16777216) := by
  unfold bswap32
  simp only [UInt32.toNat_or, UInt32.toNat_and, shl24, shl16, shl8, shr8, shr16, shr24, kff,
    and255']
  have hlt := UInt32.toNat_lt c
  generalize c.toNat = x at hlt ⊢
  refine or4hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (try unfold b4) <;> omega

theorem shr8_eq_zero (x : UInt32) : (x >>> 8 = 0) ↔ x.toNat / 256 = 0 := by
  rw [← UInt32.toNat_inj, shr8, UInt32.toNat_zero]

theorem wl_len (w : UInt32) : (writeCharLoop 4 w).length =
    if w.toNat / 256 = 0 then 1 else if w.toNat / 65536 = 0 then 2
    else if w.toNat / 16777216 = 0 then 3 else 4 := by
  simp only [writeCharLoop, shr8_eq_zero, shr8]
  repeat' split
  all_goals (try simp only [List.length_cons, List.length_nil])
  all_goals omega

end CharPf

open CharPf

theorem codepointWellFormed_proven : CodepointWellFormed := by
  intro c hm
  unfold ismalformed at hm
  simp only [Int.mul_comm (Int.ofNat (clo32 c)) 8, Bool.or_eq_false_iff] at hm
  obtain ⟨⟨hA, hD⟩, hX⟩ := hm
  unfold codepoint
  dsimp only
  by_cases h1 : c < 0x80000000
  · rw [iteT h1]; exact ⟨_, rfl⟩
  rw [iteF h1, hD, hX]
  have hl : decide (clo32 c = 1) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    rw [h] at hA
    exact absurd hA (by decide)
  rw [hl]
  exact ⟨_, rfl⟩

theorem charCodepointRoundTrip_proven : CharCodepointRoundTrip := by
  intro u
  constructor
  · intro h
    exact charOfU32_big u (UInt32.le_iff_toNat_le.mp h)
  · intro h
    have hn : u.toNat < 2097152 := UInt32.lt_iff_toNat_lt.mp h
    obtain ⟨h1, h2, h3⟩ := dec_all _ _ hn (toNat_enc hn)
    refine ⟨_, charOfU32_ok u hn, ?_, h2, h3⟩
    rw [h1, UInt32.ofNat_toNat]

theorem charOrderCodepoint_proven : CharOrderCodepoint := by
  intro u v c d hc hd
  have hu := small_of_ok hc
  have hv := small_of_ok hd
  rw [charOfU32_ok u hu] at hc
  rw [charOfU32_ok v hv] at hd
  cases hc
  cases hd
  constructor
  · rw [UInt32.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, toNat_enc hu, toNat_enc hv]
    exact enc_lt_iff hu hv
  · rw [← UInt32.toNat_inj, toNat_enc hu, toNat_enc hv, ← UInt32.toNat_inj (a := u)]
    exact enc_eq_iff hu hv

theorem isvalidCharCodepoint_proven : IsvalidCharCodepoint := by
  intro u c hc
  have hu := small_of_ok hc
  rw [charOfU32_ok u hu] at hc
  cases hc
  obtain ⟨-, h2, h3⟩ := dec_all _ _ hu (toNat_enc hu)
  have ht := toNat_enc hu
  have e1 : decide (UInt32.ofNat (enc u.toNat) ≤ 0xed9fbf00) = decide (u.toNat ≤ 0xd7ff) := by
    apply decide_eq_decide.mpr
    rw [UInt32.le_iff_toNat_le, ht, show (0xed9fbf00 : UInt32).toNat = enc 0xd7ff by decide]
    exact enc_le_iff hu (by decide)
  have e2 : decide (0xee808000 ≤ UInt32.ofNat (enc u.toNat)) = decide (0xe000 ≤ u.toNat) := by
    apply decide_eq_decide.mpr
    rw [UInt32.le_iff_toNat_le, ht, show (0xee808000 : UInt32).toNat = enc 0xe000 by decide]
    exact enc_le_iff (by decide) hu
  have e3 : decide (UInt32.ofNat (enc u.toNat) ≤ 0xf48fbfbf) = decide (u.toNat ≤ 0x10ffff) := by
    apply decide_eq_decide.mpr
    rw [UInt32.le_iff_toNat_le, ht, show (0xf48fbfbf : UInt32).toNat = enc 0x10ffff by decide]
    exact enc_le_iff hu (by decide)
  unfold isvalidChar isvalidCharU
  rw [h2, show isoverlong (UInt32.ofNat (enc u.toNat)) = false from h3, e1, e2, e3]
  rfl

theorem int_lt32 (z : Int) (h : z < 2097152) : z < 2 ^ 32 :=
  Int.lt_of_lt_of_le h (by decide)

theorem charOfInt_ok (z : Int) (h0 : 0 ≤ z) (h1 : z < 2097152) :
    charOfInt z = charOfU32 (UInt32.ofNat z.toNat) := by
  unfold charOfInt
  rw [iteT (show 0 ≤ z ∧ z < 2 ^ 32 from ⟨h0, int_lt32 z h1⟩)]

theorem add64_val (N : Int) (m : JInt64) (h0 : 0 ≤ N) (h1 : N < 2097152) (h2 : 0 ≤ N + m.val)
    (h3 : N + m.val < 2097152) : (JInt.lit .i64 N + m).val = N + m.val := by
  show wrapInt .i64 ((JInt.lit .i64 N).val + m.val) = _
  rw [show (JInt.lit .i64 N).val = N from wrap_i64 _ (by omega) (by omega)]
  exact wrap_i64 _ (by omega) (by omega)

theorem add32_val (N : Int) (y : JInt .i32) (h0 : 0 ≤ N) (h1 : N < 2097152)
    (h2 : 0 ≤ N + y.val) (h3 : N + y.val < 2097152) : (JInt.lit .i32 N + y).val = N + y.val := by
  show wrapInt .i32 ((JInt.lit .i32 N).val + y.val) = _
  rw [show (JInt.lit .i32 N).val = N from wrap_i32 _ (by omega) (by omega)]
  exact wrap_i32 _ (by omega) (by omega)

theorem conv32 (m : JInt64) (h : IntTy.i32.min ≤ m.val ∧ m.val ≤ IntTy.i32.max) :
    JInt.convert .i32 m.val = .ok ⟨m.val, h⟩ := by
  unfold JInt.convert
  split
  · rfl
  · next h' => exact absurd h h'

theorem i32_bound (m : JInt64) (h0 : -2097152 ≤ m.val) (h1 : m.val < 2097152) :
    IntTy.i32.min ≤ m.val ∧ m.val ≤ IntTy.i32.max := by
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem int32Of (c u : UInt32) (h : codepoint c = .ok u) :
    int32OfChar c = .ok (JInt.lit .i32 (u.toNat : Int)) := by
  unfold int32OfChar; rw [h]; rfl

theorem top_val (N : Nat) (hN : N < 2097152) :
    (JInt.lit .i32 ((UInt32.ofNat (enc N) >>> 24).toUInt8.toInt8.toInt)).val =
      if N < 128 then (N : Int) else ((enc N / 16777216 : Nat) : Int) - 256 := by
  have htop : ((UInt32.ofNat (enc N) >>> 24).toUInt8).toNat = enc N / 16777216 := by
    rw [UInt32.toNat_toUInt8, shr24, toNat_enc hN]; have := enc_lt hN; omega
  rw [i8_toInt, htop]
  by_cases hA : N < 128
  · have he : enc N / 16777216 = N := by unfold enc; rw [iteT hA]; unfold b4; omega
    rw [he, iteT hA]
    exact wrap_i32 _ (by omega) (by omega)
  · have he : 192 ≤ enc N / 16777216 ∧ enc N / 16777216 < 256 := by
      unfold enc; rw [iteF hA]
      repeat' split
      all_goals (unfold b4; omega)
    rw [iteF (show ¬ (enc N / 16777216 < 128) by omega), iteF hA]
    exact wrap_i32 _ (by omega) (by omega)

theorem charAdd_ascii (N : Nat) (n : JInt64) (hA : N < 128) (h0 : 0 ≤ (N : Int) + n.val)
    (h1 : (N : Int) + n.val < 2097152) :
    charAdd (UInt32.ofNat (enc N)) n = charOfU32 (UInt32.ofNat ((N : Int) + n.val).toNat) := by
  unfold charAdd
  dsimp only
  rw [top_val N (by omega), iteT hA, iteT (show (0 : Int) ≤ (N : Int) by omega),
    add64_val (N : Int) n (by omega) (by omega) h0 h1]
  by_cases hs : 0 ≤ (N : Int) + n.val ∧ (N : Int) + n.val < 0x80
  · rw [iteT hs]
    unfold charOfU32
    rw [iteT (show UInt32.ofNat ((N : Int) + n.val).toNat < 0x80 from by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat']; show _ < 128; omega)]
  · rw [iteF hs, charOfInt_ok _ h0 h1]

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem charAdd_multi (N : Nat) (n : JInt64) (hN : N < 2097152) (hA : ¬ N < 128)
    (hcp : codepoint (UInt32.ofNat (enc N)) = .ok (UInt32.ofNat N))
    (h0 : 0 ≤ (N : Int) + n.val) (h1 : (N : Int) + n.val < 2097152) :
    charAdd (UInt32.ofNat (enc N)) n = charOfU32 (UInt32.ofNat ((N : Int) + n.val).toNat) := by
  have he : 192 ≤ enc N / 16777216 := by
    unfold enc; rw [iteF hA]
    repeat' split
    all_goals (unfold b4; omega)
  have hel := enc_lt hN
  have hbound := i32_bound n (by omega) (by omega)
  have hN' : (UInt32.ofNat N).toNat = N := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  unfold charAdd
  dsimp only
  rw [top_val N hN, iteF hA,
    iteF (show ¬ (0 : Int) ≤ ((enc N / 16777216 : Nat) : Int) - 256 by omega),
    int32Of _ _ hcp, conv32 n hbound]
  rw [ok_bind]
  dsimp only
  rw [ok_bind]
  rw [hN', add32_val (N : Int) ⟨n.val, hbound⟩ (by omega) (by omega) h0 h1,
    charOfInt_ok _ h0 h1]

theorem charAddCodepoint_proven : CharAddCodepoint := by
  intro u c n hc h0 h1
  have hu := small_of_ok hc
  rw [charOfU32_ok u hu] at hc
  cases hc
  obtain ⟨hcp, -, -⟩ := dec_all _ _ hu (toNat_enc hu)
  generalize u.toNat = N at *
  by_cases hA : N < 128
  · exact charAdd_ascii N n hA h0 h1
  · exact charAdd_multi N n hu hA hcp h0 h1

theorem ncodeunitsWrite_proven : NcodeunitsWrite := by
  intro c
  unfold writeChar ncodeunitsChar
  rw [wl_len, bswap_toNat]
  by_cases h0 : c = 0
  · subst h0; decide
  rw [iteF h0]
  have hlt := UInt32.toNat_lt c
  have hx0 : c.toNat ≠ 0 := fun h => h0 (UInt32.toNat_inj.mp (by rw [h, UInt32.toNat_zero]))
  have hr : ctz32 c / 8 = (if c.toNat % 256 ≠ 0 then 0 else if c.toNat / 256 % 256 ≠ 0 then 1
      else if c.toNat / 65536 % 256 ≠ 0 then 2 else 3) := by
    by_cases b0 : c.toNat % 256 = 0
    · by_cases b1 : c.toNat / 256 % 256 = 0
      · by_cases b2 : c.toNat / 65536 % 256 = 0
        · have := ctz32_range c 24 (c.toNat / 16777216) (by omega) (by omega) (by omega)
          rw [iteF (by omega), iteF (by omega), iteF (by omega)]; omega
        · have := ctz32_range c 16 (c.toNat / 65536) (by omega) (by omega) (by omega)
          rw [iteF (by omega), iteF (by omega), iteT (by omega)]; omega
      · have := ctz32_range c 8 (c.toNat / 256) (by omega) (by omega) (by omega)
        rw [iteF (by omega), iteT (by omega)]; omega
    · have := ctz32_range c 0 c.toNat (by omega) (by omega) (by omega)
      rw [iteT (by omega)]; omega
  rw [hr]
  unfold b4
  repeat' split
  all_goals omega

end JuliaLean.MissingChar
