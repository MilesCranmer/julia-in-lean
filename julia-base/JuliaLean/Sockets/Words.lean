import JuliaLean.Sockets.Lemmas

namespace JuliaLean.Sockets

/-- Bitwise OR is addition when the high word has no bits in the low word. -/
theorem lor_add_disjoint (x y k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) :
    x ||| y = x + y := by
  have ex : x = 2 ^ k * (x / 2 ^ k) := by
    have h := Nat.div_add_mod x (2 ^ k)
    rw [hx, Nat.add_zero] at h
    exact h.symm
  apply Nat.eq_of_testBit_eq
  intro i
  change (Nat.bitwise (· || ·) x y).testBit i = (x + y).testBit i
  rw [Nat.testBit_bitwise (by rfl)]
  have hb : 0 < 2 ^ k := Nat.two_pow_pos k
  have hxb := Nat.testBit_two_pow_mul_add (x / 2 ^ k) (b := 0) hb i
  simp only [Nat.add_zero, Nat.zero_testBit] at hxb
  have hyb := Nat.testBit_two_pow_mul_add 0 hy i
  simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_testBit] at hyb
  have hsum := Nat.testBit_two_pow_mul_add (x / 2 ^ k) hy i
  rw [← ex] at hsum hxb
  rw [hxb, hsum]
  by_cases hi : i < k
  · simp [hi]
  · have hey : y.testBit i = false := by simpa [hi] using hyb
    simp [hi, hey]

@[simp] theorem or_slot0 {x v : Nat} (hx : x % 2 ^ 16 = 0) (hv : v < 65536) :
    x ||| v = x + v := lor_add_disjoint x v 16 hx (by omega)

@[simp] theorem or_slot1 {x v : Nat} (hx : x % 2 ^ 32 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 16) = x + v * 2 ^ 16 := lor_add_disjoint _ _ 32 hx (by omega)

@[simp] theorem or_slot2 {x v : Nat} (hx : x % 2 ^ 48 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 32) = x + v * 2 ^ 32 := lor_add_disjoint _ _ 48 hx (by omega)

@[simp] theorem or_slot3 {x v : Nat} (hx : x % 2 ^ 64 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 48) = x + v * 2 ^ 48 := lor_add_disjoint _ _ 64 hx (by omega)

@[simp] theorem or_slot4 {x v : Nat} (hx : x % 2 ^ 80 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 64) = x + v * 2 ^ 64 := lor_add_disjoint _ _ 80 hx (by omega)

@[simp] theorem or_slot5 {x v : Nat} (hx : x % 2 ^ 96 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 80) = x + v * 2 ^ 80 := lor_add_disjoint _ _ 96 hx (by omega)

@[simp] theorem or_slot6 {x v : Nat} (hx : x % 2 ^ 112 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 96) = x + v * 2 ^ 96 := lor_add_disjoint _ _ 112 hx (by omega)

@[simp] theorem or_slot7 {x v : Nat} (hx : x % 2 ^ 128 = 0) (hv : v < 65536) :
    x ||| (v * 2 ^ 112) = x + v * 2 ^ 112 := lor_add_disjoint _ _ 128 hx (by omega)

@[simp] theorem or_byte0 {x v : Nat} (hx : x % 2 ^ 8 = 0) (hv : v < 256) :
    x ||| v = x + v := lor_add_disjoint x v 8 hx (by omega)

@[simp] theorem or_byte1 {x v : Nat} (hx : x % 2 ^ 16 = 0) (hv : v < 256) :
    x ||| (v * 2 ^ 8) = x + v * 2 ^ 8 := lor_add_disjoint _ _ 16 hx (by omega)

@[simp] theorem or_byte2 {x v : Nat} (hx : x % 2 ^ 24 = 0) (hv : v < 256) :
    x ||| (v * 2 ^ 16) = x + v * 2 ^ 16 := lor_add_disjoint _ _ 24 hx (by omega)

@[simp] theorem or_byte3 {x v : Nat} (hx : x % 2 ^ 32 = 0) (hv : v < 256) :
    x ||| (v * 2 ^ 24) = x + v * 2 ^ 24 := lor_add_disjoint _ _ 32 hx (by omega)

theorem ipv4Byte_bound (h i : Nat) : ipv4Byte h i < 256 := Nat.mod_lt _ (by decide)
theorem ipv6Field_bound (h i : Nat) : ipv6Field h i < 65536 := Nat.mod_lt _ (by decide)

theorem ipv4_decomposition (h : Nat) (hh : h < 2 ^ 32) :
    ipv4Byte h 3 * 2 ^ 24 + ipv4Byte h 2 * 2 ^ 16 + ipv4Byte h 1 * 2 ^ 8 + ipv4Byte h 0 = h := by
  unfold ipv4Byte
  omega

theorem ipv6_decomposition (h : Nat) (hh : h < 2 ^ 128) :
    ipv6Field h 7 * 2 ^ 112 + ipv6Field h 6 * 2 ^ 96 + ipv6Field h 5 * 2 ^ 80 +
    ipv6Field h 4 * 2 ^ 64 + ipv6Field h 3 * 2 ^ 48 + ipv6Field h 2 * 2 ^ 32 +
    ipv6Field h 1 * 2 ^ 16 + ipv6Field h 0 = h := by
  unfold ipv6Field
  omega

theorem shift128_field (h i : Nat) (hi : i < 8) :
    shift128 (ipv6Field h i) ((i : Int) * 16) = ipv6Field h i * 2 ^ (16 * i) := by
  have hb := ipv6Field_bound h i
  have hp : 2 ^ (16 * i) ≤ 2 ^ 112 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := Nat.mul_le_mul_left (ipv6Field h i) hp
  have hsmall : ipv6Field h i * 2 ^ (16 * i) < 2 ^ 128 := by omega
  simp [shift128, show (0 : Int) ≤ (i : Int) * 16 from by omega, Int.toNat_mul,
    Nat.mul_comm i 16, Nat.mod_eq_of_lt hsmall]

end JuliaLean.Sockets
