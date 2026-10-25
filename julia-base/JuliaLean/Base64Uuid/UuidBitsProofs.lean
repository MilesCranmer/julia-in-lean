import JuliaLean.Base64Uuid.Props
import JuliaLean.Base64Uuid.BitLemmas

/-!
Version and variant bits of `uuid1`, `uuid4`, `uuid7` and `uuid5`.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The version nibble: bits `76:79`. -/
theorem nibble_of_bits (V v : Nat) (hv : v < 16)
    (h : ∀ i, i < 4 → V.testBit (i + 76) = v.testBit i) :
    (V / 2 ^ 76 &&& 15) % 2 ^ 8 = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_div_two_pow,
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 4
  · have hi8 : i < 8 := by omega
    simp [hi, hi8, h i hi]
  · have hv' : v.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ i)))
    simp [hi, hv']

/-- The variant field: bits `62:63`. -/
theorem variant_of_bits (V : Nat) (h62 : V.testBit 62 = false) (h63 : V.testBit 63 = true) :
    V / 2 ^ 62 % 4 = 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  match i with
  | 0 => rw [show 0 + 62 = 62 from rfl, h62]; decide
  | 1 => rw [show 1 + 62 = 63 from rfl, h63]; decide
  | i + 2 =>
    have h1 : ¬ (i + 2 < 2) := by omega
    have : (2 : Nat).testBit (i + 2) = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, this]

theorem version_eq (u : UUID) : uuid_version u = (vn u.value / 2 ^ 76 &&& 15) % 2 ^ 8 := by
  simp only [uuid_version, bn_eq_vn, vn_rem uns_u128 uns_u8, vn_band uns_u128, vn_shr uns_u128]
  rfl

theorem variant_eq (u : UUID) : uuid_variant u = vn u.value / 2 ^ 62 % 4 := by
  show vn (shr u.value 62) % 4 = _
  rw [vn_shr uns_u128]

theorem testBit_and_or (R M C j : Nat) :
    ((R &&& M) ||| C).testBit j = (R.testBit j && M.testBit j || C.testBit j) := by
  simp [Nat.testBit_or, Nat.testBit_and]

theorem testBit_shift_low (y n m j : Nat) (hj : j < n) : (y * 2 ^ n % 2 ^ m).testBit j = false := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  have : ¬ n ≤ j := by omega
  simp [this]

theorem testBit_small_shift (y n m j a : Nat) (hy : y < 2 ^ a) (hj : n + a ≤ j) :
    (y * 2 ^ n % 2 ^ m).testBit j = false := by
  apply Nat.testBit_lt_two_pow
  calc y * 2 ^ n % 2 ^ m ≤ y * 2 ^ n := Nat.mod_le _ _
    _ < 2 ^ a * 2 ^ n := Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos n)
    _ = 2 ^ (a + n) := (Nat.pow_add 2 a n).symm
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)

theorem uuid4Bits_proven : Uuid4Bits := by
  intro r
  have hv : vn (uuid4 r).value = (vn r &&& 0xffffffffffff0fff3fffffffffffffff) |||
      0x00000000000040008000000000000000 := by
    simp only [uuid4, vn_bor uns_u128, vn_band uns_u128]; rfl
  constructor
  · rw [version_eq, hv]
    apply nibble_of_bits _ _ (by decide)
    intro i hi
    rw [testBit_and_or]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ => cases (vn r).testBit _ <;> decide
  · rw [variant_eq, hv]
    apply variant_of_bits <;> rw [testBit_and_or] <;> cases (vn r).testBit _ <;> decide

theorem uuid7Bits_proven : Uuid7Bits := by
  intro r ts hts
  have hv : vn (build_uuid7 r ts).value = ((vn r &&& 0x0000000000000fff3fffffffffffffff) |||
      0x00000000000070008000000000000000) ||| vn ts * 2 ^ 80 % 2 ^ 128 := by
    simp only [build_uuid7, vn_bor uns_u128, vn_band uns_u128, vn_shl uns_u128]; rfl
  have low : ∀ j, j < 80 → (vn (build_uuid7 r ts).value).testBit j =
      ((vn r &&& 0x0000000000000fff3fffffffffffffff) ||| 0x00000000000070008000000000000000).testBit j := by
    intro j hj
    rw [hv, Nat.testBit_or, testBit_shift_low _ _ _ _ hj, Bool.or_false]
  constructor
  · rw [version_eq]
    apply nibble_of_bits _ _ (by decide)
    intro i hi
    rw [low _ (by omega), testBit_and_or]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ => cases (vn r).testBit _ <;> decide
  · rw [variant_eq]
    apply variant_of_bits <;> rw [low _ (by omega), testBit_and_or] <;> cases (vn r).testBit _ <;> decide

theorem uuid1Bits_proven : Uuid1Bits := by
  intro r ts
  let a := vn (band ts (JInt.lit .u64 0xffffffff))
  let b := vn (band (shr ts 32) (JInt.lit .u64 0xffff))
  let c := vn (band (shr ts 48) (JInt.lit .u64 0x0fff))
  have hc : c < 2 ^ 12 := by
    show vn (band (shr ts 48) (JInt.lit .u64 0x0fff)) < _
    rw [vn_band uns_u64]
    exact Nat.and_lt_two_pow _ (by decide)
  have hv : vn (build_uuid1 r ts).value =
      (((vn r &&& 0x00000000000000003fffffffffffffff) ||| 0x00000000000010008000010000000000) |||
        a % 2 ^ 128 * 2 ^ 96 % 2 ^ 128) ||| b % 2 ^ 128 * 2 ^ 80 % 2 ^ 128 |||
        c % 2 ^ 128 * 2 ^ 64 % 2 ^ 128 := by
    simp only [build_uuid1, vn_bor uns_u128, vn_band uns_u128, vn_shl uns_u128, vn_rem uns_u64 uns_u128]
    rfl
  have hlow : ∀ j, (j < 64 ∨ (76 ≤ j ∧ j < 80)) →
      (vn (build_uuid1 r ts).value).testBit j =
      ((vn r &&& 0x00000000000000003fffffffffffffff) ||| 0x00000000000010008000010000000000).testBit j := by
    intro j hj
    have h64 : (c % 2 ^ 128 * 2 ^ 64 % 2 ^ 128).testBit j = false := by
      rcases hj with hj | hj
      · exact testBit_shift_low _ _ _ _ hj
      · exact testBit_small_shift _ _ _ _ 12 (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hc) (by omega)
    rw [hv, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, testBit_shift_low _ _ _ _ (by omega : j < 96),
      testBit_shift_low _ _ _ _ (by omega : j < 80), h64]
    simp only [Bool.or_false]
  constructor
  · rw [version_eq]
    apply nibble_of_bits _ _ (by decide)
    intro i hi
    rw [hlow _ (by omega), testBit_and_or]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ => cases (vn r).testBit _ <;> decide
  · rw [variant_eq]
    apply variant_of_bits <;> rw [hlow _ (by omega), testBit_and_or] <;> cases (vn r).testBit _ <;> decide

/-- The `uuid5` accumulation `v = (v << 0x08) | hash_result[idx]` does not overflow
while the bytes fit: its value is the big-endian number of the bytes. -/
theorem fold_bytes (G : Nat → Byte) (l : List Nat) (acc : U128)
    (hacc : (vn acc + 1) * 256 ^ l.length ≤ 2 ^ 128) :
    vn (l.foldl (fun (v : U128) idx => bor (shl v 8) (JInt.rem .u128 (G idx))) acc) =
      l.foldl (fun w idx => w * 256 + vn (G idx)) (vn acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    have hb : vn (G x) < 256 := vn_lt uns_u8 _
    have hp : 1 ≤ 256 ^ xs.length := Nat.pow_pos (by decide)
    have hacc' : (vn acc + 1) * (256 ^ xs.length * 256) ≤ 2 ^ 128 := by
      simpa [List.length_cons, Nat.pow_succ] using hacc
    have h256 : (vn acc + 1) * 256 ≤ 2 ^ 128 :=
      Nat.le_trans (Nat.mul_le_mul_left _ (by simpa using Nat.mul_le_mul_right 256 hp)) hacc'
    have hstep : vn (bor (shl acc 8) (JInt.rem .u128 (G x))) = vn acc * 256 + vn (G x) := by
      rw [vn_bor uns_u128, vn_shl uns_u128, vn_rem uns_u8 uns_u128,
        Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide)),
        Nat.mod_eq_of_lt (by show vn acc * 256 < 2 ^ 128; omega)]
      rw [show vn acc * 2 ^ 8 = 2 ^ 8 * vn acc from Nat.mul_comm _ _,
        ← Nat.two_pow_add_eq_or_of_lt (show vn (G x) < 2 ^ 8 from hb)]
    have hnext : (vn (bor (shl acc 8) (JInt.rem .u128 (G x))) + 1) * 256 ^ xs.length ≤ 2 ^ 128 := by
      rw [hstep]
      calc (vn acc * 256 + vn (G x) + 1) * 256 ^ xs.length
          ≤ (vn acc * 256 + 256) * 256 ^ xs.length := Nat.mul_le_mul_right _ (by omega)
        _ = (vn acc + 1) * (256 ^ xs.length * 256) := by
            rw [show vn acc * 256 + 256 = (vn acc + 1) * 256 by omega, Nat.mul_assoc,
              Nat.mul_comm 256]
        _ ≤ 2 ^ 128 := hacc'
    rw [ih _ hnext, hstep]

theorem fold16_bits (h' : List Byte)
    (h6 : 80 ≤ vn (h'.getD 6 (b8 0)) ∧ vn (h'.getD 6 (b8 0)) < 96)
    (h8 : 128 ≤ vn (h'.getD 8 (b8 0)) ∧ vn (h'.getD 8 (b8 0)) < 192) :
    uuid_version ⟨(List.range 16).foldl (fun (v : U128) idx => bor (shl v 8)
        (JInt.rem .u128 (h'.getD idx (b8 0)))) (JInt.lit .u128 0)⟩ = 5 ∧
    uuid_variant ⟨(List.range 16).foldl (fun (v : U128) idx => bor (shl v 8)
        (JInt.rem .u128 (h'.getD idx (b8 0)))) (JInt.lit .u128 0)⟩ = 2 := by
  have hfold := fold_bytes (fun i => h'.getD i (b8 0)) (List.range 16) (JInt.lit .u128 0) (by decide)
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  have h0 : vn (JInt.lit .u128 0) = 0 := rfl
  rw [hr] at hfold ⊢
  simp only [List.foldl, h0] at hfold
  have hb : ∀ i, vn (h'.getD i (b8 0)) < 256 := fun i => vn_lt uns_u8 _
  have := hb 7; have := hb 9; have := hb 10; have := hb 11; have := hb 12; have := hb 13
  have := hb 14; have := hb 15
  rw [version_eq, variant_eq]
  simp only [List.foldl]
  rw [hfold, show ∀ x : Nat, x &&& 15 = x % 16 from fun x => Nat.and_two_pow_sub_one_eq_mod x 4]
  constructor
  · show (_ / 75557863725914323419136 % 16) % 256 = 5
    omega
  · show _ / 4611686018427387904 % 4 = 2
    omega

theorem getD_set_self (l : List Byte) (i : Nat) (v d : Byte) (hi : i < l.length) :
    (l.set i v).getD i d = v := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_ne (l : List Byte) (i j : Nat) (v d : Byte) (hij : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, hij]

theorem or_low (x a k : Nat) (hx : x < 2 ^ k) : x ||| 2 ^ k * a = 2 ^ k * a + x := by
  rw [Nat.or_comm, Nat.two_pow_add_eq_or_of_lt hx]

theorem uuid5Bits_proven : Uuid5Bits := by
  intro sha ns name u hu
  simp only [uuid5] at hu
  cases hm : uuid5Message ns name with
  | error e => rw [hm] at hu; cases hu
  | ok msg =>
    rw [hm] at hu
    change uuid5Finish (sha msg) = .ok u at hu
    unfold uuid5Finish at hu
    split at hu
    · cases hu
    · rename_i hl
      have hl' : 16 ≤ (sha msg).length := by omega
      simp only [Except.ok.injEq] at hu
      subst hu
      apply fold16_bits
      · rw [getD_set_ne _ _ _ _ _ (by decide), getD_set_self _ _ _ _ (by omega)]
        rw [vn_bor uns_u8, vn_band uns_u8, show vn (b8 0x0f) = 2 ^ 4 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod, show vn (b8 0x50) = 2 ^ 4 * 5 from rfl,
          or_low _ _ _ (Nat.mod_lt _ (by decide))]
        have := Nat.mod_lt (vn ((sha msg).getD 6 (b8 0))) (show 2 ^ 4 > 0 by decide)
        constructor <;> omega
      · rw [getD_set_self _ _ _ _ (by rw [List.length_set]; omega)]
        rw [vn_bor uns_u8, vn_band uns_u8, show vn (b8 0x3f) = 2 ^ 6 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod, show vn (b8 0x80) = 2 ^ 6 * 2 from rfl,
          or_low _ _ _ (Nat.mod_lt _ (by decide))]
        have := Nat.mod_lt (vn (((sha msg).set 6 (bor (band ((sha msg).getD 6 (b8 0)) (b8 0x0f))
          (b8 0x50))).getD 8 (b8 0))) (show 2 ^ 6 > 0 by decide)
        constructor <;> omega

end JuliaLean.Base64Uuid
